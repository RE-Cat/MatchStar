// Copyright (c) 2026 Starlang Contributors
// SPDX-License-Identifier: MIT
package main

import (
	"bufio"
	"encoding/json"
	"flag"
	"fmt"
	"os"
	"regexp"
	"sort"
	"strconv"
	"strings"
	"time"
	"unicode"
)

// ============================================================
// Starlang 1.0.0-release-go
// Multi-Engine Analysis Language (MEAL)
//
// State spec: target/value/Lines.start/token.start/token.end/number
// Multi-match index: [N]
//
// Optimizations:
//   - StateStore uses undo-log rollback (no full map copy)
//   - Lexer pre-allocates + zero-alloc string slicing + correct multi-char operators
//   - Keyword table safely reset (no global pollution)
//   - Various slice/map pre-allocations
// ============================================================

// ---------- 1. State store ----------

// undoEntry records one write op for efficient rollback (avoids full map copy)
type undoEntry struct {
	key      string
	oldValue interface{}
	existed  bool
	kind     byte // 0=data, 1=id, 2=alias
}

type StateStore struct {
	data    map[string]interface{}
	alias   map[string]string
	ids     map[string]string
	history []string
	trace   bool
	parent  *StateStore
	bodyID  string
	undo    []undoEntry // change log, supports O(changes) rollback
}

// Soft ANSI colors (low saturation / low brightness)
const (
	Reset = "\033[0m"
	Bold  = "\033[1m"
	Dim   = "\033[2m"
	Gray  = "\033[90m" // bright gray, replaces harsh white

	SoftCyan    = "\033[38;5;109m" // soft cyan
	SoftGreen   = "\033[38;5;108m" // soft green
	SoftBlue    = "\033[38;5;110m" // soft blue
	SoftYellow  = "\033[38;5;180m" // soft yellow (beige-ish)
	SoftRed     = "\033[38;5;174m" // soft red (muted)
	SoftMagenta = "\033[38;5;139m" // soft magenta
)

// colorize is disabled when output is not a TTY or NO_COLOR is set
var colorize = func() bool {
	if os.Getenv("NO_COLOR") != "" {
		return false
	}
	if os.Getenv("FORCE_COLOR") != "" {
		return true
	}
	fi, _ := os.Stdout.Stat()
	return fi != nil && (fi.Mode()&os.ModeCharDevice) != 0
}()

// C wraps s with the given color (returns s unchanged if colors disabled)
func C(s, color string) string {
	if !colorize || color == "" {
		return s
	}
	return color + s + Reset
}

func NewStateStore() *StateStore {
	return &StateStore{
		data:    make(map[string]interface{}, 32),
		alias:   make(map[string]string, 8),
		ids:     make(map[string]string, 8),
		history: make([]string, 0, 16),
		undo:    make([]undoEntry, 0, 32),
	}
}

func NewStateStoreWithID(bodyID string) *StateStore {
	s := NewStateStore()
	s.bodyID = bodyID
	return s
}

func (s *StateStore) Child() *StateStore {
	c := NewStateStore()
	c.parent = s
	c.trace = s.trace
	return c
}

func (s *StateStore) resolve(k string) string {
	if v, ok := s.ids[k]; ok {
		return v
	}
	if f, ok := s.alias[k]; ok {
		return f
	}
	return k
}

// markUndo records old value before write, to support later Rollback
func (s *StateStore) markUndo(key string, kind byte) {
	switch kind {
	case 0:
		old, ok := s.data[key]
		s.undo = append(s.undo, undoEntry{key: key, oldValue: old, existed: ok, kind: 0})
	case 1:
		old, ok := s.ids[key]
		s.undo = append(s.undo, undoEntry{key: key, oldValue: old, existed: ok, kind: 1})
	case 2:
		old, ok := s.alias[key]
		s.undo = append(s.undo, undoEntry{key: key, oldValue: old, existed: ok, kind: 2})
	}
}

func (s *StateStore) Set(k string, v interface{}) {
	full := s.resolve(k)
	s.markUndo(full, 0)
	s.data[full] = v
	if s.trace {
		s.history = append(s.history, fmt.Sprintf("SET %s = %v", full, v))
	}
}

func (s *StateStore) Get(k string) (interface{}, bool) {
	full := s.resolve(k)
	if v, ok := s.data[full]; ok {
		return v, true
	}
	if s.parent != nil {
		return s.parent.Get(k)
	}
	return nil, false
}

func (s *StateStore) SetID(id, val string) {
	s.markUndo(id, 1)
	s.ids[id] = val
	if s.trace {
		s.history = append(s.history, fmt.Sprintf("ID %s -> %s", id, val))
	}
}

func (s *StateStore) GetID(id string) (string, bool) {
	v, ok := s.ids[id]
	return v, ok
}

func (s *StateStore) GetBool(k string) bool {
	v, ok := s.Get(k)
	if !ok {
		return false
	}
	b, _ := v.(bool)
	return b
}

func (s *StateStore) GetInt(k string) int {
	v, ok := s.Get(k)
	if !ok {
		return 0
	}
	switch n := v.(type) {
	case int:
		return n
	case int64:
		return int(n)
	case float64:
		return int(n)
	}
	return 0
}

func (s *StateStore) GetFloat(k string) float64 {
	v, ok := s.Get(k)
	if !ok {
		return 0
	}
	switch n := v.(type) {
	case int:
		return float64(n)
	case int64:
		return float64(n)
	case float64:
		return n
	}
	return 0
}

func (s *StateStore) GetString(k string) string {
	v, ok := s.Get(k)
	if !ok {
		return ""
	}
	if str, ok := v.(string); ok {
		return str
	}
	return fmt.Sprintf("%v", v)
}

func (s *StateStore) Incr(k string) int {
	n := s.GetInt(k) + 1
	s.Set(k, n)
	return n
}

func (s *StateStore) Decr(k string) int {
	n := s.GetInt(k) - 1
	s.Set(k, n)
	return n
}

func (s *StateStore) AddInt(k string, delta int) int {
	n := s.GetInt(k) + delta
	s.Set(k, n)
	return n
}

func (s *StateStore) Append(k string, v string) {
	old := s.GetString(k)
	if old == "" {
		s.Set(k, v)
		return
	}
	s.Set(k, old+","+v)
}

func (s *StateStore) AddAlias(short, full string) {
	s.markUndo(short, 2)
	s.alias[short] = full
	if s.trace {
		s.history = append(s.history, fmt.Sprintf("ALIAS %s -> %s", short, full))
	}
}

func (s *StateStore) Has(k string) bool {
	_, ok := s.Get(k)
	return ok
}

func (s *StateStore) Delete(k string) {
	full := s.resolve(k)
	s.markUndo(full, 0)
	delete(s.data, full)
}

func (s *StateStore) Clear() {
	s.data = make(map[string]interface{}, 32)
	s.history = s.history[:0]
	s.undo = s.undo[:0]
}

// Checkpoint returns the current undo log length (rollback point)
func (s *StateStore) Checkpoint() int {
	return len(s.undo)
}

// Rollback rolls back to the given checkpoint (O(changes), much faster than full copy)
func (s *StateStore) Rollback(cp int) {
	for i := len(s.undo) - 1; i >= cp; i-- {
		e := s.undo[i]
		switch e.kind {
		case 0:
			if e.existed {
				s.data[e.key] = e.oldValue
			} else {
				delete(s.data, e.key)
			}
		case 1:
			if e.existed {
				s.ids[e.key] = e.oldValue.(string)
			} else {
				delete(s.ids, e.key)
			}
		case 2:
			if e.existed {
				s.alias[e.key] = e.oldValue.(string)
			} else {
				delete(s.alias, e.key)
			}
		}
	}
	s.undo = s.undo[:cp]
}

// Snapshot kept for compatibility (full copy, debug/export only)
func (s *StateStore) Snapshot() map[string]interface{} {
	cp := make(map[string]interface{}, len(s.data))
	for k, v := range s.data {
		cp[k] = v
	}
	return cp
}

// Restore kept for compatibility
func (s *StateStore) Restore(snap map[string]interface{}) {
	s.data = snap
	s.undo = s.undo[:0]
}

func (s *StateStore) Keys() []string {
	keys := make([]string, 0, len(s.data))
	for k := range s.data {
		keys = append(keys, k)
	}
	sort.Strings(keys)
	return keys
}

func (s *StateStore) IDKeys() []string {
	keys := make([]string, 0, len(s.ids))
	for k := range s.ids {
		keys = append(keys, k)
	}
	sort.Strings(keys)
	return keys
}

func (s *StateStore) AliasKeys() []string {
	keys := make([]string, 0, len(s.alias))
	for k := range s.alias {
		keys = append(keys, k)
	}
	sort.Strings(keys)
	return keys
}

func (s *StateStore) Size() int {
	return len(s.data)
}

func (s *StateStore) Dump() {
	fmt.Println(C("--- state ---", Bold+SoftCyan))
	if len(s.data) == 0 {
		fmt.Println("  " + C("(empty)", Dim+Gray))
	} else {
		for _, k := range s.Keys() {
			fmt.Printf("  %s = %s\n",
				C(k, SoftBlue),
				C(fmt.Sprintf("%v", s.data[k]), SoftGreen))
		}
	}
	if len(s.ids) > 0 {
		fmt.Println(C("--- ID ---", Bold+SoftMagenta))
		for _, k := range s.IDKeys() {
			fmt.Printf("  %s -> %s\n",
				C(k, SoftBlue),
				C(s.ids[k], SoftYellow))
		}
	}
	if len(s.alias) > 0 {
		fmt.Println(C("--- alias ---", Bold+SoftMagenta))
		for _, k := range s.AliasKeys() {
			fmt.Printf("  %s -> %s\n",
				C(k, SoftBlue),
				C(s.alias[k], SoftYellow))
		}
	}
}

func (s *StateStore) DumpHistory() {
	fmt.Println(C("--- history ---", Bold+SoftCyan))
	if len(s.history) == 0 {
		fmt.Println("  " + C("(none)", Dim+Gray))
		return
	}
	for i, h := range s.history {
		fmt.Printf("  [%d] %s\n", i, C(h, Gray))
	}
}

func (s *StateStore) ToJSON() string {
	out := map[string]interface{}{
		"data":  s.data,
		"ids":   s.ids,
		"alias": s.alias,
	}
	b, err := json.MarshalIndent(out, "", "  ")
	if err != nil {
		return "{}"
	}
	return string(b)
}

// ---------- 2. Lexer ----------

type Token struct {
	Text  string
	Pos   int
	Class string
	Line  int
	Col   int
}

var builtinBoundary = map[string]bool{
	"{": true, "}": true, "[": true, "]": true, "(": true, ")": true,
}

var builtinOperator = map[string]bool{
	"+": true, "-": true, "*": true, "/": true,
	"=": true, "==": true, "!=": true,
	"<": true, ">": true, "<=": true, ">=": true,
	"&&": true, "||": true, "!": true,
	"->": true, "-->": true, "==>": true, "=>": true,
	"<->": true, "<-->": true, "<<->>": true, "<<-->>": true,
}

var builtinSymbol = map[string]bool{
	":": true, ",": true, ".": true, ";": true,
	"\"": true, "'": true, "#": true, "@": true, "$": true, "%": true,
	"^": true, "&": true, "|": true, "~": true, "?": true, "\\": true,
}

var builtinKeyword = map[string]bool{
	"def": true, "if": true,
}

var builtinClassNames = map[string]bool{
	"Bd": true, "Ky": true, "Ot": true, "Sy": true,
	"Num": true, "Text": true, "Str": true,
}

func classifySymbol(s string) string {
	if builtinBoundary[s] {
		return "Bd"
	}
	if builtinOperator[s] {
		return "Ot"
	}
	if builtinSymbol[s] {
		return "Sy"
	}
	return "Text"
}

func stripComments(src string) string {
	var sb strings.Builder
	runes := []rune(src)
	i, n := 0, len(runes)
	var inString rune = 0
	inEscape := false
	for i < n {
		r := runes[i]
		if inString != 0 {
			sb.WriteRune(r)
			if inEscape {
				inEscape = false
			} else if r == '\\' {
				inEscape = true
			} else if r == inString {
				inString = 0
			}
			i++
			continue
		}
		if r == '"' || r == '\'' {
			inString = r
			sb.WriteRune(r)
			i++
			continue
		}
		if r == '|' {
			sb.WriteRune(r)
			i++
			for i < n && runes[i] != '|' {
				sb.WriteRune(runes[i])
				i++
			}
			if i < n {
				sb.WriteRune('|')
				i++
			}
			continue
		}
		if r == '/' && i+1 < n && runes[i+1] == '*' {
			i += 2
			for i+1 < n && !(runes[i] == '*' && runes[i+1] == '/') {
				if runes[i] == '\n' {
					sb.WriteRune('\n')
				}
				i++
			}
			i += 2
			continue
		}
		if r == '/' && i+1 < n && runes[i+1] == '/' {
			for i < n && runes[i] != '\n' {
				i++
			}
			continue
		}
		if r == '#' {
			lineStart := i == 0 || runes[i-1] == '\n'
			afterSpace := i > 0 && (runes[i-1] == ' ' || runes[i-1] == '\t')
			if lineStart || afterSpace {
				for i < n && runes[i] != '\n' {
					i++
				}
				continue
			}
		}
		sb.WriteRune(r)
		i++
	}
	return sb.String()
}

type Lexer struct {
	input  []rune
	pos    int
	line   int
	col    int
	ignore map[rune]bool
}

func NewLexer(input string, ignore map[rune]bool) *Lexer {
	return &Lexer{
		input: []rune(input), pos: 0, line: 1, col: 1, ignore: ignore,
	}
}

func (l *Lexer) peek() rune {
	if l.pos >= len(l.input) {
		return 0
	}
	return l.input[l.pos]
}

func (l *Lexer) peekAt(off int) rune {
	if l.pos+off >= len(l.input) {
		return 0
	}
	return l.input[l.pos+off]
}

func (l *Lexer) advance() rune {
	r := l.input[l.pos]
	l.pos++
	if r == '\n' {
		l.line++
		l.col = 1
	} else {
		l.col++
	}
	return r
}

func (l *Lexer) Lex() []Token {
	// Pre-allocate: roughly chars/4 tokens, reduces growth
	toks := make([]Token, 0, len(l.input)/4+8)
	for l.pos < len(l.input) {
		r := l.peek()
		switch {
		case r == '"':
			toks = append(toks, l.lexString())
		case r == '\'':
			toks = append(toks, l.lexSingleQuote())
		case r == '|':
			if tok, ok := l.lexEscape(); ok {
				toks = append(toks, tok)
			} else {
				// unclosed | treated as a normal symbol
				s := string(r)
				toks = append(toks, Token{Text: s, Pos: l.pos, Class: classifySymbol(s), Line: l.line, Col: l.col})
				l.advance()
			}
		case l.ignore[r] || r == ' ' || r == '\t' || r == '\n' || r == '\r':
			l.advance()
		case unicode.IsDigit(r) || (r == '-' && unicode.IsDigit(l.peekAt(1))):
			toks = append(toks, l.lexNumber())
		case unicode.IsLetter(r) || r == '_':
			toks = append(toks, l.lexIdent())
		default:
			// Multi-char operators: match longest first
			if n := l.matchOperator(); n > 0 {
				start, sl, sc := l.pos, l.line, l.col
				text := string(l.input[l.pos : l.pos+n])
				for i := 0; i < n; i++ {
					l.advance()
				}
				toks = append(toks, Token{Text: text, Pos: start, Class: "Ot", Line: sl, Col: sc})
			} else {
				s := string(r)
				toks = append(toks, Token{Text: s, Pos: l.pos, Class: classifySymbol(s), Line: l.line, Col: l.col})
				l.advance()
			}
		}
	}
	return toks
}

// matchOperator returns the matched operator length (0 = no match)
// Supports: <<-->>(6) <<->>(5) <-->(4) -->(3) ==>(3) <->(3) and 2-char operators
func (l *Lexer) matchOperator() int {
	remain := len(l.input) - l.pos
	in := l.input
	p := l.pos
	if remain >= 6 && in[p] == '<' && in[p+1] == '<' && in[p+2] == '-' && in[p+3] == '-' && in[p+4] == '>' && in[p+5] == '>' {
		return 6 // <<-->>
	}
	if remain >= 5 && in[p] == '<' && in[p+1] == '<' && in[p+2] == '-' && in[p+3] == '>' && in[p+4] == '>' {
		return 5 // <<->>
	}
	if remain >= 4 {
		// <-->
		if in[p] == '<' && in[p+1] == '-' && in[p+2] == '-' && in[p+3] == '>' {
			return 4
		}
	}
	if remain >= 3 {
		a, b, c := in[p], in[p+1], in[p+2]
		if (a == '-' && b == '-' && c == '>') || // -->
			(a == '=' && b == '=' && c == '>') || // ==>
			(a == '<' && b == '-' && c == '>') { // <->
			return 3
		}
	}
	if remain >= 2 {
		two := string(in[p : p+2])
		if builtinOperator[two] {
			return 2
		}
	}
	return 0
}

func (l *Lexer) lexString() Token {
	start, sl, sc := l.pos, l.line, l.col
	l.advance() // skip opening "
	for l.pos < len(l.input) && l.peek() != '"' {
		l.advance()
	}
	if l.pos < len(l.input) {
		l.advance() // skip closing "
	}
	// Slice directly, avoid intermediate rune slice allocation
	return Token{Text: string(l.input[start:l.pos]), Pos: start, Class: "Str", Line: sl, Col: sc}
}

func (l *Lexer) lexSingleQuote() Token {
	start, sl, sc := l.pos, l.line, l.col
	l.advance()
	for l.pos < len(l.input) && l.peek() != '\'' {
		l.advance()
	}
	if l.pos < len(l.input) {
		l.advance()
	}
	return Token{Text: string(l.input[start:l.pos]), Pos: start, Class: "Str", Line: sl, Col: sc}
}

func (l *Lexer) lexEscape() (Token, bool) {
	start, sl, sc := l.pos, l.line, l.col
	l.advance() // skip opening |
	for l.pos < len(l.input) && l.peek() != '|' {
		l.advance()
	}
	if l.pos >= len(l.input) {
		l.pos, l.line, l.col = start, sl, sc
		return Token{}, false
	}
	end := l.pos
	l.advance() // skip closing |
	// content excludes both | delimiters
	return Token{Text: string(l.input[start+1 : end]), Pos: start, Class: "Text", Line: sl, Col: sc}, true
}

func (l *Lexer) lexNumber() Token {
	start, sl, sc := l.pos, l.line, l.col
	if l.peek() == '-' {
		l.advance()
	}
	for l.pos < len(l.input) {
		r := l.peek()
		if unicode.IsDigit(r) || r == '.' {
			l.advance()
			continue
		}
		break
	}
	return Token{Text: string(l.input[start:l.pos]), Pos: start, Class: "Num", Line: sl, Col: sc}
}

func (l *Lexer) lexIdent() Token {
	start, sl, sc := l.pos, l.line, l.col
	for l.pos < len(l.input) {
		r := l.peek()
		if unicode.IsLetter(r) || unicode.IsDigit(r) || r == '_' || r == '@' {
			l.advance()
			continue
		}
		break
	}
	w := string(l.input[start:l.pos])
	cls := "Text"
	if builtinKeyword[w] {
		cls = "Ky"
	}
	return Token{Text: w, Pos: start, Class: cls, Line: sl, Col: sc}
}

func Lex(input string, ignore map[rune]bool) []Token {
	return NewLexer(input, ignore).Lex()
}

func TokenizeToString(toks []Token) string {
	if len(toks) == 0 {
		return ""
	}
	var sb strings.Builder
	sb.Grow(len(toks) * 12)
	for i, t := range toks {
		if i > 0 {
			sb.WriteByte(' ')
		}
		sb.WriteString(t.Text)
		sb.WriteByte('(')
		sb.WriteString(t.Class)
		sb.WriteByte(')')
	}
	return sb.String()
}

// ---------- 3. AST ----------

type Node interface{ nodeTag() string }

type TableDef struct {
	Name    string
	Items   []string
	IsEmpty bool
}

func (t *TableDef) Contains(v string) bool {
	for _, it := range t.Items {
		if it == v {
			return true
		}
	}
	return false
}

type MatchItem struct {
	Class   string
	Target  string
	IsClass bool
	Any     bool
	Table   *TableDef
	Re      *regexp.Regexp
	ReSrc   string
}

type Segment struct{ Items []MatchItem }

type MatchCond struct {
	Class    string
	Target   string
	Greed    bool
	Op       string
	Table    *TableDef
	Re       *regexp.Regexp
	ReSrc    string
	ReNamed  []string
	IsAll    bool
	IsSem    bool
	IsCap    bool
	IsSeq    bool
	Left     []Segment
	Right    []Segment
	BlockRef string
}

func (*MatchCond) nodeTag() string { return "MatchCond" }

type DeepCond struct {
	Left       string
	Right      string
	Greed      bool
	CrossLine  bool
	LeftIsRe   *regexp.Regexp
	RightIsRe  *regexp.Regexp
	LeftClass  string
	RightClass string
	LeftIsAll  bool
	RightIsAll bool
}

func (*DeepCond) nodeTag() string { return "DeepCond" }

type StarCond struct {
	Target  string
	Dir     string
	LookFor []string
	Mode    string
}

func (*StarCond) nodeTag() string { return "StarCond" }

type StatusExpr struct {
	Left  string
	Op    string
	Right string
}

func (*StatusExpr) nodeTag() string { return "StatusExpr" }

type LogicExpr struct {
	Op    string
	Left  Node
	Right Node
}

func (*LogicExpr) nodeTag() string { return "LogicExpr" }

type NotExpr struct{ Inner Node }

func (*NotExpr) nodeTag() string { return "NotExpr" }

type IfBranch struct {
	Cond Node
	Then []Node
}

type IfStmt struct {
	Branches []IfBranch
	Else     []Node
}

func (*IfStmt) nodeTag() string { return "IfStmt" }

type AssignStmt struct {
	Target string
	Value  string
	Alias  string
	Op     string
	CapID  string
	Attr   string
}

func (*AssignStmt) nodeTag() string { return "AssignStmt" }

type AppendStmt struct {
	Target string
	Value  string
}

func (*AppendStmt) nodeTag() string { return "AppendStmt" }

type StopStmt struct{}

func (*StopStmt) nodeTag() string { return "StopStmt" }

type StateStmt struct {
	Object string
	Fields []string
}

func (*StateStmt) nodeTag() string { return "StateStmt" }

type IncrStmt struct{ Target string }

func (*IncrStmt) nodeTag() string { return "IncrStmt" }

type DecrStmt struct{ Target string }

func (*DecrStmt) nodeTag() string { return "DecrStmt" }

type AddIntStmt struct {
	Target string
	Delta  int
}

func (*AddIntStmt) nodeTag() string { return "AddIntStmt" }

type StarStmt struct {
	Target  string
	Dir     string
	LookFor []string
	Mode    string
	Body    []Node
}

func (*StarStmt) nodeTag() string { return "StarStmt" }

type Block struct {
	Name     string
	Kind     string
	Num      int
	Parent   *Block
	Children []*Block
	Stmts    []Node
}

func (*Block) nodeTag() string { return "Block" }

type Head struct {
	BodyID  string
	Ignore  map[rune]bool
	Keyword map[string]bool
	Decls   map[string]interface{}
}

type Body struct {
	ID     string
	State  *StateStore
	Blocks []*Block
}

type Config struct {
	Ignore    map[rune]bool
	TableDefs map[string]*TableDef
	Heads     []*Head
	Bodies    []*Body
	Blocks    []*Block
}

// ---------- 4. Utilities ----------

func between(s, a, b string) string {
	i := strings.Index(s, a)
	j := strings.LastIndex(s, b)
	if i < 0 || j <= i {
		return ""
	}
	return s[i+1 : j]
}

func findOutsideString(s, sub string) int {
	inStr := byte(0)
	inEsc := false
	for i := 0; i+len(sub) <= len(s); i++ {
		c := s[i]
		if inStr != 0 {
			if inEsc {
				inEsc = false
			} else if c == '\\' {
				inEsc = true
			} else if c == inStr {
				inStr = 0
			}
			continue
		}
		if c == '"' || c == '\'' {
			inStr = c
			continue
		}
		if strings.HasPrefix(s[i:], sub) {
			return i
		}
	}
	return -1
}

func parseTableInline(s string) *TableDef {
	s = strings.TrimSpace(s)
	if strings.HasPrefix(s, "{") && strings.HasSuffix(s, "}") {
		inner := strings.TrimSpace(s[1 : len(s)-1])
		if strings.Contains(inner, ";") {
			return nil
		}
		td := &TableDef{Name: "_anon"}
		var items []string
		if strings.Contains(inner, " or ") {
			items = strings.Split(inner, " or ")
		} else if strings.Contains(inner, ",") {
			items = strings.Split(inner, ",")
		} else if inner != "" {
			items = []string{inner}
		}
		for _, it := range items {
			it = strings.TrimSpace(it)
			if it != "" {
				td.Items = append(td.Items, it)
			}
		}
		return td
	}
	idx := strings.IndexAny(s, "[{")
	if idx <= 0 {
		return nil
	}
	opener := s[idx]
	var closer byte
	if opener == '{' {
		closer = '}'
	} else {
		closer = ']'
	}
	name := strings.TrimSpace(s[:idx])
	if name == "" {
		return nil
	}
	for _, r := range name {
		if !unicode.IsLetter(r) && !unicode.IsDigit(r) && r != '_' {
			return nil
		}
	}
	end := strings.LastIndexByte(s, closer)
	if end <= idx {
		return nil
	}
	inner := strings.TrimSpace(s[idx+1 : end])
	if strings.Contains(inner, ";") {
		return nil
	}
	td := &TableDef{Name: name}
	if inner == "" {
		td.IsEmpty = true
		return td
	}
	var items []string
	if strings.Contains(inner, " or ") {
		items = strings.Split(inner, " or ")
	} else if strings.Contains(inner, ",") {
		items = strings.Split(inner, ",")
	} else {
		items = []string{inner}
	}
	for _, it := range items {
		it = strings.TrimSpace(it)
		if it != "" {
			td.Items = append(td.Items, it)
		}
	}
	return td
}

func parseSeqList(s string) ([]Segment, error) {
	s = strings.TrimSpace(s)
	if !strings.HasPrefix(s, "[") || !strings.HasSuffix(s, "]") {
		return nil, fmt.Errorf("sequence must use []: %s", s)
	}
	inner := strings.TrimSpace(s[1 : len(s)-1])
	var segStrs []string
	if strings.Contains(inner, ";") {
		segStrs = strings.Split(inner, ";")
	} else {
		segStrs = []string{inner}
	}
	var segs []Segment
	for _, ss := range segStrs {
		ss = strings.TrimSpace(ss)
		var itemStrs []string
		if strings.Contains(ss, ",") {
			itemStrs = strings.Split(ss, ",")
		} else if strings.Contains(ss, " or ") {
			itemStrs = strings.Split(ss, " or ")
		} else {
			itemStrs = []string{ss}
		}
		var items []MatchItem
		for _, is := range itemStrs {
			is = strings.TrimSpace(is)
			if is != "" {
				items = append(items, parseMatchItem(is))
			}
		}
		segs = append(segs, Segment{Items: items})
	}
	return segs, nil
}

func parseMatchItem(s string) MatchItem {
	s = strings.TrimSpace(s)
	if s == "nothing" || s == "*" {
		return MatchItem{Any: true}
	}
	if strings.HasPrefix(s, "Re(") {
		re, src, _, err := parseRe(s)
		if err == nil {
			return MatchItem{Re: re, ReSrc: src}
		}
	}
	if strings.HasPrefix(s, "@") {
		cls := strings.TrimPrefix(s, "@")
		if builtinClassNames[cls] {
			return MatchItem{Class: cls, IsClass: true}
		}
	}
	if td := parseTableInline(s); td != nil {
		return MatchItem{Table: td}
	}
	return MatchItem{Target: s}
}

func parseAssignTarget(s string) (target, capID, attr string) {
	s = strings.TrimSpace(s)
	if !strings.HasPrefix(s, "$") {
		return s, "", ""
	}
	rest := s
	if d := strings.Index(rest, "."); d >= 0 {
		attr = rest[d:]
		rest = rest[:d]
	}
	if i := strings.Index(rest, "-"); i >= 0 {
		return rest[:i], rest[i+1:], attr
	}
	return rest, "", attr
}

func isInt(s string) bool {
	if s == "" {
		return false
	}
	for i, r := range s {
		if r == '-' {
			if i != 0 {
				return false
			}
			continue
		}
		if r < '0' || r > '9' {
			return false
		}
	}
	return s != "-"
}

func isFloat(s string) bool {
	if s == "" {
		return false
	}
	hasDot := false
	for i, r := range s {
		if r == '-' {
			if i != 0 {
				return false
			}
			continue
		}
		if r == '.' {
			if hasDot {
				return false
			}
			hasDot = true
			continue
		}
		if r < '0' || r > '9' {
			return false
		}
	}
	return hasDot
}

// unquote strips surrounding quotes (single or double)
func unquote(s string) (string, bool) {
	n := len(s)
	if n >= 2 {
		if (s[0] == '"' && s[n-1] == '"') || (s[0] == '\'' && s[n-1] == '\'') {
			return s[1 : n-1], true
		}
	}
	return s, false
}

func extractParen(s string) (string, string) {
	if !strings.HasPrefix(s, "(") {
		return "", s
	}
	depth := 0
	for i, r := range s {
		if r == '(' {
			depth++
		} else if r == ')' {
			depth--
			if depth == 0 {
				return s[1:i], s[i+1:]
			}
		}
	}
	return "", s
}

func parseRe(s string) (*regexp.Regexp, string, []string, error) {
	s = strings.TrimSpace(s)
	if !strings.HasPrefix(s, "Re(") {
		return nil, "", nil, fmt.Errorf("not Re(...)")
	}
	inner, _ := extractParen(s[2:])
	if inner == "" && !strings.HasPrefix(s[2:], "(") {
		return nil, "", nil, fmt.Errorf("Re not closed")
	}
	var re *regexp.Regexp
	var err error
	if inner == "*" {
		re = regexp.MustCompile(".*")
	} else {
		re, err = regexp.Compile("^" + inner + "$")
		if err != nil {
			return nil, inner, nil, fmt.Errorf("regex compile failed: %v", err)
		}
	}
	var names []string
	for _, m := range re.SubexpNames() {
		if m != "" {
			names = append(names, m)
		}
	}
	return re, inner, names, nil
}

func parseDeepSym(s string) (greed, cross bool) {
	switch s {
	case "<->":
		return true, false
	case "<-->":
		return false, false
	case "<<->>":
		return true, true
	case "<<-->>":
		return false, true
	}
	return false, false
}

func extractTarget(cond Node) string {
	switch c := cond.(type) {
	case *MatchCond:
		if c.ReSrc != "" {
			return "Re(" + c.ReSrc + ")"
		}
		if c.Target != "" {
			return c.Target
		}
		if c.Class != "" {
			return "@" + c.Class
		}
		if c.Table != nil {
			return "{" + strings.Join(c.Table.Items, ",") + "}"
		}
		return ""
	case *DeepCond:
		return c.Left
	case *StarCond:
		return c.Target
	case *LogicExpr:
		l := extractTarget(c.Left)
		if l != "" {
			return l
		}
		return extractTarget(c.Right)
	}
	return ""
}

// ---------- 5. Parser ----------

type srcLine struct {
	indent int
	text   string
	lineno int
}

type Parser struct {
	lines     []srcLine
	pos       int
	cfg       *Config
	seenNames map[string]bool
	blockNum  int
}

func ParseString(content string) (*Config, error) {
	content = stripComments(content)
	raw := strings.Split(content, "\n")
	var ls []srcLine
	for i, l := range raw {
		trimmed := strings.TrimSpace(l)
		if trimmed == "" {
			continue
		}
		indent := 0
		for _, r := range l {
			if r == ' ' {
				indent++
			} else if r == '\t' {
				indent += 4
			} else {
				break
			}
		}
		ls = append(ls, srcLine{indent, trimmed, i + 1})
	}
	p := &Parser{
		lines: ls,
		cfg: &Config{
			Ignore:    map[rune]bool{},
			TableDefs: map[string]*TableDef{},
		},
		seenNames: map[string]bool{},
		blockNum:  0,
	}
	if err := p.parse(); err != nil {
		return nil, err
	}
	return p.cfg, nil
}

func ParseFile(path string) (*Config, error) {
	data, err := os.ReadFile(path)
	if err != nil {
		return nil, fmt.Errorf("cannot read %s: %w", path, err)
	}
	return ParseString(string(data))
}

func (p *Parser) parse() error {
	for p.pos < len(p.lines) {
		ln := p.lines[p.pos]
		t := ln.text
		if strings.HasPrefix(t, "Ignore") && strings.Contains(t, "=") {
			p.parseIgnoreLegacy()
			continue
		}
		if strings.HasPrefix(t, "keyword") && strings.Contains(t, ":") {
			p.parseKeywordLegacy()
			continue
		}
		if strings.HasPrefix(t, "def ") {
			if err := p.parseTopDef(); err != nil {
				return err
			}
			continue
		}
		if isBlockHeader(t) {
			blk, err := p.parseBlock(ln, nil)
			if err != nil {
				return err
			}
			if blk != nil {
				p.cfg.Blocks = append(p.cfg.Blocks, blk)
			}
			continue
		}
		return fmt.Errorf("line %d: cannot parse %q", ln.lineno, t)
	}
	return nil
}

func (p *Parser) parseIgnoreLegacy() {
	ln := p.lines[p.pos]
	full := ln.text
	p.pos++
	for !strings.Contains(full, "]") && p.pos < len(p.lines) {
		full += " " + p.lines[p.pos].text
		p.pos++
	}
	inner := between(full, "[", "]")
	for _, part := range strings.Split(inner, ",") {
		switch strings.TrimSpace(part) {
		case "space":
			p.cfg.Ignore[' '] = true
		case "enter":
			p.cfg.Ignore['\n'] = true
		case "tab":
			p.cfg.Ignore['\t'] = true
		case "return":
			p.cfg.Ignore['\r'] = true
		}
	}
}

func (p *Parser) parseKeywordLegacy() {
	ln := p.lines[p.pos]
	full := ln.text
	p.pos++
	for !strings.Contains(full, "}") && p.pos < len(p.lines) {
		full += " " + p.lines[p.pos].text
		p.pos++
	}
	inner := between(full, "{", "}")
	for _, part := range strings.Split(inner, ",") {
		w := strings.TrimSpace(part)
		if w != "" {
			builtinKeyword[w] = true
		}
	}
}

func (p *Parser) parseTopDef() error {
	ln := p.lines[p.pos]
	full := ln.text
	lineno := ln.lineno
	p.pos++
	for (strings.Contains(full, "{") && !strings.Contains(full, "}")) ||
		(!strings.Contains(full, "{") && strings.Contains(full, "[") && !strings.Contains(full, "]")) {
		if p.pos >= len(p.lines) {
			break
		}
		full += " " + p.lines[p.pos].text
		p.pos++
	}
	rest := strings.TrimSpace(strings.TrimPrefix(full, "def"))
	colon := strings.Index(rest, ":")
	if colon < 0 {
		return fmt.Errorf("line %d: def syntax error", lineno)
	}
	name := strings.TrimSpace(rest[:colon])
	rhs := strings.TrimSpace(rest[colon+1:])

	var inner string
	if strings.HasPrefix(rhs, "{") {
		if !strings.HasSuffix(rhs, "}") {
			return fmt.Errorf("line %d: def value must end with }", lineno)
		}
		inner = strings.TrimSpace(rhs[1 : len(rhs)-1])
	} else if strings.HasPrefix(rhs, "[") {
		if !strings.HasSuffix(rhs, "]") {
			return fmt.Errorf("line %d: def value must end with ]", lineno)
		}
		inner = strings.TrimSpace(rhs[1 : len(rhs)-1])
	} else {
		return fmt.Errorf("line %d: def value must be {…} or […]", lineno)
	}

	var items []string
	if strings.Contains(inner, ";") {
		return fmt.Errorf("line %d: def table cannot use ;", lineno)
	}
	if strings.Contains(inner, " or ") {
		items = strings.Split(inner, " or ")
	} else if strings.Contains(inner, ",") {
		items = strings.Split(inner, ",")
	} else if inner != "" {
		items = []string{inner}
	}

	switch name {
	case "Ignore":
		for _, it := range items {
			switch strings.TrimSpace(it) {
			case "space":
				p.cfg.Ignore[' '] = true
			case "tab":
				p.cfg.Ignore['\t'] = true
			case "enter":
				p.cfg.Ignore['\n'] = true
			case "return":
				p.cfg.Ignore['\r'] = true
			}
		}
		return nil
	case "keyword":
		for _, it := range items {
			it = strings.TrimSpace(it)
			if it != "" {
				builtinKeyword[it] = true
			}
		}
	}
	td := &TableDef{Name: name}
	for _, it := range items {
		it = strings.TrimSpace(it)
		if it != "" {
			td.Items = append(td.Items, it)
		}
	}
	p.cfg.TableDefs[name] = td
	return nil
}

func isBlockHeader(t string) bool {
	parts := strings.Fields(t)
	if len(parts) == 0 {
		return false
	}
	switch parts[0] {
	case "Match", "Deep", "Capture", "Capture_Semantics", "Star", "Any":
		return strings.Contains(t, ":")
	}
	return false
}

func parseBlockHeader(t string) (kind, name string) {
	t = strings.TrimSpace(t)
	t = strings.TrimSuffix(t, ":")
	t = strings.TrimSpace(t)
	parts := strings.Fields(t)
	if len(parts) == 0 {
		return "", ""
	}
	kind = parts[0]
	if len(parts) >= 2 {
		name = parts[1]
	}
	if name == "" {
		name = "block"
	}
	return
}

func resolveKind(kind string) string {
	switch kind {
	case "Match":
		return "match"
	case "Deep":
		return "deep"
	case "Capture":
		return "capture"
	case "Capture_Semantics":
		return "semantics"
	case "Star":
		return "star"
	case "Any":
		return "any"
	}
	return ""
}

func (p *Parser) parseBlock(header srcLine, parent *Block) (*Block, error) {
	kind, name := parseBlockHeader(header.text)
	k := resolveKind(kind)
	if k == "" {
		return nil, fmt.Errorf("line %d: unknown block kind %q", header.lineno, kind)
	}
	if p.seenNames[name] {
		return nil, fmt.Errorf("line %d: duplicate block name %q", header.lineno, name)
	}
	p.seenNames[name] = true
	p.blockNum++
	blk := &Block{
		Name:   name,
		Kind:   k,
		Num:    p.blockNum,
		Parent: parent,
	}
	p.pos++
	parentIndent := header.indent
	for p.pos < len(p.lines) {
		ln := p.lines[p.pos]
		if ln.indent <= parentIndent {
			break
		}
		if isBlockHeader(ln.text) {
			child, err := p.parseBlock(ln, blk)
			if err != nil {
				return nil, err
			}
			if child != nil {
				blk.Children = append(blk.Children, child)
			}
			continue
		}
		node, err := p.parseStmt(ln)
		if err != nil {
			return nil, err
		}
		if node != nil {
			blk.Stmts = append(blk.Stmts, node)
		}
	}
	return blk, nil
}

func (p *Parser) parseStmt(ln srcLine) (Node, error) {
	t := ln.text
	p.pos++

	if t == "State" || strings.HasPrefix(t, "State ") {
		rest := strings.TrimSpace(strings.TrimPrefix(t, "State"))
		parts := strings.Fields(rest)
		ss := &StateStmt{}
		if len(parts) >= 1 {
			ss.Object = parts[0]
			ss.Fields = parts[1:]
		}
		return ss, nil
	}
	if t == "Stop" || strings.HasPrefix(t, "Stop ") {
		return &StopStmt{}, nil
	}
	if strings.HasPrefix(t, "Status_init ") {
		return &AssignStmt{
			Target: strings.TrimSpace(strings.TrimPrefix(t, "Status_init")),
			Value:  "true", Op: "=",
		}, nil
	}
	if strings.HasPrefix(t, "Append ") {
		rest := strings.TrimSpace(strings.TrimPrefix(t, "Append"))
		eq := strings.Index(rest, "=")
		if eq < 0 {
			return nil, fmt.Errorf("line %d: Append syntax error", ln.lineno)
		}
		return &AppendStmt{
			Target: strings.TrimSpace(rest[:eq]),
			Value:  strings.TrimSpace(rest[eq+1:]),
		}, nil
	}
	if strings.HasPrefix(t, "star ") {
		rest := strings.TrimSpace(strings.TrimPrefix(t, "star"))
		parts := strings.Fields(rest)
		if len(parts) < 2 {
			return nil, fmt.Errorf("line %d: star syntax error", ln.lineno)
		}
		ss := &StarStmt{Target: parts[0], Dir: parts[1]}
		for _, pp := range parts {
			if strings.HasPrefix(pp, "mode=") {
				ss.Mode = strings.TrimPrefix(pp, "mode=")
			}
			if pp == "all" {
				ss.Mode = "all"
			}
		}
		if idx := strings.Index(rest, "["); idx >= 0 {
			end := strings.Index(rest, "]")
			if end > idx {
				inner := rest[idx+1 : end]
				for _, item := range strings.Split(inner, ",") {
					item = strings.TrimSpace(item)
					if item != "" {
						ss.LookFor = append(ss.LookFor, item)
					}
				}
			}
		}
		body, err := p.parseInnerStmts(ln.indent + 1)
		if err != nil {
			return nil, err
		}
		ss.Body = body
		return ss, nil
	}
	if strings.HasPrefix(t, "if ") || strings.HasPrefix(t, "if(") {
		return p.parseIf(ln)
	}
	if strings.HasPrefix(t, "Status") {
		return parseAssign(strings.TrimSpace(strings.TrimPrefix(t, "Status"))), nil
	}
	if strings.HasSuffix(t, "++") {
		return &IncrStmt{Target: strings.TrimSpace(strings.TrimSuffix(t, "++"))}, nil
	}
	if strings.HasSuffix(t, "--") {
		return &DecrStmt{Target: strings.TrimSpace(strings.TrimSuffix(t, "--"))}, nil
	}
	if strings.Contains(t, "+") && !strings.Contains(t, "++") && !strings.Contains(t, "+=") {
		idx := strings.LastIndex(t, "+")
		if idx > 0 && idx < len(t)-1 {
			left := strings.TrimSpace(t[:idx])
			right := strings.TrimSpace(t[idx+1:])
			if isInt(right) {
				n, _ := strconv.Atoi(right)
				return &AddIntStmt{Target: left, Delta: n}, nil
			}
		}
	}
	if strings.Contains(t, "+=") {
		eq := strings.Index(t, "+=")
		return &AssignStmt{
			Target: strings.TrimSpace(t[:eq]),
			Value:  strings.TrimSpace(t[eq+2:]), Op: "+",
		}, nil
	}
	if strings.Contains(t, "-=") {
		eq := strings.Index(t, "-=")
		return &AssignStmt{
			Target: strings.TrimSpace(t[:eq]),
			Value:  strings.TrimSpace(t[eq+2:]), Op: "-",
		}, nil
	}
	if strings.Contains(t, "=") {
		return parseAssign(t), nil
	}
	return nil, nil
}

func (p *Parser) parseIf(ln srcLine) (Node, error) {
	ifs := &IfStmt{}
	baseIndent := ln.indent

	condStr := strings.TrimSpace(strings.TrimPrefix(ln.text, "if"))
	if strings.HasPrefix(condStr, "(") && strings.HasSuffix(condStr, ")") {
		condStr = strings.TrimSpace(condStr[1 : len(condStr)-1])
	}
	cond, err := p.parseCond(condStr)
	if err != nil {
		return nil, err
	}
	then, err := p.parseInnerStmts(baseIndent + 1)
	if err != nil {
		return nil, err
	}
	ifs.Branches = append(ifs.Branches, IfBranch{Cond: cond, Then: then})

	for p.pos < len(p.lines) {
		nxt := p.lines[p.pos]
		if nxt.indent != baseIndent {
			break
		}
		if strings.HasPrefix(nxt.text, "elif ") {
			p.pos++
			condStr := strings.TrimSpace(strings.TrimPrefix(nxt.text, "elif"))
			if strings.HasPrefix(condStr, "(") && strings.HasSuffix(condStr, ")") {
				condStr = strings.TrimSpace(condStr[1 : len(condStr)-1])
			}
			c, err := p.parseCond(condStr)
			if err != nil {
				return nil, err
			}
			th, err := p.parseInnerStmts(baseIndent + 1)
			if err != nil {
				return nil, err
			}
			ifs.Branches = append(ifs.Branches, IfBranch{Cond: c, Then: th})
			continue
		}
		if nxt.text == "else" || strings.HasPrefix(nxt.text, "else ") {
			p.pos++
			els, err := p.parseInnerStmts(baseIndent + 1)
			if err != nil {
				return nil, err
			}
			ifs.Else = els
			break
		}
		break
	}
	return ifs, nil
}

func (p *Parser) parseInnerStmts(minIndent int) ([]Node, error) {
	var stmts []Node
	for p.pos < len(p.lines) {
		ln := p.lines[p.pos]
		if ln.indent < minIndent {
			break
		}
		if isBlockHeader(ln.text) {
			break
		}
		node, err := p.parseStmt(ln)
		if err != nil {
			return nil, err
		}
		if node != nil {
			stmts = append(stmts, node)
		}
	}
	return stmts, nil
}

func (p *Parser) parseCond(s string) (Node, error) {
	s = strings.TrimSpace(s)

	if idx := findOutsideString(s, " and "); idx >= 0 {
		l, err := p.parseCond(s[:idx])
		if err != nil {
			return nil, err
		}
		r, err := p.parseCond(s[idx+5:])
		if err != nil {
			return nil, err
		}
		return &LogicExpr{Op: "and", Left: l, Right: r}, nil
	}
	if idx := findOutsideString(s, " or "); idx >= 0 {
		l, err := p.parseCond(s[:idx])
		if err != nil {
			return nil, err
		}
		r, err := p.parseCond(s[idx+4:])
		if err != nil {
			return nil, err
		}
		return &LogicExpr{Op: "or", Left: l, Right: r}, nil
	}
	if strings.HasPrefix(s, "not ") {
		inner, err := p.parseCond(strings.TrimSpace(strings.TrimPrefix(s, "not")))
		if err != nil {
			return nil, err
		}
		return &NotExpr{Inner: inner}, nil
	}

	if strings.HasPrefix(s, "Capture ") {
		return p.parseCaptureCond(s)
	}
	if strings.HasPrefix(s, "Deep ") || strings.HasPrefix(s, "Deep(") {
		return p.parseDeepCond(s)
	}
	if strings.HasPrefix(s, "Match ") || strings.HasPrefix(s, "Match(") {
		return p.parseMatchCond(s)
	}
	if strings.HasPrefix(s, "Star ") {
		rest := strings.TrimSpace(strings.TrimPrefix(s, "Star"))
		parts := strings.Fields(rest)
		if len(parts) < 2 {
			return nil, fmt.Errorf("Star syntax error")
		}
		sc := &StarCond{Target: parts[0], Dir: parts[1]}
		for _, pp := range parts {
			if strings.HasPrefix(pp, "mode=") {
				sc.Mode = strings.TrimPrefix(pp, "mode=")
			}
			if pp == "all" {
				sc.Mode = "all"
			}
		}
		if idx := strings.Index(rest, "["); idx >= 0 {
			end := strings.Index(rest, "]")
			if end > idx {
				inner := rest[idx+1 : end]
				for _, item := range strings.Split(inner, ",") {
					item = strings.TrimSpace(item)
					if item != "" {
						sc.LookFor = append(sc.LookFor, item)
					}
				}
			}
		}
		return sc, nil
	}

	if idx := findOutsideString(s, "!="); idx >= 0 {
		return &StatusExpr{Left: strings.TrimSpace(s[:idx]), Op: "!=", Right: strings.TrimSpace(s[idx+2:])}, nil
	}
	if idx := findOutsideString(s, "=="); idx >= 0 {
		return &StatusExpr{Left: strings.TrimSpace(s[:idx]), Op: "=", Right: strings.TrimSpace(s[idx+2:])}, nil
	}
	if idx := findOutsideString(s, "="); idx >= 0 {
		return &StatusExpr{Left: strings.TrimSpace(s[:idx]), Op: "=", Right: strings.TrimSpace(s[idx+1:])}, nil
	}
	return &StatusExpr{Left: s, Op: "truthy"}, nil
}

func (p *Parser) parseCaptureCond(s string) (Node, error) {
	rest := strings.TrimSpace(strings.TrimPrefix(s, "Capture"))
	if strings.HasPrefix(rest, "-->") {
		rest = strings.TrimSpace(rest[3:])
	}
	mc := &MatchCond{IsCap: true}

	if strings.HasPrefix(rest, "Re(") {
		re, src, names, err := parseRe(rest)
		if err != nil {
			return nil, err
		}
		mc.Re = re
		mc.ReSrc = src
		mc.ReNamed = names
		return mc, nil
	}
	if strings.Contains(rest, "=") && strings.Contains(rest, "\"") {
		mc.Class = "__assign__"
		mc.Target = rest
		mc.IsSem = true
		return mc, nil
	}
	if strings.Contains(rest, "$*") {
		mc.IsSem = true
		mc.Target = rest
		return mc, nil
	}
	parts := strings.Fields(rest)
	if len(parts) >= 1 {
		if td := parseTableInline(parts[0]); td != nil {
			mc.Table = td
			mc.IsSem = true
			return mc, nil
		}
	}
	mc.Target = rest
	mc.IsSem = true
	return mc, nil
}

func (p *Parser) parseDeepCond(s string) (Node, error) {
	rest := strings.TrimSpace(strings.TrimPrefix(s, "Deep"))
	for _, ss := range []string{"<<-->>", "<<->>", "<-->", "<->"} {
		if idx := strings.Index(rest, ss); idx >= 0 {
			left := strings.TrimSpace(rest[:idx])
			right := strings.TrimSpace(rest[idx+len(ss):])
			if left == "" || right == "" {
				return nil, fmt.Errorf("Deep pair left/right cannot be empty: %q", s)
			}
			greed, cross := parseDeepSym(ss)
			dc := &DeepCond{Greed: greed, CrossLine: cross}
			if left == "|all|" {
				dc.LeftIsAll = true
			} else if strings.HasPrefix(left, "@") {
				dc.LeftClass = strings.TrimPrefix(left, "@")
			} else if strings.HasPrefix(left, "Re(") {
				re, _, _, err := parseRe(left)
				if err != nil {
					return nil, err
				}
				dc.LeftIsRe = re
			} else {
				dc.Left = left
			}
			if right == "|all|" {
				dc.RightIsAll = true
			} else if strings.HasPrefix(right, "@") {
				dc.RightClass = strings.TrimPrefix(right, "@")
			} else if strings.HasPrefix(right, "Re(") {
				re, _, _, err := parseRe(right)
				if err != nil {
					return nil, err
				}
				dc.RightIsRe = re
			} else {
				dc.Right = right
			}
			return dc, nil
		}
	}
	return nil, fmt.Errorf("Deep condition missing pair symbol")
}

func (p *Parser) parseMatchCond(s string) (Node, error) {
	rest := strings.TrimSpace(strings.TrimPrefix(s, "Match"))

	for _, ss := range []string{"-->", "==>", "->", "=>"} {
		if idx := findOutsideString(rest, ss); idx >= 0 {
			left := strings.TrimSpace(rest[:idx])
			right := strings.TrimSpace(rest[idx+len(ss):])
			if strings.HasPrefix(left, "[") && strings.HasSuffix(left, "]") {
				mc := &MatchCond{IsSeq: true, Op: ss}
				mc.Greed = (ss == "->" || ss == "==>")
				if right != "" && strings.HasPrefix(right, "[") && strings.HasSuffix(right, "]") {
					segs, err := parseSeqList(right)
					if err != nil {
						return nil, err
					}
					mc.Right = segs
				}
				segs, err := parseSeqList(left)
				if err != nil {
					return nil, err
				}
				mc.Left = segs
				return mc, nil
			}
			greed := (ss == "->" || ss == "==>")
			return p.buildMatchCond(left, right, greed, ss)
		}
	}

	left := rest
	if left != "" && !strings.HasPrefix(left, "@") && !strings.HasPrefix(left, "Re(") {
		td := parseTableInline(left)
		if td == nil {
			return &MatchCond{BlockRef: left, Target: left}, nil
		}
	}
	return p.buildMatchCond(left, "", false, "")
}

func (p *Parser) buildMatchCond(left, right string, greed bool, sep string) (Node, error) {
	mc := &MatchCond{Greed: greed, Op: sep}
	if left == "|all|" {
		mc.IsAll = true
	} else if strings.HasPrefix(left, "@") {
		cls := strings.TrimPrefix(left, "@")
		if !builtinClassNames[cls] {
			return nil, fmt.Errorf("unknown class @%s", cls)
		}
		mc.Class = cls
	} else if left != "" && right == "" {
		mc.Target = left
	}
	if right == "" {
		return mc, nil
	}
	if strings.HasPrefix(right, "Re(") {
		re, src, names, err := parseRe(right)
		if err != nil {
			return nil, err
		}
		mc.Re = re
		mc.ReSrc = src
		mc.ReNamed = names
		return mc, nil
	}
	if td := parseTableInline(right); td != nil {
		mc.Table = td
		return mc, nil
	}
	if strings.HasPrefix(right, "[") && strings.HasSuffix(right, "]") {
		segs, err := parseSeqList(right)
		if err == nil {
			mc.IsSeq = true
			mc.Right = segs
			return mc, nil
		}
	}
	mc.Target = right
	return mc, nil
}

func parseAssign(s string) Node {
	s = strings.TrimSpace(s)
	alias := ""
	if idx := strings.Index(s, "=="); idx >= 0 {
		alias = strings.TrimSpace(s[idx+2:])
		s = strings.TrimSpace(s[:idx])
	}
	eq := strings.Index(s, "=")
	if eq < 0 {
		return nil
	}
	target := strings.TrimSpace(s[:eq])
	value := strings.TrimSpace(s[eq+1:])
	base, capID, attr := parseAssignTarget(target)
	return &AssignStmt{
		Target: base, Value: value, Alias: alias, Op: "=",
		CapID: capID, Attr: attr,
	}
}

// ---------- 6. Matcher ----------

type memoKey struct {
	block string
	pos   int
}

type MatchResult struct {
	Width int
	OK    bool
}

type Matcher struct {
	state    *StateStore
	exec     *Executor
	debug    bool
	quiet    bool
	json     bool
	blocks   map[string]*Block
	tables   map[string]*TableDef
	depth    int
	maxDepth int
	memo     map[memoKey]MatchResult
	inFlight map[memoKey]bool
	startAt  time.Time
}

func NewMatcher(state *StateStore, debug bool) *Matcher {
	m := &Matcher{
		state:    state,
		debug:    debug,
		blocks:   make(map[string]*Block),
		tables:   make(map[string]*TableDef),
		maxDepth: 128,
		memo:     make(map[memoKey]MatchResult),
		inFlight: make(map[memoKey]bool),
		startAt:  time.Now(),
	}
	m.exec = NewExecutor(state, debug)
	return m
}

func (m *Matcher) D(f string, a ...interface{}) {
	if m.debug && !m.json {
		fmt.Printf(C("[Db] ", Dim+SoftBlue)+f+"\n", a...)
	}
}

func (m *Matcher) E(f string, a ...interface{}) {
	if !m.json {
		fmt.Printf(C("[Db.error] ", SoftRed)+f+"\n", a...)
	}
}

func (m *Matcher) SetQuiet(q bool) { m.quiet = q }
func (m *Matcher) SetJSON(j bool)  { m.json = j }

func (m *Matcher) RegisterTable(name string, td *TableDef) {
	m.tables[name] = td
}

func (m *Matcher) RegisterBlock(b *Block) {
	if _, ok := m.blocks[b.Name]; ok {
		return
	}
	m.blocks[b.Name] = b
	for _, c := range b.Children {
		m.RegisterBlock(c)
	}
}

func (m *Matcher) resolveTable(td *TableDef) *TableDef {
	if td == nil {
		return nil
	}
	if !td.IsEmpty {
		return td
	}
	if reg, ok := m.tables[td.Name]; ok {
		return reg
	}
	return nil
}

func (m *Matcher) setCtx(engine string, b *Block, pos int, tok *Token, count int, target string) {
	m.exec.curEngine = engine
	m.exec.curNum = b.Num
	m.exec.curBlock = b.Name
	m.exec.curPos = pos
	m.exec.curTok = tok
	if count < 1 {
		count = 1
	}
	m.exec.curCount = count
	m.exec.curTarget = target
	if tok != nil {
		m.exec.curValue = tok.Text
		line := tok.Line - 1
		if line < 0 {
			line = 0
		}
		m.exec.curLine = line
	} else {
		m.exec.curValue = ""
		m.exec.curLine = 0
	}
}

func (m *Matcher) RunBlock(b *Block, toks []Token) {
	if !m.quiet && !m.json {
		head := C(fmt.Sprintf("[%s#%d]", b.Name, b.Num), SoftCyan)
		fmt.Printf("%s=== block %s (%s) ===%s\n",
			Dim, head, C(b.Kind, SoftBlue), Reset)
	}
	m.exec.Reset()
	m.state.undo = m.state.undo[:0]
	m.exec.stateCount = make(map[string]int)
	m.memo = make(map[memoKey]MatchResult)
	m.inFlight = make(map[memoKey]bool)
	m.depth = 0
	m.runSelf(b, toks)
}

func (m *Matcher) runSelf(b *Block, toks []Token) {
	switch b.Kind {
	case "deep":
		m.runDeep(b, toks)
	case "capture":
		m.runCapture(b, toks)
	case "semantics":
		m.runSemantics(b, toks)
	case "star":
		m.runStar(b, toks)
	case "any":
		m.runAny(b, toks)
	default:
		m.runMatch(b, toks)
	}
}

func (m *Matcher) runMatch(b *Block, toks []Token) {
	for _, s := range b.Stmts {
		if _, ok := s.(*IfStmt); ok {
			continue
		}
		m.setCtx("Match", b, 0, nil, 1, "")
		m.exec.ExecStmt(s, nil)
		if m.exec.Stopped() {
			return
		}
	}
	pos := 0
	for pos < len(toks) {
		if m.exec.Stopped() {
			return
		}
		m.setCtx("Match", b, pos, &toks[pos], 1, "")
		r := m.tryBlock(b, toks, pos)
		if r.OK {
			if r.Width > 0 {
				pos += r.Width
			} else {
				pos++
			}
			continue
		}
		pos++
	}
}

func (m *Matcher) tryBlock(b *Block, toks []Token, pos int) MatchResult {
	if m.depth > m.maxDepth {
		return MatchResult{0, false}
	}
	key := memoKey{b.Name, pos}
	if r, ok := m.memo[key]; ok {
		return r
	}
	if m.inFlight[key] {
		return MatchResult{0, false}
	}
	m.inFlight[key] = true
	m.depth++
	defer func() {
		m.depth--
		delete(m.inFlight, key)
	}()
	var best MatchResult
	for _, s := range b.Stmts {
		ifs, ok := s.(*IfStmt)
		if !ok {
			continue
		}
		r := m.tryRule(b, ifs, toks, pos)
		if r.OK {
			best = r
			break
		}
	}
	m.memo[key] = best
	return best
}

func (m *Matcher) tryRule(b *Block, ifs *IfStmt, toks []Token, pos int) MatchResult {
	var tok *Token
	if pos < len(toks) {
		tok = &toks[pos]
	}
	for _, br := range ifs.Branches {
		cp := m.state.Checkpoint()
		r := m.tryCondR(br.Cond, toks, pos)
		if r.OK {
			if tok != nil {
				m.state.Set("$self", tok.Text)
			}
			target := extractTarget(br.Cond)
			m.setCtx("Match", b, pos, tok, r.Width, target)
			m.exec.ExecStmts(br.Then, tok)
			return r
		}
		m.state.Rollback(cp)
	}
	if len(ifs.Else) > 0 {
		if tok != nil {
			m.state.Set("$self", tok.Text)
		}
		m.setCtx("Match", b, pos, tok, 1, "")
		m.exec.ExecStmts(ifs.Else, tok)
		return MatchResult{0, true}
	}
	return MatchResult{0, false}
}

func (m *Matcher) tryCondR(cond Node, toks []Token, pos int) MatchResult {
	switch c := cond.(type) {
	case *MatchCond:
		return m.tryMatchR(c, toks, pos)
	case *StatusExpr:
		if m.evalStatus(c) {
			return MatchResult{0, true}
		}
		return MatchResult{0, false}
	case *LogicExpr:
		if c.Op == "and" {
			l := m.tryCondR(c.Left, toks, pos)
			if !l.OK {
				return MatchResult{0, false}
			}
			r := m.tryCondR(c.Right, toks, pos+l.Width)
			if !r.OK {
				return MatchResult{0, false}
			}
			return MatchResult{l.Width + r.Width, true}
		}
		if l := m.tryCondR(c.Left, toks, pos); l.OK {
			return l
		}
		return m.tryCondR(c.Right, toks, pos)
	case *NotExpr:
		r := m.tryCondR(c.Inner, toks, pos)
		if r.OK {
			return MatchResult{0, false}
		}
		return MatchResult{0, true}
	case *StarCond:
		if m.tryStar(c, toks, pos) {
			return MatchResult{0, true}
		}
		return MatchResult{0, false}
	case *DeepCond:
		if m.tryDeep(c, toks, pos) {
			return MatchResult{0, true}
		}
		return MatchResult{0, false}
	}
	return MatchResult{0, false}
}

func (m *Matcher) tryCond(cond Node, toks []Token, pos int) bool {
	return m.tryCondR(cond, toks, pos).OK
}

func (m *Matcher) tryMatchR(mc *MatchCond, toks []Token, pos int) MatchResult {
	if mc.BlockRef != "" {
		if blk, ok := m.blocks[mc.BlockRef]; ok {
			oldEngine := m.exec.curEngine
			oldNum := m.exec.curNum
			oldBlock := m.exec.curBlock
			m.exec.curEngine = "Match"
			m.exec.curNum = blk.Num
			m.exec.curBlock = blk.Name
			r := m.tryBlock(blk, toks, pos)
			m.exec.curEngine = oldEngine
			m.exec.curNum = oldNum
			m.exec.curBlock = oldBlock
			return r
		}
		if pos >= len(toks) {
			return MatchResult{0, false}
		}
		if toks[pos].Text == mc.BlockRef {
			return MatchResult{1, true}
		}
		return MatchResult{0, false}
	}
	if mc.IsSeq {
		return m.trySeq(mc, toks, pos)
	}
	if pos >= len(toks) {
		return MatchResult{0, false}
	}
	t := &toks[pos]
	if mc.Class != "" && mc.Class != t.Class {
		return MatchResult{0, false}
	}
	if mc.Re != nil {
		sub := mc.Re.FindStringSubmatch(t.Text)
		if sub == nil {
			return MatchResult{0, false}
		}
		for i := 1; i < len(sub); i++ {
			m.state.Set(fmt.Sprintf("$%d", i), sub[i])
		}
		for i, name := range mc.ReNamed {
			if name != "" && i < len(sub) {
				m.state.Set("$"+name, sub[i])
			}
		}
		return MatchResult{1, true}
	}
	if mc.Table != nil {
		td := m.resolveTable(mc.Table)
		if td == nil {
			return MatchResult{0, false}
		}
		if !td.Contains(t.Text) {
			return MatchResult{0, false}
		}
		return MatchResult{1, true}
	}
	if mc.Target == "" {
		return MatchResult{1, true}
	}
	if mc.Greed {
		if strings.Contains(t.Text, mc.Target) {
			return MatchResult{1, true}
		}
		return MatchResult{0, false}
	}
	if t.Text == mc.Target {
		return MatchResult{1, true}
	}
	return MatchResult{0, false}
}

func (m *Matcher) trySeq(mc *MatchCond, toks []Token, pos int) MatchResult {
	if len(mc.Left) == 0 {
		return MatchResult{0, false}
	}
	if pos+len(mc.Left) > len(toks) {
		return MatchResult{0, false}
	}
	for i, seg := range mc.Left {
		if !m.matchSegment(seg, &toks[pos+i]) {
			return MatchResult{0, false}
		}
	}
	if len(mc.Right) > 0 {
		if len(mc.Right) != len(mc.Left) {
			return MatchResult{0, false}
		}
		for i, seg := range mc.Right {
			if !m.matchSegment(seg, &toks[pos+i]) {
				return MatchResult{0, false}
			}
		}
	}
	return MatchResult{len(mc.Left), true}
}

func (m *Matcher) matchSegment(seg Segment, tok *Token) bool {
	for _, item := range seg.Items {
		if item.Any {
			return true
		}
		if item.Re != nil {
			if item.Re.MatchString(tok.Text) {
				return true
			}
			continue
		}
		if item.Table != nil {
			td := m.resolveTable(item.Table)
			if td != nil && td.Contains(tok.Text) {
				return true
			}
			continue
		}
		if item.IsClass {
			if item.Class == tok.Class {
				return true
			}
		} else {
			if item.Target == tok.Text {
				return true
			}
		}
	}
	return false
}

func (m *Matcher) tryStar(sc *StarCond, toks []Token, pos int) bool {
	if pos >= len(toks) {
		return false
	}
	t := &toks[pos]
	if t.Text != sc.Target && t.Class != sc.Target {
		return false
	}
	crossLine := strings.Contains(sc.Dir, ">>") || strings.Contains(sc.Dir, "<<")
	lookRight := strings.Contains(sc.Dir, ">")
	lookLeft := strings.Contains(sc.Dir, "<")
	var visible []*Token
	if lookRight {
		for j := pos + 1; j < len(toks); j++ {
			if !crossLine && toks[j].Line != t.Line {
				break
			}
			visible = append(visible, &toks[j])
		}
	}
	if lookLeft {
		for j := pos - 1; j >= 0; j-- {
			if !crossLine && toks[j].Line != t.Line {
				break
			}
			visible = append(visible, &toks[j])
		}
	}
	matched := func(lf string) bool {
		for _, v := range visible {
			if builtinClassNames[lf] {
				if v.Class == lf {
					return true
				}
			} else if v.Text == lf {
				return true
			}
		}
		return false
	}
	if sc.Mode == "all" {
		for _, lf := range sc.LookFor {
			if !matched(lf) {
				return false
			}
		}
		return true
	}
	for _, lf := range sc.LookFor {
		if matched(lf) {
			return true
		}
	}
	return false
}

func (m *Matcher) tryDeep(dc *DeepCond, toks []Token, pos int) bool {
	if pos >= len(toks) {
		return false
	}
	t := &toks[pos]
	if !m.matchLeft(dc, t) {
		return false
	}
	for j := pos + 1; j < len(toks); j++ {
		if !dc.CrossLine && toks[j].Line != t.Line {
			break
		}
		if m.matchRight(dc, &toks[j]) {
			return true
		}
	}
	return false
}

func (m *Matcher) matchLeft(dc *DeepCond, t *Token) bool {
	if dc.LeftIsAll {
		return true
	}
	if dc.LeftClass != "" {
		return t.Class == dc.LeftClass
	}
	if dc.LeftIsRe != nil {
		return dc.LeftIsRe.MatchString(t.Text)
	}
	return t.Text == dc.Left
}

func (m *Matcher) matchRight(dc *DeepCond, t *Token) bool {
	if dc.RightIsAll {
		return true
	}
	if dc.RightClass != "" {
		return t.Class == dc.RightClass
	}
	if dc.RightIsRe != nil {
		return dc.RightIsRe.MatchString(t.Text)
	}
	return t.Text == dc.Right
}

func (m *Matcher) evalStatus(se *StatusExpr) bool {
	if se.Op == "truthy" {
		return m.state.GetBool(se.Left)
	}
	right, _ := unquote(se.Right)
	v, ok := m.state.Get(se.Left)
	if !ok {
		return right == "false" || right == "0" || right == ""
	}
	switch x := v.(type) {
	case bool:
		want := right == "true" || right == "1" || right == "yes"
		if se.Op == "!=" {
			return x != want
		}
		return x == want
	case int:
		iv, _ := strconv.Atoi(right)
		if se.Op == "!=" {
			return x != iv
		}
		return x == iv
	case float64:
		fv, _ := strconv.ParseFloat(right, 64)
		if se.Op == "!=" {
			return x != fv
		}
		return x == fv
	case string:
		if se.Op == "!=" {
			return x != right
		}
		return x == right
	default:
		got := fmt.Sprintf("%v", v)
		if se.Op == "!=" {
			return got != right
		}
		return got == right
	}
}

func (m *Matcher) runDeep(b *Block, toks []Token) {
	for _, s := range b.Stmts {
		if _, ok := s.(*IfStmt); ok {
			continue
		}
		m.setCtx("Deep", b, 0, nil, 1, "")
		m.exec.ExecStmt(s, nil)
		if m.exec.Stopped() {
			return
		}
	}
	for _, s := range b.Stmts {
		ifs, ok := s.(*IfStmt)
		if !ok {
			continue
		}
		conds := collectDeepConds(ifs)
		for _, item := range conds {
			m.scanDeep(b, item.cond, item.then, toks, 0, len(toks))
		}
	}
}

type deepPair struct {
	cond *DeepCond
	then []Node
}

func collectDeepConds(ifs *IfStmt) []deepPair {
	var out []deepPair
	for _, br := range ifs.Branches {
		out = append(out, collectDeepFromCond(br.Cond, br.Then)...)
	}
	return out
}

func collectDeepFromCond(cond Node, then []Node) []deepPair {
	switch c := cond.(type) {
	case *DeepCond:
		return []deepPair{{c, then}}
	case *LogicExpr:
		if c.Op == "and" {
			l := collectDeepFromCond(c.Left, then)
			r := collectDeepFromCond(c.Right, then)
			return append(l, r...)
		}
		l := collectDeepFromCond(c.Left, then)
		if len(l) > 0 {
			return l
		}
		return collectDeepFromCond(c.Right, then)
	}
	return nil
}

func (m *Matcher) scanDeep(b *Block, dc *DeepCond, then []Node, toks []Token, start, end int) {
	i := start
	for i < end {
		if m.exec.Stopped() {
			return
		}
		t := &toks[i]
		if !m.matchLeft(dc, t) {
			i++
			continue
		}
		rpos := -1
		for j := i + 1; j < end; j++ {
			rj := &toks[j]
			if !dc.CrossLine && rj.Line != t.Line {
				break
			}
			if m.matchRight(dc, rj) {
				rpos = j
				if !dc.Greed {
					break
				}
			}
		}
		if rpos < 0 {
			m.state.Set("$1", i)
			m.state.Set("$2", -1)
			i++
			continue
		}
		m.state.Set("$1", i)
		m.state.Set("$2", rpos)
		m.setCtx("Deep", b, i, t, rpos-i+1, dc.Left)
		m.exec.ExecStmts(then, t)

		snap1, _ := m.state.Get("$1")
		snap2, _ := m.state.Get("$2")
		m.scanDeep(b, dc, then, toks, i+1, rpos)
		if snap1 != nil {
			m.state.Set("$1", snap1)
		}
		if snap2 != nil {
			m.state.Set("$2", snap2)
		}

		i = rpos + 1
	}
}

func (m *Matcher) runCapture(b *Block, toks []Token) {
	needSpace := false
	for _, s := range b.Stmts {
		ifs, ok := s.(*IfStmt)
		if !ok {
			continue
		}
		for _, br := range ifs.Branches {
			if mc, ok := br.Cond.(*MatchCond); ok {
				if mc.IsSem && strings.Contains(mc.Target, "$*") {
					needSpace = true
					break
				}
			}
		}
		if needSpace {
			break
		}
	}

	var parts []string
	for _, t := range toks {
		parts = append(parts, t.Text)
	}
	var input string
	if needSpace {
		input = strings.Join(parts, " ")
	} else {
		input = strings.Join(parts, "")
	}

	for _, s := range b.Stmts {
		ifs, ok := s.(*IfStmt)
		if !ok {
			continue
		}
		hit := false
		for _, br := range ifs.Branches {
			mc, ok := br.Cond.(*MatchCond)
			if !ok {
				continue
			}
			target := ""
			if mc.ReSrc != "" {
				target = "Re(" + mc.ReSrc + ")"
			}
			if mc.Re != nil {
				sub := mc.Re.FindStringSubmatch(input)
				if sub == nil {
					continue
				}
				for i := 1; i < len(sub); i++ {
					m.state.Set(fmt.Sprintf("$%d", i-1), sub[i])
				}
				m.state.Set(b.Name+".match", sub[0])
				m.state.Set(b.Name+".count", len(sub)-1)
				fakeTok := &Token{Text: input, Class: "Text", Line: 1, Col: 1}
				m.setCtx("Capture", b, 0, fakeTok, len(sub), target)
				m.exec.ExecStmts(br.Then, nil)
				hit = true
				break
			} else if mc.Class == "__assign__" {
				idx := strings.Index(input, "=")
				if idx < 0 {
					continue
				}
				left := strings.TrimSpace(input[:idx])
				right, _ := unquote(strings.TrimSpace(input[idx+1:]))
				m.state.Set("$0", left)
				m.state.Set("$1", right)
				m.state.Set(b.Name+".match", input)
				fakeTok := &Token{Text: input, Class: "Text", Line: 1, Col: 1}
				m.setCtx("Capture", b, 0, fakeTok, 2, target)
				m.exec.ExecStmts(br.Then, nil)
				hit = true
				break
			} else if mc.IsSem {
				if strings.Contains(mc.Target, "$*") {
					fields := strings.Fields(input)
					for i, f := range fields {
						m.state.Set(fmt.Sprintf("$%d", i), f)
					}
					fakeTok := &Token{Text: input, Class: "Text", Line: 1, Col: 1}
					m.setCtx("Capture", b, 0, fakeTok, len(fields), target)
					m.exec.ExecStmts(br.Then, nil)
					hit = true
					break
				} else if mc.Table != nil {
					fields := strings.Fields(input)
					if len(fields) >= 1 {
						td := m.resolveTable(mc.Table)
						if td != nil && td.Contains(fields[0]) {
							m.state.Set("$0", fields[0])
							if len(fields) >= 2 {
								m.state.Set("$1", fields[1])
							}
							m.state.Set("type{}", fields[0])
							fakeTok := &Token{Text: input, Class: "Text", Line: 1, Col: 1}
							m.setCtx("Capture", b, 0, fakeTok, len(fields), target)
							m.exec.ExecStmts(br.Then, nil)
							hit = true
							break
						}
					}
				}
			}
		}
		if !hit && len(ifs.Else) > 0 {
			m.exec.ExecStmts(ifs.Else, nil)
		}
	}
}

func (m *Matcher) runSemantics(b *Block, toks []Token) {
	var sb strings.Builder
	lastLine := -1
	for _, t := range toks {
		if lastLine != -1 && t.Line != lastLine {
			sb.WriteString("\n")
		} else if lastLine != -1 {
			sb.WriteString(" ")
		}
		sb.WriteString(t.Text)
		lastLine = t.Line
	}
	for _, line := range strings.Split(sb.String(), "\n") {
		fields := strings.Fields(line)
		if len(fields) == 0 {
			continue
		}
		for _, s := range b.Stmts {
			ifs, ok := s.(*IfStmt)
			if !ok {
				continue
			}
			hit := false
			for _, br := range ifs.Branches {
				mc, ok := br.Cond.(*MatchCond)
				if !ok {
					continue
				}
				target := ""
				if mc.ReSrc != "" {
					target = "Re(" + mc.ReSrc + ")"
				}
				if mc.Class == "__assign__" {
					idx := strings.Index(line, "=")
					if idx < 0 {
						continue
					}
					left := strings.TrimSpace(line[:idx])
					right, _ := unquote(strings.TrimSpace(line[idx+1:]))
					m.state.Set("$0", left)
					m.state.Set("$1", right)
					m.state.Set(b.Name+".match", line)
					fakeTok := &Token{Text: line, Class: "Text", Line: 1, Col: 1}
					m.setCtx("Capture_Semantics", b, 0, fakeTok, 2, target)
					m.exec.ExecStmts(br.Then, nil)
					hit = true
					break
				}
				if mc.Table != nil {
					td := m.resolveTable(mc.Table)
					if td == nil {
						continue
					}
					if len(fields) >= 1 && td.Contains(fields[0]) {
						m.state.Set("$0", fields[0])
						if len(fields) >= 2 {
							m.state.Set("$1", fields[1])
						}
						m.state.Set("type{}", fields[0])
						fakeTok := &Token{Text: line, Class: "Text", Line: 1, Col: 1}
						m.setCtx("Capture_Semantics", b, 0, fakeTok, len(fields), target)
						m.exec.ExecStmts(br.Then, nil)
						hit = true
						break
					}
				}
			}
			if !hit && len(ifs.Else) > 0 {
				m.exec.ExecStmts(ifs.Else, nil)
			}
		}
	}
}

func (m *Matcher) runStar(b *Block, toks []Token) {
	for _, s := range b.Stmts {
		if _, ok := s.(*StarStmt); ok {
			continue
		}
		m.setCtx("Star", b, 0, nil, 1, "")
		m.exec.ExecStmt(s, nil)
		if m.exec.Stopped() {
			return
		}
	}
	for i := 0; i < len(toks); i++ {
		if m.exec.Stopped() {
			return
		}
		tok := &toks[i]
		for _, s := range b.Stmts {
			ss, ok := s.(*StarStmt)
			if !ok {
				continue
			}
			if tok.Text != ss.Target && tok.Class != ss.Target {
				continue
			}
			if m.starCheck(toks, i, ss) {
				m.state.Set("$self", tok.Text)
				m.setCtx("Star", b, i, tok, 1, ss.Target)
				m.exec.ExecStmts(ss.Body, tok)
			}
		}
	}
}

func (m *Matcher) starCheck(toks []Token, pos int, ss *StarStmt) bool {
	crossLine := strings.Contains(ss.Dir, ">>") || strings.Contains(ss.Dir, "<<")
	lookRight := strings.Contains(ss.Dir, ">")
	lookLeft := strings.Contains(ss.Dir, "<")
	var visible []*Token
	if lookRight {
		for j := pos + 1; j < len(toks); j++ {
			if !crossLine && toks[j].Line != toks[pos].Line {
				break
			}
			visible = append(visible, &toks[j])
		}
	}
	if lookLeft {
		for j := pos - 1; j >= 0; j-- {
			if !crossLine && toks[j].Line != toks[pos].Line {
				break
			}
			visible = append(visible, &toks[j])
		}
	}
	matched := func(lf string) bool {
		for _, t := range visible {
			if builtinClassNames[lf] {
				if t.Class == lf {
					return true
				}
			} else if t.Text == lf {
				return true
			}
		}
		return false
	}
	if ss.Mode == "all" {
		for _, lf := range ss.LookFor {
			if !matched(lf) {
				return false
			}
		}
		return true
	}
	for _, lf := range ss.LookFor {
		if matched(lf) {
			return true
		}
	}
	return false
}

func (m *Matcher) runAny(b *Block, toks []Token) {
	for _, s := range b.Stmts {
		if _, ok := s.(*IfStmt); ok {
			continue
		}
		m.setCtx("Any", b, 0, nil, 1, "")
		m.exec.ExecStmt(s, nil)
		if m.exec.Stopped() {
			return
		}
	}
	pos := 0
	for pos < len(toks) {
		if m.exec.Stopped() {
			return
		}
		t := &toks[pos]
		m.state.Set("$self", t.Text)
		m.setCtx("Any", b, pos, t, 1, "")
		for _, s := range b.Stmts {
			ifs, ok := s.(*IfStmt)
			if !ok {
				continue
			}
			hit := false
			for _, br := range ifs.Branches {
				if m.tryCond(br.Cond, toks, pos) {
					target := extractTarget(br.Cond)
					m.setCtx("Any", b, pos, t, 1, target)
					m.exec.ExecStmts(br.Then, t)
					hit = true
					break
				}
			}
			if !hit && len(ifs.Else) > 0 {
				m.exec.ExecStmts(ifs.Else, t)
			}
		}
		pos++
	}
	for _, c := range b.Children {
		m.RunBlock(c, toks)
	}
}

// ---------- 7. Executor ----------

type Executor struct {
	state    *StateStore
	debug    bool
	stopFlag bool

	curEngine string
	curNum    int
	curBlock  string
	curPos    int
	curTok    *Token
	curCount  int

	curTarget  string
	curValue   string
	curLine    int
	stateCount map[string]int
}

func NewExecutor(s *StateStore, debug bool) *Executor {
	return &Executor{
		state:      s,
		debug:      debug,
		stateCount: make(map[string]int),
	}
}

func (ex *Executor) D(f string, a ...interface{}) {
	if ex.debug {
		fmt.Printf(C("[Db] ", Dim+SoftBlue)+f+"\n", a...)
	}
}

func (ex *Executor) Stopped() bool { return ex.stopFlag }
func (ex *Executor) Reset()        { ex.stopFlag = false }

func (ex *Executor) ExecStmts(stmts []Node, tok *Token) bool {
	for _, s := range stmts {
		if ex.ExecStmt(s, tok) {
			return true
		}
		if ex.stopFlag {
			return true
		}
	}
	return false
}

func (ex *Executor) ExecStmt(s Node, tok *Token) bool {
	switch n := s.(type) {
	case *StopStmt:
		ex.stopFlag = true
		return true
	case *StateStmt:
		ex.execState(n)
		return false
	case *AssignStmt:
		ex.execAssign(n)
		return false
	case *AppendStmt:
		ex.execAppend(n)
		return false
	case *IncrStmt:
		ex.state.Incr(n.Target)
		return false
	case *DecrStmt:
		ex.state.Decr(n.Target)
		return false
	case *AddIntStmt:
		ex.state.AddInt(n.Target, n.Delta)
		return false
	case *IfStmt:
		return false
	}
	return false
}

func (ex *Executor) execState(s *StateStmt) {
	obj := s.Object
	if obj == "" {
		if ex.curTok != nil {
			obj = ex.curTok.Text
		} else {
			obj = "self"
		}
	}
	prefix := fmt.Sprintf("%s#%d.%s.State.%s",
		ex.curEngine, ex.curNum, ex.curBlock, obj)

	idx := ex.stateCount[prefix]
	ex.stateCount[prefix] = idx + 1

	ex.state.Set(prefix+".number", idx+1)

	idxPrefix := fmt.Sprintf("%s[%d]", prefix, idx)

	fields := s.Fields
	if len(fields) == 0 {
		fields = []string{"target", "value", "Lines.start", "token.start", "token.end"}
	}
	for _, f := range fields {
		switch f {
		case "target":
			ex.state.Set(idxPrefix+".target", ex.curTarget)
		case "value":
			ex.state.Set(idxPrefix+".value", ex.curValue)
		case "Lines.start":
			ex.state.Set(idxPrefix+".Lines.start", ex.curLine)
		case "token.start":
			ex.state.Set(idxPrefix+".token.start", ex.curPos)
		case "token.end":
			ex.state.Set(idxPrefix+".token.end", ex.curPos+ex.curCount-1)
		case "number":
			ex.state.Set(idxPrefix+".number", 1)
		}
	}
	ex.D("State %s[%d] {target=%q value=%q line=%d pos=%d end=%d count=%d}",
		prefix, idx, ex.curTarget, ex.curValue, ex.curLine,
		ex.curPos, ex.curPos+ex.curCount-1, ex.curCount)
}

func (ex *Executor) execAssign(a *AssignStmt) {
	if a == nil {
		return
	}
	if a.Alias != "" {
		ex.state.AddAlias(a.Alias, a.Target)
	}
	if a.Op == "+" {
		if isInt(a.Value) || isFloat(a.Value) {
			delta := ex.resolveFloat(a.Value)
			cur := ex.state.GetFloat(a.Target)
			ex.state.Set(a.Target, cur+delta)
		} else {
			ex.state.Append(a.Target, a.Value)
		}
		return
	}
	if a.Op == "-" {
		delta := ex.resolveFloat(a.Value)
		cur := ex.state.GetFloat(a.Target)
		ex.state.Set(a.Target, cur-delta)
		return
	}
	var v interface{}
	switch {
	case a.Value == "true" || a.Value == "yes":
		v = true
	case a.Value == "false" || a.Value == "no":
		v = false
	case a.Value == "$self":
		v = ex.state.GetString("$self")
	case a.Value == "type{}" || a.Value == "type[]":
		v = ex.state.GetString("type{}")
		if v == "" {
			v = ex.state.GetString("type[]")
		}
	case strings.HasPrefix(a.Value, "def."):
		v = a.Value[4:]
	case isInt(a.Value):
		n, _ := strconv.Atoi(a.Value)
		v = n
	case isFloat(a.Value):
		f, _ := strconv.ParseFloat(a.Value, 64)
		v = f
	case strings.HasPrefix(a.Value, "$"):
		v = ex.state.GetString(a.Value)
	default:
		if uq, ok := unquote(a.Value); ok {
			v = uq
		} else if got, ok := ex.state.Get(a.Value); ok {
			v = got
		} else {
			v = a.Value
		}
	}
	if strings.HasPrefix(a.Target, "$") {
		capVal := ex.state.GetString(a.Target)
		if a.CapID != "" {
			ex.state.SetID(a.CapID, capVal)
		}
		key := capVal + a.Attr
		ex.state.Set(key, v)
		return
	}
	if strings.HasPrefix(a.Target, "[") && strings.HasSuffix(a.Target, "]") {
		inner := a.Target[1 : len(a.Target)-1]
		for _, part := range strings.Split(inner, ",") {
			p := strings.TrimSpace(part)
			if p != "" {
				ex.state.Set(p, v)
			}
		}
		return
	}
	ex.state.Set(a.Target, v)
}

func (ex *Executor) execAppend(a *AppendStmt) {
	if a == nil {
		return
	}
	var v string
	switch {
	case a.Value == "$self":
		v = ex.state.GetString("$self")
	case strings.HasPrefix(a.Value, "$"):
		v = ex.state.GetString(a.Value)
	default:
		if uq, ok := unquote(a.Value); ok {
			v = uq
		} else if got, ok := ex.state.Get(a.Value); ok {
			v = fmt.Sprintf("%v", got)
		} else {
			v = a.Value
		}
	}
	ex.state.Append(a.Target, v)
}

func (ex *Executor) resolveFloat(s string) float64 {
	if s == "" {
		return 0
	}
	if f, err := strconv.ParseFloat(s, 64); err == nil {
		return f
	}
	return ex.state.GetFloat(s)
}

// ---------- 8. Test runner ----------

type TestCase struct {
	Input    string
	Expected []Expectation
	LineNum  int
}

type Expectation struct {
	Key   string
	Value string
	Neg   bool
	Raw   string
	Line  int
}

func ParseTestFile(path string) ([]TestCase, error) {
	data, err := os.ReadFile(path)
	if err != nil {
		return nil, fmt.Errorf("cannot read %s: %w", path, err)
	}
	return ParseTestString(string(data))
}

func ParseTestString(content string) ([]TestCase, error) {
	lines := strings.Split(content, "\n")
	var cases []TestCase
	var cur *TestCase
	for i, raw := range lines {
		line := strings.TrimRight(raw, "\r")
		trimmed := strings.TrimSpace(line)
		if trimmed == "" {
			if cur != nil && cur.Input != "" {
				cases = append(cases, *cur)
				cur = nil
			}
			continue
		}
		if strings.HasPrefix(trimmed, "#") || strings.HasPrefix(trimmed, "//") {
			continue
		}
		if strings.HasPrefix(trimmed, "> ") || trimmed == ">" {
			if cur != nil && cur.Input != "" {
				cases = append(cases, *cur)
			}
			input := strings.TrimSpace(strings.TrimPrefix(trimmed, ">"))
			cur = &TestCase{Input: input, LineNum: i + 1}
			continue
		}
		if cur == nil {
			return nil, fmt.Errorf("line %d: expectation before input", i+1)
		}
		exp := parseExpectation(trimmed, i+1)
		if exp != nil {
			cur.Expected = append(cur.Expected, *exp)
		}
	}
	if cur != nil && cur.Input != "" {
		cases = append(cases, *cur)
	}
	return cases, nil
}

func parseExpectation(line string, lineno int) *Expectation {
	exp := &Expectation{Raw: line, Line: lineno}
	if strings.HasPrefix(line, "!") {
		exp.Neg = true
		line = strings.TrimSpace(strings.TrimPrefix(line, "!"))
	}
	if idx := strings.Index(line, "="); idx >= 0 {
		exp.Key = strings.TrimSpace(line[:idx])
		exp.Value = strings.TrimSpace(line[idx+1:])
	} else {
		exp.Key = strings.TrimSpace(line)
	}
	if exp.Key == "" {
		return nil
	}
	return exp
}

func checkExpectation(s *StateStore, exp *Expectation) (bool, string) {
	actual, exists := s.Get(exp.Key)
	if exp.Neg {
		if !exists {
			return true, ""
		}
		switch x := actual.(type) {
		case bool:
			if !x {
				return true, ""
			}
		case int:
			if x == 0 {
				return true, ""
			}
		case float64:
			if x == 0 {
				return true, ""
			}
		default:
			if fmt.Sprintf("%v", actual) == "" {
				return true, ""
			}
		}
		return false, fmt.Sprintf("expect %s false, got %v", exp.Key, actual)
	}
	if !exists {
		return false, fmt.Sprintf("state %s does not exist", exp.Key)
	}
	if exp.Value == "" {
		switch x := actual.(type) {
		case bool:
			if x {
				return true, ""
			}
			return false, fmt.Sprintf("expect %s true, got false", exp.Key)
		case int:
			if x != 0 {
				return true, ""
			}
			return false, fmt.Sprintf("expect %s true, got 0", exp.Key)
		case float64:
			if x != 0 {
				return true, ""
			}
			return false, fmt.Sprintf("expect %s true, got 0", exp.Key)
		case string:
			if x != "" {
				return true, ""
			}
			return false, fmt.Sprintf("expect %s true, got empty", exp.Key)
		}
		return false, fmt.Sprintf("cannot evaluate %s", exp.Key)
	}
	switch x := actual.(type) {
	case bool:
		want := exp.Value == "true" || exp.Value == "1" || exp.Value == "yes"
		if x == want {
			return true, ""
		}
		return false, fmt.Sprintf("expect %s = %v, got %v", exp.Key, want, x)
	case int:
		iv, _ := strconv.Atoi(exp.Value)
		if x == iv {
			return true, ""
		}
		return false, fmt.Sprintf("expect %s = %d, got %d", exp.Key, iv, x)
	case float64:
		fv, _ := strconv.ParseFloat(exp.Value, 64)
		if x == fv {
			return true, ""
		}
		return false, fmt.Sprintf("expect %s = %v, got %v", exp.Key, fv, x)
	case string:
		if x == exp.Value {
			return true, ""
		}
		return false, fmt.Sprintf("expect %s = %q, got %q", exp.Key, exp.Value, x)
	}
	got := fmt.Sprintf("%v", actual)
	if got == exp.Value {
		return true, ""
	}
	return false, fmt.Sprintf("expect %s = %q, got %q", exp.Key, exp.Value, got)
}

type TestResult struct {
	Case   TestCase
	Passed bool
	Fails  []string
}

func resetKeywords(cfg *Config) {
	// Clear and restore defaults, then merge user-defined, avoiding global pollution
	for k := range builtinKeyword {
		delete(builtinKeyword, k)
	}
	builtinKeyword["def"] = true
	builtinKeyword["if"] = true
	if td, ok := cfg.TableDefs["keyword"]; ok {
		for _, it := range td.Items {
			if it != "" {
				builtinKeyword[it] = true
			}
		}
	}
}

func RunTests(cfg *Config, cases []TestCase, debug bool) ([]TestResult, int, int) {
	results := make([]TestResult, 0, len(cases))
	passed, failed := 0, 0
	for _, tc := range cases {
		resetKeywords(cfg)
		state := NewStateStore()
		m := NewMatcher(state, debug)
		m.SetQuiet(true)
		for name, td := range cfg.TableDefs {
			m.RegisterTable(name, td)
		}
		for _, b := range cfg.Blocks {
			m.RegisterBlock(b)
		}
		toks := Lex(tc.Input, cfg.Ignore)
		for _, b := range cfg.Blocks {
			m.RunBlock(b, toks)
		}
		res := TestResult{Case: tc, Passed: true}
		for i := range tc.Expected {
			exp := &tc.Expected[i]
			ok, msg := checkExpectation(state, exp)
			if !ok {
				res.Passed = false
				res.Fails = append(res.Fails, fmt.Sprintf("line %d: %s", exp.Line, msg))
			}
		}
		if res.Passed {
			passed++
		} else {
			failed++
		}
		results = append(results, res)
	}
	return results, passed, failed
}

// ---------- 9. Demo ----------

const demoSL = `
def Ignore: {space, tab, enter}
def keyword: {int, float, string, def, class, if, return}
def type: {int, float, string}

Match Keyword :
    if Match @Ky --> def
        State kw-def
        Status kw = "def"
    elif Match @Ky --> class
        State kw-class
        Status kw = "class"
    elif Match @Ky --> return
        State kw-return
        Status kw = "return"

Match DefSeq :
    if Match [@Ky ; @Text ; ( ; ) ; :] --> [def ; * ; ( ; ) ; :]
        State defseq
        Status def.seq.matched = true

Match KeywordList :
    if Match @Ky --> {def, class}
        State kwlist
        Status kw.type = "decl"
    elif Match @Ky --> {if, else}
        State kwlist
        Status kw.type = "branch"

Deep Bracket :
    if Deep [ <-> ]
        State bracket
        Status @Boundary.[] = true
    if Deep + <-> +
        State plus
        Status @Boundary.++ = true

Capture KV :
    if Capture Re((\w+)=(\w+))
        State kv
        Status $0-id_1.k = $0
        Status $1-id_2.v = $1

Capture_Semantics Type :
    if Capture type{} $*
        State sem
        Status $1-id.t = type{}

Star Lookup :
    star def > class
        State lookup
        Status def.followedByClass = true

Any Mixed :
    if Match @Ky --> def
        State mixed
        Status mixed.def = true
    Deep InnerBracket :
        if Deep [ <-> ]
            State inner
            Status inner.bracket = true
`

func usage() {
	title := func(s string) string { return C(s, Bold+SoftCyan) }
	head := func(s string) string { return C(s, SoftYellow) }
	opt := func(s string) string { return C(s, SoftGreen) }
	desc := func(s string) string { return C(s, SoftBlue) }
	dim := func(s string) string { return C(s, Dim+Gray) }

	fmt.Fprintln(os.Stderr, title("Starlang 1.0.0-release-go"))
	fmt.Fprintln(os.Stderr, dim("Multi-Engine Analysis Language (MEAL)"))
	fmt.Fprintln(os.Stderr)

	fmt.Fprintln(os.Stderr, head("Usage:"))
	fmt.Fprintln(os.Stderr, "  sl [options] [rule-file]")
	fmt.Fprintln(os.Stderr)
	fmt.Fprintf(os.Stderr, "  %s    %s\n", opt("-r <file>"), desc("rule file"))
	fmt.Fprintf(os.Stderr, "  %s    %s\n", opt("-f <file>"), desc("script file"))
	fmt.Fprintf(os.Stderr, "  %s   %s\n", opt("-i <input>"), desc("single input"))
	fmt.Fprintf(os.Stderr, "  %s    %s\n", opt("-t <file>"), desc("test file"))
	fmt.Fprintf(os.Stderr, "  %s       %s\n", opt("-json"), desc("JSON output"))
	fmt.Fprintf(os.Stderr, "  %s       %s\n", opt("-demo"), desc("demo"))
	fmt.Fprintf(os.Stderr, "  %s      %s\n", opt("-debug"), desc("debug"))
	fmt.Fprintf(os.Stderr, "  %s      %s\n", opt("-trace"), desc("trace history"))
	fmt.Fprintf(os.Stderr, "  %s      %s\n", opt("-quiet"), desc("quiet"))
	fmt.Fprintf(os.Stderr, "  %s          %s\n", opt("-v"), desc("version"))
	fmt.Fprintf(os.Stderr, "  %s       %s\n", opt("-help"), desc("help"))
	fmt.Fprintln(os.Stderr)

	fmt.Fprintln(os.Stderr, head("Engines:"))
	fmt.Fprintln(os.Stderr, "  Match / Deep / Capture / Capture_Semantics / Star / Any")
	fmt.Fprintln(os.Stderr)

	fmt.Fprintln(os.Stderr, head("State statement:"))
	fmt.Fprintf(os.Stderr, "  %s              %s\n", opt("State"), desc("local (object = current token)"))
	fmt.Fprintf(os.Stderr, "  %s        %s\n", opt("State <name>"), desc("specify object name"))
	fmt.Fprintf(os.Stderr, "  %s  %s\n", opt("State <name> f1 f2"), desc("output only specified fields"))
	fmt.Fprintln(os.Stderr)

	fmt.Fprintln(os.Stderr, head("State fields:"))
	fmt.Fprintf(os.Stderr, "  %s          %s\n", opt("target"), desc("rule target"))
	fmt.Fprintf(os.Stderr, "  %s           %s\n", opt("value"), desc("matched text"))
	fmt.Fprintf(os.Stderr, "  %s     %s\n", opt("Lines.start"), desc("start line (0-based)"))
	fmt.Fprintf(os.Stderr, "  %s     %s\n", opt("token.start"), desc("start token index"))
	fmt.Fprintf(os.Stderr, "  %s       %s\n", opt("token.end"), desc("end token index"))
	fmt.Fprintf(os.Stderr, "  %s          %s\n", opt("number"), desc("total matches"))
	fmt.Fprintln(os.Stderr)

	fmt.Fprintln(os.Stderr, head("State output:"))
	fmt.Fprintln(os.Stderr, "  <Engine>#<num>.<block>.State.<obj>.number")
	fmt.Fprintln(os.Stderr, "  <Engine>#<num>.<block>.State.<obj>[N].target")
	fmt.Fprintln(os.Stderr, "  <Engine>#<num>.<block>.State.<obj>[N].value")
	fmt.Fprintln(os.Stderr, "  <Engine>#<num>.<block>.State.<obj>[N].Lines.start")
	fmt.Fprintln(os.Stderr, "  <Engine>#<num>.<block>.State.<obj>[N].token.start")
	fmt.Fprintln(os.Stderr, "  <Engine>#<num>.<block>.State.<obj>[N].token.end")
	fmt.Fprintln(os.Stderr)

	fmt.Fprintln(os.Stderr, head("Deep symbols:"))
	fmt.Fprintf(os.Stderr, "  %s      %s\n", opt("<->"), desc("greedy, single-line"))
	fmt.Fprintf(os.Stderr, "  %s     %s\n", opt("<-->"), desc("non-greedy, single-line"))
	fmt.Fprintf(os.Stderr, "  %s    %s\n", opt("<<->>"), desc("greedy, cross-line"))
	fmt.Fprintf(os.Stderr, "  %s   %s\n", opt("<<-->>"), desc("non-greedy, cross-line"))
	fmt.Fprintln(os.Stderr)

	fmt.Fprintln(os.Stderr, head("Table / Sequence:"))
	fmt.Fprintf(os.Stderr, "  %s   %s\n", opt("def xxx: {a, b, c}"), desc("table"))
	fmt.Fprintf(os.Stderr, "  %s                %s\n", opt("xxx{}"), desc("empty table reference"))
	fmt.Fprintf(os.Stderr, "  %s  %s\n", opt("Match [@Ky ; @Text]"), desc("sequence (; between, , inside)"))
	fmt.Fprintln(os.Stderr)

	fmt.Fprintln(os.Stderr, head("Recursion:"))
	fmt.Fprintln(os.Stderr, "  Match <block-name>")
	fmt.Fprintln(os.Stderr)

	fmt.Fprintln(os.Stderr, head("Regex:"))
	fmt.Fprintln(os.Stderr, "  Re(...)")
	fmt.Fprintln(os.Stderr)

	fmt.Fprintln(os.Stderr, head("Comments:"))
	fmt.Fprintln(os.Stderr, "  #  //  /* */")
}

func version() {
	fmt.Printf("%s\n", C("Starlang 1.0.0-release-go", Bold+SoftCyan))
	fmt.Printf("%s\n\n", C("Build by golang", Dim+Gray))

	fmt.Printf("%s\n", C("Multi-Engine", SoftYellow))
	fmt.Printf("  %s             %s\n", C("Match:", SoftGreen), C("Token-by-token mode", Gray))
	fmt.Printf("  %s              %s\n", C("Deep:", SoftGreen), C("Paired-structure mode", Gray))
	fmt.Printf("  %s           %s\n", C("Capture:", SoftGreen), C("Regular extraction mode", Gray))
	fmt.Printf("  %s %s\n", C("Capture_Semantics:", SoftGreen), C("Semantic mode", Gray))
	fmt.Printf("  %s              %s\n", C("Star:", SoftGreen), C("Direction-finding mode", Gray))
	fmt.Printf("  %s               %s\n\n", C("Any:", SoftGreen), C("Mixed mode", Gray))

	fmt.Printf("%s\n", C("What can we do?", SoftYellow))
	fmt.Printf("  %s\n", C("Lexical analysis", SoftBlue))
	fmt.Printf("  %s\n", C("Syntactic analysis", SoftBlue))
	fmt.Printf("  %s\n", C("Semantic analysis", SoftBlue))
	fmt.Printf("  %s\n", C("Configuration analysis", SoftBlue))
	fmt.Printf("  %s\n", C("Structured analysis", SoftBlue))
	fmt.Printf("  %s\n\n", C("More analysis", SoftBlue))

	fmt.Printf("%s\n", C("What is Starlang?", SoftYellow))
	fmt.Printf("  %s\n", C("A DSL", SoftMagenta))
	fmt.Printf("  %s\n", C("An analysis language", SoftMagenta))
	fmt.Printf("  %s\n\n", C("A non-general-purpose language", SoftMagenta))

	fmt.Printf("%s\n", C("Starlang has no upper limit.", SoftRed))
}

// ---------- 10. Main ----------

func main() {
	rflag := flag.String("r", "", "rule file")
	fflag := flag.String("f", "", "script file")
	iflag := flag.String("i", "", "single input")
	tflag := flag.String("t", "", "test file")
	jsonOut := flag.Bool("json", false, "JSON output")
	demo := flag.Bool("demo", false, "demo")
	debug := flag.Bool("debug", false, "debug")
	trace := flag.Bool("trace", false, "trace history")
	quiet := flag.Bool("quiet", false, "quiet")
	vflag := flag.Bool("v", false, "version")
	hflag := flag.Bool("help", false, "help")
	flag.Parse()

	if *hflag {
		usage()
		return
	}
	if *vflag {
		version()
		return
	}

	var cfg *Config
	var err error
	if *rflag != "" {
		cfg, err = ParseFile(*rflag)
	} else if flag.NArg() > 0 {
		cfg, err = ParseFile(flag.Arg(0))
	} else {
		cfg, err = ParseString(demoSL)
		if err == nil && !*jsonOut && !*quiet {
			os.WriteFile("demo.sl", []byte(demoSL), 0644)
		}
	}
	if err != nil {
		fmt.Fprintln(os.Stderr, C("parse failed:", SoftRed), err)
		os.Exit(1)
	}

	if *tflag != "" {
		cases, err := ParseTestFile(*tflag)
		if err != nil {
			fmt.Fprintln(os.Stderr, C("parse test file failed:", SoftRed), err)
			os.Exit(2)
		}
		if !*jsonOut && !*quiet {
			fmt.Println(C("=== test mode ===", Bold+SoftCyan))
			fmt.Printf("%s %s\n", C("file:", SoftBlue), *tflag)
			fmt.Printf("%s %d\n\n", C("cases:", SoftBlue), len(cases))
		}
		results, passed, failed := RunTests(cfg, cases, *debug)
		for i, r := range results {
			st := C("PASS", SoftGreen)
			if !r.Passed {
				st = C("FAIL", SoftRed)
			}
			fmt.Printf("  [%2d] %-4s  %s\n", i+1, st, r.Case.Input)
			if !r.Passed {
				for _, f := range r.Fails {
					fmt.Printf("         %s %s\n", C("|--", SoftRed), f)
				}
			}
		}
		if !*quiet {
			fmt.Printf("\n%s %d  %s %d  %s %d\n",
				C("total:", SoftBlue), len(cases),
				C("passed:", SoftGreen), passed,
				C("failed:", SoftRed), failed)
		}
		if failed > 0 {
			os.Exit(1)
		}
		return
	}

	if !*jsonOut && !*quiet {
		fmt.Println(C("=== rule load ===", Bold+SoftCyan))
		fmt.Printf("  %s %d\n", C("Ignore:", SoftBlue), len(cfg.Ignore))
		fmt.Printf("  %s %d\n", C("top tables:", SoftBlue), len(cfg.TableDefs))
		fmt.Printf("  %s %d\n", C("top blocks:", SoftBlue), len(cfg.Blocks))

		var dump func(b *Block, indent string)
		dump = func(b *Block, indent string) {
			head := C(fmt.Sprintf("[%s#%d]", b.Name, b.Num), SoftCyan)
			fmt.Printf("%s%s kind=%s stmts=%d children=%d\n",
				indent,
				head,
				C(b.Kind, SoftBlue),
				len(b.Stmts),
				len(b.Children))
			for _, c := range b.Children {
				dump(c, indent+"  ")
			}
		}
		for _, b := range cfg.Blocks {
			dump(b, "  ")
		}
		fmt.Println()
	}

	run := func(input string) {
		state := NewStateStore()
		state.trace = *trace
		m := NewMatcher(state, *debug)
		m.SetJSON(*jsonOut)
		m.SetQuiet(*quiet || *jsonOut)
		for name, td := range cfg.TableDefs {
			m.RegisterTable(name, td)
		}
		for _, b := range cfg.Blocks {
			m.RegisterBlock(b)
		}
		toks := Lex(input, cfg.Ignore)
		if *debug && !*quiet && !*jsonOut {
			fmt.Printf("%s %v\n", C("tokens:", SoftBlue), TokenizeToString(toks))
		}
		for _, b := range cfg.Blocks {
			m.RunBlock(b, toks)
		}
		if *jsonOut {
			fmt.Println(state.ToJSON())
		} else if !*quiet {
			state.Dump()
			if *trace {
				state.DumpHistory()
			}
		}
	}

	if *iflag != "" {
		run(*iflag)
		return
	}

	if *fflag != "" {
		data, err := os.ReadFile(*fflag)
		if err != nil {
			fmt.Fprintln(os.Stderr, C("cannot read script:", SoftRed), err)
			os.Exit(1)
		}
		for _, line := range strings.Split(string(data), "\n") {
			line = strings.TrimRight(line, "\r")
			trimmed := strings.TrimSpace(line)
			if trimmed == "" || strings.HasPrefix(trimmed, "#") || strings.HasPrefix(trimmed, "//") {
				continue
			}
			if !*quiet {
				fmt.Println(C("========================================", Dim+Gray))
				fmt.Printf("%s %s\n", C("input:", SoftBlue), trimmed)
			}
			run(trimmed)
		}
		return
	}

	if *demo {
		inputs := []string{
			"help help help",
			"def hello ( ) :",
			"[1+1+1]",
			"key=value",
			"x = 42",
			"def class return",
			"return",
		}
		for _, in := range inputs {
			if !*quiet {
				fmt.Println(C("========================================", Dim+Gray))
				fmt.Printf("%s %s\n", C("input:", SoftBlue), in)
			}
			run(in)
		}
		return
	}

	if !*quiet {
		fmt.Println(C("interactive mode, :q to quit, :help for help", SoftYellow))
	}
	reader := bufio.NewReader(os.Stdin)
	state := NewStateStore()
	state.trace = *trace
	m := NewMatcher(state, *debug)
	m.SetQuiet(true)
	for name, td := range cfg.TableDefs {
		m.RegisterTable(name, td)
	}
	for _, b := range cfg.Blocks {
		m.RegisterBlock(b)
	}

	for {
		fmt.Print(C("> ", SoftGreen))
		line, err := reader.ReadString('\n')
		if err != nil {
			break
		}
		line = strings.TrimRight(line, "\r\n")
		if line == "" {
			continue
		}
		if strings.HasPrefix(line, ":") {
			switch {
			case line == ":q" || line == ":quit" || line == "quit":
				fmt.Println(C("bye.", SoftYellow))
				return
			case line == ":state":
				state.Dump()
			case line == ":json":
				fmt.Println(state.ToJSON())
			case line == ":hist":
				state.DumpHistory()
			case line == ":help":
				fmt.Println(C("commands: :q :state :json :hist :tokens <input>", SoftBlue))
			case strings.HasPrefix(line, ":tokens "):
				input := strings.TrimSpace(strings.TrimPrefix(line, ":tokens"))
				toks := Lex(input, cfg.Ignore)
				fmt.Println(TokenizeToString(toks))
			default:
				fmt.Println(C("unknown command", SoftRed))
			}
			continue
		}
		m.exec.Reset()
		toks := Lex(line, cfg.Ignore)
		m.D("Tokens: %s", TokenizeToString(toks))
		for _, b := range cfg.Blocks {
			m.RunBlock(b, toks)
		}
		state.Dump()
	}
}
