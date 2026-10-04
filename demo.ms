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