# Starlang

**Starlang 1.0.0-release-go** — Multi-Engine Analysis Language (MEAL)

![version](https://img.shields.io/badge/version-1.0.0--release--go-blue)
![license](https://img.shields.io/badge/license-MIT-green)
![go](https://img.shields.io/badge/go-1.26+-00ADD8)
![engine](https://img.shields.io/badge/engines-6-purple)
![status](https://img.shields.io/badge/status-stable-brightgreen)

## What is Starlang?

Starlang is a multi-engine analysis language.
6 engines cooperate to analyze structured text (code, config, logs).

## Engines

- **Match** — Token-by-token mode
- **Deep** — Paired-structure mode
- **Capture** — Regular extraction mode
- **Capture_Semantics** — Semantic mode
- **Star** — Direction-finding mode
- **Any** — Mixed mode

## What can we do?

- Lexical analysis
- Syntactic analysis
- Semantic analysis
- Configuration analysis
- Structured analysis
- More analysis

## Usage

```bash
go build -o starlang starlang.go
./starlang -demo
./starlang -help
./starlang -v
```

##License
MIT License — see [LICENSE](LICENSE) for details.

Starlang has no upper limit.