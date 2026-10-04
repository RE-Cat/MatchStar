# MatchStar

**MatchStar 1.0.0-release-go** — Multi-Engine Analysis Language (MEAL)

![version](https://img.shields.io/badge/version-1.0.0--release--go-blue)
![license](https://img.shields.io/badge/license-MIT-green)
![go](https://img.shields.io/badge/go-1.24%20%7C%201.25%20%7C%201.26-00ADD8)
![engines](https://img.shields.io/badge/engines-6-purple)
![status](https://img.shields.io/badge/status-stable-brightgreen)

MatchStar is a multi-engine analysis language for structured text.
Six independent engines cooperate to turn source code, config,
logs and protocols into a queryable flat state.

[📖 Read the Specification](https://<user>.github.io/matchstar/)

---

## Engines

| # | Engine | Mode |
|---|--------|------|
| 1 | `Match` | Token-by-token |
| 2 | `Deep` | Paired-structure |
| 3 | `Capture` | Regular extraction |
| 4 | `Capture_Semantics` | Semantic |
| 5 | `Star` | Direction-finding |
| 6 | `Any` | Mixed |

## What can we do?

- Lexical analysis
- Syntactic analysis
- Semantic analysis
- Configuration analysis
- Structured analysis
- More analysis

## Quick start

    go build -o matchstar matchstar.go

    ./matchstar -demo
    ./matchstar -help
    ./matchstar -v
    ./matchstar -r rules.ms -i "input"

## Install

### From source

    go install github.com/<user>/matchstar@latest

### From release

Download the binary for your platform from the
[Releases](https://github.com/<user>/matchstar/releases) page.

## License

MIT License — see [LICENSE](LICENSE) for details.

---

**MatchStar has no upper limit.**