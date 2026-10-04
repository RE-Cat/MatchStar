#!/bin/bash
set -e

cd "$(dirname "$0")"
rm -rf dist
mkdir -p dist

build() {
    local os=$1 arch=$2 ext=$3
    local out="dist/MatchStar-${os}-${arch}${ext}"
    echo "-> $out"
    GOOS=$os GOARCH=$arch CGO_ENABLED=0 \
        go build -trimpath -ldflags "-s -w" -o "$out" MatchStar.go
}

build linux   amd64 ""
build linux   arm64 ""
build linux   arm   ""
build darwin  amd64 ""
build darwin  arm64 ""
build windows amd64 ".exe"
build windows arm64 ".exe"

cd dist
sha256sum * > checksums.txt
cd ..

echo
echo "=== done ==="
ls -la dist/
