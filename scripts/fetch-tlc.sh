#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TOOLS_DIR="$ROOT_DIR/tools"
DESTINATION="$TOOLS_DIR/tla2tools.jar"
VERSION="1.7.4"
URL="https://github.com/tlaplus/tlaplus/releases/download/v${VERSION}/tla2tools.jar"
EXPECTED_SHA256="936a262061c914694dfd669a543be24573c45d5aa0ff20a8b96b23d01e050e88"

sha256_file() {
    if command -v sha256sum >/dev/null 2>&1; then
        sha256sum "$1" | awk '{print $1}'
    else
        shasum -a 256 "$1" | awk '{print $1}'
    fi
}

if [[ -f "$DESTINATION" ]]; then
    actual="$(sha256_file "$DESTINATION")"
    if [[ "$actual" == "$EXPECTED_SHA256" ]]; then
        printf 'TLC %s is already available at %s\n' "$VERSION" "$DESTINATION"
        exit 0
    fi
    printf 'Checksum mismatch for existing %s\n' "$DESTINATION" >&2
    exit 1
fi

mkdir -p "$TOOLS_DIR"
temporary="$(mktemp "${TMPDIR:-/tmp}/tla2tools.XXXXXX")"
trap 'rm -f "$temporary"' EXIT

curl -L --fail --silent --show-error "$URL" -o "$temporary"
actual="$(sha256_file "$temporary")"
if [[ "$actual" != "$EXPECTED_SHA256" ]]; then
    printf 'Checksum mismatch: expected %s, got %s\n' \
        "$EXPECTED_SHA256" "$actual" >&2
    exit 1
fi

mv "$temporary" "$DESTINATION"
printf 'Downloaded TLC %s to %s\n' "$VERSION" "$DESTINATION"
