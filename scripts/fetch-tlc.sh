#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TOOLS_DIR="$ROOT_DIR/tools"
DESTINATION="$TOOLS_DIR/tla2tools.jar"
VERSION="1.8.0"
URL="https://github.com/tlaplus/tlaplus/releases/download/v${VERSION}/tla2tools.jar"
EXPECTED_SHA256="eabd140a70f49eb9305a3bd3f3df944eddf87e5a90d329789085f8953a80533a"

if [[ -f "$DESTINATION" ]]; then
    actual="$(shasum -a 256 "$DESTINATION" | awk '{print $1}')"
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
actual="$(shasum -a 256 "$temporary" | awk '{print $1}')"
if [[ "$actual" != "$EXPECTED_SHA256" ]]; then
    printf 'Checksum mismatch: expected %s, got %s\n' \
        "$EXPECTED_SHA256" "$actual" >&2
    exit 1
fi

mv "$temporary" "$DESTINATION"
printf 'Downloaded TLC %s to %s\n' "$VERSION" "$DESTINATION"

