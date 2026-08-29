#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SPEC_DIR="$ROOT_DIR/spec"
JAR="${TLA2TOOLS_JAR:-$ROOT_DIR/tools/tla2tools.jar}"
JAVA_BIN="${JAVA_BIN:-java}"
MODE="${1:-all}"

if [[ ! -f "$JAR" ]]; then
    "$ROOT_DIR/scripts/fetch-tlc.sh"
fi

case "$MODE" in
    all|passing|mutants) ;;
    *)
        printf 'usage: %s [all|passing|mutants]\n' "$0" >&2
        exit 2
        ;;
esac

run_root="$(mktemp -d "${TMPDIR:-/tmp}/resdet-tlc.XXXXXX")"
trap 'rm -rf "$run_root"' EXIT

run_tlc() {
    local config="$1"
    local name="${config##*/}"
    name="${name%.cfg}"
    "$JAVA_BIN" -XX:+UseParallelGC -jar "$JAR" \
        -cleanup \
        -noGenerateSpecTE \
        -terse \
        -workers 1 \
        -metadir "$run_root/$name" \
        -config "$config" \
        Resdet
}

run_passing() {
    local configs=(
        ResdetCore.cfg
        ResdetStrict.cfg
        ResdetBatching.cfg
        ResdetFailures.cfg
        ResdetFallback.cfg
        ResdetLiveness.cfg
    )
    for config in "${configs[@]}"; do
        local log="$run_root/${config%.cfg}.log"
        printf '\n==> PASS expected: %s\n' "$config"
        if ! (cd "$SPEC_DIR" && run_tlc "$config") >"$log" 2>&1; then
            cat "$log" >&2
            return 1
        fi
        grep -m 1 'Model checking completed' "$log"
        grep -m 1 -E \
            '[0-9]+ states generated, [0-9]+ distinct states found' \
            "$log"
    done
}

run_expected_failure() {
    local config="$1"
    local invariant="$2"
    local log="$run_root/${config##*/}.log"

    printf '\n==> COUNTEREXAMPLE expected: %s (%s)\n' \
        "$config" "$invariant"
    if (cd "$SPEC_DIR" && run_tlc "$config") >"$log" 2>&1; then
        printf 'TLC unexpectedly accepted mutant %s\n' "$config" >&2
        cat "$log" >&2
        return 1
    fi
    if ! grep -q "$invariant" "$log"; then
        printf 'TLC failed, but not for expected invariant %s\n' \
            "$invariant" >&2
        cat "$log" >&2
        return 1
    fi
    grep -m 1 -E \
        "Invariant .*${invariant}|${invariant} is violated" \
        "$log" || true
}

run_mutants() {
    run_expected_failure mutants/NoDedup.cfg AtMostOnceDelivery
    run_expected_failure mutants/NonContiguous.cfg ProcessedPrefixLearned
    run_expected_failure mutants/AllDispatch.cfg AtMostOnePhysicalDispatch
    run_expected_failure mutants/NoQuorum.cfg SelectionJustified
    run_expected_failure mutants/EarlyDelivery.cfg AppliedPrefixCorrect
    run_expected_failure mutants/NoLeaderDirect.cfg ResponseAgreement
}

if [[ "$MODE" == "all" || "$MODE" == "passing" ]]; then
    run_passing
fi
if [[ "$MODE" == "all" || "$MODE" == "mutants" ]]; then
    run_mutants
fi

printf '\nAll requested TLC checks behaved as expected.\n'
