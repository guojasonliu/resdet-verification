#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SPEC_DIR="$ROOT_DIR/spec"
JAR="${TLA2TOOLS_JAR:-$ROOT_DIR/tools/tla2tools.jar}"
JAVA_BIN="${JAVA_BIN:-java}"
MODE="${1:-simulate}"
CONFIG="ResdetResearch.cfg"

if [[ ! -f "$JAR" ]]; then
    "$ROOT_DIR/scripts/fetch-tlc.sh"
fi

case "$MODE" in
    simulate)
        traces="${TLC_SIM_TRACES:-50}"
        depth="${TLC_SIM_DEPTH:-250}"
        seed="${TLC_SIM_SEED:-20260829}"
        heap="${TLC_HEAP:-2g}"
        run_dir="$(mktemp -d "${TMPDIR:-/tmp}/resdet-research-sim.XXXXXX")"
        trap 'rm -rf "$run_dir"' EXIT

        printf 'Research-scale simulation: traces=%s depth=%s seed=%s\n' \
            "$traces" "$depth" "$seed"
        cd "$SPEC_DIR"
        "$JAVA_BIN" -XX:+UseParallelGC "-Xmx$heap" -jar "$JAR" \
            -cleanup \
            -noGenerateSpecTE \
            -terse \
            -workers 1 \
            -metadir "$run_dir" \
            -config "$CONFIG" \
            -depth "$depth" \
            -seed "$seed" \
            -simulate "num=$traces" \
            Resdet
        ;;
    exhaustive)
        workers="${TLC_WORKERS:-auto}"
        heap="${TLC_HEAP:-8g}"
        timestamp="$(date +%Y%m%d-%H%M%S)"
        run_dir="${TLC_METADIR:-$ROOT_DIR/.tlc/research-$timestamp}"

        printf 'Research-scale exhaustive run; metadata: %s\n' "$run_dir"
        cd "$SPEC_DIR"
        "$JAVA_BIN" -XX:+UseParallelGC "-Xmx$heap" -jar "$JAR" \
            -cleanup \
            -noGenerateSpecTE \
            -terse \
            -workers "$workers" \
            -checkpoint 10 \
            -metadir "$run_dir" \
            -config "$CONFIG" \
            Resdet
        ;;
    *)
        printf 'usage: %s [simulate|exhaustive]\n' "$0" >&2
        exit 2
        ;;
esac
