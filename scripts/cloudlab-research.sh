#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
MOUNT_POINT="${TLC_MOUNT_POINT:-/mnt/tlc}"
DATA_DIR="${TLC_DATA_DIR:-$MOUNT_POINT/resdet}"
EXTRA_DISK="${TLC_DISK:-/dev/sda}"
SESSION_NAME="${TLC_SCREEN_NAME:-resdet}"
HELPER="/usr/local/etc/emulab/mkextrafs.pl"

usage() {
    cat <<'EOF'
usage: ./scripts/cloudlab-research.sh

Prepare a CloudLab node's extra local disk and launch the research-scale TLC
check in a detached GNU Screen session.

Optional environment variables:
  TLC_DISK=/dev/sda          disk whose unused space should be prepared
  TLC_PARTITION=/dev/sda4    partition created from that unused space
  TLC_MOUNT_POINT=/mnt/tlc   mount point for TLC metadata
  TLC_DATA_DIR=/mnt/tlc/resdet
  TLC_HEAP=300g              Java heap (auto-sized when omitted)
  TLC_WORKERS=48             TLC workers (auto-sized when omitted)
  TLC_SCREEN_NAME=resdet     Screen session name
  CLOUDLAB_ASSUME_YES=1      skip the disk-formatting confirmation

The script never reformats a partition that already has a recognized
filesystem. It asks for the literal word PREPARE before creating/formatting
an unused partition unless CLOUDLAB_ASSUME_YES=1 is set.
EOF
}

if [[ "${1:-}" == "-h" || "${1:-}" == "--help" ]]; then
    usage
    exit 0
fi

if [[ $# -ne 0 ]]; then
    usage >&2
    exit 2
fi

partition_for_disk() {
    case "$1" in
        *[0-9]) printf '%sp4\n' "$1" ;;
        *) printf '%s4\n' "$1" ;;
    esac
}

install_dependencies() {
    local packages=()

    command -v java >/dev/null 2>&1 || packages+=(openjdk-17-jre-headless)
    command -v curl >/dev/null 2>&1 || packages+=(curl)
    command -v screen >/dev/null 2>&1 || packages+=(screen)

    if (( ${#packages[@]} == 0 )); then
        return
    fi

    if ! command -v apt-get >/dev/null 2>&1; then
        printf 'Missing commands and apt-get is unavailable: %s\n' "${packages[*]}" >&2
        exit 1
    fi

    printf 'Installing missing packages: %s\n' "${packages[*]}"
    sudo apt-get update
    sudo apt-get install -y "${packages[@]}"
}

prepare_storage() {
    local partition filesystem answer helper_status
    partition="${TLC_PARTITION:-$(partition_for_disk "$EXTRA_DISK")}"

    sudo mkdir -p "$MOUNT_POINT"

    if mountpoint -q "$MOUNT_POINT"; then
        printf 'Using existing mount %s on %s\n' \
            "$(findmnt -n -o SOURCE -T "$MOUNT_POINT")" "$MOUNT_POINT"
    else
        filesystem=""
        if [[ -b "$partition" ]]; then
            filesystem="$(lsblk -dn -o FSTYPE "$partition" | xargs)"
        fi

        if [[ -n "$filesystem" ]]; then
            printf 'Mounting existing %s filesystem from %s\n' "$filesystem" "$partition"
            sudo mount "$partition" "$MOUNT_POINT"
        else
            if [[ ! -b "$EXTRA_DISK" ]]; then
                printf 'Disk %s does not exist. Set TLC_DISK to the correct device.\n' \
                    "$EXTRA_DISK" >&2
                exit 1
            fi
            if [[ ! -x "$HELPER" ]]; then
                printf 'CloudLab storage helper not found at %s\n' "$HELPER" >&2
                exit 1
            fi

            printf '\nAbout to allocate unused space on %s as %s and format it for TLC.\n' \
                "$EXTRA_DISK" "$partition"
            printf 'Existing partitions with filesystems will not be reformatted.\n'
            if [[ "${CLOUDLAB_ASSUME_YES:-0}" != "1" ]]; then
                read -r -p 'Type PREPARE to continue: ' answer
                if [[ "$answer" != "PREPARE" ]]; then
                    printf 'Cancelled.\n'
                    exit 1
                fi
            fi

            if [[ ! -b "$partition" ]]; then
                set +e
                sudo "$HELPER" -r "$EXTRA_DISK" "$MOUNT_POINT"
                helper_status=$?
                set -e

                # Some CloudLab images create the partition successfully but
                # return nonzero because its new GPT type requires a -f pass.
                if [[ ! -b "$partition" ]]; then
                    printf 'Storage helper failed with status %s and did not create %s.\n' \
                        "$helper_status" "$partition" >&2
                    exit 1
                fi
            fi

            if ! mountpoint -q "$MOUNT_POINT"; then
                filesystem="$(lsblk -dn -o FSTYPE "$partition" | xargs)"
                if [[ -z "$filesystem" ]]; then
                    sudo "$HELPER" -f "$MOUNT_POINT"
                else
                    sudo mount "$partition" "$MOUNT_POINT"
                fi
            fi
        fi
    fi

    if ! mountpoint -q "$MOUNT_POINT"; then
        printf '%s is still not a separate mounted filesystem; refusing to run.\n' \
            "$MOUNT_POINT" >&2
        exit 1
    fi

    sudo mkdir -p "$DATA_DIR"
    sudo chown "$(id -u):$(id -g)" "$DATA_DIR"
    sudo chmod 0755 "$DATA_DIR"

    local write_test="$DATA_DIR/.write-test.$$"
    touch "$write_test"
    rm -f "$write_test"

    printf 'TLC storage is writable:\n'
    df -hT "$DATA_DIR"
}

choose_resources() {
    local memory_kib memory_gib heap_gib cpu_count worker_count
    memory_kib="$(awk '/MemTotal:/ {print $2}' /proc/meminfo)"
    memory_gib=$((memory_kib / 1024 / 1024))
    heap_gib=$((memory_gib * 60 / 100))
    (( heap_gib > 300 )) && heap_gib=300
    (( heap_gib < 2 )) && heap_gib=2

    cpu_count="$(nproc)"
    worker_count=$((cpu_count * 3 / 4))
    (( worker_count > 48 )) && worker_count=48
    (( worker_count < 1 )) && worker_count=1

    TLC_HEAP="${TLC_HEAP:-${heap_gib}g}"
    TLC_WORKERS="${TLC_WORKERS:-$worker_count}"
    export TLC_HEAP TLC_WORKERS
}

launch_run() {
    local timestamp run_dir log_file
    timestamp="$(date +%Y%m%d-%H%M%S)"
    run_dir="$DATA_DIR/research-$timestamp"
    log_file="$DATA_DIR/research-$timestamp.log"

    if screen -ls 2>/dev/null | grep -q "[.]${SESSION_NAME}[[:space:]]"; then
        printf 'A Screen session named %s already exists; not starting a duplicate.\n' \
            "$SESSION_NAME" >&2
        printf 'Attach with: screen -r %s\n' "$SESSION_NAME" >&2
        exit 1
    fi

    "$ROOT_DIR/scripts/fetch-tlc.sh"

    screen -dmS "$SESSION_NAME" bash -c '
        set -o pipefail
        root_dir="$1"
        log_file="$2"
        run_dir="$3"
        heap="$4"
        workers="$5"
        cd "$root_dir"
        printf "Starting TLC: heap=%s workers=%s metadata=%s\n" \
            "$heap" "$workers" "$run_dir" | tee "$log_file"
        TLC_METADIR="$run_dir" TLC_HEAP="$heap" TLC_WORKERS="$workers" \
            ./scripts/check-research.sh exhaustive 2>&1 | tee -a "$log_file"
        status=${PIPESTATUS[0]}
        printf "\nTLC exited with status %s. Log: %s\n" "$status" "$log_file" \
            | tee -a "$log_file"
        printf "Press Enter to close this Screen session.\n"
        read -r _
        exit "$status"
    ' bash "$ROOT_DIR" "$log_file" "$run_dir" "$TLC_HEAP" "$TLC_WORKERS"

    printf '\nResearch run launched in detached Screen session %s.\n' "$SESSION_NAME"
    printf 'Attach:  screen -r %s\n' "$SESSION_NAME"
    printf 'Detach:  Ctrl-A, then D\n'
    printf 'Log:     %s\n' "$log_file"
    printf "Monitor: watch -n 60 'df -h %s; du -sh %s'\n" \
        "$MOUNT_POINT" "$run_dir"
}

if [[ "$(uname -s)" != "Linux" ]]; then
    printf 'This bootstrap script is intended for a Linux CloudLab node.\n' >&2
    exit 1
fi

install_dependencies
prepare_storage
choose_resources
launch_run
