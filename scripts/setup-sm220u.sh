#!/usr/bin/env bash
# Standalone: this file may be saved anywhere, including ~/setup.sh.
set -euo pipefail

MOUNT=/mnt/tlc
DATA=/mnt/tlc/resdet
VG=resdet_tlc
LV=states
REPO="${RESDET_REPO_DIR:-$HOME/resdet-verification}"
HEAP="${TLC_HEAP:-140g}"
WORKERS="${TLC_WORKERS:-32}"
JAR_SHA=936a262061c914694dfd669a543be24573c45d5aa0ff20a8b96b23d01e050e88

die() { printf 'ERROR: %s\n' "$*" >&2; exit 1; }

usage() {
    printf '%s\n' \
      'CloudLab sm220u setup (run as your ordinary login user).' \
      '' \
      'bash setup-sm220u.sh --inspect' \
      '    Read-only inventory; this is the default.' \
      'bash setup-sm220u.sh --setup /dev/nvme0n1 ...' \
      '    Require six to eight explicit, unused whole NVMe drives; create a striped' \
      '    ext4 volume, install dependencies, smoke-test, and launch TLC in Screen.' \
      'bash setup-sm220u.sh --start' \
      '    Reuse an existing large ext4/XFS filesystem mounted at /mnt/tlc.' \
      '' \
      'Defaults: 140g heap, 32 workers; override TLC_HEAP/TLC_WORKERS if needed.' \
      'RESDET_REPO_DIR defaults to ~/resdet-verification, regardless of script location.' \
      'Setup asks for a confirmation before initializing the listed drives.' \
      'Local storage, including this striped volume, is lost at experiment expiry.'
}

inspect() {
    uname -sr
    lsblk -o NAME,SIZE,TYPE,FSTYPE,MOUNTPOINTS,MODEL
    findmnt -T /
    if [[ -d "$MOUNT" ]]; then findmnt -T "$MOUNT"; fi
    df -hT /
    free -h
    printf '\nCPU topology:\n'
    lscpu | awk '/^CPU\(s\):|^Core\(s\) per socket:|^Socket\(s\):/'
    printf '\nNo changes made. Use --setup with six to eight verified unused NVMe drives,\n'
    printf 'or --start if a large filesystem is already mounted at %s.\n' "$MOUNT"
}

install_dependencies() {
    command -v sudo >/dev/null || die 'sudo is required.'
    command -v apt-get >/dev/null || die 'This script supports Ubuntu/Debian CloudLab images.'
    sudo -v
    sudo apt-get update
    sudo env DEBIAN_FRONTEND=noninteractive apt-get install -y \
        openjdk-17-jre-headless ca-certificates curl git screen rsync \
        lvm2 e2fsprogs util-linux
}

check_resources() {
    [[ "$HEAP" =~ ^[1-9][0-9]*g$ ]] || die 'TLC_HEAP must be a whole number of GiB, e.g. 140g.'
    [[ "$WORKERS" =~ ^[1-9][0-9]*$ ]] || die 'TLC_WORKERS must be a positive integer.'
    local mem_kib heap_gib
    mem_kib=$(awk '/^MemTotal:/ {print $2}' /proc/meminfo)
    heap_gib=${HEAP%g}
    (( heap_gib * 1024 * 1024 <= mem_kib * 70 / 100 )) || \
        die "Heap $HEAP exceeds 70% of physical RAM. Reduce TLC_HEAP."
    (( WORKERS <= $(nproc) )) || die 'TLC_WORKERS exceeds available logical CPUs.'
}

no_existing_run() {
    local processes sessions
    processes=$(pgrep -u "$(id -u)" -af '[j]ava.*(tla2tools|tlc2)' || true)
    [[ -z "$processes" ]] || die "A TLC process already exists; inspect it before starting another:
$processes"
    if command -v screen >/dev/null; then
        sessions=$(screen -ls 2>/dev/null || true)
        if awk '$1 ~ /^[0-9]+\.resdet$/ {found=1} END {exit !found}' <<< "$sessions"; then
            die 'Screen session resdet already exists. Inspect it with screen -r resdet.'
        fi
    fi
}

check_empty_mountpoint() {
    [[ ! -L "$MOUNT" ]] || die "$MOUNT must not be a symlink."
    if [[ -e "$MOUNT" ]]; then
        [[ -d "$MOUNT" ]] || die "$MOUNT is not a directory."
        mountpoint -q "$MOUNT" && die "$MOUNT is already mounted; use --start."
        [[ -z "$(sudo find "$MOUNT" -mindepth 1 -maxdepth 1 -print -quit)" ]] || \
            die "$MOUNT contains files; refusing to hide them with a mount."
    fi
    if awk '$1 !~ /^#/ && $2 == "/mnt/tlc" {found=1} END {exit !found}' /etc/fstab; then
        die '/etc/fstab already has an entry for /mnt/tlc; inspect or mount it before using --start.'
    fi
}

validate_disk_count() {
    (( $# >= 6 && $# <= 8 )) || die 'sm220u setup requires six to eight explicit NVMe disk paths.'
}

validate_disks() {
    validate_disk_count "$@"
    local disk prior size first_size=0 nodes signatures mounts root_nodes name
    DISKS=()
    root_nodes=$(lsblk -snrp -o NAME "$(findmnt -n -o SOURCE -T /)") || \
        die 'Cannot resolve root filesystem devices.'
    for disk in "$@"; do
        disk=$(readlink -f -- "$disk") || die 'Cannot resolve disk path.'
        [[ "$disk" =~ ^/dev/nvme[0-9]+n[0-9]+$ && -b "$disk" ]] || \
            die "$disk is not a whole NVMe namespace device."
        for prior in "${DISKS[@]}"; do
            [[ "$prior" != "$disk" ]] || die "Duplicate device: $disk"
        done
        if printf '%s\n' "$root_nodes" | grep -Fx -- "$disk" >/dev/null; then
            die "$disk backs the root filesystem."
        fi
        nodes=$(lsblk -nrp -o NAME "$disk") || die "Cannot inspect $disk."
        [[ "$nodes" == "$disk" ]] || die "$disk has partitions or mapped children."
        mounts=$(lsblk -nr -o MOUNTPOINTS "$disk") || die "Cannot inspect mounts on $disk."
        [[ -z "${mounts//[[:space:]]/}" ]] || die "$disk is mounted or used as swap."
        name=${disk##*/}
        [[ -d "/sys/class/block/$name/holders" ]] || die "Cannot inspect holders of $disk."
        [[ -z "$(find "/sys/class/block/$name/holders" -mindepth 1 -maxdepth 1 -print -quit)" ]] || \
            die "$disk is in use by another block device."
        signatures=$(sudo wipefs --no-act --noheadings --output TYPE "$disk") || \
            die "Cannot inspect signatures on $disk."
        [[ -z "${signatures//[[:space:]]/}" ]] || \
            die "$disk has existing signatures ($signatures); nothing was erased."
        size=$(sudo blockdev --getsize64 "$disk") || die "Cannot read size of $disk."
        (( size >= 900000000000 && size <= 1000000000000 )) || \
            die "$disk is not an expected approximately 960 GB sm220u disk."
        if (( first_size == 0 )); then first_size=$size; fi
        (( size == first_size )) || die 'Striped setup requires equal-capacity drives.'
        DISKS+=("$disk")
    done
    local groups
    groups=$(sudo vgs --noheadings -o vg_name) || die 'Cannot inspect existing volume groups.'
    if awk -v vg="$VG" '$1 == vg {found=1} END {exit !found}' <<< "$groups"; then
        die "Volume group $VG already exists; inspect it before continuing."
    fi
}

prepare_storage() {
    check_empty_mountpoint
    validate_disks "$@"
    printf '\nThese %s drives will be initialized for a striped TLC scratch volume:\n' "${#DISKS[@]}"
    printf '  %s\n' "${DISKS[@]}"
    printf 'About 95%% of their combined capacity will be mounted at %s.\n' "$MOUNT"
    printf 'The stripe has no disk-failure redundancy and does not survive node expiry.\n'
    local answer uuid
    read -r -p 'Type PREPARE to initialize exactly these drives: ' answer
    [[ "$answer" == PREPARE ]] || die 'Cancelled; no disks were initialized.'
    # Recheck after the prompt; never use force/wipe flags on existing signatures.
    check_empty_mountpoint
    validate_disks "$@"
    sudo pvcreate "${DISKS[@]}"
    sudo vgcreate "$VG" "${DISKS[@]}"
    sudo lvcreate --stripes "${#DISKS[@]}" --stripesize 256 --extents 95%FREE --name "$LV" "$VG"
    sudo udevadm settle
    sudo mkfs.ext4 -m 0 -L resdet_tlc "/dev/$VG/$LV"
    sudo mkdir -p "$MOUNT"
    sudo mount "/dev/$VG/$LV" "$MOUNT"
    uuid=$(sudo blkid -s UUID -o value "/dev/$VG/$LV")
    [[ -n "$uuid" && "$(findmnt -n -o UUID -T "$MOUNT")" == "$uuid" ]] || \
        die 'Mounted filesystem does not match the newly created volume.'
    sudo cp -a /etc/fstab "/etc/fstab.resdet-backup-$(date +%Y%m%d-%H%M%S)"
    printf 'UUID=%s /mnt/tlc ext4 defaults,nofail 0 2\n' "$uuid" | \
        sudo tee -a /etc/fstab >/dev/null
}

check_storage() {
    [[ ! -L "$MOUNT" ]] || die "$MOUNT must not be a symlink."
    mountpoint -q "$MOUNT" || die "$MOUNT is not mounted; refusing root-filesystem fallback."
    local source filesystem size available root_device data_device
    source=$(findmnt -n -o SOURCE -T "$MOUNT")
    filesystem=$(findmnt -n -o FSTYPE -T "$MOUNT")
    [[ "$filesystem" == ext4 || "$filesystem" == xfs ]] || die "Unsupported filesystem: $filesystem"
    root_device=$(findmnt -n -o MAJ:MIN -T /)
    [[ "$(findmnt -n -o MAJ:MIN -T "$MOUNT")" != "$root_device" ]] || \
        die "$MOUNT is backed by the root filesystem."
    size=$(df -B1 --output=size "$MOUNT" | awk 'NR==2 {print $1}')
    available=$(df -B1 --output=avail "$MOUNT" | awk 'NR==2 {print $1}')
    (( size >= 5000000000000 )) || die "$source has less than 5 TB capacity; inspect the NVMe setup."
    (( available >= 1000000000000 )) || die 'Less than 1 TB free; inspect earlier runs before starting.'
    [[ ! -L "$DATA" ]] || die "$DATA must not be a symlink."
    sudo mkdir -p "$DATA"
    sudo chown "$(id -u):$(id -g)" "$DATA"
    sudo chmod 0755 "$DATA"
    data_device=$(findmnt -n -o MAJ:MIN -T "$DATA")
    [[ "$data_device" == "$(findmnt -n -o MAJ:MIN -T "$MOUNT")" ]] || \
        die 'Data directory is on an unexpected filesystem.'
    local probe
    probe=$(mktemp "$DATA/.write-test.XXXXXX")
    rm -- "$probe"
    df -hT "$DATA"
}

fetch_inputs() {
    if [[ ! -e "$REPO" ]]; then
        git clone https://github.com/guojasonliu/resdet-verification.git "$REPO"
    fi
    [[ -f "$REPO/spec/Resdet.tla" && -f "$REPO/spec/ResdetResearch.cfg" ]] || \
        die "$REPO does not contain the expected model. Set RESDET_REPO_DIR."
    REPO=$(cd "$REPO" && pwd -P)
    mkdir -p "$REPO/tools"
    JAR="$REPO/tools/tla2tools-1.7.4.jar"
    if [[ ! -e "$JAR" ]]; then
        local download
        download=$(mktemp "$REPO/tools/.tlc-download.XXXXXX")
        if ! curl -fL --retry 3 --connect-timeout 20 \
            https://github.com/tlaplus/tlaplus/releases/download/v1.7.4/tla2tools.jar -o "$download"; then
            rm -- "$download"
            die 'TLC download failed.'
        fi
        if [[ "$(sha256sum "$download" | awk '{print $1}')" != "$JAR_SHA" ]]; then
            rm -- "$download"
            die 'Downloaded TLC checksum mismatch.'
        fi
        mv -n -- "$download" "$JAR"
    fi
    [[ "$(sha256sum "$JAR" | awk '{print $1}')" == "$JAR_SHA" ]] || \
        die "$JAR has an unexpected checksum; refusing to run it."
}

run_java() {
    local run=$1
    [[ "$run" == "$DATA"/research-* && -f "$run/settings" ]] || die 'Invalid run directory.'
    # settings is generated by this script and contains only validated numbers.
    local heap workers
    read -r heap workers < "$run/settings"
    [[ "$heap" =~ ^[1-9][0-9]*g$ && "$workers" =~ ^[1-9][0-9]*$ ]] || die 'Invalid run settings.'
    mountpoint -q "$MOUNT" || die 'TLC filesystem is no longer mounted.'
    exec 9>"$DATA/.research.lock"
    flock -n 9 || die 'Another setup-managed research run holds the lock.'
    cd "$run/inputs/spec"
    exec > >(tee -a "$run/tlc.log") 2>&1
    local cmd=(java -XX:+UseParallelGC "-Xmx$heap" "-Djava.io.tmpdir=$run/tmp"
      -jar "$run/inputs/tla2tools-1.7.4.jar" -terse -gzip -workers "$workers"
      -checkpoint 10 -fp 88 -seed 20260914 -metadir "$run/states"
      -config ResdetResearch.cfg Resdet)
    printf 'Command: '; printf '%q ' "${cmd[@]}"; printf '\n'
    "${cmd[@]}" &
    local pid=$! status
    printf '%s\n' "$pid" > "$run/java.pid"
    # Async children may inherit ignored SIGINT; SIGTERM reliably reaches Java.
    trap 'kill -TERM "$pid" 2>/dev/null || true' INT TERM
    set +e
    wait "$pid"
    status=$?
    # If a signal interrupted wait, wait again until Java is actually gone.
    while kill -0 "$pid" 2>/dev/null; do wait "$pid"; status=$?; done
    set -e
    printf '%s\n' "$status" > "$run/exit-status"
    printf '\nTLC exited with status %s. Files preserved at %s\n' "$status" "$run"
    printf 'Press Enter to close this Screen session.\n'
    read -r _ || true
    return "$status"
}

launch() {
    no_existing_run
    check_resources
    check_storage
    fetch_inputs
    local run
    run=$(mktemp -d "$DATA/research-$(date -u +%Y%m%d-%H%M%S)-XXXXXX")
    mkdir -p "$run/inputs" "$run/tmp"
    cp -R "$REPO/spec" "$run/inputs/spec"
    cp "$JAR" "$run/inputs/tla2tools-1.7.4.jar"
    cp "${BASH_SOURCE[0]}" "$run/launcher.sh"
    printf '%s %s\n' "$HEAP" "$WORKERS" > "$run/settings"
    (cd "$run/inputs" && sha256sum spec/Resdet.tla spec/ResdetResearch.cfg tla2tools-1.7.4.jar) > "$run/inputs.sha256"
    printf 'Running a short smoke test first; log: %s/smoke.log\n' "$run"
    if ! (cd "$run/inputs/spec" && java -XX:+UseParallelGC -Xmx2g "-Djava.io.tmpdir=$run/tmp" \
        -jar ../tla2tools-1.7.4.jar -terse -gzip -workers 1 -seed 20260914 \
        -metadir "$run/smoke-states" -config ResdetResearch.cfg -depth 100 -simulate num=2 Resdet) \
        > "$run/smoke.log" 2>&1; then
        tail -n 30 "$run/smoke.log"
        die 'Smoke test failed; full run was not launched.'
    fi
    no_existing_run
    screen -dmS resdet bash "$run/launcher.sh" --run "$run"
    printf 'Waiting for the actual Java process and initial states (up to 30 seconds)...\n'
    local attempt pid
    for ((attempt=0; attempt<30; attempt++)); do
        [[ ! -f "$run/exit-status" ]] || die "TLC exited; inspect $run/tlc.log"
        if [[ -s "$run/java.pid" && -f "$run/tlc.log" ]]; then
            read -r pid < "$run/java.pid"
            if kill -0 "$pid" 2>/dev/null && grep -q 'Finished computing initial states:' "$run/tlc.log"; then
                printf '\nTLC is running: PID=%s, heap=%s, workers=%s\n' "$pid" "$HEAP" "$WORKERS"
                printf 'Attach: screen -r resdet\nDetach: Ctrl-A, then D\n'
                printf 'Progress: tail -f %q\n' "$run/tlc.log"
                printf 'Disk: df -h /mnt/tlc\n'
                printf 'Checkpoint data and frozen inputs: %s\n' "$run"
                printf 'This command already launched the exhaustive run; do not start make separately.\n'
                printf 'Back up a consistent copy of this run directory outside the node before expiry.\n'
                return
            fi
        fi
        sleep 1
    done
    die "Startup has not been confirmed. Inspect $run/tlc.log and screen -r resdet before retrying."
}

main() {
    local mode=${1:---inspect}
    if (( $# > 0 )); then shift; fi
    case "$mode" in -h|--help) usage; return ;; esac
    [[ "$(uname -s)" == Linux ]] || die 'Run this script on the Linux CloudLab node.'
    case "$mode" in
        --inspect) (( $# == 0 )) || die 'No arguments expected.'; inspect ;;
        --setup)
            (( EUID != 0 )) || die 'Run as your ordinary user, without sudo; the script uses sudo as needed.'
            validate_disk_count "$@"
            no_existing_run
            check_resources
            install_dependencies
            prepare_storage "$@"
            launch
            ;;
        --start)
            (( $# == 0 && EUID != 0 )) || die 'Run --start as your ordinary user, with no extra arguments.'
            no_existing_run
            check_resources
            install_dependencies
            launch
            ;;
        --run) (( $# == 1 )) || die 'Missing internal run path.'; run_java "$1" ;;
        *) usage; die "Unknown option: $mode" ;;
    esac
}

if [[ "${BASH_SOURCE[0]}" == "$0" ]]; then main "$@"; fi
