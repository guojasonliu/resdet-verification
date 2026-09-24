# sm220u setup and running experiment

Provisioned on 2026-09-15 UTC (2026-09-14 Pacific) using
[`setup-sm220u.sh`](setup-sm220u.sh).

- SSH: `gjl@sm220u-10s10541.wisc.cloudlab.us`
- Experiment hostname: `node0.resdet-veri.ucla-progsoftsys-pg0.wisc.cloudlab.us`
- Ubuntu 22.04; Linux `5.15.0-187-generic`; OpenJDK `17.0.20`.
- 32 physical cores / 64 logical CPUs; about 251 GiB OS-visible RAM.
- The actual node exposes **six**, not eight, Samsung 960 GB NVMe drives.
- `/dev/sda` remains the SATA boot drive, with the original root/boot/swap partitions.

## Storage preparation

All six NVMe drives were checked for partitions, filesystem signatures,
mounts, root-device ancestry, and mapped-device holders before preparation.
The script was run from `/users/gjl/resdet-verification` with:

```sh
bash scripts/setup-sm220u.sh --setup \
  /dev/nvme0n1 /dev/nvme1n1 /dev/nvme2n1 \
  /dev/nvme3n1 /dev/nvme4n1 /dev/nvme5n1
```

This is a record of the completed setup, not a command to repeat while TLC
is running. Device paths must be inspected again on every new node.

The script created volume group `resdet_tlc` and logical volume `states`,
striped across the six drives with a 256 KiB stripe size and 95% of capacity.
The LV is about 4.98 TiB. Its ext4 filesystem is mounted at `/mnt/tlc`, which
reports approximately 5.0 TiB usable. There is no disk-failure redundancy.

- Filesystem UUID: `07bb61ac-ea1b-487b-9581-5930455077f4`.
- The UUID mount entry was appended to `/etc/fstab`, after backing it up.
- `/mnt/tlc/resdet` is owned by `gjl`.
- Root still had approximately 56 GiB free after installation.
- Node-local storage is lost at experiment expiration, including this volume.

## TLC run

- Screen session: `resdet` (initial Screen PID `16566`).
- Initial Java PID: `16574`.
- Started: `2026-09-15 05:49:01 UTC`.
- Run directory: `/mnt/tlc/resdet/research-20260915-054859-PC7jpA`.
- Log: `tlc.log` inside that directory.
- Metadata: `states/` inside that directory; TLC adds a timestamped leaf directory.
- Frozen model and JAR: `inputs/`, verified against `inputs.sha256`.
- Heap: `-Xmx140g`; workers: `32`; queue compression: `-gzip`.
- Checkpoint interval: 10 minutes; fingerprint polynomial: `88`; seed: `20260914`.
- TLC 1.7.4, reporting `TLC2 Version 2.19 of 08 August 2024 (rev: 5a47802)`.
- Profile: `ResdetResearch.cfg`, five replicas, ten requests, two response values.

Model inputs matched repository commit `9ec1858eb66b463e84acab4f544d2fa1edc831dd`.
The versioned JAR SHA-256 is
`936a262061c914694dfd669a543be24573c45d5aa0ff20a8b96b23d01e050e88`.

Twelve non-destructive launcher tests passed on this node. The two-trace,
depth-100 simulation checked 205 states successfully. The exhaustive process
was independently verified alive and advancing after initialization. This
record does not claim that exhaustive checking has completed.

## Access and preservation

```sh
ssh gjl@sm220u-10s10541.wisc.cloudlab.us
screen -r resdet
```

Detach with Ctrl-A, then D. To inspect without attaching:

```sh
tail -n 20 /mnt/tlc/resdet/research-20260915-054859-PC7jpA/tlc.log
df -hT / /mnt/tlc
```

The complete provisioning output is also recorded on the node at
`/users/gjl/resdet-verification/setup-sm220u.log`.

No automatic off-node checkpoint backup or expiration monitor is configured.
Before expiration, preserve a consistent copy of the complete run directory,
including the input snapshots, log and full checkpoint metadata. A reservation
does not remove the experiment's own expiration time.
