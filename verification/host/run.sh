#!/usr/bin/env bash
# This host forbids creating a netlink route socket in an empty network namespace.
# Give bwrap an outer empty network namespace so it need not configure loopback.
set -euo pipefail
export COMPARATOR_BWRAP="$(cd "$(dirname "$0")" && pwd)/offline-bwrap"
export LEAN_NUM_THREADS=2
export PATH="$(lean --print-prefix)/bin:/usr/local/bin:/usr/bin:/bin"
exec bwrap --tmpfs / --ro-bind /usr /usr --symlink usr/bin /bin --symlink usr/lib /lib \
  --symlink usr/lib64 /lib64 --symlink usr/sbin /sbin --proc /proc --dev /dev \
  --ro-bind /etc /etc --tmpfs /tmp --ro-bind /opt /opt --ro-bind /home /home \
  --dir /root --dir /run/user --dir /var --dir /sys --bind /workspace /workspace \
  --chdir "$PWD" -- "$@"
