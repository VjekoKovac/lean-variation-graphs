# Local verification environment

On a regular Linux installation with bubblewrap and user namespaces, run
`bash scripts/verify.sh` from the repository root. The GitHub workflow uses
that command. Lake builds and exports the Challenge and Solution separately,
checks the theorem types and the axiom allowlist, and replays the Solution
with the default Lean kernel, NanoDa and con-ron.

The local verification machine uses a restricted container filesystem.
The wrapper `run.sh` gives Lake the expected Linux directories.
`offline-bwrap` starts a fresh user and network namespace for a build,
export or checker. Loopback stays down in that namespace. The remaining
filesystem and process isolation arguments are those supplied by Lake.
Dependencies were already present at the Git revisions in the manifest.

For the local run, the sources, pinned dependencies and Lean toolchain
were under `/workspace`. With that layout the command is

```sh
bash verification/host/run.sh bash scripts/verify.sh
```

The host wrapper assumes Linux and the stated local layout. It is separate
from the portable project sources and the standard CI command.
