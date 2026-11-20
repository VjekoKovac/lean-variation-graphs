#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
lean --version
lake --version
bwrap --version
# Palomar takes its own protected configuration. Add independent local kernels
# to a temporary copy so the submitted configuration stays portable.
verification_config=$(mktemp)
trap 'rm -f "$verification_config"' EXIT
python3 - "$verification_config" "$(lean --print-prefix)/bin" <<'PY'
import json
import sys
from pathlib import Path

config = json.loads(Path("comparator.json").read_text())
allowed = {"propext", "Classical.choice", "Quot.sound"}
if not set(config["permitted_axioms"]) <= allowed:
    raise SystemExit("Axiom allowlist is too broad")
bin_dir = Path(sys.argv[2])
config["external_kernels"] = {
    "nanoda": [str(bin_dir / "nanoda_bin")],
    "con-ron": [str(bin_dir / "con-ron")],
}
Path(sys.argv[1]).write_text(json.dumps(config))
PY
set -x
lake comparator --config "$verification_config"
