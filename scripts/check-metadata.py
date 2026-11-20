"""Check local project metadata against the named comparison targets.

This checks local consistency. The public registry performs its own admission,
license, taxonomy, authorization, and review checks at the submitted Git commit.
"""
from pathlib import Path
import json
import tomllib
import yaml

root = Path(__file__).resolve().parents[1]
metadata = yaml.safe_load((root / "formalization.yaml").read_text())
config = json.loads((root / "comparator.json").read_text())
manifest = json.loads((root / "lake-manifest.json").read_text())
lake = tomllib.loads((root / "lakefile.toml").read_text())

assert metadata["version"] == "v0.4"
project = metadata["project"]
assert 0 < len(project["name"].strip()) <= 300
assert 0 < len(project["description"].strip()) <= 10_000
assert project["authors"] and project["responsible_maintainers"]
assert project["license"] == "Apache-2.0" and "Apache License" in (root / "LICENSE").read_text()
source = metadata["sources"][0]
assert source["id"] == "arXiv:2603.12462v1"
assert source["type"] == "paper" and source["relationship"] == "formalizes"
assert project["authors"] == source["authors"]
assert metadata["review"]["status"] and metadata["automation"]["methods"]
assert set(config) == {"challenge_module", "solution_module", "theorem_names", "permitted_axioms"}
assert set(config["permitted_axioms"]) <= {"propext", "Classical.choice", "Quot.sound"}
aligned = [row["lean"] for row in metadata["alignment"]["statements"]]
assert aligned == config["theorem_names"] and len(aligned) == 3
assert lake["name"] == manifest["name"]
assert lake["defaultToolchain"] == (root / "lean-toolchain").read_text().strip()
mathlib = next(pkg for pkg in manifest["packages"] if pkg["name"] == "mathlib")
assert mathlib["inputRev"] == lake["require"][0]["rev"] == lake["defaultToolchain"].split(":")[1]
print("Project, license declaration, paper version, author lists and all three target names agree.")
print("Lean toolchain:", lake["defaultToolchain"])
print("Mathlib revision:", mathlib["rev"])
print("Configured axioms:", ", ".join(config["permitted_axioms"]))
