"""Run PalomarSubmission's own metadata and Lean-file intake checks locally.

Supply the path to a PalomarSubmission checkout. The accompanying log names the
commit used. This preflight does not contact the registry or submit anything.
"""
import hashlib
import sys
from pathlib import Path

project = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(Path(sys.argv[1]).resolve()))
from scripts import source_requirements, submission_contract

manifest_path = project / "formalization.yaml"
manifest = submission_contract.load_formalization_metadata(manifest_path)
provenance = submission_contract.normalized_provenance(manifest)
print("formalization.yaml SHA-256:", hashlib.sha256(manifest_path.read_bytes()).hexdigest())
print("Palomar metadata and source-provenance fields: PASS")
print("result origin:", provenance["result_origin"])
print("repository role:", provenance["repository_role"])
summary, issues = source_requirements.inspect_lean_sources(project)
print("Lean source files checked:", summary["files_checked"])
print("maximum lines per file:", summary["maximum_lines"])
if issues:
    for issue in issues:
        print(issue)
    sys.exit(1)
print("Palomar Lean source-format requirements: PASS")
