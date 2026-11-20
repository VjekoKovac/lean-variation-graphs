"""Validate this submission against the pinned upstream formalization.yaml v0.4."""
import hashlib
import json
import sys
from importlib.metadata import version
from pathlib import Path
from urllib.request import urlopen

import jsonschema
import yaml

COMMIT = "99c678e569c7c4c0772db297c5ddd5e4c9b6322e"
URL = (
    "https://raw.githubusercontent.com/mathlib-initiative/formalization.yaml/"
    + COMMIT + "/schema/v0.4.schema.json"
)
EXPECTED_SHA256 = "25ff6b25ca4511635aff4443cf20480c15e59dddf19591c730950b442ea54fce"
with urlopen(URL, timeout=30) as response:
    data = response.read()
digest = hashlib.sha256(data).hexdigest()
if digest != EXPECTED_SHA256:
    sys.exit("Upstream schema digest mismatch")
schema = json.loads(data)
jsonschema.Draft7Validator.check_schema(schema)
project = Path(__file__).resolve().parents[1]
manifest = (project / "formalization.yaml").read_bytes()
jsonschema.Draft7Validator(schema).validate(yaml.safe_load(manifest))
print("Python", sys.version.split()[0], "| jsonschema", version("jsonschema"), "| PyYAML", version("PyYAML"))
print("upstream schema:", URL)
print("schema SHA-256:", digest)
print("formalization.yaml SHA-256:", hashlib.sha256(manifest).hexdigest())
print("PASS: formalization.yaml validates against upstream v0.4 (JSON Schema Draft 7).")
