# Replaying the checks

Run these commands from the directory containing `lean-toolchain`.

```sh
lake exe cache get
lake build
lake env lean Axioms.lean
bash scripts/verify.sh
```

The last command requires Linux, Python 3, bubblewrap and permission to
create user namespaces. GitHub Actions supplies a Linux environment for
this step. The local verification machine used the [host wrapper](host/README.md).
The toolchain, dependency revisions and enabled axiom names are recorded in
[metadata.log](metadata.log).

## What each check establishes

* `lake build` checks that the project modules compile. `Challenge.lean`
  contains three specification holes, one in each theorem. Its warnings are
  expected. The zero hole counts reported in `formalization.yaml` apply to the implementation and its definitions. `Solution.lean` does not import `Challenge.lean`.
* `lake env lean Axioms.lean` prints the transitive axioms of the actual
  proved declarations. [axioms.log](axioms.log) contains this output.
* [comparator.log](comparator.log) gives the output of the independent
  Challenge and Solution builds, export, comparison, allowlist check and
  proof replay. Lake Comparator checks the named theorem types and the
  definitions occurring in those types. The proofs are replayed with Lean,
  NanoDa and con-ron. The comparison selects Theorems 1, 2 and 4.
* From a Linux shell, `sha256sum -c verification/proof-inputs.sha256`
  checks the source files in those theorem import chains, the lockfiles
  and the comparison script against the local verification snapshot.
* [negative-control.log](negative-control.log) records a separate, intentionally
  incomplete two-line proof. The same three-axiom allowlist caused Comparator
  to reject it for using `sorryAx`.
* [four-crosscheck.txt](four-crosscheck.txt) counts exhaustive checks over the
  specified *sample* of integer-valued vertex functions. The theorem for all
  real-valued functions follows from the proved linear inequalities and the
  graph classification in the Lean modules.

The [build transcript](build.log) includes the ordinary project build. The [upstream schema check](upstream-schema.txt) validates the shipped metadata against the pinned v0.4 JSON Schema. The [Palomar intake transcript](palomar-input.txt) runs the registry project's own metadata, provenance, and Lean source-format checks and records its Git revision. These checks use the local repository copy.

The included logs describe local verification. A public GitHub Actions run is
created by pushing the project to GitHub. A Palomar decision is a separate
registry action on the submitted full Git commit.
