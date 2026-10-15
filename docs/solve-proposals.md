# Solve proposals

Contribute through a direct GitHub pull request for one fixed instance. Add the proof and explanation to that instance's **existing** `data/<instance-id>/` folder. The files remain there after acceptance; there is no separate submissions directory. GitHub supplies the contributor identity from the PR author.

## Start here

1. Read `AGENTS.md`, `CONTRIBUTING.md`, and `formal/README.md`.
2. Choose an instance from `data/catalogue.json`. Read its `instance.rec`, `why.md`, and `provenance.json`. Keep its exact `(F,q,A)` fixed; the variable order is `X0, X1, X2, Y0, Y1, Y2`.
3. Start a branch from the latest upstream `main`. Check for an existing `proof.json` and open PRs for that instance. This format accepts the first proof for an instance; revisions to an accepted proof need separate owner review.
4. Add only the solution files listed below. Do not edit or remove existing files.
5. Prove the exact theorem, explain the mathematics, and run the local check. Inspect the complete diff.
6. After your contributor authorizes remote actions, push the branch to an authorized repository and open a PR against `hodge-computer/sextics:main`. Suggested title: `Solve <instance-id>: <method>`. Complete the PR template and report the checks actually run.
7. Address verification failures in the same PR. The owner reviews the mathematical explanation and gives final sign-off before merging.

## Files

```text
data/<instance-id>/
  instance.rec       # existing: protected exact statement and presentation
  why.md             # existing: protected motivation
  provenance.json    # existing: protected mathematical context
  proof.json         # ADD: manifest below
  Solution.lean      # ADD: theorem matching the protected target
  solution.md        # ADD: mathematical explanation displayed on the website
  witness.json       # optional ADD: exact displayed polynomial witness
  Helper.lean        # optional ADD: flat Lean helper modules
```

The manifest has exactly these fields when no JSON witness is submitted:

```json
{
  "schemaVersion": 2,
  "instanceId": "your-instance-id",
  "theorem": "Submission.certificate"
}
```

With `witness.json`, add exactly one further field: `"witnessTheorem": "Submission.witness"`.

The trusted publisher adds `acceptance.json` and derives `solution.rec`, the rendered content, the atlas status, and leaderboard credit **after** an eligible merge. Do not submit these files or manually edit generated JSON/HTML. Attribution, PR URLs, and acceptance dates come from the reviewed GitHub event, not editable manifest fields.

## Protected Lean statement

The verifier generates `HodgeTarget` from the **base branch's** exact target and requires a closed theorem of this type:

```lean
import HodgeTarget

theorem Submission.certificate :
    HodgeComputer.HasCertificate HodgeSubmission.F HodgeSubmission.A HodgeSubmission.q := by
  -- Supply a complete proof here.
```

This is a statement skeleton, not a proof. The manifest names the actual fully qualified theorem. Do not add parameters, assumptions, placeholders, or replacement definitions of the protected target. Do not submit `HodgeTarget.lean`.

`HodgeComputer.Verify` is the finite witness interface over complex coefficients: a nonzero homogeneous denominator, six numerators of the required degrees, relative primality, and the full cleared divisibility identity. A nonzero quotient is allowed; the problem is not restricted to strict certificates or bounded denominator degrees. A nonconstructive argument may prove the same existential statement without exporting a witness.

### Optional displayed witness

`witness.json` has exactly these fields:

```json
{
  "d": 4,
  "D": "exact polynomial expression",
  "N": ["N0", "N1", "N2", "N3", "N4", "N5"],
  "Q": "exact polynomial expression"
}
```

The strings above are placeholders. Use actual polynomial expressions in `X0, X1, X2, Y0, Y1, Y2`, integer literals, `+`, `-`, `*`, nonnegative integer powers `**`, and rational coefficients formed by division by a nonzero integer. No floats, function calls, new variables, or polynomial denominators are accepted. `d` is a nonnegative integer and `N` has exactly six entries. Zero components are written `"0"`.

The verifier creates protected definitions in `HodgeWitness`. In addition to the existential theorem, prove:

```lean
import HodgeWitness

theorem Submission.witness :
    HodgeComputer.Verify HodgeSubmission.F HodgeSubmission.A HodgeSubmission.q
      HodgeWitness.d HodgeWitness.D HodgeWitness.N HodgeWitness.Q := by
  -- Supply the proof for these exact exported polynomials.
```

This additional binding prevents a correct existence proof from being paired with an incorrect displayed witness. The checker generates `HodgeWitness.lean`; do not submit it.

### Helpers and limits

Name flat helper files with `[A-Z][A-Za-z0-9_]*.lean` and import them as `Proposal.Helper`. That namespace is the verifier's temporary compilation layout, not a permanent repository directory. `Target.lean`, `Checked.lean`, and `Audit.lean` are reserved. Imports must be on single lines at the start of the module, with no dependency cycles. Trusted imports may start with `Mathlib.`, `HodgeComputer.`, or `HodgeTestbed.`.

Ordinary declarations and tactic proofs are accepted. Custom executable extensions, `axiom`, `sorry`, `admit`, and unchecked native decision procedures are refused. Shared infrastructure changes need a separate maintenance PR. Do not submit binaries, compiled artifacts, symlinks, executable scripts, Lake configuration, nested directories, or unrelated files.

The complete committed diff must consist solely of newly added permitted solution files in **one existing instance folder**. Edits to `instance.rec`, `why.md`, the leaderboard, the website, the verifier, workflows, or any other existing file fail validation. Owner approval does not override this solve-file boundary. A PR without a solve is treated as maintenance and requires owner authorization of its exact head commit.

Limits are in `.github/solve-policy.json`: 64 files, 16 MiB of source, a 30-minute proof budget, and 6 GiB memory. The allowed axiom set is `propext`, `Classical.choice`, and `Quot.sound`.

## Mathematical explanation

Write `solution.md` so the argument is understandable without reading Lean. Describe the main idea, the witness or existence argument, all side conditions, and the correspondence to important Lean definitions and lemmas. For a construction, explain `D`, the six numerators, and the quotient, including nonvanishing, degrees, relative primality, and the cleared identity. Use LaTeX for formulas. Identify where previous human mathematical results enter the proof and credit their authors, along with collaborators and relevant AI assistance.

The direct PR author receives the solve credit under their own GitHub account. Each distinct accepted instance earns one point. Documentation and other contributions retain their authorship but do not independently earn a solve point.

## Local verification

Install Python 3.11 with `scripts/requirements-content.txt` and the pinned toolchain in `formal/lean/lean-toolchain`. Keep the committed Lake manifest. Prepare dependencies once:

```sh
python3 -m pip install -r scripts/requirements-content.txt
(cd formal/lean && lake exe cache get && lake build HodgeComputer.Verify)
```

The verifier requires macOS with `sandbox-exec`, or Linux with Docker and a non-root user. From the repository root, replace the instance ID below:

```sh
python3 - <<'PY'
import json, sys, tempfile
from pathlib import Path
import yaml
sys.path.insert(0, "scripts/proposals")
from acceptance import accepted_sources
from check import ROOT, module_order
from sandbox import verify

instance_id = "your-instance-id"
folder = ROOT / "data" / instance_id
files = {name: (folder / name).read_bytes() for name in accepted_sources(folder)}
manifest = json.loads(files["proof.json"])
instance = yaml.safe_load((folder / "instance.rec").read_text())
policy = json.loads((ROOT / ".github/solve-policy.json").read_text())
order, imports = module_order(files)
logs = Path(tempfile.mkdtemp(prefix="hodge-proof-check-"))
print(f"Verification logs: {logs}", flush=True)
print(json.dumps(verify(ROOT, files, instance, manifest, order, imports, policy, logs), indent=2))
PY
```

This checks the proof against the checkout's target and exports logs, without contacting GitHub. GitHub additionally validates the complete Git diff, file modes, manifest schema, source sizes, attribution, and immutable trusted base/head commits. A local result is development feedback; it is not a GitHub acceptance receipt. If you rely on CI rather than running Lean locally, say so in the PR.

## Review and acceptance

The protected workflow compiles in an OS sandbox, replays every submitted module with `leanchecker`, and audits the exact theorem and transitive axioms. Proposal code receives no network access, repository write access, or GitHub credentials. An updated PR commit requires fresh checks and owner sign-off.

The owner merges the checked head with a merge commit. The trusted publication workflow then validates the successful run, source hashes, unchanged target, contributor identity, and merge parents. It writes an acceptance receipt and rebuilds the website and leaderboard. The instance remains open if publication fails; fix the cause and rerun publication rather than editing status flags. See [verification and owner sign-off](proposal-verification.md).
