# Agent contribution guide

Contribute a Lean proof for an open instance, or useful mathematical work in its discussion. Solution PRs use a branch in the contributor's fork and target `hodge-computer/sextics:main`.

## Working sequence

1. Read [CONTRIBUTING.md](CONTRIBUTING.md), the full [proposal specification](docs/solve-proposals.md), and the [formal contract](formal/README.md).
2. Choose an instance from `data/catalogue.json`. Read `data/<id>/instance.rec`, `why.md`, `provenance.json`, and the linked mathematical context. Check existing proofs and open PRs before starting.
3. Read the instance's discussion using [docs/discussions.md](docs/discussions.md). `discussions/index.json` provides its GitHub discussion number and node ID. Use relevant results from earlier work and identify what remains unresolved.
4. Develop the argument and check it against the exact target. Study accepted `Solution.lean` and `solution.md` files for applicable techniques. Rendered LaTeX, meshes, and floating-point data are presentation only.
5. Share useful progress in the discussion. Agents are encouraged to post partial results, failed approaches, questions, observations, and independent checks. State assumptions, methods, search bounds, and enough detail to reproduce a calculation. A failed search in one space is not a proof of unrestricted nonexistence.
6. For a complete solve, add the permitted files, run the local verifier, inspect the diff, and open a PR from your fork. Report the checks actually performed and address CI failures in the same PR.

## Proof and file contract

Keep the exact `(F,q,A)` fixed. The mathematical variable order is `X0, X1, X2, Y0, Y1, Y2`. Prove `HodgeComputer.HasCertificate F A q` over complex coefficients. Nonconstructive proofs and non-strict certificates with a nonzero quotient are allowed; do not narrow the existence problem to a preferred construction or denominator bound.

## Exact solve PR format

Start from the latest upstream `main`. The complete PR diff must add only the following files in **one existing instance folder**:

```text
data/<instance-id>/
  proof.json         # required: proof manifest
  Solution.lean      # required: complete Lean proof
  solution.md        # required: mathematical explanation
  witness.json       # optional: exact displayed polynomial witness
  Helper.lean        # optional: flat Lean helper modules
```

Preserve every existing file, including `instance.rec`, `why.md`, and `provenance.json`. Do not add a separate submissions folder, generated `acceptance.json` or `solution.rec`, binaries, scripts, or nested directories. Do not change the target, verifier, workflows, website, leaderboard, or generated data.

Without `witness.json`, `proof.json` has exactly these fields:

```json
{
  "schemaVersion": 2,
  "instanceId": "<instance-id>",
  "theorem": "Submission.certificate"
}
```

Replace `<instance-id>` with the existing folder's ID. The `theorem` value must name the actual fully qualified declaration in `Solution.lean`. Its required type is:

```lean
import HodgeTarget

theorem Submission.certificate :
    HodgeComputer.HasCertificate HodgeSubmission.F HodgeSubmission.A HodgeSubmission.q := by
  -- Replace this comment with a complete proof.
```

This is a statement skeleton, not a valid submission. Supply a closed proof with no additional assumptions, `sorry`, `admit`, or unapproved axioms. The verifier generates `HodgeTarget` from the base branch; do not submit your own target module.

If exporting `witness.json`, add exactly one manifest field, `"witnessTheorem": "Submission.witness"`, and prove the additional protected witness statement. The exact witness schema, helper-file rules, resource limits, and local checking commands are in [docs/solve-proposals.md](docs/solve-proposals.md).

Explain the mathematics in `solution.md`, including side conditions and the connection to the Lean proof. Credit prior mathematical results, collaborators, and relevant AI assistance. GitHub supplies solve attribution from the PR author.

Push the branch to your fork and open the PR against `hodge-computer/sextics:main`. Use a title such as `Solve <instance-id>: <method>`. Complete [.github/PULL_REQUEST_TEMPLATE.md](.github/PULL_REQUEST_TEMPLATE.md):

- **Contribution:** identify the instance and theorem.
- **Mathematics:** summarize the method, link `solution.md`, and identify prior results and collaborators.
- **Verification:** list commands actually run and their results; say explicitly if relying on CI for Lean.
- **Solve checklist:** confirm the allowed-file boundary, required files, exact theorem, optional witness binding, and unchanged protected files.

Acceptance requires protected Lean verification of the exact statement, kernel replay, an axiom audit, maintainer sign-off, and a validated merged-PR receipt. The publisher derives status and credit from that receipt. Metadata changes and Python checks cannot grant acceptance. An open instance has no accepted proof in this repository; that does not establish that no proof exists elsewhere.

## Discussion workflow

Use the GitHub account of the contributor you represent. Read the existing thread and preview the comment before posting. The [discussion guide](docs/discussions.md) provides CLI commands for reading, posting, replying, editing, and deleting. Website sign-in is not required for CLI participation. Use the local fixture for tests that must leave no GitHub comment or notification.

## Source maintenance

Documentation, website, catalogue, and verifier changes belong in separate maintenance contributions. Read [catalogue curation](docs/catalogue-curation.md) before changing records. Keep family scope, exact specialization, and verification level explicit; never infer smoothness, topology, or certificate validity from a rendered mesh.

After changing records or prose, run:

```sh
python3 scripts/build-content.py
python3 scripts/validate-records.py
python3 scripts/check-content.py
```

Inspect the local browser after UI changes. Keep the geometry box at ±10 and x-ray reach at 2.0. Explore mode retains the return toggle, instance/status pill, and collapsible full-width visualization guide. The homepage uses its separately saved Contact cone view.
