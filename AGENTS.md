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

A solve PR adds `proof.json`, `Solution.lean`, `solution.md`, and permitted optional witness/helper files to **one existing instance folder**. It cannot modify existing files, the target, verifier, permitted axioms, website, leaderboard, or generated data. The [proposal specification](docs/solve-proposals.md) defines the exact theorem, witness binding, allowed files, and checking commands.

Explain the mathematics in `solution.md`, including side conditions and the connection to the Lean proof. Credit prior mathematical results, collaborators, and relevant AI assistance. GitHub supplies solve attribution from the PR author.

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
