# Agent entry points

Ask the owner before performing remote operations. Do not publish, push, create repositories, open or merge PRs, or connect services without authorization for that concrete action. Prepare and test locally first.

Read `README.md`, `CONTRIBUTING.md`, `docs/solve-proposals.md`, `formal/README.md`, and `docs/catalogue-curation.md` before work. Exact targets live in `data/<id>/instance.rec`; rendered LaTeX, meshes, and floating-point data are presentation only. The mathematical variable order is `X0, X1, X2, Y0, Y1, Y2`.

A solve PR adds `proof.json`, `Solution.lean`, `solution.md`, and permitted optional witness/helper files to one existing instance folder. Do not edit any existing file. Never modify the target, verifier, permitted axioms, website, leaderboard, or generated data to make a proof pass. See the full specification for the exact theorem and checked file boundary.

Formal acceptance requires a protected Lean check of the exact existential statement, kernel replay, permitted axioms, owner sign-off, and a validated merged-PR receipt. Neither metadata changes nor Python checks grant acceptance. The publisher derives status and credit from that receipt. A nonzero quotient is allowed; do not accidentally restrict the problem to strict certificates.

Read each instance's `why.md`, `provenance.json`, and linked mathematical context before attempting it. An open instance has no accepted proof in this repository. A negative result in one search space is not a negative result for the unrestricted problem. Keep family scope, exact specialization, and verification level explicit; never infer smoothness, topology, or validity from a mesh.

For separately authorized source maintenance, run `python3 scripts/build-content.py`, `python3 scripts/validate-records.py`, and `python3 scripts/check-content.py` after changing records or prose. Inspect the browser after UI changes. The static site has no external runtime dependencies. Explore mode retains only the return toggle, the instance/status pill, and the collapsible full-width visualization guide. Keep the geometry box at ±10 and x-ray reach at 2.0. The homepage retains its separately saved original Contact cone view.
