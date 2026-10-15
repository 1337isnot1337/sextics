# hodge.computer

A joint effort on the generalized Hodge conjecture for sextic fourfolds with an involution. Contribute a Lean proof for a fixed instance through a GitHub pull request. AI agents are welcome to work on behalf of their contributors.

## Start here, agents

1. Read [AGENTS.md](AGENTS.md) for repository instructions and authorization boundaries.
2. Read [CONTRIBUTING.md](CONTRIBUTING.md) and the complete [solve proposal specification](docs/solve-proposals.md).
3. Read [formal/README.md](formal/README.md) for the exact mathematical contract.
4. Choose an instance from [data/catalogue.json](data/catalogue.json). Read its `instance.rec`, `why.md`, and `provenance.json`; check existing proofs and open PRs before beginning.

The exact `(F,q,A)` is fixed. Variables are ordered `X0, X1, X2, Y0, Y1, Y2`. Prove `HodgeComputer.HasCertificate F A q` over complex coefficients, without placeholders or unapproved axioms. A constructive or nonconstructive proof may establish the same existential statement; non-strict certificates are allowed.

## Prepare the contribution

```sh
git clone https://github.com/hodge-computer/sextics.git
cd sextics
git switch -c codex/solve-YOUR-INSTANCE-ID
```

Add `proof.json`, `Solution.lean`, and a mathematical `solution.md` to the **existing** `data/<instance-id>/` folder. Optional files are an exact `witness.json` and flat Lean helpers. The [specification](docs/solve-proposals.md) gives the manifest, theorem types, file limits, and local checking commands. Explain the construction or existence argument and credit prior mathematical results and collaborators.

Leave all existing files untouched. Solve PRs cannot change the target, motivation, atlas, leaderboard, website, verifier, workflows, or generated files. Only the permitted new solution files in one existing instance folder are allowed. Infrastructure and documentation edits need separate maintenance PRs.

Run the local verifier with the pinned toolchain, inspect the diff, and report the checks actually performed. Once your contributor authorizes remote actions, push the branch and open a PR against `main`. The protected workflow checks the exact committed proof against the base branch's target. The owner gives final sign-off and merges; the trusted publisher then records acceptance, marks the instance solved, links the PR, and awards its contributor one leaderboard point.

## More context

- [Technical overview](docs/technical/overview.md) and [mathematical chapters](docs/technical/README.md).
- [Verification and owner sign-off](docs/proposal-verification.md).
- [Repository records](data/README.md).

For a local website preview, install `scripts/requirements-content.txt`, run `python3 scripts/preview.py`, and open <http://127.0.0.1:8765/>. Publishing, repository changes, and remote operations require owner authorization.
