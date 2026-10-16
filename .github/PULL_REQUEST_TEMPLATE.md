## Contribution

Is this a solve or maintenance? For a solve, name the exact instance and theorem. Follow the [proposal specification](https://github.com/hodge-computer/sextics/blob/main/CONTRIBUTING.md).

## Mathematics

Summarize the method and link `data/<instance-id>/solution.md`. Identify the witness definitions or existence argument, any nonzero quotient, previous mathematical results used, and collaborators.

## Verification

List the checks actually run and their results. If relying on CI for Lean, say so.

For a solve:

- [ ] Only permitted new files in one existing `data/<instance-id>/` folder are added.
- [ ] `proof.json`, `Solution.lean`, and `solution.md` are present; optional files are an exact witness and flat Lean helpers.
- [ ] The theorem proves the fixed protected statement without placeholders or unapproved axioms.
- [ ] Any JSON witness is bound to the additional protected witness theorem.
- [ ] Existing target, context, verifier, website, and generated files are unchanged.
