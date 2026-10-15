# Verification, sign-off, and publication

Solve contributions are direct GitHub PRs. The protected checker validates the exact target and proof, the owner signs off on the checked commit, and the owner merges it. A separate trusted publisher records acceptance and rebuilds the atlas and leaderboard. No workflow merges a PR automatically.

## Protected checks

`solve-proposal.yml` uses trusted base-branch code. Draft PRs wait until marked ready, or until the owner explicitly dispatches a check. Pinned protected Lean dependencies are cached between runs; each submitted proof is still compiled and checked independently. It fetches the PR as data and freezes the base and head commit IDs. A solve may add only permitted proof, witness, and explanation files to one existing `data/<id>/` folder. Existing target, context, infrastructure, and generated files are protected. A mixed solve/maintenance change fails even with owner approval; split it into separate PRs.

The checker generates `HodgeTarget` from the base record, and optional `HodgeWitness` from exact witness data. It compiles the proposal inside an OS sandbox, replays all submitted modules with `leanchecker`, and audits the protected theorem type and transitive axioms. A submitted JSON witness requires an additional theorem binding the exact displayed polynomials to the same protected target. Printed claims are never verification evidence.

Candidate code receives no networking, credentials, or repository write access. Protected target artifacts, candidate artifacts, and the final trusted wrapper have separate write permissions. Linux uses Docker; local macOS checking uses `sandbox-exec`. The pinned toolchain, dependencies, verifier, and OS remain trusted components. Verification fails if isolation is unavailable.

The successful report records exact target/source hashes, base/head commits, the PR author, theorem, witness binding, toolchain, kernel replay, and axiom audit. The workflow posts `solve/lean` on the submitted commit and rejects a result if either PR commit changed during checking.

## Owner sign-off

`.github/solve-policy.json` selects `live` mode. A live solve requires the configured owner's approving review of the exact checked head. A new commit, dismissed approval, or subsequent request for changes requires renewed sign-off. Maintenance PRs also require explicit owner authorization, regardless of the mode.

GitHub does not permit authors to approve their own PRs. The owner can instead run the “Solve proposal” workflow with the PR number and full reviewed SHA in `approved_head`. Both the original workflow actor and rerun actor must be the configured owner, and the SHA must still be the current head. This records explicit sign-off on that commit, not on later updates. The existing GitHub UI or GitHub CLI can invoke this workflow; there is no separate submission CLI.

Use a **merge commit**, preserving the checked head as its second parent. Merge only against the checked base. Squash/rebase merges and base drift fail publication. When merging through GitHub CLI or an owner script, bind the merge request to the reviewed head SHA. Do not merge another solve until the previous publication commit has landed and the next proof has been checked against current main.

At launch, configure GitHub's available branch protection to require `solve/lean`, up-to-date branches, and owner-controlled merging. The workflow's failing status is not itself an unavoidable merge barrier without that repository setting. Changing protection or visibility is a separate owner-authorized remote operation. `preview` mode is available for infrastructure experiments, but its receipts cannot be published as accepted solves.

## Trusted publication

`publish-solve.yml` runs on a merged PR or an explicit retry. It checks out trusted main and invokes `scripts/proposals/publish.py`. The publisher requires:

- An owner-merged PR targeting this repository's main branch.
- A successful protected workflow run associated with the exact checked head and base.
- Matching workflow/verifier hashes and a matching preserved verification report.
- A merge commit whose parents are exactly the checked base and head.
- The same target and all proof, witness, and explanation hashes in the merged checkout.
- Contributor attribution matching the PR author.

It then writes `data/<id>/acceptance.json`, derives `solution.rec`, and runs the content builder and validators. The workflow commits these derived files to main. A failed or interrupted publication leaves no accepted solve in published output; rerun the workflow once the cause is resolved. The generated acceptance record is durable even after transient CI artifacts expire.

The site reads local generated files. It needs no GitHub service at runtime. It never awards credit from editable claimed identities, an unmerged proof, or a status flag. Mathematical source maintenance after acceptance must preserve or deliberately renew the receipt's bindings.

## Local checks

```sh
python3 scripts/proposals/test_check.py
python3 scripts/proposals/test_lean.py
```

The first checks file boundaries, schema, identity, and review logic. The second exercises the real Lean/sandbox path, including a small valid certificate and deliberately invalid inputs. These verifier regression tests belong to infrastructure changes; solve PRs run their actual submitted proof, not the regression suite. See `solve-proposals.md` for the contributor's local verification recipe.
