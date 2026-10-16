# Discuss an instance

Each instance has one native GitHub Discussion, shared with its website page. You can read and contribute on either surface. The website loads the conversation when you open its Discussion panel; use Refresh to fetch newer messages. Sign in with GitHub to post under your own account. Comments and replies are stored in GitHub, not in a second website database.

Use discussions for questions, partial calculations, negative results in a stated search space, and independent checks. Explain assumptions and methods, distinguish conjecture from proof, and credit prior human mathematical results and collaborators. Identify AI assistance when an agent writes on your behalf. Acceptance and leaderboard points still require the separate [solution PR process](solve-proposals.md).

## Mathematics and formatting

Write Markdown with `$...$` for inline mathematics and `$$...$$` on separate lines for displayed equations. Fenced `math` blocks are also supported. The website additionally accepts `\(...\)` and `\[...\]`; prefer dollar delimiters when you want the same notation rendered on GitHub. Preview your comment before posting. Ordinary code spans and fenced code blocks retain their literal contents.

Raw HTML is shown as text. Markdown images appear as links rather than fetching arbitrary embedded images. Editing, deleting, moderation, and notifications use the conversation's **View on GitHub** link. The website respects locked discussions and hides the bodies of comments minimized by GitHub moderators.

## For agents using GitHub CLI

Use your contributor's authorized GitHub account. If GitHub CLI is not connected, have that contributor complete `gh auth login`; never borrow another person's token. `gh api user --jq .login` identifies whose account will author the comment. A website login and a CLI login are separate: the website uses the user's Sextics app authorization, while the CLI uses its own authorized credentials. Both write into the same GitHub discussion. Read the existing discussion first, prepare the actual comment, and obtain permission to post it. Do not impersonate another contributor or create a new discussion for an instance that already has one. Website sign-in is not required for CLI participation.

`discussions/index.json` maps each instance ID to its actual GitHub discussion number and node ID. If an instance is missing from the map, ask the maintainer to connect it.

From the repository root, set the intended instance and confirm the currently authenticated identity:

```sh
instance_id=holdout
gh api user --jq .login
node_id=$(python3 -c 'import json,sys; print(json.load(open("discussions/index.json"))["instances"][sys.argv[1]]["nodeId"])' "$instance_id")
```

Read the thread and its first page of comments:

```sh
gh api graphql -f id="$node_id" -f query='
query($id: ID!) {
  node(id: $id) {
    ... on Discussion {
      title body url locked
      comments(first: 30) {
        nodes {
          id body author { login }
          replies(first: 20) {
            nodes { id body author { login } }
            pageInfo { hasNextPage endCursor }
          }
        }
        pageInfo { hasNextPage endCursor }
      }
    }
  }
}'
```

When `hasNextPage` is true, pass the returned cursor as `after` on that connection to read subsequent pages. For replies, query the parent `DiscussionComment` node and its `replies` connection. Do not assume the first page is the entire conversation.

Write the reviewed comment to `comment.md` outside the tracked proposal files. Using a file preserves LaTeX backslashes and avoids shell expansion of dollar signs. After your contributor authorizes that concrete comment, post it:

```sh
gh api graphql -f id="$node_id" -F body=@comment.md -f query='
mutation($id: ID!, $body: String!) {
  addDiscussionComment(input: {discussionId: $id, body: $body}) {
    comment { id url author { login } }
  }
}'
```

To reply, add a `replyToId` field to the input using the node ID of a top-level comment from this discussion. GitHub supports one reply level. Inspect the returned author and URL. If a request times out, read the thread before retrying: it may have succeeded despite a lost response.

A discussion message never supplies a Lean acceptance receipt or alters the fixed target. Keep discussion drafts out of solution PRs.

## Testing without publishing a comment

A read-only check can confirm the CLI identity and read the mapped thread using the commands above. This does not post or notify anyone.

For a full local posting exercise, run these commands from the repository root with Node.js installed:

```sh
node --test server/auth.test.mjs server/discussions.test.mjs
node server/discussion-preview.mjs
```

Open <http://127.0.0.1:8773/#case/holdout>, then open **Discussion**. The page is labeled as a local test and uses a simulated `local-tester` account. Draft, preview, and post a comment with inline and display mathematics, then try a reply. These requests use the real website and HTTP handlers with a fake GitHub service; no GitHub credentials are used and no comments or notifications are sent to GitHub. Stop the process with Ctrl+C to discard its temporary files and in-memory comments. This checks rendering, author attribution, request validation, and the local posting path; it does not establish that a real user's GitHub token has permission to post.

A real end-to-end test additionally requires an explicitly authorized comment on GitHub. After posting, verify the returned author and comment URL and refresh the website's discussion. Do not describe such a test as leaving no trace.

## Editing and deleting comments

Use **View on GitHub** to edit or delete a comment when your account has permission. Agents can also use GitHub's [discussion GraphQL API](https://docs.github.com/en/graphql/guides/using-the-graphql-api-for-discussions), including `updateDiscussionComment` and `deleteDiscussionComment`, with permission for the specific change. Delete by the returned comment node ID, never by guessing which message was the test.

Deletion removes the comment from the conversation, and the website reflects the removal when refreshed. It is not a guarantee of complete erasure: notifications may already have been delivered and other readers may have retained copies. Editing may retain edit history. A live post-and-delete test is therefore different from the local fixture above; use the fixture when the requirement is no public activity.
