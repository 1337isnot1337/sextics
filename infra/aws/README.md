# AWS hosting

The static website is served from a private S3 bucket through CloudFront. Only
`/auth/*` and `/api/*` reach API Gateway and the Node 24 Lambda function. GitHub
remains the discussion store; DynamoDB holds short-lived login sessions and
one-use OAuth flows. Secrets Manager holds the existing Sextics GitHub App
credentials. No Lean builds run in AWS.

GitHub's `main` branch is the source of truth for the website. Make content and
code changes through reviewed commits; the static publishing workflow builds
from that branch and uploads its public artifact. The repository can stay
private while CloudFront serves the website publicly. Do not edit the hosted
files independently of the repository.

`template.json` describes the website infrastructure. `artifacts.json` creates
the separate private bucket used for Lambda deployment packages. The
CloudFormation service role is named `sextics`; the Lambda runtime role has only
the permissions needed for its session table, app secret, and log stream.
Provisioning or changing these resources requires the owner's authorization.

## Build a release

Use a reviewed checkout containing the current accepted records. Do not deploy
an old migration baseline or a contributor's unchecked branch.

```sh
python3 scripts/build-content.py
python3 scripts/validate-records.py
python3 scripts/check-content.py
npm ci --prefix server --ignore-scripts
node --test server/*.test.mjs
python3 infra/aws/package.py --site . --output /tmp/sextics-release
```

The packager uses an explicit public-file allowlist. It never copies the whole
repository, `.git`, credentials, server sources, dependencies, or local caches
into the public website. The Lambda archive contains only the runtime modules,
pinned dependencies, instance catalogue, and discussion mapping. Its SHA-256
and the public-file counts are recorded in `build.json`. Do not put credentials
in either package.

## Deploy

Create the artifacts stack first, then upload `lambda.zip` to its private bucket
under `lambda/<sha256>.zip`. Create or update the `hodge-sextics` stack with:

- `ArtifactBucket`: the artifacts-stack bucket;
- `ArtifactKey`: the uploaded package key;
- `SiteOrigin`: `https://hodge.computer`;
- `DomainName` and `CertificateArn`: the domain and its validated ACM certificate
  in `us-east-1`, or empty strings while preparing the CloudFront preview.

Use the `sextics` service role and acknowledge `CAPABILITY_NAMED_IAM`. Preserve
existing parameter values on updates. Inspect CloudFormation events and require
`CREATE_COMPLETE` or `UPDATE_COMPLETE`; submitting a deployment is not evidence
that it succeeded.

The outputs identify the website bucket, CloudFront distribution, API, session
table, and app secret. Upload the public package to the website bucket with
`Cache-Control: public,max-age=60`; use a CloudFront invalidation for immediate
rollout. Upload assets and content before `index.html` and `data/revision.json`
so a polling client discovers the new revision after its files are available.
Retain older content-addressed meshes while existing tabs may still need them.

Copy the existing GitHub App configuration directly from its private local
file into the named Secrets Manager secret, without printing it or writing it
to the checkout. There is no production registration endpoint or setup token.
When rotating this configuration, restart the Lambda execution environments
with a configuration/code update, because each environment caches the secret.

Infrastructure and backend releases are owner-operated. To activate
`.github/workflows/deploy-website.yml`, install the owner-approved
`publisher.json` stack and set the repository variable `AWS_WEBSITE_ROLE` to its
role output after merging the workflow. This separate role can upload static
files and invalidate this distribution; it cannot read app secrets, sessions,
or change Lambda or IAM. It trusts only this repository's `main` identity,
including the immutable organization and repository IDs in the current GitHub
OIDC subject format. Recheck that identity if the repository is ever recreated.

A GitHub-token push from the acceptance publisher does not itself start another
push workflow. The deployment workflow therefore handles successful
`workflow_run` events for `Publish accepted solve`, as well as reviewed content
pushes to `main`. It always checks out current `main`, never the submitted proof
branch or its artifacts. It does not run Lean again. Lambda code and new
discussion mappings require an owner-operated backend deployment separately.

## Domain and email

The domain remains registered at Hover. Its Route 53 hosted zone must preserve
Titan's MX, SPF, and DKIM records. Take a complete record inventory before any
nameserver change and compare all new authoritative nameservers with the old
mail records. DNS TTL expiry and certificate validation can delay cutover.

After the certificate is issued, attach it and the domain alias to CloudFront,
then point the apex A and AAAA alias records at that distribution. Confirm HTTPS
and the API before switching the existing GitHub App's homepage and callback to
the production URLs listed in [the service instructions](../../server/README.md).
Keep the old preview callback until the production sign-in test succeeds.

## Verification and operations

Check the homepage, a rendered surface, technical content, and an instance's
discussion panel. Check `/api/session`, disabled `/auth/setup`, and inaccessible
`/.git/config` and `/server/` paths. API responses and redirects must remain
uncached, and cookies must be Secure, HttpOnly, and SameSite=Lax. Perform a real
owner sign-in/sign-out test; obtain permission before posting a test comment.
Private GitHub discussions must remain unavailable to anonymous visitors.

DynamoDB TTL is eventual cleanup, not the authorization boundary. Application
checks reject expired sessions immediately. Conditional operations prevent
OAuth replay and enforce the shared posting throttle. Revoking a session must
take effect across Lambda environments.

The initial API limit is five requests/second with a burst of ten, Lambda
reserved concurrency is five, and DynamoDB on-demand throughput is capped at
25 read and 25 write units/second. Lambda logs are retained for seven days;
application logs must not contain OAuth URLs, cookies, tokens, or comment bodies.
These limits reduce exposure to excessive use but are not a billing cap.

CloudFormation retains the public-file bucket and GitHub App secret on stack
deletion. Any shutdown or cleanup must deliberately review those retained
resources and the domain's mail records. Deleting hosting must not delete or
invalidate Titan email configuration.
