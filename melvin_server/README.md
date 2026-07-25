# Melvin web demo

A browser front end for Melvin: pick an example (or write your own MLL
program), press **Verify** to check it with Boogie, or **Run** to execute it
under all thread interleavings with the reference interpreter. Diagnostics are
mapped back to the editor; after verification each statement gets a colored
mover-letter chip (R/B/L/N/Y) in the editor gutter, like the paper's annotated
figures; a second tab shows the generated Boogie; share links encode the
program in the URL.

```
melvin_server/
  server/app.py       FastAPI server (verify in-process, interpreter in a
                      killable subprocess; rate limit, job queue, LRU cache)
  server/examples_manifest.py   the Examples menu (also the file allowlist)
  static/             the UI: no build step, vendored CodeMirror 5
  Dockerfile          Python + Melvin + Boogie + Z3 + server in one image
  deploy/             local Docker + Amazon Lightsail scripts
```

## Run locally (no Docker)

Requires a working `melvin` install with Boogie (see the top-level README).

The server is part of the `melvin` distribution, so `pip install melvin` is all
it takes:

```bash
melvin-server --reload                        # or: uvicorn melvin_server.app:app --reload
# open http://127.0.0.1:8000
```

The examples menu is served from the bundled `.mml` files (a checkout's
`examples/`, or `melvin/examples/` in an installed wheel); `MELVIN_EXAMPLES_DIR`
overrides that.

## Run locally (Docker)

No local Boogie/Z3/.NET needed — the image contains the whole toolchain and
the build fails if that toolchain doesn't verify `examples/counter.mml`:

```bash
melvin_server/deploy/run-local.sh                     # builds, then serves on :8080
# or by hand:
docker build -f melvin_server/Dockerfile -t melvin-demo .
docker run --rm -p 8080:8080 melvin-demo
```

## Deploy to Amazon Lightsail

One-time prerequisites:

1. [AWS CLI v2](https://docs.aws.amazon.com/cli/latest/userguide/getting-started-install.html),
   configured with `aws configure`.
2. The [Lightsail container plugin (`lightsailctl`)](https://lightsail.aws.amazon.com/ls/docs/en_us/articles/amazon-lightsail-install-software)
   — needed by `aws lightsail push-container-image`.
3. Docker.

Then:

```bash
melvin_server/deploy/deploy-lightsail.sh              # service melvin-demo, power small
melvin_server/deploy/deploy-lightsail.sh -n           # dry run: print the commands only
melvin_server/deploy/deploy-lightsail.sh -s my-demo -r us-west-2 -p micro
```

The script builds the image for `linux/amd64`, creates the container service
if it doesn't exist, pushes the image, deploys it with a health check on
`/api/health`, waits for it to go live, and prints the public HTTPS URL
(Lightsail terminates TLS for you).

* **Update**: re-run the script; it pushes a new image version and redeploys.
  Publishing a GitHub Release does this automatically — see the `lightsail` job
  in [`.github/workflows/release.yml`](../.github/workflows/release.yml), which
  runs this same script with credentials from repository secrets.
* **Cost**: the `small` power is ~$10/month while the service exists
  (`micro` ~$7 is enough for light traffic; verification is CPU-bound, so
  avoid `nano`).
* **Tear down** (stops billing):

  ```bash
  aws lightsail delete-container-service --service-name melvin-demo
  ```

## Server configuration

All knobs are environment variables (defaults in parentheses):

| Variable | Meaning |
|---|---|
| `MELVIN_DEMO_VERIFY_TIMEOUT` (30) | seconds of Boogie time per verify request |
| `MELVIN_DEMO_RUN_TIMEOUT` (10)    | seconds per interpreter run |
| `MELVIN_DEMO_MAX_SOURCE` (65536)  | max program size in bytes |
| `MELVIN_DEMO_MAX_JOBS` (2)        | concurrent Boogie / interpreter jobs |
| `MELVIN_DEMO_MAX_QUEUE` (8)       | queued jobs before returning 429 |
| `MELVIN_DEMO_MAX_STATES` (200000) | interpreter state bound |
| `MELVIN_DEMO_RATE` (30)           | requests per minute per client IP |
| `MELVIN_EXAMPLES_DIR`             | override the examples directory |
| `MELVIN_BOOGIE`                   | path to the Boogie executable |

## API

| Endpoint | Purpose |
|---|---|
| `GET /api/health` | 200 + Boogie path, or 503 if Boogie is missing |
| `GET /api/examples` | the Examples menu manifest |
| `GET /api/examples/{name}` | one example's source (allowlisted names only) |
| `POST /api/verify` `{source}` | `{status, verified, elapsed_ms, diagnostics[], boogie, movers[]}` |
| `POST /api/run` `{source}` | `{status, states, trace, elapsed_ms, diagnostics[]}` |

`status` is `verified | rejected | timeout | error` for verify and
`safe | unsafe | unknown | error` for run. Diagnostics carry 1-based
`line`/`col`/`end_line`/`end_col` plus a message. `movers` is a list of
`{line, effect}` mover letters (`Y B R L N E`) for the editor gutter, present
whenever the program parses and type-checks.

Tests live in `tests/test_demo_server.py` (they skip themselves if the demo
dependencies are not installed).
