#!/usr/bin/env bash
# Build the Melvin demo image and run it on http://localhost:${PORT:-8080}
set -euo pipefail
cd "$(dirname "$0")/../.."

docker build -f demo/Dockerfile -t melvin-demo .
exec docker run --rm -p "${PORT:-8080}:8080" --name melvin-demo melvin-demo
