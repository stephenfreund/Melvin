#!/usr/bin/env bash
# Deploy the Melvin demo to Amazon Lightsail Container Service.
#
# Usage:
#   melvin_server/deploy/deploy-lightsail.sh [options]
#
# Options:
#   -s NAME    service name        (default: melvin-demo)
#   -r REGION  AWS region          (default: your AWS CLI default region)
#   -p POWER   service power       (default: small;  nano|micro|small|medium|...)
#   -n         dry run: print every aws/docker command instead of executing
#   -h         help
#
# Prerequisites:
#   * docker
#   * AWS CLI v2, configured (`aws configure`)
#   * the Lightsail container plugin:
#       https://lightsail.aws.amazon.com/ls/docs/en_us/articles/amazon-lightsail-install-software
#     (`aws lightsail push-container-image` fails without it)
#
# Re-running the script deploys a new image version to the same service.
# Tear down (stops billing):  aws lightsail delete-container-service --service-name melvin-demo

set -euo pipefail

SERVICE="melvin-demo"
POWER="small"
REGION_ARGS=()
DRY=false

while getopts "s:r:p:nh" opt; do
  case "$opt" in
    s) SERVICE="$OPTARG" ;;
    r) REGION_ARGS=(--region "$OPTARG") ;;
    p) POWER="$OPTARG" ;;
    n) DRY=true ;;
    h) sed -n '2,22p' "$0"; exit 0 ;;
    *) exit 2 ;;
  esac
done

HERE="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "$HERE/../.." && pwd)"

run() {
  echo "+ $*"
  $DRY || "$@"
}

say() { echo; echo "## $*"; }

# ------------------------------------------------------------ preflight
missing=""
command -v docker >/dev/null || missing="$missing docker"
command -v aws    >/dev/null || missing="$missing aws"
if [ -n "$missing" ]; then
  echo "error: missing required tools:$missing" >&2
  exit 1
fi
if ! $DRY && ! aws lightsail push-container-image help >/dev/null 2>&1; then
  echo "error: the Lightsail container plugin (lightsailctl) is not installed;" >&2
  echo "see the URL in the header of this script" >&2
  exit 1
fi

# ------------------------------------------------------------ build (amd64!)
say "Building image (linux/amd64 — Lightsail runs x86)"
run docker build --platform linux/amd64 -f "$REPO_ROOT/melvin_server/Dockerfile" \
    -t melvin-demo "$REPO_ROOT"

# ------------------------------------------------------------ service
say "Ensuring container service '$SERVICE' exists"
if $DRY || ! aws lightsail get-container-services ${REGION_ARGS[@]+"${REGION_ARGS[@]}"} \
      --service-name "$SERVICE" >/dev/null 2>&1; then
  run aws lightsail create-container-service ${REGION_ARGS[@]+"${REGION_ARGS[@]}"} \
      --service-name "$SERVICE" --power "$POWER" --scale 1
  say "Waiting for the service to become READY"
  $DRY || until [ "$(aws lightsail get-container-services ${REGION_ARGS[@]+"${REGION_ARGS[@]}"} \
        --service-name "$SERVICE" \
        --query 'containerServices[0].state' --output text)" = "READY" ]; do
    sleep 10; echo "  ...still provisioning"
  done
fi

# ------------------------------------------------------------ push image
say "Pushing the image to Lightsail"
if $DRY; then
  run aws lightsail push-container-image ${REGION_ARGS[@]+"${REGION_ARGS[@]}"} \
      --service-name "$SERVICE" --label melvin-demo --image melvin-demo:latest
  IMAGE=":$SERVICE.melvin-demo.X"
else
  PUSH_OUT=$(aws lightsail push-container-image ${REGION_ARGS[@]+"${REGION_ARGS[@]}"} \
      --service-name "$SERVICE" --label melvin-demo --image melvin-demo:latest)
  echo "$PUSH_OUT"
  IMAGE=$(echo "$PUSH_OUT" | grep -o ":$SERVICE\.melvin-demo\.[0-9]*" | tail -1)
  if [ -z "$IMAGE" ]; then
    echo "error: could not determine the pushed image name" >&2
    exit 1
  fi
fi

# ------------------------------------------------------------ deploy
say "Creating deployment with image $IMAGE"
DEPLOY_JSON=$(mktemp)
sed "s|__IMAGE__|$IMAGE|" "$HERE/lightsail-deployment.json.tmpl" > "$DEPLOY_JSON"
run aws lightsail create-container-service-deployment ${REGION_ARGS[@]+"${REGION_ARGS[@]}"} \
    --service-name "$SERVICE" \
    --containers "$(python3 -c "import json;print(json.dumps(json.load(open('$DEPLOY_JSON'))['containers']))")" \
    --public-endpoint "$(python3 -c "import json;print(json.dumps(json.load(open('$DEPLOY_JSON'))['publicEndpoint']))")"
rm -f "$DEPLOY_JSON"

# ------------------------------------------------------------ wait + report
say "Waiting for the deployment to go ACTIVE (a few minutes)"
$DRY || until [ "$(aws lightsail get-container-services ${REGION_ARGS[@]+"${REGION_ARGS[@]}"} \
      --service-name "$SERVICE" \
      --query 'containerServices[0].state' --output text)" = "RUNNING" ]; do
  STATE=$(aws lightsail get-container-services ${REGION_ARGS[@]+"${REGION_ARGS[@]}"} \
      --service-name "$SERVICE" \
      --query 'containerServices[0].state' --output text)
  echo "  state: $STATE"
  [ "$STATE" = "RUNNING" ] && break
  sleep 15
done

say "Done"
$DRY || aws lightsail get-container-services ${REGION_ARGS[@]+"${REGION_ARGS[@]}"} \
    --service-name "$SERVICE" \
    --query 'containerServices[0].url' --output text
