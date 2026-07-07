# Melvin demo image: Python + Melvin + Boogie + Z3 + the demo server.
#
# Build from the REPOSITORY ROOT (the build context must include melvin/,
# examples/, and demo/):
#
#     docker build -f demo/Dockerfile -t melvin-demo .
#     docker run --rm -p 8080:8080 melvin-demo
#
# The build runs `melvin examples/counter.mml` as a smoke test, so a broken
# Python <-> Boogie <-> Z3 toolchain fails the build rather than the demo.

# ---- stage 1: fetch the Boogie .NET tool --------------------------------
FROM mcr.microsoft.com/dotnet/sdk:8.0 AS boogie
RUN dotnet tool install --global Boogie

# ---- stage 2: runtime ----------------------------------------------------
FROM mcr.microsoft.com/dotnet/runtime:8.0-bookworm-slim
ARG TARGETARCH
ARG Z3_VERSION=4.12.6

RUN apt-get update \
 && apt-get install -y --no-install-recommends \
        python3 python3-pip python3-venv curl unzip ca-certificates \
 && rm -rf /var/lib/apt/lists/*

# Z3 release binary matched to the image architecture (Boogie needs Z3).
RUN case "${TARGETARCH}" in \
      arm64) Z3_ARCH="arm64-glibc-2.35" ;; \
      *)     Z3_ARCH="x64-glibc-2.35" ;; \
    esac \
 && curl -fsSL "https://github.com/Z3Prover/z3/releases/download/z3-${Z3_VERSION}/z3-${Z3_VERSION}-${Z3_ARCH}.zip" \
      -o /tmp/z3.zip \
 && unzip -q /tmp/z3.zip -d /opt \
 && ln -s "/opt/z3-${Z3_VERSION}-${Z3_ARCH}/bin/z3" /usr/local/bin/z3 \
 && rm /tmp/z3.zip \
 && z3 --version

COPY --from=boogie /root/.dotnet/tools /opt/dotnet-tools
ENV DOTNET_ROOT=/usr/share/dotnet \
    MELVIN_BOOGIE=/opt/dotnet-tools/boogie \
    PATH="/opt/venv/bin:/opt/dotnet-tools:${PATH}"

WORKDIR /app
COPY pyproject.toml README.md LICENSE ./
COPY melvin ./melvin
COPY examples ./examples
COPY demo ./demo

RUN python3 -m venv /opt/venv \
 && pip install --no-cache-dir . -r demo/requirements.txt

# Smoke test: verify + run one example; the build fails if the toolchain is broken.
RUN melvin examples/counter.mml && melvin-run examples/oracle_safe.mml

RUN useradd -r -m melvin
USER melvin

EXPOSE 8080
CMD ["uvicorn", "demo.server.app:app", "--host", "0.0.0.0", "--port", "8080"]
