#!/usr/bin/env bash
# Runs `lake check` and `lake comparator` in a Linux container, then checks `make run` works, on a clean
# copy of the working tree with `.lake` kept in a Docker volume. Needs Docker. Mathlib's cache is used when
# one exists for this platform; otherwise the needed parts are built, which can take an hour.
set -euo pipefail
cd "$(dirname "$0")/.."
docker build -q -t paradox-comparator -f scripts/Dockerfile.comparator scripts >/dev/null
docker run --rm --privileged \
  -v "$PWD:/project:ro" -v paradox-lake:/src/.lake \
  paradox-comparator bash -c '
    set -e
    git config --global --add safe.directory "*"
    cd /project && tar --exclude=.lake --exclude=.git --exclude=node_modules --exclude=./apps -cf - . | tar -xf - -C /src
    cd /src
    git init -q . 2>/dev/null || true
    lake exe cache get || echo "no usable cache: building what is needed"
    lake build Paradox Paradox.Comparator.Challenge Paradox.Comparator.Solution
    set +e
    echo "=== lake check"; lake check; check=$?; echo "lake check exit: $check"
    echo "=== lake comparator"; lake comparator; comparator=$?; echo "lake comparator exit: $comparator"
    echo "=== make run"
    (make run > /tmp/run.log 2>&1 &)
    for i in $(seq 1 120); do curl -s -m 1 -o /dev/null http://127.0.0.1:8787/ && break; sleep 1; done
    ui=$(curl -s -o /dev/null -w "%{http_code}" http://127.0.0.1:8787/)
    proofs=$(curl -s http://127.0.0.1:8787/api/proofs | grep -c "theorem speedLimit_holds")
    echo "make run: UI $ui, proof text found: $proofs"
    [ "$check" = 0 ] && [ "$comparator" = 0 ] && [ "$ui" = 200 ] && [ "$proofs" = 1 ]
  '
