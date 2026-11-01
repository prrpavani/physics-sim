#!/usr/bin/env bash
# Runs `lake check` and `lake comparator` in a Linux container, on a clean copy of the committed
# and working tree, with `.lake` kept in a Docker volume. Needs Docker. Mathlib's cache is used
# when one exists for this platform; otherwise the needed parts are built, which can take an hour.
set -euo pipefail
cd "$(dirname "$0")/.."
docker build -q -t paradox-comparator -f scripts/Dockerfile.comparator scripts >/dev/null
docker run --rm --privileged \
  -v "$PWD:/project:ro" -v paradox-lake:/src/.lake \
  paradox-comparator bash -c '
    set -e
    git config --global --add safe.directory "*"
    cd /project && tar --exclude=.lake --exclude=.git --exclude=node_modules --exclude=./web --exclude=./apps -cf - . | tar -xf - -C /src
    cd /src
    git init -q . 2>/dev/null || true
    lake exe cache get || echo "no usable cache: building what is needed"
    lake build Paradox Paradox.Comparator.Challenge Paradox.Comparator.Solution
    set +e
    echo "=== lake check"; lake check; check=$?; echo "lake check exit: $check"
    echo "=== lake comparator"; lake comparator; comparator=$?; echo "lake comparator exit: $comparator"
    [ "$check" = 0 ] && [ "$comparator" = 0 ]
  '
