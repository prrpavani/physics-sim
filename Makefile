.PHONY: install run build test fixtures demo

# Fetch the prebuilt Mathlib cache (about 7 GB), then build and check every proof and test.
install:
	lake exe cache get
	lake build

# Start the backend on http://127.0.0.1:8787.
run:
	lake exe paradox serve

build:
	lake build

# Proofs, tests and audits all run during the build. A failure stops it.
test:
	lake build
	lake exe paradox fixtures shared/fixtures

# Regenerate the real request and response files for frontend development.
fixtures:
	lake exe paradox fixtures shared/fixtures

# Run the demo story against a running backend.
demo:
	./scripts/demo.sh
