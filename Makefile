.PHONY: install run build frontend comparator

# Fetch the prebuilt Mathlib cache (about 7 GB), then build and check every proof and test.
install:
	lake exe cache get
	lake build

# Start the app at http://127.0.0.1:8787. The built UI is committed in web/, so this needs no Node.
run:
	lake exe paradox serve

build:
	lake build

# Rebuild the UI in web/ after changing apps/frontend. Needs Node.
frontend:
	cd apps/frontend && npm install && npm run build

# Run lake check and lake comparator in a Linux container. Needs Docker.
comparator:
	./scripts/comparator.sh
