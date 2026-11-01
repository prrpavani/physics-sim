.PHONY: install run build web serve

# Fetch the prebuilt Mathlib cache, then build and check every proof.
install:
	lake exe cache get
	lake build

# Run the formal transition function on a demo world.
run:
	lake exe paradox

build:
	lake build

# Serve the front end at http://127.0.0.1:8000. Without the Lean server it uses the mock engine.
web:
	python3 -m http.server 8000 --bind 127.0.0.1 --directory web

# Build and start the Lean server at http://127.0.0.1:8000. The browser then runs on the Lean model.
serve:
	lake build paradox-server
	.lake/build/bin/paradox-server 8000
