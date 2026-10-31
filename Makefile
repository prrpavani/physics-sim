.PHONY: install run build

# Fetch the prebuilt Mathlib cache, then build and check every proof.
install:
	lake exe cache get
	lake build

# Run the formal transition function on a demo world.
run:
	lake exe paradox

build:
	lake build
