.PHONY: check check-passing check-mutants check-research \
	check-research-exhaustive cloudlab-research fetch-tlc check-lean fetch-lean

check:
	./scripts/check.sh all

check-passing:
	./scripts/check.sh passing

check-mutants:
	./scripts/check.sh mutants

check-research:
	./scripts/check-research.sh simulate

check-research-exhaustive:
	./scripts/check-research.sh exhaustive

cloudlab-research:
	./scripts/cloudlab-research.sh

fetch-tlc:
	./scripts/fetch-tlc.sh

fetch-lean:
	bash ./scripts/fetch-lean.sh

check-lean:
	bash ./scripts/check-lean.sh
