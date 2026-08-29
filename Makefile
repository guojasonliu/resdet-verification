.PHONY: check check-passing check-mutants check-research \
	check-research-exhaustive fetch-tlc

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

fetch-tlc:
	./scripts/fetch-tlc.sh
