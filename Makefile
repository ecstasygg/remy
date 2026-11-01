ISABELLE ?= isabelle

.PHONY: all check measure payload clean

all: .build/ready

.build/ready: ROOT $(wildcard src/*.thy src/core/*.thy) cli/driver.ML Makefile
	@test "$$('$(ISABELLE)' version)" = Isabelle2026
	"$(ISABELLE)" build -D . -j 1 -o threads=1 -o parallel_proofs=0
	"$(ISABELLE)" export -n -d . -O .build -x 'Remy.Export:code/remy.ML' Remy
	REMY_ROOT="$(CURDIR)" "$$('$(ISABELLE)' getenv -b POLYML_HOME)/$$('$(ISABELLE)' getenv -b ISABELLE_PLATFORM64)/polyc" -o .build/remy cli/driver.ML
	@touch $@

check: all
	python3 tests/native.py
	python3 tests/cli.py

measure: all
	python3 tests/measure.py

payload: all
	@mkdir -p .build/payload
	@set -e; for name in Rings Weave Cells; do .build/remy examples/$$name.remy .build/payload/$$name.BIN; .build/remy vectors examples/$$name.remy .build/payload/$$name.DAT; cp examples/$$name.remy .build/payload/$$name.TXT; done
	cp guest/Remy.HC .build/payload/Remy.HC

clean:
	rm -rf .build
