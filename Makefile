
V_TARGET_SRC := $(shell find test/fixtures/unit_test_fixtures/ -name '*_target.v')

# Define their corresponding generated files
V_TARGET_GEN := $(V_TARGET_SRC:%=%.target.json)

.PHONY: all test install uninstall dump-json clean

build:
	dune build 

all:
	dune build --profile=release
#	DITTO_TRANSFORMATION=MAKE_INTROS_EXPLICIT dune exec fcc --  --plugin=constructive-plugin --diags_level=2 ./test/fixtures/constructive/ex2.v

proof_repair:
	dune build --profile=release
	dune exec fcc -- --plugin=shelley-plugin ./test/fixtures/ex_this_or_that.v

lens:
	dune build --profile=release
	dune exec fcc -- --plugin=lens-query-plugin ./test/fixtures/ex_this_or_that.v

# Rule to generate a .v.target.json from its .v source
%.v.target.json: %.v
	dune exec fcc -- --plugin=target-generator-plugin $< 2>/dev/null

test: $(V_TARGET_GEN)
	dune build --profile=release
	find test/fixtures/unit_test_fixtures/ -not -name "*_target.v"  -not -path '*/ignore/*'  -name '*.v' -exec  dune exec fcc -- --plugin=ditto-test-plugin {} 2>/dev/null \;
	dune runtest --profile=release	

PREFIX := $(HOME)/.local

dump-json:
	dune build ./test/json_dump_plugin/ --profile=release
	dune exec fcc -- --plugin=json-dump-plugin ./test/fixtures/ex_multiple_jumps.v

clean:
	dune clean
	dune cache clear
	cp ./_opam/bin/fcc ./vendor/fcc
	rm -f ./lib/rocq_version_optcomp.mlh
	rm -f test/fixtures/unit_test_fixtures/*.target.json
