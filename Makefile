# cairn_atproto: build and check. See README.md. Lean only: no Swift, no host.
export PATH := $(HOME)/.elan/bin:$(PATH)
export RESERVOIR_API_URL := https://cairn.registry.nexthub.sh/api/v1
# `cairn build` turns Lake's artifact cache on, which keeps .olean files out of the build
# directory; the ledger and audit import from there, so turn it off.
export LAKE_ARTIFACT_CACHE := false

LIBS = CairnAtproto CairnAtprotoProofs CairnAtprotoTests
FIXTURES = fixtures/public/*.json fixtures/synthesized/*.json

.PHONY: build lint audit ledger ledger-update kernel fixtures fixtures-update check clean

# The library, the proofs, the build-time tests (`#guard`) and the fixtures checker.
build:
	cd lean && lake build -q $(LIBS) fixtures

# Constructs that bypass the kernel, run unchecked code or aren't total (AGENTS.md, Rules), and
# `import Lean` in the library apps link (the claim commands are `meta import`ed).
lint:
	@! grep -rnE 'implemented_by|@\[extern|skipKernelTC|native_decide|bv_decide|^\s*(private |public )?(partial|unsafe) def|\bsorry\b|^\s*axiom ' \
	  lean/CairnAtproto lean/CairnAtproto.lean lean/CairnAtprotoProofs lean/CairnAtprotoProofs.lean \
	  lean/CairnAtprotoTests lean/CairnAtprotoTests.lean lean/Fixtures.lean \
	  || (echo "lint: forbidden construct (AGENTS.md, Rules)"; exit 1)
	@! grep -rnE '^\s*(public )?import Lean' lean/CairnAtproto lean/CairnAtproto.lean \
	  || (echo "lint: CairnAtproto must not import Lean"; exit 1)

# Every theorem depends on propext, Classical.choice and Quot.sound at most.
audit: build
	cd lean && lake exe audit $(LIBS)

# Every cairn_atproto^N claim is in claims.lock with its statement hash; `ledger-update` writes
# new ones.
ledger: build
	cd lean && lake exe ledger check --scope cairn_atproto --root CairnAtproto --lock ../claims.lock

ledger-update: build
	cd lean && lake exe ledger update --scope cairn_atproto --root CairnAtproto --lock ../claims.lock

# Replay every declaration through the kernel (unsandboxed: macOS has no bubblewrap).
kernel: build
	cd lean && lake check --inadvisably-no-sandbox

# Decode every fixture (recorded public responses and synthesized ones), compare with the golden
# summary and check every date against Python's calendar (tools/check-fixtures.py).
fixtures: build
	lean/.lake/build/bin/fixtures $(FIXTURES) | python3 -I tools/check-fixtures.py fixtures/expected.txt

fixtures-update: build
	lean/.lake/build/bin/fixtures $(FIXTURES) | python3 -I tools/check-fixtures.py fixtures/expected.txt --update

check: lint build audit ledger kernel fixtures

clean:
	rm -rf build lean/.lake/build
