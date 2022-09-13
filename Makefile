.PHONY: build
build:
	cargo build --release

.PHONY: check
check:
	cargo check --release

.PHONY: test
test:
	cargo test --release

.PHONY: coverage
coverage:
	cargo tarpaulin --avoid-cfg-tarpaulin --all-features --workspace --locked --ignore-tests -o Xml -o lcov

.PHONY: clippy
clippy:
	cargo clippy --release --locked --all-targets --all-features -- -D warnings

.PHONY: format
format:
	cargo fmt

.PHONY: build-docs
build-docs:
	cargo doc --release --target-dir ./HydraDX-math-dev-docs --no-deps

.PHONY: clean
clean:
	cargo clean
