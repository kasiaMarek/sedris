export IDRIS2 ?= idris2

.PHONY: build

build:
	${IDRIS2} --build sedris.ipkg

install: build
	${IDRIS2} --install sedris.ipkg

build-test:
	make -C test testbin IDRIS2=${IDRIS2} IDRIS2_PATH=${TYRE}

test: install build-test
	make -C test test IDRIS2=${IDRIS2} IDRIS2_PATH=${TYRE} only=$(only)

clean:
	$(RM) -r build
	$(RM) -r **/**/build
	@find . -type f -name 'output' -exec rm -rf {} \;
	@find . -type f -name '*.ttc' -exec rm -f {} \;
	@find . -type f -name '*.ttm' -exec rm -f {} \;
	@find . -type f -name '*.ibc' -exec rm -f {} \;