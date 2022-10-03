export IDRIS2 ?= idris2

.PHONY: build

build:
	${IDRIS2} --build sedris.ipkg

install: build
	${IDRIS2} --install sedris.ipkg

clean:
	$(RM) -r build
	$(RM) -r **/**/build
	@find . -type f -name 'output' -exec rm -rf {} \;
	@find . -type f -name '*.ttc' -exec rm -f {} \;
	@find . -type f -name '*.ttm' -exec rm -f {} \;
	@find . -type f -name '*.ibc' -exec rm -f {} \;