COMPILER ?= mlton

SOURCES = \
  src/main.mlb \
  src/main.sml \
  src/util/NodeID.sml \
  src/util/UniqueName.sml \
  src/util/sources.mlb \
  src/frontend/SourceAst.sml \
  src/frontend/Parser.sml \
  src/frontend/ToSourceAstSML.sml \
  src/frontend/ToSourceAst.sml \
  src/frontend/SourceAstToJson.sml \
  src/frontend/sources.mlb

build/bin/abysmal: $(SOURCES)
	mkdir -p build/bin
	$(COMPILER) -output $@ src/main.mlb

.PHONY: fmt
fmt:
	smlfmt --force -skip src/frontend/smlfmt src/main.mlb

.PHONY: clean
clean:
	rm -rf build/
