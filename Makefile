COMPILER ?= mlton

SOURCES = \
  src/main.mlb \
  src/main.sml \
  src/util/NodeID.sml \
  src/util/UniqueName.sml \
  src/util/sources.mlb \
  src/provenance/sources.mlb \
  src/provenance/ProvenanceEvent.sml \
  src/provenance/Provenance.sml \
  src/frontend/irs/source/SourceAst.sml \
  src/frontend/irs/source/SourceAstToJson.sml \
  src/frontend/irs/after-debasification/AfterDebasificationToJson.sml \
  src/frontend/irs/after-record-unification/AfterRecordUnification.sml \
  src/frontend/irs/after-boolean-elaboration/AfterBooleanElaboration.sml \
  src/frontend/irs/after-infix-elaboration/AfterInfixElaboration.sml \
  src/frontend/irs/after-debasification/AfterDebasification.sml \
  src/frontend/translations/to-source/Parser.sml \
  src/frontend/translations/to-source/ToSourceAstSML.sml \
  src/frontend/translations/to-source/ToSourceAst.sml \
  src/frontend/translations/record-unification/RecordUnification.sml \
  src/frontend/translations/boolean-elaboration/BooleanElaboration.sml \
  src/frontend/translations/infix-elaboration/InfixElaboration.sml \
  src/frontend/translations/debasification/Debasification.sml \
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
