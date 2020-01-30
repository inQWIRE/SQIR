# Using the example from https://coq.inria.fr/refman/practical-tools/utilities.html#reusing-extending-the-generated-makefile

# KNOWNTARGETS will not be passed along to CoqMakefile
KNOWNTARGETS := CoqMakefile all examples mapper optimizer voqc clean

# KNOWNFILES will not get implicit targets from the final rule, and so
# depending on them won't invoke the submake
# Warning: These files get declared as PHONY, so any targets depending
# on them always get rebuilt
KNOWNFILES := Makefile _CoqProject

.DEFAULT_GOAL := invoke-coqmakefile

CoqMakefile: Makefile _CoqProject
	git submodule init
	git submodule update
	$(COQBIN)coq_makefile -f _CoqProject -o CoqMakefile

invoke-coqmakefile: CoqMakefile
	$(MAKE) --no-print-directory -f CoqMakefile $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))

.PHONY: invoke-coqmakefile $(KNOWNFILES)

###########################################################
##		      Your targets here			 ##
###########################################################

QWIRE := externals/QWIRE
SQIR := SQIR/src
examples := SQIR/examples
optimizer := VOQC/src/optimizer
mapper := VOQC/src/mapper

COQ_OPTS := -R . Top

all: examples mapper optimizer $(optimizer)/PropagateClassical.vo $(optimizer)/RemoveZRotationBeforeMeasure.vo VOQC/src/experimental/BooleanCompilation.vo

examples: invoke-coqmakefile $(examples)/Deutsch.vo $(examples)/DeutschJozsa.vo $(examples)/GHZ.vo $(examples)/Superdense.vo $(examples)/Teleport.vo

mapper: invoke-coqmakefile $(mapper)/SimpleMapping.vo $(mapper)/MappingExamples.vo

optimizer: invoke-coqmakefile $(optimizer)/Optimize.vo VOQC/extraction/voqc.ml
	cd VOQC/extraction && ./extract.sh
	dune build voqc.exe --root VOQC/extraction

voqc: VOQC/extraction/voqc.ml VOQC/extraction/_build/default/voqc.exe

VOQC/extraction/_build/default/voqc.exe:
	dune build voqc.exe --root VOQC/extraction

# Built by 'make examples'

SQIR/examples/Deutsch.vo: $(examples)/Deutsch.v $(SQIR)/UnitarySem.vo $(QWIRE)/Dirac.vo $(QWIRE)/Proportional.vo
	coqc $(COQ_OPTS) $(examples)/Deutsch.v

SQIR/examples/DeutschJozsa.vo: $(examples)/DeutschJozsa.v $(SQIR)/UnitarySem.vo $(QWIRE)/Dirac.vo
	coqc $(COQ_OPTS) $(examples)/DeutschJozsa.v

SQIR/examples/GHZ.vo: $(examples)/GHZ.v $(SQIR)/UnitarySem.vo $(QWIRE)/Dirac.vo
	coqc $(COQ_OPTS) $(examples)/GHZ.v

SQIR/examples/Superdense.vo: $(examples)/Teleport.v $(SQIR)/UnitarySem.vo $(QWIRE)/Dirac.vo
	coqc $(COQ_OPTS) $(examples)/Superdense.v

SQIR/examples/Teleport.vo: $(examples)/Teleport.v $(SQIR)/UnitarySem.vo $(SQIR)/DensitySem.vo $(SQIR)/NDSem.vo $(QWIRE)/Dirac.vo $(QWIRE)/Proportional.vo
	coqc $(COQ_OPTS) $(examples)/Teleport.v

# Built by 'make mapper'

VOQC/src/mapper/SimpleMapping.vo: $(SQIR)/UnitarySem.vo $(optimizer)/Equivalences.vo
	coqc $(COQ_OPTS) $(mapper)/SimpleMapping.v

VOQC/src/mapper/MappingExamples.vo: $(mapper)/SimpleMapping.vo
	coqc $(COQ_OPTS) $(mapper)/MappingExamples.v

# Built by 'make optimizer'

VOQC/src/optimizer/Equivalences.vo: $(optimizer)/Equivalences.v $(SQIR)/UnitarySem.vo
	coqc $(COQ_OPTS) $(optimizer)/Equivalences.v

VOQC/src/optimizer/GateCancellation.vo: $(optimizer)/GateCancellation.v $(optimizer)/Equivalences.vo $(optimizer)/PI4GateSet.vo
	coqc $(COQ_OPTS) $(optimizer)/GateCancellation.v

VOQC/src/optimizer/HadamardReduction.vo: $(optimizer)/HadamardReduction.v $(optimizer)/Equivalences.vo $(optimizer)/PI4GateSet.vo
	coqc $(COQ_OPTS) $(optimizer)/HadamardReduction.v

VOQC/src/optimizer/ListRepresentation.vo: $(optimizer)/ListRepresentation.v $(QWIRE)/Proportional.vo $(optimizer)/Equivalences.vo $(SQIR)/DensitySem.vo
	coqc $(COQ_OPTS) $(optimizer)/ListRepresentation.v

VOQC/src/optimizer/NotPropagation.vo: $(optimizer)/NotPropagation.v $(optimizer)/Equivalences.vo $(optimizer)/PI4GateSet.vo
	coqc $(COQ_OPTS) $(optimizer)/NotPropagation.v

VOQC/src/optimizer/Optimize.vo: $(optimizer)/Optimize.v $(optimizer)/NotPropagation.vo $(optimizer)/HadamardReduction.vo $(optimizer)/GateCancellation.vo $(optimizer)/RotationMerging.vo
	coqc $(COQ_OPTS) $(optimizer)/Optimize.v

VOQC/src/optimizer/PI4GateSet.vo: $(optimizer)/PI4GateSet.v $(optimizer)/Equivalences.vo $(optimizer)/ListRepresentation.vo $(SQIR)/DensitySem.vo
	coqc $(COQ_OPTS) $(optimizer)/PI4GateSet.v

VOQC/src/optimizer/RotationMerging.vo: $(optimizer)/RotationMerging.v $(optimizer)/PI4GateSet.vo $(SQIR)/ClassicalStates.vo
	coqc $(COQ_OPTS) $(optimizer)/RotationMerging.v

# Misc. files built by 'make all'

VOQC/src/optimizer/PropagateClassical.vo: $(optimizer)/PropagateClassical.v $(optimizer)/PI4GateSet.vo $(SQIR)/DensitySem.vo
	coqc $(COQ_OPTS) $(optimizer)/PropagateClassical.v

VOQC/src/optimizer/RemoveZRotationBeforeMeasure.vo: $(optimizer)/RemoveZRotationBeforeMeasure.v $(optimizer)/PI4GateSet.vo $(SQIR)/DensitySem.vo
	coqc $(COQ_OPTS) $(optimizer)/RemoveZRotationBeforeMeasure.v

VOQC/src/experimental/BooleanCompilation.vo: VOQC/src/experimental/BooleanCompilation.v $(SQIR)/ClassicalStates.vo $(QWIRE)/Dirac.vo
	coqc $(COQ_OPTS) VOQC/src/experimental/BooleanCompilation.v

# Using a custom clean target to remove files from subdirectories
clean:
	rm -rf CoqMakefile CoqMakefile.conf {externals/QWIRE,SQIR/*,VOQC/src/*}/{*.vo,*.glob,.*.aux} .lia.cache VOQC/extraction/_build

# This should be the last rule, to handle any targets not declared above
#%: invoke-coqmakefile
#	@true
