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
VOQC := VOQC/src

COQ_OPTS := -R . Top

all: examples mapper optimizer $(VOQC)/PropagateClassical.vo $(VOQC)/RemoveZRotationBeforeMeasure.vo $(VOQC)/BooleanCompilation.vo

examples: invoke-coqmakefile $(examples)/Deutsch.vo $(examples)/DeutschJozsa.vo $(examples)/GHZ.vo $(examples)/Superdense.vo $(examples)/Teleport.vo $(examples)/QPE.vo

mapper: invoke-coqmakefile $(VOQC)/SimpleMapping.vo $(VOQC)/MappingExamples.vo

optimizer: invoke-coqmakefile $(VOQC)/Optimize.vo VOQC/extraction/voqc.ml
	cd VOQC/extraction && ./extract.sh
	dune build voqc.exe --root VOQC/extraction

voqc: VOQC/extraction/voqc.ml VOQC/extraction/_build/default/voqc.exe

VOQC/extraction/_build/default/voqc.exe:
	dune build voqc.exe --root VOQC/extraction

# Built by 'make examples'

SQIR/examples/Deutsch.vo: $(examples)/Deutsch.v $(SQIR)/UnitarySem.vo $(QWIRE)/Dirac.vo $(QWIRE)/Proportional.vo
	coqc $(COQ_OPTS) $(examples)/Deutsch.v

SQIR/examples/DeutschJozsa.vo: $(examples)/DeutschJozsa.v $(SQIR)/UnitaryOps.vo $(QWIRE)/Dirac.vo
	coqc $(COQ_OPTS) $(examples)/DeutschJozsa.v

SQIR/examples/GHZ.vo: $(examples)/GHZ.v $(SQIR)/UnitarySem.vo $(QWIRE)/Dirac.vo
	coqc $(COQ_OPTS) $(examples)/GHZ.v

SQIR/examples/Superdense.vo: $(examples)/Teleport.v $(SQIR)/UnitarySem.vo $(QWIRE)/Dirac.vo
	coqc $(COQ_OPTS) $(examples)/Superdense.v

SQIR/examples/Teleport.vo: $(examples)/Teleport.v $(SQIR)/UnitarySem.vo $(SQIR)/DensitySem.vo $(SQIR)/NDSem.vo $(QWIRE)/Dirac.vo $(QWIRE)/Proportional.vo
	coqc $(COQ_OPTS) $(examples)/Teleport.v
	
SQIR/examples/QPE.vo: $(examples)/QPE.v $(SQIR)/UnitaryOps.vo
	coqc $(COQ_OPTS) $(examples)/QPE.v

# Built by 'make mapper'

VOQC/src/SimpleMapping.vo: $(VOQC)/SimpleMapping.v $(SQIR)/UnitarySem.vo $(SQIR)/Equivalences.vo
	coqc $(COQ_OPTS) $(VOQC)/SimpleMapping.v

VOQC/src/MappingExamples.vo: $(VOQC)/SimpleMapping.vo
	coqc $(COQ_OPTS) $(VOQC)/MappingExamples.v

# Built by 'make optimizer'

VOQC/src/GateCancellation.vo: $(VOQC)/GateCancellation.v $(SQIR)/Equivalences.vo $(VOQC)/RzQGateSet.vo
	coqc $(COQ_OPTS) $(VOQC)/GateCancellation.v

VOQC/src/GateSet.vo: $(VOQC)/GateSet.v $(SQIR)/UnitarySem.vo
	coqc $(COQ_OPTS) $(VOQC)/GateSet.v

VOQC/src/HadamardReduction.vo: $(VOQC)/HadamardReduction.v $(SQIR)/Equivalences.vo $(VOQC)/RzQGateSet.vo
	coqc $(COQ_OPTS) $(VOQC)/HadamardReduction.v

VOQC/src/UnitaryListRepresentation.vo: $(VOQC)/UnitaryListRepresentation.v $(VOQC)/GateSet.vo $(QWIRE)/Proportional.vo $(SQIR)/Equivalences.vo
	coqc $(COQ_OPTS) $(VOQC)/UnitaryListRepresentation.v
	
VOQC/src/NonUnitaryListRepresentation.vo: $(VOQC)/NonUnitaryListRepresentation.v $(VOQC)/UnitaryListRepresentation.vo $(SQIR)/DensitySem.vo
	coqc $(COQ_OPTS) $(VOQC)/NonUnitaryListRepresentation.v

VOQC/src/NotPropagation.vo: $(VOQC)/NotPropagation.v $(SQIR)/Equivalences.vo $(VOQC)/RzQGateSet.vo
	coqc $(COQ_OPTS) $(VOQC)/NotPropagation.v

VOQC/src/Optimize.vo: $(VOQC)/Optimize.v $(VOQC)/NotPropagation.vo $(VOQC)/HadamardReduction.vo $(VOQC)/GateCancellation.vo $(VOQC)/RotationMerging.vo
	coqc $(COQ_OPTS) $(VOQC)/Optimize.v

VOQC/src/RzQGateSet.vo: $(VOQC)/RzQGateSet.v $(VOQC)/UnitaryListRepresentation.vo $(VOQC)/NonUnitaryListRepresentation.vo
	coqc $(COQ_OPTS) $(VOQC)/RzQGateSet.v

VOQC/src/RotationMerging.vo: $(VOQC)/RotationMerging.v $(VOQC)/RzQGateSet.vo $(SQIR)/UnitaryOps.vo
	coqc $(COQ_OPTS) $(VOQC)/RotationMerging.v

# Misc. files built by 'make all'

VOQC/src/PropagateClassical.vo: $(VOQC)/PropagateClassical.v $(VOQC)/RzQGateSet.vo $(SQIR)/DensitySem.vo
	coqc $(COQ_OPTS) $(VOQC)/PropagateClassical.v

VOQC/src/RemoveZRotationBeforeMeasure.vo: $(VOQC)/RemoveZRotationBeforeMeasure.v $(VOQC)/RzQGateSet.vo $(SQIR)/DensitySem.vo
	coqc $(COQ_OPTS) $(VOQC)/RemoveZRotationBeforeMeasure.v

VOQC/src/BooleanCompilation.vo: $(VOQC)/BooleanCompilation.v $(SQIR)/VectorStates.vo $(QWIRE)/Dirac.vo
	coqc $(COQ_OPTS) $(VOQC)/BooleanCompilation.v

# Using a custom clean target to remove files from subdirectories
clean:
	rm -rf CoqMakefile CoqMakefile.conf {externals/QWIRE,SQIR/*,VOQC/src}/{*.vo,*.glob,.*.aux} .lia.cache VOQC/extraction/_build

# This should be the last rule, to handle any targets not declared above
#%: invoke-coqmakefile
#	@true
