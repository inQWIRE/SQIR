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

examples: invoke-coqmakefile $(examples)/Deutsch.vo $(examples)/DeutschJozsa.vo $(examples)/GHZ.vo $(examples)/QPE.vo $(examples)/Simon.vo $(examples)/Superdense.vo $(examples)/Teleport.vo

mapper: invoke-coqmakefile $(VOQC)/SimpleMapping.vo $(VOQC)/MappingExamples.vo $(VOQC)/SimpleMappingWithLayout.vo

optimizer: invoke-coqmakefile $(VOQC)/Optimize.vo VOQC/voqc.ml
	cd VOQC/extraction && ./extract.sh
	dune build voqc.exe --root VOQC

voqc: VOQC/voqc.ml VOQC/_build/default/voqc.exe

VOQC/_build/default/voqc.exe:
	dune build voqc.exe --root VOQC

# Built by 'make examples'

SQIR/examples/Deutsch.vo: $(examples)/Deutsch.v $(SQIR)/UnitarySem.vo $(QWIRE)/Dirac.vo $(QWIRE)/Proportional.vo
	coqc $(COQ_OPTS) $(examples)/Deutsch.v

SQIR/examples/DeutschJozsa.vo: $(examples)/DeutschJozsa.v $(SQIR)/UnitaryOps.vo $(examples)/Utilities.vo $(QWIRE)/Dirac.vo
	coqc $(COQ_OPTS) $(examples)/DeutschJozsa.v

SQIR/examples/GHZ.vo: $(examples)/GHZ.v $(SQIR)/UnitarySem.vo $(QWIRE)/Dirac.vo
	coqc $(COQ_OPTS) $(examples)/GHZ.v

SQIR/examples/Grover.vo: $(examples)/Grover.v $(SQIR)/UnitaryOps.vo $(examples)/Utilities.vo $(QWIRE)/Dirac.vo
	coqc $(COQ_OPTS) $(examples)/Grover.v

SQIR/examples/QPE.vo: $(examples)/QPE.v $(SQIR)/UnitaryOps.vo
	coqc $(COQ_OPTS) $(examples)/QPE.v

SQIR/examples/QPEGeneral.vo: $(examples)/QPEGeneral.v $(examples)/QPE.vo $(examples)/Utilities.vo
	coqc $(COQ_OPTS) $(examples)/QPEGeneral.v

SQIR/examples/Shor.vo: $(examples)/Shor.v $(SQIR)/QPEGeneral.vo
	coqc $(COQ_OPTS) $(examples)/Shor.v

SQIR/examples/Simon.vo: $(examples)/Simon.v $(SQIR)/UnitaryOps.vo $(examples)/Utilities.vo
	coqc $(COQ_OPTS) $(examples)/Simon.v

SQIR/examples/Superdense.vo: $(examples)/Superdense.v $(SQIR)/UnitarySem.vo $(QWIRE)/Dirac.vo
	coqc $(COQ_OPTS) $(examples)/Superdense.v

SQIR/examples/Teleport.vo: $(examples)/Teleport.v $(SQIR)/UnitarySem.vo $(SQIR)/DensitySem.vo $(SQIR)/NDSem.vo $(QWIRE)/Dirac.vo $(QWIRE)/Proportional.vo
	coqc $(COQ_OPTS) $(examples)/Teleport.v

SQIR/examples/Utilities.vo: $(examples)/Utilities.v $(SQIR)/VectorStates.vo
	coqc $(COQ_OPTS) $(examples)/Utilities.v

# Built by 'make mapper'

VOQC/src/SimpleMapping.vo: $(VOQC)/SimpleMapping.v $(SQIR)/UnitarySem.vo $(SQIR)/Equivalences.vo
	coqc $(COQ_OPTS) $(VOQC)/SimpleMapping.v

VOQC/src/MappingExamples.vo: $(VOQC)/MappingExamples.v $(VOQC)/SimpleMapping.vo
	coqc $(COQ_OPTS) $(VOQC)/MappingExamples.v

VOQC/src/SimpleMappingWithLayout.vo: $(VOQC)/SimpleMappingWithLayout.v $(VOQC)/SimpleMapping.vo $(VOQC)/MappingExamples.vo 
	coqc $(COQ_OPTS) $(VOQC)/SimpleMappingWithLayout.v

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

VOQC/src/IBMGateSet.vo: $(VOQC)/IBMGateSet.v $(VOQC)/UnitaryListRepresentation.vo $(VOQC)/NonUnitaryListRepresentation.vo
	coqc $(COQ_OPTS) $(VOQC)/IBMGateSet.v

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
	rm -rf CoqMakefile CoqMakefile.conf */*/*.vo* */*/*.glob */*/*.aux .lia.cache VOQC/_build

# This should be the last rule, to handle any targets not declared above
#%: invoke-coqmakefile
#	@true
