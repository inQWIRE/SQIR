# Using the example from https://coq.inria.fr/refman/practical-tools/utilities.html#reusing-extending-the-generated-makefile

# KNOWNTARGETS will not be passed along to CoqMakefile
KNOWNTARGETS := CoqMakefile all examples voqc shor clean

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

invoke-coqmakefile-euler: _CoqProjectEuler
	$(COQBIN)coq_makefile -f _CoqProjectEuler -o CoqMakefileEuler
	$(MAKE) --no-print-directory -f CoqMakefileEuler $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))

.PHONY: invoke-coqmakefile $(KNOWNFILES)

###########################################################
##		      Your targets here			 ##
###########################################################

QWIRE := externals/QWIRE
SQIR := SQIR
examples := examples
VOQC := VOQC

COQ_OPTS := -R . Top

all: examples voqc $(VOQC)/PropagateClassical.vo $(VOQC)/RemoveZRotationBeforeMeasure.vo $(VOQC)/BooleanCompilation.vo shor

examples: invoke-coqmakefile $(examples)/Deutsch.vo $(examples)/DeutschJozsa.vo $(examples)/GHZ.vo $(examples)/Grover.vo $(examples)/QPE.vo $(examples)/Simon.vo $(examples)/Superdense.vo $(examples)/Teleport.vo $(examples)/Wiesner.vo

shor: invoke-coqmakefile invoke-coqmakefile-euler $(examples)/shor/AltShor.vo

voqc: invoke-coqmakefile $(VOQC)/Main.vo

# Built by 'make examples'

examples/Deutsch.vo: $(examples)/Deutsch.v $(SQIR)/UnitarySem.vo $(QWIRE)/Dirac.vo $(QWIRE)/Proportional.vo
	coqc $(COQ_OPTS) $(examples)/Deutsch.v

examples/DeutschJozsa.vo: $(examples)/DeutschJozsa.v $(SQIR)/UnitaryOps.vo $(examples)/Utilities.vo $(QWIRE)/Dirac.vo
	coqc $(COQ_OPTS) $(examples)/DeutschJozsa.v

examples/GHZ.vo: $(examples)/GHZ.v $(SQIR)/UnitarySem.vo $(QWIRE)/Dirac.vo
	coqc $(COQ_OPTS) $(examples)/GHZ.v

examples/Grover.vo: $(examples)/Grover.v $(SQIR)/UnitaryOps.vo $(examples)/Utilities.vo $(QWIRE)/Dirac.vo
	coqc $(COQ_OPTS) $(examples)/Grover.v

examples/QPE.vo: $(examples)/QPE.v $(SQIR)/UnitaryOps.vo
	coqc $(COQ_OPTS) $(examples)/QPE.v

examples/Simon.vo: $(examples)/Simon.v $(SQIR)/UnitaryOps.vo $(examples)/Utilities.vo
	coqc $(COQ_OPTS) $(examples)/Simon.v

examples/Superdense.vo: $(examples)/Superdense.v $(SQIR)/UnitarySem.vo $(QWIRE)/Dirac.vo
	coqc $(COQ_OPTS) $(examples)/Superdense.v

examples/Teleport.vo: $(examples)/Teleport.v $(SQIR)/UnitarySem.vo $(SQIR)/DensitySem.vo $(SQIR)/NDSem.vo $(QWIRE)/Dirac.vo $(QWIRE)/Proportional.vo
	coqc $(COQ_OPTS) $(examples)/Teleport.v

examples/Utilities.vo: $(examples)/Utilities.v $(SQIR)/VectorStates.vo
	coqc $(COQ_OPTS) $(examples)/Utilities.v

examples/Wiesner.vo: $(examples)/Wiesner.v $(SQIR)/UnitaryOps.vo $(examples)/Utilities.vo $(QWIRE)/Dirac.vo
	coqc $(COQ_OPTS) $(examples)/Wiesner.v

# Built by 'make shor'

examples/shor/AltGateSet.vo: $(examples)/shor/AltGateSet.v $(SQIR)/UnitaryOps.vo $(SQIR)/RCIR.vo
	coqc $(COQ_OPTS) $(examples)/shor/AltGateSet.v
	
examples/shor/AltShor.vo: $(examples)/shor/AltShor.v $(examples)/shor/AltGateSet.vo $(examples)/shor/Shor.vo
	coqc $(COQ_OPTS) $(examples)/shor/AltShor.v

examples/shor/ModMult.vo: $(examples)/shor/ModMult.v $(SQIR)/UnitaryOps.vo $(SQIR)/VectorStates.vo $(SQIR)/RCIR.vo
	coqc $(COQ_OPTS) $(examples)/shor/ModMult.v

examples/shor/QPEGeneral.vo: $(examples)/shor/QPEGeneral.v $(examples)/QPE.vo $(examples)/Utilities.vo
	coqc $(COQ_OPTS) $(examples)/shor/QPEGeneral.v

examples/shor/Shor.vo: $(examples)/shor/Shor.v $(examples)/shor/QPEGeneral.vo $(examples)/shor/ModMult.vo $(examples)/shor/ShorAux.vo
	coqc $(COQ_OPTS) $(examples)/shor/Shor.v
	
examples/shor/ShorAux.vo: $(examples)/shor/ShorAux.v $(examples)/Utilities.vo
	coqc $(COQ_OPTS) $(examples)/shor/ShorAux.v

# Built by 'make voqc'

VOQC/ChangeRotationBasis.vo: $(VOQC)/ChangeRotationBasis.v
	coqc $(COQ_OPTS) $(VOQC)/ChangeRotationBasis.v

VOQC/ConnectivityGraph.vo: $(VOQC)/ConnectivityGraph.v
	coqc $(COQ_OPTS) $(VOQC)/ConnectivityGraph.v

VOQC/CXCancellation.vo: $(VOQC)/CXCancellation.v $(VOQC)/IBMGateSet.vo $(VOQC)/MappingConstraints.vo
	coqc $(COQ_OPTS) $(VOQC)/CXCancellation.v

VOQC/GateCancellation.vo: $(VOQC)/GateCancellation.v $(SQIR)/Equivalences.vo $(VOQC)/RzQGateSet.vo $(VOQC)/MappingConstraints.vo
	coqc $(COQ_OPTS) $(VOQC)/GateCancellation.v

VOQC/GateSet.vo: $(VOQC)/GateSet.v $(SQIR)/UnitarySem.vo
	coqc $(COQ_OPTS) $(VOQC)/GateSet.v

VOQC/HadamardReduction.vo: $(VOQC)/HadamardReduction.v $(SQIR)/Equivalences.vo $(VOQC)/RzQGateSet.vo $(VOQC)/MappingConstraints.vo
	coqc $(COQ_OPTS) $(VOQC)/HadamardReduction.v

VOQC/IBMGateSet.vo: $(VOQC)/IBMGateSet.v $(VOQC)/ChangeRotationBasis.vo $(VOQC)/UnitaryListRepresentation.vo $(VOQC)/NonUnitaryListRepresentation.vo
	coqc $(COQ_OPTS) $(VOQC)/IBMGateSet.v

VOQC/UnitaryListRepresentation.vo: $(VOQC)/UnitaryListRepresentation.v $(VOQC)/GateSet.vo $(QWIRE)/Proportional.vo $(SQIR)/Equivalences.vo
	coqc $(COQ_OPTS) $(VOQC)/UnitaryListRepresentation.v

VOQC/Layouts.vo: $(VOQC)/Layouts.v $(SQIR)/VectorStates.vo
	coqc $(COQ_OPTS) $(VOQC)/Layouts.v

VOQC/MappingConstraints.vo: $(VOQC)/MappingConstraints.v $(VOQC)/UnitaryListRepresentation.vo
	coqc $(COQ_OPTS) $(VOQC)/MappingConstraints.v

VOQC/NonUnitaryListRepresentation.vo: $(VOQC)/NonUnitaryListRepresentation.v $(VOQC)/UnitaryListRepresentation.vo $(SQIR)/DensitySem.vo
	coqc $(COQ_OPTS) $(VOQC)/NonUnitaryListRepresentation.v

VOQC/NotPropagation.vo: $(VOQC)/NotPropagation.v $(SQIR)/Equivalences.vo $(VOQC)/RzQGateSet.vo $(VOQC)/MappingConstraints.vo
	coqc $(COQ_OPTS) $(VOQC)/NotPropagation.v

VOQC/Optimize1qGates.vo: $(VOQC)/Optimize1qGates.v $(VOQC)/IBMGateSet.vo $(VOQC)/MappingConstraints.vo
	coqc $(COQ_OPTS) $(VOQC)/Optimize1qGates.v

VOQC/RotationMerging.vo: $(VOQC)/RotationMerging.v $(VOQC)/RzQGateSet.vo $(SQIR)/UnitaryOps.vo $(VOQC)/MappingConstraints.vo
	coqc $(COQ_OPTS) $(VOQC)/RotationMerging.v
	
VOQC/RzQGateSet.vo: $(VOQC)/RzQGateSet.v $(VOQC)/UnitaryListRepresentation.vo $(VOQC)/NonUnitaryListRepresentation.vo
	coqc $(COQ_OPTS) $(VOQC)/RzQGateSet.v

VOQC/SimpleMapping.vo: $(VOQC)/SimpleMapping.v $(VOQC)/ConnectivityGraph.vo $(VOQC)/Layouts.vo $(VOQC)/MappingConstraints.vo $(VOQC)/StandardGateSet.vo
	coqc $(COQ_OPTS) $(VOQC)/SimpleMapping.v

VOQC/StandardGateSet.vo: $(VOQC)/StandardGateSet.v $(VOQC)/IBMGateSet.vo $(VOQC)/RzQGateSet.vo $(VOQC)/MappingConstraints.vo
	coqc $(COQ_OPTS) $(VOQC)/StandardGateSet.v

VOQC/Main.vo: $(VOQC)/Main.v $(VOQC)/CXCancellation.vo $(VOQC)/GateCancellation.vo $(VOQC)/HadamardReduction.vo $(VOQC)/NotPropagation.vo $(VOQC)/Optimize1qGates.vo $(VOQC)/RotationMerging.vo $(VOQC)/RzQGateSet.vo $(VOQC)/SimpleMapping.vo $(VOQC)/StandardGateSet.vo
	coqc $(COQ_OPTS) $(VOQC)/Main.v

# Misc. files built by 'make all'

VOQC/PropagateClassical.vo: $(VOQC)/PropagateClassical.v $(VOQC)/RzQGateSet.vo $(SQIR)/DensitySem.vo
	coqc $(COQ_OPTS) $(VOQC)/PropagateClassical.v

VOQC/RemoveZRotationBeforeMeasure.vo: $(VOQC)/RemoveZRotationBeforeMeasure.v $(VOQC)/RzQGateSet.vo $(SQIR)/DensitySem.vo
	coqc $(COQ_OPTS) $(VOQC)/RemoveZRotationBeforeMeasure.v

VOQC/BooleanCompilation.vo: $(VOQC)/BooleanCompilation.v $(SQIR)/VectorStates.vo $(QWIRE)/Dirac.vo
	coqc $(COQ_OPTS) $(VOQC)/BooleanCompilation.v

# Using a custom clean target to remove files from subdirectories
clean:
	rm -rf CoqMakefile CoqMakefile.conf */*/*.vo* */*/*.glob */*/*.aux */*.vo* */*.glob */*.aux .lia.cache

# This should be the last rule, to handle any targets not declared above
#%: invoke-coqmakefile
#	@true
