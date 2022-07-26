# Using the example from https://coq.inria.fr/refman/practical-tools/utilities.html#reusing-extending-the-generated-makefile

# KNOWNTARGETS will not be passed along to CoqMakefile
KNOWNTARGETS := CoqMakefile all examples voqc shor ghz clean

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

COQ_OPTS := -R SQIR Top.SQIR -R externals/euler Top.externals.euler -R examples Top.examples -R VOQC Top.VOQC

all: examples voqc shor VOQC/PropagateClassical.vo VOQC/RemoveZRotationBeforeMeasure.vo VOQC/BooleanCompilation.vo

examples: invoke-coqmakefile examples/Deutsch.vo examples/DeutschJozsa.vo examples/Grover.vo examples/QPE.vo examples/Simon.vo examples/Superdense.vo examples/Teleport.vo examples/Wiesner.vo ghz

ghz: invoke-coqmakefile examples/ghz/GHZ.vo examples/ghz/ExtrGHZ.vo

shor: invoke-coqmakefile examples/shor/Main.vo

voqc: invoke-coqmakefile VOQC/Main.vo

# Built by 'make examples'

examples/ghz/ExtrGHZ.vo: examples/ghz/ExtrGHZ.v examples/ghz/GHZ.vo SQIR/ExtractionGateSet.vo
	coqc $(COQ_OPTS) examples/ghz/ExtrGHZ.v

examples/Deutsch.vo: examples/Deutsch.v SQIR/UnitarySem.vo
	coqc $(COQ_OPTS) examples/Deutsch.v

examples/DeutschJozsa.vo: examples/DeutschJozsa.v SQIR/UnitaryOps.vo examples/Utilities.vo
	coqc $(COQ_OPTS) examples/DeutschJozsa.v

examples/ghz/GHZ.vo: examples/ghz/GHZ.v SQIR/UnitarySem.vo
	coqc $(COQ_OPTS) examples/ghz/GHZ.v

examples/Grover.vo: examples/Grover.v SQIR/UnitaryOps.vo examples/Utilities.vo
	coqc $(COQ_OPTS) examples/Grover.v

examples/QPE.vo: examples/QPE.v SQIR/UnitaryOps.vo examples/Utilities.vo
	coqc $(COQ_OPTS) examples/QPE.v

examples/Simon.vo: examples/Simon.v SQIR/UnitaryOps.vo examples/Utilities.vo
	coqc $(COQ_OPTS) examples/Simon.v

examples/Superdense.vo: examples/Superdense.v SQIR/UnitarySem.vo
	coqc $(COQ_OPTS) examples/Superdense.v

examples/Teleport.vo: examples/Teleport.v SQIR/UnitarySem.vo SQIR/DensitySem.vo SQIR/NDSem.vo
	coqc $(COQ_OPTS) examples/Teleport.v

examples/Utilities.vo: examples/Utilities.v
	coqc $(COQ_OPTS) examples/Utilities.v

examples/Wiesner.vo: examples/Wiesner.v SQIR/UnitaryOps.vo examples/Utilities.vo
	coqc $(COQ_OPTS) examples/Wiesner.v

# Built by 'make shor'

examples/shor/ExtrShor.vo: examples/shor/ExtrShor.v SQIR/ExtractionGateSet.vo examples/shor/Shor.vo
	coqc $(COQ_OPTS) examples/shor/ExtrShor.v

examples/shor/Main.vo: examples/shor/Main.v examples/shor/ExtrShor.vo
	coqc $(COQ_OPTS) examples/shor/Main.v

examples/shor/ModMult.vo: examples/shor/ModMult.v SQIR/UnitaryOps.vo examples/shor/RCIR.vo
	coqc $(COQ_OPTS) examples/shor/ModMult.v

examples/shor/QPEGeneral.vo: examples/shor/QPEGeneral.v examples/QPE.vo examples/Utilities.vo
	coqc $(COQ_OPTS) examples/shor/QPEGeneral.v

examples/shor/RCIR.vo: examples/shor/RCIR.v SQIR/UnitaryOps.vo
	coqc $(COQ_OPTS) examples/shor/RCIR.v

examples/shor/Shor.vo: examples/shor/Shor.v examples/shor/QPEGeneral.vo examples/shor/ModMult.vo examples/shor/ContFrac.vo examples/shor/Reduction.vo
	coqc $(COQ_OPTS) examples/shor/Shor.v

examples/shor/NumTheory.vo: examples/shor/NumTheory.v examples/Utilities.vo
	coqc $(COQ_OPTS) examples/shor/NumTheory.v

examples/shor/EulerTotient.vo: examples/shor/EulerTotient.v
	coqc $(COQ_OPTS) examples/shor/EulerTotient.v

examples/shor/ContFrac.vo: examples/shor/ContFrac.v
	coqc $(COQ_OPTS) examples/shor/ContFrac.v

examples/shor/Reduction.vo: examples/shor/Reduction.v examples/shor/EulerTotient.vo examples/Utilities.vo examples/shor/NumTheory.vo
	coqc $(COQ_OPTS) examples/shor/Reduction.v

# Built by 'make voqc'

VOQC/ChangeRotationBasis.vo: VOQC/ChangeRotationBasis.v
	coqc $(COQ_OPTS) VOQC/ChangeRotationBasis.v

VOQC/ConnectivityGraph.vo: VOQC/ConnectivityGraph.v VOQC/Layouts.vo
	coqc $(COQ_OPTS) VOQC/ConnectivityGraph.v

VOQC/GateCancellation.vo: VOQC/GateCancellation.v SQIR/Equivalences.vo VOQC/RzQGateSet.vo VOQC/MappingConstraints.vo
	coqc $(COQ_OPTS) VOQC/GateCancellation.v

VOQC/GateSet.vo: VOQC/GateSet.v SQIR/UnitarySem.vo
	coqc $(COQ_OPTS) VOQC/GateSet.v

VOQC/HadamardReduction.vo: VOQC/HadamardReduction.v SQIR/Equivalences.vo VOQC/RzQGateSet.vo VOQC/MappingConstraints.vo
	coqc $(COQ_OPTS) VOQC/HadamardReduction.v

VOQC/IBMGateSet.vo: VOQC/IBMGateSet.v VOQC/ChangeRotationBasis.vo VOQC/UnitaryListRepresentation.vo VOQC/NonUnitaryListRepresentation.vo
	coqc $(COQ_OPTS) VOQC/IBMGateSet.v

VOQC/UnitaryListRepresentation.vo: VOQC/UnitaryListRepresentation.v VOQC/GateSet.vo SQIR/Equivalences.vo
	coqc $(COQ_OPTS) VOQC/UnitaryListRepresentation.v

VOQC/Layouts.vo: VOQC/Layouts.v
	coqc $(COQ_OPTS) VOQC/Layouts.v

VOQC/MappingConstraints.vo: VOQC/MappingConstraints.v VOQC/UnitaryListRepresentation.vo
	coqc $(COQ_OPTS) VOQC/MappingConstraints.v

VOQC/NonUnitaryListRepresentation.vo: VOQC/NonUnitaryListRepresentation.v VOQC/UnitaryListRepresentation.vo SQIR/DensitySem.vo
	coqc $(COQ_OPTS) VOQC/NonUnitaryListRepresentation.v

VOQC/NotPropagation.vo: VOQC/NotPropagation.v SQIR/Equivalences.vo VOQC/RzQGateSet.vo VOQC/MappingConstraints.vo
	coqc $(COQ_OPTS) VOQC/NotPropagation.v

VOQC/Optimize1qGates.vo: VOQC/Optimize1qGates.v VOQC/IBMGateSet.vo VOQC/MappingConstraints.vo
	coqc $(COQ_OPTS) VOQC/Optimize1qGates.v

VOQC/RotationMerging.vo: VOQC/RotationMerging.v VOQC/RzQGateSet.vo SQIR/UnitaryOps.vo VOQC/MappingConstraints.vo
	coqc $(COQ_OPTS) VOQC/RotationMerging.v

VOQC/RzQGateSet.vo: VOQC/RzQGateSet.v VOQC/UnitaryListRepresentation.vo VOQC/NonUnitaryListRepresentation.vo
	coqc $(COQ_OPTS) VOQC/RzQGateSet.v

VOQC/SwapRoute.vo: VOQC/SwapRoute.v VOQC/ConnectivityGraph.vo VOQC/Layouts.vo VOQC/MappingConstraints.vo VOQC/FullGateSet.vo
	coqc $(COQ_OPTS) VOQC/SwapRoute.v

VOQC/FullGateSet.vo: VOQC/FullGateSet.v VOQC/IBMGateSet.vo VOQC/RzQGateSet.vo VOQC/MappingConstraints.vo VOQC/MappingGateSet.vo
	coqc $(COQ_OPTS) VOQC/FullGateSet.v

VOQC/Main.vo: VOQC/Main.v VOQC/GateCancellation.vo VOQC/HadamardReduction.vo VOQC/NotPropagation.vo VOQC/Optimize1qGates.vo VOQC/RotationMerging.vo VOQC/RzQGateSet.vo VOQC/SwapRoute.vo VOQC/MappingValidation.vo VOQC/GreedyLayout.vo
	coqc $(COQ_OPTS) VOQC/Main.v

VOQC/GreedyLayout.vo: VOQC/GreedyLayout.v VOQC/ConnectivityGraph.vo VOQC/Layouts.vo VOQC/MappingGateSet.vo
	coqc $(COQ_OPTS) VOQC/GreedyLayout.v

VOQC/MappingGateSet.vo: VOQC/MappingGateSet.v VOQC/UnitaryListRepresentation.vo
	coqc $(COQ_OPTS) VOQC/MappingGateSet.v

VOQC/MappingValidation.vo: VOQC/MappingValidation.v VOQC/SwapRoute.vo
	coqc $(COQ_OPTS) VOQC/MappingValidation.v

# Misc. files built by 'make all'

VOQC/PropagateClassical.vo: VOQC/PropagateClassical.v VOQC/RzQGateSet.vo SQIR/DensitySem.vo
	coqc $(COQ_OPTS) VOQC/PropagateClassical.v

VOQC/RemoveZRotationBeforeMeasure.vo: VOQC/RemoveZRotationBeforeMeasure.v VOQC/RzQGateSet.vo SQIR/DensitySem.vo
	coqc $(COQ_OPTS) VOQC/RemoveZRotationBeforeMeasure.v

VOQC/BooleanCompilation.vo: VOQC/BooleanCompilation.v
	coqc $(COQ_OPTS) VOQC/BooleanCompilation.v

# Using a custom clean target to remove files from subdirectories
clean:
	rm -rf CoqMakefile CoqMakefile.conf */*/*.vo* */*/*.glob */*/.*.aux */*.vo* */*.glob */.*.aux .lia.cache

# This should be the last rule, to handle any targets not declared above
%: invoke-coqmakefile
	@true
