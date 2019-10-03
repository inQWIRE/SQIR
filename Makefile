# Using the example from https://coq.inria.fr/refman/practical-tools/utilities.html#reusing-extending-the-generated-makefile

# KNOWNTARGETS will not be passed along to CoqMakefile
KNOWNTARGETS := CoqMakefile all examples mapper optimizer clean

# KNOWNFILES will not get implicit targets from the final rule, and so
# depending on them won't invoke the submake
# Warning: These files get declared as PHONY, so any targets depending
# on them always get rebuilt
KNOWNFILES   := Makefile _CoqProject

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

COQ_OPTS := -R . Top

all: examples mapper optimizer hll-compiler/BooleanCompilation.vo
examples: invoke-coqmakefile examples/Deutsch.vo examples/DeutschJozsa.vo examples/GHZ.vo examples/Superdense.vo examples/Teleport.vo
mapper: invoke-coqmakefile mapper/SimpleMapping.vo mapper/MappingExamples.vo
optimizer: invoke-coqmakefile optimizer/Equivalences.vo optimizer/GateCancellation.vo optimizer/HadamardReduction.vo optimizer/ListRepresentation.vo optimizer/NotPropagation.vo optimizer/PI4GateSet.vo optimizer/PropagateClassical.vo optimizer/RemoveZRotationBeforeMeasure.vo optimizer/RotationMerging.vo optimizer/SkipElimination.vo

# Built by 'make examples'

examples/Deutsch.vo: examples/Deutsch.v core/UnitarySem.vo lib/QWIRE/Dirac.vo lib/QWIRE/Proportional.vo
	coqc $(COQ_OPTS) examples/Deutsch.v

examples/DeutschJozsa.vo: examples/DeutschJozsa.v core/UnitarySem.vo lib/QWIRE/Dirac.vo
	coqc $(COQ_OPTS) examples/DeutschJozsa.v

examples/GHZ.vo: examples/GHZ.v core/UnitarySem.vo lib/QWIRE/Dirac.vo
	coqc $(COQ_OPTS) examples/GHZ.v

examples/Superdense.vo: examples/Teleport.v core/UnitarySem.vo lib/QWIRE/Dirac.vo
	coqc $(COQ_OPTS) examples/Superdense.v

examples/Teleport.vo: examples/Teleport.v core/UnitarySem.vo core/DensitySem.vo core/NDSem.vo lib/QWIRE/Dirac.vo lib/QWIRE/Proportional.vo
	coqc $(COQ_OPTS) examples/Teleport.v

# Built by 'make mapper'

mapper/SimpleMapping.vo: core/UnitarySem.vo optimizer/Equivalences.vo
	coqc $(COQ_OPTS) mapper/SimpleMapping.v

mapper/MappingExamples.vo: mapper/SimpleMapping.vo
	coqc $(COQ_OPTS) mapper/MappingExamples.v

# Built by 'make optimizer'

optimizer/Equivalences.vo: optimizer/Equivalences.v core/UnitarySem.vo
	coqc $(COQ_OPTS) optimizer/Equivalences.v

optimizer/GateCancellation.vo: optimizer/GateCancellation.v optimizer/Equivalences.vo optimizer/PI4GateSet.vo
	coqc $(COQ_OPTS) optimizer/GateCancellation.v

optimizer/HadamardReduction.vo: optimizer/HadamardReduction.v optimizer/Equivalences.vo optimizer/PI4GateSet.vo
	coqc $(COQ_OPTS) optimizer/HadamardReduction.v

optimizer/ListRepresentation.vo: optimizer/ListRepresentation.v lib/QWIRE/Proportional.vo optimizer/Equivalences.vo core/DensitySem.vo
	coqc $(COQ_OPTS) optimizer/ListRepresentation.v

optimizer/NotPropagation.vo: optimizer/NotPropagation.v optimizer/Equivalences.vo optimizer/PI4GateSet.vo
	coqc $(COQ_OPTS) optimizer/NotPropagation.v

optimizer/PI4GateSet.vo: optimizer/PI4GateSet.v optimizer/Equivalences.vo optimizer/ListRepresentation.vo core/DensitySem.vo
	coqc $(COQ_OPTS) optimizer/PI4GateSet.v

optimizer/PropagateClassical.vo: optimizer/PropagateClassical.v optimizer/PI4GateSet.vo core/DensitySem.vo
	coqc $(COQ_OPTS) optimizer/PropagateClassical.v
	
optimizer/RemoveZRotationBeforeMeasure.vo: optimizer/RemoveZRotationBeforeMeasure.v optimizer/PI4GateSet.vo core/DensitySem.vo
	coqc $(COQ_OPTS) optimizer/RemoveZRotationBeforeMeasure.v

optimizer/RotationMerging.vo: optimizer/RotationMerging.v optimizer/PI4GateSet.vo core/Utilities.vo
	coqc $(COQ_OPTS) optimizer/RotationMerging.v

optimizer/SkipElimination.vo: optimizer/SkipElimination.v optimizer/Equivalences.vo
	coqc $(COQ_OPTS) optimizer/SkipElimination.v

# Misc. files built by 'make all'

hll-compiler/BooleanCompilation.vo: hll-compiler/BooleanCompilation.v core/Utilities.vo lib/QWIRE/Dirac.vo
	coqc $(COQ_OPTS) hll-compiler/BooleanCompilation.v

# Using a custom clean target to remove files from subdirectories
clean:
	rm -f CoqMakefile CoqMakefile.conf lib/QWIRE/*.vo lib/QWIRE/*.glob core/*.vo core/*.glob examples/*.vo examples/*.glob mapper/*.vo mapper/*.glob optimizer/*.vo optimizer/*.glob 

# This should be the last rule, to handle any targets not declared above
%: invoke-coqmakefile
	@true
