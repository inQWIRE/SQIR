# Using the example from https://coq.inria.fr/refman/practical-tools/utilities.html#reusing-extending-the-generated-makefile

# KNOWNTARGETS will not be passed along to CoqMakefile
KNOWNTARGETS := CoqMakefile all examples mapper optimizer voqc qasm clean

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

COQ_OPTS := -R . Top

all: examples mapper optimizer optimizer/PropagateClassical.vo optimizer/RemoveZRotationBeforeMeasure.vo qasm experimental/BooleanCompilation.vo

examples: invoke-coqmakefile examples/Deutsch.vo examples/DeutschJozsa.vo examples/GHZ.vo examples/Superdense.vo examples/Teleport.vo

mapper: invoke-coqmakefile mapper/SimpleMapping.vo mapper/MappingExamples.vo

qasm: invoke-coqmakefile qasm_to_sqir/Sets.vo qasm_to_sqir/Map.vo qasm_to_sqir/qasm.vo

optimizer: invoke-coqmakefile optimizer/Optimize.vo VOQC/voqc.ml
	cd VOQC && ./extract.sh
	dune build voqc.exe --root VOQC

voqc: VOQC/voqc.ml VOQC/_build/default/voqc.exe

VOQC/_build/default/voqc.exe:
	dune build voqc.exe --root VOQC

# Built by 'make examples'

examples/Deutsch.vo: examples/Deutsch.v SQIR/UnitarySem.vo externals/QWIRE/Dirac.vo externals/QWIRE/Proportional.vo
	coqc $(COQ_OPTS) examples/Deutsch.v

examples/DeutschJozsa.vo: examples/DeutschJozsa.v SQIR/UnitarySem.vo externals/QWIRE/Dirac.vo
	coqc $(COQ_OPTS) examples/DeutschJozsa.v

examples/GHZ.vo: examples/GHZ.v SQIR/UnitarySem.vo externals/QWIRE/Dirac.vo
	coqc $(COQ_OPTS) examples/GHZ.v

examples/Superdense.vo: examples/Teleport.v SQIR/UnitarySem.vo externals/QWIRE/Dirac.vo
	coqc $(COQ_OPTS) examples/Superdense.v

examples/Teleport.vo: examples/Teleport.v SQIR/UnitarySem.vo SQIR/DensitySem.vo SQIR/NDSem.vo externals/QWIRE/Dirac.vo externals/QWIRE/Proportional.vo
	coqc $(COQ_OPTS) examples/Teleport.v

# Built by 'make mapper'

mapper/SimpleMapping.vo: SQIR/UnitarySem.vo optimizer/Equivalences.vo
	coqc $(COQ_OPTS) mapper/SimpleMapping.v

mapper/MappingExamples.vo: mapper/SimpleMapping.vo
	coqc $(COQ_OPTS) mapper/MappingExamples.v

# Built by 'make optimizer'

optimizer/Equivalences.vo: optimizer/Equivalences.v SQIR/UnitarySem.vo
	coqc $(COQ_OPTS) optimizer/Equivalences.v

optimizer/GateCancellation.vo: optimizer/GateCancellation.v optimizer/Equivalences.vo optimizer/PI4GateSet.vo
	coqc $(COQ_OPTS) optimizer/GateCancellation.v

optimizer/HadamardReduction.vo: optimizer/HadamardReduction.v optimizer/Equivalences.vo optimizer/PI4GateSet.vo
	coqc $(COQ_OPTS) optimizer/HadamardReduction.v

optimizer/ListRepresentation.vo: optimizer/ListRepresentation.v externals/QWIRE/Proportional.vo optimizer/Equivalences.vo SQIR/DensitySem.vo
	coqc $(COQ_OPTS) optimizer/ListRepresentation.v

optimizer/NotPropagation.vo: optimizer/NotPropagation.v optimizer/Equivalences.vo optimizer/PI4GateSet.vo
	coqc $(COQ_OPTS) optimizer/NotPropagation.v

optimizer/Optimize.vo: optimizer/Optimize.v optimizer/NotPropagation.vo optimizer/HadamardReduction.vo optimizer/GateCancellation.vo optimizer/RotationMerging.vo
	coqc $(COQ_OPTS) optimizer/Optimize.v

optimizer/PI4GateSet.vo: optimizer/PI4GateSet.v optimizer/Equivalences.vo optimizer/ListRepresentation.vo SQIR/DensitySem.vo
	coqc $(COQ_OPTS) optimizer/PI4GateSet.v

optimizer/RotationMerging.vo: optimizer/RotationMerging.v optimizer/PI4GateSet.vo SQIR/Utilities.vo
	coqc $(COQ_OPTS) optimizer/RotationMerging.v

# Built by 'make qasm'

qasm_to_sqir/Sets.vo: qasm_to_sqir/Sets.v
	coqc $(COQ_OPTS) qasm_to_sqir/Sets.v

qasm_to_sqir/Map.vo: qasm_to_sqir/Map.v qasm_to_sqir/Sets.vo
	coqc $(COQ_OPTS) qasm_to_sqir/Map.v

qasm_to_sqir/qasm.vo: qasm_to_sqir/qasm.v qasm_to_sqir/Map.vo externals/QWIRE/Quantum.vo
	coqc $(COQ_OPTS) qasm_to_sqir/qasm.v

# Misc. files built by 'make all'

optimizer/PropagateClassical.vo: optimizer/PropagateClassical.v optimizer/PI4GateSet.vo SQIR/DensitySem.vo
	coqc $(COQ_OPTS) optimizer/PropagateClassical.v

optimizer/RemoveZRotationBeforeMeasure.vo: optimizer/RemoveZRotationBeforeMeasure.v optimizer/PI4GateSet.vo SQIR/DensitySem.vo
	coqc $(COQ_OPTS) optimizer/RemoveZRotationBeforeMeasure.v

experimental/BooleanCompilation.vo: experimental/BooleanCompilation.v SQIR/Utilities.vo externals/QWIRE/Dirac.vo
	coqc $(COQ_OPTS) experimental/BooleanCompilation.v

# Using a custom clean target to remove files from subdirectories
clean:
	rm -rf CoqMakefile CoqMakefile.conf externals/QWIRE/*.vo externals/QWIRE/*.glob SQIR/*.vo SQIR/*.glob examples/*.vo examples/*.glob mapper/*.vo mapper/*.glob optimizer/*.vo optimizer/*.glob VOQC/_build experimental/*.vo experimental/*.glob qasm_to_sqir/*.vo qasm_to_sqir/*.glob

# This should be the last rule, to handle any targets not declared above
#%: invoke-coqmakefile
#	@true
