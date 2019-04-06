core: NDSem.vo DensitySem.vo 

all: GHZ.vo Transformations.vo Deutsch.vo Superdense.vo Teleport.vo 

Prelim.vo: Prelim.v 
	coqc Prelim.v

Complex.vo: Complex.v Prelim.vo 
	coqc Complex.v

Matrix.vo: Matrix.v Complex.vo 
	coqc Matrix.v 

Quantum.vo: Quantum.v Matrix.vo
	coqc Quantum.v

Dirac.vo: Dirac.v Quantum.vo 
	coqc Dirac.v

SQIMP.vo : SQIMP.v
	coqc SQIMP.v

UnitarySem.vo: UnitarySem.v SQIMP.vo Quantum.vo
	coqc UnitarySem.v

DensitySem.vo: DensitySem.v UnitarySem.vo
	coqc DensitySem.v

NDSem.vo: NDSem.v UnitarySem.vo
	coqc NDSem.v

# Examples

GHZ.vo : GHZ.v UnitarySem.vo Dirac.vo
	coqc GHZ.v

Transformations.vo : Transformations.v UnitarySem.vo
	coqc Transformations.v

Superdense.vo : Superdense.v UnitarySem.vo
	coqc Superdense.v

Deutsch.vo : Deutsch.v UnitarySem.vo
	coqc Deutsch.v

Teleport.vo: Teleport.v DensitySem.vo NDSem.vo Dirac.vo
	coqc Teleport.v

clean:
	rm -f *.vo *.glob

