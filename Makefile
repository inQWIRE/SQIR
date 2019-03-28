all: UnitarySem.vo Dirac.vo

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

clean:
	rm -f *.vo *.glob

