all: Quantum.vo SQIMP.vo Denote_Ctrls.vo UnitarySem.vo

Prelim.vo: Prelim.v 
	coqc Prelim.v

Complex.vo: Complex.v Prelim.vo 
	coqc Complex.v

Matrix.vo: Matrix.v Complex.vo 
	coqc Matrix.v 

Quantum.vo: Quantum.v Matrix.vo
	coqc Quantum.v

SQIMP.vo : SQIMP.v
	coqc SQIMP.v

Denote_Ctrls.vo: Denote_Ctrls.v
	coqc Denote_Ctrls.v

UnitarySem.vo: UnitarySem.v Denote_Ctrls.vo
	coqc UnitarySem.v

clean:
	rm -f *.vo *.glob

