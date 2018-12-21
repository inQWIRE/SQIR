all: Quantum.vo SQIMP.vo

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

clean:
	rm *.vo

