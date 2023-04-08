(lang dune 2.8)
(name coq-sqir-voqc)
(version 1.1.0)
(using coq 0.2)

(generate_opam_files true)

(license MIT)
(authors "inQWIRE")
(maintainers "inQWIRE Developers")
(source (github inQWIRE/SQIR))

(package
 (name coq-sqir)
 (synopsis "Coq library for reasoning about quantum circuits")
 (description "\| inQWIRE's SQIR is a Coq library for reasoning
              "\|  about quantum circuits
 )
 (depends
   (coq-quantumlib (>= 1.1.0))
   (coq (>= 8.12))))

(package
 (name coq-voqc)
 (synopsis "A verified optimizer for quantum compilation")
 (description "\| inQWIRE's VOQC is a Coq library for verified
              "\|  optimization of quantum circuits
 )
 (depends
   (coq-quantumlib (>= 1.1.0))
   (coq-sqir (>= 1.1.0))
   (coq (>= 8.12))))
