(lang dune 3.8)
(name coq-sqirvoqc)
(version 1.3.1)
(using coq 0.7)
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
   (coq-interval (>= 4.9.0))
   (coq-quantumlib (>= 1.7.0))
   (coq (>= 8.16))))

(package
 (name coq-voqc)
 (synopsis "A verified optimizer for quantum compilation")
 (description "\| inQWIRE's VOQC is a Coq library for verified
              "\|  optimization of quantum circuits
 )
 (depends
   (coq-interval (>= 4.9.0))
   (coq-quantumlib (>= 1.7.0))
   (coq-sqir (>= 1.3.0))
   (coq (>= 8.16))))
