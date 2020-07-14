BUILDDIR=_build
VPATH=$(BUILDDIR)
OCAMLDIR=$(shell ocamlopt -where)
$(shell mkdir -p $(BUILDDIR) $(BUILDDIR)/stub $(BUILDDIR)/stub_generator $(BUILDDIR)/generated)
PACKAGES=ctypes.stubs,ctypes.foreign,openQASM,zarith,ppx_deriving,ppx_deriving.enum,ctypes-zarith
CTYPES=$(shell ocamlfind query ctypes)
OCAMLDEP=ocamldep



BINDING_FILES=$(BUILDDIR)/FSetAVL.cmx      \
               $(BUILDDIR)/FMapAVL.cmx      \
               $(BUILDDIR)/Datatypes.cmx      \
               $(BUILDDIR)/OrderedTypeEx.cmx      \
               $(BUILDDIR)/UnitaryListRepresentation.cmx           \
               $(BUILDDIR)/RzQGateSet.cmx      \
               $(BUILDDIR)/qasm2sqir.cmx			\
               $(BUILDDIR)/GateCancellation.cmx      \
               $(BUILDDIR)/HadamardReduction.cmx      \
               $(BUILDDIR)/RotationMerging.cmx      \
               $(BUILDDIR)/NotPropagation.cmx      \
               $(BUILDDIR)/Optimize.cmx      

GENERATOR_FILES= $(BINDING_FILES) \
		 $(BUILDDIR)/bindings.cmx		\
		 $(BUILDDIR)/stub_generator/generate.cmx




LIBFILES=$(BUILDDIR)/FSetAVL.cmx      \
         $(BUILDDIR)/FMapAVL.cmx      \
         $(BUILDDIR)/Datatypes.cmx      \
         $(BUILDDIR)/OrderedTypeEx.cmx      \
         $(BUILDDIR)/UnitaryListRepresentation.cmx           \
         $(BUILDDIR)/RzQGateSet.cmx      \
         $(BUILDDIR)/qasm2sqir.cmx			\
         $(BUILDDIR)/GateCancellation.cmx      \
         $(BUILDDIR)/HadamardReduction.cmx      \
         $(BUILDDIR)/RotationMerging.cmx      \
         $(BUILDDIR)/NotPropagation.cmx      \
         $(BUILDDIR)/Optimize.cmx      \
         $(BUILDDIR)/bindings.cmx			\
	 $(BUILDDIR)/generated/voqc_bindings.cmx		\
         $(BUILDDIR)/apply_bindings.cmx		\
         $(BUILDDIR)/generated/voqc.o

CAML_INIT=$(BUILDDIR)/stub/init.o

GENERATED=$(BUILDDIR)/generated/voqc.h \
          $(BUILDDIR)/generated/voqc.c \
          $(BUILDDIR)/generated/voqc_bindings.ml


OSTYPE:=$(shell ocamlfind ocamlc -config | awk '/^os_type:/ {print $$2}')
SYSTEM:=$(shell ocamlfind ocamlc -config | awk '/^system:/ {print $$2}')
EXTDLL:=$(shell ocamlfind ocamlc -config | awk '/^ext_dll:/ {print $$2}')
CC:= $(shell ocamlfind ocamlc -config | awk '/^bytecomp_c_compiler/ {for(i=2;i<=NF;i++) printf "%s " ,$$i}')

ifeq ($(OSTYPE), $(filter $(OSTYPE), Win32 Cygwin))
EXTEXE=.exe
else 
EXTEXE=
endif

GENERATOR=$(BUILDDIR)/generate$(EXTEXE)

all: sharedlib

sharedlib: $(BUILDDIR)/generated/libvoqc$(EXTDLL)


ifeq ($(OSTYPE),$(filter $(OSTYPE),Win32 Cygwin))
$(BUILDDIR)/generated/libvoqc$(EXTDLL): $(CAML_INIT) $(LIBFILES)
	ocamlfind opt -o $@ -linkpkg -output-obj -verbose -package $(PACKAGES) $^
else ifeq ($(SYSTEM),$(filter $(SYSTEM),macosx))
$(BUILDDIR)/generated/libvoqc$(EXTDLL): $(CAML_INIT) $(LIBFILES)
	ocamlfind opt -o $@ -linkpkg -runtime-variant _pic -verbose -ccopt -dynamiclib -package $(PACKAGES) $^
else
$(BUILDDIR)/generated/libvoqc$(EXTDLL): $(CAML_INIT) $(LIBFILES)
	ocamlfind opt -o $@ -linkpkg -output-obj -runtime-variant _pic -verbose -package $(PACKAGES) $^
endif

stubs: $(GENERATED)

$(BUILDDIR)/qasm2sqir.cmx : $(BUILDDIR)/qasm2sqir.cmi
$(BUILDDIR)/FSetAVL.cmx : $(BUILDDIR)/FSetAVL.cmi
$(BUILDDIR)/FMapAVL.cmx : $(BUILDDIR)/FMapAVL.cmi
$(BUILDDIR)/UnitaryListRepresentation.cmx : $(BUILDDIR)/UnitaryListRepresentation.cmi
$(BUILDDIR)/RzQGateSet.cmx : $(BUILDDIR)/RzQGateSet.cmi
$(BUILDDIR)/Datatypes.cmx : $(BUILDDIR)/Datatypes.cmi
$(BUILDDIR)/OrderedTypeEx.cmx : $(BUILDDIR)/OrderedTypeEx.cmi
$(BUILDDIR)/GateCancellation.cmx : $(BUILDDIR)/GateCancellation.cmi
$(BUILDDIR)/HadamardReduction.cmx : $(BUILDDIR)/HadamardReduction.cmi
$(BUILDDIR)/NotPropagation.cmx : $(BUILDDIR)/NotPropagation.cmi
$(BUILDDIR)/RotationMerging.cmx : $(BUILDDIR)/RotationMerging.cmi
$(BUILDDIR)/Optimize.cmx : $(BUILDDIR)/Optimize.cmi



$(BUILDDIR)/stub/%.o:
	ocamlc -g -c stub/init.c
	mv init.o $@


$(GENERATED): $(GENERATOR)
	$(GENERATOR) $(BUILDDIR)/generated

$(BUILDDIR)/%.o: %.c
	$(CC) -c -o $@ -fPIC -I $(shell ocamlfind query ctypes) -I $(OCAMLDIR) -I $(OCAMLDIR)/../ctypes $<

$(BUILDDIR)/%.cmx: %.ml
	ocamlfind opt -c -o $@ -I $(BUILDDIR)/generated -I $(BUILDDIR) -package $(PACKAGES) $<

$(BUILDDIR)/%.cmi: %.mli
	ocamlfind c -c -o $@ -I $(BUILDDIR)/generated -I $(BUILDDIR) -package $(PACKAGES) $<
$(BUILDDIR)/%.ml: %.mli
	ocamlfind c -c -o $@ -I $(BUILDDIR)/generated -I $(BUILDDIR) -package $(PACKAGES) $<

$(GENERATOR): $(GENERATOR_FILES)
	ocamlfind opt  -o $@ -linkpkg -package $(PACKAGES) $^

clean:
	rm -rf $(BUILDDIR)
