build: Makefile.coq
	$(MAKE) -f Makefile.coq

docs: build
	coqdoc --html --utf8 --no-index --no-externals --short turing_typeclass.v
	mv turing_typeclass.html index.html
	sed -i '' 's,<title>turing_typeclass</title>,<title>Coq typeclass resolution is Turing-complete</title>,;s/×/*/;s/ *$$//' index.html

clean::
	@if [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq cleanall; fi
	$(RM) -f Makefile.coq Makefile.coq.conf *.html *.css

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

.PHONY: build docs clean

-include Makefile.coq
