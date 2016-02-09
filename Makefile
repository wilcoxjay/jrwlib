default: Makefile.coq
	make -f Makefile.coq all

clean:
	-make -f Makefile.coq clean
	rm -f Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject > Makefile.coq

.PHONY: default