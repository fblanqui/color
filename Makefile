# CoLoR, a Coq library on rewriting and termination.
# See the COPYRIGHTS and LICENSE files.
#
# - Frederic Blanqui, 2005-02-03

MAKEFLAGS := -r -j

.SUFFIXES:

.PHONY: clean clean-all clean-doc default config create_Makefile.coq create_Makefile.all dist doc install-dist install-doc tags all

COQC := $(COQBIN)coqc

MAKECOQ := $(MAKE) -f Makefile.coq
MAKEALL := $(MAKE) -f Makefile.all

PC_VFILE := ProofChecker/ProofChecker.v

VFILES := $(shell find . -name \*.v -not -name ProofChecker.v)

default: Makefile.coq
	$(MAKECOQ) OTHERFLAGS="-dont-load-proofs"

all: Makefile.all
	time -f %e $(MAKEALL) OTHERFLAGS="-dont-load-proofs"

config: create_Makefile.coq create_Makefile.all

create_Makefile.coq Makefile.coq:
	coq_makefile -R . CoLoR $(VFILES) > Makefile.coq
	$(MAKECOQ) depend

create_Makefile.all Makefile.all:
	coq_makefile -R . CoLoR $(VFILES) $(PC_VFILE) > Makefile.all
	$(MAKEALL) depend

clean:
	rm -f `find . -name \*~`
	$(MAKEALL) clean

clean-all: clean
	rm -f Makefile.coq Makefile.all

clean-doc:
	rm -f doc/CoLoR.*.html doc/index.html

tags:
	coqtags `find . -name \*.v`

doc:
	coqdoc --html -g -d doc -R . CoLoR `find . -path ./Coccinelle -prune -o -name \*.v -print`
	./createIndex

ADR := login-linux.inria.fr:liama/www/color

install-doc:
	scp doc/coqdoc.css doc/*.html $(ADR)/doc

dist:
	./createDist

install-dist:
	scp CoLoR_`date +%y%m%d`.tar.gz $(ADR)/CoLoR.tar.gz
	scp CHANGES $(ADR)/CHANGES.CoLoR

%.vo: %.v
	$(MAKECOQ) OTHERFLAGS="-dont-load-proofs" $@

%:
	$(MAKECOQ) OTHERFLAGS="-dont-load-proofs" $@
