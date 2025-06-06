# CoLoR, a Coq library on rewriting and termination.
# See the COPYRIGHTS and LICENSE files.
#
# - Frederic Blanqui, 2005-02-03

LIBNAME := CoLoR

.SUFFIXES:

.PHONY: default config clean clean-dep clean-all clean-doc tags doc install-doc install-dist targz

MAKECOQ := +$(MAKE) -r -f Makefile.coq

VFILES := $(shell find . -name \*.v | grep -v .\# | sed -e 's|^./||g')

default: Makefile.coq
	$(MAKECOQ)

time: Makefile.coq
	COQC=./time_coqc make

config Makefile.coq:
	echo -R . $(LIBNAME) $(VFILES) > _CoqProject
	rocq makefile -f _CoqProject -o Makefile.coq

clean:
	rm -f `find . -name \*~`
	-$(MAKECOQ) clean
	rm -rf `find . -name .coq-native -o -name .\*.aux -o -name \*.cache`

clean-dep:
	rm -f `find . -name \*.v.d`

clean-all: clean clean-doc clean-dep
	rm -f _CoqProject Makefile.coq Makefile.coq.conf stat_time.log `find . -name \*.time`

clean-doc:
	rm -f doc/$(LIBNAME).*.html doc/index.html doc/main.html doc/coqdoc.css

tags:
	coqtags $(VFILES)

doc:
	coqdoc --html -g -d doc -R . $(LIBNAME) `find . -path ./Coccinelle -prune -o -name \*.v -print`
	./create_index

WEB := scm.gforge.inria.fr:/home/groups/color/htdocs

install-doc:
	scp -r doc/coqdoc.css doc/*.html $(WEB)/doc/

install-dist:
	scp CHANGES $(WEB)/CHANGES.CoLoR

targz:
	rm -rf /tmp/color
	cp -r . /tmp/color
	make -C /tmp/color clean-all
	rm -rf `find /tmp/color -name .svn`
	(cd /tmp; tar zcf color.tar.gz color)
	rm -rf /tmp/color
	mv /tmp/color.tar.gz .

%.vo: %.v
	$(MAKECOQ) $@

%:
	$(MAKECOQ) $@
