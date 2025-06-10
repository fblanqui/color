<font color="red">C</font><font color="orange">o</font><font color="green">L</font><font color="magenta">o</font><font color="blue">R</font>, a Rocq library on rewriting theory and termination
========================================================

CoLoR is a library of formal mathematical definitions and proofs of
theorems on rewriting theory, &lambda;-calculus and termination whose
correctness has been mechanically checked by
the [Rocq](https://rocq-prover.org/) proof assistant. See
this [paper](http://rewriting.gforge.inria.fr/papers/mscs11.pdf)
for some presentation. More papers are provided at the end of this file.

Some developments using CoLoR:
[Rainbow](http://color.inria.fr/rainbow.html),
[HA-Spiral](https://users.ece.cmu.edu/~franzf/hacms.htm),
[Spi](http://sbriais.free.fr/),
[ATBR](http://perso.ens-lyon.fr/damien.pous/),
[CPV](http://proofos.sourceforge.net/doc/).

Installation:
---------------

Installation with [opam](https://opam.ocaml.org/):
```bash
opam repo add rocq-released https://rocq-prover.org/opam/released
opam update
opam install --jobs=$n coq-color
```
You can browse the definitions and statements by doing in the source directory `make doc` and read `doc/index.html` in your browser.

Scripts:
--------

CoLoR provides also useful scripts for doing statistics:
- do `make time` to record the compilation time of each file (then `time_coqc` is used instead of `coqc`)
- do `./stat_time` to get statistics on compilation time
- `./stat_coq [<directory>]` (default is `.`) provides the number of definitions, lemmas, etc.
- `./stat_color` provides the number of Rocq lines (including newlines and comments) for the various kinds of formalizations (mathematical structures, data structures, etc.)

Library contents:
----------------------

- Logic:
libraries providing basic meta-theorems and tactics (e.g. irreflexivity) on propositions and equality, both for intuitionistic and classical logic, the statement of the axiom of dependent choice, etc.

- Mathematical structures:
  * finite and infinite sets: cardinal of a finite set, infinite pigeon-hole principle, infinite Ramsey theorem
  * infinite relations/graphs: an extensive library of definitions and theorems on relations including basic operations like union/intersection/composition/iteration or reflexive/transitive/symmetric closure, their relations, the notions of finite path, cycle, strongly connected component, infinite path/rewrite sequence, etc.
  * finite relations/graphs: adjacency matrix, computation and topological sorting of strongly connected components, etc.
  * (quasi) orderings: linear extension of a finite acyclic relation, Tarski's fixpoint theorem (in a complete lattice, any monotone function has a least/greatest fixpoint), etc.
  * well-founded relations: preservation of termination for commuting relations, maximal reduction length of an element wrt a well-founded finitely branching relation, relation between the classical notion of termination (absence of infinite paths) and the intuitionistic one (inductive accessibility), etc.
  * (ordered) semi-rings: a library on semi-rings and ordered semi-rings, and its instantiation on various number data structures (natural numbers, integers, arctic/tropical numbers, etc.)

- Data structures:
  * libraries extending the Rocq standard library on various data structures: booleans, natural numbers, integers, pairs, lists, vectors, finite sets, finite maps, sets, relations, etc.
  * natural numbers: list of natural numbers smaller than some bound, least natural number satisfying some property, logarithmic to base 2, decidability of equality on bigN, maximum/minimum of a list of natural numbers, etc.
  * lists: an extensive library extending the Rocq standard library on lists including many functions and theorems on lists including for instance the number of occurrences of an element, lists with no duplicated elements, a constructive proof of the pigeon-hole principle, lemmas on the permutation of elements, etc.
  * vectors: an extensive library on vectors including many basic functions and theorems on vector manipulation, vector product/lexicographic ordering, vector arithmetic, vector components filtering and permutation
  * matrices: a library on matrices including basic functions and theorems on matrix arithmetic
  * finite multisets: a library on finite multisets including a proof that the multiset extension of a well-founded relation is well-founded
  * polynomials with multiple variables: a library on integer polynomials with multiple variables including basic functions and theorems on polynomial arithmetic, positivity and monotony
  * finite graphs: a library on finite graphs including a certified algorithm for computing its transitive closure (using a successor function representation) or its strongly connected components (using the adjacency matrix representation)

- Term structures:
  * strings/words: definition of basic notions like context and rewriting
  * varyadic terms (first-order terms with function symbols taking an arbitrary number of arguments): definition of basic notions like substitution, context, rewriting on varyadic terms
  * algebraic terms with function symbols of fixed arity: this is the most developed library on terms including many definitions and theorems on terms and term rewrite relations like the basic notions of substitution, context, subterm, position, cap and aliens, dependency pair, etc.; the notion of model/interpretation (universal algebra); a certified algorithm for matching; a certified algorithm for unification; etc.
  * simply typed &lambda;-terms with de Bruijn indices
  * pure and simply typed &lambda;-terms with named variables and explicit &alpha;-equivalence: definitions and properties of the basic notions of (higher-order) substitution, &alpha;-equivalence, &beta;-reduction, etc.; the equivalence of various definitions of &alpha;-equivalence (Curry-Feys, Church, Krivine, Gabbay-Pitts); Girard computability predicates; computability closure; strong normalization of &beta;-reduction and higher-order rewrite systems (e.g. Gödel' system T)

- Transformation techniques:
  * conversion string &rarr; algebraic term &rarr; varyadic term (CoLoR provides in particular a translation from CoLoR algebraic terms to [Coccinelle](https://www.lri.fr/~contejea/Coccinelle/coccinelle.html) terms to allow the reusability of Coccinelle results in CoLoR)
  * reversal of SRSs and unary TRSs
  * arguments filtering
  * dependancy pairs transformation
  * dependency graph decomposition
  * semantic labeling
  * flat context closure

- (Non-)Termination criteria:
  * first and higher order recursive path ordering (RPO and HORPO)
  * integer polynomial interpretations
  * integer/arctic/tropical matrix interpretations
  * computability closure for higher-order rewrite systems
  * loops (a decision procedure for verifying that a given rewrite sequence is a loop)

The directory Coccinelle is not part of CoLoR. It contains an
adaptation of the [Coccinelle](https://www.lri.fr/~contejea/Coccinelle/coccinelle.html) library which is used in
Conversion/Coccinelle.v. See `Coccinelle/README` for more information.

Contributors:
-----------------

Maintainer: [Frédéric Blanqui](https://blanqui.gitlabpages.inria.fr/) (INRIA, France)

**Contributors:**
Kim-Quyen Ly (INRIA),
Sidi Ould-Biha (INRIA, France),
Adam Koprowski (Radboud University, The Netherlands),
[Johannes Waldmann](http://www.imn.htwk-leipzig.de/~waldmann/) (Leipzig HTWK, Germany),
[Sorin Stratulat](http://sites.google.com/site/sorinica/) (Université Paul Verlaine, Metz, France),
Julien Bureaux (ENS Paris, France),
[Pierre-Yves Strub](http://pierre-yves.strub.nu/) (INRIA, France),
Wang Qian (Tsinghua University, China),
Zhang Lianyi (Tsinghua University, China),
[Hans Zantema](http://www.win.tue.nl/~hzantema/) (Radboud University, Nijmegen, The Netherlands),
[Jörg Endrullis](http://joerg.endrullis.de/) (Amsterdam Vrije Universiteit, The Netherlands),
Stéphane Le Roux (ENS Lyon, France),
Léo Ducas (ENS Paris, France),
[Solange Coupet-Grimal](http://pageperso.lif.univ-mrs.fr/~solange.coupet/) (Université de Provence Aix-Marseille I, France),
William Delobel (Université de Provence Aix-Marseille I, France),
Sébastien Hinderer (LORIA, France),
[Frédéric Blanqui](http://rewriting.gforge.inria.fr/) (INRIA, France)

Bibliography:
-----------------

- [CoLoR: a Coq library on well-founded rewrite relations and its
application to the automated verification of termination
certificates](http://rewriting.gforge.inria.fr/mscs11-pdf.html). F. Blanqui
and A. Koprowski, MSCS 21(4):827-859, 2011.

- [Coq formalization of the higher-order recursive path
ordering](http://dx.doi.org/10.1007/s00200-009-0105-5), A. Koprowski,
Applicable Algebra in Engineering Communication and Computing
20(5-6):379-425, 2009.

- [Automated Verification of Termination
Certificates](http://rewriting.gforge.inria.fr/rr09color-pdf.html),
F. Blanqui and A. Koprowski, INRIA Research Report 6949, 2009.

- [Automated Verification of Termination
Certificates](http://rewriting.gforge.inria.fr/talks/shanghai08.pdf),
F. Blanqui, Talk at East China Normal University, Shanghai, 3 December 2008.

- [Termination of rewriting and its
certification](http://dx.doi.org/10.6100/IR637480), A. Koprowski, PhD
Thesis, 2008.

- [Certification of Proving Termination of Term Rewriting by Matrix
Interpretations](http://dx.doi.org/10.1007/978-3-540-77566-9_28),
A. Koprowski and H. Zantema, SOFSEM'08.

- [Arctic termination... below
zero](http://dx.doi.org/10.1007/978-3-540-70590-1_14), A. Koprowski
and J. Waldmann, RTA'08.

- [Acyclicity and Linear Extendability: a Formal and Constructive
Equivalence](http://dx.doi.org/10.1007/978-3-642-03359-9_21), S. Le
Roux, TPHOL'07.

- [Certification of Matrix Interpretations in
Coq](http://color.inria.fr/papers/koprowski07wst.pdf), A. Koprowski
and H. Zantema, WST'07,
[[slides]](http://color.inria.fr/papers/koprowski07wst-slides.pdf)

- [Certification de preuves de terminaison basées sur la décomposition
du graphe des paires de
dépendance](http://color.inria.fr/papers/ducas07bsc.pdf), L. Ducas,
B. Sc. thesis, 2007.

- [CoLoR, a Coq Library on Rewriting and
termination](http://rewriting.gforge.inria.fr/wst06color-pdf.html),
F. Blanqui, S. Coupet-Grimal, W. Delobel, S. Hinderer and
A. Koprowski,
WST'06. [[slides]](http://rewriting.gforge.inria.fr/wst06color.pdf)

- [A Formalization of the Simply Typed Lambda Calculus in
Coq](http://color.inria.fr/papers/koprowski06draft.pdf), A. Koprowski,
Manuscript, 2006.

- [A Constructive Axiomatization of the Recursive Path
Ordering](http://color.inria.fr/papers/coupet06tr.pdf),
S. Coupet-Grimal and W. Delobel, Research report 28, LIF,
Universit&eacute de la M&eacute;diterran&eacute;e, 2006.

- [An Effective Proof of the Well-Foundedness of the Multiset Path
Ordering](http://dx.doi.org/10.1007/s00200-006-0020-y),
S. Coupet-Grimal and W. Delobel, Applicable Algebra in Engineering
Communication and Computing 17(6):453-469, 2006.

- [Certified Higher-Order Recursive Path
Ordering](http://dx.doi.org/10.1007/11805618_17), A. Koprowski,
RTA'06.

- [Une preuve effective de la bonne fondation de l'ordre récursif
multi-ensemble sur les
chemins](http://color.inria.fr/papers/coupet06jfla.pdf),
S. Coupet-Grimal and W. Delobel, JFLA'06.

- [Well-foundedness of the Higher-Order Recursive Path Ordering in
Coq](http://color.inria.fr/papers/koprowski04master.pdf),
A. Koprowski, Master thesis, 2004.

- [Certification des preuves de termination par interpr&eacute;tations
polynomiales](http://color.inria.fr/papers/hinderer04master.pdf),
S. Hinderer, Master thesis, 2004.

- [Well-foundedness of the Recursive Path Ordering in
Coq](http://color.inria.fr/papers/dekleijn04dptd.pdf), N. de Kleijn,
A. Koprowski and F. van Raamsdonk, Dutch Proof Tools Day, 2004.

- [Well-foundedness of RPO in
Coq](http://color.inria.fr/papers/dekleijn03master.pdf), N. de Kleijn,
Master thesis, 2003.
