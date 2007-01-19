(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski, 2006-04-27

This file provides the development concerning terms of simply typed
lambda-calculus.
*)

(* $Id: Terms.v,v 1.2 2007-01-19 17:22:39 blanqui Exp $ *)

Set Implicit Arguments.

Require TermsAlgebraic.

Module Terms (Sig : TermsSig.Signature).

  Module TA := TermsAlgebraic.TermsAlgebraic Sig.
  Export TA.

End Terms.
