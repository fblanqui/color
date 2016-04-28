(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski, 2006-04-27

This file provides the development concerning terms of simply typed
lambda-calculus.
*)

Set Implicit Arguments.

From CoLoR Require TermsAlgebraic.

Module Terms (Sig : TermsSig.Signature).

  Module Export TA := TermsAlgebraic.TermsAlgebraic Sig.

End Terms.
