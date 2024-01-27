
(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "-parsing" "-w" "+undeclared-scope" "-w" "+non-primitive-record" "-w" "-ambiguous-paths" "-w" "-redundant-canonical-projection" "-w" "-projection-no-head-constant" "-w" "-deprecated-native-compiler-option" "-native-compiler" "ondemand" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/analysis/classical" "mathcomp.classical" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/analysis/theories" "mathcomp.analysis" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/HB" "HB" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/elpi" "elpi" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/mathcomp" "mathcomp" "-top" "Top.bug_01") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 1520 lines to 102 lines, then from 115 lines to 7080 lines, then from 7084 lines to 5514 lines, then from 5204 lines to 214 lines, then from 227 lines to 8975 lines, then from 8977 lines to 9174 lines, then from 8558 lines to 3022 lines, then from 3030 lines to 641 lines, then from 654 lines to 3374 lines, then from 3378 lines to 3344 lines, then from 3149 lines to 2937 lines, then from 2945 lines to 2872 lines, then from 2880 lines to 2758 lines, then from 2766 lines to 2622 lines, then from 2630 lines to 2480 lines, then from 2488 lines to 2302 lines, then from 2310 lines to 2048 lines, then from 2056 lines to 1781 lines, then from 1789 lines to 1215 lines, then from 1223 lines to 1119 lines, then from 1137 lines to 891 lines, then from 904 lines to 4337 lines, then from 4342 lines to 4269 lines, then from 4063 lines to 2355 lines, then from 2363 lines to 992 lines, then from 1005 lines to 1959 lines, then from 1964 lines to 2248 lines, then from 2194 lines to 1028 lines, then from 1046 lines to 1010 lines, then from 1023 lines to 1109 lines, then from 1115 lines to 1008 lines, then from 1027 lines to 1008 lines, then from 1021 lines to 2291 lines, then from 2297 lines to 1497 lines, then from 1344 lines to 1170 lines, then from 1183 lines to 7798 lines, then from 7804 lines to 8295 lines, then from 8038 lines to 6547 lines, then from 6555 lines to 4896 lines, then from 4904 lines to 2829 lines, then from 2837 lines to 1739 lines, then from 1757 lines to 1434 lines, then from 1447 lines to 8252 lines, then from 0 lines to 8252 lines, then from 8263 lines to 7611 lines, then from 6945 lines to 6086 lines, then from 6094 lines to 4654 lines, then from 4662 lines to 3198 lines, then from 3206 lines to 2308 lines, then from 2326 lines to 1833 lines, then from 1846 lines to 1907 lines, then from 1913 lines to 1826 lines, then from 1840 lines to 10763 lines, then from 10767 lines to 12343 lines, then from 11737 lines to 9895 lines, then from 9903 lines to 8999 lines, then from 9007 lines to 7924 lines, then from 7932 lines to 6365 lines, then from 6373 lines to 4472 lines, then from 4480 lines to 2859 lines, then from 2876 lines to 2066 lines, then from 2079 lines to 6165 lines, then from 6168 lines to 5694 lines *)
(* coqc version 8.20+alpha compiled with OCaml 4.14.1
   coqtop version 532fcf76d13e:/builds/coq/coq/_build/default,(HEAD detached at 26c84c7) (26c84c7924a0b719c579dacbad84a61567e196e9)
   Modules that could not be inlined: HB.structures
   Expected coqc runtime on this file: 8.883 sec *)
Require Coq.Init.Ltac.
Require Coq.NArith.BinNat.
Require Coq.NArith.Ndec.
Require Coq.PArith.BinPos.
Require Coq.setoid_ring.Ring.
Require Coq.ssr.ssrbool.
Require Coq.ssr.ssreflect.
Require Coq.ssr.ssrfun.
Require mathcomp.ssreflect.ssrnotations.
Require mathcomp.ssreflect.ssreflect.
Require mathcomp.ssreflect.ssrfun.
Require mathcomp.ssreflect.ssrbool.
Require mathcomp.ssreflect.eqtype.
Require mathcomp.ssreflect.ssrnat.
Require mathcomp.ssreflect.seq.
Require mathcomp.ssreflect.choice.
Require mathcomp.ssreflect.div.
Require mathcomp.ssreflect.path.
Require mathcomp.ssreflect.fintype.
Require mathcomp.ssreflect.tuple.
Require mathcomp.ssreflect.finfun.
Require mathcomp.ssreflect.bigop.
Require mathcomp.ssreflect.finset.
Require Coq.Strings.String.
Require Coq.Bool.Bool.
Require Coq.Floats.PrimFloat.
Require Coq.Numbers.Cyclic.Int63.PrimInt63.
Require elpi.elpi.
Require elpi.apps.locker.
Require HB.structures.

Module Export AdmitTactic.
Module Import LocalFalse.
Inductive False : Prop := .
End LocalFalse.
Axiom proof_admitted : False.
Import Coq.Init.Ltac.
Tactic Notation "admit" := abstract case proof_admitted.
End AdmitTactic.

Module mathcomp_DOT_finmap_DOT_finmap_WRAPPED.
Module finmap.
 
 

Set Warnings "-notation-incompatible-format".
Import mathcomp.ssreflect.ssreflect mathcomp.ssreflect.ssrbool mathcomp.ssreflect.ssrnat mathcomp.ssreflect.eqtype mathcomp.ssreflect.ssrfun mathcomp.ssreflect.seq.
Set Warnings "notation-incompatible-format".
Import mathcomp.ssreflect.choice mathcomp.ssreflect.path mathcomp.ssreflect.finset mathcomp.ssreflect.finfun mathcomp.ssreflect.fintype mathcomp.ssreflect.bigop.

 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Reserved Notation "A `=` B" (at level 70, no associativity).
Reserved Notation "A `<>` B" (at level 70, no associativity).
Reserved Notation "A `==` B" (at level 70, no associativity).
Reserved Notation "A `!=` B" (at level 70, no associativity).
Reserved Notation "A `=P` B" (at level 70, no associativity).

Reserved Notation "f @`[ key ] A" (at level 24, key at level 0).
Reserved Notation "f @2`[ key ] ( A , B )"
  (at level 24, format "f  @2`[ key ]  ( A ,  B )").
Reserved Notation "f @` A" (at level 24).
Reserved Notation "f @2` ( A , B )" (at level 24, format "f  @2`  ( A ,  B )").

 
Reserved Notation "[ 'fset' E | x : T 'in' A ]" (at level 0, E, x at level 99).
Reserved Notation "[ 'fset' E | x 'in' A ]" (at level 0, E, x at level 99).
Reserved Notation "[ 'fset' E | x : A ]" (at level 0, E, x at level 99).
Reserved Notation "[ 'fset'  x  :  T  'in'  A ]" (at level 0, x at level 99).
Reserved Notation "[ 'fset'  x  :  T  'in'  A  |  P ]"
  (at level 0, x at level 99).
Reserved Notation "[ 'fset' x 'in' A | P ]" (at level 0, x at level 99).
Reserved Notation "[ 'fset' x 'in' A ]" (at level 0, x at level 99).
Reserved Notation "[ 'fset' x : T | P ]" (at level 0, x at level 99).
Reserved Notation "[ 'fset' x : T | P & Q ]" (at level 0, x at level 99).
Reserved Notation "[ 'fset'  x  :  T  'in' A  |  P  &  Q ]"
  (at level 0, x at level 99).
Reserved Notation "[ 'fset' x 'in' A | P & Q ]" (at level 0, x at level 99).

 
Reserved Notation "[ 'fset' E | x : T 'in' A , y : T' 'in' B ]"
  (at level 0, E, x at level 99, A at level 200, y at level 99).
Reserved Notation "[ 'fset' E | x 'in' A , y 'in' B ]"
  (at level 0, E, x at level 99, A at level 200, y at level 99).

 
Reserved Notation "[ 'fset[' key ] E | x : T 'in' A ]"
  (at level 0, E, x at level 99).
Reserved Notation "[ 'fset[' key ] E | x 'in' A ]"
  (at level 0, E, x at level 99).
Reserved Notation "[ 'fset[' key ] E | x : A ]" (at level 0, E, x at level 99).
Reserved Notation "[ 'fset[' key ] E | x 'in' A & P ]"
  (at level 0, E, x at level 99).
Reserved Notation "[ 'fset[' key ] E | x : A & P ]"
  (at level 0, E, x at level 99).
Reserved Notation "[ 'fset[' key ] E | x : T 'in' A , y : T' 'in' B ]"
  (at level 0, E, x at level 99, A at level 200, y at level 99).
Reserved Notation "[ 'fset[' key ] E | x 'in' A , y 'in' B ]"
  (at level 0, E, x at level 99, A at level 200, y at level 99).
Reserved Notation "[ 'fset[' key ] E | x : A , y : B ]"
  (at level 0, E, x at level 99, A at level 200, y at level 99).
Reserved Notation "[ 'fset[' key ] E | x : A , y 'in' B ]"
  (at level 0, E, x, y at level 99).
Reserved Notation "[ 'fset[' key ] E | x 'in' A , y : B ]"
  (at level 0, E, x, y at level 99).
Reserved Notation "[ 'fset[' key ] E | x 'in' A , y 'in' B & P ]"
  (at level 0, E, x, y at level 99).
Reserved Notation "[ 'fset[' key ] E | x : A , y 'in' B & P ]"
  (at level 0, E, x, y at level 99).
Reserved Notation "[ 'fset[' key ] E | x 'in' A , y : B & P ]"
  (at level 0, E, x, y at level 99).
Reserved Notation "[ 'fset[' key ] E | x : A , y : B & P ]"
  (at level 0, E, x, y at level 99).

Reserved Notation "[ 'fset[' key ]  x  :  T  'in'  A ]"
  (at level 0, x at level 99).
Reserved Notation "[ 'fset[' key ]  x  :  T  'in'  A  |  P ]"
  (at level 0, x at level 99).
Reserved Notation "[ 'fset[' key ] x 'in' A | P ]" (at level 0, x at level 99).
Reserved Notation "[ 'fset[' key ] x 'in' A ]" (at level 0, x at level 99).
Reserved Notation "[ 'fset[' key ] x : T | P ]" (at level 0, x at level 99).
Reserved Notation "[ 'fset[' key ] x : T | P & Q ]" (at level 0, x at level 99).
Reserved Notation "[ 'fset[' key ]  x  :  T  'in' A  |  P  &  Q ]"
  (at level 0, x at level 99).
Reserved Notation "[ 'fset[' key ] x 'in' A | P & Q ]"
  (at level 0, x at level 99).

 
Reserved Notation "[ 'f' 'set' E | x 'in' A ]"
  (at level 0, E, x at level 99,
   format "[ '[hv' 'f' 'set'  E '/ '  |  x  'in'  A ] ']'").
Reserved Notation "[ 'f' 'set' E | x : A ]"
  (at level 0, E, x at level 99,
   format "[ '[hv' 'f' 'set'  E '/ '  |  x  :  A ] ']'").
Reserved Notation "[ 'f' 'set' x 'in' A | P ]"
  (at level 0, x at level 99, format "[ 'f' 'set'  x  'in'  A  |  P ]").
Reserved Notation "[ 'f' 'set' x 'in' A ]"
  (at level 0, x at level 99, format "[ 'f' 'set'  x  'in'  A ]").
Reserved Notation "[ 'f' 'set' x : T | P ]"
  (at level 0, x at level 99, format "[ 'f' 'set'  x  :  T  |  P ]").
Reserved Notation "[ 'f' 'set' x : T | P & Q ]"
  (at level 0, x at level 99, format "[ 'f' 'set'  x  :  T  |  P  &  Q ]").
Reserved Notation "[ 'f' 'set' x 'in' A | P & Q ]"
  (at level 0, x at level 99, format "[ 'f' 'set'  x  'in'  A  |  P  &  Q ]").
 
Reserved Notation "[ 'f' 'set' E | x 'in' A , y 'in' B ]"
  (at level 0, E, x at level 99, A at level 200, y at level 99,
   format "[ '[hv' 'f' 'set'  E '/ '  |  x  'in'  A , '/' y  'in'  B ] ']'").

Reserved Notation "{fset K }" (at level 0, format "{fset  K }").
Reserved Notation "[ 'fset' a ]"
  (at level 0, a at level 99, format "[ 'fset'  a ]").
Reserved Notation "[ 'fset' a : T ]"
  (at level 0, a at level 99, format "[ 'fset'  a   :  T ]").
Reserved Notation "A `&` B" (at level 48, left associativity).
Reserved Notation "A `*` B" (at level 46, left associativity).
Reserved Notation "A `+` B" (at level 54, left associativity).
Reserved Notation "A +` B"  (at level 54, left associativity).
Reserved Notation "A `|` B" (at level 52, left associativity).
Reserved Notation "a |` A"  (at level 52, left associativity).
Reserved Notation "A `\` B" (at level 50, left associativity).
Reserved Notation "A `\ b"  (at level 50, left associativity).
Reserved Notation "A `<=` B" (at level 70, no associativity).
Reserved Notation "A `<` B" (at level 70, no associativity).

 
Reserved Notation "[ 'fset' a1 ; a2 ; .. ; an ]"
  (at level 0, a1 at level 99, format "[ 'fset'  a1 ;  a2 ;  .. ;  an ]").

Reserved Notation "[ 'disjoint' A & B ]".

 
Reserved Notation "[ 'fset' E | x 'in' A & P ]" (at level 0, E, x at level 99).
Reserved Notation "[ 'fset' E | x : A & P ]" (at level 0, E, x at level 99).
Reserved Notation "[ 'fset' E | x : A , y 'in' B ]"
  (at level 0, E, x, y at level 99).
Reserved Notation "[ 'fset' E | x 'in' A , y : B ]"
  (at level 0, E, x, y at level 99).
Reserved Notation "[ 'fset' E | x : A , y : B ]"
  (at level 0, E, x, y at level 99).
Reserved Notation "[ 'fset' E | x 'in' A , y 'in' B & P ]"
  (at level 0, E, x, y at level 99).
Reserved Notation "[ 'fset' E | x : A , y 'in' B & P ]"
  (at level 0, E, x, y at level 99).
Reserved Notation "[ 'fset' E | x 'in' A , y : B & P ]"
  (at level 0, E, x, y at level 99).
Reserved Notation "[ 'fset' E | x : A , y : B & P ]"
  (at level 0, E, x, y at level 99).

Reserved Notation "[ 'fsetval' x 'in' A ]" (at level 0, x at level 99).
Reserved Notation "[ 'fsetval' x 'in' A | P ]" (at level 0, x at level 99).
Reserved Notation "[ 'fsetval' x 'in' A | P & Q ]" (at level 0, x at level 99).
Reserved Notation "[ 'fsetval' x : A ]" (at level 0, x at level 99).
Reserved Notation "[ 'fsetval' x : A | P ]" (at level 0, x at level 99).
Reserved Notation "[ 'fsetval' x : A | P & Q ]" (at level 0, x at level 99).

 
Reserved Notation "[ 'fsetval[' key ] x 'in' A ]" (at level 0, x at level 99).
Reserved Notation "[ 'fsetval[' key ] x 'in' A | P ]"
  (at level 0, x at level 99).
Reserved Notation "[ 'fsetval[' key ] x 'in' A | P & Q ]"
  (at level 0, x at level 99).
Reserved Notation "[ 'fsetval[' key ] x : A ]" (at level 0, x at level 99).
Reserved Notation "[ 'fsetval[' key ] x : A | P ]" (at level 0, x at level 99).
Reserved Notation "[ 'fsetval[' key ] x : A | P & Q ]"
  (at level 0, x at level 99).

 
Reserved Notation "[ 'f' 'set' E | x 'in' A & P ]"
  (at level 0, E, x at level 99,
   format "[ '[hv' 'f' 'set'  E '/ '  |  x  'in'  A '/ '  &  P ] ']'").
Reserved Notation "[ 'f' 'set' E | x : A & P ]"
  (at level 0, E, x at level 99,
   format "[ '[hv' 'f' 'set'  E '/ '  |  x  :  A '/ '  &  P ] ']'").
Reserved Notation "[ 'f' 'set' E | x : A , y 'in' B ]"
  (at level 0, E, x, y at level 99, format
   "[ '[hv' 'f' 'set'  E '/ '  |  x  :  A , '/   '  y  'in'  B ] ']'").
Reserved Notation "[ 'f' 'set' E | x 'in' A , y : B ]"
  (at level 0, E, x, y at level 99, format
   "[ '[hv' 'f' 'set'  E '/ '  |  x  'in'  A , '/   '  y  :  B ] ']'").
Reserved Notation "[ 'f' 'set' E | x : A , y : B ]"
  (at level 0, E, x, y at level 99, format
   "[ '[hv' 'f' 'set'  E '/ '  |  x  :  A , '/   '  y  :  B ] ']'").
Reserved Notation "[ 'f' 'set' E | x 'in' A , y 'in' B & P ]"
  (at level 0, E, x, y at level 99, format
   "[ '[hv' 'f' 'set'  E '/ '  |  x  'in'  A , '/   '  y  'in'  B '/ '  &  P ] ']'").
Reserved Notation "[ 'f' 'set' E | x : A , y 'in' B & P ]"
  (at level 0, E, x, y at level 99, format
   "[ '[hv' 'f' 'set'  E '/ '  |  x  :  A , '/   '  y  'in'  B  &  P ] ']'").
Reserved Notation "[ 'f' 'set' E | x 'in' A , y : B & P ]"
  (at level 0, E, x, y at level 99, format
   "[ '[hv' 'f' 'set'  E '/ '  |  x  'in'  A , '/   '  y  :  B  &  P ] ']'").
Reserved Notation "[ 'f' 'set' E | x : A , y : B & P ]"
  (at level 0, E, x, y at level 99, format
   "[ '[hv' 'f' 'set'  E '/ '  |  x  :  A , '/   '  y  :  B  &  P ] ']'").

Reserved Notation "[ 'f' 'setval' x 'in' A ]"
  (at level 0, x at level 99, format "[ 'f' 'setval'  x  'in'  A ]").
Reserved Notation "[ 'f' 'setval' x 'in' A | P ]"
  (at level 0, x at level 99, format "[ 'f' 'setval'  x  'in'  A  |  P ]").
Reserved Notation "[ 'f' 'setval' x 'in' A | P & Q ]"
  (at level 0, x at level 99,
   format "[ 'f' 'setval'  x  'in'  A  |  P  &  Q ]").
Reserved Notation "[ 'f' 'setval' x : A ]"
  (at level 0, x at level 99, format "[ 'f' 'setval'  x  :  A ]").
Reserved Notation "[ 'f' 'setval' x : A | P ]"
  (at level 0, x at level 99, format "[ 'f' 'setval'  x  :  A  |  P ]").
Reserved Notation "[ 'f' 'setval' x : A | P & Q ]"
  (at level 0, x at level 99, format "[ 'f' 'setval'  x  :  A  |  P  &  Q ]").

Reserved Notation "\bigcup_ ( i <- r | P ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \bigcup_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\bigcup_ ( i <- r ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \bigcup_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\bigcup_ ( i | P ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \bigcup_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\bigcup_ ( i 'in' A | P ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \bigcup_ ( i  'in'  A  |  P ) '/  '  F ']'").
Reserved Notation "\bigcup_ ( i 'in' A ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \bigcup_ ( i  'in'  A ) '/  '  F ']'").

Reserved Notation "{fmap T }" (at level 0, format "{fmap  T }").
Reserved Notation "x .[ k <- v ]"
  (at level 2, left associativity, format "x .[ k  <-  v ]").
Reserved Notation "x .[~ k ]" (at level 2, k at level 200, format "x .[~  k ]").
Reserved Notation "x .[& k ]" (at level 2, k at level 200, format "x .[&  k ]").
Reserved Notation "x .[\ k ]" (at level 2, k at level 200, format "x .[\  k ]").
Reserved Notation "x .[? k ]" (at level 2, k at level 200, format "x .[?  k ]").
Reserved Infix "`~`" (at level 52).
Reserved Notation "[ 'fset' k ]" (at level 0, k at level 99, format "[ 'fset'  k ]").

 
Definition PredType : forall T pT, (pT -> pred T) -> predType T.
exact PredType || exact mkPredType.
Defined.
Arguments PredType [T pT] toP.

Local Notation predOfType T := (pred_of_simpl (@pred_of_argType T)).

Definition oextract (T : Type) (o : option T) : o -> T :=
  if o is Some t return o -> T then fun=> t else False_rect T \o notF.

Lemma oextractE (T : Type) (x : T) (xP : Some x) : oextract xP = x.
Proof.
by [].
Qed.

Lemma Some_oextract T (x : option T) (x_ex : x) : Some (oextract x_ex) = x.
Proof.
by case: x x_ex.
Qed.

Definition ojoin T (x : option (option T)) :=
  if x is Some y then y else None.

Lemma Some_ojoin T (x : option (option T)) : x -> Some (ojoin x) = x.
Proof.
by case : x.
Qed.

Lemma ojoinT T (x : option (option T)) : ojoin x -> x.
Proof.
by case: x.
Qed.

Lemma TaggedP (T1 : Type) (T2 : T1 -> Type) (P : forall x, T2 x -> Type) :
    (forall t : {x : T1 & T2 x}, P _ (tagged t)) ->
  forall (x : T1) (y : T2 x), P x y.
Proof.
by move=> /(_ (Tagged _ _)).
Qed.
Arguments TaggedP {T1} T2.

Module Type SortKeysSig.
Section SortKeys.
Variable (K : choiceType).
Implicit Types (k : K) (ks : seq K).

Axiom f : seq K -> seq K.
Axiom perm : forall s, perm_eq (f s) (undup s).
Axiom uniq : forall s, uniq (f s).
Axiom E : forall (s : seq K), f s =i s.
Axiom eq : forall (s s' : seq K), s =i s' <-> f s = f s'.
End SortKeys.
End SortKeysSig.

Module SortKeys : SortKeysSig.
Section SortKeys.
Variable (K : choiceType).
Implicit Types (k : K) (ks : seq K).
Definition f (s : seq K) := choose (perm_eq (undup s)) (undup s).
Fact perm s : perm_eq (f s) (undup s).
Proof.
by rewrite perm_sym chooseP.
Qed.
Fact uniq s : uniq (f s).
Proof.
by rewrite (perm_uniq (perm _)) undup_uniq.
Qed.
Fact E (s : seq K) : f s =i s.
Proof.
by move=> x; rewrite (perm_mem (perm _)) mem_undup.
Qed.
Lemma eq (s s' : seq K) : s =i s' <-> f s = f s'.
Proof.
split=> [eq_ss'|eq_ss' k]; last by rewrite -E eq_ss' E.
rewrite /f; have peq_ss' : perm_eq (undup s) (undup s').
  by apply: uniq_perm; rewrite ?undup_uniq // => x; rewrite !mem_undup.
rewrite (@choose_id _ _ _ (undup s')) //=; apply: eq_choose => x /=.
by apply: sym_left_transitive; [exact: perm_sym | exact: (@perm_trans)|].
Qed.
End SortKeys.
End SortKeys.

#[global] Hint Resolve SortKeys.perm SortKeys.uniq SortKeys.E : core.

Notation sort_keys      := SortKeys.f.
Notation sort_keys_perm := SortKeys.perm.
Notation sort_keys_uniq := SortKeys.uniq.
Notation sort_keysE     := SortKeys.E.
Notation eq_sort_keys   := SortKeys.eq.

Section ChoiceKeys.
Variable (K : choiceType).
Implicit Types (k : K) (ks : seq K).

Lemma mem_sort_keys ks k : k \in ks -> k \in sort_keys ks.
Proof.
by rewrite sort_keysE.
Qed.

Lemma mem_sort_keys_intro ks k : k \in sort_keys ks -> k \in ks.
Proof.
by rewrite sort_keysE.
Qed.

Lemma sort_keys_nil : sort_keys [::] = [::] :> seq K.
Proof.
have := sort_keysE ([::] : seq K).
by case: sort_keys => //= a l /(_ a); rewrite mem_head.
Qed.

Lemma sort_keys_id ks : sort_keys (sort_keys ks) = sort_keys ks.
Proof.
by have /eq_sort_keys := sort_keysE ks.
Qed.

Definition canonical_keys ks := sort_keys ks == ks.

Lemma canonical_uniq ks : canonical_keys ks -> uniq ks.
Proof.
by move=> /eqP <-; exact: sort_keys_uniq.
Qed.

Lemma canonical_sort_keys ks : canonical_keys (sort_keys ks).
Proof.
by rewrite /canonical_keys sort_keys_id.
Qed.

Lemma canonical_eq_keys ks ks' :
  canonical_keys ks -> canonical_keys ks' ->
  ks =i ks' -> ks = ks'.
Proof.
move=> /eqP; case: _ /; move=> /eqP; case: _ / => eq_ks_ks'.
by apply/eq_sort_keys => x; rewrite -sort_keysE eq_ks_ks' sort_keysE.
Qed.

Lemma size_sort_keys ks : size (sort_keys ks) = size (undup ks).
Proof.
exact: perm_size.
Qed.

End ChoiceKeys.
Arguments eq_sort_keys {K s s'}.

 
 
 

Section Def.
Variables (K : choiceType).

Structure finSet : Type := mkFinSet {
  enum_fset :> seq K;
  _ : canonical_keys enum_fset
}.

Definition finset_of (_ : phant K) := finSet.

End Def.

Identity Coercion type_of_finset : finset_of >-> finSet.
Notation "{fset T }" := (@finset_of _ (Phant T)) : type_scope.

Definition pred_of_finset (K : choiceType)
  (f : finSet K) : pred K := fun k => k \in (enum_fset f).
Canonical finSetPredType (K : choiceType) := PredType (@pred_of_finset K).

Section FinSetCanonicals.

Variable (K : choiceType).

Canonical fsetType := Eval hnf in [subType for (@enum_fset K)].
Definition fset_eqMixin := Eval hnf in [eqMixin of {fset K} by <:].
Canonical fset_eqType := Eval hnf in EqType {fset K} fset_eqMixin.
Definition fset_choiceMixin := Eval hnf in [choiceMixin of {fset K} by <:].
Canonical fset_choiceType := Eval hnf in ChoiceType {fset K} fset_choiceMixin.

End FinSetCanonicals.

Section FinTypeSet.

Variables (K : choiceType) (A : finSet K).

Lemma keys_canonical : canonical_keys (enum_fset A).
Proof.
by case: A.
Qed.

Lemma fset_uniq : uniq (enum_fset A).
Proof.
by rewrite canonical_uniq // keys_canonical.
Qed.

Record fset_sub_type : predArgType :=
  FSetSub {fsval : K; fsvalP : in_mem fsval (@mem K _ A)}.

Canonical fset_sub_subType := Eval hnf in [subType for fsval].
Definition fset_sub_eqMixin := Eval hnf in [eqMixin of fset_sub_type by <:].
Canonical fset_sub_eqType := Eval hnf in EqType fset_sub_type fset_sub_eqMixin.
Definition fset_sub_choiceMixin := Eval hnf in [choiceMixin of fset_sub_type by <:].
Canonical fset_sub_choiceType := Eval hnf in ChoiceType fset_sub_type fset_sub_choiceMixin.
Definition fset_countMixin (T : countType) := Eval hnf in [countMixin of {fset T} by <:].
Canonical fset_countType (T : countType) := Eval hnf in CountType {fset T} (fset_countMixin T).

Definition fset_sub_enum : seq fset_sub_type :=
  undup (pmap insub (enum_fset A)).

Lemma mem_fset_sub_enum x : x \in fset_sub_enum.
Proof.
by rewrite mem_undup mem_pmap -valK map_f // fsvalP.
Qed.

Lemma val_fset_sub_enum : map val fset_sub_enum = enum_fset A.
Proof.
rewrite /fset_sub_enum undup_id ?pmap_sub_uniq ?fset_uniq//.
rewrite (pmap_filter (@insubK _ _ _)); apply/all_filterP.
by apply/allP => x; rewrite isSome_insub.
Qed.

Definition fset_sub_pickle x := index x fset_sub_enum.
Definition fset_sub_unpickle n := nth None (map some fset_sub_enum) n.
Lemma fset_sub_pickleK : pcancel fset_sub_pickle fset_sub_unpickle.
Proof.
rewrite /fset_sub_unpickle => x.
by rewrite (nth_map x) ?nth_index ?index_mem ?mem_fset_sub_enum.
Qed.

Definition fset_sub_countMixin := CountMixin fset_sub_pickleK.
Canonical fset_sub_countType := Eval hnf in CountType fset_sub_type fset_sub_countMixin.

Definition fset_sub_finMixin :=
  Eval hnf in UniqFinMixin (undup_uniq _) mem_fset_sub_enum.
Canonical fset_sub_finType := Eval hnf in FinType fset_sub_type fset_sub_finMixin.
Canonical fset_sub_subfinType := [subFinType of fset_sub_type].

Lemma enum_fsetE : enum_fset A = [seq val i | i <- enum fset_sub_type].
Proof.
by rewrite enumT unlock val_fset_sub_enum.
Qed.

Lemma cardfE : size (enum_fset A) = #|fset_sub_type|.
Proof.
by rewrite cardE enum_fsetE size_map.
Qed.

End FinTypeSet.

Identity Coercion finSet_sub_type : finset_of >-> finSet.
Coercion fset_sub_type : finSet >-> predArgType.
#[global] Hint Resolve fsvalP fset_uniq mem_fset_sub_enum : core.

Declare Scope fset_scope.
Delimit Scope fset_scope with fset.
Local Open Scope fset_scope.

Notation "[` kf ]" := (FSetSub kf) (format "[`  kf ]") : fset_scope.

Lemma fsetsubE (T : choiceType) (A : {fset T}) (x : A) (xA : val x \in A) :
 [` xA] = x.
Proof.
by apply/val_inj => /=.
Qed.

Notation "#|` A |" := (size (enum_fset A))
  (at level 0, A at level 99, format "#|`  A |") : nat_scope.
Definition fset_predT {T : choiceType} {A : {fset T}} : simpl_pred A := @predT A.
Definition set_of_fset (K : choiceType) (A : {fset K}) : {set A} :=
  [set x in {: A}].

Arguments pred_of_finset : simpl never.

Section SeqFset.

Variable finset_key : unit.
Definition seq_fset : forall K : choiceType, seq K -> {fset K} :=
   locked_with finset_key (fun K s => mkFinSet (@canonical_sort_keys K s)).

Variable (K : choiceType) (s : seq K).

Lemma seq_fsetE : seq_fset s =i s.
Proof.
by move=> a; rewrite [seq_fset]unlock sort_keysE.
Qed.

Lemma size_seq_fset : size (seq_fset s) = size (undup s).
Proof.
by rewrite [seq_fset]unlock /= size_sort_keys.
Qed.

Lemma seq_fset_uniq  : uniq (seq_fset s).
Proof.
by rewrite [seq_fset]unlock /= sort_keys_uniq.
Qed.

Lemma seq_fset_perm : perm_eq (seq_fset s) (undup s).
Proof.
by rewrite [seq_fset]unlock //= sort_keys_perm.
Qed.

End SeqFset.

#[global] Hint Resolve keys_canonical sort_keys_uniq : core.

Canonical  finSetSubType K := [subType for (@enum_fset K)].
Definition finSetEqMixin (K : choiceType) := [eqMixin of {fset K} by <:].
Canonical  finSetEqType  (K : choiceType) := EqType {fset K} (finSetEqMixin K).
Definition finSetChoiceMixin (K : choiceType) := [choiceMixin of {fset K} by <:].
Canonical  finSetChoiceType  (K : choiceType) := ChoiceType {fset K} (finSetChoiceMixin K).

Section FinPredStruct.

Structure finpredType (T : eqType) := FinPredType {
  finpred_sort :> Type;
  tofinpred : finpred_sort -> pred T;
  _ : {finpred_seq : finpred_sort -> seq T |
       ((forall p, uniq (finpred_seq p))
       * forall p x, x \in finpred_seq p = tofinpred p x)%type}
}.

Canonical finpredType_predType (T : eqType) (fpT : finpredType T) :=
  @PredType T (finpred_sort fpT) (@tofinpred T fpT).

Definition enum_finpred  (T : eqType) (fpT : finpredType T) :
    fpT -> seq T :=
  let: FinPredType _ _ (exist s _) := fpT in s.

Lemma enum_finpred_uniq (T : eqType) (fpT : finpredType T) (p : fpT) :
   uniq (enum_finpred p).
Proof.
by case: fpT p => ?? [s sE] p; rewrite sE.
Qed.

Lemma enum_finpredE (T : eqType) (fpT : finpredType T) (p : fpT) :
   enum_finpred p =i p.
Proof.
by case: fpT p => ?? [s sE] p x; rewrite sE -topredE.
Qed.

Lemma mkFinPredType_of_subproof (T : eqType) (pT : predType T)
   (fpred_seq : pT -> seq T) (pred_fsetE : forall p, fpred_seq p =i p) :
  forall p x, x \in fpred_seq p = topred p x.
Proof.
by move=> p x; rewrite topredE pred_fsetE.
Qed.

Definition mkFinPredType_of (T : eqType) (U : Type) :=
  fun (pT : predType T) & pred_sort pT -> U =>
  fun a (pT' := @PredType T U a) & phant_id pT' pT =>
  fun (fpred_seq : pT' -> seq T)
      (fpred_seq_uniq : forall p, uniq (fpred_seq p))
      (fpred_seqE : forall p, fpred_seq p =i p) =>
  @FinPredType T U a (exist _ fpred_seq
   (fpred_seq_uniq, (mkFinPredType_of_subproof fpred_seqE))).

Definition clone_finpredType (T : eqType) (U : Type) :=
  fun (pT : finpredType T) & finpred_sort pT -> U =>
  fun a pP (pT' := @FinPredType T U a pP) & phant_id pT' pT => pT'.

Structure is_finite (T : eqType) (P : pred T) := IsFinite {
  seq_of_is_finite :> seq T;
  _ : uniq seq_of_is_finite;
  _ : forall x, x \in seq_of_is_finite = P x;
}.

Lemma is_finite_uniq (T : eqType) (P : pred T) (p : is_finite P) : uniq p.
Proof.
by case: p.
Qed.

Lemma is_finiteE (T : eqType) (P : pred T) (p : is_finite P) x :
  x \in (seq_of_is_finite p) = P x.
Proof.
by case: p.
Qed.

Structure finpred (T : eqType) (pT : predType T) := FinPred {
  pred_of_finpred :> pT;
  _ : is_finite [pred x in pred_of_finpred]
}.

Definition enum_fin (T : eqType) (pT : predType T) (p : finpred pT) : seq T :=
  let: FinPred _ fp := p in fp.

Lemma enum_fin_uniq (T : eqType) (pT : predType T) (p : finpred pT) :
  uniq (enum_fin p).
Proof.
by case: p => ?[].
Qed.

Lemma enum_finE  (T : eqType) (pT : predType T) (p : finpred pT) :
  enum_fin p =i (pred_of_finpred p).
Proof.
by case: p => ?[].
Qed.

Canonical fin_finpred (T : eqType) (pT : finpredType T) (p : pT) :=
  @FinPred _ _ p (@IsFinite _ _ (enum_finpred p)
                            (enum_finpred_uniq p) (enum_finpredE p)).

Definition finpred_of (T : eqType) (pT : predType T) (p : pT)
 (fp : finpred pT) & phantom pT fp : finpred pT := fp.

Structure finmempred (T : eqType) := FinMemPred {
  pred_of_finmempred :> mem_pred T;
  _ : is_finite (fun x => in_mem x pred_of_finmempred)
}.

Definition enum_finmem (T : eqType) (p : finmempred T) : seq T :=
  let: FinMemPred _ fp := p in fp.

Lemma enum_finmem_uniq (T : eqType) (p : finmempred T) :
  uniq (enum_finmem p).
Proof.
by case: p => ?[].
Qed.

Lemma enum_finmemE  (T : eqType) (p : finmempred T) :
  enum_finmem p =i p.
Proof.
by case: p => ?[].
Qed.

Definition finmempred_of (T : eqType) (P : pred T)
 (mP : finmempred T) & phantom (mem_pred T) mP : finmempred T := mP.

Canonical mem_fin (T : eqType) (pT : predType T) (p : finpred pT) :=
  @FinMemPred  _ (mem p)
   (@IsFinite _ _ (enum_fin p) (enum_fin_uniq p) (enum_finE p)).

End FinPredStruct.

Notation "[ 'finpredType' 'of' T ]" := (@clone_finpredType _ T _ id _ _ id)
  (at level 0, format "[ 'finpredType'  'of'  T ]") : form_scope.

Notation mkFinPredType T s s_uniq sE :=
  (@mkFinPredType_of _ T _ id _ id s s_uniq sE).

Section CanonicalFinPred.

Canonical fset_finpredType (T: choiceType) :=
  mkFinPredType (finSet T) (@enum_fset T) (@fset_uniq T)  (fun _ _ => erefl).

Canonical pred_finpredType (T : finType) :=
  mkFinPredType (pred T) (fun P => enum_mem (mem P)) (@enum_uniq T) (@mem_enum T).

Canonical simpl_pred_finpredType (T : finType) :=
  mkFinPredType (simpl_pred T) (fun P => enum_mem (mem P)) (@enum_uniq T) (@mem_enum T).

Canonical fset_finpred (T: choiceType) (A : finSet T) :=
  @FinPred _ _ (enum_fset A)
     (@IsFinite _ _ (enum_fset A) (fset_uniq _) (fun=> erefl)).

Program Canonical subfinset_finpred (T : choiceType)
  (A : finmempred T) (Q : pred T) :=
  @FinPred _ _ [pred x in A | Q x]
          (@IsFinite _ _ [seq x <- enum_finmem A | Q x] _ _).
Admit Obligations.
Admit Obligations.

Canonical seq_finpredType (T : eqType) :=
  mkFinPredType (seq T) undup (@undup_uniq T) (@mem_undup T).

End CanonicalFinPred.

Local Notation imfset_def key :=
  (fun (T K : choiceType) (f : T -> K) (p : finmempred T)
       of phantom (mem_pred T) p => seq_fset key [seq f x | x <- enum_finmem p]).
Local Notation imfset2_def key :=
  (fun (K T1 : choiceType) (T2 : T1 -> choiceType)
       (f : forall x : T1, T2 x -> K)
       (p1 : finmempred T1) (p2 : forall x : T1, finmempred (T2 x))
   of phantom (mem_pred T1) p1 & phantom (forall x, mem_pred (T2 x)) p2 =>
  seq_fset key [seq f x y | x <- enum_finmem p1, y <- enum_finmem (p2 x)]).

Module Type ImfsetSig.
Parameter imfset : forall (key : unit) (T K : choiceType)
       (f : T -> K) (p : finmempred T),
  phantom (mem_pred T) p ->  {fset K}.
Parameter imfset2 : forall (key : unit) (K T1 : choiceType)
       (T2 : T1 -> choiceType)(f : forall x : T1, T2 x -> K)
       (p1 : finmempred T1) (p2 : forall x : T1, finmempred (T2 x)),
  phantom (mem_pred T1) p1 -> phantom (forall x, mem_pred (T2 x)) p2 -> {fset K}.
Axiom imfsetE : forall key, imfset key = imfset_def key.
Axiom imfset2E : forall key, imfset2 key = imfset2_def key.
End ImfsetSig.

Module Imfset : ImfsetSig.
Definition imfset key := imfset_def key.
Definition imfset2 key := imfset2_def key.
Lemma imfsetE key : imfset key = imfset_def key.
Proof.
by [].
Qed.
Lemma imfset2E key : imfset2 key = imfset2_def key.
Proof.
by [].
Qed.
End Imfset.

Notation imfset key f p :=
   (Imfset.imfset key f (Phantom _ (pred_of_finmempred p))).
Notation imfset2 key f p q :=
   (Imfset.imfset2 key f (Phantom _ (pred_of_finmempred p))
                   (Phantom _ (fun x => (pred_of_finmempred (q x))))).
Canonical imfset_unlock k := Unlockable (Imfset.imfsetE k).
Canonical imfset2_unlock k := Unlockable (Imfset.imfset2E k).

Notation "A `=` B" := (A = B :> {fset _}) (only parsing) : fset_scope.
Notation "A `<>` B" := (A <> B :> {fset _}) (only parsing) : fset_scope.
Notation "A `==` B" := (A == B :> {fset _}) (only parsing) : fset_scope.
Notation "A `!=` B" := (A != B :> {fset _}) (only parsing) : fset_scope.
Notation "A `=P` B" := (A =P B :> {fset _}) (only parsing) : fset_scope.

Notation "f @`[ key ] A" :=
  (Imfset.imfset key f (Phantom _ (mem A))) : fset_scope.
Notation "f @2`[ key ] ( A , B )" :=
   (Imfset.imfset2 key f (Phantom _ (mem A)) (Phantom _ (fun x => (mem (B x)))))
  : fset_scope.

Fact imfset_key : unit.
Proof.
exact: tt.
Qed.

Notation "f @` A" := (f @`[imfset_key] A) : fset_scope.
Notation "f @2` ( A , B )" := (f @2`[imfset_key] (A, B)) : fset_scope.

 
Notation "[ 'fset' E | x : T 'in' A ]" :=
  ((fun x : T => E) @` A) (only parsing) : fset_scope.
Notation "[ 'fset' E | x 'in' A ]" :=
  [fset E | x : _ in A] (only parsing) : fset_scope.
Notation "[ 'fset' E | x : A ]" :=
  [fset E | x : _ in {: A} ] (only parsing) : fset_scope.
Notation "[ 'fset'  x  :  T  'in'  A ]" :=
  [fset (x : T) | x in A] (only parsing) : fset_scope.
Notation "[ 'fset'  x  :  T  'in'  A  |  P ]" :=
  [fset (x : T) | x in [pred x in A | P]] (only parsing) : fset_scope.
Notation "[ 'fset' x 'in' A | P ]" :=
  [fset x : _ in A | P] (only parsing) : fset_scope.
Notation "[ 'fset' x 'in' A ]" :=
  [fset x : _ in A ] (only parsing) : fset_scope.
Notation "[ 'fset' x : T | P ]" :=
  [fset x in {: T} | P] (only parsing) : fset_scope.
Notation "[ 'fset' x : T | P & Q ]" :=
  [fset x : T | P && Q] (only parsing) : fset_scope.
Notation "[ 'fset'  x  :  T  'in' A  |  P  &  Q ]" :=
  [fset x : T in A | P && Q] (only parsing) : fset_scope.
Notation "[ 'fset' x 'in' A | P & Q ]" :=
  [fset x in A | P && Q] (only parsing) : fset_scope.

 
Notation "[ 'fset' E | x : T 'in' A , y : T' 'in' B ]" :=
  ((fun (x : T) (y : T') => E) @2` (A, fun x => B)) (only parsing) : fset_scope.
Notation "[ 'fset' E | x 'in' A , y 'in' B ]" :=
  [fset E | x : _ in A, y : _ in B] (only parsing) : fset_scope.

 
Notation "[ 'fset[' key ] E | x : T 'in' A ]" :=
  ((fun x : T => E) @`[key] A) (only parsing) : fset_scope.
Notation "[ 'fset[' key ] E | x 'in' A ]" :=
  [fset[key] E | x : _ in A] (only parsing) : fset_scope.
Notation "[ 'fset[' key ] E | x : A ]" :=
  [fset[key] E | x : _ in {: A} ] (only parsing) : fset_scope.
Notation "[ 'fset[' key ]  x  :  T  'in'  A ]" :=
  [fset[key] (x : T) | x in A] (only parsing) : fset_scope.
Notation "[ 'fset[' key ]  x  :  T  'in'  A  |  P ]" :=
  [fset[key] (x : T) | x in [pred x in A | P]] (only parsing) : fset_scope.
Notation "[ 'fset[' key ] x 'in' A | P ]" :=
  [fset[key] x : _ in A | P] (only parsing) : fset_scope.
Notation "[ 'fset[' key ] x 'in' A ]" :=
  [fset[key] x : _ in A ] (only parsing) : fset_scope.
Notation "[ 'fset[' key ] x : T | P ]" :=
  [fset[key] x in {: T} | P] (only parsing) : fset_scope.
Notation "[ 'fset[' key ] x : T | P & Q ]" :=
  [fset[key] x : T | P && Q] (only parsing) : fset_scope.
Notation "[ 'fset[' key ]  x  :  T  'in' A  |  P  &  Q ]" :=
  [fset[key] x : T in A | P && Q] (only parsing) : fset_scope.
Notation "[ 'fset[' key ] x 'in' A | P & Q ]" :=
  [fset[key] x in A | P && Q] (only parsing) : fset_scope.

Notation "[ 'fset[' key ] E | x : T 'in' A , y : T' 'in' B ]" :=
  ((fun (x : T) (y : T') => E) @2` (A, fun x => B))
  (only parsing) : fset_scope.
Notation "[ 'fset[' key ] E | x 'in' A , y 'in' B ]" :=
  [fset[key] E | x : _ in A, y : _ in B] (only parsing) : fset_scope.
Notation "[ 'fset[' key ] E | x : A , y : B ]" :=
  [fset[key] E | x : _ in {: A}, y : _ in {: B}] (only parsing) : fset_scope.

 
Notation "[ 'f' 'set' E | x 'in' A ]" := [fset[_] E | x in A] : fset_scope.
Notation "[ 'f' 'set' E | x : A ]" := [fset[_] E | x : A] : fset_scope.
Notation "[ 'f' 'set' x 'in' A | P ]" := [fset[_] x in A | P] : fset_scope.
Notation "[ 'f' 'set' x 'in' A ]" := [fset[_] x in A] : fset_scope.
Notation "[ 'f' 'set' x : T | P ]" := [fset[_] x : T | P] : fset_scope.
Notation "[ 'f' 'set' x : T | P & Q ]" := [fset[_] x : T | P & Q] : fset_scope.
Notation "[ 'f' 'set' x 'in' A | P & Q ]" :=
  [fset[_] x in A | P & Q] : fset_scope.
 
Notation "[ 'f' 'set' E | x 'in' A , y 'in' B ]" :=
  [fset[_] E | x in A, y in B] : fset_scope.

Section Ops.

Context {K K': choiceType}.
Implicit Types (a b c : K) (A B C D : {fset K}) (E : {fset K'}) (s : seq K).

Definition fset0 : {fset K} :=
  @mkFinSet K [::] (introT eqP (@sort_keys_nil K)).
 

Fact fset1_key : unit.
Proof.
exact: tt.
Qed.
Definition fset1 a : {fset K} := [fset[fset1_key] x in [:: a]].

Fact fsetU_key : unit.
Proof.
exact: tt.
Qed.
Definition fsetU A B := [fset[fsetU_key] x in enum_fset A ++ enum_fset B].

Fact fsetI_key : unit.
Proof.
exact: tt.
Qed.
Definition fsetI A B := [fset[fsetI_key] x in A | x \in B].

Fact fsetD_key : unit.
Proof.
exact: tt.
Qed.
Definition fsetD A B := [fset[fsetD_key] x in A | x \notin B].

Fact fsetM_key : unit.
Proof.
exact: tt.
Qed.
Definition fsetM A E := [fset[fsetM_key] (x, y) | x : K in A, y : K' in E].

Definition fsubset A B := fsetI A B == A.

Definition fproper A B := fsubset A B && ~~ fsubset B A.

Definition fdisjoint A B := (fsetI A B == fset0).

End Ops.

Notation "[ 'fset' a ]" := (fset1 a) : fset_scope.
Notation "[ 'fset' a : T ]" := [fset (a : T)] : fset_scope.
Notation "A `|` B" := (fsetU A B) : fset_scope.
Notation "a |` A" := ([fset a] `|` A) : fset_scope.

 
Notation "[ 'fset' a1 ; a2 ; .. ; an ]" :=
  (fsetU .. (a1 |` [fset a2]) .. [fset an]) : fset_scope.
Notation "A `&` B" := (fsetI A B) : fset_scope.
Notation "A `*` B" := (fsetM A B) : fset_scope.
Notation "A `\` B" := (fsetD A B) : fset_scope.
Notation "A `\ a" := (A `\` [fset a]) : fset_scope.

Notation "A `<=` B" := (fsubset A B) : fset_scope.
Notation "A `<` B" := (fproper A B) : fset_scope.

Notation "[ 'disjoint' A & B ]" := (fdisjoint A B) : fset_scope.

 
Notation "[ 'fset' E | x 'in' A & P ]" :=
  [fset E | x in [pred x in A | P]] (only parsing) : fset_scope.
Notation "[ 'fset' E | x : A & P ]" :=
  [fset E | x in {: A} & P] (only parsing) : fset_scope.
Notation "[ 'fset' E | x : A , y 'in' B ]" :=
  [fset E | x in {: A}, y in B] (only parsing) : fset_scope.
Notation "[ 'fset' E | x 'in' A , y : B ]" :=
  [fset E | x in A, y in {: B}] (only parsing) : fset_scope.
Notation "[ 'fset' E | x : A , y : B ]" :=
  [fset E | x in {: A}, y in {: B}] (only parsing) : fset_scope.
Notation "[ 'fset' E | x 'in' A , y 'in' B & P ]" :=
  [fset E | x in A, y in [pred y in B | P]] (only parsing) : fset_scope.
Notation "[ 'fset' E | x : A , y 'in' B & P ]" :=
  [fset E | x in {: A}, y in B & P] (only parsing) : fset_scope.
Notation "[ 'fset' E | x 'in' A , y : B & P ]" :=
  [fset E | x in A, y in {: B} & P] (only parsing) : fset_scope.
Notation "[ 'fset' E | x : A , y : B & P ]" :=
  [fset E | x in {: A}, y in {: B} & P] (only parsing) : fset_scope.

Notation "[ 'fsetval' x 'in' A ]" :=
  [fset val x | x in A] (only parsing) : fset_scope.
Notation "[ 'fsetval' x 'in' A | P ]" :=
  [fset val x | x in A & P] (only parsing) : fset_scope.
Notation "[ 'fsetval' x 'in' A | P & Q ]" :=
  [fsetval x in A | (P && Q)] (only parsing) : fset_scope.
Notation "[ 'fsetval' x : A ]" :=
  [fset val x | x in {: A}] (only parsing) : fset_scope.
Notation "[ 'fsetval' x : A | P ]" :=
  [fset val x | x in {: A} & P] (only parsing) : fset_scope.
Notation "[ 'fsetval' x : A | P & Q ]" :=
  [fsetval x in {: A} | (P && Q)] (only parsing) : fset_scope.

 
Notation "[ 'fset[' key ] E | x 'in' A & P ]" :=
  [fset[key] E | x in [pred x in A | P]] (only parsing) : fset_scope.
Notation "[ 'fset[' key ] E | x : A & P ]" :=
  [fset[key] E | x in {: A} & P] (only parsing) : fset_scope.
Notation "[ 'fset[' key ] E | x : A , y 'in' B ]" :=
  [fset[key] E | x in {: A}, y in B] (only parsing) : fset_scope.
Notation "[ 'fset[' key ] E | x 'in' A , y : B ]" :=
  [fset[key] E | x in A, y in {: B}] (only parsing) : fset_scope.
Notation "[ 'fset[' key ] E | x : A , y : B ]" :=
  [fset[key] E | x in {: A}, y in {: B}] (only parsing) : fset_scope.
Notation "[ 'fset[' key ] E | x 'in' A , y 'in' B & P ]" :=
  [fset[key] E | x in A, y in [pred y in B | P]] (only parsing) : fset_scope.
Notation "[ 'fset[' key ] E | x : A , y 'in' B & P ]" :=
  [fset[key] E | x in {: A}, y in B & P] (only parsing) : fset_scope.
Notation "[ 'fset[' key ] E | x 'in' A , y : B & P ]" :=
  [fset[key] E | x in A, y in {: B} & P] (only parsing) : fset_scope.
Notation "[ 'fset[' key ] E | x : A , y : B & P ]" :=
  [fset[key] E | x in {: A}, y in {: B} & P] (only parsing) : fset_scope.

Notation "[ 'fsetval[' key ] x 'in' A ]" :=
  [fset[key] val x | x in A] (only parsing) : fset_scope.
Notation "[ 'fsetval[' key ] x 'in' A | P ]" :=
  [fset[key] val x | x in A & P] (only parsing) : fset_scope.
Notation "[ 'fsetval[' key ] x 'in' A | P & Q ]" :=
  [fsetval[key] x in A | (P && Q)] (only parsing) : fset_scope.
Notation "[ 'fsetval[' key ] x : A ]" :=
  [fset[key] val x | x in {: A}] (only parsing) : fset_scope.
Notation "[ 'fsetval[' key ] x : A | P ]" :=
  [fset[key] val x | x in {: A} & P] (only parsing) : fset_scope.
Notation "[ 'fsetval[' key ] x : A | P & Q ]" :=
  [fsetval[key] x in {: A} | (P && Q)] (only parsing) : fset_scope.

 
  Notation "[ 'f' 'set' E | x 'in' A & P ]" :=
  [fset[_] E | x in A & P] : fset_scope.
Notation "[ 'f' 'set' E | x : A & P ]" := [fset[_] E | x : A & P] : fset_scope.
Notation "[ 'f' 'set' E | x : A , y 'in' B ]" :=
  [fset[_] E | x : A, y in B] : fset_scope.
Notation "[ 'f' 'set' E | x 'in' A , y : B ]" :=
  [fset[_] E | x in A, y : B] : fset_scope.
Notation "[ 'f' 'set' E | x : A , y : B ]" :=
  [fset[_] E | x : A, y : B] : fset_scope.
Notation "[ 'f' 'set' E | x 'in' A , y 'in' B & P ]" :=
  [fset[_] E | x in A, y in B & P] : fset_scope.
Notation "[ 'f' 'set' E | x : A , y 'in' B & P ]" :=
  [fset[_] E | x : A, y in B & P] : fset_scope.
Notation "[ 'f' 'set' E | x 'in' A , y : B & P ]" :=
  [fset[_] E | x in A, y : B & P] : fset_scope.
Notation "[ 'f' 'set' E | x : A , y : B & P ]" :=
  [fset[_] E | x : A, y : B & P] : fset_scope.

Notation "[ 'f' 'setval' x 'in' A ]" := [fset[_] val x | x in A] : fset_scope.
Notation "[ 'f' 'setval' x 'in' A | P ]" :=
  [fset[_] val x | x in A & P] : fset_scope.
Notation "[ 'f' 'setval' x 'in' A | P & Q ]" :=
  [fsetval[_] x in A | (P && Q)] : fset_scope.
Notation "[ 'f' 'setval' x : A ]" := [fsetval[_] x : A] : fset_scope.
Notation "[ 'f' 'setval' x : A | P ]" := [fsetval[_] x : A | P] : fset_scope.
Notation "[ 'f' 'setval' x : A | P & Q ]" :=
  [fsetval[_] x : A | (P && Q)] : fset_scope.

Section imfset.

Variables (key : unit) (K : choiceType).
Implicit Types (A B : {fset K}).

Lemma imfsetP (T : choiceType) (f : T -> K) (p : finmempred T) (k : K) :
  reflect (exists2 x : T, in_mem x p & k = f x) (k \in imfset key f p).
Proof.
rewrite unlock seq_fsetE /=; apply: (iffP mapP) => [] [x xp eqkf];
by exists x => //=; move: xp; rewrite enum_finmemE.
Qed.

Lemma in_imfset (T : choiceType) (f : T -> K) (p : finmempred T) (x : T) :
   in_mem x p -> f x \in imfset key f p.
Proof.
by move=> px; apply/imfsetP; exists x.
Qed.

Lemma imfset_rec (T : choiceType) (f : T -> K) (p : finmempred T)
  (P : imfset key f p -> Prop) :
  (forall (x : T) (px : in_mem x p), P [` in_imfset f px ]) -> forall k, P k.
Proof.
move=> PP v; have /imfsetP [k pk vv_eq] := valP v.
pose vP := in_imfset f pk; suff -> : P v = P [` vP] by apply: PP.
by congr P; apply/val_inj => /=; rewrite vv_eq.
Qed.

Lemma mem_imfset (T : choiceType) (f : T -> K) (p : finmempred T) :
  injective f -> forall (x : T), (f x \in imfset key f p) = (in_mem x p).
Proof.
by move=> f_inj x; rewrite unlock seq_fsetE mem_map// enum_finmemE.
Qed.

Lemma imfset2P (T1 : choiceType) (T2 : T1 -> choiceType)
      (f : forall x, T2 x -> K) (p1 : finmempred T1)
      (p2 : forall x, finmempred (T2 x)) k :
  reflect (exists2 x : T1, in_mem x p1
         & exists2 y : T2 x, in_mem y (p2 x) & k = f x y)
          (k \in imfset2 key f p1 p2).
Proof.
rewrite unlock !seq_fsetE; apply: (iffP allpairsPdep).
  move=> [x [y]]; rewrite !enum_finmemE => -[xp yp ->].
  by exists x => //; exists y.
by move=> [x xp [y yp ->]]; exists x, y; rewrite ?enum_finmemE.
Qed.

Lemma in_imfset2  (T1 : choiceType) (T2 : T1 -> choiceType)
      (f : forall x, T2 x -> K) (p1 : finmempred T1)
      (p2 : forall x, finmempred (T2 x)) (x : T1) (y : T2 x) :
   in_mem x p1 -> in_mem y (p2 x) -> f x y \in imfset2 key f p1 p2.
Proof.
by move=> xD1 yD2; apply/imfset2P; exists x => //; exists y.
Qed.

Lemma mem_imfset2 (T1 : choiceType) (T2 : T1 -> choiceType)
    (f : forall x, T2 x -> K)
    (g := fun t : {x : T1 & T2 x} => f (tag t) (tagged t))
    (p1 : finmempred T1)
    (p2 : forall x, finmempred (T2 x)) (x : T1) (y : T2 x) :
   injective g ->
   f x y \in imfset2 key f p1 p2 = (in_mem x p1) && (in_mem y (p2 x)).
Proof.
move=> f_inj; rewrite unlock seq_fsetE.
apply/allpairsPdep/idP => [[t1 [t2]]|]; last first.
  by move=> /andP[xp1 xp2]; exists x, y; rewrite ?enum_finmemE.
rewrite !enum_finmemE => -[pt1 pt2]; elim/(TaggedP T2): _ / t2 => t in pt1 pt2 *.
by elim/(TaggedP T2): _ / y => ? /f_inj->; apply/andP.
Qed.

Lemma enum_imfset (T : choiceType) (f : T -> K) (p : finmempred T) :
   {in p &, injective f} ->
   perm_eq (imfset key f p) [seq f x | x <- enum_finmem p].
Proof.
move=> f_inj; rewrite unlock -[X in perm_eq _ X]undup_id ?seq_fset_perm//.
rewrite map_inj_in_uniq ?enum_finmem_uniq // => ??.
by rewrite ?enum_finmemE; apply: f_inj.
Qed.

Lemma enum_imfset2  (T1 : choiceType) (T2 : T1 -> choiceType)
      (f : forall x, T2 x -> K) (p1 : finmempred T1)
      (p2 : forall x, finmempred (T2 x)) :
   {in  [pred t | p1 (tag t) & p2 _ (tagged t)] &,
        injective (fun t : sigT T2 => f (tag t) (tagged t))} ->
   perm_eq (imfset2 key f p1 p2)
           [seq f x y | x <- enum_finmem p1, y <- enum_finmem (p2 x)].
Proof.
move=> f_inj; rewrite unlock.
apply: uniq_perm => [||i]; rewrite ?seq_fset_uniq ?seq_fsetE //.
rewrite allpairs_uniq_dep ?enum_finmem_uniq//.
  by move=> x; rewrite enum_finmem_uniq.
move=> t0 t0' /allpairsPdep[t1 [t2]]; rewrite !enum_finmemE => -[tp1 tp2 ->/=].
move=> /allpairsPdep[t1' [t2']]; rewrite !enum_finmemE => -[t'p1 t'p2 ->/=].
by apply: (f_inj (Tagged _ _) (Tagged _ _)); rewrite ?inE/=; apply/andP.
Qed.

End imfset.

Section in_imfset.

Variable (key : unit) (K : choiceType).
Implicit Types (A B : {fset K}) (a b : K).

Lemma in_fset (p : finmempred K) (k : K) : (k \in imfset key id p) = in_mem k p.
Proof.
by rewrite mem_imfset; apply: inj_id.
Qed.

Lemma val_in_fset A (p : finmempred _) (k : A) :
   (val k \in imfset key val p) = (in_mem k p).
Proof.
by rewrite mem_imfset ?in_finmempred //; exact: val_inj.
Qed.

Lemma in_fset_val A (p : finmempred [eqType of A]) (k : K) :
  (k \in imfset key val p) = if insub k is Some a then in_mem a p else false.
Proof.
have [a _ <- /=|kNA] := insubP; first by rewrite val_in_fset.
by apply/imfsetP => [] [a _ k_def]; move: kNA; rewrite k_def [_ \in _]valP.
Qed.

Lemma in_fset_valT A (p : finmempred _) (k : K) (kA : k \in A) :
  (k \in imfset key val p) = in_mem [` kA] p.
Admitted.

Lemma in_fset_valP A (p : finmempred _) (k : K) :
  reflect {kA : k \in A & in_mem [` kA] p} (k \in imfset key val p).
Admitted.

Lemma in_fset_valF A (p : finmempred [eqType of A]) (k : K) : k \notin A ->
  (k \in imfset key val p) = false.
Admitted.

Lemma in_fset_nil a : a \in [fset[key] x in [::]] = false.
Admitted.

Lemma in_fset_cons x (xs : seq K) a :
  (a \in [fset[key] x in x :: xs]) = ((a == x) || (a \in [fset[key] x in xs])).
Admitted.

Lemma in_fset_cat (xs ys : seq K) a :
  (a \in [fset[key] x in xs ++ ys]) =
  ((a \in [fset[key] x in xs]) || (a \in [fset[key] x in ys])).
Admitted.

Definition in_fset_ (key : unit) :=
  (in_fset_cons, in_fset_nil, in_fset_cat, in_fset).

Lemma card_in_imfset (T T' : choiceType) (f : T -> T') (p : finmempred T) :
   {in p &, injective f} -> #|` (imfset key f p)| = (size (enum_finmem p)).
Admitted.

Lemma card_imfset (T T' : choiceType) (f : T -> T') (p : finmempred _) :
  injective f -> #|` (imfset key f p)| = size (enum_finmem p).
Admitted.

Lemma leq_imfset_card (T T' : choiceType) (f : T -> T') (p : finmempred _) :
   (#|` imfset key f p| <= size (enum_finmem p))%N.
Admitted.

End in_imfset.

Section Theory.

Variables (key : unit) (K K': choiceType).
Implicit Types (a b x : K) (A B C D : {fset K}) (E : {fset K'})
         (pA pB pC : pred K) (s : seq K).

Lemma fsetP {A B} : A =i B <-> A = B.
Proof.
by split=> [eqAB|-> //]; apply/val_inj/canonical_eq_keys => //= a.
Qed.

Variant in_fset_spec (A : {fset K}) (x : K) : K -> bool -> Prop :=
 | InFset (u : A) & x = val u : in_fset_spec A x (val u) true
 | OutFset of x \notin A : in_fset_spec A x x false.

Lemma in_fsetP A x : in_fset_spec A x x (x \in A).
Admitted.

Lemma fset_eqP {A B} : reflect (A =i B) (A == B).
Proof.
exact: (equivP eqP (iff_sym fsetP)).
Qed.

Lemma in_fset0 x : x \in fset0 = false.
Proof.
by [].
Qed.

Lemma in_fset1 a' a : a \in [fset a'] = (a == a').
Proof.
by rewrite !in_fset_ orbF.
Qed.

Lemma in_fsetU A B a : (a \in A `|` B) = (a \in A) || (a \in B).
Proof.
by rewrite !in_fset_.
Qed.

Lemma in_fset1U a' A a : (a \in a' |` A) = (a == a') || (a \in A).
Admitted.

Lemma in_fsetI A B a : (a \in A `&` B) = (a \in A) && (a \in B).
Proof.
by rewrite in_fset.
Qed.

Lemma in_fsetD A B a : (a \in A `\` B) = (a \notin B) && (a \in A).
Proof.
by rewrite in_fset andbC.
Qed.

Lemma in_fsetD1 A b a : (a \in A `\ b) = (a != b) && (a \in A).
Admitted.

Lemma in_fsetM A E (u : K * K') : (u \in A `*` E) = (u.1 \in A) && (u.2 \in E).
Admitted.

Definition in_fsetE :=
  (@in_fset_ imfset_key,
   val_in_fset, in_fset0, in_fset1,
   in_fsetU, in_fsetI, in_fsetD, in_fsetM,
   in_fset1U, in_fsetD1).

Let inE := (inE, in_fsetE).

Lemma fsetIC (A B : {fset K}) : A `&` B = B `&` A.
Admitted.

Lemma fsetUC (A B : {fset K}) : A `|` B = B `|` A.
Proof.
by apply/fsetP => a; rewrite !inE orbC.
Qed.

Lemma fset0I A : fset0 `&` A = fset0.
Admitted.

Lemma fsetI0 A : A `&` fset0 = fset0.
Admitted.

Lemma fsetIA A B C : A `&` (B `&` C) = A `&` B `&` C.
Admitted.

Lemma fsetICA A B C : A `&` (B `&` C) = B `&` (A `&` C).
Admitted.

Lemma fsetIAC A B C : A `&` B `&` C = A `&` C `&` B.
Admitted.

Lemma fsetIACA A B C D : (A `&` B) `&` (C `&` D) = (A `&` C) `&` (B `&` D).
Admitted.

Lemma fsetIid A : A `&` A = A.
Admitted.

Lemma fsetIIl A B C : A `&` B `&` C = (A `&` C) `&` (B `&` C).
Admitted.

Lemma fsetIIr A B C : A `&` (B `&` C) = (A `&` B) `&` (A `&` C).
Admitted.

Lemma fsetUA A B C : A `|` (B `|` C) = A `|` B `|` C.
Proof.
by apply/fsetP => x; rewrite !inE orbA.
Qed.

Lemma fsetUCA A B C : A `|` (B `|` C) = B `|` (A `|` C).
Admitted.

Lemma fsetUAC A B C : A `|` B `|` C = A `|` C `|` B.
Admitted.

Lemma fsetUACA A B C D : (A `|` B) `|` (C `|` D) = (A `|` C) `|` (B `|` D).
Admitted.

Lemma fsetUid A : A `|` A = A.
Admitted.

Lemma fsetUUl A B C : A `|` B `|` C = (A `|` C) `|` (B `|` C).
Admitted.

Lemma fsetUUr A B C : A `|` (B `|` C) = (A `|` B) `|` (A `|` C).
Admitted.

 

Lemma fsetIUr A B C : A `&` (B `|` C) = (A `&` B) `|` (A `&` C).
Admitted.

Lemma fsetIUl A B C : (A `|` B) `&` C = (A `&` C) `|` (B `&` C).
Admitted.

Lemma fsetUIr A B C : A `|` (B `&` C) = (A `|` B) `&` (A `|` C).
Admitted.

Lemma fsetUIl A B C : (A `&` B) `|` C = (A `|` C) `&` (B `|` C).
Admitted.

Lemma fsetUKC A B : (A `|` B) `&` A = A.
Admitted.

Lemma fsetUK A B : (B `|` A) `&` A = A.
Admitted.

Lemma fsetKUC A B : A `&` (B `|` A) = A.
Admitted.

Lemma fsetKU A B : A `&` (A `|` B) = A.
Admitted.

Lemma fsetIKC A B : (A `&` B) `|` A = A.
Admitted.

Lemma fsetIK A B : (B `&` A) `|` A = A.
Admitted.

Lemma fsetKIC A B : A `|` (B `&` A) = A.
Admitted.

Lemma fsetKI A B : A `|` (A `&` B) = A.
Admitted.

Lemma fsetUKid A B : B `|` A `|` A = B `|` A.
Admitted.

Lemma fsetUKidC A B : A `|` B `|` A = A `|` B.
Admitted.

Lemma fsetKUid A B : A `|` (A `|` B) = A `|` B.
Admitted.

Lemma fsetKUidC A B : A `|` (B `|` A) = B `|` A.
Admitted.

Lemma fsetIKid A B : B `&` A `&` A = B `&` A.
Admitted.

Lemma fsetIKidC A B : A `&` B `&` A = A `&` B.
Admitted.

Lemma fsetKIid A B : A `&` (A `&` B) = A `&` B.
Admitted.

Lemma fsetKIidC A B : A `&` (B `&` A) = B `&` A.
Admitted.

 

Lemma fsubsetP {A B} : reflect {subset A <= B} (A `<=` B).
Proof.
apply: (iffP fset_eqP) => AsubB a; first by rewrite -AsubB inE => /andP[].
by rewrite inE; have [/AsubB|] := boolP (a \in A).
Qed.

Lemma fset_sub_val A (p : finmempred [eqType of A]) :
  (imfset key val p) `<=` A.
Proof.
by apply/fsubsetP => k /in_fset_valP [].
Qed.

Lemma fset_sub A (P : pred K) : [fset x in A | P x] `<=` A.
Proof.
by apply/fsubsetP => k; rewrite in_fset inE /= => /andP [].
Qed.

Lemma fsetD_eq0 (A B : {fset K}) : (A `\` B == fset0) = (A `<=` B).
Admitted.

Lemma fsubset_refl A : A `<=` A.
Admitted.
Hint Resolve fsubset_refl : core.

Definition fincl A B (AsubB : A `<=` B) (a : A) : B :=
  [` (fsubsetP AsubB) _ (valP a)].

Definition fsub B A : {set B} := [set x : B | val x \in A].

Lemma fsubE A B (AsubB : A `<=` B) :
  fsub B A = [set fincl AsubB x | x : A].
Proof.
apply/setP => x; rewrite in_set; apply/idP/imsetP => [|[[a aA] aA' ->]] //.
by move=> xA; exists [` xA]=> //; apply: val_inj.
Qed.

Lemma fincl_fsub A B (AsubB : A `<=` B) (a : A) :
  fincl AsubB a \in fsub B A.
Admitted.

Lemma in_fsub B A (b : B) : (b \in fsub B A) = (val b \in A).
Admitted.

Lemma subset_fsubE C A B : A `<=` C -> B `<=` C ->
   (fsub C A \subset fsub C B) = (A `<=` B).
Admitted.

Lemma fsubset_trans : transitive (@fsubset K).
Admitted.

Lemma subset_fsub A B C : A `<=` B -> B `<=` C ->
  fsub C A \subset fsub C B.
Admitted.

Lemma fsetIidPl {A B} : reflect (A `&` B = A) (A `<=` B).
Admitted.

Lemma fsetIidPr {A B} : reflect (A `&` B = B) (B `<=` A).
Admitted.

Lemma fsubsetIidl A B : (A `<=` A `&` B) = (A `<=` B).
Admitted.

Lemma fsubsetIidr A B : (B `<=` A `&` B) = (B `<=` A).
Admitted.

Lemma fsetUidPr A B : reflect (A `|` B = B) (A `<=` B).
Admitted.

Lemma fsetUidPl A B : reflect (A `|` B = A) (B `<=` A).
Admitted.

Lemma fsubsetUl A B : A `<=` A `|` B.
Admitted.
Hint Resolve fsubsetUl : core.

Lemma fsubsetUr A B : B `<=` A `|` B.
Admitted.
Hint Resolve fsubsetUr : core.

Lemma fsubsetU1 x A : A `<=` x |` A.
Admitted.
Hint Resolve fsubsetU1 : core.

Lemma fsubsetU A B C : (A `<=` B) || (A `<=` C) -> A `<=` B `|` C.
Admitted.

Lemma fincl_inj A B (AsubB : A `<=` B) : injective (fincl AsubB).
Proof.
by move=> a b [eq_ab]; apply: val_inj.
Qed.
Hint Resolve fincl_inj : core.

Lemma fsub_inj B : {in [pred A | A `<=` B] &, injective (fsub B)}.
Admitted.
Hint Resolve fsub_inj : core.

Lemma eqEfsubset A B : (A == B) = (A `<=` B) && (B `<=` A).
Admitted.

Lemma subEfproper A B : A `<=` B = (A == B) || (A `<` B).
Admitted.

Lemma fproper_sub A B : A `<` B -> A `<=` B.
Admitted.

Lemma eqVfproper A B : A `<=` B -> A = B \/ A `<` B.
Admitted.

Lemma fproperEneq A B : A `<` B = (A != B) && (A `<=` B).
Admitted.

Lemma fproper_neq A B : A `<` B -> A != B.
Admitted.

Lemma fproper_irrefl A : ~~ (A `<` A).
Admitted.

Lemma eqEfproper A B : (A == B) = (A `<=` B) && ~~ (A `<` B).
Admitted.

Lemma card_fsub B A : A `<=` B -> #|fsub B A| = #|` A|.
Proof.
by move=> sAB; rewrite cardfE fsubE card_imset //; apply: fincl_inj.
Qed.

Lemma eqEfcard A B : (A == B) = (A `<=` B) &&
  (#|` B| <= #|` A|)%N.
Admitted.

Lemma fproperEcard A B :
  (A `<` B) = (A `<=` B) && (#|` A| < #|` B|)%N.
Admitted.

Lemma fsubset_leqif_cards A B : A `<=` B -> (#|` A| <= #|` B| ?= iff (A == B))%N.
Admitted.

Lemma fsub0set A : fset0 `<=` A.
Proof.
by apply/fsubsetP=> x; rewrite inE.
Qed.
Hint Resolve fsub0set : core.

Lemma fsubset0 A : (A `<=` fset0) = (A == fset0).
Admitted.

Lemma fproper0 A : (fset0 `<` A) = (A != fset0).
Admitted.

Lemma fproperE A B : (A `<` B) = (A `<=` B) && ~~ (B `<=` A).
Admitted.

Lemma fsubEproper A B : (A `<=` B) = (A == B) || (A `<` B).
Admitted.

Lemma fsubset_leq_card A B : A `<=` B -> (#|` A| <= #|` B|)%N.
Admitted.

Lemma fproper_ltn_card A B : A `<` B -> (#|` A| < #|` B|)%N.
Admitted.

Lemma fsubset_cardP A B : #|` A| = #|` B| ->
  reflect (A =i B) (A `<=` B).
Admitted.

Lemma fproper_sub_trans B A C : A `<` B -> B `<=` C -> A `<` C.
Admitted.

Lemma fsub_proper_trans B A C :
  A `<=` B -> B `<` C -> A `<` C.
Admitted.

Lemma fsubset_neq0 A B : A `<=` B -> A != fset0 -> B != fset0.
Admitted.

 

Lemma fsub0 A : fsub A fset0 = set0 :> {set A}.
Proof.
by apply/setP => x; rewrite !inE.
Qed.

Lemma fsubT A : fsub A A = [set : A].
Admitted.

Lemma fsub1 A a (aA : a \in A) : fsub A [fset a] = [set [` aA]] :> {set A}.
Admitted.

Lemma fsubU C A B : fsub C (A `|` B) = fsub C A :|: fsub C B.
Admitted.

Lemma fsubI C A B : fsub C (A `&` B) = fsub C A :&: fsub C B.
Admitted.

Lemma fsubD C A B : fsub C (A `\` B) = fsub C A :\: fsub C B.
Admitted.

Lemma fsubD1 C A b (bC : b \in C) : fsub C (A `\ b) = fsub C A :\ [` bC].
Admitted.

Lemma fsub_eq0 A B : A `<=` B -> (fsub B A == set0) = (A == fset0).
Admitted.

Lemma fset_0Vmem A : (A = fset0) + {x : K | x \in A}.
Admitted.

Lemma fset1P x a : reflect (x = a) (x \in [fset a]).
Admitted.

Lemma fset11 x : x \in [fset x].
Proof.
by rewrite inE.
Qed.

Lemma fset1_inj : injective (@fset1 K).
Admitted.

Lemma fset1UP x a B : reflect (x = a \/ x \in B) (x \in a |` B).
Admitted.

Lemma fset_cons a s : [fset[key] x in a :: s] = a |` [fset[key] x in s].
Admitted.

Lemma fset_nil : [fset[key] x in [::] : seq K] = fset0.
Admitted.

Lemma fset_cat s s' :
   [fset[key] x in s ++ s'] = [fset[key] x in s] `|` [fset[key] x in s'].
Admitted.

Lemma fset1U1 x B : x \in x |` B.
Admitted.

Lemma fset1Ur x a B : x \in B -> x \in a |` B.
Admitted.

 
 
Lemma fsetU1l x A b : x \in A -> x \in A `|` [fset b].
Admitted.

Lemma fsetU11 x B : x \in x |` B.
Admitted.

Lemma fsetU1r A b : b \in A `|` [fset b].
Admitted.

Lemma fsetD1P x A b : reflect (x != b /\ x \in A) (x \in A `\ b).
Admitted.

Lemma fsetD11 b A : (b \in A `\ b) = false.
Admitted.

Lemma fsetD1K a A : a \in A -> a |` (A `\ a) = A.
Admitted.

Lemma fsetU1K a B : a \notin B -> (a |` B) `\ a = B.
Admitted.

Lemma fset2P x a b : reflect (x = a \/ x = b) (x \in [fset a; b]).
Admitted.

Lemma in_fset2 x a b : (x \in [fset a; b]) = (x == a) || (x == b).
Admitted.

Lemma fset21 a b : a \in [fset a; b].
Admitted.

Lemma fset22 a b : b \in [fset a; b].
Admitted.

Lemma fsetUP x A B : reflect (x \in A \/ x \in B) (x \in A `|` B).
Admitted.

Lemma fsetULVR x A B : x \in A `|` B -> (x \in A) + (x \in B).
Proof.
by rewrite inE; case: (x \in A); [left|right].
Qed.

Lemma fsetUS A B C : A `<=` B -> C `|` A `<=` C `|` B.
Admitted.

Lemma fsetSU A B C : A `<=` B -> A `|` C `<=` B `|` C.
Admitted.

Lemma fsetUSS A B C D : A `<=` C -> B `<=` D -> A `|` B `<=` C `|` D.
Admitted.

Lemma fset0U A : fset0 `|` A = A.
Proof.
by apply/fsetP => x; rewrite !inE orFb.
Qed.

Lemma fsetU0 A : A `|` fset0 = A.
Proof.
by rewrite fsetUC fset0U.
Qed.

 

Lemma fsetIP x A B : reflect (x \in A /\ x \in B) (x \in A `&` B).
Admitted.

Lemma fsetIS A B C : A `<=` B -> C `&` A `<=` C `&` B.
Admitted.

Lemma fsetSI A B C : A `<=` B -> A `&` C `<=` B `&` C.
Admitted.

Lemma fsetISS A B C D : A `<=` C -> B `<=` D -> A `&` B `<=` C `&` D.
Admitted.

 

Lemma fsetDP A B x : reflect (x \in A /\ x \notin B) (x \in A `\` B).
Admitted.

Lemma fsetSD C A B : A `<=` B -> A `\` C `<=` B `\` C.
Admitted.

Lemma fsetDS C A B : A `<=` B -> C `\` B `<=` C `\` A.
Admitted.

Lemma fsetDSS A B C D : A `<=` C -> D `<=` B -> A `\` B `<=` C `\` D.
Admitted.

Lemma fsetD0 A : A `\` fset0 = A.
Admitted.

Lemma fset0D A : fset0 `\` A = fset0.
Admitted.

Lemma fsetDv A : A `\` A = fset0.
Admitted.

Lemma fsetID B A : A `&` B `|` A `\` B = A.
Admitted.

Lemma fsetDUl A B C : (A `|` B) `\` C = (A `\` C) `|` (B `\` C).
Admitted.

Lemma fsetDUr A B C : A `\` (B `|` C) = (A `\` B) `&` (A `\` C).
Admitted.

Lemma fsetDIl A B C : (A `&` B) `\` C = (A `\` C) `&` (B `\` C).
Admitted.

Lemma fsetIDA A B C : A `&` (B `\` C) = (A `&` B) `\` C.
Admitted.

Lemma fsetIDAC A B C : (A `\` B) `&` C = (A `&` C) `\` B.
Admitted.

Lemma fsetDIr A B C : A `\` (B `&` C) = (A `\` B) `|` (A `\` C).
Admitted.

Lemma fsetDDl A B C : (A `\` B) `\` C = A `\` (B `|` C).
Admitted.

Lemma fsetDDr A B C : A `\` (B `\` C) = (A `\` B) `|` (A `&` C).
Admitted.

Lemma fsetDK A B : B `<=` A -> A `\` (A `\` B) = B.
Admitted.

Lemma fsetUDl (A B C : {fset K}) : A `|` (B `\` C) = (A `|` B) `\` (C `\` A).
Admitted.

Lemma fsetUDr (A B C : {fset K}) : (A `\` B) `|` C = (A `|` C) `\` (B `\` C).
Admitted.

 

Lemma fsubsetIl A B : A `&` B `<=` A.
Admitted.

Lemma fsubsetIr A B : A `&` B `<=` B.
Admitted.

Lemma fsubsetDl A B : A `\` B `<=` A.
Proof.
by apply/fsubsetP=> x; rewrite inE => /andP [].
Qed.

Lemma fsubD1set A x : A `\ x `<=` A.
Admitted.

Lemma fsubsetD2l C A B : A `<=` C -> B `<=` C -> (C `\` B `<=` C `\` A) = (A `<=` B).
Admitted.

Hint Resolve fsubsetIl fsubsetIr fsubsetDl fsubD1set : core.

 

Lemma card_finset (T : finType) (P : pred T) : #|` [fset x in P] | = #|P|.
Admitted.

Lemma card_fset (T : choiceType) (A : {fset T}) : #|` [fset x in A] | = #|` A|.
Admitted.

Lemma card_fseq (T : choiceType) (s : seq T) : #|` [fset x in s] | = size (undup s).
Admitted.

Lemma cardfs0 : #|` @fset0 K| = 0.
Proof.
by rewrite -(@card_fsub fset0) // fsub0 cards0.
Qed.

Lemma cardfT0 : #|{: @fset0 K}| = 0.
Proof.
by rewrite -cardfE cardfs0.
Qed.

Lemma cardfs_eq0 A : (#|` A| == 0) = (A == fset0).
Admitted.

Lemma cardfs0_eq A : #|` A| = 0 -> A = fset0.
Admitted.

Lemma fset0Pn A : reflect (exists x, x \in A) (A != fset0).
Admitted.

Lemma cardfs_gt0 A : (0 < #|` A|)%N = (A != fset0).
Admitted.

Lemma cardfs1 x : #|` [fset x]| = 1.
Admitted.

Lemma cardfsUI A B : #|` A `|` B| + #|` A `&` B| = #|` A| + #|` B|.
Admitted.

Lemma cardfsU A B : #|` A `|` B| = (#|` A| + #|` B| - #|` A `&` B|)%N.
Admitted.

Lemma cardfsI A B : #|` A `&` B| = (#|` A| + #|` B| - #|` A `|` B|)%N.
Admitted.

Lemma cardfsID B A : #|` A `&` B| + #|` A `\` B| = #|` A|.
Admitted.

Lemma cardfsD A B : #|` A `\` B| = (#|` A| - #|` A `&` B|)%N.
Admitted.

Lemma mem_fset1U a A : a \in A -> a |` A = A.
Admitted.

Lemma mem_fsetD1 a A : a \notin A -> A `\ a = A.
Admitted.

Lemma fsetI1 a A : A `&` [fset a] = if a \in A then [fset a] else fset0.
Admitted.

Lemma cardfsU1 a A : #|` a |` A| = (a \notin A) + #|` A|.
Admitted.

Lemma cardfs2 a b : #|` [fset a; b]| = (a != b).+1.
Admitted.

Lemma cardfsD1 a A : #|` A| = (a \in A) + #|` A `\ a|.
Admitted.

 

Lemma fsub1set A x : ([fset x] `<=` A) = (x \in A).
Admitted.

Lemma cardfs1P A : reflect (exists x, A = [fset x]) (#|` A| == 1).
Admitted.

Lemma fsubset1 A x : (A `<=` [fset x]) = (A == [fset x]) || (A == fset0).
Admitted.

Arguments fsetIidPl {A B}.

Lemma cardfsDS A B : B `<=` A -> #|` A `\` B| = (#|` A| - #|` B|)%N.
Admitted.

Lemma fsubIset A B C : (B `<=` A) || (C `<=` A) -> (B `&` C `<=` A).
Admitted.

Lemma fsubsetI A B C : (A `<=` B `&` C) = (A `<=` B) && (A `<=` C).
Admitted.

Lemma fsubsetIP A B C : reflect (A `<=` B /\ A `<=` C) (A `<=` B `&` C).
Admitted.

Lemma fsubUset A B C : (B `|` C `<=` A) = (B `<=` A) && (C `<=` A).
Admitted.

Lemma fsubUsetP A B C : reflect (A `<=` C /\ B `<=` C) (A `|` B `<=` C).
Admitted.

Lemma fsubDset A B C : (A `\` B `<=` C) = (A `<=` B `|` C).
Admitted.

Lemma fsetU_eq0 A B : (A `|` B == fset0) = (A == fset0) && (B == fset0).
Admitted.

Lemma fsubsetD1 A B x : (A `<=` B `\ x) = (A `<=` B) && (x \notin A).
Admitted.

Lemma fsubsetD1P A B x : reflect (A `<=` B /\ x \notin A) (A `<=` B `\ x).
Admitted.

Lemma fsubsetPn A B : reflect (exists2 x, x \in A & x \notin B) (~~ (A `<=` B)).
Admitted.

Lemma fproperD1 A x : x \in A -> A `\ x `<` A.
Admitted.

Lemma fproperIr A B : ~~ (B `<=` A) -> A `&` B `<` B.
Admitted.

Lemma fproperIl A B : ~~ (A `<=` B) -> A `&` B `<` A.
Admitted.

Lemma fproperUr A B : ~~ (A `<=` B) ->  B `<` A `|` B.
Admitted.

Lemma fproperUl A B : ~~ (B `<=` A) ->  A `<` A `|` B.
Admitted.

Lemma fproper1set A x : ([fset x] `<` A) -> (x \in A).
Admitted.

Lemma fproperIset A B C : (B `<` A) || (C `<` A) -> (B `&` C `<` A).
Admitted.

Lemma fproperI A B C : (A `<` B `&` C) -> (A `<` B) && (A `<` C).
Admitted.

Lemma fproperU A B C : (B `|` C `<` A) -> (B `<` A) && (C `<` A).
Admitted.

Lemma fsetDpS C A B : B `<=` C ->  A `<` B -> C `\` B `<` C `\` A.
Admitted.

Lemma fproperD2l C A B : A `<=` C -> B `<=` C -> (C `\` B `<` C `\` A) = (A `<` B).
Admitted.

Lemma fsetI_eq0 A B : (A `&` B == fset0) = [disjoint A & B].
Admitted.

Lemma fdisjoint_sub {A B} : [disjoint A & B]%fset ->
  forall C : {fset K}, [disjoint fsub C A & fsub C B]%bool.
Admitted.

Lemma disjoint_fsub C A B : A `|` B `<=` C ->
  [disjoint fsub C A & fsub C B]%bool = [disjoint A & B].
Admitted.

Lemma fdisjointP {A B} :
  reflect (forall a, a \in A -> a \notin B) [disjoint A & B]%fset.
Admitted.

Lemma fsetDidPl A B : reflect (A `\` B = A) [disjoint A & B]%fset.
Admitted.

Lemma disjoint_fsetI0 A B : [disjoint A & B] -> A `&` B = fset0.
Admitted.

Lemma fsubsetD A B C :
  (A `<=` (B `\` C)) = (A `<=` B) && [disjoint A & C]%fset.
Admitted.

Lemma fsubsetDP A B C :
   reflect (A `<=` B /\ [disjoint A & C]%fset) (A `<=` (B `\` C)).
Admitted.

Lemma fdisjoint_sym A B : [disjoint A & B] = [disjoint B & A].
Admitted.

Lemma fdisjointP_sym {A B} :
  reflect (forall a, a \in A -> a \notin B) [disjoint B & A]%fset.
Admitted.

Lemma fdisjointWl A B C :
  A `<=` B -> [disjoint B & C] -> [disjoint A & C].
Admitted.
Notation fdisjoint_trans := fdisjointWl.

Lemma fdisjointWr A B C :
  A `<=` B -> [disjoint C & B] -> [disjoint C & A].
Admitted.

Lemma fdisjoint0X A : [disjoint fset0 & A].
Admitted.

Lemma fdisjointX0 A : [disjoint A & fset0].
Admitted.

Lemma fdisjoint1X x A : [disjoint [fset x] & A] = (x \notin A).
Admitted.

Lemma fdisjointX1 x A : [disjoint A & [fset x]] = (x \notin A).
Admitted.

Lemma fdisjointUX A B C :
   [disjoint A `|` B & C] = [disjoint A & C]%fset && [disjoint B & C]%fset.
Admitted.

Lemma fdisjointXU A B C :
   [disjoint A & B `|` C] = [disjoint A & B]%fset && [disjoint A & C]%fset.
Admitted.

Lemma fdisjointU1X x A B :
   [disjoint x |` A & B]%fset = (x \notin B) && [disjoint A & B]%fset.
Admitted.

Lemma fsubK A B : A `<=` B -> [fsetval k in fsub B A] = A.
Admitted.

Lemma FSetK A (X : {set A}) : fsub A [fsetval k in X] = X.
Admitted.

End Theory.
#[global] Hint Resolve fsubset_refl fsubset_trans : core.
#[global] Hint Resolve fproper_irrefl fsub0set : core.

Module Import FSetInE.
Definition inE := (inE, in_fsetE).
End FSetInE.

Section Enum.

Lemma enum_fset0 (T : choiceType) :
  enum [finType of fset0] = [::] :> seq (@fset0 T).
Admitted.

Lemma enum_fset1 (T : choiceType) (x : T) :
  enum [finType of [fset x]] = [:: [`fset11 x]].
Admitted.

End Enum.

Section ImfsetTh.
Variables (key : unit) (K V V' : choiceType).
Implicit Types (f : K -> V) (g : V -> V') (A V : {fset K}).

Lemma imfset_id (A : {fset K}) : id @` A = A.
Admitted.

Lemma imfset_comp f g (p : finmempred _) :
  imfset key (g \o f) p = g @` (imfset key f p).
Admitted.

Lemma subset_imfset f (p q : finmempred _) : {subset p <= q} ->
  imfset key f p `<=` imfset key f q.
Admitted.

Lemma eq_imfset (f f' : K -> V) (p q : finmempred _):
  f =1 f' -> (forall x, in_mem x p = in_mem x q) ->
  imfset key f p = imfset key f' q.
Admitted.

End ImfsetTh.

Section PowerSetTheory.
Variable (K : choiceType).

Fact fpowerset_key : unit.
Admitted.
Definition fpowerset (A : {fset K}) : {fset {fset K}} :=
  [fset[fpowerset_key] [fsetval y in Y : {set A}] | Y in powerset [set: A]].

Lemma fpowersetE A B : (B \in fpowerset A) = (B `<=` A).
Admitted.

Lemma fpowersetCE (X A B : {fset K}) :
 (A \in fpowerset (X `\` B)) = (A `<=` X) && [disjoint A & B]%fset.
Admitted.

Lemma fpowersetS A B : (fpowerset A `<=` fpowerset B) = (A `<=` B).
Admitted.

Lemma fpowerset0 : fpowerset fset0 = [fset fset0].
Admitted.

Lemma fpowerset1 (x : K) : fpowerset [fset x] = [fset fset0; [fset x]].
Admitted.

Lemma fpowersetI A B : fpowerset (A `&` B) = fpowerset A `&` fpowerset B.
Admitted.

Lemma card_fpowerset (A : {fset K}) : #|` fpowerset A| = 2 ^ #|` A|.
Admitted.

End PowerSetTheory.

Section FinTypeFset.
Variables (T : finType).

Definition pickle (s : {fset T}) :=
  [set x in s].

Definition unpickle (s : {set T}) :=
  [fset x | x in s]%fset.

Lemma pickleK : cancel pickle unpickle.
Admitted.

Lemma unpickleK : cancel unpickle pickle.
Admitted.

Definition fset_finMixin := CanFinMixin pickleK.
Canonical fset_finType := Eval hnf in FinType {fset T} fset_finMixin.

Lemma card_fsets : #|{:{fset T}}| = 2^#|T|.
Admitted.
End FinTypeFset.

Section BigFSet.
Variable (R : Type) (idx : R) (op : Monoid.law idx).
Variable (I : choiceType).

Lemma big_seq_fsetE (X : {fset I}) (P : pred I) (F : I -> R) :
  \big[op/idx]_(i <- X | P i) F i = \big[op/idx]_(x : X | P (val x)) F (val x).
Admitted.

Lemma big1_fset (X : {fset I}) (P : pred I) (F : I -> R) :
  (forall i, i \in X -> P i -> F i = idx) ->
  \big[op/idx]_(i <- X | P i) F i = idx.
Admitted.

Lemma big_fset0 (P : pred fset0) (F : @fset0 I -> R) :
  \big[op/idx]_(i : fset0 | P i) F i = idx.
Admitted.

Lemma big_seq_fset0 (F : I -> R): \big[op/idx]_(i <- fset0) F i = idx.
Admitted.

Lemma big_fset1 (a : I) (F : [fset a] -> R) :
  \big[op/idx]_(i : [fset a]) F i = F [` fset11 a].
Admitted.

Lemma big_seq_fset1 (a : I) (F : I -> R) :
  \big[op/idx]_(i <- [fset a]) F i = F a.
Admitted.

End BigFSet.

Notation eq_big_imfset := (perm_big _ (enum_imfset _ _)).

Section BigComFSet.
Variable (R : Type) (idx : R) (op : Monoid.com_law idx).
Variable (I J : choiceType).

Lemma big_fset (X : finmempred _) (P : pred I) (F : I -> R) :
  \big[op/idx]_(i <- [fset i in X | P i]) F i = \big[op/idx]_(i <- enum_finmem X | P i) F i.
Proof.
by rewrite !eq_big_imfset//= !big_map !big_filter_cond big_andbC.
Qed.

Lemma big_fset_condE (X : {fset I}) (P : pred I) (F : I -> R) :
  \big[op/idx]_(i <- X | P i) F i = \big[op/idx]_(i <- [fset i in X | P i]) F i.
Proof.
by rewrite big_fset.
Qed.

Lemma eq_fbig_cond (A B : {fset I}) (P Q : pred I) (F G : I -> R) :
  [fset x in A | P x] =i [fset x in B | Q x] ->
  (forall x, x \in A -> P x -> F x = G x) ->
  \big[op/idx]_(i <- A | P i) F i = \big[op/idx]_(i <- B | Q i) G i.
Proof.
move=> /fsetP eqABPQ FG; rewrite big_fset_condE [in RHS]big_fset_condE -eqABPQ.
rewrite big_seq_cond [in RHS]big_seq_cond; apply: eq_bigr => i.
by rewrite in_fset !inE => /andP[/andP[??] _]; apply: FG.
Qed.

Lemma eq_fbig (A B : {fset I}) (F G : I -> R) :
  A =i B -> (forall x, x \in A -> F x = G x) ->
  \big[op/idx]_(i <- A) F i = \big[op/idx]_(i <- B) G i.
Proof.
by move=> AB FG; apply: eq_fbig_cond => x; rewrite ?inE/= -?AB// => /FG.
Qed.

Lemma eq_fbigl_cond (A B : {fset I}) (P Q : pred I) (F : I -> R) :
  [fset x in A | P x] =i [fset x in B | Q x] ->
  \big[op/idx]_(i <- A | P i) F i = \big[op/idx]_(i <- B | Q i) F i.
Admitted.

Lemma eq_fbigl (A B : {fset I}) (F : I -> R) :
  A =i B -> \big[op/idx]_(i <- A) F i = \big[op/idx]_(i <- B) F i.
Proof.
by move=> AB; apply: eq_fbig.
Qed.

Lemma eq_fbigr (A : {fset I}) (P : pred I) (F G : I -> R) :
  (forall x, x \in A -> P x -> F x = G x) ->
  \big[op/idx]_(i <- A | P i) F i = \big[op/idx]_(i <- A | P i) G i.
Admitted.

Lemma big_fsetID  (B : pred I) (A : {fset I}) (F : I -> R) :
   \big[op/idx]_(i <- A) F i =
   op (\big[op/idx]_(i <- [fset x in A | B x]) F i)
      (\big[op/idx]_(i <- [fset x in A | ~~ B x]) F i).
Proof.
by rewrite !big_fset; apply: bigID.
Qed.

Lemma big_fsetIDcond (B : pred I) (A : {fset I}) (P : pred I) (F : I -> R) :
   \big[op/idx]_(i <- A | P i) F i =
   op (\big[op/idx]_(i <- [fset x in A | B x] | P i) F i)
      (\big[op/idx]_(i <- [fset x in A | ~~ B x] | P i) F i).
Admitted.

Lemma big_fsetD1 (a : I) (A : {fset I}) (F : I -> R) : a \in A ->
  \big[op/idx]_(i <- A) F i = op (F a) (\big[op/idx]_(i <- A `\ a) F i).
Proof.
move=> aA; rewrite (big_fsetID (mem [fset a])); congr (op _ _); last first.
  by apply: eq_fbigl=> i; rewrite !inE/= andbC.
rewrite (_ : [fset _ | _ in _ & _] = [fset a]) ?big_seq_fset1//=.
by apply/fsetP=> i; rewrite !inE /= andbC; case: eqP => //->.
Qed.

Lemma big_fsetU1 (a : I) (A : {fset I}) (F : I -> R) : a \notin A ->
   \big[op/idx]_(i <- (a |` A)) F i = op (F a) (\big[op/idx]_(i <- A) F i).
Admitted.

Lemma big_fset_incl (A : {fset I}) B F : A `<=` B ->
  (forall x, x \in B -> x \notin A -> F x = idx) ->
  \big[op/idx]_(x <- A) F x = \big[op/idx]_(x <- B) F x.
Admitted.

Lemma big_imfset key (h : I -> J) (A : finmempred _)
   (G : J -> R) : {in A &, injective h} ->
   \big[op/idx]_(j <- imfset key h A) G j =
   \big[op/idx]_(i <- enum_finmem A) G (h i).
Admitted.

End BigComFSet.
Arguments big_fsetD1 {R idx op I} a [A F].

Notation eq_big_imfset2 := (perm_big _ (enum_imfset2 _ _)).

Section BigComImfset2.
Variables (R : Type) (idx : R) (op : Monoid.com_law idx)
          (I : choiceType) (J : I -> choiceType) (K : choiceType).

Lemma big_imfset2 key (A : finmempred I) (B : forall i, finmempred (J i))
      (h : forall i : I, J i -> K) (F : K -> R) :
   {in  [pred t : {i : I & J i} | A (tag t) & B _ (tagged t)] &,
        injective (fun t => h (tag t) (tagged t))} ->
   \big[op/idx]_(k <- imfset2 key h A B) F k =
   \big[op/idx]_(i <- enum_finmem A)
     \big[op/idx]_(j <- enum_finmem (B i)) F (h i j).
Admitted.

End BigComImfset2.

Section BigFsetDep.
Variables (R : Type) (idx : R) (op : Monoid.com_law idx)
          (I : choiceType) (J : choiceType) (K : choiceType).

Lemma pair_big_dep_cond (A : {fset I}) (B : I -> {fset J})
      (P : pred I) (Q : I -> pred J) (F : I -> J -> R) :
   \big[op/idx]_(i <- A | P i) \big[op/idx]_(j <- B i | Q i j) F i j =
   \big[op/idx]_(p <- [fset ((i, j) : I * J) | i in [fset i in A | P i],
                             j in [fset j in B i | Q i j]]) F p.1 p.2.
Admitted.
End BigFsetDep.

Section BigComImfset.
Variables (R : Type) (idx : R) (op : Monoid.com_law idx)
          (I : choiceType) (J : choiceType) (K : choiceType).

Lemma partition_big_imfset (h : I -> J) (A : {fset I}) (F : I -> R) :
   \big[op/idx]_(i <- A) F i =
   \big[op/idx]_(j <- [fset h x | x in A]) \big[op/idx]_(i <- A | h i == j) F i.
Admitted.

End BigComImfset.

Notation "\bigcup_ ( i <- r | P ) F" :=
  (\big[@fsetU _/fset0]_(i <- r | P%fset) F%fset) : fset_scope.

Notation "\bigcup_ ( i <- r ) F" :=
  (\big[@fsetU _/fset0]_(i <- r) F%fset) : fset_scope.

Notation "\bigcup_ ( i | P ) F" :=
  (\big[@fsetU _/fset0]_(i | P) F%fset) : fset_scope.

Notation "\bigcup_ ( i 'in' A | P ) F" :=
  (\big[@fsetU _/fset0]_(i in A | P) F%fset) : fset_scope.

Notation "\bigcup_ ( i 'in' A ) F" :=
  (\big[@fsetU _/fset0]_(i in A) F%fset) : fset_scope.

Section FSetMonoids.

Import Monoid.
Variable (T : choiceType).

Canonical fsetU_monoid := Law (@fsetUA T) (@fset0U T) (@fsetU0 T).
Canonical fsetU_comoid := ComLaw (@fsetUC T).

End FSetMonoids.
Section BigFOpsSeq.

Variables (T : choiceType) (I : eqType) (r : seq I).
Implicit Types (P : pred I) (F :  I -> {fset T}).

Lemma bigfcup_undup P F :
   \bigcup_(i <- undup r | P i) F i = \bigcup_(i <- r | P i) F i.
Admitted.

Lemma bigfcup_sup j P F : j \in r -> P j -> F j `<=` \bigcup_(i <- r | P i) F i.
Admitted.

Lemma bigfcupP x F P :
  reflect (exists2 i : I, (i \in r) && P i & x \in F i)
          (x \in \bigcup_(i <- r | P i) F i).
Admitted.

Lemma bigfcupsP (U : {fset T}) P F :
  reflect (forall i : I, i \in r -> P i -> F i `<=` U)
          (\bigcup_(i <- r | P i) F i `<=` U).
Admitted.

End BigFOpsSeq.

Section FsetPartitions.

Variables T I : choiceType.
Implicit Types (x y z : T) (A B D X : {fset T}) (P Q : {fset {fset T}}).
Implicit Types (J : pred I) (F : I -> {fset T}).

Definition fcover P := (\bigcup_(B <- P) B)%fset.
Definition trivIfset P := (\sum_(B <- P) #|` B|)%N == #|` fcover P|.

Lemma leq_card_fsetU A B :
  ((#|` A `|` B|)%fset <= #|` A| + #|` B| ?= iff [disjoint A & B]%fset)%N.
Admitted.

Lemma leq_card_fcover P :
  ((#|` fcover P|)%fset <= \sum_(A <- P) #|`A| ?= iff trivIfset P)%N.
Admitted.

Lemma trivIfsetP P :
  reflect {in P &, forall A B, A != B -> [disjoint A & B]%fset} (trivIfset P).
Admitted.

Lemma fcover_imfset (J : {fset I}) F (P : pred I) :
  fcover [fset F i | i in J & P i]%fset = (\bigcup_(i <- J | P i) F i)%fset.
Admitted.

Section FsetBigOps.

Variables (R : Type) (idx : R) (op : Monoid.com_law idx).
Let rhs_cond P K E :=
  (\big[op/idx]_(A <- P) \big[op/idx]_(x <- A | K x) E x)%fset.
Let rhs P E := (\big[op/idx]_(A <- P) \big[op/idx]_(x <- A) E x)%fset.

Lemma big_trivIfset P (E : T -> R) :
  trivIfset P -> \big[op/idx]_(x <- fcover P) E x = rhs P E.
Admitted.

Lemma partition_disjoint_bigfcup (f : T -> R) (F : I -> {fset T})
  (K : {fset I}) :
  (forall i j, i != j -> [disjoint F i & F j])%fset ->
  \big[op/idx]_(i <- \big[fsetU/fset0]_(x <- K) (F x)) f i =
  \big[op/idx]_(k <- K) (\big[op/idx]_(i <- F k) f i).
Admitted.

End FsetBigOps.

End FsetPartitions.

 
Lemma finSet_rect (T : choiceType) (P : {fset T} -> Type) :
  (forall X, (forall Y, Y `<` X -> P Y) -> P X) -> forall X, P X.
Admitted.

Lemma fset_bounded_coind (T : choiceType) (P : {fset T} -> Type) (U : {fset T}):
  (forall X, (forall Y, Y `<=` U -> X `<` Y -> P Y) -> P X) ->
   forall X, X `<=` U -> P X.
Admitted.

Lemma iter_fix T n f (x : T) : f x = x -> iter n f x = x.
Admitted.

Section SetFixpoint.

Section Least.
Variables (T : finType) (F : {set T} -> {set T}).
Hypothesis (F_mono : {homo F : X Y / X \subset Y}).

Let n := #|T|.
Notation iterF := (fun i => iter i F set0).

Lemma set_iterF_sub i : iterF i \subset iterF i.+1.
Admitted.

Lemma set_iterF_mono : {homo iterF : i j / i <= j >-> i \subset j}.
Admitted.

Definition fixset := iterF n.

Lemma fixsetK : F fixset = fixset.
Admitted.
Hint Resolve fixsetK : core.

Lemma minset_fix : minset [pred X | F X == X] fixset.
Admitted.

Lemma fixsetKn k : iter k F fixset = fixset.
Admitted.

Lemma iter_sub_fix k : iterF k \subset fixset.
Admitted.

Lemma fix_order_proof x : x \in fixset -> exists n, x \in iterF n.
Proof.
by move=> x_fix; exists n.
Qed.

Definition fix_order (x : T) :=
 if (x \in fixset) =P true isn't ReflectT x_fix then 0
 else (ex_minn (fix_order_proof x_fix)).

Lemma fix_order_le_max (x : T) : fix_order x <= n.
Admitted.

Lemma in_iter_fix_orderE (x : T) :
  (x \in iterF (fix_order x)) = (x \in fixset).
Admitted.

Lemma fix_order_gt0 (x : T) : (fix_order x > 0) = (x \in fixset).
Admitted.

Lemma fix_order_eq0 (x : T) : (fix_order x == 0) = (x \notin fixset).
Admitted.

Lemma in_iter_fixE (x : T) k : (x \in iterF k) = (0 < fix_order x <= k).
Admitted.

Lemma in_iter (x : T) k : x \in fixset -> fix_order x <= k -> x \in iterF k.
Admitted.

Lemma notin_iter (x : T) k : k < fix_order x -> x \notin iterF k.
Admitted.

Lemma fix_order_small x k : x \in iterF k -> fix_order x <= k.
Admitted.

Lemma fix_order_big x k : x \in fixset -> x \notin iterF k -> fix_order x > k.
Admitted.

Lemma le_fix_order (x y : T) : y \in iterF (fix_order x) ->
  fix_order y <= fix_order x.
Admitted.

End Least.

Section Greatest.
Variables (T : finType) (F : {set T} -> {set T}).
Hypothesis (F_mono : {homo F : X Y / X \subset Y}).

Notation n := #|T|.
Definition funsetC X := ~: (F (~: X)).
Notation G := funsetC.
Lemma funsetC_mono : {homo G : X Y / X \subset Y}.
Admitted.
Hint Resolve funsetC_mono : core.

Definition cofixset := ~: fixset G.

Lemma cofixsetK : F cofixset = cofixset.
Admitted.

Lemma maxset_cofix : maxset [pred X | F X == X] cofixset.
Admitted.

End Greatest.

End SetFixpoint.

Section Fixpoints.
Variables (T : choiceType) (U : {fset T}).

Definition sub_fun (F : {fset T} -> {fset T}) (X : {set U}) : {set U} :=
  fsub U (F [fsetval x in X]).

Lemma fset_fsub X : X `<=` U -> [fsetval x in fsub U X] = X.
Admitted.

Variable (F : {fset T} -> {fset T}).
Hypothesis (F_mono : {homo F : X Y / X `<=` Y}).
Hypothesis (F_bound : {homo F : X / X `<=` U}).

Notation Fsub := (sub_fun F).
Notation iterF := (fun i => iter i F fset0).

Lemma Fsub_mono : {homo Fsub : X Y / X \subset Y}.
Admitted.
Hint Resolve Fsub_mono : core.

Definition fixfset := [fsetval x in fixset Fsub].

Lemma fset_iterFE i : iterF i = [fsetval x in iter i Fsub set0].
Admitted.

Lemma fset_iterF_sub i : iterF i `<=` U.
Admitted.

Lemma fixfsetK : F fixfset = fixfset.
Admitted.
Hint Resolve fixfsetK : core.

Lemma fixfsetKn k : iter k F fixfset = fixfset.
Admitted.

Lemma iter_sub_ffix k : iterF k `<=` fixfset.
Admitted.

Definition ffix_order (x : T) :=
 if x \in U =P true is ReflectT xU then fix_order Fsub [` xU] else 0.

Lemma ffix_order_le_max (x : T) : ffix_order x <= #|` U|.
Admitted.

Lemma in_iter_ffix_orderE (x : T) :
  (x \in iterF (ffix_order x)) = (x \in fixfset).
Admitted.

Lemma ffix_order_gt0 (x : T) : (ffix_order x > 0) = (x \in fixfset).
Admitted.

Lemma ffix_order_eq0 (x : T) : (ffix_order x == 0) = (x \notin fixfset).
Admitted.

Lemma in_iter_ffixE (x : T) k : (x \in iterF k) = (0 < ffix_order x <= k).
Admitted.

Lemma in_iter_ffix (x : T) k : x \in fixfset -> ffix_order x <= k ->
  x \in iterF k.
Admitted.

Lemma notin_iter_ffix (x : T) k : k < ffix_order x -> x \notin iterF k.
Admitted.

Lemma ffix_order_small x k : x \in iterF k -> ffix_order x <= k.
Admitted.

Lemma ffix_order_big x k : x \in fixfset -> x \notin iterF k ->
   ffix_order x > k.
Admitted.

Lemma le_ffix_order (x y : T) : y \in iterF (ffix_order x) ->
  ffix_order y <= ffix_order x.
Admitted.

End Fixpoints.

 
 
 

Section DefMap.
Variables (K : choiceType) (V : Type).

Record finMap : Type := FinMap {
  domf : {fset K};
  ffun_of_fmap :> {ffun domf -> V}
}.

Definition finmap_of (_ : phant (K -> V)) := finMap.

Let T_ (domf : {fset K}) :=  {ffun domf -> V}.
Local Notation finMap' := {domf : _ & T_ domf}.

End DefMap.

Notation "{fmap T }" := (@finmap_of _ _ (Phant T)) : type_scope.

Definition pred_of_finmap (K : choiceType) (V : Type)
  (f : {fmap K -> V}) : pred K := mem (domf f).
Canonical finMapPredType (K : choiceType) (V : Type) :=
  PredType (@pred_of_finmap K V).

Declare Scope fmap_scope.
Delimit Scope fmap_scope with fmap.
Local Open Scope fmap_scope.
Notation "f .[ kf ]" := (f [` kf]) : fmap_scope.
Arguments ffun_of_fmap : simpl never.

Notation "[ 'fmap' x : aT => F ]" := (FinMap [ffun x : aT => F])
  (at level 0, x name, only parsing) : fun_scope.

Notation "[ 'fmap' : aT => F ]" := (FinMap [ffun _ : aT => F])
  (at level 0, only parsing) : fun_scope.

Notation "[ 'fmap' x => F ]" := [fmap x : _ => F]
  (at level 0, x name, format "[ 'fmap'  x  =>  F ]") : fun_scope.

Notation "[ 'fmap' => F ]" := [fmap: _ => F]
  (at level 0, format "[ 'fmap' =>  F ]") : fun_scope.

Canonical finmap_of_finfun (K : choiceType) V (A : {fset K}) (f : {ffun A -> V}) := FinMap f.
Arguments finmap_of_finfun /.
Arguments ffun_of_fmap : simpl nomatch.

Section OpsMap.

Variables (K : choiceType).

Definition fmap0 V : {fmap K -> V} := FinMap (ffun0 (cardfT0 K)).

Definition fnd V (A : {fset K}) (f : {ffun A -> V}) (k : K) :=
  omap f (insub k).

Inductive fnd_spec V (A : {fset K}) (f : {ffun A -> V}) k :
  bool -> option A -> option V -> Type :=
| FndIn  (kf : k \in A) : fnd_spec f k true (some [` kf]) (some (f.[kf]))
| FndOut (kNf : k \notin A) : fnd_spec f k false None None.

Definition setf V (f : {fmap K -> V}) (k0 : K) (v0 : V) : {fmap K -> V} :=
  [fmap k : k0 |` domf f => if val k == k0 then v0
                            else odflt v0 (fnd f (val k))].

End OpsMap.

Prenex Implicits fnd setf.
Arguments fmap0 {K V}.
Arguments setf : simpl never.
Arguments fnd : simpl never.

Notation "[ 'fmap' 'of' T ]" := (fmap0 : {fmap T}) (only parsing) : fmap_scope.
Notation "[fmap]" := fmap0 : fmap_scope.
Notation "x .[ k <- v ]" := (setf x k v) : fmap_scope.
Notation "f .[? k ]" := (fnd f k) : fmap_scope.

Section FinMapCanonicals.

Section FinMapEncode.
Variable K : choiceType.

Let finMap_on (V : Type) (d : {fset K}) := {ffun d -> V}.
Local Notation finMap_ V := {d : _ & finMap_on V d}.

Definition finMap_encode V (f : {fmap K -> V}) := Tagged (finMap_on V) (ffun_of_fmap f).
Definition finMap_decode V (f : finMap_ V) := FinMap (tagged f).
Lemma finMap_codeK V : cancel (@finMap_encode V) (@finMap_decode V).
Admitted.

End FinMapEncode.

Section FinMapEqType.
Variable (K : choiceType) (V : eqType).

Definition finMap_eqMixin := CanEqMixin (@finMap_codeK K V).
Canonical finMap_eqType := EqType {fmap K -> V} finMap_eqMixin.

End FinMapEqType.

Section FinMapChoiceType.
Variable (K V : choiceType).

Definition finMap_choiceMixin := CanChoiceMixin (@finMap_codeK K V).
Canonical finMap_choiceType := ChoiceType {fmap K -> V} finMap_choiceMixin.

End FinMapChoiceType.

Section FinMapCountType.
Variable (K V : countType).

Definition finMap_countMixin := CanCountMixin (@finMap_codeK K V).
Canonical finMap_countType := CountType {fmap K -> V} finMap_countMixin.

End FinMapCountType.

End FinMapCanonicals.

Section FinMapTheory.
Variables (K : choiceType).

Lemma fndP V (f : {fmap K -> V}) k :
  fnd_spec f k (k \in domf f) (insub k) (f.[? k]).
Admitted.

Lemma fndSome V (f : {fmap K -> V}) (k : K) :
  f.[? k] = (k \in f) :> bool.
Admitted.

Lemma not_fnd V (f : {fmap K -> V}) (k : K) :
  k \notin f -> f.[? k] = None.
Admitted.

Lemma getfE V (f : {fmap K -> V}) (k : domf f)
      (kf : val k \in domf f) : f.[kf] = f k :> V.
Admitted.

Lemma eq_getf V (f : {fmap K -> V}) k (kf kf' : k \in domf f) :
  f.[kf] = f.[kf'] :> V.
Admitted.

Lemma Some_fnd V (f : {fmap K -> V}) (k : domf f) :
  Some (f k) = f.[? val k].
Admitted.

Lemma in_fnd V (f : {fmap K -> V}) (k : K)
      (kf : k \in domf f) : f.[? k] = Some f.[kf].
Admitted.

Lemma fnd_if V (cond : bool) (f g : {fmap K -> V}) (k : K) :
  ((if cond then f else g) : finMap _ _).[? k] =
  if cond then f.[? k] else g.[? k].
Admitted.

Lemma getfP V (f g : {fmap K -> V}) : domf f = domf g ->
  (forall k (kMf : k \in f) (kMg : k \in g), f.[kMf] = g.[kMg]) -> f = g.
Admitted.

Lemma fmapP V (f g : {fmap K -> V}) :
      (forall k, f.[? k] = g.[? k]) <-> f = g.
Admitted.

Lemma fnd_fmap0 V k : ([fmap] : {fmap K -> V}).[? k] = None.
Admitted.

Lemma mem_setf V (f : {fmap K -> V}) (k0 : K) (v0 : V) :
  f.[k0 <- v0] =i predU1 k0 (mem (domf f)).
Admitted.

Lemma dom_setf V (f : {fmap K -> V}) (k0 : K) (v0 : V) :
  domf (f.[k0 <- v0]) = k0 |` domf f.
Admitted.

Lemma fnd_set_in V (f : {fmap K -> V}) k0 v0 (x : domf f.[k0 <- v0]) :
  val x != k0 -> val x \in f.
Admitted.

Lemma setfK V (f : {fmap K -> V}) k0 v0 (x : domf f.[k0 <- v0]):
   f.[k0 <- v0] x = if (val x != k0) =P true isn't ReflectT xNk0 then v0
                    else f.[fnd_set_in xNk0].
Admitted.

Lemma fnd_set V (f : {fmap K -> V}) k0 v0 k :
   f.[k0 <- v0].[? k] = if k == k0 then Some v0 else f.[? k].
Admitted.

Lemma fmap_nil V (f : {fmap K -> V}) : domf f = fset0 -> f = [fmap].
Admitted.

Lemma getf_set V (f : {fmap K -> V}) (k : K) (v : V) (kf' : k \in _) :
   f.[k <- v].[kf'] = v.
Admitted.

Lemma setf_get V (f : {fmap K -> V}) (k : domf f) :
  f.[val k <- f k] = f.
Admitted.

Lemma setfNK V (f : {fmap K -> V}) (k k' : K) (v : V)
      (k'f : k' \in _) (k'f' : k' \in _):
   f.[k <- v].[k'f'] = if k' == k then v else f.[k'f].
Admitted.

Lemma domf0 V : domf [fmap of K -> V] = fset0.
Admitted.

End FinMapTheory.

Section ReduceOp.

Variable (K : choiceType) (V : Type).
Implicit Types (f : {fmap K -> option V}).

Lemma reducef_subproof f (x : [fsetval x : domf f | f x]) :
  f (fincl (fset_sub_val _ _) x).
Admitted.

Definition reducef f : {fmap K -> V} :=
  [fmap x => oextract (@reducef_subproof f x)].

Lemma domf_reduce f : domf (reducef f) = [fsetval x : domf f | f x].
Admitted.

Lemma mem_reducef f k : k \in reducef f = ojoin f.[? k].
Admitted.

Lemma fnd_reducef f k : (reducef f).[? k] = ojoin f.[? k].
Admitted.

Lemma get_reducef f k (krf : k \in reducef f) (kf : k \in f):
  Some (reducef f).[krf] = f.[kf].
Admitted.

End ReduceOp.

Arguments reducef : simpl never.

Section RestrictionOps.
Variable (K : choiceType) (V : Type).
Implicit Types (f g : {fmap K -> V}).

Definition filterf f (P : pred K) : {fmap K -> V} :=
   [fmap x : [fset x in domf f | P x] => f (fincl (fset_sub _ _) x)].

Definition restrictf f (A : {fset K}) : {fmap K -> V} :=
  filterf f (mem A).

Notation "x .[& A ]" := (restrictf x A) : fmap_scope.
Notation "x .[\ A ]" := (x.[& domf x `\` A]) : fmap_scope.
Notation "x .[~ k ]" := (x.[\ [fset k]]) : fmap_scope.

Lemma domf_filterf f (P : pred K) :
 domf (filterf f P) = [fset k in domf f | P k].
Admitted.

Lemma mem_filterf f (P : pred K) (k : K) :
  (k \in domf (filterf f P)) = (k \in f) && (P k) :> bool.
Admitted.

Lemma mem_restrictf f (A : {fset K}) (k : K) :
   k \in f.[& A] = (k \in A) && (k \in f) :> bool.
Admitted.

Lemma mem_remf f (A : {fset K}) (k : K) :
   k \in f.[\ A] = (k \notin A) && (k \in f) :> bool.
Admitted.

Lemma mem_remf1 f (k' k : K) :
   k \in f.[~ k'] = (k != k') && (k \in f) :> bool.
Admitted.

Lemma domf_restrict f A : domf f.[& A] = A `&` domf f.
Admitted.

Lemma domf_rem f A : domf f.[\ A] = domf f `\` A.
Admitted.

Lemma mem_remfF f (k : K) : k \in f.[~ k] = false.
Admitted.

Lemma fnd_filterf f P k : (filterf f P).[? k] = if P k then f.[? k] else None.
Admitted.

Lemma get_filterf f P k (kff : k \in filterf f P) (kf : k \in f) :
  (filterf f P).[kff] = f.[kf].
Admitted.

Lemma fnd_restrict f A (k : K) :
   f.[& A].[? k] = if k \in A then f.[? k] else None.
Admitted.

Lemma fnd_rem f A (k : K) : f.[\ A].[? k] = if k \in A then None else f.[? k].
Admitted.

Lemma restrictf_comp f A B : f.[& A].[& B] = f.[& A `&` B].
Admitted.

Lemma remf_comp f A B : f.[\ A].[\ B] = f.[\ A `|` B].
Admitted.

Lemma restrictfT f : f.[& domf f] = f.
Admitted.

Lemma restrictf0 f : f.[& fset0] = [fmap].
Admitted.

Lemma remf0 f : f.[\ fset0] = f.
Admitted.

Lemma fnd_rem1 f (k k' : K) :
  f.[~ k].[? k'] = if k' != k then f.[? k'] else None.
Admitted.

Lemma getf_restrict f A (k : K) (kf : k \in f) (kfA : k \in f.[& A]) :
      f.[& A].[kfA] = f.[kf].
Admitted.

Lemma setf_restrict f A (k : K) (v : V) :
  f.[& A].[k <- v] = f.[k <- v].[& k |` A].
Admitted.

Lemma setf_rem f A (k : K) (v : V) :
  f.[\ A].[k <- v] = f.[k <- v].[\ (A `\ k)].
Admitted.

Lemma setf_rem1 f (k : K) (v : V) : f.[~ k].[k <- v] = f.[k <- v].
Admitted.

Lemma setfC f k1 k2 v1 v2 : f.[k1 <- v1].[k2 <- v2] =
   if k2 == k1 then f.[k2 <- v2] else f.[k2 <- v2].[k1 <- v1].
Admitted.

Lemma restrictf_mkdom f A : f.[& A] = f.[& domf f `&` A].
Admitted.

Lemma restrictf_id f A : [disjoint domf f & A] -> f.[& A] = [fmap].
Admitted.

Lemma remf_id f A : [disjoint domf f & A] -> f.[\ A] = f.
Admitted.

Lemma remf1_id f k : k \notin f -> f.[~ k] = f.
Admitted.

Lemma restrictf_set f A (k : K) (v : V) :
  f.[k <- v].[& A] = if k \in A then f.[& A].[k <- v] else f.[& A].
Admitted.

Lemma remf_set f A (k : K) (v : V) :
  f.[k <- v].[\ A] = if k \in A then f.[\ A] else f.[\ A].[k <- v].
Admitted.

Lemma remf1_set f (k k' : K) (v : V) :
  f.[k' <- v].[~ k] = if k == k' then f.[~ k] else f.[~ k].[k' <- v].
Admitted.

Lemma setf_inj f f' k v : k \notin f -> k \notin f' ->
                          f.[k <- v] = f'.[k <- v]-> f = f'.
Admitted.

End RestrictionOps.

Arguments filterf : simpl never.
Arguments restrictf : simpl never.
Notation "x .[& A ]" := (restrictf x A) : fmap_scope.
Notation "x .[\ A ]" := (x.[& domf x `\` A]) : fmap_scope.
Notation "x .[~ k ]" := (x.[\ [fset k]]) : fmap_scope.

Section Cat.
Variables (K : choiceType) (V : Type).
Implicit Types (f g : {fmap K -> V}).

Definition catf (f g : {fmap K -> V}) :=
  [fmap k : (domf f `\` domf g) `|` domf g=>
          match fsetULVR (valP k) with
            | inl kfDg => f.[fsubsetP (fsubsetDl _ _) _ kfDg]
            | inr kg => g.[kg]
          end].

Local Notation "f + g" := (catf f g) : fset_scope.

Lemma domf_cat f g : domf (f + g) = domf f `|` domf g.
Admitted.

Lemma mem_catf f g k : k \in domf (f + g) = (k \in f) || (k \in g).
Admitted.

Lemma fnd_cat f g k :
  (f + g).[? k] = if k \in domf g then g.[? k] else f.[? k].
Admitted.

Lemma catfE f g : f + g = f.[\ domf g] + g.
Admitted.

Lemma getf_catl f g k (kfg : k \in domf (f + g))
      (kf : k \in domf f) : k \notin domf g -> (f + g).[kfg] = f.[kf].
Admitted.

Lemma getf_catr f g k (kfg : k \in domf (f + g))
      (kg : k \in domf g) : (f + g).[kfg] = g.[kg].
Admitted.

Lemma catf0 f : f + [fmap] = f.
Admitted.

Lemma cat0f f : [fmap] + f = f.
Admitted.

Lemma catf_setl f g k (v : V) :
  f.[k <- v] + g = if k \in g then f + g else (f + g).[k <- v].
Admitted.

Lemma catf_setr f g k (v : V) : f + g.[k <- v] = (f + g).[k <- v].
Admitted.

Lemma restrictf_cat f g A : (f + g).[& A] = f.[& A] + g.[& A].
Admitted.

Lemma restrictf_cat_domr f g : (f + g).[& domf g] = g.
Admitted.

Lemma remf_cat f g A : (f + g).[\ A] = f.[\ A] + g.[\ A].
Admitted.

Lemma catf_restrictl A f g : f.[& A] + g = (f + g).[& A `|` domf g].
Admitted.

Lemma catf_reml A f g : f.[\ A] + g = (f + g).[\ A `\` domf g].
Admitted.

Lemma catf_rem1l k f g :
  f.[~ k] + g = if k \in g then f + g else (f + g).[~ k].
Admitted.

Lemma setf_catr f g k (v : V) : (f + g).[k <- v] = f + g.[k <- v].
Admitted.

Lemma setf_catl f g k (v : V) : (f + g).[k <- v] = f.[k <- v] + g.[~ k].
Admitted.

Lemma catfA f g h : f + (g + h) = f + g + h.
Admitted.

Lemma catfC f g : f + g = g + f.[\ domf g].
Admitted.

Lemma disjoint_catfC f g : [disjoint domf f & domf g] -> f + g = g + f.
Admitted.

Lemma catfAC f g h : f + g + h = f + h + g.[\ domf h].
Admitted.

Lemma disjoint_catfAC f g h : [disjoint domf g & domf h]%fmap ->
     f + g + h = f + h + g.
Admitted.

Lemma catfCA f g h : f + (g + h) = g + (f.[\ domf g] + h).
Admitted.

Lemma disjoint_catfCA f g h : [disjoint domf f & domf g]%fmap ->
     f + (g + h) = g + (f + h).
Admitted.

Lemma catfIs f g h : f + h = g + h -> f.[\ domf h] = g.[\ domf h].
Admitted.

Lemma disjoint_catfIs h f g :
  [disjoint domf f & domf h] -> [disjoint domf g & domf h] ->
  f + h = g + h -> f = g.
Admitted.

Lemma restrict_catfsI f g h : f + g = f + h -> g.[& domf h] = h.[& domf g].
Admitted.

Lemma disjoint_catfsI h f g :
  [disjoint domf f & domf h] -> [disjoint domf g & domf h] ->
  h + f = h + g -> f = g.
Admitted.

End Cat.

Module Import FmapE.
Definition fmapE := (fndSome, getfE, setfK, fnd_set, getf_set,
  setfNK, fnd_reducef, get_reducef, fnd_filterf, get_filterf,
  fnd_restrict, getf_restrict, fnd_rem, fnd_rem1,
  restrictfT, restrictf0, restrictf_id, remf_id, remf1_id,
  fnd_cat).
End FmapE.

Arguments catf : simpl never.
Notation "f + g" := (catf f g) : fset_scope.

Section FinMapKeyType.
Variables (K V : choiceType).
Implicit Types (f g : {fmap K -> V}).

Definition codomf f : {fset V} := [fset f k | k : domf f].

Lemma mem_codomf f v : (v \in codomf f) = [exists x : domf f, f x == v].
Admitted.

Lemma codomfP f v : reflect (exists x, f.[? x] = Some v) (v \in codomf f).
Admitted.

Lemma codomfPn f v : reflect (forall x, f.[? x] != Some v) (v \notin codomf f).
Admitted.

Lemma codomf0 : codomf [fmap] = fset0.
Admitted.

Lemma in_codomf f (k : domf f) : f k \in codomf f.
Admitted.

Lemma fndSomeP f (k : K) (v : V):
  (f.[? k] = Some v) <-> {kf : k \in f & f.[kf] = v}.
Admitted.

Lemma codomf_restrict f (A : {fset K})  :
  codomf f.[& A] = [fset f k | k : domf f & val k \in A].
Admitted.

Lemma codomf_restrict_exists f (A : {fset K})  :
  codomf f.[& A] = [fset v in codomf f
                   | [exists k : domf f, (val k \in A) && (f k == v)]].
Admitted.

Lemma codomf_rem f (A : {fset K})  :
  codomf f.[\ A] = [fset f k | k : domf f & val k \notin A].
Admitted.

Lemma codomf_rem_exists f (A : {fset K})  :
  codomf f.[\ A] = [fset v in codomf f
                   | [exists k : domf f, (val k \notin A) && (f k == v)]].
Admitted.

Lemma in_codomf_rem1 f (k : K) (kf : k \in domf f)  :
  codomf f.[~ k] =
  if [exists k' : domf f, (val k' != k) && (f k' == f.[kf])] then codomf f
  else codomf f `\ f.[kf].
Admitted.

Lemma codomf_set f (k : K) (v : V) (kf : k \in domf f) :
  codomf f.[k <- v] = v |` codomf f.[~ k].
Admitted.

Lemma codomf_cat (f g : {fmap K -> V}) :
  codomf (f + g) = codomf g `|` codomf f.[\domf g].
Admitted.

End FinMapKeyType.

Module Import FinmapInE.
Definition inE := (inE, mem_codomf, mem_catf, mem_remfF,
                   mem_filterf, mem_reducef, mem_restrictf,
                   mem_remf, mem_remf1, mem_setf).
End FinmapInE.

Section FsfunDef.

Variables (K : choiceType) (V : eqType) (default : K -> V).

Record fsfun := Fsfun {
  fmap_of_fsfun : {fmap K -> V};
  _ : [forall k : domf fmap_of_fsfun,
       fmap_of_fsfun k != default (val k)]
}.

Canonical fsfun_subType := Eval hnf in [subType for fmap_of_fsfun].
Definition fsfun_eqMixin := [eqMixin of fsfun by <:].
Canonical  fsfun_eqType := EqType fsfun fsfun_eqMixin.

Fact fsfun_subproof (f : fsfun) :
  forall (k : K) (kf : k \in fmap_of_fsfun f),
  (fmap_of_fsfun f).[kf]%fmap != default k.
Admitted.

Definition fun_of_fsfun (f : fsfun) (k : K) :=
  odflt (default k) (fmap_of_fsfun f).[? k]%fmap.
End FsfunDef.

Coercion fun_of_fsfun : fsfun >-> Funclass.

Module Type FinSuppSig.
Axiom fs : forall (K : choiceType) (V : eqType) (default : K -> V),
  fsfun default -> {fset K}.
Axiom E : fs = (fun K V d f => domf (@fmap_of_fsfun K V d f)).
End FinSuppSig.
Module FinSupp : FinSuppSig.
Definition fs := (fun K V d f => domf (@fmap_of_fsfun K V d f)).
Definition E := erefl fs.
End FinSupp.
Notation finsupp := FinSupp.fs.
Canonical unlockable_finsupp := Unlockable FinSupp.E.

Section FSfunBasics.

Variables (K : choiceType) (V : eqType) (default : K -> V).
Implicit Types (f : fsfun default) (k : K) (v : V).

Lemma mem_finsupp f k : (k \in finsupp f) = (f k != default k).
Admitted.

Lemma memNfinsupp f k : (k \notin finsupp f) = (f k == default k).
Admitted.

Lemma fsfun_dflt f k : k \notin finsupp f -> f k = default k.
Admitted.

Variant fsfun_spec f k : V -> bool -> Type :=
  | FsfunOut : k \notin finsupp f -> fsfun_spec f k (default k) false
  | FsfunIn  (kf : k \in finsupp f) : fsfun_spec f k (f k) true.

Lemma finsuppP f k : fsfun_spec f k (f k) (k \in finsupp f).
Admitted.

Lemma fsfunP f f' : f =1 f' <-> f = f'.
Admitted.

Lemma fsfun_injective_inP  f (T : {fset K}) :
  reflect {in T &, injective f} (injectiveb [ffun x : T => f (val x)]).
Admitted.

Definition fsfun_of_can_ffun (T : {fset K}) (g : {ffun T -> V})
          (can_g : forall k : T,  g k != default (val k)) :=
  @Fsfun K V default (FinMap g) (appP forallP idP can_g).

Lemma fsfun_of_can_ffunE (T : {fset K}) (g : {ffun T -> V})
          (can_g : forall k : T ,  g k != default (val k)) k (kg : k \in T) :
  (fsfun_of_can_ffun can_g) k = g.[kg].
Admitted.

End FSfunBasics.

Notation "{ 'fsfun' ty 'for' dflt }" := (fsfun (dflt : ty))
  (at level 0, format "{ 'fsfun' ty  'for'  dflt }") : type_scope.
Notation "{ 'fsfun' ty 'of' x => dflt }" := {fsfun ty for fun x => dflt}
  (at level 0, x at level 99,
   format "{ 'fsfun'  ty  'of'  x  =>  dflt }") : type_scope.
Notation "{ 'fsfun' ty 'with' dflt }" := {fsfun ty of _ => dflt}
  (at level 0, format "{ 'fsfun'  ty  'with'  dflt }") : type_scope.
Notation "{ 'fsfun' ty }" := {fsfun ty of x => x}
  (at level 0, format "{ 'fsfun'  ty }") : type_scope.

Notation "{ 'fsfun' 'for' dflt }" := {fsfun _ for dflt}
  (at level 0, only parsing) : type_scope.
Notation "{ 'fsfun' 'of' x : T => dflt }" := {fsfun T -> _ of x => dflt}
  (at level 0, x at level 99, only parsing) : type_scope.
Notation "{ 'fsfun' 'of' x => dflt }" := {fsfun of x : _ => dflt}
  (at level 0, x at level 99, only parsing) : type_scope.
Notation "{ 'fsfun' 'with' dflt }" := {fsfun of _ => dflt}
  (at level 0, only parsing) : type_scope.

Module Type FsfunSig.
Section FsfunSig.
Variables (K : choiceType) (V : eqType) (default : K -> V).

Parameter of_ffun : forall (S : {fset K}), (S -> V) -> unit -> fsfun default.
Variables (S : {fset K}) (h : S -> V).
Axiom of_ffunE :forall key x, of_ffun h key x = odflt (default x) (omap h (insub x)).

End FsfunSig.
End FsfunSig.

Module Fsfun : FsfunSig.
Section FsfunOfFinfun.

Variables (K : choiceType) (V : eqType) (default : K -> V)
          (S : {fset K}) (h : S -> V).

Let fmap :=
  [fmap a : [fsetval a in {: S} | h a != default (val a)]
   => h (fincl (fset_sub_val _ _) a)].

Fact fmapP a : fmap a != default (val a).
Admitted.

Definition of_ffun (k : unit) := fsfun_of_can_ffun fmapP.

Lemma of_ffunE key x : of_ffun key x = odflt (default x) (omap h (insub x)).
Admitted.

End FsfunOfFinfun.
End Fsfun.
Canonical fsfun_of_funE K V default S h key x :=
   Unlockable (@Fsfun.of_ffunE K V default S h key x).

Fact fsfun_key : unit.
Admitted.

Definition fsfun_of_ffun key (K : choiceType) (V : eqType)
  (S : {fset K}) (h : S -> V) (default : K -> V) :=
  (Fsfun.of_ffun default h key).

Definition fsfun_choiceMixin (K V : choiceType) (d : K -> V) :=
  [choiceMixin of fsfun d by <:].
Canonical  fsfun_choiceType (K V : choiceType) (d : K -> V) :=
  ChoiceType (fsfun d) (fsfun_choiceMixin d).

Definition fsfun_countMixin (K V : countType) (d : K -> V) :=
  [countMixin of fsfun d by <:].
Canonical  fsfun_countType (K V : countType) (d : K -> V) :=
  CountType (fsfun d) (fsfun_countMixin d).

Declare Scope fsfun_scope.
Delimit Scope fsfun_scope with fsfun.

Notation "[ 'fsfun[' key ] x : aT => F | default ]" :=
  (fsfun_of_ffun key (fun x : aT => F) (fun x => default))
  (at level 0, x at level 99, only parsing) : fun_scope.

Notation "[ 'fsfun' x : aT => F | default ]" :=
  [fsfun[fsfun_key] x : aT => F | default]
  (at level 0, x at level 99, only parsing) : fun_scope.

Notation "[ 'fsfun[' key ] x : aT => F ]" := [fsfun[key] x : aT => F | _]
  (at level 0, x at level 99, only parsing) : fun_scope.

Notation "[ 'fsfun' x : aT => F ]" := [fsfun x : aT => F | _]
  (at level 0, x at level 99, only parsing) : fun_scope.

Notation "[ 'fsfun[' key ] x => F | default ]" :=
  [fsfun[key] x : _ => F | default ]
  (at level 0, x at level 99, only parsing) : fun_scope.

Notation "[ 'fsfun' x => F | default ]" := [fsfun x : _ => F | default]
  (at level 0, x at level 99, only parsing) : fun_scope.

Notation "[ 'fsfun[' key ] x => F ]" := [fsfun[key] x => F | _]
  (at level 0, x at level 99, only parsing) : fun_scope.

Notation "[ 'fsfun' x => F ]" := [fsfun x => F | _]
  (at level 0, x at level 99, only parsing) : fun_scope.

Notation "[ 'fsfun[' key ]=> F | default ]" :=
  [fsfun[key] _ => F | default ]
  (at level 0, only parsing) : fun_scope.

Notation "[ 'fsfun=>' F | default ]" := [fsfun _ => F | default]
  (at level 0, only parsing) : fun_scope.

Notation "[ 'fsfun[' key ]=> F ]" := [fsfun[key]=> F | _]
  (at level 0, only parsing) : fun_scope.

Notation "[ 'fsfun=>' F ]" := [fsfun=> F | _]
  (at level 0, only parsing) : fun_scope.

Definition fsfun_of_fun key (K : choiceType) (V : eqType)
   (S : {fset K}) (h : K -> V) default :=
  [fsfun[key] x : S => h (val x) | default x].

Notation "[ 'fsfun[' key ] x 'in' S => F | default ]" :=
  (fsfun_of_fun key S (fun x => F) (fun x => default))
  (at level 0, x at level 99, only parsing) : fun_scope.

Notation "[ 'fsfun' x 'in' S => F | default ]" :=
  [fsfun[fsfun_key] x in S => F | default]
  (at level 0, x at level 99, only parsing) : fun_scope.

Notation "[ 'fsfun[' key ] x 'in' S => F ]" :=
  [fsfun[key] x in S => F | _]
  (at level 0, x at level 99, only parsing) : fun_scope.

Notation "[ 'fsfun' x 'in' S => F ]" :=
  [fsfun[fsfun_key] x in S => F | _]
  (at level 0, x at level 99, only parsing) : fun_scope.

Notation "[ 'fsfun[' key ] 'in' S => F | default ]" :=
  [fsfun[key] _ in S => F | default]
  (at level 0, only parsing) : fun_scope.

Notation "[ 'fsfun' 'in' S => F | default ]" :=
  [fsfun[fsfun_key] in S => F | default]
  (at level 0, only parsing) : fun_scope.

Notation "[ 'fsfun[' key ] 'in' S => F ]" :=
  [fsfun[key] in S => F | _]
  (at level 0, only parsing) : fun_scope.

Notation "[ 'fsfun' 'in' S => F ]" :=
  [fsfun[fsfun_key] in S => F | _]
  (at level 0, only parsing) : fun_scope.

 
Notation "[ 'fs' 'fun' x : aT => F ]" := [fsfun[_] x : aT => F]
  (at level 0, x at level 99,
  format "[ 'fs' 'fun'  x  :  aT  =>  F ]") : fun_scope.

Notation "[ 'fs' 'fun' x 'in' aT => F ]" := [fsfun[_] x in aT => F]
  (at level 0, x at level 99,
  format "[ 'fs' 'fun'  x  'in'  aT  =>  F ]") : fun_scope.

Fact fsfun0_key : unit.
Admitted.
Notation "[ 'fsfun' 'for' default ]" := (fsfun_of_ffun fsfun0_key [fmap] default)
  (at level 0, only parsing) : fun_scope.

Notation "[ 'fsfun' 'of' x => default ]" := [fsfun for fun x => default]
  (at level 0,  x at level 99, only parsing) : fun_scope.

Notation "[ 'fsfun' 'with' default ]" := [fsfun of _ => default]
  (at level 0, only parsing) : fun_scope.

Notation "[ 'fsfun' ]" := [fsfun for _]
 (at level 0, format "[ 'fsfun' ]") : fun_scope.

Section FsfunTheory.
Variables (key : unit) (K : choiceType) (V : eqType) (default : K -> V).

Lemma fsfun_ffun (S : {fset K}) (h : S -> V) (x : K) :
  [fsfun[key] a : S => h a | default a] x =
  odflt (default x) (omap h (insub x)).
Admitted.

Lemma fsfun_fun (S : {fset K}) (h : K -> V) (x : K) :
  [fsfun[key] a in S => h a | default a] x =
   if x \in S then h x else (default x).
Admitted.

Lemma fsfun0E : [fsfun for default] =1 default.
Admitted.

Definition fsfunE := (fsfun_fun, fsfun0E).

Lemma finsupp_sub  (S : {fset K}) (h : S -> V) :
  finsupp [fsfun[key] a : S => h a | default a] `<=` S.
Admitted.

Lemma finsupp0 : finsupp [fsfun for default] = fset0.
Admitted.

Lemma fsfun0_inj : injective default -> injective [fsfun for default].
Admitted.

Lemma in_finsupp0 x : x \in finsupp [fsfun for default] = false.
Admitted.

End FsfunTheory.

Section FsWith.
Variables (K : choiceType) (V : eqType) (default : K -> V).
Implicit Types (f : {fsfun K -> V for default}) (x z : K) (y : V).

Definition fun_delta_key (d : fun_delta K V) := let: FunDelta x y := d in x.

Definition app_fsdelta (d : fun_delta K V) f : {fsfun K -> V for default} :=
  [fsfun z in fun_delta_key d |` finsupp f => [eta f with d] z].

Definition app_fswithout x f : {fsfun K -> V for default} :=
  app_fsdelta (x |-> default x)%FUN_DELTA f.

End FsWith.

Arguments app_fsdelta {K V default}.
Arguments app_fswithout {K V default}.

Notation "[ 'fsfun' f 'with' d1 , .. , dn ]" :=
  (app_fsdelta d1%FUN_DELTA .. (app_fsdelta dn%FUN_DELTA f) ..)
  (at level 0, f at level 99, format
  "'[hv' [ '[' 'fsfun' '/ '  f ']' '/'  'with'  '[' d1 , '/'  .. , '/'  dn ']' ] ']'") : fun_scope.

Notation "[ 'fsfun' f 'without' x1 , .. , xn ]" :=
  (app_fswithout x1 .. (app_fswithout xn f) ..)
  (at level 0, f at level 99, format
  "'[hv' [ '[' 'fsfun' '/ '  f ']' '/'  'without'  '[' x1 , '/'  .. , '/'  xn ']' ] ']'") : fun_scope.

Section FsWithTheory.
Variables (K : choiceType) (V : eqType) (default : K -> V).
Implicit Types (f : {fsfun K -> V for default}) (x z : K) (y : V).

Lemma fsfun_withE f x y z :
  [fsfun f with x |-> y] z = if z == x then y else f z.
Admitted.

Lemma fsfun_with f x y : [fsfun f with x |-> y] x = y.
Admitted.

Lemma fsfun_with_id f x : [fsfun f with x |-> f x] = f.
Admitted.

Lemma finsupp_with f x y : finsupp [fsfun f with x |-> y] =
  if y == default x then finsupp f `\ x else x |` finsupp f.
Admitted.

Lemma finsupp_without f x z : finsupp [fsfun f without x] = finsupp f `\ x.
Admitted.

End FsWithTheory.

Module Import FsfunInE2.
Definition inE := (inE, in_finsupp0).
End FsfunInE2.

Section FsfunIdTheory.

Variables (K : choiceType).
Implicit Types (f g : {fsfun K -> K}).

Fact fsfun_comp_key : unit.
Admitted.
Definition fsfun_comp g f : {fsfun _} :=
  [fsfun[fsfun_comp_key] k in finsupp f `|` finsupp g => g (f k)].

Notation "g \o f" := (fsfun_comp g f) : fsfun_scope.

Lemma fscompE g f : (g \o f)%fsfun =1 g \o f.
Admitted.

Lemma fscomp0f : left_id [fsfun] fsfun_comp.
Admitted.

Lemma fscompA : associative fsfun_comp.
Admitted.

Lemma fscomp_inj g f : injective f -> injective g -> injective (g \o f)%fsfun.
Admitted.

Definition fsinjectiveb : pred {fsfun K -> K} :=
  [pred f | (injectiveb [ffun a : finsupp f => f (val a)])
            && [forall a : finsupp f, f (val a) \in finsupp f]].

Lemma fsinjP {f} : [<->
    injective f;
    let S := finsupp f in {in S &, injective f}
        /\ forall a : S, f (val a) \in S;
    exists2 S : {fset K}, (finsupp f `<=` S) & {in S &, injective f}
        /\ forall a : S, f (val a) \in S].
Admitted.

Lemma fsinjectiveP f : reflect (injective f) (fsinjectiveb f).
Admitted.

Lemma fsinjectivebP f :
  reflect (exists2 S : {fset K}, (finsupp f `<=` S)
           & {in S &, injective f} /\ forall a : S, f (val a) \in S)
        (fsinjectiveb f).
Admitted.

End FsfunIdTheory.

Arguments fsinjP {K f}.
Arguments fsinjectiveP {K f}.
Arguments fsinjectivebP {K f}.

Definition inE := inE.

End finmap.

End mathcomp_DOT_finmap_DOT_finmap_WRAPPED.
Module Export mathcomp_DOT_finmap_DOT_finmap.
Module Export mathcomp.
Module Export finmap.
Module finmap.
Include mathcomp_DOT_finmap_DOT_finmap_WRAPPED.finmap.
End finmap.

End finmap.

End mathcomp.

End mathcomp_DOT_finmap_DOT_finmap.
Module Export mathcomp_DOT_ssreflect_DOT_order_WRAPPED.
Module Export order.
Import mathcomp.ssreflect.ssreflect.
Import mathcomp.ssreflect.ssrfun.
Import mathcomp.ssreflect.ssrbool.
Import mathcomp.ssreflect.eqtype.
Import mathcomp.ssreflect.choice.

Set Implicit Arguments.
Unset Strict Implicit.

Declare Scope order_scope.

Delimit Scope order_scope with O.
Local Open Scope order_scope.

Module Export Order.

Module POrder.
Section ClassDef.

Record mixin_of (T0 : Type) (b : Equality.class_of T0)
                (T := Equality.Pack b) := Mixin {
  le : rel T;
  lt : rel T;
  _  : forall x y, lt x y = (y != x) && (le x y);
  _  : reflexive     le;
  _  : antisymmetric le;
  _  : transitive    le;
}.
Record class_of (T : Type) := Class {
  base  : Choice.class_of T;
  mixin : mixin_of base;
}.

Local Coercion base : class_of >-> Choice.class_of.

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
End ClassDef.

Module Export Exports.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Canonical eqType.
Canonical choiceType.
Notation porderType := type.
End Exports.

End POrder.
Import POrder.Exports.

Section POrderDef.

Variable (disp : unit) (T : porderType disp).
Definition le : rel T.
Admitted.
Local Notation "x <= y" := (le x y) : order_scope.
Definition lt : rel T.
Admitted.
Local Notation "x < y" := (lt x y) : order_scope.
Definition leif (x y : T) C : Prop := ((x <= y) * ((x == y) = C))%type.

Definition lteif x y C := if C then x <= y else x < y.

End POrderDef.

Prenex Implicits lt le leif lteif.

Module Import POSyntax.

Notation "<=%O" := le : function_scope.

Notation "x <= y" := (le x y) : order_scope.
Notation "x <= y :> T" := ((x : T) <= (y : T)) (only parsing) : order_scope.
Notation "x >= y" := (y <= x) (only parsing) : order_scope.

Notation "x < y"  := (lt x y) : order_scope.
Notation "x < y :> T" := ((x : T) < (y : T)) (only parsing) : order_scope.
Notation "x > y"  := (y < x) (only parsing) : order_scope.

End POSyntax.

Module Export Lattice.
Section ClassDef.

Record mixin_of (T0 : Type) (b : POrder.class_of T0)
                (T := POrder.Pack tt b) := Mixin {
  meet : T -> T -> T;
  join : T -> T -> T;
  _ : commutative meet;
  _ : commutative join;
  _ : associative meet;
  _ : associative join;
  _ : forall y x, meet x (join x y) = x;
  _ : forall y x, join x (meet x y) = x;
  _ : forall x y, (x <= y) = (meet x y == x);
}.
Record class_of (T : Type) := Class {
  base  : POrder.class_of T;
  mixin : mixin_of base;
}.

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.
End ClassDef.

Module Export Exports.
Coercion sort : type >-> Sortclass.
Notation latticeType  := type.
End Exports.
End Lattice.

Section LatticeDef.
Context {disp : unit} {T : latticeType disp}.
Definition meet : T -> T -> T.
Admitted.
Definition join : T -> T -> T.
Admitted.

End LatticeDef.

Module Import LatticeSyntax.

End LatticeSyntax.

Module Import BLatticeSyntax.

End BLatticeSyntax.

Module Import TBLatticeSyntax.

End TBLatticeSyntax.

Module Export DistrLattice.
Section ClassDef.

Record mixin_of (T0 : Type) (b : Lattice.class_of T0)
                (T := Lattice.Pack tt b) := Mixin {
  _ : @left_distributive T T meet join;
}.
End ClassDef.

End DistrLattice.

Module Import CBDistrLatticeSyntax.
End CBDistrLatticeSyntax.

Module Import CTBDistrLatticeSyntax.
End CTBDistrLatticeSyntax.

Module Export Total.
Section ClassDef.

Definition mixin_of T0 (b : POrder.class_of T0) (T := POrder.Pack tt b) :=
  total (<=%O : rel T).

End ClassDef.

End Total.

Module Import DualSyntax.

End DualSyntax.

Module Import POrderTheory.
End POrderTheory.

Module Import DualPOrder.
End DualPOrder.

Module Import DualLattice.
End DualLattice.

Module Import LatticeTheoryMeet.
End LatticeTheoryMeet.

Module Import LatticeTheoryJoin.
End LatticeTheoryJoin.

Module Import DistrLatticeTheory.
End DistrLatticeTheory.

Module Import TotalTheory.
End TotalTheory.

Module Import BLatticeTheory.
End BLatticeTheory.

Module Import DualTBLattice.
End DualTBLattice.

Module Import TBLatticeTheory.
End TBLatticeTheory.

Module Import BDistrLatticeTheory.
End BDistrLatticeTheory.

Module Import DualTBDistrLattice.
End DualTBDistrLattice.

Module Import TBDistrLatticeTheory.
End TBDistrLatticeTheory.

Module Import CBDistrLatticeTheory.
End CBDistrLatticeTheory.

Module Import CTBDistrLatticeTheory.
End CTBDistrLatticeTheory.

Module Import ProdSyntax.

End ProdSyntax.

Module Import LexiSyntax.

End LexiSyntax.

Module Import DualOrder.
End DualOrder.

Module Import EnumVal.
End EnumVal.

Module Export Syntax.
Export POSyntax.
End Syntax.

End Order.

Export Order.POrder.Exports.

End order.
Module Export mathcomp.
Module Export ssreflect.
Module Export order.
Include mathcomp_DOT_ssreflect_DOT_order_WRAPPED.order.
End order.
Export mathcomp.ssreflect.ssreflect.
Export mathcomp.ssreflect.ssrbool.
Export mathcomp.ssreflect.ssrfun.
Export mathcomp.ssreflect.eqtype.
Export mathcomp.ssreflect.ssrnat.
Export mathcomp.ssreflect.choice.
Export mathcomp.ssreflect.finset.
Module Export mathcomp_DOT_algebra_DOT_ssralg_WRAPPED.
Module Export ssralg.

Set Implicit Arguments.
Unset Strict Implicit.

Declare Scope ring_scope.
Reserved Notation "f \+ g" (at level 50, left associativity).
Reserved Notation "f \* g" (at level 40, left associativity).

Delimit Scope ring_scope with R.
Local Open Scope ring_scope.

Module Import GRing.

Module Export Zmodule.

Record mixin_of (V : Type) : Type := Mixin {
  zero : V;
  opp : V -> V;
  add : V -> V -> V;
  _ : associative add;
  _ : commutative add;
  _ : left_id zero add;
  _ : left_inverse zero opp add
}.

Section ClassDef.
Record class_of T := Class { base : Choice.class_of T; mixin : mixin_of T }.
Local Coercion base : class_of >-> Choice.class_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.

Definition pack m :=
  fun bT b & phant_id (Choice.class bT) b => Pack (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> Choice.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Canonical choiceType.
Notation zmodType := type.
Notation ZmodType T m := (@pack T m _ _ id).
Notation ZmodMixin := Mixin.
Notation "[ 'zmodType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'zmodType'  'of'  T ]") : form_scope.
End Exports.

End Zmodule.

Definition zero V := Zmodule.zero (Zmodule.class V).
Definition opp V := Zmodule.opp (Zmodule.class V).
Definition add V := Zmodule.add (Zmodule.class V).

Local Notation "0" := (zero _) : ring_scope.
Local Notation "+%R" := (@add _) : function_scope.
Local Notation "x + y" := (add x y) : ring_scope.

Definition natmul V x n := nosimpl iterop _ n +%R x (zero V).

Module Ring.

Record mixin_of (R : zmodType) : Type := Mixin {
  one : R;
  mul : R -> R -> R;
  _ : associative mul;
  _ : left_id one mul;
  _ : right_id one mul;
  _ : left_distributive mul +%R;
  _ : right_distributive mul +%R;
  _ : one != 0
}.

Section ClassDef.
Record class_of (R : Type) : Type := Class {
  base : Zmodule.class_of R;
  mixin : mixin_of (Zmodule.Pack base)
}.
Local Coercion base : class_of >-> Zmodule.class_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.

Definition pack b0 (m0 : mixin_of (@Zmodule.Pack T b0)) :=
  fun bT b & phant_id (Zmodule.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition zmodType := @Zmodule.Pack cT class.

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> Zmodule.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Canonical eqType.
Coercion zmodType : type >-> Zmodule.type.
Canonical zmodType.
Notation ringType := type.
Notation RingType T m := (@pack T _ m _ _ id _ id).
Notation RingMixin := Mixin.
Notation "[ 'ringType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'ringType'  'of'  T ]") : form_scope.
End Exports.

End Ring.
Import Ring.Exports.
Definition one (R : ringType) : R.
Admitted.
Definition mul (R : ringType) : R -> R -> R.
exact (Ring.mul (Ring.class R)).
Defined.
Definition exp R x n := nosimpl iterop _ n (@mul R) x (one R).

Local Notation "1" := (one _) : ring_scope.
Local Notation "*%R" := (@mul _) : function_scope.
Local Notation "x * y" := (mul x y) : ring_scope.
Local Notation "x ^+ n" := (exp x n) : ring_scope.

Section RingTheory.

Variable R : ringType.
Implicit Types x y : R.

Lemma mulrA : @associative R *%R.
Admitted.
Lemma mul1r : @left_id R R 1 *%R.
Admitted.
Lemma mulrDl : @left_distributive R R *%R +%R.
Admitted.
Lemma mulrDr : @right_distributive R R *%R +%R.
Admitted.
Lemma expr2 x : x ^+ 2 = x * x.
Admitted.

End RingTheory.

Module Lmodule.

Structure mixin_of (R : ringType) (V : zmodType) : Type := Mixin {
  scale : R -> V -> V;
  _ : forall a b v, scale a (scale b v) = scale (a * b) v;
  _ : left_id 1 scale;
  _ : right_distributive scale +%R;
  _ : forall v, {morph scale^~ v: a b / a + b}
}.

Section ClassDef.

Variable R : ringType.
Record class_of V := Class {
  base : Zmodule.class_of V;
  mixin : mixin_of R (Zmodule.Pack base)
}.

Structure type (phR : phant R) := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variable (phR : phant R) (T : Type) (cT : type phR).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Definition pack b0 (m0 : mixin_of R (@Zmodule.Pack T b0)) :=
  fun bT b & phant_id (Zmodule.class bT) b =>
  fun    m & phant_id m0 m => Pack phR (@Class T b m).

End ClassDef.

Module Import Exports.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Notation lmodType R := (type (Phant R)).
Notation LmodType R T m := (@pack _ (Phant R) T _ m _ _ id _ id).
End Exports.

End Lmodule.
Import Lmodule.Exports.
Definition scale (R : ringType) (V : lmodType R) : R -> V -> V.
exact (Lmodule.scale (Lmodule.class V)).
Defined.

Module Export Lalgebra.

Section ClassDef.

Variable R : ringType.

Structure type (phR : phant R) := Pack {sort; _ : class_of sort}.

End ClassDef.

Module Export Exports.
Notation lalgType R := (type (Phant R)).
End Exports.

End Lalgebra.

Definition regular R : Type := R.
Local Notation "R ^o" := (regular R) (at level 2, format "R ^o") : type_scope.

Section LalgebraTheory.

Variables (R : ringType) (A : lalgType R).
Canonical regular_zmodType := [zmodType of R^o].
Canonical regular_ringType := [ringType of R^o].

Definition regular_lmodMixin :=
  let mkMixin := @Lmodule.Mixin R regular_zmodType (@mul R) in
  mkMixin (@mulrA R) (@mul1r R) (@mulrDr R) (fun v a b => mulrDl a b v).

Canonical regular_lmodType := LmodType R R^o regular_lmodMixin.

End LalgebraTheory.

Section LiftedZmod.
Variables (U : Type) (V : zmodType).
Definition null_fun_head (phV : phant V) of U : V.
Admitted.
Definition add_fun (f g : U -> V) x := f x + g x.
End LiftedZmod.

Section LiftedRing.
Variables (R : ringType) (T : Type).
Implicit Type f : T -> R.
Definition mul_fun f g x := f x * g x.
End LiftedRing.

Notation null_fun V := (null_fun_head (Phant V)) (only parsing).

Module ComRing.

Section ClassDef.
Record class_of R :=
  Class {base : Ring.class_of R; mixin : commutative (Ring.mul base)}.
Local Coercion base : class_of >-> Ring.class_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variable (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition ringType := @Ring.Pack cT class.

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> Ring.class_of.
Coercion sort : type >-> Sortclass.
Canonical ringType.
Notation comRingType := type.
End Exports.

End ComRing.
Import ComRing.Exports.

Section ComRingTheory.

Variable R : comRingType.
Lemma mulrACA : @interchange R *%R *%R.
Admitted.

End ComRingTheory.

Module UnitRing.

Record mixin_of (R : ringType) : Type := Mixin {
  unit : pred R;
  inv : R -> R;
  _ : {in unit, left_inverse 1 inv *%R};
  _ : {in unit, right_inverse 1 inv *%R};
  _ : forall x y, y * x = 1 /\ x * y = 1 -> unit x;
  _ : {in [predC unit], inv =1 id}
}.

Section ClassDef.
Record class_of (R : Type) : Type := Class {
  base : Ring.class_of R;
  mixin : mixin_of (Ring.Pack base)
}.
Local Coercion base : class_of >-> Ring.class_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition ringType := @Ring.Pack cT class.

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> Ring.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion ringType : type >-> Ring.type.
Notation unitRingType := type.
End Exports.

End UnitRing.
Import UnitRing.Exports.

Definition unit {R : unitRingType} :=
  [qualify a u : R | UnitRing.unit (UnitRing.class R) u].

Module Export ComUnitRing.

Section ClassDef.
Record class_of (R : Type) : Type := Class {
  base : ComRing.class_of R;
  mixin : UnitRing.mixin_of (Ring.Pack base)
}.
Definition base2 R m := UnitRing.Class (@mixin R m).

End ClassDef.

Module Import Exports.
Coercion base : class_of >-> ComRing.class_of.
Coercion base2 : class_of >-> UnitRing.class_of.
End Exports.

End ComUnitRing.
Import ComUnitRing.Exports.

Module Export IntegralDomain.

Definition axiom (R : ringType) :=
  forall x y : R, x * y = 0 -> (x == 0) || (y == 0).

Section ClassDef.
Record class_of (R : Type) : Type :=
  Class {base : ComUnitRing.class_of R; mixin : axiom (Ring.Pack base)}.

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> ComUnitRing.class_of.
End Exports.

End IntegralDomain.

Module Export Field.

Definition mixin_of (R : unitRingType) := forall x : R, x != 0 -> x \in unit.

End Field.

Module Export Theory.
Definition expr2 := expr2.
Definition mulrACA := mulrACA.

End Theory.

End GRing.
Export Zmodule.Exports.
Export Ring.Exports.
Export UnitRing.Exports.
Export ComUnitRing.Exports.
Export IntegralDomain.Exports.

Notation "0" := (zero _) : ring_scope.
Notation "- x" := (opp x) : ring_scope.
Notation "x + y" := (add x y) : ring_scope.
Notation "x - y" := (add x (- y)) : ring_scope.
Notation "x *+ n" := (natmul x n) : ring_scope.

Notation "1" := (one _) : ring_scope.
Notation "x * y" := (mul x y) : ring_scope.
Notation "x ^+ n" := (exp x n) : ring_scope.

Notation "*:%R" := (@scale _ _) : function_scope.
Notation "\0" := (null_fun _) : ring_scope.
Notation "f \+ g" := (add_fun f g) : ring_scope.
Notation "f \* g" := (mul_fun f g) : ring_scope.

Notation "R ^o" := (regular R) (at level 2, format "R ^o") : type_scope.
Canonical regular_ringType.
Canonical regular_lmodType.

End ssralg.
Module Export mathcomp.
Module Export algebra.
Module Export ssralg.
Include mathcomp_DOT_algebra_DOT_ssralg_WRAPPED.ssralg.
End ssralg.

Set Implicit Arguments.
Unset Strict Implicit.
Local Open Scope ring_scope.

Fact ring_display : unit.
Admitted.

Module Export Num.

Record normed_mixin_of (R T : zmodType)
       (Rorder : Order.POrder.mixin_of (Equality.class R))
       (le_op := Order.POrder.le Rorder)
  := NormedMixin {
  norm_op : T -> R;
  _ : forall x y, le_op (norm_op (x + y)) (norm_op x + norm_op y);
  _ : forall x, norm_op x = 0 -> x = 0;
  _ : forall x n, norm_op (x *+ n) = norm_op x *+ n;
  _ : forall x, norm_op (- x) = norm_op x;
}.

Record mixin_of (R : ringType)
       (Rorder : Order.POrder.mixin_of (Equality.class R))
       (le_op := Order.POrder.le Rorder) (lt_op := Order.POrder.lt Rorder)
       (normed : @normed_mixin_of R R Rorder) (norm_op := norm_op normed)
  := Mixin {
  _ : forall x y, lt_op 0 x -> lt_op 0 y -> lt_op 0 (x + y);
  _ : forall x y, le_op 0 x -> le_op 0 y -> le_op x y || le_op y x;
  _ : {morph norm_op : x y / x * y};
  _ : forall x y, (le_op x y) = (norm_op (y - x) == y - x);
}.

Local Notation ring_for T b := (@GRing.Ring.Pack T b).

Module Export NumDomain.

Section ClassDef.
Record class_of T := Class {
  base : GRing.IntegralDomain.class_of T;
  order_mixin : Order.POrder.mixin_of (Equality.class (ring_for T base));
  normed_mixin : normed_mixin_of (ring_for T base) order_mixin;
  mixin : mixin_of normed_mixin;
}.

Local Coercion base : class_of >-> GRing.IntegralDomain.class_of.
Local Coercion order_base T (class_of_T : class_of T) :=
  @Order.POrder.Class _ class_of_T (order_mixin class_of_T).

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c  as cT' := cT return class_of cT' in c.
Definition ringType := @GRing.Ring.Pack cT class.
Definition comRingType := @GRing.ComRing.Pack cT class.
Definition unitRingType := @GRing.UnitRing.Pack cT class.
Definition porderType := @Order.POrder.Pack ring_display cT class.
Definition porder_zmodType := @GRing.Zmodule.Pack porderType class.

End ClassDef.

Module Export Exports.
Coercion base  : class_of >-> GRing.IntegralDomain.class_of.
Coercion order_base : class_of >-> Order.POrder.class_of.
Canonical ringType.
Canonical comRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical porderType.
Canonical porder_zmodType.
Notation numDomainType := type.
End Exports.

End NumDomain.

Local Notation num_for T b := (@NumDomain.Pack T b).

Module Export NormedZmodule.

Section ClassDef.

Variable R : numDomainType.
Record class_of (T : Type) := Class {
  base : GRing.Zmodule.class_of T;
  mixin : @normed_mixin_of R (@GRing.Zmodule.Pack T base) (NumDomain.class R);
}.

Local Coercion base : class_of >-> GRing.Zmodule.class_of.

Structure type (phR : phant R) :=
  Pack { sort; _ : class_of sort }.
Local Coercion sort : type >-> Sortclass.

Variables (phR : phant R) (T : Type) (cT : type phR).

Definition class := let: Pack _ c := cT return class_of cT in c.
Definition zmodType := @GRing.Zmodule.Pack cT class.

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> GRing.Zmodule.class_of.
Coercion zmodType : type >-> GRing.Zmodule.type.
Notation normedZmodType R := (type (Phant R)).
End Exports.

End NormedZmodule.

Module NumDomain_joins.
Import NumDomain.
Section NumDomain_joins.

Variables (T : Type) (cT : type).

Notation class := (class cT).
Definition normedZmodType : normedZmodType cT.
exact (@NormedZmodule.Pack
     cT (Phant cT) cT (NormedZmodule.Class (NumDomain.normed_mixin class))).
Defined.

End NumDomain_joins.

Module Export Exports.
Coercion normedZmodType : type >-> NormedZmodule.type.
Canonical normedZmodType.
End Exports.
End NumDomain_joins.
Export NumDomain_joins.Exports.

Module Import Def.
Definition normr (R : numDomainType) (T : normedZmodType R) : T -> R.
Admitted.
Arguments normr {R T} x.

End Def.

Notation norm := normr (only parsing).

Module Import Syntax.

Notation "`| x |" := (norm x) : ring_scope.

Notation "x <= y" := (le x y) : ring_scope.

End Syntax.

Section ExtensionAxioms.

Variable R : numDomainType.
Definition real_closed_axiom : Prop.
Admitted.

End ExtensionAxioms.

Module NumField.

Section ClassDef.
Record class_of R := Class {
  base  : NumDomain.class_of R;
  mixin : GRing.Field.mixin_of (num_for R base);
}.
Local Coercion base : class_of >-> NumDomain.class_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition numDomainType := @NumDomain.Pack cT class.

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> NumDomain.class_of.
Coercion numDomainType : type >-> NumDomain.type.
Notation numFieldType := type.
End Exports.

End NumField.
Import NumField.Exports.

Module Export RealField.

Section ClassDef.
Record class_of R := Class {
  base  : NumField.class_of R;
  nmixin : Order.Lattice.mixin_of base;
  lmixin : Order.DistrLattice.mixin_of (Order.Lattice.Class nmixin);
  tmixin : Order.Total.mixin_of base;
}.

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> NumField.class_of.
End Exports.

End RealField.

Module RealClosedField.

Section ClassDef.
Record class_of R := Class {
  base : RealField.class_of R;
  mixin : real_closed_axiom (num_for R base)
}.
Local Coercion base : class_of >-> RealField.class_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition zmodType := @GRing.Zmodule.Pack cT class.
Definition ringType := @GRing.Ring.Pack cT class.
Definition porderType := @Order.POrder.Pack ring_display cT class.
Definition numDomainType := @NumDomain.Pack cT class.
Definition numFieldType := @NumField.Pack cT class.

End ClassDef.

Module Export Exports.
Coercion sort : type >-> Sortclass.
Canonical zmodType.
Canonical ringType.
Canonical porderType.
Canonical numDomainType.
Canonical numFieldType.
Notation rcfType := Num.RealClosedField.type.
End Exports.

End RealClosedField.
Import RealClosedField.Exports.

Module Import Internals.

Section RealClosed.
Variable R : rcfType.

Fact sqrtr_subproof (x : R) :
  exists2 y, 0 <= y & (if 0 <= x then y ^+ 2 == x else y == 0) : bool.
Admitted.

End RealClosed.

End Internals.

Module Import ExtraDef.

Definition sqrtr {R} x := s2val (sig2W (@sqrtr_subproof R x)).

End ExtraDef.
Notation sqrt := sqrtr.

Section NumIntegralDomainTheory.

Variable R : numDomainType.
Definition normrM : {morph norm : x y / (x : R) * y}.
Admitted.

Section NormedZmoduleTheory.

Variable V : normedZmodType R.
Implicit Types (v w : V).

Lemma normr_ge0 v : 0 <= `|v|.
Admitted.

End NormedZmoduleTheory.

End NumIntegralDomainTheory.
#[global] Hint Extern 0 (is_true (0 <= norm _)) => apply: normr_ge0 : core.

Section NumDomainOperationTheory.

Variable R : numDomainType.
Implicit Types x y z t : R.

Lemma ler_pM x1 y1 x2 y2 :
  0 <= x1 -> 0 <= x2 -> x1 <= y1 -> x2 <= y2 -> x1 * x2 <= y1 * y2.
Admitted.

End NumDomainOperationTheory.
#[deprecated(since="mathcomp 1.17.0", note="Use ler_pM instead.")]
Notation ler_pmul := ler_pM.

Section RealClosedFieldTheory.

Variable R : rcfType.
Implicit Types a x y : R.

Lemma sqr_sqrtr a : 0 <= a -> sqrt a ^+ 2 = a.
Admitted.

End RealClosedFieldTheory.

Import mathcomp.ssreflect.order.
Reserved Notation "x %:num" (at level 2, format "x %:num").
Local Open Scope order_scope.
Declare Scope snum_sign_scope.
Delimit Scope snum_sign_scope with snum_sign.
Declare Scope snum_nullity_scope.
Delimit Scope snum_nullity_scope with snum_nullity.
Variant nullity := NonZero | MaybeZero.
Coercion nullity_bool nz := if nz is NonZero then true else false.

Variant sign := EqZero | NonNeg | NonPos.
Variant real := Sign of sign | AnySign.
Variant reality := Real of real | Arbitrary.

Definition wider_nullity xnz ynz :=
  match xnz, ynz with
  | MaybeZero, _
  | NonZero, NonZero => true
  | NonZero, MaybeZero => false
  end.
Definition wider_sign xs ys :=
  match xs, ys with
  | NonNeg, NonNeg | NonNeg, EqZero
  | NonPos, NonPos | NonPos, EqZero
  | EqZero, EqZero => true
  | NonNeg, NonPos | NonPos, NonNeg
  | EqZero, NonPos | EqZero, NonNeg => false
  end.
Definition wider_real xr yr :=
  match xr, yr with
  | AnySign, _ => true
  | Sign sx, Sign sy => wider_sign sx sy
  | Sign _, AnySign => false
  end.
Definition wider_reality xr yr :=
  match xr, yr with
  | Arbitrary, _ => true
  | Real xr, Real yr => wider_real xr yr
  | Real _, Arbitrary => false
  end.

Module Export Signed.
Section Signed.
Context (disp : unit) (T : porderType disp) (x0 : T).
Definition reality_cond (n : reality) (x : T) :=
  match n with
  | Real (Sign EqZero) => x == x0
  | Real (Sign NonNeg) => x >= x0
  | Real (Sign NonPos) => x <= x0
  | Real AnySign       => (x0 <= x) || (x <= x0)
  | Arbitrary          => true
  end.

Record def (nz : nullity) (cond : reality) := Def {
  r :> T;
  #[canonical=no]
  P : (nz ==> (r != x0)) && reality_cond cond r
}.

End Signed.

Notation spec x0 nz cond x :=
  ((nullity_bool nz%snum_nullity ==> (x != x0))
   && (reality_cond x0 cond%snum_sign x)).

Definition mk {d T} x0 nz cond r P : @def d T x0 nz cond :=
  @Def d T x0 nz cond r P.
Coercion Sign : sign >-> real.
Coercion Real : real >-> reality.
Bind Scope snum_sign_scope with sign.
Notation ">=0" := NonNeg : snum_sign_scope.
Notation "!=0" := NonZero : snum_nullity_scope.
Notation "{ 'compare' x0 & nz & cond }" := (def x0 nz cond) : type_scope.
Notation "{ 'num' R & nz & cond }" := (def (0%R : R) nz cond) : ring_scope.
Notation "{ > x0 }" := (def x0 NonZero NonNeg) : type_scope.
Notation "x %:num" := (r x) : ring_scope.
Definition posnum (R : numDomainType) of phant R := {> 0%R : R}.
Notation "{ 'posnum' R }" := (@posnum _ (Phant R))  : ring_scope.

Class unify {T} f (x y : T) := Unify : f x y = true.
Class unify' {T} f (x y : T) := Unify' : f x y = true.
#[global] Instance unify'P {T} f (x y : T) : unify' f x y -> unify f x y.
Admitted.
#[global]
Hint Extern 0 (unify' _ _ _) => vm_compute; reflexivity : typeclass_instances.

Notation unify_nz nzx nzy :=
  (unify wider_nullity nzx%snum_nullity nzy%snum_nullity).
Notation unify_r rx ry :=
  (unify wider_reality rx%snum_sign ry%snum_sign).

Section Theory.
Context {d : unit} {T : porderType d} {x0 : T}
  {nz : nullity} {cond : reality}.
Local Notation sT := {compare x0 & nz & cond}.
Implicit Type x : sT.

Lemma gt0 x : unify_nz !=0 nz -> unify_r >=0 cond -> x0 < x%:num :> T.
Admitted.

Lemma ge0 x : unify_r >=0 cond -> x0 <= x%:num :> T.
Admitted.

End Theory.
Arguments ge0 {d T x0 nz cond} _ {_}.

#[global] Hint Extern 0 (is_true (0%R < _)%O) => solve [apply: gt0] : core.

Section RcfStability.
Context {R : rcfType}.

Definition sqrt_nonzero_subdef (xnz : nullity) (xr : reality) :=
  if xr is Real (Sign >=0) then xnz else MaybeZero.

Lemma sqrt_snum_subproof xnz xr (x : {num R & xnz & xr})
    (nz := sqrt_nonzero_subdef xnz xr) :
  Signed.spec 0 nz >=0 (Num.sqrt x%:num).
Admitted.

Canonical sqrt_snum xnz xr (x : {num R & xnz & xr}) :=
  Signed.mk (sqrt_snum_subproof x).

End RcfStability.

CoInductive posnum_spec (R : numDomainType) (x : R) :
  R -> bool -> bool -> bool -> Type :=
| IsPosnum (p : {posnum R}) : posnum_spec x (p%:num) false true true.

Lemma posnumP (R : numDomainType) (x : R) : 0 < x ->
  posnum_spec x x (x == 0) (0 <= x) (0 < x).
Admitted.
Export mathcomp.algebra.ssralg.

Lemma cid2 (A : Type) (P Q : A -> Prop) :
  (exists2 x : A, P x & Q x) -> {x : A | P x & Q x}.
Admitted.

Lemma pselect (P : Prop): {P} + {~P}.
Admitted.

Lemma gen_choiceMixin {T : Type} : Choice.mixin_of T.
Admitted.

Definition asbool (P : Prop) := if pselect P then true else false.

Notation "`[< P >]" := (asbool P) : bool_scope.

Lemma asboolT (P : Prop) : P -> `[<P>].
Admitted.

Definition gen_eq (T : Type) (u v : T) := `[<u = v>].
Lemma gen_eqP (T : Type) : Equality.axiom (@gen_eq T).
Admitted.
Definition gen_eqMixin {T : Type} := EqMixin (@gen_eqP T).

Canonical arrow_eqType (T : Type) (T' : eqType) :=
  EqType (T -> T') gen_eqMixin.
Canonical arrow_choiceType (T : Type) (T' : choiceType) :=
  ChoiceType (T -> T') gen_choiceMixin.

Canonical Prop_eqType := EqType Prop gen_eqMixin.
Canonical Prop_choiceType := ChoiceType Prop gen_choiceMixin.

Module Export classical_sets.
Import mathcomp.finmap.finmap.

Declare Scope classical_set_scope.

Definition set T := T -> Prop.
Definition in_set T (A : set T) : pred T.
Admitted.
Canonical set_predType T := @PredType T (set T) (@in_set T).
Local Open Scope classical_set_scope.
Delimit Scope classical_set_scope with classic.
Definition mkset {T} (P : T -> Prop) : set T.
exact (P).
Defined.

Notation "[ 'set' x : T | P ]" := (mkset (fun x : T => P)) : classical_set_scope.
Notation "[ 'set' x | P ]" := [set x : _ | P] : classical_set_scope.

Definition image {T rT} (A : set T) (f : T -> rT) :=
  [set y | exists2 x, A x & f x = y].

Section basic_definitions.
Context {T rT : Type}.
Implicit Types (T : Type) (A B : set T) (f : T -> rT) (Y : set rT).

Definition setT := [set _ : T | True].
Definition setI A B := [set x | A x /\ B x].

Definition subset A B := forall t, A t -> B t.

End basic_definitions.
Notation "[ 'set' : T ]" := (@setT T) : classical_set_scope.
Notation "A `&` B" := (setI A B) : classical_set_scope.

Notation "A `<=` B" := (subset A B) : classical_set_scope.
Notation "f @` A" := (image A f) (only parsing) : classical_set_scope.

Module Export Pointed.

Definition point_of (T : Type) := T.

Record class_of (T : Type) := Class {
  base : Choice.class_of T;
  mixin : point_of T
}.

Section ClassDef.

Structure type := Pack { sort; _ : class_of sort }.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c := cT return class_of cT in c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).
Local Coercion base : class_of >-> Choice.class_of.

Definition pack m :=
  fun bT b of phant_id (Choice.class bT) b => @Pack T (Class b m).
Definition choiceType := @Choice.Pack cT xclass.

End ClassDef.

Module Export Exports.

Coercion sort : type >-> Sortclass.
Coercion mixin : class_of >-> point_of.
Canonical choiceType.
Notation pointedType := type.
Notation PointedType T m := (@pack T m _ _ idfun).

End Exports.

End Pointed.
Definition point {M : pointedType} : M.
Admitted.

Canonical arrow_pointedType (T : Type) (T' : pointedType) :=
  PointedType (T -> T') (fun=> point).
Canonical Prop_pointedType := PointedType Prop False.

Module Export Empty.

Module Import Exports.
End Exports.

End Empty.

Notation "B \; A" :=
  ([set xy | exists2 z, A (xy.1, z) & B (z, xy.2)]) : classical_set_scope.

End classical_sets.
Import HB.structures.

Reserved Notation "''oinv_' f" (at level 8, f at level 2, format "''oinv_' f").

Local Open Scope classical_set_scope.

Section MainProperties.
Context {aT rT}  (A : set aT) (B : set rT) (f : aT -> rT).
Definition set_fun := {homo f : x / A x >-> B x}.
Definition set_surj := B `<=` f @` A.
End MainProperties.

HB.mixin Record isFun {aT rT} (A : set aT) (B : set rT) (f : aT -> rT) :=
  { funS : set_fun A B f }.
HB.structure Definition Fun {aT rT} (A : set aT) (B : set rT) :=
  { f of isFun _ _ A B f }.

HB.mixin Record OInv {aT rT} (f : aT -> rT) := { oinv : rT -> option aT }.
HB.structure Definition OInversible aT rT := {f of OInv aT rT f}.
Notation "{ 'oinv' aT >-> rT }" := (@OInversible.type aT rT) : type_scope.
Definition phant_oinv aT rT (f : {oinv aT >-> rT})
  of phantom (_ -> _) f := @oinv _ _ f.
Notation "''oinv_' f" := (@phant_oinv _ _ _ (Phantom (_ -> _) f%FUN)).

HB.structure Definition OInvFun aT rT A B :=
  {f of OInv aT rT f & isFun aT rT A B f}.

HB.mixin Record OInv_Inv {aT rT} (f : aT -> rT) of OInv _ _ f := {
  inv : rT -> aT;
  oliftV : olift inv = 'oinv_f
}.

HB.factory Record Inv {aT rT} (f : aT -> rT) := { inv : rT -> aT  }.
HB.builders Context {aT rT} (f : aT -> rT) of Inv _ _ f.
  HB.instance Definition _ := OInv.Build _ _ f (olift inv).
  HB.instance Definition _ := OInv_Inv.Build _ _ f erefl.
HB.end.

HB.structure Definition Inversible aT rT := {f of Inv aT rT f}.
Notation "{ 'inv' aT >->  rT }" := (@Inversible.type aT rT) : type_scope.
Definition phant_inv aT rT (f : {inv aT >-> rT}) of phantom (_ -> _) f :=
  @inv _ _ f.
Notation "f ^-1" := (@phant_inv _ _ _ (Phantom (_ -> _) f%FUN)) : fun_scope.

HB.structure Definition InvFun aT rT A B :=
  {f of Inv aT rT f & isFun aT rT A B f}.

HB.mixin Record OInv_CanV {aT rT} {A : set aT} {B : set rT}
  (f : aT -> rT) of OInv _ _ f := {
    oinvS : {homo 'oinv_f : x / B x >-> (some @` A) x};
    oinvK : {in B, ocancel 'oinv_f f};
  }.

HB.factory Record OCanV {aT rT} {A : set aT} {B : set rT} (f : aT -> rT) := {
    oinv; oinvS : {homo oinv : x / B x >-> (some @` A) x};
          oinvK : {in B, ocancel oinv f};
  }.
HB.builders Context {aT rT} {A : set aT} {B : set rT} (f : aT -> rT)
   of OCanV _ _ A B f.
 HB.instance Definition _ := OInv.Build _ _ f oinv.
 HB.instance Definition _ := OInv_CanV.Build _ _ A B f oinvS oinvK.
HB.end.

HB.structure Definition Surject {aT rT A B} := {f of @OCanV aT rT A B f}.

HB.structure Definition SurjFun aT rT A B :=
  {f of @Surject aT rT A B f & @Fun _ _ A B f}.

HB.structure Definition SplitSurj aT rT A B :=
  {f of @Surject aT rT A B f & @Inv _ _ f}.

HB.structure Definition SplitSurjFun aT rT A B :=
   {f of @SplitSurj aT rT A B f & @Fun _ _ A B f}.

HB.mixin Record OInv_Can aT rT (A : set aT) (f : aT -> rT) of OInv _ _ f :=
  { funoK : {in A, pcancel f 'oinv_f} }.

HB.structure Definition Inject aT rT A :=
  {f of OInv aT rT f & OInv_Can aT rT A f}.

HB.structure Definition SplitInj aT rT (A : set aT) :=
  {f of @Inv aT rT f & @Inject aT rT A f}.

HB.structure Definition SplitInjFun aT rT (A : set aT) (B : set rT) :=
  {f of @SplitInj _ rT A f & @isFun _ _ A B f}.

HB.factory Record Inv_Can {aT rT} {A : set aT} (f : aT -> rT) of Inv _ _ f :=
  { funK : {in A, cancel f f^-1} }.
HB.builders Context {aT rT} A (f : aT -> rT) of @Inv_Can _ _ A f.
  Local Lemma funoK: {in A, pcancel f 'oinv_f}.
Admitted.
  HB.instance Definition _ := OInv_Can.Build _ _ A f funoK.
HB.end.

HB.factory Record Inv_CanV {aT rT} {A : set aT} {B : set rT} (f : aT -> rT)
     of Inv aT rT f := {
  invS : {homo f^-1 : x / B x >-> A x};
  invK : {in B, cancel f^-1 f};
}.
HB.builders Context {aT rT} {A : set aT} {B : set rT} (f : aT -> rT)
    of Inv_CanV _ _ A B f.
  #[local] Lemma oinvK : {in B, ocancel 'oinv_f f}.
Admitted.
  #[local] Lemma oinvS : {homo 'oinv_f : x / B x >-> (some @` A) x}.
Admitted.
  HB.instance Definition _ := OInv_CanV.Build _ _ _ _ f oinvS oinvK.
HB.end.

HB.factory Record CanV {aT rT} {A : set aT} {B : set rT} (f : aT -> rT) :=
  { inv; invS : {homo inv : x / B x >-> A x}; invK : {in B, cancel inv f}; }.
HB.builders Context {aT rT} {A : set aT} {B : set rT} (f : aT -> rT) of CanV _ _ A B f.
 HB.instance Definition _ := Inv.Build _ _ f inv.
HB.end.

HB.factory Record OInv_Can2 {aT rT} {A : set aT} {B : set rT} (f : aT -> rT) of
  @OInv _ _ f :=
  {
    funS :  {homo f : x / A x >-> B x};
    oinvS : {homo 'oinv_f : x / B x >-> (some @` A) x};
    funoK : {in A, pcancel f 'oinv_f};
    oinvK : {in B, ocancel 'oinv_f f};
  }.
HB.builders Context {aT rT} A B (f : aT -> rT) of OInv_Can2 _ _ A B f.
  HB.instance Definition _ := isFun.Build aT rT _ _ f funS.
HB.end.

HB.factory Record OCan2 {aT rT} {A : set aT} {B : set rT} (f : aT -> rT) :=
   { oinv; funS :  {homo f : x / A x >-> B x};
           oinvS : {homo oinv : x / B x >-> (some @` A) x};
           funoK : {in A, pcancel f oinv};
           oinvK : {in B, ocancel oinv f};
   }.
HB.builders Context {aT rT} A B (f : aT -> rT) of OCan2 _ _ A B f.
  HB.instance Definition _ := OInv.Build aT rT f oinv.
HB.end.

HB.factory Record Can {aT rT} {A : set aT} (f : aT -> rT) :=
  { inv; funK : {in A, cancel f inv} }.
HB.builders Context {aT rT} A (f : aT -> rT) of @Can _ _ A f.

 HB.instance Definition _ := Inv.Build _ _ f inv.
HB.end.

HB.factory Record Inv_Can2 {aT rT} {A : set aT} {B : set rT} (f : aT -> rT) of
   Inv _ _ f :=
   { funS : {homo f : x / A x >-> B x};
     invS : {homo f^-1 : x / B x >-> A x};
     funK : {in A, cancel f f^-1};
     invK : {in B, cancel f^-1 f};
   }.
HB.builders Context {aT rT} A B (f : aT -> rT) of Inv_Can2 _ _ A B f.
  HB.instance Definition _ := isFun.Build aT rT A B f funS.
HB.end.

HB.factory Record Can2 {aT rT} {A : set aT} {B : set rT} (f : aT -> rT) :=
  { inv; funS : {homo f : x / A x >-> B x};
         invS : {homo inv : x / B x >-> A x};
         funK : {in A, cancel f inv};
         invK : {in B, cancel inv f};
   }.
HB.builders Context {aT rT} A B (f : aT -> rT) of Can2 _ _ A B f.
  HB.instance Definition _ := Inv.Build aT rT f inv.
HB.end.

HB.factory Record SplitInjFun_CanV {aT rT} {A : set aT} {B : set rT} (f : aT -> rT) of
     @SplitInjFun _ _ A B f :=
  { invS : {homo f^-1 : x / B x >-> A x}; injV : {in B &, injective f^-1} }.
HB.builders Context {aT rT} {A : set aT} {B : set rT} (f : aT -> rT) of SplitInjFun_CanV _ _ A B f.
  Local Lemma invK : {in B, cancel f^-1 f}.
Admitted.
  HB.instance Definition _ := Inv_CanV.Build aT rT A B f invS invK.
HB.end.

HB.factory Record BijTT {aT rT} (f : aT -> rT) := { bij : bijective f }.
HB.builders Context {aT rT} f of BijTT aT rT f.
  Local Lemma exg : {g | cancel f g /\ cancel g f}.
Admitted.
  HB.instance Definition _ := Can2.Build aT rT setT setT f
    (fun x y => y) (fun x y => y)
    (in1W (projT2 exg).1) (in1W (projT2 exg).2).
HB.end.

Section surj_oinv.
Context {aT rT} {A : set aT} {B : set rT} {f : aT -> rT} (fsurj : set_surj A B f).

Let surjective_oinv (y : rT) :=
  if pselect (B y) is left By then some (projT1 (cid2 (fsurj By))) else None.

Lemma surjective_oinvK : {in B, ocancel surjective_oinv f}.
Admitted.

Lemma surjective_oinvS : set_fun B (some @` A) surjective_oinv.
Admitted.
End surj_oinv.
Coercion surjective_ocanV {aT rT} {A : set aT} {B : set rT} {f : aT -> rT}
    (fS : set_surj A B f) :=
  OCanV.Build aT rT A B f (surjective_oinvS fS) (surjective_oinvK fS).

Section funin_surj.
Context {aT rT : Type}.

Definition funin (A : set aT) (f : aT -> rT) := f.

Context {A : set aT} {B : set rT} (f : aT -> rT).

HB.instance Definition _ : OCanV _ _ A (f @` A) (funin A f) :=
   ((fun _ => id) : set_surj A (f @` A) f).

End funin_surj.
Notation "[ 'fun' f 'in' A ]" := (funin A f)
  (at level 0, f at next level,
   format "[ 'fun'  f  'in'  A ]") : function_scope.

HB.factory Record Inj {aT rT} (A : set aT) (f : aT -> rT) :=
   { inj : {in A &, injective f} }.
HB.builders Context {aT rT} A (f : aT -> rT) of Inj _ _ A f.
  HB.instance Definition _ := OInversible.copy f [fun f in A].
HB.end.

HB.factory Record SurjFun_Inj {aT rT} {A : set aT} {B : set rT} (f : aT -> rT) of
   @SurjFun _ _ A B f := { inj : {in A &, injective f} }.
HB.builders Context {aT rT} {A : set aT} {B : set rT} (f : aT -> rT) of
    @SurjFun_Inj _ _ A B f.
  Let fcan : OInv_Can aT rT A f.
Admitted.
 HB.instance Definition _ := fcan.
HB.end.

HB.factory Record SplitSurjFun_Inj {aT rT} {A : set aT} {B : set rT} (f : aT -> rT) of
     @SplitSurjFun _ _ A B f :=
   { inj : {in A &, injective f} }.
HB.builders Context {aT rT} {A : set aT} {B : set rT} (f : aT -> rT) of
    @SplitSurjFun_Inj _ _ A B f.
  Local Lemma funK : {in A, cancel f f^-1%FUN}.
Admitted.
  HB.instance Definition _ := Inv_Can.Build aT rT _ f funK.
HB.end.

Section function_space.
Definition cst {T T' : Type} (x : T') : T -> T'.
Admitted.

Program Definition fct_zmodMixin (T : Type) (M : zmodType) :=
  @ZmodMixin (T -> M) \0 (fun f x => - f x) (fun f g => f \+ g) _ _ _ _.
Admit Obligations.
Canonical fct_zmodType T (M : zmodType) := ZmodType (T -> M) (fct_zmodMixin T M).

Program Definition fct_ringMixin (T : pointedType) (M : ringType) :=
  @RingMixin [zmodType of T -> M] (cst 1) (fun f g => f \* g)
             _ _ _ _ _ _.
Admit Obligations.
Canonical fct_ringType (T : pointedType) (M : ringType) :=
  RingType (T -> M) (fct_ringMixin T M).

End function_space.

Module Export topology.
Reserved Notation "'\forall' x '\near' x_0 , P"
  (at level 200, x name, P at level 200,
   format "'\forall'  x  '\near'  x_0 ,  P").
Reserved Notation "x \is_near F" (at level 10, format "x  \is_near  F").

Module Export Filtered.

Definition nbhs_of U T := T -> set (set U).
Record class_of U T := Class {
  base : Pointed.class_of T;
  nbhs_op : nbhs_of U T
}.

Section ClassDef.
Variable U : Type.

Structure type := Pack { sort; _ : class_of U sort }.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c := cT return class_of U cT in c.

Definition clone c of phant_id class c := @Pack T c.

Definition pack m :=
  fun bT b of phant_id (Pointed.class bT) b => @Pack T (Class b m).

End ClassDef.

Structure source Z Y := Source {
  source_type :> Type;
  _ : (source_type -> Z) -> set (set Y)
}.
Definition source_filter Z Y (F : source Z Y) : (F -> Z) -> set (set Y).
exact (let: Source X f := F in f).
Defined.

Module Export Exports.
Coercion sort : type >-> Sortclass.
Coercion base : class_of >-> Pointed.class_of.
Coercion nbhs_op : class_of >-> nbhs_of.
Notation filteredType := type.
Notation FilteredType U T m := (@pack U T m _ _ idfun).
Notation "[ 'filteredType' U 'of' T 'for' cT ]" :=  (@clone U T cT _ idfun)
  (at level 0, format "[ 'filteredType'  U  'of'  T  'for'  cT ]") : form_scope.

Canonical default_arrow_filter Y (Z : pointedType) (X : source Z Y) :=
  FilteredType Y (X -> Z) (@source_filter _ _ X).
Canonical source_filter_filter Y :=
  @Source Prop _ (_ -> Prop) (fun x : (set (set Y)) => x).

End Exports.
End Filtered.
Definition nbhs {U} {T : filteredType U} : T -> set (set U).
exact (Filtered.nbhs_op (Filtered.class T)).
Defined.
Definition filter_from {I T : Type} (D : set I) (B : I -> set T) : set (set T).
Admitted.

Section Near.

Local Notation "{ 'all1' P }" := (forall x, P x : Prop) (at level 0).
Local Notation ph := (phantom _).

Definition prop_near1 {X} {fX : filteredType X} (x : fX)
   P (phP : ph {all1 P}) := nbhs x P.

End Near.

Notation "{ 'near' x , P }" := (@prop_near1 _ _ x _ (inPhantom P)) : type_scope.
Notation "'\forall' x '\near' x_0 , P" := {near x_0, forall x, P} : type_scope.

Definition filter_of X (fX : filteredType X) (x : fX) of phantom fX x :=
   nbhs x.
Notation "[ 'filter' 'of' x ]" :=
  (@filter_of _ _ _ (Phantom _ x)) : classical_set_scope.

Class Filter {T : Type} (F : set (set T)) := {
  filterT : F setT ;
  filterI : forall P Q : set T, F P -> F Q -> F (P `&` Q) ;
  filterS : forall P Q : set T, P `<=` Q -> F P -> F Q
}.

Class ProperFilter' {T : Type} (F : set (set T)) := {
  filter_not_empty : not (F (fun _ => False)) ;
  filter_filter' : Filter F
}.

Notation ProperFilter := ProperFilter'.

Lemma filter_setT (T' : Type) : Filter [set: set T'].
Admitted.

Structure filter_on T := FilterType {
  filter :> (T -> Prop) -> Prop;
  _ : Filter filter
}.
Definition filter_class T (F : filter_on T) : Filter F.
Admitted.
Arguments FilterType {T} _ _.
#[global] Existing Instance filter_class.

Canonical filter_on_eqType T := EqType (filter_on T) gen_eqMixin.
Canonical filter_on_choiceType T :=
  ChoiceType (filter_on T) gen_choiceMixin.
Canonical filter_on_PointedType T :=
  PointedType (filter_on T) (FilterType _ (filter_setT T)).
Canonical filter_on_FilteredType T :=
  FilteredType T (filter_on T) (@filter T).

Record in_filter T (F : set (set T)) := InFilter {
  prop_in_filter_proj : T -> Prop;
  prop_in_filterP_proj : F prop_in_filter_proj
}.

Module Type PropInFilterSig.
Axiom t : forall (T : Type) (F : set (set T)), in_filter F -> T -> Prop.
End PropInFilterSig.
Module PropInFilter : PropInFilterSig.
Definition t := prop_in_filter_proj.
End PropInFilter.

Notation prop_of := PropInFilter.t.
Notation "x \is_near F" := (@PropInFilter.t _ F _ x).
Definition in_filterT T F (FF : Filter F) : @in_filter T F.
Admitted.
Canonical in_filterI T F (FF : Filter F) (P Q : @in_filter T F) :=
  InFilter (filterI (prop_in_filterP_proj P) (prop_in_filterP_proj Q)).

Lemma filter_near_of T F (P : @in_filter T F) (Q : set T) : Filter F ->
  (forall x, prop_of P x -> Q x) -> F Q.
Admitted.

Fact near_key : unit.
Admitted.

Lemma mark_near (P : Prop) : locked_with near_key P -> P.
Admitted.

Lemma near_acc T F (P : @in_filter T F) (Q : set T) (FF : Filter F)
   (FQ : \forall x \near F, Q x) :
   locked_with near_key (forall x, prop_of (in_filterI FF P (InFilter FQ)) x -> Q x).
Admitted.

Lemma near_skip_subproof T F (P Q : @in_filter T F) (G : set T) (FF : Filter F) :
   locked_with near_key (forall x, prop_of P x -> G x) ->
   locked_with near_key (forall x, prop_of (in_filterI FF P Q) x -> G x).
Admitted.

Tactic Notation "near=>" ident(x) := apply: filter_near_of => x ?.

Ltac just_discharge_near x :=
  tryif match goal with Hx : x \is_near _ |- _ => move: (x) (Hx); apply: mark_near end
        then idtac else fail "the variable" x "is not a ""near"" variable".
Ltac near_skip :=
  match goal with |- locked_with near_key (forall _, @PropInFilter.t _ _ ?P _ -> _) =>
    tryif is_evar P then fail "nothing to skip" else apply: near_skip_subproof end.

Tactic Notation "near:" ident(x) :=
  just_discharge_near x;
  tryif do ![apply: near_acc; first shelve|near_skip]
  then idtac
  else fail "the goal depends on variables introduced after" x.

Ltac end_near := do ?exact: in_filterT.

Module Export Topological.

Record mixin_of (T : Type) (nbhs : T -> set (set T)) := Mixin {
  open : set (set T) ;
  nbhs_pfilter : forall p : T, ProperFilter (nbhs p) ;
  nbhsE : forall p : T, nbhs p =
    [set A : set T | exists B : set T, [/\ open B, B p & B `<=` A] ] ;
  openE : open = [set A : set T | A `<=` nbhs^~ A ]
}.

Record class_of (T : Type) := Class {
  base : Filtered.class_of T T;
  mixin : mixin_of (Filtered.nbhs_op base)
}.

Section ClassDef.

Structure type := Pack { sort; _ : class_of sort }.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c := cT return class_of cT in c.

Definition pack nbhs' (m : @mixin_of T nbhs') :=
  fun bT (b : Filtered.class_of T T) of phant_id (@Filtered.class T bT) b =>
  fun m'   of phant_id m (m' : @mixin_of T (Filtered.nbhs_op b)) =>
  @Pack T (@Class _ b m').

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> Filtered.class_of.
Coercion mixin : class_of >-> mixin_of.
Notation topologicalType := type.
Notation TopologicalType T m := (@pack T _ m _ _ idfun _ idfun).

End Exports.

End Topological.

Section TopologyOfFilter.

Context {T : Type} {nbhs' : T -> set (set T)}.
Hypothesis (nbhs'_filter : forall p : T, ProperFilter (nbhs' p)).
Hypothesis (nbhs'_singleton : forall (p : T) (A : set T), nbhs' p A -> A p).
Hypothesis (nbhs'_nbhs' : forall (p : T) (A : set T), nbhs' p A -> nbhs' p (nbhs'^~ A)).

Definition open_of_nbhs := [set A : set T | A `<=` nbhs'^~ A].

Program Definition topologyOfFilterMixin : Topological.mixin_of nbhs' :=
  @Topological.Mixin T nbhs' open_of_nbhs _ _ _.
Admit Obligations.

End TopologyOfFilter.

Local Notation "A ^-1" := ([set xy | A (xy.2, xy.1)]) : classical_set_scope.

Local Notation "'to_set' A x" := ([set y | A (x, y)])
  (at level 0, A at level 0) : classical_set_scope.

Definition nbhs_ {T T'} (ent : set (set (T * T'))) (x : T) :=
  filter_from ent (fun A => to_set A x).

Module Export Uniform.

Record mixin_of (M : Type) (nbhs : M -> set (set M)) := Mixin {
  entourage : (M * M -> Prop) -> Prop ;
  entourage_filter : Filter entourage ;
  entourage_refl : forall A, entourage A -> [set xy | xy.1 = xy.2] `<=` A ;
  entourage_inv : forall A, entourage A -> entourage (A^-1)%classic ;
  entourage_split_ex :
    forall A, entourage A -> exists2 B, entourage B & B \; B `<=` A ;
  nbhsE : nbhs = nbhs_ entourage
}.

Record class_of (M : Type) := Class {
  base : Topological.class_of M;
  mixin : mixin_of (Filtered.nbhs_op base)
}.

Section ClassDef.

Structure type := Pack { sort; _ : class_of sort }.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c := cT return class_of cT in c.

Definition pack nbhs (m : @mixin_of T nbhs) :=
  fun bT (b : Topological.class_of T) of phant_id (@Topological.class bT) b =>
  fun m'   of phant_id m (m' : @mixin_of T (Filtered.nbhs_op b)) =>
  @Pack T (@Class _ b m').

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> Topological.class_of.
Coercion mixin : class_of >-> mixin_of.
Notation uniformType := type.
Notation UniformType T m := (@pack T _ m _ _ idfun _ idfun).
Notation UniformMixin := Mixin.

End Exports.

End Uniform.

Section UniformTopology.

Program Definition topologyOfEntourageMixin (T : Type)
  (nbhs : T -> set (set T)) (m : Uniform.mixin_of nbhs) :
  Topological.mixin_of nbhs := topologyOfFilterMixin _ _ _.
Admit Obligations.

End UniformTopology.

Definition entourage_ {R : numDomainType} {T T'} (ball : T -> R -> set T') :=
  @filter_from R _ [set x | 0 < x] (fun e => [set xy | ball xy.1 e xy.2]).

Module Export PseudoMetric.

Record mixin_of (R : numDomainType) (M : Type)
    (entourage : set (set (M * M))) := Mixin {
  ball : M -> R -> M -> Prop ;
  ball_center : forall x (e : R), 0 < e -> ball x e x ;
  ball_sym : forall x y (e : R), ball x e y -> ball y e x ;
  ball_triangle :
    forall x y z e1 e2, ball x e1 y -> ball y e2 z -> ball x (e1 + e2) z;
  entourageE : entourage = entourage_ ball
}.

Record class_of (R : numDomainType) (M : Type) := Class {
  base : Uniform.class_of M;
  mixin : mixin_of R (Uniform.entourage base)
}.

Section ClassDef.
Variable R : numDomainType.
Structure type := Pack { sort; _ : class_of R sort }.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c := cT return class_of R cT in c.

Definition clone c of phant_id class c := @Pack T c.

Definition pack ent (m : @mixin_of R T ent) :=
  fun bT (b : Uniform.class_of T) of phant_id (@Uniform.class bT) b =>
  fun m'   of phant_id m (m' : @mixin_of R T (Uniform.entourage b)) =>
  @Pack T (@Class R _ b m').

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> Uniform.class_of.
Coercion mixin : class_of >-> mixin_of.
Notation pseudoMetricType := type.
Notation PseudoMetricType T m := (@pack _ T _ m _ _ idfun _ idfun).
Notation PseudoMetricMixin := Mixin.
Notation "[ 'pseudoMetricType' R 'of' T 'for' cT ]" := (@clone R T cT _ idfun)
  (at level 0, format "[ 'pseudoMetricType'  R  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'pseudoMetricType' R 'of' T ]" := (@clone R T _ _ id)
  (at level 0, format "[ 'pseudoMetricType'  R  'of'  T ]") : form_scope.

End Exports.

End PseudoMetric.

Section PseudoMetricUniformity.

Program Definition uniformityOfBallMixin (R : numFieldType) (T : Type)
  (ent : set (set (T * T))) (nbhs : T -> set (set T)) (nbhsE : nbhs = nbhs_ ent)
  (m : PseudoMetric.mixin_of R ent) : Uniform.mixin_of nbhs :=
  UniformMixin _ _ _ _ nbhsE.
Admit Obligations.

End PseudoMetricUniformity.

Definition ball {R : numDomainType} {M : pseudoMetricType R} :=
  PseudoMetric.ball (PseudoMetric.class M).

Definition nbhs_ball_ {R : numDomainType} {T T'} (ball : T -> R -> set T')
  (x : T) := @filter_from R _ [set e | e > 0] (ball x).

Definition pointed_of_zmodule (R : zmodType) : pointedType.
exact (PointedType R 0).
Defined.

Definition ball_
  (R : numDomainType) (V : zmodType) (norm : V -> R) (x : V) (e : R) :=
  [set y | norm (x - y) < e].
Definition filtered_of_normedZmod (K : numDomainType) (R : normedZmodType K)
  : filteredType R.
exact (Filtered.Pack (Filtered.Class
    (@Pointed.class (pointed_of_zmodule R))
    (nbhs_ball_ (ball_ (fun x => `|x|))))).
Defined.

Section pseudoMetric_of_normedDomain.
Variables (K : numDomainType) (R : normedZmodType K).
Lemma ball_norm_center (x : R) (e : K) : 0 < e -> ball_ Num.norm x e x.
Admitted.
Lemma ball_norm_symmetric (x y : R) (e : K) :
  ball_ Num.norm x e y -> ball_ Num.norm y e x.
Admitted.
Lemma ball_norm_triangle (x y z : R) (e1 e2 : K) :
  ball_ Num.norm x e1 y -> ball_ Num.norm y e2 z -> ball_ Num.norm x (e1 + e2) z.
Admitted.
Definition pseudoMetric_of_normedDomain
  : PseudoMetric.mixin_of K (@entourage_ K R R (ball_ (fun x => `|x|))).
exact (PseudoMetricMixin ball_norm_center ball_norm_symmetric ball_norm_triangle erefl).
Defined.
Lemma nbhs_ball_normE :
  @nbhs_ball_ K R R (ball_ Num.norm) = nbhs_ (entourage_ (ball_ Num.norm)).
Admitted.
End pseudoMetric_of_normedDomain.

Module Export regular_topology.

Section regular_topology.
Local Canonical filteredType (R : numDomainType) : filteredType R.
exact ([filteredType R of R^o for filtered_of_normedZmod R]).
Defined.
Local Canonical topologicalType (R : numFieldType) : topologicalType.
exact (TopologicalType R^o (topologyOfEntourageMixin (uniformityOfBallMixin
      (@nbhs_ball_normE _ _) (pseudoMetric_of_normedDomain _)))).
Defined.
Local Canonical uniformType (R : numFieldType) : uniformType.
exact (UniformType R^o (uniformityOfBallMixin
                     (@nbhs_ball_normE _ _) (pseudoMetric_of_normedDomain _))).
Defined.
Local Canonical pseudoMetricType (R : numFieldType) :=
  PseudoMetricType R^o (@pseudoMetric_of_normedDomain R R).
End regular_topology.

Module Export Exports.
Canonical pseudoMetricType.
End Exports.

End regular_topology.

Module Export numFieldTopology.

Section numFieldType.
Variable (R : numFieldType).
Local Canonical numField_pseudoMetricType :=
  [pseudoMetricType R of R for [pseudoMetricType R of R^o]].
End numFieldType.

Module Export Exports.
Coercion numField_pseudoMetricType : numFieldType >-> pseudoMetricType.
End Exports.

End numFieldTopology.

End topology.

Module Export PseudoMetricNormedZmodule.
Section ClassDef.
Variable R : numDomainType.
Record mixin_of (T : normedZmodType R) (ent : set (set (T * T)))
    (m : PseudoMetric.mixin_of R ent) := Mixin {
  _ : PseudoMetric.ball m = ball_ (fun x => `| x |) }.

Record class_of (T : Type) := Class {
  base : Num.NormedZmodule.class_of R T;
  pointed_mixin : Pointed.point_of T ;
  nbhs_mixin : Filtered.nbhs_of T T ;
  topological_mixin : @Topological.mixin_of T nbhs_mixin ;
  uniform_mixin : @Uniform.mixin_of T nbhs_mixin ;
  pseudoMetric_mixin :
    @PseudoMetric.mixin_of R T (Uniform.entourage uniform_mixin) ;
  mixin : @mixin_of (Num.NormedZmodule.Pack _ base) _ pseudoMetric_mixin
}.
Local Coercion base : class_of >-> Num.NormedZmodule.class_of.

Structure type (phR : phant R) :=
  Pack { sort; _ : class_of sort }.
Local Coercion sort : type >-> Sortclass.

Variables (phR : phant R) (T : Type) (cT : type phR).

Definition class := let: Pack _ c := cT return class_of cT in c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).
Definition pack (b0 : Num.NormedZmodule.class_of R T) lm0 um0
  (m0 : @mixin_of (@Num.NormedZmodule.Pack R (Phant R) T b0) lm0 um0) :=
  fun bT (b : Num.NormedZmodule.class_of R T)
      & phant_id (@Num.NormedZmodule.class R (Phant R) bT) b =>
  fun uT (u : PseudoMetric.class_of R T) & phant_id (@PseudoMetric.class R uT) u =>
  fun (m : @mixin_of (Num.NormedZmodule.Pack _ b) _ u) & phant_id m m0 =>
  @Pack phR T (@Class T b u u u u u m).
Definition zmodType := @GRing.Zmodule.Pack cT xclass.
Definition normedZmodType := @Num.NormedZmodule.Pack R phR cT xclass.

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> Num.NormedZmodule.class_of.
Coercion sort : type >-> Sortclass.
Canonical zmodType.
Canonical normedZmodType.
Notation pseudoMetricNormedZmodType R := (type (Phant R)).
Notation PseudoMetricNormedZmodType R T m :=
  (@pack _ (Phant R) T _ _ _ m _ _ idfun _ _ idfun _ idfun).
End Exports.

End PseudoMetricNormedZmodule.

Record mixin_of (K : numDomainType)
  (V : pseudoMetricNormedZmodType K) (scale : K -> V -> V) := Mixin {
  _ : forall (l : K) (x : V), `| scale l x | = `| l | * `| x |;
}.

Section ClassDef.

Variable K : numDomainType.

Record class_of (T : Type) := Class {
  base : PseudoMetricNormedZmodule.class_of K T ;
  lmodmixin : GRing.Lmodule.mixin_of K (GRing.Zmodule.Pack base) ;
  mixin : @mixin_of K (PseudoMetricNormedZmodule.Pack (Phant K) base)
                      (GRing.Lmodule.scale lmodmixin)
}.
Local Coercion base : class_of >-> PseudoMetricNormedZmodule.class_of.

Structure type (phK : phant K) :=
  Pack { sort; _ : class_of sort }.
Local Coercion sort : type >-> Sortclass.

Variables (phK : phant K) (T : Type) (cT : type phK).

Definition class := let: Pack _ c := cT return class_of cT in c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack b0 l0
                (m0 : @mixin_of K (@PseudoMetricNormedZmodule.Pack K (Phant K) T b0)
                                (GRing.Lmodule.scale l0)) :=
  fun bT b & phant_id (@PseudoMetricNormedZmodule.class K (Phant K) bT) b =>
  fun l & phant_id l0 l =>
  fun m & phant_id m0 m => Pack phK (@Class T b l m).
Definition zmodType := @GRing.Zmodule.Pack cT xclass.
Definition normedZmodType := @Num.NormedZmodule.Pack K phK cT xclass.
End ClassDef.
Coercion sort : type >-> Sortclass.
Canonical zmodType.
Canonical normedZmodType.
Notation normedModType K := (type (Phant K)).
Notation NormedModType K T m := (@pack _ (Phant K) T _ _ m _ _ idfun _ idfun _ idfun).
Notation NormedModMixin := Mixin.

Module Export regular_topology.

Section regular_topology.
Local Canonical pseudoMetricNormedZmodType (R : numFieldType) :=
  @PseudoMetricNormedZmodType
    R R^o
    (PseudoMetricNormedZmodule.Mixin (erefl : @ball _ R = ball_ Num.norm)).
Local Canonical normedModType (R : numFieldType) :=
  NormedModType R R^o (@NormedModMixin _ _ ( *:%R : R -> R^o -> _) (@normrM _)).
End regular_topology.

Module Export Exports.
Canonical normedModType.
End Exports.

End regular_topology.
Import GRing.Theory.

Reserved Notation "{o_ F f }" (at level 0, F at level 0, format "{o_ F  f }").

Reserved Notation "[o_ x e 'of' f ]" (at level 0, x, e at level 0, only parsing).
Reserved Notation "f '=o_' F h"
  (at level 70, no associativity,
   F at level 0, h at next level,
   format "f  '=o_' F  h").
Definition the_tag : unit.
Admitted.
Definition gen_tag : unit.
Admitted.

Section Domination.
Context {K : numDomainType} {T : Type} {V W : normedModType K}.

Let littleo_def (F : set (set T)) (f : T -> V) (g : T -> W) :=
  forall eps, 0 < eps -> \forall x \near F, `|f x| <= eps * `|g x|.

Structure littleo_type (F : set (set T)) (g : T -> W) := Littleo {
  littleo_fun :> T -> V;
  _ : `[< littleo_def F littleo_fun g >]
}.
Notation "{o_ F f }" := (littleo_type F f).

Canonical littleo_subtype (F : set (set T)) (g : T -> W) :=
  [subType for (@littleo_fun F g)].

Lemma littleo_class (F : set (set T)) (g : T -> W) (f : {o_F g}) :
  `[< littleo_def F f g >].
Admitted.

Definition littleo_clone (F : set (set T)) (g : T -> W) (f : T -> V) (fT : {o_F g}) c
  of phant_id (littleo_class fT) c := @Littleo F g f c.
Notation "[littleo 'of' f ]" := (@littleo_clone _ _ f _ _ idfun).

Lemma littleo0_subproof F (g : T -> W) :
  Filter F -> littleo_def F (0 : T -> V) g.
Admitted.

Canonical littleo0 (F : filter_on T) g :=
  Littleo (asboolT (@littleo0_subproof F g _)).

Definition the_littleo (_ : unit) (F : filter_on T)
  (phF : phantom (set (set T)) F) f h := littleo_fun (insubd (littleo0 F h) f).
Arguments the_littleo : simpl never, clear implicits.

Lemma littleoE (tag : unit) (F : filter_on T)
   (phF : phantom (set (set T)) F) f h :
   littleo_def F f h -> the_littleo tag F phF f h = f.
Admitted.

Canonical the_littleo_littleo (tag : unit) (F : filter_on T)
  (phF : phantom (set (set T)) F) f h := [littleo of the_littleo tag F phF f h].

Variant littleo_spec (F : set (set T)) (g : T -> W) : (T -> V) -> Type :=
  LittleoSpec f of littleo_def F f g : littleo_spec F g f.

Lemma littleo (F : set (set T)) (g : T -> W) (f : {o_F g}) : littleo_spec F g f.
Admitted.

End Domination.

Arguments the_littleo {_ _ _ _} _ _ _ _ _ : simpl never.
Local Notation PhantomF x := (Phantom _ [filter of x]).

Notation mklittleo tag x := (the_littleo tag _ (PhantomF x)).

Notation "[o_ x e 'of' f ]" := (mklittleo gen_tag x f e).
Notation "f '=o_' F h" := (f%function = (mklittleo the_tag F f h)).

Variables (R : rcfType) (pT : pointedType).

Lemma mulo (F : filter_on pT) (h1 h2 f g : pT -> R^o) :
  [o_F h1 of f] * [o_F h2 of g] =o_F (h1 * h2).
Proof.
rewrite [in RHS]littleoE // => _/posnumP[e]; near=> x.
rewrite [`|_|]normrM -(sqr_sqrtr (ge0 e)) expr2.
rewrite (@normrM _ (h1 x) (h2 x)) mulrACA ler_pmul //; near: x;
by have [/= h] := littleo; apply.
Unshelve.
all: by end_near.
Qed.
