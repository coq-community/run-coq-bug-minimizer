(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "-projection-no-head-constant" "-w" "-redundant-canonical-projection" "-w" "-notation-overridden" "-w" "+duplicate-clear" "-w" "-ambiguous-paths" "-w" "+non-primitive-record" "-w" "+undeclared-scope" "-w" "-deprecated-hint-without-locality" "-w" "-deprecated-ident-entry" "-w" "-deprecated-native-compiler-option" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/mathcomp/mathcomp" "mathcomp" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-I" "/github/workspace/builds/coq/coq-failing/_build_ci/mathcomp/mathcomp" "-top" "bug_01" "-native-compiler" "ondemand") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 5928 lines to 3548 lines, then from 3193 lines to 243 lines, then from 256 lines to 2271 lines, then from 2276 lines to 354 lines, then from 367 lines to 3632 lines, then from 3636 lines to 378 lines, then from 391 lines to 3219 lines, then from 3224 lines to 1994 lines, then from 1866 lines to 544 lines, then from 557 lines to 3736 lines, then from 3741 lines to 575 lines, then from 588 lines to 5227 lines, then from 5232 lines to 5524 lines, then from 5216 lines to 999 lines, then from 1012 lines to 1438 lines, then from 1443 lines to 1030 lines, then from 1043 lines to 1818 lines, then from 1823 lines to 1153 lines, then from 1166 lines to 4273 lines, then from 4278 lines to 2340 lines, then from 2121 lines to 1282 lines, then from 1295 lines to 7959 lines, then from 7964 lines to 6665 lines, then from 6004 lines to 1976 lines, then from 1989 lines to 4548 lines, then from 4552 lines to 4757 lines *)
(* coqc version 8.15+alpha compiled with OCaml 4.13.0
   coqtop version runner-z3wu8uu--project-6138686-concurrent-0:/builds/coq/coq/_build/default,(HEAD detached at 0d1a2eb) (0d1a2eb7ba6a7719f37495807fb9fa49623ac075)
   Expected coqc runtime on this file: 5.276 sec *)
Require Coq.ssr.ssreflect.
Require mathcomp.ssreflect.ssreflect.
Require Coq.ssr.ssrfun.
Require mathcomp.ssreflect.ssrnotations.
Require mathcomp.ssreflect.ssrfun.
Require Coq.ssr.ssrbool.
Require mathcomp.ssreflect.ssrbool.
Require mathcomp.ssreflect.eqtype.
Require Coq.NArith.BinNat.
Require Coq.PArith.BinPos.
Require Coq.NArith.Ndec.
Require Coq.setoid_ring.Ring.
Require mathcomp.ssreflect.ssrnat.
Require mathcomp.ssreflect.seq.
Require mathcomp.ssreflect.div.
Require mathcomp.ssreflect.choice.
Require mathcomp.ssreflect.path.
Require mathcomp.ssreflect.fintype.
Require mathcomp.ssreflect.tuple.
Require mathcomp.ssreflect.finfun.
Require mathcomp.ssreflect.bigop.

Declare ML Module "ltac_plugin".
Module Export AdmitTactic.
Module Import LocalFalse.
Inductive False : Prop := .
End LocalFalse.
Axiom proof_admitted : False.
Global Set Default Proof Mode "Classic".
Tactic Notation "admit" := abstract case proof_admitted.
End AdmitTactic.

Module mathcomp_DOT_ssreflect_DOT_finset_WRAPPED.
Module finset.
 
 
Import mathcomp.ssreflect.ssreflect mathcomp.ssreflect.ssrbool mathcomp.ssreflect.ssrfun mathcomp.ssreflect.eqtype mathcomp.ssreflect.ssrnat mathcomp.ssreflect.div mathcomp.ssreflect.seq.
Import mathcomp.ssreflect.choice mathcomp.ssreflect.fintype mathcomp.ssreflect.finfun mathcomp.ssreflect.bigop.

 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope set_scope.

Section SetType.

Variable T : finType.

Inductive set_type : predArgType := FinSet of {ffun pred T}.
Definition finfun_of_set A := let: FinSet f := A in f.
Definition set_of of phant T := set_type.
Identity Coercion type_of_set_of : set_of >-> set_type.

Canonical set_subType := Eval hnf in [newType for finfun_of_set].
Definition set_eqMixin := Eval hnf in [eqMixin of set_type by <:].
Canonical set_eqType := Eval hnf in EqType set_type set_eqMixin.
Definition set_choiceMixin := [choiceMixin of set_type by <:].
Canonical set_choiceType := Eval hnf in ChoiceType set_type set_choiceMixin.
Definition set_countMixin := [countMixin of set_type by <:].
Canonical set_countType := Eval hnf in CountType set_type set_countMixin.
Canonical set_subCountType := Eval hnf in [subCountType of set_type].
Definition set_finMixin := [finMixin of set_type by <:].
Canonical set_finType := Eval hnf in FinType set_type set_finMixin.
Canonical set_subFinType := Eval hnf in [subFinType of set_type].

End SetType.

Delimit Scope set_scope with SET.
Bind Scope set_scope with set_type.
Bind Scope set_scope with set_of.
Open Scope set_scope.
Arguments finfun_of_set {T} A%SET.

Notation "{ 'set' T }" := (set_of (Phant T))
  (at level 0, format "{ 'set'  T }") : type_scope.

 
 
 
 
 
Notation "A :=: B" := (A = B :> {set _})
  (at level 70, no associativity, only parsing) : set_scope.
Notation "A :<>: B" := (A <> B :> {set _})
  (at level 70, no associativity, only parsing) : set_scope.
Notation "A :==: B" := (A == B :> {set _})
  (at level 70, no associativity, only parsing) : set_scope.
Notation "A :!=: B" := (A != B :> {set _})
  (at level 70, no associativity, only parsing) : set_scope.
Notation "A :=P: B" := (A =P B :> {set _})
  (at level 70, no associativity, only parsing) : set_scope.

Local Notation finset_def := (fun T P => @FinSet T (finfun P)).

Local Notation pred_of_set_def := (fun T (A : set_type T) => val A : _ -> _).

Module Type SetDefSig.
Parameter finset : forall T : finType, pred T -> {set T}.
Parameter pred_of_set : forall T, set_type T -> fin_pred_sort (predPredType T).
 
 
 
 
Axiom finsetE : finset = finset_def.
Axiom pred_of_setE : pred_of_set = pred_of_set_def.
End SetDefSig.

Module SetDef : SetDefSig.
Definition finset := finset_def.
Definition pred_of_set := pred_of_set_def.
Lemma finsetE : finset = finset_def.
Proof.
by [].
Qed.
Lemma pred_of_setE : pred_of_set = pred_of_set_def.
Proof.
by [].
Qed.
End SetDef.

Notation finset := SetDef.finset.
Notation pred_of_set := SetDef.pred_of_set.
Canonical finset_unlock := Unlockable SetDef.finsetE.
Canonical pred_of_set_unlock := Unlockable SetDef.pred_of_setE.

Notation "[ 'set' x : T | P ]" := (finset (fun x : T => P%B))
  (at level 0, x at level 99, only parsing) : set_scope.
Notation "[ 'set' x | P ]" := [set x : _ | P]
  (at level 0, x, P at level 99, format "[ 'set'  x  |  P ]") : set_scope.
Notation "[ 'set' x 'in' A ]" := [set x | x \in A]
  (at level 0, x at level 99, format "[ 'set'  x  'in'  A ]") : set_scope.
Notation "[ 'set' x : T 'in' A ]" := [set x : T | x \in A]
  (at level 0, x at level 99, only parsing) : set_scope.
Notation "[ 'set' x : T | P & Q ]" := [set x : T | P && Q]
  (at level 0, x at level 99, only parsing) : set_scope.
Notation "[ 'set' x | P & Q ]" := [set x | P && Q ]
  (at level 0, x, P at level 99, format "[ 'set'  x  |  P  &  Q ]") : set_scope.
Notation "[ 'set' x : T 'in' A | P ]" := [set x : T | x \in A & P]
  (at level 0, x at level 99, only parsing) : set_scope.
Notation "[ 'set' x 'in' A | P ]" := [set x | x \in A & P]
  (at level 0, x at level 99, format "[ 'set'  x  'in'  A  |  P ]") : set_scope.
Notation "[ 'set' x 'in' A | P & Q ]" := [set x in A | P && Q]
  (at level 0, x at level 99,
   format "[ 'set'  x  'in'  A  |  P  &  Q ]") : set_scope.
Notation "[ 'set' x : T 'in' A | P & Q ]" := [set x : T in A | P && Q]
  (at level 0, x at level 99, only parsing) : set_scope.

 
 
Coercion pred_of_set: set_type >-> fin_pred_sort.

 
 
Canonical set_predType T := @PredType _ (unkeyed (set_type T)) (@pred_of_set T).

Section BasicSetTheory.

Variable T : finType.
Implicit Types (x : T) (A B : {set T}) (pA : pred T).

Canonical set_of_subType := Eval hnf in [subType of {set T}].
Canonical set_of_eqType := Eval hnf in [eqType of {set T}].
Canonical set_of_choiceType := Eval hnf in [choiceType of {set T}].
Canonical set_of_countType := Eval hnf in [countType of {set T}].
Canonical set_of_subCountType := Eval hnf in [subCountType of {set T}].
Canonical set_of_finType := Eval hnf in [finType of {set T}].
Canonical set_of_subFinType := Eval hnf in [subFinType of {set T}].

Lemma in_set pA x : x \in finset pA = pA x.
Proof.
by rewrite [@finset]unlock unlock [x \in _]ffunE.
Qed.

Lemma setP A B : A =i B <-> A = B.
Proof.
by split=> [eqAB|-> //]; apply/val_inj/ffunP=> x; have:= eqAB x; rewrite unlock.
Qed.

Definition set0 := [set x : T | false].
Definition setTfor (phT : phant T) := [set x : T | true].

Lemma in_setT x : x \in setTfor (Phant T).
Proof.
by rewrite in_set.
Qed.

Lemma eqsVneq A B : eq_xor_neq A B (B == A) (A == B).
Proof.
exact: eqVneq.
Qed.

Lemma eq_finset (pA pB : pred T) : pA =1 pB -> finset pA = finset pB.
Proof.
by move=> eq_p; apply/setP => x; rewrite !(in_set, inE) eq_p.
Qed.

End BasicSetTheory.

Arguments eqsVneq {T} A B, {T A B}.

Definition inE := (in_set, inE).

Arguments set0 {T}.
Arguments eq_finset {T} [pA] pB eq_pAB.
Hint Resolve in_setT : core.

Notation "[ 'set' : T ]" := (setTfor (Phant T))
  (at level 0, format "[ 'set' :  T ]") : set_scope.

Notation setT := [set: _] (only parsing).

Section setOpsDefs.

Variable T : finType.
Implicit Types (a x : T) (A B D : {set T}) (P : {set {set T}}).

Definition set1 a := [set x | x == a].
Definition setU A B := [set x | (x \in A) || (x \in B)].
Definition setI A B := [set x in A | x \in B].
Definition setC A := [set x | x \notin A].
Definition setD A B := [set x | x \notin B & x \in A].
Definition ssetI P D := [set A in P | A \subset D].
Definition powerset D := [set A : {set T} | A \subset D].

End setOpsDefs.

Notation "[ 'set' a ]" := (set1 a)
  (at level 0, a at level 99, format "[ 'set'  a ]") : set_scope.
Notation "[ 'set' a : T ]" := [set (a : T)]
  (at level 0, a at level 99, format "[ 'set'  a   :  T ]") : set_scope.
Notation "A :|: B" := (setU A B) : set_scope.
Notation "a |: A" := ([set a] :|: A) : set_scope.
 
Notation "[ 'set' a1 ; a2 ; .. ; an ]" := (setU .. (a1 |: [set a2]) .. [set an])
  (at level 0, a1 at level 99,
   format "[ 'set'  a1 ;  a2 ;  .. ;  an ]") : set_scope.
Notation "A :&: B" := (setI A B) : set_scope.
Notation "~: A" := (setC A) (at level 35, right associativity) : set_scope.
Notation "[ 'set' ~ a ]" := (~: [set a])
  (at level 0, format "[ 'set' ~  a ]") : set_scope.
Notation "A :\: B" := (setD A B) : set_scope.
Notation "A :\ a" := (A :\: [set a]) : set_scope.
Notation "P ::&: D" := (ssetI P D) (at level 48) : set_scope.

Section setOps.

Variable T : finType.
Implicit Types (a x : T) (A B C D : {set T}) (pA pB pC : pred T).

Lemma eqEsubset A B : (A == B) = (A \subset B) && (B \subset A).
Proof.
by apply/eqP/subset_eqP=> /setP.
Qed.

Lemma subEproper A B : A \subset B = (A == B) || (A \proper B).
Proof.
by rewrite eqEsubset -andb_orr orbN andbT.
Qed.

Lemma eqVproper A B : A \subset B -> A = B \/ A \proper B.
Proof.
by rewrite subEproper => /predU1P.
Qed.

Lemma properEneq A B : A \proper B = (A != B) && (A \subset B).
Proof.
by rewrite andbC eqEsubset negb_and andb_orr andbN.
Qed.

Lemma proper_neq A B : A \proper B -> A != B.
Proof.
by rewrite properEneq; case/andP.
Qed.

Lemma eqEproper A B : (A == B) = (A \subset B) && ~~ (A \proper B).
Proof.
by rewrite negb_and negbK andb_orr andbN eqEsubset.
Qed.

Lemma eqEcard A B : (A == B) = (A \subset B) && (#|B| <= #|A|).
Proof.
rewrite eqEsubset; apply: andb_id2l => sAB.
by rewrite (geq_leqif (subset_leqif_card sAB)).
Qed.

Lemma properEcard A B : (A \proper B) = (A \subset B) && (#|A| < #|B|).
Proof.
by rewrite properEneq ltnNge andbC eqEcard; case: (A \subset B).
Qed.

Lemma subset_leqif_cards A B : A \subset B -> (#|A| <= #|B| ?= iff (A == B)).
Proof.
by move=> sAB; rewrite eqEsubset sAB; apply: subset_leqif_card.
Qed.

Lemma in_set0 x : x \in set0 = false.
Proof.
by rewrite inE.
Qed.

Lemma sub0set A : set0 \subset A.
Proof.
by apply/subsetP=> x; rewrite inE.
Qed.

Lemma subset0 A : (A \subset set0) = (A == set0).
Proof.
by rewrite eqEsubset sub0set andbT.
Qed.

Lemma proper0 A : (set0 \proper A) = (A != set0).
Proof.
by rewrite properE sub0set subset0.
Qed.

Lemma subset_neq0 A B : A \subset B -> A != set0 -> B != set0.
Proof.
by rewrite -!proper0 => sAB /proper_sub_trans->.
Qed.

Lemma set_0Vmem A : (A = set0) + {x : T | x \in A}.
Proof.
case: (pickP (mem A)) => [x Ax | A0]; [by right; exists x | left].
by apply/setP=> x; rewrite inE; apply: A0.
Qed.

Lemma set_enum A : [set x | x \in enum A] = A.
Proof.
by apply/setP => x; rewrite inE mem_enum.
Qed.

Lemma enum_set0 : enum set0 = [::] :> seq T.
Proof.
by rewrite (eq_enum (in_set _)) enum0.
Qed.

Lemma subsetT A : A \subset setT.
Proof.
by apply/subsetP=> x; rewrite inE.
Qed.

Lemma subsetT_hint mA : subset mA (mem [set: T]).
Proof.
by rewrite unlock; apply/pred0P=> x; rewrite !inE.
Qed.
Hint Resolve subsetT_hint : core.

Lemma subTset A : (setT \subset A) = (A == setT).
Proof.
by rewrite eqEsubset subsetT.
Qed.

Lemma properT A : (A \proper setT) = (A != setT).
Proof.
by rewrite properEneq subsetT andbT.
Qed.

Lemma set1P x a : reflect (x = a) (x \in [set a]).
Proof.
by rewrite inE; apply: eqP.
Qed.

Lemma enum_setT : enum [set: T] = Finite.enum T.
Proof.
by rewrite (eq_enum (in_set _)) enumT.
Qed.

Lemma in_set1 x a : (x \in [set a]) = (x == a).
Proof.
exact: in_set.
Qed.

Lemma set11 x : x \in [set x].
Proof.
by rewrite inE.
Qed.

Lemma set1_inj : injective (@set1 T).
Proof.
by move=> a b eqsab; apply/set1P; rewrite -eqsab set11.
Qed.

Lemma enum_set1 a : enum [set a] = [:: a].
Proof.
by rewrite (eq_enum (in_set _)) enum1.
Qed.

Lemma setU1P x a B : reflect (x = a \/ x \in B) (x \in a |: B).
Proof.
by rewrite !inE; apply: predU1P.
Qed.

Lemma in_setU1 x a B : (x \in a |: B) = (x == a) || (x \in B).
Proof.
by rewrite !inE.
Qed.

Lemma set_cons a s : [set x in a :: s] = a |: [set x in s].
Proof.
by apply/setP=> x; rewrite !inE.
Qed.

Lemma setU11 x B : x \in x |: B.
Proof.
by rewrite !inE eqxx.
Qed.

Lemma setU1r x a B : x \in B -> x \in a |: B.
Proof.
by move=> Bx; rewrite !inE predU1r.
Qed.

 
 
Lemma set1Ul x A b : x \in A -> x \in A :|: [set b].
Proof.
by move=> Ax; rewrite !inE Ax.
Qed.

Lemma set1Ur A b : b \in A :|: [set b].
Proof.
by rewrite !inE eqxx orbT.
Qed.

Lemma in_setC1 x a : (x \in [set~ a]) = (x != a).
Proof.
by rewrite !inE.
Qed.

Lemma setC11 x : (x \in [set~ x]) = false.
Proof.
by rewrite !inE eqxx.
Qed.

Lemma setD1P x A b : reflect (x != b /\ x \in A) (x \in A :\ b).
Proof.
by rewrite !inE; apply: andP.
Qed.

Lemma in_setD1 x A b : (x \in A :\ b) = (x != b) && (x \in A) .
Proof.
by rewrite !inE.
Qed.

Lemma setD11 b A : (b \in A :\ b) = false.
Proof.
by rewrite !inE eqxx.
Qed.

Lemma setD1K a A : a \in A -> a |: (A :\ a) = A.
Proof.
by move=> Aa; apply/setP=> x /[!inE]; case: eqP => // ->.
Qed.

Lemma setU1K a B : a \notin B -> (a |: B) :\ a = B.
Proof.
by move/negPf=> nBa; apply/setP=> x /[!inE]; case: eqP => // ->.
Qed.

Lemma set2P x a b : reflect (x = a \/ x = b) (x \in [set a; b]).
Proof.
by rewrite !inE; apply: pred2P.
Qed.

Lemma in_set2 x a b : (x \in [set a; b]) = (x == a) || (x == b).
Proof.
by rewrite !inE.
Qed.

Lemma set21 a b : a \in [set a; b].
Proof.
by rewrite !inE eqxx.
Qed.

Lemma set22 a b : b \in [set a; b].
Proof.
by rewrite !inE eqxx orbT.
Qed.

Lemma setUP x A B : reflect (x \in A \/ x \in B) (x \in A :|: B).
Proof.
by rewrite !inE; apply: orP.
Qed.

Lemma in_setU x A B : (x \in A :|: B) = (x \in A) || (x \in B).
Proof.
exact: in_set.
Qed.

Lemma setUC A B : A :|: B = B :|: A.
Proof.
by apply/setP => x; rewrite !inE orbC.
Qed.

Lemma setUS A B C : A \subset B -> C :|: A \subset C :|: B.
Proof.
move=> sAB; apply/subsetP=> x; rewrite !inE.
by case: (x \in C) => //; apply: (subsetP sAB).
Qed.

Lemma setSU A B C : A \subset B -> A :|: C \subset B :|: C.
Proof.
by move=> sAB; rewrite -!(setUC C) setUS.
Qed.

Lemma setUSS A B C D : A \subset C -> B \subset D -> A :|: B \subset C :|: D.
Proof.
by move=> /(setSU B) /subset_trans sAC /(setUS C)/sAC.
Qed.

Lemma set0U A : set0 :|: A = A.
Proof.
by apply/setP => x; rewrite !inE orFb.
Qed.

Lemma setU0 A : A :|: set0 = A.
Proof.
by rewrite setUC set0U.
Qed.

Lemma setUA A B C : A :|: (B :|: C) = A :|: B :|: C.
Proof.
by apply/setP => x; rewrite !inE orbA.
Qed.

Lemma setUCA A B C : A :|: (B :|: C) = B :|: (A :|: C).
Proof.
by rewrite !setUA (setUC B).
Qed.

Lemma setUAC A B C : A :|: B :|: C = A :|: C :|: B.
Proof.
by rewrite -!setUA (setUC B).
Qed.

Lemma setUACA A B C D : (A :|: B) :|: (C :|: D) = (A :|: C) :|: (B :|: D).
Proof.
by rewrite -!setUA (setUCA B).
Qed.

Lemma setTU A : setT :|: A = setT.
Proof.
by apply/setP => x; rewrite !inE orTb.
Qed.

Lemma setUT A : A :|: setT = setT.
Proof.
by rewrite setUC setTU.
Qed.

Lemma setUid A : A :|: A = A.
Proof.
by apply/setP=> x; rewrite inE orbb.
Qed.

Lemma setUUl A B C : A :|: B :|: C = (A :|: C) :|: (B :|: C).
Proof.
by rewrite setUA !(setUAC _ C) -(setUA _ C) setUid.
Qed.

Lemma setUUr A B C : A :|: (B :|: C) = (A :|: B) :|: (A :|: C).
Proof.
by rewrite !(setUC A) setUUl.
Qed.

 

 
Lemma setIdP x pA pB : reflect (pA x /\ pB x) (x \in [set y | pA y & pB y]).
Proof.
by rewrite !inE; apply: andP.
Qed.

Lemma setId2P x pA pB pC :
  reflect [/\ pA x, pB x & pC x] (x \in [set y | pA y & pB y && pC y]).
Proof.
by rewrite !inE; apply: and3P.
Qed.

Lemma setIdE A pB : [set x in A | pB x] = A :&: [set x | pB x].
Proof.
by apply/setP=> x; rewrite !inE.
Qed.

Lemma setIP x A B : reflect (x \in A /\ x \in B) (x \in A :&: B).
Proof.
exact: (iffP (@setIdP _ _ _)).
Qed.

Lemma in_setI x A B : (x \in A :&: B) = (x \in A) && (x \in B).
Proof.
exact: in_set.
Qed.

Lemma setIC A B : A :&: B = B :&: A.
Proof.
by apply/setP => x; rewrite !inE andbC.
Qed.

Lemma setIS A B C : A \subset B -> C :&: A \subset C :&: B.
Proof.
move=> sAB; apply/subsetP=> x; rewrite !inE.
by case: (x \in C) => //; apply: (subsetP sAB).
Qed.

Lemma setSI A B C : A \subset B -> A :&: C \subset B :&: C.
Proof.
by move=> sAB; rewrite -!(setIC C) setIS.
Qed.

Lemma setISS A B C D : A \subset C -> B \subset D -> A :&: B \subset C :&: D.
Proof.
by move=> /(setSI B) /subset_trans sAC /(setIS C) /sAC.
Qed.

Lemma setTI A : setT :&: A = A.
Proof.
by apply/setP => x; rewrite !inE andTb.
Qed.

Lemma setIT A : A :&: setT = A.
Proof.
by rewrite setIC setTI.
Qed.

Lemma set0I A : set0 :&: A = set0.
Proof.
by apply/setP => x; rewrite !inE andFb.
Qed.

Lemma setI0 A : A :&: set0 = set0.

Proof.
by rewrite setIC set0I.
Qed.

Lemma setIA A B C : A :&: (B :&: C) = A :&: B :&: C.
Proof.
by apply/setP=> x; rewrite !inE andbA.
Qed.

Lemma setICA A B C : A :&: (B :&: C) = B :&: (A :&: C).
Proof.
by rewrite !setIA (setIC A).
Qed.

Lemma setIAC A B C : A :&: B :&: C = A :&: C :&: B.
Proof.
by rewrite -!setIA (setIC B).
Qed.

Lemma setIACA A B C D : (A :&: B) :&: (C :&: D) = (A :&: C) :&: (B :&: D).
Proof.
by rewrite -!setIA (setICA B).
Qed.

Lemma setIid A : A :&: A = A.
Proof.
by apply/setP=> x; rewrite inE andbb.
Qed.

Lemma setIIl A B C : A :&: B :&: C = (A :&: C) :&: (B :&: C).
Proof.
by rewrite setIA !(setIAC _ C) -(setIA _ C) setIid.
Qed.

Lemma setIIr A B C : A :&: (B :&: C) = (A :&: B) :&: (A :&: C).
Proof.
by rewrite !(setIC A) setIIl.
Qed.

 

Lemma setIUr A B C : A :&: (B :|: C) = (A :&: B) :|: (A :&: C).
Proof.
by apply/setP=> x; rewrite !inE andb_orr.
Qed.

Lemma setIUl A B C : (A :|: B) :&: C = (A :&: C) :|: (B :&: C).
Proof.
by apply/setP=> x; rewrite !inE andb_orl.
Qed.

Lemma setUIr A B C : A :|: (B :&: C) = (A :|: B) :&: (A :|: C).
Proof.
by apply/setP=> x; rewrite !inE orb_andr.
Qed.

Lemma setUIl A B C : (A :&: B) :|: C = (A :|: C) :&: (B :|: C).
Proof.
by apply/setP=> x; rewrite !inE orb_andl.
Qed.

Lemma setUK A B : (A :|: B) :&: A = A.
Proof.
by apply/setP=> x; rewrite !inE orbK.
Qed.

Lemma setKU A B : A :&: (B :|: A) = A.
Proof.
by apply/setP=> x; rewrite !inE orKb.
Qed.

Lemma setIK A B : (A :&: B) :|: A = A.
Proof.
by apply/setP=> x; rewrite !inE andbK.
Qed.

Lemma setKI A B : A :|: (B :&: A) = A.
Proof.
by apply/setP=> x; rewrite !inE andKb.
Qed.

 

Lemma setCP x A : reflect (~ x \in A) (x \in ~: A).
Proof.
by rewrite !inE; apply: negP.
Qed.

Lemma in_setC x A : (x \in ~: A) = (x \notin A).
Proof.
exact: in_set.
Qed.

Lemma setCK : involutive (@setC T).
Proof.
by move=> A; apply/setP=> x; rewrite !inE negbK.
Qed.

Lemma setC_inj : injective (@setC T).
Proof.
exact: can_inj setCK.
Qed.

Lemma subsets_disjoint A B : (A \subset B) = [disjoint A & ~: B].
Proof.
by rewrite subset_disjoint; apply: eq_disjoint_r => x; rewrite !inE.
Qed.

Lemma disjoints_subset A B : [disjoint A & B] = (A \subset ~: B).
Proof.
by rewrite subsets_disjoint setCK.
Qed.

Lemma powersetCE A B : (A \in powerset (~: B)) = [disjoint A & B].
Proof.
by rewrite inE disjoints_subset.
Qed.

Lemma setCS A B : (~: A \subset ~: B) = (B \subset A).
Proof.
by rewrite !subsets_disjoint setCK disjoint_sym.
Qed.

Lemma setCU A B : ~: (A :|: B) = ~: A :&: ~: B.
Proof.
by apply/setP=> x; rewrite !inE negb_or.
Qed.

Lemma setCI A B : ~: (A :&: B) = ~: A :|: ~: B.
Proof.
by apply/setP=> x; rewrite !inE negb_and.
Qed.

Lemma setUCr A : A :|: ~: A = setT.
Proof.
by apply/setP=> x; rewrite !inE orbN.
Qed.

Lemma setICr A : A :&: ~: A = set0.
Proof.
by apply/setP=> x; rewrite !inE andbN.
Qed.

Lemma setC0 : ~: set0 = [set: T].
Proof.
by apply/setP=> x; rewrite !inE.
Qed.

Lemma setCT : ~: [set: T] = set0.
Proof.
by rewrite -setC0 setCK.
Qed.

Lemma properC A B : (~: B \proper ~: A) = (A \proper B).
Proof.
by rewrite !properE !setCS.
Qed.

 

Lemma setDP A B x : reflect (x \in A /\ x \notin B) (x \in A :\: B).
Proof.
by rewrite inE andbC; apply: andP.
Qed.

Lemma in_setD A B x : (x \in A :\: B) = (x \notin B) && (x \in A).
Proof.
exact: in_set.
Qed.

Lemma setDE A B : A :\: B = A :&: ~: B.
Proof.
by apply/setP => x; rewrite !inE andbC.
Qed.

Lemma setSD A B C : A \subset B -> A :\: C \subset B :\: C.
Proof.
by rewrite !setDE; apply: setSI.
Qed.

Lemma setDS A B C : A \subset B -> C :\: B \subset C :\: A.
Proof.
by rewrite !setDE -setCS; apply: setIS.
Qed.

Lemma setDSS A B C D : A \subset C -> D \subset B -> A :\: B \subset C :\: D.
Proof.
by move=> /(setSD B) /subset_trans sAC /(setDS C) /sAC.
Qed.

Lemma setD0 A : A :\: set0 = A.
Proof.
by apply/setP=> x; rewrite !inE.
Qed.

Lemma set0D A : set0 :\: A = set0.
Proof.
by apply/setP=> x; rewrite !inE andbF.
Qed.

Lemma setDT A : A :\: setT = set0.
Proof.
by apply/setP=> x; rewrite !inE.
Qed.

Lemma setTD A : setT :\: A = ~: A.
Proof.
by apply/setP=> x; rewrite !inE andbT.
Qed.

Lemma setDv A : A :\: A = set0.
Proof.
by apply/setP=> x; rewrite !inE andNb.
Qed.

Lemma setCD A B : ~: (A :\: B) = ~: A :|: B.
Proof.
by rewrite !setDE setCI setCK.
Qed.

Lemma setID A B : A :&: B :|: A :\: B = A.
Proof.
by rewrite setDE -setIUr setUCr setIT.
Qed.

Lemma setDUl A B C : (A :|: B) :\: C = (A :\: C) :|: (B :\: C).
Proof.
by rewrite !setDE setIUl.
Qed.

Lemma setDUr A B C : A :\: (B :|: C) = (A :\: B) :&: (A :\: C).
Proof.
by rewrite !setDE setCU setIIr.
Qed.

Lemma setDIl A B C : (A :&: B) :\: C = (A :\: C) :&: (B :\: C).
Proof.
by rewrite !setDE setIIl.
Qed.

Lemma setIDA A B C : A :&: (B :\: C) = (A :&: B) :\: C.
Proof.
by rewrite !setDE setIA.
Qed.

Lemma setIDAC A B C : (A :\: B) :&: C = (A :&: C) :\: B.
Proof.
by rewrite !setDE setIAC.
Qed.

Lemma setDIr A B C : A :\: (B :&: C) = (A :\: B) :|: (A :\: C).
Proof.
by rewrite !setDE setCI setIUr.
Qed.

Lemma setDDl A B C : (A :\: B) :\: C = A :\: (B :|: C).
Proof.
by rewrite !setDE setCU setIA.
Qed.

Lemma setDDr A B C : A :\: (B :\: C) = (A :\: B) :|: (A :&: C).
Proof.
by rewrite !setDE setCI setIUr setCK.
Qed.

 

Lemma powersetE A B : (A \in powerset B) = (A \subset B).
Proof.
by rewrite inE.
Qed.

Lemma powersetS A B : (powerset A \subset powerset B) = (A \subset B).
Proof.
apply/subsetP/idP=> [sAB | sAB C /[!inE]/subset_trans->//].
by rewrite -powersetE sAB // inE.
Qed.

Lemma powerset0 : powerset set0 = [set set0] :> {set {set T}}.
Proof.
by apply/setP=> A; rewrite !inE subset0.
Qed.

Lemma powersetT : powerset [set: T] = [set: {set T}].
Proof.
by apply/setP=> A; rewrite !inE subsetT.
Qed.

Lemma setI_powerset P A : P :&: powerset A = P ::&: A.
Proof.
by apply/setP=> B; rewrite !inE.
Qed.

 

Lemma cardsE pA : #|[set x in pA]| = #|pA|.
Proof.
exact/eq_card/in_set.
Qed.

Lemma sum1dep_card pA : \sum_(x | pA x) 1 = #|[set x | pA x]|.
Proof.
by rewrite sum1_card cardsE.
Qed.

Lemma sum_nat_cond_const pA n : \sum_(x | pA x) n = #|[set x | pA x]| * n.
Proof.
by rewrite sum_nat_const cardsE.
Qed.

Lemma cards0 : #|@set0 T| = 0.
Proof.
by rewrite cardsE card0.
Qed.

Lemma cards_eq0 A : (#|A| == 0) = (A == set0).
Proof.
by rewrite (eq_sym A) eqEcard sub0set cards0 leqn0.
Qed.

Lemma set0Pn A : reflect (exists x, x \in A) (A != set0).
Proof.
by rewrite -cards_eq0; apply: existsP.
Qed.

Lemma card_gt0 A : (0 < #|A|) = (A != set0).
Proof.
by rewrite lt0n cards_eq0.
Qed.

Lemma cards0_eq A : #|A| = 0 -> A = set0.
Proof.
by move=> A_0; apply/setP=> x; rewrite inE (card0_eq A_0).
Qed.

Lemma cards1 x : #|[set x]| = 1.
Proof.
by rewrite cardsE card1.
Qed.

Lemma cardsUI A B : #|A :|: B| + #|A :&: B| = #|A| + #|B|.
Proof.
by rewrite !cardsE cardUI.
Qed.

Lemma cardsU A B : #|A :|: B| = (#|A| + #|B| - #|A :&: B|)%N.
Proof.
by rewrite -cardsUI addnK.
Qed.

Lemma cardsI A B : #|A :&: B| = (#|A| + #|B| - #|A :|: B|)%N.
Proof.
by rewrite -cardsUI addKn.
Qed.

Lemma cardsT : #|[set: T]| = #|T|.
Proof.
by rewrite cardsE.
Qed.

Lemma cardsID B A : #|A :&: B| + #|A :\: B| = #|A|.
Proof.
by rewrite !cardsE cardID.
Qed.

Lemma cardsD A B : #|A :\: B| = (#|A| - #|A :&: B|)%N.
Proof.
by rewrite -(cardsID B A) addKn.
Qed.

Lemma cardsC A : #|A| + #|~: A| = #|T|.
Proof.
by rewrite cardsE cardC.
Qed.

Lemma cardsCs A : #|A| = #|T| - #|~: A|.
Proof.
by rewrite -(cardsC A) addnK.
Qed.

Lemma cardsU1 a A : #|a |: A| = (a \notin A) + #|A|.
Proof.
by rewrite -cardU1; apply: eq_card=> x; rewrite !inE.
Qed.

Lemma cards2 a b : #|[set a; b]| = (a != b).+1.
Proof.
by rewrite -card2; apply: eq_card=> x; rewrite !inE.
Qed.

Lemma cardsC1 a : #|[set~ a]| = #|T|.-1.
Proof.
by rewrite -(cardC1 a); apply: eq_card=> x; rewrite !inE.
Qed.

Lemma cardsD1 a A : #|A| = (a \in A) + #|A :\ a|.
Proof.
by rewrite (cardD1 a); congr (_ + _); apply: eq_card => x; rewrite !inE.
Qed.

 

Lemma subsetIl A B : A :&: B \subset A.
Proof.
by apply/subsetP=> x /[!inE] /andP[].
Qed.

Lemma subsetIr A B : A :&: B \subset B.
Proof.
by apply/subsetP=> x /[!inE] /andP[].
Qed.

Lemma subsetUl A B : A \subset A :|: B.
Proof.
by apply/subsetP=> x /[!inE] ->.
Qed.

Lemma subsetUr A B : B \subset A :|: B.
Proof.
by apply/subsetP=> x; rewrite inE orbC => ->.
Qed.

Lemma subsetU1 x A : A \subset x |: A.
Proof.
exact: subsetUr.
Qed.

Lemma subsetDl A B : A :\: B \subset A.
Proof.
by rewrite setDE subsetIl.
Qed.

Lemma subD1set A x : A :\ x \subset A.
Proof.
by rewrite subsetDl.
Qed.

Lemma subsetDr A B : A :\: B \subset ~: B.
Proof.
by rewrite setDE subsetIr.
Qed.

Lemma sub1set A x : ([set x] \subset A) = (x \in A).
Proof.
by rewrite -subset_pred1; apply: eq_subset=> y; rewrite !inE.
Qed.

Variant cards_eq_spec A : seq T -> {set T} -> nat -> Type :=
| CardEq (s : seq T) & uniq s : cards_eq_spec A s [set x | x \in s] (size s).

Lemma cards_eqP A : cards_eq_spec A (enum A) A #|A|.
Proof.
by move: (enum A) (cardE A) (set_enum A) (enum_uniq A) => s -> <-; constructor.
Qed.

Lemma cards1P A : reflect (exists x, A = [set x]) (#|A| == 1).
Proof.
apply: (iffP idP) => [|[x ->]]; last by rewrite cards1.
by have [[|x []]// _] := cards_eqP; exists x; apply/setP => y; rewrite !inE.
Qed.

Lemma cards2P A : reflect (exists x y : T, x != y /\ A = [set x; y])
                          (#|A| == 2).
Proof.
apply: (iffP idP) => [|[x] [y] [xy ->]]; last by rewrite cards2 xy.
have [[|x [|y []]]//=] := cards_eqP; rewrite !inE andbT => neq_xy.
by exists x, y; split=> //; apply/setP => z; rewrite !inE.
Qed.

Lemma subset1 A x : (A \subset [set x]) = (A == [set x]) || (A == set0).
Proof.
rewrite eqEcard cards1 -cards_eq0 orbC andbC.
by case: posnP => // A0; rewrite (cards0_eq A0) sub0set.
Qed.

Lemma powerset1 x : powerset [set x] = [set set0; [set x]].
Proof.
by apply/setP=> A; rewrite !inE subset1 orbC.
Qed.

Lemma setIidPl A B : reflect (A :&: B = A) (A \subset B).
Proof.
apply: (iffP subsetP) => [sAB | <- x /setIP[] //].
by apply/setP=> x /[1!inE]; apply/andb_idr/sAB.
Qed.
Arguments setIidPl {A B}.

Lemma setIidPr A B : reflect (A :&: B = B) (B \subset A).
Proof.
by rewrite setIC; apply: setIidPl.
Qed.

Lemma cardsDS A B : B \subset A -> #|A :\: B| = (#|A| - #|B|)%N.
Proof.
by rewrite cardsD => /setIidPr->.
Qed.

Lemma setUidPl A B : reflect (A :|: B = A) (B \subset A).
Proof.
by rewrite -setCS (sameP setIidPl eqP) -setCU (inj_eq setC_inj); apply: eqP.
Qed.

Lemma setUidPr A B : reflect (A :|: B = B) (A \subset B).
Proof.
by rewrite setUC; apply: setUidPl.
Qed.

Lemma setDidPl A B : reflect (A :\: B = A) [disjoint A & B].
Proof.
by rewrite setDE disjoints_subset; apply: setIidPl.
Qed.

Lemma subIset A B C : (B \subset A) || (C \subset A) -> (B :&: C \subset A).
Proof.
by case/orP; apply: subset_trans; rewrite (subsetIl, subsetIr).
Qed.

Lemma subsetI A B C : (A \subset B :&: C) = (A \subset B) && (A \subset C).
Proof.
rewrite !(sameP setIidPl eqP) setIA; have [-> //|] := eqVneq (A :&: B) A.
by apply: contraNF => /eqP <-; rewrite -setIA -setIIl setIAC.
Qed.

Lemma subsetIP A B C : reflect (A \subset B /\ A \subset C) (A \subset B :&: C).
Proof.
by rewrite subsetI; apply: andP.
Qed.

Lemma subsetIidl A B : (A \subset A :&: B) = (A \subset B).
Proof.
by rewrite subsetI subxx.
Qed.

Lemma subsetIidr A B : (B \subset A :&: B) = (B \subset A).
Proof.
by rewrite setIC subsetIidl.
Qed.

Lemma powersetI A B : powerset (A :&: B) = powerset A :&: powerset B.
Proof.
by apply/setP=> C; rewrite !inE subsetI.
Qed.

Lemma subUset A B C : (B :|: C \subset A) = (B \subset A) && (C \subset A).
Proof.
by rewrite -setCS setCU subsetI !setCS.
Qed.

Lemma subsetU A B C : (A \subset B) || (A \subset C) -> A \subset B :|: C.
Proof.
by rewrite -!(setCS _ A) setCU; apply: subIset.
Qed.

Lemma subUsetP A B C : reflect (A \subset C /\ B \subset C) (A :|: B \subset C).
Proof.
by rewrite subUset; apply: andP.
Qed.

Lemma subsetC A B : (A \subset ~: B) = (B \subset ~: A).
Proof.
by rewrite -setCS setCK.
Qed.

Lemma subCset A B : (~: A \subset B) = (~: B \subset A).
Proof.
by rewrite -setCS setCK.
Qed.

Lemma subsetD A B C : (A \subset B :\: C) = (A \subset B) && [disjoint A & C].
Proof.
by rewrite setDE subsetI -disjoints_subset.
Qed.

Lemma subDset A B C : (A :\: B \subset C) = (A \subset B :|: C).
Proof.
apply/subsetP/subsetP=> sABC x; rewrite !inE.
  by case Bx: (x \in B) => // Ax; rewrite sABC ?inE ?Bx.
by case Bx: (x \in B) => // /sABC; rewrite inE Bx.
Qed.

Lemma subsetDP A B C :
  reflect (A \subset B /\ [disjoint A & C]) (A \subset B :\: C).
Proof.
by rewrite subsetD; apply: andP.
Qed.

Lemma setU_eq0 A B : (A :|: B == set0) = (A == set0) && (B == set0).
Proof.
by rewrite -!subset0 subUset.
Qed.

Lemma setD_eq0 A B : (A :\: B == set0) = (A \subset B).
Proof.
by rewrite -subset0 subDset setU0.
Qed.

Lemma setI_eq0 A B : (A :&: B == set0) = [disjoint A & B].
Proof.
by rewrite disjoints_subset -setD_eq0 setDE setCK.
Qed.

Lemma disjoint_setI0 A B : [disjoint A & B] -> A :&: B = set0.
Proof.
by rewrite -setI_eq0; move/eqP.
Qed.

Lemma disjoints1 A x : [disjoint [set x] & A] = (x \notin A).
Proof.
by rewrite (@eq_disjoint1 _ x) // => y; rewrite !inE.
Qed.

Lemma subsetD1 A B x : (A \subset B :\ x) = (A \subset B) && (x \notin A).
Proof.
by rewrite setDE subsetI subsetC sub1set inE.
Qed.

Lemma subsetD1P A B x : reflect (A \subset B /\ x \notin A) (A \subset B :\ x).
Proof.
by rewrite subsetD1; apply: andP.
Qed.

Lemma properD1 A x : x \in A -> A :\ x \proper A.
Proof.
move=> Ax; rewrite properE subsetDl; apply/subsetPn; exists x=> //.
by rewrite in_setD1 Ax eqxx.
Qed.

Lemma properIr A B : ~~ (B \subset A) -> A :&: B \proper B.
Proof.
by move=> nsAB; rewrite properE subsetIr subsetI negb_and nsAB.
Qed.

Lemma properIl A B : ~~ (A \subset B) -> A :&: B \proper A.
Proof.
by move=> nsBA; rewrite properE subsetIl subsetI negb_and nsBA orbT.
Qed.

Lemma properUr A B : ~~ (A \subset B) ->  B \proper A :|: B.
Proof.
by rewrite properE subsetUr subUset subxx /= andbT.
Qed.

Lemma properUl A B : ~~ (B \subset A) ->  A \proper A :|: B.
Proof.
by move=> not_sBA; rewrite setUC properUr.
Qed.

Lemma proper1set A x : ([set x] \proper A) -> (x \in A).
Proof.
by move/proper_sub; rewrite sub1set.
Qed.

Lemma properIset A B C : (B \proper A) || (C \proper A) -> (B :&: C \proper A).
Proof.
by case/orP; apply: sub_proper_trans; rewrite (subsetIl, subsetIr).
Qed.

Lemma properI A B C : (A \proper B :&: C) -> (A \proper B) && (A \proper C).
Proof.
move=> pAI; apply/andP.
by split; apply: (proper_sub_trans pAI); rewrite (subsetIl, subsetIr).
Qed.

Lemma properU A B C : (B :|: C \proper A) -> (B \proper A) && (C \proper A).
Proof.
move=> pUA; apply/andP.
by split; apply: sub_proper_trans pUA; rewrite (subsetUr, subsetUl).
Qed.

Lemma properD A B C : (A \proper B :\: C) -> (A \proper B) && [disjoint A & C].
Proof.
by rewrite setDE disjoints_subset => /properI/andP[-> /proper_sub].
Qed.

Lemma properCr A B : (A \proper ~: B) = (B \proper ~: A).
Proof.
by rewrite -properC setCK.
Qed.

Lemma properCl A B : (~: A \proper B) = (~: B \proper A).
Proof.
by rewrite -properC setCK.
Qed.

End setOps.

Arguments set1P {T x a}.
Arguments set1_inj {T} [x1 x2].
Arguments set2P {T x a b}.
Arguments setIdP {T x pA pB}.
Arguments setIP {T x A B}.
Arguments setU1P {T x a B}.
Arguments setD1P {T x A b}.
Arguments setUP {T x A B}.
Arguments setDP {T A B x}.
Arguments cards1P {T A}.
Arguments setCP {T x A}.
Arguments setIidPl {T A B}.
Arguments setIidPr {T A B}.
Arguments setUidPl {T A B}.
Arguments setUidPr {T A B}.
Arguments setDidPl {T A B}.
Arguments subsetIP {T A B C}.
Arguments subUsetP {T A B C}.
Arguments subsetDP {T A B C}.
Arguments subsetD1P {T A B x}.
Prenex Implicits set1.
Hint Resolve subsetT_hint : core.

Section setOpsAlgebra.

Import Monoid.

Variable T : finType.

Canonical setI_monoid := Law (@setIA T) (@setTI T) (@setIT T).

Canonical setI_comoid := ComLaw (@setIC T).
Canonical setI_muloid := MulLaw (@set0I T) (@setI0 T).

Canonical setU_monoid := Law (@setUA T) (@set0U T) (@setU0 T).
Canonical setU_comoid := ComLaw (@setUC T).
Canonical setU_muloid := MulLaw (@setTU T) (@setUT T).

Canonical setI_addoid := AddLaw (@setUIl T) (@setUIr T).
Canonical setU_addoid := AddLaw (@setIUl T) (@setIUr T).

End setOpsAlgebra.

Section CartesianProd.

Variables fT1 fT2 : finType.
Variables (A1 : {set fT1}) (A2 : {set fT2}).

Definition setX := [set u | u.1 \in A1 & u.2 \in A2].

Lemma in_setX x1 x2 : ((x1, x2) \in setX) = (x1 \in A1) && (x2 \in A2).
Proof.
by rewrite inE.
Qed.

Lemma setXP x1 x2 : reflect (x1 \in A1 /\ x2 \in A2) ((x1, x2) \in setX).
Proof.
by rewrite inE; apply: andP.
Qed.

Lemma cardsX : #|setX| = #|A1| * #|A2|.
Proof.
by rewrite cardsE cardX.
Qed.

End CartesianProd.

Arguments setXP {fT1 fT2 A1 A2 x1 x2}.

Local Notation imset_def :=
  (fun (aT rT : finType) f mD => [set y in @image_mem aT rT f mD]).
Local Notation imset2_def :=
  (fun (aT1 aT2 rT : finType) f (D1 : mem_pred aT1) (D2 : _ -> mem_pred aT2) =>
     [set y in @image_mem _ rT (prod_curry f)
                           (mem [pred u | D1 u.1 & D2 u.1 u.2])]).

Module Type ImsetSig.
Parameter imset : forall aT rT : finType,
 (aT -> rT) -> mem_pred aT -> {set rT}.
Parameter imset2 : forall aT1 aT2 rT : finType,
 (aT1 -> aT2 -> rT) -> mem_pred aT1 -> (aT1 -> mem_pred aT2) -> {set rT}.
Axiom imsetE : imset = imset_def.
Axiom imset2E : imset2 = imset2_def.
End ImsetSig.

Module Imset : ImsetSig.
Definition imset := imset_def.
Definition imset2 := imset2_def.
Lemma imsetE : imset = imset_def.
Proof.
by [].
Qed.
Lemma imset2E : imset2 = imset2_def.
Proof.
by [].
Qed.
End Imset.

Notation imset := Imset.imset.
Notation imset2 := Imset.imset2.
Canonical imset_unlock := Unlockable Imset.imsetE.
Canonical imset2_unlock := Unlockable Imset.imset2E.
Definition preimset (aT : finType) rT f (R : mem_pred rT) :=
  [set x : aT | in_mem (f x) R].

Notation "f @^-1: A" := (preimset f (mem A)) (at level 24) : set_scope.
Notation "f @: A" := (imset f (mem A)) (at level 24) : set_scope.
Notation "f @2: ( A , B )" := (imset2 f (mem A) (fun _ => mem B))
  (at level 24, format "f  @2:  ( A ,  B )") : set_scope.

 
Notation "[ 'set' E | x 'in' A ]" := ((fun x => E) @: A)
  (at level 0, E, x at level 99,
   format "[ '[hv' 'set'  E '/ '  |  x  'in'  A ] ']'") : set_scope.
Notation "[ 'set' E | x 'in' A & P ]" := [set E | x in pred_of_set [set x in A | P]]
  (at level 0, E, x at level 99,
   format "[ '[hv' 'set'  E '/ '  |  x  'in'  A '/ '  &  P ] ']'") : set_scope.
Notation "[ 'set' E | x 'in' A , y 'in' B ]" :=
  (imset2 (fun x y => E) (mem A) (fun x => mem B))
  (at level 0, E, x, y at level 99, format
   "[ '[hv' 'set'  E '/ '  |  x  'in'  A , '/   '  y  'in'  B ] ']'"
  ) : set_scope.
Notation "[ 'set' E | x 'in' A , y 'in' B & P ]" :=
  [set E | x in A, y in pred_of_set [set y in B | P]]
  (at level 0, E, x, y at level 99, format
   "[ '[hv' 'set'  E '/ '  |  x  'in'  A , '/   '  y  'in'  B '/ '  &  P ] ']'"
  ) : set_scope.

 
Notation "[ 'set' E | x : T 'in' A ]" := ((fun x : T => E) @: A)
  (at level 0, E, x at level 99, only parsing) : set_scope.
Notation "[ 'set' E | x : T 'in' A & P ]" :=
  [set E | x : T in [set x : T in A | P]]
  (at level 0, E, x at level 99, only parsing) : set_scope.
Notation "[ 'set' E | x : T 'in' A , y : U 'in' B ]" :=
  (imset2 (fun (x : T) (y : U) => E) (mem A) (fun (x : T) => mem B))
  (at level 0, E, x, y at level 99, only parsing) : set_scope.
Notation "[ 'set' E | x : T 'in' A , y : U 'in' B & P ]" :=
  [set E | x : T in A, y : U in [set y : U in B | P]]
  (at level 0, E, x, y at level 99, only parsing) : set_scope.

 
Local Notation predOfType T := (pred_of_simpl (@pred_of_argType T)).
Notation "[ 'set' E | x : T ]" := [set E | x : T in predOfType T]
  (at level 0, E, x at level 99,
   format "[ '[hv' 'set'  E '/ '  |  x  :  T ] ']'") : set_scope.
Notation "[ 'set' E | x : T & P ]" :=
  [set E | x : T in pred_of_set [set x : T | P]]
  (at level 0, E, x at level 99,
   format "[ '[hv' 'set'  E '/ '  |  x  :  T '/ '  &  P ] ']'") : set_scope.
Notation "[ 'set' E | x : T , y : U 'in' B ]" :=
  [set E | x : T in predOfType T, y : U in B]
  (at level 0, E, x, y at level 99, format
   "[ '[hv' 'set'  E '/ '  |  x  :  T , '/   '  y  :  U  'in'  B ] ']'")
   : set_scope.
Notation "[ 'set' E | x : T , y : U 'in' B & P ]" :=
  [set E | x : T, y : U in pred_of_set [set y in B | P]]
  (at level 0, E, x, y at level 99, format
 "[ '[hv ' 'set'  E '/'  |  x  :  T , '/  '  y  :  U  'in'  B '/'  &  P ] ']'"
  ) : set_scope.
Notation "[ 'set' E | x : T 'in' A , y : U ]" :=
  [set E | x : T in A, y : U in predOfType U]
  (at level 0, E, x, y at level 99, format
   "[ '[hv' 'set'  E '/ '  |  x  :  T  'in'  A , '/   '  y  :  U ] ']'")
   : set_scope.
Notation "[ 'set' E | x : T 'in' A , y : U & P ]" :=
  [set E | x : T in A, y : U in pred_of_set [set y in P]]
  (at level 0, E, x, y at level 99, format
   "[ '[hv' 'set'  E '/ '  |  x  :  T  'in'  A , '/   '  y  :  U  &  P ] ']'")
   : set_scope.
Notation "[ 'set' E | x : T , y : U ]" :=
  [set E | x : T, y : U in predOfType U]
  (at level 0, E, x, y at level 99, format
   "[ '[hv' 'set'  E '/ '  |  x  :  T , '/   '  y  :  U ] ']'")
   : set_scope.
Notation "[ 'set' E | x : T , y : U & P ]" :=
  [set E | x : T, y : U in pred_of_set [set y in P]]
  (at level 0, E, x, y at level 99, format
   "[ '[hv' 'set'  E '/ '  |  x  :  T , '/   '  y  :  U  &  P ] ']'")
   : set_scope.

 
Notation "[ 'set' E | x , y 'in' B ]" := [set E | x : _, y : _ in B]
  (at level 0, E, x, y at level 99, only parsing) : set_scope.
Notation "[ 'set' E | x , y 'in' B & P ]" := [set E | x : _, y : _ in B & P]
  (at level 0, E, x, y at level 99, only parsing) : set_scope.
Notation "[ 'set' E | x 'in' A , y ]" := [set E | x : _ in A, y : _]
  (at level 0, E, x, y at level 99, only parsing) : set_scope.
Notation "[ 'set' E | x 'in' A , y & P ]" := [set E | x : _ in A, y : _ & P]
  (at level 0, E, x, y at level 99, only parsing) : set_scope.
Notation "[ 'set' E | x , y ]" := [set E | x : _, y : _]
  (at level 0, E, x, y at level 99, only parsing) : set_scope.
Notation "[ 'set' E | x , y & P ]" := [set E | x : _, y : _ & P ]
  (at level 0, E, x, y at level 99, only parsing) : set_scope.

Section FunImage.

Variables aT aT2 : finType.

Section ImsetTheory.

Variable rT : finType.

Section ImsetProp.

Variables (f : aT -> rT) (f2 : aT -> aT2 -> rT).

Lemma imsetP D y : reflect (exists2 x, in_mem x D & y = f x) (y \in imset f D).
Proof.
by rewrite [@imset]unlock inE; apply: imageP.
Qed.

Variant imset2_spec D1 D2 y : Prop :=
  Imset2spec x1 x2 of in_mem x1 D1 & in_mem x2 (D2 x1) & y = f2 x1 x2.

Lemma imset2P D1 D2 y : reflect (imset2_spec D1 D2 y) (y \in imset2 f2 D1 D2).
Proof.
rewrite [@imset2]unlock inE.
apply: (iffP imageP) => [[[x1 x2] Dx12] | [x1 x2 Dx1 Dx2]] -> {y}.
  by case/andP: Dx12; exists x1 x2.
by exists (x1, x2); rewrite //= !inE Dx1.
Qed.

Lemma imset_f (D : {pred aT}) x : x \in D -> f x \in f @: D.
Proof.
by move=> Dx; apply/imsetP; exists x.
Qed.

Lemma mem_imset (D : {pred aT}) x : injective f -> f x \in f @: D = (x \in D).
Proof.
by move=> f_inj; apply/imsetP/idP;[case=> [y] ? /f_inj -> | move=> ?; exists x].
Qed.

Lemma imset0 : f @: set0 = set0.
Proof.
by apply/setP => y /[!inE]; apply/imsetP => -[x /[!inE]].
Qed.

Lemma imset_eq0 (A : {set aT}) : (f @: A == set0) = (A == set0).
Proof.
have [-> | [x Ax]] := set_0Vmem A; first by rewrite imset0 !eqxx.
by rewrite -!cards_eq0 (cardsD1 x) Ax (cardsD1 (f x)) imset_f.
Qed.

Lemma imset_set1 x : f @: [set x] = [set f x].
Proof.
apply/setP => y.
by apply/imsetP/set1P=> [[x' /set1P-> //]| ->]; exists x; rewrite ?set11.
Qed.

Lemma imset_inj : injective f -> injective (fun A : {set aT} => f @: A).
Proof.
move=> inj_f A B => /setP E; apply/setP => x.
by rewrite -(mem_imset (mem A) x inj_f) E mem_imset.
Qed.

Lemma imset_disjoint (A B : {pred aT}) :
  injective f -> [disjoint f @: A & f @: B] = [disjoint A & B].
Proof.
move=> inj_f; apply/pred0Pn/pred0Pn => /= [[_ /andP[/imsetP[x xA ->]] xB]|].
  by exists x; rewrite xA -(mem_imset (mem B) x inj_f).
by move=> [x /andP[xA xB]]; exists (f x); rewrite !mem_imset ?xA.
Qed.

Lemma imset2_f (D : {pred aT}) (D2 : aT -> {pred aT2}) x x2 :
    x \in D -> x2 \in D2 x ->
  f2 x x2 \in imset2 f2 (mem D) (fun x1 => mem (D2 x1)).
Proof.
by move=> Dx Dx2; apply/imset2P; exists x x2.
Qed.

Lemma mem_imset2 (D : {pred aT}) (D2 : aT -> {pred aT2}) x x2 :
    injective2 f2 ->
  f2 x x2 \in imset2 f2 (mem D) (fun x1 => mem (D2 x1)) =
    ((x \in D) && (x2 \in D2 x)).
Proof.
move=> inj2_f; apply/imset2P/andP => [|[xD xD2]]; last by exists x x2.
by move => [x' x2' xD xD2 eq_f2]; case: (inj2_f _ _ _ _ eq_f2) => -> ->.
Qed.

Lemma sub_imset_pre (A : {pred aT}) (B : {pred rT}) :
  (f @: A \subset B) = (A \subset f @^-1: B).
Proof.
apply/subsetP/subsetP=> [sfAB x Ax | sAf'B fx].
  by rewrite inE sfAB ?imset_f.
by move=> /imsetP[a + ->] => /sAf'B /[!inE].
Qed.

Lemma preimsetS (A B : {pred rT}) :
  A \subset B -> (f @^-1: A) \subset (f @^-1: B).
Proof.
by move=> sAB; apply/subsetP=> y /[!inE]; apply: subsetP.
Qed.

Lemma preimset0 : f @^-1: set0 = set0.
Proof.
by apply/setP=> x; rewrite !inE.
Qed.

Lemma preimsetT : f @^-1: setT = setT.
Proof.
by apply/setP=> x; rewrite !inE.
Qed.

Lemma preimsetI (A B : {set rT}) :
  f @^-1: (A :&: B) = (f @^-1: A) :&: (f @^-1: B).
Proof.
by apply/setP=> y; rewrite !inE.
Qed.

Lemma preimsetU (A B : {set rT}) :
  f @^-1: (A :|: B) = (f @^-1: A) :|: (f @^-1: B).
Proof.
by apply/setP=> y; rewrite !inE.
Qed.

Lemma preimsetD (A B : {set rT}) :
  f @^-1: (A :\: B) = (f @^-1: A) :\: (f @^-1: B).
Proof.
by apply/setP=> y; rewrite !inE.
Qed.

Lemma preimsetC (A : {set rT}) : f @^-1: (~: A) = ~: f @^-1: A.
Proof.
by apply/setP=> y; rewrite !inE.
Qed.

Lemma imsetS (A B : {pred aT}) : A \subset B -> f @: A \subset f @: B.
Proof.
move=> sAB; apply/subsetP => _ /imsetP[x Ax ->].
by apply/imsetP; exists x; rewrite ?(subsetP sAB).
Qed.

Lemma imset_proper (A B : {set aT}) :
   {in B &, injective f} -> A \proper B -> f @: A \proper f @: B.
Proof.
move=> injf /properP[sAB [x Bx nAx]]; rewrite properE imsetS //=.
apply: contra nAx => sfBA.
have: f x \in f @: A by rewrite (subsetP sfBA) ?imset_f.
by case/imsetP=> y Ay /injf-> //; apply: subsetP sAB y Ay.
Qed.

Lemma preimset_proper (A B : {set rT}) :
  B \subset codom f -> A \proper B -> (f @^-1: A) \proper (f @^-1: B).
Proof.
move=> sBc /properP[sAB [u Bu nAu]]; rewrite properE preimsetS //=.
by apply/subsetPn; exists (iinv (subsetP sBc  _ Bu)); rewrite inE /= f_iinv.
Qed.

Lemma imsetU (A B : {set aT}) : f @: (A :|: B) = (f @: A) :|: (f @: B).
Proof.
apply/eqP; rewrite eqEsubset subUset.
rewrite 2?imsetS (andbT, subsetUl, subsetUr) // andbT.
apply/subsetP=> _ /imsetP[x ABx ->]; apply/setUP.
by case/setUP: ABx => [Ax | Bx]; [left | right]; apply/imsetP; exists x.
Qed.

Lemma imsetU1 a (A : {set aT}) : f @: (a |: A) = f a |: (f @: A).
Proof.
by rewrite imsetU imset_set1.
Qed.

Lemma imsetI (A B : {set aT}) :
  {in A & B, injective f} -> f @: (A :&: B) = f @: A :&: f @: B.
Proof.
move=> injf; apply/eqP; rewrite eqEsubset subsetI.
rewrite 2?imsetS (andTb, subsetIl, subsetIr) //=.
apply/subsetP=> _ /setIP[/imsetP[x Ax ->] /imsetP[z Bz /injf eqxz]].
by rewrite imset_f // inE Ax eqxz.
Qed.

Lemma imset2Sl (A B : {pred aT}) (C : {pred aT2}) :
  A \subset B -> f2 @2: (A, C) \subset f2 @2: (B, C).
Proof.
move=> sAB; apply/subsetP=> _ /imset2P[x y Ax Cy ->].
by apply/imset2P; exists x y; rewrite ?(subsetP sAB).
Qed.

Lemma imset2Sr (A B : {pred aT2}) (C : {pred aT}) :
  A \subset B -> f2 @2: (C, A) \subset f2 @2: (C, B).
Proof.
move=> sAB; apply/subsetP=> _ /imset2P[x y Ax Cy ->].
by apply/imset2P; exists x y; rewrite ?(subsetP sAB).
Qed.

Lemma imset2S (A B : {pred aT}) (A2 B2 : {pred aT2}) :
  A \subset B ->  A2 \subset B2 -> f2 @2: (A, A2) \subset f2 @2: (B, B2).
Proof.
 by move=> /(imset2Sl B2) sBA /(imset2Sr A)/subset_trans->.
Qed.

End ImsetProp.

Implicit Types (f g : aT -> rT) (D : {pred aT}) (R : {pred rT}).

Lemma eq_preimset f g R : f =1 g -> f @^-1: R = g @^-1: R.
Proof.
by move=> eqfg; apply/setP => y; rewrite !inE eqfg.
Qed.

Lemma eq_imset f g D : f =1 g -> f @: D = g @: D.
Proof.
move=> eqfg; apply/setP=> y.
by apply/imsetP/imsetP=> [] [x Dx ->]; exists x; rewrite ?eqfg.
Qed.

Lemma eq_in_imset f g D : {in D, f =1 g} -> f @: D = g @: D.
Proof.
move=> eqfg; apply/setP => y.
by apply/imsetP/imsetP=> [] [x Dx ->]; exists x; rewrite ?eqfg.
Qed.

Lemma eq_in_imset2 (f g : aT -> aT2 -> rT) (D : {pred aT}) (D2 : {pred aT2}) :
  {in D & D2, f =2 g} -> f @2: (D, D2) = g @2: (D, D2).
Proof.
move=> eqfg; apply/setP => y.
by apply/imset2P/imset2P=> [] [x x2 Dx Dx2 ->]; exists x x2; rewrite ?eqfg.
Qed.

End ImsetTheory.

Lemma imset2_pair (A : {set aT}) (B : {set aT2}) :
  [set (x, y) | x in A, y in B] = setX A B.
Proof.
apply/setP=> [[x y]]; rewrite !inE /=.
by apply/imset2P/andP=> [[_ _ _ _ [-> ->]//]| []]; exists x y.
Qed.

Lemma setXS (A1 B1 : {set aT}) (A2 B2 : {set aT2}) :
  A1 \subset B1 -> A2 \subset B2 -> setX A1 A2 \subset setX B1 B2.
Proof.
by move=> sAB1 sAB2; rewrite -!imset2_pair imset2S.
Qed.

End FunImage.

Arguments imsetP {aT rT f D y}.
Arguments imset2P {aT aT2 rT f2 D1 D2 y}.
Arguments imset_disjoint {aT rT f A B}.

Section BigOps.

Variables (R : Type) (idx : R).
Variables (op : Monoid.law idx) (aop : Monoid.com_law idx).
Variables I J : finType.
Implicit Type A B : {set I}.
Implicit Type h : I -> J.
Implicit Type P : pred I.
Implicit Type F : I -> R.

Lemma big_set0 F : \big[op/idx]_(i in set0) F i = idx.
Proof.
by apply: big_pred0 => i; rewrite inE.
Qed.

Lemma big_set1 a F : \big[op/idx]_(i in [set a]) F i = F a.
Proof.
by apply: big_pred1 => i; rewrite !inE.
Qed.

Lemma big_set (A : pred I) F :
   \big[op/idx]_(i in [set i | A i]) (F i) = \big[op/idx]_(i in A) (F i).
Proof.
by apply: eq_bigl => i; rewrite inE.
Qed.

Lemma big_setID A B F :
  \big[aop/idx]_(i in A) F i =
     aop (\big[aop/idx]_(i in A :&: B) F i)
         (\big[aop/idx]_(i in A :\: B) F i).
Proof.
rewrite (bigID (mem B)) setDE.
by congr (aop _ _); apply: eq_bigl => i; rewrite !inE.
Qed.

Lemma big_setIDcond A B P F :
  \big[aop/idx]_(i in A | P i) F i =
     aop (\big[aop/idx]_(i in A :&: B | P i) F i)
         (\big[aop/idx]_(i in A :\: B | P i) F i).
Proof.
by rewrite !big_mkcondr; apply: big_setID.
Qed.

Lemma big_setD1 a A F : a \in A ->
  \big[aop/idx]_(i in A) F i = aop (F a) (\big[aop/idx]_(i in A :\ a) F i).
Proof.
move=> Aa; rewrite (bigD1 a Aa); congr (aop _).
by apply: eq_bigl => x; rewrite !inE andbC.
Qed.

Lemma big_setU1 a A F : a \notin A ->
  \big[aop/idx]_(i in a |: A) F i = aop (F a) (\big[aop/idx]_(i in A) F i).
Proof.
by move=> notAa; rewrite (@big_setD1 a) ?setU11 //= setU1K.
Qed.

Lemma big_imset h (A : {pred I}) G : {in A &, injective h} ->
  \big[aop/idx]_(j in h @: A) G j = \big[aop/idx]_(i in A) G (h i).
Proof.
move=> injh; pose hA := mem (image h A).
rewrite (eq_bigl hA) => [|j]; last exact/imsetP/imageP.
pose h' := omap (fun u : {j | hA j} => iinv (svalP u)) \o insub.
rewrite (reindex_omap h h') => [|j hAj]; rewrite {}/h'/= ?insubT/= ?f_iinv//.
apply: eq_bigl => i; case: insubP => [u -> /= def_u | nhAhi]; last first.
  by apply/andP/idP => [[]//| Ai]; case/imageP: nhAhi; exists i.
set i' := iinv _; have Ai' : i' \in A := mem_iinv (svalP u).
by apply/eqP/idP => [[<-] // | Ai]; congr Some; apply: injh; rewrite ?f_iinv.
Qed.

Lemma big_imset_cond h (A : {pred I}) (P : pred J) G : {in A &, injective h} ->
  \big[aop/idx]_(j in h @: A | P j) G j =
    \big[aop/idx]_(i in A | P (h i)) G (h i).
Proof.
by move=> h_inj; rewrite 2!big_mkcondr big_imset.
Qed.

Lemma partition_big_imset h (A : {pred I}) F :
  \big[aop/idx]_(i in A) F i =
     \big[aop/idx]_(j in h @: A) \big[aop/idx]_(i in A | h i == j) F i.
Proof.
by apply: partition_big => i Ai; apply/imsetP; exists i.
Qed.

End BigOps.

Arguments big_setID [R idx aop I A].
Arguments big_setD1 [R idx aop I] a [A F].
Arguments big_setU1 [R idx aop I] a [A F].
Arguments big_imset [R idx aop I J h A].
Arguments partition_big_imset [R idx aop I J].

Section Fun2Set1.

Variables aT1 aT2 rT : finType.
Variables (f : aT1 -> aT2 -> rT).

Lemma imset2_set1l x1 (D2 : {pred aT2}) : f @2: ([set x1], D2) = f x1 @: D2.
Proof.
apply/setP=> y; apply/imset2P/imsetP=> [[x x2 /set1P->]| [x2 Dx2 ->]].
  by exists x2.
by exists x1 x2; rewrite ?set11.
Qed.

Lemma imset2_set1r x2 (D1 : {pred aT1}) : f @2: (D1, [set x2]) = f^~ x2 @: D1.
Proof.
apply/setP=> y; apply/imset2P/imsetP=> [[x1 x Dx1 /set1P->]| [x1 Dx1 ->]].
  by exists x1.
by exists x1 x2; rewrite ?set11.
Qed.

End Fun2Set1.

Section CardFunImage.

Variables aT aT2 rT : finType.
Variables (f : aT -> rT) (g : rT -> aT) (f2 : aT -> aT2 -> rT).
Variables (D : {pred aT}) (D2 : {pred aT}).

Lemma imset_card : #|f @: D| = #|image f D|.
Proof.
by rewrite [@imset]unlock cardsE.
Qed.

Lemma leq_imset_card : #|f @: D| <= #|D|.
Proof.
by rewrite imset_card leq_image_card.
Qed.

Lemma card_in_imset : {in D &, injective f} -> #|f @: D| = #|D|.
Proof.
by move=> injf; rewrite imset_card card_in_image.
Qed.

Lemma card_imset : injective f -> #|f @: D| = #|D|.
Proof.
by move=> injf; rewrite imset_card card_image.
Qed.

Lemma imset_injP : reflect {in D &, injective f} (#|f @: D| == #|D|).
Proof.
by rewrite [@imset]unlock cardsE; apply: image_injP.
Qed.

Lemma can2_in_imset_pre :
  {in D, cancel f g} -> {on D, cancel g & f} -> f @: D = g @^-1: D.
Proof.
move=> fK gK; apply/setP=> y; rewrite inE.
by apply/imsetP/idP=> [[x Ax ->] | Agy]; last exists (g y); rewrite ?(fK, gK).
Qed.

Lemma can2_imset_pre : cancel f g -> cancel g f -> f @: D = g @^-1: D.
Proof.
by move=> fK gK; apply: can2_in_imset_pre; apply: in1W.
Qed.

End CardFunImage.

Arguments imset_injP {aT rT f D}.

Lemma on_card_preimset (aT rT : finType) (f : aT -> rT) (R : {pred rT}) :
  {on R, bijective f} -> #|f @^-1: R| = #|R|.
Proof.
case=> g fK gK; rewrite -(can2_in_imset_pre gK) // card_in_imset //.
exact: can_in_inj gK.
Qed.

Lemma can_imset_pre (T : finType) f g (A : {set T}) :
  cancel f g -> f @: A = g @^-1: A :> {set T}.
Proof.
move=> fK; apply: can2_imset_pre => // x.
suffices fx: x \in codom f by rewrite -(f_iinv fx) fK.
exact/(subset_cardP (card_codom (can_inj fK)))/subsetP.
Qed.

Lemma imset_id (T : finType) (A : {set T}) : [set x | x in A] = A.
Proof.
by apply/setP=> x; rewrite (@can_imset_pre _ _ id) ?inE.
Qed.

Lemma card_preimset (T : finType) (f : T -> T) (A : {set T}) :
  injective f -> #|f @^-1: A| = #|A|.
Proof.
move=> injf; apply: on_card_preimset; apply: onW_bij.
have ontof: _ \in codom f by apply/(subset_cardP (card_codom injf))/subsetP.
by exists (fun x => iinv (ontof x)) => x; rewrite (f_iinv, iinv_f).
Qed.

Lemma card_powerset (T : finType) (A : {set T}) : #|powerset A| = 2 ^ #|A|.
Proof.
rewrite -card_bool -(card_pffun_on false) -(card_imset _ val_inj).
apply: eq_card => f; pose sf := false.-support f; pose D := finset sf.
have sDA: (D \subset A) = (sf \subset A) by apply: eq_subset; apply: in_set.
have eq_sf x : sf x = f x by rewrite /= negb_eqb addbF.
have valD: val D = f by rewrite /D unlock; apply/ffunP=> x; rewrite ffunE eq_sf.
apply/imsetP/pffun_onP=> [[B] | [sBA _]]; last by exists D; rewrite // inE ?sDA.
by rewrite inE -sDA -valD => sBA /val_inj->.
Qed.

Section FunImageComp.

Variables T T' U : finType.

Lemma imset_comp (f : T' -> U) (g : T -> T') (H : {pred T}) :
  (f \o g) @: H = f @: (g @: H).
Proof.
apply/setP/subset_eqP/andP.
split; apply/subsetP=> _ /imsetP[x0 Hx0 ->]; apply/imsetP.
  by exists (g x0); first apply: imset_f.
by move/imsetP: Hx0 => [x1 Hx1 ->]; exists x1.
Qed.

End FunImageComp.

Notation "\bigcup_ ( i <- r | P ) F" :=
  (\big[@setU _/set0]_(i <- r | P) F%SET) : set_scope.
Notation "\bigcup_ ( i <- r ) F" :=
  (\big[@setU _/set0]_(i <- r) F%SET) : set_scope.
Notation "\bigcup_ ( m <= i < n | P ) F" :=
  (\big[@setU _/set0]_(m <= i < n | P%B) F%SET) : set_scope.
Notation "\bigcup_ ( m <= i < n ) F" :=
  (\big[@setU _/set0]_(m <= i < n) F%SET) : set_scope.
Notation "\bigcup_ ( i | P ) F" :=
  (\big[@setU _/set0]_(i | P%B) F%SET) : set_scope.
Notation "\bigcup_ i F" :=
  (\big[@setU _/set0]_i F%SET) : set_scope.
Notation "\bigcup_ ( i : t | P ) F" :=
  (\big[@setU _/set0]_(i : t | P%B) F%SET) (only parsing): set_scope.
Notation "\bigcup_ ( i : t ) F" :=
  (\big[@setU _/set0]_(i : t) F%SET) (only parsing) : set_scope.
Notation "\bigcup_ ( i < n | P ) F" :=
  (\big[@setU _/set0]_(i < n | P%B) F%SET) : set_scope.
Notation "\bigcup_ ( i < n ) F" :=
  (\big[@setU _/set0]_ (i < n) F%SET) : set_scope.
Notation "\bigcup_ ( i 'in' A | P ) F" :=
  (\big[@setU _/set0]_(i in A | P%B) F%SET) : set_scope.
Notation "\bigcup_ ( i 'in' A ) F" :=
  (\big[@setU _/set0]_(i in A) F%SET) : set_scope.

Notation "\bigcap_ ( i <- r | P ) F" :=
  (\big[@setI _/setT]_(i <- r | P%B) F%SET) : set_scope.
Notation "\bigcap_ ( i <- r ) F" :=
  (\big[@setI _/setT]_(i <- r) F%SET) : set_scope.
Notation "\bigcap_ ( m <= i < n | P ) F" :=
  (\big[@setI _/setT]_(m <= i < n | P%B) F%SET) : set_scope.
Notation "\bigcap_ ( m <= i < n ) F" :=
  (\big[@setI _/setT]_(m <= i < n) F%SET) : set_scope.
Notation "\bigcap_ ( i | P ) F" :=
  (\big[@setI _/setT]_(i | P%B) F%SET) : set_scope.
Notation "\bigcap_ i F" :=
  (\big[@setI _/setT]_i F%SET) : set_scope.
Notation "\bigcap_ ( i : t | P ) F" :=
  (\big[@setI _/setT]_(i : t | P%B) F%SET) (only parsing): set_scope.
Notation "\bigcap_ ( i : t ) F" :=
  (\big[@setI _/setT]_(i : t) F%SET) (only parsing) : set_scope.
Notation "\bigcap_ ( i < n | P ) F" :=
  (\big[@setI _/setT]_(i < n | P%B) F%SET) : set_scope.
Notation "\bigcap_ ( i < n ) F" :=
  (\big[@setI _/setT]_(i < n) F%SET) : set_scope.
Notation "\bigcap_ ( i 'in' A | P ) F" :=
  (\big[@setI _/setT]_(i in A | P%B) F%SET) : set_scope.
Notation "\bigcap_ ( i 'in' A ) F" :=
  (\big[@setI _/setT]_(i in A) F%SET) : set_scope.

Section BigSetOps.

Variables T I : finType.
Implicit Types (U : {pred T}) (P : pred I) (A B : {set I}) (F :  I -> {set T}).

 
 
Lemma bigcup_sup j P F : P j -> F j \subset \bigcup_(i | P i) F i.
Proof.
by move=> Pj; rewrite (bigD1 j) //= subsetUl.
Qed.

Lemma bigcup_max j U P F :
  P j -> U \subset F j -> U \subset \bigcup_(i | P i) F i.
Proof.
by move=> Pj sUF; apply: subset_trans (bigcup_sup _ Pj).
Qed.

Lemma bigcupP x P F :
  reflect (exists2 i, P i & x \in F i) (x \in \bigcup_(i | P i) F i).
Proof.
apply: (iffP idP) => [|[i Pi]]; last first.
  by apply: subsetP x; apply: bigcup_sup.
by elim/big_rec: _ => [|i _ Pi _ /setUP[|//]]; [rewrite inE | exists i].
Qed.

Lemma bigcupsP U P F :
  reflect (forall i, P i -> F i \subset U) (\bigcup_(i | P i) F i \subset U).
Proof.
apply: (iffP idP) => [sFU i Pi| sFU].
  by apply: subset_trans sFU; apply: bigcup_sup.
by apply/subsetP=> x /bigcupP[i Pi]; apply: (subsetP (sFU i Pi)).
Qed.

Lemma bigcup0P P F :
  reflect (forall i, P i -> F i = set0) (\bigcup_(i | P i) F i == set0).
Proof.
rewrite -subset0; apply: (iffP (bigcupsP _ _ _)) => sub0 i /sub0; last by move->.
by rewrite subset0 => /eqP.
Qed.

Lemma bigcup_disjointP U P F  :
  reflect (forall i : I, P i -> [disjoint U & F i])
          [disjoint U & \bigcup_(i | P i) F i].
Proof.
apply: (iffP idP) => [dUF i Pp|dUF].
  by apply: disjointWr dUF; apply: bigcup_sup.
rewrite disjoint_sym disjoint_subset.
by apply/bigcupsP=> i /dUF; rewrite disjoint_sym disjoint_subset.
Qed.

Lemma bigcup_disjoint U P F :
  (forall i, P i -> [disjoint U & F i]) -> [disjoint U & \bigcup_(i | P i) F i].
Proof.
by move/bigcup_disjointP.
Qed.

Lemma bigcup_setU A B F :
  \bigcup_(i in A :|: B) F i =
     (\bigcup_(i in A) F i) :|: (\bigcup_ (i in B) F i).
Admitted.

Lemma bigcup_seq r F : \bigcup_(i <- r) F i = \bigcup_(i in r) F i.
Admitted.

 
Lemma bigcap_inf j P F : P j -> \bigcap_(i | P i) F i \subset F j.
Admitted.

Lemma bigcap_min j U P F :
  P j -> F j \subset U -> \bigcap_(i | P i) F i \subset U.
Admitted.

Lemma bigcapsP U P F :
  reflect (forall i, P i -> U \subset F i) (U \subset \bigcap_(i | P i) F i).
Admitted.

Lemma bigcapP x P F :
  reflect (forall i, P i -> x \in F i) (x \in \bigcap_(i | P i) F i).
Admitted.

Lemma setC_bigcup J r (P : pred J) (F : J -> {set T}) :
  ~: (\bigcup_(j <- r | P j) F j) = \bigcap_(j <- r | P j) ~: F j.
Proof.
by apply: big_morph => [A B|]; rewrite ?setC0 ?setCU.
Qed.

Lemma setC_bigcap J r (P : pred J) (F : J -> {set T}) :
  ~: (\bigcap_(j <- r | P j) F j) = \bigcup_(j <- r | P j) ~: F j.
Admitted.

Lemma bigcap_setU A B F :
  (\bigcap_(i in A :|: B) F i) =
    (\bigcap_(i in A) F i) :&: (\bigcap_(i in B) F i).
Admitted.

Lemma bigcap_seq r F : \bigcap_(i <- r) F i = \bigcap_(i in r) F i.
Admitted.

End BigSetOps.

Arguments bigcup_sup [T I] j [P F].
Arguments bigcup_max [T I] j [U P F].
Arguments bigcupP {T I x P F}.
Arguments bigcupsP {T I U P F}.
Arguments bigcup_disjointP {T I U P F}.
Arguments bigcap_inf [T I] j [P F].
Arguments bigcap_min [T I] j [U P F].
Arguments bigcapP {T I x P F}.
Arguments bigcapsP {T I U P F}.

Section ImsetCurry.

Variables (aT1 aT2 rT : finType) (f : aT1 -> aT2 -> rT).

Section Curry.

Variables (A1 : {set aT1}) (A2 : {set aT2}).
Variables (D1 : {pred aT1}) (D2 : {pred aT2}).

Lemma curry_imset2X : f @2: (A1, A2) = prod_curry f @: (setX A1 A2).
Admitted.

Lemma curry_imset2l : f @2: (D1, D2) = \bigcup_(x1 in D1) f x1 @: D2.
Admitted.

Lemma curry_imset2r : f @2: (D1, D2) = \bigcup_(x2 in D2) f^~ x2 @: D1.
Admitted.

End Curry.

Lemma imset2Ul (A B : {set aT1}) (C : {set aT2}) :
  f @2: (A :|: B, C) = f @2: (A, C) :|: f @2: (B, C).
Admitted.

Lemma imset2Ur (A : {set aT1}) (B C : {set aT2}) :
  f @2: (A, B :|: C) = f @2: (A, B) :|: f @2: (A, C).
Admitted.

End ImsetCurry.

Section Partitions.

Variables T I : finType.
Implicit Types (x y z : T) (A B D X : {set T}) (P Q : {set {set T}}).
Implicit Types (J : pred I) (F : I -> {set T}).

Definition cover P := \bigcup_(B in P) B.
Definition pblock P x := odflt set0 (pick [pred B in P | x \in B]).
Definition trivIset P := \sum_(B in P) #|B| == #|cover P|.
Definition partition P D := [&& cover P == D, trivIset P & set0 \notin P].

Definition is_transversal X P D :=
  [&& partition P D, X \subset D & [forall B in P, #|X :&: B| == 1]].
Definition transversal P D := [set odflt x [pick y in pblock P x] | x in D].
Definition transversal_repr x0 X B := odflt x0 [pick x in X :&: B].

Lemma leq_card_setU A B : #|A :|: B| <= #|A| + #|B| ?= iff [disjoint A & B].
Proof.
rewrite -(addn0 #|_|) -setI_eq0 -cards_eq0 -cardsUI eq_sym.
by rewrite (mono_leqif (leq_add2l _)).
Qed.

Lemma leq_card_cover P : #|cover P| <= \sum_(A in P) #|A| ?= iff trivIset P.
Proof.
split; last exact: eq_sym.
rewrite /cover; elim/big_rec2: _ => [|A n U _ leUn]; first by rewrite cards0.
by rewrite (leq_trans (leq_card_setU A U).1) ?leq_add2l.
Qed.

Lemma imset_cover (T' : finType) P  (f : T -> T') :
  [set f x | x in cover P] = \bigcup_(i in P) [set f x | x in i].
Admitted.

Lemma cover1 A : cover [set A] = A.
Admitted.

Lemma trivIset1 A : trivIset [set A].
Admitted.

Lemma trivIsetP P :
  reflect {in P &, forall A B, A != B -> [disjoint A & B]} (trivIset P).
Proof.
have->: P = [set x in enum (mem P)] by apply/setP=> x; rewrite inE mem_enum.
elim: {P}(enum _) (enum_uniq (mem P)) => [_ | A e IHe] /=.
  by rewrite /trivIset /cover !big_set0 cards0; left=> A; rewrite inE.
case/andP; rewrite set_cons -(in_set (fun B => B \in e)) => PA {}/IHe.
move: {e}[set x in e] PA => P PA IHP.
rewrite /trivIset /cover !big_setU1 //= eq_sym.
have:= leq_card_cover P; rewrite -(mono_leqif (leq_add2l #|A|)).
move/(leqif_trans (leq_card_setU _ _))->; rewrite disjoints_subset setC_bigcup.
case: bigcapsP => [disjA | meetA]; last first.
  right=> [tI]; case: meetA => B PB; rewrite -disjoints_subset.
  by rewrite tI ?setU11 ?setU1r //; apply: contraNneq PA => ->.
apply: (iffP IHP) => [] tI B C PB PC; last by apply: tI; apply: setU1r.
by case/setU1P: PC PB => [->|PC] /setU1P[->|PB]; try by [apply: tI | case/eqP];
  first rewrite disjoint_sym; rewrite disjoints_subset disjA.
Qed.

Lemma trivIsetS P Q : P \subset Q -> trivIset Q -> trivIset P.
Admitted.

Lemma trivIsetD P Q : trivIset P -> trivIset (P :\: Q).
Admitted.

Lemma trivIsetU P Q :
  trivIset Q -> trivIset P -> [disjoint cover Q & cover P] -> trivIset (Q :|: P).
Admitted.

Lemma coverD1 P B : trivIset P -> B \in P -> cover (P :\ B) = cover P :\: B.
Admitted.

Lemma trivIsetI P D : trivIset P -> trivIset (P ::&: D).
Admitted.

Lemma cover_setI P D : cover (P ::&: D) \subset cover P :&: D.
Admitted.

Lemma mem_pblock P x : (x \in pblock P x) = (x \in cover P).
Proof.
rewrite /pblock; apply/esym/bigcupP.
case: pickP => /= [A /andP[PA Ax]| noA]; first by rewrite Ax; exists A.
by rewrite inE => [[A PA Ax]]; case/andP: (noA A).
Qed.

Lemma pblock_mem P x : x \in cover P -> pblock P x \in P.
Proof.
by rewrite -mem_pblock /pblock; case: pickP => [A /andP[]| _] //=; rewrite inE.
Qed.

Lemma def_pblock P B x : trivIset P -> B \in P -> x \in B -> pblock P x = B.
Proof.
move/trivIsetP=> tiP PB Bx; have Px: x \in cover P by apply/bigcupP; exists B.
apply: (contraNeq (tiP _ _ _ PB)); first by rewrite pblock_mem.
by apply/pred0Pn; exists x; rewrite /= mem_pblock Px.
Qed.

Lemma same_pblock P x y :
  trivIset P -> x \in pblock P y -> pblock P x = pblock P y.
Admitted.

Lemma eq_pblock P x y :
    trivIset P -> x \in cover P ->
  (pblock P x == pblock P y) = (y \in pblock P x).
Admitted.

Lemma trivIsetU1 A P :
    {in P, forall B, [disjoint A & B]} -> trivIset P -> set0 \notin P ->
  trivIset (A |: P) /\ A \notin P.
Admitted.

Lemma cover_imset J F : cover (F @: J) = \bigcup_(i in J) F i.
Admitted.

Lemma trivIimset J F (P := F @: J) :
    {in J &, forall i j, j != i -> [disjoint F i & F j]} -> set0 \notin P ->
  trivIset P /\ {in J &, injective F}.
Admitted.

Lemma cover_partition P D : partition P D -> cover P = D.
Admitted.

Lemma partition0 P D : partition P D -> set0 \in P = false.
Admitted.

Lemma partition_neq0 P D B : partition P D -> B \in P -> B != set0.
Admitted.

Lemma partition_trivIset P D : partition P D -> trivIset P.
Admitted.

Lemma partitionS P D B : partition P D -> B \in P -> B \subset D.
Admitted.

Lemma partitionD1 P D B :
  partition P D -> B \in P -> partition (P :\ B) (D :\: B).
Admitted.

Lemma partitionU1 P D B :
  partition P D -> B != set0 -> [disjoint B & D] -> partition (B |: P) (B :|: D).
Admitted.

Lemma partition_set0 P : partition P set0 = (P == set0).
Admitted.

Lemma card_partition P D : partition P D -> #|D| = \sum_(A in P) #|A|.
Admitted.

Lemma card_uniform_partition n P D :
  {in P, forall A, #|A| = n} -> partition P D -> #|D| = #|P| * n.
Admitted.

Lemma partition_pigeonhole P D A :
  partition P D -> #|P| <= #|A| -> A \subset D -> {in P, forall B, #|A :&: B| <= 1} ->
  {in P, forall B, A :&: B != set0}.
Admitted.

Section BigOps.

Variables (R : Type) (idx : R) (op : Monoid.com_law idx).
Let rhs_cond P K E := \big[op/idx]_(A in P) \big[op/idx]_(x in A | K x) E x.
Let rhs P E := \big[op/idx]_(A in P) \big[op/idx]_(x in A) E x.

Lemma big_trivIset_cond P (K : pred T) (E : T -> R) :
  trivIset P -> \big[op/idx]_(x in cover P | K x) E x = rhs_cond P K E.
Proof.
move=> tiP; rewrite (partition_big (pblock P) (mem P)) -/op => /= [|x].
  apply: eq_bigr => A PA; apply: eq_bigl => x; rewrite andbAC; congr (_ && _).
  rewrite -mem_pblock; apply/andP/idP=> [[Px /eqP <- //] | Ax].
  by rewrite (def_pblock tiP PA Ax).
by case/andP=> Px _; apply: pblock_mem.
Qed.

Lemma big_trivIset P (E : T -> R) :
  trivIset P -> \big[op/idx]_(x in cover P) E x = rhs P E.
Proof.
have biginT := eq_bigl _ _ (fun _ => andbT _) => tiP.
by rewrite -biginT big_trivIset_cond //; apply: eq_bigr => A _; apply: biginT.
Qed.

Lemma set_partition_big_cond P D (K : pred T) (E : T -> R) :
  partition P D -> \big[op/idx]_(x in D | K x) E x = rhs_cond P K E.
Proof.
by case/and3P=> /eqP <- tI_P _; apply: big_trivIset_cond.
Qed.

Lemma set_partition_big P D (E : T -> R) :
  partition P D -> \big[op/idx]_(x in D) E x = rhs P E.
Proof.
by case/and3P=> /eqP <- tI_P _; apply: big_trivIset.
Qed.

Lemma partition_disjoint_bigcup (F : I -> {set T}) E :
    (forall i j, i != j -> [disjoint F i & F j]) ->
  \big[op/idx]_(x in \bigcup_i F i) E x =
    \big[op/idx]_i \big[op/idx]_(x in F i) E x.
Admitted.

End BigOps.

Section Equivalence.

Variables (R : rel T) (D : {set T}).

Let Px x := [set y in D | R x y].
Definition equivalence_partition := [set Px x | x in D].
Local Notation P := equivalence_partition.
Hypothesis eqiR : {in D & &, equivalence_rel R}.

Let Pxx x : x \in D -> x \in Px x.
Admitted.
Let PPx x : x \in D -> Px x \in P := fun Dx => imset_f _ Dx.

Lemma equivalence_partitionP : partition P D.
Admitted.

Lemma pblock_equivalence_partition :
  {in D &, forall x y, (y \in pblock P x) = R x y}.
Admitted.

End Equivalence.

Lemma pblock_equivalence P D :
  partition P D -> {in D & &, equivalence_rel (fun x y => y \in pblock P x)}.
Admitted.

Lemma equivalence_partition_pblock P D :
  partition P D -> equivalence_partition (fun x y => y \in pblock P x) D = P.
Admitted.

Section Preim.

Variables (rT : eqType) (f : T -> rT).

Definition preim_partition := equivalence_partition (fun x y => f x == f y).

Lemma preim_partitionP D : partition (preim_partition D) D.
Admitted.

End Preim.

Lemma preim_partition_pblock P D :
  partition P D -> preim_partition (pblock P) D = P.
Admitted.

Lemma transversalP P D : partition P D -> is_transversal (transversal P D) P D.
Admitted.

Section Transversals.

Variables (X : {set T}) (P : {set {set T}}) (D : {set T}).
Hypothesis trPX : is_transversal X P D.

Lemma transversal_sub : X \subset D.
Admitted.

Let tiP : trivIset P.
Admitted.

Let sXP : {subset X <= cover P}.
Admitted.

Let trX : {in P, forall B, #|X :&: B| == 1}.
Admitted.

Lemma setI_transversal_pblock x0 B :
  B \in P -> X :&: B = [set transversal_repr x0 X B].
Admitted.

Lemma repr_mem_pblock x0 B : B \in P -> transversal_repr x0 X B \in B.
Admitted.

Lemma repr_mem_transversal x0 B : B \in P -> transversal_repr x0 X B \in X.
Admitted.

Lemma transversal_reprK x0 : {in P, cancel (transversal_repr x0 X) (pblock P)}.
Admitted.

Lemma pblockK x0 : {in X, cancel (pblock P) (transversal_repr x0 X)}.
Admitted.

Lemma pblock_inj : {in X &, injective (pblock P)}.
Admitted.

Lemma pblock_transversal : pblock P @: X = P.
Admitted.

Lemma card_transversal : #|X| = #|P|.
Admitted.

Lemma im_transversal_repr x0 : transversal_repr x0 X @: P = X.
Admitted.

End Transversals.

End Partitions.

Arguments trivIsetP {T P}.
Arguments big_trivIset_cond [T R idx op] P [K E].
Arguments set_partition_big_cond [T R idx op] P [D K E].
Arguments big_trivIset [T R idx op] P [E].
Arguments set_partition_big [T R idx op] P [D E].

Prenex Implicits cover trivIset partition pblock.

Lemma partition_partition (T : finType) (D : {set T}) P Q :
    partition P D -> partition Q P ->
  partition (cover @: Q) D /\ {in Q &, injective cover}.
Admitted.

Lemma indexed_partition (I T : finType) (J : {pred I}) (B : I -> {set T}) :
  let P := [set B i | i in J] in
  {in J &, forall i j : I, j != i -> [disjoint B i & B j]} ->
  (forall i : I, J i -> B i != set0) -> partition P (cover P) /\ {in J &, injective B}.
Admitted.

Section PartitionImage.
Variables (T : finType) (P : {set {set T}}) (D : {set T}).
Variables (T' : finType) (f : T -> T') (inj_f : injective f).
Let fP := [set f @: (B : {set T}) | B in P].

Lemma imset_trivIset : trivIset fP = trivIset P.
Admitted.

Lemma imset0mem : (set0 \in fP) = (set0 \in P).
Admitted.

Lemma imset_partition : partition fP (f @: D) = partition P D.
Admitted.
End PartitionImage.

 
 
 
 
 

Section MaxSetMinSet.

Variable T : finType.
Notation sT := {set T}.
Implicit Types A B C : sT.
Implicit Type P : pred sT.

Definition minset P A := [forall (B : sT | B \subset A), (B == A) == P B].

Lemma minset_eq P1 P2 A : P1 =1 P2 -> minset P1 A = minset P2 A.
Admitted.

Lemma minsetP P A :
  reflect ((P A) /\ (forall B, P B -> B \subset A -> B = A)) (minset P A).
Admitted.
Arguments minsetP {P A}.

Lemma minsetp P A : minset P A -> P A.
Admitted.

Lemma minsetinf P A B : minset P A -> P B -> B \subset A -> B = A.
Admitted.

Lemma ex_minset P : (exists A, P A) -> {A | minset P A}.
Admitted.

Lemma minset_exists P C : P C -> {A | minset P A & A \subset C}.
Admitted.

 
Fact maxset_key : unit.
Admitted.
Definition maxset P A :=
  minset (fun B => locked_with maxset_key P (~: B)) (~: A).

Lemma maxset_eq P1 P2 A : P1 =1 P2 -> maxset P1 A = maxset P2 A.
Admitted.

Lemma maxminset P A : maxset P A = minset [pred B | P (~: B)] (~: A).
Admitted.

Lemma minmaxset P A : minset P A = maxset [pred B | P (~: B)] (~: A).
Admitted.

Lemma maxsetP P A :
  reflect ((P A) /\ (forall B, P B -> A \subset B -> B = A)) (maxset P A).
Admitted.

Lemma maxsetp P A : maxset P A -> P A.
Admitted.

Lemma maxsetsup P A B : maxset P A -> P B -> A \subset B -> B = A.
Admitted.

Lemma ex_maxset P : (exists A, P A) -> {A | maxset P A}.
Admitted.

Lemma maxset_exists P C : P C -> {A : sT | maxset P A & C \subset A}.
Admitted.

End MaxSetMinSet.

Arguments setCK {T}.
Arguments minsetP {T P A}.
Arguments maxsetP {T P A}.
Prenex Implicits minset maxset.

Section SetFixpoint.

Section Least.
Variables (T : finType) (F : {set T} -> {set T}).
Hypothesis (F_mono : {homo F : X Y / X \subset Y}).

Let n := #|T|.
Let iterF i := iter i F set0.

Lemma subset_iterS i : iterF i \subset iterF i.+1.
Admitted.

Lemma subset_iter : {homo iterF : i j / i <= j >-> i \subset j}.
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
Admitted.

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

Definition funsetC X := ~: (F (~: X)).
Lemma funsetC_mono : {homo funsetC : X Y / X \subset Y}.
Admitted.
Hint Resolve funsetC_mono : core.

Definition cofixset := ~: fixset funsetC.

Lemma cofixsetK : F cofixset = cofixset.
Admitted.

Lemma maxset_cofix : maxset [pred X | F X == X] cofixset.
Admitted.

End Greatest.

End SetFixpoint.

#[deprecated(since="mathcomp 1.13.0", note="Use mem_imset instead.")]
Notation mem_imset_eq := mem_imset (only parsing).
#[deprecated(since="mathcomp 1.13.0", note="Use mem_imset2 instead.")]
Notation mem_imset2_eq := mem_imset2 (only parsing).

End finset.

End mathcomp_DOT_ssreflect_DOT_finset_WRAPPED.
Module Export mathcomp_DOT_ssreflect_DOT_finset.
Module Export mathcomp.
Module Export ssreflect.
Module finset.
Include mathcomp_DOT_ssreflect_DOT_finset_WRAPPED.finset.
End finset.

End ssreflect.

End mathcomp.

End mathcomp_DOT_ssreflect_DOT_finset.
Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.
Module Export ssralg.
Import mathcomp.ssreflect.ssreflect.
Import mathcomp.ssreflect.ssrfun.
Import mathcomp.ssreflect.ssrbool.
Import mathcomp.ssreflect.eqtype.
Import mathcomp.ssreflect.ssrnat.
Import mathcomp.ssreflect.seq.
Import mathcomp.ssreflect.choice.
Import mathcomp.ssreflect.fintype.
Import mathcomp.ssreflect.finfun.
Import mathcomp.ssreflect.bigop.

Set Implicit Arguments.
Unset Strict Implicit.

Declare Scope ring_scope.
Declare Scope term_scope.
Reserved Notation "n %:R" (at level 2, left associativity, format "n %:R").

Reserved Notation "x %:T" (at level 2, left associativity, format "x %:T").
Reserved Notation "''X_' i" (at level 8, i at level 2, format "''X_' i").

Reserved Notation "''exists' ''X_' i , f"
  (at level 199, i at level 2, right associativity,
   format "'[hv' ''exists'  ''X_' i , '/ '  f ']'").
Reserved Notation "''forall' ''X_' i , f"
  (at level 199, i at level 2, right associativity,
   format "'[hv' ''forall'  ''X_' i , '/ '  f ']'").

Delimit Scope ring_scope with R.
Delimit Scope term_scope with T.
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

Definition pack m :=
  fun bT b & phant_id (Choice.class bT) b => Pack (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> Choice.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Canonical eqType.
Canonical choiceType.
Notation zmodType := type.
Notation ZmodType T m := (@pack T m _ _ id).
Notation ZmodMixin := Mixin.
End Exports.

End Zmodule.

Definition zero V := Zmodule.zero (Zmodule.class V).
Definition opp V := Zmodule.opp (Zmodule.class V).
Definition add V := Zmodule.add (Zmodule.class V).

Local Notation "0" := (zero _) : ring_scope.
Local Notation "- x" := (opp x) : ring_scope.
Local Notation "+%R" := (@add _) : fun_scope.
Local Notation "x + y" := (add x y) : ring_scope.
Local Notation "x - y" := (x + - y) : ring_scope.

Definition natmul V x n := nosimpl iterop _ n +%R x (zero V).

Local Notation "x *+ n" := (natmul x n) : ring_scope.

Local Notation "s `_ i" := (nth 0 s i) : ring_scope.

Section ZmoduleTheory.

Variable V : zmodType.
Implicit Types x y : V.

Lemma subr_eq0 x y : (x - y == 0) = (x == y).
Admitted.

End ZmoduleTheory.

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

Definition EtaMixin R one mul mulA mul1x mulx1 mul_addl mul_addr nz1 :=
  let _ := @Mixin R one mul mulA mul1x mulx1 mul_addl mul_addr nz1 in
  @Mixin (Zmodule.Pack (Zmodule.class R)) _ _
     mulA mul1x mulx1 mul_addl mul_addr nz1.

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

Definition pack b0 (m0 : mixin_of (@Zmodule.Pack T b0)) :=
  fun bT b & phant_id (Zmodule.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition zmodType := @Zmodule.Pack cT class.

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> Zmodule.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Canonical eqType.
Canonical choiceType.
Canonical zmodType.
Notation ringType := type.
Notation RingType T m := (@pack T _ m _ _ id _ id).
Notation RingMixin := Mixin.
End Exports.

End Ring.
Import Ring.Exports.
Definition one (R : ringType) : R.
exact (Ring.one (Ring.class R)).
Defined.
Definition mul (R : ringType) : R -> R -> R.
exact (Ring.mul (Ring.class R)).
Defined.
Definition exp R x n := nosimpl iterop _ n (@mul R) x (one R).
Definition comm R x y := @mul R x y = mul y x.

Local Notation "1" := (one _) : ring_scope.
Local Notation "n %:R" := (1 *+ n) : ring_scope.
Local Notation "*%R" := (@mul _) : fun_scope.
Local Notation "x * y" := (mul x y) : ring_scope.
Local Notation "x ^+ n" := (exp x n) : ring_scope.

Module Export Lmodule.

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
Variable (phR : phant R) (T : Type) (cT : type phR).

Definition pack b0 (m0 : mixin_of R (@Zmodule.Pack T b0)) :=
  fun bT b & phant_id (Zmodule.class bT) b =>
  fun    m & phant_id m0 m => Pack phR (@Class T b m).

End ClassDef.

Module Import Exports.
Coercion sort : type >-> Sortclass.
Notation lmodType R := (type (Phant R)).
Notation LmodType R T m := (@pack _ (Phant R) T _ m _ _ id _ id).
Notation LmodMixin := Mixin.
End Exports.

End Lmodule.
Import Lmodule.Exports.
Definition scale (R : ringType) (V : lmodType R) : R -> V -> V.
Admitted.

Module ComRing.

Definition RingMixin R one mul mulA mulC mul1x mul_addl :=
  let mulx1 := Monoid.mulC_id mulC mul1x in
  let mul_addr := Monoid.mulC_dist mulC mul_addl in
  @Ring.EtaMixin R one mul mulA mul1x mulx1 mul_addl mul_addr.

Section ClassDef.
Record class_of R :=
  Class {base : Ring.class_of R; mixin : commutative (Ring.mul base)}.
Local Coercion base : class_of >-> Ring.class_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variable (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Definition pack mul0 (m0 : @commutative T T mul0) :=
  fun bT b & phant_id (Ring.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition zmodType := @Zmodule.Pack cT class.
Definition ringType := @Ring.Pack cT class.

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> Ring.class_of.
Coercion sort : type >-> Sortclass.
Canonical eqType.
Canonical zmodType.
Canonical ringType.
Notation comRingType := type.
Notation ComRingType T m := (@pack T _ m _ _ id _ id).
Notation ComRingMixin := RingMixin.
End Exports.

End ComRing.
Import ComRing.Exports.

Module UnitRing.

Record mixin_of (R : ringType) : Type := Mixin {
  unit : pred R;
  inv : R -> R;
  _ : {in unit, left_inverse 1 inv *%R};
  _ : {in unit, right_inverse 1 inv *%R};
  _ : forall x y, y * x = 1 /\ x * y = 1 -> unit x;
  _ : {in [predC unit], inv =1 id}
}.

Definition EtaMixin R unit inv mulVr mulrV unitP inv_out :=
  let _ := @Mixin R unit inv mulVr mulrV unitP inv_out in
  @Mixin (Ring.Pack (Ring.class R)) unit inv mulVr mulrV unitP inv_out.

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

Definition pack b0 (m0 : mixin_of (@Ring.Pack T b0)) :=
  fun bT b & phant_id (Ring.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition zmodType := @Zmodule.Pack cT class.
Definition ringType := @Ring.Pack cT class.

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> Ring.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Canonical eqType.
Canonical zmodType.
Canonical ringType.
Notation unitRingType := type.
Notation UnitRingType T m := (@pack T _ m _ _ id _ id).
Notation UnitRingMixin := EtaMixin.
End Exports.

End UnitRing.
Import UnitRing.Exports.

Definition unit {R : unitRingType} :=
  [qualify a u : R | UnitRing.unit (UnitRing.class R) u].
Definition inv {R : unitRingType} : R -> R.
Admitted.

Local Notation "x ^-1" := (inv x).

Module ComUnitRing.

Section Mixin.

Variables (R : comRingType) (unit : pred R) (inv : R -> R).
Hypothesis mulVx : {in unit, left_inverse 1 inv *%R}.
Hypothesis unitPl : forall x y, y * x = 1 -> unit x.

Fact mulC_mulrV : {in unit, right_inverse 1 inv *%R}.
Admitted.

Fact mulC_unitP x y : y * x = 1 /\ x * y = 1 -> unit x.
Admitted.

Definition Mixin := UnitRingMixin mulVx mulC_mulrV mulC_unitP.

End Mixin.

Section ClassDef.
Record class_of (R : Type) : Type := Class {
  base : ComRing.class_of R;
  mixin : UnitRing.mixin_of (Ring.Pack base)
}.
Definition base2 R m := UnitRing.Class (@mixin R m).
Local Coercion base2 : class_of >-> UnitRing.class_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition ringType := @Ring.Pack cT class.
Definition unitRingType := @UnitRing.Pack cT class.

End ClassDef.

Module Import Exports.
Coercion base : class_of >-> ComRing.class_of.
Coercion base2 : class_of >-> UnitRing.class_of.
Coercion sort : type >-> Sortclass.
Canonical ringType.
Canonical unitRingType.
Notation comUnitRingType := type.
End Exports.

End ComUnitRing.
Import ComUnitRing.Exports.

Section TermDef.

Variable R : Type.

Inductive term : Type :=
| Var of nat
| Const of R
| NatConst of nat
| Add of term & term
| Opp of term
| NatMul of term & nat
| Mul of term & term
| Inv of term
| Exp of term & nat.

Inductive formula : Type :=
| Bool of bool
| Equal of term & term
| Unit of term
| And of formula & formula
| Or of formula & formula
| Implies of formula & formula
| Not of formula
| Exists of nat & formula
| Forall of nat & formula.

End TermDef.
Bind Scope term_scope with formula.
Arguments Add {R} t1%T t2%T.
Arguments And {R} f1%T f2%T.
Arguments Or {R} f1%T f2%T.
Arguments Exists {R} i%N f1%T.

Arguments Bool {R} b.
Arguments Const {R} x.

Notation True := (Bool true).
Notation False := (Bool false).

Local Notation "''X_' i" := (Var _ i) : term_scope.
Local Notation "n %:R" := (NatConst _ n) : term_scope.
Local Notation "x %:T" := (Const x) : term_scope.
Local Infix "+" := Add : term_scope.
Local Notation "- t" := (Opp t) : term_scope.
Local Infix "*" := Mul : term_scope.
Local Infix "*+" := NatMul : term_scope.
Local Notation "t ^-1" := (Inv t) : term_scope.
Local Infix "^+" := Exp : term_scope.
Local Infix "==" := Equal : term_scope.
Local Infix "/\" := And : term_scope.
Local Infix "\/" := Or : term_scope.
Local Infix "==>" := Implies : term_scope.
Local Notation "~ f" := (Not f) : term_scope.
Local Notation "''exists' ''X_' i , f" := (Exists i f) : term_scope.
Local Notation "''forall' ''X_' i , f" := (Forall i f) : term_scope.

Section EvalTerm.

Variable R : unitRingType.
Fixpoint eval (e : seq R) (t : term R) {struct t} : R.
exact (match t with
  | ('X_i)%T => e`_i
  | (x%:T)%T => x
  | (n%:R)%T => n%:R
  | (t1 + t2)%T => eval e t1 + eval e t2
  | (- t1)%T => - eval e t1
  | (t1 *+ n)%T => eval e t1 *+ n
  | (t1 * t2)%T => eval e t1 * eval e t2
  | t1^-1%T => (eval e t1)^-1
  | (t1 ^+ n)%T => eval e t1 ^+ n
  end).
Defined.
Fixpoint holds (e : seq R) (f : formula R) {struct f} : Prop.
exact (match f with
  | Bool b => b
  | (t1 == t2)%T => eval e t1 = eval e t2
  | Unit t1 => eval e t1 \in unit
  | (f1 /\ f2)%T => holds e f1 /\ holds e f2
  | (f1 \/ f2)%T => holds e f1 \/ holds e f2
  | (f1 ==> f2)%T => holds e f1 -> holds e f2
  | (~ f1)%T => ~ holds e f1
  | ('exists 'X_i, f1)%T => exists x, holds (set_nth 0 e i x) f1
  | ('forall 'X_i, f1)%T => forall x, holds (set_nth 0 e i x) f1
  end).
Defined.

Fixpoint rterm (t : term R) :=
  match t with
  | _^-1 => false
  | t1 + t2 | t1 * t2 => rterm t1 && rterm t2
  | - t1 | t1 *+ _ | t1 ^+ _ => rterm t1
  | _ => true
  end%T.

Fixpoint rformula (f : formula R) :=
  match f with
  | Bool _ => true
  | t1 == t2 => rterm t1 && rterm t2
  | Unit t1 => false
  | f1 /\ f2 | f1 \/ f2 | f1 ==> f2 => rformula f1 && rformula f2
  | ~ f1 | ('exists 'X__, f1) | ('forall 'X__, f1) => rformula f1
  end%T.

Fixpoint qf_form (f : formula R) :=
  match f with
  | Bool _ | _ == _ | Unit _ => true
  | f1 /\ f2 | f1 \/ f2 | f1 ==> f2 => qf_form f1 && qf_form f2
  | ~ f1 => qf_form f1
  | _ => false
  end%T.

Definition qf_eval e := fix loop (f : formula R) : bool :=
  match f with
  | Bool b => b
  | t1 == t2 => (eval e t1 == eval e t2)%bool
  | Unit t1 => eval e t1 \in unit
  | f1 /\ f2 => loop f1 && loop f2
  | f1 \/ f2 => loop f1 || loop f2
  | f1 ==> f2 => (loop f1 ==> loop f2)%bool
  | ~ f1 => ~~ loop f1
  |_ => false
  end%T.

Lemma qf_evalP e f : qf_form f -> reflect (holds e f) (qf_eval e f).
Admitted.

Section Pick.

Variables (I : finType) (pred_f then_f : I -> formula R) (else_f : formula R).

Definition Pick :=
  \big[Or/False]_(p : {ffun pred I})
    ((\big[And/True]_i (if p i then pred_f i else ~ pred_f i))
    /\ (if pick p is Some i then then_f i else else_f))%T.

End Pick.

End EvalTerm.

Module IntegralDomain.

Definition axiom (R : ringType) :=
  forall x y : R, x * y = 0 -> (x == 0) || (y == 0).

Section ClassDef.
Record class_of (R : Type) : Type :=
  Class {base : ComUnitRing.class_of R; mixin : axiom (Ring.Pack base)}.
Local Coercion base : class_of >-> ComUnitRing.class_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variable (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition ringType := @Ring.Pack cT class.
Definition unitRingType := @UnitRing.Pack cT class.

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> ComUnitRing.class_of.
Coercion sort : type >-> Sortclass.
Canonical ringType.
Canonical unitRingType.
Notation idomainType := type.
End Exports.

End IntegralDomain.
Import IntegralDomain.Exports.

Module Export Field.

Definition mixin_of (R : unitRingType) := forall x : R, x != 0 -> x \in unit.

Section Mixins.

Definition axiom (R : ringType) inv := forall x : R, x != 0 -> inv x * x = 1.

Variables (R : comRingType) (inv : R -> R).
Hypotheses (mulVf : axiom inv) (inv0 : inv 0 = 0).

Fact intro_unit (x y : R) : y * x = 1 -> x != 0.
Admitted.

Fact inv_out : {in predC (predC1 0), inv =1 id}.
Admitted.

Definition UnitMixin := ComUnitRing.Mixin mulVf intro_unit inv_out.

End Mixins.

Section ClassDef.
Record class_of (F : Type) : Type := Class {
  base : IntegralDomain.class_of F;
  mixin : mixin_of (UnitRing.Pack base)
}.
Local Coercion base : class_of >-> IntegralDomain.class_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variable (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition zmodType := @Zmodule.Pack cT class.
Definition ringType := @Ring.Pack cT class.
Definition comRingType := @ComRing.Pack cT class.
Definition comUnitRingType := @ComUnitRing.Pack cT class.
Definition idomainType := @IntegralDomain.Pack cT class.

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> IntegralDomain.class_of.
Canonical eqType.
Canonical choiceType.
Canonical zmodType.
Canonical ringType.
Canonical comRingType.
Coercion comUnitRingType : type >-> ComUnitRing.type.
Canonical comUnitRingType.
Canonical idomainType.
Notation fieldType := type.
Notation FieldUnitMixin := UnitMixin.
End Exports.

End Field.

Module Export DecidableField.

Definition axiom (R : unitRingType) (s : seq R -> pred (formula R)) :=
  forall e f, reflect (holds e f) (s e f).

Record mixin_of (R : unitRingType) : Type :=
  Mixin { sat : seq R -> pred (formula R); satP : axiom sat}.

Section ClassDef.
Record class_of (F : Type) : Type :=
  Class {base : Field.class_of F; mixin : mixin_of (UnitRing.Pack base)}.
Local Coercion base : class_of >-> Field.class_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variable (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition comRingType := @ComRing.Pack cT class.
Definition comUnitRingType := @ComUnitRing.Pack cT class.
Definition fieldType := @Field.Pack cT class.

End ClassDef.

Module Export Exports.
Coercion mixin : class_of >-> mixin_of.
Canonical comRingType.
Coercion comUnitRingType : type >-> ComUnitRing.type.
Canonical fieldType.
Notation decFieldType := type.
End Exports.

End DecidableField.

Section DecidableFieldTheory.

Variable F : decFieldType.

Definition sat := DecidableField.sat (DecidableField.class F).

Lemma satP : DecidableField.axiom sat.
Admitted.

End DecidableFieldTheory.

Module Export Theory.
Definition subr_eq0 := subr_eq0.
Definition satP {F e f} := @satP F e f.

End Theory.

End GRing.
Export Zmodule.Exports.
Export Ring.Exports.
Export Lmodule.Exports.
Export UnitRing.Exports.
Export ComRing.Exports.
Export ComUnitRing.Exports.
Export IntegralDomain.Exports.
Export Field.Exports.
Export DecidableField.Exports.

Notation "0" := (zero _) : ring_scope.
Notation "- x" := (opp x) : ring_scope.
Notation "+%R" := (@add _) : fun_scope.
Notation "x + y" := (add x y) : ring_scope.
Notation "x - y" := (add x (- y)) : ring_scope.
Notation "x *+ n" := (natmul x n) : ring_scope.
Notation "s `_ i" := (seq.nth 0%R s%R i) : ring_scope.

Notation "1" := (one _) : ring_scope.
Notation "- 1" := (opp 1) : ring_scope.

Notation "n %:R" := (natmul 1 n) : ring_scope.
Notation "*%R" := (@mul _) : fun_scope.
Notation "x * y" := (mul x y) : ring_scope.
Notation "x ^+ n" := (exp x n) : ring_scope.
Notation "x ^-1" := (inv x) : ring_scope.
Notation "x ^- n" := (inv (x ^+ n)) : ring_scope.
Notation "a *: m" := (scale a m) : ring_scope.
Notation "\sum_ i F" :=
  (\big[+%R/0%R]_i F%R) : ring_scope.
Notation "\sum_ ( i : t ) F" :=
  (\big[+%R/0%R]_(i : t) F%R) (only parsing) : ring_scope.
Notation "\sum_ ( i < n ) F" :=
  (\big[+%R/0%R]_(i < n) F%R) : ring_scope.
Notation "\prod_ i F" :=
  (\big[*%R/1%R]_i F%R) : ring_scope.

Notation "''X_' i" := (Var _ i) : term_scope.
Notation "n %:R" := (NatConst _ n) : term_scope.
Notation "0" := 0%:R%T : term_scope.
Notation "x %:T" := (Const x) : term_scope.
Infix "+" := Add : term_scope.
Notation "- t" := (Opp t) : term_scope.
Notation "t - u" := (Add t (- u)) : term_scope.
Infix "*" := Mul : term_scope.
Infix "*+" := NatMul : term_scope.
Notation "t ^-1" := (Inv t) : term_scope.
Infix "^+" := Exp : term_scope.
Infix "==" := Equal : term_scope.
Notation "x != y" := (GRing.Not (x == y)) : term_scope.
Infix "/\" := And : term_scope.
Infix "\/" := Or : term_scope.
Infix "==>" := Implies : term_scope.
Notation "~ f" := (Not f) : term_scope.
Notation "''exists' ''X_' i , f" := (Exists i f) : term_scope.
Notation "''forall' ''X_' i , f" := (Forall i f) : term_scope.

End ssralg.
Import mathcomp.ssreflect.ssreflect.
Import mathcomp.ssreflect.ssrbool.
Import mathcomp.ssreflect.ssrfun.
Import mathcomp.ssreflect.eqtype.
Import mathcomp.ssreflect.choice.
Import mathcomp.ssreflect.fintype.
Import mathcomp.ssreflect.finset.

Set Implicit Arguments.
Unset Strict Implicit.

Declare Scope group_scope.
Declare Scope Group_scope.

Delimit Scope group_scope with g.
Delimit Scope Group_scope with G.
Open Scope group_scope.

Module Export FinGroup.

Record mixin_of (T : Type) : Type := BaseMixin {
  mul : T -> T -> T;
  one : T;
  inv : T -> T;
  _ : associative mul;
  _ : left_id one mul;
  _ : involutive inv;
  _ : {morph inv : x y / mul x y >-> mul y x}
}.

Structure base_type : Type := PackBase {
  sort : Type;
   _ : mixin_of sort;
   _ : Finite.class_of sort
}.

Definition arg_sort := sort.

Definition mixin T :=
  let: PackBase _ m _ := T return mixin_of (sort T) in m.

Definition finClass T :=
  let: PackBase _ _ m := T return Finite.class_of (sort T) in m.

Structure type : Type := Pack {
  base : base_type;
  _ : left_inverse (one (mixin base)) (inv (mixin base)) (mul (mixin base))
}.

Section Mixin.

Variables (T : Type) (one : T) (mul : T -> T -> T) (inv : T -> T).

Hypothesis mulA : associative mul.
Hypothesis mul1 : left_id one mul.
Hypothesis mulV : left_inverse one inv mul.
Infix "*" := mul.

Lemma mk_invgK : involutive inv.
Admitted.

Lemma mk_invMg : {morph inv : x y / x * y >-> y * x}.
Admitted.

Definition Mixin := BaseMixin mulA mul1 mk_invgK mk_invMg.

End Mixin.

Definition pack_base T m :=
  fun c cT & phant_id (Finite.class cT) c => @PackBase T m c.

Section InheritedClasses.

Variable bT : base_type.
Local Notation T := (arg_sort bT).
Local Notation class := (finClass bT).
Canonical finType := Finite.Pack class.
Definition arg_finType := Eval hnf in [finType of T].

End InheritedClasses.
Coercion base : type >-> base_type.
Coercion arg_finType : base_type >-> Finite.type.
Notation baseFinGroupType := base_type.
Notation finGroupType := type.
Notation BaseFinGroupType T m := (@pack_base T m _ _ id).
Notation FinGroupType := Pack.

Section ElementOps.

Variable T : baseFinGroupType.
Notation rT := (FinGroup.sort T).
Definition oneg : rT.
Admitted.
Definition mulg : T -> T -> rT.
Admitted.

End ElementOps.

Notation "1" := (oneg _) : group_scope.
Notation "x1 * x2" := (mulg x1 x2) : group_scope.

Section BaseSetMulDef.

Variable gT : baseFinGroupType.
Definition group_set_baseGroupMixin : FinGroup.mixin_of (set_type gT).
Admitted.

Canonical group_set_baseGroupType :=
  Eval hnf in BaseFinGroupType (set_type gT) group_set_baseGroupMixin.

End BaseSetMulDef.

Module Export GroupSet.
Definition sort (gT : baseFinGroupType) := {set gT}.
Identity Coercion GroupSet_of_sort : GroupSet.sort >-> set_of.

Section GroupSetMulProp.

Variable gT : finGroupType.
Implicit Types A B C D : {set gT}.

Definition group_set A := (1 \in A) && (A * A \subset A).

Structure group_type : Type := Group {
  gval :> GroupSet.sort gT;
  _ : group_set gval
}.
Definition group_of of phant gT : predArgType.
exact (group_type).
Defined.
Local Notation groupT := (group_of (Phant gT)).

Canonical group_subType := Eval hnf in [subType for gval].
Definition group_eqMixin := Eval hnf in [eqMixin of group_type by <:].
Canonical group_eqType := Eval hnf in EqType group_type group_eqMixin.
Definition group_choiceMixin := [choiceMixin of group_type by <:].
Canonical group_choiceType :=
  Eval hnf in ChoiceType group_type group_choiceMixin.
Definition group_countMixin := [countMixin of group_type by <:].
Canonical group_countType := Eval hnf in CountType group_type group_countMixin.
Canonical group_subCountType := Eval hnf in [subCountType of group_type].
Definition group_finMixin := [finMixin of group_type by <:].
Canonical group_finType := Eval hnf in FinType group_type group_finMixin.

Definition generated A := \bigcap_(G : groupT | A \subset G) G.
Definition cycle x := generated [set x].

End GroupSetMulProp.

Notation "{ 'group' gT }" := (group_of (Phant gT))
  (at level 0, format "{ 'group'  gT }") : type_scope.
Notation "<[ x ] >"  := (cycle x) : group_scope.

Module Export perm.
Import mathcomp.ssreflect.ssrnat.
Import mathcomp.ssreflect.seq.
Import mathcomp.ssreflect.fintype.
Import mathcomp.ssreflect.finfun.

Section PermDefSection.

Variable T : finType.

Inductive perm_type : predArgType :=
  Perm (pval : {ffun T -> T}) & injectiveb pval.
Definition pval p := let: Perm f _ := p in f.
Definition perm_of of phant T := perm_type.

Canonical perm_subType := Eval hnf in [subType for pval].
Definition perm_eqMixin := Eval hnf in [eqMixin of perm_type by <:].
Canonical perm_eqType := Eval hnf in EqType perm_type perm_eqMixin.
Definition perm_choiceMixin := [choiceMixin of perm_type by <:].
Canonical perm_choiceType := Eval hnf in ChoiceType perm_type perm_choiceMixin.
Definition perm_countMixin := [countMixin of perm_type by <:].
Canonical perm_countType := Eval hnf in CountType perm_type perm_countMixin.
Canonical perm_subCountType := Eval hnf in [subCountType of perm_type].
Definition perm_finMixin := [finMixin of perm_type by <:].
Canonical perm_finType := Eval hnf in FinType perm_type perm_finMixin.

Lemma perm_proof (f : T -> T) : injective f -> injectiveb (finfun f).
Admitted.

End PermDefSection.

Notation "{ 'perm' T }" := (perm_of (Phant T))
  (at level 0, format "{ 'perm'  T }") : type_scope.

Notation "''S_' n" := {perm 'I_n}
  (at level 8, n at level 2, format "''S_' n").

Local Notation fun_of_perm_def := (fun T (u : perm_type T) => val u : T -> T).
Local Notation perm_def := (fun T f injf => Perm (@perm_proof T f injf)).

Module Type PermDefSig.
Parameter fun_of_perm : forall T, perm_type T -> T -> T.
Parameter perm : forall (T : finType) (f : T -> T), injective f -> {perm T}.
End PermDefSig.

Module PermDef : PermDefSig.
Definition fun_of_perm := fun_of_perm_def.
Definition perm := perm_def.
End PermDef.

Notation fun_of_perm := PermDef.fun_of_perm.
Notation perm := (@PermDef.perm _ _).
Coercion fun_of_perm : perm_type >-> Funclass.

Section Theory.

Variable T : finType.
Implicit Types (x y : T) (s t : {perm T}) (S : {set T}).

Lemma perm_inj {s} : injective s.
Admitted.

Lemma perm_onto s : codom s =i predT.
Admitted.

Definition perm_one := perm (@inj_id T).

Lemma perm_invK s : cancel (fun x => iinv (perm_onto s x)) s.
Admitted.

Definition perm_inv s := perm (can_inj (perm_invK s)).

Definition perm_mul s t := perm (inj_comp (@perm_inj t) (@perm_inj s)).

Lemma perm_oneP : left_id perm_one perm_mul.
Admitted.

Lemma perm_invP : left_inverse perm_one perm_inv perm_mul.
Admitted.

Lemma perm_mulP : associative perm_mul.
Admitted.
Definition perm_of_baseFinGroupMixin : FinGroup.mixin_of (perm_type T).
exact (FinGroup.Mixin perm_mulP perm_oneP perm_invP).
Defined.
Canonical perm_baseFinGroupType :=
  Eval hnf in BaseFinGroupType (perm_type T) perm_of_baseFinGroupMixin.
Canonical perm_finGroupType := @FinGroupType perm_baseFinGroupType perm_invP.

Lemma tperm_proof x y : involutive [fun z => z with x |-> y, y |-> x].
Admitted.

Definition tperm x y := perm (can_inj (tperm_proof x y)).

End Theory.

Section PermutationParity.

Variable T : finType.

Implicit Types (s t u v : {perm T}) (x y z a b : T).

Definition aperm x s := s x.
Definition porbit s x := aperm x @: <[s]>.
Definition porbits s := porbit s @: T.
Definition odd_perm (s : perm_type T) := odd #|T| (+) odd #|porbits s|.

End PermutationParity.

Coercion odd_perm : perm_type >-> bool.

End perm.
Import mathcomp.ssreflect.ssrnat.
Import mathcomp.ssreflect.div.

Section ZpDef.

Variable p' : nat.
Local Notation p := p'.+1.

Implicit Types x y z : 'I_p.

Definition inZp i := Ordinal (ltn_pmod i (ltn0Sn p')).
Definition Zp0 : 'I_p.
Admitted.
Definition Zp_opp x := inZp (p - x).
Definition Zp_add x y := inZp (x + y).

Lemma Zp_add0z : left_id Zp0 Zp_add.
Admitted.

Lemma Zp_addNz : left_inverse Zp0 Zp_opp Zp_add.
Admitted.

Lemma Zp_addA : associative Zp_add.
Admitted.

Lemma Zp_addC : commutative Zp_add.
Admitted.

Definition Zp_zmodMixin := ZmodMixin Zp_addA Zp_addC Zp_add0z Zp_addNz.
Canonical Zp_zmodType := Eval hnf in ZmodType 'I_p Zp_zmodMixin.

End ZpDef.
Import mathcomp.ssreflect.seq.
Import mathcomp.ssreflect.finfun.
Local Open Scope ring_scope.

Reserved Notation "''M_' n"     (at level 8, n at level 2, format "''M_' n").
Reserved Notation "''rV_' n"    (at level 8, n at level 2, format "''rV_' n").

Reserved Notation "''M_' ( m , n )" (at level 8, format "''M_' ( m ,  n )").
Reserved Notation "''M[' R ]_ n"    (at level 8, n at level 2).

Reserved Notation "''rV[' R ]_ n"   (at level 8, n at level 2).

Reserved Notation "''M[' R ]_ ( m , n )" (at level 8).
Reserved Notation "\matrix_ ( i < n ) E"
  (at level 36, E at level 36, i, n at level 50).

Reserved Notation "\matrix_ ( i , j ) E"
  (at level 36, E at level 36, i, j at level 50,
   format "\matrix_ ( i ,  j )  E").
Reserved Notation "\matrix[ k ]_ ( i , j ) E"
  (at level 36, E at level 36, i, j at level 50,
   format "\matrix[ k ]_ ( i ,  j )  E").
Reserved Notation "\matrix_ ( i < m , j < n ) E"
  (at level 36, E at level 36, i, m, j, n at level 50).

Reserved Notation "\row_ j E"
  (at level 36, E at level 36, j at level 2,
   format "\row_ j  E").
Reserved Notation "\row_ ( j < n ) E"
  (at level 36, E at level 36, j, n at level 50).

Reserved Notation "x %:M"   (at level 8, format "x %:M").
Reserved Notation "A *m B" (at level 40, left associativity, format "A  *m  B").
Reserved Notation "\det A"  (at level 10, A at level 8, format "\det  A").
Reserved Notation "\adj A"  (at level 10, A at level 8, format "\adj  A").

Section MatrixDef.

Variable R : Type.
Variables m n : nat.

Variant matrix : predArgType := Matrix of {ffun 'I_m * 'I_n -> R}.

Definition mx_val A := let: Matrix g := A in g.

Canonical matrix_subType := Eval hnf in [newType for mx_val].

Fact matrix_key : unit.
admit.
Defined.
Definition matrix_of_fun_def F := Matrix [ffun ij => F ij.1 ij.2].
Definition matrix_of_fun k := locked_with k matrix_of_fun_def.

Definition fun_of_matrix A (i : 'I_m) (j : 'I_n) := mx_val A (i, j).

Coercion fun_of_matrix : matrix >-> Funclass.

End MatrixDef.

Notation "''M[' R ]_ ( m , n )" := (matrix R m n) (only parsing): type_scope.
Notation "''rV[' R ]_ n" := 'M[R]_(1, n) (only parsing) : type_scope.
Notation "''M[' R ]_ n" := 'M[R]_(n, n) (only parsing) : type_scope.
Notation "''M_' ( m , n )" := 'M[_]_(m, n) : type_scope.
Notation "''rV_' n" := 'M_(1, n) : type_scope.
Notation "''M_' n" := 'M_(n, n) : type_scope.

Notation "\matrix[ k ]_ ( i , j ) E" := (matrix_of_fun k (fun i j => E)) :
   ring_scope.

Notation "\matrix_ ( i < m , j < n ) E" :=
  (@matrix_of_fun _ m n matrix_key (fun i j => E)) (only parsing) : ring_scope.

Notation "\matrix_ ( i , j ) E" := (\matrix_(i < _, j < _) E) : ring_scope.

Notation "\matrix_ ( i < m ) E" :=
  (\matrix_(i < m, j < _) @fun_of_matrix _ 1 _ E 0 j)
  (only parsing) : ring_scope.

Notation "\row_ ( j < n ) E" := (@matrix_of_fun _ 1 n matrix_key (fun _ j => E))
  (only parsing) : ring_scope.
Notation "\row_ j E" := (\row_(j < _) E) : ring_scope.

Definition matrix_eqMixin (R : eqType) m n :=
  Eval hnf in [eqMixin of 'M[R]_(m, n) by <:].
Canonical matrix_eqType (R : eqType) m n:=
  Eval hnf in EqType 'M[R]_(m, n) (matrix_eqMixin R m n).
Definition matrix_choiceMixin (R : choiceType) m n :=
  [choiceMixin of 'M[R]_(m, n) by <:].
Canonical matrix_choiceType (R : choiceType) m n :=
  Eval hnf in ChoiceType 'M[R]_(m, n) (matrix_choiceMixin R m n).

Section MatrixStructural.

Variable R : Type.

Fact const_mx_key : unit.
Admitted.
Definition const_mx m n a : 'M[R]_(m, n) := \matrix[const_mx_key]_(i, j) a.

Section FixedDim.

Variables m n : nat.
Implicit Type A : 'M[R]_(m, n).

Definition castmx m' n' (eq_mn : (m = m') * (n = n')) A : 'M_(m', n') :=
  let: erefl in _ = m' := eq_mn.1 return 'M_(m', n') in
  let: erefl in _ = n' := eq_mn.2 return 'M_(m, n') in A.

Fact row_perm_key : unit.
Admitted.
Definition row_perm (s : 'S_m) A := \matrix[row_perm_key]_(i, j) A (s i) j.
Fact col_perm_key : unit.
Admitted.
Definition col_perm (s : 'S_n) A := \matrix[col_perm_key]_(i, j) A i (s j).

Definition xrow i1 i2 := row_perm (tperm i1 i2).
Definition xcol j1 j2 := col_perm (tperm j1 j2).

Definition row' i0 A := \matrix_(i, j) A (lift i0 i) j.
Definition col' j0 A := \matrix_(i, j) A i (lift j0 j).

End FixedDim.

Section CutPaste.

Variables m m1 m2 n n1 n2 : nat.

Fact row_mx_key : unit.
admit.
Defined.
Definition row_mx (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)) : 'M[R]_(m, n1 + n2) :=
  \matrix[row_mx_key]_(i, j)
     match split j with inl j1 => A1 i j1 | inr j2 => A2 i j2 end.

Fact col_mx_key : unit.
admit.
Defined.
Definition col_mx (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)) : 'M[R]_(m1 + m2, n) :=
  \matrix[col_mx_key]_(i, j)
     match split i with inl i1 => A1 i1 j | inr i2 => A2 i2 j end.

Fact lsubmx_key : unit.
admit.
Defined.
Definition lsubmx (A : 'M[R]_(m, n1 + n2)) :=
  \matrix[lsubmx_key]_(i, j) A i (lshift n2 j).

Fact rsubmx_key : unit.
admit.
Defined.
Definition rsubmx (A : 'M[R]_(m, n1 + n2)) :=
  \matrix[rsubmx_key]_(i, j) A i (rshift n1 j).

Fact usubmx_key : unit.
admit.
Defined.
Definition usubmx (A : 'M[R]_(m1 + m2, n)) :=
  \matrix[usubmx_key]_(i, j) A (lshift m2 i) j.

Fact dsubmx_key : unit.
admit.
Defined.
Definition dsubmx (A : 'M[R]_(m1 + m2, n)) :=
  \matrix[dsubmx_key]_(i, j) A (rshift m1 i) j.

End CutPaste.

Section Block.

Variables m1 m2 n1 n2 : nat.

Definition block_mx Aul Aur Adl Adr : 'M_(m1 + m2, n1 + n2) :=
  col_mx (row_mx Aul Aur) (row_mx Adl Adr).

Section CutBlock.

Variable A : matrix R (m1 + m2) (n1 + n2).
Definition ursubmx := rsubmx (usubmx A).
Definition dlsubmx := lsubmx (dsubmx A).
Definition drsubmx := rsubmx (dsubmx A).

End CutBlock.

End Block.

Section VecMatrix.

Variables m n : nat.

Lemma mxvec_cast : #|{:'I_m * 'I_n}| = (m * n)%N.
Admitted.

Definition mxvec_index (i : 'I_m) (j : 'I_n) :=
  cast_ord mxvec_cast (enum_rank (i, j)).

Definition mxvec (A : 'M[R]_(m, n)) :=
  castmx (erefl _, mxvec_cast) (\row_k A (enum_val k).1 (enum_val k).2).

Fact vec_mx_key : unit.
Admitted.
Definition vec_mx (u : 'rV[R]_(m * n)) :=
  \matrix[vec_mx_key]_(i, j) u 0 (mxvec_index i j).

End VecMatrix.

End MatrixStructural.

Arguments const_mx {R m n}.

Section MapMatrix.

Variables (aT rT : Type) (f : aT -> rT).

Fact map_mx_key : unit.
Admitted.
Definition map_mx m n (A : 'M_(m, n)) := \matrix[map_mx_key]_(i, j) f (A i j).

End MapMatrix.

Section MatrixZmodule.

Variable V : zmodType.

Section FixedDim.

Variables m n : nat.
Implicit Types A B : 'M[V]_(m, n).

Fact oppmx_key : unit.
Admitted.
Fact addmx_key : unit.
Admitted.
Definition oppmx A := \matrix[oppmx_key]_(i, j) (- A i j).
Definition addmx A B := \matrix[addmx_key]_(i, j) (A i j + B i j).

Lemma addmxA : associative addmx.
Admitted.

Lemma addmxC : commutative addmx.
Admitted.

Lemma add0mx : left_id (const_mx 0) addmx.
Admitted.

Lemma addNmx : left_inverse (const_mx 0) oppmx addmx.
Admitted.

Definition matrix_zmodMixin := ZmodMixin addmxA addmxC add0mx addNmx.

Canonical matrix_zmodType := Eval hnf in ZmodType 'M[V]_(m, n) matrix_zmodMixin.

End FixedDim.

End MatrixZmodule.

Section MatrixAlgebra.

Variable R : ringType.

Section RingModule.

Variables m n : nat.
Implicit Types A B : 'M[R]_(m, n).

Fact scalemx_key : unit.
Admitted.
Definition scalemx x A := \matrix[scalemx_key]_(i, j) (x * A i j).

Local Notation "x *m: A" := (scalemx x A) (at level 40) : ring_scope.

Lemma scale1mx A : 1 *m: A = A.
Admitted.

Lemma scalemxDl A x y : (x + y) *m: A = x *m: A + y *m: A.
Admitted.

Lemma scalemxDr x A B : x *m: (A + B) = x *m: A + x *m: B.
Admitted.

Lemma scalemxA x y A : x *m: (y *m: A) = (x * y) *m: A.
Admitted.

Definition matrix_lmodMixin :=
  LmodMixin scalemxA scale1mx scalemxDr scalemxDl.

Canonical matrix_lmodType :=
  Eval hnf in LmodType R 'M[R]_(m, n) matrix_lmodMixin.

End RingModule.

Section ScalarMx.

Variable n : nat.

Fact scalar_mx_key : unit.
Admitted.
Definition scalar_mx x : 'M[R]_n :=
  \matrix[scalar_mx_key]_(i , j) (x *+ (i == j)).

End ScalarMx.

Notation "x %:M" := (scalar_mx _ x) : ring_scope.

Fact mulmx_key : unit.
Admitted.
Definition mulmx {m n p} (A : 'M_(m, n)) (B : 'M_(n, p)) : 'M[R]_(m, p) :=
  \matrix[mulmx_key]_(i, k) \sum_j (A i j * B j k).

Local Notation "A *m B" := (mulmx A B) : ring_scope.

Lemma mulmxA m n p q (A : 'M_(m, n)) (B : 'M_(n, p)) (C : 'M_(p, q)) :
  A *m (B *m C) = A *m B *m C.
Admitted.

Lemma mulmxDl m n p (A1 A2 : 'M_(m, n)) (B : 'M_(n, p)) :
  (A1 + A2) *m B = A1 *m B + A2 *m B.
Admitted.

Lemma mulmxDr m n p (A : 'M_(m, n)) (B1 B2 : 'M_(n, p)) :
  A *m (B1 + B2) = A *m B1 + A *m B2.
Admitted.

Lemma mul1mx m n (A : 'M_(m, n)) : 1%:M *m A = A.
Admitted.

Lemma mulmx1 m n (A : 'M_(m, n)) : A *m 1%:M = A.
Admitted.

Section Trace.

Variable n : nat.

Definition mxtrace (A : 'M[R]_n) := \sum_i A i i.

End Trace.

Section MatrixRing.

Variable n' : nat.
Local Notation n := n'.+1.

Lemma matrix_nonzero1 : 1%:M != 0 :> 'M_n.
Admitted.

Definition matrix_ringMixin :=
  RingMixin (@mulmxA n n n n) (@mul1mx n n) (@mulmx1 n n)
            (@mulmxDl n n n) (@mulmxDr n n n) matrix_nonzero1.

Canonical matrix_ringType := Eval hnf in RingType 'M[R]_n matrix_ringMixin.

End MatrixRing.

Definition determinant n (A : 'M_n) : R :=
  \sum_(s : 'S_n) (-1) ^+ s * \prod_i A i (s i).

Definition cofactor n A (i j : 'I_n) : R :=
  (-1) ^+ (i + j) * determinant (row' i (col' j A)).

Fact adjugate_key : unit.
Admitted.
Definition adjugate n (A : 'M_n) := \matrix[adjugate_key]_(i, j) cofactor A j i.

End MatrixAlgebra.
Arguments scalar_mx {R n}.
Prenex Implicits mulmx mxtrace determinant cofactor adjugate.

Notation "a %:M" := (scalar_mx a) : ring_scope.
Notation "A *m B" := (mulmx A B) : ring_scope.
Notation "'\det' A" := (determinant A) : ring_scope.
Notation "'\adj' A" := (adjugate A) : ring_scope.

Section CommMx.

Context {R : ringType} {n : nat}.
Implicit Types (f g p : 'M[R]_n) (fs : seq 'M[R]_n) (d : 'rV[R]_n) (I : Type).
Definition comm_mx  f g : Prop.
exact (f *m g =  g *m f).
Defined.

End CommMx.

Section ComMatrix.

Variable R : comRingType.

Lemma comm_mx_scalar n a (A : 'M[R]_n) : comm_mx A a%:M.
Admitted.

End ComMatrix.
Arguments comm_mx_scalar {R n}.

Section MatrixInv.

Variables R : comUnitRingType.

Section Defs.

Variable n : nat.
Definition unitmx : pred 'M[R]_n.
Admitted.
Definition invmx A := if A \in unitmx then (\det A)^-1 *: \adj A else A.

Lemma mulVmx : {in unitmx, left_inverse 1%:M invmx mulmx}.
Admitted.

Lemma mulmxV : {in unitmx, right_inverse 1%:M invmx mulmx}.
Admitted.

Lemma intro_unitmx A B : B *m A = 1%:M /\ A *m B = 1%:M -> unitmx A.
Admitted.

Lemma invmx_out : {in [predC unitmx], invmx =1 id}.
Admitted.

End Defs.

Variable n' : nat.
Local Notation n := n'.+1.

Definition matrix_unitRingMixin :=
  UnitRingMixin (@mulVmx n) (@mulmxV n) (@intro_unitmx n) (@invmx_out n).
Canonical matrix_unitRing :=
  Eval hnf in UnitRingType 'M[R]_n matrix_unitRingMixin.

End MatrixInv.

Declare Scope matrix_set_scope.

Reserved Notation "\rank A" (at level 10, A at level 8, format "\rank  A").

Delimit Scope matrix_set_scope with MS.

Section RowSpaceTheory.

Variable F : fieldType.

Local Notation "''M_' ( m , n )" := 'M[F]_(m, n) : type_scope.
Local Notation "''M_' n" := 'M[F]_(n, n) : type_scope.

Fixpoint Gaussian_elimination {m n} : 'M_(m, n) -> 'M_m * 'M_n * nat :=
  match m, n with
  | _.+1, _.+1 => fun A : 'M_(1 + _, 1 + _) =>
    if [pick ij | A ij.1 ij.2 != 0] is Some (i, j) then
      let a := A i j in let A1 := xrow i 0 (xcol j 0 A) in
      let u := ursubmx A1 in let v := a^-1 *: dlsubmx A1 in
      let: (L, U, r) := Gaussian_elimination (drsubmx A1 - v *m u) in
      (xrow i 0 (block_mx 1 0 v L), xcol j 0 (block_mx a%:M u 0 U), r.+1)
    else (1%:M, 1%:M, 0%N)
  | _, _ => fun _ => (1%:M, 1%:M, 0%N)
  end.

Section Defs.

Variables (m n : nat) (A : 'M_(m, n)).

Fact Gaussian_elimination_key : unit.
Admitted.

Let LUr := locked_with Gaussian_elimination_key (@Gaussian_elimination) m n A.
Definition mxrank := if [|| m == 0 | n == 0]%N then 0%N else LUr.2.
Definition cokermx : 'M_n.
Admitted.
Definition pinvmx : 'M_(n, m).
Admitted.

End Defs.
Local Notation "\rank A" := (mxrank A) : nat_scope.

Definition submx_def := idfun (fun m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)) =>
  A *m cokermx B == 0).
Fact submx_key : unit.
Admitted.
Definition submx := locked_with submx_key submx_def.

Lemma mxrank_eq0 m n (A : 'M_(m, n)) : (\rank A == 0%N) = (A == 0).
Admitted.

End RowSpaceTheory.
Notation "\rank A" := (mxrank A) : nat_scope.
Notation "A <= B" := (submx A B) : matrix_set_scope.
Reserved Notation "c %:P" (at level 2, format "c %:P").
Reserved Notation "''X^' n" (at level 3, n at level 2, format "''X^' n").
Reserved Notation "\poly_ ( i < n ) E"
  (at level 36, E at level 36, i, n at level 50,
   format "\poly_ ( i  <  n )  E").

Section Polynomial.

Variable R : ringType.

Record polynomial := Polynomial {polyseq :> seq R; _ : last 1 polyseq != 0}.

Canonical polynomial_subType := Eval hnf in [subType for polyseq].
Definition polynomial_eqMixin := Eval hnf in [eqMixin of polynomial by <:].
Canonical polynomial_eqType := Eval hnf in EqType polynomial polynomial_eqMixin.
Definition polynomial_choiceMixin := [choiceMixin of polynomial by <:].
Canonical polynomial_choiceType :=
  Eval hnf in ChoiceType polynomial polynomial_choiceMixin.

Definition poly_of of phant R := polynomial.

End Polynomial.
Notation "{ 'poly' T }" := (poly_of (Phant T)).

Section PolynomialTheory.

Variable R : ringType.
Implicit Types (a b c x y z : R) (p q r d : {poly R}).

Definition lead_coef p := p`_(size p).-1.
Definition polyC c : {poly R}.
Admitted.

Local Notation "c %:P" := (polyC c).
Definition cons_poly c p : {poly R}.
Admitted.

Definition Poly := foldr cons_poly 0%:P.

Definition poly_expanded_def n E := Poly (mkseq E n).
Fact poly_key : unit.
Admitted.
Definition poly := locked_with poly_key poly_expanded_def.
Local Notation "\poly_ ( i < n ) E" := (poly n (fun i : nat => E)).

Definition add_poly_def p q := \poly_(i < maxn (size p) (size q)) (p`_i + q`_i).
Fact add_poly_key : unit.
Admitted.
Definition add_poly := locked_with add_poly_key add_poly_def.

Definition opp_poly_def p := \poly_(i < size p) - p`_i.
Fact opp_poly_key : unit.
Admitted.
Definition opp_poly := locked_with opp_poly_key opp_poly_def.

Fact add_polyA : associative add_poly.
Admitted.

Fact add_polyC : commutative add_poly.
Admitted.

Fact add_poly0 : left_id 0%:P add_poly.
Admitted.

Fact add_polyN : left_inverse 0%:P opp_poly add_poly.
Admitted.

Definition poly_zmodMixin :=
  ZmodMixin add_polyA add_polyC add_poly0 add_polyN.

Canonical poly_zmodType := Eval hnf in ZmodType {poly R} poly_zmodMixin.

Definition mul_poly_def p q :=
  \poly_(i < (size p + size q).-1) (\sum_(j < i.+1) p`_j * q`_(i - j)).
Fact mul_poly_key : unit.
Admitted.
Definition mul_poly := locked_with mul_poly_key mul_poly_def.

Fact mul_polyA : associative mul_poly.
Admitted.

Fact mul_1poly : left_id 1%:P mul_poly.
Admitted.

Fact mul_poly1 : right_id 1%:P mul_poly.
Admitted.

Fact mul_polyDl : left_distributive mul_poly +%R.
Admitted.

Fact mul_polyDr : right_distributive mul_poly +%R.
Admitted.

Fact poly1_neq0 : 1%:P != 0 :> {poly R}.
Admitted.

Definition poly_ringMixin :=
  RingMixin mul_polyA mul_1poly mul_poly1 mul_polyDl mul_polyDr poly1_neq0.

Canonical poly_ringType := Eval hnf in RingType {poly R} poly_ringMixin.

Definition scale_poly_def a (p : {poly R}) := \poly_(i < size p) (a * p`_i).
Fact scale_poly_key : unit.
Admitted.
Definition scale_poly := locked_with scale_poly_key scale_poly_def.

Fact scale_polyA a b p : scale_poly a (scale_poly b p) = scale_poly (a * b) p.
Admitted.

Fact scale_1poly : left_id 1 scale_poly.
Admitted.

Fact scale_polyDr a : {morph scale_poly a : p q / p + q}.
Admitted.

Fact scale_polyDl p : {morph scale_poly^~ p : a b / a + b}.
Admitted.

Definition poly_lmodMixin :=
  LmodMixin scale_polyA scale_1poly scale_polyDr scale_polyDl.

Canonical poly_lmodType :=
  Eval hnf in LmodType R {poly R} poly_lmodMixin.
Definition polyX : {poly R}.
Admitted.
Fixpoint horner_rec s x := if s is a :: s' then horner_rec s' x * x + a else 0.
Definition horner p := horner_rec p.

End PolynomialTheory.
Notation "\poly_ ( i < n ) E" := (poly n (fun i => E)) : ring_scope.
Notation "'X" := (polyX _) : ring_scope.
Notation "''X^' n" := ('X ^+ n) : ring_scope.
Notation "p .[ x ]" := (horner p x) : ring_scope.

Section Definitions.

Variables (aR rR : ringType) (f : aR -> rR).

Definition map_poly (p : {poly aR}) := \poly_(i < size p) f p`_i.

Definition commr_rmorph u := forall x, GRing.comm u (f x).

Definition horner_morph u of commr_rmorph u := fun p => (map_poly p).[u].

End Definitions.

Section RingPseudoDivision.

Variable R : ringType.
Definition redivp : {poly R} -> {poly R} -> nat * {poly R} * {poly R}.
Admitted.

End RingPseudoDivision.

Section IDomainPseudoDivisionDefs.

Variable R : idomainType.
Implicit Type p q r d : {poly R}.

Definition edivp_expanded_def p q :=
  let: (k, d, r) as edvpq := redivp p q in
  if lead_coef q \in GRing.unit then
    (0%N, (lead_coef q)^-k *: d, (lead_coef q)^-k *: r)
  else edvpq.
Fact edivp_key : unit.
Admitted.
Definition edivp := locked_with edivp_key edivp_expanded_def.
Definition modp p q := (edivp p q).2.

End IDomainPseudoDivisionDefs.
Notation "m %% d" := (modp m d) : ring_scope.
Import mathcomp.ssreflect.tuple.
Import mathcomp.ssreflect.bigop.

Section RowPoly.

Variables (R : ringType) (d : nat).
Implicit Types u v : 'rV[R]_d.
Implicit Types p q : {poly R}.

Definition rVpoly v := \poly_(k < d) (if insub k is Some i then v 0 i else 0).
Definition poly_rV p := \row_(i < d) p`_i.

End RowPoly.
Arguments poly_rV {R d}.

Section HornerMx.

Variables (R : comRingType) (n' : nat).
Local Notation n := n'.+1.

Section OneMatrix.

Variable A : 'M[R]_n.

Definition horner_mx := horner_morph (comm_mx_scalar^~ A).

Definition powers_mx d := \matrix_(i < d) mxvec (A ^+ i).

End OneMatrix.

End HornerMx.

Section MinPoly.

Variables (F : fieldType) (n' : nat).
Local Notation n := n'.+1.
Variable A : 'M[F]_n.

Fact degree_mxminpoly_proof : exists d, \rank (powers_mx A d.+1) <= d.
Admitted.
Definition degree_mxminpoly := ex_minn degree_mxminpoly_proof.
Local Notation d := degree_mxminpoly.
Local Notation Ad := (powers_mx A d).

Definition mx_inv_horner B := rVpoly (mxvec B *m pinvmx Ad).

Definition mxminpoly := 'X^d - mx_inv_horner (A ^+ d).

End MinPoly.

Section MatrixFormula.

Variable F : fieldType.
Local Notation Add := GRing.Add (only parsing).
Local Notation Bool b := (GRing.Bool b%bool).
Local Notation term := (GRing.term F).
Local Notation form := (GRing.formula F).
Local Notation eval := GRing.eval.
Local Notation holds := GRing.holds.
Local Notation qf_form := GRing.qf_form.
Local Notation qf_eval := GRing.qf_eval.

Definition eval_mx (e : seq F) := @map_mx term F (eval e).

Definition mx_term := @map_mx F term GRing.Const.

Definition mulmx_term m n p (A : 'M[term]_(m, n)) (B : 'M_(n, p)) :=
  \matrix_(i, k) (\big[Add/0]_j (A i j * B j k))%T.

Let Schur m n (A : 'M[term]_(1 + m, 1 + n)) (a := A 0 0) :=
  \matrix_(i, j) (drsubmx A i j - a^-1 * dlsubmx A i 0%R * ursubmx A 0%R j)%T.

Fixpoint mxrank_form (r m n : nat) : 'M_(m, n) -> form :=
  match m, n return 'M_(m, n) -> form with
  | m'.+1, n'.+1 => fun A : 'M_(1 + m', 1 + n') =>
    let nzA k := A k.1 k.2 != 0 in
    let xSchur k := Schur (xrow k.1 0%R (xcol k.2 0%R A)) in
    let recf k := Bool (r > 0) /\ mxrank_form r.-1 (xSchur k) in
    GRing.Pick nzA recf (Bool (r == 0%N))
  | _, _ => fun _ => Bool (r == 0%N)
  end%T.

Lemma mxrank_form_qf r m n (A : 'M_(m, n)) : qf_form (mxrank_form r A).
Admitted.

Lemma eval_mxrank e r m n (A : 'M_(m, n)) :
  qf_eval e (mxrank_form r A) = (\rank (eval_mx e A) == r).
Admitted.

Section Env.

Variable d : nat.

Definition seq_of_rV (v : 'rV_d) : seq F := fgraph [ffun i => v 0 i].

Definition row_var k : 'rV[term]_d := \row_i ('X_(k * d + i))%T.

Definition row_env (e : seq 'rV_d) := flatten (map seq_of_rV e).

Definition Exists_row_form k (f : form) :=
  foldr GRing.Exists f (codom (fun i : 'I_d => k * d + i)%N).

Lemma Exists_rowP e k f :
  d > 0 ->
   ((exists v : 'rV[F]_d, holds (row_env (set_nth 0 e k v)) f)
      <-> holds (row_env e) (Exists_row_form k f)).
Admitted.

End Env.

End MatrixFormula.
Unset Printing Implicit Defensive.
Import GRing.Theory.

Section RingRepr.

Variable R : comUnitRingType.

Section OneRepresentation.

Variable gT : finGroupType.

Definition mx_repr (G : {set gT}) n (r : gT -> 'M[R]_n) :=
  r 1%g = 1%:M /\ {in G &, {morph r : x y / (x * y)%g >-> x *m y}}.

Structure mx_representation G n :=
  MxRepresentation { repr_mx :> gT -> 'M_n; _ : mx_repr G repr_mx }.

Variables (G : {group gT}) (n : nat) (rG : mx_representation G n).

Section CentHom.

Variable f : 'M[R]_n.

Definition rcent := [set x in G | f *m rG x == rG x *m f].

Definition centgmx := G \subset rcent.

End CentHom.

End OneRepresentation.

End RingRepr.

Section FieldRepr.

Variable F : fieldType.

Section OneRepresentation.

Variable gT : finGroupType.

Variables (G : {group gT}) (n : nat) (rG : mx_representation F G n).

Section Stabilisers.

Variables (m : nat) (U : 'M[F]_(m, n)).

Definition rstabs := [set x in G | U *m rG x <= U]%MS.

Definition mxmodule := G \subset rstabs.

End Stabilisers.

Definition mxsimple (V : 'M_n) :=
  [/\ mxmodule V, V != 0 &
      forall U : 'M_n, mxmodule U -> (U <= V)%MS -> U != 0 -> (V <= U)%MS].

Definition mx_irreducible := mxsimple 1%:M.

End OneRepresentation.

End FieldRepr.

Record gen_of {F : fieldType} {gT : finGroupType} {G : {group gT}} {n' : nat}
              {rG : mx_representation F G n'.+1} {A : 'M[F]_n'.+1}
              (irrG : mx_irreducible rG) (cGA : centgmx rG A) :=
   Gen {rVval : 'rV[F]_(degree_mxminpoly A)}.

Local Arguments rVval {F gT G%G n'%N rG A%R irrG cGA} x%R : rename.

Section GenField.

Variables (F : fieldType) (gT : finGroupType) (G : {group gT}) (n' : nat).
Local Notation n := n'.+1.
Variables (rG : mx_representation F G n) (A : 'M[F]_n).

Local Notation d := (degree_mxminpoly A).
Local Notation pA := (mxminpoly A).
Local Notation irr := mx_irreducible.

Hypotheses (irrG : irr rG) (cGA : centgmx rG A).

Notation FA := (gen_of irrG cGA).
Let inFA := Gen irrG cGA.

Canonical gen_subType := Eval hnf in [newType for rVval : FA -> 'rV_d].
Definition gen_eqMixin := Eval hnf in [eqMixin of FA by <:].
Canonical gen_eqType := Eval hnf in EqType FA gen_eqMixin.
Definition gen_choiceMixin := [choiceMixin of FA by <:].
Canonical gen_choiceType := Eval hnf in ChoiceType FA gen_choiceMixin.

Definition gen0 := inFA 0.
Definition genN (x : FA) := inFA (- val x).
Definition genD (x y : FA) := inFA (val x + val y).

Lemma gen_addA : associative genD.
Admitted.

Lemma gen_addC : commutative genD.
Admitted.

Lemma gen_add0r : left_id gen0 genD.
Admitted.

Lemma gen_addNr : left_inverse gen0 genN genD.
Admitted.

Definition gen_zmodMixin := ZmodMixin gen_addA gen_addC gen_add0r gen_addNr.
Canonical gen_zmodType := Eval hnf in ZmodType FA gen_zmodMixin.

Definition pval (x : FA) := rVpoly (val x).

Definition mxval (x : FA) := horner_mx A (pval x).

Definition gen1 := inFA (poly_rV 1).
Definition genM x y := inFA (poly_rV (pval x * pval y %% pA)).
Definition genV x := inFA (poly_rV (mx_inv_horner A (mxval x)^-1)).

Lemma gen_mulA : associative genM.
Admitted.

Lemma gen_mulC : commutative genM.
Admitted.

Lemma gen_mul1r : left_id gen1 genM.
Admitted.

Lemma gen_mulDr : left_distributive genM +%R.
Admitted.

Lemma gen_ntriv : gen1 != 0.
Admitted.

Definition gen_ringMixin :=
  ComRingMixin gen_mulA gen_mulC gen_mul1r gen_mulDr gen_ntriv.
Canonical gen_ringType := Eval hnf in RingType FA gen_ringMixin.
Canonical gen_comRingType := Eval hnf in ComRingType FA gen_mulC.

Lemma gen_mulVr : GRing.Field.axiom genV.
Admitted.

Lemma gen_invr0 : genV 0 = 0.
Admitted.

Definition gen_unitRingMixin := FieldUnitMixin gen_mulVr gen_invr0.
Canonical gen_unitRingType :=
  Eval hnf in UnitRingType FA gen_unitRingMixin.

End GenField.

Variable F : decFieldType.
Local Notation Bool b := (GRing.Bool b%bool).

Variables (gT : finGroupType) (G : {group gT}) (n' : nat).
Local Notation n := n'.+1.
Variables (rG : mx_representation F G n) (A : 'M[F]_n).
Hypotheses (irrG : mx_irreducible rG) (cGA : centgmx rG A).
Local Notation FA := (gen_of irrG cGA).
Local Notation inFA := (Gen irrG cGA).

Local Notation d := (degree_mxminpoly A).
Local Notation Ad := (powers_mx A d).

Let mxT (u : 'rV_d) := vec_mx (mulmx_term u (mx_term Ad)).

Let Ad'T := mx_term (pinvmx Ad).
Let mulT (u v : 'rV_d) := mulmx_term (mxvec (mulmx_term (mxT u) (mxT v))) Ad'T.

Fixpoint gen_term t := match t with
| 'X_k => row_var _ d k
| x%:T => mx_term (val (x : FA))
| n1%:R => mx_term (val (n1%:R : FA))%R
| t1 + t2 => \row_i (gen_term t1 0%R i + gen_term t2 0%R i)
| - t1 => \row_i (- gen_term t1 0%R i)
| t1 *+ n1 => mulmx_term (mx_term n1%:R%:M)%R (gen_term t1)
| t1 * t2 => mulT (gen_term t1) (gen_term t2)
| t1^-1 => gen_term t1
| t1 ^+ n1 => iter n1 (mulT (gen_term t1)) (mx_term (val (1%R : FA)))
end%T.

Definition gen_env (e : seq FA) := row_env (map val e).

Lemma set_nth_map_rVval (e : seq FA) j v :
  set_nth 0 (map val e) j v = map val (set_nth 0 e j (inFA v)).
Admitted.

Lemma eval_gen_term e t :
  GRing.rterm t -> eval_mx (gen_env e) (gen_term t) = val (GRing.eval e t).
Admitted.

Fixpoint gen_form f := match f with
| Bool b => Bool b
| t1 == t2 => mxrank_form 0 (gen_term (t1 - t2))
| GRing.Unit t1 => mxrank_form 1 (gen_term t1)
| f1 /\ f2 => gen_form f1 /\ gen_form f2
| f1 \/ f2 =>  gen_form f1 \/ gen_form f2
| f1 ==> f2 => gen_form f1 ==> gen_form f2
| ~ f1 => ~ gen_form f1
| ('exists 'X_k, f1) => Exists_row_form d k (gen_form f1)
| ('forall 'X_k, f1) => ~ Exists_row_form d k (~ (gen_form f1))
end%T.

Lemma sat_gen_form e f : GRing.rformula f ->
  reflect (GRing.holds e f) (GRing.sat (gen_env e) (gen_form f)).
Proof.
have ExP := Exists_rowP; have set_val := set_nth_map_rVval.
elim: f e => //.
-
 by move=> b e _; apply: (iffP satP).
-
 rewrite /gen_form => t1 t2 e rt_t; set t := (_ - _)%T.
  have:= GRing.qf_evalP (gen_env e) (mxrank_form_qf 0 (gen_term t)).
  rewrite eval_mxrank mxrank_eq0 eval_gen_term // => tP.
  by rewrite (sameP satP tP) /= subr_eq0 val_eqE; apply: eqP.
-
 move=> f1 IH1 f2 IH2 s /= /andP[/(IH1 s)f1P /(IH2 s)f2P].
  by apply: (iffP satP) => [[/satP/f1P ? /satP/f2P] | [/f1P/satP ? /f2P/satP]].
