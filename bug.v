
(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "-parsing" "-w" "+undeclared-scope" "-w" "+non-primitive-record" "-w" "-ambiguous-paths" "-w" "-redundant-canonical-projection" "-w" "-projection-no-head-constant" "-w" "-deprecated-native-compiler-option" "-native-compiler" "ondemand" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/analysis/classical" "mathcomp.classical" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/analysis/theories" "mathcomp.analysis" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/HB" "HB" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/elpi" "elpi" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/mathcomp" "mathcomp" "-top" "Top.bug_01") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 2660 lines to 31 lines, then from 44 lines to 5349 lines, then from 5353 lines to 4369 lines, then from 4097 lines to 42 lines, then from 55 lines to 1523 lines, then from 1528 lines to 77 lines, then from 90 lines to 7964 lines, then from 7968 lines to 8383 lines, then from 7877 lines to 4876 lines, then from 4884 lines to 194 lines, then from 207 lines to 3426 lines, then from 3431 lines to 883 lines *)
(* coqc version 8.18+alpha compiled with OCaml 4.14.1
   coqtop version runner-qqwxwxez-project-6138686-concurrent-0:/builds/coq/coq/_build/default,(HEAD detached at 5cd942bb3e) (5cd942bb3ef9235adb74ad46145e5af66ec2e040)
   Expected coqc runtime on this file: 1.375 sec *)
Require Coq.Init.Ltac.
Require Coq.NArith.BinNat.
Require Coq.NArith.Ndec.
Require Coq.PArith.BinPos.
Require Coq.setoid_ring.Field_tac.
Require Coq.setoid_ring.Field_theory.
Require Coq.setoid_ring.Ring.
Require Coq.ssr.ssrbool.
Require Coq.ssr.ssreflect.
Require Coq.ssr.ssrfun.
Require mathcomp.ssreflect.ssreflect.
Require mathcomp.ssreflect.ssrnotations.
Require mathcomp.ssreflect.ssrfun.
Require mathcomp.ssreflect.ssrbool.
Require mathcomp.ssreflect.eqtype.
Require mathcomp.ssreflect.ssrnat.
Require mathcomp.ssreflect.seq.
Require mathcomp.ssreflect.choice.
Require mathcomp.ssreflect.path.
Require mathcomp.ssreflect.fintype.
Require mathcomp.ssreflect.div.
Require mathcomp.ssreflect.tuple.
Require mathcomp.ssreflect.finfun.
Require mathcomp.ssreflect.bigop.
Require mathcomp.ssreflect.prime.
Require mathcomp.ssreflect.finset.
Require mathcomp.ssreflect.binomial.
Require mathcomp.algebra.ssralg.
Require mathcomp.ssreflect.generic_quotient.
Require mathcomp.algebra.ring_quotient.
Require mathcomp.algebra.countalg.
Require mathcomp.fingroup.fingroup.
Require mathcomp.fingroup.morphism.
Require mathcomp.fingroup.perm.
Require mathcomp.fingroup.automorphism.
Require mathcomp.fingroup.quotient.
Require mathcomp.fingroup.action.
Require mathcomp.algebra.finalg.
Require mathcomp.ssreflect.order.
Require mathcomp.ssreflect.ssrAC.
Require mathcomp.algebra.poly.
Require mathcomp.algebra.ssrnum.
Require mathcomp.algebra.interval.
Require mathcomp.algebra.zmodp.
Require mathcomp.algebra.matrix.
Require mathcomp.algebra.ssrint.
Require mathcomp.algebra.rat.
Require mathcomp.ssreflect.fingraph.
Require mathcomp.ssreflect.all_ssreflect.
Require mathcomp.algebra.polydiv.
Require mathcomp.algebra.mxalgebra.
Require mathcomp.algebra.mxpoly.
Require mathcomp.algebra.polyXY.
Require mathcomp.algebra.vector.
Require mathcomp.algebra.intdiv.
Require mathcomp.algebra.fraction.
Require mathcomp.algebra.all_algebra.
Require mathcomp.finmap.finmap.
Require mathcomp.classical.mathcomp_extra.
Require mathcomp.analysis.signed.
Require mathcomp.analysis.constructive_ereal.
Require mathcomp.classical.boolp.

Module Export AdmitTactic.
Module Import LocalFalse.
Inductive False : Prop := .
End LocalFalse.
Axiom proof_admitted : False.
Import Coq.Init.Ltac.
Tactic Notation "admit" := abstract case proof_admitted.
End AdmitTactic.

Module Export mathcomp_DOT_classical_DOT_classical_sets_WRAPPED.
Module Export classical_sets.
Import mathcomp.ssreflect.all_ssreflect.
Import mathcomp.algebra.ssralg.
Import mathcomp.algebra.matrix.
Import mathcomp.finmap.finmap.
Import mathcomp.ssreflect.order.
Import mathcomp.algebra.ssrnum.
Import mathcomp.algebra.ssrint.
Import mathcomp.algebra.interval.
Import mathcomp.classical.mathcomp_extra.
Import mathcomp.classical.boolp.

 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope classical_set_scope.

Reserved Notation "[ 'set' x : T | P ]"
  (at level 0, x at level 99, only parsing).
Reserved Notation "[ 'set' x | P ]"
  (at level 0, x, P at level 99, format "[ 'set'  x  |  P ]").
Reserved Notation "[ 'set' E | x 'in' A ]" (at level 0, E, x at level 99,
  format "[ '[hv' 'set'  E '/ '  |  x  'in'  A ] ']'").
Reserved Notation "[ 'set' E | x 'in' A & y 'in' B ]"
  (at level 0, E, x at level 99,
  format "[ '[hv' 'set'  E '/ '  |  x  'in'  A  &  y  'in'  B ] ']'").
Reserved Notation "[ 'set' a ]"
  (at level 0, a at level 99, format "[ 'set'  a ]").
Reserved Notation "[ 'set' : T ]" (at level 0, format "[ 'set' :  T ]").
Reserved Notation "[ 'set' a : T ]"
  (at level 0, a at level 99, format "[ 'set'  a   :  T ]").
Reserved Notation "A `|` B" (at level 52, left associativity).
Reserved Notation "a |` A" (at level 52, left associativity).
Reserved Notation "[ 'set' a1 ; a2 ; .. ; an ]"
  (at level 0, a1 at level 99, format "[ 'set'  a1 ;  a2 ;  .. ;  an ]").
Reserved Notation "A `&` B"  (at level 48, left associativity).
Reserved Notation "A `*` B"  (at level 46, left associativity).
Reserved Notation "A `*`` B"  (at level 46, left associativity).
Reserved Notation "A ``*` B"  (at level 46, left associativity).
Reserved Notation "A .`1" (at level 2, left associativity, format "A .`1").
Reserved Notation "A .`2" (at level 2, left associativity, format "A .`2").
Reserved Notation "~` A" (at level 35, right associativity).
Reserved Notation "[ 'set' ~ a ]" (at level 0, format "[ 'set' ~  a ]").
Reserved Notation "A `\` B" (at level 50, left associativity).
Reserved Notation "A `\ b" (at level 50, left associativity).
 
Reserved Notation "\bigcup_ ( i 'in' P ) F"
  (at level 41, F at level 41, i, P at level 50,
           format "'[' \bigcup_ ( i  'in'  P ) '/  '  F ']'").
Reserved Notation "\bigcup_ ( i : T ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \bigcup_ ( i  :  T ) '/  '  F ']'").
Reserved Notation "\bigcup_ ( i < n ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \bigcup_ ( i  <  n ) '/  '  F ']'").
Reserved Notation "\bigcup_ i F"
  (at level 41, F at level 41, i at level 0,
           format "'[' \bigcup_ i '/  '  F ']'").
Reserved Notation "\bigcap_ ( i 'in' P ) F"
  (at level 41, F at level 41, i, P at level 50,
           format "'[' \bigcap_ ( i  'in'  P ) '/  '  F ']'").
Reserved Notation "\bigcap_ ( i : T ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \bigcap_ ( i  :  T ) '/  '  F ']'").
Reserved Notation "\bigcap_ ( i < n ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \bigcap_ ( i  <  n ) '/  '  F ']'").
Reserved Notation "\bigcap_ i F"
  (at level 41, F at level 41, i at level 0,
           format "'[' \bigcap_ i '/  '  F ']'").
Reserved Notation "A `<` B" (at level 70, no associativity).
Reserved Notation "A `<=` B" (at level 70, no associativity).
Reserved Notation "A `<=>` B" (at level 70, no associativity).
Reserved Notation "f @^-1` A" (at level 24).
Reserved Notation "f @` A" (at level 24).
Reserved Notation "A !=set0" (at level 80).
Reserved Notation "[ 'set`' p ]" (at level 0, format "[ 'set`'  p ]").
Reserved Notation "[ 'disjoint' A & B ]" (at level 0,
  format "'[hv' [ 'disjoint' '/  '  A '/'  &  B ] ']'").
Reserved Notation "F `#` G"
 (at level 48, left associativity, format "F  `#`  G").
Reserved Notation "'`I_' n" (at level 8, n at level 2, format "'`I_' n").

Definition set T := T -> Prop.
Definition in_set T (A : set T) : pred T. exact ((fun x => `[<A x>])). Defined.
Canonical set_predType T := @PredType T (set T) (@in_set T).

Lemma in_setE T (A : set T) x : x \in A = A x :> Prop.
Admitted.

Definition inE := (inE, in_setE).

Bind Scope classical_set_scope with set.
Local Open Scope classical_set_scope.
Delimit Scope classical_set_scope with classic.
Definition mkset {T} (P : T -> Prop) : set T. exact (P). Defined.
Arguments mkset _ _ _ /.

Notation "[ 'set' x : T | P ]" := (mkset (fun x : T => P)) : classical_set_scope.
Notation "[ 'set' x | P ]" := [set x : _ | P] : classical_set_scope.

Definition image {T rT} (A : set T) (f : T -> rT) :=
  [set y | exists2 x, A x & f x = y].
Arguments image _ _ _ _ _ /.
Notation "[ 'set' E | x 'in' A ]" :=
  (image A (fun x => E)) : classical_set_scope.

Definition image2 {TA TB rT} (A : set TA) (B : set TB) (f : TA -> TB -> rT) :=
  [set z | exists2 x, A x & exists2 y, B y & f x y = z].
Arguments image2 _ _ _ _ _ _ _ /.
Notation "[ 'set' E | x 'in' A & y 'in' B ]" :=
  (image2 A B (fun x y => E)) : classical_set_scope.

Section basic_definitions.
Context {T rT : Type}.
Implicit Types (T : Type) (A B : set T) (f : T -> rT) (Y : set rT).
Definition preimage f Y : set T. exact ([set t | Y (f t)]). Defined.

Definition setT := [set _ : T | True].
Definition set0 := [set _ : T | False].
Definition set1 (t : T) := [set x : T | x = t].
Definition setI A B := [set x | A x /\ B x].
Definition setU A B := [set x | A x \/ B x].
Definition nonempty A := exists a, A a.
Definition setC A := [set a | ~ A a].
Definition setD A B := [set x | A x /\ ~ B x].
Definition setM T1 T2 (A1 : set T1) (A2 : set T2) := [set z | A1 z.1 /\ A2 z.2].
Definition fst_set T1 T2 (A : set (T1 * T2)) := [set x | exists y, A (x, y)].
Definition snd_set T1 T2 (A : set (T1 * T2)) := [set y | exists x, A (x, y)].
Definition setMR T1 T2 (A1 : set T1) (A2 : T1 -> set T2) :=
  [set z | A1 z.1 /\ A2 z.1 z.2].
Definition setML T1 T2 (A1 : T2 -> set T1) (A2 : set T2) :=
  [set z | A1 z.2 z.1 /\ A2 z.2].

Lemma mksetE (P : T -> Prop) x : [set x | P x] x = P x.
Admitted.

Definition bigcap T I (P : set I) (F : I -> set T) :=
  [set a | forall i, P i -> F i a].
Definition bigcup T I (P : set I) (F : I -> set T) :=
  [set a | exists2 i, P i & F i a].

Definition subset A B := forall t, A t -> B t.
Local Notation "A `<=` B" := (subset A B).

Definition disj_set A B := setI A B == set0.

Definition proper A B := A `<=` B /\ ~ (B `<=` A).

End basic_definitions.
Arguments preimage T rT f Y t /.
Arguments set0 _ _ /.
Arguments setT _ _ /.
Arguments set1 _ _ _ /.
Arguments setI _ _ _ _ /.
Arguments setU _ _ _ _ /.
Arguments setC _ _ _ /.
Arguments setD _ _ _ _ /.
Arguments setM _ _ _ _ _ /.
Arguments setMR _ _ _ _ _ /.
Arguments setML _ _ _ _ _ /.
Arguments fst_set _ _ _ _ /.
Arguments snd_set _ _ _ _ /.

Notation range F := [set F i | i in setT].
Notation "[ 'set' a ]" := (set1 a) : classical_set_scope.
Notation "[ 'set' a : T ]" := [set (a : T)] : classical_set_scope.
Notation "[ 'set' : T ]" := (@setT T) : classical_set_scope.
Notation "A `|` B" := (setU A B) : classical_set_scope.
Notation "a |` A" := ([set a] `|` A) : classical_set_scope.
Notation "[ 'set' a1 ; a2 ; .. ; an ]" :=
  (setU .. (a1 |` [set a2]) .. [set an]) : classical_set_scope.
Notation "A `&` B" := (setI A B) : classical_set_scope.
Notation "A `*` B" := (setM A B) : classical_set_scope.
Notation "A .`1" := (fst_set A) : classical_set_scope.
Notation "A .`2" := (snd_set A) : classical_set_scope.
Notation "A `*`` B" := (setMR A B) : classical_set_scope.
Notation "A ``*` B" := (setML A B) : classical_set_scope.
Notation "~` A" := (setC A) : classical_set_scope.
Notation "[ 'set' ~ a ]" := (~` [set a]) : classical_set_scope.
Notation "A `\` B" := (setD A B) : classical_set_scope.
Notation "A `\ a" := (A `\` [set a]) : classical_set_scope.
Notation "[ 'disjoint' A & B ]" := (disj_set A B) : classical_set_scope.

Notation "'`I_' n" := [set k | is_true (k < n)%N].

Notation "\bigcup_ ( i 'in' P ) F" :=
  (bigcup P (fun i => F)) : classical_set_scope.
Notation "\bigcup_ ( i : T ) F" :=
  (\bigcup_(i in @setT T) F) : classical_set_scope.
Notation "\bigcup_ ( i < n ) F" :=
  (\bigcup_(i in `I_n) F) : classical_set_scope.
Notation "\bigcup_ i F" := (\bigcup_(i : _) F) : classical_set_scope.
Notation "\bigcap_ ( i 'in' P ) F" :=
  (bigcap P (fun i => F)) : classical_set_scope.
Notation "\bigcap_ ( i : T ) F" :=
  (\bigcap_(i in @setT T) F) : classical_set_scope.
Notation "\bigcap_ ( i < n ) F" :=
  (\bigcap_(i in `I_n) F) : classical_set_scope.
Notation "\bigcap_ i F" := (\bigcap_(i : _) F) : classical_set_scope.

Notation "A `<=` B" := (subset A B) : classical_set_scope.
Notation "A `<` B" := (proper A B) : classical_set_scope.

Notation "A `<=>` B" := ((A `<=` B) /\ (B `<=` A)) : classical_set_scope.
Notation "f @^-1` A" := (preimage f A) : classical_set_scope.
Notation "f @` A" := (image A f) (only parsing) : classical_set_scope.
Notation "A !=set0" := (nonempty A) : classical_set_scope.

Notation "[ 'set`' p ]":= [set x | is_true (x \in p)] : classical_set_scope.
Notation pred_set := (fun i => [set` i]).

Notation "`[ a , b ]" :=
  [set` Interval (BLeft a) (BRight b)] : classical_set_scope.
Notation "`] a , b ]" :=
  [set` Interval (BRight a) (BRight b)] : classical_set_scope.
Notation "`[ a , b [" :=
  [set` Interval (BLeft a) (BLeft b)] : classical_set_scope.
Notation "`] a , b [" :=
  [set` Interval (BRight a) (BLeft b)] : classical_set_scope.
Notation "`] '-oo' , b ]" :=
  [set` Interval -oo%O (BRight b)] : classical_set_scope.
Notation "`] '-oo' , b [" :=
  [set` Interval -oo%O (BLeft b)] : classical_set_scope.
Notation "`[ a , '+oo' [" :=
  [set` Interval (BLeft a) +oo%O] : classical_set_scope.
Notation "`] a , '+oo' [" :=
  [set` Interval (BRight a) +oo%O] : classical_set_scope.
Notation "`] -oo , '+oo' [" :=
  [set` Interval -oo%O +oo%O] : classical_set_scope.

Lemma preimage_itv T (d : unit) (rT : porderType d) (f : T -> rT) (i : interval rT) (x : T) :
  ((f @^-1` [set` i]) x) = (f x \in i).
Admitted.

Lemma preimage_itv_o_infty T (d : unit) (rT : porderType d) (f : T -> rT) y :
  f @^-1` `]y, +oo[%classic = [set x | (y < f x)%O].
Admitted.

Lemma preimage_itv_c_infty T (d : unit) (rT : porderType d) (f : T -> rT) y :
  f @^-1` `[y, +oo[%classic = [set x | (y <= f x)%O].
Admitted.

Lemma preimage_itv_infty_o T (d : unit) (rT : orderType d) (f : T -> rT) y :
  f @^-1` `]-oo, y[%classic = [set x | (f x < y)%O].
Admitted.

Lemma preimage_itv_infty_c T (d : unit) (rT : orderType d) (f : T -> rT) y :
  f @^-1` `]-oo, y]%classic = [set x | (f x <= y)%O].
Admitted.

Lemma eq_set T (P Q : T -> Prop) : (forall x : T, P x = Q x) ->
  [set x | P x] = [set x | Q x].
Admitted.

Coercion set_type T (A : set T) := {x : T | x \in A}.
Definition SigSub {T} {pT : predType T} {P : pT} x : x \in P -> {x | x \in P}. exact (exist (fun x => x \in P) x). Defined.

Lemma set0fun {P T : Type} : @set0 T -> P.
Admitted.

Lemma pred_oappE {T : Type} (D : {pred T}) :
  pred_oapp D = mem (some @` D)%classic.
Admitted.

Lemma pred_oapp_set {T : Type} (D : set T) :
  pred_oapp (mem D) = mem (some @` D)%classic.
Admitted.

Section basic_lemmas.
Context {T : Type}.
Implicit Types A B C D : set T.

Lemma mem_set {A} {u : T} : A u -> u \in A.
Admitted.
Lemma set_mem {A} {u : T} : u \in A -> A u.
Admitted.
Lemma mem_setT (u : T)    : u \in [set: T].
Admitted.
Lemma mem_setK {A} {u : T} : cancel (@mem_set A u) set_mem.
Admitted.
Lemma set_memK {A} {u : T} : cancel (@set_mem A u) mem_set.
Admitted.

Lemma memNset (A : set T) (u : T) : ~ A u -> u \in A = false.
Admitted.

Lemma notin_set (A : set T) x : (x \notin A : Prop) = ~ (A x).
Admitted.

Lemma setTPn (A : set T) : A != setT <-> exists t, ~ A t.
Admitted.
#[deprecated(note="Use setTPn instead")]
Notation setTP := setTPn.

End basic_lemmas.

Section InitialSegment.

End InitialSegment.

Section SetFset.

End SetFset.

Section SetMonoids.

End SetMonoids.

Section base_image_lemmas.

End base_image_lemmas.

Section image_lemmas.

End image_lemmas.

Section bigop_lemmas.

End bigop_lemmas.

Section bigcup_set.

End bigcup_set.

Section smallest.

End smallest.

Section bigop_nat_lemmas.

End bigop_nat_lemmas.

Definition xget {T : choiceType} x0 (P : set T) : T :=
  if pselect (exists x : T, `[<P x>]) isn't left exP then x0
  else projT1 (sigW exP).

Module Pointed.

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
Canonical choiceType.
Notation pointedType := type.
Notation PointedType T m := (@pack T m _ _ idfun).

End Exports.

End Pointed.

Export Pointed.Exports.
Definition point {M : pointedType} : M. exact (Pointed.mixin (Pointed.class M)). Defined.

Canonical arrow_pointedType (T : Type) (T' : pointedType) :=
  PointedType (T -> T') (fun=> point).
Canonical Prop_pointedType := PointedType Prop False.

Notation get := (xget point).

Section PointedTheory.

End PointedTheory.

 

Module Empty.

Section EqMixin.
End EqMixin.

Section ChoiceMixin.
End ChoiceMixin.

Section CountMixin.
End CountMixin.

Section FinMixin.
End FinMixin.

Section ClassDef.

End ClassDef.

Module Import Exports.
End Exports.

End Empty.

Section partitions.

End partitions.

Section ZL.

End ZL.

Section UpperLowerTheory.

End UpperLowerTheory.

Section UpperLowerOrderTheory.

End UpperLowerOrderTheory.

Section meets.

End meets.

Module Export SetOrder.
Module Export Internal.
Section SetOrder.

End SetOrder.
End Internal.

Module Export Exports.

Section exports.

End exports.
End Exports.
End SetOrder.

Section product.

End product.

Section section.

End section.

End classical_sets.
Module Export mathcomp.
Module Export classical.
Module Export classical_sets.
Include mathcomp_DOT_classical_DOT_classical_sets_WRAPPED.classical_sets.
End classical_sets.
Import mathcomp.ssreflect.all_ssreflect.
Import mathcomp.classical.classical_sets.
Reserved Notation "F --> G" (at level 70, format "F  -->  G").
Reserved Notation "f @ F" (at level 60, format "f  @  F").

Set Implicit Arguments.
Local Open Scope classical_set_scope.

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
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of U xT).
Local Coercion base : class_of >-> Pointed.class_of.

Definition pack m :=
  fun bT b of phant_id (Pointed.class bT) b => @Pack T (Class b m).
Definition fpointedType := @Pointed.Pack cT xclass.

End ClassDef.

Structure source Z Y := Source {
  source_type :> Type;
  _ : (source_type -> Z) -> set (set Y)
}.
Definition source_filter Z Y (F : source Z Y) : (F -> Z) -> set (set Y).
exact (let: Source X f := F in f).
Defined.
Coercion sort : type >-> Sortclass.
Canonical fpointedType.
Notation filteredType := type.
Notation FilteredType U T m := (@pack U T m _ _ idfun).
Notation "[ 'filteredType' U 'of' T ]" := (@clone U T _ _ id)
  (at level 0, format "[ 'filteredType'  U  'of'  T ]") : form_scope.

Canonical default_arrow_filter Y (Z : pointedType) (X : source Z Y) :=
  FilteredType Y (X -> Z) (@source_filter _ _ X).
Canonical source_filter_filter Y :=
  @Source Prop _ (_ -> Prop) (fun x : (set (set Y)) => x).
Definition nbhs {U} {T : filteredType U} : T -> set (set U).
exact (Filtered.nbhs_op (Filtered.class T)).
Defined.
Definition filter_from {I T : Type} (D : set I) (B : I -> set T) : set (set T).
Admitted.

Definition filter_of X (fX : filteredType X) (x : fX) of phantom fX x :=
   nbhs x.
Notation "[ 'filter' 'of' x ]" :=
  (@filter_of _ _ _ (Phantom _ x)) : classical_set_scope.

Definition cvg_to {T : Type} (F G : set (set T)) := G `<=` F.

Notation "F --> G" := (cvg_to [filter of F] [filter of G]) : classical_set_scope.
Definition type_of_filter {T} (F : set (set T)) := T.

Definition lim_in {U : Type} (T : filteredType U) :=
  fun F : set (set U) => get (fun l : T => F --> l).
Notation "[ 'lim' F 'in' T ]" := (@lim_in _ T [filter of F]) : classical_set_scope.
Notation lim F := [lim F in [filteredType _ of @type_of_filter _ [filter of F]]].

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

Definition fmap {T U : Type} (f : T -> U) (F : set (set T)) :=
  [set P | F (f @^-1` P)].
Notation "f @ F" := (fmap f [filter of F]) : classical_set_scope.

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
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).
Local Coercion base : class_of >-> Filtered.class_of.

Definition pack nbhs' (m : @mixin_of T nbhs') :=
  fun bT (b : Filtered.class_of T T) of phant_id (@Filtered.class T bT) b =>
  fun m'   of phant_id m (m' : @mixin_of T (Filtered.nbhs_op b)) =>
  @Pack T (@Class _ b m').
Definition filteredType := @Filtered.Pack cT cT xclass.

End ClassDef.

Coercion sort : type >-> Sortclass.
Canonical filteredType.
Notation topologicalType := type.
Notation TopologicalType T m := (@pack T _ m _ _ idfun _ idfun).

Definition eventually := filter_from setT (fun N => [set n | (N <= n)%N]).
Notation "'\oo'" := eventually : classical_set_scope.

Canonical eventually_filter_source X :=
   @Filtered.Source X _ nat (fun f => f @ \oo).

Global Instance eventually_filter : ProperFilter eventually.
Admitted.

Section separated_topologicalType.
Variable (T : topologicalType).

Lemma lim_cst {U} {F} {FF : ProperFilter F} (k : T) :
   lim ((fun _ : U => k) @ F) = k.
Admitted.

End separated_topologicalType.
Import mathcomp.algebra.all_algebra.
Export mathcomp.analysis.constructive_ereal.

Canonical ereal_pointed (R : numDomainType) := PointedType (extended R) 0%E.

Section ereal_nbhs.
Context {R : numFieldType}.
Definition ereal_nbhs (x : \bar R) (P : \bar R -> Prop) : Prop.
Admitted.
Canonical ereal_ereal_filter :=
  FilteredType (extended R) (extended R) (ereal_nbhs).
End ereal_nbhs.

Section ereal_topologicalType.
Variable R : realFieldType.
Definition ereal_topologicalMixin : Topological.mixin_of (@ereal_nbhs R).
Admitted.
Canonical ereal_topologicalType := TopologicalType _ ereal_topologicalMixin.

End ereal_topologicalType.
Import mathcomp.classical.boolp.

Reserved Notation "R ^nat" (at level 0).

Reserved Notation "\big [ op / idx ]_ ( m <= i <oo | P ) F"
  (at level 36, F at level 36, op, idx at level 10, m, i at level 50,
           format "'[' \big [ op / idx ]_ ( m  <=  i  <oo  |  P )  F ']'").
Reserved Notation "\sum_ ( i '<oo' | P ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \sum_ ( i  <oo  |  P ) '/  '  F ']'").

Definition sequence R := nat -> R.
Notation "R ^nat" := (sequence R) : type_scope.

Notation "\big [ op / idx ]_ ( m <= i <oo | P ) F" :=
  (lim (fun n => (\big[ op / idx ]_(m <= i < n | P) F))) : big_scope.
Notation "\sum_ ( i <oo | P ) F" :=
  (\big[+%E/0%E]_(0 <= i <oo | P%B) F%E) : ereal_scope.
Local Open Scope ereal_scope.
Variables (R : realFieldType) (f : (\bar R)^nat).

Lemma eseries_pred0 P : P =1 xpred0 -> \sum_(i <oo | P i) f i = 0.
Proof.
move=> P0; rewrite (_ : (fun _ => _) = fun=> 0) ?lim_cst// funeqE => n.
