(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "-projection-no-head-constant" "-w" "-redundant-canonical-projection" "-w" "-notation-overridden" "-w" "+duplicate-clear" "-w" "-ambiguous-paths" "-w" "+non-primitive-record" "-w" "+undeclared-scope" "-w" "-deprecated-hint-without-locality" "-w" "-deprecated-ident-entry" "-w" "-deprecated-native-compiler-option" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/mathcomp/mathcomp" "mathcomp" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-I" "/github/workspace/builds/coq/coq-failing/_build_ci/mathcomp/mathcomp" "-top" "bug_01" "-native-compiler" "ondemand") -*- *)
(* File reduced by coq-bug-finder from original input, then from 5976 lines to 4914 lines, then from 4559 lines to 258 lines, then from 312 lines to 2285 lines, then from 2290 lines to 373 lines, then from 425 lines to 3660 lines, then from 3664 lines to 414 lines, then from 465 lines to 3264 lines, then from 3269 lines to 2886 lines, then from 2755 lines to 611 lines, then from 662 lines to 3802 lines, then from 3807 lines to 646 lines, then from 696 lines to 5297 lines, then from 5302 lines to 5208 lines, then from 4903 lines to 1108 lines, then from 1156 lines to 1546 lines, then from 1551 lines to 1143 lines, then from 1182 lines to 1930 lines, then from 1935 lines to 1274 lines, then from 1311 lines to 4394 lines, then from 4399 lines to 3359 lines *)
(* coqc version 8.15+alpha compiled with OCaml 4.13.0
   coqtop version runner-0277ea0f-project-6138686-concurrent-0:/builds/coq/coq/_build/default,(HEAD detached at 3aaf20f) (3aaf20f513cc7b2633d7aed182d34a363fcb5dfa)
   Expected coqc runtime on this file: 1.817 sec *)
Declare ML Module "ltac_plugin".
Module Export AdmitTactic.
Module Import LocalFalse.
Inductive False : Prop := .
End LocalFalse.
Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.
End AdmitTactic.
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
Require mathcomp.ssreflect.prime.
Require mathcomp.ssreflect.finset.
Require mathcomp.ssreflect.binomial.
Require mathcomp.algebra.ssralg.
Module mathcomp_DOT_fingroup_DOT_fingroup_WRAPPED.
Module Export fingroup.
Import mathcomp.ssreflect.ssreflect.
Import mathcomp.ssreflect.ssrbool.
Import mathcomp.ssreflect.ssrfun.
Import mathcomp.ssreflect.eqtype.
Import mathcomp.ssreflect.ssrnat.
Import mathcomp.ssreflect.seq.
Import mathcomp.ssreflect.choice.
Import mathcomp.ssreflect.fintype.
Import mathcomp.ssreflect.div.
Import mathcomp.ssreflect.path.
Import mathcomp.ssreflect.tuple.
Import mathcomp.ssreflect.bigop.
Import mathcomp.ssreflect.prime.
Import mathcomp.ssreflect.finset.

 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope group_scope.
Declare Scope Group_scope.

Delimit Scope group_scope with g.
Delimit Scope Group_scope with G.

 
 
 
Module GroupScope.
Open Scope group_scope.
End GroupScope.
Import GroupScope.

 
Reserved Notation "[ ~ x1 , x2 , .. , xn ]" (at level 0,
  format  "'[ ' [ ~  x1 , '/'  x2 , '/'  .. , '/'  xn ] ']'").
Reserved Notation "[ 1 gT ]" (at level 0, format "[ 1  gT ]").
Reserved Notation "[ 1 ]" (at level 0, format "[ 1 ]").
Reserved Notation "[ 'subg' G ]" (at level 0, format "[ 'subg'  G ]").
Reserved Notation "A ^#" (at level 2, format "A ^#").
Reserved Notation "A :^ x" (at level 35, right associativity).
Reserved Notation "x ^: B" (at level 35, right associativity).
Reserved Notation "A :^: B" (at level 35, right associativity).
Reserved Notation "#| B : A |" (at level 0, B, A at level 99,
  format "#| B  :  A |").
Reserved Notation "''N' ( A )" (at level 8, format "''N' ( A )").
Reserved Notation "''N_' G ( A )" (at level 8, G at level 2,
  format "''N_' G ( A )").
Reserved Notation "A <| B" (at level 70, no associativity).
Reserved Notation "A <*> B" (at level 40, left associativity).
Reserved Notation "[ ~: A1 , A2 , .. , An ]" (at level 0,
  format "[ ~: '['  A1 , '/'  A2 , '/'  .. , '/'  An ']' ]").
Reserved Notation "[ 'max' A 'of' G | gP ]" (at level 0,
  format "[ '[hv' 'max'  A  'of'  G '/ '  |  gP ']' ]").
Reserved Notation "[ 'max' G | gP ]" (at level 0,
  format "[ '[hv' 'max'  G '/ '  |  gP ']' ]").
Reserved Notation "[ 'max' A 'of' G | gP & gQ ]" (at level 0,
  format "[ '[hv' 'max'  A  'of'  G '/ '  |  gP '/ '  &  gQ ']' ]").
Reserved Notation "[ 'max' G | gP & gQ ]" (at level 0,
  format "[ '[hv' 'max'  G '/ '  |  gP '/ '  &  gQ ']' ]").
Reserved Notation "[ 'min' A 'of' G | gP ]" (at level 0,
  format "[ '[hv' 'min'  A  'of'  G '/ '  |  gP ']' ]").
Reserved Notation "[ 'min' G | gP ]" (at level 0,
  format "[ '[hv' 'min'  G '/ '  |  gP ']' ]").
Reserved Notation "[ 'min' A 'of' G | gP & gQ ]" (at level 0,
  format "[ '[hv' 'min'  A  'of'  G '/ '  |  gP '/ '  &  gQ ']' ]").
Reserved Notation "[ 'min' G | gP & gQ ]" (at level 0,
  format "[ '[hv' 'min'  G '/ '  |  gP '/ '  &  gQ ']' ]").

Module FinGroup.

 
 
 
 
 
 
 
 
 
 
 
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
Notation "1" := one.
Infix "*" := mul.
Notation "x ^-1" := (inv x).

Lemma mk_invgK : involutive inv.
Proof.
have mulV21 x: x^-1^-1 * 1 = x by rewrite -(mulV x) mulA mulV mul1.
by move=> x; rewrite -[_ ^-1]mulV21 -(mul1 1) mulA !mulV21.
Qed.

Lemma mk_invMg : {morph inv : x y / x * y >-> y * x}.
admit.
Defined.

Definition Mixin := BaseMixin mulA mul1 mk_invgK mk_invMg.

End Mixin.

Definition pack_base T m :=
  fun c cT & phant_id (Finite.class cT) c => @PackBase T m c.

Definition clone_base T :=
  fun bT & sort bT -> T =>
  fun m c (bT' := @PackBase T m c) & phant_id bT' bT => bT'.

Definition clone T :=
  fun bT gT & sort bT * sort (base gT) -> T * T =>
  fun m (gT' := @Pack bT m) & phant_id gT' gT => gT'.

Section InheritedClasses.

Variable bT : base_type.
Local Notation T := (arg_sort bT).
Local Notation rT := (sort bT).
Local Notation class := (finClass bT).

Canonical eqType := Equality.Pack class.
Canonical choiceType := Choice.Pack class.
Canonical countType := Countable.Pack class.
Canonical finType := Finite.Pack class.
Definition arg_eqType := Eval hnf in [eqType of T].
Definition arg_choiceType := Eval hnf in [choiceType of T].
Definition arg_countType := Eval hnf in [countType of T].
Definition arg_finType := Eval hnf in [finType of T].

End InheritedClasses.

Module Import Exports.
 
 
 
 
Coercion arg_sort : base_type >-> Sortclass.
Coercion sort : base_type >-> Sortclass.
Coercion mixin : base_type >-> mixin_of.
Coercion base : type >-> base_type.
Canonical eqType.
Canonical choiceType.
Canonical countType.
Canonical finType.
Coercion arg_eqType : base_type >-> Equality.type.
Canonical arg_eqType.
Coercion arg_choiceType : base_type >-> Choice.type.
Canonical arg_choiceType.
Coercion arg_countType : base_type >-> Countable.type.
Canonical arg_countType.
Coercion arg_finType : base_type >-> Finite.type.
Canonical arg_finType.
Bind Scope group_scope with sort.
Bind Scope group_scope with arg_sort.
Notation baseFinGroupType := base_type.
Notation finGroupType := type.
Notation BaseFinGroupType T m := (@pack_base T m _ _ id).
Notation FinGroupType := Pack.
Notation "[ 'baseFinGroupType' 'of' T ]" := (@clone_base T _ id _ _ id)
  (at level 0, format "[ 'baseFinGroupType'  'of'  T ]") : form_scope.
Notation "[ 'finGroupType' 'of' T ]" := (@clone T _ _ id _ id)
  (at level 0, format "[ 'finGroupType'  'of'  T ]") : form_scope.
End Exports.

End FinGroup.
Export FinGroup.Exports.

Section ElementOps.

Variable T : baseFinGroupType.
Notation rT := (FinGroup.sort T).

Definition oneg : rT := FinGroup.one T.
Definition mulg : T -> T -> rT := FinGroup.mul T.
Definition invg : T -> rT := FinGroup.inv T.
Definition expgn_rec (x : T) n : rT := iterop n mulg x oneg.

End ElementOps.

Definition expgn := nosimpl expgn_rec.

Notation "1" := (oneg _) : group_scope.
Notation "x1 * x2" := (mulg x1 x2) : group_scope.
Notation "x ^-1" := (invg x) : group_scope.
Notation "x ^+ n" := (expgn x n) : group_scope.
Notation "x ^- n" := (x ^+ n)^-1 : group_scope.

 
 
 
Definition conjg (T : finGroupType) (x y : T) := y^-1 * (x * y).
Notation "x1 ^ x2" := (conjg x1 x2) : group_scope.

Definition commg (T : finGroupType) (x y : T) := x^-1 * x ^ y.
Notation "[ ~ x1 , x2 , .. , xn ]" := (commg .. (commg x1 x2) .. xn)
  : group_scope.

Prenex Implicits mulg invg expgn conjg commg.

Notation "\prod_ ( i <- r | P ) F" :=
  (\big[mulg/1]_(i <- r | P%B) F%g) : group_scope.
Notation "\prod_ ( i <- r ) F" :=
  (\big[mulg/1]_(i <- r) F%g) : group_scope.
Notation "\prod_ ( m <= i < n | P ) F" :=
  (\big[mulg/1]_(m <= i < n | P%B) F%g) : group_scope.
Notation "\prod_ ( m <= i < n ) F" :=
  (\big[mulg/1]_(m <= i < n) F%g) : group_scope.
Notation "\prod_ ( i | P ) F" :=
  (\big[mulg/1]_(i | P%B) F%g) : group_scope.
Notation "\prod_ i F" :=
  (\big[mulg/1]_i F%g) : group_scope.
Notation "\prod_ ( i : t | P ) F" :=
  (\big[mulg/1]_(i : t | P%B) F%g) (only parsing) : group_scope.
Notation "\prod_ ( i : t ) F" :=
  (\big[mulg/1]_(i : t) F%g) (only parsing) : group_scope.
Notation "\prod_ ( i < n | P ) F" :=
  (\big[mulg/1]_(i < n | P%B) F%g) : group_scope.
Notation "\prod_ ( i < n ) F" :=
  (\big[mulg/1]_(i < n) F%g) : group_scope.
Notation "\prod_ ( i 'in' A | P ) F" :=
  (\big[mulg/1]_(i in A | P%B) F%g) : group_scope.
Notation "\prod_ ( i 'in' A ) F" :=
  (\big[mulg/1]_(i in A) F%g) : group_scope.

Section PreGroupIdentities.

Variable T : baseFinGroupType.
Implicit Types x y z : T.
Local Notation mulgT := (@mulg T).

Lemma mulgA : associative mulgT.
admit.
Defined.
Lemma mul1g : left_id 1 mulgT.
admit.
Defined.
Lemma invgK : @involutive T invg.
admit.
Defined.
Lemma invMg x y : (x * y)^-1 = y^-1 * x^-1.
admit.
Defined.

Lemma invg_inj : @injective T T invg.
admit.
Defined.

Lemma eq_invg_sym x y : (x^-1 == y) = (x == y^-1).
admit.
Defined.

Lemma invg1 : 1^-1 = 1 :> T.
admit.
Defined.

Lemma eq_invg1 x : (x^-1 == 1) = (x == 1).
admit.
Defined.

Lemma mulg1 : right_id 1 mulgT.
admit.
Defined.

Canonical finGroup_law := Monoid.Law mulgA mul1g mulg1.

Lemma expgnE x n : x ^+ n = expgn_rec x n.
admit.
Defined.

Lemma expg0 x : x ^+ 0 = 1.
admit.
Defined.
Lemma expg1 x : x ^+ 1 = x.
admit.
Defined.

Lemma expgS x n : x ^+ n.+1 = x * x ^+ n.
admit.
Defined.

Lemma expg1n n : 1 ^+ n = 1 :> T.
admit.
Defined.

Lemma expgD x n m : x ^+ (n + m) = x ^+ n * x ^+ m.
admit.
Defined.

Lemma expgSr x n : x ^+ n.+1 = x ^+ n * x.
admit.
Defined.

Lemma expgM x n m : x ^+ (n * m) = x ^+ n ^+ m.
admit.
Defined.

Lemma expgAC x m n : x ^+ m ^+ n = x ^+ n ^+ m.
admit.
Defined.

Definition commute x y := x * y = y * x.

Lemma commute_refl x : commute x x.
admit.
Defined.

Lemma commute_sym x y : commute x y -> commute y x.
admit.
Defined.

Lemma commute1 x : commute x 1.
admit.
Defined.

Lemma commuteM x y z : commute x y ->  commute x z ->  commute x (y * z).
admit.
Defined.

Lemma commuteX x y n : commute x y ->  commute x (y ^+ n).
admit.
Defined.

Lemma commuteX2 x y m n : commute x y -> commute (x ^+ m) (y ^+ n).
admit.
Defined.

Lemma expgVn x n : x^-1 ^+ n = x ^- n.
admit.
Defined.

Lemma expgMn x y n : commute x y -> (x * y) ^+ n  = x ^+ n * y ^+ n.
admit.
Defined.

End PreGroupIdentities.

Hint Resolve commute1 : core.
Arguments invg_inj {T} [x1 x2].
Prenex Implicits commute invgK.

Section GroupIdentities.

Variable T : finGroupType.
Implicit Types x y z : T.
Local Notation mulgT := (@mulg T).

Lemma mulVg : left_inverse 1 invg mulgT.
admit.
Defined.

Lemma mulgV : right_inverse 1 invg mulgT.
admit.
Defined.

Lemma mulKg : left_loop invg mulgT.
admit.
Defined.

Lemma mulKVg : rev_left_loop invg mulgT.
admit.
Defined.

Lemma mulgI : right_injective mulgT.
admit.
Defined.

Lemma mulgK : right_loop invg mulgT.
admit.
Defined.

Lemma mulgKV : rev_right_loop invg mulgT.
admit.
Defined.

Lemma mulIg : left_injective mulgT.
admit.
Defined.

Lemma eq_invg_mul x y : (x^-1 == y :> T) = (x * y == 1 :> T).
admit.
Defined.

Lemma eq_mulgV1 x y : (x == y) = (x * y^-1 == 1 :> T).
admit.
Defined.

Lemma eq_mulVg1 x y : (x == y) = (x^-1 * y == 1 :> T).
admit.
Defined.

Lemma commuteV x y : commute x y -> commute x y^-1.
admit.
Defined.

Lemma conjgE x y : x ^ y = y^-1 * (x * y).
admit.
Defined.

Lemma conjgC x y : x * y = y * x ^ y.
admit.
Defined.

Lemma conjgCV x y : x * y = y ^ x^-1 * x.
admit.
Defined.

Lemma conjg1 x : x ^ 1 = x.
admit.
Defined.

Lemma conj1g x : 1 ^ x = 1.
admit.
Defined.

Lemma conjMg x y z : (x * y) ^ z = x ^ z * y ^ z.
admit.
Defined.

Lemma conjgM x y z : x ^ (y * z) = (x ^ y) ^ z.
admit.
Defined.

Lemma conjVg x y : x^-1 ^ y = (x ^ y)^-1.
admit.
Defined.

Lemma conjJg x y z : (x ^ y) ^ z = (x ^ z) ^ y ^ z.
admit.
Defined.

Lemma conjXg x y n : (x ^+ n) ^ y = (x ^ y) ^+ n.
admit.
Defined.

Lemma conjgK : @right_loop T T invg conjg.
admit.
Defined.

Lemma conjgKV : @rev_right_loop T T invg conjg.
admit.
Defined.

Lemma conjg_inj : @left_injective T T T conjg.
admit.
Defined.

Lemma conjg_eq1 x y : (x ^ y == 1) = (x == 1).
admit.
Defined.

Lemma conjg_prod I r (P : pred I) F z :
  (\prod_(i <- r | P i) F i) ^ z = \prod_(i <- r | P i) (F i ^ z).
admit.
Defined.

Lemma commgEl x y : [~ x, y] = x^-1 * x ^ y.
admit.
Defined.

Lemma commgEr x y : [~ x, y] = y^-1 ^ x * y.
admit.
Defined.

Lemma commgC x y : x * y = y * x * [~ x, y].
admit.
Defined.

Lemma commgCV x y : x * y = [~ x^-1, y^-1] * (y * x).
admit.
Defined.

Lemma conjRg x y z : [~ x, y] ^ z = [~ x ^ z, y ^ z].
admit.
Defined.

Lemma invg_comm x y : [~ x, y]^-1 = [~ y, x].
admit.
Defined.

Lemma commgP x y : reflect (commute x y) ([~ x, y] == 1 :> T).
admit.
Defined.

Lemma conjg_fixP x y : reflect (x ^ y = x) ([~ x, y] == 1 :> T).
admit.
Defined.

Lemma commg1_sym x y : ([~ x, y] == 1 :> T) = ([~ y, x] == 1 :> T).
admit.
Defined.

Lemma commg1 x : [~ x, 1] = 1.
admit.
Defined.

Lemma comm1g x : [~ 1, x] = 1.
admit.
Defined.

Lemma commgg x : [~ x, x] = 1.
admit.
Defined.

Lemma commgXg x n : [~ x, x ^+ n] = 1.
admit.
Defined.

Lemma commgVg x : [~ x, x^-1] = 1.
admit.
Defined.

Lemma commgXVg x n : [~ x, x ^- n] = 1.
admit.
Defined.

 

End GroupIdentities.

Hint Rewrite mulg1 mul1g invg1 mulVg mulgV (@invgK) mulgK mulgKV
             invMg mulgA : gsimpl.

Definition gsimp := (mulg1 , mul1g, (invg1, @invgK), (mulgV, mulVg)).
Definition gnorm := (gsimp, (mulgK, mulgKV, (mulgA, invMg))).

Arguments mulgI [T].
Arguments mulIg [T].
Arguments conjg_inj {T} x [x1 x2].
Arguments commgP {T x y}.
Arguments conjg_fixP {T x y}.

Section Repr.
 

Variable gT : baseFinGroupType.
Implicit Type A : {set gT}.

Definition repr A := if 1 \in A then 1 else odflt 1 [pick x in A].

Lemma mem_repr A x : x \in A -> repr A \in A.
admit.
Defined.

Lemma card_mem_repr A : #|A| > 0 -> repr A \in A.
admit.
Defined.

Lemma repr_set1 x : repr [set x] = x.
admit.
Defined.

Lemma repr_set0 : repr set0 = 1.
admit.
Defined.

End Repr.

Arguments mem_repr [gT A].

Section BaseSetMulDef.
 
Variable gT : baseFinGroupType.
Implicit Types A B : {set gT}.

 

Definition set_mulg A B := mulg @2: (A, B).
Definition set_invg A := invg @^-1: A.

 

Lemma set_mul1g : left_id [set 1] set_mulg.
admit.
Defined.

Lemma set_mulgA : associative set_mulg.
admit.
Defined.

Lemma set_invgK : involutive set_invg.
admit.
Defined.

Lemma set_invgM : {morph set_invg : A B / set_mulg A B >-> set_mulg B A}.
admit.
Defined.

Definition group_set_baseGroupMixin : FinGroup.mixin_of (set_type gT) :=
  FinGroup.BaseMixin set_mulgA set_mul1g set_invgK set_invgM.

Canonical group_set_baseGroupType :=
  Eval hnf in BaseFinGroupType (set_type gT) group_set_baseGroupMixin.

Canonical group_set_of_baseGroupType :=
  Eval hnf in [baseFinGroupType of {set gT}].

End BaseSetMulDef.

 
 
 
 
 
 
 
 

Module Export GroupSet.
Definition sort (gT : baseFinGroupType) := {set gT}.
End GroupSet.
Identity Coercion GroupSet_of_sort : GroupSet.sort >-> set_of.

Module Type GroupSetBaseGroupSig.
Definition sort gT := group_set_of_baseGroupType gT : Type.
End GroupSetBaseGroupSig.

Module MakeGroupSetBaseGroup (Gset_base : GroupSetBaseGroupSig).
Identity Coercion of_sort : Gset_base.sort >-> FinGroup.arg_sort.
End MakeGroupSetBaseGroup.

Module Export GroupSetBaseGroup := MakeGroupSetBaseGroup GroupSet.

Canonical group_set_eqType gT := Eval hnf in [eqType of GroupSet.sort gT].
Canonical group_set_choiceType gT :=
  Eval hnf in [choiceType of GroupSet.sort gT].
Canonical group_set_countType gT := Eval hnf in [countType of GroupSet.sort gT].
Canonical group_set_finType gT := Eval hnf in [finType of GroupSet.sort gT].

Section GroupSetMulDef.
 
 
 
Variable gT : finGroupType.
Implicit Types A B : {set gT}.
Implicit Type x y : gT.

Definition lcoset A x := mulg x @: A.
Definition rcoset A x := mulg^~ x @: A.
Definition lcosets A B := lcoset A @: B.
Definition rcosets A B := rcoset A @: B.
Definition indexg B A := #|rcosets A B|.

Definition conjugate A x := conjg^~ x @: A.
Definition conjugates A B := conjugate A @: B.
Definition class x B := conjg x @: B.
Definition classes A := class^~ A @: A.
Definition class_support A B := conjg @2: (A, B).

Definition commg_set A B := commg @2: (A, B).

 
 
Definition normaliser A := [set x | conjugate A x \subset A].
Definition centraliser A := \bigcap_(x in A) normaliser [set x].
Definition abelian A := A \subset centraliser A.
Definition normal A B := (A \subset B) && (B \subset normaliser A).

 
 
Definition normalised A := forall x, conjugate A x = A.
Definition centralises x A := forall y, y \in A -> commute x y.
Definition centralised A := forall x, centralises x A.

End GroupSetMulDef.

Arguments lcoset _ _%g _%g.
Arguments rcoset _ _%g _%g.
Arguments rcosets _ _%g _%g.
Arguments lcosets _ _%g _%g.
Arguments indexg _ _%g _%g.
Arguments conjugate _ _%g _%g.
Arguments conjugates _ _%g _%g.
Arguments class _ _%g _%g.
Arguments classes _ _%g.
Arguments class_support _ _%g _%g.
Arguments commg_set _ _%g _%g.
Arguments normaliser _ _%g.
Arguments centraliser _ _%g.
Arguments abelian _ _%g.
Arguments normal _ _%g _%g.
Arguments normalised _ _%g.
Arguments centralises _ _%g _%g.
Arguments centralised _ _%g.

Notation "[ 1 gT ]" := (1 : {set gT}) : group_scope.
Notation "[ 1 ]" := [1 FinGroup.sort _] : group_scope.

Notation "A ^#" := (A :\ 1) : group_scope.

Notation "x *: A" := ([set x%g] * A) : group_scope.
Notation "A :* x" := (A * [set x%g]) : group_scope.
Notation "A :^ x" := (conjugate A x) : group_scope.
Notation "x ^: B" := (class x B) : group_scope.
Notation "A :^: B" := (conjugates A B) : group_scope.

Notation "#| B : A |" := (indexg B A) : group_scope.

 
 
 
 

Notation "''N' ( A )" := (normaliser A) : group_scope.
Notation "''N_' G ( A )" := (G%g :&: 'N(A)) : group_scope.
Notation "A <| B" := (normal A B) : group_scope.
Notation "''C' ( A )" := (centraliser A) : group_scope.
Notation "''C_' G ( A )" := (G%g :&: 'C(A)) : group_scope.
Notation "''C_' ( G ) ( A )" := 'C_G(A) (only parsing) : group_scope.
Notation "''C' [ x ]" := 'N([set x%g]) : group_scope.
Notation "''C_' G [ x ]" := 'N_G([set x%g]) : group_scope.
Notation "''C_' ( G ) [ x ]" := 'C_G[x] (only parsing) : group_scope.

Prenex Implicits repr lcoset rcoset lcosets rcosets normal.
Prenex Implicits conjugate conjugates class classes class_support.
Prenex Implicits commg_set normalised centralised abelian.

Section BaseSetMulProp.
 
Variable gT : baseFinGroupType.
Implicit Types A B C D : {set gT}.
Implicit Type x y z : gT.

 
 

Lemma mulsgP A B x :
  reflect (imset2_spec mulg (mem A) (fun _ => mem B) x) (x \in A * B).
admit.
Defined.

Lemma mem_mulg A B x y : x \in A -> y \in B -> x * y \in A * B.
admit.
Defined.

Lemma prodsgP (I : finType) (P : pred I) (A : I -> {set gT}) x :
  reflect (exists2 c, forall i, P i -> c i \in A i & x = \prod_(i | P i) c i)
          (x \in \prod_(i | P i) A i).
admit.
Defined.

Lemma mem_prodg (I : finType) (P : pred I) (A : I -> {set gT}) c :
  (forall i, P i -> c i \in A i) -> \prod_(i | P i) c i \in \prod_(i | P i) A i.
admit.
Defined.

Lemma mulSg A B C : A \subset B -> A * C \subset B * C.
admit.
Defined.

Lemma mulgS A B C : B \subset C -> A * B \subset A * C.
admit.
Defined.

Lemma mulgSS A B C D : A \subset B -> C \subset D -> A * C \subset B * D.
admit.
Defined.

Lemma mulg_subl A B : 1 \in B -> A \subset A * B.
admit.
Defined.

Lemma mulg_subr A B : 1 \in A -> B \subset A * B.
admit.
Defined.

Lemma mulUg A B C : (A :|: B) * C = (A * C) :|: (B * C).
admit.
Defined.

Lemma mulgU A B C : A * (B :|: C) = (A * B) :|: (A * C).
admit.
Defined.

 

Lemma invUg A B : (A :|: B)^-1 = A^-1 :|: B^-1.
admit.
Defined.

Lemma invIg A B : (A :&: B)^-1 = A^-1 :&: B^-1.
admit.
Defined.

Lemma invDg A B : (A :\: B)^-1 = A^-1 :\: B^-1.
admit.
Defined.

Lemma invCg A : (~: A)^-1 = ~: A^-1.
admit.
Defined.

Lemma invSg A B : (A^-1 \subset B^-1) = (A \subset B).
admit.
Defined.

Lemma mem_invg x A : (x \in A^-1) = (x^-1 \in A).
admit.
Defined.

Lemma memV_invg x A : (x^-1 \in A^-1) = (x \in A).
admit.
Defined.

Lemma card_invg A : #|A^-1| = #|A|.
admit.
Defined.

 

Lemma set1gE : 1 = [set 1] :> {set gT}.
admit.
Defined.

Lemma set1gP x : reflect (x = 1) (x \in [1]).
admit.
Defined.

Lemma mulg_set1 x y : [set x] :* y = [set x * y].
admit.
Defined.

Lemma invg_set1 x : [set x]^-1 = [set x^-1].
admit.
Defined.

End BaseSetMulProp.

Arguments set1gP {gT x}.
Arguments mulsgP {gT A B x}.
Arguments prodsgP {gT I P A x}.

Section GroupSetMulProp.
 
Variable gT : finGroupType.
Implicit Types A B C D : {set gT}.
Implicit Type x y z : gT.

 

Lemma lcosetE A x : lcoset A x = x *: A.
admit.
Defined.

Lemma card_lcoset A x : #|x *: A| = #|A|.
admit.
Defined.

Lemma mem_lcoset A x y : (y \in x *: A) = (x^-1 * y \in A).
admit.
Defined.

Lemma lcosetP A x y : reflect (exists2 a, a \in A & y = x * a) (y \in x *: A).
admit.
Defined.

Lemma lcosetsP A B C :
  reflect (exists2 x, x \in B & C = x *: A) (C \in lcosets A B).
admit.
Defined.

Lemma lcosetM A x y : (x * y) *: A = x *: (y *: A).
admit.
Defined.

Lemma lcoset1 A : 1 *: A = A.
admit.
Defined.

Lemma lcosetK : left_loop invg (fun x A => x *: A).
admit.
Defined.

Lemma lcosetKV : rev_left_loop invg (fun x A => x *: A).
admit.
Defined.

Lemma lcoset_inj : right_injective (fun x A => x *: A).
admit.
Defined.

Lemma lcosetS x A B : (x *: A \subset x *: B) = (A \subset B).
admit.
Defined.

Lemma sub_lcoset x A B : (A \subset x *: B) = (x^-1 *: A \subset B).
admit.
Defined.

Lemma sub_lcosetV x A B : (A \subset x^-1 *: B) = (x *: A \subset B).
admit.
Defined.

 

Lemma rcosetE A x : rcoset A x = A :* x.
admit.
Defined.

Lemma card_rcoset A x : #|A :* x| = #|A|.
admit.
Defined.

Lemma mem_rcoset A x y : (y \in A :* x) = (y * x^-1 \in A).
admit.
Defined.

Lemma rcosetP A x y : reflect (exists2 a, a \in A & y = a * x) (y \in A :* x).
admit.
Defined.

Lemma rcosetsP A B C :
  reflect (exists2 x, x \in B & C = A :* x) (C \in rcosets A B).
admit.
Defined.

Lemma rcosetM A x y : A :* (x * y) = A :* x :* y.
admit.
Defined.

Lemma rcoset1 A : A :* 1 = A.
admit.
Defined.

Lemma rcosetK : right_loop invg (fun A x => A :* x).
admit.
Defined.

Lemma rcosetKV : rev_right_loop invg (fun A x => A :* x).
admit.
Defined.

Lemma rcoset_inj : left_injective (fun A x => A :* x).
admit.
Defined.

Lemma rcosetS x A B : (A :* x \subset B :* x) = (A \subset B).
admit.
Defined.

Lemma sub_rcoset x A B : (A \subset B :* x) = (A :* x ^-1 \subset B).
admit.
Defined.

Lemma sub_rcosetV x A B : (A \subset B :* x^-1) = (A :* x \subset B).
admit.
Defined.

 
Lemma invg_lcosets A B : (lcosets A B)^-1 = rcosets A^-1 B^-1.
admit.
Defined.

 

Lemma conjg_preim A x : A :^ x = (conjg^~ x^-1) @^-1: A.
admit.
Defined.

Lemma mem_conjg A x y : (y \in A :^ x) = (y ^ x^-1 \in A).
admit.
Defined.

Lemma mem_conjgV A x y : (y \in A :^ x^-1) = (y ^ x \in A).
admit.
Defined.

Lemma memJ_conjg A x y : (y ^ x \in A :^ x) = (y \in A).
admit.
Defined.

Lemma conjsgE A x : A :^ x = x^-1 *: (A :* x).
admit.
Defined.

Lemma conjsg1 A : A :^ 1 = A.
admit.
Defined.

Lemma conjsgM A x y : A :^ (x * y) = (A :^ x) :^ y.
admit.
Defined.

Lemma conjsgK : @right_loop _ gT invg conjugate.
admit.
Defined.

Lemma conjsgKV : @rev_right_loop _ gT invg conjugate.
admit.
Defined.

Lemma conjsg_inj : @left_injective _ gT _ conjugate.
admit.
Defined.

Lemma cardJg A x : #|A :^ x| = #|A|.
admit.
Defined.

Lemma conjSg A B x : (A :^ x \subset B :^ x) = (A \subset B).
admit.
Defined.

Lemma properJ A B x : (A :^ x \proper B :^ x) = (A \proper B).
admit.
Defined.

Lemma sub_conjg A B x : (A :^ x \subset B) = (A \subset B :^ x^-1).
admit.
Defined.

Lemma sub_conjgV A B x : (A :^ x^-1 \subset B) = (A \subset B :^ x).
admit.
Defined.

Lemma conjg_set1 x y : [set x] :^ y = [set x ^ y].
admit.
Defined.

Lemma conjs1g x : 1 :^ x = 1.
admit.
Defined.

Lemma conjsg_eq1 A x : (A :^ x == 1%g) = (A == 1%g).
admit.
Defined.

Lemma conjsMg A B x : (A * B) :^ x = A :^ x * B :^ x.
admit.
Defined.

Lemma conjIg A B x : (A :&: B) :^ x = A :^ x :&: B :^ x.
admit.
Defined.

Lemma conj0g x : set0 :^ x = set0.
admit.
Defined.

Lemma conjTg x : [set: gT] :^ x = [set: gT].
admit.
Defined.

Lemma bigcapJ I r (P : pred I) (B : I -> {set gT}) x :
  \bigcap_(i <- r | P i) (B i :^ x) = (\bigcap_(i <- r | P i) B i) :^ x.
admit.
Defined.

Lemma conjUg A B x : (A :|: B) :^ x = A :^ x :|: B :^ x.
admit.
Defined.

Lemma bigcupJ I r (P : pred I) (B : I -> {set gT}) x :
  \bigcup_(i <- r | P i) (B i :^ x) = (\bigcup_(i <- r | P i) B i) :^ x.
admit.
Defined.

Lemma conjCg A x : (~: A) :^ x = ~: A :^ x.
admit.
Defined.

Lemma conjDg A B x : (A :\: B) :^ x = A :^ x :\: B :^ x.
admit.
Defined.

Lemma conjD1g A x : A^# :^ x = (A :^ x)^#.
admit.
Defined.

 

Lemma memJ_class x y A : y \in A -> x ^ y \in x ^: A.
admit.
Defined.

Lemma classS x A B : A \subset B -> x ^: A \subset x ^: B.
admit.
Defined.

Lemma class_set1 x y :  x ^: [set y] = [set x ^ y].
admit.
Defined.

Lemma class1g x A : x \in A -> 1 ^: A = 1.
admit.
Defined.

Lemma classVg x A : x^-1 ^: A = (x ^: A)^-1.
admit.
Defined.

Lemma mem_classes x A : x \in A -> x ^: A \in classes A.
admit.
Defined.

Lemma memJ_class_support A B x y :
   x \in A -> y \in B -> x ^ y \in class_support A B.
admit.
Defined.

Lemma class_supportM A B C :
  class_support A (B * C) = class_support (class_support A B) C.
admit.
Defined.

Lemma class_support_set1l A x : class_support [set x] A = x ^: A.
admit.
Defined.

Lemma class_support_set1r A x : class_support A [set x] = A :^ x.
admit.
Defined.

Lemma classM x A B : x ^: (A * B) = class_support (x ^: A) B.
admit.
Defined.

Lemma class_lcoset x y A : x ^: (y *: A) = (x ^ y) ^: A.
admit.
Defined.

Lemma class_rcoset x A y : x ^: (A :* y) = (x ^: A) :^ y.
admit.
Defined.

 

Lemma conjugatesS A B C : B \subset C -> A :^: B \subset A :^: C.
admit.
Defined.

Lemma conjugates_set1 A x : A :^: [set x] = [set A :^ x].
admit.
Defined.

Lemma conjugates_conj A x B : (A :^ x) :^: B = A :^: (x *: B).
admit.
Defined.

 

Lemma class_supportEl A B : class_support A B = \bigcup_(x in A) x ^: B.
admit.
Defined.

Lemma class_supportEr A B : class_support A B = \bigcup_(x in B) A :^ x.
admit.
Defined.

 

Definition group_set A := (1 \in A) && (A * A \subset A).

Lemma group_setP A :
  reflect (1 \in A /\ {in A & A, forall x y, x * y \in A}) (group_set A).
admit.
Defined.

Structure group_type : Type := Group {
  gval :> GroupSet.sort gT;
  _ : group_set gval
}.

Definition group_of of phant gT : predArgType := group_type.
Local Notation groupT := (group_of (Phant gT)).
Identity Coercion type_of_group : group_of >-> group_type.

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
Canonical group_subFinType := Eval hnf in [subFinType of group_type].

 
 

Canonical group_of_subType := Eval hnf in [subType of groupT].
Canonical group_of_eqType := Eval hnf in [eqType of groupT].
Canonical group_of_choiceType := Eval hnf in [choiceType of groupT].
Canonical group_of_countType := Eval hnf in [countType of groupT].
Canonical group_of_subCountType := Eval hnf in [subCountType of groupT].
Canonical group_of_finType := Eval hnf in [finType of groupT].
Canonical group_of_subFinType := Eval hnf in [subFinType of groupT].

Definition group (A : {set gT}) gA : groupT := @Group A gA.

Definition clone_group G :=
  let: Group _ gP := G return {type of Group for G} -> groupT in fun k => k gP.

Lemma group_inj : injective gval.
admit.
Defined.
Lemma groupP (G : groupT) : group_set G.
admit.
Defined.

Lemma congr_group (H K : groupT) : H = K -> H :=: K.
admit.
Defined.

Lemma isgroupP A : reflect (exists G : groupT, A = G) (group_set A).
admit.
Defined.

Lemma group_set_one : group_set 1.
admit.
Defined.

Canonical one_group := group group_set_one.
Canonical set1_group := @group [set 1] group_set_one.

Lemma group_setT (phT : phant gT) : group_set (setTfor phT).
admit.
Defined.

Canonical setT_group phT := group (group_setT phT).

 
Definition generated A := \bigcap_(G : groupT | A \subset G) G.
Definition gcore A B := \bigcap_(x in B) A :^ x.
Definition joing A B := generated (A :|: B).
Definition commutator A B := generated (commg_set A B).
Definition cycle x := generated [set x].
Definition order x := #|cycle x|.

End GroupSetMulProp.

Arguments lcosetP {gT A x y}.
Arguments lcosetsP {gT A B C}.
Arguments rcosetP {gT A x y}.
Arguments rcosetsP {gT A B C}.
Arguments group_setP {gT A}.
Prenex Implicits group_set mulsgP set1gP.

Arguments commutator _ _%g _%g.
Arguments joing _ _%g _%g.
Arguments generated _ _%g.

Notation "{ 'group' gT }" := (group_of (Phant gT))
  (at level 0, format "{ 'group'  gT }") : type_scope.

Notation "[ 'group' 'of' G ]" := (clone_group (@group _ G))
  (at level 0, format "[ 'group'  'of'  G ]") : form_scope.

Bind Scope Group_scope with group_type.
Bind Scope Group_scope with group_of.
Notation "1" := (one_group _) : Group_scope.
Notation "[ 1 gT ]" := (1%G : {group gT}) : Group_scope.
Notation "[ 'set' : gT ]" := (setT_group (Phant gT)) : Group_scope.

 
 
 
 
 
 
Notation gsort gT := (FinGroup.arg_sort (FinGroup.base gT%type)) (only parsing).
Notation "<< A >>"  := (generated A) : group_scope.
Notation "<[ x ] >"  := (cycle x) : group_scope.
Notation "#[ x ]"  := (order x) : group_scope.
Notation "A <*> B" := (joing A B) : group_scope.
Notation "[ ~: A1 , A2 , .. , An ]" :=
  (commutator .. (commutator A1 A2) .. An) : group_scope.

Prenex Implicits order cycle gcore.

Section GroupProp.

Variable gT : finGroupType.
Notation sT := {set gT}.
Implicit Types A B C D : sT.
Implicit Types x y z : gT.
Implicit Types G H K : {group gT}.

Section OneGroup.

Variable G : {group gT}.

Lemma valG : val G = G.
admit.
Defined.

 

Lemma group1 : 1 \in G.
admit.
Defined.
Hint Resolve group1 : core.

Lemma group1_contra x : x \notin G -> x != 1.
admit.
Defined.

Lemma sub1G : [1 gT] \subset G.
admit.
Defined.
Lemma subG1 : (G \subset [1]) = (G :==: 1).
admit.
Defined.

Lemma setI1g : 1 :&: G = 1.
admit.
Defined.
Lemma setIg1 : G :&: 1 = 1.
admit.
Defined.

Lemma subG1_contra H : G \subset H -> G :!=: 1 -> H :!=: 1.
admit.
Defined.

Lemma repr_group : repr G = 1.
admit.
Defined.

Lemma cardG_gt0 : 0 < #|G|.
admit.
Defined.

Lemma indexg_gt0 A : 0 < #|G : A|.
admit.
Defined.

Lemma trivgP : reflect (G :=: 1) (G \subset [1]).
admit.
Defined.

Lemma trivGP : reflect (G = 1%G) (G \subset [1]).
admit.
Defined.

Lemma proper1G : ([1] \proper G) = (G :!=: 1).
admit.
Defined.

Lemma trivgPn : reflect (exists2 x, x \in G & x != 1) (G :!=: 1).
admit.
Defined.

Lemma trivg_card_le1 : (G :==: 1) = (#|G| <= 1).
admit.
Defined.

Lemma trivg_card1 : (G :==: 1) = (#|G| == 1%N).
admit.
Defined.

Lemma cardG_gt1 : (#|G| > 1) = (G :!=: 1).
admit.
Defined.

Lemma card_le1_trivg : #|G| <= 1 -> G :=: 1.
admit.
Defined.

Lemma card1_trivg : #|G| = 1%N -> G :=: 1.
admit.
Defined.

 

Lemma mulG_subl A : A \subset A * G.
admit.
Defined.

Lemma mulG_subr A : A \subset G * A.
admit.
Defined.

Lemma mulGid : G * G = G.
admit.
Defined.

Lemma mulGS A B : (G * A \subset G * B) = (A \subset G * B).
admit.
Defined.

Lemma mulSG A B : (A * G \subset B * G) = (A \subset B * G).
admit.
Defined.

Lemma mul_subG A B : A \subset G -> B \subset G -> A * B \subset G.
admit.
Defined.

 

Lemma groupM x y : x \in G -> y \in G -> x * y \in G.
admit.
Defined.

Lemma groupX x n : x \in G -> x ^+ n \in G.
admit.
Defined.

Lemma groupVr x : x \in G -> x^-1 \in G.
admit.
Defined.

Lemma groupVl x : x^-1 \in G -> x \in G.
admit.
Defined.

Lemma groupV x : (x^-1 \in G) = (x \in G).
admit.
Defined.

Lemma groupMl x y : x \in G -> (x * y \in G) = (y \in G).
admit.
Defined.

Lemma groupMr x y : x \in G -> (y * x \in G) = (y \in G).
admit.
Defined.

Definition in_group := (group1, groupV, (groupMl, groupX)).

Lemma groupJ x y : x \in G -> y \in G -> x ^ y \in G.
admit.
Defined.

Lemma groupJr x y : y \in G -> (x ^ y \in G) = (x \in G).
admit.
Defined.

Lemma groupR x y : x \in G -> y \in G -> [~ x, y] \in G.
admit.
Defined.

Lemma group_prod I r (P : pred I) F :
  (forall i, P i -> F i \in G) -> \prod_(i <- r | P i) F i \in G.
admit.
Defined.

 

Lemma invGid : G^-1 = G.
admit.
Defined.

Lemma inv_subG A : (A^-1 \subset G) = (A \subset G).
admit.
Defined.

Lemma invg_lcoset x : (x *: G)^-1 = G :* x^-1.
admit.
Defined.

Lemma invg_rcoset x : (G :* x)^-1 = x^-1 *: G.
admit.
Defined.

Lemma memV_lcosetV x y : (y^-1 \in x^-1 *: G) = (y \in G :* x).
admit.
Defined.

Lemma memV_rcosetV x y : (y^-1 \in G :* x^-1) = (y \in x *: G).
admit.
Defined.

 

Lemma mulSgGid A x : x \in A -> A \subset G -> A * G = G.
admit.
Defined.

Lemma mulGSgid A x : x \in A -> A \subset G -> G * A = G.
admit.
Defined.

 

Lemma lcoset_refl x : x \in x *: G.
admit.
Defined.

Lemma lcoset_sym x y : (x \in y *: G) = (y \in x *: G).
admit.
Defined.

Lemma lcoset_eqP {x y} : reflect (x *: G = y *: G) (x \in y *: G).
admit.
Defined.

Lemma lcoset_transl x y z : x \in y *: G -> (x \in z *: G) = (y \in z *: G).
admit.
Defined.

Lemma lcoset_trans x y z : x \in y *: G -> y \in z *: G -> x \in z *: G.
admit.
Defined.

Lemma lcoset_id x : x \in G -> x *: G = G.
admit.
Defined.

 

Lemma rcoset_refl x : x \in G :* x.
admit.
Defined.

Lemma rcoset_sym x y : (x \in G :* y) = (y \in G :* x).
admit.
Defined.

Lemma rcoset_eqP {x y} : reflect (G :* x = G :* y) (x \in G :* y).
admit.
Defined.

Lemma rcoset_transl x y z : x \in G :* y -> (x \in G :* z) = (y \in G :* z).
admit.
Defined.

Lemma rcoset_trans x y z : x \in G :* y -> y \in G :* z -> x \in G :* z.
admit.
Defined.

Lemma rcoset_id x : x \in G -> G :* x = G.
admit.
Defined.

 

Variant rcoset_repr_spec x : gT -> Type :=
  RcosetReprSpec g : g \in G -> rcoset_repr_spec x (g * x).

Lemma mem_repr_rcoset x : repr (G :* x) \in G :* x.
admit.
Defined.

 
 
Lemma repr_rcosetP x : rcoset_repr_spec x (repr (G :* x)).
admit.
Defined.

Lemma rcoset_repr x : G :* (repr (G :* x)) = G :* x.
admit.
Defined.

 

Lemma mem_rcosets A x : (G :* x \in rcosets G A) = (x \in G * A).
admit.
Defined.

Lemma mem_lcosets A x : (x *: G \in lcosets G A) = (x \in A * G).
admit.
Defined.

 

Lemma group_setJ A x : group_set (A :^ x) = group_set A.
admit.
Defined.

Lemma group_set_conjG x : group_set (G :^ x).
admit.
Defined.

Canonical conjG_group x := group (group_set_conjG x).

Lemma conjGid : {in G, normalised G}.
admit.
Defined.

Lemma conj_subG x A : x \in G -> A \subset G -> A :^ x \subset G.
admit.
Defined.

 

Lemma class1G : 1 ^: G = 1.
admit.
Defined.

Lemma classes1 : [1] \in classes G.
admit.
Defined.

Lemma classGidl x y : y \in G -> (x ^ y) ^: G = x ^: G.
admit.
Defined.

Lemma classGidr x : {in G, normalised (x ^: G)}.
admit.
Defined.

Lemma class_refl x : x \in x ^: G.
admit.
Defined.
Hint Resolve class_refl : core.

Lemma class_eqP x y : reflect (x ^: G = y ^: G) (x \in y ^: G).
admit.
Defined.

Lemma class_sym x y : (x \in y ^: G) = (y \in x ^: G).
admit.
Defined.

Lemma class_transl x y z : x \in y ^: G -> (x \in z ^: G) = (y \in z ^: G).
admit.
Defined.

Lemma class_trans x y z : x \in y ^: G -> y \in z ^: G -> x \in z ^: G.
admit.
Defined.

Lemma repr_class x : {y | y \in G & repr (x ^: G) = x ^ y}.
admit.
Defined.

Lemma classG_eq1 x : (x ^: G == 1) = (x == 1).
admit.
Defined.

Lemma class_subG x A : x \in G -> A \subset G -> x ^: A \subset G.
admit.
Defined.

Lemma repr_classesP xG :
  reflect (repr xG \in G /\ xG = repr xG ^: G) (xG \in classes G).
admit.
Defined.

Lemma mem_repr_classes xG : xG \in classes G -> repr xG \in xG.
admit.
Defined.

Lemma classes_gt0 : 0 < #|classes G|.
admit.
Defined.

Lemma classes_gt1 : (#|classes G| > 1) = (G :!=: 1).
admit.
Defined.

Lemma mem_class_support A x : x \in A -> x \in class_support A G.
admit.
Defined.

Lemma class_supportGidl A x :
  x \in G -> class_support (A :^ x) G = class_support A G.
admit.
Defined.

Lemma class_supportGidr A : {in G, normalised (class_support A G)}.
admit.
Defined.

Lemma class_support_subG A : A \subset G -> class_support A G \subset G.
admit.
Defined.

Lemma sub_class_support A : A \subset class_support A G.
admit.
Defined.

Lemma class_support_id : class_support G G = G.
admit.
Defined.

Lemma class_supportD1 A : (class_support A G)^# =  cover (A^# :^: G).
admit.
Defined.

 
 
 

Inductive subg_of : predArgType := Subg x & x \in G.
Definition sgval u := let: Subg x _ := u in x.
Canonical subg_subType := Eval hnf in [subType for sgval].
Definition subg_eqMixin := Eval hnf in [eqMixin of subg_of by <:].
Canonical subg_eqType := Eval hnf in EqType subg_of subg_eqMixin.
Definition subg_choiceMixin := [choiceMixin of subg_of by <:].
Canonical subg_choiceType := Eval hnf in ChoiceType subg_of subg_choiceMixin.
Definition subg_countMixin := [countMixin of subg_of by <:].
Canonical subg_countType := Eval hnf in CountType subg_of subg_countMixin.
Canonical subg_subCountType := Eval hnf in [subCountType of subg_of].
Definition subg_finMixin := [finMixin of subg_of by <:].
Canonical subg_finType := Eval hnf in FinType subg_of subg_finMixin.
Canonical subg_subFinType := Eval hnf in [subFinType of subg_of].

Lemma subgP u : sgval u \in G.
admit.
Defined.
Lemma subg_inj : injective sgval.
admit.
Defined.
Lemma congr_subg u v : u = v -> sgval u = sgval v.
admit.
Defined.

Definition subg_one := Subg group1.
Definition subg_inv u := Subg (groupVr (subgP u)).
Definition subg_mul u v := Subg (groupM (subgP u) (subgP v)).
Lemma subg_oneP : left_id subg_one subg_mul.
admit.
Defined.

Lemma subg_invP : left_inverse subg_one subg_inv subg_mul.
admit.
Defined.
Lemma subg_mulP : associative subg_mul.
admit.
Defined.

Definition subFinGroupMixin := FinGroup.Mixin subg_mulP subg_oneP subg_invP.
Canonical subBaseFinGroupType :=
  Eval hnf in BaseFinGroupType subg_of subFinGroupMixin.
Canonical subFinGroupType := FinGroupType subg_invP.

Lemma sgvalM : {in setT &, {morph sgval : x y / x * y}}.
admit.
Defined.
Lemma valgM : {in setT &, {morph val : x y / (x : subg_of) * y >-> x * y}}.
admit.
Defined.

Definition subg : gT -> subg_of := insubd (1 : subg_of).
Lemma subgK x : x \in G -> val (subg x) = x.
admit.
Defined.
Lemma sgvalK : cancel sgval subg.
admit.
Defined.
Lemma subg_default x : (x \in G) = false -> val (subg x) = 1.
admit.
Defined.
Lemma subgM : {in G &, {morph subg : x y / x * y}}.
admit.
Defined.

End OneGroup.

Hint Resolve group1 : core.

Lemma groupD1_inj G H : G^# = H^# -> G :=: H.
admit.
Defined.

Lemma invMG G H : (G * H)^-1 = H * G.
admit.
Defined.

Lemma mulSGid G H : H \subset G -> H * G = G.
admit.
Defined.

Lemma mulGSid G H : H \subset G -> G * H = G.
admit.
Defined.

Lemma mulGidPl G H : reflect (G * H = G) (H \subset G).
admit.
Defined.

Lemma mulGidPr G H : reflect (G * H = H) (G \subset H).
admit.
Defined.

Lemma comm_group_setP G H : reflect (commute G H) (group_set (G * H)).
admit.
Defined.

Lemma card_lcosets G H : #|lcosets H G| = #|G : H|.
admit.
Defined.

 

Lemma group_modl A B G : A \subset G -> A * (B :&: G) = A * B :&: G.
admit.
Defined.

Lemma group_modr A B G : B \subset G -> (G :&: A) * B = G :&: A * B.
admit.
Defined.

End GroupProp.

Hint Extern 0 (is_true (1%g \in _)) => apply: group1 : core.
Hint Extern 0 (is_true (0 < #|_|)) => apply: cardG_gt0 : core.
Hint Extern 0 (is_true (0 < #|_ : _|)) => apply: indexg_gt0 : core.

Notation "G :^ x" := (conjG_group G x) : Group_scope.

Notation "[ 'subg' G ]" := (subg_of G) : type_scope.
Notation "[ 'subg' G ]" := [set: subg_of G] : group_scope.
Notation "[ 'subg' G ]" := [set: subg_of G]%G : Group_scope.

Prenex Implicits subg sgval subg_of.
Bind Scope group_scope with subg_of.
Arguments subgK {gT G}.
Arguments sgvalK {gT G}.
Arguments subg_inj {gT G} [u1 u2] eq_u12 : rename.

Arguments trivgP {gT G}.
Arguments trivGP {gT G}.
Arguments lcoset_eqP {gT G x y}.
Arguments rcoset_eqP {gT G x y}.
Arguments mulGidPl {gT G H}.
Arguments mulGidPr {gT G H}.
Arguments comm_group_setP {gT G H}.
Arguments class_eqP {gT G x y}.
Arguments repr_classesP {gT G xG}.

Section GroupInter.

Variable gT : finGroupType.
Implicit Types A B : {set gT}.
Implicit Types G H : {group gT}.

Section Nary.

End Nary.

End GroupInter.

Section Lagrange.

End Lagrange.

Section GeneratedGroup.

End GeneratedGroup.

Section Cycles.

End Cycles.

Section Normaliser.

Section norm_trans.

End norm_trans.

Section SubAbelian.

End SubAbelian.

End Normaliser.

Section MinMaxGroup.

End MinMaxGroup.

End fingroup.

End mathcomp_DOT_fingroup_DOT_fingroup_WRAPPED.
Module Export mathcomp.
Module Export fingroup.
Module fingroup.
Include mathcomp_DOT_fingroup_DOT_fingroup_WRAPPED.fingroup.
End fingroup.
Module Export perm.
Import mathcomp.ssreflect.ssreflect.
Import mathcomp.ssreflect.ssrfun.
Import mathcomp.ssreflect.ssrbool.
Import mathcomp.ssreflect.eqtype.
Import mathcomp.ssreflect.ssrnat.
Import mathcomp.ssreflect.seq.
Import mathcomp.ssreflect.choice.
Import mathcomp.ssreflect.fintype.
Import mathcomp.ssreflect.finfun.
Import mathcomp.ssreflect.finset.
Import mathcomp.fingroup.fingroup.

Set Implicit Arguments.
Unset Strict Implicit.

Import GroupScope.

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
admit.
Defined.

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
admit.
Defined.

Lemma perm_onto s : codom s =i predT.
admit.
Defined.

Definition perm_one := perm (@inj_id T).

Lemma perm_invK s : cancel (fun x => iinv (perm_onto s x)) s.
admit.
Defined.

Definition perm_inv s := perm (can_inj (perm_invK s)).

Definition perm_mul s t := perm (inj_comp (@perm_inj t) (@perm_inj s)).

Lemma perm_oneP : left_id perm_one perm_mul.
admit.
Defined.

Lemma perm_invP : left_inverse perm_one perm_inv perm_mul.
admit.
Defined.

Lemma perm_mulP : associative perm_mul.
admit.
Defined.

Definition perm_of_baseFinGroupMixin : FinGroup.mixin_of (perm_type T) :=
  FinGroup.Mixin perm_mulP perm_oneP perm_invP.
Canonical perm_baseFinGroupType :=
  Eval hnf in BaseFinGroupType (perm_type T) perm_of_baseFinGroupMixin.
Canonical perm_finGroupType := @FinGroupType perm_baseFinGroupType perm_invP.

Lemma tperm_proof x y : involutive [fun z => z with x |-> y, y |-> x].
admit.
Defined.

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
Import mathcomp.ssreflect.ssrfun.
Import mathcomp.ssreflect.ssrnat.
Import mathcomp.ssreflect.div.
Import mathcomp.ssreflect.fintype.
Import mathcomp.algebra.ssralg.

Section ZpDef.

Variable p' : nat.
Local Notation p := p'.+1.

Implicit Types x y z : 'I_p.

Definition inZp i := Ordinal (ltn_pmod i (ltn0Sn p')).

Definition Zp0 : 'I_p := ord0.
Definition Zp_opp x := inZp (p - x).
Definition Zp_add x y := inZp (x + y).

Lemma Zp_add0z : left_id Zp0 Zp_add.
admit.
Defined.

Lemma Zp_addNz : left_inverse Zp0 Zp_opp Zp_add.
admit.
Defined.

Lemma Zp_addA : associative Zp_add.
admit.
Defined.

Lemma Zp_addC : commutative Zp_add.
admit.
Defined.

Definition Zp_zmodMixin := ZmodMixin Zp_addA Zp_addC Zp_add0z Zp_addNz.
Canonical Zp_zmodType := Eval hnf in ZmodType 'I_p Zp_zmodMixin.

End ZpDef.
Import mathcomp.ssreflect.ssreflect.
Import mathcomp.ssreflect.ssrbool.
Import mathcomp.ssreflect.eqtype.
Import mathcomp.ssreflect.seq.
Import mathcomp.ssreflect.choice.
Import mathcomp.ssreflect.finfun.

Set Implicit Arguments.
Unset Strict Implicit.
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
admit.
Defined.
Definition const_mx m n a : 'M[R]_(m, n) := \matrix[const_mx_key]_(i, j) a.

Section FixedDim.

Variables m n : nat.
Implicit Type A : 'M[R]_(m, n).

Definition castmx m' n' (eq_mn : (m = m') * (n = n')) A : 'M_(m', n') :=
  let: erefl in _ = m' := eq_mn.1 return 'M_(m', n') in
  let: erefl in _ = n' := eq_mn.2 return 'M_(m, n') in A.

Fact row_perm_key : unit.
admit.
Defined.
Definition row_perm (s : 'S_m) A := \matrix[row_perm_key]_(i, j) A (s i) j.
Fact col_perm_key : unit.
admit.
Defined.
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
admit.
Defined.

Definition mxvec_index (i : 'I_m) (j : 'I_n) :=
  cast_ord mxvec_cast (enum_rank (i, j)).

Definition mxvec (A : 'M[R]_(m, n)) :=
  castmx (erefl _, mxvec_cast) (\row_k A (enum_val k).1 (enum_val k).2).

Fact vec_mx_key : unit.
admit.
Defined.
Definition vec_mx (u : 'rV[R]_(m * n)) :=
  \matrix[vec_mx_key]_(i, j) u 0 (mxvec_index i j).

End VecMatrix.

End MatrixStructural.

Arguments const_mx {R m n}.

Section MapMatrix.

Variables (aT rT : Type) (f : aT -> rT).

Fact map_mx_key : unit.
admit.
Defined.
Definition map_mx m n (A : 'M_(m, n)) := \matrix[map_mx_key]_(i, j) f (A i j).

End MapMatrix.

Section MatrixZmodule.

Variable V : zmodType.

Section FixedDim.

Variables m n : nat.
Implicit Types A B : 'M[V]_(m, n).

Fact oppmx_key : unit.
admit.
Defined.
Fact addmx_key : unit.
admit.
Defined.
Definition oppmx A := \matrix[oppmx_key]_(i, j) (- A i j).
Definition addmx A B := \matrix[addmx_key]_(i, j) (A i j + B i j).

Lemma addmxA : associative addmx.
admit.
Defined.

Lemma addmxC : commutative addmx.
admit.
Defined.

Lemma add0mx : left_id (const_mx 0) addmx.
admit.
Defined.

Lemma addNmx : left_inverse (const_mx 0) oppmx addmx.
admit.
Defined.

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
admit.
Defined.
Definition scalemx x A := \matrix[scalemx_key]_(i, j) (x * A i j).

Local Notation "x *m: A" := (scalemx x A) (at level 40) : ring_scope.

Lemma scale1mx A : 1 *m: A = A.
admit.
Defined.

Lemma scalemxDl A x y : (x + y) *m: A = x *m: A + y *m: A.
admit.
Defined.

Lemma scalemxDr x A B : x *m: (A + B) = x *m: A + x *m: B.
admit.
Defined.

Lemma scalemxA x y A : x *m: (y *m: A) = (x * y) *m: A.
admit.
Defined.

Definition matrix_lmodMixin :=
  LmodMixin scalemxA scale1mx scalemxDr scalemxDl.

Canonical matrix_lmodType :=
  Eval hnf in LmodType R 'M[R]_(m, n) matrix_lmodMixin.

End RingModule.

Section ScalarMx.

Variable n : nat.

Fact scalar_mx_key : unit.
admit.
Defined.
Definition scalar_mx x : 'M[R]_n :=
  \matrix[scalar_mx_key]_(i , j) (x *+ (i == j)).

End ScalarMx.

Notation "x %:M" := (scalar_mx _ x) : ring_scope.

Fact mulmx_key : unit.
admit.
Defined.
Definition mulmx {m n p} (A : 'M_(m, n)) (B : 'M_(n, p)) : 'M[R]_(m, p) :=
  \matrix[mulmx_key]_(i, k) \sum_j (A i j * B j k).

Local Notation "A *m B" := (mulmx A B) : ring_scope.

Lemma mulmxA m n p q (A : 'M_(m, n)) (B : 'M_(n, p)) (C : 'M_(p, q)) :
  A *m (B *m C) = A *m B *m C.
admit.
Defined.

Lemma mulmxDl m n p (A1 A2 : 'M_(m, n)) (B : 'M_(n, p)) :
  (A1 + A2) *m B = A1 *m B + A2 *m B.
admit.
Defined.

Lemma mulmxDr m n p (A : 'M_(m, n)) (B1 B2 : 'M_(n, p)) :
  A *m (B1 + B2) = A *m B1 + A *m B2.
admit.
Defined.

Lemma mul1mx m n (A : 'M_(m, n)) : 1%:M *m A = A.
admit.
Defined.

Lemma mulmx1 m n (A : 'M_(m, n)) : A *m 1%:M = A.
admit.
Defined.

Fact pid_mx_key : unit.
admit.
Defined.
Definition pid_mx {m n} r : 'M[R]_(m, n) :=
  \matrix[pid_mx_key]_(i, j) ((i == j :> nat) && (i < r))%:R.

Definition copid_mx {n} r : 'M_n := 1%:M - pid_mx r.

Section Trace.

Variable n : nat.

Definition mxtrace (A : 'M[R]_n) := \sum_i A i i.

End Trace.

Section MatrixRing.

Variable n' : nat.
Local Notation n := n'.+1.

Lemma matrix_nonzero1 : 1%:M != 0 :> 'M_n.
admit.
Defined.

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
admit.
Defined.
Definition adjugate n (A : 'M_n) := \matrix[adjugate_key]_(i, j) cofactor A j i.

End MatrixAlgebra.
Arguments scalar_mx {R n}.
Arguments pid_mx {R m n}.
Arguments copid_mx {R n}.
Prenex Implicits mulmx mxtrace determinant cofactor adjugate.

Notation "a %:M" := (scalar_mx a) : ring_scope.
Notation "A *m B" := (mulmx A B) : ring_scope.
Notation "'\det' A" := (determinant A) : ring_scope.
Notation "'\adj' A" := (adjugate A) : ring_scope.

Section CommMx.

Context {R : ringType} {n : nat}.
Implicit Types (f g p : 'M[R]_n) (fs : seq 'M[R]_n) (d : 'rV[R]_n) (I : Type).

Definition comm_mx  f g : Prop := f *m g =  g *m f.

End CommMx.

Section ComMatrix.

Variable R : comRingType.

Lemma comm_mx_scalar n a (A : 'M[R]_n) : comm_mx A a%:M.
admit.
Defined.

End ComMatrix.
Arguments comm_mx_scalar {R n}.

Section MatrixInv.

Variables R : comUnitRingType.

Section Defs.

Variable n : nat.

Definition unitmx : pred 'M[R]_n := fun A => \det A \is a GRing.unit.
Definition invmx A := if A \in unitmx then (\det A)^-1 *: \adj A else A.

Lemma mulVmx : {in unitmx, left_inverse 1%:M invmx mulmx}.
admit.
Defined.

Lemma mulmxV : {in unitmx, right_inverse 1%:M invmx mulmx}.
admit.
Defined.

Lemma intro_unitmx A B : B *m A = 1%:M /\ A *m B = 1%:M -> unitmx A.
admit.
Defined.

Lemma invmx_out : {in [predC unitmx], invmx =1 id}.
admit.
Defined.

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
admit.
Defined.

Let LUr := locked_with Gaussian_elimination_key (@Gaussian_elimination) m n A.

Definition col_ebase := LUr.1.1.
Definition row_ebase := LUr.1.2.
Definition mxrank := if [|| m == 0 | n == 0]%N then 0%N else LUr.2.
Definition cokermx : 'M_n := invmx row_ebase *m copid_mx mxrank.

Definition pinvmx : 'M_(n, m) :=
  invmx row_ebase *m pid_mx mxrank *m invmx col_ebase.

End Defs.
Local Notation "\rank A" := (mxrank A) : nat_scope.

Definition submx_def := idfun (fun m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)) =>
  A *m cokermx B == 0).
Fact submx_key : unit.
admit.
Defined.
Definition submx := locked_with submx_key submx_def.

Lemma mxrank_eq0 m n (A : 'M_(m, n)) : (\rank A == 0%N) = (A == 0).
admit.
Defined.

End RowSpaceTheory.
Notation "\rank A" := (mxrank A) : nat_scope.
Notation "A <= B" := (submx A B) : matrix_set_scope.

Import GRing.Theory.
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
Canonical poly_eqType := Eval hnf in [eqType of {poly R}].

Definition lead_coef p := p`_(size p).-1.

Definition poly_nil := @Polynomial R [::] (oner_neq0 R).
Definition polyC c : {poly R} := insubd poly_nil [:: c].

Local Notation "c %:P" := (polyC c).

Definition cons_poly c p : {poly R} :=
  if p is Polynomial ((_ :: _) as s) ns then
    @Polynomial R (c :: s) ns
  else c%:P.

Definition Poly := foldr cons_poly 0%:P.

Definition poly_expanded_def n E := Poly (mkseq E n).
Fact poly_key : unit.
admit.
Defined.
Definition poly := locked_with poly_key poly_expanded_def.
Local Notation "\poly_ ( i < n ) E" := (poly n (fun i : nat => E)).

Definition add_poly_def p q := \poly_(i < maxn (size p) (size q)) (p`_i + q`_i).
Fact add_poly_key : unit.
admit.
Defined.
Definition add_poly := locked_with add_poly_key add_poly_def.

Definition opp_poly_def p := \poly_(i < size p) - p`_i.
Fact opp_poly_key : unit.
admit.
Defined.
Definition opp_poly := locked_with opp_poly_key opp_poly_def.

Fact add_polyA : associative add_poly.
admit.
Defined.

Fact add_polyC : commutative add_poly.
admit.
Defined.

Fact add_poly0 : left_id 0%:P add_poly.
admit.
Defined.

Fact add_polyN : left_inverse 0%:P opp_poly add_poly.
admit.
Defined.

Definition poly_zmodMixin :=
  ZmodMixin add_polyA add_polyC add_poly0 add_polyN.

Canonical poly_zmodType := Eval hnf in ZmodType {poly R} poly_zmodMixin.

Definition mul_poly_def p q :=
  \poly_(i < (size p + size q).-1) (\sum_(j < i.+1) p`_j * q`_(i - j)).
Fact mul_poly_key : unit.
admit.
Defined.
Definition mul_poly := locked_with mul_poly_key mul_poly_def.

Fact mul_polyA : associative mul_poly.
admit.
Defined.

Fact mul_1poly : left_id 1%:P mul_poly.
admit.
Defined.

Fact mul_poly1 : right_id 1%:P mul_poly.
admit.
Defined.

Fact mul_polyDl : left_distributive mul_poly +%R.
admit.
Defined.

Fact mul_polyDr : right_distributive mul_poly +%R.
admit.
Defined.

Fact poly1_neq0 : 1%:P != 0 :> {poly R}.
admit.
Defined.

Definition poly_ringMixin :=
  RingMixin mul_polyA mul_1poly mul_poly1 mul_polyDl mul_polyDr poly1_neq0.

Canonical poly_ringType := Eval hnf in RingType {poly R} poly_ringMixin.

Definition scale_poly_def a (p : {poly R}) := \poly_(i < size p) (a * p`_i).
Fact scale_poly_key : unit.
admit.
Defined.
Definition scale_poly := locked_with scale_poly_key scale_poly_def.

Fact scale_polyA a b p : scale_poly a (scale_poly b p) = scale_poly (a * b) p.
admit.
Defined.

Fact scale_1poly : left_id 1 scale_poly.
admit.
Defined.

Fact scale_polyDr a : {morph scale_poly a : p q / p + q}.
admit.
Defined.

Fact scale_polyDl p : {morph scale_poly^~ p : a b / a + b}.
admit.
Defined.

Definition poly_lmodMixin :=
  LmodMixin scale_polyA scale_1poly scale_polyDr scale_polyDl.

Canonical poly_lmodType :=
  Eval hnf in LmodType R {poly R} poly_lmodMixin.

Definition polyX_def := Poly [:: 0; 1].
Fact polyX_key : unit.
admit.
Defined.
Definition polyX : {poly R} := locked_with polyX_key polyX_def.
Fixpoint horner_rec s x := if s is a :: s' then horner_rec s' x * x + a else 0.
Definition horner p := horner_rec p.

End PolynomialTheory.
Notation "\poly_ ( i < n ) E" := (poly n (fun i => E)) : ring_scope.
Notation "c %:P" := (polyC c) : ring_scope.
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

Definition redivp_rec (q : {poly R}) :=
  let sq := size q in
  let cq := lead_coef q in
   fix loop (k : nat) (qq r : {poly R})(n : nat) {struct n} :=
    if size r < sq then (k, qq, r) else
    let m := (lead_coef r) *: 'X^(size r - sq) in
    let qq1 := qq * cq%:P + m in
    let r1 := r * cq%:P - m * q in
       if n is n1.+1 then loop k.+1 qq1 r1 n1 else (k.+1, qq1, r1).

Definition redivp_expanded_def p q :=
   if q == 0 then (0%N, 0, p) else redivp_rec q 0 0 p (size p).
Fact redivp_key : unit.
admit.
Defined.
Definition redivp : {poly R} -> {poly R} -> nat * {poly R} * {poly R} :=
  locked_with redivp_key redivp_expanded_def.

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
admit.
Defined.
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
admit.
Defined.
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
admit.
Defined.

Lemma eval_mxrank e r m n (A : 'M_(m, n)) :
  qf_eval e (mxrank_form r A) = (\rank (eval_mx e A) == r).
admit.
Defined.

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
admit.
Defined.

End Env.

End MatrixFormula.
Import mathcomp.ssreflect.finset.
Import mathcomp.fingroup.fingroup.
Unset Printing Implicit Defensive.

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
admit.
Defined.

Lemma gen_addC : commutative genD.
admit.
Defined.

Lemma gen_add0r : left_id gen0 genD.
admit.
Defined.

Lemma gen_addNr : left_inverse gen0 genN genD.
admit.
Defined.

Definition gen_zmodMixin := ZmodMixin gen_addA gen_addC gen_add0r gen_addNr.
Canonical gen_zmodType := Eval hnf in ZmodType FA gen_zmodMixin.

Definition pval (x : FA) := rVpoly (val x).

Definition mxval (x : FA) := horner_mx A (pval x).

Definition gen1 := inFA (poly_rV 1).
Definition genM x y := inFA (poly_rV (pval x * pval y %% pA)).
Definition genV x := inFA (poly_rV (mx_inv_horner A (mxval x)^-1)).

Lemma gen_mulA : associative genM.
admit.
Defined.

Lemma gen_mulC : commutative genM.
admit.
Defined.

Lemma gen_mul1r : left_id gen1 genM.
admit.
Defined.

Lemma gen_mulDr : left_distributive genM +%R.
admit.
Defined.

Lemma gen_ntriv : gen1 != 0.
admit.
Defined.

Definition gen_ringMixin :=
  ComRingMixin gen_mulA gen_mulC gen_mul1r gen_mulDr gen_ntriv.
Canonical gen_ringType := Eval hnf in RingType FA gen_ringMixin.
Canonical gen_comRingType := Eval hnf in ComRingType FA gen_mulC.

Lemma gen_mulVr : GRing.Field.axiom genV.
admit.
Defined.

Lemma gen_invr0 : genV 0 = 0.
admit.
Defined.

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
admit.
Defined.

Lemma eval_gen_term e t :
  GRing.rterm t -> eval_mx (gen_env e) (gen_term t) = val (GRing.eval e t).
admit.
Defined.

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
