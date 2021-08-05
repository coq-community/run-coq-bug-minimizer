(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "-projection-no-head-constant" "-w" "-redundant-canonical-projection" "-w" "-notation-overridden" "-w" "+duplicate-clear" "-w" "-ambiguous-paths" "-w" "+non-primitive-record" "-w" "+undeclared-scope" "-w" "-deprecated-hint-without-locality" "-w" "-deprecated-ident-entry" "-w" "-deprecated-native-compiler-option" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/mathcomp/mathcomp" "mathcomp" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-I" "/github/workspace/builds/coq/coq-failing/_build_ci/mathcomp/mathcomp" "-top" "bug_01" "-native-compiler" "ondemand") -*- *)
(* File reduced by coq-bug-finder from original input, then from 5975 lines to 4644 lines, then from 4288 lines to 258 lines, then from 311 lines to 2273 lines, then from 2277 lines to 373 lines, then from 424 lines to 3656 lines, then from 3659 lines to 414 lines, then from 464 lines to 3258 lines, then from 3262 lines to 611 lines, then from 661 lines to 3802 lines, then from 3806 lines to 2026 lines, then from 1863 lines to 645 lines, then from 694 lines to 5235 lines, then from 5239 lines to 1107 lines, then from 1154 lines to 1545 lines, then from 1549 lines to 1575 lines, then from 1518 lines to 1142 lines, then from 1180 lines to 1911 lines, then from 1915 lines to 1273 lines, then from 1309 lines to 4393 lines, then from 4397 lines to 1439 lines, then from 1475 lines to 8096 lines, then from 8099 lines to 8259 lines *)
(* coqc version 8.15+alpha compiled with OCaml 4.12.0
   coqtop version 8.15+alpha *)
Declare ML Module "ltac_plugin".
Module Export AdmitTactic.
Module Import LocalFalse.
Inductive False := .
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
Module mathcomp_DOT_algebra_DOT_ssralg_WRAPPED.
Module ssralg.
 
 
Import mathcomp.ssreflect.ssreflect mathcomp.ssreflect.ssrfun mathcomp.ssreflect.ssrbool mathcomp.ssreflect.eqtype mathcomp.ssreflect.ssrnat mathcomp.ssreflect.div mathcomp.ssreflect.seq.
Import mathcomp.ssreflect.choice mathcomp.ssreflect.fintype mathcomp.ssreflect.finfun mathcomp.ssreflect.bigop mathcomp.ssreflect.prime mathcomp.ssreflect.binomial.

 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope ring_scope.
Declare Scope term_scope.
Declare Scope linear_ring_scope.

Reserved Notation "+%R" (at level 0).
Reserved Notation "-%R" (at level 0).
Reserved Notation "*%R" (at level 0, format " *%R").
Reserved Notation "*:%R" (at level 0, format " *:%R").
Reserved Notation "n %:R" (at level 2, left associativity, format "n %:R").
Reserved Notation "k %:A" (at level 2, left associativity, format "k %:A").
Reserved Notation "[ 'char' F ]" (at level 0, format "[ 'char'  F ]").

Reserved Notation "x %:T" (at level 2, left associativity, format "x %:T").
Reserved Notation "''X_' i" (at level 8, i at level 2, format "''X_' i").
 
 
Reserved Notation "''exists' ''X_' i , f"
  (at level 199, i at level 2, right associativity,
   format "'[hv' ''exists'  ''X_' i , '/ '  f ']'").
Reserved Notation "''forall' ''X_' i , f"
  (at level 199, i at level 2, right associativity,
   format "'[hv' ''forall'  ''X_' i , '/ '  f ']'").

Reserved Notation "x ^f" (at level 2, left associativity, format "x ^f").

Reserved Notation "\0" (at level 0).
Reserved Notation "f \+ g" (at level 50, left associativity).
Reserved Notation "f \- g" (at level 50, left associativity).
Reserved Notation "a \*o f" (at level 40).
Reserved Notation "a \o* f" (at level 40).
Reserved Notation "a \*: f" (at level 40).

Delimit Scope ring_scope with R.
Delimit Scope term_scope with T.
Local Open Scope ring_scope.

Module Import GRing.

Import Monoid.Theory.

Module Zmodule.

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

Set Primitive Projections.
Record class_of T := Class { base : Choice.class_of T; mixin : mixin_of T }.
Unset Primitive Projections.
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

Module Exports.
Coercion base : class_of >-> Choice.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Notation zmodType := type.
Notation ZmodType T m := (@pack T m _ _ id).
Notation ZmodMixin := Mixin.
Notation "[ 'zmodType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'zmodType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'zmodType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'zmodType'  'of'  T ]") : form_scope.
End Exports.

End Zmodule.
Import Zmodule.Exports.

Definition zero V := Zmodule.zero (Zmodule.class V).
Definition opp V := Zmodule.opp (Zmodule.class V).
Definition add V := Zmodule.add (Zmodule.class V).

Local Notation "0" := (zero _) : ring_scope.
Local Notation "-%R" := (@opp _) : fun_scope.
Local Notation "- x" := (opp x) : ring_scope.
Local Notation "+%R" := (@add _) : fun_scope.
Local Notation "x + y" := (add x y) : ring_scope.
Local Notation "x - y" := (x + - y) : ring_scope.

Definition natmul V x n := nosimpl iterop _ n +%R x (zero V).

Local Notation "x *+ n" := (natmul x n) : ring_scope.
Local Notation "x *- n" := (- (x *+ n)) : ring_scope.

Local Notation "\sum_ ( i <- r | P ) F" := (\big[+%R/0]_(i <- r | P) F).
Local Notation "\sum_ ( m <= i < n ) F" := (\big[+%R/0]_(m <= i < n) F).
Local Notation "\sum_ ( i < n ) F" := (\big[+%R/0]_(i < n) F).
Local Notation "\sum_ ( i 'in' A ) F" := (\big[+%R/0]_(i in A) F).

Local Notation "s `_ i" := (nth 0 s i) : ring_scope.

Section ZmoduleTheory.

Variable V : zmodType.
Implicit Types x y : V.

Lemma addrA : @associative V +%R.
Proof.
by case V => T [? []].
Qed.
Lemma addrC : @commutative V V +%R.
Proof.
by case V => T [? []].
Qed.
Lemma add0r : @left_id V V 0 +%R.
Proof.
by case V => T [? []].
Qed.
Lemma addNr : @left_inverse V V V 0 -%R +%R.
Proof.
by case V => T [? []].
Qed.

Lemma addr0 : @right_id V V 0 +%R.
Proof.
by move=> x; rewrite addrC add0r.
Qed.
Lemma addrN : @right_inverse V V V 0 -%R +%R.
Proof.
by move=> x; rewrite addrC addNr.
Qed.
Definition subrr := addrN.

Canonical add_monoid := Monoid.Law addrA add0r addr0.
Canonical add_comoid := Monoid.ComLaw addrC.

Lemma addrCA : @left_commutative V V +%R.
Proof.
exact: mulmCA.
Qed.
Lemma addrAC : @right_commutative V V +%R.
Proof.
exact: mulmAC.
Qed.
Lemma addrACA : @interchange V +%R +%R.
Proof.
exact: mulmACA.
Qed.

Lemma addKr : @left_loop V V -%R +%R.
Proof.
by move=> x y; rewrite addrA addNr add0r.
Qed.
Lemma addNKr : @rev_left_loop V V -%R +%R.
Proof.
by move=> x y; rewrite addrA addrN add0r.
Qed.
Lemma addrK : @right_loop V V -%R +%R.
Proof.
by move=> x y; rewrite -addrA addrN addr0.
Qed.
Lemma addrNK : @rev_right_loop V V -%R +%R.
Proof.
by move=> x y; rewrite -addrA addNr addr0.
Qed.
Definition subrK := addrNK.
Lemma subKr x : involutive (fun y => x - y).
Proof.
by move=> y; apply: (canLR (addrK _)); rewrite addrC subrK.
Qed.
Lemma addrI : @right_injective V V V +%R.
Proof.
by move=> x; apply: can_inj (addKr x).
Qed.
Lemma addIr : @left_injective V V V +%R.
Proof.
by move=> y; apply: can_inj (addrK y).
Qed.
Lemma subrI : right_injective (fun x y => x - y).
Proof.
by move=> x; apply: can_inj (subKr x).
Qed.
Lemma subIr : left_injective (fun x y => x - y).
Proof.
by move=> y; apply: addIr.
Qed.
Lemma opprK : @involutive V -%R.
Proof.
by move=> x; apply: (@subIr x); rewrite addNr addrN.
Qed.
Lemma oppr_inj : @injective V V -%R.
Proof.
exact: inv_inj opprK.
Qed.
Lemma oppr0 : -0 = 0 :> V.
Proof.
by rewrite -[-0]add0r subrr.
Qed.
Lemma oppr_eq0 x : (- x == 0) = (x == 0).
Proof.
by rewrite (inv_eq opprK) oppr0.
Qed.

Lemma subr0 x : x - 0 = x.
Proof.
by rewrite oppr0 addr0.
Qed.
Lemma sub0r x : 0 - x = - x.
Proof.
by rewrite add0r.
Qed.

Lemma opprB x y : - (x - y) = y - x.
Proof.
by apply: (canRL (addrK x)); rewrite addrC subKr.
Qed.

Lemma opprD : {morph -%R: x y / x + y : V}.
Proof.
by move=> x y; rewrite -[y in LHS]opprK opprB addrC.
Qed.

Lemma addrKA z x y : (x + z) - (z + y) = x - y.
Proof.
by rewrite opprD addrA addrK.
Qed.

Lemma subrKA z x y : (x - z) + (z + y) = x + y.
Proof.
by rewrite addrA addrNK.
Qed.

Lemma addr0_eq x y : x + y = 0 -> - x = y.
Proof.
by rewrite -[-x]addr0 => <-; rewrite addKr.
Qed.

Lemma subr0_eq x y : x - y = 0 -> x = y.
Proof.
by move/addr0_eq/oppr_inj.
Qed.

Lemma subr_eq x y z : (x - z == y) = (x == y + z).
Proof.
exact: can2_eq (subrK z) (addrK z) x y.
Qed.

Lemma subr_eq0 x y : (x - y == 0) = (x == y).
Proof.
by rewrite subr_eq add0r.
Qed.

Lemma addr_eq0 x y : (x + y == 0) = (x == - y).
Proof.
by rewrite -[y in LHS]opprK subr_eq0.
Qed.

Lemma eqr_opp x y : (- x == - y) = (x == y).
Proof.
exact: can_eq opprK x y.
Qed.

Lemma eqr_oppLR x y : (- x == y) = (x == - y).
Proof.
exact: inv_eq opprK x y.
Qed.

Lemma mulr0n x : x *+ 0 = 0.
Proof.
by [].
Qed.
Lemma mulr1n x : x *+ 1 = x.
Proof.
by [].
Qed.
Lemma mulr2n x : x *+ 2 = x + x.
Proof.
by [].
Qed.

Lemma mulrS x n : x *+ n.+1 = x + x *+ n.
Proof.
by case: n => //=; rewrite addr0.
Qed.

Lemma mulrSr x n : x *+ n.+1 = x *+ n + x.
Proof.
by rewrite addrC mulrS.
Qed.

Lemma mulrb x (b : bool) : x *+ b = (if b then x else 0).
Proof.
by case: b.
Qed.

Lemma mul0rn n : 0 *+ n = 0 :> V.
Proof.
by elim: n => // n IHn; rewrite mulrS add0r.
Qed.

Lemma mulNrn x n : (- x) *+ n = x *- n.
Proof.
by elim: n => [|n IHn]; rewrite ?oppr0 // !mulrS opprD IHn.
Qed.

Lemma mulrnDl n : {morph (fun x => x *+ n) : x y / x + y}.
Proof.
move=> x y; elim: n => [|n IHn]; rewrite ?addr0 // !mulrS.
by rewrite addrCA -!addrA -IHn -addrCA.
Qed.

Lemma mulrnDr x m n : x *+ (m + n) = x *+ m + x *+ n.
Proof.
elim: m => [|m IHm]; first by rewrite add0r.
by rewrite !mulrS IHm addrA.
Qed.

Lemma mulrnBl n : {morph (fun x => x *+ n) : x y / x - y}.
Proof.
move=> x y; elim: n => [|n IHn]; rewrite ?subr0 // !mulrS -!addrA; congr(_ + _).
by rewrite addrC IHn -!addrA opprD [_ - y]addrC.
Qed.

Lemma mulrnBr x m n : n <= m -> x *+ (m - n) = x *+ m - x *+ n.
Proof.
elim: m n => [|m IHm] [|n le_n_m]; rewrite ?subr0 // {}IHm //.
by rewrite mulrSr mulrS opprD addrA addrK.
Qed.

Lemma mulrnA x m n : x *+ (m * n) = x *+ m *+ n.
Proof.
by rewrite mulnC; elim: n => //= n IHn; rewrite mulrS mulrnDr IHn.
Qed.

Lemma mulrnAC x m n : x *+ m *+ n = x *+ n *+ m.
Proof.
by rewrite -!mulrnA mulnC.
Qed.

Lemma iter_addr n x y : iter n (+%R x) y = x *+ n + y.
Proof.
by elim: n => [|n ih]; rewrite ?add0r //= ih mulrS addrA.
Qed.

Lemma iter_addr_0 n x : iter n (+%R x) 0 = x *+ n.
Proof.
by rewrite iter_addr addr0.
Qed.

Lemma sumrN I r P (F : I -> V) :
  (\sum_(i <- r | P i) - F i = - (\sum_(i <- r | P i) F i)).
Proof.
by rewrite (big_morph _ opprD oppr0).
Qed.

Lemma sumrB I r (P : pred I) (F1 F2 : I -> V) :
  \sum_(i <- r | P i) (F1 i - F2 i)
     = \sum_(i <- r | P i) F1 i - \sum_(i <- r | P i) F2 i.
Proof.
by rewrite -sumrN -big_split /=.
Qed.

Lemma sumrMnl I r P (F : I -> V) n :
  \sum_(i <- r | P i) F i *+ n = (\sum_(i <- r | P i) F i) *+ n.
Proof.
by rewrite (big_morph _ (mulrnDl n) (mul0rn _)).
Qed.

Lemma sumrMnr x I r P (F : I -> nat) :
  \sum_(i <- r | P i) x *+ F i = x *+ (\sum_(i <- r | P i) F i).
Proof.
by rewrite (big_morph _ (mulrnDr x) (erefl _)).
Qed.

Lemma sumr_const (I : finType) (A : pred I) x : \sum_(i in A) x = x *+ #|A|.
Proof.
by rewrite big_const -iteropE.
Qed.

Lemma sumr_const_nat m n x : \sum_(n <= i < m) x = x *+ (m - n).
Proof.
by rewrite big_const_nat iter_addr_0.
Qed.

Lemma telescope_sumr n m (f : nat -> V) : n <= m ->
  \sum_(n <= k < m) (f k.+1 - f k) = f m - f n.
Proof.
rewrite leq_eqVlt => /predU1P[-> | ]; first by rewrite subrr big_geq.
case: m => // m lenm; rewrite sumrB big_nat_recr // big_nat_recl //=.
by rewrite addrC opprD addrA subrK addrC.
Qed.

Section ClosedPredicates.

Variable S : {pred V}.

Definition addr_closed := 0 \in S /\ {in S &, forall u v, u + v \in S}.
Definition oppr_closed := {in S, forall u, - u \in S}.
Definition subr_2closed := {in S &, forall u v, u - v \in S}.
Definition zmod_closed := 0 \in S /\ subr_2closed.

Lemma zmod_closedN : zmod_closed -> oppr_closed.
Proof.
by case=> S0 SB y Sy; rewrite -sub0r !SB.
Qed.

Lemma zmod_closedD : zmod_closed -> addr_closed.
Proof.
by case=> S0 SB; split=> // y z Sy Sz; rewrite -[z]opprK -[- z]sub0r !SB.
Qed.

End ClosedPredicates.

End ZmoduleTheory.

Arguments addrI {V} y [x1 x2].
Arguments addIr {V} x [x1 x2].
Arguments opprK {V}.
Arguments oppr_inj {V} [x1 x2].

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

Set Primitive Projections.
Record class_of (R : Type) : Type := Class {
  base : Zmodule.class_of R;
  mixin : mixin_of (Zmodule.Pack base)
}.
Unset Primitive Projections.
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
Definition choiceType := @Choice.Pack cT class.
Definition zmodType := @Zmodule.Pack cT class.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Zmodule.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> Zmodule.type.
Canonical zmodType.
Notation ringType := type.
Notation RingType T m := (@pack T _ m _ _ id _ id).
Notation RingMixin := Mixin.
Notation "[ 'ringType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'ringType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'ringType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'ringType'  'of'  T ]") : form_scope.
End Exports.

End Ring.
Import Ring.Exports.

Definition one (R : ringType) : R := Ring.one (Ring.class R).
Definition mul (R : ringType) : R -> R -> R := Ring.mul (Ring.class R).
Definition exp R x n := nosimpl iterop _ n (@mul R) x (one R).
Notation sign R b := (exp (- one R) (nat_of_bool b)) (only parsing).
Definition comm R x y := @mul R x y = mul y x.
Definition lreg R x := injective (@mul R x).
Definition rreg R x := injective ((@mul R)^~ x).

Local Notation "1" := (one _) : ring_scope.
Local Notation "- 1" := (- (1)) : ring_scope.
Local Notation "n %:R" := (1 *+ n) : ring_scope.
Local Notation "*%R" := (@mul _) : fun_scope.
Local Notation "x * y" := (mul x y) : ring_scope.
Local Notation "x ^+ n" := (exp x n) : ring_scope.

Local Notation "\prod_ ( i <- r | P ) F" := (\big[*%R/1]_(i <- r | P) F).
Local Notation "\prod_ ( i | P ) F" := (\big[*%R/1]_(i | P) F).
Local Notation "\prod_ ( i 'in' A ) F" := (\big[*%R/1]_(i in A) F).
Local Notation "\prod_ ( m <= i < n ) F" := (\big[*%R/1%R]_(m <= i < n) F%R).

 
 
 
Definition char (R : Ring.type) of phant R : nat_pred :=
  [pred p | prime p & p%:R == 0 :> R].

Local Notation "[ 'char' R ]" := (char (Phant R)) : ring_scope.

 
Definition converse R : Type := R.
Local Notation "R ^c" := (converse R) (at level 2, format "R ^c") : type_scope.

Section RingTheory.

Variable R : ringType.
Implicit Types x y : R.

Lemma mulrA : @associative R *%R.
Proof.
by case R => T [? []].
Qed.
Lemma mul1r : @left_id R R 1 *%R.
Proof.
by case R => T [? []].
Qed.
Lemma mulr1 : @right_id R R 1 *%R.
Proof.
by case R => T [? []].
Qed.
Lemma mulrDl : @left_distributive R R *%R +%R.
Proof.
by case R => T [? []].
Qed.
Lemma mulrDr : @right_distributive R R *%R +%R.
Proof.
by case R => T [? []].
Qed.
Lemma oner_neq0 : 1 != 0 :> R.
Proof.
by case R => T [? []].
Qed.
Lemma oner_eq0 : (1 == 0 :> R) = false.
Proof.
exact: negbTE oner_neq0.
Qed.

Lemma mul0r : @left_zero R R 0 *%R.
Proof.
by move=> x; apply: (addIr (1 * x)); rewrite -mulrDl !add0r mul1r.
Qed.
Lemma mulr0 : @right_zero R R 0 *%R.
Proof.
by move=> x; apply: (addIr (x * 1)); rewrite -mulrDr !add0r mulr1.
Qed.
Lemma mulrN x y : x * (- y) = - (x * y).
Proof.
by apply: (addrI (x * y)); rewrite -mulrDr !subrr mulr0.
Qed.
Lemma mulNr x y : (- x) * y = - (x * y).
Proof.
by apply: (addrI (x * y)); rewrite -mulrDl !subrr mul0r.
Qed.
Lemma mulrNN x y : (- x) * (- y) = x * y.
Proof.
by rewrite mulrN mulNr opprK.
Qed.
Lemma mulN1r x : -1 * x = - x.
Proof.
by rewrite mulNr mul1r.
Qed.
Lemma mulrN1 x : x * -1 = - x.
Proof.
by rewrite mulrN mulr1.
Qed.

Canonical mul_monoid := Monoid.Law mulrA mul1r mulr1.
Canonical muloid := Monoid.MulLaw mul0r mulr0.
Canonical addoid := Monoid.AddLaw mulrDl mulrDr.

Lemma mulr_suml I r P (F : I -> R) x :
  (\sum_(i <- r | P i) F i) * x = \sum_(i <- r | P i) F i * x.
Proof.
exact: big_distrl.
Qed.

Lemma mulr_sumr I r P (F : I -> R) x :
  x * (\sum_(i <- r | P i) F i) = \sum_(i <- r | P i) x * F i.
Proof.
exact: big_distrr.
Qed.

Lemma mulrBl x y z : (y - z) * x = y * x - z * x.
Proof.
by rewrite mulrDl mulNr.
Qed.

Lemma mulrBr x y z : x * (y - z) = x * y - x * z.
Proof.
by rewrite mulrDr mulrN.
Qed.

Lemma mulrnAl x y n : (x *+ n) * y = (x * y) *+ n.
Proof.
by elim: n => [|n IHn]; rewrite ?mul0r // !mulrS mulrDl IHn.
Qed.

Lemma mulrnAr x y n : x * (y *+ n) = (x * y) *+ n.
Proof.
by elim: n => [|n IHn]; rewrite ?mulr0 // !mulrS mulrDr IHn.
Qed.

Lemma mulr_natl x n : n%:R * x = x *+ n.
Proof.
by rewrite mulrnAl mul1r.
Qed.

Lemma mulr_natr x n : x * n%:R = x *+ n.
Proof.
by rewrite mulrnAr mulr1.
Qed.

Lemma natrD m n : (m + n)%:R = m%:R + n%:R :> R.
Proof.
exact: mulrnDr.
Qed.

Lemma natrB m n : n <= m -> (m - n)%:R = m%:R - n%:R :> R.
Proof.
exact: mulrnBr.
Qed.

Definition natr_sum := big_morph (natmul 1) natrD (mulr0n 1).

Lemma natrM m n : (m * n)%:R = m%:R * n%:R :> R.
Proof.
by rewrite mulrnA -mulr_natr.
Qed.

Lemma expr0 x : x ^+ 0 = 1.
Proof.
by [].
Qed.
Lemma expr1 x : x ^+ 1 = x.
Proof.
by [].
Qed.
Lemma expr2 x : x ^+ 2 = x * x.
Proof.
by [].
Qed.

Lemma exprS x n : x ^+ n.+1 = x * x ^+ n.
Proof.
by case: n => //; rewrite mulr1.
Qed.

Lemma expr0n n : 0 ^+ n = (n == 0%N)%:R :> R.
Proof.
by case: n => // n; rewrite exprS mul0r.
Qed.

Lemma expr1n n : 1 ^+ n = 1 :> R.
Proof.
by elim: n => // n IHn; rewrite exprS mul1r.
Qed.

Lemma exprD x m n : x ^+ (m + n) = x ^+ m * x ^+ n.
Proof.
by elim: m => [|m IHm]; rewrite ?mul1r // !exprS -mulrA -IHm.
Qed.

Lemma exprSr x n : x ^+ n.+1 = x ^+ n * x.
Proof.
by rewrite -addn1 exprD expr1.
Qed.

Lemma expr_sum x (I : Type) (s : seq I) (P : pred I) F :
  x ^+ (\sum_(i <- s | P i) F i) = \prod_(i <- s | P i) x ^+ F i :> R.
Proof.
exact: (big_morph _ (exprD _)).
Qed.

Lemma commr_sym x y : comm x y -> comm y x.
Proof.
by [].
Qed.
Lemma commr_refl x : comm x x.
Proof.
by [].
Qed.

Lemma commr0 x : comm x 0.
Proof.
by rewrite /comm mulr0 mul0r.
Qed.

Lemma commr1 x : comm x 1.
Proof.
by rewrite /comm mulr1 mul1r.
Qed.

Lemma commrN x y : comm x y -> comm x (- y).
Proof.
by move=> com_xy; rewrite /comm mulrN com_xy mulNr.
Qed.

Lemma commrN1 x : comm x (-1).
Proof.
exact/commrN/commr1.
Qed.

Lemma commrD x y z : comm x y -> comm x z -> comm x (y + z).
Proof.
by rewrite /comm mulrDl mulrDr => -> ->.
Qed.

Lemma commrB x y z : comm x y -> comm x z -> comm x (y - z).
Proof.
by move=> com_xy com_xz; apply: commrD => //; apply: commrN.
Qed.

Lemma commr_sum (I : Type) (s : seq I) (P : pred I) (F : I -> R) x :
  (forall i, P i -> comm x (F i)) -> comm x (\sum_(i <- s | P i) F i).
Proof.
move=> comm_x_F; rewrite /comm mulr_suml mulr_sumr.
by apply: eq_bigr => i /comm_x_F.
Qed.

Lemma commrMn x y n : comm x y -> comm x (y *+ n).
Proof.
rewrite /comm => com_xy.
by elim: n => [|n IHn]; rewrite ?commr0 // mulrS commrD.
Qed.

Lemma commrM x y z : comm x y -> comm x z -> comm x (y * z).
Proof.
by move=> com_xy; rewrite /comm mulrA com_xy -!mulrA => ->.
Qed.

Lemma commr_prod (I : Type) (s : seq I) (P : pred I) (F : I -> R) x :
  (forall i, P i -> comm x (F i)) -> comm x (\prod_(i <- s | P i) F i).
Proof.
exact: (big_ind _ (commr1 x) (@commrM x)).
Qed.

Lemma commr_nat x n : comm x n%:R.
Proof.
exact/commrMn/commr1.
Qed.

Lemma commrX x y n : comm x y -> comm x (y ^+ n).
Proof.
rewrite /comm => com_xy.
by elim: n => [|n IHn]; rewrite ?commr1 // exprS commrM.
Qed.

Lemma exprMn_comm x y n : comm x y -> (x * y) ^+ n = x ^+ n * y ^+ n.
Proof.
move=> com_xy; elim: n => /= [|n IHn]; first by rewrite mulr1.
by rewrite !exprS IHn !mulrA; congr (_ * _); rewrite -!mulrA -commrX.
Qed.

Lemma commr_sign x n : comm x ((-1) ^+ n).
Proof.
exact: (commrX n (commrN1 x)).
Qed.

Lemma exprMn_n x m n : (x *+ m) ^+ n = x ^+ n *+ (m ^ n) :> R.
Proof.
elim: n => [|n IHn]; first by rewrite mulr1n.
rewrite exprS IHn -mulr_natr -mulrA -commr_nat mulr_natr -mulrnA -expnSr.
by rewrite -mulr_natr mulrA -exprS mulr_natr.
Qed.

Lemma exprM x m n : x ^+ (m * n) = x ^+ m ^+ n.
Proof.
elim: m => [|m IHm]; first by rewrite expr1n.
by rewrite mulSn exprD IHm exprS exprMn_comm //; apply: commrX.
Qed.

Lemma exprAC x m n : (x ^+ m) ^+ n = (x ^+ n) ^+ m.
Proof.
by rewrite -!exprM mulnC.
Qed.

Lemma expr_mod n x i : x ^+ n = 1 -> x ^+ (i %% n) = x ^+ i.
Proof.
move=> xn1; rewrite {2}(divn_eq i n) exprD mulnC exprM xn1.
by rewrite expr1n mul1r.
Qed.

Lemma expr_dvd n x i : x ^+ n = 1 -> n %| i -> x ^+ i = 1.
Proof.
by move=> xn1 dvd_n_i; rewrite -(expr_mod i xn1) (eqnP dvd_n_i).
Qed.

Lemma natrX n k : (n ^ k)%:R = n%:R ^+ k :> R.
Proof.
by rewrite exprMn_n expr1n.
Qed.

Lemma signr_odd n : (-1) ^+ (odd n) = (-1) ^+ n :> R.
Proof.
elim: n => //= n IHn; rewrite exprS -{}IHn.
by case/odd: n; rewrite !mulN1r ?opprK.
Qed.

Lemma signr_eq0 n : ((-1) ^+ n == 0 :> R) = false.
Proof.
by rewrite -signr_odd; case: odd; rewrite ?oppr_eq0 oner_eq0.
Qed.

Lemma mulr_sign (b : bool) x : (-1) ^+ b * x = (if b then - x else x).
Proof.
by case: b; rewrite ?mulNr mul1r.
Qed.

Lemma signr_addb b1 b2 : (-1) ^+ (b1 (+) b2) = (-1) ^+ b1 * (-1) ^+ b2 :> R.
Proof.
by rewrite mulr_sign; case: b1 b2 => [] []; rewrite ?opprK.
Qed.

Lemma signrE (b : bool) : (-1) ^+ b = 1 - b.*2%:R :> R.
Proof.
by case: b; rewrite ?subr0 // opprD addNKr.
Qed.

Lemma signrN b : (-1) ^+ (~~ b) = - (-1) ^+ b :> R.
Proof.
by case: b; rewrite ?opprK.
Qed.

Lemma mulr_signM (b1 b2 : bool) x1 x2 :
  ((-1) ^+ b1 * x1) * ((-1) ^+ b2 * x2) = (-1) ^+ (b1 (+) b2) * (x1 * x2).
Proof.
by rewrite signr_addb -!mulrA; congr (_ * _); rewrite !mulrA commr_sign.
Qed.

Lemma exprNn x n : (- x) ^+ n = (-1) ^+ n * x ^+ n :> R.
Proof.
by rewrite -mulN1r exprMn_comm // /comm mulN1r mulrN mulr1.
Qed.

Lemma sqrrN x : (- x) ^+ 2 = x ^+ 2.
Proof.
exact: mulrNN.
Qed.

Lemma sqrr_sign n : ((-1) ^+ n) ^+ 2 = 1 :> R.
Proof.
by rewrite exprAC sqrrN !expr1n.
Qed.

Lemma signrMK n : @involutive R ( *%R ((-1) ^+ n)).
Proof.
by move=> x; rewrite mulrA -expr2 sqrr_sign mul1r.
Qed.

Lemma lastr_eq0 (s : seq R) x : x != 0 -> (last x s == 0) = (last 1 s == 0).
Proof.
by case: s => [|y s] /negPf // ->; rewrite oner_eq0.
Qed.

Lemma mulrI_eq0 x y : lreg x -> (x * y == 0) = (y == 0).
Proof.
by move=> reg_x; rewrite -{1}(mulr0 x) (inj_eq reg_x).
Qed.

Lemma lreg_neq0 x : lreg x -> x != 0.
Proof.
by move=> reg_x; rewrite -[x]mulr1 mulrI_eq0 ?oner_eq0.
Qed.

Lemma mulrI0_lreg x : (forall y, x * y = 0 -> y = 0) -> lreg x.
Proof.
move=> reg_x y z eq_xy_xz; apply/eqP; rewrite -subr_eq0 [y - z]reg_x //.
by rewrite mulrBr eq_xy_xz subrr.
Qed.

Lemma lregN x : lreg x -> lreg (- x).
Proof.
by move=> reg_x y z; rewrite !mulNr => /oppr_inj/reg_x.
Qed.

Lemma lreg1 : lreg (1 : R).
Proof.
by move=> x y; rewrite !mul1r.
Qed.

Lemma lregM x y : lreg x -> lreg y -> lreg (x * y).
Proof.
by move=> reg_x reg_y z t; rewrite -!mulrA => /reg_x/reg_y.
Qed.

Lemma lregX x n : lreg x -> lreg (x ^+ n).
Proof.
by move=> reg_x; elim: n => [|n]; [apply: lreg1 | rewrite exprS; apply: lregM].
Qed.

Lemma lreg_sign n : lreg ((-1) ^+ n : R).
Proof.
exact/lregX/lregN/lreg1.
Qed.

Lemma iter_mulr n x y : iter n ( *%R x) y = x ^+ n * y.
Proof.
by elim: n => [|n ih]; rewrite ?expr0 ?mul1r //= ih exprS -mulrA.
Qed.

Lemma iter_mulr_1 n x : iter n ( *%R x) 1 = x ^+ n.
Proof.
by rewrite iter_mulr mulr1.
Qed.

Lemma prodr_const (I : finType) (A : pred I) x : \prod_(i in A) x = x ^+ #|A|.
Proof.
by rewrite big_const -iteropE.
Qed.

Lemma prodr_const_nat n m x : \prod_(n <= i < m) x = x ^+ (m - n).
Proof.
by rewrite big_const_nat -iteropE.
Qed.

Lemma prodrXr x I r P (F : I -> nat) :
  \prod_(i <- r | P i) x ^+ F i = x ^+ (\sum_(i <- r | P i) F i).
Proof.
by rewrite (big_morph _ (exprD _) (erefl _)).
Qed.

Lemma prodrN (I : finType) (A : pred I) (F : I -> R) :
  \prod_(i in A) - F i = (- 1) ^+ #|A| * \prod_(i in A) F i.
Proof.
rewrite -sum1_card; elim/big_rec3: _ => [|i x n _ _ ->]; first by rewrite mulr1.
by rewrite exprS !mulrA mulN1r !mulNr commrX //; apply: commrN1.
Qed.

Lemma prodrMn (I : Type) (s : seq I) (P : pred I) (F : I -> R) (g : I -> nat) :
  \prod_(i <- s | P i) (F i *+ g i) =
  \prod_(i <- s | P i) (F i) *+ \prod_(i <- s | P i) g i.
Proof.
by elim/big_rec3: _ => // i y1 y2 y3 _ ->; rewrite mulrnAr mulrnAl -mulrnA.
Qed.

Lemma prodrMn_const n (I : finType) (A : pred I) (F : I -> R) :
  \prod_(i in A) (F i *+ n) = \prod_(i in A) F i *+ n ^ #|A|.
Proof.
by rewrite prodrMn prod_nat_const.
Qed.

Lemma natr_prod I r P (F : I -> nat) :
  (\prod_(i <- r | P i) F i)%:R = \prod_(i <- r | P i) (F i)%:R :> R.
Proof.
exact: (big_morph _ natrM).
Qed.

Lemma exprDn_comm x y n (cxy : comm x y) :
  (x + y) ^+ n = \sum_(i < n.+1) (x ^+ (n - i) * y ^+ i) *+ 'C(n, i).
Proof.
elim: n => [|n IHn]; rewrite big_ord_recl mulr1 ?big_ord0 ?addr0 //=.
rewrite exprS {}IHn /= mulrDl !big_distrr /= big_ord_recl mulr1 subn0.
rewrite !big_ord_recr /= !binn !subnn !mul1r !subn0 bin0 !exprS -addrA.
congr (_ + _); rewrite addrA -big_split /=; congr (_ + _).
apply: eq_bigr => i _; rewrite !mulrnAr !mulrA -exprS -subSn ?(valP i) //.
by rewrite subSS (commrX _ (commr_sym cxy)) -mulrA -exprS -mulrnDr.
Qed.

Lemma exprBn_comm x y n (cxy : comm x y) :
  (x - y) ^+ n =
    \sum_(i < n.+1) ((-1) ^+ i * x ^+ (n - i) * y ^+ i) *+ 'C(n, i).
Proof.
rewrite exprDn_comm; last exact: commrN.
by apply: eq_bigr => i _; congr (_ *+ _); rewrite -commr_sign -mulrA -exprNn.
Qed.

Lemma subrXX_comm x y n (cxy : comm x y) :
  x ^+ n - y ^+ n = (x - y) * (\sum_(i < n) x ^+ (n.-1 - i) * y ^+ i).
Proof.
case: n => [|n]; first by rewrite big_ord0 mulr0 subrr.
rewrite mulrBl !big_distrr big_ord_recl big_ord_recr /= subnn mulr1 mul1r.
rewrite subn0 -!exprS opprD -!addrA; congr (_ + _); rewrite addrA -sumrB.
rewrite big1 ?add0r // => i _; rewrite !mulrA -exprS -subSn ?(valP i) //.
by rewrite subSS (commrX _ (commr_sym cxy)) -mulrA -exprS subrr.
Qed.

Lemma exprD1n x n : (x + 1) ^+ n = \sum_(i < n.+1) x ^+ i *+ 'C(n, i).
Proof.
rewrite addrC (exprDn_comm n (commr_sym (commr1 x))).
by apply: eq_bigr => i _; rewrite expr1n mul1r.
Qed.

Lemma subrX1 x n : x ^+ n - 1 = (x - 1) * (\sum_(i < n) x ^+ i).
Proof.
rewrite -!(opprB 1) mulNr -{1}(expr1n n).
rewrite (subrXX_comm _ (commr_sym (commr1 x))); congr (- (_ * _)).
by apply: eq_bigr => i _; rewrite expr1n mul1r.
Qed.

Lemma sqrrD1 x : (x + 1) ^+ 2 = x ^+ 2 + x *+ 2 + 1.
Proof.
rewrite exprD1n !big_ord_recr big_ord0 /= add0r.
by rewrite addrC addrA addrAC.
Qed.

Lemma sqrrB1 x : (x - 1) ^+ 2 = x ^+ 2 - x *+ 2 + 1.
Proof.
by rewrite -sqrrN opprB addrC sqrrD1 sqrrN mulNrn.
Qed.

Lemma subr_sqr_1 x : x ^+ 2 - 1 = (x - 1) * (x + 1).
Proof.
by rewrite subrX1 !big_ord_recr big_ord0 /= addrAC add0r.
Qed.

Definition Frobenius_aut p of p \in [char R] := fun x => x ^+ p.

Section FrobeniusAutomorphism.

Variable p : nat.
Hypothesis charFp : p \in [char R].

Lemma charf0 : p%:R = 0 :> R.
Proof.
by apply/eqP; case/andP: charFp.
Qed.
Lemma charf_prime : prime p.
Proof.
by case/andP: charFp.
Qed.
Hint Resolve charf_prime : core.

Lemma mulrn_char x : x *+ p = 0.
Proof.
by rewrite -mulr_natl charf0 mul0r.
Qed.

Lemma natr_mod_char n : (n %% p)%:R = n%:R :> R.
Proof.
by rewrite {2}(divn_eq n p) natrD mulrnA mulrn_char add0r.
Qed.

Lemma dvdn_charf n : (p %| n)%N = (n%:R == 0 :> R).
Proof.
apply/idP/eqP=> [/dvdnP[n' ->]|n0]; first by rewrite natrM charf0 mulr0.
apply/idPn; rewrite -prime_coprime // => /eqnP pn1.
have [a _ /dvdnP[b]] := Bezoutl n (prime_gt0 charf_prime).
move/(congr1 (fun m => m%:R : R))/eqP.
by rewrite natrD !natrM charf0 n0 !mulr0 pn1 addr0 oner_eq0.
Qed.

Lemma charf_eq : [char R] =i (p : nat_pred).
Proof.
move=> q; apply/andP/eqP=> [[q_pr q0] | ->]; last by rewrite charf0.
by apply/eqP; rewrite eq_sym -dvdn_prime2 // dvdn_charf.
Qed.

Lemma bin_lt_charf_0 k : 0 < k < p -> 'C(p, k)%:R = 0 :> R.
Proof.
by move=> lt0kp; apply/eqP; rewrite -dvdn_charf prime_dvd_bin.
Qed.

Local Notation "x ^f" := (Frobenius_aut charFp x).

Lemma Frobenius_autE x : x^f = x ^+ p.
Proof.
by [].
Qed.
Local Notation fE := Frobenius_autE.

Lemma Frobenius_aut0 : 0^f = 0.
Proof.
by rewrite fE -(prednK (prime_gt0 charf_prime)) exprS mul0r.
Qed.

Lemma Frobenius_aut1 : 1^f = 1.
Proof.
by rewrite fE expr1n.
Qed.

Lemma Frobenius_autD_comm x y (cxy : comm x y) : (x + y)^f = x^f + y^f.
Proof.
have defp := prednK (prime_gt0 charf_prime).
rewrite !fE exprDn_comm // big_ord_recr subnn -defp big_ord_recl /= defp.
rewrite subn0 mulr1 mul1r bin0 binn big1 ?addr0 // => i _.
by rewrite -mulr_natl bin_lt_charf_0 ?mul0r //= -{2}defp ltnS (valP i).
Qed.

Lemma Frobenius_autMn x n : (x *+ n)^f = x^f *+ n.
admit.
Defined.

Lemma Frobenius_aut_nat n : (n%:R)^f = n%:R.
admit.
Defined.

Lemma Frobenius_autM_comm x y : comm x y -> (x * y)^f = x^f * y^f.
admit.
Defined.

Lemma Frobenius_autX x n : (x ^+ n)^f = x^f ^+ n.
admit.
Defined.

Lemma Frobenius_autN x : (- x)^f = - x^f.
admit.
Defined.

Lemma Frobenius_autB_comm x y : comm x y -> (x - y)^f = x^f - y^f.
admit.
Defined.

End FrobeniusAutomorphism.

Lemma exprNn_char x n : [char R].-nat n -> (- x) ^+ n = - (x ^+ n).
admit.
Defined.

Section Char2.

Hypothesis charR2 : 2 \in [char R].

Lemma addrr_char2 x : x + x = 0.
admit.
Defined.

Lemma oppr_char2 x : - x = x.
admit.
Defined.

Lemma subr_char2 x y : x - y = x + y.
admit.
Defined.

Lemma addrK_char2 x : involutive (+%R^~ x).
admit.
Defined.

Lemma addKr_char2 x : involutive (+%R x).
admit.
Defined.

End Char2.

Canonical converse_eqType := [eqType of R^c].
Canonical converse_choiceType := [choiceType of R^c].
Canonical converse_zmodType := [zmodType of R^c].

Definition converse_ringMixin :=
  let mul' x y := y * x in
  let mulrA' x y z := esym (mulrA z y x) in
  let mulrDl' x y z := mulrDr z x y in
  let mulrDr' x y z := mulrDl y z x in
  @Ring.Mixin converse_zmodType
    1 mul' mulrA' mulr1 mul1r mulrDl' mulrDr' oner_neq0.
Canonical converse_ringType := RingType R^c converse_ringMixin.

Section ClosedPredicates.

Variable S : {pred R}.

Definition mulr_2closed := {in S &, forall u v, u * v \in S}.
Definition mulr_closed := 1 \in S /\ mulr_2closed.
Definition smulr_closed := -1 \in S /\ mulr_2closed.
Definition semiring_closed := addr_closed S /\ mulr_closed.
Definition subring_closed := [/\ 1 \in S, subr_2closed S & mulr_2closed].

Lemma smulr_closedM : smulr_closed -> mulr_closed.
admit.
Defined.

Lemma smulr_closedN : smulr_closed -> oppr_closed S.
admit.
Defined.

Lemma semiring_closedD : semiring_closed -> addr_closed S.
admit.
Defined.

Lemma semiring_closedM : semiring_closed -> mulr_closed.
admit.
Defined.

Lemma subring_closedB : subring_closed -> zmod_closed S.
admit.
Defined.

Lemma subring_closedM : subring_closed -> smulr_closed.
admit.
Defined.

Lemma subring_closed_semi : subring_closed -> semiring_closed.
admit.
Defined.

End ClosedPredicates.

End RingTheory.

Section RightRegular.

Variable R : ringType.
Implicit Types x y : R.
Let Rc := converse_ringType R.

Lemma mulIr_eq0 x y : rreg x -> (y * x == 0) = (y == 0).
admit.
Defined.

Lemma mulIr0_rreg x : (forall y, y * x = 0 -> y = 0) -> rreg x.
admit.
Defined.

Lemma rreg_neq0 x : rreg x -> x != 0.
admit.
Defined.

Lemma rregN x : rreg x -> rreg (- x).
admit.
Defined.

Lemma rreg1 : rreg (1 : R).
admit.
Defined.

Lemma rregM x y : rreg x -> rreg y -> rreg (x * y).
admit.
Defined.

Lemma revrX x n : (x : Rc) ^+ n = (x : R) ^+ n.
admit.
Defined.

Lemma rregX x n : rreg x -> rreg (x ^+ n).
admit.
Defined.

End RightRegular.

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

Set Primitive Projections.
Record class_of V := Class {
  base : Zmodule.class_of V;
  mixin : mixin_of R (Zmodule.Pack base)
}.
Unset Primitive Projections.
Local Coercion base : class_of >-> Zmodule.class_of.

Structure type (phR : phant R) := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variable (phR : phant R) (T : Type) (cT : type phR).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack phR T c.

Definition pack b0 (m0 : mixin_of R (@Zmodule.Pack T b0)) :=
  fun bT b & phant_id (Zmodule.class bT) b =>
  fun    m & phant_id m0 m => Pack phR (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition zmodType := @Zmodule.Pack cT class.

End ClassDef.

Module Import Exports.
Coercion base : class_of >-> Zmodule.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> Zmodule.type.
Canonical zmodType.
Notation lmodType R := (type (Phant R)).
Notation LmodType R T m := (@pack _ (Phant R) T _ m _ _ id _ id).
Notation LmodMixin := Mixin.
Notation "[ 'lmodType' R 'of' T 'for' cT ]" := (@clone _ (Phant R) T cT _ idfun)
  (at level 0, format "[ 'lmodType'  R  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'lmodType' R 'of' T ]" := (@clone _ (Phant R) T _ _ id)
  (at level 0, format "[ 'lmodType'  R  'of'  T ]") : form_scope.
End Exports.

End Lmodule.
Import Lmodule.Exports.

Definition scale (R : ringType) (V : lmodType R) : R -> V -> V :=
  Lmodule.scale (Lmodule.class V).

Local Notation "*:%R" := (@scale _ _) : fun_scope.
Local Notation "a *: v" := (scale a v) : ring_scope.

Section LmoduleTheory.

Variables (R : ringType) (V : lmodType R).
Implicit Types (a b c : R) (u v : V).

Local Notation "*:%R" := (@scale R V) : fun_scope.

Lemma scalerA a b v : a *: (b *: v) = a * b *: v.
admit.
Defined.

Lemma scale1r : @left_id R V 1 *:%R.
admit.
Defined.

Lemma scalerDr a : {morph *:%R a : u v / u + v}.
admit.
Defined.

Lemma scalerDl v : {morph *:%R^~ v : a b / a + b}.
admit.
Defined.

Lemma scale0r v : 0 *: v = 0.
admit.
Defined.

Lemma scaler0 a : a *: 0 = 0 :> V.
admit.
Defined.

Lemma scaleNr a v : - a *: v = - (a *: v).
admit.
Defined.

Lemma scaleN1r v : (- 1) *: v = - v.
admit.
Defined.

Lemma scalerN a v : a *: (- v) = - (a *: v).
admit.
Defined.

Lemma scalerBl a b v : (a - b) *: v = a *: v - b *: v.
admit.
Defined.

Lemma scalerBr a u v : a *: (u - v) = a *: u - a *: v.
admit.
Defined.

Lemma scaler_nat n v : n%:R *: v = v *+ n.
admit.
Defined.

Lemma scaler_sign (b : bool) v: (-1) ^+ b *: v = (if b then - v else v).
admit.
Defined.

Lemma signrZK n : @involutive V ( *:%R ((-1) ^+ n)).
admit.
Defined.

Lemma scalerMnl a v n : a *: v *+ n = (a *+ n) *: v.
admit.
Defined.

Lemma scalerMnr a v n : a *: v *+ n = a *: (v *+ n).
admit.
Defined.

Lemma scaler_suml v I r (P : pred I) F :
  (\sum_(i <- r | P i) F i) *: v = \sum_(i <- r | P i) F i *: v.
admit.
Defined.

Lemma scaler_sumr a I r (P : pred I) (F : I -> V) :
  a *: (\sum_(i <- r | P i) F i) = \sum_(i <- r | P i) a *: F i.
admit.
Defined.

Section ClosedPredicates.

Variable S : {pred V}.

Definition scaler_closed := forall a, {in S, forall v, a *: v \in S}.
Definition linear_closed := forall a, {in S &, forall u v, a *: u + v \in S}.
Definition submod_closed := 0 \in S /\ linear_closed.

Lemma linear_closedB : linear_closed -> subr_2closed S.
admit.
Defined.

Lemma submod_closedB : submod_closed -> zmod_closed S.
admit.
Defined.

Lemma submod_closedZ : submod_closed -> scaler_closed.
admit.
Defined.

End ClosedPredicates.

End LmoduleTheory.

Module Lalgebra.

Definition axiom (R : ringType) (V : lmodType R) (mul : V -> V -> V) :=
  forall a u v, a *: mul u v = mul (a *: u) v.

Section ClassDef.

Variable R : ringType.

Set Primitive Projections.
Record class_of (T : Type) : Type := Class {
  base : Ring.class_of T;
  mixin : Lmodule.mixin_of R (Zmodule.Pack base);
  ext : @axiom R (Lmodule.Pack _ (Lmodule.Class mixin)) (Ring.mul base)
}.
Unset Primitive Projections.
Definition base2 R m := Lmodule.Class (@mixin R m).
Local Coercion base : class_of >-> Ring.class_of.
Local Coercion base2 : class_of >-> Lmodule.class_of.

Structure type (phR : phant R) := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variable (phR : phant R) (T : Type) (cT : type phR).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack phR T c.

Definition pack b0 mul0 (axT : @axiom R (@Lmodule.Pack R _ T b0) mul0) :=
  fun bT b & phant_id (Ring.class bT) (b : Ring.class_of T) =>
  fun mT m & phant_id (@Lmodule.class R phR mT) (@Lmodule.Class R T b m) =>
  fun ax & phant_id axT ax =>
  Pack (Phant R) (@Class T b m ax).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition zmodType := @Zmodule.Pack cT class.
Definition ringType := @Ring.Pack cT class.
Definition lmodType := @Lmodule.Pack R phR cT class.
Definition lmod_ringType := @Lmodule.Pack R phR ringType class.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Ring.class_of.
Coercion base2 : class_of >-> Lmodule.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> Ring.type.
Canonical ringType.
Coercion lmodType : type >-> Lmodule.type.
Canonical lmodType.
Canonical lmod_ringType.
Notation lalgType R := (type (Phant R)).
Notation LalgType R T a := (@pack _ (Phant R) T _ _ a _ _ id _ _ id _ id).
Notation "[ 'lalgType' R 'of' T 'for' cT ]" := (@clone _ (Phant R) T cT _ idfun)
  (at level 0, format "[ 'lalgType'  R  'of'  T  'for'  cT ]")
  : form_scope.
Notation "[ 'lalgType' R 'of' T ]" := (@clone _ (Phant R) T _ _ id)
  (at level 0, format "[ 'lalgType'  R  'of'  T ]") : form_scope.
End Exports.

End Lalgebra.
Import Lalgebra.Exports.

 
Local Notation "k %:A" := (k *: 1) : ring_scope.

 
Definition regular R : Type := R.
Local Notation "R ^o" := (regular R) (at level 2, format "R ^o") : type_scope.

Section LalgebraTheory.

Variables (R : ringType) (A : lalgType R).
Implicit Types x y : A.

Lemma scalerAl k (x y : A) : k *: (x * y) = k *: x * y.
admit.
Defined.

Lemma mulr_algl a x : a%:A * x = a *: x.
admit.
Defined.

Canonical regular_eqType := [eqType of R^o].
Canonical regular_choiceType := [choiceType of R^o].
Canonical regular_zmodType := [zmodType of R^o].
Canonical regular_ringType := [ringType of R^o].

Definition regular_lmodMixin :=
  let mkMixin := @Lmodule.Mixin R regular_zmodType (@mul R) in
  mkMixin (@mulrA R) (@mul1r R) (@mulrDr R) (fun v a b => mulrDl a b v).

Canonical regular_lmodType := LmodType R R^o regular_lmodMixin.
Canonical regular_lalgType := LalgType R R^o (@mulrA regular_ringType).

Section ClosedPredicates.

Variable S : {pred A}.

Definition subalg_closed := [/\ 1 \in S, linear_closed S & mulr_2closed S].

Lemma subalg_closedZ : subalg_closed -> submod_closed S.
admit.
Defined.

Lemma subalg_closedBM : subalg_closed -> subring_closed S.
admit.
Defined.

End ClosedPredicates.

End LalgebraTheory.

 

Module Additive.

Section ClassDef.

Variables U V : zmodType.

Definition axiom (f : U -> V) := {morph f : x y / x - y}.

Structure map (phUV : phant (U -> V)) := Pack {apply; _ : axiom apply}.
Local Coercion apply : map >-> Funclass.

Variables (phUV : phant (U -> V)) (f g : U -> V) (cF : map phUV).
Definition class := let: Pack _ c as cF' := cF return axiom cF' in c.
Definition clone fA of phant_id g (apply cF) & phant_id fA class :=
  @Pack phUV f fA.

End ClassDef.

Module Exports.
Notation additive f := (axiom f).
Coercion apply : map >-> Funclass.
Notation Additive fA := (Pack (Phant _) fA).
Notation "{ 'additive' fUV }" := (map (Phant fUV))
  (at level 0, format "{ 'additive'  fUV }") : ring_scope.
Notation "[ 'additive' 'of' f 'as' g ]" := (@clone _ _ _ f g _ _ idfun id)
  (at level 0, format "[ 'additive'  'of'  f  'as'  g ]") : form_scope.
Notation "[ 'additive' 'of' f ]" := (@clone _ _ _ f f _ _ id id)
  (at level 0, format "[ 'additive'  'of'  f ]") : form_scope.
End Exports.

End Additive.
Include Additive.Exports.
 

 
Section LiftedZmod.
Variables (U : Type) (V : zmodType).
Definition null_fun_head (phV : phant V) of U : V := let: Phant := phV in 0.
Definition add_fun (f g : U -> V) x := f x + g x.
Definition sub_fun (f g : U -> V) x := f x - g x.
End LiftedZmod.

 
Section LiftedRing.
Variables (R : ringType) (T : Type).
Implicit Type f : T -> R.
Definition mull_fun a f x := a * f x.
Definition mulr_fun a f x := f x * a.
End LiftedRing.

 
Section LiftedScale.
Variables (R : ringType) (U : Type) (V : lmodType R) (A : lalgType R).
Definition scale_fun a (f : U -> V) x := a *: f x.
Definition in_alg_head (phA : phant A) k : A := let: Phant := phA in k%:A.
End LiftedScale.

Notation null_fun V := (null_fun_head (Phant V)) (only parsing).
 
 
Local Notation in_alg_loc A := (in_alg_head (Phant A)) (only parsing).

Local Notation "\0" := (null_fun _) : ring_scope.
Local Notation "f \+ g" := (add_fun f g) : ring_scope.
Local Notation "f \- g" := (sub_fun f g) : ring_scope.
Local Notation "a \*: f" := (scale_fun a f) : ring_scope.
Local Notation "x \*o f" := (mull_fun x f) : ring_scope.
Local Notation "x \o* f" := (mulr_fun x f) : ring_scope.

Arguments add_fun {_ _} f g _ /.
Arguments sub_fun {_ _} f g _ /.
Arguments mull_fun {_ _}  a f _ /.
Arguments mulr_fun {_ _} a f _ /.
Arguments scale_fun {_ _ _} a f _ /.

Section AdditiveTheory.

Section Properties.

Variables (U V : zmodType) (k : unit) (f : {additive U -> V}).

Lemma raddfB : {morph f : x y / x - y}.
admit.
Defined.

Lemma raddf0 : f 0 = 0.
admit.
Defined.

Lemma raddf_eq0 x : injective f -> (f x == 0) = (x == 0).
admit.
Defined.

Lemma raddf_inj : (forall x, f x = 0 -> x = 0) -> injective f.
admit.
Defined.

Lemma raddfN : {morph f : x / - x}.
admit.
Defined.

Lemma raddfD : {morph f : x y / x + y}.
admit.
Defined.

Lemma raddfMn n : {morph f : x / x *+ n}.
admit.
Defined.

Lemma raddfMNn n : {morph f : x / x *- n}.
admit.
Defined.

Lemma raddf_sum I r (P : pred I) E :
  f (\sum_(i <- r | P i) E i) = \sum_(i <- r | P i) f (E i).
admit.
Defined.

Lemma can2_additive f' : cancel f f' -> cancel f' f -> additive f'.
admit.
Defined.

Lemma bij_additive :
  bijective f -> exists2 f' : {additive V -> U}, cancel f f' & cancel f' f.
admit.
Defined.

Fact locked_is_additive : additive (locked_with k (f : U -> V)).
admit.
Defined.
Canonical locked_additive := Additive locked_is_additive.

End Properties.

Section RingProperties.

Variables (R S : ringType) (f : {additive R -> S}).

Lemma raddfMnat n x : f (n%:R * x) = n%:R * f x.
admit.
Defined.

Lemma raddfMsign n x : f ((-1) ^+ n * x) = (-1) ^+ n * f x.
admit.
Defined.

Variables (U : lmodType R) (V : lmodType S) (h : {additive U -> V}).

Lemma raddfZnat n u : h (n%:R *: u) = n%:R *: h u.
admit.
Defined.

Lemma raddfZsign n u : h ((-1) ^+ n *: u) = (-1) ^+ n *: h u.
admit.
Defined.

End RingProperties.

Section AddFun.

Variables (U V W : zmodType) (f g : {additive V -> W}) (h : {additive U -> V}).

Fact idfun_is_additive : additive (@idfun U).
admit.
Defined.
Canonical idfun_additive := Additive idfun_is_additive.

Fact comp_is_additive : additive (f \o h).
admit.
Defined.
Canonical comp_additive := Additive comp_is_additive.

Fact opp_is_additive : additive (-%R : U -> U).
admit.
Defined.
Canonical opp_additive := Additive opp_is_additive.

Fact null_fun_is_additive : additive (\0 : U -> V).
admit.
Defined.
Canonical null_fun_additive := Additive null_fun_is_additive.

Fact add_fun_is_additive : additive (f \+ g).
admit.
Defined.
Canonical add_fun_additive := Additive add_fun_is_additive.

Fact sub_fun_is_additive : additive (f \- g).
admit.
Defined.
Canonical sub_fun_additive := Additive sub_fun_is_additive.

End AddFun.

Section MulFun.

Variables (R : ringType) (U : zmodType).
Variables (a : R) (f : {additive U -> R}).

Fact mull_fun_is_additive : additive (a \*o f).
admit.
Defined.
Canonical mull_fun_additive := Additive mull_fun_is_additive.

Fact mulr_fun_is_additive : additive (a \o* f).
admit.
Defined.
Canonical mulr_fun_additive := Additive mulr_fun_is_additive.

End MulFun.

Section ScaleFun.

Variables (R : ringType) (U : zmodType) (V : lmodType R).
Variables (a : R) (f : {additive U -> V}).

Canonical scale_additive := Additive (@scalerBr R V a).
Canonical scale_fun_additive := [additive of a \*: f as f \; *:%R a].

End ScaleFun.

End AdditiveTheory.

Module RMorphism.

Section ClassDef.

Variables R S : ringType.

Definition mixin_of (f : R -> S) :=
  {morph f : x y / x * y}%R * (f 1 = 1) : Prop.

Record class_of f : Prop := Class {base : additive f; mixin : mixin_of f}.
Local Coercion base : class_of >-> additive.

Structure map (phRS : phant (R -> S)) := Pack {apply; _ : class_of apply}.
Local Coercion apply : map >-> Funclass.
Variables (phRS : phant (R -> S)) (f g : R -> S) (cF : map phRS).

Definition class := let: Pack _ c as cF' := cF return class_of cF' in c.

Definition clone fM of phant_id g (apply cF) & phant_id fM class :=
  @Pack phRS f fM.

Definition pack (fM : mixin_of f) :=
  fun (bF : Additive.map phRS) fA & phant_id (Additive.class bF) fA =>
  Pack phRS (Class fA fM).

Canonical additive := Additive.Pack phRS class.

End ClassDef.

Module Exports.
Notation multiplicative f := (mixin_of f).
Notation rmorphism f := (class_of f).
Coercion base : rmorphism >-> Additive.axiom.
Coercion mixin : rmorphism >-> multiplicative.
Coercion apply : map >-> Funclass.
Notation RMorphism fM := (Pack (Phant _) fM).
Notation AddRMorphism fM := (pack fM id).
Notation "{ 'rmorphism' fRS }" := (map (Phant fRS))
  (at level 0, format "{ 'rmorphism'  fRS }") : ring_scope.
Notation "[ 'rmorphism' 'of' f 'as' g ]" := (@clone _ _ _ f g _ _ idfun id)
  (at level 0, format "[ 'rmorphism'  'of'  f  'as'  g ]") : form_scope.
Notation "[ 'rmorphism' 'of' f ]" := (@clone _ _ _ f f _ _ id id)
  (at level 0, format "[ 'rmorphism'  'of'  f ]") : form_scope.
Coercion additive : map >-> Additive.map.
Canonical additive.
End Exports.

End RMorphism.
Include RMorphism.Exports.

Section RmorphismTheory.

Section Properties.

Variables (R S : ringType) (k : unit) (f : {rmorphism R -> S}).

Lemma rmorph0 : f 0 = 0.
admit.
Defined.
Lemma rmorphN : {morph f : x / - x}.
admit.
Defined.
Lemma rmorphD : {morph f : x y / x + y}.
admit.
Defined.
Lemma rmorphB : {morph f: x y / x - y}.
admit.
Defined.
Lemma rmorphMn n : {morph f : x / x *+ n}.
admit.
Defined.
Lemma rmorphMNn n : {morph f : x / x *- n}.
admit.
Defined.
Lemma rmorph_sum I r (P : pred I) E :
  f (\sum_(i <- r | P i) E i) = \sum_(i <- r | P i) f (E i).
admit.
Defined.
Lemma rmorphMsign n : {morph f : x / (- 1) ^+ n * x}.
admit.
Defined.

Lemma rmorphismP : rmorphism f.
admit.
Defined.
Lemma rmorphismMP : multiplicative f.
admit.
Defined.
Lemma rmorph1 : f 1 = 1.
admit.
Defined.
Lemma rmorphM : {morph f: x y  / x * y}.
admit.
Defined.

Lemma rmorph_prod I r (P : pred I) E :
  f (\prod_(i <- r | P i) E i) = \prod_(i <- r | P i) f (E i).
admit.
Defined.

Lemma rmorphX n : {morph f: x / x ^+ n}.
admit.
Defined.

Lemma rmorph_nat n : f n%:R = n%:R.
admit.
Defined.
Lemma rmorphN1 : f (- 1) = (- 1).
admit.
Defined.

Lemma rmorph_sign n : f ((- 1) ^+ n) = (- 1) ^+ n.
admit.
Defined.

Lemma rmorph_char p : p \in [char R] -> p \in [char S].
admit.
Defined.

Lemma rmorph_eq_nat x n : injective f -> (f x == n%:R) = (x == n%:R).
admit.
Defined.

Lemma rmorph_eq1 x : injective f -> (f x == 1) = (x == 1).
admit.
Defined.

Lemma can2_rmorphism f' : cancel f f' -> cancel f' f -> rmorphism f'.
admit.
Defined.

Lemma bij_rmorphism :
  bijective f -> exists2 f' : {rmorphism S -> R}, cancel f f' & cancel f' f.
admit.
Defined.

Fact locked_is_multiplicative : multiplicative (locked_with k (f : R -> S)).
admit.
Defined.
Canonical locked_rmorphism := AddRMorphism locked_is_multiplicative.

End Properties.

Section Projections.

Variables (R S T : ringType) (f : {rmorphism S -> T}) (g : {rmorphism R -> S}).

Fact idfun_is_multiplicative : multiplicative (@idfun R).
admit.
Defined.
Canonical idfun_rmorphism := AddRMorphism idfun_is_multiplicative.

Fact comp_is_multiplicative : multiplicative (f \o g).
admit.
Defined.
Canonical comp_rmorphism := AddRMorphism comp_is_multiplicative.

End Projections.

Section InAlgebra.

Variables (R : ringType) (A : lalgType R).

Fact in_alg_is_rmorphism : rmorphism (in_alg_loc A).
admit.
Defined.
Canonical in_alg_additive := Additive in_alg_is_rmorphism.
Canonical in_alg_rmorphism := RMorphism in_alg_is_rmorphism.

Lemma in_algE a : in_alg_loc A a = a%:A.
admit.
Defined.

End InAlgebra.

End RmorphismTheory.

Module Scale.

Section ScaleLaw.

Structure law (R : ringType) (V : zmodType) (s : R -> V -> V) := Law {
  op : R -> V -> V;
  _ : op = s;
  _ : op (-1) =1 -%R;
  _ : forall a, additive (op a)
}.

Definition mul_law R := Law (erefl *%R) (@mulN1r R) (@mulrBr R).
Definition scale_law R U := Law (erefl *:%R) (@scaleN1r R U) (@scalerBr R U).

Variables (R : ringType) (V : zmodType) (s : R -> V -> V) (s_law : law s).
Local Notation s_op := (op s_law).

Lemma opE : s_op = s.
admit.
Defined.
Lemma N1op : s_op (-1) =1 -%R.
admit.
Defined.
Fact opB a : additive (s_op a).
admit.
Defined.
Definition op_additive a := Additive (opB a).

Variables (aR : ringType) (nu : {rmorphism aR -> R}).
Fact comp_opE : nu \; s_op = nu \; s.
admit.
Defined.
Fact compN1op : (nu \; s_op) (-1) =1 -%R.
admit.
Defined.
Definition comp_law : law (nu \; s) := Law comp_opE compN1op (fun a => opB _).

End ScaleLaw.

End Scale.

Module Linear.

Section ClassDef.

Variables (R : ringType) (U : lmodType R) (V : zmodType) (s : R -> V -> V).
Implicit Type phUV : phant (U -> V).

Local Coercion Scale.op : Scale.law >-> Funclass.
Definition axiom (f : U -> V) (s_law : Scale.law s) of s = s_law :=
  forall a, {morph f : u v / a *: u + v >-> s a u + v}.
Definition mixin_of (f : U -> V) :=
  forall a, {morph f : v / a *: v >-> s a v}.

Record class_of f : Prop := Class {base : additive f; mixin : mixin_of f}.
Local Coercion base : class_of >-> additive.

Lemma class_of_axiom f s_law Ds : @axiom f s_law Ds -> class_of f.
admit.
Defined.

Structure map (phUV : phant (U -> V)) := Pack {apply; _ : class_of apply}.
Local Coercion apply : map >-> Funclass.

Variables (phUV : phant (U -> V)) (f g : U -> V) (cF : map phUV).
Definition class := let: Pack _ c as cF' := cF return class_of cF' in c.
Definition clone fL of phant_id g (apply cF) & phant_id fL class :=
  @Pack phUV f fL.

Definition pack (fZ : mixin_of f) :=
  fun (bF : Additive.map phUV) fA & phant_id (Additive.class bF) fA =>
  Pack phUV (Class fA fZ).

Canonical additive := Additive.Pack phUV class.

 
Notation mapUV := (map (Phant (U -> V))).
Definition map_class := mapUV.
Definition map_at (a : R) := mapUV.
Structure map_for a s_a := MapFor {map_for_map : mapUV; _ : s a = s_a}.
Definition unify_map_at a (f : map_at a) := MapFor f (erefl (s a)).
Structure wrapped := Wrap {unwrap : mapUV}.
Definition wrap (f : map_class) := Wrap f.

End ClassDef.

Module Exports.
Canonical Scale.mul_law.
Canonical Scale.scale_law.
Canonical Scale.comp_law.
Canonical Scale.op_additive.
Delimit Scope linear_ring_scope with linR.
Notation "a *: u" := (@Scale.op _ _ *:%R _ a u) : linear_ring_scope.
Notation "a * u" := (@Scale.op _ _ *%R _ a u) : linear_ring_scope.
Notation "a *:^ nu u" := (@Scale.op _ _ (nu \; *:%R) _ a u)
  (at level 40, nu at level 1, format "a  *:^ nu  u") : linear_ring_scope.
Notation "a *^ nu u" := (@Scale.op _ _ (nu \; *%R) _ a u)
  (at level 40, nu at level 1, format "a  *^ nu  u") : linear_ring_scope.
Notation scalable_for s f := (mixin_of s f).
Notation scalable f := (scalable_for *:%R f).
Notation linear_for s f := (axiom f (erefl s)).
Notation linear f := (linear_for *:%R f).
Notation scalar f := (linear_for *%R f).
Notation lmorphism_for s f := (class_of s f).
Notation lmorphism f := (lmorphism_for *:%R f).
Coercion class_of_axiom : axiom >-> lmorphism_for.
Coercion base : lmorphism_for >-> Additive.axiom.
Coercion mixin : lmorphism_for >-> scalable.
Coercion apply : map >-> Funclass.
Notation Linear fL := (Pack (Phant _) fL).
Notation AddLinear fZ := (pack fZ id).
Notation "{ 'linear' fUV | s }" := (map s (Phant fUV))
  (at level 0, format "{ 'linear'  fUV  |  s }") : ring_scope.
Notation "{ 'linear' fUV }" := {linear fUV | *:%R}
  (at level 0, format "{ 'linear'  fUV }") : ring_scope.
Notation "{ 'scalar' U }" := {linear U -> _ | *%R}
  (at level 0, format "{ 'scalar'  U }") : ring_scope.
Notation "[ 'linear' 'of' f 'as' g ]" := (@clone _ _ _ _ _ f g _ _ idfun id)
  (at level 0, format "[ 'linear'  'of'  f  'as'  g ]") : form_scope.
Notation "[ 'linear' 'of' f ]" := (@clone _ _ _ _ _ f f _ _ id id)
  (at level 0, format "[ 'linear'  'of'  f ]") : form_scope.
Coercion additive : map >-> Additive.map.
Canonical additive.
 
Coercion map_for_map : map_for >-> map.
Coercion unify_map_at : map_at >-> map_for.
Canonical unify_map_at.
Coercion unwrap : wrapped >-> map.
Coercion wrap : map_class >-> wrapped.
Canonical wrap.
End Exports.

End Linear.
Include Linear.Exports.

Section LinearTheory.

Variable R : ringType.

Section GenericProperties.

Variables (U : lmodType R) (V : zmodType) (s : R -> V -> V) (k : unit).
Variable f : {linear U -> V | s}.

Lemma linear0 : f 0 = 0.
admit.
Defined.
Lemma linearN : {morph f : x / - x}.
admit.
Defined.
Lemma linearD : {morph f : x y / x + y}.
admit.
Defined.
Lemma linearB : {morph f : x y / x - y}.
admit.
Defined.
Lemma linearMn n : {morph f : x / x *+ n}.
admit.
Defined.
Lemma linearMNn n : {morph f : x / x *- n}.
admit.
Defined.
Lemma linear_sum I r (P : pred I) E :
  f (\sum_(i <- r | P i) E i) = \sum_(i <- r | P i) f (E i).
admit.
Defined.

Lemma linearZ_LR : scalable_for s f.
admit.
Defined.
Lemma linearP a : {morph f : u v / a *: u + v >-> s a u + v}.
admit.
Defined.

Fact locked_is_scalable : scalable_for s (locked_with k (f : U -> V)).
admit.
Defined.
Canonical locked_linear := AddLinear locked_is_scalable.

End GenericProperties.

Section BidirectionalLinearZ.

Variables (U : lmodType R) (V : zmodType) (s : R -> V -> V).

 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 

Variables (S : ringType) (h : S -> V -> V) (h_law : Scale.law h).

Lemma linearZ c a (h_c := Scale.op h_law c) (f : Linear.map_for U s a h_c) u :
  f (a *: u) = h_c (Linear.wrap f u).
admit.
Defined.

End BidirectionalLinearZ.

Section LmodProperties.

Variables (U V : lmodType R) (f : {linear U -> V}).

Lemma linearZZ : scalable f.
admit.
Defined.
Lemma linearPZ : linear f.
admit.
Defined.

Lemma can2_linear f' : cancel f f' -> cancel f' f -> linear f'.
admit.
Defined.

Lemma bij_linear :
  bijective f -> exists2 f' : {linear V -> U}, cancel f f' & cancel f' f.
admit.
Defined.

End LmodProperties.

Section ScalarProperties.

Variable (U : lmodType R) (f : {scalar U}).

Lemma scalarZ : scalable_for *%R f.
admit.
Defined.
Lemma scalarP : scalar f.
admit.
Defined.

End ScalarProperties.

Section LinearLmod.

Variables (W U : lmodType R) (V : zmodType) (s : R -> V -> V).
Variables (f : {linear U -> V | s}) (h : {linear W -> U}).

Lemma idfun_is_scalable : scalable (@idfun U).
admit.
Defined.
Canonical idfun_linear := AddLinear idfun_is_scalable.

Lemma opp_is_scalable : scalable (-%R : U -> U).
admit.
Defined.
Canonical opp_linear := AddLinear opp_is_scalable.

Lemma comp_is_scalable : scalable_for s (f \o h).
admit.
Defined.
Canonical comp_linear := AddLinear comp_is_scalable.

Variables (s_law : Scale.law s) (g : {linear U -> V | Scale.op s_law}).
Let Ds : s =1 Scale.op s_law.
admit.
Defined.

Lemma null_fun_is_scalable : scalable_for (Scale.op s_law) (\0 : U -> V).
admit.
Defined.
Canonical null_fun_linear := AddLinear null_fun_is_scalable.

Lemma add_fun_is_scalable : scalable_for s (f \+ g).
admit.
Defined.
Canonical add_fun_linear := AddLinear add_fun_is_scalable.

Lemma sub_fun_is_scalable : scalable_for s (f \- g).
admit.
Defined.
Canonical sub_fun_linear := AddLinear sub_fun_is_scalable.

End LinearLmod.

Section LinearLalg.

Variables (A : lalgType R) (U : lmodType R).

Variables (a : A) (f : {linear U -> A}).

Fact mulr_fun_is_scalable : scalable (a \o* f).
admit.
Defined.
Canonical mulr_fun_linear := AddLinear mulr_fun_is_scalable.

End LinearLalg.

End LinearTheory.

Module LRMorphism.

Section ClassDef.

Variables (R : ringType) (A : lalgType R) (B : ringType) (s : R -> B -> B).

Record class_of (f : A -> B) : Prop :=
  Class {base : rmorphism f; mixin : scalable_for s f}.
Local Coercion base : class_of >-> rmorphism.
Definition base2 f (fLM : class_of f) := Linear.Class fLM (mixin fLM).
Local Coercion base2 : class_of >-> lmorphism.

Structure map (phAB : phant (A -> B)) := Pack {apply; _ : class_of apply}.
Local Coercion apply : map >-> Funclass.

Variables (phAB : phant (A -> B)) (f : A -> B) (cF : map phAB).
Definition class := let: Pack _ c as cF' := cF return class_of cF' in c.

Definition clone :=
  fun (g : RMorphism.map phAB) fM & phant_id (RMorphism.class g) fM =>
  fun (h : Linear.map s phAB) fZ &
     phant_id (Linear.mixin (Linear.class h)) fZ =>
  Pack phAB (@Class f fM fZ).

Definition pack (fZ : scalable_for s f) :=
  fun (g : RMorphism.map phAB) fM & phant_id (RMorphism.class g) fM =>
  Pack phAB (Class fM fZ).

Canonical additive := Additive.Pack phAB class.
Canonical rmorphism := RMorphism.Pack phAB class.
Canonical linear := Linear.Pack phAB class.
Canonical join_rmorphism := @RMorphism.Pack _ _ phAB linear class.
Canonical join_linear := @Linear.Pack R A B s phAB rmorphism class.

End ClassDef.

Module Exports.
Notation lrmorphism_for s f := (class_of s f).
Notation lrmorphism f := (lrmorphism_for *:%R f).
Coercion base : lrmorphism_for >-> RMorphism.class_of.
Coercion base2 : lrmorphism_for >-> lmorphism_for.
Coercion apply : map >-> Funclass.
Notation LRMorphism f_lrM := (Pack (Phant _) (Class f_lrM f_lrM)).
Notation AddLRMorphism fZ := (pack fZ id).
Notation "{ 'lrmorphism' fAB | s }" := (map s (Phant fAB))
  (at level 0, format "{ 'lrmorphism'  fAB  |  s }") : ring_scope.
Notation "{ 'lrmorphism' fAB }" := {lrmorphism fAB | *:%R}
  (at level 0, format "{ 'lrmorphism'  fAB }") : ring_scope.
Notation "[ 'lrmorphism' 'of' f ]" := (@clone _ _ _ _ _ f _ _ id _ _ id)
  (at level 0, format "[ 'lrmorphism'  'of'  f ]") : form_scope.
Coercion additive : map >-> Additive.map.
Canonical additive.
Coercion rmorphism : map >-> RMorphism.map.
Canonical rmorphism.
Coercion linear : map >-> Linear.map.
Canonical linear.
Canonical join_rmorphism.
Canonical join_linear.
End Exports.

End LRMorphism.
Include LRMorphism.Exports.

Section LRMorphismTheory.

Variables (R : ringType) (A B : lalgType R) (C : ringType) (s : R -> C -> C).
Variables (k : unit) (f : {lrmorphism A -> B}) (g : {lrmorphism B -> C | s}).

Definition idfun_lrmorphism := [lrmorphism of @idfun A].
Definition comp_lrmorphism := [lrmorphism of g \o f].
Definition locked_lrmorphism := [lrmorphism of locked_with k (f : A -> B)].

Lemma rmorph_alg a : f a%:A = a%:A.
admit.
Defined.

Lemma lrmorphismP : lrmorphism f.
admit.
Defined.

Lemma can2_lrmorphism f' : cancel f f' -> cancel f' f -> lrmorphism f'.
admit.
Defined.

Lemma bij_lrmorphism :
  bijective f -> exists2 f' : {lrmorphism B -> A}, cancel f f' & cancel f' f.
admit.
Defined.

End LRMorphismTheory.

Module ComRing.

Definition RingMixin R one mul mulA mulC mul1x mul_addl :=
  let mulx1 := Monoid.mulC_id mulC mul1x in
  let mul_addr := Monoid.mulC_dist mulC mul_addl in
  @Ring.EtaMixin R one mul mulA mul1x mulx1 mul_addl mul_addr.

Section ClassDef.

Set Primitive Projections.
Record class_of R :=
  Class {base : Ring.class_of R; mixin : commutative (Ring.mul base)}.
Unset Primitive Projections.
Local Coercion base : class_of >-> Ring.class_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variable (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.

Definition pack mul0 (m0 : @commutative T T mul0) :=
  fun bT b & phant_id (Ring.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition zmodType := @Zmodule.Pack cT class.
Definition ringType := @Ring.Pack cT class.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Ring.class_of.
Arguments mixin [R].
Coercion mixin : class_of >-> commutative.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> Ring.type.
Canonical ringType.
Notation comRingType := type.
Notation ComRingType T m := (@pack T _ m _ _ id _ id).
Notation ComRingMixin := RingMixin.
Notation "[ 'comRingType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'comRingType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'comRingType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'comRingType'  'of'  T ]") : form_scope.
End Exports.

End ComRing.
Import ComRing.Exports.

Section ComRingTheory.

Variable R : comRingType.
Implicit Types x y : R.

Lemma mulrC : @commutative R R *%R.
admit.
Defined.
Canonical mul_comoid := Monoid.ComLaw mulrC.
Lemma mulrCA : @left_commutative R R *%R.
admit.
Defined.
Lemma mulrAC : @right_commutative R R *%R.
admit.
Defined.
Lemma mulrACA : @interchange R *%R *%R.
admit.
Defined.

Lemma exprMn n : {morph (fun x => x ^+ n) : x y / x * y}.
admit.
Defined.

Lemma prodrXl n I r (P : pred I) (F : I -> R) :
  \prod_(i <- r | P i) F i ^+ n = (\prod_(i <- r | P i) F i) ^+ n.
admit.
Defined.

Lemma prodr_undup_exp_count (I : eqType) r (P : pred I) (F : I -> R) :
  \prod_(i <- undup r | P i) F i ^+ count_mem i r = \prod_(i <- r | P i) F i.
admit.
Defined.

Lemma exprDn x y n :
  (x + y) ^+ n = \sum_(i < n.+1) (x ^+ (n - i) * y ^+ i) *+ 'C(n, i).
admit.
Defined.

Lemma exprBn x y n :
  (x - y) ^+ n =
     \sum_(i < n.+1) ((-1) ^+ i * x ^+ (n - i) * y ^+ i) *+ 'C(n, i).
admit.
Defined.

Lemma subrXX x y n :
  x ^+ n - y ^+ n = (x - y) * (\sum_(i < n) x ^+ (n.-1 - i) * y ^+ i).
admit.
Defined.

Lemma sqrrD x y : (x + y) ^+ 2 = x ^+ 2 + x * y *+ 2 + y ^+ 2.
admit.
Defined.

Lemma sqrrB x y : (x - y) ^+ 2 = x ^+ 2 - x * y *+ 2 + y ^+ 2.
admit.
Defined.

Lemma subr_sqr x y : x ^+ 2 - y ^+ 2 = (x - y) * (x + y).
admit.
Defined.

Lemma subr_sqrDB x y : (x + y) ^+ 2 - (x - y) ^+ 2 = x * y *+ 4.
admit.
Defined.

Section FrobeniusAutomorphism.

Variables (p : nat) (charRp : p \in [char R]).

Lemma Frobenius_aut_is_rmorphism : rmorphism (Frobenius_aut charRp).
admit.
Defined.

Canonical Frobenius_aut_additive := Additive Frobenius_aut_is_rmorphism.
Canonical Frobenius_aut_rmorphism := RMorphism Frobenius_aut_is_rmorphism.

End FrobeniusAutomorphism.

Lemma exprDn_char x y n : [char R].-nat n -> (x + y) ^+ n = x ^+ n + y ^+ n.
admit.
Defined.

Lemma rmorph_comm (S : ringType) (f : {rmorphism R -> S}) x y :
  comm (f x) (f y).
admit.
Defined.

Section ScaleLinear.

Variables (U V : lmodType R) (b : R) (f : {linear U -> V}).

Lemma scale_is_scalable : scalable ( *:%R b : V -> V).
admit.
Defined.
Canonical scale_linear := AddLinear scale_is_scalable.

Lemma scale_fun_is_scalable : scalable (b \*: f).
admit.
Defined.
Canonical scale_fun_linear := AddLinear scale_fun_is_scalable.

End ScaleLinear.

End ComRingTheory.

Module Algebra.

Section Mixin.

Variables (R : ringType) (A : lalgType R).

Definition axiom := forall k (x y : A), k *: (x * y) = x * (k *: y).

Lemma comm_axiom : phant A -> commutative (@mul A) -> axiom.
admit.
Defined.

End Mixin.

Section ClassDef.

Variable R : ringType.

Set Primitive Projections.
Record class_of (T : Type) : Type := Class {
  base : Lalgebra.class_of R T;
  mixin : axiom (Lalgebra.Pack _ base)
}.
Unset Primitive Projections.
Local Coercion base : class_of >-> Lalgebra.class_of.

Structure type (phR : phant R) := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variable (phR : phant R) (T : Type) (cT : type phR).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack phR T c.

Definition pack b0 (ax0 : @axiom R b0) :=
  fun bT b & phant_id (@Lalgebra.class R phR bT) b =>
  fun   ax & phant_id ax0 ax => Pack phR (@Class T b ax).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition zmodType := @Zmodule.Pack cT class.
Definition ringType := @Ring.Pack cT class.
Definition lmodType := @Lmodule.Pack R phR cT class.
Definition lalgType := @Lalgebra.Pack R phR cT class.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Lalgebra.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> Ring.type.
Canonical ringType.
Coercion lmodType : type >-> Lmodule.type.
Canonical lmodType.
Coercion lalgType : type >-> Lalgebra.type.
Canonical lalgType.
Notation algType R := (type (Phant R)).
Notation AlgType R A ax := (@pack _ (Phant R) A _ ax _ _ id _ id).
Notation CommAlgType R A := (AlgType R A (comm_axiom (Phant A) (@mulrC _))).
Notation "[ 'algType' R 'of' T 'for' cT ]" := (@clone _ (Phant R) T cT _ idfun)
  (at level 0, format "[ 'algType'  R  'of'  T  'for'  cT ]")
  : form_scope.
Notation "[ 'algType' R 'of' T ]" := (@clone _ (Phant R) T _ _ id)
  (at level 0, format "[ 'algType'  R  'of'  T ]") : form_scope.
End Exports.

End Algebra.
Import Algebra.Exports.

Module ComAlgebra.

Section ClassDef.

Variable R : ringType.

Set Primitive Projections.
Record class_of (T : Type) : Type := Class {
  base : Algebra.class_of R T;
  mixin : commutative (Ring.mul base)
}.
Unset Primitive Projections.
Definition base2 R m := ComRing.Class (@mixin R m).
Local Coercion base : class_of >-> Algebra.class_of.
Local Coercion base2 : class_of >-> ComRing.class_of.

Structure type (phR : phant R) := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variable (phR : phant R) (T : Type) (cT : type phR).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Definition pack :=
  fun bT b & phant_id (@Algebra.class R phR bT) (b : Algebra.class_of R T) =>
  fun mT m & phant_id (ComRing.mixin (ComRing.class mT)) m =>
  Pack (Phant R) (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition zmodType := @Zmodule.Pack cT class.
Definition ringType := @Ring.Pack cT class.
Definition comRingType := @ComRing.Pack cT class.
Definition lmodType := @Lmodule.Pack R phR cT class.
Definition lalgType := @Lalgebra.Pack R phR cT class.
Definition algType := @Algebra.Pack R phR cT class.
Definition lmod_comRingType := @Lmodule.Pack R phR comRingType class.
Definition lalg_comRingType := @Lalgebra.Pack R phR comRingType class.
Definition alg_comRingType := @Algebra.Pack R phR comRingType class.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Algebra.class_of.
Coercion base2 : class_of >-> ComRing.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> Ring.type.
Canonical ringType.
Coercion comRingType : type >-> ComRing.type.
Canonical comRingType.
Coercion lmodType : type >-> Lmodule.type.
Canonical lmodType.
Coercion lalgType : type >-> Lalgebra.type.
Canonical lalgType.
Coercion algType : type >-> Algebra.type.
Canonical algType.
Canonical lmod_comRingType.
Canonical lalg_comRingType.
Canonical alg_comRingType.

Notation comAlgType R := (type (Phant R)).
Notation "[ 'comAlgType' R 'of' T ]" := (@pack _ (Phant R) T _ _ id _ _ id)
  (at level 0, format "[ 'comAlgType'  R  'of'  T ]") : form_scope.
End Exports.

End ComAlgebra.
Import ComAlgebra.Exports.

Section AlgebraTheory.

Variables (R : comRingType) (A : algType R).
Implicit Types (k : R) (x y : A).

Lemma scalerAr k x y : k *: (x * y) = x * (k *: y).
admit.
Defined.

Lemma scalerCA k x y : k *: x * y = x * (k *: y).
admit.
Defined.

Lemma mulr_algr a x : x * a%:A = a *: x.
admit.
Defined.

Lemma comm_alg a x : comm a%:A x.
admit.
Defined.

Lemma exprZn k x n : (k *: x) ^+ n = k ^+ n *: x ^+ n.
admit.
Defined.

Lemma scaler_prod I r (P : pred I) (F : I -> R) (G : I -> A) :
  \prod_(i <- r | P i) (F i *: G i) =
    \prod_(i <- r | P i) F i *: \prod_(i <- r | P i) G i.
admit.
Defined.

Lemma scaler_prodl (I : finType) (S : pred I) (F : I -> A) k :
  \prod_(i in S) (k *: F i)  = k ^+ #|S| *: \prod_(i in S) F i.
admit.
Defined.

Lemma scaler_prodr (I : finType) (S : pred I) (F : I -> R) x :
  \prod_(i in S) (F i *: x)  = \prod_(i in S) F i *: x ^+ #|S|.
admit.
Defined.

Canonical regular_comRingType := [comRingType of R^o].
Canonical regular_algType := CommAlgType R R^o.
Canonical regular_comAlgType := [comAlgType R of R^o].

Variables (U : lmodType R) (a : A) (f : {linear U -> A}).

Lemma mull_fun_is_scalable : scalable (a \*o f).
admit.
Defined.
Canonical mull_fun_linear := AddLinear mull_fun_is_scalable.

End AlgebraTheory.

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

Set Primitive Projections.
Record class_of (R : Type) : Type := Class {
  base : Ring.class_of R;
  mixin : mixin_of (Ring.Pack base)
}.
Unset Primitive Projections.
Local Coercion base : class_of >-> Ring.class_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.

Definition pack b0 (m0 : mixin_of (@Ring.Pack T b0)) :=
  fun bT b & phant_id (Ring.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition zmodType := @Zmodule.Pack cT class.
Definition ringType := @Ring.Pack cT class.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Ring.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> Ring.type.
Canonical ringType.
Notation unitRingType := type.
Notation UnitRingType T m := (@pack T _ m _ _ id _ id).
Notation UnitRingMixin := EtaMixin.
Notation "[ 'unitRingType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'unitRingType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'unitRingType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'unitRingType'  'of'  T ]") : form_scope.
End Exports.

End UnitRing.
Import UnitRing.Exports.

Definition unit {R : unitRingType} :=
  [qualify a u : R | UnitRing.unit (UnitRing.class R) u].
Fact unit_key R : pred_key (@unit R).
admit.
Defined.
Canonical unit_keyed R := KeyedQualifier (@unit_key R).
Definition inv {R : unitRingType} : R -> R := UnitRing.inv (UnitRing.class R).

Local Notation "x ^-1" := (inv x).
Local Notation "x / y" := (x * y^-1).
Local Notation "x ^- n" := ((x ^+ n)^-1).

Section UnitRingTheory.

Variable R : unitRingType.
Implicit Types x y : R.

Lemma divrr : {in unit, right_inverse 1 (@inv R) *%R}.
admit.
Defined.
Definition mulrV := divrr.

Lemma mulVr : {in unit, left_inverse 1 (@inv R) *%R}.
admit.
Defined.

Lemma invr_out x : x \isn't a unit -> x^-1 = x.
admit.
Defined.

Lemma unitrP x : reflect (exists y, y * x = 1 /\ x * y = 1) (x \is a unit).
admit.
Defined.

Lemma mulKr : {in unit, left_loop (@inv R) *%R}.
admit.
Defined.

Lemma mulVKr : {in unit, rev_left_loop (@inv R) *%R}.
admit.
Defined.

Lemma mulrK : {in unit, right_loop (@inv R) *%R}.
admit.
Defined.

Lemma mulrVK : {in unit, rev_right_loop (@inv R) *%R}.
admit.
Defined.
Definition divrK := mulrVK.

Lemma mulrI : {in @unit R, right_injective *%R}.
admit.
Defined.

Lemma mulIr : {in @unit R, left_injective *%R}.
admit.
Defined.

 
Lemma telescope_prodr n m (f : nat -> R) :
    (forall k, n < k < m -> f k \is a unit) -> n < m ->
  \prod_(n <= k < m) (f k / f k.+1) = f n / f m.
admit.
Defined.

Lemma commrV x y : comm x y -> comm x y^-1.
admit.
Defined.

Lemma unitrE x : (x \is a unit) = (x / x == 1).
admit.
Defined.

Lemma invrK : involutive (@inv R).
admit.
Defined.

Lemma invr_inj : injective (@inv R).
admit.
Defined.

Lemma unitrV x : (x^-1 \in unit) = (x \in unit).
admit.
Defined.

Lemma unitr1 : 1 \in @unit R.
admit.
Defined.

Lemma invr1 : 1^-1 = 1 :> R.
admit.
Defined.

Lemma div1r x : 1 / x = x^-1.
admit.
Defined.
Lemma divr1 x : x / 1 = x.
admit.
Defined.

Lemma natr_div m d :
  d %| m -> d%:R \is a @unit R -> (m %/ d)%:R = m%:R / d%:R :> R.
admit.
Defined.

Lemma divrI : {in unit, right_injective (fun x y => x / y)}.
admit.
Defined.

Lemma divIr : {in unit, left_injective (fun x y => x / y)}.
admit.
Defined.

Lemma unitr0 : (0 \is a @unit R) = false.
admit.
Defined.

Lemma invr0 : 0^-1 = 0 :> R.
admit.
Defined.

Lemma unitrN1 : -1 \is a @unit R.
admit.
Defined.

Lemma invrN1 : (-1)^-1 = -1 :> R.
admit.
Defined.

Lemma invr_sign n : ((-1) ^- n) = (-1) ^+ n :> R.
admit.
Defined.

Lemma unitrMl x y : y \is a unit -> (x * y \is a unit) = (x \is a unit).
admit.
Defined.

Lemma unitrMr x y : x \is a unit -> (x * y \is a unit) = (y \is a unit).
admit.
Defined.

Lemma invrM : {in unit &, forall x y, (x * y)^-1 = y^-1 * x^-1}.
admit.
Defined.

Lemma unitrM_comm x y :
  comm x y -> (x * y \is a unit) = (x \is a unit) && (y \is a unit).
admit.
Defined.

Lemma unitrX x n : x \is a unit -> x ^+ n \is a unit.
admit.
Defined.

Lemma unitrX_pos x n : n > 0 -> (x ^+ n \in unit) = (x \in unit).
admit.
Defined.

Lemma exprVn x n : x^-1 ^+ n = x ^- n.
admit.
Defined.

Lemma exprB m n x : n <= m -> x \is a unit -> x ^+ (m - n) = x ^+ m / x ^+ n.
admit.
Defined.

Lemma invr_neq0 x : x != 0 -> x^-1 != 0.
admit.
Defined.

Lemma invr_eq0 x : (x^-1 == 0) = (x == 0).
admit.
Defined.

Lemma invr_eq1 x : (x^-1 == 1) = (x == 1).
admit.
Defined.

Lemma rev_unitrP (x y : R^c) : y * x = 1 /\ x * y = 1 -> x \is a unit.
admit.
Defined.

Definition converse_unitRingMixin :=
  @UnitRing.Mixin _ (unit : {pred R^c}) _ mulrV mulVr rev_unitrP invr_out.
Canonical converse_unitRingType := UnitRingType R^c converse_unitRingMixin.
Canonical regular_unitRingType := [unitRingType of R^o].

Section ClosedPredicates.

Variables S : {pred R}.

Definition invr_closed := {in S, forall x, x^-1 \in S}.
Definition divr_2closed := {in S &, forall x y, x / y \in S}.
Definition divr_closed := 1 \in S /\ divr_2closed.
Definition sdivr_closed := -1 \in S /\ divr_2closed.
Definition divring_closed := [/\ 1 \in S, subr_2closed S & divr_2closed].

Lemma divr_closedV : divr_closed -> invr_closed.
admit.
Defined.

Lemma divr_closedM : divr_closed -> mulr_closed S.
admit.
Defined.

Lemma sdivr_closed_div : sdivr_closed -> divr_closed.
admit.
Defined.

Lemma sdivr_closedM : sdivr_closed -> smulr_closed S.
admit.
Defined.

Lemma divring_closedBM : divring_closed -> subring_closed S.
admit.
Defined.

Lemma divring_closed_div : divring_closed -> sdivr_closed.
admit.
Defined.

End ClosedPredicates.

End UnitRingTheory.

Arguments invrK {R}.
Arguments invr_inj {R} [x1 x2].

Section UnitRingMorphism.

Variables (R S : unitRingType) (f : {rmorphism R -> S}).

Lemma rmorph_unit x : x \in unit -> f x \in unit.
admit.
Defined.

Lemma rmorphV : {in unit, {morph f: x / x^-1}}.
admit.
Defined.

Lemma rmorph_div x y : y \in unit -> f (x / y) = f x / f y.
admit.
Defined.

End UnitRingMorphism.

Module ComUnitRing.

Section Mixin.

Variables (R : comRingType) (unit : pred R) (inv : R -> R).
Hypothesis mulVx : {in unit, left_inverse 1 inv *%R}.
Hypothesis unitPl : forall x y, y * x = 1 -> unit x.

Fact mulC_mulrV : {in unit, right_inverse 1 inv *%R}.
admit.
Defined.

Fact mulC_unitP x y : y * x = 1 /\ x * y = 1 -> unit x.
Proof.
by case=> yx _; apply: unitPl yx.
Qed.

Definition Mixin := UnitRingMixin mulVx mulC_mulrV mulC_unitP.

End Mixin.

Section ClassDef.

Set Primitive Projections.
Record class_of (R : Type) : Type := Class {
  base : ComRing.class_of R;
  mixin : UnitRing.mixin_of (Ring.Pack base)
}.
Unset Primitive Projections.
Local Coercion base : class_of >-> ComRing.class_of.
Definition base2 R m := UnitRing.Class (@mixin R m).
Local Coercion base2 : class_of >-> UnitRing.class_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Definition pack :=
  fun bT b & phant_id (ComRing.class bT) (b : ComRing.class_of T) =>
  fun mT m & phant_id (UnitRing.class mT) (@UnitRing.Class T b m) =>
  Pack (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition zmodType := @Zmodule.Pack cT class.
Definition ringType := @Ring.Pack cT class.
Definition comRingType := @ComRing.Pack cT class.
Definition unitRingType := @UnitRing.Pack cT class.
Definition com_unitRingType := @UnitRing.Pack comRingType class.

End ClassDef.

Module Import Exports.
Coercion base : class_of >-> ComRing.class_of.
Coercion mixin : class_of >-> UnitRing.mixin_of.
Coercion base2 : class_of >-> UnitRing.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> Ring.type.
Canonical ringType.
Coercion comRingType : type >-> ComRing.type.
Canonical comRingType.
Coercion unitRingType : type >-> UnitRing.type.
Canonical unitRingType.
Canonical com_unitRingType.
Notation comUnitRingType := type.
Notation ComUnitRingMixin := Mixin.
Notation "[ 'comUnitRingType' 'of' T ]" := (@pack T _ _ id _ _ id)
  (at level 0, format "[ 'comUnitRingType'  'of'  T ]") : form_scope.
End Exports.

End ComUnitRing.
Import ComUnitRing.Exports.

Module UnitAlgebra.

Section ClassDef.

Variable R : ringType.

Set Primitive Projections.
Record class_of (T : Type) : Type := Class {
  base : Algebra.class_of R T;
  mixin : GRing.UnitRing.mixin_of (Ring.Pack base)
}.
Unset Primitive Projections.
Definition base2 R m := UnitRing.Class (@mixin R m).
Local Coercion base : class_of >-> Algebra.class_of.
Local Coercion base2 : class_of >-> UnitRing.class_of.

Structure type (phR : phant R) := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variable (phR : phant R) (T : Type) (cT : type phR).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Definition pack :=
  fun bT b & phant_id (@Algebra.class R phR bT) (b : Algebra.class_of R T) =>
  fun mT m & phant_id (UnitRing.mixin (UnitRing.class mT)) m =>
  Pack (Phant R) (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition zmodType := @Zmodule.Pack cT class.
Definition ringType := @Ring.Pack cT class.
Definition unitRingType := @UnitRing.Pack cT class.
Definition lmodType := @Lmodule.Pack R phR cT class.
Definition lalgType := @Lalgebra.Pack R phR cT class.
Definition algType := @Algebra.Pack R phR cT class.
Definition lmod_unitRingType := @Lmodule.Pack R phR unitRingType class.
Definition lalg_unitRingType := @Lalgebra.Pack R phR unitRingType class.
Definition alg_unitRingType := @Algebra.Pack R phR unitRingType class.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Algebra.class_of.
Coercion base2 : class_of >-> UnitRing.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> Ring.type.
Canonical ringType.
Coercion unitRingType : type >-> UnitRing.type.
Canonical unitRingType.
Coercion lmodType : type >-> Lmodule.type.
Canonical lmodType.
Coercion lalgType : type >-> Lalgebra.type.
Canonical lalgType.
Coercion algType : type >-> Algebra.type.
Canonical algType.
Canonical lmod_unitRingType.
Canonical lalg_unitRingType.
Canonical alg_unitRingType.
Notation unitAlgType R := (type (Phant R)).
Notation "[ 'unitAlgType' R 'of' T ]" := (@pack _ (Phant R) T _ _ id _ _ id)
  (at level 0, format "[ 'unitAlgType'  R  'of'  T ]") : form_scope.
End Exports.

End UnitAlgebra.
Import UnitAlgebra.Exports.

Module ComUnitAlgebra.

Section ClassDef.

Variable R : ringType.

Set Primitive Projections.
Record class_of (T : Type) : Type := Class {
  base : ComAlgebra.class_of R T;
  mixin : GRing.UnitRing.mixin_of (ComRing.Pack base)
}.
Unset Primitive Projections.
Definition base2 R m := UnitAlgebra.Class (@mixin R m).
Definition base3 R m := ComUnitRing.Class (@mixin R m).
Local Coercion base : class_of >-> ComAlgebra.class_of.
Local Coercion base2 : class_of >-> UnitAlgebra.class_of.
Local Coercion base3 : class_of >-> ComUnitRing.class_of.

Structure type (phR : phant R) := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variable (phR : phant R) (T : Type) (cT : type phR).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Definition pack :=
  fun bT b & phant_id (@ComAlgebra.class R phR bT) (b : ComAlgebra.class_of R T) =>
  fun mT m & phant_id (UnitRing.mixin (UnitRing.class mT)) m =>
  Pack (Phant R) (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition zmodType := @Zmodule.Pack cT class.
Definition ringType := @Ring.Pack cT class.
Definition unitRingType := @UnitRing.Pack cT class.
Definition comRingType := @ComRing.Pack cT class.
Definition comUnitRingType := @ComUnitRing.Pack cT class.
Definition lmodType := @Lmodule.Pack R phR cT class.
Definition lalgType := @Lalgebra.Pack R phR cT class.
Definition algType := @Algebra.Pack R phR cT class.
Definition comAlgType := @ComAlgebra.Pack R phR cT class.
Definition unitAlgType := @UnitAlgebra.Pack R phR cT class.
Definition comalg_unitRingType := @ComAlgebra.Pack R phR unitRingType class.
Definition comalg_comUnitRingType :=
  @ComAlgebra.Pack R phR comUnitRingType class.
Definition comalg_unitAlgType := @ComAlgebra.Pack R phR unitAlgType class.
Definition unitalg_comRingType := @UnitAlgebra.Pack R phR comRingType class.
Definition unitalg_comUnitRingType :=
  @UnitAlgebra.Pack R phR comUnitRingType class.
Definition lmod_comUnitRingType := @Lmodule.Pack R phR comUnitRingType class.
Definition lalg_comUnitRingType := @Lalgebra.Pack R phR comUnitRingType class.
Definition alg_comUnitRingType := @Algebra.Pack R phR comUnitRingType class.

End ClassDef.

Module Exports.
Coercion base : class_of >-> ComAlgebra.class_of.
Coercion base2 : class_of >-> UnitAlgebra.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> Ring.type.
Canonical ringType.
Coercion unitRingType : type >-> UnitRing.type.
Canonical unitRingType.
Coercion comRingType : type >-> ComRing.type.
Canonical comRingType.
Coercion comUnitRingType : type >-> ComUnitRing.type.
Canonical comUnitRingType.
Coercion lmodType : type >-> Lmodule.type.
Canonical lmodType.
Coercion lalgType : type >-> Lalgebra.type.
Canonical lalgType.
Coercion algType : type >-> Algebra.type.
Canonical algType.
Coercion comAlgType : type >-> ComAlgebra.type.
Canonical comAlgType.
Coercion unitAlgType : type >-> UnitAlgebra.type.
Canonical unitAlgType.
Canonical comalg_unitRingType.
Canonical comalg_comUnitRingType.
Canonical comalg_unitAlgType.
Canonical unitalg_comRingType.
Canonical unitalg_comUnitRingType.
Canonical lmod_comUnitRingType.
Canonical lalg_comUnitRingType.
Canonical alg_comUnitRingType.

Notation comUnitAlgType R := (type (Phant R)).
Notation "[ 'comUnitAlgType' R 'of' T ]" := (@pack _ (Phant R) T _ _ id _ _ id)
  (at level 0, format "[ 'comUnitAlgType'  R  'of'  T ]") : form_scope.
End Exports.

End ComUnitAlgebra.
Import ComUnitAlgebra.Exports.

Section ComUnitRingTheory.

Variable R : comUnitRingType.
Implicit Types x y : R.

Lemma unitrM x y : (x * y \in unit) = (x \in unit) && (y \in unit).
admit.
Defined.

Lemma unitrPr x : reflect (exists y, x * y = 1) (x \in unit).
admit.
Defined.

Lemma mulr1_eq x y : x * y = 1 -> x^-1 = y.
admit.
Defined.

Lemma divr1_eq x y : x / y = 1 -> x = y.
admit.
Defined.

Lemma divKr x : x \is a unit -> {in unit, involutive (fun y => x / y)}.
admit.
Defined.

Lemma expr_div_n x y n : (x / y) ^+ n = x ^+ n / y ^+ n.
admit.
Defined.

Canonical regular_comUnitRingType := [comUnitRingType of R^o].
Canonical regular_unitAlgType := [unitAlgType R of R^o].
Canonical regular_comUnitAlgType := [comUnitAlgType R of R^o].

End ComUnitRingTheory.

Section UnitAlgebraTheory.

Variable (R : comUnitRingType) (A : unitAlgType R).
Implicit Types (k : R) (x y : A).

Lemma scaler_injl : {in unit, @right_injective R A A *:%R}.
admit.
Defined.

Lemma scaler_unit k x : k \in unit -> (k *: x \in unit) = (x \in unit).
admit.
Defined.

Lemma invrZ k x : k \in unit -> x \in unit -> (k *: x)^-1 = k^-1 *: x^-1.
admit.
Defined.

Section ClosedPredicates.

Variables S : {pred A}.

Definition divalg_closed := [/\ 1 \in S, linear_closed S & divr_2closed S].

Lemma divalg_closedBdiv : divalg_closed -> divring_closed S.
admit.
Defined.

Lemma divalg_closedZ : divalg_closed -> subalg_closed S.
admit.
Defined.

End ClosedPredicates.

End UnitAlgebraTheory.

 
Module Pred.

Structure opp V S := Opp {opp_key : pred_key S; _ : @oppr_closed V S}.
Structure add V S := Add {add_key : pred_key S; _ : @addr_closed V S}.
Structure mul R S := Mul {mul_key : pred_key S; _ : @mulr_closed R S}.
Structure zmod V S := Zmod {zmod_add : add S; _ : @oppr_closed V S}.
Structure semiring R S := Semiring {semiring_add : add S; _ : @mulr_closed R S}.
Structure smul R S := Smul {smul_opp : opp S; _ : @mulr_closed R S}.
Structure div R S := Div {div_mul : mul S; _ : @invr_closed R S}.
Structure submod R V S :=
  Submod {submod_zmod : zmod S; _ : @scaler_closed R V S}.
Structure subring R S := Subring {subring_zmod : zmod S; _ : @mulr_closed R S}.
Structure sdiv R S := Sdiv {sdiv_smul : smul S; _ : @invr_closed R S}.
Structure subalg (R : ringType) (A : lalgType R) S :=
  Subalg {subalg_ring : subring S; _ : @scaler_closed R A S}.
Structure divring R S :=
  Divring {divring_ring : subring S; _ : @invr_closed R S}.
Structure divalg (R : ringType) (A : unitAlgType R) S :=
  Divalg {divalg_ring : divring S; _ : @scaler_closed R A S}.

Section Subtyping.

Ltac done := case=> *; assumption.
Fact zmod_oppr R S : @zmod R S -> oppr_closed S.
admit.
Defined.
Fact semiring_mulr R S : @semiring R S -> mulr_closed S.
admit.
Defined.
Fact smul_mulr R S : @smul R S -> mulr_closed S.
admit.
Defined.
Fact submod_scaler R V S : @submod R V S -> scaler_closed S.
admit.
Defined.
Fact subring_mulr R S : @subring R S -> mulr_closed S.
admit.
Defined.
Fact sdiv_invr R S : @sdiv R S -> invr_closed S.
admit.
Defined.
Fact subalg_scaler R A S : @subalg R A S -> scaler_closed S.
admit.
Defined.
Fact divring_invr R S : @divring R S -> invr_closed S.
admit.
Defined.
Fact divalg_scaler R A S : @divalg R A S -> scaler_closed S.
admit.
Defined.

Definition zmod_opp R S (addS : @zmod R S) :=
  Opp (add_key (zmod_add addS)) (zmod_oppr addS).
Definition semiring_mul R S (ringS : @semiring R S) :=
  Mul (add_key (semiring_add ringS)) (semiring_mulr ringS).
Definition smul_mul R S (mulS : @smul R S) :=
  Mul (opp_key (smul_opp mulS)) (smul_mulr mulS).
Definition subring_semi R S (ringS : @subring R S) :=
  Semiring (zmod_add (subring_zmod ringS)) (subring_mulr ringS).
Definition subring_smul R S (ringS : @subring R S) :=
  Smul (zmod_opp (subring_zmod ringS)) (subring_mulr ringS).
Definition sdiv_div R S (divS : @sdiv R S) :=
  Div (smul_mul (sdiv_smul divS)) (sdiv_invr divS).
Definition subalg_submod R A S (algS : @subalg R A S) :=
  Submod (subring_zmod (subalg_ring algS)) (subalg_scaler algS).
Definition divring_sdiv R S (ringS : @divring R S) :=
  Sdiv (subring_smul (divring_ring ringS)) (divring_invr ringS).
Definition divalg_alg R A S (algS : @divalg R A S) :=
  Subalg (divring_ring (divalg_ring algS)) (divalg_scaler algS).

End Subtyping.

Section Extensionality.
 

Lemma opp_ext (U : zmodType) S k (kS : @keyed_pred U S k) :
  oppr_closed kS -> oppr_closed S.
admit.
Defined.

Lemma add_ext (U : zmodType) S k (kS : @keyed_pred U S k) :
  addr_closed kS -> addr_closed S.
admit.
Defined.

Lemma mul_ext (R : ringType) S k (kS : @keyed_pred R S k) :
  mulr_closed kS -> mulr_closed S.
admit.
Defined.

Lemma scale_ext (R : ringType) (U : lmodType R) S k (kS : @keyed_pred U S k) :
  scaler_closed kS -> scaler_closed S.
admit.
Defined.

Lemma inv_ext (R : unitRingType) S k (kS : @keyed_pred R S k) :
  invr_closed kS -> invr_closed S.
admit.
Defined.

End Extensionality.

Module Default.
Definition opp V S oppS := @Opp V S (DefaultPredKey S) oppS.
Definition add V S addS := @Add V S (DefaultPredKey S) addS.
Definition mul R S mulS := @Mul R S (DefaultPredKey S) mulS.
Definition zmod V S addS oppS := @Zmod V S (add addS) oppS.
Definition semiring R S addS mulS := @Semiring R S (add addS) mulS.
Definition smul R S oppS mulS := @Smul R S (opp oppS) mulS.
Definition div R S mulS invS := @Div R S (mul mulS) invS.
Definition submod R V S addS oppS linS := @Submod R V S (zmod addS oppS) linS.
Definition subring R S addS oppS mulS := @Subring R S (zmod addS oppS) mulS.
Definition sdiv R S oppS mulS invS := @Sdiv R S (smul oppS mulS) invS.
Definition subalg R A S addS oppS mulS linS :=
  @Subalg R A S (subring addS oppS mulS) linS.
Definition divring R S addS oppS mulS invS :=
  @Divring R S (subring addS oppS mulS) invS.
Definition divalg R A S addS oppS mulS invS linS :=
  @Divalg R A S (divring addS oppS mulS invS) linS.
End Default.

Module Exports.

Notation oppr_closed := oppr_closed.
Notation addr_closed := addr_closed.
Notation mulr_closed := mulr_closed.
Notation zmod_closed := zmod_closed.
Notation smulr_closed := smulr_closed.
Notation invr_closed := invr_closed.
Notation divr_closed := divr_closed.
Notation scaler_closed := scaler_closed.
Notation linear_closed := linear_closed.
Notation submod_closed := submod_closed.
Notation semiring_closed := semiring_closed.
Notation subring_closed := subring_closed.
Notation sdivr_closed := sdivr_closed.
Notation subalg_closed := subalg_closed.
Notation divring_closed := divring_closed.
Notation divalg_closed := divalg_closed.

Coercion zmod_closedD : zmod_closed >-> addr_closed.
Coercion zmod_closedN : zmod_closed >-> oppr_closed.
Coercion smulr_closedN : smulr_closed >-> oppr_closed.
Coercion smulr_closedM : smulr_closed >-> mulr_closed.
Coercion divr_closedV : divr_closed >-> invr_closed.
Coercion divr_closedM : divr_closed >-> mulr_closed.
Coercion submod_closedZ : submod_closed >-> scaler_closed.
Coercion submod_closedB : submod_closed >-> zmod_closed.
Coercion semiring_closedD : semiring_closed >-> addr_closed.
Coercion semiring_closedM : semiring_closed >-> mulr_closed.
Coercion subring_closedB : subring_closed >-> zmod_closed.
Coercion subring_closedM : subring_closed >-> smulr_closed.
Coercion subring_closed_semi : subring_closed >-> semiring_closed.
Coercion sdivr_closedM : sdivr_closed >-> smulr_closed.
Coercion sdivr_closed_div : sdivr_closed >-> divr_closed.
Coercion subalg_closedZ : subalg_closed >-> submod_closed.
Coercion subalg_closedBM : subalg_closed >-> subring_closed.
Coercion divring_closedBM : divring_closed >-> subring_closed.
Coercion divring_closed_div : divring_closed >-> sdivr_closed.
Coercion divalg_closedZ : divalg_closed >-> subalg_closed.
Coercion divalg_closedBdiv : divalg_closed >-> divring_closed.

Coercion opp_key : opp >-> pred_key.
Coercion add_key : add >-> pred_key.
Coercion mul_key : mul >-> pred_key.
Coercion zmod_opp : zmod >-> opp.
Canonical zmod_opp.
Coercion zmod_add : zmod >-> add.
Coercion semiring_add : semiring >-> add.
Coercion semiring_mul : semiring >-> mul.
Canonical semiring_mul.
Coercion smul_opp : smul >-> opp.
Coercion smul_mul : smul >-> mul.
Canonical smul_mul.
Coercion div_mul : div >-> mul.
Coercion submod_zmod : submod >-> zmod.
Coercion subring_zmod : subring >-> zmod.
Coercion subring_semi : subring >-> semiring.
Canonical subring_semi.
Coercion subring_smul : subring >-> smul.
Canonical subring_smul.
Coercion sdiv_smul : sdiv >-> smul.
Coercion sdiv_div : sdiv >-> div.
Canonical sdiv_div.
Coercion subalg_submod : subalg >-> submod.
Canonical subalg_submod.
Coercion subalg_ring : subalg >-> subring.
Coercion divring_ring : divring >-> subring.
Coercion divring_sdiv : divring >-> sdiv.
Canonical divring_sdiv.
Coercion divalg_alg : divalg >-> subalg.
Canonical divalg_alg.
Coercion divalg_ring : divalg >-> divring.

Notation opprPred := opp.
Notation addrPred := add.
Notation mulrPred := mul.
Notation zmodPred := zmod.
Notation semiringPred := semiring.
Notation smulrPred := smul.
Notation divrPred := div.
Notation submodPred := submod.
Notation subringPred := subring.
Notation sdivrPred := sdiv.
Notation subalgPred := subalg.
Notation divringPred := divring.
Notation divalgPred := divalg.

Definition OpprPred U S k kS NkS := Opp k (@opp_ext U S k kS NkS).
Definition AddrPred U S k kS DkS := Add k (@add_ext U S k kS DkS).
Definition MulrPred R S k kS MkS := Mul k (@mul_ext R S k kS MkS).
Definition ZmodPred U S k kS NkS := Zmod k (@opp_ext U S k kS NkS).
Definition SemiringPred R S k kS MkS := Semiring k (@mul_ext R S k kS MkS).
Definition SmulrPred R S k kS MkS := Smul k (@mul_ext R S k kS MkS).
Definition DivrPred R S k kS VkS := Div k (@inv_ext R S k kS VkS).
Definition SubmodPred R U S k kS ZkS := Submod k (@scale_ext R U S k kS ZkS).
Definition SubringPred R S k kS MkS := Subring k (@mul_ext R S k kS MkS).
Definition SdivrPred R S k kS VkS := Sdiv k (@inv_ext R S k kS VkS).
Definition SubalgPred (R : ringType) (A : lalgType R) S k kS ZkS :=
  Subalg k (@scale_ext R A S k kS ZkS).
Definition DivringPred R S k kS VkS := Divring k (@inv_ext R S k kS VkS).
Definition DivalgPred (R : ringType) (A : unitAlgType R) S k kS ZkS :=
  Divalg k (@scale_ext R A S k kS ZkS).

End Exports.

End Pred.
Import Pred.Exports.

Module DefaultPred.

Canonical Pred.Default.opp.
Canonical Pred.Default.add.
Canonical Pred.Default.mul.
Canonical Pred.Default.zmod.
Canonical Pred.Default.semiring.
Canonical Pred.Default.smul.
Canonical Pred.Default.div.
Canonical Pred.Default.submod.
Canonical Pred.Default.subring.
Canonical Pred.Default.sdiv.
Canonical Pred.Default.subalg.
Canonical Pred.Default.divring.
Canonical Pred.Default.divalg.

End DefaultPred.

Section ZmodulePred.

Variables (V : zmodType) (S : {pred V}).

Section Add.

Variables (addS : addrPred S) (kS : keyed_pred addS).

Lemma rpred0D : addr_closed kS.
admit.
Defined.

Lemma rpred0 : 0 \in kS.
admit.
Defined.

Lemma rpredD : {in kS &, forall u v, u + v \in kS}.
admit.
Defined.

Lemma rpred_sum I r (P : pred I) F :
  (forall i, P i -> F i \in kS) -> \sum_(i <- r | P i) F i \in kS.
admit.
Defined.

Lemma rpredMn n : {in kS, forall u, u *+ n \in kS}.
admit.
Defined.

End Add.

Section Opp.

Variables (oppS : opprPred S) (kS : keyed_pred oppS).

Lemma rpredNr : oppr_closed kS.
admit.
Defined.

Lemma rpredN : {mono -%R: u / u \in kS}.
admit.
Defined.

End Opp.

Section Sub.

Variables (subS : zmodPred S) (kS : keyed_pred subS).

Lemma rpredB : {in kS &, forall u v, u - v \in kS}.
admit.
Defined.

Lemma rpredBC u v : u - v \in kS = (v - u \in kS).
admit.
Defined.

Lemma rpredMNn n : {in kS, forall u, u *- n \in kS}.
admit.
Defined.

Lemma rpredDr x y : x \in kS -> (y + x \in kS) = (y \in kS).
admit.
Defined.

Lemma rpredDl x y : x \in kS -> (x + y \in kS) = (y \in kS).
admit.
Defined.

Lemma rpredBr x y : x \in kS -> (y - x \in kS) = (y \in kS).
admit.
Defined.

Lemma rpredBl x y : x \in kS -> (x - y \in kS) = (y \in kS).
admit.
Defined.

End Sub.

End ZmodulePred.

Section RingPred.

Variables (R : ringType) (S : {pred R}).

Lemma rpredMsign (oppS : opprPred S) (kS : keyed_pred oppS) n x :
  ((-1) ^+ n * x \in kS) = (x \in kS).
admit.
Defined.

Section Mul.

Variables (mulS : mulrPred S) (kS : keyed_pred mulS).

Lemma rpred1M : mulr_closed kS.
admit.
Defined.

Lemma rpred1 : 1 \in kS.
admit.
Defined.

Lemma rpredM : {in kS &, forall u v, u * v \in kS}.
admit.
Defined.

Lemma rpred_prod I r (P : pred I) F :
  (forall i, P i -> F i \in kS) -> \prod_(i <- r | P i) F i \in kS.
admit.
Defined.

Lemma rpredX n : {in kS, forall u, u ^+ n \in kS}.
admit.
Defined.

End Mul.

Lemma rpred_nat (rngS : semiringPred S) (kS : keyed_pred rngS) n : n%:R \in kS.
admit.
Defined.

Lemma rpredN1 (mulS : smulrPred S) (kS : keyed_pred mulS) : -1 \in kS.
admit.
Defined.

Lemma rpred_sign (mulS : smulrPred S) (kS : keyed_pred mulS) n :
  (-1) ^+ n \in kS.
admit.
Defined.

End RingPred.

Section LmodPred.

Variables (R : ringType) (V : lmodType R) (S : {pred V}).

Lemma rpredZsign (oppS : opprPred S) (kS : keyed_pred oppS) n u :
  ((-1) ^+ n *: u \in kS) = (u \in kS).
admit.
Defined.

Lemma rpredZnat (addS : addrPred S) (kS : keyed_pred addS) n :
  {in kS, forall u, n%:R *: u \in kS}.
admit.
Defined.

Lemma rpredZ (linS : submodPred S) (kS : keyed_pred linS) : scaler_closed kS.
admit.
Defined.

End LmodPred.

Section UnitRingPred.

Variable R : unitRingType.

Section Div.

Variables (S : {pred R}) (divS : divrPred S) (kS : keyed_pred divS).

Lemma rpredVr x : x \in kS -> x^-1 \in kS.
admit.
Defined.

Lemma rpredV x : (x^-1 \in kS) = (x \in kS).
admit.
Defined.

Lemma rpred_div : {in kS &, forall x y, x / y \in kS}.
admit.
Defined.

Lemma rpredXN n : {in kS, forall x, x ^- n \in kS}.
admit.
Defined.

Lemma rpredMl x y : x \in kS -> x \is a unit-> (x * y \in kS) = (y \in kS).
admit.
Defined.

Lemma rpredMr x y : x \in kS -> x \is a unit -> (y * x \in kS) = (y \in kS).
admit.
Defined.

Lemma rpred_divr x y : x \in kS -> x \is a unit -> (y / x \in kS) = (y \in kS).
admit.
Defined.

Lemma rpred_divl x y : x \in kS -> x \is a unit -> (x / y \in kS) = (y \in kS).
admit.
Defined.

End Div.

Fact unitr_sdivr_closed : @sdivr_closed R unit.
admit.
Defined.

Canonical unit_opprPred := OpprPred unitr_sdivr_closed.
Canonical unit_mulrPred := MulrPred unitr_sdivr_closed.
Canonical unit_divrPred := DivrPred unitr_sdivr_closed.
Canonical unit_smulrPred := SmulrPred unitr_sdivr_closed.
Canonical unit_sdivrPred := SdivrPred unitr_sdivr_closed.

Implicit Type x : R.

Lemma unitrN x : (- x \is a unit) = (x \is a unit).
admit.
Defined.

Lemma invrN x : (- x)^-1 = - x^-1.
admit.
Defined.

Lemma invr_signM n x : ((-1) ^+ n * x)^-1 = (-1) ^+ n * x^-1.
admit.
Defined.

Lemma divr_signM (b1 b2 : bool) x1 x2:
  ((-1) ^+ b1 * x1) / ((-1) ^+ b2 * x2) = (-1) ^+ (b1 (+) b2) * (x1 / x2).
admit.
Defined.

End UnitRingPred.

 
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

Bind Scope term_scope with term.
Bind Scope term_scope with formula.
Arguments Add {R} t1%T t2%T.
Arguments Opp {R} t1%T.
Arguments NatMul {R} t1%T n%N.
Arguments Mul {R} t1%T t2%T.
Arguments Inv {R} t1%T.
Arguments Exp {R} t1%T n%N.
Arguments Equal {R} t1%T t2%T.
Arguments Unit {R} t1%T.
Arguments And {R} f1%T f2%T.
Arguments Or {R} f1%T f2%T.
Arguments Implies {R} f1%T f2%T.
Arguments Not {R} f1%T.
Arguments Exists {R} i%N f1%T.
Arguments Forall {R} i%N f1%T.

Arguments Bool {R} b.
Arguments Const {R} x.

Notation True := (Bool true).
Notation False := (Bool false).

Local Notation "''X_' i" := (Var _ i) : term_scope.
Local Notation "n %:R" := (NatConst _ n) : term_scope.
Local Notation "x %:T" := (Const x) : term_scope.
Local Notation "0" := 0%:R%T : term_scope.
Local Notation "1" := 1%:R%T : term_scope.
Local Infix "+" := Add : term_scope.
Local Notation "- t" := (Opp t) : term_scope.
Local Notation "t - u" := (Add t (- u)) : term_scope.
Local Infix "*" := Mul : term_scope.
Local Infix "*+" := NatMul : term_scope.
Local Notation "t ^-1" := (Inv t) : term_scope.
Local Notation "t / u" := (Mul t u^-1) : term_scope.
Local Infix "^+" := Exp : term_scope.
Local Infix "==" := Equal : term_scope.
Local Infix "/\" := And : term_scope.
Local Infix "\/" := Or : term_scope.
Local Infix "==>" := Implies : term_scope.
Local Notation "~ f" := (Not f) : term_scope.
Local Notation "x != y" := (Not (x == y)) : term_scope.
Local Notation "''exists' ''X_' i , f" := (Exists i f) : term_scope.
Local Notation "''forall' ''X_' i , f" := (Forall i f) : term_scope.

Section Substitution.

Variable R : Type.

Fixpoint tsubst (t : term R) (s : nat * term R) :=
  match t with
  | 'X_i => if i == s.1 then s.2 else t
  | _%:T | _%:R => t
  | t1 + t2 => tsubst t1 s + tsubst t2 s
  | - t1 => - tsubst t1 s
  | t1 *+ n => tsubst t1 s *+ n
  | t1 * t2 => tsubst t1 s * tsubst t2 s
  | t1^-1 => (tsubst t1 s)^-1
  | t1 ^+ n => tsubst t1 s ^+ n
  end%T.

Fixpoint fsubst (f : formula R) (s : nat * term R) :=
  match f with
  | Bool _ => f
  | t1 == t2 => tsubst t1 s == tsubst t2 s
  | Unit t1 => Unit (tsubst t1 s)
  | f1 /\ f2 => fsubst f1 s /\ fsubst f2 s
  | f1 \/ f2 => fsubst f1 s \/ fsubst f2 s
  | f1 ==> f2 => fsubst f1 s ==> fsubst f2 s
  | ~ f1 => ~ fsubst f1 s
  | ('exists 'X_i, f1) => 'exists 'X_i, if i == s.1 then f1 else fsubst f1 s
  | ('forall 'X_i, f1) => 'forall 'X_i, if i == s.1 then f1 else fsubst f1 s
  end%T.

End Substitution.

Section EvalTerm.

Variable R : unitRingType.

 
Fixpoint eval (e : seq R) (t : term R) {struct t} : R :=
  match t with
  | ('X_i)%T => e`_i
  | (x%:T)%T => x
  | (n%:R)%T => n%:R
  | (t1 + t2)%T => eval e t1 + eval e t2
  | (- t1)%T => - eval e t1
  | (t1 *+ n)%T => eval e t1 *+ n
  | (t1 * t2)%T => eval e t1 * eval e t2
  | t1^-1%T => (eval e t1)^-1
  | (t1 ^+ n)%T => eval e t1 ^+ n
  end.

Definition same_env (e e' : seq R) := nth 0 e =1 nth 0 e'.

Lemma eq_eval e e' t : same_env e e' -> eval e t = eval e' t.
admit.
Defined.

Lemma eval_tsubst e t s :
  eval e (tsubst t s) = eval (set_nth 0 e s.1 (eval e s.2)) t.
admit.
Defined.

 
Fixpoint holds (e : seq R) (f : formula R) {struct f} : Prop :=
  match f with
  | Bool b => b
  | (t1 == t2)%T => eval e t1 = eval e t2
  | Unit t1 => eval e t1 \in unit
  | (f1 /\ f2)%T => holds e f1 /\ holds e f2
  | (f1 \/ f2)%T => holds e f1 \/ holds e f2
  | (f1 ==> f2)%T => holds e f1 -> holds e f2
  | (~ f1)%T => ~ holds e f1
  | ('exists 'X_i, f1)%T => exists x, holds (set_nth 0 e i x) f1
  | ('forall 'X_i, f1)%T => forall x, holds (set_nth 0 e i x) f1
  end.

Lemma same_env_sym e e' : same_env e e' -> same_env e' e.
admit.
Defined.

 
Lemma eq_holds e e' f : same_env e e' -> holds e f -> holds e' f.
admit.
Defined.

 
Lemma holds_fsubst e f i v :
  holds e (fsubst f (i, v%:T)%T) <-> holds (set_nth 0 e i v) f.
admit.
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

 
Fixpoint ub_var (t : term R) :=
  match t with
  | 'X_i => i.+1
  | t1 + t2 | t1 * t2 => maxn (ub_var t1) (ub_var t2)
  | - t1 | t1 *+ _ | t1 ^+ _ | t1^-1 => ub_var t1
  | _ => 0%N
  end%T.

 
 
Fixpoint to_rterm (t : term R) (r : seq (term R)) (n : nat) {struct t} :=
  match t with
  | t1^-1 =>
    let: (t1', r1) := to_rterm t1 r n in
      ('X_(n + size r1), rcons r1 t1')
  | t1 + t2 =>
    let: (t1', r1) := to_rterm t1 r n in
    let: (t2', r2) := to_rterm t2 r1 n in
      (t1' + t2', r2)
  | - t1 =>
   let: (t1', r1) := to_rterm t1 r n in
     (- t1', r1)
  | t1 *+ m =>
   let: (t1', r1) := to_rterm t1 r n in
     (t1' *+ m, r1)
  | t1 * t2 =>
    let: (t1', r1) := to_rterm t1 r n in
    let: (t2', r2) := to_rterm t2 r1 n in
      (Mul t1' t2', r2)
  | t1 ^+ m =>
       let: (t1', r1) := to_rterm t1 r n in
     (t1' ^+ m, r1)
  | _ => (t, r)
  end%T.

Lemma to_rterm_id t r n : rterm t -> to_rterm t r n = (t, r).
admit.
Defined.

 
 
Definition eq0_rform t1 :=
  let m := ub_var t1 in
  let: (t1', r1) := to_rterm t1 [::] m in
  let fix loop r i := match r with
  | [::] => t1' == 0
  | t :: r' =>
    let f := 'X_i * t == 1 /\ t * 'X_i == 1 in
     'forall 'X_i, (f \/ 'X_i == t /\ ~ ('exists 'X_i,  f)) ==> loop r' i.+1
  end%T
  in loop r1 m.

 
 
Fixpoint to_rform f :=
  match f with
  | Bool b => f
  | t1 == t2 => eq0_rform (t1 - t2)
  | Unit t1 => eq0_rform (t1 * t1^-1 - 1)
  | f1 /\ f2 => to_rform f1 /\ to_rform f2
  | f1 \/ f2 =>  to_rform f1 \/ to_rform f2
  | f1 ==> f2 => to_rform f1 ==> to_rform f2
  | ~ f1 => ~ to_rform f1
  | ('exists 'X_i, f1) => 'exists 'X_i, to_rform f1
  | ('forall 'X_i, f1) => 'forall 'X_i, to_rform f1
  end%T.

 
Lemma to_rform_rformula f : rformula (to_rform f).
admit.
Defined.

 
Lemma to_rformP e f : holds e (to_rform f) <-> holds e f.
admit.
Defined.

 
 

 
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
admit.
Defined.

Implicit Type bc : seq (term R) * seq (term R).

 
 
 

 
Definition and_dnf bcs1 bcs2 :=
  \big[cat/nil]_(bc1 <- bcs1)
     map (fun bc2 => (bc1.1 ++ bc2.1, bc1.2 ++ bc2.2)) bcs2.

 
Fixpoint qf_to_dnf (f : formula R) (neg : bool) {struct f} :=
  match f with
  | Bool b => if b (+) neg then [:: ([::], [::])] else [::]
  | t1 == t2 => [:: if neg then ([::], [:: t1 - t2]) else ([:: t1 - t2], [::])]
  | f1 /\ f2 => (if neg then cat else and_dnf) [rec f1, neg] [rec f2, neg]
  | f1 \/ f2 => (if neg then and_dnf else cat) [rec f1, neg] [rec f2, neg]
  | f1 ==> f2 => (if neg then and_dnf else cat) [rec f1, ~~ neg] [rec f2, neg]
  | ~ f1 => [rec f1, ~~ neg]
  | _ =>  if neg then [:: ([::], [::])] else [::]
  end%T where "[ 'rec' f , neg ]" := (qf_to_dnf f neg).

 
Definition dnf_to_form :=
  let pos_lit t := And (t == 0) in let neg_lit t := And (t != 0) in
  let cls bc := Or (foldr pos_lit True bc.1 /\ foldr neg_lit True bc.2) in
  foldr cls False.

 
Lemma cat_dnfP e bcs1 bcs2 :
  qf_eval e (dnf_to_form (bcs1 ++ bcs2))
    = qf_eval e (dnf_to_form bcs1 \/ dnf_to_form bcs2).
admit.
Defined.

 
Lemma and_dnfP e bcs1 bcs2 :
  qf_eval e (dnf_to_form (and_dnf bcs1 bcs2))
   = qf_eval e (dnf_to_form bcs1 /\ dnf_to_form bcs2).
admit.
Defined.

Lemma qf_to_dnfP e :
  let qev f b := qf_eval e (dnf_to_form (qf_to_dnf f b)) in
  forall f, qf_form f && rformula f -> qev f false = qf_eval e f.
admit.
Defined.

Lemma dnf_to_form_qf bcs : qf_form (dnf_to_form bcs).
admit.
Defined.

Definition dnf_rterm cl := all rterm cl.1 && all rterm cl.2.

Lemma qf_to_dnf_rterm f b : rformula f -> all dnf_rterm (qf_to_dnf f b).
admit.
Defined.

Lemma dnf_to_rform bcs : rformula (dnf_to_form bcs) = all dnf_rterm bcs.
admit.
Defined.

Section If.

Variables (pred_f then_f else_f : formula R).

Definition If := (pred_f /\ then_f \/ ~ pred_f /\ else_f)%T.

Lemma If_form_qf :
  qf_form pred_f -> qf_form then_f -> qf_form else_f -> qf_form If.
admit.
Defined.

Lemma If_form_rf :
  rformula pred_f -> rformula then_f -> rformula else_f -> rformula If.
admit.
Defined.

Lemma eval_If e :
  let ev := qf_eval e in ev If = (if ev pred_f then ev then_f else ev else_f).
admit.
Defined.

End If.

Section Pick.

Variables (I : finType) (pred_f then_f : I -> formula R) (else_f : formula R).

Definition Pick :=
  \big[Or/False]_(p : {ffun pred I})
    ((\big[And/True]_i (if p i then pred_f i else ~ pred_f i))
    /\ (if pick p is Some i then then_f i else else_f))%T.

Lemma Pick_form_qf :
   (forall i, qf_form (pred_f i)) ->
   (forall i, qf_form (then_f i)) ->
    qf_form else_f ->
  qf_form Pick.
admit.
Defined.

Lemma eval_Pick e (qev := qf_eval e) :
  let P i := qev (pred_f i) in
  qev Pick = (if pick P is Some i then qev (then_f i) else qev else_f).
admit.
Defined.

End Pick.

Section MultiQuant.

Variable f : formula R.
Implicit Types (I : seq nat) (e : seq R).

Lemma foldExistsP I e :
  (exists2 e', {in [predC I], same_env e e'} & holds e' f)
    <-> holds e (foldr Exists f I).
admit.
Defined.

Lemma foldForallP I e :
  (forall e', {in [predC I], same_env e e'} -> holds e' f)
    <-> holds e (foldr Forall f I).
admit.
Defined.

End MultiQuant.

End EvalTerm.

Prenex Implicits dnf_rterm.

Module IntegralDomain.

Definition axiom (R : ringType) :=
  forall x y : R, x * y = 0 -> (x == 0) || (y == 0).

Section ClassDef.

Set Primitive Projections.
Record class_of (R : Type) : Type :=
  Class {base : ComUnitRing.class_of R; mixin : axiom (Ring.Pack base)}.
Unset Primitive Projections.
Local Coercion base : class_of >-> ComUnitRing.class_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variable (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.

Definition pack b0 (m0 : axiom (@Ring.Pack T b0)) :=
  fun bT b & phant_id (ComUnitRing.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition zmodType := @Zmodule.Pack cT class.
Definition ringType := @Ring.Pack cT class.
Definition comRingType := @ComRing.Pack cT class.
Definition unitRingType := @UnitRing.Pack cT class.
Definition comUnitRingType := @ComUnitRing.Pack cT class.

End ClassDef.

Module Exports.
Coercion base : class_of >-> ComUnitRing.class_of.
Arguments mixin [R] c [x y].
Coercion mixin : class_of >-> axiom.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> Ring.type.
Canonical ringType.
Coercion comRingType : type >-> ComRing.type.
Canonical comRingType.
Coercion unitRingType : type >-> UnitRing.type.
Canonical unitRingType.
Coercion comUnitRingType : type >-> ComUnitRing.type.
Canonical comUnitRingType.
Notation idomainType := type.
Notation IdomainType T m := (@pack T _ m _ _ id _ id).
Notation "[ 'idomainType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'idomainType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'idomainType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'idomainType'  'of'  T ]") : form_scope.
End Exports.

End IntegralDomain.
Import IntegralDomain.Exports.

Section IntegralDomainTheory.

Variable R : idomainType.
Implicit Types x y : R.

Lemma mulf_eq0 x y : (x * y == 0) = (x == 0) || (y == 0).
admit.
Defined.

Lemma prodf_eq0 (I : finType) (P : pred I) (F : I -> R) :
  reflect (exists2 i, P i & (F i == 0)) (\prod_(i | P i) F i == 0).
admit.
Defined.

Lemma prodf_seq_eq0 I r (P : pred I) (F : I -> R) :
  (\prod_(i <- r | P i) F i == 0) = has (fun i => P i && (F i == 0)) r.
admit.
Defined.

Lemma mulf_neq0 x y : x != 0 -> y != 0 -> x * y != 0.
admit.
Defined.

Lemma prodf_neq0 (I : finType) (P : pred I) (F : I -> R) :
  reflect (forall i, P i -> (F i != 0)) (\prod_(i | P i) F i != 0).
admit.
Defined.

Lemma prodf_seq_neq0 I r (P : pred I) (F : I -> R) :
  (\prod_(i <- r | P i) F i != 0) = all (fun i => P i ==> (F i != 0)) r.
admit.
Defined.

Lemma expf_eq0 x n : (x ^+ n == 0) = (n > 0) && (x == 0).
admit.
Defined.

Lemma sqrf_eq0 x : (x ^+ 2 == 0) = (x == 0).
admit.
Defined.

Lemma expf_neq0 x m : x != 0 -> x ^+ m != 0.
admit.
Defined.

Lemma natf_neq0 n : (n%:R != 0 :> R) = [char R]^'.-nat n.
admit.
Defined.

Lemma natf0_char n : n > 0 -> n%:R == 0 :> R -> exists p, p \in [char R].
admit.
Defined.

Lemma charf'_nat n : [char R]^'.-nat n = (n%:R != 0 :> R).
admit.
Defined.

Lemma charf0P : [char R] =i pred0 <-> (forall n, (n%:R == 0 :> R) = (n == 0)%N).
admit.
Defined.

Lemma eqf_sqr x y : (x ^+ 2 == y ^+ 2) = (x == y) || (x == - y).
admit.
Defined.

Lemma mulfI x : x != 0 -> injective ( *%R x).
admit.
Defined.

Lemma mulIf x : x != 0 -> injective ( *%R^~ x).
admit.
Defined.

Lemma divfI x : x != 0 -> injective (fun y => x / y).
admit.
Defined.

Lemma divIf y : y != 0 -> injective (fun x => x / y).
admit.
Defined.

Lemma sqrf_eq1 x : (x ^+ 2 == 1) = (x == 1) || (x == -1).
admit.
Defined.

Lemma expfS_eq1 x n :
  (x ^+ n.+1 == 1) = (x == 1) || (\sum_(i < n.+1) x ^+ i == 0).
admit.
Defined.

Lemma lregP x : reflect (lreg x) (x != 0).
admit.
Defined.

Lemma rregP x : reflect (rreg x) (x != 0).
admit.
Defined.

Canonical regular_idomainType := [idomainType of R^o].

End IntegralDomainTheory.

Arguments lregP {R x}.
Arguments rregP {R x}.

Module Field.

Definition mixin_of (R : unitRingType) := forall x : R, x != 0 -> x \in unit.

Lemma IdomainMixin R : mixin_of R -> IntegralDomain.axiom R.
admit.
Defined.

Section Mixins.

Definition axiom (R : ringType) inv := forall x : R, x != 0 -> inv x * x = 1.

Variables (R : comRingType) (inv : R -> R).
Hypotheses (mulVf : axiom inv) (inv0 : inv 0 = 0).

Fact intro_unit (x y : R) : y * x = 1 -> x != 0.
admit.
Defined.

Fact inv_out : {in predC (predC1 0), inv =1 id}.
Proof.
by move=> x /negbNE/eqP->.
Qed.

Definition UnitMixin := ComUnitRing.Mixin mulVf intro_unit inv_out.

Definition UnitRingType := [comUnitRingType of UnitRingType R UnitMixin].

Definition IdomainType :=
  IdomainType UnitRingType (@IdomainMixin UnitRingType (fun => id)).

Lemma Mixin : mixin_of IdomainType.
admit.
Defined.

End Mixins.

Section ClassDef.

Set Primitive Projections.
Record class_of (F : Type) : Type := Class {
  base : IntegralDomain.class_of F;
  mixin : mixin_of (UnitRing.Pack base)
}.
Unset Primitive Projections.
Local Coercion base : class_of >-> IntegralDomain.class_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variable (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.

Definition pack b0 (m0 : mixin_of (@UnitRing.Pack T b0)) :=
  fun bT b & phant_id (IntegralDomain.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition zmodType := @Zmodule.Pack cT class.
Definition ringType := @Ring.Pack cT class.
Definition comRingType := @ComRing.Pack cT class.
Definition unitRingType := @UnitRing.Pack cT class.
Definition comUnitRingType := @ComUnitRing.Pack cT class.
Definition idomainType := @IntegralDomain.Pack cT class.

End ClassDef.

Module Exports.
Coercion base : class_of >-> IntegralDomain.class_of.
Arguments mixin [F] c [x].
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> Ring.type.
Canonical ringType.
Coercion comRingType : type >-> ComRing.type.
Canonical comRingType.
Coercion unitRingType : type >-> UnitRing.type.
Canonical unitRingType.
Coercion comUnitRingType : type >-> ComUnitRing.type.
Canonical comUnitRingType.
Coercion idomainType : type >-> IntegralDomain.type.
Canonical idomainType.
Notation fieldType := type.
Notation FieldType T m := (@pack T _ m _ _ id _ id).
Arguments Mixin {R inv} mulVf inv0 [x] nz_x.
Notation FieldUnitMixin := UnitMixin.
Notation FieldIdomainMixin := IdomainMixin.
Notation FieldMixin := Mixin.
Notation "[ 'fieldType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'fieldType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'fieldType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'fieldType'  'of'  T ]") : form_scope.
End Exports.

End Field.
Import Field.Exports.

Section FieldTheory.

Variable F : fieldType.
Implicit Types x y : F.

Lemma fieldP : Field.mixin_of F.
admit.
Defined.

Lemma unitfE x : (x \in unit) = (x != 0).
admit.
Defined.

Lemma mulVf x : x != 0 -> x^-1 * x = 1.
admit.
Defined.
Lemma divff x : x != 0 -> x / x = 1.
admit.
Defined.
Definition mulfV := divff.
Lemma mulKf x : x != 0 -> cancel ( *%R x) ( *%R x^-1).
admit.
Defined.
Lemma mulVKf x : x != 0 -> cancel ( *%R x^-1) ( *%R x).
admit.
Defined.
Lemma mulfK x : x != 0 -> cancel ( *%R^~ x) ( *%R^~ x^-1).
admit.
Defined.
Lemma mulfVK x : x != 0 -> cancel ( *%R^~ x^-1) ( *%R^~ x).
admit.
Defined.
Definition divfK := mulfVK.

Lemma invfM : {morph @inv F : x y / x * y}.
admit.
Defined.

Lemma invf_div x y : (x / y)^-1 = y / x.
admit.
Defined.

Lemma divKf x : x != 0 -> involutive (fun y => x / y).
admit.
Defined.

Lemma expfB_cond m n x : (x == 0) + n <= m -> x ^+ (m - n) = x ^+ m / x ^+ n.
admit.
Defined.

Lemma expfB m n x : n < m -> x ^+ (m - n) = x ^+ m / x ^+ n.
admit.
Defined.

Lemma prodfV I r (P : pred I) (E : I -> F) :
  \prod_(i <- r | P i) (E i)^-1 = (\prod_(i <- r | P i) E i)^-1.
admit.
Defined.

Lemma prodf_div I r (P : pred I) (E D : I -> F) :
  \prod_(i <- r | P i) (E i / D i) =
     \prod_(i <- r | P i) E i / \prod_(i <- r | P i) D i.
admit.
Defined.

Lemma telescope_prodf n m (f : nat -> F) :
    (forall k, n < k < m -> f k != 0) -> n < m ->
  \prod_(n <= k < m) (f k.+1 / f k) = f m / f n.
admit.
Defined.

Lemma addf_div x1 y1 x2 y2 :
  y1 != 0 -> y2 != 0 -> x1 / y1 + x2 / y2 = (x1 * y2 + x2 * y1) / (y1 * y2).
admit.
Defined.

Lemma mulf_div x1 y1 x2 y2 : (x1 / y1) * (x2 / y2) = (x1 * x2) / (y1 * y2).
admit.
Defined.

Lemma char0_natf_div :
  [char F] =i pred0 -> forall m d, d %| m -> (m %/ d)%:R = m%:R / d%:R :> F.
admit.
Defined.

Section FieldMorphismInj.

Variables (R : ringType) (f : {rmorphism F -> R}).

Lemma fmorph_eq0 x : (f x == 0) = (x == 0).
admit.
Defined.

Lemma fmorph_inj : injective f.
admit.
Defined.

Lemma fmorph_eq : {mono f : x y / x == y}.
admit.
Defined.

Lemma fmorph_eq1 x : (f x == 1) = (x == 1).
admit.
Defined.

Lemma fmorph_char : [char R] =i [char F].
admit.
Defined.

End FieldMorphismInj.

Section FieldMorphismInv.

Variables (R : unitRingType) (f : {rmorphism F -> R}).

Lemma fmorph_unit x : (f x \in unit) = (x != 0).
admit.
Defined.

Lemma fmorphV : {morph f: x / x^-1}.
admit.
Defined.

Lemma fmorph_div : {morph f : x y / x / y}.
admit.
Defined.

End FieldMorphismInv.

Canonical regular_fieldType := [fieldType of F^o].

Section ModuleTheory.

Variable V : lmodType F.
Implicit Types (a : F) (v : V).

Lemma scalerK a : a != 0 -> cancel ( *:%R a : V -> V) ( *:%R a^-1).
admit.
Defined.

Lemma scalerKV a : a != 0 -> cancel ( *:%R a^-1 : V -> V) ( *:%R a).
admit.
Defined.

Lemma scalerI a : a != 0 -> injective ( *:%R a : V -> V).
admit.
Defined.

Lemma scaler_eq0 a v : (a *: v == 0) = (a == 0) || (v == 0).
admit.
Defined.

Lemma rpredZeq S (modS : submodPred S) (kS : keyed_pred modS) a v :
  (a *: v \in kS) = (a == 0) || (v \in kS).
admit.
Defined.

End ModuleTheory.

Lemma char_lalg (A : lalgType F) : [char A] =i [char F].
admit.
Defined.

Section Predicates.

Context (S : {pred F}) (divS : @divrPred F S) (kS : keyed_pred divS).

Lemma fpredMl x y : x \in kS -> x != 0 -> (x * y \in kS) = (y \in kS).
admit.
Defined.

Lemma fpredMr x y : x \in kS -> x != 0 -> (y * x \in kS) = (y \in kS).
admit.
Defined.

Lemma fpred_divl x y : x \in kS -> x != 0 -> (x / y \in kS) = (y \in kS).
admit.
Defined.

Lemma fpred_divr x y : x \in kS -> x != 0 -> (y / x \in kS) = (y \in kS).
admit.
Defined.

End Predicates.

End FieldTheory.

Arguments fmorph_inj {F R} f [x1 x2].

Module DecidableField.

Definition axiom (R : unitRingType) (s : seq R -> pred (formula R)) :=
  forall e f, reflect (holds e f) (s e f).

Record mixin_of (R : unitRingType) : Type :=
  Mixin { sat : seq R -> pred (formula R); satP : axiom sat}.

Section ClassDef.

Set Primitive Projections.
Record class_of (F : Type) : Type :=
  Class {base : Field.class_of F; mixin : mixin_of (UnitRing.Pack base)}.
Unset Primitive Projections.
Local Coercion base : class_of >-> Field.class_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variable (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.

Definition pack b0 (m0 : mixin_of (@UnitRing.Pack T b0)) :=
  fun bT b & phant_id (Field.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition zmodType := @Zmodule.Pack cT class.
Definition ringType := @Ring.Pack cT class.
Definition comRingType := @ComRing.Pack cT class.
Definition unitRingType := @UnitRing.Pack cT class.
Definition comUnitRingType := @ComUnitRing.Pack cT class.
Definition idomainType := @IntegralDomain.Pack cT class.
Definition fieldType := @Field.Pack cT class.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Field.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> Ring.type.
Canonical ringType.
Coercion comRingType : type >-> ComRing.type.
Canonical comRingType.
Coercion unitRingType : type >-> UnitRing.type.
Canonical unitRingType.
Coercion comUnitRingType : type >-> ComUnitRing.type.
Canonical comUnitRingType.
Coercion idomainType : type >-> IntegralDomain.type.
Canonical idomainType.
Coercion fieldType : type >-> Field.type.
Canonical fieldType.
Notation decFieldType := type.
Notation DecFieldType T m := (@pack T _ m _ _ id _ id).
Notation DecFieldMixin := Mixin.
Notation "[ 'decFieldType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'decFieldType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'decFieldType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'decFieldType'  'of'  T ]") : form_scope.
End Exports.

End DecidableField.
Import DecidableField.Exports.

Section DecidableFieldTheory.

Variable F : decFieldType.

Definition sat := DecidableField.sat (DecidableField.class F).

Lemma satP : DecidableField.axiom sat.
admit.
Defined.

Fact sol_subproof n f :
  reflect (exists s, (size s == n) && sat s f)
          (sat [::] (foldr Exists f (iota 0 n))).
admit.
Defined.

Definition sol n f :=
  if sol_subproof n f is ReflectT sP then xchoose sP else nseq n 0.

Lemma size_sol n f : size (sol n f) = n.
admit.
Defined.

Lemma solP n f : reflect (exists2 s, size s = n & holds s f) (sat (sol n f) f).
admit.
Defined.

Lemma eq_sat f1 f2 :
  (forall e, holds e f1 <-> holds e f2) -> sat^~ f1 =1 sat^~ f2.
admit.
Defined.

Lemma eq_sol f1 f2 :
  (forall e, holds e f1 <-> holds e f2) -> sol^~ f1 =1 sol^~ f2.
admit.
Defined.

End DecidableFieldTheory.

Arguments satP {F e f}.
Arguments solP {F n f}.

Section QE_Mixin.

Variable F : Field.type.
Implicit Type f : formula F.

Variable proj : nat -> seq (term F) * seq (term F) -> formula F.
 

 
Definition wf_QE_proj :=
  forall i bc (bc_i := proj i bc),
  dnf_rterm bc -> qf_form bc_i && rformula bc_i.

 
Definition valid_QE_proj :=
  forall i bc (ex_i_bc := ('exists 'X_i, dnf_to_form [:: bc])%T) e,
  dnf_rterm bc -> reflect (holds e ex_i_bc) (qf_eval e (proj i bc)).

Hypotheses (wf_proj : wf_QE_proj) (ok_proj : valid_QE_proj).

Let elim_aux f n := foldr Or False (map (proj n) (qf_to_dnf f false)).

Fixpoint quantifier_elim f :=
  match f with
  | f1 /\ f2 => (quantifier_elim f1) /\ (quantifier_elim f2)
  | f1 \/ f2 => (quantifier_elim f1) \/ (quantifier_elim f2)
  | f1 ==> f2 => (~ quantifier_elim f1) \/ (quantifier_elim f2)
  | ~ f => ~ quantifier_elim f
  | ('exists 'X_n, f) => elim_aux (quantifier_elim f) n
  | ('forall 'X_n, f) => ~ elim_aux (~ quantifier_elim f) n
  | _ => f
  end%T.

Lemma quantifier_elim_wf f :
  let qf := quantifier_elim f in rformula f -> qf_form qf && rformula qf.
admit.
Defined.

Lemma quantifier_elim_rformP e f :
  rformula f -> reflect (holds e f) (qf_eval e (quantifier_elim f)).
admit.
Defined.

Definition proj_sat e f := qf_eval e (quantifier_elim (to_rform f)).

Lemma proj_satP : DecidableField.axiom proj_sat.
admit.
Defined.

Definition QEdecFieldMixin := DecidableField.Mixin proj_satP.

End QE_Mixin.

Module ClosedField.

 
Definition axiom (R : ringType) :=
  forall n (P : nat -> R), n > 0 ->
   exists x : R, x ^+ n = \sum_(i < n) P i * (x ^+ i).

Section ClassDef.

Set Primitive Projections.
Record class_of (F : Type) : Type :=
  Class {base : DecidableField.class_of F; mixin : axiom (Ring.Pack base)}.
Unset Primitive Projections.
Local Coercion base : class_of >-> DecidableField.class_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variable (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.

Definition pack b0 (m0 : axiom (@Ring.Pack T b0)) :=
  fun bT b & phant_id (DecidableField.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m).

 
 

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition zmodType := @Zmodule.Pack cT class.
Definition ringType := @Ring.Pack cT class.
Definition comRingType := @ComRing.Pack cT class.
Definition unitRingType := @UnitRing.Pack cT class.
Definition comUnitRingType := @ComUnitRing.Pack cT class.
Definition idomainType := @IntegralDomain.Pack cT class.
Definition fieldType := @Field.Pack cT class.
Definition decFieldType := @DecidableField.Pack cT class.

End ClassDef.

Module Exports.
Coercion base : class_of >-> DecidableField.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> Ring.type.
Canonical ringType.
Coercion comRingType : type >-> ComRing.type.
Canonical comRingType.
Coercion unitRingType : type >-> UnitRing.type.
Canonical unitRingType.
Coercion comUnitRingType : type >-> ComUnitRing.type.
Canonical comUnitRingType.
Coercion idomainType : type >-> IntegralDomain.type.
Canonical idomainType.
Coercion fieldType : type >-> Field.type.
Canonical fieldType.
Coercion decFieldType : type >-> DecidableField.type.
Canonical decFieldType.
Notation closedFieldType := type.
Notation ClosedFieldType T m := (@pack T _ m _ _ id _ id).
Notation "[ 'closedFieldType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'closedFieldType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'closedFieldType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'closedFieldType'  'of'  T ]") : form_scope.
End Exports.

End ClosedField.
Import ClosedField.Exports.

Section ClosedFieldTheory.

Variable F : closedFieldType.

Lemma solve_monicpoly : ClosedField.axiom F.
admit.
Defined.

Lemma imaginary_exists : {i : F | i ^+ 2 = -1}.
admit.
Defined.

End ClosedFieldTheory.

Module SubType.

Section Zmodule.

Variables (V : zmodType) (S : {pred V}).
Variables (subS : zmodPred S) (kS : keyed_pred subS).
Variable U : subType (mem kS).

Let inU v Sv : U := Sub v Sv.
Let zeroU := inU (rpred0 kS).

Let oppU (u : U) := inU (rpredNr (valP u)).
Let addU (u1 u2 : U) := inU (rpredD (valP u1) (valP u2)).

Fact addA : associative addU.
admit.
Defined.
Fact addC : commutative addU.
admit.
Defined.
Fact add0 : left_id zeroU addU.
admit.
Defined.
Fact addN : left_inverse zeroU oppU addU.
admit.
Defined.

Definition zmodMixin of phant U := ZmodMixin addA addC add0 addN.

End Zmodule.

Section Ring.

Variables (R : ringType) (S : {pred R}).
Variables (ringS : subringPred S) (kS : keyed_pred ringS).

Definition cast_zmodType (V : zmodType) T (VeqT : V = T :> Type) :=
  let cast mV := let: erefl in _ = T := VeqT return Zmodule.class_of T in mV in
  Zmodule.Pack (cast (Zmodule.class V)).

Variable (T : subType (mem kS)) (V : zmodType) (VeqT: V = T :> Type).

Let inT x Sx : T := Sub x Sx.
Let oneT := inT (rpred1 kS).
Let mulT (u1 u2 : T) := inT (rpredM (valP u1) (valP u2)).
Let T' := cast_zmodType VeqT.

Hypothesis valM : {morph (val : T' -> R) : x y / x - y}.

Let val0 : val (0 : T') = 0.
admit.
Defined.
Let valD : {morph (val : T' -> R): x y / x + y}.
admit.
Defined.

Fact mulA : @associative T' mulT.
admit.
Defined.
Fact mul1l : left_id oneT mulT.
admit.
Defined.
Fact mul1r : right_id oneT mulT.
admit.
Defined.
Fact mulDl : @left_distributive T' T' mulT +%R.
admit.
Defined.
Fact mulDr : @right_distributive T' T' mulT +%R.
admit.
Defined.
Fact nz1 : oneT != 0 :> T'.
admit.
Defined.

Definition ringMixin := RingMixin mulA mul1l mul1r mulDl mulDr nz1.

End Ring.

Section Lmodule.

Variables (R : ringType) (V : lmodType R) (S : {pred V}).
Variables (linS : submodPred S) (kS : keyed_pred linS).
Variables (W : subType (mem kS)) (Z : zmodType) (ZeqW : Z = W :> Type).

Let scaleW a (w : W) := (Sub _ : _ -> W) (rpredZ a (valP w)).
Let W' := cast_zmodType ZeqW.

Hypothesis valD : {morph (val : W' -> V) : x y / x + y}.

Fact scaleA a b (w : W') : scaleW a (scaleW b w) = scaleW (a * b) w.
admit.
Defined.
Fact scale1 : left_id 1 scaleW.
admit.
Defined.
Fact scaleDr : @right_distributive R W' scaleW +%R.
admit.
Defined.
Fact scaleDl w : {morph (scaleW^~ w : R -> W') : a b / a + b}.
admit.
Defined.

Definition lmodMixin := LmodMixin scaleA scale1 scaleDr scaleDl.

End Lmodule.

Lemma lalgMixin (R : ringType) (A : lalgType R) (B : lmodType R) (f : B -> A) :
     phant B -> injective f -> scalable f ->
   forall mulB, {morph f : x y / mulB x y >-> x * y} -> Lalgebra.axiom mulB.
admit.
Defined.

Lemma comRingMixin (R : comRingType) (T : ringType) (f : T -> R) :
  phant T -> injective f -> {morph f : x y / x * y} -> commutative (@mul T).
admit.
Defined.

Lemma algMixin (R : comRingType) (A : algType R) (B : lalgType R) (f : B -> A) :
    phant B -> injective f -> {morph f : x y / x * y} -> scalable f ->
  @Algebra.axiom R B.
admit.
Defined.

Section UnitRing.

Definition cast_ringType (Q : ringType) T (QeqT : Q = T :> Type) :=
  let cast rQ := let: erefl in _ = T := QeqT return Ring.class_of T in rQ in
  Ring.Pack (cast (Ring.class Q)).

Variables (R : unitRingType) (S : {pred R}).
Variables (ringS : divringPred S) (kS : keyed_pred ringS).

Variables (T : subType (mem kS)) (Q : ringType) (QeqT : Q = T :> Type).

Let inT x Sx : T := Sub x Sx.
Let invT (u : T) := inT (rpredVr (valP u)).
Let unitT := [qualify a u : T | val u \is a unit].
Let T' := cast_ringType QeqT.

Hypothesis val1 : val (1 : T') = 1.
Hypothesis valM : {morph (val : T' -> R) : x y / x * y}.

Fact mulVr :
  {in (unitT : {pred T'}), left_inverse (1 : T') invT (@mul T')}.
admit.
Defined.

Fact mulrV : {in unitT, right_inverse (1 : T') invT (@mul T')}.
admit.
Defined.

Fact unitP (u v : T') : v * u = 1 /\ u * v = 1 -> u \in unitT.
admit.
Defined.

Fact unit_id : {in [predC unitT], invT =1 id}.
admit.
Defined.

Definition unitRingMixin := UnitRingMixin mulVr mulrV unitP unit_id.

End UnitRing.

Lemma idomainMixin (R : idomainType) (T : ringType) (f : T -> R) :
    phant T -> injective f -> f 0 = 0 -> {morph f : u v / u * v} ->
  @IntegralDomain.axiom T.
admit.
Defined.

Lemma fieldMixin (F : fieldType) (K : unitRingType) (f : K -> F) :
    phant K -> injective f -> f 0 = 0 -> {mono f : u / u \in unit} ->
  @Field.mixin_of K.
admit.
Defined.

Module Exports.

Notation "[ 'zmodMixin' 'of' U 'by' <: ]" := (zmodMixin (Phant U))
  (at level 0, format "[ 'zmodMixin'  'of'  U  'by'  <: ]") : form_scope.
Notation "[ 'ringMixin' 'of' R 'by' <: ]" :=
  (@ringMixin _ _ _ _ _ _ (@erefl Type R%type) (rrefl _))
  (at level 0, format "[ 'ringMixin'  'of'  R  'by'  <: ]") : form_scope.
Notation "[ 'lmodMixin' 'of' U 'by' <: ]" :=
  (@lmodMixin _ _ _ _ _ _ _ (@erefl Type U%type) (rrefl _))
  (at level 0, format "[ 'lmodMixin'  'of'  U  'by'  <: ]") : form_scope.
Notation "[ 'lalgMixin' 'of' A 'by' <: ]" :=
  ((lalgMixin (Phant A) val_inj (rrefl _)) *%R (rrefl _))
  (at level 0, format "[ 'lalgMixin'  'of'  A  'by'  <: ]") : form_scope.
Notation "[ 'comRingMixin' 'of' R 'by' <: ]" :=
  (comRingMixin (Phant R) val_inj (rrefl _))
  (at level 0, format "[ 'comRingMixin'  'of'  R  'by'  <: ]") : form_scope.
Notation "[ 'algMixin' 'of' A 'by' <: ]" :=
  (algMixin (Phant A) val_inj (rrefl _) (rrefl _))
  (at level 0, format "[ 'algMixin'  'of'  A  'by'  <: ]") : form_scope.
Notation "[ 'unitRingMixin' 'of' R 'by' <: ]" :=
  (@unitRingMixin _ _ _ _ _ _ (@erefl Type R%type) (erefl _) (rrefl _))
  (at level 0, format "[ 'unitRingMixin'  'of'  R  'by'  <: ]") : form_scope.
Notation "[ 'idomainMixin' 'of' R 'by' <: ]" :=
  (idomainMixin (Phant R) val_inj (erefl _) (rrefl _))
  (at level 0, format "[ 'idomainMixin'  'of'  R  'by'  <: ]") : form_scope.
Notation "[ 'fieldMixin' 'of' F 'by' <: ]" :=
  (fieldMixin (Phant F) val_inj (erefl _) (frefl _))
  (at level 0, format "[ 'fieldMixin'  'of'  F  'by'  <: ]") : form_scope.

End Exports.

End SubType.

Module Theory.

Definition addrA := addrA.
Definition addrC := addrC.
Definition add0r := add0r.
Definition addNr := addNr.
Definition addr0 := addr0.
Definition addrN := addrN.
Definition subrr := subrr.
Definition addrCA := addrCA.
Definition addrAC := addrAC.
Definition addrACA := addrACA.
Definition addKr := addKr.
Definition addNKr := addNKr.
Definition addrK := addrK.
Definition addrNK := addrNK.
Definition subrK := subrK.
Definition subKr := subKr.
Definition addrI := @addrI.
Definition addIr := @addIr.
Definition subrI := @subrI.
Definition subIr := @subIr.
Arguments addrI {V} y [x1 x2].
Arguments addIr {V} x [x1 x2].
Arguments subrI {V} y [x1 x2].
Arguments subIr {V} x [x1 x2].
Definition opprK := @opprK.
Arguments opprK {V}.
Definition oppr_inj := @oppr_inj.
Arguments oppr_inj {V} [x1 x2].
Definition oppr0 := oppr0.
Definition oppr_eq0 := oppr_eq0.
Definition opprD := opprD.
Definition opprB := opprB.
Definition addrKA := addrKA.
Definition subrKA := subrKA.
Definition subr0 := subr0.
Definition sub0r := sub0r.
Definition subr_eq := subr_eq.
Definition addr0_eq := addr0_eq.
Definition subr0_eq := subr0_eq.
Definition subr_eq0 := subr_eq0.
Definition addr_eq0 := addr_eq0.
Definition eqr_opp := eqr_opp.
Definition eqr_oppLR := eqr_oppLR.
Definition sumrN := sumrN.
Definition sumrB := sumrB.
Definition sumrMnl := sumrMnl.
Definition sumrMnr := sumrMnr.
Definition sumr_const := sumr_const.
Definition sumr_const_nat := sumr_const_nat.
Definition telescope_sumr := telescope_sumr.
Definition mulr0n := mulr0n.
Definition mulr1n := mulr1n.
Definition mulr2n := mulr2n.
Definition mulrS := mulrS.
Definition mulrSr := mulrSr.
Definition mulrb := mulrb.
Definition mul0rn := mul0rn.
Definition mulNrn := mulNrn.
Definition mulrnDl := mulrnDl.
Definition mulrnDr := mulrnDr.
Definition mulrnBl := mulrnBl.
Definition mulrnBr := mulrnBr.
Definition mulrnA := mulrnA.
Definition mulrnAC := mulrnAC.
Definition iter_addr := iter_addr.
Definition iter_addr_0 := iter_addr_0.
Definition mulrA := mulrA.
Definition mul1r := mul1r.
Definition mulr1 := mulr1.
Definition mulrDl := mulrDl.
Definition mulrDr := mulrDr.
Definition oner_neq0 := oner_neq0.
Definition oner_eq0 := oner_eq0.
Definition mul0r := mul0r.
Definition mulr0 := mulr0.
Definition mulrN := mulrN.
Definition mulNr := mulNr.
Definition mulrNN := mulrNN.
Definition mulN1r := mulN1r.
Definition mulrN1 := mulrN1.
Definition mulr_suml := mulr_suml.
Definition mulr_sumr := mulr_sumr.
Definition mulrBl := mulrBl.
Definition mulrBr := mulrBr.
Definition mulrnAl := mulrnAl.
Definition mulrnAr := mulrnAr.
Definition mulr_natl := mulr_natl.
Definition mulr_natr := mulr_natr.
Definition natrD := natrD.
Definition natrB := natrB.
Definition natr_sum := natr_sum.
Definition natrM := natrM.
Definition natrX := natrX.
Definition expr0 := expr0.
Definition exprS := exprS.
Definition expr1 := expr1.
Definition expr2 := expr2.
Definition expr0n := expr0n.
Definition expr1n := expr1n.
Definition exprD := exprD.
Definition exprSr := exprSr.
Definition expr_sum := expr_sum.
Definition commr_sym := commr_sym.
Definition commr_refl := commr_refl.
Definition commr0 := commr0.
Definition commr1 := commr1.
Definition commrN := commrN.
Definition commrN1 := commrN1.
Definition commrD := commrD.
Definition commrB := commrB.
Definition commr_sum := commr_sum.
Definition commr_prod := commr_prod.
Definition commrMn := commrMn.
Definition commrM := commrM.
Definition commr_nat := commr_nat.
Definition commrX := commrX.
Definition exprMn_comm := exprMn_comm.
Definition commr_sign := commr_sign.
Definition exprMn_n := exprMn_n.
Definition exprM := exprM.
Definition exprAC := exprAC.
Definition expr_mod := expr_mod.
Definition expr_dvd := expr_dvd.
Definition signr_odd := signr_odd.
Definition signr_eq0 := signr_eq0.
Definition mulr_sign := mulr_sign.
Definition signr_addb := signr_addb.
Definition signrN := signrN.
Definition signrE := signrE.
Definition mulr_signM := mulr_signM.
Definition exprNn := exprNn.
Definition sqrrN := sqrrN.
Definition sqrr_sign := sqrr_sign.
Definition signrMK := signrMK.
Definition mulrI_eq0 := mulrI_eq0.
Definition lreg_neq0 := lreg_neq0.
Definition mulrI0_lreg := mulrI0_lreg.
Definition lregN := lregN.
Definition lreg1 := lreg1.
Definition lregM := lregM.
Definition lregX := lregX.
Definition lreg_sign := lreg_sign.
Definition lregP {R x} := @lregP R x.
Definition mulIr_eq0 := mulIr_eq0.
Definition mulIr0_rreg := mulIr0_rreg.
Definition rreg_neq0 := rreg_neq0.
Definition rregN := rregN.
Definition rreg1 := rreg1.
Definition rregM := rregM.
Definition revrX := revrX.
Definition rregX := rregX.
Definition rregP {R x} := @rregP R x.
Definition exprDn_comm := exprDn_comm.
Definition exprBn_comm := exprBn_comm.
Definition subrXX_comm := subrXX_comm.
Definition exprD1n := exprD1n.
Definition subrX1 := subrX1.
Definition sqrrD1 := sqrrD1.
Definition sqrrB1 := sqrrB1.
Definition subr_sqr_1 := subr_sqr_1.
Definition charf0 := charf0.
Definition charf_prime := charf_prime.
Definition mulrn_char := mulrn_char.
Definition dvdn_charf := dvdn_charf.
Definition charf_eq := charf_eq.
Definition bin_lt_charf_0 := bin_lt_charf_0.
Definition Frobenius_autE := Frobenius_autE.
Definition Frobenius_aut0 := Frobenius_aut0.
Definition Frobenius_aut1 := Frobenius_aut1.
Definition Frobenius_autD_comm := Frobenius_autD_comm.
Definition Frobenius_autMn := Frobenius_autMn.
Definition Frobenius_aut_nat := Frobenius_aut_nat.
Definition Frobenius_autM_comm := Frobenius_autM_comm.
Definition Frobenius_autX := Frobenius_autX.
Definition Frobenius_autN := Frobenius_autN.
Definition Frobenius_autB_comm := Frobenius_autB_comm.
Definition exprNn_char := exprNn_char.
Definition addrr_char2 := addrr_char2.
Definition oppr_char2 := oppr_char2.
Definition addrK_char2 := addrK_char2.
Definition addKr_char2 := addKr_char2.
Definition iter_mulr := iter_mulr.
Definition iter_mulr_1 := iter_mulr_1.
Definition prodr_const := prodr_const.
Definition prodr_const_nat := prodr_const_nat.
Definition mulrC := mulrC.
Definition mulrCA := mulrCA.
Definition mulrAC := mulrAC.
Definition mulrACA := mulrACA.
Definition exprMn := exprMn.
Definition prodrXl := prodrXl.
Definition prodrXr := prodrXr.
Definition prodrN := prodrN.
Definition prodrMn_const := prodrMn_const.
Definition prodrMn := prodrMn.
Definition natr_prod := natr_prod.
Definition prodr_undup_exp_count := prodr_undup_exp_count.
Definition exprDn := exprDn.
Definition exprBn := exprBn.
Definition subrXX := subrXX.
Definition sqrrD := sqrrD.
Definition sqrrB := sqrrB.
Definition subr_sqr := subr_sqr.
Definition subr_sqrDB := subr_sqrDB.
Definition exprDn_char := exprDn_char.
Definition mulrV := mulrV.
Definition divrr := divrr.
Definition mulVr := mulVr.
Definition invr_out := invr_out.
Definition unitrP {R x} := @unitrP R x.
Definition mulKr := mulKr.
Definition mulVKr := mulVKr.
Definition mulrK := mulrK.
Definition mulrVK := mulrVK.
Definition divrK := divrK.
Definition mulrI := mulrI.
Definition mulIr := mulIr.
Definition divrI := divrI.
Definition divIr := divIr.
Definition telescope_prodr := telescope_prodr.
Definition commrV := commrV.
Definition unitrE := unitrE.
Definition invrK := @invrK.
Arguments invrK {R}.
Definition invr_inj := @invr_inj.
Arguments invr_inj {R} [x1 x2].
Definition unitrV := unitrV.
Definition unitr1 := unitr1.
Definition invr1 := invr1.
Definition divr1 := divr1.
Definition div1r := div1r.
Definition natr_div := natr_div.
Definition unitr0 := unitr0.
Definition invr0 := invr0.
Definition unitrN1 := unitrN1.
Definition unitrN := unitrN.
Definition invrN1 := invrN1.
Definition invrN := invrN.
Definition invr_sign := invr_sign.
Definition unitrMl := unitrMl.
Definition unitrMr := unitrMr.
Definition invrM := invrM.
Definition invr_eq0 := invr_eq0.
Definition invr_eq1 := invr_eq1.
Definition invr_neq0 := invr_neq0.
Definition unitrM_comm := unitrM_comm.
Definition unitrX := unitrX.
Definition unitrX_pos := unitrX_pos.
Definition exprVn := exprVn.
Definition exprB := exprB.
Definition invr_signM := invr_signM.
Definition divr_signM := divr_signM.
Definition rpred0D := rpred0D.
Definition rpred0 := rpred0.
Definition rpredD := rpredD.
Definition rpredNr := rpredNr.
Definition rpred_sum := rpred_sum.
Definition rpredMn := rpredMn.
Definition rpredN := rpredN.
Definition rpredB := rpredB.
Definition rpredBC := rpredBC.
Definition rpredMNn := rpredMNn.
Definition rpredDr := rpredDr.
Definition rpredDl := rpredDl.
Definition rpredBr := rpredBr.
Definition rpredBl := rpredBl.
Definition rpredMsign := rpredMsign.
Definition rpred1M := rpred1M.
Definition rpred1 := rpred1.
Definition rpredM := rpredM.
Definition rpred_prod := rpred_prod.
Definition rpredX := rpredX.
Definition rpred_nat := rpred_nat.
Definition rpredN1 := rpredN1.
Definition rpred_sign := rpred_sign.
Definition rpredZsign := rpredZsign.
Definition rpredZnat := rpredZnat.
Definition rpredZ := rpredZ.
Definition rpredVr := rpredVr.
Definition rpredV := rpredV.
Definition rpred_div := rpred_div.
Definition rpredXN := rpredXN.
Definition rpredZeq := rpredZeq.
Definition char_lalg := char_lalg.
Definition rpredMr := rpredMr.
Definition rpredMl := rpredMl.
Definition rpred_divr := rpred_divr.
Definition rpred_divl := rpred_divl.
Definition eq_eval := eq_eval.
Definition eval_tsubst := eval_tsubst.
Definition eq_holds := eq_holds.
Definition holds_fsubst := holds_fsubst.
Definition unitrM := unitrM.
Definition unitrPr {R x} := @unitrPr R x.
Definition expr_div_n := expr_div_n.
Definition mulr1_eq := mulr1_eq.
Definition divr1_eq := divr1_eq.
Definition divKr := divKr.
Definition mulf_eq0 := mulf_eq0.
Definition prodf_eq0 := prodf_eq0.
Definition prodf_seq_eq0 := prodf_seq_eq0.
Definition mulf_neq0 := mulf_neq0.
Definition prodf_neq0 := prodf_neq0.
Definition prodf_seq_neq0 := prodf_seq_neq0.
Definition expf_eq0 := expf_eq0.
Definition sqrf_eq0 := sqrf_eq0.
Definition expf_neq0 := expf_neq0.
Definition natf_neq0 := natf_neq0.
Definition natf0_char := natf0_char.
Definition charf'_nat := charf'_nat.
Definition charf0P := charf0P.
Definition eqf_sqr := eqf_sqr.
Definition mulfI := mulfI.
Definition mulIf := mulIf.
Definition divfI := divfI.
Definition divIf := divIf.
Definition sqrf_eq1 := sqrf_eq1.
Definition expfS_eq1 := expfS_eq1.
Definition fieldP := fieldP.
Definition unitfE := unitfE.
Definition mulVf := mulVf.
Definition mulfV := mulfV.
Definition divff := divff.
Definition mulKf := mulKf.
Definition mulVKf := mulVKf.
Definition mulfK := mulfK.
Definition mulfVK := mulfVK.
Definition divfK := divfK.
Definition divKf := divKf.
Definition invfM := invfM.
Definition invf_div := invf_div.
Definition expfB_cond := expfB_cond.
Definition expfB := expfB.
Definition prodfV := prodfV.
Definition prodf_div := prodf_div.
Definition telescope_prodf := telescope_prodf.
Definition addf_div := addf_div.
Definition mulf_div := mulf_div.
Definition char0_natf_div := char0_natf_div.
Definition fpredMr := fpredMr.
Definition fpredMl := fpredMl.
Definition fpred_divr := fpred_divr.
Definition fpred_divl := fpred_divl.
Definition satP {F e f} := @satP F e f.
Definition eq_sat := eq_sat.
Definition solP {F n f} := @solP F n f.
Definition eq_sol := eq_sol.
Definition size_sol := size_sol.
Definition solve_monicpoly := solve_monicpoly.
Definition raddf0 := raddf0.
Definition raddf_eq0 := raddf_eq0.
Definition raddf_inj := raddf_inj.
Definition raddfN := raddfN.
Definition raddfD := raddfD.
Definition raddfB := raddfB.
Definition raddf_sum := raddf_sum.
Definition raddfMn := raddfMn.
Definition raddfMNn := raddfMNn.
Definition raddfMnat := raddfMnat.
Definition raddfMsign := raddfMsign.
Definition can2_additive := can2_additive.
Definition bij_additive := bij_additive.
Definition rmorph0 := rmorph0.
Definition rmorphN := rmorphN.
Definition rmorphD := rmorphD.
Definition rmorphB := rmorphB.
Definition rmorph_sum := rmorph_sum.
Definition rmorphMn := rmorphMn.
Definition rmorphMNn := rmorphMNn.
Definition rmorphismP := rmorphismP.
Definition rmorphismMP := rmorphismMP.
Definition rmorph1 := rmorph1.
Definition rmorph_eq1 := rmorph_eq1.
Definition rmorphM := rmorphM.
Definition rmorphMsign := rmorphMsign.
Definition rmorph_nat := rmorph_nat.
Definition rmorph_eq_nat := rmorph_eq_nat.
Definition rmorph_prod := rmorph_prod.
Definition rmorphX := rmorphX.
Definition rmorphN1 := rmorphN1.
Definition rmorph_sign := rmorph_sign.
Definition rmorph_char := rmorph_char.
Definition can2_rmorphism := can2_rmorphism.
Definition bij_rmorphism := bij_rmorphism.
Definition rmorph_comm := rmorph_comm.
Definition rmorph_unit := rmorph_unit.
Definition rmorphV := rmorphV.
Definition rmorph_div := rmorph_div.
Definition fmorph_eq0 := fmorph_eq0.
Definition fmorph_inj := @fmorph_inj.
Arguments fmorph_inj {F R} f [x1 x2].
Definition fmorph_eq := fmorph_eq.
Definition fmorph_eq1 := fmorph_eq1.
Definition fmorph_char := fmorph_char.
Definition fmorph_unit := fmorph_unit.
Definition fmorphV := fmorphV.
Definition fmorph_div := fmorph_div.
Definition scalerA := scalerA.
Definition scale1r := scale1r.
Definition scalerDr := scalerDr.
Definition scalerDl := scalerDl.
Definition scaler0 := scaler0.
Definition scale0r := scale0r.
Definition scaleNr := scaleNr.
Definition scaleN1r := scaleN1r.
Definition scalerN := scalerN.
Definition scalerBl := scalerBl.
Definition scalerBr := scalerBr.
Definition scaler_nat := scaler_nat.
Definition scalerMnl := scalerMnl.
Definition scalerMnr := scalerMnr.
Definition scaler_suml := scaler_suml.
Definition scaler_sumr := scaler_sumr.
Definition scaler_eq0 := scaler_eq0.
Definition scalerK := scalerK.
Definition scalerKV := scalerKV.
Definition scalerI := scalerI.
Definition scalerAl := scalerAl.
Definition mulr_algl := mulr_algl.
Definition scaler_sign := scaler_sign.
Definition signrZK := signrZK.
Definition scalerCA := scalerCA.
Definition scalerAr := scalerAr.
Definition mulr_algr := mulr_algr.
Definition comm_alg := comm_alg.
Definition exprZn := exprZn.
Definition scaler_prodl := scaler_prodl.
Definition scaler_prodr := scaler_prodr.
Definition scaler_prod := scaler_prod.
Definition scaler_injl := scaler_injl.
Definition scaler_unit := scaler_unit.
Definition invrZ := invrZ.
Definition raddfZnat := raddfZnat.
Definition raddfZsign := raddfZsign.
Definition in_algE := in_algE.
Definition linear0 := linear0.
Definition linearN := linearN.
Definition linearD := linearD.
Definition linearB := linearB.
Definition linear_sum := linear_sum.
Definition linearMn := linearMn.
Definition linearMNn := linearMNn.
Definition linearP := linearP.
Definition linearZ_LR := linearZ_LR.
Definition linearZ := linearZ.
Definition linearPZ := linearPZ.
Definition linearZZ := linearZZ.
Definition scalarP := scalarP.
Definition scalarZ := scalarZ.
Definition can2_linear := can2_linear.
Definition bij_linear := bij_linear.
Definition rmorph_alg := rmorph_alg.
Definition lrmorphismP := lrmorphismP.
Definition can2_lrmorphism := can2_lrmorphism.
Definition bij_lrmorphism := bij_lrmorphism.
Definition imaginary_exists := imaginary_exists.

Notation null_fun V := (null_fun V) (only parsing).
Notation in_alg A := (in_alg_loc A).

#[deprecated(since="mathcomp 1.13.0", note="Use prodrMn instead.")]
Notation prodr_natmul := prodrMn (only parsing).

End Theory.

Notation in_alg A := (in_alg_loc A).

End GRing.

Export Zmodule.Exports Ring.Exports Lmodule.Exports Lalgebra.Exports.
Export Additive.Exports RMorphism.Exports Linear.Exports LRMorphism.Exports.
Export Algebra.Exports UnitRing.Exports UnitAlgebra.Exports.
Export ComRing.Exports ComAlgebra.Exports ComUnitRing.Exports.
Export ComUnitAlgebra.Exports IntegralDomain.Exports Field.Exports.
Export DecidableField.Exports ClosedField.Exports.
Export Pred.Exports SubType.Exports.
Notation QEdecFieldMixin := QEdecFieldMixin.

Notation "0" := (zero _) : ring_scope.
Notation "-%R" := (@opp _) : fun_scope.
Notation "- x" := (opp x) : ring_scope.
Notation "+%R" := (@add _) : fun_scope.
Notation "x + y" := (add x y) : ring_scope.
Notation "x - y" := (add x (- y)) : ring_scope.
Notation "x *+ n" := (natmul x n) : ring_scope.
Notation "x *- n" := (opp (x *+ n)) : ring_scope.
Notation "s `_ i" := (seq.nth 0%R s%R i) : ring_scope.
Notation support := 0.-support.

Notation "1" := (one _) : ring_scope.
Notation "- 1" := (opp 1) : ring_scope.

Notation "n %:R" := (natmul 1 n) : ring_scope.
Notation "[ 'char' R ]" := (char (Phant R)) : ring_scope.
Notation Frobenius_aut chRp := (Frobenius_aut chRp).
Notation "*%R" := (@mul _) : fun_scope.
Notation "x * y" := (mul x y) : ring_scope.
Notation "x ^+ n" := (exp x n) : ring_scope.
Notation "x ^-1" := (inv x) : ring_scope.
Notation "x ^- n" := (inv (x ^+ n)) : ring_scope.
Notation "x / y" := (mul x y^-1) : ring_scope.

Notation "*:%R" := (@scale _ _) : fun_scope.
Notation "a *: m" := (scale a m) : ring_scope.
Notation "k %:A" := (scale k 1) : ring_scope.
Notation "\0" := (null_fun _) : ring_scope.
Notation "f \+ g" := (add_fun f g) : ring_scope.
Notation "f \- g" := (sub_fun f g) : ring_scope.
Notation "a \*: f" := (scale_fun a f) : ring_scope.
Notation "x \*o f" := (mull_fun x f) : ring_scope.
Notation "x \o* f" := (mulr_fun x f) : ring_scope.

Arguments add_fun {_ _} f g _ /.
Arguments sub_fun {_ _} f g _ /.
Arguments mull_fun {_ _}  a f _ /.
Arguments mulr_fun {_ _} a f _ /.
Arguments scale_fun {_ _ _} a f _ /.

Notation "\sum_ ( i <- r | P ) F" :=
  (\big[+%R/0%R]_(i <- r | P%B) F%R) : ring_scope.
Notation "\sum_ ( i <- r ) F" :=
  (\big[+%R/0%R]_(i <- r) F%R) : ring_scope.
Notation "\sum_ ( m <= i < n | P ) F" :=
  (\big[+%R/0%R]_(m <= i < n | P%B) F%R) : ring_scope.
Notation "\sum_ ( m <= i < n ) F" :=
  (\big[+%R/0%R]_(m <= i < n) F%R) : ring_scope.
Notation "\sum_ ( i | P ) F" :=
  (\big[+%R/0%R]_(i | P%B) F%R) : ring_scope.
Notation "\sum_ i F" :=
  (\big[+%R/0%R]_i F%R) : ring_scope.
Notation "\sum_ ( i : t | P ) F" :=
  (\big[+%R/0%R]_(i : t | P%B) F%R) (only parsing) : ring_scope.
Notation "\sum_ ( i : t ) F" :=
  (\big[+%R/0%R]_(i : t) F%R) (only parsing) : ring_scope.
Notation "\sum_ ( i < n | P ) F" :=
  (\big[+%R/0%R]_(i < n | P%B) F%R) : ring_scope.
Notation "\sum_ ( i < n ) F" :=
  (\big[+%R/0%R]_(i < n) F%R) : ring_scope.
Notation "\sum_ ( i 'in' A | P ) F" :=
  (\big[+%R/0%R]_(i in A | P%B) F%R) : ring_scope.
Notation "\sum_ ( i 'in' A ) F" :=
  (\big[+%R/0%R]_(i in A) F%R) : ring_scope.

Notation "\prod_ ( i <- r | P ) F" :=
  (\big[*%R/1%R]_(i <- r | P%B) F%R) : ring_scope.
Notation "\prod_ ( i <- r ) F" :=
  (\big[*%R/1%R]_(i <- r) F%R) : ring_scope.
Notation "\prod_ ( m <= i < n | P ) F" :=
  (\big[*%R/1%R]_(m <= i < n | P%B) F%R) : ring_scope.
Notation "\prod_ ( m <= i < n ) F" :=
  (\big[*%R/1%R]_(m <= i < n) F%R) : ring_scope.
Notation "\prod_ ( i | P ) F" :=
  (\big[*%R/1%R]_(i | P%B) F%R) : ring_scope.
Notation "\prod_ i F" :=
  (\big[*%R/1%R]_i F%R) : ring_scope.
Notation "\prod_ ( i : t | P ) F" :=
  (\big[*%R/1%R]_(i : t | P%B) F%R) (only parsing) : ring_scope.
Notation "\prod_ ( i : t ) F" :=
  (\big[*%R/1%R]_(i : t) F%R) (only parsing) : ring_scope.
Notation "\prod_ ( i < n | P ) F" :=
  (\big[*%R/1%R]_(i < n | P%B) F%R) : ring_scope.
Notation "\prod_ ( i < n ) F" :=
  (\big[*%R/1%R]_(i < n) F%R) : ring_scope.
Notation "\prod_ ( i 'in' A | P ) F" :=
  (\big[*%R/1%R]_(i in A | P%B) F%R) : ring_scope.
Notation "\prod_ ( i 'in' A ) F" :=
  (\big[*%R/1%R]_(i in A) F%R) : ring_scope.

Canonical add_monoid.
Canonical add_comoid.
Canonical mul_monoid.
Canonical mul_comoid.
Canonical muloid.
Canonical addoid.

Canonical locked_additive.
Canonical locked_rmorphism.
Canonical locked_linear.
Canonical locked_lrmorphism.
Canonical idfun_additive.
Canonical idfun_rmorphism.
Canonical idfun_linear.
Canonical idfun_lrmorphism.
Canonical comp_additive.
Canonical comp_rmorphism.
Canonical comp_linear.
Canonical comp_lrmorphism.
Canonical opp_additive.
Canonical opp_linear.
Canonical scale_additive.
Canonical scale_linear.
Canonical null_fun_additive.
Canonical null_fun_linear.
Canonical scale_fun_additive.
Canonical scale_fun_linear.
Canonical add_fun_additive.
Canonical add_fun_linear.
Canonical sub_fun_additive.
Canonical sub_fun_linear.
Canonical mull_fun_additive.
Canonical mull_fun_linear.
Canonical mulr_fun_additive.
Canonical mulr_fun_linear.
Canonical Frobenius_aut_additive.
Canonical Frobenius_aut_rmorphism.
Canonical in_alg_additive.
Canonical in_alg_rmorphism.

Notation "R ^c" := (converse R) (at level 2, format "R ^c") : type_scope.
Canonical converse_eqType.
Canonical converse_choiceType.
Canonical converse_zmodType.
Canonical converse_ringType.
Canonical converse_unitRingType.

Notation "R ^o" := (regular R) (at level 2, format "R ^o") : type_scope.
Canonical regular_eqType.
Canonical regular_choiceType.
Canonical regular_zmodType.
Canonical regular_ringType.
Canonical regular_lmodType.
Canonical regular_lalgType.
Canonical regular_comRingType.
Canonical regular_algType.
Canonical regular_unitRingType.
Canonical regular_comUnitRingType.
Canonical regular_unitAlgType.
Canonical regular_comAlgType.
Canonical regular_comUnitAlgType.
Canonical regular_idomainType.
Canonical regular_fieldType.

Canonical unit_keyed.
Canonical unit_opprPred.
Canonical unit_mulrPred.
Canonical unit_smulrPred.
Canonical unit_divrPred.
Canonical unit_sdivrPred.

Bind Scope term_scope with term.
Bind Scope term_scope with formula.

Notation "''X_' i" := (Var _ i) : term_scope.
Notation "n %:R" := (NatConst _ n) : term_scope.
Notation "0" := 0%:R%T : term_scope.
Notation "1" := 1%:R%T : term_scope.
Notation "x %:T" := (Const x) : term_scope.
Infix "+" := Add : term_scope.
Notation "- t" := (Opp t) : term_scope.
Notation "t - u" := (Add t (- u)) : term_scope.
Infix "*" := Mul : term_scope.
Infix "*+" := NatMul : term_scope.
Notation "t ^-1" := (Inv t) : term_scope.
Notation "t / u" := (Mul t u^-1) : term_scope.
Infix "^+" := Exp : term_scope.
Infix "==" := Equal : term_scope.
Notation "x != y" := (GRing.Not (x == y)) : term_scope.
Infix "/\" := And : term_scope.
Infix "\/" := Or : term_scope.
Infix "==>" := Implies : term_scope.
Notation "~ f" := (Not f) : term_scope.
Notation "''exists' ''X_' i , f" := (Exists i f) : term_scope.
Notation "''forall' ''X_' i , f" := (Forall i f) : term_scope.

 
Section FinFunZmod.

Variable (aT : finType) (rT : zmodType).
Implicit Types f g : {ffun aT -> rT}.

Definition ffun_zero := [ffun a : aT => (0 : rT)].
Definition ffun_opp f := [ffun a => - f a].
Definition ffun_add f g := [ffun a => f a + g a].

Fact ffun_addA : associative ffun_add.
admit.
Defined.
Fact ffun_addC : commutative ffun_add.
admit.
Defined.
Fact ffun_add0 : left_id ffun_zero ffun_add.
admit.
Defined.
Fact ffun_addN : left_inverse ffun_zero ffun_opp ffun_add.
admit.
Defined.

Definition ffun_zmodMixin :=
  Zmodule.Mixin ffun_addA ffun_addC ffun_add0 ffun_addN.
Canonical ffun_zmodType := Eval hnf in ZmodType _ ffun_zmodMixin.

Section Sum.

Variables (I : Type) (r : seq I) (P : pred I) (F : I -> {ffun aT -> rT}).

Lemma sum_ffunE x : (\sum_(i <- r | P i) F i) x = \sum_(i <- r | P i) F i x.
admit.
Defined.

Lemma sum_ffun :
  \sum_(i <- r | P i) F i = [ffun x => \sum_(i <- r | P i) F i x].
admit.
Defined.

End Sum.

Lemma ffunMnE f n x : (f *+ n) x = f x *+ n.
admit.
Defined.

End FinFunZmod.

Section FinFunRing.

 
 

Variable (aT : finType) (R : ringType) (a : aT).

Definition ffun_one : {ffun aT -> R} := [ffun => 1].
Definition ffun_mul (f g : {ffun aT -> R}) := [ffun x => f x * g x].

Fact ffun_mulA : associative ffun_mul.
admit.
Defined.
Fact ffun_mul_1l : left_id ffun_one ffun_mul.
admit.
Defined.
Fact ffun_mul_1r : right_id ffun_one ffun_mul.
admit.
Defined.
Fact ffun_mul_addl :  left_distributive ffun_mul (@ffun_add _ _).
admit.
Defined.
Fact ffun_mul_addr :  right_distributive ffun_mul (@ffun_add _ _).
admit.
Defined.
Fact ffun1_nonzero : ffun_one != 0.
Proof.
by apply/eqP => /ffunP/(_ a)/eqP; rewrite !ffunE oner_eq0.
Qed.

Definition ffun_ringMixin :=
  RingMixin ffun_mulA ffun_mul_1l ffun_mul_1r ffun_mul_addl ffun_mul_addr
            ffun1_nonzero.
Definition ffun_ringType :=
  Eval hnf in RingType {ffun aT -> R} ffun_ringMixin.

End FinFunRing.

Section FinFunComRing.

Variable (aT : finType) (R : comRingType) (a : aT).

Fact ffun_mulC : commutative (@ffun_mul aT R).
admit.
Defined.

Definition ffun_comRingType :=
  Eval hnf in ComRingType (ffun_ringType R a) ffun_mulC.

End FinFunComRing.

Section FinFunLmod.

Variable (R : ringType) (aT : finType) (rT : lmodType R).

Implicit Types f g : {ffun aT -> rT}.

Definition ffun_scale k f := [ffun a => k *: f a].

Fact ffun_scaleA k1 k2 f :
  ffun_scale k1 (ffun_scale k2 f) = ffun_scale (k1 * k2) f.
admit.
Defined.
Fact ffun_scale1 : left_id 1 ffun_scale.
admit.
Defined.
Fact ffun_scale_addr k : {morph (ffun_scale k) : x y / x + y}.
admit.
Defined.
Fact ffun_scale_addl u : {morph (ffun_scale)^~ u : k1 k2 / k1 + k2}.
admit.
Defined.

Definition ffun_lmodMixin :=
  LmodMixin ffun_scaleA ffun_scale1 ffun_scale_addr ffun_scale_addl.
Canonical ffun_lmodType :=
  Eval hnf in LmodType R {ffun aT -> rT} ffun_lmodMixin.

End FinFunLmod.

 
Section PairZmod.

Variables M1 M2 : zmodType.

Definition opp_pair (x : M1 * M2) := (- x.1, - x.2).
Definition add_pair (x y : M1 * M2) := (x.1 + y.1, x.2 + y.2).

Fact pair_addA : associative add_pair.
admit.
Defined.

Fact pair_addC : commutative add_pair.
admit.
Defined.

Fact pair_add0 : left_id (0, 0) add_pair.
admit.
Defined.

Fact pair_addN : left_inverse (0, 0) opp_pair add_pair.
admit.
Defined.

Definition pair_zmodMixin := ZmodMixin pair_addA pair_addC pair_add0 pair_addN.
Canonical pair_zmodType := Eval hnf in ZmodType (M1 * M2) pair_zmodMixin.

Fact fst_is_additive : additive fst.
admit.
Defined.
Canonical fst_additive := Additive fst_is_additive.
Fact snd_is_additive : additive snd.
admit.
Defined.
Canonical snd_additive := Additive snd_is_additive.

End PairZmod.

Section PairRing.

Variables R1 R2 : ringType.

Definition mul_pair (x y : R1 * R2) := (x.1 * y.1, x.2 * y.2).

Fact pair_mulA : associative mul_pair.
admit.
Defined.

Fact pair_mul1l : left_id (1, 1) mul_pair.
admit.
Defined.

Fact pair_mul1r : right_id (1, 1) mul_pair.
admit.
Defined.

Fact pair_mulDl : left_distributive mul_pair +%R.
admit.
Defined.

Fact pair_mulDr : right_distributive mul_pair +%R.
admit.
Defined.

Fact pair_one_neq0 : (1, 1) != 0 :> R1 * R2.
admit.
Defined.

Definition pair_ringMixin :=
  RingMixin pair_mulA pair_mul1l pair_mul1r pair_mulDl pair_mulDr pair_one_neq0.
Canonical pair_ringType := Eval hnf in RingType (R1 * R2) pair_ringMixin.

Fact fst_is_multiplicative : multiplicative fst.
admit.
Defined.
Canonical fst_rmorphism := AddRMorphism fst_is_multiplicative.
Fact snd_is_multiplicative : multiplicative snd.
admit.
Defined.
Canonical snd_rmorphism := AddRMorphism snd_is_multiplicative.

End PairRing.

Section PairComRing.

Variables R1 R2 : comRingType.

Fact pair_mulC : commutative (@mul_pair R1 R2).
admit.
Defined.

Canonical pair_comRingType := Eval hnf in ComRingType (R1 * R2) pair_mulC.

End PairComRing.

Section PairLmod.

Variables (R : ringType) (V1 V2 : lmodType R).

Definition scale_pair a (v : V1 * V2) : V1 * V2 := (a *: v.1, a *: v.2).

Fact pair_scaleA a b u : scale_pair a (scale_pair b u) = scale_pair (a * b) u.
admit.
Defined.

Fact pair_scale1 u : scale_pair 1 u = u.
admit.
Defined.

Fact pair_scaleDr : right_distributive scale_pair +%R.
admit.
Defined.

Fact pair_scaleDl u : {morph scale_pair^~ u: a b / a + b}.
admit.
Defined.

Definition pair_lmodMixin :=
  LmodMixin pair_scaleA pair_scale1 pair_scaleDr pair_scaleDl.
Canonical pair_lmodType := Eval hnf in LmodType R (V1 * V2) pair_lmodMixin.

Fact fst_is_scalable : scalable fst.
admit.
Defined.
Canonical fst_linear := AddLinear fst_is_scalable.
Fact snd_is_scalable : scalable snd.
admit.
Defined.
Canonical snd_linear := AddLinear snd_is_scalable.

End PairLmod.

Section PairLalg.

Variables (R : ringType) (A1 A2 : lalgType R).

Fact pair_scaleAl a (u v : A1 * A2) : a *: (u * v) = (a *: u) * v.
admit.
Defined.
Canonical pair_lalgType :=  Eval hnf in LalgType R (A1 * A2) pair_scaleAl.

Definition fst_lrmorphism := [lrmorphism of fst].
Definition snd_lrmorphism := [lrmorphism of snd].

End PairLalg.

Section PairAlg.

Variables (R : comRingType) (A1 A2 : algType R).

Fact pair_scaleAr a (u v : A1 * A2) : a *: (u * v) = u * (a *: v).
admit.
Defined.
Canonical pair_algType :=  Eval hnf in AlgType R (A1 * A2) pair_scaleAr.

End PairAlg.

Section PairUnitRing.

Variables R1 R2 : unitRingType.

Definition pair_unitr :=
  [qualify a x : R1 * R2 | (x.1 \is a GRing.unit) && (x.2 \is a GRing.unit)].
Definition pair_invr x :=
  if x \is a pair_unitr then (x.1^-1, x.2^-1) else x.

Lemma pair_mulVl : {in pair_unitr, left_inverse 1 pair_invr *%R}.
admit.
Defined.

Lemma pair_mulVr : {in pair_unitr, right_inverse 1 pair_invr *%R}.
admit.
Defined.

Lemma pair_unitP x y : y * x = 1 /\ x * y = 1 -> x \is a pair_unitr.
admit.
Defined.

Lemma pair_invr_out : {in [predC pair_unitr], pair_invr =1 id}.
admit.
Defined.

Definition pair_unitRingMixin :=
  UnitRingMixin pair_mulVl pair_mulVr pair_unitP pair_invr_out.
Canonical pair_unitRingType :=
  Eval hnf in UnitRingType (R1 * R2) pair_unitRingMixin.

End PairUnitRing.

Canonical pair_comUnitRingType (R1 R2 : comUnitRingType) :=
  Eval hnf in [comUnitRingType of R1 * R2].

Canonical pair_unitAlgType (R : comUnitRingType) (A1 A2 : unitAlgType R) :=
  Eval hnf in [unitAlgType R of A1 * A2].

Lemma pairMnE (M1 M2 : zmodType) (x : M1 * M2) n :
  x *+ n = (x.1 *+ n, x.2 *+ n).
admit.
Defined.

 

 

 

End ssralg.

End mathcomp_DOT_algebra_DOT_ssralg_WRAPPED.
Module Export mathcomp_DOT_algebra_DOT_ssralg.
Module Export mathcomp.
Module Export algebra.
Module ssralg.
Include mathcomp_DOT_algebra_DOT_ssralg_WRAPPED.ssralg.
End ssralg.

End algebra.

End mathcomp.

End mathcomp_DOT_algebra_DOT_ssralg.

Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.
Import mathcomp.ssreflect.ssreflect.
Import mathcomp.ssreflect.ssrbool.
Import mathcomp.ssreflect.ssrfun.
Import mathcomp.ssreflect.eqtype.
Import mathcomp.ssreflect.ssrnat.
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

Section InheritedClasses.

Variable bT : base_type.
Local Notation T := (arg_sort bT).
Local Notation class := (finClass bT).
Canonical finType := Finite.Pack class.
Definition arg_finType := Eval hnf in [finType of T].

End InheritedClasses.
Coercion mixin : base_type >-> mixin_of.
Coercion base : type >-> base_type.
Coercion arg_finType : base_type >-> Finite.type.
Notation baseFinGroupType := base_type.
Notation finGroupType := type.
Notation BaseFinGroupType T m := (@pack_base T m _ _ id).
Notation FinGroupType := Pack.

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

Definition conjg (T : finGroupType) (x y : T) := y^-1 * (x * y).
Notation "x1 ^ x2" := (conjg x1 x2) : group_scope.

Definition commg (T : finGroupType) (x y : T) := x^-1 * x ^ y.

Prenex Implicits mulg invg expgn conjg commg.

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

Definition group_of of phant gT : predArgType := group_type.
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
Import mathcomp.ssreflect.div.
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
Import mathcomp.ssreflect.bigop.
Unset Printing Implicit Defensive.

Declare Scope matrix_set_scope.
Import GRing.Theory.

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
