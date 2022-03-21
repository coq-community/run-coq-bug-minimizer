(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "-projection-no-head-constant" "-w" "-redundant-canonical-projection" "-w" "-notation-overridden" "-w" "+duplicate-clear" "-w" "-ambiguous-paths" "-w" "+non-primitive-record" "-w" "+undeclared-scope" "-w" "-deprecated-hint-without-locality" "-w" "-deprecated-hint-rewrite-without-locality" "-w" "-deprecated-native-compiler-option" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/mathcomp/mathcomp" "mathcomp" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-I" "/github/workspace/builds/coq/coq-failing/_build_ci/mathcomp/mathcomp" "-top" "ssrnum" "-native-compiler" "ondemand") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 5422 lines to 262 lines, then from 275 lines to 6956 lines, then from 6961 lines to 3833 lines *)
(* coqc version 8.16+alpha compiled with OCaml 4.13.0
   coqtop version runner-j2nyww-s-project-6138686-concurrent-0:/builds/coq/coq/_build/default,(HEAD detached at fc47230) (fc4723013ccb61d269b1012a4137751a097dba69)
   Expected coqc runtime on this file: 1.451 sec *)
Require Coq.PArith.BinPos.
Require Coq.NArith.BinNat.
Require Coq.ssr.ssreflect.
Require mathcomp.ssreflect.ssreflect.
Require Coq.ssr.ssrfun.
Require mathcomp.ssreflect.ssrnotations.
Require mathcomp.ssreflect.ssrfun.
Require Coq.ssr.ssrbool.
Require mathcomp.ssreflect.ssrbool.
Require mathcomp.ssreflect.eqtype.
Require Coq.NArith.Ndec.
Require Coq.setoid_ring.Ring.
Require mathcomp.ssreflect.ssrnat.
Require mathcomp.ssreflect.seq.
Require mathcomp.ssreflect.path.
Require mathcomp.ssreflect.div.
Require mathcomp.ssreflect.choice.
Require mathcomp.ssreflect.fintype.
Require mathcomp.ssreflect.tuple.
Require mathcomp.ssreflect.finfun.
Require mathcomp.ssreflect.bigop.
Require mathcomp.ssreflect.ssrAC.
Require mathcomp.ssreflect.finset.
Require mathcomp.ssreflect.prime.
Require mathcomp.ssreflect.order.
Require mathcomp.ssreflect.binomial.

Declare ML Module "coq-core.plugins.ltac".
Module Export AdmitTactic.
Module Import LocalFalse.
Inductive False : Prop := .
End LocalFalse.
Axiom proof_admitted : False.
Global Set Default Proof Mode "Classic".
Tactic Notation "admit" := abstract case proof_admitted.
End AdmitTactic.

Module Export mathcomp_DOT_algebra_DOT_ssralg_WRAPPED.
Module Export ssralg.
Import mathcomp.ssreflect.ssreflect.
Import mathcomp.ssreflect.ssrfun.
Import mathcomp.ssreflect.ssrbool.
Import mathcomp.ssreflect.eqtype.
Import mathcomp.ssreflect.ssrnat.
Import mathcomp.ssreflect.div.
Import mathcomp.ssreflect.seq.
Import mathcomp.ssreflect.choice.
Import mathcomp.ssreflect.fintype.
Import mathcomp.ssreflect.finfun.
Import mathcomp.ssreflect.bigop.
Import mathcomp.ssreflect.prime.
Import mathcomp.ssreflect.binomial.

 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 

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

Module Export Exports.
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
Admitted.
Lemma addrC : @commutative V V +%R.
Admitted.
Lemma add0r : @left_id V V 0 +%R.
Admitted.
Lemma addNr : @left_inverse V V V 0 -%R +%R.
Admitted.

Lemma addr0 : @right_id V V 0 +%R.
Admitted.
Lemma addrN : @right_inverse V V V 0 -%R +%R.
Admitted.
Definition subrr := addrN.

Canonical add_monoid := Monoid.Law addrA add0r addr0.
Canonical add_comoid := Monoid.ComLaw addrC.

Lemma addrCA : @left_commutative V V +%R.
Admitted.
Lemma addrAC : @right_commutative V V +%R.
Admitted.
Lemma addrACA : @interchange V +%R +%R.
Admitted.

Lemma addKr : @left_loop V V -%R +%R.
Admitted.
Lemma addNKr : @rev_left_loop V V -%R +%R.
Admitted.
Lemma addrK : @right_loop V V -%R +%R.
Admitted.
Lemma addrNK : @rev_right_loop V V -%R +%R.
Admitted.
Definition subrK := addrNK.
Lemma subKr x : involutive (fun y => x - y).
Admitted.
Lemma addrI : @right_injective V V V +%R.
Admitted.
Lemma addIr : @left_injective V V V +%R.
Admitted.
Lemma subrI : right_injective (fun x y => x - y).
Admitted.
Lemma subIr : left_injective (fun x y => x - y).
Admitted.
Lemma opprK : @involutive V -%R.
Admitted.
Lemma oppr_inj : @injective V V -%R.
Admitted.
Lemma oppr0 : -0 = 0 :> V.
Admitted.
Lemma oppr_eq0 x : (- x == 0) = (x == 0).
Admitted.

Lemma subr0 x : x - 0 = x.
Admitted.
Lemma sub0r x : 0 - x = - x.
Admitted.

Lemma opprB x y : - (x - y) = y - x.
Admitted.

Lemma opprD : {morph -%R: x y / x + y : V}.
Admitted.

Lemma addrKA z x y : (x + z) - (z + y) = x - y.
Admitted.

Lemma subrKA z x y : (x - z) + (z + y) = x + y.
Admitted.

Lemma addr0_eq x y : x + y = 0 -> - x = y.
Admitted.

Lemma subr0_eq x y : x - y = 0 -> x = y.
Admitted.

Lemma subr_eq x y z : (x - z == y) = (x == y + z).
Admitted.

Lemma subr_eq0 x y : (x - y == 0) = (x == y).
Admitted.

Lemma addr_eq0 x y : (x + y == 0) = (x == - y).
Admitted.

Lemma eqr_opp x y : (- x == - y) = (x == y).
Admitted.

Lemma eqr_oppLR x y : (- x == y) = (x == - y).
Admitted.

Lemma mulr0n x : x *+ 0 = 0.
Admitted.
Lemma mulr1n x : x *+ 1 = x.
Admitted.
Lemma mulr2n x : x *+ 2 = x + x.
Admitted.

Lemma mulrS x n : x *+ n.+1 = x + x *+ n.
Admitted.

Lemma mulrSr x n : x *+ n.+1 = x *+ n + x.
Admitted.

Lemma mulrb x (b : bool) : x *+ b = (if b then x else 0).
Admitted.

Lemma mul0rn n : 0 *+ n = 0 :> V.
Admitted.

Lemma mulNrn x n : (- x) *+ n = x *- n.
Admitted.

Lemma mulrnDl n : {morph (fun x => x *+ n) : x y / x + y}.
Admitted.

Lemma mulrnDr x m n : x *+ (m + n) = x *+ m + x *+ n.
Admitted.

Lemma mulrnBl n : {morph (fun x => x *+ n) : x y / x - y}.
Admitted.

Lemma mulrnBr x m n : n <= m -> x *+ (m - n) = x *+ m - x *+ n.
Admitted.

Lemma mulrnA x m n : x *+ (m * n) = x *+ m *+ n.
Admitted.

Lemma mulrnAC x m n : x *+ m *+ n = x *+ n *+ m.
Admitted.

Lemma iter_addr n x y : iter n (+%R x) y = x *+ n + y.
Admitted.

Lemma iter_addr_0 n x : iter n (+%R x) 0 = x *+ n.
Admitted.

Lemma sumrN I r P (F : I -> V) :
  (\sum_(i <- r | P i) - F i = - (\sum_(i <- r | P i) F i)).
Admitted.

Lemma sumrB I r (P : pred I) (F1 F2 : I -> V) :
  \sum_(i <- r | P i) (F1 i - F2 i)
     = \sum_(i <- r | P i) F1 i - \sum_(i <- r | P i) F2 i.
Admitted.

Lemma sumrMnl I r P (F : I -> V) n :
  \sum_(i <- r | P i) F i *+ n = (\sum_(i <- r | P i) F i) *+ n.
Admitted.

Lemma sumrMnr x I r P (F : I -> nat) :
  \sum_(i <- r | P i) x *+ F i = x *+ (\sum_(i <- r | P i) F i).
Admitted.

Lemma sumr_const (I : finType) (A : pred I) x : \sum_(i in A) x = x *+ #|A|.
Admitted.

Lemma sumr_const_nat m n x : \sum_(n <= i < m) x = x *+ (m - n).
Admitted.

Lemma telescope_sumr n m (f : nat -> V) : n <= m ->
  \sum_(n <= k < m) (f k.+1 - f k) = f m - f n.
Admitted.

Section ClosedPredicates.

Variable S : {pred V}.

Definition addr_closed := 0 \in S /\ {in S &, forall u v, u + v \in S}.
Definition oppr_closed := {in S, forall u, - u \in S}.
Definition subr_2closed := {in S &, forall u v, u - v \in S}.
Definition zmod_closed := 0 \in S /\ subr_2closed.

Lemma zmod_closedN : zmod_closed -> oppr_closed.
Admitted.

Lemma zmod_closedD : zmod_closed -> addr_closed.
Admitted.

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

Module Export Exports.
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
Definition one (R : ringType) : R. exact (Ring.one (Ring.class R)). Defined.
Definition mul (R : ringType) : R -> R -> R. exact (Ring.mul (Ring.class R)). Defined.
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
Definition char (R : Ring.type) of phant R : nat_pred. exact ([pred p | prime p & p%:R == 0 :> R]). Defined.

Local Notation "[ 'char' R ]" := (char (Phant R)) : ring_scope.

 
Definition converse R : Type := R.
Local Notation "R ^c" := (converse R) (at level 2, format "R ^c") : type_scope.

Section RingTheory.

Variable R : ringType.
Implicit Types x y : R.

Lemma mulrA : @associative R *%R.
Admitted.
Lemma mul1r : @left_id R R 1 *%R.
Admitted.
Lemma mulr1 : @right_id R R 1 *%R.
Admitted.
Lemma mulrDl : @left_distributive R R *%R +%R.
Admitted.
Lemma mulrDr : @right_distributive R R *%R +%R.
Admitted.
Lemma oner_neq0 : 1 != 0 :> R.
Admitted.
Lemma oner_eq0 : (1 == 0 :> R) = false.
Admitted.

Lemma mul0r : @left_zero R R 0 *%R.
Admitted.
Lemma mulr0 : @right_zero R R 0 *%R.
Admitted.
Lemma mulrN x y : x * (- y) = - (x * y).
Admitted.
Lemma mulNr x y : (- x) * y = - (x * y).
Admitted.
Lemma mulrNN x y : (- x) * (- y) = x * y.
Admitted.
Lemma mulN1r x : -1 * x = - x.
Admitted.
Lemma mulrN1 x : x * -1 = - x.
Admitted.

Canonical mul_monoid := Monoid.Law mulrA mul1r mulr1.
Canonical muloid := Monoid.MulLaw mul0r mulr0.
Canonical addoid := Monoid.AddLaw mulrDl mulrDr.

Lemma mulr_suml I r P (F : I -> R) x :
  (\sum_(i <- r | P i) F i) * x = \sum_(i <- r | P i) F i * x.
Admitted.

Lemma mulr_sumr I r P (F : I -> R) x :
  x * (\sum_(i <- r | P i) F i) = \sum_(i <- r | P i) x * F i.
Admitted.

Lemma mulrBl x y z : (y - z) * x = y * x - z * x.
Admitted.

Lemma mulrBr x y z : x * (y - z) = x * y - x * z.
Admitted.

Lemma mulrnAl x y n : (x *+ n) * y = (x * y) *+ n.
Admitted.

Lemma mulrnAr x y n : x * (y *+ n) = (x * y) *+ n.
Admitted.

Lemma mulr_natl x n : n%:R * x = x *+ n.
Admitted.

Lemma mulr_natr x n : x * n%:R = x *+ n.
Admitted.

Lemma natrD m n : (m + n)%:R = m%:R + n%:R :> R.
Admitted.

Lemma natrB m n : n <= m -> (m - n)%:R = m%:R - n%:R :> R.
Admitted.

Definition natr_sum := big_morph (natmul 1) natrD (mulr0n 1).

Lemma natrM m n : (m * n)%:R = m%:R * n%:R :> R.
Admitted.

Lemma expr0 x : x ^+ 0 = 1.
Admitted.
Lemma expr1 x : x ^+ 1 = x.
Admitted.
Lemma expr2 x : x ^+ 2 = x * x.
Admitted.

Lemma exprS x n : x ^+ n.+1 = x * x ^+ n.
Admitted.

Lemma expr0n n : 0 ^+ n = (n == 0%N)%:R :> R.
Admitted.

Lemma expr1n n : 1 ^+ n = 1 :> R.
Admitted.

Lemma exprD x m n : x ^+ (m + n) = x ^+ m * x ^+ n.
Admitted.

Lemma exprSr x n : x ^+ n.+1 = x ^+ n * x.
Admitted.

Lemma expr_sum x (I : Type) (s : seq I) (P : pred I) F :
  x ^+ (\sum_(i <- s | P i) F i) = \prod_(i <- s | P i) x ^+ F i :> R.
Admitted.

Lemma commr_sym x y : comm x y -> comm y x.
Admitted.
Lemma commr_refl x : comm x x.
Admitted.

Lemma commr0 x : comm x 0.
Admitted.

Lemma commr1 x : comm x 1.
Admitted.

Lemma commrN x y : comm x y -> comm x (- y).
Admitted.

Lemma commrN1 x : comm x (-1).
Admitted.

Lemma commrD x y z : comm x y -> comm x z -> comm x (y + z).
Admitted.

Lemma commrB x y z : comm x y -> comm x z -> comm x (y - z).
Admitted.

Lemma commr_sum (I : Type) (s : seq I) (P : pred I) (F : I -> R) x :
  (forall i, P i -> comm x (F i)) -> comm x (\sum_(i <- s | P i) F i).
Admitted.

Lemma commrMn x y n : comm x y -> comm x (y *+ n).
Admitted.

Lemma commrM x y z : comm x y -> comm x z -> comm x (y * z).
Admitted.

Lemma commr_prod (I : Type) (s : seq I) (P : pred I) (F : I -> R) x :
  (forall i, P i -> comm x (F i)) -> comm x (\prod_(i <- s | P i) F i).
Admitted.

Lemma commr_nat x n : comm x n%:R.
Admitted.

Lemma commrX x y n : comm x y -> comm x (y ^+ n).
Admitted.

Lemma exprMn_comm x y n : comm x y -> (x * y) ^+ n = x ^+ n * y ^+ n.
Admitted.

Lemma commr_sign x n : comm x ((-1) ^+ n).
Admitted.

Lemma exprMn_n x m n : (x *+ m) ^+ n = x ^+ n *+ (m ^ n) :> R.
Admitted.

Lemma exprM x m n : x ^+ (m * n) = x ^+ m ^+ n.
Admitted.

Lemma exprAC x m n : (x ^+ m) ^+ n = (x ^+ n) ^+ m.
Admitted.

Lemma expr_mod n x i : x ^+ n = 1 -> x ^+ (i %% n) = x ^+ i.
Admitted.

Lemma expr_dvd n x i : x ^+ n = 1 -> n %| i -> x ^+ i = 1.
Admitted.

Lemma natrX n k : (n ^ k)%:R = n%:R ^+ k :> R.
Admitted.

Lemma signr_odd n : (-1) ^+ (odd n) = (-1) ^+ n :> R.
Admitted.

Lemma signr_eq0 n : ((-1) ^+ n == 0 :> R) = false.
Admitted.

Lemma mulr_sign (b : bool) x : (-1) ^+ b * x = (if b then - x else x).
Admitted.

Lemma signr_addb b1 b2 : (-1) ^+ (b1 (+) b2) = (-1) ^+ b1 * (-1) ^+ b2 :> R.
Admitted.

Lemma signrE (b : bool) : (-1) ^+ b = 1 - b.*2%:R :> R.
Admitted.

Lemma signrN b : (-1) ^+ (~~ b) = - (-1) ^+ b :> R.
Admitted.

Lemma mulr_signM (b1 b2 : bool) x1 x2 :
  ((-1) ^+ b1 * x1) * ((-1) ^+ b2 * x2) = (-1) ^+ (b1 (+) b2) * (x1 * x2).
Admitted.

Lemma exprNn x n : (- x) ^+ n = (-1) ^+ n * x ^+ n :> R.
Admitted.

Lemma sqrrN x : (- x) ^+ 2 = x ^+ 2.
Admitted.

Lemma sqrr_sign n : ((-1) ^+ n) ^+ 2 = 1 :> R.
Admitted.

Lemma signrMK n : @involutive R ( *%R ((-1) ^+ n)).
Admitted.

Lemma lastr_eq0 (s : seq R) x : x != 0 -> (last x s == 0) = (last 1 s == 0).
Admitted.

Lemma mulrI_eq0 x y : lreg x -> (x * y == 0) = (y == 0).
Admitted.

Lemma lreg_neq0 x : lreg x -> x != 0.
Admitted.

Lemma mulrI0_lreg x : (forall y, x * y = 0 -> y = 0) -> lreg x.
Admitted.

Lemma lregN x : lreg x -> lreg (- x).
Admitted.

Lemma lreg1 : lreg (1 : R).
Admitted.

Lemma lregM x y : lreg x -> lreg y -> lreg (x * y).
Admitted.

Lemma lregMl (a b: R) : lreg (a * b) -> lreg b.
Admitted.

Lemma rregMr (a b: R) : rreg (a * b) -> rreg a.
Admitted.

Lemma lregX x n : lreg x -> lreg (x ^+ n).
Admitted.

Lemma lreg_sign n : lreg ((-1) ^+ n : R).
Admitted.

Lemma iter_mulr n x y : iter n ( *%R x) y = x ^+ n * y.
Admitted.

Lemma iter_mulr_1 n x : iter n ( *%R x) 1 = x ^+ n.
Admitted.

Lemma prodr_const (I : finType) (A : pred I) x : \prod_(i in A) x = x ^+ #|A|.
Admitted.

Lemma prodr_const_nat n m x : \prod_(n <= i < m) x = x ^+ (m - n).
Admitted.

Lemma prodrXr x I r P (F : I -> nat) :
  \prod_(i <- r | P i) x ^+ F i = x ^+ (\sum_(i <- r | P i) F i).
Admitted.

Lemma prodrN (I : finType) (A : pred I) (F : I -> R) :
  \prod_(i in A) - F i = (- 1) ^+ #|A| * \prod_(i in A) F i.
Admitted.

Lemma prodrMn (I : Type) (s : seq I) (P : pred I) (F : I -> R) (g : I -> nat) :
  \prod_(i <- s | P i) (F i *+ g i) =
  \prod_(i <- s | P i) (F i) *+ \prod_(i <- s | P i) g i.
Admitted.

Lemma prodrMn_const n (I : finType) (A : pred I) (F : I -> R) :
  \prod_(i in A) (F i *+ n) = \prod_(i in A) F i *+ n ^ #|A|.
Admitted.

Lemma natr_prod I r P (F : I -> nat) :
  (\prod_(i <- r | P i) F i)%:R = \prod_(i <- r | P i) (F i)%:R :> R.
Admitted.

Lemma exprDn_comm x y n (cxy : comm x y) :
  (x + y) ^+ n = \sum_(i < n.+1) (x ^+ (n - i) * y ^+ i) *+ 'C(n, i).
Admitted.

Lemma exprBn_comm x y n (cxy : comm x y) :
  (x - y) ^+ n =
    \sum_(i < n.+1) ((-1) ^+ i * x ^+ (n - i) * y ^+ i) *+ 'C(n, i).
Admitted.

Lemma subrXX_comm x y n (cxy : comm x y) :
  x ^+ n - y ^+ n = (x - y) * (\sum_(i < n) x ^+ (n.-1 - i) * y ^+ i).
Admitted.

Lemma exprD1n x n : (x + 1) ^+ n = \sum_(i < n.+1) x ^+ i *+ 'C(n, i).
Admitted.

Lemma subrX1 x n : x ^+ n - 1 = (x - 1) * (\sum_(i < n) x ^+ i).
Admitted.

Lemma sqrrD1 x : (x + 1) ^+ 2 = x ^+ 2 + x *+ 2 + 1.
Admitted.

Lemma sqrrB1 x : (x - 1) ^+ 2 = x ^+ 2 - x *+ 2 + 1.
Admitted.

Lemma subr_sqr_1 x : x ^+ 2 - 1 = (x - 1) * (x + 1).
Admitted.

Definition Frobenius_aut p of p \in [char R] := fun x => x ^+ p.

Section FrobeniusAutomorphism.

Variable p : nat.
Hypothesis charFp : p \in [char R].

Lemma charf0 : p%:R = 0 :> R.
Admitted.
Lemma charf_prime : prime p.
Admitted.
Hint Resolve charf_prime : core.

Lemma mulrn_char x : x *+ p = 0.
Admitted.

Lemma natr_mod_char n : (n %% p)%:R = n%:R :> R.
Admitted.

Lemma dvdn_charf n : (p %| n)%N = (n%:R == 0 :> R).
Admitted.

Lemma charf_eq : [char R] =i (p : nat_pred).
Admitted.

Lemma bin_lt_charf_0 k : 0 < k < p -> 'C(p, k)%:R = 0 :> R.
Admitted.

Local Notation "x ^f" := (Frobenius_aut charFp x).

Lemma Frobenius_autE x : x^f = x ^+ p.
Admitted.
Local Notation fE := Frobenius_autE.

Lemma Frobenius_aut0 : 0^f = 0.
Admitted.

Lemma Frobenius_aut1 : 1^f = 1.
Admitted.

Lemma Frobenius_autD_comm x y (cxy : comm x y) : (x + y)^f = x^f + y^f.
Admitted.

Lemma Frobenius_autMn x n : (x *+ n)^f = x^f *+ n.
Admitted.

Lemma Frobenius_aut_nat n : (n%:R)^f = n%:R.
Admitted.

Lemma Frobenius_autM_comm x y : comm x y -> (x * y)^f = x^f * y^f.
Admitted.

Lemma Frobenius_autX x n : (x ^+ n)^f = x^f ^+ n.
Admitted.

Lemma Frobenius_autN x : (- x)^f = - x^f.
Admitted.

Lemma Frobenius_autB_comm x y : comm x y -> (x - y)^f = x^f - y^f.
Admitted.

End FrobeniusAutomorphism.

Lemma exprNn_char x n : [char R].-nat n -> (- x) ^+ n = - (x ^+ n).
Admitted.

Section Char2.

Hypothesis charR2 : 2 \in [char R].

Lemma addrr_char2 x : x + x = 0.
Admitted.

Lemma oppr_char2 x : - x = x.
Admitted.

Lemma subr_char2 x y : x - y = x + y.
Admitted.

Lemma addrK_char2 x : involutive (+%R^~ x).
Admitted.

Lemma addKr_char2 x : involutive (+%R x).
Admitted.

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
Admitted.

Lemma smulr_closedN : smulr_closed -> oppr_closed S.
Admitted.

Lemma semiring_closedD : semiring_closed -> addr_closed S.
Admitted.

Lemma semiring_closedM : semiring_closed -> mulr_closed.
Admitted.

Lemma subring_closedB : subring_closed -> zmod_closed S.
Admitted.

Lemma subring_closedM : subring_closed -> smulr_closed.
Admitted.

Lemma subring_closed_semi : subring_closed -> semiring_closed.
Admitted.

End ClosedPredicates.

End RingTheory.

Section RightRegular.

Variable R : ringType.
Implicit Types x y : R.
Let Rc := converse_ringType R.

Lemma mulIr_eq0 x y : rreg x -> (y * x == 0) = (y == 0).
Admitted.

Lemma mulIr0_rreg x : (forall y, y * x = 0 -> y = 0) -> rreg x.
Admitted.

Lemma rreg_neq0 x : rreg x -> x != 0.
Admitted.

Lemma rregN x : rreg x -> rreg (- x).
Admitted.

Lemma rreg1 : rreg (1 : R).
Admitted.

Lemma rregM x y : rreg x -> rreg y -> rreg (x * y).
Admitted.

Lemma revrX x n : (x : Rc) ^+ n = (x : R) ^+ n.
Admitted.

Lemma rregX x n : rreg x -> rreg (x ^+ n).
Admitted.

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
Definition scale (R : ringType) (V : lmodType R) : R -> V -> V. exact (Lmodule.scale (Lmodule.class V)). Defined.

Local Notation "*:%R" := (@scale _ _) : fun_scope.
Local Notation "a *: v" := (scale a v) : ring_scope.

Section LmoduleTheory.

Variables (R : ringType) (V : lmodType R).
Implicit Types (a b c : R) (u v : V).

Local Notation "*:%R" := (@scale R V) : fun_scope.

Lemma scalerA a b v : a *: (b *: v) = a * b *: v.
Admitted.

Lemma scale1r : @left_id R V 1 *:%R.
Admitted.

Lemma scalerDr a : {morph *:%R a : u v / u + v}.
Admitted.

Lemma scalerDl v : {morph *:%R^~ v : a b / a + b}.
Admitted.

Lemma scale0r v : 0 *: v = 0.
Admitted.

Lemma scaler0 a : a *: 0 = 0 :> V.
Admitted.

Lemma scaleNr a v : - a *: v = - (a *: v).
Admitted.

Lemma scaleN1r v : (- 1) *: v = - v.
Admitted.

Lemma scalerN a v : a *: (- v) = - (a *: v).
Admitted.

Lemma scalerBl a b v : (a - b) *: v = a *: v - b *: v.
Admitted.

Lemma scalerBr a u v : a *: (u - v) = a *: u - a *: v.
Admitted.

Lemma scaler_nat n v : n%:R *: v = v *+ n.
Admitted.

Lemma scaler_sign (b : bool) v: (-1) ^+ b *: v = (if b then - v else v).
Admitted.

Lemma signrZK n : @involutive V ( *:%R ((-1) ^+ n)).
Admitted.

Lemma scalerMnl a v n : a *: v *+ n = (a *+ n) *: v.
Admitted.

Lemma scalerMnr a v n : a *: v *+ n = a *: (v *+ n).
Admitted.

Lemma scaler_suml v I r (P : pred I) F :
  (\sum_(i <- r | P i) F i) *: v = \sum_(i <- r | P i) F i *: v.
Admitted.

Lemma scaler_sumr a I r (P : pred I) (F : I -> V) :
  a *: (\sum_(i <- r | P i) F i) = \sum_(i <- r | P i) a *: F i.
Admitted.

Section ClosedPredicates.

Variable S : {pred V}.

Definition scaler_closed := forall a, {in S, forall v, a *: v \in S}.
Definition linear_closed := forall a, {in S &, forall u v, a *: u + v \in S}.
Definition submod_closed := 0 \in S /\ linear_closed.

Lemma linear_closedB : linear_closed -> subr_2closed S.
Admitted.

Lemma submod_closedB : submod_closed -> zmod_closed S.
Admitted.

Lemma submod_closedZ : submod_closed -> scaler_closed.
Admitted.

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

Module Export Exports.
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
Admitted.

Lemma mulr_algl a x : a%:A * x = a *: x.
Admitted.

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
Admitted.

Lemma subalg_closedBM : subalg_closed -> subring_closed S.
Admitted.

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

Module Export Exports.
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
Definition null_fun_head (phV : phant V) of U : V. exact (let: Phant := phV in 0). Defined.
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
Admitted.

Lemma raddf0 : f 0 = 0.
Admitted.

Lemma raddf_eq0 x : injective f -> (f x == 0) = (x == 0).
Admitted.

Lemma raddf_inj : (forall x, f x = 0 -> x = 0) -> injective f.
Admitted.

Lemma raddfN : {morph f : x / - x}.
Admitted.

Lemma raddfD : {morph f : x y / x + y}.
Admitted.

Lemma raddfMn n : {morph f : x / x *+ n}.
Admitted.

Lemma raddfMNn n : {morph f : x / x *- n}.
Admitted.

Lemma raddf_sum I r (P : pred I) E :
  f (\sum_(i <- r | P i) E i) = \sum_(i <- r | P i) f (E i).
Admitted.

Lemma can2_additive f' : cancel f f' -> cancel f' f -> additive f'.
Admitted.

Lemma bij_additive :
  bijective f -> exists2 f' : {additive V -> U}, cancel f f' & cancel f' f.
Admitted.

Fact locked_is_additive : additive (locked_with k (f : U -> V)).
Admitted.
Canonical locked_additive := Additive locked_is_additive.

End Properties.

Section RingProperties.

Variables (R S : ringType) (f : {additive R -> S}).

Lemma raddfMnat n x : f (n%:R * x) = n%:R * f x.
Admitted.

Lemma raddfMsign n x : f ((-1) ^+ n * x) = (-1) ^+ n * f x.
Admitted.

Variables (U : lmodType R) (V : lmodType S) (h : {additive U -> V}).

Lemma raddfZnat n u : h (n%:R *: u) = n%:R *: h u.
Admitted.

Lemma raddfZsign n u : h ((-1) ^+ n *: u) = (-1) ^+ n *: h u.
Admitted.

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
Admitted.
Canonical mull_fun_additive := Additive mull_fun_is_additive.

Fact mulr_fun_is_additive : additive (a \o* f).
Admitted.
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

Module Export Exports.
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
Admitted.
Lemma rmorphD : {morph f : x y / x + y}.
Admitted.
Lemma rmorphB : {morph f: x y / x - y}.
Admitted.
Lemma rmorphMn n : {morph f : x / x *+ n}.
Admitted.
Lemma rmorphMNn n : {morph f : x / x *- n}.
Admitted.
Lemma rmorph_sum I r (P : pred I) E :
  f (\sum_(i <- r | P i) E i) = \sum_(i <- r | P i) f (E i).
Admitted.
Lemma rmorphMsign n : {morph f : x / (- 1) ^+ n * x}.
Admitted.

Lemma rmorphismP : rmorphism f.
Admitted.
Lemma rmorphismMP : multiplicative f.
Admitted.
Lemma rmorph1 : f 1 = 1.
Admitted.
Lemma rmorphM : {morph f: x y  / x * y}.
Admitted.

Lemma rmorph_prod I r (P : pred I) E :
  f (\prod_(i <- r | P i) E i) = \prod_(i <- r | P i) f (E i).
Admitted.

Lemma rmorphX n : {morph f: x / x ^+ n}.
Admitted.

Lemma rmorph_nat n : f n%:R = n%:R.
Admitted.
Lemma rmorphN1 : f (- 1) = (- 1).
Admitted.

Lemma rmorph_sign n : f ((- 1) ^+ n) = (- 1) ^+ n.
Admitted.

Lemma rmorph_char p : p \in [char R] -> p \in [char S].
Admitted.

Lemma rmorph_eq_nat x n : injective f -> (f x == n%:R) = (x == n%:R).
Admitted.

Lemma rmorph_eq1 x : injective f -> (f x == 1) = (x == 1).
Admitted.

Lemma can2_rmorphism f' : cancel f f' -> cancel f' f -> rmorphism f'.
Admitted.

Lemma bij_rmorphism :
  bijective f -> exists2 f' : {rmorphism S -> R}, cancel f f' & cancel f' f.
Admitted.

Fact locked_is_multiplicative : multiplicative (locked_with k (f : R -> S)).
Admitted.
Canonical locked_rmorphism := AddRMorphism locked_is_multiplicative.

End Properties.

Section Projections.

Variables (R S T : ringType) (f : {rmorphism S -> T}) (g : {rmorphism R -> S}).

Fact idfun_is_multiplicative : multiplicative (@idfun R).
admit.
Defined.
Canonical idfun_rmorphism := AddRMorphism idfun_is_multiplicative.

Fact comp_is_multiplicative : multiplicative (f \o g).
Admitted.
Canonical comp_rmorphism := AddRMorphism comp_is_multiplicative.

End Projections.

Section InAlgebra.

Variables (R : ringType) (A : lalgType R).

Fact in_alg_is_rmorphism : rmorphism (in_alg_loc A).
Admitted.
Canonical in_alg_additive := Additive in_alg_is_rmorphism.
Canonical in_alg_rmorphism := RMorphism in_alg_is_rmorphism.

Lemma in_algE a : in_alg_loc A a = a%:A.
Admitted.

End InAlgebra.

End RmorphismTheory.

Module Export Scale.

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
Admitted.
Lemma N1op : s_op (-1) =1 -%R.
Admitted.
Fact opB a : additive (s_op a).
Admitted.
Definition op_additive a := Additive (opB a).

Variables (aR : ringType) (nu : {rmorphism aR -> R}).
Fact comp_opE : nu \; s_op = nu \; s.
Admitted.
Fact compN1op : (nu \; s_op) (-1) =1 -%R.
Admitted.
Definition comp_law : law (nu \; s). exact (Law comp_opE compN1op (fun a => opB _)). Defined.

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
Admitted.

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

Module Export Exports.
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
Admitted.
Lemma linearN : {morph f : x / - x}.
Admitted.
Lemma linearD : {morph f : x y / x + y}.
Admitted.
Lemma linearB : {morph f : x y / x - y}.
Admitted.
Lemma linearMn n : {morph f : x / x *+ n}.
Admitted.
Lemma linearMNn n : {morph f : x / x *- n}.
Admitted.
Lemma linear_sum I r (P : pred I) E :
  f (\sum_(i <- r | P i) E i) = \sum_(i <- r | P i) f (E i).
Admitted.

Lemma linearZ_LR : scalable_for s f.
Admitted.
Lemma linearP a : {morph f : u v / a *: u + v >-> s a u + v}.
Admitted.

Fact locked_is_scalable : scalable_for s (locked_with k (f : U -> V)).
Admitted.
Canonical locked_linear := AddLinear locked_is_scalable.

End GenericProperties.

Section BidirectionalLinearZ.

Variables (U : lmodType R) (V : zmodType) (s : R -> V -> V).

 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 

Variables (S : ringType) (h : S -> V -> V) (h_law : Scale.law h).

Lemma linearZ c a (h_c := Scale.op h_law c) (f : Linear.map_for U s a h_c) u :
  f (a *: u) = h_c (Linear.wrap f u).
Admitted.

End BidirectionalLinearZ.

Section LmodProperties.

Variables (U V : lmodType R) (f : {linear U -> V}).

Lemma linearZZ : scalable f.
Admitted.
Lemma linearPZ : linear f.
Admitted.

Lemma can2_linear f' : cancel f f' -> cancel f' f -> linear f'.
Admitted.

Lemma bij_linear :
  bijective f -> exists2 f' : {linear V -> U}, cancel f f' & cancel f' f.
Admitted.

End LmodProperties.

Section ScalarProperties.

Variable (U : lmodType R) (f : {scalar U}).

Lemma scalarZ : scalable_for *%R f.
Admitted.
Lemma scalarP : scalar f.
Admitted.

End ScalarProperties.

Section LinearLmod.

Variables (W U : lmodType R) (V : zmodType) (s : R -> V -> V).
Variables (f : {linear U -> V | s}) (h : {linear W -> U}).

Lemma idfun_is_scalable : scalable (@idfun U).
admit.
Defined.
Canonical idfun_linear := AddLinear idfun_is_scalable.

Lemma opp_is_scalable : scalable (-%R : U -> U).
Admitted.
Canonical opp_linear := AddLinear opp_is_scalable.

Lemma comp_is_scalable : scalable_for s (f \o h).
Admitted.
Canonical comp_linear := AddLinear comp_is_scalable.

Variables (s_law : Scale.law s) (g : {linear U -> V | Scale.op s_law}).
Let Ds : s =1 Scale.op s_law.
Admitted.

Lemma null_fun_is_scalable : scalable_for (Scale.op s_law) (\0 : U -> V).
Admitted.
Canonical null_fun_linear := AddLinear null_fun_is_scalable.

Lemma add_fun_is_scalable : scalable_for s (f \+ g).
Admitted.
Canonical add_fun_linear := AddLinear add_fun_is_scalable.

Lemma sub_fun_is_scalable : scalable_for s (f \- g).
Admitted.
Canonical sub_fun_linear := AddLinear sub_fun_is_scalable.

End LinearLmod.

Section LinearLalg.

Variables (A : lalgType R) (U : lmodType R).

Variables (a : A) (f : {linear U -> A}).

Fact mulr_fun_is_scalable : scalable (a \o* f).
Admitted.
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

Module Export Exports.
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
Admitted.

Lemma lrmorphismP : lrmorphism f.
Admitted.

Lemma can2_lrmorphism f' : cancel f f' -> cancel f' f -> lrmorphism f'.
Admitted.

Lemma bij_lrmorphism :
  bijective f -> exists2 f' : {lrmorphism B -> A}, cancel f f' & cancel f' f.
Admitted.

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

Module Export Exports.
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
Admitted.
Canonical mul_comoid := Monoid.ComLaw mulrC.
Lemma mulrCA : @left_commutative R R *%R.
Admitted.
Lemma mulrAC : @right_commutative R R *%R.
Admitted.
Lemma mulrACA : @interchange R *%R *%R.
Admitted.

Lemma exprMn n : {morph (fun x => x ^+ n) : x y / x * y}.
Admitted.

Lemma prodrXl n I r (P : pred I) (F : I -> R) :
  \prod_(i <- r | P i) F i ^+ n = (\prod_(i <- r | P i) F i) ^+ n.
Admitted.

Lemma prodr_undup_exp_count (I : eqType) r (P : pred I) (F : I -> R) :
  \prod_(i <- undup r | P i) F i ^+ count_mem i r = \prod_(i <- r | P i) F i.
Admitted.

Lemma exprDn x y n :
  (x + y) ^+ n = \sum_(i < n.+1) (x ^+ (n - i) * y ^+ i) *+ 'C(n, i).
Admitted.

Lemma exprBn x y n :
  (x - y) ^+ n =
     \sum_(i < n.+1) ((-1) ^+ i * x ^+ (n - i) * y ^+ i) *+ 'C(n, i).
Admitted.

Lemma subrXX x y n :
  x ^+ n - y ^+ n = (x - y) * (\sum_(i < n) x ^+ (n.-1 - i) * y ^+ i).
Admitted.

Lemma sqrrD x y : (x + y) ^+ 2 = x ^+ 2 + x * y *+ 2 + y ^+ 2.
Admitted.

Lemma sqrrB x y : (x - y) ^+ 2 = x ^+ 2 - x * y *+ 2 + y ^+ 2.
Admitted.

Lemma subr_sqr x y : x ^+ 2 - y ^+ 2 = (x - y) * (x + y).
Admitted.

Lemma subr_sqrDB x y : (x + y) ^+ 2 - (x - y) ^+ 2 = x * y *+ 4.
Admitted.

Section FrobeniusAutomorphism.

Variables (p : nat) (charRp : p \in [char R]).

Lemma Frobenius_aut_is_rmorphism : rmorphism (Frobenius_aut charRp).
Admitted.

Canonical Frobenius_aut_additive := Additive Frobenius_aut_is_rmorphism.
Canonical Frobenius_aut_rmorphism := RMorphism Frobenius_aut_is_rmorphism.

End FrobeniusAutomorphism.

Lemma exprDn_char x y n : [char R].-nat n -> (x + y) ^+ n = x ^+ n + y ^+ n.
Admitted.

Lemma rmorph_comm (S : ringType) (f : {rmorphism R -> S}) x y :
  comm (f x) (f y).
Admitted.

Section ScaleLinear.

Variables (U V : lmodType R) (b : R) (f : {linear U -> V}).

Lemma scale_is_scalable : scalable ( *:%R b : V -> V).
Admitted.
Canonical scale_linear := AddLinear scale_is_scalable.

Lemma scale_fun_is_scalable : scalable (b \*: f).
Admitted.
Canonical scale_fun_linear := AddLinear scale_fun_is_scalable.

End ScaleLinear.

End ComRingTheory.

Module Algebra.

Section Mixin.

Variables (R : ringType) (A : lalgType R).

Definition axiom := forall k (x y : A), k *: (x * y) = x * (k *: y).

Lemma comm_axiom : phant A -> commutative (@mul A) -> axiom.
Admitted.

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

Module Export Exports.
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

Module Export Exports.
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
Admitted.

Lemma scalerCA k x y : k *: x * y = x * (k *: y).
Admitted.

Lemma mulr_algr a x : x * a%:A = a *: x.
Admitted.

Lemma comm_alg a x : comm a%:A x.
Admitted.

Lemma exprZn k x n : (k *: x) ^+ n = k ^+ n *: x ^+ n.
Admitted.

Lemma scaler_prod I r (P : pred I) (F : I -> R) (G : I -> A) :
  \prod_(i <- r | P i) (F i *: G i) =
    \prod_(i <- r | P i) F i *: \prod_(i <- r | P i) G i.
Admitted.

Lemma scaler_prodl (I : finType) (S : pred I) (F : I -> A) k :
  \prod_(i in S) (k *: F i)  = k ^+ #|S| *: \prod_(i in S) F i.
Admitted.

Lemma scaler_prodr (I : finType) (S : pred I) (F : I -> R) x :
  \prod_(i in S) (F i *: x)  = \prod_(i in S) F i *: x ^+ #|S|.
Admitted.

Canonical regular_comRingType := [comRingType of R^o].
Canonical regular_algType := CommAlgType R R^o.
Canonical regular_comAlgType := [comAlgType R of R^o].

Variables (U : lmodType R) (a : A) (f : {linear U -> A}).

Lemma mull_fun_is_scalable : scalable (a \*o f).
Admitted.
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

Module Export Exports.
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
Admitted.
Canonical unit_keyed R := KeyedQualifier (@unit_key R).
Definition inv {R : unitRingType} : R -> R. exact (UnitRing.inv (UnitRing.class R)). Defined.

Local Notation "x ^-1" := (inv x).
Local Notation "x / y" := (x * y^-1).
Local Notation "x ^- n" := ((x ^+ n)^-1).

Section UnitRingTheory.

Variable R : unitRingType.
Implicit Types x y : R.

Lemma divrr : {in unit, right_inverse 1 (@inv R) *%R}.
Admitted.
Definition mulrV := divrr.

Lemma mulVr : {in unit, left_inverse 1 (@inv R) *%R}.
Admitted.

Lemma invr_out x : x \isn't a unit -> x^-1 = x.
Admitted.

Lemma unitrP x : reflect (exists y, y * x = 1 /\ x * y = 1) (x \is a unit).
Admitted.

Lemma mulKr : {in unit, left_loop (@inv R) *%R}.
Admitted.

Lemma mulVKr : {in unit, rev_left_loop (@inv R) *%R}.
Admitted.

Lemma mulrK : {in unit, right_loop (@inv R) *%R}.
Admitted.

Lemma mulrVK : {in unit, rev_right_loop (@inv R) *%R}.
Admitted.
Definition divrK := mulrVK.

Lemma mulrI : {in @unit R, right_injective *%R}.
Admitted.

Lemma mulIr : {in @unit R, left_injective *%R}.
Admitted.

 
Lemma telescope_prodr n m (f : nat -> R) :
    (forall k, n < k < m -> f k \is a unit) -> n < m ->
  \prod_(n <= k < m) (f k / f k.+1) = f n / f m.
Admitted.

Lemma commrV x y : comm x y -> comm x y^-1.
Admitted.

Lemma unitrE x : (x \is a unit) = (x / x == 1).
Admitted.

Lemma invrK : involutive (@inv R).
Admitted.

Lemma invr_inj : injective (@inv R).
Admitted.

Lemma unitrV x : (x^-1 \in unit) = (x \in unit).
Admitted.

Lemma unitr1 : 1 \in @unit R.
Admitted.

Lemma invr1 : 1^-1 = 1 :> R.
Admitted.

Lemma div1r x : 1 / x = x^-1.
Admitted.
Lemma divr1 x : x / 1 = x.
Admitted.

Lemma natr_div m d :
  d %| m -> d%:R \is a @unit R -> (m %/ d)%:R = m%:R / d%:R :> R.
Admitted.

Lemma divrI : {in unit, right_injective (fun x y => x / y)}.
Admitted.

Lemma divIr : {in unit, left_injective (fun x y => x / y)}.
Admitted.

Lemma unitr0 : (0 \is a @unit R) = false.
Admitted.

Lemma invr0 : 0^-1 = 0 :> R.
Admitted.

Lemma unitrN1 : -1 \is a @unit R.
Admitted.

Lemma invrN1 : (-1)^-1 = -1 :> R.
Admitted.

Lemma invr_sign n : ((-1) ^- n) = (-1) ^+ n :> R.
Admitted.

Lemma unitrMl x y : y \is a unit -> (x * y \is a unit) = (x \is a unit).
Admitted.

Lemma unitrMr x y : x \is a unit -> (x * y \is a unit) = (y \is a unit).
Admitted.

Lemma invrM : {in unit &, forall x y, (x * y)^-1 = y^-1 * x^-1}.
Admitted.

Lemma unitrM_comm x y :
  comm x y -> (x * y \is a unit) = (x \is a unit) && (y \is a unit).
Admitted.

Lemma unitrX x n : x \is a unit -> x ^+ n \is a unit.
Admitted.

Lemma unitrX_pos x n : n > 0 -> (x ^+ n \in unit) = (x \in unit).
Admitted.

Lemma exprVn x n : x^-1 ^+ n = x ^- n.
Admitted.

Lemma exprB m n x : n <= m -> x \is a unit -> x ^+ (m - n) = x ^+ m / x ^+ n.
Admitted.

Lemma invr_neq0 x : x != 0 -> x^-1 != 0.
Admitted.

Lemma invr_eq0 x : (x^-1 == 0) = (x == 0).
Admitted.

Lemma invr_eq1 x : (x^-1 == 1) = (x == 1).
Admitted.

Lemma rev_unitrP (x y : R^c) : y * x = 1 /\ x * y = 1 -> x \is a unit.
Admitted.

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
Admitted.

Lemma divr_closedM : divr_closed -> mulr_closed S.
Admitted.

Lemma sdivr_closed_div : sdivr_closed -> divr_closed.
Admitted.

Lemma sdivr_closedM : sdivr_closed -> smulr_closed S.
Admitted.

Lemma divring_closedBM : divring_closed -> subring_closed S.
Admitted.

Lemma divring_closed_div : divring_closed -> sdivr_closed.
Admitted.

End ClosedPredicates.

End UnitRingTheory.

Arguments invrK {R}.
Arguments invr_inj {R} [x1 x2].

Section UnitRingMorphism.

Variables (R S : unitRingType) (f : {rmorphism R -> S}).

Lemma rmorph_unit x : x \in unit -> f x \in unit.
Admitted.

Lemma rmorphV : {in unit, {morph f: x / x^-1}}.
Admitted.

Lemma rmorph_div x y : y \in unit -> f (x / y) = f x / f y.
Admitted.

End UnitRingMorphism.

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

End ClassDef.

Module Import Exports.
Coercion base : class_of >-> ComRing.class_of.
Coercion base2 : class_of >-> UnitRing.class_of.
End Exports.

End ComUnitRing.
Import ComUnitRing.Exports.

Module UnitAlgebra.

Section ClassDef.

End ClassDef.

Module Export Exports.
End Exports.

End UnitAlgebra.

Module ComUnitAlgebra.

Section ClassDef.

End ClassDef.

Module Export Exports.
End Exports.

End ComUnitAlgebra.

Section ComUnitRingTheory.

End ComUnitRingTheory.

Section UnitAlgebraTheory.

Section ClosedPredicates.

End ClosedPredicates.

End UnitAlgebraTheory.

 
Module Pred.

Section Subtyping.

End Subtyping.

Section Extensionality.

End Extensionality.

Module Default.
End Default.

Module Export Exports.

End Exports.

End Pred.

Module Export DefaultPred.

End DefaultPred.

Section ZmodulePred.

Section Add.

End Add.

Section Opp.

End Opp.

Section Sub.

End Sub.

End ZmodulePred.

Section RingPred.

Section Mul.

End Mul.

End RingPred.

Section LmodPred.

End LmodPred.

Section UnitRingPred.

Section Div.

End Div.

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

Section Substitution.

End Substitution.

Section EvalTerm.

Variable R : unitRingType.
Fixpoint eval (e : seq R) (t : term R) {struct t} : R. exact (match t with
  | ('X_i)%T => e`_i
  | (x%:T)%T => x
  | (n%:R)%T => n%:R
  | (t1 + t2)%T => eval e t1 + eval e t2
  | (- t1)%T => - eval e t1
  | (t1 *+ n)%T => eval e t1 *+ n
  | (t1 * t2)%T => eval e t1 * eval e t2
  | t1^-1%T => (eval e t1)^-1
  | (t1 ^+ n)%T => eval e t1 ^+ n
  end). Defined.
Fixpoint holds (e : seq R) (f : formula R) {struct f} : Prop. exact (match f with
  | Bool b => b
  | (t1 == t2)%T => eval e t1 = eval e t2
  | Unit t1 => eval e t1 \in unit
  | (f1 /\ f2)%T => holds e f1 /\ holds e f2
  | (f1 \/ f2)%T => holds e f1 \/ holds e f2
  | (f1 ==> f2)%T => holds e f1 -> holds e f2
  | (~ f1)%T => ~ holds e f1
  | ('exists 'X_i, f1)%T => exists x, holds (set_nth 0 e i x) f1
  | ('forall 'X_i, f1)%T => forall x, holds (set_nth 0 e i x) f1
  end). Defined.

Section If.

End If.

Section Pick.

End Pick.

Section MultiQuant.

End MultiQuant.

End EvalTerm.

Module IntegralDomain.

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
Import IntegralDomain.Exports.

Section IntegralDomainTheory.

End IntegralDomainTheory.

Module Field.

Definition mixin_of (R : unitRingType) := forall x : R, x != 0 -> x \in unit.

Section Mixins.

End Mixins.

Section ClassDef.
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

Definition eqType := @Equality.Pack cT class.
Definition zmodType := @Zmodule.Pack cT class.
Definition ringType := @Ring.Pack cT class.
Definition comRingType := @ComRing.Pack cT class.
Definition unitRingType := @UnitRing.Pack cT class.

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> IntegralDomain.class_of.
Canonical eqType.
Canonical zmodType.
Canonical ringType.
Canonical comRingType.
Coercion unitRingType : type >-> UnitRing.type.
Canonical unitRingType.
Notation fieldType := type.
End Exports.

End Field.
Import Field.Exports.

Section FieldTheory.

Variable F : fieldType.
Implicit Types x y : F.
Lemma mulfK x : x != 0 -> cancel ( *%R^~ x) ( *%R^~ x^-1).
Admitted.

Lemma invfM : {morph @inv F : x y / x * y}.
Admitted.

Section FieldMorphismInj.

End FieldMorphismInj.

Section FieldMorphismInv.

End FieldMorphismInv.

Section ModuleTheory.

End ModuleTheory.

Section Predicates.

End Predicates.

End FieldTheory.

Module DecidableField.

Definition axiom (R : unitRingType) (s : seq R -> pred (formula R)) :=
  forall e f, reflect (holds e f) (s e f).

Record mixin_of (R : unitRingType) : Type :=
  Mixin { sat : seq R -> pred (formula R); satP : axiom sat}.

Section ClassDef.

End ClassDef.

Module Export Exports.
End Exports.

End DecidableField.

Section DecidableFieldTheory.

End DecidableFieldTheory.

Section QE_Mixin.

End QE_Mixin.

Module ClosedField.

 
Definition axiom (R : ringType) :=
  forall n (P : nat -> R), n > 0 ->
   exists x : R, x ^+ n = \sum_(i < n) P i * (x ^+ i).

Section ClassDef.

End ClassDef.

Module Export Exports.
End Exports.

End ClosedField.

Section ClosedFieldTheory.

End ClosedFieldTheory.

Module Export SubType.

Section Zmodule.

End Zmodule.

Section Ring.

End Ring.

Section Lmodule.

End Lmodule.

Section UnitRing.

End UnitRing.

Module Export Exports.

End Exports.

End SubType.

Module Export Theory.

End Theory.
Export Zmodule.Exports.
Export Ring.Exports.
Export UnitRing.Exports.
Export ComUnitRing.Exports.
Export IntegralDomain.Exports.
Export Field.Exports.

Variant Ione := IOne : Ione.
Variant Inatmul := INatmul : Ione -> nat -> Inatmul.
Variant Idummy_placeholder :=.
Definition parse (x : Number.uint) : Inatmul. exact (INatmul IOne (Nat.of_num_uint x)). Defined.
Definition print (x : Inatmul) : Number.uint. exact (match x with
  | INatmul IOne n => Number.UIntDecimal (Nat.to_uint n)
  end). Defined.

Arguments GRing.one {R}.
Number Notation Idummy_placeholder parse print (via Inatmul
  mapping [[GRing.natmul] => INatmul, [GRing.one] => IOne])
  : ring_scope.

Notation "0" := (zero _) : ring_scope.
Notation "- x" := (opp x) : ring_scope.
Notation "x + y" := (add x y) : ring_scope.
Notation "x - y" := (add x (- y)) : ring_scope.
Notation "x *+ n" := (natmul x n) : ring_scope.
Notation "- 1" := (opp 1) : ring_scope.
Notation "x * y" := (mul x y) : ring_scope.
Notation "x ^+ n" := (exp x n) : ring_scope.
Notation "x ^-1" := (inv x) : ring_scope.
Notation "x / y" := (mul x y^-1) : ring_scope.

 
Section FinFunZmod.

Section Sum.

End Sum.

End FinFunZmod.

Section FinFunRing.

End FinFunRing.

Section FinFunComRing.

End FinFunComRing.

Section FinFunLmod.

End FinFunLmod.

 
Section PairZmod.

End PairZmod.

Section PairRing.

End PairRing.

Section PairComRing.

End PairComRing.

Section PairLmod.

End PairLmod.

Section PairLalg.

End PairLalg.

Section PairAlg.

End PairAlg.

Section PairUnitRing.

End PairUnitRing.
Import mathcomp.ssreflect.ssreflect.
Import mathcomp.ssreflect.ssrfun.
Import mathcomp.ssreflect.ssrbool.
Import mathcomp.ssreflect.eqtype.
Import mathcomp.ssreflect.ssrnat.
Import mathcomp.ssreflect.choice.
Import mathcomp.ssreflect.ssrAC.
Import mathcomp.ssreflect.order.

Set Implicit Arguments.
Unset Strict Implicit.
Local Open Scope ring_scope.
Import GRing.Theory.

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
Definition comRingType := @GRing.ComRing.Pack cT class.
Definition unitRingType := @GRing.UnitRing.Pack cT class.

End ClassDef.

Module Export Exports.
Coercion order_base : class_of >-> Order.POrder.class_of.
Coercion normed_mixin : class_of >-> normed_mixin_of.
Canonical comRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
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

Structure type (phR : phant R) :=
  Pack { sort; _ : class_of sort }.

Variables (phR : phant R) (T : Type) (cT : type phR).
Definition pack b0 (m0 : @normed_mixin_of R (@GRing.Zmodule.Pack T b0)
                                          (NumDomain.class R)) :=
  Pack phR (@Class T b0 m0).

End ClassDef.
Coercion sort : type >-> Sortclass.
Notation normedZmodType R := (type (Phant R)).
Notation NormedZmodType R T m := (@pack _ (Phant R) T _ m).

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
Definition normr (R : numDomainType) (T : normedZmodType R) : T -> R.
Admitted.
Arguments normr {R T} x.

Notation norm := normr (only parsing).

Notation "`| x |" := (norm x) : ring_scope.

Module NumField.

Section ClassDef.
Record class_of R := Class {
  base  : NumDomain.class_of R;
  mixin : GRing.Field.mixin_of (num_for R base);
}.
Local Coercion base : class_of >-> NumDomain.class_of.
Local Coercion base2 R (c : class_of R) : GRing.Field.class_of _ :=
  GRing.Field.Class (@mixin _ c).

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition numDomainType := @NumDomain.Pack cT class.

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> NumDomain.class_of.
Coercion base2 : class_of >-> GRing.Field.class_of.
Coercion numDomainType : type >-> NumDomain.type.
Notation numFieldType := type.
End Exports.

End NumField.
Import NumField.Exports.

Module ClosedField.

Section ClassDef.

Record imaginary_mixin_of (R : numDomainType) := ImaginaryMixin {
  imaginary : R;
  conj_op : {rmorphism R -> R};
  _ : imaginary ^+ 2 = - 1;
  _ : forall x, x * conj_op x = `|x| ^+ 2;
}.
Record class_of R := Class {
  base : NumField.class_of R;
  decField_mixin : GRing.DecidableField.mixin_of (num_for R base);
  closedField_axiom : GRing.ClosedField.axiom (num_for R base);
  conj_mixin  : imaginary_mixin_of (num_for R base);
}.
Local Coercion base : class_of >-> NumField.class_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Definition eqType := @Equality.Pack cT class.
Definition zmodType := @GRing.Zmodule.Pack cT class.
Definition ringType := @GRing.Ring.Pack cT class.
Definition unitRingType := @GRing.UnitRing.Pack cT class.
Definition numDomainType := @NumDomain.Pack cT class.
Definition fieldType := @GRing.Field.Pack cT class.
Definition numFieldType := @NumField.Pack cT class.
Definition normedZmodType := NormedZmodType numDomainType cT class.

End ClassDef.

Module Export Exports.
Coercion sort : type >-> Sortclass.
Canonical eqType.
Canonical zmodType.
Canonical ringType.
Canonical unitRingType.
Canonical fieldType.
Canonical numFieldType.
Canonical normedZmodType.
Notation numClosedFieldType := type.
End Exports.

End ClosedField.
Import ClosedField.Exports.

Section NumDomain.
Variable R : numDomainType.

Lemma normrM : {morph norm : x y / (x : R) * y}.
Admitted.

End NumDomain.

Section NumIntegralDomainTheory.

Variable R : numDomainType.
Implicit Types (V : normedZmodType R) (x y z t : R).

Lemma normrX n x : `|x ^+ n| = `|x| ^+ n.
Admitted.

Section NormedZmoduleTheory.

Variable V : normedZmodType R.
Implicit Types (v w : V).

Lemma normr_id v : `| `|v| | = `|v|.
Admitted.

End NormedZmoduleTheory.

End NumIntegralDomainTheory.

Section NumFieldTheory.

Variable F : numFieldType.

Lemma normfV : {morph (@norm F F) : x / x ^-1}.
Admitted.

End NumFieldTheory.
Definition conjC {C : numClosedFieldType} : {rmorphism C -> C}.
Admitted.
Notation "z ^*" := (@conjC _ z) (at level 2, format "z ^*") : ring_scope.

Variable C : numClosedFieldType.
Implicit Types a x y z : C.

Definition normCK x : `|x| ^+ 2 = x * x^*.
Admitted.

Lemma conjCK : involutive (@conjC C).
Proof.
have JE x : x^* = `|x|^+2 / x.
  have [->|x_neq0] := eqVneq x 0; first by rewrite rmorph0 invr0 mulr0.
  by apply: (canRL (mulfK _)) => //; rewrite mulrC -normCK.
move=> x; have [->|x_neq0] := eqVneq x 0; first by rewrite !rmorph0.
rewrite !JE normrM normfV exprMn normrX normr_id.
rewrite invfM exprVn (AC (2*2) (1*(2*3)*4))/= -invfM -exprMn.
