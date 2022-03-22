(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "-projection-no-head-constant" "-w" "-redundant-canonical-projection" "-w" "-notation-overridden" "-w" "+duplicate-clear" "-w" "-ambiguous-paths" "-w" "+non-primitive-record" "-w" "+undeclared-scope" "-w" "-deprecated-hint-without-locality" "-w" "-deprecated-hint-rewrite-without-locality" "-w" "-deprecated-native-compiler-option" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/mathcomp/mathcomp" "mathcomp" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-I" "/github/workspace/builds/coq/coq-failing/_build_ci/mathcomp/mathcomp" "-top" "bug_01" "-native-compiler" "ondemand") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 5422 lines to 262 lines, then from 275 lines to 6956 lines, then from 6961 lines to 4136 lines, then from 3514 lines to 672 lines, then from 685 lines to 9231 lines, then from 9234 lines to 8788 lines, then from 8195 lines to 922 lines *)
(* coqc version 8.16+alpha compiled with OCaml 4.13.0
   coqtop version runner-j2nyww-s-project-6138686-concurrent-0:/builds/coq/coq/_build/default,(HEAD detached at fc47230) (fc4723013ccb61d269b1012a4137751a097dba69)
   Expected coqc runtime on this file: 0.762 sec *)
Require mathcomp.ssreflect.ssrAC.
Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.
Import mathcomp.ssreflect.ssrbool.
Import mathcomp.ssreflect.eqtype.
Import mathcomp.ssreflect.choice.

Set Implicit Arguments.

Module Export Order.

Module Export POrder.
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
End ClassDef.
Coercion mixin : class_of >-> mixin_of.

Section POrderDef.

End POrderDef.
Section ClassDef.
End ClassDef.

Section LatticeDef.

End LatticeDef.
Section ClassDef.
End ClassDef.
Section ClassDef.
End ClassDef.
Section ClassDef.
End ClassDef.
Section ClassDef.
End ClassDef.
Section ClassDef.
End ClassDef.
Section ClassDef.
End ClassDef.
Section ClassDef.
End ClassDef.
Section ClassDef.

End ClassDef.
Section ClassDef.
End ClassDef.
Section ClassDef.

End ClassDef.
Section ClassDef.

End ClassDef.
Section ClassDef.

End ClassDef.
Section ClassDef.

End ClassDef.

Section Comparable2.

End Comparable2.

Section Comparable3.

End Comparable3.

Section ArgExtremum.

End ArgExtremum.

Section ContraTheory.

End ContraTheory.

Section POrderMonotonyTheory.

End POrderMonotonyTheory.

Section ArgExtremum.

End ArgExtremum.

Section ContraTheory.

End ContraTheory.

Section TotalMonotonyTheory.

End TotalMonotonyTheory.

Section Total.

End Total.

Section Order.

Section Partial.

Section PCan.

End PCan.

End Partial.

Section Total.

Section PCan.

End PCan.

End Total.
End Order.

Section Lattice.

End Lattice.

Section DistrLattice.

End DistrLattice.

Section Partial.

End Partial.

Section Total.

End Total.

Section PossiblyTrivial.
End PossiblyTrivial.

Section NonTrivial.

End NonTrivial.

Section Lattice.

End Lattice.

Section BLattice.

End BLattice.

Section TBLattice.

End TBLattice.

Section DistrLattice.

End DistrLattice.

Section CBDistrLattice.

End CBDistrLattice.

Section CTBDistrLattice.

End CTBDistrLattice.

Section Total.

End Total.

Section FinDistrLattice.

End FinDistrLattice.

Section Total.

End Total.

Section FinDistrLattice.

End FinDistrLattice.

Section Lattice.

End Lattice.

Section DistrLattice.

End DistrLattice.

Section Total.

End Total.

Section Basics.
End Basics.

Section Lattice.

End Lattice.

Section BLattice.

End BLattice.

Section TBLattice.

End TBLattice.

Section DistrLattice.

End DistrLattice.

Section CBDistrLattice.

End CBDistrLattice.

Section CTBDistrLattice.

End CTBDistrLattice.

Section Basics.
End Basics.

End POrder.

Section Total.

End Total.

Section BDistrLattice.

End BDistrLattice.

Section TBDistrLattice.

End TBDistrLattice.

Section DualOrderTheory.

End DualOrderTheory.

Section Enum.

End Enum.

Section Ordinal.

End Ordinal.

Section total.

End total.
Import mathcomp.ssreflect.ssreflect.
Import mathcomp.ssreflect.ssrfun.
Import mathcomp.ssreflect.ssrnat.
Import mathcomp.ssreflect.seq.
Import mathcomp.ssreflect.fintype.
Import mathcomp.ssreflect.bigop.
Unset Strict Implicit.

Declare Scope ring_scope.

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

Definition eqType := @Equality.Pack cT class.

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> Choice.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion eqType : type >-> Equality.type.
Notation zmodType := type.
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
Local Notation "\sum_ ( i < n ) F" := (\big[+%R/0]_(i < n) F).

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
Definition zmodType := @Zmodule.Pack cT class.

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> Zmodule.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion zmodType : type >-> Zmodule.type.
Notation ringType := type.
End Exports.

End Ring.
Import Ring.Exports.
Definition one (R : ringType) : R.
Admitted.
Definition mul (R : ringType) : R -> R -> R.
Admitted.
Definition exp R x n := nosimpl iterop _ n (@mul R) x (one R).

Local Notation "1" := (one _) : ring_scope.
Local Notation "- 1" := (- (1)) : ring_scope.
Local Notation "*%R" := (@mul _) : fun_scope.
Local Notation "x * y" := (mul x y) : ring_scope.
Local Notation "x ^+ n" := (exp x n) : ring_scope.

Section RingTheory.

Variable R : ringType.

Lemma mulrA : @associative R *%R.
Admitted.
Lemma mul1r : @left_id R R 1 *%R.
Admitted.
Lemma mulr1 : @right_id R R 1 *%R.
Admitted.
Lemma mulr0 : @right_zero R R 0 *%R.
Admitted.

Canonical mul_monoid := Monoid.Law mulrA mul1r mulr1.

End RingTheory.

Module Export Lmodule.

Module Import Exports.
End Exports.

End Lmodule.

Module Export Additive.

Section ClassDef.

Variables U V : zmodType.

Definition axiom (f : U -> V) := {morph f : x y / x - y}.

End ClassDef.

Module Export Exports.
Notation additive f := (axiom f).
End Exports.

End Additive.

Module Export RMorphism.

Section ClassDef.

Variables R S : ringType.

Definition mixin_of (f : R -> S) :=
  {morph f : x y / x * y}%R * (f 1 = 1) : Prop.

Record class_of f : Prop := Class {base : additive f; mixin : mixin_of f}.

Structure map (phRS : phant (R -> S)) := Pack {apply; _ : class_of apply}.

End ClassDef.

Module Export Exports.
Coercion apply : map >-> Funclass.
Notation "{ 'rmorphism' fRS }" := (map (Phant fRS))
  (at level 0, format "{ 'rmorphism'  fRS }") : ring_scope.
End Exports.

End RMorphism.

Section RmorphismTheory.

Section Properties.

Variables (R S : ringType) (k : unit) (f : {rmorphism R -> S}).

Lemma rmorph0 : f 0 = 0.
admit.
Defined.

End Properties.

End RmorphismTheory.

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
Implicit Types x y : R.

Lemma mulrC : @commutative R R *%R.
Admitted.
Canonical mul_comoid := Monoid.ComLaw mulrC.

Lemma exprMn n : {morph (fun x => x ^+ n) : x y / x * y}.
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
Coercion mixin : class_of >-> mixin_of.
Coercion ringType : type >-> Ring.type.
Notation unitRingType := type.
End Exports.

End UnitRing.
Import UnitRing.Exports.

Definition unit {R : unitRingType} :=
  [qualify a u : R | UnitRing.unit (UnitRing.class R) u].
Definition inv {R : unitRingType} : R -> R.
Admitted.

Local Notation "x ^-1" := (inv x).
Local Notation "x / y" := (x * y^-1).
Local Notation "x ^- n" := ((x ^+ n)^-1).

Section UnitRingTheory.

Variable R : unitRingType.
Implicit Types x y : R.

Lemma invr0 : 0^-1 = 0 :> R.
Admitted.

Lemma exprVn x n : x^-1 ^+ n = x ^- n.
Admitted.

End UnitRingTheory.

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

Section EvalTerm.

Variable R : unitRingType.
Fixpoint holds (e : seq R) (f : formula R) {struct f} : Prop.
Admitted.

End EvalTerm.

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

Module Field.

Definition mixin_of (R : unitRingType) := forall x : R, x != 0 -> x \in unit.

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
Definition comRingType := @ComRing.Pack cT class.
Definition unitRingType := @UnitRing.Pack cT class.

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> IntegralDomain.class_of.
Canonical comRingType.
Coercion unitRingType : type >-> UnitRing.type.
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

End FieldTheory.

Module Export DecidableField.

Definition axiom (R : unitRingType) (s : seq R -> pred (formula R)) :=
  forall e f, reflect (holds e f) (s e f).

Record mixin_of (R : unitRingType) : Type :=
  Mixin { sat : seq R -> pred (formula R); satP : axiom sat}.

End DecidableField.

Module Export ClosedField.

Definition axiom (R : ringType) :=
  forall n (P : nat -> R), n > 0 ->
   exists x : R, x ^+ n = \sum_(i < n) P i * (x ^+ i).

Import mathcomp.ssreflect.ssrAC.

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
