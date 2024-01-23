
(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "-parsing" "-w" "+undeclared-scope" "-w" "+non-primitive-record" "-w" "-ambiguous-paths" "-w" "-redundant-canonical-projection" "-w" "-projection-no-head-constant" "-w" "-deprecated-native-compiler-option" "-native-compiler" "ondemand" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/analysis/classical" "mathcomp.classical" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/analysis/theories" "mathcomp.analysis" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/HB" "HB" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/elpi" "elpi" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/mathcomp" "mathcomp" "-top" "Top.bug_01") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 1520 lines to 102 lines, then from 115 lines to 7080 lines, then from 7084 lines to 5514 lines, then from 5204 lines to 214 lines, then from 227 lines to 8975 lines, then from 8977 lines to 9174 lines, then from 8558 lines to 3022 lines, then from 3030 lines to 641 lines, then from 654 lines to 3374 lines, then from 3378 lines to 3344 lines, then from 3149 lines to 2937 lines, then from 2945 lines to 2872 lines, then from 2880 lines to 2758 lines, then from 2766 lines to 2622 lines, then from 2630 lines to 2480 lines, then from 2488 lines to 2302 lines, then from 2310 lines to 2048 lines, then from 2056 lines to 1781 lines, then from 1789 lines to 1215 lines, then from 1223 lines to 1119 lines, then from 1137 lines to 891 lines, then from 904 lines to 4337 lines, then from 4342 lines to 4269 lines, then from 4063 lines to 2355 lines, then from 2363 lines to 992 lines, then from 1005 lines to 1959 lines, then from 1964 lines to 2248 lines, then from 2194 lines to 1028 lines, then from 1046 lines to 1010 lines, then from 1023 lines to 1109 lines, then from 1115 lines to 1008 lines, then from 1027 lines to 1008 lines, then from 1021 lines to 2291 lines, then from 2297 lines to 1497 lines, then from 1344 lines to 1170 lines, then from 1183 lines to 7798 lines, then from 7804 lines to 8295 lines, then from 8038 lines to 6547 lines, then from 6555 lines to 4896 lines, then from 4904 lines to 2829 lines *)
(* coqc version 8.20+alpha compiled with OCaml 4.14.1
   coqtop version 532fcf76d13e:/builds/coq/coq/_build/default,(HEAD detached at 26c84c7) (26c84c7924a0b719c579dacbad84a61567e196e9)
   Expected coqc runtime on this file: 8.543 sec *)
Require Coq.Init.Ltac.
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
Require mathcomp.ssreflect.choice.
Require mathcomp.ssreflect.path.
Require mathcomp.ssreflect.div.
Require mathcomp.ssreflect.fintype.
Require mathcomp.ssreflect.tuple.
Require mathcomp.ssreflect.finfun.
Require mathcomp.ssreflect.bigop.
Require mathcomp.ssreflect.finset.
Require mathcomp.finmap.finmap.
Require mathcomp.ssreflect.fingraph.
Require mathcomp.ssreflect.prime.
Require mathcomp.ssreflect.order.
Require mathcomp.ssreflect.binomial.
Require mathcomp.ssreflect.generic_quotient.
Require mathcomp.ssreflect.ssrAC.
Require mathcomp.ssreflect.all_ssreflect.
Require mathcomp.fingroup.fingroup.
Require mathcomp.algebra.ssralg.
Require mathcomp.algebra.ring_quotient.
Require mathcomp.algebra.countalg.
Require mathcomp.algebra.poly.
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
Module mathcomp_DOT_algebra_DOT_ssrnum_WRAPPED.
Module Export ssrnum.
Import mathcomp.ssreflect.ssreflect.
Import mathcomp.ssreflect.ssrfun.
Import mathcomp.ssreflect.ssrbool.
Import mathcomp.ssreflect.eqtype.
Import mathcomp.ssreflect.ssrnat.
Import mathcomp.ssreflect.seq.
Import mathcomp.ssreflect.choice.
Import mathcomp.ssreflect.ssrAC.
Import mathcomp.ssreflect.div.
Import mathcomp.ssreflect.fintype.
Import mathcomp.ssreflect.path.
Import mathcomp.ssreflect.bigop.
Import mathcomp.ssreflect.order.
Import mathcomp.ssreflect.finset.
Import mathcomp.fingroup.fingroup.
Import mathcomp.algebra.ssralg.
Import mathcomp.algebra.poly.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "n .-root" (at level 2, format "n .-root").
Reserved Notation "'i" (at level 0).
Reserved Notation "'Re z" (at level 10, z at level 8).
Reserved Notation "'Im z" (at level 10, z at level 8).

Local Open Scope order_scope.
Local Open Scope ring_scope.
Import Order.TTheory.
Import GRing.Theory.

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

Module NumDomain.

Section ClassDef.
Set Primitive Projections.
Record class_of T := Class {
  base : GRing.IntegralDomain.class_of T;
  order_mixin : Order.POrder.mixin_of (Equality.class (ring_for T base));
  normed_mixin : normed_mixin_of (ring_for T base) order_mixin;
  mixin : mixin_of normed_mixin;
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> GRing.IntegralDomain.class_of.
Local Coercion order_base T (class_of_T : class_of T) :=
  @Order.POrder.Class _ class_of_T (order_mixin class_of_T).

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c  as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.
Definition pack (b0 : GRing.IntegralDomain.class_of _) om0
           (nm0 : @normed_mixin_of (ring_for T b0) (ring_for T b0) om0)
           (m0 : @mixin_of (ring_for T b0) om0 nm0) :=
  fun bT (b : GRing.IntegralDomain.class_of T)
      & phant_id (@GRing.IntegralDomain.class bT) b =>
  fun om & phant_id om0 om =>
  fun nm & phant_id nm0 nm =>
  fun m & phant_id m0 m =>
  @Pack T (@Class T b om nm m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition zmodType := @GRing.Zmodule.Pack cT class.
Definition ringType := @GRing.Ring.Pack cT class.
Definition comRingType := @GRing.ComRing.Pack cT class.
Definition unitRingType := @GRing.UnitRing.Pack cT class.
Definition comUnitRingType := @GRing.ComUnitRing.Pack cT class.
Definition idomainType := @GRing.IntegralDomain.Pack cT class.
Definition porderType := @Order.POrder.Pack ring_display cT class.
Definition porder_zmodType := @GRing.Zmodule.Pack porderType class.
Definition porder_ringType := @GRing.Ring.Pack porderType class.
Definition porder_comRingType := @GRing.ComRing.Pack porderType class.
Definition porder_unitRingType := @GRing.UnitRing.Pack porderType class.
Definition porder_comUnitRingType := @GRing.ComUnitRing.Pack porderType class.
Definition porder_idomainType := @GRing.IntegralDomain.Pack porderType class.

End ClassDef.

Module Export Exports.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion base  : class_of >-> GRing.IntegralDomain.class_of.
Coercion order_base : class_of >-> Order.POrder.class_of.
Coercion normed_mixin : class_of >-> normed_mixin_of.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical comRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical unitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical comUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical idomainType.
Coercion porderType : type >-> Order.POrder.type.
Canonical porderType.
Canonical porder_zmodType.
Canonical porder_ringType.
Canonical porder_comRingType.
Canonical porder_unitRingType.
Canonical porder_comUnitRingType.
Canonical porder_idomainType.
Notation numDomainType := type.
Notation NumDomainType T m := (@pack T _ _ _ m _ _ id _ id _ id _ id).
Notation "[ 'numDomainType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'numDomainType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'numDomainType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'numDomainType'  'of'  T ]") : form_scope.
End Exports.

End NumDomain.
Import NumDomain.Exports.

Local Notation num_for T b := (@NumDomain.Pack T b).

Module NormedZmodule.

Section ClassDef.

Variable R : numDomainType.

Set Primitive Projections.
Record class_of (T : Type) := Class {
  base : GRing.Zmodule.class_of T;
  mixin : @normed_mixin_of R (@GRing.Zmodule.Pack T base) (NumDomain.class R);
}.
Unset Primitive Projections.

Local Coercion base : class_of >-> GRing.Zmodule.class_of.
Local Coercion mixin : class_of >-> normed_mixin_of.

Structure type (phR : phant R) :=
  Pack { sort; _ : class_of sort }.
Local Coercion sort : type >-> Sortclass.

Variables (phR : phant R) (T : Type) (cT : type phR).

Definition class := let: Pack _ c := cT return class_of cT in c.
Definition clone c of phant_id class c := @Pack phR T c.
Definition pack b0 (m0 : @normed_mixin_of R (@GRing.Zmodule.Pack T b0)
                                          (NumDomain.class R)) :=
  Pack phR (@Class T b0 m0).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition zmodType := @GRing.Zmodule.Pack cT class.

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> GRing.Zmodule.class_of.
Coercion mixin : class_of >-> normed_mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Notation normedZmodType R := (type (Phant R)).
Notation NormedZmodType R T m := (@pack _ (Phant R) T _ m).
Notation NormedZmodMixin := Mixin.
Notation "[ 'normedZmodType' R 'of' T 'for' cT ]" :=
  (@clone _ (Phant R) T cT _ idfun)
  (at level 0, format "[ 'normedZmodType'  R  'of'  T  'for'  cT ]") :
  form_scope.
Notation "[ 'normedZmodType' R 'of' T ]" := (@clone _ (Phant R) T _ _ id)
  (at level 0, format "[ 'normedZmodType'  R  'of'  T ]") : form_scope.
End Exports.

End NormedZmodule.
Import NormedZmodule.Exports.

Module NumDomain_joins.
Import NumDomain.
Section NumDomain_joins.

Variables (T : Type) (cT : type).

Notation class := (class cT).
Definition normedZmodType : normedZmodType cT.
exact (@NormedZmodule.Pack
     cT (Phant cT) cT (NormedZmodule.Class (NumDomain.normed_mixin class))).
Defined.
Definition normedZmod_ringType := @GRing.Ring.Pack normedZmodType class.
Definition normedZmod_comRingType := @GRing.ComRing.Pack normedZmodType class.
Definition normedZmod_unitRingType := @GRing.UnitRing.Pack normedZmodType class.
Definition normedZmod_comUnitRingType :=
  @GRing.ComUnitRing.Pack normedZmodType class.
Definition normedZmod_idomainType :=
  @GRing.IntegralDomain.Pack normedZmodType class.
Definition normedZmod_porderType :=
  @Order.POrder.Pack ring_display normedZmodType class.

End NumDomain_joins.

Module Export Exports.
Coercion normedZmodType : type >-> NormedZmodule.type.
Canonical normedZmodType.
Canonical normedZmod_ringType.
Canonical normedZmod_comRingType.
Canonical normedZmod_unitRingType.
Canonical normedZmod_comUnitRingType.
Canonical normedZmod_idomainType.
Canonical normedZmod_porderType.
End Exports.
End NumDomain_joins.
Export NumDomain_joins.Exports.

Module Import Def.
Definition normr (R : numDomainType) (T : normedZmodType R) : T -> R.
Admitted.
Arguments normr {R T} x.

Notation ler := (@Order.le ring_display _) (only parsing).
Notation "@ 'ler' R" := (@Order.le ring_display R)
  (at level 10, R at level 8, only parsing) : function_scope.
Notation ltr := (@Order.lt ring_display _) (only parsing).
Notation "@ 'ltr' R" := (@Order.lt ring_display R)
  (at level 10, R at level 8, only parsing) : function_scope.
Notation ger := (@Order.ge ring_display _) (only parsing).
Notation "@ 'ger' R" := (@Order.ge ring_display R)
  (at level 10, R at level 8, only parsing) : function_scope.
Notation gtr := (@Order.gt ring_display _) (only parsing).
Notation "@ 'gtr' R" := (@Order.gt ring_display R)
  (at level 10, R at level 8, only parsing) : function_scope.
Notation lerif := (@Order.leif ring_display _) (only parsing).
Notation "@ 'lerif' R" := (@Order.leif ring_display R)
  (at level 10, R at level 8, only parsing) : function_scope.
Notation lterif := (@Order.lteif ring_display _) (only parsing).
Notation "@ 'lteif' R" := (@Order.lteif ring_display R)
  (at level 10, R at level 8, only parsing) : function_scope.
Notation comparabler := (@Order.comparable ring_display _) (only parsing).
Notation "@ 'comparabler' R" := (@Order.comparable ring_display R)
  (at level 10, R at level 8, only parsing) : function_scope.
Notation maxr := (@Order.max ring_display _).
Notation "@ 'maxr' R" := (@Order.max ring_display R)
    (at level 10, R at level 8, only parsing) : function_scope.
Notation minr := (@Order.min ring_display _).
Notation "@ 'minr' R" := (@Order.min ring_display R)
  (at level 10, R at level 8, only parsing) : function_scope.

Section Def.
Context {R : numDomainType}.
Implicit Types (x : R).
Definition sgr x : R.
Admitted.
Definition Rpos : qualifier 0 R.
Admitted.
Definition Rneg : qualifier 0 R.
Admitted.
Definition Rnneg : qualifier 0 R.
Admitted.
Definition Rnpos : qualifier 0 R.
Admitted.
Definition Rreal : qualifier 0 R.
Admitted.

End Def.
End Def.

Notation norm := normr (only parsing).
Notation le := ler (only parsing).
Notation lt := ltr (only parsing).
Notation ge := ger (only parsing).
Notation gt := gtr (only parsing).
Notation leif := lerif (only parsing).
Notation lteif := lterif (only parsing).
Notation comparable := comparabler (only parsing).
Notation sg := sgr.
Notation max := maxr.
Notation min := minr.
Notation pos := Rpos.
Notation neg := Rneg.
Notation nneg := Rnneg.
Notation npos := Rnpos.
Notation real := Rreal.

Module Export Keys.
Section Keys.
Variable R : numDomainType.
Fact Rpos_key : pred_key (@pos R).
Admitted.
Definition Rpos_keyed := KeyedQualifier Rpos_key.
Fact Rneg_key : pred_key (@real R).
Admitted.
Definition Rneg_keyed := KeyedQualifier Rneg_key.
Fact Rnneg_key : pred_key (@nneg R).
Admitted.
Definition Rnneg_keyed := KeyedQualifier Rnneg_key.
Fact Rreal_key : pred_key (@real R).
Admitted.
Definition Rreal_keyed := KeyedQualifier Rreal_key.
End Keys.
End Keys.

Module Import Syntax.
Import Def.
Import Keys.

Notation "`| x |" := (norm x) : ring_scope.

Notation "<=%R" := le : function_scope.
Notation ">=%R" := ge : function_scope.
Notation "<%R" := lt : function_scope.
Notation ">%R" := gt : function_scope.
Notation "<?=%R" := leif : function_scope.
Notation "<?<=%R" := lteif : function_scope.
Notation ">=<%R" := comparable : function_scope.
Notation "><%R" := (fun x y => ~~ (comparable x y)) : function_scope.

Notation "<= y" := (ge y) : ring_scope.
Notation "<= y :> T" := (<= (y : T)) (only parsing) : ring_scope.
Notation ">= y"  := (le y) : ring_scope.
Notation ">= y :> T" := (>= (y : T)) (only parsing) : ring_scope.

Notation "< y" := (gt y) : ring_scope.
Notation "< y :> T" := (< (y : T)) (only parsing) : ring_scope.
Notation "> y" := (lt y) : ring_scope.
Notation "> y :> T" := (> (y : T)) (only parsing) : ring_scope.

Notation "x <= y" := (le x y) : ring_scope.
Notation "x <= y :> T" := ((x : T) <= (y : T)) (only parsing) : ring_scope.
Notation "x >= y" := (y <= x) (only parsing) : ring_scope.
Notation "x >= y :> T" := ((x : T) >= (y : T)) (only parsing) : ring_scope.

Notation "x < y"  := (lt x y) : ring_scope.
Notation "x < y :> T" := ((x : T) < (y : T)) (only parsing) : ring_scope.
Notation "x > y"  := (y < x) (only parsing) : ring_scope.
Notation "x > y :> T" := ((x : T) > (y : T)) (only parsing) : ring_scope.

Notation "x <= y <= z" := ((x <= y) && (y <= z)) : ring_scope.
Notation "x < y <= z" := ((x < y) && (y <= z)) : ring_scope.
Notation "x <= y < z" := ((x <= y) && (y < z)) : ring_scope.
Notation "x < y < z" := ((x < y) && (y < z)) : ring_scope.

Notation "x <= y ?= 'iff' C" := (lerif x y C) : ring_scope.
Notation "x <= y ?= 'iff' C :> R" := ((x : R) <= (y : R) ?= iff C)
  (only parsing) : ring_scope.

Notation "x < y ?<= 'if' C" := (lterif x y C) : ring_scope.
Notation "x < y ?<= 'if' C :> R" := ((x : R) < (y : R) ?<= if C)
  (only parsing) : ring_scope.

Notation ">=< y" := [pred x | comparable x y] : ring_scope.
Notation ">=< y :> T" := (>=< (y : T)) (only parsing) : ring_scope.
Notation "x >=< y" := (comparable x y) : ring_scope.

Notation ">< y" := [pred x | ~~ comparable x y] : ring_scope.
Notation ">< y :> T" := (>< (y : T)) (only parsing) : ring_scope.
Notation "x >< y" := (~~ (comparable x y)) : ring_scope.

Canonical Rpos_keyed.
Canonical Rneg_keyed.
Canonical Rnneg_keyed.
Canonical Rreal_keyed.

Export Order.POCoercions.

End Syntax.

Section ExtensionAxioms.

Variable R : numDomainType.
Definition real_axiom : Prop.
Admitted.
Definition archimedean_axiom : Prop.
exact (forall x : R, exists ub, `|x| < ub%:R).
Defined.
Definition real_closed_axiom : Prop.
Admitted.

End ExtensionAxioms.

Module NumField.

Section ClassDef.

Set Primitive Projections.
Record class_of R := Class {
  base  : NumDomain.class_of R;
  mixin : GRing.Field.mixin_of (num_for R base);
}.
Unset Primitive Projections.
Local Coercion base : class_of >-> NumDomain.class_of.
Local Coercion base2 R (c : class_of R) : GRing.Field.class_of _ :=
  GRing.Field.Class (@mixin _ c).

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition pack :=
  fun bT b & phant_id (NumDomain.class bT) (b : NumDomain.class_of T) =>
  fun mT m & phant_id (GRing.Field.mixin (GRing.Field.class mT)) m =>
  Pack (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition zmodType := @GRing.Zmodule.Pack cT class.
Definition ringType := @GRing.Ring.Pack cT class.
Definition comRingType := @GRing.ComRing.Pack cT class.
Definition unitRingType := @GRing.UnitRing.Pack cT class.
Definition comUnitRingType := @GRing.ComUnitRing.Pack cT class.
Definition idomainType := @GRing.IntegralDomain.Pack cT class.
Definition porderType := @Order.POrder.Pack ring_display cT class.
Definition numDomainType := @NumDomain.Pack cT class.
Definition fieldType := @GRing.Field.Pack cT class.
Definition normedZmodType := NormedZmodType numDomainType cT class.
Definition porder_fieldType := @GRing.Field.Pack porderType class.
Definition normedZmod_fieldType := @GRing.Field.Pack normedZmodType class.
Definition numDomain_fieldType := @GRing.Field.Pack numDomainType class.

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> NumDomain.class_of.
Coercion base2 : class_of >-> GRing.Field.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical comRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical unitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical comUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical idomainType.
Coercion porderType : type >-> Order.POrder.type.
Canonical porderType.
Coercion numDomainType : type >-> NumDomain.type.
Canonical numDomainType.
Coercion fieldType : type >-> GRing.Field.type.
Canonical fieldType.
Coercion normedZmodType : type >-> NormedZmodule.type.
Canonical normedZmodType.
Canonical porder_fieldType.
Canonical normedZmod_fieldType.
Canonical numDomain_fieldType.
Notation numFieldType := type.
Notation "[ 'numFieldType' 'of' T ]" := (@pack T _ _ id _ _ id)
  (at level 0, format "[ 'numFieldType'  'of'  T ]") : form_scope.
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

Set Primitive Projections.
Record class_of R := Class {
  base : NumField.class_of R;
  decField_mixin : GRing.DecidableField.mixin_of (num_for R base);
  closedField_axiom : GRing.ClosedField.axiom (num_for R base);
  conj_mixin  : imaginary_mixin_of (num_for R base);
}.
Unset Primitive Projections.
Local Coercion base : class_of >-> NumField.class_of.
Local Coercion base2 R (c : class_of R) : GRing.ClosedField.class_of R.
Admitted.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone := fun b & phant_id class (b : class_of T) => Pack b.
Definition pack :=
  fun bT b & phant_id (NumField.class bT) (b : NumField.class_of T) =>
  fun mT dec closed
      & phant_id (GRing.ClosedField.class mT)
                 (@GRing.ClosedField.Class
                    _ (@GRing.DecidableField.Class _ b dec) closed) =>
  fun mc => Pack (@Class T b dec closed mc).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition zmodType := @GRing.Zmodule.Pack cT class.
Definition ringType := @GRing.Ring.Pack cT class.
Definition comRingType := @GRing.ComRing.Pack cT class.
Definition unitRingType := @GRing.UnitRing.Pack cT class.
Definition comUnitRingType := @GRing.ComUnitRing.Pack cT class.
Definition idomainType := @GRing.IntegralDomain.Pack cT class.
Definition porderType := @Order.POrder.Pack ring_display cT class.
Definition numDomainType := @NumDomain.Pack cT class.
Definition fieldType := @GRing.Field.Pack cT class.
Definition numFieldType := @NumField.Pack cT class.
Definition decFieldType := @GRing.DecidableField.Pack cT class.
Definition closedFieldType := @GRing.ClosedField.Pack cT class.
Definition normedZmodType := NormedZmodType numDomainType cT class.
Definition porder_decFieldType := @GRing.DecidableField.Pack porderType class.
Definition normedZmod_decFieldType :=
  @GRing.DecidableField.Pack normedZmodType class.
Definition numDomain_decFieldType :=
  @GRing.DecidableField.Pack numDomainType class.
Definition numField_decFieldType :=
  @GRing.DecidableField.Pack numFieldType class.
Definition porder_closedFieldType := @GRing.ClosedField.Pack porderType class.
Definition normedZmod_closedFieldType :=
  @GRing.ClosedField.Pack normedZmodType class.
Definition numDomain_closedFieldType :=
  @GRing.ClosedField.Pack numDomainType class.
Definition numField_closedFieldType :=
  @GRing.ClosedField.Pack numFieldType class.

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> NumField.class_of.
Coercion base2 : class_of >-> GRing.ClosedField.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical comRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical unitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical comUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical idomainType.
Coercion porderType : type >-> Order.POrder.type.
Canonical porderType.
Coercion numDomainType : type >-> NumDomain.type.
Canonical numDomainType.
Coercion fieldType : type >-> GRing.Field.type.
Canonical fieldType.
Coercion decFieldType : type >-> GRing.DecidableField.type.
Canonical decFieldType.
Coercion numFieldType : type >-> NumField.type.
Canonical numFieldType.
Coercion closedFieldType : type >-> GRing.ClosedField.type.
Canonical closedFieldType.
Coercion normedZmodType : type >-> NormedZmodule.type.
Canonical normedZmodType.
Canonical porder_decFieldType.
Canonical normedZmod_decFieldType.
Canonical numDomain_decFieldType.
Canonical numField_decFieldType.
Canonical porder_closedFieldType.
Canonical normedZmod_closedFieldType.
Canonical numDomain_closedFieldType.
Canonical numField_closedFieldType.
Notation numClosedFieldType := type.
Notation NumClosedFieldType T m := (@pack T _ _ id _ _ _ id m).
Notation "[ 'numClosedFieldType' 'of' T 'for' cT ]" := (@clone T cT _ id)
  (at level 0, format "[ 'numClosedFieldType'  'of'  T  'for' cT ]") :
                                                         form_scope.
Notation "[ 'numClosedFieldType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'numClosedFieldType'  'of'  T ]") : form_scope.
End Exports.

End ClosedField.
Import ClosedField.Exports.

Module RealDomain.

Section ClassDef.

Set Primitive Projections.
Record class_of R := Class {
  base   : NumDomain.class_of R;
  nmixin : Order.Lattice.mixin_of base;
  lmixin : Order.DistrLattice.mixin_of (Order.Lattice.Class nmixin);
  tmixin : Order.Total.mixin_of base;
}.
Unset Primitive Projections.
Local Coercion base : class_of >-> NumDomain.class_of.
Local Coercion base2 T (c : class_of T) : Order.Total.class_of T.
Admitted.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition pack :=
  fun bT b & phant_id (NumDomain.class bT) (b : NumDomain.class_of T) =>
  fun mT n l m &
      phant_id (@Order.Total.class ring_display mT)
               (@Order.Total.Class T (@Order.DistrLattice.Class
                                        T (@Order.Lattice.Class T b n) l) m) =>
  Pack (@Class T b n l m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition zmodType := @GRing.Zmodule.Pack cT class.
Definition ringType := @GRing.Ring.Pack cT class.
Definition comRingType := @GRing.ComRing.Pack cT class.
Definition unitRingType := @GRing.UnitRing.Pack cT class.
Definition comUnitRingType := @GRing.ComUnitRing.Pack cT class.
Definition idomainType := @GRing.IntegralDomain.Pack cT class.
Definition porderType := @Order.POrder.Pack ring_display cT class.
Definition latticeType := @Order.Lattice.Pack ring_display cT class.
Definition distrLatticeType := @Order.DistrLattice.Pack ring_display cT class.
Definition orderType := @Order.Total.Pack ring_display cT class.
Definition numDomainType := @NumDomain.Pack cT class.
Definition normedZmodType := NormedZmodType numDomainType cT class.
Definition zmod_latticeType := @Order.Lattice.Pack ring_display zmodType class.
Definition ring_latticeType := @Order.Lattice.Pack ring_display ringType class.
Definition comRing_latticeType :=
  @Order.Lattice.Pack ring_display comRingType class.
Definition unitRing_latticeType :=
  @Order.Lattice.Pack ring_display unitRingType class.
Definition comUnitRing_latticeType :=
  @Order.Lattice.Pack ring_display comUnitRingType class.
Definition idomain_latticeType :=
  @Order.Lattice.Pack ring_display idomainType class.
Definition normedZmod_latticeType :=
  @Order.Lattice.Pack ring_display normedZmodType class.
Definition numDomain_latticeType :=
  @Order.Lattice.Pack ring_display numDomainType class.
Definition zmod_distrLatticeType :=
  @Order.DistrLattice.Pack ring_display zmodType class.
Definition ring_distrLatticeType :=
  @Order.DistrLattice.Pack ring_display ringType class.
Definition comRing_distrLatticeType :=
  @Order.DistrLattice.Pack ring_display comRingType class.
Definition unitRing_distrLatticeType :=
  @Order.DistrLattice.Pack ring_display unitRingType class.
Definition comUnitRing_distrLatticeType :=
  @Order.DistrLattice.Pack ring_display comUnitRingType class.
Definition idomain_distrLatticeType :=
  @Order.DistrLattice.Pack ring_display idomainType class.
Definition normedZmod_distrLatticeType :=
  @Order.DistrLattice.Pack ring_display normedZmodType class.
Definition numDomain_distrLatticeType :=
  @Order.DistrLattice.Pack ring_display numDomainType class.
Definition zmod_orderType := @Order.Total.Pack ring_display zmodType class.
Definition ring_orderType := @Order.Total.Pack ring_display ringType class.
Definition comRing_orderType :=
  @Order.Total.Pack ring_display comRingType class.
Definition unitRing_orderType :=
  @Order.Total.Pack ring_display unitRingType class.
Definition comUnitRing_orderType :=
  @Order.Total.Pack ring_display comUnitRingType class.
Definition idomain_orderType :=
  @Order.Total.Pack ring_display idomainType class.
Definition normedZmod_orderType :=
  @Order.Total.Pack ring_display normedZmodType class.
Definition numDomain_orderType :=
  @Order.Total.Pack ring_display numDomainType class.

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> NumDomain.class_of.
Coercion base2 : class_of >-> Order.Total.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical comRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical unitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical comUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical idomainType.
Coercion porderType : type >-> Order.POrder.type.
Canonical porderType.
Coercion numDomainType : type >-> NumDomain.type.
Canonical numDomainType.
Coercion latticeType : type >-> Order.Lattice.type.
Canonical latticeType.
Coercion distrLatticeType : type >-> Order.DistrLattice.type.
Canonical distrLatticeType.
Coercion orderType : type >-> Order.Total.type.
Canonical orderType.
Coercion normedZmodType : type >-> NormedZmodule.type.
Canonical normedZmodType.
Canonical zmod_latticeType.
Canonical ring_latticeType.
Canonical comRing_latticeType.
Canonical unitRing_latticeType.
Canonical comUnitRing_latticeType.
Canonical idomain_latticeType.
Canonical normedZmod_latticeType.
Canonical numDomain_latticeType.
Canonical zmod_distrLatticeType.
Canonical ring_distrLatticeType.
Canonical comRing_distrLatticeType.
Canonical unitRing_distrLatticeType.
Canonical comUnitRing_distrLatticeType.
Canonical idomain_distrLatticeType.
Canonical normedZmod_distrLatticeType.
Canonical numDomain_distrLatticeType.
Canonical zmod_orderType.
Canonical ring_orderType.
Canonical comRing_orderType.
Canonical unitRing_orderType.
Canonical comUnitRing_orderType.
Canonical idomain_orderType.
Canonical normedZmod_orderType.
Canonical numDomain_orderType.
Notation realDomainType := type.
Notation "[ 'realDomainType' 'of' T ]" := (@pack T _ _ id _ _ _ _ id)
  (at level 0, format "[ 'realDomainType'  'of'  T ]") : form_scope.
End Exports.

End RealDomain.
Import RealDomain.Exports.

Module RealField.

Section ClassDef.

Set Primitive Projections.
Record class_of R := Class {
  base  : NumField.class_of R;
  nmixin : Order.Lattice.mixin_of base;
  lmixin : Order.DistrLattice.mixin_of (Order.Lattice.Class nmixin);
  tmixin : Order.Total.mixin_of base;
}.
Unset Primitive Projections.
Local Coercion base : class_of >-> NumField.class_of.
Local Coercion base2 R (c : class_of R) : RealDomain.class_of R.
Admitted.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition pack :=
  fun bT (b : NumField.class_of T) & phant_id (NumField.class bT) b =>
  fun mT n l t
      & phant_id (RealDomain.class mT) (@RealDomain.Class T b n l t) =>
  Pack (@Class T b n l t).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition zmodType := @GRing.Zmodule.Pack cT class.
Definition ringType := @GRing.Ring.Pack cT class.
Definition comRingType := @GRing.ComRing.Pack cT class.
Definition unitRingType := @GRing.UnitRing.Pack cT class.
Definition comUnitRingType := @GRing.ComUnitRing.Pack cT class.
Definition idomainType := @GRing.IntegralDomain.Pack cT class.
Definition porderType := @Order.POrder.Pack ring_display cT class.
Definition numDomainType := @NumDomain.Pack cT class.
Definition latticeType := @Order.Lattice.Pack ring_display cT class.
Definition distrLatticeType := @Order.DistrLattice.Pack ring_display cT class.
Definition orderType := @Order.Total.Pack ring_display cT class.
Definition realDomainType := @RealDomain.Pack cT class.
Definition fieldType := @GRing.Field.Pack cT class.
Definition numFieldType := @NumField.Pack cT class.
Definition normedZmodType := NormedZmodType numDomainType cT class.
Definition field_latticeType :=
  @Order.Lattice.Pack ring_display fieldType class.
Definition field_distrLatticeType :=
  @Order.DistrLattice.Pack ring_display fieldType class.
Definition field_orderType := @Order.Total.Pack ring_display fieldType class.
Definition field_realDomainType := @RealDomain.Pack fieldType class.
Definition numField_latticeType :=
  @Order.Lattice.Pack ring_display numFieldType class.
Definition numField_distrLatticeType :=
  @Order.DistrLattice.Pack ring_display numFieldType class.
Definition numField_orderType :=
  @Order.Total.Pack ring_display numFieldType class.
Definition numField_realDomainType := @RealDomain.Pack numFieldType class.

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> NumField.class_of.
Coercion base2 : class_of >-> RealDomain.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical comRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical unitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical comUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical idomainType.
Coercion porderType : type >-> Order.POrder.type.
Canonical porderType.
Coercion numDomainType : type >-> NumDomain.type.
Canonical numDomainType.
Coercion latticeType : type >-> Order.Lattice.type.
Canonical latticeType.
Coercion distrLatticeType : type >-> Order.DistrLattice.type.
Canonical distrLatticeType.
Coercion orderType : type >-> Order.Total.type.
Canonical orderType.
Coercion realDomainType : type >-> RealDomain.type.
Canonical realDomainType.
Coercion fieldType : type >-> GRing.Field.type.
Canonical fieldType.
Coercion numFieldType : type >-> NumField.type.
Canonical numFieldType.
Coercion normedZmodType : type >-> NormedZmodule.type.
Canonical normedZmodType.
Canonical field_latticeType.
Canonical field_distrLatticeType.
Canonical field_orderType.
Canonical field_realDomainType.
Canonical numField_latticeType.
Canonical numField_distrLatticeType.
Canonical numField_orderType.
Canonical numField_realDomainType.
Notation realFieldType := type.
Notation "[ 'realFieldType' 'of' T ]" := (@pack T _ _ id _ _ _ _ id)
  (at level 0, format "[ 'realFieldType'  'of'  T ]") : form_scope.
End Exports.

End RealField.
Import RealField.Exports.

Module ArchimedeanField.

Section ClassDef.

Set Primitive Projections.
Record class_of R := Class {
  base : RealField.class_of R;
  mixin : archimedean_axiom (num_for R base)
}.
Unset Primitive Projections.
Local Coercion base : class_of >-> RealField.class_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.
Definition pack b0 (m0 : archimedean_axiom (num_for T b0)) :=
  fun bT b & phant_id (RealField.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition zmodType := @GRing.Zmodule.Pack cT class.
Definition ringType := @GRing.Ring.Pack cT class.
Definition comRingType := @GRing.ComRing.Pack cT class.
Definition unitRingType := @GRing.UnitRing.Pack cT class.
Definition comUnitRingType := @GRing.ComUnitRing.Pack cT class.
Definition idomainType := @GRing.IntegralDomain.Pack cT class.
Definition porderType := @Order.POrder.Pack ring_display cT class.
Definition latticeType := @Order.Lattice.Pack ring_display cT class.
Definition distrLatticeType := @Order.DistrLattice.Pack ring_display cT class.
Definition orderType := @Order.Total.Pack ring_display cT class.
Definition numDomainType := @NumDomain.Pack cT class.
Definition realDomainType := @RealDomain.Pack cT class.
Definition fieldType := @GRing.Field.Pack cT class.
Definition numFieldType := @NumField.Pack cT class.
Definition realFieldType := @RealField.Pack cT class.
Definition normedZmodType := NormedZmodType numDomainType cT class.

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> RealField.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical comRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical unitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical comUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical idomainType.
Coercion porderType : type >-> Order.POrder.type.
Canonical porderType.
Coercion latticeType : type >-> Order.Lattice.type.
Canonical latticeType.
Coercion distrLatticeType : type >-> Order.DistrLattice.type.
Canonical distrLatticeType.
Coercion orderType : type >-> Order.Total.type.
Canonical orderType.
Coercion numDomainType : type >-> NumDomain.type.
Canonical numDomainType.
Coercion realDomainType : type >-> RealDomain.type.
Canonical realDomainType.
Coercion fieldType : type >-> GRing.Field.type.
Canonical fieldType.
Coercion numFieldType : type >-> NumField.type.
Canonical numFieldType.
Coercion realFieldType : type >-> RealField.type.
Canonical realFieldType.
Coercion normedZmodType : type >-> NormedZmodule.type.
Canonical normedZmodType.
Notation archiFieldType := type.
Notation ArchiFieldType T m := (@pack T _ m _ _ id _ id).
Notation "[ 'archiFieldType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'archiFieldType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'archiFieldType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'archiFieldType'  'of'  T ]") : form_scope.
End Exports.

End ArchimedeanField.
Import ArchimedeanField.Exports.

Module RealClosedField.

Section ClassDef.

Set Primitive Projections.
Record class_of R := Class {
  base : RealField.class_of R;
  mixin : real_closed_axiom (num_for R base)
}.
Unset Primitive Projections.
Local Coercion base : class_of >-> RealField.class_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.
Definition pack b0 (m0 : real_closed_axiom (num_for T b0)) :=
  fun bT b & phant_id (RealField.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition zmodType := @GRing.Zmodule.Pack cT class.
Definition ringType := @GRing.Ring.Pack cT class.
Definition comRingType := @GRing.ComRing.Pack cT class.
Definition unitRingType := @GRing.UnitRing.Pack cT class.
Definition comUnitRingType := @GRing.ComUnitRing.Pack cT class.
Definition idomainType := @GRing.IntegralDomain.Pack cT class.
Definition porderType := @Order.POrder.Pack ring_display cT class.
Definition latticeType := @Order.Lattice.Pack ring_display cT class.
Definition distrLatticeType := @Order.DistrLattice.Pack ring_display cT class.
Definition orderType := @Order.Total.Pack ring_display cT class.
Definition numDomainType := @NumDomain.Pack cT class.
Definition realDomainType := @RealDomain.Pack cT class.
Definition fieldType := @GRing.Field.Pack cT class.
Definition numFieldType := @NumField.Pack cT class.
Definition realFieldType := @RealField.Pack cT class.
Definition normedZmodType := NormedZmodType numDomainType cT class.

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> RealField.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical comRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical unitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical comUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical idomainType.
Coercion porderType : type >-> Order.POrder.type.
Canonical porderType.
Coercion latticeType : type >-> Order.Lattice.type.
Canonical latticeType.
Coercion distrLatticeType : type >-> Order.DistrLattice.type.
Canonical distrLatticeType.
Coercion orderType : type >-> Order.Total.type.
Canonical orderType.
Coercion numDomainType : type >-> NumDomain.type.
Canonical numDomainType.
Coercion realDomainType : type >-> RealDomain.type.
Canonical realDomainType.
Coercion fieldType : type >-> GRing.Field.type.
Canonical fieldType.
Coercion numFieldType : type >-> NumField.type.
Canonical numFieldType.
Coercion realFieldType : type >-> RealField.type.
Canonical realFieldType.
Coercion normedZmodType : type >-> NormedZmodule.type.
Canonical normedZmodType.
Notation rcfType := Num.RealClosedField.type.
Notation RcfType T m := (@pack T _ m _ _ id _ id).
Notation "[ 'rcfType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'rcfType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'rcfType' 'of' T ]" :=  (@clone T _ _ id)
  (at level 0, format "[ 'rcfType'  'of'  T ]") : form_scope.
End Exports.

End RealClosedField.
Import RealClosedField.Exports.

Module Import Internals.

Section NormedZmodule.
Variables (R : numDomainType) (V : normedZmodType R).
Implicit Types (l : R) (x y : V).

Lemma ler_normD x y : `|x + y| <= `|x| + `|y|.
Admitted.

Lemma normr0_eq0 x : `|x| = 0 -> x = 0.
Admitted.

Lemma normrMn x n : `|x *+ n| = `|x| *+ n.
Admitted.

Lemma normrN x : `|- x| = `|x|.
Admitted.

End NormedZmodule.

Section NumDomain.
Variable R : numDomainType.
Implicit Types x y : R.

Lemma addr_gt0 x y : 0 < x -> 0 < y -> 0 < x + y.
Admitted.

Lemma ger_leVge x y : 0 <= x -> 0 <= y -> (x <= y) || (y <= x).
Admitted.

Lemma normrM : {morph norm : x y / (x : R) * y}.
Admitted.

Lemma ler_def x y : (x <= y) = (`|y - x| == y - x).
Admitted.

Lemma ger0_def x : (0 <= x) = (`|x| == x).
Admitted.

Lemma subr_ge0 x y : (0 <= x - y) = (y <= x).
Admitted.

Lemma oppr_ge0 x : (0 <= - x) = (x <= 0).
Admitted.

Lemma ler01 : 0 <= 1 :> R.
Admitted.

Lemma ltr01 : 0 < 1 :> R.
Admitted.

Lemma le0r x : (0 <= x) = (x == 0) || (0 < x).
Admitted.

Lemma addr_ge0 x y : 0 <= x -> 0 <= y -> 0 <= x + y.
Admitted.

Lemma pmulr_rgt0 x y : 0 < x -> (0 < x * y) = (0 < y).
Admitted.

Lemma posrE x : (x \is pos) = (0 < x).
Admitted.
Lemma nnegrE x : (x \is nneg) = (0 <= x).
Admitted.
Lemma realE x : (x \is real) = (0 <= x) || (x <= 0).
Admitted.

Fact pos_divr_closed : divr_closed (@pos R).
Admitted.
Canonical pos_mulrPred := MulrPred pos_divr_closed.
Canonical pos_divrPred := DivrPred pos_divr_closed.

Fact nneg_divr_closed : divr_closed (@nneg R).
Admitted.
Canonical nneg_mulrPred := MulrPred nneg_divr_closed.
Canonical nneg_divrPred := DivrPred nneg_divr_closed.

Fact nneg_addr_closed : addr_closed (@nneg R).
Admitted.
Canonical nneg_addrPred := AddrPred nneg_addr_closed.
Canonical nneg_semiringPred := SemiringPred nneg_divr_closed.

Fact real_oppr_closed : oppr_closed (@real R).
Admitted.
Canonical real_opprPred := OpprPred real_oppr_closed.

Fact real_addr_closed : addr_closed (@real R).
Admitted.
Canonical real_addrPred := AddrPred real_addr_closed.
Canonical real_zmodPred := ZmodPred real_oppr_closed.

Fact real_divr_closed : divr_closed (@real R).
Admitted.
Canonical real_mulrPred := MulrPred real_divr_closed.
Canonical real_smulrPred := SmulrPred real_divr_closed.
Canonical real_divrPred := DivrPred real_divr_closed.
Canonical real_sdivrPred := SdivrPred real_divr_closed.
Canonical real_semiringPred := SemiringPred real_divr_closed.
Canonical real_subringPred := SubringPred real_divr_closed.
Canonical real_divringPred := DivringPred real_divr_closed.

End NumDomain.

Lemma num_real (R : realDomainType) (x : R) : x \is real.
Admitted.

Fact archi_bound_subproof (R : archiFieldType) : archimedean_axiom R.
Admitted.

Section RealClosed.
Variable R : rcfType.

Lemma poly_ivt : real_closed_axiom R.
Admitted.

Fact sqrtr_subproof (x : R) :
  exists2 y, 0 <= y & (if 0 <= x then y ^+ 2 == x else y == 0) : bool.
Admitted.

End RealClosed.

End Internals.

Module Export PredInstances.

Canonical pos_mulrPred.
Canonical pos_divrPred.

Canonical nneg_addrPred.
Canonical nneg_mulrPred.
Canonical nneg_divrPred.
Canonical nneg_semiringPred.

Canonical real_addrPred.
Canonical real_opprPred.
Canonical real_zmodPred.
Canonical real_mulrPred.
Canonical real_smulrPred.
Canonical real_divrPred.
Canonical real_sdivrPred.
Canonical real_semiringPred.
Canonical real_subringPred.
Canonical real_divringPred.

End PredInstances.

Module Import ExtraDef.

Definition archi_bound {R} x := sval (sigW (@archi_bound_subproof R x)).

Definition sqrtr {R} x := s2val (sig2W (@sqrtr_subproof R x)).

End ExtraDef.

Notation bound := archi_bound.
Notation sqrt := sqrtr.

Module Import Theory.

Section NumIntegralDomainTheory.

Variable R : numDomainType.
Implicit Types (V : normedZmodType R) (x y z t : R).
Definition ler_normD V (x y : V) : `|x + y| <= `|x| + `|y|.
Admitted.
Definition addr_gt0 x y : 0 < x -> 0 < y -> 0 < x + y.
Admitted.
Definition normr0_eq0 V (x : V) : `|x| = 0 -> x = 0.
Admitted.
Definition ger_leVge x y : 0 <= x -> 0 <= y -> (x <= y) || (y <= x).
Admitted.
Definition normrM : {morph norm : x y / (x : R) * y}.
Admitted.
Definition ler_def x y : (x <= y) = (`|y - x| == y - x).
Admitted.
Definition normrMn V (x : V) n : `|x *+ n| = `|x| *+ n.
Admitted.
Definition normrN V (x : V) : `|- x| = `|x|.
Admitted.

Lemma posrE x : (x \is pos) = (0 < x).
Admitted.
Lemma negrE x : (x \is neg) = (x < 0).
Admitted.
Lemma nnegrE x : (x \is nneg) = (0 <= x).
Admitted.
Lemma nposrE x : (x \is npos) = (x <= 0).
Admitted.
Lemma realE x : (x \is real) = (0 <= x) || (x <= 0).
Admitted.

Lemma lt0r x : (0 < x) = (x != 0) && (0 <= x).
Admitted.
Lemma le0r x : (0 <= x) = (x == 0) || (0 < x).
Admitted.

Lemma lt0r_neq0 (x : R) : 0 < x -> x != 0.
Admitted.

Lemma ltr0_neq0 (x : R) : x < 0 -> x != 0.
Admitted.

Lemma pmulr_rgt0 x y : 0 < x -> (0 < x * y) = (0 < y).
Admitted.

Lemma pmulr_rge0 x y : 0 < x -> (0 <= x * y) = (0 <= y).
Admitted.

Lemma ler01 : 0 <= 1 :> R.
Admitted.
Lemma ltr01 : 0 < 1 :> R.
Admitted.
Lemma ler0n n : 0 <= n%:R :> R.
Admitted.
Hint Resolve ler01 ltr01 ler0n : core.
Lemma ltr0Sn n : 0 < n.+1%:R :> R.
Admitted.
Lemma ltr0n n : (0 < n%:R :> R) = (0 < n)%N.
Admitted.
Hint Resolve ltr0Sn : core.

Lemma pnatr_eq0 n : (n%:R == 0 :> R) = (n == 0)%N.
Admitted.

Lemma char_num : [char R] =i pred0.
Admitted.

Lemma ger0_def x : (0 <= x) = (`|x| == x).
Admitted.
Lemma normr_idP {x} : reflect (`|x| = x) (0 <= x).
Admitted.
Lemma ger0_norm x : 0 <= x -> `|x| = x.
Admitted.
Lemma normr1 : `|1 : R| = 1.
Admitted.
Lemma normr_nat n : `|n%:R : R| = n%:R.
Admitted.

Lemma normr_prod I r (P : pred I) (F : I -> R) :
  `|\prod_(i <- r | P i) F i| = \prod_(i <- r | P i) `|F i|.
Admitted.

Lemma normrX n x : `|x ^+ n| = `|x| ^+ n.
Admitted.

Lemma normr_unit : {homo (@norm R R) : x / x \is a GRing.unit}.
Admitted.

Lemma normrV : {in GRing.unit, {morph (@norm R R) : x / x ^-1}}.
Admitted.

Lemma normrN1 : `|-1 : R| = 1.
Admitted.

Lemma big_real x0 op I (P : pred I) F (s : seq I) :
  {in real &, forall x y, op x y \is real} -> x0 \is real ->
  {in P, forall i, F i \is real} -> \big[op/x0]_(i <- s | P i) F i \is real.
Admitted.

Lemma sum_real I (P : pred I) (F : I -> R) (s : seq I) :
  {in P, forall i, F i \is real} -> \sum_(i <- s | P i) F i \is real.
Admitted.

Lemma prod_real I (P : pred I) (F : I -> R) (s : seq I) :
  {in P, forall i, F i \is real} -> \prod_(i <- s | P i) F i \is real.
Admitted.

Section NormedZmoduleTheory.

Variable V : normedZmodType R.
Implicit Types (v w : V).

Lemma normr0 : `|0 : V| = 0.
Admitted.

Lemma normr0P v : reflect (`|v| = 0) (v == 0).
Admitted.

Definition normr_eq0 v := sameP (`|v| =P 0) (normr0P v).

Lemma distrC v w : `|v - w| = `|w - v|.
Admitted.

Lemma normr_id v : `| `|v| | = `|v|.
Admitted.

Lemma normr_ge0 v : 0 <= `|v|.
Admitted.

Lemma normr_le0 v : `|v| <= 0 = (v == 0).
Admitted.

Lemma normr_lt0 v : `|v| < 0 = false.
Admitted.

Lemma normr_gt0 v : `|v| > 0 = (v != 0).
Admitted.

Definition normrE := (normr_id, normr0, normr1, normrN1, normr_ge0, normr_eq0,
  normr_lt0, normr_le0, normr_gt0, normrN).

End NormedZmoduleTheory.

Lemma ler0_def x : (x <= 0) = (`|x| == - x).
Admitted.

Lemma ler0_norm x : x <= 0 -> `|x| = - x.
Admitted.

Definition gtr0_norm x (hx : 0 < x) := ger0_norm (ltW hx).
Definition ltr0_norm x (hx : x < 0) := ler0_norm (ltW hx).

Lemma ger0_le_norm :
  {in nneg &, {mono (@normr _ R) : x y / x <= y}}.
Admitted.

Lemma gtr0_le_norm :
  {in pos &, {mono (@normr _ R) : x y / x <= y}}.
Admitted.

Lemma ler0_ge_norm :
  {in npos &, {mono (@normr _ R) : x y / x <= y >-> x >= y}}.
Admitted.

Lemma ltr0_ge_norm :
  {in neg &, {mono (@normr _ R) : x y / x <= y >-> x >= y}}.
Admitted.

Lemma subr_ge0 x y : (0 <= y - x) = (x <= y).
Admitted.

End NumIntegralDomainTheory.
#[global] Hint Extern 0 (is_true (0 <= norm _)) => apply: normr_ge0 : core.

Section NumDomainOperationTheory.

Variable R : numDomainType.
Implicit Types x y z t : R.

Lemma ler_pM x1 y1 x2 y2 :
  0 <= x1 -> 0 <= x2 -> x1 <= y1 -> x2 <= y2 -> x1 * x2 <= y1 * y2.
Admitted.

Section RealDomainArgExtremum.

End RealDomainArgExtremum.

Section NormedZmoduleTheory.

End NormedZmoduleTheory.

End NumDomainOperationTheory.
#[deprecated(since="mathcomp 1.17.0", note="Use ler_pM instead.")]
Notation ler_pmul := ler_pM.

Section NumDomainMonotonyTheoryForReals.

End NumDomainMonotonyTheoryForReals.

Section FinGroup.

End FinGroup.

Section NumFieldTheory.

End NumFieldTheory.

Section RealDomainTheory.

End RealDomainTheory.

Section RealDomainOperations.

Section MinMax.

End MinMax.

Section PolyBounds.

End PolyBounds.

End RealDomainOperations.

Section RealField.

End RealField.

Section ArchimedeanFieldTheory.

End ArchimedeanFieldTheory.

Section RealClosedFieldTheory.

Variable R : rcfType.
Implicit Types a x y : R.

Lemma sqr_sqrtr a : 0 <= a -> sqrt a ^+ 2 = a.
Admitted.

End RealClosedFieldTheory.

Section ClosedFieldTheory.

End ClosedFieldTheory.

End Theory.

Module Export Pdeg2.

Module Export NumClosed.

Section Pdeg2NumClosed.

End Pdeg2NumClosed.

End NumClosed.

Module Export NumClosedMonic.

Section Pdeg2NumClosedMonic.

End Pdeg2NumClosedMonic.
End NumClosedMonic.

Module Export Real.

Section Pdeg2Real.

Section Pdeg2RealConvex.

End Pdeg2RealConvex.

Section Pdeg2RealConcave.

End Pdeg2RealConcave.
End Pdeg2Real.

Section Pdeg2RealClosed.

Section Pdeg2RealClosedConvex.

End Pdeg2RealClosedConvex.

Section Pdeg2RealClosedConcave.

End Pdeg2RealClosedConcave.
End Pdeg2RealClosed.
End Real.

Module Export RealMonic.

Section Pdeg2RealMonic.

End Pdeg2RealMonic.

Section Pdeg2RealClosedMonic.

End Pdeg2RealClosedMonic.
End RealMonic.
End Pdeg2.

Section Degle2PolyRealConvex.

End Degle2PolyRealConvex.

Section Degle2PolyRealConcave.

End Degle2PolyRealConcave.

Section Degle2PolyRealClosedConvex.

End Degle2PolyRealClosedConvex.

Section Degle2PolyRealClosedConcave.

End Degle2PolyRealClosedConcave.

Module Export NumMixin.
Section NumMixin.

End NumMixin.

Module Export Exports.
End Exports.

End NumMixin.

Module Export RealMixin.
Section RealMixin.

End RealMixin.

Module Export Exports.
End Exports.

End RealMixin.

Module Export RealLeMixin.
Section RealLeMixin.

End RealLeMixin.

Module Export Exports.
End Exports.

End RealLeMixin.

Module Export RealLtMixin.
Section RealLtMixin.

End RealLtMixin.

Module Export Exports.
End Exports.

End RealLtMixin.

End Num.
Export Num.NumDomain.Exports.
Export Num.NormedZmodule.Exports.
Export Num.NumField.Exports.
Export Num.RealClosedField.Exports.
Export Num.Syntax.

End ssrnum.

End mathcomp_DOT_algebra_DOT_ssrnum_WRAPPED.
Module Export mathcomp_DOT_algebra_DOT_ssrnum.
Module Export mathcomp.
Module Export algebra.
Module ssrnum.
Include mathcomp_DOT_algebra_DOT_ssrnum_WRAPPED.ssrnum.
End ssrnum.

End algebra.

End mathcomp.

End mathcomp_DOT_algebra_DOT_ssrnum.
Module mathcomp_DOT_analysis_DOT_signed_WRAPPED.
Module Export signed.
Import Coq.ssr.ssreflect.
Import Coq.ssr.ssrfun.
Import Coq.ssr.ssrbool.
Import mathcomp.ssreflect.eqtype.
Import mathcomp.ssreflect.order.
Import mathcomp.algebra.ssralg.
Import mathcomp.algebra.ssrnum.
Reserved Notation "x %:num" (at level 2, format "x %:num").

Set Implicit Arguments.
Unset Strict Implicit.

Local Open Scope ring_scope.
Local Open Scope order_scope.
Declare Scope snum_sign_scope.
Delimit Scope snum_sign_scope with snum_sign.
Declare Scope snum_nullity_scope.
Delimit Scope snum_nullity_scope with snum_nullity.

Module Import KnownSign.
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
End KnownSign.

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

Module Export Exports.
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
End Exports.
End Signed.

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

End signed.

End mathcomp_DOT_analysis_DOT_signed_WRAPPED.
Module Export mathcomp.
Module Export analysis.
Module signed.
Include mathcomp_DOT_analysis_DOT_signed_WRAPPED.signed.
End signed.
Export mathcomp.algebra.ssralg.
Export mathcomp.algebra.ssrnum.

Import mathcomp.ssreflect.all_ssreflect.

Set   Implicit Arguments.
Unset Strict Implicit.

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
Local Open Scope ring_scope.
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
Local Open Scope ring_scope.

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
Import Num.Theory.
Local Open Scope ring_scope.

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
Import mathcomp.analysis.signed.
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
