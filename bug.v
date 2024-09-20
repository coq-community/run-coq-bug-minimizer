
(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "-projection-no-head-constant" "-w" "-redundant-canonical-projection" "-w" "-notation-overridden" "-w" "+duplicate-clear" "-w" "-ambiguous-paths" "-w" "+non-primitive-record" "-w" "+undeclared-scope" "-w" "+deprecated-hint-without-locality" "-w" "+deprecated-hint-rewrite-without-locality" "-w" "-elpi.add-const-for-axiom-or-sectionvar" "-w" "-opaque-let" "-w" "-argument-scope-delimiter" "-w" "-overwriting-delimiting-key" "-w" "-closed-notation-not-level-0" "-w" "-postfix-notation-not-level-1" "-w" "-deprecated-native-compiler-option" "-native-compiler" "ondemand" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/mathcomp/mathcomp" "mathcomp" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/HB" "HB" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/elpi" "elpi" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/elpi_elpi" "elpi_elpi" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/elpi_examples" "elpi_examples" "-I" "/github/workspace/builds/coq/coq-failing/_build_ci/mathcomp/mathcomp" "-top" "Top.bug_01") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 2537 lines to 103 lines, then from 116 lines to 1129 lines, then from 1134 lines to 287 lines, then from 300 lines to 1280 lines, then from 1285 lines to 292 lines, then from 305 lines to 1296 lines, then from 1300 lines to 533 lines, then from 509 lines to 357 lines, then from 370 lines to 2392 lines, then from 2397 lines to 398 lines, then from 411 lines to 1104 lines, then from 1109 lines to 690 lines, then from 580 lines to 495 lines, then from 508 lines to 1540 lines, then from 1545 lines to 678 lines, then from 691 lines to 2493 lines, then from 2498 lines to 1305 lines, then from 1265 lines to 914 lines, then from 927 lines to 6128 lines, then from 6133 lines to 6702 lines, then from 6490 lines to 5306 lines, then from 5304 lines to 4731 lines, then from 4729 lines to 3961 lines *)
(* coqc version 8.21+alpha compiled with OCaml 4.14.1
   coqtop version runner-t7b1znuaq-project-4504-concurrent-5:/builds/coq/coq/_build/default,(HEAD detached at 995395a49c6a1) (995395a49c6a15a52eef2f9b0f48eebe4aaa49d6)
   Expected coqc runtime on this file: 15.384 sec *)












Require Stdlib.Init.Ltac.
Require Stdlib.NArith.BinNat.
Require Stdlib.NArith.Ndec.
Require Stdlib.PArith.BinPos.
Require Stdlib.Strings.String.
Require Stdlib.setoid_ring.Ring.
Require Stdlib.ssr.ssrbool.
Require Stdlib.ssr.ssreflect.
Require Stdlib.ssr.ssrfun.
Require mathcomp.ssreflect.ssrnotations.
Require elpi_elpi.dummy.
Require mathcomp.ssreflect.ssreflect.
Require elpi.elpi.
Require mathcomp.ssreflect.ssrfun.
Require elpi.apps.locker.locker.
Require mathcomp.ssreflect.ssrbool.
Require HB.structures.
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
Require mathcomp.ssreflect.prime.
Require mathcomp.ssreflect.ssrAC.
Require mathcomp.fingroup.fingroup.
Require mathcomp.ssreflect.binomial.
Require mathcomp.ssreflect.order.
Require mathcomp.algebra.ssralg.
Require mathcomp.algebra.countalg.
Require mathcomp.algebra.poly.

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

Import HB.structures.
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

Fact ring_display : Order.disp_t.
Admitted.

Module Export Num.

#[short(type="porderZmodType")]
HB.structure Definition POrderedZmodule :=
  { R of Order.isPOrder ring_display R & GRing.Zmodule R }.

HB.mixin Record Zmodule_isNormed (R : POrderedZmodule.type) M
         of GRing.Zmodule M := {
  norm : M -> R;
  ler_normD : forall x y, norm (x + y) <= norm x + norm y;
  normr0_eq0 : forall x, norm x = 0 -> x = 0;
  normrMn : forall x n, norm (x *+ n) = norm x *+ n;
  normrN : forall x, norm (- x) = norm x;
}.

#[short(type="normedZmodType")]
HB.structure Definition NormedZmodule (R : porderZmodType) :=
  { M of Zmodule_isNormed R M & GRing.Zmodule M }.
Arguments norm {R M} x : rename.

Module Export NormedZmoduleExports.
Bind Scope ring_scope with NormedZmodule.sort.

End NormedZmoduleExports.
HB.export NormedZmoduleExports.

HB.mixin Record isNumRing R of GRing.Ring R & POrderedZmodule R
  & NormedZmodule (POrderedZmodule.clone R _) R := {
 addr_gt0 : forall x y : R, 0 < x -> 0 < y -> 0 < (x + y);
 ger_leVge : forall x y : R, 0 <= x -> 0 <= y -> (x <= y) || (y <= x);
 normrM : {morph (norm : R -> R) : x y / x * y};
 ler_def : forall x y : R, (x <= y) = (norm (y - x) == (y - x));
}.

#[short(type="numDomainType")]
HB.structure Definition NumDomain := { R of
     GRing.IntegralDomain R &
     POrderedZmodule R &
     NormedZmodule (POrderedZmodule.clone R _) R &
     isNumRing R
  }.
Arguments addr_gt0 {_} [x y] : rename.
Arguments ger_leVge {_} [x y] : rename.

Module Export NumDomainExports.
Bind Scope ring_scope with NumDomain.sort.
End NumDomainExports.
HB.export NumDomainExports.

Module Import Def.

Notation normr := norm.
Notation "`| x |" := (norm x) : ring_scope.

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

Section NumDomainDef.
Context {R : numDomainType}.
Definition sgr (x : R) : R.
Admitted.
Definition Rpos_pred := fun x : R => 0 < x.
Definition Rpos : qualifier 0 R.
exact ([qualify x | Rpos_pred x]).
Defined.
Definition Rneg_pred := fun x : R => x < 0.
Definition Rneg : qualifier 0 R.
Admitted.
Definition Rnneg_pred := fun x : R => 0 <= x.
Definition Rnneg : qualifier 0 R.
exact ([qualify x : R | Rnneg_pred x]).
Defined.
Definition Rnpos_pred := fun x : R => x <= 0.
Definition Rnpos : qualifier 0 R.
Admitted.
Definition Rreal_pred := fun x : R => (0 <= x) || (x <= 0).
Definition Rreal : qualifier 0 R.
exact ([qualify x : R | Rreal_pred x]).
Defined.

End NumDomainDef.

End Def.

Arguments Rpos_pred _ _ /.
Arguments Rneg_pred _ _ /.
Arguments Rnneg_pred _ _ /.
Arguments Rreal_pred _ _ /.

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

Module Import Syntax.
Import Def.

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

Export Order.POCoercions.

End Syntax.

Section ExtensionAxioms.

Variable R : numDomainType.
Definition real_axiom : Prop.
Admitted.
Definition archimedean_axiom : Prop.
Admitted.
Definition real_closed_axiom : Prop.
Admitted.

End ExtensionAxioms.

#[short(type="numFieldType")]
HB.structure Definition NumField := { R of GRing.UnitRing_isField R &
     GRing.IntegralDomain R &
     POrderedZmodule R &
     NormedZmodule (POrderedZmodule.clone R _) R &
     isNumRing R }.

Module Export NumFieldExports.
Bind Scope ring_scope with NumField.sort.
End NumFieldExports.
HB.export NumFieldExports.

HB.mixin Record NumField_isImaginary R of NumField R := {
  imaginary : R;
  conj_op : {rmorphism R -> R};
  sqrCi : imaginary ^+ 2 = - 1;
  normCK : forall x, `|x| ^+ 2 = x * conj_op x;
}.

#[short(type="numClosedFieldType")]
HB.structure Definition ClosedField :=
  { R of NumField_isImaginary R & GRing.ClosedField R & NumField R }.

Module Export ClosedFieldExports.
Bind Scope ring_scope with ClosedField.sort.
End ClosedFieldExports.
HB.export ClosedFieldExports.

#[short(type="realDomainType")]
HB.structure Definition RealDomain :=
  { R of Order.Total ring_display R & NumDomain R }.

Module Export RealDomainExports.
Bind Scope ring_scope with RealDomain.sort.
End RealDomainExports.
HB.export RealDomainExports.

#[short(type="realFieldType")]
HB.structure Definition RealField :=
  { R of Order.Total ring_display R & NumField R }.

Module Export RealFieldExports.
Bind Scope ring_scope with RealField.sort.
End RealFieldExports.
HB.export RealFieldExports.

HB.mixin Record RealField_isClosed R of RealField R := {
  poly_ivt_subproof : real_closed_axiom R
}.

#[short(type="rcfType")]
HB.structure Definition RealClosedField :=
  { R of RealField_isClosed R & RealField R }.

Module Export RealClosedFieldExports.
Bind Scope ring_scope with RealClosedField.sort.
End RealClosedFieldExports.
HB.export RealClosedFieldExports.

Module Import Internals.

Section NumDomain.
Variable R : numDomainType.
Implicit Types x y : R.

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
#[export]
HB.instance Definition _ := GRing.isDivClosed.Build R Rpos_pred
  pos_divr_closed.

Fact nneg_divr_closed : divr_closed (@nneg R).
Admitted.
#[export]
HB.instance Definition _ := GRing.isDivClosed.Build R Rnneg_pred
  nneg_divr_closed.

Fact nneg_addr_closed : addr_closed (@nneg R).
Admitted.
#[export]
HB.instance Definition _ := GRing.isAddClosed.Build R Rnneg_pred
  nneg_addr_closed.

Fact real_oppr_closed : oppr_closed (@real R).
Admitted.
#[export]
HB.instance Definition _ := GRing.isOppClosed.Build R Rreal_pred
  real_oppr_closed.

Fact real_addr_closed : addr_closed (@real R).
Admitted.
#[export]
HB.instance Definition _ := GRing.isAddClosed.Build R Rreal_pred
  real_addr_closed.

Fact real_divr_closed : divr_closed (@real R).
Admitted.
#[export]
HB.instance Definition _ := GRing.isDivClosed.Build R Rreal_pred
  real_divr_closed.

End NumDomain.

Lemma num_real (R : realDomainType) (x : R) : x \is real.
Admitted.

Section RealClosed.
Variable R : rcfType.

Lemma poly_ivt : real_closed_axiom R.
Admitted.

Fact sqrtr_subproof (x : R) :
  exists2 y, 0 <= y & (if 0 <= x then y ^+ 2 == x else y == 0) : bool.
Admitted.

End RealClosed.

Module Export Exports.
HB.reexport.
End Exports.

End Internals.

Module Export PredInstances.

Export Internals.Exports.

End PredInstances.

Module Import ExtraDef.

Definition sqrtr {R} x := s2val (sig2W (@sqrtr_subproof R x)).

End ExtraDef.

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
Hint Extern 0 (is_true (@Order.le ring_display _ _ _)) =>
  (apply: ler01) : core.
Hint Extern 0 (is_true (@Order.lt ring_display _ _ _)) =>
  (apply: ltr01) : core.
Hint Extern 0 (is_true (@Order.le ring_display _ _ _)) =>
  (apply: ler0n) : core.
Lemma ltr0Sn n : 0 < n.+1%:R :> R.
Admitted.
Lemma ltr0n n : (0 < n%:R :> R) = (0 < n)%N.
Admitted.
Hint Extern 0 (is_true (@Order.lt ring_display _ _ _)) =>
  (apply: ltr0Sn) : core.

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

Lemma normr_unit : {homo (@norm _  R) : x / x \is a GRing.unit}.
Admitted.

Lemma normrV : {in GRing.unit, {morph (@norm _  R) : x / x ^-1}}.
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
Lemma subr_gt0 x y : (0 < y - x) = (x < y).
Admitted.
Lemma subr_le0  x y : (y - x <= 0) = (y <= x).
Admitted.

Lemma subr_lt0  x y : (y - x < 0) = (y < x).
Admitted.

Definition subr_lte0 := (subr_le0, subr_lt0).
Definition subr_gte0 := (subr_ge0, subr_gt0).
Definition subr_cp0 := (subr_lte0, subr_gte0).

Lemma comparable0r x : (0 >=< x)%R = (x \is Num.real).
Admitted.

Lemma comparabler0 x : (x >=< 0)%R = (x \is Num.real).
Admitted.

Lemma subr_comparable0 x y : (x - y >=< 0)%R = (x >=< y)%R.
Admitted.

Lemma comparablerE x y : (x >=< y)%R = (x - y \is Num.real).
Admitted.

Lemma  comparabler_trans : transitive (comparable : rel R).
Admitted.

Definition lter01 := (ler01, ltr01).

Lemma addr_ge0 x y : 0 <= x -> 0 <= y -> 0 <= x + y.
Admitted.

End NumIntegralDomainTheory.

Arguments ler01 {R}.
Arguments ltr01 {R}.
Arguments normr_idP {R x}.
Arguments normr0P {R V v}.
#[global] Hint Extern 0 (is_true (@Order.le ring_display _ _ _)) =>
  (apply: ler01) : core.
#[global] Hint Extern 0 (is_true (@Order.lt ring_display _ _ _)) =>
  (apply: ltr01) : core.
#[global] Hint Extern 0 (is_true (@Order.le ring_display _ _ _)) =>
  (apply: ler0n) : core.
#[global] Hint Extern 0 (is_true (@Order.lt ring_display _ _ _)) =>
  (apply: ltr0Sn) : core.
#[global] Hint Extern 0 (is_true (0 <= norm _)) => apply: normr_ge0 : core.

Lemma normr_nneg (R : numDomainType) (x : R) : `|x| \is Num.nneg.
Admitted.
#[global] Hint Resolve normr_nneg : core.

Section NumDomainOperationTheory.

Variable R : numDomainType.
Implicit Types x y z t : R.

Lemma lerN2 : {mono -%R : x y /~ x <= y :> R}.
Admitted.
Hint Resolve lerN2 : core.
Lemma ltrN2 : {mono -%R : x y /~ x < y :> R}.
Admitted.
Hint Resolve ltrN2 : core.
Definition lterN2 := (lerN2, ltrN2).

Lemma lerNr x y : (x <= - y) = (y <= - x).
Admitted.

Lemma ltrNr x y : (x < - y) = (y < - x).
Admitted.

Definition lterNr := (lerNr, ltrNr).

Lemma lerNl x y : (- x <= y) = (- y <= x).
Admitted.

Lemma ltrNl x y : (- x < y) = (- y < x).
Admitted.

Definition lterNl := (lerNl, ltrNl).

Lemma oppr_ge0 x : (0 <= - x) = (x <= 0).
Admitted.

Lemma oppr_gt0 x : (0 < - x) = (x < 0).
Admitted.

Definition oppr_gte0 := (oppr_ge0, oppr_gt0).

Lemma oppr_le0 x : (- x <= 0) = (0 <= x).
Admitted.

Lemma oppr_lt0 x : (- x < 0) = (0 < x).
Admitted.

Lemma gtrN x : 0 < x -> - x < x.
Admitted.

Definition oppr_lte0 := (oppr_le0, oppr_lt0).
Definition oppr_cp0 := (oppr_gte0, oppr_lte0).
Definition lterNE := (oppr_cp0, lterN2).

Lemma ge0_cp x : 0 <= x -> (- x <= 0) * (- x <= x).
Admitted.

Lemma gt0_cp x : 0 < x ->
  (0 <= x) * (- x <= 0) * (- x <= x) * (- x < 0) * (- x < x).
Admitted.

Lemma le0_cp x : x <= 0 -> (0 <= - x) * (x <= - x).
Admitted.

Lemma lt0_cp x :
  x < 0 -> (x <= 0) * (0 <= - x) * (x <= - x) * (0 < - x) * (x < - x).
Admitted.

Lemma ger0_real x : 0 <= x -> x \is real.
Admitted.

Lemma ler0_real x : x <= 0 -> x \is real.
Admitted.

Lemma gtr0_real x : 0 < x -> x \is real.
Admitted.

Lemma ltr0_real x : x < 0 -> x \is real.
Admitted.

Lemma real0 : 0 \is @real R.
Admitted.
Lemma real1 : 1 \is @real R.
Admitted.
Lemma realn n : n%:R \is @real R.
Admitted.
#[local] Hint Resolve real0 real1 : core.

Lemma ler_leVge x y : x <= 0 -> y <= 0 -> (x <= y) || (y <= x).
Admitted.

Lemma real_leVge x y : x \is real -> y \is real -> (x <= y) || (y <= x).
Admitted.

Lemma real_comparable x y : x \is real -> y \is real -> x >=< y.
Admitted.

Lemma realB : {in real &, forall x y, x - y \is real}.
Admitted.

Lemma realN : {mono (@GRing.opp R) : x / x \is real}.
Admitted.

Lemma realBC x y : (x - y \is real) = (y - x \is real).
Admitted.

Lemma realD : {in real &, forall x y, x + y \is real}.
Admitted.

Variant ler_xor_gt (x y : R) : R -> R -> R -> R -> R -> R ->
    bool -> bool -> Set :=
  | LerNotGt of x <= y : ler_xor_gt x y x x y y (y - x) (y - x) true false
  | GtrNotLe of y < x  : ler_xor_gt x y y y x x (x - y) (x - y) false true.

Variant ltr_xor_ge (x y : R) : R -> R -> R -> R -> R -> R ->
    bool -> bool -> Set :=
  | LtrNotGe of x < y  : ltr_xor_ge x y x x y y (y - x) (y - x) false true
  | GerNotLt of y <= x : ltr_xor_ge x y y y x x (x - y) (x - y) true false.

Variant comparer x y : R -> R -> R -> R -> R -> R ->
    bool -> bool -> bool -> bool -> bool -> bool -> Set :=
  | ComparerLt of x < y : comparer x y x x y y (y - x) (y - x)
    false false false true false true
  | ComparerGt of x > y : comparer x y y y x x (x - y) (x - y)
    false false true false true false
  | ComparerEq of x = y : comparer x y x x x x 0 0
    true true true true false false.

Lemma real_leP x y : x \is real -> y \is real ->
  ler_xor_gt x y (min y x) (min x y) (max y x) (max x y)
                 `|x - y| `|y - x| (x <= y) (y < x).
Admitted.

Lemma real_ltP x y : x \is real -> y \is real ->
  ltr_xor_ge x y (min y x) (min x y) (max y x) (max x y)
             `|x - y| `|y - x| (y <= x) (x < y).
Admitted.

Lemma real_ltNge : {in real &, forall x y, (x < y) = ~~ (y <= x)}.
Admitted.

Lemma real_leNgt : {in real &, forall x y, (x <= y) = ~~ (y < x)}.
Admitted.

Lemma real_ltgtP x y : x \is real -> y \is real ->
  comparer x y (min y x) (min x y) (max y x) (max x y) `|x - y| `|y - x|
               (y == x) (x == y) (x >= y) (x <= y) (x > y) (x < y).
Admitted.

Variant ger0_xor_lt0 (x : R) : R -> R -> R -> R -> R ->
    bool -> bool -> Set :=
  | Ger0NotLt0 of 0 <= x : ger0_xor_lt0 x 0 0 x x x false true
  | Ltr0NotGe0 of x < 0  : ger0_xor_lt0 x x x 0 0 (- x) true false.

Variant ler0_xor_gt0 (x : R) : R -> R -> R -> R -> R ->
   bool -> bool -> Set :=
  | Ler0NotLe0 of x <= 0 : ler0_xor_gt0 x x x 0 0 (- x) false true
  | Gtr0NotGt0 of 0 < x  : ler0_xor_gt0 x 0 0 x x x true false.

Variant comparer0 x : R -> R -> R -> R -> R ->
    bool -> bool -> bool -> bool -> bool -> bool -> Set :=
  | ComparerGt0 of 0 < x : comparer0 x 0 0 x x x false false false true false true
  | ComparerLt0 of x < 0 : comparer0 x x x 0 0 (- x) false false true false true false
  | ComparerEq0 of x = 0 : comparer0 x 0 0 0 0 0 true true true true false false.

Lemma real_ge0P x : x \is real -> ger0_xor_lt0 x
   (min 0 x) (min x 0) (max 0 x) (max x 0)
  `|x| (x < 0) (0 <= x).
Admitted.

Lemma real_le0P x : x \is real -> ler0_xor_gt0 x
  (min 0 x) (min x 0) (max 0 x) (max x 0)
  `|x| (0 < x) (x <= 0).
Admitted.

Lemma real_ltgt0P x : x \is real ->
  comparer0 x (min 0 x) (min x 0) (max 0 x) (max x 0)
            `|x| (0 == x) (x == 0) (x <= 0) (0 <= x) (x < 0) (x > 0).
Admitted.

Lemma max_real : {in real &, forall x y, max x y \is real}.
Admitted.

Lemma min_real : {in real &, forall x y, min x y \is real}.
Admitted.

Lemma bigmax_real I x0 (r : seq I) (P : pred I) (f : I -> R):
  x0 \is real -> {in P, forall i : I, f i \is real} ->
  \big[max/x0]_(i <- r | P i) f i \is real.
Admitted.

Lemma bigmin_real I x0 (r : seq I) (P : pred I) (f : I -> R):
  x0 \is real -> {in P, forall i : I, f i \is real} ->
  \big[min/x0]_(i <- r | P i) f i \is real.
Admitted.

Lemma real_neqr_lt : {in real &, forall x y, (x != y) = (x < y) || (y < x)}.
Admitted.

Lemma lerB_real x y : x <= y -> y - x \is real.
Admitted.

Lemma gerB_real x y : x <= y -> x - y \is real.
Admitted.

Lemma ler_real y x : x <= y -> (x \is real) = (y \is real).
Admitted.

Lemma ger_real x y : y <= x -> (x \is real) = (y \is real).
Admitted.

Lemma ger1_real x : 1 <= x -> x \is real.
Admitted.
Lemma ler1_real x : x <= 1 -> x \is real.
Admitted.

Lemma Nreal_leF x y : y \is real -> x \notin real -> (x <= y) = false.
Admitted.

Lemma Nreal_geF x y : y \is real -> x \notin real -> (y <= x) = false.
Admitted.

Lemma Nreal_ltF x y : y \is real -> x \notin real -> (x < y) = false.
Admitted.

Lemma Nreal_gtF x y : y \is real -> x \notin real -> (y < x) = false.
Admitted.

Lemma real_wlog_ler P :
    (forall a b, P b a -> P a b) -> (forall a b, a <= b -> P a b) ->
  forall a b : R, a \is real -> b \is real -> P a b.
Admitted.

Lemma real_wlog_ltr P :
    (forall a, P a a) -> (forall a b, (P b a -> P a b)) ->
    (forall a b, a < b -> P a b) ->
  forall a b : R, a \is real -> b \is real -> P a b.
Admitted.

Lemma lerD2l x : {mono +%R x : y z / y <= z}.
Admitted.

Lemma lerD2r x : {mono +%R^~ x : y z / y <= z}.
Admitted.

Lemma ltrD2l x : {mono +%R x : y z / y < z}.
Admitted.

Lemma ltrD2r x : {mono +%R^~ x : y z / y < z}.
Admitted.

Definition lerD2 := (lerD2l, lerD2r).
Definition ltrD2 := (ltrD2l, ltrD2r).
Definition lterD2 := (lerD2, ltrD2).

Lemma lerD x y z t : x <= y -> z <= t -> x + z <= y + t.
Admitted.

Lemma ler_ltD x y z t : x <= y -> z < t -> x + z < y + t.
Admitted.

Lemma ltr_leD x y z t : x < y -> z <= t -> x + z < y + t.
Admitted.

Lemma ltrD x y z t : x < y -> z < t -> x + z < y + t.
Admitted.

Lemma lerB x y z t : x <= y -> t <= z -> x - z <= y - t.
Admitted.

Lemma ler_ltB x y z t : x <= y -> t < z -> x - z < y - t.
Admitted.

Lemma ltr_leB x y z t : x < y -> t <= z -> x - z < y - t.
Admitted.

Lemma ltrB x y z t : x < y -> t < z -> x - z < y - t.
Admitted.

Lemma lerBlDr x y z : (x - y <= z) = (x <= z + y).
Admitted.

Lemma ltrBlDr x y z : (x - y < z) = (x < z + y).
Admitted.

Lemma lerBrDr x y z : (x <= y - z) = (x + z <= y).
Admitted.

Lemma ltrBrDr x y z : (x < y - z) = (x + z < y).
Admitted.

Definition lerBDr := (lerBlDr, lerBrDr).
Definition ltrBDr := (ltrBlDr, ltrBrDr).
Definition lterBDr := (lerBDr, ltrBDr).

Lemma lerBlDl x y z : (x - y <= z) = (x <= y + z).
Admitted.

Lemma ltrBlDl x y z : (x - y < z) = (x < y + z).
Admitted.

Lemma lerBrDl x y z : (x <= y - z) = (z + x <= y).
Admitted.

Lemma ltrBrDl x y z : (x < y - z) = (z + x < y).
Admitted.

Definition lerBDl := (lerBlDl, lerBrDl).
Definition ltrBDl := (ltrBlDl, ltrBrDl).
Definition lterBDl := (lerBDl, ltrBDl).

Lemma lerDl x y : (x <= x + y) = (0 <= y).
Admitted.

Lemma ltrDl x y : (x < x + y) = (0 < y).
Admitted.

Lemma lerDr x y : (x <= y + x) = (0 <= y).
Admitted.

Lemma ltrDr x y : (x < y + x) = (0 < y).
Admitted.

Lemma gerDl x y : (x + y <= x) = (y <= 0).
Admitted.

Lemma gerBl x y : (x - y <= x) = (0 <= y).
Admitted.

Lemma gtrDl x y : (x + y < x) = (y < 0).
Admitted.

Lemma gtrBl x y : (x - y < x) = (0 < y).
Admitted.

Lemma gerDr x y : (y + x <= x) = (y <= 0).
Admitted.

Lemma gtrDr x y : (y + x < x) = (y < 0).
Admitted.

Definition cprD := (lerDl, lerDr, gerDl, gerDl,
                    ltrDl, ltrDr, gtrDl, gtrDl).

Lemma ler_wpDl y x z : 0 <= x -> y <= z -> y <= x + z.
Admitted.

Lemma ltr_wpDl y x z : 0 <= x -> y < z -> y < x + z.
Admitted.

Lemma ltr_pwDl y x z : 0 < x -> y <= z -> y < x + z.
Admitted.

Lemma ltr_pDl y x z : 0 < x -> y < z -> y < x + z.
Admitted.

Lemma ler_wnDl y x z : x <= 0 -> y <= z -> x + y <= z.
Admitted.

Lemma ltr_wnDl y x z : x <= 0 -> y < z -> x + y < z.
Admitted.

Lemma ltr_nwDl y x z : x < 0 -> y <= z -> x + y < z.
Admitted.

Lemma ltr_nDl y x z : x < 0 -> y < z -> x + y < z.
Admitted.

Lemma ler_wpDr y x z : 0 <= x -> y <= z -> y <= z + x.
Admitted.

Lemma ltr_wpDr y x z : 0 <= x -> y < z -> y < z + x.
Admitted.

Lemma ltr_pwDr y x z : 0 < x -> y <= z -> y < z + x.
Admitted.

Lemma ltr_pDr y x z : 0 < x -> y < z -> y < z + x.
Admitted.

Lemma ler_wnDr y x z : x <= 0 -> y <= z -> y + x <= z.
Admitted.

Lemma ltr_wnDr y x z : x <= 0 -> y < z -> y + x < z.
Admitted.

Lemma ltr_nwDr y x z : x < 0 -> y <= z -> y + x < z.
Admitted.

Lemma ltr_nDr y x z : x < 0 -> y < z -> y + x < z.
Admitted.

Lemma paddr_eq0 (x y : R) :
  0 <= x -> 0 <= y -> (x + y == 0) = (x == 0) && (y == 0).
Admitted.

Lemma naddr_eq0 (x y : R) :
  x <= 0 -> y <= 0 -> (x + y == 0) = (x == 0) && (y == 0).
Admitted.

Lemma addr_ss_eq0 (x y : R) :
    (0 <= x) && (0 <= y) || (x <= 0) && (y <= 0) ->
  (x + y == 0) = (x == 0) && (y == 0).
Admitted.

Lemma sumr_ge0 I (r : seq I) (P : pred I) (F : I -> R) :
  (forall i, P i -> (0 <= F i)) -> 0 <= \sum_(i <- r | P i) (F i).
Admitted.

Lemma ler_sum I (r : seq I) (P : pred I) (F G : I -> R) :
    (forall i, P i -> F i <= G i) ->
  \sum_(i <- r | P i) F i <= \sum_(i <- r | P i) G i.
Admitted.

Lemma ler_sum_nat (m n : nat) (F G : nat -> R) :
  (forall i, (m <= i < n)%N -> F i <= G i) ->
  \sum_(m <= i < n) F i <= \sum_(m <= i < n) G i.
Admitted.

Lemma psumr_eq0 (I : eqType) (r : seq I) (P : pred I) (F : I -> R) :
    (forall i, P i -> 0 <= F i) ->
  (\sum_(i <- r | P i) (F i) == 0) = (all (fun i => (P i) ==> (F i == 0)) r).
Admitted.

Lemma psumr_eq0P (I : finType) (P : pred I) (F : I -> R) :
     (forall i, P i -> 0 <= F i) -> \sum_(i | P i) F i = 0 ->
  (forall i, P i -> F i = 0).
Admitted.

Lemma psumr_neq0 (I : eqType) (r : seq I) (P : pred I) (F : I -> R) :
    (forall i, P i -> 0 <= F i) ->
  (\sum_(i <- r | P i) (F i) != 0) = (has (fun i => P i && (0 < F i)) r).
Admitted.

Lemma psumr_neq0P (I : finType) (P : pred I) (F : I -> R) :
     (forall i, P i -> 0 <= F i) -> \sum_(i | P i) F i <> 0 ->
  (exists i, P i && (0 < F i)).
Admitted.

Lemma ler_pM2l x : 0 < x -> {mono *%R x : x y / x <= y}.
Admitted.

Lemma ltr_pM2l x : 0 < x -> {mono *%R x : x y / x < y}.
Admitted.

Definition lter_pM2l := (ler_pM2l, ltr_pM2l).

Lemma ler_pM2r x : 0 < x -> {mono *%R^~ x : x y / x <= y}.
Admitted.

Lemma ltr_pM2r x : 0 < x -> {mono *%R^~ x : x y / x < y}.
Admitted.

Definition lter_pM2r := (ler_pM2r, ltr_pM2r).

Lemma ler_nM2l x : x < 0 -> {mono *%R x : x y /~ x <= y}.
Admitted.

Lemma ltr_nM2l x : x < 0 -> {mono *%R x : x y /~ x < y}.
Admitted.

Definition lter_nM2l := (ler_nM2l, ltr_nM2l).

Lemma ler_nM2r x : x < 0 -> {mono *%R^~ x : x y /~ x <= y}.
Admitted.

Lemma ltr_nM2r x : x < 0 -> {mono *%R^~ x : x y /~ x < y}.
Admitted.

Definition lter_nM2r := (ler_nM2r, ltr_nM2r).

Lemma ler_wpM2l x : 0 <= x -> {homo *%R x : y z / y <= z}.
Admitted.

Lemma ler_wpM2r x : 0 <= x -> {homo *%R^~ x : y z / y <= z}.
Admitted.

Lemma ler_wnM2l x : x <= 0 -> {homo *%R x : y z /~ y <= z}.
Admitted.

Lemma ler_wnM2r x : x <= 0 -> {homo *%R^~ x : y z /~ y <= z}.
Admitted.

Lemma ler_pM x1 y1 x2 y2 :
  0 <= x1 -> 0 <= x2 -> x1 <= y1 -> x2 <= y2 -> x1 * x2 <= y1 * y2.
Admitted.

Lemma ltr_pM x1 y1 x2 y2 :
  0 <= x1 -> 0 <= x2 -> x1 < y1 -> x2 < y2 -> x1 * x2 < y1 * y2.
Admitted.

Lemma ler_pMn2r n : (0 < n)%N -> {mono (@GRing.natmul R)^~ n : x y / x <= y}.
Admitted.

Lemma ltr_pMn2r n : (0 < n)%N -> {mono (@GRing.natmul R)^~ n : x y / x < y}.
Admitted.

Lemma pmulrnI n : (0 < n)%N -> injective ((@GRing.natmul R)^~ n).
Admitted.

Lemma eqr_pMn2r n : (0 < n)%N -> {mono (@GRing.natmul R)^~ n : x y / x == y}.
Admitted.

Lemma pmulrn_lgt0 x n : (0 < n)%N -> (0 < x *+ n) = (0 < x).
Admitted.

Lemma pmulrn_llt0 x n : (0 < n)%N -> (x *+ n < 0) = (x < 0).
Admitted.

Lemma pmulrn_lge0 x n : (0 < n)%N -> (0 <= x *+ n) = (0 <= x).
Admitted.

Lemma pmulrn_lle0 x n : (0 < n)%N -> (x *+ n <= 0) = (x <= 0).
Admitted.

Lemma ltr_wMn2r x y n : x < y -> (x *+ n < y *+ n) = (0 < n)%N.
Admitted.

Lemma ltr_wpMn2r n : (0 < n)%N -> {homo (@GRing.natmul R)^~ n : x y / x < y}.
Admitted.

Lemma ler_wMn2r n : {homo (@GRing.natmul R)^~ n : x y / x <= y}.
Admitted.

Lemma mulrn_wge0 x n : 0 <= x -> 0 <= x *+ n.
Admitted.

Lemma mulrn_wle0 x n : x <= 0 -> x *+ n <= 0.
Admitted.

Lemma lerMn2r n x y : (x *+ n <= y *+ n) = ((n == 0) || (x <= y)).
Admitted.

Lemma ltrMn2r n x y : (x *+ n < y *+ n) = ((0 < n)%N && (x < y)).
Admitted.

Lemma eqrMn2r n x y : (x *+ n == y *+ n) = (n == 0)%N || (x == y).
Admitted.

Lemma mulrn_eq0 x n : (x *+ n == 0) = ((n == 0)%N || (x == 0)).
Admitted.

Lemma eqNr x : (- x == x) = (x == 0).
Admitted.

Lemma mulrIn x : x != 0 -> injective (GRing.natmul x).
Admitted.

Lemma ler_wpMn2l x :
  0 <= x -> {homo (@GRing.natmul R x) : m n / (m <= n)%N >-> m <= n}.
Admitted.

Lemma ler_wnMn2l x :
  x <= 0 -> {homo (@GRing.natmul R x) : m n / (n <= m)%N >-> m <= n}.
Admitted.

Lemma mulrn_wgt0 x n : 0 < x -> 0 < x *+ n = (0 < n)%N.
Admitted.

Lemma mulrn_wlt0 x n : x < 0 -> x *+ n < 0 = (0 < n)%N.
Admitted.

Lemma ler_pMn2l x :
  0 < x -> {mono (@GRing.natmul R x) : m n / (m <= n)%N >-> m <= n}.
Admitted.

Lemma ltr_pMn2l x :
  0 < x -> {mono (@GRing.natmul R x) : m n / (m < n)%N >-> m < n}.
Admitted.

Lemma ler_nMn2l x :
  x < 0 -> {mono (@GRing.natmul R x) : m n / (n <= m)%N >-> m <= n}.
Admitted.

Lemma ltr_nMn2l x :
  x < 0 -> {mono (@GRing.natmul R x) : m n / (n < m)%N >-> m < n}.
Admitted.

Lemma ler_nat m n : (m%:R <= n%:R :> R) = (m <= n)%N.
Admitted.

Lemma ltr_nat m n : (m%:R < n%:R :> R) = (m < n)%N.
Admitted.

Lemma eqr_nat m n : (m%:R == n%:R :> R) = (m == n)%N.
Admitted.

Lemma pnatr_eq1 n : (n%:R == 1 :> R) = (n == 1)%N.
Admitted.

Lemma lern0 n : (n%:R <= 0 :> R) = (n == 0).
Admitted.

Lemma ltrn0 n : (n%:R < 0 :> R) = false.
Admitted.

Lemma ler1n n : 1 <= n%:R :> R = (1 <= n)%N.
Admitted.
Lemma ltr1n n : 1 < n%:R :> R = (1 < n)%N.
Admitted.
Lemma lern1 n : n%:R <= 1 :> R = (n <= 1)%N.
Admitted.
Lemma ltrn1 n : n%:R < 1 :> R = (n < 1)%N.
Admitted.

Lemma ltrN10 : -1 < 0 :> R.
Admitted.
Lemma lerN10 : -1 <= 0 :> R.
Admitted.
Lemma ltr10 : 1 < 0 :> R = false.
Admitted.
Lemma ler10 : 1 <= 0 :> R = false.
Admitted.
Lemma ltr0N1 : 0 < -1 :> R = false.
Admitted.
Lemma ler0N1 : 0 <= -1 :> R = false.
Admitted.

Lemma pmulrn_rgt0 x n : 0 < x -> 0 < x *+ n = (0 < n)%N.
Admitted.

Lemma pmulrn_rlt0 x n : 0 < x -> x *+ n < 0 = false.
Admitted.

Lemma pmulrn_rge0 x n : 0 < x -> 0 <= x *+ n.
Admitted.

Lemma pmulrn_rle0 x n : 0 < x -> x *+ n <= 0 = (n == 0)%N.
Admitted.

Lemma nmulrn_rgt0 x n : x < 0 -> 0 < x *+ n = false.
Admitted.

Lemma nmulrn_rge0 x n : x < 0 -> 0 <= x *+ n = (n == 0)%N.
Admitted.

Lemma nmulrn_rle0 x n : x < 0 -> x *+ n <= 0.
Admitted.

Lemma pmulr_rlt0 x y : 0 < x -> (x * y < 0) = (y < 0).
Admitted.

Lemma pmulr_rle0 x y : 0 < x -> (x * y <= 0) = (y <= 0).
Admitted.

Lemma pmulr_lgt0 x y : 0 < x -> (0 < y * x) = (0 < y).
Admitted.

Lemma pmulr_lge0 x y : 0 < x -> (0 <= y * x) = (0 <= y).
Admitted.

Lemma pmulr_llt0 x y : 0 < x -> (y * x < 0) = (y < 0).
Admitted.

Lemma pmulr_lle0 x y : 0 < x -> (y * x <= 0) = (y <= 0).
Admitted.

Lemma nmulr_rgt0 x y : x < 0 -> (0 < x * y) = (y < 0).
Admitted.

Lemma nmulr_rge0 x y : x < 0 -> (0 <= x * y) = (y <= 0).
Admitted.

Lemma nmulr_rlt0 x y : x < 0 -> (x * y < 0) = (0 < y).
Admitted.

Lemma nmulr_rle0 x y : x < 0 -> (x * y <= 0) = (0 <= y).
Admitted.

Lemma nmulr_lgt0 x y : x < 0 -> (0 < y * x) = (y < 0).
Admitted.

Lemma nmulr_lge0 x y : x < 0 -> (0 <= y * x) = (y <= 0).
Admitted.

Lemma nmulr_llt0 x y : x < 0 -> (y * x < 0) = (0 < y).
Admitted.

Lemma nmulr_lle0 x y : x < 0 -> (y * x <= 0) = (0 <= y).
Admitted.

Lemma mulr_ge0 x y : 0 <= x -> 0 <= y -> 0 <= x * y.
Admitted.

Lemma mulr_le0 x y : x <= 0 -> y <= 0 -> 0 <= x * y.
Admitted.

Lemma mulr_ge0_le0 x y : 0 <= x -> y <= 0 -> x * y <= 0.
Admitted.

Lemma mulr_le0_ge0 x y : x <= 0 -> 0 <= y -> x * y <= 0.
Admitted.

Lemma mulr_gt0 x y : 0 < x -> 0 < y -> 0 < x * y.
Admitted.

Lemma mulr_ge0_gt0 x y : 0 <= x -> 0 <= y -> (0 < x * y) = (0 < x) && (0 < y).
Admitted.

Lemma prodr_ge0 I r (P : pred I) (E : I -> R) :
  (forall i, P i -> 0 <= E i) -> 0 <= \prod_(i <- r | P i) E i.
Admitted.

Lemma prodr_gt0 I r (P : pred I) (E : I -> R) :
  (forall i, P i -> 0 < E i) -> 0 < \prod_(i <- r | P i) E i.
Admitted.

Lemma ler_prod I r (P : pred I) (E1 E2 : I -> R) :
    (forall i, P i -> 0 <= E1 i <= E2 i) ->
  \prod_(i <- r | P i) E1 i <= \prod_(i <- r | P i) E2 i.
Admitted.

Lemma ltr_prod I r (P : pred I) (E1 E2 : I -> R) :
    has P r -> (forall i, P i -> 0 <= E1 i < E2 i) ->
  \prod_(i <- r | P i) E1 i < \prod_(i <- r | P i) E2 i.
Admitted.

Lemma ltr_prod_nat (E1 E2 : nat -> R) (n m : nat) :
   (m < n)%N -> (forall i, (m <= i < n)%N -> 0 <= E1 i < E2 i) ->
  \prod_(m <= i < n) E1 i < \prod_(m <= i < n) E2 i.
Admitted.

Lemma realMr x y : x != 0 -> x \is real -> (x * y \is real) = (y \is real).
Admitted.

Lemma realrM x y : y != 0 -> y \is real -> (x * y \is real) = (x \is real).
Admitted.

Lemma realM : {in real &, forall x y, x * y \is real}.
Admitted.

Lemma realrMn x n : (n != 0)%N -> (x *+ n \is real) = (x \is real).
Admitted.

Lemma ger_pMl x y : 0 < y -> (x * y <= y) = (x <= 1).
Admitted.

Lemma gtr_pMl x y : 0 < y -> (x * y < y) = (x < 1).
Admitted.

Lemma ger_pMr x y : 0 < y -> (y * x <= y) = (x <= 1).
Admitted.

Lemma gtr_pMr x y : 0 < y -> (y * x < y) = (x < 1).
Admitted.

Lemma ler_pMl x y : 0 < y -> (y <= x * y) = (1 <= x).
Admitted.

Lemma ltr_pMl x y : 0 < y -> (y < x * y) = (1 < x).
Admitted.

Lemma ler_pMr x y : 0 < y -> (y <= y * x) = (1 <= x).
Admitted.

Lemma ltr_pMr x y : 0 < y -> (y < y * x) = (1 < x).
Admitted.

Lemma ger_nMl x y : y < 0 -> (x * y <= y) = (1 <= x).
Admitted.

Lemma gtr_nMl x y : y < 0 -> (x * y < y) = (1 < x).
Admitted.

Lemma ger_nMr x y : y < 0 -> (y * x <= y) = (1 <= x).
Admitted.

Lemma gtr_nMr x y : y < 0 -> (y * x < y) = (1 < x).
Admitted.

Lemma ler_nMl x y : y < 0 -> (y <= x * y) = (x <= 1).
Admitted.

Lemma ltr_nMl x y : y < 0 -> (y < x * y) = (x < 1).
Admitted.

Lemma ler_nMr x y : y < 0 -> (y <= y * x) = (x <= 1).
Admitted.

Lemma ltr_nMr x y : y < 0 -> (y < y * x) = (x < 1).
Admitted.

Lemma ler_peMl x y : 0 <= y -> 1 <= x -> y <= x * y.
Admitted.

Lemma ler_neMl x y : y <= 0 -> 1 <= x -> x * y <= y.
Admitted.

Lemma ler_peMr x y : 0 <= y -> 1 <= x -> y <= y * x.
Admitted.

Lemma ler_neMr x y : y <= 0 -> 1 <= x -> y * x <= y.
Admitted.

Lemma ler_piMl x y : 0 <= y -> x <= 1 -> x * y <= y.
Admitted.

Lemma ler_niMl x y : y <= 0 -> x <= 1 -> y <= x * y.
Admitted.

Lemma ler_piMr x y : 0 <= y -> x <= 1 -> y * x <= y.
Admitted.

Lemma ler_niMr x y : y <= 0 -> x <= 1 -> y <= y * x.
Admitted.

Lemma mulr_ile1 x y : 0 <= x -> 0 <= y -> x <= 1 -> y <= 1 -> x * y <= 1.
Admitted.

Lemma mulr_ilt1 x y : 0 <= x -> 0 <= y -> x < 1 -> y < 1 -> x * y < 1.
Admitted.

Definition mulr_ilte1 := (mulr_ile1, mulr_ilt1).

Lemma mulr_ege1 x y : 1 <= x -> 1 <= y -> 1 <= x * y.
Admitted.

Lemma mulr_egt1 x y : 1 < x -> 1 < y -> 1 < x * y.
Admitted.
Definition mulr_egte1 := (mulr_ege1, mulr_egt1).
Definition mulr_cp1 := (mulr_ilte1, mulr_egte1).

Lemma invr_gt0 x : (0 < x^-1) = (0 < x).
Admitted.

Lemma invr_ge0 x : (0 <= x^-1) = (0 <= x).
Admitted.

Lemma invr_lt0 x : (x^-1 < 0) = (x < 0).
Admitted.

Lemma invr_le0 x : (x^-1 <= 0) = (x <= 0).
Admitted.

Definition invr_gte0 := (invr_ge0, invr_gt0).
Definition invr_lte0 := (invr_le0, invr_lt0).

Lemma divr_ge0 x y : 0 <= x -> 0 <= y -> 0 <= x / y.
Admitted.

Lemma divr_gt0 x y : 0 < x -> 0 < y -> 0 < x / y.
Admitted.

Lemma realV : {mono (@GRing.inv R) : x / x \is real}.
Admitted.

Lemma exprn_ge0 n x : 0 <= x -> 0 <= x ^+ n.
Admitted.

Lemma realX n : {in real, forall x, x ^+ n \is real}.
Admitted.

Lemma exprn_gt0 n x : 0 < x -> 0 < x ^+ n.
Admitted.

Definition exprn_gte0 := (exprn_ge0, exprn_gt0).

Lemma exprn_ile1 n x : 0 <= x -> x <= 1 -> x ^+ n <= 1.
Admitted.

Lemma exprn_ilt1 n x : 0 <= x -> x < 1 -> x ^+ n < 1 = (n != 0).
Admitted.

Definition exprn_ilte1 := (exprn_ile1, exprn_ilt1).

Lemma exprn_ege1 n x : 1 <= x -> 1 <= x ^+ n.
Admitted.

Lemma exprn_egt1 n x : 1 < x -> 1 < x ^+ n = (n != 0).
Admitted.

Definition exprn_egte1 := (exprn_ege1, exprn_egt1).
Definition exprn_cp1 := (exprn_ilte1, exprn_egte1).

Lemma ler_iXnr x n : (0 < n)%N -> 0 <= x -> x <= 1 -> x ^+ n <= x.
Admitted.

Lemma ltr_iXnr x n : 0 < x -> x < 1 -> (x ^+ n < x) = (1 < n)%N.
Admitted.

Definition lter_iXnr := (ler_iXnr, ltr_iXnr).

Lemma ler_eXnr x n : (0 < n)%N -> 1 <= x -> x <= x ^+ n.
Admitted.

Lemma ltr_eXnr x n : 1 < x -> (x < x ^+ n) = (1 < n)%N.
Admitted.

Definition lter_eXnr := (ler_eXnr, ltr_eXnr).
Definition lter_Xnr := (lter_iXnr, lter_eXnr).

Lemma ler_wiXn2l x :
  0 <= x -> x <= 1 -> {homo GRing.exp x : m n / (n <= m)%N >-> m <= n}.
Admitted.

Lemma ler_weXn2l x : 1 <= x -> {homo GRing.exp x : m n / (m <= n)%N >-> m <= n}.
Admitted.

Lemma ieexprn_weq1 x n : 0 <= x -> (x ^+ n == 1) = ((n == 0) || (x == 1)).
Admitted.

Lemma ieexprIn x : 0 < x -> x != 1 -> injective (GRing.exp x).
Admitted.

Lemma ler_iXn2l x :
  0 < x -> x < 1 -> {mono GRing.exp x : m n / (n <= m)%N >-> m <= n}.
Admitted.

Lemma ltr_iXn2l x :
  0 < x -> x < 1 -> {mono GRing.exp x : m n / (n < m)%N >-> m < n}.
Admitted.

Definition lter_iXn2l := (ler_iXn2l, ltr_iXn2l).

Lemma ler_eXn2l x :
  1 < x -> {mono GRing.exp x : m n / (m <= n)%N >-> m <= n}.
Admitted.

Lemma ltr_eXn2l x :
  1 < x -> {mono (GRing.exp x) : m n / (m < n)%N >-> m < n}.
Admitted.

Definition lter_eXn2l := (ler_eXn2l, ltr_eXn2l).

Lemma ltrXn2r n x y : 0 <= x -> x < y -> x ^+ n < y ^+ n = (n != 0).
Admitted.

Lemma lerXn2r n : {in nneg & , {homo (@GRing.exp R)^~ n : x y / x <= y}}.
Admitted.

Definition lterXn2r := (lerXn2r, ltrXn2r).

Lemma ltr_wpXn2r n :
  (0 < n)%N -> {in nneg & , {homo (@GRing.exp R)^~ n : x y / x < y}}.
Admitted.

Lemma ler_pXn2r n :
  (0 < n)%N -> {in nneg & , {mono (@GRing.exp R)^~ n : x y / x <= y}}.
Admitted.

Lemma ltr_pXn2r n :
  (0 < n)%N -> {in nneg & , {mono (@GRing.exp R)^~ n : x y / x < y}}.
Admitted.

Definition lter_pXn2r := (ler_pXn2r, ltr_pXn2r).

Lemma pexpIrn n : (0 < n)%N -> {in nneg &, injective ((@GRing.exp R)^~ n)}.
Admitted.

Lemma expr_le1 n x : (0 < n)%N -> 0 <= x -> (x ^+ n <= 1) = (x <= 1).
Admitted.

Lemma expr_lt1 n x : (0 < n)%N -> 0 <= x -> (x ^+ n < 1) = (x < 1).
Admitted.

Definition expr_lte1 := (expr_le1, expr_lt1).

Lemma expr_ge1 n x : (0 < n)%N -> 0 <= x -> (1 <= x ^+ n) = (1 <= x).
Admitted.

Lemma expr_gt1 n x : (0 < n)%N -> 0 <= x -> (1 < x ^+ n) = (1 < x).
Admitted.

Definition expr_gte1 := (expr_ge1, expr_gt1).

Lemma pexpr_eq1 x n : (0 < n)%N -> 0 <= x -> (x ^+ n == 1) = (x == 1).
Admitted.

Lemma pexprn_eq1 x n : 0 <= x -> (x ^+ n == 1) = (n == 0) || (x == 1).
Admitted.

Lemma eqrXn2 n x y :
  (0 < n)%N -> 0 <= x -> 0 <= y -> (x ^+ n == y ^+ n) = (x == y).
Admitted.

Lemma sqrp_eq1 x : 0 <= x -> (x ^+ 2 == 1) = (x == 1).
Admitted.

Lemma sqrn_eq1 x : x <= 0 -> (x ^+ 2 == 1) = (x == -1).
Admitted.

Lemma ler_sqr : {in nneg &, {mono (fun x => x ^+ 2) : x y / x <= y}}.
Admitted.

Lemma ltr_sqr : {in nneg &, {mono (fun x => x ^+ 2) : x y / x < y}}.
Admitted.

Lemma ler_pV2 :
  {in [pred x in GRing.unit | 0 < x] &, {mono (@GRing.inv R) : x y /~ x <= y}}.
Admitted.

Lemma ler_nV2 :
  {in [pred x in GRing.unit | x < 0] &, {mono (@GRing.inv R) : x y /~ x <= y}}.
Admitted.

Lemma ltr_pV2 :
  {in [pred x in GRing.unit | 0 < x] &, {mono (@GRing.inv R) : x y /~ x < y}}.
Admitted.

Lemma ltr_nV2 :
  {in [pred x in GRing.unit | x < 0] &, {mono (@GRing.inv R) : x y /~ x < y}}.
Admitted.

Lemma invr_gt1 x : x \is a GRing.unit -> 0 < x -> (1 < x^-1) = (x < 1).
Admitted.

Lemma invr_ge1 x : x \is a GRing.unit -> 0 < x -> (1 <= x^-1) = (x <= 1).
Admitted.

Definition invr_gte1 := (invr_ge1, invr_gt1).

Lemma invr_le1 x (ux : x \is a GRing.unit) (hx : 0 < x) :
  (x^-1 <= 1) = (1 <= x).
Admitted.

Lemma invr_lt1 x (ux : x \is a GRing.unit) (hx : 0 < x) : (x^-1 < 1) = (1 < x).
Admitted.

Definition invr_lte1 := (invr_le1, invr_lt1).
Definition invr_cp1 := (invr_gte1, invr_lte1).

Lemma addr_min_max x y : min x y + max x y = x + y.
Admitted.

Lemma addr_max_min x y : max x y + min x y = x + y.
Admitted.

Lemma minr_to_max x y : min x y = x + y - max x y.
Admitted.

Lemma maxr_to_min x y : max x y = x + y - min x y.
Admitted.

Lemma real_oppr_max : {in real &, {morph -%R : x y / max x y >-> min x y : R}}.
Admitted.

Lemma real_oppr_min : {in real &, {morph -%R : x y / min x y >-> max x y : R}}.
Admitted.

Lemma real_addr_minl : {in real & real & real, @left_distributive R R +%R min}.
Admitted.

Lemma real_addr_minr : {in real & real & real, @right_distributive R R +%R min}.
Admitted.

Lemma real_addr_maxl : {in real & real & real, @left_distributive R R +%R max}.
Admitted.

Lemma real_addr_maxr : {in real & real & real, @right_distributive R R +%R max}.
Admitted.

Lemma minr_pMr x y z : 0 <= x -> x * min y z = min (x * y) (x * z).
Admitted.

Lemma maxr_pMr x y z : 0 <= x -> x * max y z = max (x * y) (x * z).
Admitted.

Lemma real_maxr_nMr x y z : x <= 0 -> y \is real -> z \is real ->
  x * max y z = min (x * y) (x * z).
Admitted.

Lemma real_minr_nMr x y z :  x <= 0 -> y \is real -> z \is real ->
  x * min y z = max (x * y) (x * z).
Admitted.

Lemma minr_pMl x y z : 0 <= x -> min y z * x = min (y * x) (z * x).
Admitted.

Lemma maxr_pMl x y z : 0 <= x -> max y z * x = max (y * x) (z * x).
Admitted.

Lemma real_minr_nMl x y z : x <= 0 -> y \is real -> z \is real ->
  min y z * x = max (y * x) (z * x).
Admitted.

Lemma real_maxr_nMl x y z : x <= 0 -> y \is real -> z \is real ->
  max y z * x = min (y * x) (z * x).
Admitted.

Lemma real_maxrN x : x \is real -> max x (- x) = `|x|.
Admitted.

Lemma real_maxNr x : x \is real -> max (- x) x = `|x|.
Admitted.

Lemma real_minrN x : x \is real -> min x (- x) = - `|x|.
Admitted.

Lemma real_minNr x : x \is real ->  min (- x) x = - `|x|.
Admitted.

Section RealDomainArgExtremum.

Context {I : finType} (i0 : I).
Context (P : pred I) (F : I -> R) (Pi0 : P i0).
Hypothesis F_real : {in P, forall i, F i \is real}.

Lemma real_arg_minP : extremum_spec <=%R P F [arg min_(i < i0 | P i) F i].
Admitted.

Lemma real_arg_maxP : extremum_spec >=%R P F [arg max_(i > i0 | P i) F i].
Admitted.

End RealDomainArgExtremum.

Lemma real_ler_norm x : x \is real -> x <= `|x|.
Admitted.

Section NormedZmoduleTheory.

Variable V : normedZmodType R.
Implicit Types (u v w : V).

Lemma normr_real v : `|v| \is real.
Admitted.
Hint Resolve normr_real : core.

Lemma ler_norm_sum I r (G : I -> V) (P : pred I):
  `|\sum_(i <- r | P i) G i| <= \sum_(i <- r | P i) `|G i|.
Admitted.

Lemma ler_normB v w : `|v - w| <= `|v| + `|w|.
Admitted.

Lemma ler_distD u v w : `|v - w| <= `|v - u| + `|u - w|.
Admitted.

Lemma lerB_normD v w : `|v| - `|w| <= `|v + w|.
Admitted.

Lemma lerB_dist v w : `|v| - `|w| <= `|v - w|.
Admitted.

Lemma ler_dist_dist v w : `| `|v| - `|w| | <= `|v - w|.
Admitted.

Lemma ler_dist_normD v w : `| `|v| - `|w| | <= `|v + w|.
Admitted.

Lemma ler_nnorml v x : x < 0 -> `|v| <= x = false.
Admitted.

Lemma ltr_nnorml v x : x <= 0 -> `|v| < x = false.
Admitted.

Definition lter_nnormr := (ler_nnorml, ltr_nnorml).

End NormedZmoduleTheory.

Hint Extern 0 (is_true (norm _ \is real)) => apply: normr_real : core.

Lemma real_ler_norml x y : x \is real -> (`|x| <= y) = (- y <= x <= y).
Admitted.

Lemma real_ler_normlP x y :
  x \is real -> reflect ((-x <= y) * (x <= y)) (`|x| <= y).
Admitted.
Arguments real_ler_normlP {x y}.

Lemma real_eqr_norml x y :
  x \is real -> (`|x| == y) = ((x == y) || (x == -y)) && (0 <= y).
Admitted.

Lemma real_eqr_norm2 x y :
  x \is real -> y \is real -> (`|x| == `|y|) = (x == y) || (x == -y).
Admitted.

Lemma real_ltr_norml x y : x \is real -> (`|x| < y) = (- y < x < y).
Admitted.

Definition real_lter_norml := (real_ler_norml, real_ltr_norml).

Lemma real_ltr_normlP x y :
  x \is real -> reflect ((-x < y) * (x < y)) (`|x| < y).
Admitted.
Arguments real_ltr_normlP {x y}.

Lemma real_ler_normr x y : y \is real -> (x <= `|y|) = (x <= y) || (x <= - y).
Admitted.

Lemma real_ltr_normr x y : y \is real -> (x < `|y|) = (x < y) || (x < - y).
Admitted.

Definition real_lter_normr := (real_ler_normr, real_ltr_normr).

Lemma real_ltr_normlW x y : x \is real -> `|x| < y -> x < y.
Admitted.

Lemma real_ltrNnormlW x y : x \is real -> `|x| < y -> - y < x.
Admitted.

Lemma real_ler_normlW x y : x \is real -> `|x| <= y -> x <= y.
Admitted.

Lemma real_lerNnormlW x y : x \is real -> `|x| <= y -> - y <= x.
Admitted.

Lemma real_ler_distl x y e :
  x - y \is real -> (`|x - y| <= e) = (y - e <= x <= y + e).
Admitted.

Lemma real_ltr_distl x y e :
  x - y \is real -> (`|x - y| < e) = (y - e < x < y + e).
Admitted.

Definition real_lter_distl := (real_ler_distl, real_ltr_distl).

Lemma real_ltr_distlDr x y e : x - y \is real -> `|x - y| < e -> x < y + e.
Admitted.

Lemma real_ler_distlDr x y e : x - y \is real -> `|x - y| <= e -> x <= y + e.
Admitted.

Lemma real_ltr_distlCDr x y e : x - y \is real -> `|x - y| < e -> y < x + e.
Admitted.

Lemma real_ler_distlCDr x y e : x - y \is real -> `|x - y| <= e -> y <= x + e.
Admitted.

Lemma real_ltr_distlBl x y e : x - y \is real -> `|x - y| < e -> x - e < y.
Admitted.

Lemma real_ler_distlBl x y e : x - y \is real -> `|x - y| <= e -> x - e <= y.
Admitted.

Lemma real_ltr_distlCBl x y e : x - y \is real -> `|x - y| < e -> y - e < x.
Admitted.

Lemma real_ler_distlCBl x y e : x - y \is real -> `|x - y| <= e -> y - e <= x.
Admitted.

#[deprecated(since="mathcomp 2.3.0", note="use `ger0_def` instead")]
Lemma eqr_norm_id x : (`|x| == x) = (0 <= x).
Admitted.

#[deprecated(since="mathcomp 2.3.0", note="use `ler0_def` instead")]
Lemma eqr_normN x : (`|x| == - x) = (x <= 0).
Admitted.

Definition eqr_norm_idVN := =^~ (ger0_def, ler0_def).

Lemma real_exprn_even_ge0 n x : x \is real -> ~~ odd n -> 0 <= x ^+ n.
Admitted.

Lemma real_exprn_even_gt0 n x :
  x \is real -> ~~ odd n -> (0 < x ^+ n) = (n == 0)%N || (x != 0).
Admitted.

Lemma real_exprn_even_le0 n x :
  x \is real -> ~~ odd n -> (x ^+ n <= 0) = (n != 0) && (x == 0).
Admitted.

Lemma real_exprn_even_lt0 n x :
  x \is real -> ~~ odd n -> (x ^+ n < 0) = false.
Admitted.

Lemma real_exprn_odd_ge0 n x :
  x \is real -> odd n -> (0 <= x ^+ n) = (0 <= x).
Admitted.

Lemma real_exprn_odd_gt0 n x : x \is real -> odd n -> (0 < x ^+ n) = (0 < x).
Admitted.

Lemma real_exprn_odd_le0 n x : x \is real -> odd n -> (x ^+ n <= 0) = (x <= 0).
Admitted.

Lemma real_exprn_odd_lt0 n x : x \is real -> odd n -> (x ^+ n < 0) = (x < 0).
Admitted.

Lemma realEsqr x : (x \is real) = (0 <= x ^+ 2).
Admitted.

Lemma real_normK x : x \is real -> `|x| ^+ 2 = x ^+ 2.
Admitted.

Lemma normr_sign s : `|(-1) ^+ s : R| = 1.
Admitted.

Lemma normrMsign s x : `|(-1) ^+ s * x| = `|x|.
Admitted.

Lemma signr_gt0 (b : bool) : (0 < (-1) ^+ b :> R) = ~~ b.
Admitted.

Lemma signr_lt0 (b : bool) : ((-1) ^+ b < 0 :> R) = b.
Admitted.

Lemma signr_ge0 (b : bool) : (0 <= (-1) ^+ b :> R) = ~~ b.
Admitted.

Lemma signr_le0 (b : bool) : ((-1) ^+ b <= 0 :> R) = b.
Admitted.

Lemma signr_inj : injective (fun b : bool => (-1) ^+ b : R).
Admitted.

Lemma sgr_def x : sg x = (-1) ^+ (x < 0)%R *+ (x != 0).
Admitted.

Lemma neqr0_sign x : x != 0 -> (-1) ^+ (x < 0)%R = sgr x.
Admitted.

Lemma gtr0_sg x : 0 < x -> sg x = 1.
Admitted.

Lemma ltr0_sg x : x < 0 -> sg x = -1.
Admitted.

Lemma sgr0 : sg 0 = 0 :> R.
Admitted.
Lemma sgr1 : sg 1 = 1 :> R.
Admitted.
Lemma sgrN1 : sg (-1) = -1 :> R.
Admitted.
Definition sgrE := (sgr0, sgr1, sgrN1).

Lemma sqr_sg x : sg x ^+ 2 = (x != 0)%:R.
Admitted.

Lemma mulr_sg_eq1 x y : (sg x * y == 1) = (x != 0) && (sg x == y).
Admitted.

Lemma mulr_sg_eqN1 x y : (sg x * sg y == -1) = (x != 0) && (sg x == - sg y).
Admitted.

Lemma sgr_eq0 x : (sg x == 0) = (x == 0).
Admitted.

Lemma sgr_odd n x : x != 0 -> (sg x) ^+ n = (sg x) ^+ (odd n).
Admitted.

Lemma sgrMn x n : sg (x *+ n) = (n != 0)%:R * sg x.
Admitted.

Lemma sgr_nat n : sg n%:R = (n != 0)%:R :> R.
Admitted.

Lemma sgr_id x : sg (sg x) = sg x.
Admitted.

Lemma sgr_lt0 x : (sg x < 0) = (x < 0).
Admitted.

Lemma sgr_le0 x : (sgr x <= 0) = (x <= 0).
Admitted.

Lemma realEsign x : x \is real -> x = (-1) ^+ (x < 0)%R * `|x|.
Admitted.

Lemma realNEsign x : x \is real -> - x = (-1) ^+ (0 < x)%R * `|x|.
Admitted.

Lemma real_normrEsign (x : R) (xR : x \is real) : `|x| = (-1) ^+ (x < 0)%R * x.
Admitted.

#[deprecated(since="mathcomp 2.3.0", note="use `realEsign` instead")]
Lemma real_mulr_sign_norm x : x \is real -> (-1) ^+ (x < 0)%R * `|x| = x.
Admitted.

Lemma real_mulr_Nsign_norm x : x \is real -> (-1) ^+ (0 < x)%R * `|x| = - x.
Admitted.

Lemma realEsg x : x \is real -> x = sgr x * `|x|.
Admitted.

Lemma normr_sg x : `|sg x| = (x != 0)%:R.
Admitted.

Lemma sgr_norm x : sg `|x| = (x != 0)%:R.
Admitted.

Lemma leif_nat_r m n C : (m%:R <= n%:R ?= iff C :> R) = (m <= n ?= iff C)%N.
Admitted.

Lemma leifBLR x y z C : (x - y <= z ?= iff C) = (x <= z + y ?= iff C).
Admitted.

Lemma leifBRL x y z C : (x <= y - z ?= iff C) = (x + z <= y ?= iff C).
Admitted.

Lemma leifD x1 y1 C1 x2 y2 C2 :
    x1 <= y1 ?= iff C1 -> x2 <= y2 ?= iff C2 ->
  x1 + x2 <= y1 + y2 ?= iff C1 && C2.
Admitted.

Lemma leif_sum (I : finType) (P C : pred I) (E1 E2 : I -> R) :
    (forall i, P i -> E1 i <= E2 i ?= iff C i) ->
  \sum_(i | P i) E1 i <= \sum_(i | P i) E2 i ?= iff [forall (i | P i), C i].
Admitted.

Lemma leif_0_sum (I : finType) (P C : pred I) (E : I -> R) :
    (forall i, P i -> 0 <= E i ?= iff C i) ->
  0 <= \sum_(i | P i) E i ?= iff [forall (i | P i), C i].
Admitted.

Lemma real_leif_norm x : x \is real -> x <= `|x| ?= iff (0 <= x).
Admitted.

Lemma leif_pM x1 x2 y1 y2 C1 C2 :
    0 <= x1 -> 0 <= x2 -> x1 <= y1 ?= iff C1 -> x2 <= y2 ?= iff C2 ->
  x1 * x2 <= y1 * y2 ?= iff (y1 * y2 == 0) || C1 && C2.
Admitted.

Lemma leif_nM x1 x2 y1 y2 C1 C2 :
    y1 <= 0 -> y2 <= 0 -> x1 <= y1 ?= iff C1 -> x2 <= y2 ?= iff C2 ->
  y1 * y2 <= x1 * x2 ?= iff (x1 * x2 == 0) || C1 && C2.
Admitted.

Lemma leif_pprod (I : finType) (P C : pred I) (E1 E2 : I -> R) :
    (forall i, P i -> 0 <= E1 i) ->
    (forall i, P i -> E1 i <= E2 i ?= iff C i) ->
  let pi E := \prod_(i | P i) E i in
  pi E1 <= pi E2 ?= iff (pi E2 == 0) || [forall (i | P i), C i].
Admitted.

Lemma subr_lteifr0 C x y : (y - x < 0 ?<= if C) = (y < x ?<= if C).
Admitted.

Lemma subr_lteif0r C x y : (0 < y - x ?<= if C) = (x < y ?<= if C).
Admitted.

Definition subr_lteif0 := (subr_lteifr0, subr_lteif0r).

Lemma lteif01 C : 0 < 1 ?<= if C :> R.
Admitted.

Lemma lteifNl C x y : - x < y ?<= if C = (- y < x ?<= if C).
Admitted.

Lemma lteifNr C x y : x < - y ?<= if C = (y < - x ?<= if C).
Admitted.

Lemma lteif0Nr C x : 0 < - x ?<= if C = (x < 0 ?<= if C).
Admitted.

Lemma lteifNr0 C x : - x < 0 ?<= if C = (0 < x ?<= if C).
Admitted.

Lemma lteifN2 C : {mono -%R : x y /~ x < y ?<= if C :> R}.
Admitted.

Definition lteif_oppE := (lteif0Nr, lteifNr0, lteifN2).

Lemma lteifD2l C x : {mono +%R x : y z / y < z ?<= if C}.
Admitted.

Lemma lteifD2r C x : {mono +%R^~ x : y z / y < z ?<= if C}.
Admitted.

Definition lteifD2 := (lteifD2l, lteifD2r).

Lemma lteifBlDr C x y z : (x - y < z ?<= if C) = (x < z + y ?<= if C).
Admitted.

Lemma lteifBrDr C x y z : (x < y - z ?<= if C) = (x + z < y ?<= if C).
Admitted.

Definition lteifBDr := (lteifBlDr, lteifBrDr).

Lemma lteifBlDl C x y z : (x - y < z ?<= if C) = (x < y + z ?<= if C).
Admitted.

Lemma lteifBrDl C x y z : (x < y - z ?<= if C) = (z + x < y ?<= if C).
Admitted.

Definition lteifBDl := (lteifBlDl, lteifBrDl).

Lemma lteif_pM2l C x : 0 < x -> {mono *%R x : y z / y < z ?<= if C}.
Admitted.

Lemma lteif_pM2r C x : 0 < x -> {mono *%R^~ x : y z / y < z ?<= if C}.
Admitted.

Lemma lteif_nM2l C x : x < 0 -> {mono *%R x : y z /~ y < z ?<= if C}.
Admitted.

Lemma lteif_nM2r C x : x < 0 -> {mono *%R^~ x : y z /~ y < z ?<= if C}.
Admitted.

Lemma lteif_nnormr C x y : y < 0 ?<= if ~~ C -> (`|x| < y ?<= if C) = false.
Admitted.

Lemma real_lteifNE x y C : x \is Num.real -> y \is Num.real ->
  x < y ?<= if ~~ C = ~~ (y < x ?<= if C).
Admitted.

Lemma real_lteif_norml C x y :
  x \is Num.real ->
  (`|x| < y ?<= if C) = ((- y < x ?<= if C) && (x < y ?<= if C)).
Admitted.

Lemma real_lteif_normr C x y :
  y \is Num.real ->
  (x < `|y| ?<= if C) = ((x < y ?<= if C) || (x < - y ?<= if C)).
Admitted.

Lemma real_lteif_distl C x y e :
  x - y \is real ->
  (`|x - y| < e ?<= if C) = (y - e < x ?<= if C) && (x < y + e ?<= if C).
Admitted.

Lemma real_leif_mean_square_scaled x y :
  x \is real -> y \is real -> x * y *+ 2 <= x ^+ 2 + y ^+ 2 ?= iff (x == y).
Admitted.

Lemma real_leif_AGM2_scaled x y :
  x \is real -> y \is real -> x * y *+ 4 <= (x + y) ^+ 2 ?= iff (x == y).
Admitted.

Lemma leif_AGM_scaled (I : finType) (A : {pred I}) (E : I -> R) (n := #|A|) :
    {in A, forall i, 0 <= E i *+ n} ->
  \prod_(i in A) (E i *+ n) <= (\sum_(i in A) E i) ^+ n
                            ?= iff [forall i in A, forall j in A, E i == E j].
Admitted.

Implicit Type p : {poly R}.

Lemma poly_disk_bound p b : {ub | forall x, `|x| <= b -> `|p.[x]| <= ub}.
Admitted.

End NumDomainOperationTheory.

#[global] Hint Resolve lerN2 ltrN2 normr_real : core.
#[global] Hint Extern 0 (is_true (_%:R \is real)) => apply: realn : core.
#[global] Hint Extern 0 (is_true (0 \is real)) => apply: real0 : core.
#[global] Hint Extern 0 (is_true (1 \is real)) => apply: real1 : core.

Arguments ler_sqr {R} [x y].
Arguments ltr_sqr {R} [x y].
Arguments signr_inj {R} [x1 x2].
Arguments real_ler_normlP {R x y}.
Arguments real_ltr_normlP {R x y}.

Section NumDomainMonotonyTheoryForReals.
Local Open Scope order_scope.

Variables (R R' : numDomainType) (D : pred R) (f : R -> R') (f' : R -> nat).
Implicit Types (m n p : nat) (x y z : R) (u v w : R').

Lemma real_mono :
  {homo f : x y / x < y} -> {in real &, {mono f : x y / x <= y}}.
Admitted.

Lemma real_nmono :
  {homo f : x y /~ x < y} -> {in real &, {mono f : x y /~ x <= y}}.
Admitted.

Lemma real_mono_in :
    {in D &, {homo f : x y / x < y}} ->
  {in [pred x in D | x \is real] &, {mono f : x y / x <= y}}.
Admitted.

Lemma real_nmono_in :
    {in D &, {homo f : x y /~ x < y}} ->
  {in [pred x in D | x \is real] &, {mono f : x y /~ x <= y}}.
Admitted.

Lemma realn_mono : {homo f' : x y / x < y >-> (x < y)} ->
  {in real &, {mono f' : x y / x <= y >-> (x <= y)}}.
Admitted.

Lemma realn_nmono : {homo f' : x y / y < x >-> (x < y)} ->
  {in real &, {mono f' : x y / y <= x >-> (x <= y)}}.
Admitted.

Lemma realn_mono_in : {in D &, {homo f' : x y / x < y >-> (x < y)}} ->
  {in [pred x in D | x \is real] &, {mono f' : x y / x <= y >-> (x <= y)}}.
Admitted.

Lemma realn_nmono_in : {in D &, {homo f' : x y / y < x >-> (x < y)}} ->
  {in [pred x in D | x \is real] &, {mono f' : x y / y <= x >-> (x <= y)}}.
Admitted.

End NumDomainMonotonyTheoryForReals.

Section FinGroup.

Import GroupScope.

Variables (R : numDomainType) (gT : finGroupType).
Implicit Types G : {group gT}.

Lemma natrG_gt0 G : #|G|%:R > 0 :> R.
Admitted.

Lemma natrG_neq0 G : #|G|%:R != 0 :> R.
Admitted.

Lemma natr_indexg_gt0 G B : #|G : B|%:R > 0 :> R.
Admitted.

Lemma natr_indexg_neq0 G B : #|G : B|%:R != 0 :> R.
Admitted.

End FinGroup.

Section NumFieldTheory.

Variable F : numFieldType.
Implicit Types x y z t : F.

Lemma unitf_gt0 x : 0 < x -> x \is a GRing.unit.
Admitted.

Lemma unitf_lt0 x : x < 0 -> x \is a GRing.unit.
Admitted.

Lemma lef_pV2 : {in pos &, {mono (@GRing.inv F) : x y /~ x <= y}}.
Admitted.

Lemma lef_nV2 : {in neg &, {mono (@GRing.inv F) : x y /~ x <= y}}.
Admitted.

Lemma ltf_pV2 : {in pos &, {mono (@GRing.inv F) : x y /~ x < y}}.
Admitted.

Lemma ltf_nV2 : {in neg &, {mono (@GRing.inv F) : x y /~ x < y}}.
Admitted.

Definition ltef_pV2 := (lef_pV2, ltf_pV2).
Definition ltef_nV2 := (lef_nV2, ltf_nV2).

Lemma invf_pgt : {in pos &, forall x y, (x < y^-1) = (y < x^-1)}.
Admitted.

Lemma invf_pge : {in pos &, forall x y, (x <= y^-1) = (y <= x^-1)}.
Admitted.

Lemma invf_ngt : {in neg &, forall x y, (x < y^-1) = (y < x^-1)}.
Admitted.

Lemma invf_nge : {in neg &, forall x y, (x <= y^-1) = (y <= x^-1)}.
Admitted.

Lemma invf_gt1 x : 0 < x -> (1 < x^-1) = (x < 1).
Admitted.

Lemma invf_ge1 x : 0 < x -> (1 <= x^-1) = (x <= 1).
Admitted.

Definition invf_gte1 := (invf_ge1, invf_gt1).

Lemma invf_plt : {in pos &, forall x y, (x^-1 < y) = (y^-1 < x)}.
Admitted.

Lemma invf_ple : {in pos &, forall x y, (x^-1 <= y) = (y^-1 <= x)}.
Admitted.

Lemma invf_nlt : {in neg &, forall x y, (x^-1 < y) = (y^-1 < x)}.
Admitted.

Lemma invf_nle : {in neg &, forall x y, (x^-1 <= y) = (y^-1 <= x)}.
Admitted.

Lemma invf_le1 x : 0 < x -> (x^-1 <= 1) = (1 <= x).
Admitted.

Lemma invf_lt1 x : 0 < x -> (x^-1 < 1) = (1 < x).
Admitted.

Definition invf_lte1 := (invf_le1, invf_lt1).
Definition invf_cp1 := (invf_gte1, invf_lte1).

Lemma ler_pdivlMr z x y : 0 < z -> (x <= y / z) = (x * z <= y).
Admitted.

Lemma ltr_pdivlMr z x y : 0 < z -> (x < y / z) = (x * z < y).
Admitted.

Definition lter_pdivlMr := (ler_pdivlMr, ltr_pdivlMr).

Lemma ler_pdivrMr z x y : 0 < z -> (y / z <= x) = (y <= x * z).
Admitted.

Lemma ltr_pdivrMr z x y : 0 < z -> (y / z < x) = (y < x * z).
Admitted.

Definition lter_pdivrMr := (ler_pdivrMr, ltr_pdivrMr).

Lemma ler_pdivlMl z x y : 0 < z -> (x <= z^-1 * y) = (z * x <= y).
Admitted.

Lemma ltr_pdivlMl z x y : 0 < z -> (x < z^-1 * y) = (z * x < y).
Admitted.

Definition lter_pdivlMl := (ler_pdivlMl, ltr_pdivlMl).

Lemma ler_pdivrMl z x y : 0 < z -> (z^-1 * y <= x) = (y <= z * x).
Admitted.

Lemma ltr_pdivrMl z x y : 0 < z -> (z^-1 * y < x) = (y < z * x).
Admitted.

Definition lter_pdivrMl := (ler_pdivrMl, ltr_pdivrMl).

Lemma ler_ndivlMr z x y : z < 0 -> (x <= y / z) = (y <= x * z).
Admitted.

Lemma ltr_ndivlMr z x y : z < 0 -> (x < y / z) = (y < x * z).
Admitted.

Definition lter_ndivlMr := (ler_ndivlMr, ltr_ndivlMr).

Lemma ler_ndivrMr z x y : z < 0 -> (y / z <= x) = (x * z <= y).
Admitted.

Lemma ltr_ndivrMr z x y : z < 0 -> (y / z < x) = (x * z < y).
Admitted.

Definition lter_ndivrMr := (ler_ndivrMr, ltr_ndivrMr).

Lemma ler_ndivlMl z x y : z < 0 -> (x <= z^-1 * y) = (y <= z * x).
Admitted.

Lemma ltr_ndivlMl z x y : z < 0 -> (x < z^-1 * y) = (y < z * x).
Admitted.

Definition lter_ndivlMl := (ler_ndivlMl, ltr_ndivlMl).

Lemma ler_ndivrMl z x y : z < 0 -> (z^-1 * y <= x) = (z * x <= y).
Admitted.

Lemma ltr_ndivrMl z x y : z < 0 -> (z^-1 * y < x) = (z * x < y).
Admitted.

Definition lter_ndivrMl := (ler_ndivrMl, ltr_ndivrMl).

Lemma natf_div m d : (d %| m)%N -> (m %/ d)%:R = m%:R / d%:R :> F.
Admitted.

Lemma normfV : {morph (norm : F -> F) : x / x ^-1}.
Admitted.

Lemma normf_div : {morph (norm : F -> F) : x y / x / y}.
Admitted.

Lemma invr_sg x : (sg x)^-1 = sgr x.
Admitted.

Lemma sgrV x : sgr x^-1 = sgr x.
Admitted.

Lemma splitr x : x = x / 2%:R + x / 2%:R.
Admitted.

Lemma lteif_pdivlMr C z x y :
  0 < z -> x < y / z ?<= if C = (x * z < y ?<= if C).
Admitted.

Lemma lteif_pdivrMr C z x y :
  0 < z -> y / z < x ?<= if C = (y < x * z ?<= if C).
Admitted.

Lemma lteif_pdivlMl C z x y :
  0 < z -> x < z^-1 * y ?<= if C = (z * x < y ?<= if C).
Admitted.

Lemma lteif_pdivrMl C z x y :
  0 < z -> z^-1 * y < x ?<= if C = (y < z * x ?<= if C).
Admitted.

Lemma lteif_ndivlMr C z x y :
  z < 0 -> x < y / z ?<= if C = (y < x * z ?<= if C).
Admitted.

Lemma lteif_ndivrMr C z x y :
  z < 0 -> y / z < x ?<= if C = (x * z < y ?<= if C).
Admitted.

Lemma lteif_ndivlMl C z x y :
  z < 0 -> x < z^-1 * y ?<= if C = (y < z * x ?<= if C).
Admitted.

Lemma lteif_ndivrMl C z x y :
  z < 0 -> z^-1 * y < x ?<= if C = (z * x < y ?<= if C).
Admitted.

Local Notation mid x y := ((x + y) / 2).

Lemma midf_le x y : x <= y -> (x <= mid x y) * (mid x y <= y).
Admitted.

Lemma midf_lt x y : x < y -> (x < mid x y) * (mid x y < y).
Admitted.

Definition midf_lte := (midf_le, midf_lt).

Lemma ler_addgt0Pr x y : reflect (forall e, e > 0 -> x <= y + e) (x <= y).
Admitted.

Lemma ler_addgt0Pl x y : reflect (forall e, e > 0 -> x <= e + y) (x <= y).
Admitted.

Lemma lt_le a b : (forall x, x < a -> x < b) -> a <= b.
Admitted.

Lemma gt_ge a b : (forall x, b < x -> a < x) -> a <= b.
Admitted.

Lemma real_leif_mean_square x y :
  x \is real -> y \is real -> x * y <= mid (x ^+ 2) (y ^+ 2) ?= iff (x == y).
Admitted.

Lemma real_leif_AGM2 x y :
  x \is real -> y \is real -> x * y <= mid x y ^+ 2 ?= iff (x == y).
Admitted.

Lemma leif_AGM (I : finType) (A : {pred I}) (E : I -> F) :
    let n := #|A| in let mu := (\sum_(i in A) E i) / n%:R in
    {in A, forall i, 0 <= E i} ->
  \prod_(i in A) E i <= mu ^+ n
                     ?= iff [forall i in A, forall j in A, E i == E j].
Admitted.

Implicit Type p : {poly F}.
Lemma Cauchy_root_bound p : p != 0 -> {b | forall x, root p x -> `|x| <= b}.
Admitted.

Import GroupScope.

Lemma natf_indexg (gT : finGroupType) (G H : {group gT}) :
  H \subset G -> #|G : H|%:R = (#|G|%:R / #|H|%:R)%R :> F.
Admitted.

End NumFieldTheory.

Section RealDomainTheory.

Variable R : realDomainType.
Implicit Types x y z t : R.

Lemma num_real x : x \is real.
Admitted.
Hint Resolve num_real : core.

Lemma lerP x y : ler_xor_gt x y (min y x) (min x y) (max y x) (max x y)
                                `|x - y| `|y - x| (x <= y) (y < x).
Admitted.

Lemma ltrP x y : ltr_xor_ge x y (min y x) (min x y) (max y x) (max x y)
                                `|x - y| `|y - x| (y <= x) (x < y).
Admitted.

Lemma ltrgtP x y :
   comparer x y  (min y x) (min x y) (max y x) (max x y)
                 `|x - y| `|y - x| (y == x) (x == y)
                 (x >= y) (x <= y) (x > y) (x < y) .
Admitted.

Lemma ger0P x : ger0_xor_lt0 x (min 0 x) (min x 0) (max 0 x) (max x 0)
                                `|x| (x < 0) (0 <= x).
Admitted.

Lemma ler0P x : ler0_xor_gt0 x (min 0 x) (min x 0) (max 0 x) (max x 0)
                                `|x| (0 < x) (x <= 0).
Admitted.

Lemma ltrgt0P x : comparer0 x (min 0 x) (min x 0) (max 0 x) (max x 0)
  `|x| (0 == x) (x == 0) (x <= 0) (0 <= x) (x < 0) (x > 0).
Admitted.

Lemma mulr_lt0 x y :
  (x * y < 0) = [&& x != 0, y != 0 & (x < 0) (+) (y < 0)].
Admitted.

Lemma neq0_mulr_lt0 x y :
  x != 0 -> y != 0 -> (x * y < 0) = (x < 0) (+) (y < 0).
Admitted.

Lemma mulr_sign_lt0 (b : bool) x :
  ((-1) ^+ b * x < 0) = (x != 0) && (b (+) (x < 0)%R).
Admitted.

Lemma mulr_sign_norm x : (-1) ^+ (x < 0)%R * `|x| = x.
Admitted.

Lemma mulr_Nsign_norm x : (-1) ^+ (0 < x)%R * `|x| = - x.
Admitted.

Lemma numEsign x : x = (-1) ^+ (x < 0)%R * `|x|.
Admitted.

Lemma numNEsign x : -x = (-1) ^+ (0 < x)%R * `|x|.
Admitted.

Lemma normrEsign x : `|x| = (-1) ^+ (x < 0)%R * x.
Admitted.

End RealDomainTheory.

#[global] Hint Resolve num_real : core.

Section RealDomainOperations.

Notation "[ 'arg' 'min_' ( i < i0 | P ) F ]" :=
    (Order.arg_min (disp := ring_display) i0 (fun i => P%B) (fun i => F)) :
   ring_scope.

Notation "[ 'arg' 'min_' ( i < i0 'in' A ) F ]" :=
  [arg min_(i < i0 | i \in A) F] : ring_scope.

Notation "[ 'arg' 'min_' ( i < i0 ) F ]" := [arg min_(i < i0 | true) F] :
  ring_scope.

Notation "[ 'arg' 'max_' ( i > i0 | P ) F ]" :=
   (Order.arg_max (disp := ring_display) i0 (fun i => P%B) (fun i => F)) :
  ring_scope.

Notation "[ 'arg' 'max_' ( i > i0 'in' A ) F ]" :=
    [arg max_(i > i0 | i \in A) F] : ring_scope.

Notation "[ 'arg' 'max_' ( i > i0 ) F ]" := [arg max_(i > i0 | true) F] :
  ring_scope.

Variable R : realDomainType.
Implicit Types x y z t : R.
Let numR_real := @num_real R.
Hint Resolve numR_real : core.

Lemma sgr_cp0 x :
  ((sg x == 1) = (0 < x)) *
  ((sg x == -1) = (x < 0)) *
  ((sg x == 0) = (x == 0)).
Admitted.

Variant sgr_val x : R -> bool -> bool -> bool -> bool -> bool -> bool
  -> bool -> bool -> bool -> bool -> bool -> bool -> R -> Set :=
  | SgrNull of x = 0 : sgr_val x 0 true true true true false false
    true false false true false false 0
  | SgrPos of x > 0 : sgr_val x x false false true false false true
    false false true false false true 1
  | SgrNeg of x < 0 : sgr_val x (- x) false true false false true false
    false true false false true false (-1).

Lemma sgrP x :
  sgr_val x `|x| (0 == x) (x <= 0) (0 <= x) (x == 0) (x < 0) (0 < x)
                 (0 == sg x) (-1 == sg x) (1 == sg x)
                 (sg x == 0)  (sg x == -1) (sg x == 1) (sg x).
Admitted.

Lemma normrEsg x : `|x| = sg x * x.
Admitted.

Lemma numEsg x : x = sg x * `|x|.
Admitted.

#[deprecated(since="mathcomp 2.3.0", note="use `numEsg` instead")]
Lemma mulr_sg_norm x : sg x * `|x| = x.
Admitted.

Lemma sgrM x y : sg (x * y) = sg x * sg y.
Admitted.

Lemma sgrN x : sg (- x) = - sg x.
Admitted.

Lemma sgrX n x : sg (x ^+ n) = (sg x) ^+ n.
Admitted.

Lemma sgr_smul x y : sg (sg x * y) = sg x * sg y.
Admitted.

Lemma sgr_gt0 x : (sg x > 0) = (x > 0).
Admitted.

Lemma sgr_ge0 x : (sgr x >= 0) = (x >= 0).
Admitted.

Lemma ler_norm x : (x <= `|x|).
Admitted.

Lemma ler_norml x y : (`|x| <= y) = (- y <= x <= y).
Admitted.

Lemma ler_normlP x y : reflect ((- x <= y) * (x <= y)) (`|x| <= y).
Admitted.
Arguments ler_normlP {x y}.

Lemma eqr_norml x y : (`|x| == y) = ((x == y) || (x == -y)) && (0 <= y).
Admitted.

Lemma eqr_norm2 x y : (`|x| == `|y|) = (x == y) || (x == -y).
Admitted.

Lemma ltr_norml x y : (`|x| < y) = (- y < x < y).
Admitted.

Definition lter_norml := (ler_norml, ltr_norml).

Lemma ltr_normlP x y : reflect ((-x < y) * (x < y)) (`|x| < y).
Admitted.
Arguments ltr_normlP {x y}.

Lemma ltr_normlW x y : `|x| < y -> x < y.
Admitted.

Lemma ltrNnormlW x y : `|x| < y -> - y < x.
Admitted.

Lemma ler_normlW x y : `|x| <= y -> x <= y.
Admitted.

Lemma lerNnormlW x y : `|x| <= y -> - y <= x.
Admitted.

Lemma ler_normr x y : (x <= `|y|) = (x <= y) || (x <= - y).
Admitted.

Lemma ltr_normr x y : (x < `|y|) = (x < y) || (x < - y).
Admitted.

Definition lter_normr := (ler_normr, ltr_normr).

Lemma ler_distl x y e : (`|x - y| <= e) = (y - e <= x <= y + e).
Admitted.

Lemma ltr_distl x y e : (`|x - y| < e) = (y - e < x < y + e).
Admitted.

Definition lter_distl := (ler_distl, ltr_distl).

Lemma ltr_distlC x y e : (`|x - y| < e) = (x - e < y < x + e).
Admitted.

Lemma ler_distlC x y e : (`|x - y| <= e) = (x - e <= y <= x + e).
Admitted.

Definition lter_distlC := (ler_distlC, ltr_distlC).

Lemma ltr_distlDr x y e : `|x - y| < e -> x < y + e.
Admitted.

Lemma ler_distlDr x y e : `|x - y| <= e -> x <= y + e.
Admitted.

Lemma ltr_distlCDr x y e : `|x - y| < e -> y < x + e.
Admitted.

Lemma ler_distlCDr x y e : `|x - y| <= e -> y <= x + e.
Admitted.

Lemma ltr_distlBl x y e : `|x - y| < e -> x - e < y.
Admitted.

Lemma ler_distlBl x y e : `|x - y| <= e -> x - e <= y.
Admitted.

Lemma ltr_distlCBl x y e : `|x - y| < e -> y - e < x.
Admitted.

Lemma ler_distlCBl x y e : `|x - y| <= e -> y - e <= x.
Admitted.

Lemma exprn_even_ge0 n x : ~~ odd n -> 0 <= x ^+ n.
Admitted.

Lemma exprn_even_gt0 n x : ~~ odd n -> (0 < x ^+ n) = (n == 0)%N || (x != 0).
Admitted.

Lemma exprn_even_le0 n x : ~~ odd n -> (x ^+ n <= 0) = (n != 0) && (x == 0).
Admitted.

Lemma exprn_even_lt0 n x : ~~ odd n -> (x ^+ n < 0) = false.
Admitted.

Lemma exprn_odd_ge0 n x : odd n -> (0 <= x ^+ n) = (0 <= x).
Admitted.

Lemma exprn_odd_gt0 n x : odd n -> (0 < x ^+ n) = (0 < x).
Admitted.

Lemma exprn_odd_le0 n x : odd n -> (x ^+ n <= 0) = (x <= 0).
Admitted.

Lemma exprn_odd_lt0 n x : odd n -> (x ^+ n < 0) = (x < 0).
Admitted.

Lemma lteif_norml C x y :
  (`|x| < y ?<= if C) = (- y < x ?<= if C) && (x < y ?<= if C).
Admitted.

Lemma lteif_normr C x y :
  (x < `|y| ?<= if C) = (x < y ?<= if C) || (x < - y ?<= if C).
Admitted.

Lemma lteif_distl C x y e :
  (`|x - y| < e ?<= if C) = (y - e < x ?<= if C) && (x < y + e ?<= if C).
Admitted.

Lemma sqr_ge0 x : 0 <= x ^+ 2.
Admitted.

Lemma sqr_norm_eq1 x : (x ^+ 2 == 1) = (`|x| == 1).
Admitted.

Lemma leif_mean_square_scaled x y :
  x * y *+ 2 <= x ^+ 2 + y ^+ 2 ?= iff (x == y).
Admitted.

Section MinMax.

End MinMax.

Section PolyBounds.

End PolyBounds.

End RealDomainOperations.

Section RealField.

End RealField.

Section RealClosedFieldTheory.

End RealClosedFieldTheory.

Notation "z ^*" := (conj_op z) (at level 2, format "z ^*") : ring_scope.

Section ClosedFieldTheory.

End ClosedFieldTheory.

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

End Theory.

HB.factory Record IntegralDomain_isNumRing R of GRing.IntegralDomain R := {
  Rle : rel R;
  Rlt : rel R;
  norm : R -> R;
  normD     : forall x y, Rle (norm (x + y)) (norm x + norm y);
  addr_gt0  : forall x y, Rlt 0 x -> Rlt 0 y -> Rlt 0 (x + y);
  norm_eq0  : forall x, norm x = 0 -> x = 0;
  ger_total : forall x y, Rle 0 x -> Rle 0 y -> Rle x y || Rle y x;
  normM     : {morph norm : x y / x * y};
  le_def    : forall x y, (Rle x y) = (norm (y - x) == y - x);
  lt_def    : forall x y, (Rlt x y) = (y != x) && (Rle x y)
}.

HB.builders Context R of IntegralDomain_isNumRing R.
  Local Notation "x <= y" := (Rle x y) : ring_scope.
  Local Notation "x < y" := (Rlt x y) : ring_scope.
  Local Notation "`| x |" := (norm x) : ring_scope.

  Lemma ltrr x : x < x = false.
Admitted.

  Lemma lt_trans : transitive Rlt.
Admitted.

  Lemma le_def' x y : (x <= y) = (x == y) || (x < y).
Admitted.

  Lemma normrMn x n : `|x *+ n| = `|x| *+ n.
Admitted.

  Lemma normrN x : `|- x| = `|x|.
Admitted.

  HB.instance Definition _ :=
    Order.LtLe_isPOrder.Build ring_display R le_def' ltrr lt_trans.

  HB.instance Definition _ :=
    Zmodule_isNormed.Build _ R normD norm_eq0 normrMn normrN.

  HB.instance Definition _ :=
    isNumRing.Build R addr_gt0 ger_total normM le_def.
HB.end.

HB.factory Record NumDomain_isReal R of NumDomain R := {
  real : real_axiom R
}.

HB.builders Context R of NumDomain_isReal R.
  Lemma le_total : Order.POrder_isTotal ring_display R.
Admitted.

  HB.instance Definition _ := le_total.
HB.end.

HB.factory Record IntegralDomain_isLeReal R of GRing.IntegralDomain R := {
  Rle : rel R;
  Rlt : rel R;
  norm : R -> R;
  le0_add   : forall x y, Rle 0 x -> Rle 0 y -> Rle 0 (x + y);
  le0_mul   : forall x y, Rle 0 x -> Rle 0 y -> Rle 0 (x * y);
  le0_anti  : forall x, Rle 0 x -> Rle x 0 -> x = 0;
  sub_ge0   : forall x y, Rle 0 (y - x) = Rle x y;
  le0_total : forall x, Rle 0 x || Rle x 0;
  normN     : forall x, norm (- x) = norm x;
  ge0_norm  : forall x, Rle 0 x -> norm x = x;
  lt_def    : forall x y, Rlt x y = (y != x) && Rle x y;
}.

HB.builders Context R of IntegralDomain_isLeReal R.
  Local Notation le := Rle.
  Local Notation lt := Rlt.

  Local Notation "x <= y" := (le x y) : ring_scope.
  Local Notation "x < y" := (lt x y) : ring_scope.
  Local Notation "`| x |" := (norm x) : ring_scope.

  Fact lt0_add x y : 0 < x -> 0 < y -> 0 < x + y.
Admitted.

  Fact eq0_norm x : `|x| = 0 -> x = 0.
Admitted.

  Fact le_def x y : (x <= y) = (`|y - x| == y - x).
Admitted.

  Fact normM : {morph norm : x y / x * y}.
Admitted.

  Fact le_normD x y : `|x + y| <= `|x| + `|y|.
Admitted.

  Fact le_total : total le.
Admitted.

  HB.instance Definition _ := IntegralDomain_isNumRing.Build R
    le_normD lt0_add eq0_norm (in2W le_total) normM le_def lt_def.
HB.end.

HB.factory Record IntegralDomain_isLtReal R of GRing.IntegralDomain R := {
  Rlt : rel R;
  Rle : rel R;
  norm : R -> R;
  lt0_add   : forall x y, Rlt 0 x -> Rlt 0 y -> Rlt 0 (x + y);
  lt0_mul   : forall x y, Rlt 0 x -> Rlt 0 y -> Rlt 0 (x * y);
  lt0_ngt0  : forall x,  Rlt 0 x -> ~~ (Rlt x 0);
  sub_gt0   : forall x y, Rlt 0 (y - x) = Rlt x y;
  lt0_total : forall x, x != 0 -> Rlt 0 x || Rlt x 0;
  normN     : forall x, norm (- x) = norm x;
  ge0_norm  : forall x, Rle 0 x -> norm x = x;
  le_def    : forall x y, Rle x y = (x == y) || Rlt x y;
}.

HB.builders Context R of IntegralDomain_isLtReal R.
  Local Notation le := Rle.
  Local Notation lt := Rlt.

  Local Notation "x < y" := (lt x y) : ring_scope.
  Local Notation "x <= y" := (le x y) : ring_scope.
  Local Notation "`| x |" := (norm x) : ring_scope.

  Fact normM : {morph norm : x y / x * y}.
Admitted.

  Fact le_normD x y : `|x + y| <= `|x| + `|y|.
Admitted.

  Fact eq0_norm x : `|x| = 0 -> x = 0.
Admitted.

  Fact le_def' x y : (x <= y) = (`|y - x| == y - x).
Admitted.

  Fact lt_def x y : (x < y) = (y != x) && (x <= y).
Admitted.

  Fact le_total : total le.
Admitted.

  HB.instance Definition _ := IntegralDomain_isNumRing.Build R
    le_normD lt0_add eq0_norm (in2W le_total) normM le_def' lt_def.
HB.end.

Module Export Exports.
End Exports.

End Num.
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
Module mathcomp_DOT_algebra_DOT_ssrint_WRAPPED.
Module Export ssrint.

Import HB.structures.
Import mathcomp.ssreflect.ssreflect.
Import mathcomp.ssreflect.ssrfun.
Import mathcomp.ssreflect.ssrbool.
Import mathcomp.ssreflect.eqtype.
Import mathcomp.ssreflect.ssrnat.
Import mathcomp.ssreflect.choice.
Import mathcomp.ssreflect.order.
Import mathcomp.algebra.ssralg.
Import mathcomp.algebra.ssrnum.

Set Implicit Arguments.
Unset Strict Implicit.

Declare Scope int_scope.
Declare Scope rat_scope.
Delimit Scope int_scope with Z.
Local Open Scope int_scope.

Variant int : Set := Posz of nat | Negz of nat.
Notation "n %:Z" := (Posz n) (only parsing) : ring_scope.
Definition parse_int (x : Number.int) : int.
exact (match x with
  | Number.IntDecimal (Decimal.Pos u) => Posz (Nat.of_uint u)
  | Number.IntDecimal (Decimal.Neg u) => Negz (Nat.of_uint u).-1
  | Number.IntHexadecimal (Hexadecimal.Pos u) => Posz (Nat.of_hex_uint u)
  | Number.IntHexadecimal (Hexadecimal.Neg u) => Negz (Nat.of_hex_uint u).-1
  end).
Defined.
Definition print_int (x : int) : Number.int.
Admitted.

Number Notation int parse_int print_int : int_scope.
Definition natsum_of_int (m : int) : nat + nat.
Admitted.

Definition int_of_natsum (m : nat + nat) :=
  match m with inl p => Posz p | inr n => Negz n end.

Lemma natsum_of_intK : cancel natsum_of_int int_of_natsum.
Admitted.

HB.instance Definition _ := Countable.copy int (can_type natsum_of_intK).

Module Export intZmod.
Section intZmod.

Definition addz (m n : int) :=
  match m, n with
    | Posz m', Posz n' => Posz (m' + n')
    | Negz m', Negz n' => Negz (m' + n').+1
    | Posz m', Negz n' => if n' < m' then Posz (m' - n'.+1) else Negz (n' - m')
    | Negz n', Posz m' => if n' < m' then Posz (m' - n'.+1) else Negz (n' - m')
  end.

Definition oppz m :=
  match m with
    | Posz n => if n is (n'.+1)%N then Negz n' else Posz 0
    | Negz n => Posz (n.+1)%N
  end.

Lemma addzC : commutative addz.
Admitted.

Lemma add0z : left_id 0 addz.
Admitted.

Lemma addzA : associative addz.
Admitted.

Lemma addNz : left_inverse (0:int) oppz addz.
Admitted.

Definition Mixin := GRing.isZmodule.Build int addzA addzC add0z addNz.

End intZmod.
End intZmod.

HB.instance Definition _ := intZmod.Mixin.

Local Open Scope ring_scope.

Module Export intRing.
Section intRing.

Definition mulz (m n : int) :=
  match m, n with
    | Posz m', Posz n' => (m' * n')%N%:Z
    | Negz m', Negz n' => (m'.+1%N * n'.+1%N)%N%:Z
    | Posz m', Negz n' => - (m' * (n'.+1%N))%N%:Z
    | Negz n', Posz m' => - (m' * (n'.+1%N))%N%:Z
  end.

Lemma mulzC : commutative mulz.
Admitted.

Lemma mulzA : associative mulz.
Admitted.

Lemma mul1z : left_id 1%Z mulz.
Admitted.

Lemma mulz_addl : left_distributive mulz (+%R).
Admitted.

Lemma nonzero1z : 1%Z != 0.
Admitted.

Definition comMixin := GRing.Zmodule_isComRing.Build int
  mulzA mulzC mul1z mulz_addl nonzero1z.

End intRing.
End intRing.

HB.instance Definition _ := intRing.comMixin.

Module Export intUnitRing.
Section intUnitRing.
Implicit Types m n : int.

Definition unitz := [qualify a n : int | (n == 1) || (n == -1)].
Definition invz n : int.
Admitted.

Lemma mulVz : {in unitz, left_inverse 1%R invz *%R}.
Admitted.

Lemma unitzPl m n : n * m = 1 -> m \is a unitz.
Admitted.

Lemma invz_out : {in [predC unitz], invz =1 id}.
Admitted.

Lemma idomain_axiomz m n : m * n = 0 -> (m == 0) || (n == 0).
Admitted.

Definition comMixin := GRing.ComRing_hasMulInverse.Build int
  mulVz unitzPl invz_out.

End intUnitRing.
End intUnitRing.

HB.instance Definition _ := intUnitRing.comMixin.
HB.instance Definition _ := GRing.ComUnitRing_isIntegral.Build int
  intUnitRing.idomain_axiomz.

Definition absz m := match m with Posz p => p | Negz n => n.+1 end.

Module Export intOrdered.
Section intOrdered.

Local Notation normz m := (absz m)%:Z.

Definition lez m n :=
  match m, n with
    | Posz m', Posz n' => (m' <= n')%N
    | Posz m', Negz n' => false
    | Negz m', Posz n' => true
    | Negz m', Negz n' => (n' <= m')%N
  end.

Definition ltz m n :=
  match m, n with
    | Posz m', Posz n' => (m' < n')%N
    | Posz m', Negz n' => false
    | Negz m', Posz n' => true
    | Negz m', Negz n' => (n' < m')%N
  end.

Fact lez_add m n : lez 0 m -> lez 0 n -> lez 0 (m + n).
Admitted.

Fact lez_mul m n : lez 0 m -> lez 0 n -> lez 0 (m * n).
Admitted.

Fact lez_anti m : lez 0 m -> lez m 0 -> m = 0.
Admitted.

Lemma subz_ge0 m n : lez 0 (n - m) = lez m n.
Admitted.

Fact lez_total m n : lez m n || lez n m.
Admitted.

Fact normzN m : normz (- m) = normz m.
Admitted.

Fact gez0_norm m : lez 0 m -> normz m = m.
Admitted.

Fact ltz_def m n : (ltz m n) = (n != m) && (lez m n).
Admitted.

Definition Mixin := Num.IntegralDomain_isLeReal.Build int
  lez_add lez_mul lez_anti subz_ge0 (lez_total 0) normzN gez0_norm ltz_def.

End intOrdered.
End intOrdered.

HB.instance Definition _ := intOrdered.Mixin.

Definition intmul (R : zmodType) (x : R) (n : int) :=
  match n with
    | Posz n => (x *+ n)%R
    | Negz n => (x *- (n.+1))%R
  end.
Notation "x *~ n" := (intmul x n)
  (at level 40, left associativity, format "x  *~  n") : ring_scope.
Notation "n %:~R" := (1 *~ n)%R
  (at level 2, left associativity, format "n %:~R")  : ring_scope.

Definition exprz (R : unitRingType) (x : R) (n : int) :=
  match n with
    | Posz n => x ^+ n
    | Negz n => x ^- (n.+1)
  end.

Notation "x ^ n" := (exprz x n) : ring_scope.

Module Export IntDist.
Notation "`| m |" := (absz m) : nat_scope.
Coercion Posz : nat >-> int.

End IntDist.

End ssrint.

End mathcomp_DOT_algebra_DOT_ssrint_WRAPPED.
Module Export mathcomp.
Module Export algebra.
Module ssrint.
Include mathcomp_DOT_algebra_DOT_ssrint_WRAPPED.ssrint.
End ssrint.
Module Export rat.

Import HB.structures.
Import mathcomp.ssreflect.ssreflect.
Import mathcomp.ssreflect.ssrfun.
Import mathcomp.ssreflect.ssrbool.
Import mathcomp.ssreflect.eqtype.
Import mathcomp.ssreflect.ssrnat.
Import mathcomp.ssreflect.choice.
Import mathcomp.algebra.ssralg.
Import mathcomp.ssreflect.div.
Import mathcomp.algebra.ssrnum.
Import mathcomp.algebra.ssrint.
Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.

Local Open Scope ring_scope.

Record rat : Set := Rat {
  valq : (int * int);
  _ : (0 < valq.2) && coprime `|valq.1| `|valq.2|
}.
Delimit Scope rat_scope with Q.

Definition rat_isSub := Eval hnf in [isSub for valq].
HB.instance Definition _ := rat_isSub.
HB.instance Definition _ := [Countable of rat by <:].

Definition numq x := (valq x).1.
Definition denq x := (valq x).2.

Definition fracq_subdef x :=
  if x.2 != 0 then  let g := gcdn `|x.1| `|x.2| in
    ((-1) ^ ((x.2 < 0) (+) (x.1 < 0)) * (`|x.1| %/ g)%:Z, (`|x.2| %/ g)%:Z)
 else (0, 1).

Definition fracq_opt_subdef (x : int * int) :=
  if (0 < x.2) && coprime `|x.1| `|x.2| then x else fracq_subdef x.

Fact fracq_subproof x (y := fracq_opt_subdef x) :
  (0 < y.2) && (coprime `|y.1| `|y.2|).
Admitted.

Definition fracq '((n', d')) : rat :=
  match d', n' with
  | Posz 0 as d, _ as n => Rat (fracq_subproof (1, 0))
  | _ as d, Posz _ as n | _ as d, _ as n =>
     Rat (fracq_subproof (fracq_opt_subdef (n, d)))
  end.

Variant Irat_prf := Ifracq_subproof : (int * int) -> Irat_prf.
Variant Irat := IRat : (int * int) -> Irat_prf -> Irat.
Definition parse (x : Number.number) : option Irat.
exact (let parse_pos i f :=
    let nf := Decimal.nb_digits f in
    let d := (10 ^ nf)%nat in
    let n := (Nat.of_uint i * d + Nat.of_uint f)%nat in
    valq (fracq (Posz n, Posz d)) in
  let parse i f :=
    match i with
    | Decimal.Pos i => parse_pos i f
    | Decimal.Neg i => let (n, d) := parse_pos i f in ((- n)%R, d)
    end in
  match x with
  | Number.Decimal (Decimal.Decimal i f) =>
      let nd := parse i f in
      Some (IRat nd (Ifracq_subproof nd))
  | Number.Decimal (Decimal.DecimalExp _ _ _) => None
  | Number.Hexadecimal _ => None
  end).
Defined.
Definition print (r : Irat) : option Number.number.
Admitted.

Number Notation rat parse print (via Irat
  mapping [Rat => IRat, fracq_subproof => Ifracq_subproof])
  : rat_scope.

Definition zeroq := 0%Q.
Definition oneq := 1%Q.

Definition addq_subdef (x y : int * int) :=
  let: (x1, x2) := x in
  let: (y1, y2) := y in
  match x2, y2 with
    | Posz 1, Posz 1   =>
        match x1, y1 with
        | Posz 0, _ => (y1, 1)
        | _, Posz 0 => (x1, 1)
        | Posz n, Posz 1 => (Posz n.+1, 1)
        | Posz 1, Posz n => (Posz n.+1, 1)
        | _, _ => (x1 + y1, 1)
        end
    | Posz 1, _  => (x1 * y2 + y1, y2)
    | _, Posz 1  => (x1 + y1 * x2, x2)
    | _, _       => (x1 * y2 + y1 * x2, x2 * y2)
  end.
Definition addq '(Rat x xP) '(Rat y yP) := fracq (addq_subdef x y).

Definition oppq_subdef (x : int * int) := (- x.1, x.2).
Definition oppq '(Rat x xP) := fracq (oppq_subdef x).

Fact addqC : commutative addq.
Admitted.

Fact addqA : associative addq.
Admitted.

Fact add0q : left_id zeroq addq.
Admitted.

Fact addNq : left_inverse (fracq (0, 1)) oppq addq.
Admitted.

HB.instance Definition _ := GRing.isZmodule.Build rat addqA addqC add0q addNq.

Definition mulq_subdef (x y : int * int) :=
  let: (x1, x2) := x in
  let: (y1, y2) := y in
  match x2, y2 with
    | Posz 1, Posz 1 => (x1 * y1, 1)
    | Posz 1, _      => (x1 * y1, y2)
    | _, Posz 1      => (x1 * y1, x2)
    | _, _           => (x1 * y1, x2 * y2)
  end.
Definition mulq '(Rat x xP) '(Rat y yP) := fracq (mulq_subdef x y).

Definition invq_subdef (x : int * int) := (x.2, x.1).
Definition invq '(Rat x xP) := fracq (invq_subdef x).

Fact mulqC : commutative mulq.
Admitted.

Fact mulqA : associative mulq.
Admitted.

Fact mul1q : left_id oneq mulq.
Admitted.

Fact mulq_addl : left_distributive mulq addq.
Admitted.

Fact nonzero1q : oneq != zeroq.
Admitted.

HB.instance Definition _ :=
  GRing.Zmodule_isComRing.Build rat mulqA mulqC mul1q mulq_addl nonzero1q.

Fact mulVq x : x != 0 -> mulq (invq x) x = 1.
Admitted.

Fact invq0 : invq 0 = 0.
Admitted.

HB.instance Definition _ := GRing.ComRing_isField.Build rat mulVq invq0.

Section InRing.

Variable R : unitRingType.

Definition ratr x : R := (numq x)%:~R / (denq x)%:~R.

End InRing.

Section InPrealField.

Variable F : numFieldType.

Fact ratr_is_additive : additive (@ratr F).
Admitted.

Fact ratr_is_multiplicative : multiplicative (@ratr F).
Admitted.

HB.instance Definition _ := GRing.isAdditive.Build rat F (@ratr F)
  ratr_is_additive.
HB.instance Definition _ := GRing.isMultiplicative.Build rat F (@ratr F)
  ratr_is_multiplicative.

End InPrealField.

End rat.

Import HB.structures.
Import mathcomp.ssreflect.ssreflect.
Import mathcomp.ssreflect.ssrfun.
Import mathcomp.ssreflect.ssrbool.
Import mathcomp.ssreflect.eqtype.
Import mathcomp.ssreflect.choice.

Set Implicit Arguments.
Unset Strict Implicit.

Declare Scope quotient_scope.

Delimit Scope quotient_scope with qT.

HB.mixin Record isQuotient T (qT : Type) := {
  repr_of : qT -> T;
  quot_pi_subdef : T -> qT;
  repr_ofK_subproof : cancel repr_of quot_pi_subdef
}.

#[short(type="quotType")]
HB.structure Definition Quotient T := { qT of isQuotient T qT }.
Arguments repr_of [T qT] : rename.

HB.lock Definition repr := repr_of.

Section EquivRel.

Variable T : Type.

Variant equiv_class_of (equiv : rel T) :=
  EquivClass of reflexive equiv & symmetric equiv & transitive equiv.

Record equiv_rel := EquivRelPack {
  equiv :> rel T;
  _ : equiv_class_of equiv
}.

End EquivRel.

Section EncodingModuloRel.

Variables (D E : Type) (ED : E -> D) (DE : D -> E) (e : rel D).

Variant encModRel_class_of (r : rel D) :=
  EncModRelClassPack of (forall x, r x x -> r (ED (DE x)) x) & (r =2 e).

Record encModRel := EncModRelPack {
  enc_mod_rel :> rel D;
  _ : encModRel_class_of enc_mod_rel
}.

Variable r : encModRel.
Definition encoded_equiv : rel E.
Admitted.

End EncodingModuloRel.

Module Export EquivQuot.
Section EquivQuot.

Variables (D : Type) (C : choiceType) (CD : C -> D) (DC : D -> C).
Variables (eD : equiv_rel D) (encD : encModRel CD DC eD).
Notation eC := (encoded_equiv encD).

Definition canon x := choose (eC x) (x).

Record equivQuotient := EquivQuotient {
  erepr : C;
  _ : (frel canon) erepr erepr
}.

Definition type_of of (phantom (rel _) encD) := equivQuotient.

Lemma canon_id : forall x, (invariant canon canon) x.
Admitted.

Definition pi := locked (fun x => EquivQuotient (canon_id x)).

Lemma ereprK : cancel erepr pi.
Admitted.

Lemma equivQTP : cancel (CD \o erepr) (pi \o DC).
Admitted.

Local Notation qT := (type_of (Phantom (rel D) encD)).
#[export]
HB.instance Definition _ := isQuotient.Build D qT equivQTP.

#[export]
HB.instance Definition _ := Choice.copy qT (can_type ereprK).

End EquivQuot.

Notation "{eq_quot e }" :=
(@EquivQuot.type_of _ _ _ _ _ _ (Phantom (rel _) e)) : quotient_scope.

Section DefaultEncodingModuloRel.

Variables (D : choiceType) (r : rel D).

Definition defaultEncModRelClass :=
  @EncModRelClassPack D D id id r r (fun _ rxx => rxx) (fun _ _ => erefl _).

Canonical defaultEncModRel := EncModRelPack defaultEncModRelClass.

End DefaultEncodingModuloRel.

Import mathcomp.algebra.ssralg.
Import mathcomp.algebra.poly.

Section IntegralOverRing.

Definition integralOver (R K : ringType) (RtoK : R -> K) (z : K) :=
  exists2 p, p \is monic & root (map_poly RtoK p) z.

Variables (B R K : ringType) (BtoR : B -> R) (RtoK : {rmorphism R -> K}).

Lemma integral0 : integralOver RtoK 0.
admit.
Defined.

Lemma integral1 : integralOver RtoK 1.
admit.
Defined.

End IntegralOverRing.

Section IntegralOverComRing.

Variables (R K : comRingType) (RtoK : {rmorphism R -> K}).

Lemma integral_opp u : integralOver RtoK u -> integralOver RtoK (- u).
Admitted.

Lemma integral_add u v :
  integralOver RtoK u -> integralOver RtoK v -> integralOver RtoK (u + v).
Admitted.

Lemma integral_mul u v :
  integralOver RtoK u -> integralOver RtoK v -> integralOver RtoK (u * v).
Admitted.

End IntegralOverComRing.

Section IntegralOverField.

Variables (F E : fieldType) (FtoE : {rmorphism F -> E}).

Lemma integral_inv x : integralOver FtoE x -> integralOver FtoE x^-1.
Admitted.

End IntegralOverField.
Import mathcomp.ssreflect.ssrnat.
Import mathcomp.ssreflect.seq.
Import mathcomp.ssreflect.fintype.
Import mathcomp.ssreflect.bigop.

Import GRing.Theory.

Module Export ClosedFieldQE.
Section ClosedFieldQE.

Variables (F : fieldType) (F_closed : GRing.closed_field_axiom F).

Notation fF := (@GRing.formula F).
Notation tF := (@GRing.term F).
Definition polyF := seq tF.

Fixpoint sumpT (p q : polyF) :=
  match p, q with a :: p, b :: q => (a + b)%T :: sumpT p q
                | [::], q => q | p, [::] => p end.

Fixpoint mulpT (p q : polyF) :=
  if p isn't a :: p then [::]
  else sumpT [seq (a * x)%T | x <- q] (0%T :: mulpT p q).
Definition opppT : polyF -> polyF.
admit.
Defined.

Definition natmulpT n : polyF -> polyF := map (GRing.Mul n%:R%T).
Definition ex_elim_seq (ps : seq polyF) (q : polyF) : fF.
admit.
Defined.

Fixpoint abstrX (i : nat) (t : tF) :=
  match t with
    | 'X_n => if n == i then [::0; 1] else [::t]
    | - x => opppT (abstrX i x)
    | x + y => sumpT (abstrX i x) (abstrX i y)
    | x * y => mulpT (abstrX i x) (abstrX i y)
    | x *+ n => natmulpT n (abstrX i x)
    | x ^+ n => let ax := (abstrX i x) in iter n (mulpT ax) [::1]
    | _ => [::t]
  end%T.

Definition ex_elim (x : nat) (pqs : seq tF * seq tF) :=
  ex_elim_seq (map (abstrX x) pqs.1)
  (abstrX x (\big[GRing.Mul/1%T]_(q <- pqs.2) q)).

Lemma holds_ex_elim: GRing.valid_QE_proj ex_elim.
Admitted.

Lemma wf_ex_elim : GRing.wf_QE_proj ex_elim.
admit.
Defined.

End ClosedFieldQE.

HB.factory Record Field_isAlgClosed F of GRing.Field F := {
  solve_monicpoly : GRing.closed_field_axiom F;
}.

HB.builders Context F of Field_isAlgClosed F.
  HB.instance Definition _ := GRing.Field_QE_isDecField.Build F
    (@ClosedFieldQE.wf_ex_elim F)
    (ClosedFieldQE.holds_ex_elim solve_monicpoly).
  HB.instance Definition _ := GRing.DecField_isAlgClosed.Build F
    solve_monicpoly.
HB.end.

Theorem Fundamental_Theorem_of_Algebraics :
  {L : closedFieldType &
     {conj : {rmorphism L -> L} | involutive conj & ~ conj =1 id}}.
Admitted.
Import mathcomp.ssreflect.order.
Import mathcomp.algebra.ssrnum.
Local Open Scope ring_scope.

HB.factory Record isComplex L of GRing.ClosedField L  := {
  conj :  {rmorphism L -> L};
  conjK : involutive conj;
  conj_nt : ~ conj =1 id
}.

HB.builders Context L of isComplex L.

Definition sqrt x : L :=
  sval (sig_eqW (@solve_monicpoly _ 2%N (nth 0 [:: x]) isT)).

Lemma sqrtK x: sqrt x ^+ 2 = x.
Admitted.

Definition norm x := sqrt x * conj (sqrt x).

Lemma normK x : norm x ^+ 2 = x * conj x.
Admitted.

Lemma norm_eq0 x : norm x = 0 -> x = 0.
Admitted.

Lemma normM x y : norm (x * y) = norm x * norm y.
Admitted.

Definition le x y := norm (y - x) == y - x.
Definition lt x y := (y != x) && le x y.

Lemma pos_linear x y : le 0 x -> le 0 y -> le x y || le y x.
Admitted.

Lemma sposD x y : lt 0 x -> lt 0 y -> lt 0 (x + y).
Admitted.

Lemma normD x y : le (norm (x + y)) (norm x + norm y).
Admitted.

HB.instance Definition _ :=
  Num.IntegralDomain_isNumRing.Build L normD sposD norm_eq0
         pos_linear normM (fun x y => erefl (le x y))
                          (fun x y => erefl (lt x y)).

HB.instance Definition _ :=
  Num.NumField_isImaginary.Build L (sqrtK _) normK.

HB.end.

Module Type Specification.

Parameter type : Type.

Parameter conjMixin : Num.ClosedField type.

End Specification.

Module Implementation : Specification.

Definition L := tag Fundamental_Theorem_of_Algebraics.
Definition conjL : {rmorphism L -> L}.
Admitted.

Fact conjL_K : involutive conjL.
Admitted.

Fact conjL_nt : ~ conjL =1 id.
Admitted.
Definition L' : Type.
exact (eta L).
Defined.
HB.instance Definition _ := GRing.ClosedField.on L'.
HB.instance Definition _ := isComplex.Build L' conjL_K conjL_nt.

Notation cfType := (L' : closedFieldType).

Definition QtoL : {rmorphism _ -> _} := @ratr cfType.

Notation pQtoL := (map_poly QtoL).

Definition rootQtoL p_j :=
  if p_j.1 == 0 then 0 else
  (sval (closed_field_poly_normal (pQtoL p_j.1)))`_p_j.2.

Definition eq_root p_j q_k := rootQtoL p_j == rootQtoL q_k.

Fact eq_root_is_equiv : equiv_class_of eq_root.
Admitted.
Canonical eq_root_equiv := EquivRelPack eq_root_is_equiv.
Definition type : Type.
exact ({eq_quot eq_root}%qT).
Defined.
HB.instance Definition _ := Choice.on type.

Definition CtoL (u : type) := rootQtoL (repr u).

Fact CtoL_P u : integralOver QtoL (CtoL u).
Admitted.

Fact LtoC_subproof z : integralOver QtoL z -> {u | CtoL u = z}.
Admitted.

Definition LtoC z Az := sval (@LtoC_subproof z Az).

Definition zero := LtoC (integral0 _).
Definition add u v := LtoC (integral_add (CtoL_P u) (CtoL_P v)).
Definition opp u := LtoC (integral_opp (CtoL_P u)).

Fact addA : associative add.
Admitted.

Fact addC : commutative add.
Admitted.

Fact add0 : left_id zero add.
Admitted.

Fact addN : left_inverse zero opp add.
Admitted.

HB.instance Definition _ := GRing.isZmodule.Build type addA addC add0 addN.

Definition one := LtoC (integral1 _).
Definition mul u v := LtoC (integral_mul (CtoL_P u) (CtoL_P v)).
Definition inv u := LtoC (integral_inv (CtoL_P u)).

Fact mulA : associative mul.
Admitted.

Fact mulC : commutative mul.
Admitted.

Fact mul1 : left_id one mul.
Admitted.

Fact mulD : left_distributive mul +%R.
Admitted.

Fact one_nz : one != 0 :> type.
Admitted.

HB.instance Definition _ :=
  GRing.Zmodule_isComRing.Build type mulA mulC mul1 mulD one_nz.

Fact mulVf u :  u != 0 -> inv u * u = 1.
Admitted.

Fact inv0 : inv 0 = 0.
Admitted.

HB.instance Definition _ := GRing.ComRing_isField.Build type mulVf inv0.

Fact closedFieldAxiom : GRing.closed_field_axiom type.
Admitted.

HB.instance Definition _ := Field_isAlgClosed.Build type closedFieldAxiom.
Definition conj : {rmorphism type -> type}.
Admitted.

Lemma conjK : involutive conj.
Admitted.

Fact conj_nt : ~ conj =1 id.
Admitted.

HB.instance Definition _ := isComplex.Build type conjK conj_nt.

Definition conjMixin := Num.ClosedField.on type.

End Implementation.

#[export] HB.instance Definition _ := Implementation.conjMixin.
Import Implementation.

Notation algC := type.
Import mathcomp.ssreflect.finfun.
Import mathcomp.ssreflect.finset.
Import mathcomp.fingroup.fingroup.
Import GroupScope.
Import Num.Theory.
Local Open Scope ring_scope.

Section Defs.

Variable gT : finGroupType.

Definition is_class_fun (B : {set gT}) (f : {ffun gT -> algC}) :=
  [forall x, forall y in B, f (x ^ y) == f x] && (support f \subset B).

Variable B : {set gT}.
Local Notation G := <<B>>.

Record classfun : predArgType :=
  Classfun {cfun_val; _ : is_class_fun G cfun_val}.
Implicit Types phi psi xi : classfun.

Fact classfun_key : unit.
Admitted.
Definition Cfun := locked_with classfun_key (fun flag : nat => Classfun).

HB.instance Definition _ := [isSub for cfun_val].
HB.instance Definition _ := [Choice of classfun by <:].

Definition fun_of_cfun phi := cfun_val phi : gT -> algC.
Coercion fun_of_cfun : classfun >-> Funclass.

Fact cfun_zero_subproof : is_class_fun G (0 : {ffun _}).
Admitted.
Definition cfun_zero := Cfun 0 cfun_zero_subproof.

Fact cfun_comp_subproof f phi :
  f 0 = 0 -> is_class_fun G [ffun x => f (phi x)].
Admitted.
Definition cfun_comp f f0 phi := Cfun 0 (@cfun_comp_subproof f phi f0).
Definition cfun_opp := cfun_comp (oppr0 _).

Fact cfun_add_subproof phi psi : is_class_fun G [ffun x => phi x + psi x].
Admitted.
Definition cfun_add phi psi := Cfun 0 (cfun_add_subproof phi psi).

Definition cfun_scale a := cfun_comp (mulr0 a).

Fact cfun_addA : associative cfun_add.
Admitted.
Fact cfun_addC : commutative cfun_add.
Admitted.
Fact cfun_add0 : left_id cfun_zero cfun_add.
Admitted.
Fact cfun_addN : left_inverse cfun_zero cfun_opp cfun_add.
Admitted.

HB.instance Definition _ := GRing.isZmodule.Build classfun
  cfun_addA cfun_addC cfun_add0 cfun_addN.

Fact cfun_scaleA a b phi :
  cfun_scale a (cfun_scale b phi) = cfun_scale (a * b) phi.
Admitted.
Fact cfun_scale1 : left_id 1 cfun_scale.
Admitted.
Fact cfun_scaleDr : right_distributive cfun_scale +%R.
Admitted.
Fact cfun_scaleDl phi : {morph cfun_scale^~ phi : a b / a + b}.
Admitted.

HB.instance Definition _ := GRing.Zmodule_isLmodule.Build algC classfun
  cfun_scaleA cfun_scale1 cfun_scaleDr cfun_scaleDl.

Definition cfdot phi psi := #|B|%:R^-1 * \sum_(x in B) phi x * (psi x)^*.
Definition cfdotr psi phi := cfdot phi psi.

End Defs.

Notation "''CF' ( G )" := (classfun G) : type_scope.

Section DotProduct.

Variable (gT : finGroupType) (G : {group gT}).

Lemma cfdotr_is_linear xi : linear (cfdotr xi : 'CF(G) -> algC^o).
Proof.
move=> a phi psi; rewrite scalerAr -mulrDr; congr (_ * _).
