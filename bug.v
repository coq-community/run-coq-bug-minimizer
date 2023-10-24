
(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "-parsing" "-w" "+undeclared-scope" "-w" "+non-primitive-record" "-w" "-ambiguous-paths" "-w" "-redundant-canonical-projection" "-w" "-projection-no-head-constant" "-w" "-deprecated-native-compiler-option" "-native-compiler" "ondemand" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/analysis/classical" "mathcomp.classical" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/analysis/theories" "mathcomp.analysis" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/HB" "HB" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/elpi" "elpi" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/mathcomp" "mathcomp" "-top" "Top.bug_01") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 579 lines to 89 lines, then from 102 lines to 6293 lines, then from 6296 lines to 5465 lines, then from 5180 lines to 3737 lines *)
(* coqc version 8.19+alpha compiled with OCaml 4.14.1
   coqtop version 28f8ca807578:/builds/coq/coq/_build/default,(HEAD detached at e3a3a61) (e3a3a6145f06cd1cd15ecb40292486f2f4783b7d)
   Expected coqc runtime on this file: 10.976 sec *)
Require Coq.Init.Ltac.
Require Coq.Bool.Bool.
Require Coq.Floats.PrimFloat.
Require Coq.Logic.Epsilon.
Require Coq.Logic.FunctionalExtensionality.
Require Coq.NArith.BinNat.
Require Coq.NArith.Ndec.
Require Coq.Numbers.Cyclic.Int63.PrimInt63.
Require Coq.PArith.BinPos.
Require Coq.Reals.RIneq.
Require Coq.Reals.Ranalysis1.
Require Coq.Reals.Raxioms.
Require Coq.Reals.Rbasic_fun.
Require Coq.Reals.Rdefinitions.
Require Coq.Reals.Reals.
Require Coq.Reals.Rsqrt_def.
Require Coq.Reals.Rtrigo1.
Require Coq.Setoids.Setoid.
Require Coq.Strings.String.
Require Coq.ZArith.Zwf.
Require Coq.setoid_ring.Field_tac.
Require Coq.setoid_ring.Field_theory.
Require Coq.setoid_ring.Ring.
Require Coq.ssr.ssrbool.
Require Coq.ssr.ssreflect.
Require Coq.ssr.ssrfun.
Require mathcomp.ssreflect.ssrnotations.
Require mathcomp.ssreflect.ssreflect.
Require elpi.elpi.
Require mathcomp.ssreflect.ssrfun.
Require mathcomp.ssreflect.ssrbool.
Require mathcomp.ssreflect.eqtype.
Require HB.structures.
Require mathcomp.ssreflect.ssrnat.
Require mathcomp.ssreflect.seq.
Require mathcomp.ssreflect.choice.
Require mathcomp.ssreflect.div.
Require mathcomp.ssreflect.path.
Require mathcomp.ssreflect.fintype.
Require mathcomp.ssreflect.fingraph.
Require mathcomp.ssreflect.generic_quotient.
Require mathcomp.ssreflect.tuple.
Require mathcomp.ssreflect.finfun.
Require mathcomp.ssreflect.bigop.
Require mathcomp.ssreflect.finset.
Require mathcomp.ssreflect.prime.
Require mathcomp.ssreflect.ssrAC.
Require mathcomp.finmap.finmap.
Require mathcomp.fingroup.fingroup.
Require mathcomp.ssreflect.binomial.
Require mathcomp.ssreflect.order.
Require mathcomp.algebra.ssralg.
Require mathcomp.fingroup.morphism.
Require mathcomp.algebra.ring_quotient.
Require mathcomp.fingroup.perm.
Require mathcomp.algebra.countalg.
Require mathcomp.fingroup.automorphism.
Require mathcomp.algebra.poly.
Require mathcomp.fingroup.quotient.
Require mathcomp.ssreflect.all_ssreflect.
Require mathcomp.algebra.polydiv.
Require mathcomp.classical.boolp.
Require mathcomp.fingroup.action.
Require mathcomp.algebra.fraction.
Require mathcomp.algebra.ssrnum.
Require mathcomp.algebra.interval.
Require mathcomp.algebra.ssrint.
Require mathcomp.algebra.finalg.
Require mathcomp.algebra.zmodp.
Require mathcomp.algebra.rat.
Require mathcomp.algebra.matrix.
Require mathcomp.algebra.mxalgebra.
Require mathcomp.algebra.vector.
Require mathcomp.algebra.mxpoly.
Require mathcomp.classical.mathcomp_extra.
Require mathcomp.field.falgebra.
Require mathcomp.algebra.polyXY.
Require mathcomp.analysis.signed.
Require mathcomp.algebra.qpoly.
Require mathcomp.analysis.prodnormedzmodule.
Require mathcomp.field.fieldext.
Require mathcomp.algebra.intdiv.
Require mathcomp.classical.classical_sets.
Require mathcomp.algebra.all_algebra.
Require mathcomp.classical.functions.
Require mathcomp.analysis.constructive_ereal.
Require mathcomp.classical.cardinality.
Require mathcomp.classical.set_interval.
Require mathcomp.classical.fsbigop.
Require mathcomp.analysis.reals.
Require mathcomp.analysis.topology.
Require mathcomp.analysis.ereal.
Require mathcomp.analysis.Rstruct.

Module Export AdmitTactic.
Module Import LocalFalse.
Inductive False : Prop := .
End LocalFalse.
Axiom proof_admitted : False.
Import Coq.Init.Ltac.
Tactic Notation "admit" := abstract case proof_admitted.
End AdmitTactic.
Module mathcomp_DOT_analysis_DOT_normedtype_WRAPPED.
Module Export normedtype.
Import mathcomp.ssreflect.all_ssreflect.
Import mathcomp.algebra.ssralg.
Import mathcomp.algebra.ssrint.
Import mathcomp.algebra.ssrnum.
Import mathcomp.finmap.finmap.
Import mathcomp.algebra.matrix.
Import mathcomp.algebra.rat.
Import mathcomp.algebra.interval.
Import mathcomp.algebra.zmodp.
Import mathcomp.algebra.vector.
Import mathcomp.field.fieldext.
Import mathcomp.field.falgebra.
Import mathcomp.classical.mathcomp_extra.
Import mathcomp.classical.boolp.
Import mathcomp.classical.classical_sets.
Import mathcomp.classical.functions.
Import mathcomp.classical.cardinality.
Import mathcomp.classical.set_interval.
Import mathcomp.analysis.Rstruct.
Import mathcomp.analysis.ereal.
Import mathcomp.analysis.reals.
Import mathcomp.analysis.signed.
Import mathcomp.analysis.topology.
Import mathcomp.analysis.prodnormedzmodule.

Reserved Notation "f @`[ a , b ]" (at level 20, b at level 9,
  format "f  @`[ a ,  b ]").
Reserved Notation "f @`] a , b [" (at level 20, b at level 9,
  format "f  @`] a ,  b [").
Reserved Notation "x ^'+" (at level 3, format "x ^'+").
Reserved Notation "x ^'-" (at level 3, format "x ^'-").
Reserved Notation "+oo_ R" (at level 3, format "+oo_ R").
Reserved Notation "-oo_ R" (at level 3, format "-oo_ R").
Reserved Notation "[ 'bounded' E | x 'in' A ]"
  (at level 0, x name, format "[ 'bounded'  E  |  x  'in'  A ]").
Reserved Notation "k .-lipschitz_on f"
  (at level 2, format "k .-lipschitz_on  f").
Reserved Notation "k .-lipschitz_ A f"
  (at level 2, A at level 0, format "k .-lipschitz_ A  f").
Reserved Notation "k .-lipschitz f" (at level 2, format "k .-lipschitz  f").
Reserved Notation "[ 'lipschitz' E | x 'in' A ]"
  (at level 0, x name, format "[ 'lipschitz'  E  |  x  'in'  A ]").

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Import GRing.Theory.
Import Num.Def.
Import Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Definition pointed_of_zmodule (R : zmodType) : pointedType. exact (PointedType R 0). Defined.
Definition filtered_of_normedZmod (K : numDomainType) (R : normedZmodType K)
  : filteredType R. exact (Filtered.Pack (Filtered.Class
    (@Pointed.class (pointed_of_zmodule R))
    (nbhs_ball_ (ball_ (fun x => `|x|))))). Defined.

Section pseudoMetric_of_normedDomain.
Variables (K : numDomainType) (R : normedZmodType K).
Lemma ball_norm_center (x : R) (e : K) : 0 < e -> ball_ normr x e x.
Admitted.
Lemma ball_norm_symmetric (x y : R) (e : K) :
  ball_ normr x e y -> ball_ normr y e x.
Admitted.
Lemma ball_norm_triangle (x y z : R) (e1 e2 : K) :
  ball_ normr x e1 y -> ball_ normr y e2 z -> ball_ normr x (e1 + e2) z.
Admitted.
Definition pseudoMetric_of_normedDomain
  : PseudoMetric.mixin_of K (@entourage_ K R R (ball_ (fun x => `|x|))). exact (PseudoMetricMixin ball_norm_center ball_norm_symmetric ball_norm_triangle erefl). Defined.

Lemma nbhs_ball_normE :
  @nbhs_ball_ K R R (ball_ normr) = nbhs_ (entourage_ (ball_ normr)).
Admitted.
End pseudoMetric_of_normedDomain.

Lemma nbhsN (R : numFieldType) (x : R) : nbhs (- x) = -%R @ x.
Admitted.

Lemma nbhsNimage (R : numFieldType) (x : R) :
  nbhs (- x) = [set -%R @` A | A in nbhs x].
Admitted.

Lemma nearN (R : numFieldType) (x : R) (P : R -> Prop) :
  (\forall y \near - x, P y) <-> \near x, P (- x).
Admitted.

Lemma openN (R : numFieldType) (A : set R) :
  open A -> open [set - x | x in A].
Admitted.

Lemma closedN (R : numFieldType) (A : set R) :
  closed A -> closed [set - x | x in A].
Admitted.

Module PseudoMetricNormedZmodule.
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
Definition base2 T c := @PseudoMetric.Class _ _
    (@Uniform.Class _
      (@Topological.Class _
        (Filtered.Class
         (Pointed.Class (@base T c) (pointed_mixin c))
         (nbhs_mixin c))
        (topological_mixin c))
      (uniform_mixin c))
    (pseudoMetric_mixin c).
Local Coercion base2 : class_of >-> PseudoMetric.class_of.

Structure type (phR : phant R) :=
  Pack { sort; _ : class_of sort }.
Local Coercion sort : type >-> Sortclass.

Variables (phR : phant R) (T : Type) (cT : type phR).

Definition class := let: Pack _ c := cT return class_of cT in c.
Definition clone c of phant_id class c := @Pack phR T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).
Definition pack (b0 : Num.NormedZmodule.class_of R T) lm0 um0
  (m0 : @mixin_of (@Num.NormedZmodule.Pack R (Phant R) T b0) lm0 um0) :=
  fun bT (b : Num.NormedZmodule.class_of R T)
      & phant_id (@Num.NormedZmodule.class R (Phant R) bT) b =>
  fun uT (u : PseudoMetric.class_of R T) & phant_id (@PseudoMetric.class R uT) u =>
  fun (m : @mixin_of (Num.NormedZmodule.Pack _ b) _ u) & phant_id m m0 =>
  @Pack phR T (@Class T b u u u u u m).

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition zmodType := @GRing.Zmodule.Pack cT xclass.
Definition normedZmodType := @Num.NormedZmodule.Pack R phR cT xclass.
Definition pointedType := @Pointed.Pack cT xclass.
Definition filteredType := @Filtered.Pack cT cT xclass.
Definition topologicalType := @Topological.Pack cT xclass.
Definition uniformType := @Uniform.Pack cT xclass.
Definition pseudoMetricType := @PseudoMetric.Pack R cT xclass.
Definition pointed_zmodType := @GRing.Zmodule.Pack pointedType xclass.
Definition filtered_zmodType := @GRing.Zmodule.Pack filteredType xclass.
Definition topological_zmodType := @GRing.Zmodule.Pack topologicalType xclass.
Definition uniform_zmodType := @GRing.Zmodule.Pack uniformType xclass.
Definition pseudoMetric_zmodType := @GRing.Zmodule.Pack pseudoMetricType xclass.
Definition pointed_normedZmodType := @Num.NormedZmodule.Pack R phR pointedType xclass.
Definition filtered_normedZmodType := @Num.NormedZmodule.Pack R phR filteredType xclass.
Definition topological_normedZmodType := @Num.NormedZmodule.Pack R phR topologicalType xclass.
Definition uniform_normedZmodType := @Num.NormedZmodule.Pack R phR uniformType xclass.
Definition pseudoMetric_normedZmodType := @Num.NormedZmodule.Pack R phR pseudoMetricType xclass.

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> Num.NormedZmodule.class_of.
Coercion base2 : class_of >-> PseudoMetric.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion normedZmodType : type >-> Num.NormedZmodule.type.
Canonical normedZmodType.
Coercion pointedType : type >-> Pointed.type.
Canonical pointedType.
Coercion filteredType : type >-> Filtered.type.
Canonical filteredType.
Coercion topologicalType : type >-> Topological.type.
Canonical topologicalType.
Coercion uniformType : type >-> Uniform.type.
Canonical uniformType.
Coercion pseudoMetricType : type >-> PseudoMetric.type.
Canonical pseudoMetricType.
Canonical pointed_zmodType.
Canonical filtered_zmodType.
Canonical topological_zmodType.
Canonical uniform_zmodType.
Canonical pseudoMetric_zmodType.
Canonical pointed_normedZmodType.
Canonical filtered_normedZmodType.
Canonical topological_normedZmodType.
Canonical uniform_normedZmodType.
Canonical pseudoMetric_normedZmodType.
Notation pseudoMetricNormedZmodType R := (type (Phant R)).
Notation PseudoMetricNormedZmodType R T m :=
  (@pack _ (Phant R) T _ _ _ m _ _ idfun _ _ idfun _ idfun).
Notation "[ 'pseudoMetricNormedZmodType' R 'of' T 'for' cT ]" :=
  (@clone _ (Phant R) T cT _ idfun)
  (at level 0, format "[ 'pseudoMetricNormedZmodType'  R  'of'  T  'for'  cT ]") :
  form_scope.
Notation "[ 'pseudoMetricNormedZmodType' R 'of' T ]" :=
  (@clone _ (Phant R) T _ _ idfun)
  (at level 0, format "[ 'pseudoMetricNormedZmodType'  R  'of'  T ]") : form_scope.
End Exports.

End PseudoMetricNormedZmodule.
Export PseudoMetricNormedZmodule.Exports.

Section pseudoMetricnormedzmodule_lemmas.
Context {K : numDomainType} {V : pseudoMetricNormedZmodType K}.

Local Notation ball_norm := (ball_ (@normr K V)).

Lemma ball_normE : ball_norm = ball.
Admitted.

End pseudoMetricnormedzmodule_lemmas.

Section Nbhs'.
Context {R : numDomainType} {T : pseudoMetricType R}.

Lemma ex_ball_sig (x : T) (P : set T) :
  ~ (forall eps : {posnum R}, ~ (ball x eps%:num `<=` ~` P)) ->
    {d : {posnum R} | ball x d%:num `<=` ~` P}.
Admitted.

Lemma nbhsC (x : T) (P : set T) :
  ~ (forall eps : {posnum R}, ~ (ball x eps%:num `<=` ~` P)) ->
  nbhs x (~` P).
Admitted.

Lemma nbhsC_ball (x : T) (P : set T) :
  nbhs x (~` P) -> {d : {posnum R} | ball x d%:num `<=` ~` P}.
Admitted.

Lemma nbhs_ex (x : T) (P : T -> Prop) : nbhs x P ->
  {d : {posnum R} | forall y, ball x d%:num y -> P y}.
Admitted.

End Nbhs'.

Lemma coord_continuous {K : numFieldType} m n i j :
  continuous (fun M : 'M[K]_(m, n) => M i j).
Admitted.

Global Instance Proper_dnbhs_numFieldType (R : numFieldType) (x : R) :
  ProperFilter x^'.
Admitted.

#[global] Hint Extern 0 (ProperFilter _^') =>
  (apply: Proper_dnbhs_numFieldType) : typeclass_instances.
Definition pinfty_nbhs (R : numFieldType) : set (set R). exact (fun P => exists M, M \is Num.real /\ forall x, M < x -> P x). Defined.
Arguments pinfty_nbhs R : clear implicits.
Definition ninfty_nbhs (R : numFieldType) : set (set R). exact (fun P => exists M, M \is Num.real /\ forall x, x < M -> P x). Defined.
Arguments ninfty_nbhs R : clear implicits.

Notation "+oo_ R" := (pinfty_nbhs [numFieldType of R])
  (only parsing) : ring_scope.
Notation "-oo_ R" := (ninfty_nbhs [numFieldType of R])
  (only parsing) : ring_scope.

Notation "+oo" := (pinfty_nbhs _) : ring_scope.
Notation "-oo" := (ninfty_nbhs _) : ring_scope.

Section infty_nbhs_instances.
Context {R : numFieldType}.
Let R_topologicalType := [topologicalType of R].
Implicit Types r : R.

Global Instance proper_pinfty_nbhs : ProperFilter (pinfty_nbhs R).
Admitted.

Global Instance proper_ninfty_nbhs : ProperFilter (ninfty_nbhs R).
Admitted.

Lemma nbhs_pinfty_gt r : r \is Num.real -> \forall x \near +oo, r < x.
Admitted.

Lemma nbhs_pinfty_ge r : r \is Num.real -> \forall x \near +oo, r <= x.
Admitted.

Lemma nbhs_ninfty_lt r : r \is Num.real -> \forall x \near -oo, r > x.
Admitted.

Lemma nbhs_ninfty_le r : r \is Num.real -> \forall x \near -oo, r >= x.
Admitted.

Lemma nbhs_pinfty_real : \forall x \near +oo, x \is @Num.real R.
Admitted.

Lemma nbhs_ninfty_real : \forall x \near -oo, x \is @Num.real R.
Admitted.

Lemma pinfty_ex_gt (m : R) (A : set R) : m \is Num.real ->
  (\forall k \near +oo, A k) -> exists2 M, m < M & A M.
Admitted.

Lemma pinfty_ex_ge (m : R) (A : set R) : m \is Num.real ->
  (\forall k \near +oo, A k) -> exists2 M, m <= M & A M.
Admitted.

Lemma pinfty_ex_gt0 (A : set R) :
  (\forall k \near +oo, A k) -> exists2 M, M > 0 & A M.
Admitted.

Lemma near_pinfty_div2 (A : set R) :
  (\forall k \near +oo, A k) -> (\forall k \near +oo, A (k / 2)).
Admitted.

End infty_nbhs_instances.

#[global] Hint Extern 0 (is_true (_ < ?x)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: nbhs_pinfty_gt end : core.
#[global] Hint Extern 0 (is_true (_ <= ?x)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: nbhs_pinfty_ge end : core.
#[global] Hint Extern 0 (is_true (_ > ?x)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: nbhs_ninfty_lt end : core.
#[global] Hint Extern 0 (is_true (_ >= ?x)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: nbhs_ninfty_le end : core.
#[global] Hint Extern 0 (is_true (?x \is Num.real)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: nbhs_pinfty_real end : core.
#[global] Hint Extern 0 (is_true (?x \is Num.real)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: nbhs_ninfty_real end : core.

#[global] Hint Extern 0 (is_true (_ < ?x)%E) => match goal with
  H : x \is_near _ |- _ => near: x; exact: ereal_nbhs_pinfty_gt end : core.
#[global] Hint Extern 0 (is_true (_ <= ?x)%E) => match goal with
  H : x \is_near _ |- _ => near: x; exact: ereal_nbhs_pinfty_ge end : core.
#[global] Hint Extern 0 (is_true (_ > ?x)%E) => match goal with
  H : x \is_near _ |- _ => near: x; exact: ereal_nbhs_ninfty_lt end : core.
#[global] Hint Extern 0 (is_true (_ >= ?x)%E) => match goal with
  H : x \is_near _ |- _ => near: x; exact: ereal_nbhs_ninfty_le end : core.
#[global] Hint Extern 0 (is_true (fine ?x \is Num.real)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: ereal_nbhs_pinfty_real end : core.
#[global] Hint Extern 0 (is_true (fine ?x \is Num.real)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: ereal_nbhs_ninfty_real end : core.

Section cvg_infty_numField.
Context {R : numFieldType}.

Let cvgryPnum {F : set (set R)} {FF : Filter F} : [<->
  F --> +oo;
  forall A, A \is Num.real -> \forall x \near F, A <= x;
  forall A, A \is Num.real -> \forall x \near F, A < x;
  \forall A \near +oo, \forall x \near F, A < x;
  \forall A \near +oo, \forall x \near F, A <= x ].
Admitted.

Let cvgrNyPnum {F : set (set R)} {FF : Filter F} : [<->
  F --> -oo;
  forall A, A \is Num.real -> \forall x \near F, A >= x;
  forall A, A \is Num.real -> \forall x \near F, A > x;
  \forall A \near -oo, \forall x \near F, A > x;
  \forall A \near -oo, \forall x \near F, A >= x ].
Admitted.

Context {T} {F : set (set T)} {FF : Filter F}.
Implicit Types f : T -> R.

Lemma cvgryPger f :
  f @ F --> +oo <-> forall A, A \is Num.real -> \forall x \near F, A <= f x.
Admitted.

Lemma cvgryPgtr f :
  f @ F --> +oo <-> forall A, A \is Num.real -> \forall x \near F, A < f x.
Admitted.

Lemma cvgryPgty f :
  f @ F --> +oo <-> \forall A \near +oo, \forall x \near F, A < f x.
Admitted.

Lemma cvgryPgey f :
  f @ F --> +oo <-> \forall A \near +oo, \forall x \near F, A <= f x.
Admitted.

Lemma cvgrNyPler f :
  f @ F --> -oo <-> forall A, A \is Num.real -> \forall x \near F, A >= f x.
Admitted.

Lemma cvgrNyPltr f :
  f @ F --> -oo <-> forall A, A \is Num.real -> \forall x \near F, A > f x.
Admitted.

Lemma cvgrNyPltNy f :
  f @ F --> -oo <-> \forall A \near -oo, \forall x \near F, A > f x.
Admitted.

Lemma cvgrNyPleNy f :
  f @ F --> -oo <-> \forall A \near -oo, \forall x \near F, A >= f x.
Admitted.

Lemma cvgry_ger f :
  f @ F --> +oo -> forall A, A \is Num.real -> \forall x \near F, A <= f x.
Admitted.

Lemma cvgry_gtr f :
  f @ F --> +oo -> forall A, A \is Num.real -> \forall x \near F, A < f x.
Admitted.

Lemma cvgrNy_ler f :
  f @ F --> -oo -> forall A, A \is Num.real -> \forall x \near F, A >= f x.
Admitted.

Lemma cvgrNy_ltr f :
  f @ F --> -oo -> forall A, A \is Num.real -> \forall x \near F, A > f x.
Admitted.

Lemma cvgNry f : (- f @ F --> +oo) <-> (f @ F --> -oo).
Admitted.

Lemma cvgNrNy f : (- f @ F --> -oo) <-> (f @ F --> +oo).
Admitted.

End cvg_infty_numField.

Section cvg_infty_realField.
Context {R : realFieldType}.
Context {T} {F : set (set T)} {FF : Filter F} (f : T -> R).

Lemma cvgryPge : f @ F --> +oo <-> forall A, \forall x \near F, A <= f x.
Admitted.

Lemma cvgryPgt : f @ F --> +oo <-> forall A, \forall x \near F, A < f x.
Admitted.

Lemma cvgrNyPle : f @ F --> -oo <-> forall A, \forall x \near F, A >= f x.
Admitted.

Lemma cvgrNyPlt : f @ F --> -oo <-> forall A, \forall x \near F, A > f x.
Admitted.

Lemma cvgry_ge : f @ F --> +oo -> forall A, \forall x \near F, A <= f x.
Admitted.

Lemma cvgry_gt : f @ F --> +oo -> forall A, \forall x \near F, A < f x.
Admitted.

Lemma cvgrNy_le : f @ F --> -oo -> forall A, \forall x \near F, A >= f x.
Admitted.

Lemma cvgrNy_lt : f @ F --> -oo -> forall A, \forall x \near F, A > f x.
Admitted.

End cvg_infty_realField.

Lemma cvgrnyP {R : realType} {T} {F : set (set T)} {FF : Filter F} (f : T -> nat) :
   (((f n)%:R : R) @[n --> F] --> +oo) <-> (f @ F --> \oo).
Admitted.

Section ecvg_infty_numField.
Local Open Scope ereal_scope.

Context {R : numFieldType}.

Let cvgeyPnum {F : set (set \bar R)} {FF : Filter F} : [<->
  F --> +oo;
  forall A, A \is Num.real -> \forall x \near F, A%:E <= x;
  forall A, A \is Num.real -> \forall x \near F, A%:E < x;
  \forall A \near +oo%R, \forall x \near F, A%:E < x;
  \forall A \near +oo%R, \forall x \near F, A%:E <= x ].
Admitted.

Let cvgeNyPnum {F : set (set \bar R)} {FF : Filter F} : [<->
  F --> -oo;
  forall A, A \is Num.real -> \forall x \near F, A%:E >= x;
  forall A, A \is Num.real -> \forall x \near F, A%:E > x;
  \forall A \near -oo%R, \forall x \near F, A%:E > x;
  \forall A \near -oo%R, \forall x \near F, A%:E >= x ].
Admitted.

Context {T} {F : set (set T)} {FF : Filter F}.
Implicit Types (f : T -> \bar R) (u : T -> R).

Lemma cvgeyPger f :
  f @ F --> +oo <-> forall A, A \is Num.real -> \forall x \near F, A%:E <= f x.
Admitted.

Lemma cvgeyPgtr f :
  f @ F --> +oo <-> forall A, A \is Num.real -> \forall x \near F, A%:E < f x.
Admitted.

Lemma cvgeyPgty f :
  f @ F --> +oo <-> \forall A \near +oo%R, \forall x \near F, A%:E < f x.
Admitted.

Lemma cvgeyPgey f :
  f @ F --> +oo <-> \forall A \near +oo%R, \forall x \near F, A%:E <= f x.
Admitted.

Lemma cvgeNyPler f :
  f @ F --> -oo <-> forall A, A \is Num.real -> \forall x \near F, A%:E >= f x.
Admitted.

Lemma cvgeNyPltr f :
  f @ F --> -oo <-> forall A, A \is Num.real -> \forall x \near F, A%:E > f x.
Admitted.

Lemma cvgeNyPltNy f :
  f @ F --> -oo <-> \forall A \near -oo%R, \forall x \near F, A%:E > f x.
Admitted.

Lemma cvgeNyPleNy f :
  f @ F --> -oo <-> \forall A \near -oo%R, \forall x \near F, A%:E >= f x.
Admitted.

Lemma cvgey_ger f :
  f @ F --> +oo -> forall A, A \is Num.real -> \forall x \near F, A%:E <= f x.
Admitted.

Lemma cvgey_gtr f :
  f @ F --> +oo -> forall A, A \is Num.real -> \forall x \near F, A%:E < f x.
Admitted.

Lemma cvgeNy_ler f :
  f @ F --> -oo -> forall A, A \is Num.real -> \forall x \near F, A%:E >= f x.
Admitted.

Lemma cvgeNy_ltr f :
  f @ F --> -oo -> forall A, A \is Num.real -> \forall x \near F, A%:E > f x.
Admitted.

Lemma cvgNey f : (\- f @ F --> +oo) <-> (f @ F --> -oo).
Admitted.

Lemma cvgNeNy f : (\- f @ F --> -oo) <-> (f @ F --> +oo).
Admitted.

Lemma cvgeryP u : ((u x)%:E @[x --> F] --> +oo) <-> (u @ F --> +oo%R).
Admitted.

Lemma cvgerNyP u : ((u x)%:E @[x --> F] --> -oo) <-> (u @ F --> -oo%R).
Admitted.

End ecvg_infty_numField.

Section ecvg_infty_realField.
Local Open Scope ereal_scope.
Context {R : realFieldType}.
Context {T} {F : set (set T)} {FF : Filter F} (f : T -> \bar R).

Lemma cvgeyPge : f @ F --> +oo <-> forall A, \forall x \near F, A%:E <= f x.
Admitted.

Lemma cvgeyPgt : f @ F --> +oo <-> forall A, \forall x \near F, A%:E < f x.
Admitted.

Lemma cvgeNyPle : f @ F --> -oo <-> forall A, \forall x \near F, A%:E >= f x.
Admitted.

Lemma cvgeNyPlt : f @ F --> -oo <-> forall A, \forall x \near F, A%:E > f x.
Admitted.

Lemma cvgey_ge : f @ F --> +oo -> forall A, \forall x \near F, A%:E <= f x.
Admitted.

Lemma cvgey_gt : f @ F --> +oo -> forall A, \forall x \near F, A%:E < f x.
Admitted.

Lemma cvgeNy_le : f @ F --> -oo -> forall A, \forall x \near F, A%:E >= f x.
Admitted.

Lemma cvgeNy_lt : f @ F --> -oo -> forall A, \forall x \near F, A%:E > f x.
Admitted.

End ecvg_infty_realField.

Lemma cvgenyP {R : realType} {T} {F : set (set T)} {FF : Filter F} (f : T -> nat) :
   (((f n)%:R : R)%:E @[n --> F] --> +oo%E) <-> (f @ F --> \oo).
Admitted.

Module NormedModule.

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
Local Coercion base2 T (c : class_of T) : GRing.Lmodule.class_of K T. exact (@GRing.Lmodule.Class K T (base c) (lmodmixin c)). Defined.
Local Coercion mixin : class_of >-> mixin_of.

Structure type (phK : phant K) :=
  Pack { sort; _ : class_of sort }.
Local Coercion sort : type >-> Sortclass.

Variables (phK : phant K) (T : Type) (cT : type phK).

Definition class := let: Pack _ c := cT return class_of cT in c.
Definition clone c of phant_id class c := @Pack phK T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack b0 l0
                (m0 : @mixin_of K (@PseudoMetricNormedZmodule.Pack K (Phant K) T b0)
                                (GRing.Lmodule.scale l0)) :=
  fun bT b & phant_id (@PseudoMetricNormedZmodule.class K (Phant K) bT) b =>
  fun l & phant_id l0 l =>
  fun m & phant_id m0 m => Pack phK (@Class T b l m).

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition zmodType := @GRing.Zmodule.Pack cT xclass.
Definition normedZmodType := @Num.NormedZmodule.Pack K phK cT xclass.
Definition lmodType := @GRing.Lmodule.Pack K phK cT xclass.
Definition pointedType := @Pointed.Pack cT xclass.
Definition filteredType := @Filtered.Pack cT cT xclass.
Definition topologicalType := @Topological.Pack cT xclass.
Definition uniformType := @Uniform.Pack cT xclass.
Definition pseudoMetricType := @PseudoMetric.Pack K cT xclass.
Definition pseudoMetricNormedZmodType := @PseudoMetricNormedZmodule.Pack K phK cT xclass.
Definition pointed_lmodType := @GRing.Lmodule.Pack K phK pointedType xclass.
Definition filtered_lmodType := @GRing.Lmodule.Pack K phK filteredType xclass.
Definition topological_lmodType := @GRing.Lmodule.Pack K phK topologicalType xclass.
Definition uniform_lmodType := @GRing.Lmodule.Pack K phK uniformType xclass.
Definition pseudoMetric_lmodType := @GRing.Lmodule.Pack K phK pseudoMetricType xclass.
Definition normedZmod_lmodType := @GRing.Lmodule.Pack K phK normedZmodType xclass.
Definition pseudoMetricNormedZmod_lmodType := @GRing.Lmodule.Pack K phK pseudoMetricNormedZmodType xclass.
End ClassDef.

Module Export Exports.

Coercion base : class_of >-> PseudoMetricNormedZmodule.class_of.
Coercion base2 : class_of >-> GRing.Lmodule.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion normedZmodType : type >-> Num.NormedZmodule.type.
Canonical normedZmodType.
Coercion lmodType : type >-> GRing.Lmodule.type.
Canonical lmodType.
Coercion pointedType : type >-> Pointed.type.
Canonical pointedType.
Coercion filteredType : type >-> Filtered.type.
Canonical filteredType.
Coercion topologicalType : type >-> Topological.type.
Canonical topologicalType.
Coercion uniformType : type >-> Uniform.type.
Canonical uniformType.
Coercion pseudoMetricType : type >-> PseudoMetric.type.
Canonical pseudoMetricType.
Coercion pseudoMetricNormedZmodType : type >-> PseudoMetricNormedZmodule.type.
Canonical pseudoMetricNormedZmodType.
Canonical pointed_lmodType.
Canonical filtered_lmodType.
Canonical topological_lmodType.
Canonical uniform_lmodType.
Canonical pseudoMetric_lmodType.
Canonical normedZmod_lmodType.
Canonical pseudoMetricNormedZmod_lmodType.
Notation normedModType K := (type (Phant K)).
Notation NormedModType K T m := (@pack _ (Phant K) T _ _ m _ _ idfun _ idfun _ idfun).
Notation NormedModMixin := Mixin.
Notation "[ 'normedModType' K 'of' T 'for' cT ]" := (@clone _ (Phant K) T cT _ idfun)
  (at level 0, format "[ 'normedModType'  K  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'normedModType' K 'of' T ]" := (@clone _ (Phant K) T _ _ id)
  (at level 0, format "[ 'normedModType'  K  'of'  T ]") : form_scope.
End Exports.

End NormedModule.

Export NormedModule.Exports.

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
Canonical pseudoMetricNormedZmodType.
Canonical normedModType.
End Exports.

End regular_topology.
Export regular_topology.Exports.

Module Export numFieldNormedType.

Section realType.
Variable (R : realType).
Local Canonical real_lmodType := [lmodType R of R for [lmodType R of R^o]].
Local Canonical real_lalgType := [lalgType R of R for [lalgType R of R^o]].
Local Canonical real_algType := [algType R of R for [algType R of R^o]].
Local Canonical real_comAlgType := [comAlgType R of R].
Local Canonical real_unitAlgType := [unitAlgType R of R].
Local Canonical real_comUnitAlgType := [comUnitAlgType R of R].
Local Canonical real_vectType := [vectType R of R for [vectType R of R^o]].
Local Canonical real_FalgType := [FalgType R of R].
Local Canonical real_fieldExtType :=
  [fieldExtType R of R for [fieldExtType R of R^o]].
Local Canonical real_pseudoMetricNormedZmodType :=
  [pseudoMetricNormedZmodType R of R for [pseudoMetricNormedZmodType R of R^o]].
Local Canonical real_normedModType :=
  [normedModType R of R for [normedModType R of R^o]].
End realType.

Section rcfType.
Variable (R : rcfType).
Local Canonical rcf_lmodType := [lmodType R of R for [lmodType R of R^o]].
Local Canonical rcf_lalgType := [lalgType R of R for [lalgType R of R^o]].
Local Canonical rcf_algType := [algType R of R for [algType R of R^o]].
Local Canonical rcf_comAlgType := [comAlgType R of R].
Local Canonical rcf_unitAlgType := [unitAlgType R of R].
Local Canonical rcf_comUnitAlgType := [comUnitAlgType R of R].
Local Canonical rcf_vectType := [vectType R of R for [vectType R of R^o]].
Local Canonical rcf_FalgType := [FalgType R of R].
Local Canonical rcf_fieldExtType :=
  [fieldExtType R of R for [fieldExtType R of R^o]].
Local Canonical rcf_pseudoMetricNormedZmodType :=
  [pseudoMetricNormedZmodType R of R for [pseudoMetricNormedZmodType R of R^o]].
Local Canonical rcf_normedModType :=
  [normedModType R of R for [normedModType R of R^o]].
End rcfType.

Section archiFieldType.
Variable (R : archiFieldType).
Local Canonical archiField_lmodType :=
  [lmodType R of R for [lmodType R of R^o]].
Local Canonical archiField_lalgType :=
  [lalgType R of R for [lalgType R of R^o]].
Local Canonical archiField_algType := [algType R of R for [algType R of R^o]].
Local Canonical archiField_comAlgType := [comAlgType R of R].
Local Canonical archiField_unitAlgType := [unitAlgType R of R].
Local Canonical archiField_comUnitAlgType := [comUnitAlgType R of R].
Local Canonical archiField_vectType :=
  [vectType R of R for [vectType R of R^o]].
Local Canonical archiField_FalgType := [FalgType R of R].
Local Canonical archiField_fieldExtType :=
  [fieldExtType R of R for [fieldExtType R of R^o]].
Local Canonical archiField_pseudoMetricNormedZmodType :=
  [pseudoMetricNormedZmodType R of R for [pseudoMetricNormedZmodType R of R^o]].
Local Canonical archiField_normedModType :=
  [normedModType R of R for [normedModType R of R^o]].
End archiFieldType.

Section realFieldType.
Variable (R : realFieldType).
Local Canonical realField_lmodType := [lmodType R of R for [lmodType R of R^o]].
Local Canonical realField_lalgType := [lalgType R of R for [lalgType R of R^o]].
Local Canonical realField_algType := [algType R of R for [algType R of R^o]].
Local Canonical realField_comAlgType := [comAlgType R of R].
Local Canonical realField_unitAlgType := [unitAlgType R of R].
Local Canonical realField_comUnitAlgType := [comUnitAlgType R of R].
Local Canonical realField_vectType := [vectType R of R for [vectType R of R^o]].
Local Canonical realField_FalgType := [FalgType R of R].
Local Canonical realField_fieldExtType :=
  [fieldExtType R of R for [fieldExtType R of R^o]].
Local Canonical realField_pseudoMetricNormedZmodType :=
  [pseudoMetricNormedZmodType R of R for [pseudoMetricNormedZmodType R of R^o]].
Local Canonical realField_normedModType :=
  [normedModType R of R for [normedModType R of R^o]].
Definition lmod_latticeType := [latticeType of realField_lmodType].
Definition lmod_distrLatticeType := [distrLatticeType of realField_lmodType].
Definition lmod_orderType := [orderType of realField_lmodType].
Definition lmod_realDomainType := [realDomainType of realField_lmodType].
Definition lalg_latticeType := [latticeType of realField_lalgType].
Definition lalg_distrLatticeType := [distrLatticeType of realField_lalgType].
Definition lalg_orderType := [orderType of realField_lalgType].
Definition lalg_realDomainType := [realDomainType of realField_lalgType].
Definition alg_latticeType := [latticeType of realField_algType].
Definition alg_distrLatticeType := [distrLatticeType of realField_algType].
Definition alg_orderType := [orderType of realField_algType].
Definition alg_realDomainType := [realDomainType of realField_algType].
Definition comAlg_latticeType := [latticeType of realField_comAlgType].
Definition comAlg_distrLatticeType :=
  [distrLatticeType of realField_comAlgType].
Definition comAlg_orderType := [orderType of realField_comAlgType].
Definition comAlg_realDomainType := [realDomainType of realField_comAlgType].
Definition unitAlg_latticeType := [latticeType of realField_unitAlgType].
Definition unitAlg_distrLatticeType :=
  [distrLatticeType of realField_unitAlgType].
Definition unitAlg_orderType := [orderType of realField_unitAlgType].
Definition unitAlg_realDomainType := [realDomainType of realField_unitAlgType].
Definition comUnitAlg_latticeType := [latticeType of realField_comUnitAlgType].
Definition comUnitAlg_distrLatticeType :=
  [distrLatticeType of realField_comUnitAlgType].
Definition comUnitAlg_orderType := [orderType of realField_comUnitAlgType].
Definition comUnitAlg_realDomainType :=
  [realDomainType of realField_comUnitAlgType].
Definition vect_latticeType := [latticeType of realField_vectType].
Definition vect_distrLatticeType := [distrLatticeType of realField_vectType].
Definition vect_orderType := [orderType of realField_vectType].
Definition vect_realDomainType := [realDomainType of realField_vectType].
Definition Falg_latticeType := [latticeType of realField_FalgType].
Definition Falg_distrLatticeType := [distrLatticeType of realField_FalgType].
Definition Falg_orderType := [orderType of realField_FalgType].
Definition Falg_realDomainType := [realDomainType of realField_FalgType].
Definition fieldExt_latticeType := [latticeType of realField_fieldExtType].
Definition fieldExt_distrLatticeType :=
  [distrLatticeType of realField_fieldExtType].
Definition fieldExt_orderType := [orderType of realField_fieldExtType].
Definition fieldExt_realDomainType :=
  [realDomainType of realField_fieldExtType].
Definition pseudoMetricNormedZmod_latticeType :=
  [latticeType of realField_pseudoMetricNormedZmodType].
Definition pseudoMetricNormedZmod_distrLatticeType :=
  [distrLatticeType of realField_pseudoMetricNormedZmodType].
Definition pseudoMetricNormedZmod_orderType :=
  [orderType of realField_pseudoMetricNormedZmodType].
Definition pseudoMetricNormedZmod_realDomainType :=
  [realDomainType of realField_pseudoMetricNormedZmodType].
Definition normedMod_latticeType := [latticeType of realField_normedModType].
Definition normedMod_distrLatticeType :=
  [distrLatticeType of realField_normedModType].
Definition normedMod_orderType := [orderType of realField_normedModType].
Definition normedMod_realDomainType :=
  [realDomainType of realField_normedModType].
End realFieldType.

Section numClosedFieldType.
Variable (R : numClosedFieldType).
Local Canonical numClosedField_lmodType :=
  [lmodType R of R for [lmodType R of R^o]].
Local Canonical numClosedField_lalgType :=
  [lalgType R of R for [lalgType R of R^o]].
Local Canonical numClosedField_algType :=
  [algType R of R for [algType R of R^o]].
Local Canonical numClosedField_comAlgType := [comAlgType R of R].
Local Canonical numClosedField_unitAlgType := [unitAlgType R of R].
Local Canonical numClosedField_comUnitAlgType := [comUnitAlgType R of R].
Local Canonical numClosedField_vectType :=
  [vectType R of R for [vectType R of R^o]].
Local Canonical numClosedField_FalgType := [FalgType R of R].
Local Canonical numClosedField_fieldExtType :=
  [fieldExtType R of R for [fieldExtType R of R^o]].
Local Canonical numClosedField_pseudoMetricNormedZmodType :=
  [pseudoMetricNormedZmodType R of R for [pseudoMetricNormedZmodType R of R^o]].
Local Canonical numClosedField_normedModType :=
  [normedModType R of R for [normedModType R of R^o]].
Definition lmod_decFieldType := [decFieldType of numClosedField_lmodType].
Definition lmod_closedFieldType := [closedFieldType of numClosedField_lmodType].
Definition lalg_decFieldType := [decFieldType of numClosedField_lalgType].
Definition lalg_closedFieldType := [closedFieldType of numClosedField_lalgType].
Definition alg_decFieldType := [decFieldType of numClosedField_algType].
Definition alg_closedFieldType := [closedFieldType of numClosedField_algType].
Definition comAlg_decFieldType := [decFieldType of numClosedField_comAlgType].
Definition comAlg_closedFieldType :=
  [closedFieldType of numClosedField_comAlgType].
Definition unitAlg_decFieldType := [decFieldType of numClosedField_unitAlgType].
Definition unitAlg_closedFieldType :=
  [closedFieldType of numClosedField_unitAlgType].
Definition comUnitAlg_decFieldType :=
  [decFieldType of numClosedField_comUnitAlgType].
Definition comUnitAlg_closedFieldType :=
  [closedFieldType of numClosedField_comUnitAlgType].
Definition vect_decFieldType := [decFieldType of numClosedField_vectType].
Definition vect_closedFieldType := [closedFieldType of numClosedField_vectType].
Definition Falg_decFieldType := [decFieldType of numClosedField_FalgType].
Definition Falg_closedFieldType := [closedFieldType of numClosedField_FalgType].
Definition fieldExt_decFieldType :=
  [decFieldType of numClosedField_fieldExtType].
Definition fieldExt_closedFieldType :=
  [closedFieldType of numClosedField_fieldExtType].
Definition pseudoMetricNormedZmod_decFieldType :=
  [decFieldType of numClosedField_pseudoMetricNormedZmodType].
Definition pseudoMetricNormedZmod_closedFieldType :=
  [closedFieldType of numClosedField_pseudoMetricNormedZmodType].
Definition normedMod_decFieldType :=
  [decFieldType of numClosedField_normedModType].
Definition normedMod_closedFieldType :=
  [closedFieldType of numClosedField_normedModType].
End numClosedFieldType.

Section numFieldType.
Variable (R : numFieldType).
Local Canonical numField_lmodType := [lmodType R of R for [lmodType R of R^o]].
Local Canonical numField_lalgType := [lalgType R of R for [lalgType R of R^o]].
Local Canonical numField_algType := [algType R of R for [algType R of R^o]].
Local Canonical numField_comAlgType := [comAlgType R of R].
Local Canonical numField_unitAlgType := [unitAlgType R of R].
Local Canonical numField_comUnitAlgType := [comUnitAlgType R of R].
Local Canonical numField_vectType := [vectType R of R for [vectType R of R^o]].
Local Canonical numField_FalgType := [FalgType R of R].
Local Canonical numField_fieldExtType :=
  [fieldExtType R of R for [fieldExtType R of R^o]].
Local Canonical numField_pseudoMetricNormedZmodType :=
  [pseudoMetricNormedZmodType R of R for [pseudoMetricNormedZmodType R of R^o]].
Local Canonical numField_normedModType :=
  [normedModType R of R for [normedModType R of R^o]].
Definition lmod_porderType := [porderType of numField_lmodType].
Definition lmod_numDomainType := [numDomainType of numField_lmodType].
Definition lalg_pointedType := [pointedType of numField_lalgType].
Definition lalg_filteredType := [filteredType R of numField_lalgType].
Definition lalg_topologicalType := [topologicalType of numField_lalgType].
Definition lalg_uniformType := [uniformType of numField_lalgType].
Definition lalg_pseudoMetricType := [pseudoMetricType R of numField_lalgType].
Definition lalg_normedZmodType := [normedZmodType R of numField_lalgType].
Definition lalg_pseudoMetricNormedZmodType :=
  [pseudoMetricNormedZmodType R of numField_lalgType].
Definition lalg_normedModType := [normedModType R of numField_lalgType].
Definition lalg_porderType := [porderType of numField_lalgType].
Definition lalg_numDomainType := [numDomainType of numField_lalgType].
Definition alg_pointedType := [pointedType of numField_algType].
Definition alg_filteredType := [filteredType R of numField_algType].
Definition alg_topologicalType := [topologicalType of numField_algType].
Definition alg_uniformType := [uniformType of numField_algType].
Definition alg_pseudoMetricType := [pseudoMetricType R of numField_algType].
Definition alg_normedZmodType := [normedZmodType R of numField_algType].
Definition alg_pseudoMetricNormedZmodType :=
  [pseudoMetricNormedZmodType R of numField_algType].
Definition alg_normedModType := [normedModType R of numField_algType].
Definition alg_porderType := [porderType of numField_algType].
Definition alg_numDomainType := [numDomainType of numField_algType].
Definition comAlg_pointedType := [pointedType of numField_comAlgType].
Definition comAlg_filteredType := [filteredType R of numField_comAlgType].
Definition comAlg_topologicalType := [topologicalType of numField_comAlgType].
Definition comAlg_uniformType := [uniformType of numField_comAlgType].
Definition comAlg_pseudoMetricType :=
  [pseudoMetricType R of numField_comAlgType].
Definition comAlg_normedZmodType := [normedZmodType R of numField_comAlgType].
Definition comAlg_pseudoMetricNormedZmodType :=
  [pseudoMetricNormedZmodType R of numField_comAlgType].
Definition comAlg_normedModType := [normedModType R of numField_comAlgType].
Definition comAlg_porderType := [porderType of numField_comAlgType].
Definition comAlg_numDomainType := [numDomainType of numField_comAlgType].
Definition unitAlg_pointedType := [pointedType of numField_unitAlgType].
Definition unitAlg_filteredType := [filteredType R of numField_unitAlgType].
Definition unitAlg_topologicalType := [topologicalType of numField_unitAlgType].
Definition unitAlg_uniformType := [uniformType of numField_unitAlgType].
Definition unitAlg_pseudoMetricType :=
  [pseudoMetricType R of numField_unitAlgType].
Definition unitAlg_normedZmodType := [normedZmodType R of numField_unitAlgType].
Definition unitAlg_pseudoMetricNormedZmodType :=
  [pseudoMetricNormedZmodType R of numField_unitAlgType].
Definition unitAlg_normedModType := [normedModType R of numField_unitAlgType].
Definition unitAlg_porderType := [porderType of numField_unitAlgType].
Definition unitAlg_numDomainType := [numDomainType of numField_unitAlgType].
Definition comUnitAlg_pointedType := [pointedType of numField_comUnitAlgType].
Definition comUnitAlg_filteredType :=
  [filteredType R of numField_comUnitAlgType].
Definition comUnitAlg_topologicalType :=
  [topologicalType of numField_comUnitAlgType].
Definition comUnitAlg_uniformType := [uniformType of numField_comUnitAlgType].
Definition comUnitAlg_pseudoMetricType :=
  [pseudoMetricType R of numField_comUnitAlgType].
Definition comUnitAlg_normedZmodType :=
  [normedZmodType R of numField_comUnitAlgType].
Definition comUnitAlg_pseudoMetricNormedZmodType :=
  [pseudoMetricNormedZmodType R of numField_comUnitAlgType].
Definition comUnitAlg_normedModType :=
  [normedModType R of numField_comUnitAlgType].
Definition comUnitAlg_porderType := [porderType of numField_comUnitAlgType].
Definition comUnitAlg_numDomainType :=
  [numDomainType of numField_comUnitAlgType].
Definition vect_pointedType := [pointedType of numField_vectType].
Definition vect_filteredType := [filteredType R of numField_vectType].
Definition vect_topologicalType := [topologicalType of numField_vectType].
Definition vect_uniformType := [uniformType of numField_vectType].
Definition vect_pseudoMetricType := [pseudoMetricType R of numField_vectType].
Definition vect_normedZmodType := [normedZmodType R of numField_vectType].
Definition vect_pseudoMetricNormedZmodType :=
  [pseudoMetricNormedZmodType R of numField_vectType].
Definition vect_normedModType := [normedModType R of numField_vectType].
Definition vect_porderType := [porderType of numField_vectType].
Definition vect_numDomainType := [numDomainType of numField_vectType].
Definition Falg_pointedType := [pointedType of numField_FalgType].
Definition Falg_filteredType := [filteredType R of numField_FalgType].
Definition Falg_topologicalType := [topologicalType of numField_FalgType].
Definition Falg_uniformType := [uniformType of numField_FalgType].
Definition Falg_pseudoMetricType := [pseudoMetricType R of numField_FalgType].
Definition Falg_normedZmodType := [normedZmodType R of numField_FalgType].
Definition Falg_pseudoMetricNormedZmodType :=
  [pseudoMetricNormedZmodType R of numField_FalgType].
Definition Falg_normedModType := [normedModType R of numField_FalgType].
Definition Falg_porderType := [porderType of numField_FalgType].
Definition Falg_numDomainType := [numDomainType of numField_FalgType].
Definition fieldExt_pointedType := [pointedType of numField_fieldExtType].
Definition fieldExt_filteredType := [filteredType R of numField_fieldExtType].
Definition fieldExt_topologicalType :=
  [topologicalType of numField_fieldExtType].
Definition fieldExt_uniformType := [uniformType of numField_fieldExtType].
Definition fieldExt_pseudoMetricType :=
  [pseudoMetricType R of numField_fieldExtType].
Definition fieldExt_normedZmodType :=
  [normedZmodType R of numField_fieldExtType].
Definition fieldExt_pseudoMetricNormedZmodType :=
  [pseudoMetricNormedZmodType R of numField_fieldExtType].
Definition fieldExt_normedModType := [normedModType R of numField_fieldExtType].
Definition fieldExt_porderType := [porderType of numField_fieldExtType].
Definition fieldExt_numDomainType := [numDomainType of numField_fieldExtType].
Definition pseudoMetricNormedZmod_ringType :=
  [ringType of numField_pseudoMetricNormedZmodType].
Definition pseudoMetricNormedZmod_comRingType :=
  [comRingType of numField_pseudoMetricNormedZmodType].
Definition pseudoMetricNormedZmod_unitRingType :=
  [unitRingType of numField_pseudoMetricNormedZmodType].
Definition pseudoMetricNormedZmod_comUnitRingType :=
  [comUnitRingType of numField_pseudoMetricNormedZmodType].
Definition pseudoMetricNormedZmod_idomainType :=
  [idomainType of numField_pseudoMetricNormedZmodType].
Definition pseudoMetricNormedZmod_fieldType :=
  [fieldType of numField_pseudoMetricNormedZmodType].
Definition pseudoMetricNormedZmod_porderType :=
  [porderType of numField_pseudoMetricNormedZmodType].
Definition pseudoMetricNormedZmod_numDomainType :=
  [numDomainType of numField_pseudoMetricNormedZmodType].
Definition normedMod_ringType := [ringType of numField_normedModType].
Definition normedMod_comRingType := [comRingType of numField_normedModType].
Definition normedMod_unitRingType := [unitRingType of numField_normedModType].
Definition normedMod_comUnitRingType :=
  [comUnitRingType of numField_normedModType].
Definition normedMod_idomainType := [idomainType of numField_normedModType].
Definition normedMod_fieldType := [fieldType of numField_normedModType].
Definition normedMod_porderType := [porderType of numField_normedModType].
Definition normedMod_numDomainType := [numDomainType of numField_normedModType].
End numFieldType.

Module Export Exports.
Export topology.numFieldTopology.Exports.

Canonical real_lmodType.
Canonical real_lalgType.
Canonical real_algType.
Canonical real_comAlgType.
Canonical real_unitAlgType.
Canonical real_comUnitAlgType.
Canonical real_vectType.
Canonical real_FalgType.
Canonical real_fieldExtType.
Canonical real_pseudoMetricNormedZmodType.
Canonical real_normedModType.
Coercion real_lmodType : realType >-> lmodType.
Coercion real_lalgType : realType >-> lalgType.
Coercion real_algType : realType >-> algType.
Coercion real_comAlgType : realType >-> comAlgType.
Coercion real_unitAlgType : realType >-> unitAlgType.
Coercion real_comUnitAlgType : realType >-> comUnitAlgType.
Coercion real_vectType : realType >-> vectType.
Coercion real_FalgType : realType >-> FalgType.
Coercion real_fieldExtType : realType >-> fieldExtType.
Coercion real_pseudoMetricNormedZmodType :
  realType >-> pseudoMetricNormedZmodType.
Coercion real_normedModType : realType >-> normedModType.

Canonical rcf_lmodType.
Canonical rcf_lalgType.
Canonical rcf_algType.
Canonical rcf_comAlgType.
Canonical rcf_unitAlgType.
Canonical rcf_comUnitAlgType.
Canonical rcf_vectType.
Canonical rcf_FalgType.
Canonical rcf_fieldExtType.
Canonical rcf_pseudoMetricNormedZmodType.
Canonical rcf_normedModType.
Coercion rcf_lmodType : rcfType >-> lmodType.
Coercion rcf_lalgType : rcfType >-> lalgType.
Coercion rcf_algType : rcfType >-> algType.
Coercion rcf_comAlgType : rcfType >-> comAlgType.
Coercion rcf_unitAlgType : rcfType >-> unitAlgType.
Coercion rcf_comUnitAlgType : rcfType >-> comUnitAlgType.
Coercion rcf_vectType : rcfType >-> vectType.
Coercion rcf_FalgType : rcfType >-> FalgType.
Coercion rcf_fieldExtType : rcfType >-> fieldExtType.
Coercion rcf_pseudoMetricNormedZmodType :
  rcfType >-> pseudoMetricNormedZmodType.
Coercion rcf_normedModType : rcfType >-> normedModType.

Canonical archiField_lmodType.
Canonical archiField_lalgType.
Canonical archiField_algType.
Canonical archiField_comAlgType.
Canonical archiField_unitAlgType.
Canonical archiField_comUnitAlgType.
Canonical archiField_vectType.
Canonical archiField_FalgType.
Canonical archiField_fieldExtType.
Canonical archiField_pseudoMetricNormedZmodType.
Canonical archiField_normedModType.
Coercion archiField_lmodType : archiFieldType >-> lmodType.
Coercion archiField_lalgType : archiFieldType >-> lalgType.
Coercion archiField_algType : archiFieldType >-> algType.
Coercion archiField_comAlgType : archiFieldType >-> comAlgType.
Coercion archiField_unitAlgType : archiFieldType >-> unitAlgType.
Coercion archiField_comUnitAlgType : archiFieldType >-> comUnitAlgType.
Coercion archiField_vectType : archiFieldType >-> vectType.
Coercion archiField_FalgType : archiFieldType >-> FalgType.
Coercion archiField_fieldExtType : archiFieldType >-> fieldExtType.
Coercion archiField_pseudoMetricNormedZmodType :
  archiFieldType >-> pseudoMetricNormedZmodType.
Coercion archiField_normedModType : archiFieldType >-> normedModType.

Canonical realField_lmodType.
Canonical realField_lalgType.
Canonical realField_algType.
Canonical realField_comAlgType.
Canonical realField_unitAlgType.
Canonical realField_comUnitAlgType.
Canonical realField_vectType.
Canonical realField_FalgType.
Canonical realField_fieldExtType.
Canonical realField_pseudoMetricNormedZmodType.
Canonical realField_normedModType.
Canonical lmod_latticeType.
Canonical lmod_distrLatticeType.
Canonical lmod_orderType.
Canonical lmod_realDomainType.
Canonical lalg_latticeType.
Canonical lalg_distrLatticeType.
Canonical lalg_orderType.
Canonical lalg_realDomainType.
Canonical alg_latticeType.
Canonical alg_distrLatticeType.
Canonical alg_orderType.
Canonical alg_realDomainType.
Canonical comAlg_latticeType.
Canonical comAlg_distrLatticeType.
Canonical comAlg_orderType.
Canonical comAlg_realDomainType.
Canonical unitAlg_latticeType.
Canonical unitAlg_distrLatticeType.
Canonical unitAlg_orderType.
Canonical unitAlg_realDomainType.
Canonical comUnitAlg_latticeType.
Canonical comUnitAlg_distrLatticeType.
Canonical comUnitAlg_orderType.
Canonical comUnitAlg_realDomainType.
Canonical vect_latticeType.
Canonical vect_distrLatticeType.
Canonical vect_orderType.
Canonical vect_realDomainType.
Canonical Falg_latticeType.
Canonical Falg_distrLatticeType.
Canonical Falg_orderType.
Canonical Falg_realDomainType.
Canonical fieldExt_latticeType.
Canonical fieldExt_distrLatticeType.
Canonical fieldExt_orderType.
Canonical fieldExt_realDomainType.
Canonical pseudoMetricNormedZmod_latticeType.
Canonical pseudoMetricNormedZmod_distrLatticeType.
Canonical pseudoMetricNormedZmod_orderType.
Canonical pseudoMetricNormedZmod_realDomainType.
Canonical normedMod_latticeType.
Canonical normedMod_distrLatticeType.
Canonical normedMod_orderType.
Canonical normedMod_realDomainType.
Coercion realField_lmodType : realFieldType >-> lmodType.
Coercion realField_lalgType : realFieldType >-> lalgType.
Coercion realField_algType : realFieldType >-> algType.
Coercion realField_comAlgType : realFieldType >-> comAlgType.
Coercion realField_unitAlgType : realFieldType >-> unitAlgType.
Coercion realField_comUnitAlgType : realFieldType >-> comUnitAlgType.
Coercion realField_vectType : realFieldType >-> vectType.
Coercion realField_FalgType : realFieldType >-> FalgType.
Coercion realField_fieldExtType : realFieldType >-> fieldExtType.
Coercion realField_pseudoMetricNormedZmodType :
  Num.RealField.type >-> PseudoMetricNormedZmodule.type.
Coercion realField_normedModType : Num.RealField.type >-> NormedModule.type.

Canonical numClosedField_lmodType.
Canonical numClosedField_lalgType.
Canonical numClosedField_algType.
Canonical numClosedField_comAlgType.
Canonical numClosedField_unitAlgType.
Canonical numClosedField_comUnitAlgType.
Canonical numClosedField_vectType.
Canonical numClosedField_FalgType.
Canonical numClosedField_fieldExtType.
Canonical numClosedField_pseudoMetricNormedZmodType.
Canonical numClosedField_normedModType.
Canonical lmod_decFieldType.
Canonical lmod_closedFieldType.
Canonical lalg_decFieldType.
Canonical lalg_closedFieldType.
Canonical alg_decFieldType.
Canonical alg_closedFieldType.
Canonical comAlg_decFieldType.
Canonical comAlg_closedFieldType.
Canonical unitAlg_decFieldType.
Canonical unitAlg_closedFieldType.
Canonical comUnitAlg_decFieldType.
Canonical comUnitAlg_closedFieldType.
Canonical vect_decFieldType.
Canonical vect_closedFieldType.
Canonical Falg_decFieldType.
Canonical Falg_closedFieldType.
Canonical fieldExt_decFieldType.
Canonical fieldExt_closedFieldType.
Canonical pseudoMetricNormedZmod_decFieldType.
Canonical pseudoMetricNormedZmod_closedFieldType.
Canonical normedMod_decFieldType.
Canonical normedMod_closedFieldType.
Coercion numClosedField_lmodType : numClosedFieldType >-> lmodType.
Coercion numClosedField_lalgType : numClosedFieldType >-> lalgType.
Coercion numClosedField_algType : numClosedFieldType >-> algType.
Coercion numClosedField_comAlgType : numClosedFieldType >-> comAlgType.
Coercion numClosedField_unitAlgType : numClosedFieldType >-> unitAlgType.
Coercion numClosedField_comUnitAlgType : numClosedFieldType >-> comUnitAlgType.
Coercion numClosedField_vectType : numClosedFieldType >-> vectType.
Coercion numClosedField_FalgType : numClosedFieldType >-> FalgType.
Coercion numClosedField_fieldExtType : numClosedFieldType >-> fieldExtType.
Coercion numClosedField_pseudoMetricNormedZmodType :
  numClosedFieldType >-> pseudoMetricNormedZmodType.
Coercion numClosedField_normedModType : numClosedFieldType >-> normedModType.

Canonical numField_lmodType.
Canonical numField_lalgType.
Canonical numField_algType.
Canonical numField_comAlgType.
Canonical numField_unitAlgType.
Canonical numField_comUnitAlgType.
Canonical numField_vectType.
Canonical numField_FalgType.
Canonical numField_fieldExtType.
Canonical numField_pseudoMetricNormedZmodType.
Canonical numField_normedModType.
Canonical lmod_porderType.
Canonical lmod_numDomainType.
Canonical lalg_pointedType.
Canonical lalg_filteredType.
Canonical lalg_topologicalType.
Canonical lalg_uniformType.
Canonical lalg_pseudoMetricType.
Canonical lalg_normedZmodType.
Canonical lalg_pseudoMetricNormedZmodType.
Canonical lalg_normedModType.
Canonical lalg_porderType.
Canonical lalg_numDomainType.
Canonical alg_pointedType.
Canonical alg_filteredType.
Canonical alg_topologicalType.
Canonical alg_uniformType.
Canonical alg_pseudoMetricType.
Canonical alg_normedZmodType.
Canonical alg_pseudoMetricNormedZmodType.
Canonical alg_normedModType.
Canonical alg_porderType.
Canonical alg_numDomainType.
Canonical comAlg_pointedType.
Canonical comAlg_filteredType.
Canonical comAlg_topologicalType.
Canonical comAlg_uniformType.
Canonical comAlg_pseudoMetricType.
Canonical comAlg_normedZmodType.
Canonical comAlg_pseudoMetricNormedZmodType.
Canonical comAlg_normedModType.
Canonical comAlg_porderType.
Canonical comAlg_numDomainType.
Canonical unitAlg_pointedType.
Canonical unitAlg_filteredType.
Canonical unitAlg_topologicalType.
Canonical unitAlg_uniformType.
Canonical unitAlg_pseudoMetricType.
Canonical unitAlg_normedZmodType.
Canonical unitAlg_pseudoMetricNormedZmodType.
Canonical unitAlg_normedModType.
Canonical unitAlg_porderType.
Canonical unitAlg_numDomainType.
Canonical comUnitAlg_pointedType.
Canonical comUnitAlg_filteredType.
Canonical comUnitAlg_topologicalType.
Canonical comUnitAlg_uniformType.
Canonical comUnitAlg_pseudoMetricType.
Canonical comUnitAlg_normedZmodType.
Canonical comUnitAlg_pseudoMetricNormedZmodType.
Canonical comUnitAlg_normedModType.
Canonical comUnitAlg_porderType.
Canonical comUnitAlg_numDomainType.
Canonical vect_pointedType.
Canonical vect_filteredType.
Canonical vect_topologicalType.
Canonical vect_uniformType.
Canonical vect_pseudoMetricType.
Canonical vect_normedZmodType.
Canonical vect_pseudoMetricNormedZmodType.
Canonical vect_normedModType.
Canonical vect_porderType.
Canonical vect_numDomainType.
Canonical Falg_pointedType.
Canonical Falg_filteredType.
Canonical Falg_topologicalType.
Canonical Falg_uniformType.
Canonical Falg_pseudoMetricType.
Canonical Falg_normedZmodType.
Canonical Falg_pseudoMetricNormedZmodType.
Canonical Falg_normedModType.
Canonical Falg_porderType.
Canonical Falg_numDomainType.
Canonical fieldExt_pointedType.
Canonical fieldExt_filteredType.
Canonical fieldExt_topologicalType.
Canonical fieldExt_uniformType.
Canonical fieldExt_pseudoMetricType.
Canonical fieldExt_normedZmodType.
Canonical fieldExt_pseudoMetricNormedZmodType.
Canonical fieldExt_normedModType.
Canonical fieldExt_porderType.
Canonical fieldExt_numDomainType.
Canonical pseudoMetricNormedZmod_ringType.
Canonical pseudoMetricNormedZmod_comRingType.
Canonical pseudoMetricNormedZmod_unitRingType.
Canonical pseudoMetricNormedZmod_comUnitRingType.
Canonical pseudoMetricNormedZmod_idomainType.
Canonical pseudoMetricNormedZmod_fieldType.
Canonical pseudoMetricNormedZmod_porderType.
Canonical pseudoMetricNormedZmod_numDomainType.
Canonical normedMod_ringType.
Canonical normedMod_comRingType.
Canonical normedMod_unitRingType.
Canonical normedMod_comUnitRingType.
Canonical normedMod_idomainType.
Canonical normedMod_fieldType.
Canonical normedMod_porderType.
Canonical normedMod_numDomainType.
Coercion numField_lmodType : numFieldType >-> lmodType.
Coercion numField_lalgType : numFieldType >-> lalgType.
Coercion numField_algType : numFieldType >-> algType.
Coercion numField_comAlgType : numFieldType >-> comAlgType.
Coercion numField_unitAlgType : numFieldType >-> unitAlgType.
Coercion numField_comUnitAlgType : numFieldType >-> comUnitAlgType.
Coercion numField_vectType : numFieldType >-> vectType.
Coercion numField_FalgType : numFieldType >-> FalgType.
Coercion numField_fieldExtType : numFieldType >-> fieldExtType.
Coercion numField_pseudoMetricNormedZmodType :
  numFieldType >-> pseudoMetricNormedZmodType.
Coercion numField_normedModType : numFieldType >-> normedModType.
End Exports.

End numFieldNormedType.
Import numFieldNormedType.Exports.

Section NormedModule_numDomainType.
Variables (R : numDomainType) (V : normedModType R).

Lemma normrZ l (x : V) : `| l *: x | = `| l | * `| x |.
Admitted.

Lemma normrZV (x : V) : `|x| \in GRing.unit -> `| `| x |^-1 *: x | = 1.
Admitted.

End NormedModule_numDomainType.

#[deprecated(since="mathcomp-analysis 0.6.0", note="renamed `normrZ`")]
Notation normmZ := normrZ.

Section NormedModule_numFieldType.
Variables (R : numFieldType) (V : normedModType R).

Lemma normfZV (x : V) : x != 0 -> `| `|x|^-1 *: x | = 1.
Admitted.

End NormedModule_numFieldType.

Section PseudoNormedZmod_numDomainType.
Variables (R : numDomainType) (V : pseudoMetricNormedZmodType R).

Local Notation ball_norm := (ball_ (@normr R V)).

Local Notation nbhs_ball := (@nbhs_ball _ V).

Local Notation nbhs_norm := (nbhs_ball_ ball_norm).

Lemma nbhs_nbhs_norm : nbhs_norm = nbhs.
Admitted.

Lemma nbhs_normP x (P : V -> Prop) : (\near x, P x) <-> nbhs_norm x P.
Admitted.

Lemma nbhs_le_nbhs_norm (x : V) : @nbhs V _ x `=>` nbhs_norm x.
Admitted.

Lemma nbhs_norm_le_nbhs x : nbhs_norm x `=>` nbhs x.
Admitted.

Lemma filter_from_norm_nbhs x :
  @filter_from R _ [set x : R | 0 < x] (ball_norm x) = nbhs x.
Admitted.

Lemma nbhs_normE (x : V) (P : V -> Prop) :
  nbhs_norm x P = \near x, P x.
Admitted.

Lemma filter_from_normE (x : V) (P : V -> Prop) :
  @filter_from R _ [set x : R | 0 < x] (ball_norm x) P = \near x, P x.
Admitted.

Lemma near_nbhs_norm (x : V) (P : V -> Prop) :
  (\forall x \near nbhs_norm x, P x) = \near x, P x.
Admitted.

Lemma nbhs_norm_ball_norm x (e : {posnum R}) :
  nbhs_norm x (ball_norm x e%:num).
Admitted.

Lemma nbhs_ball_norm (x : V) (eps : {posnum R}) : nbhs x (ball_norm x eps%:num).
Admitted.

Lemma ball_norm_dec x y (e : R) : {ball_norm x e y} + {~ ball_norm x e y}.
Admitted.

Lemma ball_norm_sym x y (e : R) : ball_norm x e y -> ball_norm y e x.
Admitted.

Lemma ball_norm_le x (e1 e2 : R) :
  e1 <= e2 -> ball_norm x e1 `<=` ball_norm x e2.
Admitted.

Let nbhs_simpl := (nbhs_simpl,@nbhs_nbhs_norm,@filter_from_norm_nbhs).

Lemma fcvgrPdist_lt {F : set (set V)} {FF : Filter F} (y : V) :
  F --> y <-> forall eps, 0 < eps -> \forall y' \near F, `|y - y'| < eps.
Admitted.

Lemma cvgrPdist_lt {T} {F : set (set T)} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y <-> forall eps, 0 < eps -> \forall t \near F, `|y - f t| < eps.
Admitted.

Lemma cvgrPdistC_lt {T} {F : set (set T)} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y <-> forall eps, 0 < eps -> \forall t \near F, `|f t - y| < eps.
Admitted.

Lemma cvgr_dist_lt {T} {F : set (set T)} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y -> forall eps, eps > 0 -> \forall t \near F, `|y - f t| < eps.
Admitted.

Lemma __deprecated__cvg_dist {F : set (set V)} {FF : Filter F} (y : V) :
  F --> y -> forall eps, eps > 0 -> \forall y' \near F, `|y - y'| < eps.
Admitted.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="use `cvgr_dist_lt` or a variation instead")]
Notation cvg_dist := __deprecated__cvg_dist.

Lemma cvgr_distC_lt {T} {F : set (set T)} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y -> forall eps, eps > 0 -> \forall t \near F, `|f t - y| < eps.
Admitted.

Lemma cvgr_dist_le {T} {F : set (set T)} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y -> forall eps, eps > 0 -> \forall t \near F, `|y - f t| <= eps.
Admitted.

Lemma cvgr_distC_le {T} {F : set (set T)} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y -> forall eps, eps > 0 -> \forall t \near F, `|f t - y| <= eps.
Admitted.

Lemma nbhs_norm0P {P : V -> Prop} :
  (\forall x \near 0, P x) <->
  filter_from [set e | 0 < e] (fun e => [set y | `|y| < e]) P.
Admitted.

Lemma cvgr0Pnorm_lt {T} {F : set (set T)} {FF : Filter F} (f : T -> V) :
  f @ F --> 0 <-> forall eps, 0 < eps -> \forall t \near F, `|f t| < eps.
Admitted.

Lemma cvgr0_norm_lt {T} {F : set (set T)} {FF : Filter F} (f : T -> V) :
  f @ F --> 0 -> forall eps, eps > 0 -> \forall t \near F, `|f t| < eps.
Admitted.

Lemma cvgr0_norm_le {T} {F : set (set T)} {FF : Filter F} (f : T -> V) :
  f @ F --> 0 -> forall eps, eps > 0 -> \forall t \near F, `|f t| <= eps.
Admitted.

Lemma nbhs0_lt e : 0 < e -> \forall x \near (0 : V), `|x| < e.
Admitted.

Lemma dnbhs0_lt e : 0 < e -> \forall x \near (0 : V)^', `|x| < e.
Admitted.

Lemma nbhs0_le e : 0 < e -> \forall x \near (0 : V), `|x| <= e.
Admitted.

Lemma dnbhs0_le e : 0 < e -> \forall x \near (0 : V)^', `|x| <= e.
Admitted.

Lemma nbhs_norm_ball x (eps : {posnum R}) : nbhs_norm x (ball x eps%:num).
Admitted.

Lemma nbhsDl (P : set V) (x y : V) :
  (\forall z \near (x + y), P z) <-> (\near x, P (x + y)).
Admitted.

Lemma nbhsDr (P : set V) x y :
  (\forall z \near (x + y), P z) <-> (\near y, P (x + y)).
Admitted.

Lemma nbhs0P (P : set V) x : (\near x, P x) <-> (\forall e \near 0, P (x + e)).
Admitted.

End PseudoNormedZmod_numDomainType.
#[global] Hint Resolve normr_ge0 : core.
Arguments cvgr_dist_lt {_ _ _ F FF}.
Arguments cvgr_distC_lt {_ _ _ F FF}.
Arguments cvgr_dist_le {_ _ _ F FF}.
Arguments cvgr_distC_le {_ _ _ F FF}.
Arguments cvgr0_norm_lt {_ _ _ F FF}.
Arguments cvgr0_norm_le {_ _ _ F FF}.

#[global] Hint Extern 0 (is_true (`|_ - ?x| < _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: cvgr_dist_lt end : core.
#[global] Hint Extern 0 (is_true (`|?x - _| < _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: cvgr_distC_lt end : core.
#[global] Hint Extern 0 (is_true (`|?x| < _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: cvgr0_norm_lt end : core.
#[global] Hint Extern 0 (is_true (`|_ - ?x| <= _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: cvgr_dist_le end : core.
#[global] Hint Extern 0 (is_true (`|?x - _| <= _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: cvgr_distC_le end : core.
#[global] Hint Extern 0 (is_true (`|?x| <= _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: cvgr0_norm_le end : core.

#[deprecated(since="mathcomp-analysis 0.6.0",
  note="use `cvgrPdist_lt` or a variation instead")]
Notation cvg_distP := fcvgrPdist_lt.

Section analysis_struct.

Import Coq.Reals.Rdefinitions.
Import mathcomp.analysis.Rstruct.

Canonical R_pointedType := [pointedType of R for pointed_of_zmodule R_ringType].
Canonical R_filteredType :=
  [filteredType R of R for filtered_of_normedZmod R_normedZmodType].
Canonical R_topologicalType : topologicalType. exact (TopologicalType R
  (topologyOfEntourageMixin
    (uniformityOfBallMixin
      (@nbhs_ball_normE _ R_normedZmodType)
      (pseudoMetric_of_normedDomain R_normedZmodType)))). Defined.
Canonical R_uniformType : uniformType. exact (UniformType R
  (uniformityOfBallMixin (@nbhs_ball_normE _ R_normedZmodType)
    (pseudoMetric_of_normedDomain R_normedZmodType))). Defined.
Canonical R_pseudoMetricType : pseudoMetricType R_numDomainType. exact (PseudoMetricType R (pseudoMetric_of_normedDomain R_normedZmodType)). Defined.

Lemma continuity_pt_nbhs (f : R -> R) x :
  Ranalysis1.continuity_pt f x <->
  forall eps : {posnum R}, nbhs x (fun u => `|f u - f x| < eps%:num).
Admitted.

Lemma continuity_pt_cvg (f : R -> R) (x : R) :
  Ranalysis1.continuity_pt f x <-> {for x, continuous f}.
Admitted.

Lemma continuity_ptE (f : R -> R) (x : R) :
  Ranalysis1.continuity_pt f x <-> {for x, continuous f}.
Admitted.

Local Open Scope classical_set_scope.

Lemma continuity_pt_cvg' f x :
  Ranalysis1.continuity_pt f x <-> f @ x^' --> f x.
Admitted.

Lemma continuity_pt_dnbhs f x :
  Ranalysis1.continuity_pt f x <->
  forall eps, 0 < eps -> x^' (fun u => `|f x - f u| < eps).
Admitted.

Lemma nbhs_pt_comp (P : R -> Prop) (f : R -> R) (x : R) :
  nbhs (f x) P -> Ranalysis1.continuity_pt f x -> \near x, P (f x).
Admitted.

End analysis_struct.

Section open_closed_sets.

Variable R : realFieldType.

Lemma open_lt (y : R) : open [set x : R| x < y].
Admitted.
Hint Resolve open_lt : core.

Lemma open_gt (y : R) : open [set x : R | x > y].
Admitted.
Hint Resolve open_gt : core.

Lemma open_neq (y : R) : open [set x : R | x != y].
Admitted.

Lemma interval_open a b : ~~ bound_side true a -> ~~ bound_side false b ->
  open [set x : R^o | x \in Interval a b].
Admitted.

Lemma closed_le (y : R) : closed [set x : R | x <= y].
Admitted.

Lemma closed_ge (y : R) : closed [set x : R | y <= x].
Admitted.

Lemma closed_eq (y : R) : closed [set x : R | x = y].
Admitted.

Lemma interval_closed a b : ~~ bound_side false a -> ~~ bound_side true b ->
  closed [set x : R^o | x \in Interval a b].
Admitted.

End open_closed_sets.

#[global] Hint Extern 0 (open _) => now apply: open_gt : core.
#[global] Hint Extern 0 (open _) => now apply: open_lt : core.
#[global] Hint Extern 0 (open _) => now apply: open_neq : core.
#[global] Hint Extern 0 (closed _) => now apply: closed_ge : core.
#[global] Hint Extern 0 (closed _) => now apply: closed_le : core.
#[global] Hint Extern 0 (closed _) => now apply: closed_eq : core.

Section at_left_right.
Variable R : numFieldType.

Definition at_left (x : R) := within (fun u => u < x) (nbhs x).
Definition at_right (x : R) := within (fun u => x < u) (nbhs x).
Local Notation "x ^'-" := (at_left x) : classical_set_scope.
Local Notation "x ^'+" := (at_right x) : classical_set_scope.

Global Instance at_right_proper_filter (x : R) : ProperFilter x^'+.
Admitted.

Global Instance at_left_proper_filter (x : R) : ProperFilter x^'-.
Admitted.

Lemma nbhs_right0P x (P : set R) :
  (\forall y \near x^'+, P y) <-> \forall e \near 0^'+, P (x + e).
Admitted.

Lemma nbhs_left0P x (P : set R) :
  (\forall y \near x^'-, P y) <-> \forall e \near 0^'+, P (x - e).
Admitted.

Lemma nbhs_right_gt x : \forall y \near x^'+, x < y.
Admitted.

Lemma nbhs_left_lt x : \forall y \near x^'-, y < x.
Admitted.

Lemma nbhs_right_neq x : \forall y \near x^'+, y != x.
Admitted.

Lemma nbhs_left_neq x : \forall y \near x^'-, y != x.
Admitted.

Lemma nbhs_right_ge x : \forall y \near x^'+, x <= y.
Admitted.

Lemma nbhs_left_le x : \forall y \near x^'-, y <= x.
Admitted.

Lemma nbhs_right_lt x z : x < z -> \forall y \near x^'+, y < z.
Admitted.

Lemma nbhs_right_le x z : x < z -> \forall y \near x^'+, y <= z.
Admitted.

Lemma nbhs_left_gt x z : z < x -> \forall y \near x^'-, z < y.
Admitted.

Lemma nbhs_left_ge x z : z < x -> \forall y \near x^'-, z <= y.
Admitted.

End at_left_right.
#[global] Typeclasses Opaque at_left at_right.
Notation "x ^'-" := (at_left x) : classical_set_scope.
Notation "x ^'+" := (at_right x) : classical_set_scope.

Section open_itv_subset.
Context {R : realType}.
Variables (A : set R) (x : R).

Lemma open_itvoo_subset :
  open A -> A x -> \forall r \near 0^'+, `]x - r, x + r[ `<=` A.
Admitted.

Lemma open_itvcc_subset :
  open A -> A x -> \forall r \near 0^'+, `[x - r, x + r] `<=` A.
Admitted.

End open_itv_subset.

Section at_left_right_topologicalType.
Variables (R : numFieldType) (V : topologicalType) (f : R -> V) (x : R).

Lemma cvg_at_right_filter : f z @[z --> x] --> f x -> f z @[z --> x^'+] --> f x.
Admitted.

Lemma cvg_at_left_filter : f z @[z --> x] --> f x -> f z @[z --> x^'-] --> f x.
Admitted.

Lemma cvg_at_right_within : f x @[x --> x^'+] --> f x ->
  f x @[x --> within (fun u => x <= u) (nbhs x)] --> f x.
Admitted.

Lemma cvg_at_left_within : f x @[x --> x^'-] --> f x ->
  f x @[x --> within (fun u => u <= x) (nbhs x)] --> f x.
Admitted.

End at_left_right_topologicalType.

Section at_left_right_pmNormedZmod.
Variables (R : numFieldType) (V : pseudoMetricNormedZmodType R).

Lemma nbhsr0P (P : set V) x :
  (\forall y \near x, P y) <->
  (\forall e \near 0^'+, forall y, `|x - y| <= e -> P y).
Admitted.

Let cvgrP {F : set (set V)} {FF : Filter F} (y : V) : [<->
  F --> y;
  forall eps, 0 < eps -> \forall t \near F, `|y - t| <= eps;
  \forall eps \near 0^'+, \forall t \near F, `|y - t| <= eps;
  \forall eps \near 0^'+, \forall t \near F, `|y - t| < eps].
Admitted.

Lemma cvgrPdist_le {T} {F : set (set T)} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y <-> forall eps, 0 < eps -> \forall t \near F, `|y - f t| <= eps.
Admitted.

Lemma cvgrPdist_ltp {T} {F : set (set T)} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y <-> \forall eps \near 0^'+, \forall t \near F, `|y - f t| < eps.
Admitted.

Lemma cvgrPdist_lep {T} {F : set (set T)} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y <-> \forall eps \near 0^'+, \forall t \near F, `|y - f t| <= eps.
Admitted.

Lemma cvgrPdistC_le {T} {F : set (set T)} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y <-> forall eps, 0 < eps -> \forall t \near F, `|f t - y| <= eps.
Admitted.

Lemma cvgrPdistC_ltp {T} {F : set (set T)} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y <-> \forall eps \near 0^'+, \forall t \near F, `|f t - y| < eps.
Admitted.

Lemma cvgrPdistC_lep {T} {F : set (set T)} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y <-> \forall eps \near 0^'+, \forall t \near F, `|f t - y| <= eps.
Admitted.

Lemma cvgr0Pnorm_le {T} {F : set (set T)} {FF : Filter F} (f : T -> V) :
  f @ F --> 0 <-> forall eps, 0 < eps -> \forall t \near F, `|f t| <= eps.
Admitted.

Lemma cvgr0Pnorm_ltp {T} {F : set (set T)} {FF : Filter F} (f : T -> V) :
  f @ F --> 0 <-> \forall eps \near 0^'+, \forall t \near F, `|f t| < eps.
Admitted.

Lemma cvgr0Pnorm_lep {T} {F : set (set T)} {FF : Filter F} (f : T -> V) :
  f @ F --> 0 <-> \forall eps \near 0^'+, \forall t \near F, `|f t| <= eps.
Admitted.

Lemma cvgr_norm_lt {T} {F : set (set T)} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y -> forall u, `|y| < u -> \forall t \near F, `|f t| < u.
Admitted.

Lemma cvgr_norm_le {T} {F : set (set T)} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y -> forall u, `|y| < u -> \forall t \near F, `|f t| <= u.
Admitted.

Lemma cvgr_norm_gt {T} {F : set (set T)} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y -> forall u, `|y| > u -> \forall t \near F, `|f t| > u.
Admitted.

Lemma cvgr_norm_ge {T} {F : set (set T)} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y -> forall u, `|y| > u -> \forall t \near F, `|f t| >= u.
Admitted.

Lemma cvgr_neq0 {T} {F : set (set T)} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y -> y != 0 -> \forall t \near F, f t != 0.
Admitted.

End at_left_right_pmNormedZmod.
Arguments cvgr_norm_lt {R V T F FF f}.
Arguments cvgr_norm_le {R V T F FF f}.
Arguments cvgr_norm_gt {R V T F FF f}.
Arguments cvgr_norm_ge {R V T F FF f}.
Arguments cvgr_neq0 {R V T F FF f}.

#[global] Hint Extern 0 (is_true (`|_ - ?x| < _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: cvgr_dist_lt end : core.
#[global] Hint Extern 0 (is_true (`|?x - _| < _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: cvgr_distC_lt end : core.
#[global] Hint Extern 0 (is_true (`|?x| < _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: cvgr0_norm_lt end : core.
#[global] Hint Extern 0 (is_true (`|_ - ?x| <= _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: cvgr_dist_le end : core.
#[global] Hint Extern 0 (is_true (`|?x - _| <= _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: cvgr_distC_le end : core.
#[global] Hint Extern 0 (is_true (`|?x| <= _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: cvgr0_norm_le end : core.

#[global] Hint Extern 0 (is_true (_ < ?x)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: nbhs_right_gt end : core.
#[global] Hint Extern 0 (is_true (?x < _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: nbhs_left_lt end : core.
#[global] Hint Extern 0 (is_true (?x != _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: nbhs_right_neq end : core.
#[global] Hint Extern 0 (is_true (?x != _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: nbhs_left_neq end : core.
#[global] Hint Extern 0 (is_true (_ < ?x)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: nbhs_left_gt end : core.
#[global] Hint Extern 0 (is_true (?x < _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: nbhs_right_lt end : core.
#[global] Hint Extern 0 (is_true (_ <= ?x)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: nbhs_right_ge end : core.
#[global] Hint Extern 0 (is_true (?x <= _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: nbhs_left_le end : core.
#[global] Hint Extern 0 (is_true (_ <= ?x)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: nbhs_right_ge end : core.
#[global] Hint Extern 0 (is_true (?x <= _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: nbhs_left_le end : core.

#[global] Hint Extern 0 (ProperFilter _^'-) =>
  (apply: at_left_proper_filter) : typeclass_instances.
#[global] Hint Extern 0 (ProperFilter _^'+) =>
  (apply: at_right_proper_filter) : typeclass_instances.

Section at_left_rightR.
Variable (R : numFieldType).

Lemma real_cvgr_lt {T} {F : set (set T)} {FF : Filter F} (f : T -> R) (y : R) :
    y \is Num.real -> f @ F --> y ->
  forall z, z > y -> \forall t \near F, f t \is Num.real -> f t < z.
Admitted.

Lemma real_cvgr_le {T} {F : set (set T)} {FF : Filter F} (f : T -> R) (y : R) :
    y \is Num.real ->  f @ F --> y ->
  forall z, z > y -> \forall t \near F, f t \is Num.real -> f t <= z.
Admitted.

Lemma real_cvgr_gt {T} {F : set (set T)} {FF : Filter F} (f : T -> R) (y : R) :
    y \is Num.real -> f @ F --> y ->
  forall z, y > z -> \forall t \near F, f t \is Num.real -> f t > z.
Admitted.

Lemma real_cvgr_ge {T} {F : set (set T)} {FF : Filter F} (f : T -> R) (y : R) :
    y \is Num.real -> f @ F --> y ->
  forall z, z < y -> \forall t \near F, f t \is Num.real -> f t >= z.
Admitted.

End at_left_rightR.
Arguments real_cvgr_le {R T F FF f}.
Arguments real_cvgr_lt {R T F FF f}.
Arguments real_cvgr_ge {R T F FF f}.
Arguments real_cvgr_gt {R T F FF f}.

Section realFieldType.
Context (R : realFieldType).

Lemma at_right_in_segment (x : R) (P : set R) :
  (\forall e \near 0^'+, {in `[x - e, x + e], forall x, P x}) <-> (\near x, P x).
Admitted.

Lemma cvgr_lt {T} {F : set (set T)} {FF : Filter F} (f : T -> R) (y : R) :
  f @ F --> y -> forall z, z > y -> \forall t \near F, f t < z.
Admitted.

Lemma cvgr_le {T} {F : set (set T)} {FF : Filter F} (f : T -> R) (y : R) :
  f @ F --> y -> forall z, z > y -> \forall t \near F, f t <= z.
Admitted.

Lemma cvgr_gt {T} {F : set (set T)} {FF : Filter F} (f : T -> R) (y : R) :
  f @ F --> y -> forall z, y > z -> \forall t \near F, f t > z.
Admitted.

Lemma cvgr_ge {T} {F : set (set T)} {FF : Filter F} (f : T -> R) (y : R) :
  f @ F --> y -> forall z, z < y -> \forall t \near F, f t >= z.
Admitted.

End realFieldType.
Arguments cvgr_le {R T F FF f}.
Arguments cvgr_lt {R T F FF f}.
Arguments cvgr_ge {R T F FF f}.
Arguments cvgr_gt {R T F FF f}.
Definition self_sub (K : numDomainType) (V W : normedModType K)
  (f : V -> W) (x : V * V) : W. exact (f x.1 - f x.2). Defined.
Arguments self_sub {K V W} f x /.
Definition fun1 {T : Type} {K : numFieldType} : T -> K. exact (fun=> 1). Defined.
Arguments fun1 {T K} x /.

Definition dominated_by {T : Type} {K : numDomainType} {V W : pseudoMetricNormedZmodType K}
  (h : T -> V) (k : K) (f : T -> W) (F : set (set T)) :=
  F [set x | `|f x| <= k * `|h x|].

Definition strictly_dominated_by {T : Type} {K : numDomainType} {V W : pseudoMetricNormedZmodType K}
  (h : T -> V) (k : K) (f : T -> W) (F : set (set T)) :=
  F [set x | `|f x| < k * `|h x|].

Lemma sub_dominatedl (T : Type) (K : numDomainType) (V W : pseudoMetricNormedZmodType K)
   (h : T -> V) (k : K) (F G : set (set T)) : F `=>` G ->
  (@dominated_by T K V W h k)^~ G `<=` (dominated_by h k)^~ F.
Admitted.

Lemma sub_dominatedr (T : Type) (K : numDomainType) (V : pseudoMetricNormedZmodType K)
    (h : T -> V) (k : K) (f g : T -> V) (F : set (set T)) (FF : Filter F) :
   (\forall x \near F, `|f x| <= `|g x|) ->
   dominated_by h k g F -> dominated_by h k f F.
Admitted.

Lemma dominated_by1 {T : Type} {K : numFieldType} {V : pseudoMetricNormedZmodType K} :
  @dominated_by T K _ V fun1 = fun k f F => F [set x | `|f x| <= k].
Admitted.

Lemma strictly_dominated_by1 {T : Type} {K : numFieldType}
    {V : pseudoMetricNormedZmodType K} :
  @strictly_dominated_by T K _ V fun1 = fun k f F => F [set x | `|f x| < k].
Admitted.

Lemma ex_dom_bound {T : Type} {K : numFieldType} {V W : pseudoMetricNormedZmodType K}
    (h : T -> V) (f : T -> W) (F : set (set T)) {PF : ProperFilter F}:
  (\forall M \near +oo, dominated_by h M f F) <->
  exists M, dominated_by h M f F.
Admitted.

Lemma ex_strict_dom_bound {T : Type} {K : numFieldType}
    {V W : pseudoMetricNormedZmodType K}
    (h : T -> V) (f : T -> W) (F : set (set T)) {PF : ProperFilter F} :
  (\forall x \near F, h x != 0) ->
  (\forall M \near +oo, dominated_by h M f F) <->
   exists M, strictly_dominated_by h M f F.
Admitted.

Definition bounded_near {T : Type} {K : numFieldType}
    {V : pseudoMetricNormedZmodType K}
  (f : T -> V) (F : set (set T)) :=
  \forall M \near +oo, F [set x | `|f x| <= M].

Lemma boundedE {T : Type} {K : numFieldType} {V : pseudoMetricNormedZmodType K} :
  @bounded_near T K V = fun f F => \forall M \near +oo, dominated_by fun1 M f F.
Admitted.

Lemma sub_boundedr (T : Type) (K : numFieldType) (V : pseudoMetricNormedZmodType K)
     (F G : set (set T)) : F `=>` G ->
  (@bounded_near T K V)^~ G `<=` bounded_near^~ F.
Admitted.

Lemma sub_boundedl (T : Type) (K : numFieldType) (V : pseudoMetricNormedZmodType K)
     (f g : T -> V) (F : set (set T)) (FF : Filter F) :
 (\forall x \near F, `|f x| <= `|g x|) ->  bounded_near g F -> bounded_near f F.
Admitted.

Lemma ex_bound {T : Type} {K : numFieldType} {V : pseudoMetricNormedZmodType K}
  (f : T -> V) (F : set (set T)) {PF : ProperFilter F}:
  bounded_near f F <-> exists M, F [set x | `|f x| <= M].
Admitted.

Lemma ex_strict_bound {T : Type} {K : numFieldType} {V : pseudoMetricNormedZmodType K}
  (f : T -> V) (F : set (set T)) {PF : ProperFilter F}:
  bounded_near f F <-> exists M, F [set x | `|f x| < M].
Admitted.

Lemma ex_strict_bound_gt0 {T : Type} {K : numFieldType} {V : pseudoMetricNormedZmodType K}
  (f : T -> V) (F : set (set T)) {PF : Filter F}:
  bounded_near f F -> exists2 M, M > 0 & F [set x | `|f x| < M].
Admitted.

Notation "[ 'bounded' E | x 'in' A ]" :=
  (bounded_near (fun x => E) (globally A)).
Notation bounded_set := [set A | [bounded x | x in A]].
Notation bounded_fun := [set f | [bounded f x | x in setT]].

Lemma bounded_fun_has_ubound (T : Type) (R : realFieldType) (a : T -> R) :
  bounded_fun a -> has_ubound (range a).
Admitted.

Lemma bounded_funN (T : Type) (R : realFieldType) (a : T -> R) :
  bounded_fun a -> bounded_fun (- a).
Admitted.

Lemma bounded_fun_has_lbound (T : Type) (R : realFieldType) (a : T -> R) :
  bounded_fun a -> has_lbound (range a).
Admitted.

Lemma bounded_funD (T : Type) (R : realFieldType) (a b : T -> R) :
  bounded_fun a -> bounded_fun b -> bounded_fun (a \+ b).
Admitted.

Lemma bounded_locally (T : topologicalType)
    (R : numFieldType) (V : normedModType R) (A : set T) (f : T -> V) :
  [bounded f x | x in A] -> [locally [bounded f x | x in A]].
Admitted.

Notation "k .-lipschitz_on f" :=
  (dominated_by (self_sub id) k (self_sub f)) : type_scope.

Definition sub_klipschitz (K : numFieldType) (V W : normedModType K) (k : K)
           (f : V -> W) (F G : set (set (V * V))) :
  F `=>` G -> k.-lipschitz_on f G -> k.-lipschitz_on f F.
Admitted.

Definition lipschitz_on (K : numFieldType) (V W : normedModType K)
           (f : V -> W) (F : set (set (V * V))) :=
  \forall M \near +oo, M.-lipschitz_on f F.

Definition sub_lipschitz (K : numFieldType) (V W : normedModType K)
           (f : V -> W) (F G : set (set (V * V))) :
  F `=>` G -> lipschitz_on f G -> lipschitz_on f F.
Admitted.

Lemma klipschitzW (K : numFieldType) (V W : normedModType K) (k : K)
      (f : V -> W) (F : set (set (V * V))) {PF : ProperFilter F} :
  k.-lipschitz_on f F -> lipschitz_on f F.
Admitted.

Notation "k .-lipschitz_ A f" :=
  (k.-lipschitz_on f (globally (A `*` A))) : type_scope.
Notation "k .-lipschitz f" := (k.-lipschitz_setT f) : type_scope.
Notation "[ 'lipschitz' E | x 'in' A ]" :=
  (lipschitz_on (fun x => E) (globally (A `*` A))) : type_scope.
Notation lipschitz f := [lipschitz f x | x in setT].

Lemma lipschitz_set0 (K : numFieldType) (V W : normedModType K)
  (f : V -> W) : [lipschitz f x | x in set0].
Admitted.

Lemma lipschitz_set1 (K : numFieldType) (V W : normedModType K)
  (f : V -> W) (a : V) : [lipschitz f x | x in [set a]].
Admitted.

Lemma klipschitz_locally (R : numFieldType) (V W : normedModType R) (k : R)
    (f : V -> W) (A : set V) :
  k.-lipschitz_A f -> [locally k.-lipschitz_A f].
Admitted.

Lemma lipschitz_locally (R : numFieldType) (V W : normedModType R)
    (A : set V) (f : V -> W) :
  [lipschitz f x | x in A] -> [locally [lipschitz f x | x in A]].
Admitted.

Lemma lipschitz_id (R : numFieldType) (V : normedModType R) :
  1.-lipschitz (@id V).
Admitted.
Arguments lipschitz_id {R V}.

Section contractions.
Context {R : numDomainType} {X Y : normedModType R} {U : set X} {V : set Y}.

Definition contraction (q : {nonneg R}) (f : {fun U >-> V}) :=
  q%:num < 1 /\ q%:num.-lipschitz_U f.

Definition is_contraction (f : {fun U >-> V}) := exists q, contraction q f.

End contractions.

Lemma contraction_fixpoint_unique {R : realDomainType}
    {X : normedModType R} (U : set X) (f : {fun U >-> U}) (x y : X) :
  is_contraction f -> U x -> U y -> x = f x -> y = f y -> x = y.
Admitted.

Section PseudoNormedZMod_numFieldType.
Variables (R : numFieldType) (V : pseudoMetricNormedZmodType R).

Local Notation ball_norm := (ball_ (@normr R V)).

Local Notation nbhs_norm := (@nbhs_ball _ V).

Lemma norm_hausdorff : hausdorff_space V.
Admitted.
Hint Extern 0 (hausdorff_space _) => solve[apply: norm_hausdorff] : core.

Lemma norm_closeE (x y : V): close x y = (x = y).
Admitted.
Lemma norm_close_eq (x y : V) : close x y -> x = y.
Admitted.

Lemma norm_cvg_unique {F} {FF : ProperFilter F} : is_subset1 [set x : V | F --> x].
Admitted.

Lemma norm_cvg_eq (x y : V) : x --> y -> x = y.
Admitted.
Lemma norm_lim_id (x : V) : lim x = x.
Admitted.

Lemma norm_cvg_lim {F} {FF : ProperFilter F} (l : V) : F --> l -> lim F = l.
Admitted.

Lemma norm_lim_near_cst U {F} {FF : ProperFilter F} (l : V) (f : U -> V) :
   (\forall x \near F, f x = l) -> lim (f @ F) = l.
Admitted.

Lemma norm_lim_cst U {F} {FF : ProperFilter F} (k : V) :
   lim ((fun _ : U => k) @ F) = k.
Admitted.

Lemma norm_cvgi_unique {U : Type} {F} {FF : ProperFilter F} (f : U -> set V) :
  {near F, is_fun f} -> is_subset1 [set x : V | f `@ F --> x].
Admitted.

Lemma norm_cvgi_lim {U} {F} {FF : ProperFilter F} (f : U -> V -> Prop) (l : V) :
  F (fun x : U => is_subset1 (f x)) ->
  f `@ F --> l -> lim (f `@ F) = l.
Admitted.

Lemma distm_lt_split (z x y : V) (e : R) :
  `|x - z| < e / 2 -> `|z - y| < e / 2 -> `|x - y| < e.
Admitted.

Lemma distm_lt_splitr (z x y : V) (e : R) :
  `|z - x| < e / 2 -> `|z - y| < e / 2 -> `|x - y| < e.
Admitted.

Lemma distm_lt_splitl (z x y : V) (e : R) :
  `|x - z| < e / 2 -> `|y - z| < e / 2 -> `|x - y| < e.
Admitted.

Lemma normm_leW (x : V) (e : R) : e > 0 -> `|x| <= e / 2 -> `|x| < e.
Admitted.

Lemma normm_lt_split (x y : V) (e : R) :
  `|x| < e / 2 -> `|y| < e / 2 -> `|x + y| < e.
Admitted.

Lemma __deprecated__cvg_distW {F : set (set V)} {FF : Filter F} (y : V) :
  (forall eps, 0 < eps -> \forall y' \near F, `|y - y'| <= eps) ->
  F --> y.
Admitted.

End PseudoNormedZMod_numFieldType.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="use `cvgrPdist_le` or a variation instead")]
Notation cvg_distW := __deprecated__cvg_distW.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="renamed to `norm_cvgi_lim`")]
Notation norm_cvgi_map_lim := norm_cvgi_lim.

Section NormedModule_numFieldType.
Variables (R : numFieldType) (V : normedModType R).

Section cvgr_norm_infty.
Variables (I : Type) (F : set (set I)) (FF : Filter F) (f : I -> V) (y : V).

Lemma cvgr_norm_lty :
  f @ F --> y -> \forall M \near +oo, \forall y' \near F, `|f y'| < M.
Admitted.

Lemma cvgr_norm_ley :
  f @ F --> y -> \forall M \near +oo, \forall y' \near F, `|f y'| <= M.
Admitted.

Lemma cvgr_norm_gtNy :
  f @ F --> y -> \forall M \near -oo, \forall y' \near F, `|f y'| > M.
Admitted.

Lemma cvgr_norm_geNy :
  f @ F --> y -> \forall M \near -oo, \forall y' \near F, `|f y'| >= M.
Admitted.

End cvgr_norm_infty.

Lemma __deprecated__cvg_bounded_real {F : set (set V)} {FF : Filter F} (y : V) :
  F --> y -> \forall M \near +oo, \forall y' \near F, `|y'| < M.
Admitted.

Lemma cvg_bounded {I} {F : set (set I)} {FF : Filter F} (f : I -> V) (y : V) :
  f @ F --> y -> bounded_near f F.
Admitted.

End NormedModule_numFieldType.
Arguments cvgr_norm_lty {R V I F FF}.
Arguments cvgr_norm_ley {R V I F FF}.
Arguments cvgr_norm_gtNy {R V I F FF}.
Arguments cvgr_norm_geNy {R V I F FF}.
Arguments cvg_bounded {R V I F FF}.
#[global]
Hint Extern 0 (hausdorff_space _) => solve[apply: norm_hausdorff] : core.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="use `cvgr_norm_lty` or a variation instead")]
Notation cvg_bounded_real := __deprecated__cvg_bounded_real.

Module Export NbhsNorm.
Definition nbhs_simpl := (nbhs_simpl,@nbhs_nbhs_norm,@filter_from_norm_nbhs).
End NbhsNorm.

Section hausdorff.

Lemma pseudoMetricNormedZModType_hausdorff (R : realFieldType)
    (V : pseudoMetricNormedZmodType R) :
  hausdorff_space V.
Admitted.

End hausdorff.

Module Export NearNorm.
Definition near_simpl := (@near_simpl, @nbhs_normE, @filter_from_normE,
  @near_nbhs_norm).
End NearNorm.

Lemma __deprecated__continuous_cvg_dist {R : numFieldType}
  (V W : pseudoMetricNormedZmodType R) (f : V -> W) x l :
  continuous f -> x --> l -> forall e : {posnum R}, `|f l - f x| < e%:num.
Admitted.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="simply use the fact that `(x --> l) -> (x = l)`")]
Notation continuous_cvg_dist := __deprecated__continuous_cvg_dist.

Section mx_norm.
Variables (K : numDomainType) (m n : nat).
Implicit Types x y : 'M[K]_(m, n).
Definition mx_norm x : K. exact ((\big[maxr/0%:nng]_i `|x i.1 i.2|%:nng)%:num). Defined.

Lemma mx_normE x : mx_norm x = (\big[maxr/0%:nng]_i `|x i.1 i.2|%:nng)%:num.
Admitted.

Lemma ler_mx_norm_add x y : mx_norm (x + y) <= mx_norm x + mx_norm y.
Admitted.

Lemma mx_norm_eq0 x : mx_norm x = 0 -> x = 0.
Admitted.

Lemma mx_norm0 : mx_norm 0 = 0.
Admitted.

Lemma mx_norm_neq0 x : mx_norm x != 0 -> exists i, mx_norm x = `|x i.1 i.2|.
Admitted.

Lemma mx_norm_natmul x k : mx_norm (x *+ k) = (mx_norm x) *+ k.
Admitted.

Lemma mx_normN x : mx_norm (- x) = mx_norm x.
Admitted.

End mx_norm.

Lemma mx_normrE (K : realDomainType) (m n : nat) (x : 'M[K]_(m, n)) :
  mx_norm x = \big[maxr/0]_ij `|x ij.1 ij.2|.
Admitted.

Definition matrix_normedZmodMixin (K : numDomainType) (m n : nat) :=
  @Num.NormedMixin _ _ _ (@mx_norm K m.+1 n.+1) (@ler_mx_norm_add _ _ _)
    (@mx_norm_eq0 _ _ _) (@mx_norm_natmul _ _ _) (@mx_normN _ _ _).

Canonical matrix_normedZmodType (K : numDomainType) (m n : nat) :=
  NormedZmodType K 'M[K]_(m.+1, n.+1) (matrix_normedZmodMixin K m n).

Section matrix_NormedModule.
Variables (K : numFieldType) (m n : nat).

Local Lemma ball_gt0 (x y : 'M[K]_(m.+1, n.+1)) e : ball x e y -> 0 < e.
Admitted.

Lemma mx_norm_ball :
  @ball _ [pseudoMetricType K of 'M[K]_(m.+1, n.+1)] = ball_ (fun x => `| x |).
Admitted.

Definition matrix_PseudoMetricNormedZmodMixin :=
  PseudoMetricNormedZmodule.Mixin mx_norm_ball.
Canonical matrix_pseudoMetricNormedZmodType :=
  PseudoMetricNormedZmodType K 'M[K]_(m.+1, n.+1) matrix_PseudoMetricNormedZmodMixin.

Lemma mx_normZ (l : K) (x : 'M[K]_(m.+1, n.+1)) : `| l *: x | = `| l | * `| x |.
Admitted.

Definition matrix_NormedModMixin := NormedModMixin mx_normZ.
Canonical matrix_normedModType :=
  NormedModType K 'M[K]_(m.+1, n.+1) matrix_NormedModMixin.

End matrix_NormedModule.

Section prod_PseudoMetricNormedZmodule.
Context {K : numDomainType} {U V : pseudoMetricNormedZmodType K}.

Lemma ball_prod_normE : ball = ball_ (fun x => `| x : U * V |).
Admitted.

Lemma prod_norm_ball : @ball _ [pseudoMetricType K of U * V] = ball_ (fun x => `|x|).
Admitted.

Definition prod_pseudoMetricNormedZmodMixin :=
  PseudoMetricNormedZmodule.Mixin prod_norm_ball.
Canonical prod_pseudoMetricNormedZmodType :=
  PseudoMetricNormedZmodType K (U * V) prod_pseudoMetricNormedZmodMixin.

End prod_PseudoMetricNormedZmodule.

Section prod_NormedModule.
Context {K : numDomainType} {U V : normedModType K}.

Lemma prod_norm_scale (l : K) (x : U * V) : `| l *: x | = `|l| * `| x |.
Admitted.

Definition prod_NormedModMixin := NormedModMixin prod_norm_scale.
Canonical prod_normedModType :=
  NormedModType K (U * V) prod_NormedModMixin.

End prod_NormedModule.

Section example_of_sharing.
Variables (K : numDomainType).

Example matrix_triangke m n (M N : 'M[K]_(m.+1, n.+1)) :
  `|M + N| <= `|M| + `|N|.
Admitted.

Example pair_triangle (x y : K * K) : `|x + y| <= `|x| + `|y|.
Admitted.

End example_of_sharing.

Section prod_NormedModule_lemmas.

Context {T : Type} {K : numDomainType} {U V : normedModType K}.

Lemma fcvgr2dist_ltP {F : set (set U)} {G : set (set V)}
  {FF : Filter F} {FG : Filter G} (y : U) (z : V) :
  (F, G) --> (y, z) <->
  forall eps, 0 < eps ->
   \forall y' \near F & z' \near G, `| (y, z) - (y', z') | < eps.
Admitted.

Lemma cvgr2dist_ltP {I J} {F : set (set I)} {G : set (set J)}
  {FF : Filter F} {FG : Filter G} (f : I -> U) (g : J -> V) (y : U) (z : V) :
  (f @ F, g @ G) --> (y, z) <->
  forall eps, 0 < eps ->
   \forall i \near F & j \near G, `| (y, z) - (f i, g j) | < eps.
admit.
Defined.

Lemma cvgr2dist_lt {I J} {F : set (set I)} {G : set (set J)}
  {FF : Filter F} {FG : Filter G} (f : I -> U) (g : J -> V) (y : U) (z : V) :
  (f @ F, g @ G) --> (y, z) ->
  forall eps, 0 < eps ->
   \forall i \near F & j \near G, `| (y, z) - (f i, g j) | < eps.
admit.
Defined.

Lemma __deprecated__cvg_dist2 {F : set (set U)} {G : set (set V)}
  {FF : Filter F} {FG : Filter G} (y : U) (z : V):
  (F, G) --> (y, z) ->
  forall eps, 0 < eps ->
   \forall y' \near F & z' \near G, `|(y, z) - (y', z')| < eps.
Admitted.
#[deprecated(since="mathcomp-analysis 0.6.0",
note="use `cvgr2dist_lt` or a variant instead")]
Notation cvg_dist2 := __deprecated__cvg_dist2.

End prod_NormedModule_lemmas.
Arguments cvgr2dist_ltP {_ _ _ _ _ F G FF FG}.
Arguments cvgr2dist_lt {_ _ _ _ _ F G FF FG}.

#[deprecated(since="mathcomp-analysis 0.6.0",
note="use `fcvgr2dist_ltP` or a variant instead")]
Notation cvg_dist2P := fcvgr2dist_ltP.

Section NVS_continuity_pseudoMetricNormedZmodType.
Context {K : numFieldType} {V : pseudoMetricNormedZmodType K}.

Lemma opp_continuous : continuous (@GRing.opp V).
Admitted.

Lemma add_continuous : continuous (fun z : V * V => z.1 + z.2).
Admitted.

Lemma natmul_continuous n : continuous (fun x : V => x *+ n).
Admitted.

Lemma norm_continuous : continuous (normr : V -> K).
Admitted.

End NVS_continuity_pseudoMetricNormedZmodType.

Section NVS_continuity_normedModType.
Context {K : numFieldType} {V : normedModType K}.

Lemma scale_continuous : continuous (fun z : K * V => z.1 *: z.2).
Admitted.

Arguments scale_continuous _ _ : clear implicits.

Lemma scaler_continuous k : continuous (fun x : V => k *: x).
Admitted.

Lemma scalel_continuous (x : V) : continuous (fun k : K => k *: x).
Admitted.

End NVS_continuity_normedModType.

Section NVS_continuity_mul.

Context {K : numFieldType}.

Lemma mul_continuous : continuous (fun z : K * K => z.1 * z.2).
Admitted.

Lemma mulrl_continuous (x : K) : continuous ( *%R x).
Admitted.

Lemma mulrr_continuous (y : K) : continuous ( *%R^~ y).
Admitted.

Lemma inv_continuous (x : K) : x != 0 -> {for x, continuous GRing.inv}.
Admitted.

End NVS_continuity_mul.

Section cvg_composition_pseudometric.

Context {K : numFieldType} {V : pseudoMetricNormedZmodType K} {T : Type}.
Context (F : set (set T)) {FF : Filter F}.
Implicit Types (f g : T -> V) (s : T -> K) (k : K) (x : T) (a b : V).

Lemma cvgN f a : f @ F --> a -> - f @ F --> - a.
Admitted.

Lemma cvgNP f a : - f @ F --> - a <-> f @ F --> a.
Admitted.

Lemma is_cvgN f : cvg (f @ F) -> cvg (- f @ F).
Admitted.

Lemma is_cvgNE f : cvg ((- f) @ F) = cvg (f @ F).
Admitted.

Lemma cvgMn f n a : f @ F --> a -> ((@GRing.natmul _)^~n \o f) @ F --> a *+ n.
Admitted.

Lemma is_cvgMn f n : cvg (f @ F) -> cvg (((@GRing.natmul _)^~n \o f) @ F).
Admitted.

Lemma cvgD f g a b : f @ F --> a -> g @ F --> b -> (f + g) @ F --> a + b.
Admitted.

Lemma is_cvgD f g : cvg (f @ F) -> cvg (g @ F) -> cvg (f + g @ F).
Admitted.

Lemma cvgB f g a b : f @ F --> a -> g @ F --> b -> (f - g) @ F --> a - b.
Admitted.

Lemma is_cvgB f g : cvg (f @ F) -> cvg (g @ F) -> cvg (f - g @ F).
Admitted.

Lemma is_cvgDlE f g : cvg (g @ F) -> cvg ((f + g) @ F) = cvg (f @ F).
Admitted.

Lemma is_cvgDrE f g : cvg (f @ F) -> cvg ((f + g) @ F) = cvg (g @ F).
Admitted.

Lemma cvg_sub0 f g a : (f - g) @ F --> (0 : V) -> g @ F --> a -> f @ F --> a.
Admitted.

Lemma cvg_zero f a : (f - cst a) @ F --> (0 : V) -> f @ F --> a.
Admitted.

Lemma cvg_norm f a : f @ F --> a -> `|f x| @[x --> F] --> (`|a| : K).
Admitted.

Lemma is_cvg_norm f : cvg (f @ F) -> cvg ((Num.norm \o f : T -> K) @ F).
Admitted.

Lemma norm_cvg0P f : `|f x| @[x --> F] --> 0 <-> f @ F --> 0.
Admitted.

Lemma norm_cvg0 f : `|f x| @[x --> F] --> 0 -> f @ F --> 0.
Admitted.

End cvg_composition_pseudometric.

Lemma __deprecated__cvg_dist0 {U} {K : numFieldType} {V : normedModType K}
  {F : set (set U)} {FF : Filter F} (f : U -> V) :
  (fun x => `|f x|) @ F --> (0 : K)
  -> f @ F --> (0 : V).
Admitted.
#[deprecated(since="mathcomp-analysis 0.6.0",
 note="renamed to `norm_cvg0` and generalized to `pseudoMetricNormedZmodType`")]
Notation cvg_dist0 := __deprecated__cvg_dist0.

Section cvg_composition_normed.
Context {K : numFieldType} {V : normedModType K} {T : Type}.
Context (F : set (set T)) {FF : Filter F}.
Implicit Types (f g : T -> V) (s : T -> K) (k : K) (x : T) (a b : V).

Lemma cvgZ s f k a : s @ F --> k -> f @ F --> a ->
                     s x *: f x @[x --> F] --> k *: a.
Admitted.

Lemma is_cvgZ s f : cvg (s @ F) ->
  cvg (f @ F) -> cvg ((fun x => s x *: f x) @ F).
Admitted.

Lemma cvgZl s k a : s @ F --> k -> s x *: a @[x --> F] --> k *: a.
Admitted.

Lemma is_cvgZl s a : cvg (s @ F) -> cvg ((fun x => s x *: a) @ F).
Admitted.

Lemma cvgZr k f a : f @ F --> a -> k \*: f @ F --> k *: a.
Admitted.

Lemma is_cvgZr k f : cvg (f @ F) -> cvg (k *: f  @ F).
Admitted.

Lemma is_cvgZrE k f : k != 0 -> cvg (k *: f @ F) = cvg (f @ F).
Admitted.

End cvg_composition_normed.

Section cvg_composition_field.
Context {K : numFieldType}  {T : Type}.
Context (F : set (set T)) {FF : Filter F}.
Implicit Types (f g : T -> K) (a b : K).

Lemma cvgV f a : a != 0 -> f @ F --> a -> f\^-1 @ F --> a^-1.
Admitted.

Lemma cvgVP f a : a != 0 -> f\^-1 @ F --> a^-1 <-> f @ F --> a.
Admitted.

Lemma is_cvgV f : lim (f @ F) != 0 -> cvg (f @ F) -> cvg (f\^-1 @ F).
Admitted.

Lemma cvgM f g a b : f @ F --> a -> g @ F --> b -> (f \* g) @ F --> a * b.
Admitted.

Lemma cvgMl f a b : f @ F --> a -> (f x * b) @[x --> F] --> a * b.
Admitted.

Lemma cvgMr g a b : g @ F --> b -> (a * g x) @[x --> F] --> a * b.
Admitted.

Lemma is_cvgM f g : cvg (f @ F) -> cvg (g @ F) -> cvg (f \* g @ F).
Admitted.

Lemma is_cvgMr g a (f := fun=> a) : cvg (g @ F) -> cvg (f \* g @ F).
Admitted.

Lemma is_cvgMrE g a (f := fun=> a) : a != 0 -> cvg (f \* g @ F) = cvg (g @ F).
Admitted.

Lemma is_cvgMl f a (g := fun=> a) : cvg (f @ F) -> cvg (f \* g @ F).
Admitted.

Lemma is_cvgMlE f a (g := fun=> a) : a != 0 -> cvg (f \* g @ F) = cvg (f @ F).
Admitted.

End cvg_composition_field.

Section limit_composition_pseudometric.

Context {K : numFieldType} {V : pseudoMetricNormedZmodType K} {T : Type}.
Context (F : set (set T)) {FF : ProperFilter F}.
Implicit Types (f g : T -> V) (s : T -> K) (k : K) (x : T) (a : V).

Lemma limN f : cvg (f @ F) -> lim (- f @ F) = - lim (f @ F).
Admitted.

Lemma limD f g : cvg (f @ F) -> cvg (g @ F) ->
   lim (f + g @ F) = lim (f @ F) + lim (g @ F).
Admitted.

Lemma limB f g : cvg (f @ F) -> cvg (g @ F) ->
   lim (f - g @ F) = lim (f @ F) - lim (g @ F).
Admitted.

Lemma lim_norm f : cvg (f @ F) -> lim ((fun x => `|f x| : K) @ F) = `|lim (f @ F)|.
Admitted.

End limit_composition_pseudometric.

Section limit_composition_normed.

Context {K : numFieldType} {V : normedModType K} {T : Type}.
Context (F : set (set T)) {FF : ProperFilter F}.
Implicit Types (f g : T -> V) (s : T -> K) (k : K) (x : T) (a : V).

Lemma limZ s f : cvg (s @ F) -> cvg (f @ F) ->
   lim ((fun x => s x *: f x) @ F) = lim (s @ F) *: lim (f @ F).
Admitted.

Lemma limZl s a : cvg (s @ F) ->
   lim ((fun x => s x *: a) @ F) = lim (s @ F) *: a.
Admitted.

Lemma limZr k f : cvg (f @ F) -> lim (k *: f @ F) = k *: lim (f @ F).
Admitted.

End limit_composition_normed.

Section limit_composition_field.

Context {K : numFieldType} {T : Type}.
Context (F : set (set T)) {FF : ProperFilter F}.
Implicit Types (f g : T -> K).

Lemma limM f g : cvg (f @ F) -> cvg (g @ F) ->
   lim (f \* g @ F) = lim (f @ F) * lim (g @ F).
Admitted.

End limit_composition_field.

Section cvg_composition_field_proper.

Context {K : numFieldType}  {T : Type}.
Context (F : set (set T)) {FF : ProperFilter F}.
Implicit Types (f g : T -> K) (a b : K).

Lemma limV f : lim (f @ F) != 0 -> lim (f\^-1 @ F) = (lim (f @ F))^-1.
Admitted.

Lemma is_cvgVE f : lim (f @ F) != 0 -> cvg (f\^-1 @ F) = cvg (f @ F).
Admitted.

End cvg_composition_field_proper.

Section ProperFilterRealType.
Context {T : Type} {F : set (set T)} {FF : ProperFilter F} {R : realFieldType}.
Implicit Types (f g h : T -> R) (a b : R).

Lemma cvgr_to_ge f a b : f @ F --> a -> (\near F, b <= f F) -> b <= a.
Admitted.

Lemma cvgr_to_le f a b : f @ F --> a -> (\near F, f F <= b) -> a <= b.
Admitted.

Lemma limr_ge x f : cvg (f @ F) -> (\near F, x <= f F) -> x <= lim (f @ F).
Admitted.

Lemma limr_le x f : cvg (f @ F) -> (\near F, x >= f F) -> x >= lim (f @ F).
Admitted.

Lemma __deprecated__cvg_gt_ge (u : T -> R) a b :
  u @ F --> b -> a < b -> \forall n \near F, a <= u n.
Admitted.

Lemma __deprecated__cvg_lt_le (u : T -> R) c b :
  u @ F --> b -> b < c -> \forall n \near F, u n <= c.
Admitted.

End ProperFilterRealType.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="renamed to `cvgr_ge` and generalized to a `Filter`")]
Notation cvg_gt_ge := __deprecated__cvg_gt_ge.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="renamed to `cvgr_le` and generalized to a `Filter`")]
Notation cvg_lt_le_:= __deprecated__cvg_lt_le.

Section local_continuity.

Context {K : numFieldType} {V : normedModType K} {T : topologicalType}.
Implicit Types (f g : T -> V) (s t : T -> K) (x : T) (k : K) (a : V).

Lemma continuousN (f : T -> V) x :
  {for x, continuous f} -> {for x, continuous (fun x => - f x)}.
Admitted.

Lemma continuousD f g x :
  {for x, continuous f} -> {for x, continuous g} ->
  {for x, continuous (f + g)}.
Admitted.

Lemma continuousB f g x :
  {for x, continuous f} -> {for x, continuous g} ->
  {for x, continuous (f - g)}.
Admitted.

Lemma continuousZ s f x :
  {for x, continuous s} -> {for x, continuous f} ->
  {for x, continuous (fun x => s x *: f x)}.
Admitted.

Lemma continuousZr f k x :
  {for x, continuous f} -> {for x, continuous (k \*: f)}.
Admitted.

Lemma continuousZl s a x :
  {for x, continuous s} -> {for x, continuous (fun z => s z *: a)}.
Admitted.

Lemma continuousM s t x :
  {for x, continuous s} -> {for x, continuous t} ->
  {for x, continuous (s * t)}.
Admitted.

Lemma continuousV s x : s x != 0 ->
  {for x, continuous s} -> {for x, continuous (fun x => (s x)^-1%R)}.
Admitted.

End local_continuity.

Section nbhs_ereal.
Context {R : numFieldType} (P : \bar R -> Prop).

Lemma nbhs_EFin (x : R) : (\forall y \near x%:E, P y) <-> \near x, P x%:E.
Admitted.

Lemma nbhs_ereal_pinfty :
  (\forall x \near +oo%E, P x) <-> [/\ P +oo%E & \forall x \near +oo, P x%:E].
Admitted.

Lemma nbhs_ereal_ninfty :
  (\forall x \near -oo%E, P x) <-> [/\ P -oo%E & \forall x \near -oo, P x%:E].
Admitted.
End nbhs_ereal.

Section cvg_fin.
Context {R : numFieldType}.

Section filter.
Context {F : set (set \bar R)} {FF : Filter F}.

Lemma fine_fcvg a : F --> a%:E -> fine @ F --> a.
Admitted.

Lemma fcvg_is_fine a : F --> a%:E -> \near F, F \is a fin_num.
Admitted.

End filter.

Section limit.
Context {I : Type} {F : set (set I)} {FF : Filter F} (f : I -> \bar R).

Lemma fine_cvg a : f @ F --> a%:E -> fine \o f @ F --> a.
Admitted.

Lemma cvg_is_fine a : f @ F --> a%:E -> \near F, f F \is a fin_num.
Admitted.

Lemma cvg_EFin a : (\near F, f F \is a fin_num) -> fine \o f @ F --> a ->
  f @ F --> a%:E.
Admitted.

Lemma fine_cvgP a :
   f @ F --> a%:E <-> (\near F, f F \is a fin_num) /\ fine \o f @ F --> a.
Admitted.

Lemma neq0_fine_cvgP a : a != 0 -> f @ F --> a%:E <-> fine \o f @ F --> a.
Admitted.

End limit.

End cvg_fin.

Lemma eq_cvg (T T' : Type) (F : set (set T)) (f g : T -> T') (x : set (set T')) :
  f =1 g -> (f @ F --> x) = (g @ F --> x).
Admitted.

Lemma eq_is_cvg (T T' : Type) (fT : filteredType T') (F : set (set T)) (f g : T -> T') :
  f =1 g -> [cvg (f @ F) in fT] = [cvg (g @ F) in fT].
Admitted.

Section ecvg_realFieldType.
Context {I} {F : set (set I)} {FF : Filter F} {R : realFieldType}.
Implicit Types f g u v : I -> \bar R.
Local Open Scope ereal_scope.

Lemma cvgeD f g a b :
  a +? b -> f @ F --> a -> g @ F --> b -> f \+ g @ F --> a + b.
Admitted.

Lemma cvgeN f x : f @ F --> x -> - f x @[x --> F] --> - x.
Admitted.

Lemma cvgeNP f a : - f x @[x --> F] --> - a <-> f @ F --> a.
Admitted.

Lemma cvgeB f g a b :
  a +? - b -> f @ F --> a -> g @ F --> b -> f \- g @ F --> a - b.
Admitted.

Lemma cvge_sub0 f (k : \bar R) :
  k \is a fin_num -> (fun x => f x - k) @ F --> 0 <-> f @ F --> k.
Admitted.

Lemma abse_continuous : continuous (@abse R).
Admitted.

Lemma cvg_abse f (a : \bar R) : f @ F --> a -> `|f x|%E @[x --> F] --> `|a|%E.
Admitted.

Lemma is_cvg_abse (f : I -> \bar R) : cvg (f @ F) -> cvg (`|f x|%E @[x --> F]).
Admitted.

Lemma is_cvgeN f : cvg (f @ F) -> cvg (\- f @ F).
Admitted.

Lemma is_cvgeNE f : cvg (\- f @ F) = cvg (f @ F).
Admitted.

Lemma mule_continuous (r : R) : continuous (mule r%:E).
Admitted.

Lemma cvgeMl f x y : y \is a fin_num ->
  f @ F --> x -> (fun n => y * f n) @ F --> y * x.
Admitted.

Lemma is_cvgeMl f y : y \is a fin_num ->
  cvg (f @ F) -> cvg ((fun n => y * f n) @ F).
Admitted.

Lemma cvgeMr f x y : y \is a fin_num ->
  f @ F --> x -> (fun n => f n * y) @ F --> x * y.
Admitted.

Lemma is_cvgeMr f y : y \is a fin_num ->
  cvg (f @ F) -> cvg ((fun n => f n * y) @ F).
Admitted.

Lemma cvg_abse0P f : abse \o f @ F --> 0 <-> f @ F --> 0.
Admitted.

Let cvgeM_gt0_pinfty f g b :
  (0 < b)%R -> f @ F --> +oo -> g @ F --> b%:E -> f \* g @ F --> +oo.
Admitted.

Let cvgeM_lt0_pinfty  f g b :
  (b < 0)%R -> f @ F --> +oo -> g @ F --> b%:E -> f \* g @ F --> -oo.
Admitted.

Let cvgeM_gt0_ninfty f g b :
  (0 < b)%R -> f @ F --> -oo -> g @ F --> b%:E -> f \* g @ F --> -oo.
Admitted.

Let cvgeM_lt0_ninfty f g b :
  (b < 0)%R -> f @ F --> -oo -> g @ F --> b%:E -> f \* g @ F --> +oo.
Admitted.

Lemma cvgeM f g (a b : \bar R) :
 a *? b -> f @ F --> a -> g @ F --> b -> f \* g @ F --> a * b.
Admitted.

End ecvg_realFieldType.

Section max_cts.
Context {R : realType} {T : topologicalType}.

Lemma continuous_min (f g : T -> R^o) x :
  {for x, continuous f} -> {for x, continuous g} ->
  {for x, continuous (f \min g)}.
Admitted.

Lemma continuous_max (f g : T -> R^o) x :
  {for x, continuous f} -> {for x, continuous g} ->
  {for x, continuous (f \max g)}.
Admitted.

End max_cts.

#[deprecated(since="mathcomp-analysis 0.6.0",
  note="renamed to cvgeN, and generalized to filter in Type")]
Notation ereal_cvgN := cvgeN.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="renamed to is_cvgeN, and generalized to filter in Type")]
Notation ereal_is_cvgN := is_cvgeN.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="renamed to cvgeMl, and generalized to filter in Type")]
Notation ereal_cvgrM := cvgeMl.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="renamed to is_cvgeMl, and generalized to filter in Type")]
Notation ereal_is_cvgrM := is_cvgeMl.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="renamed to cvgeMr, and generalized to filter in Type")]
Notation ereal_cvgMr := cvgeMr.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="renamed to is_cvgeMr, and generalized to filter in Type")]
Notation ereal_is_cvgMr := is_cvgeMr.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="renamed to cvgeM, and generalized to a realFieldType")]
Notation ereal_cvgM := cvgeM.

Section pseudoMetricDist.
Context {R : realType} {X : pseudoMetricType R}.
Implicit Types r : R.
Definition edist (xy : X * X) : \bar R. exact (ereal_inf (EFin @` [set r | 0 < r /\ ball xy.1 r xy.2])). Defined.

Lemma edist_ge0 (xy : X * X) : (0 <= edist xy)%E.
Admitted.
Hint Resolve edist_ge0 : core.

Lemma edist_neqNy (xy : X * X) : (edist xy != -oo)%E.
Admitted.
Hint Resolve edist_neqNy : core.

Lemma edist_lt_ball r (xy : X * X) : (edist xy < r%:E)%E -> ball xy.1 r xy.2.
Admitted.

Lemma edist_fin r (xy : X * X) :
  0 < r -> ball xy.1 r xy.2 -> (edist xy <= r%:E)%E.
Admitted.

Lemma edist_pinftyP (xy : X * X) :
  (edist xy = +oo)%E <-> (forall r, 0 < r -> ~ ball xy.1 r xy.2).
Admitted.

Lemma edist_finP (xy : X * X) :
  (edist xy \is a fin_num)%E <-> exists2 r, 0 < r & ball xy.1 r xy.2.
Admitted.

Lemma edist_fin_open : open [set xy : X * X | edist xy \is a fin_num].
Admitted.

Lemma edist_fin_closed : closed [set xy : X * X | edist xy \is a fin_num].
Admitted.

Lemma edist_pinfty_open : open [set xy : X * X | edist xy = +oo]%E.
Admitted.

Lemma edist_sym (x y : X) : edist (x, y) = edist (y, x).
Admitted.

Lemma edist_triangle (x y z : X) :
  (edist (x, z) <= edist (x, y) + edist (y, z))%E.
Admitted.

Lemma edist_continuous : continuous edist.
Admitted.

Lemma edist_closeP x y : close x y <-> edist (x, y) = 0%E.
Admitted.

Lemma edist_refl x : edist (x, x) = 0%E.
Admitted.

Lemma edist_closel x y z : close x y -> edist (x, z) = edist (y, z).
Admitted.

End pseudoMetricDist.
#[global]
Hint Extern 0 (is_true (0 <= edist _)%E) => solve [apply: edist_ge0] : core.
#[global]
Hint Extern 0 (is_true (edist _ != -oo%E)) => solve [apply: edist_neqNy] : core.

Section edist_inf.
Context {R : realType} {T : pseudoMetricType R} (A : set T).

Definition edist_inf z := ereal_inf [set edist (z, a) | a in A].

Lemma edist_inf_ge0 w : (0 <= edist_inf w)%E.
Admitted.
Hint Resolve edist_inf_ge0 : core.

Lemma edist_inf_neqNy w : (edist_inf w != -oo)%E.
Admitted.
Hint Resolve edist_inf_neqNy : core.

Lemma edist_inf_triangle x y : (edist_inf x <= edist (x, y) + edist_inf y)%E.
Admitted.

Lemma edist_inf_continuous : continuous edist_inf.
Admitted.

Lemma edist_inf0 a : A a -> edist_inf a = 0%E.
Admitted.

End edist_inf.
#[global]
Hint Extern 0 (is_true (0 <= edist_inf _ _)%E) =>
  solve [apply: edist_inf_ge0] : core.
#[global]
Hint Extern 0 (is_true (edist_inf _ _ != -oo%E)) =>
  solve [apply: edist_inf_neqNy] : core.

Section urysohn_separator.
Context {T : uniformType} {R : realType}.
Context (A B : set T) (E : set (T * T)).
Hypothesis entE : entourage E.
Hypothesis AB0 : A `*` B `&` E = set0.

Local Notation T' := (@gauge_pseudoMetricType _ _  entE R).

Local Lemma urysohn_separation : exists (f : T -> R),
  [/\ continuous f, range f `<=` `[0, 1],
      f @` A `<=` [set 0] & f @` B `<=` [set 1] ].
Admitted.

End urysohn_separator.

Section topological_urysohn_separator.
Context {T : topologicalType} {R : realType}.

Definition uniform_separator (A B : set T) :=
  exists (uT : @Uniform.class_of T^o) (E : set (T * T)),
    let UT := Uniform.Pack uT in [/\
      @entourage UT E, A `*` B `&` E = set0 &
      (forall x, @nbhs UT UT x `<=` @nbhs T T x)].

Local Lemma Urysohn' (A B : set T) : exists (f : T -> R),
    [/\ continuous f,
    range f `<=` `[0, 1]
    & uniform_separator A B ->
    f @` A `<=` [set 0] /\ f @` B `<=` [set 1]].
Admitted.
Definition Urysohn (A B : set T) : T -> R. exact (projT1 (cid (Urysohn' A B))). Defined.

Section urysohn_facts.

Lemma Urysohn_continuous (A B : set T) : continuous (Urysohn A B).
Admitted.

Lemma Urysohn_range (A B : set T) : range (Urysohn A B) `<=` `[0, 1].
Admitted.

Lemma Urysohn_sub0 (A B : set T) :
  uniform_separator A B -> Urysohn A B @` A `<=` [set 0].
Admitted.

Lemma Urysohn_sub1 (A B : set T) :
  uniform_separator A B -> Urysohn A B @` B `<=` [set 1].
Admitted.

Lemma Urysohn_eq0 (A B : set T) :
  uniform_separator A B -> A !=set0 -> Urysohn A B @` A = [set 0].
Admitted.

Lemma Urysohn_eq1 (A B : set T) :
  uniform_separator A B -> (B !=set0) -> (Urysohn A B) @` B = [set 1].
Admitted.

End urysohn_facts.
End topological_urysohn_separator.

Lemma uniform_separatorW {T : uniformType} (A B : set T) :
    (exists2 E, entourage E & A `*` B `&` E = set0) ->
  uniform_separator A B.
Admitted.

Section Urysohn.
Context {T : topologicalType} .
Hypothesis normalT : normal_space T.
Section normal_uniform_separators.
Context (A : set T).

Local Notation "A ^-1" := [set xy | A (xy.2, xy.1)] : classical_set_scope.

Local Notation "'to_set' A x" := [set y | A (x, y)]
  (at level 0, A at level 0) : classical_set_scope.
Let apxU (UV : set T * set T) : set (T * T). exact ((UV.2 `*` UV.2) `|` (~` closure UV.1 `*` ~` closure UV.1)). Defined.

Let nested (UV : set T * set T) :=
  [/\ open UV.1, open UV.2, A `<=` UV.1 & closure UV.1 `<=`UV.2].

Let ury_base := [set apxU UV | UV in nested].

Local Lemma ury_base_refl E :
  ury_base E -> [set fg | fg.1 = fg.2] `<=` E.
Admitted.

Local Lemma ury_base_inv E : ury_base E -> ury_base (E^-1)%classic.
Admitted.

Local Lemma ury_base_split E : ury_base E ->
  exists E1 E2, [/\ ury_base E1, ury_base E2 &
                    (E1 `&` E2) \; (E1 `&` E2) `<=` E].
Admitted.

Let ury_unif := smallest Filter ury_base.

Instance ury_unif_filter : Filter ury_unif.
Admitted.

Local Lemma ury_unif_refl E : ury_unif E -> [set fg | fg.1 = fg.2] `<=` E.
Admitted.

Local Lemma set_prod_invK (K : set (T * T)) : (K^-1^-1)%classic = K.
Admitted.

Local Lemma ury_unif_inv E : ury_unif E -> ury_unif (E^-1)%classic.
Admitted.

Local Lemma ury_unif_split_iter E n :
  filterI_iter ury_base n E -> exists2 K : set (T * T),
    filterI_iter ury_base n.+1 K & K\;K `<=` E.
Admitted.

Local Lemma ury_unif_split E : ury_unif E ->
  exists2 K, ury_unif K & K \; K `<=` E.
Admitted.

Local Lemma ury_unif_covA E : ury_unif E -> A `*` A `<=` E.
Admitted.

Let urysohn_uniformType_mixin :=
  UniformMixin ury_unif_filter ury_unif_refl ury_unif_inv ury_unif_split erefl.

Let urysohn_topologicalTypeMixin :=
  topologyOfEntourageMixin urysohn_uniformType_mixin.

Let urysohn_filtered := FilteredType T T (nbhs_ ury_unif).
Let urysohn_topologicalType :=
  TopologicalType urysohn_filtered urysohn_topologicalTypeMixin.
Let urysohn_uniformType := UniformType
  urysohn_topologicalType urysohn_uniformType_mixin.

Lemma normal_uniform_separator (B : set T) :
  closed A -> closed B -> A `&` B = set0 -> uniform_separator A B.
Admitted.

End normal_uniform_separators.
End Urysohn.
Lemma uniform_separatorP {T : topologicalType} {R : realType} (A B : set T) :
  uniform_separator A B <->
  exists (f : T -> R), [/\ continuous f, range f `<=` `[0, 1],
                           f @` A `<=` [set 0] & f @` B `<=` [set 1]].
Admitted.

Section normalP.
Context {T : topologicalType}.

Let normal_spaceP : [<->
    normal_space T;
    forall (A B : set T), closed A -> closed B -> A `&` B = set0 ->
    uniform_separator A B;
    forall (A B : set T), closed A -> closed B -> A `&` B = set0 ->
    exists U V, [/\ open U, open V, A `<=` U, B `<=` V & U `&` V = set0] ].
Admitted.

Lemma normal_openP : normal_space T <->
  forall (A B : set T), closed A -> closed B -> A `&` B = set0 ->
  exists U V, [/\ open U, open V, A `<=` U, B `<=` V & U `&` V = set0].
Admitted.

Lemma normal_separatorP : normal_space T <->
  forall (A B : set T), closed A -> closed B -> A `&` B = set0 ->
  uniform_separator A B.
Admitted.

End normalP.

Section pseudometric_normal.

Lemma uniform_regular {X : uniformType} : @regular_space X.
Admitted.

Lemma regular_openP {T : topologicalType} (x : T) :
  {for x, @regular_space T} <-> forall A, closed A -> ~ A x ->
  exists U V : set T, [/\ open U, open V, U x, A `<=` V & U `&` V = set0].
Admitted.

Lemma pseudometric_normal {R : realType} {X : pseudoMetricType R} :
  normal_space X.
Admitted.

End pseudometric_normal.

Section open_closed_sets_ereal.
Variable R : realFieldType  .
Local Open Scope ereal_scope.
Implicit Types x y : \bar R.
Implicit Types r : R.

Lemma open_ereal_lt y : open [set r : R | r%:E < y].
Admitted.

Lemma open_ereal_gt y : open [set r : R | y < r%:E].
Admitted.

Lemma open_ereal_lt' x y : x < y -> ereal_nbhs x (fun u => u < y).
Admitted.

Lemma open_ereal_gt' x y : y < x -> ereal_nbhs x (fun u => y < u).
Admitted.

Lemma open_ereal_lt_ereal x : open [set y | y < x].
Admitted.

Lemma open_ereal_gt_ereal x : open [set y | x < y].
Admitted.

Lemma closed_ereal_le_ereal y : closed [set x | y <= x].
Admitted.

Lemma closed_ereal_ge_ereal y : closed [set x | y >= x].
Admitted.

End open_closed_sets_ereal.

Section closure_left_right_open.
Variable R : realFieldType.
Implicit Types z : R.

Lemma closure_gt z : closure ([set x | z < x] : set R) = [set x | z <= x].
Admitted.

Lemma closure_lt z : closure ([set x : R | x < z]) = [set x | x <= z].
Admitted.

End closure_left_right_open.

Module CompleteNormedModule.

Section ClassDef.

Variable K : numFieldType.

Record class_of (T : Type) := Class {
  base : NormedModule.class_of K T ;
  mixin : Complete.axiom (PseudoMetric.Pack base)
}.
Local Coercion base : class_of >-> NormedModule.class_of.
Definition base2 T (cT : class_of T) : CompletePseudoMetric.class_of K T. exact (@CompletePseudoMetric.Class _ _ (@base T cT) (@mixin T cT)). Defined.
Local Coercion base2 : class_of >-> CompletePseudoMetric.class_of.

Structure type (phK : phant K) := Pack { sort; _ : class_of sort }.
Local Coercion sort : type >-> Sortclass.

Variables (phK : phant K) (cT : type phK) (T : Type).

Definition class := let: Pack _ c := cT return class_of cT in c.

Definition pack :=
  fun bT (b : NormedModule.class_of K T) & phant_id (@NormedModule.class K phK bT) b =>
  fun mT m & phant_id (@Complete.class mT) (@Complete.Class T b m) =>
    Pack phK (@Class T b m).
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition zmodType := @GRing.Zmodule.Pack cT xclass.
Definition normedZmodType := @Num.NormedZmodule.Pack K phK cT xclass.
Definition lmodType := @GRing.Lmodule.Pack K phK cT xclass.
Definition pointedType := @Pointed.Pack cT xclass.
Definition filteredType := @Filtered.Pack cT cT xclass.
Definition topologicalType := @Topological.Pack cT xclass.
Definition uniformType := @Uniform.Pack cT xclass.
Definition pseudoMetricType := @PseudoMetric.Pack K cT xclass.
Definition pseudoMetricNormedZmodType :=
  @PseudoMetricNormedZmodule.Pack K phK cT xclass.
Definition normedModType := @NormedModule.Pack K phK cT xclass.
Definition completeType := @Complete.Pack cT xclass.
Definition completePseudoMetricType := @CompletePseudoMetric.Pack K cT xclass.
Definition complete_zmodType := @GRing.Zmodule.Pack completeType xclass.
Definition complete_lmodType := @GRing.Lmodule.Pack K phK completeType xclass.
Definition complete_normedZmodType := @Num.NormedZmodule.Pack K phK completeType xclass.
Definition complete_pseudoMetricNormedZmodType :=
  @PseudoMetricNormedZmodule.Pack K phK completeType xclass.
Definition complete_normedModType := @NormedModule.Pack K phK completeType xclass.
Definition completePseudoMetric_lmodType : GRing.Lmodule.type phK. exact (@GRing.Lmodule.Pack K phK (CompletePseudoMetric.sort completePseudoMetricType)
  xclass). Defined.
Definition completePseudoMetric_zmodType : GRing.Zmodule.type. exact (@GRing.Zmodule.Pack (CompletePseudoMetric.sort completePseudoMetricType)
  xclass). Defined.
Definition completePseudoMetric_normedModType : NormedModule.type phK. exact (@NormedModule.Pack K phK (CompletePseudoMetric.sort completePseudoMetricType)
  xclass). Defined.
Definition completePseudoMetric_normedZmodType : Num.NormedZmodule.type phK. exact (@Num.NormedZmodule.Pack K phK
  (CompletePseudoMetric.sort completePseudoMetricType) xclass). Defined.
Definition completePseudoMetric_pseudoMetricNormedZmodType :
  PseudoMetricNormedZmodule.type phK. exact (@PseudoMetricNormedZmodule.Pack K phK
  (CompletePseudoMetric.sort completePseudoMetricType) xclass). Defined.
End ClassDef.

Module Export Exports.

Coercion base : class_of >-> NormedModule.class_of.
Coercion base2 : class_of >-> CompletePseudoMetric.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion pseudoMetricNormedZmodType : type >-> PseudoMetricNormedZmodule.type.
Canonical pseudoMetricNormedZmodType.
Coercion normedZmodType : type >-> Num.NormedZmodule.type.
Canonical normedZmodType.
Coercion lmodType : type >-> GRing.Lmodule.type.
Canonical lmodType.
Coercion pointedType : type >-> Pointed.type.
Canonical pointedType.
Coercion filteredType : type >-> Filtered.type.
Canonical filteredType.
Coercion topologicalType : type >-> Topological.type.
Canonical topologicalType.
Coercion uniformType : type >-> Uniform.type.
Canonical uniformType.
Coercion pseudoMetricType : type >-> PseudoMetric.type.
Canonical pseudoMetricType.
Coercion normedModType : type >-> NormedModule.type.
Canonical normedModType.
Coercion completeType : type >-> Complete.type.
Canonical completeType.
Coercion completePseudoMetricType : type >-> CompletePseudoMetric.type.
Canonical completePseudoMetricType.
Canonical complete_zmodType.
Canonical complete_lmodType.
Canonical complete_normedZmodType.
Canonical complete_pseudoMetricNormedZmodType.
Canonical complete_normedModType.
Canonical completePseudoMetric_lmodType.
Canonical completePseudoMetric_zmodType.
Canonical completePseudoMetric_normedModType.
Canonical completePseudoMetric_normedZmodType.
Canonical completePseudoMetric_pseudoMetricNormedZmodType.
Notation completeNormedModType K := (type (Phant K)).
Notation "[ 'completeNormedModType' K 'of' T ]" := (@pack _ (Phant K) T _ _ idfun _ _ idfun)
  (at level 0, format "[ 'completeNormedModType'  K  'of'  T ]") : form_scope.
End Exports.

End CompleteNormedModule.

Export CompleteNormedModule.Exports.

Lemma R_complete (R : realType) (F : set (set R)) : ProperFilter F -> cauchy F -> cvg F.
Admitted.

Canonical R_regular_completeType (R : realType) :=
  CompleteType R^o (@R_complete R).

Canonical R_regular_CompleteNormedModule (R : realType) :=
  [completeNormedModType R of R^o].

Canonical R_completeType (R : realType) :=
  [completeType of R for [completeType of R^o]].
Canonical R_CompleteNormedModule (R : realType) :=
  [completeNormedModType R of R].

Section cvg_seq_bounded.
Context {K : numFieldType}.
Local Notation "'+oo'" := (@pinfty_nbhs K).

Lemma cvg_seq_bounded {V : normedModType K} (a : nat -> V) :
  cvg a -> bounded_fun a.
Admitted.

End cvg_seq_bounded.

Lemma closure_sup (R : realType) (A : set R) :
  A !=set0 -> has_ubound A -> closure A (sup A).
Admitted.

Lemma near_infty_natSinv_lt (R : archiFieldType) (e : {posnum R}) :
  \forall n \near \oo, n.+1%:R^-1 < e%:num.
Admitted.

Lemma near_infty_natSinv_expn_lt (R : archiFieldType) (e : {posnum R}) :
  \forall n \near \oo, 1 / 2 ^+ n < e%:num.
Admitted.

Lemma limit_pointP (T : archiFieldType) (A : set T) (x : T) :
  limit_point A x <-> exists a_ : nat -> T,
    [/\ a_ @` setT `<=` A, forall n, a_ n != x & a_ --> x].
Admitted.

Section interval.
Variable R : numDomainType.

Definition is_interval (E : set R) :=
  forall x y, E x -> E y -> forall z, x <= z <= y -> E z.

Lemma is_intervalPlt (E : set R) :
  is_interval E <-> forall x y, E x -> E y -> forall z, x < z < y -> E z.
Admitted.

Lemma interval_is_interval (i : interval R) : is_interval [set` i].
Admitted.

End interval.

Section ereal_is_hausdorff.
Variable R : realFieldType.
Implicit Types r : R.

Lemma nbhs_image_EFin (x : R) (X : set R) :
  nbhs x X -> nbhs x%:E ((fun r => r%:E) @` X).
Admitted.

Lemma nbhs_open_ereal_lt r (f : R -> R) : r < f r ->
  nbhs r%:E [set y | y < (f r)%:E]%E.
Admitted.

Lemma nbhs_open_ereal_gt r (f : R -> R) : f r < r ->
  nbhs r%:E [set y | (f r)%:E < y]%E.
Admitted.

Lemma nbhs_open_ereal_pinfty r : (nbhs +oo [set y | r%:E < y])%E.
Admitted.

Lemma nbhs_open_ereal_ninfty r : (nbhs -oo [set y | y < r%:E])%E.
Admitted.

Lemma ereal_hausdorff : hausdorff_space (ereal_topologicalType R).
Admitted.

End ereal_is_hausdorff.

#[global]
Hint Extern 0 (hausdorff_space _) => solve[apply: ereal_hausdorff] : core.

#[deprecated(since="mathcomp-analysis 0.6.0",
  note="renamed to `nbhs_image_EFin`")]
Notation nbhs_image_ERFin := nbhs_image_EFin.

Lemma EFin_lim (R : realFieldType) (f : nat -> R) : cvg f ->
  lim (EFin \o f) = (lim f)%:E.
Admitted.

Section ProperFilterERealType.
Context {T : Type} {a : set (set T)} {Fa : ProperFilter a} {R : realFieldType}.
Local Open Scope ereal_scope.
Implicit Types f g h : T -> \bar R.

Lemma cvge_to_ge f b c : f @ a --> c -> (\near a, b <= f a) -> b <= c.
Admitted.

Lemma cvge_to_le f b c : f @ a --> c -> (\near a, f a <= b) -> c <= b.
Admitted.

Lemma lime_ge x f : cvg (f @ a) -> (\near a, x <= f a) -> x <= lim (f @ a).
Admitted.

Lemma lime_le x f : cvg (f @ a) -> (\near a, x >= f a) -> x >= lim (f @ a).
Admitted.

End ProperFilterERealType.

Section ecvg_realFieldType_proper.
Context {I} {F : set (set I)} {FF : ProperFilter F} {R : realFieldType}.
Implicit Types (f g : I -> \bar R) (u v : I -> R) (x : \bar R) (r : R).
Local Open Scope ereal_scope.

Lemma is_cvgeD f g :
  lim (f @ F) +? lim (g @ F) -> cvg (f @ F) -> cvg (g @ F) -> cvg (f \+ g @ F).
Admitted.

Lemma limeD f g :
  cvg (f @ F) -> cvg (g @ F) -> lim (f @ F) +? lim (g @ F) ->
  lim (f \+ g @ F) = lim (f @ F) + lim (g @ F).
Admitted.

Lemma limeMl f y : y \is a fin_num -> cvg (f @ F) ->
  lim ((fun n => y * f n) @ F) = y * lim (f @ F).
Admitted.

Lemma limeMr f y : y \is a fin_num -> cvg (f @ F) ->
  lim ((fun n => f n * y) @ F) = lim (f @ F) * y.
Admitted.

Lemma is_cvgeM f g :
  lim (f @ F) *? lim (g @ F) -> cvg (f @ F) -> cvg (g @ F) -> cvg (f \* g @ F).
Admitted.

Lemma limeM f g :
  cvg (f @ F) -> cvg (g @ F) -> lim (f @ F) *? lim (g @ F) ->
  lim (f \* g @ F) = lim (f @ F) * lim (g @ F).
Admitted.

Lemma limeN f : cvg (f @ F) -> lim (\- f @ F) = - lim (f @ F).
Admitted.

Lemma cvge_ge f a b : (\forall x \near F, b <= f x) -> f @ F --> a -> b <= a.
Admitted.

Lemma cvge_le f a b : (\forall x \near F, b >= f x) -> f @ F --> a -> b >= a.
Admitted.

Lemma cvg_nnesum (J : Type) (r : seq J) (f : J -> I -> \bar R)
   (l : J -> \bar R) (P : pred J) :
  (forall j, P j -> \near F, 0 <= f j F) ->
  (forall j, P j -> f j @ F --> l j) ->
  \sum_(j <- r | P j) f j i @[i --> F] --> \sum_(j <- r | P j) l j.
Admitted.

Lemma lim_nnesum (J : Type) (r : seq J) (f : J -> I -> \bar R)
   (l : J -> \bar R) (P : pred J) :
  (forall j, P j -> \near F, 0 <= f j F) ->
  (forall j, P j -> cvg (f j @ F)) ->
  lim (\sum_(j <- r | P j) f j i @[i --> F]) = \sum_(j <- r | P j) (lim (f j @ F)).
Admitted.

End ecvg_realFieldType_proper.

#[deprecated(since="mathcomp-analysis 0.6.0", note="generalized to `limeMl`")]
Notation ereal_limrM := limeMl.
#[deprecated(since="mathcomp-analysis 0.6.0", note="generalized to `limeMr`")]
Notation ereal_limMr := limeMr.
#[deprecated(since="mathcomp-analysis 0.6.0", note="generalized to `limeN`")]
Notation ereal_limN := limeN.

Section cvg_0_pinfty.
Context {R : realFieldType} {I : Type} {a : set (set I)} {FF : Filter a}.
Implicit Types f : I -> R.

Lemma gtr0_cvgV0 f : (\near a, 0 < f a) -> f\^-1 @ a --> 0 <-> f @ a --> +oo.
Admitted.

Lemma cvgrVy f : (\near a, 0 < f a) -> f\^-1 @ a --> +oo <-> f @ a --> 0.
Admitted.

Lemma ltr0_cvgV0 f : (\near a, 0 > f a) -> f\^-1 @ a --> 0 <-> f @ a --> -oo.
Admitted.

Lemma cvgrVNy f : (\near a, 0 > f a) -> f\^-1 @ a --> -oo <-> f @ a --> 0.
Admitted.

End cvg_0_pinfty.

Section FilterRealType.

End FilterRealType.

Section TopoProperFilterRealType.

End TopoProperFilterRealType.

Section FilterERealType.

End FilterERealType.

Section TopoProperFilterERealType.

End TopoProperFilterERealType.

Section open_union_rat.

End open_union_rat.

Section interval_realType.
End interval_realType.

Section segment.

End segment.

Section Shift.

End Shift.

Section continuous.

End continuous.

Section Closed_Ball.

End Closed_Ball.

Section image_interval.

End image_interval.

Section LinearContinuousBounded.

End LinearContinuousBounded.

End normedtype.

End mathcomp_DOT_analysis_DOT_normedtype_WRAPPED.
Module Export mathcomp.
Module Export analysis.
Module normedtype.
Include mathcomp_DOT_analysis_DOT_normedtype_WRAPPED.normedtype.
End normedtype.
Import HB.structures.
Import mathcomp.ssreflect.all_ssreflect.
Import mathcomp.algebra.ssralg.
Import mathcomp.algebra.ssrnum.
Import mathcomp.algebra.ssrint.
Import mathcomp.algebra.interval.
Import mathcomp.classical.classical_sets.
Import mathcomp.classical.cardinality.
Import mathcomp.classical.set_interval.
Import mathcomp.analysis.signed.
Import mathcomp.analysis.reals.
Import mathcomp.analysis.topology.
Import mathcomp.analysis.normedtype.
Import Order.TTheory.
Import GRing.Theory.
Import Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Definition indic {T} {R : ringType} (A : set T) (x : T) : R.
Admitted.
Reserved Notation "'\1_' A" (at level 8, A at level 2, format "'\1_' A") .
Notation "'\1_' A" := (indic A) : ring_scope.

HB.factory Record FiniteDecomp (T : pointedType) (R : ringType) (f : T -> R) :=
  { fimfunE : exists (r : seq R) (A_ : R -> set T),
      forall x, f x = \sum_(y <- r) (y * \1_(A_ y) x) }.
HB.builders Context T R f of @FiniteDecomp T R f.
  Lemma finite_subproof: @FiniteImage T R f.
Admitted.
  HB.instance Definition _ := finite_subproof.
HB.end.

Section Tietze.
Context {X : topologicalType} {R : realType}.

Lemma urysohn_ext_itv A B x y :
  closed A -> closed B -> A `&` B = set0 -> x < y ->
  exists f : X -> R, [/\ continuous f,
    f @` A `<=` [set x], f @` B `<=` [set y] & range f `<=` `[x, y]].
Admitted.

Context (A : set X).
Hypothesis clA : closed A.

Local Lemma tietze_step' (f : X -> R) (M : R) :
  0 < M -> {within A, continuous f} ->
  (forall x, A x -> `|f x| <= M) ->
  exists g : X -> R, [/\ continuous g,
     (forall x, A x -> `|f x - g x| <= 2/3 * M) &
     (forall x, `|g x| <= 1/3 * M)].
Proof.
move: M => _/posnumP[M] ctsf fA1.
have [] := @urysohn_ext_itv (A `&` f @^-1` `]-oo, -(1/3) * M%:num])
    (A `&` f @^-1` `[1/3 * M%:num,+oo[) (-(1/3) * M%:num) (1/3 * M%:num).
-
 by rewrite closed_setSI; exact: closed_comp.
-
 by rewrite closed_setSI; apply: closed_comp => //; exact: interval_closed.
-
 rewrite setIACA -preimage_setI eqEsubset; split => z // [_ []].
  rewrite !set_itvE/= => /[swap] /le_trans /[apply].
  by rewrite leNgt mulNr gtr_opp// mulr_gt0// divr_gt0.
-
 by rewrite mulNr gtr_opp// mulr_gt0.
move=> g [ctsg gL3 gR3 grng]; exists g; split => //; first last.
  by move=> x; rewrite ler_norml -mulNr; apply: grng; exists x.
move=> x Ax; have := fA1 _ Ax; rewrite 2!ler_norml => /andP[Mfx fxM].
have [xL|xL] := leP (f x) (-(1/3) * M%:num).
  have: [set g x | x in A `&` f@^-1` `]-oo, -(1/3) * M%:num]] (g x) by exists x.
  move/gL3=> ->; rewrite !mulNr opprK; apply/andP; split.
    by rewrite -ler_subl_addr -opprD -2!mulrDl natr1 divrr ?unitfE// mul1r.
  rewrite -ler_subr_addr -2!mulrBl -(@natrB _ 2 1)// (le_trans xL)//.
  by rewrite ler_pmul2r// ltW// gtr_opp// divr_gt0.
have [xR|xR] := lerP (1/3 * M%:num) (f x).
  have : [set g x | x in A `&` f@^-1` `[1/3 * M%:num, +oo[] (g x).
    by exists x => //; split => //; rewrite /= in_itv //= xR.
  move/gR3 => ->; apply/andP; split.
    rewrite ler_subr_addl -2!mulrBl (le_trans _ xR)// ler_pmul2r//.
    by rewrite ler_wpmul2r ?invr_ge0 ?ler0n// ler_subl_addl natr1 ler1n.
  by rewrite ler_subl_addl -2!mulrDl nat1r divrr ?mul1r// unitfE.
have /andP[ng3 pg3] : -(1/3) * M%:num <= g x <= 1/3 * M%:num.
  by apply: grng; exists x.
rewrite (intrD _ 1 1) !mulrDl; apply/andP; split.
