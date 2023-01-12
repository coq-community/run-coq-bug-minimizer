(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "-deprecated-native-compiler-option" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/category_theory" "Category" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Equations" "Equations" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-top" "Top.bug_01" "-native-compiler" "no") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 255 lines to 43 lines, then from 56 lines to 364 lines, then from 369 lines to 54 lines, then from 67 lines to 188 lines, then from 193 lines to 74 lines, then from 87 lines to 179 lines, then from 185 lines to 82 lines, then from 95 lines to 219 lines, then from 224 lines to 120 lines, then from 133 lines to 269 lines, then from 274 lines to 169 lines *)
(* coqc version 8.18+alpha compiled with OCaml 4.09.0
   coqtop version runner-htnstaz1-project-6138686-concurrent-0:/builds/coq/coq/_build/default,(HEAD detached at fd69eda) (fd69edad0ac6cff8cb0cad43426d6b7b44adc0f8)
   Expected coqc runtime on this file: 31.193 sec *)
Require Coq.Lists.List.
Require Coq.Bool.Bool.
Require Coq.Program.Program.
Require Coq.Classes.CMorphisms.
Require Category.Lib.Foundation.
Require Category.Lib.Setoid.
Require Category.Lib.Tactics.
Require Category.Lib.Datatypes.
Require Category.Lib.
Require Category.Theory.Category.
Require Category.Theory.Morphisms.
Require Category.Theory.Isomorphism.
Require Category.Construction.Opposite.
Require Category.Theory.Functor.
Require Category.Construction.Product.
Require Category.Functor.Bifunctor.
Require Category.Structure.Monoidal.
Require Category.Theory.Naturality.
Require Category.Structure.Monoidal.Naturality.
Require Category.Structure.Monoidal.Braided.
Require Category.Structure.Monoidal.Balanced.

Declare ML Module "coq-core.plugins.ltac".
Module Export AdmitTactic.
Module Import LocalFalse.
Inductive False : Prop := .
End LocalFalse.
Axiom proof_admitted : False.
Global Set Default Proof Mode "Classic".
Tactic Notation "admit" := abstract case proof_admitted.
End AdmitTactic.

Module Export Category_DOT_Structure_DOT_Monoidal_DOT_Symmetric_WRAPPED.
Module Export Symmetric.
Import Category.Lib.
Import Category.Theory.Category.
Import Category.Theory.Functor.
Export Category.Structure.Monoidal.Braided.

Section SymmetricMonoidal.

Context {C : Category}.

Class SymmetricMonoidal := {
  symmetric_is_braided : @BraidedMonoidal C;

  braid_invol {x y} : braid ∘ braid ≈ id[x ⨂ y];
}.
#[export] Existing Instance symmetric_is_braided.

End SymmetricMonoidal.
Import Category.Lib.
Import Category.Theory.Category.
Import Category.Theory.Isomorphism.
Import Category.Theory.Functor.
Import Category.Theory.Naturality.

Section RelevanceMonoidal.

Context {C : Category}.

Class RelevanceMonoidal := {
  relevance_is_symmetric : @SymmetricMonoidal C;

  diagonal {x} : x ~> x ⨂ x;
  diagonal_natural : natural (@diagonal);

  diagonal_unit : @diagonal I ≈ unit_left⁻¹;

  diagonal_tensor_assoc {x} :
   id ⨂ diagonal ∘ diagonal ≈ tensor_assoc ∘ diagonal ⨂ id ∘ @diagonal x;

  braid_diagonal {x} :
    braid ∘ diagonal ≈ @diagonal x;

  braid2 {x y z w} : (x ⨂ y) ⨂ (z ⨂ w) ~> (x ⨂ z) ⨂ (y ⨂ w) :=
    tensor_assoc⁻¹
      ∘ id ⨂ (tensor_assoc ∘ braid ⨂ id ∘ tensor_assoc⁻¹)
      ∘ tensor_assoc;

  diagonal_braid2 {x y} :
    @diagonal (x ⨂ y) ≈ braid2 ∘ diagonal ⨂ diagonal
}.
#[export] Existing Instance relevance_is_symmetric.

Context `{RelevanceMonoidal}.

Lemma braid2_natural : natural (@braid2 _).
Admitted.

End RelevanceMonoidal.

Notation "∆ x" := (@diagonal _ _ x)
  (at level 9, format "∆ x") : morphism_scope.

Generalizable All Variables.

Class SemicartesianMonoidal `{@Monoidal C} := {
  eliminate {x} : x ~> I;

  unit_terminal {x} (f g : x ~> I) : f ≈ g;

  proj_left  {x y} : x ⨂ y ~> x := unit_right ∘ id ⨂ eliminate;
  proj_right {x y} : x ⨂ y ~> y := unit_left  ∘ eliminate ⨂ id
}.

Section CartesianMonoidal.

Context {C : Category}.

Class CartesianMonoidal := {
  cartesian_is_relevance     : @RelevanceMonoidal C;
  cartesian_is_semicartesian : @SemicartesianMonoidal C _;

  proj_left_diagonal  {x} : proj_left  ∘ diagonal ≈ id[x];
  proj_right_diagonal {x} : proj_right ∘ diagonal ≈ id[x];

  unit_left_braid  {x} : unit_left  ∘ @braid _ _ x I ≈ unit_right;
  unit_right_braid {x} : unit_right ∘ @braid _ _ I x ≈ unit_left
}.
#[export] Existing Instance cartesian_is_semicartesian.
#[export] Existing Instance cartesian_is_relevance.

End CartesianMonoidal.

Section MonoidalProofs.

Context `{M : @Monoidal C}.

Theorem triangle_identity_left {x y} :
  unit_left ⨂ id
    << (I ⨂ x) ⨂ y ~~> x ⨂ y >>
  unit_left ∘ tensor_assoc.
Admitted.

End MonoidalProofs.
Import Category.Functor.Bifunctor.

Context `{@CartesianMonoidal C}.

Lemma eliminate_left_diagonal {x} :
  eliminate ⨂ id[x] ∘ ∆x ≈ unit_left⁻¹.
Admitted.

Lemma proj_right_id_diagonal {x y} :
  proj_right ⨂ id ∘ ∆(x ⨂ y)
    ≈ tensor_assoc ∘ braid ⨂ id ∘ tensor_assoc⁻¹ ∘ id[x] ⨂ ∆y.
Proof.
  rewrite diagonal_braid2.
  remember (_ ∘ _ ∘ tensor_assoc) as p.
  spose (@braid2_natural _ _ x _ eliminate x _ id y _ id y _ id) as X0.
  rewrite !bimap_id_id in X0.
  rewrite !id_right in X0.
  unfold braid2 in X0.
  unfold proj_right.
  normal.
  rewrite bimap_comp_id_right.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc ((_ ⨂ _) ⨂ _)).
  rewrite Heqp; clear Heqp p.
  rewrite X0; clear X0.
  normal.
  rewrite eliminate_left_diagonal.
  rewrite triangle_identity_left.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc tensor_assoc).
  rewrite iso_to_from.
