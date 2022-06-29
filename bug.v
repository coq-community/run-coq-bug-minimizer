(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-noinit" "-indices-matter" "-type-in-type" "-w" "-notation-overridden" "-w" "-deprecated-native-compiler-option" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/unimath/UniMath" "UniMath" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-top" "bug_01" "-native-compiler" "no") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 1132 lines to 869 lines, then from 882 lines to 1044 lines, then from 1046 lines to 988 lines, then from 1001 lines to 1113 lines, then from 1117 lines to 1035 lines, then from 1048 lines to 1293 lines, then from 1297 lines to 1199 lines, then from 1212 lines to 1343 lines, then from 1348 lines to 1241 lines, then from 1254 lines to 1474 lines, then from 1478 lines to 1379 lines, then from 1392 lines to 1626 lines, then from 1628 lines to 1557 lines, then from 1570 lines to 1873 lines, then from 1875 lines to 1753 lines, then from 1766 lines to 2142 lines, then from 2122 lines to 2038 lines, then from 2051 lines to 4370 lines, then from 4339 lines to 4887 lines, then from 4900 lines to 5446 lines, then from 5450 lines to 5342 lines, then from 5341 lines to 5295 lines, then from 5308 lines to 5295 lines, then from 5308 lines to 5602 lines, then from 5603 lines to 5620 lines, then from 5607 lines to 5520 lines, then from 5533 lines to 5520 lines, then from 5533 lines to 6859 lines, then from 6850 lines to 6907 lines *)
(* coqc version 8.17+alpha compiled with OCaml 4.14.0
   coqtop version 
   Expected coqc runtime on this file: 17.658 sec *)
Require Coq.Init.Logic.
Require Coq.Init.Notations.
Require Coq.Init.Ltac.
Require UniMath.Foundations.Init.
Require UniMath.Foundations.Preamble.
Require UniMath.Foundations.PartA.
Require UniMath.Foundations.PartB.
Require UniMath.Foundations.UnivalenceAxiom.
Require UniMath.Foundations.PartC.
Require UniMath.Foundations.PartD.
Require UniMath.Foundations.UnivalenceAxiom2.
Require UniMath.Foundations.Propositions.
Require UniMath.Foundations.Sets.
Require UniMath.Foundations.NaturalNumbers.
Require UniMath.Foundations.HLevels.
Require UniMath.Foundations.All.
Require UniMath.MoreFoundations.Bool.
Require UniMath.MoreFoundations.WeakEquivalences.
Require UniMath.MoreFoundations.Tactics.
Require UniMath.MoreFoundations.PartA.
Require UniMath.MoreFoundations.PathsOver.
Require UniMath.MoreFoundations.Nat.
Require UniMath.MoreFoundations.Notations.
Require UniMath.MoreFoundations.AlternativeProofs.
Require UniMath.MoreFoundations.Subposets.
Require UniMath.MoreFoundations.DoubleNegation.
Require UniMath.MoreFoundations.DecidablePropositions.
Require UniMath.MoreFoundations.Propositions.
Require UniMath.MoreFoundations.NullHomotopies.
Require UniMath.MoreFoundations.Interval.
Require UniMath.MoreFoundations.NegativePropositions.
Require UniMath.MoreFoundations.Sets.
Require UniMath.MoreFoundations.Equivalences.
Require UniMath.MoreFoundations.MoreEquivalences.
Require UniMath.MoreFoundations.QuotientSet.
Require UniMath.MoreFoundations.Subtypes.
Require UniMath.MoreFoundations.AxiomOfChoice.
Require UniMath.MoreFoundations.StructureIdentity.
Require UniMath.MoreFoundations.Univalence.
Require UniMath.MoreFoundations.NoInjectivePairing.
Require UniMath.MoreFoundations.PartD.
Require UniMath.MoreFoundations.All.
Require UniMath.CategoryTheory.Core.Categories.
Require UniMath.CategoryTheory.Core.Isos.
Require UniMath.CategoryTheory.Core.Univalence.
Require UniMath.CategoryTheory.Core.TransportMorphisms.
Require UniMath.CategoryTheory.Core.Functors.
Require UniMath.CategoryTheory.Core.NaturalTransformations.
Require UniMath.CategoryTheory.FunctorCategory.
Require UniMath.CategoryTheory.opp_precat.

Declare ML Module "coq-core.plugins.ltac".
Module Export AdmitTactic.
Module Import LocalFalse.
Inductive False : Prop := .
End LocalFalse.
Axiom proof_admitted : False.
Global Set Default Proof Mode "Classic".
Tactic Notation "admit" := abstract case proof_admitted.
End AdmitTactic.

Module Export UniMath_DOT_CategoryTheory_DOT_PrecategoryBinProduct_WRAPPED.
Module Export PrecategoryBinProduct.
 

 
Import UniMath.Foundations.All.
Import UniMath.MoreFoundations.All.
Import UniMath.CategoryTheory.Core.Categories.
Import UniMath.CategoryTheory.Core.Isos.
Import UniMath.CategoryTheory.Core.Univalence.
Import UniMath.CategoryTheory.Core.Functors.
Import UniMath.CategoryTheory.Core.NaturalTransformations.
Import UniMath.CategoryTheory.FunctorCategory.
Import UniMath.CategoryTheory.opp_precat.
Local Open Scope cat.

Definition precategory_binproduct_mor (C D : precategory_ob_mor) (cd cd' : C × D) := pr1 cd --> pr1 cd' × pr2 cd --> pr2 cd'.

Definition precategory_binproduct_ob_mor (C D : precategory_ob_mor) : precategory_ob_mor
  := tpair _ _ (precategory_binproduct_mor C D).

Definition precategory_binproduct_data (C D : precategory_data) : precategory_data.
Proof.
  exists (precategory_binproduct_ob_mor C D).
  split.
  -
 intro cd.
    exact (make_dirprod (identity (pr1 cd)) (identity (pr2 cd))).
  -
 intros cd cd' cd'' fg fg'.
    exact (make_dirprod (pr1 fg · pr1 fg') (pr2 fg · pr2 fg')).
Defined.

Section precategory_binproduct.

Variables C D : precategory.

Lemma is_precategory_precategory_binproduct_data : is_precategory (precategory_binproduct_data C D).
Proof.
  repeat split; intros.
  -
 apply dirprodeq; apply id_left.
  -
 apply dirprodeq; apply id_right.
  -
 apply dirprodeq; apply assoc.
  -
 apply dirprodeq; apply assoc'.
Defined.
 

Definition precategory_binproduct : precategory
  := tpair _ _ is_precategory_precategory_binproduct_data.

Definition has_homsets_precategory_binproduct (hsC : has_homsets C) (hsD : has_homsets D) :
  has_homsets precategory_binproduct.
Proof.
  intros a b.
  apply isasetdirprod.
  -
 apply hsC.
  -
 apply hsD.
Qed.

End precategory_binproduct.

Definition category_binproduct (C D : category) : category :=
    make_category (precategory_binproduct C D) (has_homsets_precategory_binproduct C D C D).

Definition ob1 {C D} (x : category_binproduct C D) : C := pr1 x.
Definition ob2 {C D} (x : category_binproduct C D) : D := pr2 x.
Definition mor1 {C D} (x x' : category_binproduct C D) (f : _ ⟦x, x'⟧) : _ ⟦ob1 x, ob1 x'⟧ := pr1 f.
Definition mor2 {C D} (x x' : category_binproduct C D) (f : _ ⟦x, x'⟧) : _ ⟦ob2 x, ob2 x'⟧ := pr2 f.

Arguments ob1 { _ _ } _ .
Arguments ob2 { _ _ } _ .
Arguments mor1 { _ _ _ _ } _ .
Arguments mor2 { _ _ _ _ } _ .
Local Notation "C × D" := (category_binproduct C D) (at level 75, right associativity).

 
Definition make_catbinprod {C D : category} (X : C) (Y : D) : category_binproduct C D
  := make_dirprod X Y.

Local Notation "A ⊗ B" := (make_catbinprod A B).
Local Notation "( A , B )" := (make_catbinprod A B).

Definition catbinprodmor {C D : category} {X X' : C} {Z Z' : D} (α : X --> X') (β : Z --> Z')
  : X ⊗ Z --> X' ⊗ Z'
  := make_dirprod α β.

Local Notation "( f #, g )" := (catbinprodmor f g).

 
Lemma binprod_id {C D : category} (c : C) (d : D) : (identity c #, identity d) = identity (c, d).
Proof.
  apply idpath.
Defined.
 

Lemma binprod_comp {C D : category} (c c' c'' : C) (d d' d'' : D) (f : c --> c') (f' : c' --> c'') (g : d --> d') (g' : d' --> d'') : (f · f' #, g · g') = (f #, g) · (f' #, g').
Proof.
  apply idpath.
Defined.
 

Lemma is_z_iso_binprod_z_iso_aux {C D : category} {c c' : C} {d d' : D} {f : c --> c'} {g : d --> d'} (f_is_iso : is_z_isomorphism f)
  (g_is_iso : is_z_isomorphism g) : is_inverse_in_precat (f #, g)
        (inv_from_z_iso (make_z_iso' f f_is_iso) #, inv_from_z_iso (make_z_iso' g g_is_iso)).
Proof.
  apply make_dirprod.
  -
 transitivity ((make_z_iso' f f_is_iso) · (inv_from_z_iso (make_z_iso' f f_is_iso)) #, (make_z_iso' g g_is_iso) · (inv_from_z_iso (make_z_iso' g g_is_iso))).
    +
 symmetry.
      apply binprod_comp.
    +
 rewrite 2 z_iso_inv_after_z_iso.
      apply binprod_id.
  -
 transitivity ((inv_from_z_iso (make_z_iso' f f_is_iso)) · (make_z_iso' f f_is_iso) #, (inv_from_z_iso (make_z_iso' g g_is_iso)) · (make_z_iso' g g_is_iso)).
    +
 symmetry.
      apply binprod_comp.
    +
 rewrite 2 z_iso_after_z_iso_inv.
      apply binprod_id.
Qed.

Definition is_z_iso_binprod_z_iso {C D : category} {c c' : C} {d d' : D} {f : c --> c'} {g : d --> d'} (f_is_iso : is_z_isomorphism f)
  (g_is_iso : is_z_isomorphism g) : is_z_isomorphism (f #, g).
Proof.
  exists (inv_from_z_iso (make_z_iso' f f_is_iso) #, inv_from_z_iso (make_z_iso' g g_is_iso)).
  apply is_z_iso_binprod_z_iso_aux.
Defined.

 
Definition precatbinprod_z_iso {C D : category} {X X' : C} {Z Z' : D} (α : z_iso X X') (β : z_iso Z Z')
  : z_iso (X ⊗ Z) (X' ⊗ Z').
Proof.
  set (f := catbinprodmor α β).
  set (g := catbinprodmor (z_iso_inv_from_z_iso α) (z_iso_inv_from_z_iso β)).
  exists f.
  exists g.
  split.
  -
 apply pathsdirprod;
    apply z_iso_inv_after_z_iso.
  -
 apply pathsdirprod;
    apply z_iso_after_z_iso_inv.
Defined.

Definition precatbinprod_z_iso_inv {C D : category} {X X' : C} {Z Z' : D}
  (α : z_iso X X') (β : z_iso Z Z')
  : precatbinprod_z_iso (z_iso_inv_from_z_iso α) (z_iso_inv_from_z_iso β)
  = z_iso_inv_from_z_iso (precatbinprod_z_iso α β).
Proof.
  apply inv_z_iso_unique.
  split; apply z_iso_inv_after_z_iso.
Defined.

 

 
Section assoc.

Definition precategory_binproduct_assoc_data (C0 C1 C2 : precategory_data)
  : functor_data (precategory_binproduct_data C0 (precategory_binproduct_data C1 C2))
                 (precategory_binproduct_data (precategory_binproduct_data C0 C1) C2).
Proof.
  use tpair.
  -
 intros c.
exact (tpair _ (tpair _ (pr1 c) (pr1 (pr2 c))) (pr2 (pr2 c))).
  -
 intros a b c.
exact (tpair _ (tpair _ (pr1 c) (pr1 (pr2 c))) (pr2 (pr2 c))).
Defined.

Definition precategory_binproduct_assoc (C0 C1 C2 : category)
  : (C0 × (C1 × C2)) ⟶ ((C0 × C1) × C2).
Proof.
  exists (precategory_binproduct_assoc_data _ _ _). admit.
Defined.

Definition precategory_binproduct_unassoc_data (C0 C1 C2 : precategory_data)
  : functor_data (precategory_binproduct_data (precategory_binproduct_data C0 C1) C2)
                 (precategory_binproduct_data C0 (precategory_binproduct_data C1 C2)).
Proof.
  use tpair.
  -
 intros c.
exact (tpair _ (pr1 (pr1 c)) (tpair _ (pr2 (pr1 c)) (pr2 c))).
  -
 intros a b c.
exact (tpair _ (pr1 (pr1 c)) (tpair _ (pr2 (pr1 c)) (pr2 c))).
Defined.

Definition precategory_binproduct_unassoc (C0 C1 C2 : category)
  : ((C0 × C1) × C2) ⟶ (C0 × (C1 × C2)).
Proof.
  exists (precategory_binproduct_unassoc_data _ _ _). admit.
Defined.

End assoc.

 
Section functor_fix_fst_arg.

Variable C D E : precategory.
Variable F : functor (precategory_binproduct C D) E.
Variable c : C.

Definition functor_fix_fst_arg_ob (d: D) : E := F (tpair _ c d).
Definition functor_fix_fst_arg_mor (d d' : D) (f : d --> d') : functor_fix_fst_arg_ob d --> functor_fix_fst_arg_ob d'.
Proof.
  apply (#F).
  exact (make_dirprod (identity c) f).
Defined.

Definition functor_fix_fst_arg_data : functor_data D E
  := tpair _ functor_fix_fst_arg_ob functor_fix_fst_arg_mor.

Lemma is_functor_functor_fix_fst_arg_data: is_functor functor_fix_fst_arg_data.
Proof.
  red.
  split; red.
  +
 intros d.
    unfold functor_fix_fst_arg_data; simpl.
    unfold functor_fix_fst_arg_mor; simpl.
    unfold functor_fix_fst_arg_ob; simpl.
    assert (functor_id_inst := functor_id F).
    rewrite <- functor_id_inst.
    apply maponpaths.
    apply idpath.
  +
 intros d d' d'' f g.
    unfold functor_fix_fst_arg_data; simpl.
    unfold functor_fix_fst_arg_mor; simpl.
    assert (functor_comp_inst := @functor_comp _ _ F (make_dirprod c d) (make_dirprod c d') (make_dirprod c d'')).
    rewrite <- functor_comp_inst.
    apply maponpaths.
    unfold compose at 2.
    unfold precategory_binproduct; simpl.
    rewrite id_left.
    apply idpath.
Qed.

Definition functor_fix_fst_arg : D ⟶ E
  := tpair _ functor_fix_fst_arg_data is_functor_functor_fix_fst_arg_data.

End functor_fix_fst_arg.

Section nat_trans_from_functor_fix_fst_morphism_arg.

Variable C D E : category.
Variable F : (C × D) ⟶ E.
Variable c c' : C.
Variable g: c --> c'.

Definition nat_trans_from_functor_fix_fst_morphism_arg_data (d: D): functor_fix_fst_arg C D E F c d --> functor_fix_fst_arg C D E F c' d.
Proof.
  apply (#F).
  exact (make_dirprod g (identity d)).
Defined.

Lemma nat_trans_from_functor_fix_fst_morphism_arg_ax: is_nat_trans _ _ nat_trans_from_functor_fix_fst_morphism_arg_data.
Proof.
  red.
  intros d d' f.
  unfold nat_trans_from_functor_fix_fst_morphism_arg_data.
  unfold functor_fix_fst_arg; cbn.
  unfold functor_fix_fst_arg_mor; simpl.
  eapply pathscomp0.
  2: { apply functor_comp.
}
  apply pathsinv0.
  eapply pathscomp0.
  2: { apply functor_comp.
}
  apply maponpaths.
  unfold compose.
  cbn.
  do 2 rewrite id_left.
  do 2 rewrite id_right.
  apply idpath.
Qed.

Definition nat_trans_from_functor_fix_fst_morphism_arg: functor_fix_fst_arg C D E F c ⟹ functor_fix_fst_arg C D E F c'.
Proof.
  use tpair.
  -
 intro d.
apply nat_trans_from_functor_fix_fst_morphism_arg_data.
  -
 cbn.
exact nat_trans_from_functor_fix_fst_morphism_arg_ax.
Defined.

End nat_trans_from_functor_fix_fst_morphism_arg.

Section nat_trans_fix_fst_arg.

Variable C D E : category.
Variable F F' : (C × D) ⟶ E.
Variable α : F ⟹ F'.
Variable c : C.

Definition nat_trans_fix_fst_arg_data (d: D): functor_fix_fst_arg C D E F c d --> functor_fix_fst_arg C D E F' c d := α (tpair _ c d).

Lemma nat_trans_fix_fst_arg_ax: is_nat_trans _ _ nat_trans_fix_fst_arg_data.
Proof.
  red.
  intros d d' f.
  unfold nat_trans_fix_fst_arg_data, functor_fix_fst_arg; simpl.
  unfold functor_fix_fst_arg_mor; simpl.
  assert (nat_trans_ax_inst := nat_trans_ax α).
  apply nat_trans_ax_inst.
Qed.

Definition nat_trans_fix_fst_arg: functor_fix_fst_arg C D E F c ⟹ functor_fix_fst_arg C D E F' c
  := tpair _ nat_trans_fix_fst_arg_data nat_trans_fix_fst_arg_ax.

End nat_trans_fix_fst_arg.

Section functor_fix_snd_arg.

Variable C D E : category.
Variable F: (C × D) ⟶ E.
Variable d: D.

Definition functor_fix_snd_arg_ob (c: C): E := F (tpair _ c d).
Definition functor_fix_snd_arg_mor (c c': C)(f: c --> c'): functor_fix_snd_arg_ob c --> functor_fix_snd_arg_ob c'.
Proof.
  apply (#F).
  exact (make_dirprod f (identity d)).
Defined.

Definition functor_fix_snd_arg_data : functor_data C E
  := tpair _ functor_fix_snd_arg_ob functor_fix_snd_arg_mor.

Lemma is_functor_functor_fix_snd_arg_data: is_functor functor_fix_snd_arg_data.
Proof.
  split.
  +
 intros c.
    unfold functor_fix_snd_arg_data; simpl.
    unfold functor_fix_snd_arg_mor; simpl.
    unfold functor_fix_snd_arg_ob; simpl.
    assert (functor_id_inst := functor_id F).
    rewrite <- functor_id_inst.
    apply maponpaths.
    apply idpath.
  +
 intros c c' c'' f g.
    unfold functor_fix_snd_arg_data; simpl.
    unfold functor_fix_snd_arg_mor; simpl.
    assert (functor_comp_inst := @functor_comp _ _ F (make_dirprod c d) (make_dirprod c' d) (make_dirprod c'' d)).
    rewrite <- functor_comp_inst.
    apply maponpaths.
    unfold compose at 2.
    unfold precategory_binproduct; simpl.
    rewrite id_left.
    apply idpath.
Qed.

Definition functor_fix_snd_arg: C ⟶ E.
Proof.
  exists functor_fix_snd_arg_data.
  exact is_functor_functor_fix_snd_arg_data.
Defined.

End functor_fix_snd_arg.

Section nat_trans_from_functor_fix_snd_morphism_arg.

Variable C D E : category.
Variable F : (C × D) ⟶ E.
Variable d d' : D.
Variable f: d --> d'.

Definition nat_trans_from_functor_fix_snd_morphism_arg_data (c: C): functor_fix_snd_arg C D E F d c --> functor_fix_snd_arg C D E F d' c.
Proof.
  apply (#F).
  exact (make_dirprod (identity c) f).
Defined.

Lemma nat_trans_from_functor_fix_snd_morphism_arg_ax: is_nat_trans _ _ nat_trans_from_functor_fix_snd_morphism_arg_data.
Proof.
  red.
  intros c c' g.
  unfold nat_trans_from_functor_fix_snd_morphism_arg_data.
  unfold functor_fix_snd_arg; cbn.
  unfold functor_fix_snd_arg_mor; simpl.
  eapply pathscomp0.
  2: { apply functor_comp.
}
  apply pathsinv0.
  eapply pathscomp0.
  2: { apply functor_comp.
}
  apply maponpaths.
  unfold compose.
  cbn.
  do 2 rewrite id_left.
  do 2 rewrite id_right.
  apply idpath.
Qed.

Definition nat_trans_from_functor_fix_snd_morphism_arg: functor_fix_snd_arg C D E F d ⟹ functor_fix_snd_arg C D E F d'.
Proof.
  use tpair.
  -
 intro c.
apply nat_trans_from_functor_fix_snd_morphism_arg_data.
  -
 cbn.
exact nat_trans_from_functor_fix_snd_morphism_arg_ax.
Defined.

End nat_trans_from_functor_fix_snd_morphism_arg.

Section nat_trans_fix_snd_arg.

Variable C D E : category.
Variable F F': (C × D) ⟶ E.
Variable α: F ⟹ F'.
Variable d: D.

Definition nat_trans_fix_snd_arg_data (c:C): functor_fix_snd_arg C D E F d c --> functor_fix_snd_arg C D E F' d c := α (tpair _ c d).

Lemma nat_trans_fix_snd_arg_ax: is_nat_trans _ _ nat_trans_fix_snd_arg_data.
Proof.
  red.
  intros c c' f.
  unfold nat_trans_fix_snd_arg_data, functor_fix_snd_arg; simpl.
  unfold functor_fix_snd_arg_mor; simpl.
  assert (nat_trans_ax_inst := nat_trans_ax α).
  apply nat_trans_ax_inst.
Qed.

Definition nat_trans_fix_snd_arg: functor_fix_snd_arg C D E F d ⟹ functor_fix_snd_arg C D E F' d
  := tpair _ nat_trans_fix_snd_arg_data nat_trans_fix_snd_arg_ax.

End nat_trans_fix_snd_arg.

 
Section functors.

Definition pair_functor_data {A B C D : category}
  (F : A ⟶ C) (G : B ⟶ D) : functor_data (A × B) (C × D).
Proof.
use tpair.
-
 intro x; apply (make_catbinprod (F (pr1 x)) (G (pr2 x))).
-
 intros x y f; simpl; apply (catbinprodmor (# F (pr1 f)) (# G (pr2 f))).
Defined.

Definition pair_functor {A B C D : category}
  (F : A ⟶ C) (G : B ⟶ D) : (A × B) ⟶ (C × D).
Proof.
apply (tpair _ (pair_functor_data F G)). admit.
Defined.

Definition pr1_functor_data (A B : category) :
  functor_data (A × B) A.
Proof.
use tpair.
-
 intro x; apply (pr1 x).
-
 intros x y f; simpl; apply (pr1 f).
Defined.

Definition pr1_functor (A B : category) : (A × B) ⟶ A.
Proof.
apply (tpair _ (pr1_functor_data A B)). admit.
Defined.

Definition pr2_functor_data (A B : category) :
  functor_data (A × B) B.
Proof.
use tpair.
-
 intro x; apply (pr2 x).
-
 intros x y f; simpl; apply (pr2 f).
Defined.

Definition pr2_functor (A B : category) : (A × B) ⟶ B.
Proof.
apply (tpair _ (pr2_functor_data A B)). admit.
Defined.

Definition bindelta_functor_data (C : category) :
  functor_data C (C × C).
Proof.
use tpair.
-
 intro x; apply (make_catbinprod x x).
-
 intros x y f; simpl; apply (catbinprodmor f f).
Defined.

 
Definition bindelta_functor (C : category) : C ⟶ (C × C).
Proof.
apply (tpair _ (bindelta_functor_data C)). admit.
Defined.

Definition bindelta_pair_functor_data (C D E : category)
  (F : C ⟶ D) (G : C ⟶ E) :
  functor_data C (category_binproduct D E).
Proof.
  use tpair.
  -
 intro c.
apply (make_catbinprod (F c) (G c)).
  -
 intros x y f.
simpl.
apply (catbinprodmor (# F f) (# G f)).
Defined.

Lemma is_functor_bindelta_pair_functor_data (C D E : category)
  (F : C ⟶ D) (G : C ⟶ E) : is_functor (bindelta_pair_functor_data _ _ _ F G).
Proof.
  split.
  -
 intro c.
    simpl.
    rewrite functor_id.
    rewrite functor_id.
    apply idpath.
  -
 intros c c' c'' f g.
    simpl.
    rewrite functor_comp.
    rewrite functor_comp.
    apply idpath.
Qed.

Definition bindelta_pair_functor {C D E : category}
  (F : C ⟶ D) (G : C ⟶ E) : C ⟶ (D × E).
Proof.
  apply (tpair _ (bindelta_pair_functor_data C D E F G)).
  apply is_functor_bindelta_pair_functor_data.
Defined.

 
Definition bindelta_pair_pr1_data
           {C₁ C₂ C₃ : category}
           (F : C₁ ⟶ C₂)
           (G : C₁ ⟶ C₃)
  : nat_trans_data (bindelta_pair_functor F G ∙ pr1_functor _ _) F
  := λ _, identity _.

Definition bindelta_pair_pr1_is_nat_trans
           {C₁ C₂ C₃ : category}
           (F : C₁ ⟶ C₂)
           (G : C₁ ⟶ C₃)
  : is_nat_trans _ _ (bindelta_pair_pr1_data F G).
Proof.
  intros x y f ; cbn ; unfold bindelta_pair_pr1_data.
  rewrite id_left, id_right.
  apply idpath.
Qed.

Definition bindelta_pair_pr1
           {C₁ C₂ C₃ : category}
           (F : C₁ ⟶ C₂)
           (G : C₁ ⟶ C₃)
  : bindelta_pair_functor F G ∙ pr1_functor _ _ ⟹ F.
Proof.
  use make_nat_trans.
  -
 exact (bindelta_pair_pr1_data F G).
  -
 exact (bindelta_pair_pr1_is_nat_trans F G).
Defined.

Definition bindelta_pair_pr1_z_iso
           {C₁ C₂ C₃ : category}
           (F : C₁ ⟶ C₂)
           (G : C₁ ⟶ C₃)
  : nat_z_iso
      (bindelta_pair_functor F G ∙ pr1_functor _ _)
      F.
Proof.
  use make_nat_z_iso.
  -
 exact (bindelta_pair_pr1 F G).
  -
 intro.
    apply identity_is_z_iso.
Defined.

Definition bindelta_pair_pr2_data
           {C₁ C₂ C₃ : category}
           (F : C₁ ⟶ C₂)
           (G : C₁ ⟶ C₃)
  : nat_trans_data (bindelta_pair_functor F G ∙ pr2_functor _ _) G
  := λ _, identity _.

Definition bindelta_pair_pr2_is_nat_trans
           {C₁ C₂ C₃ : category}
           (F : C₁ ⟶ C₂)
           (G : C₁ ⟶ C₃)
  : is_nat_trans _ _ (bindelta_pair_pr2_data F G).
Proof.
  intros x y f ; cbn ; unfold bindelta_pair_pr1_data.
  rewrite id_left, id_right.
  apply idpath.
Qed.

Definition bindelta_pair_pr2
           {C₁ C₂ C₃ : category}
           (F : C₁ ⟶ C₂)
           (G : C₁ ⟶ C₃)
  : bindelta_pair_functor F G ∙ pr2_functor _ _ ⟹ G.
Proof.
  use make_nat_trans.
  -
 exact (bindelta_pair_pr2_data F G).
  -
 exact (bindelta_pair_pr2_is_nat_trans F G).
Defined.

Definition bindelta_pair_pr2_z_iso
           {C₁ C₂ C₃ : category}
           (F : C₁ ⟶ C₂)
           (G : C₁ ⟶ C₃)
  : nat_z_iso
      (bindelta_pair_functor F G ∙ pr2_functor _ _)
      G.
Proof.
  use make_nat_z_iso.
  -
 exact (bindelta_pair_pr2 F G).
  -
 intro.
    apply identity_is_z_iso.
Defined.

 
Definition binswap_pair_functor {C D : category} : (C × D) ⟶ (D × C) :=
  bindelta_functor (C × D) ∙ pair_functor (pr2_functor C D) (pr1_functor C D).

 
Definition reverse_three_args {C D E : category} : ((C × D) × E) ⟶ ((E × D) × C).
Proof.
  use (functor_composite (precategory_binproduct_unassoc _ _ _)).
  use (functor_composite binswap_pair_functor).
  exact (pair_functor binswap_pair_functor (functor_identity _)).
Defined.

Lemma reverse_three_args_ok {C D E : category} :
  functor_on_objects (reverse_three_args(C:=C)(D:=D)(E:=E)) = λ c, ((pr2 c, pr2 (pr1 c)), pr1 (pr1 c)).
Proof.
  apply idpath.
Qed.

Lemma reverse_three_args_idempotent {C D E : category} :
  functor_composite (reverse_three_args(C:=C)(D:=D)(E:=E))(reverse_three_args(C:=E)(D:=D)(E:=C))
  = functor_identity _.
Proof.
  apply functor_eq.
  -
 repeat (apply has_homsets_precategory_binproduct; try apply homset_property).
  -
 use functor_data_eq.
    +
 cbn.
      intro cde.
      apply idpath.
    +
 intros cde1 cde2 f.
      cbn.
      apply idpath.
Qed.

End functors.

Section whiskering.

 

Definition nat_trans_data_post_whisker_fst_param {B C D P: category}
           {G H : B ⟶ C} (γ : G ⟹ H) (K : (P × C) ⟶ D):
  nat_trans_data (functor_composite (pair_functor (functor_identity _) G) K)
                 (functor_composite (pair_functor (functor_identity _) H) K) :=
  λ pb : P × B, #K ((identity (ob1 pb),, γ (ob2 pb)):
                      (P × C)⟦ob1 pb,, G(ob2 pb), ob1 pb,, H(ob2 pb)⟧).

Lemma is_nat_trans_post_whisker_fst_param {B C D P: category}
  {G H : B ⟶ C} (γ : G ⟹ H) (K : (P × C) ⟶ D):
  is_nat_trans _ _ (nat_trans_data_post_whisker_fst_param γ K).
Proof.
  intros pb pb' f.
  cbn.
  unfold nat_trans_data_post_whisker_fst_param.
  eapply pathscomp0.
  2: { apply functor_comp.
}
  eapply pathscomp0.
  {
 apply pathsinv0.
apply functor_comp.
}
  apply maponpaths.
  unfold compose; cbn.
  rewrite id_left.
rewrite id_right.
  apply maponpaths.
  apply (nat_trans_ax γ).
Qed.

Definition post_whisker_fst_param {B C D P: category}
  {G H : B ⟶ C} (γ : G ⟹ H) (K : (P × C) ⟶ D):
  (functor_composite (pair_functor (functor_identity _) G) K) ⟹
  (functor_composite (pair_functor (functor_identity _) H) K) :=
  make_nat_trans _ _ _ (is_nat_trans_post_whisker_fst_param γ K).

Definition nat_trans_data_post_whisker_snd_param {B C D P: category}
           {G H : B ⟶ C} (γ : G ⟹ H) (K : (C × P) ⟶ D):
  nat_trans_data (functor_composite (pair_functor G (functor_identity _)) K)
                 (functor_composite (pair_functor H (functor_identity _)) K) :=
  λ bp : B × P, #K ((γ (ob1 bp),, identity (ob2 bp)):
                      (C × P)⟦G(ob1 bp),, ob2 bp, H(ob1 bp),, ob2 bp⟧).

Lemma is_nat_trans_post_whisker_snd_param {B C D P: category}
  {G H : B ⟶ C} (γ : G ⟹ H) (K : (C × P) ⟶ D):
  is_nat_trans _ _ (nat_trans_data_post_whisker_snd_param γ K).
Proof.
  intros bp bp' f.
  cbn.
  unfold nat_trans_data_post_whisker_snd_param.
  eapply pathscomp0.
  2: { apply functor_comp.
}
  eapply pathscomp0.
  {
 apply pathsinv0.
apply functor_comp.
}
  apply maponpaths.
  unfold compose; cbn.
  rewrite id_left.
rewrite id_right.
  apply (maponpaths (λ x, make_dirprod x (pr2 f))).
  apply (nat_trans_ax γ).
Qed.

Definition post_whisker_snd_param {B C D P: category}
  {G H : B ⟶ C} (γ : G ⟹ H) (K : (C × P) ⟶ D):
  (functor_composite (pair_functor G (functor_identity _)) K) ⟹
  (functor_composite (pair_functor H (functor_identity _)) K) :=
  make_nat_trans _ _ _ (is_nat_trans_post_whisker_snd_param γ K).

End whiskering.

Section Currying.
   

  Context (C D E : category).

Section Def_Curry_Ob.
  Context (F: (C × D) ⟶ E).

  Definition curry_functor_data: functor_data D [C, E].
  Proof.
    use make_functor_data.
    -
 intro d.
      exact (functor_fix_snd_arg C D E F d).
    -
 intros d d' f.
      exact (nat_trans_from_functor_fix_snd_morphism_arg C D E F d d' f).
  Defined.

  Lemma curry_functor_data_is_functor: is_functor curry_functor_data.
  Proof.
    split.
    -
 intro d.
      apply (nat_trans_eq E).
      intro c.
      cbn.
      unfold nat_trans_from_functor_fix_snd_morphism_arg_data.
      etrans.
      {
 apply maponpaths.
apply binprod_id.
}
      apply functor_id.
    -
 intros d1 d2 d3 f g.
      apply (nat_trans_eq E).
      intro c.
      cbn.
      unfold nat_trans_from_functor_fix_snd_morphism_arg_data.
      etrans.
      2: { apply functor_comp.
}
      apply maponpaths.
      apply dirprodeq; cbn.
      +
 apply pathsinv0.
apply id_left.
      +
 apply idpath.
  Qed.

  Definition curry_functor: D ⟶ [C, E] := make_functor curry_functor_data curry_functor_data_is_functor.

End Def_Curry_Ob.

Section Def_Curry_Mor.

  Context {F G: (C × D) ⟶ E} (α: F ⟹ G).

  Definition curry_nattrans : curry_functor F ⟹ curry_functor G.
  Proof.
    use make_nat_trans.
    -
 intro d.
      exact (nat_trans_fix_snd_arg _ _ _ _ _ α d).
    -
 intros d d' f.
      apply nat_trans_eq; try exact E.
      intro c.
      cbn.
      unfold nat_trans_from_functor_fix_snd_morphism_arg_data, nat_trans_fix_snd_arg_data.
      apply nat_trans_ax.
  Defined.

End Def_Curry_Mor.

Section Def_Uncurry_Ob.

  Context (G: D ⟶ [C, E]).

  Definition uncurry_functor_data: functor_data (C × D) E.
  Proof.
    use make_functor_data.
    -
 intro cd.
induction cd as [c d].
      exact (pr1 (G d) c).
    -
 intros cd cd' ff'.
      induction cd as [c d].
induction cd' as [c' d'].
induction ff' as [f f'].
      cbn in *.
      exact (#(G d: functor C E) f · pr1 (#G f') c').
  Defined.

  Lemma uncurry_functor_data_is_functor: is_functor uncurry_functor_data.
  Proof.
    split.
    -
 intro cd.
induction cd as [c d].
      cbn.
      rewrite functor_id.
      rewrite id_left.
      assert (H := functor_id G d).
      apply (maponpaths (fun f => pr1 f c)) in H.
      exact H.
    -
 intros cd1 cd2 cd3 ff' gg'.
      induction cd1 as [c1 d1].
induction cd2 as [c2 d2].
induction cd3 as [c3 d3].
induction ff' as [f f'].
induction gg' as [g g'].
      cbn in *.
      rewrite functor_comp.
      assert (H := functor_comp G f' g').
      apply (maponpaths (fun f => pr1 f c3)) in H.
      etrans.
      {
 apply maponpaths.
        exact H.
}
      cbn.
      repeat rewrite assoc.
      apply cancel_postcomposition.
      repeat rewrite <- assoc.
      apply maponpaths.
      apply nat_trans_ax.
  Qed.

  Definition uncurry_functor: (C × D) ⟶ E := make_functor uncurry_functor_data uncurry_functor_data_is_functor.

End Def_Uncurry_Ob.

Section Def_Uncurry_Mor.

  Context {F G: D ⟶ [C, E]} (α: F ⟹ G).

  Definition uncurry_nattrans : uncurry_functor F ⟹ uncurry_functor G.
  Proof.
    use make_nat_trans.
    -
 intro cd.
      cbn.
      exact (pr1 (α (pr2 cd)) (pr1 cd)).
    -
 intros cd cd' fg.
      induction cd as [c d].
induction cd' as [c' d'].
induction fg as [f g].
      cbn in *.
      assert (aux := nat_trans_ax α d d' g).
      apply (maponpaths pr1) in aux.
      apply toforallpaths in aux.
      assert (auxinst := aux c').
      rewrite <- assoc.
      etrans.
      {
 apply maponpaths.
exact auxinst.
}
      clear aux auxinst.
      cbn.
      do 2 rewrite assoc.
      apply cancel_postcomposition.
      apply nat_trans_ax.
  Defined.

End Def_Uncurry_Mor.

Lemma uncurry_after_curry (F: (C × D) ⟶ E): uncurry_functor (curry_functor F) = F.
Proof.
  apply functor_eq.
{
 exact E.
}
   
  use functor_data_eq.
  -
 intro cd; apply idpath.
  -
 cbn.
intros cd cd' ff'.
    induction cd as [c d].
induction cd' as [c' d'].
induction ff' as [f f'].
    cbn in *.
    unfold functor_fix_snd_arg_mor, nat_trans_from_functor_fix_snd_morphism_arg_data.
    etrans.
    {
 apply pathsinv0.
apply functor_comp.
}
    unfold compose.
cbn.
    rewrite id_left, id_right.
    apply idpath.
Qed.

Lemma curry_after_uncurry_pointwise (G: D ⟶ [C, E]) (d: D) : pr1 (curry_functor (uncurry_functor G)) d = pr1 G d.
Proof.
   
  apply functor_eq.
{
 exact E.
}
  use functor_data_eq.
  -
 intro c.
    apply idpath.
  -
 cbn.
    intros c c' f.
    assert (H := functor_id G d).
    apply (maponpaths (fun f => pr1 f c')) in H.
    etrans.
    {
 apply maponpaths.
exact H.
}
    apply id_right.
Qed.

End Currying.

Section Evaluation.
 

  Context {C D : category}.

Definition evaluation_functor: ([C, D] × C) ⟶  D.
Proof.
  apply (functor_composite (@binswap_pair_functor _ _)).
  apply (uncurry_functor).
  exact (functor_identity _).
Defined.

Goal ∏ (F: C ⟶ D) (c: C), evaluation_functor (F ,, c) = F c.
Proof.
  intros.
  apply idpath.
Qed.

End Evaluation.

Section EvaluationNatTrans.
  Context {C D₁ D₂ : category}
          (F G : D₁ ⟶ functor_category C D₂)
          (α : bindelta_pair_functor
                 (pr1_functor D₁ C ∙ F)
                 (pr2_functor D₁ C ∙ functor_identity C)
               ∙ bindelta_functor (category_binproduct [C, D₂] C)
               ∙ pair_functor (pr2_functor [C, D₂] C) (pr1_functor [C, D₂] C)
               ∙ uncurry_functor _ _ _ (functor_identity _)
               ⟹
               bindelta_pair_functor
                 (pr1_functor D₁ C ∙ G)
                 (pr2_functor D₁ C ∙ functor_identity C)
               ∙ bindelta_functor (category_binproduct [C, D₂] C)
               ∙ pair_functor (pr2_functor [C, D₂] C) (pr1_functor [C, D₂] C)
               ∙ uncurry_functor _ _ _ (functor_identity _)).

  Definition evaluation_nat_trans_data_point
             (x : D₁)
    : nat_trans_data (F x : _ ⟶ _) (G x : _ ⟶ _)
    := λ y, α (x ,, y).

  Definition evaluation_nat_trans_data_point_is_nat_trans
             (x : D₁)
    : is_nat_trans _ _ (evaluation_nat_trans_data_point x).
  Proof.
    intros y₁ y₂ g ; unfold evaluation_nat_trans_data_point ; cbn.
    pose (nat_trans_ax α (x ,, y₁) (x ,, y₂) (identity _ ,, g)) as p.
    cbn in p.
    rewrite (functor_id F), (functor_id G) in p.
    rewrite !id_right in p.
    exact p.
  Qed.

  Definition evaluation_nat_trans_data
    : nat_trans_data F G.
  Proof.
    intro x.
    use make_nat_trans.
    -
 exact (evaluation_nat_trans_data_point x).
    -
 exact (evaluation_nat_trans_data_point_is_nat_trans x).
  Defined.

  Definition evaluation_nat_trans_is_nat_trans
    : is_nat_trans _ _ evaluation_nat_trans_data.
  Proof.
    intros x₁ x₂ f.
    use nat_trans_eq.
    {
      apply homset_property.
    }
    intros y ; cbn.
    pose (nat_trans_ax α (x₁ ,, y) (x₂ ,, y) (f ,, identity _)) as p.
    cbn in p.
    rewrite (functor_id (F _)), (functor_id (G _)) in p.
    rewrite !id_left in p.
    exact p.
  Qed.

  Definition evaluation_nat_trans : F ⟹ G.
  Proof.
    use make_nat_trans.
    -
 exact evaluation_nat_trans_data.
    -
 exact evaluation_nat_trans_is_nat_trans.
  Defined.
End EvaluationNatTrans.

 
Section CurryFunctor.
  Context {C D₁ D₂ : category}
          (F : category_binproduct D₁ C ⟶ D₂).

  Definition curry_functor'_point_data
             (x : D₁)
    : functor_data C D₂.
  Proof.
    use make_functor_data.
    -
 exact (λ y, F (x ,, y)).
    -
 refine (λ y₁ y₂ g, #F (_ ,, _)).
      +
 exact (identity x).
      +
 exact g.
  Defined.

  Definition curry_functor'_point_is_functor
             (x : D₁)
    : is_functor (curry_functor'_point_data x).
  Proof.
    split.
    -
 intro y ; cbn.
      apply (functor_id F).
    -
 intros y₁ y₂ y₃ g₁ g₂ ; cbn.
      refine (_ @ functor_comp F _ _) ; cbn.
      rewrite id_left.
      apply idpath.
  Qed.

  Definition curry_functor'_point
             (x : D₁)
    : C ⟶ D₂.
  Proof.
    use make_functor.
    -
 exact (curry_functor'_point_data x).
    -
 exact (curry_functor'_point_is_functor x).
  Defined.

  Definition curry_functor'_mor
             {x₁ x₂ : D₁}
             (f : x₁ --> x₂)
    : curry_functor'_point x₁ ⟹ curry_functor'_point x₂.
  Proof.
    use make_nat_trans.
    -
 refine (λ y, #F (_ ,, _)).
      +
 exact f.
      +
 exact (identity y).
    -
 admit.
  Defined.

  Definition curry_functor'_data
    : functor_data D₁ (functor_precategory_data C D₂).
  Proof.
    use make_functor_data.
    -
 exact curry_functor'_point.
    -
 exact @curry_functor'_mor.
  Defined.

  Definition curry_functor'_is_functor
    : is_functor curry_functor'_data.
  Proof.
    split.
    -
 intro x.
      use nat_trans_eq.
      {
        apply homset_property.
      }
      intro y ; cbn.
      apply (functor_id F).
    -
 intros x₁ x₂ x₃ f₁ f₂.
      use nat_trans_eq.
      {
        apply homset_property.
      }
      intro y ; cbn.
      refine (_ @ functor_comp F _ _).
      cbn.
      rewrite id_left.
      apply idpath.
  Qed.

  Definition curry_functor'
    : D₁ ⟶ functor_category C D₂.
  Proof.
    use make_functor.
    -
 exact curry_functor'_data.
    -
 exact curry_functor'_is_functor.
  Defined.

  Definition evaluate_curry_functor'
    : bindelta_pair_functor
        (pr1_functor D₁ C ∙ curry_functor')
        (pr2_functor D₁ C ∙ functor_identity _)
      ∙ evaluation_functor
      ⟹
      F.
  Proof.
    use make_nat_trans.
    -
 exact (λ x, identity _).
    -
 admit.
  Defined.

  Definition evaluate_curry_functor'_nat_z_iso
    : nat_z_iso
        (bindelta_pair_functor
           (pr1_functor D₁ C ∙ curry_functor')
           (pr2_functor D₁ C ∙ functor_identity _)
         ∙ evaluation_functor)
        F.
  Proof.
    use make_nat_z_iso.
    -
 exact evaluate_curry_functor'.
    -
 intro x.
      apply identity_is_z_iso.
  Defined.
End CurryFunctor.

Section Coevaluation.
   

  Context {C D : category}.

  Definition coevaluation_functor: C ⟶  [D, C × D].
  Proof.
    apply curry_functor.
    apply binswap_pair_functor.
  Defined.

End Coevaluation.

Section CategoryBinproductIsoWeq.
  Context {C D : category}
          (x y : category_binproduct C D).

  Definition category_binproduct_z_iso_map
    : z_iso (pr1 x) (pr1 y) × z_iso (pr2 x) (pr2 y) → z_iso x y.
  Proof.
    intros i.
    simple refine ((pr11 i ,, pr12 i) ,, _).
    apply is_z_iso_binprod_z_iso.
    -
 exact (pr21 i).
    -
 exact (pr22 i).
  Defined.

  Definition category_binproduct_z_iso_inv
    : z_iso x y → z_iso (pr1 x) (pr1 y) × z_iso (pr2 x) (pr2 y)
    := λ i, functor_on_z_iso (pr1_functor C D) i ,, functor_on_z_iso (pr2_functor C D) i.

  Definition category_binproduct_z_iso_weq
    : z_iso (pr1 x) (pr1 y) × z_iso (pr2 x) (pr2 y) ≃ z_iso x y.
  Proof.
    use make_weq.
    -
 exact category_binproduct_z_iso_map.
    -
 use gradth.
      +
 exact category_binproduct_z_iso_inv.
      +
 admit.
      +
 admit.
  Defined.

   

End CategoryBinproductIsoWeq.

Section Univalence.
  Context {C D : category}
          (HC : is_univalent C)
          (HD : is_univalent D).

  Definition is_unvialent_category_binproduct
    : is_univalent (category_binproduct C D).
  Proof.
    intros x y.
    use weqhomot.
    -
 exact (category_binproduct_z_iso_weq x y
             ∘ weqdirprodf
                 (make_weq _ (HC _ _))
                 (make_weq _ (HD _ _))
             ∘ pathsdirprodweq)%weq.
    -
 admit.
  Defined.
End Univalence.

Definition univalent_category_binproduct
           (C₁ C₂ : univalent_category)
  : univalent_category.
Proof.
  use make_univalent_category.
  -
 exact (category_binproduct C₁ C₂).
  -
 use is_unvialent_category_binproduct.
    +
 exact (pr2 C₁).
    +
 exact (pr2 C₂).
Defined.

End PrecategoryBinProduct.

End UniMath_DOT_CategoryTheory_DOT_PrecategoryBinProduct_WRAPPED.
Module Export UniMath_DOT_CategoryTheory_DOT_PrecategoryBinProduct.
Module Export UniMath.
Module Export CategoryTheory.
Module Export PrecategoryBinProduct.
Include UniMath_DOT_CategoryTheory_DOT_PrecategoryBinProduct_WRAPPED.PrecategoryBinProduct.
End PrecategoryBinProduct.

End CategoryTheory.

End UniMath.

End UniMath_DOT_CategoryTheory_DOT_PrecategoryBinProduct.
Inductive False : Prop := .
Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.
Module Export whiskering.

Import UniMath.Foundations.PartD.
Import UniMath.CategoryTheory.Core.Categories.
Import UniMath.CategoryTheory.Core.Functors.
Import UniMath.CategoryTheory.Core.Isos.
Import UniMath.CategoryTheory.Core.NaturalTransformations.
Import UniMath.CategoryTheory.FunctorCategory.
Local Open Scope cat.

Definition functor_compose {A B C : category} (F : ob [A, B])
      (G : ob [B , C]) : ob [A , C] :=
   functor_composite F G.

Lemma is_nat_trans_pre_whisker (A B C : precategory_data)
   (F : functor_data A B) (G H : functor_data B C) (gamma : nat_trans G H) :
   is_nat_trans
        (functor_composite_data F G)
        (functor_composite_data F H)
   (λ a : A, gamma (F a)).
Proof.
  intros a b f; simpl.
  apply nat_trans_ax.
Qed.

Definition pre_whisker {A B C : precategory_data}
   (F : functor_data A B)  {G H : functor_data B C} (gamma : nat_trans G H) :
   nat_trans (functor_composite_data F G)  (functor_composite_data F H).
  exists (λ a, pr1 gamma (pr1 F a)).
  apply is_nat_trans_pre_whisker.
Defined.

Lemma pre_whisker_iso_is_iso {A B C : precategory_data}
    (F : functor_data A B)  {G H : functor_data B C} (gamma : nat_trans G H)
    (X : is_nat_iso gamma)
  : is_nat_iso (pre_whisker F gamma).
  intros a.
  apply X.
Defined.

Lemma pre_whisker_on_nat_z_iso {A B C : precategory_data}
    (F : functor_data A B)  {G H : functor_data B C} (gamma : nat_trans G H)
    (X : is_nat_z_iso gamma)
  : is_nat_z_iso (pre_whisker F gamma).
  intros a.
  apply X.
Defined.

Definition pre_whisker_in_funcat (A B C : category)
           (F : [A, B]) {G H : [B, C]} (γ : [B, C]⟦G, H⟧) :
  [A, C]⟦functor_compose F G, functor_compose F H⟧.
Proof.
  exact (pre_whisker (F: A ⟶ B) γ).
Defined.

Lemma is_nat_trans_post_whisker (B C D : precategory_data)
   (G H : functor_data B C) (gamma : nat_trans G  H)
        (K : functor C D):
  is_nat_trans (functor_composite_data  G K)
                         (functor_composite_data H K)
     (λ b : B, #K (gamma b)).
Proof.
  unfold is_nat_trans.
  simpl in *.
  intros;
  repeat rewrite <- functor_comp.
  rewrite (nat_trans_ax gamma).
  apply idpath.
Qed.

Definition post_whisker {B C D : precategory_data}
   {G H : functor_data B C} (gamma : nat_trans G H)
        (K : functor C D)
  : nat_trans (functor_composite_data G K) (functor_composite_data H K).
  exists (λ a : ob B, #(pr1 K) (pr1 gamma  a)).
  apply is_nat_trans_post_whisker.
Defined.

Lemma post_whisker_iso_is_iso {B C D : precategory}
   {G H : functor_data B C} (gamma : nat_trans G H)
   (K : functor C D)
   (X : is_nat_iso gamma)
  : is_nat_iso (post_whisker gamma K).
  intros b.
  unfold post_whisker.
  simpl.
  set ( gammab := make_iso (gamma b) (X b) ).
  apply (functor_on_iso_is_iso C D K _ _ gammab).
Defined.

Lemma post_whisker_z_iso_is_z_iso {B C D : precategory}
   {G H : functor_data B C} (gamma : nat_trans G H)
   (K : functor C D)
   (X : is_nat_z_iso gamma)
  : is_nat_z_iso (post_whisker gamma K).
  intros b.
  unfold post_whisker.
  simpl.
  apply (functor_on_is_z_isomorphism K (X b)).
Defined.

Definition post_whisker_in_funcat (B C D : category)
            {G H : [B, C]} (γ : [B, C]⟦G, H⟧) (K : [C, D]) :
  [B, D]⟦functor_compose G K, functor_compose H K⟧.
Proof.
  exact (post_whisker γ (K: C ⟶ D)).
Defined.

Definition pre_composition_functor_data (A B C : category)
      (H : ob [A, B]) : functor_data [B, C] [A, C].
Proof.
  exists (λ G, functor_compose H G).
  exact (λ a b gamma, pre_whisker_in_funcat _ _ _ H gamma).
Defined.

Lemma pre_whisker_identity (A B : precategory_data) (C : category)
  (H : functor_data A B) (G : functor_data B C)
  : pre_whisker H (nat_trans_id G) =
   nat_trans_id (functor_composite_data H G).
Proof.
  apply nat_trans_eq.
  -
 apply homset_property.
  -
 intro a.
apply idpath.
Qed.

Lemma pre_whisker_composition (A B : precategory_data) (C : category)
  (H : functor_data A B) (a b c : functor_data B C)
  (f : nat_trans a b) (g : nat_trans b c)
  : pre_whisker H (nat_trans_comp _ _ _ f g) =
     nat_trans_comp _ _ _ (pre_whisker H f) (pre_whisker H g).
Proof.
  apply nat_trans_eq.
  -
 apply homset_property.
  -
 intro; simpl.
    apply idpath.
Qed.

Lemma pre_composition_is_functor (A B C : category) (H : [A, B]) :
    is_functor (pre_composition_functor_data A B C H).
Proof.
  split; simpl in *.
  -
 unfold functor_idax .
    intros.
    apply pre_whisker_identity.
  -
 unfold functor_compax .
    intros.
    apply pre_whisker_composition.
Qed.

Definition pre_composition_functor (A B C : category) (H : [A , B]) : functor [B, C] [A, C].
Proof.
  exists (pre_composition_functor_data A B C H).
  apply pre_composition_is_functor.
Defined.

Definition pre_comp_functor {A B C: category} :
  [A, B] → [B, C] ⟶ [A, C] :=
    pre_composition_functor _ _ _.

Definition post_composition_functor_data (A B C : category)
      (H : ob [B, C]) : functor_data [A, B] [A, C].
Proof.
  exists (λ G, functor_compose G H).
  exact (λ a b gamma, post_whisker_in_funcat _ _ _ gamma H).
Defined.

Lemma post_whisker_identity (A B : precategory) (C : category)
  (H : functor B C) (G : functor_data A B)
  : post_whisker (nat_trans_id G) H =
   nat_trans_id (functor_composite_data G H).
Proof.
  apply nat_trans_eq.
  -
 apply homset_property.
  -
 intro a.
unfold post_whisker.
simpl.
    apply functor_id.
Qed.

Lemma post_whisker_composition (A B : precategory) (C : category)
  (H : functor B C) (a b c : functor_data A B)
  (f : nat_trans a b) (g : nat_trans b c)
  : post_whisker (nat_trans_comp _ _ _ f g) H =
     nat_trans_comp _ _ _ (post_whisker f H) (post_whisker g H).
Proof.
  apply nat_trans_eq.
  -
 apply homset_property.
  -
 intro; simpl.
    apply functor_comp.
Qed.

Lemma post_composition_is_functor (A B C : category) (H : [B, C]) :
    is_functor (post_composition_functor_data A B C H).
Proof.
  split; simpl in *.
  -
 unfold functor_idax .
    intros.
    apply post_whisker_identity.
  -
 unfold functor_compax .
    intros.
    apply post_whisker_composition.
Qed.

Definition post_composition_functor (A B C : category) (H : [B , C]) : functor [A, B] [A, C].
Proof.
  exists (post_composition_functor_data A B C H).
  apply post_composition_is_functor.
Defined.

Definition post_comp_functor {A B C : category} :
  [B, C] → [A, B] ⟶ [A, C] :=
    post_composition_functor _ _ _.

End whiskering.

Import UniMath.Foundations.PartD.
Import UniMath.CategoryTheory.Core.Categories.
Import UniMath.CategoryTheory.Core.Isos.
Import UniMath.CategoryTheory.Core.NaturalTransformations.
Import UniMath.CategoryTheory.Core.Functors.
Import UniMath.CategoryTheory.PrecategoryBinProduct.

Local Open Scope cat.

Notation "'id' X" := (identity X) (at level 30).

Notation "C ⊠ D" := (category_binproduct C D) (at level 38).
Notation "( c , d )" := (make_catbinprod c d).
Notation "( f #, g )" := (catbinprodmor f g).

Section Monoidal_Precat.

Context {C : category} (tensor : C ⊠ C ⟶ C) (I : C).

Notation "X ⊗ Y" := (tensor (X, Y)).
Notation "f #⊗ g" := (#tensor (f #, g)) (at level 31).

Lemma tensor_id {X Y : C} : id X #⊗ id Y = id (X ⊗ Y).
Proof.
  apply (functor_id tensor).
Qed.

Lemma tensor_comp {X Y Z X' Y' Z' : C} (f : X --> Y) (g : Y --> Z) (f' : X' --> Y') (g' : Y' --> Z') :
  (f · g) #⊗ (f' · g') = f #⊗ f' · g #⊗ g'.
Proof.
  rewrite binprod_comp.
  apply (functor_comp tensor).
Qed.

Definition is_z_iso_tensor_z_iso {X Y X' Y' : C} {f : X --> Y} {g : X' --> Y'}
           (f_is_z_iso : is_z_isomorphism f) (g_is_z_iso : is_z_isomorphism g) : is_z_isomorphism (f #⊗ g).
Proof.
  exact (functor_on_is_z_isomorphism _ (is_z_iso_binprod_z_iso f_is_z_iso g_is_z_iso)).
Defined.

Definition I_pretensor : C ⟶ C := functor_fix_fst_arg _ _ _ tensor I.

Lemma I_pretensor_ok: functor_on_objects I_pretensor = λ c, I ⊗ c.
Proof.
  apply idpath.
Qed.

Definition left_unitor : UU :=
  nat_z_iso I_pretensor (functor_identity C).

Definition left_unitor_to_nat_trans (λ' : left_unitor): nat_trans I_pretensor (functor_identity C)
  := nat_z_iso_to_trans λ'.
Coercion left_unitor_to_nat_trans: left_unitor >-> nat_trans.

Definition I_posttensor : C ⟶ C := functor_fix_snd_arg _ _ _ tensor I.

Lemma I_posttensor_ok: functor_on_objects I_posttensor = λ c, c ⊗ I.
Proof.
  apply idpath.
Qed.

Definition right_unitor : UU :=
  nat_z_iso I_posttensor (functor_identity C).

Definition right_unitor_to_nat_trans (ρ' : right_unitor): nat_trans I_posttensor (functor_identity C)
  := nat_z_iso_to_trans ρ'.
Coercion right_unitor_to_nat_trans: right_unitor >-> nat_trans.

Definition assoc_left : (C ⊠ C) ⊠ C ⟶ C :=
  functor_composite (pair_functor tensor (functor_identity _)) tensor.

Lemma assoc_left_ok: functor_on_objects assoc_left =
  λ c, (ob1 (ob1 c) ⊗ ob2 (ob1 c)) ⊗ ob2 c.
Proof.
  apply idpath.
Qed.

Definition assoc_right : (C ⊠ C) ⊠ C ⟶ C :=
  functor_composite
    (precategory_binproduct_unassoc _ _ _)
    (functor_composite (pair_functor (functor_identity _) tensor) tensor).

Lemma assoc_right_ok: functor_on_objects assoc_right =
  λ c, ob1 (ob1 c) ⊗ (ob2 (ob1 c) ⊗ ob2 c).
Proof.
  apply idpath.
Qed.

Definition associator : UU :=
  nat_z_iso assoc_left assoc_right.

Definition associator_to_nat_trans (α' : associator): nat_trans assoc_left assoc_right
  := nat_z_iso_to_trans α'.
Coercion associator_to_nat_trans: associator >-> nat_trans.

Definition triangle_eq (λ' : left_unitor) (ρ' : right_unitor) (α' : associator) : UU :=
  ∏ (a b : C), pr1 ρ' a #⊗ id b = pr1 α' ((a, I), b) · id a #⊗ pr1 λ' b.

Definition pentagon_eq (α' : associator) : UU :=
  ∏ (a b c d : C), pr1 α' ((a ⊗ b, c), d) · pr1 α' ((a, b), c ⊗ d) =
   pr1 α' ((a, b), c) #⊗ id d · pr1 α' ((a, b ⊗ c), d) · id a #⊗ pr1 α' ((b, c), d).

Definition is_strict (eq_λ : I_pretensor = functor_identity C) (λ' : left_unitor)
           (eq_ρ : I_posttensor = functor_identity C) (ρ' : right_unitor)
           (eq_α : assoc_left = assoc_right) (α' : associator) : UU :=
  (is_nat_z_iso_id eq_λ λ') × (is_nat_z_iso_id eq_ρ ρ') × (is_nat_z_iso_id eq_α α').

End Monoidal_Precat.

Definition monoidal_cat : UU :=
  ∑ C : category, ∑ tensor : C ⊠ C ⟶ C, ∑ I : C,
  ∑ λ' : left_unitor tensor I,
  ∑ ρ' : right_unitor tensor I,
  ∑ α' : associator tensor,
         (triangle_eq tensor I λ' ρ' α') × (pentagon_eq tensor α').

Definition mk_monoidal_cat (C: category)(tensor: C ⊠ C ⟶ C)(I: C)
  (λ': left_unitor tensor I)(ρ': right_unitor tensor I)(α': associator tensor)
  (eq1: triangle_eq tensor I λ' ρ' α')(eq2: pentagon_eq tensor α'): monoidal_cat :=
  (C,, (tensor,, (I,, (λ',, (ρ',, (α',, (eq1,, eq2))))))).

Definition monoidal_cat_cat (M : monoidal_cat) : category := pr1 M.
Coercion monoidal_cat_cat : monoidal_cat >-> category.

Section Monoidal_Cat_Accessors.

  Context (M : monoidal_cat).

Definition monoidal_cat_tensor : pr1 M ⊠ pr1 M ⟶ pr1 M := pr1 (pr2 M).

Definition monoidal_cat_unit : pr1 M := pr1 (pr2 (pr2 M)).

Definition monoidal_cat_left_unitor : left_unitor (pr1 (pr2 M)) (pr1 (pr2 (pr2 M))) := pr1 (pr2 (pr2 (pr2 M))).

Definition monoidal_cat_right_unitor : right_unitor (pr1 (pr2 M)) (pr1 (pr2 (pr2 M))) := pr1 (pr2 (pr2 (pr2 (pr2 M)))).

Definition monoidal_cat_associator : associator (pr1 (pr2 M)) := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 M))))).

Definition monoidal_cat_triangle_eq : triangle_eq (pr1 (pr2 M)) (pr1 (pr2 (pr2 M))) (pr1 (pr2 (pr2 (pr2 M)))) (pr1 (pr2 (pr2 (pr2 (pr2 M))))) (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 M)))))) := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 M)))))).

Definition monoidal_cat_pentagon_eq : pentagon_eq (pr1 (pr2 M)) (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 M)))))) := pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 M)))))).

End Monoidal_Cat_Accessors.

Definition strict_monoidal_cat : UU :=
  ∑ M : monoidal_cat,
  ∏ (eq_λ : I_pretensor (monoidal_cat_tensor M) (monoidal_cat_unit M) =
  functor_identity (pr1 M)),
  ∏ (eq_ρ : I_posttensor (monoidal_cat_tensor M) (monoidal_cat_unit M) =
  functor_identity (pr1 M)),
  ∏ (eq_α : assoc_left (monoidal_cat_tensor M) =
  assoc_right (monoidal_cat_tensor M)),
  is_strict (monoidal_cat_tensor M) (monoidal_cat_unit M) eq_λ (monoidal_cat_left_unitor M) eq_ρ (monoidal_cat_right_unitor M) eq_α (monoidal_cat_associator M).

Section swapped_tensor.

Context (M : monoidal_cat).

Definition swapping_of_tensor: M ⊠ M ⟶ M := functor_composite binswap_pair_functor (monoidal_cat_tensor M).

Definition associator_swapping_of_tensor: associator swapping_of_tensor.
  set (α := monoidal_cat_associator M).
  set (α' := nat_z_iso_to_trans_inv α).
  red.
  set (trafo := (pre_whisker reverse_three_args α'): (assoc_left swapping_of_tensor) ⟹ (assoc_right swapping_of_tensor)).
  assert (tisziso: is_nat_z_iso trafo).
  {
 red.
intro c.
set (aux := pr2 (nat_z_iso_inv α)).
    apply (pre_whisker_on_nat_z_iso reverse_three_args α' aux).
  }
  exact (trafo,, tisziso).
Defined.

Lemma triangle_eq_swapping_of_tensor: triangle_eq swapping_of_tensor (monoidal_cat_unit M)
  (monoidal_cat_right_unitor M) (monoidal_cat_left_unitor M) associator_swapping_of_tensor.
  red.
intros a b.
cbn.
  set (H := monoidal_cat_triangle_eq M).
  unfold triangle_eq in H.
  etrans.
  2: { apply cancel_precomposition.
       apply pathsinv0.
       apply H.
}
  clear H.
  rewrite assoc.
  etrans.
  {
 apply pathsinv0.
    apply id_left.
}
  apply cancel_postcomposition.
  apply pathsinv0.
  set (f := nat_z_iso_pointwise_z_iso (monoidal_cat_associator M)((b, monoidal_cat_unit M), a)).
  apply (z_iso_after_z_iso_inv f).
Qed.

Lemma pentagon_eq_swapping_of_tensor: pentagon_eq swapping_of_tensor associator_swapping_of_tensor.
  red.
intros a b c d.
cbn.
  set (H := monoidal_cat_pentagon_eq M).
  unfold pentagon_eq in H.
  set (f := nat_z_iso_pointwise_z_iso (monoidal_cat_associator M) ((d, c), monoidal_cat_tensor M (b, a))).
  apply (z_iso_inv_on_right _ _ _ f).
  apply pathsinv0.
  set (f' := nat_z_iso_pointwise_z_iso (monoidal_cat_associator M) ((monoidal_cat_tensor M (d, c), b), a)).
  apply (inv_z_iso_unique' _ _ _ f').
  unfold precomp_with.
  rewrite assoc.
  etrans.
  {
 apply cancel_postcomposition.
    apply H.
}
  clear H.
  repeat rewrite assoc.
  etrans.
  {
 do 2 apply cancel_postcomposition.
    rewrite <- assoc.
    apply cancel_precomposition.
    apply pathsinv0.
    apply (functor_comp (functor_fix_fst_arg _ _ _ (monoidal_cat_tensor M) d)).
  }
  etrans.
  {
 do 2 apply cancel_postcomposition.
    apply cancel_precomposition.
    apply maponpaths.
    apply (z_iso_inv_after_z_iso (nat_z_iso_pointwise_z_iso (monoidal_cat_associator M) ((c, b), a))).
}
  rewrite functor_id.
  rewrite id_right.
  etrans.
  {
 apply cancel_postcomposition.
    rewrite <- assoc.
    apply cancel_precomposition.
    apply (z_iso_inv_after_z_iso (nat_z_iso_pointwise_z_iso (monoidal_cat_associator M) ((d, monoidal_cat_tensor M (c, b)), a))).
}
  rewrite id_right.
  etrans.
  apply pathsinv0.
  apply (functor_comp (functor_fix_snd_arg _ _ _ (monoidal_cat_tensor M) a)).
  etrans.
  {
 apply maponpaths.
    apply (z_iso_inv_after_z_iso (nat_z_iso_pointwise_z_iso (monoidal_cat_associator M) ((d, c), b))).
}
  cbn.
  unfold functor_fix_snd_arg_mor.
  use functor_id.
Qed.

Definition swapping_of_monoidal_cat: monoidal_cat.
  use (mk_monoidal_cat M swapping_of_tensor).
  -
 exact (monoidal_cat_unit M).
  -
 apply monoidal_cat_right_unitor.
  -
 apply monoidal_cat_left_unitor.
  -
 exact associator_swapping_of_tensor.
  -
 exact triangle_eq_swapping_of_tensor.
  -
 exact pentagon_eq_swapping_of_tensor.
Defined.

End swapped_tensor.

Section coherence_lemmas.

Context {Mon_V : monoidal_cat}.

Let I        : Mon_V                  := monoidal_cat_unit Mon_V.
Let tensor   : Mon_V ⊠ Mon_V ⟶ Mon_V := monoidal_cat_tensor Mon_V.
Let α        : associator tensor      := monoidal_cat_associator Mon_V.
Let l_unitor : left_unitor tensor I   := monoidal_cat_left_unitor Mon_V.
Let r_unitor : right_unitor tensor I  := monoidal_cat_right_unitor Mon_V.

Local Notation "X ⊗ Y" := (tensor (X, Y)).
Local Notation "f #⊗ g" := (#tensor (f #, g)) (at level 31).

Lemma tensor_comp_left {X Y Z W : Mon_V} (f : X --> Y) (g : Y --> Z) : ((f · g) #⊗ id W) = (f #⊗ id W) · (g #⊗ id W).
Proof.
  rewrite <- (functor_comp tensor).
  change ((?x #, ?y) · (?z #, ?w)) with (x · z #, y · w).
  rewrite id_left.
  apply idpath.
Defined.

Lemma tensor_comp_right {X Y Z W : Mon_V} (f : X --> Y) (g : Y --> Z) : (id W #⊗ (f · g)) = (id W #⊗ f) · (id W #⊗ g).
Proof.
  rewrite <- (functor_comp tensor).
  change ((?x #, ?y) · (?z #, ?w)) with (x · z #, y · w).
  rewrite id_left.
  apply idpath.
Defined.

Lemma I_posttensor_faithful {X Y : Mon_V} {f g : X --> Y} : (f #⊗ id I) = (g #⊗ id I) -> f = g.
Proof.
  intro H.
  apply (pre_comp_with_z_iso_is_inj (is_z_isomorphism_is_inverse_in_precat (pr2 r_unitor _))).
  use (pathscomp0 (! (nat_trans_ax r_unitor _ _ f))).
  use (pathscomp0 _ (nat_trans_ax r_unitor _ _ g)).
  apply cancel_postcomposition.
  assumption.
Defined.

Lemma I_pretensor_faithful {X Y : Mon_V} {f g : X --> Y} : (id I #⊗ f) = (id I #⊗ g) -> f = g.
Proof.
  intro H.
  apply (pre_comp_with_z_iso_is_inj (is_z_isomorphism_is_inverse_in_precat (pr2 l_unitor _))).
  use (pathscomp0 (! (nat_trans_ax l_unitor _ _ f))).
  use (pathscomp0 _ (nat_trans_ax l_unitor _ _ g)).
  apply cancel_postcomposition.
  assumption.
Defined.

Lemma right_unitor_of_tensor (X Y : Mon_V) : r_unitor (X ⊗ Y) = α ((X, Y), I) · (id X #⊗ r_unitor Y).
Proof.
  apply I_posttensor_faithful.
  rewrite tensor_comp_left.
  apply (post_comp_with_z_iso_is_inj (is_z_isomorphism_is_inverse_in_precat (pr2 α (_, _)))).
  rewrite assoc'.
  apply (transportb (λ h, _ = _ · h) (nat_trans_ax α _ _ ((_#, _)#, _))).
  simpl.
  rewrite assoc.
  apply (transportb (λ h, _ = _ · #tensor (id _ #, h)) (monoidal_cat_triangle_eq Mon_V _ _)).
  apply (transportf (λ k, _ = _ · #tensor (k #, _)) (id_left (id X))).
  change (?x · ?z #, ?y · ?w) with ((x #, y) · (z #, w)).
  rewrite (functor_comp tensor).
  apply (transportb (λ h, h · _ = _) (monoidal_cat_triangle_eq Mon_V _ _)).
  apply (transportf (λ h, _ · #tensor (h #, _) · _ = _) (functor_id tensor (X, Y))).
  rewrite assoc'.
  apply (transportb (λ h, _ · h = _) (nat_trans_ax α _ _ ((_#, _)#, _))).
  rewrite !assoc.
  apply cancel_postcomposition.
  apply monoidal_cat_pentagon_eq.
Defined.

Lemma left_unitor_right_unitor_of_unit : l_unitor I = r_unitor I.
Proof.
  apply I_pretensor_faithful.
  apply (pre_comp_with_z_iso_is_inj (is_z_isomorphism_is_inverse_in_precat (pr2 α ((_, _), _)))).
  apply (pathscomp0 (! (monoidal_cat_triangle_eq Mon_V I I))).
  use (pathscomp0 _ (right_unitor_of_tensor I I)).
  apply (post_comp_with_z_iso_is_inj (is_z_isomorphism_is_inverse_in_precat (pr2 r_unitor _))).
  apply (nat_trans_ax r_unitor).
Defined.

Lemma left_unitor_of_tensor (X Y : Mon_V) : α ((I, X), Y) · l_unitor (X ⊗ Y) = l_unitor X #⊗ id Y.
Proof.
  apply I_pretensor_faithful.
  rewrite tensor_comp_right.
  apply (pre_comp_with_z_iso_is_inj (pr2 α ((I, (I ⊗ X)), Y))).
  use (pathscomp0 _ (nat_trans_ax α _ _ ((_ #, _) #, _))).
  simpl.
  apply (pre_comp_with_z_iso_is_inj (functor_on_is_z_isomorphism (functor_fix_snd_arg _ _ _ tensor Y) (pr2 α ((I, I), X)))).
  simpl.
  unfold functor_fix_snd_arg_mor.
  change (make_dirprod ?x ?y) with (x #, y).
  rewrite !assoc.
  apply (transportf (λ h, _ = h · _) (functor_comp tensor _ _)).
  change ((?x #, ?y) · (?z #, ?w)) with (x · z #, y · w).
  apply (transportf (λ h, h · _ = _) (monoidal_cat_pentagon_eq Mon_V I I X Y)).
  rewrite assoc'.
  apply (transportf (λ h, _ · h = _) (monoidal_cat_triangle_eq Mon_V _ _)).
  simpl.
  apply (transportf (λ h, _ · #tensor (_ #, h) = _) (functor_id tensor (X, Y))).
  apply (pathscomp0 (! (nat_trans_ax α _ _ ((_ #, _) #, _)))).
  simpl.
  apply cancel_postcomposition.
  apply pathsinv0.
  apply maponpaths.
  apply dirprod_paths; simpl; [|apply id_left].
  apply pathsinv0.
  apply monoidal_cat_triangle_eq.
Defined.

Lemma tensor_z_isomorphism_left : ∏ (x y z : Mon_V) (f : x --> y) (f_z_iso : is_z_isomorphism f), # tensor (is_z_isomorphism_mor f_z_iso #, id z) = is_z_isomorphism_mor (functor_on_is_z_isomorphism (functor_fix_snd_arg _ _ _ tensor z) f_z_iso).
Proof.
  intros.
  reflexivity.
Qed.

Lemma tensor_z_isomorphism_right : ∏ (x y z : Mon_V) (f : x --> y) (f_z_iso : is_z_isomorphism f), # tensor (id z #, is_z_isomorphism_mor f_z_iso) = is_z_isomorphism_mor (functor_on_is_z_isomorphism (functor_fix_fst_arg _ _ _ tensor z) f_z_iso).
Proof.
  intros.
  reflexivity.
Qed.

Lemma monoidal_cat_triangle_eq_inv (X Y : Mon_V) : (nat_z_iso_to_trans_inv r_unitor X #⊗ id Y) · α ((X, I), Y) = (id X #⊗ nat_z_iso_to_trans_inv l_unitor Y).
Proof.
  cbn.
  rewrite (tensor_z_isomorphism_right _ _ _ _ _ : #tensor _ = _).
  rewrite (tensor_z_isomorphism_left _ _ _ _ _ : #tensor _ = _).
  change (is_z_isomorphism_mor ?x) with (inv_from_z_iso (_,,x)).
  apply z_iso_inv_on_right, z_iso_inv_on_left.
  apply monoidal_cat_triangle_eq.
Qed.

Corollary left_unitor_inv_right_unitor_inv_of_unit : nat_z_iso_to_trans_inv l_unitor I = nat_z_iso_to_trans_inv r_unitor _.
Proof.
  apply (post_comp_with_z_iso_is_inj (is_z_isomorphism_is_inverse_in_precat (pr2 l_unitor _))).
  apply (pathscomp0 (is_inverse_in_precat2 (is_z_isomorphism_is_inverse_in_precat (pr2 l_unitor _)))).
  apply (transportb (λ f, id _ = is_z_isomorphism_mor _ · f) left_unitor_right_unitor_of_unit).
  apply pathsinv0.
  apply (is_inverse_in_precat2 (is_z_isomorphism_is_inverse_in_precat (pr2 r_unitor _))).
Qed.

Corollary left_unitor_inv_of_tensor (X Y : Mon_V) : (nat_z_iso_to_trans_inv l_unitor _ #⊗ id _) · α ((_, _), _) = nat_z_iso_to_trans_inv l_unitor (X ⊗ Y).
Proof.
  simpl.
  rewrite tensor_z_isomorphism_left.
  change (is_z_isomorphism_mor ?x) with (inv_from_z_iso (_,,x)).
  apply z_iso_inv_on_right, z_iso_inv_on_left.
  apply pathsinv0.
  apply left_unitor_of_tensor.
Qed.

Corollary right_unitor_inv_of_tensor (X Y : Mon_V) : (id _ #⊗ nat_z_iso_to_trans_inv r_unitor _) = nat_z_iso_to_trans_inv r_unitor (X ⊗ Y)  · α ((_, _), _).
Proof.
  simpl.
  rewrite tensor_z_isomorphism_right.
  change (is_z_isomorphism_mor ?x) with (inv_from_z_iso (_,,x)).
  apply pathsinv0.
  apply z_iso_inv_on_right, z_iso_inv_on_left.
  apply right_unitor_of_tensor.
Qed.

End coherence_lemmas.
Module Export StandardFiniteSets.

Export UniMath.Foundations.NaturalNumbers.
Import UniMath.MoreFoundations.DecidablePropositions.
Import UniMath.MoreFoundations.NegativePropositions.

Definition stn ( n : nat ) := ∑ m, m < n.
Definition make_stn n m (l:m<n) := (m,,l) : stn n.
Definition stntonat ( n : nat ) : stn n -> nat := @pr1 _ _ .
Coercion stntonat : stn >-> nat.
Lemma stnlt {n : nat} (i:stn n) : i < n.
Proof.
  intros.
  exact (pr2 i).
Defined.

Notation " 'stnpr' j " := (j,,idpath _) ( at level 70 ).
Notation " 'stnel' ( i , j ) " := ( (j,,idpath _) : stn i ) ( at level 70 ).

Declare Scope stn.
Delimit Scope stn with stn.

Notation "⟦ n ⟧" := (stn n) : stn.

Notation "● i" := (i ,, (idpath _ : natgtb _ _ = _)) (at level 35) : stn.

Lemma isinclstntonat ( n : nat ) : isincl ( stntonat n ).
  intro.
  use isinclpr1.
  intro x.
  apply ( pr2 ( natlth x n ) ).
Defined.

Definition stntonat_incl n := make_incl (stntonat n) (isinclstntonat n).

Lemma isdecinclstntonat ( n : nat ) : isdecincl ( stntonat n ).
  intro.
  use isdecinclpr1.
  intro x.
  apply isdecpropif.
  use pr2.
  apply isdecrelnatgth.
Defined.

Lemma neghfiberstntonat ( n m : nat ) ( is : natgeh m n ) : ¬ ( hfiber ( stntonat n ) m ).
Proof.
  intros.
  intro h.
  destruct h as [ j e ].
  destruct j as [ j is' ].
  simpl in e.
  rewrite e in is'.
  apply ( natgehtonegnatlth _ _ is is' ).
Defined.

Lemma iscontrhfiberstntonat ( n m : nat ) ( is : natlth m n ) :
  iscontr ( hfiber ( stntonat n ) m ).
  intros.
  apply ( iscontrhfiberofincl ( stntonat n ) ( isinclstntonat n ) ( make_stn n m is ) ).
Defined.

Local Open Scope stn.

Lemma stn_ne_iff_neq {n : nat} (i j: ⟦n⟧ ) : ¬ (i = j) <-> stntonat _ i ≠ stntonat _ j.
Proof.
  intros.
split.
  -
 intro ne.
apply nat_nopath_to_neq.
Set Printing Coercions.
idtac.
    intro e; apply ne; clear ne.
apply subtypePath_prop.
assumption.
  -
 simpl.
intros neq e.
apply (nat_neq_to_nopath neq), maponpaths.
assumption.
  Unset Printing Coercions.
Defined.

Lemma stnneq {n : nat} : neqReln (⟦n⟧).
Proof.

  intros i j.
exists (i ≠ j)%nat.
split.
  -
 apply propproperty.
  -
 apply stn_ne_iff_neq.
Defined.

Notation " x ≠ y " := ( stnneq x y ) (at level 70, no associativity) : stn.

Lemma isisolatedinstn { n : nat } ( x : ⟦n⟧ ) : isisolated _ x.
Proof.
  intros.
  apply ( isisolatedinclb ( stntonat n ) ( isinclstntonat n ) x ( isisolatedn x ) ).
Defined.

Lemma stnneq_iff_nopath {n : nat} (i j: ⟦n⟧ ) : ¬ (i = j) <-> i ≠ j.
Proof.
  intros.
  apply negProp_to_iff.
Defined.

Definition stnneq_to_nopath {n : nat} (i j: ⟦n⟧ ) : ¬ (i = j) <- i ≠ j
  := pr2 (stn_ne_iff_neq i j).

Corollary isdeceqstn ( n : nat ) : isdeceq (⟦n⟧).
Proof.
  unfold isdeceq.
  intros x x'.
  apply (isisolatedinstn x x' ).
Defined.

Lemma stn_eq_or_neq {n : nat} (i j: ⟦n⟧ ) : (i=j) ⨿ (i≠j).
Proof.
  intros.
induction (nat_eq_or_neq i j) as [eq|ne].
  -
 apply ii1, subtypePath_prop.
assumption.
  -
 apply ii2.
assumption.
Defined.

Definition weqisolatedstntostn ( n : nat ) : ( isolated (⟦n⟧) ) ≃ ⟦n⟧.
Proof.
  apply weqpr1.
  intro x.
  apply iscontraprop1.
  apply isapropisisolated.
  set ( int := isdeceqstn n x  ).
  assumption.
Defined.

Corollary isasetstn ( n : nat ) : isaset (⟦n⟧).
Proof.
  intro.
  apply ( isasetifdeceq _ ( isdeceqstn n ) ).
Defined.

Definition stnset n := make_hSet (⟦n⟧) (isasetstn n).

Definition stn_to_nat n : stnset n -> natset := pr1.

Definition stnposet ( n : nat ) : Poset.
  unfold Poset.
  exists (_,,isasetstn n).
  unfold PartialOrder.
  exists (λ i j: ⟦n⟧, i ≤ j)%dnat.
  unfold isPartialOrder.
  split.
  -
 unfold ispreorder.
    split.
    *
 intros i j k.
apply istransnatleh.
    *
 intros i.
apply isreflnatleh.
  -
 intros i j r s.
apply (invmaponpathsincl _ ( isinclstntonat _ )).
    apply isantisymmnatleh; assumption.
Defined.

Definition lastelement {n : nat} : ⟦S n⟧.
Proof.
  split with n.
  apply ( natgthsnn n ).
Defined.

Lemma lastelement_ge {n : nat} : ∏ i : ⟦S n⟧, @lastelement n ≥ i.
Proof.
  intros.
  apply natlthsntoleh.
  unfold lastelement.
  apply stnlt.
Defined.

Definition firstelement {n : nat} : ⟦S n⟧.
Proof.
  exists 0.
  apply natgthsn0.
Defined.

Lemma firstelement_le {n : nat} : ∏ i : ⟦S n⟧, @firstelement n ≤ i.
Proof.
  intros.
  apply idpath.
Defined.

Definition firstValue {X:UU} {n:nat} : (⟦S n⟧ -> X) -> X
  := λ x, x firstelement.

Definition lastValue {X:UU} {n:nat} : (⟦S n⟧ -> X) -> X
  := λ x, x lastelement.

Local Lemma dualelement_0_empty {n : nat} (i : ⟦n⟧ ) (e : 0 = n) : empty.
Proof.
  induction e.
  apply (negnatlthn0 _ (stnlt i)).
Qed.

Local Lemma dualelement_lt (i n : nat) (H : n > 0) : n - 1 - i < n.
Proof.
  rewrite natminusminus.
  apply (natminuslthn _ _ H).
  apply idpath.
Qed.

Definition dualelement {n : nat} (i : ⟦n⟧ ) : ⟦n⟧.
Proof.
  induction (natchoice0 n) as [H | H].
  -
 exact (make_stn n (n - 1 - i) (fromempty (dualelement_0_empty i H))).
  -
 exact (make_stn n (n - 1 - i) (dualelement_lt i n H)).
Defined.

Definition stnmtostnn ( m n : nat ) (isnatleh: natleh m n ) : ⟦m⟧ -> ⟦n⟧ :=
  λ x : ⟦m⟧, match x with tpair _ i is
                 => make_stn _ i ( natlthlehtrans i m n is isnatleh ) end.

Definition stn_left (m n : nat) : ⟦m⟧ -> ⟦m+n⟧.
Proof.
  intros i.
  exists (pr1 i).
  apply (natlthlehtrans (pr1 i) m (m+n) (pr2 i)).
  apply natlehnplusnm.
Defined.

Definition stn_right (m n : nat) : ⟦n⟧ -> ⟦m+n⟧.
Proof.
  intros i.
  exists (m+pr1 i).
  apply natlthandplusl.
  exact (pr2 i).
Defined.

Definition stn_left_compute (m n : nat) (i: ⟦m⟧ ) : pr1 (stn_left m n i) = i.
Proof.
  intros.
  apply idpath.
Defined.

Definition stn_right_compute (m n : nat) (i: ⟦n⟧ ) : pr1 (stn_right m n i) = m+i.
Proof.
  intros.
  apply idpath.
Defined.

Lemma stn_left_0 {m:nat} {i:⟦m⟧} (e: m=m+0) : stn_left m 0 i = transportf stn e i.
Proof.
  intros.
  apply subtypePath_prop.
  induction e.
  apply idpath.
Defined.

Definition stn_left' (m n : nat) : m ≤ n -> ⟦m⟧ -> ⟦n⟧.
Proof.
  intros le i.
  exact (make_stn _ _ (natlthlehtrans _ _ _ (stnlt i) le)).
Defined.

Definition stn_left'' {m n : nat} : m < n -> ⟦m⟧ -> ⟦n⟧.
Proof.
  intros le i.
  exact (make_stn _ _ (istransnatlth _ _ _ (stnlt i) le)).
Defined.

Lemma stn_left_compare (m n : nat) (r : m ≤ m+n) : stn_left' m (m+n) r = stn_left m n.
Proof.
  intros.
  apply funextfun; intro i.
  apply subtypePath_prop.
  apply idpath.
Defined.

Definition dni {n : nat} ( i : ⟦S n⟧ ) : ⟦n⟧ -> ⟦S n⟧.
Proof.
intros x.
exists (di i x).
unfold di.
       induction (natlthorgeh x i) as [lt|ge].
       -
 apply natgthtogths.
exact (pr2 x).
       -
 exact (pr2 x).
Defined.

Definition compute_pr1_dni_last (n : nat) (i: ⟦n⟧ ) : pr1 (dni lastelement i) = pr1 i.
Proof.
  intros.
unfold dni,di; simpl.
induction (natlthorgeh i n) as [q|q].
  -
 apply idpath.
  -
 contradicts (pr2 i) (natlehneggth q).
Defined.

Definition compute_pr1_dni_first (n : nat) (i: ⟦n⟧ ) : pr1 (dni firstelement i) = S (pr1 i).
Proof.
  intros.
  apply idpath.
Defined.

Lemma dni_last {n : nat} (i: ⟦n⟧ ) : pr1 (dni lastelement i) = i.
Proof.
  intros.
  induction i as [i I].
  unfold dni,di.
simpl.
  induction (natlthorgeh i n) as [g|g].
  {
 apply idpath.
}
  simpl.
  contradicts (natlehtonegnatgth _ _ g) I.
Defined.

Lemma dni_first {n : nat} (i: ⟦n⟧ ) : pr1 (dni firstelement i) = S i.
Proof.
  intros.
  apply idpath.
Defined.

Definition dni_firstelement {n : nat} : ⟦n⟧ -> ⟦S n⟧.

Proof.
  intros h.
  exact (S (pr1 h),, pr2 h).
Defined.

Definition replace_dni_first (n : nat) : dni (@firstelement n) = dni_firstelement.
Proof.
  intros.
  apply funextfun; intros i.
  apply subtypePath_prop.
  exact (compute_pr1_dni_first n i).
Defined.

Definition dni_lastelement {n : nat} : ⟦n⟧ -> ⟦S n⟧.

Proof.
  intros h.
  exists (pr1 h).
  exact (natlthtolths _ _ (pr2 h)).
Defined.

Definition replace_dni_last (n : nat) : dni (@lastelement n) = dni_lastelement.
Proof.
  intros.
  apply funextfun; intros i.
  apply subtypePath_prop.
  exact (compute_pr1_dni_last n i).
Defined.

Lemma dni_lastelement_ord {n : nat} : ∏ i j: ⟦n⟧, i≤j -> dni_lastelement i ≤ dni_lastelement j.
Proof.
  intros ? ? e.
  exact e.
Defined.

Definition pr1_dni_lastelement {n : nat} {i: ⟦n⟧ } : pr1 (dni_lastelement i) = pr1 i.
Proof.
  intros.
  apply idpath.
Defined.

Lemma dni_last_lt {n : nat} (j : ⟦ n ⟧) : dni lastelement j < @lastelement n.
Proof.
  intros.
  induction j as [j J].
  simpl.
unfold di.
  induction (natlthorgeh j n) as [L|M].
  -
 exact J.
  -
 apply fromempty.
    exact (natlthtonegnatgeh _ _ J M).
Defined.

Lemma dnicommsq ( n : nat ) ( i : ⟦S n⟧ ) :
  commsqstr( dni i )  ( stntonat ( S n ) ) ( stntonat n ) ( di i ).
Proof.
  intros.
  intro x.
  unfold dni.
unfold di.
  destruct ( natlthorgeh x i ).
  -
 simpl.
    apply idpath.
  -
 simpl.
    apply idpath.
Defined.

Theorem dnihfsq ( n : nat ) ( i : ⟦S n⟧ ) :
  hfsqstr ( di i ) ( stntonat ( S n ) ) ( stntonat n ) ( dni i ).
Proof.
  intros.
  apply ( ishfsqweqhfibersgtof' ( di i ) ( stntonat ( S n ) ) ( stntonat n ) ( dni i ) ( dnicommsq _ _  ) ).
  intro x.
  destruct ( natlthorgeh x n ) as [ g | l ].
  -
 assert ( is1 : iscontr ( hfiber ( stntonat n ) x ) ).
    {
 apply iscontrhfiberstntonat.
assumption.
}
    assert ( is2 : iscontr ( hfiber ( stntonat ( S n ) ) ( di i x )  ) ).
    {
 apply iscontrhfiberstntonat.
      apply ( natlehlthtrans _ ( S x ) ( S n ) ( natlehdinsn i x ) g ).
}
    apply isweqcontrcontr.
    +
 assumption.
    +
 assumption.
  -
 assert ( is1 : ¬ ( hfiber ( stntonat ( S n ) ) ( di i x ) ) ).
    {
 apply neghfiberstntonat.
      unfold di.
      destruct ( natlthorgeh x i ) as [ l'' | g' ].
      +
 destruct ( natgehchoice2 _ _ l ) as [ g' | e ].
        *
 apply g'.
        *
 rewrite e in l''.
          assert ( int := natlthtolehsn _ _ l'' ).
          contradicts (natgthnegleh (pr2 i)) int.
      +
 apply l.
    }
    apply ( isweqtoempty2 _ is1 ).
Defined.

Lemma dni_neq_i {n : nat} (i : ⟦S n⟧) (j : ⟦n⟧ ) : i ≠ @dni n i j.
Proof.
  intros.
  simpl.
  apply di_neq_i.
Defined.

Lemma weqhfiberdnihfiberdi ( n : nat ) ( i j : ⟦S n⟧ ) :
  ( hfiber ( dni i ) j ) ≃ ( hfiber ( di i ) j ).
Proof.
  intros.
  apply ( weqhfibersg'tof _ _ _ _ ( dnihfsq n i ) j ).
Defined.

Lemma neghfiberdni ( n : nat ) ( i : ⟦S n⟧ ) : ¬ ( hfiber ( dni i ) i ).
Proof.
  intros.
  apply ( negf ( weqhfiberdnihfiberdi n i i ) ( neghfiberdi i ) ).
Defined.

Lemma iscontrhfiberdni ( n : nat ) ( i j : ⟦S n⟧ ) : i ≠ j -> iscontr ( hfiber ( dni i ) j ).
Proof.
  intros ne.
  exact ( iscontrweqb ( weqhfiberdnihfiberdi n i j ) ( iscontrhfiberdi i j ne ) ).
Defined.

Lemma isdecincldni ( n : nat ) ( i : ⟦S n⟧ ) : isdecincl ( dni i ).
Proof.
 intros.
intro j.
induction ( stn_eq_or_neq i j ) as [eq|ne].
        -
 induction eq.
apply ( isdecpropfromneg ( neghfiberdni n i ) ).
        -
 exact ( isdecpropfromiscontr (iscontrhfiberdni _ _ _ ne) ).
Defined.

Lemma isincldni ( n : nat ) ( i : ⟦S n⟧ ) : isincl ( dni i ).
Proof.
  intros.
  exact ( isdecincltoisincl _  ( isdecincldni n i ) ).
Defined.

Definition sni {n : nat} ( i : ⟦n⟧ ) : ⟦n⟧ <- ⟦S n⟧.
Proof.
  intros j.
exists (si i j).
unfold si.
induction (natlthorgeh i j) as [lt|ge].
  -
 induction j as [j J].
induction i as [i I].
simpl.
    induction j as [|j _].
    +
 contradicts (negnatlthn0 i) lt.
    +
 change (S j - 1 < n).
      change (S j) with (1 + j).
      rewrite natpluscomm.
      rewrite plusminusnmm.
      exact J.
  -
 induction i as [i I].
    exact (natlehlthtrans _ _ _ ge I).
Defined.

Definition stn_compl {n : nat} (i: ⟦n⟧ ) := compl_ne _ i (stnneq i).

Definition dnitocompl ( n : nat ) ( i : ⟦S n⟧ ) : ⟦n⟧ -> stn_compl i.
Proof.
  intros j.
  exists ( dni i j ).
  apply dni_neq_i.
Defined.

Lemma isweqdnitocompl  ( n : nat ) ( i : ⟦S n⟧ ) : isweq ( dnitocompl n i ).
Proof.
  intros jni.
  assert ( w := samehfibers ( dnitocompl n i )  _ ( isinclpr1compl_ne _ i _ ) jni ) ;
    simpl in w.
  apply (iscontrweqb w).
  apply iscontrhfiberdni.
  exact (pr2 jni).
Defined.

Definition weqdnicompl {n : nat} (i: ⟦S n⟧ ): ⟦n⟧ ≃ stn_compl i.
Proof.
  intros.
  set (w := weqdicompl (stntonat _ i)).
  assert (eq : ∏ j, j < n <-> pr1 (w j) < S n).
  {
 simpl in w.
intros j.
unfold w.
    change (pr1 ((weqdicompl i) j)) with (di (stntonat _ i) j).
    unfold di.
    induction (natlthorgeh j i) as [lt|ge].
    -
 split.
      +
 apply natlthtolths.
      +
 intros _.
exact (natlehlthtrans (S j) i (S n) lt (pr2 i)).
    -
 split; exact (idfun _).
}
  refine (_ ∘ (weq_subtypes w (λ j, j < n) (λ j, pr1 j < S n) eq))%weq.
  use weqtotal2comm12.
Defined.

Definition weqdnicompl_compute {n : nat} (j: ⟦S n⟧ ) (i: ⟦n⟧ ) :
  pr1 (weqdnicompl j i) = dni j i.
Proof.
  intros.
  apply subtypePath_prop.
  apply idpath.
Defined.

Definition weqdnicoprod_provisional (n : nat) (j : ⟦S n⟧) : ⟦n⟧ ⨿ unit ≃ ⟦S n⟧.
Proof.
  intros.
  apply (weqcomp (weqcoprodf (weqdnicompl j) (idweq unit))
                 (weqrecompl_ne (⟦S n⟧) j (isdeceqstn (S n) j) (stnneq j))).
Defined.

Opaque weqdnicoprod_provisional.

Definition weqdnicoprod_map {n : nat} (j : ⟦S n⟧ ) : ⟦n⟧ ⨿ unit -> ⟦S n⟧.
Proof.
  intros x.
induction x as [i|t].
  -
 exact (dni j i).
  -
 exact j.
Defined.

Definition weqdnicoprod_compute {n : nat} (j : ⟦S n⟧ ) :
  weqdnicoprod_provisional n j ~ weqdnicoprod_map j.
Proof.
  intros.
  intros i.
  induction i as [i|i].
  -
 apply subtypePath_prop.
induction i as [i I].
apply idpath.
  -
 apply idpath.
Defined.

Definition weqdnicoprod (n : nat) (j : ⟦S n⟧ ) : ⟦n⟧ ⨿ unit ≃ ⟦S n⟧.
Proof.
  intros.
  apply (make_weq (weqdnicoprod_map j)).
  apply (isweqhomot _ _ (weqdnicoprod_compute _)).
  apply weqproperty.
Defined.

Definition weqoverdnicoprod {n : nat} (P: ⟦S n⟧ → UU) :
  (∑ i, P i) ≃ (∑ j, P(dni lastelement j)) ⨿ P lastelement.
Proof.
  intros.
  use (weqcomp (weqtotal2overcoprod' P (weqdnicoprod n lastelement))).
  apply weqcoprodf.
  -
 apply idweq.
  -
 apply weqtotal2overunit.
Defined.

Lemma weqoverdnicoprod_eq1 {n : nat} (P: ⟦S n⟧ → UU) j p :
  invmap (weqoverdnicoprod P) (ii1 (j,,p)) = ( dni lastelement j ,, p ).
Proof.
  intros.
  apply idpath.
Defined.

Definition weqdnicoprod_invmap {n : nat} (j : ⟦S n⟧ ) : ⟦n⟧ ⨿ unit <- ⟦S n⟧.

Proof.
  intros i.
  induction (isdeceqstn (S n) i j) as [eq|ne].
  -
 exact (ii2 tt).
  -
 apply ii1.
induction i as [i I].
induction j as [j J].
    choose (i < j)%dnat a a.
    +
 exists i.
exact (natltltSlt _ _ _ a J).
    +
 exists (i - 1).
      induction (natlehchoice _ _ (negnatgthtoleh a)) as [b|b].
      *
 induction (natlehchoice4 _ _ I) as [c|c].
        --
 apply (natlehlthtrans (i - 1) i n).
           ++
 apply natminuslehn.
           ++
 exact c.
        --
 induction c.
apply natminuslthn.
           ++
 apply (natlehlthtrans _ j _).
              **
 apply natleh0n.
              **
 exact b.
           ++
 apply natlthnsn.
      *
 induction b.
        induction (ne (@subtypePath_prop _ _ (make_stn _ j I) (make_stn _ j J) (idpath j))).
Defined.

Definition negstn0 : ¬ (⟦0⟧).
Proof.
  intro x.
  destruct x as [ a b ].
  apply ( negnatlthn0 _ b ).
Defined.

Definition weqstn0toempty : ⟦0⟧ ≃ empty.
Proof.
  apply weqtoempty.
  apply negstn0.
Defined.

Definition weqstn1tounit : ⟦1⟧ ≃ unit.
Proof.
  set ( f := λ x : ⟦1⟧, tt ).
  apply weqcontrcontr.
  -
 split with lastelement.
    intro t.
    destruct t as [ t l ].
    set ( e := natlth1tois0 _ l ).
    apply ( invmaponpathsincl _ ( isinclstntonat 1 ) ( make_stn _ t l ) lastelement e ).
  -
 apply iscontrunit.
Defined.

Corollary iscontrstn1 : iscontr (⟦1⟧).
Proof.
  apply iscontrifweqtounit.
  apply weqstn1tounit.
Defined.

Corollary isconnectedstn1 : ∏ i1 i2 : ⟦1⟧, i1 = i2.
Proof.
  intros i1 i2.
  apply (invmaponpathsweq weqstn1tounit).
  apply isProofIrrelevantUnit.
Defined.

Lemma isinclfromstn1 { X : UU } ( f : ⟦1⟧ -> X ) ( is : isaset X ) : isincl f.
Proof.
  intros.
  apply ( isinclbetweensets f ( isasetstn 1 ) is ).
  intros x x' e.
  apply ( invmaponpathsweq weqstn1tounit x x' ( idpath tt ) ).
Defined.

Definition weqstn2tobool : ⟦2⟧ ≃ bool.
Proof.
  set ( f := λ j : ⟦2⟧, match ( isdeceqnat j 0 ) with
                            ii1 _ => false
                          | ii2 _ => true
                          end ).
  set ( g := λ b : bool, match b with
                        false => make_stn 2 0 ( idpath true )
                      | true => make_stn 2 1 ( idpath true )
                      end ).
  split with f.
  assert ( egf : ∏ j : _ , paths ( g ( f j ) ) j ).
  {
 intro j.
    unfold f.
    destruct ( isdeceqnat j 0 ) as [ e | ne ].
    -
 apply ( invmaponpathsincl _ ( isinclstntonat 2 ) ).
      rewrite e.
      apply idpath.
    -
 apply ( invmaponpathsincl _ ( isinclstntonat 2 ) ).
      destruct j as [ j l ].
      simpl.
      set ( l' := natlthtolehsn _ _ l ).
      destruct ( natlehchoice _ _ l' ) as [ l'' | e ].
      +
 simpl in ne.
        destruct  ( ne ( natlth1tois0 _ l'' ) ).
      +
 apply ( pathsinv0 ( invmaponpathsS _ _ e ) ).
  }
  assert ( efg : ∏ b : _ , paths ( f ( g b ) ) b ).
  {
 intro b.
    unfold g.
    destruct b.
    -
 apply idpath.
    -
 apply idpath.
  }
  apply ( isweq_iso _ _ egf efg ).
Defined.

Lemma isinjstntonat (n : nat) : isInjectiveFunction (pr1 : stnset n -> natset).
Proof.
  intros i j.
  apply subtypePath_prop.
Defined.

Definition weqfromcoprodofstn_invmap (n m : nat) : ⟦n + m⟧ -> (⟦n⟧ ⨿ ⟦m⟧).
Proof.
  intros i.
  induction (natlthorgeh i n) as [i1 | i2].
  -
 exact (ii1 (make_stn n i i1)).
  -
 exact (ii2 (make_stn m (i - n) (nat_split (pr2 i) i2))).
Defined.

Lemma weqfromcoprodofstn_invmap_r0 (n : nat) (i : ⟦n+0⟧ ) :
  weqfromcoprodofstn_invmap n 0 i = ii1 (transportf stn (natplusr0 n) i).
Proof.
  intros.
  unfold weqfromcoprodofstn_invmap.
  simpl.
  induction (natlthorgeh i n) as [I|J].
  -
 simpl.
apply maponpaths.
apply subtypePath_prop.
simpl.
    induction (natplusr0 n).
apply idpath.
  -
 simpl.
apply fromempty.
induction (! natplusr0 n).
    exact (natgehtonegnatlth _ _ J (stnlt i)).
Defined.

Definition weqfromcoprodofstn_map (n m : nat) : (⟦n⟧ ⨿ ⟦m⟧) -> ⟦n+m⟧.
Proof.
  intros i.
  induction i as [i | i].
  -
 apply stn_left.
assumption.
  -
 apply stn_right.
assumption.
Defined.

Lemma weqfromcoprodofstn_eq1 (n m : nat) :
  ∏ x : ⟦n⟧ ⨿ ⟦m⟧, weqfromcoprodofstn_invmap n m (weqfromcoprodofstn_map n m x) = x.
Proof.
  intros x.
  unfold weqfromcoprodofstn_map, weqfromcoprodofstn_invmap.
unfold coprod_rect.
  induction x as [x | x].
  -
 induction (natlthorgeh (stn_left n m x) n) as [H | H].
    +
 apply maponpaths.
apply isinjstntonat.
apply idpath.
    +
 apply fromempty.
apply (natlthtonegnatgeh x n (stnlt x) H).
  -
 induction (natlthorgeh (stn_right n m x) n) as [H | H].
    +
 apply fromempty.
      set (tmp := natlehlthtrans n (n + x) n (natlehnplusnm n x) H).
      use (isirrefl_natneq n (natlthtoneq _ _ tmp)).
    +
 apply maponpaths.
apply isinjstntonat.
cbn.
      rewrite natpluscomm.
apply plusminusnmm.
Qed.

Lemma weqfromcoprodofstn_eq2 (n m : nat) :
  ∏ y : ⟦n+m⟧, weqfromcoprodofstn_map n m (weqfromcoprodofstn_invmap n m y) = y.
Proof.
  intros x.
  unfold weqfromcoprodofstn_map, weqfromcoprodofstn_invmap.
unfold coprod_rect.
  induction (natlthorgeh x n) as [H | H].
  -
 apply isinjstntonat.
apply idpath.
  -
 induction (natchoice0 m) as [H1 | H1].
    +
 apply fromempty.
induction H1.
induction (! (natplusr0 n)).
      use (natlthtonegnatgeh x n (stnlt x) H).
    +
 apply isinjstntonat.
cbn.
rewrite natpluscomm.
apply minusplusnmm.
apply H.
Qed.

Theorem weqfromcoprodofstn (n m : nat) : (⟦n⟧ ⨿ ⟦m⟧) ≃ ⟦n+m⟧.
Proof.
  use (tpair _ (weqfromcoprodofstn_map n m)).
  use (isweq_iso _ (weqfromcoprodofstn_invmap n m)).
  -
 exact (weqfromcoprodofstn_eq1 n m).
  -
 exact (weqfromcoprodofstn_eq2 n m).
Defined.

Definition pr1_eqweqmap_stn (m n : nat) (e: m=n) (i: ⟦m⟧ ) :
  pr1 (pr1weq (eqweqmap (maponpaths stn e)) i) = pr1 i.
Proof.
  intros.
  induction e.
  apply idpath.
Defined.

Definition coprod_stn_assoc (l m n : nat) : (
  eqweqmap (maponpaths stn (natplusassoc l m n))
           ∘ weqfromcoprodofstn (l+m) n
           ∘ weqcoprodf (weqfromcoprodofstn l m) (idweq _)
  ~
  weqfromcoprodofstn l (m+n)
           ∘ weqcoprodf (idweq _) (weqfromcoprodofstn m n)
           ∘ weqcoprodasstor _ _ _
  ) %weq.
Proof.
  intros.
  intros abc.
  simpl.
  apply (invmaponpathsincl pr1).
apply isinclstntonat.
  rewrite pr1_eqweqmap_stn.
  induction abc as [[a|b]|c].
  -
 simpl.
apply idpath.
  -
 simpl.
apply idpath.
  -
 simpl.
apply natplusassoc.
Defined.

Definition stnsum {n : nat} (f : ⟦n⟧ -> nat) : nat.
Proof.
  revert f.
  induction n as [ | n IHn].
  -
 intro.
exact 0.
  -
 intro f.
exact (IHn (λ i, f (dni lastelement i)) + f lastelement).
Defined.

Lemma stnsum_step {n : nat} (f: ⟦S n⟧ -> nat) :
  stnsum f = stnsum (f ∘ (dni lastelement)) + f lastelement.
Proof.
  intros.
  apply idpath.
Defined.

Lemma stnsum_eq {n : nat} (f g: ⟦n⟧ -> nat) : f ~ g -> stnsum f = stnsum g.
Proof.
  intros h.
  induction n as [|n IH].
  -
 apply idpath.
  -
 rewrite 2? stnsum_step.
    induction (h lastelement).
    apply (maponpaths (λ i, i + f lastelement)).
    apply IH.
    intro x.
    apply h.
Defined.

Lemma transport_stnsum {m n : nat} (e: m=n) (g: ⟦n⟧ -> nat) :
  stnsum g = stnsum (λ i, g(transportf stn e i)).
Proof.
  intros.
  induction e.
  apply idpath.
Defined.

Lemma stnsum_le {n : nat} (f g: ⟦n⟧ -> nat) : (∏ i, f i ≤ g i) -> stnsum f ≤ stnsum g.
Proof.
  intros le.
  induction n as [|n IH].
  -
 simpl.
apply idpath.
  -
 apply natlehandplus.
    +
 apply IH.
intro i.
apply le.
    +
 apply le.
Defined.

Lemma transport_stn {m n : nat} (e: m=n) (i: ⟦m⟧ ) :
  transportf stn e i = make_stn n (pr1 i) (transportf (λ k, pr1 i < k) e (pr2 i)).
Proof.
  intros.
  induction e.
  apply subtypePath_prop.
  apply idpath.
Defined.

Lemma stnsum_left_right (m n : nat) (f: ⟦m+n⟧ -> nat) :
  stnsum f = stnsum (f ∘ stn_left m n) + stnsum (f ∘ stn_right m n).
Proof.

  intros.
induction n as [|n IHn].
  {
 change (stnsum _) with 0 at 3.
rewrite natplusr0.
    assert (e := ! natplusr0 m).
    rewrite (transport_stnsum e).
apply stnsum_eq; intro i.
simpl.
    apply maponpaths.
apply pathsinv0.
apply stn_left_0.
}
  rewrite stnsum_step.
assert (e : S (m+n) = m + S n).
  {
 apply pathsinv0.
apply natplusnsm.
}
  rewrite (transport_stnsum e).
  rewrite stnsum_step.
rewrite <- natplusassoc.
apply map_on_two_paths.
  {
 rewrite IHn; clear IHn.
apply map_on_two_paths.
    {
 apply stnsum_eq; intro i.
simpl.
      apply maponpaths.
apply subtypePath_prop.
      rewrite stn_left_compute.
induction e.
      rewrite idpath_transportf.
rewrite dni_last.
      apply idpath.
}
    {
 apply stnsum_eq; intro i.
simpl.
      apply maponpaths.
apply subtypePath_prop.
      rewrite stn_right_compute.
unfold stntonat.
induction e.
      rewrite idpath_transportf.
rewrite 2? dni_last.
apply idpath.
}
 }
  simpl.
apply maponpaths.
apply subtypePath_prop.
  induction e.
apply idpath.
Defined.

Corollary stnsum_left_le (m n : nat) (f: ⟦m+n⟧ -> nat) :
  stnsum (f ∘ stn_left m n) ≤ stnsum f.
Proof.
  intros.
  rewrite stnsum_left_right.
  apply natlehnplusnm.
Defined.

Corollary stnsum_left_le' {m n : nat} (f: ⟦n⟧ -> nat) (r:m≤n) :
  stnsum (f ∘ stn_left' m n r) ≤ stnsum f.
Proof.
  intros.
  assert (s := minusplusnmm n m r).
rewrite (natpluscomm (n-m) m) in s.
  generalize r f; clear r f.
  rewrite <- s; clear s.
  set (k := n-m).
  generalize k; clear k; intros k r f.
  induction (natpluscomm m k).
  rewrite stn_left_compare.
  rewrite stnsum_left_right.
  apply natlehnplusnm.
Defined.

Lemma stnsum_dni {n : nat} (f: ⟦S n⟧ -> nat) (j: ⟦S n⟧ ) :
  stnsum f = stnsum (f ∘ dni j) + f j.
Proof.
  intros.
  induction j as [j J].
  assert (e2 : j + (n - j) = n).
  {
 rewrite natpluscomm.
apply minusplusnmm.
apply natlthsntoleh.
exact J.
}
  assert (e : (S j) + (n - j) = S n).
  {
 change (S j + (n - j)) with (S (j + (n - j))).
apply maponpaths.
exact e2.
}
  intermediate_path (stnsum (λ i, f (transportf stn e i))).
  -
 apply (transport_stnsum e).
  -
 rewrite (stnsum_left_right (S j) (n - j)); unfold funcomp.
    apply pathsinv0.
rewrite (transport_stnsum e2).
    rewrite (stnsum_left_right j (n-j)); unfold funcomp.
    rewrite (stnsum_step (λ x, f (transportf stn e _))); unfold funcomp.
    apply pathsinv0.
    rewrite natplusassoc.
rewrite (natpluscomm (f _)).
rewrite <- natplusassoc.
    apply map_on_two_paths.
    +
 apply map_on_two_paths.
      *
 apply stnsum_eq; intro i.
induction i as [i I].
        apply maponpaths.
apply subtypePath_prop.
        induction e.
rewrite idpath_transportf.
rewrite stn_left_compute.
        unfold dni,di, stntonat; simpl.
        induction (natlthorgeh i j) as [R|R].
        --
 unfold stntonat; simpl; rewrite transport_stn; simpl.
           induction (natlthorgeh i j) as [a|b].
           ++
 apply idpath.
           ++
 contradicts R (natlehneggth b).
        --
 unfold stntonat; simpl; rewrite transport_stn; simpl.
           induction (natlthorgeh i j) as [V|V].
           ++
 contradicts I (natlehneggth R).
           ++
 apply idpath.
      *
 apply stnsum_eq; intro i.
induction i as [i I].
apply maponpaths.
        unfold dni,di, stn_right, stntonat; repeat rewrite transport_stn; simpl.
        induction (natlthorgeh (j+i) j) as [X|X].
        --
 contradicts (negnatlthplusnmn j i) X.
        --
 apply subtypePath_prop.
simpl.
apply idpath.
    +
 apply maponpaths.
      rewrite transport_stn; simpl.
      apply subtypePath_prop.
      apply idpath.
Defined.

Lemma stnsum_pos {n : nat} (f: ⟦n⟧ -> nat) (j: ⟦n⟧ ) : f j ≤ stnsum f.
Proof.
  assert (m : 0 < n).
  {
 apply (natlehlthtrans _ j).
    -
 apply natleh0n.
    -
 exact (pr2 j).
}
  assert (l : 1 ≤ n).
{
 apply natlthtolehsn.
assumption.
}
  assert (e : n = S (n - 1)).
  {
 change (S (n - 1)) with (1 + (n - 1)).
rewrite natpluscomm.
    apply pathsinv0.
apply minusplusnmm.
assumption.
}
  rewrite (transport_stnsum (!e) f).
  rewrite (stnsum_dni _ (transportf stn e j)).
  unfold funcomp.
  generalize (stnsum (λ x, f (transportf stn (! e) (dni (transportf stn e j) x)))); intro s.
  induction e.
apply natlehmplusnm.
Defined.

Corollary stnsum_pos_0 {n : nat} (f: ⟦S n⟧ -> nat) : f firstelement ≤ stnsum f.
Proof.
  intros.
  exact (stnsum_pos f firstelement).
Defined.

Lemma stnsum_1 (n : nat) : stnsum(λ i: ⟦n⟧, 1) = n.
Proof.
  intros.
  induction n as [|n IH].
  {
 apply idpath.
}
  simpl.
  use (natpluscomm _ _ @ _).
  apply maponpaths.
  exact IH.
Defined.

Lemma stnsum_const {m c : nat} : stnsum (λ i: ⟦m⟧, c) = m*c.
Proof.
  intros.
  induction m as [|m I].
  -
 apply idpath.
  -
 exact (maponpaths (λ i, i+c) I).
Defined.

Lemma stnsum_last_le {n : nat} (f: ⟦S n⟧ -> nat) : f lastelement ≤ stnsum f.
Proof.
  intros.
rewrite stnsum_step.
apply natlehmplusnm.
Defined.

Lemma stnsum_first_le {n : nat} (f: ⟦S n⟧ -> nat) : f firstelement ≤ stnsum f.
Proof.
  intros.
induction n as [|n IH].
  -
 apply isreflnatleh.
  -
 rewrite stnsum_step.
assert (W := IH (f ∘ dni lastelement)).
    change ((f ∘ dni lastelement) firstelement) with (f firstelement) in W.
    apply (istransnatleh W); clear W.
apply natlehnplusnm.
Defined.

Lemma _c_ {n : nat} {m: ⟦ n ⟧ → nat} (ij : ∑ i : ⟦ n ⟧, ⟦ m i ⟧) :
  stnsum (m ∘ stn_left'' (stnlt (pr1 ij))) + pr2 ij < stnsum m.
Proof.
  intros.
  set (m1 := m ∘ stn_left'' (stnlt (pr1 ij))).
  induction ij as [i j].
  induction i as [i I].
  induction j as [j J].
  simpl in m1.
  change (stnsum m1 + j < stnsum m).
  assert (s := stnsum_left_le' m (I : S i ≤ n)).
  use (natlthlehtrans _ _ _ _ s).
  clear s.
  induction n as [|n _].
  -
 induction (negnatlthn0 _ I).
  -
 assert (t : stnsum m1 + j < stnsum m1 + m (i,,I)).
    {
 apply natlthandplusl.
exact J.
}
    apply (natlthlehtrans _ _ _ t).
    assert (K : ∏ m n, m = n -> m ≤ n).
    {
 intros a b e.
induction e.
apply isreflnatleh.
}
    apply K; clear K.
    rewrite stnsum_step.
    clear j J t.
    unfold m1 ; clear m1.
    apply two_arg_paths.
    +
 apply stnsum_eq.
intro l.
      simpl.
apply maponpaths.
      apply subtypePath_prop; simpl.
      apply pathsinv0, di_eq1, stnlt.
    +
 simpl.
apply maponpaths.
apply subtypePath_prop.
      simpl.
apply idpath.
Defined.

Local Definition weqstnsum_map { n : nat } (m : ⟦n⟧ -> nat) :
  (∑ i, ⟦m i⟧) -> ⟦stnsum m⟧.
Proof.
  intros ij.
  exact (make_stn _ (stnsum (m ∘ stn_left'' (stnlt (pr1 ij))) + pr2 ij) (_c_ ij)).
Defined.

Local Definition weqstnsum_invmap {n : nat} (m : ⟦n⟧ -> nat) :
  ⟦stnsum m⟧ -> (∑ i, ⟦m i⟧).
Proof.
  revert m.
  induction n as [|n IH].
  {
 intros ? l.
apply fromempty, negstn0.
assumption.
}
  intros ? l.
  change (⟦ stnsum (m ∘ dni lastelement) + m lastelement ⟧) in l.

  assert (ls := weqfromcoprodofstn_invmap _ _ l).
  induction ls as [j|k].
  -
 exact (total2_base_map (dni lastelement) (IH _ j)).
  -
 exact (lastelement,,k).
Defined.

Definition weqstnsum_invmap_step1 {n : nat} (f : ⟦S n⟧ -> nat)
  (j : stn (stnsum (λ x, f (dni lastelement x)))) :
  weqstnsum_invmap f
    (weqfromcoprodofstn_map (stnsum (λ x, f (dni lastelement x)))
                            (f lastelement) (ii1 j))
  = total2_base_map (dni lastelement) (weqstnsum_invmap (f ∘ dni lastelement) j).
Proof.
  intros.
unfold weqstnsum_invmap at 1.
unfold nat_rect at 1.
  rewrite weqfromcoprodofstn_eq1.
apply idpath.
Defined.

Definition weqstnsum_invmap_step2 {n : nat} (f : ⟦S n⟧ -> nat)
  (k : ⟦f lastelement⟧) :
  weqstnsum_invmap f
    (weqfromcoprodofstn_map (stnsum (λ x, f (dni lastelement x)))
                            (f lastelement) (ii2 k))
  = (lastelement,,k).
Proof.
  intros.
unfold weqstnsum_invmap at 1.
unfold nat_rect at 1.
  rewrite weqfromcoprodofstn_eq1.
apply idpath.
Defined.

Lemma partial_sum_prop_aux {n : nat} {m : ⟦n⟧ → nat} :
  ∏ (i i' : ⟦ n ⟧) (j : ⟦ m i ⟧) (j' : ⟦ m i' ⟧),
  i < i' → stnsum (m ∘ stn_left'' (stnlt i)) + j <
           stnsum (m ∘ stn_left'' (stnlt i')) + j'.
Proof.
  intros ? ? ? ? lt.
  apply natlthtolehsn in lt.
  pose (ltS := (natlehlthtrans _ _ _ lt (stnlt i'))).
  refine (natlthlehtrans _ _ _ _ (natlehnplusnm _ _)).
  apply natlthlehtrans with (stnsum (m ∘ stn_left'' ltS)).
  -
 rewrite stnsum_step.
    assert (stnsum (m ∘ stn_left'' (stnlt i)) =
            stnsum (m ∘ stn_left'' ltS ∘ dni lastelement)) as e.
{
      apply stnsum_eq.
      intros k.
      simpl.
apply maponpaths.
      apply subtypePath_prop.
simpl.
      apply pathsinv0, di_eq1.
      apply (stnlt k).
    }
    induction e.
    apply natlthandplusl.
    assert ((m ∘ stn_left'' ltS) lastelement = m i) as e.
{
      simpl.
apply maponpaths.
      apply subtypePath_prop, idpath.
    }
    induction e.
    apply (stnlt j).
  -
 assert (stnsum (m ∘ stn_left'' ltS) =
            stnsum (m ∘ stn_left'' (stnlt i') ∘ stn_left' _ _ lt)) as e.
{
      apply stnsum_eq.
      intros k.
      simpl.
apply maponpaths.
      apply subtypePath_prop, idpath.
    }
    rewrite e.
    apply stnsum_left_le'.
Defined.

Lemma partial_sum_prop {n : nat} {m : ⟦n⟧ → nat} {l : nat} :
  isaprop (∑ (i : ⟦n⟧ ) (j : ⟦m i⟧ ), stnsum (m ∘ stn_left'' (stnlt i)) + j = l).
Proof.
  intros.
  apply invproofirrelevance.
  intros t t'.
  induction t as [i je].
induction je as [j e].
  induction t' as [i' je'].
induction je' as [j' e'].
  pose (e'' := e @ !e').
  assert (i = i') as p.
{
    induction (nat_eq_or_neq i i') as [eq | ne].
    +
 apply subtypePath_prop.
assumption.
    +
 apply fromempty.
      generalize e''.
      apply nat_neq_to_nopath.
      induction (natneqchoice _ _ ne);
        [apply natgthtoneq | apply natlthtoneq];
        apply partial_sum_prop_aux;
        assumption.
  }
  apply total2_paths_f with p.
  -
 use total2_paths_f.
    +
 induction p.
simpl.
      apply subtypePath_prop.
      apply (natpluslcan _ _ _ e'').
    +
 apply isasetnat.
Defined.

Lemma partial_sum_slot {n : nat} {m : ⟦n⟧ → nat} {l : nat} : l < stnsum m ->
  ∃! (i : ⟦n⟧ ) (j : ⟦m i⟧ ), stnsum (m ∘ stn_left'' (stnlt i)) + j = l.
Proof.
  intros lt.
  set (len := stnsum m).
  induction n as [|n IH].
  {
 apply fromempty.
change (hProptoType(l < 0)) in lt.
exact (negnatlthn0 _ lt).
}
  set (m' := m ∘ dni_lastelement).
  set (len' := stnsum m').
  induction (natlthorgeh l len') as [I|J].
  -
 assert (IH' := IH m' I); clear IH.
    induction IH' as [ijJ Q].
induction ijJ as [i jJ].
induction jJ as [j J].
    use tpair.
    +
 exists (dni_lastelement i).
exists j.
admit.
    +
 intro t.
      apply partial_sum_prop.
  -
 clear IH.
set (j := l - len').
    apply iscontraprop1.
    {
 apply partial_sum_prop.
}
    assert (K := minusplusnmm _ _ J).
change (l-len') with j in K.
    exists lastelement.
    use tpair.
    *
 exists j.
apply (natlthandpluslinv _ _ len').
rewrite natpluscomm.
      induction (!K); clear K J j.
      assert(C : len = len' + m lastelement).
      {
 use (stnsum_step _ @ _).
unfold len', m'; clear m' len'.
        rewrite replace_dni_last.
apply idpath.
}
      induction C.
exact lt.
    *
 simpl.
intermediate_path (stnsum m' + j).
      --
 apply (maponpaths (λ x, x+j)).
apply stnsum_eq; intro i.
         unfold m'.
simpl.
apply maponpaths.
         apply subtypePath_prop, idpath.
      --
 rewrite natpluscomm.
exact K.
Defined.

Lemma stn_right_first (n i : nat) :
  stn_right i (S n) firstelement = make_stn (i + S n) i (natltplusS n i).
Proof.
  intros.
  apply subtypePath_prop.
  simpl.
  apply natplusr0.
Defined.

Lemma nat_rect_step (P : nat → UU) (p0 : P 0) (IH : ∏ n, P n → P (S n)) n :
  nat_rect P p0 IH (S n) = IH n (nat_rect P p0 IH n).
Proof.
  intros.
  apply idpath.
Defined.

Definition weqstnsum1_prelim {n : nat} (f : ⟦n⟧ -> nat) :
  (∑ i, ⟦f i⟧) ≃ ⟦stnsum f⟧.
Proof.
  revert f.
  induction n as [ | n' IHn ].
  {
 intros f.
apply weqempty.
    -
 exact (negstn0 ∘ pr1).
    -
 exact negstn0.
}
  intros f.
  change (⟦stnsum f⟧) with (⟦stnsum (f ∘ dni lastelement) + f lastelement⟧).
  use (weqcomp _ (weqfromcoprodofstn _ _)).
  use (weqcomp (weqoverdnicoprod _) _).
  apply weqcoprodf1.
  apply IHn.
Defined.

Lemma weqstnsum1_step {n : nat} (f : ⟦S n⟧ -> nat)
  : (
      weqstnsum1_prelim f
      =
      weqfromcoprodofstn (stnsum (funcomp (dni lastelement) f)) (f lastelement)
      ∘ (weqcoprodf1 (weqstnsum1_prelim (λ i, f (dni lastelement i)))
         ∘ weqoverdnicoprod (λ i, ⟦ f i ⟧))) % weq.
Proof.
  intros.
  apply idpath.
Defined.

Lemma weqstnsum1_prelim_eq { n : nat } (f : ⟦n⟧ -> nat) :
  weqstnsum1_prelim f ~ weqstnsum_map f.
Proof.
  revert f.
  induction n as [|n I].
  -
 intros f ij.
apply fromempty, negstn0.
exact (pr1 ij).
  -
 intros f.
    rewrite weqstnsum1_step.
    intros ij.
    rewrite 2 weqcomp_to_funcomp_app.
    unfold weqcoprodf1.
    change (pr1weq (weqcoprodf (weqstnsum1_prelim (λ i, f (dni lastelement i)))
                               (idweq (⟦ f lastelement ⟧))))
    with (coprodf (weqstnsum1_prelim (λ i, f (dni lastelement i)))
                  (idfun (⟦ f lastelement ⟧))).
    intermediate_path
      ((weqfromcoprodofstn (stnsum (f ∘ dni lastelement)) (f lastelement))
         (coprodf (weqstnsum_map (λ i, f (dni lastelement i)))
                  (idfun (⟦ f lastelement ⟧)) ((weqoverdnicoprod (λ i, ⟦ f i ⟧)) ij))).
    +
 apply maponpaths.
      apply homotcoprodfhomot.
      *
 apply I.
      *
 intro x.
apply idpath.
    +
 clear I.
      apply pathsinv0.
      generalize ij ; clear ij.
      apply (homotweqinv' (weqstnsum_map f)
                          (weqoverdnicoprod (λ i : ⟦ S n ⟧, ⟦ f i ⟧))
                          (λ c, pr1weq (weqfromcoprodofstn (stnsum (f ∘ dni lastelement)) (f lastelement))
                                       (coprodf (weqstnsum_map (λ i, f (dni lastelement i)))
                                                (idfun _) c))
            ).
      intros c.
      simpl.
      set (P := λ i, ⟦ f i ⟧).
      change (pr1weq (weqfromcoprodofstn (stnsum (λ x : ⟦ n ⟧, f (dni lastelement x))) (f lastelement)))
      with (weqfromcoprodofstn_map (stnsum (λ x : ⟦ n ⟧, f (dni lastelement x))) (f lastelement)).
      induction c as [jk|k].
      *
 unfold coprodf.
        induction jk as [j k].
        change (invmap (weqoverdnicoprod P) (ii1 (j,,k))) with (tpair P (dni lastelement j) k).
        unfold weqfromcoprodofstn_map.
unfold coprod_rect.
unfold weqstnsum_map.
        apply subtypePath_prop.
        induction k as [k K].
simpl.
        apply (maponpaths (λ x, x+k)).
unfold funcomp, stntonat, di.
        clear K k.
        induction (natlthorgeh _ n) as [G|G'].
        --
 simpl.
apply stnsum_eq; intro k.
apply maponpaths.
           apply subtypePath_prop.
simpl.
           apply pathsinv0, di_eq1.
           exact (istransnatlth _ _ _ (stnlt k) G).
        --
 apply fromempty.
exact (natlthtonegnatgeh _ _ (stnlt j) G').
      *
 change (invmap (weqoverdnicoprod P) (ii2 k)) with (tpair P lastelement k).
        simpl.
        unfold weqstnsum_map.
        apply subtypePath_prop.
        induction k as [k K].
simpl.
        apply (maponpaths (λ x, x+k)).
        apply maponpaths.
        apply funextfun; intro i.
induction i as [i I].
        simpl.
apply maponpaths.
        apply subtypePath_prop.
        simpl.
        apply pathsinv0, di_eq1.
assumption.
Defined.

Lemma weqstnsum1_prelim_eq' { n : nat } (f : ⟦n⟧ -> nat) :
  invweq (weqstnsum1_prelim f) ~ weqstnsum_invmap f.
Proof.
  revert f.
  induction n as [|n I].
  -
 intros f k.
apply fromempty, negstn0.
exact k.
  -
 intros f.
rewrite weqstnsum1_step.
    intros k.
rewrite 2 invweqcomp.
rewrite 2 weqcomp_to_funcomp_app.
rewrite 3 pr1_invweq.
    unfold weqcoprodf1.
    change (invmap (weqcoprodf (weqstnsum1_prelim (λ i, f (dni lastelement i))) (idweq (⟦ f lastelement ⟧))))
    with (coprodf (invweq (weqstnsum1_prelim (λ i, f (dni lastelement i)))) (idweq (⟦ f lastelement ⟧))).
    intermediate_path (invmap (weqoverdnicoprod (λ i : ⟦ S n ⟧, ⟦ f i ⟧))
                              (coprodf (weqstnsum_invmap (λ i : ⟦ n ⟧, f (dni lastelement i))) (idweq (⟦ f lastelement ⟧))
                                       (invmap (weqfromcoprodofstn (stnsum (f ∘ dni lastelement)) (f lastelement)) k))).
    +
 apply maponpaths.
      change (invmap _ k)
      with (invmap (weqfromcoprodofstn (stnsum (f ∘ dni lastelement)) (f lastelement)) k).
      generalize (invmap (weqfromcoprodofstn (stnsum (f ∘ dni lastelement)) (f lastelement)) k).
      intro c.
      apply homotcoprodfhomot.
      *
 apply I.
      *
 apply homotrefl.
    +
 clear I.
      generalize k; clear k.
      use (homotweqinv
                (λ c, invmap (weqoverdnicoprod (λ i, ⟦ f i ⟧))
                             (coprodf (weqstnsum_invmap (λ i, f (dni lastelement i)))
                                      (idweq (⟦ f lastelement ⟧))
                                      c))
                (weqfromcoprodofstn (stnsum (f ∘ dni lastelement)) (f lastelement))
                ).
      unfold funcomp.
      intro c.
      induction c as [r|s].
      *
 unfold coprodf.
        change (pr1weq (weqfromcoprodofstn (stnsum (λ x, f (dni lastelement x))) (f lastelement)))
        with (weqfromcoprodofstn_map (stnsum (λ x, f (dni lastelement x))) (f lastelement)).
        set (P := (λ i : ⟦ S n ⟧, ⟦ f i ⟧)).
        rewrite weqstnsum_invmap_step1.
        change (λ i : ⟦ n ⟧, f (dni lastelement i)) with (f ∘ dni lastelement).
        generalize (weqstnsum_invmap (f ∘ dni lastelement) r); intro ij.
        induction ij as [i j].
        apply idpath.
      *
 unfold coprodf.
        change (pr1weq (idweq _) s) with s.
        set (P := (λ i : ⟦ S n ⟧, ⟦ f i ⟧)).
        change (pr1weq _)
        with (weqfromcoprodofstn_map (stnsum (λ x : ⟦ n ⟧, f (dni lastelement x))) (f lastelement)).
        rewrite weqstnsum_invmap_step2.
        apply idpath.
Defined.

Definition weqstnsum1 {n : nat} (f : ⟦n⟧ -> nat) : (∑ i, ⟦f i⟧) ≃ ⟦stnsum f⟧.
Proof.
  intros.
use (remakeweqboth (weqstnsum1_prelim_eq _) (weqstnsum1_prelim_eq' _)).
Defined.

Lemma weqstnsum1_eq {n : nat} (f : ⟦n⟧ -> nat) : pr1weq (weqstnsum1 f) = weqstnsum_map f.
Proof.
  intros.
  apply idpath.
Defined.

Theorem weqstnsum { n : nat } (P : ⟦n⟧ -> UU) (f : ⟦n⟧ -> nat) :
  (∏ i, ⟦f i⟧ ≃ P i) -> total2 P ≃ ⟦stnsum f⟧.
Proof.
  intros w.
  intermediate_weq (∑ i, ⟦f i⟧).
  -
 apply invweq.
apply weqfibtototal.
assumption.
  -
 apply weqstnsum1.
Defined.

Corollary weqstnsum2 { X : UU } {n : nat} (f : ⟦n⟧ -> nat) (g : X -> ⟦n⟧ ) :
  (∏ i, ⟦f i⟧ ≃ hfiber g i) -> X ≃ ⟦stnsum f⟧.
Proof.
  intros w.
  use (weqcomp _ (weqstnsum _ _ w)).
  apply weqtococonusf.
Defined.

Definition lexicalEnumeration {n : nat} (m: ⟦n⟧ -> nat) :
  ⟦stnsum m⟧ ≃ (∑ i : ⟦n⟧, ⟦m i⟧) := invweq (weqstnsum1 m).

Definition inverse_lexicalEnumeration {n : nat} (m: ⟦n⟧ -> nat) :
  (∑ i : ⟦n⟧, ⟦m i⟧) ≃ ⟦stnsum m⟧ := weqstnsum1 m.

Definition foldleft {E} (e : E) (m : binop E) {n : nat} (x: ⟦n⟧ -> E) : E.
Proof.
  intros.
  induction n as [|n foldleft].
  +
 exact e.
  +
 exact (m (foldleft (x ∘ (dni lastelement))) (x lastelement)).
Defined.

Definition foldright {E} (m : binop E) (e : E) {n : nat} (x: ⟦n⟧ -> E) : E.
Proof.
  intros.
  induction n as [|n foldright].
  +
 exact e.
  +
 exact (m (x firstelement) (foldright (x ∘ dni firstelement))).
Defined.

Theorem weqfromprodofstn ( n m : nat ) : ⟦n⟧ × ⟦m⟧ ≃ ⟦n*m⟧.
Proof.
  intros.
  induction ( natgthorleh m 0 ) as [ is | i ].
  -
 assert ( i1 : ∏ i j : nat, i < n -> j < m -> j + i * m < n * m).
    +
 intros i j li lj.
      apply (natlthlehtrans ( j + i * m ) ( ( S i ) * m ) ( n * m )).
      *
 change (S i * m) with (i*m + m).
        rewrite natpluscomm.
        exact (natgthandplusl m j ( i * m ) lj ).
      *
 exact ( natlehandmultr ( S i ) n m ( natgthtogehsn _ _ li ) ).
    +
 set ( f := λ ij : ⟦n⟧ × ⟦m⟧,
                   match ij
                   with tpair _ i j =>
                        make_stn ( n * m ) ( j + i * m ) ( i1 i j ( pr2 i ) ( pr2 j ) )
                   end ).
      split with f.
      assert ( isinf : isincl f ).
      *
 apply isinclbetweensets.
        apply ( isofhleveldirprod 2 _ _ ( isasetstn n ) ( isasetstn m ) ).
        apply ( isasetstn ( n * m ) ).
        intros ij ij' e.
 destruct ij as [ i j ].
destruct ij' as [ i' j' ].
        destruct i as [ i li ].
destruct i' as [ i' li' ].
        destruct j as [ j lj ].
destruct j' as [ j' lj' ].
        simpl in e.
        assert ( e' := maponpaths ( stntonat ( n * m ) ) e ).
simpl in e'.
        assert ( eei : i = i' ).
        {
 apply ( pr1 ( natdivremunique m i j i' j' lj lj' ( maponpaths ( stntonat _ ) e ) ) ).
}
        set ( eeis := invmaponpathsincl _ ( isinclstntonat _ ) ( make_stn _ i li ) ( make_stn _ i' li' ) eei ).
        assert ( eej : j = j' ).
        {
 apply ( pr2 ( natdivremunique m i j i' j' lj lj' ( maponpaths ( stntonat _ ) e ) ) ).
}
        set ( eejs := invmaponpathsincl _ ( isinclstntonat _ ) ( make_stn _ j lj ) ( make_stn _ j' lj' ) eej ).
        apply ( pathsdirprod eeis eejs ).
      *
 intro xnm.
        apply iscontraprop1.
apply ( isinf xnm ).
        set ( e := pathsinv0 ( natdivremrule xnm m ( natgthtoneq _ _ is ) ) ).
        set ( i := natdiv xnm m ).
  set ( j := natrem xnm m ).
        destruct xnm as [ xnm lxnm ].
        set ( li := natlthandmultrinv _ _ _ ( natlehlthtrans _ _ _ ( natlehmultnatdiv xnm m ( natgthtoneq _ _ is ) ) lxnm ) ).
        set ( lj := lthnatrem xnm m ( natgthtoneq _ _ is ) ).
        split with ( make_dirprod ( make_stn n i li ) ( make_stn m j lj ) ).
        simpl.
        apply ( invmaponpathsincl _ ( isinclstntonat _ ) _ _ ).
 simpl.
        apply e.
  -
 set ( e := natleh0tois0 i ).
 rewrite e.
 rewrite ( natmultn0 n ).
split with ( @pr2 _ _ ).
  apply ( isweqtoempty2 _ ( weqstn0toempty ) ).
Defined.

Theorem weqfromdecsubsetofstn { n : nat } ( f : ⟦n⟧ -> bool ) :
  total2 ( λ x : nat, hfiber f true ≃ (⟦x⟧) ).
Proof.
  revert f.
  induction n as [ | n IHn ].
  -
 intros.
    split with 0.
    assert ( g : hfiber f true -> (⟦0⟧) ).
    {
 intro hf.
      destruct hf as [ i e ].
      destruct ( weqstn0toempty i ).
    }
    apply ( weqtoempty2 g weqstn0toempty ).
  -
 intro.
    set ( g := weqfromcoprodofstn 1 n ).
    change ( 1 + n ) with ( S n ) in g.
    set ( fl := λ i : ⟦1⟧, f ( g ( ii1 i ) ) ).
    set ( fh := λ i : ⟦n⟧, f ( g ( ii2 i ) ) ).
    assert ( w : ( hfiber f true ) ≃ ( hfiber ( sumofmaps fl fh ) true ) ).
    {
 set ( int := invweq ( weqhfibersgwtog g f true  ) ).
      assert ( h : ∏ x : _ , paths ( f ( g x ) ) ( sumofmaps fl fh x ) ).
      {
 intro.
        destruct x as [ x1 | xn ].
        +
 apply idpath.
        +
 apply idpath.
      }
      apply ( weqcomp int ( weqhfibershomot _ _ h true ) ).
    }
    set ( w' := weqcomp w ( invweq ( weqhfibersofsumofmaps fl fh true ) ) ).
    set ( x0 := pr1 ( IHn fh ) ).
    set ( w0 := pr2 ( IHn fh ) ).
    simpl in w0.
    destruct ( boolchoice ( fl lastelement ) ) as [ i | ni ].
    +
 split with ( S x0 ).
      assert ( wi : hfiber fl true ≃ ⟦1⟧ ).
      {
 assert ( is : iscontr ( hfiber fl true ) ).
        {
 apply iscontraprop1.
          *
 apply ( isinclfromstn1 fl isasetbool true ).
          *
 apply ( make_hfiber _ lastelement i ).
        }
        apply ( weqcontrcontr is iscontrstn1 ).
      }
      apply ( weqcomp ( weqcomp w' ( weqcoprodf wi w0 ) ) ( weqfromcoprodofstn 1 _ ) ).
    +
 split with x0.
      assert ( g' : ¬ ( hfiber fl true ) ).
      {
 intro hf.
        destruct hf as [ j e ].
        assert ( ee : j = lastelement ).
        {
 apply proofirrelevancecontr, iscontrstn1.
}
        destruct ( nopathstruetofalse ( pathscomp0 ( pathscomp0 ( pathsinv0 e ) ( maponpaths fl ee ) ) ni ) ).
      }
      apply ( weqcomp w' ( weqcomp ( invweq ( weqii2withneg _ g' ) ) w0 )  ).
Defined.

Theorem weqfromhfiberfromstn { n : nat } { X : UU } ( x : X )
  ( is : isisolated X x ) ( f : ⟦n⟧ -> X ) :
  total2 ( λ x0 : nat, hfiber f x  ≃ (⟦x0⟧) ).
Proof.
  intros.
  set ( t := weqfromdecsubsetofstn ( λ i : _, eqbx X x is ( f i ) ) ).
  split with ( pr1 t ).
  apply ( weqcomp ( weqhfibertobhfiber f x is ) ( pr2 t ) ).
Defined.

Theorem weqfromfunstntostn ( n m : nat ) : (⟦n⟧ -> ⟦m⟧) ≃ ⟦natpower m n⟧.
Proof.
  revert m.
  induction n as [ | n IHn ].
  -
 intro m.
    apply weqcontrcontr.
    +
 apply ( iscontrfunfromempty2 _ weqstn0toempty ).
    +
 apply iscontrstn1.
  -
 intro m.
    set ( w1 := weqfromcoprodofstn 1 n ).
    assert ( w2 : ( ⟦S n⟧ -> ⟦m⟧ ) ≃ ( (⟦1⟧ ⨿ ⟦n⟧) -> ⟦m⟧ ) ) by apply ( weqbfun _ w1  ).
    set ( w3 := weqcomp w2 ( weqfunfromcoprodtoprod (⟦1⟧) (⟦n⟧) (⟦m⟧) ) ).
    set ( w4 := weqcomp w3 ( weqdirprodf ( weqfunfromcontr (⟦m⟧) iscontrstn1 ) ( IHn m ) ) ).
    apply ( weqcomp w4 ( weqfromprodofstn m ( natpower m n ) ) ).
Defined.

Definition stnprod { n : nat } ( f : ⟦n⟧ -> nat ) : nat.
Proof.
  revert f.
  induction n as [ | n IHn ].
  -
 intro.
    apply 1.
  -
 intro f.
    apply (  ( IHn ( λ i : ⟦n⟧, f ( dni lastelement i ) ) ) * f lastelement ).
Defined.

Definition stnprod_step { n : nat } ( f : ⟦S n⟧ -> nat ) :
  stnprod f = stnprod (f ∘ dni lastelement) * f lastelement.
Proof.
  intros.
  apply idpath.
Defined.

Lemma stnprod_eq {n : nat} (f g: ⟦n⟧ -> nat) : f ~ g -> stnprod f = stnprod g.
Proof.
  intros h.
induction n as [|n IH].
  {
 apply idpath.
}
  rewrite 2? stnprod_step.
induction (h lastelement).
  apply (maponpaths (λ i, i * f lastelement)).
apply IH.
intro x.
apply h.
Defined.

Theorem weqstnprod { n : nat } ( P : ⟦n⟧ -> UU ) ( f : ⟦n⟧ -> nat )
  ( ww : ∏ i : ⟦n⟧ , ( stn ( f i ) ) ≃ ( P i ) ) :
  ( ∏ x : ⟦n⟧ , P x  ) ≃ stn ( stnprod f ).
Proof.
  revert P f ww.
  induction n as [ | n IHn ].
  -
 intros.
simpl.
apply ( weqcontrcontr ).
    +
 apply ( iscontrsecoverempty2 _ ( negstn0 ) ).
    +
 apply iscontrstn1.
  -
 intros.
    set ( w1 := weqdnicoprod n lastelement ).
    assert ( w2 := weqonsecbase P w1 ).
    assert ( w3 := weqsecovercoprodtoprod ( λ x : _, P ( w1 x ) ) ).
    assert ( w4 := weqcomp w2 w3 ) ; clear w2 w3.
    assert ( w5 := IHn ( λ x : ⟦n⟧, P ( w1 ( ii1 x ) ) ) ( λ x : ⟦n⟧, f ( w1 ( ii1 x ) ) ) ( λ i : ⟦n⟧, ww ( w1 ( ii1 i ) ) ) ).
    assert ( w6 := weqcomp w4 ( weqdirprodf w5 ( weqsecoverunit _ ) ) ) ; clear w4 w5.
    simpl in w6.
    assert ( w7 := weqcomp w6 ( weqdirprodf ( idweq _ ) ( invweq ( ww lastelement ) ) ) ).
    refine ( _ ∘ w7 )%weq.
    unfold w1.
    exact (weqfromprodofstn _ _ ).
Defined.

Theorem weqweqstnsn ( n : nat ) : (⟦S n⟧ ≃ ⟦S n⟧)  ≃  ⟦S n⟧ × ( ⟦n⟧ ≃ ⟦n⟧ ).
Proof.
  assert ( l := @lastelement n ).
  intermediate_weq ( isolated (⟦S n⟧) × (compl _ l ≃ compl _ l) ).
  {
 apply weqcutonweq.
intro i.
apply isdeceqstn.
}
  apply weqdirprodf.
  -
 apply weqisolatedstntostn.
  -
 apply weqweq.
apply invweq.
    intermediate_weq (compl_ne (⟦S n⟧) l (stnneq l)).
    +
 apply weqdnicompl.
    +
 apply compl_weq_compl_ne.
Defined.

Theorem weqfromweqstntostn ( n : nat ) : ( (⟦n⟧) ≃ (⟦n⟧) ) ≃ ⟦factorial n⟧.
Proof.
  induction n as [ | n IHn ].
  -
 simpl.
    apply ( weqcontrcontr ).
    +
 apply ( iscontraprop1 ).
      *
 apply ( isapropweqtoempty2 _ ( negstn0 ) ).
      *
 apply idweq.
    +
 apply iscontrstn1.
  -
 change ( factorial ( S n ) ) with ( ( S n ) * ( factorial n ) ).
    set ( w1 := weqweqstnsn n ).
    apply ( weqcomp w1 ( weqcomp ( weqdirprodf ( idweq _ ) IHn ) ( weqfromprodofstn _ _ ) ) ).
Defined.

Theorem ischoicebasestn ( n : nat ) : ischoicebase (⟦n⟧).
Proof.
  induction n as [ | n IHn ].
  -
 apply ( ischoicebaseempty2 negstn0 ).
  -
 apply ( ischoicebaseweqf ( weqdnicoprod n lastelement )
                             ( ischoicebasecoprod IHn ischoicebaseunit ) ).
Defined.

Lemma negweqstnsn0 (n : nat) : ¬ (⟦S n⟧ ≃ stn O).
Proof.
  unfold neg.
  assert (lp: ⟦S n⟧) by apply lastelement.
  intro X.
  apply weqstn0toempty.
  apply (pr1 X lp).
Defined.

Lemma negweqstn0sn (n : nat) : ¬ (stn O ≃ ⟦S n⟧).
Proof.
  unfold neg.
  assert (lp: ⟦S n⟧) by apply lastelement.
  intro X.
  apply weqstn0toempty.
  apply (pr1 ( invweq X ) lp).
Defined.

Lemma weqcutforstn ( n n' : nat ) : ⟦S n⟧ ≃ ⟦S n'⟧ -> ⟦n⟧ ≃ ⟦n'⟧.
Proof.
  intros w.
assert ( k := @lastelement n  ).
  intermediate_weq (stn_compl k).
  -
 apply weqdnicompl.
  -
 intermediate_weq (stn_compl (w k)).
    +
 apply weqoncompl_ne.
    +
 apply invweq, weqdnicompl.
Defined.

Theorem weqtoeqstn { n n' : nat } : ⟦n⟧ ≃ ⟦n'⟧ -> n = n'.
Proof.
revert n'.
       induction n as [ | n IHn ].
       -
 intro.
destruct n' as [ | n' ].
         +
 intros; apply idpath.
         +
 intro X.
apply (fromempty (negweqstn0sn _ X)).
       -
 intro n'.
destruct n' as [ | n' ].
         +
 intro X.
apply (fromempty ( negweqstnsn0 n X)).
         +
 intro X.
apply maponpaths.
apply IHn.
           apply weqcutforstn.
assumption.
Defined.

Corollary stnsdnegweqtoeq ( n n' : nat ) ( dw : dneg (⟦n⟧ ≃ ⟦n'⟧) ) : n = n'.
Proof.
  apply (eqfromdnegeq nat isdeceqnat _ _  (dnegf (@weqtoeqstn n n') dw)).
Defined.

Lemma weqforallnatlehn0 ( F : nat -> hProp ) :
  ( ∏ n : nat , natleh n 0 -> F n ) ≃ ( F 0 ).
Proof.
  intros.
  assert ( lg : ( ∏ n : nat , natleh n 0 -> F n ) <-> ( F 0 ) ).
  {
 split.
    -
 intro f.
      apply ( f 0 ( isreflnatleh 0 ) ).
    -
 intros f0 n l.
      set ( e := natleh0tois0 l ).
      rewrite e.
      apply f0.
  }
  assert ( is1 : isaprop ( ∏ n : nat , natleh n 0 -> F n ) ).
  {
 apply impred.
    intro n.
    apply impred.
    intro l.
    apply ( pr2 ( F n ) ).
  }
  apply ( weqimplimpl ( pr1 lg ) ( pr2 lg ) is1 ( pr2 ( F 0 ) ) ).
Defined.

Lemma weqforallnatlehnsn' ( n' : nat ) ( F : nat -> hProp ) :
  ( ∏ n : nat , natleh n ( S n' ) -> F n ) ≃
  ( ∏ n : nat , natleh n n' -> F n ) × ( F ( S n' ) ).
Proof.
  intros.
  assert ( lg : ( ∏ n : nat , natleh n ( S n' ) -> F n ) <->
                ( ∏ n : nat , natleh n n' -> F n ) × ( F ( S n' ) ) ).
  {
 split.
    -
 intro f.
      apply ( make_dirprod ( λ n, λ l, ( f n ( natlehtolehs _ _ l ) ) )
                          ( f ( S n' ) ( isreflnatleh _ ) ) ).
    -
 intro d2.
      intro n.
intro l.
      destruct ( natlehchoice2 _ _ l ) as [ h | e ].
      +
 simpl in h.
        apply ( pr1 d2 n h ).
      +
 destruct d2 as [ f2 d2 ].
        rewrite e.
        apply d2.
  }
  assert ( is1 : isaprop ( ∏ n : nat , natleh n ( S n' ) -> F n ) ).
  {
 apply impred.
    intro n.
    apply impred.
    intro l.
    apply ( pr2 ( F n ) ).
  }
  assert ( is2 : isaprop ( ( ∏ n : nat , natleh n n' -> F n ) × ( F ( S n' ) ) ) ).
  {
 apply isapropdirprod.
    -
 apply impred.
      intro n.
      apply impred.
      intro l.
      apply ( pr2 ( F n ) ).
    -
 apply ( pr2 ( F ( S n' ) ) ).
  }
  apply ( weqimplimpl ( pr1 lg ) ( pr2 lg ) is1 is2 ).
Defined.

Lemma weqexistsnatlehn0 ( P : nat -> hProp  ) :
  ( hexists ( λ n : nat, ( natleh n 0 ) × ( P n ) ) ) ≃ P 0.
Proof.
  assert ( lg : hexists ( λ n : nat, ( natleh n 0 ) × ( P n ) ) <-> P 0  ).
  {
 split.
    -
 simpl.
      apply ( @hinhuniv _ ( P 0 ) ).
      intro t2.
      destruct t2 as [ n d2 ].
      destruct d2 as [ l p ].
      set ( e := natleh0tois0 l ).
      clearbody e.
      destruct e.
      apply p.
    -
 intro p.
      apply hinhpr.
      split with 0.
      split with ( isreflnatleh 0 ).
      apply p.
  }
  apply ( weqimplimpl ( pr1 lg ) ( pr2 lg ) ( pr2 _ ) ( pr2 _ ) ).
Defined.

Lemma weqexistsnatlehnsn' ( n' : nat ) ( P : nat -> hProp  ) :
  ( hexists ( λ n : nat, ( natleh n ( S n' ) ) × ( P n ) ) ) ≃
  hdisj ( hexists ( λ n : nat, ( natleh n n' ) × ( P n ) ) )  ( P ( S n' ) ).
Proof.
  intros.
  assert ( lg : hexists ( λ n : nat, ( natleh n ( S n' ) ) × ( P n ) ) <->
                hdisj ( hexists ( λ n : nat, ( natleh n n' ) × ( P n ) ) )  ( P ( S n' ) ) ).
  {
 split.
    -
 apply hinhfun.
      intro t2.
      destruct t2 as [ n d2 ].
      destruct d2 as [ l p ].
      destruct ( natlehchoice2 _ _ l ) as [ h | nh ].
      +
 simpl in h.
        apply ii1.
        apply hinhpr.
        split with n.
        apply ( make_dirprod h p ).
      +
 destruct nh.
        apply ( ii2 p ).
    -
 simpl.
      apply ( @hinhuniv _ ( ishinh _ ) ).
      intro c.
      destruct c as [ t | p ].
      +
 generalize t.
        simpl.
        apply hinhfun.
        clear t.
        intro t.
        destruct t as [ n d2 ].
        destruct d2 as [ l p ].
        split with n.
        split with ( natlehtolehs _ _ l ).
        apply p.
      +
 apply hinhpr.
        split with ( S n' ).
        split with ( isreflnatleh _ ).
        apply p.
  }
  apply ( weqimplimpl ( pr1 lg ) ( pr2 lg ) ( pr2 _ ) ( pr2 _ ) ).
Defined.

Lemma isdecbexists ( n : nat ) ( P : nat -> UU ) ( is : ∏ n' , isdecprop ( P n' ) ) :
  isdecprop ( hexists ( λ n', ( natleh n' n ) × ( P n' ) ) ).
Proof.
  intros.
  set ( P' := λ n' : nat, make_hProp _ ( is n' ) ).
  induction n as [ | n IHn ].
  -
 apply ( isdecpropweqb ( weqexistsnatlehn0 P' ) ).
    apply ( is 0 ).
  -
 apply ( isdecpropweqb ( weqexistsnatlehnsn' _ P' ) ).
    apply isdecprophdisj.
    +
 apply IHn.
    +
 apply ( is ( S n ) ).
Defined.

Lemma isdecbforall ( n : nat ) ( P : nat -> UU ) ( is : ∏ n' , isdecprop ( P n' ) ) :
  isdecprop ( ∏ n' , natleh n' n -> P n' ).
Proof.
  intros.
  set ( P' := λ n' : nat, make_hProp _ ( is n' ) ).
  induction n as [ | n IHn ].
  -
 apply ( isdecpropweqb ( weqforallnatlehn0 P' ) ).
    apply ( is 0 ).
  -
 apply ( isdecpropweqb ( weqforallnatlehnsn' _ P' ) ).
    apply isdecpropdirprod.
    +
 apply IHn.
    +
 apply ( is ( S n ) ).
Defined.

Lemma negbforalldectototal2neg ( n : nat ) ( P : nat -> UU )
  ( is : ∏ n' : nat , isdecprop ( P n' ) ) :
  ¬ ( ∏ n' : nat , natleh n' n -> P n' ) ->
  total2 ( λ n', ( natleh n' n ) × ¬ ( P n' ) ).
Proof.
  set ( P' := λ n' : nat, make_hProp _ ( is n' ) ).
  induction n as [ | n IHn ].
  -
 intro nf.
    set ( nf0 := negf ( invweq ( weqforallnatlehn0 P' ) ) nf ).
    split with 0.
    apply ( make_dirprod ( isreflnatleh 0 ) nf0 ).
  -
 intro nf.
    set ( nf2 := negf ( invweq ( weqforallnatlehnsn' n P' ) ) nf ).
    set ( nf3 := fromneganddecy ( is ( S n ) ) nf2 ).
    destruct nf3 as [ f1 | f2 ].
    +
 set ( int := IHn f1 ).
      destruct int as [ n' d2 ].
      destruct d2 as [ l np ].
      split with n'.
      split with ( natlehtolehs _ _ l ).
      apply np.
    +
 split with ( S n ).
      split with ( isreflnatleh _ ).
      apply f2.
Defined.

Definition natdecleast ( F : nat -> UU ) ( is : ∏ n , isdecprop ( F n ) ) :=
  total2 ( λ  n : nat, ( F n ) × ( ∏ n' : nat , F n' -> natleh n n' ) ).

Lemma isapropnatdecleast ( F : nat -> UU ) ( is : ∏ n , isdecprop ( F n ) ) :
  isaprop ( natdecleast F is ).
Proof.
  intros.
  set ( P := λ n' : nat, make_hProp _ ( is n' ) ).
  assert ( int1 : ∏ n : nat, isaprop ( ( F n ) × ( ∏ n' : nat , F n' -> natleh n n' ) ) ).
  {
 intro n.
    apply isapropdirprod.
    -
 apply ( pr2 ( P n ) ).
    -
 apply impred.
      intro t.
      apply impred.
      intro.
      apply ( pr2 ( natleh n t ) ).
  }
  set ( int2 := ( λ n : nat, make_hProp _ ( int1 n ) ) : nat -> hProp ).
  change ( isaprop ( total2 int2 ) ).
  apply isapropsubtype.
  intros x1 x2.
intros c1 c2.
  simpl in *.
  destruct c1 as [ e1 c1 ].
  destruct c2 as [ e2 c2 ].
  set ( l1 := c1 x2 e2 ).
  set ( l2 := c2 x1 e1 ).
  apply ( isantisymmnatleh _ _ l1 l2 ).
Defined.

Theorem accth ( F : nat -> UU ) ( is : ∏ n , isdecprop ( F n ) )
        ( is' : hexists F ) : natdecleast F is.
Proof.
  revert is'.
  simpl.
  apply (@hinhuniv _ ( make_hProp _ ( isapropnatdecleast F is ) ) ).
  intro t2.
  destruct t2 as [ n l ].
  simpl.
  set ( F' := λ n' : nat, hexists ( λ n'', ( natleh n'' n' ) × ( F n'' ) ) ).
  assert ( X : ∏ n' , F' n' -> natdecleast F is ).
  {
 intro n'.
    induction n' as [ | n' IHn' ].
    -
 apply ( @hinhuniv _  ( make_hProp _ ( isapropnatdecleast F is ) ) ).
      intro t2.
      destruct t2 as [ n'' is'' ].
      destruct is'' as [ l'' d'' ].
      split with 0.
      split.
      +
 set ( e := natleh0tois0 l'' ).
        clearbody e.
        destruct e.
        apply d''.
      +
 apply ( λ n', λ f : _, natleh0n n' ).
    -
 apply ( @hinhuniv _  ( make_hProp _ ( isapropnatdecleast F is ) ) ).
      intro t2.
      destruct t2 as [ n'' is'' ].
      set ( j := natlehchoice2 _ _ ( pr1 is'' ) ).
      destruct j as [ jl | je ].
      +
 simpl.
        apply ( IHn' ( hinhpr ( tpair _ n'' ( make_dirprod jl ( pr2 is'' ) ) ) ) ).
      +
 simpl.
        rewrite je in is''.
        destruct is'' as [ nn is'' ].
        clear nn.
clear je.
clear n''.
        assert ( is' : isdecprop ( F' n' ) ) by apply ( isdecbexists n' F is ).
        destruct ( pr1 is' ) as [ f | nf ].
        *
 apply ( IHn'  f ).
        *
 split with ( S n' ).
          split with is''.
          intros n0 fn0.
          destruct ( natlthorgeh n0 ( S n' ) )  as [ l' | g' ].
          --
 set ( i' := natlthtolehsn _ _ l' ).
             destruct ( nf ( hinhpr ( tpair _ n0 ( make_dirprod i' fn0 ) ) ) ).
          --
 apply g'.
  }
  apply ( X n ( hinhpr ( tpair _ n ( make_dirprod ( isreflnatleh n ) l ) ) ) ).
Defined.

Corollary dni_lastelement_is_inj {n : nat} {i j : ⟦n⟧ }
  (e : dni_lastelement i = dni_lastelement j) :
  i = j.
Proof.
  apply isinjstntonat.
  unfold dni_lastelement in e.
  apply (maponpaths pr1) in e.
  exact e.
Defined.

Corollary dni_lastelement_eq : ∏ (n : nat) (i : ⟦S n⟧ ) (ie : pr1 i < n),
    i = dni_lastelement (make_stn n (pr1 i) ie).
Proof.
  intros n i ie.
  apply isinjstntonat.
  apply idpath.
Defined.

Corollary lastelement_eq : ∏ (n : nat) (i : ⟦S n⟧ ) (e : pr1 i = n),
    i = lastelement.
Proof.
  intros n i e.
  unfold lastelement.
  apply isinjstntonat.
  apply e.
Defined.

Ltac inductive_reflexivity i b :=

  induction i as [|i];
  [ try apply isinjstntonat ; apply idpath |
    contradicts (negnatlthn0 i) b || inductive_reflexivity i b ].

Definition concatenate' {X:UU} {m n:nat} (f : ⟦m⟧ -> X) (g : ⟦n⟧ -> X) : ⟦m+n⟧ -> X.
Proof.
  intros i.

  induction (weqfromcoprodofstn_invmap _ _ i) as [j | k].
  +
 exact (f j).
  +
 exact (g k).
Defined.

Definition concatenate'_r0 {X:UU} {m:nat} (f : ⟦m⟧ -> X) (g : ⟦0⟧ -> X) :
  concatenate' f g = transportb (λ n, ⟦n⟧ -> X) (natplusr0 m) f.
Proof.
  intros.
apply funextfun; intro i.
unfold concatenate'.
  rewrite weqfromcoprodofstn_invmap_r0; simpl.
clear g.
  apply transportb_fun'.
Defined.

Definition concatenate'_r0' {X:UU} {m:nat} (f : ⟦m⟧ -> X) (g : ⟦0⟧ -> X) (i : ⟦m+0⟧ ) :
  concatenate' f g i = f (transportf stn (natplusr0 m) i).
Proof.
  intros.
  unfold concatenate'.
  rewrite weqfromcoprodofstn_invmap_r0.
  apply idpath.
Defined.

Definition flatten' {X:UU} {n:nat} {m: ⟦n⟧ -> nat} :
  (∏ (i: ⟦n⟧ ), ⟦m i⟧ -> X) -> ( ⟦stnsum m⟧ -> X).
Proof.
  intros g.
  exact (uncurry g ∘ invmap (weqstnsum1 m)).
Defined.

Definition stn_predicate {n : nat} (P : ⟦n⟧ -> UU)
           (k : nat) (h h' : k < n) :
           P (k,,h) -> P (k,,h').
Proof.
  intros H.
  transparent assert (X : (h = h')).
  -
 apply propproperty.
  -
 exact (transportf (λ x, P (k,,x)) X H).
Defined.

Definition two := ⟦2⟧.

Definition two_rec {A : UU} (a b : A) : ⟦2⟧ -> A.
Proof.
  induction 1 as [n p].
  induction n as [|n _]; [apply a|].
  induction n as [|n _]; [apply b|].
  induction (nopathsfalsetotrue p).
Defined.

Definition two_rec_dep (P : two -> UU):
  P (● 0) -> P (● 1) -> ∏ n, P n.
Proof.
  intros a b n.
  induction n as [n p].
  induction n as [|n _].
eapply stn_predicate.
apply a.
  induction n as [|n _].
eapply stn_predicate.
apply b.
  induction (nopathsfalsetotrue p).
Defined.

Definition three := stn 3.

Definition three_rec {A : UU} (a b c : A) : stn 3 -> A.
Proof.
  induction 1 as [n p].
  induction n as [|n _]; [apply a|].
  induction n as [|n _]; [apply b|].
  induction n as [|n _]; [apply c|].
  induction (nopathsfalsetotrue p).
Defined.

Definition three_rec_dep (P : three -> UU):
  P (● 0) -> P (● 1) -> P (● 2) -> ∏ n, P n.
Proof.
  intros a b c n.
  induction n as [n p].
  induction n as [|n _].
eapply stn_predicate.
apply a.
  induction n as [|n _].
eapply stn_predicate.
apply b.
  induction n as [|n _].
eapply stn_predicate.
apply c.
  induction (nopathsfalsetotrue p).
Defined.

Definition is_stn_increasing {m : nat} (f : ⟦m⟧ → nat) :=
  ∏ (i j: ⟦m⟧ ), i ≤ j → f i ≤ f j.

Definition is_stn_strictly_increasing {m : nat} (f : ⟦m⟧ → nat) :=
  ∏ (i j: ⟦m⟧ ), i < j → f i < f j.

Lemma is_strincr_impl_incr {m : nat} (f : ⟦m⟧ → nat) :
  is_stn_strictly_increasing f -> is_stn_increasing f.
Proof.
  intros inc ? ? e.
induction (natlehchoice _ _ e) as [I|J]; clear e.
  +
 apply natlthtoleh.
apply inc.
exact I.
  +
 assert (J' : i = j).
    {
 apply subtypePath_prop.
exact J.
}
    clear J.
induction J'.
apply isreflnatleh.
Defined.

Lemma is_incr_impl_strincr {m : nat} (f : ⟦m⟧ → nat) :
  isincl f -> is_stn_increasing f -> is_stn_strictly_increasing f.
Proof.
  intros incl incr i j e.
  assert (d : i ≤ j).
  {
 apply natlthtoleh.
assumption.
}
  assert (c := incr _ _ d); clear d.
  assert (b : i != j).
  {
 intro p.
induction p.
exact (isirreflnatlth _ e).
}
  induction (natlehchoice _ _ c) as [T|U].
  -
 exact T.
  -
 apply fromempty.
    unfold isincl,isofhlevel,isofhlevelf in incl.
    assert (V := invmaponpathsincl f incl i j U).
    induction V.
    exact (isirreflnatlth _ e).
Defined.

Lemma stnsum_ge1 {m : nat} (f : ⟦m⟧ → nat) : ( ∏ i, f i ≥ 1 ) → stnsum f ≥ m.
Proof.
  intros G.
  set (g := λ i:⟦m⟧, 1).
  assert (E : stnsum g = m).
  {
 apply stnsum_1.
}
  assert (F : stnsum g ≤ stnsum f).
  {
 apply stnsum_le.
exact G.
}
  generalize E F; generalize (stnsum g); clear E F g; intros s e i.
  induction e.
  exact i.
Defined.

Lemma stnsum_add {m : nat} (f g : ⟦m⟧ → nat) : stnsum (λ i, f i + g i) = stnsum f + stnsum g.
Proof.
  intros.
  induction m as [|m I].
  -
 apply idpath.
  -
 rewrite 3 stnsum_step.
    change ((λ i : ⟦ S m ⟧, f i + g i) ∘ dni lastelement)
    with (λ y : ⟦ m ⟧, f (dni lastelement y) + g (dni lastelement y)).
    rewrite I.
rewrite natplusassoc.
    rewrite natplusassoc.
simpl.
apply maponpaths.
rewrite natpluscomm.
    rewrite natplusassoc.
apply maponpaths.
rewrite natpluscomm.
apply idpath.
Defined.

Lemma stnsum_lt {m : nat} (f g : ⟦m⟧ → nat) :
  ( ∏ i, f i < g i ) → stnsum g ≥ stnsum f + m.
Proof.
  intros.
set (h := λ i, f i + 1).
  assert (E : stnsum h = stnsum f + m).
  {
 unfold h; clear h.
rewrite stnsum_add.
rewrite stnsum_1.
apply idpath.
}
  rewrite <- E.
apply stnsum_le.
intros i.
unfold h.
apply natlthtolehp1.
apply X.
Defined.

Local Arguments dni {_} _ _.

Lemma stnsum_diffs {m : nat} (f : ⟦S m⟧ → nat) : is_stn_increasing f ->
  stnsum (λ i, f (dni_firstelement i) - f (dni_lastelement i)) =
  f lastelement - f firstelement.
Proof.
  intros e.
  induction m as [|m I].
  -
 change (0 = f firstelement - f firstelement).
    apply pathsinv0.
    apply minuseq0'.
  -
 rewrite stnsum_step.
    change (f (dni_firstelement lastelement)) with (f lastelement).
    rewrite natpluscomm.
    use (_ @ ! @natdiffplusdiff
                     (f lastelement)
                     (f (dni_lastelement lastelement))
                     (f firstelement) _ _).
    +
 apply maponpaths.
      use (_ @ I (f ∘ dni_lastelement) _ @ _).
      *
 simpl.
apply stnsum_eq; intros i.
        rewrite replace_dni_last.
apply idpath.
      *
 intros i j s.
unfold funcomp.
apply e.
apply s.
      *
 apply idpath.
    +
 apply e.
apply lastelement_ge.
    +
 apply e.
apply firstelement_le.
Defined.

Lemma stn_ord_incl {m : nat} (f : ⟦S m⟧ → nat) :
  is_stn_strictly_increasing f  →  f lastelement ≥ f firstelement + m.
Proof.
  intros strinc.
  assert (inc := is_strincr_impl_incr _ strinc).
  set (d := λ i : ⟦ m ⟧, f (dni_firstelement i) - f (dni_lastelement i)).
  assert (E := stnsum_diffs f inc).
  change (stnsum d = f lastelement - f firstelement) in E.
  assert (F : ∏ i, f (dni_firstelement i) > f (dni_lastelement i)).
  {
 intros i.
apply strinc.
change (stntonat _ i < S(stntonat _ i)).
apply natlthnsn.
}
  assert (G : ∏ i, d i ≥ 1).
  {
 intros i.
apply natgthtogehsn.
apply minusgth0.
apply F.
}
  clear F.
  assert (H := stnsum_ge1 _ G).
clear G.
  rewrite E in H.
clear E d.
  assert (I : f lastelement ≥ f firstelement).
  {
 apply inc.
apply idpath.
}
  assert (J := minusplusnmm _ _ I); clear I.
  rewrite <- J; clear J.
  rewrite natpluscomm.
  apply natgehandplusl.
  exact H.
Defined.

Lemma stn_ord_inj {n : nat} (f : incl (⟦n⟧) (⟦n⟧)) :
  (∏ (i j: ⟦n⟧ ), i ≤ j → f i ≤ f j) -> ∏ i, f i = i.
Proof.
  intros inc ?.
  induction n as [|n I].
  -
 apply fromempty.
apply negstn0.
assumption.
  -
 assert (strincr : is_stn_strictly_increasing (pr1incl _ _ f)).
    {
 apply is_incr_impl_strincr.
      {
 use (isinclcomp f (stntonat_incl _)).
}
      {
 exact inc.
}
 }
    assert (M : stntonat _ (f lastelement) = n).
    {
 apply isantisymmnatgeh.
      *
 assert (N : f lastelement ≥ f firstelement + n).
        {
 exact (stn_ord_incl (pr1incl _ _ f) strincr).
}
        use (istransnatgeh _ _ _ N).
        apply natgehplusnmm.
      *
 exact (stnlt (f lastelement)).
}
    assert (L : ∏ j, f (dni lastelement j) < n).
    {
 intros.
induction M.
apply strincr.
apply dni_last_lt.
}

    pose (f'' :=
        inclcomp (inclcomp (make_incl _ (isincldni n lastelement)) f)
                 (make_incl _ (isinclstntonat _))).
    pose (f' := λ j : ⟦n⟧, make_stn n (f'' j) (L j)).
    assert (J : isincl f').
    {
 unfold f'.
intros x j j'.
      apply iscontraprop1.
      *
 apply isaset_hfiber; apply isasetstn.
      *
 use subtypePath.
        **
 intros ?.
apply isasetstn.
        **
 induction j as [j e].
induction j' as [j' e'].
simpl.
           apply (invmaponpathsincl f'' (pr2 f'')).
           apply (base_paths _ _ (e @ !e')).
}
    assert (F : ∏ j : ⟦n⟧, f' j = j).
    {
 apply (I (make_incl _ J)).
      intros j j' lt.
apply inc.
      change (pr1 (dni lastelement j) ≤ pr1 (dni lastelement j')).
      rewrite 2?dni_last.
assumption.
}

    apply subtypePath_prop.
    change (stntonat _ (f i) = i).
    induction (natgehchoice _ _ (lastelement_ge i)) as [ge | eq].
    +
 pose (p := maponpaths (stntonat _) (F (make_stn n i ge))).
      simpl in p.
induction p.
      change (stntonat _ (f i) = f (dni lastelement (make_stn n i ge))).
      apply maponpaths, maponpaths, pathsinv0.
      apply subtypePath_prop.
apply dni_last.
    +
 apply subtypePath_prop in eq.
      rewrite <- eq.
      apply M.
Defined.

Lemma stn_ord_bij {n : nat} (f : ⟦ n ⟧ ≃ ⟦ n ⟧) :
  (∏ (i j: ⟦n⟧ ), i ≤ j → f i ≤ f j) -> ∏ i, f i = i.
Proof.
  apply (stn_ord_inj (weqtoincl f)).
Defined.

End StandardFiniteSets.
Module Export FiniteSets.

Import UniMath.MoreFoundations.Tactics.
Import UniMath.MoreFoundations.DecidablePropositions.
Import UniMath.MoreFoundations.NegativePropositions.

Definition nelstruct ( n : nat ) ( X : UU ) := weq ( stn n ) X .

Definition nelstructonstn ( n : nat ) : nelstruct n ( stn n ) := idweq _ .

Definition nelstructweqf { X Y : UU } { n : nat } ( w : X ≃ Y ) ( sx : nelstruct n X ) : nelstruct n Y := weqcomp sx w .

Definition nelstructweqb { X Y : UU } { n : nat } ( w : X ≃ Y ) ( sy : nelstruct n Y ) : nelstruct n X := weqcomp sy ( invweq w ) .

Definition nelstructonempty : nelstruct 0 empty := weqstn0toempty .

Definition nelstructoncoprodwithunit { X : UU } { n : nat } ( sx : nelstruct n X ) : nelstruct ( S n ) ( coprod X unit ) :=  weqcomp ( invweq ( weqdnicoprod n lastelement ) ) ( weqcoprodf sx ( idweq unit ) ) .

Definition nelstructoncompl {X} {n} (x:X) : nelstruct (S n) X -> nelstruct n (compl X x).
Proof.
  intros sx.
  refine (invweq ( weqoncompl ( invweq sx ) x) ∘ _ ∘ weqdnicompl (invweq sx x))%weq.
  apply compl_weq_compl_ne.
Defined.

Definition nelstructoncoprod { X  Y : UU } { n m : nat } ( sx : nelstruct n X ) ( sy : nelstruct m Y ) : nelstruct ( n + m ) ( coprod X Y ) := weqcomp ( invweq ( weqfromcoprodofstn n m ) ) ( weqcoprodf sx sy ) .

Definition nelstructontotal2 { X : UU } ( P : X -> UU ) ( f : X -> nat ) { n : nat } ( sx : nelstruct n X ) ( fs : ∏ x : X , nelstruct ( f x ) ( P x ) ) : nelstruct ( stnsum ( funcomp ( pr1 sx ) f ) ) ( total2 P )  := weqcomp ( invweq ( weqstnsum ( funcomp ( pr1 sx ) P ) ( funcomp ( pr1 sx ) f ) ( λ i : stn n, fs ( ( pr1 sx ) i ) ) ) )  ( weqfp sx P )  .

Definition nelstructondirprod { X Y : UU } { n m : nat } ( sx : nelstruct n X ) ( sy : nelstruct m Y ) : nelstruct ( n * m ) ( dirprod X Y ) := weqcomp ( invweq ( weqfromprodofstn n m ) ) ( weqdirprodf sx sy ) .

Definition nelstructonfun { X Y : UU } { n m : nat } ( sx : nelstruct n X ) ( sy : nelstruct m Y ) : nelstruct ( natpower m n ) ( X -> Y ) := weqcomp ( invweq ( weqfromfunstntostn n m ) ) ( weqcomp ( weqbfun _ ( invweq sx ) ) ( weqffun _ sy ) )  .

Definition nelstructonforall { X : UU } ( P : X -> UU ) ( f : X -> nat ) { n : nat } ( sx : nelstruct n X ) ( fs : ∏ x : X , nelstruct ( f x ) ( P x ) ) : nelstruct ( stnprod ( funcomp ( pr1 sx ) f ) ) ( ∏ x : X , P x )  := invweq ( weqcomp ( weqonsecbase P sx ) ( weqstnprod ( funcomp ( pr1 sx ) P ) ( funcomp ( pr1 sx ) f ) ( λ i : stn n, fs ( ( pr1 sx ) i ) ) ) )  .

Definition nelstructonweq { X : UU } { n : nat } ( sx : nelstruct n X ) : nelstruct ( factorial n ) ( X ≃ X ) := weqcomp ( invweq ( weqfromweqstntostn n ) ) ( weqcomp ( weqbweq _ ( invweq sx ) ) ( weqfweq _ sx ) ) .

Definition isofnel ( n : nat ) ( X : UU ) : hProp := ishinh ( weq ( stn n ) X ) .

Lemma isofneluniv { n : nat} { X : UU }  ( P : hProp ) : ( ( nelstruct n X ) -> P ) -> ( isofnel n X -> P ) .
Proof.
intros.
 apply @hinhuniv with ( weq ( stn n ) X ) .
assumption.
assumption.
Defined.

Definition isofnelstn ( n : nat ) : isofnel n ( stn n ) := hinhpr ( nelstructonstn n ) .

Definition isofnelcoprodwithunit { X : UU } { n : nat } ( sx : isofnel n X ) : isofnel ( S n ) ( coprod X unit ) :=   hinhfun ( λ sx0 : _,  nelstructoncoprodwithunit sx0 ) sx .

Definition isofnelcompl { X : UU } { n : nat } ( x : X ) ( sx : isofnel ( S n ) X ) : isofnel n ( compl X x ) := hinhfun ( λ sx0 : _,  nelstructoncompl x sx0 ) sx .

Definition isofnelcoprod { X  Y : UU } { n m : nat } ( sx : isofnel n X ) ( sy : isofnel m Y ) : isofnel ( n + m ) ( coprod X Y ) :=  hinhfun2 ( λ sx0 : _, λ sy0 : _,  nelstructoncoprod sx0 sy0 ) sx sy .

Definition isofnelondirprod { X Y : UU } { n m : nat } ( sx : isofnel n X ) ( sy : isofnel m Y ) : isofnel ( n * m ) ( dirprod X Y ) := hinhfun2 ( λ sx0 : _, λ sy0 : _,  nelstructondirprod sx0 sy0 ) sx sy .

Definition isofnelonfun { X Y : UU } { n m : nat } ( sx : isofnel n X ) ( sy : isofnel m Y ) : isofnel ( natpower m n ) ( X -> Y ) := hinhfun2 ( λ sx0 : _, λ sy0 : _,  nelstructonfun sx0 sy0 ) sx sy .

Definition isofnelonweq { X : UU } { n : nat } ( sx : isofnel n X ) : isofnel ( factorial n ) ( X ≃ X ) := hinhfun ( λ sx0 : _,  nelstructonweq sx0 ) sx .

Definition finstruct  ( X : UU ) := total2 ( λ n : nat, nelstruct n X ) .

Definition finstructToFunction {X} (S : finstruct X) := pr2 S : nelstruct (pr1 S) X.

Definition make_finstruct  ( X : UU )  := tpair ( λ n : nat, nelstruct n X ) .

Definition finstructonstn ( n : nat ) : finstruct ( stn n ) := tpair _ n ( nelstructonstn n ) .

Definition finstructweqf { X Y : UU } ( w : X ≃ Y ) ( sx : finstruct X ) : finstruct Y := tpair _ ( pr1 sx ) ( nelstructweqf w ( pr2 sx ) ) .

Definition finstructweqb { X Y : UU } ( w : X ≃ Y ) ( sy : finstruct Y ) : finstruct X :=  tpair _ ( pr1 sy ) ( nelstructweqb w ( pr2 sy ) ) .

Definition finstructonempty : finstruct empty := tpair _ 0 nelstructonempty .

Definition finstructoncoprodwithunit { X : UU }  ( sx : finstruct X ) : finstruct ( coprod X unit ) :=  tpair _ ( S ( pr1 sx ) ) ( nelstructoncoprodwithunit ( pr2 sx ) ) .

Definition finstructoncompl { X : UU } ( x : X ) ( sx : finstruct X ) : finstruct ( compl X x ) .
intros .
unfold finstruct .
 unfold finstruct in sx .
destruct sx as [ n w ] .
destruct n as [ | n ] .
 destruct ( negstn0 ( invweq w x ) ) .
split with n .
  apply ( nelstructoncompl x w ) .
 Defined .

Definition finstructoncoprod { X  Y : UU } ( sx : finstruct X ) ( sy : finstruct Y ) : finstruct ( coprod X Y ) := tpair _ ( ( pr1 sx ) + ( pr1 sy ) ) ( nelstructoncoprod ( pr2 sx ) ( pr2 sy ) ) .

Definition finstructontotal2 { X : UU } ( P : X -> UU )   ( sx : finstruct X ) ( fs : ∏ x : X , finstruct ( P x ) ) : finstruct ( total2 P ) := tpair _ ( stnsum ( funcomp ( pr1 ( pr2 sx ) ) ( λ x : X,  pr1 ( fs x ) ) ) ) ( nelstructontotal2 P ( λ x : X, pr1 ( fs x ) ) ( pr2 sx ) ( λ x : X, pr2 ( fs x ) ) ) .

Definition finstructondirprod { X Y : UU } ( sx : finstruct X ) ( sy : finstruct Y ) : finstruct ( dirprod X Y ) := tpair _ ( ( pr1 sx ) * ( pr1 sy ) ) ( nelstructondirprod ( pr2 sx ) ( pr2 sy ) ) .

Definition finstructondecsubset { X : UU }  ( f : X -> bool ) ( sx : finstruct X ) : finstruct ( hfiber f true ) := tpair _ ( pr1 ( weqfromdecsubsetofstn ( funcomp ( pr1 ( pr2 sx ) ) f ) ) ) ( weqcomp ( invweq ( pr2 ( weqfromdecsubsetofstn ( funcomp ( pr1 ( pr2 sx ) ) f ) ) ) ) ( weqhfibersgwtog ( pr2 sx ) f true ) ) .

Definition finstructonfun { X Y : UU } ( sx : finstruct X ) ( sy : finstruct Y ) : finstruct ( X -> Y ) := tpair _ ( natpower ( pr1 sy ) ( pr1 sx ) ) ( nelstructonfun ( pr2 sx ) ( pr2 sy ) ) .

Definition finstructonforall { X : UU } ( P : X -> UU )  ( sx : finstruct X ) ( fs : ∏ x : X , finstruct ( P x ) ) : finstruct ( ∏ x : X , P x )  := tpair _ ( stnprod ( funcomp ( pr1 ( pr2 sx ) ) ( λ x : X,  pr1 ( fs x ) ) ) ) ( nelstructonforall P ( λ x : X, pr1 ( fs x ) ) ( pr2 sx ) ( λ x : X, pr2 ( fs x ) ) ) .

Definition finstructonweq { X : UU }  ( sx : finstruct X ) : finstruct ( X ≃ X ) := tpair _ ( factorial ( pr1 sx ) ) ( nelstructonweq ( pr2 sx ) ) .

Definition isfinite  ( X : UU ) := ishinh ( finstruct X ) .

Definition FiniteSet := ∑ X:UU, isfinite X.

Definition isfinite_to_FiniteSet {X:UU} (f:isfinite X) : FiniteSet := X,,f.

Lemma isfinite_isdeceq X : isfinite X -> isdeceq X.

Proof.
intros isfin.
       apply (isfin (make_hProp _ (isapropisdeceq X))); intro f; clear isfin; simpl.
       apply (isdeceqweqf (pr2 f)).
       apply isdeceqstn.
Defined.

Lemma isfinite_isaset X : isfinite X -> isaset X.
Proof.
  intros isfin.
apply (isfin (make_hProp _ (isapropisaset X))); intro f; clear isfin; simpl.
  apply (isofhlevelweqf 2 (pr2 f)).
apply isasetstn.
Defined.

Definition FiniteSet_to_hSet : FiniteSet -> hSet.
Proof.
intro X.
exact (make_hSet (pr1 X) (isfinite_isaset (pr1 X) (pr2 X))).
Defined.
Coercion FiniteSet_to_hSet : FiniteSet >-> hSet.

Definition fincard { X : UU } ( is : isfinite X ) : nat .
  intros.
apply (squash_pairs_to_set (λ n, stn n ≃ X) isasetnat).
  {
 intros n n' w w'.
apply weqtoeqstn.
exact (invweq w' ∘ w)%weq.
}
  assumption.
Defined.

Definition cardinalityFiniteSet (X:FiniteSet) : nat := fincard (pr2 X).

Theorem ischoicebasefiniteset { X : UU } ( is : isfinite X ) : ischoicebase X .
intros .
apply ( @hinhuniv ( finstruct X ) ( ischoicebase X ) ) .
 intro nw .
destruct nw as [ n w ] .
  apply ( ischoicebaseweqf w ( ischoicebasestn n ) ) .
 apply is .
 Defined .

Definition isfinitestn ( n : nat ) : isfinite ( stn n ) := hinhpr ( finstructonstn n ) .

Definition isfiniteweqf { X Y : UU } ( w : X ≃ Y ) ( sx : isfinite X ) : isfinite Y :=  hinhfun ( λ sx0 : _,  finstructweqf w sx0 ) sx .

Definition isfiniteweqb { X Y : UU } ( w : X ≃ Y ) ( sy : isfinite Y ) : isfinite X :=   hinhfun ( λ sy0 : _,  finstructweqb w sy0 ) sy .

Definition isfiniteempty : isfinite empty := hinhpr finstructonempty .

Definition isfinitecoprodwithunit { X : UU } ( sx : isfinite X ) : isfinite ( coprod X unit ) :=  hinhfun ( λ sx0 : _, finstructoncoprodwithunit sx0 ) sx .

Definition isfinitecompl { X : UU } ( x : X ) ( sx : isfinite X ) : isfinite ( compl X x ) := hinhfun ( λ sx0 : _, finstructoncompl x sx0 ) sx .

Definition isfinitecoprod { X  Y : UU } ( sx : isfinite X ) ( sy : isfinite Y ) : isfinite ( coprod X Y ) := hinhfun2 ( λ sx0 : _, λ sy0 : _, finstructoncoprod sx0 sy0 ) sx sy .

Definition isfinitetotal2 { X : UU } ( P : X -> UU ) ( sx : isfinite X ) ( fs : ∏ x : X , isfinite ( P x ) ) : isfinite ( total2 P ) .
Proof .
intros .
set ( fs' := ischoicebasefiniteset sx _ fs ) .
 apply ( hinhfun2 ( fun fx0 : ∏ x : X , finstruct ( P x )  => λ sx0 : _, finstructontotal2 P sx0 fx0 ) fs' sx ) .
 Defined .

Definition FiniteSetSum {I:FiniteSet} (X : I -> FiniteSet) : FiniteSet.
Proof.
  intros.
exists (∑ i, X i).
  apply isfinitetotal2.
  -
 exact (pr2 I).
  -
 intros i.
exact (pr2 (X i)).
Defined.

Declare Scope finset.

Notation "'∑' x .. y , P" := (FiniteSetSum (λ x,.. (FiniteSetSum (λ y, P))..))
  (at level 200, x binder, y binder, right associativity) : finset.

Definition isfinitedirprod { X Y : UU } ( sx : isfinite X ) ( sy : isfinite Y ) : isfinite ( dirprod X Y ) := hinhfun2 ( λ sx0 : _, λ sy0 : _, finstructondirprod sx0 sy0 ) sx sy .

Definition isfinitedecsubset { X : UU } ( f : X -> bool ) ( sx : isfinite X ) : isfinite ( hfiber f true ) := hinhfun ( λ sx0 : _,  finstructondecsubset f sx0 ) sx .

Definition isfinitefun { X Y : UU } ( sx : isfinite X ) ( sy : isfinite Y ) : isfinite ( X -> Y ) := hinhfun2 ( λ sx0 : _, λ sy0 : _, finstructonfun sx0 sy0 ) sx sy .

Definition isfiniteforall { X : UU } ( P : X -> UU ) ( sx : isfinite X ) ( fs : ∏ x : X , isfinite ( P x ) ) : isfinite ( ∏ x : X , P x ) .
Proof .
intros .
set ( fs' := ischoicebasefiniteset sx _ fs ) .
 apply ( hinhfun2 ( fun fx0 : ∏ x : X , finstruct ( P x )  => λ sx0 : _, finstructonforall P sx0 fx0 ) fs' sx ) .
 Defined .

Definition isfiniteweq { X : UU } ( sx : isfinite X ) : isfinite ( X ≃ X ) := hinhfun ( λ sx0 : _,  finstructonweq sx0 ) sx .

Definition isfinite_to_DecidableEquality {X} : isfinite X -> DecidableRelation X.
  intros fin x y.
  exact (@isdecprop_to_DecidableProposition
                  (x=y)
                  (isdecpropif (x=y)
                               (isfinite_isaset X fin x y)
                               (isfinite_isdeceq X fin x y))).
Defined.

Lemma subsetFiniteness {X} (is : isfinite X) (P : DecidableSubtype X) :
  isfinite (decidableSubtypeCarrier P).
  intros.
  assert (fin : isfinite (decidableSubtypeCarrier' P)).
  {
 now apply isfinitedecsubset.
}
  refine (isfiniteweqf _ fin).
  apply decidableSubtypeCarrier_weq.
Defined.

Definition subsetFiniteSet {X:FiniteSet} (P:DecidableSubtype X) : FiniteSet.
exact (isfinite_to_FiniteSet (subsetFiniteness (pr2 X) P)).
Defined.

Definition fincard_subset {X} (is : isfinite X) (P : DecidableSubtype X) : nat.
exact (fincard (subsetFiniteness is P)).
Defined.

Definition fincard_standardSubset {n} (P : DecidableSubtype (stn n)) : nat.
intros.
exact (fincard (subsetFiniteness (isfinitestn n) P)).
Defined.

Local Definition bound01 (P:DecidableProposition) : ((choice P 1 0) ≤ 1)%nat.
Proof.
  intros.
unfold choice.
choose P p q; reflexivity.
Defined.

Definition tallyStandardSubset {n} (P: DecidableSubtype (stn n)) : stn (S n).
intros.
exists (stnsum (λ x, choice (P x) 1 0)).
apply natlehtolthsn.
       apply (istransnatleh (m := stnsum(λ _ : stn n, 1))).
       {
 apply stnsum_le; intro i.
apply bound01.
}
       assert ( p : ∏ r s, r = s -> (r ≤ s)%nat).
{
 intros ? ? e.
destruct e.
apply isreflnatleh.
}
       apply p.
apply stnsum_1.
Defined.

Definition tallyStandardSubsetSegment {n} (P: DecidableSubtype (stn n))
           (i:stn n) : stn n.

  intros.
  assert (k := tallyStandardSubset
                 (λ j:stn i, P (stnmtostnn i n (natlthtoleh i n (pr2 i)) j))).
  apply (stnmtostnn (S i) n).
  {
 apply natlthtolehsn.
exact (pr2 i).
}
  exact k.
Defined.

End FiniteSets.

Module Export UniMath_DOT_CategoryTheory_DOT_Subcategory_DOT_Core_WRAPPED.
Module Export Core.
Import UniMath.MoreFoundations.PartA.

Definition is_sub_precategory {C : category}
    (C' : hsubtype C)
    (Cmor' : ∏ a b : C, hsubtype (a --> b)) :=
  (∏ a : C, C' a ->  Cmor' _ _ (identity a)) ×
  (∏ (a b c : C) (f: a --> b) (g : b --> c),
            Cmor' _ _ f -> Cmor' _ _  g -> Cmor' _ _  (f · g)).

Definition sub_precategories (C : category) :=
  total2 (fun C' : (hsubtype (ob C)) × (∏ a b:ob C, hsubtype (a --> b)) =>
           is_sub_precategory (pr1 C') (pr2 C')).

Definition sub_precategory_predicate_objects {C : category}
     (C': sub_precategories C):
       hsubtype (ob C) := pr1 (pr1 C').

Definition sub_ob {C : category}(C': sub_precategories C): UU :=
       (sub_precategory_predicate_objects C').

Definition sub_precategory_predicate_morphisms {C : category}
        (C':sub_precategories C) (a b : C) : hsubtype (a --> b) := pr2 (pr1 C') a b.

Definition sub_precategory_morphisms {C : category}(C':sub_precategories C)
      (a b : C) : UU :=  sub_precategory_predicate_morphisms C' a b.

Definition sub_precategory_id (C : category) (C':sub_precategories C) :
   ∏ a : ob C,
       sub_precategory_predicate_objects C' a ->
       sub_precategory_predicate_morphisms  C' _ _ (identity a) :=
         dirprod_pr1 (pr2 C').

Definition sub_precategory_comp (C : category) (C':sub_precategories C) :
   ∏ (a b c: ob C) (f: a --> b) (g : b --> c),
          sub_precategory_predicate_morphisms C' _ _ f ->
          sub_precategory_predicate_morphisms C' _ _ g ->
          sub_precategory_predicate_morphisms C' _ _  (f · g) :=
        dirprod_pr2 (pr2 C').

Definition precategory_object_from_sub_precategory_object (C:category)
         (C':sub_precategories C) (a : sub_ob C') :
    ob C := pr1 a.
Coercion precategory_object_from_sub_precategory_object :
     sub_ob >-> ob.

Definition precategory_morphism_from_sub_precategory_morphism (C:category)
          (C':sub_precategories C) (a b : ob C)
           (f : sub_precategory_morphisms C' a b) : a --> b := pr1 f .
Coercion precategory_morphism_from_sub_precategory_morphism :
         sub_precategory_morphisms >-> precategory_morphisms.

Definition sub_precategory_ob_mor (C : category)(C':sub_precategories C) :
     precategory_ob_mor.
  exists (sub_ob C').
  exact (λ a b, @sub_precategory_morphisms _ C' a b).
Defined.

Definition sub_precategory_data (C : category)(C':sub_precategories C) :
      precategory_data.
  exists (sub_precategory_ob_mor C C').
  split.
    intro c.
    exists (identity (C:=C) (pr1 c)).
    apply sub_precategory_id.
    apply (pr2 c).
  intros a b c f g.
  exists (compose (pr1 f) (pr1 g)).
  apply sub_precategory_comp.
  apply (pr2 f).
apply (pr2 g).
Defined.

Lemma eq_in_sub_precategory (C : category)(C':sub_precategories C)
      (a b : sub_ob C') (f g : sub_precategory_morphisms C' a b) :
          pr1 f = pr1 g -> f = g.
Proof.
  intro H.
  apply (total2_paths_f H).
  apply proofirrelevance.
  apply pr2.
Qed.

Definition is_precategory_sub_precategory (C : category)(C':sub_precategories C) :
    is_precategory (sub_precategory_data C C').
  repeat split;
  simpl; intros.
  unfold sub_precategory_comp;
  apply eq_in_sub_precategory; simpl;
  apply id_left.
  apply eq_in_sub_precategory.
simpl.
  apply id_right.
  apply eq_in_sub_precategory.
  cbn.
  apply assoc.
  apply eq_in_sub_precategory.
  cbn.
  apply assoc'.
Defined.

Definition carrier_of_sub_precategory (C : category)(C':sub_precategories C) :
   precategory := tpair _ _ (is_precategory_sub_precategory C C').

Definition has_homsets_carrier_of_subcategory (C : category) (C' : sub_precategories C)
  : has_homsets (carrier_of_sub_precategory C C').
  intros a b.
  cbn.
  apply (isofhleveltotal2 2).
  -
 apply C.
  -
 intro f.
    apply hlevelntosn.
    apply propproperty.
Qed.

Definition carrier_of_sub_category (C : category) (C' : sub_precategories C)
  : category
  := make_category _ (has_homsets_carrier_of_subcategory C C').

Coercion carrier_of_sub_category : sub_precategories >-> category.

Definition precategory_morphisms_in_subcat {C : category} {C':sub_precategories C}
   {a b : ob C'}(f : pr1 a --> pr1 b)
   (p : sub_precategory_predicate_morphisms C' (pr1 a) (pr1 b) (f)) :
       precategory_morphisms (C:=C') a b := tpair _ f p.

Definition sub_precategory_inclusion_data (C : category) (C':sub_precategories C):
  functor_data C' C.
  exists (@pr1 _ _ ).
  intros a b.
  exact (@pr1 _ _ ).
Defined.

Definition is_functor_sub_precategory_inclusion (C : category)
         (C':sub_precategories C) :
    is_functor  (sub_precategory_inclusion_data C C').
  split; simpl.
  unfold functor_idax .
intros.
 apply (idpath _ ).
  unfold functor_compax .
intros.
 apply (idpath _ ).
Qed.

Definition sub_precategory_inclusion (C : category) (C' : sub_precategories C) :
    functor C' C := tpair _ _ (is_functor_sub_precategory_inclusion C C').

Lemma is_set_sub_precategory_morphisms {C : category}
                                       (C' : sub_precategories C) (a b : ob C) :
  isaset (sub_precategory_morphisms C' a b).
  apply isofhlevel_hsubtype, C.
Defined.

Definition sub_precategory_morphisms_set {C : category}
  (C':sub_precategories C) (a b : ob C) : hSet :=
    tpair _ (sub_precategory_morphisms C' a b)
        (is_set_sub_precategory_morphisms C' a b).

Definition subcategory (C : category) (C' : sub_precategories C) : category.
  use make_category.
  -
 exact (carrier_of_sub_precategory C C').
  -
 intros ? ?.
    apply is_set_sub_precategory_morphisms.
Defined.

Definition restrict_functor_to_sub_precategory {C D : category}
           (C' : sub_precategories C) (F : functor C D) : functor C' D.
  use make_functor.
  -
 use make_functor_data.
    +
 exact (F ∘ precategory_object_from_sub_precategory_object _ C')%functions.
    +
 intros ? ?.
      apply (# F ∘ precategory_morphism_from_sub_precategory_morphism _ C' _ _)%functions.
  -
 use make_dirprod.
    +
 intro; apply (functor_id F).
    +
 intros ? ? ? ? ?; apply (functor_comp F).
Defined.

End Core.

End UniMath_DOT_CategoryTheory_DOT_Subcategory_DOT_Core_WRAPPED.
Module Export Monics.
Import UniMath.CategoryTheory.FunctorCategory.

Section def_monic.

  Variable C : category.
  Let hs : has_homsets C := homset_property C.

  Definition isMonic {y z : C} (f : y --> z) : UU :=
    ∏ (x : C) (g h : x --> y), g · f = h · f -> g = h.

  Definition make_isMonic {y z : C} (f : y --> z)
             (H : ∏ (x : C) (g h : x --> y), g · f = h · f -> g = h) : isMonic f := H.

  Lemma isapropisMonic {y z : C} (f : y --> z) : isaprop (isMonic f).
  Proof.
    apply impred_isaprop; intros t.
    apply impred_isaprop; intros g.
    apply impred_isaprop; intros h.
    apply impred_isaprop; intros H.
    apply hs.
  Qed.

  Definition Monic (y z : C) : UU := ∑ f : y --> z, isMonic f.

  Definition make_Monic {y z : C} (f : y --> z) (H : isMonic f) : Monic y z := tpair _ f H.

  Definition MonicArrow {y z : C} (M : Monic y z) : C⟦y, z⟧ := pr1 M.
  Coercion MonicArrow : Monic >-> precategory_morphisms.

  Lemma is_iso_isMonic {y x : C} (f : y --> x) (H : is_z_isomorphism f) : isMonic f.
  Proof.
    apply make_isMonic.
    intros z g h X.
    apply (post_comp_with_z_iso_is_inj H).
    exact X.
  Qed.

  Lemma is_iso_Monic {y x : C} (f : y --> x) (H : is_z_isomorphism f) : Monic y x.
  Proof.
    apply (make_Monic f (is_iso_isMonic f H)).
  Defined.

  Lemma identity_isMonic {x : C} : isMonic (identity x).
    apply (is_iso_isMonic (identity x) (is_z_isomorphism_identity x)).
  Defined.

  Lemma identity_Monic {x : C} : Monic x x.
    exact (tpair _ (identity x) (identity_isMonic)).
  Defined.

  Definition isMonic_comp {x y z : C} (f : x --> y) (g : y --> z) :
    isMonic f -> isMonic g -> isMonic (f · g).
  Proof.
    intros X X0.
apply make_isMonic.
intros x0 g0 h X1.
    repeat rewrite assoc in X1.
apply X0 in X1.
apply X in X1.
apply X1.
  Qed.

  Definition Monic_comp {x y z : C} (M1 : Monic x y) (M2 : Monic y z) :
    Monic x z := tpair _ (M1 · M2) (isMonic_comp M1 M2 (pr2 M1) (pr2 M2)).

  Definition isMonic_postcomp {x y z : C} (f : x --> y) (g : y --> z) :
    isMonic (f · g) -> isMonic f.
  Proof.
    intros X.
intros w φ ψ H.
    apply (maponpaths (λ f', f' · g)) in H.
    repeat rewrite <- assoc in H.
    apply (X w _ _ H).
  Defined.

  Lemma isMonic_path {x y : C} (f1 f2 : x --> y) (e : f1 = f2) (isM : isMonic f1) : isMonic f2.
  Proof.
    induction e.
exact isM.
  Qed.

  Lemma transport_target_isMonic {x y z : C} (f : x --> y) (E : isMonic f) (e : y = z) :
    isMonic (transportf (precategory_morphisms x) e f).
  Proof.
    induction e.
apply E.
  Qed.

End def_monic.
Arguments isMonic [C] [y] [z] _.

Section monics_subcategory.

  Variable C : category.

  Definition hsubtype_obs_isMonic : hsubtype C := (λ c : C, make_hProp _ isapropunit).

  Definition hsubtype_mors_isMonic : ∏ (a b : C), hsubtype (C⟦a, b⟧) :=
    (λ a b : C, (fun f : C⟦a, b⟧ => make_hProp _ (isapropisMonic C f))).

  Definition subprecategory_of_monics : sub_precategories C.
    use tpair.
    split.
    -
 exact hsubtype_obs_isMonic.
    -
 exact hsubtype_mors_isMonic.
    -
 cbn.
unfold is_sub_precategory.
cbn.
      split.
      +
 intros a tt.
exact (identity_isMonic C).
      +
 apply isMonic_comp.
  Defined.

  Definition has_homsets_subprecategory_of_monics : has_homsets subprecategory_of_monics.
    intros a b.
    apply is_set_sub_precategory_morphisms.
  Qed.

  Definition subcategory_of_monics : category := make_category _ has_homsets_subprecategory_of_monics.

  Definition subprecategory_of_monics_ob (c : C) : ob (subcategory_of_monics) := tpair _ c tt.

  Definition subprecategory_of_monics_mor {c' c : C} (f : c' --> c) (isM : isMonic f) :
    subcategory_of_monics⟦subprecategory_of_monics_ob c', subprecategory_of_monics_ob c⟧ :=
    tpair _ f isM.

End monics_subcategory.

Section monics_functorcategories.

  Lemma is_nat_trans_monic_from_pointwise_monics (C D : category)
        (F G : ob (functor_category C D)) (α : F --> G) (H : ∏ a : ob C, isMonic (pr1 α a)) :
    isMonic α.
  Proof.
    intros G' β η H'.
    use (nat_trans_eq).
    -
 apply D.
    -
 intros x.
      set (H'' := nat_trans_eq_pointwise H' x).
cbn in H''.
      apply (H x) in H''.
      exact H''.
  Qed.

End monics_functorcategories.

Lemma faithful_reflects_mono {C D : category} (F : functor C D)
      (FF : faithful F) : reflects_morphism F (@isMonic).
  unfold reflects_morphism.
  intros ? ? ? is_monic_Ff.
  intros ? ? ? eqcomp.
  apply (Injectivity (# F)).
  -
 apply isweqonpathsincl, FF.
  -
 apply is_monic_Ff.
    refine (!(functor_comp F g f) @ _).
    refine (_ @ functor_comp F h f).
    apply maponpaths; assumption.
Defined.

End Monics.
Import UniMath.CategoryTheory.FunctorCategory.

Section def_epi.

  Variable C : precategory.
  Hypothesis hs : has_homsets C.

  Definition isEpi {x y : C} (f : x --> y) : UU :=
    ∏ (z : C) (g h : y --> z), f · g = f · h -> g = h.

  Definition make_isEpi {x y : C} (f : x --> y)
             (H : ∏ (z : C) (g h : y --> z), f · g = f · h -> g = h) : isEpi f := H.

  Lemma isapropisEpi {y z : C} (f : y --> z) : isaprop (isEpi f).
  Proof.
    apply impred_isaprop; intros t.
    apply impred_isaprop; intros g.
    apply impred_isaprop; intros h.
    apply impred_isaprop; intros H.
    apply hs.
  Qed.

  Definition Epi (x y : C) : UU := ∑ f : x --> y, isEpi f.
  Definition make_Epi {x y : C} (f : x --> y) (H : isEpi f) :
    Epi x y := tpair _ f H.

  Definition EpiArrow {x y : C} (E : Epi x y) : C⟦x, y⟧ := pr1 E.
  Coercion EpiArrow : Epi >-> precategory_morphisms.

  Lemma is_iso_isEpi {x y : C} (f : x --> y) (H : is_z_isomorphism f) : isEpi f.
  Proof.
    apply make_isEpi.
    intros z g h X.
    apply (pre_comp_with_z_iso_is_inj H).
    exact X.
  Qed.

  Lemma is_iso_Epi {x y : C} (f : x --> y) (H : is_z_isomorphism f) : Epi x y.
  Proof.
    apply (make_Epi f (is_iso_isEpi f H)).
  Defined.

  Lemma identity_isEpi {x : C} : isEpi (identity x).
    apply (is_iso_isEpi (identity x) (is_z_isomorphism_identity x)).
  Defined.

  Lemma identity_Epi {x : C} : Epi x x.
    exact (tpair _ (identity x) (identity_isEpi)).
  Defined.

  Definition isEpi_comp {x y z : C} (f : x --> y) (g : y --> z) :
    isEpi f -> isEpi g -> isEpi (f · g).
  Proof.
    intros X X0.
unfold isEpi.
intros z0 g0 h X1.
    repeat rewrite <- assoc in X1.
apply X in X1.
apply X0 in X1.
apply X1.
  Qed.

  Definition Epi_comp {x y z : C} (E1 : Epi x y) (E2 : Epi y z) :
    Epi x z := tpair _ (E1 · E2) (isEpi_comp E1 E2 (pr2 E1) (pr2 E2)).

  Definition isEpi_precomp {x y z : C} (f : x --> y) (g : y --> z) : isEpi (f · g) -> isEpi g.
  Proof.
    intros X.
intros w φ ψ H.
    apply (maponpaths (λ g', f · g')) in H.
    repeat rewrite assoc in H.
    apply (X w _ _ H).
  Defined.

  Lemma isEpi_path {x y : C} (f1 f2 : x --> y) (e : f1 = f2) (isE : isEpi f1) : isEpi f2.
  Proof.
    induction e.
exact isE.
  Qed.

  Lemma transport_target_isEpi {x y z : C} (f : x --> y) (E : isEpi f) (e : y = z) :
    isEpi (transportf (precategory_morphisms x) e f).
  Proof.
    induction e.
apply E.
  Qed.

End def_epi.
Arguments isEpi [C] [x] [y] _.

Lemma precomp_with_epi_isincl {C : category} {A B : ob C} {f : A --> B} :
  isEpi f -> ∏ c, isincl (@precomp_with _ _ _ f c).
Proof.
  intros is_epi ? ?.
  apply invproofirrelevance.
  intros z w.
  apply subtypePath; [intros ? ?; apply homset_property|].
  apply (is_epi _ (hfiberpr1 _ _ z) (hfiberpr1 _ _ w)).
  exact (hfiberpr2 _ _ z @ !hfiberpr2 _ _ w).
Qed.

Section epis_subcategory.

  Variable C : category.

  Definition hsubtype_obs_isEpi : hsubtype C := (λ c : C, make_hProp _ isapropunit).

  Definition hsubtype_mors_isEpi : ∏ (a b : C), hsubtype (C⟦a, b⟧) :=
    (λ a b : C, (fun f : C⟦a, b⟧ => make_hProp _ (isapropisEpi C C f))).

  Definition subprecategory_of_epis : sub_precategories C.
    use tpair.
    split.
    -
 exact hsubtype_obs_isEpi.
    -
 exact hsubtype_mors_isEpi.
    -
 cbn.
unfold is_sub_precategory.
cbn.
      split.
      +
 intros a tt.
exact (identity_isEpi C).
      +
 apply isEpi_comp.
  Defined.

  Definition has_homsets_subprecategory_of_epis : has_homsets subprecategory_of_epis.
    intros a b.
    apply is_set_sub_precategory_morphisms.
  Qed.

  Definition subprecategory_of_epis_ob (c : C) : ob (subprecategory_of_epis) := tpair _ c tt.

End epis_subcategory.

Section epis_functorcategories.

  Lemma is_nat_trans_epi_from_pointwise_epis (C D : precategory) (hs : has_homsets D)
        (F G : ob (functor_precategory C D hs)) (α : F --> G) (H : ∏ a : ob C, isEpi (pr1 α a)) :
    isEpi α.
  Proof.
    intros G' β η H'.
    use (nat_trans_eq hs).
    intros x.
    set (H'' := nat_trans_eq_pointwise H' x).
cbn in H''.
    apply (H x) in H''.
    exact H''.
  Qed.

End epis_functorcategories.
Module Export Core.

Section HSET_precategory.

Definition hset_fun_space (A B : hSet) : hSet :=
  make_hSet _ (isaset_set_fun_space A B).

Definition hset_precategory_ob_mor : precategory_ob_mor :=
  tpair (λ ob : UU, ob -> ob -> UU) hSet
        (λ A B : hSet, hset_fun_space A B).

Definition hset_precategory_data : precategory_data :=
  make_precategory_data hset_precategory_ob_mor (fun (A:hSet) (x : A) => x)
     (fun (A B C : hSet) (f : A -> B) (g : B -> C) (x : A) => g (f x)).

Lemma is_precategory_hset_precategory_data :
  is_precategory hset_precategory_data.
repeat split.
Qed.

Definition hset_precategory : precategory :=
  tpair _ _ is_precategory_hset_precategory_data.

Local Notation "'HSET'" := hset_precategory : cat.

Lemma has_homsets_HSET : has_homsets HSET.
intros a b; apply isaset_set_fun_space.
Qed.

Definition hset_category : category := (HSET ,, has_homsets_HSET).

End HSET_precategory.

Notation "'HSET'" := hset_category : cat.

Definition emptyHSET : HSET.
  exists nat.
admit.
Defined.

End Core.
Module Export MonoEpiIso.
Import UniMath.MoreFoundations.Tactics.

Local Definition global_element_HSET {A : hSet} (a : A) : HSET⟦unitset, A⟧ :=
  invweq (weqfunfromunit A) a.

Local Definition global_element_HSET_paths_weq {A : hSet} (x y : A) :
  (x = y) ≃ (global_element_HSET x = global_element_HSET y).
Proof.
 admit.
Qed.

Lemma MonosAreInjective_HSET {A B : HSET} (f: HSET ⟦ A, B ⟧) :
      isMonic f ≃ isInjective f.
Proof.
  apply weqimplimpl.
  -
 intro isM.
    apply incl_injectivity; intros b.
    apply invproofirrelevance; intros a1 a2.
    apply subtypePath; [intro; apply setproperty|].
    apply global_element_HSET_paths_weq.
    apply isM.
    apply funextsec; intro t.
admit.
  -
 intro isI.
    unfold isMonic.
    intros ? ? ? eq.
    apply funextfun; intro.
    apply (invweq (Injectivity _ isI _ _)).
    apply toforallpaths in eq.
    apply eq.
  -
 apply isapropisMonic.
  -
 apply isaprop_isInjective.
Qed.

Lemma EpisAreSurjective_HSET {A B : HSET} (f: HSET ⟦ A, B ⟧) :
      isEpi f ≃ issurjective f.
Proof.
  apply weqimplimpl.
  -
 intro epif.
    apply epiissurjectiontosets; [apply setproperty|].
    intros ? ? ? ?.
    apply toforallpaths.
    apply epif.
    now apply funextfun.
  -
 intros is_surj_f.
    intros C g h H.
    apply funextfun; intro.

    specialize (is_surj_f x).
    apply (squash_to_prop is_surj_f); [apply setproperty|].
    intro x'.

    refine (!maponpaths _ (hfiberpr2 _ _ x') @ _).
    refine (_ @ maponpaths _ (hfiberpr2 _ _ x')).

    apply toforallpaths in H.
    apply H.
  -
 apply isapropisEpi.
    apply has_homsets_HSET.
  -
 apply isapropissurjective.
Qed.

Lemma hset_z_iso_is_equiv (A B : ob HSET)
   (f : z_iso A B) : isweq (pr1 f).
  apply (isweq_iso _ (inv_from_z_iso f)).
  -
 intro x.
    set (T:=z_iso_inv_after_z_iso f).
    set (T':=toforallpaths _ _ _ T).
apply T'.
  -
 intro x.
    apply (toforallpaths _ _ _ (z_iso_after_z_iso_inv f)).
Defined.

Lemma hset_z_iso_equiv (A B : ob HSET) : z_iso A B -> (pr1 A) ≃ (pr1 B).
Proof.
  intro f.
  exists (pr1 f).
  apply hset_z_iso_is_equiv.
Defined.

Lemma hset_equiv_is_z_iso (A B : hSet)
      (f : (pr1 A) ≃ (pr1 B)) :
           is_z_isomorphism (C:=HSET) (pr1 f).
Proof.
  exists (invmap f).
  split; simpl.
  -
 apply funextfun; intro x; simpl in *.
    unfold compose, identity; simpl.
    apply homotinvweqweq.
  -
 apply funextfun; intro x; simpl in *.
    unfold compose, identity; simpl.
    apply homotweqinvweq.
Defined.

Lemma hset_equiv_z_iso (A B : ob HSET) : (pr1 A) ≃ (pr1 B) -> z_iso A B.
Proof.
  intro f.
  simpl in *.
  exists (pr1 f).
  apply hset_equiv_is_z_iso.
Defined.

Lemma hset_z_iso_equiv_is_equiv (A B : ob HSET) : isweq (hset_z_iso_equiv A B).
  apply (isweq_iso _ (hset_equiv_z_iso A B)).
  intro; apply eq_z_iso.
  -
 reflexivity.
  -
 intro; apply subtypePath.
    +
 intro; apply isapropisweq.
    +
 reflexivity.
Qed.

Definition hset_z_iso_equiv_weq (A B : ob HSET) : (z_iso A B) ≃ ((pr1 A) ≃ (pr1 B)).
Proof.
  exists (hset_z_iso_equiv A B).
  apply hset_z_iso_equiv_is_equiv.
Defined.

Lemma hset_equiv_z_iso_is_equiv (A B : ob HSET) : isweq (hset_equiv_z_iso A B).
  apply (isweq_iso _ (hset_z_iso_equiv A B)).
  {
 intro f.
    apply subtypePath.
    {
 intro; apply isapropisweq.
}
    reflexivity.
}
  intro; apply eq_z_iso.
  reflexivity.
Qed.

Definition hset_equiv_weq_z_iso (A B : ob HSET) :
  (pr1 A ≃ pr1 B) ≃ z_iso A B.
Proof.
  exists (hset_equiv_z_iso A B).
  apply hset_equiv_z_iso_is_equiv.
Defined.

End MonoEpiIso.
Module Export Univalence.
Import UniMath.Foundations.HLevels.
Import UniMath.CategoryTheory.Core.Univalence.

Definition univalenceweq (X X' : UU) : (X = X') ≃ (X ≃ X') :=
   tpair _ _ (univalenceAxiom X X').

Definition hset_id_weq_z_iso (A B : ob HSET) :
  (A = B) ≃ (z_iso A B) :=
  weqcomp (UA_for_HLevels 2 A B) (hset_equiv_weq_z_iso A B).

Lemma hset_id_weq_iso_is (A B : ob HSET):
    @idtoiso _ A B = pr1 (hset_id_weq_z_iso A B).
Proof.
  apply funextfun.
  intro p; elim p.
  apply eq_z_iso; simpl.
  -
 apply funextfun;
    intro x;
    destruct A.
    apply idpath.
Defined.

Lemma is_weq_precat_paths_to_iso_hset (A B : ob HSET):
   isweq (@idtoiso _ A B).
  rewrite hset_id_weq_iso_is.
  apply (pr2 (hset_id_weq_z_iso A B)).
Defined.

Definition category_HSET : category := make_category HSET has_homsets_HSET.

Lemma is_univalent_HSET : is_univalent category_HSET.
  intros a b.
  apply (is_weq_precat_paths_to_iso_hset a b).
Defined.

Definition HSET_univalent_category : univalent_category := _ ,, is_univalent_HSET.

End Univalence.
Module Export SimplicialSets.

Import UniMath.MoreFoundations.Tactics.
Export UniMath.CategoryTheory.opp_precat.

Local Open Scope stn.

Definition monfunstn ( n m : nat ) : UU := ∑ f : ⟦ n ⟧ -> ⟦ m ⟧, ∏ (x y: ⟦n⟧), x ≤ y -> f x ≤ f y.
Definition make_monfunstn { m n : nat } f is := (f,,is) : monfunstn m n.
Definition monfunstnpr1 {n m : nat} : monfunstn n m  -> ⟦ n ⟧ -> ⟦ m ⟧ := pr1.

Lemma monfunstnpr1_isInjective {m n} (f g : monfunstn m n) : monfunstnpr1 f = monfunstnpr1 g -> f = g.
Proof.
  intros e.
  apply subtypePath.
  {
 intros h.
apply impred; intro i.
apply impred; intro j.
apply impred; intro l.
    apply propproperty.
}
  exact e.
Defined.

Coercion monfunstnpr1 : monfunstn >-> Funclass .

Lemma isasetmonfunstn n m : isaset ( monfunstn n m ) .
  intros .
apply ( isofhleveltotal2 2 ) .
  {
 apply impred.
intro t.
apply isasetstn.
}
  intro f.
apply impred; intro i.
 apply impred; intro j.
apply impred; intro l.
  apply isasetaprop, propproperty.
Defined.

Definition monfunstnid n : monfunstn n n := make_monfunstn (idfun _) (λ x y is, is).

Definition monfunstncomp { n m k : nat } ( f : monfunstn n m ) ( g : monfunstn m k ) :
  monfunstn n k .
  intros .
exists ( g ∘ f ) .
intros i j l.
unfold funcomp.
  apply ( pr2 g ).
apply ( pr2 f ) .
assumption.
Defined.

Definition precatDelta : precategory .
  use tpair.
  {
 use tpair.
    {
 exists nat.
intros m n.
exact (monfunstn (S m) (S n)).
}
    {
 split.
      {
 intros m.
apply monfunstnid.
}
      {
 intros l m n f g.
exact (monfunstncomp f g).
}
 }
 }
  apply is_precategory_one_assoc_to_two.
  simpl.
split.
  {
 simpl.
split.
    {
 intros m n f.
now apply monfunstnpr1_isInjective.
}
    {
 intros m n f.
now apply monfunstnpr1_isInjective.
}
 }
  {
 simpl.
intros m n o p f g h.
now apply monfunstnpr1_isInjective.
}
Defined.

Local Open Scope cat.

Definition has_homsets_precatDelta : has_homsets precatDelta.
  intros a b.
  cbn.
  apply isasetmonfunstn.
Qed.

Definition catDelta : category := make_category precatDelta has_homsets_precatDelta.

Definition sSet := functor_category catDelta^op category_HSET.

End SimplicialSets.

Definition fincard_has_homsets (n m : nat) : isaset ((⟦ n ⟧)%stn -> (⟦ m ⟧)%stn) :=
  (Propositions.funspace_isaset (isasetstn m)).

Proposition iscontr_inequal (n m : nat) : iscontr ((n > m) ⨿ (n ≤ m)).
Proof.
  unfold iscontr.
  exists (natgthorleh n m).
intro t.
  induction t.
  -
 unfold natgthorleh.
    induction (isdecrelnatgth n m).
    +
 simpl.
apply maponpaths.
apply (pr2 (n > m)).
    +
 contradiction.
  -
 unfold natgthorleh.
    induction (isdecrelnatgth n m).
    +
 simpl.
assert (¬ (n > m)).
{
 apply natlehtonegnatgth.
assumption.
}
 contradiction.
    +
 simpl.
apply maponpaths.
apply (pr2 (n ≤ m)).
Defined.

Local Proposition iscontr_inequal' (n m : nat) : iscontr ((n < m) ⨿ (n ≥ m)).
Proof.
  change (n < m) with (m > n).
  change (n ≥ m) with (m ≤ n).
  exact (iscontr_inequal m n).
Defined.

Local Proposition fincard_hom_extensionality { n m : nat } { f g : (⟦ n ⟧)%stn → (⟦ m ⟧)%stn } : (∏ x  : (⟦ n ⟧)%stn, (pr1 (f x)= pr1 (g x))) -> f=g.
Proof.
  intro X.
apply funextfun.
  intro x.
apply subtypeInjectivity_prop.
  exact (X x).
Qed.

Definition ordconstr {n : nat} (k : nat) (bd : k < n) : stn n := k,,bd.

Definition precat_Delta_precategory_data : precategory_data.
  use make_precategory_data.
  -
 exact (make_precategory_ob_mor nat monfunstn).
  -
 intros m.
apply monfunstnid.

  -
  intros l m n f g.
exact (monfunstncomp f g).
Defined.

Definition precat_Delta_is_precategory : is_precategory precat_Delta_precategory_data.
  unfold precat_Delta_precategory_data.
  unfold is_precategory.
split.
{
    split.
    -
 intros a b f.
unfold "id".
simpl in *.
reflexivity.
    -
 intros a b f.
unfold "id".
simpl in *.
reflexivity.
  }
  {
    split.
    -
 reflexivity.
    -
 reflexivity.
  }
Qed.

Definition precat_Delta : precategory :=
  (precat_Delta_precategory_data,, precat_Delta_is_precategory).

Notation "C ⊠ D" := (precategory_binproduct C D) (at level 38).

Definition precat_fincard_data : precategory_data.
  unshelve eapply (make_precategory_data _).
  -
 unshelve eapply (make_precategory_ob_mor _ _).
    *
 exact nat.
    *
 exact (λ n, λ m, (⟦n⟧%stn → ⟦m⟧%stn)).

  -
 intro c.
exact (idfun (⟦c⟧)%stn).

  -
 intros n m k f g.
exact (g∘f).

Defined.

Proposition precat_fincard_is_precategory : is_precategory precat_fincard_data.
  unfold precat_Delta_precategory_data.
  unfold is_precategory.
split.
{
    split.
    -
 intros a b f.
unfold "id".
simpl in *.
reflexivity.
    -
 intros a b f.
unfold "id".
simpl in *.
reflexivity.
  }
  {
    split.
    -
 reflexivity.
    -
 reflexivity.
  }
Qed.

Definition precat_fincard : precategory := (precat_fincard_data,, precat_fincard_is_precategory).

Proposition Delta_has_homsets : has_homsets precat_Delta.
  unfold has_homsets.
simpl.
intros a b.
  apply isaset_total2.
  -
 exact (fincard_has_homsets a b).
  -
 intro f.
apply impred_isaset.
intro x.
apply impred_isaset.
intro y.
apply impred_isaset.
    intro.
exact (isasetaprop (propproperty (f x ≤ f y))).
Qed.

Definition category_Delta : category := (precat_Delta,, Delta_has_homsets).
Definition category_fincard : category := (precat_fincard,, fincard_has_homsets).

Notation Δ_sdg := category_fincard.
Notation Δ := category_Delta.
Notation Δ_sd := category_Delta.

Definition Δ_ob_constr ( n : nat) : Δ := n.
Definition Δ_sdg_ob_constr ( n : nat) : Δ_sdg := n.

Definition Δ_mor_constr { n m : nat } ( f : (⟦ n ⟧)%stn -> (⟦ m ⟧)%stn )
           ( pk : ∏ x y : (⟦ n ⟧)%stn, x ≤ y -> f x ≤ f y) : (Δ_ob_constr n) --> (Δ_ob_constr m)
:= (make_monfunstn f pk).

Definition Δ_sdg_mor_constr { n m : nat } ( f : (⟦ n ⟧)%stn -> (⟦ m ⟧)%stn ) :
  Δ_sdg_ob_constr n -->   Δ_sdg_ob_constr m := f.

Definition fget_monoton_functor_data : functor_data category_Delta category_fincard.
    use tpair.
{
 exact (idfun nat).
}
    intros a b f.
exact (pr1 f).
Defined.

Proposition fget_monoton_is_functor : is_functor fget_monoton_functor_data.
  use tpair.
  -
 unfold functor_idax.
reflexivity.
  -
 unfold functor_compax.
reflexivity.
Qed.

Definition fget_monoton_functor : functor category_Delta category_fincard :=
  (fget_monoton_functor_data,, fget_monoton_is_functor).

Local Notation U := fget_monoton_functor.

Local Proposition U_faithful { a b : Δ } (f g : a --> b) : (# U f = # U g) -> f = g.
Proof.
  apply subtypeInjectivity.
unfold isPredicate.
  intro.
apply impred_isaprop.
  intro.
apply impred_isaprop.
  intro.
apply impred_isaprop.
  intro.
apply propproperty.
Qed.

Local Proposition morphism_extensionality { a b : Δ } (f g : a --> b) :
  (∏ x, (# U f) x  = (# U g) x) -> f = g.
Proof.
  intro ext_hypothesis.
  simpl in ext_hypothesis.
apply U_faithful.
simpl.
  apply fincard_hom_extensionality.
intro x.
apply maponpaths.
exact (ext_hypothesis x).
Qed.

Lemma mon_iso_mon_inv {n m : Δ} {f : n --> m} (I : is_z_isomorphism ((# U) f)) :
  ∏ x y : (⟦m⟧)%stn, x ≤ y -> (is_z_isomorphism_mor I) x ≤ (is_z_isomorphism_mor I) y.
Proof.
  intros x y l.
  unfold is_z_isomorphism in I.
simpl in I.
  induction I as [I_fn I_is_inverse_in_preord], f as [f_fn f_guarantee].
  induction (natlehchoice x y l) as [a | a'].
  -
 induction (natgthorleh (I_fn x) (I_fn y)).
    +

      contradiction (natlthtonegnatgeh x y a).
      assert (∏ z , f_fn (I_fn z) = z) as X.
{
        intro z.
change (f_fn (I_fn z)) with (compose (C:=Δ_sdg) I_fn f_fn z).
        simpl.
set (j := (pr2 I_is_inverse_in_preord)).
simpl in j.
        rewrite j.
reflexivity.
        }
      rewrite <- (X x), <- (X y); apply f_guarantee.
exact (natlthtoleh _ _ a0).
    +
 exact b.
  -
 simpl is_z_isomorphism_mor.
apply subtypeInjectivity_prop in a'.
    induction a'.
exact (isreflnatleh (I_fn x)).
Qed.

Lemma fincard_inv_is_inverse_in_precat (n m : Δ) (f : n --> m ) (I : is_z_isomorphism ((# U) f)):
is_inverse_in_precat f (is_z_isomorphism_mor I,, mon_iso_mon_inv I).
Proof.
  unfold is_z_isomorphism in I.
simpl in I.
  induction I as [g is_inverse], f as [ffun fguarantee].
  simpl in is_inverse.
induction is_inverse as [l r].
  split.
  -
 apply morphism_extensionality.
simpl.
intro x.
    change ((@compose precat_fincard _ _ _ ffun g) x = x).
simpl.
rewrite l.
reflexivity.
  -
 apply morphism_extensionality.
intro x.
simpl.
    change (ffun (g x)) with (compose (C:=Δ_sdg) g ffun x).
    simpl.
rewrite r.
unfold "id".
reflexivity.
Qed.

Lemma U_reflects_isos (n m : Δ) ( f : n --> m ) : (is_z_isomorphism ((# U) f)) -> (is_z_isomorphism f).
Proof.
  intro I.
  use tpair.
{
 exact (is_z_isomorphism_mor I,, mon_iso_mon_inv I).
}
  cbv beta.
  exact (fincard_inv_is_inverse_in_precat n m f I).
Defined.

Local Proposition U_reflects_id (a : Δ) (f : a --> a) :
    (# U f) = id (U a) -> f = id a.
Proof.
  intro.
apply U_faithful.
assumption.
Qed.

Local Definition ordinal_addition : (Δ ⊠ Δ) → Δ.
Proof.
  simpl.
  intro nm.
induction nm as [n m].
exact (n+m).
Defined.
Arguments ordinal_addition /.

Local Definition pr_n_m_l { n m : nat} ( x : (⟦ n + m⟧)%stn ) (s : x < n) : (⟦ n ⟧)%stn.
Proof.
  exists (stntonat _ x).
  exact s.
Defined.

Local Definition pr_n_m_r { n m : nat} ( x : (⟦ n + m⟧)%stn ) (s : x ≥ n) : (⟦ m ⟧)%stn.
Proof.
  exists (stntonat _ x - n).
  apply nat_split.
  -
 exact (stnlt x).
  -
 exact s.
Defined.

Local Definition sumfn {n n' m m' : nat} (f : (⟦ n ⟧)%stn → (⟦ m ⟧)%stn) ( g : (⟦ n' ⟧)%stn → (⟦ m' ⟧)%stn) : (⟦ n + n' ⟧)%stn → (⟦ m + m'⟧)%stn.
Proof.
  intro x.
  induction (natlthorgeh x n) as [less_n | geq_n].
  -
 set (x' := pr_n_m_l x less_n).
    refine (ordconstr (n:=m+m') (stntonat _ (f x')) _).
    apply (natgehgthtrans _ m _).
    +
 exact (natlehnplusnm m m').
    +
 exact (stnlt (f x')).
  -
 set (x' := pr_n_m_r x geq_n).
    refine (ordconstr (stntonat _ (g x')+m) _).
    rewrite natpluscomm.
apply natlthandplusl.
exact (stnlt (g x')).
Defined.

Local Proposition pr_n_m_l_compute { n m : nat}
      ( x : (⟦ n + m⟧)%stn ) (s : x < n) : stntonat _ (pr_n_m_l x s) = stntonat _ x.
Proof.
  reflexivity.
Qed.

Local Proposition pr_n_m_r_compute { n m : nat}
      ( x : (⟦ n + m⟧)%stn ) (s : x ≥ n) : stntonat _ (pr_n_m_r x s) = (stntonat _ x) - n.
Proof.
  reflexivity.
Qed.

Local Proposition proj_incl_l { n m : nat } ( x : (⟦ n + m⟧)%stn ) (s :  x < n) :
  (stn_left n m) (pr_n_m_l x s) = x.
Proof.
  unfold stn_left.
simpl.
  apply subtypeInjectivity_prop.
  reflexivity.
Qed.

Local Proposition proj_incl_r { n m : nat } ( x : (⟦ n + m⟧)%stn ) (s : x ≥ n) :
  (stn_right n m) (pr_n_m_r x s) = x.
Proof.
  unfold stn_right.
simpl.
  apply subtypeInjectivity_prop.
  simpl.
  rewrite natpluscomm.
exact (minusplusnmm x n s).
Qed.

Definition natlthorgeh_left_branch {n m : nat} (s : n < m) (j : (n < m) ⨿ (n ≥ m)) : j = inl s
  := (proofirrelevancecontr (iscontr_inequal m n) j (inl s)).
Definition natlthorgeh_right_branch {n m : nat} (s : n ≥ m) (j : (n < m) ⨿ (n ≥ m)) : j = inr s
  := (proofirrelevancecontr (iscontr_inequal m n) j (inr s)).

Local Proposition sumfn_l { n n' m m' : nat}
      (f : (⟦ n ⟧)%stn -> (⟦ m ⟧)%stn) ( g : (⟦ n' ⟧)%stn -> (⟦ m' ⟧)%stn)
      (x : (⟦ n + n' ⟧)%stn) ( s : x < n) : (sumfn f g) x < m.
Proof.
  unfold sumfn.
  rewrite (natlthorgeh_left_branch s _).
  simpl.
  exact (stnlt (f (pr_n_m_l x s))).
Qed.

Local Proposition sumfn_r { n n' m m' : nat }
      (f : (⟦ n ⟧)%stn -> (⟦ m ⟧)%stn) (g : (⟦ n' ⟧)%stn -> (⟦ m' ⟧)%stn)
      (x : (⟦ n + n' ⟧)%stn) ( s : x ≥ n) : (sumfn f g) x ≥ m.
Proof.
  unfold sumfn.
rewrite (natlthorgeh_right_branch s _).
  simpl.
change (g (pr_n_m_r x s) + m ≥ m).
exact (natlehmplusnm _ m).
Qed.

Local Proposition sumfn_l1 { n n' m m' : nat}
      (f : (⟦ n ⟧)%stn -> (⟦ m ⟧)%stn) ( g : (⟦ n' ⟧)%stn -> (⟦ m' ⟧)%stn)
      (x : (⟦ n + n' ⟧)%stn) ( s : x < n) :
  f (pr_n_m_l x s) = pr_n_m_l ((sumfn f g) x) (sumfn_l f g x s).
Proof.
  apply subtypeInjectivity_prop.
  simpl.
unfold sumfn.
rewrite (natlthorgeh_left_branch s _).
  simpl.
reflexivity.
Qed.

Local Proposition sumfn_r1 { n n' m m' : nat}
      (f : (⟦ n ⟧)%stn -> (⟦ m ⟧)%stn) (g : (⟦ n' ⟧)%stn -> (⟦ m' ⟧)%stn)
      (x : (⟦ n + n' ⟧)%stn) ( s :x ≥ n) :
  g (pr_n_m_r x s) = pr_n_m_r ((sumfn f g) x) (sumfn_r f g x s).
Proof.
  apply subtypeInjectivity_prop.
  simpl.
unfold sumfn.
rewrite (natlthorgeh_right_branch s _).
  simpl.
rewrite ( plusminusnmm _ m).
reflexivity.
Qed.

Local Proposition sumfn_l2 { n n' m m' : nat}
      (f : (⟦ n ⟧)%stn -> (⟦ m ⟧)%stn) ( g : (⟦ n' ⟧)%stn -> (⟦ m' ⟧)%stn)
      (x : (⟦ n + n' ⟧)%stn) ( s : x < n) :
  (stn_left m m') (f (pr_n_m_l x s)) = (sumfn f g) x.
Proof.
  rewrite (sumfn_l1 f g x s).
exact (proj_incl_l (sumfn f g x) (sumfn_l f g x s)).
Qed.

Local Proposition sumfn_r2 { n n' m m' : nat}
      (f : (⟦ n ⟧)%stn -> (⟦ m ⟧)%stn) ( g : (⟦ n' ⟧)%stn -> (⟦ m' ⟧)%stn)
      (x : (⟦ n + n' ⟧)%stn) ( s : x ≥ n) :
  (stn_right m m') (g (pr_n_m_r x s)) = (sumfn f g) x.
Proof.
  rewrite (sumfn_r1 f g x s).
exact (proj_incl_r (sumfn f g x) (sumfn_r f g x s)).
Qed.

Local Proposition stn_left_monotonic ( n m : nat ) :
  ∏ x y : (⟦ n ⟧)%stn, (x ≤ y) -> ( stn_left n m x ) ≤ ( stn_left n m y).
Proof.
  intros x y l.
  exact l.
Qed.

Local Proposition stn_right_monotonic ( n m : nat ) :
  ∏ x y : (⟦ m ⟧)%stn, (x ≤ y) -> ( stn_right n m x ) ≤ ( stn_right n m y).
Proof.
  intros x y l.
simpl.
  change (n + x ≤ n + y).
  rewrite natpluscomm.
rewrite (natpluscomm n y).
apply natlehandplusr.
  exact l.
Qed.

Definition monfunmonprop { n m : nat } (f : monfunstn n m) := pr2 f.

Local Arguments precategory_binproduct_mor /.

Local Definition ordinal_hom :
  ∏ a b : ob (Δ ⊠ Δ), a --> b -> (ordinal_addition a) --> (ordinal_addition b).
Proof.
  simpl.
intros nn' mm'.
induction nn' as [n n'], mm' as [m m'].
  intro fg.
simpl in fg.
induction fg as [f g].
  unshelve refine (make_monfunstn _ _).
  -
 exact (sumfn f g).
  -
 intros x y.
    induction f as [f_fun f_guarantee].
induction g as [g_fun g_guarantee].
    intro l.
simpl.
change (sumfn f_fun g_fun x ≤ sumfn f_fun g_fun y).
    unfold sumfn.
    induction natlthorgeh as [xl | xgth], (natlthorgeh y n) as [yl | ygth].
    +
 simpl.
exact (f_guarantee (pr_n_m_l x xl) (pr_n_m_l y yl) l).
    +
 simpl.
apply natlthtoleh.
apply (natgehgthtrans _ m _ ).
      *
 exact (natlehmplusnm _ m).
      *
 exact (stnlt (f_fun _)).
    +
 contradiction (natgthnegleh yl).
exact (istransnatleh xgth l).
    +
 simpl.
change (g_fun (pr_n_m_r x xgth) + m ≤ g_fun (pr_n_m_r y ygth) +m ).
      apply natlehandplusr.
apply g_guarantee.
rewrite pr_n_m_r_compute.
      rewrite pr_n_m_r_compute.
exact (natgehandminusr _ _ n l).
Defined.

Local Definition tensor_data_card : (functor_data (Δ_sdg ⊠ Δ_sdg) Δ_sdg).
Proof.
  use functor_data_constr.
  +
 exact ordinal_addition.
  +
 intros a b pr.
induction pr as [f g].
exact (sumfn f g).
Defined.

Local Definition tensor_data_ord : (functor_data (Δ ⊠ Δ)  Δ).
Proof.
use functor_data_constr.
       +
 exact ordinal_addition.
       +
 exact ordinal_hom.
Defined.

Local Proposition tensor_id_card : (functor_idax tensor_data_card).
  intro a.
induction a as [n m].
simpl.
unfold sumfn.
apply fincard_hom_extensionality.
  intro x.
  induction natlthorgeh.
  -
 simpl.
unfold "id".
reflexivity.
  -
 simpl.
unfold "id".
simpl.
exact (minusplusnmm x n b).
Qed.

Local Proposition tensor_id_ord : (functor_idax tensor_data_ord).
  intro a.
  apply U_reflects_id.
unfold tensor_data_ord.
  apply (tensor_id_card).
Qed.

Local Proposition tensor_comp_card : (functor_compax tensor_data_card).
  unfold functor_compax.
unfold tensor_data_card.
simpl.
  intros a b c f g.
  induction a as [a0 a1], b as [b0 b1], c as [c0 c1].
  simpl in f, g.
induction f as [f0 f1], g as [g0 g1].

  apply fincard_hom_extensionality.
simpl.
intro x.
  unfold "·".
simpl.
unfold sumfn.

  induction natlthorgeh.
  -
 rewrite (natlthorgeh_left_branch (stnlt (f0 (ordconstr x a) )) _).
simpl in *.
    apply maponpaths.
apply maponpaths.
    apply subtypeInjectivity_prop.
                              reflexivity.
  -
 rewrite (natlthorgeh_right_branch (natgehplusnmm _ b0) _).
simpl in *.
    apply (maponpaths (λ k : nat, k+c0)).
apply maponpaths.
apply maponpaths.
    apply subtypeInjectivity_prop.
                              simpl.
exact (pathsinv0 (plusminusnmm _ b0)).
Qed.

Local Proposition tensor_comp_ord : (functor_compax tensor_data_ord).
  unfold functor_compax, tensor_data_ord.
intros a b c f g.
  induction f as [f0 f1], g as [g0 g1].
  set (Uf := make_dirprod (# U f0) (# U f1)).
  set (Ug := make_dirprod (# U g0) (# U g1)).
  apply U_faithful.
exact (tensor_comp_card a b c Uf Ug).
Qed.

Local Proposition tensor_card_is_functor : is_functor tensor_data_card.
  split.
  exact tensor_id_card.
  exact tensor_comp_card.
Qed.

Local Proposition tensor_ord_is_functor : is_functor tensor_data_ord.
  split.
  exact tensor_id_ord.
  exact tensor_comp_ord.
Qed.

Local Definition tensor_functor_card : functor (Δ_sdg ⊠ Δ_sdg) Δ_sdg.
Proof.
use make_functor.
       +
 exact tensor_data_card.
       +
 exact tensor_card_is_functor.
Defined.

Local Definition tensor_functor_ord : functor (Δ ⊠ Δ) Δ.
Proof.
use make_functor.
       +
 exact tensor_data_ord.
       +
 exact tensor_ord_is_functor.
Defined.

Local Definition tensor_unit : Δ :=0.
Arguments tensor_unit /.

Local Definition tensor_left_unitor_card : left_unitor tensor_functor_card tensor_unit.
  unfold left_unitor, I_pretensor, functor_fix_fst_arg,functor_identity,nat_z_iso.

  use tpair.
  -
 unfold "⟹".
use tpair.
    +
 unfold nat_trans_data.
intro x.
exact (id x).
    +
 admit.
  -
 cbv beta.

    unfold is_nat_z_iso, is_z_isomorphism, is_inverse_in_precat.
    intro c.
exists (id c).
admit.
Defined.

Local Definition tensor_left_unitor_ord : left_unitor tensor_functor_ord tensor_unit.
  unfold left_unitor, I_pretensor, functor_fix_fst_arg,functor_identity,nat_z_iso.

  use tpair.
  -
 unfold "⟹".
use tpair.
    +
 unfold nat_trans_data.
intro n.
exact (id n).
    +
 admit.
  -
 cbv beta;
    unfold is_nat_z_iso; intro c; unfold is_z_isomorphism.
    exists (id c).
admit.
Defined.

Local Definition tensor_right_unitor_card_nt_data : nat_trans_data (I_posttensor tensor_functor_card tensor_unit) (functor_identity Δ_sdg).
  simpl.
unfold "⟹".
unfold nat_trans_data.
simpl.
intro x.
      unfold functor_fix_snd_arg_ob, tensor_functor_card, tensor_unit.
simpl.
      rewrite natplusr0.
exact (idfun _).
Defined.

Local Definition tensor_right_unitor_card_is_nat_trans : is_nat_trans (I_posttensor tensor_functor_card tensor_unit) (functor_identity Δ_sdg) tensor_right_unitor_card_nt_data.
  unfold is_nat_trans, tensor_right_unitor_card_nt_data.
simpl.
  intros n m f.
unfold functor_fix_snd_arg_mor; simpl.
  apply fincard_hom_extensionality; unfold functor_fix_snd_arg_ob; simpl.
  intro x.
  unfold "·"; simpl.
 unfold sumfn.
  assert (x < n) as j.
{
 simpl; induction (natplusr0 n); exact (stnlt x).
}
  rewrite (natlthorgeh_left_branch j _).
simpl.
  generalize (natgehgthtrans (m+0) m), (! natplusr0 m).
intros h p.
  intermediate_path (pr1 (f (ordconstr x j))).
  -
 induction (natplusr0 m).
 reflexivity.
  -
 apply maponpaths, maponpaths, subtypeInjectivity_prop;
      simpl; induction (natplusr0 n); reflexivity.
Qed.

Local Definition tensor_right_unitor_card : right_unitor tensor_functor_card tensor_unit.
  use tpair.
{
 exact (tensor_right_unitor_card_nt_data,,tensor_right_unitor_card_is_nat_trans).
 }
  cbv beta.
  unfold is_nat_z_iso, is_z_isomorphism.
simpl.
intro c.
  use tpair.
    +
  simpl.
unfold functor_fix_snd_arg_ob, tensor_functor_card.
simpl.
       rewrite natplusr0.
exact (idfun _).
    +
 admit.
Defined.

Local Definition tensor_right_unitor_ord_nt_data : nat_trans_data (I_posttensor tensor_functor_ord tensor_unit) (functor_identity Δ_sd).
  unfold nat_trans_data.
intro n.
use make_monfunstn.
  *
 simpl.
unfold functor_fix_snd_arg_ob, tensor_functor_ord.
  simpl.
rewrite natplusr0.
exact (idfun _).
  *
 cbv beta.
intros x y leq.
induction (natplusr0 n).
exact leq.
Defined.

Arguments tensor_right_unitor_ord_nt_data /.

Local Definition tensor_right_unitor_ord_is_nat_trans : is_nat_trans (I_posttensor tensor_functor_ord tensor_unit) (functor_identity Δ_sd) tensor_right_unitor_ord_nt_data.
  unfold is_nat_trans.
intros n m f.
      apply U_faithful.
rewrite (functor_comp U).
simpl.
      unfold "·".
simpl.
      apply fincard_hom_extensionality.
      unfold functor_fix_snd_arg_ob, tensor_functor_ord.
simpl.
      induction (natplusr0 m).
simpl.
intro x.

      unfold sumfn.
      assert (x < n) as xbd.
{
 simpl in *.
induction (pathsinv0 (natplusr0 n)).
exact (stnlt x).
}
      rewrite (natlthorgeh_left_branch xbd _).
simpl.
      apply maponpaths.
apply maponpaths.
apply subtypeInjectivity_prop.
      induction (natplusr0 n).
simpl.
reflexivity.
Qed.

Local Proposition tensor_right_unitor_ord : right_unitor tensor_functor_ord tensor_unit.
  unfold right_unitor.
  use tpair.
{
 exact (tensor_right_unitor_ord_nt_data,,tensor_right_unitor_ord_is_nat_trans).
}
  cbv beta.
unfold is_nat_z_iso.
simpl.
intro c.
unfold is_z_isomorphism.
  use tpair.
{
 simpl.
unfold functor_fix_snd_arg_ob.
simpl.
               rewrite natplusr0.
exact (monfunstnid c).
}
  {
 admit.
  }
Defined.

Definition tensor_associator_card_nat_trans_data : nat_trans_data (assoc_left tensor_functor_card) (assoc_right tensor_functor_card).
  unfold nat_trans_data.
simpl.
induction x as [nm k], nm as [n m].
   simpl.
rewrite natplusassoc.
exact (idfun _).
Defined.

Arguments tensor_associator_card_nat_trans_data /.

Definition tensor_associator_card_is_nat_trans : is_nat_trans _ _ tensor_associator_card_nat_trans_data.
  unfold is_nat_trans.
simpl.
  induction x as [nm k], nm as [n m], x' as [n'm' k'], n'm' as [n' m'].
  simpl.
induction f as [fg h], fg as [f g].
  unfold "·".
simpl.
  apply fincard_hom_extensionality.
simpl.
  induction x as [xval xbd].
  simpl.
induction (natplusassoc n' m' k').
simpl.

  unfold sumfn.
simpl.

  set (QQ := internal_paths_rew_r nat (n + m + k ) (n + (m + k )) _ _ _).
