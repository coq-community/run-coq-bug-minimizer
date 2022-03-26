(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "-deprecated-native-compiler-option" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/category_theory" "Category" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Equations" "Equations" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-top" "Closed" "-native-compiler" "no") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 182 lines to 46 lines, then from 59 lines to 165 lines, then from 170 lines to 62 lines, then from 75 lines to 256 lines, then from 261 lines to 71 lines, then from 84 lines to 324 lines, then from 329 lines to 216 lines *)
(* coqc version 8.16+alpha compiled with OCaml 4.05.0
   coqtop version runner-jhcjxvh-project-6138686-concurrent-0:/builds/coq/coq/_build/default,(HEAD detached at c0c74d7) (c0c74d7d15ff944b450701a74f34d8ceb9505546)
   Expected coqc runtime on this file: 9.374 sec *)
Require Coq.Init.Datatypes.
Require Coq.Program.Program.
Require Category.Lib.Foundation.
Require Coq.Classes.CEquivalence.
Require Coq.Classes.CRelationClasses.
Require Coq.Classes.CMorphisms.
Require Category.Lib.Setoid.
Require Coq.Bool.Bool.
Require Category.Lib.Tactics.
Require Coq.NArith.NArith.
Require Coq.Lists.List.
Require Category.Lib.Datatypes.
Require Category.Lib.
Require Category.Theory.Category.
Require Category.Theory.Morphisms.
Require Category.Theory.Isomorphism.
Require Category.Structure.Terminal.
Require Category.Structure.Cartesian.
Require Category.Construction.Opposite.
Require Category.Structure.Initial.
Require Category.Theory.Functor.
Require Category.Theory.Functor.Endo.
Require Category.Theory.Naturality.
Require Category.Construction.Product.
Require Category.Functor.Bifunctor.
Require Category.Structure.Monoidal.
Require Category.Instance.Sets.
Require Category.Structure.Cartesian.Closed.
Require Category.Theory.Natural.Transformation.

Declare ML Module "coq-core.plugins.ltac".
Module Export AdmitTactic.
Module Import LocalFalse.
Inductive False : Prop := .
End LocalFalse.
Axiom proof_admitted : False.
Global Set Default Proof Mode "Classic".
Tactic Notation "admit" := abstract case proof_admitted.
End AdmitTactic.

Module Export Category_DOT_Instance_DOT_Fun_WRAPPED.
Module Export Fun.
Set Warnings "-notation-overridden".
Set Warnings "-deprecated-hint-without-locality".
Import Category.Lib.
Export Category.Theory.Natural.Transformation.
Import Category.Instance.Sets.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Fun.

Context {C : Category}.
Context {D : Category}.

 

Global Program Definition Fun : Category := {|
  obj     := C ⟶ D;
  hom     := @Transform C D;
  id      := @nat_id C D;
  compose := @nat_compose C D;

  compose_respects := @nat_compose_respects C D
|}.

End Fun.

Notation "[ C , D ]" := (@Fun C D)
  (at level 90, right associativity, format "[ C ,  D ]") : category_scope.

Notation "[[[ C , D ]]]( F , G )" := ({| carrier   := @hom (@Fun C D) F G
                                       ; is_setoid := @homset (@Fun C D) F G |})
  (at level 90, right associativity, format "[[[ C ,  D ]]]( F , G )") : homset_scope.

Corollary nat_id_left C D (F G : C ⟶ D) (N : F ⟹ G) :
  nat_id ∙ N ≈[Fun] N.
Admitted.

Corollary nat_id_right C D (F G : C ⟶ D) (N : F ⟹ G) :
  N ∙ nat_id ≈[Fun] N.
Admitted.

Corollary nat_comp_assoc C D (F G H J : C ⟶ D)
          (M : H ⟹ J) (N : G ⟹ H) (O : F ⟹ G) :
  M ∙ (N ∙ O) ≈[Fun] (M ∙ N) ∙ O.
Admitted.

Lemma whisker_right_id A B C (F : A ⟶ B) (G : B ⟶ C) : id{Fun} ⊲ F ≈ id{Fun}.
Admitted.

Lemma whisker_left_id A B C (F : A ⟶ B) (G : B ⟶ C) : G ⊳ id{Fun} ≈ id{Fun}.
Admitted.

Lemma whisker_left_dist A B C (F : A ⟶ B) (G H J : B ⟶ C)
      (η : G ⟹ H) (θ : H ⟹ J) : (θ ⊲ F) ∙ (η ⊲ F) ≈ (θ ∙ η) ⊲ F.
Admitted.

Lemma whisker_right_dist A B C (F G H : A ⟶ B) (J : B ⟶ C)
      (η : F ⟹ G) (θ : G ⟹ H) : (J ⊳ θ) ∙ (J ⊳ η) ≈ J ⊳ (θ ∙ η).
Admitted.

Lemma nat_λ {A B} (F : A ⟶ B) : F ◯ Id ≅[Fun] F.
Admitted.

Lemma nat_ρ {A B} (F : A ⟶ B) : Id ◯ F ≅[Fun] F.
Admitted.

Lemma nat_α {A B C D} (F : A ⟶ B) (G : B ⟶ C) (H : C ⟶ D) :
  H ◯ (G ◯ F) ≅[Fun] (H ◯ G) ◯ F.
Admitted.

Lemma whisker_left_right A B C (F G : A ⟶ B) (H J : B ⟶ C)
      (η : F ⟹ G) (θ : H ⟹ J) :
  (J ⊳ η) ∙ (θ ⊲ F) ≈ (θ ⊲ G) ∙ (H ⊳ η).
Admitted.

Lemma whisker_flip A B C (F : A ⟶ B) (G : B ⟶ C) :
  (to (nat_λ G) ⊲ F) ∙ to (nat_α F Id G) ≈ G ⊳ (to (nat_ρ F)).
Admitted.

Lemma nat_α_whisker_right_comp
      A B C D (F : A ⟶ B) (G : B ⟶ C) (H J : C ⟶ D) (η : H ⟹ J) :
  to (nat_α F G J) ∙ η ⊲ (G ◯ F) ≈ (η ⊲ G) ⊲ F ∙ to (nat_α F G H).
Admitted.

Lemma nat_α_whisker_left_comp
      A B C D (F G : A ⟶ B) (H : B ⟶ C) (J : C ⟶ D) (η : F ⟹ G) :
  to (nat_α G H J) ∙ J ⊳ (H ⊳ η) ≈ (J ◯ H) ⊳ η ∙ to (nat_α F H J).
Admitted.

Lemma nat_α_whisker_assoc
      A B C D (F : A ⟶ B) (G H : B ⟶ C) (J : C ⟶ D) (η : G ⟹ H) :
  to (nat_α F H J) ∙ J ⊳ (η ⊲ F) ≈ (J ⊳ η) ⊲ F ∙ to (nat_α F G J).
Admitted.

Lemma nat_α_nat_α A B C D E (F : A ⟶ B) (G : B ⟶ C) (H : C ⟶ D) (J : D ⟶ E) :
  (to (nat_α G H J) ⊲ F ∙ to (nat_α F (H ◯ G) J)) ∙ (J ⊳ (to (nat_α F G H)))
    ≈ to (nat_α F G (J ◯ H)) ∙ to (nat_α (G ◯ F) H J).
Admitted.

Class Pointed {C : Category} (F : C ⟶ C) := {
  point : Id ⟹ F
}.

End Fun.
Set Universe Polymorphism.

Program Instance Cat : Category := {
  obj     := Category;
  hom     := @Functor;
  homset  := @Functor_Setoid;
  id      := @Id;
  compose := @Compose;

  compose_respects := @Compose_respects
}.
Export Category.Structure.Cartesian.
Export Category.Construction.Product.

Program Instance Cat_Cartesian : @Cartesian Cat := {
  product_obj := @Product;
  fork := fun _ _ _ F G =>
            {| fobj := fun x => (F x, G x)
             ; fmap := fun _ _ f => (fmap[F] f, fmap[G] f) |};
  exl := fun _ _ =>
            {| fobj := fst
             ; fmap := fun _ _ => fst |};
  exr := fun _ _ =>
            {| fobj := snd
             ; fmap := fun _ _ => snd |};
}.
Admit Obligations.
Import Category.Lib.
Export Category.Structure.Cartesian.Closed.

Program Instance Cat_Closed : @Closed Cat Cat_Cartesian := {
  exponent_obj := @Fun;
  exp_iso := fun A B C =>
    {| to :=
       {| morphism := fun F : A × B ⟶ C =>
          {| fobj := fun x : A =>
             {| fobj := fun y : B => F (x, y)
              ; fmap := fun J K (f : J ~{B}~> K) =>
                  fmap[F] (@id A x, f) |}
           ; fmap := fun J K (f : J ~{A}~> K) =>
             {| transform := fun L : B =>
                  fmap[F] (f, @id B L) |} |} |}
     ; from :=
       {| morphism := fun F : A ⟶ [B, C] =>
          {| fobj := fun x : A × B => F (fst x) (snd x)
           ; fmap := fun J K (f : J ~{A × B}~> K) =>
               fmap (snd f) ∘ transform[fmap[F] (fst f)] _ |} |} |}
}.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
  proper.
  rewrite H.
