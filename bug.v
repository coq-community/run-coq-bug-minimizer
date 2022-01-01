(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "-deprecated-native-compiler-option" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/category_theory" "Category" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Equations" "Equations" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-top" "bug_01" "-native-compiler" "no") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 182 lines to 48 lines, then from 61 lines to 167 lines, then from 172 lines to 75 lines, then from 88 lines to 269 lines, then from 274 lines to 84 lines, then from 97 lines to 337 lines, then from 342 lines to 85 lines, then from 98 lines to 85 lines, then from 98 lines to 85 lines, then from 98 lines to 85 lines, then from 98 lines to 85 lines, then from 98 lines to 85 lines, then from 98 lines to 85 lines *)
(* coqc version 8.15+alpha compiled with OCaml 4.05.0
   coqtop version runner-0277ea0f-project-6138686-concurrent-0:/builds/coq/coq/_build/default,(HEAD detached at 0d1a2eb) (0d1a2eb7ba6a7719f37495807fb9fa49623ac075)
   Expected coqc runtime on this file: 18.171 sec *)
Require Category.Structure.Cartesian.Closed.
Require Category.Theory.Natural.Transformation.
Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.
Export Category.Theory.Natural.Transformation.

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
Next Obligation.
admit.
Defined.
Next Obligation.
admit.
Defined.
Next Obligation.
admit.
Defined.
Next Obligation.
admit.
Defined.
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
Admit Obligations.
