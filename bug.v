(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "-deprecated-native-compiler-option" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/category_theory" "Category" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Equations" "Equations" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-top" "Top.bug_01" "-native-compiler" "no") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 255 lines to 43 lines, then from 56 lines to 364 lines, then from 369 lines to 54 lines, then from 67 lines to 188 lines, then from 193 lines to 74 lines, then from 87 lines to 179 lines, then from 185 lines to 82 lines, then from 95 lines to 219 lines, then from 224 lines to 120 lines, then from 133 lines to 269 lines, then from 274 lines to 169 lines, then from 171 lines to 133 lines, then from 146 lines to 252 lines, then from 257 lines to 158 lines, then from 171 lines to 269 lines, then from 274 lines to 180 lines, then from 193 lines to 516 lines, then from 521 lines to 248 lines, then from 261 lines to 362 lines, then from 367 lines to 312 lines, then from 325 lines to 523 lines, then from 528 lines to 421 lines, then from 432 lines to 406 lines, then from 419 lines to 535 lines, then from 540 lines to 459 lines, then from 472 lines to 816 lines, then from 821 lines to 669 lines, then from 668 lines to 456 lines, then from 469 lines to 726 lines, then from 731 lines to 594 lines, then from 594 lines to 482 lines, then from 495 lines to 767 lines, then from 772 lines to 553 lines, then from 566 lines to 593 lines, then from 598 lines to 556 lines *)
(* coqc version 8.18+alpha compiled with OCaml 4.09.0
   coqtop version runner-htnstaz1-project-6138686-concurrent-0:/builds/coq/coq/_build/default,(HEAD detached at fd69eda) (fd69edad0ac6cff8cb0cad43426d6b7b44adc0f8)
   Expected coqc runtime on this file: 30.276 sec *)
Require Category.Lib.Datatypes.
#[export] Set Primitive Projections.
#[export] Set Universe Polymorphism.
Export Category.Lib.Datatypes.
Module Export Category_DOT_Lib.
Module Export Category.
Module Export Lib.
End Lib.

End Category.

End Category_DOT_Lib.

Module Export Category_DOT_Theory_DOT_Category_WRAPPED.
Module Export Category.

Reserved Infix "~>" (at level 90, right associativity).

Class Category@{o h p | h <= p} : Type@{max(o+1,h+1,p+1)} := {
  obj : Type@{o};

  uhom := Type@{h} : Type@{h+1};
  hom : obj → obj → uhom where "a ~> b" := (hom a b);
  homset : ∀ X Y, Setoid@{h p} (X ~> Y);

  id {x} : x ~> x;
  compose {x y z} (f: y ~> z) (g : x ~> y) : x ~> z
    where "f ∘ g" := (compose f g);

  compose_respects {x y z} :
    Proper@{h p} (respectful@{h p h p h p} equiv
                    (respectful@{h p h p h p} equiv equiv))
      (@compose x y z);

  dom {x y} (f : x ~> y) := x;
  cod {x y} (f : x ~> y) := y;

  id_left  {x y} (f : x ~> y) : id ∘ f ≈ f;
  id_right {x y} (f : x ~> y) : f ∘ id ≈ f;

  comp_assoc {x y z w} (f : z ~> w) (g : y ~> z) (h : x ~> y) :
    f ∘ (g ∘ h) ≈ (f ∘ g) ∘ h;
  comp_assoc_sym {x y z w} (f : z ~> w) (g : y ~> z) (h : x ~> y) :
    (f ∘ g) ∘ h ≈ f ∘ (g ∘ h)
}.
#[export] Existing Instance homset.
#[export] Existing Instance compose_respects.
Bind Scope object_scope with obj.

Delimit Scope category_scope with category.
Delimit Scope object_scope with object.
Delimit Scope homset_scope with homset.
Delimit Scope morphism_scope with morphism.

Notation "x ~> y" := (@hom _%category x%object y%object)
  (at level 90, right associativity) : homset_scope.
Notation "x ~{ C }~> y" := (@hom C%category x%object y%object)
  (at level 90) : homset_scope.

Notation "id[ x ]" := (@id _%category x%object)
  (at level 9, format "id[ x ]") : morphism_scope.

Notation "f ∘ g" :=
  (@compose _%category _%object _%object _%object f%morphism g%morphism)
  : morphism_scope.

Notation "f << A ~~> B >> g" :=
  (@equiv (A%object ~> B%object)%homset _ f%morphism g%morphism)
  (at level 99, A at next level, B at next level, only parsing) : category_theory_scope.

Coercion obj : Category >-> Sortclass.
Open Scope homset_scope.
Open Scope morphism_scope.

End Category.

End Category_DOT_Theory_DOT_Category_WRAPPED.

Generalizable All Variables.

Section Isomorphism.

Universes o h p.
Context {C : Category@{o h p}}.

Class Isomorphism (x y : C) : Type := {
  to   : x ~> y;
  from : y ~> x;

  iso_to_from : to ∘ from ≈ id;
  iso_from_to : from ∘ to ≈ id
}.

End Isomorphism.

Declare Scope isomorphism_scope.
Open Scope isomorphism_scope.

Notation "x ≅ y" := (@Isomorphism _%category x%object y%object)
  (at level 91) : isomorphism_scope.
Arguments from {_%category x%object y%object} _%morphism.
Arguments iso_to_from {_ _ _} _.

Coercion to : Isomorphism >-> hom.

Notation "f '⁻¹'" := (from f) (at level 9, format "f '⁻¹'") : morphism_scope.

Class Functor@{o1 h1 p1 o2 h2 p2}
  {C : Category@{o1 h1 p1}} {D : Category@{o2 h2 p2}} := {
  fobj : C → D;
  fmap {x y : C} (f : x ~> y) : fobj x ~> fobj y;

  fmap_respects : ∀ x y,
    Proper@{h2 p2} (respectful@{h1 p1 h2 p2 h2 p2}
                      equiv@{h1 p1} equiv@{h2 p2}) (@fmap x y);

  fmap_id {x : C} : fmap (@id C x) ≈ id;
  fmap_comp {x y z : C} (f : y ~> z) (g : x ~> y) :
    fmap (f ∘ g) ≈ fmap f ∘ fmap g
}.
Declare Scope functor_type_scope.
Delimit Scope functor_scope with functor.
Open Scope functor_type_scope.

Coercion fobj : Functor >-> Funclass.

Notation "C ⟶ D" := (@Functor C%category D%category)
  (at level 90, right associativity) : functor_type_scope.
Notation "fmap[ F ]" := (@fmap _ _ F%functor _ _)
  (at level 9, format "fmap[ F ]") : morphism_scope.
Definition Product (C D : Category) : Category.
exact ({|
  obj     := C * D;
  hom     := fun x y => (fst x ~> fst y) * (snd x ~> snd y);
  homset  := fun x y =>
    let setoid_C := @homset C (fst x) (fst y) in
    let setoid_D := @homset D (snd x) (snd y) in
    {| equiv := fun f g =>
         (@equiv _ setoid_C (fst f) (fst g) *
          @equiv _ setoid_D (snd f) (snd g))
     ; setoid_equiv := _
         {| Equivalence_Reflexive  := fun x =>
              (@Equivalence_Reflexive _ _ (@setoid_equiv _ setoid_C) (fst x),
               @Equivalence_Reflexive _ _ (@setoid_equiv _ setoid_D) (snd x))
          ; Equivalence_Symmetric  := fun x y f =>
              (@Equivalence_Symmetric
                 _ _ (@setoid_equiv _ setoid_C) (fst x) (fst y) (fst f),
               @Equivalence_Symmetric
                 _ _ (@setoid_equiv _ setoid_D) (snd x) (snd y) (snd f))
          ; Equivalence_Transitive := fun x y z f g =>
              (@Equivalence_Transitive
                 _ _ (@setoid_equiv _ setoid_C) (fst x) (fst y) (fst z)
                 (fst f) (fst g),
               @Equivalence_Transitive
                 _ _ (@setoid_equiv _ setoid_D) (snd x) (snd y) (snd z)
                 (snd f) (snd g)) |} |};
  id      := fun _ => (id, id);
  compose := fun _ _ _ f g => (fst f ∘ fst g, snd f ∘ snd g);

  compose_respects := fun x y z f g fg h i hi =>
    (compose_respects (fst f) (fst g) (fst fg) (fst h) (fst i) (fst hi),
     compose_respects (snd f) (snd g) (snd fg) (snd h) (snd i) (snd hi));

  id_left  := fun x y f =>
    (@id_left C (fst x) (fst y) (fst f),
     @id_left D (snd x) (snd y) (snd f));
  id_right := fun x y f =>
    (@id_right C (fst x) (fst y) (fst f),
     @id_right D (snd x) (snd y) (snd f));

  comp_assoc := fun x y z w f g h =>
    (@comp_assoc C (fst x) (fst y) (fst z) (fst w) (fst f) (fst g) (fst h),
     @comp_assoc D (snd x) (snd y) (snd z) (snd w) (snd f) (snd g) (snd h));
  comp_assoc_sym := fun x y z w f g h =>
    (@comp_assoc_sym C (fst x) (fst y) (fst z) (fst w) (fst f) (fst g) (fst h),
     @comp_assoc_sym D (snd x) (snd y) (snd z) (snd w) (snd f) (snd g) (snd h))
|}).
Defined.

Notation "C ∏ D" := (@Product C D) (at level 90) : category_scope.

Section Bifunctor.

Context {C : Category}.
Context {D : Category}.
Context {E : Category}.
Definition bimap {F : C ∏ D ⟶ E} {x w : C} {y z : D}
           (f : x ~{C}~> w) (g : y ~{D}~> z) :
  F (x, y) ~{E}~> F (w, z).
Admitted.

#[export] Program Instance bimap_respects {F : C ∏ D ⟶ E} {x w : C} {y z : D} :
  Proper (equiv ==> equiv ==> equiv) (@bimap F x w y z).

Lemma bimap_id_id {F : C ∏ D ⟶ E} {x y} :
  bimap (id[x]) (id[y]) ≈ id.
Admitted.

Lemma bimap_comp {F : C ∏ D ⟶ E} {x y z w u v}
      (f : y ~{C}~> z) (h : x ~{C}~> y)
      (g : v ~{D}~> w) (i : u ~{D}~> v) :
  bimap (f ∘ h) (g ∘ i) ≈ bimap f g ∘ bimap h i.
Admitted.

Lemma bimap_comp_id_right {F : C ∏ D ⟶ E} {w}
      `(f : y ~{C}~> z) `(g : x ~{C}~> y) :
  bimap (f ∘ g) (id[w]) ≈ bimap f id ∘ bimap g id.
Admitted.

Lemma bimap_id_right_left {F : C ∏ D ⟶ E} {w}
      `(f : z ~{C}~> w) `(g : x ~{D}~> y) :
  bimap f id ∘ bimap id g ≈ bimap f g.
Admitted.

Lemma bimap_id_left_right {F : C ∏ D ⟶ E} {w}
      `(f : z ~{D}~> w) `(g : x ~{C}~> y) :
  bimap id f ∘ bimap g id ≈ bimap g f.
Admitted.
Admit Obligations.

End Bifunctor.

Notation "bimap[ F ]" := (@bimap _ _ _ F%functor _ _ _ _)
  (at level 9, format "bimap[ F ]") : morphism_scope.

Ltac normal :=
  repeat
    match goal with
    | [ |- context [?F ∘ (?G ∘ ?H)] ] =>
      rewrite (comp_assoc F G H)

    | [ |- context [fmap[?F] ?G ∘ fmap[?F] _] ] =>
      rewrite <- (@fmap_comp _ _ F _ _ _ G)

    | [ |- context [fmap[?F] id] ] =>
      rewrite <- (@fmap_id _ _ F)

    | [ |- context [bimap ?F _ ∘ bimap _ _] ] =>
      rewrite <- (bimap_comp F)
    | [ |- context [(?F ∘ bimap ?G _) ∘ bimap _ _] ] =>
      rewrite <- (comp_assoc F (bimap _ _));
      rewrite <- (bimap_comp G)

    | [ |- context [id ∘ ?F] ] => rewrite (id_left F)
    | [ |- context [?F ∘ id] ] => rewrite (id_right F)

    | [ |- context [bimap id id] ] =>
      rewrite bimap_id_id
    | [ |- context [bimap ?F id ∘ bimap id ?G] ] =>
      rewrite (bimap_id_right_left F)
    | [ |- context [bimap id ?F ∘ bimap ?G id] ] =>
      rewrite (bimap_id_left_right F G)

    | [ H : context [fmap[?F] ?G ∘ fmap[?F] _] |- _ ] =>
      rewrite <- (@fmap_comp _ _ F _ _ _ G) in H
    | [ H : context [bimap ?F id ∘ bimap id ?G] |- _ ] =>
      rewrite (bimap_id_right_left F) in H
    | [ H : context [bimap id ?F ∘ bimap ?G id] |- _ ] =>
      rewrite (bimap_id_left_right F G) in H
    | [ H : context [bimap ?F _ ∘ bimap _ _] |- _ ] =>
      rewrite <- (bimap_comp F) in H
    | [ H : context [(?F ∘ bimap ?G _) ∘ bimap _ _] |- _ ] =>
      rewrite <- (comp_assoc F (bimap _ _)) in H;
      rewrite <- (bimap_comp G) in H
    | [ H : context [id ∘ ?F] |- _ ] => rewrite (id_left F) in H
    | [ H : context [?F ∘ id] |- _ ] => rewrite (id_right F) in H
    end.

Section Monoidal.

Context {C : Category}.

Reserved Infix "⨂" (at level 30, right associativity).

Class Monoidal := {
  I : C;
  tensor : C ∏ C ⟶ C where "x ⨂ y" := (tensor (x, y));

  unit_left  {x} : I ⨂ x ≅ x;
  unit_right {x} : x ⨂ I ≅ x;

  tensor_assoc {x y z} : (x ⨂ y) ⨂ z ≅ x ⨂ (y ⨂ z);

  to_unit_left_natural {x y} (g : x ~> y) :
    g ∘ unit_left << I ⨂ x ~~> y >> unit_left ∘ bimap id g;
  from_unit_left_natural {x y} (g : x ~> y) :
    bimap id g ∘ unit_left⁻¹ << x ~~> I ⨂ y >> unit_left⁻¹ ∘ g;

  to_unit_right_natural {x y} (g : x ~> y) :
    g ∘ unit_right << x ⨂ I ~~> y >> unit_right ∘ bimap g id;
  from_unit_right_natural {x y} (g : x ~> y) :
    bimap g id ∘ unit_right⁻¹ << x ~~> y ⨂ I >> unit_right⁻¹ ∘ g;

  to_tensor_assoc_natural
    {x y z w v u} (g : x ~> y) (h : z ~> w) (i : v ~> u) :
    bimap g (bimap h i) ∘ tensor_assoc
      << (x ⨂ z) ⨂ v ~~> y ⨂ w ⨂ u >>
    tensor_assoc ∘ bimap (bimap g h) i;

  from_tensor_assoc_natural
    {x y z w v u} (g : x ~> y) (h : z ~> w) (i : v ~> u) :
    bimap (bimap g h) i ∘ tensor_assoc⁻¹
      << x ⨂ z ⨂ v ~~> (y ⨂ w) ⨂ u >>
    tensor_assoc⁻¹ ∘ bimap g (bimap h i);

  triangle_identity {x y} :
    bimap unit_right id
      << (x ⨂ I) ⨂ y ~~> x ⨂ y >>
    bimap id unit_left ∘ tensor_assoc;

  pentagon_identity {x y z w} :
    bimap id tensor_assoc ∘ tensor_assoc ∘ bimap tensor_assoc id
      << ((x ⨂ y) ⨂ z) ⨂ w ~~> x ⨂ (y ⨂ (z ⨂ w)) >>
    tensor_assoc ∘ tensor_assoc
}.

End Monoidal.

Notation "(⨂)" := (@tensor _ _) : functor_scope.
Notation "x ⨂ y" := (@tensor _ _ (x%object, y%object))
  (at level 30, right associativity) : object_scope.
Notation "f ⨂ g" := (bimap[(⨂)] f g)
  (at level 30, right associativity) : morphism_scope.

Class Naturality (A : Type) : Type := {
  natural (f : A) : Type
}.

Class Mapping {C : Category} (F : C → C) : Type := {
  map {x y} (f : x ~> y) : F x ~> F y;
}.

#[export]
Program Instance Identity_Mapping {C : Category} :
  Mapping (fun x => x) | 9 := {
  map := fun _ _ f => f;
}.

#[export]
Program Instance ArityOne {C : Category}
  (P : C → C) {F : @Mapping C P}
  (Q : C → C) {G : @Mapping C Q} :
  @Naturality (∀ A, P A ~> Q A) := {
  natural := fun f => ∀ x y (g : x ~> y), @map _ _ G _ _ g ∘ f x ≈ f y ∘ @map _ _ F _ _ g
}.

#[export]
Program Instance ArityTwo {C : Category}
  (P : C → C → C)
  {FA : ∀ B, @Mapping C (fun A => P A B)}
  {FB : ∀ A, @Mapping C (fun B => P A B)}
  (Q : C → C → C)
  {GA : ∀ B, @Mapping C (fun A => Q A B)}
  {GB : ∀ A, @Mapping C (fun B => Q A B)} :
  @Naturality (∀ A B, P A B ~> Q A B) := {
  natural := fun f => ∀ x y (g : x ~> y) z w (h : z ~> w),
                 @map _ _ (GB _) _ _ h ∘ @map _ _ (GA _) _ _ g ∘ f x z
                   ≈ f y w ∘ @map _ _ (FB _) _ _ h ∘ @map _ _ (FA _) _ _ g
}.

#[export]
Program Instance ArityFour {C : Category}
  (P : C → C → C → C → C)
  {FA : ∀ B D E : C, @Mapping C (fun A => P A B D E)}
  {FB : ∀ A D E : C, @Mapping C (fun B => P A B D E)}
  {FC : ∀ A B E : C, @Mapping C (fun D => P A B D E)}
  {FD : ∀ A B D : C, @Mapping C (fun E => P A B D E)}
  (Q : C → C → C → C → C)
  {GA : ∀ B D E : C, @Mapping C (fun A => Q A B D E)}
  {GB : ∀ A D E : C, @Mapping C (fun B => Q A B D E)}
  {GC : ∀ A B E : C, @Mapping C (fun D => Q A B D E)}
  {GD : ∀ A B D : C, @Mapping C (fun E => Q A B D E)} :
  @Naturality (∀ A B D E, P A B D E ~> Q A B D E) := {
  natural := fun f => ∀ x y (g : x ~> y)
                        z w (h : z ~> w)
                        v u (i : v ~> u)
                        t s (j : t ~> s),
                 @map _ _ (GD _ _ _) _ _ j ∘
                   @map _ _ (GC _ _ _) _ _ i ∘
                   @map _ _ (GB _ _ _) _ _ h ∘
                   @map _ _ (GA _ _ _) _ _ g
                   ∘ f x z v t
                   ≈ f y w u s
                   ∘ @map _ _ (FD _ _ _) _ _ j
                   ∘ @map _ _ (FC _ _ _) _ _ i
                   ∘ @map _ _ (FB _ _ _) _ _ h
                   ∘ @map _ _ (FA _ _ _) _ _ g
}.

Section MonoidalNaturality.

Context `{M : @Monoidal C}.

#[export] Program Instance Tensor_Left_Map `{@Mapping C P} {y : C} :
  @Mapping C (fun x => P x ⨂ y)%object := {
  map := fun _ _ f => map f ⨂ id;
}.

#[export] Program Instance Tensor_Right_Map `{@Mapping C P} {x : C} :
  @Mapping C (fun y => x ⨂ P y)%object := {
  map := fun _ _ f => id ⨂ map f;
}.

#[export] Program Instance Tensor_Both_Map `{@Mapping C P} :
  @Mapping C (fun x => P x ⨂ P x)%object := {
  map := fun _ _ f => map f ⨂ map f;
}.

End MonoidalNaturality.

Section BraidedMonoidal.

Context {C : Category}.

Class BraidedMonoidal := {
  braided_is_monoidal : @Monoidal C;

  braid {x y} : x ⨂ y ~> y ⨂ x;
  braid_natural : natural (@braid);

  hexagon_identity {x y z} :
    tensor_assoc ∘ braid ∘ tensor_assoc
      << (x ⨂ y) ⨂ z ~~> y ⨂ (z ⨂ x) >>
    id ⨂ braid ∘ tensor_assoc ∘ braid ⨂ id;

  hexagon_identity_sym {x y z} :
    tensor_assoc⁻¹ ∘ braid ∘ tensor_assoc⁻¹
      << x ⨂ (y ⨂ z) ~~> (z ⨂ x) ⨂ y >>
    braid ⨂ id ∘ tensor_assoc⁻¹ ∘ id ⨂ braid;
}.
#[export] Existing Instance braided_is_monoidal.

End BraidedMonoidal.

Section SymmetricMonoidal.

Context {C : Category}.

Class SymmetricMonoidal := {
  symmetric_is_braided : @BraidedMonoidal C;

  braid_invol {x y} : braid ∘ braid ≈ id[x ⨂ y];
}.
#[export] Existing Instance symmetric_is_braided.

End SymmetricMonoidal.

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
