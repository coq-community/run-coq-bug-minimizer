
(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "-notation-overridden" "-w" "-redundant-canonical-projection" "-w" "-unknown-warning" "-w" "-argument-scope-delimiter" "-w" "-deprecated-native-compiler-option" "-native-compiler" "ondemand" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/iris/iris/prelude" "iris.prelude" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/iris/iris/algebra" "iris.algebra" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/iris/iris/si_logic" "iris.si_logic" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/iris/iris/bi" "iris.bi" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/iris/iris/proofmode" "iris.proofmode" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/iris/iris/base_logic" "iris.base_logic" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/iris/iris/program_logic" "iris.program_logic" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/iris/iris_heap_lang" "iris.heap_lang" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/iris/iris_unstable" "iris.unstable" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/iris/iris_deprecated" "iris.deprecated" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Autosubst" "Autosubst" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/stdpp" "stdpp" "-top" "Top.bug_01") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 726 lines to 130 lines, then from 143 lines to 1002 lines, then from 1007 lines to 170 lines, then from 183 lines to 949 lines, then from 954 lines to 233 lines, then from 246 lines to 540 lines, then from 545 lines to 265 lines, then from 278 lines to 605 lines, then from 610 lines to 267 lines, then from 280 lines to 682 lines, then from 687 lines to 271 lines, then from 284 lines to 2333 lines, then from 2338 lines to 477 lines, then from 490 lines to 2487 lines, then from 2489 lines to 558 lines, then from 571 lines to 632 lines, then from 637 lines to 558 lines, then from 571 lines to 636 lines, then from 641 lines to 560 lines, then from 573 lines to 637 lines, then from 642 lines to 559 lines, then from 572 lines to 1419 lines, then from 1424 lines to 1134 lines, then from 1133 lines to 611 lines, then from 624 lines to 5214 lines, then from 5218 lines to 1697 lines *)
(* coqc version 8.20+alpha compiled with OCaml 4.14.1
   coqtop version runner-cabngxqim-project-4504-concurrent-1:/builds/coq/coq/_build/default,(HEAD detached at 30ed4fe1292f0) (30ed4fe1292f0d84b330fc8932e8041060152357)
   Expected coqc runtime on this file: 1.919 sec *)
Require Coq.Init.Ltac.
Require Coq.Bool.Bool.
Require Coq.Classes.Morphisms.
Require Coq.Classes.RelationClasses.
Require Coq.Init.Peano.
Require Coq.Lists.List.
Require Coq.Logic.EqdepFacts.
Require Coq.NArith.NArith.
Require Coq.PArith.PArith.
Require Coq.Program.Basics.
Require Coq.Program.Syntax.
Require Coq.QArith.QArith.
Require Coq.QArith.QArith_base.
Require Coq.QArith.Qcanon.
Require Coq.Setoids.Setoid.
Require Coq.Sorting.Permutation.
Require Coq.Unicode.Utf8.
Require Coq.ZArith.ZArith.
Require Coq.micromega.Lia.
Require Coq.ssr.ssrfun.
Require stdpp.options.
Require stdpp.base.
Require stdpp.proof_irrel.
Require stdpp.well_founded.
Require stdpp.decidable.
Require stdpp.tactics.
Require stdpp.fin.
Require stdpp.option.
Require stdpp.orders.
Require stdpp.numbers.
Require stdpp.list.
Require stdpp.list_numbers.
Require stdpp.countable.
Require stdpp.vector.
Require stdpp.finite.
Require stdpp.sets.
Require stdpp.relations.
Require stdpp.fin_sets.

Module Export AdmitTactic.
Module Import LocalFalse.
Inductive False : Prop := .
End LocalFalse.
Axiom proof_admitted : False.
Import Coq.Init.Ltac.
Tactic Notation "admit" := abstract case proof_admitted.
End AdmitTactic.

Module Export stdpp_DOT_fin_maps_WRAPPED.
Module Export fin_maps.
 
Import Coq.Sorting.Permutation.
Export stdpp.relations.
Export stdpp.orders.
Export stdpp.vector.
Export stdpp.fin_sets.
Import stdpp.options.

 
Unset Default Proof Using.

 
 

 

Class MapFold K A M := map_fold B : (K → A → B → B) → B → M → B.
Global Arguments map_fold {_ _ _ _ _} _ _ _.
Global Hint Mode MapFold - - ! : typeclass_instances.
Global Hint Mode MapFold ! - - : typeclass_instances.

 
Global Strategy 1 [map_fold].
Definition diag_None {A B C} (f : option A → option B → option C)
    (mx : option A) (my : option B) : option C. exact (match mx, my with None, None => None | _, _ => f mx my end). Defined.
Global Instance map_insert `{PartialAlter K A M} : Insert K A M. exact (λ i x, partial_alter (λ _, Some x) i). Defined.

Class FinMap K M `{FMap M, ∀ A, Lookup K A (M A), ∀ A, Empty (M A), ∀ A,
    PartialAlter K A (M A), OMap M, Merge M, ∀ A, MapFold K A (M A),
    EqDecision K} := {
  map_eq {A} (m1 m2 : M A) : (∀ i, m1 !! i = m2 !! i) → m1 = m2;
  lookup_empty {A} i : (∅ : M A) !! i = None;
  lookup_partial_alter {A} f (m : M A) i :
    partial_alter f i m !! i = f (m !! i);
  lookup_partial_alter_ne {A} f (m : M A) i j :
    i ≠ j → partial_alter f i m !! j = m !! j;
  lookup_fmap {A B} (f : A → B) (m : M A) i : (f <$> m) !! i = f <$> m !! i;
  lookup_omap {A B} (f : A → option B) (m : M A) i :
    omap f m !! i = m !! i ≫= f;
  lookup_merge {A B C} (f : option A → option B → option C) (m1 : M A) (m2 : M B) i :
    merge f m1 m2 !! i = diag_None f (m1 !! i) (m2 !! i);
  map_fold_ind {A B} (P : B → M A → Prop) (f : K → A → B → B) (b : B) :
    P b ∅ →
    (∀ i x m r, m !! i = None → P r m → P (f i x r) (<[i:=x]> m)) →
    ∀ m, P (map_fold f b m) m
}.
Global Instance map_alter `{PartialAlter K A M} : Alter K A M. exact (λ f, partial_alter (fmap f)). Defined.
Global Instance map_delete `{PartialAlter K A M} : Delete K M. exact (partial_alter (λ _, None)). Defined.
Global Instance map_singleton `{PartialAlter K A M, Empty M} :
  SingletonM K A M. exact (λ i x, <[i:=x]> ∅). Defined.
Definition list_to_map `{Insert K A M, Empty M} : list (K * A) → M. exact (fold_right (λ p, <[p.1:=p.2]>) ∅). Defined.
Global Instance map_size `{MapFold K A M} : Size M. exact (map_fold (λ _ _, S) 0). Defined.
Definition map_to_list `{MapFold K A M} : M → list (K * A). exact (map_fold (λ i x, ((i,x) ::.)) []). Defined.
Definition map_to_set `{MapFold K A M,
    Singleton B C, Empty C, Union C} (f : K → A → B) (m : M) : C. exact (list_to_set (uncurry f <$> map_to_list m)). Defined.
Definition set_to_map `{Elements B C, Insert K A M, Empty M}
    (f : B → K * A) (X : C) : M. exact (list_to_map (f <$> elements X)). Defined.
Global Instance map_union_with `{Merge M} {A} : UnionWith A (M A). exact (λ f, merge (union_with f)). Defined.
Global Instance map_intersection_with `{Merge M} {A} : IntersectionWith A (M A). exact (λ f, merge (intersection_with f)). Defined.
Global Instance map_difference_with `{Merge M} {A} : DifferenceWith A (M A). exact (λ f, merge (difference_with f)). Defined.
Global Instance map_equiv `{∀ A, Lookup K A (M A), Equiv A} : Equiv (M A) | 20. exact (λ m1 m2, ∀ i, m1 !! i ≡ m2 !! i). Defined.
Definition map_Forall `{Lookup K A M} (P : K → A → Prop) : M → Prop. exact (λ m, ∀ i x, m !! i = Some x → P i x). Defined.
Definition map_Exists `{Lookup K A M} (P : K → A → Prop) : M → Prop. exact (λ m, ∃ i x, m !! i = Some x ∧ P i x). Defined.
Definition map_relation `{∀ A, Lookup K A (M A)} {A B} (R : A → B → Prop)
    (P : A → Prop) (Q : B → Prop) (m1 : M A) (m2 : M B) : Prop. exact (∀ i,
  option_relation R P Q (m1 !! i) (m2 !! i)). Defined.
Definition map_included `{∀ A, Lookup K A (M A)} {A}
  (R : relation A) : relation (M A). exact (map_relation R (λ _, False) (λ _, True)). Defined.
Definition map_agree `{∀ A, Lookup K A (M A)} {A} : relation (M A). exact (map_relation (=) (λ _, True) (λ _, True)). Defined.
Definition map_disjoint `{∀ A, Lookup K A (M A)} {A} : relation (M A). exact (map_relation (λ _ _, False) (λ _, True) (λ _, True)). Defined.
Infix "##ₘ" := map_disjoint (at level 70) : stdpp_scope.
Global Hint Extern 0 (_ ##ₘ _) => symmetry; eassumption : core.
Notation "( m ##ₘ.)" := (map_disjoint m) (only parsing) : stdpp_scope.
Notation "(.##ₘ m )" := (λ m2, m2 ##ₘ m) (only parsing) : stdpp_scope.
Global Instance map_subseteq `{∀ A, Lookup K A (M A)} {A} : SubsetEq (M A). exact (map_included (=)). Defined.
Global Instance map_union `{Merge M} {A} : Union (M A). exact (union_with (λ x _, Some x)). Defined.
Global Instance map_intersection `{Merge M} {A} : Intersection (M A). exact (intersection_with (λ x _, Some x)). Defined.
Global Instance map_difference `{Merge M} {A} : Difference (M A). exact (difference_with (λ _ _, None)). Defined.
Definition map_imap `{∀ A, Insert K A (M A), ∀ A, Empty (M A),
    ∀ A, MapFold K A (M A)} {A B} (f : K → A → option B) (m : M A) : M B. exact (list_to_map (omap (λ ix, (fst ix ,.) <$> uncurry f ix) (map_to_list m))). Defined.
Definition kmap `{∀ A, Insert K2 A (M2 A), ∀ A, Empty (M2 A),
    ∀ A, MapFold K1 A (M1 A)} {A} (f : K1 → K2) (m : M1 A) : M2 A. exact (list_to_map (fmap (prod_map f id) (map_to_list m))). Defined.
Definition map_zip_with `{Merge M} {A B C} (f : A → B → C) : M A → M B → M C. exact (merge (λ mx my,
    match mx, my with Some x, Some y => Some (f x y) | _, _ => None end)). Defined.
Notation map_zip := (map_zip_with pair).
Global Instance map_filter
    `{MapFold K A M, Insert K A M, Empty M} : Filter (K * A) M. exact (λ P _, map_fold (λ k v m, if decide (P (k,v)) then <[k := v]>m else m) ∅). Defined.

Fixpoint map_seq `{Insert nat A M, Empty M} (start : nat) (xs : list A) : M :=
  match xs with
  | [] => ∅
  | x :: xs => <[start:=x]> (map_seq (S start) xs)
  end.

Fixpoint map_seqZ `{Insert Z A M, Empty M} (start : Z) (xs : list A) : M :=
  match xs with
  | [] => ∅
  | x :: xs => <[start:=x]> (map_seqZ (Z.succ start) xs)
  end.
Global Instance map_lookup_total `{!Lookup K A (M A), !Inhabited A} :
  LookupTotal K A (M A) | 20. exact (λ i m, default inhabitant (m !! i)). Defined.
Global Typeclasses Opaque map_lookup_total.
Definition map_img `{MapFold K A M,
  Singleton A SA, Empty SA, Union SA} : M → SA. exact (map_to_set (λ _ x, x)). Defined.
Global Typeclasses Opaque map_img.
Definition map_preimg `{MapFold K A MKA, Empty MASK,
    PartialAlter A SK MASK, Empty SK, Singleton K SK, Union SK}
    (m : MKA) : MASK. exact (map_fold (λ i, partial_alter (λ mX, Some $ {[ i ]} ∪ default ∅ mX)) ∅ m). Defined.
Global Typeclasses Opaque map_preimg.
Definition map_compose `{OMap MA, Lookup B C MB}
  (m : MB) (n : MA B) : MA C. exact (omap (m !!.) n). Defined.

Infix "∘ₘ" := map_compose (at level 65, right associativity) : stdpp_scope.
Notation "(∘ₘ)" := map_compose (only parsing) : stdpp_scope.
Notation "( m ∘ₘ.)" := (map_compose m) (only parsing) : stdpp_scope.
Notation "(.∘ₘ m )" := (λ n, map_compose n m) (only parsing) : stdpp_scope.

 
Section theorems.
Context `{FinMap K M}.

 
Lemma map_eq_iff {A} (m1 m2 : M A) : m1 = m2 ↔ ∀ i, m1 !! i = m2 !! i.
Admitted.
Lemma map_subseteq_spec {A} (m1 m2 : M A) :
  m1 ⊆ m2 ↔ ∀ i x, m1 !! i = Some x → m2 !! i = Some x.
Admitted.
Global Instance map_included_preorder {A} (R : relation A) :
  PreOrder R → PreOrder (map_included R : relation (M A)).
Admitted.
Global Instance map_subseteq_po {A} : PartialOrder (⊆@{M A}).
Admitted.
Lemma lookup_total_alt `{!Inhabited A} (m : M A) i :
  m !!! i = default inhabitant (m !! i).
Admitted.
Lemma lookup_total_correct `{!Inhabited A} (m : M A) i x :
  m !! i = Some x → m !!! i = x.
Admitted.
Lemma lookup_lookup_total `{!Inhabited A} (m : M A) i :
  is_Some (m !! i) → m !! i = Some (m !!! i).
Admitted.
Lemma lookup_weaken {A} (m1 m2 : M A) i x :
  m1 !! i = Some x → m1 ⊆ m2 → m2 !! i = Some x.
Admitted.
Lemma lookup_weaken_is_Some {A} (m1 m2 : M A) i :
  is_Some (m1 !! i) → m1 ⊆ m2 → is_Some (m2 !! i).
Admitted.
Lemma lookup_weaken_None {A} (m1 m2 : M A) i :
  m2 !! i = None → m1 ⊆ m2 → m1 !! i = None.
Admitted.
Lemma lookup_weaken_inv {A} (m1 m2 : M A) i x y :
  m1 !! i = Some x → m1 ⊆ m2 → m2 !! i = Some y → x = y.
Admitted.
Lemma lookup_ne {A} (m : M A) i j : m !! i ≠ m !! j → i ≠ j.
Admitted.
Lemma map_empty {A} (m : M A) : m = ∅ ↔ ∀ i, m !! i = None.
Admitted.
Lemma lookup_empty_is_Some {A} i : ¬is_Some ((∅ : M A) !! i).
Admitted.
Lemma lookup_empty_Some {A} i (x : A) : ¬(∅ : M A) !! i = Some x.
Admitted.
Lemma lookup_total_empty `{!Inhabited A} i : (∅ : M A) !!! i = inhabitant.
Admitted.
Lemma map_subset_empty {A} (m : M A) : m ⊄ ∅.
Admitted.
Lemma map_empty_subseteq {A} (m : M A) : ∅ ⊆ m.
Admitted.

 
Local Lemma map_to_list_spec {A} (m : M A) :
  NoDup (map_to_list m) ∧ (∀ i x, (i,x) ∈ map_to_list m ↔ m !! i = Some x).
Admitted.
Lemma NoDup_map_to_list {A} (m : M A) : NoDup (map_to_list m).
Admitted.
Lemma elem_of_map_to_list {A} (m : M A) i x :
  (i,x) ∈ map_to_list m ↔ m !! i = Some x.
Admitted.

Lemma map_subset_alt {A} (m1 m2 : M A) :
  m1 ⊂ m2 ↔ m1 ⊆ m2 ∧ ∃ i, m1 !! i = None ∧ is_Some (m2 !! i).
Admitted.

 
Lemma partial_alter_ext {A} (f g : option A → option A) (m : M A) i :
  (∀ x, m !! i = x → f x = g x) → partial_alter f i m = partial_alter g i m.
Admitted.
Lemma partial_alter_compose {A} f g (m : M A) i:
  partial_alter (f ∘ g) i m = partial_alter f i (partial_alter g i m).
Admitted.
Lemma partial_alter_commute {A} f g (m : M A) i j :
  i ≠ j → partial_alter f i (partial_alter g j m) =
    partial_alter g j (partial_alter f i m).
Admitted.
Lemma partial_alter_self_alt {A} (m : M A) i x :
  x = m !! i → partial_alter (λ _, x) i m = m.
Admitted.
Lemma partial_alter_self {A} (m : M A) i : partial_alter (λ _, m !! i) i m = m.
Admitted.
Lemma partial_alter_subseteq {A} f (m : M A) i :
  m !! i = None → m ⊆ partial_alter f i m.
Admitted.
Lemma partial_alter_subset {A} f (m : M A) i :
  m !! i = None → is_Some (f (m !! i)) → m ⊂ partial_alter f i m.
Admitted.
Lemma lookup_partial_alter_Some {A} (f : option A → option A) (m : M A) i j x :
  partial_alter f i m !! j = Some x ↔
    (i = j ∧ f (m !! i) = Some x) ∨ (i ≠ j ∧ m !! j = Some x).
Admitted.
Lemma lookup_total_partial_alter {A} `{Inhabited A}
    (f : option A → option A) (m : M A) i:
  partial_alter f i m !!! i = default inhabitant (f (m !! i)).
Admitted.

 
Lemma lookup_alter {A} (f : A → A) (m : M A) i : alter f i m !! i = f <$> m !! i.
Admitted.
Lemma lookup_alter_ne {A} (f : A → A) (m : M A) i j :
  i ≠ j → alter f i m !! j = m !! j.
Admitted.
Lemma alter_ext {A} (f g : A → A) (m : M A) i :
  (∀ x, m !! i = Some x → f x = g x) → alter f i m = alter g i m.
Admitted.
Lemma alter_compose {A} (f g : A → A) (m : M A) i:
  alter (f ∘ g) i m = alter f i (alter g i m).
Admitted.
Lemma alter_commute {A} (f g : A → A) (m : M A) i j :
  i ≠ j → alter f i (alter g j m) = alter g j (alter f i m).
Admitted.
Lemma alter_insert {A} (m : M A) i f x :
  alter f i (<[i := x]> m) = <[i := f x]> m.
Admitted.
Lemma alter_insert_ne {A} (m : M A) i j f x :
  i ≠ j →
  alter f i (<[j := x]> m) = <[j := x]> (alter f i m).
Admitted.
Lemma lookup_alter_Some {A} (f : A → A) (m : M A) i j y :
  alter f i m !! j = Some y ↔
    (i = j ∧ ∃ x, m !! j = Some x ∧ y = f x) ∨ (i ≠ j ∧ m !! j = Some y).
Admitted.
Lemma lookup_alter_None {A} (f : A → A) (m : M A) i j :
  alter f i m !! j = None ↔ m !! j = None.
Admitted.
Lemma lookup_alter_is_Some {A} (f : A → A) (m : M A) i j :
  is_Some (alter f i m !! j) ↔ is_Some (m !! j).
Admitted.
Lemma alter_id {A} (f : A → A) (m : M A) i :
  (∀ x, m !! i = Some x → f x = x) → alter f i m = m.
Admitted.
Lemma alter_mono {A} f (m1 m2 : M A) i : m1 ⊆ m2 → alter f i m1 ⊆ alter f i m2.
Admitted.
Lemma alter_strict_mono {A} f (m1 m2 : M A) i :
  m1 ⊂ m2 → alter f i m1 ⊂ alter f i m2.
Admitted.

 
Lemma lookup_delete {A} (m : M A) i : delete i m !! i = None.
Admitted.
Lemma lookup_total_delete `{!Inhabited A} (m : M A) i :
  delete i m !!! i = inhabitant.
Admitted.
Lemma lookup_delete_ne {A} (m : M A) i j : i ≠ j → delete i m !! j = m !! j.
Admitted.
Lemma lookup_total_delete_ne `{!Inhabited A} (m : M A) i j :
  i ≠ j → delete i m !!! j = m !!! j.
Admitted.
Lemma lookup_delete_Some {A} (m : M A) i j y :
  delete i m !! j = Some y ↔ i ≠ j ∧ m !! j = Some y.
Admitted.
Lemma lookup_delete_is_Some {A} (m : M A) i j :
  is_Some (delete i m !! j) ↔ i ≠ j ∧ is_Some (m !! j).
Admitted.
Lemma lookup_delete_None {A} (m : M A) i j :
  delete i m !! j = None ↔ i = j ∨ m !! j = None.
Admitted.
Lemma delete_empty {A} i : delete i ∅ =@{M A} ∅.
Admitted.
Lemma delete_commute {A} (m : M A) i j :
  delete i (delete j m) = delete j (delete i m).
Admitted.
Lemma delete_notin {A} (m : M A) i : m !! i = None → delete i m = m.
Admitted.
Lemma delete_idemp {A} (m : M A) i :
  delete i (delete i m) = delete i m.
Admitted.
Lemma delete_partial_alter {A} (m : M A) i f :
  m !! i = None → delete i (partial_alter f i m) = m.
Admitted.
Lemma delete_insert {A} (m : M A) i x :
  m !! i = None → delete i (<[i:=x]>m) = m.
Admitted.
Lemma delete_insert_delete {A} (m : M A) i x :
  delete i (<[i:=x]>m) = delete i m.
Admitted.
Lemma delete_insert_ne {A} (m : M A) i j x :
  i ≠ j → delete i (<[j:=x]>m) = <[j:=x]>(delete i m).
Admitted.
Lemma delete_alter {A} (m : M A) i f :
  delete i (alter f i m) = delete i m.
Admitted.
Lemma delete_alter_ne {A} (m : M A) i j f :
  i ≠ j → delete i (alter f j m) = alter f j (delete i m).
Admitted.
Lemma delete_subseteq {A} (m : M A) i : delete i m ⊆ m.
Admitted.
Lemma delete_subset {A} (m : M A) i : is_Some (m !! i) → delete i m ⊂ m.
Admitted.
Lemma delete_mono {A} (m1 m2 : M A) i : m1 ⊆ m2 → delete i m1 ⊆ delete i m2.
Admitted.

 
Lemma lookup_insert {A} (m : M A) i x : <[i:=x]>m !! i = Some x.
Admitted.
Lemma lookup_total_insert `{!Inhabited A} (m : M A) i x : <[i:=x]>m !!! i = x.
Admitted.
Lemma lookup_insert_rev {A}  (m : M A) i x y : <[i:=x]>m !! i = Some y → x = y.
Admitted.
Lemma lookup_insert_ne {A} (m : M A) i j x : i ≠ j → <[i:=x]>m !! j = m !! j.
Admitted.
Lemma lookup_total_insert_ne `{!Inhabited A} (m : M A) i j x :
  i ≠ j → <[i:=x]>m !!! j = m !!! j.
Admitted.
Lemma insert_insert {A} (m : M A) i x y : <[i:=x]>(<[i:=y]>m) = <[i:=x]>m.
Admitted.
Lemma insert_commute {A} (m : M A) i j x y :
  i ≠ j → <[i:=x]>(<[j:=y]>m) = <[j:=y]>(<[i:=x]>m).
Admitted.
Lemma lookup_insert_Some {A} (m : M A) i j x y :
  <[i:=x]>m !! j = Some y ↔ (i = j ∧ x = y) ∨ (i ≠ j ∧ m !! j = Some y).
Admitted.
Lemma lookup_insert_is_Some {A} (m : M A) i j x :
  is_Some (<[i:=x]>m !! j) ↔ i = j ∨ i ≠ j ∧ is_Some (m !! j).
Admitted.
Lemma lookup_insert_is_Some' {A} (m : M A) i j x :
  is_Some (<[i:=x]>m !! j) ↔ i = j ∨ is_Some (m !! j).
Admitted.
Lemma lookup_insert_None {A} (m : M A) i j x :
  <[i:=x]>m !! j = None ↔ m !! j = None ∧ i ≠ j.
Admitted.
Lemma insert_id {A} (m : M A) i x : m !! i = Some x → <[i:=x]>m = m.
Admitted.
Lemma insert_included {A} R `{!Reflexive R} (m : M A) i x :
  (∀ y, m !! i = Some y → R y x) → map_included R m (<[i:=x]>m).
Admitted.
Lemma insert_empty {A} i (x : A) : <[i:=x]> ∅ =@{M A} {[i := x]}.
Admitted.
Lemma insert_non_empty {A} (m : M A) i x : <[i:=x]>m ≠ ∅.
Admitted.
Lemma insert_delete_insert {A} (m : M A) i x : <[i:=x]>(delete i m) = <[i:=x]> m.
Admitted.
Lemma insert_delete {A} (m : M A) i x :
  m !! i = Some x → <[i:=x]> (delete i m) = m.
Admitted.

Lemma insert_subseteq {A} (m : M A) i x : m !! i = None → m ⊆ <[i:=x]>m.
Admitted.
Lemma insert_subset {A} (m : M A) i x : m !! i = None → m ⊂ <[i:=x]>m.
Admitted.
Lemma insert_mono {A} (m1 m2 : M A) i x : m1 ⊆ m2 → <[i:=x]> m1 ⊆ <[i:=x]>m2.
Admitted.
Lemma insert_subseteq_r {A} (m1 m2 : M A) i x :
  m1 !! i = None → m1 ⊆ m2 → m1 ⊆ <[i:=x]>m2.
Admitted.
Lemma insert_subseteq_l {A} (m1 m2 : M A) i x :
  m2 !! i = Some x → m1 ⊆ m2 → <[i:=x]> m1 ⊆ m2.
Admitted.

Lemma insert_delete_subseteq {A} (m1 m2 : M A) i x :
  m1 !! i = None → <[i:=x]> m1 ⊆ m2 → m1 ⊆ delete i m2.
Admitted.
Lemma delete_insert_subseteq {A} (m1 m2 : M A) i x :
  m1 !! i = Some x → delete i m1 ⊆ m2 → m1 ⊆ <[i:=x]> m2.
Admitted.
Lemma insert_delete_subset {A} (m1 m2 : M A) i x :
  m1 !! i = None → <[i:=x]> m1 ⊂ m2 → m1 ⊂ delete i m2.
Admitted.
Lemma insert_subset_inv {A} (m1 m2 : M A) i x :
  m1 !! i = None → <[i:=x]> m1 ⊂ m2 →
  ∃ m2', m2 = <[i:=x]>m2' ∧ m1 ⊂ m2' ∧ m2' !! i = None.
Admitted.

 
Lemma lookup_singleton_Some {A} i j (x y : A) :
  ({[i := x]} : M A) !! j = Some y ↔ i = j ∧ x = y.
Admitted.
Lemma lookup_singleton_None {A} i j (x : A) :
  ({[i := x]} : M A) !! j = None ↔ i ≠ j.
Admitted.
Lemma lookup_singleton {A} i (x : A) : ({[i := x]} : M A) !! i = Some x.
Admitted.
Lemma lookup_total_singleton `{!Inhabited A} i (x : A) :
  ({[i := x]} : M A) !!! i = x.
Admitted.
Lemma lookup_singleton_ne {A} i j (x : A) :
  i ≠ j → ({[i := x]} : M A) !! j = None.
Admitted.
Lemma lookup_total_singleton_ne `{!Inhabited A} i j (x : A) :
  i ≠ j → ({[i := x]} : M A) !!! j = inhabitant.
Admitted.

Global Instance map_singleton_inj {A} : Inj2 (=) (=) (=) (singletonM (M:=M A)).
Admitted.

Lemma map_non_empty_singleton {A} i (x : A) : {[i := x]} ≠@{M A} ∅.
Admitted.
Lemma insert_singleton {A} i (x y : A) : <[i:=y]> {[i := x]} =@{M A} {[i := y]}.
Admitted.
Lemma alter_singleton {A} (f : A → A) i x :
  alter f i {[i := x]} =@{M A} {[i := f x]}.
Admitted.
Lemma alter_singleton_ne {A} (f : A → A) i j x :
  i ≠ j → alter f i {[j := x]}=@{M A} {[j := x]}.
Admitted.
Lemma singleton_non_empty {A} i (x : A) : {[i:=x]} ≠@{M A} ∅.
Admitted.
Lemma delete_singleton {A} i (x : A) : delete i {[i := x]} =@{M A} ∅.
Admitted.
Lemma delete_singleton_ne {A} i j (x : A) :
  i ≠ j → delete i {[j := x]} =@{M A} {[j := x]}.
Admitted.

Lemma map_singleton_subseteq_l {A} i (x : A) (m : M A) :
  {[i := x]} ⊆ m ↔ m !! i = Some x.
Admitted.
Lemma map_singleton_subseteq {A} i j (x y : A) :
  {[i := x]} ⊆@{M A} {[j := y]} ↔ i = j ∧ x = y.
Admitted.

 
Global Instance map_fmap_inj {A B} (f : A → B) :
  Inj (=) (=) f → Inj (=@{M A}) (=@{M B}) (fmap f).
Admitted.

Lemma lookup_fmap_Some {A B} (f : A → B) (m : M A) i y :
  (f <$> m) !! i = Some y ↔ ∃ x, f x = y ∧ m !! i = Some x.
Admitted.
Lemma lookup_omap_Some {A B} (f : A → option B) (m : M A) i y :
  omap f m !! i = Some y ↔ ∃ x, f x = Some y ∧ m !! i = Some x.
Admitted.
Lemma lookup_omap_id_Some {A} (m : M (option A)) i x :
  omap id m !! i = Some x ↔ m !! i = Some (Some x).
Admitted.

Lemma fmap_empty {A B} (f : A → B) : f <$> ∅ =@{M B} ∅.
Admitted.
Lemma omap_empty {A B} (f : A → option B) : omap f ∅ =@{M B} ∅.
Admitted.

Lemma fmap_empty_iff {A B} (f : A → B) m : f <$> m =@{M B} ∅ ↔ m = ∅.
Admitted.
Lemma fmap_empty_inv {A B} (f : A → B) m : f <$> m =@{M B} ∅ → m = ∅.
Admitted.

Lemma fmap_insert {A B} (f: A → B) (m : M A) i x :
  f <$> <[i:=x]>m = <[i:=f x]>(f <$> m).
Admitted.
Lemma omap_insert {A B} (f : A → option B) (m : M A) i x :
  omap f (<[i:=x]>m) =
    (match f x with Some y => <[i:=y]> | None => delete i end) (omap f m).
Admitted.
Lemma omap_insert_Some {A B} (f : A → option B) (m : M A) i x y :
  f x = Some y → omap f (<[i:=x]>m) = <[i:=y]>(omap f m).
Admitted.
Lemma omap_insert_None {A B} (f : A → option B) (m : M A) i x :
  f x = None → omap f (<[i:=x]>m) = delete i (omap f m).
Admitted.

Lemma fmap_delete {A B} (f: A → B) (m : M A) i :
  f <$> delete i m = delete i (f <$> m).
Admitted.
Lemma omap_delete {A B} (f: A → option B) (m : M A) i :
  omap f (delete i m) = delete i (omap f m).
Admitted.

Lemma map_fmap_singleton {A B} (f : A → B) i x :
  f <$> {[i := x]} =@{M B} {[i := f x]}.
Admitted.
Lemma map_fmap_singleton_inv {A B} (f : A → B) (m : M A) i y :
  f <$> m = {[i := y]} → ∃ x, y = f x ∧ m = {[ i := x ]}.
Admitted.

Lemma omap_singleton {A B} (f : A → option B) i x :
  omap f {[ i := x ]} =@{M B} match f x with Some y => {[ i:=y ]} | None => ∅ end.
Admitted.
Lemma omap_singleton_Some {A B} (f : A → option B) i x y :
  f x = Some y → omap f {[ i := x ]} =@{M B} {[ i := y ]}.
Admitted.
Lemma omap_singleton_None {A B} (f : A → option B) i x :
  f x = None → omap f {[ i := x ]} =@{M B} ∅.
Admitted.

Lemma map_fmap_id {A} (m : M A) : id <$> m = m.
Admitted.
Lemma map_fmap_compose {A B C} (f : A → B) (g : B → C) (m : M A) :
  g ∘ f <$> m = g <$> (f <$> m).
Admitted.
Lemma map_fmap_ext {A B} (f1 f2 : A → B) (m : M A) :
  (∀ i x, m !! i = Some x → f1 x = f2 x) → f1 <$> m = f2 <$> m.
Admitted.
Lemma omap_ext {A B} (f1 f2 : A → option B) (m : M A) :
  (∀ i x, m !! i = Some x → f1 x = f2 x) → omap f1 m = omap f2 m.
Admitted.

Lemma map_fmap_omap {A B C} (f : A → option B) (g : B → C) (m : M A) :
  g <$> omap f m = omap (λ x, g <$> f x) m.
Admitted.

Lemma map_fmap_alt {A B} (f : A → B) (m : M A) :
  f <$> m = omap (λ x, Some (f x)) m.
Admitted.

Lemma map_fmap_mono {A B} (f : A → B) (m1 m2 : M A) :
  m1 ⊆ m2 → f <$> m1 ⊆ f <$> m2.
Admitted.
Lemma map_fmap_strict_mono {A B} (f : A → B) (m1 m2 : M A) :
  m1 ⊂ m2 → f <$> m1 ⊂ f <$> m2.
Admitted.
Lemma map_omap_mono {A B} (f : A → option B) (m1 m2 : M A) :
  m1 ⊆ m2 → omap f m1 ⊆ omap f m2.
Admitted.

 
Lemma elem_of_map_to_list' {A} (m : M A) ix :
  ix ∈ map_to_list m ↔ m !! ix.1 = Some (ix.2).
Admitted.
Lemma map_to_list_unique {A} (m : M A) i x y :
  (i,x) ∈ map_to_list m → (i,y) ∈ map_to_list m → x = y.
Admitted.
Lemma NoDup_fst_map_to_list {A} (m : M A) : NoDup ((map_to_list m).*1).
Admitted.
Lemma elem_of_list_to_map_1' {A} (l : list (K * A)) i x :
  (∀ y, (i,y) ∈ l → x = y) → (i,x) ∈ l → (list_to_map l : M A) !! i = Some x.
Admitted.
Lemma elem_of_list_to_map_1 {A} (l : list (K * A)) i x :
  NoDup (l.*1) → (i,x) ∈ l → (list_to_map l : M A) !! i = Some x.
Admitted.
Lemma elem_of_list_to_map_2 {A} (l : list (K * A)) i x :
  (list_to_map l : M A) !! i = Some x → (i,x) ∈ l.
Admitted.
Lemma elem_of_list_to_map' {A} (l : list (K * A)) i x :
  (∀ x', (i,x) ∈ l → (i,x') ∈ l → x = x') →
  (i,x) ∈ l ↔ (list_to_map l : M A) !! i = Some x.
Admitted.
Lemma elem_of_list_to_map {A} (l : list (K * A)) i x :
  NoDup (l.*1) → (i,x) ∈ l ↔ (list_to_map l : M A) !! i = Some x.
Admitted.

Lemma not_elem_of_list_to_map_1 {A} (l : list (K * A)) i :
  i ∉ l.*1 → (list_to_map l : M A) !! i = None.
Admitted.
Lemma not_elem_of_list_to_map_2 {A} (l : list (K * A)) i :
  (list_to_map l : M A) !! i = None → i ∉ l.*1.
Admitted.
Lemma not_elem_of_list_to_map {A} (l : list (K * A)) i :
  i ∉ l.*1 ↔ (list_to_map l : M A) !! i = None.
Admitted.
Lemma list_to_map_proper {A} (l1 l2 : list (K * A)) :
  NoDup (l1.*1) → l1 ≡ₚ l2 → (list_to_map l1 : M A) = list_to_map l2.
Admitted.
Lemma list_to_map_inj {A} (l1 l2 : list (K * A)) :
  NoDup (l1.*1) → NoDup (l2.*1) →
  (list_to_map l1 : M A) = list_to_map l2 → l1 ≡ₚ l2.
Admitted.
Lemma list_to_map_to_list {A} (m : M A) : list_to_map (map_to_list m) = m.
Admitted.
Lemma map_to_list_to_map {A} (l : list (K * A)) :
  NoDup (l.*1) → map_to_list (list_to_map l) ≡ₚ l.
Admitted.
Lemma map_to_list_inj {A} (m1 m2 : M A) :
  map_to_list m1 ≡ₚ map_to_list m2 → m1 = m2.
Admitted.
Lemma list_to_map_flip {A} (m1 : M A) l2 :
  map_to_list m1 ≡ₚ l2 → m1 = list_to_map l2.
Admitted.

Lemma list_to_map_nil {A} : list_to_map [] =@{M A} ∅.
Admitted.
Lemma list_to_map_cons {A} (l : list (K * A)) i x :
  list_to_map ((i, x) :: l) =@{M A} <[i:=x]>(list_to_map l).
Admitted.
Lemma list_to_map_snoc {A} (l : list (K * A)) i x :
  i ∉ l.*1 → list_to_map (l ++ [(i, x)]) =@{M A} <[i:=x]>(list_to_map l).
Admitted.
Lemma list_to_map_fmap {A B} (f : A → B) l :
  list_to_map (prod_map id f <$> l) = f <$> (list_to_map l : M A).
Admitted.

Lemma map_to_list_empty {A} : map_to_list ∅ = @nil (K * A).
Admitted.
Lemma map_to_list_insert {A} (m : M A) i x :
  m !! i = None → map_to_list (<[i:=x]>m) ≡ₚ (i,x) :: map_to_list m.
Admitted.
Lemma map_to_list_singleton {A} i (x : A) :
  map_to_list ({[i:=x]} : M A) = [(i,x)].
Admitted.
Lemma map_to_list_delete {A} (m : M A) i x :
  m !! i = Some x → (i,x) :: map_to_list (delete i m) ≡ₚ map_to_list m.
Admitted.

Lemma map_to_list_submseteq {A} (m1 m2 : M A) :
  m1 ⊆ m2 → map_to_list m1 ⊆+ map_to_list m2.
Admitted.
Lemma map_to_list_fmap {A B} (f : A → B) (m : M A) :
  map_to_list (f <$> m) ≡ₚ prod_map id f <$> map_to_list m.
Admitted.

Lemma map_to_list_empty_iff {A} (m : M A) : map_to_list m = [] ↔ m = ∅.
Admitted.

Lemma map_to_list_insert_inv {A} (m : M A) l i x :
  map_to_list m ≡ₚ (i,x) :: l → m = <[i:=x]>(list_to_map l).
Admitted.

Lemma map_to_list_length {A} (m : M A) :
  length (map_to_list m) = size m.
Admitted.

Lemma map_choose {A} (m : M A) : m ≠ ∅ → ∃ i x, m !! i = Some x.
Admitted.

Global Instance map_eq_dec_empty {A} (m : M A) : Decision (m = ∅) | 20.
Admitted.

Lemma map_choose_or_empty {A} (m : M A) : (∃ i x, m !! i = Some x) ∨ m = ∅.
Admitted.

 
Lemma map_lookup_imap {A B} (f : K → A → option B) (m : M A) i :
  map_imap f m !! i = m !! i ≫= f i.
Admitted.

Lemma map_imap_Some {A} (m : M A) : map_imap (λ _, Some) m = m.
Admitted.

Lemma map_imap_insert {A B} (f : K → A → option B) i x (m : M A) :
  map_imap f (<[i:=x]> m) =
    (match f i x with Some y => <[i:=y]> | None => delete i end) (map_imap f m).
Admitted.
Lemma map_imap_insert_Some {A B} (f : K → A → option B) i x (m : M A) y :
  f i x = Some y → map_imap f (<[i:=x]> m) = <[i:=y]> (map_imap f m).
Admitted.
Lemma map_imap_insert_None {A B} (f : K → A → option B) i x (m : M A) :
  f i x = None → map_imap f (<[i:=x]> m) = delete i (map_imap f m).
Admitted.

Lemma map_imap_delete {A B} (f : K → A → option B) (m : M A) (i : K) :
  map_imap f (delete i m) = delete i (map_imap f m).
Admitted.

Lemma map_imap_ext {A1 A2 B} (f1 : K → A1 → option B)
    (f2 : K → A2 → option B) (m1 : M A1) (m2 : M A2) :
  (∀ k, f1 k <$> (m1 !! k) = f2 k <$> (m2 !! k)) →
  map_imap f1 m1 = map_imap f2 m2.
Admitted.

Lemma map_imap_compose {A1 A2 B} (f1 : K → A1 → option B)
    (f2 : K → A2 → option A1) (m : M A2) :
  map_imap f1 (map_imap f2 m) = map_imap (λ k x, f2 k x ≫= f1 k) m.
Admitted.

Lemma map_imap_empty {A B} (f : K → A → option B) :
  map_imap f ∅ =@{M B} ∅.
Admitted.

 
Lemma map_size_empty {A} : size (∅ : M A) = 0.
Admitted.
Lemma map_size_empty_iff {A} (m : M A) : size m = 0 ↔ m = ∅.
Admitted.
Lemma map_size_empty_inv {A} (m : M A) : size m = 0 → m = ∅.
Admitted.
Lemma map_size_non_empty_iff {A} (m : M A) : size m ≠ 0 ↔ m ≠ ∅.
Admitted.

Lemma map_size_singleton {A} i (x : A) : size ({[ i := x ]} : M A) = 1.
Admitted.

Lemma map_size_ne_0_lookup {A} (m : M A) :
  size m ≠ 0 ↔ ∃ i, is_Some (m !! i).
Admitted.
Lemma map_size_ne_0_lookup_1 {A} (m : M A) :
  size m ≠ 0 → ∃ i, is_Some (m !! i).
Admitted.
Lemma map_size_ne_0_lookup_2 {A} (m : M A) i :
  is_Some (m !! i) → size m ≠ 0.
Admitted.

Lemma map_size_insert {A} i x (m : M A) :
  size (<[i:=x]> m) = (match m !! i with Some _ => id | None => S end) (size m).
Admitted.
Lemma map_size_insert_Some {A} i x (m : M A) :
  is_Some (m !! i) → size (<[i:=x]> m) = size m.
Admitted.
Lemma map_size_insert_None {A} i x (m : M A) :
  m !! i = None → size (<[i:=x]> m) = S (size m).
Admitted.

Lemma map_size_delete {A} i (m : M A) :
  size (delete i m) = (match m !! i with Some _ => pred | None => id end) (size m).
Admitted.
Lemma map_size_delete_Some {A} i (m : M A) :
  is_Some (m !! i) → size (delete i m) = pred (size m).
Admitted.
Lemma map_size_delete_None {A} i (m : M A) :
  m !! i = None → size (delete i m) = size m.
Admitted.

Lemma map_size_fmap {A B} (f : A -> B) (m : M A) : size (f <$> m) = size m.
Admitted.

Lemma map_size_list_to_map {A} (l : list (K * A)) :
  NoDup l.*1 →
  size (list_to_map l : M A) = length l.
Admitted.

Lemma map_subseteq_size_eq {A} (m1 m2 : M A) :
  m1 ⊆ m2 → size m2 ≤ size m1 → m1 = m2.
Admitted.

Lemma map_subseteq_size {A} (m1 m2 : M A) : m1 ⊆ m2 → size m1 ≤ size m2.
Admitted.

Lemma map_subset_size {A} (m1 m2 : M A) : m1 ⊂ m2 → size m1 < size m2.
Admitted.

 
Lemma map_wf {A} : well_founded (⊂@{M A}).
Admitted.

Lemma map_ind {A} (P : M A → Prop) :
  P ∅ → (∀ i x m, m !! i = None → P m → P (<[i:=x]>m)) → ∀ m, P m.
Admitted.

 
Section set_to_map.
  Context {A : Type} `{FinSet B C}.

  Lemma lookup_set_to_map (f : B → K * A) (Y : C) i x :
    (∀ y y', y ∈ Y → y' ∈ Y → (f y).1 = (f y').1 → y = y') →
    (set_to_map f Y : M A) !! i = Some x ↔ ∃ y, y ∈ Y ∧ f y = (i,x).
Admitted.
End set_to_map.

Lemma lookup_set_to_map_id `{FinSet (K * A) C} (X : C) i x :
  (∀ i y y', (i,y) ∈ X → (i,y') ∈ X → y = y') →
  (set_to_map id X : M A) !! i = Some x ↔ (i,x) ∈ X.
Admitted.

Section map_to_set.
  Context {A : Type} `{SemiSet B C}.

  Lemma elem_of_map_to_set (f : K → A → B) (m : M A) (y : B) :
    y ∈ map_to_set (C:=C) f m ↔ ∃ i x, m !! i = Some x ∧ f i x = y.
Admitted.
  Lemma map_to_set_empty (f : K → A → B) :
    map_to_set f (∅ : M A) = (∅ : C).
Admitted.
  Lemma map_to_set_insert (f : K → A → B)(m : M A) i x :
    m !! i = None →
    map_to_set f (<[i:=x]>m) ≡@{C} {[f i x]} ∪ map_to_set f m.
Admitted.
  Lemma map_to_set_insert_L `{!LeibnizEquiv C} (f : K → A → B) (m : M A) i x :
    m !! i = None →
    map_to_set f (<[i:=x]>m) =@{C} {[f i x]} ∪ map_to_set f m.
Admitted.
End map_to_set.

Lemma elem_of_map_to_set_pair `{SemiSet (K * A) C} (m : M A) i x :
  (i,x) ∈@{C} map_to_set pair m ↔ m !! i = Some x.
Admitted.

 
Lemma map_fold_foldr {A B} (R : relation B) `{!PreOrder R} (l : list (K * A))
    (f : K → A → B → B) (b : B) m :
  (∀ j z, Proper (R ==> R) (f j z)) →
  (∀ j1 j2 z1 z2 y,
    j1 ≠ j2 → m !! j1 = Some z1 → m !! j2 = Some z2 →
    R (f j1 z1 (f j2 z2 y)) (f j2 z2 (f j1 z1 y))) →
  map_to_list m ≡ₚ l →
  R (map_fold f b m) (foldr (uncurry f) b l).
Admitted.

Lemma map_fold_empty {A B} (f : K → A → B → B) (b : B) :
  map_fold f b ∅ = b.
Admitted.

Lemma map_fold_singleton {A B} (f : K → A → B → B) (b : B) i x :
  map_fold f b {[i:=x]} = f i x b.
Admitted.

Lemma map_fold_insert {A B} (R : relation B) `{!PreOrder R}
    (f : K → A → B → B) (b : B) (i : K) (x : A) (m : M A) :
  (∀ j z, Proper (R ==> R) (f j z)) →
  (∀ j1 j2 z1 z2 y,
    j1 ≠ j2 → <[i:=x]> m !! j1 = Some z1 → <[i:=x]> m !! j2 = Some z2 →
    R (f j1 z1 (f j2 z2 y)) (f j2 z2 (f j1 z1 y))) →
  m !! i = None →
  R (map_fold f b (<[i:=x]> m)) (f i x (map_fold f b m)).
Admitted.

Lemma map_fold_insert_L {A B} (f : K → A → B → B) (b : B) (i : K) (x : A) (m : M A) :
  (∀ j1 j2 z1 z2 y,
    j1 ≠ j2 → <[i:=x]> m !! j1 = Some z1 → <[i:=x]> m !! j2 = Some z2 →
    f j1 z1 (f j2 z2 y) = f j2 z2 (f j1 z1 y)) →
  m !! i = None →
  map_fold f b (<[i:=x]> m) = f i x (map_fold f b m).
Admitted.

Lemma map_fold_delete {A B} (R : relation B) `{!PreOrder R}
    (f : K → A → B → B) (b : B) (i : K) (x : A) (m : M A) :
  (∀ j z, Proper (R ==> R) (f j z)) →
  (∀ j1 j2 z1 z2 y,
    j1 ≠ j2 → m !! j1 = Some z1 → m !! j2 = Some z2 →
    R (f j1 z1 (f j2 z2 y)) (f j2 z2 (f j1 z1 y))) →
  m !! i = Some x →
  R (map_fold f b m) (f i x (map_fold f b (delete i m))).
Admitted.

Lemma map_fold_delete_L {A B} (f : K → A → B → B) (b : B) (i : K) (x : A) (m : M A) :
  (∀ j1 j2 z1 z2 y,
    j1 ≠ j2 → m !! j1 = Some z1 → m !! j2 = Some z2 →
    f j1 z1 (f j2 z2 y) = f j2 z2 (f j1 z1 y)) →
  m !! i = Some x →
  map_fold f b m = f i x (map_fold f b (delete i m)).
Admitted.

 
Lemma map_fold_comm_acc_strong {A B} (R : relation B) `{!PreOrder R}
    (f : K → A → B → B) (g : B → B) (x : B) (m : M A) :
  (∀ j z, Proper (R ==> R) (f j z)) →
  Proper (R ==> R) g →
  (∀ j1 j2 z1 z2 y,
    j1 ≠ j2 → m !! j1 = Some z1 → m !! j2 = Some z2 →
    R (f j1 z1 (f j2 z2 y)) (f j2 z2 (f j1 z1 y))) →
  (∀ j z y, m !! j = Some z → R (f j z (g y)) (g (f j z y))) →
  R (map_fold f (g x) m) (g (map_fold f x m)).
Admitted.

Lemma map_fold_comm_acc {A} (f : K → A → A → A) (g : A → A) (x : A) (m : M A) :
  (∀ j1 j2 z1 z2 y, f j1 z1 (f j2 z2 y) = f j2 z2 (f j1 z1 y)) →
  (∀ j z y, f j z (g y) = g (f j z y)) →
  map_fold f (g x) m = g (map_fold f x m).
Admitted.

 
Section map_Forall.
  Context {A} (P : K → A → Prop).
End map_Forall.

 
Section map_Exists.
End map_Exists.

 
Section map_lookup_filter.
End map_lookup_filter.

Section map_filter_ext.
End map_filter_ext.

Section map_filter.

End map_filter.

 
Section merge.
End merge.

Section more_merge.
End more_merge.

 
Section Forall2.
End Forall2.
Lemma map_disjoint_singleton_l {A} (m: M A) i x : {[i:=x]} ##ₘ m ↔ m !! i = None.
Admitted.
Lemma map_disjoint_singleton_r {A} (m : M A) i x :
  m ##ₘ {[i := x]} ↔ m !! i = None.
Admitted.

 
Section union_with.
End union_with.
Lemma map_union_cancel_l {A} (m1 m2 m3 : M A) :
  m1 ##ₘ m3 → m2 ##ₘ m3 → m3 ∪ m1 = m3 ∪ m2 → m1 = m2.
Admitted.
Lemma map_union_cancel_r {A} (m1 m2 m3 : M A) :
  m1 ##ₘ m3 → m2 ##ₘ m3 → m1 ∪ m3 = m2 ∪ m3 → m1 = m2.
Admitted.
Lemma map_disjoint_union_l {A} (m1 m2 m3 : M A) :
  m1 ∪ m2 ##ₘ m3 ↔ m1 ##ₘ m3 ∧ m2 ##ₘ m3.
Admitted.
Lemma map_disjoint_union_r {A} (m1 m2 m3 : M A) :
  m1 ##ₘ m2 ∪ m3 ↔ m1 ##ₘ m2 ∧ m1 ##ₘ m3.
Admitted.
Lemma map_disjoint_insert_l {A} (m1 m2 : M A) i x :
  <[i:=x]>m1 ##ₘ m2 ↔ m2 !! i = None ∧ m1 ##ₘ m2.
Admitted.
Lemma map_disjoint_insert_r {A} (m1 m2 : M A) i x :
  m1 ##ₘ <[i:=x]>m2 ↔ m1 !! i = None ∧ m1 ##ₘ m2.
Admitted.

 
Lemma map_disjoint_union_list_l {A} (ms : list (M A)) (m : M A) :
  ⋃ ms ##ₘ m ↔ Forall (.##ₘ m) ms.
Admitted.
Lemma map_disjoint_union_list_r {A} (ms : list (M A)) (m : M A) :
  m ##ₘ ⋃ ms ↔ Forall (.##ₘ m) ms.
Admitted.

 
Section intersection_with.
End intersection_with.

 
Section setoid.
End setoid.

 
Section setoid_inversion.
End setoid_inversion.
End theorems.

 
Section map_seq.
End map_seq.

 
Section map_seqZ.
End map_seqZ.

Section kmap.
End kmap.

Section preimg.
End preimg.

 
Section img.

  Section leibniz.
  End leibniz.
End img.

 
Section map_compose.
End map_compose.

 
 
Ltac decompose_map_disjoint := repeat
  match goal with
  | H : _ ∪ _ ##ₘ _ |- _ => apply map_disjoint_union_l in H; destruct H
  | H : _ ##ₘ _ ∪ _ |- _ => apply map_disjoint_union_r in H; destruct H
  | H : {[ _ := _ ]} ##ₘ _ |- _ => apply map_disjoint_singleton_l in H
  | H : _ ##ₘ {[ _ := _ ]} |- _ =>  apply map_disjoint_singleton_r in H
  | H : <[_:=_]>_ ##ₘ _ |- _ => apply map_disjoint_insert_l in H; destruct H
  | H : _ ##ₘ <[_:=_]>_ |- _ => apply map_disjoint_insert_r in H; destruct H
  | H : ⋃ _ ##ₘ _ |- _ => apply map_disjoint_union_list_l in H
  | H : _ ##ₘ ⋃ _ |- _ => apply map_disjoint_union_list_r in H
  | H : ∅ ##ₘ _ |- _ => clear H
  | H : _ ##ₘ ∅ |- _ => clear H
  | H : Forall (.##ₘ _) _ |- _ => rewrite Forall_vlookup in H
  | H : Forall (.##ₘ _) [] |- _ => clear H
  | H : Forall (.##ₘ _) (_ :: _) |- _ => rewrite Forall_cons in H; destruct H
  | H : Forall (.##ₘ _) (_ :: _) |- _ => rewrite Forall_app in H; destruct H
  end.

 
Create HintDb map_disjoint discriminated.

 
Tactic Notation "simpl_map" "by" tactic3(tac) := repeat
  match goal with
  | H : context[ ∅ !! _ ] |- _ => rewrite lookup_empty in H
  | H : context[ (<[_:=_]>_) !! _ ] |- _ =>
    rewrite lookup_insert in H || rewrite lookup_insert_ne in H by tac
  | H : context[ (alter _ _ _) !! _] |- _ =>
    rewrite lookup_alter in H || rewrite lookup_alter_ne in H by tac
  | H : context[ (delete _ _) !! _] |- _ =>
    rewrite lookup_delete in H || rewrite lookup_delete_ne in H by tac
  | H : context[ {[ _ := _ ]} !! _ ] |- _ =>
    rewrite lookup_singleton in H || rewrite lookup_singleton_ne in H by tac
  | H : context[ (_ <$> _) !! _ ] |- _ => rewrite lookup_fmap in H
  | H : context[ (omap _ _) !! _ ] |- _ => rewrite lookup_omap in H
  | H : context[ lookup (A:=?A) ?i (?m1 ∪ ?m2) ] |- _ =>
    let x := mk_evar A in
    let E := fresh in
    assert ((m1 ∪ m2) !! i = Some x) as E by (clear H; by tac);
    rewrite E in H; clear E
  | |- context[ ∅ !! _ ] => rewrite lookup_empty
  | |- context[ (<[_:=_]>_) !! _ ] =>
    rewrite lookup_insert || rewrite lookup_insert_ne by tac
  | |- context[ (alter _ _ _) !! _ ] =>
    rewrite lookup_alter || rewrite lookup_alter_ne by tac
  | |- context[ (delete _ _) !! _ ] =>
    rewrite lookup_delete || rewrite lookup_delete_ne by tac
  | |- context[ {[ _ := _ ]} !! _ ] =>
    rewrite lookup_singleton || rewrite lookup_singleton_ne by tac
  | |- context[ (_ <$> _) !! _ ] => rewrite lookup_fmap
  | |- context[ (omap _ _) !! _ ] => rewrite lookup_omap
  | |- context [ lookup (A:=?A) ?i ?m ] =>
    let x := mk_evar A in
    let E := fresh in
    assert (m !! i = Some x) as E by tac;
    rewrite E; clear E
  end.

Create HintDb simpl_map discriminated.

 
Tactic Notation "simplify_map_eq" "by" tactic3(tac) :=
  decompose_map_disjoint;
  repeat match goal with
  | _ => progress simpl_map by tac
  | _ => progress simplify_eq/=
  | _ => progress simpl_option by tac
  | H : {[ _ := _ ]} !! _ = None |- _ => rewrite lookup_singleton_None in H
  | H : {[ _ := _ ]} !! _ = Some _ |- _ =>
    rewrite lookup_singleton_Some in H; destruct H
  | H1 : ?m1 !! ?i = Some ?x, H2 : ?m2 !! ?i = Some ?y |- _ =>
    let H3 := fresh in
    opose proof* (lookup_weaken_inv m1 m2 i x y) as H3; [done|by tac|done|];
    clear H2; symmetry in H3
  | H1 : ?m1 !! ?i = Some ?x, H2 : ?m2 !! ?i = None |- _ =>
    let H3 := fresh in
    apply (lookup_weaken _ m2) in H1; [congruence|by tac]
  | H : ?m ∪ _ = ?m ∪ _ |- _ =>
    apply map_union_cancel_l in H; [|by tac|by tac]
  | H : _ ∪ ?m = _ ∪ ?m |- _ =>
    apply map_union_cancel_r in H; [|by tac|by tac]
  | H : {[?i := ?x]} = ∅ |- _ => by destruct (map_non_empty_singleton i x)
  | H : ∅ = {[?i := ?x]} |- _ => by destruct (map_non_empty_singleton i x)
  | H : ?m !! ?i = Some _, H2 : ?m !! ?j = None |- _ =>
     unless (i ≠ j) by done;
     assert (i ≠ j) by (by intros ?; simplify_eq)
  end.
Tactic Notation "simplify_map_eq" :=
  simplify_map_eq by eauto with simpl_map map_disjoint.
Module Export stdpp_DOT_gmap_WRAPPED.
Module Export gmap.
Export stdpp.countable.

Local Open Scope positive_scope.

Local Notation "P ~ 0" := (λ p, P p~0) : function_scope.
Local Notation "P ~ 1" := (λ p, P p~1) : function_scope.

Inductive gmap_dep_ne (A : Type) (P : positive → Prop) :=
  | GNode001 : gmap_dep_ne A P~1  → gmap_dep_ne A P
  | GNode010 : P 1 → A → gmap_dep_ne A P
  | GNode011 : P 1 → A → gmap_dep_ne A P~1 → gmap_dep_ne A P
  | GNode100 : gmap_dep_ne A P~0 → gmap_dep_ne A P
  | GNode101 : gmap_dep_ne A P~0 → gmap_dep_ne A P~1 → gmap_dep_ne A P
  | GNode110 : gmap_dep_ne A P~0 → P 1 → A → gmap_dep_ne A P
  | GNode111 : gmap_dep_ne A P~0 → P 1 → A → gmap_dep_ne A P~1 → gmap_dep_ne A P.

Variant gmap_dep (A : Type) (P : positive → Prop) :=
  | GEmpty : gmap_dep A P
  | GNodes : gmap_dep_ne A P → gmap_dep A P.

Record gmap_key K `{Countable K} (q : positive) :=
  GMapKey { _ : encode (A:=K) <$> decode q = Some q }.

Record gmap K `{Countable K} A := GMap { gmap_car : gmap_dep A (gmap_key K) }.
Global Instance gmap_lookup `{Countable K} {A} :
    Lookup K A (gmap K A).
Admitted.
Global Instance gmap_empty `{Countable K} {A} : Empty (gmap K A).
Admitted.
Global Instance gmap_partial_alter `{Countable K} {A} :
    PartialAlter K A (gmap K A).
Admitted.
Global Instance gmap_fmap `{Countable K} : FMap (gmap K).
Admitted.
Global Instance gmap_omap `{Countable K} : OMap (gmap K).
Admitted.
Global Instance gmap_merge `{Countable K} : Merge (gmap K).
Admitted.
Global Instance gmap_fold `{Countable K} {A} :
    MapFold K A (gmap K A).
Admitted.

Global Instance gmap_finmap `{Countable K} : FinMap K (gmap K).
Admitted.

End gmap.
Module Export stdpp.
Module Export gmap.
Include stdpp_DOT_gmap_WRAPPED.gmap.
End gmap.

Export Coq.ssr.ssreflect.

Class Dist A := dist : nat → relation A.
Notation "x ≡{ n }≡ y" := (dist n x y)
  (at level 70, n at next level, format "x  ≡{ n }≡  y").
Notation NonExpansive f := (∀ n, Proper (dist n ==> dist n) f).

Record OfeMixin A `{Equiv A, Dist A} := {
  mixin_equiv_dist (x y : A) : x ≡ y ↔ ∀ n, x ≡{n}≡ y;
  mixin_dist_equivalence n : Equivalence (@dist A _ n);
  mixin_dist_lt n m (x y : A) : x ≡{n}≡ y → m < n → x ≡{m}≡ y;
}.

Structure ofe := Ofe {
  ofe_car :> Type;
  ofe_equiv : Equiv ofe_car;
  ofe_dist : Dist ofe_car;
  ofe_mixin : OfeMixin ofe_car
}.
Global Arguments Ofe _ {_ _} _.

Global Hint Extern 0 (Equiv _) => refine (ofe_equiv _); shelve : typeclass_instances.
Global Hint Extern 0 (Dist _) => refine (ofe_dist _); shelve : typeclass_instances.
Global Arguments ofe_dist : simpl never.
Definition ofe_mixin_of' A {Ac : ofe} (f : Ac → A) : OfeMixin Ac.
exact (ofe_mixin Ac).
Defined.
Notation ofe_mixin_of A :=
  ltac:(let H := eval hnf in (ofe_mixin_of' A id) in exact H) (only parsing).

Section ofe_mixin.
  Context {A : ofe}.
  Global Instance dist_equivalence n : Equivalence (@dist A _ n).
Admitted.
End ofe_mixin.

Section ofe.
  Context {A : ofe}.
  Global Instance ofe_equivalence : Equivalence ((≡) : relation A).
Admitted.
  Global Instance dist_proper n : Proper ((≡) ==> (≡) ==> iff) (@dist A _ n).
Admitted.
End ofe.

Section product.
  Context {A B : ofe}.
Local Instance prod_dist : Dist (A * B).
exact (λ n, prod_relation (dist n) (dist n)).
Defined.

  Definition prod_ofe_mixin : OfeMixin (A * B).
Admitted.
Canonical Structure prodO : ofe.
exact (Ofe (A * B) prod_ofe_mixin).
Defined.
End product.

Section discrete_ofe.
  Context {A : Type} `{!Equiv A} (Heq : @Equivalence A (≡)).
Local Instance discrete_dist : Dist A.
exact (λ n x y, x ≡ y).
Defined.
  Definition discrete_ofe_mixin : OfeMixin A.
Admitted.
End discrete_ofe.

Notation leibnizO A := (Ofe A (@discrete_ofe_mixin _ equivL eq_equivalence)).

Notation discrete_ofe_equivalence_of A := ltac:(
  match constr:(ofe_mixin_of A) with
  | discrete_ofe_mixin ?H => exact H
  end) (only parsing).

Section option.
  Context {A : ofe}.
Local Instance option_dist : Dist (option A).
Admitted.

  Definition option_ofe_mixin : OfeMixin (option A).
Admitted.
  Canonical Structure optionO := Ofe (option A) option_ofe_mixin.
End option.

Module iris_DOT_algebra_DOT_cmra_WRAPPED.
Module Export cmra.

Class PCore (A : Type) := pcore : A → option A.

Class Op (A : Type) := op : A → A → A.
Infix "⋅" := op (at level 50, left associativity) : stdpp_scope.
Notation "(⋅)" := op (only parsing) : stdpp_scope.

Definition included {A} `{!Equiv A, !Op A} (x y : A) := ∃ z, y ≡ x ⋅ z.
Infix "≼" := included (at level 70) : stdpp_scope.

Definition opM `{!Op A} (x : A) (my : option A) :=
  match my with Some y => x ⋅ y | None => x end.
Infix "⋅?" := opM (at level 50, left associativity) : stdpp_scope.

Class ValidN (A : Type) := validN : nat → A → Prop.
Notation "✓{ n } x" := (validN n x)
  (at level 20, n at next level, format "✓{ n }  x").

Class Valid (A : Type) := valid : A → Prop.
Notation "✓ x" := (valid x) (at level 20) : stdpp_scope.

Definition includedN `{!Dist A, !Op A} (n : nat) (x y : A) := ∃ z, y ≡{n}≡ x ⋅ z.
Notation "x ≼{ n } y" := (includedN n x y)
  (at level 70, n at next level, format "x  ≼{ n }  y") : stdpp_scope.

Section mixin.
  Record CmraMixin A `{!Dist A, !Equiv A, !PCore A, !Op A, !Valid A, !ValidN A} := {

    mixin_cmra_op_ne (x : A) : NonExpansive (op x);
    mixin_cmra_pcore_ne n (x y : A) cx :
      x ≡{n}≡ y → pcore x = Some cx → ∃ cy, pcore y = Some cy ∧ cx ≡{n}≡ cy;
    mixin_cmra_validN_ne n : Proper (dist (A := A) n ==> impl) (validN n);

    mixin_cmra_valid_validN (x : A) : ✓ x ↔ ∀ n, ✓{n} x;
    mixin_cmra_validN_S n (x : A) : ✓{S n} x → ✓{n} x;

    mixin_cmra_assoc : Assoc (≡@{A}) (⋅);
    mixin_cmra_comm : Comm (≡@{A}) (⋅);
    mixin_cmra_pcore_l (x : A) cx : pcore x = Some cx → cx ⋅ x ≡ x;
    mixin_cmra_pcore_idemp (x : A) cx : pcore x = Some cx → pcore cx ≡ Some cx;
    mixin_cmra_pcore_mono (x y : A) cx :
      x ≼ y → pcore x = Some cx → ∃ cy, pcore y = Some cy ∧ cx ≼ cy;
    mixin_cmra_validN_op_l n (x y : A) : ✓{n} (x ⋅ y) → ✓{n} x;
    mixin_cmra_extend n (x y1 y2 : A) :
      ✓{n} x → x ≡{n}≡ y1 ⋅ y2 →
      { z1 : A & { z2 | x ≡ z1 ⋅ z2 ∧ z1 ≡{n}≡ y1 ∧ z2 ≡{n}≡ y2 } }
  }.
End mixin.

#[projections(primitive=no)]
Structure cmra := Cmra' {
  cmra_car :> Type;
  cmra_equiv : Equiv cmra_car;
  cmra_dist : Dist cmra_car;
  cmra_pcore : PCore cmra_car;
  cmra_op : Op cmra_car;
  cmra_valid : Valid cmra_car;
  cmra_validN : ValidN cmra_car;
  cmra_ofe_mixin : OfeMixin cmra_car;
  cmra_mixin : CmraMixin cmra_car;
}.
Global Arguments Cmra' _ {_ _ _ _ _ _} _ _.

Notation Cmra A m := (Cmra' A (ofe_mixin_of A%type) m) (only parsing).
Global Arguments cmra_op : simpl never.
Global Arguments cmra_validN : simpl never.

Global Hint Extern 0 (PCore _) => refine (cmra_pcore _); shelve : typeclass_instances.
Global Hint Extern 0 (Op _) => refine (cmra_op _); shelve : typeclass_instances.
Global Hint Extern 0 (Valid _) => refine (cmra_valid _); shelve : typeclass_instances.
Global Hint Extern 0 (ValidN _) => refine (cmra_validN _); shelve : typeclass_instances.
Coercion cmra_ofeO (A : cmra) : ofe.
exact (Ofe A (cmra_ofe_mixin A)).
Defined.
Canonical Structure cmra_ofeO.
Definition cmra_mixin_of' A {Ac : cmra} (f : Ac → A) : CmraMixin Ac.
Admitted.
Notation cmra_mixin_of A :=
  ltac:(let H := eval hnf in (cmra_mixin_of' A id) in exact H) (only parsing).

Section cmra_mixin.
  Context {A : cmra}.
  Global Instance cmra_validN_ne n : Proper (dist n ==> impl) (@validN A _ n).
Admitted.
End cmra_mixin.

Class Unit (A : Type) := ε : A.

Record UcmraMixin A `{!Dist A, !Equiv A, !PCore A, !Op A, !Valid A, !Unit A} := {
  mixin_ucmra_unit_valid : ✓ (ε : A);
  mixin_ucmra_unit_left_id : LeftId (≡@{A}) ε (⋅);
  mixin_ucmra_pcore_unit : pcore ε ≡@{option A} Some ε
}.

#[projections(primitive=no)]
Structure ucmra := Ucmra' {
  ucmra_car :> Type;
  ucmra_equiv : Equiv ucmra_car;
  ucmra_dist : Dist ucmra_car;
  ucmra_pcore : PCore ucmra_car;
  ucmra_op : Op ucmra_car;
  ucmra_valid : Valid ucmra_car;
  ucmra_validN : ValidN ucmra_car;
  ucmra_unit : Unit ucmra_car;
  ucmra_ofe_mixin : OfeMixin ucmra_car;
  ucmra_cmra_mixin : CmraMixin ucmra_car;
  ucmra_mixin : UcmraMixin ucmra_car;
}.
Global Arguments Ucmra' _ {_ _ _ _ _ _ _} _ _ _.
Notation Ucmra A m :=
  (Ucmra' A (ofe_mixin_of A%type) (cmra_mixin_of A%type) m) (only parsing).
Global Arguments ucmra_car : simpl never.

Global Hint Extern 0 (Unit _) => refine (ucmra_unit _); shelve : typeclass_instances.
Coercion ucmra_ofeO (A : ucmra) : ofe.
exact (Ofe A (ucmra_ofe_mixin A)).
Defined.
Canonical Structure ucmra_ofeO.
Coercion ucmra_cmraR (A : ucmra) : cmra.
exact (Cmra' A (ucmra_ofe_mixin A) (ucmra_cmra_mixin A)).
Defined.
Canonical Structure ucmra_cmraR.

Record RAMixin A `{Equiv A, PCore A, Op A, Valid A} := {

  ra_op_proper (x : A) : Proper ((≡) ==> (≡)) (op x);
  ra_core_proper (x y : A) cx :
    x ≡ y → pcore x = Some cx → ∃ cy, pcore y = Some cy ∧ cx ≡ cy;
  ra_validN_proper : Proper ((≡@{A}) ==> impl) valid;

  ra_assoc : Assoc (≡@{A}) (⋅);
  ra_comm : Comm (≡@{A}) (⋅);
  ra_pcore_l (x : A) cx : pcore x = Some cx → cx ⋅ x ≡ x;
  ra_pcore_idemp (x : A) cx : pcore x = Some cx → pcore cx ≡ Some cx;
  ra_pcore_mono (x y : A) cx :
    x ≼ y → pcore x = Some cx → ∃ cy, pcore y = Some cy ∧ cx ≼ cy;
  ra_valid_op_l (x y : A) : ✓ (x ⋅ y) → ✓ x
}.

Section discrete.
  Context `{!Equiv A, !PCore A, !Op A, !Valid A} (Heq : @Equivalence A (≡)).
  Context (ra_mix : RAMixin A).
  Existing Instances discrete_dist.
Local Instance discrete_validN_instance : ValidN A.
Admitted.
  Definition discrete_cmra_mixin : CmraMixin A.
Admitted.
End discrete.

Notation discreteR A ra_mix :=
  (Cmra A (discrete_cmra_mixin (discrete_ofe_equivalence_of A%type) ra_mix))
  (only parsing).

Section prod.
  Context {A B : cmra}.
Local Instance prod_op_instance : Op (A * B).
exact (λ x y, (x.1 ⋅ y.1, x.2 ⋅ y.2)).
Defined.
Local Instance prod_pcore_instance : PCore (A * B).
Admitted.
Local Instance prod_valid_instance : Valid (A * B).
Admitted.
Local Instance prod_validN_instance : ValidN (A * B).
exact (λ n x, ✓{n} x.1 ∧ ✓{n} x.2).
Defined.

  Definition prod_cmra_mixin : CmraMixin (A * B).
Admitted.
  Canonical Structure prodR := Cmra (prod A B) prod_cmra_mixin.
End prod.

Global Arguments prodR : clear implicits.

Section option.
  Context {A : cmra}.
Local Instance option_valid_instance : Valid (option A).
Admitted.
Local Instance option_validN_instance : ValidN (option A).
Admitted.
Local Instance option_pcore_instance : PCore (option A).
Admitted.
Local Instance option_op_instance : Op (option A).
Admitted.
  Lemma Some_op_opM a ma : Some a ⋅ ma = Some (a ⋅? ma).
Admitted.

  Lemma option_cmra_mixin : CmraMixin (option A).
Admitted.
  Canonical Structure optionR := Cmra (option A) option_cmra_mixin.

  Global Instance op_None_left_id : LeftId (=) None (@op (option A) _).
Admitted.

  Lemma cmra_opM_opM_assoc a mb mc : a ⋅? mb ⋅? mc ≡ a ⋅? (mb ⋅ mc).
Admitted.

  Lemma Some_includedN_opM n a b : Some a ≼{n} Some b ↔ ∃ mc, b ≡{n}≡ a ⋅? mc.
Admitted.
End option.

End cmra.

End iris_DOT_algebra_DOT_cmra_WRAPPED.
Include iris_DOT_algebra_DOT_cmra_WRAPPED.cmra.

Record agree (A : Type) : Type := {
  agree_car : list A;
  agree_not_nil : bool_decide (agree_car = []) = false
}.

Definition cmra_update {A : cmra} (x y : A) := ∀ n mz,
  ✓{n} (x ⋅? mz) → ✓{n} (y ⋅? mz).
Infix "~~>" := cmra_update (at level 70).

Module iris_DOT_algebra_DOT_dfrac_WRAPPED.
Module Export dfrac.

Inductive dfrac :=
  | DfracOwn : Qp → dfrac
  | DfracDiscarded : dfrac
  | DfracBoth : Qp → dfrac.

Declare Custom Entry dfrac.
Notation "{ dq }" := (dq) (in custom dfrac at level 1, dq constr).
Notation "" := (DfracOwn 1) (in custom dfrac).

Section dfrac.
  Canonical Structure dfracO := leibnizO dfrac.
Local Instance dfrac_valid_instance : Valid dfrac.
Admitted.
Local Instance dfrac_pcore_instance : PCore dfrac.
Admitted.
Local Instance dfrac_op_instance : Op dfrac.
Admitted.

  Definition dfrac_ra_mixin : RAMixin dfrac.
Admitted.
  Canonical Structure dfracR := discreteR dfrac dfrac_ra_mixin.

End dfrac.

End dfrac.

End iris_DOT_algebra_DOT_dfrac_WRAPPED.
Include iris_DOT_algebra_DOT_dfrac_WRAPPED.dfrac.

Structure view_rel (A : ofe) (B : ucmra) := ViewRel {
  view_rel_holds :> nat → A → B → Prop;
  view_rel_mono n1 n2 a1 a2 b1 b2 :
    view_rel_holds n1 a1 b1 →
    a1 ≡{n2}≡ a2 →
    b2 ≼{n2} b1 →
    n2 ≤ n1 →
    view_rel_holds n2 a2 b2;
  view_rel_validN n a b :
    view_rel_holds n a b → ✓{n} b;
  view_rel_unit n :
    ∃ a, view_rel_holds n a ε
}.
Global Arguments ViewRel {_ _} _ _.

Record view {A B} (rel : nat → A → B → Prop) :=
  View { view_auth_proj : option (dfrac * agree A) ; view_frag_proj : B }.
Definition view_auth {A B} {rel : view_rel A B} (dq : dfrac) (a : A) : view rel.
Admitted.
Definition view_frag {A B} {rel : view_rel A B} (b : B) : view rel.
Admitted.

Notation "●V dq a" := (view_auth dq a)
  (at level 20, dq custom dfrac at level 1, format "●V dq  a").
Notation "◯V a" := (view_frag a) (at level 20).

Section ofe.
  Context {A B : ofe} (rel : nat → A → B → Prop).
Local Instance view_equiv : Equiv (view rel).
Admitted.
Local Instance view_dist : Dist (view rel).
Admitted.

  Definition view_ofe_mixin : OfeMixin (view rel).
Admitted.
  Canonical Structure viewO := Ofe (view rel) view_ofe_mixin.
End ofe.

Section cmra.
  Context {A B} (rel : view_rel A B).
Local Instance view_valid_instance : Valid (view rel).
Admitted.
Local Instance view_validN_instance : ValidN (view rel).
Admitted.
Local Instance view_pcore_instance : PCore (view rel).
Admitted.
Local Instance view_op_instance : Op (view rel).
Admitted.

  Lemma view_cmra_mixin : CmraMixin (view rel).
Admitted.
  Canonical Structure viewR := Cmra (view rel) view_cmra_mixin.

  Lemma view_update a b a' b' :
    (∀ n bf, rel n a (b ⋅ bf) → rel n a' (b' ⋅ bf)) →
    ●V a ⋅ ◯V b ~~> ●V a' ⋅ ◯V b'.
Admitted.

End cmra.
Export stdpp.gmap.

Section ofe.
Context `{Countable K} {A : ofe}.
Local Instance gmap_dist : Dist (gmap K A).
Admitted.
Definition gmap_ofe_mixin : OfeMixin (gmap K A).
Admitted.
Canonical Structure gmapO : ofe.
exact (Ofe (gmap K A) gmap_ofe_mixin).
Defined.
End ofe.

Global Arguments gmapO _ {_ _} _.

Section cmra.
Context `{Countable K} {A : cmra}.
Local Instance gmap_unit_instance : Unit (gmap K A).
Admitted.
Local Instance gmap_op_instance : Op (gmap K A).
Admitted.
Local Instance gmap_pcore_instance : PCore (gmap K A).
Admitted.
Local Instance gmap_valid_instance : Valid (gmap K A).
Admitted.
Local Instance gmap_validN_instance : ValidN (gmap K A).
Admitted.
Lemma lookup_op m1 m2 i : (m1 ⋅ m2) !! i = m1 !! i ⋅ m2 !! i.
Admitted.

Lemma gmap_cmra_mixin : CmraMixin (gmap K A).
Admitted.
Canonical Structure gmapR := Cmra (gmap K A) gmap_cmra_mixin.

Lemma gmap_ucmra_mixin : UcmraMixin (gmap K A).
Admitted.
Canonical Structure gmapUR := Ucmra (gmap K A) gmap_ucmra_mixin.

End cmra.
Global Arguments gmapUR _ {_ _} _.
Local Definition gmap_view_fragUR (K : Type) `{Countable K} (V : cmra) : ucmra.
exact (gmapUR K (prodR dfracR V)).
Defined.

Section rel.
  Context (K : Type) `{Countable K} (V : cmra).
  Implicit Types (m : gmap K V) (k : K) (v : V) (n : nat).
  Implicit Types (f : gmap K (dfrac * V)).

  Local Definition gmap_view_rel_raw n m f :=
    map_Forall (λ k fv,
      ∃ v dq, m !! k = Some v ∧ ✓{n} (dq, v) ∧ (Some fv ≼{n} Some (dq, v))) f.

  Local Lemma gmap_view_rel_raw_mono n1 n2 m1 m2 f1 f2 :
    gmap_view_rel_raw n1 m1 f1 →
    m1 ≡{n2}≡ m2 →
    f2 ≼{n2} f1 →
    n2 ≤ n1 →
    gmap_view_rel_raw n2 m2 f2.
Admitted.

  Local Lemma gmap_view_rel_raw_valid n m f :
    gmap_view_rel_raw n m f → ✓{n} f.
Admitted.

  Local Lemma gmap_view_rel_raw_unit n :
    ∃ m, gmap_view_rel_raw n m ε.
Admitted.
Local Canonical Structure gmap_view_rel : view_rel (gmapO K V) (gmap_view_fragUR K V).
exact (ViewRel gmap_view_rel_raw gmap_view_rel_raw_mono
            gmap_view_rel_raw_valid gmap_view_rel_raw_unit).
Defined.
End rel.
Definition gmap_viewR (K : Type) `{Countable K} (V : cmra) : cmra.
exact (viewR (gmap_view_rel K V)).
Defined.

Section definitions.
  Context {K : Type} `{Countable K} {V : cmra}.
Definition gmap_view_auth (dq : dfrac) (m : gmap K V) : gmap_viewR K V.
exact (●V{dq} m).
Defined.
Definition gmap_view_frag (k : K) (dq : dfrac) (v : V) : gmap_viewR K V.
exact (◯V {[k := (dq, v)]}).
Defined.
End definitions.

Section lemmas.
  Context {K : Type} `{Countable K} {V : cmra}.
  Implicit Types (m : gmap K V) (k : K) (q : Qp) (dq : dfrac) (v : V).

  Lemma gmap_view_update m k dq v mv' v' dq' :
    (∀ n mv f,
      m !! k = Some mv →
      ✓{n} ((dq, v) ⋅? f) →
      mv ≡{n}≡ v ⋅? (snd <$> f) →
      ✓{n} ((dq', v') ⋅? f) ∧ mv' ≡{n}≡ v' ⋅? (snd <$> f)) →
    gmap_view_auth (DfracOwn 1) m ⋅ gmap_view_frag k dq v ~~>
      gmap_view_auth (DfracOwn 1) (<[k := mv']> m) ⋅ gmap_view_frag k dq' v'.
  Proof.
    intros Hup.
apply view_update=> n bf Hrel j [df va].
    rewrite lookup_op.
    destruct (decide (j = k)) as [->|Hne]; last first.
    {

      simplify_map_eq.
rewrite lookup_singleton_ne //.

      rewrite left_id.
intros Hbf.
      edestruct (Hrel j) as (mva & mdf & Hlookup & Hval & Hincl).
      {
 rewrite lookup_op lookup_singleton_ne // left_id //.
}
      naive_solver.
}
    simplify_map_eq.
rewrite lookup_singleton.

    intros Hbf.
    edestruct (Hrel k) as (mv & mdf & Hlookup & Hval & Hincl).
    {
 rewrite lookup_op lookup_singleton // Some_op_opM //.
}
    rewrite Some_includedN_opM in Hincl.
    destruct Hincl as [f' Hincl].
rewrite cmra_opM_opM_assoc in Hincl.
    set f := bf !! k ⋅ f'.

    change (bf !! k ⋅ f') with f in Hincl.
    specialize (Hup n mv f).
destruct Hup as (Hval' & Hincl').
    {
 done.
}
    {
 rewrite -Hincl.
done.
}
    {
 destruct Hincl as [_ Hincl].
simpl in Hincl.
rewrite Hincl.
      by destruct f.
}
    eexists mv', (dq' ⋅? (fst <$> f)).
split; first done.
    rewrite -Hbf.
clear Hbf.
split.
    -
 rewrite Hincl'.
destruct Hval'.
by destruct f.
    -
 rewrite Some_op_opM.
rewrite Some_includedN_opM.
      exists f'.
rewrite Hincl'.
      rewrite cmra_opM_opM_assoc.
change (bf !! k ⋅ f') with f.
      by destruct f.
  Qed.
