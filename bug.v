
(* -*- mode: coq; coq-prog-args: ("-emacs" "-w" "-ssr-search-moved" "-w" "+deprecated-instance-without-locality" "-w" "+ambiguous-paths" "-w" "+deprecated-hint-rewrite-without-locality" "-w" "-deprecated-field-instance-without-locality" "-w" "+deprecated-tactic-notation" "-w" "-deprecated-since-8.19" "-w" "-deprecated-since-8.20" "-w" "-deprecated-from-Coq" "-w" "-deprecated-dirpath-Coq" "-w" "-notation-incompatible-prefix" "-w" "-deprecated-typeclasses-transparency-without-locality" "-w" "-notation-overridden,-redundant-canonical-projection,-unknown-warning,-argument-scope-delimiter" "-w" "-deprecated-native-compiler-option,-native-compiler-disabled" "-native-compiler" "ondemand" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/src" "Perennial" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/stdpp/stdpp" "stdpp" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/stdpp/stdpp_unstable" "stdpp.unstable" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/stdpp/stdpp_bitvector" "stdpp.bitvector" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/iris/iris" "iris" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/iris/iris_deprecated" "iris.deprecated" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/iris/iris_unstable" "iris.unstable" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/iris/iris_heap_lang" "iris.heap_lang" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/coqutil/src/coqutil" "coqutil" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/Goose" "Goose" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/record-update/src" "RecordUpdate" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/coq-tactical/src" "Tactical" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/iris-named-props/src" "iris_named_props" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/new_trusted_code" "New.code" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/new_code_axioms" "New.code" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/new_partial_axioms" "New.code_axioms" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/new" "New" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-top" "Perennial.base_logic.lib.wsat") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 1066 lines to 167 lines, then from 180 lines to 368 lines, then from 373 lines to 168 lines, then from 181 lines to 855 lines, then from 857 lines to 177 lines, then from 190 lines to 549 lines, then from 554 lines to 194 lines, then from 207 lines to 743 lines, then from 748 lines to 248 lines, then from 261 lines to 446 lines, then from 451 lines to 249 lines, then from 262 lines to 842 lines, then from 847 lines to 260 lines, then from 273 lines to 624 lines, then from 624 lines to 278 lines, then from 291 lines to 478 lines, then from 483 lines to 279 lines, then from 292 lines to 558 lines, then from 563 lines to 279 lines, then from 292 lines to 689 lines, then from 694 lines to 309 lines, then from 322 lines to 1312 lines, then from 1316 lines to 426 lines, then from 439 lines to 919 lines, then from 924 lines to 474 lines, then from 487 lines to 1254 lines, then from 1259 lines to 659 lines *)
(* coqc version 9.0+alpha compiled with OCaml 4.14.1
   coqtop version runner-t7b1znuaq-project-4504-concurrent-0:/builds/coq/coq/_build/default,(HEAD detached at c04db99c8cfbe3) (c04db99c8cfbe3fa002bf604971eb5b0e09656d4)
   Expected coqc runtime on this file: 1.805 sec *)








Require Stdlib.Init.Ltac.
Require Stdlib.micromega.Lia.
Require Stdlib.Classes.Morphisms.
Require Stdlib.Classes.RelationClasses.
Require Stdlib.Lists.List.
Require Stdlib.Bool.Bool.
Require Stdlib.Setoids.Setoid.
Require Stdlib.Init.Peano.
Require Stdlib.Unicode.Utf8.
Require Stdlib.Sorting.Permutation.
Require Stdlib.Program.Basics.
Require Stdlib.Program.Syntax.
Require Stdlib.ssr.ssrfun.
Require stdpp.options.
Require stdpp.base.
Require stdpp.proof_irrel.
Require stdpp.decidable.
Require stdpp.tactics.
Require stdpp.orders.
Require Stdlib.Logic.EqdepFacts.
Require Stdlib.PArith.PArith.
Require Stdlib.NArith.NArith.
Require Stdlib.ZArith.ZArith.
Require Stdlib.QArith.QArith.
Require Stdlib.QArith.Qcanon.
Require stdpp.option.
Require stdpp.well_founded.
Require stdpp.numbers.
Require stdpp.list.
Require stdpp.list_numbers.
Require Stdlib.QArith.QArith_base.
Require stdpp.fin.
Require stdpp.countable.
Require Stdlib.Vectors.Vector.
Require stdpp.vector.
Require stdpp.finite.
Require stdpp.sets.
Require stdpp.relations.
Require stdpp.fin_sets.
Require stdpp.fin_maps.
Require stdpp.fin_map_dom.
Require stdpp.mapset.
Require stdpp.pmap.
Require Stdlib.Strings.Ascii.
Require Stdlib.Strings.String.
Require stdpp.strings.
Require stdpp.pretty.
Require stdpp.infinite.
Require stdpp.gmap.
Require stdpp.coPset.
Require Stdlib.ssr.ssreflect.
Require stdpp.listset.
Require stdpp.lexico.
Require stdpp.prelude.
Require stdpp.ssreflect.
Require iris.prelude.options.
Require iris.prelude.prelude.
Require iris.algebra.ofe.
Require iris.algebra.monoid.
Require iris.algebra.cmra.
Require iris.algebra.updates.
Require iris.algebra.local_updates.
Require iris.algebra.coPset.
Require stdpp.namespaces.
Require stdpp.hlist.
Require iris.bi.notation.
Require iris.bi.interface.
Require iris.bi.derived_connectives.
Require iris.bi.extensions.
Require iris.bi.derived_laws.
Require iris.bi.derived_laws_later.
Require stdpp.functions.
Require stdpp.gmultiset.
Require iris.algebra.big_op.
Require iris.algebra.list.
Require iris.algebra.gset.
Require iris.algebra.proofmode_classes.
Require iris.algebra.gmap.
Require iris.bi.big_op.
Require iris.algebra.excl.
Require iris.algebra.csum.
Require iris.bi.internal_eq.
Require iris.bi.plainly.
Require iris.bi.updates.
Require iris.bi.embedding.
Require iris.bi.bi.
Require stdpp.telescopes.
Require iris.bi.telescopes.
Require Ltac2.Init.
Require Ltac2.Int.
Require Ltac2.Message.
Require iris.proofmode.tactics.
Require iris.algebra.agree.
Require iris.algebra.dfrac.
Export iris.algebra.frac.
Export iris.algebra.dfrac.
Export iris.algebra.agree.






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
Global Arguments View {_ _ _} _ _.
Global Arguments view_auth_proj {_ _ _} _.
Global Arguments view_frag_proj {_ _ _} _.



Section ofe.
  Context {A B : ofe} (rel : nat → A → B → Prop).
Local Instance view_equiv : Equiv (view rel). exact (λ x y,
    view_auth_proj x ≡ view_auth_proj y ∧ view_frag_proj x ≡ view_frag_proj y). Defined.
Local Instance view_dist : Dist (view rel). exact (λ n x y,
    view_auth_proj x ≡{n}≡ view_auth_proj y ∧
    view_frag_proj x ≡{n}≡ view_frag_proj y). Defined.

  Definition view_ofe_mixin : OfeMixin (view rel).
Admitted.
  Canonical Structure viewO := Ofe (view rel) view_ofe_mixin.
End ofe.


Section cmra.
  Context {A B} (rel : view_rel A B).
Local Instance view_valid_instance : Valid (view rel). exact (λ x,
    match view_auth_proj x with
    | Some (dq, ag) =>
       ✓ dq ∧ (∀ n, ∃ a, ag ≡{n}≡ to_agree a ∧ rel n a (view_frag_proj x))
    | None => ∀ n, ∃ a, rel n a (view_frag_proj x)
    end). Defined.
Local Instance view_validN_instance : ValidN (view rel). exact (λ n x,
    match view_auth_proj x with
    | Some (dq, ag) =>
       ✓{n} dq ∧ ∃ a, ag ≡{n}≡ to_agree a ∧ rel n a (view_frag_proj x)
    | None => ∃ a, rel n a (view_frag_proj x)
    end). Defined.
Local Instance view_pcore_instance : PCore (view rel). exact (λ x,
    Some (View (core (view_auth_proj x)) (core (view_frag_proj x)))). Defined.
Local Instance view_op_instance : Op (view rel). exact (λ x y,
    View (view_auth_proj x ⋅ view_auth_proj y) (view_frag_proj x ⋅ view_frag_proj y)). Defined.

  Lemma view_cmra_mixin : CmraMixin (view rel).
Admitted.
  Canonical Structure viewR := Cmra (view rel) view_cmra_mixin.
Local Instance view_empty_instance : Unit (view rel). exact (View ε ε). Defined.
  Lemma view_ucmra_mixin : UcmraMixin (view rel).
Admitted.
  Canonical Structure viewUR := Ucmra (view rel) view_ucmra_mixin.

End cmra.
Definition view_map {A A' B B'}
    {rel : nat → A → B → Prop} {rel' : nat → A' → B' → Prop}
    (f : A → A') (g : B → B') (x : view rel) : view rel'. exact (View (prod_map id (agree_map f) <$> view_auth_proj x) (g (view_frag_proj x))). Defined.
Global Instance view_map_ne {A A' B B' : ofe}
    {rel : nat → A → B → Prop} {rel' : nat → A' → B' → Prop}
    (f : A → A') (g : B → B') `{Hf : !NonExpansive f, Hg : !NonExpansive g} :
  NonExpansive (view_map (rel':=rel') (rel:=rel) f g).
Admitted.
Definition viewO_map {A A' B B' : ofe}
    {rel : nat → A → B → Prop} {rel' : nat → A' → B' → Prop}
    (f : A -n> A') (g : B -n> B') : viewO rel -n> viewO rel'. exact (OfeMor (view_map f g)). Defined.
Definition auth_view_rel_raw {A : ucmra} (n : nat) (a b : A) : Prop.
Admitted.
Lemma auth_view_rel_raw_mono (A : ucmra) n1 n2 (a1 a2 b1 b2 : A) :
  auth_view_rel_raw n1 a1 b1 →
  a1 ≡{n2}≡ a2 →
  b2 ≼{n2} b1 →
  n2 ≤ n1 →
  auth_view_rel_raw n2 a2 b2.
Admitted.
Lemma auth_view_rel_raw_valid (A : ucmra) n (a b : A) :
  auth_view_rel_raw n a b → ✓{n} b.
Admitted.
Lemma auth_view_rel_raw_unit (A : ucmra) n :
  ∃ a : A, auth_view_rel_raw n a ε.
Admitted.
Canonical Structure auth_view_rel {A : ucmra} : view_rel A A.
exact (ViewRel auth_view_rel_raw (auth_view_rel_raw_mono A)
          (auth_view_rel_raw_valid A) (auth_view_rel_raw_unit A)).
Defined.

Notation auth A := (view (A:=A) (B:=A) auth_view_rel_raw).
Definition authR (A : ucmra) : cmra.
exact (viewR (A:=A) (B:=A) auth_view_rel).
Defined.
Definition authUR (A : ucmra) : ucmra.
exact (viewUR (A:=A) (B:=A) auth_view_rel).
Defined.
Definition auth_auth {A: ucmra} : dfrac → A → auth A.
Admitted.
Definition auth_frag {A: ucmra} : A → auth A.
Admitted.

Notation "● dq a" := (auth_auth dq a)
  (at level 20, dq custom dfrac at level 1, format "● dq  a").
Notation "◯ a" := (auth_frag a) (at level 20).

Program Definition authURF (F : urFunctor) : urFunctor := {|
  urFunctor_car A _ B _ := authUR (urFunctor_car F A B);
  urFunctor_map A1 _ A2 _ B1 _ B2 _ fg :=
    viewO_map (urFunctor_map F fg) (urFunctor_map F fg)
|}.
Admit Obligations.

Program Definition authRF (F : urFunctor) : rFunctor := {|
  rFunctor_car A _ B _ := authR (urFunctor_car F A B);
  rFunctor_map A1 _ A2 _ B1 _ B2 _ fg :=
    viewO_map (urFunctor_map F fg) (urFunctor_map F fg)
|}.
Solve Obligations with apply authURF.

Record uPred (M : ucmra) : Type := UPred {
  uPred_holds : nat → M → Prop;

  uPred_mono n1 n2 x1 x2 :
    uPred_holds n1 x1 → x1 ≼{n2} x2 → n2 ≤ n1 → uPred_holds n2 x2
}.

Local Coercion uPred_holds : uPred >-> Funclass.
Bind Scope bi_scope with uPred.

Section cofe.
  Context {M : ucmra}.
Local Instance uPred_equiv : Equiv (uPred M).
Admitted.
Local Instance uPred_dist : Dist (uPred M).
Admitted.
  Definition uPred_ofe_mixin : OfeMixin (uPred M).
Admitted.
Canonical Structure uPredO : ofe.
exact (Ofe (uPred M) uPred_ofe_mixin).
Defined.

  Program Definition uPred_compl : Compl uPredO := λ c,
    {| uPred_holds n x := ∀ n', n' ≤ n → ✓{n'} x → c n' n' x |}.
Admit Obligations.
  Global Program Instance uPred_cofe : Cofe uPredO := {| compl := uPred_compl |}.
Admit Obligations.
End cofe.
Global Arguments uPredO : clear implicits.

Inductive uPred_entails {M} (P Q : uPred M) : Prop :=
  { uPred_in_entails : ∀ n x, ✓{n} x → P n x → Q n x }.
Global Hint Resolve uPred_mono : uPred_def.

Local Program Definition uPred_pure_def {M} (φ : Prop) : uPred M :=
  {| uPred_holds n x := φ |}.
Solve Obligations with done.
Local Definition uPred_pure_aux : seal (@uPred_pure_def).
Admitted.
Definition uPred_pure := uPred_pure_aux.(unseal).
Global Arguments uPred_pure {M}.

Local Program Definition uPred_and_def {M} (P Q : uPred M) : uPred M :=
  {| uPred_holds n x := P n x ∧ Q n x |}.
Solve Obligations with naive_solver eauto 2 with uPred_def.
Local Definition uPred_and_aux : seal (@uPred_and_def).
Admitted.
Definition uPred_and := uPred_and_aux.(unseal).
Global Arguments uPred_and {M}.

Local Program Definition uPred_or_def {M} (P Q : uPred M) : uPred M :=
  {| uPred_holds n x := P n x ∨ Q n x |}.
Solve Obligations with naive_solver eauto 2 with uPred_def.
Local Definition uPred_or_aux : seal (@uPred_or_def).
Admitted.
Definition uPred_or := uPred_or_aux.(unseal).
Global Arguments uPred_or {M}.

Local Program Definition uPred_impl_def {M} (P Q : uPred M) : uPred M :=
  {| uPred_holds n x := ∀ n' x',
       x ≼ x' → n' ≤ n → ✓{n'} x' → P n' x' → Q n' x' |}.
Admit Obligations.
Local Definition uPred_impl_aux : seal (@uPred_impl_def).
Admitted.
Definition uPred_impl := uPred_impl_aux.(unseal).
Global Arguments uPred_impl {M}.

Local Program Definition uPred_forall_def {M A} (Ψ : A → uPred M) : uPred M :=
  {| uPred_holds n x := ∀ a, Ψ a n x |}.
Solve Obligations with naive_solver eauto 2 with uPred_def.
Local Definition uPred_forall_aux : seal (@uPred_forall_def).
Admitted.
Definition uPred_forall := uPred_forall_aux.(unseal).

Local Program Definition uPred_exist_def {M A} (Ψ : A → uPred M) : uPred M :=
  {| uPred_holds n x := ∃ a, Ψ a n x |}.
Solve Obligations with naive_solver eauto 2 with uPred_def.
Local Definition uPred_exist_aux : seal (@uPred_exist_def).
Admitted.
Definition uPred_exist := uPred_exist_aux.(unseal).

Local Program Definition uPred_sep_def {M} (P Q : uPred M) : uPred M :=
  {| uPred_holds n x := ∃ x1 x2, x ≡{n}≡ x1 ⋅ x2 ∧ P n x1 ∧ Q n x2 |}.
Admit Obligations.
Local Definition uPred_sep_aux : seal (@uPred_sep_def).
Admitted.
Definition uPred_sep := uPred_sep_aux.(unseal).
Global Arguments uPred_sep {M}.

Local Program Definition uPred_wand_def {M} (P Q : uPred M) : uPred M :=
  {| uPred_holds n x := ∀ n' x',
       n' ≤ n → ✓{n'} (x ⋅ x') → P n' x' → Q n' (x ⋅ x') |}.
Admit Obligations.
Local Definition uPred_wand_aux : seal (@uPred_wand_def).
Admitted.
Definition uPred_wand := uPred_wand_aux.(unseal).
Global Arguments uPred_wand {M}.

Local Program Definition uPred_plainly_def {M} (P : uPred M) : uPred M :=
  {| uPred_holds n x := P n ε |}.
Solve Obligations with naive_solver eauto using uPred_mono, ucmra_unit_validN.

Local Program Definition uPred_persistently_def {M} (P : uPred M) : uPred M :=
  {| uPred_holds n x := P n (core x) |}.
Solve Obligations with naive_solver eauto using uPred_mono, cmra_core_monoN.
Local Definition uPred_persistently_aux : seal (@uPred_persistently_def).
Admitted.
Definition uPred_persistently := uPred_persistently_aux.(unseal).
Global Arguments uPred_persistently {M}.

Local Program Definition uPred_later_def {M} (P : uPred M) : uPred M :=
  {| uPred_holds n x := match n return _ with 0 => True | S n' => P n' x end |}.
Admit Obligations.
Local Definition uPred_later_aux : seal (@uPred_later_def).
Admitted.
Definition uPred_later := uPred_later_aux.(unseal).
Global Arguments uPred_later {M}.
Export iris.bi.derived_connectives.
Export iris.bi.updates.
Definition uPred_emp {M} : uPred M.
Admitted.

Lemma uPred_bi_mixin (M : ucmra) :
  BiMixin
    uPred_entails uPred_emp uPred_pure uPred_and uPred_or uPred_impl
    (@uPred_forall M) (@uPred_exist M) uPred_sep uPred_wand.
Admitted.

Lemma uPred_bi_persistently_mixin (M : ucmra) :
  BiPersistentlyMixin
    uPred_entails uPred_emp uPred_and
    (@uPred_exist M) uPred_sep uPred_persistently.
Admitted.

Lemma uPred_bi_later_mixin (M : ucmra) :
  BiLaterMixin
    uPred_entails uPred_pure uPred_or uPred_impl
    (@uPred_forall M) (@uPred_exist M) uPred_sep uPred_persistently uPred_later.
Admitted.
Canonical Structure uPredI (M : ucmra) : bi.
exact ({| bi_ofe_mixin := ofe_mixin_of (uPred M);
     bi_bi_mixin := uPred_bi_mixin M;
     bi_bi_later_mixin := uPred_bi_later_mixin M;
     bi_bi_persistently_mixin := uPred_bi_persistently_mixin M |}).
Defined.
Global Instance uPred_bi_bupd M : BiBUpd (uPredI M).
Admitted.
Import iris.algebra.gmap.

Structure gFunctor := GFunctor {
  gFunctor_F :> rFunctor;
  gFunctor_map_contractive : rFunctorContractive gFunctor_F;
}.

Record gFunctors := GFunctors {
  gFunctors_len : nat;
  gFunctors_lookup : fin gFunctors_len → gFunctor
}.

Definition gid (Σ : gFunctors) := fin (gFunctors_len Σ).

Definition gname := positive.
Definition iResUR (Σ : gFunctors) : ucmra.
Admitted.
  Notation iProp Σ := (uPred (iResUR Σ)).
  Notation iPropO Σ := (uPredO (iResUR Σ)).

Class inG (Σ : gFunctors) (A : cmra) := InG {
  inG_id : gid Σ;
  inG_apply := rFunctor_apply (gFunctors_lookup Σ inG_id);
  inG_prf : A = inG_apply (iPropO Σ) _;
}.
Local Definition own_def `{!inG Σ A} (γ : gname) (a : A) : iProp Σ.
Admitted.
Local Definition own_aux : seal (@own_def).
Admitted.
Definition own := own_aux.(unseal).
Global Arguments own {Σ A _} γ a.

Section cmra_mlist.

  Context (A: Type) `{EqDecision A}.
  Implicit Types (D: list A).

  Inductive mlist :=
    | MList D : mlist
    | MListBot : mlist.

  Inductive mlist_equiv : Equiv mlist :=
    | MList_equiv D1 D2:
        D1 = D2 → MList D1 ≡ MList D2
    | MListBot_equiv : MListBot ≡ MListBot.

  Existing Instance mlist_equiv.
  Local Instance mlist_equiv_Equivalence : @Equivalence mlist equiv.
Admitted.
Canonical Structure mlistC : ofe.
exact (discreteO mlist).
Defined.
Local Instance mlist_valid : Valid mlist.
Admitted.
Local Instance mlist_op : Op mlist.
Admitted.
Local Instance mlist_PCore : PCore mlist.
Admitted.
Local Instance mlist_unit : Unit mlist.
Admitted.

  Definition mlist_ra_mixin : RAMixin mlist.
Admitted.

  Canonical Structure mlistR := discreteR mlist mlist_ra_mixin.

  Definition mlist_ucmra_mixin : UcmraMixin mlist.
Admitted.

  Canonical Structure mlistUR :=
    Ucmra mlist mlist_ucmra_mixin.

End cmra_mlist.

Global Arguments MList {_} _.

Definition fmlistUR (A: Type) {Heq: EqDecision A} := authUR (mlistUR A).
Class fmlistG (A: Type) {Heq: EqDecision A} Σ :=
  { #[global] fmlist_inG :: inG Σ (fmlistUR A) }.

Section fmlist_props.
Context `{fmlistG A Σ}.
Definition fmlist_lb γ l := own γ (◯ (MList l)).
Definition fmlist_idx γ i a := (∃ l, ⌜ l !! i = Some a ⌝ ∗ fmlist_lb γ l)%I.

End fmlist_props.
Local Instance nat_valid_instance : Valid nat.
Admitted.
Local Instance nat_pcore_instance : PCore nat.
Admitted.
Local Instance nat_op_instance : Op nat.
Admitted.
  Lemma nat_ra_mixin : RAMixin nat.
Admitted.
Canonical Structure natR : cmra.
exact (discreteR nat nat_ra_mixin).
Defined.
Local Instance nat_unit_instance : Unit nat.
Admitted.
  Lemma nat_ucmra_mixin : UcmraMixin nat.
Admitted.
Canonical Structure natUR : ucmra.
exact (Ucmra nat nat_ucmra_mixin).
Defined.

Class lcGpreS (Σ : gFunctors) := LcGpreS {
  #[local] lcGpreS_inG :: inG Σ (authR natUR)
}.

Class lcGS (Σ : gFunctors) := LcGS {
  #[local] lcGS_inG :: inG Σ (authR natUR);
  lcGS_name : gname;
}.
Import iris.algebra.gset.
Import iris.algebra.coPset.
Import iris.proofmode.tactics.

Inductive bi_schema :=
| bi_sch_emp : bi_schema
| bi_sch_pure : Prop → bi_schema
| bi_sch_and : bi_schema → bi_schema → bi_schema
| bi_sch_or : bi_schema → bi_schema → bi_schema
| bi_sch_forall : ∀ A, (A → bi_schema) → bi_schema
| bi_sch_exist : ∀ A, (A → bi_schema) → bi_schema
| bi_sch_sep : bi_schema → bi_schema → bi_schema
| bi_sch_wand : bi_schema → bi_schema → bi_schema
| bi_sch_persistently : bi_schema → bi_schema
| bi_sch_later : bi_schema → bi_schema
| bi_sch_bupd : bi_schema → bi_schema

| bi_sch_var_fixed : nat → bi_schema
| bi_sch_var_mut : nat → bi_schema
| bi_sch_wsat : bi_schema
| bi_sch_ownE : (nat → coPset) → bi_schema.

Canonical Structure bi_schemaO := leibnizO bi_schema.

Record invariant_level_names := { invariant_name : gname; }.

Global Instance invariant_level_names_eq_dec : EqDecision (invariant_level_names).
Admitted.
  Class invGpreS (Σ : gFunctors) : Set := WsatPreG {
    #[global] inv_inPreG :: inG Σ (authR (gmapUR positive
                                    (prodR (agreeR (prodO (listO (laterO (iPropO Σ))) bi_schemaO))
                                           (optionR (prodR fracR (agreeR (listO (laterO (iPropO Σ)))))))));
    #[global] enabled_inPreG :: inG Σ coPset_disjR;
    #[global] disabled_inPreG :: inG Σ (gset_disjR positive);
    #[global] mlist_inPreG :: fmlistG (invariant_level_names) Σ;
    inv_lcPreG : lcGpreS Σ;
  }.

  Class invGS (Σ : gFunctors) : Set := WsatG {
    #[global] inv_inG :: invGpreS Σ;
    #[global] invGS_lc :: lcGS Σ;
    inv_list_name : gname;
    enabled_name : gname;
    disabled_name : gname;
  }.

Definition invariant_unfold {Σ} {n} sch (Ps : vec (iProp Σ) n) : agree (list (later (iPropO Σ)) * bi_schema) :=
  to_agree ((λ P, Next P) <$> (vec_to_list Ps), sch).
Definition inv_mut_unfold {Σ} {n} q (Ps : vec (iProp Σ) n) : option (frac * (agree (list (later (iPropO Σ))))) :=
  Some (q%Qp, to_agree ((λ P, Next P) <$> (vec_to_list Ps))).
Definition ownI `{!invGS Σ} {n} (lvl: nat) (i : positive) (sch: bi_schema) (Ps : vec (iProp Σ) n) : iProp Σ :=
  (∃ γs, fmlist_idx inv_list_name lvl γs ∗
         own (invariant_name γs) (◯ {[ i := (invariant_unfold sch Ps, ε) ]})).

Definition ownI_mut `{!invGS Σ} {n} (lvl: nat) (i : positive) q (Qs : vec (iProp Σ) n) : iProp Σ :=
  (∃ (l: agree (list (later (iPropO Σ)) * bi_schema)) γs, fmlist_idx inv_list_name lvl γs ∗
         own (invariant_name γs) (◯ {[ i := (l, inv_mut_unfold q Qs) ]})).
Definition ownE `{!invGS Σ} (E : coPset) : iProp Σ.
Admitted.
Definition ownD `{!invGS Σ} (E : gset positive) : iProp Σ.
Admitted.

Definition inv_cmra_fmap `{!invGS Σ} (v: (list (iProp Σ) * bi_schema) * list (iProp Σ)) :=
  let '((Ps, sch), Qs) := v in
  (invariant_unfold sch (list_to_vec Ps), inv_mut_unfold 1%Qp (list_to_vec Qs)).

Fixpoint bi_schema_pre `{!invGS Σ} n (Ps Ps_mut: list (iProp Σ)) wsat (sch: bi_schema) :=
  match sch with
  | bi_sch_emp => emp
  | bi_sch_pure φ => ⌜φ⌝
  | bi_sch_and sch1 sch2 => bi_schema_pre n Ps Ps_mut wsat sch1 ∧ bi_schema_pre n Ps Ps_mut wsat sch2
  | bi_sch_or sch1 sch2 => bi_schema_pre n Ps Ps_mut wsat sch1 ∨ bi_schema_pre n Ps Ps_mut wsat sch2
  | bi_sch_forall A sch => ∀ (a: A),  bi_schema_pre n Ps Ps_mut wsat (sch a)
  | bi_sch_exist A sch => ∃ (a: A),  bi_schema_pre n Ps Ps_mut wsat (sch a)
  | bi_sch_sep sch1 sch2 => bi_schema_pre n Ps Ps_mut wsat sch1 ∗ bi_schema_pre n Ps Ps_mut wsat sch2
  | bi_sch_wand sch1 sch2 => bi_schema_pre n Ps Ps_mut wsat sch1 -∗ bi_schema_pre n Ps Ps_mut wsat sch2
  | bi_sch_persistently sch => <pers> bi_schema_pre n Ps Ps_mut wsat sch
  | bi_sch_later sch => ▷ bi_schema_pre n Ps Ps_mut wsat sch
  | bi_sch_bupd sch => |==> bi_schema_pre n Ps Ps_mut wsat sch
  | bi_sch_var_fixed i =>
    match (Ps !! i) with
    | None => emp
    | Some P => P
    end
  | bi_sch_var_mut i =>
    match (Ps_mut !! i) with
    | None => emp
    | Some P => P
    end
  | bi_sch_wsat => wsat
  | bi_sch_ownE E => ownE (E n)
  end%I.

Definition wsat_pre `{!invGS Σ} n bi_schema_interp :=
  (∃ I : gmap positive ((list (iProp Σ) * bi_schema) * list (iProp Σ)),
        (∃ γs, fmlist_idx inv_list_name n γs ∗
             own (invariant_name γs) (● (inv_cmra_fmap <$> I : gmap _ _))) ∗
        [∗ map] i ↦ Qs ∈ I, (bi_schema_interp (bi_later <$> Qs.1.1) (bi_later <$> Qs.2) Qs.1.2 ∗
                             ownI_mut n i (1/2)%Qp (list_to_vec Qs.2) ∗
                             ownD {[i]}) ∨
                            ownE {[i]})%I.

Fixpoint bi_schema_interp `{!invGS Σ} n (Ps Ps_mut: list (iProp Σ)) sch {struct n} :=
  match n with
  | O => bi_schema_pre O Ps Ps_mut True%I sch
  | S n' => bi_schema_pre (S n') Ps Ps_mut (wsat_pre n' (bi_schema_interp n') ∗ wsat n')%I sch
  end
  with
  wsat `{!invGS Σ} n :=
  match n with
    | S n =>
  (∃ I : gmap positive ((list (iProp Σ) * bi_schema) * list (iProp Σ)),
        (∃ γs, fmlist_idx inv_list_name n γs ∗
             own (invariant_name γs) (● (inv_cmra_fmap <$> I : gmap _ _))) ∗
        [∗ map] i ↦ Qs ∈ I, (bi_schema_interp n (bi_later <$> Qs.1.1) (bi_later <$> Qs.2) Qs.1.2 ∗
                             ownI_mut n i (1/2)%Qp (list_to_vec Qs.2) ∗
                             ownD {[i]}) ∨
                            ownE {[i]})
    ∗ wsat n
    | O => True
  end%I.

Section wsat.
Context `{!invGS Σ}.

Lemma ownI_alloc {n m} φ sch lvl (Ps: vec _ n) (Ps_mut: vec _ m):
  (∀ E : gset positive, ∃ i, i ∉ E ∧ φ i) →
  wsat (S lvl) ∗
  bi_schema_interp lvl (bi_later <$> (vec_to_list Ps)) (bi_later <$> (vec_to_list Ps_mut)) sch ==∗
  ∃ i, ⌜φ i⌝ ∗ wsat (S lvl) ∗ ownI lvl i sch Ps ∗ ownI_mut lvl i (1/2)%Qp Ps_mut.
Admitted.

End wsat.

Section schema_test_mut.
Context `{!invGS Σ}.
Definition bi_sch_bupd_factory (Q P: bi_schema) : bi_schema.
Admitted.

Definition ownI_full_bupd_factory lvl i q Q P :=
  (∃ n (Qs: vec _ n), ownI lvl i (bi_sch_bupd_factory (bi_sch_var_mut O) (bi_sch_var_fixed O)) (list_to_vec [P]) ∗
   ownI_mut lvl i q Qs ∗ ⌜ default True%I (vec_to_list Qs !! 0) = Q ⌝)%I.

Lemma ownI_bupd_factory_alloc lvl φ Q P :
  (∀ E : gset positive, ∃ i, i ∉ E ∧ φ i) →
  wsat (S lvl) ∗ (▷ Q ∗ □ (▷ Q ==∗ ▷ Q ∗ ▷ P))
       ==∗ ∃ i, ⌜φ i⌝ ∗ wsat (S lvl) ∗ ownI_full_bupd_factory lvl i (1/2)%Qp Q P.
Proof.
  iIntros (?) "(Hw&(HQ&#Hfactory))".
iMod (ownI_alloc with "[$Hw HQ]") as (i) "(?&?&?&?)"; eauto; last first.
  {
 iModIntro.
iExists i.
iFrame.
instantiate (1:= list_to_vec [Q]).
rewrite //=.
}
  repeat (rewrite ?bi_schema_interp_unfold //=).
