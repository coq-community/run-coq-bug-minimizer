(* -*- mode: coq; coq-prog-args: ("-emacs" "-w" "-ssr-search-moved" "-w" "-deprecated-hint-without-locality" "-w" "-deprecated-instance-without-locality" "-w" "-deprecated-hint-rewrite-without-locality" "-w" "-deprecated-typeclasses-transparency-without-locality" "-w" "+deprecated-tactic-notation" "-w" "-notation-overridden,-redundant-canonical-projection" "-w" "-deprecated-native-compiler-option,-native-compiler-disabled" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/src" "Perennial" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/stdpp/theories" "stdpp" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/iris/iris" "iris" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/iris/iris_deprecated" "iris.deprecated" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/iris/iris_staging" "iris.staging" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/iris/iris_heap_lang" "iris.heap_lang" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/coqutil/src/coqutil" "coqutil" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/Goose" "Goose" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/record-update/src" "RecordUpdate" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/coq-tactical/src" "Tactical" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/iris-named-props/src" "iris_named_props" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-top" "class_instances" "-native-compiler" "ondemand") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 1111 lines to 19 lines, then from 32 lines to 197 lines, then from 202 lines to 19 lines, then from 32 lines to 785 lines, then from 789 lines to 28 lines, then from 41 lines to 141 lines, then from 146 lines to 28 lines, then from 41 lines to 1746 lines, then from 1749 lines to 51 lines, then from 64 lines to 170 lines, then from 175 lines to 55 lines, then from 68 lines to 239 lines, then from 244 lines to 63 lines, then from 76 lines to 548 lines, then from 553 lines to 235 lines, then from 248 lines to 453 lines, then from 457 lines to 251 lines, then from 264 lines to 2032 lines, then from 2036 lines to 291 lines, then from 304 lines to 372 lines, then from 377 lines to 293 lines, then from 306 lines to 370 lines, then from 375 lines to 338 lines *)
(* coqc version 8.16+alpha compiled with OCaml 4.13.0
   coqtop version runner-zxwgkjap-project-6138686-concurrent-0:/builds/coq/coq/_build/default,(HEAD detached at 669d0ce) (669d0ce0433b8dcea9024cb15acdead47d2b910d)
   Expected coqc runtime on this file: 0.837 sec *)
Require Coq.ssr.ssreflect.
Require Coq.Classes.Morphisms.
Require Coq.Classes.RelationClasses.
Require Coq.Lists.List.
Require Coq.Bool.Bool.
Require Coq.Setoids.Setoid.
Require Coq.Init.Peano.
Require Coq.Unicode.Utf8.
Require Coq.Sorting.Permutation.
Require Coq.Program.Basics.
Require Coq.Program.Syntax.
Require stdpp.options.
Require stdpp.base.
Require Coq.micromega.Lia.
Require stdpp.proof_irrel.
Require stdpp.decidable.
Require stdpp.tactics.
Require stdpp.orders.
Require stdpp.option.
Require Coq.QArith.QArith_base.
Require Coq.QArith.Qcanon.
Require Coq.Logic.EqdepFacts.
Require Coq.PArith.PArith.
Require Coq.NArith.NArith.
Require Coq.ZArith.ZArith.
Require Coq.Numbers.Natural.Peano.NPeano.
Require Coq.QArith.QArith.
Require stdpp.numbers.
Require stdpp.list.
Require stdpp.list_numbers.
Require stdpp.fin.
Require stdpp.well_founded.
Require stdpp.countable.
Require stdpp.vector.
Require stdpp.finite.
Require stdpp.sets.
Require stdpp.relations.

Module Export stdpp_DOT_prelude_WRAPPED.
Module Export prelude.
Export stdpp.tactics.

End prelude.
Module Export stdpp.
Module Export prelude.
Include stdpp_DOT_prelude_WRAPPED.prelude.
End prelude.
Export Coq.ssr.ssreflect.
Export stdpp.prelude.

Class Dist A := dist : nat → relation A.
Notation "x ≡{ n }≡ y" := (dist n x y)
  (at level 70, n at next level, format "x  ≡{ n }≡  y").
Notation NonExpansive f := (∀ n, Proper (dist n ==> dist n) f).
Notation NonExpansive2 f := (∀ n, Proper (dist n ==> dist n ==> dist n) f).

Record OfeMixin A `{Equiv A, Dist A} := {
  mixin_equiv_dist (x y : A) : x ≡ y ↔ ∀ n, x ≡{n}≡ y;
  mixin_dist_equivalence n : Equivalence (@dist A _ n);
  mixin_dist_S n (x y : A) : x ≡{S n}≡ y → x ≡{n}≡ y
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

Record chain (A : ofe) := {
  chain_car :> nat → A;
  chain_cauchy n i : n ≤ i → chain_car i ≡{n}≡ chain_car n
}.

Notation Compl A := (chain A%type → A).
Class Cofe (A : ofe) := {
  compl : Compl A;
  conv_compl n c : compl c ≡{n}≡ c n;
}.

Section ofe.
  Context {A : ofe}.
  Global Instance ofe_equivalence : Equivalence ((≡) : relation A).
Admitted.
End ofe.

Reserved Notation "P ⊢ Q" (at level 99, Q at level 200, right associativity).

Reserved Notation "P ⊣⊢ Q" (at level 95, no associativity).
Reserved Notation "'⌜' φ '⌝'" (at level 1, φ at level 200, format "⌜ φ ⌝").
Reserved Notation "P ∗ Q" (at level 80, right associativity, format "P  ∗  '/' Q").
Reserved Notation "P -∗ Q"
  (at level 99, Q at level 200, right associativity,
   format "'[' P  -∗  '/' '[' Q ']' ']'").

Reserved Notation "'<pers>' P" (at level 20, right associativity).

Reserved Notation "▷ P" (at level 20, right associativity).

Reserved Notation "'<affine>' P" (at level 20, right associativity).
Reserved Notation "'<affine>?' p P" (at level 20, p at level 9, P at level 20,
   right associativity, format "'<affine>?' p  P").
Delimit Scope bi_scope with I.

Section bi_mixin.
  Context {PROP : Type} `{Dist PROP, Equiv PROP}.
  Context (bi_entails : PROP → PROP → Prop).
  Context (bi_emp : PROP).
  Context (bi_pure : Prop → PROP).
  Context (bi_and : PROP → PROP → PROP).
  Context (bi_or : PROP → PROP → PROP).
  Context (bi_impl : PROP → PROP → PROP).
  Context (bi_forall : ∀ A, (A → PROP) → PROP).
  Context (bi_exist : ∀ A, (A → PROP) → PROP).
  Context (bi_sep : PROP → PROP → PROP).
  Context (bi_wand : PROP → PROP → PROP).
  Context (bi_persistently : PROP → PROP).

  Bind Scope bi_scope with PROP.
  Local Infix "⊢" := bi_entails.
  Local Notation "'emp'" := bi_emp : bi_scope.
  Local Notation "'True'" := (bi_pure True) : bi_scope.
  Local Notation "'False'" := (bi_pure False) : bi_scope.
  Local Notation "'⌜' φ '⌝'" := (bi_pure φ%type%stdpp) : bi_scope.
  Local Infix "∧" := bi_and : bi_scope.
  Local Infix "∨" := bi_or : bi_scope.
  Local Infix "→" := bi_impl : bi_scope.
  Local Notation "∀ x .. y , P" :=
    (bi_forall _ (λ x, .. (bi_forall _ (λ y, P%I)) ..)) : bi_scope.
  Local Notation "∃ x .. y , P" :=
    (bi_exist _ (λ x, .. (bi_exist _ (λ y, P%I)) ..)) : bi_scope.
  Local Infix "∗" := bi_sep : bi_scope.
  Local Infix "-∗" := bi_wand : bi_scope.
  Local Notation "'<pers>' P" := (bi_persistently P) : bi_scope.

  Record BiMixin := {
    bi_mixin_entails_po : PreOrder bi_entails;
    bi_mixin_equiv_entails P Q : (P ≡ Q) ↔ (P ⊢ Q) ∧ (Q ⊢ P);

    bi_mixin_pure_ne n : Proper (iff ==> dist n) bi_pure;
    bi_mixin_and_ne : NonExpansive2 bi_and;
    bi_mixin_or_ne : NonExpansive2 bi_or;
    bi_mixin_impl_ne : NonExpansive2 bi_impl;
    bi_mixin_forall_ne A n :
      Proper (pointwise_relation _ (dist n) ==> dist n) (bi_forall A);
    bi_mixin_exist_ne A n :
      Proper (pointwise_relation _ (dist n) ==> dist n) (bi_exist A);
    bi_mixin_sep_ne : NonExpansive2 bi_sep;
    bi_mixin_wand_ne : NonExpansive2 bi_wand;
    bi_mixin_persistently_ne : NonExpansive bi_persistently;

    bi_mixin_pure_intro (φ : Prop) P : φ → P ⊢ ⌜ φ ⌝;
    bi_mixin_pure_elim' (φ : Prop) P : (φ → True ⊢ P) → ⌜ φ ⌝ ⊢ P;

    bi_mixin_and_elim_l P Q : P ∧ Q ⊢ P;
    bi_mixin_and_elim_r P Q : P ∧ Q ⊢ Q;
    bi_mixin_and_intro P Q R : (P ⊢ Q) → (P ⊢ R) → P ⊢ Q ∧ R;

    bi_mixin_or_intro_l P Q : P ⊢ P ∨ Q;
    bi_mixin_or_intro_r P Q : Q ⊢ P ∨ Q;
    bi_mixin_or_elim P Q R : (P ⊢ R) → (Q ⊢ R) → P ∨ Q ⊢ R;

    bi_mixin_impl_intro_r P Q R : (P ∧ Q ⊢ R) → P ⊢ Q → R;
    bi_mixin_impl_elim_l' P Q R : (P ⊢ Q → R) → P ∧ Q ⊢ R;

    bi_mixin_forall_intro {A} P (Ψ : A → PROP) : (∀ a, P ⊢ Ψ a) → P ⊢ ∀ a, Ψ a;
    bi_mixin_forall_elim {A} {Ψ : A → PROP} a : (∀ a, Ψ a) ⊢ Ψ a;

    bi_mixin_exist_intro {A} {Ψ : A → PROP} a : Ψ a ⊢ ∃ a, Ψ a;
    bi_mixin_exist_elim {A} (Φ : A → PROP) Q : (∀ a, Φ a ⊢ Q) → (∃ a, Φ a) ⊢ Q;

    bi_mixin_sep_mono P P' Q Q' : (P ⊢ Q) → (P' ⊢ Q') → P ∗ P' ⊢ Q ∗ Q';
    bi_mixin_emp_sep_1 P : P ⊢ emp ∗ P;
    bi_mixin_emp_sep_2 P : emp ∗ P ⊢ P;
    bi_mixin_sep_comm' P Q : P ∗ Q ⊢ Q ∗ P;
    bi_mixin_sep_assoc' P Q R : (P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R);
    bi_mixin_wand_intro_r P Q R : (P ∗ Q ⊢ R) → P ⊢ Q -∗ R;
    bi_mixin_wand_elim_l' P Q R : (P ⊢ Q -∗ R) → P ∗ Q ⊢ R;

    bi_mixin_persistently_mono P Q : (P ⊢ Q) → <pers> P ⊢ <pers> Q;

    bi_mixin_persistently_idemp_2 P : <pers> P ⊢ <pers> <pers> P;

    bi_mixin_persistently_emp_2 : emp ⊢ <pers> emp;

    bi_mixin_persistently_and_2 (P Q : PROP) :
      (<pers> P) ∧ (<pers> Q) ⊢ <pers> (P ∧ Q);
    bi_mixin_persistently_exist_1 {A} (Ψ : A → PROP) :
      <pers> (∃ a, Ψ a) ⊢ ∃ a, <pers> (Ψ a);

    bi_mixin_persistently_absorbing P Q : <pers> P ∗ Q ⊢ <pers> P;

    bi_mixin_persistently_and_sep_elim P Q : <pers> P ∧ Q ⊢ P ∗ Q;
  }.

  Context (bi_later : PROP → PROP).
  Local Notation "▷ P" := (bi_later P) : bi_scope.

  Record BiLaterMixin := {
    bi_mixin_later_ne : NonExpansive bi_later;

    bi_mixin_later_mono P Q : (P ⊢ Q) → ▷ P ⊢ ▷ Q;
    bi_mixin_later_intro P : P ⊢ ▷ P;

    bi_mixin_later_forall_2 {A} (Φ : A → PROP) : (∀ a, ▷ Φ a) ⊢ ▷ ∀ a, Φ a;
    bi_mixin_later_exist_false {A} (Φ : A → PROP) :
      (▷ ∃ a, Φ a) ⊢ ▷ False ∨ (∃ a, ▷ Φ a);
    bi_mixin_later_sep_1 P Q : ▷ (P ∗ Q) ⊢ ▷ P ∗ ▷ Q;
    bi_mixin_later_sep_2 P Q : ▷ P ∗ ▷ Q ⊢ ▷ (P ∗ Q);
    bi_mixin_later_persistently_1 P : ▷ <pers> P ⊢ <pers> ▷ P;
    bi_mixin_later_persistently_2 P : <pers> ▷ P ⊢ ▷ <pers> P;

    bi_mixin_later_false_em P : ▷ P ⊢ ▷ False ∨ (▷ False → P);
  }.
End bi_mixin.

Structure bi := Bi {
  bi_car :> Type;
  bi_dist : Dist bi_car;
  bi_equiv : Equiv bi_car;
  bi_entails : bi_car → bi_car → Prop;
  bi_emp : bi_car;
  bi_pure : Prop → bi_car;
  bi_and : bi_car → bi_car → bi_car;
  bi_or : bi_car → bi_car → bi_car;
  bi_impl : bi_car → bi_car → bi_car;
  bi_forall : ∀ A, (A → bi_car) → bi_car;
  bi_exist : ∀ A, (A → bi_car) → bi_car;
  bi_sep : bi_car → bi_car → bi_car;
  bi_wand : bi_car → bi_car → bi_car;
  bi_persistently : bi_car → bi_car;
  bi_later : bi_car → bi_car;
  bi_ofe_mixin : OfeMixin bi_car;
  bi_cofe : Cofe (Ofe bi_car bi_ofe_mixin);
  bi_bi_mixin : BiMixin bi_entails bi_emp bi_pure bi_and bi_or bi_impl bi_forall
                        bi_exist bi_sep bi_wand bi_persistently;
  bi_bi_later_mixin : BiLaterMixin bi_entails bi_pure bi_or bi_impl
                                   bi_forall bi_exist bi_sep bi_persistently bi_later;
}.
Bind Scope bi_scope with bi_car.
Coercion bi_ofeO (PROP : bi) : ofe.
exact (Ofe PROP (bi_ofe_mixin PROP)).
Defined.
Canonical Structure bi_ofeO.
Global Arguments bi_entails {PROP} _ _ : simpl never, rename.
Global Arguments bi_emp {PROP} : simpl never, rename.
Global Arguments bi_pure {PROP} _%stdpp : simpl never, rename.
Global Arguments bi_and {PROP} _ _ : simpl never, rename.
Global Arguments bi_impl {PROP} _ _ : simpl never, rename.
Global Arguments bi_forall {PROP _} _%I : simpl never, rename.

Global Instance bi_rewrite_relation (PROP : bi) : RewriteRelation (@bi_entails PROP) | 170 := {}.

Notation "P ⊢ Q" := (bi_entails P%I Q%I) : stdpp_scope.
Notation "(⊢)" := bi_entails (only parsing) : stdpp_scope.

Notation "P ⊣⊢ Q" := (equiv (A:=bi_car _) P%I Q%I) : stdpp_scope.
Notation "(⊣⊢)" := (equiv (A:=bi_car _)) (only parsing) : stdpp_scope.

Notation "P -∗ Q" := (P ⊢ Q) : stdpp_scope.

Notation "'emp'" := (bi_emp) : bi_scope.
Notation "'⌜' φ '⌝'" := (bi_pure φ%type%stdpp) : bi_scope.
Infix "∧" := bi_and : bi_scope.
Infix "→" := bi_impl : bi_scope.
Notation "∀ x .. y , P" :=
  (bi_forall (λ x, .. (bi_forall (λ y, P%I)) ..)) : bi_scope.
Section bi_laws.
Context {PROP : bi}.

Global Instance entails_po : PreOrder (@bi_entails PROP).
Admitted.
End bi_laws.

Definition bi_affinely {PROP : bi} (P : PROP) : PROP := emp ∧ P.
Notation "'<affine>' P" := (bi_affinely P) : bi_scope.

Class Affine {PROP : bi} (Q : PROP) := affine : Q ⊢ emp.
Definition bi_affinely_if {PROP : bi} (p : bool) (P : PROP) : PROP.
exact ((if p then <affine> P else P)%I).
Defined.
Notation "'<affine>?' p P" := (bi_affinely_if p P) : bi_scope.

Class BiAffine (PROP : bi) := absorbing_bi (Q : PROP) : Affine Q.
Global Existing Instance absorbing_bi | 0.
Section derived.
Context {PROP : bi}.
Implicit Types P Q R : PROP.

Global Instance entails_proper :
  Proper ((⊣⊢) ==> (⊣⊢) ==> iff) ((⊢) : relation PROP).
Admitted.
Global Instance impl_proper :
  Proper ((⊣⊢) ==> (⊣⊢) ==> (⊣⊢)) (@bi_impl PROP).
Admitted.
Global Instance impl_mono' :
  Proper (flip (⊢) ==> (⊢) ==> (⊢)) (@bi_impl PROP).
Admitted.

Lemma pure_impl_forall φ P : (⌜φ⌝ → P) ⊣⊢ (∀ _ : φ, P).
Admitted.

Lemma affine_affinely P `{!Affine P} : <affine> P ⊣⊢ P.
Admitted.

Lemma affinely_affinely_if p P : <affine> P ⊢ <affine>?p P.
Admitted.

End derived.

Class FromPure {PROP : bi} (a : bool) (P : PROP) (φ : Prop) :=
  from_pure : <affine>?a ⌜φ⌝ ⊢ P.

Class FromPureT {PROP : bi} (a : bool) (P : PROP) (φ : Type) :=
  from_pureT : ∃ ψ : Prop, φ = ψ ∧ FromPure a P ψ.

Class IntoForall {PROP : bi} {A} (P : PROP) (Φ : A → PROP) :=
  into_forall : P ⊢ ∀ x, Φ x.
Context {PROP : bi}.
Implicit Types P Q R : PROP.

Global Instance into_forall_impl_pure a φ P Q :
  FromPureT a P φ →
  TCOr (TCEq a false) (BiAffine PROP) →
  IntoForall (P → Q) (λ _ : φ, Q).
Proof.
  rewrite /FromPureT /FromPure /IntoForall=> -[φ' [-> <-]] [->|?] /=.
  -
 by rewrite pure_impl_forall.
  -
 by rewrite -affinely_affinely_if affine_affinely pure_impl_forall.
Qed.
