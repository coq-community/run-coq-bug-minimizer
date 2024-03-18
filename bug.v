
(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "-notation-overridden" "-w" "-redundant-canonical-projection" "-w" "-unknown-warning" "-w" "-argument-scope-delimiter" "-w" "-deprecated-native-compiler-option" "-native-compiler" "ondemand" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/iris/iris/prelude" "iris.prelude" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/iris/iris/algebra" "iris.algebra" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/iris/iris/si_logic" "iris.si_logic" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/iris/iris/bi" "iris.bi" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/iris/iris/proofmode" "iris.proofmode" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/iris/iris/base_logic" "iris.base_logic" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/iris/iris/program_logic" "iris.program_logic" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/iris/iris_heap_lang" "iris.heap_lang" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/iris/iris_unstable" "iris.unstable" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/iris/iris_deprecated" "iris.deprecated" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Autosubst" "Autosubst" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/stdpp" "stdpp" "-top" "iris.algebra.lib.gmap_view") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 726 lines to 130 lines, then from 143 lines to 1002 lines, then from 1007 lines to 170 lines, then from 183 lines to 949 lines, then from 954 lines to 233 lines, then from 246 lines to 540 lines, then from 545 lines to 265 lines, then from 278 lines to 605 lines, then from 610 lines to 267 lines, then from 280 lines to 682 lines, then from 687 lines to 271 lines, then from 284 lines to 2333 lines, then from 2338 lines to 477 lines, then from 490 lines to 2487 lines, then from 2489 lines to 558 lines, then from 571 lines to 632 lines, then from 637 lines to 558 lines, then from 571 lines to 636 lines, then from 641 lines to 560 lines, then from 573 lines to 637 lines, then from 642 lines to 559 lines, then from 572 lines to 1419 lines, then from 1424 lines to 1134 lines *)
(* coqc version 8.20+alpha compiled with OCaml 4.14.1
   coqtop version runner-cabngxqim-project-4504-concurrent-1:/builds/coq/coq/_build/default,(HEAD detached at 30ed4fe1292f0) (30ed4fe1292f0d84b330fc8932e8041060152357)
   Expected coqc runtime on this file: 2.586 sec *)
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
Require Coq.Strings.Ascii.
Require Coq.Strings.String.
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
Require stdpp.strings.
Require stdpp.sets.
Require stdpp.relations.
Require stdpp.fin_sets.
Require stdpp.fin_maps.
Require stdpp.fin_map_dom.
Require stdpp.mapset.
Require stdpp.pretty.
Require stdpp.infinite.
Require stdpp.pmap.

Module Export AdmitTactic.
Module Import LocalFalse.
Inductive False : Prop := .
End LocalFalse.
Axiom proof_admitted : False.
Import Coq.Init.Ltac.
Tactic Notation "admit" := abstract case proof_admitted.
End AdmitTactic.

Module Export stdpp_DOT_gmap_WRAPPED.
Module Export gmap.
Export stdpp.countable.
Export stdpp.infinite.
Export stdpp.fin_maps.
Export stdpp.fin_map_dom.
Import stdpp.mapset.
Import stdpp.pmap.
Import stdpp.options.

Local Open Scope positive_scope.

Local Notation "P ~ 0" := (λ p, P p~0) : function_scope.
Local Notation "P ~ 1" := (λ p, P p~1) : function_scope.
Implicit Type P : positive → Prop.

 
Inductive gmap_dep_ne (A : Type) (P : positive → Prop) :=
  | GNode001 : gmap_dep_ne A P~1  → gmap_dep_ne A P
  | GNode010 : P 1 → A → gmap_dep_ne A P
  | GNode011 : P 1 → A → gmap_dep_ne A P~1 → gmap_dep_ne A P
  | GNode100 : gmap_dep_ne A P~0 → gmap_dep_ne A P
  | GNode101 : gmap_dep_ne A P~0 → gmap_dep_ne A P~1 → gmap_dep_ne A P
  | GNode110 : gmap_dep_ne A P~0 → P 1 → A → gmap_dep_ne A P
  | GNode111 : gmap_dep_ne A P~0 → P 1 → A → gmap_dep_ne A P~1 → gmap_dep_ne A P.
Global Arguments GNode001 {A P} _ : assert.
Global Arguments GNode010 {A P} _ _ : assert.
Global Arguments GNode011 {A P} _ _ _ : assert.
Global Arguments GNode100 {A P} _ : assert.
Global Arguments GNode101 {A P} _ _ : assert.
Global Arguments GNode110 {A P} _ _ _ : assert.
Global Arguments GNode111 {A P} _ _ _ _ : assert.

 
Variant gmap_dep (A : Type) (P : positive → Prop) :=
  | GEmpty : gmap_dep A P
  | GNodes : gmap_dep_ne A P → gmap_dep A P.
Global Arguments GEmpty {A P}.
Global Arguments GNodes {A P} _.

Record gmap_key K `{Countable K} (q : positive) :=
  GMapKey { _ : encode (A:=K) <$> decode q = Some q }.
Global Arguments GMapKey {_ _ _ _} _.

Lemma gmap_key_encode `{Countable K} (k : K) : gmap_key K (encode k).
Admitted.
Global Instance gmap_key_pi `{Countable K} q : ProofIrrel (gmap_key K q).
Admitted.

Record gmap K `{Countable K} A := GMap { gmap_car : gmap_dep A (gmap_key K) }.
Global Arguments GMap {_ _ _ _} _.
Global Arguments gmap_car {_ _ _ _} _.

Global Instance gmap_dep_ne_eq_dec {A P} :
  EqDecision A → (∀ i, ProofIrrel (P i)) → EqDecision (gmap_dep_ne A P).
Admitted.
Global Instance gmap_dep_eq_dec {A P} :
  (∀ i, ProofIrrel (P i)) → EqDecision A → EqDecision (gmap_dep A P).
Admitted.
Global Instance gmap_eq_dec `{Countable K} {A} :
  EqDecision A → EqDecision (gmap K A).
Admitted.

 
Local Definition GNode {A P}
    (ml : gmap_dep A P~0)
    (mx : option (P 1 * A)) (mr : gmap_dep A P~1) : gmap_dep A P :=
  match ml, mx, mr with
  | GEmpty, None, GEmpty => GEmpty
  | GEmpty, None, GNodes r => GNodes (GNode001 r)
  | GEmpty, Some (p,x), GEmpty => GNodes (GNode010 p x)
  | GEmpty, Some (p,x), GNodes r => GNodes (GNode011 p x r)
  | GNodes l, None, GEmpty => GNodes (GNode100 l)
  | GNodes l, None, GNodes r => GNodes (GNode101 l r)
  | GNodes l, Some (p,x), GEmpty => GNodes (GNode110 l p x)
  | GNodes l, Some (p,x), GNodes r => GNodes (GNode111 l p x r)
  end.

Local Definition gmap_dep_ne_case {A P B} (t : gmap_dep_ne A P)
    (f : gmap_dep A P~0 → option (P 1 * A) → gmap_dep A P~1 → B) : B :=
  match t with
  | GNode001 r => f GEmpty None (GNodes r)
  | GNode010 p x => f GEmpty (Some (p,x)) GEmpty
  | GNode011 p x r => f GEmpty (Some (p,x)) (GNodes r)
  | GNode100 l => f (GNodes l) None GEmpty
  | GNode101 l r => f (GNodes l) None (GNodes r)
  | GNode110 l p x => f (GNodes l) (Some (p,x)) GEmpty
  | GNode111 l p x r => f (GNodes l) (Some (p,x)) (GNodes r)
  end.

 
Local Definition gmap_dep_ne_lookup {A} : ∀ {P}, positive → gmap_dep_ne A P → option A :=
  fix go {P} i t {struct t} :=
  match t, i with
  | (GNode010 _ x | GNode011 _ x _ | GNode110 _ _ x | GNode111 _ _ x _), 1 => Some x
  | (GNode100 l | GNode110 l _ _ | GNode101 l _ | GNode111 l _ _ _), i~0 => go i l
  | (GNode001 r | GNode011 _ _ r | GNode101 _ r | GNode111 _ _ _ r), i~1 => go i r
  | _, _ => None
  end.
Local Definition gmap_dep_lookup {A P}
    (i : positive) (mt : gmap_dep A P) : option A :=
  match mt with GEmpty => None | GNodes t => gmap_dep_ne_lookup i t end.
Global Instance gmap_lookup `{Countable K} {A} :
    Lookup K A (gmap K A) := λ k mt,
  gmap_dep_lookup (encode k) (gmap_car mt).

Global Instance gmap_empty `{Countable K} {A} : Empty (gmap K A) := GMap GEmpty.

 
Global Opaque gmap_empty.

Local Fixpoint gmap_dep_ne_singleton {A P} (i : positive) :
    P i → A → gmap_dep_ne A P :=
  match i with
  | 1 => GNode010
  | i~0 => λ p x, GNode100 (gmap_dep_ne_singleton i p x)
  | i~1 => λ p x, GNode001 (gmap_dep_ne_singleton i p x)
  end.

Local Definition gmap_partial_alter_aux {A P}
    (go : ∀ i, P i → gmap_dep_ne A P → gmap_dep A P)
    (f : option A → option A) (i : positive) (p : P i)
    (mt : gmap_dep A P) : gmap_dep A P :=
  match mt with
  | GEmpty =>
     match f None with
     | None => GEmpty | Some x => GNodes (gmap_dep_ne_singleton i p x)
     end
  | GNodes t => go i p t
  end.
Local Definition gmap_dep_ne_partial_alter {A} (f : option A → option A) :
    ∀ {P} (i : positive), P i → gmap_dep_ne A P → gmap_dep A P :=
  Eval lazy -[gmap_dep_ne_singleton] in
  fix go {P} i p t {struct t} :=
    gmap_dep_ne_case t $ λ ml mx mr,
      match i with
      | 1 => λ p, GNode ml ((p,.) <$> f (snd <$> mx)) mr
      | i~0 => λ p, GNode (gmap_partial_alter_aux go f i p ml) mx mr
      | i~1 => λ p, GNode ml mx (gmap_partial_alter_aux go f i p mr)
      end p.
Local Definition gmap_dep_partial_alter {A P}
    (f : option A → option A) : ∀ i : positive, P i → gmap_dep A P → gmap_dep A P :=
  gmap_partial_alter_aux (gmap_dep_ne_partial_alter f) f.
Global Instance gmap_partial_alter `{Countable K} {A} :
    PartialAlter K A (gmap K A) := λ f k '(GMap mt),
  GMap $ gmap_dep_partial_alter f (encode k) (gmap_key_encode k) mt.

Local Definition gmap_dep_ne_fmap {A B} (f : A → B) :
    ∀ {P}, gmap_dep_ne A P → gmap_dep_ne B P :=
  fix go {P} t :=
    match t with
    | GNode001 r => GNode001 (go r)
    | GNode010 p x => GNode010 p (f x)
    | GNode011 p x r => GNode011 p (f x) (go r)
    | GNode100 l => GNode100 (go l)
    | GNode101 l r => GNode101 (go l) (go r)
    | GNode110 l p x => GNode110 (go l) p (f x)
    | GNode111 l p x r => GNode111 (go l) p (f x) (go r)
    end.
Local Definition gmap_dep_fmap {A B P} (f : A → B)
    (mt : gmap_dep A P) : gmap_dep B P :=
  match mt with GEmpty => GEmpty | GNodes t => GNodes (gmap_dep_ne_fmap f t) end.
Global Instance gmap_fmap `{Countable K} : FMap (gmap K) := λ {A B} f '(GMap mt),
  GMap $ gmap_dep_fmap f mt.
Local Definition gmap_dep_omap_aux {A B P}
    (go : gmap_dep_ne A P → gmap_dep B P) (tm : gmap_dep A P) : gmap_dep B P. exact (match tm with GEmpty => GEmpty | GNodes t' => go t' end). Defined.
Local Definition gmap_dep_ne_omap {A B} (f : A → option B) :
    ∀ {P}, gmap_dep_ne A P → gmap_dep B P. exact (fix go {P} t :=
    gmap_dep_ne_case t $ λ ml mx mr,
      GNode (gmap_dep_omap_aux go ml) ('(p,x) ← mx; (p,.) <$> f x)
            (gmap_dep_omap_aux go mr)). Defined.
Local Definition gmap_dep_omap {A B P} (f : A → option B) :
  gmap_dep A P → gmap_dep B P. exact (gmap_dep_omap_aux (gmap_dep_ne_omap f)). Defined.
Global Instance gmap_omap `{Countable K} : OMap (gmap K). exact (λ {A B} f '(GMap mt),
  GMap $ gmap_dep_omap f mt). Defined.
Local Definition gmap_merge_aux {A B C P}
    (go : gmap_dep_ne A P → gmap_dep_ne B P → gmap_dep C P)
    (f : option A → option B → option C)
    (mt1 : gmap_dep A P) (mt2 : gmap_dep B P) : gmap_dep C P. exact (match mt1, mt2 with
  | GEmpty, GEmpty => GEmpty
  | GNodes t1', GEmpty => gmap_dep_ne_omap (λ x, f (Some x) None) t1'
  | GEmpty, GNodes t2' => gmap_dep_ne_omap (λ x, f None (Some x)) t2'
  | GNodes t1', GNodes t2' => go t1' t2'
  end). Defined.
Local Definition diag_None' {A B C} {P : Prop}
    (f : option A → option B → option C)
    (mx : option (P * A)) (my : option (P * B)) : option (P * C). exact (match mx, my with
  | None, None => None
  | Some (p,x), None => (p,.) <$> f (Some x) None
  | None, Some (p,y) => (p,.) <$> f None (Some y)
  | Some (p,x), Some (_,y) => (p,.) <$> f (Some x) (Some y)
  end). Defined.
Local Definition gmap_dep_ne_merge {A B C} (f : option A → option B → option C) :
    ∀ {P}, gmap_dep_ne A P → gmap_dep_ne B P → gmap_dep C P. exact (fix go {P} t1 t2 {struct t1} :=
    gmap_dep_ne_case t1 $ λ ml1 mx1 mr1,
      gmap_dep_ne_case t2 $ λ ml2 mx2 mr2,
        GNode (gmap_merge_aux go f ml1 ml2) (diag_None' f mx1 mx2)
              (gmap_merge_aux go f mr1 mr2)). Defined.
Local Definition gmap_dep_merge {A B C P} (f : option A → option B → option C) :
    gmap_dep A P → gmap_dep B P → gmap_dep C P. exact (gmap_merge_aux (gmap_dep_ne_merge f) f). Defined.
Global Instance gmap_merge `{Countable K} : Merge (gmap K). exact (λ {A B C} f '(GMap mt1) '(GMap mt2), GMap $ gmap_dep_merge f mt1 mt2). Defined.
Local Definition gmap_fold_aux {A B P}
    (go : positive → B → gmap_dep_ne A P → B)
    (i : positive) (y : B) (mt : gmap_dep A P) : B. exact (match mt with GEmpty => y | GNodes t => go i y t end). Defined.
Local Definition gmap_dep_ne_fold {A B} (f : positive → A → B → B) :
    ∀ {P}, positive → B → gmap_dep_ne A P → B. exact (fix go {P} i y t :=
    gmap_dep_ne_case t $ λ ml mx mr,
      gmap_fold_aux go i~1
        (gmap_fold_aux go i~0
          match mx with None => y | Some (p,x) => f (Pos.reverse i) x y end ml) mr). Defined.
Local Definition gmap_dep_fold {A B P} (f : positive → A → B → B) :
    positive → B → gmap_dep A P → B. exact (gmap_fold_aux (gmap_dep_ne_fold f)). Defined.
Global Instance gmap_fold `{Countable K} {A} :
    MapFold K A (gmap K A). exact (λ {B} f y '(GMap mt),
  gmap_dep_fold (λ i x, match decode i with Some k => f k x | None => id end) 1 y mt). Defined.

 
Local Definition GNode_valid {A P}
    (ml : gmap_dep A P~0) (mx : option (P 1 * A)) (mr : gmap_dep A P~1) :=
  match ml, mx, mr with GEmpty, None, GEmpty => False | _, _, _ => True end.
Local Lemma gmap_dep_ind A (Q : ∀ P, gmap_dep A P → Prop) :
  (∀ P, Q P GEmpty) →
  (∀ P ml mx mr, GNode_valid ml mx mr → Q _ ml → Q _ mr → Q P (GNode ml mx mr)) →
  ∀ P mt, Q P mt.
Admitted.

Local Lemma gmap_dep_lookup_GNode {A P} (ml : gmap_dep A P~0) mr mx i :
  gmap_dep_lookup i (GNode ml mx mr) =
    match i with
    | 1 => snd <$> mx | i~0 => gmap_dep_lookup i ml | i~1 => gmap_dep_lookup i mr
    end.
Admitted.

Local Lemma gmap_dep_ne_lookup_not_None {A P} (t : gmap_dep_ne A P) :
  ∃ i, P i ∧ gmap_dep_ne_lookup i t ≠ None.
Admitted.
Local Lemma gmap_dep_eq_empty {A P} (mt : gmap_dep A P) :
  (∀ i, P i → gmap_dep_lookup i mt = None) → mt = GEmpty.
Admitted.
Local Lemma gmap_dep_eq {A P} (mt1 mt2 : gmap_dep A P) :
  (∀ i, ProofIrrel (P i)) →
  (∀ i, P i → gmap_dep_lookup i mt1 = gmap_dep_lookup i mt2) → mt1 = mt2.
Admitted.

Local Lemma gmap_dep_ne_lookup_singleton {A P} i (p : P i) (x : A) :
  gmap_dep_ne_lookup i (gmap_dep_ne_singleton i p x) = Some x.
Admitted.
Local Lemma gmap_dep_ne_lookup_singleton_ne {A P} i j (p : P i) (x : A) :
  i ≠ j → gmap_dep_ne_lookup j (gmap_dep_ne_singleton i p x) = None.
Admitted.

Local Lemma gmap_dep_partial_alter_GNode {A P} (f : option A → option A)
    i (p : P i) (ml : gmap_dep A P~0) mx mr :
  GNode_valid ml mx mr →
  gmap_dep_partial_alter f i p (GNode ml mx mr) =
    match i with
    | 1 => λ p, GNode ml ((p,.) <$> f (snd <$> mx)) mr
    | i~0 => λ p, GNode (gmap_dep_partial_alter f i p ml) mx mr
    | i~1 => λ p, GNode ml mx (gmap_dep_partial_alter f i p mr)
    end p.
Admitted.
Local Lemma gmap_dep_lookup_partial_alter {A P} (f : option A → option A)
    (mt : gmap_dep A P) i (p : P i) :
  gmap_dep_lookup i (gmap_dep_partial_alter f i p mt) = f (gmap_dep_lookup i mt).
Admitted.
Local Lemma gmap_dep_lookup_partial_alter_ne {A P} (f : option A → option A)
    (mt : gmap_dep A P) i (p : P i) j :
  i ≠ j →
  gmap_dep_lookup j (gmap_dep_partial_alter f i p mt) = gmap_dep_lookup j mt.
Admitted.

Local Lemma gmap_dep_lookup_fmap {A B P} (f : A → B) (mt : gmap_dep A P) i :
  gmap_dep_lookup i (gmap_dep_fmap f mt) = f <$> gmap_dep_lookup i mt.
Admitted.

Local Lemma gmap_dep_omap_GNode {A B P} (f : A → option B)
    (ml : gmap_dep A P~0) mx mr :
  GNode_valid ml mx mr →
  gmap_dep_omap f (GNode ml mx mr) =
    GNode (gmap_dep_omap f ml) ('(p,x) ← mx; (p,.) <$> f x) (gmap_dep_omap f mr).
Admitted.
Local Lemma gmap_dep_lookup_omap {A B P} (f : A → option B) (mt : gmap_dep A P) i :
  gmap_dep_lookup i (gmap_dep_omap f mt) = gmap_dep_lookup i mt ≫= f.
Admitted.

Section gmap_merge.
  Context {A B C} (f : option A → option B → option C).

  Local Lemma gmap_dep_merge_GNode_GEmpty {P} (ml : gmap_dep A P~0) mx mr :
    GNode_valid ml mx mr →
    gmap_dep_merge f (GNode ml mx mr) GEmpty =
      GNode (gmap_dep_omap (λ x, f (Some x) None) ml) (diag_None' f mx None)
            (gmap_dep_omap (λ x, f (Some x) None) mr).
Admitted.
  Local Lemma gmap_dep_merge_GEmpty_GNode {P} (ml : gmap_dep B P~0) mx mr :
    GNode_valid ml mx mr →
    gmap_dep_merge f GEmpty (GNode ml mx mr) =
      GNode (gmap_dep_omap (λ x, f None (Some x)) ml) (diag_None' f None mx)
            (gmap_dep_omap (λ x, f None (Some x)) mr).
Admitted.
  Local Lemma gmap_dep_merge_GNode_GNode {P}
      (ml1 : gmap_dep A P~0) ml2 mx1 mx2 mr1 mr2 :
    GNode_valid ml1 mx1 mr1 → GNode_valid ml2 mx2 mr2 →
    gmap_dep_merge f (GNode ml1 mx1 mr1) (GNode ml2 mx2 mr2) =
      GNode (gmap_dep_merge f ml1 ml2) (diag_None' f mx1 mx2)
            (gmap_dep_merge f mr1 mr2).
Admitted.

  Local Lemma gmap_dep_lookup_merge {P} (mt1 : gmap_dep A P) (mt2 : gmap_dep B P) i :
    gmap_dep_lookup i (gmap_dep_merge f mt1 mt2) =
      diag_None f (gmap_dep_lookup i mt1) (gmap_dep_lookup i mt2).
Admitted.
End gmap_merge.

Section gmap_fold.
  Context {A B} (f : positive → A → B → B).

  Local Lemma gmap_dep_fold_GNode {P} i y (ml : gmap_dep A P~0) mx mr :
    GNode_valid ml mx mr →
    gmap_dep_fold f i y (GNode ml mx mr) = gmap_dep_fold f i~1
      (gmap_dep_fold f i~0
        match mx with None => y | Some (_,x) => f (Pos.reverse i) x y end ml) mr.
Admitted.

  Local Lemma gmap_dep_fold_ind {P} (Q : B → gmap_dep A P → Prop) (b : B) j :
    Q b GEmpty →
    (∀ i p x mt r, gmap_dep_lookup i mt = None →
      Q r mt →
      Q (f (Pos.reverse_go i j) x r) (gmap_dep_partial_alter (λ _, Some x) i p mt)) →
    ∀ mt, Q (gmap_dep_fold f j b mt) mt.
Admitted.
End gmap_fold.

 
Global Instance gmap_finmap `{Countable K} : FinMap K (gmap K).
Admitted.

Global Program Instance gmap_countable
    `{Countable K, Countable A} : Countable (gmap K A) := {
  encode m := encode (map_to_list m : list (K * A));
  decode p := list_to_map <$> decode p
}.
Admit Obligations.
Local Definition gmap_dep_ne_to_pmap_ne {A} : ∀ {P}, gmap_dep_ne A P → Pmap_ne A. exact (fix go {P} t :=
    match t with
    | GNode001 r => PNode001 (go r)
    | GNode010 _ x => PNode010 x
    | GNode011 _ x r => PNode011 x (go r)
    | GNode100 l => PNode100 (go l)
    | GNode101 l r => PNode101 (go l) (go r)
    | GNode110 l _ x => PNode110 (go l) x
    | GNode111 l _ x r => PNode111 (go l) x (go r)
    end). Defined.
Local Definition gmap_dep_to_pmap {A P} (mt : gmap_dep A P) : Pmap A. exact (match mt with
  | GEmpty => PEmpty
  | GNodes t => PNodes (gmap_dep_ne_to_pmap_ne t)
  end). Defined.
Definition gmap_to_pmap {A} (m : gmap positive A) : Pmap A. exact (let '(GMap mt) := m in gmap_dep_to_pmap mt). Defined.

Local Lemma lookup_gmap_dep_ne_to_pmap_ne {A P} (t : gmap_dep_ne A P) i :
  gmap_dep_ne_to_pmap_ne t !! i = gmap_dep_ne_lookup i t.
Admitted.
Lemma lookup_gmap_to_pmap {A} (m : gmap positive A) i :
  gmap_to_pmap m !! i = m !! i.
Admitted.
Local Definition pmap_ne_to_gmap_dep_ne {A} :
    ∀ {P}, (∀ i, P i) → Pmap_ne A → gmap_dep_ne A P. exact (fix go {P} (p : ∀ i, P i) t :=
    match t with
    | PNode001 r => GNode001 (go p~1 r)
    | PNode010 x => GNode010 (p 1) x
    | PNode011 x r => GNode011 (p 1) x (go p~1 r)
    | PNode100 l => GNode100 (go p~0 l)
    | PNode101 l r => GNode101 (go p~0 l) (go p~1 r)
    | PNode110 l x => GNode110 (go p~0 l) (p 1) x
    | PNode111 l x r => GNode111 (go p~0 l) (p 1) x (go p~1 r)
    end%function). Defined.
Local Definition pmap_to_gmap_dep {A P}
    (p : ∀ i, P i) (mt : Pmap A) : gmap_dep A P. exact (match mt with
  | PEmpty => GEmpty
  | PNodes t => GNodes (pmap_ne_to_gmap_dep_ne p t)
  end). Defined.
Definition pmap_to_gmap {A} (m : Pmap A) : gmap positive A. exact (GMap $ pmap_to_gmap_dep gmap_key_encode m). Defined.

Local Lemma lookup_pmap_ne_to_gmap_dep_ne {A P} (p : ∀ i, P i) (t : Pmap_ne A) i :
  gmap_dep_ne_lookup i (pmap_ne_to_gmap_dep_ne p t) = t !! i.
Admitted.
Lemma lookup_pmap_to_gmap {A} (m : Pmap A) i : pmap_to_gmap m !! i = m !! i.
Admitted.
Definition gmap_uncurry `{Countable K1, Countable K2} {A} :
    gmap K1 (gmap K2 A) → gmap (K1 * K2) A. exact (map_fold (λ i1 m' macc,
    map_fold (λ i2 x, <[(i1,i2):=x]>) macc m') ∅). Defined.
Definition gmap_curry `{Countable K1, Countable K2} {A} :
    gmap (K1 * K2) A → gmap K1 (gmap K2 A). exact (map_fold (λ '(i1, i2) x,
    partial_alter (Some ∘ <[i2:=x]> ∘ default ∅) i1) ∅). Defined.

Section curry_uncurry.
  Context `{Countable K1, Countable K2} {A : Type}.

  Lemma lookup_gmap_uncurry (m : gmap K1 (gmap K2 A)) i j :
    gmap_uncurry m !! (i,j) = m !! i ≫= (.!! j).
Admitted.

  Lemma lookup_gmap_curry (m : gmap (K1 * K2) A) i j :
    gmap_curry m !! i ≫= (.!! j) = m !! (i, j).
Admitted.

  Lemma lookup_gmap_curry_None (m : gmap (K1 * K2) A) i :
    gmap_curry m !! i = None ↔ (∀ j, m !! (i, j) = None).
Admitted.

  Lemma gmap_uncurry_curry (m : gmap (K1 * K2) A) :
    gmap_uncurry (gmap_curry m) = m.
Admitted.

  Lemma gmap_curry_non_empty (m : gmap (K1 * K2) A) i x :
    gmap_curry m !! i = Some x → x ≠ ∅.
Admitted.

  Lemma gmap_curry_uncurry_non_empty (m : gmap K1 (gmap K2 A)) :
    (∀ i x, m !! i = Some x → x ≠ ∅) →
    gmap_curry (gmap_uncurry m) = m.
Admitted.
End curry_uncurry.

 
Definition gset K `{Countable K} := mapset (gmap K).

Section gset.
  Context `{Countable K}.
Global Instance gset_elem_of: ElemOf K (gset K). exact (_). Defined.
Global Instance gset_empty : Empty (gset K). exact (_). Defined.
Global Instance gset_singleton : Singleton K (gset K). exact (_). Defined.
Global Instance gset_union: Union (gset K). exact (_). Defined.
Global Instance gset_intersection: Intersection (gset K). exact (_). Defined.
Global Instance gset_difference: Difference (gset K). exact (_). Defined.
Global Instance gset_elements: Elements K (gset K). exact (_). Defined.
Global Instance gset_eq_dec : EqDecision (gset K). exact (_). Defined.
Global Instance gset_countable : Countable (gset K). exact (_). Defined.
Global Instance gset_equiv_dec : RelDecision (≡@{gset K}) | 1. exact (_). Defined.
Global Instance gset_elem_of_dec : RelDecision (∈@{gset K}) | 1. exact (_). Defined.
Global Instance gset_disjoint_dec : RelDecision (##@{gset K}). exact (_). Defined.
Global Instance gset_subseteq_dec : RelDecision (⊆@{gset K}). exact (_). Defined.
Global Instance gset_dom {A} : Dom (gmap K A) (gset K). exact (λ m,
    let '(GMap mt) := m in mapset_dom (GMap mt)). Defined.

  Global Arguments gset_elem_of : simpl never.
  Global Arguments gset_empty : simpl never.
  Global Arguments gset_singleton : simpl never.
  Global Arguments gset_union : simpl never.
  Global Arguments gset_intersection : simpl never.
  Global Arguments gset_difference : simpl never.
  Global Arguments gset_elements : simpl never.
  Global Arguments gset_eq_dec : simpl never.
  Global Arguments gset_countable : simpl never.
  Global Arguments gset_equiv_dec : simpl never.
  Global Arguments gset_elem_of_dec : simpl never.
  Global Arguments gset_disjoint_dec : simpl never.
  Global Arguments gset_subseteq_dec : simpl never.
  Global Arguments gset_dom : simpl never.
Global Instance gset_leibniz : LeibnizEquiv (gset K). exact (_). Defined.
Global Instance gset_semi_set : SemiSet K (gset K) | 1. exact (_). Defined.
Global Instance gset_set : Set_ K (gset K) | 1. exact (_). Defined.
Global Instance gset_fin_set : FinSet K (gset K). exact (_). Defined.
  Global Instance gset_dom_spec : FinMapDom K (gmap K) (gset K).
Admitted.
Definition gset_to_gmap {A} (x : A) (X : gset K) : gmap K A. exact ((λ _, x) <$> mapset_car X). Defined.

  Lemma lookup_gset_to_gmap {A} (x : A) (X : gset K) i :
    gset_to_gmap x X !! i = (guard (i ∈ X);; Some x).
Admitted.
  Lemma lookup_gset_to_gmap_Some {A} (x : A) (X : gset K) i y :
    gset_to_gmap x X !! i = Some y ↔ i ∈ X ∧ x = y.
Admitted.
  Lemma lookup_gset_to_gmap_None {A} (x : A) (X : gset K) i :
    gset_to_gmap x X !! i = None ↔ i ∉ X.
Admitted.

  Lemma gset_to_gmap_empty {A} (x : A) : gset_to_gmap x ∅ = ∅.
Admitted.
  Lemma gset_to_gmap_union_singleton {A} (x : A) i Y :
    gset_to_gmap x ({[ i ]} ∪ Y) = <[i:=x]>(gset_to_gmap x Y).
Admitted.
  Lemma gset_to_gmap_difference_singleton {A} (x : A) i Y :
    gset_to_gmap x (Y ∖ {[i]}) = delete i (gset_to_gmap x Y).
Admitted.

  Lemma fmap_gset_to_gmap {A B} (f : A → B) (X : gset K) (x : A) :
    f <$> gset_to_gmap x X = gset_to_gmap (f x) X.
Admitted.
  Lemma gset_to_gmap_dom {A B} (m : gmap K A) (y : B) :
    gset_to_gmap y (dom m) = const y <$> m.
Admitted.
  Lemma dom_gset_to_gmap {A} (X : gset K) (x : A) :
    dom (gset_to_gmap x X) = X.
Admitted.

  Lemma gset_to_gmap_set_to_map {A} (X : gset K) (x : A) :
    gset_to_gmap x X = set_to_map (.,x) X.
Admitted.

  Lemma map_to_list_gset_to_gmap {A} (X : gset K) (x : A) :
    map_to_list (gset_to_gmap x X) ≡ₚ (., x) <$> elements X.
Admitted.
End gset.

Global Typeclasses Opaque gset.

End gmap.

End stdpp_DOT_gmap_WRAPPED.
Module Export stdpp_DOT_gmap.
Module Export stdpp.
Module Export gmap.
Include stdpp_DOT_gmap_WRAPPED.gmap.
End gmap.

End stdpp.

End stdpp_DOT_gmap.
Export stdpp.vector.

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
