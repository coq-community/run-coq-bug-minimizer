(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "-notation-overridden" "-w" "-redundant-canonical-projection" "-w" "-deprecated-native-compiler-option" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/iris_examples/theories" "iris_examples" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Autosubst" "Autosubst" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/iris" "iris" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/stdpp" "stdpp" "-top" "Top.bug_01" "-native-compiler" "ondemand") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 81 lines to 59 lines, then from 72 lines to 296 lines, then from 301 lines to 73 lines, then from 86 lines to 644 lines, then from 649 lines to 86 lines, then from 99 lines to 483 lines, then from 488 lines to 129 lines, then from 142 lines to 619 lines, then from 624 lines to 125 lines, then from 138 lines to 893 lines, then from 898 lines to 138 lines, then from 151 lines to 623 lines, then from 628 lines to 397 lines, then from 409 lines to 177 lines, then from 190 lines to 333 lines, then from 338 lines to 202 lines, then from 215 lines to 546 lines, then from 551 lines to 220 lines, then from 233 lines to 935 lines, then from 938 lines to 273 lines, then from 286 lines to 670 lines, then from 675 lines to 610 lines *)
(* coqc version 8.18+alpha compiled with OCaml 4.14.0
   coqtop version runner-q6hytnfs-project-6138686-concurrent-0:/builds/coq/coq/_build/default,(HEAD detached at 41fd2ab) (41fd2ab2f7d875b43ff3442483386100b081bd29)
   Expected coqc runtime on this file: 14.470 sec *)
Require Coq.Program.Tactics.
Require Coq.Arith.Plus.
Require Coq.Lists.List.
Require Coq.Logic.FunctionalExtensionality.
Require Autosubst.Autosubst_Basics.
Require Autosubst.Autosubst_MMap.
Require Autosubst.Autosubst_Classes.
Require Autosubst.Autosubst_Tactics.
Require Autosubst.Autosubst_Lemmas.
Require Autosubst.Autosubst_Derive.
Require Autosubst.Autosubst_MMapInstances.
Require Autosubst.Autosubst.
Require Coq.Bool.Bool.
Require Coq.Classes.Morphisms.
Require Coq.Classes.RelationClasses.
Require Coq.Init.Byte.
Require Coq.Init.Peano.
Require Coq.Logic.EqdepFacts.
Require Coq.NArith.NArith.
Require Coq.Numbers.Natural.Peano.NPeano.
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
Require Coq.ssr.ssreflect.
Require Ltac2.Ltac2.
Require stdpp.options.
Require stdpp.base.
Require stdpp.proof_irrel.
Require stdpp.decidable.
Require stdpp.tactics.
Require stdpp.option.
Require stdpp.numbers.
Require stdpp.list.
Require stdpp.list_numbers.
Require stdpp.fin.
Require stdpp.well_founded.
Require stdpp.countable.
Require stdpp.vector.
Require stdpp.finite.
Require stdpp.orders.
Require stdpp.sets.
Require stdpp.relations.
Require stdpp.fin_sets.
Require stdpp.listset.
Require stdpp.lexico.
Require stdpp.prelude.
Require iris.prelude.options.
Require iris.prelude.prelude.
Require iris.algebra.ofe.
Require iris.algebra.monoid.
Require iris.algebra.cmra.
Require iris.algebra.agree.
Require iris.algebra.updates.
Require iris.algebra.local_updates.
Require iris.algebra.proofmode_classes.
Require iris.algebra.frac.
Require iris.algebra.dfrac.
Require stdpp.functions.
Require stdpp.strings.
Require stdpp.pretty.
Require stdpp.infinite.
Require stdpp.fin_maps.
Require stdpp.fin_map_dom.
Require stdpp.mapset.
Require stdpp.pmap.
Require stdpp.propset.
Require stdpp.gmap.
Require stdpp.gmultiset.
Require iris.algebra.big_op.
Require iris.algebra.view.
Require iris.algebra.auth.
Require stdpp.coPset.
Require iris.algebra.coPset.
Require iris.algebra.cofe_solver.
Require iris.algebra.csum.
Require iris.algebra.excl.
Require iris.algebra.functions.
Require iris.algebra.list.
Require iris.algebra.gset.
Require iris.algebra.gmap.
Require iris.algebra.lib.dfrac_agree.
Require iris.algebra.lib.excl_auth.
Require iris.algebra.lib.gmap_view.
Require iris.algebra.numbers.
Require iris.algebra.reservation_map.
Require iris.bi.notation.
Require iris.bi.interface.
Require iris.bi.derived_connectives.
Require iris.bi.extensions.
Require iris.bi.derived_laws.
Require iris.bi.derived_laws_later.
Require iris.bi.big_op.
Require iris.bi.internal_eq.
Require iris.bi.plainly.
Require iris.bi.updates.
Require iris.base_logic.upred.
Require iris.base_logic.bi.
Require iris.bi.embedding.
Require iris.bi.bi.
Require iris.base_logic.derived.
Require iris.base_logic.algebra.
Require stdpp.namespaces.
Require iris.proofmode.base.
Require iris.proofmode.ident_name.
Require iris.proofmode.modalities.
Require iris.proofmode.classes.
Require iris.base_logic.proofmode.
Require iris.base_logic.base_logic.
Require stdpp.hlist.
Require stdpp.telescopes.
Require iris.bi.telescopes.
Require iris.proofmode.tokens.
Require iris.proofmode.sel_patterns.
Require iris.proofmode.intro_patterns.
Require iris.proofmode.spec_patterns.
Require iris.proofmode.environments.
Require iris.proofmode.modality_instances.
Require iris.proofmode.coq_tactics.
Require iris.proofmode.reduction.
Require iris.proofmode.string_ident.
Require iris.proofmode.notation.
Require iris.proofmode.ltac_tactics.
Require iris.proofmode.classes_make.
Require iris.proofmode.class_instances.
Require stdpp.nat_cancel.
Require iris.proofmode.class_instances_later.
Require iris.proofmode.class_instances_updates.
Require iris.proofmode.class_instances_embedding.
Require iris.proofmode.class_instances_plainly.
Require iris.proofmode.class_instances_internal_eq.
Require iris.proofmode.class_instances_frame.
Require iris.proofmode.class_instances_make.
Require iris.proofmode.proofmode.
Require iris.base_logic.lib.iprop.
Require iris.base_logic.lib.own.
Require iris.base_logic.lib.wsat.
Require iris.proofmode.tactics.
Require iris.base_logic.lib.later_credits.
Require iris.base_logic.lib.fancy_updates.
Require iris.bi.lib.fractional.
Require iris.base_logic.lib.ghost_map.
Require iris.base_logic.lib.gen_heap.
Require iris.base_logic.lib.invariants.
Require iris.bi.weakestpre.
Require iris.program_logic.language.
Require iris.program_logic.weakestpre.
Require iris.program_logic.adequacy.
Require iris.program_logic.ectx_language.
Require iris.program_logic.lifting.
Require iris.program_logic.ectx_lifting.
Require iris.program_logic.ectxi_language.
Require iris_examples.logrel.F_mu_ref_conc.base.
Require iris_examples.logrel.F_mu_ref_conc.lang.

Declare ML Module "coq-core.plugins.ltac".
Module Export AdmitTactic.
Module Import LocalFalse.
Inductive False : Prop := .
End LocalFalse.
Axiom proof_admitted : False.
Global Set Default Proof Mode "Classic".
Tactic Notation "admit" := abstract case proof_admitted.
End AdmitTactic.

Module Export iris_examples_DOT_logrel_DOT_F_mu_ref_conc_DOT_wp_rules_WRAPPED.
Module Export wp_rules.
Export iris.program_logic.weakestpre.
Import iris.program_logic.ectx_lifting.
Export iris.base_logic.lib.invariants.
Import iris.algebra.auth.
Import iris.algebra.frac.
Import iris.algebra.agree.
Import iris.algebra.gmap.
Import iris.proofmode.proofmode.
Export iris.base_logic.lib.gen_heap.
Export iris_examples.logrel.F_mu_ref_conc.lang.
Import iris.prelude.options.

 
Class heapIG Σ := HeapIG {
  heapI_invG : invGS Σ;
  heapI_gen_heapG :> gen_heapGS loc val Σ;
}.

Global Instance heapIG_irisG `{heapIG Σ} : irisGS F_mu_ref_conc_lang Σ := {
  iris_invGS := heapI_invG;
  num_laters_per_step _ := 0;
  state_interp σ  _ _ _ := gen_heap_interp σ;
  fork_post _ := True%I;
  state_interp_mono _ _ _ _ := fupd_intro _ _
}.

Notation "l ↦ᵢ{ dq } v" := (mapsto (L:=loc) (V:=val) l dq v)
  (at level 20, format "l  ↦ᵢ{ dq }  v") : bi_scope.
Notation "l ↦ᵢ□ v" := (mapsto (L:=loc) (V:=val) l DfracDiscarded v)
  (at level 20, format "l  ↦ᵢ□  v") : bi_scope.
Notation "l ↦ᵢ{# q } v" := (mapsto (L:=loc) (V:=val) l (DfracOwn q) v)
  (at level 20, format "l  ↦ᵢ{# q }  v") : bi_scope.
Notation "l ↦ᵢ v" := (mapsto (L:=loc) (V:=val) l (DfracOwn 1) v)
  (at level 20, format "l  ↦ᵢ  v") : bi_scope.

Section lang_rules.
  Context `{heapIG Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.
  Implicit Types σ : state.
  Implicit Types e : expr.
  Implicit Types v w : val.

  Local Hint Extern 0 (atomic _) => solve_atomic : core.
  Local Hint Extern 0 (head_reducible _ _) => eexists _, _, _, _; simpl : core.

  Local Hint Constructors head_step : core.
  Local Hint Resolve alloc_fresh : core.
  Local Hint Resolve to_of_val : core.

   
  Lemma wp_alloc E e v :
    IntoVal e v →
    {{{ True }}} Alloc e @ E {{{ l, RET (LocV l); l ↦ᵢ v }}}.
Admitted.

  Lemma wp_load E l dq v :
    {{{ ▷ l ↦ᵢ{dq} v }}} Load (Loc l) @ E {{{ RET v; l ↦ᵢ{dq} v }}}.
Admitted.

  Lemma wp_store E l v' e v :
    IntoVal e v →
    {{{ ▷ l ↦ᵢ v' }}} Store (Loc l) e @ E
    {{{ RET UnitV; l ↦ᵢ v }}}.
Admitted.

  Lemma wp_cas_fail E l dq v' e1 v1 e2 v2 :
    IntoVal e1 v1 → IntoVal e2 v2 → v' ≠ v1 →
    {{{ ▷ l ↦ᵢ{dq} v' }}} CAS (Loc l) e1 e2 @ E
    {{{ RET (BoolV false); l ↦ᵢ{dq} v' }}}.
Admitted.

  Lemma wp_cas_suc E l e1 v1 e2 v2 :
    IntoVal e1 v1 → IntoVal e2 v2 →
    {{{ ▷ l ↦ᵢ v1 }}} CAS (Loc l) e1 e2 @ E
    {{{ RET (BoolV true); l ↦ᵢ v2 }}}.
Admitted.

  Lemma wp_FAA E l m e2 k :
    IntoVal e2 (#nv k) →
    {{{ ▷ l ↦ᵢ (#nv m) }}} FAA (Loc l) e2 @ E
    {{{ RET (#nv m); l ↦ᵢ #nv (m + k) }}}.
Admitted.

  Lemma wp_fork E e Φ :
    ▷ (|={E}=> Φ UnitV) ∗ ▷ WP e {{ _, True }} ⊢ WP Fork e @ E {{ Φ }}.
Admitted.

  Global Instance pure_rec e1 e2 `{!AsVal e2} :
    PureExec True 1 (App (Rec e1) e2) e1.[(Rec e1), e2 /].
Admitted.

  Global Instance pure_lam e1 e2 `{!AsVal e2} :
    PureExec True 1 (App (Lam e1) e2) e1.[e2 /].
Admitted.

  Global Instance pure_LetIn e1 e2 `{!AsVal e1} :
    PureExec True 1 (LetIn e1 e2) e2.[e1 /].
Admitted.

  Global Instance pure_seq e1 e2 `{!AsVal e1} :
    PureExec True 1 (Seq e1 e2) e2.
Admitted.

  Global Instance pure_tlam e : PureExec True 1 (TApp (TLam e)) e.
Admitted.

  Global Instance pure_pack e1 `{!AsVal e1} e2:
    PureExec True 1 (UnpackIn (Pack e1) e2) e2.[e1/].
Admitted.

  Global Instance pure_fold e `{!AsVal e}:
    PureExec True 1 (Unfold (Fold e)) e.
Admitted.

  Global Instance pure_fst e1 e2 `{!AsVal e1, !AsVal e2} :
    PureExec True 1 (Fst (Pair e1 e2)) e1.
Admitted.

  Global Instance pure_snd e1 e2 `{!AsVal e1, !AsVal e2} :
    PureExec True 1 (Snd (Pair e1 e2)) e2.
Admitted.

  Global Instance pure_case_inl e0 e1 e2 `{!AsVal e0}:
    PureExec True 1 (Case (InjL e0) e1 e2) e1.[e0/].
Admitted.

  Global Instance pure_case_inr e0 e1 e2 `{!AsVal e0}:
    PureExec True 1 (Case (InjR e0) e1 e2) e2.[e0/].
Admitted.

  Global Instance wp_if_true e1 e2 :
    PureExec True 1 (If (#♭ true) e1 e2) e1.
Admitted.

  Global Instance wp_if_false e1 e2 :
    PureExec True 1 (If (#♭ false) e1 e2) e2.
Admitted.

  Global Instance wp_nat_binop op a b :
    PureExec True 1 (BinOp op (#n a) (#n b)) (of_val (binop_eval op a b)).
Admitted.

End lang_rules.

End wp_rules.

End iris_examples_DOT_logrel_DOT_F_mu_ref_conc_DOT_wp_rules_WRAPPED.
Module Export iris_examples_DOT_logrel_DOT_F_mu_ref_conc_DOT_wp_rules.
Module Export iris_examples.
Module Export logrel.
Module Export F_mu_ref_conc.
Module Export wp_rules.
Include iris_examples_DOT_logrel_DOT_F_mu_ref_conc_DOT_wp_rules_WRAPPED.wp_rules.
End wp_rules.

End F_mu_ref_conc.

End logrel.

End iris_examples.

End iris_examples_DOT_logrel_DOT_F_mu_ref_conc_DOT_wp_rules.

Module Export iris_examples_DOT_logrel_DOT_F_mu_ref_conc_DOT_binary_DOT_rules_WRAPPED.
Module Export rules.
Import iris.algebra.excl.
Import iris.algebra.gmap.
Import iris.proofmode.proofmode.
Export iris_examples.logrel.F_mu_ref_conc.wp_rules.

Definition specN := nroot .@ "spec".
Definition tpoolUR : ucmra.
exact (gmapUR nat (exclR exprO)).
Defined.
Definition heapUR (L V : Type) `{Countable L} : ucmra.
exact (gmapUR L (prodR fracR (agreeR (leibnizO V)))).
Defined.
Definition cfgUR := prodUR tpoolUR (heapUR loc val).
Definition to_tpool : list expr → tpoolUR.
Admitted.
Definition to_heap {L V} `{Countable L} : gmap L V → heapUR L V.
exact (fmap (λ v, (1%Qp, to_agree (v : leibnizO V)))).
Defined.

Class cfgSG Σ := CFGSG { cfg_inG :> inG Σ (authR cfgUR); cfg_name : gname }.

Section definitionsS.
  Context `{cfgSG Σ, invGS Σ}.
Definition heapS_mapsto (l : loc) (q : Qp) (v: val) : iProp Σ.
Admitted.
Definition tpool_mapsto (j : nat) (e: expr) : iProp Σ.
Admitted.
Definition spec_inv (ρ : cfg F_mu_ref_conc_lang) : iProp Σ.
exact ((∃ tp σ, own cfg_name (● (to_tpool tp, to_heap σ))
                 ∗ ⌜rtc erased_step ρ (tp,σ)⌝)%I).
Defined.
Definition spec_ctx : iProp Σ.
exact ((∃ ρ, inv specN (spec_inv ρ))%I).
Defined.
End definitionsS.
Notation "l ↦ₛ v" := (heapS_mapsto l 1 v) (at level 20) : bi_scope.
Notation "j ⤇ e" := (tpool_mapsto j e) (at level 20) : bi_scope.

Section conversions.

  Lemma to_tpool_valid es : ✓ to_tpool es.
Admitted.

End conversions.

End rules.
Module Export iris_examples.
Module Export logrel.
Module Export F_mu_ref_conc.
Module Export binary.
Module Export rules.
Include iris_examples_DOT_logrel_DOT_F_mu_ref_conc_DOT_binary_DOT_rules_WRAPPED.rules.
End rules.

Inductive type :=
  | TUnit : type
  | TNat : type
  | TBool : type
  | TProd : type → type → type
  | TSum : type → type → type
  | TArrow : type → type → type
  | TRec (τ : {bind 1 of type})
  | TVar (x : var)
  | TForall (τ : {bind 1 of type})
  | TExist (τ : {bind 1 of type})
  | Tref (τ : type).
Fixpoint env_subst (vs : list val) : var → expr.
exact (match vs with
  | [] => ids
  | v :: vs' => (of_val v) .: env_subst vs'
  end).
Defined.

Section persistent_pred.
  Context (A : Type) (PROP : bi).

  Record persistent_pred := PersPred {
    pers_pred_car :> A → PROP;
    pers_pred_persistent x : Persistent (pers_pred_car x)
  }.
Local Instance persistent_pred_equiv : Equiv persistent_pred.
Admitted.
Local Instance persistent_pred_dist : Dist persistent_pred.
exact (λ n Φ Φ', ∀ x, Φ x ≡{n}≡ Φ' x).
Defined.
  Definition persistent_pred_ofe_mixin : OfeMixin persistent_pred.
Admitted.
  Canonical Structure persistent_predO :=
    Ofe persistent_pred persistent_pred_ofe_mixin.

  Global Instance persistent_pred_car_ne n :
    Proper (dist n ==> (=) ==> dist n)
      pers_pred_car.
Admitted.

End persistent_pred.

Global Arguments PersPred {_ _} _%I {_}.
Import iris.proofmode.proofmode.
Import iris.algebra.list.
Definition logN : namespace.
Admitted.

Section logrel.
  Context `{heapIG Σ, cfgSG Σ}.
  Notation D := (persistent_predO (val * val) (iPropI Σ)).
Definition interp_expr (τi : listO D -n> D) (Δ : listO D)
      (ee : expr * expr) : iProp Σ.
exact ((∀ j K,
    j ⤇ fill K (ee.2) -∗
    WP ee.1 {{ v, ∃ v', j ⤇ fill K (of_val v') ∗ τi Δ (v, v') }})%I).
Defined.

  Program Definition interp_ref_inv (ll : loc * loc) : D -n> iPropO Σ := λne τi,
    (∃ vv, ll.1 ↦ᵢ vv.1 ∗ ll.2 ↦ₛ vv.2 ∗ τi vv)%I.
  Solve Obligations with solve_proper.

  Program Definition interp_ref
      (interp : listO D -n> D) : listO D -n> D :=
    λne Δ,
    PersPred (λ ww,
            ∃ ll, ⌜ww = (LocV (ll.1), LocV (ll.2))⌝ ∧
                  inv (logN .@ ll) (interp_ref_inv ll (interp Δ)))%I.
  Solve Obligations with solve_proper.
Fixpoint interp (τ : type) : listO D -n> D.
Admitted.
  Notation "⟦ τ ⟧" := (interp τ).
Definition interp_env (Γ : list type)
      (Δ : listO D) (vvs : list (val * val)) : iProp Σ.
exact ((⌜length Γ = length vvs⌝ ∗ [∗] zip_with (λ τ, ⟦ τ ⟧ Δ) Γ vvs)%I).
Defined.

End logrel.
Notation "⟦ τ ⟧ₑ" := (interp_expr (interp τ)).
Notation "⟦ Γ ⟧*" := (interp_env Γ).

Section bin_log_def.
  Context `{heapIG Σ, cfgSG Σ}.
Definition bin_log_related (Γ : list type) (e e' : expr) (τ : type) : iProp Σ.
exact (tc_opaque (□ ∀ Δ vvs,
      spec_ctx ∧ ⟦ Γ ⟧* Δ vvs -∗
      ⟦ τ ⟧ₑ Δ (e.[env_subst (vvs.*1)], e'.[env_subst (vvs.*2)]))%I).
Defined.

End bin_log_def.

Notation "Γ ⊨ e '≤log≤' e' : τ" :=
  (bin_log_related Γ e e' τ) (at level 74, e, e', τ at next level).

Module Export iris_examples_DOT_logrel_DOT_F_mu_ref_conc_DOT_unary_DOT_logrel_WRAPPED.
Module Export logrel.
Export iris_examples.logrel.F_mu_ref_conc.binary.rules.

Section logrel.
  Context `{heapIG Σ}.
  Notation D := (persistent_predO val (iPropI Σ)).

  Program Definition interp_ref_inv (l : loc) : D -n> iPropO Σ := λne τi,
    (∃ v, l ↦ᵢ v ∗ τi v)%I.
  Solve Obligations with solve_proper.

  Program Definition interp_ref (interp : listO D -n> D) : listO D -n> D :=
    λne Δ,
    PersPred (λ w, ∃ l, ⌜w = LocV l⌝ ∧
                      inv (logN .@ l) (interp_ref_inv l (interp Δ)))%I.
  Solve Obligations with solve_proper.
Fixpoint interp (τ : type) : listO D -n> D.
Admitted.
  Notation "⟦ τ ⟧" := (interp τ).
Definition interp_env (Γ : list type)
      (Δ : listO D) (vs : list val) : iProp Σ.
exact ((⌜length Γ = length vs⌝ ∗ [∗] zip_with (λ τ, ⟦ τ ⟧ Δ) Γ vs)%I).
Defined.
  Notation "⟦ Γ ⟧*" := (interp_env Γ).

  Lemma interp_env_nil Δ : ⊢ ⟦ [] ⟧* Δ [].
Admitted.
End logrel.

End logrel.
Module Export iris_examples.
Module Export logrel.
Module Export F_mu_ref_conc.
Module Export unary.
Module Export logrel.
Include iris_examples_DOT_logrel_DOT_F_mu_ref_conc_DOT_unary_DOT_logrel_WRAPPED.logrel.
End logrel.

Module Export iris_examples_DOT_logrel_DOT_F_mu_ref_conc_DOT_unary_DOT_fundamental_WRAPPED.
Module Export fundamental.
Export iris_examples.logrel.F_mu_ref_conc.unary.logrel.

End fundamental.
Module Export iris_examples.
Module Export logrel.
Module Export F_mu_ref_conc.
Module Export unary.
Module Export fundamental.
Include iris_examples_DOT_logrel_DOT_F_mu_ref_conc_DOT_unary_DOT_fundamental_WRAPPED.fundamental.
End fundamental.

Module Export iris_examples_DOT_logrel_DOT_F_mu_ref_conc_DOT_unary_DOT_soundness_WRAPPED.
Module Export soundness.
Export iris_examples.logrel.F_mu_ref_conc.unary.fundamental.

End soundness.
Module Export iris_examples.
Module Export logrel.
Module Export F_mu_ref_conc.
Module Export unary.
Module Export soundness.
Include iris_examples_DOT_logrel_DOT_F_mu_ref_conc_DOT_unary_DOT_soundness_WRAPPED.soundness.
End soundness.
Import iris.program_logic.adequacy.
Import iris_examples.logrel.F_mu_ref_conc.unary.soundness.

Lemma basic_soundness Σ `{heapPreIG Σ, inG Σ (authR cfgUR)}
    e e' τ v thp hp :
  (∀ `{heapIG Σ, cfgSG Σ}, ⊢ [] ⊨ e ≤log≤ e' : τ) →
  rtc erased_step ([e], ∅) (of_val v :: thp, hp) →
  (∃ thp' hp' v', rtc erased_step ([e'], ∅) (of_val v' :: thp', hp')).
Proof.
  intros Hlog Hsteps.
  cut (adequate NotStuck e ∅ (λ _ _, ∃ thp' h v, rtc erased_step ([e'], ∅) (of_val v :: thp', h))).
  {
 destruct 1; naive_solver.
}
  eapply (wp_adequacy Σ _); iIntros (Hinv ?).
  iMod (gen_heap_init (∅: state)) as (Hheap) "[Hh _]".
  iMod (own_alloc (● (to_tpool [e'], ∅)
    ⋅ ◯ ((to_tpool [e'] : tpoolUR, ∅) : cfgUR))) as (γc) "[Hcfg1 Hcfg2]".
  {
 apply auth_both_valid_discrete.
split=>//.
split=>//.
apply to_tpool_valid.
}
  set (Hcfg := CFGSG _ _ γc).
  iMod (inv_alloc specN _ (spec_inv ([e'], ∅)) with "[Hcfg1]") as "#Hcfg".
  {
 iNext.
iExists [e'], ∅.
rewrite /to_heap fmap_empty.
auto.
}
  set (HeapΣ := (HeapIG Σ Hinv Hheap)).
  iExists (λ σ _, gen_heap_interp σ), (λ _, True%I); iFrame.
  iApply wp_fupd.
iApply wp_wand_r.
  iSplitL.
  -
 iPoseProof ((Hlog _ _)) as "Hrel".
    iSpecialize ("Hrel" $! [] [] with "[]").
    {
 iSplit.
      -
 by iExists ([e'], ∅).
      -
 by iApply (@interp_env_nil Σ HeapΣ []).
}
    simpl.
    replace e with e.[env_subst[]] at 2 by by asimpl.
    iApply ("Hrel" $! 0 []).
    {
 rewrite /tpool_mapsto.
asimpl.
