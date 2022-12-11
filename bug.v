(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "-notation-overridden" "-w" "-redundant-canonical-projection" "-w" "-deprecated-native-compiler-option" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/iris_examples/theories" "iris_examples" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Autosubst" "Autosubst" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/iris" "iris" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/stdpp" "stdpp" "-top" "Top.bug_01" "-native-compiler" "ondemand") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 81 lines to 59 lines, then from 72 lines to 296 lines, then from 301 lines to 73 lines, then from 86 lines to 644 lines, then from 649 lines to 86 lines, then from 99 lines to 483 lines, then from 488 lines to 129 lines, then from 142 lines to 619 lines, then from 624 lines to 125 lines, then from 138 lines to 893 lines, then from 898 lines to 138 lines, then from 151 lines to 623 lines, then from 628 lines to 397 lines, then from 409 lines to 177 lines, then from 190 lines to 333 lines, then from 338 lines to 202 lines, then from 215 lines to 546 lines, then from 551 lines to 220 lines, then from 233 lines to 935 lines, then from 938 lines to 273 lines, then from 286 lines to 670 lines, then from 675 lines to 610 lines, then from 610 lines to 303 lines, then from 316 lines to 874 lines, then from 879 lines to 529 lines *)
(* coqc version 8.18+alpha compiled with OCaml 4.14.0
   coqtop version runner-q6hytnfs-project-6138686-concurrent-0:/builds/coq/coq/_build/default,(HEAD detached at 41fd2ab) (41fd2ab2f7d875b43ff3442483386100b081bd29)
   Expected coqc runtime on this file: 16.786 sec *)
Require iris.base_logic.lib.gen_heap.
Require iris.program_logic.adequacy.
Require iris.program_logic.ectxi_language.
Require iris_examples.logrel.F_mu_ref_conc.base.

Module Export iris_examples_DOT_logrel_DOT_F_mu_ref_conc_DOT_lang_WRAPPED.
Module Export lang.
Export iris.program_logic.language.
Export iris.program_logic.ectx_language.
Export iris.program_logic.ectxi_language.
Export iris_examples.logrel.F_mu_ref_conc.base.
Import stdpp.gmap.

Module Export F_mu_ref_conc.
  Definition loc := positive.

  Inductive binop := Add | Sub | Mult | Eq | Le | Lt.

  Inductive expr :=
  | Var (x : var)
  | Rec (e : {bind 2 of expr})
  | App (e1 e2 : expr)
  | Lam (e : {bind expr})
  | LetIn (e1 : expr) (e2 : {bind expr})
  | Seq (e1 e2 : expr)
   
  | Unit
  | Nat (n : nat)
  | Bool (b : bool)
  | BinOp (op : binop) (e1 e2 : expr)
   
  | If (e0 e1 e2 : expr)
   
  | Pair (e1 e2 : expr)
  | Fst (e : expr)
  | Snd (e : expr)
   
  | InjL (e : expr)
  | InjR (e : expr)
  | Case (e0 : expr) (e1 : {bind expr}) (e2 : {bind expr})
   
  | Fold (e : expr)
  | Unfold (e : expr)
   
  | TLam (e : expr)
  | TApp (e : expr)
   
  | Pack (e : expr)
  | UnpackIn (e1 : expr) (e2 : {bind expr})
   
  | Fork (e : expr)
   
  | Loc (l : loc)
  | Alloc (e : expr)
  | Load (e : expr)
  | Store (e1 : expr) (e2 : expr)
   
  | CAS (e0 : expr) (e1 : expr) (e2 : expr)
   
  | FAA (e1 : expr) (e2 : expr).
  Global Instance Ids_expr : Ids expr.
Admitted.
  Global Instance Rename_expr : Rename expr.
Admitted.
  Global Instance Subst_expr : Subst expr.
Admitted.
  Global Instance SubstLemmas_expr : SubstLemmas expr.
Admitted.

   
  Notation "#♭ b" := (Bool b) (at level 20).
  Notation "#n n" := (Nat n) (at level 20).

  Inductive val :=
  | RecV (e : {bind 1 of expr})
  | LamV (e : {bind expr})
  | TLamV (e : {bind 1 of expr})
  | PackV (v : val)
  | UnitV
  | NatV (n : nat)
  | BoolV (b : bool)
  | PairV (v1 v2 : val)
  | InjLV (v : val)
  | InjRV (v : val)
  | FoldV (v : val)
  | LocV (l : loc).

   
  Notation "'#♭v' b" := (BoolV b) (at level 20).
  Notation "'#nv' n" := (NatV n) (at level 20).
Definition binop_eval (op : binop) : nat → nat → val.
Admitted.
Fixpoint of_val (v : val) : expr.
Admitted.
Fixpoint to_val (e : expr) : option val.
Admitted.

   
  Inductive ectx_item :=
  | AppLCtx (e2 : expr)
  | AppRCtx (v1 : val)
  | LetInCtx (e2 : expr)
  | SeqCtx (e2 : expr)
  | TAppCtx
  | PackCtx
  | UnpackInCtx (e2 : expr)
  | PairLCtx (e2 : expr)
  | PairRCtx (v1 : val)
  | BinOpLCtx (op : binop) (e2 : expr)
  | BinOpRCtx (op : binop) (v1 : val)
  | FstCtx
  | SndCtx
  | InjLCtx
  | InjRCtx
  | CaseCtx (e1 : {bind expr}) (e2 : {bind expr})
  | IfCtx (e1 : {bind expr}) (e2 : {bind expr})
  | FoldCtx
  | UnfoldCtx
  | AllocCtx
  | LoadCtx
  | StoreLCtx (e2 : expr)
  | StoreRCtx (v1 : val)
  | CasLCtx (e1 : expr)  (e2 : expr)
  | CasMCtx (v0 : val) (e2 : expr)
  | CasRCtx (v0 : val) (v1 : val)
  | FAALCtx (e2 : expr)
  | FAARCtx (v1 : val).
Definition fill_item (Ki : ectx_item) (e : expr) : expr.
Admitted.
Definition state : Type.
exact (gmap loc val).
Defined.

  Inductive head_step : expr → state → list Empty_set → expr → state → list expr → Prop :=
   
  | BetaS e1 e2 v2 σ :
      to_val e2 = Some v2 →
      head_step (App (Rec e1) e2) σ [] e1.[(Rec e1), e2/] σ []
   
  | LamBetaS e1 e2 v2 σ :
      to_val e2 = Some v2 →
      head_step (App (Lam e1) e2) σ [] e1.[e2/] σ []
   
  | LetInBetaS e1 e2 v2 σ :
      to_val e1 = Some v2 →
      head_step (LetIn e1 e2) σ [] e2.[e1/] σ []
   
  | SeqBetaS e1 e2 v2 σ :
      to_val e1 = Some v2 →
      head_step (Seq e1 e2) σ [] e2 σ []
   
  | FstS e1 v1 e2 v2 σ :
      to_val e1 = Some v1 → to_val e2 = Some v2 →
      head_step (Fst (Pair e1 e2)) σ [] e1 σ []
  | SndS e1 v1 e2 v2 σ :
      to_val e1 = Some v1 → to_val e2 = Some v2 →
      head_step (Snd (Pair e1 e2)) σ [] e2 σ []
   
  | CaseLS e0 v0 e1 e2 σ :
      to_val e0 = Some v0 →
      head_step (Case (InjL e0) e1 e2) σ [] e1.[e0/] σ []
  | CaseRS e0 v0 e1 e2 σ :
      to_val e0 = Some v0 →
      head_step (Case (InjR e0) e1 e2) σ [] e2.[e0/] σ []
     
  | BinOpS op a b σ :
      head_step (BinOp op (#n a) (#n b)) σ [] (of_val (binop_eval op a b)) σ []
   
  | IfFalse e1 e2 σ :
      head_step (If (#♭ false) e1 e2) σ [] e2 σ []
  | IfTrue e1 e2 σ :
      head_step (If (#♭ true) e1 e2) σ [] e1 σ []
   
  | Unfold_Fold e v σ :
      to_val e = Some v →
      head_step (Unfold (Fold e)) σ [] e σ []
   
  | TBeta e σ :
      head_step (TApp (TLam e)) σ [] e σ []
   
  | UnpackS e1 v e2 σ :
      to_val e1 = Some v →
      head_step (UnpackIn (Pack e1) e2) σ [] e2.[e1/] σ []
   
  | ForkS e σ:
      head_step (Fork e) σ [] Unit σ [e]
   
  | AllocS e v σ l :
     to_val e = Some v → σ !! l = None →
     head_step (Alloc e) σ [] (Loc l) (<[l:=v]>σ) []
  | LoadS l v σ :
     σ !! l = Some v →
     head_step (Load (Loc l)) σ [] (of_val v) σ []
  | StoreS l e v σ :
     to_val e = Some v → is_Some (σ !! l) →
     head_step (Store (Loc l) e) σ [] Unit (<[l:=v]>σ) []
   
  | CasFailS l e1 v1 e2 v2 vl σ :
     to_val e1 = Some v1 → to_val e2 = Some v2 →
     σ !! l = Some vl → vl ≠ v1 →
     head_step (CAS (Loc l) e1 e2) σ [] (#♭ false) σ []
  | CasSucS l e1 v1 e2 v2 σ :
     to_val e1 = Some v1 → to_val e2 = Some v2 →
     σ !! l = Some v1 →
     head_step (CAS (Loc l) e1 e2) σ [] (#♭ true) (<[l:=v2]>σ) []
  | FAAS l m e2 k σ :
      to_val e2 = Some (NatV k) →
      σ !! l = Some (NatV m) →
      head_step (FAA (Loc l) e2) σ [] (#n m) (<[l:=NatV (m + k)]>σ) [].

  Lemma lang_mixin : EctxiLanguageMixin of_val to_val fill_item head_step.
Admitted.
  Canonical Structure exprO := leibnizO expr.
End F_mu_ref_conc.

Canonical Structure F_mu_ref_conc_ectxi_lang :=
  EctxiLanguage F_mu_ref_conc.lang_mixin.
Canonical Structure F_mu_ref_conc_ectx_lang :=
  EctxLanguageOfEctxi F_mu_ref_conc_ectxi_lang.
Canonical Structure F_mu_ref_conc_lang :=
  LanguageOfEctx F_mu_ref_conc_ectx_lang.

End lang.
Module Export iris_examples.
Module Export logrel.
Module Export F_mu_ref_conc.
Module Export lang.
Include iris_examples_DOT_logrel_DOT_F_mu_ref_conc_DOT_lang_WRAPPED.lang.
End lang.
Module Export iris_examples_DOT_logrel_DOT_F_mu_ref_conc_DOT_wp_rules_WRAPPED.
Module Export wp_rules.
Export iris.program_logic.weakestpre.
Export iris.base_logic.lib.invariants.
Export iris.base_logic.lib.gen_heap.
Export iris_examples.logrel.F_mu_ref_conc.lang.

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
Notation "l ↦ᵢ v" := (mapsto (L:=loc) (V:=val) l (DfracOwn 1) v)
  (at level 20, format "l  ↦ᵢ  v") : bi_scope.

End wp_rules.
Module Export iris_examples.
Module Export logrel.
Module Export F_mu_ref_conc.
Module Export wp_rules.
Include iris_examples_DOT_logrel_DOT_F_mu_ref_conc_DOT_wp_rules_WRAPPED.wp_rules.
End wp_rules.

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
