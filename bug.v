
(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "-deprecated-native-compiler-option" "-native-compiler" "no" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/metacoq/utils/theories" "MetaCoq.Utils" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/metacoq/common/theories" "MetaCoq.Common" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/metacoq/pcuic/theories" "MetaCoq.PCUIC" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/metacoq/safechecker/theories" "MetaCoq.SafeChecker" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Equations" "Equations" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-top" "MetaCoq.SafeChecker.PCUICSafeRetyping") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 973 lines to 345 lines *)
(* coqc version 8.20+alpha compiled with OCaml 4.09.0
   coqtop version runner-t7b1znuaq-project-4504-concurrent-4:/builds/coq/coq/_build/default,(HEAD detached at c8eb5da7e30) (c8eb5da7e30015d6ad310fae11d3c1d21d3bf4bb)
   Expected coqc runtime on this file: 18.489 sec *)
Require MetaCoq.PCUIC.Bidirectional.BDUnique.
Require MetaCoq.SafeChecker.PCUICSafeReduce.
Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.
Import MetaCoq.Utils.utils.
Import MetaCoq.Common.config.
Import MetaCoq.PCUIC.PCUICAst.
Import MetaCoq.PCUIC.PCUICTyping.
Import MetaCoq.PCUIC.PCUICReduction.
Import MetaCoq.PCUIC.Typing.PCUICClosedTyp.
Import MetaCoq.PCUIC.PCUICWellScopedCumulativity.
Import MetaCoq.PCUIC.PCUICSN.
Import MetaCoq.PCUIC.Bidirectional.BDTyping.
Import MetaCoq.PCUIC.Bidirectional.BDFromPCUIC.
Import MetaCoq.PCUIC.Bidirectional.BDUnique.
Import MetaCoq.SafeChecker.PCUICErrors.
Import MetaCoq.SafeChecker.PCUICSafeReduce.
Import MetaCoq.SafeChecker.PCUICWfEnv.

Inductive wellinferred {cf: checker_flags} Σ Γ t : Prop :=
  | iswellinferred T : Σ ;;; Γ |- t ▹ T -> wellinferred Σ Γ t.

Definition well_sorted {cf:checker_flags} Σ Γ T :=
  ∥ ∑ u, Σ ;;; Γ |- T ▹□ u ∥.

Lemma well_sorted_wellinferred {cf:checker_flags} {Σ Γ T} :
  well_sorted Σ Γ T -> wellinferred Σ Γ T.
Admitted.

Coercion well_sorted_wellinferred : well_sorted >-> wellinferred.
Context {cf : checker_flags} {nor : normalizing_flags}.

  Context (X_type : abstract_env_impl).

  Context (X : X_type.π2.π1).

  Context {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X -> NormalizationIn Σ}.
Local Definition hΣ Σ (wfΣ : abstract_env_ext_rel X Σ) :
    ∥ wf Σ ∥.
exact (abstract_env_ext_sq_wf _ _ _ wfΣ).
Defined.

  Ltac specialize_Σ wfΣ :=
    repeat match goal with | h : _ |- _ => specialize (h _ wfΣ) end.

  Definition on_subterm P Pty Γ t : Type :=
  match t with
  | tProd na t b => Pty Γ t * Pty (Γ ,, vass na t) b
  | tLetIn na d t t' =>
    Pty Γ t * P Γ d * P (Γ ,, vdef na d t) t'
  | tLambda na t b => Pty Γ t * P (Γ ,, vass na t) b
  | _ => True
  end.

Lemma welltyped_subterm {Σ Γ t} :
  wellinferred Σ Γ t -> on_subterm (wellinferred Σ) (well_sorted Σ) Γ t.
Admitted.

  #[local] Notation ret t := (t; _).

  #[local] Definition principal_type Γ t :=
    ∑ T : term, forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ Σ ;;; Γ |- t ▹ T ∥.
  #[local] Definition principal_sort Γ T :=
    ∑ u, forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ Σ ;;; Γ |- T ▹□ u ∥.
#[local] Definition principal_type_type {Γ t} (wt : principal_type Γ t) : term.
exact (projT1 wt).
Defined.
#[local] Definition principal_sort_sort {Γ T} (ps : principal_sort Γ T) : Universe.t.
exact (projT1 ps).
Defined.
  #[local] Coercion principal_type_type : principal_type >-> term.
  #[local] Coercion principal_sort_sort : principal_sort >-> Universe.t.

  Program Definition infer_as_sort {Γ T}
    (wfΓ : forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ wf_local Σ Γ ∥)
    (wf : forall Σ (wfΣ : abstract_env_ext_rel X Σ), well_sorted Σ Γ T)
    (tx : principal_type Γ T) : principal_sort Γ T :=
    match @reduce_to_sort cf nor _ X _ Γ tx _ with
    | Checked_comp (u;_) => (u;_)
    | TypeError_comp e _ => !
    end.

  Program Definition infer_as_prod Γ T
    (wfΓ : forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ wf_local Σ Γ ∥)
    (wf : forall Σ (wfΣ : abstract_env_ext_rel X Σ), welltyped Σ Γ T)
    (isprod : forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ ∑ na A B, red Σ Γ T (tProd na A B) ∥) :
    ∑ na' A' B', forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ Σ ;;; Γ ⊢ T ⇝ tProd na' A' B' ∥ :=
    match @reduce_to_prod cf nor _ X _ Γ T wf with
    | Checked_comp p => p
    | TypeError_comp e _ => !
    end.

  Equations lookup_ind_decl ind : typing_result
        (∑ decl body, forall Σ (wfΣ : abstract_env_ext_rel X Σ), declared_inductive (fst Σ) ind decl body) :=
  lookup_ind_decl ind with inspect (abstract_env_lookup X ind.(inductive_mind)) :=
    { | exist (Some (InductiveDecl decl)) look with inspect (nth_error decl.(ind_bodies) ind.(inductive_ind)) :=
      { | exist (Some body) eqnth => Checked (decl; body; _);
        | exist None _ => raise (UndeclaredInductive ind) };
      | _ => raise (UndeclaredInductive ind) }.
Admit Obligations.

  Equations infer (Γ : context) (wfΓ : forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ wf_local Σ Γ ∥) (t : term)
    (wt : forall Σ (wfΣ : abstract_env_ext_rel X Σ), wellinferred Σ Γ t) :
    principal_type Γ t
    by struct t :=
   infer Γ wfΓ (tRel n) wt with
    inspect (option_map (lift0 (S n) ∘ decl_type) (nth_error Γ n)) :=
    { | exist None _ => !
      | exist (Some t) _ => ret t };

    infer Γ wfΓ (tVar n) wt := !;
    infer Γ wfΓ (tEvar ev args) wt := !;

    infer Γ wfΓ (tSort s) wt := ret (tSort (Universe.super s));

    infer Γ wfΓ (tProd n ty b) wt :=
      let wfΓ' : forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ wf_local Σ (Γ ,, vass n ty) ∥ := _ in
      let ty1 := infer Γ wfΓ ty (fun a b => (welltyped_subterm (wt a b)).1) in
      let s1 := infer_as_sort wfΓ (fun a b => (welltyped_subterm (wt a b)).1) ty1 in
      let ty2 := infer (Γ ,, vass n ty) wfΓ' b (fun a b => (welltyped_subterm (wt a b)).2) in
      let s2 := infer_as_sort wfΓ' (fun a b => (welltyped_subterm (wt a b)).2) ty2 in
      ret (tSort (Universe.sort_of_product s1 s2));

    infer Γ wfΓ (tLambda n t b) wt :=
      let t2 := infer (Γ ,, vass n t) _ b (fun a b => (welltyped_subterm (wt a b)).2) in
      ret (tProd n t t2);

    infer Γ wfΓ (tLetIn n b b_ty b') wt :=
      let b'_ty := infer (Γ ,, vdef n b b_ty) _ b' (fun a b => (welltyped_subterm (wt a b)).2) in
      ret (tLetIn n b b_ty b'_ty);

    infer Γ wfΓ (tApp t a) wt :=
      let ty := infer Γ wfΓ t _ in
      let pi := infer_as_prod Γ ty wfΓ _ _ in
      ret (subst10 a pi.π2.π2.π1);

    infer Γ wfΓ (tConst cst u) wt with inspect (abstract_env_lookup X cst) :=
      { | exist (Some (ConstantDecl d)) _ := ret (subst_instance u d.(cst_type))
        |  _ := ! };

    infer Γ wfΓ (tInd ind u) wt with inspect (lookup_ind_decl ind) :=
      { | exist (Checked decl) _ := ret (subst_instance u decl.π2.π1.(ind_type))
        | exist (TypeError e) _ := ! };

    infer Γ wfΓ (tConstruct ind k u) wt with inspect (lookup_ind_decl ind) :=
      { | exist (Checked decl) _ with inspect (nth_error decl.π2.π1.(ind_ctors) k) :=
        { | exist (Some cdecl) _ => ret (type_of_constructor decl.π1 cdecl (ind, k) u)
          | exist None _ => ! }
      | exist (TypeError e) _ => ! };

    infer Γ wfΓ (tCase ci p c brs) wt
      with inspect (reduce_to_ind Γ (infer Γ wfΓ c _) _) :=
      { | exist (Checked_comp indargs) _ =>
          let ptm := it_mkLambda_or_LetIn (inst_case_predicate_context p) p.(preturn) in
          ret (mkApps ptm (List.skipn ci.(ci_npar) indargs.π2.π2.π1 ++ [c]));
        | exist (TypeError_comp _ _) _ => ! };

    infer Γ wfΓ (tProj p c) wt with inspect (@lookup_ind_decl p.(proj_ind)) :=
      { | exist (Checked d) _ with inspect (nth_error d.π2.π1.(ind_projs) p.(proj_arg)) :=
        { | exist (Some pdecl) _ with inspect (reduce_to_ind Γ (infer Γ wfΓ c _) _) :=
          { | exist (Checked_comp indargs) _ =>
              let ty := pdecl.(proj_type) in
              ret (subst0 (c :: List.rev (indargs.π2.π2.π1)) (subst_instance indargs.π2.π1 ty))
            | exist (TypeError_comp _ _) _ => ! }
         | exist None _ => ! }
        | exist (TypeError e) _ => ! };

    infer Γ wfΓ (tFix mfix n) wt with inspect (nth_error mfix n) :=
      { | exist (Some f) _ => ret f.(dtype)
        | exist None _ => ! };

    infer Γ wfΓ (tCoFix mfix n) wt with inspect (nth_error mfix n) :=
      { | exist (Some f) _ => ret f.(dtype)
        | exist None _ => ! };

    infer Γ wfΓ (tPrim p) wt with inspect (abstract_primitive_constant X p.π1) :=
      { | exist (Some prim_ty) eqp => ret (tConst prim_ty [])
        | exist None _ => ! }.

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
Admitted.
  Next Obligation.
admit.
Defined.

  Next Obligation.
Admitted.
  Next Obligation.
admit.
Defined.

  Next Obligation.
Admitted.
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
Admitted.
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
Admitted.
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
  Next Obligation.
admit.
Defined.

  Next Obligation.
admit.
Defined.

  Next Obligation.
admit.
Defined.

  Definition type_of Γ wfΓ t wt : term := (infer Γ wfΓ t wt).

  Equations? type_of_subtype {Γ t T} (wt : forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ Σ ;;; Γ |- t : T ∥) :
  forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ Σ ;;; Γ ⊢ type_of Γ _ t _ ≤ T ∥ :=
    type_of_subtype wt := _.
  Proof.
    -
 erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
      specialize_Σ wfΣ.
 case wt as [wt'].
      apply sq.
      now exact (typing_wf_local wt').
    -
 erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
      specialize_Σ wfΣ.
 case wt as [wt'].
      case (hΣ _ wfΣ) as [hΣ'].
      apply typing_infering in wt'.
      case wt' as [T' [i]].
      exists T'.
      exact i.
    -
 unfold type_of.
      destruct infer as [P HP].
cbn.
      specialize_Σ wfΣ.
      pose (hΣ _ wfΣ) ; sq.
simpl.
      eapply infering_checking ; eauto.
      +
 now eapply typing_wf_local.
      +
 now eapply type_is_open_term.
      +
 now eapply typing_checking.
      Unshelve.
all: eauto.
  Defined.
