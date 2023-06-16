
(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "-deprecated-native-compiler-option" "-native-compiler" "no" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/metacoq/utils/theories" "MetaCoq.Utils" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/metacoq/common/theories" "MetaCoq.Common" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/metacoq/pcuic/theories" "MetaCoq.PCUIC" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Equations" "Equations" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-top" "MetaCoq.PCUIC.Conversion.PCUICUnivSubstitutionConv") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 2038 lines to 90 lines, then from 103 lines to 2399 lines, then from 2401 lines to 305 lines, then from 318 lines to 2211 lines, then from 2215 lines to 322 lines, then from 335 lines to 615 lines, then from 620 lines to 337 lines, then from 350 lines to 939 lines, then from 942 lines to 384 lines, then from 397 lines to 1614 lines, then from 1613 lines to 397 lines, then from 410 lines to 822 lines, then from 827 lines to 400 lines, then from 413 lines to 1872 lines, then from 1873 lines to 663 lines, then from 676 lines to 933 lines, then from 938 lines to 670 lines, then from 683 lines to 2715 lines, then from 2716 lines to 1827 lines *)
(* coqc version 8.18+alpha compiled with OCaml 4.09.0
   coqtop version runner-vxtc-u6t-project-6138686-concurrent-0:/builds/coq/coq/_build/default,(HEAD detached at ea07289) (ea07289c2f91dc651a9c72195bde8fa5c3b41ad8)
   Expected coqc runtime on this file: 6.307 sec *)
Require Coq.Init.Ltac.
Require Coq.Arith.Arith.
Require Coq.Arith.Wf_nat.
Require Coq.Bool.Bool.
Require Coq.Bool.Bvector.
Require Coq.Classes.CMorphisms.
Require Coq.Classes.CRelationClasses.
Require Coq.Classes.Morphisms.
Require Coq.Classes.RelationClasses.
Require Coq.FSets.FMapAVL.
Require Coq.FSets.FMapFacts.
Require Coq.FSets.FMapFullAVL.
Require Coq.FSets.FMapInterface.
Require Coq.FSets.FMapList.
Require Coq.Floats.FloatOps.
Require Coq.Floats.PrimFloat.
Require Coq.Floats.SpecFloat.
Require Coq.Init.Decimal.
Require Coq.Init.Nat.
Require Coq.Lists.List.
Require Coq.Lists.SetoidList.
Require Coq.Logic.FunctionalExtensionality.
Require Coq.MSets.MSetAVL.
Require Coq.MSets.MSetDecide.
Require Coq.MSets.MSetFacts.
Require Coq.MSets.MSetInterface.
Require Coq.MSets.MSetList.
Require Coq.MSets.MSetProperties.
Require Coq.NArith.BinNat.
Require Coq.NArith.NArith.
Require Coq.Numbers.Cyclic.Int63.Uint63.
Require Coq.Numbers.DecimalString.
Require Coq.Numbers.HexadecimalString.
Require Coq.Program.Tactics.
Require Coq.Program.Wf.
Require Coq.Relations.Relation_Definitions.
Require Coq.Relations.Relation_Operators.
Require Coq.Relations.Relations.
Require Coq.Setoids.Setoid.
Require Coq.Strings.Ascii.
Require Coq.Strings.Byte.
Require Coq.Strings.String.
Require Coq.Structures.Equalities.
Require Coq.Structures.OrderedType.
Require Coq.Structures.OrderedTypeAlt.
Require Coq.Structures.OrderedTypeEx.
Require Coq.Structures.Orders.
Require Coq.Structures.OrdersAlt.
Require Coq.Unicode.Utf8.
Require Coq.Unicode.Utf8_core.
Require Coq.Wellfounded.Lexicographic_Product.
Require Coq.Wellfounded.Wellfounded.
Require Coq.ZArith.ZArith.
Require Coq.btauto.Btauto.
Require Coq.extraction.Extraction.
Require Coq.micromega.Lia.
Require Coq.ssr.ssrbool.
Require Coq.ssr.ssreflect.
Require Coq.ssr.ssrfun.
Require Ltac2.Init.
Require MetaCoq.Utils.MCEquality.
Require MetaCoq.Utils.MCSquash.
Require MetaCoq.Utils.MCTactics.DestructHyps.
Require MetaCoq.Utils.MCTactics.FindHyp.
Require MetaCoq.Utils.MCTactics.Head.
Require MetaCoq.Utils.MCTactics.SpecializeBy.
Require MetaCoq.Utils.MCTactics.SplitInContext.
Require MetaCoq.Utils.MCTactics.Zeta1.
Require Ltac2.Ltac1.
Require Ltac2.Message.
Require MetaCoq.Utils.MCTactics.UniquePose.
Require Equations.Init.
Require Ltac2.Control.
Require MetaCoq.Utils.ByteCompare.
Require MetaCoq.Utils.MCTactics.DestructHead.
Require MetaCoq.Utils.MCTactics.GeneralizeOverHoles.
Require MetaCoq.Utils.MCTactics.SpecializeAllWays.
Require Equations.Signature.
Require MetaCoq.Utils.MCArith.
Require Equations.CoreTactics.
Require Equations.Prop.Logic.
Require Equations.Type.Logic.
Require MetaCoq.Utils.MCProd.
Require Equations.Type.Relation.
Require Equations.Type.Relation_Properties.
Require MetaCoq.Common.config.
Require MetaCoq.Utils.MCTactics.InHypUnderBindersDo.
Require MetaCoq.Utils.MCTactics.SpecializeUnderBindersBy.
Require Equations.Prop.Classes.
Require Equations.Prop.EqDec.
Require MetaCoq.Utils.MCRelations.
Require Equations.Prop.DepElim.
Require Equations.Prop.FunctionalInduction.
Require Equations.Prop.Constants.
Require Equations.Prop.Subterm.
Require Equations.Prop.Tactics.
Require Equations.Prop.NoConfusion.
Require Equations.Prop.EqDecInstances.
Require Equations.Prop.Loader.
Require Equations.Prop.Telescopes.
Require Equations.Prop.Equations.
Require MetaCoq.Utils.ReflectEq.
Require MetaCoq.Utils.MCCompare.
Require MetaCoq.Utils.MCPrelude.
Require MetaCoq.Utils.MCReflect.
Require MetaCoq.Utils.ByteCompareSpec.
Require MetaCoq.Utils.bytestring.
Require MetaCoq.Utils.MCMSets.
Require MetaCoq.Utils.MCList.
Require MetaCoq.Utils.MCString.
Require MetaCoq.Utils.MCOption.
Require MetaCoq.Common.Primitive.
Require MetaCoq.Utils.All_Forall.
Require MetaCoq.Utils.monad_utils.
Require MetaCoq.Utils.MCUtils.
Require MetaCoq.Utils.utils.
Require MetaCoq.Utils.MCFSets.
Require MetaCoq.Common.Kernames.
Require MetaCoq.Common.BasicAst.
Require MetaCoq.Common.Universes.
Require MetaCoq.Common.Environment.

Module Export AdmitTactic.
Module Import LocalFalse.
Inductive False : Prop := .
End LocalFalse.
Axiom proof_admitted : False.
Import Coq.Init.Ltac.
Tactic Notation "admit" := abstract case proof_admitted.
End AdmitTactic.

Module Export MetaCoq_DOT_Common_DOT_EnvironmentTyping_WRAPPED.
Module Export EnvironmentTyping.
Import Coq.ssr.ssreflect.
Import Coq.ssr.ssrbool.
Import MetaCoq.Utils.utils.
Import MetaCoq.Common.config.
Import MetaCoq.Common.BasicAst.
Import MetaCoq.Common.Universes.
Import MetaCoq.Common.Environment.
Import MetaCoq.Common.Primitive.
Import Equations.Prop.Equations.

Module Lookup (T : Term) (E : EnvironmentSig T).
Import T.
Import E.

   

  Definition declared_constant_gen (lookup : kername -> option global_decl) (id : kername) decl : Prop :=
    lookup id = Some (ConstantDecl decl).

  Definition declared_constant (Σ : global_env) id decl := In (id,ConstantDecl decl) (declarations Σ).

  Definition declared_minductive_gen (lookup : kername -> option global_decl) mind decl :=
    lookup mind = Some (InductiveDecl decl).

  Definition declared_minductive Σ mind decl := In (mind,InductiveDecl decl) (declarations Σ).

  Definition declared_inductive_gen lookup ind mdecl decl :=
    declared_minductive_gen lookup (inductive_mind ind) mdecl /\
    List.nth_error mdecl.(ind_bodies) (inductive_ind ind) = Some decl.

  Definition declared_inductive Σ ind mdecl decl :=
    declared_minductive Σ (inductive_mind ind) mdecl /\
    List.nth_error mdecl.(ind_bodies) (inductive_ind ind) = Some decl.

  Definition declared_constructor_gen lookup cstr mdecl idecl cdecl : Prop :=
    declared_inductive_gen lookup (fst cstr) mdecl idecl /\
    List.nth_error idecl.(ind_ctors) (snd cstr) = Some cdecl.

  Definition declared_constructor Σ cstr mdecl idecl cdecl :=
    declared_inductive Σ (fst cstr) mdecl idecl /\
    List.nth_error idecl.(ind_ctors) (snd cstr) = Some cdecl.

  Definition declared_projection_gen lookup (proj : projection) mdecl idecl cdecl pdecl
  : Prop :=
    declared_constructor_gen lookup (proj.(proj_ind), 0) mdecl idecl cdecl /\
    List.nth_error idecl.(ind_projs) proj.(proj_arg) = Some pdecl /\
    mdecl.(ind_npars) = proj.(proj_npars).

  Definition declared_projection Σ (proj : projection) mdecl idecl cdecl pdecl
  : Prop :=
    declared_constructor Σ (proj.(proj_ind), 0) mdecl idecl cdecl /\
    List.nth_error idecl.(ind_projs) proj.(proj_arg) = Some pdecl /\
    mdecl.(ind_npars) = proj.(proj_npars).

  Definition lookup_constant_gen (lookup : kername -> option global_decl) kn :=
    match lookup kn with
    | Some (ConstantDecl d) => Some d
    | _ => None
    end.

  Definition lookup_constant Σ := lookup_constant_gen (lookup_env Σ).

  Definition lookup_minductive_gen (lookup : kername -> option global_decl) mind :=
    match lookup mind with
    | Some (InductiveDecl decl) => Some decl
    | _ => None
    end.

  Definition lookup_minductive Σ := lookup_minductive_gen (lookup_env Σ).

  Definition lookup_inductive_gen lookup ind :=
    match lookup_minductive_gen lookup (inductive_mind ind) with
    | Some mdecl =>
      match nth_error mdecl.(ind_bodies) (inductive_ind ind) with
      | Some idecl => Some (mdecl, idecl)
      | None => None
      end
    | None => None
    end.

  Definition lookup_inductive Σ := lookup_inductive_gen (lookup_env Σ).

  Definition lookup_constructor_gen lookup ind k :=
    match lookup_inductive_gen lookup ind with
    | Some (mdecl, idecl) =>
      match nth_error idecl.(ind_ctors) k with
      | Some cdecl => Some (mdecl, idecl, cdecl)
      | None => None
      end
    | _ => None
    end.

  Definition lookup_constructor Σ := lookup_constructor_gen (lookup_env Σ).

  Definition lookup_projection_gen lookup p :=
    match lookup_constructor_gen lookup p.(proj_ind) 0 with
    | Some (mdecl, idecl, cdecl) =>
      match nth_error idecl.(ind_projs) p.(proj_arg) with
      | Some pdecl => Some (mdecl, idecl, cdecl, pdecl)
      | None => None
      end
    | _ => None
    end.

  Definition lookup_projection Σ := lookup_projection_gen (lookup_env Σ).

  Lemma declared_constant_lookup_gen {lookup kn cdecl} :
    declared_constant_gen lookup kn cdecl ->
    lookup_constant_gen lookup kn = Some cdecl.
Admitted.

  Lemma lookup_constant_declared_gen {lookup kn cdecl} :
    lookup_constant_gen lookup kn = Some cdecl ->
    declared_constant_gen lookup kn cdecl.
Admitted.

  Lemma declared_minductive_lookup_gen {lookup ind mdecl} :
    declared_minductive_gen lookup ind mdecl ->
    lookup_minductive_gen lookup ind = Some mdecl.
Admitted.

  Lemma lookup_minductive_declared_gen {lookup ind mdecl} :
    lookup_minductive_gen lookup ind = Some mdecl ->
    declared_minductive_gen lookup ind mdecl.
Admitted.

  Lemma declared_inductive_lookup_gen {lookup ind mdecl idecl} :
    declared_inductive_gen lookup ind mdecl idecl ->
    lookup_inductive_gen lookup ind = Some (mdecl, idecl).
Admitted.

  Lemma lookup_inductive_declared_gen {lookup ind mdecl idecl} :
    lookup_inductive_gen lookup ind = Some (mdecl, idecl) ->
    declared_inductive_gen lookup ind mdecl idecl.
Admitted.

  Lemma declared_constructor_lookup_gen {lookup id mdecl idecl cdecl} :
    declared_constructor_gen lookup id mdecl idecl cdecl ->
    lookup_constructor_gen lookup id.1 id.2 = Some (mdecl, idecl, cdecl).
Admitted.

  Lemma lookup_constructor_declared_gen {lookup id mdecl idecl cdecl} :
    lookup_constructor_gen lookup id.1 id.2 = Some (mdecl, idecl, cdecl) ->
    declared_constructor_gen lookup id mdecl idecl cdecl.
Admitted.

  Lemma declared_projection_lookup_gen {lookup p mdecl idecl cdecl pdecl} :
    declared_projection_gen lookup p mdecl idecl cdecl pdecl ->
    lookup_projection_gen lookup p = Some (mdecl, idecl, cdecl, pdecl).
Admitted.

  Lemma lookup_projection_declared_gen {lookup p mdecl idecl cdecl pdecl} :
    ind_npars mdecl = p.(proj_npars) ->
    lookup_projection_gen lookup p = Some (mdecl, idecl, cdecl, pdecl) ->
    declared_projection_gen lookup p mdecl idecl cdecl pdecl.
Admitted.

  Definition on_udecl_decl {A} (F : universes_decl -> A) d : A :=
  match d with
  | ConstantDecl cb => F cb.(cst_universes)
  | InductiveDecl mb => F mb.(ind_universes)
  end.

  Definition universes_decl_of_decl := on_udecl_decl (fun x => x).
Definition global_levels (univs : ContextSet.t) : LevelSet.t. exact (LevelSet.union (ContextSet.levels univs) (LevelSet.singleton (Level.lzero))). Defined.

  Lemma global_levels_InSet Σ :
    LevelSet.In Level.lzero (global_levels Σ).
Admitted.

  Lemma global_levels_memSet univs :
    LevelSet.mem Level.lzero (global_levels univs) = true.
Admitted.
Definition global_constraints (Σ : global_env) : ConstraintSet.t. exact (snd Σ.(universes)). Defined.
Definition global_uctx (Σ : global_env) : ContextSet.t. exact ((global_levels Σ.(universes), global_constraints Σ)). Defined.
Definition global_ext_levels (Σ : global_env_ext) : LevelSet.t. exact (LevelSet.union (levels_of_udecl (snd Σ)) (global_levels Σ.1.(universes))). Defined.
Definition global_ext_constraints (Σ : global_env_ext) : ConstraintSet.t. exact (ConstraintSet.union
      (constraints_of_udecl (snd Σ))
      (global_constraints Σ.1)). Defined.

  Coercion global_ext_constraints : global_env_ext >-> ConstraintSet.t.
Definition global_ext_uctx (Σ : global_env_ext) : ContextSet.t. exact ((global_ext_levels Σ, global_ext_constraints Σ)). Defined.

  Lemma global_ext_levels_InSet Σ :
    LevelSet.In Level.lzero (global_ext_levels Σ).
Admitted.

   

  Definition consistent_instance `{checker_flags} (lvs : LevelSet.t) (φ : ConstraintSet.t) uctx (u : Instance.t) :=
    match uctx with
    | Monomorphic_ctx => List.length u = 0
    | Polymorphic_ctx c =>
       
      forallb (fun l => LevelSet.mem l lvs) u /\
      List.length u = List.length c.1 /\
      valid_constraints φ (subst_instance_cstrs u c.2)
    end.

  Definition consistent_instance_ext `{checker_flags} Σ :=
    consistent_instance (global_ext_levels Σ) (global_ext_constraints Σ).

  Lemma consistent_instance_length {cf : checker_flags} {Σ : global_env_ext} {univs u} :
    consistent_instance_ext Σ univs u ->
    #|u| = #|abstract_instance univs|.
Admitted.

  Definition wf_universe Σ s : Prop :=
    Universe.on_sort
      (fun u => forall l, LevelExprSet.In l u -> LevelSet.In (LevelExpr.get_level l) (global_ext_levels Σ))
      True s.

  Definition wf_universe_dec Σ s : {@wf_universe Σ s} + {~@wf_universe Σ s}.
Admitted.

  Lemma declared_ind_declared_constructors `{cf : checker_flags} {Σ ind mib oib} :
    declared_inductive Σ ind mib oib ->
    Alli (fun i => declared_constructor Σ (ind, i) mib oib) 0 (ind_ctors oib).
Admitted.

End Lookup.

Module Type LookupSig (T : Term) (E : EnvironmentSig T).
  Include Lookup T E.
End LookupSig.

Module EnvTyping (T : Term) (E : EnvironmentSig T) (TU : TermUtils T E).
Import T.
Import E.
Import TU.

  Section TypeLocal.
    Context (typing : forall (Γ : context), term -> typ_or_sort -> Type).

    Inductive All_local_env : context -> Type :=
    | localenv_nil :
        All_local_env []

    | localenv_cons_abs Γ na t :
        All_local_env Γ ->
        typing Γ t Sort ->
        All_local_env (Γ ,, vass na t)

    | localenv_cons_def Γ na b t :
        All_local_env Γ ->
        typing Γ t Sort ->
        typing Γ b (Typ t) ->
        All_local_env (Γ ,, vdef na b t).
  Derive Signature NoConfusion for All_local_env.
  End TypeLocal.

  Arguments localenv_nil {_}.
  Arguments localenv_cons_def {_ _ _ _ _} _ _.
  Arguments localenv_cons_abs {_ _ _ _} _ _.

  Lemma All_local_env_fold P f Γ :
    All_local_env (fun Γ t T => P (fold_context_k f Γ) (f #|Γ| t) (typ_or_sort_map (f #|Γ|) T)) Γ <~>
    All_local_env P (fold_context_k f Γ).
Admitted.

  Lemma All_local_env_impl (P Q : context -> term -> typ_or_sort -> Type) l :
    All_local_env P l ->
    (forall Γ t T, P Γ t T -> Q Γ t T) ->
    All_local_env Q l.
Admitted.

  Lemma All_local_env_impl_ind {P Q : context -> term -> typ_or_sort -> Type} {l} :
    All_local_env P l ->
    (forall Γ t T, All_local_env Q Γ -> P Γ t T -> Q Γ t T) ->
    All_local_env Q l.
Admitted.

  Lemma All_local_env_skipn P Γ : All_local_env P Γ -> forall n, All_local_env P (skipn n Γ).
Admitted.
  #[global]
  Hint Resolve All_local_env_skipn : wf.

  Section All_local_env_rel.

    Definition All_local_rel P Γ Γ'
      := (All_local_env (fun Γ0 t T => P (Γ ,,, Γ0) t T) Γ').
Definition All_local_rel_nil {P Γ} : All_local_rel P Γ []. exact (localenv_nil). Defined.
Definition All_local_rel_abs {P Γ Γ' A na} :
      All_local_rel P Γ Γ' -> P (Γ ,,, Γ') A Sort
      -> All_local_rel P Γ (Γ',, vass na A). exact (localenv_cons_abs). Defined.
Definition All_local_rel_def {P Γ Γ' t A na} :
      All_local_rel P Γ Γ' ->
      P (Γ ,,, Γ') A Sort ->
      P (Γ ,,, Γ') t (Typ A) ->
      All_local_rel P Γ (Γ',, vdef na t A). exact (localenv_cons_def). Defined.

    Lemma All_local_rel_local :
      forall P Γ,
        All_local_env P Γ ->
        All_local_rel P [] Γ.
Admitted.

    Lemma All_local_local_rel P Γ :
      All_local_rel P [] Γ -> All_local_env P Γ.
Admitted.

    Lemma All_local_app_rel {P Γ Γ'} :
      All_local_env P (Γ ,,, Γ') -> All_local_env P Γ × All_local_rel P Γ Γ'.
Admitted.

    Lemma All_local_rel_app {P Γ Γ'} :
      All_local_env P Γ -> All_local_rel P Γ Γ' -> All_local_env P (Γ ,,, Γ').
Admitted.

  End All_local_env_rel.

   

  Definition on_local_decl (P : context -> term -> typ_or_sort -> Type) Γ d :=
    match d.(decl_body) with
    | Some b => P Γ b (Typ d.(decl_type))
    | None => P Γ d.(decl_type) Sort
    end.

  Definition on_def_type (P : context -> term -> typ_or_sort -> Type) Γ d :=
    P Γ d.(dtype) Sort.

  Definition on_def_body (P : context -> term -> typ_or_sort -> Type) types Γ d :=
    P (Γ ,,, types) d.(dbody) (Typ (lift0 #|types| d.(dtype))).
Definition lift_judgment
    (check : global_env_ext -> context -> term -> term -> Type)
    (infer_sort : global_env_ext -> context -> term -> Type) :
    (global_env_ext -> context -> term -> typ_or_sort -> Type). exact (fun Σ Γ t T =>
    match T with
    | Typ T => check Σ Γ t T
    | Sort => infer_sort Σ Γ t
    end). Defined.

  Lemma lift_judgment_impl {P Ps Q Qs Σ Σ' Γ Γ' t t' T} :
    lift_judgment P Ps Σ Γ t T ->
    (forall T, P Σ Γ t T -> Q Σ' Γ' t' T) ->
    (Ps Σ Γ t -> Qs Σ' Γ' t') ->
    lift_judgment Q Qs Σ' Γ' t' T.
Admitted.

   

  Definition lift_wf_term wf_term := (lift_judgment (fun Σ Γ t T => wf_term Σ Γ t × wf_term Σ Γ T) wf_term).

  Definition infer_sort (sorting : global_env_ext -> context -> term -> Universe.t -> Type) := (fun Σ Γ T => { s : Universe.t & sorting Σ Γ T s }).
  Notation typing_sort typing := (fun Σ Γ T s => typing Σ Γ T (tSort s)).

  Definition lift_typing typing := lift_judgment typing (infer_sort (typing_sort typing)).
  Definition lift_sorting checking sorting := lift_judgment checking (infer_sort sorting).

  Notation Prop_conj P Q := (fun Σ Γ t T => P Σ Γ t T × Q Σ Γ t T).

  Definition lift_typing2 P Q := lift_typing (Prop_conj P Q).

  Lemma infer_sort_impl {P Q} {Σ Σ' : global_env_ext} {Γ Γ' : context} {t t' : term} :
    forall f, forall tu: infer_sort P Σ Γ t,
    let s := tu.π1 in
    (P Σ Γ t s -> Q Σ' Γ' t' (f s)) ->
    infer_sort Q Σ' Γ' t'.
Admitted.

  Lemma infer_typing_sort_impl {P Q} {Σ Σ' : global_env_ext} {Γ Γ' : context} {t t' : term} :
    forall f, forall tu: infer_sort (typing_sort P) Σ Γ t,
    let s := tu.π1 in
    (P Σ Γ t (tSort s) -> Q Σ' Γ' t' (tSort (f s))) ->
    infer_sort (typing_sort Q) Σ' Γ' t'.
Admitted.

  Lemma lift_typing_impl {P Q Σ Σ' Γ Γ' t t' T} :
    lift_typing P Σ Γ t T ->
    (forall T, P Σ Γ t T -> Q Σ' Γ' t' T) ->
    lift_typing Q Σ' Γ' t' T.
Admitted.

  Section TypeLocalOver.
    Context (checking : global_env_ext -> context -> term -> term -> Type).
    Context (sorting : global_env_ext -> context -> term -> Type).
    Context (cproperty : forall (Σ : global_env_ext) (Γ : context),
                All_local_env (lift_judgment checking sorting Σ) Γ ->
                forall (t T : term), checking Σ Γ t T -> Type).
    Context (sproperty : forall (Σ : global_env_ext) (Γ : context),
                All_local_env (lift_judgment checking sorting Σ) Γ ->
                forall (t : term), sorting Σ Γ t -> Type).

    Inductive All_local_env_over_gen (Σ : global_env_ext) :
        forall (Γ : context), All_local_env (lift_judgment checking sorting Σ) Γ -> Type :=
    | localenv_over_nil :
        All_local_env_over_gen Σ [] localenv_nil

    | localenv_over_cons_abs Γ na t
        (all : All_local_env (lift_judgment checking sorting Σ) Γ) :
        All_local_env_over_gen Σ Γ all ->
        forall (tu : lift_judgment checking sorting Σ Γ t Sort)
          (Hs: sproperty Σ Γ all _ tu),
          All_local_env_over_gen Σ (Γ ,, vass na t)
                              (localenv_cons_abs all tu)

    | localenv_over_cons_def Γ na b t
        (all : All_local_env (lift_judgment checking sorting Σ) Γ) (tb : checking Σ Γ b t) :
        All_local_env_over_gen Σ Γ all ->
        forall (Hc: cproperty Σ Γ all _ _ tb),
        forall (tu : lift_judgment checking sorting Σ Γ t Sort)
          (Hs: sproperty Σ Γ all _ tu),
          All_local_env_over_gen Σ (Γ ,, vdef na b t)
                              (localenv_cons_def all tu tb).

  End TypeLocalOver.
  Derive Signature for All_local_env_over_gen.

  Definition All_local_env_over typing property :=
    (All_local_env_over_gen typing (infer_sort (typing_sort typing)) property (fun Σ Γ H t tu => property _ _ H _ _ tu.π2)).

  Definition All_local_env_over_sorting checking sorting cproperty (sproperty : forall Σ Γ _ t s, sorting Σ Γ t s -> Type) :=
    (All_local_env_over_gen checking (infer_sort sorting) cproperty (fun Σ Γ H t tu => sproperty Σ Γ H t tu.π1 tu.π2)).

  Section TypeCtxInst.
    Context (typing : forall (Σ : global_env_ext) (Γ : context), term -> term -> Type).

     
    Inductive ctx_inst Σ (Γ : context) : list term -> context -> Type :=
    | ctx_inst_nil : ctx_inst Σ Γ [] []
    | ctx_inst_ass na t i inst Δ :
        typing Σ Γ i t ->
        ctx_inst Σ Γ inst (subst_telescope [i] 0 Δ) ->
        ctx_inst Σ Γ (i :: inst) (vass na t :: Δ)
    | ctx_inst_def na b t inst Δ :
        ctx_inst Σ Γ inst (subst_telescope [b] 0 Δ) ->
        ctx_inst Σ Γ inst (vdef na b t :: Δ).
    Derive Signature NoConfusion for ctx_inst.
  End TypeCtxInst.

  Lemma ctx_inst_impl_gen Σ Γ inst Δ args P :
    { P' & ctx_inst P' Σ Γ inst Δ } ->
    (forall t T,
        All (fun P' => P' Σ Γ t T) args ->
        P Σ Γ t T) ->
    All (fun P' => ctx_inst P' Σ Γ inst Δ) args ->
    ctx_inst P Σ Γ inst Δ.
Admitted.

  Lemma ctx_inst_impl P Q Σ Γ inst Δ :
    ctx_inst P Σ Γ inst Δ ->
    (forall t T, P Σ Γ t T -> Q Σ Γ t T) ->
    ctx_inst Q Σ Γ inst Δ.
Admitted.

  Section All_local_env_size.
    Context {P : forall (Σ : global_env_ext) (Γ : context), term -> typ_or_sort -> Type}.
    Context (Psize : forall (Σ : global_env_ext) Γ t T, P Σ Γ t T -> size).

    Fixpoint All_local_env_size_gen base Σ Γ (w : All_local_env (P Σ) Γ) : size :=
      match w with
      | localenv_nil => base
      | localenv_cons_abs Γ' na t w' p => Psize _ _ _ _ p + All_local_env_size_gen base _ _ w'
      | localenv_cons_def Γ' na b t w' pt pb => Psize _ _ _ _ pt + Psize _ _ _ _ pb + All_local_env_size_gen base _ _ w'
      end.

    Lemma All_local_env_size_pos base Σ Γ w : base <= All_local_env_size_gen base Σ Γ w.
Admitted.
  End All_local_env_size.

  Notation All_local_rel_size_gen Psize base := (fun Σ Γ Δ (w : All_local_rel _ Γ Δ) =>
    All_local_env_size_gen (fun Σ Δ => Psize Σ (Γ ,,, Δ)) base Σ Δ w).

  Lemma All_local_env_size_app P Psize base Σ Γ Γ' (wfΓ : All_local_env (P Σ) Γ) (wfΓ' : All_local_rel (P Σ) Γ Γ') :
    All_local_env_size_gen Psize base _ _ (All_local_rel_app wfΓ wfΓ') + base = All_local_env_size_gen Psize base _ _ wfΓ + All_local_rel_size_gen Psize base _ _ _ wfΓ'.
Admitted.

  Section lift_judgment_size.
    Context {checking : global_env_ext -> context -> term -> term -> Type}.
    Context {sorting : global_env_ext -> context -> term -> Type}.
    Context (csize : forall (Σ : global_env_ext) (Γ : context) (t T : term), checking Σ Γ t T -> size).
    Context (ssize : forall (Σ : global_env_ext) (Γ : context) (t : term), sorting Σ Γ t -> size).
Definition lift_judgment_size Σ Γ t T (w : lift_judgment checking sorting Σ Γ t T) : size. exact (match T return lift_judgment checking sorting Σ Γ t T -> size with
      | Typ T => csize _ _ _ _
      | Sort => ssize _ _ _
      end w). Defined.
  End lift_judgment_size.

  Implicit Types (Σ : global_env_ext) (Γ : context) (t : term).

  Notation infer_sort_size  typing_size := (fun Σ Γ t   (tu: infer_sort _ Σ Γ t) => let 'existT s d := tu in typing_size Σ Γ t s d).
  Notation typing_sort_size typing_size := (fun Σ Γ t s (tu: typing_sort _ Σ Γ t s) => typing_size Σ Γ t (tSort s) tu).

  Section Regular.
    Context {typing : global_env_ext -> context -> term -> term -> Type}.
    Context (typing_size : forall Σ Γ t T, typing Σ Γ t T -> size).

    Definition lift_typing_size := lift_judgment_size typing_size (infer_sort_size (typing_sort_size typing_size)).
    Definition All_local_env_size := All_local_env_size_gen lift_typing_size 0.
    Definition All_local_rel_size := All_local_rel_size_gen lift_typing_size 0.
  End Regular.

  Section Bidirectional.
    Context {checking : global_env_ext -> context -> term -> term -> Type} {sorting : global_env_ext -> context -> term -> Universe.t -> Type}.
    Context (checking_size : forall Σ Γ t T, checking Σ Γ t T -> size).
    Context (sorting_size : forall Σ Γ t s, sorting Σ Γ t s -> size).

    Definition lift_sorting_size := lift_judgment_size checking_size (infer_sort_size sorting_size).
    Definition All_local_env_sorting_size := All_local_env_size_gen lift_sorting_size 1.
    Definition All_local_rel_sorting_size := All_local_rel_size_gen lift_sorting_size 1.
  End Bidirectional.

End EnvTyping.

Module Type EnvTypingSig (T : Term) (E : EnvironmentSig T) (TU : TermUtils T E).
  Include EnvTyping T E TU.
End EnvTypingSig.

Module Conversion (T : Term) (E : EnvironmentSig T) (TU : TermUtils T E) (ET : EnvTypingSig T E TU).
Import T.
Import E.
Import TU.
Import ET.

  Section Conversion.
  Context (cumul_gen : global_env_ext -> context -> conv_pb -> term -> term -> Type).

  Inductive All_decls_alpha_pb {pb} {P : conv_pb -> term -> term -> Type} :
    context_decl -> context_decl -> Type :=
  | all_decls_alpha_vass {na na' : binder_annot name} {t t' : term}
    (eqna : eq_binder_annot na na')
    (eqt : P pb t t') :
    All_decls_alpha_pb (vass na t) (vass na' t')

  | all_decls_alpha_vdef {na na' : binder_annot name} {b t b' t' : term}
    (eqna : eq_binder_annot na na')
    (eqb : P Conv b b')  
    (eqt : P pb t t') :
    All_decls_alpha_pb (vdef na b t) (vdef na' b' t').

  Derive Signature NoConfusion for All_decls_alpha_pb.

  Arguments All_decls_alpha_pb pb P : clear implicits.

  Definition cumul_pb_decls pb (Σ : global_env_ext) (Γ Γ' : context) : forall (x y : context_decl), Type :=
    All_decls_alpha_pb pb (cumul_gen Σ Γ).

  Definition cumul_pb_context pb (Σ : global_env_ext) :=
    All2_fold (cumul_pb_decls pb Σ).

  Definition cumul_ctx_rel Σ Γ Δ Δ' :=
    All2_fold (fun Δ Δ' => cumul_pb_decls Cumul Σ (Γ ,,, Δ) (Γ ,,, Δ')) Δ Δ'.
  End Conversion.

  Arguments All_decls_alpha_pb pb P : clear implicits.
  Notation conv cumul_gen Σ Γ := (cumul_gen Σ Γ Conv).
  Notation cumul cumul_gen Σ Γ := (cumul_gen Σ Γ Cumul).

  Notation conv_decls cumul_gen := (cumul_pb_decls cumul_gen Conv).
  Notation cumul_decls cumul_gen := (cumul_pb_decls cumul_gen Cumul).
  Notation conv_context cumul_gen Σ := (cumul_pb_context cumul_gen Conv Σ).
  Notation cumul_context cumul_gen Σ := (cumul_pb_context cumul_gen Cumul Σ).

  Lemma All_decls_alpha_pb_impl {pb} {P Q : conv_pb -> term -> term -> Type} {t t'} :
    (forall pb t t', P pb t t' -> Q pb t t') ->
    All_decls_alpha_pb pb P t t' -> All_decls_alpha_pb pb Q t t'.
Admitted.
End Conversion.

Module Type ConversionSig (T : Term) (E : EnvironmentSig T) (TU : TermUtils T E) (ET : EnvTypingSig T E TU).
  Include Conversion T E TU ET.
End ConversionSig.

Module GlobalMaps (T: Term) (E: EnvironmentSig T) (TU : TermUtils T E) (ET: EnvTypingSig T E TU) (C: ConversionSig T E TU ET) (L: LookupSig T E).
Import T.
Import E.
Import TU.
Import ET.
Import C.
Import L.

  Section GlobalMaps.

    Context {cf: checker_flags}.
    Context (Pcmp: global_env_ext -> context -> conv_pb -> term -> term -> Type).
    Context (P : global_env_ext -> context -> term -> typ_or_sort -> Type).
    Definition on_context Σ ctx :=
      All_local_env (P Σ) ctx.

     
    Fixpoint type_local_ctx Σ (Γ Δ : context) (u : Universe.t) : Type :=
      match Δ with
      | [] => wf_universe Σ u
      | {| decl_body := None;   decl_type := t |} :: Δ => type_local_ctx Σ Γ Δ u × P Σ (Γ ,,, Δ) t (Typ (tSort u))
      | {| decl_body := Some b; decl_type := t |} :: Δ => type_local_ctx Σ Γ Δ u × P Σ (Γ ,,, Δ) t Sort × P Σ (Γ ,,, Δ) b (Typ t)
      end.

    Fixpoint sorts_local_ctx Σ (Γ Δ : context) (us : list Universe.t) : Type :=
      match Δ, us with
      | [], [] => unit
      | {| decl_body := None;   decl_type := t |} :: Δ, u :: us =>
        sorts_local_ctx Σ Γ Δ us × P Σ (Γ ,,, Δ) t (Typ (tSort u))
      | {| decl_body := Some b; decl_type := t |} :: Δ, us =>
        sorts_local_ctx Σ Γ Δ us × P Σ (Γ ,,, Δ) t Sort × P Σ (Γ ,,, Δ) b (Typ t)
      | _, _ => False
      end.

    Implicit Types (mdecl : mutual_inductive_body) (idecl : one_inductive_body) (cdecl : constructor_body).

    Definition on_type Σ Γ T := P Σ Γ T Sort.

    Open Scope type_scope.

    Definition univs_ext_constraints univs φ :=
      ConstraintSet.union (constraints_of_udecl φ) univs.

    Definition satisfiable_udecl (univs : ContextSet.t) φ
      := consistent (univs_ext_constraints (ContextSet.constraints univs) φ).

     
    Definition valid_on_mono_udecl (univs : ContextSet.t) ϕ :=
      consistent_extension_on univs (constraints_of_udecl ϕ).

     
     
     
    Definition on_udecl (univs : ContextSet.t) (udecl : universes_decl)
      := let levels := levels_of_udecl udecl in
        let global_levels := global_levels univs in
        let all_levels := LevelSet.union levels global_levels in
        LevelSet.For_all (fun l => ~ LevelSet.In l global_levels) levels
        /\ ConstraintSet.For_all (declared_cstr_levels all_levels) (constraints_of_udecl udecl)
        /\ satisfiable_udecl univs udecl
        /\ valid_on_mono_udecl univs udecl.

     
     

     

    Definition ind_realargs (o : one_inductive_body) :=
      match destArity [] o.(ind_type) with
      | Some (ctx, _) => #|smash_context [] ctx|
      | _ => 0
      end.

    Definition mdecl_at_i mdecl i (Γ:context) k : Prop :=
      #|Γ| <= k /\ k < #|Γ| + #|mdecl.(ind_bodies)| /\
       nth_error (List.rev mdecl.(ind_bodies)) (k - #|Γ|) = Some i.

    Reserved Notation " mdecl ;;; Γ |arg+> t " (at level 50, Γ, t at next level).
    Notation subst0 t := (subst t 0).
    Notation "M { j := N }" := (subst [N] j M) (at level 10, right associativity).

    Inductive positive_cstr_arg mdecl Γ : term -> Type :=
    | pos_arg_closed ty :
      closedn #|Γ| ty ->
      mdecl ;;; Γ |arg+> ty

    | pos_arg_concl l k i :
       
      #|l| = ind_realargs i -> All (closedn #|Γ|) l ->
      mdecl_at_i mdecl i Γ k ->
      mdecl ;;; Γ |arg+> mkApps (tRel k) l

    | pos_arg_let na b ty ty' :
      mdecl ;;; Γ |arg+> ty' {0 := b} ->
      mdecl ;;; Γ |arg+> tLetIn na b ty ty'

    | pos_arg_ass na ty ty' :
      closedn #|Γ| ty ->
      mdecl ;;; vass na ty :: Γ |arg+> ty' ->
      mdecl ;;; Γ |arg+> tProd na ty ty'

  where " mdecl ;;; Γ |arg+> t " := (positive_cstr_arg mdecl Γ t) : type_scope.

     

    Reserved Notation " mdecl @ i ;;; Γ |+> t " (at level 50, i, Γ, t at next level).

    Inductive positive_cstr mdecl i Γ : term -> Type :=
    | pos_concl l (headrel := (#|mdecl.(ind_bodies)| - S i + #|Γ|)%nat) :
      All (closedn #|Γ|) l ->
      mdecl @ i ;;; Γ |+> mkApps (tRel headrel) l

    | pos_let na b ty ty' :
      mdecl @ i ;;; Γ |+> ty' {0 := b} ->
      mdecl @ i ;;; Γ |+> tLetIn na b ty ty'

    | pos_ass na ty ty' :
      mdecl ;;; Γ |arg+> ty ->
      mdecl @ i ;;; vass na ty :: Γ |+> ty' ->
      mdecl @ i ;;; Γ |+> tProd na ty ty'

    where " mdecl @ i ;;; Γ |+> t " := (positive_cstr mdecl i Γ t) : type_scope.

    Definition lift_level n l :=
      match l with
      | Level.lzero | Level.level _ => l
      | Level.lvar k => Level.lvar (n + k)
      end.

    Definition lift_instance n l :=
      map (lift_level n) l.

    Definition lift_constraint n (c : Level.t * ConstraintType.t * Level.t) :=
      let '((l, r), l') := c in
      ((lift_level n l, r), lift_level n l').

    Definition lift_constraints n cstrs :=
      ConstraintSet.fold (fun elt acc => ConstraintSet.add (lift_constraint n elt) acc)
        cstrs ConstraintSet.empty.

    Definition level_var_instance n (inst : list name) :=
      mapi_rec (fun i _ => Level.lvar i) inst n.

    Fixpoint variance_cstrs (v : list Variance.t) (u u' : Instance.t) :=
      match v, u, u' with
      | _, [], [] => ConstraintSet.empty
      | v :: vs, u :: us, u' :: us' =>
        match v with
        | Variance.Irrelevant => variance_cstrs vs us us'
        | Variance.Covariant => ConstraintSet.add (u, ConstraintType.Le 0, u') (variance_cstrs vs us us')
        | Variance.Invariant => ConstraintSet.add (u, ConstraintType.Eq, u') (variance_cstrs vs us us')
        end
      | _, _, _ =>   ConstraintSet.empty
      end.

     

    Definition variance_universes univs v :=
      match univs with
      | Monomorphic_ctx => None
      | Polymorphic_ctx auctx =>
        let (inst, cstrs) := auctx in
        let u' := level_var_instance 0 inst in
        let u := lift_instance #|inst| u' in
        let cstrs := ConstraintSet.union cstrs (lift_constraints #|inst| cstrs) in
        let cstrv := variance_cstrs v u u' in
        let auctx' := (inst ++ inst, ConstraintSet.union cstrs cstrv) in
        Some (Polymorphic_ctx auctx', u, u')
      end.

     

    Definition ind_arities mdecl := arities_context (ind_bodies mdecl).

    Definition ind_respects_variance Σ mdecl v indices :=
      let univs := ind_universes mdecl in
      match variance_universes univs v with
      | Some (univs, u, u') =>
        cumul_ctx_rel Pcmp (Σ, univs) (smash_context [] (ind_params mdecl))@[u]
          (expand_lets_ctx (ind_params mdecl) (smash_context [] indices))@[u]
          (expand_lets_ctx (ind_params mdecl) (smash_context [] indices))@[u']
      | None => False
      end.

    Definition cstr_respects_variance Σ mdecl v cs :=
      let univs := ind_universes mdecl in
      match variance_universes univs v with
      | Some (univs, u, u') =>
        cumul_ctx_rel Pcmp (Σ, univs) (ind_arities mdecl ,,, smash_context [] (ind_params mdecl))@[u]
          (expand_lets_ctx (ind_params mdecl) (smash_context [] (cstr_args cs)))@[u]
          (expand_lets_ctx (ind_params mdecl) (smash_context [] (cstr_args cs)))@[u'] *
        All2
          (Pcmp (Σ, univs) (ind_arities mdecl ,,, smash_context [] (ind_params mdecl ,,, cstr_args cs))@[u] Conv)
          (map (subst_instance u ∘ expand_lets (ind_params mdecl ,,, cstr_args cs)) (cstr_indices cs))
          (map (subst_instance u' ∘ expand_lets (ind_params mdecl ,,, cstr_args cs)) (cstr_indices cs))
      | None => False  
      end.

     
    Definition cstr_concl_head mdecl i cdecl :=
      tRel (#|mdecl.(ind_bodies)| - S i + #|mdecl.(ind_params)| + #|cstr_args cdecl|).

     
    Definition cstr_concl mdecl i cdecl :=
      (mkApps (cstr_concl_head mdecl i cdecl)
        (to_extended_list_k mdecl.(ind_params) #|cstr_args cdecl|
          ++ cstr_indices cdecl)).

    Record on_constructor Σ mdecl i idecl ind_indices cdecl cunivs := {
       
      cstr_args_length : context_assumptions (cstr_args cdecl) = cstr_arity cdecl;

      cstr_eq : cstr_type cdecl =
       it_mkProd_or_LetIn mdecl.(ind_params)
        (it_mkProd_or_LetIn (cstr_args cdecl)
          (cstr_concl mdecl i cdecl));
       

      on_ctype : on_type Σ (arities_context mdecl.(ind_bodies)) (cstr_type cdecl);
      on_cargs :
        sorts_local_ctx Σ (arities_context mdecl.(ind_bodies) ,,, mdecl.(ind_params))
                      cdecl.(cstr_args) cunivs;
      on_cindices :
        ctx_inst (fun Σ Γ t T => P Σ Γ t (Typ T)) Σ (arities_context mdecl.(ind_bodies) ,,, mdecl.(ind_params) ,,, cdecl.(cstr_args))
                      cdecl.(cstr_indices)
                      (List.rev (lift_context #|cdecl.(cstr_args)| 0 ind_indices));

      on_ctype_positive :  
        positive_cstr mdecl i [] (cstr_type cdecl);

      on_ctype_variance :  
        forall v, ind_variance mdecl = Some v ->
        cstr_respects_variance Σ mdecl v cdecl;

      on_lets_in_type : if lets_in_constructor_types
                        then True else is_true (is_assumption_context (cstr_args cdecl))
    }.

    Arguments on_ctype {Σ mdecl i idecl ind_indices cdecl cunivs}.
    Arguments on_cargs {Σ mdecl i idecl ind_indices cdecl cunivs}.
    Arguments on_cindices {Σ mdecl i idecl ind_indices cdecl cunivs}.
    Arguments cstr_args_length {Σ mdecl i idecl ind_indices cdecl cunivs}.
    Arguments cstr_eq {Σ mdecl i idecl ind_indices cdecl cunivs}.

    Definition on_constructors Σ mdecl i idecl ind_indices :=
      All2 (on_constructor Σ mdecl i idecl ind_indices).

     

    Record on_proj mdecl mind i k (p : projection_body) decl :=
      { on_proj_name :  
          binder_name (decl_name decl) = nNamed p.(proj_name);
        on_proj_type :
           
          let u := abstract_instance mdecl.(ind_universes) in
          let ind := {| inductive_mind := mind; inductive_ind := i |} in
          p.(proj_type) = subst (inds mind u mdecl.(ind_bodies)) (S (ind_npars mdecl))
            (subst (projs ind mdecl.(ind_npars) k) 0
              (lift 1 k (decl_type decl)));
        on_proj_relevance : p.(proj_relevance) = decl.(decl_name).(binder_relevance) }.

    Definition on_projection mdecl mind i cdecl (k : nat) (p : projection_body) :=
      let Γ := smash_context [] (cdecl.(cstr_args) ++ mdecl.(ind_params)) in
      match nth_error Γ (context_assumptions cdecl.(cstr_args) - S k) with
      | None => False
      | Some decl => on_proj mdecl mind i k p decl
      end.

    Record on_projections mdecl mind i idecl (ind_indices : context) cdecl :=
      { on_projs_record : #|idecl.(ind_ctors)| = 1;
         

        on_projs_noidx : #|ind_indices| = 0;
         

        on_projs_elim : idecl.(ind_kelim) = IntoAny;
         

        on_projs_all : #|idecl.(ind_projs)| = context_assumptions (cstr_args cdecl);
         

        on_projs : Alli (on_projection mdecl mind i cdecl) 0 idecl.(ind_projs) }.

    Definition check_constructors_smaller φ cunivss ind_sort :=
      Forall (fun cunivs =>
        Forall (fun argsort => leq_universe φ argsort ind_sort) cunivs) cunivss.

     

    Definition constructor_univs := list Universe.t.
     

    Definition elim_sort_prop_ind (ind_ctors_sort : list constructor_univs) :=
      match ind_ctors_sort with
      | [] =>   IntoAny
      | [ s ] =>
        if forallb Universes.is_propositional s then
          IntoAny  
        else
          IntoPropSProp  
      | _ =>   IntoPropSProp
      end.

    Definition elim_sort_sprop_ind (ind_ctors_sort : list constructor_univs) :=
      match ind_ctors_sort with
      | [] =>   IntoAny
      | _ =>   IntoSProp
      end.

    Definition check_ind_sorts (Σ : global_env_ext)
              params kelim ind_indices cdecls ind_sort : Type :=
      if Universe.is_prop ind_sort then
         
         
        (allowed_eliminations_subset kelim (elim_sort_prop_ind cdecls) : Type)
      else if Universe.is_sprop ind_sort then
         
         
        (allowed_eliminations_subset kelim (elim_sort_sprop_ind cdecls) : Type)
      else
         
        check_constructors_smaller Σ cdecls ind_sort
        × if indices_matter then
            type_local_ctx Σ params ind_indices ind_sort
          else True.

    Record on_ind_body Σ mind mdecl i idecl :=
      {  
        ind_arity_eq : idecl.(ind_type)
                      = it_mkProd_or_LetIn mdecl.(ind_params)
                                (it_mkProd_or_LetIn idecl.(ind_indices) (tSort idecl.(ind_sort)));

         
        onArity : on_type Σ [] idecl.(ind_type);

         
        ind_cunivs : list constructor_univs;

         
        onConstructors :
          on_constructors Σ mdecl i idecl idecl.(ind_indices) idecl.(ind_ctors) ind_cunivs;

         
        onProjections :
          match idecl.(ind_projs), idecl.(ind_ctors) return Type with
          | [], _ => True
          | _, [ o ] =>
              on_projections mdecl mind i idecl idecl.(ind_indices) o
          | _, _ => False
          end;

         
        ind_sorts :
          check_ind_sorts Σ mdecl.(ind_params) idecl.(ind_kelim)
                          idecl.(ind_indices) ind_cunivs idecl.(ind_sort);

        onIndices :
           
          match ind_variance mdecl with
          | Some v => ind_respects_variance Σ mdecl v idecl.(ind_indices)
          | None => True
          end
      }.

    Definition on_variance Σ univs (variances : option (list Variance.t)) :=
      match univs return Type with
      | Monomorphic_ctx => variances = None
      | Polymorphic_ctx auctx =>
        match variances with
        | None => unit
        | Some v =>
          ∑ univs' i i',
            [/\ (variance_universes univs v = Some (univs', i, i')),
              consistent_instance_ext (Σ, univs') univs i,
              consistent_instance_ext (Σ, univs') univs i' &
              List.length v = #|UContext.instance (AUContext.repr auctx)|]
        end
      end.

     

    Record on_inductive Σ mind mdecl :=
      { onInductives : Alli (on_ind_body Σ mind mdecl) 0 mdecl.(ind_bodies);
         
        onParams : on_context Σ mdecl.(ind_params);
        onNpars : context_assumptions mdecl.(ind_params) = mdecl.(ind_npars);
         
        onVariance : on_variance Σ mdecl.(ind_universes) mdecl.(ind_variance);
      }.

     

    Definition on_constant_decl Σ d :=
      match d.(cst_body) with
      | Some trm => P Σ [] trm (Typ d.(cst_type))
      | None => on_type Σ [] d.(cst_type)
      end.

    Definition on_global_decl Σ kn decl :=
      match decl with
      | ConstantDecl d => on_constant_decl Σ d
      | InductiveDecl inds => on_inductive Σ kn inds
      end.
Definition fresh_global (s : kername) (g : global_declarations) : Prop. exact (Forall (fun g => g.1 <> s) g). Defined.

    Record on_global_decls_data (univs : ContextSet.t) retro (Σ : global_declarations) (kn : kername) (d : global_decl) :=
        {
          kn_fresh :  fresh_global kn Σ ;
          udecl := universes_decl_of_decl d ;
          on_udecl_udecl : on_udecl univs udecl ;
          on_global_decl_d : on_global_decl (mk_global_env univs Σ retro, udecl) kn d
        }.

    Inductive on_global_decls (univs : ContextSet.t) (retro : Retroknowledge.t): global_declarations -> Type :=
    | globenv_nil : on_global_decls univs retro []
    | globenv_decl Σ kn d :
        on_global_decls univs retro Σ ->
        on_global_decls_data univs retro Σ kn d ->
        on_global_decls univs retro (Σ ,, (kn, d)).

    Derive Signature for on_global_decls.

    Lemma fresh_global_iff_not_In kn Σ
      : fresh_global kn Σ <-> ~ In kn (map fst Σ).
Admitted.

    Lemma fresh_global_iff_lookup_global_None kn Σ
      : fresh_global kn Σ <-> lookup_global Σ kn = None.
Admitted.

    Lemma fresh_global_iff_lookup_globals_nil kn Σ
      : fresh_global kn Σ <-> lookup_globals Σ kn = [].
Admitted.

    Lemma NoDup_on_global_decls univs retro decls
      : on_global_decls univs retro decls -> NoDup (List.map fst decls).
Admitted.

    Definition on_global_univs (c : ContextSet.t) :=
      let levels := global_levels c in
      let cstrs := ContextSet.constraints c in
      ConstraintSet.For_all (declared_cstr_levels levels) cstrs /\
      LS.For_all (negb ∘ Level.is_var) levels /\
      consistent cstrs.
Definition on_global_env (g : global_env) : Type. exact (on_global_univs g.(universes) × on_global_decls g.(universes) g.(retroknowledge) g.(declarations)). Defined.

    Definition on_global_env_ext (Σ : global_env_ext) :=
      on_global_env Σ.1 × on_udecl Σ.(universes) Σ.2.

  End GlobalMaps.

  Arguments cstr_args_length {_ Pcmp P Σ mdecl i idecl ind_indices cdecl cunivs}.
  Arguments cstr_eq {_ Pcmp P Σ mdecl i idecl ind_indices cdecl cunivs}.
  Arguments on_ctype {_ Pcmp P Σ mdecl i idecl ind_indices cdecl cunivs}.
  Arguments on_cargs {_ Pcmp P Σ mdecl i idecl ind_indices cdecl cunivs}.
  Arguments on_cindices {_ Pcmp P Σ mdecl i idecl ind_indices cdecl cunivs}.
  Arguments on_ctype_positive {_ Pcmp P Σ mdecl i idecl ind_indices cdecl cunivs}.
  Arguments on_ctype_variance {_ Pcmp P Σ mdecl i idecl ind_indices cdecl cunivs}.

  Section Properties.
  End Properties.

Import MetaCoq.Utils.utils.
Import MetaCoq.Common.Primitive.

Inductive prim_model (term : Type) : prim_tag -> Type :=
| primIntModel (i : PrimInt63.int) : prim_model term primInt
| primFloatModel (f : PrimFloat.float) : prim_model term primFloat.

Definition prim_val term := ∑ t : prim_tag, prim_model term t.
Export MetaCoq.Common.Universes.
Export MetaCoq.Common.BasicAst.
Export MetaCoq.Common.Environment.

Record predicate {term} := mk_predicate {
  pparams : list term;
  puinst : Instance.t;
  pcontext : list (context_decl term);

  preturn : term;   }.
Arguments predicate : clear implicits.

Section map_predicate.
  Context {term term' : Type}.
  Context (uf : Instance.t -> Instance.t).
  Context (paramf preturnf : term -> term').
  Context (pcontextf : list (context_decl term) -> list (context_decl term')).

  Definition map_predicate (p : predicate term) :=
    {| pparams := map paramf p.(pparams);
        puinst := uf p.(puinst);
        pcontext := pcontextf p.(pcontext);
        preturn := preturnf p.(preturn) |}.

End map_predicate.

Section map_predicate_k.
  Context {term : Type}.
  Context (uf : Instance.t -> Instance.t).
  Context (f : nat -> term -> term).

  Definition map_predicate_k k (p : predicate term) :=
    {| pparams := map (f k) p.(pparams);
        puinst := uf p.(puinst);
        pcontext := p.(pcontext);
        preturn := f (#|p.(pcontext)| + k) p.(preturn) |}.

  Definition test_predicate_k (instp : Instance.t -> bool)
    (p : nat -> term -> bool) k (pred : predicate term) :=
    instp pred.(puinst) && forallb (p k) pred.(pparams) &&
    test_context_k p #|pred.(pparams)| pred.(pcontext) &&
    p (#|pred.(pcontext)| + k) pred.(preturn).

End map_predicate_k.

Section Branch.
  Context {term : Type}.

  Record branch := mk_branch {
    bcontext : list (context_decl term);

    bbody : term;   }.

  Definition test_branch_k (pred : predicate term) (p : nat -> term -> bool) k (b : branch) :=
    test_context_k p #|pred.(pparams)| b.(bcontext) && p (#|b.(bcontext)| + k) b.(bbody).

End Branch.
Arguments branch : clear implicits.

Section map_branch.
  Context {term term' : Type}.
  Context (f : term -> term').
  Context (g : list (BasicAst.context_decl term) -> list (BasicAst.context_decl term')).

  Definition map_branch (b : branch term) :=
  {| bcontext := g b.(bcontext);
      bbody := f b.(bbody) |}.
End map_branch.

Section map_branch_k.
  Context {term term' : Type}.
  Context (f : nat -> term -> term').
  Context (g : list (BasicAst.context_decl term) -> list (BasicAst.context_decl term')).
  Definition map_branch_k k (b : branch term) :=
  {| bcontext := g b.(bcontext);
     bbody := f (#|b.(bcontext)| + k) b.(bbody) |}.
End map_branch_k.

Notation map_branches_k f h k brs :=
  (List.map (map_branch_k f h k) brs).

Notation test_branches_k p test k brs :=
  (List.forallb (test_branch_k p test k) brs).

Inductive term :=
| tRel (n : nat)
| tVar (i : ident)
| tEvar (n : nat) (l : list term)
| tSort (u : Universe.t)
| tProd (na : aname) (A B : term)
| tLambda (na : aname) (A t : term)
| tLetIn (na : aname) (b B t : term)
| tApp (u v : term)
| tConst (k : kername) (ui : Instance.t)
| tInd (ind : inductive) (ui : Instance.t)
| tConstruct (ind : inductive) (n : nat) (ui : Instance.t)
| tCase (indn : case_info) (p : predicate term) (c : term) (brs : list (branch term))
| tProj (p : projection) (c : term)
| tFix (mfix : mfixpoint term) (idx : nat)
| tCoFix (mfix : mfixpoint term) (idx : nat)
| tPrim (prim : prim_val term).

Fixpoint mkApps t us :=
  match us with
  | nil => t
  | u :: us => mkApps (tApp t u) us
  end.

Fixpoint lift n k t : term :=
  match t with
  | tRel i => tRel (if Nat.leb k i then (n + i) else i)
  | tEvar ev args => tEvar ev (List.map (lift n k) args)
  | tLambda na T M => tLambda na (lift n k T) (lift n (S k) M)
  | tApp u v => tApp (lift n k u) (lift n k v)
  | tProd na A B => tProd na (lift n k A) (lift n (S k) B)
  | tLetIn na b t b' => tLetIn na (lift n k b) (lift n k t) (lift n (S k) b')
  | tCase ind p c brs =>
    let p' := map_predicate_k id (lift n) k p in
    let brs' := map_branches_k (lift n) id k brs in
    tCase ind p' (lift n k c) brs'
  | tProj p c => tProj p (lift n k c)
  | tFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (lift n k) (lift n k')) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (lift n k) (lift n k')) mfix in
    tCoFix mfix' idx
  | x => x
  end.

Notation lift0 n := (lift n 0).

Fixpoint subst s k u :=
  match u with
  | tRel n =>
    if Nat.leb k n then
      match nth_error s (n - k) with
      | Some b => lift0 k b
      | None => tRel (n - List.length s)
      end
    else tRel n
  | tEvar ev args => tEvar ev (List.map (subst s k) args)
  | tLambda na T M => tLambda na (subst s k T) (subst s (S k) M)
  | tApp u v => tApp (subst s k u) (subst s k v)
  | tProd na A B => tProd na (subst s k A) (subst s (S k) B)
  | tLetIn na b ty b' => tLetIn na (subst s k b) (subst s k ty) (subst s (S k) b')
  | tCase ind p c brs =>
    let p' := map_predicate_k id (subst s) k p in
    let brs' := map_branches_k (subst s) id k brs in
    tCase ind p' (subst s k c) brs'
  | tProj p c => tProj p (subst s k c)
  | tFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (subst s k) (subst s k')) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (subst s k) (subst s k')) mfix in
    tCoFix mfix' idx
  | x => x
  end.

Notation subst0 t := (subst t 0).
Definition subst1 t k u := subst [t] k u.
Notation "M { j := N }" := (subst1 N j M) (at level 10, right associativity).

Fixpoint closedn k (t : term) : bool :=
  match t with
  | tRel i => Nat.ltb i k
  | tEvar ev args => List.forallb (closedn k) args
  | tLambda _ T M | tProd _ T M => closedn k T && closedn (S k) M
  | tApp u v => closedn k u && closedn k v
  | tLetIn na b t b' => closedn k b && closedn k t && closedn (S k) b'
  | tCase ind p c brs =>
    let p' := test_predicate_k (fun _ => true) closedn k p in
    let brs' := test_branches_k p closedn k brs in
    p' && closedn k c && brs'
  | tProj p c => closedn k c
  | tFix mfix idx =>
    let k' := List.length mfix + k in
    List.forallb (test_def (closedn k) (closedn k')) mfix
  | tCoFix mfix idx =>
    let k' := List.length mfix + k in
    List.forallb (test_def (closedn k) (closedn k')) mfix
  | _ => true
  end.

Fixpoint noccur_between k n (t : term) : bool :=
  match t with
  | tRel i => Nat.ltb i k || Nat.leb (k + n) i
  | tEvar ev args => List.forallb (noccur_between k n) args
  | tLambda _ T M | tProd _ T M => noccur_between k n T && noccur_between (S k) n M
  | tApp u v => noccur_between k n u && noccur_between k n v
  | tLetIn na b t b' => noccur_between k n b && noccur_between k n t && noccur_between (S k) n b'
  | tCase ind p c brs =>
    let p' := test_predicate_k (fun _ => true) (fun k' => noccur_between k' n) k p in
    let brs' := test_branches_k p (fun k => noccur_between k n) k brs in
    p' && noccur_between k n c && brs'
  | tProj p c => noccur_between k n c
  | tFix mfix idx =>
    let k' := List.length mfix + k in
    List.forallb (test_def (noccur_between k n) (noccur_between k' n)) mfix
  | tCoFix mfix idx =>
    let k' := List.length mfix + k in
    List.forallb (test_def (noccur_between k n) (noccur_between k' n)) mfix
  | _ => true
  end.
#[global]
Instance subst_instance_constr : UnivSubst term.
exact (fix subst_instance_constr u c {struct c} : term :=
  match c with
  | tRel _ | tVar _ => c
  | tEvar ev args => tEvar ev (List.map (subst_instance_constr u) args)
  | tSort s => tSort (subst_instance_univ u s)
  | tConst c u' => tConst c (subst_instance_instance u u')
  | tInd i u' => tInd i (subst_instance_instance u u')
  | tConstruct ind k u' => tConstruct ind k (subst_instance_instance u u')
  | tLambda na T M => tLambda na (subst_instance_constr u T) (subst_instance_constr u M)
  | tApp f v => tApp (subst_instance_constr u f) (subst_instance_constr u v)
  | tProd na A B => tProd na (subst_instance_constr u A) (subst_instance_constr u B)
  | tLetIn na b ty b' => tLetIn na (subst_instance_constr u b) (subst_instance_constr u ty)
                                (subst_instance_constr u b')
  | tCase ind p c brs =>
    let p' := map_predicate (subst_instance_instance u) (subst_instance_constr u) (subst_instance_constr u) id p in
    let brs' := List.map (map_branch (subst_instance_constr u) id) brs in
    tCase ind p' (subst_instance_constr u c) brs'
  | tProj p c => tProj p (subst_instance_constr u c)
  | tFix mfix idx =>
    let mfix' := List.map (map_def (subst_instance_constr u) (subst_instance_constr u)) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let mfix' := List.map (map_def (subst_instance_constr u) (subst_instance_constr u)) mfix in
    tCoFix mfix' idx
  | tPrim _ => c
  end).
Defined.

Module PCUICTerm <: Term.

  Definition term := term.

  Definition tRel := tRel.
  Definition tSort := tSort.
  Definition tProd := tProd.
  Definition tLambda := tLambda.
  Definition tLetIn := tLetIn.
  Definition tInd := tInd.
  Definition tProj := tProj.
  Definition mkApps := mkApps.

  Definition lift := lift.
  Definition subst := subst.
  Definition closedn := closedn.
  Definition noccur_between := noccur_between.
  Definition subst_instance_constr := subst_instance.
End PCUICTerm.

Module PCUICEnvironment := Environment PCUICTerm.
Export PCUICEnvironment.

Module PCUICLookup := EnvironmentTyping.Lookup PCUICTerm PCUICEnvironment.
Include PCUICLookup.
Definition set_preturn (p : predicate term) (pret' : term) : predicate term.
Admitted.
Definition set_pparams (p : predicate term) (pars' : list term) : predicate term.
Admitted.

Fixpoint decompose_app_rec (t : term) l :=
  match t with
  | tApp f a => decompose_app_rec f (a :: l)
  | _ => (t, l)
  end.

Definition decompose_app t := decompose_app_rec t [].

Definition isConstruct_app t :=
  match fst (decompose_app t) with
  | tConstruct _ _ _ => true
  | _ => false
  end.

Definition inst_case_context params puinst (pctx : context) :=
  subst_context (List.rev params) 0 (subst_instance puinst pctx).

Definition inst_case_predicate_context (p : predicate term) :=
  inst_case_context p.(pparams) p.(puinst) p.(pcontext).

Definition inst_case_branch_context (p : predicate term) (br : branch term) :=
  inst_case_context p.(pparams) p.(puinst) br.(bcontext).

Definition iota_red npar p args br :=
  subst (List.rev (List.skipn npar args)) 0
    (expand_lets (inst_case_branch_context p br) (bbody br)).

Definition fix_subst (l : mfixpoint term) :=
  let fix aux n :=
      match n with
      | 0 => []
      | S n => tFix l n :: aux n
      end
  in aux (List.length l).

Definition unfold_fix (mfix : mfixpoint term) (idx : nat) :=
  match List.nth_error mfix idx with
  | Some d => Some (d.(rarg), subst0 (fix_subst mfix) d.(dbody))
  | None => None
  end.

Definition cofix_subst (l : mfixpoint term) :=
  let fix aux n :=
      match n with
      | 0 => []
      | S n => tCoFix l n :: aux n
      end
  in aux (List.length l).

Definition unfold_cofix (mfix : mfixpoint term) (idx : nat) :=
  match List.nth_error mfix idx with
  | Some d => Some (d.(rarg), subst0 (cofix_subst mfix) d.(dbody))
  | None => None
  end.

Definition is_constructor n ts :=
  match List.nth_error ts n with
  | Some a => isConstruct_app a
  | None => false
  end.
#[global]
Instance subst_instance_list A `{UnivSubst A} : UnivSubst (list A).
exact (fun u => List.map (subst_instance u)).
Defined.

Lemma subst_instance_lift u c n k :
  subst_instance u (lift n k c) = lift n k (subst_instance u c).
Admitted.

Lemma subst_instance_mkApps u f a :
  subst_instance u (mkApps f a) =
  mkApps (subst_instance u f) (map (subst_instance u) a).
Admitted.

Lemma subst_instance_subst u c (s : list term) k :
  subst_instance u (subst s k c) = subst (subst_instance u s) k (subst_instance u c).
Admitted.

Section compare_decls.

  Context {eq_term leq_term : term -> term -> Type}.
  Inductive compare_decls  : context_decl -> context_decl -> Type :=
  | compare_vass {na T na' T'} :
    eq_binder_annot na na' ->
    leq_term T T' ->
    compare_decls (vass na T) (vass na' T')
  | compare_vdef {na b T na' b' T'} :
    eq_binder_annot na na' ->
    eq_term b b' ->
    leq_term T T' ->
    compare_decls (vdef na b T) (vdef na' b' T').
End compare_decls.

#[global]
Hint Constructors compare_decls : pcuic.

Reserved Notation " Σ ;;; Γ |- t ⇝ u " (at level 50, Γ, t, u at next level).

Inductive red1 (Σ : global_env) (Γ : context) : term -> term -> Type :=

| red_beta na t b a :
  Σ ;;; Γ |- tApp (tLambda na t b) a ⇝ b {0 := a}

| red_zeta na b t b' :
  Σ ;;; Γ |- tLetIn na b t b' ⇝ b' {0 := b}

| red_rel i body :
    option_map decl_body (nth_error Γ i) = Some (Some body) ->
    Σ ;;; Γ |- tRel i ⇝ lift0 (S i) body

| red_iota ci c u args p brs br :
    nth_error brs c = Some br ->
    #|args| = (ci.(ci_npar) + context_assumptions br.(bcontext))%nat ->
    Σ ;;; Γ |- tCase ci p (mkApps (tConstruct ci.(ci_ind) c u) args) brs
        ⇝ iota_red ci.(ci_npar) p args br

| red_fix mfix idx args narg fn :
    unfold_fix mfix idx = Some (narg, fn) ->
    is_constructor narg args = true ->
    Σ ;;; Γ |- mkApps (tFix mfix idx) args ⇝ mkApps fn args

| red_cofix_case ip p mfix idx args narg fn brs :
    unfold_cofix mfix idx = Some (narg, fn) ->
    Σ ;;; Γ |- tCase ip p (mkApps (tCoFix mfix idx) args) brs ⇝
         tCase ip p (mkApps fn args) brs

| red_cofix_proj p mfix idx args narg fn :
    unfold_cofix mfix idx = Some (narg, fn) ->
    Σ ;;; Γ |- tProj p (mkApps (tCoFix mfix idx) args) ⇝ tProj p (mkApps fn args)

| red_delta c decl body (isdecl : declared_constant Σ c decl) u :
    decl.(cst_body) = Some body ->
    Σ ;;; Γ |- tConst c u ⇝ subst_instance u body

| red_proj p args u arg:
    nth_error args (p.(proj_npars) + p.(proj_arg)) = Some arg ->
    Σ ;;; Γ |- tProj p (mkApps (tConstruct p.(proj_ind) 0 u) args) ⇝ arg

| abs_red_l na M M' N : Σ ;;; Γ |- M ⇝ M' -> Σ ;;; Γ |- tLambda na M N ⇝ tLambda na M' N
| abs_red_r na M M' N : Σ ;;; Γ ,, vass na N |- M ⇝ M' -> Σ ;;; Γ |- tLambda na N M ⇝ tLambda na N M'

| letin_red_def na b t b' r : Σ ;;; Γ |- b ⇝ r -> Σ ;;; Γ |- tLetIn na b t b' ⇝ tLetIn na r t b'
| letin_red_ty na b t b' r : Σ ;;; Γ |- t ⇝ r -> Σ ;;; Γ |- tLetIn na b t b' ⇝ tLetIn na b r b'
| letin_red_body na b t b' r : Σ ;;; Γ ,, vdef na b t |- b' ⇝ r -> Σ ;;; Γ |- tLetIn na b t b' ⇝ tLetIn na b t r

| case_red_param ci p params' c brs :
    OnOne2 (fun t u => Σ ;;; Γ |- t ⇝ u) p.(pparams) params' ->
    Σ ;;; Γ |- tCase ci p c brs ⇝ tCase ci (set_pparams p params') c brs

| case_red_return ci p preturn' c brs :
  Σ ;;; Γ ,,, inst_case_predicate_context p |- p.(preturn) ⇝ preturn' ->
  Σ ;;; Γ |- tCase ci p c brs ⇝ tCase ci (set_preturn p preturn') c brs

| case_red_discr ci p c c' brs :
  Σ ;;; Γ |- c ⇝ c' -> Σ ;;; Γ |- tCase ci p c brs ⇝ tCase ci p c' brs

| case_red_brs ci p c brs brs' :
    OnOne2 (fun br br' =>
      on_Trel_eq (fun t u => Σ ;;; Γ ,,, inst_case_branch_context p br |- t ⇝ u) bbody bcontext br br')
      brs brs' ->
    Σ ;;; Γ |- tCase ci p c brs ⇝ tCase ci p c brs'

| proj_red p c c' : Σ ;;; Γ |- c ⇝ c' -> Σ ;;; Γ |- tProj p c ⇝ tProj p c'

| app_red_l M1 N1 M2 : Σ ;;; Γ |- M1 ⇝ N1 -> Σ ;;; Γ |- tApp M1 M2 ⇝ tApp N1 M2
| app_red_r M2 N2 M1 : Σ ;;; Γ |- M2 ⇝ N2 -> Σ ;;; Γ |- tApp M1 M2 ⇝ tApp M1 N2

| prod_red_l na M1 M2 N1 : Σ ;;; Γ |- M1 ⇝ N1 -> Σ ;;; Γ |- tProd na M1 M2 ⇝ tProd na N1 M2
| prod_red_r na M2 N2 M1 : Σ ;;; Γ ,, vass na M1 |- M2 ⇝ N2 ->
                           Σ ;;; Γ |- tProd na M1 M2 ⇝ tProd na M1 N2

| evar_red ev l l' : OnOne2 (fun t u => Σ ;;; Γ |- t ⇝ u) l l' -> Σ ;;; Γ |- tEvar ev l ⇝ tEvar ev l'

| fix_red_ty mfix0 mfix1 idx :
    OnOne2 (on_Trel_eq (fun t u => Σ ;;; Γ |- t ⇝ u) dtype (fun x => (dname x, dbody x, rarg x))) mfix0 mfix1 ->
    Σ ;;; Γ |- tFix mfix0 idx ⇝ tFix mfix1 idx

| fix_red_body mfix0 mfix1 idx :
    OnOne2 (on_Trel_eq (fun t u => Σ ;;; Γ ,,, fix_context mfix0 |- t ⇝ u) dbody (fun x => (dname x, dtype x, rarg x)))
           mfix0 mfix1 ->
    Σ ;;; Γ |- tFix mfix0 idx ⇝ tFix mfix1 idx

| cofix_red_ty mfix0 mfix1 idx :
    OnOne2 (on_Trel_eq (fun t u => Σ ;;; Γ |- t ⇝ u) dtype (fun x => (dname x, dbody x, rarg x))) mfix0 mfix1 ->
    Σ ;;; Γ |- tCoFix mfix0 idx ⇝ tCoFix mfix1 idx

| cofix_red_body mfix0 mfix1 idx :
    OnOne2 (on_Trel_eq (fun t u => Σ ;;; Γ ,,, fix_context mfix0 |- t ⇝ u) dbody (fun x => (dname x, dtype x, rarg x))) mfix0 mfix1 ->
    Σ ;;; Γ |- tCoFix mfix0 idx ⇝ tCoFix mfix1 idx
where " Σ ;;; Γ |- t ⇝ u " := (red1 Σ Γ t u).

Lemma red1_ind_all :
  forall (Σ : global_env) (P : context -> term -> term -> Type),

       (forall (Γ : context) (na : aname) (t b a : term),
        P Γ (tApp (tLambda na t b) a) (b {0 := a})) ->

       (forall (Γ : context) (na : aname) (b t b' : term), P Γ (tLetIn na b t b') (b' {0 := b})) ->

       (forall (Γ : context) (i : nat) (body : term),
        option_map decl_body (nth_error Γ i) = Some (Some body) -> P Γ (tRel i) ((lift0 (S i)) body)) ->

       (forall (Γ : context) (ci : case_info) (c : nat) (u : Instance.t) (args : list term)
          (p : predicate term) (brs : list (branch term)) br,
          nth_error brs c = Some br ->
          #|args| = (ci.(ci_npar) + context_assumptions br.(bcontext))%nat ->
          P Γ (tCase ci p (mkApps (tConstruct ci.(ci_ind) c u) args) brs)
              (iota_red ci.(ci_npar) p args br)) ->

       (forall (Γ : context) (mfix : mfixpoint term) (idx : nat) (args : list term) (narg : nat) (fn : term),
        unfold_fix mfix idx = Some (narg, fn) ->
        is_constructor narg args = true -> P Γ (mkApps (tFix mfix idx) args) (mkApps fn args)) ->

       (forall (Γ : context) ci (p : predicate term) (mfix : mfixpoint term) (idx : nat)
          (args : list term) (narg : nat) (fn : term) (brs : list (branch term)),
        unfold_cofix mfix idx = Some (narg, fn) ->
        P Γ (tCase ci p (mkApps (tCoFix mfix idx) args) brs) (tCase ci p (mkApps fn args) brs)) ->

       (forall (Γ : context) (p : projection) (mfix : mfixpoint term) (idx : nat) (args : list term)
          (narg : nat) (fn : term),
        unfold_cofix mfix idx = Some (narg, fn) -> P Γ (tProj p (mkApps (tCoFix mfix idx) args)) (tProj p (mkApps fn args))) ->

       (forall (Γ : context) c (decl : constant_body) (body : term),
        declared_constant Σ c decl ->
        forall u : Instance.t, cst_body decl = Some body -> P Γ (tConst c u) (subst_instance u body)) ->

       (forall (Γ : context) p (args : list term) (u : Instance.t)
         (arg : term),
           nth_error args (p.(proj_npars) + p.(proj_arg)) = Some arg ->
           P Γ (tProj p (mkApps (tConstruct p.(proj_ind) 0 u) args)) arg) ->

       (forall (Γ : context) (na : aname) (M M' N : term),
        red1 Σ Γ M M' -> P Γ M M' -> P Γ (tLambda na M N) (tLambda na M' N)) ->

       (forall (Γ : context) (na : aname) (M M' N : term),
        red1 Σ (Γ,, vass na N) M M' -> P (Γ,, vass na N) M M' -> P Γ (tLambda na N M) (tLambda na N M')) ->

       (forall (Γ : context) (na : aname) (b t b' r : term),
        red1 Σ Γ b r -> P Γ b r -> P Γ (tLetIn na b t b') (tLetIn na r t b')) ->

       (forall (Γ : context) (na : aname) (b t b' r : term),
        red1 Σ Γ t r -> P Γ t r -> P Γ (tLetIn na b t b') (tLetIn na b r b')) ->

       (forall (Γ : context) (na : aname) (b t b' r : term),
        red1 Σ (Γ,, vdef na b t) b' r -> P (Γ,, vdef na b t) b' r -> P Γ (tLetIn na b t b') (tLetIn na b t r)) ->

       (forall (Γ : context) (ci : case_info) p params' c brs,
          OnOne2 (Trel_conj (red1 Σ Γ) (P Γ)) p.(pparams) params' ->
           P Γ (tCase ci p c brs)
               (tCase ci (set_pparams p params') c brs)) ->

       (forall (Γ : context) (ci : case_info) p preturn' c brs,
          red1 Σ (Γ ,,, inst_case_predicate_context p) p.(preturn) preturn' ->
          P (Γ ,,, inst_case_predicate_context p) p.(preturn) preturn' ->
          P Γ (tCase ci p c brs)
              (tCase ci (set_preturn p preturn') c brs)) ->

       (forall (Γ : context) (ind : case_info) (p : predicate term) (c c' : term) (brs : list (branch term)),
        red1 Σ Γ c c' -> P Γ c c' -> P Γ (tCase ind p c brs) (tCase ind p c' brs)) ->

       (forall (Γ : context) ci p c brs brs',
          OnOne2 (fun br br' =>
          (on_Trel_eq (Trel_conj (red1 Σ (Γ ,,, inst_case_branch_context p br))
            (P (Γ ,,, inst_case_branch_context p br)))
            bbody bcontext br br')) brs brs' ->
          P Γ (tCase ci p c brs) (tCase ci p c brs')) ->

       (forall (Γ : context) (p : projection) (c c' : term), red1 Σ Γ c c' -> P Γ c c' ->
                                                             P Γ (tProj p c) (tProj p c')) ->

       (forall (Γ : context) (M1 N1 : term) (M2 : term), red1 Σ Γ M1 N1 -> P Γ M1 N1 ->
                                                         P Γ (tApp M1 M2) (tApp N1 M2)) ->

       (forall (Γ : context) (M2 N2 : term) (M1 : term), red1 Σ Γ M2 N2 -> P Γ M2 N2 ->
                                                         P Γ (tApp M1 M2) (tApp M1 N2)) ->

       (forall (Γ : context) (na : aname) (M1 M2 N1 : term),
        red1 Σ Γ M1 N1 -> P Γ M1 N1 -> P Γ (tProd na M1 M2) (tProd na N1 M2)) ->

       (forall (Γ : context) (na : aname) (M2 N2 M1 : term),
        red1 Σ (Γ,, vass na M1) M2 N2 -> P (Γ,, vass na M1) M2 N2 -> P Γ (tProd na M1 M2) (tProd na M1 N2)) ->

       (forall (Γ : context) (ev : nat) (l l' : list term),
           OnOne2 (Trel_conj (red1 Σ Γ) (P Γ)) l l' -> P Γ (tEvar ev l) (tEvar ev l')) ->

       (forall (Γ : context) (mfix0 mfix1 : list (def term)) (idx : nat),
        OnOne2 (on_Trel_eq (Trel_conj (red1 Σ Γ) (P Γ)) dtype (fun x => (dname x, dbody x, rarg x))) mfix0 mfix1 ->
        P Γ (tFix mfix0 idx) (tFix mfix1 idx)) ->

       (forall (Γ : context) (mfix0 mfix1 : list (def term)) (idx : nat),
        OnOne2 (on_Trel_eq (Trel_conj (red1 Σ (Γ ,,, fix_context mfix0))
                                      (P (Γ ,,, fix_context mfix0))) dbody
                           (fun x => (dname x, dtype x, rarg x))) mfix0 mfix1 ->
        P Γ (tFix mfix0 idx) (tFix mfix1 idx)) ->

       (forall (Γ : context) (mfix0 mfix1 : list (def term)) (idx : nat),
        OnOne2 (on_Trel_eq (Trel_conj (red1 Σ Γ) (P Γ)) dtype (fun x => (dname x, dbody x, rarg x))) mfix0 mfix1 ->
        P Γ (tCoFix mfix0 idx) (tCoFix mfix1 idx)) ->

       (forall (Γ : context) (mfix0 mfix1 : list (def term)) (idx : nat),
        OnOne2 (on_Trel_eq (Trel_conj (red1 Σ (Γ ,,, fix_context mfix0))
                                      (P (Γ ,,, fix_context mfix0))) dbody
                           (fun x => (dname x, dtype x, rarg x))) mfix0 mfix1 ->
        P Γ (tCoFix mfix0 idx) (tCoFix mfix1 idx)) ->

       forall (Γ : context) (t t0 : term), red1 Σ Γ t t0 -> P Γ t t0.
Admitted.
Import Coq.ssr.ssreflect.

Set Default Goal Selector "!".
Global Instance subst_instance_def {A} `(UnivSubst A) : UnivSubst (def A).
exact (fun u => map_def (subst_instance u) (subst_instance u)).
Defined.
Global Instance subst_instance_predicate : UnivSubst (predicate term).
exact (fun u => map_predicate (subst_instance u) (subst_instance u) (subst_instance u) id).
Defined.

Lemma fix_subst_instance_subst u mfix :
  subst_instance u (fix_subst mfix) = fix_subst (subst_instance u mfix).
Admitted.

Lemma iota_red_subst_instance pars p args br u :
  subst_instance u (iota_red pars p args br)
  = iota_red pars (subst_instance u p) (List.map (subst_instance u) args) (map_branch (subst_instance u) id br).
Admitted.

Lemma red1_subst_instance Σ Γ u s t :
  red1 Σ Γ s t ->
  red1 Σ (subst_instance u Γ)
       (subst_instance u s) (subst_instance u t).
Proof.
  intros X0.
pose proof I as X.
  intros.
induction X0 using red1_ind_all.
  all: try (cbn; econstructor; eauto; fail).
  -
 cbn.
rewrite subst_instance_subst.
econstructor.
  -
 cbn.
rewrite subst_instance_subst.
econstructor.
  -
 cbn.
rewrite subst_instance_lift.
econstructor.
    unfold subst_instance.
    unfold option_map in *.
destruct (nth_error Γ) eqn:E; inversion H.
    unfold map_context.
rewrite nth_error_map E.
cbn.
    rewrite map_decl_body.
destruct c.
cbn in H1.
subst.
    reflexivity.
  -
 cbn.
rewrite subst_instance_mkApps.
cbn.
    rewrite iota_red_subst_instance.
    change (bcontext br) with (bcotext (map_branch (subst_instance u) br)).
    eapply red_iota; eauto with pcuic.
    *
 rewrite nth_error_map H //.
    *
 simpl.
now len.
  -
 cbn.
rewrite !subst_instance_mkApps.
cbn.
    econstructor.
    +
 unfold unfold_fix in *.
destruct (nth_error mfix idx) eqn:E.
      *
 inversion H.
        rewrite nth_error_map E.
cbn.
        destruct d.
cbn in *.
cbn in *; try congruence.
        f_equal.
f_equal.
        now rewrite subst_instance_subst fix_subst_instance_subst.
