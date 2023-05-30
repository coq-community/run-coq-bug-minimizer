
(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "-deprecated-native-compiler-option" "-native-compiler" "no" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/metacoq/utils/theories" "MetaCoq.Utils" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/metacoq/common/theories" "MetaCoq.Common" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/metacoq/template-coq/theories" "MetaCoq.Template" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Equations" "Equations" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-I" "/github/workspace/builds/coq/coq-failing/_build_ci/metacoq/template-coq/src" "-I" "/github/workspace/builds/coq/coq-failing/_build_ci/metacoq/template-coq" "-top" "MetaCoq.Template.Typing") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 1722 lines to 454 lines, then from 467 lines to 1149 lines, then from 1151 lines to 610 lines, then from 623 lines to 1192 lines, then from 1194 lines to 615 lines, then from 628 lines to 1072 lines, then from 1075 lines to 616 lines, then from 629 lines to 1222 lines, then from 1227 lines to 634 lines, then from 647 lines to 1604 lines, then from 1606 lines to 952 lines, then from 965 lines to 2997 lines, then from 2998 lines to 1304 lines *)
(* coqc version 8.18+alpha compiled with OCaml 4.09.0
   coqtop version runner-htnstaz1-project-6138686-concurrent-0:/builds/coq/coq/_build/default,(HEAD detached at ac1cbb0) (ac1cbb0ae7ecd8379f3cfb4be86059206288e497)
   Expected coqc runtime on this file: 3.683 sec *)
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

  Definition lookup_minductive_gen (lookup : kername -> option global_decl) mind :=
    match lookup mind with
    | Some (InductiveDecl decl) => Some decl
    | _ => None
    end.

  Definition lookup_inductive_gen lookup ind :=
    match lookup_minductive_gen lookup (inductive_mind ind) with
    | Some mdecl =>
      match nth_error mdecl.(ind_bodies) (inductive_ind ind) with
      | Some idecl => Some (mdecl, idecl)
      | None => None
      end
    | None => None
    end.

  Definition lookup_constructor_gen lookup ind k :=
    match lookup_inductive_gen lookup ind with
    | Some (mdecl, idecl) =>
      match nth_error idecl.(ind_ctors) k with
      | Some cdecl => Some (mdecl, idecl, cdecl)
      | None => None
      end
    | _ => None
    end.
Definition global_levels (univs : ContextSet.t) : LevelSet.t. exact (LevelSet.union (ContextSet.levels univs) (LevelSet.singleton (Level.lzero))). Defined.
Definition global_constraints (Σ : global_env) : ConstraintSet.t. exact (snd Σ.(universes)). Defined.
Definition global_ext_levels (Σ : global_env_ext) : LevelSet.t. exact (LevelSet.union (levels_of_udecl (snd Σ)) (global_levels Σ.1.(universes))). Defined.
Definition global_ext_constraints (Σ : global_env_ext) : ConstraintSet.t. exact (ConstraintSet.union
      (constraints_of_udecl (snd Σ))
      (global_constraints Σ.1)). Defined.

  Coercion global_ext_constraints : global_env_ext >-> ConstraintSet.t.

   

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

  Definition wf_universe Σ s : Prop :=
    Universe.on_sort
      (fun u => forall l, LevelExprSet.In l u -> LevelSet.In (LevelExpr.get_level l) (global_ext_levels Σ))
      True s.

End Lookup.

Module Type LookupSig (T : Term) (E : EnvironmentSig T).
End LookupSig.

Module EnvTyping (T : Term) (E : EnvironmentSig T) (TU : TermUtils T E).
Import T.
Import E.

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
  End TypeLocal.

  Section All_local_env_rel.

  End All_local_env_rel.
Definition lift_judgment
    (check : global_env_ext -> context -> term -> term -> Type)
    (infer_sort : global_env_ext -> context -> term -> Type) :
    (global_env_ext -> context -> term -> typ_or_sort -> Type). exact (fun Σ Γ t T =>
    match T with
    | Typ T => check Σ Γ t T
    | Sort => infer_sort Σ Γ t
    end). Defined.

  Definition infer_sort (sorting : global_env_ext -> context -> term -> Universe.t -> Type) := (fun Σ Γ T => { s : Universe.t & sorting Σ Γ T s }).
  Notation typing_sort typing := (fun Σ Γ T s => typing Σ Γ T (tSort s)).

  Definition lift_typing typing := lift_judgment typing (infer_sort (typing_sort typing)).

  Section TypeLocalOver.

  End TypeLocalOver.

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
  End TypeCtxInst.

  Section All_local_env_size.
  End All_local_env_size.

  Section lift_judgment_size.
  End lift_judgment_size.

  Section Regular.
  End Regular.

  Section Bidirectional.
  End Bidirectional.

End EnvTyping.

Module Type EnvTypingSig (T : Term) (E : EnvironmentSig T) (TU : TermUtils T E).
End EnvTypingSig.

Module Conversion (T : Term) (E : EnvironmentSig T) (TU : TermUtils T E) (ET : EnvTypingSig T E TU).

  Section Conversion.
  End Conversion.
  Notation cumul cumul_gen Σ Γ := (cumul_gen Σ Γ Cumul).
End Conversion.

Module Type ConversionSig (T : Term) (E : EnvironmentSig T) (TU : TermUtils T E) (ET : EnvTypingSig T E TU).
End ConversionSig.

Module GlobalMaps (T: Term) (E: EnvironmentSig T) (TU : TermUtils T E) (ET: EnvTypingSig T E TU) (C: ConversionSig T E TU ET) (L: LookupSig T E).

  Section GlobalMaps.

  End GlobalMaps.

End GlobalMaps.

Module Type GlobalMapsSig (T: Term) (E: EnvironmentSig T) (TU : TermUtils T E) (ET: EnvTypingSig T E TU) (C: ConversionSig T E TU ET) (L: LookupSig T E).
End GlobalMapsSig.

Module Type ConversionParSig (T : Term) (E : EnvironmentSig T) (TU : TermUtils T E) (ET : EnvTypingSig T E TU).

End ConversionParSig.

Module Type Typing (T : Term) (E : EnvironmentSig T) (TU : TermUtils T E) (ET : EnvTypingSig T E TU)
  (CT : ConversionSig T E TU ET) (CS : ConversionParSig T E TU ET).

End Typing.

  Section Properties.
  End Properties.

Import MetaCoq.Utils.utils.
Export MetaCoq.Common.Environment.
Export MetaCoq.Common.Universes.
Export MetaCoq.Common.BasicAst.

Record predicate {term} := mk_predicate {
  puinst : Instance.t;
  pparams : list term;
  pcontext : list aname;
  preturn : term;   }.

Arguments predicate : clear implicits.
Arguments mk_predicate {_}.

Definition test_predicate {term}
            (instf : Instance.t -> bool) (paramf preturnf : term -> bool) (p : predicate term) :=
  instf p.(puinst) && forallb paramf p.(pparams) && preturnf p.(preturn).

Section map_predicate.
  Context {term term' : Type}.
  Context (uf : Instance.t -> Instance.t).
  Context (paramf preturnf : term -> term').

  Definition map_predicate (p : predicate term) :=
    {| pparams := map paramf p.(pparams);
        puinst := uf p.(puinst);
        pcontext := p.(pcontext);
        preturn := preturnf p.(preturn) |}.

End map_predicate.

Section Branch.
  Context {term : Type}.

  Record branch := mk_branch {
    bcontext : list aname;
    bbody : term;   }.

  Definition test_branch (bodyf : term -> bool) (b : branch) :=
    bodyf b.(bbody).
End Branch.
Arguments branch : clear implicits.

Section map_branch.
  Context {term term' : Type}.
  Context (bbodyf : term -> term').

    Definition map_branch (b : branch term) :=
    {| bcontext := b.(bcontext);
      bbody := bbodyf b.(bbody) |}.
End map_branch.

Notation map_branches_k f k brs :=
  (List.map (fun b => map_branch (f (#|b.(bcontext)| + k)) b) brs).

Notation test_branches_k test k brs :=
  (List.forallb (fun b => test_branch (test (#|b.(bcontext)| + k)) b) brs).

Inductive term : Type :=
| tRel (n : nat)
| tVar (id : ident)
| tEvar (ev : nat) (args : list term)
| tSort (s : Universe.t)
| tCast (t : term) (kind : cast_kind) (v : term)
| tProd (na : aname) (ty : term) (body : term)
| tLambda (na : aname) (ty : term) (body : term)
| tLetIn (na : aname) (def : term) (def_ty : term) (body : term)
| tApp (f : term) (args : list term)
| tConst (c : kername) (u : Instance.t)
| tInd (ind : inductive) (u : Instance.t)
| tConstruct (ind : inductive) (idx : nat) (u : Instance.t)
| tCase (ci : case_info) (type_info:predicate term)
        (discr:term) (branches : list (branch term))
| tProj (proj : projection) (t : term)
| tFix (mfix : mfixpoint term) (idx : nat)
| tCoFix (mfix : mfixpoint term) (idx : nat)
| tInt (i : PrimInt63.int)
| tFloat (f : PrimFloat.float).

Definition mkApps t us :=
  match us with
  | nil => t
  | _ => match t with
        | tApp f args => tApp f (args ++ us)
        | _ => tApp t us
        end
  end.

Fixpoint lift n k t : term :=
  match t with
  | tRel i => tRel (if Nat.leb k i then n + i else i)
  | tEvar ev args => tEvar ev (List.map (lift n k) args)
  | tLambda na T M => tLambda na (lift n k T) (lift n (S k) M)
  | tApp u v => tApp (lift n k u) (List.map (lift n k) v)
  | tProd na A B => tProd na (lift n k A) (lift n (S k) B)
  | tCast c kind t => tCast (lift n k c) kind (lift n k t)
  | tLetIn na b t b' => tLetIn na (lift n k b) (lift n k t) (lift n (S k) b')
  | tCase ind p c brs =>
    let k' := List.length (pcontext p) + k in
    let p' := map_predicate id (lift n k) (lift n k') p in
    let brs' := map_branches_k (lift n) k brs in
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
  | tApp u v => mkApps (subst s k u) (List.map (subst s k) v)
  | tProd na A B => tProd na (subst s k A) (subst s (S k) B)
  | tCast c kind ty => tCast (subst s k c) kind (subst s k ty)
  | tLetIn na b ty b' => tLetIn na (subst s k b) (subst s k ty) (subst s (S k) b')
  | tCase ind p c brs =>
    let k' := List.length (pcontext p) + k in
    let p' := map_predicate id (subst s k) (subst s k') p in
    let brs' := map_branches_k (subst s) k brs in
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
Notation subst10 t := (subst1 t 0).

Fixpoint closedn k (t : term) : bool :=
  match t with
  | tRel i => Nat.ltb i k
  | tEvar ev args => List.forallb (closedn k) args
  | tLambda _ T M | tProd _ T M => closedn k T && closedn (S k) M
  | tApp u v => closedn k u && List.forallb (closedn k) v
  | tCast c kind t => closedn k c && closedn k t
  | tLetIn na b t b' => closedn k b && closedn k t && closedn (S k) b'
  | tCase ind p c brs =>
    let k' := List.length (pcontext p) + k in
    let p' := test_predicate (fun _ => true) (closedn k) (closedn k') p in
    let brs' := test_branches_k closedn k brs in
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
  | tRel i => Nat.ltb i k && Nat.leb (k + n) i
  | tEvar ev args => List.forallb (noccur_between k n) args
  | tLambda _ T M | tProd _ T M => noccur_between k n T && noccur_between (S k) n M
  | tApp u v => noccur_between k n u && List.forallb (noccur_between k n) v
  | tCast c kind t => noccur_between k n c && noccur_between k n t
  | tLetIn na b t b' => noccur_between k n b && noccur_between k n t && noccur_between (S k) n b'
  | tCase ind p c brs =>
    let k' := List.length (pcontext p) + k in
    let p' := test_predicate (fun _ => true) (noccur_between k n) (noccur_between k' n) p in
    let brs' := test_branches_k (fun k => noccur_between k n) k brs in
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
#[global] Instance subst_instance_constr : UnivSubst term.
Admitted.

Module TemplateTerm <: Term.

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

End TemplateTerm.

Module Env := Environment TemplateTerm.
Export Env.

Fixpoint destArity Γ (t : term) :=
  match t with
  | tProd na t b => destArity (Γ ,, vass na t) b
  | tLetIn na b b_ty b' => destArity (Γ ,, vdef na b b_ty) b'
  | tSort s => Some (Γ, s)
  | _ => None
  end.

Definition inds ind u (l : list one_inductive_body) :=
  let fix aux n :=
      match n with
      | 0 => []
      | S n => tInd (mkInd ind n) u :: aux n
      end
  in aux (List.length l).

Module TemplateTermUtils <: TermUtils TemplateTerm Env.

Definition destArity := destArity.
Definition inds := inds.

End TemplateTermUtils.

Module TemplateLookup := EnvironmentTyping.Lookup TemplateTerm Env.
Include TemplateLookup.

Definition isApp t :=
  match t with
  | tApp _ _ => true
  | _ => false
  end.

Definition isLambda t :=
  match t with
  | tLambda _ _ _ => true
  | _ => false
  end.

Definition ind_predicate_context ind mdecl idecl : context :=
  let ictx := (expand_lets_ctx mdecl.(ind_params) idecl.(ind_indices)) in
  let indty := mkApps (tInd ind (abstract_instance mdecl.(ind_universes)))
    (to_extended_list (smash_context [] mdecl.(ind_params) ,,, ictx)) in
  let inddecl :=
    {| decl_name :=
      {| binder_name := nNamed (ind_name idecl); binder_relevance := idecl.(ind_relevance) |};
        decl_body := None;
        decl_type := indty |}
  in (inddecl :: ictx).

Definition inst_case_context params puinst (pctx : context) :=
  subst_context (List.rev params) 0 (subst_instance puinst pctx).

Definition pre_case_predicate_context_gen ind mdecl idecl params puinst : context :=
  inst_case_context params puinst (ind_predicate_context ind mdecl idecl).

Definition case_predicate_context_gen ind mdecl idecl params puinst pctx :=
  map2 set_binder_name pctx (pre_case_predicate_context_gen ind mdecl idecl params puinst).

Definition case_predicate_context ind mdecl idecl p : context :=
  case_predicate_context_gen ind mdecl idecl p.(pparams) p.(puinst) p.(pcontext).

Definition cstr_branch_context ind mdecl cdecl : context :=
  expand_lets_ctx mdecl.(ind_params)
    (subst_context (inds (inductive_mind ind) (abstract_instance mdecl.(ind_universes))
        mdecl.(ind_bodies)) #|mdecl.(ind_params)|
      cdecl.(cstr_args)).

Definition case_branch_context_gen ind mdecl params puinst bctx cdecl : context :=
  map2 set_binder_name bctx
    (inst_case_context params puinst (cstr_branch_context ind mdecl cdecl)).

Definition case_branch_context ind mdecl cdecl p (br : branch term) : context :=
  case_branch_context_gen ind mdecl p.(pparams) p.(puinst) br.(bcontext) cdecl.

Definition case_branches_contexts ind mdecl idecl p (brs : list (branch term)) : list context :=
  map2 (fun br => case_branch_context_gen ind mdecl p.(pparams) p.(puinst) br.(bcontext)) brs idecl.(ind_ctors).

Definition case_branch_type_gen ind mdecl params puinst ptm i cdecl (br : branch term) : context * term :=
  let cstr := tConstruct ind i puinst in
  let args := to_extended_list cdecl.(cstr_args) in
  let cstrapp := mkApps cstr (map (lift0 #|cdecl.(cstr_args)|) params ++ args) in
  let brctx := case_branch_context_gen ind mdecl params puinst br.(bcontext) cdecl in
  let upars := subst_instance puinst mdecl.(ind_params) in
  let indices :=
    (map (subst (List.rev params) #|cdecl.(cstr_args)|)
      (map (expand_lets_k upars #|cdecl.(cstr_args)|)
        (map (subst (inds (inductive_mind ind) puinst mdecl.(ind_bodies))
                    (#|mdecl.(ind_params)| + #|cdecl.(cstr_args)|))
          (map (subst_instance puinst) cdecl.(cstr_indices))))) in
  let ty := mkApps (lift0 #|cdecl.(cstr_args)| ptm) (indices ++ [cstrapp]) in
  (brctx, ty).

Definition case_branch_type ind mdecl p ptm i cdecl br : context * term :=
  case_branch_type_gen ind mdecl p.(pparams) p.(puinst) ptm i cdecl br.

Definition decompose_app (t : term) :=
  match t with
  | tApp f l => (f, l)
  | _ => (t, [])
  end.
Fixpoint decompose_prod_assum (Γ : context) (t : term) : context * term.
Admitted.

Definition isConstruct_app t :=
  match fst (decompose_app t) with
  | tConstruct _ _ _ => true
  | _ => false
  end.

Definition destInd (t : term) :=
  match t with
  | tInd ind u => Some (ind, u)
  | _ => None
  end.

Notation wf_nactx :=
  (All2 (fun x y => eq_binder_annot x (decl_name y))).
Definition eq_cast_kind (c c' : cast_kind) : bool.
Admitted.

#[global] Instance reflect_recursivity_kind : ReflectEq recursivity_kind.
Admitted.
Import MetaCoq.Common.config.

Definition R_universe_instance R :=
  fun u u' => Forall2 R (List.map Universe.make u) (List.map Universe.make u').

Definition R_universe_variance (Re Rle : Universe.t -> Universe.t -> Prop) v u u' :=
  match v with
  | Variance.Irrelevant => True
  | Variance.Covariant => Rle (Universe.make u) (Universe.make u')
  | Variance.Invariant => Re (Universe.make u) (Universe.make u')
  end.

Fixpoint R_universe_instance_variance Re Rle v u u' :=
  match u, u' return Prop with
  | u :: us, u' :: us' =>
    match v with
    | [] => R_universe_instance_variance Re Rle v us us'

    | v :: vs => R_universe_variance Re Rle v u u' /\
        R_universe_instance_variance Re Rle vs us us'
    end
  | [], [] => True
  | _, _ => False
  end.

Definition global_variance_gen lookup gr napp :=
  match gr with
  | IndRef ind =>
    match lookup_inductive_gen lookup ind with
    | Some (mdecl, idecl) =>
      match destArity [] idecl.(ind_type) with
      | Some (ctx, _) => if (context_assumptions ctx) <=? napp then mdecl.(ind_variance)
        else None
      | None => None
      end
    | None => None
    end
  | ConstructRef ind k =>
    match lookup_constructor_gen lookup ind k with
    | Some (mdecl, idecl, cdecl) =>
      if (cdecl.(cstr_arity) + mdecl.(ind_npars))%nat <=? napp then

        Some []
      else None
    | _ => None
    end
  | _ => None
  end.

Definition R_opt_variance Re Rle v :=
  match v with
  | Some v => R_universe_instance_variance Re Rle v
  | None => R_universe_instance Re
  end.

Definition R_global_instance_gen Σ Re Rle gr napp :=
  R_opt_variance Re Rle (global_variance_gen Σ gr napp).

Notation R_global_instance Σ := (R_global_instance_gen (lookup_env Σ)).

Inductive eq_term_upto_univ_napp Σ (Re Rle : Universe.t -> Universe.t -> Prop) (napp : nat) : term -> term -> Type :=
| eq_Rel n  :
    eq_term_upto_univ_napp Σ Re Rle napp (tRel n) (tRel n)

| eq_Evar e args args' :
    All2 (eq_term_upto_univ_napp Σ Re Re 0) args args' ->
    eq_term_upto_univ_napp Σ Re Rle napp (tEvar e args) (tEvar e args')

| eq_Var id :
    eq_term_upto_univ_napp Σ Re Rle napp (tVar id) (tVar id)

| eq_Sort s s' :
    Rle s s' ->
    eq_term_upto_univ_napp Σ Re Rle napp (tSort s) (tSort s')

| eq_App t t' u u' :
    eq_term_upto_univ_napp Σ Re Rle (#|u| + napp) t t' ->
    All2 (eq_term_upto_univ_napp Σ Re Re 0) u u' ->
    eq_term_upto_univ_napp Σ Re Rle napp (tApp t u) (tApp t' u')

| eq_Const c u u' :
    R_universe_instance Re u u' ->
    eq_term_upto_univ_napp Σ Re Rle napp (tConst c u) (tConst c u')

| eq_Ind i u u' :
    R_global_instance Σ Re Rle (IndRef i) napp u u' ->
    eq_term_upto_univ_napp Σ Re Rle napp (tInd i u) (tInd i u')

| eq_Construct i k u u' :
    R_global_instance Σ Re Rle (ConstructRef i k) napp u u' ->
    eq_term_upto_univ_napp Σ Re Rle napp (tConstruct i k u) (tConstruct i k u')

| eq_Lambda na na' ty ty' t t' :
    eq_binder_annot na na' ->
    eq_term_upto_univ_napp Σ Re Re 0 ty ty' ->
    eq_term_upto_univ_napp Σ Re Rle 0 t t' ->
    eq_term_upto_univ_napp Σ Re Rle napp (tLambda na ty t) (tLambda na' ty' t')

| eq_Prod na na' a a' b b' :
    eq_binder_annot na na' ->
    eq_term_upto_univ_napp Σ Re Re 0 a a' ->
    eq_term_upto_univ_napp Σ Re Rle 0 b b' ->
    eq_term_upto_univ_napp Σ Re Rle napp (tProd na a b) (tProd na' a' b')

| eq_LetIn na na' t t' ty ty' u u' :
    eq_binder_annot na na' ->
    eq_term_upto_univ_napp Σ Re Re 0 t t' ->
    eq_term_upto_univ_napp Σ Re Re 0 ty ty' ->
    eq_term_upto_univ_napp Σ Re Rle 0 u u' ->
    eq_term_upto_univ_napp Σ Re Rle napp (tLetIn na t ty u) (tLetIn na' t' ty' u')

| eq_Case ind p p' c c' brs brs' :
    All2 (eq_term_upto_univ_napp Σ Re Re 0) p.(pparams) p'.(pparams) ->
    R_universe_instance Re p.(puinst) p'.(puinst) ->
    eq_term_upto_univ_napp Σ Re Re 0 p.(preturn) p'.(preturn) ->
    All2 eq_binder_annot p.(pcontext) p'.(pcontext) ->
    eq_term_upto_univ_napp Σ Re Re 0 c c' ->
    All2 (fun x y =>
      All2 (eq_binder_annot) (bcontext x) (bcontext y) *
      eq_term_upto_univ_napp Σ Re Re 0 (bbody x) (bbody y)
    ) brs brs' ->
  eq_term_upto_univ_napp Σ Re Rle napp (tCase ind p c brs) (tCase ind p' c' brs')

| eq_Proj p c c' :
    eq_term_upto_univ_napp Σ Re Re 0 c c' ->
    eq_term_upto_univ_napp Σ Re Rle napp (tProj p c) (tProj p c')

| eq_Fix mfix mfix' idx :
    All2 (fun x y =>
      eq_term_upto_univ_napp Σ Re Re 0 x.(dtype) y.(dtype) *
      eq_term_upto_univ_napp Σ Re Re 0 x.(dbody) y.(dbody) *
      (x.(rarg) = y.(rarg)) *
      eq_binder_annot x.(dname) y.(dname)
    )%type mfix mfix' ->
    eq_term_upto_univ_napp Σ Re Rle napp (tFix mfix idx) (tFix mfix' idx)

| eq_CoFix mfix mfix' idx :
    All2 (fun x y =>
      eq_term_upto_univ_napp Σ Re Re 0 x.(dtype) y.(dtype) *
      eq_term_upto_univ_napp Σ Re Re 0 x.(dbody) y.(dbody) *
      (x.(rarg) = y.(rarg)) *
      eq_binder_annot x.(dname) y.(dname)
    ) mfix mfix' ->
    eq_term_upto_univ_napp Σ Re Rle napp (tCoFix mfix idx) (tCoFix mfix' idx)

| eq_Cast t1 c t2 t1' c' t2' :
  eq_term_upto_univ_napp Σ Re Re 0 t1 t1' ->
  eq_cast_kind c c' ->
  eq_term_upto_univ_napp Σ Re Re 0 t2 t2' ->
  eq_term_upto_univ_napp Σ Re Rle napp (tCast t1 c t2) (tCast t1' c' t2')

| eq_Int i : eq_term_upto_univ_napp Σ Re Rle napp (tInt i) (tInt i)
| eq_Float f : eq_term_upto_univ_napp Σ Re Rle napp (tFloat f) (tFloat f).

Notation eq_term_upto_univ Σ Re Rle := (eq_term_upto_univ_napp Σ Re Rle 0).

Definition compare_term `{checker_flags} (pb : conv_pb) Σ φ :=
  eq_term_upto_univ Σ (eq_universe φ) (compare_universe pb φ).
Import MetaCoq.Common.Primitive.

Definition type_of_constructor mdecl cdecl (c : inductive * nat) (u : list Level.t) :=
  let mind := inductive_mind (fst c) in
  subst0 (inds mind u mdecl.(ind_bodies)) (subst_instance u cdecl.(cstr_type)).

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

Definition iota_red npar args bctx br :=
  subst (List.rev (List.skipn npar args)) 0 (expand_lets bctx br.(bbody)).

Inductive red1 (Σ : global_env) (Γ : context) : term -> term -> Type :=

| red_beta na t b a l :
    red1 Σ Γ (tApp (tLambda na t b) (a :: l)) (mkApps (subst10 a b) l)

| red_zeta na b t b' :
    red1 Σ Γ (tLetIn na b t b') (subst10 b b')

| red_rel i body :
    option_map decl_body (nth_error Γ i) = Some (Some body) ->
    red1 Σ Γ (tRel i) (lift0 (S i) body)

| red_iota ci mdecl idecl cdecl c u args p brs br :
    nth_error brs c = Some br ->

    declared_constructor Σ (ci.(ci_ind), c) mdecl idecl cdecl ->
    let bctx := case_branch_context ci.(ci_ind) mdecl cdecl p br in
    #|args| = (ci.(ci_npar) + context_assumptions bctx)%nat ->
    red1 Σ Γ (tCase ci p (mkApps (tConstruct ci.(ci_ind) c u) args) brs)
         (iota_red ci.(ci_npar) args bctx br)

| red_fix mfix idx args narg fn :
    unfold_fix mfix idx = Some (narg, fn) ->
    is_constructor narg args = true ->
    red1 Σ Γ (tApp (tFix mfix idx) args) (mkApps fn args)

| red_cofix_case ip p mfix idx args narg fn brs :
    unfold_cofix mfix idx = Some (narg, fn) ->
    red1 Σ Γ (tCase ip p (mkApps (tCoFix mfix idx) args) brs)
         (tCase ip p (mkApps fn args) brs)

| red_cofix_proj p mfix idx args narg fn :
    unfold_cofix mfix idx = Some (narg, fn) ->
    red1 Σ Γ (tProj p (mkApps (tCoFix mfix idx) args))
         (tProj p (mkApps fn args))

| red_delta c decl body (isdecl : declared_constant Σ c decl) u :
    decl.(cst_body) = Some body ->
    red1 Σ Γ (tConst c u) (subst_instance u body)

| red_proj p u args arg:
    nth_error args (p.(proj_npars) + p.(proj_arg)) = Some arg ->
    red1 Σ Γ (tProj p (mkApps (tConstruct p.(proj_ind) 0 u) args)) arg

| abs_red_l na M M' N : red1 Σ Γ M M' -> red1 Σ Γ (tLambda na M N) (tLambda na M' N)
| abs_red_r na M M' N : red1 Σ (Γ ,, vass na N) M M' -> red1 Σ Γ (tLambda na N M) (tLambda na N M')

| letin_red_def na b t b' r : red1 Σ Γ b r -> red1 Σ Γ (tLetIn na b t b') (tLetIn na r t b')
| letin_red_ty na b t b' r : red1 Σ Γ t r -> red1 Σ Γ (tLetIn na b t b') (tLetIn na b r b')
| letin_red_body na b t b' r : red1 Σ (Γ ,, vdef na b t) b' r -> red1 Σ Γ (tLetIn na b t b') (tLetIn na b t r)

| case_red_pred_param ind params params' puinst pcontext preturn c brs :
    OnOne2 (red1 Σ Γ) params params' ->
    red1 Σ Γ (tCase ind (mk_predicate puinst params pcontext preturn) c brs)
             (tCase ind (mk_predicate puinst params' pcontext preturn) c brs)

| case_red_pred_return ind mdecl idecl (isdecl : declared_inductive Σ ind.(ci_ind) mdecl idecl)
                       params puinst pcontext preturn preturn' c brs :
    let p := {| pparams := params; puinst := puinst; pcontext := pcontext; preturn := preturn |} in
    let p' := {| pparams := params; puinst := puinst; pcontext := pcontext; preturn := preturn' |} in
    red1 Σ (Γ ,,, case_predicate_context ind.(ci_ind) mdecl idecl p) preturn preturn' ->
    red1 Σ Γ (tCase ind p c brs)
             (tCase ind p' c brs)

| case_red_discr ind p c c' brs : red1 Σ Γ c c' -> red1 Σ Γ (tCase ind p c brs) (tCase ind p c' brs)

| case_red_brs ind mdecl idecl (isdecl : declared_inductive Σ ind.(ci_ind) mdecl idecl) p c brs brs' :
    OnOne2All (fun brctx br br' =>
      on_Trel_eq (red1 Σ (Γ ,,, brctx)) bbody bcontext br br')
      (case_branches_contexts ind.(ci_ind) mdecl idecl p brs) brs brs' ->
    red1 Σ Γ (tCase ind p c brs) (tCase ind p c brs')

| proj_red p c c' : red1 Σ Γ c c' -> red1 Σ Γ (tProj p c) (tProj p c')

| app_red_l M1 N1 M2 : red1 Σ Γ M1 N1 -> red1 Σ Γ (tApp M1 M2) (mkApps N1 M2)
| app_red_r M2 N2 M1 : OnOne2 (red1 Σ Γ) M2 N2 -> red1 Σ Γ (tApp M1 M2) (tApp M1 N2)

| prod_red_l na M1 M2 N1 : red1 Σ Γ M1 N1 -> red1 Σ Γ (tProd na M1 M2) (tProd na N1 M2)
| prod_red_r na M2 N2 M1 : red1 Σ (Γ ,, vass na M1) M2 N2 ->
                               red1 Σ Γ (tProd na M1 M2) (tProd na M1 N2)

| evar_red ev l l' : OnOne2 (red1 Σ Γ) l l' -> red1 Σ Γ (tEvar ev l) (tEvar ev l')

| cast_red_l M1 k M2 N1 : red1 Σ Γ M1 N1 -> red1 Σ Γ (tCast M1 k M2) (tCast N1 k M2)
| cast_red_r M2 k N2 M1 : red1 Σ Γ M2 N2 -> red1 Σ Γ (tCast M1 k M2) (tCast M1 k N2)
| cast_red M1 k M2 : red1 Σ Γ (tCast M1 k M2) M1

| fix_red_ty mfix0 mfix1 idx :
    OnOne2 (on_Trel_eq (red1 Σ Γ) dtype (fun x => (dname x, dbody x, rarg x))) mfix0 mfix1 ->
    red1 Σ Γ (tFix mfix0 idx) (tFix mfix1 idx)

| fix_red_body mfix0 mfix1 idx :
    OnOne2 (on_Trel_eq (red1 Σ (Γ ,,, fix_context mfix0)) dbody (fun x => (dname x, dtype x, rarg x)))
      mfix0 mfix1 ->
    red1 Σ Γ (tFix mfix0 idx) (tFix mfix1 idx)

| cofix_red_ty mfix0 mfix1 idx :
    OnOne2 (on_Trel_eq (red1 Σ Γ) dtype (fun x => (dname x, dbody x, rarg x))) mfix0 mfix1 ->
    red1 Σ Γ (tCoFix mfix0 idx) (tCoFix mfix1 idx)

| cofix_red_body mfix0 mfix1 idx :
    OnOne2 (on_Trel_eq (red1 Σ (Γ ,,, fix_context mfix0)) dbody (fun x => (dname x, dtype x, rarg x))) mfix0 mfix1 ->
    red1 Σ Γ (tCoFix mfix0 idx) (tCoFix mfix1 idx).

Reserved Notation " Σ ;;; Γ |- t : T " (at level 50, Γ, t, T at next level).
Reserved Notation " Σ ;;; Γ |- t <=[ pb ] u " (at level 50, Γ, t, u at next level).

Inductive cumul_gen `{checker_flags} (Σ : global_env_ext) (Γ : context) (pb : conv_pb) : term -> term -> Type :=
 | cumul_refl t u : compare_term pb Σ (global_ext_constraints Σ) t u -> Σ ;;; Γ |- t <=[pb] u
 | cumul_red_l t u v : red1 Σ.1 Γ t v -> Σ ;;; Γ |- v <=[pb] u -> Σ ;;; Γ |- t <=[pb] u
 | cumul_red_r t u v : Σ ;;; Γ |- t <=[pb] v -> red1 Σ.1 Γ u v -> Σ ;;; Γ |- t <=[pb] u
  where "Σ ;;; Γ |- t <=[ pb ] u " := (cumul_gen Σ Γ pb t u).
Notation " Σ ;;; Γ |- t <= u " := (cumul_gen Σ Γ Cumul t u) (at level 50, Γ, t, u at next level) : type_scope.

Module TemplateEnvTyping := EnvTyping TemplateTerm Env TemplateTermUtils.
Include TemplateEnvTyping.

Module TemplateConversion := Conversion TemplateTerm Env TemplateTermUtils TemplateEnvTyping.
Include TemplateConversion.

Module TemplateConversionPar <: ConversionParSig TemplateTerm Env TemplateTermUtils TemplateEnvTyping.
  Definition cumul_gen := @cumul_gen.
End TemplateConversionPar.

Class GuardChecker :=
{
  fix_guard : global_env_ext -> context -> mfixpoint term -> bool ;

  cofix_guard : global_env_ext -> context -> mfixpoint term -> bool ;

  fix_guard_red1 Σ Γ mfix mfix' idx :
      fix_guard Σ Γ mfix ->
      red1 Σ Γ (tFix mfix idx) (tFix mfix' idx) ->
      fix_guard Σ Γ mfix' ;

  fix_guard_lift Σ Γ Γ' Γ'' mfix :
    let k' := (#|mfix| + #|Γ'|)%nat in
    let mfix' := map (map_def (lift #|Γ''| #|Γ'|) (lift #|Γ''| k')) mfix in
    fix_guard Σ (Γ ,,, Γ') mfix ->
    fix_guard Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') mfix' ;

  fix_guard_subst Σ Γ Γ' Δ mfix s k :
    let k' := (#|mfix| + k)%nat in
    let mfix' := map (map_def (subst s k) (subst s k')) mfix in
    fix_guard Σ (Γ ,,, Γ' ,,, Δ) mfix ->
    fix_guard Σ (Γ ,,, subst_context s 0 Δ) mfix' ;

  fix_guard_subst_instance {cf:checker_flags} Σ Γ mfix u univs :
    consistent_instance_ext (Σ.1, univs) Σ.2 u ->
    fix_guard Σ Γ mfix ->
    fix_guard (Σ.1, univs) (subst_instance u Γ) (map (map_def (subst_instance u) (subst_instance u))
                    mfix) ;

  fix_guard_extends Σ Γ mfix (Σ' : global_env_ext) :
    fix_guard Σ Γ mfix ->
    extends Σ.1 Σ' ->
    fix_guard Σ' Γ mfix ;

  cofix_guard_red1 Σ Γ mfix mfix' idx :
    cofix_guard Σ Γ mfix ->
    red1 Σ Γ (tCoFix mfix idx) (tCoFix mfix' idx) ->
    cofix_guard Σ Γ mfix' ;

  cofix_guard_lift Σ Γ Γ' Γ'' mfix :
    let k' := (#|mfix| + #|Γ'|)%nat in
    let mfix' := map (map_def (lift #|Γ''| #|Γ'|) (lift #|Γ''| k')) mfix in
    cofix_guard Σ (Γ ,,, Γ') mfix ->
    cofix_guard Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') mfix' ;

  cofix_guard_subst Σ Γ Γ' Δ mfix s k :
    let k' := (#|mfix| + k)%nat in
    let mfix' := map (map_def (subst s k) (subst s k')) mfix in
    cofix_guard Σ (Γ ,,, Γ' ,,, Δ) mfix ->
    cofix_guard Σ (Γ ,,, subst_context s 0 Δ) mfix' ;

  cofix_guard_subst_instance {cf:checker_flags} Σ Γ mfix u univs :
    consistent_instance_ext (Σ.1, univs) Σ.2 u ->
    cofix_guard Σ Γ mfix ->
    cofix_guard (Σ.1, univs) (subst_instance u Γ) (map (map_def (subst_instance u) (subst_instance u))
                    mfix) ;

  cofix_guard_extends Σ Γ mfix (Σ' : global_env_ext) :
    cofix_guard Σ Γ mfix ->
    extends Σ.1 Σ' ->
    cofix_guard Σ' Γ mfix }.

Axiom guard_checking : GuardChecker.
Global Existing Instance guard_checking.

Definition isCoFinite (r : recursivity_kind) :=
  match r with
  | CoFinite => true
  | _ => false
  end.

Definition check_recursivity_kind (Σ : global_env) ind r :=
  match lookup_env Σ ind with
  | Some (InductiveDecl mib) => eqb mib.(ind_finite) r
  | _ => false
  end.

Definition check_one_fix d :=
  let '{| dname := na;
          dtype := ty;
          dbody := b;
          rarg := arg |} := d in
  let '(ctx, ty) := decompose_prod_assum [] ty in
  match nth_error (List.rev (smash_context [] ctx)) arg with
  | Some argd =>
    let (hd, args) := decompose_app argd.(decl_type) in
    match destInd hd with
    | Some (mkInd mind _, u) => Some mind
    | None => None
    end
  | None => None
  end.

Definition wf_fixpoint (Σ : global_env) mfix :=
  forallb (isLambda ∘ dbody) mfix &&
  let checks := map check_one_fix mfix in
  match map_option_out checks with
  | Some (ind :: inds) =>

    forallb (eqb ind) inds &&
    check_recursivity_kind Σ ind Finite
  | _ => false
  end.

Definition check_one_cofix d :=
  let '{| dname := na;
          dtype := ty;
          dbody := b;
          rarg := arg |} := d in
  let '(ctx, ty) := decompose_prod_assum [] ty in
  let (hd, args) := decompose_app ty in
  match destInd hd with
  | Some (mkInd ind _, u) => Some ind
  | None => None
  end.

Definition wf_cofixpoint (Σ : global_env) mfix :=
  let checks := map check_one_cofix mfix in
  match map_option_out checks with
  | Some (ind :: inds) =>

    forallb (eqb ind) inds &&
    check_recursivity_kind Σ ind CoFinite
  | _ => false
  end.

Reserved Notation "'wf_local' Σ Γ " (at level 9, Σ, Γ at next level).

Inductive typing `{checker_flags} (Σ : global_env_ext) (Γ : context) : term -> term -> Type :=
| type_Rel n decl :
    wf_local Σ Γ ->
    nth_error Γ n = Some decl ->
    Σ ;;; Γ |- tRel n : lift0 (S n) decl.(decl_type)

| type_Sort s :
    wf_local Σ Γ ->
    wf_universe Σ s ->
    Σ ;;; Γ |- tSort s : tSort (Universe.super s)

| type_Cast c k t s :
    Σ ;;; Γ |- t : tSort s ->
    Σ ;;; Γ |- c : t ->
    Σ ;;; Γ |- tCast c k t : t

| type_Prod n t b s1 s2 :
    Σ ;;; Γ |- t : tSort s1 ->
    Σ ;;; Γ ,, vass n t |- b : tSort s2 ->
    Σ ;;; Γ |- tProd n t b : tSort (Universe.sort_of_product s1 s2)

| type_Lambda n t b s1 bty :
    Σ ;;; Γ |- t : tSort s1 ->
    Σ ;;; Γ ,, vass n t |- b : bty ->
    Σ ;;; Γ |- tLambda n t b : tProd n t bty

| type_LetIn n b b_ty b' s1 b'_ty :
    Σ ;;; Γ |- b_ty : tSort s1 ->
    Σ ;;; Γ |- b : b_ty ->
    Σ ;;; Γ ,, vdef n b b_ty |- b' : b'_ty ->
    Σ ;;; Γ |- tLetIn n b b_ty b' : tLetIn n b b_ty b'_ty

| type_App t l t_ty t' :
    Σ ;;; Γ |- t : t_ty ->
    isApp t = false -> l <> [] ->
    typing_spine Σ Γ t_ty l t' ->
    Σ ;;; Γ |- tApp t l : t'

| type_Const cst u :
    wf_local Σ Γ ->
    forall decl (isdecl : declared_constant Σ.1 cst decl),
    consistent_instance_ext Σ decl.(cst_universes) u ->
    Σ ;;; Γ |- (tConst cst u) : subst_instance u decl.(cst_type)

| type_Ind ind u :
    wf_local Σ Γ ->
    forall mdecl idecl (isdecl : declared_inductive Σ.1 ind mdecl idecl),
    consistent_instance_ext Σ mdecl.(ind_universes) u ->
    Σ ;;; Γ |- (tInd ind u) : subst_instance u idecl.(ind_type)

| type_Construct ind i u :
    wf_local Σ Γ ->
    forall mdecl idecl cdecl (isdecl : declared_constructor Σ.1 (ind, i) mdecl idecl cdecl),
    consistent_instance_ext Σ mdecl.(ind_universes) u ->
    Σ ;;; Γ |- (tConstruct ind i u) : type_of_constructor mdecl cdecl (ind, i) u

| type_Case (ci : case_info) p c brs indices ps :
    forall mdecl idecl (isdecl : declared_inductive Σ.1 ci.(ci_ind) mdecl idecl),
    mdecl.(ind_npars) = ci.(ci_npar) ->
    wf_nactx p.(pcontext) (ind_predicate_context ci.(ci_ind) mdecl idecl) ->
    context_assumptions mdecl.(ind_params) = #|p.(pparams)| ->
    consistent_instance_ext Σ (ind_universes mdecl) p.(puinst) ->
    let predctx := case_predicate_context ci.(ci_ind) mdecl idecl p in
    ctx_inst typing Σ Γ (p.(pparams) ++ indices)
      (List.rev (ind_params mdecl ,,, ind_indices idecl)@[p.(puinst)]) ->
    Σ ;;; Γ ,,, predctx |- p.(preturn) : tSort ps ->
    is_allowed_elimination Σ idecl.(ind_kelim) ps ->
    Σ ;;; Γ |- c : mkApps (tInd ci.(ci_ind) p.(puinst)) (p.(pparams) ++ indices) ->
    isCoFinite mdecl.(ind_finite) = false ->
    let ptm := it_mkLambda_or_LetIn predctx p.(preturn) in
    All2i (fun i cdecl br =>
      let brctxty := case_branch_type ci.(ci_ind) mdecl p ptm i cdecl br in
      (wf_nactx br.(bcontext) (cstr_branch_context ci.(ci_ind) mdecl cdecl)) *
      (Σ ;;; Γ ,,, brctxty.1 |- br.(bbody) : brctxty.2) *
      (Σ ;;; Γ ,,, brctxty.1 |- brctxty.2 : tSort ps))
      0 idecl.(ind_ctors) brs ->
    Σ ;;; Γ |- tCase ci p c brs : mkApps ptm (indices ++ [c])

| type_Proj p c u :
    forall mdecl idecl cdecl pdecl (isdecl : declared_projection Σ.1 p mdecl idecl cdecl pdecl) args,
    Σ ;;; Γ |- c : mkApps (tInd p.(proj_ind) u) args ->
    #|args| = ind_npars mdecl ->
    Σ ;;; Γ |- tProj p c : subst0 (c :: List.rev args) (subst_instance u pdecl.(proj_type))

| type_Fix mfix n decl :
    fix_guard Σ Γ mfix ->
    nth_error mfix n = Some decl ->
    wf_local Σ Γ ->
    All (fun d => {s & Σ ;;; Γ |- d.(dtype) :  tSort s}) mfix ->
    All (fun d => (Σ ;;; Γ ,,, fix_context mfix |- d.(dbody) : lift0 #|fix_context mfix| d.(dtype))) mfix ->
    wf_fixpoint Σ mfix ->
      Σ ;;; Γ |- tFix mfix n : decl.(dtype)

| type_CoFix mfix n decl :
    cofix_guard Σ Γ mfix ->
    nth_error mfix n = Some decl ->
    wf_local Σ Γ ->
    All (fun d => {s & Σ ;;; Γ |- d.(dtype) :  tSort s}) mfix ->
    All (fun d => Σ ;;; Γ ,,, fix_context mfix |- d.(dbody) : lift0 #|fix_context mfix| d.(dtype)) mfix ->
    wf_cofixpoint Σ mfix ->
    Σ ;;; Γ |- tCoFix mfix n : decl.(dtype)

| type_Int p prim_ty cdecl :
    wf_local Σ Γ ->
    primitive_constant Σ primInt = Some prim_ty ->
    declared_constant Σ prim_ty cdecl ->
    primitive_invariants cdecl ->
    Σ ;;; Γ |- tInt p : tConst prim_ty []

| type_Float p prim_ty cdecl :
    wf_local Σ Γ ->
    primitive_constant Σ primFloat = Some prim_ty ->
    declared_constant Σ prim_ty cdecl ->
    primitive_invariants cdecl ->
    Σ ;;; Γ |- tFloat p : tConst prim_ty []

| type_Conv t A B s :
    Σ ;;; Γ |- t : A ->
    Σ ;;; Γ |- B : tSort s ->
    Σ ;;; Γ |- A <= B -> Σ ;;; Γ |- t : B

where " Σ ;;; Γ |- t : T " := (typing Σ Γ t T) : type_scope
  and "'wf_local' Σ Γ " := (All_local_env (lift_typing typing Σ) Γ) : type_scope

with typing_spine `{checker_flags} (Σ : global_env_ext) (Γ : context) : term -> list term -> term -> Type :=
| type_spine_nil ty : typing_spine Σ Γ ty [] ty
| type_spine_cons hd tl na A B s T B' :
    Σ ;;; Γ |- tProd na A B : tSort s ->
    Σ ;;; Γ |- T <= tProd na A B ->
    Σ ;;; Γ |- hd : A ->
    typing_spine Σ Γ (subst10 hd B) tl B' ->
    typing_spine Σ Γ T (cons hd tl) B'.

Module TemplateTyping <: Typing TemplateTerm Env TemplateTermUtils TemplateEnvTyping
  TemplateConversion TemplateConversionPar.

  Definition typing := @typing.

End TemplateTyping.
  Context `{checker_flags}.
  Context (fn : forall (Σ : global_env_ext) (Γ : context) (t T : term), typing Σ Γ t T -> size).
  Context (Σ : global_env_ext) (Γ : context).
Fixpoint typing_spine_size t T U (s : typing_spine Σ Γ t T U) : size.
exact (match s with
  | type_spine_nil _ => 0
  | type_spine_cons hd tl na A B s T B' typrod cumul ty s' =>
    (fn _ _ _ _ ty + fn _ _ _ _ typrod + typing_spine_size _ _ _ s')%nat
  end).
