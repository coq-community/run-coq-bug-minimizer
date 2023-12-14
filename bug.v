
(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "-deprecated-native-compiler-option" "-native-compiler" "no" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/metacoq/utils/theories" "MetaCoq.Utils" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/metacoq/common/theories" "MetaCoq.Common" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/metacoq/pcuic/theories" "MetaCoq.PCUIC" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Equations" "Equations" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-top" "Top.bug_01") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 406 lines to 79 lines, then from 92 lines to 4252 lines, then from 4249 lines to 89 lines, then from 102 lines to 901 lines, then from 906 lines to 127 lines, then from 140 lines to 1768 lines, then from 1773 lines to 2117 lines, then from 2107 lines to 389 lines, then from 402 lines to 1300 lines, then from 1304 lines to 550 lines, then from 563 lines to 2362 lines, then from 2361 lines to 555 lines, then from 568 lines to 1055 lines, then from 1060 lines to 562 lines, then from 575 lines to 2873 lines, then from 2875 lines to 659 lines, then from 672 lines to 2567 lines, then from 2571 lines to 2380 lines *)
(* coqc version 8.20+alpha compiled with OCaml 4.09.0
   coqtop version c74786003383:/builds/coq/coq/_build/default,(HEAD detached at f7aaed9) (f7aaed98877033e8fd8c34e63e9c7269aff2f1c7)
   Expected coqc runtime on this file: 11.257 sec *)
Require Coq.Init.Ltac.
Require Coq.Bool.Bool.
Require Coq.ZArith.ZArith.
Require Coq.Arith.Arith.
Require Coq.micromega.Lia.
Require Coq.Lists.List.
Require Coq.Init.Nat.
Require Coq.Strings.Ascii.
Require Coq.Strings.String.
Require Coq.Classes.Morphisms.
Require Coq.extraction.Extraction.
Require Coq.Unicode.Utf8_core.
Require Equations.Init.
Require Equations.Signature.
Require Equations.CoreTactics.
Require Coq.Relations.Relation_Definitions.
Require Equations.Prop.Logic.
Require Equations.Prop.Classes.
Require Coq.Program.Tactics.
Require Equations.Prop.EqDec.
Require Equations.Prop.DepElim.
Require Coq.Relations.Relations.
Require Equations.Prop.Constants.
Require Coq.Bool.Bvector.
Require Coq.Arith.Wf_nat.
Require Coq.Wellfounded.Wellfounded.
Require Coq.Relations.Relation_Operators.
Require Coq.Wellfounded.Lexicographic_Product.
Require Coq.Program.Wf.
Require Coq.Logic.FunctionalExtensionality.
Require Equations.Prop.Subterm.
Require Equations.Prop.FunctionalInduction.
Require Equations.Prop.Tactics.
Require Equations.Prop.NoConfusion.
Require Equations.Prop.EqDecInstances.
Require Equations.Prop.Loader.
Require Equations.Prop.Telescopes.
Require Equations.Prop.Equations.
Require MetaCoq.Utils.MCPrelude.
Require Coq.ssr.ssreflect.
Require MetaCoq.Utils.MCReflect.
Require Coq.Unicode.Utf8.
Require Coq.Lists.SetoidList.
Require Coq.Classes.CRelationClasses.
Require Equations.Type.Logic.
Require Equations.Type.Relation.
Require Equations.Type.Relation_Properties.
Require MetaCoq.Utils.MCRelations.
Require Coq.ssr.ssrbool.
Require MetaCoq.Utils.ReflectEq.
Require MetaCoq.Utils.MCList.
Require Coq.Classes.RelationClasses.
Require MetaCoq.Utils.MCProd.
Require MetaCoq.Utils.MCOption.
Require MetaCoq.Utils.MCSquash.
Require MetaCoq.Utils.All_Forall.
Require MetaCoq.Utils.MCArith.
Require Coq.Structures.OrderedType.
Require Coq.Structures.Orders.
Require MetaCoq.Utils.MCCompare.
Require MetaCoq.Utils.MCEquality.
Require Coq.Init.Decimal.
Require Coq.Numbers.DecimalString.
Require Coq.NArith.NArith.
Require Coq.Strings.Byte.
Require Coq.NArith.BinNat.
Require MetaCoq.Utils.ByteCompare.
Require Coq.Logic.Eqdep_dec.
Require MetaCoq.Utils.ByteCompareSpec.
Require Coq.Structures.OrdersAlt.
Require MetaCoq.Utils.bytestring.
Require MetaCoq.Utils.MCString.
Require MetaCoq.Utils.MCTactics.SpecializeBy.
Require MetaCoq.Utils.MCTactics.Zeta1.
Require MetaCoq.Utils.MCTactics.GeneralizeOverHoles.
Require MetaCoq.Utils.MCTactics.FindHyp.
Require MetaCoq.Utils.MCTactics.UniquePose.
Require MetaCoq.Utils.MCTactics.InHypUnderBindersDo.
Require MetaCoq.Utils.MCTactics.SpecializeUnderBindersBy.
Require MetaCoq.Utils.MCTactics.Head.
Require MetaCoq.Utils.MCTactics.DestructHyps.
Require MetaCoq.Utils.MCTactics.DestructHead.
Require MetaCoq.Utils.MCTactics.SpecializeAllWays.
Require MetaCoq.Utils.MCTactics.SplitInContext.
Require Ltac2.Init.
Require Ltac2.Message.
Require Ltac2.Control.
Require Ltac2.Ltac1.
Require MetaCoq.Utils.MCUtils.
Require MetaCoq.Utils.monad_utils.
Require MetaCoq.Utils.utils.
Require Coq.btauto.Btauto.
Require MetaCoq.Common.config.
Require Coq.MSets.MSetList.
Require Coq.MSets.MSetAVL.
Require Coq.MSets.MSetFacts.
Require Coq.MSets.MSetProperties.
Require Coq.MSets.MSetDecide.
Require Coq.FSets.FMapAVL.
Require Coq.MSets.MSetInterface.
Require MetaCoq.Utils.MCMSets.
Require Coq.Structures.Equalities.
Require Coq.FSets.FMapInterface.
Require Coq.FSets.FMapList.
Require Coq.FSets.FMapFullAVL.
Require Coq.FSets.FMapFacts.
Require MetaCoq.Utils.MCFSets.
Require Coq.Setoids.Setoid.
Require Coq.Structures.OrderedTypeAlt.
Require Coq.Structures.OrderedTypeEx.
Require MetaCoq.Common.Kernames.
Require Coq.Floats.SpecFloat.
Require MetaCoq.Common.BasicAst.
Require MetaCoq.Common.Universes.
Require Coq.ssr.ssrfun.
Require Coq.Numbers.Cyclic.Int63.Uint63.
Require Coq.Floats.PrimFloat.
Require Coq.Floats.FloatOps.
Require Coq.Numbers.HexadecimalString.
Require MetaCoq.Common.Primitive.
Require MetaCoq.Common.Environment.
Require Coq.Floats.FloatAxioms.
Require MetaCoq.Common.Reflect.
Require Coq.Classes.CMorphisms.
Require MetaCoq.Common.EnvironmentTyping.
Require MetaCoq.PCUIC.utils.PCUICPrimitive.
Require MetaCoq.PCUIC.PCUICAst.
Require MetaCoq.PCUIC.utils.PCUICOnOne.
Require Coq.Arith.Compare_dec.
Require Coq.Classes.SetoidTactics.
Require Coq.PArith.BinPos.
Require Coq.Program.Program.
Require Coq.ZArith.Zcompare.
Require MetaCoq.Utils.LibHypsNaming.
Require MetaCoq.Utils.wGraph.
Require MetaCoq.Common.uGraph.
Require MetaCoq.Common.EnvironmentReflect.
Require MetaCoq.PCUIC.utils.PCUICSize.
Require MetaCoq.PCUIC.utils.PCUICAstUtils.
Require MetaCoq.PCUIC.Syntax.PCUICCases.
Require MetaCoq.PCUIC.Syntax.PCUICInduction.
Require MetaCoq.PCUIC.Syntax.PCUICLiftSubst.
Require MetaCoq.PCUIC.Syntax.PCUICReflect.

Module Export AdmitTactic.
Module Import LocalFalse.
Inductive False : Prop := .
End LocalFalse.
Axiom proof_admitted : False.
Import Coq.Init.Ltac.
Tactic Notation "admit" := abstract case proof_admitted.
End AdmitTactic.

Module MetaCoq_DOT_PCUIC_DOT_PCUICEquality_WRAPPED.
Module PCUICEquality.
 
Import Coq.Classes.CMorphisms.
Import MetaCoq.Utils.LibHypsNaming MetaCoq.Utils.utils.
Import MetaCoq.Common.config MetaCoq.Common.Reflect.
Import MetaCoq.PCUIC.PCUICAst MetaCoq.PCUIC.utils.PCUICAstUtils MetaCoq.PCUIC.Syntax.PCUICInduction
     MetaCoq.PCUIC.Syntax.PCUICLiftSubst MetaCoq.PCUIC.Syntax.PCUICReflect.
Import Coq.ssr.ssreflect Coq.ssr.ssrbool.
Import Equations.Prop.DepElim.
Import Equations.Prop.Equations.
Set Equations With UIP.

Ltac pcuic :=
  try repeat red; cbn in *;
   try (solve [ intuition auto; eauto with pcuic || (try lia || congruence) ]).

#[global]
Instance All2_fold_len {A} P (Γ Δ : list A) : HasLen (All2_fold P Γ Δ) #|Γ| #|Δ| :=
  All2_fold_length.

Implicit Types (cf : checker_flags).

Definition R_universe_instance R :=
  fun u u' => Forall2 R (List.map Universe.make u) (List.map Universe.make u').

Definition R_universe_instance_dep R R' :=
  fun {u u'} (H : R_universe_instance R u u') => Forall2_dep R' H.

 

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

Notation global_variance Σ := (global_variance_gen (lookup_env Σ)).

Definition R_opt_variance Re Rle v :=
  match v with
  | Some v => R_universe_instance_variance Re Rle v
  | None => R_universe_instance Re
  end.

Definition R_global_instance_gen Σ Re Rle gr napp :=
  R_opt_variance Re Rle (global_variance_gen Σ gr napp).

Notation R_global_instance Σ := (R_global_instance_gen (lookup_env Σ)).

Definition R_ind_universes {cf:checker_flags} (Σ : global_env_ext) ind n i i' :=
  R_global_instance Σ (eq_universe (global_ext_constraints Σ))
    (leq_universe (global_ext_constraints Σ)) (IndRef ind) n i i'.

Lemma R_universe_instance_impl R R' :
  RelationClasses.subrelation R R' ->
  RelationClasses.subrelation (R_universe_instance R) (R_universe_instance R').
Proof.
  intros H x y xy.
eapply Forall2_impl ; tea.
Qed.

Lemma R_universe_instance_impl' R R' :
  RelationClasses.subrelation R R' ->
  forall u u', R_universe_instance R u u' -> R_universe_instance R' u u'.
Proof.
  intros H x y xy.
eapply Forall2_impl ; tea.
Qed.

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

  Derive Signature NoConfusion for compare_decls.
End compare_decls.
Arguments compare_decls : clear implicits.

Notation eq_context_upto_names := (All2 (compare_decls eq eq)).

Notation eq_context_gen eq_term leq_term :=
  (All2_fold (fun _ _ => compare_decls eq_term leq_term)).

Lemma eq_context_upto_names_gen Γ Γ' : eq_context_upto_names Γ Γ' <~> eq_context_gen eq eq Γ Γ'.
Proof.
  split; intros e; depind e; constructor; auto.
Qed.

Lemma compare_decls_impl eq_term leq_term eq_term' leq_term' :
  subrelation eq_term eq_term' ->
  subrelation leq_term leq_term' ->
  subrelation (compare_decls eq_term leq_term)
    (compare_decls eq_term' leq_term').
Proof.
  intros he hle x y []; constructor; auto.
Qed.

Lemma eq_context_gen_impl eq_term leq_term eq_term' leq_term' :
  subrelation eq_term eq_term' ->
  subrelation leq_term leq_term' ->
  subrelation (eq_context_gen eq_term leq_term) (eq_context_gen eq_term' leq_term').
Proof.
  intros he hle x y eq.
  eapply All2_fold_impl; tea => /=.
  intros; eapply compare_decls_impl; tea.
Qed.

Lemma compare_decl_impl_ondecl P eq_term leq_term eq_term' leq_term' d d' :
  ondecl P d ->
  (forall x y, P x -> eq_term x y -> eq_term' x y) ->
  (forall x y, P x -> leq_term x y -> leq_term' x y) ->
  compare_decls eq_term leq_term d d' ->
  compare_decls eq_term' leq_term' d d'.
Proof.
  intros ond he hle cd; depelim cd; depelim ond; constructor => //; eauto.
Qed.

Lemma compare_decl_map eq_term leq_term f g d d' :
  compare_decls (fun x y => eq_term (f x) (g y))
    (fun x y => leq_term (f x) (g y)) d d' ->
  compare_decls eq_term leq_term (map_decl f d) (map_decl g d').
Proof.
  intros h; depelim h; constructor; intuition auto.
Qed.

Definition bcompare_decls (eq_term leq_term : term -> term -> bool) (d d' : context_decl) : bool :=
  match d, d' with
  | {| decl_name := na; decl_body := None; decl_type := T |},
    {| decl_name := na'; decl_body := None; decl_type := T' |} =>
    eqb_binder_annot na na' && leq_term T T'
  | {| decl_name := na; decl_body := Some b; decl_type := T |},
    {| decl_name := na'; decl_body := Some b'; decl_type := T' |} =>
    eqb_binder_annot na na' && eq_term b b' && leq_term T T'
  | _, _ => false
  end.

#[global]
Polymorphic Instance compare_decl_refl eq_term leq_term :
  CRelationClasses.Reflexive eq_term ->
  CRelationClasses.Reflexive leq_term ->
  CRelationClasses.Reflexive (compare_decls eq_term leq_term).
Proof.
  intros heq hle d.
  destruct d as [na [b|] ty]; constructor; auto; reflexivity.
Qed.

#[global]
Polymorphic Instance compare_decl_sym eq_term leq_term :
  CRelationClasses.Symmetric eq_term ->
  CRelationClasses.Symmetric leq_term ->
  CRelationClasses.Symmetric (compare_decls eq_term leq_term).
Proof.
  intros heq hle d d' []; constructor; auto; now symmetry.
Qed.

#[global]
Polymorphic Instance compare_decl_trans eq_term leq_term :
  CRelationClasses.Transitive eq_term ->
  CRelationClasses.Transitive leq_term ->
  CRelationClasses.Transitive (compare_decls eq_term leq_term).
Proof.
  intros hle hre x y z h h'; depelim h; depelim h'; constructor; auto;
  etransitivity; eauto.
Qed.

#[global]
Instance alpha_eq_reflexive : CRelationClasses.Reflexive eq_context_upto_names.
Proof.
  intros x.
eapply All2_refl.
reflexivity.
Qed.

#[global]
Instance alpha_eq_symmmetric : CRelationClasses.Symmetric eq_context_upto_names.
Proof.
  intros x.
eapply All2_symP.
tc.
Qed.

#[global]
Instance alpha_eq_trans : CRelationClasses.Transitive eq_context_upto_names.
Proof.
  intros x y z.
apply All2_trans.
tc.
Qed.

#[global]
Polymorphic Instance eq_context_refl eq_term leq_term :
  CRelationClasses.Reflexive eq_term ->
  CRelationClasses.Reflexive leq_term ->
  CRelationClasses.Reflexive (eq_context_gen eq_term leq_term).
Proof.
  intros heq hle x.
  eapply All2_fold_refl.
  intros.
reflexivity.
Qed.

#[global]
Polymorphic Instance eq_context_sym eq_term leq_term :
  CRelationClasses.Symmetric eq_term ->
  CRelationClasses.Symmetric leq_term ->
  CRelationClasses.Symmetric (eq_context_gen eq_term leq_term).
Proof.
  intros heq hle x.
  eapply All2_fold_sym.
  intros.
now symmetry.
Qed.

#[global]
Polymorphic Instance eq_context_trans eq_term leq_term :
  CRelationClasses.Transitive eq_term ->
  CRelationClasses.Transitive leq_term ->
  CRelationClasses.Transitive (eq_context_gen eq_term leq_term).
Proof.
  intros hr x y z.
  eapply All2_fold_trans; intros.
  now transitivity y0.
Qed.

Definition eq_predicate (eq_term : term -> term -> Type) Re p p' :=
  All2 eq_term p.(pparams) p'.(pparams) *
  (R_universe_instance Re p.(puinst) p'.(puinst) *
  ((eq_context_gen eq eq p.(pcontext) p'.(pcontext)) *
    eq_term p.(preturn) p'.(preturn))).

 

 

Reserved Notation " Σ ⊢ t <==[ Rle , napp ] u" (at level 50, t, u at next level,
  format "Σ  ⊢  t  <==[ Rle , napp ]  u").

Inductive eq_term_upto_univ_napp Σ (Re Rle : Universe.t -> Universe.t -> Prop) (napp : nat) : term -> term -> Type :=
| eq_Rel : forall n,
    Σ ⊢ tRel n <==[ Rle , napp ] tRel n

| eq_Evar : forall e args args',
    All2 (eq_term_upto_univ_napp Σ Re Re 0) args args' ->
    Σ ⊢ tEvar e args <==[ Rle , napp ] tEvar e args'

| eq_Var : forall id,
    Σ ⊢ tVar id <==[ Rle , napp ] tVar id

| eq_Sort : forall s s',
    Rle s s' ->
    Σ ⊢ tSort s  <==[ Rle , napp ] tSort s'

| eq_App : forall t t' u u',
    Σ ⊢ t <==[ Rle , S napp ] t' ->
    Σ ⊢ u <==[ Re , 0 ] u' ->
    Σ ⊢ tApp t u <==[ Rle , napp ] tApp t' u'

| eq_Const : forall c u u',
    R_universe_instance Re u u' ->
    Σ ⊢ tConst c u <==[ Rle , napp ] tConst c u'

| eq_Ind : forall i u u',
    R_global_instance Σ Re Rle (IndRef i) napp u u' ->
    Σ ⊢ tInd i u <==[ Rle , napp ] tInd i u'

| eq_Construct : forall i k u u',
    R_global_instance Σ Re Rle (ConstructRef i k) napp u u' ->
    Σ ⊢ tConstruct i k u <==[ Rle , napp ] tConstruct i k u'

| eq_Lambda : forall na na' ty ty' t t',
    eq_binder_annot na na' ->
    Σ ⊢ ty <==[ Re , 0 ] ty' ->
    Σ ⊢ t <==[ Rle , 0 ] t' ->
    Σ ⊢ tLambda na ty t <==[ Rle , napp ] tLambda na' ty' t'

| eq_Prod : forall na na' a a' b b',
    eq_binder_annot na na' ->
    Σ ⊢ a <==[ Re , 0 ] a' ->
    Σ ⊢ b <==[ Rle , 0 ] b' ->
    Σ ⊢ tProd na a b <==[ Rle , napp ] tProd na' a' b'

| eq_LetIn : forall na na' t t' ty ty' u u',
    eq_binder_annot na na' ->
    Σ ⊢ t <==[ Re , 0 ] t' ->
    Σ ⊢ ty <==[ Re , 0 ] ty' ->
    Σ ⊢ u <==[ Rle , 0 ] u' ->
    Σ ⊢ tLetIn na t ty u <==[ Rle , napp ] tLetIn na' t' ty' u'

| eq_Case : forall indn p p' c c' brs brs',
    eq_predicate (eq_term_upto_univ_napp Σ Re Re 0) Re p p' ->
    Σ ⊢ c <==[ Re , 0 ] c' ->
    All2 (fun x y =>
      eq_context_gen eq eq (bcontext x) (bcontext y) *
      (Σ ⊢ x.(bbody) <==[ Re , 0 ] y.(bbody))
    ) brs brs' ->
    Σ ⊢ tCase indn p c brs <==[ Rle , napp ] tCase indn p' c' brs'

| eq_Proj : forall p c c',
    Σ ⊢ c <==[ Re , 0 ] c' ->
    Σ ⊢ tProj p c <==[ Rle , napp ] tProj p c'

| eq_Fix : forall mfix mfix' idx,
    All2 (fun x y =>
      (Σ ⊢ x.(dtype) <==[ Re , 0 ] y.(dtype)) *
      (Σ ⊢ x.(dbody) <==[ Re , 0 ] y.(dbody)) *
      (x.(rarg) = y.(rarg)) *
      eq_binder_annot x.(dname) y.(dname)
    )%type mfix mfix' ->
    Σ ⊢ tFix mfix idx <==[ Rle , napp ] tFix mfix' idx

| eq_CoFix : forall mfix mfix' idx,
    All2 (fun x y =>
      (Σ ⊢ x.(dtype) <==[ Re , 0 ] y.(dtype)) *
      (Σ ⊢ x.(dbody) <==[ Re , 0 ] y.(dbody)) *
      (x.(rarg) = y.(rarg)) *
      eq_binder_annot x.(dname) y.(dname)
    ) mfix mfix' ->
    Σ ⊢ tCoFix mfix idx <==[ Rle , napp ] tCoFix mfix' idx

| eq_Prim i : eq_term_upto_univ_napp Σ Re Rle napp (tPrim i) (tPrim i)
where " Σ ⊢ t <==[ Rle , napp ] u " := (eq_term_upto_univ_napp Σ _ Rle napp t u) : type_scope.

Notation eq_term_upto_univ Σ Re Rle := (eq_term_upto_univ_napp Σ Re Rle 0).

 

Definition compare_term_napp `{checker_flags} (pb : conv_pb) Σ φ napp (t u : term) :=
  eq_term_upto_univ_napp Σ (eq_universe φ) (compare_universe pb φ) napp t u.

Definition compare_term `{checker_flags} (pb : conv_pb) Σ φ (t u : term) :=
  eq_term_upto_univ Σ (eq_universe φ) (compare_universe pb φ) t u.

 

Notation eq_term := (compare_term Conv).

 

Notation leq_term := (compare_term Cumul).

Definition compare_opt_term `{checker_flags} (pb : conv_pb) Σ φ (t u : option term) :=
  match t, u with
  | Some t, Some u => compare_term pb Σ φ t u
  | None, None => True
  | _, _ => False
  end.

Definition compare_decl `{checker_flags} pb Σ φ (d d' : context_decl) :=
  compare_decls (compare_term Conv Σ φ) (compare_term pb Σ φ) d d'.

Notation eq_decl := (compare_decl Conv).
Notation leq_decl := (compare_decl Cumul).

Definition compare_context `{checker_flags} pb Σ φ (Γ Δ : context) :=
  eq_context_gen (compare_term Conv Σ φ) (compare_term pb Σ φ) Γ Δ.

Notation eq_context := (compare_context Conv).
Notation leq_context := (compare_context Cumul).

Notation eq_context_upto Σ Re Rle :=
  (eq_context_gen (eq_term_upto_univ Σ Re Re) (eq_term_upto_univ Σ Re Rle)).

Lemma R_global_instance_refl Σ Re Rle gr napp u :
  RelationClasses.Reflexive Re ->
  RelationClasses.Reflexive Rle ->
  R_global_instance Σ Re Rle gr napp u u.
Proof.
  intros rRE rRle.
  unfold R_global_instance_gen.
  destruct global_variance_gen as [v|] eqn:lookup.
  -
 induction u in v |- *; simpl; auto;
    unfold R_opt_variance in IHu; destruct v; simpl; auto.
    split; auto.
    destruct t; simpl; auto.
  -
 apply Forall2_same; eauto.
Qed.

#[global]
Instance eq_binder_annot_equiv {A} : RelationClasses.Equivalence (@eq_binder_annot A A).
Proof.
  split.
  -
 red.
reflexivity.
  -
 red; now symmetry.
  -
 intros x y z; unfold eq_binder_annot.
    apply transitivity.
Qed.

Definition eq_binder_annot_refl {A} x : @eq_binder_annot A A x x.
Proof.
reflexivity.
Qed.

#[global]
Hint Resolve eq_binder_annot_refl : core.

 
#[global]
Existing Instance All2_symP.

 
#[global]
Instance Forall2_symP :
  forall A (P : A -> A -> Prop),
    RelationClasses.Symmetric P ->
    Symmetric (Forall2 P).
Proof.
  intros A P h l l' hl.
  induction hl.
all: auto.
Qed.

Lemma eq_binder_relevances_refl (x : list aname) : All2 (on_rel eq binder_relevance) x x.
Proof.
now eapply All_All2_refl, All_refl.
Qed.
#[global]
Hint Resolve eq_binder_relevances_refl : core.

#[global]
Instance R_universe_instance_refl Re : RelationClasses.Reflexive Re ->
  RelationClasses.Reflexive (R_universe_instance Re).
Proof.
intros tRe x.
eapply Forall2_map.
  induction x; constructor; auto.
Qed.

#[global]
Instance R_universe_instance_sym Re : RelationClasses.Symmetric Re ->
  RelationClasses.Symmetric (R_universe_instance Re).
Proof.
intros tRe x y.
now eapply Forall2_symP.
Qed.

#[global]
Instance R_universe_instance_trans Re : RelationClasses.Transitive Re ->
  RelationClasses.Transitive (R_universe_instance Re).
Proof.
intros tRe x y z.
now eapply Forall2_trans.
Qed.

Lemma onctx_eq_ctx P ctx eq_term :
  onctx P ctx ->
  (forall x, P x -> eq_term x x) ->
  All2_fold (fun _ _ => compare_decls eq_term eq_term) ctx ctx.
Proof.
  intros onc HP.
  induction onc.
  -
 constructor; auto.
  -
 constructor; auto; simpl.
    destruct x as [na [b|] ty]; destruct p; simpl in *;
    constructor; auto.
Qed.

#[global]
Polymorphic Instance creflexive_eq A : CRelationClasses.Reflexive (@eq A).
Proof.
intro x.
constructor.
Qed.

#[global]
Polymorphic Instance eq_predicate_refl Re Ru :
  CRelationClasses.Reflexive Re ->
  RelationClasses.Reflexive Ru ->
  CRelationClasses.Reflexive (eq_predicate Re Ru).
Proof.
  intros hre hru.
  intros p.
unfold eq_predicate; intuition auto; try reflexivity.
  eapply All2_same; reflexivity.
Qed.

#[global]
Polymorphic Instance eq_term_upto_univ_refl Σ Re Rle napp :
  RelationClasses.Reflexive Re ->
  RelationClasses.Reflexive Rle ->
  Reflexive (eq_term_upto_univ_napp Σ Re Rle napp).
Proof.
  intros hRe hRle t.
  induction t in napp, Rle, hRle |- * using term_forall_list_ind.
  all: simpl.
  all: try constructor.
all: eauto.
  all: try solve [eapply All_All2 ; eauto].
  all: try solve [eapply Forall2_same ; eauto].
  all: try solve [unfold eq_predicate; solve_all; eapply All_All2; eauto].
  -
 apply R_global_instance_refl; auto.
  -
 apply R_global_instance_refl; auto.
  -
 destruct X as [? [? ?]].
    unfold eq_predicate; solve_all.
    eapply All_All2; eauto.
reflexivity.
    eapply onctx_eq_ctx in a0; eauto.
  -
 eapply All_All2; eauto; simpl; intuition eauto.
    eapply onctx_eq_ctx in a; eauto.
  -
 eapply All_All2; eauto; simpl; intuition eauto.
  -
 eapply All_All2; eauto; simpl; intuition eauto.
Qed.

#[global]
Instance compare_term_refl {cf} pb {Σ : global_env} φ : Reflexive (compare_term pb Σ φ).
Proof.
eapply eq_term_upto_univ_refl; tc.
Qed.

Derive Signature for eq_term_upto_univ_napp.

Lemma R_global_instance_sym Σ Re Rle gr napp u u' :
  RelationClasses.Symmetric Re ->
  RelationClasses.Symmetric Rle ->
  R_global_instance Σ Re Rle gr napp u' u ->
  R_global_instance Σ Re Rle gr napp u u'.
Proof.
  intros rRE rRle.
  unfold R_global_instance_gen.
  destruct global_variance_gen as [v|] eqn:lookup.
  -
 induction u in u', v |- *; destruct u'; simpl; auto;
    destruct v as [|v vs]; unfold R_opt_variance in IHu; simpl; auto.
    intros [Ra Ru'].
split.
    destruct v; simpl; auto.
    apply IHu; auto.
  -
 apply Forall2_symP; eauto.
Qed.

Lemma onctx_eq_ctx_sym P ctx ctx' eq_term :
  onctx P ctx ->
  (forall x, P x -> forall y, eq_term x y -> eq_term y x) ->
  All2_fold (fun _ _ => compare_decls eq_term eq_term) ctx ctx' ->
  All2_fold (fun _ _ => compare_decls eq_term eq_term) ctx' ctx.
Proof.
  intros onc HP H1.
  induction H1; depelim onc; constructor; intuition auto; simpl in *.
  depelim p; depelim o; constructor; auto; try now symmetry.
Qed.

#[global]
Polymorphic Instance eq_term_upto_univ_sym Σ Re Rle napp :
  RelationClasses.Symmetric Re ->
  RelationClasses.Symmetric Rle ->
  Symmetric (eq_term_upto_univ_napp Σ Re Rle napp).
Proof.
  intros he hle u v e.
  pose proof (@RelationClasses.symmetry _ (@eq_binder_annot name name) _).
  induction u in Rle, hle, v, napp, e |- * using term_forall_list_ind.
  all: dependent destruction e.
  all: try solve [
    econstructor ; eauto using R_global_instance_sym ;
    try eapply Forall2_symP ; eauto
  ].
  -
 econstructor.
    eapply All2_All_mix_left in X as h; eauto.
    clear a X.
    induction h.
    +
 constructor.
    +
 destruct r as [h1 h2].
eapply h1 in h2 ; auto.
  -
 solve_all.
destruct e as (r & ? & eq & ?).
    econstructor; rewrite ?e; unfold eq_predicate in *; solve_all; eauto.
    eapply All2_sym; solve_all.
    unfold R_universe_instance in r |- *.
    eapply Forall2_symP; eauto.
    eapply onctx_eq_ctx_sym in a1; eauto.
    eapply All2_sym; solve_all.
    eapply onctx_eq_ctx_sym in a0; eauto.
  -
 econstructor.
    eapply All2_All_mix_left in X as h; eauto.
    clear a X.
    induction h.
    +
 constructor.
    +
 destruct r as [[h1 h2] [[[h3 h4] h5] h6]].
      eapply h1 in h3; auto.
constructor; auto.
  -
 econstructor.
    eapply All2_All_mix_left in X as h; eauto.
    clear a X.
    induction h.
    +
 constructor.
    +
 destruct r as [[h1 h2] [[[h3 h4] h5] h6]].
eapply h1 in h3 ; auto.
    constructor; auto.
Qed.

#[global]
Polymorphic Instance eq_predicate_sym Re Ru :
  CRelationClasses.Symmetric Re ->
  RelationClasses.Symmetric Ru ->
  CRelationClasses.Symmetric (eq_predicate Re Ru).
Proof.
  intros hre hru.
  intros p.
unfold eq_predicate; intuition auto; try now symmetry.
Qed.

#[global]
Instance compare_term_sym {cf} Σ φ : Symmetric (compare_term Conv Σ φ).
Proof.
  now intros t u; unfold compare_term; cbn; symmetry.
Qed.

#[global]
Instance R_global_instance_trans Σ Re Rle gr napp :
  RelationClasses.Transitive Re ->
  RelationClasses.Transitive Rle ->
  RelationClasses.Transitive (R_global_instance Σ Re Rle gr napp).
Proof.
  intros he hle x y z.
  unfold R_global_instance_gen, R_opt_variance.
  destruct global_variance_gen as [v|].
  clear -he hle.
  induction x in y, z, v |- *; destruct y, z, v; simpl; auto => //.
eauto.
  intros [Ra Rxy] [Rt Ryz].
  split; eauto.
  destruct t1; simpl in *; auto.
  now etransitivity; eauto.
  now etransitivity; eauto.
  eapply Forall2_trans; auto.
Qed.

Lemma onctx_eq_ctx_trans P ctx ctx' ctx'' eq_term :
  onctx P ctx ->
  (forall x, P x -> forall y z, eq_term x y -> eq_term y z -> eq_term x z) ->
  All2_fold (fun _ _ => compare_decls eq_term eq_term) ctx ctx' ->
  All2_fold (fun _ _ => compare_decls eq_term eq_term) ctx' ctx'' ->
  All2_fold (fun _ _ => compare_decls eq_term eq_term) ctx ctx''.
Proof.
  intros onc HP H1; revert ctx''.
  induction H1; depelim onc; intros ctx'' H; depelim H; constructor; intuition auto; simpl in *.
  depelim o.
depelim p0.
  -
 depelim c; constructor; [now etransitivity|eauto].
  -
 depelim c; constructor; [now etransitivity|eauto ..].
Qed.

#[global]
Polymorphic Instance eq_predicate_trans Re Ru :
  CRelationClasses.Transitive Re ->
  RelationClasses.Transitive Ru ->
  CRelationClasses.Transitive (eq_predicate Re Ru).
Proof.
  intros hre hru.
  intros p.
unfold eq_predicate; intuition auto; try now etransitivity.
  eapply All2_trans; tea.
  etransitivity; tea.
Qed.

#[global]
Polymorphic Instance eq_term_upto_univ_trans Σ Re Rle napp :
  RelationClasses.Transitive Re ->
  RelationClasses.Transitive Rle ->
  Transitive (eq_term_upto_univ_napp Σ Re Rle napp).
Proof.
  intros he hle u v w e1 e2.
  pose proof (@RelationClasses.transitivity _ (@eq_binder_annot name name) _).
  induction u in Rle, hle, v, w, napp, e1, e2 |- * using term_forall_list_ind.
  all: dependent destruction e1.
  all: try solve [ eauto ].
  all: try solve [
    dependent destruction e2 ; econstructor ; eauto;
    try eapply Forall2_trans ; eauto
  ].
  -
 dependent destruction e2.
    econstructor.
    eapply All2_All_mix_left in X as h; eauto.
    clear a X.
    induction h in a0, args'0 |- *.
    +
 assumption.
    +
 dependent destruction a0.
constructor ; eauto.
      destruct r as [h1 h2].
eauto.
  -
 dependent destruction e2.
    constructor.
    eapply R_global_instance_trans; eauto.
  -
 dependent destruction e2.
    constructor.
    eapply R_global_instance_trans; eauto.
  -
 dependent destruction e2.
    unfold eq_predicate in *.
    !!solve_all.
    econstructor; unfold eq_predicate in *; solve_all; eauto.
    *
 clear -he hh1 hh2.
      revert hh1 hh2.
generalize (pparams p), p'.(pparams), p'0.(pparams).
      intros l l' l''.
      induction 1 in l'' |- *; auto.
intros H; depelim H.
constructor; auto.
      eapply r; eauto.
apply r.
    *
 etransitivity; eauto.
    *
 eapply onctx_eq_ctx_trans in hh; eauto.
      intros ???? -> ->; eauto.
    *
 clear -H he a a0.
      induction a in a0, brs'0 |- *.
      +
 assumption.
      +
 depelim a0.
destruct p.
constructor; auto.
        destruct r as [[h1 h1'] [h2 h3]].
        split.
        eapply onctx_eq_ctx_trans in h1; eauto.
        intros ???? -> ->;reflexivity.
        eapply h1'; eauto.
  -
 dependent destruction e2.
    econstructor.
    eapply All2_All_mix_left in X as h; eauto.
    clear a X.
    induction h in a0, mfix'0 |- *.
    +
 assumption.
    +
 dependent destruction a0.
constructor ; eauto.
      intuition eauto.
      transitivity (rarg y); auto.
  -
 dependent destruction e2.
    econstructor.
    eapply All2_All_mix_left in X as h; eauto.
    clear a X.
    induction h in a0, mfix'0 |- *.
    +
 assumption.
    +
 dependent destruction a0.
constructor ; eauto.
      intuition eauto.
      transitivity (rarg y); auto.
Qed.

#[global]
Instance compare_term_trans {cf} pb Σ φ : Transitive (compare_term pb Σ φ).
Proof.
apply eq_term_upto_univ_trans; tc.
Qed.

#[global]
Polymorphic Instance eq_term_upto_univ_equiv Σ Re (hRe : RelationClasses.Equivalence Re)
  : Equivalence (eq_term_upto_univ Σ Re Re).
Proof.
  constructor.
all: exact _.
Defined.

#[global]
Polymorphic Instance eq_context_equiv {cf} Σ φ : Equivalence (eq_context_gen (eq_term Σ φ) (eq_term Σ φ)).
Proof.
  constructor; try exact _.
Qed.

#[global]
Polymorphic Instance leq_context_preord {cf} Σ φ : PreOrder (eq_context_gen (eq_term Σ φ) (leq_term Σ φ)).
Proof.
  constructor; try exact _.
Qed.

#[global]
Polymorphic Instance eq_term_equiv {cf:checker_flags} Σ φ : Equivalence (eq_term Σ φ).
Proof.
split; tc.
Qed.

#[global]
Polymorphic Instance leq_term_preorder {cf:checker_flags} Σ φ : PreOrder (leq_term Σ φ).
Proof.
split; tc.
Qed.

#[global]
Instance R_universe_instance_equiv R (hR : RelationClasses.Equivalence R)
  : RelationClasses.Equivalence (R_universe_instance R).
Proof.
  split.
  -
 intro.
apply Forall2_same.
reflexivity.
  -
 intros x y xy.
eapply Forall2_sym, Forall2_impl; tea.
now symmetry.
  -
 intros x y z xy yz.
eapply Forall2_trans; tea.
apply hR.
Qed.

Lemma R_universe_instance_antisym Re Rle (hRe : RelationClasses.Equivalence Re) :
  RelationClasses.Antisymmetric _ Re Rle ->
  RelationClasses.Antisymmetric _ (R_universe_instance Re) (R_universe_instance Rle).
Proof.
  intros H x y H1 H2.
  eapply Forall2_sym in H2.
  eapply Forall2_impl; [eapply Forall2_and|]; [exact H1|exact H2|].
  cbn; intros ? ? [? ?].
eapply H; assumption.
Qed.

#[global]
Instance R_global_instance_equiv Σ R (hR : RelationClasses.Equivalence R) gr napp
  : RelationClasses.Equivalence (R_global_instance Σ R R gr napp).
Proof.
  split.
  -
 intro.
apply R_global_instance_refl; typeclasses eauto.
  -
 intros x y xy.
eapply R_global_instance_sym; auto; typeclasses eauto.
  -
 intros x y z xy yz.
eapply R_global_instance_trans; eauto; typeclasses eauto.
Qed.

#[global]
Instance R_global_instance_antisym Σ Re Rle (hRe : RelationClasses.Equivalence Re) gr napp :
  RelationClasses.Antisymmetric _ Re Rle ->
  RelationClasses.Antisymmetric _ (R_global_instance Σ Re Re gr napp) (R_global_instance Σ Re Rle gr napp).
Proof.
  intros hR u v.
  unfold R_global_instance_gen, R_opt_variance.
  destruct global_variance_gen; auto.
  induction u in l, v |- *; destruct v, l; simpl; auto.
  intros [at' uv] [ta vu].
split; auto.
  destruct t0; simpl in *; auto.
Qed.

Lemma eq_term_upto_univ_antisym Σ Re Rle (hRe : RelationClasses.Equivalence Re) :
  RelationClasses.Antisymmetric _ Re Rle ->
  Antisymmetric (eq_term_upto_univ Σ Re Re) (eq_term_upto_univ Σ Re Rle).
Proof.
  intros hR u v.
generalize 0; intros n h h'.
  induction u in v, n, h, h' |- * using term_forall_list_ind.
  all: simpl ; inversion h ; subst; inversion h' ;
       subst ; try constructor ; auto.
  all: eapply RelationClasses.antisymmetry; eauto.
Qed.

#[global]
Instance leq_term_antisym {cf:checker_flags} Σ φ
  : Antisymmetric (eq_term Σ φ) (leq_term Σ φ).
Proof.
  eapply eq_term_upto_univ_antisym; exact _.
Qed.

Lemma global_variance_napp_mon {Σ gr napp napp' v} :
  napp <= napp' ->
  global_variance Σ gr napp = Some v ->
  global_variance Σ gr napp' = Some v.
Proof.
  intros hnapp.
  rewrite /global_variance_gen.
  destruct gr; try congruence.
  -
 destruct lookup_inductive_gen as [[mdecl idec]|] => //.
    destruct destArity as [[ctx s]|] => //.
    elim: Nat.leb_spec => // cass indv.
    elim: Nat.leb_spec => //.
lia.
  -
 destruct lookup_constructor_gen as [[[mdecl idecl] cdecl]|] => //.
    elim: Nat.leb_spec => // cass indv.
    elim: Nat.leb_spec => //.
lia.
Qed.

#[global]
Instance R_global_instance_impl_same_napp Σ Re Re' Rle Rle' gr napp :
  RelationClasses.subrelation Re Re' ->
  RelationClasses.subrelation Rle Rle' ->
  subrelation (R_global_instance Σ Re Rle gr napp) (R_global_instance Σ Re' Rle' gr napp).
Proof.
  intros he hle t t'.
  unfold R_global_instance_gen, R_opt_variance.
  destruct global_variance_gen as [v|] eqn:glob.
  induction t in v, t' |- *; destruct v, t'; simpl; auto.
  intros []; split; auto.
  destruct t0; simpl; auto.
  now eapply R_universe_instance_impl'.
Qed.

#[global]
Instance R_global_instance_impl Σ Re Re' Rle Rle' gr napp napp' :
  RelationClasses.subrelation Re Re' ->
  RelationClasses.subrelation Re Rle' ->
  RelationClasses.subrelation Rle Rle' ->
  napp <= napp' ->
  subrelation (R_global_instance Σ Re Rle gr napp) (R_global_instance Σ Re' Rle' gr napp').
Proof.
  intros he hle hele hnapp t t'.
  unfold R_global_instance_gen, R_opt_variance.
  destruct global_variance_gen as [v|] eqn:glob.
  rewrite (global_variance_napp_mon hnapp glob).
  induction t in v, t' |- *; destruct v, t'; simpl; auto.
  intros []; split; auto.
  destruct t0; simpl; auto.
  destruct (global_variance _ _ napp') as [v|] eqn:glob'; eauto using R_universe_instance_impl'.
  induction t in v, t' |- *; destruct v, t'; simpl; auto; intros H; inv H.
  eauto.
  split; auto.
  destruct t0; simpl; auto.
Qed.

Lemma global_variance_empty gr napp env : env.(declarations) = [] -> global_variance env gr napp = None.
Proof.
  destruct env; cbn => ->.
destruct gr; auto.
Qed.

 

#[global]
Instance R_global_instance_empty_impl Σ Re Re' Rle Rle' gr napp napp' :
  RelationClasses.subrelation Re Re' ->
  RelationClasses.subrelation Rle Rle' ->
  RelationClasses.subrelation Re Rle' ->
  subrelation (R_global_instance empty_global_env Re Rle gr napp) (R_global_instance Σ Re' Rle' gr napp').
Proof.
  intros he hle hele t t'.
  unfold R_global_instance_gen, R_opt_variance.
  rewrite global_variance_empty //.
  destruct global_variance_gen as [v|]; eauto using R_universe_instance_impl'.
  induction t in v, t' |- *; destruct v, t'; simpl; intros H; inv H; auto.
  simpl.
  split; auto.
  destruct t0; simpl; auto.
Qed.

Lemma onctx_eq_ctx_impl P ctx ctx' eq_term eq_term' :
  onctx P ctx ->
  (forall x, P x -> forall y, eq_term x y -> eq_term' x y) ->
  eq_context_gen eq_term eq_term ctx ctx' ->
  eq_context_gen eq_term' eq_term' ctx ctx'.
Proof.
  intros onc HP H1.
  induction H1; depelim onc; constructor; eauto; intuition auto; simpl in *.
  destruct o; depelim p; constructor; auto.
Qed.

#[global]
Instance eq_term_upto_univ_impl Σ Re Re' Rle Rle' napp napp' :
  RelationClasses.subrelation Re Re' ->
  RelationClasses.subrelation Rle Rle' ->
  RelationClasses.subrelation Re Rle' ->
  napp <= napp' ->
  subrelation (eq_term_upto_univ_napp Σ Re Rle napp) (eq_term_upto_univ_napp Σ Re' Rle' napp').
Proof.
  intros he hle hele hnapp t t'.
  induction t in napp, napp', hnapp, t', Rle, Rle', hle, hele |- * using term_forall_list_ind;
    try (inversion 1; subst; constructor;
         eauto using R_universe_instance_impl'; fail).
  -
 inversion 1; subst; constructor.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
  -
 inversion 1; subst; constructor.
    eapply IHt1.
4:eauto.
all:auto with arith.
eauto.
  -
 inversion 1; subst; constructor.
    eapply R_global_instance_impl.
5:eauto.
all:auto.
  -
 inversion 1; subst; constructor.
    eapply R_global_instance_impl.
5:eauto.
all:eauto.
  -
 inversion 1; subst; constructor; unfold eq_predicate in *; eauto; solve_all.
    *
 eapply R_universe_instance_impl'; eauto.
  -
 inversion 1; subst; constructor.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
    cbn.
intros x [? ?] y [[[? ?] ?] ?].
repeat split; eauto.
  -
 inversion 1; subst; constructor.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
    cbn.
intros x [? ?] y [[[? ?] ?] ?].
repeat split; eauto.
Qed.

#[global]
Instance eq_term_upto_univ_empty_impl Σ Re Re' Rle Rle' napp napp' :
  RelationClasses.subrelation Re Re' ->
  RelationClasses.subrelation Rle Rle' ->
  RelationClasses.subrelation Re Rle' ->
  subrelation (eq_term_upto_univ_napp empty_global_env Re Rle napp) (eq_term_upto_univ_napp Σ Re' Rle' napp').
Proof.
  intros he hle hele t t'.
  induction t in napp, napp', t', Rle, Rle', hle, hele |- * using term_forall_list_ind;
    try (inversion 1; subst; constructor;
         eauto using R_universe_instance_impl'; fail).
  -
 inversion 1; subst; constructor.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
  -
 inversion 1; subst; constructor.
     
    eapply R_global_instance_empty_impl.
4:eauto.
all:eauto.
  -
 inversion 1; subst; constructor.
    eapply R_global_instance_empty_impl.
4:eauto.
all:eauto.
  -
 inversion 1; subst; constructor; unfold eq_predicate in *; solve_all.
    *
 eapply R_universe_instance_impl'; eauto.
  -
 inversion 1; subst; constructor.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
    cbn.
intros x [? ?] y [[[? ?] ?] ?].
repeat split; eauto.
  -
 inversion 1; subst; constructor.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
    cbn.
intros x [? ?] y [[[? ?] ?] ?].
repeat split; eauto.
Qed.

#[global]
Instance eq_term_upto_univ_leq Σ Re Rle napp napp' :
  RelationClasses.subrelation Re Rle ->
  napp <= napp' ->
  subrelation (eq_term_upto_univ_napp Σ Re Re napp) (eq_term_upto_univ_napp Σ Re Rle napp').
Proof.
  intros H.
eapply eq_term_upto_univ_impl; exact _.
Qed.

#[global]
Instance eq_term_leq_term {cf:checker_flags} Σ φ
  : subrelation (eq_term Σ φ) (leq_term Σ φ).
Admitted.

#[global]
Instance leq_term_partial_order {cf:checker_flags} Σ φ
  : PartialOrder (eq_term Σ φ) (leq_term Σ φ).
Admitted.

#[global]
Hint Constructors compare_decls : pcuic.

Local Ltac lih :=
  lazymatch goal with
  | ih : forall Rle v n k, eq_term_upto_univ_napp _ _ _ ?u _ -> _
    |- eq_term_upto_univ _ _ (lift _ _ ?u) _ =>
    eapply ih
  end.

Lemma eq_term_upto_univ_lift Σ Re Rle n n' k :
  Proper (eq_term_upto_univ_napp Σ Re Rle n' ==> eq_term_upto_univ_napp Σ Re Rle n') (lift n k).
Admitted.

Lemma lift_compare_term `{checker_flags} pb Σ ϕ n k t t' :
  compare_term pb Σ ϕ t t' -> compare_term pb Σ ϕ (lift n k t) (lift n k t').
Admitted.

Lemma lift_compare_decls `{checker_flags} pb Σ ϕ n k d d' :
  compare_decl pb Σ ϕ d d' -> compare_decl pb Σ ϕ (lift_decl n k d) (lift_decl n k d').
Admitted.

Lemma lift_compare_context `{checker_flags} pb Σ φ l l' n k :
  compare_context pb Σ φ l l' ->
  compare_context pb Σ φ (lift_context n k l) (lift_context n k l').
Admitted.

Lemma lift_eq_term {cf:checker_flags} Σ φ n k T U :
  eq_term Σ φ T U -> eq_term Σ φ (lift n k T) (lift n k U).
Admitted.

Lemma lift_leq_term {cf:checker_flags} Σ φ n k T U :
  leq_term Σ φ T U -> leq_term Σ φ (lift n k T) (lift n k U).
Admitted.

Local Ltac sih :=
  lazymatch goal with
  | ih : forall Rle v n x y, _ -> eq_term_upto_univ _ _ ?u _ -> _ -> _
    |- eq_term_upto_univ _ _ (subst _ _ ?u) _ => eapply ih
  end.

Lemma eq_term_upto_univ_substs Σ Re Rle napp :
  RelationClasses.subrelation Re Rle ->
  forall u v n l l',
    eq_term_upto_univ_napp Σ Re Rle napp u v ->
    All2 (eq_term_upto_univ Σ Re Re) l l' ->
    eq_term_upto_univ_napp Σ Re Rle napp (subst l n u) (subst l' n v).
Admitted.

Lemma eq_term_upto_univ_subst Σ Re Rle :
  RelationClasses.subrelation Re Rle ->
  forall u v n x y,
    eq_term_upto_univ Σ Re Rle u v ->
    eq_term_upto_univ Σ Re Re x y ->
    eq_term_upto_univ Σ Re Rle (u{n := x}) (v{n := y}).
Admitted.

Lemma subst_eq_term {cf:checker_flags} Σ φ l k T U :
  eq_term Σ φ T U ->
  eq_term Σ φ (subst l k T) (subst l k U).
Admitted.

Lemma subst_leq_term {cf:checker_flags} Σ φ l k T U :
  leq_term Σ φ T U ->
  leq_term Σ φ (subst l k T) (subst l k U).
Admitted.

 

Lemma eq_term_eq_term_napp Σ Re Rle napp t t' :
  RelationClasses.subrelation Re Rle ->
  eq_term_upto_univ Σ Re Rle t t' ->
  eq_term_upto_univ_napp Σ Re Rle napp t t'.
Admitted.

Lemma leq_term_leq_term_napp Σ Re Rle napp t t' :
  RelationClasses.subrelation Re Rle ->
  eq_term_upto_univ Σ Re Rle t t' ->
  eq_term_upto_univ_napp Σ Re Rle napp t t'.
Admitted.

Lemma eq_term_upto_univ_napp_mkApps Σ Re Rle u1 l1 u2 l2 napp :
    eq_term_upto_univ_napp Σ Re Rle (#|l1| + napp) u1 u2 ->
    All2 (eq_term_upto_univ Σ Re Re) l1 l2 ->
    eq_term_upto_univ_napp Σ Re Rle napp (mkApps u1 l1) (mkApps u2 l2).
Admitted.

Lemma eq_term_upto_univ_napp_mkApps_l_inv Σ Re Rle napp u l t :
    eq_term_upto_univ_napp Σ Re Rle napp (mkApps u l) t ->
    ∑ u' l',
      eq_term_upto_univ_napp Σ Re Rle (#|l| + napp) u u' *
      All2 (eq_term_upto_univ Σ Re Re) l l' *
      (t = mkApps u' l').
Admitted.

Lemma eq_term_upto_univ_napp_mkApps_r_inv Σ Re Rle napp u l t :
    eq_term_upto_univ_napp Σ Re Rle napp t (mkApps u l) ->
    ∑ u' l',
      eq_term_upto_univ_napp Σ Re Rle (#|l| + napp) u' u *
      All2 (eq_term_upto_univ Σ Re Re) l' l *
      (t = mkApps u' l').
Admitted.

Lemma eq_term_upto_univ_mkApps Σ Re Rle u1 l1 u2 l2 :
    eq_term_upto_univ_napp Σ Re Rle #|l1| u1 u2 ->
    All2 (eq_term_upto_univ Σ Re Re) l1 l2 ->
    eq_term_upto_univ Σ Re Rle (mkApps u1 l1) (mkApps u2 l2).
Admitted.

Lemma eq_term_upto_univ_mkApps_l_inv Σ Re Rle u l t :
    eq_term_upto_univ Σ Re Rle (mkApps u l) t ->
    ∑ u' l',
      eq_term_upto_univ_napp Σ Re Rle #|l| u u' *
      All2 (eq_term_upto_univ Σ Re Re) l l' *
      (t = mkApps u' l').
Admitted.

Lemma eq_term_upto_univ_mkApps_r_inv Σ Re Rle u l t :
    eq_term_upto_univ Σ Re Rle t (mkApps u l) ->
    ∑ u' l',
      eq_term_upto_univ_napp Σ Re Rle #|l| u' u *
      All2 (eq_term_upto_univ Σ Re Re) l' l *
      (t = mkApps u' l').
Admitted.

Lemma R_universe_instance_eq {u u'} : R_universe_instance eq u u' -> u = u'.
Admitted.

Lemma valid_constraints_empty {cf} i :
  valid_constraints (empty_ext empty_global_env) (subst_instance_cstrs i (empty_ext empty_global_env)).
Admitted.

Lemma upto_eq_impl Σ Re Rle :
  RelationClasses.Reflexive Re ->
  RelationClasses.Reflexive Rle ->
  subrelation (eq_term_upto_univ Σ eq eq) (eq_term_upto_univ Σ Re Rle).
Admitted.

 

Definition upto_names := eq_term_upto_univ empty_global_env eq eq.

Infix "≡" := upto_names (at level 70).

Infix "≡'" := (eq_term_upto_univ empty_global_env eq eq) (at level 70).
Notation upto_names' := (eq_term_upto_univ empty_global_env eq eq).

#[global]
Instance upto_names_ref : Reflexive upto_names.
Admitted.

#[global]
Instance upto_names_sym : Symmetric upto_names.
Admitted.

#[global]
Instance upto_names_trans : Transitive upto_names.
Admitted.

 
 
 

 
 
 
 
 
 

Lemma upto_names_impl Σ Re Rle :
  RelationClasses.Reflexive Re ->
  RelationClasses.Reflexive Rle ->
  subrelation upto_names (eq_term_upto_univ Σ Re Rle).
Admitted.

Lemma upto_names_impl_eq_term {cf:checker_flags} Σ φ u v :
    u ≡ v -> eq_term Σ φ u v.
Admitted.

Lemma upto_names_impl_leq_term {cf:checker_flags} Σ φ u v :
    u ≡ v -> leq_term Σ φ u v.
Admitted.

Lemma eq_term_upto_univ_isApp Σ Re Rle napp u v :
  eq_term_upto_univ_napp Σ Re Rle napp u v ->
  isApp u = isApp v.
Admitted.

 

Inductive rel_option {A B} (R : A -> B -> Type) : option A -> option B -> Type :=
| rel_some : forall a b, R a b -> rel_option R (Some a) (Some b)
| rel_none : rel_option R None None.

Derive Signature NoConfusion for rel_option.

Definition eq_decl_upto_gen Σ Re Rle d d' : Type :=
  eq_binder_annot d.(decl_name) d'.(decl_name) *
  rel_option (eq_term_upto_univ Σ Re Re) d.(decl_body) d'.(decl_body) *
  eq_term_upto_univ Σ Re Rle d.(decl_type) d'.(decl_type).

 
Lemma All2_eq_context_upto Σ Re Rle :
  subrelation (All2 (eq_decl_upto_gen Σ Re Rle)) (eq_context_upto Σ Re Rle).
Admitted.

Lemma eq_context_upto_refl Σ Re Rle :
  RelationClasses.Reflexive Re ->
  RelationClasses.Reflexive Rle ->
  Reflexive (eq_context_upto Σ Re Rle).
Admitted.

Lemma eq_context_upto_sym Σ Re Rle :
  RelationClasses.Symmetric Re ->
  RelationClasses.Symmetric Rle ->
  Symmetric (eq_context_upto Σ Re Rle).
Admitted.

Lemma eq_context_upto_cat Σ Re Rle Γ Δ Γ' Δ' :
  eq_context_upto Σ Re Rle Γ Γ' ->
  eq_context_upto Σ Re Rle Δ Δ' ->
  eq_context_upto Σ Re Rle (Γ ,,, Δ) (Γ' ,,, Δ').
Admitted.

Lemma eq_context_upto_rev Σ Re Rle Γ Δ :
  eq_context_upto Σ Re Rle Γ Δ ->
  eq_context_upto Σ Re Rle (rev Γ) (rev Δ).
Admitted.

Lemma eq_context_upto_rev' :
  forall Σ Γ Δ Re Rle,
    eq_context_upto Σ Re Rle Γ Δ ->
    eq_context_upto Σ Re Rle (List.rev Γ) (List.rev Δ).
Admitted.

Lemma eq_context_upto_length :
  forall {Σ Re Rle Γ Δ},
    eq_context_upto Σ Re Rle Γ Δ ->
    #|Γ| = #|Δ|.
Admitted.

Lemma eq_context_upto_subst_context Σ Re Rle :
  RelationClasses.subrelation Re Rle ->
  forall u v n l l',
    eq_context_upto Σ Re Rle u v ->
    All2 (eq_term_upto_univ Σ Re Re) l l' ->
    eq_context_upto Σ Re Rle (subst_context l n u) (subst_context l' n v).
Admitted.

#[global]
Hint Resolve All2_fold_nil : pcuic.

Lemma eq_context_upto_smash_context Σ ctx ctx' x y :
  eq_context_upto Σ eq eq ctx ctx' -> eq_context_upto Σ eq eq x y ->
  eq_context_upto Σ eq eq (smash_context ctx x) (smash_context ctx' y).
Admitted.

Lemma eq_context_upto_nth_error Σ Re Rle ctx ctx' n :
  eq_context_upto Σ Re Rle ctx ctx' ->
  rel_option (eq_decl_upto_gen Σ Re Rle) (nth_error ctx n) (nth_error ctx' n).
Admitted.

Lemma eq_context_impl :
  forall Σ Re Re' Rle Rle',
    RelationClasses.subrelation Re Re' ->
    RelationClasses.subrelation Rle Rle' ->
    RelationClasses.subrelation Re' Rle' ->
    subrelation (eq_context_upto Σ Re Rle) (eq_context_upto Σ Re' Rle').
Admitted.

Lemma eq_term_upto_univ_it_mkLambda_or_LetIn Σ Re Rle :
    RelationClasses.Reflexive Re ->
    Proper (eq_context_upto Σ Re Re ==> eq_term_upto_univ Σ Re Rle ==> eq_term_upto_univ Σ Re Rle) it_mkLambda_or_LetIn.
Admitted.

Lemma eq_term_upto_univ_it_mkLambda_or_LetIn_r Σ Re Rle Γ :
  RelationClasses.Reflexive Re ->
  respectful (eq_term_upto_univ Σ Re Rle) (eq_term_upto_univ Σ Re Rle)
             (it_mkLambda_or_LetIn Γ) (it_mkLambda_or_LetIn Γ).
Admitted.

Lemma eq_term_it_mkLambda_or_LetIn {cf:checker_flags} Σ φ Γ :
  respectful (eq_term Σ φ) (eq_term Σ φ)
             (it_mkLambda_or_LetIn Γ) (it_mkLambda_or_LetIn Γ).
Admitted.

Lemma eq_term_upto_univ_it_mkProd_or_LetIn Σ Re Rle Γ :
  RelationClasses.Reflexive Re ->
  respectful (eq_term_upto_univ Σ Re Rle) (eq_term_upto_univ Σ Re Rle)
             (it_mkProd_or_LetIn Γ) (it_mkProd_or_LetIn Γ).
Admitted.

Lemma eq_term_it_mkProd_or_LetIn {cf:checker_flags} Σ φ Γ:
  respectful (eq_term Σ φ) (eq_term Σ φ)
             (it_mkProd_or_LetIn Γ) (it_mkProd_or_LetIn Γ).
Admitted.

Lemma eq_term_it_mkLambda_or_LetIn_inv {cf:checker_flags} Σ φ Γ u v :
    eq_term Σ φ (it_mkLambda_or_LetIn Γ u) (it_mkLambda_or_LetIn Γ v) ->
    eq_term Σ  φ u v.
Admitted.

Lemma eq_term_upto_univ_mkApps_inv Σ Re Rle u l u' l' :
  isApp u = false ->
  isApp u' = false ->
  eq_term_upto_univ Σ Re Rle (mkApps u l) (mkApps u' l') ->
  eq_term_upto_univ_napp Σ Re Rle #|l| u u' * All2 (eq_term_upto_univ Σ Re Re) l l'.
Admitted.

Lemma isLambda_eq_term_l Σ Re u v :
    isLambda u ->
    eq_term_upto_univ Σ Re Re u v ->
    isLambda v.
Admitted.

Lemma isLambda_eq_term_r Σ Re u v :
    isLambda v ->
    eq_term_upto_univ Σ Re Re u v ->
    isLambda u.
Admitted.

Lemma isConstruct_app_eq_term_l Σ Re u v :
    isConstruct_app u ->
    eq_term_upto_univ Σ Re Re u v ->
    isConstruct_app v.
Admitted.

Lemma isConstruct_app_eq_term_r :
  forall Σ Re u v,
    isConstruct_app v ->
    eq_term_upto_univ Σ Re Re u v ->
    isConstruct_app u.
Admitted.

Lemma R_global_instance_flip Σ gr napp
  (Re Rle Rle' : Universe.t -> Universe.t -> Prop) u v:
  RelationClasses.Reflexive Re ->
  RelationClasses.Reflexive Rle ->
  RelationClasses.Symmetric Re ->
  RelationClasses.Transitive Re ->
  RelationClasses.Transitive Rle ->
  RelationClasses.subrelation Re Rle ->
  (forall x y, Rle x y -> Rle' y x) ->
  R_global_instance Σ Re Rle gr napp u v ->
  R_global_instance Σ Re Rle' gr napp v u.
Admitted.

Lemma eq_term_upto_univ_napp_flip Σ (Re Rle Rle' : Universe.t -> Universe.t -> Prop) napp u v :
  RelationClasses.Reflexive Re ->
  RelationClasses.Reflexive Rle ->
  RelationClasses.Symmetric Re ->
  RelationClasses.Transitive Re ->
  RelationClasses.Transitive Rle ->
  RelationClasses.subrelation Re Rle ->
  (forall x y, Rle x y -> Rle' y x) ->
  eq_term_upto_univ_napp Σ Re Rle napp u v ->
  eq_term_upto_univ_napp Σ Re Rle' napp v u.
Admitted.

Lemma eq_univ_make :
  forall u u',
    Forall2 eq (map Universe.make u) (map Universe.make u') ->
    u = u'.
Admitted.

 
Notation eq_annots Γ Δ :=
  (Forall2 (fun na decl => eq_binder_annot na (decl_name decl)) Γ Δ).

Lemma eq_context_gen_binder_annot Γ Δ :
  eq_context_gen eq eq Γ Δ -> eq_annots (forget_types Γ) Δ.
Admitted.

Lemma eq_annots_fold (Γ : list aname) (f : nat -> term -> term) (Δ : context) :
  eq_annots Γ (fold_context_k f Δ) <-> eq_annots Γ Δ.
Admitted.

Lemma eq_annots_subst_context (Γ : list aname) s k (Δ : context) :
  eq_annots Γ (subst_context s k Δ) <-> eq_annots Γ Δ.
Admitted.

Lemma eq_annots_lift_context (Γ : list aname) n k (Δ : context) :
  eq_annots Γ (lift_context n k Δ) <-> eq_annots Γ Δ.
Admitted.

#[global]
Instance Forall2_ext {A B} :
  Proper (pointwise_relation A (pointwise_relation B iff) ==> eq ==> eq ==> iff) (@Forall2 A B).
Admitted.

Lemma eq_annots_subst_instance_ctx (Γ : list aname) u (Δ : context) :
  eq_annots Γ Δ@[u] <-> eq_annots Γ Δ.
Admitted.

Lemma eq_annots_inst_case_context (Γ : list aname) pars puinst (ctx : context) :
  eq_annots Γ ctx <->
  eq_annots Γ (PCUICCases.inst_case_context pars puinst ctx).
Admitted.

End PCUICEquality.

End MetaCoq_DOT_PCUIC_DOT_PCUICEquality_WRAPPED.
Module Export MetaCoq_DOT_PCUIC_DOT_PCUICEquality.
Module Export MetaCoq.
Module Export PCUIC.
Module PCUICEquality.
Include MetaCoq_DOT_PCUIC_DOT_PCUICEquality_WRAPPED.PCUICEquality.
End PCUICEquality.

End PCUIC.

End MetaCoq.

End MetaCoq_DOT_PCUIC_DOT_PCUICEquality.

Import MetaCoq.Utils.utils.
Import MetaCoq.PCUIC.PCUICAst.
Import MetaCoq.PCUIC.utils.PCUICOnOne.
Import MetaCoq.PCUIC.Syntax.PCUICCases.

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

Import MetaCoq.Common.config.
Import MetaCoq.PCUIC.PCUICEquality.

Reserved Notation " Σ ;;; Γ |- t <=[ pb ] u" (at level 50, Γ, t, u at next level,
  format "Σ  ;;;  Γ  |-  t  <=[ pb ] u").

Notation " Σ ⊢ t <===[ pb ] u" := (compare_term pb Σ Σ t u) (at level 50, t, u at next level).

Inductive cumulAlgo_gen `{checker_flags} (Σ : global_env_ext) (Γ : context) (pb : conv_pb) : term -> term -> Type :=
| cumul_refl t u : Σ ⊢ t <===[ pb ] u -> Σ ;;; Γ |- t <=[pb] u
| cumul_red_l t u v : Σ ;;; Γ |- t ⇝ v -> Σ ;;; Γ |- v <=[pb] u -> Σ ;;; Γ |- t <=[pb] u
| cumul_red_r t u v : Σ ;;; Γ |- t <=[pb] v -> Σ ;;; Γ |- u ⇝ v -> Σ ;;; Γ |- t <=[pb] u
where " Σ ;;; Γ |- t <=[ pb ] u " := (cumulAlgo_gen Σ Γ pb t u) : type_scope.
Notation " Σ ;;; Γ |- t <= u " := (cumulAlgo_gen Σ Γ Cumul t u) (at level 50, Γ, t, u at next level) : type_scope.

Import Coq.ssr.ssrbool.

Definition shiftnP k p i :=
  (i <? k) || p (i - k).
Fixpoint on_free_vars (p : nat -> bool) (t : term) : bool.
Admitted.

Definition on_free_vars_decl P d :=
  test_decl (on_free_vars P) d.

Definition on_free_vars_ctx P ctx :=
  alli (fun k => (on_free_vars_decl (shiftnP k P))) 0 (List.rev ctx).

Notation is_open_term Γ := (on_free_vars (shiftnP #|Γ| xpred0)).
Notation is_closed_context := (on_free_vars_ctx xpred0).
Module Export PCUICCumulativitySpec.

Implicit Types (cf : checker_flags).

Definition cumul_predicate (cumul : context -> term -> term -> Type) Γ Re p p' :=
  All2 (cumul Γ) p.(pparams) p'.(pparams) *
  (R_universe_instance Re p.(puinst) p'.(puinst) *
  ((eq_context_gen eq eq p.(pcontext) p'.(pcontext)) *
    cumul (Γ ,,, inst_case_predicate_context p) p.(preturn) p'.(preturn))).

Reserved Notation " Σ ;;; Γ ⊢ t ≤s[ pb ] u" (at level 50, Γ, t, u at next level,
  format "Σ  ;;;  Γ  ⊢  t  ≤s[ pb ]  u").

Definition cumul_Ind_univ {cf} (Σ : global_env_ext) pb i napp :=
  R_global_instance Σ (eq_universe Σ) (compare_universe pb Σ) (IndRef i) napp.

Definition cumul_Construct_univ {cf} (Σ : global_env_ext) pb  i k napp :=
  R_global_instance Σ (eq_universe Σ) (compare_universe pb Σ) (ConstructRef i k) napp.
Inductive cumulSpec0 {cf : checker_flags} (Σ : global_env_ext) Γ (pb : conv_pb) : term -> term -> Type :=

| cumul_Trans : forall t u v,
    is_closed_context Γ -> is_open_term Γ u ->
    Σ ;;; Γ ⊢ t ≤s[pb] u ->
    Σ ;;; Γ ⊢ u ≤s[pb] v ->
    Σ ;;; Γ ⊢ t ≤s[pb] v

| cumul_Sym : forall t u,
    Σ ;;; Γ ⊢ t ≤s[Conv] u ->
    Σ ;;; Γ ⊢ u ≤s[pb] t

| cumul_Refl : forall t,
    Σ ;;; Γ ⊢ t ≤s[pb] t

| cumul_Ind : forall i u u' args args',
    cumul_Ind_univ Σ pb i #|args| u u' ->
    All2 (fun t u => Σ ;;; Γ ⊢ t ≤s[Conv] u) args args' ->
    Σ ;;; Γ ⊢ mkApps (tInd i u) args ≤s[pb] mkApps (tInd i u') args'

| cumul_Construct : forall i k u u' args args',
    cumul_Construct_univ Σ pb i k #|args| u u' ->
    All2 (fun t u => Σ ;;; Γ ⊢ t ≤s[Conv] u) args args' ->
    Σ ;;; Γ ⊢ mkApps (tConstruct i k u) args ≤s[pb] mkApps (tConstruct i k u') args'

| cumul_Sort : forall s s',
    compare_universe pb Σ s s' ->
    Σ ;;; Γ ⊢ tSort s ≤s[pb] tSort s'

| cumul_Const : forall c u u',
    R_universe_instance (compare_universe Conv Σ) u u' ->
    Σ ;;; Γ ⊢ tConst c u ≤s[pb] tConst c u'

| cumul_Evar : forall e args args',
    All2 (fun t u => Σ ;;; Γ ⊢ t ≤s[Conv] u) args args' ->
    Σ ;;; Γ ⊢ tEvar e args ≤s[pb] tEvar e args'

| cumul_App : forall t t' u u',
    Σ ;;; Γ ⊢ t ≤s[pb] t' ->
    Σ ;;; Γ ⊢ u ≤s[Conv] u' ->
    Σ ;;; Γ ⊢ tApp t u ≤s[pb] tApp t' u'

| cumul_Lambda : forall na na' ty ty' t t',
    eq_binder_annot na na' ->
    Σ ;;; Γ ⊢ ty ≤s[Conv] ty' ->
    Σ ;;; Γ ,, vass na ty ⊢ t ≤s[pb] t' ->
    Σ ;;; Γ ⊢ tLambda na ty t ≤s[pb] tLambda na' ty' t'

| cumul_Prod : forall na na' a a' b b',
    eq_binder_annot na na' ->
    Σ ;;; Γ ⊢ a ≤s[Conv] a' ->
    Σ ;;; Γ ,, vass na a ⊢ b ≤s[pb] b' ->
    Σ ;;; Γ ⊢ tProd na a b ≤s[pb] tProd na' a' b'

| cumul_LetIn : forall na na' t t' ty ty' u u',
    eq_binder_annot na na' ->
    Σ ;;; Γ ⊢ t ≤s[Conv] t' ->
    Σ ;;; Γ ⊢ ty ≤s[Conv] ty' ->
    Σ ;;; Γ ,, vdef na t ty ⊢ u ≤s[pb] u' ->
    Σ ;;; Γ ⊢ tLetIn na t ty u ≤s[pb] tLetIn na' t' ty' u'

| cumul_Case indn : forall p p' c c' brs brs',
    cumul_predicate (fun Γ t u => Σ ;;; Γ ⊢ t ≤s[Conv] u) Γ (compare_universe Conv Σ) p p' ->
    Σ ;;; Γ ⊢ c ≤s[Conv] c' ->
    All2 (fun br br' =>
      eq_context_gen eq eq (bcontext br) (bcontext br') ×
      Σ ;;; Γ ,,, inst_case_branch_context p br ⊢ bbody br ≤s[Conv] bbody br'
    ) brs brs' ->
    Σ ;;; Γ ⊢ tCase indn p c brs ≤s[pb] tCase indn p' c' brs'

| cumul_Proj : forall p c c',
    Σ ;;; Γ ⊢ c ≤s[Conv] c' ->
    Σ ;;; Γ ⊢ tProj p c ≤s[pb] tProj p c'

| cumul_Fix : forall mfix mfix' idx,
    All2 (fun x y =>
      Σ ;;; Γ ⊢ x.(dtype) ≤s[Conv] y.(dtype) ×
      Σ ;;; Γ ,,, fix_context mfix ⊢ x.(dbody) ≤s[Conv] y.(dbody) ×
      (x.(rarg) = y.(rarg)) ×
      eq_binder_annot x.(dname) y.(dname)
    ) mfix mfix' ->
    Σ ;;; Γ ⊢ tFix mfix idx ≤s[pb] tFix mfix' idx

| cumul_CoFix : forall mfix mfix' idx,
    All2 (fun x y =>
      Σ ;;; Γ ⊢ x.(dtype) ≤s[Conv] y.(dtype) ×
      Σ ;;; Γ ,,, fix_context mfix ⊢ x.(dbody) ≤s[Conv] y.(dbody) ×
      (x.(rarg) = y.(rarg)) ×
      eq_binder_annot x.(dname) y.(dname)
    ) mfix mfix' ->
    Σ ;;; Γ ⊢ tCoFix mfix idx ≤s[pb] tCoFix mfix' idx

| cumul_beta : forall na t b a,
    Σ ;;; Γ ⊢ tApp (tLambda na t b) a ≤s[pb] b {0 := a}

| cumul_zeta : forall na b t b',
    Σ ;;; Γ ⊢ tLetIn na b t b' ≤s[pb] b' {0 := b}

| cumul_rel i body :
    option_map decl_body (nth_error Γ i) = Some (Some body) ->
    Σ ;;; Γ ⊢ tRel i ≤s[pb] lift0 (S i) body

| cumul_iota : forall ci c u args p brs br,
    nth_error brs c = Some br ->
    #|args| = (ci.(ci_npar) + context_assumptions br.(bcontext))%nat ->
    Σ ;;; Γ ⊢ tCase ci p (mkApps (tConstruct ci.(ci_ind) c u) args) brs  ≤s[pb] iota_red ci.(ci_npar) p args br

| cumul_fix : forall mfix idx args narg fn,
    unfold_fix mfix idx = Some (narg, fn) ->
    is_constructor narg args = true ->
    Σ ;;; Γ ⊢ mkApps (tFix mfix idx) args ≤s[pb] mkApps fn args

| cumul_cofix_case : forall ip p mfix idx args narg fn brs,
    unfold_cofix mfix idx = Some (narg, fn) ->
    Σ ;;; Γ ⊢ tCase ip p (mkApps (tCoFix mfix idx) args) brs ≤s[pb] tCase ip p (mkApps fn args) brs

| cumul_cofix_proj : forall p mfix idx args narg fn,
    unfold_cofix mfix idx = Some (narg, fn) ->
    Σ ;;; Γ ⊢ tProj p (mkApps (tCoFix mfix idx) args) ≤s[pb] tProj p (mkApps fn args)

| cumul_delta : forall c decl body (isdecl : declared_constant Σ c decl) u,
    decl.(cst_body) = Some body ->
    Σ ;;; Γ ⊢ tConst c u ≤s[pb] body@[u]

| cumul_proj : forall p args u arg,
    nth_error args (p.(proj_npars) + p.(proj_arg)) = Some arg ->
    Σ ;;; Γ ⊢ tProj p (mkApps (tConstruct p.(proj_ind) 0 u) args) ≤s[pb] arg

where " Σ ;;; Γ ⊢ t ≤s[ pb ] u " := (@cumulSpec0 _ Σ Γ pb t u) : type_scope.
Definition cumulSpec `{checker_flags} (Σ : global_env_ext) Γ := cumulSpec0 Σ Γ Cumul.

Notation " Σ ;;; Γ |- t <=s u " := (@cumulSpec _ Σ Γ t u) (at level 50, Γ, t, u at next level).

Module PCUICConversionParSpec <: EnvironmentTyping.ConversionParSig PCUICTerm PCUICEnvironment PCUICTermUtils PCUICEnvTyping.
  Definition cumul_gen := @cumulSpec0.
End PCUICConversionParSpec.

End PCUICCumulativitySpec.
Module Export PCUICTyping.
Import MetaCoq.PCUIC.utils.PCUICAstUtils.

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

Definition type_of_constructor mdecl (cdecl : constructor_body) (c : inductive * nat) (u : list Level.t) :=
  let mind := inductive_mind (fst c) in
  subst0 (inds mind u mdecl.(ind_bodies)) (subst_instance u (cstr_type cdecl)).

Include PCUICEnvTyping.

Inductive FixCoFix : Type := Fix | CoFix.

Class GuardChecker :=
{
  guard : FixCoFix -> global_env_ext -> context -> mfixpoint term -> Prop ;
}.

Axiom guard_checking : GuardChecker.
#[global]
Existing Instance guard_checking.

Definition fix_guard := guard Fix.
Definition cofix_guard := guard CoFix.

Definition destInd (t : term) :=
  match t with
  | tInd ind u => Some (ind, u)
  | _ => None
  end.

Definition isCoFinite (r : recursivity_kind) :=
  match r with
  | CoFinite => true
  | _ => false
  end.

Definition check_recursivity_kind
  (lookup: kername -> option global_decl) ind r :=
  match lookup ind with
  | Some (InductiveDecl mib) => ReflectEq.eqb mib.(ind_finite) r
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

Definition wf_fixpoint_gen
  (lookup: kername -> option global_decl) mfix :=
  forallb (isLambda ∘ dbody) mfix &&
  let checks := map check_one_fix mfix in
  match map_option_out checks with
  | Some (ind :: inds) =>

    forallb (eqb ind) inds &&
    check_recursivity_kind lookup ind Finite
  | _ => false
  end.

Definition wf_fixpoint (Σ : global_env) := wf_fixpoint_gen (lookup_env Σ).

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

Definition wf_cofixpoint_gen
  (lookup: kername -> option global_decl) mfix :=
  let checks := map check_one_cofix mfix in
  match map_option_out checks with
  | Some (ind :: inds) =>

    forallb (eqb ind) inds &&
    check_recursivity_kind lookup ind CoFinite
  | _ => false
  end.

Definition wf_cofixpoint (Σ : global_env) := wf_cofixpoint_gen (lookup_env Σ).

Reserved Notation "'wf_local' Σ Γ " (at level 9, Σ, Γ at next level).

Reserved Notation " Σ ;;; Γ |- t : T " (at level 50, Γ, t, T at next level).

Variant case_side_conditions `{checker_flags} wf_local_fun typing Σ Γ ci p ps mdecl idecl indices predctx :=
| case_side_info
    (eq_npars : mdecl.(ind_npars) = ci.(ci_npar))
    (wf_pred : wf_predicate mdecl idecl p)
    (cons : consistent_instance_ext Σ (ind_universes mdecl) p.(puinst))
    (wf_pctx : wf_local_fun Σ (Γ ,,, predctx))

    (conv_pctx : eq_context_upto_names p.(pcontext) (ind_predicate_context ci.(ci_ind) mdecl idecl))
    (allowed_elim : is_allowed_elimination Σ idecl.(ind_kelim) ps)
    (ind_inst : ctx_inst typing Σ Γ (p.(pparams) ++ indices)
                         (List.rev (subst_instance p.(puinst)
                                                   (ind_params mdecl ,,, ind_indices idecl))))
    (not_cofinite : isCoFinite mdecl.(ind_finite) = false).

Variant case_branch_typing `{checker_flags} wf_local_fun typing Σ Γ (ci:case_info) p ps mdecl idecl ptm  brs :=
| case_branch_info
    (wf_brs : wf_branches idecl brs)
    (brs_ty :
       All2i (fun i cdecl br =>

                eq_context_upto_names br.(bcontext) (cstr_branch_context ci mdecl cdecl) ×
                let brctxty := case_branch_type ci.(ci_ind) mdecl idecl p br ptm i cdecl in
                (wf_local_fun Σ (Γ ,,, brctxty.1) ×
                ((typing Σ (Γ ,,, brctxty.1) br.(bbody) (brctxty.2)) ×
                (typing Σ (Γ ,,, brctxty.1) brctxty.2 (tSort ps)))))
             0 idecl.(ind_ctors) brs).

Inductive typing `{checker_flags} (Σ : global_env_ext) (Γ : context) : term -> term -> Type :=
| type_Rel : forall n decl,
    wf_local Σ Γ ->
    nth_error Γ n = Some decl ->
    Σ ;;; Γ |- tRel n : lift0 (S n) decl.(decl_type)

| type_Sort : forall s,
    wf_local Σ Γ ->
    wf_universe Σ s ->
    Σ ;;; Γ |- tSort s : tSort (Universe.super s)

| type_Prod : forall na A B s1 s2,
    Σ ;;; Γ |- A : tSort s1 ->
    Σ ;;; Γ ,, vass na A |- B : tSort s2 ->
    Σ ;;; Γ |- tProd na A B : tSort (Universe.sort_of_product s1 s2)

| type_Lambda : forall na A t s1 B,
    Σ ;;; Γ |- A : tSort s1 ->
    Σ ;;; Γ ,, vass na A |- t : B ->
    Σ ;;; Γ |- tLambda na A t : tProd na A B

| type_LetIn : forall na b B t s1 A,
    Σ ;;; Γ |- B : tSort s1 ->
    Σ ;;; Γ |- b : B ->
    Σ ;;; Γ ,, vdef na b B |- t : A ->
    Σ ;;; Γ |- tLetIn na b B t : tLetIn na b B A

| type_App : forall t na A B s u,

    Σ ;;; Γ |- tProd na A B : tSort s ->
    Σ ;;; Γ |- t : tProd na A B ->
    Σ ;;; Γ |- u : A ->
    Σ ;;; Γ |- tApp t u : B{0 := u}

| type_Const : forall cst u decl,
    wf_local Σ Γ ->
    declared_constant Σ cst decl ->
    consistent_instance_ext Σ decl.(cst_universes) u ->
    Σ ;;; Γ |- tConst cst u : decl.(cst_type)@[u]

| type_Ind : forall ind u mdecl idecl,
    wf_local Σ Γ ->
    declared_inductive Σ ind mdecl idecl ->
    consistent_instance_ext Σ mdecl.(ind_universes) u ->
    Σ ;;; Γ |- tInd ind u : idecl.(ind_type)@[u]

| type_Construct : forall ind i u mdecl idecl cdecl,
    wf_local Σ Γ ->
    declared_constructor Σ (ind, i) mdecl idecl cdecl ->
    consistent_instance_ext Σ mdecl.(ind_universes) u ->
    Σ ;;; Γ |- tConstruct ind i u : type_of_constructor mdecl cdecl (ind, i) u

| type_Case : forall ci p c brs indices ps mdecl idecl,
    let predctx := case_predicate_context ci.(ci_ind) mdecl idecl p in
    let ptm := it_mkLambda_or_LetIn predctx p.(preturn) in
    declared_inductive Σ ci.(ci_ind) mdecl idecl ->
    Σ ;;; Γ ,,, predctx |- p.(preturn) : tSort ps ->
    Σ ;;; Γ |- c : mkApps (tInd ci.(ci_ind) p.(puinst)) (p.(pparams) ++ indices) ->
    case_side_conditions (fun Σ Γ => wf_local Σ Γ) typing Σ Γ ci p ps
                         mdecl idecl indices predctx  ->
    case_branch_typing (fun Σ Γ => wf_local Σ Γ) typing Σ Γ ci p ps
                        mdecl idecl ptm brs ->
    Σ ;;; Γ |- tCase ci p c brs : mkApps ptm (indices ++ [c])

| type_Proj : forall p c u mdecl idecl cdecl pdecl args,
    declared_projection Σ p mdecl idecl cdecl pdecl ->
    Σ ;;; Γ |- c : mkApps (tInd p.(proj_ind) u) args ->
    #|args| = ind_npars mdecl ->
    Σ ;;; Γ |- tProj p c : subst0 (c :: List.rev args) pdecl.(proj_type)@[u]

| type_Fix : forall mfix n decl,
    wf_local Σ Γ ->
    fix_guard Σ Γ mfix ->
    nth_error mfix n = Some decl ->
    All (fun d => {s & Σ ;;; Γ |- d.(dtype) :  tSort s}) mfix ->
    All (fun d => (Σ ;;; Γ ,,, fix_context mfix |- d.(dbody) : lift0 #|fix_context mfix| d.(dtype))) mfix ->
    wf_fixpoint Σ mfix ->
    Σ ;;; Γ |- tFix mfix n : decl.(dtype)

| type_CoFix : forall mfix n decl,
    wf_local Σ Γ ->
    cofix_guard Σ Γ mfix ->
    nth_error mfix n = Some decl ->
    All (fun d => {s & Σ ;;; Γ |- d.(dtype) :  tSort s}) mfix ->
    All (fun d => Σ ;;; Γ ,,, fix_context mfix |- d.(dbody) : lift0 #|fix_context mfix| d.(dtype)) mfix ->
    wf_cofixpoint Σ mfix ->
    Σ ;;; Γ |- tCoFix mfix n : decl.(dtype)

| type_Prim p prim_ty cdecl :
   wf_local Σ Γ ->
   primitive_constant Σ (prim_val_tag p) = Some prim_ty ->
   declared_constant Σ prim_ty cdecl ->
   primitive_invariants cdecl ->
   Σ ;;; Γ |- tPrim p : tConst prim_ty []

| type_Cumul : forall t A B s,
    Σ ;;; Γ |- t : A ->
    Σ ;;; Γ |- B : tSort s ->
    Σ ;;; Γ |- A <=s B ->
    Σ ;;; Γ |- t : B

where " Σ ;;; Γ |- t : T " := (typing Σ Γ t T)
and "'wf_local' Σ Γ " := (All_local_env (lift_typing typing Σ) Γ).

Module PCUICTypingDef <: EnvironmentTyping.Typing PCUICTerm PCUICEnvironment PCUICTermUtils PCUICEnvTyping PCUICConversion PCUICConversionParSpec.

  Definition typing := @typing.

End PCUICTypingDef.

Module PCUICDeclarationTyping :=
  EnvironmentTyping.DeclarationTyping
    PCUICTerm
    PCUICEnvironment
    PCUICTermUtils
    PCUICEnvTyping
    PCUICConversion
    PCUICConversionParSpec
    PCUICTypingDef
    PCUICLookup
    PCUICGlobalMaps.
Include PCUICDeclarationTyping.

Definition wf `{checker_flags} := Forall_decls_typing typing.
Existing Class wf.

End PCUICTyping.
Module Export PCUICWellScopedCumulativity.
Import Coq.Classes.CRelationClasses.

Reserved Notation " Σ ;;; Γ ⊢ t ≤[ pb ] u" (at level 50, Γ, t, u at next level,
  format "Σ  ;;;  Γ  ⊢  t  ≤[ pb ]  u").

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

Inductive ws_cumul_pb {cf} (pb : conv_pb) (Σ : global_env_ext) (Γ : context) : term -> term -> Type :=
| ws_cumul_pb_compare (t u : term) :
  is_closed_context Γ -> is_open_term Γ t -> is_open_term Γ u ->
  compare_term pb Σ.1 (global_ext_constraints Σ) t u -> Σ ;;; Γ ⊢ t ≤[pb] u
| ws_cumul_pb_red_l (t u v : term) :
  is_closed_context Γ ->
  is_open_term Γ t -> is_open_term Γ u -> is_open_term Γ v ->
  red1 Σ Γ t v -> Σ ;;; Γ ⊢ v ≤[pb] u -> Σ ;;; Γ ⊢ t ≤[pb] u
| ws_cumul_pb_red_r (t u v : term) :
  is_closed_context Γ ->
  is_open_term Γ t -> is_open_term Γ u -> is_open_term Γ v ->
  Σ ;;; Γ ⊢ t ≤[pb] v -> red1 Σ Γ u v -> Σ ;;; Γ ⊢ t ≤[pb] u
where " Σ ;;; Γ ⊢ t ≤[ pb ] u " := (ws_cumul_pb pb Σ Γ t u) : type_scope.

Notation " Σ ;;; Γ ⊢ t ≤ u " := (ws_cumul_pb Cumul Σ Γ t u) (at level 50, Γ, t, u at next level,
    format "Σ  ;;;  Γ  ⊢  t  ≤  u") : type_scope.

#[global]
Instance ws_cumul_pb_trans {cf:checker_flags} {pb} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ} :
  Transitive (ws_cumul_pb pb Σ Γ).
Admitted.

End PCUICWellScopedCumulativity.

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

Lemma cumulSpec_typed_cumulAlgo {cf} {Σ} {wfΣ : wf Σ} {Γ : context} {t A B s} :
  Σ ;;; Γ |- t : A ->
  Σ ;;; Γ |- B : tSort s ->
  Σ ;;; Γ |- A <=s B  ->
  Σ ;;; Γ ⊢ A ≤ B.
Admitted.
#[global] Hint Immediate cumulSpec_typed_cumulAlgo : pcuic.
Import Equations.Prop.DepElim.

Section Inversion.

  Context {cf : checker_flags}.
  Context (Σ : global_env_ext).
  Context (wfΣ : wf Σ).

  Ltac insum :=
    match goal with
    | |- ∑ x : _, _ =>
      eexists
    end.

  Ltac intimes :=
    match goal with
    | |- _ × _ =>
      split
    end.

  Ltac outsum :=
    match goal with
    | ih : ∑ x : _, _ |- _ =>
      destruct ih as [? ?]
    end.

  Ltac outtimes :=
    match goal with
    | ih : _ × _ |- _ =>
      destruct ih as [? ?]
    end.

  Lemma into_ws_cumul {Γ t T U s} :
    Σ ;;; Γ |- t : T ->
    Σ ;;; Γ |- U : tSort s ->
    Σ ;;; Γ |- T <= U ->
    Σ ;;; Γ ⊢ T ≤ U.
Admitted.

  Lemma typing_ws_cumul_pb le Γ t T :
    Σ ;;; Γ |- t : T ->
    Σ ;;; Γ ⊢ T ≤[le] T.
Admitted.

  Ltac invtac h :=
    dependent induction h ; [
      repeat insum ;
      repeat intimes ;
      [ try first [ eassumption | try reflexivity ] .. | try solve [eapply typing_ws_cumul_pb; econstructor; eauto] ]
    | repeat outsum ;
      repeat outtimes ;
      repeat insum ;
      repeat intimes ;
      [ try first [ eassumption | reflexivity ] ..
      | try etransitivity ; try eassumption;
        try eauto with pcuic;
        try solve [eapply into_ws_cumul; tea] ]
    ].

  Lemma inversion_Rel :
    forall {Γ n T},
      Σ ;;; Γ |- tRel n : T ->
      ∑ decl,
        wf_local Σ Γ ×
        (nth_error Γ n = Some decl) ×
        Σ ;;; Γ ⊢ lift0 (S n) (decl_type decl) ≤ T.
  Proof using wfΣ.
    intros Γ n T h.
invtac h.
  Qed.
