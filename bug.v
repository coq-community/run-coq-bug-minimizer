(* -*- mode: coq; coq-prog-args: ("-emacs" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/msl" "VST.msl" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/sepcomp" "VST.sepcomp" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/veric" "VST.veric" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/floyd" "VST.floyd" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/progs" "VST.progs" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/concurrency" "VST.concurrency" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/atomics" "VST.atomics" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/wand_demo" "wand_demo" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/sha" "sha" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/hmacfcf" "hmacfcf" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/tweetnacl20140427" "tweetnacl20140427" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/hmacdrbg" "hmacdrbg" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/aes" "aes" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/mailbox" "mailbox" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/lib" "compcert.lib" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/common" "compcert.common" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/x86_32" "compcert.x86_32" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/x86" "compcert.x86" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/cfrontend" "compcert.cfrontend" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/exportclight" "compcert.exportclight" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Flocq" "Flocq" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-top" "bug_01" "-native-compiler" "no" "-native-compiler" "no") -*- *)
(* File reduced by coq-bug-finder from original input, then from 981 lines to 48 lines, then from 177 lines to 227 lines, then from 231 lines to 58 lines, then from 187 lines to 753 lines, then from 757 lines to 78 lines, then from 197 lines to 969 lines, then from 973 lines to 86 lines, then from 194 lines to 1059 lines, then from 1063 lines to 113 lines, then from 217 lines to 504 lines, then from 501 lines to 113 lines, then from 216 lines to 350 lines, then from 354 lines to 115 lines, then from 218 lines to 2333 lines, then from 2329 lines to 134 lines, then from 223 lines to 123 lines, then from 224 lines to 1656 lines, then from 1658 lines to 442 lines, then from 541 lines to 1816 lines, then from 1814 lines to 450 lines, then from 548 lines to 446 lines, then from 544 lines to 587 lines, then from 591 lines to 461 lines, then from 546 lines to 1447 lines, then from 1448 lines to 466 lines, then from 549 lines to 1160 lines, then from 1162 lines to 747 lines *)
(* coqc version 8.15+alpha compiled with OCaml 4.12.0
   coqtop version 8.15+alpha *)
Declare ML Module "ltac_plugin".
Module Export AdmitTactic.
Module Import LocalFalse.
Inductive False := .
End LocalFalse.
Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.
End AdmitTactic.
Require Coq.Arith.EqNat.
Require Coq.Relations.Relations.
Require Coq.Logic.ClassicalFacts.
Require Coq.Logic.FunctionalExtensionality.
Require compcert.lib.Axioms.
Require Coq.Strings.String.
Require Coq.ZArith.ZArith.
Require Coq.ZArith.Znumtheory.
Require Coq.Lists.List.
Require Coq.Bool.Bool.
Require Coq.micromega.Lia.
Require compcert.lib.Coqlib.
Require Coq.Logic.Eqdep_dec.
Require Coq.ZArith.Zquot.
Require Coq.ZArith.Zwf.
Require Coq.micromega.Psatz.
Require compcert.lib.Zbits.
Require Flocq.IEEE754.Binary.
Require Flocq.IEEE754.Bits.
Require compcert.x86_32.Archi.
Require compcert.lib.Integers.
Require Flocq.Core.Core.
Require Flocq.Core.Digits.
Require Flocq.Calc.Operations.
Require Flocq.Calc.Round.
Require Flocq.Calc.Bracket.
Require Flocq.Prop.Sterbenz.
Require Coq.Reals.Reals.
Require Flocq.Prop.Round_odd.
Require compcert.lib.IEEE754_extra.
Require Coq.Program.Program.
Require compcert.lib.Floats.
Require Coq.Classes.Equivalence.
Require Coq.Classes.EquivDec.
Require compcert.lib.Maps.
Require compcert.common.Errors.
Require compcert.common.AST.
Require compcert.common.Values.
Require compcert.common.Memdata.
Require compcert.common.Memtype.
Require Coq.Program.Wf.
Require Coq.funind.Recdef.
Require compcert.lib.Intv.
Require compcert.common.Memory.
Require compcert.common.Linking.
Require compcert.common.Globalenvs.
Require VST.msl.Axioms.
Require Coq.Logic.EqdepFacts.
Require VST.msl.Extensionality.
Require VST.msl.base.
Require VST.msl.Coqlib2.
Require Coq.Sorting.Permutation.
Require VST.msl.eq_dec.
Require Coq.Sets.Ensembles.
Require Coq.Logic.ConstructiveEpsilon.
Require VST.veric.coqlib4.
Require VST.veric.base.
Require compcert.cfrontend.Ctypes.
Require VST.msl.sepalg.
Require VST.msl.ghost.
Require VST.msl.sig_isomorphism.
Require VST.msl.functors.
Require Coq.Wellfounded.Wellfounded.
Require VST.msl.ageable.
Require VST.msl.knot.
Require VST.msl.knot_full_variant.
Require VST.msl.predicates_hered.
Require VST.msl.knot_shims.
Require VST.msl.sepalg_generators.
Require VST.msl.sepalg_functors.
Require VST.msl.age_sepalg.
Require VST.msl.knot_full_sa.
Module Export VST_DOT_msl_DOT_psepalg_WRAPPED.
Module Export psepalg.
 
Import VST.msl.base.
Import VST.msl.eq_dec.
Import VST.msl.sepalg.
Import VST.msl.sepalg_generators.

 

Lemma pjoin_unit {A} {JA: Join A}{PosA: Pos_alg A}: forall {a b : A},
  join a b b -> False.
admit.
Defined.

 
Definition cjoins {A} {JA: Join A} (a b : A) : Type := {c : A | join a b c}.

 
Definition cjoin_sub {A} {JA: Join A} (a c : A) : Type := {b : A | join a b c}.

 
Lemma joins_comm {A} {JA: Join A}{PA: Perm_alg A} : forall a b,
  joins a b -> joins b a.
admit.
Defined.

 
Lemma pfull_pmaximal {A} {JA: Join A} {PA: Perm_alg A} {Pos_A: Pos_alg A} : full = maximal.
admit.
Defined.

Lemma psub_joins {A}  {JA: Join A} {PA: Perm_alg A} {Pos_A: Pos_alg A}{DA: Disj_alg A} : forall a b,
  join_sub a b -> joins a b -> False.
admit.
Defined.

Section DISCRETE.
  
 

  Instance Join_discrete (A : Type): Join A := fun a1 a2 a3 : A => False.

  Instance Perm_discrete (A: Type)  : @Perm_alg A (Join_discrete A).
admit.
Defined.

  Instance psa_discrete (A: Type) :  @Pos_alg A  (Join_discrete A).
admit.
Defined.
End DISCRETE.

Set Implicit Arguments.

 
Section PSA_LIFT.
  Variable A : Type.
  Variable J_A: Join A.
  Variable PA_A : Perm_alg A.

  Definition lifted : Type := sig nonunit.

  Definition lifted_obj (la: lifted) : A := proj1_sig la.
 
  Coercion lifted_obj : lifted >-> A.
  Definition mk_lifted (a : A) (pf : nonunit a) : lifted :=
    exist nonunit a pf.

  Instance Join_lift: Join lifted := fun a1 a2 a3 : lifted => @join A J_A a1 a2 a3.

    Instance Perm_lift: Perm_alg lifted.
admit.
Defined.

  Instance Pos_lift: Pos_alg lifted.
admit.
Defined.

  Instance Canc_lift {CA: Canc_alg A}: Canc_alg lifted.
admit.
Defined.

  Instance Disj_lift {DA: Disj_alg A}: Disj_alg lifted.
admit.
Defined.

   

  Lemma lifted_eq : forall a b,
    lifted_obj a = lifted_obj b ->
    a = b.
admit.
Defined.

  Lemma mk_lifted_refl1: forall (a:A)  (pf1 pf2: nonunit a),
    mk_lifted pf1 = mk_lifted pf2.
admit.
Defined.

  Lemma lifted_pjoins : forall a b : lifted,
    joins a b = @joins A J_A a b.
admit.
Defined.

  Lemma lifted_psub : forall a b : lifted,
    join_sub a b -> @join_sub A J_A a b.
admit.
Defined.

  Lemma lifted_full {CA: Canc_alg A} : forall a : lifted,
    @full A J_A a -> full a.
admit.
Defined.

End PSA_LIFT.

Existing Instance Join_lift.
  
Existing Instance Perm_lift.
Existing Instance Pos_lift.
Existing Instance Canc_lift.
Existing Instance Disj_lift.
Arguments mk_lifted [A J_A] _ _.

 

Section SA_LOWER.
  Variable A : Type.
  Variable Pj_A: Join A.
  Variable PA_A : Perm_alg A.

  Inductive lower_join: option A -> option A -> option A -> Prop :=
  | lower_None1: forall a, lower_join None a a
  | lower_None2: forall a, lower_join a None a
  | lower_Some: forall a1 a2 a3,  join a1 a2 a3 ->
        lower_join (Some a1) (Some a2) (Some a3).

  Instance Join_lower: Join (option A) := lower_join.

  Instance Perm_lower: @Perm_alg (option A) Join_lower.
  Proof.
   constructor; intros.

   inv H; inv H0; try constructor.
f_equal.
  apply (join_eq H1 H3).

    icase d; [ |  exists c; inv H; inv H0; split; constructor; auto].
    icase e; [ | exists a; inv H0; inv H; split; constructor; auto].
    icase c; [ | exists b; inv H; inv H0; split; constructor; auto].
    icase a; [ | exists (Some a1); inv H; inv H0; split; try constructor; auto].
    icase b; [ | exists (Some a2); inv H; inv H0; split; constructor; auto].
    assert (join a a3 a0) by (inv H; auto).
    assert (join a0 a2 a1) by (inv H0; auto).
    destruct (join_assoc H1 H2) as [f [? ?]]; exists (Some f); split; constructor; auto.

    inv H; constructor; auto.

    inv H; inv H0; auto.
f_equal.
apply (join_positivity H1 H4).
 Qed.

 Instance Sep_lower: @Sep_alg _ Join_lower.
admit.
Defined.

  Instance Sing_lower: @Sing_alg _ Join_lower _.
admit.
Defined.

  Instance Canc_lower {psa_A: Pos_alg A}{CA: Canc_alg A}: @Canc_alg _ Join_lower.
admit.
Defined.

  Instance Disj_lower {psa_A: Pos_alg A}{DA: Disj_alg A}: @Disj_alg _ Join_lower.
  Proof.
repeat intro.
inv H0; inv H; auto.
    -
 contradiction (no_units a1 a1).
      apply identity_unit; [eapply join_self | eexists]; eauto.
    -
 eapply f_equal, join_self; eauto.
  Qed.

End SA_LOWER.
Arguments Perm_lower _ {Pj_A}{PA_A}.
Arguments Sep_lower _ {Pj_A}.
Arguments Sing_lower _ {Pj_A}.
Arguments Canc_lower _ [Pj_A][psa_A][CA] _ _ _ _ _ _.
Arguments Disj_lower _ [Pj_A][PA_A][psa_A][DA] _ _ _.

Existing Instance Join_lower.
Existing Instance Sep_lower.

 

Section SA_SMASH.
End SA_SMASH.
 

 Instance Perm_option (T : Type)  : @Perm_alg (option T) (@Join_lower T (@Join_discrete T)) :=
    @Perm_lower T  (@Join_discrete T) (Perm_discrete T).

 
Section FinitePartialMap.
End FinitePartialMap.

End psepalg.
Require VST.msl.tree_shares.
Import VST.msl.boolean_alg.

Module Share : SHARE_MODEL := tree_shares.Share.

Definition share : Type := Share.t.
Export VST.msl.ageable.
Export VST.msl.base.
Export VST.msl.knot_shims.
Export VST.msl.knot_full_sa.
Export VST.msl.predicates_hered.
Export VST.msl.sepalg.
Export VST.msl.functors.
Export VST.msl.sepalg_functors.
Export VST.msl.sepalg_generators.

Export MixVariantFunctor.
Export MixVariantFunctorGenerator.

Definition nonempty_share (sh: share) :=
       sepalg.nonidentity sh.
Definition readable_share (sh: share) :=
       nonempty_share (Share.glb Share.Rsh sh).
Import VST.msl.ghost.

Module Type ADR_VAL.
Parameter address : Type.

Parameter kind: Type.
End ADR_VAL.

Inductive TypeTree: Type :=
  | ConstType: Type -> TypeTree
  | Mpred: TypeTree
  | DependentType: nat -> TypeTree
  | ProdType: TypeTree -> TypeTree -> TypeTree
  | ArrowType: TypeTree -> TypeTree -> TypeTree
  | SigType: forall (I : Type), (I -> TypeTree) -> TypeTree
  | PiType: forall (I : Type), (I -> TypeTree) -> TypeTree
  | ListType: TypeTree -> TypeTree.

Definition dependent_type_functor_rec (ts: list Type): TypeTree -> functor :=
  fix dtfr (T: TypeTree): functor :=
  match T with
  | ConstType A => fconst A
  | Mpred => fidentity
  | DependentType n => fconst (nth n ts unit)
  | ProdType T1 T2 => fpair (dtfr T1) (dtfr T2)
  | ArrowType T1 T2 => ffunc (dtfr T1) (dtfr T2)
  | SigType _ f => fsig (fun i => dtfr (f i))
  | PiType _ f => fpi (fun i => dtfr (f i))
  | ListType T => flist (dtfr T)
  end.

Definition fpreds: functor :=
  fsig (fun T: TypeTree =>
    fpi (fun ts: list Type => dependent_type_functor_rec ts T)).

Module Type STRAT_MODEL.
  Declare Module AV : ADR_VAL.
  Import AV.

  Inductive res (PRED : Type) : Type :=
    | NO':  forall sh: Share.t, ~(readable_share sh) -> res PRED
    | YES': forall sh: Share.t, readable_share sh -> kind -> fpreds PRED -> res PRED
    | PURE': kind -> fpreds PRED -> res PRED.

  Definition res_fmap (A B:Type) (f:A->B) (g:B->A)(x:res A) : res B :=
    match x with
      | NO' rsh nsh => NO' B rsh nsh
      | YES' sh rsh k pds => YES' B sh rsh k (fmap fpreds f g pds)
      | PURE' k pds => PURE' B k (fmap fpreds f g pds)
    end.
  Axiom ff_res : functorFacts res res_fmap.
  Definition f_res : functor := Functor ff_res.

  Inductive res_join (PRED : Type) : f_res PRED -> f_res PRED -> f_res PRED -> Prop :=
    | res_join_NO1 : forall sh1 nsh1 sh2 nsh2 sh3 nsh3,
                               join sh1 sh2 sh3 ->
                               res_join PRED (NO' PRED sh1 nsh1) (NO' PRED sh2 nsh2)
                                     (NO' PRED sh3 nsh3)
    | res_join_NO2 : forall sh1 nsh1 sh2 rsh2 sh3 rsh3 k p,
                               join sh1 sh2 sh3 ->
                               res_join PRED (NO' PRED sh1 nsh1) (YES' PRED sh2 rsh2 k p)
                                   (YES' PRED sh3 rsh3 k p)
    | res_join_NO3 : forall sh1 rsh1 sh2 nsh2 sh3 rsh3 k p,
                               join sh1 sh2 sh3 ->
                               res_join PRED (YES' PRED sh1 rsh1 k p) (NO' PRED sh2 nsh2)
                                   (YES' PRED sh3 rsh3 k p)
    | res_join_YES : forall sh1 rsh1 sh2 rsh2 sh3 rsh3 k p,
                              join sh1 sh2 sh3 ->
              res_join PRED (YES' PRED sh1 rsh1 k p) (YES' PRED sh2 rsh2 k p) (YES' PRED sh3 rsh3 k p)
    | res_join_PURE : forall k p, res_join PRED (PURE' PRED k p) (PURE' PRED k p) (PURE' PRED k p).

  Definition ghost (PRED : Type) : Type :=
    list (option ({g: Ghost & {a: @G g | ghost.valid a}} * fpreds PRED)%type).

  Definition ghost_fmap (A B:Type) (f:A->B) (g:B->A)(x:ghost A) : ghost B :=
    fmap (flist (foption (fpair (fconst _) fpreds))) f g x.

  Axiom ff_ghost : functorFacts ghost ghost_fmap.
  Definition f_ghost : functor := Functor ff_ghost.

  Instance preds_join PRED : Join _ := Join_equiv (fpreds PRED).

  Inductive ghost_elem_join : Join {g: Ghost & {a: @G g | ghost.valid a}} :=
  | elem_join_I g a b c va vb vc: join a b c ->
    ghost_elem_join (existT _ g (exist _ a va)) (existT _ g (exist _ b vb))
                    (existT _ g (exist _ c vc)).
  Existing Instance ghost_elem_join.

  Inductive ghost_join PRED : Join (ghost PRED) :=
  | ghost_join_nil_l m: ghost_join PRED nil m m
  | ghost_join_nil_r m: ghost_join PRED m nil m
  | ghost_join_cons a1 a2 m1 m2 a3 m3: join a1 a2 a3 -> ghost_join PRED m1 m2 m3 ->
      ghost_join PRED (a1 :: m1) (a2 :: m2) (a3 :: m3).

  Definition f_pre_rmap : functor :=
    fpair (ffunc (fconst address) f_res) f_ghost.

  Instance Join_pre_rmap (A: Type) : Join (f_pre_rmap A) :=
            Join_prod _ (Join_fun address (res A) (res_join A)) _ (ghost_join A).

  Declare Instance Perm_pre_rmap: forall (A: Type), Perm_alg (f_pre_rmap A).
  Declare Instance Sep_pre_rmap: forall (A: Type), Sep_alg (f_pre_rmap A).
  Parameter paf_pre_rmap : @pafunctor f_pre_rmap Join_pre_rmap.

End STRAT_MODEL.

Module StratModel (AV' : ADR_VAL) : STRAT_MODEL with Module AV:=AV'.
  Module AV := AV'.
  Import AV.

  Definition preds: functor :=
    fsig (fun T: TypeTree =>
      fpi (fun ts: list Type => dependent_type_functor_rec ts T)).

  Inductive res (PRED : Type) : Type :=
    | NO':  forall sh: Share.t, ~(readable_share sh) -> res PRED
    | YES': forall sh: Share.t, readable_share sh -> kind -> preds PRED -> res PRED
    | PURE': kind -> preds PRED -> res PRED.

  Definition res_fmap (A B:Type) (f:A->B) (g:B->A)(x:res A) : res B :=
    match x with
      | NO' rsh nsh => NO' B rsh nsh
      | YES' sh rsh k pds => YES' B sh rsh k (fmap preds f g pds)
      | PURE' k pds => PURE' B k (fmap preds f g pds)
    end.

  Lemma ff_res : functorFacts res res_fmap.
admit.
Defined.

  Definition f_res : functor := Functor ff_res.

  Inductive res_join (PRED : Type) : f_res PRED -> f_res PRED -> f_res PRED -> Prop :=
    | res_join_NO1 : forall sh1 nsh1 sh2 nsh2 sh3 nsh3,
                               join sh1 sh2 sh3 ->
                               res_join PRED (NO' PRED sh1 nsh1) (NO' PRED sh2 nsh2)
                                     (NO' PRED sh3 nsh3)
    | res_join_NO2 : forall sh1 nsh1 sh2 rsh2 sh3 rsh3 k p,
                               join sh1 sh2 sh3 ->
                               res_join PRED (NO' PRED sh1 nsh1) (YES' PRED sh2 rsh2 k p)
                                   (YES' PRED sh3 rsh3 k p)
    | res_join_NO3 : forall sh1 rsh1 sh2 nsh2 sh3 rsh3 k p,
                               join sh1 sh2 sh3 ->
                               res_join PRED (YES' PRED sh1 rsh1 k p) (NO' PRED sh2 nsh2)
                                   (YES' PRED sh3 rsh3 k p)
    | res_join_YES : forall sh1 rsh1 sh2 rsh2 sh3 rsh3 k p,
                              join sh1 sh2 sh3 ->
              res_join PRED (YES' PRED sh1 rsh1 k p) (YES' PRED sh2 rsh2 k p) (YES' PRED sh3 rsh3 k p)
    | res_join_PURE : forall k p, res_join PRED (PURE' PRED k p) (PURE' PRED k p) (PURE' PRED k p).

  Instance pa_rj : forall PRED, @Perm_alg _ (res_join PRED).
admit.
Defined.

  Instance sa_rj : forall PRED, @Sep_alg _ (res_join PRED).
admit.
Defined.

  Definition paf_res : @pafunctor f_res res_join.
admit.
Defined.

  Definition ghost (PRED : Type) : Type :=
    list (option ({g: Ghost & {a: @G g | ghost.valid a}} * fpreds PRED)%type).

  Definition ghost_fmap (A B:Type) (f:A->B) (g:B->A)(x:ghost A) : ghost B :=
    fmap (flist (foption (fpair (fconst _) fpreds))) f g x.

  Lemma ff_ghost : functorFacts ghost ghost_fmap.
admit.
Defined.

  Definition f_ghost : functor := Functor ff_ghost.

  Instance preds_join PRED : Join _ := Join_equiv (fpreds PRED).

  Inductive ghost_elem_join : Join {g: Ghost & {a: @G g | ghost.valid a}} :=
  | elem_join_I g a b c va vb vc: join a b c ->
    ghost_elem_join (existT _ g (exist _ a va)) (existT _ g (exist _ b vb))
                    (existT _ g (exist _ c vc)).
  Existing Instance ghost_elem_join.

  Inductive ghost_join PRED : Join (ghost PRED) :=
  | ghost_join_nil_l m: ghost_join PRED nil m m
  | ghost_join_nil_r m: ghost_join PRED m nil m
  | ghost_join_cons a1 a2 m1 m2 a3 m3: join a1 a2 a3 -> ghost_join PRED m1 m2 m3 ->
      ghost_join PRED (a1 :: m1) (a2 :: m2) (a3 :: m3).

  Instance pa_gj : forall PRED, @Perm_alg _ (ghost_join PRED).
admit.
Defined.

  Instance sa_gj : forall PRED, @Sep_alg _ (ghost_join PRED).
admit.
Defined.

  Definition paf_ghost : @pafunctor f_ghost ghost_join.
admit.
Defined.

  Definition pre_rmap (A:Type) := ((address -> res A) * ghost A)%type.
  Definition f_pre_rmap : functor :=
    fpair (ffunc (fconst address) f_res) f_ghost.

  Notation Join_obj A := (Join_prod _ (Join_fun address (res A) (res_join A)) _ (ghost_join A)).

  Instance Join_pre_rmap (A: Type) : Join (pre_rmap A) :=
    Join_obj A.

  Definition paf_pre_rmap : @pafunctor f_pre_rmap Join_pre_rmap :=
    paf_pair (paf_fun address paf_res) paf_ghost.

  Definition Perm_pre_rmap (A: Type): Perm_alg (pre_rmap A) :=
    Perm_prod (Perm_fun address _ _ _) (pa_gj A).

  Definition Sep_pre_rmap (A: Type): Sep_alg (pre_rmap A) :=
    Sep_prod (Sep_fun address _ _ _) (sa_gj A).

End StratModel.

Module Type RMAPS.
  Declare Module AV:ADR_VAL.

  Parameter rmap : Type.
  Axiom ag_rmap: ageable rmap.
 Existing Instance ag_rmap.

  Inductive preds : Type :=
    SomeP : forall A : TypeTree,
      (forall ts: list Type, dependent_type_functor_rec ts A (pred rmap)) -> preds.

  Definition NoneP := SomeP (ConstType unit) (fun _ => tt).

  Definition preds_fmap (f g: pred rmap -> pred rmap) (x:preds) : preds :=
    match x with SomeP A Q => SomeP A (fmap (fpi _) f g Q)
    end.

  Definition ghost : Type := list (option ({g: Ghost & {a: @G g | ghost.valid a}} * preds)%type).

  Instance preds_join : Join _ := Join_equiv preds.

  Inductive ghost_elem_join : Join {g: Ghost & {a: @G g | ghost.valid a}} :=
  | elem_join_I g a b c va vb vc: join a b c ->
    ghost_elem_join (existT _ g (exist _ a va)) (existT _ g (exist _ b vb))
                    (existT _ g (exist _ c vc)).
  Existing Instance ghost_elem_join.

  Inductive ghost_join : Join ghost :=
  | ghost_join_nil_l m: ghost_join nil m m
  | ghost_join_nil_r m: ghost_join m nil m
  | ghost_join_cons a1 a2 m1 m2 a3 m3: join a1 a2 a3 -> ghost_join m1 m2 m3 ->
      ghost_join (a1 :: m1) (a2 :: m2) (a3 :: m3).
  Existing Instance ghost_join.

  Definition ghost_fmap (f g:pred rmap -> pred rmap)(x:ghost) : ghost :=
    map (option_map (fun '(a, b) => (a, preds_fmap f g b))) x.

  Program Definition approx (n:nat) (p: pred rmap) : pred rmap :=
    fun w => level w < n /\ p w.
Admit Obligations.

End RMAPS.

Module Rmaps (AV':ADR_VAL): RMAPS with Module AV:=AV'.
  Module Export AV:=AV'.

  Module SM := StratModel(AV).
  Import SM.

  Module Export TyF.

    Definition F := f_pre_rmap.
  End TyF.

  Module TyFSA <: KNOT_FULL_SA_INPUT with Module KI:=TyF.
    Module KI := TyF.

    Instance Join_F: forall A, Join (F A) := _.
    Definition Perm_F : forall A, Perm_alg (F A) := Perm_pre_rmap.
    Definition Sep_F := Sep_pre_rmap.
    Definition paf_F := paf_pre_rmap.
  End TyFSA.

  Module K := Knot_MixVariantHeredProp(TyF).

  Definition rmap := K.knot.
  Instance ag_rmap : ageable rmap := K.ageable_knot.

  Inductive preds : Type :=
    SomeP : forall A : TypeTree,
    (forall ts: list Type, dependent_type_functor_rec ts A (pred rmap)) -> preds.

  Definition NoneP := SomeP (ConstType unit) (fun _ => tt).

  Definition ghost : Type := list (option ({g: Ghost & {a: @G g | ghost.valid a}} * preds)%type).

  Instance preds_join : Join _ := Join_equiv preds.

  Inductive ghost_elem_join : Join {g: Ghost & {a: @G g | ghost.valid a}} :=
  | elem_join_I g a b c va vb vc: join a b c ->
    ghost_elem_join (existT _ g (exist _ a va)) (existT _ g (exist _ b vb))
                    (existT _ g (exist _ c vc)).
  Existing Instance ghost_elem_join.

  Inductive ghost_join : Join ghost :=
  | ghost_join_nil_l m: ghost_join nil m m
  | ghost_join_nil_r m: ghost_join m nil m
  | ghost_join_cons a1 a2 m1 m2 a3 m3: join a1 a2 a3 -> ghost_join m1 m2 m3 ->
      ghost_join (a1 :: m1) (a2 :: m2) (a3 :: m3).
  Definition preds_fmap (f g:(pred rmap)->(pred rmap)) (x:preds) : preds :=
    match x with SomeP A ls => SomeP A (fmap (fpi _) f g ls) end.

  Definition ghost_fmap (f g:pred rmap -> pred rmap)(x:ghost) : ghost :=
    map (option_map (fun '(a, b) => (a, preds_fmap f g b))) x.

  Program Definition approx (n:nat) (p: (pred rmap)) : (pred rmap) :=
    fun w => level w < n /\ p w.
Admit Obligations.

End Rmaps.

Module Rmaps_Lemmas (R0: RMAPS).

Ltac inj_pair_tac :=
 match goal with H: (@existT ?U ?P ?p ?x = @existT _ _ _ ?y) |- _ =>
   generalize (@inj_pair2 U P p x y H); clear H; intro; try (subst x || subst y)
 end.

End Rmaps_Lemmas.
Import compcert.lib.Coqlib.
Import compcert.common.Values.

Definition address : Type := (block * Z)%type.
Import VST.veric.base.
Import compcert.cfrontend.Ctypes.

Definition typesig := (list type * type)%type.

Inductive kind : Type := VAL : memval -> kind
                                   | LK : forall n i : Z, kind
                                   | FUN:  typesig -> calling_convention -> kind.

Module CompCert_AV <: ADR_VAL.

Definition address := address.
Definition kind := kind.

End CompCert_AV.

Module R := Rmaps (CompCert_AV).
Module RML := Rmaps_Lemmas(R).

Export RML.
Export R.

Fixpoint make_join (a c : ghost) : ghost :=
  match a, c with
  | nil, _ => c
  | _, nil => nil
  | None :: a', x :: c' => x :: make_join a' c'
  | _ :: a', None :: c' => None :: make_join a' c'
  | Some (ga, pa) :: a', Some (gc, _) :: c' => Some (gc, pa) :: make_join a' c'
  end.

Global Program Instance pos_PCM (P : Ghost) : Ghost := { G := option (share * G);
  valid a := match a with Some (sh, _) => sh <> Share.bot | _ => True end;
  Join_G a b c := match a, b, c with
  | Some (sha, a'), Some (shb, b'), Some (shc, c') =>
      sha <> Share.bot /\ shb <> Share.bot /\ sepalg.join sha shb shc /\ join a' b' c'
  | Some (sh, a), None, Some c' | None, Some (sh, a), Some c' => c' = (sh, a)
  | None, None, None => True
  | _, _, _ => False
  end  }.
Admit Obligations.

Definition completable {P : Ghost} (a: @G (pos_PCM P)) r := exists x, join a x (Some (Share.top, r)).

Global Program Instance ref_PCM (P : Ghost) : Ghost :=
{ valid a := valid (fst a) /\ match snd a with Some r => completable (fst a) r | None => True end;
  Join_G a b c := @Join_G (pos_PCM P) (fst a) (fst b) (fst c) /\
    @psepalg.Join_lower _ (psepalg.Join_discrete _) (snd a) (snd b) (snd c)  }.
Admit Obligations.

Program Instance exclusive_PCM A : Ghost :=
  { valid a := True; Join_G := Join_lower (Join_discrete A)  }.

Definition ext_PCM Z : Ghost := ref_PCM (exclusive_PCM Z).

Lemma valid_ext_ref : forall {Z} (ora : Z), @valid (ext_PCM _) (None, Some (Some ora)).
admit.
Defined.

Definition ext_ref {Z} (ora : Z) : {g : Ghost & {a : G | valid a}} :=
  existT _ (ext_PCM _) (exist _ _ (valid_ext_ref ora)).

Lemma make_join_ext : forall (ora : Z) a c n,
  join_sub (Some (ext_ref ora, NoneP) :: nil) c ->
  joins (ghost_fmap (approx n) (approx n) a) (ghost_fmap (approx n) (approx n) c) ->
  join_sub (Some (ext_ref ora, NoneP) :: nil) (make_join a c).
Proof.
  destruct a; auto; simpl.
  intros ?? [? HC] [? J].
  inv J.
  {
 destruct c; inv H1; inv HC.
}
  destruct c; inv H1.
  inv H2.
  {
 destruct o; inv H0; inv HC.
    *
 eexists; constructor; constructor.
    *
 eexists; constructor; eauto; constructor.
}
  {
 destruct o0; inv H1; inv HC.
    inv H3.
}
  destruct o as [[]|], o0 as [[]|]; inv H; inv H0.
  destruct a0; inv H1; simpl in *.
  inv H0.
  assert (@ghost.valid (ext_PCM Z) (None, None)) as Hv.
  {
 simpl; auto.
}
  inv HC.
  -
 eexists; constructor; constructor.
    destruct p; inv H1; inj_pair_tac.
    instantiate (1 := (existT _ (ext_PCM Z) (exist _ _ Hv), _)); repeat constructor; simpl.
    rewrite <- H0; auto.
