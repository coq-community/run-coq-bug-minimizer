(* -*- mode: coq; coq-prog-args: ("-emacs" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/msl" "VST.msl" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/sepcomp" "VST.sepcomp" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/veric" "VST.veric" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/floyd" "VST.floyd" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/progs" "VST.progs" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/concurrency" "VST.concurrency" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/atomics" "VST.atomics" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/wand_demo" "wand_demo" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/sha" "sha" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/hmacfcf" "hmacfcf" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/tweetnacl20140427" "tweetnacl20140427" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/hmacdrbg" "hmacdrbg" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/aes" "aes" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/mailbox" "mailbox" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/lib" "compcert.lib" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/common" "compcert.common" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/x86_32" "compcert.x86_32" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/x86" "compcert.x86" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/cfrontend" "compcert.cfrontend" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/exportclight" "compcert.exportclight" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Flocq" "Flocq" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-top" "bug_01" "-native-compiler" "no" "-native-compiler" "no") -*- *)
(* File reduced by coq-bug-finder from original input, then from 981 lines to 48 lines, then from 177 lines to 227 lines, then from 231 lines to 58 lines, then from 187 lines to 753 lines, then from 757 lines to 78 lines, then from 197 lines to 969 lines, then from 973 lines to 86 lines, then from 194 lines to 1059 lines, then from 1063 lines to 113 lines, then from 217 lines to 504 lines, then from 501 lines to 113 lines, then from 216 lines to 350 lines, then from 354 lines to 115 lines, then from 218 lines to 2333 lines, then from 2329 lines to 134 lines, then from 223 lines to 123 lines, then from 224 lines to 1656 lines, then from 1658 lines to 442 lines, then from 541 lines to 1816 lines, then from 1814 lines to 450 lines, then from 548 lines to 446 lines, then from 544 lines to 587 lines, then from 591 lines to 461 lines, then from 546 lines to 1447 lines, then from 1448 lines to 466 lines, then from 549 lines to 1160 lines, then from 1162 lines to 747 lines, then from 737 lines to 530 lines, then from 613 lines to 996 lines, then from 1000 lines to 419 lines, then from 500 lines to 812 lines, then from 815 lines to 420 lines, then from 499 lines to 1328 lines, then from 1329 lines to 913 lines *)
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
Module Export VST_DOT_msl_DOT_sepalg_generators_WRAPPED.
Module Export sepalg_generators.
 

 
Import VST.msl.base.
Import VST.msl.sepalg.

 

  Instance Join_unit : Join unit := fun x y z => True.

  Instance Perm_unit : Perm_alg unit.
admit.
Defined.

  Instance Sep_unit: Sep_alg unit.
admit.
Defined.

  Instance Sing_unit: Sing_alg unit.
admit.
Defined.

  Instance Canc_unit: Canc_alg unit.
admit.
Defined.

  Instance Disj_unit: Disj_alg unit.
admit.
Defined.

  Instance Cross_unit: Cross_alg unit.
admit.
Defined.

 

  Inductive Void : Type :=.

  Instance Join_void : Join Void := fun x y z => False.

  Instance Perm_void : Perm_alg Void.
admit.
Defined.
  Instance Sep_void: Sep_alg Void.
admit.
Defined.
  Instance Canc_void: Canc_alg Void.
admit.
Defined.
  Instance Disj_void: Disj_alg Void.
admit.
Defined.
  Instance Cross_void: Cross_alg Void.
admit.
Defined.

 

  Inductive join_bool : bool -> bool -> bool -> Prop :=
  | jb_fff: join_bool false false false
  | jb_tft: join_bool true false true
  | jb_ftt: join_bool false true true.

  Instance Join_bool : Join bool := join_bool.

  Instance Perm_bool: Perm_alg bool.
admit.
Defined.

  Instance Sep_bool: Sep_alg bool.
admit.
Defined.

  Instance Sing_bool: Sing_alg bool.
admit.
Defined.

  Instance Canc_bool: Canc_alg bool.
admit.
Defined.

  Instance Disj_bool: Disj_alg bool.
admit.
Defined.

  Instance Cross_bool: Cross_alg bool.
admit.
Defined.

Section JOIN_EQUIV.
 

  Instance Join_equiv (A: Type) : Join A := fun x y z => x=y/\y=z.

  Instance Perm_equiv (A: Type) :  @Perm_alg A (Join_equiv A).
admit.
Defined.

  Instance Sep_equiv (A: Type): Sep_alg A.
admit.
Defined.

  Instance Canc_equiv (A: Type): Canc_alg A.
admit.
Defined.

  Instance Disj_equiv (A: Type): Disj_alg A.
admit.
Defined.

  Instance Cross_equiv (A: Type): Cross_alg A.
admit.
Defined.

Lemma join_equiv_refl: forall A (v: A), @join A (Join_equiv A) v v v.
admit.
Defined.
End JOIN_EQUIV.

 
Existing Instance Perm_equiv.
Existing Instance Sep_equiv.
Existing Instance Canc_equiv.
Existing Instance Disj_equiv.
Existing Instance Cross_equiv.

#[export] Hint Extern 1 (@join _ _ _ _ _) =>
   match goal with |- @join _ (@Join_equiv _) _ _ _ => apply join_equiv_refl end
   : core.

Section SepAlgProp.
  Variable A:Type.
  Variable JOIN: Join A.
  Variable PA: Perm_alg A.
  Variable P:A -> Prop.

  Variable HPjoin : forall x y z, join x y z -> P x -> P y -> P z.

  Instance Join_prop : Join (sig P) :=
                 fun x y z: (sig P) => join (proj1_sig x) (proj1_sig y) (proj1_sig z).

  Instance Perm_prop : Perm_alg (sig P).
admit.
Defined.

  Instance Sep_prop (SA: Sep_alg A)(HPcore : forall x, P x -> P (core x)): Sep_alg (sig P).
admit.
Defined.

 Instance Sing_prop  (SA: Sep_alg A)(Sing_A: Sing_alg A)
               (HPcore : forall x, P x -> P (core x)): P the_unit ->
    @Sing_alg (sig P) Join_prop (Sep_prop _ HPcore).
admit.
Defined.

  Instance Canc_prop  {CA: Canc_alg A}:  Canc_alg (sig P).
admit.
Defined.

  Instance Disj_prop {DA: Disj_alg A}: Disj_alg (sig P).
admit.
Defined.

 

End SepAlgProp.
Existing Instance Join_prop.
Existing Instance Perm_prop.
Existing Instance Sep_prop.
Existing Instance Sing_prop.
Existing Instance Canc_prop.
Existing Instance Disj_prop.

 
Section SepAlgFun.
  Variable key: Type.
  Variable t' : Type.
  Variable JOIN: Join t'.
  Variable Pt': Perm_alg t'.

  Instance Join_fun: Join (key -> t') :=
                  fun a b c : key -> t' => forall x, join (a x) (b x) (c x).

  Instance Perm_fun : Perm_alg (key -> t').
admit.
Defined.

  Instance Sep_fun (SA: Sep_alg t'): Sep_alg (key -> t').
admit.
Defined.

 Instance Sing_fun (SA: Sep_alg t'): Sing_alg t' -> Sing_alg (key -> t').
admit.
Defined.

 Instance Canc_fun: Canc_alg t' -> Canc_alg (key -> t').
admit.
Defined.

 Instance Disj_fun: Disj_alg t' -> Disj_alg (key -> t').
admit.
Defined.
End SepAlgFun.

Existing Instance Join_fun.
Existing Instance Perm_fun.
Existing Instance Sep_fun.
Existing Instance Sing_fun.
Existing Instance Canc_fun.
Existing Instance Disj_fun.

 

Section SepAlgPi.
  Variable I:Type.
  Variable Pi: I -> Type.
  Variable pi_J: forall i, Join (Pi i).
  Variable PA:  forall i, Perm_alg (Pi i).

  Let P := forall i:I, Pi i.

  Instance Join_pi: Join P := fun x y z => forall i:I, join (x i) (y i) (z i).

  Instance Perm_pi  : Perm_alg P.
admit.
Defined.

  Instance Sep_pi (SA : forall i:I, Sep_alg (Pi i)): Sep_alg P.
admit.
Defined.

  Instance Canc_pi: (forall i, Canc_alg (Pi i)) -> Canc_alg P.
admit.
Defined.

  Instance Disj_pi: (forall i, Disj_alg (Pi i)) -> Disj_alg P.
admit.
Defined.

End SepAlgPi.
Existing Instance Join_pi.
Existing Instance Perm_pi.
Existing Instance Sep_pi.
Existing Instance Canc_pi.
Existing Instance Disj_pi.

 
Section SepAlgSigma.
  Variable I:Type.
  Variable Sigma: I -> Type.
  Variable JOIN: forall i, Join (Sigma i).
  Variable PA: forall i, Perm_alg (Sigma i).
  Let S := sigT Sigma.

  Inductive join_sigma : S -> S -> S -> Prop :=
    j_sig_def : forall (i:I) (a b c:Sigma i),
      join a b c ->
      join_sigma (existT Sigma i a) (existT Sigma i b) (existT Sigma i c).

  Instance Join_sigma: Join S := join_sigma.

  Instance Perm_sigma: Perm_alg S.
admit.
Defined.

  Instance Sep_sigma (SA : forall i:I, Sep_alg (Sigma i)) : Sep_alg S.
admit.
Defined.

  Instance Canc_sigma: (forall i, Canc_alg (Sigma i)) -> Canc_alg S.
admit.
Defined.

  Instance Disj_sigma: (forall i, Disj_alg (Sigma i)) -> Disj_alg S.
admit.
Defined.
End SepAlgSigma.

Existing Instance Join_sigma.
Existing Instance Perm_sigma.
Existing Instance Sep_sigma.
Existing Instance Canc_sigma.
Existing Instance Disj_sigma.

 
Section SepAlgProd.

  Variables (A: Type) (Ja: Join A).
  Variables (B: Type) (Jb: Join B) .
  Variables (PAa: Perm_alg A)(PAb: Perm_alg B).

  Instance Join_prod : Join (A*B) :=
               fun (x y z:A*B) =>  join (fst x) (fst y) (fst z) /\ join (snd x) (snd y) (snd z).

  Instance Perm_prod  : Perm_alg (A*B).
  Proof.
    constructor.

     
    intros [? ?] [? ?] [? ?] [? ?] [? ?] [? ?]; simpl in *.
    f_equal; simpl; eapply join_eq; eauto.

     
    intros [? ?] [? ?] [? ?] [? ?] [? ?] [? ?] [? ?]; simpl in *.
    destruct (join_assoc H H1) as [x [? ?]].
    destruct (join_assoc H0 H2) as [y [? ?]].
    exists (x,y); simpl; repeat split; auto.

     
    intros [? ?] [? ?] [? ?] [? ?]; repeat split; simpl in *; apply join_comm; auto.

     
    intros [? ?] [? ?] [? ?] [? ?] [? ?] [? ?]; simpl in *.
    f_equal; simpl; eapply join_positivity; eauto.
 Qed.

  Instance Sep_prod (SAa: Sep_alg A) (SAb: Sep_alg B) : Sep_alg (A*B).
admit.
Defined.

  Instance Sing_prod {SAa: Sep_alg A} {SAb: Sep_alg B} {SingA: Sing_alg A}{SingB: Sing_alg B}: Sing_alg (A*B).
admit.
Defined.

  Instance Canc_prod {CAa: Canc_alg A} {CAb:  Canc_alg B}: Canc_alg (A*B).
admit.
Defined.

  Instance Disj_prod {DAa: Disj_alg A} {DAb:  Disj_alg B}: Disj_alg (A*B).
admit.
Defined.

End SepAlgProd.

Arguments Perm_prod [A] [Ja] [B] [Jb] _ _.
Arguments Sep_prod [A] [Ja] [B] [Jb] _ _.
Existing Instance Join_prod.
Existing Instance Perm_prod.
Existing Instance Sep_prod.
Existing Instance Canc_prod.
Existing Instance Disj_prod.

 
Section SepAlgSum.

  Variables (A: Type) (Ja: Join A) .
  Variables (B: Type) (Jb: Join B) .
  Variables (PAa: Perm_alg A) (PAb: Perm_alg B).
  Instance Join_sum : Join (A+B) :=
    (fun (x y z: A+B) =>
    match x, y, z with
    | inl xa, inl ya, inl za => join xa ya za
    | inr xb, inr yb, inr zb => join xb yb zb
    | _, _, _ => False
    end).

  Instance Perm_sum: Perm_alg (A+B).
admit.
Defined.

  Instance Sep_sum (SAa: Sep_alg A) (SAb: Sep_alg B): Sep_alg (A+B).
admit.
Defined.

  Instance Canc_sum {CAa: Canc_alg A} {CAb:  Canc_alg B}: Canc_alg (A+B).
admit.
Defined.

  Instance Disj_sum {DAa: Disj_alg A} {DAb:  Disj_alg B}: Disj_alg (A+B).
admit.
Defined.

End SepAlgSum.
Existing Instance Join_sum.
Existing Instance Perm_sum.
Existing Instance Sep_sum.
Existing Instance Canc_sum.
Existing Instance Disj_sum.

 
Section sa_list.

  Variables (A: Type) (Ja: Join A)  (PAa: Perm_alg A).

  Inductive list_join : list A -> list A -> list A -> Prop :=
  | lj_nil : list_join nil nil nil
  | lj_cons : forall x y z xs ys zs,
      join x y z ->
      list_join xs ys zs ->
      list_join (x::xs) (y::ys) (z::zs).

  Instance Join_list: Join (list A) := list_join.

  Instance Perm_list: Perm_alg (list A).
admit.
Defined.

  Instance Sep_list (SAa: Sep_alg A) : Sep_alg (list A).
admit.
Defined.

  Instance Canc_list {CA: Canc_alg A}: Canc_alg (list A).
admit.
Defined.

  Instance Disj_list {DAa: Disj_alg A} : Disj_alg (list A).
admit.
Defined.

End sa_list.
Existing Instance Join_list.
Existing Instance Perm_list.
Existing Instance Sep_list.
Existing Instance Canc_list.
Existing Instance Disj_list.

 
Section sa_preimage.

End sa_preimage.

Section SepAlgBijection.

End SepAlgBijection.
Require VST.msl.tree_shares.

Module Type KNOT_FULL_BASIC_INPUT.
End KNOT_FULL_BASIC_INPUT.

Module Type KNOT_FULL_SA_INPUT.
  Declare Module KI: KNOT_FULL_BASIC_INPUT.
End KNOT_FULL_SA_INPUT.
Module Export psepalg.

Import VST.msl.base.
Import VST.msl.sepalg.

Section DISCRETE.

  Instance Join_discrete (A : Type): Join A := fun a1 a2 a3 : A => False.

  Instance Perm_discrete (A: Type)  : @Perm_alg A (Join_discrete A).
admit.
Defined.
End DISCRETE.

Set Implicit Arguments.

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

End SA_LOWER.

Existing Instance Join_lower.
Existing Instance Sep_lower.

Instance Perm_option (T : Type)  : @Perm_alg (option T) (@Join_lower T (@Join_discrete T)) :=
    @Perm_lower T  (@Join_discrete T) (Perm_discrete T).

End psepalg.
Import VST.msl.boolean_alg.

Module Share : SHARE_MODEL := tree_shares.Share.

Definition share : Type := Share.t.
Export VST.msl.ageable.
Export VST.msl.base.
Export VST.msl.knot_shims.
Export VST.msl.predicates_hered.
Export VST.msl.sepalg.
Export VST.msl.functors.

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

  Definition ghost (PRED : Type) : Type :=
    list (option ({g: Ghost & {a: @G g | ghost.valid a}} * fpreds PRED)%type).

  Definition ghost_fmap (A B:Type) (f:A->B) (g:B->A)(x:ghost A) : ghost B :=
    fmap (flist (foption (fpair (fconst _) fpreds))) f g x.

  Axiom ff_ghost : functorFacts ghost ghost_fmap.
  Definition f_ghost : functor := Functor ff_ghost.

  Definition f_pre_rmap : functor :=
    fpair (ffunc (fconst address) f_res) f_ghost.

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

  Definition ghost (PRED : Type) : Type :=
    list (option ({g: Ghost & {a: @G g | ghost.valid a}} * fpreds PRED)%type).

  Definition ghost_fmap (A B:Type) (f:A->B) (g:B->A)(x:ghost A) : ghost B :=
    fmap (flist (foption (fpair (fconst _) fpreds))) f g x.

  Lemma ff_ghost : functorFacts ghost ghost_fmap.
admit.
Defined.

  Definition f_ghost : functor := Functor ff_ghost.
  Definition f_pre_rmap : functor :=
    fpair (ffunc (fconst address) f_res) f_ghost.

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
