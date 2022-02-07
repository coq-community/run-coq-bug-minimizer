cat > bug.v <<'EOF'
(* -*- mode: coq; coq-prog-args: ("-emacs" "-w" "none" "-R" "/github/workspace/VST/compcert" "compcert" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/VST/msl" "VST.msl" "-Q" "/github/workspace/VST/sepcomp" "VST.sepcomp" "-Q" "/github/workspace/VST/veric" "VST.veric" "-Q" "/github/workspace/VST/floyd" "VST.floyd" "-Q" "/github/workspace/VST/progs" "VST.progs" "-Q" "/github/workspace/VST/concurrency" "VST.concurrency" "-Q" "/github/workspace/VST/ccc26x86" "VST.ccc26x86" "-Q" "/github/workspace/VST/wand_demo" "wand_demo" "-Q" "/github/workspace/VST/sha" "sha" "-Q" "/github/workspace/VST/fcf" "fcf" "-Q" "/github/workspace/VST/hmacfcf" "hmacfcf" "-Q" "/github/workspace/VST/tweetnacl20140427" "tweetnacl20140427" "-Q" "/github/workspace/VST/hmacdrbg" "hmacdrbg" "-Q" "/github/workspace/VST/aes" "aes" "-Q" "/github/workspace/VST/mailbox" "mailbox" "-top" "bug_01") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 1507 lines to 166 lines, then from 179 lines to 1613 lines, then from 1618 lines to 283 lines, then from 296 lines to 1447 lines, then from 1447 lines to 305 lines, then from 318 lines to 2145 lines, then from 2137 lines to 360 lines, then from 373 lines to 520 lines, then from 523 lines to 388 lines, then from 401 lines to 1790 lines, then from 1792 lines to 448 lines, then from 461 lines to 1138 lines, then from 1142 lines to 444 lines, then from 457 lines to 1784 lines, then from 1789 lines to 481 lines, then from 494 lines to 2397 lines, then from 2398 lines to 682 lines, then from 689 lines to 676 lines, then from 689 lines to 1896 lines, then from 1895 lines to 680 lines, then from 693 lines to 779 lines, then from 784 lines to 693 lines, then from 706 lines to 1627 lines, then from 1629 lines to 699 lines, then from 712 lines to 1325 lines, then from 1329 lines to 717 lines, then from 731 lines to 1132 lines, then from 1138 lines to 704 lines, then from 718 lines to 1032 lines, then from 1037 lines to 706 lines, then from 720 lines to 2384 lines, then from 2385 lines to 993 lines, then from 1007 lines to 2529 lines, then from 2521 lines to 921 lines *)
(* coqc version 8.7.2 (February 2022) compiled on Feb 7 2022 16:37:53 with OCaml 4.09.1
   coqtop version 8.7.2 (February 2022)
   Modules that could not be inlined: VST.msl.tree_shares, VST.msl.predicates_hered
   Expected coqc runtime on this file: 1.011 sec *)
Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.
Module Export knot_full_variant.

Require VST.msl.base.
Import VST.msl.base.

Require VST.msl.ageable.
Import VST.msl.ageable.

Require VST.msl.functors.
Import VST.msl.functors.
Import VST.msl.functors.MixVariantFunctor.

Module Type KNOT_INPUT__MIXVARIANT_HERED_T_OTH_REL.
  Parameter F : functor.

End KNOT_INPUT__MIXVARIANT_HERED_T_OTH_REL.

Module Type KNOT__MIXVARIANT_HERED_T_OTH_REL.
  Declare Module KI: KNOT_INPUT__MIXVARIANT_HERED_T_OTH_REL.

  Parameter knot:Type.

End KNOT__MIXVARIANT_HERED_T_OTH_REL.

Module Knot_MixVariantHeredTOthRel (KI':KNOT_INPUT__MIXVARIANT_HERED_T_OTH_REL) :
  KNOT__MIXVARIANT_HERED_T_OTH_REL with Module KI:=KI'.
  Module KI := KI'.
  Import KI.
Definition sinv (n:nat) : Type.
Admitted.

  Definition knot := { n:nat & F (sinv n) }.

  Section stratifies.
  End stratifies.

End Knot_MixVariantHeredTOthRel.

Module Export KnotLemmas1.

End KnotLemmas1.

Module Export KnotLemmas2.

End KnotLemmas2.

Module KnotLemmas_MixVariantHeredTOthRel (K : KNOT__MIXVARIANT_HERED_T_OTH_REL).

End KnotLemmas_MixVariantHeredTOthRel.

Module Type KNOT_FULL_OUTPUT.
  Declare Module KI: KNOT_INPUT__MIXVARIANT_HERED_T_OTH_REL.
  Declare Module K0: KNOT__MIXVARIANT_HERED_T_OTH_REL with Module KI := KI.
End KNOT_FULL_OUTPUT.

Module Type KNOT_FULL.
  Declare Module KI: KNOT_INPUT__MIXVARIANT_HERED_T_OTH_REL.
  Declare Module KO: KNOT_FULL_OUTPUT with Module KI := KI.
Definition knot : Type.
Admitted.

End KNOT_FULL.

Module Type KNOT_FULL_LEMMAS.

End KNOT_FULL_LEMMAS.

Module KnotFull
  (KI': KNOT_INPUT__MIXVARIANT_HERED_T_OTH_REL)
  (KO': KNOT_FULL_OUTPUT with Module KI := KI'):
  KNOT_FULL with Module KI := KI' with Module KO:=KO'.
  Module Export KI:=KI'.
  Module Export KO:=KO'.
Definition knot: Type.
exact (KO.K0.knot).
Defined.

End KnotFull.
Require VST.msl.sepalg_generators.
Require VST.msl.seplog.
Require VST.veric.base.
Require VST.msl.ghost.
Require VST.msl.predicates_hered.
Require VST.msl.tree_shares.
Import VST.msl.predicates_hered.

Module Type KNOT_INPUT__COCONTRAVARIANT_HERED_T_OTH_REL.

End KNOT_INPUT__COCONTRAVARIANT_HERED_T_OTH_REL.

Module Type KNOT__COCONTRAVARIANT_HERED_T_OTH_REL.
  Declare Module KI: KNOT_INPUT__COCONTRAVARIANT_HERED_T_OTH_REL.

End KNOT__COCONTRAVARIANT_HERED_T_OTH_REL.

Module Type KNOT_INPUT__COVARIANT_HERED_PROP_OTH_REL.

  Parameter other : Type.

End KNOT_INPUT__COVARIANT_HERED_PROP_OTH_REL.

Module Type KNOT__COVARIANT_HERED_PROP_OTH_REL.
  Declare Module KI : KNOT_INPUT__COVARIANT_HERED_PROP_OTH_REL.

End KNOT__COVARIANT_HERED_PROP_OTH_REL.

Module Type KNOT_INPUT__COVARIANT_HERED_PROP_OTH.
  Parameter other : Type.

End KNOT_INPUT__COVARIANT_HERED_PROP_OTH.

Module Type KNOT__COVARIANT_HERED_PROP_OTH.
  Declare Module KI : KNOT_INPUT__COVARIANT_HERED_PROP_OTH.

End KNOT__COVARIANT_HERED_PROP_OTH.

Module Type KNOT_INPUT__COVARIANT_HERED_PROP.

End KNOT_INPUT__COVARIANT_HERED_PROP.

Module Type KNOT__COVARIANT_HERED_PROP.
  Declare Module KI : KNOT_INPUT__COVARIANT_HERED_PROP.

End KNOT__COVARIANT_HERED_PROP.

Module Type KNOT_INPUT__MIXVARIANT_HERED_PROP.

End KNOT_INPUT__MIXVARIANT_HERED_PROP.

Module Type KNOT__MIXVARIANT_HERED_PROP.
  Declare Module KI : KNOT_INPUT__MIXVARIANT_HERED_PROP.

  Parameter knot : Type.

End KNOT__MIXVARIANT_HERED_PROP.

Module Knot_CoContraVariantHeredTOthRel
  (KI': KNOT_INPUT__COCONTRAVARIANT_HERED_T_OTH_REL):
  KNOT__COCONTRAVARIANT_HERED_T_OTH_REL with Module KI:=KI'.
  Module Export KI:=KI'.

  Module Export Input.

  End Input.

End Knot_CoContraVariantHeredTOthRel.

Module Knot_CovariantHeredPropOthRel (KI':KNOT_INPUT__COVARIANT_HERED_PROP_OTH_REL)
  : KNOT__COVARIANT_HERED_PROP_OTH_REL with Module KI:=KI'.

  Module Export KI:=KI'.

  Module Export Input.
Definition F: functor.
Admitted.

    Definition other := KI.other.

    Definition T := Prop.
  End Input.

  Module K0 := knot_full_variant.Knot_MixVariantHeredTOthRel(Input).

  Module Output <: knot_full_variant.KNOT_FULL_OUTPUT with Module KI := Input.
    Module KI := Input.
    Module K0 := K0.

  End Output.

End Knot_CovariantHeredPropOthRel.

Module Knot_CovariantHeredPropOth (KI':KNOT_INPUT__COVARIANT_HERED_PROP_OTH)
  : KNOT__COVARIANT_HERED_PROP_OTH with Module KI:=KI'.
  Module Export KI:=KI'.

  Module Export Input.
Definition F: functor.
Admitted.
    Definition other := KI.other.

    Definition T := Prop.
  End Input.

  Module K0 := knot_full_variant.Knot_MixVariantHeredTOthRel(Input).

  Module Output <: knot_full_variant.KNOT_FULL_OUTPUT with Module KI := Input.
    Module KI := Input.
    Module K0 := K0.
  End Output.

End Knot_CovariantHeredPropOth.

Module Knot_CovariantHeredProp (KI':KNOT_INPUT__COVARIANT_HERED_PROP)
  : KNOT__COVARIANT_HERED_PROP with Module KI:=KI'.
  Module Export KI:=KI'.

  Module Export Input.
Definition F: functor.
Admitted.
    Definition other := unit.

    Definition T := Prop.
  End Input.

  Module K0 := knot_full_variant.Knot_MixVariantHeredTOthRel(Input).

  Module Output <: knot_full_variant.KNOT_FULL_OUTPUT with Module KI := Input.
    Module KI := Input.
    Module K0 := K0.
  End Output.

End Knot_CovariantHeredProp.

Module Knot_MixVariantHeredProp (KI':KNOT_INPUT__MIXVARIANT_HERED_PROP)
  : KNOT__MIXVARIANT_HERED_PROP with Module KI:=KI'.
  Module Export KI:=KI'.

  Module Export Input.
Definition F: functor.
Admitted.
    Definition other := unit.

    Definition T := Prop.
  End Input.

  Module K0 := knot_full_variant.Knot_MixVariantHeredTOthRel(Input).

  Module Output <: knot_full_variant.KNOT_FULL_OUTPUT with Module KI := Input.
    Module KI := Input.
    Module K0 := K0.
  End Output.

  Module K := knot_full_variant.KnotFull(Input)(Output).

  Definition knot := K.knot.

End Knot_MixVariantHeredProp.
Import VST.msl.sepalg.

Section SA_LOWER.
  Variable A : Type.
Instance Join_lower: Join (option A).
Admitted.

  Instance Perm_lower: @Perm_alg (option A) Join_lower.
Admitted.

 Instance Sep_lower: @Sep_alg _ Join_lower.
Admitted.

End SA_LOWER.

Existing Instance Join_lower.

Existing Instance Perm_lower.
Existing Instance Sep_lower.

Module Type KNOT_FULL_BASIC_INPUT.
End KNOT_FULL_BASIC_INPUT.

Module Type KNOT_FULL_SA_INPUT.
  Declare Module KI: KNOT_FULL_BASIC_INPUT.
End KNOT_FULL_SA_INPUT.
Import VST.msl.boolean_alg.

Module Share : SHARE_MODEL := tree_shares.Share.
Definition share : Type.
exact (Share.t).
Defined.
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

Module Type ADR_VAL0.
Parameter address : Type.
Parameter kind: Type.
End ADR_VAL0.

Module SimpleAdrVal (AV0: ADR_VAL0) <:
   ADR_VAL with Definition address := AV0.address
                   with Definition kind := AV0.kind.
  Import AV0.
  Definition address := address.
  Definition kind := kind.
End SimpleAdrVal.

Inductive TypeTree: Type :=
  | ConstType: Type -> TypeTree
  | Mpred: TypeTree
  | DependentType: nat -> TypeTree
  | ProdType: TypeTree -> TypeTree -> TypeTree
  | ArrowType: TypeTree -> TypeTree -> TypeTree
  | PiType: forall (I : Type), (I -> TypeTree) -> TypeTree.
Definition dependent_type_functor_rec (ts: list Type): TypeTree -> functor.
Admitted.
Definition fpreds: functor.
Admitted.

Section Finmap.

Definition finmap A := list (option A).

Import ListNotations.

Definition finmap_get {A} (m : finmap A) k := nth k m None.

Context {A} {J: Join A}.

Inductive finmap_join: Join (finmap A) :=
| finmap_join_nil_l m: finmap_join [] m m
| finmap_join_nil_r m: finmap_join m [] m
| finmap_join_cons a1 a2 m1 m2 a3 m3: join a1 a2 a3 -> finmap_join m1 m2 m3 ->
    finmap_join (a1 :: m1) (a2 :: m2) (a3 :: m3).

Global Instance Perm_finmap {P: Perm_alg A} : @Perm_alg _ finmap_join.
Admitted.

Global Instance Sep_finmap {S: Sep_alg A} : @Sep_alg _ finmap_join.
Admitted.

End Finmap.

Instance finmap_RA {RA: Ghost} : Ghost :=
  { valid m := forall i a, finmap_get m i = Some a -> valid a; Join_G := finmap_join }.
admit.
Defined.

Instance Global_Ghost {I} {RAs: I -> Ghost}: Ghost :=
  { G := forall i, finmap (@G (RAs i)); valid m := forall i, @valid finmap_RA (m i) }.
admit.
Defined.

Module Type STRAT_MODEL.
  Declare Module AV : ADR_VAL.

End STRAT_MODEL.

Module StratModel (AV' : ADR_VAL) : STRAT_MODEL with Module AV:=AV'.
  Module AV := AV'.
  Import AV.
Definition preds: functor.
Admitted.

  Inductive res (PRED : Type) : Type :=
    | NO':  forall sh: Share.t, ~(readable_share sh) -> res PRED
    | YES': forall sh: Share.t, readable_share sh -> kind -> preds PRED -> res PRED
    | PURE': kind -> preds PRED -> res PRED.
Definition res_fmap (A B:Type) (f:A->B) (g:B->A)(x:res A) : res B.
Admitted.

  Lemma ff_res : functorFacts res res_fmap.
Admitted.
Definition f_res : functor.
exact (Functor ff_res).
Defined.

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
Instance Join_res (PRED: Type) : Join (res PRED).
exact (res_join PRED).
Defined.

  Instance sa_rj : forall PRED, @Sep_alg _ (res_join PRED).
Admitted.

  Inductive ghost (PRED : Type) : Type :=
    GHOST' I (RAs: I -> Ghost) (g: @G Global_Ghost) (pds: I -> nat -> option (fpreds PRED))
      (Hv: ghost.valid g)
      (dom: forall i n pp, pds i n = Some pp -> exists a, finmap_get (g i) n = Some a).

  Program Definition ghost_fmap (A B:Type) (f:A->B) (g:B->A)(x:ghost A) : ghost B :=
    match x with
      | GHOST' _ RAs a pds _ _ =>
        GHOST' _ _ RAs a (fmap (ffunc (fconst _) (ffunc (fconst _) (foption fpreds))) f g pds) _ _
    end.
Admit Obligations.

  Lemma ff_ghost : functorFacts ghost ghost_fmap.
Admitted.
Definition f_ghost : functor.
exact (Functor ff_ghost).
Defined.

  Inductive ghost_join (PRED : Type) : f_ghost PRED -> f_ghost PRED -> f_ghost PRED -> Prop :=
    | ghost_join_I : forall A (RAs : A -> Ghost) a b c pdsa pdsb pdsc Hva Hvb Hvc doma domb domc,
        join a b c -> join pdsa pdsb pdsc ->
        ghost_join PRED (GHOST' PRED _ RAs a pdsa Hva doma) (GHOST' PRED _ RAs b pdsb Hvb domb)
                        (GHOST' PRED _ RAs c pdsc Hvc domc).
Instance Join_ghost (PRED: Type) : Join (ghost PRED).
exact (ghost_join PRED).
Defined.

  Instance sa_gj : forall PRED, @Sep_alg _ (ghost_join PRED).
Admitted.
Definition valid' A (w: (address -> res A) * ghost A) : Prop.
Admitted.

  Lemma valid'_res_map : forall A B f g m,
    valid' A m -> valid' B (fmap f_res f g oo fst m, fmap f_ghost f g (snd m)).
Admitted.

  Definition pre_rmap (A:Type) := { m:(address -> res A) * ghost A | valid' A m }.
Definition f_pre_rmap : functor.
exact (fsubset (fpair (ffunc (fconst address) f_res) f_ghost) _ valid'_res_map).
Defined.
Instance Sep_pre_rmap (A: Type): Sep_alg (pre_rmap A).
Admitted.

  Lemma pre_rmap_core: forall A (m : f_pre_rmap A),
    exists P, core m = exist (valid' A) (core (proj1_sig m)) P.
Admitted.

End StratModel.

Module Type RMAPS.
  Declare Module AV:ADR_VAL.

  Parameter rmap : Type.
  Axiom ag_rmap: ageable rmap.

End RMAPS.

Module Rmaps (AV':ADR_VAL): RMAPS with Module AV:=AV'.
  Module Export AV:=AV'.

  Module Export TyF.
  End TyF.

  Module TyFSA <: KNOT_FULL_SA_INPUT with Module KI:=TyF.
    Module KI := TyF.
  End TyFSA.

  Module K := Knot_MixVariantHeredProp(TyF).

  Definition rmap := K.knot.
Instance ag_rmap : ageable rmap.
Admitted.

End Rmaps.
Import VST.veric.base.

Inductive kind : Type := VAL : memval -> kind
                                   | LK : Z -> kind
                                   | CT: Z -> kind
                                   | FUN: funsig -> calling_convention -> kind.

Module CompCert_AV <: ADR_VAL.

Definition address := address.
Definition kind := kind.

End CompCert_AV.

Module R := Rmaps (CompCert_AV).
Export R.

Section cuof.

Context (cenv: composite_env).
Definition composite_env_complete_legal_cosu_type: Prop.
Admitted.

End cuof.

Definition hardware_alignof_env_consistent (cenv: composite_env) (ha_env: PTree.t Z): Prop.
Admitted.
Definition hardware_alignof_env_complete (cenv: composite_env) (ha_env: PTree.t Z): Prop.
Admitted.

Module Type LEGAL_ALIGNAS.

  Parameter legal_alignas_obs: Type.

End LEGAL_ALIGNAS.

Module LegalAlignasDefsGen (LegalAlignas: LEGAL_ALIGNAS).

  Import LegalAlignas.
Definition legal_alignas_env_consistent (cenv: composite_env) (ha_env: PTree.t Z) (la_env: PTree.t legal_alignas_obs): Prop.
Admitted.
Definition legal_alignas_env_complete (cenv: composite_env) (la_env: PTree.t legal_alignas_obs): Prop.
Admitted.
Definition legal_alignas_env_sound (cenv: composite_env) (ha_env: PTree.t Z) (la_env: PTree.t legal_alignas_obs): Prop.
Admitted.

End LegalAlignasDefsGen.

Module Type LEGAL_ALIGNAS_FACTS.

  Declare Module LegalAlignas: LEGAL_ALIGNAS.
  Module LegalAlignasDefs := LegalAlignasDefsGen (LegalAlignas).
Export LegalAlignas.
Export LegalAlignasDefs.

End LEGAL_ALIGNAS_FACTS.

Module LegalAlignasStrong <: LEGAL_ALIGNAS.

Section legal_alignas.
Definition legal_alignas_obs: Type.
Admitted.

End legal_alignas.

End LegalAlignasStrong.

Module LegalAlignasStrongFacts: LEGAL_ALIGNAS_FACTS with Module LegalAlignas := LegalAlignasStrong.

Module LegalAlignas := LegalAlignasStrong.
Module LegalAlignasDefs := LegalAlignasDefsGen (LegalAlignas).

End LegalAlignasStrongFacts.

Module Export LegalAlignasFacts := LegalAlignasStrongFacts.

Structure Lift := mkLift {
         lift_S: Type;
         lift_T: Type;
         lift_prod : Type;
         lift_last: Type;
         lifted:> Type;
         lift_curry: lift_T -> lift_prod -> lift_last;
         lift_uncurry_open: ((lift_S -> lift_prod) -> (lift_S -> lift_last)) -> lifted
}.

Definition Tend (S: Type) (A: Type) :=
    mkLift S A unit A
          (S -> A)
          (fun f _ => f)
          (fun f => f (fun _: S => tt)).

Canonical Structure Tarrow (A: Type) (H: Lift) :=
    mkLift (lift_S H)
      (A -> lift_T H)
      (prod A (lift_prod H))
      (lift_last H)
      ((lift_S H -> A) -> lifted H)
      (fun f x => match x with (x1,x2) => lift_curry H (f x1) x2 end)
      (fun f x => lift_uncurry_open H (fun y: lift_S H -> lift_prod H => f (fun z => (x z, y z)))).

Set Implicit Arguments.
Definition liftx {H: Lift} (f: lift_T H) : lifted H.
Admitted.

Notation "'`' x" := (liftx x) (at level 9).
Notation "'`(' x ')'" := (liftx (x : _)).
Module Export Map.
Section map.
Variables (B : Type).

Definition t := positive -> option B.
Definition get (h: t) (a:positive) : option B.
Admitted.

End map.

Definition genviron := Map.t block.

Definition venviron := Map.t (block * type).

Definition tenviron := Map.t val.

Inductive environ : Type :=
 mkEnviron: forall (ge: genviron) (ve: venviron) (te: tenviron), environ.
Definition te_of (rho: environ) : tenviron.
Admitted.

Definition mpred := pred rmap.
Definition AssertTT (A: TypeTree): TypeTree.
Admitted.
Definition super_non_expansive {A: TypeTree}
  (P: forall ts, dependent_type_functor_rec ts (AssertTT A) mpred): Prop.
Admitted.

Inductive funspec :=
   mk_funspec: funsig -> calling_convention -> forall (A: TypeTree)
     (P Q: forall ts, dependent_type_functor_rec ts (AssertTT A) mpred)
     (P_ne: super_non_expansive P) (Q_ne: super_non_expansive Q),
     funspec.
Definition composite_legal_fieldlist (co: composite): Prop.
Admitted.

Definition composite_env_legal_fieldlist env :=
  forall (id : positive) (co : composite),
    env ! id = Some co -> composite_legal_fieldlist co.

Class compspecs := mkcompspecs {
  cenv_cs : composite_env;
  cenv_consistent: composite_env_consistent cenv_cs;
  cenv_legal_fieldlist: composite_env_legal_fieldlist cenv_cs;
  cenv_legal_su: composite_env_complete_legal_cosu_type cenv_cs;
  ha_env_cs: PTree.t Z;
  ha_env_cs_consistent: hardware_alignof_env_consistent cenv_cs ha_env_cs;
  ha_env_cs_complete: hardware_alignof_env_complete cenv_cs ha_env_cs;
  la_env_cs: PTree.t legal_alignas_obs;
  la_env_cs_consistent: legal_alignas_env_consistent cenv_cs ha_env_cs la_env_cs;
  la_env_cs_complete: legal_alignas_env_complete cenv_cs la_env_cs;
  la_env_cs_sound: legal_alignas_env_sound cenv_cs ha_env_cs la_env_cs
}.

Existing Class composite_env.
Existing Instance cenv_cs.

Arguments sizeof {env} !t / .
Arguments alignof {env} !t / .

Inductive Annotation :=
  WeakAnnotation : (environ -> mpred) -> Annotation
| StrongAnnotation : (environ -> mpred) -> Annotation.

Inductive tycontext : Type :=
  mk_tycontext : forall (tyc_temps: PTree.t (type * bool))
                        (tyc_vars: PTree.t type)
                        (tyc_ret: type)
                        (tyc_globty: PTree.t type)
                        (tyc_globsp: PTree.t funspec)
                        (tyc_annot: PTree.t Annotation),
                             tycontext.

Module Export Cop2.
Definition sem_cast (t1 t2: type): val -> option val.
Admitted.
Definition sem_unary_operation
            (op: Cop.unary_operation) (ty: type) (v: val): option val.
Admitted.
Definition sem_binary_operation'
    {CS: compspecs} (op: Cop.binary_operation)
    (t1:type) (t2: type) : val -> val -> option val.
Admitted.
Definition force_val (v: option val) : val.
Admitted.

Definition force_val1 (f: val -> option val) (v: val) := force_val (f v).
Definition force_val2 (f: val -> val -> option val) (v1 v2: val) := force_val (f v1 v2).

Canonical Structure LiftEnviron := Tend environ.

Definition eval_id (id: ident) (rho: environ) := force_val (Map.get (te_of rho) id).

Definition eval_unop (op: Cop.unary_operation) (t1 : type) :=
       force_val1 (Cop2.sem_unary_operation op t1).

Definition eval_binop {CS:compspecs} (op: Cop.binary_operation) (t1 t2 : type) :=
       force_val2 (Cop2.sem_binary_operation'  op t1 t2).

Definition eval_cast (t1 t2 : type) :=
  force_val1 (sem_cast t1 t2).
Definition eval_field {CS: compspecs} (ty: type) (fld: ident) : val -> val.
Admitted.
Definition eval_var (id:ident) (ty: type) (rho: environ) : val.
Admitted.

Fixpoint eval_expr {CS: compspecs} (e: expr) : environ -> val :=
 match e with
 | Econst_int i ty => `(Vint i)
 | Econst_long i ty => `(Vlong i)
 | Econst_float f ty => `(Vfloat f)
 | Econst_single f ty => `(Vsingle f)
 | Etempvar id ty => eval_id id
 | Eaddrof a ty => eval_lvalue a
 | Eunop op a ty =>  `(eval_unop op (typeof a)) (eval_expr a)
 | Ebinop op a1 a2 ty =>
                  `(eval_binop op (typeof a1) (typeof a2)) (eval_expr a1) (eval_expr a2)
 | Ecast a ty => `(eval_cast (typeof a) ty) (eval_expr a)
 | Evar id ty => eval_var id ty
 | Ederef a ty => eval_expr a
 | Efield a i ty => `(eval_field (typeof a) i) (eval_lvalue a)
 | Esizeof t ty => `(Vptrofs (Ptrofs.repr (sizeof t)))
 | Ealignof t ty => `(Vptrofs (Ptrofs.repr (alignof t)))
 end

 with eval_lvalue {CS: compspecs} (e: expr) : environ -> val :=
 match e with
 | Evar id ty => eval_var id ty
 | Ederef a ty => eval_expr a
 | Efield a i ty => `(eval_field (typeof a) i) (eval_lvalue a)
 | _  => `Vundef
 end.

Fixpoint eval_exprlist {CS: compspecs} (et: list type) (el:list expr) : environ -> list val :=
 match et, el with
 | t::et', e::el' =>
    `(@cons val) (`force_val (`(sem_cast (typeof e) t) (eval_expr e))) (eval_exprlist et' el')
 | _, _ => `nil
 end.

Inductive tc_error :=
| op_result_type : expr -> tc_error
| arg_type : expr -> tc_error
| pp_compare_size_0 : type -> tc_error
| pp_compare_size_exceed : type -> tc_error
| invalid_cast : type -> type -> tc_error
| invalid_cast_result : type -> type -> tc_error
| invalid_expression : expr -> tc_error
| var_not_in_tycontext : tycontext -> positive  -> tc_error
| mismatch_context_type : type -> type -> tc_error
| deref_byvalue : type -> tc_error
| volatile_load : type -> tc_error
| invalid_field_access : expr -> tc_error
| invalid_composite_name: ident -> tc_error
| invalid_struct_field : ident   -> ident   -> tc_error
| invalid_lvalue : expr -> tc_error
| wrong_signature : tc_error
| int_or_ptr_type_error : tc_error
| miscellaneous_typecheck_error : tc_error.

Inductive tc_assert :=
| tc_FF: tc_error -> tc_assert
| tc_TT : tc_assert
| tc_andp': tc_assert -> tc_assert -> tc_assert
| tc_orp' : tc_assert -> tc_assert -> tc_assert
| tc_nonzero': expr -> tc_assert
| tc_iszero': expr -> tc_assert
| tc_isptr: expr -> tc_assert
| tc_test_eq': expr -> expr -> tc_assert
| tc_test_order': expr -> expr -> tc_assert
| tc_ilt': expr -> int -> tc_assert
| tc_llt': expr -> int64 -> tc_assert
| tc_Zle: expr -> Z -> tc_assert
| tc_Zge: expr -> Z -> tc_assert
| tc_samebase: expr -> expr -> tc_assert
| tc_nodivover': expr -> expr -> tc_assert
| tc_initialized: PTree.elt -> type -> tc_assert
| tc_nosignedover: (Z->Z->Z) -> expr -> expr -> tc_assert.

Definition isptr v :=
   match v with | Vptr _ _ => True | _ => False end.
Definition tc_val (ty: type) : val -> Prop.
Admitted.
Definition valid_pointer (p: val) : mpred.
Admitted.
Definition weak_valid_pointer (p: val) : mpred.
Admitted.
Export VST.msl.seplog.
Instance Nveric: NatDed mpred.
Admitted.

Definition denote_tc_iszero v : mpred :=
         match v with
         | Vint i => prop (is_true (Int.eq i Int.zero))
         | Vlong i => prop (is_true (Int64.eq (Int64.repr (Int64.unsigned i)) Int64.zero))
         | _ => FF
         end.

Definition denote_tc_nonzero v : mpred :=
         match v with
         | Vint i => prop (i <> Int.zero)
         | Vlong i =>prop (i <> Int64.zero)
         | _ => FF end.

Definition denote_tc_igt i v : mpred :=
     match v with
     | Vint i1 => prop (Int.unsigned i1 < Int.unsigned i)
     | _ => FF
     end.

Definition denote_tc_lgt l v : mpred :=
     match v with
     | Vlong l1 => prop (Int64.unsigned l1 < Int64.unsigned l)
     | _ => FF
     end.
Definition Zoffloat (f:float): option Z.
Admitted.
Definition Zofsingle (f: float32): option Z.
Admitted.

Definition denote_tc_Zge z v : mpred :=
          match v with
                     | Vfloat f => match Zoffloat f with
                                    | Some n => prop (z >= n)
                                    | None => FF
                                   end
                     | Vsingle f => match Zofsingle f with
                                    | Some n => prop (z >= n)
                                    | None => FF
                                   end
                     | _ => FF
                  end.

Definition denote_tc_Zle z v : mpred :=
          match v with
                     | Vfloat f => match Zoffloat f with
                                    | Some n => prop (z <= n)
                                    | None => FF
                                   end
                     | Vsingle f => match Zofsingle f with
                                    | Some n => prop (z <= n)
                                    | None => FF
                                   end
                     | _ => FF
                  end.

Definition sameblock v1 v2 : bool :=
         match v1, v2 with
          | Vptr b1 _, Vptr b2 _ => peq b1 b2
          | _, _ => false
         end.

Definition denote_tc_samebase v1 v2 : mpred :=
       prop (is_true (sameblock v1 v2)).

Definition denote_tc_nodivover v1 v2 : mpred :=
match v1, v2 with
          | Vint n1, Vint n2 => prop (~(n1 = Int.repr Int.min_signed /\ n2 = Int.mone))
          | Vlong n1, Vlong n2 => prop (~(n1 = Int64.repr Int64.min_signed /\ n2 = Int64.mone))
          | Vint n1, Vlong n2 => TT
          | Vlong n1, Vint n2 => prop (~ (n1 = Int64.repr Int64.min_signed  /\ n2 = Int.mone))
          | _ , _ => FF
        end.

Definition denote_tc_nosignedover (op: Z->Z->Z) v1 v2 : mpred :=
 match v1,v2 with
 | Vint n1, Vint n2 =>
   prop (Int.min_signed <= op (Int.signed n1) (Int.signed n2) <= Int.max_signed)
 | Vlong n1, Vlong n2 =>
   prop (Int64.min_signed <= op (Int64.signed n1) (Int64.signed n2) <= Int64.max_signed)
 | Vint n1, Vlong n2 =>
   prop (Int64.min_signed <= op (Int.signed n1) (Int64.signed n2) <= Int64.max_signed)
 | Vlong n1, Vint n2 =>
   prop (Int64.min_signed <= op (Int64.signed n1) (Int.signed n2) <= Int64.max_signed)
 | _, _ => FF
 end.

Definition denote_tc_initialized id ty rho : mpred :=
    prop (exists v, Map.get (te_of rho) id = Some v
               /\ tc_val ty v).

Definition denote_tc_isptr v : mpred :=
  prop (isptr v).

Definition test_eq_ptrs v1 v2 : mpred :=
  if sameblock v1 v2
  then (andp (weak_valid_pointer v1) (weak_valid_pointer v2))
  else (andp (valid_pointer v1) (valid_pointer v2)).

Definition test_order_ptrs v1 v2 : mpred :=
  if sameblock v1 v2
  then (andp (weak_valid_pointer v1) (weak_valid_pointer v2))
  else FF.

Definition denote_tc_test_eq v1 v2 : mpred :=
 match v1, v2 with
 | Vint i, Vint j =>
     if Archi.ptr64 then FF else andp (prop (i = Int.zero)) (prop (j = Int.zero))
 | Vlong i, Vlong j =>
     if Archi.ptr64 then andp (prop (i = Int64.zero)) (prop (j = Int64.zero)) else FF
 | Vint i, Vptr _ _ =>
      if Archi.ptr64 then FF else andp (prop (i = Int.zero)) (weak_valid_pointer v2)
 | Vlong i, Vptr _ _ =>
      if Archi.ptr64 then andp (prop (i = Int64.zero)) (weak_valid_pointer v2) else FF
 | Vptr _ _, Vint i =>
      if Archi.ptr64 then FF else andp (prop (i = Int.zero)) (weak_valid_pointer v1)
 | Vptr _ _, Vlong i =>
      if Archi.ptr64 then andp (prop (i = Int64.zero)) (weak_valid_pointer v1) else FF
 | Vptr _ _, Vptr _ _ =>
      test_eq_ptrs v1 v2
 | _, _ => FF
 end.

Definition denote_tc_test_order v1 v2 : mpred :=
 match v1, v2 with
 | Vint i, Vint j => if Archi.ptr64 then FF else andp (prop (i = Int.zero)) (prop (j = Int.zero))
 | Vlong i, Vlong j => if Archi.ptr64 then andp (prop (i = Int64.zero)) (prop (j = Int64.zero)) else FF
 | Vptr _ _, Vptr _ _ =>
      test_order_ptrs v1 v2
 | _, _ => FF
 end.
Definition typecheck_error (e: tc_error) : Prop.
Admitted.

Fixpoint denote_tc_assert {CS: compspecs} (a: tc_assert) : environ -> mpred :=
  match a with
  | tc_FF msg => `(prop (typecheck_error msg))
  | tc_TT => TT
  | tc_andp' b c => fun rho => andp (denote_tc_assert b rho) (denote_tc_assert c rho)
  | tc_orp' b c => `orp (denote_tc_assert b) (denote_tc_assert c)
  | tc_nonzero' e => `denote_tc_nonzero (eval_expr e)
  | tc_isptr e => `denote_tc_isptr (eval_expr e)
  | tc_test_eq' e1 e2 => `denote_tc_test_eq (eval_expr e1) (eval_expr e2)
  | tc_test_order' e1 e2 => `denote_tc_test_order (eval_expr e1) (eval_expr e2)
  | tc_ilt' e i => `(denote_tc_igt i) (eval_expr e)
  | tc_llt' e i => `(denote_tc_lgt i) (eval_expr e)
  | tc_Zle e z => `(denote_tc_Zge z) (eval_expr e)
  | tc_Zge e z => `(denote_tc_Zle z) (eval_expr e)
  | tc_samebase e1 e2 => `denote_tc_samebase (eval_expr e1) (eval_expr e2)
  | tc_nodivover' v1 v2 => `denote_tc_nodivover (eval_expr v1) (eval_expr v2)
  | tc_initialized id ty => denote_tc_initialized id ty
  | tc_iszero' e => `denote_tc_iszero (eval_expr e)
  | tc_nosignedover op e1 e2 => `(denote_tc_nosignedover op) (eval_expr e1) (eval_expr e2)
 end.

Definition fool' := @map _ Type (fun it : ident * type => mpred).
EOF
cat bug.v
opam switch create coq.8.7.2 --empty
opam switch coq.8.7.2
opam install -y coq.8.7.2
eval $(opam env)
git clone https://github.com/Alizter/VST.git
cd VST
git checkout test-6984
make veric/SeparationLogic.vo
