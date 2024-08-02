
(* -*- mode: coq; coq-prog-args: ("-emacs" "-native-compiler" "no" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/msl" "VST.msl" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/sepcomp" "VST.sepcomp" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/veric" "VST.veric" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/zlist" "VST.zlist" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/floyd" "VST.floyd" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/progs" "VST.progs" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/concurrency" "VST.concurrency" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/atomics" "VST.atomics" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/wand_demo" "wand_demo" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/sha" "sha" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/hmacfcf" "hmacfcf" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/tweetnacl20140427" "tweetnacl20140427" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/hmacdrbg" "hmacdrbg" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/aes" "aes" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/mailbox" "mailbox" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/lib" "compcert.lib" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/common" "compcert.common" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/x86_32" "compcert.x86_32" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/x86" "compcert.x86" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/cfrontend" "compcert.cfrontend" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/export" "compcert.export" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Flocq" "Flocq" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/MenhirLib" "MenhirLib" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/compcert" "compcert" "-top" "Top.bug_01") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 96 lines to 23 lines, then from 36 lines to 716 lines, then from 719 lines to 79 lines, then from 92 lines to 320 lines, then from 322 lines to 80 lines, then from 93 lines to 5188 lines, then from 5180 lines to 232 lines, then from 245 lines to 3421 lines, then from 3420 lines to 243 lines, then from 256 lines to 2589 lines, then from 2592 lines to 463 lines, then from 476 lines to 2786 lines, then from 2790 lines to 495 lines, then from 508 lines to 2004 lines, then from 2004 lines to 789 lines, then from 802 lines to 1528 lines, then from 1532 lines to 797 lines, then from 810 lines to 1190 lines, then from 1192 lines to 852 lines, then from 865 lines to 1463 lines, then from 1468 lines to 868 lines, then from 874 lines to 869 lines, then from 137 lines to 140 lines, then from 153 lines to 800 lines, then from 804 lines to 183 lines, then from 196 lines to 1519 lines, then from 1522 lines to 210 lines, then from 223 lines to 569 lines, then from 573 lines to 198 lines, then from 211 lines to 714 lines, then from 718 lines to 224 lines, then from 237 lines to 2385 lines, then from 2387 lines to 226 lines, then from 239 lines to 958 lines, then from 963 lines to 257 lines, then from 270 lines to 868 lines, then from 873 lines to 258 lines, then from 271 lines to 2216 lines, then from 2195 lines to 261 lines, then from 274 lines to 1842 lines, then from 1847 lines to 524 lines, then from 537 lines to 1226 lines, then from 1231 lines to 568 lines, then from 581 lines to 1460 lines, then from 1465 lines to 614 lines, then from 627 lines to 2448 lines, then from 2448 lines to 617 lines, then from 630 lines to 1120 lines, then from 1124 lines to 682 lines, then from 695 lines to 1670 lines, then from 1674 lines to 688 lines, then from 701 lines to 2489 lines, then from 2492 lines to 1274 lines, then from 1278 lines to 950 lines, then from 963 lines to 1085 lines, then from 1090 lines to 975 lines, then from 988 lines to 2423 lines, then from 2425 lines to 1056 lines, then from 1069 lines to 1743 lines, then from 1746 lines to 1083 lines, then from 1096 lines to 1314 lines, then from 1319 lines to 1099 lines, then from 1112 lines to 1742 lines, then from 1744 lines to 1104 lines, then from 1117 lines to 3171 lines, then from 3175 lines to 1184 lines, then from 1197 lines to 2560 lines, then from 2562 lines to 1192 lines *)
(* coqc version 8.21+alpha compiled with OCaml 4.14.1
   coqtop version runner-cabngxqim-project-4504-concurrent-0:/builds/coq/coq/_build/default,(HEAD detached at f42e33223ce00) (f42e33223ce00c4e3dcaabf7b8fa0be63c149bba)
   Expected coqc runtime on this file: 1.602 sec *)
Require VST.floyd.jmeq_lemmas.
Require VST.msl.iter_sepcon.
Require VST.veric.Memory.
Require VST.msl.Coqlib2.
Import VST.msl.msl_standard.
Definition Tsh : share.
Admitted.

Definition nonempty_share (sh: share) :=
       sepalg.nonidentity sh.
Definition readable_share (sh: share) :=
       nonempty_share (Share.glb Share.Rsh sh).

Module Export compcert_DOT_cfrontend_DOT_Ctypes_WRAPPED.
Module Export Ctypes.
Import compcert.lib.Coqlib.
Import compcert.lib.Maps.
Import compcert.common.Errors.
Import compcert.common.AST.

Inductive signedness : Type :=
  | Signed: signedness
  | Unsigned: signedness.

Inductive intsize : Type :=
  | I8: intsize
  | I16: intsize
  | I32: intsize
  | IBool: intsize.

Inductive floatsize : Type :=
  | F32: floatsize
  | F64: floatsize.

Record attr : Type := mk_attr {
  attr_volatile: bool;
  attr_alignas: option N
}.

Definition noattr := {| attr_volatile := false; attr_alignas := None |}.

Inductive type : Type :=
  | Tvoid: type
  | Tint: intsize -> signedness -> attr -> type
  | Tlong: signedness -> attr -> type
  | Tfloat: floatsize -> attr -> type
  | Tpointer: type -> attr -> type
  | Tarray: type -> Z -> attr -> type
  | Tfunction: typelist -> type -> calling_convention -> type
  | Tstruct: ident -> attr -> type
  | Tunion: ident -> attr -> type
with typelist : Type :=
  | Tnil: typelist
  | Tcons: type -> typelist -> typelist.

Inductive struct_or_union : Type := Struct | Union.

Inductive member : Type :=
  | Member_plain (id: ident) (t: type)
  | Member_bitfield (id: ident) (sz: intsize) (sg: signedness) (a: attr)
                    (width: Z) (padding: bool).
Definition members : Type.
exact (list member).
Defined.
Definition name_member (m: member) : ident.
Admitted.

Record composite : Type := {
  co_su: struct_or_union;
  co_members: members;
  co_attr: attr;
  co_sizeof: Z;
  co_alignof: Z;
  co_rank: nat;
  co_sizeof_pos: co_sizeof >= 0;
  co_alignof_two_p: exists n, co_alignof = two_power_nat n;
  co_sizeof_alignof: (co_alignof | co_sizeof)
}.
Definition composite_env : Type.
exact (PTree.t composite).
Defined.

Fixpoint field_type (id: ident) (ms: members) {struct ms} : res type.
Admitted.
Fixpoint rank_type (ce: composite_env) (t: type) : nat.
Admitted.

Definition composite_env_consistent (env: composite_env) : Prop.
Admitted.

End Ctypes.
Module Export compcert.
Module Export cfrontend.
Module Export Ctypes.
Include compcert_DOT_cfrontend_DOT_Ctypes_WRAPPED.Ctypes.
End Ctypes.
Module Export coqlib4.
Import compcert.lib.Coqlib.

Lemma Zlength_repeat : forall {A} (x : A) n, Zlength (repeat x n) = Z.of_nat n.
Admitted.

End coqlib4.
Module VST_DOT_veric_DOT_base_WRAPPED.
Module Export base.
Export compcert.lib.Coqlib.
Export compcert.common.AST.
Export compcert.common.Values.
Export compcert.common.Memdata.
Export VST.msl.Coqlib2.
End base.

End VST_DOT_veric_DOT_base_WRAPPED.
Module Export VST.
Module Export veric.
Module base.
Include VST_DOT_veric_DOT_base_WRAPPED.base.
End base.
Module Export composite_compute.
Import Coq.Structures.Orders.
Import VST.veric.base.

Module Export composite_reorder.

Module CompositeRankOrder <: TotalLeBool.
  Definition t := (positive * composite)%type.
  Definition leb (x y: t) := Nat.leb (co_rank (snd y)) (co_rank (snd x)).

  Theorem leb_total : forall a1 a2, leb a1 a2 = true \/ leb a2 a1 = true.
Admitted.

End CompositeRankOrder.

End composite_reorder.

Section cuof.

Context (cenv: composite_env).
Definition composite_env_complete_legal_cosu_type: Prop.
Admitted.

End cuof.

End composite_compute.
Module Export align_mem.
Import VST.veric.base.
Import compcert.lib.Maps.

Definition hardware_alignof_env_consistent (cenv: composite_env) (ha_env: PTree.t Z): Prop.
Admitted.
Definition hardware_alignof_env_complete (cenv: composite_env) (ha_env: PTree.t Z): Prop.
Admitted.

Module Type HARDWARE_ALIGNOF_FACTS.

End HARDWARE_ALIGNOF_FACTS.

Module hardware_alignof_facts: HARDWARE_ALIGNOF_FACTS.

End hardware_alignof_facts.

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

Module LegalAlignasStrict <: LEGAL_ALIGNAS.

Section legal_alignas.
Definition legal_alignas_obs: Type.
Admitted.

End legal_alignas.

End LegalAlignasStrict.

Module LegalAlignasStrictFacts: LEGAL_ALIGNAS_FACTS with Module LegalAlignas := LegalAlignasStrict.

Module LegalAlignas := LegalAlignasStrict.
Module LegalAlignasDefs := LegalAlignasDefsGen (LegalAlignas).

End LegalAlignasStrictFacts.

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

End align_mem.
Module Export compspecs.
Import VST.veric.base.
Import compcert.lib.Maps.
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
End compspecs.
Module Export rmaps.
Import VST.msl.msl_standard.
Import VST.msl.ghost.

Module Type ADR_VAL.
Parameter address : Type.

Parameter kind: Type.
End ADR_VAL.

Inductive TypeTree: Type :=
  | ConstType: Type -> TypeTree
  | CompspecsType: TypeTree
  | Mpred: TypeTree
  | DependentType: nat -> TypeTree
  | ProdType: TypeTree -> TypeTree -> TypeTree
  | ArrowType: TypeTree -> TypeTree -> TypeTree
  | SigType: forall (I : Type), (I -> TypeTree) -> TypeTree
  | PiType: forall (I : Type), (I -> TypeTree) -> TypeTree
  | ListType: TypeTree -> TypeTree.
Definition dependent_type_functor_rec (ts: list Type): TypeTree -> functor.
exact (fix dtfr (T: TypeTree): functor :=
  match T with
  | ConstType A => fconst A
  | CompspecsType => fconst compspecs
  | Mpred => fidentity
  | DependentType n => fconst (nth n ts unit)
  | ProdType T1 T2 => fpair (dtfr T1) (dtfr T2)
  | ArrowType T1 T2 => ffunc (dtfr T1) (dtfr T2)
  | SigType _ f => fsig (fun i => dtfr (f i))
  | PiType _ f => fpi (fun i => dtfr (f i))
  | ListType T => flist (dtfr T)
  end).
Defined.
Definition fpreds: functor.
Admitted.

Module Type STRAT_MODEL.
  Declare Module AV : ADR_VAL.
  Import AV.
Definition f_res : functor.
Admitted.
Definition ghost (PRED : Type) : Type.
exact (list (option ({g: Ghost & {a: @G g | ghost.valid a}} * fpreds PRED)%type)).
Defined.
Definition ghost_fmap (A B:Type) (f:A->B) (g:B->A)(x:ghost A) : ghost B.
Admitted.

  Axiom ff_ghost : functorFacts ghost ghost_fmap.
Definition f_ghost : functor.
exact (Functor ff_ghost).
Defined.

  #[global] Instance preds_join PRED : Join _ := Join_equiv (fpreds PRED).
Definition f_pre_rmap : functor.
exact (fpair (ffunc (fconst address) f_res) f_ghost).
Defined.
#[global] Instance Join_pre_rmap (A: Type) : Join (f_pre_rmap A).
Admitted.
  #[global] Declare Instance Sep_pre_rmap: forall (A: Type), Sep_alg (f_pre_rmap A).
  Parameter paf_pre_rmap : @pafunctor f_pre_rmap Join_pre_rmap.

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
Definition ghost (PRED : Type) : Type.
exact (list (option ({g: Ghost & {a: @G g | ghost.valid a}} * fpreds PRED)%type)).
Defined.
Definition ghost_fmap (A B:Type) (f:A->B) (g:B->A)(x:ghost A) : ghost B.
Admitted.

  Lemma ff_ghost : functorFacts ghost ghost_fmap.
Admitted.
Definition f_ghost : functor.
exact (Functor ff_ghost).
Defined.

  #[global] Instance preds_join PRED : Join _ := Join_equiv (fpreds PRED).

  Definition pre_rmap (A:Type) := ((address -> res A) * ghost A)%type.
Definition f_pre_rmap : functor.
exact (fpair (ffunc (fconst address) f_res) f_ghost).
Defined.
#[global] Instance Join_pre_rmap (A: Type) : Join (pre_rmap A).
Admitted.
Definition paf_pre_rmap : @pafunctor f_pre_rmap Join_pre_rmap.
Admitted.
Definition Sep_pre_rmap (A: Type): Sep_alg (pre_rmap A).
Admitted.

End StratModel.

Module Type RMAPS.
  Declare Module AV:ADR_VAL.
  Import AV.

  Parameter rmap : Type.
  Axiom Join_rmap: Join rmap.
#[global] Existing Instance Join_rmap.
  Axiom Perm_rmap: Perm_alg rmap.
#[global] Existing Instance Perm_rmap.
  Axiom Sep_rmap: Sep_alg rmap.
#[global] Existing Instance Sep_rmap.
  Axiom ag_rmap: ageable rmap.
#[global] Existing Instance ag_rmap.
  Axiom Age_rmap: Age_alg rmap.
#[global] Existing Instance Age_rmap.
  Axiom Ext_rmap: Ext_ord rmap.
#[global] Existing Instance Ext_rmap.
  Axiom ExtA_rmap: Ext_alg rmap.
#[global] Existing Instance ExtA_rmap.

  Inductive preds : Type :=
    SomeP : forall A : TypeTree,
      (forall ts: list Type, dependent_type_functor_rec ts A (pred rmap)) -> preds.

  Definition NoneP := SomeP (ConstType unit) (fun _ => tt).

  Inductive resource : Type :=
    | NO: forall sh: Share.t, ~(readable_share sh) -> resource
    | YES: forall sh: Share.t, readable_share sh -> kind -> preds -> resource
    | PURE: kind -> preds -> resource.
#[global] Instance Join_resource: Join resource.
Admitted.
Definition ghost : Type.
exact (list (option ({g: Ghost & {a: @G g | ghost.valid a}} * preds)%type)).
Defined.

  #[global] Instance preds_join : Join _ := Join_equiv preds.
Definition ghost_fmap (f g:pred rmap -> pred rmap)(x:ghost) : ghost.
Admitted.
Definition resource_at (phi:rmap) : address -> resource.
Admitted.
  Infix "@" := resource_at (at level 50, no associativity).
Definition ghost_of (phi:rmap) : ghost.
Admitted.

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

    Definition Rel A (r1 r2 : f_pre_rmap A) := fst r1 = fst r2 /\ join_sub (snd r1) (snd r2).
    Lemma Rel_fmap :
      forall (A B : Type) (f1 : A -> B) (f2 : B -> A) (x y : F A),
      Rel A x y -> Rel B (fmap F f1 f2 x) (fmap F f1 f2 y).
Admitted.
    Lemma Rel_refl : forall (A : Type) (x : F A), Rel A x x.
Admitted.
    Lemma Rel_trans :
      forall (A : Type) (x y z : F A),
      Rel A x y -> Rel A y z -> Rel A x z.
Admitted.
  End TyF.

  Module TyFSA <: KNOT_FULL_SA_INPUT with Module KI:=TyF.
    Module KI := TyF.
#[global] Instance Join_F: forall A, Join (F A).
exact (_).
Defined.
Definition Perm_F : forall A, Perm_alg (F A).
Admitted.
    Definition Sep_F := Sep_pre_rmap.
    Definition paf_F := paf_pre_rmap.

    Lemma Rel_join_commut : forall {A} {x y z z' : F A}, join x y z ->
      Rel A z z' -> exists x', Rel A x x' /\ join x' y z'.
Admitted.

    Lemma join_Rel_commut : forall {A} {x x' y' z' : F A}, Rel A x x' ->
      join x' y' z' -> exists z, join x y' z /\ Rel A z z'.
Admitted.

    Lemma id_exists : forall {A} (x : F A), exists e,
      identity e /\ unit_for e x.
Admitted.

  End TyFSA.

  Module K := Knot_MixVariantHeredProp(TyF).

  Module KA <: KNOT_ASSM with Module KI := TyF with Module KSAI := TyFSA
    with Module K := K.
    Module KI := TyF.
    Module KSAI := TyFSA.
    Module K := K.
    Import K.

    Lemma approx_core : forall n f,
      core(Sep_alg := Sep_pre_rmap predicate) (fmap f_pre_rmap (approx n) (approx n) f) = fmap f_pre_rmap (approx n) (approx n) (core(Sep_alg := Sep_pre_rmap predicate) f).
Admitted.

  End KA.

  Definition rmap := K.knot.
#[global] Instance Join_rmap : Join rmap.
Admitted.
#[global] Instance Perm_rmap : Perm_alg rmap.
Admitted.
#[global] Instance Sep_rmap : Sep_alg rmap.
Admitted.
#[global] Instance ag_rmap : ageable rmap.
Admitted.
#[global] Instance Age_rmap : Age_alg rmap.
Admitted.
#[global] Instance Ext_rmap : Ext_ord rmap.
Admitted.
#[global] Instance ExtA_rmap : Ext_alg rmap.
Admitted.

  Inductive preds : Type :=
    SomeP : forall A : TypeTree,
    (forall ts: list Type, dependent_type_functor_rec ts A (pred rmap)) -> preds.

  Definition NoneP := SomeP (ConstType unit) (fun _ => tt).

  Inductive resource : Type :=
    | NO: forall sh: Share.t, ~ readable_share sh -> resource
    | YES: forall sh: Share.t, readable_share sh -> kind -> preds -> resource
    | PURE: kind -> preds -> resource.
Definition ghost : Type.
exact (list (option ({g: Ghost & {a: @G g | ghost.valid a}} * preds)%type)).
Defined.
#[global] Instance Join_resource: Join resource.
Admitted.

  #[global] Instance preds_join : Join _ := Join_equiv preds.
Definition ghost_fmap (f g:pred rmap -> pred rmap)(x:ghost) : ghost.
Admitted.
Definition resource_at (phi:rmap) : address -> resource.
Admitted.
Definition ghost_of (phi:rmap) : ghost.
Admitted.

  Program Definition approx (n:nat) (p: (pred rmap)) : (pred rmap) :=
    fun w => level w < n /\ p w.
Admit Obligations.

End Rmaps.
Import VST.veric.base.
Import compcert.cfrontend.Ctypes.
Export VST.veric.Memory.

Definition typesig := (list type * type)%type.

Inductive kind : Type := VAL : memval -> kind
                                   | LK : forall n i : Z, kind
                                   | FUN: typesig -> calling_convention -> kind.

Module CompCert_AV <: ADR_VAL.

Definition address := address.
Definition kind := kind.

End CompCert_AV.

Module R := Rmaps (CompCert_AV).
Export R.
Module Export Map.
Section map.
Variables (B : Type).

Definition t := positive -> option B.

End map.

Section FUNSPEC.

Definition genviron := Map.t block.

Definition venviron := Map.t (block * type).

Definition tenviron := Map.t val.

Inductive environ : Type :=
 mkEnviron: forall (ge: genviron) (ve: venviron) (te: tenviron), environ.

Definition mpred := pred rmap.

Definition argsEnviron:Type := genviron * (list val).
Definition AssertTT (A: TypeTree): TypeTree.
exact (ArrowType A (ArrowType (ConstType environ) Mpred)).
Defined.
Definition ArgsTT (A: TypeTree): TypeTree.
exact (ArrowType A (ArrowType (ConstType argsEnviron) Mpred)).
Defined.
Definition super_non_expansive {A: TypeTree}
  (P: forall ts, dependent_type_functor_rec ts (AssertTT A) mpred): Prop.
Admitted.
Definition args_super_non_expansive {A: TypeTree}
  (P: forall ts, dependent_type_functor_rec ts (ArgsTT A) mpred): Prop.
Admitted.
Definition const_super_non_expansive: forall (T: Type) P,
  @super_non_expansive (ConstType T) P.
Admitted.
Definition args_const_super_non_expansive: forall (T: Type) P,
  @args_super_non_expansive (ConstType T) P.
Admitted.

Inductive funspec :=
   mk_funspec: typesig -> calling_convention -> forall (A: TypeTree)
     (P: forall ts, dependent_type_functor_rec ts (ArgsTT A) mpred)
     (Q: forall ts, dependent_type_functor_rec ts (AssertTT A) mpred)
     (P_ne: args_super_non_expansive P) (Q_ne: super_non_expansive Q),
     funspec.

End FUNSPEC.

Program Definition noat (l: AV.address) : pred rmap :=
    fun m => identity (m @ l).
Admit Obligations.
Module Export own.
Local Open Scope pred.

Notation ghost_approx m := (ghost_fmap (approx (level m)) (approx (level m))).

Program Definition ghost_is g: pred rmap :=
  fun m => join_sub (ghost_approx m g) (ghost_of m).
Admit Obligations.

Definition Own g: pred rmap := allp noat && ghost_is g.

Program Definition bupd (P: pred rmap): pred rmap :=
  fun m => forall c, joins (ghost_of m) (ghost_approx m c) ->
    exists b, joins b (ghost_approx m c) /\
    exists m', level m' = level m /\ resource_at m' = resource_at m /\ ghost_of m' = b /\ P m'.
Admit Obligations.

Lemma bupd_intro: forall P, P |-- bupd P.
Admitted.

Lemma bupd_mono: forall P Q, (P |-- Q) -> bupd P |-- bupd Q.
Admitted.

Lemma bupd_frame_r: forall P Q, bupd P * Q |-- bupd (P * Q).
Admitted.

Lemma bupd_trans: forall P, bupd (bupd P) |-- bupd P.
Admitted.

Definition singleton {A} k (x : A) : list (option A) := repeat None k ++ Some x :: nil.

Definition gname := nat.

Definition own {RA: Ghost} (n: gname) (a: G) (pp: preds) :=
  EX v : _, Own (singleton n (existT _ RA (exist _ a v), pp)).

Lemma map_repeat : forall {A B} (f : A -> B) x n, map f (repeat x n) = repeat (f x) n.
Admitted.

Lemma ghost_alloc: forall {RA: Ghost} a pp, ghost.valid a ->
  emp |-- bupd (EX g, own g a pp).
Admitted.

Lemma ghost_update_ND: forall {RA: Ghost} g (a: G) B pp,
  fp_update_ND a B -> own g a pp |-- bupd (EX b : _, !!(B b) && own g b pp).
Admitted.
Import VST.msl.iter_sepcon.

Notation "|==> P" := (own.bupd P) (at level 99, P at level 200): pred.

#[global] Program Instance exclusive_PCM A : Ghost :=
  { valid a := True; Join_G := Join_lower (Join_discrete A) }.

Class PCM_order `{P : Ghost} (ord : G -> G -> Prop) := { ord_preorder : PreOrder ord;
  ord_lub : forall a b c, ord a c -> ord b c -> {c' | join a b c' /\ ord c' c};
  join_ord : forall a b c, join a b c -> ord a c /\ ord b c; ord_join : forall a b, ord b a -> join a b a }.

Section Snapshot.

Context `{ORD : PCM_order}.

Global Program Instance snap_PCM : Ghost :=
  { valid _ := True; Join_G a b c := sepalg.join (fst a) (fst b) (fst c) /\
      if eq_dec (fst a) Share.bot then if eq_dec (fst b) Share.bot then join (snd a) (snd b) (snd c)
        else ord (snd a) (snd b) /\ snd c = snd b else snd c = snd a /\
          if eq_dec (fst b) Share.bot then ord (snd b) (snd a) else snd c = snd b }.
Admit Obligations.

Definition ghost_snap (a : @G P) p := own p (Share.bot, a) NoneP.

Definition ghost_master sh (a : @G P) p := own p (sh, a) NoneP.

Lemma master_update : forall v v' p, ord v v' -> ghost_master Tsh v p |-- |==> ghost_master Tsh v' p.
Admitted.

Lemma make_snap : forall (sh : share) v p, ghost_master sh v p |-- |==> ghost_snap v p * ghost_master sh v p.
Admitted.

Lemma ghost_snap_forget : forall v1 v2 p, ord v1 v2 -> ghost_snap v2 p |-- |==> ghost_snap v1 p.
Admitted.

Definition ghost_master1 a p := ghost_master Tsh a p.

End Snapshot.

#[global] Program Instance discrete_PCM (A : Type) : Ghost := { valid a := True;
  Join_G := Join_equiv A }.
Import VST.zlist.sublist.
Import ListNotations.

Section Invariants.

#[global] Program Instance unit_PCM : Ghost := { valid a := True; Join_G a b c := True }.
Admit Obligations.

Definition pred_of (P : mpred) := SomeP rmaps.Mpred (fun _ => P).

Definition agree g (P : mpred) : mpred := own(RA := unit_PCM) g tt (pred_of P).

Lemma agree_dup : forall g P, (agree g P = agree g P * agree g P)%pred.
Admitted.

Inductive list_join {P : Ghost} : Join (list (option G)) :=
  | list_join_nil_l m: list_join nil m m
  | list_join_nil_r m: list_join m nil m
  | list_join_cons a1 a2 m1 m2 a3 m3: join a1 a2 a3 -> list_join m1 m2 m3 ->
      list_join (a1 :: m1) (a2 :: m2) (a3 :: m3).
#[global] Existing Instance list_join.

#[global] Program Instance list_PCM (P : Ghost) : Ghost := { valid a := True; Join_G := list_join }.
Admit Obligations.

Definition ghost_list {P : Ghost} g l := own(RA := list_PCM P) g l NoneP.

Definition list_singleton {A} n (a : A) := repeat None n ++ [Some a].

Definition list_incl {A} (l1 l2 : list (option A)) := (length l1 <= length l2)%nat /\
  forall n a, nth n l1 None = Some a -> nth n l2 None = Some a.

Lemma app_nth : forall {A} n l1 l2 (d : A),
  nth n (l1 ++ l2) d = if lt_dec n (length l1) then nth n l1 d else nth (n - length l1) l2 d.
Admitted.

Lemma list_join_over : forall {P : Ghost} l l1 l2 l1', (length l <= length l1)%nat ->
  list_join l l1 l1' -> list_join l (l1 ++ l2) (l1' ++ l2).
Admitted.

Lemma list_join_length : forall {P : Ghost} l1 l2 l3, list_join l1 l2 l3 ->
  (length l1 <= length l3)%nat.
Admitted.

Lemma list_join_filler : forall {P : Ghost} l1 l2 l3 n, list_join l1 l2 l3 ->
  (n <= length l3 - length l1)%nat -> list_join (l1 ++ repeat None n) l2 l3.
Admitted.

#[global] Instance list_order A : @PCM_order (list_PCM (discrete_PCM A)) list_incl.
Admitted.

Import Coq.Sets.Ensembles.

Global Arguments Union {_} _ _.
Global Arguments Disjoint {_} _ _.

#[global] Polymorphic Program Instance set_PCM : Ghost := { valid := fun _ : Ensemble nat => True;
  Join_G a b c := Disjoint a b /\ c = Union a b }.
Admit Obligations.

Definition ghost_set g s := own(RA := set_PCM) g s NoneP.

Definition iname := nat.

Class invG := { g_inv : gname; g_en : gname; g_dis : gname }.

Context {inv_names : invG}.

Definition master_list {A} g (l : list (option A)) := ghost_master1(ORD := list_order A) l g.
#[global] Instance token_PCM : Ghost.
exact (exclusive_PCM unit).
Defined.

Fixpoint iter_sepcon {A} (p : A -> mpred) l :=
  match l with
    | nil => emp
    | x :: xl => (p x * iter_sepcon p xl)%pred
  end.

Typeclasses eauto := 1.
#[global] Instance Inhabitant_mpred : Inhabitant mpred.
Admitted.
Definition wsat : mpred.
exact ((EX I : list mpred, EX lg : list gname, EX lb : list (option bool),
  !!(length lg = length I /\ length lb = length I) &&
  master_list g_inv (map (fun i => match Znth i lb with Some _ => Some (Znth i lg)
                                   | None => None end) (upto (length I))) *
  ghost_list g_dis (map (fun o => match o with Some true => Some (Some tt) | _ => None end) lb) *
  ghost_set g_en (fun i : iname => nth i lb None = Some false) *
  iter_sepcon (fun i => match Znth i lb with
                        | Some true => agree (Znth i lg) (Znth i I) * |> Znth i I
                        | Some false => agree (Znth i lg) (Znth i I)
                        | _ => emp end) (upto (length I)))%pred).
Defined.

Definition invariant (i : iname) P : mpred := (EX g : gname,
  ghost_snap(ORD := list_order _) (list_singleton i g) g_inv * agree g P)%pred.

Lemma Zlength_eq : forall {A B} (l1 : list A) (l2 : list B),
  Zlength l1 = Zlength l2 <-> length l1 = length l2.
Admitted.

#[global] Instance list_Perm {P : Ghost} : Perm_alg (list (option G)).
Admitted.

Lemma nth_upto : forall m n d, (n < m)%nat -> nth n (upto m) d = Z.of_nat n.
Admitted.

Lemma list_incl_singleton : forall {A} n (a : A) l,
  list_incl (list_singleton n a) l <-> nth n l None = Some a.
Admitted.

Ltac view_shift H := eapply derives_trans; [apply sepcon_derives, derives_refl; apply H
  | eapply derives_trans; [apply bupd_frame_r | eapply derives_trans, bupd_trans; apply bupd_mono]].

Lemma iter_sepcon_app:
  forall {B} p (l1 l2 : list B), (iter_sepcon p (l1 ++ l2) = iter_sepcon p l1 * iter_sepcon p l2)%pred.
Admitted.

Lemma iter_sepcon_func_strong: forall {A} (l : list A) P Q, (forall x, List.In x l -> P x = Q x) -> iter_sepcon P l = iter_sepcon Q l.
Admitted.

Lemma iter_sepcon_emp': forall {B} p (l : list B), (forall x, List.In x l -> p x = emp) -> iter_sepcon p l = emp.
Admitted.

Lemma wsat_alloc_dep : forall P, wsat * (ALL i, |> P i) |-- |==> wsat * EX i : _, invariant i (P i).
Proof.
  intros; unfold wsat.
  rewrite !exp_sepcon1; apply exp_left; intro l.
  rewrite !exp_sepcon1; apply exp_left; intro lg.
  rewrite !exp_sepcon1; apply exp_left; intro lb.
  rewrite !sepcon_andp_prop1; apply prop_andp_left; intros [].
  rewrite (sepcon_comm _ (ghost_list _ _)), !sepcon_assoc.
  view_shift (ghost_update_ND(RA := list_PCM token_PCM) g_dis (map
     (fun o => match o with Some true => Some (Some tt) | _ => None end) lb)
     (fun l => exists i, l =
      map (fun o => match o with Some true => Some (Some tt) | _ => None end)
          ((lb ++ repeat None i) ++ [Some true]))).
  {
 intros ? (? & ? & _).
    exists (map (fun o => match o with Some true => Some (Some tt) | _ => None end)
      ((lb ++ repeat None (length x - length lb)) ++ [Some true])).
    split; [eauto|].
    exists (x ++ [Some (Some tt)]); split; simpl; auto.
    erewrite !map_app, own.map_repeat; simpl.
    pose proof (list_join_length _ _ _ H1) as Hlen.
    rewrite map_length in Hlen.
    apply join_comm in H1.
    pose proof (list_join_length _ _ _ H1) as Hlen'.
    apply (join_comm(Perm_alg := list_Perm)), (list_join_over c).
    {
 erewrite app_length, map_length, repeat_length, Nat.add_comm, Nat.sub_add; auto.
}
    apply (join_comm(Perm_alg := list_Perm)), (list_join_filler(P := token_PCM));
      [|rewrite map_length; auto].
    apply join_comm in H1; auto.
}
  rewrite exp_sepcon1; apply exp_left; intro.
  rewrite !sepcon_andp_prop1; apply prop_andp_left; intros [i ?]; subst.
  eapply derives_trans with (emp * _)%pred; [rewrite emp_sepcon; apply derives_refl|].
  set (P' := P (length lg + i)%nat).
  view_shift (ghost_alloc(RA := unit_PCM) tt (pred_of P')); [simpl; auto|].
  rewrite !exp_sepcon1; apply exp_left; intro g.
  replace (own(RA := unit_PCM) g tt (pred_of P')) with (agree g P') by reflexivity.
  rewrite agree_dup.
  assert (Zlength lg = Zlength l) as Hlg by (apply Zlength_eq; auto).
  assert (Zlength lb = Zlength l) as Hlb by (apply Zlength_eq; auto).
  rewrite <- !sepcon_assoc, (sepcon_comm _ (master_list _ _)), !sepcon_assoc.
  view_shift (master_update(ORD := list_order _) ((map (fun i0 : Z =>
      match Znth i0 lb with Some _ => Some (Znth i0 lg) | None => None end) (upto (Datatypes.length l))))
        (map (fun j => match Znth j ((lb ++ repeat None i) ++ [Some true]) with
                       | Some _ => Some (Znth j ((lg ++ repeat O i) ++ [g]))
                       | None => None
                       end) (upto (length ((l ++ repeat emp i) ++ [P']))))).
  {
 rewrite <- !app_assoc, app_length, upto_app, map_app.
    split.
    {
 erewrite app_length, !map_length; lia.
}
    intros ?? Hn.
    erewrite app_nth, map_length.
    if_tac; [|erewrite nth_overflow in Hn by (rewrite map_length; lia); discriminate].
    erewrite nth_map' with (d' := 0) in * by auto.
    erewrite upto_length in *.
    assert (Z.of_nat n < Zlength l).
    {
 rewrite Zlength_correct; apply Nat2Z.inj_lt; auto.
}
    erewrite nth_upto in * by auto.
    erewrite !app_Znth1 by lia; auto.
}
  view_shift (make_snap(ORD := list_order gname)).
  rewrite !sepcon_assoc.
  view_shift (ghost_snap_forget(ORD := list_order _) (list_singleton (length lg + i) g)).
  {
 apply list_incl_singleton.
    erewrite app_length, upto_app, map_app, app_nth2; erewrite map_length, upto_length, app_length,
      repeat_length; try lia.
    replace (_ - _)%nat with O by lia; simpl.
    rewrite Nat2Z.inj_add, Z.add_0_r.
    rewrite !app_Znth2; erewrite !Zlength_app, !coqlib4.Zlength_repeat, <- Zlength_correct; try lia.
    replace (_ - _) with 0 by lia; replace (_ - _) with 0 by lia; auto.
}
  eapply derives_trans, bupd_intro.
  apply exp_right with ((l ++ repeat emp i) ++ [P']).
  rewrite exp_sepcon1; apply exp_right with ((lg ++ repeat O i) ++ [g]).
  rewrite exp_sepcon1; apply exp_right with ((lb ++ repeat None i) ++ [Some true]).
  erewrite !(app_length (_ ++ _)); simpl.
  erewrite prop_true_andp by (erewrite !app_length, !repeat_length; lia).
  erewrite upto_app, iter_sepcon_app; simpl.
  erewrite Z.add_0_r, <- Zlength_correct, !app_Znth2; erewrite !Zlength_app, !coqlib4.Zlength_repeat; try lia.
  erewrite Hlg, Hlb, Zminus_diag, !Znth_0_cons.
  rewrite sepcon_comm, !sepcon_assoc; apply sepcon_derives; [apply derives_refl|].
  rewrite <- sepcon_assoc, sepcon_comm, sepcon_assoc; apply sepcon_derives; [apply derives_refl|].
  rewrite sepcon_assoc; apply sepcon_derives.
  {
 match goal with |-?P |-- ?Q => replace P with Q; [apply derives_refl|] end.
    f_equal.
extensionality; apply prop_ext; split; intro X.
    -
 rewrite !app_nth, nth_repeat in X.
      repeat destruct (lt_dec _ _); auto; try discriminate.
      destruct (x - _)%nat; [|destruct n0]; inv X.
    -
 destruct (lt_dec x (length lb)).
      rewrite !app_nth, app_length.
      destruct (lt_dec _ _); [|lia].
      destruct (lt_dec _ _); [auto | lia].
      {
 rewrite nth_overflow in X by lia; discriminate.
}
 }
  erewrite app_length, upto_app, iter_sepcon_app.
  rewrite sepcon_assoc; apply sepcon_derives.
  -
 eapply derives_trans with (_ * emp)%pred; [rewrite sepcon_emp; apply derives_refl|].
    apply sepcon_derives.
    +
 erewrite iter_sepcon_func_strong; auto.
      intros ??%In_upto.
      rewrite <- Zlength_correct in *.
      rewrite <- !app_assoc, !app_Znth1 by (rewrite ?Zlength_app; lia); auto.
    +
 rewrite iter_sepcon_emp'; auto.
      intros ? Hin.
      eapply in_map_iff in Hin as (? & ? & Hin%In_upto); subst.
      rewrite <- Zlength_correct, coqlib4.Zlength_repeat in Hin.
      rewrite <- Zlength_correct, <- app_assoc, app_Znth2 by lia.
      erewrite app_Znth1 by (rewrite coqlib4.Zlength_repeat; lia).
      unfold Znth; destruct (Z_lt_dec _ _); auto.
      rewrite nth_repeat; auto.
  -
 unfold invariant.
    rewrite emp_sepcon, !exp_sepcon2; apply exp_right with (length lg + i)%nat.
    rewrite !exp_sepcon2; apply exp_right with g.
    rewrite <- !sepcon_assoc, sepcon_comm, !sepcon_assoc; apply sepcon_derives; [apply derives_refl|].
    apply sepcon_derives, derives_refl.
    eapply allp_left, derives_refl.
Qed.

End Invariants.
Definition NDmk_funspec (f: typesig) (cc: calling_convention)
  (A: Type) (Pre: A -> argsEnviron -> mpred) (Post: A -> environ -> mpred): funspec.
exact (mk_funspec f cc (rmaps.ConstType A) (fun _ => Pre) (fun _ => Post)
             (args_const_super_non_expansive _ _) (const_super_non_expansive _ _)).
Defined.
Import compcert.lib.Maps.

Section cs_preserve.

Context (cs_from cs_to: compspecs).
Definition test_aux (b: bool) (i: ident): bool.
Admitted.
Fixpoint cs_preserve_type (coeq: PTree.t bool) (t: type): bool.
exact (match t with
  | Tarray t0 _ _ => cs_preserve_type coeq t0
  | Tstruct id _ => match coeq ! id with | Some b => test_aux b id | _ => false end
  | Tunion id _ => match coeq ! id with | Some b => test_aux b id | _ => false end
  | _ => true
  end).
Defined.
Fixpoint cs_preserve_members (coeq: PTree.t bool) (m: members): bool.
Admitted.

Class change_composite_env: Type := {
  coeq: PTree.t bool;
  coeq_consistent:
    forall i co b,
      (@cenv_cs cs_to) ! i = Some co ->
      coeq ! i = Some b ->
      b = cs_preserve_members coeq (co_members co);
  coeq_complete:
    forall i,
      (exists co, (@cenv_cs cs_to) ! i = Some co) <->
      (exists b, coeq ! i = Some b)
}.

End cs_preserve.
Export VST.floyd.jmeq_lemmas.

Section GET_CO.

Context {cs: compspecs}.

Definition co_default (s: struct_or_union): composite.
Admitted.

Definition get_co id :=
  match cenv_cs ! id with
  | Some co => co
  | _ => co_default Struct
  end.

End GET_CO.

Lemma co_members_get_co_change_composite {cs_from cs_to} {CCE: change_composite_env cs_from cs_to}: forall id,
  match (coeq cs_from cs_to) ! id with
  | Some b => test_aux cs_from cs_to b id
  | None => false
  end = true ->
  co_members (@get_co cs_from id) = co_members (@get_co cs_to id).
Admitted.

Definition field_type i (m: members) : type :=
 match Ctypes.field_type i m with
 | Errors.OK t => t
 | _ => Tvoid
 end.

Lemma members_spec_change_composite {cs_from cs_to} {CCE: change_composite_env cs_from cs_to}:
  forall id,
  match (coeq cs_from cs_to) ! id with
  | Some b => test_aux cs_from cs_to b id
  | None => false
  end = true ->
  Forall (fun it => cs_preserve_type cs_from cs_to (coeq _ _) (field_type (name_member it) (co_members (@get_co cs_to id))) = true) (co_members (@get_co cs_to id)).
Admitted.

Inductive ListType: list Type -> Type :=
  | Nil: ListType nil
  | Cons: forall {A B} (a: A) (b: ListType B), ListType (A :: B).
Definition decay {X} {F: Type} {l: list X} (v: ListType (map (fun _ => F) l)): list F.
Admitted.

Section COMPOSITE_ENV.
Context {cs: compspecs}.

Lemma type_ind: forall P : type -> Prop,
  (forall t,
  match t with
  | Tarray t0 _ _ => P t0
  | Tstruct id _ => let m := co_members (get_co id) in Forall (fun it => P (field_type (name_member it) m)) m
  | Tunion id _ => let m := co_members (get_co id) in Forall (fun it => P (field_type (name_member it) m)) m
  | _ => True
  end -> P t) ->
  forall t, P t.
Admitted.

Variable A: type -> Type.

Definition FT_aux id :=
    let m := co_members (get_co id) in ListType (map (fun it => A (field_type (name_member it) m)) m).

Variable F_ByValue: forall t: type, A t.
Variable F_Tarray: forall t n a, A t -> A (Tarray t n a).
Variable F_Tstruct: forall id a, FT_aux id -> A (Tstruct id a).
Variable F_Tunion: forall id a, FT_aux id -> A (Tunion id a).
Fixpoint type_func_rec (n: nat) (t: type): A t.
Admitted.

Definition type_func t := type_func_rec (rank_type cenv_cs t) t.

End COMPOSITE_ENV.

Ltac type_induction t :=
  pattern t;
  match goal with
  | |- ?P t =>
    apply type_ind; clear t;
    let t := fresh "t" in
    intros t IH;
    let id := fresh "id" in
    let a := fresh "a" in
    destruct t as [| | | | | | | id a | id a]
  end.

Axiom admit : False.
Fixpoint compact_prod (T: list Type): Type.
exact (match T with
  | nil => unit
  | t :: nil => t
  | t :: T0 => (t * compact_prod T0)%type
  end).
Defined.

Definition compact_prod_sigT_type {A} {P: A -> Type} (l: list (sigT P)): Type.
Proof.
exact (compact_prod nil).
Qed.

Axiom compact_prod_sigT_value: forall {A} {P: A -> Type} (l: list (sigT P)), compact_prod_sigT_type l.

Definition reptype {cs: compspecs} : type -> Type.
Proof.
exact (fun t => match type_func (fun _ => (sigT (fun x => x)))
  (fun t => existT (fun x => x) unit tt)
  (fun t n a TV => existT (fun x => x) unit tt)
  (fun id a TVs => existT (fun x => x) (compact_prod_sigT_type (decay TVs)) (compact_prod_sigT_value (decay TVs)))
  (fun id a TVs => existT (fun x => x) unit tt) t with existT t _ => t end).
Qed.

Section CENV.
Context {cs: compspecs}.

Definition reptype_structlist (m: members) := compact_prod (map (fun it => reptype (field_type (name_member it) m)) m).

Notation REPTYPE t :=
  match t return Type with
  | Tvoid
  | Tfunction _ _ _
  | Tint _ _ _
  | Tlong _ _
  | Tfloat _ _
  | Tunion _ _
  | Tpointer _ _ => unit
  | Tarray t0 _ _ => list (reptype t0)
  | Tstruct id _ => reptype_structlist (co_members (get_co id))
  end.

Axiom reptype_eq: forall t, reptype t = REPTYPE t.
Axiom unfold_reptype : forall {t} (v: reptype t), REPTYPE t.

End CENV.

Lemma reptype_change_composite {cs_from cs_to} {CCE: change_composite_env cs_from cs_to}: forall (t: type),
  cs_preserve_type cs_from cs_to (coeq _ _) t = true ->
  @reptype cs_from t = @reptype cs_to t.
Proof.
  intros t.
  type_induction t; intros.
  +
 elim admit.
  +
 elim admit.
  +
 elim admit.
  +
 elim admit.
  +
 elim admit.
  +
 elim admit.
  +
 elim admit.
  +
 rewrite (@reptype_eq cs_from), (@reptype_eq cs_to).
    simpl in H.
    rewrite co_members_get_co_change_composite by auto.
    apply members_spec_change_composite in H.
    cbv zeta in IH.
    revert H IH.
    unfold reptype_structlist.
    generalize (co_members (get_co id)) at 1 3 4 5 7 9; intros.
    f_equal.
clear - H IH.
    induction IH as [| [i t|] ?].
    -
 elim admit.
    -
 cbn [map].
      inv H.
      f_equal.
    *
 apply H0.
elim admit.
    *
 elim admit.
    -
 elim admit.
  +
 elim admit.
Qed.

Axiom array_pred : forall {A: Type} (v: list A), mpred.

Axiom array_pred_ext: forall {A B} (v0: list A) (v1: list B),
  Zlength v0 = Zlength v1 ->
  array_pred v0 = array_pred v1.

Goal forall (cs_from cs_to : compspecs) (CCE : change_composite_env cs_from cs_to)
  (t : type) (z : Z) (a : attr)
  (v1 : @reptype cs_from (Tarray t z a)) (v2 : @reptype cs_to (Tarray t z a))
,
@eq mpred
  (@array_pred (@reptype cs_from t)
     (@unfold_reptype cs_from (Tarray t z a) v1))
  (@array_pred (@reptype cs_to t)
     (@unfold_reptype cs_to (Tarray t z a) v2))
.
Proof.
intros.
apply array_pred_ext.
apply list_func_JMeq.
-
 apply reptype_change_composite.
  elim admit.
-
 elim admit.
Qed.

Axiom _c : ident.

Definition t_struct_c := Tstruct _c noattr.

Definition get_spec0 {_ : compspecs} := NDmk_funspec (pair nil Tvoid) cc_default (reptype t_struct_c).
