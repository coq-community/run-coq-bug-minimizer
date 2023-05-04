
(* -*- mode: coq; coq-prog-args: ("-emacs" "-w" "-deprecated-native-compiler-option,-native-compiler-disabled" "-native-compiler" "ondemand" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/msl" "VST.msl" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/sepcomp" "VST.sepcomp" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/veric" "VST.veric" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/zlist" "VST.zlist" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/floyd" "VST.floyd" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/progs" "VST.progs" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/concurrency" "VST.concurrency" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/atomics" "VST.atomics" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/wand_demo" "wand_demo" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/sha" "sha" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/hmacfcf" "hmacfcf" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/tweetnacl20140427" "tweetnacl20140427" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/hmacdrbg" "hmacdrbg" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/aes" "aes" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/mailbox" "mailbox" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/lib" "compcert.lib" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/common" "compcert.common" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/x86_32" "compcert.x86_32" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/x86" "compcert.x86" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/cfrontend" "compcert.cfrontend" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/export" "compcert.export" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Flocq" "Flocq" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-top" "VST.floyd.local2ptree_denote") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 837 lines to 57 lines, then from 70 lines to 2829 lines, then from 2813 lines to 57 lines, then from 70 lines to 3286 lines, then from 3287 lines to 67 lines, then from 80 lines to 428 lines, then from 432 lines to 67 lines, then from 80 lines to 585 lines, then from 589 lines to 67 lines, then from 80 lines to 2212 lines, then from 2214 lines to 70 lines, then from 83 lines to 683 lines, then from 688 lines to 71 lines, then from 84 lines to 576 lines, then from 580 lines to 89 lines, then from 102 lines to 1079 lines, then from 1083 lines to 110 lines, then from 123 lines to 1913 lines, then from 1916 lines to 271 lines, then from 284 lines to 1649 lines, then from 1651 lines to 275 lines, then from 288 lines to 410 lines, then from 415 lines to 276 lines, then from 289 lines to 2343 lines, then from 2347 lines to 310 lines, then from 323 lines to 541 lines, then from 546 lines to 310 lines, then from 323 lines to 666 lines, then from 663 lines to 309 lines *)
(* coqc version 8.18+alpha compiled with OCaml 4.14.1
   coqtop version runner-jztamce-project-6138686-concurrent-0:/builds/coq/coq/_build/default,(HEAD detached at b2f5d6faa5) (b2f5d6faa5658dc7d74585d2c613dac927d52deb)
   Expected coqc runtime on this file: 0.935 sec *)
Require VST.msl.ghost.
Require VST.msl.msl_standard.
Require VST.sepcomp.Address.
Export VST.sepcomp.Address.
Export compcert.lib.Coqlib.
Export compcert.common.AST.
Export compcert.common.Values.
Export compcert.common.Memdata.

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

Import VST.msl.msl_standard.

Definition nonempty_share (sh: share) :=
       sepalg.nonidentity sh.
Definition readable_share (sh: share) :=
       nonempty_share (Share.glb Share.Rsh sh).
Import VST.msl.ghost.

Module Type ADR_VAL.

Parameter kind: Type.
End ADR_VAL.
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

  Parameter rmap : Type.
  Axiom ag_rmap: ageable rmap.
#[global] Existing Instance ag_rmap.
  Axiom Ext_rmap: Ext_ord rmap.
#[global] Existing Instance Ext_rmap.

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
#[global] Instance ag_rmap : ageable rmap.
Admitted.
#[global] Instance Ext_rmap : Ext_ord rmap.
Admitted.

End Rmaps.

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

Definition genviron := Map.t block.

Definition venviron := Map.t (block * type).

Definition tenviron := Map.t val.

Inductive environ : Type :=
 mkEnviron: forall (ge: genviron) (ve: venviron) (te: tenviron), environ.

Definition mpred := pred rmap.

Definition globals := ident -> val.

Inductive localdef : Type :=
 | temp: ident -> val -> localdef
 | lvar: ident -> type -> val -> localdef
 | gvars: globals -> localdef.

Arguments temp i%positive v.
Definition PROPx {A} (P: list Prop): forall (Q: A->mpred), A->mpred.
Admitted.
Definition LOCALx (Q: list localdef) : forall (R: environ->mpred), environ->mpred.
Admitted.
Import compcert.lib.Maps.

Definition local_trees :=
   (PTree.t val * PTree.t (type * val) * list Prop * option globals)%type.
Definition local2ptree1 (Q: localdef)
   (T1: PTree.t val) (T2: PTree.t (type * val)) (P': list Prop) (Q': option globals)
   (f:  PTree.t val -> PTree.t (type * val) -> list Prop -> option globals -> local_trees)
   : local_trees.
exact (match Q with
| temp i v =>   match T1 ! i with
                | None => f (PTree.set i v T1) T2 P' Q'
                | Some v' => f T1 T2 ((v=v')::P')  Q'
                end
| lvar i t v => match T2 ! i with
                | None => f T1 (PTree.set i (t, v) T2) P' Q'
                | Some (t', vl) => f T1 T2 ((vl=v)::(t'=t)::P') Q'
                end
| gvars gv =>   match Q' with
                | None => f T1 T2 P' (Some gv)
                | Some gv' => f T1 T2 ((gv' = gv)::P') Q'
                end
end).
Defined.
Fixpoint local2ptree_aux (Q: list localdef)
   (T1: PTree.t val) (T2: PTree.t (type * val)) (P': list Prop) (Q': option globals):
   local_trees.
exact (match Q with
| Q1 :: Qr => local2ptree1 Q1 T1 T2 P' Q' (local2ptree_aux Qr)
| nil => (T1,T2,P',Q')
end).
Defined.

Definition LocalD (T1: PTree.t val) (T2: PTree.t (type * val)) (Q: option globals) :=
  PTree.fold (fun Q i v => temp i v :: Q) T1
  (PTree.fold (fun Q i tv => match tv with (t, v) => lvar i t v end :: Q) T2
   match Q with Some gv => (gvars gv) :: nil | None => nil end).

Lemma local2ptree_soundness' : forall P Q R T1a T2a Pa Qa T1 T2 P' Q',
  local2ptree_aux Q T1a T2a Pa Qa = (T1, T2, P', Q') ->
  PROPx (Pa++P) (LOCALx (Q ++ LocalD T1a T2a Qa) R)
   = PROPx (P' ++ P) (LOCALx (LocalD T1 T2 Q') R).
Proof.
  intros until R.
  induction Q; intros.
  simpl in H.
inv H.
reflexivity.
  simpl in H.
  destruct a; simpl in H.
+
    destruct (T1a ! i) eqn:H8; inv H;
    rewrite <- (IHQ _ _ _ _ _ _ _ _ H1); clear H1 IHQ.
