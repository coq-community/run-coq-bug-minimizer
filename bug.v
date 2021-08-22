(* -*- mode: coq; coq-prog-args: ("-emacs" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/msl" "VST.msl" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/sepcomp" "VST.sepcomp" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/veric" "VST.veric" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/floyd" "VST.floyd" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/progs" "VST.progs" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/concurrency" "VST.concurrency" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/atomics" "VST.atomics" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/wand_demo" "wand_demo" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/sha" "sha" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/hmacfcf" "hmacfcf" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/tweetnacl20140427" "tweetnacl20140427" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/hmacdrbg" "hmacdrbg" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/aes" "aes" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/mailbox" "mailbox" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/lib" "compcert.lib" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/common" "compcert.common" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/x86_32" "compcert.x86_32" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/x86" "compcert.x86" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/cfrontend" "compcert.cfrontend" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/exportclight" "compcert.exportclight" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Flocq" "Flocq" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-top" "bug_01" "-native-compiler" "no" "-native-compiler" "no") -*- *)
(* File reduced by coq-bug-finder from original input, then from 981 lines to 48 lines, then from 177 lines to 227 lines, then from 231 lines to 58 lines, then from 187 lines to 753 lines, then from 757 lines to 78 lines, then from 197 lines to 969 lines, then from 973 lines to 86 lines, then from 194 lines to 1059 lines, then from 1063 lines to 113 lines, then from 217 lines to 504 lines, then from 501 lines to 113 lines, then from 216 lines to 350 lines, then from 354 lines to 115 lines, then from 218 lines to 2333 lines, then from 2329 lines to 134 lines, then from 223 lines to 123 lines, then from 224 lines to 1656 lines, then from 1658 lines to 442 lines, then from 541 lines to 1816 lines, then from 1814 lines to 450 lines *)
(* coqc version 8.15+alpha compiled with OCaml 4.12.0
   coqtop version 8.15+alpha *)
Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.
Require VST.veric.base.
Require compcert.cfrontend.Ctypes.
Require VST.msl.ghost.
Require VST.msl.msl_standard.
Module Export shares.
Import VST.msl.msl_standard.

Definition nonempty_share (sh: share) :=
       sepalg.nonidentity sh.
Definition readable_share (sh: share) :=
       nonempty_share (Share.glb Share.Rsh sh).

End shares.
Import VST.msl.msl_standard.
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
