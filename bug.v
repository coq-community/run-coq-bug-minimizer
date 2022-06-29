(* -*- mode: coq; coq-prog-args: ("-emacs" "-w" "-deprecated-native-compiler-option,-native-compiler-disabled" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/msl" "VST.msl" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/sepcomp" "VST.sepcomp" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/veric" "VST.veric" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/zlist" "VST.zlist" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/floyd" "VST.floyd" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/progs" "VST.progs" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/concurrency" "VST.concurrency" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/atomics" "VST.atomics" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/wand_demo" "wand_demo" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/sha" "sha" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/hmacfcf" "hmacfcf" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/tweetnacl20140427" "tweetnacl20140427" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/hmacdrbg" "hmacdrbg" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/aes" "aes" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/mailbox" "mailbox" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/lib" "compcert.lib" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/common" "compcert.common" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/x86_32" "compcert.x86_32" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/x86" "compcert.x86" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/cfrontend" "compcert.cfrontend" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/export" "compcert.export" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Flocq" "Flocq" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-top" "bug_01" "-native-compiler" "ondemand") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 568 lines to 303 lines, then from 317 lines to 1175 lines, then from 1180 lines to 1121 lines, then from 1134 lines to 2955 lines, then from 2955 lines to 2824 lines, then from 2821 lines to 2808 lines, then from 2821 lines to 3058 lines, then from 3062 lines to 2966 lines, then from 2975 lines to 2962 lines, then from 2975 lines to 3465 lines, then from 3469 lines to 3196 lines, then from 3197 lines to 3184 lines, then from 3197 lines to 3537 lines, then from 3542 lines to 3383 lines, then from 3390 lines to 3377 lines, then from 3390 lines to 4354 lines, then from 4358 lines to 4081 lines *)
(* coqc version 8.17+alpha compiled with OCaml 4.14.0
   coqtop version 
   Expected coqc runtime on this file: 10.884 sec *)
Require VST.msl.iter_sepcon.
Require VST.veric.rmaps_lemmas.
Require VST.veric.Memory.
Module Export AdmitTactic.
Module Import LocalFalse.
End LocalFalse.
End AdmitTactic.

Module Export VST_DOT_veric_DOT_compcert_rmaps_WRAPPED.
Module Export compcert_rmaps.
Export VST.msl.msl_standard.
Import VST.veric.base.
Import compcert.cfrontend.Ctypes.
Import VST.veric.shares.
Import VST.veric.rmaps.
Import VST.veric.rmaps_lemmas.
Export VST.veric.Memory.
 

Global Instance EqDec_type: EqDec type := type_eq.
 

Definition typesig := (list type * type)%type.

Inductive kind : Type := VAL : memval -> kind
                                   | LK : forall n i : Z, kind
                                   | FUN: typesig -> calling_convention -> kind.

Definition isVAL (k: kind) := match k with | VAL _ => True | _ => False end.
Definition isFUN (k: kind) := match k with | FUN _ _ => True | _ => False end.

Lemma isVAL_i: forall v, isVAL (VAL v).
intros; simpl; auto.
Qed.
Global Hint Resolve isVAL_i : core.

Lemma isVAL_dec: forall k, {isVAL k}+{~isVAL k}.
intros; destruct k; auto.
Qed.

Module CompCert_AV <: ADR_VAL.

Definition address := address.
Definition some_address : address := (xH,0).
Definition kind := kind.

End CompCert_AV.

Lemma getVAL: forall k, {v : memval & k = VAL v}  + {~isVAL k}.
intros.
destruct k;
  try solve [simpl; right; tauto].
left.
eauto.
Qed.

Lemma VAL_inj: forall v v', VAL v = VAL v' -> v = v'.
intros.
inv H; auto.
Qed.

Global Instance EqDec_calling_convention: EqDec calling_convention.
  hnf.
decide equality.
  destruct cc_structret, cc_structret0; subst; try tauto; right; congruence.
  destruct cc_unproto, cc_unproto0;  subst; try tauto; right; congruence.
  destruct cc_vararg, cc_vararg0; subst; try tauto.
  destruct (zeq z0 z); subst; [left|right]; congruence.
  right; congruence.
  right; congruence.
Qed.

Global Instance EqDec_kind: EqDec kind.
  hnf.
decide equality; try apply eq_dec; try apply zeq; try apply signature_eq.
Qed.

Module R := Rmaps (CompCert_AV).
Module RML := Rmaps_Lemmas(R).

Export RML.
Export R.

Definition mk_rshare: forall p: Share.t, pure_readable_share p -> rshare := exist pure_readable_share.
Definition rshare_sh (p: rshare) : Share.t := proj1_sig p.

Lemma mk_rshare_sh: forall (p:rshare) (H: pure_readable_share (rshare_sh p)),
  mk_rshare (rshare_sh p) H = p.
  intros.
  unfold mk_rshare.
  destruct p; simpl.
  auto with extensionality.
Qed.

Definition fixup_splitting
  (a:address -> Share.t) (z: address -> option (rshare * kind)) : address -> option (rshare * kind) :=
  fun l =>
    match z l with
    | Some (sh, k) =>
       match dec_readable (a l) with
       | left p => Some (readable_part p,  k)
       | right _ => None
       end
    | None => None
    end.

Definition share_of (x: option (rshare * kind)) : Share.t :=
  match x with Some (p,_) => proj1_sig p | None => Share.bot end.

Definition Join_pk := (Join_lower (Join_prod rshare _ kind (Join_equiv _))).

Lemma share_of_Some: forall p: rshare * AV.kind, readable_share (share_of (Some p)).
 intros.
destruct p as [[? ?] ?]; simpl.
 auto.
 destruct p; auto.
Qed.

Lemma join_sub_same_k:
 forall {a a' : rshare} {k k': AV.kind},
      @join_sub _ Join_pk (Some (a,k)) (Some (a',k')) -> k=k'.
  intros.
destruct H.
inv H; auto.
inv H3.
simpl in H0.
inv H0; congruence.
Qed.

Lemma pure_readable_glb_Rsh:
 forall sh, pure_readable_share sh -> Share.glb Share.Rsh sh = sh.
 intros.
 destruct H.
 rewrite (comp_parts comp_Lsh_Rsh sh) at 2.
rewrite H.
 rewrite Share.lub_commute, Share.lub_bot; auto.
Qed.

Lemma join_glb_Rsh:
  forall a b c : Share.t,
  join a b c ->
  join (Share.glb Share.Rsh a) (Share.glb Share.Rsh b) (Share.glb Share.Rsh c).
intros.
apply (join_comp_parts comp_Lsh_Rsh).
auto.
Qed.

Lemma pure_readable_share_glb:
  forall a, pure_readable_share a -> Share.glb Share.Rsh a = a.
 intros.
destruct H.
 rewrite (comp_parts comp_Lsh_Rsh a) at 2.
rewrite H.
 rewrite Share.lub_commute, Share.lub_bot.
auto.
Qed.

Lemma glb_Rsh_bot_unreadable:
  forall a, Share.glb Share.Rsh a = Share.bot -> ~readable_share a.
 intros.
unfold readable_share.
rewrite H.
intro.
apply H0.
 apply bot_identity.
Qed.

Lemma fixup_join : forall a (ac ad: address -> Share.t)  z,
  (forall x, @join_sub _ Join_pk (a x) (z x)) ->
  (forall x, join (ac x) (ad x) (share_of (a x))) ->
  (forall x,
    @join _ Join_pk
    (fixup_splitting ac z x)
    (fixup_splitting ad z x)
    (a x)).
 do 2  pose proof I.
  intros.
  unfold fixup_splitting.

Ltac glb_Rsh_tac :=
 repeat
 match goal with
 | |- Some _ = None => elimtype False
 | |- None = Some _ => elimtype False
 | |- join (Some _) _ None => elimtype False
 | |- join _ (Some _) None => elimtype False
 | |- join _ None _ => apply join_unit2; [ apply None_unit |]
 | |- join None _ _ => apply join_unit1; [ apply None_unit |]
 | |- Some (_,_) = Some(_,_) => do 2 f_equal; try apply exist_ext; auto
 | H: ~readable_share ?X, H1: join (Share.glb Share.Rsh ?X) _ _ |- _ =>
         rewrite (not_readable_Rsh_part H) in H1;
         apply join_unit1_e in H1; [ | apply bot_identity];
         rewrite ?H1 in *
 | H: ~readable_share ?X, H1: join _ (Share.glb Share.Rsh ?X) _ |- _ =>
         rewrite (not_readable_Rsh_part H) in H1;
         apply join_unit2_e in H1; [ | apply bot_identity];
         rewrite ?H1 in *
 | H: identity ?A, H1: readable_share ?A |- _ =>
    apply (readable_not_identity A _ H1 H)
 | H: pure_readable_share ?A |- Share.glb Share.Rsh ?A = ?A =>
     apply pure_readable_glb_Rsh; auto
 | H: join ?A ?B Share.bot |- _ =>
     let H1 := fresh in
         assert (H1 := identity_share_bot _ (split_identity _ _ H bot_identity));
         rewrite ?H1 in *;
     let H2 := fresh in
         assert (H2 := identity_share_bot _ (split_identity _ _ (join_comm H) bot_identity));
         rewrite ?H2 in *;
     clear H
 | H: readable_share Share.bot |- _ => contradiction bot_unreadable
 | H: join_sub None _ |- _ => clear H
 | H: join_sub (Some(_,?A)) (Some (_,?B)) |- _ =>
      unify A B ||
      (is_var A; pose proof (join_sub_same_k H); subst A)
 | |- _ => rewrite Share.glb_bot in *
 | H: Share.glb Share.Rsh _ = Share.bot |- _ =>
          apply glb_Rsh_bot_unreadable in H; try contradiction
 | H: pure_readable_share ?A |- _ => rewrite (pure_readable_share_glb _ H) in *
 | |- _ => assumption
 end;
 auto.

  case_eq (z x); intros; [destruct p | ].
*
  specialize (H1 x); specialize (H2 x).
  clear H H0.
rewrite H3 in *.
clear z H3.
  destruct (dec_readable (ac x)).
 +
  destruct (dec_readable (ad x)).
 -
  destruct (a x) as [[[? ?] ?] | ]; simpl in *.
  constructor.
  pose proof (join_sub_same_k H1); subst k.
  constructor; auto.
simpl.
  red.
red.
simpl.
  apply join_glb_Rsh in H2.
  glb_Rsh_tac.
  glb_Rsh_tac.
  -
  apply join_glb_Rsh in H2.
  glb_Rsh_tac.
  destruct (a x) as [[[? ?] ?]|]; simpl in *.
  glb_Rsh_tac.
  glb_Rsh_tac.
+
  glb_Rsh_tac.
  apply join_glb_Rsh in H2.
  destruct (a x) as [[[? ?] ?]|]; simpl in *.
  glb_Rsh_tac.
  destruct (dec_readable (ad x)).
  glb_Rsh_tac.
  glb_Rsh_tac.
  apply n0.
  unfold readable_share.
rewrite H2.
destruct p.
intro.
  glb_Rsh_tac.
  glb_Rsh_tac.
  destruct (dec_readable (ad x)).
  glb_Rsh_tac.
  glb_Rsh_tac.
*
 specialize (H1 x).
rewrite H3 in H1.
 destruct H1.
 inv H1.
constructor.
rewrite H7; constructor.
Qed.

Lemma join_share_of: forall a b c,
     @join _ Join_pk a b c -> join (share_of a) (share_of b) (share_of c).
  intros.
inv H; simpl.
apply join_unit1; auto.
apply join_unit2; auto.
  destruct a1; destruct a2; destruct a3.
  destruct r,r0,r1; simpl.
  destruct H0.
simpl in *.
do 3 red in H.
simpl in H.
auto.
Qed.

#[export] Instance Cross_rmap_aux: Cross_alg (AV.address -> option (rshare * AV.kind)).
 hnf.
intros a b c d z ? ?.
 destruct (cross_split_fun Share.t _ address share_cross_split
                   (share_of oo a) (share_of oo b) (share_of oo c) (share_of oo d) (share_of oo z))
  as [[[[ac ad] bc] bd] [? [? [? ?]]]].
 intro x.
specialize (H x).
unfold compose.
 clear - H.
inv H; simpl in *.
apply join_unit1; auto.
apply join_unit2; auto.
 destruct a1; destruct a2; destruct a3; apply H3.
 intro x.
specialize (H0 x).
unfold compose.
 clear - H0.
inv H0; simpl in *.
apply join_unit1; auto.
apply join_unit2; auto.
 destruct a1; destruct a2; destruct a3; apply H3.
 exists (fixup_splitting ac z,
            fixup_splitting ad z,
            fixup_splitting bc z,
            fixup_splitting bd z).
 split3; [ | | split];  do 2 red; simpl; intro;
 apply fixup_join; auto; intros.
 exists (b x0); apply H.
 exists (a x0); apply join_comm; apply H.
 exists (d x0); apply H0.
 exists (c x0); apply join_comm; apply H0.
Qed.

#[export] Instance Trip_resource: Trip_alg resource.
intro; intros.
destruct a as [ra | ra sa ka pa | ka pa].
destruct b as [rb | rb sb kb pb | kb pb]; try solve [elimtype False; inv H].
destruct ab as [rab | rab sab kab pab | kab pab]; try solve [elimtype False; inv H].
destruct c as [rc | rc sc kc pc | kc pc]; try solve [elimtype False; inv H0].
destruct bc as [rbc | rbc sbc kbc pbc | kbc pbc]; try solve [elimtype False; inv H0].
destruct ac as [rac | rac sac kac pac | kac pac]; try solve [elimtype False; inv H1].
destruct (triple_join_exists_share ra rb rc rab rbc rac) as [rabc ?];
  [inv H | inv H0 | inv H1 | ] ; auto.
assert (n5 := join_unreadable_shares j n1 n2).
exists (NO rabc n5); constructor; auto.
destruct bc as [rbc | rbc sbc kbc pbc | kbc pbc]; try solve [elimtype False; inv H0].
destruct ac as [rac | rac sac kac pac | kac pac]; try solve [elimtype False; inv H1].
destruct (triple_join_exists_share ra rb rc rab rbc rac) as [rabc ?];
  [inv H | inv H0 | inv H1 | ] ; auto.
assert (sabc := join_readable2 j sc).
exists (YES rabc sabc kc pc); constructor; auto.
destruct ab as [rab | rab sab kab pab | kab pab]; try solve [elimtype False; inv H].
destruct c as [rc | rc sc kc pc | kc pc]; try solve [elimtype False; inv H0].
destruct bc as [rbc | rbc sbc kbc pbc | kbc pbc]; try solve [elimtype False; inv H0].
destruct ac as [rac | rac sac kac pac | kac pac]; try solve [elimtype False; inv H1].
destruct (triple_join_exists_share ra rb rc rab rbc rac) as [rabc ?];
  [inv H | inv H0 | inv H1 | ] ; auto.
assert (sabc := join_readable1 j sab).
exists (YES rabc sabc kab pab); constructor; auto.
destruct bc as [rbc | rbc sbc kbc pbc | kbc pbc]; try solve [elimtype False; inv H0].
destruct ac as [rac | rac sac kac pac | kac pac]; try solve [elimtype False; inv H1].
destruct (triple_join_exists_share ra rb rc rab rbc rac) as [rabc ?];
  [inv H | inv H0 | inv H1 | ] ; auto.
assert (sabc := join_readable1 j sab).
exists (YES rabc sabc kbc pbc).
inv H0; inv H; inv H1; constructor; auto.
destruct b as [rb | rb sb kb pb | kb pb]; try solve [elimtype False; inv H].
destruct ab as [rab | rab sab kab pab | kab pab]; try solve [elimtype False; inv H].
destruct c as [rc | rc sc kc pc | kc pc]; try solve [elimtype False; inv H0].
destruct bc as [rbc | rbc sbc kbc pbc | kbc pbc]; try solve [elimtype False; inv H0].
destruct ac as [rac | rac sac kac pac | kac pac]; try solve [elimtype False; inv H1].
destruct (triple_join_exists_share ra rb rc rab rbc rac) as [rabc ?];
  [inv H | inv H0 | inv H1 | ] ; auto.
assert (sabc := join_readable1 j sab).
exists (YES rabc sabc kab pab); constructor; auto.
destruct bc as [rbc | rbc sbc kbc pbc | kbc pbc]; try solve [elimtype False; inv H0].
destruct ac as [rac | rac sac kac pac | kac pac]; try solve [elimtype False; inv H1].
destruct (triple_join_exists_share ra rb rc rab rbc rac) as [rabc ?];
  [inv H | inv H0 | inv H1 | ] ; auto.
assert (sabc := join_readable1 j sab).
exists (YES rabc sabc kac pac).
 inv H; inv H0; inv H1; constructor; auto.
destruct ab as [rab | rab sab kab pab | kab pab]; try solve [elimtype False; inv H].
destruct c as [rc | rc sc kc pc | kc pc]; try solve [elimtype False; inv H0].
destruct bc as [rbc | rbc sbc kbc pbc | kbc pbc]; try solve [elimtype False; inv H0].
destruct ac as [rac | rac sac kac pac | kac pac]; try solve [elimtype False; inv H1].
destruct (triple_join_exists_share ra rb rc rab rbc rac) as [rabc ?];
  [inv H | inv H0 | inv H1 | ] ; auto.
assert (sabc := join_readable1 j sab).
exists (YES rabc sabc kab pab); constructor; auto.
destruct bc as [rbc | rbc sbc kbc pbc | kbc pbc]; try solve [elimtype False; inv H0].
destruct ac as [rac | rac sac kac pac | kac pac]; try solve [elimtype False; inv H1].
destruct (triple_join_exists_share ra rb rc rab rbc rac) as [rabc ?];
  [inv H | inv H0 | inv H1 | ] ; auto.
assert (sabc := join_readable1 j sab).
exists (YES rabc sabc kc pc).
 inv H.
inv H1.
inv H0.
constructor; auto.
 exists ab.
inv H.
inv H1.
inv H0.
constructor.
Qed.

Lemma pure_readable_share_i:
  forall sh, readable_share sh -> (pure_readable_share (Share.glb Share.Rsh sh)).
intros.
split.
rewrite <- Share.glb_assoc.
rewrite glb_Lsh_Rsh.
rewrite Share.glb_commute.
apply Share.glb_bot.
do 3 red in H|-*.
contradict H.
rewrite glb_twice in H.
auto.
Qed.

 

Obligation Tactic := Tactics.program_simpl.

Lemma pure_readable_Rsh: pure_readable_share Share.Rsh.
split.
apply glb_Lsh_Rsh.
intro.
rewrite Share.glb_idem in H.
pose proof (Share.split_nontrivial Share.Lsh Share.Rsh Share.top).
spec H0.
unfold Share.Lsh, Share.Rsh.
destruct (Share.split Share.top); auto.
apply identity_share_bot in H.
spec H0; auto.
contradiction Share.nontrivial.
Qed.

Definition rfullshare : rshare := mk_rshare _ pure_readable_Rsh.

Program Definition writable (l: address): pred rmap :=
 fun phi =>
  match phi @ l with
    | YES sh _ k lp => writable0_share sh /\ isVAL k
    | _ => False
  end.
 Next Obligation.
  split; intro; intros.
  generalize (age1_res_option a a' l H); intro.
  destruct (a @ l); try contradiction.
  simpl in H1.
  destruct (a' @ l); inv H1; auto.
  destruct H0; split; auto.
  unfold writable0_share in *.
  clear - H3 H0.
  apply leq_join_sub in H0.
  apply leq_join_sub.
  apply Share.ord_spec2 in H0.
rewrite <- H0 in H3.
  rewrite Share.glb_absorb in H3.
  clear H0.
  rewrite H3.
  apply Share.glb_lower2.

  rewrite rmap_order in H; destruct H as (? & <- & ?); auto.
Qed.

Program Definition readable (loc: address) : pred rmap :=
   fun phi => match phi @ loc with YES _ _ k _ => isVAL k | _ => False end.
 Next Obligation.
  split; intro; intros.
  generalize (age1_res_option a a' loc H); intro.
  destruct (a @ loc); try contradiction.
  simpl in H1.
  destruct (a' @ loc); inv H1; auto.

  rewrite rmap_order in H; destruct H as (? & <- & ?); auto.
 Qed.

Lemma readable_join:
  forall phi1 phi2 phi3 loc, join phi1 phi2 phi3 ->
            readable loc phi1 -> readable loc phi3.
unfold readable; intros until loc.
intros.
simpl in *.
generalize (resource_at_join _ _ _ loc H); clear H; intros.
revert H0 H; destruct (phi1 @ loc); intros; try contradiction.
inv H; auto.
Qed.

Lemma readable_writable_join:
forall phi1 phi2 l, readable l phi1 -> writable l phi2 -> joins phi1 phi2 -> False.
intros.
unfold readable, writable in *.
simpl in H, H0.
destruct H1 as [phi ?].
generalize (resource_at_join _ _ _ l H1); clear H1; revert H H0.
destruct (phi1 @ l); intros; try contradiction.
destruct (phi2 @ l); try contradiction.
inv H1.
destruct H0.
clear - RJ H0 r.
unfold readable_share, writable0_share in *.
destruct H0.
destruct (join_assoc (join_comm H) (join_comm RJ)) as [a [? ?]].
clear - r H0.
apply r; clear r.
destruct H0.
rewrite H.
auto.
Qed.

Lemma writable0_join_sub:
  forall sh sh', join_sub sh sh' -> writable0_share sh -> writable0_share sh'.
intros.
destruct H.
destruct H0 as [b ?].
destruct (join_assoc H0 H) as [c [? ?]].
exists c; auto.
Qed.

Lemma writable_join: forall loc phi1 phi2, join_sub phi1 phi2 ->
            writable loc phi1 -> writable loc phi2.
unfold writable; intros.
simpl in *.
destruct H; generalize (resource_at_join _ _ _ loc H); clear H.
revert H0; destruct (phi1 @ loc); intros; try contradiction.
destruct H0; subst.
inv H; split; auto; eapply writable0_join_sub; eauto; eexists; eauto.
Qed.

Lemma writable_readable: forall loc m, writable loc m -> readable loc m.
 unfold writable, readable.
 intros ? ?.
simpl.
 destruct (m @ loc); auto.
intros [? ?].
auto.
Qed.

Lemma writable_e: forall loc m,
   writable loc m ->
   exists sh, exists rsh, exists v, exists p,
     m @ loc = YES sh rsh (VAL v) p /\ writable0_share sh.
Proof.
unfold writable; simpl; intros; destruct (m@loc); try contradiction.
destruct H.
destruct k; try solve [inversion H0].
exists sh, r, m0, p; split; auto.
Qed.
Arguments writable_e [loc] [m] _.

Lemma readable_e: forall loc m,
   readable loc m ->
  exists sh, exists rsh, exists v, exists p, m @ loc = YES sh rsh (VAL v) p.
Proof.
unfold readable; simpl; intros; destruct (m@loc); try contradiction.
destruct k; try solve [inversion H].
subst.
econstructor; eauto.
Qed.
Arguments readable_e [loc] [m] _.

Definition bytes_writable (loc: address) (size: Z) (phi: rmap) : Prop :=
  forall i, (0 <= i < size) -> writable (adr_add loc i) phi.

Definition bytes_readable (loc: address) (size: Z) (phi: rmap) : Prop :=
  forall i, (0 <= i < size) -> readable (adr_add loc i) phi.

Lemma readable_dec (loc: address) (phi: rmap) : {readable loc phi} + {~readable loc phi}.
intros.
unfold readable.
simpl.
case (phi @ loc); intros; auto.
apply isVAL_dec.
Qed.

Lemma writable_dec: forall loc phi, {writable loc phi}+{~writable loc phi}.
intros.
unfold writable.
simpl.
destruct (phi @ loc); auto.
destruct (isVAL_dec k).
destruct (writable0_share_dec sh).
left; auto.
right; auto.
contradict n; auto.
destruct n; auto.
right; contradict n; destruct n; auto.
Qed.

Lemma bytes_writable_dec:
   forall loc n m, {bytes_writable loc n m}+{~bytes_writable loc n m}.
intros.
destruct n.
left; intro; intros; lia.
2: generalize (Zlt_neg_0 p); intro; left; intro; intros; lia.
rewrite Zpos_eq_Z_of_nat_o_nat_of_P.
remember (nat_of_P p) as n.
clear.
destruct loc as [b z].
revert z;
induction n; intros.
left; intro; intros.
simpl in H; lia.
rewrite inj_S.
destruct (IHn (z+1)).
destruct (writable_dec (b,z) m).
left.
intro; intros.
unfold adr_add; simpl.
destruct (zeq i 0).
subst.
replace (z+0) with z by lia.
auto.
replace (z+i) with (z+1+(i-1)) by lia.
apply b0.
lia.
right.
contradict n0.
specialize ( n0 0).
unfold adr_add in n0; simpl in n0.
replace (z+0) with z in n0.
apply n0.
lia.
lia.
right.
contradict n0.
intro; intros.
unfold adr_add; simpl.
replace (z+1+i) with (z+(1+i)) by lia.
apply n0.
lia.
Qed.

Lemma bytes_readable_dec:
   forall loc n m, {bytes_readable loc n m}+{~bytes_readable loc n m}.
intros.
destruct n.
left; intro; intros; lia.
2: generalize (Zlt_neg_0 p); intro; left; intro; intros; lia.
rewrite Zpos_eq_Z_of_nat_o_nat_of_P.
remember (nat_of_P p) as n.
clear.
destruct loc as [b z].
revert z;
induction n; intros.
left; intro; intros.
simpl in H; lia.
rewrite inj_S.
destruct (IHn (z+1)).
destruct (readable_dec (b,z) m).
left.
intro; intros.
unfold adr_add; simpl.
destruct (zeq i 0).
subst.
replace (z+0) with z by lia.
auto.
replace (z+i) with (z+1+(i-1)) by lia.
apply b0.
lia.
right.
contradict n0.
specialize ( n0 0).
unfold adr_add in n0; simpl in n0.
replace (z+0) with z in n0.
apply n0.
lia.
lia.
right.
contradict n0.
intro; intros.
unfold adr_add; simpl.
replace (z+1+i) with (z+(1+i)) by lia.
apply n0.
lia.
Qed.

Lemma bytes_writable_readable:
  forall m loc n, bytes_writable m loc n -> bytes_readable m loc n.
unfold bytes_writable, bytes_readable; intros.
apply writable_readable; auto.
Qed.

Global Hint Resolve bytes_writable_readable : mem.

Lemma rmap_age_i:
 forall w w' : rmap,
    level w = S (level w') ->
   (forall l, resource_fmap (approx (level w')) (approx (level w')) (w @ l) = w' @ l) ->
    ghost_fmap (approx (level w')) (approx (level w')) (ghost_of w) = ghost_of w' ->
    age w w'.
Proof.
intros.
hnf.
destruct (levelS_age1 _ _ H).
assert (x=w'); [ | subst; auto].
assert (level x = level w')
  by (apply age_level in H2; lia).
apply rmap_ext; auto.
intros.
specialize (H0 l).
rewrite (age1_resource_at w x H2 l (w@l)).
rewrite H3.
apply H0.
symmetry; apply resource_at_approx.
erewrite age1_ghost_of; eauto.
rewrite H3; apply H1.
Qed.

End compcert_rmaps.
Module Export VST.
Module Export veric.
Module Export compcert_rmaps.
Include VST_DOT_veric_DOT_compcert_rmaps_WRAPPED.compcert_rmaps.
End compcert_rmaps.
Module Export val_lemmas.
Import compcert.lib.Coqlib.
Import compcert.lib.Integers.
Import compcert.common.Values.
Import VST.msl.Coqlib2.

Definition force_val (v: option val) : val :=
 match v with Some v' => v' | None => Vundef end.

Definition isptr v :=
   match v with | Vptr _ _ => True | _ => False end.

Lemma int_eq_e: forall i j, Int.eq i j = true -> i=j.
intros.
pose proof (Int.eq_spec i j); rewrite H in H0; auto.
Qed.

Lemma two_p_neg:
 forall n, n<0 -> two_p n = 0.
destruct n; intros; simpl; auto; lia.
Qed.

Unset Implicit Arguments.

Lemma testbit_signed_neg:
 forall i j n,
   - two_p n <= Int.signed i < 0 ->
    0 <= n <= j ->
    j < Int.zwordsize ->
   Int.testbit i j = true.
intros.
rename H1 into Wj.
pose proof (Int.unsigned_range i).
unfold Int.signed in H.
if_tac in H.
lia.
unfold Int.testbit.
forget (Int.unsigned i) as i'; clear i; rename i' into i.
rewrite <- (Z2Nat.id j) in * by lia.
unfold Int.half_modulus in *.
unfold Int.modulus in *.
unfold Int.zwordsize in Wj.
forget Int.wordsize as W.
assert (Z.to_nat j < W)%nat by (apply Nat2Z.inj_lt; auto).
clear Wj.
assert (W = Z.to_nat j + 1 + (W-Z.to_nat j-1))%nat by lia.
forget (W - Z.to_nat j - 1)%nat as K.
subst W.

clear H3.
rewrite <- (Z2Nat.id n) in H by lia.
rewrite <- (Z2Nat.id n) in H0 by lia.
rewrite <- two_power_nat_two_p in H.
assert (Z.to_nat n <= Z.to_nat j)%nat.
  apply Nat2Z.inj_le; lia.
clear H0.
forget (Z.to_nat n) as n'; clear n; rename n' into n.
forget (Z.to_nat j) as j'; clear j; rename j' into j.
destruct H as [H _].
revert n i H3 H2 H  H1; induction j; intros.
*
simpl (Z.of_nat) in *.
assert (n=0)%nat by lia.
subst n.
simpl plus in *.
clear H3.
change (- two_power_nat 0) with (-1) in H.
assert (i = (two_power_nat (S K) - 1)) by lia.
subst i.
rewrite two_power_nat_S.
clear.
forget (two_power_nat K) as A.
replace A with ((A-1)+1) by lia.
rewrite Z.mul_add_distr_l.
replace (2 * (A - 1) + 2 * 1 - 1) with (2 * (A - 1) + 1) by lia.
apply Z.testbit_odd_0.
*
destruct n.
change (- two_power_nat 0)%Z with (-1) in H.
assert (i = two_power_nat (S j + 1 + K) - 1) by lia.
clear H H1 H2.
subst i.
replace (two_power_nat (S j + 1 + K) - 1) with (Z.ones (Z.of_nat (S j + 1 + K))).
apply Z.ones_spec_low.
split; [lia | ].
apply Nat2Z.inj_lt.
lia.
rewrite Z.ones_equiv.
rewrite two_power_nat_equiv.
lia.
rewrite inj_S.
rewrite Zbits.Ztestbit_succ by lia.
apply (IHj n); clear IHj.
+
lia.
+
rewrite Zdiv2_div.
apply Z_div_ge; try lia.
replace (S j + 1 + K)%nat with (S (j + 1 + K))%nat in H2 by lia.
rewrite two_power_nat_S in H2.
rewrite Z.mul_comm in H2.
rewrite Z_div_mult_full in H2 by lia.
auto.
+
rewrite two_power_nat_S in H.
replace (S j + 1 + K)%nat with (S (j + 1 + K))%nat in H by lia.
rewrite two_power_nat_S in H.
rewrite (Zdiv2_odd_eqn i) in H.
destruct (Z.odd i) eqn:?H; lia.
+
replace (S j + 1 + K)%nat with (S (j + 1 + K))%nat in H1 by lia.
rewrite two_power_nat_S in H1.
rewrite (Zdiv2_odd_eqn i) in H1.
destruct (Z.odd i) eqn:?H; lia.
Qed.

Lemma sign_ext_inrange:
  forall n i, - two_p (n-1) <= Int.signed i <= two_p (n-1) - 1 ->
       Int.sign_ext n i = i.
intros.
destruct (zlt n Int.zwordsize);
  [ | apply Int.sign_ext_above; auto].
destruct (zlt n 0).
assert (n-1 < 0) by lia.
repeat rewrite two_p_neg in H by lia.
lia.
destruct (zeq n 0).
subst n.
simpl in H.
assert (Int.signed i = 0) by lia.
clear - H0.
rewrite <- (Int.repr_signed i).
rewrite H0.
reflexivity.
assert (0 < n < Int.zwordsize) by lia.
clear - H H0.

apply Int.same_bits_eq; intros j ?.
rewrite (Int.bits_sign_ext n i j) by lia.
if_tac; auto.
destruct H1.
destruct (zlt (Int.signed i) 0).
*

assert (- two_p (n - 1) <= Int.signed i  < 0) by lia.
clear H.
rewrite (testbit_signed_neg i (n-1) (n-1)); auto; try lia.
rewrite (testbit_signed_neg i j (n-1)%Z); auto; lia.
*

rewrite Int.signed_eq_unsigned in H by (apply Int.signed_positive; auto).
assert (Int.size i <= n-1);
  [ | rewrite !Int.bits_size_2 by lia; auto].
apply Z.ge_le.
apply Int.size_interval_2.
lia.
pose proof (Int.unsigned_range i); lia.
Qed.

Lemma zero_ext_inrange:
  forall n i, Int.unsigned i <= two_p n - 1 ->
       Int.zero_ext n i = i.
intros.
destruct (zlt n Int.zwordsize);
  [ | apply Int.zero_ext_above; auto].
destruct (zlt n 0).
assert (n-1 < 0) by lia.
repeat rewrite two_p_neg in H by lia.
pose proof (Int.unsigned_range i).
lia.
destruct (zeq n 0).
subst n.
simpl in H.
assert (Int.unsigned i = 0) by (pose proof (Int.unsigned_range i); lia).
clear - H0.
rewrite <- (Int.repr_unsigned i).
rewrite H0.
reflexivity.
assert (0 < n < Int.zwordsize) by lia.
clear - H H0.
apply Int.same_bits_eq; intros j ?.
rewrite (Int.bits_zero_ext n i j) by lia.
if_tac; auto.
symmetry.
apply Int.bits_size_2.
apply Z.ge_le.
apply Int.size_interval_2.
lia.
split.
apply Int.unsigned_range.
assert (two_p n <= two_p j); try lia.
apply two_p_monotone.
lia.
Qed.

End val_lemmas.
Module Export mpred.
Import VST.veric.base.
Import VST.veric.rmaps.
Export VST.veric.compspecs.
Import compcert.lib.Maps.

Set Implicit Arguments.
Module Map.
Section map.
Variables (B : Type).

Definition t := positive -> option B.

Definition get (h: t) (a:positive) : option B := h a.

Definition set (a:positive) (v: B) (h: t) : t :=
  fun i => if ident_eq i a then Some v else h i.

Definition remove (a: positive) (h: t) : t :=
  fun i => if ident_eq i a then None else h i.

Lemma gss h x v : get (set x v h) x = Some v.
unfold get, set; if_tac; intuition.
Qed.

Lemma gso h x y v : x<>y -> get (set x v h) y = get h y.
unfold get, set; intros; if_tac; intuition.
Qed.

Lemma grs h x : get (remove x h) x = None.
unfold get, remove; intros; if_tac; intuition.
Qed.

Lemma ext h h' : (forall x, get h x = get h' x) -> h=h'.
intros.
extensionality x.
apply H.
Qed.

Lemma override (a: positive) (b b' : B) h : set a b' (set a b h) = set a b' h.
apply ext; intros; unfold get, set; if_tac; intuition.
Qed.

Lemma gsspec:
    forall (i j: positive) (x: B) (m: t),
    get (set j x m) i = if ident_eq i j then Some x else get m i.
intros.
unfold get; unfold set; if_tac; intuition.
Qed.

Lemma override_same : forall id t (x:B), get t id = Some x -> set id x t = t.
intros.
unfold set.
unfold get in H.
 apply ext.
intros.
unfold get.
if_tac; subst; auto.
Qed.

End map.

End Map.

Section FUNSPEC.

Definition genviron := Map.t block.

Definition venviron := Map.t (block * type).

Definition tenviron := Map.t val.

Inductive environ : Type :=
 mkEnviron: forall (ge: genviron) (ve: venviron) (te: tenviron), environ.

Definition ge_of (rho: environ) : genviron :=
  match rho with mkEnviron ge ve te => ge end.

Definition ve_of (rho: environ) : venviron :=
  match rho with mkEnviron ge ve te => ve end.

Definition te_of (rho: environ) : tenviron :=
  match rho with mkEnviron ge ve te => te end.

Definition mpred := pred rmap.

Definition argsEnviron:Type := genviron * (list val).

Definition AssertTT (A: TypeTree): TypeTree :=
  ArrowType A (ArrowType (ConstType environ) Mpred).

Definition ArgsTT (A: TypeTree): TypeTree :=
  ArrowType A (ArrowType (ConstType argsEnviron) Mpred).

Definition SpecArgsTT (A: TypeTree): TypeTree :=
  ArrowType A
  (PiType bool (fun b => ArrowType (ConstType
                                         (if b
                                          then argsEnviron
                                          else environ))
                                    Mpred)).

End FUNSPEC.

Definition packPQ {A: rmaps.TypeTree}
  (P: forall ts, dependent_type_functor_rec ts (ArgsTT A) mpred)
  (Q: forall ts, dependent_type_functor_rec ts (AssertTT A) mpred):
  forall ts, dependent_type_functor_rec ts (SpecArgsTT A) mpred.
intros ts a b.
destruct b.
apply (P ts a).
apply (Q ts a).
Defined.

Definition int_range (sz: intsize) (sgn: signedness) (i: int) :=
 match sz, sgn with
 | I8, Signed => -128 <= Int.signed i < 128
 | I8, Unsigned => 0 <= Int.unsigned i < 256
 | I16, Signed => -32768 <= Int.signed i < 32768
 | I16, Unsigned => 0 <= Int.unsigned i < 65536
 | I32, Signed => -2147483648 <= Int.signed i < 2147483648
 | I32, Unsigned => 0 <= Int.unsigned i < 4294967296
 | IBool, _ => 0 <= Int.unsigned i < 256
 end.

Lemma size_chunk_sizeof: forall env t ch, access_mode t = By_value ch -> sizeof env t = Memdata.size_chunk ch.
  intros.
  destruct t; inversion H.
  -
 destruct i, s; inversion H1; reflexivity.
  -
 destruct s; inversion H1; reflexivity.
  -
 destruct f; inversion H1; reflexivity.
  -
 inversion H1; reflexivity.
Qed.

Arguments sizeof {env} !t / .

Goal forall {cs: compspecs} t, sizeof t >= 0.
intros.
apply sizeof_pos.
Abort.

Fixpoint typelist_of_type_list (params : list type) : typelist :=
  match params with
  | nil => Tnil
  | ty :: rem => Tcons ty (typelist_of_type_list rem)
  end.

Fixpoint typelist2list (tl: typelist) : list type :=
 match tl with Tcons t r => t::typelist2list r | Tnil => nil end.

Lemma TTL1 l: typelist_of_type_list (map snd l) = type_of_params l.
induction l; simpl; trivial.
destruct a.
f_equal; trivial.
Qed.

Lemma TTL2 l: (typlist_of_typelist (typelist_of_type_list l)) = map typ_of_type l.
induction l; simpl; trivial.
f_equal; trivial .
Qed.

Lemma TTL4 l: map snd l = typelist2list (type_of_params l).
induction l; simpl; trivial.
destruct a.
simpl.
f_equal; trivial.
Qed.

Lemma TTL5 {l}: typelist2list (typelist_of_type_list l) = l.
induction l; simpl; trivial.
f_equal; trivial.
Qed.

Definition idset := PTree.t unit.

Definition eval_id (id: ident) (rho: environ) := force_val (Map.get (te_of rho) id).

Definition env_set (rho: environ) (x: ident) (v: val) : environ :=
  mkEnviron (ge_of rho) (ve_of rho) (Map.set x v (te_of rho)).

Lemma eval_id_same: forall rho id v, eval_id id (env_set rho id v) = v.
unfold eval_id; intros; simpl.
unfold force_val.
rewrite Map.gss.
auto.
Qed.
#[export] Hint Rewrite eval_id_same : normalize norm.

Lemma eval_id_other: forall rho id id' v,
   id<>id' -> eval_id id' (env_set rho id v) = eval_id id' rho.
 unfold eval_id, force_val; intros.
simpl.
rewrite Map.gso; auto.
Qed.
#[export] Hint Rewrite eval_id_other using solve [clear; intro Hx; inversion Hx] : normalize norm.

Lemma approx_hered_derives_e n P Q: predicates_hered.derives P Q -> predicates_hered.derives (approx n P) (approx n Q).
intros.
unfold approx.
intros m.
simpl.
intros [? ?].
split; auto.
Qed.
Lemma approx_derives_e n P Q: P |-- Q -> approx n P |-- approx n Q.
Proof.
intros.
apply approx_hered_derives_e.
apply H.
Qed.

Lemma hered_derives_derives P Q: predicates_hered.derives P Q -> derives P Q.
trivial.
Qed.

End mpred.
Module Export address_conflict.

Import VST.veric.base.

Lemma range_overlap_spec: forall l1 n1 l2 n2,
  n1 > 0 ->
  n2 > 0 ->
  (range_overlap l1 n1 l2 n2 <-> adr_range l1 n1 l2 \/ adr_range l2 n2 l1).
  intros.
  unfold range_overlap, adr_range.
  destruct l1, l2.
  split; intros.
  +
 destruct H1 as [[? ?] [[? ?] [? ?]]].
    subst.
    destruct (zle z z0); [left | right].
    -
 split; auto.
      lia.
    -
 split; auto.
      lia.
  +
 destruct H1 as [[? ?] | [? ?]].
    -
 exists (b0, z0).
repeat split; auto; lia.
    -
 exists (b, z).
repeat split; auto; lia.
Qed.

Lemma range_overlap_comm: forall l1 n1 l2 n2, range_overlap l1 n1 l2 n2 -> range_overlap l2 n2 l1 n1.
  unfold range_overlap.
  intros.
  destruct H as [l ?].
  exists l.
  tauto.
Qed.

Lemma range_overlap_non_zero: forall l1 n1 l2 n2, range_overlap l1 n1 l2 n2 -> n1 > 0 /\ n2 > 0.
  unfold range_overlap.
  intros.
  destruct H as [l [? ?]].
  apply adr_range_non_zero in H.
  apply adr_range_non_zero in H0.
  auto.
Qed.

Definition pointer_range_overlap p n p' n' :=
  exists l l', val2adr p l /\ val2adr p' l' /\ range_overlap l n l' n'.

Lemma pointer_range_overlap_dec: forall p1 n1 p2 n2, {pointer_range_overlap p1 n1 p2 n2} + {~ pointer_range_overlap p1 n1 p2 n2}.
  unfold pointer_range_overlap.
  intros.
  destruct p1;
  try solve
   [right;
    intros [[? ?] [[? ?] [HH [_ _]]]];
    inversion HH].
  destruct p2;
  try solve
   [right;
    intros [[? ?] [[? ?] [_ [HH _]]]];
    inversion HH].
  destruct (zlt 0 n1); [| right; intros [[? ?] [[? ?] [_ [_ HH]]]]; apply range_overlap_non_zero in HH; lia].
  destruct (zlt 0 n2); [| right; intros [[? ?] [[? ?] [_ [_ HH]]]]; apply range_overlap_non_zero in HH; lia].
  destruct (eq_block b b0).
  +
 subst b0.
    unfold val2adr.
    forget (Ptrofs.unsigned i) as i1;
    forget (Ptrofs.unsigned i0) as i2;
    clear i i0.
    destruct (range_dec i1 i2 (i1 + n1)); [| destruct (range_dec i2 i1 (i2 + n2))].
    -
 left.
      exists (b, i1), (b, i2); repeat split; auto.
      apply range_overlap_spec; try lia.
      left; simpl; auto.
    -
 left.
      exists (b, i1), (b, i2); repeat split; auto.
      apply range_overlap_spec; try lia.
      right; simpl; auto.
    -
 right.
      intros [[? ?] [[? ?] [? [? HH]]]].
      inversion H; inversion H0; subst.
      apply range_overlap_spec in HH; [| lia | lia].
      simpl in HH; lia.
  +
 right.
    intros [[? ?] [[? ?] [? [? HH]]]].
    simpl in H, H0.
    inversion H; inversion H0; subst.
    apply range_overlap_spec in HH; [| lia | lia].
    simpl in HH.
    pose proof @eq_sym _ b0 b.
    tauto.
Qed.

Lemma pointer_range_overlap_refl: forall p n1 n2,
  isptr p ->
  n1 > 0 ->
  n2 > 0 ->
  pointer_range_overlap p n1 p n2.
  intros.
  destruct p; try inversion H.
  exists (b, Ptrofs.unsigned i), (b, Ptrofs.unsigned i).
  repeat split; auto.
  apply range_overlap_spec; auto.
  left.
  simpl.
  split; auto; lia.
Qed.

Lemma pointer_range_overlap_comm: forall p1 n1 p2 n2,
  pointer_range_overlap p1 n1 p2 n2 <->
  pointer_range_overlap p2 n2 p1 n1.
  cut (forall p1 n1 p2 n2,
         pointer_range_overlap p1 n1 p2 n2 ->
         pointer_range_overlap p2 n2 p1 n1).
{
    intros.
    pose proof H p1 n1 p2 n2.
    pose proof H p2 n2 p1 n1.
    tauto.
  }
  unfold pointer_range_overlap.
  intros.
  destruct H as [l [l' [? [? ?]]]].
  exists l', l.
  repeat split; auto.
  apply range_overlap_comm.
  auto.
Qed.

Lemma pointer_range_overlap_non_zero: forall p1 n1 p2 n2,
  pointer_range_overlap p1 n1 p2 n2 -> n1 > 0 /\ n2 > 0.
  intros.
  destruct H as [? [? [? [? ?]]]].
  eapply range_overlap_non_zero; eauto.
Qed.

Lemma pointer_range_overlap_isptr: forall p1 n1 p2 n2,
  pointer_range_overlap p1 n1 p2 n2 -> isptr p1 /\ isptr p2.
  intros.
  destruct H as [? [? [? [? ?]]]].
  destruct p1, p2; try solve [inversion H | inversion H0].
  simpl; auto.
Qed.

End address_conflict.
Module Export res_predicates.
Import VST.msl.log_normalize.
Export VST.veric.base.
Import VST.veric.rmaps.
Import VST.veric.shares.
Local Open Scope pred.

Program Definition kind_at (k: kind) (l: address) : pred rmap :=
   fun m => exists rsh, exists sh, exists pp, m @ l = YES rsh sh k pp.
 Next Obligation.
   split; repeat intro.
   destruct H0 as [rsh [sh [pp ?]]].
   generalize (eq_sym (resource_at_approx a l)); intro.
   generalize (age1_resource_at a a'  H l (a@l) H1); intro.
   rewrite H0 in H2.
simpl in H2.
eauto.

  apply rmap_order in H as (_ & <- & _); auto.
 Qed.

Definition spec : Type :=  forall (sh: Share.t) (l: AV.address), pred rmap.

Program Definition yesat_raw (pp: preds) (k: kind)
                           (sh: share) (rsh: readable_share sh) (l: address) : pred rmap :=
   fun phi => phi @ l = YES sh rsh k (preds_fmap (approx (level phi)) (approx (level phi)) pp).
  Next Obligation.
   split; repeat intro.
   apply (age1_resource_at a a' H l (YES sh rsh k pp) H0).

  apply rmap_order in H as (<- & <- & _); auto.
  Qed.

Obligation Tactic := idtac.

Program Definition yesat (pp: preds) (k: kind) : spec :=
 fun (sh: share) (l: AV.address) (m: rmap) =>
  exists rsh, yesat_raw pp k sh rsh l m.
  Next Obligation.
    split; repeat intro.
    destruct H0 as [p ?]; exists p.
    apply pred_hereditary with a; auto.

    destruct H0 as [p ?]; exists p.
    apply pred_upclosed with a; auto.
  Qed.

Program Definition pureat (pp: preds) (k: kind) (l: AV.address): pred rmap :=
       fun phi => phi @ l = PURE k (preds_fmap (approx (level phi)) (approx (level phi)) pp).
  Next Obligation.
    split; repeat intro.
   apply (age1_resource_at a a' H l (PURE k pp) H0).

   apply rmap_order in H as (<- & <- & _); auto.
  Qed.

Ltac do_map_arg :=
match goal with |- ?a = ?b =>
  match a with context [map ?x _] =>
    match b with context [map ?y _] => replace y with x; auto end end end.

Lemma yesat_raw_eq_aux:
  forall pp k rsh sh l,
    hereditary age
    (fun phi : rmap =>
     resource_fmap (approx (level phi)) (approx (level phi)) (phi @ l) =
     resource_fmap (approx (level phi)) (approx (level phi)) (YES rsh sh k pp)) /\
    hereditary ext_order
    (fun phi : rmap =>
     resource_fmap (approx (level phi)) (approx (level phi)) (phi @ l) =
     resource_fmap (approx (level phi)) (approx (level phi)) (YES rsh sh k pp)).
Proof.
 split; repeat intro.
  generalize (resource_at_approx a l); intro.
  generalize (resource_at_approx a' l); intro.
  rewrite H2.
  rewrite H1 in H0.
  apply (age1_resource_at a a'  H); auto.

  apply rmap_order in H as (<- & <- & _); auto.
Qed.

Lemma yesat_raw_eq: yesat_raw =
  fun pp k rsh sh l =>
  ((exist (fun p => hereditary age p /\ hereditary ext_order p)
   (fun phi =>
   resource_fmap (approx (level phi)) (approx (level phi)) (phi @ l) =
   resource_fmap (approx (level phi)) (approx (level phi)) (YES rsh sh k pp))
   (yesat_raw_eq_aux pp k rsh sh l)) : pred rmap).
Proof.
unfold yesat_raw.
extensionality pp k rsh sh l.
apply exist_ext.
extensionality phi.
apply prop_ext; split; intros.
rewrite H.
simpl.
f_equal.
rewrite preds_fmap_fmap.
rewrite approx_oo_approx.
auto.
simpl in H.
revert H; case_eq (phi @ l); simpl; intros; inv H0.
f_equal; try apply proof_irr.
revert H4; destruct p as [?A ?p]; destruct pp as [?A ?p]; simpl; intros; auto; inv H4.
clear - H.
repeat f_equal.
revert H; unfold resource_at.
 rewrite rmap_level_eq.
case_eq (unsquash phi); simpl; intros.
rename r0 into f.
pose proof I.
set (phi' := ((fun l' => if eq_dec l' l
       then YES rsh r k (SomeP A0 (fun i => fmap _ (approx n) (approx n) (p i))) else fst f l', snd f)): rmap').
assert (phi = squash (n,phi')).
apply unsquash_inj.
replace (unsquash phi) with (unsquash (squash (unsquash phi))).
2: rewrite squash_unsquash; auto.
rewrite H.
do 2 rewrite unsquash_squash.
f_equal.
unfold phi'.
clear - H0.
simpl.
unfold rmap_fmap.
unfold compose.
f_equal.
extensionality x.
simpl.
if_tac; auto.
subst.
rewrite H0.
simpl.
do 2 apply f_equal.
extensionality.
rewrite fmap_app.
rewrite approx_oo_approx; auto.
subst phi.
unfold phi' in H.
rewrite unsquash_squash in H.
injection H; clear H; intros.
destruct f; simpl in *; inv H.
generalize (equal_f H3 l); intro.
rewrite H0 in H.
clear - H.
unfold compose in H.
rewrite if_true in H; auto.
simpl in H.
revert H; generalize p at 2 3.
intros q ?H.
apply YES_inj in H.
match goal with
| H: ?A = ?B |- _ =>
  assert (snd A = snd B)
end.
rewrite H; auto.
simpl in H0.
apply SomeP_inj2 in H0.
subst q.
extensionality i.
rewrite fmap_app.
rewrite approx_oo_approx.
auto.
Qed.

Lemma yesat_eq_aux:
  forall pp k sh l,
    hereditary age
    (fun m : rmap =>
      exists rsh,
     resource_fmap (approx (level m)) (approx (level m)) (m @ l) =
     resource_fmap (approx (level m)) (approx (level m)) (YES sh rsh k pp)) /\
    hereditary ext_order
    (fun m : rmap =>
      exists rsh,
     resource_fmap (approx (level m)) (approx (level m)) (m @ l) =
     resource_fmap (approx (level m)) (approx (level m)) (YES sh rsh k pp)).
Proof.
 split; repeat intro.
  destruct H0 as [p ?]; exists p.
  rewrite resource_at_approx.
  rewrite resource_at_approx in H0.
  apply (age1_resource_at a a' H); auto.

 apply rmap_order in H as (<- & <- & _); auto.
Qed.

Lemma yesat_eq: yesat = fun pp k sh l =>
 exist (fun p => hereditary age p /\ hereditary ext_order p)
  (fun m =>
  exists rsh,
   resource_fmap (approx (level m)) (approx (level m)) (m @ l) =
   resource_fmap (approx (level m)) (approx (level m)) (YES sh rsh k pp))
   (yesat_eq_aux pp k sh l).
Proof.
unfold yesat.
extensionality pp k sh l.
apply exist_ext.
extensionality w.
apply exists_ext; intro p.
rewrite yesat_raw_eq.
auto.
Qed.

Lemma map_compose_approx_succ_e:
  forall A n pp pp',
       map (compose (A:=A) (approx (S n))) pp =
    map (compose (A:=A) (approx (S n))) pp' ->
  map (compose (A:=A) (approx n)) pp = map (compose (A:=A) (approx n)) pp'.
induction pp; intros.
destruct pp'; inv H; auto.
destruct pp'; inv H; auto.
simpl.
rewrite <- (IHpp pp'); auto.
replace (approx n oo a) with (approx n oo p); auto.
clear - H1.
extensionality x.
apply pred_ext'.
extensionality w.
generalize (equal_f H1 x); clear H1; intro.
unfold compose in *.
assert (approx (S n) (a x) w <-> approx (S n) (p x) w).
rewrite H; intuition.
simpl.
apply and_ext'; auto; intros.
apply prop_ext.
intuition.
destruct H3; auto.
split; auto.
destruct H2; auto.
split; auto.
Qed.

Program Definition noat (l: AV.address) : pred rmap :=
    fun m => identity (m @ l).
 Next Obligation.
    split; repeat intro.
    apply (proj1 (age1_resource_at_identity _ _ l H) H0); auto.

    apply rmap_order in H as (_ & Hr & _); rewrite <- Hr in H1; auto.
 Qed.

Definition resource_share (r: resource) : option share :=
 match r with
 | YES sh _ _ _ => Some sh
 | NO sh _ => Some sh
 | PURE _ _ => None
 end.

Definition nonlock (r: resource) : Prop :=
 match r with
 | YES _ _ k _ => isVAL k \/ isFUN k
 | NO _ _ => True
 | PURE _ _ => False
 end.

Lemma age1_nonlock: forall phi phi' l,
  age1 phi = Some phi' -> (nonlock (phi @ l) <-> nonlock (phi' @ l)).
Proof.
  intros.
  destruct (phi @ l) as [rsh | rsh sh k P |] eqn:?H.
  +
 pose proof (age1_NO phi phi' l rsh n H).
    rewrite H1 in H0.
    rewrite H0.
    reflexivity.
  +
 pose proof (age1_YES' phi phi' l rsh sh k H).
    destruct H1 as [? _].
    spec H1; [eauto |].
    destruct H1 as [P' ?].
    rewrite H1.
    reflexivity.
  +
 pose proof (age1_PURE phi phi' l k H).
    destruct H1 as [? _].
    spec H1; [eauto |].
    destruct H1 as [P' ?].
    rewrite H1.
    reflexivity.
Qed.

Lemma age1_resource_share: forall phi phi' l,
  age1 phi = Some phi' -> (resource_share (phi @ l) = resource_share (phi' @ l)).
Proof.
  intros.
  destruct (phi @ l) as [rsh | rsh sh k P |] eqn:?H.
  +
 pose proof (age1_NO phi phi' l rsh n H).
    rewrite H1 in H0.
    rewrite H0.
    reflexivity.
  +
 pose proof (age1_YES' phi phi' l rsh sh k H).
    destruct H1 as [? _].
    spec H1; [eauto |].
    destruct H1 as [P' ?].
    rewrite H1.
    reflexivity.
  +
 pose proof (age1_PURE phi phi' l k H).
    destruct H1 as [? _].
    spec H1; [eauto |].
    destruct H1 as [P' ?].
    rewrite H1.
    reflexivity.
Qed.

Lemma resource_share_join_exists: forall r1 r2 r sh1 sh2,
  resource_share r1 = Some sh1 ->
  resource_share r2 = Some sh2 ->
  join r1 r2 r ->
  exists sh, join sh1 sh2 sh /\ resource_share r = Some sh.
  intros.
  destruct r1, r2; try solve [inversion H | inversion H0];
  inv H; inv H0; inv H1;
  eexists; split; eauto.
Qed.

Lemma resource_share_join: forall r1 r2 r sh1 sh2 sh,
  resource_share r1 = Some sh1 ->
  resource_share r2 = Some sh2 ->
  join r1 r2 r ->
  join sh1 sh2 sh ->
  resource_share r = Some sh.
  intros.
  destruct (resource_share_join_exists _ _ _ _ _ H H0 H1) as [sh' [? ?]].
  rewrite H4.
  f_equal.
  eapply join_eq; eauto.
Qed.

Lemma resource_share_joins: forall r1 r2 sh1 sh2,
  resource_share r1 = Some sh1 ->
  resource_share r2 = Some sh2 ->
  joins r1 r2 ->
  joins sh1 sh2.
  intros.
  destruct H1 as [r ?].
  destruct (resource_share_join_exists _ _ _ _ _ H H0 H1) as [sh [? ?]].
  exists sh.
  auto.
Qed.

Lemma nonlock_join: forall r1 r2 r,
  nonlock r1 ->
  nonlock r2 ->
  join r1 r2 r ->
  nonlock r.
  intros.
  destruct r1, r2; inv H1; auto.
Qed.

Program Definition nonlockat (l: AV.address): pred rmap :=
  fun m => nonlock (m @ l).
 Next Obligation.
    split; repeat intro.
    unfold resource_share in *.
    destruct (a @ l) eqn:?H.
    +
 rewrite (necR_NO a a' l _ n) in H1 by (constructor; auto).
      rewrite H1; assumption.
    +
 eapply necR_YES in H1; [ | constructor; eassumption].
      rewrite H1; assumption.
    +
 eapply necR_PURE in H1; [ | constructor; eassumption].
      rewrite H1; assumption.
    +
 apply rmap_order in H as (_ & <- & _); auto.
 Qed.

Program Definition shareat (l: AV.address) (sh: share): pred rmap :=
  fun m => resource_share (m @ l) = Some sh.
 Next Obligation.
    split; repeat intro.
    unfold resource_share in *.
    destruct (a @ l) eqn:?H.
    +
 rewrite (necR_NO a a' l _ n) in H1 by (constructor; auto).
      rewrite H1; assumption.
    +
 eapply necR_YES in H1; [ | constructor; eassumption].
      rewrite H1; assumption.
    +
 inv H0.
    +
 apply rmap_order in H as (_ & <- & _); auto.
 Qed.

Program Definition jam {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A} {EO: Ext_ord A} {EA: Ext_alg A} {B: Type} {S': B -> Prop} (S: forall l, {S' l}+{~ S' l}) (P Q: B -> pred A) : B -> pred A :=
  fun (l: B) m => if S l then P l m else Q l m.
 Next Obligation.
    split; repeat intro.
  if_tac; try (eapply pred_hereditary; eauto).
  if_tac; try (eapply pred_upclosed; eauto).
 Qed.

Lemma jam_true: forall A JA PA SA agA AgeA EO EA B (S': B -> Prop) S P Q loc, S' loc -> @jam A JA PA SA agA AgeA EO EA B S' S P Q loc = P loc.
intros.
apply pred_ext'.
extensionality m; unfold jam.
simpl.
rewrite if_true; auto.
Qed.

Lemma jam_false: forall A JA PA SA agA AgeA EO EA B (S': B -> Prop) S P Q loc, ~ S' loc -> @jam A JA PA SA agA AgeA EO EA B S' S P Q loc = Q loc.
intros.
apply pred_ext'.
extensionality m; unfold jam.
simpl; rewrite if_false; auto.
Qed.

Lemma boxy_jam:  forall (m: modality) A (S': A -> Prop) S P Q,
      (forall (x: A), boxy m (P x)) ->
      (forall x, boxy m (Q x)) ->
      forall x, boxy m (@jam rmap _ _ _ _ _ _ _ A S' S P Q x).
  intros.
   unfold boxy in *.
   apply pred_ext; intros w ?.
   unfold jam in *.
   simpl in *; if_tac.
rewrite <- H .
simpl.
apply H1.
   rewrite <- H0; simpl; apply H1.
   simpl in *; if_tac.
    rewrite <- H in H1; auto.
   rewrite <- H0 in H1; auto.
Qed.

Definition extensible_jam: forall A (S': A -> Prop) S (P Q: A -> pred rmap),
      (forall (x: A), boxy extendM (P x)) ->
      (forall x, boxy extendM (Q x)) ->
      forall x, boxy extendM  (@jam _ _ _ _ _ _ _ _ _ S' S P Q x).
  apply boxy_jam; auto.
Qed.

Definition jam_vacuous:
  forall A JA PA SA agA AgeA EO EA B S S' P Q, (forall x:B, ~ S x) -> @jam A JA PA SA agA AgeA EO EA B S S' P Q = Q.
intros.
extensionality l; apply pred_ext'; extensionality w.
unfold jam.
simpl; rewrite if_false; auto.
Qed.

Lemma make_sub_rmap: forall w (P: address -> Prop) (P_DEC: forall l, {P l} + {~ P l}),
  (forall l sh k, P l -> res_option (w @ l) = Some (sh, k) -> isVAL k \/ isFUN k) ->
  {w' | level w' = level w /\ resource_at w' =
       (fun l => if P_DEC l then w @ l else core (w @ l)) /\ ghost_of w' = ghost_of w}.
Proof.
  intros.
  apply remake_rmap.
  intros.
    if_tac; [left; eauto |].
    destruct (w @ l) eqn:?H; rewrite ?core_NO, ?core_YES, ?core_PURE; simpl; auto.
    left.
    exists w; split; auto.
    apply ghost_of_approx.
Qed.

Lemma make_sub_rmap_core: forall w (P: address -> Prop) (P_DEC: forall l, {P l} + {~ P l}),
  (forall l sh k, P l -> res_option (w @ l) = Some (sh, k) -> isVAL k \/ isFUN k) ->
  {w' | level w' = level w /\ resource_at w' =
       (fun l => if P_DEC l then w @ l else core (w @ l)) /\ ghost_of w' = core (ghost_of w)}.
Proof.
  intros.
  apply remake_rmap.
  intros.
    if_tac; [left; eauto |].
    destruct (w @ l) eqn:?H; rewrite ?core_NO, ?core_YES, ?core_PURE; simpl; auto.
    left.
    exists w; split; auto.
    apply ghost_fmap_core.
Qed.

Definition is_resource_pred (p: address -> pred rmap) (q: resource -> address -> nat -> Prop) :=
  forall l w, (p l) w = q (w @ l) l (level w).

Definition resource_stable (p: address -> pred rmap) :=
  forall l w w', w @ l = w' @ l -> level w = level w' -> (p l) w = (p l) w'.

Lemma is_resource_pred_resource_stable: forall {p},
  (exists q, is_resource_pred p q) -> resource_stable p.
  unfold is_resource_pred, resource_stable.
  intros.
  destruct H as [q ?]; rewrite !H.
  rewrite H0; auto.
Qed.

Lemma allp_jam_split2: forall (P Q R: address -> Prop) (p q r: address -> pred rmap)
  (P_DEC: forall l, {P l} + {~ P l})
  (Q_DEC: forall l, {Q l} + {~ Q l})
  (R_DEC: forall l, {R l} + {~ R l}),
  (exists resp, is_resource_pred p resp) ->
  (exists resp, is_resource_pred q resp) ->
  (exists resp, is_resource_pred r resp) ->
  Ensemble_join Q R P ->
  (forall l, Q l -> p l = q l) ->
  (forall l, R l -> p l = r l) ->
  (forall l m sh k, P l -> (p l) m -> res_option (m @ l) = Some (sh, k) -> isVAL k \/ isFUN k) ->
  allp (jam P_DEC p noat) =
  (allp (jam Q_DEC q noat)) * (allp (jam R_DEC r noat)).
Proof.
  intros until R_DEC.
  intros ST_P ST_Q ST_R.
  intros [] ? ? ?.
  apply pred_ext; intros w; simpl; intros.
  +
 destruct (make_sub_rmap_core w Q Q_DEC) as [w1 [? ?]].
    {
      intros.
eapply H3; [| | eauto].
      +
 firstorder.
      +
 specialize (H4 l); if_tac in H4; [auto | firstorder].
    }
    destruct (make_sub_rmap w R R_DEC) as [w2 [? ?]].
    {
      intros.
eapply H3; [| | eauto].
      +
 firstorder.
      +
 specialize (H4 l); if_tac in H4; [auto | firstorder].
    }
    exists w1, w2.
    split3; auto.
    -
 apply resource_at_join2; try congruence.
      intro l.
      destruct H6, H8.
      rewrite H6, H8.
      pose proof core_unit (w @ l).
      destruct (Q_DEC l), (R_DEC l).
      *
 firstorder.
      *
 apply join_comm; auto.
      *
 auto.
      *
 specialize (H4 l).
        rewrite if_false in H4 by firstorder.
        rewrite identity_core by auto.
        apply core_duplicable.
      *
 destruct H6 as [_ ->], H8 as [_ ->].
        apply core_unit.
    -
 intros l.
      specialize (H4 l).
      if_tac.
      *
 rewrite <- H1 by auto.
        rewrite if_true in H4 by firstorder.
        erewrite <- (is_resource_pred_resource_stable ST_P); [eauto | | auto].
        destruct H6; rewrite H6, if_true by auto; auto.
      *
 destruct H6; rewrite H6, if_false by auto.
        apply core_identity.
    -
 intros l.
      specialize (H4 l).
      if_tac.
      *
 rewrite <- H2 by auto.
        rewrite if_true in H4 by firstorder.
        erewrite <- (is_resource_pred_resource_stable ST_P); [eauto | | auto].
        destruct H8; rewrite H8, if_true by auto; auto.
      *
 destruct H8; rewrite H8, if_false by auto.
        apply core_identity.
  +
 destruct H4 as [y [z [? [H5 H6]]]].
    specialize (H5 b); specialize (H6 b).
    if_tac.
    -
 if_tac in H5; if_tac in H6.
      *
 firstorder.
      *
 rewrite H1 by auto.
        erewrite (is_resource_pred_resource_stable ST_Q); [eauto | | apply join_level in H4; symmetry; tauto].
        apply resource_at_join with (loc := b) in H4.
        apply join_comm, H6 in H4.
        auto.
      *
 rewrite H2 by auto; auto.
        erewrite (is_resource_pred_resource_stable ST_R); [eauto | | apply join_level in H4; symmetry; tauto].
        apply resource_at_join with (loc := b) in H4.
        apply H5 in H4.
        auto.
      *
 firstorder.
    -
 rewrite if_false in H5 by firstorder.
      rewrite if_false in H6 by firstorder.
      apply resource_at_join with (loc := b) in H4.
      apply H5 in H4; rewrite <- H4; auto.
Qed.

Lemma allp_jam_overlap: forall (P Q: address -> Prop) (p q: address -> pred rmap)
  (P_DEC: forall l, {P l} + {~ P l})
  (Q_DEC: forall l, {Q l} + {~ Q l}),
  (exists resp, is_resource_pred p resp) ->
  (exists resp, is_resource_pred q resp) ->
  (forall l w1 w2, p l w1 -> q l w2 -> joins w1 w2 -> False) ->
  (exists l, P l /\ Q l) ->
  allp (jam P_DEC p noat) * allp (jam Q_DEC q noat) |-- FF.
Proof.
  intros.
  intro w; simpl; intros.
  destruct H3 as [w1 [w2 [? [? ?]]]].
  destruct H2 as [l ?].
  specialize (H4 l).
  specialize (H5 l).
  rewrite if_true in H4, H5 by tauto.
  apply (H1 l w1 w2); auto.
  eauto.
Qed.

Lemma yesat_join_diff:
  forall pp pp' k k' sh sh' l w, k <> k' ->
                  yesat pp k sh l w -> yesat pp' k' sh' l w -> False.
unfold yesat, yesat_raw; intros.
destruct H0 as [p ?].
destruct H1 as [p' ?].
simpl in *; inversion2 H0 H1.
contradiction H; auto.
Qed.

Lemma yesat_raw_join:
  forall pp k (sh1 sh2 sh3: Share.t) rsh1 rsh2 rsh3 l phi1 phi2 phi3,
   join sh1 sh2 sh3 ->
   yesat_raw pp k sh1 rsh1 l phi1 ->
   yesat_raw pp k sh2 rsh2 l phi2 ->
   join phi1 phi2 phi3 ->
   yesat_raw pp k sh3 rsh3 l phi3.
unfold yesat_raw;
intros until 1; rename H into HR; intros.
simpl in H,H0|-*.
assert (level phi2 = level phi3) by (apply join_level in H1; intuition).
rewrite H2 in *; clear H2.
assert (level phi1 = level phi3) by  (apply join_level in H1; intuition).
rewrite H2 in *; clear H2.
generalize (resource_at_join _ _ _ l H1); clear H1.
revert H H0.
case_eq (phi1 @ l); intros; try discriminate.
inv H0.
revert H1 H2; case_eq (phi2 @ l); intros; try discriminate.
inv H1.
inv H2.
inv H0.
pose proof (join_eq HR RJ).
subst sh5.
clear RJ.
repeat proof_irr.
auto.
Qed.

Lemma nonunit_join: forall A {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{CA: Disj_alg A} (x y z: A),
  nonunit x -> join x y z -> nonunit z.
intros.
intro; intro.
apply unit_identity in H1.
apply split_identity in H0; auto.
apply nonunit_nonidentity in H.
contradiction.
Qed.

Lemma yesat_join:
  forall pp k sh1 sh2 sh3 l m1 m2 m3,
   join sh1 sh2 sh3 ->
   yesat pp k sh1 l m1 ->
   yesat pp k sh2 l m2 ->
   join m1 m2 m3 ->
   yesat pp k sh3 l m3.
intros.
destruct H0 as [p1 ?].
destruct H1 as [p2 ?].
assert (p3: readable_share sh3).
eapply join_readable1; eauto.
exists p3.
eapply yesat_raw_join with (phi1 := m1); eauto.
Qed.

Definition spec_parametric (Q: address -> spec) : Prop :=
   forall l l', exists pp, exists ok,
             forall sh m,
           Q l sh l' m =
            (exists p, exists k, ok k /\ m @ l' =
                 YES sh p k (preds_fmap (approx (level m)) (approx (level m)) pp)).

Lemma YES_ext:
  forall sh sh' rsh rsh' k p, sh=sh' -> YES sh rsh k p = YES sh' rsh' k p.
intros.
subst.
f_equal.
apply proof_irr.
Qed.

Definition VALspec : spec :=
       fun (sh: Share.t) (l: address) =>
          allp (jam (eq_dec l)
                                  (fun l' => EX v: memval,
                                                yesat NoneP (VAL v) sh l')
                                  noat).

Definition VALspec_range (n: Z) : spec :=
     fun (sh: Share.t) (l: address) =>
          allp (jam (adr_range_dec l n)
                                  (fun l' => EX v: memval,
                                                yesat NoneP (VAL v) sh l')
                                  noat).

Definition nonlock_permission_bytes (sh: share) (a: address) (n: Z) : pred rmap :=
  allp (jam (adr_range_dec a n) (fun i => shareat i sh && nonlockat i) noat).

Definition nthbyte (n: Z) (l: list memval) : memval :=
     nth (Z.to_nat n) l Undef.

Definition address_mapsto (ch: memory_chunk) (v: val) : spec :=
        fun (sh: Share.t) (l: AV.address) =>
           EX bl: list memval,
               !! (length bl = size_chunk_nat ch  /\ decode_val ch bl = v /\ (align_chunk ch | snd l))  &&
                (allp (jam (adr_range_dec l (size_chunk ch))
                                    (fun loc => yesat NoneP (VAL (nth (Z.to_nat (snd loc - snd l)) bl Undef)) sh loc)
                                    noat)).

Lemma address_mapsto_align: forall ch v sh l,
  address_mapsto ch v sh l = address_mapsto ch v sh l && !! (align_chunk ch | snd l).
Proof.
  intros.
  pose proof (@add_andp (pred rmap) _); simpl in H.
apply H; clear H.
  constructor; unfold address_mapsto.
  apply exp_left; intro.
  apply andp_left1.
  intros ? [? [? ?]].
  auto.
Qed.

Lemma address_mapsto_fun:
  forall ch sh sh' l v v',
          (address_mapsto ch v sh l * TT) && (address_mapsto ch v' sh' l * TT) |-- !!(v=v').
Proof.
intros.
intros m [? ?].
unfold prop.
destruct H as [m1 [m2 [J [[bl [[Hlen [? _]] ?]] _]]]].
destruct H0 as [m1' [m2' [J' [[bl' [[Hlen' [? _]] ?]] _]]]].
subst.
assert (forall i, nth_error bl i = nth_error bl' i).
intro i; specialize(H1 (fst l, snd l + Z_of_nat i)); specialize( H2 (fst l, snd l + Z_of_nat i)).
unfold jam in *.
destruct l as [b z].
simpl in *.
if_tac in H1.
destruct H as [_ ?].
replace (z + Z_of_nat i - z) with (Z_of_nat i) in * by lia.
assert ((i < length bl)%nat).
rewrite Hlen.
rewrite size_chunk_conv in H.
lia.
rewrite <- Hlen' in Hlen.
rewrite Nat2Z.id in *.
destruct H1; destruct H2.
unfold yesat_raw in *.
repeat rewrite preds_fmap_NoneP in *.
assert (H5: nth i bl Undef = nth i bl' Undef).
apply (resource_at_join _ _ _ (b,z + Z_of_nat i)) in J.
apply (resource_at_join _ _ _ (b,z + Z_of_nat i)) in J'.
rewrite H1 in J; rewrite H2 in J'; clear H1 H2.
inv J; inv J'; try congruence.
clear - Hlen H0 H5.
revert bl bl' Hlen H0 H5; induction i; destruct bl; destruct bl'; simpl; intros; auto; try lia.
apply IHi; auto.
lia.
assert (~ (i < length bl)%nat).
contradict H.
split; auto.
rewrite Hlen in H.
rewrite size_chunk_conv.
lia.
assert (i >= length bl)%nat by lia.
destruct (nth_error_length i bl).
rewrite H5; auto.
destruct (nth_error_length i bl').
rewrite H7; auto.
lia.
clear - H.
assert (bl=bl'); [| subst; auto].
revert bl' H; induction bl; destruct bl'; intros; auto.
specialize (H 0%nat); simpl in H.
inv H.
specialize (H 0%nat); simpl in H.
inv H.
f_equal.
specialize (H 0%nat); simpl in H.
inv H.
auto.
apply IHbl.
intro.
specialize( H (S i)).
simpl in H.
auto.
simpl; auto.
Qed.

Definition LKspec lock_size (R: pred rmap) : spec :=
   fun (sh: Share.t) (l: AV.address)  =>
    allp (jam (adr_range_dec l lock_size)
               (fun l' => yesat (SomeP Mpred (fun _ => R)) (LK lock_size (snd l' - snd l)) sh l')
               noat).

Lemma address_mapsto_old_parametric: forall ch v,
   spec_parametric (fun l sh l' => yesat NoneP (VAL (nthbyte (snd l' - snd l) (encode_val ch v))) sh l').
intros.
exists NoneP.
exists (fun k => k= VAL (nthbyte (snd l' - snd l) (encode_val ch v))).
intros.
unfold yesat.
apply exists_ext; intro p.
unfold yesat_raw.
simpl.
apply prop_ext; split; intros.
econstructor; split; [reflexivity | ].
rewrite H; f_equal.

simpl.
eauto.
destruct H as [k [? ?]].
subst; auto.
Qed.

Lemma VALspec_parametric:
  spec_parametric (fun l sh l' => EX v: memval,  yesat NoneP (VAL v) sh l').
intros.
exists NoneP.
exists (fun k => exists v, k=VAL v).
intros.
unfold yesat.
apply prop_ext; split; intros.
destruct H as [v [p ?]].
exists p.
exists (VAL v).
split; eauto.
destruct H as [p [k [[v ?] ?]]].
subst.
exists v.
exists p.
auto.
Qed.

Lemma LKspec_parametric lock_size: forall R: pred rmap,
  spec_parametric (fun l sh l' => yesat (SomeP Mpred (fun _ => R)) (LK lock_size (snd l' - snd l)) sh l').
intros.
unfold jam.
intro; intros.
simpl.
exists (SomeP Mpred (fun _ => R)).
exists (fun k => k = LK lock_size (snd l' - snd l)).
intros.
apply exists_ext; intro p.
apply prop_ext; split; intros.
rewrite H.
econstructor.
 split; eauto.

destruct H as [k [? ?]].
subst; auto.
Qed.

Definition val2address (v: val) : option AV.address :=
  match v with Vptr b ofs => Some (b, Ptrofs.signed ofs) | _ => None end.

Lemma VALspec_readable:
  forall l sh w,  (VALspec sh l * TT) %pred w -> readable l w.
unfold VALspec, readable;
intros.
destruct H as [w1 [w2 [? [? _]]]].
specialize (H0 l).
unfold jam in H0.
hnf in H0|-*; rewrite if_true in H0 by auto.
destruct H0 as [v [p ?]].
unfold yesat_raw in H0.
generalize (resource_at_join _ _ _ l H); rewrite H0; intro Hx.
inv Hx; auto.
Qed.

Lemma address_mapsto_VALspec:
  forall ch v sh l i, 0 <= i < size_chunk ch ->
        address_mapsto ch v sh l |-- VALspec sh (adr_add l i) * TT.
Proof.
intros.
intros w ?.
pose (f l' := if eq_dec (adr_add l i) l' then w @ l'
                   else if adr_range_dec l (size_chunk ch) l' then NO Share.bot bot_unreadable else w @ l').
pose (g l' := if eq_dec (adr_add l i) l' then NO Share.bot bot_unreadable else w @ l').
exploit (deallocate (w) f g); intros.
*
unfold f,g; clear f g.
destruct H0 as [b [? ?]].
specialize (H1 l0).
 hnf in H1.
if_tac in H1.
destruct H1.
 hnf in H1.
if_tac; rewrite H1; constructor.
apply join_unit2; auto.
apply join_unit1; auto.
if_tac.
contradiction H2.
unfold adr_add in H3; destruct l; destruct l0; simpl in H3.
inv H3.
split; auto.
lia.
do 3 red in H1.
apply identity_unit' in H1.
auto.
*
apply join_comm, core_unit.
*
destruct H1 as [phi1 [phi2 [? ?]]].
exists phi1; exists phi2.
split; auto.
split; auto.
unfold VALspec.
intro l'.
unfold jam in *.
destruct H0 as [bl [H0' ?]].
specialize (H0 l').
unfold jam in H0.
hnf in H0|-*; if_tac.
subst l'.
rewrite if_true in H0.
destruct H0.
unfold yesat_raw in H0.
destruct H2 as [H2 _].
pose proof (equal_f H2 (adr_add l i)).
unfold f in H3.
rewrite if_true in H3.
rewrite H0 in H3.
exists (nth (Z.to_nat (snd (adr_add l i) - snd l)) bl Undef).
exists x.
unfold yesat_raw.
hnf in H0|-*.
repeat rewrite preds_fmap_NoneP in *.
auto.
destruct l; unfold adr_range, adr_add.
split; auto.
destruct l; unfold adr_range, adr_add.
split; auto.
simpl; lia.
do 3 red.
destruct H2 as [-> _].
unfold f.
rewrite if_false; auto.
if_tac.
apply NO_identity.
apply H0.
Qed.

Lemma address_mapsto_exists:
  forall ch v sh (rsh: readable_share sh) loc w0
      (RESERVE: forall l', adr_range loc (size_chunk ch) l' -> w0 @ l' = NO Share.bot bot_unreadable),
      (align_chunk ch | snd loc) ->
      exists w, address_mapsto ch (decode_val ch (encode_val ch v)) sh loc w
                    /\ core w = core w0.
Proof.
intros.
rename H into Halign.
unfold address_mapsto.
pose (f l' := if adr_range_dec loc (size_chunk ch) l'
                     then YES sh rsh (VAL (nthbyte (snd l' - snd loc) (encode_val ch v))) NoneP
                     else core w0 @ l').
pose proof I.
destruct (make_rmap f (ghost_of w0) (level w0)) as [phi [? ?]].
extensionality l; unfold f, compose; simpl.
if_tac; simpl; auto.
rewrite <- level_core.
apply resource_at_approx.
{
 apply ghost_of_approx.
}
exists phi.
split.
+
 exists (encode_val ch v).
  split.
  split; auto.
  apply encode_val_length.
  intro l'.
  unfold jam.
  hnf.
  unfold yesat, yesat_raw, noat.
  unfold app_pred, proj1_sig.
destruct H1; rewrite H1; clear H H1.
  unfold f; clear f.
  if_tac.
  exists rsh.
  f_equal.
  rewrite <- core_resource_at.
  apply core_identity.
+
 apply rmap_ext.
do 2 rewrite level_core.
auto.
  intro l; specialize (RESERVE l).
  rewrite <- core_resource_at.
destruct H1.
rewrite H1.
unfold f.
  if_tac.
  rewrite core_YES.
  rewrite <- core_resource_at.
rewrite RESERVE; auto.
  rewrite core_NO; auto.
  rewrite <- core_resource_at; rewrite core_idem; auto.
  {
 rewrite <- core_ghost_of.
    destruct H1 as [_ ->].
    rewrite core_ghost_of; auto.
}
Qed.

Lemma VALspec1: VALspec_range 1 = VALspec.
unfold VALspec, VALspec_range.
extensionality sh l.
f_equal.
unfold jam.
extensionality l'.
apply exist_ext; extensionality m.
symmetry.
if_tac.
 subst l'.
rewrite if_true; auto.
destruct l; split; auto; lia.
rewrite if_false; auto.
destruct l; destruct l'; unfold block in *; intros [? ?]; try lia.
subst.
contradict H.
f_equal; lia.
Qed.

Lemma VALspec_range_exp_address_mapsto:
  forall ch sh l,
    (align_chunk ch | snd l) ->
    VALspec_range (size_chunk ch) sh l |-- EX v: val, address_mapsto ch v sh l.
Proof.
  intros.
  intros w ?.
  simpl in H0 |- *.
  cut (exists (b0 : list memval),
     length b0 = size_chunk_nat ch /\
     (forall b1 : address,
      if adr_range_dec l (size_chunk ch) b1
      then
       exists rsh: readable_share sh,
         w @ b1 =
         YES sh rsh
           (VAL (nth (Z.to_nat (snd b1 - snd l)) b0 Undef))
           (SomeP (ConstType unit) (fun _ => tt))
      else identity (w @ b1))).
  {
    intros.
    destruct H1 as [b0 [? ?]].
    exists (decode_val ch b0), b0.
    tauto.
  }
  rewrite !size_chunk_conv in *.
  forget (size_chunk_nat ch) as n; clear - H0.

  cut (exists b0 : list memval,
     length b0 = n /\
     (forall b1 : address,
        adr_range l (Z.of_nat n) b1 ->
       exists rsh: readable_share sh,
         w @ b1 =
         YES sh rsh
           (VAL (nth (Z.to_nat (snd b1 - snd l)) b0 Undef))
           (SomeP (ConstType unit) (fun _ => tt)))).
  {
    intros.
    destruct H as [b0 H].
    exists b0.
    split; [tauto |].
    intros b; specialize (H0 b).
    if_tac; [apply (proj2 H) |]; auto.
  }

  assert (forall b : address,
    adr_range l (Z.of_nat n) b ->
        exists (b0 : memval) (rsh : readable_share sh),
          w @ b =
          YES sh rsh (VAL b0)
            (SomeP (ConstType unit) (fun _ => tt))).
  {
    intros.
    specialize (H0 b).
    if_tac in H0; tauto.
  }
  clear H0.

  destruct l as [bl ofs].
  revert ofs H; induction n; intros.
  +
 exists nil.
    split; auto.
    intros b.
    specialize (H b).
    auto.
    intros.
    apply adr_range_non_zero in H0.
    simpl in H0; lia.
  +
 specialize (IHn (ofs + 1)).
    spec IHn.
    -
 clear - H; intros b; specialize (H b).
      intros; spec H; auto.
      apply adr_range_shift_1; auto.
    -
 assert (adr_range (bl, ofs) (Z.of_nat (S n)) (bl, ofs))
        by (rewrite Nat2Z.inj_succ; repeat split; auto; lia).
      destruct (H _ H0) as [b_hd ?H]; clear H0.
      destruct IHn as [b_tl ?H].
      exists (b_hd :: b_tl).
      split; [simpl; lia |]; destruct H0 as [_ ?].
      intros.
      apply adr_range_S_split in H2.
      destruct H2.
      *
 destruct (H0 b1 H2) as [p ?H].
        destruct b1; destruct H2 as [_ ?].
        exists p; clear - H2 H3.
        unfold snd in *.
        replace (Z.to_nat (z - ofs)) with (S (Z.to_nat (z - (ofs + 1)))); [exact H3 |].
        replace (z - ofs) with (Z.succ (z - (ofs + 1))) by lia.
        rewrite Z2Nat.inj_succ; auto.
        lia.
      *
 subst.
rewrite Z.sub_diag.
simpl nth.
        exact H1.
Qed.

Lemma address_mapsto_VALspec_range:
  forall ch v sh l,
        address_mapsto ch v sh l |-- VALspec_range (size_chunk ch) sh l.
Proof.
intros.
intros w ?.
unfold VALspec_range.
destruct H as [bl [Hbl ?]].
intro l'.
specialize ( H l').
unfold jam in *.
hnf in H|-*.
if_tac; auto.
exists (nth (Z.to_nat (snd l' - snd l)) bl Undef).
destruct H as [p ?].
exists p.
auto.
Qed.

Lemma approx_eq_i:
  forall (P Q: pred rmap) (w: rmap),
      (|> ! (P <=> Q)) w -> approx (level w) P = approx (level w) Q.
Proof.
intros.
apply pred_ext'; extensionality m'.
unfold approx.
apply and_ext'; auto; intros.
destruct (level_later_fash _ _ H0) as [m1 [? ?]].
specialize (H _ H1).
specialize (H m').
spec H.
rewrite H2; auto.
destruct H; apply prop_ext.
intuition eauto.
Qed.

Lemma level_later {A} `{H : ageable A}: forall {w: A} {n': nat},
         laterR (level w) n' ->
       exists w', laterR w w' /\ n' = level w'.
intros.
remember (level w) as n.
revert w Heqn; induction H0; intros; subst.
case_eq (age1 w); intros.
exists a; split.
constructor; auto.
symmetry; unfold age in H0; simpl in H0.
  unfold natAge1 in H0; simpl in H0.
revert H0; case_eq (level w); intros; inv H2.
  apply age_level in H1.
congruence.
rewrite age1_level0 in H1.
   rewrite H1 in H0.
inv H0.
 specialize (IHclos_trans1 _ (refl_equal _)).
  destruct IHclos_trans1 as [w2 [? ?]].
  subst.
  specialize (IHclos_trans2 _ (refl_equal _)).
  destruct IHclos_trans2 as [w3 [? ?]].
  subst.
  exists w3; split; auto.
econstructor 2; eauto.
Qed.

Lemma VALspec_range_bytes_readable:
  forall n sh loc m, VALspec_range n sh loc m -> bytes_readable loc n m.
intros; intro; intros.
specialize (H (adr_add loc i)).
hnf in H.
rewrite if_true in H.
destruct H as [v [p ?]].
hnf in H.
red.
red.
red.
rewrite H; auto.
destruct loc; split; unfold adr_add; auto.
simpl.
lia.
Qed.

Lemma VALspec_range_bytes_writable:
  forall n sh loc m, writable_share sh -> VALspec_range n sh loc m -> bytes_writable loc n m.
intros; intro; intros.
specialize (H0 (adr_add loc i)).
hnf in H0.
rewrite if_true in H0.
destruct H0 as [v [p ?]].
hnf in H0.
do 3 red.
rewrite H0; auto with extensionality.
destruct loc; split; unfold adr_add; auto.
simpl.
lia.
Qed.

Lemma yesat_join_sub:
  forall pp k l sh m m',
          join_sub m m' ->
          yesat pp k sh l m ->
         exists sh', yesat pp k sh' l m'.
intros.
unfold yesat_raw in H0.
destruct H0.
generalize (resource_at_join_sub _ _ l H); rewrite H0; intro.
assert (level m = level m').
destruct H; apply join_level in H; intuition.
destruct H1.
destruct x0; case_eq (m' @ l); intros; rewrite H3 in H1; inv H1.
do 2 econstructor.
unfold yesat_raw.
simpl.
rewrite <- H2.
 eapply H3.
exists sh1.
unfold yesat.
simpl.
exists r0.
rewrite <- H2.
rewrite H3.
subst; f_equal; auto.
Qed.

Program Definition core_load (ch: memory_chunk) (l: address) (v: val): pred rmap :=
  EX bl: list memval,
  !!(length bl = size_chunk_nat ch /\ decode_val ch bl = v /\ (align_chunk ch | snd l)) &&
    allp (jam (adr_range_dec l (size_chunk ch))
      (fun l' phi => exists sh, exists rsh, phi @ l'
        = YES sh rsh (VAL (nth (Z.to_nat (snd l' - snd l)) bl Undef)) NoneP)
      (fun _ _ => True)).
 Next Obligation.
    split; repeat intro.
    destruct H0 as [sh [rsh ?]]; exists sh, rsh.
    apply (age1_YES a a'); auto.

    apply rmap_order in H as (_ & <- & _); auto.
  Qed.
  Next Obligation.
    split; repeat intro; auto.
  Qed.

Program Definition core_load' (ch: memory_chunk) (l: address) (v: val) (bl: list memval)
  : pred rmap :=
  !!(length bl = size_chunk_nat ch /\ decode_val ch bl = v /\ (align_chunk ch | snd l)) &&
    allp (jam (adr_range_dec l (size_chunk ch))
      (fun l' phi => exists sh, exists rsh, phi @ l'
        = YES sh rsh (VAL (nth (Z.to_nat (snd l' - snd l)) bl Undef)) NoneP)
      (fun _ _ => True)).
 Next Obligation.
    split; repeat intro.
    destruct H0 as [sh [rsh ?]]; exists sh, rsh.
    apply (age1_YES a a'); auto.

    apply rmap_order in H as (_ & <- & _); auto.
  Qed.
  Next Obligation.
    split; repeat intro; auto.
  Qed.

Lemma emp_no : emp = (ALL l, noat l).
  apply pred_ext.
  -
 intros ? (? & ? & Hord) ?; simpl.
    apply rmap_order in Hord as (_ & <- & _).
    apply resource_at_identity; auto.
  -
 intros ??; exists (id_core a); split; [apply id_core_identity|].
    rewrite rmap_order, id_core_level, id_core_resource, id_core_ghost.
    split; auto; split; [|eexists; constructor].
    extensionality l; specialize (H l).
    rewrite <- core_resource_at; symmetry; apply identity_core; auto.
Qed.

Lemma VALspec_range_0: forall sh loc, VALspec_range 0 sh loc = emp.
 intros.
 rewrite emp_no.
 apply pred_ext.
 -
 intros ? H l.
simpl in *.
   specialize (H l); rewrite if_false in H; auto.
   {
 unfold adr_range.
destruct loc, l; intros []; lia.
}
 -
 intros ? H l.
simpl in *.
   rewrite if_false; auto.
   {
 unfold adr_range.
destruct loc, l; intros []; lia.
}
Qed.
#[export] Hint Resolve VALspec_range_0: normalize.

Lemma nonlock_permission_bytes_0: forall sh a, nonlock_permission_bytes sh a 0 = emp.
  intros.
  rewrite emp_no.
  apply pred_ext.
  +
 intros ? H l.
simpl in *.
    specialize (H l); rewrite if_false in H; auto.
   {
 unfold adr_range.
destruct a, l; intros []; lia.
}
  +
 intros ? H l.
simpl in *.
    rewrite if_false; auto.
   {
 unfold adr_range.
destruct a, l; intros []; lia.
}
Qed.

Lemma nonlock_permission_bytes_not_nonunit: forall sh p n,
  ~ nonunit sh ->
  nonlock_permission_bytes sh p n |-- emp.
Proof.
  intros.
  assert (sh = Share.bot).
  {
    destruct (dec_share_identity sh).
    +
 apply identity_share_bot; auto.
    +
 apply nonidentity_nonunit in n0; tauto.
  }
  subst.
  intros ? ?.
simpl in H0.
  rewrite emp_no; intros l; simpl.
  specialize (H0 l); if_tac in H0; auto.
  destruct H0 as [H0 _]; unfold resource_share in H0.
  destruct (a @ l); inv H0.
  +
 apply NO_identity.
  +
 contradiction (bot_unreadable r).
Qed.

Lemma is_resource_pred_YES_VAL sh:
  is_resource_pred
    (fun l' => EX  v: memval, yesat NoneP (VAL v) sh l')
    (fun r _ n => (exists b0 rsh, r = YES sh rsh (VAL b0)
        (SomeP (ConstType unit) (fun _ => tt)))).
hnf; intros.
reflexivity.
Qed.

Lemma is_resource_pred_nonlock_shareat sh:
  is_resource_pred
    (fun i : address => shareat i sh && nonlockat i)
    (fun r _ _ => resource_share r = Some sh /\ nonlock r).
hnf; intros.
reflexivity.
Qed.

Lemma VALspec_range_split2:
  forall (n m r: Z) (sh: Share.t) (b: block) (ofs: Z),
    r = n + m -> n >= 0 -> m >= 0 ->
    VALspec_range r sh (b, ofs) =
    VALspec_range n sh (b, ofs) * VALspec_range m sh (b, ofs + n).
  intros.
  assert (exists resp, is_resource_pred (fun l' => EX  v: memval, yesat NoneP (VAL v) sh l') resp) by (eexists; apply is_resource_pred_YES_VAL).
  apply allp_jam_split2; auto.
  +
 split; intros [? ?]; unfold adr_range.
    -
 assert (ofs <= z < ofs + r <-> ofs <= z < ofs + n \/ ofs + n <= z < ofs + n + m) by lia.
      tauto.
    -
 lia.
  +
 intros.
    simpl in H4.
    destruct (m0 @ l); try solve [inversion H5; simpl; auto].
    destruct H4 as [? [? ?]].
    inversion H4; subst.
    inversion H5; subst.
    auto.
Qed.

Lemma nonlock_permission_bytes_split2:
  forall (n m r: Z) (sh: Share.t) (b: block) (ofs: Z),
    r = n + m -> n >= 0 -> m >= 0 ->
    nonlock_permission_bytes sh (b, ofs) r =
    nonlock_permission_bytes sh (b, ofs) n *
    nonlock_permission_bytes sh (b, ofs + n) m.
  intros.
  assert (exists resp, is_resource_pred (fun i : address => shareat i sh && nonlockat i) resp) by (eexists; apply is_resource_pred_nonlock_shareat).
  apply allp_jam_split2; auto.
  +
 split; intros [? ?]; unfold adr_range.
    -
 assert (ofs <= z < ofs + r <-> ofs <= z < ofs + n \/ ofs + n <= z < ofs + n + m) by lia.
      tauto.
    -
 lia.
  +
 intros.
    destruct H4 as [_ ?].
    simpl in H4.
    destruct (m0 @ l); inv H5.
    simpl in H4; auto.
Qed.

Lemma VALspec_range_VALspec:
  forall (n : Z) (v : val) (sh : Share.t) (l : address) (i : Z),
       0 <= i < n ->
       VALspec_range n sh l
       |-- VALspec sh (adr_add l i) * TT.
Proof.
 intros.
  destruct l as [b ofs].
  rewrite (VALspec_range_split2 i (n-i) n sh b ofs); try lia.
  rewrite (VALspec_range_split2 1 (n-i-1) (n-i) sh b (ofs+i)); try lia.
  change (VALspec_range 1) with (VALspec_range 1).
  rewrite VALspec1.
  rewrite <- sepcon_assoc.
  rewrite (sepcon_comm (VALspec_range i sh (b, ofs))).
  rewrite sepcon_assoc.
  apply sepcon_derives; auto.
Qed.

Lemma VALspec_range_overlap': forall sh p1 p2 n1 n2,
  adr_range p1 n1 p2 ->
  n2 > 0 ->
  VALspec_range n1 sh p1 * VALspec_range n2 sh p2 |-- FF.
Proof.
  intros.
  intros w [w1 [w2 [? [H2 H3]]]].
  specialize (H2 p2).
  specialize (H3 p2).
  rewrite jam_true in H2 by auto.
  rewrite jam_true in H3 by (destruct p2; simpl; split; auto; lia).
  destruct H2; destruct H3.
hnf in H2,H3.
  apply (resource_at_join _ _ _ p2) in H1.
  destruct H2, H3.
  rewrite H2, H3 in H1.
  clear - x1 H1; simpl in H1.
  inv H1.
  clear - x1 RJ.
  generalize (join_self' RJ); intro.
subst sh3.
  apply readable_nonidentity in x1.
  apply x1.
apply identity_unit_equiv.
apply RJ.
Qed.

Lemma address_mapsto_overlap':
  forall sh ch1 v1 ch2 v2 a1 a2,
     adr_range a1 (size_chunk ch1) a2 ->
     address_mapsto ch1 v1 sh a1 * address_mapsto ch2 v2 sh a2 |-- FF.
Proof.
  intros.
  eapply derives_trans; [eapply sepcon_derives | apply VALspec_range_overlap'].
  +
 apply address_mapsto_VALspec_range.
  +
 apply address_mapsto_VALspec_range.
  +
 auto.
  +
 apply size_chunk_pos.
Qed.

Lemma VALspec_range_overlap: forall sh l1 n1 l2 n2,
  range_overlap l1 n1 l2 n2 ->
  VALspec_range n1 sh l1 * VALspec_range n2 sh l2 |-- FF.
Proof.
  intros.
  pose proof range_overlap_non_zero _ _ _ _ H.
  apply range_overlap_spec in H; try tauto.
  destruct H.
  +
 apply VALspec_range_overlap'; tauto.
  +
 rewrite sepcon_comm.
    apply VALspec_range_overlap'; tauto.
Qed.

Lemma address_mapsto_overlap: forall sh l1 ch1 v1 l2 ch2 v2,
  range_overlap l1 (size_chunk ch1) l2 (size_chunk ch2) ->
  address_mapsto ch1 v1 sh l1 * address_mapsto ch2 v2 sh l2 |-- FF.
Proof.
  intros.
  apply range_overlap_spec in H; try apply size_chunk_pos.
  destruct H.
  +
 apply address_mapsto_overlap'; auto.
  +
 rewrite sepcon_comm.
    apply address_mapsto_overlap'; auto.
Qed.

Lemma share_joins_self: forall sh: share, joins sh sh -> nonunit sh -> False.
  intros.
  destruct H as [sh' ?].
  apply nonunit_nonidentity in H0; contradiction H0.
  eapply join_self; eauto.
Qed.

Lemma nonlock_permission_bytes_overlap:
  forall sh n1 n2 p1 p2,
  nonunit sh ->
  range_overlap p1 n1 p2 n2 ->
  nonlock_permission_bytes sh p1 n1 * nonlock_permission_bytes sh p2 n2 |-- FF.
Proof.
  intros.
  eapply derives_trans; [apply sepcon_derives; apply derives_refl|].
  apply allp_jam_overlap.
  +
 eexists.
apply is_resource_pred_nonlock_shareat.
  +
 eexists.
apply is_resource_pred_nonlock_shareat.
  +
 unfold shareat; simpl; intros.
    destruct H3 as [w ?].
    apply (resource_at_join _ _ _ l) in H3.
    pose proof resource_share_joins (w1 @ l) (w2 @ l) sh sh.
    do 2 (spec H4; [tauto |]).
    spec H4; [firstorder |].
    apply (share_joins_self sh); auto.
  +
 auto.
Qed.

Lemma address_mapsto_value_cohere':
  forall ch v1 v2 sh1 sh2 a r
 (Hmaps1 : address_mapsto ch v1 sh1 a r)
 (Hmaps2 : address_mapsto ch v2 sh2 a r), v1=v2.
 intros.
 destruct Hmaps1 as [b1 [[Hlen1 [? ?]] Hall1]].
 destruct Hmaps2 as [b2 [[Hlen2 [? ?]] Hall2]].
 assert (b1 = b2); [ | subst; auto].
 clear - Hlen1 Hlen2 Hall1 Hall2.
 rewrite size_chunk_conv in *.
 forget (size_chunk_nat ch) as n.
clear ch.
 assert (forall i, nth_error b1 i = nth_error b2 i).
 intro.
 destruct a as [b z].
 specialize (Hall1 (b, (z+Z.of_nat i))).
 specialize (Hall2 (b, (z+Z.of_nat i))).
 hnf in Hall1,Hall2.
if_tac in Hall1.
destruct H as [_ [_ ?]].
 destruct Hall1 as (? & Hall1), Hall2 as (? & Hall2).
simpl in Hall1, Hall2.
 rewrite Hall1 in Hall2; inversion Hall2.
 replace (z + Z.of_nat i - z) with (Z.of_nat i) in H2 by lia.
 rewrite Nat2Z.id in H2.
 rewrite coqlib4.nth_error_nth with (z:=Undef) by lia.
 rewrite coqlib4.nth_error_nth with (z:=Undef) by lia.
 f_equal; auto.
 assert (~(i<n)%nat).
 contradict H.
split; auto.
lia.
 transitivity (@None memval); [ | symmetry];
 apply nth_error_length; lia.
 clear - H Hlen1 Hlen2.
 revert b1 b2 Hlen1 Hlen2 H.
 induction n; destruct b1,b2; intros; auto; inv Hlen1; inv Hlen2.
 f_equal.
 specialize (H O).
simpl in H.
inv H; auto.
 apply IHn; auto.
 intro i; specialize (H (S i)); apply H.
Qed.

Lemma address_mapsto_value_cohere:
  forall ch v1 v2 sh1 sh2 a,
 address_mapsto ch v1 sh1 a * address_mapsto ch v2 sh2 a |-- !! (v1=v2).
Proof.
 intros.
 intros w [w1 [w2 [? [? ?]]]].
hnf.
 destruct H0 as [b1 [[? [? ?]] ?]].
 destruct H1 as [b2 [[? [? ?]] ?]].
 assert (b1 = b2); [ | subst; auto].
 clear - H H0 H4 H1 H7.
 rewrite size_chunk_conv in *.
 forget (size_chunk_nat ch) as n.
clear ch.
 assert (forall i, nth_error b1 i = nth_error b2 i).
 intro.
 destruct a as [b z].
 specialize (H4 (b, (z+Z.of_nat i))).
 specialize (H7 (b, (z+Z.of_nat i))).
 hnf in H4,H7.
if_tac in H4.
destruct H2 as [_ [_ ?]].
 destruct H4, H7.
hnf in H3,H4.
 apply (resource_at_join _ _ _ (b, z + Z.of_nat i)) in H.
 rewrite H3,H4 in H.
inv  H.
 clear - H2 H10 H1.
 replace (z + Z.of_nat i - z) with (Z.of_nat i) in H10 by lia.
 rewrite Nat2Z.id in H10.
 rewrite coqlib4.nth_error_nth with (z:=Undef) by lia.
 rewrite coqlib4.nth_error_nth with (z:=Undef) by lia.
 f_equal; auto.
 assert (~(i<n)%nat).
 contradict H2.
split; auto.
lia.
 transitivity (@None memval); [ | symmetry];
 apply nth_error_length; lia.
 clear - H2 H0 H1.
 revert b1 b2 H0 H1 H2.
 induction n; destruct b1,b2; intros; auto; inv H0; inv H1.
 f_equal.
 specialize (H2 O).
simpl in H2.
inv H2; auto.
 apply IHn; auto.
 intro i; specialize (H2 (S i)); apply H2.
Qed.

Definition almost_empty rm: Prop:=
  forall loc sh psh k P, rm @ loc = YES sh psh k P -> forall val, ~ k = VAL val.

Definition no_locks phi :=
  forall addr sh sh' z z' P,
phi @ addr <> YES sh sh' (LK z z') P.

End res_predicates.
Module Export own.
Import VST.msl.ghost.
Import VST.msl.ghost_seplog.
Local Open Scope pred.

Notation ghost_approx m := (ghost_fmap (approx (level m)) (approx (level m))).

Program Definition ghost_is g: pred rmap :=
  fun m => join_sub (ghost_approx m g) (ghost_of m).
Next Obligation.
  split; intros ??? J.
  -
 rewrite (age1_ghost_of _ _ H).
    destruct J as [? J].
    eapply ghost_fmap_join in J.
    assert (level a >= level a')%nat as Hl by (apply age_level in H; lia).
    erewrite ghost_fmap_fmap, approx_oo_approx', approx'_oo_approx in J by apply Hl.
    eexists; eauto.
  -
 apply rmap_order in H as (? & _ & J').
    eapply join_sub_trans; eauto.
    rewrite <- H; auto.
Qed.

Definition Own g: pred rmap := allp noat && ghost_is g.

Lemma Own_op: forall a b c, join a b c -> Own c = Own a * Own b.
  intros; apply pred_ext.
  -
 intros w (Hno & [? J]).
    eapply ghost_fmap_join in H.
    destruct (join_assoc H J) as (b' & J1 & J2).
    eapply ghost_fmap_join in J1; rewrite ghost_fmap_fmap, 2approx_oo_approx in J1.
    eapply ghost_fmap_join in J2; rewrite ghost_fmap_fmap, 2approx_oo_approx, ghost_of_approx in J2.
    destruct (make_rmap (resource_at w) (ghost_approx w a) (level w))
      as (wa & Hla & Hra & Hga).
    {
 extensionality; apply resource_at_approx.
}
    {
 rewrite ghost_fmap_fmap, approx_oo_approx; auto.
}
    destruct (make_rmap (resource_at w) (ghost_approx w b') (level w))
      as (wb & Hlb & Hrb & Hgb).
    {
 extensionality; apply resource_at_approx.
}
    {
 rewrite ghost_fmap_fmap, approx_oo_approx; auto.
}
    exists wa, wb; split.
    +
 apply resource_at_join2; auto.
      *
 intro; rewrite Hra, Hrb.
        apply identity_unit', Hno.
      *
 rewrite Hga, Hgb; auto.
    +
 simpl; rewrite Hla, Hlb, Hra, Hrb, Hga, Hgb; simpl.
      repeat split; auto.
      *
 apply join_sub_refl.
      *
 eexists; eauto.
  -
 intros w (w1 & w2 & J & (Hnoa & Hga) & (Hnob & Hgb)).
    split.
    +
 intro l; apply (resource_at_join _ _ _ l) in J.
      simpl in *; rewrite <- (Hnoa _ _ _ J); auto.
    +
 destruct (join_level _ _ _ J) as [Hl1 Hl2].
      apply ghost_of_join in J.
      destruct Hga as [? Ja], Hgb as [? Jb].
      destruct (join_assoc (join_comm Ja) J) as (? & Ja' & J').
      destruct (join_assoc (join_comm Jb) (join_comm Ja')) as (? & Jc & J'').
      rewrite Hl1, Hl2 in Jc.
      eapply ghost_fmap_join, join_eq in H; [|apply join_comm, Jc]; subst.
      destruct (join_assoc (join_comm J'') (join_comm J')) as (? & ? & ?).
      eexists; eauto.
Qed.

Fixpoint make_join (a c : ghost) : ghost :=
  match a, c with
  | nil, _ => c
  | _, nil => nil
  | None :: a', x :: c' => x :: make_join a' c'
  | _ :: a', None :: c' => None :: make_join a' c'
  | Some (ga, pa) :: a', Some (gc, _) :: c' => Some (gc, pa) :: make_join a' c'
  end.

Lemma make_join_nil : forall a, make_join a nil = nil.
  destruct a; auto.
  destruct o as [[]|]; auto.
Qed.

Lemma make_join_nil_cons : forall o a c, make_join (o :: a) (None :: c) = None :: make_join a c.
  destruct o as [[]|]; auto.
Qed.

Lemma ghost_joins_approx: forall n a c,
  joins (ghost_fmap (approx n) (approx n) a) (ghost_fmap (approx n) (approx n) c) ->
  let c' := make_join a c in
  joins (ghost_fmap (approx (S n)) (approx (S n)) a) (ghost_fmap (approx (S n)) (approx (S n)) c') /\
    forall b, joins b (ghost_fmap (approx (S n)) (approx (S n)) c') ->
      joins (ghost_fmap (approx n) (approx n) b) (ghost_fmap (approx n) (approx n) c).
  intros ???; revert a; induction c; intros; subst c'; simpl.
  -
 rewrite make_join_nil; split.
    +
 eexists; constructor.
    +
 eexists; constructor.
  -
 destruct H; inv H.
    +
 destruct a0; inv H1.
      split.
      {
 eexists; constructor.
}
      intros ? []; eexists.
      apply ghost_fmap_join with (f := approx n)(g := approx n) in H.
      rewrite ghost_fmap_fmap, approx_oo_approx', approx'_oo_approx in H by auto; eauto.
    +
 destruct a0; inv H0.
      destruct (IHc a0) as (H & Hc'); eauto.
      inv H3.
      *
 destruct o; inv H1.
        split.
        {
 destruct H; eexists; constructor; eauto; constructor.
}
        intros ? [? J]; inv J; [eexists; constructor|].
        destruct (Hc' m1); eauto.
        eexists; constructor; eauto.
        instantiate (1 := option_map (fun '(a, b) => (a, preds_fmap (approx n) (approx n) b)) a3).
        inv H3.
        --
 destruct a as [[]|]; [simpl | constructor].
           rewrite preds_fmap_fmap, approx_oo_approx', approx'_oo_approx by auto; constructor; auto.
        --
 destruct a; inv H4; constructor.
        --
 destruct a as [[]|]; inv H1; constructor.
           destruct a2, a5; inv H4; constructor; auto; simpl in *.
           inv H2.
           rewrite preds_fmap_fmap, approx_oo_approx', approx'_oo_approx by auto; constructor; auto.
      *
 destruct a; inv H2.
        rewrite make_join_nil_cons.
        split.
        {
 destruct H; eexists; constructor; eauto; constructor.
}
        intros ? [? J]; inv J; [eexists; constructor|].
        destruct (Hc' m1); eauto.
        eexists; constructor; eauto; constructor.
      *
 destruct o as [[]|], a as [[]|]; inv H0; inv H1.
        split.
        {
 destruct H.
          destruct a4; inv H2; simpl in *.
          inv H1.
          eexists (Some (_, _) :: _); constructor; eauto; constructor.
          constructor; simpl; eauto; constructor; eauto.
}
        intros ? [? J]; inv J; [eexists; constructor|].
        destruct (Hc' m1); eauto.
        eexists; constructor; eauto.
        instantiate (1 := option_map (fun '(a, b) => (a, preds_fmap (approx n) (approx n) b)) a3).
        inv H4.
        --
 destruct a4; inv H2; simpl in *.
           inv H3.
           rewrite <- H2, preds_fmap_fmap, approx_oo_approx', approx'_oo_approx by auto; constructor.
        --
 constructor.
           destruct a2, a4, a6; inv H2; inv H6; constructor; auto; simpl in *.
           inv H3; inv H4.
           rewrite <- H6, preds_fmap_fmap, approx_oo_approx', approx'_oo_approx by auto; constructor; auto.
Qed.

Program Definition bupd (P: pred rmap): pred rmap :=
  fun m => forall c, joins (ghost_of m) (ghost_approx m c) ->
    exists b, joins b (ghost_approx m c) /\
    exists m', level m' = level m /\ resource_at m' = resource_at m /\ ghost_of m' = b /\ P m'.
Next Obligation.
  split; repeat intro.
  rewrite (age1_ghost_of _ _ H) in H1.
  rewrite <- ghost_of_approx in H0.
  destruct (ghost_joins_approx _ _ _ H1) as (J0 & Hc0).
  rewrite <- (age_level _ _ H) in *.
  specialize (H0 _ J0); destruct H0 as (b & J & Hrb).
  pose proof (age_level _ _ H).
  exists (ghost_approx a' b); split; auto.
  destruct Hrb as (m' & Hl' & Hr' & Hg' & HP).
  destruct (levelS_age m' (level a')) as (m'' & Hage' & Hl'').
  {
 congruence.
}
  exists m''; repeat split; auto.
  +
 extensionality l.
    erewrite (age1_resource_at _ _ H l) by (symmetry; apply resource_at_approx).
    erewrite (age1_resource_at _ _ Hage' l) by (symmetry; apply resource_at_approx).
    congruence.
  +
 rewrite (age1_ghost_of _ _ Hage').
    rewrite Hg', <- Hl''; auto.
  +
 eapply pred_hereditary; eauto.
  +
 apply rmap_order in H as (Hl & Hr & [? J]).
    destruct H1 as [d J'].
    destruct (join_assoc J J') as (c' & ? & Jc').
    eapply ghost_fmap_join in Jc'; rewrite ghost_of_approx in Jc'.
    destruct (H0 c') as (? & Jm' & m' & ? & ? & ? & ?); eauto; subst.
    do 2 eexists; [|exists m'; repeat split; eauto; congruence].
    eapply join_sub_joins'; eauto.
    {
 apply join_sub_refl.
}
    eapply ghost_fmap_join in H; rewrite ghost_fmap_fmap, 2approx_oo_approx in H.
    rewrite Hl; eexists; eauto.
Qed.

Lemma bupd_intro: forall P, P |-- bupd P.
Proof.
  repeat intro; eauto 7.
Qed.

Lemma bupd_mono: forall P Q, (P |-- Q) -> bupd P |-- bupd Q.
Proof.
  repeat intro.
  simpl in *.
  destruct (H0 _ H1) as (b & ? & m' & ? & ? & ? & ?).
  exists b; split; auto.
  exists m'; repeat split; auto.
Qed.

Lemma bupd_frame_r: forall P Q, bupd P * Q |-- bupd (P * Q).
Proof.
  repeat intro.
  destruct H as (w1 & w2 & J & HP & HQ).
  destruct (join_level _ _ _ J) as [Hl1 Hl2].
  pose proof (ghost_of_join _ _ _ J) as Jg.
  destruct H0 as [? J'].
  destruct (join_assoc Jg J') as (c' & J1 & J2).
  erewrite <- (ghost_same_level_gen (level a) (ghost_of w2) c c') in J2, J1
    by (rewrite <- Hl2 at 1 2; rewrite ghost_of_approx; auto).
  destruct (HP c') as (? & [? J1'] & w1' & ? & Hr' & ? & HP'); subst.
  {
 rewrite Hl1; eauto.
}
  rewrite Hl1 in J1'; destruct (join_assoc (join_comm J1) (join_comm J1')) as (w' & ? & ?).
  exists w'; split; [eexists; apply join_comm; eauto|].
  destruct (make_rmap (resource_at a) w' (level a)) as (m' & ? & Hr'' & ?); subst.
  {
 extensionality l; apply resource_at_approx.
}
  {
 eapply ghost_same_level_gen.
    rewrite <- (ghost_of_approx w2), <- (ghost_of_approx w1'), H, Hl1, Hl2 in H0.
    apply join_comm; eauto.
}
  exists m'; repeat split; auto.
  exists w1', w2; repeat split; auto.
  apply resource_at_join2; auto; try lia.
  intro; rewrite Hr', Hr''.
  apply resource_at_join; auto.
Qed.

Lemma bupd_frame_l: forall P Q, P * bupd Q |-- bupd (P * Q).
Proof.
  intros; rewrite sepcon_comm, (sepcon_comm P Q); apply bupd_frame_r.
Qed.

Lemma bupd_trans: forall P, bupd (bupd P) |-- bupd P.
Proof.
  repeat intro.
  destruct (H _ H0) as (b & J & a' & Hl & Hr & ? & Ha'); subst.
  rewrite <- Hl in J; destruct (Ha' _ J) as (b' & ? & Hm').
  rewrite <- Hl, <- Hr; eauto.
Qed.

Lemma joins_approx_core : forall a, joins (ghost_of a) (ghost_approx a (core (ghost_of a))).
  intros; eexists.
  rewrite <- ghost_of_approx at 1; apply ghost_fmap_join.
  apply join_comm, core_unit.
Qed.

Lemma bupd_prop : forall P, bupd (!! P) = !! P.
Proof.
  intros ?; apply pred_ext.
  -
 intros ??; simpl in *.
    destruct (H _ (joins_approx_core _)) as (? & ? & ? & ? & ? & ? & ?); auto.
  -
 intros ??.
    do 2 eexists; eauto.
Qed.

Lemma bupd_andp_prop : forall P Q, bupd (!! P && Q) = !! P && bupd Q.
Proof.
  intros; apply pred_ext.
  -
 intros ??; simpl in *.
    split.
    +
 destruct (H _ (joins_approx_core _)) as (? & ? & ? & ? & ? & ? & ? & ?); auto.
    +
 intros ? J; destruct (H _ J) as (? & ? & m & ? & ? & ? & ? & ?).
      do 2 eexists; eauto.
  -
 intros ? [? HQ] ? J.
    destruct (HQ _ J) as (? & ? & m & ? & ? & ? & ?).
    do 2 eexists; eauto.
    do 2 eexists; eauto.
    repeat split; auto.
Qed.

Lemma subp_bupd: forall (G : pred nat) (P P' : pred rmap), (G |-- P >=> P') ->
    G |-- (bupd P >=> bupd P')%pred.
Proof.
  repeat intro.
  specialize (H4 _ H5) as (? & ? & ? & ? & ? & ? & HP).
  do 2 eexists; eauto; do 2 eexists; eauto; repeat (split; auto).
  eapply H; try apply ext_refl; try apply necR_refl; eauto.
  apply necR_level in H2; apply ext_level in H3; lia.
Qed.

Lemma eqp_bupd: forall (G : pred nat) (P P' : pred rmap), (G |-- P <=> P') ->
    G |-- (bupd P <=> bupd P').
Proof.
  intros.
  rewrite fash_and in *.
  apply andp_right; apply subp_bupd; eapply derives_trans; try apply H;
    [apply andp_left1 | apply andp_left2]; apply derives_refl.
Qed.

Definition ghost_fp_update_ND a B :=
  forall n c, joins (ghost_fmap (approx n) (approx n) a) c ->
    exists b, B b /\ joins (ghost_fmap (approx n) (approx n) b) c.

Lemma Own_update_ND: forall a B, ghost_fp_update_ND a B ->
  Own a |-- bupd (EX b : _, !!(B b) && Own b).
Proof.
  unfold ghost_fp_update_ND; repeat intro.
  destruct H0 as (Hno & J).
  eapply join_sub_joins_trans in H1; eauto; [|apply J].
  apply H in H1 as (g' & ? & J').
  exists (ghost_fmap (approx (level a0)) (approx (level a0)) g'); split; auto.
  destruct (make_rmap (resource_at a0)
    (ghost_fmap (approx (level a0)) (approx (level a0)) g') (level a0))
    as (m' & Hl & Hr & Hg').
  {
 extensionality; apply resource_at_approx.
}
  {
 rewrite ghost_fmap_fmap, approx_oo_approx; auto.
}
  exists m'; repeat split; auto.
  exists g'; repeat split; auto.
  -
 simpl in *; intro; rewrite Hr; auto.
  -
 simpl; rewrite Hg', Hl; simpl; eauto.
    apply join_sub_refl.
Qed.

Definition ghost_fp_update (a b : ghost) :=
  forall n c, joins (ghost_fmap (approx n) (approx n) a) c ->
               joins (ghost_fmap (approx n) (approx n) b) c.

#[export] Instance ghost_fp_update_preorder: RelationClasses.PreOrder ghost_fp_update.
  split; repeat intro; auto.
Qed.

Lemma ghost_fp_update_approx: forall a b n, ghost_fp_update a b ->
  ghost_fp_update (ghost_fmap (approx n) (approx n) a) (ghost_fmap (approx n) (approx n) b).
  intros; intros m c J.
  rewrite ghost_fmap_fmap in *.
  replace (approx m oo approx n) with (approx (min m n)) in *.
  replace (approx n oo approx m) with (approx (min m n)) in *.
  auto.
  {
 destruct (Min.min_spec m n) as [[? ->] | [? ->]];
      [rewrite approx'_oo_approx | rewrite approx_oo_approx']; auto; lia.
}
  {
 destruct (Min.min_spec m n) as [[? ->] | [? ->]];
      [rewrite approx_oo_approx' | rewrite approx'_oo_approx]; auto; lia.
}
Qed.

Lemma Own_update: forall a b, ghost_fp_update a b ->
  Own a |-- bupd (Own b).
Proof.
  intros; eapply derives_trans.
  -
 eapply (Own_update_ND _ (eq _)).
    repeat intro.
    eexists; split; [constructor|].
    apply H; eauto.
  -
 apply bupd_mono.
    repeat (apply exp_left; intro).
    apply prop_andp_left; intro X; inv X; auto.
Qed.

Lemma Own_unit: emp |-- EX a : _, !!(identity a) && Own a.
Proof.
  intros w Hemp.
  assert (forall l, identity (w @ l)).
  {
 rewrite emp_no in Hemp; auto.
}
  destruct Hemp as (e & ? & Hext).
  exists (ghost_of e); split; [|split; auto].
  -
 apply ghost_of_identity; auto.
  -
 apply rmap_order in Hext as (? & ? & []).
    eexists.
    rewrite <- (ghost_of_approx w).
    apply ghost_fmap_join; eauto.
Qed.

Lemma Own_dealloc: forall a, Own a |-- emp.
Proof.
  rewrite emp_no.
  intros; apply andp_left1; auto.
Qed.

Definition singleton {A} k (x : A) : list (option A) := repeat None k ++ Some x :: nil.

Definition gname := nat.

Definition own {RA: Ghost} (n: gname) (a: G) (pp: preds) :=
  EX v : _, Own (singleton n (existT _ RA (exist _ a v), pp)).

Definition list_set {A} (m : list (option A)) k v : list (option A) :=
  firstn k m ++ repeat None (k - length m) ++ Some v :: skipn (S k) m.

Lemma singleton_join_gen: forall k a c (m: ghost)
  (Hjoin: join (Some a) (nth k m None) (Some c)),
  join (singleton k a) m (list_set m k c).
  induction k; intros.
  -
 destruct m; simpl in *; subst; inv Hjoin; constructor; constructor; auto.
  -
 destruct m; simpl in *.
    +
 inv Hjoin; constructor.
    +
 constructor; [constructor | apply IHk; auto].
Qed.

Lemma map_repeat : forall {A B} (f : A -> B) x n, map f (repeat x n) = repeat (f x) n.
  induction n; auto; simpl.
  rewrite IHn; auto.
Qed.

Lemma ghost_fmap_singleton: forall f g k v, ghost_fmap f g (singleton k v) =
  singleton k (match v with (a, b) => (a, preds_fmap f g b) end).
  intros; unfold ghost_fmap, singleton.
  rewrite map_app, map_repeat; auto.
Qed.

Lemma ghost_fmap_singleton_inv : forall f g a k v,
  ghost_fmap f g a = singleton k v ->
  exists v', a = singleton k v' /\ v = let (a, b) := v' in (a, preds_fmap f g b).
  unfold singleton; induction a; simpl; intros.
  -
 destruct k; discriminate.
  -
 destruct a as [[]|]; simpl in *.
    +
 destruct k; inv H.
      destruct a0; inv H2.
      simpl; eauto.
    +
 destruct k; inv H.
      edestruct IHa as (? & ? & ?); eauto; subst.
      simpl; eauto.
Qed.

Import ListNotations.
Fixpoint uptoN (n : nat) : list nat :=
  match n with
  | O => []
  | S n' => uptoN n' ++ [n']
  end.

Lemma In_uptoN : forall m n, (m < n)%nat -> In m (uptoN n).
  induction n; intros; [lia | simpl].
  rewrite in_app; destruct (lt_dec m n); auto.
  right; simpl; lia.
Qed.

Lemma ghost_alloc_strong: forall {RA: Ghost} P a pp, pred_infinite P -> ghost.valid a ->
  emp |-- bupd (EX g, !!(P g) && own g a pp).
Proof.
  intros.
  eapply derives_trans; [apply Own_unit|].
  apply exp_left; intro g0.
  apply prop_andp_left; intro Hg0.
  eapply derives_trans.
  -
 apply Own_update_ND with (B := fun b => exists g, P g /\ b = singleton g (existT _ RA (exist _ _ H0), pp)).
    intros ? c [? J].
    destruct (H (uptoN (length c))) as (g & ? & ?).
    exists (singleton g (existT _ RA (exist _ _ H0), pp)).
    split; eauto.
    apply ghost_identity in Hg0; subst.
    assert (x = c) by (inv J; auto); subst.
    rewrite ghost_fmap_singleton; eexists; apply singleton_join_gen.
    rewrite nth_overflow; [constructor|].
    destruct (lt_dec g (length c)); [|lia].
    apply In_uptoN in l; contradiction.
  -
 apply bupd_mono, exp_left; intro g'.
    apply prop_andp_left; intros (g & ? & ?); subst.
    apply exp_right with g.
    apply prop_andp_right; auto.
    eapply exp_right; eauto.
Qed.

Lemma list_max : forall x (l : list nat), In x l -> (x <= fold_right max O l)%nat.
  induction l; [contradiction | simpl; intros].
  destruct H.
  -
 subst.
    apply Nat.le_max_l.
  -
 etransitivity; [apply IHl; auto|].
    apply Nat.le_max_r.
Qed.

Lemma fresh_nat: forall (l : list nat), exists n, ~In n l.
  intros; exists (S (fold_right max O l)).
  intros X%list_max; lia.
Qed.

Lemma ghost_alloc: forall {RA: Ghost} a pp, ghost.valid a ->
  emp |-- bupd (EX g, own g a pp).
Proof.
  intros.
  eapply derives_trans; [apply (ghost_alloc_strong (fun _ => True)); eauto|].
  {
 intros ?.
    destruct (fresh_nat l); eauto.
}
  apply bupd_mono.
  apply exp_left; intros g.
  apply exp_right with g.
  apply andp_left2; auto.
Qed.

Lemma singleton_join: forall a b c k,
  join (singleton k a) (singleton k b) (singleton k c) <-> join a b c.
  unfold singleton; induction k; simpl.
  -
 split.
    +
 inversion 1; subst.
      inv H3; auto.
    +
 intro; do 2 constructor; auto.
  -
 rewrite <- IHk.
    split; [inversion 1 | repeat constructor]; auto.
Qed.

Lemma singleton_join_inv: forall k a b c,
  join (singleton k a) (singleton k b) c -> exists c', join a b c' /\ c = singleton k c'.
  unfold singleton; induction k; inversion 1; subst.
  -
 assert (m3 = nil) by (inv H6; auto).
    inv H5; eauto.
  -
 assert (a3 = None) by (inv H5; auto); subst.
    edestruct IHk as (? & ? & ?); eauto; subst; eauto.
Qed.

Lemma ghost_valid_2: forall {RA: Ghost} g a1 a2 pp,
  own g a1 pp * own g a2 pp |-- !!ghost.valid_2 a1 a2.
Proof.
  intros.
  intros w (? & ? & J%ghost_of_join & (? & ? & [? J1]) & (? & ? & [? J2])).
  destruct (join_assoc (join_comm J1) J) as (? & J1' & ?).
  destruct (join_assoc (join_comm J2) (join_comm J1')) as (? & J' & ?).
  rewrite !ghost_fmap_singleton in J'.
  apply singleton_join_inv in J' as ([] & J' & ?).
  inv J'; simpl in *.
  inv H4; repeat inj_pair_tac.
  eexists; eauto.
Qed.

Lemma ghost_op: forall {RA: Ghost} g (a1 a2 a3: G) pp, join a1 a2 a3 ->
  own g a3 pp = own g a1 pp * own g a2 pp.
  intros; apply pred_ext.
  -
 apply exp_left; intro.
    erewrite Own_op; [apply sepcon_derives; eapply exp_right; eauto|].
    instantiate (1 := join_valid _ _ _ (join_comm H) x).
    instantiate (1 := join_valid _ _ _ H x).
    apply singleton_join; constructor; constructor; auto.
  -
 eapply derives_trans; [apply andp_right, derives_refl; apply ghost_valid_2|].
    apply prop_andp_left; intros (? & J & ?).
    eapply join_eq in H; eauto; subst.
    unfold own; rewrite exp_sepcon1; apply exp_left; intro.
    rewrite exp_sepcon2; apply exp_left; intro.
    erewrite <- Own_op; [eapply exp_right; eauto|].
    instantiate (1 := H0).
    apply singleton_join; constructor; constructor; auto.
Qed.

Lemma ghost_valid: forall {RA: Ghost} g a pp,
  own g a pp |-- !!ghost.valid a.
Proof.
  intros.
  rewrite <- (normalize.andp_TT (!!_)).
  erewrite ghost_op by apply core_unit.
  eapply derives_trans; [apply andp_right, derives_refl; apply ghost_valid_2|].
  apply prop_andp_left; intros (? & J & ?); apply prop_andp_right; auto.
  assert (x = a) as <-; auto.
  eapply join_eq, core_unit; assumption.
Qed.

Lemma singleton_join_inv_gen: forall k a (b c: ghost),
  join (singleton k a) b c ->
  join (Some a) (nth k b None) (nth k c None) /\
    exists c', nth k c None = Some c' /\ c = list_set b k c'.
  unfold singleton; induction k; inversion 1; subst; auto.
  -
 split; simpl; eauto; constructor.
  -
 split; auto.
    unfold list_set; simpl.
    assert (m2 = m3) by (inv H5; auto).
    inv H2; eauto.
  -
 rewrite app_nth2; rewrite repeat_length; auto.
    rewrite minus_diag; split; [constructor | simpl; eauto].
  -
 assert (a2 = a3) by (inv H2; auto).
    destruct (IHk _ _ _ H5) as (? & ? & ? & ?); subst; eauto.
Qed.

Lemma ghost_update_ND: forall {RA: Ghost} g (a: G) B pp,
  fp_update_ND a B -> own g a pp |-- bupd (EX b : _, !!(B b) && own g b pp).
Proof.
  intros.
  apply exp_left; intro Hva.
  eapply derives_trans.
  -
 apply Own_update_ND with
      (B := fun b => exists b' Hvb, B b' /\ b = singleton g (existT _ RA (exist _ b' Hvb), pp)).
    intros ?? [? J].
    rewrite ghost_fmap_singleton in J.
    destruct (singleton_join_inv_gen _ _ _ _ J) as [Jg _].
    inv Jg.
    +
 destruct (H (core a)) as (b & ? & Hv).
      {
 eexists; split; [apply join_comm, core_unit | auto].
}
      assert (ghost.valid b) as Hvb.
      {
 destruct Hv as (? & ? & ?); eapply join_valid; eauto.
}
      exists (singleton g (existT _ RA (exist _ _ Hvb), pp)); split; eauto.
      rewrite ghost_fmap_singleton.
      eexists; apply singleton_join_gen.
      rewrite <- H2; constructor.
    +
 destruct a2, a3; inv H3; simpl in *.
      inv H0; inj_pair_tac.
      destruct (H b0) as (b & ? & Hv).
      {
 eexists; eauto.
}
      destruct Hv as (? & ? & ?).
      assert (ghost.valid b) as Hvb by (eapply join_valid; eauto).
      exists (singleton g (existT _ RA (exist _ _ Hvb), pp)); split; eauto.
      rewrite ghost_fmap_singleton.
      eexists; apply singleton_join_gen.
      instantiate (1 := (_, _)).
      rewrite <- H1; constructor; constructor; [constructor|]; eauto.
      Unshelve.
auto.
  -
 apply bupd_mono, exp_left; intro.
    apply prop_andp_left; intros (b & ? & ? & ?); subst.
    apply exp_right with b, prop_andp_right; auto.
    eapply exp_right; auto.
Qed.

Lemma ghost_update: forall {RA: Ghost} g (a b: G) pp,
  fp_update a b -> own g a pp |-- bupd (own g b pp).
Proof.
  intros; eapply derives_trans.
  -
 apply (ghost_update_ND g a (eq b)).
    intros ? J; destruct (H _ J).
    do 2 eexists; [constructor | eauto].
  -
 apply bupd_mono.
    apply exp_left; intro; apply prop_andp_left; intro X; inv X; auto.
Qed.

Lemma ghost_dealloc: forall {RA: Ghost} g a pp,
  own g a pp |-- emp.
Proof.
  intros; unfold own.
  apply exp_left; intro; apply Own_dealloc.
Qed.

Lemma list_set_same : forall {A} n l (a : A), nth n l None = Some a ->
  list_set l n a = l.
  unfold list_set; induction n; destruct l; simpl; try discriminate; intros; subst; auto.
  f_equal; eauto.
Qed.

Lemma map_firstn : forall {A B} (f : A -> B) (l : list A) n,
  map f (firstn n l) = firstn n (map f l).
  induction l; destruct n; auto; simpl.
  rewrite IHl; auto.
Qed.

Lemma map_skipn : forall {A B} (f : A -> B) (l : list A) n,
  map f (skipn n l) = skipn n (map f l).
  induction l; destruct n; auto; simpl.
  rewrite IHl; auto.
Qed.

Lemma list_set_set : forall {A} n l (a b : A), (n <= length l)%nat ->
  list_set (list_set l n a) n b = list_set l n b.
  intros; unfold list_set.
  rewrite (proj2 (Nat.sub_0_le _ _) H).
  rewrite !app_length, !skipn_app, firstn_app, firstn_length, min_l, minus_diag, app_nil_r, repeat_length by auto.
  rewrite firstn_firstn, min_l by auto; f_equal.
  unfold length; setoid_rewrite skipn_length; f_equal.
  -
 f_equal.
lia.
  -
 rewrite skipn_all2, skipn_nil, Nat.sub_0_r; [|rewrite firstn_length; lia].
    rewrite (Nat.add_sub 1); auto.
Qed.

Lemma nth_list_set : forall {A} n l (a : A) d, nth n (list_set l n a) d = Some a.
  intros; unfold list_set.
  rewrite 2app_nth2; rewrite ?repeat_length, ?firstn_length; try lia.
  match goal with |- nth ?n _ _ = _ => replace n with O by lia end; auto.
Qed.

Lemma own_core : forall {RA: Ghost} g (a : G) pp,
  a = core a -> forall w, own g a pp w -> own g a pp (core w).
  unfold own, Own, ghost_is; intros; simpl in *.
  destruct H0 as (Hv & _ & ? & J).
  exists Hv; split; auto.
  -
 intros ?; apply resource_at_core_identity.
  -
 rewrite ghost_of_core.
    rewrite ghost_fmap_singleton in J.
    apply singleton_join_inv_gen in J as (J & ((?, (?, ?)), ?) & Hg & Hw).
    rewrite Hg in J.
    rewrite Hw, ghost_core_eq.
    unfold list_set; rewrite !map_app, map_firstn, map_repeat.
    unfold map at 2; setoid_rewrite map_skipn.
    rewrite ghost_fmap_singleton; simpl Datatypes.option_map.
    erewrite <- map_length.
    rewrite level_core.
    inv J.
    +
 inj_pair_tac.
      eexists; apply singleton_join_gen.
      setoid_rewrite (map_nth _ _ None).
rewrite <- H2.
      match goal with |- join ?a _ ?c => assert (a = c) as ->; [|constructor] end.
      do 3 f_equal.
apply exist_ext; auto.
    +
 destruct a2, H3 as [J ?].
      inv J.
      repeat inj_pair_tac.
      apply join_core_sub in H5 as [].
      setoid_rewrite <- list_set_set.
      eexists; apply singleton_join_gen.
      rewrite nth_list_set.
      instantiate (1 := (_, _)).
      constructor.
split; simpl in *; [|split; auto].
      constructor.
rewrite H; eauto.
      Unshelve.
 inv H0; auto.
      *
 rewrite map_length.
        destruct (le_dec (length x) g); [|lia].
        rewrite nth_overflow in H1 by auto; discriminate.
      *
 apply join_comm, join_valid in H2; auto.
        apply core_valid; auto.
Qed.

End own.
Export VST.msl.ghost.
Import VST.msl.iter_sepcon.
Import VST.veric.shares.
Import VST.veric.compcert_rmaps.

Notation "|==> P" := (own.bupd P) (at level 99, P at level 200): pred.

Section ghost.

Local Open Scope pred.

Context {RA: Ghost}.

Lemma own_op' : forall g a1 a2 pp,
  own g a1 pp * own g a2 pp = EX a3 : _, !!(join a1 a2 a3 /\ valid a3) && own g a3 pp.
Proof.
  intros.
  apply pred_ext.
  -
 eapply derives_trans, prop_andp_left; [apply andp_right, derives_refl; apply ghost_valid_2|].
    intros (a3 & ? & ?); apply exp_right with a3, prop_andp_right; auto.
    erewrite <- ghost_op by eauto; apply derives_refl.
  -
 apply exp_left; intro; apply prop_andp_left; intros [].
    erewrite ghost_op by eauto; apply derives_refl.
Qed.

Lemma own_op_gen : forall g a1 a2 a3 pp, (valid_2 a1 a2 -> join a1 a2 a3) ->
  own g a1 pp * own g a2 pp = !!(valid_2 a1 a2) && own g a3 pp.
Proof.
  intros; apply pred_ext.
  -
 eapply derives_trans, prop_andp_left; [apply andp_right, derives_refl; apply ghost_valid_2|].
    intro; erewrite <- ghost_op by eauto.
    apply prop_andp_right; auto.
  -
 apply prop_andp_left; intro.
    erewrite ghost_op by eauto; apply derives_refl.
Qed.

End ghost.

Section Reference.

Lemma join_Bot : forall a b, sepalg.join a b Share.bot -> a = Share.bot /\ b = Share.bot.
  intros ?? (? & ?).
  apply lub_bot_e; auto.
Qed.

Global Program Instance pos_PCM (P : Ghost) : Ghost := { G := option (share * G);
  valid a := match a with Some (sh, _) => sh <> Share.bot | _ => True end;
  Join_G a b c := match a, b, c with
  | Some (sha, a'), Some (shb, b'), Some (shc, c') =>
      sha <> Share.bot /\ shb <> Share.bot /\ sepalg.join sha shb shc /\ join a' b' c'
  | Some (sh, a), None, Some c' | None, Some (sh, a), Some c' => c' = (sh, a)
  | None, None, None => True
  | _, _, _ => False
  end }.
Next Obligation.
repeat split; intros; intro X; decompose [and] X; congruence.
Qed.
Next Obligation.
repeat split; intros; intro X; decompose [and] X; congruence.
Qed.
Next Obligation.
repeat split; intros; intro X; decompose [and] X; congruence.
Qed.
Next Obligation.
repeat split; intros; intro X; decompose [and] X; congruence.
Qed.
Next Obligation.
apply fsep_sep.
exists (fun _ => None); auto.
intros [[]|]; constructor.
Defined.
Next Obligation.
constructor.
  -
 intros [[]|] [[]|] [[]|] [[]|]; unfold join; simpl; auto; try contradiction; try congruence.
    intros (? & ? & ? & ?) (? & ? & ? & ?); f_equal; f_equal; eapply join_eq; eauto.
  -
 intros [[]|] [[]|] [[]|] [[]|] [[]|]; try contradiction; unfold join; simpl;
      intros; decompose [and] H; decompose [and] H0;
      repeat match goal with H : (_, _) = (_, _) |- _ => inv H end;
      try solve [eexists (Some _); split; auto; simpl; auto]; try solve [exists None; split; auto].
    +
 destruct (join_assoc H2 H6) as (sh' & ? & ?), (join_assoc H5 H9) as (a' & ? & ?).
      exists (Some (sh', a')); repeat (split; auto).
      intro; subst.
      apply join_Bot in H8 as []; auto.
    +
 exists (Some (s2, g2)); auto.
  -
 intros [[]|] [[]|] [[]|]; try contradiction; unfold join; auto.
    intros (? & ? & ? & ?); split; auto; split; auto; split; apply join_comm; auto.
  -
 intros [[]|] [[]|] [[]|] [[]|]; try contradiction; intros H1 H2; try solve [inv H1; reflexivity || inv H2; reflexivity].
    destruct H1 as (? & ? & ? & ?), H2 as (? & ? & ? & ?); f_equal; f_equal; eapply join_positivity; eauto.
Qed.

Next Obligation.
destruct a as [[]|]; destruct b as [[]|]; destruct c as [[]|]; try trivial;
unfold join in *; try contradiction.
-
 decompose [and] H; assumption.
-
 congruence.
Qed.

Definition completable {P : Ghost} (a: @G (pos_PCM P)) r := exists x, join a x (Some (Share.top, r)).

Local Obligation Tactic := idtac.

Global Program Instance ref_PCM (P : Ghost) : Ghost :=
{ valid a := valid (fst a) /\ match snd a with Some r => completable (fst a) r | None => True end;
  Join_G a b c := @Join_G (pos_PCM P) (fst a) (fst b) (fst c) /\
    @psepalg.Join_lower _ (psepalg.Join_discrete _) (snd a) (snd b) (snd c) }.
Next Obligation.
  intros P; apply sepalg_generators.Sep_prod; try apply _.
  apply fsep_sep, _.
Defined.
Next Obligation.
  intros P; apply sepalg_generators.Perm_prod; typeclasses eauto.
Qed.

Next Obligation.
  intros P ??? [? J] []; split; [eapply join_valid; eauto|].
  destruct a, b, c; simpl in *; inv J; auto.
  +
 destruct o1; auto.
    destruct H1.
    destruct (join_assoc H H1) as (? & ? & ?); eexists; eauto.
  +
 inv H2.
Qed.

End Reference.

#[global] Program Instance exclusive_PCM A : Ghost :=
  { valid a := True; Join_G := Join_lower (Join_discrete A) }.

Definition excl {A} g a : mpred := own(RA := exclusive_PCM A) g (Some a) NoneP.

Lemma exclusive_update : forall {A} (v v' : A) p, excl p v |-- |==> excl p v'.
Proof.
  intros; apply ghost_update.
  intros ? (? & ? & _).
  exists (Some v'); split; simpl; auto; inv H; constructor.
  inv H1.
Qed.

Local Obligation Tactic := idtac.

#[global] Program Instance prod_PCM (GA GB: Ghost): Ghost := { G := @G GA * @G GB;
  valid a := valid (fst a) /\ valid (snd a); Join_G := Join_prod _ _ _ _ }.
Next Obligation.
  intros GA GB ??? [] []; split; eapply join_valid; eauto.
Defined.

Class PCM_order `{P : Ghost} (ord : G -> G -> Prop) := { ord_preorder :> PreOrder ord;
  ord_lub : forall a b c, ord a c -> ord b c -> {c' | join a b c' /\ ord c' c};
  join_ord : forall a b c, join a b c -> ord a c /\ ord b c; ord_join : forall a b, ord b a -> join a b a }.

Context `{ORD : PCM_order}.

Lemma join_refl : forall (v : G), join v v v.
  intros.
apply ord_join; reflexivity.
Qed.

Lemma join_compat : forall v1 v2 v' v'', join v2 v' v'' -> ord v1 v2 -> exists v0, join v1 v' v0 /\ ord v0 v''.
  intros.
  destruct (join_ord _ _ _ H).
  destruct (ord_lub v1 v' v'') as (? & ? & ?); eauto.
  etransitivity; eauto.
Qed.

Lemma join_ord_eq : forall a b, ord a b <-> exists c, join a c b.
  split.
  -
 intros; exists b.
    apply ord_join in H.
    apply join_comm; auto.
  -
 intros (? & H); apply join_ord in H; tauto.
Qed.

Global Program Instance snap_PCM : Ghost :=
  { valid _ := True; Join_G a b c := sepalg.join (fst a) (fst b) (fst c) /\
      if eq_dec (fst a) Share.bot then if eq_dec (fst b) Share.bot then join (snd a) (snd b) (snd c)
        else ord (snd a) (snd b) /\ snd c = snd b else snd c = snd a /\
          if eq_dec (fst b) Share.bot then ord (snd b) (snd a) else snd c = snd b }.
Next Obligation.
  exists (fun '(sh, a) => (Share.bot, a)); repeat intro.
  +
 destruct t; constructor; auto; simpl.
    rewrite eq_dec_refl.
    if_tac; [apply join_refl | split; auto].
    reflexivity.
  +
 destruct a, c, H as [? Hj].
    assert (join_sub g g0) as [].
    {
 if_tac in Hj.
if_tac in Hj.
      eexists; eauto.
      destruct Hj; simpl in *; subst.
      apply join_ord_eq; auto.
      destruct Hj; simpl in *; subst.
      apply join_sub_refl.
}
    eexists (_, _).
split; simpl.
    *
 apply join_bot_eq.
    *
 rewrite !eq_dec_refl; eauto.
  +
 destruct a; reflexivity.
Defined.
Next Obligation.
  constructor.
  -
 intros ???? [? Hjoin1] [? Hjoin2].
    assert (fst z = fst z') by (eapply join_eq; eauto).
    destruct z, z'; simpl in *; subst; f_equal.
    destruct (eq_dec (fst x) Share.bot); [|destruct Hjoin1, Hjoin2; subst; auto].
    destruct (eq_dec (fst y) Share.bot); [|destruct Hjoin1, Hjoin2; subst; auto].
    eapply join_eq; eauto.
  -
 intros ????? [Hsh1 Hjoin1] [Hsh2 Hjoin2].
    destruct (sepalg.join_assoc Hsh1 Hsh2) as [sh' []].
    destruct (eq_dec (fst b) Share.bot) eqn: Hb.
    +
 assert (fst d = fst a) as Hd.
      {
 eapply sepalg.join_eq; eauto.
        rewrite e0; apply join_bot_eq.
}
      rewrite Hd in Hsh1, Hsh2, Hjoin2.
      assert (sh' = fst c) as Hc.
      {
 eapply sepalg.join_eq; eauto.
        rewrite e0; apply bot_join_eq.
}
      subst sh'.
      destruct (eq_dec (fst c) Share.bot) eqn: Hc1.
      *
 destruct (eq_dec (fst a) Share.bot) eqn: Ha.
        --
 destruct (join_assoc Hjoin1 Hjoin2) as [c' []].
            destruct a, b, c; simpl in *; subst.
           exists (Share.bot, c'); split; split; rewrite ?eq_dec_refl; auto.
        --
 destruct Hjoin1 as [Hc' ?]; rewrite Hc' in Hjoin2.
           destruct Hjoin2, (ord_lub (snd b) (snd c) (snd a)) as [c' []]; eauto.
           destruct b, c; simpl in *; subst.
           exists (Share.bot, c'); split; split; rewrite ?eq_dec_refl, ?Ha; auto.
      *
 exists c.
        destruct (eq_dec (fst a) Share.bot) eqn: Ha; try solve [split; split; auto].
        --
 destruct Hjoin2.
           apply join_ord in Hjoin1; destruct Hjoin1.
           destruct b; simpl in *; subst.
           split; split; rewrite ?Ha, ?Hc1, ?eq_dec_refl; auto; split; auto; etransitivity; eauto.
        --
 destruct Hjoin2 as [He1 He2].
           destruct Hjoin1 as [Hd' ?]; rewrite He2, Hd' in He1; split; split; rewrite ?e0, ?He2, ?He1, ?Ha, ?Hc1, ?eq_dec_refl, ?Hd'; auto.
    +
 exists (sh', snd b); simpl.
      destruct (eq_dec (fst d) Share.bot).
      {
 rewrite e0 in Hsh1; apply join_Bot in Hsh1; destruct Hsh1; contradiction.
}
      destruct (eq_dec sh' Share.bot) eqn: Hn'.
      {
 subst; apply join_Bot in H; destruct H; contradiction.
}
      assert (snd d = snd b) as Hd by (destruct (eq_dec (fst a) Share.bot); tauto).
      rewrite Hd in Hjoin1, Hjoin2; destruct Hjoin2 as [He Hjoin2]; rewrite He in Hjoin2; split; split; simpl; rewrite ?Hb, ?Hn', ?Hd, ?He; auto.
  -
 intros ??? []; split; [apply join_comm; auto|].
    if_tac; if_tac; auto; tauto.
  -
 intros ???? [? Hjoin1] [? Hjoin2].
    assert (fst a = fst b) by (eapply join_positivity; eauto).
    destruct (eq_dec (fst a) Share.bot), a, a', b, b'; simpl in *; subst; f_equal.
    +
 rewrite eq_dec_refl in Hjoin2.
      apply join_Bot in H0 as []; subst.
      apply join_Bot in H as []; subst.
      rewrite !eq_dec_refl in Hjoin1, Hjoin2.
      eapply join_positivity; eauto.
    +
 destruct Hjoin1; auto.
Defined.
