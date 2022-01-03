(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "-deprecated-native-compiler-option" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/bedrock2/bedrock2/src/bedrock2" "bedrock2" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/bedrock2/bedrock2/src/bedrock2Examples" "bedrock2Examples" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/bedrock2/deps/coqutil/src/coqutil" "coqutil" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-top" "lightbulb" "-async-proofs-tac-j" "1" "-native-compiler" "no") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 717 lines to 555 lines, then from 568 lines to 1468 lines, then from 1472 lines to 694 lines *)
(* coqc version 8.16+alpha compiled with OCaml 4.13.0
   coqtop version runner-ns46nmmj-project-6138686-concurrent-0:/builds/coq/coq/_build/default,(HEAD detached at 5820455) (58204555aaac561f1cef980bf74a3ef045f3a9bb)
   Expected coqc runtime on this file: 33.010 sec *)
Require coqutil.sanity.
Require coqutil.Macros.subst.
Require coqutil.Macros.unique.
Require Coq.Strings.String.
Require Coq.Numbers.BinNums.
Require bedrock2.Syntax.
Require Coq.ZArith.BinIntDef.
Require Ltac2.Init.
Require Ltac2.Int.
Require Ltac2.Message.
Require Ltac2.Control.
Require Ltac2.Bool.
Require Ltac2.Array.
Require Ltac2.Char.
Require Ltac2.Constr.
Require Ltac2.Std.
Require Ltac2.Env.
Require Ltac2.List.
Require Ltac2.Fresh.
Require Ltac2.Ident.
Require Ltac2.Ind.
Require Ltac2.Ltac1.
Require Ltac2.Option.
Require Ltac2.Pattern.
Require Ltac2.Printf.
Require Ltac2.String.
Require Ltac2.Notations.
Require Ltac2.Ltac2.
Require coqutil.Macros.ident_to_string.
Require bedrock2.NotationsCustomEntry.
Require Coq.ZArith.ZArith.
Require Coq.Strings.HexString.
Require coqutil.Z.HexNotation.
Require Coq.micromega.Lia.
Require coqutil.Z.Lia.
Require Coq.btauto.Btauto.
Require coqutil.Z.bitblast.
Require Coq.ZArith.BinInt.
Require coqutil.Z.div_mod_to_equations.
Require coqutil.Z.BitOps.
Require Coq.setoid_ring.ZArithRing.
Require coqutil.Z.prove_Zeq_bitwise.
Require coqutil.Word.Interface.
Require Coq.Init.Byte.
Require Coq.Strings.Byte.
Require coqutil.Byte.
Require Coq.Lists.List.
Require bedrock2.ReversedListNotations.
Require bedrock2.TracePredicate.
Require Coq.ZArith.Zpow_facts.
Require coqutil.Z.PushPullMod.
Require Coq.setoid_ring.Ring_theory.
Require coqutil.Tactics.autoforward.
Require Coq.Arith.PeanoNat.
Require Coq.Arith.Compare_dec.
Require Coq.NArith.NArith.
Require coqutil.Decidable.
Require coqutil.Word.Properties.
Require coqutil.Tactics.destr.
Require coqutil.Tactics.forward.
Require coqutil.Tactics.Tactics.
Require coqutil.Datatypes.Option.
Require Coq.Sorting.Permutation.
Require coqutil.Datatypes.List.
Require coqutil.Word.LittleEndianList.
Require bedrock2Examples.lightbulb_spec.
Require coqutil.Tactics.letexists.
Require coqutil.Tactics.eabstract.
Require coqutil.Tactics.rdelta.
Require coqutil.Tactics.ident_of_string.
Require bedrock2.Notations.
Require coqutil.Datatypes.PrimitivePair.
Require coqutil.Datatypes.HList.
Require Coq.Classes.Morphisms.
Require Coq.Classes.RelationClasses.
Require Coq.Logic.PropExtensionality.
Require Coq.Logic.FunctionalExtensionality.
Require Coq.Program.Tactics.
Require coqutil.Datatypes.PropSet.
Require coqutil.Map.Interface.
Require coqutil.Map.Properties.
Require coqutil.Map.MapKeys.
Require coqutil.Map.OfFunc.
Require coqutil.Map.OfListWord.
Require coqutil.Word.Bitwidth.
Require coqutil.dlet.
Require bedrock2.MetricLogging.
Require bedrock2.Memory.
Require bedrock2.Semantics.
Require bedrock2.Lift1Prop.
Require bedrock2.Map.Separation.
Require bedrock2.WeakestPrecondition.
Require bedrock2.WeakestPreconditionProperties.
Require coqutil.Tactics.syntactic_unify.
Require bedrock2.Map.SeparationLogic.
Require bedrock2.Markers.
Require bedrock2.Loops.
Require coqutil.Tactics.eplace.
Require bedrock2.Array.
Require coqutil.Macros.symmetry.
Require Coq.setoid_ring.Ring_tac.
Require bedrock2.ptsto_bytes.
Require bedrock2.Scalars.
Require Coq.Logic.Eqdep_dec.
Require coqutil.Map.SortedList.
Require bedrock2.ProgramLogic.
Require Coq.NArith.BinNatDef.
Require coqutil.Datatypes.String.
Require coqutil.Map.SortedListString.
Require coqutil.Word.Bitwidth32.
Require bedrock2Examples.SPI.
Require bedrock2.AbsintWordToZ.
Module Export AdmitTactic.
Module Import LocalFalse.
End LocalFalse.
End AdmitTactic.
Import coqutil.Z.HexNotation.
Import bedrock2Examples.SPI.
Import Coq.ZArith.BinInt.
Import List.ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.
Import coqutil.Word.Interface.
Import bedrock2.TracePredicate.
Import TracePredicateNotations.

Import coqutil.Map.Interface.

Section WithParameters.
  Context {word: word.word 32} {mem: map.map word Byte.byte}.
Global Instance spec_of_lan9250_readword : ProgramLogic.spec_of "lan9250_readword". exact (fun functions => forall t m a,
    (0x0 <= Word.Interface.word.unsigned a < 0x400) ->
    WeakestPrecondition.call functions "lan9250_readword" t m [a] (fun T M RETS =>
      M = m /\
      exists ret err, RETS = [ret; err] /\
      exists iol, T = iol ++ t /\
      exists ioh, mmio_trace_abstraction_relation ioh iol /\ Logic.or
        (word.unsigned err <> 0 /\ (any +++ lightbulb_spec.spi_timeout _) ioh)
        (word.unsigned err = 0 /\ lightbulb_spec.lan9250_fastread4 _ a ret ioh))). Defined.
End WithParameters.
Import coqutil.Z.Lia.
Import bedrock2.Syntax.
Import bedrock2.NotationsCustomEntry.
Import coqutil.Z.HexNotation.
Import bedrock2.FE310CSemantics.
Import coqutil.Macros.symmetry.
Import coqutil.Byte.
Import bedrock2Examples.SPI.
Import coqutil.Word.Interface.
Import coqutil.Map.Interface.
Import coqutil.Tactics.letexists.
Import bedrock2.WeakestPrecondition.
Import bedrock2.ProgramLogic.
Import bedrock2.Array.
Import bedrock2.Scalars.
Import bedrock2.Map.SeparationLogic.
Import Coq.ZArith.ZArith.

Section WithParameters.
Import List.ListNotations.
  Context {word: word.word 32} {mem: map.map word Byte.byte}.
  Context {word_ok: word.ok word} {mem_ok: map.ok mem}.
  Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

  Definition recvEthernet :=
    ("recvEthernet", (["buf"], ["num_bytes";"err"], bedrock_func_body:(
      num_bytes = $0;
      unpack! read, err = lan9250_readword(coq:(Ox"7C"));
      require !err else { err = $-1 };
      require (read & coq:((2^8-1)*2^16)) else { err = $1 };
      unpack! read, err = lan9250_readword($0x40);
      require !err else { err = $-1 };

      num_bytes = read >> $16 & coq:(2^14-1);

      num_bytes = (num_bytes + coq:(4-1)) >> $2;
      num_bytes = num_bytes + num_bytes;
      num_bytes = num_bytes + num_bytes;

      require (num_bytes < coq:(1520 + 1)) else { err = $2 };

      i = $0; while (i < num_bytes) {
        unpack! read, err = lan9250_readword($0);
        if err { err = $-1; i = num_bytes }
        else { store4(buf + i, read); i = i + $4 }
      }
      ))).
Import Coq.Init.Datatypes.
  Local Notation bytes := (array scalar8 (word.of_Z 1)).
  Local Infix "*" := (sep).
  Local Infix "*" := (sep) : type_scope.

  Import bedrock2.TracePredicate.
  Import coqutil.Word.Properties.
  Import bedrock2Examples.lightbulb_spec.
Instance spec_of_recvEthernet : spec_of "recvEthernet".
exact (fun functions =>
    forall p_addr (buf:list byte) R m t,
      (array scalar8 (word.of_Z 1) p_addr buf * R) m ->
      length buf = 1520%nat ->
      WeakestPrecondition.call functions "recvEthernet" t m [p_addr] (fun t' m' rets =>
        exists bytes_written err, rets = [bytes_written; err] /\
        exists iol, t' = iol ++ t /\
        exists ioh, mmio_trace_abstraction_relation ioh iol /\ Logic.or
          (word.unsigned err = 0 /\
            exists recv buf, (bytes p_addr recv * bytes (word.add p_addr bytes_written) buf * R) m' /\ lan9250_recv _ recv ioh /\
            word.unsigned bytes_written + Z.of_nat (length buf) = 1520%Z /\
            Z.of_nat (length recv) = word.unsigned bytes_written)
          (word.unsigned err <> 0 /\ exists buf, (array scalar8 (word.of_Z 1) p_addr buf * R) m' /\ length buf = 1520%nat /\ (
             word.unsigned err = 1 /\ lan9250_recv_no_packet _ ioh \/
             word.unsigned err = 2 /\ lan9250_recv_packet_too_long _ ioh \/
             word.unsigned err = 2^32-1 /\ TracePredicate.concat TracePredicate.any (spi_timeout word) ioh
            ))
        )).
Defined.
Import bedrock2.AbsintWordToZ.
  Local Ltac trans_ltu :=
    match goal with
    | H : word.unsigned ?v <> 0 |- _ =>
        let v := rdelta.rdelta v in
        let __ := lazymatch v with if word.ltu _ _ then word.of_Z 1 else word.of_Z 0 => I end in
        eapply Properties.word.if_nonzero in H; rewrite word.unsigned_ltu in H; eapply Z.ltb_lt in H
    | H : word.unsigned ?v = 0 |- _ =>
        let v := rdelta.rdelta v in
        let __ := lazymatch v with if word.ltu _ _ then word.of_Z 1 else word.of_Z 0 => I end in
        eapply Word.Properties.word.if_zero in H; rewrite word.unsigned_ltu in H; eapply Z.ltb_nlt in H
  end.
  Local Ltac split_if :=
    lazymatch goal with
      |- WeakestPrecondition.cmd _ ?c _ _ _ ?post =>
      let c := eval hnf in c in
          lazymatch c with
          | cmd.cond _ _ _ => letexists; split; [solve[repeat straightline]|split]
          end
    end.

  Local Hint Mode map.map - - : typeclass_instances.

  Local Ltac prove_ext_spec :=
    lazymatch goal with
    | |- ext_spec _ _ _ _ _ => split; [shelve|]; split; [trivial|]
    end.

  Local Ltac zify_unsigned :=
    repeat match goal with
    | |- context[word.unsigned ?e] => let H := unsigned.zify_expr e in rewrite H; pose proof H
    | G : context[word.unsigned ?e] |- _ => let H := unsigned.zify_expr e in rewrite H in G; pose proof H
    end;
    repeat match goal with H:absint_eq ?x ?x |- _ => clear H end;
    repeat match goal with H:?A |- _ => clear H; match goal with G:A |- _ => idtac end end.

  Add Ring wring : (Properties.word.ring_theory (word := word))
        (preprocess [autorewrite with rew_word_morphism],
         morphism (Properties.word.ring_morph (word := word)),
         constants [Properties.word_cst]).

  Lemma recvEthernet_ok : program_logic_goal_for_function! recvEthernet.
  Proof.
    straightline.
    rename H into Hcall; clear H0 H1.
rename H2 into H.
rename H3 into H0.
    repeat (straightline || split_if || straightline_call || eauto 99 || prove_ext_spec).
    1, 3: rewrite word.unsigned_of_Z; cbv - [Z.le Z.lt]; clear; blia.

    3: {

    refine (Loops.tailrec_earlyout
      (HList.polymorphic_list.cons (list byte) (HList.polymorphic_list.cons (mem -> Prop) HList.polymorphic_list.nil))
      ["buf";"num_bytes";"i";"read";"err"]
      (fun v scratch R t m buf num_bytes_loop i read err => PrimitivePair.pair.mk (
        word.unsigned err = 0 /\ word.unsigned i <= word.unsigned num_bytes /\
        v = word.unsigned i /\ (bytes (word.add buf i) scratch * R) m /\
        Z.of_nat (List.length scratch) = word.unsigned (word.sub num_bytes i) /\
        word.unsigned i mod 4 = word.unsigned num_bytes mod 4 /\
        num_bytes_loop = num_bytes)
      (fun T M BUF NUM_BYTES I READ ERR =>
         NUM_BYTES = num_bytes_loop /\
         exists RECV, (bytes (word.add buf i) RECV * R) M /\
         List.length RECV = List.length scratch /\
         exists iol, T = iol ++ t /\ exists ioh, mmio_trace_abstraction_relation ioh iol /\
         (word.unsigned ERR = 0 /\ lan9250_readpacket _ RECV ioh \/
          word.unsigned ERR = 2^32-1 /\ TracePredicate.concat TracePredicate.any (spi_timeout _) ioh ) )
      )
      _ _ _ _ _ _ _ _);

    cbn [HList.hlist.foralls HList.tuple.foralls
         HList.hlist.existss HList.tuple.existss
         HList.hlist.apply  HList.tuple.apply
         HList.hlist
         List.repeat Datatypes.length
         HList.polymorphic_list.repeat HList.polymorphic_list.length
         PrimitivePair.pair._1 PrimitivePair.pair._2] in *;
      repeat (straightline || split_if || eapply interact_nomem || eauto 99).
    {
 exact (Z.gt_wf (word.unsigned num_bytes)).
}
    1: repeat (refine (conj _ _)); eauto.
    {
 subst i.
rewrite word.unsigned_of_Z.
      eapply Properties.word.unsigned_range.
}
    1: zify_unsigned.
    1: replace (word.add p_addr i) with p_addr by (subst i; ring).
    1: rewrite <- (List.firstn_skipn (Z.to_nat (word.unsigned (word.sub num_bytes i) ) )  _) in H.
    1: SeparationLogic.seprewrite_in (symmetry! @bytearray_index_merge) H; [|ecancel_assumption].
      1,2,3:
      repeat match goal with
      | |- ?x = ?x => exact (eq_refl x)
      | _ => progress trans_ltu
      | _ => progress zify_unsigned
      | _ => progress rewrite ?Znat.Z2Nat.id by blia
      | H: _ |- _ => progress (rewrite ?Znat.Z2Nat.id in H by blia)
      | _ => rewrite List.length_firstn_inbounds by blia
      | _ => progress rewrite ?Z.sub_0_r
      end; repeat straightline.
      {
 repeat match goal with x:= _ |- context[?x]  => subst x end.
clear.
Z.div_mod_to_equations.
blia.
}

      {
 straightline_call; repeat straightline.
        {
 rewrite word.unsigned_of_Z.
cbv; clear.
intuition congruence.
}
        split_if; do 6 straightline.

        {
 straightline.
          straightline.
          straightline.
          straightline.

          do 5 eexists; split; [repeat straightline|]; [].
          left.
          repeat straightline.
          {
 subst br0.
rewrite word.unsigned_ltu, Z.ltb_irrefl, word.unsigned_of_Z; exact eq_refl.
}
          split; eauto.
          eexists; split; eauto.
          split; eauto.
          eexists; split.
          {
 subst a; eauto.
}
          eexists; split; eauto.
          right; split.
          {
 subst err.
rewrite word.unsigned_of_Z.
exact eq_refl.
}
          intuition eauto.
}

        do 4 straightline.
        trans_ltu.
        match goal with
          | H: context[word.unsigned (word.sub ?a ?b)] |- _ =>
              pose proof Properties.word.unsigned_range a;
              pose proof Properties.word.unsigned_range b;
              let H := fresh in
              pose proof word.unsigned_sub a b as H;
              unfold word.wrap in H;
              rewrite Z.mod_small in H by blia
        end.
        match goal with H10 : _ ?a0 |- store _ ?a0 _ _ _ => rewrite <- (List.firstn_skipn 4 _) in H10;
          SeparationLogic.seprewrite_in (symmetry! @bytearray_index_merge) H10 end.
        {
 instantiate (1:= word.of_Z 4).
          rewrite word.unsigned_of_Z.
          rewrite List.length_firstn_inbounds; [exact eq_refl|].
Z.div_mod_to_equations.
blia.
}
        do 2 straightline.
        match goal with H12:_|-_ => seprewrite_in @scalar32_of_bytes H12 end.
1: reflexivity.
        {
 eapply List.length_firstn_inbounds; Z.div_mod_to_equations; blia.
}
        straightline.

        do 3 straightline.

        do 5 letexists.
split.
{
 repeat straightline.
}
        right.
do 3 letexists.
        repeat split; repeat straightline; repeat split.
        {
 intuition idtac.
}
        {
 subst i.
          rewrite word.unsigned_add; cbv [word.wrap]; rewrite Z.mod_small;
          replace (word.unsigned (word.of_Z 4)) with 4.
          2,4: rewrite word.unsigned_of_Z; exact eq_refl.
          1,2: try (Z.div_mod_to_equations; blia).
}
        {
 replace (word.add x9 i)
            with (word.add (word.add x9 x11) (word.of_Z 4)) by (subst i; ring).
          ecancel_assumption.
}
        {
 repeat match goal with x1 := _ |- _ => subst x1; rewrite List.length_skipn; rewrite Znat.Nat2Z.inj_sub end.
          {
 repeat match goal with H5:_|-_=>rewrite H5 end; subst i.
            progress replace (word.sub num_bytes (word.add x11 (word.of_Z 4)))
              with (word.sub (word.sub num_bytes x11) (word.of_Z 4)) by ring.
            rewrite (word.unsigned_sub _ (word.of_Z 4)).
            unfold word.wrap.
rewrite Z.mod_small.
            all: replace (word.unsigned (word.of_Z 4)) with 4 by (rewrite word.unsigned_of_Z; exact eq_refl).
            all: change (Z.of_nat 4) with 4.
            all : Z.div_mod_to_equations; blia.
}
          Z.div_mod_to_equations; blia.
}
        {
 subst i.
          rewrite word.unsigned_add.
unfold word.wrap.
rewrite (Z.mod_small _ (2 ^ 32)).
          {
 revert dependent x11.
clear -word_ok.
            replace (word.unsigned (word.of_Z 4)) with 4 by (rewrite word.unsigned_of_Z; exact eq_refl).
            intros.
            Z.div_mod_to_equations.
blia.
}
          replace (word.unsigned (word.of_Z 4)) with 4 by (rewrite word.unsigned_of_Z; exact eq_refl).
          Z.div_mod_to_equations.
          blia.
}
        {
 repeat match goal with |- context [?x] => is_var x; subst x end.
          rewrite word.unsigned_add.
unfold word.wrap.
rewrite Z.mod_small.
          {
 replace (word.unsigned (word.of_Z 4)) with 4 by (rewrite word.unsigned_of_Z; exact eq_refl).
blia.
}
          replace (word.unsigned (word.of_Z 4)) with 4 by (rewrite word.unsigned_of_Z; exact eq_refl).
          Z.div_mod_to_equations.
blia.
}
        {
 subst v'.
subst i.
          rewrite word.unsigned_add.
          replace (word.unsigned (word.of_Z 4)) with 4 by (rewrite word.unsigned_of_Z; exact eq_refl).
          unfold word.wrap.
rewrite (Z.mod_small _ (2 ^ 32)); Z.div_mod_to_equations; blia.
}

        {
 letexists; repeat split.
          {
 repeat match goal with x := _ |- _ => is_var x; subst x end; subst.
            cbv [scalar32 truncated_word truncate_word truncate_Z truncated_scalar littleendian ptsto_bytes.ptsto_bytes] in *.
            progress replace (word.add x9 (word.add x11 (word.of_Z 4))) with
                    (word.add (word.add x9 x11) (word.of_Z 4)) in * by ring.
            SeparationLogic.seprewrite_in (@bytearray_index_merge) H25.
            {
 rewrite word.unsigned_of_Z; exact eq_refl.
}
 {
 ecancel_assumption.
}
 }
          {
 subst RECV.
rewrite List.app_length.
            rewrite H26.
subst x22.
rewrite List.length_skipn.
            unshelve erewrite (_ : length (HList.tuple.to_list _) = 4%nat); [exact eq_refl|].
            enough ((4 <= length x7)%nat) by blia.
            Z.div_mod_to_equations; blia.
}
          cbv [truncate_word truncate_Z] in *.
          repeat match goal with x := _ |- _ => is_var x; subst x end; subst.
          eexists; split.
          {
 rewrite List.app_assoc; eauto.
}
          eexists; split.
          {
 eapply List.Forall2_app; eauto.
 }
          rewrite HList.tuple.to_list_of_list.
          destruct H29; [left|right]; repeat (straightline || split || eauto using TracePredicate.any_app_more).
          eapply TracePredicate.concat_app; eauto.
          unshelve erewrite (_ : LittleEndianList.le_combine _ = word.unsigned x10); rewrite ?word.of_Z_unsigned; try solve [intuition idtac].
          {
            etransitivity.
            1: eapply (LittleEndianList.le_combine_split 4).
            eapply Properties.word.wrap_unsigned.
}
 }
 }

      {
 split; eauto.
eexists; split; eauto.
split; eauto.
exists nil; split; eauto.
        eexists; split; [constructor|].
        left.
split; eauto.
        enough (Hlen : length x7 = 0%nat) by (destruct x7; try solve[inversion Hlen]; exact eq_refl).
        PreOmega.zify.
        rewrite H13.
        subst br.
        rewrite word.unsigned_ltu in H11.
        destruct (word.unsigned x11 <? word.unsigned num_bytes) eqn:HJ.
        {
 rewrite word.unsigned_of_Z in H11.
inversion H11.
}
        eapply Z.ltb_nlt in HJ.
        revert dependent x7; revert dependent num_bytes; revert dependent x11; clear -word_ok; intros.
        unshelve erewrite (_:x11 = num_bytes) in *.
        {
 eapply Properties.word.unsigned_inj.
Z.div_mod_to_equations; blia.
}
        rewrite word.unsigned_sub, Z.sub_diag; exact eq_refl.
}
      repeat straightline.
      repeat letexists.
split.
{
 repeat straightline.
}
      eexists _, _.
split.
{
 exact eq_refl.
}

      repeat straightline.
      subst i.
      match goal with H: _ |- _ =>
        progress repeat (unshelve erewrite (_ : forall x, word.add x (word.of_Z 0) = x) in H; [intros; ring|]);
        progress repeat (unshelve erewrite (_ : forall x, word.sub x (word.of_Z 0) = x) in H; [intros; ring|])
      end.
      eexists; split.
      1: {
 repeat match goal with |- context [?x] => match type of x with list _ => subst x end end.
        repeat rewrite List.app_assoc.
f_equal.
}
      eexists; split.
      1:repeat eapply List.Forall2_app; eauto.
      destruct H14; [left|right]; repeat straightline; repeat split; eauto.
      {
 trans_ltu;
        replace (word.unsigned (word.of_Z 1521)) with 1521 in *
          by (rewrite word.unsigned_of_Z; exact eq_refl).
          eexists _, _; repeat split.
        {
 SeparationLogic.ecancel_assumption.
}
        {
 revert dependent x2.
revert dependent x6.
intros.
          destruct H5; repeat straightline; try contradiction.
          destruct H9; repeat straightline; try contradiction.
          eexists _, _; split.
          {
 rewrite <-!List.app_assoc.
eauto using concat_app.
}
          split; [zify_unsigned; eauto|].
        {
 cbv beta delta [lan9250_decode_length].
          rewrite H11.
rewrite List.firstn_length, Znat.Nat2Z.inj_min.
          replace (word.sub num_bytes (word.of_Z 0)) with num_bytes by ring.
          rewrite ?Znat.Z2Nat.id by eapply word.unsigned_range.
          transitivity (word.unsigned num_bytes); [blia|exact eq_refl].
}
 }
        {
 pose proof word.unsigned_range num_bytes.
          rewrite List.length_skipn.
blia.
}
        rewrite H11, List.length_firstn_inbounds, ?Znat.Z2Nat.id.
        all: try (zify_unsigned; blia).
        }
      {
 repeat match goal with H : _ |- _ => rewrite H; intro HX; solve[inversion HX] end.
}
      {
 trans_ltu;
        replace (word.unsigned (word.of_Z 1521)) with 1521 in * by
          (rewrite word.unsigned_of_Z; exact eq_refl).
        eexists _; split; eauto; repeat split; try blia.
        {
 SeparationLogic.seprewrite_in @bytearray_index_merge H10.
          {
 rewrite H11.
            1: replace (word.sub num_bytes (word.of_Z 0)) with num_bytes by ring.
            rewrite List.length_firstn_inbounds, ?Znat.Z2Nat.id.
            1:exact eq_refl.
            1:eapply word.unsigned_range.
            rewrite ?Znat.Z2Nat.id by eapply word.unsigned_range.
            blia.
}
          eassumption.
}
        {
 1:rewrite List.app_length, List.length_skipn, H11, List.firstn_length.
          replace (word.sub num_bytes (word.of_Z 0)) with num_bytes by ring.
          enough (Z.to_nat (word.unsigned num_bytes) <= length buf)%nat by blia.
          rewrite ?Znat.Z2Nat.id by eapply word.unsigned_range; blia.
}
        right.
right.
split; eauto using TracePredicate.any_app_more.
}
 }

    all: repeat letexists; split; repeat straightline;
      eexists _, _; split; [ exact eq_refl | ].
    all: eexists; split;
      [repeat match goal with |- context [?x] => match type of x with list _ => subst x end end;
      rewrite ?List.app_assoc; eauto|].
    all: eexists; split;
      [repeat eapply List.Forall2_app; eauto|].
    all:
      right; subst err;
      split; [intro HX; rewrite word.unsigned_of_Z in HX; inversion HX|].
    all : repeat ((eexists; split; [solve[eauto]|]) || (split; [solve[eauto]|])).
    all : rewrite !word.unsigned_of_Z.

    {
 left; split; [exact eq_refl|] || right.
      left; split; [exact eq_refl|] || right.
            split; [exact eq_refl|].
        intuition eauto using TracePredicate.any_app_more.
}
    {
 left; split; [exact eq_refl|] || right.
      left; split; [exact eq_refl|] || right.
            split; [exact eq_refl|].
        intuition eauto using TracePredicate.any_app_more.
}
    {
 left; split; [exact eq_refl|] || right.
      left; split; [exact eq_refl|].
      eexists _, _; split.
      1:eapply TracePredicate.concat_app; try intuition eassumption.
      subst v0.
      rewrite word.unsigned_ltu in H6.
      destruct (word.unsigned num_bytes <? word.unsigned (word.of_Z 1521)) eqn:?.
      all : rewrite word.unsigned_of_Z in Heqb, H6; try inversion H6.
      eapply Z.ltb_nlt in Heqb; revert Heqb.
      repeat match goal with |- context [?x] => match type of x with _ => subst x end end.
      cbv [lan9250_decode_length].
split.
2: cbn in *; blia.
      subst v.
rewrite word.unsigned_and_nowrap, word.unsigned_of_Z in H2.
eapply H2.
}
    {
 left.
      split; [exact eq_refl|].
      eexists; split; intuition eauto.
}
  Defined.
