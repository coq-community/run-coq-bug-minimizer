(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "-deprecated-native-compiler-option" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/bedrock2/processor/src/processor" "processor" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/bedrock2/deps/coqutil/src/coqutil" "coqutil" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/bedrock2/deps/riscv-coq/src/riscv" "riscv" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/bedrock2/deps/kami/Kami" "Kami" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-top" "bug_01" "-async-proofs-tac-j" "1" "-native-compiler" "no") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 3608 lines to 860 lines, then from 846 lines to 763 lines, then from 776 lines to 1308 lines, then from 1313 lines to 1140 lines, then from 1137 lines to 879 lines, then from 892 lines to 1319 lines, then from 1324 lines to 1261 lines, then from 1257 lines to 988 lines, then from 995 lines to 970 lines, then from 983 lines to 1633 lines, then from 1637 lines to 1335 lines *)
(* coqc version 8.16+alpha compiled with OCaml 4.13.0
   coqtop version runner-zxwgkjap-project-6138686-concurrent-0:/builds/coq/coq/_build/default,(HEAD detached at f054677) (f0546773f9c28baf7c9082c77355fdcec8e20139)
   Expected coqc runtime on this file: 34.971 sec *)
Require Coq.ZArith.ZArith.
Require Coq.ZArith.BinIntDef.
Require Coq.ZArith.BinInt.
Require coqutil.Word.Interface.
Require coqutil.Word.Bitwidth.
Require coqutil.Word.Bitwidth32.
Require coqutil.Tactics.rdelta.
Require Coq.Logic.FunctionalExtensionality.
Require Coq.Logic.PropExtensionality.
Require Coq.Lists.List.
Require riscv.Utility.Monads.
Require riscv.Utility.MonadNotations.
Require Coq.Program.Tactics.
Require Coq.Program.Wf.
Require Coq.Init.Datatypes.
Require Coq.setoid_ring.Ring_theory.
Require Coq.Init.Byte.
Require Coq.Strings.Byte.
Require coqutil.Byte.
Require coqutil.Datatypes.PrimitivePair.
Require coqutil.Datatypes.HList.
Require coqutil.sanity.
Require Coq.micromega.Lia.
Require coqutil.Z.Lia.
Require Coq.btauto.Btauto.
Require coqutil.Z.bitblast.
Require coqutil.Z.div_mod_to_equations.
Require coqutil.Z.BitOps.
Require riscv.Utility.Utility.
Require riscv.Spec.Decode.
Require riscv.Spec.CSRField.
Require riscv.Spec.Machine.
Require coqutil.Tactics.autoforward.
Require Coq.Arith.PeanoNat.
Require Coq.Arith.Compare_dec.
Require Coq.NArith.NArith.
Require Coq.Strings.String.
Require coqutil.Decidable.
Require coqutil.Tactics.destr.
Require coqutil.Tactics.forward.
Require coqutil.Tactics.Tactics.
Require coqutil.Datatypes.Option.
Require Coq.Sorting.Permutation.
Require coqutil.Sorting.Permutation.
Require coqutil.Datatypes.List.
Require Coq.Classes.Morphisms.
Require Coq.Classes.RelationClasses.
Require coqutil.Datatypes.PropSet.
Require coqutil.Map.Interface.
Require Coq.ZArith.Zpow_facts.
Require coqutil.Z.PushPullMod.
Require coqutil.Word.Properties.
Require coqutil.Map.Properties.
Require riscv.Platform.Memory.
Require Coq.setoid_ring.ZArithRing.
Require coqutil.Z.prove_Zeq_bitwise.
Require coqutil.Word.LittleEndianList.
Require coqutil.Word.LittleEndian.
Require riscv.Platform.RiscvMachine.
Require riscv.Utility.MkMachineWidth.
Require riscv.Spec.Primitives.
Require riscv.Platform.MetricLogging.
Require riscv.Platform.MetricRiscvMachine.
Require riscv.Spec.MetricPrimitives.
Require riscv.Utility.FreeMonad.
Require coqutil.Datatypes.ListSet.
Require riscv.Platform.MaterializeRiscvProgram.
Require riscv.Spec.VirtualMemory.
Require riscv.Spec.ExecuteI.
Require riscv.Spec.ExecuteI64.
Require riscv.Spec.ExecuteM.
Require riscv.Spec.ExecuteM64.
Require riscv.Spec.CSR.
Require riscv.Spec.CSRGetSet.
Require riscv.Spec.CSRSpec.
Require riscv.Spec.ExecuteCSR.
Require riscv.Spec.Execute.
Require riscv.Platform.Run.
Require riscv.Platform.Sane.
Require riscv.Platform.MinimalMMIO.
Require riscv.Platform.MetricMinimalMMIO.
Require riscv.Platform.FE310ExtSpec.
Require Coq.Bool.Bool.
Require Coq.Strings.Ascii.
Require Coq.Logic.Eqdep.
Require Kami.Lib.CommonTactics.
Require Coq.Program.Equality.
Require Kami.Lib.StringAsList.
Require Kami.Lib.StringEq.
Require Kami.Lib.Indexer.
Require Coq.FSets.FMapList.
Require Coq.FSets.FMapFacts.
Require Coq.Lists.SetoidList.
Require Coq.Structures.OrderedType.
Require Coq.Structures.OrderedTypeEx.
Require Coq.Structures.Equalities.
Require Coq.Logic.Eqdep_dec.
Require Coq.FSets.FMapInterface.
Require Kami.Lib.StringAsOT.
Require Coq.Arith.Arith.
Require Coq.Arith.Div2.
Require Coq.Logic.EqdepFacts.
Require Coq.setoid_ring.Ring.
Require Coq.setoid_ring.Ring_polynom.
Require Kami.Lib.Nlia.
Require Kami.Lib.N_Z_nat_conversions.
Require Kami.Lib.NatLib.
Require Kami.Lib.DepEq.
Require Kami.Lib.Word.
Require Kami.Lib.Struct.
Require Kami.Lib.FMap.
Require Coq.Arith.Peano_dec.
Require Coq.Vectors.Vector.
Require Kami.Lib.VectorFacts.
Require Kami.Lib.ilist.
Require Kami.Syntax.
Require Kami.Semantics.
Require Kami.Wf.
Require Kami.Notations.
Require Coq.Program.Basics.
Require Kami.Lib.ListSupport.
Require Kami.SemFacts.
Require Kami.ModularFacts.
Require Kami.RefinementFacts.
Require Kami.Decomposition.
Require Kami.Inline.
Require Kami.InlineFacts.
Require Kami.PartialInlineFacts.
Require Kami.Lib.Reflection.
Require Kami.StepDet.
Require Kami.Renaming.
Require Kami.Specialize.
Require Kami.Duplicate.
Require Kami.Substitute.
Require Kami.Lib.Concat.
Require Kami.ModuleBound.
Require Kami.ModuleBoundEx.
Require Kami.Tactics.
Require Kami.Kami.
Require Kami.Ex.Names.
Require Kami.Ex.MemTypes.
Require Kami.Ex.SC.
Require Kami.Ex.IsaRv32.
Require Kami.Ex.SCMMInl.
Require Kami.Ex.SCMMInv.

Declare ML Module "coq-core.plugins.ltac".
Module Export AdmitTactic.
Module Import LocalFalse.
Inductive False : Prop := .
End LocalFalse.
Axiom proof_admitted : False.
Global Set Default Proof Mode "Classic".
Tactic Notation "admit" := abstract case proof_admitted.
End AdmitTactic.

Module Export processor_DOT_KamiWord_WRAPPED.
Module Export KamiWord.
Import Coq.ZArith.ZArith.
Import Coq.ZArith.BinIntDef.
Import Coq.ZArith.BinInt.
Import coqutil.Z.Lia.
Import coqutil.sanity.
Import coqutil.Tactics.forward.
Import coqutil.Word.Interface.
Import word.
Import Kami.Lib.Word.
Import coqutil.Tactics.destr.
Import coqutil.Z.div_mod_to_equations.

Local Open Scope bool_scope.
Local Open Scope Z_scope.

Section KamiWordFacts.

   
  Fact Znat_N2Z_inj_mod : forall n m : N, m <> 0%N -> Z.of_N (n mod m) = Z.of_N n mod Z.of_N m.
Admitted.

  Lemma wordToN_split2 a b w :
    wordToN (@split2 a b w) = BinNat.N.div (wordToN w) (NatLib.Npow2 a).
Admitted.

  Lemma wmsb_split2 a b w x y (H:b <> 0%nat)
    : wmsb (split2 a b w) x = wmsb w y.
Admitted.

  Lemma wordToZ_split2 a b w (H:b <> 0%nat)
    : wordToZ (@split2 a b w) = Z.div (wordToZ w) (2^Z.of_nat a).
Admitted.

  Lemma wordToN_wones_ones:
    forall sz, wordToN (wones sz) = BinNat.N.ones (BinNat.N.of_nat sz).
Admitted.

  Lemma uwordToZ_wplus_distr:
    forall sz (x y: Word.word sz),
      Z.of_N (wordToN (x ^+ y)) = (Z.of_N (wordToN x) + Z.of_N (wordToN y)) mod 2 ^ (Z.of_nat sz).
Admitted.

  Lemma wnot_idempotent:
    forall {sz} (w: word sz),
      wnot (wnot w) = w.
Admitted.

  Lemma wordToN_eq_rect:
    forall sz (w: Word.word sz) nsz Hsz,
      wordToN (eq_rect _ Word.word w nsz Hsz) = wordToN w.
Admitted.

  Lemma Z_pow_add_lor:
    forall n m p: Z,
      0 <= n < 2 ^ p -> 0 <= m -> 0 <= p ->
      (n + 2 ^ p * m)%Z = Z.lor n (2 ^ p * m).
Admitted.

  Lemma Z_of_wordToN_combine_alt:
    forall sz1 (w1: Word.word sz1) sz2 (w2: Word.word sz2),
      Z.of_N (wordToN (Word.combine w1 w2)) =
      Z.lor (Z.of_N (wordToN w1)) (Z.shiftl (Z.of_N (wordToN w2)) (Z.of_N (BinNat.N.of_nat sz1))).
Admitted.

  Lemma ZToWord_zero:
    forall n, ZToWord n 0 = wzero n.
Admitted.

  Lemma combine_wplus_wzero:
    forall sz1 (wb: Word.word sz1) sz2 (w1 w2: Word.word sz2),
      Word.combine wb w1 ^+ Word.combine (wzero sz1) w2 =
      Word.combine wb (w1 ^+ w2).
Admitted.

  Lemma split1_wplus_silent:
    forall sz1 sz2 (w1 w2: Word.word (sz1 + sz2)),
      split1 sz1 sz2 w2 = wzero _ ->
      split1 sz1 sz2 (w1 ^+ w2) = split1 sz1 sz2 w1.
Admitted.

  Lemma wordToN_split1 a b w :
    wordToN (@split1 a b w) = BinNat.N.modulo (wordToN w) (NatLib.Npow2 a).
Admitted.

  Lemma sumbool_rect_weq {T} a b n x y :
    sumbool_rect (fun _ => T) (fun _ => a) (fun _ => b) (@weq n x y) = if weqb x y then a else b.
Admitted.

  Lemma sumbool_rect_bool_weq n x y :
    sumbool_rect (fun _ => bool) (fun _ => true) (fun _ => false) (@weq n x y) = weqb x y.
Admitted.

  Lemma unsigned_eqb n x y : Z.eqb (Z.of_N (wordToN x)) (Z.of_N (wordToN y)) = @weqb n x y.
Admitted.

  Lemma unsigned_split1_mod:
    forall n m w,
      Z.of_N (wordToN (split1 n m w)) = Z.of_N (wordToN w) mod (2 ^ (Z.of_nat n)).
Admitted.

End KamiWordFacts.

Section WithWidth.
  Context {width : Z}.
  Context {width_nonneg : Z.lt 0 width}.
  Local Notation sz := (Z.to_nat width).

  Definition kword: Type := Kami.Lib.Word.word sz.
  Definition kunsigned(x: kword): Z := Z.of_N (wordToN x).
Definition ksigned: kword -> Z. exact (@wordToZ sz). Defined.
Definition kofZ: Z -> kword. exact (ZToWord sz). Defined.
Definition riscvZdivu(x y: Z): Z. exact (if y =? 0 then 2 ^ width - 1 else Z.div x y). Defined.
Definition riscvZdivs(x y: Z): Z. exact (if (x =? - 2 ^ (width - 1)) && (y =? - 1) then x
    else if y =? 0 then - 1 else Z.quot x y). Defined.
Definition riscvZmodu(x y: Z): Z. exact (if y =? 0 then x else Z.modulo x y). Defined.
Definition riscvZmods(x y: Z): Z. exact (if y =? 0 then x else Z.rem x y). Defined.
Instance word : word.word width. exact ({|
    rep := kword;
    unsigned := kunsigned;
    signed := ksigned;
    of_Z := kofZ;

    add := @wplus sz;
    sub := @wminus sz;
    opp := @wneg sz;

    or  := @wor sz;
    and := @wand sz;
    xor := @wxor sz;
    not := @wnot sz;

     
    ndn x y := kofZ (Z.ldiff (kunsigned x) (kunsigned y));

    mul := @wmult sz;
    mulhss x y := kofZ (Z.mul (ksigned x) (ksigned y) / 2^width);
    mulhsu x y := kofZ (Z.mul (ksigned x) (kunsigned y) / 2^width);
    mulhuu x y := kofZ (Z.mul (kunsigned x) (kunsigned y) / 2^width);

    divu x y := kofZ (riscvZdivu (kunsigned x) (kunsigned y));
    divs x y := kofZ (riscvZdivs (ksigned x) (ksigned y));
    modu x y := kofZ (riscvZmodu (kunsigned x) (kunsigned y));
    mods x y := kofZ (riscvZmods (ksigned x) (ksigned y));

     
    slu x y := wlshift x (Z.to_nat ((kunsigned y) mod width));
    sru x y := wrshift x (Z.to_nat ((kunsigned y) mod width));
    srs x y := wrshifta x (Z.to_nat ((kunsigned y) mod width));

    eqb := @weqb sz;
    ltu x y := if wlt_dec x y then true else false;
    lts x y := if wslt_dec x y then true else false;

    sextend oldwidth z := kofZ ((kunsigned z + 2^(oldwidth-1)) mod 2^oldwidth - 2^(oldwidth-1));

  |}). Defined.

  Section __.
Import Coq.NArith.BinNat.
Import Kami.Lib.Word.
Local Open Scope N_scope.

    Lemma wordToN_WS b n w :
      wordToN (@WS b n w) = 2*wordToN w + N.b2n b.
Admitted.

    Lemma testbit_wordToN_oob n (a : word n) i (H: Logic.not (i < N.of_nat n)) :
      N.testbit (wordToN a) i = false.
Admitted.

    Lemma testbit_wordToN_bitwp_inbounds f n (a b : word n) i (H:i < N.of_nat n) :
      N.testbit (wordToN (bitwp f a b)) i = f (N.testbit (wordToN a) i) (N.testbit (wordToN b) i).
Admitted.
  End __.

  Lemma uwordToZ_bitwp f F (F_spec : forall x y i, Z.testbit (F x y) i = f (Z.testbit x i) (Z.testbit y i)) sz (x y : Word.word sz)
    : uwordToZ (bitwp f x y) = (F (uwordToZ x) (uwordToZ y)) mod 2 ^ Z.of_nat sz.
Admitted.

  Instance ok : word.ok word.
Admitted.
End WithWidth.
Arguments word : clear implicits.
Arguments ok : clear implicits.
Arguments kword : clear implicits.

Existing Instance word.
Existing Instance ok.

Open Scope Z_scope.

Section MkWords.
  Context {width : Z}.
  Context {width_cases : width = 32 \/ width = 64}.

  Lemma boundW: 0 < width.
Admitted.
Instance wordW: word.word width. exact (word width). Defined.
Instance wordWok: word.ok wordW. exact (ok width boundW). Defined.
Instance word8: word.word 8. exact (word 8). Defined.
Instance word8ok: word.ok word8. exact (ok 8 eq_refl). Defined.
End MkWords.

End KamiWord.

End processor_DOT_KamiWord_WRAPPED.
Module Export processor_DOT_KamiWord.
Module Export processor.
Module Export KamiWord.
Include processor_DOT_KamiWord_WRAPPED.KamiWord.
End KamiWord.

End processor.

End processor_DOT_KamiWord.
Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.
Module Export KamiProc.
Import Coq.ZArith.ZArith.
Import coqutil.Z.Lia.
Import Kami.Kami.
Import Kami.Ex.MemTypes.
Import Kami.Ex.SC.
Import Kami.Ex.IsaRv32.
Import Kami.Ex.SCMMInl.
Import processor.KamiWord.

Set Implicit Arguments.

Section Parametrized.
  Variables (addrSize maddrSize iaddrSize fifoSize instBytes dataBytes rfIdx: nat)
            (Hdb: {pdb & dataBytes = S pdb}).

  Variables (fetch: AbsFetch addrSize iaddrSize instBytes dataBytes)
            (dec: AbsDec addrSize instBytes dataBytes rfIdx)
            (exec: AbsExec addrSize instBytes dataBytes rfIdx)
            (ammio: AbsMMIO addrSize).

  Variable (procInit: ProcInit addrSize dataBytes rfIdx)
           (memInit: MemInit maddrSize).

  Definition pprocInl := scmmInl Hdb fetch dec exec ammio procInit memInit.

  Record pst :=
    mk { pc: Word.word addrSize;
         rf: Word.word rfIdx -> Word.word (dataBytes * BitsPerByte);
         pinit: bool;
         pgm: Word.word iaddrSize -> Word.word (instBytes * BitsPerByte);
         mem: Word.word maddrSize -> Word.word BitsPerByte
       }.
Definition pRegsToT (r: Kami.Semantics.RegsT): option pst.
exact ((mlet pcv: (Pc addrSize) <- r |> "pc" <| None;
    mlet rfv: (Vector (Data dataBytes) rfIdx) <- r |> "rf" <| None;
    mlet pinitv: Bool <- r |> "pinit" <| None;
    mlet pgmv: (Vector (Data instBytes) iaddrSize) <- r |> "pgm" <| None;
    mlet memv: (Vector (Bit BitsPerByte) maddrSize) <- r |> "mem" <| None;
    (Some {| pc := pcv; rf := rfv;
             pinit := pinitv; pgm := pgmv; mem := memv |}))%mapping).
Defined.

End Parametrized.
Definition width: Z.
exact (32).
Defined.
Local Notation nwidth := (Z.to_nat width).

Section PerInstAddr.
  Context {instrMemSizeLg memSizeLg: Z}.
  Hypothesis (Hiaddr: 3 <= instrMemSizeLg <= 30).

  Local Notation ninstrMemSizeLg := (Z.to_nat instrMemSizeLg).
  Local Notation nmemSizeLg := (Z.to_nat memSizeLg).

  Lemma width_inst_valid:
    nwidth = (2 + ninstrMemSizeLg + (nwidth - (2 + ninstrMemSizeLg)))%nat.
  Proof.
    change 2%nat with (Z.to_nat 2).
    rewrite <-Z2Nat.inj_add by blia.
    rewrite <-Z2Nat.inj_sub by blia.
    rewrite <-Z2Nat.inj_add by (unfold width; blia).
    f_equal; blia.
  Qed.
Definition procInit: ProcInit nwidth rv32DataBytes rv32RfIdx.
Admitted.
  Variables (memInit: MemInit nmemSizeLg)
            (rv32MMIO: AbsMMIO nwidth).

  Definition procInl :=
    pprocInl (existT _ _ eq_refl) (rv32Fetch _ _ width_inst_valid)
             (rv32Dec _) (rv32Exec _)
             rv32MMIO procInit memInit.
Definition proc: Kami.Syntax.Modules.
exact (projT1 procInl).
Defined.

  Definition hst := Kami.Semantics.RegsT.
  Definition KamiMachine := hst.

  Definition st :=
    @pst nwidth nmemSizeLg ninstrMemSizeLg rv32InstBytes rv32DataBytes rv32RfIdx.
Definition RegsToT (r: hst): option st.
exact (pRegsToT nwidth nmemSizeLg ninstrMemSizeLg rv32InstBytes rv32DataBytes rv32RfIdx r).
Defined.

End PerInstAddr.
Instance kami_AbsMMIO (memSizeLg: N): AbsMMIO (Z.to_nat width).
Admitted.

End KamiProc.
Module Export processor_DOT_Consistency_WRAPPED.
Module Export Consistency.
Import Coq.ZArith.BinInt.
Import Coq.Lists.List.
Import Kami.Lib.Word.
Import Kami.Semantics.
Import coqutil.Word.LittleEndian.
Import coqutil.Map.Interface.

Import processor.KamiWord.
Import riscv.Utility.Utility.
Import riscv.Platform.RiscvMachine.
Instance word: word 32.
exact (@KamiWord.wordW width).
Defined.

Section FetchOk.
  Fixpoint alignedXAddrsRange (base: nat) (n: nat): XAddrs (width := width) :=
    match n with
    | O => nil
    | S n' => $(base + n') :: alignedXAddrsRange base n'
    end.

  Context {mem: map.map word byte}.

  Variables instrMemSizeLg memSizeLg: Z.
  Hypothesis (HinstrMemBound: 3 <= instrMemSizeLg <= width - 2).
  Local Notation nwidth := (Z.to_nat width).
  Local Notation width_inst_valid := (width_inst_valid HinstrMemBound).
Definition instrMemSize: nat.
exact (NatLib.pow2 (2 + Z.to_nat instrMemSizeLg)).
Defined.
Definition pc_related (kpc rpc: kword width): Prop.
admit.
Defined.

  Definition AddrAligned (addr: kword width) :=
    split1 2 (nwidth - 2) addr = WO~0~0.

  Definition kamiXAddrs: XAddrs :=
    alignedXAddrsRange 0 instrMemSize.
Definition mem_related (kmem: kword memSizeLg -> kword 8)
             (rmem : mem): Prop.
admit.
Defined.

  Definition RiscvXAddrsSafe
             (kmemi: kword instrMemSizeLg -> kword width)
             (kmemd: kword memSizeLg -> kword 8)
             (xaddrs: XAddrs) :=
    forall rpc,
      isXAddr4 rpc xaddrs ->
      isXAddr4 rpc kamiXAddrs /\
      (AddrAligned rpc ->
       forall kpc,
         pc_related kpc rpc ->
         Kami.Ex.SC.combineBytes 4%nat rpc kmemd =
         kmemi (evalExpr (IsaRv32.rv32ToIAddr _ _ width_inst_valid _ kpc))).

  Hypothesis (Hkmem: 2 + instrMemSizeLg < memSizeLg <= width).

  Lemma fetch_ok:
    forall (kmemi: kword instrMemSizeLg -> kword width)
           (kmemd: kword memSizeLg -> kword 8)
           (kpc: kword width)
           (xaddrs: XAddrs)
           (Hxs: RiscvXAddrsSafe kmemi kmemd xaddrs)
           (rmemd: mem)
           (rpc: kword width),
      isXAddr4 (width := width) rpc xaddrs ->
      AddrAligned rpc ->
      pc_related kpc rpc ->
      mem_related kmemd rmemd ->
      exists (rinst: HList.tuple byte 4),
        Memory.load_bytes 4 rmemd rpc = Some rinst /\
        combine 4 rinst = kunsigned (kmemi (evalExpr (IsaRv32.rv32ToIAddr
                                                        _ _ width_inst_valid
                                                        _ kpc))).
Admitted.

End FetchOk.

Section DecExecOk.

  Context {Registers: map.map Z word}
          (Registers_ok : map.ok Registers).
Definition regs_related (krf: kword 5 -> kword width)
             (rrf: Registers): Prop.
admit.
Defined.

  Lemma regs_related_get:
    forall krf (Hkrf0: krf $0 = $0) rrf,
      regs_related krf rrf ->
      forall w z,
        Z.of_N (wordToN w) = z ->
        krf w =
        (if Z.eq_dec z 0 then kofZ 0
         else
           match map.get rrf z with
           | Some x => x
           | None => kofZ 0
           end).
admit.
Defined.

End DecExecOk.

End Consistency.
Module Export processor.
Module Export Consistency.
Include processor_DOT_Consistency_WRAPPED.Consistency.
End Consistency.
Import Coq.Strings.String.
Import Coq.ZArith.ZArith.
Import coqutil.Z.Lia.
Import Coq.Lists.List.
Import ListNotations.
Import Kami.Lib.Word.
Import Kami.Ex.IsaRv32.
Import riscv.Spec.Decode.
Import coqutil.Word.LittleEndian.
Import coqutil.Map.Interface.
Import coqutil.Tactics.Tactics.
Import coqutil.Tactics.rdelta.
Import processor.KamiWord.
Import riscv.Utility.Utility.
Import riscv.Spec.Primitives.
Import riscv.Spec.Machine.
Import riscv.Platform.Run.
Import riscv.Utility.MkMachineWidth.
Import riscv.Utility.Monads.
Import riscv.Platform.MinimalMMIO.
Import riscv.Platform.MetricMinimalMMIO.
Import riscv.Platform.FE310ExtSpec.
Import Kami.Syntax.
Import Kami.Semantics.
Import Kami.Tactics.
Import Kami.Ex.MemTypes.
Import Kami.Ex.SC.
Import Kami.Ex.SCMMInv.
Import processor.Consistency.

  Lemma bitSlice_range_ex:
    forall z n m,
      0 <= n <= m -> 0 <= bitSlice z n m < 2 ^ (m - n).
Admitted.

  Lemma unsigned_split1_as_bitSlice a b x :
    Z.of_N (wordToN (split1 a b x)) =
    bitSlice (Z.of_N (wordToN x)) 0 (Z.of_nat a).
Admitted.

  Lemma unsigned_split2_as_bitSlice a b x :
    Z.of_N (wordToN (split2 a b x)) =
    bitSlice (Z.of_N (wordToN x)) (Z.of_nat a) (Z.of_nat a + Z.of_nat b).
Admitted.

  Lemma unsigned_split2_split1_as_bitSlice a b c x :
    Z.of_N (wordToN (split2 a b (split1 (a+b) c x))) =
    bitSlice (Z.of_N (wordToN x)) (Z.of_nat a) (Z.of_nat a + Z.of_nat b).
Admitted.

  Lemma kami_evalSignExtendTrunc:
    forall {a} (w: Word.word a) b,
      (a <= b)%nat ->
      evalSignExtendTrunc b w =
      ZToWord b (signExtend (Z.of_nat a) (Z.of_N (wordToN w))).
Admitted.

  Lemma kami_evalZeroExtendTrunc_32:
    forall w, evalZeroExtendTrunc 32 w = w.
Admitted.

  Lemma kami_evalSignExtendTrunc_32:
    forall w, evalSignExtendTrunc 32 w = w.
Admitted.

Section Equiv.
  Local Hint Mode word.word - : typeclass_instances.

  Context {Registers: map.map Z word}
          {mem: map.map word byte}.
  Local Notation RiscvMachine := MetricRiscvMachine.

  Variable (instrMemSizeLg memSizeLg: Z).
  Hypotheses (Hinstr1: 3 <= instrMemSizeLg)
             (Hinstr2: instrMemSizeLg <= width - 2)
             (Hkmem1: 2 + instrMemSizeLg < memSizeLg)
             (Hkmem2: memSizeLg <= width)

             (Hkmemdisj: memSizeLg <= 16).
  Local Notation Hinstr := (conj Hinstr1 Hinstr2).

  Variable (memInit: Vec (ConstT (Bit BitsPerByte)) (Z.to_nat memSizeLg)).
  Definition kamiMemInit := ConstVector memInit.
  Local Definition kamiProc :=
    @KamiProc.proc instrMemSizeLg memSizeLg Hinstr kamiMemInit (kami_AbsMMIO (Z.to_N memSizeLg)).
  Local Definition kamiStMk := @KamiProc.mk (Z.to_nat width)
                                            (Z.to_nat memSizeLg)
                                            (Z.to_nat instrMemSizeLg)
                                            rv32InstBytes rv32DataBytes rv32RfIdx.
  Local Notation kamiXAddrs := (kamiXAddrs instrMemSizeLg).
  Local Notation rv32Fetch :=
    (rv32Fetch (Z.to_nat width)
               (Z.to_nat instrMemSizeLg)
               (width_inst_valid Hinstr)).
  Local Hint Resolve (kami_AbsMMIO (Z.to_N memSizeLg)): typeclass_instances.

  Local Notation RiscvXAddrsSafe :=
    (RiscvXAddrsSafe instrMemSizeLg memSizeLg (conj Hinstr1 Hinstr2)).
Definition iset: InstructionSet.
exact (RV32I).
Defined.

  Local Notation mcomp_sat_unit m initialL post :=
    (mcomp_sat m initialL (fun (_: unit) => post)).

  Definition Event: Type := (string * word * word).

  Inductive events_related: Event -> LogItem -> Prop :=
  | relate_MMInput: forall addr v,
      events_related ("ld"%string, addr, v) ((map.empty, "MMIOREAD"%string, [addr]), (map.empty, [v]))
  | relate_MMOutput: forall addr v,
      events_related ("st"%string, addr, v) ((map.empty, "MMIOWRITE"%string, [addr; v]), (map.empty, [])).

  Inductive traces_related: list Event -> list LogItem -> Prop :=
  | relate_nil:
      traces_related nil nil
  | relate_cons: forall e e' t t',
      events_related e e' ->
      traces_related t t' ->
      traces_related (e :: t) (e' :: t').

  Definition pc_related_and_valid (kpc rpc: kword width) :=
    AddrAligned rpc /\ pc_related kpc rpc.

  Inductive states_related: KamiMachine * list Event -> RiscvMachine -> Prop :=
  | relate_states:
      forall t t' m riscvXAddrs kpc krf rrf rpc nrpc pinit instrMem kdataMem rdataMem metrics,
        traces_related t t' ->
        KamiProc.RegsToT m = Some (kamiStMk kpc krf pinit instrMem kdataMem) ->
        (pinit = false -> riscvXAddrs = kamiXAddrs) ->
        (pinit = true -> RiscvXAddrsSafe instrMem kdataMem riscvXAddrs) ->
        pc_related_and_valid kpc rpc ->
        nrpc = word.add rpc (word.of_Z 4) ->
        regs_related krf rrf ->
        mem_related _ kdataMem rdataMem ->
        states_related
          (m, t) {| getMachine := {| RiscvMachine.getRegs := rrf;
                                     RiscvMachine.getPc := rpc;
                                     RiscvMachine.getNextPc := nrpc;
                                     RiscvMachine.getMem := rdataMem;
                                     RiscvMachine.getXAddrs := riscvXAddrs;
                                     RiscvMachine.getLog := t'; |};
                    getMetrics := metrics; |}.

  Inductive KamiLabelR: Kami.Semantics.LabelT -> list Event -> Prop :=
  | KamiSilent:
      forall klbl,
        klbl.(calls) = FMap.M.empty _ ->
        KamiLabelR klbl nil
  | KamiMMIO:
      forall klbl argV retV e,
        klbl.(calls) =
        FMap.M.add
          "mmioExec"%string
          (existT SignT {| arg := Struct (RqFromProc (Z.to_nat width) rv32DataBytes);
                           ret := Struct (RsToProc rv32DataBytes) |} (argV, retV))
          (FMap.M.empty _) ->
        e = (if argV (Fin.FS Fin.F1)
             then ("st"%string, (argV Fin.F1), (argV (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))
             else ("ld"%string, (argV Fin.F1), (retV Fin.F1))) ->
        KamiLabelR klbl [e].

  Lemma is_mmio_spec:
    forall a, evalExpr (isMMIO type a) = true <-> 2 ^ memSizeLg <= kunsigned a.
Admitted.

  Lemma mem_related_load_bytes_Some:
    forall kmem rmem,
      mem_related memSizeLg kmem rmem ->
      forall sz addr bs,
        sz <> O ->
        Memory.load_bytes sz rmem addr = Some bs ->
        kunsigned addr < Z.pow 2 memSizeLg.
Admitted.

  Inductive PHide: Prop -> Prop :=
  | PHidden: forall P: Prop, P -> PHide P.

  Ltac mcomp_step_in HR :=
    progress
      (let ucode := match type of HR with mcomp_sat ?u ?s ?p => u end in
       let state := match type of HR with mcomp_sat ?u ?s ?p => s end in
       let post := match type of HR with mcomp_sat ?u ?s ?p => p end in
       (let uc := fresh "uc" in set ucode as uc in HR; hnf in uc; subst uc);
       let ucode := match type of HR with mcomp_sat ?u ?s ?p => u end in
       change (mcomp_sat ucode state post) in HR;
       match ucode with
       | free.act ?a ?k =>
         let pf := constr:(HR : free.interp interp_action ucode state post) in
         (let HRR := fresh in pose proof pf as HRR; clear HR; rename HRR into HR);
         remember k as kV;

         let interp_action := eval cbv delta [interp_action MinimalMMIO.interpret_action] in
         interp_action in
         let TR := eval cbn iota beta delta [
                     fst snd
                     getMetrics getMachine
                     translate
                     getRegs getPc getNextPc getMem getXAddrs getLog]
         in (interp_action a state (fun x state' => mcomp_sat (kV x) state' post)) in
             change TR in HR; subst kV
       | free.ret ?v => change (post v state) in HR
       | _ => idtac
       end).

  Ltac destruct_if_by_contradiction :=
    let c := match goal with
             | H : context [if ?c then _ else _] |- _ => c
             | H := context [if ?c then _ else _] |- _ => c
             | |- if ?c then _ else _ => c
             end in
    destruct c; try (exfalso; contradiction); [].

  Ltac zcstP x :=
    let x := rdelta x in
    let t := isZcst x in
    constr_eq t true.
  Ltac natcstP x :=
    let x := rdelta x in
    let t := isnatcst x in
    constr_eq t true.

  Ltac eval2 op arg1P arg2P :=
    repeat match goal with
           | H : context G [op ?x ?y] |- _ =>
             arg1P x; arg2P y;
             let z := eval cbv in (op x y) in
             let e := context G [z] in
             change e in H
           | H := context G [op ?x ?y] |- _ =>
             arg1P x; arg2P y;
             let z := eval cbv in (op x y) in
             let e := context G [z] in
             change e in (value of H)
           | |- context G [op ?x ?y] =>
             arg1P x; arg2P y;
             let z := eval cbv in (op x y) in
             let e := context G [z] in
             change e
           end.

  Ltac t  :=
    match goal with
    | H : ?LHS = let x := ?v in ?C |- _ =>
        change (let x := v in LHS = C) in H
    | H := let x := ?v in @?C x |- _ =>
        let x := fresh x in pose v as x;
        let C := eval cbv beta in (C x) in
        change C in (value of H)
    | H: let x := ?v in @?C x |- _ =>
        let x := fresh x in pose v as x;
        let C := eval cbv beta in (C x) in
        change C in H
    | |- let x := _ in _ => intro
    | x := ?y |- _ => first [is_var y|is_const y|is_ind y|is_constructor y]; subst x
    | H : context G [ Z.of_nat ?n ] |- _ =>
        natcstP n;
        let nn := eval cbv in (Z.of_nat n) in
        let e := context G [nn] in
        change e in H
    | _ => progress eval2 Z.add zcstP zcstP
    | _ => progress eval2 Z.eqb zcstP zcstP
    | H: ?t = ?t -> _ |- _ => specialize (H eq_refl)
    | H: mcomp_sat _ _ _ |- _ => mcomp_step_in H
    | H: exists _, _ |- _ => destruct H
    | H: _ /\ _ |- _ => destruct H
    | _ => destruct_if_by_contradiction
    end.

  Ltac r :=
    match goal with
    | [H: context G [let x := ?y in @?z x] |- _] =>
      let x' := fresh x in
      pose y as x';
      let zy := eval cbv beta in (z x') in
      let h' := context G [zy] in
      change h' in H
    | [H: Memory.load_bytes _ _ _ = Some _, G: context [Memory.load_bytes] |- _] =>
      rewrite H in G
    | _ =>
      progress cbn iota beta delta [when free.bind] in *
    | [H: mcomp_sat _ _ _ |- _] =>
      match type of H with
      | context G [when ?b _] => destr b
      | context G [if ?b then _ else _] => destr b
      end
    | [H: combine ?n ?rinst = _, G: context [combine ?n ?rinst] |- _] =>
      setoid_rewrite H in G
    | [H: False |- _] => case H
    | [H: _ |- _] =>
      progress
        (cbv beta delta [load store] in H;
         cbn beta iota delta [
           load store fst snd translate
           withMetrics updateMetrics getMachine getMetrics getRegs getPc getNextPc getMem getXAddrs getLog withRegs withPc withNextPc withMem withXAddrs withLog withLogItem withLogItems
           RiscvMachine.withRegs RiscvMachine.withPc RiscvMachine.withNextPc RiscvMachine.withMem RiscvMachine.withXAddrs RiscvMachine.withLog RiscvMachine.withLogItem RiscvMachine.withLogItems] in H)
    end.

  Ltac rt := repeat (r || t).

  Ltac regs_get_red H :=
    repeat
      (try (erewrite <-regs_related_get
              with (w:= split2 15 5 (split1 (15 + 5) 12 _)) in H;
            [|eauto; fail|eassumption|eapply unsigned_split2_split1_as_bitSlice; fail]);
       try (erewrite <-regs_related_get
              with (w:= split2 20 5 (split1 (20 + 5) 7 _)) in H;
            [|eauto; fail|eassumption|eapply unsigned_split2_split1_as_bitSlice; fail])).

  Ltac kinvert_more :=
    kinvert;
    try (repeat
           match goal with
           | [H: Semantics.annot ?klbl = Some _ |- _] => rewrite H in *
           | [H: (_ :: _)%struct = (_ :: _)%struct |- _] =>
             inversion H; subst; clear H
           end; discriminate).

  Ltac invertActionRep_nosimpl :=
    repeat
      match goal with
      | H: (_ :: _)%struct = (_ :: _)%struct |- _ => CommonTactics.inv H
      | H: SemAction _ _ _ _ _ |- _ =>
        apply inversionSemAction in H; CommonTactics.dest
      | H: if ?c
           then SemAction _ _ _ _ _ /\ _ /\ _ /\ _
           else SemAction _ _ _ _ _ /\ _ /\ _ /\ _ |- _ =>
        repeat autounfold with MethDefs;
        match goal with
        | H: if ?c
             then SemAction _ _ _ _ _ /\ _ /\ _ /\ _
             else SemAction _ _ _ _ _ /\ _ /\ _ /\ _ |- _ =>
          let ic := fresh "ic" in
          remember c as ic; destruct ic; CommonTactics.dest
        end
      end.

  Ltac kinv_action_dest_nosimpl :=
    kinv_red; invertActionRep_nosimpl.

  Ltac block_subst vn :=
    match goal with
    | [H: vn = ?v |- _] =>
      assert (PHide (vn = v)) by (constructor; assumption); clear H
    end.

  Ltac red_regmap :=
    try match goal with
        | [H: scmm_inv _ _ _ _ |- _] => inversion H
        end;
    cbv [RegsToT pRegsToT] in *;
    kregmap_red; kinv_red.

  Ltac red_trivial_conds :=
    repeat
      match goal with
      | [H: evalExpr (Var type (SyntaxKind Bool) ?b) = _ |- _] => simpl in H; subst b
      end.

  Ltac cleanup_trivial :=
    cbv [Semantics.annot Semantics.defs Semantics.calls] in *;
    repeat
      match goal with
      | [H: FMap.M.empty _ = FMap.M.empty _ |- _] => clear H
      | [H: true = false -> _ |- _] => clear H
      | [H: false = true -> _ |- _] => clear H
      | [H: Some _ = Some _ |- _] => inversion H; subst; clear H
      | [H: {| pc := _ |} = kamiStMk _ _ _ _ _ |- _] => inversion H; subst; clear H
      | [H: true = true -> _ |- _] => specialize (H eq_refl)
      | [H: context [FMap.M.Map.In] |- _] => clear H
      end.

  Ltac unblock_subst vn :=
    match goal with
    | [H: PHide (vn = _) |- _] => inversion_clear H
    end.

  Ltac eval_kami_fetch :=
    try match goal with
        | [H: pc_related_and_valid _ _ |- _] => destruct H
        end;
    try match goal with
        | [H: isXAddr4 _ _ |- _] =>
          let Hxaddr := fresh "Hxaddr" in
          pose proof H as Hxaddr;
          eapply fetch_ok in H; try eassumption; [|blia];
          let rinst := fresh "rinst" in
          destruct H as (rinst & ? & ?)
        end.

  Ltac kami_cbn_all :=
    cbn [evalExpr evalUniBool evalBinBool evalBinBit
                  evalConstT getDefaultConst isEq Data BitsPerByte Nat.mul Nat.add Nat.sub
                  AlignInstT DstE DstK DstT ExecT f3Lb f3Lbu f3Lh f3Lhu f3Lw getFunct3E getFunct6E getFunct7E getOffsetIE getOffsetSBE getOffsetSE getOffsetShamtE getHiShamtE getOffsetUE getOffsetUJE getOpcodeE getRdE getRs1E getRs1ValueE getRs2E getRs2ValueE IsMMIOE IsMMIOT LdAddrCalcT LdAddrE LdAddrK LdAddrT LdDstE LdDstK LdDstT LdSrcE LdSrcK LdSrcT LdTypeE LdTypeK LdTypeT LdValCalcT MemInit memInst memOp mm mmioExec nextPc NextPcT OpcodeE OpcodeK OpcodeT opLd opNm opSt OptypeE OptypeK OptypeT Pc pinst procInitDefault procInst RqFromProc RsToProc rv32AlignInst rv32CalcLdAddr rv32CalcStAddr rv32CalcStByteEn rv32DataBytes rv32GetDst rv32GetLdAddr rv32GetLdDst rv32GetLdSrc rv32GetLdType rv32GetOptype rv32GetSrc1 rv32GetSrc2 rv32GetStAddr rv32GetStSrc rv32GetStVSrc rv32InstBytes rv32RfIdx scmm Src1E Src1K Src1T Src2E Src2K Src2T StAddrCalcT StByteEnCalcT StAddrE StAddrK StAddrT StateE StateK StateT StSrcE StSrcK StSrcT StVSrcE StVSrcK StVSrcT] in *.

  Ltac kami_cbn_hint H :=
    let t := type of H in
    let tc :=
      eval cbn [evalExpr evalUniBool evalBinBool evalBinBit
                evalConstT getDefaultConst isEq Data BitsPerByte Nat.mul Nat.add Nat.sub
                AlignInstT DstE DstK DstT ExecT f3Lb f3Lbu f3Lh f3Lhu f3Lw getFunct3E getFunct6E getFunct7E getOffsetIE getOffsetSBE getOffsetSE getOffsetShamtE getHiShamtE getOffsetUE getOffsetUJE getOpcodeE getRdE getRs1E getRs1ValueE getRs2E getRs2ValueE IsMMIOE IsMMIOT LdAddrCalcT LdAddrE LdAddrK LdAddrT LdDstE LdDstK LdDstT LdSrcE LdSrcK LdSrcT LdTypeE LdTypeK LdTypeT LdValCalcT MemInit memInst memOp mm mmioExec nextPc NextPcT OpcodeE OpcodeK OpcodeT opLd opNm opSt OptypeE OptypeK OptypeT Pc pinst procInitDefault procInst RqFromProc RsToProc rv32AlignInst rv32CalcLdAddr rv32CalcStAddr rv32CalcStByteEn rv32DataBytes rv32GetDst rv32GetLdAddr rv32GetLdDst rv32GetLdSrc rv32GetLdType rv32GetOptype rv32GetSrc1 rv32GetSrc2 rv32GetStAddr rv32GetStSrc rv32GetStVSrc rv32InstBytes rv32RfIdx scmm Src1E Src1K Src1T Src2E Src2K Src2T StAddrCalcT StByteEnCalcT StAddrE StAddrK StAddrT StateE StateK StateT StSrcE StSrcK StSrcT StVSrcE StVSrcK StVSrcT]
    in t in
    let Ht := fresh "H" in
    assert (Ht: t = tc) by reflexivity;
    rewrite Ht in H; clear Ht.

  Ltac kami_cbn_hint_func H func :=
    let t := type of H in
    let tc :=
      eval cbn [evalExpr evalUniBool evalBinBool evalBinBit
                evalConstT getDefaultConst isEq Data BitsPerByte Nat.mul Nat.add Nat.sub
                func

                AlignInstT DstE DstK DstT ExecT f3Lb f3Lbu f3Lh f3Lhu f3Lw getFunct3E getFunct6E getFunct7E getOffsetIE getOffsetSBE getOffsetSE getOffsetShamtE getHiShamtE getOffsetUE getOffsetUJE getOpcodeE getRdE getRs1E getRs1ValueE getRs2E getRs2ValueE IsMMIOE IsMMIOT LdAddrCalcT LdAddrE LdAddrK LdAddrT LdDstE LdDstK LdDstT LdSrcE LdSrcK LdSrcT LdTypeE LdTypeK LdTypeT LdValCalcT MemInit memInst memOp mm mmioExec nextPc NextPcT OpcodeE OpcodeK OpcodeT opLd opNm opSt OptypeE OptypeK OptypeT Pc pinst procInitDefault procInst RqFromProc RsToProc rv32AlignInst rv32CalcLdAddr rv32CalcStAddr rv32CalcStByteEn rv32DataBytes rv32GetDst rv32GetLdAddr rv32GetLdDst rv32GetLdSrc rv32GetLdType rv32GetOptype rv32GetSrc1 rv32GetSrc2 rv32GetStAddr rv32GetStSrc rv32GetStVSrc rv32InstBytes rv32RfIdx scmm Src1E Src1K Src1T Src2E Src2K Src2T StAddrCalcT StByteEnCalcT StAddrE StAddrK StAddrT StateE StateK StateT StSrcE StSrcK StSrcT StVSrcE StVSrcK StVSrcT]
    in t in
    let Ht := fresh "H" in
    assert (Ht: t = tc) by reflexivity;
    rewrite Ht in H; clear Ht.

  Ltac weq_to_Zeqb :=

    repeat match goal with
           | |- context G [if ?x then ?a else ?b] =>
             let e := context G [@bool_rect (fun _ => _) a b x] in
             change e
           | |- context G [if ?x then ?a else ?b] =>
             let e := context G [@sumbool_rect _ _ (fun _ => _) (fun _ => a) (fun _ => b) x] in
             change e
           | H : context G [if ?x then ?a else ?b] |- _ =>
             let e := context G [@bool_rect (fun _ => _) a b x] in
             change e in H
           | H : context G [if ?x then ?a else ?b] |- _ =>
             let e := context G [@sumbool_rect _ _ (fun _ => _) (fun _ => a) (fun _ => b) x] in
             change e in H
           end;
    repeat match goal with
           | [H: _ |- _] =>
             progress repeat rewrite ?sumbool_rect_bool_weq, <-?unsigned_eqb in H
           end;
    repeat rewrite ?sumbool_rect_bool_weq, <-?unsigned_eqb;
    cbv [bool_rect] in *;

    progress
      repeat (match goal with
              | [ |- context G [Z.of_N (@wordToN ?n ?x)] ] =>
                let nn := eval cbv in (Z.of_nat n) in
                let e := context G [@kunsigned nn x] in
                change e
              | [ |- context G [kunsigned (@natToWord ?n ?x)] ] =>
                let xx := eval cbv in (Z.of_nat x) in
                let e := context G [xx] in
                change e
              | [ |- context G [kunsigned (@WS ?b ?n ?t)] ] =>
                let xx := eval cbv in (kunsigned (width:= Z.of_nat (S n)) (WS b t)) in
                let e := context G [xx] in
                change e
              | [H: context G [Z.of_N (@wordToN ?n ?x)] |- _] =>
                let nn := eval cbv in (Z.of_nat n) in
                let e := context G [@kunsigned nn x] in
                change e in H
              | [H: context G [kunsigned (@natToWord ?n ?x)] |- _] =>
                let xx := eval cbv in (Z.of_nat x) in
                let e := context G [xx] in
                change e in H
              | [H: context G [kunsigned (@WS ?b ?n ?t)] |- _] =>
                let xx := eval cbv in (kunsigned (width:= Z.of_nat (S n)) (WS b t)) in
                let e := context G [xx] in
                change e in H
              end).

  Ltac dest_Zeqb :=
    progress
      repeat match goal with
             | [ |- context G [if Z.eqb ?x ?y then ?a else ?b] ] =>
               destruct (Z.eqb_spec x y) in *
             | [H : context G [if Z.eqb ?x ?y then ?a else ?b] |- _] =>
               destruct (Z.eqb_spec x y) in *

             | [H : context G [if (Z.eqb ?x ?y && _)%bool then _ else _] |- _] =>
               destruct (Z.eqb_spec x y)
             | [H : context G [if (_ && Z.eqb ?x ?y)%bool then _ else _] |- _] =>
               destruct (Z.eqb_spec x y)

             | [H : context G [if (Z.eqb ?x ?y && _ && _)%bool then _ else _] |- _] =>
               destruct (Z.eqb_spec x y)
             | [H : context G [if (_ && Z.eqb ?x ?y && _)%bool then _ else _] |- _] =>
               destruct (Z.eqb_spec x y)
             | [H : context G [if (_ && _ && Z.eqb ?x ?y)%bool then _ else _] |- _] =>
               destruct (Z.eqb_spec x y)

             | [H: ?x = ?a, G: ?x = ?b |- _] =>
               let aa := eval cbv in a in
               let bb := eval cbv in b in
               let t := isZcst aa in constr_eq t true;
               let t := isZcst bb in constr_eq t true;
               assert_fails (constr_eq aa bb);
               exfalso; remember x; clear -H G;
               cbv in H; cbv in G; rewrite H in G; inversion G
             | [H: ?x = ?a, G: ?x <> ?b |- _] =>
               let aa := eval cbv in a in
               let bb := eval cbv in b in
               let t := isZcst aa in constr_eq t true;
               let t := isZcst bb in constr_eq t true;
               assert_fails (constr_eq aa bb);
               clear G
             end.

  Ltac simpl_bit_manip :=
    cbv [evalUniBit] in *;
    repeat match goal with
           | [H: context [evalZeroExtendTrunc _ _] |- _] =>
             rewrite kami_evalZeroExtendTrunc_32 in H
           | [H: context [evalSignExtendTrunc _ _] |- _] =>
             rewrite kami_evalSignExtendTrunc_32 in H
           end;
    repeat match goal with
           | [H: context [evalSignExtendTrunc _ _] |- _] =>
             rewrite kami_evalSignExtendTrunc in H by (compute; blia)
           end;
    cbv [kunsigned] in *;
    repeat match goal with
           | [H: context [Z.to_nat ?z] |- _] =>
             let t := isZcst z in
             constr_eq t true;
             let n := eval cbv in (Z.to_nat z) in
                 change (Z.to_nat z) with n in H
           end;
    repeat match goal with
           | [H: context [Z.of_N (wordToN (split2 ?va ?vb (split1 _ _ ?w)))] |- _] =>
             is_var w; rewrite unsigned_split2_split1_as_bitSlice
                         with (a:= va) (b:= vb) (x:= w) in H
           | [H: context [Z.of_N (wordToN (split1 ?va ?vb ?w))] |- _] =>
             is_var w; rewrite unsigned_split1_as_bitSlice
                         with (a:= va) (b:= vb) (x:= w) in H
           | [H: context [Z.of_N (wordToN (split2 ?va ?vb ?w))] |- _] =>
             is_var w; rewrite unsigned_split2_as_bitSlice
                         with (a:= va) (b:= vb) (x:= w) in H
           end;
    repeat match goal with
           | H : context [ Z.of_nat ?n ] |- _ =>
             natcstP n;
             let nn := eval cbv in (Z.of_nat n) in
             change (Z.of_nat n) with nn in H
           end;
    repeat match goal with
           | H : context [ Z.add ?x ?y ] |- _ =>
             let t := isZcst x in constr_eq t true;
             let t := isZcst y in constr_eq t true;
             let z := eval cbv in (Z.add x y) in
             change (Z.add x y) with z in H
           end;
    repeat match goal with
           | H : context [ Z.of_N (@wordToN ?w ?x) ] |- _ =>
             change (Z.of_N (@wordToN w x)) with (@kunsigned 32 x) in H
           end.

  Ltac eval_decode :=
    idtac "KamiRiscv: evaluating [decode] in riscv-coq; this might take several minutes...";
    let dec := fresh "dec" in
    let Hdec := fresh "Hdec" in
    match goal with
    | H : context[decode ?a ?b] |- _ => remember (decode a b) as dec eqn:Hdec in H
    end;
    cbv beta iota delta [decode] in Hdec;
    repeat
      match goal with
      | [Hbs: bitSlice _ _ _ = _ |- _] => rewrite !Hbs in Hdec
      end;
    repeat
      (match goal with
       | _ => progress cbn iota beta delta
                       [iset andb
                             Z.gtb Z.eqb Pos.eqb
                             BinInt.Z.of_nat Pos.of_succ_nat
                             BinInt.Z.compare Pos.compare Pos.compare_cont
                             Datatypes.length nth

                             bitwidth decode funct12_EBREAK funct12_ECALL funct12_MRET funct12_SRET funct12_URET funct12_WFI funct2_FMADD_S funct3_ADD funct3_ADDI funct3_ADDIW funct3_ADDW funct3_AMOD funct3_AMOW funct3_AND funct3_ANDI funct3_BEQ funct3_BGE funct3_BGEU funct3_BLT funct3_BLTU funct3_BNE funct3_CSRRC funct3_CSRRCI funct3_CSRRS funct3_CSRRSI funct3_CSRRW funct3_CSRRWI funct3_DIV funct3_DIVU funct3_DIVUW funct3_DIVW funct3_FCLASS_S funct3_FENCE funct3_FENCE_I funct3_FEQ_S funct3_FLE_S funct3_FLT_S funct3_FLW funct3_FMAX_S funct3_FMIN_S funct3_FMV_X_W funct3_FSGNJN_S funct3_FSGNJ_S funct3_FSGNJX_S funct3_FSW funct3_LB funct3_LBU funct3_LD funct3_LH funct3_LHU funct3_LW funct3_LWU funct3_MUL funct3_MULH funct3_MULHSU funct3_MULHU funct3_MULW funct3_OR funct3_ORI funct3_PRIV funct3_REM funct3_REMU funct3_REMUW funct3_REMW funct3_SB funct3_SD funct3_SH funct3_SLL funct3_SLLI funct3_SLLIW funct3_SLLW funct3_SLT funct3_SLTI funct3_SLTIU funct3_SLTU funct3_SRA funct3_SRAI funct3_SRAIW funct3_SRAW funct3_SRL funct3_SRLI funct3_SRLIW funct3_SRLW funct3_SUB funct3_SUBW funct3_SW funct3_XOR funct3_XORI funct5_AMOADD funct5_AMOAND funct5_AMOMAX funct5_AMOMAXU funct5_AMOMIN funct5_AMOMINU funct5_AMOOR funct5_AMOSWAP funct5_AMOXOR funct5_LR funct5_SC funct6_SLLI funct6_SRAI funct6_SRLI funct7_ADD funct7_ADDW funct7_AND funct7_DIV funct7_DIVU funct7_DIVUW funct7_DIVW funct7_FADD_S funct7_FCLASS_S funct7_FCVT_S_W funct7_FCVT_W_S funct7_FDIV_S funct7_FEQ_S funct7_FMIN_S funct7_FMUL_S funct7_FMV_W_X funct7_FMV_X_W funct7_FSGNJ_S funct7_FSQRT_S funct7_FSUB_S funct7_MUL funct7_MULH funct7_MULHSU funct7_MULHU funct7_MULW funct7_OR funct7_REM funct7_REMU funct7_REMUW funct7_REMW funct7_SFENCE_VMA funct7_SLL funct7_SLLIW funct7_SLLW funct7_SLT funct7_SLTU funct7_SRA funct7_SRAIW funct7_SRAW funct7_SRL funct7_SRLIW funct7_SRLW funct7_SUB funct7_SUBW funct7_XOR isValidA isValidA64 isValidCSR isValidF isValidF64 isValidI isValidI64 isValidM isValidM64 opcode_AMO opcode_AUIPC opcode_BRANCH opcode_JAL opcode_JALR opcode_LOAD opcode_LOAD_FP opcode_LUI opcode_MADD opcode_MISC_MEM opcode_MSUB opcode_NMADD opcode_NMSUB opcode_OP opcode_OP_32 opcode_OP_FP opcode_OP_IMM opcode_OP_IMM_32 opcode_STORE opcode_STORE_FP opcode_SYSTEM rs2_FCVT_L_S rs2_FCVT_LU_S rs2_FCVT_W_S rs2_FCVT_WU_S supportsA supportsF supportsM] in *
       | x := @nil _ |- _ => subst x
       | _ => t
       end).

  Ltac eval_decodeI decodeI :=
    try cbn in decodeI;
    cbv [funct12_EBREAK funct12_ECALL funct12_MRET funct12_SRET funct12_URET funct12_WFI funct2_FMADD_S funct3_ADD funct3_ADDI funct3_ADDIW funct3_ADDW funct3_AMOD funct3_AMOW funct3_AND funct3_ANDI funct3_BEQ funct3_BGE funct3_BGEU funct3_BLT funct3_BLTU funct3_BNE funct3_CSRRC funct3_CSRRCI funct3_CSRRS funct3_CSRRSI funct3_CSRRW funct3_CSRRWI funct3_DIV funct3_DIVU funct3_DIVUW funct3_DIVW funct3_FCLASS_S funct3_FENCE funct3_FENCE_I funct3_FEQ_S funct3_FLE_S funct3_FLT_S funct3_FLW funct3_FMAX_S funct3_FMIN_S funct3_FMV_X_W funct3_FSGNJN_S funct3_FSGNJ_S funct3_FSGNJX_S funct3_FSW funct3_LB funct3_LBU funct3_LD funct3_LH funct3_LHU funct3_LW funct3_LWU funct3_MUL funct3_MULH funct3_MULHSU funct3_MULHU funct3_MULW funct3_OR funct3_ORI funct3_PRIV funct3_REM funct3_REMU funct3_REMUW funct3_REMW funct3_SB funct3_SD funct3_SH funct3_SLL funct3_SLLI funct3_SLLIW funct3_SLLW funct3_SLT funct3_SLTI funct3_SLTIU funct3_SLTU funct3_SRA funct3_SRAI funct3_SRAIW funct3_SRAW funct3_SRL funct3_SRLI funct3_SRLIW funct3_SRLW funct3_SUB funct3_SUBW funct3_SW funct3_XOR funct3_XORI funct5_AMOADD funct5_AMOAND funct5_AMOMAX funct5_AMOMAXU funct5_AMOMIN funct5_AMOMINU funct5_AMOOR funct5_AMOSWAP funct5_AMOXOR funct5_LR funct5_SC funct6_SLLI funct6_SRAI funct6_SRLI funct7_ADD funct7_ADDW funct7_AND funct7_DIV funct7_DIVU funct7_DIVUW funct7_DIVW funct7_FADD_S funct7_FCLASS_S funct7_FCVT_S_W funct7_FCVT_W_S funct7_FDIV_S funct7_FEQ_S funct7_FMIN_S funct7_FMUL_S funct7_FMV_W_X funct7_FMV_X_W funct7_FSGNJ_S funct7_FSQRT_S funct7_FSUB_S funct7_MUL funct7_MULH funct7_MULHSU funct7_MULHU funct7_MULW funct7_OR funct7_REM funct7_REMU funct7_REMUW funct7_REMW funct7_SFENCE_VMA funct7_SLL funct7_SLLIW funct7_SLLW funct7_SLT funct7_SLTU funct7_SRA funct7_SRAIW funct7_SRAW funct7_SRL funct7_SRLIW funct7_SRLW funct7_SUB funct7_SUBW funct7_XOR isValidA isValidA64 isValidCSR isValidF isValidF64 isValidI isValidI64 isValidM isValidM64 opcode_AMO opcode_AUIPC opcode_BRANCH opcode_JAL opcode_JALR opcode_LOAD opcode_LOAD_FP opcode_LUI opcode_MADD opcode_MISC_MEM opcode_MSUB opcode_NMADD opcode_NMSUB opcode_OP opcode_OP_32 opcode_OP_FP opcode_OP_IMM opcode_OP_IMM_32 opcode_STORE opcode_STORE_FP opcode_SYSTEM rs2_FCVT_L_S rs2_FCVT_LU_S rs2_FCVT_W_S rs2_FCVT_WU_S supportsA supportsF supportsM] in *;
    repeat match goal with
           | [v := context [Z.eqb ?x ?y], H: ?x <> ?y |- _] =>
             destruct (Z.eqb_spec x y) in *; [exfalso; auto; fail|cbn in v]
           end;
    try cbn in decodeI.

  Ltac kami_struct_cbv H :=
    let t := type of H in
    let tc :=
      eval cbv [ilist.ilist_to_fun_m
                  Notations.icons'
                  VectorFacts.Vector_nth_map VectorFacts.Vector_nth_map' Fin.t_rect
                  VectorFacts.Vector_find VectorFacts.Vector_find'
                  Notations.fieldAccessor
                  Struct.attrName StringEq.string_eq StringEq.ascii_eq Bool.eqb andb
                  Vector.caseS projT2]
    in t in
    let Ht := fresh "H" in
    assert (Ht: t = tc) by reflexivity;
    rewrite Ht in H; clear Ht.

  Lemma kamiStep_sound_case_execLd:
    forall km1 t0 rm1 post kupd cs
           (Hkinv: scmm_inv (Z.to_nat memSizeLg) rv32RfIdx rv32Fetch km1),
      states_related (km1, t0) rm1 ->
      mcomp_sat_unit (run1 iset) rm1 post ->
      Step kamiProc km1 kupd
           {| annot := Some (Some "execLd"%string);
              defs := FMap.M.empty _;
              calls := cs |} ->
      exists rm2 t,
        KamiLabelR
          {| annot := Some (Some "execLd"%string);
             defs := FMap.M.empty _;
             calls := cs |} t /\
        states_related (FMap.M.union kupd km1, t ++ t0) rm2 /\ post rm2.
  Proof.
    intros.
    match goal with
    | [H: states_related _ _ |- _] => inversion H; subst; clear H
    end.
    kinvert_more.
    kinv_action_dest_nosimpl.
    3:   exfalso; clear -Heqic0; discriminate.

    -

      block_subst kupd.
      red_regmap.
      red_trivial_conds.
      cleanup_trivial.
      unblock_subst kupd.

      rt.
eval_kami_fetch.
rt.

      kami_cbn_hint Heqic.
      kami_cbn_hint H.
      kami_cbn_all.
      kami_struct_cbv Heqic.
      kami_struct_cbv H.

      match goal with
      | [H: context [instrMem ?ipc] |- _] => set (kinst:= instrMem ipc)
      end.
      repeat
        match goal with
        | [H: context [instrMem ?ipc] |- _] => change (instrMem ipc) with kinst in H
        | [ |- context [instrMem ?ipc] ] => change (instrMem ipc) with kinst
        end.
      clearbody kinst.

      match goal with
      | [H: context [@evalExpr ?fk (rv32CalcLdVal ?sz ?ty ?la ?lv ?lty)] |- _] =>
        remember (@evalExpr fk (rv32CalcLdVal sz ty la lv lty)) as ldVal
      end.
      kami_cbn_hint_func HeqldVal rv32CalcLdVal.

      match goal with
      | [H: context [@evalExpr ?fk (rv32NextPc ?sz ?ty ?rf ?pc ?inst)] |- _] =>
        remember (@evalExpr fk (rv32NextPc sz ty rf pc inst)) as npc
      end.
      kami_cbn_hint_func Heqnpc rv32NextPc.

      weq_to_Zeqb.

      match type of H15 with
      | context [Z.eqb ?x ?y] =>
        destruct (Z.eqb_spec x y) in H15; [discriminate|clear H15]
      end.
      match type of H14 with
      | context [Z.eqb ?x ?y] =>
        destruct (Z.eqb_spec x y) in H14; [clear H14|discriminate]
      end.
      match type of e with
      | context [Z.eqb ?x ?y] =>
        destruct (Z.eqb_spec x y) in e; [clear e|]
      end.
      2: match type of e with
         | context [Z.eqb ?x ?y] =>
           destruct (Z.eqb_spec x y) in e; discriminate
         end.

      dest_Zeqb.

      all: simpl_bit_manip.

      all: eval_decode.
      all: try subst opcode; try subst funct3; try subst funct6; try subst funct7;
        try subst shamtHi; try subst shamtHiTest.
      all: eval_decodeI decodeI.

      5: match goal with
         | [decodeI := if ?x =? ?y then Lw _ _ _ else InvalidI |- _] =>
           destruct (Z.eqb_spec x y) in *
         end.
      all: subst dec; mcomp_step_in H5;
        repeat match goal with
               | H : False |- _ => case H
               | H : Z |- _ => clear H
               | H : list Instruction |- _ => clear H
               | H : Instruction |- _ => clear H
               end.

      all: replace (getReg rrf rs1) with
        (if Z.eq_dec rs1 0 then word.of_Z 0
         else match map.get rrf rs1 with
              | Some x => x
              | None => word.of_Z 0
              end) in *.
      2,4,6,8,10,12:
        unfold getReg; repeat destruct_one_match; try reflexivity;
      [ clearbody rs1; subst rs1; discriminate
      | exfalso;
        pose proof bitSlice_range_ex (@kunsigned 32 kinst) 15 20 as HR;
        change (bitSlice (@kunsigned 32 kinst) 15 20) with rs1 in HR;
        Lia.lia ].

      all: rt.

      all: unfold evalExpr in Heqic; fold evalExpr in Heqic.
      all: try match goal with
               | [H: match Memory.load_bytes ?sz ?m ?a with | Some _ => _ | None => _ end |- _] =>
                 destruct (Memory.load_bytes sz m a) as [lv|] eqn:Hlv; [exfalso|]
               end.
      all: try (subst v oimm12;
                regs_get_red Hlv;
                match goal with
                | [Heqic: true = evalExpr (isMMIO _ _) |- _] =>
                  apply eq_sym, is_mmio_spec in Heqic;
                  eapply mem_related_load_bytes_Some in Hlv; [|eassumption|discriminate];
                  clear -Heqic Hlv;
                  cbv [Utility.add
                         ZToReg MachineWidth_XLEN
                         word.add word wordW KamiWord.word
                         word.of_Z kofZ] in Hlv;
                  try change (BinInt.Z.to_nat width) with (Pos.to_nat 32) in Hlv;
                  blia
                end).

      all: match goal with
           | [H: nonmem_load _ _ _ _ _ |- _] =>
             let Hpost := fresh "H" in
             destruct H as [? [? [[? ?] Hpost]]];
               cbv [MMIOReadOK FE310_mmio] in Hpost;
               specialize (Hpost (split _ (wordToZ ldVal)) ltac:(trivial))
           end.
