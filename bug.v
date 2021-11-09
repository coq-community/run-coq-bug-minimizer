(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "-deprecated-native-compiler-option" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/bedrock2/processor/src/processor" "processor" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/bedrock2/deps/coqutil/src/coqutil" "coqutil" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/bedrock2/deps/riscv-coq/src/riscv" "riscv" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/bedrock2/deps/kami/Kami" "Kami" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-top" "bug_01" "-async-proofs-tac-j" "1" "-native-compiler" "no") -*- *)
(* File reduced by coq-bug-finder from original input, then from 3550 lines to 869 lines, then from 927 lines to 743 lines, then from 925 lines to 744 lines, then from 925 lines to 1312 lines, then from 1317 lines to 1048 lines, then from 1047 lines to 862 lines, then from 1043 lines to 1348 lines, then from 1353 lines to 1345 lines, then from 1343 lines to 981 lines, then from 1110 lines to 962 lines, then from 1113 lines to 1719 lines, then from 1723 lines to 1335 lines, then from 1336 lines to 1078 lines, then from 1206 lines to 1056 lines, then from 1207 lines to 1394 lines, then from 1398 lines to 1312 lines, then from 1316 lines to 1118 lines, then from 1268 lines to 1312 lines, then from 1316 lines to 1326 lines, then from 1329 lines to 1145 lines, then from 1288 lines to 1141 lines, then from 1291 lines to 1141 lines, then from 1291 lines to 1848 lines, then from 1852 lines to 1730 lines, then from 1731 lines to 1549 lines, then from 1579 lines to 1437 lines *)
(* coqc version 8.15+alpha compiled with OCaml 4.13.0
   coqtop version runner-0277ea0f-project-6138686-concurrent-0:/builds/coq/coq/_build/default,(HEAD detached at f363a4f) (f363a4f627994f230b0ff01ad62efe071b33fb68)
   Expected coqc runtime on this file: 49.554 sec *)
Module Export AdmitTactic.
Module Import LocalFalse.
End LocalFalse.
Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.
End AdmitTactic.
Require coqutil.Word.Bitwidth32.
Require coqutil.Tactics.rdelta.
Require riscv.Platform.MetricMinimalMMIO.
Require riscv.Platform.FE310ExtSpec.
Require Kami.Kami.
Require Kami.Ex.SC.
Module Export IsaRv32.
Import Kami.Lib.Word.
Import Kami.Syntax.
Import Kami.Notations.
Import Kami.Ex.MemTypes.
Import Kami.Ex.SC.

Definition rv32InstBytes := 4.
Definition rv32DataBytes := 4.

Definition rv32RfIdx := 5.

Section Common.

  Definition getOpcodeE {ty}
             (inst : Expr ty (SyntaxKind (Data rv32DataBytes))) :=
    (UniBit (Trunc 7 _) inst)%kami_expr.

  Definition getRs1E {ty}
             (inst : Expr ty (SyntaxKind (Data rv32DataBytes))) :=
    (UniBit (ConstExtract 15 5 _) inst)%kami_expr.

  Definition getRs1ValueE {ty}
             (s : StateT rv32DataBytes rv32RfIdx ty)
             (inst : Expr ty (SyntaxKind (Data rv32DataBytes))) :=
    (#s @[getRs1E inst])%kami_expr.

  Definition getRs2E {ty}
             (inst : Expr ty (SyntaxKind (Data rv32DataBytes))) :=
    (UniBit (ConstExtract 20 5 _) inst)%kami_expr.

  Definition getRs2ValueE {ty}
             (s : StateT rv32DataBytes rv32RfIdx ty)
             (inst : Expr ty (SyntaxKind (Data rv32DataBytes))) :=
    (#s @[getRs2E inst])%kami_expr.

  Definition getRdE {ty}
             (inst: Expr ty (SyntaxKind (Data rv32DataBytes))) :=
    UniBit (ConstExtract 7 5 _) inst.

  Definition getFunct7E {ty}
             (inst : Expr ty (SyntaxKind (Data rv32DataBytes))) :=
    (UniBit (TruncLsb 25 7) inst)%kami_expr.

  Definition getFunct6E {ty}
             (inst : Expr ty (SyntaxKind (Data rv32DataBytes))) :=
    (UniBit (TruncLsb 26 6) inst)%kami_expr.

  Definition getFunct3E {ty}
             (inst : Expr ty (SyntaxKind (Data rv32DataBytes))) :=
    (UniBit (ConstExtract 12 3 _) inst)%kami_expr.

  Definition getOffsetIE {ty}
             (inst : Expr ty (SyntaxKind (Data rv32DataBytes))) :=
    (UniBit (TruncLsb 20 12) inst)%kami_expr.

  Definition getOffsetShamtE {ty}
             (inst : Expr ty (SyntaxKind (Data rv32DataBytes))) :=
    (UniBit (ConstExtract 20 5 _) inst)%kami_expr.

  Definition getHiShamtE {ty}
             (inst : Expr ty (SyntaxKind (Data rv32DataBytes))) :=
    (UniBit (ConstExtract 25 1 _) inst)%kami_expr.

  Definition getOffsetSE {ty}
             (inst : Expr ty (SyntaxKind (Data rv32DataBytes))) :=
    (BinBit (Concat _ _)
            (UniBit (TruncLsb 25 7) inst)
            (UniBit (ConstExtract 7 5 _) inst))%kami_expr.

  Definition getOffsetSBE {ty}
             (inst: Expr ty (SyntaxKind (Data rv32DataBytes))) :=
    (BinBit (Concat _ _)
            (BinBit (Concat _ _)
                    (UniBit (TruncLsb 31 1) inst)
                    (UniBit (ConstExtract 7 1 _) inst))
            (BinBit (Concat _ _)
                    (UniBit (ConstExtract 25 6 _) inst)
                    (UniBit (ConstExtract 8 4 _) inst)))%kami_expr.

  Definition getOffsetUE {ty}
             (inst: Expr ty (SyntaxKind (Data rv32DataBytes))) :=
    (UniBit (TruncLsb 12 20) inst)%kami_expr.

  Definition getOffsetUJE {ty}
             (inst: Expr ty (SyntaxKind (Data rv32DataBytes))) :=
    (BinBit (Concat _ _)
            (BinBit (Concat _ _)
                    (UniBit (TruncLsb 31 1) inst)
                    (UniBit (ConstExtract 12 8 _) inst))
            (BinBit (Concat _ _)
                    (UniBit (ConstExtract 20 1 _) inst)
                    (UniBit (ConstExtract 21 10 _) inst))).
End Common.

Section RV32IM.
  Variables rv32AddrSize
            rv32IAddrSize: nat.

  Hypotheses (Haddr1: rv32AddrSize = 2 + (rv32AddrSize - 2))
             (Haddr2: rv32AddrSize = 1 + 1 + (rv32AddrSize - 2))
             (Haddr3: rv32AddrSize = 2 + rv32IAddrSize
                                     + (rv32AddrSize - (2 + rv32IAddrSize))).

  Section Constants.
    Definition opcode_BRANCH: nat := 99.
    Definition opcode_LOAD: nat := 3.
    Definition opcode_JAL: nat := 111.
    Definition opcode_JALR: nat := 103.
    Definition opcode_STORE: nat := 35.
    Definition funct3_LHU: nat := 5.
    Definition funct3_LH: nat := 1.
    Definition funct3_LBU: nat := 4.
    Definition funct3_LB: nat := 0.
    Definition funct3_BNE: nat := 1.
    Definition funct3_BLTU: nat := 6.
    Definition funct3_BLT: nat := 4.
    Definition funct3_BGEU: nat := 7.
    Definition funct3_BGE: nat := 5.
    Definition funct3_BEQ: nat := 0.

  End Constants.
  Ltac register_op_funct3 inst op expr :=
    refine (IF (getFunct3E #inst == $op) then expr else _)%kami_expr.

  Section Decode.

    Definition rv32GetOptype: OptypeT rv32InstBytes.
      unfold OptypeT; intros ty inst.
      refine (IF (getOpcodeE #inst == $opcode_LOAD) then $$opLd else _)%kami_expr.
      refine (IF (getOpcodeE #inst == $opcode_STORE) then $$opSt else $$opNm)%kami_expr.
    Defined.

    Definition rv32GetLdDst: LdDstT rv32InstBytes rv32RfIdx.
admit.
Defined.

    Definition rv32GetLdAddr: LdAddrT rv32AddrSize rv32InstBytes.
      unfold LdAddrT; intros ty inst.
      exact (_signExtend_ (getOffsetIE #inst))%kami_expr.
    Defined.

    Definition rv32GetLdSrc: LdSrcT rv32InstBytes rv32RfIdx.
      unfold LdSrcT; intros ty inst.
      exact (getRs1E #inst)%kami_expr.
    Defined.

    Definition rv32CalcLdAddr: LdAddrCalcT rv32AddrSize rv32DataBytes.
      unfold LdAddrCalcT; intros ty ofs base.
      exact ((_zeroExtend_ #base) + #ofs)%kami_expr.
    Defined.

    Definition rv32GetLdType: LdTypeT rv32InstBytes.
      unfold LdTypeT; intros ty inst.
      exact (getFunct3E #inst)%kami_expr.
    Defined.

    Definition rv32GetStAddr: StAddrT rv32AddrSize rv32InstBytes.
admit.
Defined.

    Definition rv32GetStSrc: StSrcT rv32InstBytes rv32RfIdx.
admit.
Defined.

    Definition rv32CalcStAddr: StAddrCalcT rv32AddrSize rv32DataBytes.
admit.
Defined.

    Definition rv32CalcStByteEn: StByteEnCalcT rv32InstBytes rv32DataBytes.
admit.
Defined.

    Definition rv32GetStVSrc: StVSrcT rv32InstBytes rv32RfIdx.
admit.
Defined.

    Definition rv32GetSrc1: Src1T rv32InstBytes rv32RfIdx.
admit.
Defined.

    Definition rv32GetSrc2: Src2T rv32InstBytes rv32RfIdx.
admit.
Defined.

    Definition rv32GetDst: DstT rv32InstBytes rv32RfIdx.
admit.
Defined.

  End Decode.

  Definition rv32DoExec: ExecT rv32AddrSize rv32InstBytes rv32DataBytes.
admit.
Defined.

  Definition rv32CalcLdVal: LdValCalcT rv32AddrSize rv32DataBytes.
    unfold LdValCalcT; intros ty addr val ldty.
    refine (IF (#ldty == $funct3_LB)
            then _signExtend_ (UniBit (Trunc BitsPerByte _) #val)
            else _)%kami_expr.
    refine (IF (#ldty == $funct3_LH)
            then _signExtend_ (UniBit (Trunc (2 * BitsPerByte) _) #val)
            else _)%kami_expr.
    refine (IF (#ldty == $funct3_LBU)
            then _zeroExtend_ (UniBit (Trunc BitsPerByte _) #val)
            else _)%kami_expr.
    refine (IF (#ldty == $funct3_LHU)
            then _zeroExtend_ (UniBit (Trunc (2 * BitsPerByte) _) #val)
            else #val)%kami_expr.
  Defined.

  Definition rv32ToIAddr: ToIAddrT rv32AddrSize rv32IAddrSize.
    unfold ToIAddrT; intros ty addr.
    rewrite Haddr3 in addr.
    exact (_truncLsb_ (_truncate_ #addr))%kami_expr.
  Defined.

  Definition rv32ToAddr: ToAddrT rv32AddrSize rv32IAddrSize.
admit.
Defined.

  Definition rv32AlignInst: AlignInstT rv32InstBytes rv32DataBytes.
admit.
Defined.

  Definition rv32NextPc: NextPcT rv32AddrSize rv32InstBytes rv32DataBytes rv32RfIdx.
    unfold NextPcT; intros ty st pc inst.

    refine (IF (getOpcodeE #inst == $opcode_JAL)
            then #pc + (_signExtend_ {getOffsetUJE #inst, $$(WO~0)})
            else _)%kami_expr.
    refine (IF (getOpcodeE #inst == $opcode_JALR)
            then ((_signExtend_ (getRs1ValueE st #inst) + _signExtend_ (getOffsetIE #inst))
                    ~& (UniBit (Inv _) $1))
            else _)%kami_expr.

    refine (IF (getOpcodeE #inst == $opcode_BRANCH) then _ else #pc + $4)%kami_expr.
    register_op_funct3 inst funct3_BEQ
                       (IF (getRs1ValueE st #inst == getRs2ValueE st #inst)
                        then #pc + (_signExtend_ {getOffsetSBE #inst, $$(WO~0)})
                        else #pc + $4)%kami_expr.
    register_op_funct3 inst funct3_BNE
                       (IF (getRs1ValueE st #inst != getRs2ValueE st #inst)
                        then #pc + (_signExtend_ {getOffsetSBE #inst, $$(WO~0)})
                        else #pc + $4)%kami_expr.
    register_op_funct3 inst funct3_BLT
                       (IF (getRs1ValueE st #inst <s getRs2ValueE st #inst)
                        then #pc + (_signExtend_ {getOffsetSBE #inst, $$(WO~0)})
                        else #pc + $4)%kami_expr.
    register_op_funct3 inst funct3_BGE
                       (IF (getRs1ValueE st #inst >s= getRs2ValueE st #inst)
                        then #pc + (_signExtend_ {getOffsetSBE #inst, $$(WO~0)})
                        else #pc + $4)%kami_expr.
    register_op_funct3 inst funct3_BLTU
                       (IF (getRs1ValueE st #inst < getRs2ValueE st #inst)
                        then #pc + (_signExtend_ {getOffsetSBE #inst, $$(WO~0)})
                        else #pc + $4)%kami_expr.
    register_op_funct3 inst funct3_BGEU
                       (IF (getRs1ValueE st #inst >= getRs2ValueE st #inst)
                        then #pc + (_signExtend_ {getOffsetSBE #inst, $$(WO~0)})
                        else #pc + $4)%kami_expr.
    exact (#pc + $4)%kami_expr.
  Defined.

  Instance rv32Fetch: AbsFetch rv32AddrSize rv32IAddrSize rv32InstBytes rv32DataBytes :=
    {| toIAddr := rv32ToIAddr;
       toAddr := rv32ToAddr;
       alignInst := rv32AlignInst |}.

  Instance rv32Dec: AbsDec rv32AddrSize rv32InstBytes rv32DataBytes rv32RfIdx :=
    {| getOptype := rv32GetOptype;
       getLdDst := rv32GetLdDst;
       getLdAddr := rv32GetLdAddr;
       getLdSrc := rv32GetLdSrc;
       calcLdAddr := rv32CalcLdAddr;
       getLdType := rv32GetLdType;
       getStAddr := rv32GetStAddr;
       getStSrc := rv32GetStSrc;
       calcStAddr := rv32CalcStAddr;
       calcStByteEn := rv32CalcStByteEn;
       getStVSrc := rv32GetStVSrc;
       getSrc1 := rv32GetSrc1;
       getSrc2 := rv32GetSrc2;
       getDst := rv32GetDst |}.

  Instance rv32Exec:
    AbsExec rv32AddrSize rv32InstBytes rv32DataBytes rv32RfIdx :=
    {| calcLdVal := rv32CalcLdVal;
       doExec := rv32DoExec;
       getNextPc := rv32NextPc |}.

End RV32IM.

End IsaRv32.
Module Export SCMMInl.
Import Kami.Syntax.
Import Kami.Semantics.
Import Kami.Tactics.
Import Kami.Ex.SC.

Set Implicit Arguments.

Section Inlined.
  Variables (addrSize maddrSize iaddrSize fifoSize instBytes dataBytes rfIdx: nat)
            (Hdb: {pdb & dataBytes = S pdb}).

  Variables (fetch: AbsFetch addrSize iaddrSize instBytes dataBytes)
            (dec: AbsDec addrSize instBytes dataBytes rfIdx)
            (exec: AbsExec addrSize instBytes dataBytes rfIdx)
            (ammio: AbsMMIO addrSize).

  Variable (procInit: ProcInit addrSize dataBytes rfIdx)
           (memInit: MemInit maddrSize).

  Definition scmm: Modules := scmm Hdb fetch dec exec ammio procInit memInit.
  Hint Unfold scmm: ModuleDefs.

  Definition scmmInl: sigT (fun m: Modules => scmm <<== m).
  Proof.
    kinline_refine scmm.
  Defined.

End Inlined.

End SCMMInl.
Module Export SCMMInv.
Import Coq.Strings.String.
Import Kami.Lib.Word.
Import Kami.Lib.FMap.
Import Kami.Syntax.
Import Kami.Semantics.
Import Kami.Ex.MemTypes.
Import Kami.Ex.SC.

Set Implicit Arguments.

Local Open Scope fmap.

Section Invariants.
  Variables (addrSize maddrSize iaddrSize fifoSize instBytes dataBytes rfIdx: nat)
            (Hdb: {pdb & dataBytes = S pdb}).

  Variables (fetch: AbsFetch addrSize iaddrSize instBytes dataBytes)
            (dec: AbsDec addrSize instBytes dataBytes rfIdx)
            (exec: AbsExec addrSize instBytes dataBytes rfIdx)
            (ammio: AbsMMIO addrSize).

  Definition scmm_inv_rf_zero
             (rfv: fullType type (SyntaxKind (Vector (Data dataBytes) rfIdx))) :=
    rfv $0 = $0.

  Definition scmm_inv_pgm_init
             (initv: fullType type (SyntaxKind Bool))
             (ofsv: fullType type (SyntaxKind (Bit iaddrSize)))
             (pgmv: fullType type (SyntaxKind (Vector (Data instBytes) iaddrSize)))
             (memv: fullType type (SyntaxKind (Vector (Bit BitsPerByte) maddrSize))) :=
    initv = false ->
    forall iaddr,
      iaddr < ofsv ->
      pgmv iaddr = evalExpr (alignInst _ (combineBytes dataBytes (evalExpr (toAddr _ iaddr)) memv)).

  Inductive scmm_inv (o: RegsT) : Prop :=
  | ProcInv:
      forall (pcv: fullType type (SyntaxKind (Pc addrSize)))
             (Hpcv: o@["pc"] = Some (existT _ _ pcv))
             (rfv: fullType type (SyntaxKind (Vector (Data dataBytes) rfIdx)))
             (Hrfv: o@["rf"] = Some (existT _ _ rfv))
             (pinitv: fullType type (SyntaxKind Bool))
             (Hpinitv: o@["pinit"] = Some (existT _ _ pinitv))
             (pinitOfsv: fullType type (SyntaxKind (Bit iaddrSize)))
             (HpinitOfsv: o@["pinitOfs"] = Some (existT _ _ pinitOfsv))
             (pgmv: fullType type (SyntaxKind (Vector (Data instBytes) iaddrSize)))
             (Hpgmv: o@["pgm"] = Some (existT _ _ pgmv))
             (memv: fullType type (SyntaxKind (Vector (Bit BitsPerByte) maddrSize)))
             (Hmemv: o@["mem"] = Some (existT _ _ memv)),
        scmm_inv_rf_zero rfv ->
        scmm_inv_pgm_init pinitv pinitOfsv pgmv memv ->
        scmm_inv o.

End Invariants.

End SCMMInv.
Module Export processor_DOT_KamiWord_WRAPPED.
Module Export KamiWord.
Import Coq.ZArith.ZArith.
Import coqutil.Word.Interface.
Import word.
Import Kami.Lib.Word.

Local Open Scope bool_scope.
Local Open Scope Z_scope.

Section KamiWordFacts.

  Lemma sumbool_rect_bool_weq n x y :
    sumbool_rect (fun _ => bool) (fun _ => true) (fun _ => false) (@weq n x y) = weqb x y.
Admitted.

  Lemma unsigned_eqb n x y : Z.eqb (Z.of_N (wordToN x)) (Z.of_N (wordToN y)) = @weqb n x y.
Admitted.

End KamiWordFacts.

Section WithWidth.
  Context {width : Z}.
  Local Notation sz := (Z.to_nat width).

  Definition kword: Type := Kami.Lib.Word.word sz.
  Definition kunsigned(x: kword): Z := Z.of_N (wordToN x).
  Definition ksigned: kword -> Z := @wordToZ sz.
  Definition kofZ: Z -> kword := ZToWord sz.

  Definition riscvZdivu(x y: Z): Z :=
    if y =? 0 then 2 ^ width - 1 else Z.div x y.

  Definition riscvZdivs(x y: Z): Z :=
    if (x =? - 2 ^ (width - 1)) && (y =? - 1) then x
    else if y =? 0 then - 1 else Z.quot x y.

  Definition riscvZmodu(x y: Z): Z :=
    if y =? 0 then x else Z.modulo x y.

  Definition riscvZmods(x y: Z): Z :=
    if y =? 0 then x else Z.rem x y.

  Instance word : word.word width := {|
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

  |}.

  End WithWidth.
Arguments word : clear implicits.
Arguments kword : clear implicits.

Open Scope Z_scope.

Section MkWords.
  Context {width : Z}.
  Instance wordW: word.word width := word width.
End MkWords.

End KamiWord.
Module Export processor.
Module Export KamiWord.
Include processor_DOT_KamiWord_WRAPPED.KamiWord.
End KamiWord.
Module Export KamiProc.
Import Coq.ZArith.ZArith.
Import coqutil.Z.Lia.
Import Kami.Kami.
Import Kami.Ex.MemTypes.
Import Kami.Ex.SC.

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

  Definition pRegsToT (r: Kami.Semantics.RegsT): option pst :=
    (mlet pcv: (Pc addrSize) <- r |> "pc" <| None;
    mlet rfv: (Vector (Data dataBytes) rfIdx) <- r |> "rf" <| None;
    mlet pinitv: Bool <- r |> "pinit" <| None;
    mlet pgmv: (Vector (Data instBytes) iaddrSize) <- r |> "pgm" <| None;
    mlet memv: (Vector (Bit BitsPerByte) maddrSize) <- r |> "mem" <| None;
    (Some {| pc := pcv; rf := rfv;
             pinit := pinitv; pgm := pgmv; mem := memv |}))%mapping.

End Parametrized.

Definition width: Z := 32.
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

  Local Definition pcInitVal: ConstT (Pc nwidth) :=
    ConstBit $0.

  Local Definition rfInitVal: ConstT (Vector (Data rv32DataBytes) rv32RfIdx) :=
    ConstVector (replicate (ConstBit $0) _).

  Definition procInit: ProcInit nwidth rv32DataBytes rv32RfIdx :=
    {| pcInit := pcInitVal; rfInit := rfInitVal |}.
  Variables (memInit: MemInit nmemSizeLg)
            (rv32MMIO: AbsMMIO nwidth).

  Definition procInl :=
    pprocInl (existT _ _ eq_refl) (rv32Fetch _ _ width_inst_valid)
             (rv32Dec _) (rv32Exec _)
             rv32MMIO procInit memInit.
  Definition proc: Kami.Syntax.Modules := projT1 procInl.

  Definition hst := Kami.Semantics.RegsT.
  Definition KamiMachine := hst.

  Definition st :=
    @pst nwidth nmemSizeLg ninstrMemSizeLg rv32InstBytes rv32DataBytes rv32RfIdx.

  Definition RegsToT (r: hst): option st :=
    pRegsToT nwidth nmemSizeLg ninstrMemSizeLg rv32InstBytes rv32DataBytes rv32RfIdx r.

End PerInstAddr.

Instance kami_AbsMMIO (memSizeLg: N): AbsMMIO (Z.to_nat width) :=
  {| isMMIO :=
       fun _ addr => ($$(NToWord _ (2 ^ memSizeLg)) <= #addr)%kami_expr
  |}.

End KamiProc.
Module Export processor_DOT_Consistency_WRAPPED.
Module Export Consistency.
Import Coq.ZArith.BinInt.
Import Coq.Lists.List.
Import Kami.Lib.Word.
Import Kami.Semantics.
Import coqutil.Word.LittleEndian.
Import coqutil.Map.Interface.
Import riscv.Utility.Utility.
Import riscv.Platform.RiscvMachine.

Instance word: word 32 := @KamiWord.wordW width.

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

  Definition instrMemSize: nat := NatLib.pow2 (2 + Z.to_nat instrMemSizeLg).

  Definition pc_related (kpc rpc: kword width): Prop :=
    kpc = rpc.

  Definition AddrAligned (addr: kword width) :=
    split1 2 (nwidth - 2) addr = WO~0~0.

  Definition kamiXAddrs: XAddrs :=
    alignedXAddrsRange 0 instrMemSize.

  Definition mem_related (kmem: kword memSizeLg -> kword 8)
             (rmem : mem): Prop :=
    forall addr: kword width,
      map.get rmem addr =
      if Z.ltb (kunsigned addr) (Z.pow 2 memSizeLg)
      then Some (byte.of_Z (uwordToZ (kmem (evalZeroExtendTrunc _ addr))))
      else None.

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
             (rrf: Registers): Prop :=
    forall w, w <> $0 -> map.get rrf (Z.of_N (wordToN w)) = Some (krf w).

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
Import processor.Consistency.

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

  Definition iset: InstructionSet := RV32I.

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

  Arguments isMMIO: simpl never.

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
