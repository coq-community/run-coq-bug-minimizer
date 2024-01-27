
(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "-deprecated-native-compiler-option" "-native-compiler" "no" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/fiat_crypto/rupicola/bedrock2/compiler/src/compiler" "compiler" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/fiat_crypto/rupicola/bedrock2/compiler/src/compilerExamples" "compilerExamples" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/fiat_crypto/rupicola/bedrock2/bedrock2/src/bedrock2" "bedrock2" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/fiat_crypto/rupicola/bedrock2/bedrock2/src/bedrock2Examples" "bedrock2Examples" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/fiat_crypto/rupicola/bedrock2/deps/coqutil/src/coqutil" "coqutil" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/fiat_crypto/rupicola/bedrock2/deps/riscv-coq/src/riscv" "riscv" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-top" "compiler.FlatToRiscvFunctions" "-async-proofs-tac-j" "1") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 2072 lines to 788 lines, then from 801 lines to 1082 lines, then from 1087 lines to 864 lines, then from 870 lines to 1030 lines *)
(* coqc version 8.20+alpha compiled with OCaml 4.14.1
   coqtop version runner-t7b1znuaq-project-4504-concurrent-1:/builds/coq/coq/_build/default,(HEAD detached at f2a18e4e13cd) (f2a18e4e13cd555e95ea9f3963207e79f835209a)
   Modules that could not be inlined: compiler.FlatToRiscvCommon
   Expected coqc runtime on this file: 17.379 sec *)
Require Coq.Lists.List.
Require Coq.ZArith.ZArith.
Require Coq.ZArith.BinIntDef.
Require Coq.ZArith.BinInt.
Require coqutil.Word.Interface.
Require Coq.ZArith.Zpow_facts.
Require coqutil.Z.div_mod_to_equations.
Require Coq.micromega.Lia.
Require coqutil.Z.Lia.
Require Coq.btauto.Btauto.
Require coqutil.Z.PushPullMod.
Require Coq.setoid_ring.Ring_theory.
Require coqutil.Z.bitblast.
Require coqutil.sanity.
Require Coq.Arith.PeanoNat.
Require Coq.Arith.Compare_dec.
Require Coq.NArith.NArith.
Require Coq.Strings.String.
Require coqutil.Decidable.
Require coqutil.Word.Properties.
Require coqutil.Word.Bitwidth.
Require coqutil.Datatypes.PrimitivePair.
Require coqutil.Datatypes.HList.
Require coqutil.Tactics.destr.
Require coqutil.Tactics.forward.
Require coqutil.Tactics.Tactics.
Require coqutil.Datatypes.Option.
Require Coq.Sorting.Permutation.
Require coqutil.Sorting.Permutation.
Require coqutil.Datatypes.List.
Require Coq.Classes.Morphisms.
Require Coq.Classes.RelationClasses.
Require Coq.Logic.PropExtensionality.
Require Coq.Logic.FunctionalExtensionality.
Require Coq.Program.Tactics.
Require coqutil.Datatypes.PropSet.
Require coqutil.Map.Interface.
Require coqutil.Tactics.autoforward.
Require coqutil.Map.Properties.
Require Coq.Init.Byte.
Require Coq.Strings.Byte.
Require coqutil.Byte.
Require coqutil.Z.ZLib.
Require coqutil.Z.BitOps.
Require riscv.Utility.Utility.
Require riscv.Platform.Memory.
Require riscv.Utility.Monads.
Require riscv.Utility.MonadNotations.
Require coqutil.Macros.unique.
Require Coq.Bool.Bool.
Require bedrock2.MetricLogging.
Require Coq.setoid_ring.ZArithRing.
Require coqutil.Z.prove_Zeq_bitwise.
Require coqutil.Word.LittleEndianList.
Require coqutil.Macros.subst.
Require Coq.Numbers.BinNums.
Require bedrock2.Syntax.
Require coqutil.Map.MapKeys.
Require coqutil.Map.OfFunc.
Require coqutil.Map.OfListWord.
Require bedrock2.Memory.
Require coqutil.Datatypes.dlist.
Require Coq.NArith.BinNat.
Require coqutil.Tactics.fwd_core.
Require coqutil.Tactics.fwd_arith_hints.
Require coqutil.Tactics.fwd_list_hints.
Require coqutil.Tactics.fwd_map_hints.
Require coqutil.Tactics.fwd_word_hints.
Require coqutil.Tactics.fwd.
Require coqutil.Datatypes.Result.
Require coqutil.Map.Solver.
Require compiler.util.Common.
Require coqutil.Tactics.Simp.
Require Coq.Logic.Eqdep_dec.
Require coqutil.Map.SortedList.
Require Coq.NArith.BinNatDef.
Require coqutil.Datatypes.String.
Require coqutil.Map.SortedListString.
Require bedrock2.Semantics.
Require coqutil.Datatypes.ListSet.
Require compiler.FlatImp.
Require Coq.Program.Wf.
Require Coq.Init.Datatypes.
Require riscv.Spec.Decode.
Require riscv.Spec.CSRField.
Require riscv.Spec.Machine.
Require riscv.Spec.PseudoInstructions.
Require coqutil.Word.LittleEndian.
Require riscv.Platform.RiscvMachine.
Require riscv.Platform.MetricLogging.
Require riscv.Platform.MetricRiscvMachine.
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
Require riscv.Utility.PowerFunc.
Require coqutil.Tactics.rewr.
Require riscv.Utility.InstructionCoercions.
Require riscv.Utility.MkMachineWidth.
Require riscv.Spec.Primitives.
Require riscv.Spec.MetricPrimitives.
Require compiler.util.Misc.
Require riscv.Utility.runsToNonDet.
Require riscv.Utility.RegisterNames.
Require compiler.Registers.
Require compiler.FlatImpConstraints.
Require riscv.Utility.Encode.
Require coqutil.Tactics.rdelta.
Require bedrock2.Lift1Prop.
Require bedrock2.Map.Separation.
Require coqutil.Tactics.syntactic_unify.
Require coqutil.Tactics.ltac_list_ops.
Require bedrock2.Map.SeparationLogic.
Require coqutil.Tactics.eplace.
Require Coq.setoid_ring.Ring.
Require bedrock2.Array.
Require coqutil.Macros.symmetry.
Require Coq.setoid_ring.Ring_tac.
Require bedrock2.ptsto_bytes.
Require bedrock2.Scalars.
Require coqutil.Word.SimplWordExpr.
Require bedrock2.SepLogAddrArith.
Require bedrock2.footpr.
Require compiler.SeparationLogic.
Require compiler.FlatToRiscvDef.
Require compiler.mod4_0.
Require compiler.DivisibleBy4.
Require riscv.Utility.Tactics.
Require riscv.Proofs.EncodeBound.
Require riscv.Proofs.invert_encode_R.
Require riscv.Proofs.invert_encode_R_atomic.
Require riscv.Proofs.invert_encode_I.
Require riscv.Proofs.invert_encode_I_shift_57.
Require riscv.Proofs.invert_encode_I_shift_66.
Require riscv.Proofs.invert_encode_I_system.
Require riscv.Proofs.invert_encode_S.
Require riscv.Proofs.invert_encode_SB.
Require riscv.Proofs.invert_encode_U.
Require riscv.Proofs.invert_encode_UJ.
Require riscv.Proofs.invert_encode_Fence.
Require riscv.Proofs.invert_encode_FenceI.
Require riscv.Proofs.DecodeEncodeProver.
Require riscv.Proofs.DecodeEncodeI.
Require riscv.Proofs.DecodeEncodeM.
Require riscv.Proofs.DecodeEncodeA.
Require riscv.Proofs.DecodeEncodeI64.
Require riscv.Proofs.DecodeEncodeM64.
Require riscv.Proofs.DecodeEncodeA64.
Require riscv.Proofs.DecodeEncodeCSR.
Require riscv.Proofs.DecodeEncode.
Require riscv.Platform.MetricSane.
Require compiler.GoFlatToRiscv.
Require compiler.RiscvWordProperties.
Require compiler.eqexact.
Require compiler.on_hyp_containing.
Require compiler.ZLemmas.
Require compiler.RunInstruction.
Require compiler.MetricsToRiscv.
Require compiler.regs_initialized.
Require compiler.FlatToRiscvCommon.

Import coqutil.Decidable.
Import coqutil.Map.Interface.
Import coqutil.Datatypes.PropSet.

Section WithParams.
  Import Interface.map.
  Context {var: Type}.

  Context {var_eqb: var -> var -> bool}.
  Context {var_eqb_spec: EqDecider var_eqb}.
  Context {val: Type}.

  Context {stateMap: map.map var val}.
  Local Hint Mode map.map - - : typeclass_instances.

  Lemma only_differ_refl: forall s1 r,
    only_differ s1 r s1.
Admitted.

  Lemma only_differ_put_r: forall m1 m2 k (v : val) s,
      k \in s ->
      map.only_differ m1 s m2 ->
      map.only_differ m1 s (map.put m2 k v).
Admitted.

  Lemma only_differ_trans_r: forall (s1 s2 s3 : stateMap) (r1 r2 : var -> Prop),
      map.only_differ s2 r1 s3 ->
      subset r1 r2 ->
      map.only_differ s1 r2 s2 ->
      map.only_differ s1 r2 s3.
Admitted.

  Lemma only_differ_subset: forall (s1 s2 : stateMap) (r1 r2 : var -> Prop),
      map.only_differ s1 r1 s2 ->
      subset r1 r2 ->
      map.only_differ s1 r2 s2.
Admitted.

  Lemma only_differ_put: forall s (d: set var) x v,
    elem_of x d ->
    only_differ s d (put s x v).
Admitted.

  Lemma put_extends_l: forall m1 m2 k v,
      map.get m2 k = None ->
      map.extends m1 m2 ->
      map.extends (map.put m1 k v) m2.
Admitted.

  Lemma extends_remove: forall m1 m2 k,
      map.extends m1 m2 ->
      map.extends m1 (map.remove m2 k).
Admitted.

  Lemma get_Some_remove: forall m k1 k2 v,
      map.get (map.remove m k1) k2 = Some v ->
      map.get m k2 = Some v.
Admitted.

  Lemma get_putmany_none: forall m1 m2 k,
      map.get m1 k = None ->
      map.get m2 k = None ->
      map.get (map.putmany m1 m2) k = None.
Admitted.

  Lemma get_put_diff_eq_l: forall m k v k' (r: option val),
      k <> k' ->
      map.get m k = r ->
      map.get (map.put m k' v) k = r.
Admitted.

  Lemma get_None_in_forall_keys: forall m k P,
      forall_keys P m ->
      ~ P k ->
      map.get m k = None.
Admitted.

End WithParams.
Import riscv.Spec.Decode.
Import riscv.Spec.Primitives.
Import riscv.Platform.RiscvMachine.
Import riscv.Platform.MetricRiscvMachine.
Import riscv.Utility.runsToNonDet.
Import compiler.util.Common.
Import coqutil.Datatypes.ListSet.
Import coqutil.Datatypes.List.
Import coqutil.Tactics.fwd.
Import compiler.SeparationLogic.
Import compiler.GoFlatToRiscv.
Import compiler.DivisibleBy4.
Import compiler.MetricsToRiscv.
Import compiler.FlatImp.
Import compiler.RunInstruction.
Import compiler.FlatToRiscvDef.
Import compiler.FlatToRiscvCommon.
Import compiler.Registers.

Import bedrock2.MetricLogging.

Local Arguments Z.mul: simpl never.
Local Arguments Z.add: simpl never.
Local Arguments Z.of_nat: simpl never.

Section Proofs.
  Context {iset: Decode.InstructionSet}.
  Context {pos_map: map.map String.string Z}.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width}.
  Context {word_ok: word.ok word}.
  Context {locals: map.map Z word}.
  Context {mem: map.map word byte}.
  Context {env: map.map String.string (list Z * list Z * FlatImp.stmt Z)}.
  Context {M: Type -> Type}.
  Context {MM: Monads.Monad M}.
  Context {RVM: Machine.RiscvProgram M word}.
  Context {PRParams: PrimitivesParams M MetricRiscvMachine}.
  Context {ext_spec: Semantics.ExtSpec}.
  Context {word_riscv_ok: RiscvWordProperties.word.riscv_ok word}.
  Context {locals_ok: map.ok locals}.
  Context {mem_ok: map.ok mem}.
  Context {pos_map_ok: map.ok pos_map}.
  Context {env_ok: map.ok env}.
  Context {PR: MetricPrimitives.MetricPrimitives PRParams}.
  Context {BWM: bitwidth_iset width iset}.
  Context (compile_ext_call: pos_map -> Z -> Z -> stmt Z -> list Instruction).

  Add Ring wring : (word.ring_theory (word := word))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (word.ring_morph (word := word)),
       constants [word_cst]).

  Local Notation RiscvMachineL := MetricRiscvMachine.

  Notation functions := (functions (iset := iset) compile_ext_call).
  Notation compile_function := (compile_function iset compile_ext_call).

  Lemma functions_expose: forall (base: word) (finfo: pos_map) impls f pos impl,
      map.get finfo f = Some pos ->
      map.get impls f = Some impl ->
      iff1 (functions base finfo impls)
           (functions base finfo (map.remove impls f) *
            program iset (word.add base (word.of_Z pos)) (compile_function finfo pos impl))%sep.
Admitted.

  Ltac safe_sidecond :=
    match goal with

    | |- @eq (list Instruction) _ _ => reflexivity
    | H: fits_stack _ _ _ ?Code |- fits_stack _ _ _ ?Code => exact H
    | H: map.get ?R RegisterNames.sp = Some _ |- map.get ?R RegisterNames.sp = Some _ => exact H
    | |- ?G => assert_fails (has_evar G);
               solve [ simpl_addrs; solve_word_eq word_ok
                     | reflexivity
                     | assumption
                     | solve_divisibleBy4
                     | solve_valid_machine word_ok ]
    | |- iff1 ?x _ =>
      simpl_MetricRiscvMachine_get_set;
      (tryif is_var x then
         lazymatch goal with
         | H: iff1 x _ |- _ => etransitivity; [exact H|]
         end
       else idtac);
      subst_sep_vars;
      wwcancel
    | H: subset (footpr _) _ |- subset (footpr ?F) _ =>
      tryif is_evar F then
        eassumption
      else
        (eapply rearrange_footpr_subset; [ exact H | solve [sidecondition] ])
    | |- _ => solve [wcancel_assumption]
    | |- ?G => is_lia G; assert_fails (has_evar G);

               repeat match goal with x := _ |- _ => subst x end;
               blia
    end.
  Notation "! n" := (word.of_Z n) (at level 0, n at level 0, format "! n") : word_scope.
  Notation "# n" := (Z.of_nat n) (at level 0, n at level 0, format "# n") : word_scope.
  Infix "+" := word.add : word_scope.
  Infix "*" := word.mul : word_scope.

  Open Scope word_scope.

  Ltac run1done :=
    apply runsToDone;
    simpl_MetricRiscvMachine_get_set;
    simpl in *;
    repeat match goal with
           | |- exists _, _ => eexists
           end; ssplit; simpl_word_exprs word_ok;
    match goal with
    | |- _ => solve_word_eq word_ok
    | |- (_ <= _)%metricsL => MetricsToRiscv.solve_MetricLog
    | |- iff1 ?x ?x => reflexivity

    | |- exists _ _, _ = _ /\ _ = _ /\ (_ * _)%sep _ =>
      eexists _, _; (split; [|split]); [..|wcancel_assumption]; blia
    | |- _ => solve [ solve_valid_machine word_ok ]
    | H:subset (footpr _) _
      |- subset (footpr _) _ => eapply rearrange_footpr_subset; [ exact H | solve [ wwcancel ] ]
    | |- _ => solve [ rewrite ?of_list_list_union in *; eauto 8 with map_hints ]
    | |- _ => idtac
  end.

  Lemma split_from_right{A: Type}: forall (l: list A) (len: nat),
      (len <= length l)%nat ->
      exists lL lR, l = lL ++ lR /\ length lL = (length l - len)%nat /\ length lR = len.
Admitted.

  Ltac split_from_right nameOrig nameL nameR len :=
    let nL := fresh in let nR := fresh in
    destruct (split_from_right nameOrig len) as [ nL [ nR [ ? [ ? ? ] ] ] ];
    [ try blia
    | subst nameOrig;
      rename nL into nameL, nR into nameR ].

  Ltac clear_old_sep_hyps :=
    repeat match goal with
           | H1: (_ * _)%sep ?m1, H2: (_ * _)%sep ?m2 |- _ => clear H1
           end.

  Ltac inline_iff1 :=
    match goal with
    | H: iff1 ?x _ |- _ => is_var x; apply iff1ToEq in H; subst x
    end.

  Hint Resolve
       get_putmany_none
       Decidable.Z.eqb_spec
       coqutil.Decidable.String.eqb_spec
       get_None_in_forall_keys
       sp_not_valid_FlatImp_var
       ra_not_valid_FlatImp_var
       map.not_in_of_list_zip_to_get_None
       sp_not_in_arg_regs
       ra_not_in_arg_regs
       regs_initialized_put
       map.forall_keys_put
       only_differ_put
       in_union_l
       in_union_l
       in_of_list
       in_eq
       map.put_extends
       get_put_diff_eq_l
       only_differ_refl
       only_differ_subset
       subset_union_l
       subset_union_rl
       subset_union_rr
       subset_refl
       in_singleton_set
       only_differ_put_r
       put_extends_l
       get_None_in_forall_keys
       ra_not_valid_FlatImp_var
       extends_remove
       map.get_put_same
    : map_hints.

  Hint Extern 3 (not (@eq Z _ _)) => (discriminate 1) : map_hints.

  Hint Extern 3 (map.only_differ _ _ _)
  => eapply only_differ_trans_r; [eassumption|eauto with map_hints ..]
  : map_hints.

  Lemma compile_function_body_correct: forall (e_impl_full : env) m l mc (argvs : list word)
    (st0 : locals) (post outcome : Semantics.trace -> mem -> locals -> MetricLog -> Prop)
    (argnames retnames : list Z) (body : stmt Z) (program_base : word)
    (pos : Z) (ret_addr : word) (mach : RiscvMachineL) (e_impl : env)
    (e_pos : pos_map) (binds_count : nat) (insts : list Instruction)
    (xframe : mem -> Prop) (t : list LogItem) (g : GhostConsts)
    (IH: forall (g0 : GhostConsts) (insts0 : list Instruction) (xframe0 : mem -> Prop)
                (initialL : RiscvMachineL) (pos0 : Z),
        fits_stack (rem_framewords g0) (rem_stackwords g0) e_impl body ->
        compile_stmt iset compile_ext_call e_pos pos0 (bytes_per_word * rem_framewords g0) body =
        insts0 ->
        pos0 mod 4 = 0 ->
        getPc initialL = program_base + !pos0 ->
        iff1 (allx g0)
             ((xframe0 * program iset (program_base + !pos0) insts0)%sep *
              FlatToRiscvCommon.functions compile_ext_call program_base e_pos e_impl) ->
        goodMachine t m st0 g0 initialL ->
        runsTo initialL (fun finalL =>
          exists finalTrace finalMH finalRegsH finalMetricsH,
            outcome finalTrace finalMH finalRegsH finalMetricsH /\
            getPc finalL = getPc initialL + !(4 * #(Datatypes.length insts0)) /\
            map.only_differ (getRegs initialL)
                   (union (of_list (modVars_as_list Z.eqb body)) (singleton_set RegisterNames.ra))
                   (getRegs finalL) /\
            (getMetrics finalL - getMetrics initialL <= lowerMetrics (finalMetricsH - mc))%metricsL /\
            goodMachine finalTrace finalMH finalRegsH g0 finalL))
    (HOutcome: forall (t' : Semantics.trace) (m' : mem) (mc' : MetricLog) (st1 : locals),
        outcome t' m' st1 mc' ->
        exists (retvs : list word) (l' : locals),
          map.getmany_of_list st1 retnames = Some retvs /\
          map.putmany_of_list_zip (List.firstn binds_count (reg_class.all reg_class.arg)) retvs l =
          Some l' /\
          post t' m' l' mc'),
      (binds_count <= 8)%nat ->
      map.of_list_zip argnames argvs = Some st0 ->
      exec e_impl_full body t m st0 mc outcome ->
      map.getmany_of_list l (List.firstn (List.length argnames) (reg_class.all reg_class.arg)) =
      Some argvs ->
      map.extends e_impl_full e_impl ->
      good_e_impl e_impl e_pos ->
      fits_stack (stackalloc_words iset body)
                 (rem_stackwords g - framelength (argnames, retnames, body)) e_impl body ->
      FlatToRiscvDef.compile_function iset compile_ext_call e_pos pos (argnames, retnames, body) =
      insts ->
      valid_FlatImp_fun (argnames, retnames, body) ->
      pos mod 4 = 0 ->
      word.unsigned program_base mod 4 = 0 ->
      map.get (getRegs mach) RegisterNames.ra = Some ret_addr ->
      word.unsigned ret_addr mod 4 = 0 ->
      getPc mach = program_base + !pos ->
      iff1 (allx g)
           ((xframe * program iset (program_base + !pos) insts)%sep *
            FlatToRiscvCommon.functions compile_ext_call program_base e_pos e_impl) ->
      goodMachine t m l g mach ->
      runsToNonDet.runsTo (mcomp_sat (Run.run1 iset)) mach (fun finalL =>
        exists finalTrace finalMH finalRegsH finalMetricsH,
          post finalTrace finalMH finalRegsH finalMetricsH /\
          getPc finalL = ret_addr /\
          map.only_differ (getRegs mach)
           (union
              (of_list
                 (list_union Z.eqb (List.firstn binds_count (reg_class.all reg_class.arg)) []))
              (singleton_set RegisterNames.ra)) (getRegs finalL) /\
          (getMetrics finalL - Platform.MetricLogging.addMetricInstructions 100
                                 (Platform.MetricLogging.addMetricJumps 100
                                    (Platform.MetricLogging.addMetricLoads 100
                                       (Platform.MetricLogging.addMetricStores 100 (getMetrics mach)))) <=
             lowerMetrics (finalMetricsH - mc))%metricsL /\
          goodMachine finalTrace finalMH finalRegsH g finalL).
Admitted.

  Lemma compile_stmt_correct:
    (forall resvars extcall argvars,
        compiles_FlatToRiscv_correctly compile_ext_call
          compile_ext_call (SInteract resvars extcall argvars)) ->
    (forall s,
        compiles_FlatToRiscv_correctly compile_ext_call
          (compile_stmt iset compile_ext_call) s).
  Proof.

    intros compile_ext_call_correct.
    unfold compiles_FlatToRiscv_correctly.
    induction 1; intros; unfold goodMachine in *; destruct g.
      all: repeat match goal with
                  | m: _ |- _ => destruct_RiscvMachine m
                  end.
      all: match goal with
           | H: fits_stack _ _ _ ?s |- _ =>
             let h := head_of_app s in is_constructor h;
             inversion H; subst
           end.
      all: fwd.

    -
 idtac "Case compile_stmt_correct/SInteract".
      eapply runsTo_weaken.
      +
 unfold compiles_FlatToRiscv_correctly in *.
        eapply compile_ext_call_correct with
            (postH := post) (g := {| allx := allx |}) (pos := pos)
            (extcall := action) (argvars := argvars) (resvars := resvars) (initialMH := m);
          simpl;
          clear compile_ext_call_correct; cycle -1.
        {
 unfold goodMachine, valid_FlatImp_var in *.
simpl.
ssplit; eauto.
}
        all: eauto using exec.interact, fits_stack_interact.
      +
 simpl.
intros finalL A.
destruct_RiscvMachine finalL.
unfold goodMachine in *.
simpl in *.
        destruct_products.
subst.
        do 4 eexists; ssplit; eauto.

    -
 idtac "Case compile_stmt_correct/SCall".

      unfold good_e_impl, valid_FlatImp_fun in *.
      simpl in *.
      fwd.
      lazymatch goal with
      | H1: map.get e_impl_full fname = ?RHS1,
        H2: map.get e_impl fname = ?RHS2,
        H3: map.extends e_impl_full e_impl |- _ =>
        let F := fresh in assert (RHS1 = RHS2) as F
            by (clear -H1 H2 H3;
                unfold map.extends in H3;
                specialize H3 with (1 := H2); clear H2;
                etransitivity; [symmetry|]; eassumption);
        inversion F; subst; clear F
      end.
      match goal with
      | H: map.get e_impl fname = Some _, G: _ |- _ =>
          pose proof G as e_impl_reduced_props;
          specialize G with (1 := H);
          simpl in G
      end.
      fwd.
      match goal with
      | H: map.get e_pos _ = Some _ |- _ => rename H into GetPos
      end.

      rename stack_trash into old_stackvals.
      rename frame_trash into unused_part_of_caller_frame.

      assert (valid_register RegisterNames.ra) by (cbv; auto).
      assert (valid_register RegisterNames.sp) by (cbv; auto).

      eapply runsToStep.
{
        eapply run_Jal; simpl; try solve [sidecondition]; cycle 2.
        -
 solve_divisibleBy4.
        -
 assumption.
      }
      simpl_MetricRiscvMachine_get_set.
      clear_old_sep_hyps.
      intro mid.
set (mach := mid).
intros.
fwd.
destruct_RiscvMachine mid.
subst.

      remember mach.(getLog) as t.
      assert (GM: goodMachine t m l
                              {| p_sp := p_sp;
                                 rem_stackwords := #(List.length old_stackvals);
                                 rem_framewords := #(List.length unused_part_of_caller_frame);
                                 dframe := dframe;
                                 allx := allx |}
                              mach).
{
        unfold goodMachine; simpl.
        subst mach.
subst.
simpl.
ssplit.
        all: try eauto with map_hints.
      }
      match type of GM with
      | goodMachine _ _ _ ?gh _ => remember gh as g
      end.
      match goal with
      | |- ?G => replace G with
            (runsToNonDet.runsTo (mcomp_sat (Run.run1 iset)) mach
              (fun finalL : RiscvMachineL => exists
                   finalTrace finalMH finalRegsH finalMetricsH,
       post finalTrace finalMH finalRegsH finalMetricsH /\
       getPc finalL = program_base + !pos + !(4 * #1) /\
       map.only_differ initialL_regs
         (union (of_list (list_union Z.eqb binds [])) (singleton_set RegisterNames.ra))
         (getRegs finalL) /\
       (getMetrics finalL - initialL_metrics <= lowerMetrics (finalMetricsH - mc))%metricsL /\
       goodMachine finalTrace finalMH finalRegsH g finalL))
      end.
      2: {
 subst.
reflexivity.
}

      pose proof functions_expose as P.
      match goal with
      | H: map.get e_impl _ = Some _ |- _ => specialize P with (2 := H)
      end.
      specialize P with (1 := GetPos).
      specialize (P program_base).
      match type of P with
      | iff1 _ (functions _ _ _ * ?F)%sep => set (current_fun := F) in *
      end.
      apply iff1ToEq in P.
      match goal with
      | H: iff1 allx _ |- _ => rewrite P in H
      end.
      clear P.
      set (insts := (compile_function e_pos pos0 (argnames, retnames, body))) in *.
      rename xframe into xframe_orig.
      set (xframe := (xframe_orig *
          (ptsto_instr iset (program_base + !pos)
                       (IInstruction (Jal RegisterNames.ra (pos0 - pos))) * emp True))%sep) in *.
      match goal with
      | H: iff1 allx _ |- _ => rename H into A
      end.
      move A before GM.
replace allx with (FlatToRiscvCommon.allx g) in A by (subst; reflexivity).
      rename e_impl into e_impl_orig.
      set (e_impl := (map.remove e_impl_orig fname)) in *.
      rewrite <- (sep_comm current_fun) in A.
rewrite <- sep_assoc in A.
      change current_fun with (program iset (program_base + !pos0) insts) in A.
      eassert (_ = insts) as C.
{
        subst insts.
reflexivity.
      }
      move C after A.
      match goal with
      | H: exec _ body _ _ _ _ _ |- _ => rename H into Exb
      end.
      move Exb before C.
      assert (Ext: map.extends e_impl_full e_impl).
{
        subst e_impl.
eauto with map_hints.
      }
      move Ext before Exb.
      assert (GE: good_e_impl e_impl e_pos).
{
        unfold good_e_impl.
        move e_impl_reduced_props at bottom.
        intros *.
intro G.
        assert (map.get e_impl_orig f = Some fun_impl) as G'.
{
          subst e_impl.
          eapply get_Some_remove; eassumption.
        }
        specialize e_impl_reduced_props with (1 := G').
fwd.
        repeat split; eauto.
      }
      move GE before Ext.
      match goal with
      | H: fits_stack ?x ?y e_impl body |- _ =>
        rename H into FS; move FS after GE;
          replace y with
              (g.(rem_stackwords) - framelength (argnames, retnames, body))%Z in FS
      end.
      2: {
        unfold framelength.
subst g.
simpl.
blia.
      }

      assert (V: valid_FlatImp_fun (argnames, retnames, body)).
{
        simpl.
eauto.
      }
      move V before C.
      match goal with
      | H: pos0 mod 4 = 0 |- _ => rename H into Mo; move Mo after V
      end.
      match goal with
      | H: word.unsigned program_base mod 4 = 0 |- _ => rename H into Mo'; move Mo' after Mo
      end.
      eassert (GPC: mach.(getPc) = program_base + !pos0).
{
        subst mach.
simpl.
solve_word_eq word_ok.
      }
      move GPC after A.
      rename pos into pos_orig, pos0 into pos.
      replace (!(4 * #1)) with (word.of_Z (word := word) 4).
2: {
 solve_word_eq word_ok.
}
      assert (OL: map.of_list_zip argnames argvs = Some st0) by assumption.
      move OL after Exb.
      set (stack_trash := old_stackvals).
      assert (args = List.firstn (Datatypes.length argnames) (reg_class.all reg_class.arg)).
{
        replace (Datatypes.length argnames) with (Datatypes.length args).
1: assumption.
        apply_in_hyps @map.putmany_of_list_zip_sameLength.
        apply_in_hyps @map.getmany_of_list_length.
        congruence.
      }
      subst args.
      let T := type of IHexec in let T' := open_constr:(
        (forall (g : GhostConsts) (e_impl : env) (e_pos : pos_map)
             (program_base : word) (insts : list Instruction) (xframe : mem -> Prop)
             (initialL : RiscvMachineL) (pos : Z),
           map.extends e_impl_full e_impl ->
           good_e_impl e_impl e_pos ->
           fits_stack (rem_framewords g) (rem_stackwords g) e_impl body ->
           compile_stmt iset compile_ext_call e_pos pos (bytes_per_word * rem_framewords g) body =
           insts ->
           FlatImpConstraints.uses_standard_arg_regs body ->
           valid_FlatImp_vars body ->
           pos mod 4 = 0 ->
           word.unsigned program_base mod 4 = 0 ->
           getPc initialL = program_base + !pos ->
           iff1 (FlatToRiscvCommon.allx g)
             ((xframe * program iset (program_base + !pos) insts)%sep *
              functions program_base e_pos e_impl) ->
           goodMachine mid_log m st0 g initialL ->
           runsTo initialL
             (fun finalL : RiscvMachineL =>
              exists
                (finalTrace : Semantics.trace) (finalMH : mem) (finalRegsH : locals)
              (finalMetricsH : MetricLog),
                outcome finalTrace finalMH finalRegsH finalMetricsH /\
                getPc finalL = getPc initialL + !(4 * #(Datatypes.length insts)) /\
                map.only_differ (getRegs initialL)
                  (union (of_list (modVars_as_list Z.eqb body)) (singleton_set RegisterNames.ra))
                  (getRegs finalL) /\

                  _ /\
                goodMachine finalTrace finalMH finalRegsH g finalL))
        ) in replace T with T' in IHexec.
      2: {
        subst.
reflexivity.
      }

      specialize IHexec with (1 := Ext).
      specialize IHexec with (1 := GE).
      specialize IHexec with (6 := Mo').
      match goal with
      | H: FlatImpConstraints.uses_standard_arg_regs body |- _ =>
        specialize IHexec with (3 := H)
      end.
      match goal with
      | H: valid_FlatImp_vars body |- _ => specialize IHexec with (3 := H)
      end.
      move stack_trash at top.
      move IHexec before OL.
      rename H3 into OC.
      rename H0 into GetMany.
      move GetMany after Exb.
      move OC before OL.
      remember (program_base + !pos_orig + !4) as ret_addr.
      assert (map.get mach.(getRegs) RegisterNames.ra = Some ret_addr) as Gra.
{
        subst mach.
cbn.
eauto with map_hints.
      }
      move Gra after GPC.
      assert (word.unsigned ret_addr mod 4 = 0) as RaM by (subst ret_addr; solve_divisibleBy4).
      move RaM before Gra.
      replace mid_log with t in *.
      forget (Datatypes.length binds) as binds_count.
      subst binds.
      eapply runsTo_weaken.
{
        match goal with
        | H: (binds_count <= 8)%nat |- _ => rename H into BC
        end.
        move BC after OC.
        repeat match goal with
               | x := _ |- _ => clearbody x
               end.
        clear - word_ok RVM PRParams PR ext_spec word_riscv_ok locals_ok mem_ok pos_map_ok env_ok
                  IHexec OC BC OL Exb GetMany Ext GE FS C V Mo Mo' Gra RaM GPC A GM.
        revert IHexec OC BC OL Exb GetMany Ext GE FS C V Mo Mo' Gra RaM GPC A GM.
        eapply compile_function_body_correct.
      }
      subst mach.
simpl_MetricRiscvMachine_get_set.
      intros.
fwd.
eexists.
eexists.
eexists.
eexists.
      split; [ eapply H0p0 | ].
      split; eauto 8 with map_hints.
      split; eauto 8 with map_hints.
      split; eauto 8 with map_hints.
      MetricsToRiscv.solve_MetricLog.

    -
 idtac "Case compile_stmt_correct/SLoad".
      progress unfold Memory.load, Memory.load_Z in *.
fwd.
      subst_load_bytes_for_eq.
      assert (x <> RegisterNames.sp).
{
        unfold valid_FlatImp_var, RegisterNames.sp in *.
        blia.
      }
      inline_iff1.
      run1det.
clear H0.
  run1done.

    -
 idtac "Case compile_stmt_correct/SStore".
      inline_iff1.
      simpl_MetricRiscvMachine_get_set.
      unfold Memory.store, Memory.store_Z in *.
      change Memory.store_bytes with (Platform.Memory.store_bytes(word:=word)) in *.
      match goal with
      | H: Platform.Memory.store_bytes _ _ _ _ = _ |- _ =>
        unshelve epose proof (store_bytes_frame H _) as P; cycle 2
      end.
      1: ecancel_assumption.
      destruct P as (finalML & P1 & P2).
      match goal with
      | H: _ = Some m' |- _ => move H at bottom; rename H into A
      end.
      unfold Platform.Memory.store_bytes, Memory.store_Z, Memory.store_bytes in A.
fwd.
      destruct (eq_sym (LittleEndianList.length_le_split (Memory.bytes_per(width:=width) sz) (word.unsigned val))) in t0, E.
      subst_load_bytes_for_eq.
      run1det.
run1done.
      eapply preserve_subset_of_xAddrs.
1: assumption.
      ecancel_assumption.

    -
 idtac "Case compile_stmt_correct/SInlinetable".
      inline_iff1.
      run1det.
      assert (map.get (map.put initialL_regs x (program_base + !pos + !4)) i = Some index).
{
        rewrite map.get_put_diff by congruence.
unfold map.extends in *.
eauto.
      }
      run1det.
      assert (Memory.load sz initialL_mem (program_base + !pos + !4 + index + !0) = Some v).
{
        rewrite word.add_0_r.
        eapply load_from_compile_byte_list.
1: eassumption.
        wcancel_assumption.
      }
      run1det.
      rewrite !map.put_put_same in *.
      assert (x <> RegisterNames.sp).
{
        unfold valid_FlatImp_var, RegisterNames.sp in *.
        blia.
      }
      run1done.

    -
 idtac "Case compile_stmt_correct/SStackalloc".
      rename H1 into IHexec.
      assert (x <> RegisterNames.sp).
{
        unfold valid_FlatImp_var, RegisterNames.sp in *.
        blia.
      }
      assert (valid_register RegisterNames.sp) by (cbv; auto).
      eapply runsToStep.
{
        eapply run_Addi; cycle 4; try safe_sidecond.
        apply valid_FlatImp_var_implies_valid_register.
assumption.
      }
      simpl_MetricRiscvMachine_get_set.
      intros.
fwd.
destruct_RiscvMachine mid.
      assert (bytes_per_word = 4 \/ bytes_per_word = 8) as B48.
{
        unfold bytes_per_word.
destruct width_cases as [E | E]; rewrite E; cbv; auto.
      }
      assert (Memory.bytes_per_word (bitwidth iset) = bytes_per_word) as BPW.
{
        rewrite bitwidth_matches.
reflexivity.
      }
      assert (n / bytes_per_word <= Z.of_nat (List.length frame_trash)) as enough_stack_space.
{
        match goal with
        | H: fits_stack _ _ _ _ |- _ => apply fits_stack_nonneg in H; move H at bottom
        end.
        rewrite BPW in *.
        blia.
      }
      assert (0 <= n / bytes_per_word) as Nonneg.
{
        assert (0 <= n) as K by assumption.
clear -B48 enough_stack_space K.
        Z.div_mod_to_equations.
blia.
      }
      split_from_right frame_trash remaining_frame allocated_stack (Z.to_nat (n / bytes_per_word)).
      match goal with
      | H: Datatypes.length remaining_frame = _ |- _ => clear H
      end.

      edestruct (ll_mem_to_hl_mem mSmall mid_mem
                       (p_sp + !bytes_per_word * !#(Datatypes.length remaining_frame)))
        as (mStack & P & D & Ab).
{
        use_sep_assumption.
        wseplog_pre.
        rewrite (cast_word_array_to_bytes allocated_stack).
        wcancel.
      }
      match reverse goal with
      | H: _ mid_mem |- _ => clear H
      end.
      subst.

      assert ((bytes_per_word * (#(List.length remaining_frame) + n / bytes_per_word) - n)%Z
              = (bytes_per_word * (#(Datatypes.length remaining_frame)))%Z) as DeDiv.
{
        rewrite BPW in *.
        forget bytes_per_word as B.
        forget (Datatypes.length remaining_frame) as L.
        assert (0 <= #L) as A1 by blia.
        assert (0 <= n) as A2 by blia.
        assert (n mod B = 0) as A3 by blia.
        assert (B = 4 \/ B = 8) as A4 by blia.
        clear -A1 A2 A3 A4.
        Z.to_euclidean_division_equations.
blia.
      }

      eapply runsTo_trans; simpl_MetricRiscvMachine_get_set.
      +
 eapply IHexec with (g := {| p_sp := p_sp;
                                    rem_framewords := Z.of_nat (List.length remaining_frame); |})
                           (program_base := program_base)
                           (e_impl := e_impl)
                           (pos := (pos + 4)%Z)
                           (a := p_sp + !bytes_per_word * !#(Datatypes.length remaining_frame))
                           (mStack := mStack)
                           (mCombined := map.putmany mSmall mStack);
          simpl_MetricRiscvMachine_get_set;
          simpl_g_get;
          rewrite ?@length_save_regs, ?@length_load_regs in *;
          simpl_word_exprs word_ok;
          ssplit;
          cycle -5.
        {
 reflexivity.
}
        {
 eassumption.
}
        {
 exists stack_trash, remaining_frame.
ssplit.
1,2: reflexivity.
          wcancel_assumption.
}
        {
 reflexivity.
}
        {
 assumption.
}
        {
 match goal with
          | |- ?G => let t := type of Ab in replace G with t; [exact Ab|f_equal]
          end.
          rewrite @length_flat_map with (n := Z.to_nat bytes_per_word).
