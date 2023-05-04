
(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "-deprecated-hint-rewrite-without-locality,+deprecated-hint-without-locality,+deprecated-instance-without-locality,unsupported-attributes" "-w" "-notation-overridden" "-w" "-deprecated-native-compiler-option" "-native-compiler" "no" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/fiat_crypto_legacy/src" "Crypto" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/fiat_crypto_legacy/bbv/src/bbv" "bbv" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/fiat_crypto_legacy/coqprime/src/Coqprime" "Coqprime" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-I" "/github/workspace/builds/coq/coq-failing/_build_ci/fiat_crypto_legacy/coqprime/src" "-top" "Top.bug_01") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 24 lines to 408 lines, then from 412 lines to 516 lines, then from 521 lines to 466 lines, then from 469 lines to 1076 lines, then from 1081 lines to 691 lines, then from 694 lines to 1041 lines, then from 1045 lines to 804 lines, then from 807 lines to 1305 lines, then from 1309 lines to 1105 lines, then from 1108 lines to 1514 lines, then from 1519 lines to 1352 lines, then from 1355 lines to 1587 lines, then from 1592 lines to 1414 lines, then from 1417 lines to 1865 lines, then from 1869 lines to 1785 lines, then from 1788 lines to 2519 lines, then from 2523 lines to 2305 lines, then from 2308 lines to 3043 lines, then from 3043 lines to 2869 lines, then from 2872 lines to 2937 lines, then from 2942 lines to 2933 lines, then from 2936 lines to 3220 lines, then from 3224 lines to 3030 lines, then from 3033 lines to 3296 lines, then from 3301 lines to 3140 lines, then from 3143 lines to 3411 lines, then from 3415 lines to 3223 lines, then from 3226 lines to 3526 lines, then from 3531 lines to 3346 lines, then from 3349 lines to 3549 lines, then from 3554 lines to 3548 lines, then from 3560 lines to 3397 lines, then from 3400 lines to 3666 lines, then from 3670 lines to 3479 lines, then from 3482 lines to 3763 lines, then from 3768 lines to 3583 lines, then from 3586 lines to 3995 lines, then from 3999 lines to 3813 lines, then from 3816 lines to 4417 lines, then from 4421 lines to 4233 lines, then from 4236 lines to 4267 lines, then from 4272 lines to 4264 lines, then from 4267 lines to 4711 lines, then from 4715 lines to 4533 lines, then from 4536 lines to 4692 lines, then from 4696 lines to 4642 lines, then from 4645 lines to 4680 lines, then from 4685 lines to 4674 lines, then from 4677 lines to 5157 lines, then from 5161 lines to 4986 lines, then from 4989 lines to 5215 lines, then from 5220 lines to 5139 lines, then from 5142 lines to 5624 lines, then from 5629 lines to 5577 lines, then from 5580 lines to 5706 lines, then from 5711 lines to 5705 lines *)
(* coqc version 8.18+alpha compiled with OCaml 4.14.1
   coqtop version runner-zseo-lx5-project-6138686-concurrent-0:/builds/coq/coq/_build/default,(HEAD detached at 0e442216b9) (0e442216b96435abd04509c68407249a51da5dec)
   Expected coqc runtime on this file: 12.074 sec *)
Require Coq.Init.Ltac.
Module Export AdmitTactic.
Module Import LocalFalse.
Inductive False : Prop := .
End LocalFalse.
Axiom proof_admitted : False.
Import Coq.Init.Ltac.
Tactic Notation "admit" := abstract case proof_admitted.
End AdmitTactic.
Require Coq.Arith.Arith.
Require Coq.Arith.Div2.
Require Coq.Arith.PeanoNat.
Require Coq.Arith.Peano_dec.
Require Coq.Arith.Wf_nat.
Require Coq.Bool.Bool.
Require Coq.Bool.Sumbool.
Require Coq.Classes.Equivalence.
Require Coq.Classes.Morphisms.
Require Coq.Classes.Morphisms_Prop.
Require Coq.Classes.RelationClasses.
Require Coq.Classes.RelationPairs.
Require Coq.FSets.FMapFacts.
Require Coq.FSets.FMapInterface.
Require Coq.FSets.FMapPositive.
Require Coq.Init.Nat.
Require Coq.Init.Wf.
Require Coq.Lists.List.
Require Coq.Lists.ListSet.
Require Coq.Lists.SetoidList.
Require Coq.Logic.Eqdep.
Require Coq.Logic.EqdepFacts.
Require Coq.Logic.Eqdep_dec.
Require Coq.NArith.BinNat.
Require Coq.NArith.BinNatDef.
Require Coq.NArith.NArith.
Require Coq.Numbers.BinNums.
Require Coq.Numbers.Natural.Peano.NPeano.
Require Coq.PArith.BinPos.
Require Coq.PArith.BinPosDef.
Require Coq.PArith.PArith.
Require Coq.Program.Equality.
Require Coq.Program.Program.
Require Coq.Program.Tactics.
Require Coq.QArith.QArith.
Require Coq.QArith.QArith_base.
Require Coq.QArith.Qround.
Require Coq.Relations.Relation_Definitions.
Require Coq.Setoids.Setoid.
Require Coq.Strings.String.
Require Coq.Structures.Equalities.
Require Coq.Wellfounded.Inverse_Image.
Require Coq.ZArith.BinInt.
Require Coq.ZArith.BinIntDef.
Require Coq.ZArith.ZArith.
Require Coq.ZArith.ZArith_dec.
Require Coq.ZArith.Zdiv.
Require Coq.ZArith.Znumtheory.
Require Coq.ZArith.Zpow_facts.
Require Coq.ZArith.Zpower.
Require Coq.micromega.Lia.
Require Coq.micromega.Psatz.
Require Coq.nsatz.Nsatz.
Require Coq.setoid_ring.ArithRing.
Require Coq.setoid_ring.Cring.
Require Coq.setoid_ring.Field_tac.
Require Coq.setoid_ring.Field_theory.
Require Coq.setoid_ring.Integral_domain.
Require Coq.setoid_ring.Ncring.
Require Coq.setoid_ring.Ring.
Require Coq.setoid_ring.Ring_polynom.
Require Coq.setoid_ring.Ring_tac.
Require Coq.setoid_ring.Ring_theory.
Require Coqprime.Tactic.Tactic.
Require Coqprime.List.ListAux.
Require Coqprime.List.Permutation.
Require Coqprime.List.Iterator.
Require Coqprime.List.UList.
Require Coqprime.List.ZProgression.
Require Coqprime.N.NatAux.
Require Coqprime.Z.ZCAux.
Require Coqprime.PrimalityTest.Root.
Require Coqprime.PrimalityTest.FGroup.
Require Coqprime.PrimalityTest.IGroup.
Require Coqprime.PrimalityTest.Lagrange.
Require Coqprime.PrimalityTest.EGroup.
Require Coqprime.PrimalityTest.Cyclic.
Require Coqprime.Z.ZSum.
Require Coqprime.PrimalityTest.Euler.
Require Coqprime.PrimalityTest.Zp.
Require Crypto.Util.GlobalSettings.
Require Crypto.Util.FixCoqMistakes.
Require Crypto.Util.Logic.
Require Crypto.Util.Relations.
Require Crypto.Util.Notations.
Require Crypto.Util.Tactics.UniquePose.
Require Crypto.Util.Tactics.DebugPrint.
Require Crypto.Util.Isomorphism.
Require Crypto.Util.HProp.
Require Crypto.Util.Equality.
Require Crypto.Util.Sigma.
Require Crypto.Util.Decidable.
Require Crypto.Algebra.Hierarchy.
Require Crypto.Util.Tactics.Test.
Require Crypto.Util.Tactics.Not.
Require Crypto.Util.Tactics.DoWithHyp.
Require Crypto.Util.Tactics.RewriteHyp.
Require Crypto.Algebra.Monoid.
Require Crypto.Util.Tactics.Head.
Require Crypto.Util.Tactics.BreakMatch.
Require Crypto.Util.Tactics.OnSubterms.
Require Crypto.Util.Tactics.Revert.
Require Crypto.Algebra.Group.
Require Crypto.Algebra.Ring.
Require Crypto.Algebra.Nsatz.
Require Crypto.Util.Factorize.
Require Crypto.Algebra.IntegralDomain.
Require Crypto.Algebra.Field.
Require Crypto.Util.ZUtil.Peano.
Require Crypto.Algebra.ScalarMult.
Require Crypto.Util.Tactics.GetGoal.
Require Crypto.Util.LetIn.
Require Crypto.Util.NatUtil.
Require Crypto.Util.Pointed.
Require Crypto.Util.IffT.
Require Crypto.Util.Prod.
Require Crypto.Util.Tactics.DestructHyps.
Require Crypto.Util.Tactics.DestructHead.
Require Crypto.Util.Tactics.SpecializeBy.
Require Crypto.Util.ListUtil.
Require Crypto.Util.Option.
Require Crypto.Util.Tuple.
Require Crypto.Util.IdfunWithAlt.
Require Crypto.Util.CPSUtil.
Require Crypto.Util.ZUtil.Hints.Core.
Require Crypto.Util.ZUtil.ZSimplify.Core.
Require Crypto.Util.ZUtil.Modulo.PullPush.
Require Crypto.Util.ZUtil.Notations.
Require Crypto.Util.ZUtil.Definitions.
Require Crypto.Util.ZUtil.Zselect.
Require Crypto.Util.Bool.
Require Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Crypto.Util.ZUtil.CPS.
Require Crypto.Util.ZUtil.Tactics.CompareToSgn.
Require Crypto.Util.ZUtil.Div.Bootstrap.
Require Crypto.Util.ZUtil.Modulo.Bootstrap.
Require Crypto.Util.ZUtil.Tactics.DivModToQuotRem.
Require Crypto.Util.ZUtil.Le.
Require Crypto.Util.ZUtil.Hints.ZArith.
Require Crypto.Util.ZUtil.Hints.PullPush.
Require Crypto.Util.ZUtil.Hints.Ztestbit.
Require Crypto.Util.ZUtil.Hints.
Require Crypto.Util.ZUtil.Div.
Require Crypto.Util.ZUtil.Tactics.DivideExistsMul.
Require Crypto.Util.ZUtil.Divide.
Require Crypto.Util.ZUtil.Tactics.ReplaceNegWithPos.
Require Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Crypto.Util.ZUtil.Modulo.
Require Crypto.Util.ZUtil.Odd.
Require Crypto.Util.ZUtil.Tactics.PrimeBound.
Require Crypto.Util.NumTheoryUtil.
Require Crypto.Arithmetic.ModularArithmeticPre.
Require Crypto.Spec.ModularArithmetic.
Require Crypto.Arithmetic.ModularArithmeticTheorems.
Require Crypto.Util.ZUtil.Tactics.ZeroBounds.
Require Crypto.Arithmetic.PrimeFieldTheorems.
Require Crypto.Util.Tactics.VM.
Require Crypto.Arithmetic.Core.
Require Crypto.Arithmetic.CoreUnfolder.
Require Crypto.Util.ZUtil.EquivModulo.
Require Crypto.Arithmetic.Karatsuba.
Require Crypto.Arithmetic.MontgomeryReduction.WordByWord.Abstract.Dependent.Definition.
Require Crypto.Util.ZUtil.MulSplit.
Require Crypto.Util.ZUtil.Tactics.PeelLe.
Require Crypto.Util.ZUtil.Tactics.RewriteModSmall.
Require Crypto.Util.Tactics.SetEvars.
Require Crypto.Util.Tactics.SubstEvars.
Require Crypto.Arithmetic.MontgomeryReduction.WordByWord.Abstract.Dependent.Proofs.
Require Crypto.Arithmetic.Saturated.Core.
Require Crypto.Arithmetic.Saturated.UniformWeight.
Require Crypto.Arithmetic.Saturated.MulSplit.
Require Crypto.Arithmetic.Saturated.Wrappers.
Require Crypto.Util.ZUtil.AddGetCarry.
Require Crypto.Arithmetic.Saturated.AddSub.
Require Crypto.Util.ZUtil.Opp.
Require Crypto.Arithmetic.Saturated.MontgomeryAPI.
Require Crypto.Arithmetic.MontgomeryReduction.WordByWord.Definition.
Require Crypto.Arithmetic.MontgomeryReduction.WordByWord.Proofs.
Require Crypto.Arithmetic.Saturated.CoreUnfolder.
Require Crypto.Arithmetic.Saturated.Freeze.
Require Crypto.Arithmetic.Saturated.MulSplitUnfolder.
Require Crypto.Arithmetic.Saturated.WrappersUnfolder.
Require Crypto.Arithmetic.Saturated.FreezeUnfolder.
Require Crypto.Arithmetic.Saturated.UniformWeightInstances.
Require Crypto.Compilers.Syntax.
Require Crypto.Compilers.Tuple.
Require Crypto.Compilers.SmartMap.
Require Crypto.Compilers.CountLets.
Require Crypto.Compilers.Equality.
Require Crypto.Compilers.TypeInversion.
Require Crypto.Compilers.ExprInversion.
Require Crypto.Compilers.Eta.
Require Crypto.Compilers.EtaInterp.
Require Crypto.Compilers.Wf.
Require Crypto.Compilers.WfInversion.
Require Crypto.Util.Tactics.SplitInContext.
Require Crypto.Compilers.EtaWf.
Require Crypto.Compilers.Inline.
Require Crypto.Compilers.Relations.
Require Crypto.Compilers.WfProofs.
Require Crypto.Compilers.InlineWf.
Require Crypto.Compilers.InterpProofs.
Require Crypto.Compilers.InlineInterp.
Require Crypto.Compilers.InputSyntax.
Require Crypto.Util.Tactics.TransparentAssert.
Require Crypto.Util.Tactics.CacheTerm.
Require Crypto.Compilers.InterpRewriting.
Require Crypto.Util.PointedProp.
Require Crypto.Compilers.InterpSideConditions.
Require Crypto.Compilers.Intros.
Require Crypto.Compilers.Linearize.
Require Crypto.Compilers.LinearizeInterp.
Require Crypto.Compilers.LinearizeWf.
Require Crypto.Compilers.Named.Context.
Require Crypto.Compilers.Named.Syntax.
Require Crypto.Compilers.Named.MapCast.
Require Crypto.Compilers.Named.Wf.
Require Crypto.Compilers.Named.InterpretToPHOAS.
Require Crypto.Compilers.Named.NameUtil.
Require Crypto.Compilers.Named.Compile.
Require Crypto.Compilers.Named.ContextDefinitions.
Require Crypto.Compilers.Named.FMapContext.
Require Crypto.Compilers.Named.PositiveContext.
Require Crypto.Compilers.Named.CountLets.
Require Crypto.Compilers.Named.PositiveContext.Defaults.
Require Crypto.Compilers.MapCastByDeBruijn.
Require Crypto.Compilers.Named.ContextProperties.Tactics.
Require Crypto.Compilers.Named.ContextProperties.
Require Crypto.Compilers.Named.ContextProperties.SmartMap.
Require Crypto.Compilers.Named.InterpSideConditions.
Require Crypto.Compilers.Named.InterpSideConditionsInterp.
Require Crypto.Compilers.Named.MapCastInterp.
Require Crypto.Compilers.Named.MapCastWf.
Require Crypto.Compilers.Named.InterpretToPHOASInterp.
Require Crypto.Compilers.Named.NameUtilProperties.
Require Crypto.Compilers.Named.ContextProperties.NameUtil.
Require Crypto.Compilers.Named.CompileInterp.
Require Crypto.Compilers.Named.CompileInterpSideConditions.
Require Crypto.Compilers.Named.CompileWf.
Require Crypto.Compilers.Named.PositiveContext.DefaultsProperties.
Require Crypto.Compilers.MapCastByDeBruijnInterp.
Require Crypto.Compilers.Named.InterpretToPHOASWf.
Require Crypto.Compilers.MapCastByDeBruijnWf.
Require Crypto.Compilers.Named.ContextProperties.Proper.
Require Crypto.Compilers.Named.RegisterAssign.
Require Crypto.Compilers.Named.EstablishLiveness.
Require Crypto.Compilers.Named.DeadCodeElimination.
Require Crypto.Compilers.Named.RegisterAssignInterp.
Require Crypto.Compilers.Named.DeadCodeEliminationInterp.
Require Crypto.Compilers.Named.GetNames.
Require Crypto.Compilers.Named.WfFromUnit.
Require Crypto.Compilers.Named.WfInterp.
Require Crypto.Util.SideConditions.CorePackages.
Require Crypto.Util.Tactics.SubstLet.
Require Crypto.Compilers.Reify.
Require Crypto.Compilers.RenameBinders.
Require Crypto.Compilers.Rewriter.
Require Crypto.Compilers.RewriterInterp.
Require Crypto.Compilers.RewriterWf.
Require Crypto.Compilers.TypeUtil.
Require Crypto.Util.PartiallyReifiedProp.
Require Crypto.Compilers.WfReflectiveGen.
Require Crypto.Compilers.WfReflective.
Require bbv.Nomega.
Require bbv.ZLib.
Require bbv.N_Z_nat_conversions.
Require bbv.NatLib.
Require bbv.NLib.
Require bbv.DepEq.
Require bbv.DepEqNat.
Require bbv.ReservedNotations.
Require bbv.Word.
Require bbv.WordScope.
Require Crypto.Util.FixedWordSizes.
Require Crypto.Compilers.Z.Syntax.
Require Crypto.Util.ZUtil.Pow.
Require Crypto.Util.ZUtil.Pow2.
Require Crypto.Util.ZUtil.Lnot.
Require Crypto.Util.ZUtil.Testbit.
Require Crypto.Util.NUtil.WithoutReferenceToZ.
Require Crypto.Util.ZUtil.LandLorShiftBounds.
Require Crypto.Util.ZUtil.N2Z.
Require Crypto.Util.WordUtil.
Require Crypto.Util.ZUtil.ZSimplify.Simple.
Require Crypto.Util.ZUtil.Log2.
Require Crypto.Util.ZUtil.Z2Nat.
Require Crypto.Util.FixedWordSizesEquality.
Require Crypto.Compilers.Z.Syntax.Equality.
Require Crypto.Compilers.Z.ArithmeticSimplifier.
Require Crypto.Compilers.Z.TypeInversion.
Require Crypto.Compilers.Z.OpInversion.
Require Crypto.Compilers.Z.ArithmeticSimplifierUtil.
Require Crypto.Util.Sum.
Require Crypto.Compilers.Z.ArithmeticSimplifierInterp.
Require Crypto.Compilers.Z.Syntax.Util.
Require Crypto.Compilers.Z.ArithmeticSimplifierWf.
Require Crypto.Util.ZRange.
Require Crypto.Util.ZRange.Operations.
Require Crypto.Compilers.Z.Bounds.Interpretation.
Require Crypto.Util.ZUtil.Ones.
Require Crypto.Util.ZUtil.Pow2Mod.
Require Crypto.Util.ZUtil.Shift.
Require Crypto.Util.ZUtil.Tactics.SplitMinMax.
Require Crypto.Compilers.Z.Bounds.InterpretationLemmas.Tactics.
Require Crypto.Util.ZUtil.Stabilization.
Require Crypto.Util.Tactics.SpecializeAllWays.
Require Crypto.Util.ZRange.BasicLemmas.
Require Crypto.Util.ZRange.CornersMonotoneBounds.
Require Crypto.Util.Tactics.Contains.
Require Crypto.Util.ZUtil.Tactics.LinearSubstitute.
Require Crypto.Util.ZUtil.Land.
Require Crypto.Util.ZUtil.LandLorBounds.
Require Crypto.Util.ZUtil.Morphisms.
Require Crypto.Compilers.Z.Bounds.InterpretationLemmas.IsBoundedBy.
Require Crypto.Compilers.Z.Bounds.InterpretationLemmas.PullCast.
Require Crypto.Compilers.Z.MapCastByDeBruijn.
Require Crypto.Compilers.Z.Bounds.MapCastByDeBruijn.
Require Crypto.Compilers.Z.InterpSideConditions.
Require Crypto.Compilers.Z.MapCastByDeBruijnInterp.
Require Crypto.Compilers.Z.Bounds.MapCastByDeBruijnInterp.
Require Crypto.Compilers.Z.MapCastByDeBruijnWf.
Require Crypto.Compilers.Z.Bounds.MapCastByDeBruijnWf.
Require Crypto.Compilers.Z.Reify.
Require Crypto.Util.Tactics.ChangeInAll.
Require Crypto.Util.Curry.
Require Crypto.Util.BoundedWord.
Require Crypto.Util.Sigma.Associativity.
Require Crypto.Util.Sigma.MapProjections.
Require Crypto.Util.Logic.ImplAnd.
Require Crypto.Util.Tactics.EvarExists.
Require Crypto.Util.Tactics.PrintContext.
Require Crypto.Util.Tactics.MoveLetIn.
Require Crypto.Util.Tactics.ClearAll.
Require Crypto.Util.Tactics.ClearbodyAll.
Require Crypto.Compilers.Z.Bounds.Pipeline.Glue.
Require Crypto.Compilers.Z.Bounds.RoundUpLemmas.
Require Crypto.Compilers.Z.Bounds.Relax.
Require Crypto.Compilers.Z.Bounds.Pipeline.OutputType.
Require Crypto.Compilers.Z.Inline.
Require Crypto.Compilers.Z.InlineInterp.
Require Crypto.Compilers.Z.InlineWf.
Require Crypto.Compilers.Z.Named.DeadCodeElimination.
Require Crypto.Compilers.Z.Named.RewriteAddToAdc.
Require Crypto.Compilers.Z.RewriteAddToAdc.
Require Crypto.Compilers.Z.RewriteAddToAdcWf.
Require Crypto.Util.ListUtil.FoldBool.
Require Crypto.Compilers.Z.Named.RewriteAddToAdcInterp.
Require Crypto.Compilers.Z.RewriteAddToAdcInterp.
Require Crypto.Util.DefaultedTypes.
Require Crypto.Compilers.Z.Bounds.Pipeline.Definition.
Require Crypto.Util.Tactics.UnfoldArg.
Require Crypto.Util.Tactics.UnifyAbstractReflexivity.
Require Crypto.Compilers.Z.Bounds.Pipeline.ReflectiveTactics.
Require Crypto.Compilers.Z.Bounds.Pipeline.
Require Crypto.Spec.MontgomeryCurve.
Require Crypto.Spec.WeierstrassCurve.
Require Crypto.Curves.Montgomery.Affine.
Require Crypto.Util.Loops.
Require Crypto.Curves.Montgomery.XZ.
Require Crypto.Util.ZUtil.ModInv.
Require Crypto.Specific.Framework.ArithmeticSynthesis.HelperTactics.
Require Crypto.Specific.Framework.RawCurveParameters.
Require Coq.Classes.Morphisms.
Require Coq.Classes.Morphisms_Prop.
Require Coq.Lists.List.
Require Crypto.Util.GlobalSettings.
Require Crypto.Util.FixCoqMistakes.
Require Crypto.Util.Notations.

Module Crypto_DOT_Util_DOT_TagList_WRAPPED.
Module TagList.
Import Coq.Lists.List.
Import Crypto.Util.Notations.
Import ListNotations.

Module Tag.
  Record tagged :=
    { keyT : Type;
      key : keyT;
      valueT : Type;
      value : valueT;
      local : bool }.

  Definition Context := list tagged.

  Definition add_gen {K V} (key' : K) (value' : V) (local' : bool) (ctx : Context) : Context
    := cons {| key := key' ; value := value' ; local := local' |} ctx.

  Definition add {K V} (key' : K) (value' : V) (ctx : Context) : Context
    := add_gen key' value' false ctx.

  Definition add_local {K V} (key' : K) (value' : V) (ctx : Context) : Context
    := add_gen key' value' true ctx.

  Definition strip_local (ctx : Context) : Context
    := List.filter (fun '{| key := k ; value := v ; local := loc |}
                    => negb loc)
                   ctx.

  Definition get_local (ctx : Context) : Context
    := List.filter (fun '{| key := k ; value := v ; local := loc |}
                    => loc)
                   ctx.

  Ltac subst_from_list ls :=
    lazymatch eval hnf in ls with
    | {| value := ?id |} :: ?ls
      => try subst id; subst_from_list ls
    | nil => idtac
    end.

  Ltac subst_local ctx :=
    let loc := (eval cbv [get_local List.filter add add_local add_gen]
                 in (get_local ctx)) in
    subst_from_list loc.

  Ltac strip_local ctx :=
    let upd := (eval cbv [strip_local negb List.filter] in strip_local) in
    eval cbv [add add_local add_gen] in (upd ctx).

  Ltac strip_subst_local ctx :=
    let ret := strip_local ctx in
    let dummy := match goal with
                 | _ => subst_local ctx
                 end in
    ret.

  Ltac update ctx key value :=
    constr:(add key value ctx).

  Ltac local_update ctx key value :=
    constr:(add_local key value ctx).

  Ltac get_gen_cont ctx key' tac_found tac_not_found allow_unfound :=
    lazymatch (eval hnf in ctx) with
    | context[{| key := key' ; value := ?value' |}]
      => tac_found value'
    | context[add_gen key' ?value' _ _] => tac_found value'
    | context[add_local key' ?value' _] => tac_found value'
    | context[add key' ?value' _] => tac_found value'
    | _ => lazymatch allow_unfound with
           | true => tac_not_found ()
           end
    end.

  Ltac update_by_tac_if_not_exists ctx key value_tac :=
    get_gen_cont
      ctx key
      ltac:(fun value' => ctx)
             ltac:(fun _ => let value := value_tac () in
                            update ctx key value)
                    true.

  Ltac update_if_not_exists ctx key value :=
    update_by_tac_if_not_exists ctx key ltac:(fun _ => value).

  Ltac get_gen ctx key' default :=
    get_gen_cont ctx key' ltac:(fun v => v) default true.

  Ltac get_error ctx key' :=
    get_gen_cont ctx key' ltac:(fun v => v) ltac:(fun _ => constr:(I)) false.
  Ltac get_default ctx key' := get_gen ctx key' ltac:(fun _ => constr:(I)).

  Ltac get ctx key' := get_error ctx key'.

  Notation get ctx key' := ltac:(let v := get ctx key' in exact v) (only parsing).

  Notation empty := (@nil tagged).

  Module Export TagNotations.
    Bind Scope tagged_scope with tagged.
    Delimit Scope tagged_scope with tagged.
    Notation "t[ k ~> v ]" := {| key := k ; value := v ; local := _ |} : tagged_scope.
    Notation "l[ k ~> v ]" := {| key := k ; value := v ; local := true |} : tagged_scope.
  End TagNotations.
End Tag.

Export Tag.TagNotations.

End TagList.

End Crypto_DOT_Util_DOT_TagList_WRAPPED.
Module Export Crypto_DOT_Util_DOT_TagList.
Module Export Crypto.
Module Export Util.
Module TagList.
Include Crypto_DOT_Util_DOT_TagList_WRAPPED.TagList.
End TagList.

End Util.

End Crypto.

End Crypto_DOT_Util_DOT_TagList.
Module Export Crypto_DOT_Specific_DOT_Framework_DOT_CurveParameters.
Module Export Crypto.
Module Export Specific.
Module Export Framework.
Module CurveParameters.
Import Coq.QArith.Qround.
Export Coq.ZArith.BinInt.
Export Coq.Lists.List.
Export Crypto.Util.ZUtil.Notations.
Import Crypto.Util.Tactics.CacheTerm.
Import Crypto.Specific.Framework.RawCurveParameters.
Import Crypto.Util.TagList.

Local Set Primitive Projections.

Module Export Notations := RawCurveParameters.Notations.

Module TAG.

  Inductive tags := CP | sz | base | bitwidth | s | c | carry_chains | a24 | coef_div_modulus | goldilocks | karatsuba | montgomery | freeze | ladderstep | upper_bound_of_exponent_tight | upper_bound_of_exponent_loose | allowable_bit_widths | freeze_allowable_bit_widths | modinv_fuel | mul_code | square_code.
End TAG.

Module Export CurveParameters.
  Local Notation eval p :=
    (List.fold_right Z.add 0%Z (List.map (fun t => fst t * snd t) p)).

  Ltac do_compute v :=
    let v' := (eval vm_compute in v) in v'.
  Notation compute v
    := (ltac:(let v' := do_compute v in exact v'))
         (only parsing).
  Local Notation defaulted opt_v default
    := (match opt_v with
        | Some v => v
        | None => default
        end)
         (only parsing).
  Record CurveParameters :=
    {
      sz : nat;
      base : Q;
      bitwidth : Z;
      s : Z;
      c : list limb;
      carry_chains : list (list nat);
      a24 : option Z;
      coef_div_modulus : nat;

      goldilocks : bool;
      karatsuba : bool;
      montgomery : bool;
      freeze : bool;
      ladderstep : bool;

      mul_code : option (Z^sz -> Z^sz -> Z^sz);
      square_code : option (Z^sz -> Z^sz);
      upper_bound_of_exponent_tight : Z -> Z;
      upper_bound_of_exponent_loose : Z -> Z;
      allowable_bit_widths : list nat;
      freeze_allowable_bit_widths : list nat;
      modinv_fuel : nat
    }.

  Declare Reduction cbv_CurveParameters
    := cbv [sz
              base
              bitwidth
              s
              c
              carry_chains
              a24
              coef_div_modulus
              goldilocks
              karatsuba
              montgomery
              freeze
              ladderstep
              mul_code
              square_code
              upper_bound_of_exponent_tight
              upper_bound_of_exponent_loose
              allowable_bit_widths
              freeze_allowable_bit_widths
              modinv_fuel].

  Ltac default_mul CP :=
    lazymatch (eval hnf in (mul_code CP)) with
    | None => reflexivity
    | Some ?mul_code
      => instantiate (1:=mul_code)
    end.
  Ltac default_square CP :=
    lazymatch (eval hnf in (square_code CP)) with
    | None => reflexivity
    | Some ?square_code
      => instantiate (1:=square_code)
    end.

  Local Notation list_n_if_not_exists n ls :=
    (if existsb (Nat.eqb n) ls
     then nil
     else [n]%nat)
      (only parsing).
  Local Notation list_8_if_not_exists ls
    := (list_n_if_not_exists 8%nat ls) (only parsing).
  Local Notation list_1_if_not_exists ls
    := (list_n_if_not_exists 1%nat ls) (only parsing).

  Definition fill_defaults_CurveParameters (CP : RawCurveParameters.CurveParameters)
    : CurveParameters
    := Eval cbv_RawCurveParameters in
        let sz := RawCurveParameters.sz CP in
        let base := RawCurveParameters.base CP in
        let bitwidth := RawCurveParameters.bitwidth CP in
        let montgomery := RawCurveParameters.montgomery CP in
        let karatsuba := defaulted (RawCurveParameters.karatsuba CP) false in
        let s := RawCurveParameters.s CP in
        let c := RawCurveParameters.c CP in
        let freeze
            := defaulted
                 (RawCurveParameters.freeze CP)
                 (s =? 2^(Qceiling (base * sz))) in
        let goldilocks :=
            defaulted
              (RawCurveParameters.goldilocks CP)
              (let k := Z.log2 s / 2 in
               (s - eval c) =? (2^(2*k) - 2^k - 1)) in
        let allowable_bit_widths
            := defaulted
                 (RawCurveParameters.allowable_bit_widths CP)
                 ((if montgomery
                   then [1; 8]
                   else nil)
                    ++ (Z.to_nat bitwidth :: 2*Z.to_nat bitwidth :: nil))%nat in
        let upper_bound_of_exponent_tight
            := defaulted (RawCurveParameters.upper_bound_of_exponent_tight CP)
                         (if montgomery
                          then (fun exp => (2^exp - 1)%Z)
                          else (fun exp => (2^exp + 2^(exp-3))%Z))
          in
        let upper_bound_of_exponent_loose
            := defaulted (RawCurveParameters.upper_bound_of_exponent_loose CP)
                         (if montgomery
                          then (fun exp => (2^exp - 1)%Z)
                          else (fun exp => (3 * upper_bound_of_exponent_tight exp)%Z)) in
        {|
          sz := sz;
          base := base;
          bitwidth := bitwidth;
          s := s;
          c := c;
          carry_chains := defaulted (RawCurveParameters.carry_chains CP) [seq 0 (pred sz); [0; 1]]%nat;
          a24 := RawCurveParameters.a24 CP;
          coef_div_modulus := defaulted (RawCurveParameters.coef_div_modulus CP) 0%nat;

          goldilocks := goldilocks;
          karatsuba := karatsuba;
          montgomery := montgomery;
          freeze := freeze;
          ladderstep := RawCurveParameters.ladderstep CP;

          mul_code := RawCurveParameters.mul_code CP;
          square_code := RawCurveParameters.square_code CP;
          upper_bound_of_exponent_tight := upper_bound_of_exponent_tight;
          upper_bound_of_exponent_loose := upper_bound_of_exponent_loose;

          allowable_bit_widths := allowable_bit_widths;
          freeze_allowable_bit_widths
          := defaulted
               (RawCurveParameters.freeze_extra_allowable_bit_widths CP)
               ((list_1_if_not_exists allowable_bit_widths)
                  ++ (list_8_if_not_exists allowable_bit_widths))
               ++ allowable_bit_widths;
          modinv_fuel := defaulted (RawCurveParameters.modinv_fuel CP) (Z.to_nat (Z.log2_up s))
        |}.

  Ltac get_fill_CurveParameters CP :=
    let CP := (eval hnf in CP) in
    let v := (eval cbv [fill_defaults_CurveParameters] in
                 (fill_defaults_CurveParameters CP)) in
    let v := (eval cbv_CurveParameters in v) in
    let v := (eval cbv_RawCurveParameters in v) in
    lazymatch v with
    | ({|
          sz := ?sz';
          base := ?base';
          bitwidth := ?bitwidth';
          s := ?s';
          c := ?c';
          carry_chains := ?carry_chains';
          a24 := ?a24';
          coef_div_modulus := ?coef_div_modulus';
          goldilocks := ?goldilocks';
          karatsuba := ?karatsuba';
          montgomery := ?montgomery';
          freeze := ?freeze';
          ladderstep := ?ladderstep';
          mul_code := ?mul_code';
          square_code := ?square_code';
          upper_bound_of_exponent_tight := ?upper_bound_of_exponent_tight';
          upper_bound_of_exponent_loose := ?upper_bound_of_exponent_loose';
          allowable_bit_widths := ?allowable_bit_widths';
          freeze_allowable_bit_widths := ?freeze_allowable_bit_widths';
          modinv_fuel := ?modinv_fuel'
        |})
      => let sz' := do_compute sz' in
         let base' := do_compute base' in
         let bitwidth' := do_compute bitwidth' in
         let carry_chains' := do_compute carry_chains' in
         let goldilocks' := do_compute goldilocks' in
         let karatsuba' := do_compute karatsuba' in
         let montgomery' := do_compute montgomery' in
         let freeze' := do_compute freeze' in
         let ladderstep' := do_compute ladderstep' in
         let allowable_bit_widths' := do_compute allowable_bit_widths' in
         let freeze_allowable_bit_widths' := do_compute freeze_allowable_bit_widths' in
         let modinv_fuel' := do_compute modinv_fuel' in
         constr:({|
                    sz := sz';
                    base := base';
                    bitwidth := bitwidth';
                    s := s';
                    c := c';
                    carry_chains := carry_chains';
                    a24 := a24';
                    coef_div_modulus := coef_div_modulus';
                    goldilocks := goldilocks';
                    karatsuba := karatsuba';
                    montgomery := montgomery';
                    freeze := freeze';
                    ladderstep := ladderstep';
                    mul_code := mul_code';
                    square_code := square_code';
                    upper_bound_of_exponent_tight := upper_bound_of_exponent_tight';
                    upper_bound_of_exponent_loose := upper_bound_of_exponent_loose';
                    allowable_bit_widths := allowable_bit_widths';
                    freeze_allowable_bit_widths := freeze_allowable_bit_widths';
                    modinv_fuel := modinv_fuel'
                  |})
    end.
  Notation fill_CurveParameters CP := ltac:(let v := get_fill_CurveParameters CP in exact v) (only parsing).

  Ltac internal_pose_of_CP CP proj id :=
    let P_proj := (eval cbv_CurveParameters in (proj CP)) in
    cache_term P_proj id.
  Ltac pose_base CP base :=
    internal_pose_of_CP CP CurveParameters.base base.
  Ltac pose_sz CP sz :=
    internal_pose_of_CP CP CurveParameters.sz sz.
  Ltac pose_bitwidth CP bitwidth :=
    internal_pose_of_CP CP CurveParameters.bitwidth bitwidth.
  Ltac pose_s CP s :=
    internal_pose_of_CP CP CurveParameters.s s.
  Ltac pose_c CP c :=
    internal_pose_of_CP CP CurveParameters.c c.
  Ltac pose_carry_chains CP carry_chains :=
    internal_pose_of_CP CP CurveParameters.carry_chains carry_chains.
  Ltac pose_a24 CP a24 :=
    internal_pose_of_CP CP CurveParameters.a24 a24.
  Ltac pose_coef_div_modulus CP coef_div_modulus :=
    internal_pose_of_CP CP CurveParameters.coef_div_modulus coef_div_modulus.
  Ltac pose_goldilocks CP goldilocks :=
    internal_pose_of_CP CP CurveParameters.goldilocks goldilocks.
  Ltac pose_karatsuba CP karatsuba :=
    internal_pose_of_CP CP CurveParameters.karatsuba karatsuba.
  Ltac pose_montgomery CP montgomery :=
    internal_pose_of_CP CP CurveParameters.montgomery montgomery.
  Ltac pose_freeze CP freeze :=
    internal_pose_of_CP CP CurveParameters.freeze freeze.
  Ltac pose_ladderstep CP ladderstep :=
    internal_pose_of_CP CP CurveParameters.ladderstep ladderstep.
  Ltac pose_allowable_bit_widths CP allowable_bit_widths :=
    internal_pose_of_CP CP CurveParameters.allowable_bit_widths allowable_bit_widths.
  Ltac pose_freeze_allowable_bit_widths CP freeze_allowable_bit_widths :=
    internal_pose_of_CP CP CurveParameters.freeze_allowable_bit_widths freeze_allowable_bit_widths.
  Ltac pose_upper_bound_of_exponent_tight CP upper_bound_of_exponent_tight :=
    internal_pose_of_CP CP CurveParameters.upper_bound_of_exponent_tight upper_bound_of_exponent_tight.
  Ltac pose_upper_bound_of_exponent_loose CP upper_bound_of_exponent_loose :=
    internal_pose_of_CP CP CurveParameters.upper_bound_of_exponent_loose upper_bound_of_exponent_loose.
  Ltac pose_modinv_fuel CP modinv_fuel :=
    internal_pose_of_CP CP CurveParameters.modinv_fuel modinv_fuel.
  Ltac pose_mul_code CP mul_code :=
    internal_pose_of_CP CP CurveParameters.mul_code mul_code.
  Ltac pose_square_code CP square_code :=
    internal_pose_of_CP CP CurveParameters.square_code square_code.

  Ltac add_base pkg :=
    let CP := Tag.get pkg TAG.CP in
    let base := fresh "base" in
    let base := pose_base CP base in
    Tag.update pkg TAG.base base.

  Ltac add_sz pkg :=
    let CP := Tag.get pkg TAG.CP in
    let sz := fresh "sz" in
    let sz := pose_sz CP sz in
    Tag.update pkg TAG.sz sz.

  Ltac add_bitwidth pkg :=
    let CP := Tag.get pkg TAG.CP in
    let bitwidth := fresh "bitwidth" in
    let bitwidth := pose_bitwidth CP bitwidth in
    Tag.update pkg TAG.bitwidth bitwidth.

  Ltac add_s pkg :=
    let CP := Tag.get pkg TAG.CP in
    let s := fresh "s" in
    let s := pose_s CP s in
    Tag.update pkg TAG.s s.

  Ltac add_c pkg :=
    let CP := Tag.get pkg TAG.CP in
    let c := fresh "c" in
    let c := pose_c CP c in
    Tag.update pkg TAG.c c.

  Ltac add_carry_chains pkg :=
    let CP := Tag.get pkg TAG.CP in
    let carry_chains := fresh "carry_chains" in
    let carry_chains := pose_carry_chains CP carry_chains in
    Tag.update pkg TAG.carry_chains carry_chains.

  Ltac add_a24 pkg :=
    let CP := Tag.get pkg TAG.CP in
    let a24 := fresh "a24" in
    let a24 := pose_a24 CP a24 in
    Tag.update pkg TAG.a24 a24.

  Ltac add_coef_div_modulus pkg :=
    let CP := Tag.get pkg TAG.CP in
    let coef_div_modulus := fresh "coef_div_modulus" in
    let coef_div_modulus := pose_coef_div_modulus CP coef_div_modulus in
    Tag.update pkg TAG.coef_div_modulus coef_div_modulus.

  Ltac add_goldilocks pkg :=
    let CP := Tag.get pkg TAG.CP in
    let goldilocks := fresh "goldilocks" in
    let goldilocks := pose_goldilocks CP goldilocks in
    Tag.update pkg TAG.goldilocks goldilocks.

  Ltac add_karatsuba pkg :=
    let CP := Tag.get pkg TAG.CP in
    let karatsuba := fresh "karatsuba" in
    let karatsuba := pose_karatsuba CP karatsuba in
    Tag.update pkg TAG.karatsuba karatsuba.

  Ltac add_montgomery pkg :=
    let CP := Tag.get pkg TAG.CP in
    let montgomery := fresh "montgomery" in
    let montgomery := pose_montgomery CP montgomery in
    Tag.update pkg TAG.montgomery montgomery.

  Ltac add_freeze pkg :=
    let CP := Tag.get pkg TAG.CP in
    let freeze := fresh "freeze" in
    let freeze := pose_freeze CP freeze in
    Tag.update pkg TAG.freeze freeze.

  Ltac add_ladderstep pkg :=
    let CP := Tag.get pkg TAG.CP in
    let ladderstep := fresh "ladderstep" in
    let ladderstep := pose_ladderstep CP ladderstep in
    Tag.update pkg TAG.ladderstep ladderstep.

  Ltac add_allowable_bit_widths pkg :=
    let CP := Tag.get pkg TAG.CP in
    let allowable_bit_widths := fresh "allowable_bit_widths" in
    let allowable_bit_widths := pose_allowable_bit_widths CP allowable_bit_widths in
    Tag.update pkg TAG.allowable_bit_widths allowable_bit_widths.

  Ltac add_freeze_allowable_bit_widths pkg :=
    let CP := Tag.get pkg TAG.CP in
    let freeze_allowable_bit_widths := fresh "freeze_allowable_bit_widths" in
    let freeze_allowable_bit_widths := pose_freeze_allowable_bit_widths CP freeze_allowable_bit_widths in
    Tag.update pkg TAG.freeze_allowable_bit_widths freeze_allowable_bit_widths.

  Ltac add_upper_bound_of_exponent_tight pkg :=
    let CP := Tag.get pkg TAG.CP in
    let upper_bound_of_exponent_tight := fresh "upper_bound_of_exponent_tight" in
    let upper_bound_of_exponent_tight := pose_upper_bound_of_exponent_tight CP upper_bound_of_exponent_tight in
    Tag.update pkg TAG.upper_bound_of_exponent_tight upper_bound_of_exponent_tight.

  Ltac add_upper_bound_of_exponent_loose pkg :=
    let CP := Tag.get pkg TAG.CP in
    let upper_bound_of_exponent_loose := fresh "upper_bound_of_exponent_loose" in
    let upper_bound_of_exponent_loose := pose_upper_bound_of_exponent_loose CP upper_bound_of_exponent_loose in
    Tag.update pkg TAG.upper_bound_of_exponent_loose upper_bound_of_exponent_loose.

  Ltac add_modinv_fuel pkg :=
    let CP := Tag.get pkg TAG.CP in
    let modinv_fuel := fresh "modinv_fuel" in
    let modinv_fuel := pose_modinv_fuel CP modinv_fuel in
    Tag.update pkg TAG.modinv_fuel modinv_fuel.

  Ltac add_mul_code pkg :=
    let CP := Tag.get pkg TAG.CP in
    let mul_code := fresh "mul_code" in
    let mul_code := pose_mul_code CP mul_code in
    Tag.update pkg TAG.mul_code mul_code.

  Ltac add_square_code pkg :=
    let CP := Tag.get pkg TAG.CP in
    let square_code := fresh "square_code" in
    let square_code := pose_square_code CP square_code in
    Tag.update pkg TAG.square_code square_code.

  Ltac add_CurveParameters_package pkg :=
    let pkg := add_base pkg in
    let pkg := add_sz pkg in
    let pkg := add_bitwidth pkg in
    let pkg := add_s pkg in
    let pkg := add_c pkg in
    let pkg := add_carry_chains pkg in
    let pkg := add_a24 pkg in
    let pkg := add_coef_div_modulus pkg in
    let pkg := add_goldilocks pkg in
    let pkg := add_karatsuba pkg in
    let pkg := add_montgomery pkg in
    let pkg := add_freeze pkg in
    let pkg := add_ladderstep pkg in
    let pkg := add_allowable_bit_widths pkg in
    let pkg := add_freeze_allowable_bit_widths pkg in
    let pkg := add_upper_bound_of_exponent_tight pkg in
    let pkg := add_upper_bound_of_exponent_loose pkg in
    let pkg := add_modinv_fuel pkg in
    let pkg := add_mul_code pkg in
    let pkg := add_square_code pkg in
    Tag.strip_subst_local pkg.
End CurveParameters.

End CurveParameters.

End Framework.

End Specific.

End Crypto.

End Crypto_DOT_Specific_DOT_Framework_DOT_CurveParameters.
Module Crypto_DOT_Util_DOT_QUtil_WRAPPED.
Module QUtil.
Import Coq.ZArith.ZArith Coq.QArith.QArith Coq.QArith.Qround.
Import Coq.micromega.Lia Coq.Classes.Morphisms Coq.Classes.Morphisms_Prop.
Import Crypto.Util.Decidable.
Import Crypto.Util.ZUtil.Tactics.DivModToQuotRem.
Import Crypto.Util.ZUtil.Morphisms.

Local Open Scope Z_scope.

Lemma Qfloor_le_add a b :  Qfloor a + Qfloor b <= Qfloor (a + b).
  destruct a as [x y], b as [a b]; cbv [Qceiling Qfloor Qplus Qopp QArith_base.Qden QArith_base.Qnum].
  Z.div_mod_to_quot_rem_in_goal; nia.
Qed.

Lemma Qceiling_le_add a b : Qceiling (a + b) <= Qceiling a + Qceiling b.
  destruct a as [x y], b as [a b]; cbv [Qceiling Qfloor Qplus Qopp QArith_base.Qden QArith_base.Qnum].
  Z.div_mod_to_quot_rem_in_goal.
nia.
Qed.

Lemma add_floor_l_le_ceiling a b : Qfloor a + Qceiling b <= Qceiling (a + b).
  destruct a as [x y], b as [a b]; cbv [Qceiling Qfloor Qplus Qopp QArith_base.Qden QArith_base.Qnum].
  Z.div_mod_to_quot_rem_in_goal; nia.
Qed.

Lemma Zle_floor_ceiling  a : Z.le (Qfloor a) (Qceiling a).
  pose proof Qle_floor_ceiling.
  destruct a as [x y]; cbv [Qceiling Qfloor Qplus Qopp QArith_base.Qden QArith_base.Qnum].
  Z.div_mod_to_quot_rem_in_goal; nia.
Qed.

Section pow_ceil_mul_nat.
  Context b f (b_nz:0 <> b) (f_pos:(0 <= f)%Q).
  Local Notation wt i := (b^Qceiling (f * inject_Z (Z.of_nat i))) (only parsing).

  Lemma zero_le_ceil_mul_nat i :
    0 <= Qceiling (f * inject_Z (Z.of_nat i))%Q.
  Proof.
    rewrite Zle_Qle.
    eapply Qle_trans; [|eapply Qle_ceiling].
    eapply Qle_trans; [|eapply (Qmult_le_compat_r 0)]; trivial.
    cbv; discriminate.
    apply (Qle_trans _ (inject_Z 0)); [vm_decide|].
    change 0%Q with (inject_Z 0).
    rewrite <-Zle_Qle.
    eapply Zle_0_nat.
  Qed.

  Lemma pow_ceil_mul_nat_nonzero
    : forall i, wt i <> 0.
  Proof.
    intros.
    eapply Z.pow_nonzero; try lia.
    eapply zero_le_ceil_mul_nat.
  Qed.

  Lemma pow_ceil_mul_nat_nonneg (Hb : 0 <= b)
    : forall i, 0 <= wt i.
  Proof.
    intros.
    apply Z.pow_nonneg; assumption.
  Qed.

  Lemma pow_ceil_mul_S i :
    wt (S i) =
    (b ^ (Qceiling (f + f * inject_Z (Z.of_nat i)) - Qceiling (f * inject_Z (Z.of_nat i))) * wt i).
  Proof.
    rewrite Nat2Z.inj_succ.
    rewrite <-Z.add_1_l.
    rewrite inject_Z_plus.
    change (inject_Z 1) with 1%Q.
    rewrite Qmult_plus_distr_r, Qmult_1_r.
    let g := constr:((f * inject_Z (Z.of_nat i))%Q) in
    replace (Qceiling (f+g)) with ((Qceiling (f+g)-Qceiling g)+Qceiling g) at 1 by lia.
    rewrite Z.pow_add_r; [reflexivity|eapply Zle_minus_le_0|apply zero_le_ceil_mul_nat].
    eapply Qceiling_resp_le.
    rewrite <-Qplus_0_l at 1.
    eapply Qplus_le_compat;
      auto with qarith.
  Qed.

  Lemma pow_ceil_mul_nat_multiples i :
    wt (S i) mod (wt i) = 0.
  Proof.
    rewrite pow_ceil_mul_S, Z_mod_mult; reflexivity.
  Qed.
End pow_ceil_mul_nat.

Section pow_ceil_mul_nat2.
  Context b f (b_pos:0 < b) (f_ge_1:(1 <= f)%Q).
  Local Notation wt i := (b^Qceiling (f * inject_Z (Z.of_nat i))) (only parsing).

  Lemma pow_ceil_mul_nat_pos
    : forall i, wt i > 0.
  Proof.
    intros.
    eapply Z.gt_lt_iff.
    eapply Z.pow_pos_nonneg; [assumption|].
    eapply zero_le_ceil_mul_nat.
    eapply (Qle_trans _ 1 _); [vm_decide|assumption].
  Qed.

  Lemma pow_ceil_mul_nat_divide i :
    wt (S i) / (wt i) > 0.
  Proof.
    rewrite pow_ceil_mul_S.
    rewrite Z_div_mult_full; [|apply pow_ceil_mul_nat_nonzero].
    rewrite Z.gt_lt_iff.
    eapply Z.pow_pos_nonneg; [assumption|].
    etransitivity; [|eapply Z.sub_le_ge_Proper].
    2:eapply add_floor_l_le_ceiling.
    2:eapply Z.ge_le_iff; reflexivity.
    assert (1 <= Qfloor f); [|lia].
    change 1%Z with (Qfloor 1).
    eapply Qfloor_resp_le.
    all: trivial; try lia; (eapply (Qle_trans _ 1 _); [vm_decide|assumption]).
  Qed.

  Lemma pow_ceil_mul_nat_divide_nonzero i :
    wt (S i) / (wt i) <> 0.
  Proof.
    pose proof (pow_ceil_mul_nat_divide i).
    lia.
  Qed.

  Lemma pow_ceil_mul_nat_divide_upperbound i :
    wt (S i) / (wt i) <= b^Qceiling f.
  Proof.
    rewrite pow_ceil_mul_S.
    rewrite Z_div_mult_full; [|apply pow_ceil_mul_nat_nonzero].
    all:[ > | lia | eapply (Qle_trans _ 1 _); [vm_decide|assumption].. ].
    apply Z.pow_le_mono_r; [ assumption | ].
    rewrite Z.le_sub_le_add_l, Z.add_comm.
    etransitivity; [ | apply Qceiling_le_add ].
    reflexivity.
  Qed.
End pow_ceil_mul_nat2.

End QUtil.

End Crypto_DOT_Util_DOT_QUtil_WRAPPED.
Module Export Crypto_DOT_Util_DOT_QUtil.
Module Export Crypto.
Module Export Util.
Module QUtil.
Include Crypto_DOT_Util_DOT_QUtil_WRAPPED.QUtil.
End QUtil.

End Util.

End Crypto.

End Crypto_DOT_Util_DOT_QUtil.
Module Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_Base_WRAPPED.
Module Base.
Import Coq.ZArith.ZArith Coq.ZArith.BinIntDef.
Import Coq.Lists.List.
Import ListNotations.
Import Coq.micromega.Lia Coq.Classes.Morphisms Coq.Classes.Morphisms_Prop.
Import Coq.QArith.QArith_base.
Import Crypto.Arithmetic.Core.
Import B.
Import Crypto.Specific.Framework.CurveParameters.
Import Crypto.Specific.Framework.ArithmeticSynthesis.HelperTactics.
Import Crypto.Util.QUtil.
Export Crypto.Util.Decidable.
Import Crypto.Util.Relations.
Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Import Crypto.Util.Tactics.CacheTerm.

Ltac pose_r bitwidth r :=
  cache_term_with_type_by
    positive
    ltac:(let v := (eval vm_compute in (Z.to_pos (2^bitwidth))) in exact v)
           r.

Ltac pose_m s c m :=
  let v := (eval vm_compute in (Z.to_pos (s - Associational.eval c))) in
  cache_term v m.

Section wt.
  Import Coq.QArith.QArith Coq.QArith.Qround.
  Local Coercion QArith_base.inject_Z : Z >-> Q.
  Local Coercion Z.of_nat : nat >-> Z.
  Local Coercion Z.pos : positive >-> Z.
  Definition wt_gen (base : Q) (i:nat) : Z := 2^Qceiling(base*i).
End wt.

Section gen.
  Context (base : Q)
          (m : positive)
          (sz : nat)
          (coef_div_modulus : nat)
          (base_pos : (1 <= base)%Q).

  Local Notation wt := (wt_gen base).

  Definition sz2' := ((sz * 2) - 1)%nat.

  Definition half_sz' := (sz / 2)%nat.

  Definition m_enc'
    := Positional.encode (modulo_cps:=@modulo_cps) (div_cps:=@div_cps) (n:=sz) wt (Z.pos m).

  Lemma sz2'_nonzero
        (sz_nonzero : sz <> 0%nat)
    : sz2' <> 0%nat.
  Proof using Type.
clear -sz_nonzero; cbv [sz2']; lia.
Qed.

  Local Ltac Q_cbv :=
    cbv [wt_gen Qround.Qceiling QArith_base.Qmult QArith_base.Qdiv QArith_base.inject_Z QArith_base.Qden QArith_base.Qnum QArith_base.Qopp Qround.Qfloor QArith_base.Qinv QArith_base.Qle QArith_base.Qeq Z.of_nat] in *.
  Lemma wt_gen0_1 : wt 0 = 1.
  Proof using Type.
    Q_cbv; simpl.
    autorewrite with zsimplify_const; reflexivity.
  Qed.

  Lemma wt_gen_nonzero : forall i, wt i <> 0.
  Proof using base_pos.
    eapply pow_ceil_mul_nat_nonzero; [ lia | ].
    destruct base; Q_cbv; lia.
  Qed.

  Lemma wt_gen_nonneg : forall i, 0 <= wt i.
  Proof using Type.
apply pow_ceil_mul_nat_nonneg; lia.
Qed.

  Lemma wt_gen_pos : forall i, wt i > 0.
  Proof using base_pos.
    intro i; pose proof (wt_gen_nonzero i); pose proof (wt_gen_nonneg i).
    lia.
  Qed.

  Lemma wt_gen_multiples : forall i, wt (S i) mod (wt i) = 0.
  Proof using base_pos.
    apply pow_ceil_mul_nat_multiples; destruct base; Q_cbv; lia.
  Qed.

  Section divides.
    Lemma wt_gen_divides
      : forall i, wt (S i) / wt i > 0.
    Proof using base_pos.
      apply pow_ceil_mul_nat_divide; [ lia | ].
      destruct base; Q_cbv; lia.
    Qed.

    Lemma wt_gen_divides'
      : forall i, wt (S i) / wt i <> 0.
    Proof using base_pos.
      symmetry; apply Z.lt_neq, Z.gt_lt_iff, wt_gen_divides; assumption.
    Qed.

    Lemma wt_gen_div_bound
      : forall i, wt (S i) / wt i <= wt 1.
    Proof using base_pos.
      intro; etransitivity.
      eapply pow_ceil_mul_nat_divide_upperbound; [ lia | ].
      all:destruct base; Q_cbv; autorewrite with zsimplify_const;
        rewrite ?Pos.mul_1_l, ?Pos.mul_1_r; try assumption; lia.
    Qed.
    Lemma wt_gen_divides_chain
          carry_chain
      : forall i (H:In i carry_chain), wt (S i) / wt i <> 0.
    Proof using base_pos.
intros i ?; apply wt_gen_divides'; assumption.
Qed.

    Lemma wt_gen_divides_chains
          carry_chains
      : List.fold_right
          and
          True
          (List.map
             (fun carry_chain
              => forall i (H:In i carry_chain), wt (S i) / wt i <> 0)
             carry_chains).
    Proof using base_pos.
      induction carry_chains as [|carry_chain carry_chains IHcarry_chains];
        constructor; eauto using wt_gen_divides_chain.
    Qed.
  End divides.

  Definition coef'
    := (fix addm (acc: Z^sz) (ctr : nat) : Z^sz :=
          match ctr with
          | O => acc
          | S n => addm (Positional.add_cps wt acc m_enc' id) n
          end) (Positional.zeros sz) coef_div_modulus.

  Lemma coef_mod'
    : mod_eq m (Positional.eval (n:=sz) wt coef') 0.
  Proof using base_pos.
    cbv [coef' m_enc'].
    remember (Positional.zeros sz) as v eqn:Hv.
    assert (Hv' : mod_eq m (Positional.eval wt v) 0)
      by (subst v; autorewrite with push_basesystem_eval; reflexivity);
      clear Hv.
    revert dependent v.
    induction coef_div_modulus as [|n IHn]; clear coef_div_modulus;
      intros; [ assumption | ].
    rewrite IHn; [ reflexivity | ].
    pose proof wt_gen0_1.
    pose proof wt_gen_nonzero.
    pose proof div_mod.
    pose proof wt_gen_divides'.
    destruct (Nat.eq_dec sz 0).
    { subst; reflexivity.
}
    { repeat autounfold; autorewrite with uncps push_id push_basesystem_eval.
      rewrite Positional.eval_encode by (intros; autorewrite with uncps; unfold id; auto).
      cbv [mod_eq] in *.
      push_Zmod; rewrite Hv'; pull_Zmod.
      reflexivity.
}
  Qed.
End gen.

Ltac pose_wt base wt :=
  let v := (eval cbv [wt_gen] in (wt_gen base)) in
  cache_term v wt.

Ltac pose_sz2 sz sz2 :=
  let v := (eval vm_compute in (sz2' sz)) in
  cache_term v sz2.

Ltac pose_half_sz sz half_sz :=
  let v := (eval compute in (half_sz' sz)) in
  cache_term v half_sz.

Ltac pose_s_nonzero s s_nonzero :=
  cache_proof_with_type_by
    (s <> 0)
    ltac:(vm_decide_no_check)
           s_nonzero.

Ltac pose_sz_le_log2_m sz m sz_le_log2_m :=
  cache_proof_with_type_by
    (Z.of_nat sz <= Z.log2_up (Z.pos m))
    ltac:(vm_decide_no_check)
           sz_le_log2_m.

Ltac pose_base_pos base base_pos :=
  cache_proof_with_type_by
    ((1 <= base)%Q)
    ltac:(vm_decide_no_check)
           base_pos.

Ltac pose_m_correct m s c m_correct :=
  cache_proof_with_type_by
    (Z.pos m = s - Associational.eval c)
    ltac:(vm_decide_no_check)
           m_correct.

Ltac pose_m_enc base m sz m_enc :=
  let v := (eval vm_compute in (m_enc' base m sz)) in
  let v := (eval compute in v) in
  cache_term v m_enc.

Ltac pose_coef base m sz coef_div_modulus coef :=
  let v := (eval vm_compute in (coef' base m sz coef_div_modulus)) in
  cache_term v coef.

Ltac pose_coef_mod wt coef base m sz coef_div_modulus base_pos coef_mod :=
  cache_proof_with_type_by
    (mod_eq m (Positional.eval (n:=sz) wt coef) 0)
    ltac:(vm_cast_no_check (coef_mod' base m sz coef_div_modulus base_pos))
           coef_mod.
Ltac pose_sz_nonzero sz sz_nonzero :=
  cache_proof_with_type_by
    (sz <> 0%nat)
    ltac:(vm_decide_no_check)
           sz_nonzero.

Ltac pose_wt_nonzero wt wt_nonzero :=
  cache_proof_with_type_by
    (forall i, wt i <> 0)
    ltac:(apply wt_gen_nonzero; vm_decide_no_check)
           wt_nonzero.
Ltac pose_wt_nonneg wt wt_nonneg :=
  cache_proof_with_type_by
    (forall i, 0 <= wt i)
    ltac:(apply wt_gen_nonneg; vm_decide_no_check)
           wt_nonneg.
Ltac pose_wt_divides wt wt_divides :=
  cache_proof_with_type_by
    (forall i, wt (S i) / wt i > 0)
    ltac:(apply wt_gen_divides; vm_decide_no_check)
           wt_divides.
Ltac pose_wt_divides' wt wt_divides wt_divides' :=
  cache_proof_with_type_by
    (forall i, wt (S i) / wt i <> 0)
    ltac:(apply wt_gen_divides'; vm_decide_no_check)
           wt_divides'.

Ltac pose_wt_divides_chains wt carry_chains wt_divides_chains :=
  let T := (eval cbv [carry_chains List.fold_right List.map] in
               (List.fold_right
                  and
                  True
                  (List.map
                     (fun carry_chain
                      => forall i (H:In i carry_chain), wt (S i) / wt i <> 0)
                     carry_chains))) in
  cache_proof_with_type_by
    T
    ltac:(refine (@wt_gen_divides_chains _ _ carry_chains); vm_decide_no_check)
           wt_divides_chains.

Ltac pose_wt_pos wt wt_pos :=
  cache_proof_with_type_by
    (forall i, wt i > 0)
    ltac:(apply wt_gen_pos; vm_decide_no_check)
           wt_pos.

Ltac pose_wt_multiples wt wt_multiples :=
  cache_proof_with_type_by
    (forall i, wt (S i) mod (wt i) = 0)
    ltac:(apply wt_gen_multiples; vm_decide_no_check)
           wt_multiples.

Ltac pose_c_small c wt sz c_small :=
  cache_proof_with_type_by
    (0 < Associational.eval c < wt sz)
    ltac:(vm_decide_no_check)
           c_small.

Ltac pose_base_le_bitwidth base bitwidth base_le_bitwidth :=
  cache_proof_with_type_by
    (base <= inject_Z bitwidth)%Q
    ltac:(cbv -[Z.le]; vm_decide_no_check)
           base_le_bitwidth.

Ltac pose_m_enc_bounded sz bitwidth m_enc m_enc_bounded :=
  cache_proof_with_type_by
    (Tuple.map (n:=sz) (BinInt.Z.land (Z.ones bitwidth)) m_enc = m_enc)
    ltac:(vm_compute; reflexivity)
           m_enc_bounded.

Module Export Exports.
  Export Crypto.Util.Decidable.
End Exports.

End Base.

End Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_Base_WRAPPED.
Module Export Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_Base.
Module Export Crypto.
Module Export Specific.
Module Export Framework.
Module Export ArithmeticSynthesis.
Module Base.
Include Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_Base_WRAPPED.Base.
End Base.

End ArithmeticSynthesis.

End Framework.

End Specific.

End Crypto.

End Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_Base.
Module Crypto_DOT_Specific_DOT_Framework_DOT_Packages_WRAPPED.
Module Packages.
Import Crypto.Util.TagList.

Module Type PrePackage.
  Parameter package : Tag.Context.
End PrePackage.

Module MakePackageBase (PKG : PrePackage).
  Ltac get_package _ := eval hnf in PKG.package.
  Ltac get key :=
    let pkg := get_package () in
    Tag.get pkg key.
End MakePackageBase.

End Packages.

End Crypto_DOT_Specific_DOT_Framework_DOT_Packages_WRAPPED.
Module Export Crypto_DOT_Specific_DOT_Framework_DOT_Packages.
Module Export Crypto.
Module Export Specific.
Module Export Framework.
Module Packages.
Include Crypto_DOT_Specific_DOT_Framework_DOT_Packages_WRAPPED.Packages.
End Packages.

End Framework.

End Specific.

End Crypto.

End Crypto_DOT_Specific_DOT_Framework_DOT_Packages.
Module Crypto_DOT_Specific_DOT_Framework_DOT_CurveParametersPackage_WRAPPED.
Module CurveParametersPackage.

Export Crypto.Specific.Framework.CurveParameters.
Import Crypto.Specific.Framework.Packages.
Import Crypto.Util.TagList.

Ltac if_goldilocks pkg tac_true tac_false arg :=
  let goldilocks := Tag.get pkg TAG.goldilocks in
  let goldilocks := (eval vm_compute in (goldilocks : bool)) in
  lazymatch goldilocks with
  | true => tac_true arg
  | false => tac_false arg
  end.

Ltac if_karatsuba pkg tac_true tac_false arg :=
  let karatsuba := Tag.get pkg TAG.karatsuba in
  let karatsuba := (eval vm_compute in (karatsuba : bool)) in
  lazymatch karatsuba with
  | true => tac_true arg
  | false => tac_false arg
  end.

Ltac if_montgomery pkg tac_true tac_false arg :=
  let montgomery := Tag.get pkg TAG.montgomery in
  let montgomery := (eval vm_compute in (montgomery : bool)) in
  lazymatch montgomery with
  | true => tac_true arg
  | false => tac_false arg
  end.

Ltac if_freeze pkg tac_true tac_false arg :=
  let freeze := Tag.get pkg TAG.freeze in
  let freeze := (eval vm_compute in (freeze : bool)) in
  lazymatch freeze with
  | true => tac_true arg
  | false => tac_false arg
  end.

Ltac if_ladderstep pkg tac_true tac_false arg :=
  let ladderstep := Tag.get pkg TAG.ladderstep in
  let ladderstep := (eval vm_compute in (ladderstep : bool)) in
  lazymatch ladderstep with
  | true => tac_true arg
  | false => tac_false arg
  end.

Module MakeCurveParametersPackage (PKG : PrePackage).
  Module Import MakeCurveParametersPackageInternal := MakePackageBase PKG.

  Ltac get_base _ := get TAG.base.
  Notation base := (ltac:(let v := get_base () in exact v)) (only parsing).
  Ltac get_sz _ := get TAG.sz.
  Notation sz := (ltac:(let v := get_sz () in exact v)) (only parsing).
  Ltac get_bitwidth _ := get TAG.bitwidth.
  Notation bitwidth := (ltac:(let v := get_bitwidth () in exact v)) (only parsing).
  Ltac get_s _ := get TAG.s.
  Notation s := (ltac:(let v := get_s () in exact v)) (only parsing).
  Ltac get_c _ := get TAG.c.
  Notation c := (ltac:(let v := get_c () in exact v)) (only parsing).
  Ltac get_carry_chains _ := get TAG.carry_chains.
  Notation carry_chains := (ltac:(let v := get_carry_chains () in exact v)) (only parsing).
  Ltac get_a24 _ := get TAG.a24.
  Notation a24 := (ltac:(let v := get_a24 () in exact v)) (only parsing).
  Ltac get_coef_div_modulus _ := get TAG.coef_div_modulus.
  Notation coef_div_modulus := (ltac:(let v := get_coef_div_modulus () in exact v)) (only parsing).
  Ltac get_goldilocks _ := get TAG.goldilocks.
  Notation goldilocks := (ltac:(let v := get_goldilocks () in exact v)) (only parsing).
  Ltac get_karatsuba _ := get TAG.karatsuba.
  Notation karatsuba := (ltac:(let v := get_karatsuba () in exact v)) (only parsing).
  Ltac get_montgomery _ := get TAG.montgomery.
  Notation montgomery := (ltac:(let v := get_montgomery () in exact v)) (only parsing).
  Ltac get_freeze _ := get TAG.freeze.
  Notation freeze := (ltac:(let v := get_freeze () in exact v)) (only parsing).
  Ltac get_ladderstep _ := get TAG.ladderstep.
  Notation ladderstep := (ltac:(let v := get_ladderstep () in exact v)) (only parsing).
  Ltac get_allowable_bit_widths _ := get TAG.allowable_bit_widths.
  Notation allowable_bit_widths := (ltac:(let v := get_allowable_bit_widths () in exact v)) (only parsing).
  Ltac get_freeze_allowable_bit_widths _ := get TAG.freeze_allowable_bit_widths.
  Notation freeze_allowable_bit_widths := (ltac:(let v := get_freeze_allowable_bit_widths () in exact v)) (only parsing).
  Ltac get_upper_bound_of_exponent_tight _ := get TAG.upper_bound_of_exponent_tight.
  Notation upper_bound_of_exponent_tight := (ltac:(let v := get_upper_bound_of_exponent_tight () in exact v)) (only parsing).
  Ltac get_upper_bound_of_exponent_loose _ := get TAG.upper_bound_of_exponent_loose.
  Notation upper_bound_of_exponent_loose := (ltac:(let v := get_upper_bound_of_exponent_loose () in exact v)) (only parsing).
  Ltac get_modinv_fuel _ := get TAG.modinv_fuel.
  Notation modinv_fuel := (ltac:(let v := get_modinv_fuel () in exact v)) (only parsing).
  Ltac get_mul_code _ := get TAG.mul_code.
  Notation mul_code := (ltac:(let v := get_mul_code () in exact v)) (only parsing).
  Ltac get_square_code _ := get TAG.square_code.
  Notation square_code := (ltac:(let v := get_square_code () in exact v)) (only parsing).
End MakeCurveParametersPackage.

End CurveParametersPackage.

End Crypto_DOT_Specific_DOT_Framework_DOT_CurveParametersPackage_WRAPPED.
Module Export Crypto_DOT_Specific_DOT_Framework_DOT_CurveParametersPackage.
Module Export Crypto.
Module Export Specific.
Module Export Framework.
Module CurveParametersPackage.
Include Crypto_DOT_Specific_DOT_Framework_DOT_CurveParametersPackage_WRAPPED.CurveParametersPackage.
End CurveParametersPackage.

End Framework.

End Specific.

End Crypto.

End Crypto_DOT_Specific_DOT_Framework_DOT_CurveParametersPackage.
Module Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_BasePackage_WRAPPED.
Module BasePackage.

Import Crypto.Specific.Framework.CurveParametersPackage.
Export Crypto.Specific.Framework.ArithmeticSynthesis.Base.
Import Crypto.Specific.Framework.Packages.
Import Crypto.Util.TagList.

Module TAG.
  Inductive tags := r | m | wt | sz2 | half_sz | s_nonzero | sz_le_log2_m | base_pos | m_correct | m_enc | coef | coef_mod | sz_nonzero | wt_nonzero | wt_nonneg | wt_divides | wt_divides' | wt_divides_chains | wt_pos | wt_multiples | c_small | base_le_bitwidth | m_enc_bounded.
End TAG.

Ltac add_r pkg :=
  let bitwidth := Tag.get pkg TAG.bitwidth in
  let r := fresh "r" in
  let r := pose_r bitwidth r in
  Tag.update pkg TAG.r r.

Ltac add_m pkg :=
  let s := Tag.get pkg TAG.s in
  let c := Tag.get pkg TAG.c in
  let m := fresh "m" in
  let m := pose_m s c m in
  Tag.update pkg TAG.m m.

Ltac add_wt pkg :=
  let base := Tag.get pkg TAG.base in
  let wt := fresh "wt" in
  let wt := pose_wt base wt in
  Tag.update pkg TAG.wt wt.

Ltac add_sz2 pkg :=
  let sz := Tag.get pkg TAG.sz in
  let sz2 := fresh "sz2" in
  let sz2 := pose_sz2 sz sz2 in
  Tag.update pkg TAG.sz2 sz2.

Ltac add_half_sz pkg :=
  let sz := Tag.get pkg TAG.sz in
  let half_sz := fresh "half_sz" in
  let half_sz := pose_half_sz sz half_sz in
  Tag.update pkg TAG.half_sz half_sz.

Ltac add_s_nonzero pkg :=
  let s := Tag.get pkg TAG.s in
  let s_nonzero := fresh "s_nonzero" in
  let s_nonzero := pose_s_nonzero s s_nonzero in
  Tag.update pkg TAG.s_nonzero s_nonzero.

Ltac add_sz_le_log2_m pkg :=
  let sz := Tag.get pkg TAG.sz in
  let m := Tag.get pkg TAG.m in
  let sz_le_log2_m := fresh "sz_le_log2_m" in
  let sz_le_log2_m := pose_sz_le_log2_m sz m sz_le_log2_m in
  Tag.update pkg TAG.sz_le_log2_m sz_le_log2_m.

Ltac add_base_pos pkg :=
  let base := Tag.get pkg TAG.base in
  let base_pos := fresh "base_pos" in
  let base_pos := pose_base_pos base base_pos in
  Tag.update pkg TAG.base_pos base_pos.

Ltac add_m_correct pkg :=
  let m := Tag.get pkg TAG.m in
  let s := Tag.get pkg TAG.s in
  let c := Tag.get pkg TAG.c in
  let m_correct := fresh "m_correct" in
  let m_correct := pose_m_correct m s c m_correct in
  Tag.update pkg TAG.m_correct m_correct.

Ltac add_m_enc pkg :=
  let base := Tag.get pkg TAG.base in
  let m := Tag.get pkg TAG.m in
  let sz := Tag.get pkg TAG.sz in
  let m_enc := fresh "m_enc" in
  let m_enc := pose_m_enc base m sz m_enc in
  Tag.update pkg TAG.m_enc m_enc.

Ltac add_coef pkg :=
  let base := Tag.get pkg TAG.base in
  let m := Tag.get pkg TAG.m in
  let sz := Tag.get pkg TAG.sz in
  let coef_div_modulus := Tag.get pkg TAG.coef_div_modulus in
  let coef := fresh "coef" in
  let coef := pose_coef base m sz coef_div_modulus coef in
  Tag.update pkg TAG.coef coef.

Ltac add_coef_mod pkg :=
  let wt := Tag.get pkg TAG.wt in
  let coef := Tag.get pkg TAG.coef in
  let base := Tag.get pkg TAG.base in
  let m := Tag.get pkg TAG.m in
  let sz := Tag.get pkg TAG.sz in
  let coef_div_modulus := Tag.get pkg TAG.coef_div_modulus in
  let base_pos := Tag.get pkg TAG.base_pos in
  let coef_mod := fresh "coef_mod" in
  let coef_mod := pose_coef_mod wt coef base m sz coef_div_modulus base_pos coef_mod in
  Tag.update pkg TAG.coef_mod coef_mod.

Ltac add_sz_nonzero pkg :=
  let sz := Tag.get pkg TAG.sz in
  let sz_nonzero := fresh "sz_nonzero" in
  let sz_nonzero := pose_sz_nonzero sz sz_nonzero in
  Tag.update pkg TAG.sz_nonzero sz_nonzero.

Ltac add_wt_nonzero pkg :=
  let wt := Tag.get pkg TAG.wt in
  let wt_nonzero := fresh "wt_nonzero" in
  let wt_nonzero := pose_wt_nonzero wt wt_nonzero in
  Tag.update pkg TAG.wt_nonzero wt_nonzero.

Ltac add_wt_nonneg pkg :=
  let wt := Tag.get pkg TAG.wt in
  let wt_nonneg := fresh "wt_nonneg" in
  let wt_nonneg := pose_wt_nonneg wt wt_nonneg in
  Tag.update pkg TAG.wt_nonneg wt_nonneg.

Ltac add_wt_divides pkg :=
  let wt := Tag.get pkg TAG.wt in
  let wt_divides := fresh "wt_divides" in
  let wt_divides := pose_wt_divides wt wt_divides in
  Tag.update pkg TAG.wt_divides wt_divides.

Ltac add_wt_divides' pkg :=
  let wt := Tag.get pkg TAG.wt in
  let wt_divides := Tag.get pkg TAG.wt_divides in
  let wt_divides' := fresh "wt_divides'" in
  let wt_divides' := pose_wt_divides' wt wt_divides wt_divides' in
  Tag.update pkg TAG.wt_divides' wt_divides'.

Ltac add_wt_divides_chains pkg :=
  let wt := Tag.get pkg TAG.wt in
  let carry_chains := Tag.get pkg TAG.carry_chains in
  let wt_divides_chains := fresh "wt_divides_chains" in
  let wt_divides_chains := pose_wt_divides_chains wt carry_chains wt_divides_chains in
  Tag.update pkg TAG.wt_divides_chains wt_divides_chains.

Ltac add_wt_pos pkg :=
  let wt := Tag.get pkg TAG.wt in
  let wt_pos := fresh "wt_pos" in
  let wt_pos := pose_wt_pos wt wt_pos in
  Tag.update pkg TAG.wt_pos wt_pos.

Ltac add_wt_multiples pkg :=
  let wt := Tag.get pkg TAG.wt in
  let wt_multiples := fresh "wt_multiples" in
  let wt_multiples := pose_wt_multiples wt wt_multiples in
  Tag.update pkg TAG.wt_multiples wt_multiples.

Ltac add_c_small pkg :=
  let c := Tag.get pkg TAG.c in
  let wt := Tag.get pkg TAG.wt in
  let sz := Tag.get pkg TAG.sz in
  let c_small := fresh "c_small" in
  let c_small := pose_c_small c wt sz c_small in
  Tag.update pkg TAG.c_small c_small.

Ltac add_base_le_bitwidth pkg :=
  let base := Tag.get pkg TAG.base in
  let bitwidth := Tag.get pkg TAG.bitwidth in
  let base_le_bitwidth := fresh "base_le_bitwidth" in
  let base_le_bitwidth := pose_base_le_bitwidth base bitwidth base_le_bitwidth in
  Tag.update pkg TAG.base_le_bitwidth base_le_bitwidth.

Ltac add_m_enc_bounded pkg :=
  let sz := Tag.get pkg TAG.sz in
  let bitwidth := Tag.get pkg TAG.bitwidth in
  let m_enc := Tag.get pkg TAG.m_enc in
  let m_enc_bounded := fresh "m_enc_bounded" in
  let m_enc_bounded := pose_m_enc_bounded sz bitwidth m_enc m_enc_bounded in
  Tag.update pkg TAG.m_enc_bounded m_enc_bounded.

Ltac add_Base_package pkg :=
  let pkg := add_r pkg in
  let pkg := add_m pkg in
  let pkg := add_wt pkg in
  let pkg := add_sz2 pkg in
  let pkg := add_half_sz pkg in
  let pkg := add_s_nonzero pkg in
  let pkg := add_sz_le_log2_m pkg in
  let pkg := add_base_pos pkg in
  let pkg := add_m_correct pkg in
  let pkg := add_m_enc pkg in
  let pkg := add_coef pkg in
  let pkg := add_coef_mod pkg in
  let pkg := add_sz_nonzero pkg in
  let pkg := add_wt_nonzero pkg in
  let pkg := add_wt_nonneg pkg in
  let pkg := add_wt_divides pkg in
  let pkg := add_wt_divides' pkg in
  let pkg := add_wt_divides_chains pkg in
  let pkg := add_wt_pos pkg in
  let pkg := add_wt_multiples pkg in
  let pkg := add_c_small pkg in
  let pkg := add_base_le_bitwidth pkg in
  let pkg := add_m_enc_bounded pkg in
  Tag.strip_subst_local pkg.

Module MakeBasePackage (PKG : PrePackage).
  Module Import MakeBasePackageInternal := MakePackageBase PKG.

  Ltac get_r _ := get TAG.r.
  Notation r := (ltac:(let v := get_r () in exact v)) (only parsing).
  Ltac get_m _ := get TAG.m.
  Notation m := (ltac:(let v := get_m () in exact v)) (only parsing).
  Ltac get_wt _ := get TAG.wt.
  Notation wt := (ltac:(let v := get_wt () in exact v)) (only parsing).
  Ltac get_sz2 _ := get TAG.sz2.
  Notation sz2 := (ltac:(let v := get_sz2 () in exact v)) (only parsing).
  Ltac get_half_sz _ := get TAG.half_sz.
  Notation half_sz := (ltac:(let v := get_half_sz () in exact v)) (only parsing).
  Ltac get_s_nonzero _ := get TAG.s_nonzero.
  Notation s_nonzero := (ltac:(let v := get_s_nonzero () in exact v)) (only parsing).
  Ltac get_sz_le_log2_m _ := get TAG.sz_le_log2_m.
  Notation sz_le_log2_m := (ltac:(let v := get_sz_le_log2_m () in exact v)) (only parsing).
  Ltac get_base_pos _ := get TAG.base_pos.
  Notation base_pos := (ltac:(let v := get_base_pos () in exact v)) (only parsing).
  Ltac get_m_correct _ := get TAG.m_correct.
  Notation m_correct := (ltac:(let v := get_m_correct () in exact v)) (only parsing).
  Ltac get_m_enc _ := get TAG.m_enc.
  Notation m_enc := (ltac:(let v := get_m_enc () in exact v)) (only parsing).
  Ltac get_coef _ := get TAG.coef.
  Notation coef := (ltac:(let v := get_coef () in exact v)) (only parsing).
  Ltac get_coef_mod _ := get TAG.coef_mod.
  Notation coef_mod := (ltac:(let v := get_coef_mod () in exact v)) (only parsing).
  Ltac get_sz_nonzero _ := get TAG.sz_nonzero.
  Notation sz_nonzero := (ltac:(let v := get_sz_nonzero () in exact v)) (only parsing).
  Ltac get_wt_nonzero _ := get TAG.wt_nonzero.
  Notation wt_nonzero := (ltac:(let v := get_wt_nonzero () in exact v)) (only parsing).
  Ltac get_wt_nonneg _ := get TAG.wt_nonneg.
  Notation wt_nonneg := (ltac:(let v := get_wt_nonneg () in exact v)) (only parsing).
  Ltac get_wt_divides _ := get TAG.wt_divides.
  Notation wt_divides := (ltac:(let v := get_wt_divides () in exact v)) (only parsing).
  Ltac get_wt_divides' _ := get TAG.wt_divides'.
  Notation wt_divides' := (ltac:(let v := get_wt_divides' () in exact v)) (only parsing).
  Ltac get_wt_divides_chains _ := get TAG.wt_divides_chains.
  Notation wt_divides_chains := (ltac:(let v := get_wt_divides_chains () in exact v)) (only parsing).
  Ltac get_wt_pos _ := get TAG.wt_pos.
  Notation wt_pos := (ltac:(let v := get_wt_pos () in exact v)) (only parsing).
  Ltac get_wt_multiples _ := get TAG.wt_multiples.
  Notation wt_multiples := (ltac:(let v := get_wt_multiples () in exact v)) (only parsing).
  Ltac get_c_small _ := get TAG.c_small.
  Notation c_small := (ltac:(let v := get_c_small () in exact v)) (only parsing).
  Ltac get_base_le_bitwidth _ := get TAG.base_le_bitwidth.
  Notation base_le_bitwidth := (ltac:(let v := get_base_le_bitwidth () in exact v)) (only parsing).
  Ltac get_m_enc_bounded _ := get TAG.m_enc_bounded.
  Notation m_enc_bounded := (ltac:(let v := get_m_enc_bounded () in exact v)) (only parsing).
End MakeBasePackage.

End BasePackage.

End Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_BasePackage_WRAPPED.
Module Export Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_BasePackage.
Module Export Crypto.
Module Export Specific.
Module Export Framework.
Module Export ArithmeticSynthesis.
Module BasePackage.
Include Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_BasePackage_WRAPPED.BasePackage.
End BasePackage.

End ArithmeticSynthesis.

End Framework.

End Specific.

End Crypto.

End Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_BasePackage.
Module Crypto_DOT_Util_DOT_Tactics_DOT_PoseTermWithName_WRAPPED.
Module PoseTermWithName.
Export Crypto.Util.FixCoqMistakes.
Ltac pose_term_with tac name :=
  let name := fresh name in
  let v := tac () in
  let dummy := match goal with
               | _ => pose v as name
               end in
  name.

Ltac pose_term_with_type type tac name :=
  pose_term_with ltac:(fun u => let v := tac u in constr:(v : type)) name.

End PoseTermWithName.

End Crypto_DOT_Util_DOT_Tactics_DOT_PoseTermWithName_WRAPPED.
Module Export Crypto_DOT_Util_DOT_Tactics_DOT_PoseTermWithName.
Module Export Crypto.
Module Export Util.
Module Export Tactics.
Module PoseTermWithName.
Include Crypto_DOT_Util_DOT_Tactics_DOT_PoseTermWithName_WRAPPED.PoseTermWithName.
End PoseTermWithName.

End Tactics.

End Util.

End Crypto.

End Crypto_DOT_Util_DOT_Tactics_DOT_PoseTermWithName.
Module Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_Defaults_WRAPPED.
Module Defaults.
Import Coq.micromega.Lia Coq.Classes.Morphisms Coq.Classes.Morphisms_Prop.
Import Coq.ZArith.ZArith Coq.ZArith.BinIntDef.
Import Coq.QArith.QArith_base.
Import Coq.Lists.List.
Import ListNotations.
Import Crypto.Arithmetic.CoreUnfolder.
Import Crypto.Arithmetic.Core.
Import B.
Import Crypto.Arithmetic.PrimeFieldTheorems.
Import Crypto.Specific.Framework.ArithmeticSynthesis.HelperTactics.
Import Crypto.Specific.Framework.ArithmeticSynthesis.Base.
Import Crypto.Util.Decidable.
Import Crypto.Util.LetIn.
Import Crypto.Util.Tactics.BreakMatch.
Import Crypto.Util.Tactics.DestructHead.
Import Crypto.Util.Tactics.PoseTermWithName.
Import Crypto.Util.Tactics.CacheTerm.

Local Notation tuple := Tuple.tuple.
Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Infix "^" := tuple : type_scope.

Module Export Exports.
  Export Coq.setoid_ring.ZArithRing.
End Exports.

Local Ltac solve_constant_local_sig :=
  idtac;
  lazymatch goal with
  | [ |- { c : Z^?sz | Positional.Fdecode (m:=?M) ?wt c = ?v } ]
    => (exists (Positional.encode (n:=sz) (modulo_cps:=@modulo_cps) (div_cps:=@div_cps) wt (F.to_Z (m:=M) v)));
       lazymatch goal with
       | [ sz_nonzero : sz <> 0%nat, base_pos : (1 <= _)%Q |- _ ]
         => clear -base_pos sz_nonzero
       end
  end;
  abstract (
      setoid_rewrite Positional.Fdecode_Fencode_id;
      [ reflexivity
      | auto using wt_gen0_1, wt_gen_nonzero, wt_gen_divides', div_mod;
        intros; autorewrite with uncps push_id; auto using div_mod.. ]
    ).

Section gen.
  Context (m : positive)
          (base : Q)
          (sz : nat)
          (s : Z)
          (c : list limb)
          (carry_chains : list (list nat))
          (coef : Z^sz)
          (mul_code : option (Z^sz -> Z^sz -> Z^sz))
          (square_code : option (Z^sz -> Z^sz))
          (sz_nonzero : sz <> 0%nat)
          (s_nonzero : s <> 0)
          (base_pos : (1 <= base)%Q)
          (sz_le_log2_m : Z.of_nat sz <= Z.log2_up (Z.pos m)).

  Local Notation wt := (wt_gen base).
  Local Notation sz2 := (sz2' sz).
  Local Notation wt_divides' := (wt_gen_divides' base base_pos).
  Local Notation wt_nonzero := (wt_gen_nonzero base base_pos).

  Context (mul_code_correct
           : match mul_code with
             | None => True
             | Some v
               => forall a b,
                 v a b
                 = Positional.mul_cps (n:=sz) (m:=sz2) wt a b
                                      (fun ab => Positional.reduce_cps (n:=sz) (m:=sz2) wt s c ab id)
             end)
          (square_code_correct
           : match square_code with
             | None => True
             | Some v
               => forall a,
                 v a
                 = Positional.mul_cps (n:=sz) (m:=sz2) wt a a
                                      (fun ab => Positional.reduce_cps (n:=sz) (m:=sz2) wt s c ab id)
             end).

  Context (coef_mod : mod_eq m (Positional.eval wt coef) 0)
          (m_correct : Z.pos m = s - Associational.eval c).

  Definition carry_sig'
    : { carry : (Z^sz -> Z^sz)%type
      | forall a : Z^sz,
          let eval := Positional.Fdecode (m := m) wt in
          eval (carry a) = eval a }.
  Proof.
    let a := fresh "a" in
    eexists; cbv beta zeta; intros a.
    pose proof (wt_gen0_1 base).
    pose proof wt_nonzero; pose proof div_mod.
    pose proof (wt_gen_divides_chains base base_pos carry_chains).
    pose proof wt_divides'.
    let x := constr:(Positional.chained_carries_reduce (n:=sz) (modulo_cps:=@modulo_cps) (div_cps:=@div_cps) wt s c a carry_chains) in
    presolve_op_F constr:(wt) x;
      [ autorewrite with pattern_runtime; reflexivity | ].
    reflexivity.
  Defined.

  Definition constant_sig' v
    : { c : Z^sz | Positional.Fdecode (m:=m) wt c = v}.
  Proof.
solve_constant_local_sig.
Defined.

  Definition zero_sig'
    : { zero : Z^sz | Positional.Fdecode (m:=m) wt zero = 0%F}
    := Eval hnf in constant_sig' _.

  Definition one_sig'
    : { one : Z^sz | Positional.Fdecode (m:=m) wt one = 1%F}
    := Eval hnf in constant_sig' _.

  Definition add_sig'
    : { add : (Z^sz -> Z^sz -> Z^sz)%type
      | forall a b : Z^sz,
          let eval := Positional.Fdecode (m:=m) wt in
          eval (add a b) = (eval a + eval b)%F }.
  Proof.
    eexists; cbv beta zeta; intros a b.
    pose proof wt_nonzero.
    pose proof (wt_gen0_1 base).
    let x := constr:(
               Positional.add_cps (n := sz) wt a b id) in
    presolve_op_F constr:(wt) x;
      [ autorewrite with pattern_runtime; reflexivity | ].
    reflexivity.
  Defined.

  Definition sub_sig'
    : { sub : (Z^sz -> Z^sz -> Z^sz)%type
      | forall a b : Z^sz,
          let eval := Positional.Fdecode (m:=m) wt in
          eval (sub a b) = (eval a - eval b)%F }.
  Proof.
    let a := fresh "a" in
    let b := fresh "b" in
    eexists; cbv beta zeta; intros a b.
    pose proof wt_nonzero.
    pose proof (wt_gen0_1 base).
    let x := constr:(
               Positional.sub_cps (n:=sz) (coef := coef) wt a b id) in
    presolve_op_F constr:(wt) x;
      [ autorewrite with pattern_runtime; reflexivity | ].
    reflexivity.
  Defined.

  Definition opp_sig'
    : { opp : (Z^sz -> Z^sz)%type
      | forall a : Z^sz,
          let eval := Positional.Fdecode (m := m) wt in
          eval (opp a) = F.opp (eval a) }.
  Proof.
    eexists; cbv beta zeta; intros a.
    pose proof wt_nonzero.
    pose proof (wt_gen0_1 base).
    let x := constr:(
               Positional.opp_cps (n:=sz) (coef := coef) wt a id) in
    presolve_op_F constr:(wt) x;
      [ autorewrite with pattern_runtime; reflexivity | ].
    reflexivity.
  Defined.

  Definition mul_sig'
    : { mul : (Z^sz -> Z^sz -> Z^sz)%type
      | forall a b : Z^sz,
          let eval := Positional.Fdecode (m := m) wt in
          eval (mul a b) = (eval a * eval b)%F }.
  Proof.
    eexists; cbv beta zeta; intros a b.
    pose proof wt_nonzero.
    pose proof (wt_gen0_1 base).
    pose proof (sz2'_nonzero sz sz_nonzero).
    let x := constr:(
               Positional.mul_cps (n:=sz) (m:=sz2) wt a b
                                  (fun ab => Positional.reduce_cps (n:=sz) (m:=sz2) wt s c ab id)) in
    presolve_op_F constr:(wt) x; [ | reflexivity ].
    let rhs := match goal with |- _ = ?rhs => rhs end in
    transitivity (match mul_code with
                  | None => rhs
                  | Some v => v a b
                  end);
      [ reflexivity | ].
    destruct mul_code; try reflexivity.
    transitivity (Positional.mul_cps (n:=sz) (m:=sz2) wt a b
                                     (fun ab => Positional.reduce_cps (n:=sz) (m:=sz2) wt s c ab id)); [ | reflexivity ].
    auto.
  Defined.

  Definition square_sig'
    : { square : (Z^sz -> Z^sz)%type
      | forall a : Z^sz,
          let eval := Positional.Fdecode (m := m) wt in
          eval (square a) = (eval a * eval a)%F }.
  Proof.
    eexists; cbv beta zeta; intros a.
    pose proof wt_nonzero.
    pose proof (wt_gen0_1 base).
    pose proof (sz2'_nonzero sz sz_nonzero).
    let x := constr:(
               Positional.mul_cps (n:=sz) (m:=sz2) wt a a
                                  (fun ab => Positional.reduce_cps (n:=sz) (m:=sz2) wt s c ab id)) in
    presolve_op_F constr:(wt) x; [ | reflexivity ].
    let rhs := match goal with |- _ = ?rhs => rhs end in
    transitivity (match square_code with
                  | None => rhs
                  | Some v => v a
                  end);
      [ reflexivity | ].
    destruct square_code; try reflexivity.
    transitivity (Positional.mul_cps (n:=sz) (m:=sz2) wt a a
                                     (fun ab => Positional.reduce_cps (n:=sz) (m:=sz2) wt s c ab id)); [ | reflexivity ].
    auto.
  Defined.

  Let ring_pkg : { T : _ & T }.
  Proof.
    eexists.
    refine (fun zero_sig one_sig add_sig sub_sig mul_sig opp_sig
            => Ring.ring_by_isomorphism
                 (F := F m)
                 (H := Z^sz)
                 (phi := Positional.Fencode wt)
                 (phi' := Positional.Fdecode wt)
                 (zero := proj1_sig zero_sig)
                 (one := proj1_sig one_sig)
                 (opp := proj1_sig opp_sig)
                 (add := proj1_sig add_sig)
                 (sub := proj1_sig sub_sig)
                 (mul := proj1_sig mul_sig)
                 (phi'_zero := _)
                 (phi'_one := _)
                 (phi'_opp := _)
                 (Positional.Fdecode_Fencode_id
                    (sz_nonzero := sz_nonzero)
                    (div_mod := div_mod)
                    wt (wt_gen0_1 base) wt_nonzero wt_divides')
                 (Positional.eq_Feq_iff wt)
                 _ _ _);
      lazymatch goal with
      | [ |- context[@proj1_sig ?A ?P ?x] ]
        => pattern (@proj1_sig A P x);
             exact (@proj2_sig A P x)
      | _ => eauto using @Core.modulo_id, @Core.div_id with nocore
      end.
  Defined.

  Definition ring' zero_sig one_sig add_sig sub_sig mul_sig opp_sig
    := Eval cbv [ring_pkg projT2] in
        projT2 ring_pkg zero_sig one_sig add_sig sub_sig mul_sig opp_sig.
End gen.

Ltac internal_solve_code_correct P_tac :=
  hnf;
  lazymatch goal with
  | [ |- True ] => constructor
  | _
    => cbv [Positional.mul_cps Positional.reduce_cps];
       intros;
       autorewrite with pattern_runtime;
       repeat autounfold;
       autorewrite with pattern_runtime;
       basesystem_partial_evaluation_RHS;
       P_tac ();
       break_match; cbv [Let_In runtime_mul runtime_add]; repeat apply (f_equal2 pair); rewrite ?Z.shiftl_mul_pow2 by lia; ring
  end.

Ltac pose_mul_code_correct P_extra_prove_mul_eq sz sz2 wt s c mul_code mul_code_correct :=
  cache_proof_with_type_by
    (match mul_code with
     | None => True
     | Some v
       => forall a b,
         v a b
         = Positional.mul_cps (n:=sz) (m:=sz2) wt a b
                              (fun ab => Positional.reduce_cps (n:=sz) (m:=sz2) wt s c ab id)
     end)
    ltac:(internal_solve_code_correct P_extra_prove_mul_eq)
           mul_code_correct.

Ltac pose_square_code_correct P_extra_prove_square_eq sz sz2 wt s c square_code square_code_correct :=
  cache_proof_with_type_by
    (match square_code with
     | None => True
     | Some v
       => forall a,
         v a
         = Positional.mul_cps (n:=sz) (m:=sz2) wt a a
                              (fun ab => Positional.reduce_cps (n:=sz) (m:=sz2) wt s c ab id)
     end)
    ltac:(internal_solve_code_correct P_extra_prove_square_eq)
           square_code_correct.

Ltac cache_sig_with_type_by_existing_sig ty existing_sig id :=
  cache_sig_with_type_by_existing_sig_helper
    ltac:(fun _ => cbv [carry_sig' constant_sig' zero_sig' one_sig' add_sig' sub_sig' mul_sig' square_sig' opp_sig'])
           ty existing_sig id.

Ltac pose_carry_sig wt m base sz s c carry_chains carry_sig :=
  cache_sig_with_type_by_existing_sig
    {carry : (Z^sz -> Z^sz)%type |
     forall a : Z^sz,
       let eval := Positional.Fdecode (m := m) wt in
       eval (carry a) = eval a}
    (carry_sig' m base sz s c carry_chains)
    carry_sig.

Ltac pose_zero_sig wt m base sz sz_nonzero base_pos zero_sig :=
  cache_vm_sig_with_type
    { zero : Z^sz | Positional.Fdecode (m:=m) wt zero = 0%F}
    (zero_sig' m base sz sz_nonzero base_pos)
    zero_sig.

Ltac pose_one_sig wt m base sz sz_nonzero base_pos one_sig :=
  cache_vm_sig_with_type
    { one : Z^sz | Positional.Fdecode (m:=m) wt one = 1%F}
    (one_sig' m base sz sz_nonzero base_pos)
    one_sig.

Ltac pose_add_sig wt m base sz add_sig :=
  cache_sig_with_type_by_existing_sig
    { add : (Z^sz -> Z^sz -> Z^sz)%type |
      forall a b : Z^sz,
        let eval := Positional.Fdecode (m:=m) wt in
        eval (add a b) = (eval a + eval b)%F }
    (add_sig' m base sz)
    add_sig.

Ltac pose_sub_sig wt m base sz coef sub_sig :=
  cache_sig_with_type_by_existing_sig
    {sub : (Z^sz -> Z^sz -> Z^sz)%type |
     forall a b : Z^sz,
       let eval := Positional.Fdecode (m:=m) wt in
       eval (sub a b) = (eval a - eval b)%F}
    (sub_sig' m base sz coef)
    sub_sig.

Ltac pose_opp_sig wt m base sz coef opp_sig :=
  cache_sig_with_type_by_existing_sig
    {opp : (Z^sz -> Z^sz)%type |
     forall a : Z^sz,
       let eval := Positional.Fdecode (m := m) wt in
       eval (opp a) = F.opp (eval a)}
    (opp_sig' m base sz coef)
    opp_sig.

Ltac pose_mul_sig wt m base sz s c mul_code sz_nonzero s_nonzero base_pos mul_code_correct mul_sig :=
  cache_sig_with_type_by_existing_sig
    {mul : (Z^sz -> Z^sz -> Z^sz)%type |
     forall a b : Z^sz,
       let eval := Positional.Fdecode (m := m) wt in
       eval (mul a b) = (eval a * eval b)%F}
    (mul_sig' m base sz s c mul_code sz_nonzero s_nonzero base_pos mul_code_correct)
    mul_sig.

Ltac pose_square_sig wt m base sz s c square_code sz_nonzero s_nonzero base_pos square_code_correct square_sig :=
  cache_sig_with_type_by_existing_sig
    {square : (Z^sz -> Z^sz)%type |
     forall a : Z^sz,
       let eval := Positional.Fdecode (m := m) wt in
       eval (square a) = (eval a * eval a)%F}
    (square_sig' m base sz s c square_code sz_nonzero s_nonzero base_pos square_code_correct)
    square_sig.

Ltac pose_ring sz m wt wt_divides' sz_nonzero wt_nonzero zero_sig one_sig opp_sig add_sig sub_sig mul_sig ring :=
  cache_term
    (Ring.ring_by_isomorphism
       (F := F m)
       (H := Z^sz)
       (phi := Positional.Fencode wt)
       (phi' := Positional.Fdecode wt)
       (zero := proj1_sig zero_sig)
       (one := proj1_sig one_sig)
       (opp := proj1_sig opp_sig)
       (add := proj1_sig add_sig)
       (sub := proj1_sig sub_sig)
       (mul := proj1_sig mul_sig)
       (phi'_zero := proj2_sig zero_sig)
       (phi'_one := proj2_sig one_sig)
       (phi'_opp := proj2_sig opp_sig)
       (Positional.Fdecode_Fencode_id
          (sz_nonzero := sz_nonzero)
          (div_mod := div_mod)
          (modulo_cps_id:=@Core.modulo_id)
          (div_cps_id:=@Core.div_id)
          wt eq_refl wt_nonzero wt_divides')
       (Positional.eq_Feq_iff wt)
       (proj2_sig add_sig)
       (proj2_sig sub_sig)
       (proj2_sig mul_sig)
    )
    ring.

End Defaults.

End Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_Defaults_WRAPPED.
Module Export Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_Defaults.
Module Export Crypto.
Module Export Specific.
Module Export Framework.
Module Export ArithmeticSynthesis.
Module Defaults.
Include Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_Defaults_WRAPPED.Defaults.
End Defaults.

End ArithmeticSynthesis.

End Framework.

End Specific.

End Crypto.

End Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_Defaults.
Module Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_DefaultsPackage_WRAPPED.
Module DefaultsPackage.

Import Crypto.Specific.Framework.CurveParametersPackage.
Import Crypto.Specific.Framework.ArithmeticSynthesis.BasePackage.
Export Crypto.Specific.Framework.ArithmeticSynthesis.Defaults.
Import Crypto.Specific.Framework.Packages.
Import Crypto.Util.TagList.

Module TAG.
  Inductive tags := mul_code_correct | square_code_correct | carry_sig | zero_sig | one_sig | add_sig | sub_sig | opp_sig | mul_sig | square_sig | ring.
End TAG.

Ltac add_mul_code_correct pkg P_extra_prove_mul_eq :=
  Tag.update_by_tac_if_not_exists
    pkg
    TAG.mul_code_correct
    ltac:(fun _ => let sz := Tag.get pkg TAG.sz in
                   let sz2 := Tag.get pkg TAG.sz2 in
                   let wt := Tag.get pkg TAG.wt in
                   let s := Tag.get pkg TAG.s in
                   let c := Tag.get pkg TAG.c in
                   let mul_code := Tag.get pkg TAG.mul_code in
                   let mul_code_correct := fresh "mul_code_correct" in
                   let mul_code_correct := pose_mul_code_correct P_extra_prove_mul_eq sz sz2 wt s c mul_code mul_code_correct in
                   constr:(mul_code_correct)).
Ltac add_square_code_correct pkg P_extra_prove_square_eq :=
  Tag.update_by_tac_if_not_exists
    pkg
    TAG.square_code_correct
    ltac:(fun _ => let sz := Tag.get pkg TAG.sz in
                   let sz2 := Tag.get pkg TAG.sz2 in
                   let wt := Tag.get pkg TAG.wt in
                   let s := Tag.get pkg TAG.s in
                   let c := Tag.get pkg TAG.c in
                   let square_code := Tag.get pkg TAG.square_code in
                   let square_code_correct := fresh "square_code_correct" in
                   let square_code_correct := pose_square_code_correct P_extra_prove_square_eq sz sz2 wt s c square_code square_code_correct in
                   constr:(square_code_correct)).
Ltac add_carry_sig pkg :=
  Tag.update_by_tac_if_not_exists
    pkg
    TAG.carry_sig
    ltac:(fun _ => let wt := Tag.get pkg TAG.wt in
                   let m := Tag.get pkg TAG.m in
                   let base := Tag.get pkg TAG.base in
                   let sz := Tag.get pkg TAG.sz in
                   let s := Tag.get pkg TAG.s in
                   let c := Tag.get pkg TAG.c in
                   let carry_chains := Tag.get pkg TAG.carry_chains in
                   let carry_sig := fresh "carry_sig" in
                   let carry_sig := pose_carry_sig wt m base sz s c carry_chains carry_sig in
                   constr:(carry_sig)).
Ltac add_zero_sig pkg :=
  Tag.update_by_tac_if_not_exists
    pkg
    TAG.zero_sig
    ltac:(fun _ => let wt := Tag.get pkg TAG.wt in
                   let m := Tag.get pkg TAG.m in
                   let base := Tag.get pkg TAG.base in
                   let sz := Tag.get pkg TAG.sz in
                   let sz_nonzero := Tag.get pkg TAG.sz_nonzero in
                   let base_pos := Tag.get pkg TAG.base_pos in
                   let zero_sig := fresh "zero_sig" in
                   let zero_sig := pose_zero_sig wt m base sz sz_nonzero base_pos zero_sig in
                   constr:(zero_sig)).
Ltac add_one_sig pkg :=
  Tag.update_by_tac_if_not_exists
    pkg
    TAG.one_sig
    ltac:(fun _ => let wt := Tag.get pkg TAG.wt in
                   let m := Tag.get pkg TAG.m in
                   let base := Tag.get pkg TAG.base in
                   let sz := Tag.get pkg TAG.sz in
                   let sz_nonzero := Tag.get pkg TAG.sz_nonzero in
                   let base_pos := Tag.get pkg TAG.base_pos in
                   let one_sig := fresh "one_sig" in
                   let one_sig := pose_one_sig wt m base sz sz_nonzero base_pos one_sig in
                   constr:(one_sig)).
Ltac add_add_sig pkg :=
  Tag.update_by_tac_if_not_exists
    pkg
    TAG.add_sig
    ltac:(fun _ => let wt := Tag.get pkg TAG.wt in
                   let m := Tag.get pkg TAG.m in
                   let base := Tag.get pkg TAG.base in
                   let sz := Tag.get pkg TAG.sz in
                   let add_sig := fresh "add_sig" in
                   let add_sig := pose_add_sig wt m base sz add_sig in
                   constr:(add_sig)).
Ltac add_sub_sig pkg :=
  Tag.update_by_tac_if_not_exists
    pkg
    TAG.sub_sig
    ltac:(fun _ => let wt := Tag.get pkg TAG.wt in
                   let m := Tag.get pkg TAG.m in
                   let base := Tag.get pkg TAG.base in
                   let sz := Tag.get pkg TAG.sz in
                   let coef := Tag.get pkg TAG.coef in
                   let sub_sig := fresh "sub_sig" in
                   let sub_sig := pose_sub_sig wt m base sz coef sub_sig in
                   constr:(sub_sig)).
Ltac add_opp_sig pkg :=
  Tag.update_by_tac_if_not_exists
    pkg
    TAG.opp_sig
    ltac:(fun _ => let wt := Tag.get pkg TAG.wt in
                   let m := Tag.get pkg TAG.m in
                   let base := Tag.get pkg TAG.base in
                   let sz := Tag.get pkg TAG.sz in
                   let coef := Tag.get pkg TAG.coef in
                   let opp_sig := fresh "opp_sig" in
                   let opp_sig := pose_opp_sig wt m base sz coef opp_sig in
                   constr:(opp_sig)).
Ltac add_mul_sig pkg :=
  Tag.update_by_tac_if_not_exists
    pkg
    TAG.mul_sig
    ltac:(fun _ => let wt := Tag.get pkg TAG.wt in
                   let m := Tag.get pkg TAG.m in
                   let base := Tag.get pkg TAG.base in
                   let sz := Tag.get pkg TAG.sz in
                   let s := Tag.get pkg TAG.s in
                   let c := Tag.get pkg TAG.c in
                   let mul_code := Tag.get pkg TAG.mul_code in
                   let sz_nonzero := Tag.get pkg TAG.sz_nonzero in
                   let s_nonzero := Tag.get pkg TAG.s_nonzero in
                   let base_pos := Tag.get pkg TAG.base_pos in
                   let mul_code_correct := Tag.get pkg TAG.mul_code_correct in
                   let mul_sig := fresh "mul_sig" in
                   let mul_sig := pose_mul_sig wt m base sz s c mul_code sz_nonzero s_nonzero base_pos mul_code_correct mul_sig in
                   constr:(mul_sig)).
Ltac add_square_sig pkg :=
  Tag.update_by_tac_if_not_exists
    pkg
    TAG.square_sig
    ltac:(fun _ => let wt := Tag.get pkg TAG.wt in
                   let m := Tag.get pkg TAG.m in
                   let base := Tag.get pkg TAG.base in
                   let sz := Tag.get pkg TAG.sz in
                   let s := Tag.get pkg TAG.s in
                   let c := Tag.get pkg TAG.c in
                   let square_code := Tag.get pkg TAG.square_code in
                   let sz_nonzero := Tag.get pkg TAG.sz_nonzero in
                   let s_nonzero := Tag.get pkg TAG.s_nonzero in
                   let base_pos := Tag.get pkg TAG.base_pos in
                   let square_code_correct := Tag.get pkg TAG.square_code_correct in
                   let square_sig := fresh "square_sig" in
                   let square_sig := pose_square_sig wt m base sz s c square_code sz_nonzero s_nonzero base_pos square_code_correct square_sig in
                   constr:(square_sig)).
Ltac add_ring pkg :=
  Tag.update_by_tac_if_not_exists
    pkg
    TAG.ring
    ltac:(fun _ => let sz := Tag.get pkg TAG.sz in
                   let m := Tag.get pkg TAG.m in
                   let wt := Tag.get pkg TAG.wt in
                   let wt_divides' := Tag.get pkg TAG.wt_divides' in
                   let sz_nonzero := Tag.get pkg TAG.sz_nonzero in
                   let wt_nonzero := Tag.get pkg TAG.wt_nonzero in
                   let zero_sig := Tag.get pkg TAG.zero_sig in
                   let one_sig := Tag.get pkg TAG.one_sig in
                   let opp_sig := Tag.get pkg TAG.opp_sig in
                   let add_sig := Tag.get pkg TAG.add_sig in
                   let sub_sig := Tag.get pkg TAG.sub_sig in
                   let mul_sig := Tag.get pkg TAG.mul_sig in
                   let ring := fresh "ring" in
                   let ring := pose_ring sz m wt wt_divides' sz_nonzero wt_nonzero zero_sig one_sig opp_sig add_sig sub_sig mul_sig ring in
                   constr:(ring)).
Ltac add_Defaults_package pkg P_extra_prove_mul_eq P_extra_prove_square_eq :=
  let pkg := add_mul_code_correct pkg P_extra_prove_mul_eq in
  let pkg := add_square_code_correct pkg P_extra_prove_square_eq in
  let pkg := add_carry_sig pkg in
  let pkg := add_zero_sig pkg in
  let pkg := add_one_sig pkg in
  let pkg := add_add_sig pkg in
  let pkg := add_sub_sig pkg in
  let pkg := add_opp_sig pkg in
  let pkg := add_mul_sig pkg in
  let pkg := add_square_sig pkg in
  let pkg := add_ring pkg in
  Tag.strip_subst_local pkg.

Module MakeDefaultsPackage (PKG : PrePackage).
  Module Import MakeDefaultsPackageInternal := MakePackageBase PKG.

  Ltac get_mul_code_correct _ := get TAG.mul_code_correct.
  Notation mul_code_correct := (ltac:(let v := get_mul_code_correct () in exact v)) (only parsing).
  Ltac get_square_code_correct _ := get TAG.square_code_correct.
  Notation square_code_correct := (ltac:(let v := get_square_code_correct () in exact v)) (only parsing).
  Ltac get_carry_sig _ := get TAG.carry_sig.
  Notation carry_sig := (ltac:(let v := get_carry_sig () in exact v)) (only parsing).
  Ltac get_zero_sig _ := get TAG.zero_sig.
  Notation zero_sig := (ltac:(let v := get_zero_sig () in exact v)) (only parsing).
  Ltac get_one_sig _ := get TAG.one_sig.
  Notation one_sig := (ltac:(let v := get_one_sig () in exact v)) (only parsing).
  Ltac get_add_sig _ := get TAG.add_sig.
  Notation add_sig := (ltac:(let v := get_add_sig () in exact v)) (only parsing).
  Ltac get_sub_sig _ := get TAG.sub_sig.
  Notation sub_sig := (ltac:(let v := get_sub_sig () in exact v)) (only parsing).
  Ltac get_opp_sig _ := get TAG.opp_sig.
  Notation opp_sig := (ltac:(let v := get_opp_sig () in exact v)) (only parsing).
  Ltac get_mul_sig _ := get TAG.mul_sig.
  Notation mul_sig := (ltac:(let v := get_mul_sig () in exact v)) (only parsing).
  Ltac get_square_sig _ := get TAG.square_sig.
  Notation square_sig := (ltac:(let v := get_square_sig () in exact v)) (only parsing).
  Ltac get_ring _ := get TAG.ring.
  Notation ring := (ltac:(let v := get_ring () in exact v)) (only parsing).
End MakeDefaultsPackage.

End DefaultsPackage.

End Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_DefaultsPackage_WRAPPED.
Module Export Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_DefaultsPackage.
Module Export Crypto.
Module Export Specific.
Module Export Framework.
Module Export ArithmeticSynthesis.
Module DefaultsPackage.
Include Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_DefaultsPackage_WRAPPED.DefaultsPackage.
End DefaultsPackage.

End ArithmeticSynthesis.

End Framework.

End Specific.

End Crypto.

End Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_DefaultsPackage.
Module Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_Freeze_WRAPPED.
Module Freeze.
Import Coq.ZArith.ZArith Coq.ZArith.BinIntDef.
Import Coq.QArith.QArith_base.
Import Coq.Lists.List.
Import ListNotations.
Import Crypto.Arithmetic.CoreUnfolder.
Import Crypto.Arithmetic.Saturated.CoreUnfolder.
Import Crypto.Arithmetic.Saturated.FreezeUnfolder.
Import Crypto.Arithmetic.Core.
Import B.
Import Crypto.Arithmetic.Saturated.Freeze.
Import Crypto.Specific.Framework.ArithmeticSynthesis.Base.
Import Crypto.Specific.Framework.ArithmeticSynthesis.HelperTactics.
Import Crypto.Util.Decidable.
Import Crypto.Util.LetIn Crypto.Util.ZUtil.Definitions.
Import Crypto.Util.Tactics.CacheTerm.

Module Export Exports.
  Global Hint Opaque freeze : uncps.
#[global]
  Hint Rewrite freeze_id : uncps.
End Exports.

Local Open Scope Z_scope.
Local Infix "^" := Tuple.tuple : type_scope.

Section gen.
  Context (m : positive)
          (base : Q)
          (sz : nat)
          (c : list limb)
          (bitwidth : Z)
          (m_enc : Z^sz)
          (base_pos : (1 <= base)%Q)
          (sz_nonzero : sz <> 0%nat).

  Local Notation wt := (wt_gen base).
  Local Notation sz2 := (sz2' sz).
  Local Notation wt_divides' := (wt_gen_divides' base base_pos).
  Local Notation wt_nonzero := (wt_gen_nonzero base base_pos).

  Context (c_small : 0 < Associational.eval c < wt sz)
          (m_enc_bounded : Tuple.map (BinInt.Z.land (Z.ones bitwidth)) m_enc = m_enc)
          (m_enc_correct : Positional.eval wt m_enc = Z.pos m)
          (m_correct_wt : Z.pos m = wt sz - Associational.eval c).

  Definition freeze_sig'
    : { freeze : (Z^sz -> Z^sz)%type |
        forall a : Z^sz,
          (0 <= Positional.eval wt a < 2 * Z.pos m)->
          let eval := Positional.Fdecode (m := m) wt in
          eval (freeze a) = eval a }.
  Proof.
    eexists; cbv beta zeta; (intros a ?).
    pose proof wt_nonzero; pose proof (wt_gen_pos base base_pos).
    pose proof (wt_gen0_1 base).
    pose proof div_mod; pose proof (wt_gen_divides base base_pos).
    pose proof (wt_gen_multiples base base_pos).
    pose proof div_correct; pose proof modulo_correct.
    let x := constr:(freeze (n:=sz) wt (Z.ones bitwidth) m_enc a) in
    presolve_op_F constr:(wt) x;
      [ autorewrite with pattern_runtime; reflexivity | ].
    reflexivity.
  Defined.
End gen.

Ltac pose_m_correct_wt m c sz wt m_correct_wt :=
  cache_proof_with_type_by
    (Z.pos m = wt sz - Associational.eval c)
    ltac:(vm_decide_no_check)
           m_correct_wt.

Ltac pose_freeze_sig wt m base sz c bitwidth m_enc base_pos sz_nonzero freeze_sig :=
  cache_sig_with_type_by_existing_sig_helper
    ltac:(fun _ => cbv [freeze_sig'])
           {freeze : (Z^sz -> Z^sz)%type |
            forall a : Z^sz,
              (0 <= Positional.eval wt a < 2 * Z.pos m)->
              let eval := Positional.Fdecode (m := m) wt in
              eval (freeze a) = eval a}
           (freeze_sig' m base sz c bitwidth m_enc base_pos sz_nonzero)
           freeze_sig.

End Freeze.

End Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_Freeze_WRAPPED.
Module Export Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_Freeze.
Module Export Crypto.
Module Export Specific.
Module Export Framework.
Module Export ArithmeticSynthesis.
Module Freeze.
Include Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_Freeze_WRAPPED.Freeze.
End Freeze.

End ArithmeticSynthesis.

End Framework.

End Specific.

End Crypto.

End Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_Freeze.
Module Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_FreezePackage_WRAPPED.
Module FreezePackage.

Import Crypto.Specific.Framework.CurveParametersPackage.
Import Crypto.Specific.Framework.ArithmeticSynthesis.BasePackage.
Export Crypto.Specific.Framework.ArithmeticSynthesis.Freeze.
Import Crypto.Specific.Framework.Packages.
Import Crypto.Util.TagList.

Module TAG.
  Inductive tags := m_correct_wt | freeze_sig.
End TAG.

Ltac add_m_correct_wt pkg :=
  if_freeze
    pkg
    ltac:(fun _ => Tag.update_by_tac_if_not_exists
                       pkg
                       TAG.m_correct_wt
                       ltac:(fun _ => let m := Tag.get pkg TAG.m in
                                      let c := Tag.get pkg TAG.c in
                                      let sz := Tag.get pkg TAG.sz in
                                      let wt := Tag.get pkg TAG.wt in
                                      let m_correct_wt := fresh "m_correct_wt" in
                                      let m_correct_wt := pose_m_correct_wt m c sz wt m_correct_wt in
                                      constr:(m_correct_wt)))
    ltac:(fun _ => pkg)
    ().
Ltac add_freeze_sig pkg :=
  if_freeze
    pkg
    ltac:(fun _ => Tag.update_by_tac_if_not_exists
                       pkg
                       TAG.freeze_sig
                       ltac:(fun _ => let wt := Tag.get pkg TAG.wt in
                                      let m := Tag.get pkg TAG.m in
                                      let base := Tag.get pkg TAG.base in
                                      let sz := Tag.get pkg TAG.sz in
                                      let c := Tag.get pkg TAG.c in
                                      let bitwidth := Tag.get pkg TAG.bitwidth in
                                      let m_enc := Tag.get pkg TAG.m_enc in
                                      let base_pos := Tag.get pkg TAG.base_pos in
                                      let sz_nonzero := Tag.get pkg TAG.sz_nonzero in
                                      let freeze_sig := fresh "freeze_sig" in
                                      let freeze_sig := pose_freeze_sig wt m base sz c bitwidth m_enc base_pos sz_nonzero freeze_sig in
                                      constr:(freeze_sig)))
    ltac:(fun _ => pkg)
    ().
Ltac add_Freeze_package pkg :=
  let pkg := add_m_correct_wt pkg in
  let pkg := add_freeze_sig pkg in
  Tag.strip_subst_local pkg.

Module MakeFreezePackage (PKG : PrePackage).
  Module Import MakeFreezePackageInternal := MakePackageBase PKG.

  Ltac get_m_correct_wt _ := get TAG.m_correct_wt.
  Notation m_correct_wt := (ltac:(let v := get_m_correct_wt () in exact v)) (only parsing).
  Ltac get_freeze_sig _ := get TAG.freeze_sig.
  Notation freeze_sig := (ltac:(let v := get_freeze_sig () in exact v)) (only parsing).
End MakeFreezePackage.

End FreezePackage.

End Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_FreezePackage_WRAPPED.
Module Export Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_FreezePackage.
Module Export Crypto.
Module Export Specific.
Module Export Framework.
Module Export ArithmeticSynthesis.
Module FreezePackage.
Include Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_FreezePackage_WRAPPED.FreezePackage.
End FreezePackage.

End ArithmeticSynthesis.

End Framework.

End Specific.

End Crypto.

End Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_FreezePackage.
Module Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_SquareFromMul_WRAPPED.
Module SquareFromMul.
Import Coq.ZArith.ZArith Coq.ZArith.BinIntDef.
Import Coq.Lists.List.
Import ListNotations.
Import Crypto.Arithmetic.Core.
Import B.
Import Crypto.Arithmetic.PrimeFieldTheorems.
Import Crypto.Specific.Framework.ArithmeticSynthesis.HelperTactics.
Import Crypto.Util.Tactics.CacheTerm.

Local Notation tuple := Tuple.tuple.
Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Infix "^" := tuple : type_scope.

Ltac pose_square_sig sz m wt mul_sig square_sig :=
  cache_term_with_type_by
    {square : (Z^sz -> Z^sz)%type |
     forall a : Z^sz,
       let eval := Positional.Fdecode (m := m) wt in
       Positional.Fdecode (m := m) wt (square a) = (eval a * eval a)%F}
    ltac:(idtac;
          let a := fresh "a" in
          eexists; cbv beta zeta; intros a;
          rewrite <-(proj2_sig mul_sig);
          apply f_equal;
          cbv [proj1_sig mul_sig];
          reflexivity)
           square_sig.

End SquareFromMul.

End Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_SquareFromMul_WRAPPED.
Module Export Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_SquareFromMul.
Module Export Crypto.
Module Export Specific.
Module Export Framework.
Module Export ArithmeticSynthesis.
Module SquareFromMul.
Include Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_SquareFromMul_WRAPPED.SquareFromMul.
End SquareFromMul.

End ArithmeticSynthesis.

End Framework.

End Specific.

End Crypto.

End Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_SquareFromMul.
Module Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_Karatsuba_WRAPPED.
Module Karatsuba.
Import Coq.ZArith.ZArith Coq.ZArith.BinIntDef.
Import Coq.QArith.QArith_base.
Import Coq.Lists.List.
Import ListNotations.
Import Crypto.Arithmetic.CoreUnfolder.
Import Crypto.Arithmetic.Core.
Import B.
Import Crypto.Arithmetic.PrimeFieldTheorems.
Import Crypto.Util.Decidable.
Import Crypto.Util.LetIn.
Import Crypto.Arithmetic.Karatsuba.
Import Crypto.Util.Tactics.BreakMatch.
Import Crypto.Util.IdfunWithAlt.
Import Crypto.Util.Tactics.VM.
Import Crypto.Util.QUtil.
Import Crypto.Util.ZUtil.ModInv.
Import Crypto.Specific.Framework.ArithmeticSynthesis.SquareFromMul.
Import Crypto.Specific.Framework.ArithmeticSynthesis.Base.
Import Crypto.Specific.Framework.ArithmeticSynthesis.HelperTactics.
Import Crypto.Util.Tactics.PoseTermWithName.
Import Crypto.Util.Tactics.CacheTerm.

Local Open Scope Z_scope.
Local Infix "^" := Tuple.tuple : type_scope.

Ltac internal_pose_sqrt_s s sqrt_s :=
  let v := (eval vm_compute in (Z.log2 s / 2)) in
  cache_term (2^v) sqrt_s.

Section gen.
  Context (m : positive)
          (base : Q)
          (sz : nat)
          (s : Z)
          (c : list limb)
          (half_sz : nat)
          (sqrt_s : Z)
          (base_pos : (1 <= base)%Q)
          (sz_nonzero : sz <> 0%nat)
          (half_sz_nonzero : half_sz <> 0%nat)
          (s_nonzero : s <> 0%Z)
          (m_correct : Z.pos m = s - Associational.eval c)
          (sqrt_s_nonzero : sqrt_s <> 0)
          (sqrt_s_mod_m : sqrt_s ^ 2 mod Z.pos m = (sqrt_s + 1) mod Z.pos m).

  Local Notation wt := (wt_gen base).
  Local Notation wt_divides' := (wt_gen_divides' base base_pos).
  Local Notation wt_nonzero := (wt_gen_nonzero base base_pos).

  Definition goldilocks_mul_sig'
    : { mul : (Z^sz -> Z^sz -> Z^sz)%type
      | forall a b : Z^sz,
          mul a b = goldilocks_mul_cps (n:=half_sz) (n2:=sz) wt sqrt_s a b (fun ab => Positional.reduce_cps (n:=sz) wt s c ab id) }.
  Proof.
    eexists; cbv beta zeta; intros.
    cbv [goldilocks_mul_cps].
    autorewrite with pattern_runtime.
    reflexivity.
  Defined.

  Definition mul_sig'
    : { mul : (Z^sz -> Z^sz -> Z^sz)%type
      | forall a b : Z^sz,
          let eval := Positional.Fdecode (m := m) wt in
          Positional.Fdecode (m := m) wt (mul a b) = (eval a * eval b)%F }.
  Proof.
    eexists; cbv beta zeta; intros a b.
    pose proof wt_nonzero.
    pose proof (wt_gen0_1 base).
    let x := constr:(
               goldilocks_mul_cps (n:=half_sz) (n2:=sz) wt sqrt_s a b (fun ab => Positional.reduce_cps (n:=sz) wt s c ab id)) in
    presolve_op_F constr:(wt) x;
      [ cbv [goldilocks_mul_cps];
        autorewrite with pattern_runtime;
        reflexivity
      | ].
    reflexivity.
  Defined.
End gen.

Ltac pose_half_sz_nonzero half_sz half_sz_nonzero :=
  cache_proof_with_type_by
    (half_sz <> 0%nat)
    ltac:(cbv; congruence)
           half_sz_nonzero.

Ltac pose_mul_sig wt m base sz s c half_sz mul_sig :=
  let sqrt_s := fresh "sqrt_s" in
  let sqrt_s := internal_pose_sqrt_s s sqrt_s in
  cache_sig_with_type_by_existing_sig_helper
    ltac:(fun _ => cbv [mul_sig'])
           { mul : (Z^sz -> Z^sz -> Z^sz)%type
           | forall a b : Z^sz,
               let eval := Positional.Fdecode (m := m) wt in
               Positional.Fdecode (m := m) wt (mul a b) = (eval a * eval b)%F }
           (mul_sig' m base sz s c half_sz sqrt_s)
           mul_sig.

Ltac pose_square_sig sz m wt mul_sig square_sig :=
  SquareFromMul.pose_square_sig sz m wt mul_sig square_sig.

End Karatsuba.

End Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_Karatsuba_WRAPPED.
Module Export Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_Karatsuba.
Module Export Crypto.
Module Export Specific.
Module Export Framework.
Module Export ArithmeticSynthesis.
Module Karatsuba.
Include Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_Karatsuba_WRAPPED.Karatsuba.
End Karatsuba.

End ArithmeticSynthesis.

End Framework.

End Specific.

End Crypto.

End Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_Karatsuba.
Module Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_KaratsubaPackage_WRAPPED.
Module KaratsubaPackage.

Import Crypto.Specific.Framework.CurveParametersPackage.
Import Crypto.Specific.Framework.ArithmeticSynthesis.BasePackage.
Import Crypto.Specific.Framework.ArithmeticSynthesis.DefaultsPackage.
Export Crypto.Specific.Framework.ArithmeticSynthesis.Karatsuba.
Import Crypto.Specific.Framework.Packages.
Import Crypto.Util.TagList.

Module TAG.
  Inductive tags := half_sz_nonzero.
End TAG.

Ltac add_half_sz_nonzero pkg :=
  if_goldilocks
    pkg
    ltac:(fun _ => let half_sz := Tag.get pkg TAG.half_sz in
                   let half_sz_nonzero := fresh "half_sz_nonzero" in
                   let half_sz_nonzero := pose_half_sz_nonzero half_sz half_sz_nonzero in
                   Tag.update pkg TAG.half_sz_nonzero half_sz_nonzero)
    ltac:(fun _ => pkg)
    ().
Ltac add_mul_sig pkg :=
  if_goldilocks
    pkg
    ltac:(fun _ => let wt := Tag.get pkg TAG.wt in
                   let m := Tag.get pkg TAG.m in
                   let base := Tag.get pkg TAG.base in
                   let sz := Tag.get pkg TAG.sz in
                   let s := Tag.get pkg TAG.s in
                   let c := Tag.get pkg TAG.c in
                   let half_sz := Tag.get pkg TAG.half_sz in
                   let mul_sig := fresh "mul_sig" in
                   let mul_sig := pose_mul_sig wt m base sz s c half_sz mul_sig in
                   Tag.update pkg TAG.mul_sig mul_sig)
    ltac:(fun _ => pkg)
    ().
Ltac add_square_sig pkg :=
  if_goldilocks
    pkg
    ltac:(fun _ => let sz := Tag.get pkg TAG.sz in
                   let m := Tag.get pkg TAG.m in
                   let wt := Tag.get pkg TAG.wt in
                   let mul_sig := Tag.get pkg TAG.mul_sig in
                   let square_sig := fresh "square_sig" in
                   let square_sig := pose_square_sig sz m wt mul_sig square_sig in
                   Tag.update pkg TAG.square_sig square_sig)
    ltac:(fun _ => pkg)
    ().
Ltac add_Karatsuba_package pkg :=
  let pkg := add_half_sz_nonzero pkg in
  let pkg := add_mul_sig pkg in
  let pkg := add_square_sig pkg in
  Tag.strip_subst_local pkg.

Module MakeKaratsubaPackage (PKG : PrePackage).
  Module Import MakeKaratsubaPackageInternal := MakePackageBase PKG.

  Ltac get_half_sz_nonzero _ := get TAG.half_sz_nonzero.
  Notation half_sz_nonzero := (ltac:(let v := get_half_sz_nonzero () in exact v)) (only parsing).
End MakeKaratsubaPackage.

End KaratsubaPackage.

End Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_KaratsubaPackage_WRAPPED.
Module Export Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_KaratsubaPackage.
Module Export Crypto.
Module Export Specific.
Module Export Framework.
Module Export ArithmeticSynthesis.
Module KaratsubaPackage.
Include Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_KaratsubaPackage_WRAPPED.KaratsubaPackage.
End KaratsubaPackage.

End ArithmeticSynthesis.

End Framework.

End Specific.

End Crypto.

End Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_KaratsubaPackage.
Module Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_Ladderstep_WRAPPED.
Module Ladderstep.
Import Coq.ZArith.BinIntDef.
Import Crypto.Arithmetic.Core.
Import B.
Import Crypto.Arithmetic.PrimeFieldTheorems.
Import Crypto.Curves.Montgomery.XZ.
Import Crypto.Specific.Framework.ArithmeticSynthesis.HelperTactics.
Import Crypto.Util.Tuple.
Import Crypto.Util.LetIn.
Import Crypto.Util.Notations.
Import Crypto.Util.Tactics.PoseTermWithName.
Import Crypto.Util.Tactics.CacheTerm.
Import Crypto.Util.Option.

Local Notation tuple := Tuple.tuple.
Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Infix "^" := tuple : type_scope.

Definition FMxzladderstep {m} := @M.donnaladderstep (F m) F.add F.sub F.mul.

Section with_notations.
  Context sz (add sub mul : tuple Z sz -> tuple Z sz -> tuple Z sz)
          (square carry : tuple Z sz -> tuple Z sz).
  Local Infix "+" := add.
  Local Notation "a * b" := (carry (mul a b)).
  Local Notation "x ^ 2" := (carry (square x)).
  Local Infix "-" := sub.
  Definition Mxzladderstep a24 x1 Q Q'
    := match Q, Q' with
       | (x, z), (x', z') =>
         dlet origx := x in
         dlet x := x + z in
         dlet z := origx - z in
         dlet origx' := x' in
         dlet x' := x' + z' in
         dlet z' := origx' - z' in
         dlet xx' := x' * z in
         dlet zz' := x * z' in
         dlet origx' := xx' in
         dlet xx' := xx' + zz' in
         dlet zz' := origx' - zz' in
         dlet x3 := xx'^2 in
         dlet zzz' := zz'^2 in
         dlet z3 := zzz' * x1 in
         dlet xx := x^2 in
         dlet zz := z^2 in
         dlet x2 := xx * zz in
         dlet zz := xx - zz in
         dlet zzz := zz * a24 in
         dlet zzz := zzz + xx in
         dlet z2 := zz * zzz in
         ((x2, z2), (x3, z3))%core
       end.
End with_notations.

Ltac pose_a24' a24 a24' :=
  let a24 := (eval vm_compute in (invert_Some a24)) in
  cache_term_with_type_by
    Z
    ltac:(exact a24)
           a24'.

Ltac pose_a24_sig sz m wt a24' a24_sig :=
  cache_term_with_type_by
    { a24t : Z^sz | Positional.Fdecode (m:=m) wt a24t = F.of_Z m a24' }
    solve_constant_sig
    a24_sig.

Ltac pose_Mxzladderstep_sig sz wt m add_sig sub_sig mul_sig square_sig carry_sig Mxzladderstep_sig :=
  cache_term_with_type_by
    { xzladderstep : tuple Z sz -> tuple Z sz -> tuple Z sz * tuple Z sz -> tuple Z sz * tuple Z sz -> tuple Z sz * tuple Z sz * (tuple Z sz * tuple Z sz)
    | forall a24 x1 Q Q', let eval := B.Positional.Fdecode wt in Tuple.map (n:=2) (Tuple.map (n:=2) eval) (xzladderstep a24 x1 Q Q') = FMxzladderstep (m:=m) (eval a24) (eval x1) (Tuple.map (n:=2) eval Q) (Tuple.map (n:=2) eval Q') }
    ltac:((exists (Mxzladderstep sz (proj1_sig add_sig) (proj1_sig sub_sig) (proj1_sig mul_sig) (proj1_sig square_sig) (proj1_sig carry_sig)));
          let a24 := fresh "a24" in
          let x1 := fresh "x1" in
          let Q := fresh "Q" in
          let Q' := fresh "Q'" in
          let eval := fresh "eval" in
          intros a24 x1 Q Q' eval;
          cbv [Mxzladderstep FMxzladderstep M.donnaladderstep];
          destruct Q, Q'; cbv [map map' fst snd Let_In eval];
          repeat match goal with
                 | [ |- context[@proj1_sig ?a ?b ?s] ]
                   => rewrite !(@proj2_sig a b s)
                 end;
          reflexivity)
           Mxzladderstep_sig.

End Ladderstep.

End Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_Ladderstep_WRAPPED.
Module Export Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_Ladderstep.
Module Export Crypto.
Module Export Specific.
Module Export Framework.
Module Export ArithmeticSynthesis.
Module Ladderstep.
Include Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_Ladderstep_WRAPPED.Ladderstep.
End Ladderstep.

End ArithmeticSynthesis.

End Framework.

End Specific.

End Crypto.

End Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_Ladderstep.
Module Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_LadderstepPackage_WRAPPED.
Module LadderstepPackage.

Import Crypto.Specific.Framework.CurveParametersPackage.
Import Crypto.Specific.Framework.ArithmeticSynthesis.BasePackage.
Import Crypto.Specific.Framework.ArithmeticSynthesis.DefaultsPackage.
Export Crypto.Specific.Framework.ArithmeticSynthesis.Ladderstep.
Import Crypto.Specific.Framework.Packages.
Import Crypto.Util.TagList.

Module TAG.
  Inductive tags := a24' | a24_sig | Mxzladderstep_sig.
End TAG.

Ltac add_a24' pkg :=
  if_ladderstep
    pkg
    ltac:(fun _ => Tag.update_by_tac_if_not_exists
                       pkg
                       TAG.a24'
                       ltac:(fun _ => let a24 := Tag.get pkg TAG.a24 in
                                      let a24' := fresh "a24'" in
                                      let a24' := pose_a24' a24 a24' in
                                      constr:(a24')))
    ltac:(fun _ => pkg)
    ().
Ltac add_a24_sig pkg :=
  if_ladderstep
    pkg
    ltac:(fun _ => Tag.update_by_tac_if_not_exists
                       pkg
                       TAG.a24_sig
                       ltac:(fun _ => let sz := Tag.get pkg TAG.sz in
                                      let m := Tag.get pkg TAG.m in
                                      let wt := Tag.get pkg TAG.wt in
                                      let a24' := Tag.get pkg TAG.a24' in
                                      let a24_sig := fresh "a24_sig" in
                                      let a24_sig := pose_a24_sig sz m wt a24' a24_sig in
                                      constr:(a24_sig)))
    ltac:(fun _ => pkg)
    ().
Ltac add_Mxzladderstep_sig pkg :=
  if_ladderstep
    pkg
    ltac:(fun _ => Tag.update_by_tac_if_not_exists
                       pkg
                       TAG.Mxzladderstep_sig
                       ltac:(fun _ => let sz := Tag.get pkg TAG.sz in
                                      let wt := Tag.get pkg TAG.wt in
                                      let m := Tag.get pkg TAG.m in
                                      let add_sig := Tag.get pkg TAG.add_sig in
                                      let sub_sig := Tag.get pkg TAG.sub_sig in
                                      let mul_sig := Tag.get pkg TAG.mul_sig in
                                      let square_sig := Tag.get pkg TAG.square_sig in
                                      let carry_sig := Tag.get pkg TAG.carry_sig in
                                      let Mxzladderstep_sig := fresh "Mxzladderstep_sig" in
                                      let Mxzladderstep_sig := pose_Mxzladderstep_sig sz wt m add_sig sub_sig mul_sig square_sig carry_sig Mxzladderstep_sig in
                                      constr:(Mxzladderstep_sig)))
    ltac:(fun _ => pkg)
    ().
Ltac add_Ladderstep_package pkg :=
  let pkg := add_a24' pkg in
  let pkg := add_a24_sig pkg in
  let pkg := add_Mxzladderstep_sig pkg in
  Tag.strip_subst_local pkg.

Module MakeLadderstepPackage (PKG : PrePackage).
  Module Import MakeLadderstepPackageInternal := MakePackageBase PKG.

  Ltac get_a24' _ := get TAG.a24'.
  Notation a24' := (ltac:(let v := get_a24' () in exact v)) (only parsing).
  Ltac get_a24_sig _ := get TAG.a24_sig.
  Notation a24_sig := (ltac:(let v := get_a24_sig () in exact v)) (only parsing).
  Ltac get_Mxzladderstep_sig _ := get TAG.Mxzladderstep_sig.
  Notation Mxzladderstep_sig := (ltac:(let v := get_Mxzladderstep_sig () in exact v)) (only parsing).
End MakeLadderstepPackage.

End LadderstepPackage.

End Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_LadderstepPackage_WRAPPED.
Module Export Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_LadderstepPackage.
Module Export Crypto.
Module Export Specific.
Module Export Framework.
Module Export ArithmeticSynthesis.
Module LadderstepPackage.
Include Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_LadderstepPackage_WRAPPED.LadderstepPackage.
End LadderstepPackage.

End ArithmeticSynthesis.

End Framework.

End Specific.

End Crypto.

End Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_LadderstepPackage.
Module Crypto_DOT_Util_DOT_Sigma_DOT_Lift_WRAPPED.
Module Lift.
Export Crypto.Util.FixCoqMistakes.

Definition lift1_sig {A C} (P:A->C->Prop)
           (op_sig : forall (a:A), {c | P a c})
: { op : A -> C | forall (a:A), P a (op a) }
:= exist
     (fun op => forall a, P a (op a))
     (fun a => proj1_sig (op_sig a))
     (fun a => proj2_sig (op_sig a)).

Definition lift2_sig {A B C} (P:A->B->C->Prop)
           (op_sig : forall (a:A) (b:B), {c | P a b c})
  : { op : A -> B -> C | forall (a:A) (b:B), P a b (op a b) }
  := exist
       (fun op => forall a b, P a b (op a b))
       (fun a b => proj1_sig (op_sig a b))
       (fun a b => proj2_sig (op_sig a b)).

Definition lift3_sig {A B C D} (P:A->B->C->D->Prop)
           (op_sig : forall (a:A) (b:B) (c:C), {d | P a b c d})
  : { op : A -> B -> C -> D | forall (a:A) (b:B) (c:C), P a b c (op a b c) }
  := exist
       (fun op => forall a b c, P a b c (op a b c))
       (fun a b c => proj1_sig (op_sig a b c))
       (fun a b c => proj2_sig (op_sig a b c)).

Definition lift4_sig {A B C D E} (P:A->B->C->D->E->Prop)
           (op_sig : forall (a:A) (b:B) (c:C) (d:D), {e | P a b c d e})
  : { op : A -> B -> C -> D -> E | forall (a:A) (b:B) (c:C) (d:D), P a b c d (op a b c d) }
  := exist
       (fun op => forall a b c d, P a b c d (op a b c d))
       (fun a b c d => proj1_sig (op_sig a b c d))
       (fun a b c d => proj2_sig (op_sig a b c d)).

Definition lift4_sig_sig {A B C D E} {E' : A -> B -> C -> D -> E -> Prop}
           (P:forall (a:A) (b:B) (c:C) (d:D) (e:E), E' a b c d e -> Prop)
           (op_sig : forall (a:A) (b:B) (c:C) (d:D), {e : {e : E | E' a b c d e } | P a b c d (proj1_sig e) (proj2_sig e) })
           (opTP := fun op : A -> B -> C -> D -> E => forall a b c d, E' a b c d (op a b c d))
      : { op : sig opTP
    | forall (a:A) (b:B) (c:C) (d:D), P a b c d (proj1_sig op a b c d) (proj2_sig op a b c d) }
  := exist
       (fun op : sig opTP => forall a b c d, P a b c d (proj1_sig op a b c d) (proj2_sig op a b c d))
       (exist opTP (fun a b c d => proj1_sig (proj1_sig (op_sig a b c d))) (fun a b c d => proj2_sig (proj1_sig (op_sig a b c d))))
       (fun a b c d => proj2_sig (op_sig a b c d)).

End Lift.

End Crypto_DOT_Util_DOT_Sigma_DOT_Lift_WRAPPED.
Module Export Crypto_DOT_Util_DOT_Sigma_DOT_Lift.
Module Export Crypto.
Module Export Util.
Module Export Sigma.
Module Lift.
Include Crypto_DOT_Util_DOT_Sigma_DOT_Lift_WRAPPED.Lift.
End Lift.

End Sigma.

End Util.

End Crypto.

End Crypto_DOT_Util_DOT_Sigma_DOT_Lift.
Module Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_Montgomery_WRAPPED.
Module Montgomery.
Import Coq.micromega.Lia Coq.Classes.Morphisms Coq.Classes.Morphisms_Prop.
Import Crypto.Arithmetic.MontgomeryReduction.WordByWord.Definition.
Import Crypto.Arithmetic.MontgomeryReduction.WordByWord.Proofs.
Import Crypto.Arithmetic.Core.
Import B.
Import Crypto.Arithmetic.Saturated.UniformWeight.
Import Crypto.Util.Sigma.Lift.
Import Coq.ZArith.BinInt.
Import Coq.PArith.BinPos.
Import Crypto.Util.LetIn.
Import Crypto.Util.ZUtil.ModInv.
Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Import Crypto.Util.Tactics.DestructHead.
Import Crypto.Util.Tactics.BreakMatch.
Import Crypto.Util.Decidable.
Import Crypto.Arithmetic.Saturated.UniformWeightInstances.
Import Crypto.Specific.Framework.ArithmeticSynthesis.HelperTactics.
Import Crypto.Util.Tactics.CacheTerm.

Local Open Scope Z_scope.
Local Infix "^" := Tuple.tuple : type_scope.

Local Definition sig_by_eq {A P} (x : { a : A | P a }) (a : A) (H : a = proj1_sig x)
  : { a : A | P a }.
Proof.
  exists a; subst; exact (proj2_sig x).
Defined.

Section with_args.
  Context (wt : nat -> Z)
          (r : positive)
          (sz : nat)
          (m : positive)
          (m_enc : Z^sz)
          (r' : Z)
          (r'_correct : ((Z.pos r * r') mod (Z.pos m) = 1)%Z)
          (m' : Z)
          (m'_correct : ((Z.pos m * m') mod (Z.pos r) = (-1) mod Z.pos r)%Z)
          (m_enc_correct_montgomery : Z.pos m = MontgomeryAPI.eval (n:=sz) (Z.pos r) m_enc)
          (r'_pow_correct : ((r' ^ Z.of_nat sz * Z.pos r ^ Z.of_nat sz) mod MontgomeryAPI.eval (n:=sz) (Z.pos r) m_enc = 1)%Z)

          (r_big : Z.pos r > 1)
          (m_big : 1 < Z.pos m)
          (m_enc_small : small (Z.pos r) m_enc)
          (map_m_enc : Tuple.map (Z.land (Z.pos r - 1)) m_enc = m_enc).

  Local Ltac t_fin :=
    repeat match goal with
           | _ => assumption
           | [ |- ?x = ?x ] => reflexivity
           | [ |- and _ _ ] => split
           | [ |- (0 <= MontgomeryAPI.eval (Z.pos r) _)%Z ] => apply MontgomeryAPI.eval_small
           | _ => rewrite <- !m_enc_correct_montgomery
           | _ => rewrite !r'_correct
           | _ => rewrite !Z.mod_1_l by assumption; reflexivity
           | _ => rewrite !(Z.mul_comm m' (Z.pos m))
           | _ => lia
           end.

  Local Definition mul'_gen
    : { f:Z^sz -> Z^sz -> Z^sz
      | forall (A B : Z^sz),
          small (Z.pos r) A -> small (Z.pos r) B ->
          let eval := MontgomeryAPI.eval (Z.pos r) in
          (small (Z.pos r) (f A B)
           /\ (eval B < eval m_enc -> 0 <= eval (f A B) < eval m_enc)
           /\ (eval (f A B) mod Z.pos m
               = (eval A * eval B * r'^(Z.of_nat sz)) mod Z.pos m))%Z
      }.
  Proof.
    exists (fun A B => redc (r:=r)(R_numlimbs:=sz) m_enc A B m').
    abstract (
        intros;
        split; [ | split ];
        [ apply small_redc with (ri:=r') | apply redc_bound_N with (ri:=r') | rewrite !m_enc_correct_montgomery; apply redc_mod_N ];
        t_fin
      ).
  Defined.

  Import Crypto.Spec.ModularArithmetic.

  Definition montgomery_to_F_gen (v : Z) : F m
    := (F.of_Z m v * F.of_Z m (r'^Z.of_nat sz)%Z)%F.

  Local Definition mul_ext_gen
    : { f:Z^sz -> Z^sz -> Z^sz
      | let eval := MontgomeryAPI.eval (Z.pos r) in
        (forall (A : Z^sz) (_ : small (Z.pos r) A)
                (B : Z^sz) (_ : small (Z.pos r) B),
            montgomery_to_F_gen (eval (f A B))
            = (montgomery_to_F_gen (eval A) * montgomery_to_F_gen (eval B))%F)
        /\ (forall (A : Z^sz) (_ : small (Z.pos r) A)
                   (B : Z^sz) (_ : small (Z.pos r) B),
               (eval B < eval m_enc -> 0 <= eval (f A B) < eval m_enc)%Z) }.
  Proof.
    exists (proj1_sig mul'_gen).
    abstract (
        split; intros A Asm B Bsm;
        pose proof (proj2_sig mul'_gen A B Asm Bsm) as H;
        cbv zeta in *;
        try solve [ destruct_head'_and; assumption ];
        rewrite ModularArithmeticTheorems.F.eq_of_Z_iff in H;
        unfold montgomery_to_F_gen;
        destruct H as [H1 [H2 H3]];
        rewrite H3;
        rewrite <- !ModularArithmeticTheorems.F.of_Z_mul;
        f_equal; nia
      ).
  Defined.

  Local Definition add_ext_gen
    : { f:Z^sz -> Z^sz -> Z^sz
      | let eval := MontgomeryAPI.eval (Z.pos r) in
        ((forall (A : Z^sz) (_ : small (Z.pos r) A)
                 (B : Z^sz) (_ : small (Z.pos r) B),
             (eval A < eval m_enc
              -> eval B < eval m_enc
              -> montgomery_to_F_gen (eval (f A B))
                 = (montgomery_to_F_gen (eval A) + montgomery_to_F_gen (eval B))%F))
         /\ (forall (A : Z^sz) (_ : small (Z.pos r) A)
                    (B : Z^sz) (_ : small (Z.pos r) B),
                (eval A < eval m_enc
                 -> eval B < eval m_enc
                 -> 0 <= eval (f A B) < eval m_enc)))%Z }.
  Proof.
    generalize m_big.
    exists (fun A B => add (r:=r)(R_numlimbs:=sz) m_enc A B).
    abstract (
        split; intros;
        unfold montgomery_to_F_gen; rewrite <- ?ModularArithmeticTheorems.F.of_Z_mul, <- ?ModularArithmeticTheorems.F.of_Z_add;
        rewrite <- ?Z.mul_add_distr_r;
        [ rewrite <- ModularArithmeticTheorems.F.eq_of_Z_iff, m_enc_correct_montgomery; push_Zmod; rewrite eval_add_mod_N; pull_Zmod
        | apply add_bound ];
        t_fin
      ).
  Defined.

  Local Definition sub_ext_gen
    : { f:Z^sz -> Z^sz -> Z^sz
      | let eval := MontgomeryAPI.eval (Z.pos r) in
        ((forall (A : Z^sz) (_ : small (Z.pos r) A)
                 (B : Z^sz) (_ : small (Z.pos r) B),
             (eval A < eval m_enc
              -> eval B < eval m_enc
              -> montgomery_to_F_gen (eval (f A B))
                 = (montgomery_to_F_gen (eval A) - montgomery_to_F_gen (eval B))%F))
         /\ (forall (A : Z^sz) (_ : small (Z.pos r) A)
                    (B : Z^sz) (_ : small (Z.pos r) B),
                (eval A < eval m_enc
                 -> eval B < eval m_enc
                 -> 0 <= eval (f A B) < eval m_enc)))%Z }.
  Proof.
    exists (fun A B => sub (r:=r) (R_numlimbs:=sz) m_enc A B).
    abstract (
        split; intros;
        unfold montgomery_to_F_gen; rewrite <- ?ModularArithmeticTheorems.F.of_Z_mul, <- ?ModularArithmeticTheorems.F.of_Z_sub;
        rewrite <- ?Z.mul_sub_distr_r;
        [ rewrite <- ModularArithmeticTheorems.F.eq_of_Z_iff, m_enc_correct_montgomery; push_Zmod; rewrite eval_sub_mod_N; pull_Zmod
        | apply sub_bound ];
        t_fin
      ).
  Defined.

  Local Definition opp_ext_gen
    : { f:Z^sz -> Z^sz
      | let eval := MontgomeryAPI.eval (Z.pos r) in
        ((forall (A : Z^sz) (_ : small (Z.pos r) A),
             (eval A < eval m_enc
              -> montgomery_to_F_gen (eval (f A))
                 = (F.opp (montgomery_to_F_gen (eval A)))%F))
         /\ (forall (A : Z^sz) (_ : small (Z.pos r) A),
                (eval A < eval m_enc
                 -> 0 <= eval (f A) < eval m_enc)))%Z }.
  Proof.
    exists (fun A => opp (r:=r) (R_numlimbs:=sz) m_enc A).
    abstract (
        split; intros;
        unfold montgomery_to_F_gen; rewrite <- ?ModularArithmeticTheorems.F.of_Z_mul, <- ?F_of_Z_opp;
        rewrite <- ?Z.mul_opp_l;
        [ rewrite <- ModularArithmeticTheorems.F.eq_of_Z_iff, m_enc_correct_montgomery; push_Zmod; rewrite eval_opp_mod_N; pull_Zmod
        | apply opp_bound ];
        t_fin
      ).
  Defined.

  Local Definition carry_ext_gen
    : { f:Z^sz -> Z^sz
      | let eval := MontgomeryAPI.eval (Z.pos r) in
        ((forall (A : Z^sz) (_ : small (Z.pos r) A),
             (eval A < eval m_enc
              -> montgomery_to_F_gen (eval (f A))
                 = montgomery_to_F_gen (eval A))))
         /\ (forall (A : Z^sz) (_ : small (Z.pos r) A),
                (eval A < eval m_enc
                 -> 0 <= eval (f A) < eval m_enc))%Z }.
  Proof.
    exists (fun A => A).
    abstract (
        split; eauto; split; auto;
        apply MontgomeryAPI.eval_small; auto; lia
      ).
  Defined.

  Local Definition nonzero_ext_gen
    : { f:Z^sz -> Z
      | let eval := MontgomeryAPI.eval (Z.pos r) in
        forall (A : Z^sz) (_ : small (Z.pos r) A),
          (eval A < eval m_enc
           -> f A = 0 <-> (montgomery_to_F_gen (eval A) = F.of_Z m 0))%Z }.
  Proof.
    generalize m_big;
    exists (fun A => nonzero (R_numlimbs:=sz) A).
    abstract (
        intros eval A H **; rewrite (@eval_nonzero r) by (eassumption || reflexivity);
        subst eval;
        unfold montgomery_to_F_gen, uweight in *; rewrite <- ?ModularArithmeticTheorems.F.of_Z_mul;
        rewrite <- ModularArithmeticTheorems.F.eq_of_Z_iff, m_enc_correct_montgomery;
        let H := fresh in
        split; intro H;
        [ rewrite H; autorewrite with zsimplify_const; reflexivity
        | cut ((MontgomeryAPI.eval (Z.pos r) A * (r' ^ Z.of_nat sz * Z.pos r ^ Z.of_nat sz)) mod MontgomeryAPI.eval (n:=sz) (Z.pos r) m_enc = 0)%Z;
          [ rewrite Z.mul_mod, r'_pow_correct; autorewrite with zsimplify_const; pull_Zmod; [ | t_fin ];
            rewrite Z.mod_small; [ trivial | split; try assumption; apply MontgomeryAPI.eval_small; try assumption; lia ]
          | rewrite Z.mul_assoc, Z.mul_mod, H by t_fin; autorewrite with zsimplify_const; reflexivity ] ]
      ).
  Defined.
End with_args.

Local Definition for_assumptions
  := (mul_ext_gen, add_ext_gen, sub_ext_gen, opp_ext_gen, nonzero_ext_gen).

Print Assumptions for_assumptions.

Ltac pose_m' modinv_fuel m r m' :=
  pose_modinv modinv_fuel (-Z.pos m) (Z.pos r) m'.
Ltac pose_r' modinv_fuel m r r' :=
  pose_modinv modinv_fuel (Z.pos r) (Z.pos m) r'.

Ltac pose_m'_correct m m' r m'_correct :=
  pose_correct_if_Z
    m'
    ltac:(fun _ => constr:((Z.pos m * m') mod (Z.pos r) = (-1) mod Z.pos r))
           m'_correct.
Ltac pose_r'_correct m r r' r'_correct :=
  pose_correct_if_Z
    r'
    ltac:(fun _ => constr:((Z.pos r * r') mod (Z.pos m) = 1))
           r'_correct.

Ltac pose_m_enc_correct_montgomery m sz r m_enc m_enc_correct_montgomery :=
  cache_proof_with_type_by
    (Z.pos m = MontgomeryAPI.eval (n:=sz) (Z.pos r) m_enc)
    ltac:(vm_compute; reflexivity)
           m_enc_correct_montgomery.

Ltac pose_r'_pow_correct r' sz r m_enc r'_pow_correct :=
  cache_proof_with_type_by
    ((r' ^ Z.of_nat sz * Z.pos r ^ Z.of_nat sz) mod MontgomeryAPI.eval (n:=sz) (Z.pos r) m_enc = 1)
    ltac:(vm_compute; reflexivity)
           r'_pow_correct.

Ltac pose_montgomery_to_F sz m r' montgomery_to_F :=
  let v := (eval cbv [montgomery_to_F_gen] in (montgomery_to_F_gen sz m r')) in
  cache_term v montgomery_to_F.

Ltac pose_r_big r r_big :=
  cache_proof_with_type_by
    (Z.pos r > 1)
    ltac:(vm_compute; reflexivity)
           r_big.

Ltac pose_m_big m m_big :=
  cache_proof_with_type_by
    (1 < Z.pos m)
    ltac:(vm_compute; reflexivity)
           m_big.

Ltac pose_m_enc_small sz r m_enc m_enc_small :=
  cache_proof_with_type_by
    (small (n:=sz) (Z.pos r) m_enc)
    ltac:(pose (small_Decidable (n:=sz) (bound:=Z.pos r)); vm_decide_no_check)
           m_enc_small.

Ltac pose_map_m_enc sz r m_enc map_m_enc :=
  cache_proof_with_type_by
    (Tuple.map (n:=sz) (Z.land (Z.pos r - 1)) m_enc = m_enc)
    ltac:(pose (@dec_eq_prod); pose dec_eq_Z; vm_decide_no_check)
           map_m_enc.

Ltac internal_pose_sig_by_eq ty sigl tac_eq id :=
  cache_term_with_type_by
    ty
    ltac:(eapply (@sig_by_eq _ _ sigl _); tac_eq ())
           id.

Import Crypto.Spec.ModularArithmetic.

Local Ltac reduce_eq _ :=
  cbv -[Definitions.Z.add_with_get_carry Definitions.Z.add_with_carry Definitions.Z.sub_with_get_borrow Definitions.Z.sub_with_borrow Definitions.Z.mul_split_at_bitwidth Definitions.Z.zselect runtime_add runtime_mul runtime_and runtime_opp runtime_lor Let_In].

Ltac pose_mul_ext r sz m m_enc r' r'_correct m' m'_correct m_enc_correct_montgomery r_big m_big m_enc_small montgomery_to_F mul_ext :=
  internal_pose_sig_by_eq
    { f:Z^sz -> Z^sz -> Z^sz
    | let eval := MontgomeryAPI.eval (Z.pos r) in
      (forall (A : Z^sz) (_ : small (Z.pos r) A)
              (B : Z^sz) (_ : small (Z.pos r) B),
          montgomery_to_F (eval (f A B))
          = (montgomery_to_F (eval A) * montgomery_to_F (eval B))%F)
      /\ (forall (A : Z^sz) (_ : small (Z.pos r) A)
                 (B : Z^sz) (_ : small (Z.pos r) B),
             (eval B < eval m_enc -> 0 <= eval (f A B) < eval m_enc)%Z) }
    (@mul_ext_gen r sz m m_enc r' r'_correct m' m'_correct m_enc_correct_montgomery r_big m_big m_enc_small)
    ltac:(fun _ => reduce_eq (); reflexivity)
           mul_ext.

Ltac pose_add_ext r sz m m_enc r' m_enc_correct_montgomery r_big m_big m_enc_small montgomery_to_F add_ext :=
  internal_pose_sig_by_eq
    { f:Z^sz -> Z^sz -> Z^sz
    | let eval := MontgomeryAPI.eval (Z.pos r) in
      ((forall (A : Z^sz) (_ : small (Z.pos r) A)
               (B : Z^sz) (_ : small (Z.pos r) B),
           (eval A < eval m_enc
            -> eval B < eval m_enc
            -> montgomery_to_F (eval (f A B))
               = (montgomery_to_F (eval A) + montgomery_to_F (eval B))%F))
       /\ (forall (A : Z^sz) (_ : small (Z.pos r) A)
                  (B : Z^sz) (_ : small (Z.pos r) B),
              (eval A < eval m_enc
               -> eval B < eval m_enc
               -> 0 <= eval (f A B) < eval m_enc)))%Z }
    (@add_ext_gen r sz m m_enc r' m_enc_correct_montgomery r_big m_big m_enc_small)
    ltac:(fun _ => reduce_eq (); reflexivity)
           add_ext.

Ltac pose_sub_ext r sz m m_enc r' m_enc_correct_montgomery r_big m_enc_small map_m_enc montgomery_to_F sub_ext :=
  internal_pose_sig_by_eq
    { f:Z^sz -> Z^sz -> Z^sz
    | let eval := MontgomeryAPI.eval (Z.pos r) in
      ((forall (A : Z^sz) (_ : small (Z.pos r) A)
               (B : Z^sz) (_ : small (Z.pos r) B),
           (eval A < eval m_enc
            -> eval B < eval m_enc
            -> montgomery_to_F (eval (f A B))
               = (montgomery_to_F (eval A) - montgomery_to_F (eval B))%F))
       /\ (forall (A : Z^sz) (_ : small (Z.pos r) A)
                  (B : Z^sz) (_ : small (Z.pos r) B),
              (eval A < eval m_enc
               -> eval B < eval m_enc
               -> 0 <= eval (f A B) < eval m_enc)))%Z }
    (@sub_ext_gen r sz m m_enc r' m_enc_correct_montgomery r_big m_enc_small map_m_enc)
    ltac:(fun _ => reduce_eq (); reflexivity)
           sub_ext.

Ltac pose_opp_ext r sz m m_enc r' m_enc_correct_montgomery r_big m_enc_small map_m_enc montgomery_to_F opp_ext :=
  internal_pose_sig_by_eq
    { f:Z^sz -> Z^sz
    | let eval := MontgomeryAPI.eval (Z.pos r) in
      ((forall (A : Z^sz) (_ : small (Z.pos r) A),
           (eval A < eval m_enc
            -> montgomery_to_F (eval (f A))
               = (F.opp (montgomery_to_F (eval A)))%F))
       /\ (forall (A : Z^sz) (_ : small (Z.pos r) A),
              (eval A < eval m_enc
               -> 0 <= eval (f A) < eval m_enc)))%Z }
    (@opp_ext_gen r sz m m_enc r' m_enc_correct_montgomery r_big m_enc_small map_m_enc)
    ltac:(fun _ => reduce_eq (); reflexivity)
           opp_ext.

Ltac pose_carry_ext r sz m m_enc r' r_big montgomery_to_F carry_ext :=
  internal_pose_sig_by_eq
    { f:Z^sz -> Z^sz
    | let eval := MontgomeryAPI.eval (Z.pos r) in
      ((forall (A : Z^sz) (_ : small (Z.pos r) A),
           (eval A < eval m_enc
            -> montgomery_to_F (eval (f A))
               = (montgomery_to_F (eval A))))
       /\ (forall (A : Z^sz) (_ : small (Z.pos r) A),
              (eval A < eval m_enc
               -> 0 <= eval (f A) < eval m_enc)))%Z }
    (@carry_ext_gen r sz m m_enc r' r_big)
    ltac:(fun _ => reduce_eq (); reflexivity)
           carry_ext.

Ltac pose_nonzero_ext r sz m m_enc r' m_enc_correct_montgomery r'_pow_correct r_big m_big montgomery_to_F nonzero_ext :=
  internal_pose_sig_by_eq
    { f:Z^sz -> Z
    | let eval := MontgomeryAPI.eval (Z.pos r) in
      forall (A : Z^sz) (_ : small (Z.pos r) A),
        (eval A < eval m_enc
         -> f A = 0 <-> (montgomery_to_F (eval A) = F.of_Z m 0))%Z }
    (@nonzero_ext_gen r sz m m_enc r' m_enc_correct_montgomery r'_pow_correct r_big m_big)
    ltac:(fun _ => reduce_eq (); reflexivity)
           nonzero_ext.

Ltac pose_mul_sig r sz montgomery_to_F mul_ext mul_sig :=
  cache_term_with_type_by
    { f:Z^sz -> Z^sz -> Z^sz
    | let eval := MontgomeryAPI.eval (Z.pos r) in
      forall (A : Z^sz) (_ : small (Z.pos r) A)
             (B : Z^sz) (_ : small (Z.pos r) B),
        montgomery_to_F (eval (f A B))
        = (montgomery_to_F (eval A) * montgomery_to_F (eval B))%F }
    ltac:(idtac;
          let v := (eval cbv [proj1_sig mul_ext_gen mul_ext sig_by_eq] in (proj1_sig mul_ext)) in
          (exists v);
          abstract apply (proj2_sig mul_ext))
           mul_sig.

Ltac pose_mul_bounded r sz m_enc montgomery_to_F mul_ext mul_sig mul_bounded :=
  cache_proof_with_type_by
    (let eval := MontgomeryAPI.eval (Z.pos r) in
     forall (A : Z^sz) (_ : small (Z.pos r) A)
            (B : Z^sz) (_ : small (Z.pos r) B),
       (eval B < eval m_enc
        -> 0 <= eval (proj1_sig mul_sig A B) < eval m_enc)%Z)
    ltac:(apply (proj2_sig mul_ext))
           mul_bounded.

Ltac pose_add_sig r sz m_enc montgomery_to_F add_ext add_sig :=
  cache_term_with_type_by
    { f:Z^sz -> Z^sz -> Z^sz
    | let eval := MontgomeryAPI.eval (Z.pos r) in
      forall (A : Z^sz) (_ : small (Z.pos r) A)
             (B : Z^sz) (_ : small (Z.pos r) B),
        (eval A < eval m_enc
         -> eval B < eval m_enc
         -> montgomery_to_F (eval (f A B))
            = (montgomery_to_F (eval A) + montgomery_to_F (eval B))%F)%Z }
    ltac:(idtac;
          let v := (eval cbv [proj1_sig add_ext_gen add_ext sig_by_eq] in (proj1_sig add_ext)) in
          (exists v);
          abstract apply (proj2_sig add_ext))
           add_sig.

Ltac pose_add_bounded r sz m_enc montgomery_to_F add_ext add_sig add_bounded :=
  cache_proof_with_type_by
    (let eval := MontgomeryAPI.eval (Z.pos r) in
     (forall (A : Z^sz) (_ : small (Z.pos r) A)
             (B : Z^sz) (_ : small (Z.pos r) B),
         (eval A < eval m_enc
          -> eval B < eval m_enc
          -> 0 <= eval (proj1_sig add_sig A B) < eval m_enc))%Z)
    ltac:(apply (proj2_sig add_ext))
           add_bounded.

Ltac pose_sub_sig r sz m_enc montgomery_to_F sub_ext sub_sig :=
  cache_term_with_type_by
    { f:Z^sz -> Z^sz -> Z^sz
    | let eval := MontgomeryAPI.eval (Z.pos r) in
      forall (A : Z^sz) (_ : small (Z.pos r) A)
             (B : Z^sz) (_ : small (Z.pos r) B),
        (eval A < eval m_enc
         -> eval B < eval m_enc
         -> montgomery_to_F (eval (f A B))
            = (montgomery_to_F (eval A) - montgomery_to_F (eval B))%F)%Z }
    ltac:(idtac;
          let v := (eval cbv [proj1_sig sub_ext_gen sub_ext sig_by_eq] in (proj1_sig sub_ext)) in
          (exists v);
          abstract apply (proj2_sig sub_ext))
           sub_sig.

Ltac pose_sub_bounded r sz m_enc montgomery_to_F sub_ext sub_sig sub_bounded :=
  cache_proof_with_type_by
    (let eval := MontgomeryAPI.eval (Z.pos r) in
     (forall (A : Z^sz) (_ : small (Z.pos r) A)
             (B : Z^sz) (_ : small (Z.pos r) B),
         (eval A < eval m_enc
          -> eval B < eval m_enc
          -> 0 <= eval (proj1_sig sub_sig A B) < eval m_enc))%Z)
    ltac:(apply (proj2_sig sub_ext))
           sub_bounded.

Ltac pose_opp_sig r sz m_enc montgomery_to_F opp_ext opp_sig :=
  cache_term_with_type_by
    { f:Z^sz -> Z^sz
    | let eval := MontgomeryAPI.eval (Z.pos r) in
      forall (A : Z^sz) (_ : small (Z.pos r) A),
        (eval A < eval m_enc
         -> montgomery_to_F (eval (f A))
            = (F.opp (montgomery_to_F (eval A)))%F)%Z }
    ltac:(idtac;
          let v := (eval cbv [proj1_sig opp_ext_gen opp_ext sig_by_eq] in (proj1_sig opp_ext)) in
          (exists v);
          abstract apply (proj2_sig opp_ext))
           opp_sig.

Ltac pose_opp_bounded r sz m_enc montgomery_to_F opp_ext opp_sig opp_bounded :=
  cache_proof_with_type_by
    (let eval := MontgomeryAPI.eval (Z.pos r) in
     (forall (A : Z^sz) (_ : small (Z.pos r) A),
         (eval A < eval m_enc
          -> 0 <= eval (proj1_sig opp_sig A) < eval m_enc))%Z)
    ltac:(apply (proj2_sig opp_ext))
           opp_bounded.

Ltac pose_carry_sig r sz m_enc montgomery_to_F carry_ext carry_sig :=
  cache_term_with_type_by
    { f:Z^sz -> Z^sz
    | let eval := MontgomeryAPI.eval (Z.pos r) in
      forall (A : Z^sz) (_ : small (Z.pos r) A),
        (eval A < eval m_enc
         -> montgomery_to_F (eval (f A))
            = (montgomery_to_F (eval A)))%Z }
    ltac:(idtac;
          let v := (eval cbv [proj1_sig carry_ext_gen carry_ext sig_by_eq] in (proj1_sig carry_ext)) in
          (exists v);
          abstract apply (proj2_sig carry_ext))
           carry_sig.

Ltac pose_carry_bounded r sz m_enc montgomery_to_F carry_ext carry_sig carry_bounded :=
  cache_proof_with_type_by
    (let eval := MontgomeryAPI.eval (Z.pos r) in
     (forall (A : Z^sz) (_ : small (Z.pos r) A),
         (eval A < eval m_enc
          -> 0 <= eval (proj1_sig carry_sig A) < eval m_enc))%Z)
    ltac:(apply (proj2_sig carry_ext))
           carry_bounded.

Ltac pose_nonzero_sig r sz m m_enc montgomery_to_F nonzero_ext nonzero_sig :=
  cache_term_with_type_by
    { f:Z^sz -> Z
    | let eval := MontgomeryAPI.eval (Z.pos r) in
      forall (A : Z^sz) (_ : small (Z.pos r) A),
        (eval A < eval m_enc
         -> f A = 0 <-> (montgomery_to_F (eval A) = F.of_Z m 0))%Z }
    ltac:(idtac;
          let v := (eval cbv [proj1_sig nonzero_ext_gen nonzero_ext sig_by_eq] in (proj1_sig nonzero_ext)) in
          (exists v);
          abstract apply (proj2_sig nonzero_ext))
           nonzero_sig.

Ltac pose_ring ring :=

  cache_term
    I
    ring.

Ltac pose_freeze_sig freeze_sig :=
  cache_term tt freeze_sig.
Ltac pose_Mxzladderstep_sig Mxzladderstep_sig :=
  cache_term tt Mxzladderstep_sig.

End Montgomery.

End Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_Montgomery_WRAPPED.
Module Export Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_Montgomery.
Module Export Crypto.
Module Export Specific.
Module Export Framework.
Module Export ArithmeticSynthesis.
Module Montgomery.
Include Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_Montgomery_WRAPPED.Montgomery.
End Montgomery.

End ArithmeticSynthesis.

End Framework.

End Specific.

End Crypto.

End Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_Montgomery.
Module Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_MontgomeryPackage_WRAPPED.
Module MontgomeryPackage.

Import Crypto.Specific.Framework.CurveParametersPackage.
Import Crypto.Specific.Framework.ArithmeticSynthesis.BasePackage.
Import Crypto.Specific.Framework.ArithmeticSynthesis.DefaultsPackage.
Import Crypto.Specific.Framework.ArithmeticSynthesis.FreezePackage.
Import Crypto.Specific.Framework.ArithmeticSynthesis.LadderstepPackage.
Export Crypto.Specific.Framework.ArithmeticSynthesis.Montgomery.
Import Crypto.Specific.Framework.Packages.
Import Crypto.Util.TagList.

Module TAG.
  Inductive tags := m' | r' | m'_correct | r'_correct | m_enc_correct_montgomery | r'_pow_correct | montgomery_to_F | r_big | m_big | m_enc_small | map_m_enc | mul_ext | add_ext | sub_ext | opp_ext | carry_ext | nonzero_ext | mul_bounded | add_bounded | sub_bounded | opp_bounded | carry_bounded | nonzero_sig.
End TAG.

Ltac add_m' pkg :=
  if_montgomery
    pkg
    ltac:(fun _ => let modinv_fuel := Tag.get pkg TAG.modinv_fuel in
                   let m := Tag.get pkg TAG.m in
                   let r := Tag.get pkg TAG.r in
                   let m' := fresh "m'" in
                   let m' := pose_m' modinv_fuel m r m' in
                   Tag.update pkg TAG.m' m')
    ltac:(fun _ => pkg)
    ().
Ltac add_r' pkg :=
  if_montgomery
    pkg
    ltac:(fun _ => let modinv_fuel := Tag.get pkg TAG.modinv_fuel in
                   let m := Tag.get pkg TAG.m in
                   let r := Tag.get pkg TAG.r in
                   let r' := fresh "r'" in
                   let r' := pose_r' modinv_fuel m r r' in
                   Tag.update pkg TAG.r' r')
    ltac:(fun _ => pkg)
    ().
Ltac add_m'_correct pkg :=
  if_montgomery
    pkg
    ltac:(fun _ => let m := Tag.get pkg TAG.m in
                   let m' := Tag.get pkg TAG.m' in
                   let r := Tag.get pkg TAG.r in
                   let m'_correct := fresh "m'_correct" in
                   let m'_correct := pose_m'_correct m m' r m'_correct in
                   Tag.update pkg TAG.m'_correct m'_correct)
    ltac:(fun _ => pkg)
    ().
Ltac add_r'_correct pkg :=
  if_montgomery
    pkg
    ltac:(fun _ => let m := Tag.get pkg TAG.m in
                   let r := Tag.get pkg TAG.r in
                   let r' := Tag.get pkg TAG.r' in
                   let r'_correct := fresh "r'_correct" in
                   let r'_correct := pose_r'_correct m r r' r'_correct in
                   Tag.update pkg TAG.r'_correct r'_correct)
    ltac:(fun _ => pkg)
    ().
Ltac add_m_enc_correct_montgomery pkg :=
  if_montgomery
    pkg
    ltac:(fun _ => let m := Tag.get pkg TAG.m in
                   let sz := Tag.get pkg TAG.sz in
                   let r := Tag.get pkg TAG.r in
                   let m_enc := Tag.get pkg TAG.m_enc in
                   let m_enc_correct_montgomery := fresh "m_enc_correct_montgomery" in
                   let m_enc_correct_montgomery := pose_m_enc_correct_montgomery m sz r m_enc m_enc_correct_montgomery in
                   Tag.update pkg TAG.m_enc_correct_montgomery m_enc_correct_montgomery)
    ltac:(fun _ => pkg)
    ().
Ltac add_r'_pow_correct pkg :=
  if_montgomery
    pkg
    ltac:(fun _ => let r' := Tag.get pkg TAG.r' in
                   let sz := Tag.get pkg TAG.sz in
                   let r := Tag.get pkg TAG.r in
                   let m_enc := Tag.get pkg TAG.m_enc in
                   let r'_pow_correct := fresh "r'_pow_correct" in
                   let r'_pow_correct := pose_r'_pow_correct r' sz r m_enc r'_pow_correct in
                   Tag.update pkg TAG.r'_pow_correct r'_pow_correct)
    ltac:(fun _ => pkg)
    ().
Ltac add_montgomery_to_F pkg :=
  if_montgomery
    pkg
    ltac:(fun _ => let sz := Tag.get pkg TAG.sz in
                   let m := Tag.get pkg TAG.m in
                   let r' := Tag.get pkg TAG.r' in
                   let montgomery_to_F := fresh "montgomery_to_F" in
                   let montgomery_to_F := pose_montgomery_to_F sz m r' montgomery_to_F in
                   Tag.update pkg TAG.montgomery_to_F montgomery_to_F)
    ltac:(fun _ => pkg)
    ().
Ltac add_r_big pkg :=
  if_montgomery
    pkg
    ltac:(fun _ => let r := Tag.get pkg TAG.r in
                   let r_big := fresh "r_big" in
                   let r_big := pose_r_big r r_big in
                   Tag.update pkg TAG.r_big r_big)
    ltac:(fun _ => pkg)
    ().
Ltac add_m_big pkg :=
  if_montgomery
    pkg
    ltac:(fun _ => let m := Tag.get pkg TAG.m in
                   let m_big := fresh "m_big" in
                   let m_big := pose_m_big m m_big in
                   Tag.update pkg TAG.m_big m_big)
    ltac:(fun _ => pkg)
    ().
Ltac add_m_enc_small pkg :=
  if_montgomery
    pkg
    ltac:(fun _ => let sz := Tag.get pkg TAG.sz in
                   let r := Tag.get pkg TAG.r in
                   let m_enc := Tag.get pkg TAG.m_enc in
                   let m_enc_small := fresh "m_enc_small" in
                   let m_enc_small := pose_m_enc_small sz r m_enc m_enc_small in
                   Tag.update pkg TAG.m_enc_small m_enc_small)
    ltac:(fun _ => pkg)
    ().
Ltac add_map_m_enc pkg :=
  if_montgomery
    pkg
    ltac:(fun _ => let sz := Tag.get pkg TAG.sz in
                   let r := Tag.get pkg TAG.r in
                   let m_enc := Tag.get pkg TAG.m_enc in
                   let map_m_enc := fresh "map_m_enc" in
                   let map_m_enc := pose_map_m_enc sz r m_enc map_m_enc in
                   Tag.update pkg TAG.map_m_enc map_m_enc)
    ltac:(fun _ => pkg)
    ().
Ltac add_mul_ext pkg :=
  if_montgomery
    pkg
    ltac:(fun _ => let r := Tag.get pkg TAG.r in
                   let sz := Tag.get pkg TAG.sz in
                   let m := Tag.get pkg TAG.m in
                   let m_enc := Tag.get pkg TAG.m_enc in
                   let r' := Tag.get pkg TAG.r' in
                   let r'_correct := Tag.get pkg TAG.r'_correct in
                   let m' := Tag.get pkg TAG.m' in
                   let m'_correct := Tag.get pkg TAG.m'_correct in
                   let m_enc_correct_montgomery := Tag.get pkg TAG.m_enc_correct_montgomery in
                   let r_big := Tag.get pkg TAG.r_big in
                   let m_big := Tag.get pkg TAG.m_big in
                   let m_enc_small := Tag.get pkg TAG.m_enc_small in
                   let montgomery_to_F := Tag.get pkg TAG.montgomery_to_F in
                   let mul_ext := fresh "mul_ext" in
                   let mul_ext := pose_mul_ext r sz m m_enc r' r'_correct m' m'_correct m_enc_correct_montgomery r_big m_big m_enc_small montgomery_to_F mul_ext in
                   Tag.update pkg TAG.mul_ext mul_ext)
    ltac:(fun _ => pkg)
    ().
Ltac add_add_ext pkg :=
  if_montgomery
    pkg
    ltac:(fun _ => let r := Tag.get pkg TAG.r in
                   let sz := Tag.get pkg TAG.sz in
                   let m := Tag.get pkg TAG.m in
                   let m_enc := Tag.get pkg TAG.m_enc in
                   let r' := Tag.get pkg TAG.r' in
                   let m_enc_correct_montgomery := Tag.get pkg TAG.m_enc_correct_montgomery in
                   let r_big := Tag.get pkg TAG.r_big in
                   let m_big := Tag.get pkg TAG.m_big in
                   let m_enc_small := Tag.get pkg TAG.m_enc_small in
                   let montgomery_to_F := Tag.get pkg TAG.montgomery_to_F in
                   let add_ext := fresh "add_ext" in
                   let add_ext := pose_add_ext r sz m m_enc r' m_enc_correct_montgomery r_big m_big m_enc_small montgomery_to_F add_ext in
                   Tag.update pkg TAG.add_ext add_ext)
    ltac:(fun _ => pkg)
    ().
Ltac add_sub_ext pkg :=
  if_montgomery
    pkg
    ltac:(fun _ => let r := Tag.get pkg TAG.r in
                   let sz := Tag.get pkg TAG.sz in
                   let m := Tag.get pkg TAG.m in
                   let m_enc := Tag.get pkg TAG.m_enc in
                   let r' := Tag.get pkg TAG.r' in
                   let m_enc_correct_montgomery := Tag.get pkg TAG.m_enc_correct_montgomery in
                   let r_big := Tag.get pkg TAG.r_big in
                   let m_enc_small := Tag.get pkg TAG.m_enc_small in
                   let map_m_enc := Tag.get pkg TAG.map_m_enc in
                   let montgomery_to_F := Tag.get pkg TAG.montgomery_to_F in
                   let sub_ext := fresh "sub_ext" in
                   let sub_ext := pose_sub_ext r sz m m_enc r' m_enc_correct_montgomery r_big m_enc_small map_m_enc montgomery_to_F sub_ext in
                   Tag.update pkg TAG.sub_ext sub_ext)
    ltac:(fun _ => pkg)
    ().
Ltac add_opp_ext pkg :=
  if_montgomery
    pkg
    ltac:(fun _ => let r := Tag.get pkg TAG.r in
                   let sz := Tag.get pkg TAG.sz in
                   let m := Tag.get pkg TAG.m in
                   let m_enc := Tag.get pkg TAG.m_enc in
                   let r' := Tag.get pkg TAG.r' in
                   let m_enc_correct_montgomery := Tag.get pkg TAG.m_enc_correct_montgomery in
                   let r_big := Tag.get pkg TAG.r_big in
                   let m_enc_small := Tag.get pkg TAG.m_enc_small in
                   let map_m_enc := Tag.get pkg TAG.map_m_enc in
                   let montgomery_to_F := Tag.get pkg TAG.montgomery_to_F in
                   let opp_ext := fresh "opp_ext" in
                   let opp_ext := pose_opp_ext r sz m m_enc r' m_enc_correct_montgomery r_big m_enc_small map_m_enc montgomery_to_F opp_ext in
                   Tag.update pkg TAG.opp_ext opp_ext)
    ltac:(fun _ => pkg)
    ().
Ltac add_carry_ext pkg :=
  if_montgomery
    pkg
    ltac:(fun _ => let r := Tag.get pkg TAG.r in
                   let sz := Tag.get pkg TAG.sz in
                   let m := Tag.get pkg TAG.m in
                   let m_enc := Tag.get pkg TAG.m_enc in
                   let r' := Tag.get pkg TAG.r' in
                   let r_big := Tag.get pkg TAG.r_big in
                   let montgomery_to_F := Tag.get pkg TAG.montgomery_to_F in
                   let carry_ext := fresh "carry_ext" in
                   let carry_ext := pose_carry_ext r sz m m_enc r' r_big montgomery_to_F carry_ext in
                   Tag.update pkg TAG.carry_ext carry_ext)
    ltac:(fun _ => pkg)
    ().
Ltac add_nonzero_ext pkg :=
  if_montgomery
    pkg
    ltac:(fun _ => let r := Tag.get pkg TAG.r in
                   let sz := Tag.get pkg TAG.sz in
                   let m := Tag.get pkg TAG.m in
                   let m_enc := Tag.get pkg TAG.m_enc in
                   let r' := Tag.get pkg TAG.r' in
                   let m_enc_correct_montgomery := Tag.get pkg TAG.m_enc_correct_montgomery in
                   let r'_pow_correct := Tag.get pkg TAG.r'_pow_correct in
                   let r_big := Tag.get pkg TAG.r_big in
                   let m_big := Tag.get pkg TAG.m_big in
                   let montgomery_to_F := Tag.get pkg TAG.montgomery_to_F in
                   let nonzero_ext := fresh "nonzero_ext" in
                   let nonzero_ext := pose_nonzero_ext r sz m m_enc r' m_enc_correct_montgomery r'_pow_correct r_big m_big montgomery_to_F nonzero_ext in
                   Tag.update pkg TAG.nonzero_ext nonzero_ext)
    ltac:(fun _ => pkg)
    ().
Ltac add_mul_sig pkg :=
  if_montgomery
    pkg
    ltac:(fun _ => let r := Tag.get pkg TAG.r in
                   let sz := Tag.get pkg TAG.sz in
                   let montgomery_to_F := Tag.get pkg TAG.montgomery_to_F in
                   let mul_ext := Tag.get pkg TAG.mul_ext in
                   let mul_sig := fresh "mul_sig" in
                   let mul_sig := pose_mul_sig r sz montgomery_to_F mul_ext mul_sig in
                   Tag.update pkg TAG.mul_sig mul_sig)
    ltac:(fun _ => pkg)
    ().
Ltac add_mul_bounded pkg :=
  if_montgomery
    pkg
    ltac:(fun _ => let r := Tag.get pkg TAG.r in
                   let sz := Tag.get pkg TAG.sz in
                   let m_enc := Tag.get pkg TAG.m_enc in
                   let montgomery_to_F := Tag.get pkg TAG.montgomery_to_F in
                   let mul_ext := Tag.get pkg TAG.mul_ext in
                   let mul_sig := Tag.get pkg TAG.mul_sig in
                   let mul_bounded := fresh "mul_bounded" in
                   let mul_bounded := pose_mul_bounded r sz m_enc montgomery_to_F mul_ext mul_sig mul_bounded in
                   Tag.update pkg TAG.mul_bounded mul_bounded)
    ltac:(fun _ => pkg)
    ().
Ltac add_add_sig pkg :=
  if_montgomery
    pkg
    ltac:(fun _ => let r := Tag.get pkg TAG.r in
                   let sz := Tag.get pkg TAG.sz in
                   let m_enc := Tag.get pkg TAG.m_enc in
                   let montgomery_to_F := Tag.get pkg TAG.montgomery_to_F in
                   let add_ext := Tag.get pkg TAG.add_ext in
                   let add_sig := fresh "add_sig" in
                   let add_sig := pose_add_sig r sz m_enc montgomery_to_F add_ext add_sig in
                   Tag.update pkg TAG.add_sig add_sig)
    ltac:(fun _ => pkg)
    ().
Ltac add_add_bounded pkg :=
  if_montgomery
    pkg
    ltac:(fun _ => let r := Tag.get pkg TAG.r in
                   let sz := Tag.get pkg TAG.sz in
                   let m_enc := Tag.get pkg TAG.m_enc in
                   let montgomery_to_F := Tag.get pkg TAG.montgomery_to_F in
                   let add_ext := Tag.get pkg TAG.add_ext in
                   let add_sig := Tag.get pkg TAG.add_sig in
                   let add_bounded := fresh "add_bounded" in
                   let add_bounded := pose_add_bounded r sz m_enc montgomery_to_F add_ext add_sig add_bounded in
                   Tag.update pkg TAG.add_bounded add_bounded)
    ltac:(fun _ => pkg)
    ().
Ltac add_sub_sig pkg :=
  if_montgomery
    pkg
    ltac:(fun _ => let r := Tag.get pkg TAG.r in
                   let sz := Tag.get pkg TAG.sz in
                   let m_enc := Tag.get pkg TAG.m_enc in
                   let montgomery_to_F := Tag.get pkg TAG.montgomery_to_F in
                   let sub_ext := Tag.get pkg TAG.sub_ext in
                   let sub_sig := fresh "sub_sig" in
                   let sub_sig := pose_sub_sig r sz m_enc montgomery_to_F sub_ext sub_sig in
                   Tag.update pkg TAG.sub_sig sub_sig)
    ltac:(fun _ => pkg)
    ().
Ltac add_sub_bounded pkg :=
  if_montgomery
    pkg
    ltac:(fun _ => let r := Tag.get pkg TAG.r in
                   let sz := Tag.get pkg TAG.sz in
                   let m_enc := Tag.get pkg TAG.m_enc in
                   let montgomery_to_F := Tag.get pkg TAG.montgomery_to_F in
                   let sub_ext := Tag.get pkg TAG.sub_ext in
                   let sub_sig := Tag.get pkg TAG.sub_sig in
                   let sub_bounded := fresh "sub_bounded" in
                   let sub_bounded := pose_sub_bounded r sz m_enc montgomery_to_F sub_ext sub_sig sub_bounded in
                   Tag.update pkg TAG.sub_bounded sub_bounded)
    ltac:(fun _ => pkg)
    ().
Ltac add_opp_sig pkg :=
  if_montgomery
    pkg
    ltac:(fun _ => let r := Tag.get pkg TAG.r in
                   let sz := Tag.get pkg TAG.sz in
                   let m_enc := Tag.get pkg TAG.m_enc in
                   let montgomery_to_F := Tag.get pkg TAG.montgomery_to_F in
                   let opp_ext := Tag.get pkg TAG.opp_ext in
                   let opp_sig := fresh "opp_sig" in
                   let opp_sig := pose_opp_sig r sz m_enc montgomery_to_F opp_ext opp_sig in
                   Tag.update pkg TAG.opp_sig opp_sig)
    ltac:(fun _ => pkg)
    ().
Ltac add_opp_bounded pkg :=
  if_montgomery
    pkg
    ltac:(fun _ => let r := Tag.get pkg TAG.r in
                   let sz := Tag.get pkg TAG.sz in
                   let m_enc := Tag.get pkg TAG.m_enc in
                   let montgomery_to_F := Tag.get pkg TAG.montgomery_to_F in
                   let opp_ext := Tag.get pkg TAG.opp_ext in
                   let opp_sig := Tag.get pkg TAG.opp_sig in
                   let opp_bounded := fresh "opp_bounded" in
                   let opp_bounded := pose_opp_bounded r sz m_enc montgomery_to_F opp_ext opp_sig opp_bounded in
                   Tag.update pkg TAG.opp_bounded opp_bounded)
    ltac:(fun _ => pkg)
    ().
Ltac add_carry_sig pkg :=
  if_montgomery
    pkg
    ltac:(fun _ => let r := Tag.get pkg TAG.r in
                   let sz := Tag.get pkg TAG.sz in
                   let m_enc := Tag.get pkg TAG.m_enc in
                   let montgomery_to_F := Tag.get pkg TAG.montgomery_to_F in
                   let carry_ext := Tag.get pkg TAG.carry_ext in
                   let carry_sig := fresh "carry_sig" in
                   let carry_sig := pose_carry_sig r sz m_enc montgomery_to_F carry_ext carry_sig in
                   Tag.update pkg TAG.carry_sig carry_sig)
    ltac:(fun _ => pkg)
    ().
Ltac add_carry_bounded pkg :=
  if_montgomery
    pkg
    ltac:(fun _ => let r := Tag.get pkg TAG.r in
                   let sz := Tag.get pkg TAG.sz in
                   let m_enc := Tag.get pkg TAG.m_enc in
                   let montgomery_to_F := Tag.get pkg TAG.montgomery_to_F in
                   let carry_ext := Tag.get pkg TAG.carry_ext in
                   let carry_sig := Tag.get pkg TAG.carry_sig in
                   let carry_bounded := fresh "carry_bounded" in
                   let carry_bounded := pose_carry_bounded r sz m_enc montgomery_to_F carry_ext carry_sig carry_bounded in
                   Tag.update pkg TAG.carry_bounded carry_bounded)
    ltac:(fun _ => pkg)
    ().
Ltac add_nonzero_sig pkg :=
  if_montgomery
    pkg
    ltac:(fun _ => let r := Tag.get pkg TAG.r in
                   let sz := Tag.get pkg TAG.sz in
                   let m := Tag.get pkg TAG.m in
                   let m_enc := Tag.get pkg TAG.m_enc in
                   let montgomery_to_F := Tag.get pkg TAG.montgomery_to_F in
                   let nonzero_ext := Tag.get pkg TAG.nonzero_ext in
                   let nonzero_sig := fresh "nonzero_sig" in
                   let nonzero_sig := pose_nonzero_sig r sz m m_enc montgomery_to_F nonzero_ext nonzero_sig in
                   Tag.update pkg TAG.nonzero_sig nonzero_sig)
    ltac:(fun _ => pkg)
    ().
Ltac add_ring pkg :=
  if_montgomery
    pkg
    ltac:(fun _ => let ring := fresh "ring" in
                   let ring := pose_ring ring in
                   Tag.update pkg TAG.ring ring)
    ltac:(fun _ => pkg)
    ().
Ltac add_freeze_sig pkg :=
  if_montgomery
    pkg
    ltac:(fun _ => let freeze_sig := fresh "freeze_sig" in
                   let freeze_sig := pose_freeze_sig freeze_sig in
                   Tag.update pkg TAG.freeze_sig freeze_sig)
    ltac:(fun _ => pkg)
    ().
Ltac add_Mxzladderstep_sig pkg :=
  if_montgomery
    pkg
    ltac:(fun _ => let Mxzladderstep_sig := fresh "Mxzladderstep_sig" in
                   let Mxzladderstep_sig := pose_Mxzladderstep_sig Mxzladderstep_sig in
                   Tag.update pkg TAG.Mxzladderstep_sig Mxzladderstep_sig)
    ltac:(fun _ => pkg)
    ().
Ltac add_Montgomery_package pkg :=
  let pkg := add_m' pkg in
  let pkg := add_r' pkg in
  let pkg := add_m'_correct pkg in
  let pkg := add_r'_correct pkg in
  let pkg := add_m_enc_correct_montgomery pkg in
  let pkg := add_r'_pow_correct pkg in
  let pkg := add_montgomery_to_F pkg in
  let pkg := add_r_big pkg in
  let pkg := add_m_big pkg in
  let pkg := add_m_enc_small pkg in
  let pkg := add_map_m_enc pkg in
  let pkg := add_mul_ext pkg in
  let pkg := add_add_ext pkg in
  let pkg := add_sub_ext pkg in
  let pkg := add_opp_ext pkg in
  let pkg := add_carry_ext pkg in
  let pkg := add_nonzero_ext pkg in
  let pkg := add_mul_sig pkg in
  let pkg := add_mul_bounded pkg in
  let pkg := add_add_sig pkg in
  let pkg := add_add_bounded pkg in
  let pkg := add_sub_sig pkg in
  let pkg := add_sub_bounded pkg in
  let pkg := add_opp_sig pkg in
  let pkg := add_opp_bounded pkg in
  let pkg := add_carry_sig pkg in
  let pkg := add_carry_bounded pkg in
  let pkg := add_nonzero_sig pkg in
  let pkg := add_ring pkg in
  let pkg := add_freeze_sig pkg in
  let pkg := add_Mxzladderstep_sig pkg in
  Tag.strip_subst_local pkg.

Module MakeMontgomeryPackage (PKG : PrePackage).
  Module Import MakeMontgomeryPackageInternal := MakePackageBase PKG.

  Ltac get_m' _ := get TAG.m'.
  Notation m' := (ltac:(let v := get_m' () in exact v)) (only parsing).
  Ltac get_r' _ := get TAG.r'.
  Notation r' := (ltac:(let v := get_r' () in exact v)) (only parsing).
  Ltac get_m'_correct _ := get TAG.m'_correct.
  Notation m'_correct := (ltac:(let v := get_m'_correct () in exact v)) (only parsing).
  Ltac get_r'_correct _ := get TAG.r'_correct.
  Notation r'_correct := (ltac:(let v := get_r'_correct () in exact v)) (only parsing).
  Ltac get_m_enc_correct_montgomery _ := get TAG.m_enc_correct_montgomery.
  Notation m_enc_correct_montgomery := (ltac:(let v := get_m_enc_correct_montgomery () in exact v)) (only parsing).
  Ltac get_r'_pow_correct _ := get TAG.r'_pow_correct.
  Notation r'_pow_correct := (ltac:(let v := get_r'_pow_correct () in exact v)) (only parsing).
  Ltac get_montgomery_to_F _ := get TAG.montgomery_to_F.
  Notation montgomery_to_F := (ltac:(let v := get_montgomery_to_F () in exact v)) (only parsing).
  Ltac get_r_big _ := get TAG.r_big.
  Notation r_big := (ltac:(let v := get_r_big () in exact v)) (only parsing).
  Ltac get_m_big _ := get TAG.m_big.
  Notation m_big := (ltac:(let v := get_m_big () in exact v)) (only parsing).
  Ltac get_m_enc_small _ := get TAG.m_enc_small.
  Notation m_enc_small := (ltac:(let v := get_m_enc_small () in exact v)) (only parsing).
  Ltac get_map_m_enc _ := get TAG.map_m_enc.
  Notation map_m_enc := (ltac:(let v := get_map_m_enc () in exact v)) (only parsing).
  Ltac get_mul_ext _ := get TAG.mul_ext.
  Notation mul_ext := (ltac:(let v := get_mul_ext () in exact v)) (only parsing).
  Ltac get_add_ext _ := get TAG.add_ext.
  Notation add_ext := (ltac:(let v := get_add_ext () in exact v)) (only parsing).
  Ltac get_sub_ext _ := get TAG.sub_ext.
  Notation sub_ext := (ltac:(let v := get_sub_ext () in exact v)) (only parsing).
  Ltac get_opp_ext _ := get TAG.opp_ext.
  Notation opp_ext := (ltac:(let v := get_opp_ext () in exact v)) (only parsing).
  Ltac get_carry_ext _ := get TAG.carry_ext.
  Notation carry_ext := (ltac:(let v := get_carry_ext () in exact v)) (only parsing).
  Ltac get_nonzero_ext _ := get TAG.nonzero_ext.
  Notation nonzero_ext := (ltac:(let v := get_nonzero_ext () in exact v)) (only parsing).
  Ltac get_mul_bounded _ := get TAG.mul_bounded.
  Notation mul_bounded := (ltac:(let v := get_mul_bounded () in exact v)) (only parsing).
  Ltac get_add_bounded _ := get TAG.add_bounded.
  Notation add_bounded := (ltac:(let v := get_add_bounded () in exact v)) (only parsing).
  Ltac get_sub_bounded _ := get TAG.sub_bounded.
  Notation sub_bounded := (ltac:(let v := get_sub_bounded () in exact v)) (only parsing).
  Ltac get_opp_bounded _ := get TAG.opp_bounded.
  Notation opp_bounded := (ltac:(let v := get_opp_bounded () in exact v)) (only parsing).
  Ltac get_carry_bounded _ := get TAG.carry_bounded.
  Notation carry_bounded := (ltac:(let v := get_carry_bounded () in exact v)) (only parsing).
  Ltac get_nonzero_sig _ := get TAG.nonzero_sig.
  Notation nonzero_sig := (ltac:(let v := get_nonzero_sig () in exact v)) (only parsing).
End MakeMontgomeryPackage.

End MontgomeryPackage.

End Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_MontgomeryPackage_WRAPPED.
Module Export Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_MontgomeryPackage.
Module Export Crypto.
Module Export Specific.
Module Export Framework.
Module Export ArithmeticSynthesis.
Module MontgomeryPackage.
Include Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_MontgomeryPackage_WRAPPED.MontgomeryPackage.
End MontgomeryPackage.

End ArithmeticSynthesis.

End Framework.

End Specific.

End Crypto.

End Crypto_DOT_Specific_DOT_Framework_DOT_ArithmeticSynthesis_DOT_MontgomeryPackage.
Module Crypto_DOT_Specific_DOT_Framework_DOT_IntegrationTestTemporaryMiscCommon_WRAPPED.
Module IntegrationTestTemporaryMiscCommon.

Import Coq.ZArith.BinInt.
Import Coq.Classes.Morphisms Coq.Classes.Morphisms_Prop.
Import Crypto.Util.Tuple.
Import Crypto.Util.BoundedWord.
Import Crypto.Util.Sigma.Lift.
Import Crypto.Util.Sigma.Associativity.
Import Crypto.Util.Sigma.MapProjections.
Import Crypto.Util.ZRange.
Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Import Crypto.Util.Tactics.MoveLetIn.
Import Crypto.Util.Tactics.DestructHead.

Definition adjust_tuple2_tuple2_sig {A P Q}
           (v : { a : { a : tuple (tuple A 2) 2 | (P (fst (fst a)) /\ P (snd (fst a))) /\ (P (fst (snd a)) /\ P (snd (snd a))) }
                | Q (exist _ _ (proj1 (proj1 (proj2_sig a))),
                     exist _ _ (proj2 (proj1 (proj2_sig a))),
                     (exist _ _ (proj1 (proj2 (proj2_sig a))),
                      exist _ _ (proj2 (proj2 (proj2_sig a))))) })
  : { a : tuple (tuple (@sig A P) 2) 2 | Q a }.
Proof.
  eexists.
  exact (proj2_sig v).
Defined.

Definition sig_R_trans_exist1 {B} (R : B -> B -> Prop) {HT : Transitive R} {A} (f : A -> B)
           (b b' : B)
           (pf : R b' b)
           (y : { a : A | R (f a) b' })
  : { a : A | R (f a) b }
  := let 'exist a p := y in exist _ a (transitivity (R:=R) p pf).
Ltac eexists_sig_etransitivity_R R :=
  lazymatch goal with
  | [ |- @sig ?A ?P ]
    => let RT := type of R in
       let B := lazymatch (eval hnf in RT) with ?B -> _ => B end in
       let lem := constr:(@sig_R_trans_exist1 B R _ A _ _ : forall b' pf y, @sig A P) in
       let lem := open_constr:(lem _) in
       simple refine (lem _ _)
  end.
Tactic Notation "eexists_sig_etransitivity_R" open_constr(R) := eexists_sig_etransitivity_R R.

Definition sig_eq_trans_exist1 {A B}
  := @sig_R_trans_exist1 B (@eq B) _ A.
Ltac eexists_sig_etransitivity :=
  lazymatch goal with
  | [ |- { a : ?A | @?f a = ?b } ]
    => let lem := open_constr:(@sig_eq_trans_exist1 A _ f b _) in
       simple refine (lem _ (_ : { a : A | _ }))
  end.
Definition sig_R_trans_rewrite_fun_exist1 {B} (R : B -> B -> Prop) {HT : Transitive R}
{A} (f : A -> B) (b : B) (f' : A -> B)
           (pf : forall a, R (f a) (f' a))
           (y : { a : A | R (f' a) b })
  : { a : A | R (f a) b }
  := let 'exist a p := y in exist _ a (transitivity (R:=R) (pf a) p).
Ltac eexists_sig_etransitivity_for_rewrite_fun_R R :=
  lazymatch goal with
  | [ |- @sig ?A ?P ]
    => let RT := type of R in
       let B := lazymatch (eval hnf in RT) with ?B -> _ => B end in
       let lem := constr:(@sig_R_trans_rewrite_fun_exist1 B R _ A _ _ : forall f' pf y, @sig A P) in
       let lem := open_constr:(lem _) in
       simple refine (lem _ _); cbv beta
  end.
Tactic Notation "eexists_sig_etransitivity_for_rewrite_fun_R" open_constr(R)
  := eexists_sig_etransitivity_for_rewrite_fun_R R.
Definition sig_eq_trans_rewrite_fun_exist1 {A B} (f f' : A -> B)
           (b : B)
           (pf : forall a, f' a = f a)
           (y : { a : A | f' a = b })
  : { a : A | f a = b }
  := let 'exist a p := y in exist _ a (eq_trans (eq_sym (pf a)) p).
Ltac eexists_sig_etransitivity_for_rewrite_fun :=
  lazymatch goal with
  | [ |- { a : ?A | @?f a = ?b } ]
    => let lem := open_constr:(@sig_eq_trans_rewrite_fun_exist1 A _ f _ b) in
       simple refine (lem _ _); cbv beta
  end.
Definition sig_conj_by_impl2 {A} {P Q : A -> Prop} (H : forall a : A, Q a -> P a)
           (H' : { a : A | Q a })
  : { a : A | P a /\ Q a }
  := let (a, p) := H' in exist _ a (conj (H a p) p).

Ltac make_P_for_apply_lift_sig P :=
  lazymatch P with
  | fun (f : ?F) => forall (a : ?A), @?P f a
    => constr:(fun (a : A)
               => ltac:(lazymatch constr:(fun (f : F)
                                          => ltac:(let v := (eval cbv beta in (P f a)) in
                                                   lazymatch (eval pattern (f a) in v) with
                                                   | ?k _ => exact k
                                                   end))
                        with
                        | fun _ => ?P
                          => let v := make_P_for_apply_lift_sig P in
                             exact v
                        end))
  | _ => P
  end.
Ltac apply_lift_sig :=
  let P := lazymatch goal with |- sig ?P => P end in
  let P := make_P_for_apply_lift_sig P in
  lazymatch goal with
  | [ |- { f | forall a b c d e, _ } ]
    => fail "apply_lift_sig does not yet support ≥ 5 binders"
  | [ |- { f | forall (a : ?A) (b : ?B) (c : ?C) (d : ?D), _ } ]
    => apply (@lift4_sig A B C D _ P)
  | [ |- { f | forall (a : ?A) (b : ?B) (c : ?C), _ } ]
    => apply (@lift3_sig A B C _ P)
  | [ |- { f | forall (a : ?A) (b : ?B), _ } ]
    => apply (@lift2_sig A B _ P)
  | [ |- { f | forall (a : ?A), _ } ]
    => apply (@lift1_sig A _ P)
  | [ |- { f | _ } ]
    => idtac
  end.
Ltac get_proj2_sig_map_arg_helper P :=
  lazymatch P with
  | (fun e => ?A -> @?B e)
    => let B' := get_proj2_sig_map_arg_helper B in
       uconstr:(A -> B')
  | _ => uconstr:(_ : Prop)
  end.
Ltac get_proj2_sig_map_arg _ :=
  lazymatch goal with
  | [ |- { e : ?T | @?E e } ]
    => let P := get_proj2_sig_map_arg_helper E in
       uconstr:(fun e : T => P)
  end.
Ltac get_phi1_for_preglue _ :=
  lazymatch goal with
  | [ |- { e | @?E e } ]
    => lazymatch E with
       | context[Tuple.map (Tuple.map ?phi) _ = _]
         => phi
       | context[?phi _ = _]
         => phi
       end
  end.
Ltac get_phi2_for_preglue _ :=
  lazymatch goal with
  | [ |- { e | @?E e } ]
    => lazymatch E with
       | context[_ = ?f (Tuple.map ?phi _)]
         => phi
       | context[_ = ?f (?phi _)]
         => phi
       | context[_ = ?phi _]
         => phi
       end
  end.
Ltac start_preglue :=
  apply_lift_sig; intros; cbv beta iota zeta;
  let phi := get_phi1_for_preglue () in
  let phi2 := get_phi2_for_preglue () in
  let P' := get_proj2_sig_map_arg () in
  refine (proj2_sig_map (P:=P') _ _);
  [ let FINAL := fresh "FINAL" in
    let a := fresh "a" in
    intros a FINAL;
    repeat (let H := fresh in intro H; specialize (FINAL H));
    lazymatch goal with
    | [ |- ?phi _ = ?RHS ]
      => refine (@eq_trans _ _ _ RHS FINAL _); cbv [phi phi2]; clear a FINAL
    | [ |- _ /\ Tuple.map (Tuple.map ?phi) _ = _ ]
      => split; cbv [phi phi2]; [ refine (proj1 FINAL); shelve | ]
    end
  | cbv [phi phi2] ].
Ltac do_set_sig f_sig :=
  let fZ := fresh f_sig in
  set (fZ := proj1_sig f_sig);
  context_to_dlet_in_rhs fZ;
  try cbv beta iota delta [proj1_sig f_sig] in fZ;
  cbv beta delta [fZ]; clear fZ;
  cbv beta iota delta [fst snd].
Ltac do_set_sig_1arg f_sig :=
  let fZ := fresh f_sig in
  set (fZ := proj1_sig f_sig);
  context_to_dlet_in_rhs (fZ _);
  try cbn beta iota delta [proj1_sig f_sig] in fZ;
  try cbv [f_sig] in fZ;
  cbv beta delta [fZ]; clear fZ;
  cbv beta iota delta [fst snd].
Ltac do_set_sigs _ :=
  lazymatch goal with
  | [ |- context[@proj1_sig ?a ?b ?f_sig] ]
    => let fZ := fresh f_sig in
       set (fZ := proj1_sig f_sig);
       context_to_dlet_in_rhs fZ;
       do_set_sigs ();
       try cbv beta iota delta [proj1_sig f_sig] in fZ;
       cbv beta delta [fZ];
       cbv beta iota delta [fst snd]
  | _ => idtac
  end.
Ltac trim_after_do_rewrite_with_sig _ :=
  repeat match goal with
         | [ |- Tuple.map ?f _ = Tuple.map ?f _ ]
           => apply f_equal
         end.
Ltac do_rewrite_with_sig_no_set_by f_sig by_tac :=
  let lem := constr:(proj2_sig f_sig) in
  let lemT := type of lem in
  let lemT := (eval cbv beta zeta in lemT) in
  rewrite <- (lem : lemT) by by_tac ();
  trim_after_do_rewrite_with_sig ().
Ltac do_rewrite_with_sig_by f_sig by_tac :=
  do_rewrite_with_sig_no_set_by f_sig by_tac;
  do_set_sig f_sig.
Ltac do_rewrite_with_sig_1arg_by f_sig by_tac :=
  do_rewrite_with_sig_no_set_by f_sig by_tac;
  do_set_sig_1arg f_sig.
Ltac do_rewrite_with_sig f_sig := do_rewrite_with_sig_by f_sig ltac:(fun _ => idtac).
Ltac do_rewrite_with_sig_1arg f_sig := do_rewrite_with_sig_1arg_by f_sig ltac:(fun _ => idtac).
Ltac do_rewrite_with_1sig_add_carry_by f_sig carry_sig by_tac :=
  let fZ := fresh f_sig in
  rewrite <- (proj2_sig f_sig) by by_tac ();
  symmetry; rewrite <- (proj2_sig carry_sig) by by_tac (); symmetry;
  pose (fun a => proj1_sig carry_sig (proj1_sig f_sig a)) as fZ;
  lazymatch goal with
  | [ |- context G[proj1_sig carry_sig (proj1_sig f_sig ?a)] ]
    => let G' := context G[fZ a] in change G'
  end;
  context_to_dlet_in_rhs fZ; cbv beta delta [fZ];
  try cbv beta iota delta [proj1_sig f_sig carry_sig];
  cbv beta iota delta [fst snd].
Ltac do_rewrite_with_1sig_add_carry f_sig carry_sig := do_rewrite_with_1sig_add_carry_by f_sig carry_sig ltac:(fun _ => idtac).
Ltac do_rewrite_with_2sig_add_carry_by f_sig carry_sig by_tac :=
  let fZ := fresh f_sig in
  rewrite <- (proj2_sig f_sig) by by_tac ();
  symmetry; rewrite <- (proj2_sig carry_sig) by by_tac (); symmetry;
  pose (fun a b => proj1_sig carry_sig (proj1_sig f_sig a b)) as fZ;
  lazymatch goal with
  | [ |- context G[proj1_sig carry_sig (proj1_sig f_sig ?a ?b)] ]
    => let G' := context G[fZ a b] in change G'
  end;
  context_to_dlet_in_rhs fZ; cbv beta delta [fZ];
  try cbv beta iota delta [proj1_sig f_sig carry_sig];
  cbv beta iota delta [fst snd].
Ltac do_rewrite_with_2sig_add_carry f_sig carry_sig := do_rewrite_with_2sig_add_carry_by f_sig carry_sig ltac:(fun _ => idtac).
Ltac unmap_map_tuple _ :=
  repeat match goal with
         | [ |- context[Tuple.map (n:=?N) (fun x : ?T => ?f (?g x))] ]
           => rewrite <- (Tuple.map_map (n:=N) f g
                          : pointwise_relation _ eq _ (Tuple.map (n:=N) (fun x : T => f (g x))))
         end.
Ltac get_feW_bounded boundedT :=
  lazymatch boundedT with
  | and ?X ?Y => get_feW_bounded X
  | ?feW_bounded _ => feW_bounded
  end.
Ltac subst_feW _ :=
  let T := lazymatch goal with |- @sig ?T _ => T end in
  let boundedT := lazymatch goal with |- { e | ?A -> _ } => A end in
  let feW_bounded := get_feW_bounded boundedT in
  let feW := lazymatch type of feW_bounded with ?feW -> Prop => feW end in
  cbv [feW feW_bounded];
  try clear feW feW_bounded.
Ltac finish_conjoined_preglue _ :=
  [ > match goal with
      | [ FINAL : _ /\ ?e |- _ ] => is_evar e; refine (proj2 FINAL)
      end
  | try subst_feW () ].
Ltac fin_preglue :=
  [ > reflexivity
  | repeat sig_dlet_in_rhs_to_context;
    apply (fun f => proj2_sig_map (fun THIS_NAME_MUST_NOT_BE_UNDERSCORE_TO_WORK_AROUND_CONSTR_MATCHING_ANAOMLIES___BUT_NOTE_THAT_IF_THIS_NAME_IS_LOWERCASE_A___THEN_REIFICATION_STACK_OVERFLOWS___AND_I_HAVE_NO_IDEA_WHATS_GOING_ON p => f_equal f p)) ].

Ltac factor_out_bounds_and_strip_eval op_bounded op_sig_side_conditions_t :=
  let feBW_small := lazymatch goal with |- { f : ?feBW_small | _ } => feBW_small end in
  Associativity.sig_sig_assoc;
  apply sig_conj_by_impl2;
  [ let H := fresh in
    intros ? H;
    try lazymatch goal with
        | [ |- (?eval _ < _)%Z ]
          => cbv [eval]
        end;
    rewrite H; clear H;
    eapply Z.le_lt_trans;
      [ apply Z.eq_le_incl, f_equal | apply op_bounded ];
      [ repeat match goal with
               | [ |- ?f ?x = ?g ?y ]
                 => is_evar y; unify x y;
                    apply (f_equal (fun fg => fg x))
               end;
        clear; abstract reflexivity
      | .. ];
      op_sig_side_conditions_t ()
  | apply (fun f => proj2_sig_map (fun THIS_NAME_MUST_NOT_BE_UNDERSCORE_TO_WORK_AROUND_CONSTR_MATCHING_ANAOMLIES___BUT_NOTE_THAT_IF_THIS_NAME_IS_LOWERCASE_A___THEN_REIFICATION_STACK_OVERFLOWS___AND_I_HAVE_NO_IDEA_WHATS_GOING_ON p => f_equal f p));
    cbv [proj1_sig];
    repeat match goal with
           | [ H : feBW_small |- _ ] => destruct H as [? _]
           end ].

Ltac op_sig_side_conditions_t _ :=
  try (hnf; rewrite <- (ZRange.is_bounded_by_None_repeat_In_iff_lt _ _ _)); destruct_head_hnf' sig; try assumption.

Local Open Scope Z_scope.

Ltac nonzero_preglue op_sig cbv_runtime :=
  let phi := lazymatch goal with
             | [ |- context[Decidable.dec (?phi _ = _)] ] => phi
             end in
  let do_red _ :=
      lazymatch (eval cbv [phi] in phi) with
      | (fun x => ?montgomery_to_F (?meval (?feBW_of_feBW_small _)))
        => cbv [feBW_of_feBW_small phi meval]
      end in
  lazymatch goal with
  | [ |- @sig (?feBW_small -> BoundedWord 1 _ ?bound1) _ ]
    => let b1 := (eval vm_compute in bound1) in
       change bound1 with b1
  end;
  apply_lift_sig; intros; eexists_sig_etransitivity;
  do_red ();
  [ refine (_ : (if Decidable.dec (_ = 0) then true else false) = _);
    lazymatch goal with
    | [ |- (if Decidable.dec ?x then _ else _) = (if Decidable.dec ?y then _ else _) ]
      => cut (x <-> y);
         [ destruct (Decidable.dec x), (Decidable.dec y); try reflexivity; intros [? ?];
           generalize dependent x; generalize dependent y; solve [ intuition congruence ]
         | ]
    end;
    etransitivity; [ | eapply (proj2_sig op_sig) ];
    [ | solve [ op_sig_side_conditions_t () ].. ];
    reflexivity
  | ];
  let decP := lazymatch goal with |- { c | _ = if Decidable.dec (?decP = 0) then _ else _ } => decP end in
  apply (@proj2_sig_map _ (fun c => BoundedWordToZ 1 _ _ c = decP) _);
  [ let a' := fresh "a'" in
    let H' := fresh "H'" in
    intros a' H'; rewrite H';
    let H := fresh in
    lazymatch goal with |- context[Decidable.dec ?x] => destruct (Decidable.dec x) as [H|H]; try rewrite H end;
    [ reflexivity
    | let H := fresh in
      lazymatch goal with |- context[?x =? 0] => destruct (x =? 0) eqn:? end;
      try reflexivity;
      Z.ltb_to_lt; congruence ]
  | ];
  eexists_sig_etransitivity;
  [ do_set_sig op_sig; cbv_runtime (); reflexivity
  | ];
  sig_dlet_in_rhs_to_context;
  cbv [proj1_sig];
  match goal with
  | [ |- context[match ?v with exist _ _ => _ end] ]
    => is_var v; destruct v as [? _]
  end.

End IntegrationTestTemporaryMiscCommon.

End Crypto_DOT_Specific_DOT_Framework_DOT_IntegrationTestTemporaryMiscCommon_WRAPPED.
Module Export Crypto_DOT_Specific_DOT_Framework_DOT_IntegrationTestTemporaryMiscCommon.
Module Export Crypto.
Module Export Specific.
Module Export Framework.
Module IntegrationTestTemporaryMiscCommon.
Include Crypto_DOT_Specific_DOT_Framework_DOT_IntegrationTestTemporaryMiscCommon_WRAPPED.IntegrationTestTemporaryMiscCommon.
End IntegrationTestTemporaryMiscCommon.

End Framework.

End Specific.

End Crypto.

End Crypto_DOT_Specific_DOT_Framework_DOT_IntegrationTestTemporaryMiscCommon.
Module Crypto_DOT_Specific_DOT_Framework_DOT_MontgomeryReificationTypes_WRAPPED.
Module MontgomeryReificationTypes.
Import Coq.ZArith.ZArith.
Import Coq.micromega.Lia Coq.Classes.Morphisms Coq.Classes.Morphisms_Prop.
Import Coq.Lists.List.
Local Open Scope Z_scope.
Import Crypto.Arithmetic.Core.
Import Crypto.Arithmetic.PrimeFieldTheorems.
Import Crypto.Util.FixedWordSizes.
Import Crypto.Util.Tuple.
Import Crypto.Util.ZRange Crypto.Util.BoundedWord.
Import Crypto.Util.Tactics.DestructHead.
Import Crypto.Util.Decidable.
Import Crypto.Util.Tactics.PoseTermWithName.
Import Crypto.Util.Tactics.CacheTerm.

Ltac pose_meval feBW_tight r meval :=
  cache_term_with_type_by
    (feBW_tight -> Z)
    ltac:(exact (fun x : feBW_tight => MontgomeryAPI.eval (Z.pos r) (BoundedWordToZ _ _ _ x)))
           meval.

Ltac pose_feBW_small sz feBW_tight meval r m_enc feBW_small :=
  cache_term
    { v : feBW_tight | meval v < MontgomeryAPI.eval (n:=sz) (Z.pos r) m_enc }
    feBW_small.

Ltac pose_feBW_tight_of_feBW_small feBW_tight feBW_small feBW_tight_of_feBW_small :=
  cache_term_with_type_by
    (feBW_small -> feBW_tight)
    ltac:(refine (@proj1_sig _ _))
           feBW_tight_of_feBW_small.

Ltac pose_phiM feBW_tight m meval montgomery_to_F phiM :=
  cache_term_with_type_by
    (feBW_tight -> F m)
    ltac:(exact (fun x : feBW_tight => montgomery_to_F (meval x)))
           phiM.

Ltac pose_phiM_small feBW_small feBW_tight_of_feBW_small m meval montgomery_to_F phiM_small :=
  cache_term_with_type_by
    (feBW_small -> F m)
    ltac:(exact (fun x : feBW_small => montgomery_to_F (meval (feBW_tight_of_feBW_small x))))
           phiM_small.

End MontgomeryReificationTypes.

End Crypto_DOT_Specific_DOT_Framework_DOT_MontgomeryReificationTypes_WRAPPED.
Module Export Crypto_DOT_Specific_DOT_Framework_DOT_MontgomeryReificationTypes.
Module Export Crypto.
Module Export Specific.
Module Export Framework.
Module MontgomeryReificationTypes.
Include Crypto_DOT_Specific_DOT_Framework_DOT_MontgomeryReificationTypes_WRAPPED.MontgomeryReificationTypes.
End MontgomeryReificationTypes.

End Framework.

End Specific.

End Crypto.

End Crypto_DOT_Specific_DOT_Framework_DOT_MontgomeryReificationTypes.
Module Crypto_DOT_Specific_DOT_Framework_DOT_ReificationTypes_WRAPPED.
Module ReificationTypes.
Import Coq.ZArith.ZArith.
Import Coq.micromega.Lia Coq.Classes.Morphisms Coq.Classes.Morphisms_Prop.
Import Coq.Lists.List.
Local Open Scope Z_scope.
Import Crypto.Arithmetic.Core.
Import Crypto.Arithmetic.PrimeFieldTheorems.
Import Crypto.Util.FixedWordSizes.
Import Crypto.Util.Tuple.
Import Crypto.Util.ZRange Crypto.Util.BoundedWord.
Import Crypto.Util.Tactics.DestructHead.
Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Import Crypto.Util.Bool.
Import Crypto.Util.Decidable.
Import Crypto.Util.Tactics.PoseTermWithName.
Import Crypto.Util.Tactics.CacheTerm.

Ltac pose_local_limb_widths wt sz limb_widths :=
  pose_term_with
    ltac:(fun _ => (eval vm_compute in (List.map (fun i => Z.log2 (wt (S i) / wt i)) (seq 0 sz))))
           limb_widths.

Ltac get_b_of upper_bound_of_exponent :=
  constr:(fun exp => {| lower := 0 ; upper := upper_bound_of_exponent exp |}%Z).

Ltac pose_local_bounds_exp sz limb_widths bounds_exp :=
  pose_term_with_type
    (Tuple.tuple Z sz)
    ltac:(fun _ => eval compute in
               (Tuple.from_list sz limb_widths eq_refl))
           bounds_exp.

Ltac internal_pose_local_bounds sz upper_bound_of_exponent bounds_exp bounds :=
  let b_of := get_b_of upper_bound_of_exponent in
  pose_term_with_type
    (Tuple.tuple zrange sz)
    ltac:(fun _ => eval compute in
               (Tuple.map (fun e => b_of e) bounds_exp))
           bounds.
Ltac pose_local_bounds_tight sz upper_bound_of_exponent_tight bounds_exp bounds_tight :=
  internal_pose_local_bounds sz upper_bound_of_exponent_tight bounds_exp bounds_tight.
Ltac pose_local_bounds_loose sz upper_bound_of_exponent_loose bounds_exp bounds_loose :=
  internal_pose_local_bounds sz upper_bound_of_exponent_loose bounds_exp bounds_loose.
Ltac pose_local_bounds_limbwidths sz bounds_exp bounds_limbwidths :=
  internal_pose_local_bounds sz (fun exp => (2^exp - 1)%Z) bounds_exp bounds_limbwidths.

Ltac pose_bound1 r bound1 :=
  cache_term_with_type_by
    zrange
    ltac:(exact {| lower := 0 ; upper := Z.pos r-1 |})
           bound1.

Ltac pose_local_lgbitwidth bitwidth lgbitwidth :=
  pose_term_with
    ltac:(fun _ => eval compute in (Z.to_nat (Z.log2_up bitwidth)))
           lgbitwidth.

Ltac pose_local_adjusted_bitwidth' lgbitwidth adjusted_bitwidth' :=
  pose_term_with
    ltac:(fun _ => eval compute in (2^lgbitwidth)%nat)
           adjusted_bitwidth'.
Ltac pose_adjusted_bitwidth adjusted_bitwidth' adjusted_bitwidth :=
  cache_term adjusted_bitwidth' adjusted_bitwidth.

Ltac pose_local_feZ sz feZ :=
  pose_term_with
    ltac:(fun _ => constr:(tuple Z sz))
           feZ.

Ltac pose_feW sz lgbitwidth feW :=
  cache_term_with_type_by
    Type
    ltac:(let v := eval cbv [lgbitwidth] in (tuple (wordT lgbitwidth) sz) in exact v)
           feW.
Ltac internal_pose_feW_bounded feW bounds feW_bounded :=
  cache_term_with_type_by
    (feW -> Prop)
    ltac:(let v := eval cbv [bounds] in (fun w : feW => is_bounded_by None bounds (map wordToZ w)) in exact_no_check v)
           feW_bounded.
Ltac pose_feW_tight_bounded feW bounds_tight feW_tight_bounded :=
  internal_pose_feW_bounded feW bounds_tight feW_tight_bounded.
Ltac pose_feW_loose_bounded feW bounds_loose feW_loose_bounded :=
  internal_pose_feW_bounded feW bounds_loose feW_loose_bounded.
Ltac pose_feW_limbwidths_bounded feW bounds_limbwidths feW_limbwidths_bounded :=
  internal_pose_feW_bounded feW bounds_limbwidths feW_limbwidths_bounded.

Ltac internal_pose_feBW sz adjusted_bitwidth' bounds feBW :=
  cache_term_with_type_by
    Type
    ltac:(let v := eval cbv [adjusted_bitwidth' bounds] in (BoundedWord sz adjusted_bitwidth' bounds) in exact v)
           feBW.
Ltac pose_feBW_tight sz adjusted_bitwidth' bounds_tight feBW_tight :=
  internal_pose_feBW sz adjusted_bitwidth' bounds_tight feBW_tight.
Ltac pose_feBW_loose sz adjusted_bitwidth' bounds_loose feBW_loose :=
  internal_pose_feBW sz adjusted_bitwidth' bounds_loose feBW_loose.
Ltac pose_feBW_limbwidths sz adjusted_bitwidth' bounds_limbwidths feBW_limbwidths :=
  internal_pose_feBW sz adjusted_bitwidth' bounds_limbwidths feBW_limbwidths.

Lemma relax'_pf {sz in_bounds out_bounds} {v : tuple Z sz}
      (Htight : fieldwiseb is_tighter_than_bool in_bounds out_bounds = true)
  : is_bounded_by None in_bounds v -> is_bounded_by None out_bounds v.
Proof.
  destruct sz as [|sz]; simpl in *; trivial.
  induction sz as [|sz IHsz]; simpl in *;
    repeat first [ exact I
                 | progress destruct_head'_prod
                 | progress destruct_head' zrange
                 | progress cbv [is_tighter_than_bool] in *
                 | progress split_andb
                 | progress Z.ltb_to_lt
                 | progress cbn [fst snd ZRange.lower ZRange.upper] in *
                 | progress destruct_head_hnf' and
                 | progress intros
                 | apply conj
                 | lia
                 | solve [ eauto ] ].
Qed.

Definition relax' {sz adjusted_bitwidth'} {in_bounds out_bounds}
           (Htight : Tuple.fieldwiseb ZRange.is_tighter_than_bool in_bounds out_bounds = true)
  : BoundedWord sz adjusted_bitwidth' in_bounds
    -> BoundedWord sz adjusted_bitwidth' out_bounds
  := fun w => exist _ (proj1_sig w) (relax'_pf Htight (proj2_sig w)).

Ltac internal_pose_feBW_relax sz feBW_in feBW_out feBW_relax :=
  cache_term_with_type_by
    (feBW_in -> feBW_out)
    ltac:(refine (@relax' sz _ _ _ _);
          lazymatch goal with
          | [ |- fieldwiseb is_tighter_than_bool ?in_bounds ?out_bounds = true ]
            => try cbv [in_bounds];
               try cbv [out_bounds]
          end;
          abstract vm_cast_no_check (eq_refl true))
           feBW_relax.
Ltac pose_feBW_relax sz feBW_tight feBW_loose feBW_relax :=
  internal_pose_feBW_relax sz feBW_tight feBW_loose feBW_relax.
Ltac pose_feBW_relax_limbwidths_to_tight sz feBW_limbwidths feBW_tight feBW_relax_limbwidths_to_tight :=
  internal_pose_feBW_relax sz feBW_limbwidths feBW_tight feBW_relax_limbwidths_to_tight.
Ltac pose_feBW_relax_limbwidths_to_loose sz feBW_limbwidths feBW_loose feBW_relax_limbwidths_to_loose :=
  internal_pose_feBW_relax sz feBW_limbwidths feBW_loose feBW_relax_limbwidths_to_loose.

Lemma feBW_bounded_helper'
      sz adjusted_bitwidth' bounds
      (feBW := BoundedWord sz adjusted_bitwidth' bounds)
      (wt : nat -> Z)
      (Hwt : forall i, 0 <= wt i)
  : forall (a : feBW),
    B.Positional.eval wt (map lower bounds)
    <= B.Positional.eval wt (BoundedWordToZ sz adjusted_bitwidth' bounds a)
    <= B.Positional.eval wt (map upper bounds).
Proof.
  let a := fresh "a" in
  intro a;
    destruct a as [a H]; unfold BoundedWordToZ, proj1_sig.
  destruct sz as [|sz].
  { cbv -[Z.le Z.lt Z.mul]; lia.
}
  { cbn [tuple map] in *.
    revert dependent wt; induction sz as [|sz IHsz]; intros.
    { cbv -[Z.le Z.lt wordToZ Z.mul Z.pow Z.add lower upper Nat.log2 wordT] in *.
      repeat match goal with
             | [ |- context[@wordToZ ?n ?x] ]
               => generalize dependent (@wordToZ n x); intros
             | [ H : forall j, 0 <= wt j |- context[wt ?i] ]
               => pose proof (H i); generalize dependent (wt i); intros
             end.
      nia.
}
    { pose proof (Hwt 0%nat).
      cbn [tuple' map'] in *.
      destruct a as [a' a], bounds as [bounds b], H as [H [H' _]].
      cbn [fst snd] in *.
      setoid_rewrite (@B.Positional.eval_step (S _)).
      specialize (IHsz bounds a' H (fun i => wt (S i)) (fun i => Hwt _)).
      nia.
} }
Qed.
Lemma feBW_bounded_helper
      sz adjusted_bitwidth' bounds
      (feBW := BoundedWord sz adjusted_bitwidth' bounds)
      (wt : nat -> Z)
      (Hwt : forall i, 0 <= wt i)
      l u
  : l <= B.Positional.eval wt (map lower bounds)
    /\ B.Positional.eval wt (map upper bounds) < u
    -> forall (a : feBW),
      l <= B.Positional.eval wt (BoundedWordToZ sz adjusted_bitwidth' bounds a) < u.
Proof.
  intros [Hl Hu] a; split;
    [ eapply Z.le_trans | eapply Z.le_lt_trans ];
    [ | eapply feBW_bounded_helper' | eapply feBW_bounded_helper' | ];
    assumption.
Qed.

Ltac internal_pose_feBW_bounded freeze wt sz feBW adjusted_bitwidth' bounds m wt_nonneg feBW_bounded :=
  lazymatch (eval vm_compute in freeze) with
  | true
    => cache_proof_with_type_by
         (forall a : feBW, 0 <= B.Positional.eval wt (BoundedWordToZ sz adjusted_bitwidth' bounds a) < 2 * Z.pos m)
         ltac:(apply (@feBW_bounded_helper sz adjusted_bitwidth' bounds wt wt_nonneg);
               cbv -[Z.lt Z.le];
               clear; vm_decide)
                feBW_bounded
  | false
    => cache_term tt feBW_bounded
  end.
Ltac pose_feBW_tight_bounded freeze wt sz feBW_tight adjusted_bitwidth' bounds_tight m wt_nonneg feBW_tight_bounded :=
  internal_pose_feBW_bounded freeze wt sz feBW_tight adjusted_bitwidth' bounds_tight m wt_nonneg feBW_tight_bounded.
Ltac pose_feBW_limbwidths_bounded freeze wt sz feBW_limbwidths adjusted_bitwidth' bounds_limbwidths m wt_nonneg feBW_limbwidths_bounded :=
  internal_pose_feBW_bounded freeze wt sz feBW_limbwidths adjusted_bitwidth' bounds_limbwidths m wt_nonneg feBW_limbwidths_bounded.

Ltac pose_phiW feW m wt phiW :=
  cache_term_with_type_by
    (feW -> F m)
    ltac:(exact (fun x : feW => B.Positional.Fdecode wt (Tuple.map wordToZ x)))
           phiW.
Ltac internal_pose_phiBW feBW m wt phiBW :=
  cache_term_with_type_by
    (feBW -> F m)
    ltac:(exact (fun x : feBW => B.Positional.Fdecode wt (BoundedWordToZ _ _ _ x)))
           phiBW.
Ltac pose_phiBW_tight feBW_tight m wt phiBW_tight :=
  internal_pose_phiBW feBW_tight m wt phiBW_tight.
Ltac pose_phiBW_loose feBW_loose m wt phiBW_loose :=
  internal_pose_phiBW feBW_loose m wt phiBW_loose.
Ltac pose_phiBW_limbwidths feBW_limbwidths m wt phiBW_limbwidths :=
  internal_pose_phiBW feBW_limbwidths m wt phiBW_limbwidths.

End ReificationTypes.

End Crypto_DOT_Specific_DOT_Framework_DOT_ReificationTypes_WRAPPED.
Module Export Crypto_DOT_Specific_DOT_Framework_DOT_ReificationTypes.
Module Export Crypto.
Module Export Specific.
Module Export Framework.
Module ReificationTypes.
Include Crypto_DOT_Specific_DOT_Framework_DOT_ReificationTypes_WRAPPED.ReificationTypes.
End ReificationTypes.

End Framework.

End Specific.

End Crypto.

End Crypto_DOT_Specific_DOT_Framework_DOT_ReificationTypes.
Module Crypto_DOT_Specific_DOT_Framework_DOT_ReificationTypesPackage_WRAPPED.
Module ReificationTypesPackage.

Import Crypto.Specific.Framework.CurveParametersPackage.
Import Crypto.Specific.Framework.ArithmeticSynthesis.BasePackage.
Export Crypto.Specific.Framework.ReificationTypes.
Import Crypto.Specific.Framework.Packages.
Import Crypto.Util.TagList.

Module TAG.
  Inductive tags := limb_widths | bounds_exp | bounds_tight | bounds_loose | bounds_limbwidths | bound1 | lgbitwidth | adjusted_bitwidth' | adjusted_bitwidth | feZ | feW | feW_tight_bounded | feW_loose_bounded | feW_limbwidths_bounded | feBW_tight | feBW_loose | feBW_limbwidths | feBW_relax | feBW_relax_limbwidths_to_tight | feBW_relax_limbwidths_to_loose | feBW_tight_bounded | feBW_limbwidths_bounded | phiW | phiBW_tight | phiBW_loose | phiBW_limbwidths.
End TAG.

Ltac add_limb_widths pkg :=
  let wt := Tag.get pkg TAG.wt in
  let sz := Tag.get pkg TAG.sz in
  let limb_widths := fresh "limb_widths" in
  let limb_widths := pose_local_limb_widths wt sz limb_widths in
  Tag.local_update pkg TAG.limb_widths limb_widths.

Ltac add_bounds_exp pkg :=
  let sz := Tag.get pkg TAG.sz in
  let limb_widths := Tag.get pkg TAG.limb_widths in
  let bounds_exp := fresh "bounds_exp" in
  let bounds_exp := pose_local_bounds_exp sz limb_widths bounds_exp in
  Tag.local_update pkg TAG.bounds_exp bounds_exp.

Ltac add_bounds_tight pkg :=
  let sz := Tag.get pkg TAG.sz in
  let upper_bound_of_exponent_tight := Tag.get pkg TAG.upper_bound_of_exponent_tight in
  let bounds_exp := Tag.get pkg TAG.bounds_exp in
  let bounds_tight := fresh "bounds_tight" in
  let bounds_tight := pose_local_bounds_tight sz upper_bound_of_exponent_tight bounds_exp bounds_tight in
  Tag.local_update pkg TAG.bounds_tight bounds_tight.

Ltac add_bounds_loose pkg :=
  let sz := Tag.get pkg TAG.sz in
  let upper_bound_of_exponent_loose := Tag.get pkg TAG.upper_bound_of_exponent_loose in
  let bounds_exp := Tag.get pkg TAG.bounds_exp in
  let bounds_loose := fresh "bounds_loose" in
  let bounds_loose := pose_local_bounds_loose sz upper_bound_of_exponent_loose bounds_exp bounds_loose in
  Tag.local_update pkg TAG.bounds_loose bounds_loose.

Ltac add_bounds_limbwidths pkg :=
  let sz := Tag.get pkg TAG.sz in
  let bounds_exp := Tag.get pkg TAG.bounds_exp in
  let bounds_limbwidths := fresh "bounds_limbwidths" in
  let bounds_limbwidths := pose_local_bounds_limbwidths sz bounds_exp bounds_limbwidths in
  Tag.local_update pkg TAG.bounds_limbwidths bounds_limbwidths.

Ltac add_bound1 pkg :=
  let r := Tag.get pkg TAG.r in
  let bound1 := fresh "bound1" in
  let bound1 := pose_bound1 r bound1 in
  Tag.update pkg TAG.bound1 bound1.

Ltac add_lgbitwidth pkg :=
  let bitwidth := Tag.get pkg TAG.bitwidth in
  let lgbitwidth := fresh "lgbitwidth" in
  let lgbitwidth := pose_local_lgbitwidth bitwidth lgbitwidth in
  Tag.local_update pkg TAG.lgbitwidth lgbitwidth.

Ltac add_adjusted_bitwidth' pkg :=
  let lgbitwidth := Tag.get pkg TAG.lgbitwidth in
  let adjusted_bitwidth' := fresh "adjusted_bitwidth'" in
  let adjusted_bitwidth' := pose_local_adjusted_bitwidth' lgbitwidth adjusted_bitwidth' in
  Tag.local_update pkg TAG.adjusted_bitwidth' adjusted_bitwidth'.

Ltac add_adjusted_bitwidth pkg :=
  let adjusted_bitwidth' := Tag.get pkg TAG.adjusted_bitwidth' in
  let adjusted_bitwidth := fresh "adjusted_bitwidth" in
  let adjusted_bitwidth := pose_adjusted_bitwidth adjusted_bitwidth' adjusted_bitwidth in
  Tag.update pkg TAG.adjusted_bitwidth adjusted_bitwidth.

Ltac add_feZ pkg :=
  let sz := Tag.get pkg TAG.sz in
  let feZ := fresh "feZ" in
  let feZ := pose_local_feZ sz feZ in
  Tag.local_update pkg TAG.feZ feZ.

Ltac add_feW pkg :=
  let sz := Tag.get pkg TAG.sz in
  let lgbitwidth := Tag.get pkg TAG.lgbitwidth in
  let feW := fresh "feW" in
  let feW := pose_feW sz lgbitwidth feW in
  Tag.update pkg TAG.feW feW.

Ltac add_feW_tight_bounded pkg :=
  let feW := Tag.get pkg TAG.feW in
  let bounds_tight := Tag.get pkg TAG.bounds_tight in
  let feW_tight_bounded := fresh "feW_tight_bounded" in
  let feW_tight_bounded := pose_feW_tight_bounded feW bounds_tight feW_tight_bounded in
  Tag.update pkg TAG.feW_tight_bounded feW_tight_bounded.

Ltac add_feW_loose_bounded pkg :=
  let feW := Tag.get pkg TAG.feW in
  let bounds_loose := Tag.get pkg TAG.bounds_loose in
  let feW_loose_bounded := fresh "feW_loose_bounded" in
  let feW_loose_bounded := pose_feW_loose_bounded feW bounds_loose feW_loose_bounded in
  Tag.update pkg TAG.feW_loose_bounded feW_loose_bounded.

Ltac add_feW_limbwidths_bounded pkg :=
  let feW := Tag.get pkg TAG.feW in
  let bounds_limbwidths := Tag.get pkg TAG.bounds_limbwidths in
  let feW_limbwidths_bounded := fresh "feW_limbwidths_bounded" in
  let feW_limbwidths_bounded := pose_feW_limbwidths_bounded feW bounds_limbwidths feW_limbwidths_bounded in
  Tag.update pkg TAG.feW_limbwidths_bounded feW_limbwidths_bounded.

Ltac add_feBW_tight pkg :=
  let sz := Tag.get pkg TAG.sz in
  let adjusted_bitwidth' := Tag.get pkg TAG.adjusted_bitwidth' in
  let bounds_tight := Tag.get pkg TAG.bounds_tight in
  let feBW_tight := fresh "feBW_tight" in
  let feBW_tight := pose_feBW_tight sz adjusted_bitwidth' bounds_tight feBW_tight in
  Tag.update pkg TAG.feBW_tight feBW_tight.

Ltac add_feBW_loose pkg :=
  let sz := Tag.get pkg TAG.sz in
  let adjusted_bitwidth' := Tag.get pkg TAG.adjusted_bitwidth' in
  let bounds_loose := Tag.get pkg TAG.bounds_loose in
  let feBW_loose := fresh "feBW_loose" in
  let feBW_loose := pose_feBW_loose sz adjusted_bitwidth' bounds_loose feBW_loose in
  Tag.update pkg TAG.feBW_loose feBW_loose.

Ltac add_feBW_limbwidths pkg :=
  let sz := Tag.get pkg TAG.sz in
  let adjusted_bitwidth' := Tag.get pkg TAG.adjusted_bitwidth' in
  let bounds_limbwidths := Tag.get pkg TAG.bounds_limbwidths in
  let feBW_limbwidths := fresh "feBW_limbwidths" in
  let feBW_limbwidths := pose_feBW_limbwidths sz adjusted_bitwidth' bounds_limbwidths feBW_limbwidths in
  Tag.update pkg TAG.feBW_limbwidths feBW_limbwidths.

Ltac add_feBW_relax pkg :=
  let sz := Tag.get pkg TAG.sz in
  let feBW_tight := Tag.get pkg TAG.feBW_tight in
  let feBW_loose := Tag.get pkg TAG.feBW_loose in
  let feBW_relax := fresh "feBW_relax" in
  let feBW_relax := pose_feBW_relax sz feBW_tight feBW_loose feBW_relax in
  Tag.update pkg TAG.feBW_relax feBW_relax.

Ltac add_feBW_relax_limbwidths_to_tight pkg :=
  let sz := Tag.get pkg TAG.sz in
  let feBW_limbwidths := Tag.get pkg TAG.feBW_limbwidths in
  let feBW_tight := Tag.get pkg TAG.feBW_tight in
  let feBW_relax_limbwidths_to_tight := fresh "feBW_relax_limbwidths_to_tight" in
  let feBW_relax_limbwidths_to_tight := pose_feBW_relax_limbwidths_to_tight sz feBW_limbwidths feBW_tight feBW_relax_limbwidths_to_tight in
  Tag.update pkg TAG.feBW_relax_limbwidths_to_tight feBW_relax_limbwidths_to_tight.

Ltac add_feBW_relax_limbwidths_to_loose pkg :=
  let sz := Tag.get pkg TAG.sz in
  let feBW_limbwidths := Tag.get pkg TAG.feBW_limbwidths in
  let feBW_loose := Tag.get pkg TAG.feBW_loose in
  let feBW_relax_limbwidths_to_loose := fresh "feBW_relax_limbwidths_to_loose" in
  let feBW_relax_limbwidths_to_loose := pose_feBW_relax_limbwidths_to_loose sz feBW_limbwidths feBW_loose feBW_relax_limbwidths_to_loose in
  Tag.update pkg TAG.feBW_relax_limbwidths_to_loose feBW_relax_limbwidths_to_loose.

Ltac add_feBW_tight_bounded pkg :=
  let freeze := Tag.get pkg TAG.freeze in
  let wt := Tag.get pkg TAG.wt in
  let sz := Tag.get pkg TAG.sz in
  let feBW_tight := Tag.get pkg TAG.feBW_tight in
  let adjusted_bitwidth' := Tag.get pkg TAG.adjusted_bitwidth' in
  let bounds_tight := Tag.get pkg TAG.bounds_tight in
  let m := Tag.get pkg TAG.m in
  let wt_nonneg := Tag.get pkg TAG.wt_nonneg in
  let feBW_tight_bounded := fresh "feBW_tight_bounded" in
  let feBW_tight_bounded := pose_feBW_tight_bounded freeze wt sz feBW_tight adjusted_bitwidth' bounds_tight m wt_nonneg feBW_tight_bounded in
  Tag.update pkg TAG.feBW_tight_bounded feBW_tight_bounded.

Ltac add_feBW_limbwidths_bounded pkg :=
  let freeze := Tag.get pkg TAG.freeze in
  let wt := Tag.get pkg TAG.wt in
  let sz := Tag.get pkg TAG.sz in
  let feBW_limbwidths := Tag.get pkg TAG.feBW_limbwidths in
  let adjusted_bitwidth' := Tag.get pkg TAG.adjusted_bitwidth' in
  let bounds_limbwidths := Tag.get pkg TAG.bounds_limbwidths in
  let m := Tag.get pkg TAG.m in
  let wt_nonneg := Tag.get pkg TAG.wt_nonneg in
  let feBW_limbwidths_bounded := fresh "feBW_limbwidths_bounded" in
  let feBW_limbwidths_bounded := pose_feBW_limbwidths_bounded freeze wt sz feBW_limbwidths adjusted_bitwidth' bounds_limbwidths m wt_nonneg feBW_limbwidths_bounded in
  Tag.update pkg TAG.feBW_limbwidths_bounded feBW_limbwidths_bounded.

Ltac add_phiW pkg :=
  let feW := Tag.get pkg TAG.feW in
  let m := Tag.get pkg TAG.m in
  let wt := Tag.get pkg TAG.wt in
  let phiW := fresh "phiW" in
  let phiW := pose_phiW feW m wt phiW in
  Tag.update pkg TAG.phiW phiW.

Ltac add_phiBW_tight pkg :=
  let feBW_tight := Tag.get pkg TAG.feBW_tight in
  let m := Tag.get pkg TAG.m in
  let wt := Tag.get pkg TAG.wt in
  let phiBW_tight := fresh "phiBW_tight" in
  let phiBW_tight := pose_phiBW_tight feBW_tight m wt phiBW_tight in
  Tag.update pkg TAG.phiBW_tight phiBW_tight.

Ltac add_phiBW_loose pkg :=
  let feBW_loose := Tag.get pkg TAG.feBW_loose in
  let m := Tag.get pkg TAG.m in
  let wt := Tag.get pkg TAG.wt in
  let phiBW_loose := fresh "phiBW_loose" in
  let phiBW_loose := pose_phiBW_loose feBW_loose m wt phiBW_loose in
  Tag.update pkg TAG.phiBW_loose phiBW_loose.

Ltac add_phiBW_limbwidths pkg :=
  let feBW_limbwidths := Tag.get pkg TAG.feBW_limbwidths in
  let m := Tag.get pkg TAG.m in
  let wt := Tag.get pkg TAG.wt in
  let phiBW_limbwidths := fresh "phiBW_limbwidths" in
  let phiBW_limbwidths := pose_phiBW_limbwidths feBW_limbwidths m wt phiBW_limbwidths in
  Tag.update pkg TAG.phiBW_limbwidths phiBW_limbwidths.

Ltac add_ReificationTypes_package pkg :=
  let pkg := add_limb_widths pkg in
  let pkg := add_bounds_exp pkg in
  let pkg := add_bounds_tight pkg in
  let pkg := add_bounds_loose pkg in
  let pkg := add_bounds_limbwidths pkg in
  let pkg := add_bound1 pkg in
  let pkg := add_lgbitwidth pkg in
  let pkg := add_adjusted_bitwidth' pkg in
  let pkg := add_adjusted_bitwidth pkg in
  let pkg := add_feZ pkg in
  let pkg := add_feW pkg in
  let pkg := add_feW_tight_bounded pkg in
  let pkg := add_feW_loose_bounded pkg in
  let pkg := add_feW_limbwidths_bounded pkg in
  let pkg := add_feBW_tight pkg in
  let pkg := add_feBW_loose pkg in
  let pkg := add_feBW_limbwidths pkg in
  let pkg := add_feBW_relax pkg in
  let pkg := add_feBW_relax_limbwidths_to_tight pkg in
  let pkg := add_feBW_relax_limbwidths_to_loose pkg in
  let pkg := add_feBW_tight_bounded pkg in
  let pkg := add_feBW_limbwidths_bounded pkg in
  let pkg := add_phiW pkg in
  let pkg := add_phiBW_tight pkg in
  let pkg := add_phiBW_loose pkg in
  let pkg := add_phiBW_limbwidths pkg in
  Tag.strip_subst_local pkg.

Module MakeReificationTypesPackage (PKG : PrePackage).
  Module Import MakeReificationTypesPackageInternal := MakePackageBase PKG.

  Ltac get_bound1 _ := get TAG.bound1.
  Notation bound1 := (ltac:(let v := get_bound1 () in exact v)) (only parsing).
  Ltac get_adjusted_bitwidth _ := get TAG.adjusted_bitwidth.
  Notation adjusted_bitwidth := (ltac:(let v := get_adjusted_bitwidth () in exact v)) (only parsing).
  Ltac get_feW _ := get TAG.feW.
  Notation feW := (ltac:(let v := get_feW () in exact v)) (only parsing).
  Ltac get_feW_tight_bounded _ := get TAG.feW_tight_bounded.
  Notation feW_tight_bounded := (ltac:(let v := get_feW_tight_bounded () in exact v)) (only parsing).
  Ltac get_feW_loose_bounded _ := get TAG.feW_loose_bounded.
  Notation feW_loose_bounded := (ltac:(let v := get_feW_loose_bounded () in exact v)) (only parsing).
  Ltac get_feW_limbwidths_bounded _ := get TAG.feW_limbwidths_bounded.
  Notation feW_limbwidths_bounded := (ltac:(let v := get_feW_limbwidths_bounded () in exact v)) (only parsing).
  Ltac get_feBW_tight _ := get TAG.feBW_tight.
  Notation feBW_tight := (ltac:(let v := get_feBW_tight () in exact v)) (only parsing).
  Ltac get_feBW_loose _ := get TAG.feBW_loose.
  Notation feBW_loose := (ltac:(let v := get_feBW_loose () in exact v)) (only parsing).
  Ltac get_feBW_limbwidths _ := get TAG.feBW_limbwidths.
  Notation feBW_limbwidths := (ltac:(let v := get_feBW_limbwidths () in exact v)) (only parsing).
  Ltac get_feBW_relax _ := get TAG.feBW_relax.
  Notation feBW_relax := (ltac:(let v := get_feBW_relax () in exact v)) (only parsing).
  Ltac get_feBW_relax_limbwidths_to_tight _ := get TAG.feBW_relax_limbwidths_to_tight.
  Notation feBW_relax_limbwidths_to_tight := (ltac:(let v := get_feBW_relax_limbwidths_to_tight () in exact v)) (only parsing).
  Ltac get_feBW_relax_limbwidths_to_loose _ := get TAG.feBW_relax_limbwidths_to_loose.
  Notation feBW_relax_limbwidths_to_loose := (ltac:(let v := get_feBW_relax_limbwidths_to_loose () in exact v)) (only parsing).
  Ltac get_feBW_tight_bounded _ := get TAG.feBW_tight_bounded.
  Notation feBW_tight_bounded := (ltac:(let v := get_feBW_tight_bounded () in exact v)) (only parsing).
  Ltac get_feBW_limbwidths_bounded _ := get TAG.feBW_limbwidths_bounded.
  Notation feBW_limbwidths_bounded := (ltac:(let v := get_feBW_limbwidths_bounded () in exact v)) (only parsing).
  Ltac get_phiW _ := get TAG.phiW.
  Notation phiW := (ltac:(let v := get_phiW () in exact v)) (only parsing).
  Ltac get_phiBW_tight _ := get TAG.phiBW_tight.
  Notation phiBW_tight := (ltac:(let v := get_phiBW_tight () in exact v)) (only parsing).
  Ltac get_phiBW_loose _ := get TAG.phiBW_loose.
  Notation phiBW_loose := (ltac:(let v := get_phiBW_loose () in exact v)) (only parsing).
  Ltac get_phiBW_limbwidths _ := get TAG.phiBW_limbwidths.
  Notation phiBW_limbwidths := (ltac:(let v := get_phiBW_limbwidths () in exact v)) (only parsing).
End MakeReificationTypesPackage.

End ReificationTypesPackage.

End Crypto_DOT_Specific_DOT_Framework_DOT_ReificationTypesPackage_WRAPPED.
Module Export Crypto_DOT_Specific_DOT_Framework_DOT_ReificationTypesPackage.
Module Export Crypto.
Module Export Specific.
Module Export Framework.
Module ReificationTypesPackage.
Include Crypto_DOT_Specific_DOT_Framework_DOT_ReificationTypesPackage_WRAPPED.ReificationTypesPackage.
End ReificationTypesPackage.

End Framework.

End Specific.

End Crypto.

End Crypto_DOT_Specific_DOT_Framework_DOT_ReificationTypesPackage.
Module Crypto_DOT_Specific_DOT_Framework_DOT_MontgomeryReificationTypesPackage_WRAPPED.
Module MontgomeryReificationTypesPackage.

Import Crypto.Specific.Framework.CurveParametersPackage.
Import Crypto.Specific.Framework.ArithmeticSynthesis.BasePackage.
Import Crypto.Specific.Framework.ArithmeticSynthesis.MontgomeryPackage.
Import Crypto.Specific.Framework.ReificationTypesPackage.
Export Crypto.Specific.Framework.MontgomeryReificationTypes.
Import Crypto.Specific.Framework.Packages.
Import Crypto.Util.TagList.

Module TAG.
  Inductive tags := meval | feBW_small | feBW_tight_of_feBW_small | phiM | phiM_small.
End TAG.

Ltac add_meval pkg :=
  if_montgomery
    pkg
    ltac:(fun _ => let feBW_tight := Tag.get pkg TAG.feBW_tight in
                   let r := Tag.get pkg TAG.r in
                   let meval := fresh "meval" in
                   let meval := pose_meval feBW_tight r meval in
                   Tag.update pkg TAG.meval meval)
    ltac:(fun _ => pkg)
    ().
Ltac add_feBW_small pkg :=
  if_montgomery
    pkg
    ltac:(fun _ => let sz := Tag.get pkg TAG.sz in
                   let feBW_tight := Tag.get pkg TAG.feBW_tight in
                   let meval := Tag.get pkg TAG.meval in
                   let r := Tag.get pkg TAG.r in
                   let m_enc := Tag.get pkg TAG.m_enc in
                   let feBW_small := fresh "feBW_small" in
                   let feBW_small := pose_feBW_small sz feBW_tight meval r m_enc feBW_small in
                   Tag.update pkg TAG.feBW_small feBW_small)
    ltac:(fun _ => pkg)
    ().
Ltac add_feBW_tight_of_feBW_small pkg :=
  if_montgomery
    pkg
    ltac:(fun _ => let feBW_tight := Tag.get pkg TAG.feBW_tight in
                   let feBW_small := Tag.get pkg TAG.feBW_small in
                   let feBW_tight_of_feBW_small := fresh "feBW_tight_of_feBW_small" in
                   let feBW_tight_of_feBW_small := pose_feBW_tight_of_feBW_small feBW_tight feBW_small feBW_tight_of_feBW_small in
                   Tag.update pkg TAG.feBW_tight_of_feBW_small feBW_tight_of_feBW_small)
    ltac:(fun _ => pkg)
    ().
Ltac add_phiM pkg :=
  if_montgomery
    pkg
    ltac:(fun _ => let feBW_tight := Tag.get pkg TAG.feBW_tight in
                   let m := Tag.get pkg TAG.m in
                   let meval := Tag.get pkg TAG.meval in
                   let montgomery_to_F := Tag.get pkg TAG.montgomery_to_F in
                   let phiM := fresh "phiM" in
                   let phiM := pose_phiM feBW_tight m meval montgomery_to_F phiM in
                   Tag.update pkg TAG.phiM phiM)
    ltac:(fun _ => pkg)
    ().
Ltac add_phiM_small pkg :=
  if_montgomery
    pkg
    ltac:(fun _ => let feBW_small := Tag.get pkg TAG.feBW_small in
                   let feBW_tight_of_feBW_small := Tag.get pkg TAG.feBW_tight_of_feBW_small in
                   let m := Tag.get pkg TAG.m in
                   let meval := Tag.get pkg TAG.meval in
                   let montgomery_to_F := Tag.get pkg TAG.montgomery_to_F in
                   let phiM_small := fresh "phiM_small" in
                   let phiM_small := pose_phiM_small feBW_small feBW_tight_of_feBW_small m meval montgomery_to_F phiM_small in
                   Tag.update pkg TAG.phiM_small phiM_small)
    ltac:(fun _ => pkg)
    ().
Ltac add_MontgomeryReificationTypes_package pkg :=
  let pkg := add_meval pkg in
  let pkg := add_feBW_small pkg in
  let pkg := add_feBW_tight_of_feBW_small pkg in
  let pkg := add_phiM pkg in
  let pkg := add_phiM_small pkg in
  Tag.strip_subst_local pkg.

Module MakeMontgomeryReificationTypesPackage (PKG : PrePackage).
  Module Import MakeMontgomeryReificationTypesPackageInternal := MakePackageBase PKG.

  Ltac get_meval _ := get TAG.meval.
  Notation meval := (ltac:(let v := get_meval () in exact v)) (only parsing).
  Ltac get_feBW_small _ := get TAG.feBW_small.
  Notation feBW_small := (ltac:(let v := get_feBW_small () in exact v)) (only parsing).
  Ltac get_feBW_tight_of_feBW_small _ := get TAG.feBW_tight_of_feBW_small.
  Notation feBW_tight_of_feBW_small := (ltac:(let v := get_feBW_tight_of_feBW_small () in exact v)) (only parsing).
  Ltac get_phiM _ := get TAG.phiM.
  Notation phiM := (ltac:(let v := get_phiM () in exact v)) (only parsing).
  Ltac get_phiM_small _ := get TAG.phiM_small.
  Notation phiM_small := (ltac:(let v := get_phiM_small () in exact v)) (only parsing).
End MakeMontgomeryReificationTypesPackage.

End MontgomeryReificationTypesPackage.

End Crypto_DOT_Specific_DOT_Framework_DOT_MontgomeryReificationTypesPackage_WRAPPED.
Module Export Crypto_DOT_Specific_DOT_Framework_DOT_MontgomeryReificationTypesPackage.
Module Export Crypto.
Module Export Specific.
Module Export Framework.
Module MontgomeryReificationTypesPackage.
Include Crypto_DOT_Specific_DOT_Framework_DOT_MontgomeryReificationTypesPackage_WRAPPED.MontgomeryReificationTypesPackage.
End MontgomeryReificationTypesPackage.

End Framework.

End Specific.

End Crypto.

End Crypto_DOT_Specific_DOT_Framework_DOT_MontgomeryReificationTypesPackage.
Module Crypto_DOT_Specific_DOT_Framework_DOT_SynthesisFramework_WRAPPED.
Module SynthesisFramework.
Import Crypto.Specific.Framework.ArithmeticSynthesis.BasePackage.
Import Crypto.Specific.Framework.ArithmeticSynthesis.DefaultsPackage.
Import Crypto.Specific.Framework.ArithmeticSynthesis.FreezePackage.
Import Crypto.Specific.Framework.ArithmeticSynthesis.KaratsubaPackage.
Import Crypto.Specific.Framework.ArithmeticSynthesis.LadderstepPackage.
Import Crypto.Specific.Framework.ArithmeticSynthesis.MontgomeryPackage.
Import Crypto.Specific.Framework.CurveParametersPackage.
Import Crypto.Specific.Framework.ReificationTypesPackage.
Import Crypto.Specific.Framework.MontgomeryReificationTypesPackage.
Import Crypto.Specific.Framework.Packages.
Import Crypto.Arithmetic.Core.
Import Crypto.Arithmetic.PrimeFieldTheorems.
Import Crypto.Util.BoundedWord.
Import Crypto.Util.TagList.
Import Crypto.Util.Tactics.DestructHead.
Import Crypto.Specific.Framework.IntegrationTestTemporaryMiscCommon.
Import Crypto.Compilers.Z.Bounds.Pipeline.

Module Export Exports.
  Export Coq.Classes.Equivalence Coq.Classes.RelationClasses Coq.Classes.Morphisms Coq.Classes.Morphisms_Prop.

  Export Crypto.Util.Decidable.

  Module Export TupleInstances.
    Import Crypto.Util.Tuple.
    Global Existing Instance Reflexive_fieldwise' | 5.
    Global Existing Instance Symmetric_fieldwise' | 5.
    Global Existing Instance Transitive_fieldwise' | 5.
    Global Existing Instance Equivalence_fieldwise'.
    Global Existing Instance Reflexive_fieldwise | 5.
    Global Existing Instance Symmetric_fieldwise | 5.
    Global Existing Instance Transitive_fieldwise | 5.
    Global Existing Instance Equivalence_fieldwise.
    Global Existing Instance dec_fieldwise' | 10.
    Global Existing Instance dec_fieldwise | 10.
    Global Existing Instance dec_eq' | 10.
    Global Existing Instance dec_eq | 10.
    Global Existing Instance map'_Proper | 10.
    Global Existing Instance map_Proper | 10.
    Global Existing Instances
           fieldwise'_Proper_gen
           fieldwise_Proper_gen
           fieldwise'_Proper_gen_eq
           fieldwise_Proper_gen_eq
           fieldwise'_Proper
           fieldwise_Proper
           fieldwise'_Proper_iff
           fieldwise_Proper_iff
           fieldwise'_Proper_flip_impl
           fieldwise_Proper_flip_impl
    | 10.
  End TupleInstances.
  Export ModularArithmeticTheorems.F.Instances.
  Export Field.Hints.
  Export Pipeline.Exports.
  Export ArithmeticSynthesis.Defaults.Exports.
  Export ArithmeticSynthesis.Freeze.Exports.
End Exports.

Module Type PrePackage := PrePackage.
Module Tag.
  Notation Context := Tag.Context (only parsing).
End Tag.

Module Export MakeSynthesisTactics.
  Ltac add_Synthesis_package pkg curve extra_prove_mul_eq extra_prove_square_eq :=
    let CP := get_fill_CurveParameters curve in
    let P_extra_prove_mul_eq := extra_prove_mul_eq in
    let P_extra_prove_square_eq := extra_prove_square_eq in
    let pkg := Tag.local_update pkg TAG.CP CP in
    let pkg := add_CurveParameters_package pkg in
    let pkg := Tag.strip_subst_local pkg in
    let pkg := add_Base_package pkg in
    let pkg := add_ReificationTypes_package pkg in
    let pkg := add_Karatsuba_package pkg in
    let pkg := add_Montgomery_package pkg in
    let pkg := add_MontgomeryReificationTypes_package pkg in

    let pkg := add_Freeze_package pkg in

    let pkg := add_Defaults_package pkg P_extra_prove_mul_eq P_extra_prove_square_eq in

    let pkg := add_Ladderstep_package pkg in
    pkg.

  Ltac get_Synthesis_package curve extra_prove_mul_eq extra_prove_square_eq :=
    let pkg := constr:(Tag.empty) in
    add_Synthesis_package pkg curve extra_prove_mul_eq extra_prove_square_eq.

  Ltac make_Synthesis_package curve extra_prove_mul_eq extra_prove_square_eq :=
    let pkg := get_Synthesis_package curve extra_prove_mul_eq extra_prove_square_eq in
    exact pkg.
End MakeSynthesisTactics.

Module PackageSynthesis (PKG : PrePackage).
  Module CP := MakeCurveParametersPackage PKG.
  Module BP := MakeBasePackage PKG.
  Module DP := MakeDefaultsPackage PKG.
  Module RP := MakeReificationTypesPackage PKG.
  Module FP := MakeFreezePackage PKG.
  Module LP := MakeLadderstepPackage PKG.
  Module KP := MakeKaratsubaPackage PKG.
  Module MP := MakeMontgomeryPackage PKG.
  Module MRP := MakeMontgomeryReificationTypesPackage PKG.
  Include CP.
  Include BP.
  Include DP.
  Include RP.
  Include FP.
  Include LP.
  Include KP.
  Include MP.
  Include MRP.

  Ltac synthesize do_rewrite get_op_sig :=
    let op_sig := get_op_sig () in
    let allowable_bit_widths := get_allowable_bit_widths () in
    start_preglue;
    [ do_rewrite op_sig; cbv_runtime
    | .. ];
    fin_preglue;
    refine_reflectively_gen allowable_bit_widths default.
  Ltac synthesize_with_carry do_rewrite get_op_sig :=
    let carry_sig := get_carry_sig () in
    synthesize ltac:(fun op_sig => do_rewrite op_sig carry_sig) get_op_sig.
  Ltac synthesize_narg get_op_sig :=
    synthesize do_rewrite_with_sig get_op_sig.
  Ltac synthesize_2arg_with_carry get_op_sig :=
    synthesize_with_carry do_rewrite_with_2sig_add_carry get_op_sig.
  Ltac synthesize_1arg_with_carry get_op_sig :=
    synthesize_with_carry do_rewrite_with_1sig_add_carry get_op_sig.

  Ltac synthesize_montgomery get_op_sig get_op_bounded :=
    let phi := get_phi1_for_preglue () in
    let op_sig := get_op_sig () in
    let op_bounded := get_op_bounded () in
    let allowable_bit_widths := get_allowable_bit_widths () in
    let do_red _ :=
        lazymatch (eval cbv [phi] in phi) with
        | (fun x => ?montgomery_to_F (?meval (?feBW_of_feBW_small _)))
          => cbv [feBW_of_feBW_small meval]
        end in
    start_preglue;
    do_red ();
    [ do_rewrite_with_sig_by op_sig op_sig_side_conditions_t;
      cbv_runtime
    | .. ];
    fin_preglue;
    factor_out_bounds_and_strip_eval op_bounded op_sig_side_conditions_t;
    refine_reflectively_gen allowable_bit_widths anf.

  Ltac synthesize_narg_choice_gen synthesize get_op_sig get_op_bounded :=
    let montgomery := get_montgomery () in
    lazymatch (eval vm_compute in montgomery) with
    | true => synthesize_montgomery get_op_sig get_op_bounded
    | false => synthesize get_op_sig
    end.
  Ltac synthesize_narg_choice get_op_sig get_op_bounded :=
    synthesize_narg_choice_gen synthesize_narg get_op_sig get_op_bounded.
  Ltac synthesize_2arg_choice_with_carry get_op_sig get_op_bounded :=
    synthesize_narg_choice_gen synthesize_2arg_with_carry get_op_sig get_op_bounded.
  Ltac synthesize_1arg_choice_with_carry get_op_sig get_op_bounded :=
    synthesize_narg_choice_gen synthesize_1arg_with_carry get_op_sig get_op_bounded.

  Ltac synthesize_carry_mul _ := synthesize_2arg_choice_with_carry get_mul_sig get_mul_bounded.
  Ltac synthesize_carry_add _ := synthesize_2arg_choice_with_carry get_add_sig get_add_bounded.
  Ltac synthesize_carry_sub _ := synthesize_2arg_choice_with_carry get_sub_sig get_sub_bounded.
  Ltac synthesize_carry_opp _ := synthesize_1arg_choice_with_carry get_opp_sig get_opp_bounded.
  Ltac synthesize_carry_square _ := synthesize_1arg_with_carry get_square_sig.
  Ltac synthesize_nocarry_mul _ := synthesize_narg_choice get_mul_sig get_mul_bounded.
  Ltac synthesize_add _ := synthesize_narg_choice get_add_sig get_add_bounded.
  Ltac synthesize_sub _ := synthesize_narg_choice get_sub_sig get_sub_bounded.
  Ltac synthesize_opp _ := synthesize_narg_choice get_opp_sig get_opp_bounded.
  Ltac synthesize_carry _ := synthesize_narg_choice get_carry_sig get_carry_bounded.
  Ltac synthesize_nocarry_square _ := synthesize_narg get_square_sig.
  Ltac synthesize_mul _ := synthesize_carry_mul ().
  Ltac synthesize_square _ := synthesize_carry_square ().
  Ltac synthesize_freeze _ :=
    let freeze_sig := get_freeze_sig () in
    let feBW_tight_bounded := get_feBW_tight_bounded () in
    let freeze_allowable_bit_widths := get_freeze_allowable_bit_widths () in
    start_preglue;
    [ do_rewrite_with_sig_by freeze_sig ltac:(fun _ => apply feBW_tight_bounded); cbv_runtime
    | .. ];
    fin_preglue;
    refine_reflectively_gen freeze_allowable_bit_widths anf.
  Ltac synthesize_xzladderstep _ :=
    let Mxzladderstep_sig := get_Mxzladderstep_sig () in
    let a24_sig := get_a24_sig () in
    let allowable_bit_widths := get_allowable_bit_widths () in
    start_preglue;
    [ unmap_map_tuple ();
      do_rewrite_with_sig_1arg Mxzladderstep_sig;
      cbv [Mxzladderstep XZ.M.xzladderstep a24_sig]; cbn [proj1_sig];
      do_set_sigs ();
      cbv_runtime
    | .. ];
    finish_conjoined_preglue ();
    refine_reflectively_gen allowable_bit_widths default.
  Ltac synthesize_nonzero _ :=
    let op_sig := get_nonzero_sig () in
    let allowable_bit_widths := get_allowable_bit_widths () in
    nonzero_preglue op_sig ltac:(fun _ => cbv_runtime);
    refine_reflectively_gen allowable_bit_widths anf.
End PackageSynthesis.

End SynthesisFramework.

End Crypto_DOT_Specific_DOT_Framework_DOT_SynthesisFramework_WRAPPED.
Module Export Crypto_DOT_Specific_DOT_Framework_DOT_SynthesisFramework.
Module Export Crypto.
Module Export Specific.
Module Export Framework.
Module SynthesisFramework.
Include Crypto_DOT_Specific_DOT_Framework_DOT_SynthesisFramework_WRAPPED.SynthesisFramework.
End SynthesisFramework.

End Framework.

End Specific.

End Crypto.

End Crypto_DOT_Specific_DOT_Framework_DOT_SynthesisFramework.
Module Crypto_DOT_Specific_DOT_NISTP256_DOT_AMD128_DOT_CurveParameters_WRAPPED.
Module CurveParameters.
Import Crypto.Specific.Framework.RawCurveParameters.
Import Crypto.Util.LetIn.

Definition curve : CurveParameters :=
  {|
    sz := 2%nat;
    base := 128;
    bitwidth := 128;
    s := 2^256;
    c := [(1, 1); (2^96, -1); (2^192, -1); (2^224, 1)];
    carry_chains := None;

    a24 := None;
    coef_div_modulus := None;

    goldilocks := None;
    karatsuba := None;
    montgomery := true;
    freeze := Some false;
    ladderstep := false;

    mul_code := None;

    square_code := None;

    upper_bound_of_exponent_loose := None;
    upper_bound_of_exponent_tight := None;
    allowable_bit_widths := None;
    freeze_extra_allowable_bit_widths := None;
    modinv_fuel := None
  |}.

Ltac extra_prove_mul_eq _ := idtac.
Ltac extra_prove_square_eq _ := idtac.

End CurveParameters.

End Crypto_DOT_Specific_DOT_NISTP256_DOT_AMD128_DOT_CurveParameters_WRAPPED.
Module Export Crypto_DOT_Specific_DOT_NISTP256_DOT_AMD128_DOT_CurveParameters.
Module Export Crypto.
Module Export Specific.
Module Export NISTP256.
Module Export AMD128.
Module CurveParameters.
Include Crypto_DOT_Specific_DOT_NISTP256_DOT_AMD128_DOT_CurveParameters_WRAPPED.CurveParameters.
End CurveParameters.

End AMD128.

End NISTP256.

End Specific.

End Crypto.

End Crypto_DOT_Specific_DOT_NISTP256_DOT_AMD128_DOT_CurveParameters.
Import Crypto.Specific.Framework.SynthesisFramework.
Export SynthesisFramework.Exports.
Import Crypto.Specific.NISTP256.AMD128.CurveParameters.

Module P <: PrePackage.
  Definition package : Tag.Context.
  Proof.
make_Synthesis_package curve extra_prove_mul_eq extra_prove_square_eq.
