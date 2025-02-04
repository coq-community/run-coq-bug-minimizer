
(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "+implicit-core-hint-db,+implicits-in-term,+non-reversible-notation,+deprecated-intros-until-0,+deprecated-focus,+unused-intro-pattern,+variable-collision,+unexpected-implicit-declaration,+omega-is-deprecated,+deprecated-instantiate-syntax,+non-recursive,+undeclared-scope,+deprecated-hint-rewrite-without-locality,+deprecated-hint-without-locality,+deprecated-instance-without-locality,+deprecated-typeclasses-transparency-without-locality,unsupported-attributes" "-w" "-notation-overridden,-deprecated-hint-constr,-fragile-hint-constr,-native-compiler-disabled,-ambiguous-paths,-masking-absolute-name" "-w" "-deprecated-native-compiler-option" "-native-compiler" "no" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/fiat_crypto/src" "Crypto" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq//user-contrib/Bignums" "Bignums" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq//user-contrib/Coqprime" "Coqprime" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq//user-contrib/Kami" "Kami" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq//user-contrib/Ltac2" "Ltac2" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq//user-contrib/Rewriter" "Rewriter" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq//user-contrib/Rupicola" "Rupicola" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq//user-contrib/Stdlib" "Stdlib" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq//user-contrib/bedrock2" "bedrock2" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq//user-contrib/bedrock2Examples" "bedrock2Examples" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq//user-contrib/compiler" "compiler" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq//user-contrib/coqutil" "coqutil" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq//user-contrib/riscv" "riscv" "-top" "Top.bug_01") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 3483 lines to 2115 lines, then from 2115 lines to 1785 lines, then from 1787 lines to 1694 lines *)
(* coqc version None
   coqtop version None
   Expected coqc runtime on this file: 60.421 sec *)












Require Corelib.Init.Ltac.
Require Stdlib.Classes.DecidableClass.
Require Stdlib.Bool.Bool.
Require Corelib.Classes.RelationClasses.
Require Stdlib.Classes.RelationClasses.
Require Corelib.Classes.Morphisms.
Require Stdlib.Classes.Morphisms.
Require Corelib.Setoids.Setoid.
Require Stdlib.Setoids.Setoid.
Require Stdlib.Structures.Equalities.
Require Corelib.Relations.Relation_Definitions.
Require Stdlib.Relations.Relation_Definitions.
Require Stdlib.Relations.Relation_Operators.
Require Stdlib.Relations.Operators_Properties.
Require Stdlib.Relations.Relations.
Require Stdlib.Structures.Orders.
Require Corelib.Classes.Morphisms_Prop.
Require Stdlib.Classes.Morphisms_Prop.
Require Stdlib.Numbers.NumPrelude.
Require Corelib.Program.Basics.
Require Stdlib.Program.Basics.
Require Stdlib.Structures.OrdersTac.
Require Stdlib.Structures.OrdersFacts.
Require Stdlib.Structures.GenericMinMax.
Require Stdlib.Numbers.NatInt.NZAxioms.
Require Stdlib.Numbers.NatInt.NZBase.
Require Stdlib.Numbers.NatInt.NZAdd.
Require Stdlib.Numbers.NatInt.NZMul.
Require Stdlib.Logic.Decidable.
Require Stdlib.Numbers.NatInt.NZOrder.
Require Stdlib.Numbers.NatInt.NZAddOrder.
Require Stdlib.Numbers.NatInt.NZMulOrder.
Require Stdlib.Numbers.NatInt.NZParity.
Require Stdlib.Numbers.NatInt.NZPow.
Require Stdlib.Numbers.NatInt.NZSqrt.
Require Stdlib.Numbers.NatInt.NZLog.
Require Stdlib.Numbers.NatInt.NZDiv.
Require Stdlib.Numbers.NatInt.NZGcd.
Require Stdlib.Numbers.NatInt.NZBits.
Require Stdlib.Numbers.Natural.Abstract.NAxioms.
Require Stdlib.Numbers.Natural.Abstract.NBase.
Require Stdlib.Numbers.Natural.Abstract.NAdd.
Require Stdlib.Numbers.Natural.Abstract.NOrder.
Require Stdlib.Numbers.Natural.Abstract.NAddOrder.
Require Stdlib.Numbers.Natural.Abstract.NMulOrder.
Require Stdlib.Numbers.Natural.Abstract.NSub.
Require Stdlib.Numbers.Natural.Abstract.NMaxMin.
Require Stdlib.Numbers.Natural.Abstract.NParity.
Require Stdlib.Numbers.Natural.Abstract.NPow.
Require Stdlib.Numbers.Natural.Abstract.NSqrt.
Require Stdlib.Numbers.Natural.Abstract.NLog.
Require Stdlib.Numbers.Natural.Abstract.NDiv.
Require Stdlib.Numbers.Natural.Abstract.NDiv0.
Require Stdlib.Numbers.Natural.Abstract.NGcd.
Require Stdlib.Numbers.Natural.Abstract.NLcm.
Require Stdlib.Numbers.Natural.Abstract.NLcm0.
Require Stdlib.Numbers.Natural.Abstract.NBits.
Require Stdlib.Numbers.Natural.Abstract.NProperties.
Require Stdlib.Arith.PeanoNat.
Require Corelib.Lists.ListDef.
Require Stdlib.Lists.ListDef.
Require Stdlib.Lists.List.
Require Stdlib.Arith.Compare_dec.
Require Stdlib.Arith.EqNat.
Require Stdlib.Lists.ListDec.
Require Stdlib.Arith.Factorial.
Require Stdlib.Arith.Between.
Require Stdlib.Logic.EqdepFacts.
Require Stdlib.Logic.Eqdep_dec.
Require Stdlib.Arith.Peano_dec.
Require Stdlib.Arith.Wf_nat.
Require Stdlib.Arith.Arith_base.
Require Stdlib.Vectors.Fin.
Require Stdlib.Vectors.FinFun.
Require Stdlib.Sorting.Permutation.
Require Corelib.Numbers.BinNums.
Require Stdlib.Numbers.BinNums.
Require Corelib.BinNums.PosDef.
Require Stdlib.BinNums.PosDef.
Require Stdlib.PArith.BinPosDef.
Require Stdlib.PArith.BinPos.
Require Corelib.BinNums.NatDef.
Require Stdlib.BinNums.NatDef.
Require Stdlib.NArith.BinNatDef.
Require Stdlib.NArith.BinNat.
Require Stdlib.PArith.Pnat.
Require Stdlib.NArith.Nnat.
Require Stdlib.setoid_ring.Ring_theory.
Require Stdlib.setoid_ring.BinList.
Require Stdlib.Numbers.Integer.Abstract.ZAxioms.
Require Stdlib.Numbers.Integer.Abstract.ZBase.
Require Stdlib.Numbers.Integer.Abstract.ZAdd.
Require Stdlib.Numbers.Integer.Abstract.ZMul.
Require Stdlib.Numbers.Integer.Abstract.ZLt.
Require Stdlib.Numbers.Integer.Abstract.ZAddOrder.
Require Stdlib.Numbers.Integer.Abstract.ZMulOrder.
Require Stdlib.Numbers.Integer.Abstract.ZMaxMin.
Require Stdlib.Numbers.Integer.Abstract.ZSgnAbs.
Require Stdlib.Numbers.Integer.Abstract.ZParity.
Require Stdlib.Numbers.Integer.Abstract.ZPow.
Require Stdlib.Numbers.Integer.Abstract.ZDivTrunc.
Require Stdlib.Numbers.Integer.Abstract.ZDivFloor.
Require Stdlib.Numbers.Integer.Abstract.ZGcd.
Require Stdlib.Numbers.Integer.Abstract.ZLcm.
Require Stdlib.Numbers.Integer.Abstract.ZBits.
Require Stdlib.Numbers.Integer.Abstract.ZProperties.
Require Corelib.BinNums.IntDef.
Require Stdlib.BinNums.IntDef.
Require Stdlib.ZArith.BinIntDef.
Require Stdlib.ZArith.BinInt.
Require Stdlib.setoid_ring.Ring_polynom.
Require Stdlib.Lists.ListTactics.
Require Stdlib.setoid_ring.InitialRing.
Require Stdlib.setoid_ring.Ring_tac.
Require Stdlib.setoid_ring.Ring_base.
Require Stdlib.setoid_ring.Ring.
Require Stdlib.setoid_ring.ArithRing.
Require Stdlib.Arith.Arith.
Require Stdlib.ZArith.Znat.
Require Stdlib.micromega.ZifyClasses.
Require Stdlib.ZArith.Zeven.
Require Stdlib.micromega.ZifyInst.
Require Stdlib.micromega.Zify.
Require Stdlib.omega.PreOmega.
Require Stdlib.micromega.OrderedRing.
Require Stdlib.NArith.Ndiv_def.
Require Stdlib.NArith.Nsqrt_def.
Require Stdlib.NArith.Ngcd_def.
Require Stdlib.NArith.NArith.
Require Stdlib.setoid_ring.NArithRing.
Require Stdlib.micromega.Env.
Require Stdlib.micromega.EnvRing.
Require Stdlib.micromega.Refl.
Require Stdlib.micromega.Tauto.
Require Stdlib.micromega.RingMicromega.
Require Stdlib.ZArith.Zpow_def.
Require Stdlib.setoid_ring.ZArithRing.
Require Stdlib.micromega.ZCoeff.
Require Stdlib.ZArith.Zcompare.
Require Stdlib.ZArith.Zorder.
Require Stdlib.ZArith.Zmisc.
Require Stdlib.ZArith.Wf_Z.
Require Corelib.Init.Sumbool.
Require Stdlib.Init.Sumbool.
Require Stdlib.ZArith.ZArith_dec.
Require Stdlib.ZArith.Zbool.
Require Stdlib.ZArith.Zabs.
Require Stdlib.ZArith.Zcomplements.
Require Stdlib.ZArith.Zdiv.
Require Stdlib.ZArith.Zminmax.
Require Stdlib.ZArith.Zmin.
Require Stdlib.ZArith.Zmax.
Require Stdlib.ZArith.auxiliary.
Require Stdlib.ZArith.Zhints.
Require Stdlib.ZArith.ZArith_base.
Require Stdlib.ZArith.Znumtheory.
Require Stdlib.micromega.VarMap.
Require Stdlib.micromega.ZMicromega.
Require Stdlib.micromega.DeclConstantZ.
Require Stdlib.micromega.Lia.
Require Stdlib.omega.OmegaLemmas.
Require Stdlib.micromega.ZArith_hints.
Require Stdlib.ZArith.Zpower.
Require Stdlib.ZArith.Zdiv_facts.
Require Stdlib.PArith.POrderedType.
Require Stdlib.PArith.PArith.
Require Stdlib.btauto.Algebra.
Require Stdlib.btauto.Reflect.
Require Stdlib.btauto.Btauto.
Require Stdlib.ZArith.Zbitwise.
Require Stdlib.ZArith.ZArith.
Require Crypto.Util.GlobalSettings.
Require Crypto.Util.FixCoqMistakes.
Require Crypto.Util.Tactics.Head.
Require Crypto.Util.Tactics.BreakMatch.
Require Crypto.Util.Tactics.DestructHyps.
Require Crypto.Util.Tactics.DestructHead.
Require Crypto.Util.Notations.
Require Crypto.Util.Option.
Require Crypto.Util.IffT.
Require Crypto.Util.Isomorphism.
Require Crypto.Util.HProp.
Require Crypto.Util.Equality.
Require Crypto.Util.Prod.
Require Crypto.Util.Tactics.SpecializeBy.
Require Crypto.Util.Sigma.
Require Crypto.Util.Decidable.
Require Stdlib.Sets.Relations_1.
Require Stdlib.Sorting.Sorted.
Require Stdlib.Sorting.SetoidList.
Require Crypto.Util.NatUtil.
Require Crypto.Util.Pointed.
Require Crypto.Util.Tactics.Test.
Require Crypto.Util.Tactics.Not.
Require Crypto.Util.Tactics.DoWithHyp.
Require Crypto.Util.Tactics.RewriteHyp.
Require Crypto.Util.Tactics.ConstrFail.
Require Crypto.Util.Tactics.SplitInContext.
Require Crypto.Util.ListUtil.
Require Crypto.Util.Tuple.
Require Corelib.Classes.CMorphisms.
Require Stdlib.Classes.CMorphisms.
Require Corelib.Init.Byte.
Require Stdlib.Init.Byte.
Require Stdlib.Strings.Byte.
Require Stdlib.Strings.Ascii.
Require Stdlib.Strings.String.
Require Crypto.Util.ListUtil.SetoidList.
Require Crypto.Util.Tactics.Contains.
Require Crypto.Util.Tactics.SetoidSubst.
Require Crypto.Util.Sum.
Require Crypto.Util.Comparison.
Require Crypto.Util.PrimitiveProd.
Require Crypto.Util.Bool.Reflect.
Require Crypto.Util.ZRange.
Require Crypto.Util.ZUtil.Notations.
Require Crypto.Util.Tactics.GetGoal.
Require Rewriter.Util.GlobalSettings.
Require Rewriter.Util.FixCoqMistakes.
Require Rewriter.Util.Tactics.GetGoal.
Require Rewriter.Util.Notations.
Require Rewriter.Util.LetIn.
Require Crypto.Util.LetIn.
Require Crypto.Util.ZUtil.Definitions.
Require Crypto.Util.ZRange.Operations.
Require Rewriter.Util.Bool.
Require Rewriter.Util.Tactics.Head.
Require Rewriter.Util.Tactics.BreakMatch.
Require Rewriter.Util.Tactics.DestructHyps.
Require Rewriter.Util.Tactics.DestructHead.
Require Rewriter.Util.Option.
Require Rewriter.Util.IffT.
Require Rewriter.Util.Isomorphism.
Require Rewriter.Util.HProp.
Require Rewriter.Util.Equality.
Require Rewriter.Util.Prod.
Require Rewriter.Util.NatUtil.
Require Rewriter.Util.Pointed.
Require Rewriter.Util.Sigma.
Require Rewriter.Util.Decidable.
Require Rewriter.Util.Tactics.SpecializeBy.
Require Rewriter.Util.Tactics.Test.
Require Rewriter.Util.Tactics.Not.
Require Rewriter.Util.Tactics.DoWithHyp.
Require Rewriter.Util.Tactics.RewriteHyp.
Require Rewriter.Util.Tactics.ConstrFail.
Require Rewriter.Util.Tactics.SplitInContext.
Require Rewriter.Util.ListUtil.
Require Ltac2.Init.
Require Rewriter.Util.PrimitiveProd.
Require Rewriter.Util.PrimitiveHList.
Require Rewriter.Util.InductiveHList.
Require Rewriter.Language.PreCommon.
Require Rewriter.Language.Pre.
Require Crypto.Util.PrimitiveHList.
Require Crypto.Language.PreExtra.
Require Ltac2.Int.
Require Ltac2.Message.
Require Ltac2.Control.
Require Ltac2.Bool.
Require Ltac2.Array.
Require Ltac2.Char.
Require Ltac2.Constant.
Require Ltac2.Ind.
Require Ltac2.Constr.
Require Ltac2.Constructor.
Require Ltac2.Std.
Require Ltac2.Env.
Require Ltac2.Evar.
Require Ltac2.Float.
Require Ltac2.List.
Require Ltac2.Fresh.
Require Ltac2.Ident.
Require Ltac2.Ref.
Require Ltac2.Lazy.
Require Ltac2.Ltac1.
Require Ltac2.Meta.
Require Ltac2.Option.
Require Ltac2.Pattern.
Require Ltac2.Printf.
Require Ltac2.Proj.
Require Ltac2.RedFlags.
Require Ltac2.String.
Require Ltac2.Uint63.
Require Ltac2.FSet.
Require Ltac2.FMap.
Require Ltac2.TransparentState.
Require Ltac2.Unification.
Require Ltac2.Notations.
Require Ltac2.Ltac2.
Require Stdlib.Structures.OrderedType.
Require Stdlib.NArith.Ndec.
Require Stdlib.Structures.OrderedTypeEx.
Require Stdlib.Structures.DecidableType.
Require Stdlib.FSets.FMapInterface.
Require Stdlib.FSets.FMapPositive.
Require Rewriter.Util.OptionList.
Require Rewriter.Util.CPSNotations.
Require Rewriter.Util.ListUtil.SetoidList.
Require Rewriter.Util.Tactics.Contains.
Require Rewriter.Util.Tactics.SetoidSubst.
Require Rewriter.Util.Sum.
Require Rewriter.Util.Comparison.
Require Rewriter.Util.Bool.Reflect.
Require Rewriter.Language.Language.
Require Rewriter.Language.UnderLets.
Require Rewriter.Language.UnderLetsCacheProofs.
Require Rewriter.Util.Tactics.RunTacticAsConstr.
Require Rewriter.Util.Tactics.DebugPrint.
Require Rewriter.Util.Tactics2.List.
Require Rewriter.Util.Tactics2.Ltac1.
Require Rewriter.Util.Tactics2.Message.
Require Rewriter.Util.Tactics2.Ident.
Require Rewriter.Util.Tactics2.Char.
Require Rewriter.Util.Tactics2.String.
Require Rewriter.Util.Tactics2.Array.
Require Rewriter.Util.Tactics2.Proj.
Require Rewriter.Util.Tactics2.Option.
Require Rewriter.Util.Tactics2.Iterate.
Require Rewriter.Util.plugins.Ltac2Extra.
Require Rewriter.Util.Tactics2.Constr.
Require Rewriter.Util.Tactics2.DestEvar.
Require Rewriter.Util.Tactics2.DestCase.
Require Rewriter.Util.Tactics2.InstantiateEvar.
Require Rewriter.Util.Tactics2.Constr.Unsafe.MakeAbbreviations.
Require Rewriter.Util.Tactics2.FixNotationsForPerformance.
Require Rewriter.Language.Reify.
Require Crypto.Language.IdentifierParameters.
Require Rewriter.Util.Tactics.FindHyp.
Require Rewriter.Util.Tactics.UniquePose.
Require Rewriter.Util.Tactics.SpecializeAllWays.
Require Rewriter.Language.Inversion.
Require Rewriter.Language.IdentifiersBasicLibrary.
Require Rewriter.Util.TypeList.
Require Rewriter.Util.Tactics.HeadUnderBinders.
Require Rewriter.Util.Tactics.PrintContext.
Require Rewriter.Util.Tactics.PrintGoal.
Require Rewriter.Util.Tactics.EvarNormalize.
Require Rewriter.Util.Tactics.ClearFree.
Require Rewriter.Util.Tactics.CacheTerm.
Require Rewriter.Util.Tactics2.Notations.
Require Rewriter.Language.IdentifiersBasicGenerate.
Require Rewriter.Language.PreLemmas.
Require Stdlib.Structures.BoolOrder.
Require Stdlib.Classes.RelationPairs.
Require Stdlib.Structures.EqualitiesFacts.
Require Stdlib.Structures.OrdersEx.
Require Stdlib.MSets.MSetInterface.
Require Stdlib.MSets.MSetPositive.
Require Corelib.Program.Tactics.
Require Stdlib.Program.Tactics.
Require Rewriter.Util.ListUtil.Forall.
Require Rewriter.Util.Logic.ProdForall.
Require Rewriter.Language.Wf.
Require Rewriter.Language.UnderLetsProofs.
Require Corelib.derive.Derive.
Require Stdlib.derive.Derive.
Require Rewriter.Util.PrimitiveSigma.
Require Rewriter.Language.IdentifiersLibrary.
Require Stdlib.Structures.DecidableTypeEx.
Require Stdlib.MSets.MSetFacts.
Require Rewriter.Util.Logic.ExistsEqAnd.
Require Rewriter.Util.MSetPositive.Facts.
Require Rewriter.Language.IdentifiersLibraryProofs.
Require Rewriter.Rewriter.Rewriter.
Require Rewriter.Util.Tactics.CPSId.
Require Rewriter.Util.Bool.Equality.
Require Rewriter.Util.FMapPositive.Equality.
Require Rewriter.Util.MSetPositive.Equality.
Require Rewriter.Util.Sigma.Related.
Require Rewriter.Rewriter.ProofsCommon.
Require Rewriter.Util.Tactics.WarnIfGoalsRemain.
Require Rewriter.Language.IdentifiersGenerate.
Require Rewriter.Language.IdentifiersGenerateProofs.
Require Rewriter.Util.Tactics2.Head.
Require Rewriter.Util.Tactics2.HeadReference.
Require Rewriter.Util.Tactics2.DecomposeLambda.
Require Rewriter.Util.Tactics2.ReplaceByPattern.
Require Rewriter.Util.Tactics2.InFreshContext.
Require Rewriter.Rewriter.Reify.
Require Rewriter.Rewriter.ProofsCommonTactics.
Require Rewriter.Rewriter.Wf.
Require Rewriter.Util.Tactics.SetEvars.
Require Rewriter.Util.Tactics.SubstEvars.
Require Rewriter.Util.Tactics.TransparentAssert.
Require Rewriter.Rewriter.InterpProofs.
Require Rewriter.Rewriter.AllTactics.
Require Rewriter.Util.plugins.StrategyTactic.
Require Rewriter.Util.plugins.RewriterBuildRegistryImports.
Require Rewriter.Util.plugins.RewriterBuildRegistry.
Require Rewriter.Util.plugins.RewriterBuild.
Require Crypto.Util.ListUtil.Filter.
Require Crypto.Language.IdentifiersBasicGENERATED.
Require Crypto.Util.CPSNotations.
Require Crypto.Util.Tactics.RunTacticAsConstr.
Require Crypto.Util.Tactics.DebugPrint.
Require Crypto.Language.APINotations.
Require Crypto.Language.API.
Require Crypto.Util.Bool.
Require Crypto.Util.ListUtil.FoldBool.
Require Crypto.Util.ListUtil.NthExt.
Require Crypto.Util.OptionList.
Require Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Crypto.AbstractInterpretation.ZRange.
Require Crypto.Util.ErrorT.
Require Crypto.Assembly.Syntax.
Require Crypto.Assembly.Equality.
Require Crypto.Util.Strings.Ascii.
Require Crypto.Util.Strings.String.
Require Crypto.Util.Strings.Parse.Common.
Require Stdlib.QArith.QArith_base.
Require Stdlib.setoid_ring.Field_theory.
Require Stdlib.setoid_ring.Field_tac.
Require Stdlib.setoid_ring.Field.
Require Stdlib.QArith.Qfield.
Require Stdlib.QArith.Qring.
Require Stdlib.QArith.Qreduction.
Require Stdlib.QArith.QArith.
Require Stdlib.Strings.BinaryString.
Require Stdlib.Strings.OctalString.
Require Stdlib.Strings.HexString.
Require Corelib.Init.Decimal.
Require Stdlib.Init.Decimal.
Require Stdlib.Numbers.DecimalString.
Require Stdlib.Numbers.DecimalFacts.
Require Stdlib.Numbers.DecimalPos.
Require Stdlib.Numbers.DecimalN.
Require Stdlib.Numbers.DecimalZ.
Require Crypto.Util.Strings.Decimal.
Require Crypto.Util.ListUtil.Partition.
Require Crypto.Util.ListUtil.StdlibCompat.
Require Crypto.Util.ListUtil.GroupAllBy.
Require Crypto.Util.Strings.ParseArithmetic.
Require Crypto.Util.Level.
Require Crypto.Util.Strings.Show.
Require coqutil.Tactics.ident_to_string.
Require coqutil.Ltac2Lib.Pervasives.
Require coqutil.Ltac2Lib.List.
Require coqutil.Ltac2Lib.Char.
Require coqutil.Ltac2Lib.String.
Require coqutil.Tactics.reference_to_string.
Require Crypto.Util.Strings.Show.Enum.
Require Crypto.Util.Listable.
Require Crypto.Assembly.Parse.
Require Stdlib.FSets.FMapFacts.
Require Stdlib.micromega.QMicromega.
Require Stdlib.micromega.DeclConstant.
Require Stdlib.micromega.Lqa.
Require Crypto.Util.ZUtil.Hints.Core.
Require Stdlib.ZArith.Zpow_facts.
Require Crypto.Util.ZUtil.ZSimplify.Core.
Require Crypto.Util.ZUtil.Modulo.PullPush.
Require Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Crypto.Util.ZUtil.Hints.ZArith.
Require Crypto.Util.ZUtil.Hints.Ztestbit.
Require Crypto.Util.ZUtil.Hints.PullPush.
Require Crypto.Util.ZUtil.Hints.
Require Crypto.Util.ZUtil.Lnot.
Require Crypto.Util.ZUtil.Tactics.CompareToSgn.
Require Crypto.Util.ZUtil.Div.Bootstrap.
Require Crypto.Util.ZUtil.Modulo.Bootstrap.
Require Crypto.Util.ZUtil.Tactics.DivModToQuotRem.
Require Crypto.Util.ZUtil.Le.
Require Crypto.Util.ZUtil.Pow.
Require Crypto.Util.ZUtil.Div.
Require Crypto.Util.ZUtil.Tactics.PrimeBound.
Require Crypto.Util.ZUtil.Tactics.ZeroBounds.
Require Crypto.Util.ZUtil.ZSimplify.Simple.
Require Crypto.Util.ZUtil.Log2.
Require Crypto.Util.Bool.LeCompat.
Require Crypto.Util.ZUtil.Testbit.
Require Crypto.Util.ZUtil.Land.
Require Crypto.Util.ZUtil.Land.Fold.
Require Crypto.Util.ZUtil.Pow2.
Require Crypto.Util.Tactics.FindHyp.
Require Crypto.Util.Tactics.UniquePose.
Require Crypto.Util.ZUtil.Ones.
Require Crypto.Util.Strings.Subscript.
Require Crypto.Util.Structures.Equalities.
Require Crypto.Util.Tactics.SpecializeAllWays.
Require Crypto.Util.Structures.Orders.
Require Crypto.Util.Structures.Equalities.Iso.
Require Crypto.Util.Structures.Equalities.Prod.
Require Crypto.Util.Structures.Equalities.Option.
Require Crypto.Util.Structures.Orders.Iso.
Require Crypto.Util.Structures.Orders.Prod.
Require Crypto.Util.Structures.Orders.Option.
Require Crypto.Util.Structures.Equalities.Sum.
Require Crypto.Util.Structures.Orders.Sum.
Require Crypto.Util.Structures.Equalities.Project.
Require Crypto.Util.Structures.Orders.Flip.
Require Crypto.Util.Structures.OrdersEx.
Require Crypto.Util.ListUtil.Concat.
Require Crypto.Util.ListUtil.FoldMap.
Require Crypto.Util.ListUtil.IndexOf.
Require Crypto.Util.ListUtil.Forall.
Require Crypto.Util.ListUtil.Permutation.
Require Crypto.Util.ListUtil.PermutationCompat.
Require Stdlib.Sorting.Mergesort.
Require Crypto.Util.NUtil.Sorting.
Require Crypto.Util.NUtil.Testbit.
Require Crypto.Util.Compose.
Require Crypto.Util.Logic.Forall.
Require Crypto.Util.Logic.Exists.
Require Crypto.Util.Logic.
Require Crypto.Util.Relations.
Require Crypto.Util.Unit.
Require Crypto.Util.Structures.Equalities.Unit.
Require Crypto.Util.Structures.Orders.Unit.
Require Crypto.Util.FSets.FMapInterface.
Require Crypto.Util.Tactics.Zeta1.
Require Corelib.ssr.ssreflect.
Require Stdlib.ssr.ssreflect.
Require Crypto.Util.Tactics.GeneralizeOverHoles.
Require Crypto.Util.Tactics.SpecializeUnderBindersBy.
Require Crypto.Util.Tactics.InHypUnderBindersDo.
Require Crypto.Util.FSets.FMapFacts.
Require Stdlib.Sorting.SetoidPermutation.
Require Crypto.Util.Sorting.Sorted.Proper.
Require Crypto.Util.FSets.FMapUnit.
Require Crypto.Util.FSets.FMapOption.
Require Crypto.Util.FSets.FMapIso.
Require Crypto.Util.FSets.FMapN.
Require Crypto.Util.ListUtil.SetoidListRev.
Require Crypto.Util.Tactics.RevertUntil.
Require Crypto.Assembly.EquivalenceProofs.
Require Crypto.Assembly.WithBedrock.SymbolicProofs.
Require bedrock2.Array.

Module Export AdmitTactic.
Module Import LocalFalse.
End LocalFalse.
End AdmitTactic.
Import Stdlib.Sorting.Permutation.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.ZArith.ZArith.
Import Crypto.Util.ErrorT.
Import Crypto.Assembly.Syntax.
Import Crypto.Assembly.Equivalence.
Import Crypto.Util.Option.
Import Crypto.Util.Prod.
Import Crypto.Util.Sum.
Import Crypto.Util.ListUtil.
Import Crypto.Util.ListUtil.Forall.
Import Crypto.Util.ListUtil.Filter.
Import Crypto.Util.Tactics.SpecializeBy.
Import Crypto.Util.Tactics.RevertUntil.
Import Crypto.Util.Tactics.UniquePose.
Import Crypto.Util.Tactics.SplitInContext.
Import Crypto.Util.Tactics.SetEvars.
Import Crypto.Util.Tactics.SubstEvars.
Import Crypto.Assembly.EquivalenceProofs.
Import Crypto.Assembly.WithBedrock.Semantics.
Import Crypto.Assembly.WithBedrock.SymbolicProofs.
Import Crypto.Assembly.Symbolic.
Import ListNotations.

Local Set Keyed Unification.
Import coqutil.Map.Interface.
Import bedrock2.Map.Separation.

Import bedrock2.Array.

Import coqutil.Word.LittleEndianList.
Import coqutil.Word.Interface.
Definition cell64 wa (v : Z) : Semantics.mem_state -> Prop :=
  Lift1Prop.ex1 (fun bs => sep (emp (
      length bs = 8%nat /\ v = le_combine bs))
                               (eq (OfListWord.map.of_list_word_at wa bs))).

Definition R_scalar_or_array {dereference_scalar:bool}
           (val : Z + list Z) (asm_val : Naive.word 64)
  := match val with
     | inr array_vals => array cell64 (word.of_Z 8) asm_val array_vals
     | inl scalar_val => if dereference_scalar
                         then cell64 asm_val scalar_val
                         else emp (word.unsigned asm_val = scalar_val)
     end.
Definition R_list_scalar_or_array_nolen {dereference_scalar:bool}
           (Z_vals : list (Z + list Z)) (asm_vals : list (Naive.word 64))
  := List.fold_right
       sep
       (emp True)
       (List.map
          (fun '(val, asm_val) => R_scalar_or_array (dereference_scalar:=dereference_scalar) val asm_val)
          (List.combine Z_vals asm_vals)).
Definition R_list_scalar_or_array {dereference_scalar:bool}
           (Z_vals : list (Z + list Z)) (asm_vals : list (Naive.word 64))
  := sep (emp (List.length Z_vals = List.length asm_vals))
         (R_list_scalar_or_array_nolen (dereference_scalar:=dereference_scalar) Z_vals asm_vals).
Definition get_asm_reg (m : Semantics.reg_state) (reg_available : list REG) : list Z.
exact (List.map (Semantics.get_reg m) reg_available).
Defined.
Definition R_runtime_input_mem
           {output_scalars_are_pointers:bool}
           (frame : Semantics.mem_state -> Prop)
           (output_types : type_spec) (runtime_inputs : list (Z + list Z))
           (stack_size : nat) (stack_base : Naive.word 64)
           (asm_arguments_out asm_arguments_in : list (Naive.word 64))
           (runtime_reg : list Z)
           (m : Semantics.mem_state)
  : Prop.
exact (exists (stack_placeholder_values : list Z) (output_placeholder_values : list (Z + list Z)),
    Forall (fun v : Z => (0 <= v < 2 ^ 64)%Z) stack_placeholder_values
    /\ stack_size = List.length stack_placeholder_values
    /\ Forall2 val_or_list_val_matches_spec output_placeholder_values output_types
    /\ Forall (fun v => match v with
                        | inl v => (0 <= v < 2^64)%Z
                        | inr vs => Forall (fun v => (0 <= v < 2^64)%Z) vs
                        end) output_placeholder_values
    /\
      Forall2
        (fun v1 v2 => match v1 with
                      | inl v => if output_scalars_are_pointers
                                 then True
                                 else v = v2
                      | inr _ => True
                      end)
        output_placeholder_values
        (firstn (length output_types) runtime_reg)
    /\ ((frame *
           R_list_scalar_or_array (dereference_scalar:=output_scalars_are_pointers) output_placeholder_values asm_arguments_out *
           R_list_scalar_or_array (dereference_scalar:=false) runtime_inputs asm_arguments_in *
           array cell64 (word.of_Z 8) stack_base stack_placeholder_values)%sep)
         m).
Defined.
Definition R_runtime_input
           {output_scalars_are_pointers:bool}
           (frame : Semantics.mem_state -> Prop)
           (output_types : type_spec) (runtime_inputs : list (Z + list Z))
           (stack_size : nat) (stack_base : Naive.word 64)
           (asm_pointer_arguments_out asm_pointer_arguments_in : list (Naive.word 64))
           (reg_available : list REG) (runtime_reg : list Z)
           (callee_saved_registers : list REG) (runtime_callee_saved_registers : list Z)
           (m : machine_state)
  : Prop.
exact (exists (asm_arguments_out asm_arguments_in : list (Naive.word 64)),
    Forall (fun v => (0 <= v < 2^64)%Z) (Tuple.to_list _ m.(machine_reg_state))
    /\ (Nat.min (List.length output_types + List.length runtime_inputs) (List.length reg_available) <= List.length runtime_reg)%nat
    /\ get_asm_reg m reg_available = runtime_reg
    /\ get_asm_reg m callee_saved_registers = runtime_callee_saved_registers
    /\ List.length asm_arguments_out = List.length output_types
    /\ List.map word.unsigned asm_arguments_out = List.firstn (List.length output_types) runtime_reg
    /\ List.map word.unsigned asm_arguments_in = List.firstn (List.length runtime_inputs) (List.skipn (List.length output_types) runtime_reg)
    /\ List.map fst (List.filter (fun '(_, v) => output_scalars_are_pointers || Option.is_Some v)%bool (List.combine asm_arguments_out output_types)) = asm_pointer_arguments_out
    /\ List.map fst (List.filter (fun '(_, v) => match v with inl _ => false | inr _ => true end)%bool (List.combine asm_arguments_in runtime_inputs)) = asm_pointer_arguments_in
    /\ (Semantics.get_reg m rsp - 8 * Z.of_nat stack_size)%Z = word.unsigned stack_base
    /\
      Forall2
        (fun v1 v2 => match v1 with
                      | inl v => v = v2
                      | inr _ => True
                      end)
        runtime_inputs
        (firstn (length runtime_inputs) (skipn (length output_types) runtime_reg))
    /\ R_runtime_input_mem (output_scalars_are_pointers:=output_scalars_are_pointers) frame output_types runtime_inputs stack_size stack_base asm_arguments_out asm_arguments_in runtime_reg m).
Defined.
Definition R_runtime_output_mem
           {output_scalars_are_pointers:bool}
           (frame : Semantics.mem_state -> Prop)
           (runtime_outputs : list (Z + list Z)) (input_types : type_spec)
           (stack_size : nat) (stack_base : Naive.word 64)
           (asm_arguments_out asm_arguments_in : list (Naive.word 64))
           (m : Semantics.mem_state)
  : Prop.
exact (exists (stack_placeholder_values : list Z) (input_placeholder_values : list (Z + list Z)),
    Forall (fun v : Z => (0 <= v < 2 ^ 64)%Z) stack_placeholder_values
    /\ stack_size = List.length stack_placeholder_values
    /\ Forall2 val_or_list_val_matches_spec input_placeholder_values input_types
    /\ Forall (fun v => match v with
                        | inl v => (0 <= v < 2^64)%Z
                        | inr vs => Forall (fun v => (0 <= v < 2^64)%Z) vs
                        end) input_placeholder_values
    /\ ((frame *
           R_list_scalar_or_array (dereference_scalar:=output_scalars_are_pointers) runtime_outputs asm_arguments_out *
           R_list_scalar_or_array (dereference_scalar:=false) input_placeholder_values asm_arguments_in *
           array cell64 (word.of_Z 8) stack_base stack_placeholder_values)%sep)
         m).
Defined.
Definition R_runtime_output
           {output_scalars_are_pointers:bool}
           (frame : Semantics.mem_state -> Prop)
           (runtime_outputs : list (Z + list Z)) (input_types : type_spec)
           (stack_size : nat) (stack_base : Naive.word 64)
           (asm_pointer_arguments_out asm_pointer_arguments_in : list (Naive.word 64))
           (callee_saved_registers : list REG) (runtime_callee_saved_registers : list Z)
           (m : machine_state)
  : Prop.
exact (exists (asm_arguments_out asm_arguments_in : list (Naive.word 64)),
    Forall (fun v => (0 <= v < 2^64)%Z) (Tuple.to_list _ m.(machine_reg_state))
    /\ get_asm_reg m callee_saved_registers = runtime_callee_saved_registers
    /\ List.map fst (List.filter (fun '(_, v) => output_scalars_are_pointers || match v with inl _ => false | inr _ => true end)%bool (List.combine asm_arguments_out runtime_outputs)) = asm_pointer_arguments_out
    /\ List.map fst (List.filter (fun '(_, v) => Option.is_Some v)%bool (List.combine asm_arguments_in input_types)) = asm_pointer_arguments_in
    /\ R_runtime_output_mem (output_scalars_are_pointers:=output_scalars_are_pointers) frame runtime_outputs input_types stack_size stack_base asm_arguments_out asm_arguments_in m).
Defined.
Definition word_args_to_Z_args
  : list (Naive.word 64 + list (Naive.word 64)) -> list (Z + list Z).
Admitted.

Lemma word_args_to_Z_args_bounded args
  : Forall (fun v => match v with
                     | inl v => (0 <= v < 2^64)%Z
                     | inr vs => Forall (fun v => (0 <= v < 2^64)%Z) vs
                     end) (word_args_to_Z_args args).
Admitted.

Lemma init_symbolic_state_ok m G d
      (frame : Semantics.mem_state -> Prop)
      (Hd : gensym_dag_ok G d)
      (ss := init_symbolic_state d)
      (d' := ss.(dag_state))
      (Hbounds : Forall (fun v => (0 <= v < 2^64)%Z) (Tuple.to_list 16 m.(machine_reg_state)))
      (Hframe : frame m)
  : exists G',
    R frame G' ss m
    /\ (forall reg, Option.is_Some (Symbolic.get_reg ss.(symbolic_reg_state) (reg_index reg)) = true)
    /\ gensym_dag_ok G' d'
    /\ (forall e n, eval G d e n -> eval G' d' e n).
Admitted.

Lemma get_reg_bounded mr reg
  : (0 <= Semantics.get_reg mr reg < 2 ^ 64)%Z.
Admitted.

Local Lemma eq_list_of_filter_nil A (l : list A) l1 l2
      (H : (List.length l1 = List.length l2) /\ (List.length l1 <= List.length l)%nat)
      (H'' : filter (fun '(_, (init, final)) => negb (init =? final)%N)
                    (List.combine l (List.combine l2 l1)) = [])
  : l1 = l2.
Admitted.

Lemma reg_bounded_of_R frame G s m
      (H : R frame G s m)
  : Forall (fun v : Z => (0 <= v < 2 ^ 64)%Z) (Tuple.to_list _ m.(machine_reg_state)).
Admitted.

Lemma build_inputs_ok_R {descr:description} G ss types inputs args d' frame ms
      (d := ss.(dag_state))
      (H : build_inputs types d = (inputs, d'))
      (HR : R frame G ss ms)
      (Hargs : Forall2 val_or_list_val_matches_spec args types)
      (Hbounds : Forall (fun v => match v with
                                  | inl v => (0 <= v < 2^64)%Z
                                  | inr vs => Forall (fun v => (0 <= v < 2^64)%Z) vs
                                  end) args)
  : exists G',
    Forall2 (eval_idx_or_list_idx G' d') inputs args
    /\ gensym_dag_ok G' d'
    /\ (forall e n, eval G d e n -> eval G' d' e n)
    /\ R frame G' (update_dag_with ss (fun _ => d')) ms.
Admitted.

Lemma build_merge_stack_placeholders_ok_R {opts : symbolic_options_computed_opt} {descr:description} G s s' frame frame' ms
      (rsp_val : Z) (stack_vals : list Z) base_stack base_stack_word_val
      (H : build_merge_stack_placeholders (List.length stack_vals) s = Success (base_stack, s'))
      (d := s.(dag_state))
      (d' := s'.(dag_state))
      (r := s.(symbolic_reg_state))
      (r' := s'.(symbolic_reg_state))
      (f := s.(symbolic_flag_state))
      (f' := s'.(symbolic_flag_state))
      (m := s.(symbolic_mem_state))
      (m' := s'.(symbolic_mem_state))
      (Hstack_vals_bounded : Forall (fun v : Z => (0 <= v < 2 ^ 64)%Z) stack_vals)
      (stack_addr_vals := List.map (fun i => Z.land (rsp_val - 8 * Z.of_nat (List.length stack_vals) + 8 * Z.of_nat i) (Z.ones 64)) (seq 0 (List.length stack_vals)))
      (HR : R frame' G s ms)
      (Hrsp : (rsp_val - 8 * Z.of_nat (List.length stack_vals))%Z = word.unsigned base_stack_word_val)
      (Hframe : Lift1Prop.iff1 frame' (frame * array cell64 (word.of_Z 8) base_stack_word_val stack_vals)%sep)
      (Hreg_good : forall reg, Option.is_Some (Symbolic.get_reg r (reg_index reg)) = true)
      (Hrsp_val : Z.land rsp_val (Z.ones 64) = Z.land (Semantics.get_reg ms rsp) (Z.ones 64))
  : exists G',
    ((exists rsp_idx,
         set_reg r (reg_index rsp) rsp_idx = r'
         /\ eval_idx_Z G' d' rsp_idx (Z.land rsp_val (Z.ones 64)))
     /\ f = f'
     /\ (exists stack_addr_idxs stack_idxs,
            Forall2 (eval_idx_Z G' d') stack_addr_idxs stack_addr_vals
            /\ Forall2 (eval_idx_Z G' d') stack_idxs stack_vals
            /\  List.rev (List.combine stack_addr_idxs stack_idxs) ++ m = m'))
    /\ eval_idx_Z G' d' base_stack (Z.land (rsp_val - 8 * Z.of_nat (List.length stack_vals)) (Z.ones 64))
    /\ gensym_dag_ok G' d'
    /\ (forall e n, eval G d e n -> eval G' d' e n)
    /\ R frame G' s' ms
    /\ (forall reg, Option.is_Some (Symbolic.get_reg r' (reg_index reg)) = true).
Admitted.

Local Ltac find_list_in ls in_ls :=
  lazymatch in_ls with
  | ls => idtac
  | firstn _ ?ls' => find_list_in ls ls'
  | List.combine ?lsa ?lsb => first [ find_list_in ls lsa | find_list_in ls lsb ]
  | List.map _ ?ls' => find_list_in ls ls'
  end.

Local Ltac revert_Forall_step ls :=
  match goal with
  | [ H : Forall2 _ ?lsa ?lsb |- _ ]
    => first [ find_list_in ls lsa | find_list_in ls lsb ];
       revert H
  | [ H : Forall _ ?ls' |- _ ]
    => find_list_in ls ls';
       revert H
  | [ H : context[nth_error ?ls' _] |- _ ]
    => find_list_in ls ls';
       revert H
  end.

Local Ltac revert_Foralls :=
  repeat match goal with
         | [ |- context[Forall2 _ ?ls _] ]
           => revert_Forall_step ls
         | [ |- context[Forall2 _ _ ?ls] ]
           => revert_Forall_step ls
         | [ |- context[Forall _ ?ls] ]
           => revert_Forall_step ls
         end.

Local Ltac intros_then_revert tac :=
  let H := fresh in
  pose proof I as H;
  intros;
  tac ();
  revert_until H;
  clear H.

Local Ltac reverted_Foralls_to_nth_error :=
  rewrite ?@Forall2_forall_iff_nth_error, ?@Forall_forall_iff_nth_error_match;
  cbv [option_eq];
  intros_then_revert
    ltac:(fun _
          => repeat match goal with
                    | [ H : context[nth_error ?ls _] |- context[nth_error ?ls ?i] ]
                      => specialize (H i)
                    | [ H : context[nth_error ?ls _], H' : context[nth_error ?ls ?i] |- _ ]
                      => specialize (H i)
                    | [ H : context[nth_error ?ls _] |- context[nth_error ?ls' ?i] ]
                      => first [ find_list_in ls ls' | find_list_in ls' ls ];
                         specialize (H i)
                    | [ H : context[nth_error ?ls _], H' : context[nth_error ?ls' ?i] |- _ ]
                      => find_list_in ls ls'; specialize (H i)
                    end).

Local Ltac revert_Foralls_to_nth_error := revert_Foralls; reverted_Foralls_to_nth_error.

Ltac adjust_Foralls_firstn_skipn :=
  let rep a a' :=
    tryif constr_eq a a'
    then idtac
    else (let H' := fresh in
          assert (H' : a' = a) by congruence;
          rewrite H' in * ) in
  let check_H H :=
    lazymatch type of H with
    | Forall _ _ => idtac
    | Forall2 _ _ _ => idtac
    end in
  repeat match goal with
         | [ H : context[firstn ?n ?ls] |- context[firstn ?n' ?ls] ]
           => check_H H; progress rep n n'
         | [ H : context[skipn ?n ?ls] |- context[skipn ?n' ?ls] ]
           => check_H H; progress rep n n'
         end.

Local Ltac Foralls_to_nth_error_rewrites :=
  repeat rewrite ?@nth_error_combine, ?@nth_error_firstn, ?@nth_error_skipn, ?@nth_error_map, ?@nth_error_seq; cbv [option_map].

Local Ltac Foralls_to_nth_error_destructs :=
  let cleanup _ :=
    try match goal with
        | [ |- context[False -> _] ] => intros; exfalso; assumption
        | [ |- context[Some _ = None -> _] ] => intros; now inversion_option
        | [ |- context[None = Some _ -> _] ] => intros; now inversion_option
        | [ |- context[_ -> True] ] => intros; exact I
        | [ |- context[_ -> ?x = ?x] ] => intros; reflexivity
        end in
  let match_free v :=
    lazymatch v with
    | context[match _ with _ => _ end] => fail
    | _ => idtac
    end in
  let do_destruct v :=
    first [ is_var v; destruct v
          | lazymatch type of v with
            | sumbool _ _ => destruct v
            | _ => let H := fresh in
                   destruct v eqn:H; revert H
            end ] in
  let find_v P :=
    match P with
    | context[False]
      => lazymatch P with
         | match ?v with _ => _ end => v
         end
    | match ?v with _ => _ end = ?RHS
      => let LHS := lazymatch P with ?LHS = _ => LHS end in
         lazymatch RHS with
         | None
           => lazymatch LHS with
              | context[None] => v
              end
         | Some _
           => lazymatch LHS with
              | context[Some _] => v
              end
         end
    end in
  repeat (first [ match goal with
                  | [ |- context[?P -> _] ]
                    => let v := find_v P in
                       match_free v; do_destruct v
                  | [ |- context[?P -> _] ]
                    => let v := find_v P in
                       do_destruct v
                  end
                | break_innermost_match_step
                | progress Foralls_to_nth_error_rewrites ];
          cleanup ()).

Local Ltac Foralls_to_nth_error_cleanup :=
  intros_then_revert
    ltac:(fun _
          => repeat first [ assumption
                          | exact I
                          | exfalso; assumption
                          | progress subst
                          | progress destruct_head'_and
                          | progress inversion_option
                          | progress inversion_pair
                          | progress inversion_sum
                          | discriminate ]).

Local Ltac Foralls_to_nth_error :=
  revert_Foralls_to_nth_error;
  intros *;
  Foralls_to_nth_error_rewrites;
  Foralls_to_nth_error_destructs;
  Foralls_to_nth_error_cleanup.

Lemma build_merge_base_addresses_ok_R
      {opts : symbolic_options_computed_opt} {descr:description} {dereference_scalar:bool}
      (idxs : list (idx + list idx))
      (reg_available : list REG)
      (runtime_reg : list Z)
      G s frame frame' ms
      (d := s.(dag_state))
      (Hvals : Forall2 (fun it rv
                        => match it with
                           | inl idx => if dereference_scalar
                                        then True
                                        else eval_idx_Z G d idx rv
                           | inr _ => True
                           end)
                       idxs (List.firstn (List.length idxs) runtime_reg))
      (Hreg : Nat.min (List.length idxs) (List.length reg_available) <= List.length runtime_reg)
      (Henough_reg : List.length idxs <= List.length reg_available)
      s'
      (d' := s'.(dag_state))
      (r := s.(symbolic_reg_state))
      (r' := s'.(symbolic_reg_state))
      (f := s.(symbolic_flag_state))
      (f' := s'.(symbolic_flag_state))
      (m := s.(symbolic_mem_state))
      (m' := s'.(symbolic_mem_state))
      outputaddrs
      (H : build_merge_base_addresses (dereference_scalar:=dereference_scalar) idxs reg_available s = Success (outputaddrs, s'))
      (Hreg_available_wide : Forall (fun reg => let '(rn, lo, sz) := index_and_shift_and_bitcount_of_reg reg in sz = 64%N) reg_available)
      (HR : R frame' G s ms)
      (Hreg_good : forall reg, Option.is_Some (Symbolic.get_reg r (reg_index reg)) = true)
      (Hruntime_reg : get_asm_reg ms reg_available = runtime_reg)
      addr_vals addr_ptr_vals
      (Haddr_ptr_vals : List.map word.unsigned addr_ptr_vals = List.firstn (List.length idxs) runtime_reg)
      (Hframe : Lift1Prop.iff1 frame' (frame * R_list_scalar_or_array (dereference_scalar:=dereference_scalar) addr_vals addr_ptr_vals)%sep)
      (Heval_addr_vals : Forall2 (eval_idx_or_list_idx G d) idxs addr_vals)
      (Hruntime_reg_bounded : Forall (fun v => (0 <= v < 2^64)%Z) runtime_reg)
  : exists G',
    ((exists (outputaddrs' : list (idx * option idx + idx * list idx)),
         let addrs_vals_of := fun base_reg_val addrs' => List.map (fun i => Z.land (base_reg_val + 8 * Z.of_nat i) (Z.ones 64)) (seq 0 (List.length addrs')) in
         fold_left (fun rst '(r, idx')
                    => set_reg rst (reg_index r)
                               match idx' with
                               | inl (idx', _) => idx'
                               | inr (base_idx', idxs') => base_idx'
                               end)
                   (List.combine reg_available outputaddrs')
                   r
         = r'
         /\ (
             List.rev (List.flat_map
                         (fun '(idx', idx)
                          => match idx', idx with
                             | inl (reg_val, Some addr), inl val => if dereference_scalar then [(addr, val)] else []

                             | inl _, _ | _, inl _ => []
                             | inr (base', addrs'), inr items
                               => List.combine addrs' items
                             end)
                         (List.combine outputaddrs' idxs))
                      ++ m)
            = m'
         /\
           Forall2
             (fun idx' v =>
                match idx' with
                | inl (idx', addr')
                  => eval_idx_Z G' d' idx' (Z.land v (Z.ones 64))
                     /\ option_eq (eval_idx_Z G' d') addr' (if dereference_scalar then Some (Z.land v (Z.ones 64)) else None)
                | inr (base', addrs')

                  => eval_idx_Z G' d' base' (Z.land v (Z.ones 64))
                     /\
                       Forall2 (eval_idx_Z G' d') addrs' (addrs_vals_of v addrs')
                end)
             outputaddrs'
             (List.firstn (List.length outputaddrs') runtime_reg)
         /\
           Forall2
             (fun idx base_reg_val =>
                match idx with
                | inr base => eval_idx_Z G' d' base (Z.land base_reg_val (Z.ones 64))
                | inl (inr base) => eval_idx_Z G' d' base (Z.land base_reg_val (Z.ones 64))
                | inl (inl r) => True
                end)
             outputaddrs
             (List.firstn (List.length outputaddrs) runtime_reg)
         /\
           Forall2
             (fun idx r =>
                match idx with
                | inl (inl r') => r = r'
                | inl (inr _) | inr _ => True
                end)
             outputaddrs
             (List.firstn (List.length outputaddrs) reg_available)
         /\ Forall2 (fun addr idx =>
                       match addr, idx with
                       | inl (idx, _), inl val_idx
                         => if dereference_scalar
                            then True
                            else forall v, (0 <= v < 2^64)%Z -> eval_idx_Z G' d' idx v <-> eval_idx_Z G' d' val_idx v
                       | inr (_, ls), inr ls' => List.length ls = List.length ls'
                       | inl _, inr _ | inr _, inl _ => False
                       end)
                    outputaddrs' idxs
         /\ Forall2 (fun addr idx =>
                       match addr, idx with
                       | inl (inl _), inl (_, None) => dereference_scalar = false
                       | inl (inr addr), inl (_, Some addr') => dereference_scalar = true /\ addr = addr'
                       | inr _, inr _ => True
                       | inl (inl _), inl (_, Some _) | inl (inr _), inl (_, None) => False
                       | inl _, inr _ | inr _, inl _ => False
                       end)
                    outputaddrs outputaddrs')
     /\ f = f')
    /\ gensym_dag_ok G' d'
    /\ (forall e n, eval G d e n -> eval G' d' e n)
    /\ R frame G' s' ms
    /\ (forall reg, Option.is_Some (Symbolic.get_reg r' (reg_index reg)) = true).
Admitted.

Lemma mapM_GetReg_ok_R {opts : symbolic_options_computed_opt} {descr:description} G regs idxs s s' frame (ms : machine_state)
      (H : mapM GetReg regs s = Success (idxs, s'))
      (d := s.(dag_state))
      (d' := s'.(dag_state))
      (r := s.(symbolic_reg_state))
      (r' := s'.(symbolic_reg_state))
      (f := s.(symbolic_flag_state))
      (f' := s'.(symbolic_flag_state))
      (m := s.(symbolic_mem_state))
      (m' := s'.(symbolic_mem_state))
      (reg_vals := List.map (Semantics.get_reg ms) regs)
      (Hwide : Forall (fun reg => let '(_, _, sz) := index_and_shift_and_bitcount_of_reg reg in sz = 64%N) regs)
      (HR : R frame G s ms)
      (Hreg_good : forall reg, Option.is_Some (Symbolic.get_reg r (reg_index reg)) = true)
  : ((exists reg_idxs,
         List.map (get_reg r) (List.map reg_index regs) = List.map Some reg_idxs
         /\ Forall2 (eval_idx_Z G s') reg_idxs reg_vals)
     /\ Forall2 (eval_idx_Z G s') idxs reg_vals
     /\ r = r'
     /\ f = f'
     /\ m = m')
    /\ gensym_dag_ok G d'
    /\ (forall e n, eval G d e n -> eval G d' e n)
    /\ R frame G s' ms
    /\ (forall reg, Option.is_Some (Symbolic.get_reg r' (reg_index reg)) = true).
Admitted.

Lemma SymexLines_ok_R {opts : symbolic_options_computed_opt}
      frame G s m asm _tt s'
      (d := s.(dag_state))
      (d' := s'.(dag_state))
      (r := s.(symbolic_reg_state))
      (r' := s'.(symbolic_reg_state))
      (H : Symbolic.SymexLines asm s = Success (_tt, s'))
      (Hreg_good : forall reg, Option.is_Some (Symbolic.get_reg r (reg_index reg)) = true)
      (HR : R frame G s m)
  : exists m',
    Semantics.DenoteLines m asm = Some m'
    /\ gensym_dag_ok G d
    /\ (forall e n, eval G d e n -> eval G d' e n)
    /\ R frame G s' m'
    /\ same_mem_addressed s s'
    /\ (forall reg, Option.is_Some (Symbolic.get_reg r' (reg_index reg)) = true).
Admitted.

Lemma get_asm_reg_bounded s rs : Forall (fun v => (0 <= v < 2 ^ 64)%Z) (get_asm_reg s rs).
Admitted.

Lemma LoadArray_ok_R {opts : symbolic_options_computed_opt} {descr:description} frame G s ms s' base base_val base_word_val len idxs
      (H : LoadArray base len s = Success (idxs, s'))
      (d := s.(dag_state))
      (d' := s'.(dag_state))
      (r := s.(symbolic_reg_state))
      (r' := s'.(symbolic_reg_state))
      (f := s.(symbolic_flag_state))
      (f' := s'.(symbolic_flag_state))
      (m := s.(symbolic_mem_state))
      (m' := s'.(symbolic_mem_state))
      (HR : R frame G s ms)
      (Hbase : eval_idx_Z G d base (Z.land base_val (Z.ones 64)))
      (Hbase_word_val : base_val = word.unsigned base_word_val)
      (Hreg_good : forall reg, Option.is_Some (Symbolic.get_reg r (reg_index reg)) = true)
  : ((exists (addrs : list idx),
         Permutation m (List.combine addrs idxs ++ m')
         /\ List.length idxs = len
         /\ Forall2 (eval_idx_Z G d') addrs (List.map (fun i => Z.land (base_val + 8 * Z.of_nat i) (Z.ones 64)) (seq 0 len))
         /\ Forall (fun addr => Forall (fun x => (fst x =? addr)%N = false) m') addrs)
     /\ r = r'
     /\ f = f')
    /\ gensym_dag_ok G d'
    /\ (forall e n, eval G d e n -> eval G d' e n)
    /\ ((exists vals,
            Forall2 (eval_idx_Z G d') idxs vals
            /\ Forall (fun v => 0 <= v < 2^64)%Z vals
            /\ R (frame * array cell64 (word.of_Z 8) base_word_val vals)%sep G s' ms)
        /\ (forall reg, Option.is_Some (Symbolic.get_reg r' (reg_index reg)) = true)).
Admitted.

Lemma LoadOutputs_ok_R {opts : symbolic_options_computed_opt} {descr:description} {dereference_scalar:bool} frame G s ms s' outputaddrs output_types output_vals idxs
      (H : LoadOutputs (dereference_scalar:=dereference_scalar) outputaddrs output_types s = Success (Success idxs, s'))
      (d := s.(dag_state))
      (d' := s'.(dag_state))
      (r := s.(symbolic_reg_state))
      (r' := s'.(symbolic_reg_state))
      (f := s.(symbolic_flag_state))
      (f' := s'.(symbolic_flag_state))
      (m := s.(symbolic_mem_state))
      (m' := s'.(symbolic_mem_state))
      (HR : R frame G s ms)
      (Houtputaddrs : Forall2 (fun idx val
                               => match idx with
                                  | inl (inr base) | inr base => eval_idx_Z G d base (Z.land val (Z.ones 64))
                                  | inl (inl _)
                                    => True
                                  end) outputaddrs output_vals)
      (Houtputaddrs_reg : Forall (fun idx
                                  => match idx with
                                     | inl (inl r)
                                       => (let '(rn, lo, sz) := index_and_shift_and_bitcount_of_reg r in sz = 64%N)
                                          /\ dereference_scalar = false
                                     | inl (inr _)
                                       => dereference_scalar = true
                                     | _ => True
                                     end) outputaddrs)
      (Hreg_good : forall reg, Option.is_Some (Symbolic.get_reg r (reg_index reg)) = true)
  : (exists output_vals_words (output_vals' : list Z) (outputaddrs' : list (idx + list idx)) vals,
        output_vals' = List.map word.unsigned output_vals_words
        /\ Forall (fun v => (0 <= v < 2^64)%Z) output_vals'
        /\ List.length output_vals = List.length output_vals'
        /\ (Forall2 (fun idxs '((base, len), (base_val, base_val'))
                     => match idxs, base, len with
                        | inr idxs, inr base, Some len
                          => Forall2 (eval_idx_Z G d') idxs (List.map (fun i => Z.land (base_val + 8 * Z.of_nat i) (Z.ones 64)) (seq 0 len))
                             /\ Z.land base_val (Z.ones 64) = base_val'
                        | inl idx, inl (inl r), None
                          => (exists idx',
                                 get_reg s' (reg_index r) = Some idx'
                                 /\ eval_idx_Z G d' idx' base_val')
                             /\ eval_idx_Z G d' idx base_val'
                             /\ dereference_scalar = false
                        | inl idx, inl (inr addr), None
                          => idx = addr
                             /\ eval_idx_Z G d' addr base_val'
                             /\ dereference_scalar = true
                        | _, _, _ => False
                        end)
                    outputaddrs'
                    (List.combine (List.combine outputaddrs output_types) (List.combine output_vals output_vals'))
            /\ Permutation m (List.flat_map
                                (fun '(addrs, idxs)
                                 => match addrs, idxs with
                                    | inr addrs, inr idxs
                                      => List.combine addrs idxs
                                    | inl addr, inl idx
                                      => if dereference_scalar
                                         then [(addr, idx)]
                                         else []
                                    | inl _, inr _ | inr _, inl _ => []
                                    end)
                                (List.combine outputaddrs' idxs)
                                ++ m')
            /\ Forall2
                 (fun addrs idxs
                  => match addrs, idxs with
                     | inl idx, inl val_idx
                       => if dereference_scalar
                          then True
                          else forall v, (0 <= v < 2^64)%Z -> eval_idx_Z G d' idx v <-> eval_idx_Z G d' val_idx v
                     | inr addrs, inr idxs
                       => List.length idxs = List.length addrs
                     | inl _, inr _ | inr _, inl _ => False
                     end)
                 outputaddrs'
                 idxs
            /\ Forall (fun addrs => match addrs with
                                    | inl idx => True
                                    | inr addrs
                                      => Forall (fun addr => Forall (fun x => (fst x =? addr)%N = false) m') addrs
                                    end)
                      outputaddrs'
            /\ List.length output_types = List.length outputaddrs)
        /\ (Forall2 (eval_idx_or_list_idx G d') idxs vals
            /\ Forall (fun v => match v with
                                | inl v => (0 <= v < 2^64)%Z
                                | inr vs => Forall (fun v => (0 <= v < 2^64)%Z) vs
                                end) vals
            /\ R (frame * R_list_scalar_or_array (dereference_scalar:=dereference_scalar) vals output_vals_words)%sep G s' ms))
    /\ r = r'
    /\ f = f'
    /\ gensym_dag_ok G d'
    /\ (forall e n, eval G d e n -> eval G d' e n)
    /\ (forall reg, Option.is_Some (Symbolic.get_reg r' (reg_index reg)) = true).
Admitted.

Local Ltac debug_run tac := tac ().

Theorem symex_asm_func_M_correct
        {opts : symbolic_options_computed_opt}
        {output_scalars_are_pointers:bool}
        d frame asm_args_out asm_args_in (G : symbol -> option Z) (s := init_symbolic_state d)
        (s' : symbolic_state) (m : machine_state) (output_types : type_spec) (stack_size : nat) (stack_base : Naive.word 64)
        (inputs : list (idx + list idx)) (callee_saved_registers : list REG) (reg_available : list REG) (asm : Lines)
        (rets : list (idx + list idx))
        (H : symex_asm_func_M (dereference_output_scalars:=output_scalars_are_pointers) callee_saved_registers output_types stack_size inputs reg_available asm s = Success (Success rets, s'))
        (word_runtime_inputs : list (Naive.word 64 + list (Naive.word 64)))
        (runtime_inputs := word_args_to_Z_args word_runtime_inputs)
        (runtime_reg : list Z)

        (runtime_callee_saved_registers : list Z)

        (HR : R_runtime_input (output_scalars_are_pointers:=output_scalars_are_pointers) frame output_types runtime_inputs stack_size stack_base asm_args_out asm_args_in reg_available runtime_reg callee_saved_registers runtime_callee_saved_registers m)
        (Hd_ok : gensym_dag_ok G d)
        (d' := s'.(dag_state))
        (H_enough_reg : (List.length output_types + List.length runtime_inputs <= List.length reg_available)%nat)
        (Hcallee_saved_reg_wide_enough : Forall (fun reg => let '(_, _, sz) := index_and_shift_and_bitcount_of_reg reg in sz = 64%N) callee_saved_registers)
        (Hreg_wide_enough : Forall (fun reg => let '(_, _, sz) := index_and_shift_and_bitcount_of_reg reg in sz = 64%N) reg_available)
        (Hinputs : List.Forall2 (eval_idx_or_list_idx G d) inputs runtime_inputs)
  : exists m' G'
           (runtime_rets : list (Z + list Z)),
    (DenoteLines m asm = Some m'
     /\ R_runtime_output (output_scalars_are_pointers:=output_scalars_are_pointers) frame runtime_rets (type_spec_of_runtime runtime_inputs) stack_size stack_base asm_args_out asm_args_in callee_saved_registers runtime_callee_saved_registers m'
     /\ List.Forall2 (eval_idx_or_list_idx G' d') rets runtime_rets)
    /\ gensym_dag_ok G' d'
    /\ (forall e n, eval G d e n -> eval G' d' e n).
Proof.
  pose proof (word_args_to_Z_args_bounded word_runtime_inputs).
  pose proof get_asm_reg_bounded.
  cbv [symex_asm_func_M Symbolic.bind ErrorT.bind lift_dag] in H.
  break_match_hyps; destruct_head'_prod; destruct_head'_unit; cbn [fst snd] in *; try discriminate; [].
  repeat first [ progress subst
               | match goal with
                 | [ H : Success _ = Success _ |- _ ] => inversion H; clear H
                 | [ x := ?y |- _ ] => subst x
                 end ].
  cbv [R_runtime_output].
  cbv [R_runtime_input R_runtime_input_mem] in HR; repeat (destruct_head'_ex; destruct_head'_and).
  let HR := lazymatch goal with HR : sep _ _ (machine_mem_state m) |- _ => HR end in
  destruct (init_symbolic_state_ok m G _ _ ltac:(eassumption) ltac:(eassumption) HR) as [G1 ?]; destruct_head'_and.
  move Heqp at bottom.
  repeat first [ progress destruct_head'_ex
               | progress destruct_head'_and
               | progress cbn [update_dag_with Symbolic.dag_state Symbolic.symbolic_flag_state Symbolic.symbolic_mem_state Symbolic.symbolic_reg_state] in *
               | solve [ auto ]
               | match goal with
                 | [ H : filter _ (List.combine _ (List.combine ?l1 ?l2))  = [] |- _ ]
                   => is_var l1; is_var l2; apply eq_list_of_filter_nil in H;
                      [ try (subst l1 || subst l2)
                      | cbv [idx] in *; saturate_lengths;
                        generalize dependent (List.length l1);
                        generalize dependent (List.length l2);
                        intros; subst; rewrite ?map_length; split; try reflexivity; try congruence; lia ]
                 | [ H : Forall2 (eval_idx_Z _ _) ?l ?v, H' : Forall2 (eval_idx_Z _ _) ?l ?v' |- _ ]
                   => unique assert (v = v')
                     by (eapply eval_eval_idx_Z_Forall2; eapply Forall2_weaken; [ | eassumption | | eassumption ];
                         intros *; apply lift_eval_idx_Z_impl;
                         now typeclasses eauto with core)
                 | [ H : R _ _ _ ?m |- _ ]
                   => is_var m; unique pose proof (@reg_bounded_of_R _ _ _ _ H)
                 end
               | match reverse goal with
                 | [ H : build_inputs _ _ = _ |- exists m' : machine_state, _ ]
                   => debug_run ltac:(fun _ => idtac "build_inputs start");
                      move H at bottom; eapply build_inputs_ok_R in H;
                      [ | eassumption .. ];
                      debug_run ltac:(fun _ => idtac "build_inputs end")
                 | [ H : build_merge_base_addresses _ ?reg_available _ = _ |- exists m' : machine_state, _ ]
                   => debug_run ltac:(fun _ => idtac "build_merge_base_addresses start");
                      move H at bottom;
                      let runtime_regv := lazymatch reg_available with
                                          | firstn ?n _ => constr:(firstn n runtime_reg)
                                          | skipn ?n _ => constr:(skipn n runtime_reg)
                                          | _ => runtime_reg
                                          end in
                      eapply @build_merge_base_addresses_ok_R
                        with (runtime_reg := runtime_regv )
                        in H;
                      [
                      | try solve [ eassumption | subst; eauto using Forall_skipn, Forall_firstn with nocore ] .. ];
                      [
                      | lazymatch goal with
                        | [ |- (_ <= _)%nat ] => saturate_lengths; try lia
                        | [ |- ?G ]
                          => first [ has_evar G
                                   | try solve
                                         [ repeat
                                             first [ reflexivity
                                                   | progress subst
                                                   | progress cbv [get_asm_reg]
                                                   | rewrite skipn_map
                                                   | rewrite firstn_map ] ] ]
                        end .. ];
                      [
                      | try solve [ eapply Forall2_weaken; [ | eassumption ]; now eauto using lift_eval_idx_or_list_idx_impl ] .. ];
                      [
                      | lazymatch goal with
                        | [ |- Lift1Prop.iff1 ?P ?Q ]
                          => match P with
                             | context[R_list_scalar_or_array ?p ?v]
                               => match Q with
                                  | context[R_list_scalar_or_array ?p' ?v']
                                    => tryif (is_evar p'; is_evar v')
                                      then fail
                                      else (unify p p'; unify v v')
                                  end
                             end;
                             SeparationLogic.cancel
                        | [ |- Forall2 _ _ _ ]
                          => saturate_lengths;
                             adjust_Foralls_firstn_skipn;
                             try solve [ Foralls_to_nth_error; eauto using lift_eval_idx_Z_impl ]
                        | _ => idtac
                        end .. ];
                      [
                      | lazymatch goal with
                        | [ |- List.map word.unsigned _ = _ ]
                          => saturate_lengths;
                             adjust_Foralls_firstn_skipn;
                             try rewrite ListUtil.List.firstn_firstn, Nat.min_idempotent;
                             try eassumption
                        | _ => idtac
                        end .. ];
                      [];
                      debug_run ltac:(fun _ => idtac "build_merge_base_addresses end")
                 | [ H : build_merge_stack_placeholders _ _ = _ |- exists m' : machine_state, _ ]
                   => debug_run ltac:(fun _ => idtac "build_merge_stack_placeholders start");
                      subst stack_size;
                      eapply build_merge_stack_placeholders_ok_R in H;
                      [ | try eassumption; auto .. ];
                      [
                      | lazymatch goal with
                        | [ |- Lift1Prop.iff1 _ _ ] => set_evars; SeparationLogic.cancel
                        | _ => idtac
                        end .. ];
                      [];
                      debug_run ltac:(fun _ => idtac "build_merge_stack_placeholders end")
                 | [ H : mapM _ callee_saved_registers _ = _ |- @ex ?T _ ]
                   => lazymatch T with
                      |  list (Z + list Z) => idtac
                      |  machine_state => idtac
                      end;
                      debug_run ltac:(fun _ => idtac "get callee_saved_registers start");
                      eapply mapM_GetReg_ok_R in H;
                      [ | eassumption .. ];
                      debug_run ltac:(fun _ => idtac "get callee_saved_registers end")
                 | [ H : SymexLines _ _ = Success _ |- exists m' : machine_state, _ ]
                   => debug_run ltac:(fun _ => idtac "SymexLines start");
                      let H' := fresh in
                      eapply SymexLines_ok_R in H;
                      [ destruct H as [m' H];
                        exists m';
                        unshelve eexists;
                        lazymatch goal with
                        | [ |- symbol -> option Z ]
                          => repeat match goal with
                                    | [ H : ?T |- _ ]
                                      => lazymatch T with
                                         | symbol -> option Z => fail
                                         | _ => clear H
                                         end
                                    end;
                             shelve
                        | _ => idtac
                        end
                      | eassumption .. ];
                      debug_run ltac:(fun _ => idtac "SymexLines end")
                 | [ H : LoadArray _ _ _ = Success _ |- _ ]
                   => debug_run ltac:(fun _ => idtac "LoadArray start");
                      eapply LoadArray_ok_R in H;
                      [ | eauto using lift_eval_idx_Z_impl .. ];
                      [];
                      debug_run ltac:(fun _ => idtac "LoadArray end")
                 | [ H : LoadOutputs _ _ _ = Success _ |- _ ]
                   => debug_run ltac:(fun _ => idtac "LoadOutputs start");
                      eapply LoadOutputs_ok_R in H;
                      [ | try eassumption .. ];
                      [
                      | try solve [ eapply Forall2_weaken; [ | eassumption ]; cbv beta; intros *;
                                    break_innermost_match; cbv [eval_idx_Z] in *; eauto 10
                                  | lazymatch goal with
                                    | [ |- Forall _ ?ls ]
                                      => rewrite Forall_forall_iff_nth_error in Hreg_wide_enough;
                                         cbv [get_asm_reg] in *;
                                         cbv [val_or_list_val_matches_spec] in *;
                                         subst;
                                         Foralls_to_nth_error;
                                         cbv [index_and_shift_and_bitcount_of_reg] in *; inversion_pair; subst;
                                         eauto
                                    end ] .. ];
                      [];
                      debug_run ltac:(fun _ => idtac "LoadOutputs end")
                 end ].
  all: [ > ].
  lazymatch reverse goal with
  | [ H : ?x = Success ?y |- _ ]
    => let T := type of H in
       fail 0 "A non-processed step remains:" T
  | _ => idtac
  end.
  all: destruct_head' symbolic_state; cbn [update_dag_with Symbolic.dag_state Symbolic.symbolic_flag_state Symbolic.symbolic_mem_state Symbolic.symbolic_reg_state] in *; subst.
  all: cbv [R update_dag_with R_runtime_output_mem] in *; destruct_head'_and.
  all: destruct_head' machine_state; cbn [Semantics.machine_reg_state Semantics.machine_flag_state Semantics.machine_mem_state] in *.
  all: cbn [R_mem] in *.
  eexists.
  all: repeat first [ assumption
                    | match goal with
                      | [ |- _ /\ _ ] => split
                      | [ |- ex _ ] => eexists
                      end ].
  all: lazymatch goal with
       | [ |- gensym_dag_ok _ _ ] => eassumption
       | [ |- forall x y, eval _ _ _ _ -> eval _ _ _ _ ] => solve [ eauto 100 ]
       | [ |- Forall2 (eval_idx_or_list_idx _ _) _ _ ]
         => eapply Forall2_weaken; [ | eassumption ];
            eapply lift_eval_idx_or_list_idx_impl; eauto 100
       | _ => idtac
       end.
  all: lazymatch goal with
       | [ |- sep _ _ ?m ]
         => let H := lazymatch goal with H : sep _ _ m |- _ => H end in
            set_evars;
            revert H; generalize m;
            refine (_ : Lift1Prop.impl1 _ _);
            subst_evars;
            lazymatch goal with
            | [ |- Lift1Prop.impl1 ?P ?Q ]
              => cut (Lift1Prop.iff1 P Q); [ intros ->; reflexivity | ]
            end;
            repeat first [ progress (SeparationLogic.cancel; cbn [seps])
                         | match goal with
                           | [ |- Lift1Prop.iff1 ?P ?Q ]
                             => match P with
                                | context[array ?c ?s ?base ?v]
                                  => match Q with
                                     | context[array c s base ?v']
                                       => assert_fails (constr_eq v v');
                                          cut (v' = v); [ intros -> | ]
                                     end
                                | context[R_list_scalar_or_array ?x ?v]
                                  => match Q with
                                     | context[R_list_scalar_or_array x ?v']
                                       => assert_fails (constr_eq v v');
                                          cut (v' = v); [ intros -> | ]
                                     end
                                end
                           | [ |- Lift1Prop.iff1 (R_list_scalar_or_array ?x ?v) (R_list_scalar_or_array ?x' ?v') ]
                             => unify x x';
                                cut (v' = v); [ intros -> | ]
                           end ]
       | _ => idtac
       end.
  all: let G := match goal with |- ?G => G end in
       tryif has_evar G
       then idtac
       else (try assumption;
             lazymatch goal with
             | [ |- List.length _ = List.length _ ]
               => saturate_lengths; congruence
             | [ |- ?x = ?x ] => reflexivity
             | _ => idtac
             end).
  all: lazymatch goal with
       | [ |- Forall2 val_or_list_val_matches_spec _ _ ]
         => cbv [eval_idx_or_list_idx val_or_list_val_matches_spec type_spec_of_runtime] in *;
            rewrite ?@Forall2_map_l_iff, ?@Forall2_map_r_iff in *;
            saturate_lengths;
            Foralls_to_nth_error;
            intros; saturate_lengths;
            try congruence;
            try match goal with
                | [ H : (?x < ?y)%nat, H' : (?x >= ?y')%nat |- _ ]
                  => exfalso; cut (y = y'); [ clear -H H'; lia | congruence ]
                end
       | _ => idtac
       end.
  all: [ > | ].
  all: lazymatch goal with
       | [ |- List.map fst (filter _ (List.combine _ _)) = List.map fst (filter _ (List.combine _ _)) ]
         => idtac
       end.
  all: rewrite <- Forall2_eq, !Forall2_map_l_iff, !Forall2_map_r_iff.
  all: apply List.Forall2_filter_same.
  all: pose proof Hreg_wide_enough as Hreg_wide_enough'.
  all: rewrite Forall_forall_iff_nth_error in Hreg_wide_enough;
    cbv [get_asm_reg val_or_list_val_matches_spec] in *;
    rewrite <- !@Forall2_eq, ?@Forall2_map_l_iff, ?@Forall2_map_r_iff in *;
    saturate_lengths;
    Foralls_to_nth_error.
  all: cbn [fst].
  all: repeat (rewrite ?Bool.orb_true_l, ?Bool.orb_true_r, ?Bool.orb_false_l, ?Bool.orb_false_r in *; subst).
  all: try discriminate.
  all: try reflexivity.
  all: try specialize (Hreg_wide_enough _ eq_refl).
  all: try specialize (Hreg_wide_enough _ _ ltac:(eassumption)).
  all: intros; saturate_lengths.
  all: try specialize (Hreg_wide_enough _ _ ltac:(eassumption)).
  all: try match goal with
           | [ H : (?x < ?y)%nat, H' : (?x >= ?y')%nat |- _ ]
             => exfalso; cut (y = y'); [ clear -H H'; lia | congruence ]
           end.
  all: repeat match goal with
              | [ H : ?x = Some _, H' : ?x = None |- _ ]
                => rewrite H in H'; inversion_option
              | [ H : ?x = Some _, H' : ?x = Some _ |- _ ]
                => rewrite H in H'; inversion_option
              end.
  all: repeat match goal with
              | [ H : nth_error ?ls (?a + ?b) = _, H' : nth_error ?ls (?a' + ?b) = _ |- _ ]
                => replace a' with a in * by congruence;
                   rewrite H in H'
              end.
  all: inversion_option; subst.
  all: cbv [Option.is_Some] in *; break_innermost_match_hyps; inversion_option; inversion_sum.
  all: subst.
  all: try discriminate.
  all: lazymatch goal with
       | [ H : nth_error ?ls ?i = Some (Some _), H' : nth_error ?ls' ?i = Some (inl _) |- False ]
         => revert H H'
       | [ H : nth_error ?ls ?i = Some None, H' : nth_error ?ls' ?i = Some (inr _) |- False ]
         => revert H H'
       | [ H : nth_error _ _ = Some ?r, H' : nth_error _ _ = Some ?r0 |- ?r = ?r0 ]
         => apply Properties.word.unsigned_inj; revert H H'
       end.
  all: repeat match goal with
              | [ H : Forall2 _ ?x _ |- context[nth_error ?x _] ] => revert H
              | [ H : Forall2 _ _ (List.combine ?lsa ?lsb) |- context[nth_error ?ls] ]
                => first [ find_list_in ls lsa | find_list_in ls lsb ]; revert H
              end.
  all: revert dependent rets; intro.
  all: reverted_Foralls_to_nth_error;
    intros *; Foralls_to_nth_error_rewrites; Foralls_to_nth_error_destructs;
    Foralls_to_nth_error_cleanup.
  all: intros; saturate_lengths.
  all: try match goal with
           | [ H : (?x < ?y)%nat, H' : (?x >= ?y')%nat |- _ ]
             => exfalso; cut (y = y'); [ clear -H H'; lia | congruence ]
           end.
  all: try congruence.
  all: repeat match goal with
              | [ H : context[nth_error (List.combine _ _)] |- _ ]
                => lazymatch type of H with
                   | forall i : nat, @?P i
                     => let T := open_constr:(forall i : nat, _) in
                        cut T;
                        [ clear H
                        | let i := fresh "i" in
                          intro i; specialize (H i);
                          set_evars; revert H; Foralls_to_nth_error_rewrites;
                          intro H; subst_evars; exact H ]
                   end
              end.
  all: Foralls_to_nth_error.
  all: intros; saturate_lengths.
  all: try match goal with
           | [ H : (?x < ?y)%nat, H' : (?x >= ?y')%nat |- _ ]
             => exfalso; cut (y = y'); [ clear -H H'; lia | congruence ]
           end.
  all: rewrite ?(fun x y => Z.land_ones (Semantics.get_reg x y)) in * by (clear; lia).
  all: rewrite ?(fun x y => Z.mod_small (Semantics.get_reg x y)) in * by now apply get_reg_bounded.
  all: split_iff.
  all: repeat match goal with
              | [ H : forall v, (0 <= v < _)%Z -> eval_idx_Z _ _ ?a v -> _, H' : eval_idx_Z _ _ ?a ?v' |- _ ]
                => specialize (fun H1 H2 => H v' (conj H1 H2))
              end.
  all: specialize_by_assumption.
  all: specialize_by (cbv [eval_idx_Z] in *; eauto).
  all: specialize_by apply get_reg_bounded.
  all: specialize_by_assumption.
  all: handle_eval_eval.
  all: subst.
  all: try congruence.
  all: destruct_head'_ex.
  all: destruct_head'_and.
  all: handle_eval_eval.
  all: subst.
  all: try match goal with
           | [ H : Symbolic.get_reg _ _ = Some _ |- _ ]
             => eapply get_reg_of_R_regs in H; [ | eassumption .. ]
           end.
  all: lazymatch goal with
       | [ H : nth_error ?ls _ = Some (inl (inl ?r)), H' : Symbolic.get_reg _ (reg_index ?r) = _ |- _ ]
         => repeat match goal with
                   | [ H : Forall2 _ ls _ |- _ ]
                     => revert H
                   end
       | _ => idtac
       end.
  all: Foralls_to_nth_error.
  all: handle_eval_eval.
  all: repeat match goal with
              | [ H : eval_idx_Z ?G ?d ?e ?v, H' : forall a b, eval ?G ?d a b -> eval ?G' ?d' a b |- _ ]
                => apply H' in H; change (eval_idx_Z G' d' e v) in H
              end.
  all: handle_eval_eval.
  all: subst.
  all: try congruence.
  all: try specialize (Hreg_wide_enough _ eq_refl).
  all: lazymatch goal with
       | [ H : eval_idx_Z _ _ ?i ?v, H' : nth_error _ _ = Some (inl ?i), H'' : nth_error _ _ = Some (inl (inr ?i)) |- ?v = _ ]
         => revert H' H''
       | [ H : eval_idx_Z _ _ ?i ?v, H' : nth_error ?ls _ = Some (inl ?i) |- ?v = _ ]
         => revert H'
       | [ H : nth_error _ _ = Some ?r |- word.unsigned ?r = _ ]
         => revert H
       end.
  all: repeat match goal with
              | [ H : Forall2 _ ?lsa ?lsb |- context[nth_error ?ls] ]
                => first [ find_list_in ls lsa | find_list_in ls lsb ];
                   revert H
              end.
  all: Foralls_to_nth_error.
  all: intros.
  all: cbv [eval_idx_or_list_idx] in *.
  all: rewrite ?(fun x y => Z.land_ones (Semantics.get_reg x y)) in * by (clear; lia).
  all: rewrite ?(fun x y => Z.mod_small (Semantics.get_reg x y)) in * by now apply get_reg_bounded.
  all: split_iff.
  all: try specialize (Hreg_wide_enough _ eq_refl).
  all: repeat first [ match goal with
                      | [ H : forall v, (0 <= v < _)%Z -> eval_idx_Z _ _ ?a v -> _, H' : eval_idx_Z _ _ ?a ?v' |- _ ]
                        => specialize (fun H1 H2 => H v' (conj H1 H2))
                      | [ H : ?x = Some _, H' : ?x = None |- _ ]
                        => rewrite H in H'; inversion_option
                      | [ H : ?x = Some _, H' : ?x = Some _ |- _ ]
                        => rewrite H in H'; inversion_option
                      | [ H : Symbolic.get_reg _ _ = Some _ |- _ ]
                        => eapply get_reg_of_R_regs in H; [ | eassumption .. ]
                      end
                    | progress subst
                    | progress inversion_sum
                    | congruence
                    | progress specialize_by_assumption
                    | progress specialize_by (cbv [eval_idx_Z] in *; eauto)
                    | progress specialize_by apply get_reg_bounded
                    | progress handle_eval_eval ].
  all: repeat match goal with
              | [ H : eval_idx_Z ?G ?d ?e ?v, H' : forall a b, eval ?G ?d a b -> eval ?G' ?d' a b |- _ ]
                => apply H' in H; change (eval_idx_Z G' d' e v) in H
              end.
  all: handle_eval_eval.
  all: try congruence.
Time Qed.
