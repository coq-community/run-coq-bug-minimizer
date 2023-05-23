(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "+implicit-core-hint-db,+implicits-in-term,+non-reversible-notation,+deprecated-intros-until-0,+deprecated-focus,+unused-intro-pattern,+deprecated-hint-constr,+fragile-hint-constr,+variable-collision,+unexpected-implicit-declaration,+omega-is-deprecated,+deprecated-instantiate-syntax,+non-recursive,+deprecated-hint-rewrite-without-locality,+deprecated-hint-without-locality,+deprecated-instance-without-locality,+undeclared-scope,+deprecated-typeclasses-transparency-without-locality,+future-coercion-class-field,unsupported-attributes" "-w" "-notation-overridden,-unusable-identifier" "-w" "-notation-overridden" "-w" "-deprecated-native-compiler-option" "-native-compiler" "ondemand" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/rewriter/src/Rewriter" "Rewriter" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-I" "/github/workspace/builds/coq/coq-failing/_build_ci/rewriter/src/Rewriter/Util/plugins" "-top" "Rewriter.Rewriter.Examples") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 138 lines to 269 lines, then from 273 lines to 467 lines, then from 472 lines to 300 lines, then from 306 lines to 300 lines *)
(* coqc version 8.18+alpha compiled with OCaml 4.14.1
   coqtop version runner-zseo-lx5-project-6138686-concurrent-0:/builds/coq/coq/_build/default,(HEAD detached at 0e442216b9) (0e442216b96435abd04509c68407249a51da5dec)
   Modules that could not be inlined: Rewriter.Util.plugins.RewriterBuildRegistry
   Expected coqc runtime on this file: 33.028 sec *)
Require Coq.Init.Ltac.
Require Coq.ZArith.ZArith.
Require Coq.micromega.Lia.
Require Coq.Lists.List.
Require Coq.Lists.SetoidList.
Require Coq.Arith.Peano_dec.
Require Coq.Arith.Arith.
Require Coq.Classes.Morphisms.
Require Coq.Numbers.Natural.Peano.NPeano.
Require Coq.Logic.Eqdep_dec.
Require Coq.NArith.NArith.
Require Coq.Relations.Relation_Definitions.
Require Rewriter.Util.NatUtil.
Require Coq.Numbers.BinNums.
Require Rewriter.Util.Pointed.
Require Coq.Setoids.Setoid.
Require Coq.Bool.Bool.
Require Coq.Classes.RelationClasses.
Require Rewriter.Util.IffT.
Require Rewriter.Util.Isomorphism.
Require Rewriter.Util.HProp.
Require Rewriter.Util.Equality.
Require Rewriter.Util.GlobalSettings.
Require Rewriter.Util.Prod.
Require Rewriter.Util.FixCoqMistakes.
Require Rewriter.Util.Sigma.
Require Coq.ZArith.BinInt.
Require Coq.ZArith.ZArith_dec.
Require Coq.NArith.BinNat.
Require Rewriter.Util.Decidable.
Require Rewriter.Util.Tactics.Head.
Require Rewriter.Util.Tactics.BreakMatch.
Require Rewriter.Util.Tactics.DestructHyps.
Require Rewriter.Util.Tactics.DestructHead.
Require Rewriter.Util.Notations.
Require Rewriter.Util.Option.
Require Rewriter.Util.Tactics.SpecializeBy.
Require Rewriter.Util.Tactics.Test.
Require Rewriter.Util.Tactics.Not.
Require Rewriter.Util.Tactics.DoWithHyp.
Require Rewriter.Util.Tactics.RewriteHyp.
Require Rewriter.Util.Tactics.ConstrFail.
Require Rewriter.Util.Tactics.SplitInContext.
Require Rewriter.Util.ListUtil.
Require Rewriter.Util.Tactics.GetGoal.
Require Rewriter.Util.LetIn.
Require Ltac2.Init.
Require Rewriter.Util.PrimitiveProd.
Require Rewriter.Util.PrimitiveHList.
Require Rewriter.Util.InductiveHList.
Require Rewriter.Language.PreCommon.
Require Rewriter.Language.Pre.
Require Rewriter.Util.Bool.
Require Rewriter.Language.PreLemmas.
Require Ltac2.Int.
Require Ltac2.Message.
Require Ltac2.Control.
Require Ltac2.Bool.
Require Ltac2.Array.
Require Ltac2.Char.
Require Ltac2.Constant.
Require Ltac2.Constr.
Require Ltac2.Constructor.
Require Ltac2.Std.
Require Ltac2.Env.
Require Ltac2.Evar.
Require Ltac2.Float.
Require Ltac2.List.
Require Ltac2.Fresh.
Require Ltac2.Ident.
Require Ltac2.Ind.
Require Ltac2.Ltac1.
Require Ltac2.Meta.
Require Ltac2.Option.
Require Ltac2.Pattern.
Require Ltac2.Printf.
Require Ltac2.Proj.
Require Ltac2.String.
Require Ltac2.Uint63.
Require Ltac2.Notations.
Require Ltac2.Ltac2.
Require Coq.FSets.FMapPositive.
Require Rewriter.Util.OptionList.
Require Rewriter.Util.CPSNotations.
Require Coq.Classes.CMorphisms.
Require Coq.Strings.String.
Require Coq.Strings.Ascii.
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
Require Rewriter.Util.Tactics2.InstantiateEvar.
Require Rewriter.Util.Tactics2.Constr.Unsafe.MakeAbbreviations.
Require Rewriter.Util.Tactics2.FixNotationsForPerformance.
Require Rewriter.Language.Reify.
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
Require Coq.MSets.MSetPositive.
Require Coq.Program.Tactics.
Require Coq.Relations.Relations.
Require Rewriter.Util.ListUtil.Forall.
Require Rewriter.Util.Logic.ProdForall.
Require Rewriter.Language.Wf.
Require Rewriter.Language.UnderLetsProofs.
Require Coq.derive.Derive.
Require Rewriter.Util.PrimitiveSigma.
Require Rewriter.Language.IdentifiersLibrary.
Require Coq.MSets.MSetFacts.
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

Module Export AdmitTactic.
Module Import LocalFalse.
Inductive False : Prop := .
End LocalFalse.
Axiom proof_admitted : False.
Import Coq.Init.Ltac.
Tactic Notation "admit" := abstract case proof_admitted.
End AdmitTactic.

Module Rewriter_DOT_Util_DOT_plugins_DOT_RewriterBuild_WRAPPED.
Module RewriterBuild.
Import Rewriter.Util.plugins.RewriterBuildRegistry.

Declare ML Module "coq-rewriter.rewriter_build".

Ltac Rewrite_lhs_for verified_rewriter_package := RewriteRules.Tactic.Rewrite_lhs_for verified_rewriter_package.
Ltac Rewrite_rhs_for verified_rewriter_package := RewriteRules.Tactic.Rewrite_rhs_for verified_rewriter_package.
Ltac Rewrite_for verified_rewriter_package := RewriteRules.Tactic.Rewrite_for verified_rewriter_package.

Export Pre.RewriteRuleNotations.
Export IdentifiersGenerateProofs.Compilers.pattern.ProofTactic.Settings.

End RewriterBuild.

End Rewriter_DOT_Util_DOT_plugins_DOT_RewriterBuild_WRAPPED.
Module Export Rewriter_DOT_Util_DOT_plugins_DOT_RewriterBuild.
Module Export Rewriter.
Module Export Util.
Module Export plugins.
Module RewriterBuild.
Include Rewriter_DOT_Util_DOT_plugins_DOT_RewriterBuild_WRAPPED.RewriterBuild.
End RewriterBuild.

End plugins.

End Util.

End Rewriter.

End Rewriter_DOT_Util_DOT_plugins_DOT_RewriterBuild.
Import Coq.ZArith.ZArith.
Import Coq.micromega.Lia.
Import Coq.Lists.List.
Import Rewriter.Util.ListUtil.
Import Rewriter.Util.LetIn.
Import Rewriter.Util.Notations.
Import Rewriter.Util.plugins.RewriterBuild.
Import ListNotations.
Local Open Scope bool_scope.
Local Open Scope Z_scope.

Time Make norules := Rewriter For ().

Example ex1 : forall x : nat, x = x.
Proof.
  Rewrite_for norules.
  lazymatch goal with
  | |- ?x = ?x => is_var x; reflexivity
  end.
Qed.

Example ex2 : forall x : nat, id x = id x.
Proof.
  Rewrite_for norules.
  lazymatch goal with
  | |- ?x = ?x => is_var x; reflexivity
  end.
Qed.

Local Ltac t :=
  repeat constructor; cbn [snd]; cbv [ident.eagerly]; intros;
  try solve [ lia
            | now apply ListUtil.eq_app_list_rect ].

Lemma map_eagerly_rect
  : forall A B f ls, @List.map A B f ls
                     = (ident.eagerly (@list_rect) _ _)
                         []
                         (fun x xs map_f_xs => f x :: map_f_xs)
                         ls.
Proof.
t.
Qed.

Lemma app_eagerly_rect
  : forall A xs ys, @List.app A xs ys
                    = (ident.eagerly (@list_rect) _ _)
                        ys (fun x xs app_xs_ys => x :: app_xs_ys) xs.
Proof.
t.
Qed.

Lemma flat_map_rect
  : forall A B f xs,
    @List.flat_map A B f xs
    = (list_rect (fun _ => _))
        nil
        (fun x _ flat_map_tl => f x ++ flat_map_tl)%list
        xs.
Proof.
t.
Qed.

Module ForDebugging.
  Definition rules_proofs :=
    Eval cbv [projT2] in
      projT2
        (ltac:(RewriterBuildRegistry.make_rules_proofs_with_args)
          : Pre.rules_proofsT_with_args
              (Z.add_0_r
                , (@Prod.fst_pair)
                , (@Prod.snd_pair)
                , map_eagerly_rect
                , app_eagerly_rect
                , eval_rect list
                , do_again flat_map_rect)).

  Definition scraped_data :=
    (ltac:(cbv [projT1]; RewriterBuildRegistry.make_scraped_data_with_args)
      : PreCommon.Pre.ScrapedData.t_with_args
          rules_proofs
            false).

  Rewriter Emit Inductives From Scraped scraped_data As base ident raw_ident pattern_ident.

  Definition myrules : ProofsCommon.Compilers.RewriteRules.GoalType.VerifiedRewriter_with_ind_args
          scraped_data InductiveHList.nil base ident raw_ident pattern_ident   false   false   true rules_proofs.
Set Ltac Debug.
Set Ltac Batch Debug.
    RewriterBuildRegistry.make_verified_rewriter_with_args.
