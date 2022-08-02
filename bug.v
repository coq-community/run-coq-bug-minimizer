(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-noinit" "-indices-matter" "-w" "-deprecated-native-compiler-option" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/hott/theories" "HoTT" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/hott/contrib" "HoTT.Contrib" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-top" "Top.bug_01" "-native-compiler" "no") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 203 lines to 268 lines, then from 260 lines to 255 lines, then from 260 lines to 255 lines, then from 260 lines to 255 lines, then from 260 lines to 255 lines, then from 260 lines to 255 lines, then from 260 lines to 173 lines, then from 178 lines to 173 lines, then from 178 lines to 185 lines, then from 188 lines to 185 lines, then from 188 lines to 183 lines, then from 188 lines to 184 lines, then from 188 lines to 185 lines, then from 188 lines to 183 lines, then from 188 lines to 183 lines, then from 188 lines to 183 lines *)
(* coqc version 8.17+alpha compiled with OCaml 4.09.0
   coqtop version runner-jlguopmm-project-6138686-concurrent-0:/builds/coq/coq/_build/default,(HEAD detached at 2126e71) (2126e716343beaf48faa330d47a3a6eb5886a6bf)
   Expected coqc runtime on this file: 0.224 sec *)
Require HoTT.Basics.Notations.
Require HoTT.Basics.Logic.
Require HoTT.Basics.Datatypes.
Require HoTT.Basics.Overture.
Require HoTT.Basics.Decimal.
Require HoTT.Basics.Hexadecimal.
Require HoTT.Basics.Numeral.
Require HoTT.Basics.Nat.
Require HoTT.Basics.Tactics.
Require HoTT.Basics.PathGroupoids.
Require HoTT.Basics.UniverseLevel.
Require HoTT.Basics.Contractible.
Require HoTT.Basics.Equivalences.
Require HoTT.Basics.Trunc.
Require HoTT.Basics.Decidable.
Require HoTT.Basics.Utf8.
Require HoTT.Basics.
Require HoTT.Types.Unit.
Require HoTT.Types.Empty.
Require HoTT.Types.Paths.
Require HoTT.Types.Prod.
Require HoTT.Types.Forall.
Require HoTT.Types.Arrow.
Require HoTT.Types.Sigma.
Require HoTT.Types.Equiv.
Require HoTT.Types.Bool.
Require HoTT.Types.Universe.
Require HoTT.Types.Sum.
Require HoTT.Types.WType.
Require HoTT.Types.IWType.
Require HoTT.Types.
Require HoTT.Cubical.DPath.
Require HoTT.Cubical.PathSquare.
Require HoTT.Cubical.DPathSquare.
Require HoTT.Cubical.PathCube.
Require HoTT.Cubical.DPathCube.
Require HoTT.Cubical.
Require HoTT.HProp.
Require HoTT.HSet.
Require HoTT.Spaces.Pos.Core.
Require HoTT.Spaces.Pos.Spec.
Require HoTT.Spaces.Pos.
Require HoTT.Spaces.Int.Core.
Require HoTT.Spaces.Int.Spec.
Require HoTT.Spaces.Int.Equiv.
Require HoTT.Spaces.Int.LoopExp.
Require HoTT.Spaces.Int.
Require HoTT.Colimits.GraphQuotient.
Require HoTT.Colimits.Coeq.
Require HoTT.Diagrams.CommutativeSquares.
Require HoTT.HFiber.
Require HoTT.Equiv.PathSplit.
Require HoTT.PathAny.
Require HoTT.WildCat.Core.
Require HoTT.WildCat.Equiv.
Require HoTT.WildCat.Square.
Require HoTT.WildCat.NatTrans.
Require HoTT.WildCat.Prod.
Require HoTT.WildCat.Induced.
Require HoTT.WildCat.FunctorCat.
Require HoTT.WildCat.Opposite.
Require HoTT.WildCat.Universe.
Require HoTT.WildCat.Yoneda.
Require HoTT.WildCat.Adjoint.
Require HoTT.WildCat.Sigma.
Require HoTT.WildCat.EquivGpd.
Require HoTT.WildCat.PointedCat.
Require HoTT.WildCat.Paths.
Require HoTT.WildCat.UnitCat.
Require HoTT.WildCat.EmptyCat.
Require HoTT.WildCat.Sum.
Require HoTT.WildCat.Forall.
Require HoTT.WildCat.TwoOneCat.
Require HoTT.WildCat.
Require HoTT.TruncType.
Require HoTT.Colimits.Pushout.
Require HoTT.Colimits.MappingCylinder.
Require HoTT.Extensions.
Require HoTT.Factorization.
Require HoTT.NullHomotopy.
Require HoTT.Limits.Pullback.
Require HoTT.Equiv.BiInv.
Require HoTT.Modalities.ReflectiveSubuniverse.
Require HoTT.Modalities.Modality.
Require HoTT.Modalities.Accessible.
Require HoTT.Modalities.Localization.
Require HoTT.Modalities.Descent.
Require HoTT.Truncations.Core.
Require HoTT.Homotopy.Suspension.
Require HoTT.Modalities.Separated.
Require HoTT.Truncations.Connectedness.
Require HoTT.Truncations.
Require HoTT.Spaces.Circle.
Require HoTT.Spaces.Torus.Torus.

Declare ML Module "coq-core.plugins.ltac".
Module Export AdmitTactic.
Module Import LocalFalse.
Inductive False : Prop := .
End LocalFalse.
Axiom proof_admitted : False.
Global Set Default Proof Mode "Classic".
Tactic Notation "admit" := abstract case proof_admitted.
End AdmitTactic.
Import HoTT.Basics HoTT.Types.
Import HoTT.Cubical.
Import HoTT.Spaces.Circle HoTT.Spaces.Torus.Torus.

Section TorusEquivCircle.

  Context `{Funext}.

  Definition c2t_square_and_cube
    : {s : PathSquare loop_a loop_a
        (ap (Circle_rec _ tbase loop_b) loop)
        (ap (Circle_rec _ tbase loop_b) loop)
      &  PathCube s surf hr hr
         (sq_G1 (Circle_rec_beta_loop _ _ _))
         (sq_G1 (Circle_rec_beta_loop _ _ _))}.
  Proof.
    apply cu_fill_left.
  Defined.

  Definition t2c : Torus -> Circle * Circle.
  Proof.
    srapply Torus_rec.
    +
 exact (base, base).

    +
 exact (path_prod' loop 1).

    +
 exact (path_prod' 1 loop).

    +
 exact (sq_prod (hr, vr)).

  Defined.

  Definition c2t' : Circle -> Circle -> Torus.
  Proof.
    srapply Circle_rec.
    +
 srapply Circle_rec.

      -
 exact tbase.

      -
 exact loop_b.

    +
 apply path_forall.

      srapply Circle_ind_dp.

      -
 exact loop_a.

      -
 srapply sq_dp^-1.

        apply (pr1 c2t_square_and_cube).

  Defined.

  Definition c2t : Circle * Circle -> Torus.
  Proof.
    apply uncurry, c2t'.
  Defined.

  Definition c2t'_beta :
    {bl1 : PathSquare (ap (fun y => c2t' base y) loop) loop_b 1 1 &
    {bl2 : PathSquare (ap (fun x => c2t' x base) loop) loop_a 1 1 &
    PathCube (sq_ap011 c2t' loop loop) surf bl2 bl2 bl1 bl1}}.
  Proof.
    refine (_;_;_).
    unfold sq_ap011.

    refine (cu_concat_lr (cu_ds (dp_apD_nat
      (fun y => ap_compose _ (fun f => f y) _) _)) _
      (sji0:=?[X1]) (sji1:=?X1) (sj0i:=?[Y1]) (sj1i:=?Y1) (pj11:=1)).
