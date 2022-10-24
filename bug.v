(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "-projection-no-head-constant" "-w" "-redundant-canonical-projection" "-w" "-notation-overridden" "-w" "-deprecated-native-compiler-option" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/oddorder/theories" "odd_order" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/mathcomp" "mathcomp" "-top" "odd_order.PFsection13" "-native-compiler" "ondemand") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 2201 lines to 188 lines, then from 201 lines to 1446 lines, then from 1450 lines to 262 lines, then from 275 lines to 1971 lines, then from 1976 lines to 313 lines, then from 326 lines to 1408 lines, then from 1413 lines to 683 lines *)
(* coqc version 8.17+alpha compiled with OCaml 4.14.0
   coqtop version runner-xsmttqsu-project-6138686-concurrent-0:/builds/coq/coq/_build/default,(HEAD detached at 2dcf3f4) (2dcf3f4621d80cdec6e4cb691614a0d1ac516999)
   Expected coqc runtime on this file: 4.172 sec *)
Require Coq.NArith.BinNat.
Require Coq.NArith.Ndec.
Require Coq.PArith.BinPos.
Require Coq.setoid_ring.Field_tac.
Require Coq.setoid_ring.Field_theory.
Require Coq.setoid_ring.Ring.
Require Coq.ssr.ssrbool.
Require Coq.ssr.ssreflect.
Require Coq.ssr.ssrfun.
Require mathcomp.ssreflect.ssreflect.
Require mathcomp.ssreflect.ssrnotations.
Require mathcomp.ssreflect.ssrfun.
Require mathcomp.ssreflect.ssrbool.
Require mathcomp.ssreflect.eqtype.
Require mathcomp.ssreflect.ssrnat.
Require mathcomp.ssreflect.seq.
Require mathcomp.ssreflect.choice.
Require mathcomp.ssreflect.path.
Require mathcomp.ssreflect.fintype.
Require mathcomp.ssreflect.div.
Require mathcomp.ssreflect.tuple.
Require mathcomp.ssreflect.finfun.
Require mathcomp.ssreflect.bigop.
Require mathcomp.ssreflect.prime.
Require mathcomp.ssreflect.finset.
Require mathcomp.ssreflect.binomial.
Require mathcomp.algebra.ssralg.
Require mathcomp.ssreflect.generic_quotient.
Require mathcomp.algebra.ring_quotient.
Require mathcomp.algebra.countalg.
Require mathcomp.fingroup.fingroup.
Require mathcomp.fingroup.morphism.
Require mathcomp.fingroup.perm.
Require mathcomp.fingroup.automorphism.
Require mathcomp.fingroup.quotient.
Require mathcomp.fingroup.action.
Require mathcomp.algebra.finalg.
Require mathcomp.ssreflect.order.
Require mathcomp.algebra.poly.
Require mathcomp.ssreflect.ssrAC.
Require mathcomp.algebra.ssrnum.
Require mathcomp.algebra.ssrint.
Require mathcomp.algebra.rat.
Require mathcomp.algebra.zmodp.
Require mathcomp.algebra.matrix.
Require mathcomp.algebra.polydiv.
Require mathcomp.algebra.mxalgebra.
Require mathcomp.algebra.vector.
Require mathcomp.algebra.intdiv.
Require mathcomp.algebra.mxpoly.
Require mathcomp.algebra.polyXY.
Require mathcomp.fingroup.gproduct.
Require mathcomp.solvable.gfunctor.
Require mathcomp.solvable.commutator.
Require mathcomp.solvable.cyclic.
Require mathcomp.solvable.center.
Require mathcomp.solvable.pgroup.
Require mathcomp.solvable.gseries.
Require mathcomp.solvable.nilpotent.
Require mathcomp.solvable.sylow.
Require mathcomp.solvable.abelian.
Require mathcomp.character.mxrepresentation.
Require mathcomp.field.closed_field.
Require mathcomp.field.falgebra.
Require mathcomp.field.fieldext.
Require mathcomp.field.separable.
Require mathcomp.field.galois.
Require mathcomp.field.algebraics_fundamentals.
Require mathcomp.field.algC.
Require mathcomp.field.cyclotomic.
Require mathcomp.field.algnum.
Require mathcomp.character.classfun.
Require mathcomp.character.character.
Require mathcomp.solvable.finmodule.
Require mathcomp.solvable.maximal.
Require mathcomp.solvable.hall.
Require mathcomp.solvable.frobenius.
Require mathcomp.character.inertia.
Require mathcomp.character.integral_char.
Require mathcomp.character.vcharacter.
Require mathcomp.fingroup.presentation.
Require mathcomp.solvable.extremal.
Require mathcomp.character.mxabelem.
Require odd_order.BGsection1.
Require odd_order.BGsection2.
Require odd_order.wielandt_fixpoint.
Require odd_order.BGsection3.
Require odd_order.BGsection4.
Require odd_order.BGsection5.
Require odd_order.BGappendixAB.
Require odd_order.BGsection6.
Require odd_order.BGsection7.
Require odd_order.BGsection8.
Require odd_order.BGsection9.
Require odd_order.BGsection10.
Require odd_order.BGsection11.
Require odd_order.BGsection12.
Require odd_order.BGsection13.
Require odd_order.BGsection14.
Require odd_order.BGsection15.
Require odd_order.BGsection16.
Require odd_order.PFsection1.
Require odd_order.PFsection2.
Require odd_order.PFsection3.

Declare ML Module "coq-core.plugins.ltac".
Module Export AdmitTactic.
Module Import LocalFalse.
Inductive False : Prop := .
End LocalFalse.
Axiom proof_admitted : False.
Global Set Default Proof Mode "Classic".
Tactic Notation "admit" := abstract case proof_admitted.
End AdmitTactic.

Module Export odd_order_DOT_PFsection4_WRAPPED.
Module Export PFsection4.
 
 
Import mathcomp.ssreflect.ssreflect.
Import mathcomp.ssreflect.ssrbool.
Import mathcomp.ssreflect.ssrfun.
Import mathcomp.ssreflect.eqtype.
Import mathcomp.ssreflect.ssrnat.
Import mathcomp.ssreflect.seq.
Import mathcomp.ssreflect.path.
Import mathcomp.ssreflect.div.
Import mathcomp.ssreflect.choice.
Import mathcomp.ssreflect.fintype.
Import mathcomp.ssreflect.tuple.
Import mathcomp.ssreflect.finfun.
Import mathcomp.ssreflect.bigop.
Import mathcomp.ssreflect.order.
Import mathcomp.ssreflect.prime.
Import mathcomp.algebra.ssralg.
Import mathcomp.algebra.poly.
Import mathcomp.ssreflect.finset.
Import mathcomp.fingroup.fingroup.
Import mathcomp.fingroup.morphism.
Import mathcomp.fingroup.perm.
Import mathcomp.fingroup.automorphism.
Import mathcomp.fingroup.quotient.
Import mathcomp.fingroup.action.
Import mathcomp.solvable.gfunctor.
Import mathcomp.fingroup.gproduct.
Import mathcomp.solvable.center.
Import mathcomp.solvable.commutator.
Import mathcomp.algebra.zmodp.
Import mathcomp.solvable.cyclic.
Import mathcomp.solvable.pgroup.
Import mathcomp.solvable.nilpotent.
Import mathcomp.solvable.hall.
Import mathcomp.solvable.frobenius.
Import mathcomp.algebra.matrix.
Import mathcomp.algebra.mxalgebra.
Import mathcomp.character.mxrepresentation.
Import mathcomp.algebra.vector.
Import mathcomp.algebra.ssrnum.
Import mathcomp.field.algC.
Import mathcomp.character.classfun.
Import mathcomp.character.character.
Import mathcomp.character.inertia.
Import mathcomp.character.vcharacter.
Import odd_order.PFsection1.
Import odd_order.PFsection2.
Import odd_order.PFsection3.

 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GroupScope.
Import Order.TTheory.
Import GRing.Theory.
Import Num.Theory.
Local Open Scope ring_scope.

Section Four_1_to_2.

 

Variable gT : finGroupType.

Lemma vchar_pairs_orthonormal (X : {group gT}) (a b c d : 'CF(X)) u v :
    {subset (a :: b) <= 'Z[irr X]} /\ {subset (c :: d) <= 'Z[irr X]} ->
    orthonormal (a :: b) && orthonormal (c :: d) ->
    [&& u \is Creal, v \is Creal, u != 0 & v != 0] ->
    [&& '[a - b, u *: c - v *: d] == 0,
         (a - b) 1%g == 0 & (u *: c - v *: d) 1%g == 0] ->
    orthonormal [:: a; b; c; d].
Admitted.

Corollary orthonormal_vchar_diff_ortho (X : {group gT}) (a b c d : 'CF(X)) :
    {subset a :: b <= 'Z[irr X]} /\ {subset c :: d <= 'Z[irr X]} ->
    orthonormal (a :: b) && orthonormal (c :: d) ->
    [&& '[a - b, c - d] == 0, (a - b) 1%g == 0 & (c - d) 1%g == 0] ->
  '[a, c] = 0.
Admitted.

 
Definition primeTI_hypothesis (L K W W1 W2 : {set gT}) of W1 \x W2 = W :=
  [/\   [/\ K ><| W1 = L, W1 != 1, Hall L W1 & cyclic W1],
        [/\ W2 != 1, W2 \subset K & cyclic W2],
            {in W1^#, forall x, 'C_K[x] = W2}
   &    odd #|W|]%g.

End Four_1_to_2.

Arguments primeTI_hypothesis _ _%g _%g _%g _ _%g _%g.

Section Four_3_to_5.

Variables (gT : finGroupType) (L K W W1 W2 : {group gT}) (defW : W1 \x W2 = W).
Hypothesis ptiWL : primeTI_hypothesis L K defW.

Let V := cyclicTIset defW.
Let w1 := #|W1|.
Let w2 := #|W2|.

Let defL : K ><| W1 = L.
admit.
Defined.
Let ntW1 : W1 :!=: 1%g.
admit.
Defined.
Let cycW1 : cyclic W1.
admit.
Defined.
Let hallW1 : Hall L W1.
Admitted.

Let ntW2 : W2 :!=: 1%g.
admit.
Defined.
Let sW2K : W2 \subset K.
admit.
Defined.
Let cycW2 : cyclic W2.
admit.
Defined.
Let prKW1 : {in W1^#, forall x, 'C_K[x] = W2}.
Admitted.

Let oddW : odd #|W|.
admit.
Defined.

Let nsKL : K <| L.
Admitted.
Let sKL : K \subset L.
admit.
Defined.
Let sW1L : W1 \subset L.
Admitted.
Let sWL : W \subset L.
admit.
Defined.
Let sW1W : W1 \subset W.
admit.
Defined.
Let sW2W : W2 \subset W.
admit.
Defined.

Let coKW1 : coprime #|K| #|W1|.
admit.
Defined.
Let coW12 : coprime #|W1| #|W2|.
Admitted.

Let cycW : cyclic W.
admit.
Defined.
Let cWW : abelian W.
Admitted.
Let oddW1 : odd w1.
admit.
Defined.
Let oddW2 : odd w2.
admit.
Defined.

Let ntV : V != set0.
Admitted.

Let sV_V2 : V \subset W :\: W2.
Admitted.

Lemma primeTIhyp_quotient (M : {group gT}) :
    (W2 / M != 1)%g -> M \subset K -> M <| L ->
  {defWbar : (W1 / M) \x (W2 / M) = W / M
           & primeTI_hypothesis (L / M) (K / M) defWbar}%g.
Admitted.

 
Theorem normedTI_prTIset : normedTI (W :\: W2) L W.
Admitted.

 
Theorem prime_cycTIhyp : cyclicTI_hypothesis L defW.
Admitted.
Local Notation ctiW := prime_cycTIhyp.
Let sigma := cyclicTIiso ctiW.
Let w_ i j := cyclicTIirr defW i j.

Let Wlin k : 'chi[W]_k \is a linear_char.
Admitted.

 
Fact primeTIdIirr_key : unit.
Admitted.
Definition primeTIdIirr_def := dirr_dIirr (sigma \o prod_curry w_).
Definition primeTIdIirr := locked_with primeTIdIirr_key primeTIdIirr_def.
Definition primeTI_Iirr ij := (primeTIdIirr ij).2.
Local Notation mu2_ i j := 'chi_(primeTI_Iirr (i, j)).

 
Definition primeTIred j : 'CF(L) := \sum_i mu2_ i j.

End Four_3_to_5.

Section Four_6_t0_10.

End Four_6_t0_10.

End PFsection4.

End odd_order_DOT_PFsection4_WRAPPED.
Module Export PFsection4.
End PFsection4.
Import mathcomp.ssreflect.ssrbool.
Import mathcomp.ssreflect.ssrfun.
Import mathcomp.ssreflect.seq.
Import mathcomp.ssreflect.fintype.
Import mathcomp.ssreflect.tuple.
Import mathcomp.algebra.ssralg.
Import mathcomp.ssreflect.finset.
Import mathcomp.fingroup.fingroup.
Import mathcomp.algebra.vector.
Import mathcomp.character.classfun.
Import mathcomp.character.character.
Import mathcomp.character.vcharacter.

Set Implicit Arguments.
Unset Strict Implicit.
Import GroupScope.
Local Open Scope ring_scope.

Section InducedIrrs.

Variables (gT : finGroupType) (K L : {group gT}).
Implicit Types (A B : {set gT}) (H M : {group gT}).

Section KerIirr.

Definition Iirr_ker A := [set i | A \subset cfker 'chi[K]_i].

Definition Iirr_kerD B A := Iirr_ker A :\: Iirr_ker B.

End KerIirr.

Hypothesis nsKL : K <| L.

Section SeqInd.

Variable calX : {set (Iirr K)}.

Definition seqInd := undup [seq 'Ind[L] 'chi_i | i in calX].
Local Notation S := seqInd.

Lemma seqInd_on : {subset S <= 'CF(L, K)}.
Admitted.

End SeqInd.

Definition seqIndT := seqInd setT.

Definition seqIndD H M := seqInd (Iirr_kerD H M).

End InducedIrrs.

Section Five.

Variable gT : finGroupType.

Section Defs.

Variables L G : {group gT}.

Definition coherent_with S A tau (tau1 : {additive 'CF(L) -> 'CF(G)}) :=
  {in 'Z[S], isometry tau1, to 'Z[irr G]} /\ {in 'Z[S, A], tau1 =1 tau}.

Definition coherent S A tau := exists tau1, coherent_with S A tau tau1.

End Defs.

End Five.

Import mathcomp.ssreflect.ssreflect.
Import mathcomp.ssreflect.eqtype.
Import mathcomp.ssreflect.ssrnat.
Import mathcomp.ssreflect.div.
Import mathcomp.fingroup.gproduct.
Import mathcomp.solvable.frobenius.
Import odd_order.BGsection7.
Import odd_order.BGsection14.
Import odd_order.BGsection15.
Import odd_order.BGsection16.
Import odd_order.PFsection2.
Import GroupScope.

Notation "''R' [ x ]" := 'C_((gval 'N[x])`_\F)[x]
 (at level 8, format "''R' [ x ]")  : group_scope.

Section Definitions.

Variable gT : minSimpleOddGroupType.
Implicit Types L M X : {set gT}.

Definition FTsignalizer M x := if 'C[x] \subset M then 1%G else 'R[x]%G.

End Definitions.

Notation "''R_' M" := (FTsignalizer M)
 (at level 8, M at level 2, format "''R_' M") : group_scope.

Section Eight.

Variable gT : minSimpleOddGroupType.
Local Notation G := (TheMinSimpleOddGroup gT).

Section OneMaximal.

Variable M U W W1 W2 : {group gT}.

Hypothesis maxM : M \in 'M.

Lemma FTsupport_facts (X := 'A0(M)) (D := [set x in X | ~~('C[x] \subset M)]) :
  [/\   {in X &, forall x, {subset x ^: G <= x ^: M}},
        D \subset 'A1(M) /\ {in D, forall x, 'M('C[x]) = [set 'N[x]]}
    &   {in D, forall x (L := 'N[x]) (H := L`_\F),
        [/\   H ><| (M :&: L) = L /\ 'C_H[x] ><| 'C_M[x] = 'C[x],
              {in X, forall y, coprime #|H| #|'C_M[y]| },
              x \in 'A(L) :\: 'A1(L)
          &   1 <= FTtype L <= 2
                /\ (FTtype L == 2%N -> [Frobenius M with kernel M`_\F])]}].
Proof.
have defX: X \in pred2 'A(M) 'A0(M) by rewrite !inE eqxx orbT.
have [sDA1 part_a part_c] := BGsummaryII maxM defX.
have{} part_a: {in X &, forall x, {subset x ^: G <= x ^: M}}.
  move=> x y A0x A0y /= /imsetP[g Gg def_y]; rewrite def_y.
  by apply/imsetP/part_a; rewrite -?def_y.
do [split=> //; first split=> //] => x /part_c[_ ] //.
rewrite /= -(mem_iota 1) !inE => -> [-> ? -> -> L2_frob].
by do 2![split=> //] => /L2_frob[E /FrobeniusWker].
Qed.

Lemma norm_FTsupp0 : 'N('A0(M)) = M.
admit.
Defined.

Let is_FTsignalizer : is_Dade_signalizer G M 'A0(M) 'R_M.
admit.
Defined.

Lemma FT_Dade0_hyp : Dade_hypothesis G M 'A0(M).
Proof.
have [part_a _ parts_bc] := FTsupport_facts.
have /subsetD1P[sA0M notA0_1] := FTsupp0_sub M.
split; rewrite // /normal ?sA0M ?norm_FTsupp0 //=.
exists 'R_M => [|x y A0x A0y]; first exact: is_FTsignalizer.
rewrite /'R_M; case: ifPn => [_ | not_sCxM]; first by rewrite cards1 coprime1n.
rewrite (coprimeSg (subsetIl _ _)) //=.
by have [| _ -> //] := parts_bc x; apply/setIdP.
Qed.

End OneMaximal.

End Eight.

Notation FT_Dade0 maxM := (Dade (FT_Dade0_hyp maxM)).
Import mathcomp.ssreflect.bigop.
Import mathcomp.ssreflect.prime.
Import mathcomp.algebra.finalg.
Import mathcomp.algebra.zmodp.
Import mathcomp.solvable.gfunctor.
Import mathcomp.solvable.cyclic.
Import mathcomp.solvable.commutator.
Import mathcomp.solvable.abelian.
Import mathcomp.solvable.maximal.
Import mathcomp.field.algC.
Import odd_order.PFsection3.
Import GRing.Theory.

Section Thirteen.

Variable gT : minSimpleOddGroupType.
Local Notation G := (TheMinSimpleOddGroup gT).
Implicit Types H K L N P Q R S T U W : {group gT}.

Definition irr_Ind_Fitting S := [predI irr S & seqIndT 'F(S) S].

Local Notation irrIndH := (irr_Ind_Fitting _).
Local Notation "#1" := (inord 1) (at level 0).

Variables S U W W1 W2 : {group gT}.
Hypotheses (maxS : S \in 'M) (defW : W1 \x W2 = W).

Local Notation "` 'S'" := (gval S) (at level 0, only parsing) : group_scope.
Local Notation P := `S`_\F%G.
Local Notation "` 'P'" := `S`_\F (at level 0) : group_scope.
Local Notation PU := S^`(1)%G.
Local Notation C := 'C_U(`P)%G.
Local Notation H := 'F(S)%G.
Let ptiWS : primeTI_hypothesis S PU defW.
Admitted.
Let ctiWG : cyclicTI_hypothesis G defW.
Admitted.

Let ntW1 : W1 :!=: 1.
admit.
Defined.
Let ntW2 : W2 :!=: 1.
admit.
Defined.

Let p := #|W2|.
Let q := #|W1|.
Let u := #|U : C|.
Let pr_q : prime q.
Admitted.

Let nirrW1 : #|Iirr W1| = q.
Admitted.

Local Open Scope ring_scope.

Let sigma := (cyclicTIiso ctiWG).
Let w_ i j := (cyclicTIirr defW i j).
Local Notation eta_ i j := (sigma (w_ i j)).
Let mu_ := primeTIred ptiWS.

Local Notation tau := (FT_Dade0 maxS).

Let calS := seqIndD PU S P 1.

Lemma FTtypeP_facts :
  [/\   [/\ pred2 2 3 (FTtype S), q < p -> FTtype S == 2,
                [Frobenius U <*> W1 = U ><| W1] & abelian U],
        p.-abelem P /\ #|P| = p ^ q,
        u <= (p ^ q).-1 %/ p.-1,
        coherent calS S^# tau
    &   normedTI 'A0(S) G S /\ {in 'CF(S, 'A0(S)), tau =1 'Ind}]%N.
Admitted.

Lemma FTseqInd_TIred j : j != 0 -> mu_ j \in calS.
Admitted.

Local Notation calH := (seqIndT H S).

Lemma FTtypeP_Ind_Fitting_1 lambda : lambda \in calH -> lambda 1%g = (u * q)%:R.
Admitted.
Local Notation calHuq := FTtypeP_Ind_Fitting_1.

Lemma FTprTIred_Ind_Fitting j : j != 0 -> mu_ j \in calH.
Admitted.
Local Notation Hmu := FTprTIred_Ind_Fitting.

Let signW2 (b : bool) := iter b (@conjC_Iirr _ W2).

Let signW2K b : involutive (signW2 b).
Admitted.

Let signW2_eq0 b : {mono signW2 b: j / j == 0}.
Admitted.

Definition typeP_TIred_coherent tau1 :=
  exists2 b : bool, b -> p = 3%N
  & forall j, j != 0 -> tau1 (mu_ j) = (-1) ^+ b *: \sum_i eta_ i (signW2 b j).

Variable K : {group gT}.
Let G0 := ~: (class_support H G :|: class_support K G).

Variables (tau1 : {additive 'CF(S) -> 'CF(G)}) (lambda : 'CF(S)).

Hypothesis cohS : coherent_with calS S^# tau tau1.
Hypothesis cohSmu : typeP_TIred_coherent tau1.

Hypotheses (Slam : lambda \in calS) (irrHlam : irrIndH lambda).

Let cover_G0 : {in G0, forall x, tau1 lambda x != 0 \/ eta_ #1 0 x != 0}.
Proof.
have [[b _ Dtau1_mu] [/= Ilam Hlam]] := (cohSmu, andP irrHlam).
pose sum_eta1 := (-1) ^+ b *: \sum_i eta_ i #1.
have{Dtau1_mu} [j nz_j tau1muj]: exists2 j, j != 0 & tau1 (mu_ j) = sum_eta1.
  pose j := signW2 b #1; have nz: j != 0 by rewrite signW2_eq0 Iirr1_neq0.
  by exists j; rewrite // Dtau1_mu // signW2K.
move=> x; rewrite !inE => /norP[H'x _].
have{tau1muj} ->: tau1 lambda x = sum_eta1 x.
  rewrite -[lambda](subrK (mu_ j)) raddfD cfunE tau1muj.
  rewrite [tau1 _ x](cfun_on0 _ H'x) ?add0r {x H'x}//=.
  have Hmuj: mu_ j \in calH := Hmu nz_j.
  have dmu1: (lambda - mu_ j) 1%g == 0 by rewrite !cfunE !calHuq ?subrr.
  have H1dmu: lambda - mu_ j \in 'CF(S, H^#).
    by rewrite cfun_onD1 rpredB ?((seqInd_on (gFnormal _ _)) setT).
  have [_ ->] := cohS; last first.
    by rewrite zcharD1E ?rpredB ?mem_zchar ?FTseqInd_TIred /=.
  have A0dmu := cfun_onS (Fitting_sub_FTsupp0 maxS) H1dmu.
  have [_ _ _ _ [_ -> //]] := FTtypeP_facts.
  by rewrite cfInd_on ?subsetT // (cfun_onS _ H1dmu) ?imset2Sl ?subsetDl.
apply/nandP/andP=> [[/eqP sum_eta1x_0 /eqP eta1x_0]].
have cycW: cyclic W by have [] := ctiWG.
have W'x: x \notin class_support (cyclicTIset defW) G.
  apply: contra_eqN eta1x_0 => /imset2P[{H'x sum_eta1x_0}x g Wx Gg ->].
  rewrite cfunJ {g Gg}// cycTIiso_restrict //.
  by rewrite lin_char_neq0 ?irr_cyclic_lin //; case/setDP: Wx.
have nz_i1 : #1 != 0 :> Iirr W1 by rewrite Iirr1_neq0.
have eta_x_0 i: i != 0 -> eta_ i 0 x = 0.
  rewrite /w_ dprod_IirrEl => /(cfExp_prime_transitive pr_q nz_i1)[k co_k_p ->].
  have: coprime k #[w_ #1 0]%CF by rewrite /w_ dprod_IirrEl cforder_sdprod.
  rewrite rmorphX /= -dprod_IirrEl => /(cycTIiso_aut_exists ctiWG)[[uu ->] _].
  by rewrite cfunE /= -/sigma eta1x_0 rmorph0.
have eta_i1 i: i != 0 -> eta_ i #1 x = eta_ 0 #1 x - 1.
  move=> nz_i; apply/eqP; pose alpha := cfCyclicTIset defW i #1.
  have Walpha: alpha \in 'CF(W, cyclicTIset defW).
    by rewrite (cfCycTI_on ctiWG) ?Iirr1_neq0.
  have: sigma alpha x == 0.
    by rewrite cycTIiso_Ind // (cfun_on0 _ W'x) ?cfInd_on ?subsetT.
  rewrite [alpha]cfCycTI_E linearD !linearB /= !cfunE cycTIiso1 cfun1E inE.
  by rewrite {1}eta_x_0 //= subr0 addrC addr_eq0 opprB.
have eta11x: eta_ #1 #1 x = - (q%:R)^-1.
  rewrite -mulN1r; apply: canRL (mulfK (neq0CG W1)) _.
  transitivity ((-1) ^+ b * sum_eta1 x - 1); last first.
    by rewrite sum_eta1x_0 mulr0 add0r.
  rewrite cfunE signrMK mulr_natr -/q -nirrW1 -sumr_const sum_cfunE.
  by rewrite !(bigD1 0 isT) /= addrAC eta_i1 // (eq_bigr _ eta_i1).
