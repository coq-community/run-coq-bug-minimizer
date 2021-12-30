(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "-projection-no-head-constant" "-w" "-redundant-canonical-projection" "-w" "-notation-overridden" "-w" "+duplicate-clear" "-w" "-ambiguous-paths" "-w" "+non-primitive-record" "-w" "+undeclared-scope" "-w" "-deprecated-hint-without-locality" "-w" "-deprecated-ident-entry" "-w" "-deprecated-native-compiler-option" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/mathcomp/mathcomp" "mathcomp" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-I" "/github/workspace/builds/coq/coq-failing/_build_ci/mathcomp/mathcomp" "-top" "mxrepresentation" "-native-compiler" "ondemand") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 5928 lines to 3548 lines *)
(* coqc version 8.15+alpha compiled with OCaml 4.13.0
   coqtop version runner-z3wu8uu--project-6138686-concurrent-0:/builds/coq/coq/_build/default,(HEAD detached at 0d1a2eb) (0d1a2eb7ba6a7719f37495807fb9fa49623ac075)
   Expected coqc runtime on this file: 5.177 sec *)
Require Coq.ssr.ssreflect.
Require mathcomp.ssreflect.ssreflect.
Require Coq.ssr.ssrfun.
Require mathcomp.ssreflect.ssrnotations.
Require mathcomp.ssreflect.ssrfun.
Require Coq.ssr.ssrbool.
Require mathcomp.ssreflect.ssrbool.
Require mathcomp.ssreflect.eqtype.
Require Coq.NArith.BinNat.
Require Coq.PArith.BinPos.
Require Coq.NArith.Ndec.
Require Coq.setoid_ring.Ring.
Require mathcomp.ssreflect.ssrnat.
Require mathcomp.ssreflect.seq.
Require mathcomp.ssreflect.path.
Require mathcomp.ssreflect.div.
Require mathcomp.ssreflect.choice.
Require mathcomp.ssreflect.fintype.
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
Require mathcomp.algebra.poly.
Require mathcomp.algebra.polydiv.
Require mathcomp.fingroup.fingroup.
Require mathcomp.fingroup.morphism.
Require mathcomp.fingroup.perm.
Require mathcomp.fingroup.automorphism.
Require mathcomp.fingroup.quotient.
Require mathcomp.fingroup.action.
Require mathcomp.algebra.finalg.
Require mathcomp.algebra.zmodp.
Require mathcomp.fingroup.gproduct.
Require mathcomp.solvable.gfunctor.
Require mathcomp.solvable.commutator.
Require mathcomp.solvable.cyclic.
Require mathcomp.solvable.center.
Require mathcomp.solvable.pgroup.
Require mathcomp.ssreflect.order.
Require mathcomp.algebra.matrix.
Require mathcomp.algebra.mxalgebra.
Require mathcomp.algebra.mxpoly.

Declare ML Module "ltac_plugin".
Module Export AdmitTactic.
Module Import LocalFalse.
Inductive False : Prop := .
End LocalFalse.
Axiom proof_admitted : False.
Global Set Default Proof Mode "Classic".
Tactic Notation "admit" := abstract case proof_admitted.
End AdmitTactic.
Import mathcomp.ssreflect.ssreflect mathcomp.ssreflect.ssrbool mathcomp.ssreflect.ssrfun mathcomp.ssreflect.eqtype mathcomp.ssreflect.ssrnat mathcomp.ssreflect.seq mathcomp.ssreflect.path.
Import mathcomp.ssreflect.div mathcomp.ssreflect.choice mathcomp.ssreflect.fintype mathcomp.ssreflect.tuple mathcomp.ssreflect.finfun mathcomp.ssreflect.bigop mathcomp.ssreflect.prime.
Import mathcomp.algebra.ssralg mathcomp.algebra.poly mathcomp.algebra.polydiv mathcomp.ssreflect.finset mathcomp.fingroup.fingroup mathcomp.fingroup.morphism.
Import mathcomp.fingroup.perm mathcomp.fingroup.automorphism mathcomp.fingroup.quotient mathcomp.algebra.finalg mathcomp.fingroup.action mathcomp.algebra.zmodp.
Import mathcomp.solvable.commutator mathcomp.solvable.cyclic mathcomp.solvable.center mathcomp.solvable.pgroup mathcomp.algebra.matrix mathcomp.algebra.mxalgebra.
Import mathcomp.algebra.mxpoly.

 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope irrType_scope.
Declare Scope group_ring_scope.

Import GroupScope GRing.Theory.
Local Open Scope ring_scope.

Reserved Notation "''n_' i" (at level 8, i at level 2, format "''n_' i").
Reserved Notation "''R_' i" (at level 8, i at level 2, format "''R_' i").
Reserved Notation "''e_' i" (at level 8, i at level 2, format "''e_' i").

Delimit Scope irrType_scope with irr.

Section RingRepr.

Variable R : comUnitRingType.

Section OneRepresentation.

Variable gT : finGroupType.

Definition mx_repr (G : {set gT}) n (r : gT -> 'M[R]_n) :=
  r 1%g = 1%:M /\ {in G &, {morph r : x y / (x * y)%g >-> x *m y}}.

Structure mx_representation G n :=
  MxRepresentation { repr_mx :> gT -> 'M_n; _ : mx_repr G repr_mx }.

Variables (G : {group gT}) (n : nat) (rG : mx_representation G n).
Arguments rG _%group_scope : extra scopes.

Lemma repr_mx1 : rG 1 = 1%:M.
Proof.
by case: rG => r [].
Qed.

Lemma repr_mxM : {in G &, {morph rG : x y / (x * y)%g >-> x *m y}}.
Proof.
by case: rG => r [].
Qed.

Lemma repr_mxK m x :
  x \in G ->  cancel ((@mulmx R m n n)^~ (rG x)) (mulmx^~ (rG x^-1)).
Proof.
by move=> Gx U; rewrite -mulmxA -repr_mxM ?groupV // mulgV repr_mx1 mulmx1.
Qed.

Lemma repr_mxKV m x :
  x \in G -> cancel ((@mulmx R m n n)^~ (rG x^-1)) (mulmx^~ (rG x)).
Proof.
by rewrite -groupV -{3}[x]invgK; apply: repr_mxK.
Qed.

Lemma repr_mx_unit x : x \in G -> rG x \in unitmx.
Proof.
by move=> Gx; case/mulmx1_unit: (repr_mxKV Gx 1%:M).
Qed.

Lemma repr_mxV : {in G, {morph rG : x / x^-1%g >-> invmx x}}.
Proof.
by move=> x Gx /=; rewrite -[rG x^-1](mulKmx (repr_mx_unit Gx)) mulmxA repr_mxK.
Qed.

 
 
Definition enveloping_algebra_mx := \matrix_(i < #|G|) mxvec (rG (enum_val i)).

Section Stabiliser.

Variables (m : nat) (U : 'M[R]_(m, n)).

Definition rstab := [set x in G | U *m rG x == U].

Lemma rstab_sub : rstab \subset G.
Proof.
by apply/subsetP=> x; case/setIdP.
Qed.

Lemma rstab_group_set : group_set rstab.
Proof.
apply/group_setP; rewrite inE group1 repr_mx1 mulmx1; split=> //= x y.
case/setIdP=> Gx cUx; case/setIdP=> Gy cUy; rewrite inE repr_mxM ?groupM //.
by rewrite mulmxA (eqP cUx).
Qed.
Canonical rstab_group := Group rstab_group_set.

End Stabiliser.

 
Section CentHom.

Variable f : 'M[R]_n.

Definition rcent := [set x in G | f *m rG x == rG x *m f].

Lemma rcent_sub : rcent \subset G.
Proof.
by apply/subsetP=> x; case/setIdP.
Qed.

Lemma rcent_group_set : group_set rcent.
Proof.
apply/group_setP; rewrite inE group1 repr_mx1 mulmx1 mul1mx; split=> //= x y.
case/setIdP=> Gx; move/eqP=> cfx; case/setIdP=> Gy; move/eqP=> cfy.
by rewrite inE repr_mxM ?groupM //= -mulmxA -cfy !mulmxA cfx.
Qed.
Canonical rcent_group := Group rcent_group_set.

Definition centgmx := G \subset rcent.

Lemma centgmxP : reflect (forall x, x \in G -> f *m rG x = rG x *m f) centgmx.
Proof.
by apply: (iffP subsetP) => cGf x Gx; have /[!(inE, Gx)] /eqP := cGf x Gx.
Qed.

End CentHom.

 

Definition rker := rstab 1%:M.
Canonical rker_group := Eval hnf in [group of rker].

Lemma rkerP x : reflect (x \in G /\ rG x = 1%:M) (x \in rker).
Proof.
by apply: (iffP setIdP) => [] [->]; move/eqP; rewrite mul1mx.
Qed.

Lemma rker_norm : G \subset 'N(rker).
Proof.
apply/subsetP=> x Gx; rewrite inE sub_conjg; apply/subsetP=> y.
case/rkerP=> Gy ry1; rewrite mem_conjgV !inE groupJ //=.
by rewrite !repr_mxM ?groupM ?groupV // ry1 !mulmxA mulmx1 repr_mxKV.
Qed.

Lemma rker_normal : rker <| G.
Proof.
by rewrite /normal rstab_sub rker_norm.
Qed.

Definition mx_faithful := rker \subset [1].

Lemma mx_faithful_inj : mx_faithful -> {in G &, injective rG}.
Proof.
move=> ffulG x y Gx Gy eq_rGxy; apply/eqP; rewrite eq_mulgV1 -in_set1.
rewrite (subsetP ffulG) // inE groupM ?repr_mxM ?groupV //= eq_rGxy.
by rewrite mulmxA repr_mxK.
Qed.

Lemma rker_linear : n = 1%N -> G^`(1)%g \subset rker.
Proof.
move=> n1; rewrite gen_subG; apply/subsetP=> xy; case/imset2P=> x y Gx Gy ->.
rewrite !inE groupR //= /commg mulgA -invMg repr_mxM ?groupV ?groupM //.
rewrite mulmxA (can2_eq (repr_mxK _) (repr_mxKV _)) ?groupM //.
rewrite !repr_mxV ?repr_mxM ?groupM //; move: (rG x) (rG y).
by rewrite n1 => rx ry; rewrite (mx11_scalar rx) scalar_mxC.
Qed.

 

Definition rcenter := [set g in G | is_scalar_mx (rG g)].

Fact rcenter_group_set : group_set rcenter.
Proof.
apply/group_setP; split=> [|x y].
  by rewrite inE group1 repr_mx1 scalar_mx_is_scalar.
move=> /setIdP[Gx /is_scalar_mxP[a defx]] /setIdP[Gy /is_scalar_mxP[b defy]].
by rewrite !inE groupM ?repr_mxM // defx defy -scalar_mxM ?scalar_mx_is_scalar.
Qed.
Canonical rcenter_group := Group rcenter_group_set.

Lemma rcenter_normal : rcenter <| G.
Proof.
rewrite /normal /rcenter {1}setIdE subsetIl; apply/subsetP=> x Gx /[1!inE].
apply/subsetP=> _ /imsetP[y /setIdP[Gy /is_scalar_mxP[c rGy]] ->].
rewrite inE !repr_mxM ?groupM ?groupV //= mulmxA rGy scalar_mxC repr_mxKV //.
exact: scalar_mx_is_scalar.
Qed.

End OneRepresentation.

Arguments rkerP {gT G n rG x}.

Section Proper.

Variables (gT : finGroupType) (G : {group gT}) (n' : nat).
Local Notation n := n'.+1.
Variable rG : mx_representation G n.

Lemma repr_mxMr : {in G &, {morph rG : x y / (x * y)%g >-> x * y}}.
Proof.
exact: repr_mxM.
Qed.

Lemma repr_mxVr : {in G, {morph rG : x / (x^-1)%g >-> x^-1}}.
Proof.
exact: repr_mxV.
 Qed.

Lemma repr_mx_unitr x : x \in G -> rG x \is a GRing.unit.
Proof.
exact: repr_mx_unit.
Qed.

Lemma repr_mxX m : {in G, {morph rG : x / (x ^+ m)%g >-> x ^+ m}}.
Proof.
elim: m => [|m IHm] x Gx; rewrite /= ?repr_mx1 // expgS exprS -IHm //.
by rewrite repr_mxM ?groupX.
Qed.

End Proper.

Section ChangeGroup.

Variables (gT : finGroupType) (G H : {group gT}) (n : nat).
Variables (rG : mx_representation G n).

Section SubGroup.

Hypothesis sHG : H \subset G.

Lemma subg_mx_repr : mx_repr H rG.
Proof.
by split=> [|x y Hx Hy]; rewrite (repr_mx1, repr_mxM) ?(subsetP sHG).
Qed.
Definition subg_repr := MxRepresentation subg_mx_repr.
Local Notation rH := subg_repr.

Lemma rcent_subg U : rcent rH U = H :&: rcent rG U.
Proof.
by apply/setP=> x; rewrite !inE andbA -in_setI (setIidPl sHG).
Qed.

Section Stabiliser.

Variables (m : nat) (U : 'M[R]_(m, n)).

Lemma rstab_subg : rstab rH U = H :&: rstab rG U.
Proof.
by apply/setP=> x; rewrite !inE andbA -in_setI (setIidPl sHG).
Qed.

End Stabiliser.

Lemma rker_subg : rker rH = H :&: rker rG.
Proof.
exact: rstab_subg.
Qed.

Lemma subg_mx_faithful : mx_faithful rG -> mx_faithful rH.
Proof.
by apply: subset_trans; rewrite rker_subg subsetIr.
Qed.

End SubGroup.

Section SameGroup.

Hypothesis eqGH : G :==: H.

Lemma eqg_repr_proof : H \subset G.
Proof.
by rewrite (eqP eqGH).
Qed.

Definition eqg_repr := subg_repr eqg_repr_proof.
Local Notation rH := eqg_repr.

Lemma rcent_eqg U : rcent rH U = rcent rG U.
Proof.
by rewrite rcent_subg -(eqP eqGH) (setIidPr _) ?rcent_sub.
Qed.

Section Stabiliser.

Variables (m : nat) (U : 'M[R]_(m, n)).

Lemma rstab_eqg : rstab rH U = rstab rG U.
Proof.
by rewrite rstab_subg -(eqP eqGH) (setIidPr _) ?rstab_sub.
Qed.

End Stabiliser.

Lemma rker_eqg : rker rH = rker rG.
Proof.
exact: rstab_eqg.
Qed.

Lemma eqg_mx_faithful : mx_faithful rH = mx_faithful rG.
Proof.
by rewrite /mx_faithful rker_eqg.
Qed.

End SameGroup.

End ChangeGroup.

Section Morphpre.

Variables (aT rT : finGroupType) (D : {group aT}) (f : {morphism D >-> rT}).
Variables (G : {group rT}) (n : nat) (rG : mx_representation G n).

Lemma morphpre_mx_repr : mx_repr (f @*^-1 G) (rG \o f).
Proof.
split=> [|x y]; first by rewrite /= morph1 repr_mx1.
case/morphpreP=> Dx Gfx; case/morphpreP=> Dy Gfy.
by rewrite /= morphM ?repr_mxM.
Qed.
Canonical morphpre_repr := MxRepresentation morphpre_mx_repr.
Local Notation rGf := morphpre_repr.

Section Stabiliser.

Variables (m : nat) (U : 'M[R]_(m, n)).

Lemma rstab_morphpre : rstab rGf U = f @*^-1 (rstab rG U).
Proof.
by apply/setP=> x; rewrite !inE andbA.
Qed.

End Stabiliser.

Lemma rker_morphpre : rker rGf = f @*^-1 (rker rG).
Proof.
exact: rstab_morphpre.
Qed.

End Morphpre.

Section Morphim.

Variables (aT rT : finGroupType) (G D : {group aT}) (f : {morphism D >-> rT}).
Variables (n : nat) (rGf : mx_representation (f @* G) n).

Definition morphim_mx of G \subset D := fun x => rGf (f x).

Hypothesis sGD : G \subset D.

Lemma morphim_mxE x : morphim_mx sGD x = rGf (f x).
Proof.
by [].
Qed.

Let sG_f'fG : G \subset f @*^-1 (f @* G).
Proof.
by rewrite -sub_morphim_pre.
Qed.

Lemma morphim_mx_repr : mx_repr G (morphim_mx sGD).
Proof.
exact: subg_mx_repr (morphpre_repr f rGf) sG_f'fG.
Qed.
Canonical morphim_repr := MxRepresentation morphim_mx_repr.
Local Notation rG := morphim_repr.

Section Stabiliser.
Variables (m : nat) (U : 'M[R]_(m, n)).

Lemma rstab_morphim : rstab rG U = G :&: f @*^-1 rstab rGf U.
Proof.
by rewrite -rstab_morphpre -(rstab_subg _ sG_f'fG).
Qed.

End Stabiliser.

Lemma rker_morphim : rker rG = G :&: f @*^-1 (rker rGf).
Proof.
exact: rstab_morphim.
Qed.

End Morphim.

Section Conjugate.

Variables (gT : finGroupType) (G : {group gT}) (n : nat).
Variables (rG : mx_representation G n) (B : 'M[R]_n).

Definition rconj_mx of B \in unitmx := fun x => B *m rG x *m invmx B.

Hypothesis uB : B \in unitmx.

Lemma rconj_mx_repr : mx_repr G (rconj_mx uB).
Proof.
split=> [|x y Gx Gy]; rewrite /rconj_mx ?repr_mx1 ?mulmx1 ?mulmxV ?repr_mxM //.
by rewrite !mulmxA mulmxKV.
Qed.
Canonical rconj_repr := MxRepresentation rconj_mx_repr.
Local Notation rGB := rconj_repr.

Lemma rconj_mxE x : rGB x = B *m rG x *m invmx B.
Proof.
by [].
Qed.

Lemma rconj_mxJ m (W : 'M_(m, n)) x : W *m rGB x *m B = W *m B *m rG x.
Proof.
by rewrite !mulmxA mulmxKV.
Qed.

Lemma rcent_conj A : rcent rGB A = rcent rG (invmx B *m A *m B).
Proof.
apply/setP=> x; rewrite !inE /= rconj_mxE !mulmxA.
rewrite (can2_eq (mulmxKV uB) (mulmxK uB)) -!mulmxA.
by rewrite -(can2_eq (mulKVmx uB) (mulKmx uB)).
Qed.

Lemma rstab_conj m (U : 'M_(m, n)) : rstab rGB U = rstab rG (U *m B).
Proof.
apply/setP=> x; rewrite !inE /= rconj_mxE !mulmxA.
by rewrite (can2_eq (mulmxKV uB) (mulmxK uB)).
Qed.

Lemma rker_conj : rker rGB = rker rG.
Proof.
apply/setP=> x; rewrite !inE /= mulmxA (can2_eq (mulmxKV uB) (mulmxK uB)).
by rewrite mul1mx -scalar_mxC (inj_eq (can_inj (mulKmx uB))) mul1mx.
Qed.

Lemma conj_mx_faithful : mx_faithful rGB = mx_faithful rG.
Proof.
by rewrite /mx_faithful rker_conj.
Qed.

End Conjugate.

Section Quotient.

Variables (gT : finGroupType) (G : {group gT}) (n : nat).
Variable rG : mx_representation G n.

Definition quo_mx (H : {set gT}) of H \subset rker rG & G \subset 'N(H) :=
  fun Hx : coset_of H => rG (repr Hx).

Section SubQuotient.

Variable H : {group gT}.
Hypotheses (krH : H \subset rker rG) (nHG : G \subset 'N(H)).
Let nHGs := subsetP nHG.

Lemma quo_mx_coset x : x \in G -> quo_mx krH nHG (coset H x) = rG x.
Proof.
move=> Gx; rewrite /quo_mx val_coset ?nHGs //; case: repr_rcosetP => z Hz.
by case/rkerP: (subsetP krH z Hz) => Gz rz1; rewrite repr_mxM // rz1 mul1mx.
Qed.

Lemma quo_mx_repr : mx_repr (G / H)%g (quo_mx krH nHG).
Proof.
split=> [|Hx Hy]; first by rewrite /quo_mx repr_coset1 repr_mx1.
case/morphimP=> x Nx Gx ->{Hx}; case/morphimP=> y Ny Gy ->{Hy}.
by rewrite -morphM // !quo_mx_coset ?groupM ?repr_mxM.
Qed.
Canonical quo_repr := MxRepresentation quo_mx_repr.
Local Notation rGH := quo_repr.

Lemma quo_repr_coset x : x \in G -> rGH (coset H x) = rG x.
Proof.
exact: quo_mx_coset.
Qed.

Lemma rcent_quo A : rcent rGH A = (rcent rG A / H)%g.
Proof.
apply/setP=> Hx /[!inE]; apply/andP/idP=> [[]|]; case/morphimP=> x Nx Gx ->{Hx}.
  by rewrite quo_repr_coset // => cAx; rewrite mem_morphim // inE Gx.
by case/setIdP: Gx => Gx cAx; rewrite quo_repr_coset ?mem_morphim.
Qed.

Lemma rstab_quo m (U : 'M_(m, n)) : rstab rGH U = (rstab rG U / H)%g.
Proof.
apply/setP=> Hx /[!inE]; apply/andP/idP=> [[]|]; case/morphimP=> x Nx Gx ->{Hx}.
  by rewrite quo_repr_coset // => nUx; rewrite mem_morphim // inE Gx.
by case/setIdP: Gx => Gx nUx; rewrite quo_repr_coset ?mem_morphim.
Qed.

Lemma rker_quo : rker rGH = (rker rG / H)%g.
Proof.
exact: rstab_quo.
Qed.

End SubQuotient.

Definition kquo_mx := quo_mx (subxx (rker rG)) (rker_norm rG).
Lemma kquo_mxE : kquo_mx = quo_mx (subxx (rker rG)) (rker_norm rG).
Proof.
by [].
Qed.

Canonical kquo_repr := @MxRepresentation _ _ _ kquo_mx (quo_mx_repr _ _).

Lemma kquo_repr_coset x :
  x \in G -> kquo_repr (coset (rker rG) x) = rG x.
Proof.
exact: quo_repr_coset.
Qed.

Lemma kquo_mx_faithful : mx_faithful kquo_repr.
Proof.
by rewrite /mx_faithful rker_quo trivg_quotient.
Qed.

End Quotient.

Section Regular.

Variables (gT : finGroupType) (G : {group gT}).
Local Notation nG := #|pred_of_set (gval G)|.

Definition gring_index (x : gT) := enum_rank_in (group1 G) x.

Lemma gring_valK : cancel enum_val gring_index.
Proof.
exact: enum_valK_in.
Qed.

Lemma gring_indexK : {in G, cancel gring_index enum_val}.
Proof.
exact: enum_rankK_in.
Qed.

Definition regular_mx x : 'M[R]_nG :=
  \matrix_i delta_mx 0 (gring_index (enum_val i * x)).

Lemma regular_mx_repr : mx_repr G regular_mx.
Proof.
split=> [|x y Gx Gy]; apply/row_matrixP=> i; rewrite !rowK.
  by rewrite mulg1 row1 gring_valK.
by rewrite row_mul rowK -rowE rowK mulgA gring_indexK // groupM ?enum_valP.
Qed.
Canonical regular_repr := MxRepresentation regular_mx_repr.
Local Notation aG := regular_repr.

Definition group_ring := enveloping_algebra_mx aG.
Local Notation R_G := group_ring.

Definition gring_row : 'M[R]_nG -> 'rV_nG := row (gring_index 1).
Canonical gring_row_linear := [linear of gring_row].

Lemma gring_row_mul A B : gring_row (A *m B) = gring_row A *m B.
Proof.
exact: row_mul.
Qed.

Definition gring_proj x := row (gring_index x) \o trmx \o gring_row.
Canonical gring_proj_linear x := [linear of gring_proj x].

Lemma gring_projE : {in G &, forall x y, gring_proj x (aG y) = (x == y)%:R}.
Proof.
move=> x y Gx Gy; rewrite /gring_proj /= /gring_row rowK gring_indexK //=.
rewrite mul1g trmx_delta rowE mul_delta_mx_cond [delta_mx 0 0]mx11_scalar !mxE.
by rewrite /= -(inj_eq (can_inj gring_valK)) !gring_indexK.
Qed.

Lemma regular_mx_faithful : mx_faithful aG.
Proof.
apply/subsetP=> x /setIdP[Gx].
rewrite mul1mx inE => /eqP/(congr1 (gring_proj 1%g)).
rewrite -(repr_mx1 aG) !gring_projE ?group1 // eqxx eq_sym.
by case: (x == _) => // /eqP; rewrite eq_sym oner_eq0.
Qed.

Section GringMx.

Variables (n : nat) (rG : mx_representation G n).

Definition gring_mx := vec_mx \o mulmxr (enveloping_algebra_mx rG).
Canonical gring_mx_linear := [linear of gring_mx].

Lemma gring_mxJ a x :
  x \in G -> gring_mx (a *m aG x) = gring_mx a *m rG x.
Proof.
move=> Gx; rewrite /gring_mx /= ![a *m _]mulmx_sum_row.
rewrite !(mulmx_suml, linear_sum); apply: eq_bigr => i _.
rewrite linearZ -!scalemxAl linearZ /=; congr (_ *: _) => {a}.
rewrite !rowK /= !mxvecK -rowE rowK mxvecK.
by rewrite gring_indexK ?groupM ?repr_mxM ?enum_valP.
Qed.

End GringMx.

Lemma gring_mxK : cancel (gring_mx aG) gring_row.
Proof.
move=> a; rewrite /gring_mx /= mulmx_sum_row !linear_sum.
rewrite {2}[a]row_sum_delta; apply: eq_bigr => i _.
rewrite !linearZ /= /gring_row !(rowK, mxvecK).
by rewrite gring_indexK // mul1g gring_valK.
Qed.

Section GringOp.

Variables (n : nat) (rG : mx_representation G n).

Definition gring_op := gring_mx rG \o gring_row.
Canonical gring_op_linear := [linear of gring_op].

Lemma gring_opE a : gring_op a = gring_mx rG (gring_row a).
Proof.
by [].
Qed.

Lemma gring_opG x : x \in G -> gring_op (aG x) = rG x.
Proof.
move=> Gx; rewrite gring_opE /gring_row rowK gring_indexK // mul1g.
by rewrite /gring_mx /= -rowE rowK mxvecK gring_indexK.
Qed.

Lemma gring_op1 : gring_op 1%:M = 1%:M.
Proof.
by rewrite -(repr_mx1 aG) gring_opG ?repr_mx1.
Qed.

Lemma gring_opJ A b :
  gring_op (A *m gring_mx aG b) = gring_op A *m gring_mx rG b.
Proof.
rewrite /gring_mx /= ![b *m _]mulmx_sum_row !linear_sum.
apply: eq_bigr => i _; rewrite !linearZ /= !rowK !mxvecK.
by rewrite gring_opE gring_row_mul gring_mxJ ?enum_valP.
Qed.

Lemma gring_op_mx b : gring_op (gring_mx aG b) = gring_mx rG b.
Proof.
by rewrite -[_ b]mul1mx gring_opJ gring_op1 mul1mx.
Qed.

Lemma gring_mxA a b :
  gring_mx rG (a *m gring_mx aG b) = gring_mx rG a *m gring_mx rG b.
Proof.
by rewrite -(gring_op_mx a) -gring_opJ gring_opE gring_row_mul gring_mxK.
Qed.

End GringOp.

End Regular.

End RingRepr.

Arguments mx_representation R {gT} G%g n%N.
Arguments mx_repr {R gT} G%g {n%N} r.
Arguments group_ring R {gT} G%g.
Arguments regular_repr R {gT} G%g.

Arguments centgmxP {R gT G n rG f}.
Arguments rkerP {R gT G n rG x}.
Arguments repr_mxK {R gT G%G n%N} rG {m%N} [x%g] Gx.
Arguments repr_mxKV {R gT G%G n%N} rG {m%N} [x%g] Gx.
Arguments gring_valK {gT G%G} i%R : rename.
Arguments gring_indexK {gT G%G} x%g.
Arguments gring_mxK {R gT G%G} v%R : rename.

Section ChangeOfRing.

Variables (aR rR : comUnitRingType) (f : {rmorphism aR -> rR}).
Local Notation "A ^f" := (map_mx (GRing.RMorphism.apply f) A) : ring_scope.
Variables (gT : finGroupType) (G : {group gT}).

Lemma map_regular_mx x : (regular_mx aR G x)^f = regular_mx rR G x.
Proof.
by apply/matrixP=> i j; rewrite !mxE rmorph_nat.
Qed.

Lemma map_gring_row (A : 'M_#|G|) : (gring_row A)^f = gring_row A^f.
Proof.
by rewrite map_row.
Qed.

Lemma map_gring_proj x (A : 'M_#|G|) : (gring_proj x A)^f = gring_proj x A^f.
Proof.
by rewrite map_row -map_trmx map_gring_row.
Qed.

Section OneRepresentation.

Variables (n : nat) (rG : mx_representation aR G n).

Definition map_repr_mx (f0 : aR -> rR) rG0 (g : gT) : 'M_n := map_mx f0 (rG0 g).

Lemma map_mx_repr : mx_repr G (map_repr_mx f rG).
Proof.
split=> [|x y Gx Gy]; first by rewrite /map_repr_mx repr_mx1 map_mx1.
by rewrite -map_mxM -repr_mxM.
Qed.
Canonical map_repr := MxRepresentation map_mx_repr.
Local Notation rGf := map_repr.

Lemma map_reprE x : rGf x = (rG x)^f.
Proof.
by [].
Qed.

Lemma map_reprJ m (A : 'M_(m, n)) x : (A *m rG x)^f = A^f *m rGf x.
Proof.
exact: map_mxM.
Qed.

Lemma map_enveloping_algebra_mx :
  (enveloping_algebra_mx rG)^f = enveloping_algebra_mx rGf.
Proof.
by apply/row_matrixP=> i; rewrite -map_row !rowK map_mxvec.
Qed.

Lemma map_gring_mx a : (gring_mx rG a)^f = gring_mx rGf a^f.
Proof.
by rewrite map_vec_mx map_mxM map_enveloping_algebra_mx.
Qed.

Lemma map_gring_op A : (gring_op rG A)^f = gring_op rGf A^f.
Proof.
by rewrite map_gring_mx map_gring_row.
Qed.

End OneRepresentation.

Lemma map_regular_repr : map_repr (regular_repr aR G) =1 regular_repr rR G.
Proof.
exact: map_regular_mx.
Qed.

Lemma map_group_ring : (group_ring aR G)^f = group_ring rR G.
Proof.
rewrite map_enveloping_algebra_mx; apply/row_matrixP=> i.
by rewrite !rowK map_regular_repr.
Qed.

 

End ChangeOfRing.

Section FieldRepr.

Variable F : fieldType.

Section OneRepresentation.

Variable gT : finGroupType.

Variables (G : {group gT}) (n : nat) (rG : mx_representation F G n).
Arguments rG _%group_scope : extra scopes.

Local Notation E_G := (enveloping_algebra_mx rG).

Lemma repr_mx_free x : x \in G -> row_free (rG x).
Proof.
by move=> Gx; rewrite row_free_unit repr_mx_unit.
Qed.

Section Stabilisers.

Variables (m : nat) (U : 'M[F]_(m, n)).

Definition rstabs := [set x in G | U *m rG x <= U]%MS.

Lemma rstabs_sub : rstabs \subset G.
Proof.
by apply/subsetP=> x /setIdP[].
Qed.

Lemma rstabs_group_set : group_set rstabs.
Proof.
apply/group_setP; rewrite inE group1 repr_mx1 mulmx1.
split=> //= x y /setIdP[Gx nUx] /setIdP[Gy]; rewrite inE repr_mxM ?groupM //.
by apply: submx_trans; rewrite mulmxA submxMr.
Qed.
Canonical rstabs_group := Group rstabs_group_set.

Lemma rstab_act x m1 (W : 'M_(m1, n)) :
  x \in rstab rG U -> (W <= U)%MS -> W *m rG x = W.
Proof.
by case/setIdP=> _ /eqP cUx /submxP[w ->]; rewrite -mulmxA cUx.
Qed.

Lemma rstabs_act x m1 (W : 'M_(m1, n)) :
  x \in rstabs -> (W <= U)%MS -> (W *m rG x <= U)%MS.
Admitted.

Definition mxmodule := G \subset rstabs.

Lemma mxmoduleP : reflect {in G, forall x, U *m rG x <= U}%MS mxmodule.
Admitted.

End Stabilisers.
Arguments mxmoduleP {m U}.

Lemma rstabS m1 m2 (U : 'M_(m1, n)) (V : 'M_(m2, n)) :
  (U <= V)%MS -> rstab rG V \subset rstab rG U.
Admitted.

Lemma eqmx_rstab m1 m2 (U : 'M_(m1, n)) (V : 'M_(m2, n)) :
  (U :=: V)%MS -> rstab rG U = rstab rG V.
Admitted.

Lemma eqmx_rstabs m1 m2 (U : 'M_(m1, n)) (V : 'M_(m2, n)) :
  (U :=: V)%MS -> rstabs U = rstabs V.
Admitted.

Lemma eqmx_module m1 m2 (U : 'M_(m1, n)) (V : 'M_(m2, n)) :
  (U :=: V)%MS -> mxmodule U = mxmodule V.
Admitted.

Lemma mxmodule0 m : mxmodule (0 : 'M_(m, n)).
Admitted.

Lemma mxmodule1 : mxmodule 1%:M.
Admitted.

Lemma mxmodule_trans m1 m2 (U : 'M_(m1, n)) (W : 'M_(m2, n)) x :
  mxmodule U -> x \in G -> (W <= U -> W *m rG x <= U)%MS.
Admitted.

Lemma mxmodule_eigenvector m (U : 'M_(m, n)) :
    mxmodule U -> \rank U = 1%N ->
  {u : 'rV_n & {a | (U :=: u)%MS & {in G, forall x, u *m rG x = a x *: u}}}.
Admitted.

Lemma addsmx_module m1 m2 U V :
  @mxmodule m1 U -> @mxmodule m2 V -> mxmodule (U + V)%MS.
Admitted.

Lemma sumsmx_module I r (P : pred I) U :
  (forall i, P i -> mxmodule (U i)) -> mxmodule (\sum_(i <- r | P i) U i)%MS.
Admitted.

Lemma capmx_module m1 m2 U V :
  @mxmodule m1 U -> @mxmodule m2 V -> mxmodule (U :&: V)%MS.
Admitted.

Lemma bigcapmx_module I r (P : pred I) U :
  (forall i, P i -> mxmodule (U i)) -> mxmodule (\bigcap_(i <- r | P i) U i)%MS.
Admitted.

 
Section Submodule.

Variable U : 'M[F]_n.

Definition val_submod m : 'M_(m, \rank U) -> 'M_(m, n) := mulmxr (row_base U).
Definition in_submod m : 'M_(m, n) -> 'M_(m, \rank U) :=
   mulmxr (invmx (row_ebase U) *m pid_mx (\rank U)).
Canonical val_submod_linear m := [linear of @val_submod m].
Canonical in_submod_linear m := [linear of @in_submod m].

Lemma val_submodE m W : @val_submod m W = W *m val_submod 1%:M.
Admitted.

Lemma in_submodE m W : @in_submod m W = W *m in_submod 1%:M.
Admitted.

Lemma val_submod1 : (val_submod 1%:M :=: U)%MS.
Admitted.

Lemma val_submodP m W : (@val_submod m W <= U)%MS.
Admitted.

Lemma val_submodK m : cancel (@val_submod m) (@in_submod m).
Admitted.

Lemma val_submod_inj m : injective (@val_submod m).
Admitted.

Lemma val_submodS m1 m2 (V : 'M_(m1, \rank U)) (W : 'M_(m2, \rank U)) :
  (val_submod V <= val_submod W)%MS = (V <= W)%MS.
Admitted.

Lemma in_submodK m W : (W <= U)%MS -> val_submod (@in_submod m W) = W.
Proof.
case/submxP=> w ->; rewrite /val_submod /= -!mulmxA.
congr (_ *m _); rewrite -{1}[U]mulmx_ebase !mulmxA mulmxK ?row_ebase_unit //.
by rewrite -2!(mulmxA (col_ebase U)) !pid_mx_id ?rank_leq_row // mulmx_ebase.
Qed.

Lemma val_submod_eq0 m W : (@val_submod m W == 0) = (W == 0).
Admitted.

Lemma in_submod_eq0 m W : (@in_submod m W == 0) = (W <= U^C)%MS.
Admitted.

Lemma mxrank_in_submod m (W : 'M_(m, n)) :
  (W <= U)%MS -> \rank (in_submod W) = \rank W.
Admitted.

Definition val_factmod m : _ -> 'M_(m, n) :=
  mulmxr (row_base (cokermx U) *m row_ebase U).
Definition in_factmod m : 'M_(m, n) -> _ := mulmxr (col_base (cokermx U)).
Canonical val_factmod_linear m := [linear of @val_factmod m].
Canonical in_factmod_linear m := [linear of @in_factmod m].

Lemma val_factmodE m W : @val_factmod m W = W *m val_factmod 1%:M.
Admitted.

Lemma in_factmodE m W : @in_factmod m W = W *m in_factmod 1%:M.
Admitted.

Lemma val_factmodP m W : (@val_factmod m W <= U^C)%MS.
Admitted.

Lemma val_factmodK m : cancel (@val_factmod m) (@in_factmod m).
Admitted.

Lemma val_factmod_inj m : injective (@val_factmod m).
Admitted.

Lemma val_factmodS m1 m2 (V : 'M_(m1, _)) (W : 'M_(m2, _)) :
  (val_factmod V <= val_factmod W)%MS = (V <= W)%MS.
Admitted.

Lemma val_factmod_eq0 m W : (@val_factmod m W == 0) = (W == 0).
Admitted.

Lemma in_factmod_eq0 m (W : 'M_(m, n)) : (in_factmod W == 0) = (W <= U)%MS.
Admitted.

Lemma in_factmodK m (W : 'M_(m, n)) :
  (W <= U^C)%MS -> val_factmod (in_factmod W) = W.
Proof.
case/submxP=> w ->{W}; rewrite /val_factmod /= -2!mulmxA.
congr (_ *m _); rewrite (mulmxA (col_base _)) mulmx_base -2!mulmxA.
by rewrite mulKVmx ?row_ebase_unit // mulmxA copid_mx_id ?rank_leq_row.
Qed.

Lemma in_factmod_addsK m (W : 'M_(m, n)) :
  (in_factmod (U + W)%MS :=: in_factmod W)%MS.
Admitted.

Lemma add_sub_fact_mod m (W : 'M_(m, n)) :
  val_submod (in_submod W) + val_factmod (in_factmod W) = W.
Admitted.

Lemma proj_factmodS m (W : 'M_(m, n)) :
  (val_factmod (in_factmod W) <= U + W)%MS.
Admitted.

Lemma in_factmodsK m (W : 'M_(m, n)) :
  (U <= W)%MS -> (U + val_factmod (in_factmod W) :=: W)%MS.
Admitted.

Lemma mxrank_in_factmod m (W : 'M_(m, n)) :
  (\rank (in_factmod W) + \rank U)%N = \rank (U + W).
Admitted.

Definition submod_mx of mxmodule U :=
  fun x => in_submod (val_submod 1%:M *m rG x).

Definition factmod_mx of mxmodule U :=
  fun x => in_factmod (val_factmod 1%:M *m rG x).

Hypothesis Umod : mxmodule U.

Lemma in_submodJ m (W : 'M_(m, n)) x :
  (W <= U)%MS -> in_submod (W *m rG x) = in_submod W *m submod_mx Umod x.
Admitted.

Lemma val_submodJ m (W : 'M_(m, \rank U)) x :
  x \in G -> val_submod (W *m submod_mx Umod x) = val_submod W *m rG x.
Admitted.

Lemma submod_mx_repr : mx_repr G (submod_mx Umod).
Admitted.

Canonical submod_repr := MxRepresentation submod_mx_repr.

Lemma in_factmodJ m (W : 'M_(m, n)) x :
  x \in G -> in_factmod (W *m rG x) = in_factmod W *m factmod_mx Umod x.
Admitted.

Lemma val_factmodJ m (W : 'M_(m, \rank (cokermx U))) x :
  x \in G ->
  val_factmod (W *m factmod_mx Umod x) =
     val_factmod (in_factmod (val_factmod W *m rG x)).
Admitted.

Lemma factmod_mx_repr : mx_repr G (factmod_mx Umod).
Admitted.
Canonical factmod_repr := MxRepresentation factmod_mx_repr.

 
Lemma mxtrace_sub_fact_mod x :
  \tr (submod_repr x) + \tr (factmod_repr x) = \tr (rG x).
Admitted.

End Submodule.

 

Lemma envelop_mx_id x : x \in G -> (rG x \in E_G)%MS.
Admitted.

Lemma envelop_mx1 : (1%:M \in E_G)%MS.
Admitted.

Lemma envelop_mxP A :
  reflect (exists a, A = \sum_(x in G) a x *: rG x) (A \in E_G)%MS.
Admitted.

Lemma envelop_mxM A B : (A \in E_G -> B \in E_G -> A *m B \in E_G)%MS.
Admitted.

Lemma mxmodule_envelop m1 m2 (U : 'M_(m1, n)) (W : 'M_(m2, n)) A :
  (mxmodule U -> mxvec A <= E_G -> W <= U -> W *m A <= U)%MS.
Admitted.

 
 

Definition dom_hom_mx f : 'M_n :=
  kermx (lin1_mx (mxvec \o mulmx (cent_mx_fun E_G f) \o lin_mul_row)).

Lemma hom_mxP m f (W : 'M_(m, n)) :
  reflect (forall x, x \in G -> W *m rG x *m f = W *m f *m rG x)
          (W <= dom_hom_mx f)%MS.
Admitted.
Arguments hom_mxP {m f W}.

Lemma hom_envelop_mxC m f (W : 'M_(m, n)) A :
  (W <= dom_hom_mx f -> A \in E_G -> W *m A *m f = W *m f *m A)%MS.
Admitted.

Lemma dom_hom_invmx f :
  f \in unitmx -> (dom_hom_mx (invmx f) :=: dom_hom_mx f *m f)%MS.
Admitted.

Lemma dom_hom_mx_module f : mxmodule (dom_hom_mx f).
Admitted.

Lemma hom_mxmodule m (U : 'M_(m, n)) f :
  (U <= dom_hom_mx f)%MS -> mxmodule U -> mxmodule (U *m f).
Admitted.

Lemma kermx_hom_module m (U : 'M_(m, n)) f :
  (U <= dom_hom_mx f)%MS -> mxmodule U -> mxmodule (U :&: kermx f)%MS.
Admitted.

Lemma scalar_mx_hom a m (U : 'M_(m, n)) : (U <= dom_hom_mx a%:M)%MS.
Admitted.

Lemma proj_mx_hom (U V : 'M_n) :
    (U :&: V = 0)%MS -> mxmodule U -> mxmodule V ->
  (U + V <= dom_hom_mx (proj_mx U V))%MS.
Admitted.

 
 
 
 
 

Definition rfix_mx (H : {set gT}) :=
  let commrH := \matrix_(i < #|H|) mxvec (rG (enum_val i) - 1%:M) in
  kermx (lin1_mx (mxvec \o mulmx commrH \o lin_mul_row)).

Lemma rfix_mxP m (W : 'M_(m, n)) (H : {set gT}) :
  reflect (forall x, x \in H -> W *m rG x = W) (W <= rfix_mx H)%MS.
Admitted.
Arguments rfix_mxP {m W}.

Lemma rfix_mx_id (H : {set gT}) x : x \in H -> rfix_mx H *m rG x = rfix_mx H.
Admitted.

Lemma rfix_mxS (H K : {set gT}) : H \subset K -> (rfix_mx K <= rfix_mx H)%MS.
Admitted.

Lemma rfix_mx_conjsg (H : {set gT}) x :
  x \in G -> H \subset G -> (rfix_mx (H :^ x) :=: rfix_mx H *m rG x)%MS.
Admitted.

Lemma norm_sub_rstabs_rfix_mx (H : {set gT}) :
  H \subset G -> 'N_G(H) \subset rstabs (rfix_mx H).
Admitted.

Lemma normal_rfix_mx_module H : H <| G -> mxmodule (rfix_mx H).
Admitted.

Lemma rfix_mx_module : mxmodule (rfix_mx G).
Admitted.

Lemma rfix_mx_rstabC (H : {set gT}) m (U : 'M[F]_(m, n)) :
  H \subset G -> (H \subset rstab rG U) = (U <= rfix_mx H)%MS.
Admitted.

 
Definition cyclic_mx u := <<E_G *m lin_mul_row u>>%MS.

Lemma cyclic_mxP u v :
  reflect (exists2 A, A \in E_G & v = u *m A)%MS (v <= cyclic_mx u)%MS.
Admitted.
Arguments cyclic_mxP {u v}.

Lemma cyclic_mx_id u : (u <= cyclic_mx u)%MS.
Admitted.

Lemma cyclic_mx_eq0 u : (cyclic_mx u == 0) = (u == 0).
Admitted.

Lemma cyclic_mx_module u : mxmodule (cyclic_mx u).
Admitted.

Lemma cyclic_mx_sub m u (W : 'M_(m, n)) :
  mxmodule W -> (u <= W)%MS -> (cyclic_mx u <= W)%MS.
Admitted.

Lemma hom_cyclic_mx u f :
  (u <= dom_hom_mx f)%MS -> (cyclic_mx u *m f :=: cyclic_mx (u *m f))%MS.
Admitted.

 

Definition annihilator_mx u := (E_G :&: kermx (lin_mul_row u))%MS.

Lemma annihilator_mxP u A :
  reflect (A \in E_G /\ u *m A = 0)%MS (A \in annihilator_mx u)%MS.
Admitted.

 

Definition row_hom_mx u :=
  (\bigcap_j kermx (vec_mx (row j (annihilator_mx u))))%MS.

Lemma row_hom_mxP u v :
  reflect (exists2 f, u <= dom_hom_mx f & u *m f = v)%MS (v <= row_hom_mx u)%MS.
Admitted.

 
 
 
 

 
 

Variant mx_iso (U V : 'M_n) : Prop :=
  MxIso f of f \in unitmx & (U <= dom_hom_mx f)%MS & (U *m f :=: V)%MS.

Lemma eqmx_iso U V : (U :=: V)%MS -> mx_iso U V.
Admitted.

Lemma mx_iso_refl U : mx_iso U U.
Admitted.

Lemma mx_iso_sym U V : mx_iso U V -> mx_iso V U.
Admitted.

Lemma mx_iso_trans U V W : mx_iso U V -> mx_iso V W -> mx_iso U W.
Admitted.

Lemma mxrank_iso U V : mx_iso U V -> \rank U = \rank V.
Admitted.

Lemma mx_iso_module U V : mx_iso U V -> mxmodule U -> mxmodule V.
Admitted.

 

Definition mxsimple (V : 'M_n) :=
  [/\ mxmodule V, V != 0 &
      forall U : 'M_n, mxmodule U -> (U <= V)%MS -> U != 0 -> (V <= U)%MS].

Definition mxnonsimple (U : 'M_n) :=
  exists V : 'M_n, [&& mxmodule V, (V <= U)%MS, V != 0 & \rank V < \rank U].

Lemma mxsimpleP U :
  [/\ mxmodule U, U != 0 & ~ mxnonsimple U] <-> mxsimple U.
Admitted.

Lemma mxsimple_module U : mxsimple U -> mxmodule U.
Admitted.

Lemma mxsimple_exists m (U : 'M_(m, n)) :
  mxmodule U -> U != 0 -> classically (exists2 V, mxsimple V & V <= U)%MS.
Admitted.

Lemma mx_iso_simple U V : mx_iso U V -> mxsimple U -> mxsimple V.
Admitted.

Lemma mxsimple_cyclic u U :
  mxsimple U -> u != 0 -> (u <= U)%MS -> (U :=: cyclic_mx u)%MS.
Admitted.

 
Lemma mx_Schur_onto m (U : 'M_(m, n)) V f :
    mxmodule U -> mxsimple V -> (U <= dom_hom_mx f)%MS ->
  (U *m f <= V)%MS -> U *m f != 0 -> (U *m f :=: V)%MS.
Admitted.

 
Lemma mx_Schur_inj U f :
  mxsimple U -> (U <= dom_hom_mx f)%MS -> U *m f != 0 -> (U :&: kermx f)%MS = 0.
Admitted.

 
Lemma mx_Schur_inj_iso U f :
  mxsimple U -> (U <= dom_hom_mx f)%MS -> U *m f != 0 -> mx_iso U (U *m f).
Admitted.

 
Lemma mx_Schur_iso U V f :
    mxsimple U -> mxsimple V -> (U <= dom_hom_mx f)%MS ->
  (U *m f <= V)%MS -> U *m f != 0 -> mx_iso U V.
Admitted.

 
 

Lemma nz_row_mxsimple U : mxsimple U -> nz_row U != 0.
Admitted.

Definition mxsimple_iso (U V : 'M_n) :=
  [&& mxmodule V, (V :&: row_hom_mx (nz_row U))%MS != 0 & \rank V <= \rank U].

Lemma mxsimple_isoP U V :
  mxsimple U -> reflect (mx_iso U V) (mxsimple_iso U V).
Admitted.

Lemma mxsimple_iso_simple U V :
  mxsimple_iso U V -> mxsimple U -> mxsimple V.
Admitted.

 
 
 

Implicit Type I : finType.

Variant mxsemisimple (V : 'M_n) :=
  MxSemisimple I U (W := (\sum_(i : I) U i)%MS) of
    forall i, mxsimple (U i) & (W :=: V)%MS & mxdirect W.

 
Lemma sum_mxsimple_direct_compl m I W (U : 'M_(m, n)) :
    let V := (\sum_(i : I) W i)%MS in
    (forall i : I, mxsimple (W i)) -> mxmodule U -> (U <= V)%MS ->
  {J : {set I} | let S := U + \sum_(i in J) W i in S :=: V /\ mxdirect S}%MS.
Admitted.

Lemma sum_mxsimple_direct_sub I W (V : 'M_n) :
    (forall i : I, mxsimple (W i)) -> (\sum_i W i :=: V)%MS ->
  {J : {set I} | let S := \sum_(i in J) W i in S :=: V /\ mxdirect S}%MS.
Admitted.

Lemma mxsemisimple0 : mxsemisimple 0.
Admitted.

Lemma intro_mxsemisimple (I : Type) r (P : pred I) W V :
    (\sum_(i <- r | P i) W i :=: V)%MS ->
    (forall i, P i -> W i != 0 -> mxsimple (W i)) ->
  mxsemisimple V.
Admitted.

Lemma mxsimple_semisimple U : mxsimple U -> mxsemisimple U.
Admitted.

Lemma addsmx_semisimple U V :
  mxsemisimple U -> mxsemisimple V -> mxsemisimple (U + V)%MS.
Admitted.

Lemma sumsmx_semisimple (I : finType) (P : pred I) V :
  (forall i, P i -> mxsemisimple (V i)) -> mxsemisimple (\sum_(i | P i) V i)%MS.
Admitted.

Lemma eqmx_semisimple U V : (U :=: V)%MS -> mxsemisimple U -> mxsemisimple V.
Admitted.

Lemma hom_mxsemisimple (V f : 'M_n) :
  mxsemisimple V -> (V <= dom_hom_mx f)%MS -> mxsemisimple (V *m f).
Admitted.

Lemma mxsemisimple_module U : mxsemisimple U -> mxmodule U.
Admitted.

 

Variant mxsplits (V U : 'M_n) :=
  MxSplits (W : 'M_n) of mxmodule W & (U + W :=: V)%MS & mxdirect (U + W).

Definition mx_completely_reducible V :=
  forall U, mxmodule U -> (U <= V)%MS -> mxsplits V U.

Lemma mx_reducibleS U V :
    mxmodule U -> (U <= V)%MS ->
  mx_completely_reducible V -> mx_completely_reducible U.
Admitted.

Lemma mx_Maschke : [char F]^'.-group G -> mx_completely_reducible 1%:M.
Admitted.

Lemma mxsemisimple_reducible V : mxsemisimple V -> mx_completely_reducible V.
Admitted.

Lemma mx_reducible_semisimple V :
  mxmodule V -> mx_completely_reducible V -> classically (mxsemisimple V).
Admitted.

Lemma mxsemisimpleS U V :
  mxmodule U -> (U <= V)%MS -> mxsemisimple V -> mxsemisimple U.
Admitted.

Lemma hom_mxsemisimple_iso I P U W f :
  let V := (\sum_(i : I |  P i) W i)%MS in
  mxsimple U -> (forall i, P i -> W i != 0 -> mxsimple (W i)) ->
  (V <= dom_hom_mx f)%MS -> (U <= V *m f)%MS ->
  {i | P i & mx_iso (W i) U}.
Admitted.

 

Section Components.

Fact component_mx_key : unit.
Admitted.
Definition component_mx_expr (U : 'M[F]_n) :=
  (\sum_i cyclic_mx (row i (row_hom_mx (nz_row U))))%MS.
Definition component_mx := locked_with component_mx_key component_mx_expr.
Canonical component_mx_unfoldable := [unlockable fun component_mx].

Variable U : 'M[F]_n.
Hypothesis simU : mxsimple U.

Let u := nz_row U.
Let iso_u := row_hom_mx u.
Let nz_u : u != 0 := nz_row_mxsimple simU.
Let Uu : (u <= U)%MS := nz_row_sub U.
Let defU : (U :=: cyclic_mx u)%MS := mxsimple_cyclic simU nz_u Uu.
Local Notation compU := (component_mx U).

Lemma component_mx_module : mxmodule compU.
Proof.
by rewrite unlock sumsmx_module // => i; rewrite cyclic_mx_module.
Qed.

Lemma genmx_component : <<compU>>%MS = compU.
Admitted.

Lemma component_mx_def : {I : finType & {W : I -> 'M_n |
  forall i, mx_iso U (W i) & compU = \sum_i W i}}%MS.
Admitted.

Lemma component_mx_semisimple : mxsemisimple compU.
Admitted.

Lemma mx_iso_component V : mx_iso U V -> (V <= compU)%MS.
Admitted.

Lemma component_mx_id : (U <= compU)%MS.
Admitted.

Lemma hom_component_mx_iso f V :
    mxsimple V -> (compU <= dom_hom_mx f)%MS -> (V <= compU *m f)%MS ->
  mx_iso U V.
Admitted.

Lemma component_mx_iso V : mxsimple V -> (V <= compU)%MS -> mx_iso U V.
Admitted.

Lemma hom_component_mx f :
  (compU <= dom_hom_mx f)%MS -> (compU *m f <= compU)%MS.
Admitted.

End Components.

Lemma component_mx_isoP U V :
    mxsimple U -> mxsimple V ->
  reflect (mx_iso U V) (component_mx U == component_mx V).
Admitted.

Lemma component_mx_disjoint U V :
    mxsimple U -> mxsimple V -> component_mx U != component_mx V ->
  (component_mx U :&: component_mx V = 0)%MS.
Admitted.

Section Socle.

Record socleType := EnumSocle {
  socle_base_enum : seq 'M[F]_n;
  _ : forall M, M \in socle_base_enum -> mxsimple M;
  _ : forall M, mxsimple M -> has (mxsimple_iso M) socle_base_enum
}.

Lemma socle_exists : classically socleType.
Admitted.

Section SocleDef.

Variable sG0 : socleType.

Definition socle_enum := map component_mx (socle_base_enum sG0).

Lemma component_socle M : mxsimple M -> component_mx M \in socle_enum.
Admitted.

Inductive socle_sort : predArgType := PackSocle W of W \in socle_enum.

Local Notation sG := socle_sort.
Local Notation e0 := (socle_base_enum sG0).

Definition socle_base W := let: PackSocle W _ := W in e0`_(index W socle_enum).

Coercion socle_val W : 'M[F]_n := component_mx (socle_base W).

Definition socle_mult (W : sG) := (\rank W %/ \rank (socle_base W))%N.

Lemma socle_simple W : mxsimple (socle_base W).
Admitted.

Definition socle_module (W : sG) := mxsimple_module (socle_simple W).

Definition socle_repr W := submod_repr (socle_module W).

Lemma nz_socle (W : sG) : W != 0 :> 'M_n.
Admitted.

Lemma socle_mem (W : sG) : (W : 'M_n) \in socle_enum.
Admitted.

Lemma PackSocleK W e0W : @PackSocle W e0W = W :> 'M_n.
Admitted.

Canonical socle_subType := SubType _ _ _ socle_sort_rect PackSocleK.
Definition socle_eqMixin := Eval hnf in [eqMixin of sG by <:].
Canonical socle_eqType := Eval hnf in EqType sG socle_eqMixin.
Definition socle_choiceMixin := Eval hnf in [choiceMixin of sG by <:].
Canonical socle_choiceType := ChoiceType sG socle_choiceMixin.

Lemma socleP (W W' : sG) : reflect (W = W') (W == W')%MS.
Admitted.

Fact socle_finType_subproof :
  cancel (fun W => SeqSub (socle_mem W)) (fun s => PackSocle (valP s)).
Admitted.

Definition socle_countMixin := CanCountMixin socle_finType_subproof.
Canonical socle_countType := CountType sG socle_countMixin.
Canonical socle_subCountType := [subCountType of sG].
Definition socle_finMixin := CanFinMixin socle_finType_subproof.
Canonical socle_finType := FinType sG socle_finMixin.
Canonical socle_subFinType := [subFinType of sG].

End SocleDef.

Coercion socle_sort : socleType >-> predArgType.

Variable sG : socleType.

Section SubSocle.

Variable P : pred sG.
Notation S := (\sum_(W : sG | P W) socle_val W)%MS.

Lemma subSocle_module : mxmodule S.
Admitted.

Lemma subSocle_semisimple : mxsemisimple S.
Admitted.
Local Notation ssimS := subSocle_semisimple.

Lemma subSocle_iso M :
  mxsimple M -> (M <= S)%MS -> {W : sG | P W & mx_iso (socle_base W) M}.
Admitted.

Lemma capmx_subSocle m (M : 'M_(m, n)) :
  mxmodule M -> (M :&: S :=: \sum_(W : sG | P W) (M :&: W))%MS.
Admitted.

End SubSocle.

Lemma subSocle_direct P : mxdirect (\sum_(W : sG | P W) W).
Admitted.

Definition Socle := (\sum_(W : sG) W)%MS.

Lemma simple_Socle M : mxsimple M -> (M <= Socle)%MS.
Admitted.

Lemma semisimple_Socle U : mxsemisimple U -> (U <= Socle)%MS.
Admitted.

Lemma reducible_Socle U :
  mxmodule U -> mx_completely_reducible U -> (U <= Socle)%MS.
Admitted.

Lemma genmx_Socle : <<Socle>>%MS = Socle.
Admitted.

Lemma reducible_Socle1 : mx_completely_reducible 1%:M -> Socle = 1%:M.
Admitted.

Lemma Socle_module : mxmodule Socle.
Admitted.

Lemma Socle_semisimple : mxsemisimple Socle.
Admitted.

Lemma Socle_direct : mxdirect Socle.
Admitted.

Lemma Socle_iso M : mxsimple M -> {W : sG | mx_iso (socle_base W) M}.
Admitted.

End Socle.

 
Section CentHom.

Variable f : 'M[F]_n.

Lemma row_full_dom_hom : row_full (dom_hom_mx f) = centgmx rG f.
Admitted.

Lemma memmx_cent_envelop : (f \in 'C(E_G))%MS = centgmx rG f.
Admitted.

Lemma kermx_centg_module : centgmx rG f -> mxmodule (kermx f).
Admitted.

Lemma centgmx_hom m (U : 'M_(m, n)) : centgmx rG f -> (U <= dom_hom_mx f)%MS.
Admitted.

End CentHom.

 
 

Definition mx_irreducible := mxsimple 1%:M.

Lemma mx_irrP :
  mx_irreducible <-> n > 0 /\ (forall U, @mxmodule n U -> U != 0 -> row_full U).
Admitted.

 
Lemma mx_Schur :
  mx_irreducible -> forall f, centgmx rG f -> f != 0 -> f \in unitmx.
Admitted.

Definition mx_absolutely_irreducible := (n > 0) && row_full E_G.

Lemma mx_abs_irrP :
  reflect (n > 0 /\ exists a_, forall A, A = \sum_(x in G) a_ x A *: rG x)
          mx_absolutely_irreducible.
Admitted.

Lemma mx_abs_irr_cent_scalar :
  mx_absolutely_irreducible -> forall A, centgmx rG A -> is_scalar_mx A.
Admitted.

Lemma mx_abs_irrW : mx_absolutely_irreducible -> mx_irreducible.
Admitted.

Lemma linear_mx_abs_irr : n = 1%N -> mx_absolutely_irreducible.
Admitted.

Lemma abelian_abs_irr : abelian G -> mx_absolutely_irreducible = (n == 1%N).
Admitted.

End OneRepresentation.

Arguments mxmoduleP {gT G n rG m U}.
Arguments envelop_mxP {gT G n rG A}.
Arguments hom_mxP {gT G n rG m f W}.
Arguments rfix_mxP {gT G n rG m W}.
Arguments cyclic_mxP {gT G n rG u v}.
Arguments annihilator_mxP {gT G n rG u A}.
Arguments row_hom_mxP {gT G n rG u v}.
Arguments mxsimple_isoP {gT G n rG U V}.
Arguments socleP {gT G n rG sG0 W W'}.
Arguments mx_abs_irrP {gT G n rG}.

Arguments val_submod {n U m} W.
Arguments in_submod {n} U {m} W.
Arguments val_submodK {n U m} W : rename.
Arguments in_submodK {n U m} [W] sWU.
Arguments val_submod_inj {n U m} [W1 W2] : rename.

Arguments val_factmod {n U m} W.
Arguments in_factmod {n} U {m} W.
Arguments val_factmodK {n U m} W : rename.
Arguments in_factmodK {n} U {m} [W] sWU.
Arguments val_factmod_inj {n U m} [W1 W2] : rename.

Section Proper.

Variables (gT : finGroupType) (G : {group gT}) (n' : nat).
Local Notation n := n'.+1.
Variable rG : mx_representation F G n.

Lemma envelop_mx_ring : mxring (enveloping_algebra_mx rG).
Admitted.

End Proper.

Section JacobsonDensity.

Variables (gT : finGroupType) (G : {group gT}) (n : nat).
Variable rG : mx_representation F G n.
Hypothesis irrG : mx_irreducible rG.

Local Notation E_G := (enveloping_algebra_mx rG).
Local Notation Hom_G := 'C(E_G)%MS.

Lemma mx_Jacobson_density : ('C(Hom_G) <= E_G)%MS.
Admitted.

Lemma cent_mx_scalar_abs_irr : \rank Hom_G <= 1 -> mx_absolutely_irreducible rG.
Admitted.

End JacobsonDensity.

Section ChangeGroup.

Variables (gT : finGroupType) (G H : {group gT}) (n : nat).
Variables (rG : mx_representation F G n).

Section SubGroup.

Hypothesis sHG : H \subset G.

Local Notation rH := (subg_repr rG sHG).

Lemma rfix_subg : rfix_mx rH = rfix_mx rG.
Admitted.

Section Stabilisers.

Variables (m : nat) (U : 'M[F]_(m, n)).

Lemma rstabs_subg : rstabs rH U = H :&: rstabs rG U.
Admitted.

Lemma mxmodule_subg : mxmodule rG U -> mxmodule rH U.
Admitted.

End Stabilisers.

Lemma mxsimple_subg M : mxmodule rG M -> mxsimple rH M -> mxsimple rG M.
Admitted.

Lemma subg_mx_irr : mx_irreducible rH -> mx_irreducible rG.
Admitted.

Lemma subg_mx_abs_irr :
   mx_absolutely_irreducible rH -> mx_absolutely_irreducible rG.
Admitted.

End SubGroup.

Section SameGroup.

Hypothesis eqGH : G :==: H.

Local Notation rH := (eqg_repr rG eqGH).

Lemma rfix_eqg : rfix_mx rH = rfix_mx rG.
Admitted.

Section Stabilisers.

Variables (m : nat) (U : 'M[F]_(m, n)).

Lemma rstabs_eqg : rstabs rH U = rstabs rG U.
Admitted.

Lemma mxmodule_eqg : mxmodule rH U = mxmodule rG U.
Admitted.

End Stabilisers.

Lemma mxsimple_eqg M : mxsimple rH M <-> mxsimple rG M.
Admitted.

Lemma eqg_mx_irr : mx_irreducible rH <-> mx_irreducible rG.
Admitted.

Lemma eqg_mx_abs_irr :
  mx_absolutely_irreducible rH = mx_absolutely_irreducible rG.
Admitted.

End SameGroup.

End ChangeGroup.

Section Morphpre.

Variables (aT rT : finGroupType) (D : {group aT}) (f : {morphism D >-> rT}).
Variables (G : {group rT}) (n : nat) (rG : mx_representation F G n).

Local Notation rGf := (morphpre_repr f rG).

Section Stabilisers.
Variables (m : nat) (U : 'M[F]_(m, n)).

Lemma rstabs_morphpre : rstabs rGf U = f @*^-1 (rstabs rG U).
Admitted.

Lemma mxmodule_morphpre : G \subset f @* D -> mxmodule rGf U = mxmodule rG U.
Admitted.

End Stabilisers.

Lemma rfix_morphpre (H : {set aT}) :
  H \subset D -> (rfix_mx rGf H :=: rfix_mx rG (f @* H))%MS.
Admitted.

Lemma morphpre_mx_irr :
  G \subset f @* D -> (mx_irreducible rGf <-> mx_irreducible rG).
Admitted.

Lemma morphpre_mx_abs_irr :
    G \subset f @* D ->
  mx_absolutely_irreducible rGf = mx_absolutely_irreducible rG.
Admitted.

End Morphpre.

Section Morphim.

Variables (aT rT : finGroupType) (G D : {group aT}) (f : {morphism D >-> rT}).
Variables (n : nat) (rGf : mx_representation F (f @* G) n).

Hypothesis sGD : G \subset D.

Let sG_f'fG : G \subset f @*^-1 (f @* G).
Admitted.

Local Notation rG := (morphim_repr rGf sGD).

Section Stabilisers.
Variables (m : nat) (U : 'M[F]_(m, n)).

Lemma rstabs_morphim : rstabs rG U = G :&: f @*^-1 rstabs rGf U.
Admitted.

Lemma mxmodule_morphim : mxmodule rG U = mxmodule rGf U.
Admitted.

End Stabilisers.

Lemma rfix_morphim (H : {set aT}) :
  H \subset D -> (rfix_mx rG H :=: rfix_mx rGf (f @* H))%MS.
Admitted.

Lemma mxsimple_morphim M : mxsimple rG M <-> mxsimple rGf M.
Admitted.

Lemma morphim_mx_irr : (mx_irreducible rG <-> mx_irreducible rGf).
Admitted.

Lemma morphim_mx_abs_irr :
  mx_absolutely_irreducible rG = mx_absolutely_irreducible rGf.
Admitted.

End Morphim.

Section Submodule.

Variables (gT : finGroupType) (G : {group gT}) (n : nat).
Variables (rG : mx_representation F G n) (U : 'M[F]_n) (Umod : mxmodule rG U).
Local Notation rU := (submod_repr Umod).
Local Notation rU' := (factmod_repr Umod).

Lemma rfix_submod (H : {set gT}) :
  H \subset G -> (rfix_mx rU H :=: in_submod U (U :&: rfix_mx rG H))%MS.
Admitted.

Lemma rfix_factmod (H : {set gT}) :
  H \subset G -> (in_factmod U (rfix_mx rG H) <= rfix_mx rU' H)%MS.
Admitted.

Lemma rstab_submod m (W : 'M_(m, \rank U)) :
  rstab rU W = rstab rG (val_submod W).
Admitted.

Lemma rstabs_submod m (W : 'M_(m, \rank U)) :
  rstabs rU W = rstabs rG (val_submod W).
Admitted.

Lemma val_submod_module m (W : 'M_(m, \rank U)) :
   mxmodule rG (val_submod W) = mxmodule rU W.
Admitted.

Lemma in_submod_module m (V : 'M_(m, n)) :
  (V <= U)%MS -> mxmodule rU (in_submod U V) = mxmodule rG V.
Admitted.

Lemma rstab_factmod m (W : 'M_(m, n)) :
  rstab rG W \subset rstab rU' (in_factmod U W).
Admitted.

Lemma rstabs_factmod m (W : 'M_(m, \rank (cokermx U))) :
  rstabs rU' W = rstabs rG (U + val_factmod W)%MS.
Admitted.

Lemma val_factmod_module m (W : 'M_(m, \rank (cokermx U))) :
  mxmodule rG (U + val_factmod W)%MS = mxmodule rU' W.
Admitted.

Lemma in_factmod_module m (V : 'M_(m, n)) :
  mxmodule rU' (in_factmod U V) = mxmodule rG (U + V)%MS.
Admitted.

Lemma rker_submod : rker rU = rstab rG U.
Admitted.

Lemma rstab_norm : G \subset 'N(rstab rG U).
Admitted.

Lemma rstab_normal : rstab rG U <| G.
Admitted.

Lemma submod_mx_faithful : mx_faithful rU -> mx_faithful rG.
Admitted.

Lemma rker_factmod : rker rG \subset rker rU'.
Admitted.

Lemma factmod_mx_faithful : mx_faithful rU' -> mx_faithful rG.
Admitted.

Lemma submod_mx_irr : mx_irreducible rU <-> mxsimple rG U.
Admitted.

End Submodule.

Section Conjugate.

Variables (gT : finGroupType) (G : {group gT}) (n : nat).
Variables (rG : mx_representation F G n) (B : 'M[F]_n).

Hypothesis uB : B \in unitmx.

Local Notation rGB := (rconj_repr rG uB).

Lemma rfix_conj (H : {set gT}) :
   (rfix_mx rGB H :=: B *m rfix_mx rG H *m invmx B)%MS.
Admitted.

Lemma rstabs_conj m (U : 'M_(m, n)) : rstabs rGB U = rstabs rG (U *m B).
Admitted.

Lemma mxmodule_conj m (U : 'M_(m, n)) : mxmodule rGB U = mxmodule rG (U *m B).
Admitted.

Lemma conj_mx_irr : mx_irreducible rGB <-> mx_irreducible rG.
Admitted.

End Conjugate.

Section Quotient.

Variables (gT : finGroupType) (G : {group gT}) (n : nat).
Variables (rG : mx_representation F G n) (H : {group gT}).
Hypotheses (krH : H \subset rker rG) (nHG : G \subset 'N(H)).
Let nHGs := subsetP nHG.

Local Notation rGH := (quo_repr krH nHG).

Local Notation E_ r := (enveloping_algebra_mx r).
Lemma quo_mx_quotient : (E_ rGH :=: E_ rG)%MS.
Admitted.

Lemma rfix_quo (K : {group gT}) :
  K \subset G -> (rfix_mx rGH (K / H)%g :=: rfix_mx rG K)%MS.
Admitted.

Lemma rstabs_quo m (U : 'M_(m, n)) : rstabs rGH U = (rstabs rG U / H)%g.
Admitted.

Lemma mxmodule_quo m (U : 'M_(m, n)) : mxmodule rGH U = mxmodule rG U.
Admitted.

Lemma quo_mx_irr : mx_irreducible rGH <-> mx_irreducible rG.
Admitted.

End Quotient.

Section SplittingField.

Implicit Type gT : finGroupType.

Definition group_splitting_field gT (G : {group gT}) :=
  forall n (rG : mx_representation F G n),
     mx_irreducible rG -> mx_absolutely_irreducible rG.

Definition group_closure_field gT :=
  forall G : {group gT}, group_splitting_field G.

Lemma quotient_splitting_field gT (G : {group gT}) (H : {set gT}) :
  G \subset 'N(H) -> group_splitting_field G -> group_splitting_field (G / H).
Admitted.

Lemma coset_splitting_field gT (H : {set gT}) :
  group_closure_field gT -> group_closure_field (coset_groupType H).
Admitted.

End SplittingField.

Section Abelian.

Variables (gT : finGroupType) (G : {group gT}).

Lemma mx_faithful_irr_center_cyclic n (rG : mx_representation F G n) :
  mx_faithful rG -> mx_irreducible rG -> cyclic 'Z(G).
Admitted.

Lemma mx_faithful_irr_abelian_cyclic n (rG : mx_representation F G n) :
  mx_faithful rG -> mx_irreducible rG -> abelian G -> cyclic G.
Admitted.

Hypothesis splitG : group_splitting_field G.

Lemma mx_irr_abelian_linear n (rG : mx_representation F G n) :
  mx_irreducible rG -> abelian G -> n = 1%N.
Admitted.

Lemma mxsimple_abelian_linear n (rG : mx_representation F G n) M :
  abelian G -> mxsimple rG M -> \rank M = 1%N.
Admitted.

Lemma linear_mxsimple n (rG : mx_representation F G n) (M : 'M_n) :
  mxmodule rG M -> \rank M = 1%N -> mxsimple rG M.
Admitted.

End Abelian.

Section AbelianQuotient.

Variables (gT : finGroupType) (G : {group gT}).
Variables (n : nat) (rG : mx_representation F G n).

Lemma center_kquo_cyclic : mx_irreducible rG -> cyclic 'Z(G / rker rG)%g.
Admitted.

Lemma der1_sub_rker :
    group_splitting_field G -> mx_irreducible rG ->
  (G^`(1) \subset rker rG)%g = (n == 1)%N.
Admitted.

End AbelianQuotient.

Section Similarity.

Variables (gT : finGroupType) (G : {group gT}).
Local Notation reprG := (mx_representation F G).

Variant mx_rsim n1 (rG1 : reprG n1) n2 (rG2 : reprG n2) : Prop :=
  MxReprSim B of n1 = n2 & row_free B
              & forall x, x \in G -> rG1 x *m B = B *m rG2 x.

Lemma mxrank_rsim n1 n2 (rG1 : reprG n1) (rG2 : reprG n2) :
  mx_rsim rG1 rG2 -> n1 = n2.
Admitted.

Lemma mx_rsim_refl n (rG : reprG n) : mx_rsim rG rG.
Admitted.

Lemma mx_rsim_sym n1 n2 (rG1 : reprG n1) (rG2 : reprG n2) :
  mx_rsim rG1 rG2 ->  mx_rsim rG2 rG1.
Admitted.

Lemma mx_rsim_trans n1 n2 n3
                    (rG1 : reprG n1) (rG2 : reprG n2) (rG3 : reprG n3) :
  mx_rsim rG1 rG2 -> mx_rsim rG2 rG3 -> mx_rsim rG1 rG3.
Admitted.

Lemma mx_rsim_def n1 n2 (rG1 : reprG n1) (rG2 : reprG n2) :
    mx_rsim rG1 rG2 ->
  exists B, exists2 B', B' *m B = 1%:M &
    forall x, x \in G -> rG1 x = B *m rG2 x *m B'.
Admitted.

Lemma mx_rsim_iso n (rG : reprG n) (U V : 'M_n)
                  (modU : mxmodule rG U) (modV : mxmodule rG V) :
  mx_rsim (submod_repr modU) (submod_repr modV) <-> mx_iso rG U V.
Admitted.

Lemma mx_rsim_irr n1 n2 (rG1 : reprG n1) (rG2 : reprG n2) :
  mx_rsim rG1 rG2 -> mx_irreducible rG1 -> mx_irreducible rG2.
Admitted.

Lemma mx_rsim_abs_irr n1 n2 (rG1 : reprG n1) (rG2 : reprG n2) :
    mx_rsim rG1 rG2 ->
  mx_absolutely_irreducible rG1 = mx_absolutely_irreducible rG2.
Admitted.

Lemma rker_mx_rsim n1 n2 (rG1 : reprG n1) (rG2 : reprG n2) :
  mx_rsim rG1 rG2 -> rker rG1 = rker rG2.
Admitted.

Lemma mx_rsim_faithful n1 n2 (rG1 : reprG n1) (rG2 : reprG n2) :
  mx_rsim rG1 rG2 -> mx_faithful rG1 = mx_faithful rG2.
Admitted.

Lemma mx_rsim_factmod n (rG : reprG n) U V
                     (modU : mxmodule rG U) (modV : mxmodule rG V) :
    (U + V :=: 1%:M)%MS -> mxdirect (U + V) ->
  mx_rsim (factmod_repr modV) (submod_repr modU).
Admitted.

Lemma mxtrace_rsim n1 n2 (rG1 : reprG n1) (rG2 : reprG n2) :
  mx_rsim rG1 rG2 -> {in G, forall x, \tr (rG1 x) = \tr (rG2 x)}.
Admitted.

Lemma mx_rsim_scalar n1 n2 (rG1 : reprG n1) (rG2 : reprG n2) x c :
   x \in G -> mx_rsim rG1 rG2 -> rG1 x = c%:M -> rG2 x = c%:M.
Admitted.

End Similarity.

Section Socle.

Variables (gT : finGroupType) (G : {group gT}).
Variables (n : nat) (rG : mx_representation F G n) (sG : socleType rG).

Lemma socle_irr (W : sG) : mx_irreducible (socle_repr W).
Admitted.

Lemma socle_rsimP (W1 W2 : sG) :
  reflect (mx_rsim (socle_repr W1) (socle_repr W2)) (W1 == W2).
Admitted.

Local Notation mG U := (mxmodule rG U).
Local Notation sr modV := (submod_repr modV).

Lemma mx_rsim_in_submod U V (modU : mG U) (modV : mG V) :
  let U' := <<in_submod V U>>%MS in
    (U <= V)%MS ->
  exists modU' : mxmodule (sr modV) U', mx_rsim (sr modU) (sr modU').
Admitted.

Lemma rsim_submod1 U (modU : mG U) : (U :=: 1%:M)%MS -> mx_rsim (sr modU) rG.
Admitted.

Lemma mxtrace_submod1 U (modU : mG U) :
  (U :=: 1%:M)%MS -> {in G, forall x, \tr (sr modU x) = \tr (rG x)}.
Admitted.

Lemma mxtrace_dadd_mod U V W (modU : mG U) (modV : mG V) (modW : mG W) :
    (U + V :=: W)%MS -> mxdirect (U + V) ->
  {in G, forall x, \tr (sr modU x) + \tr (sr modV x) = \tr (sr modW x)}.
Admitted.

Lemma mxtrace_dsum_mod (I : finType) (P : pred I) U W
                       (modU : forall i, mG (U i)) (modW : mG W) :
    let S := (\sum_(i | P i) U i)%MS in (S :=: W)%MS -> mxdirect S ->
  {in G, forall x, \sum_(i | P i) \tr (sr (modU i) x) = \tr (sr modW x)}.
Admitted.

Lemma mxtrace_component U (simU : mxsimple rG U) :
   let V := component_mx rG U in
   let modV := component_mx_module rG U in let modU := mxsimple_module simU in
  {in G, forall x, \tr (sr modV x) = \tr (sr modU x) *+ (\rank V %/ \rank U)}.
Admitted.

Lemma mxtrace_Socle : let modS := Socle_module sG in
  {in G, forall x,
    \tr (sr modS x) = \sum_(W : sG) \tr (socle_repr W x) *+ socle_mult W}.
Admitted.

End Socle.

Section Clifford.

Variables (gT : finGroupType) (G H : {group gT}).
Hypothesis nsHG : H <| G.
Variables (n : nat) (rG : mx_representation F G n).
Let sHG := normal_sub nsHG.
Let nHG := normal_norm nsHG.
Let rH := subg_repr rG sHG.

Lemma Clifford_simple M x : mxsimple rH M -> x \in G -> mxsimple rH (M *m rG x).
Admitted.

Lemma Clifford_hom x m (U : 'M_(m, n)) :
  x \in 'C_G(H) -> (U <= dom_hom_mx rH (rG x))%MS.
Admitted.

Lemma Clifford_iso x U : x \in 'C_G(H) -> mx_iso rH U (U *m rG x).
Admitted.

Lemma Clifford_iso2 x U V :
  mx_iso rH U V -> x \in G -> mx_iso rH (U *m rG x) (V *m rG x).
Admitted.

Lemma Clifford_componentJ M x :
    mxsimple rH M -> x \in G ->
  (component_mx rH (M *m rG x) :=: component_mx rH M *m rG x)%MS.
Admitted.

Hypothesis irrG : mx_irreducible rG.

Lemma Clifford_basis M : mxsimple rH M ->
  {X : {set gT} | X \subset G &
    let S := \sum_(x in X) M *m rG x in S :=: 1%:M /\ mxdirect S}%MS.
Admitted.

Variable sH : socleType rH.

Definition Clifford_act (W : sH) x :=
  let Gx := subgP (subg G x) in
  PackSocle (component_socle sH (Clifford_simple (socle_simple W) Gx)).

Let valWact W x : (Clifford_act W x :=: W *m rG (sgval (subg G x)))%MS.
Admitted.

Fact Clifford_is_action : is_action G Clifford_act.
Admitted.

Definition Clifford_action := Action Clifford_is_action.

Local Notation "'Cl" := Clifford_action (at level 8) : action_scope.

Lemma val_Clifford_act W x : x \in G -> ('Cl%act W x :=: W *m rG x)%MS.
Admitted.

Lemma Clifford_atrans : [transitive G, on [set: sH] | 'Cl].
Admitted.

Lemma Clifford_Socle1 : Socle sH = 1%:M.
Admitted.

Lemma Clifford_rank_components (W : sH) : (#|sH| * \rank W)%N = n.
Admitted.

Theorem Clifford_component_basis M : mxsimple rH M ->
  {t : nat & {x_ : sH -> 'I_t -> gT |
    forall W, let sW := (\sum_j M *m rG (x_ W j))%MS in
      [/\ forall j, x_ W j \in G, (sW :=: W)%MS & mxdirect sW]}}.
Admitted.

Lemma Clifford_astab : H <*> 'C_G(H) \subset 'C([set: sH] | 'Cl).
Admitted.

Lemma Clifford_astab1 (W : sH) : 'C[W | 'Cl] = rstabs rG W.
Admitted.

Lemma Clifford_rstabs_simple (W : sH) :
  mxsimple (subg_repr rG (rstabs_sub rG W)) W.
Admitted.

End Clifford.

Section JordanHolder.

Variables (gT : finGroupType) (G : {group gT}).
Variables (n : nat) (rG : mx_representation F G n).
Local Notation modG := ((mxmodule rG) n).

Lemma section_module (U V : 'M_n) (modU : modG U) (modV : modG V) :
  mxmodule (factmod_repr modU) <<in_factmod U V>>%MS.
Admitted.

Definition section_repr U V (modU : modG U) (modV : modG V) :=
  submod_repr (section_module modU modV).

Lemma mx_factmod_sub U modU :
  mx_rsim (@section_repr U _ modU (mxmodule1 rG)) (factmod_repr modU).
Admitted.

Definition max_submod (U V : 'M_n) :=
  (U < V)%MS /\ (forall W, ~ [/\ modG W, U < W & W < V])%MS.

Lemma max_submodP U V (modU : modG U) (modV : modG V) :
  (U <= V)%MS -> (max_submod U V <-> mx_irreducible (section_repr modU modV)).
Admitted.

Lemma max_submod_eqmx U1 U2 V1 V2 :
  (U1 :=: U2)%MS -> (V1 :=: V2)%MS -> max_submod U1 V1 -> max_submod U2 V2.
Admitted.

Definition mx_subseries := all modG.

Definition mx_composition_series V :=
  mx_subseries V /\ (forall i, i < size V -> max_submod (0 :: V)`_i V`_i).
Local Notation mx_series := mx_composition_series.

Fact mx_subseries_module V i : mx_subseries V -> mxmodule rG V`_i.
Admitted.

Fact mx_subseries_module' V i : mx_subseries V -> mxmodule rG (0 :: V)`_i.
Admitted.

Definition subseries_repr V i (modV : all modG V) :=
  section_repr (mx_subseries_module' i modV) (mx_subseries_module i modV).

Definition series_repr V i (compV : mx_composition_series V) :=
  subseries_repr i (proj1 compV).

Lemma mx_series_lt V : mx_composition_series V -> path ltmx 0 V.
Admitted.

Lemma max_size_mx_series (V : seq 'M[F]_n) :
   path ltmx 0 V -> size V <= \rank (last 0 V).
Admitted.

Lemma mx_series_repr_irr V i (compV : mx_composition_series V) :
  i < size V -> mx_irreducible (series_repr i compV).
Admitted.

Lemma mx_series_rcons U V :
  mx_series (rcons U V) <-> [/\ mx_series U, modG V & max_submod (last 0 U) V].
Admitted.

Theorem mx_Schreier U :
    mx_subseries U -> path ltmx 0 U ->
  classically (exists V, [/\ mx_series V, last 0 V :=: 1%:M & subseq U V])%MS.
Admitted.

Lemma mx_second_rsim U V (modU : modG U) (modV : modG V) :
  let modI := capmx_module modU modV in let modA := addsmx_module modU modV in
  mx_rsim (section_repr modI modU) (section_repr modV modA).
Admitted.

Lemma section_eqmx_add U1 U2 V1 V2 modU1 modU2 modV1 modV2 :
    (U1 :=: U2)%MS -> (U1 + V1 :=: U2 + V2)%MS ->
  mx_rsim (@section_repr U1 V1 modU1 modV1) (@section_repr U2 V2 modU2 modV2).
Admitted.

Lemma section_eqmx U1 U2 V1 V2 modU1 modU2 modV1 modV2
                   (eqU : (U1 :=: U2)%MS) (eqV : (V1 :=: V2)%MS) :
  mx_rsim (@section_repr U1 V1 modU1 modV1) (@section_repr U2 V2 modU2 modV2).
Admitted.

Lemma mx_butterfly U V W modU modV modW :
    ~~ (U == V)%MS -> max_submod U W -> max_submod V W ->
  let modUV := capmx_module modU modV in
     max_submod (U :&: V)%MS U
  /\ mx_rsim (@section_repr V W modV modW) (@section_repr _ U modUV modU).
Admitted.

Lemma mx_JordanHolder_exists U V :
    mx_composition_series U -> modG V -> max_submod V (last 0 U) ->
  {W : seq 'M_n | mx_composition_series W & last 0 W = V}.
Admitted.

Let rsim_rcons U V compU compUV i : i < size U ->
  mx_rsim (@series_repr U i compU) (@series_repr (rcons U V) i compUV).
Admitted.

Let last_mod U (compU : mx_series U) : modG (last 0 U).
Admitted.

Let rsim_last U V modUm modV compUV :
  mx_rsim (@section_repr (last 0 U) V modUm modV)
          (@series_repr (rcons U V) (size U) compUV).
Admitted.
Local Notation rsimT := mx_rsim_trans.
Local Notation rsimC := mx_rsim_sym.

Lemma mx_JordanHolder U V compU compV :
  let m := size U in (last 0 U :=: last 0 V)%MS ->
  m = size V  /\ (exists p : 'S_m, forall i : 'I_m,
     mx_rsim (@series_repr U i compU) (@series_repr V (p i) compV)).
Admitted.

Lemma mx_JordanHolder_max U (m := size U) V compU modV :
    (last 0 U :=: 1%:M)%MS -> mx_irreducible (@factmod_repr _ G n rG V modV) ->
  exists i : 'I_m, mx_rsim (factmod_repr modV) (@series_repr U i compU).
Admitted.

End JordanHolder.

Bind Scope irrType_scope with socle_sort.

Section Regular.

Variables (gT : finGroupType) (G : {group gT}).
Local Notation nG := #|pred_of_set (gval G)|.

Local Notation rF := (GRing.Field.comUnitRingType F) (only parsing).
Local Notation aG := (regular_repr rF G).
Local Notation R_G := (group_ring rF G).

Lemma gring_free : row_free R_G.
Admitted.

Lemma gring_op_id A : (A \in R_G)%MS -> gring_op aG A = A.
Admitted.

Lemma gring_rowK A : (A \in R_G)%MS -> gring_mx aG (gring_row A) = A.
Admitted.

Lemma mem_gring_mx m a (M : 'M_(m, nG)) :
  (gring_mx aG a \in M *m R_G)%MS = (a <= M)%MS.
Admitted.

Lemma mem_sub_gring m A (M : 'M_(m, nG)) :
  (A \in M *m R_G)%MS = (A \in R_G)%MS && (gring_row A <= M)%MS.
Admitted.

Section GringMx.

Variables (n : nat) (rG : mx_representation F G n).

Lemma gring_mxP a : (gring_mx rG a \in enveloping_algebra_mx rG)%MS.
Admitted.

Lemma gring_opM A B :
  (B \in R_G)%MS -> gring_op rG (A *m B) = gring_op rG A *m gring_op rG B.
Admitted.

Hypothesis irrG : mx_irreducible rG.

Lemma rsim_regular_factmod :
  {U : 'M_nG & {modU : mxmodule aG U & mx_rsim rG (factmod_repr modU)}}.
Admitted.

Lemma rsim_regular_series U (compU : mx_composition_series aG U) :
    (last 0 U :=: 1%:M)%MS ->
  exists i : 'I_(size U), mx_rsim rG (series_repr i compU).
Admitted.

Hypothesis F'G : [char F]^'.-group G.

Lemma rsim_regular_submod :
  {U : 'M_nG & {modU : mxmodule aG U & mx_rsim rG (submod_repr modU)}}.
Admitted.

End GringMx.

Definition gset_mx (A : {set gT}) := \sum_(x in A) aG x.

Local Notation tG := #|pred_of_set (classes (gval G))|.

Definition classg_base := \matrix_(k < tG) mxvec (gset_mx (enum_val k)).

Let groupCl : {in G, forall x, {subset x ^: G <= G}}.
Admitted.

Lemma classg_base_free : row_free classg_base.
Admitted.

Lemma classg_base_center : (classg_base :=: 'Z(R_G))%MS.
Admitted.

Lemma regular_module_ideal m (M : 'M_(m, nG)) :
  mxmodule aG M = right_mx_ideal R_G (M *m R_G).
Admitted.

Definition irrType := socleType aG.
Identity Coercion type_of_irrType : irrType >-> socleType.

Variable sG : irrType.

Definition irr_degree (i : sG) := \rank (socle_base i).
Local Notation "'n_ i" := (irr_degree i) : group_ring_scope.
Local Open Scope group_ring_scope.

Lemma irr_degreeE i : 'n_i = \rank (socle_base i).
Admitted.
Lemma irr_degree_gt0 i : 'n_i > 0.
Admitted.

Definition irr_repr i : mx_representation F G 'n_i := socle_repr i.
Lemma irr_reprE i x : irr_repr i x = submod_mx (socle_module i) x.
Admitted.

Lemma rfix_regular : (rfix_mx aG G :=: gring_row (gset_mx G))%MS.
Admitted.

Lemma principal_comp_subproof : mxsimple aG (rfix_mx aG G).
Admitted.

Fact principal_comp_key : unit.
Admitted.
Definition principal_comp_def :=
  PackSocle (component_socle sG principal_comp_subproof).
Definition principal_comp := locked_with principal_comp_key principal_comp_def.
Local Notation "1" := principal_comp : irrType_scope.

Lemma irr1_rfix : (1%irr :=: rfix_mx aG G)%MS.
Admitted.

Lemma rank_irr1 : \rank 1%irr = 1%N.
Admitted.

Lemma degree_irr1 : 'n_1 = 1%N.
Admitted.

Definition Wedderburn_subring (i : sG) := <<i *m R_G>>%MS.

Local Notation "''R_' i" := (Wedderburn_subring i) : group_ring_scope.

Let sums_R : (\sum_i 'R_i :=: Socle sG *m R_G)%MS.
Admitted.

Lemma Wedderburn_ideal i : mx_ideal R_G 'R_i.
Admitted.

Lemma Wedderburn_direct : mxdirect (\sum_i 'R_i)%MS.
Admitted.

Lemma Wedderburn_disjoint i j : i != j -> ('R_i :&: 'R_j)%MS = 0.
Admitted.

Lemma Wedderburn_annihilate i j : i != j -> ('R_i * 'R_j)%MS = 0.
Admitted.

Lemma Wedderburn_mulmx0 i j A B :
  i != j -> (A \in 'R_i)%MS -> (B \in 'R_j)%MS -> A *m B = 0.
Admitted.

Hypothesis F'G : [char F]^'.-group G.

Lemma irr_mx_sum : (\sum_(i : sG) i = 1%:M)%MS.
Admitted.

Lemma Wedderburn_sum : (\sum_i 'R_i :=: R_G)%MS.
Admitted.

Definition Wedderburn_id i :=
  vec_mx (mxvec 1%:M *m proj_mx 'R_i (\sum_(j | j != i) 'R_j)%MS).

Local Notation "''e_' i" := (Wedderburn_id i) : group_ring_scope.

Lemma Wedderburn_sum_id : \sum_i 'e_i = 1%:M.
Admitted.

Lemma Wedderburn_id_mem i : ('e_i \in 'R_i)%MS.
Admitted.

Lemma Wedderburn_is_id i : mxring_id 'R_i 'e_i.
Admitted.

Lemma Wedderburn_closed i : ('R_i * 'R_i = 'R_i)%MS.
Admitted.

Lemma Wedderburn_is_ring i : mxring 'R_i.
Admitted.

Lemma Wedderburn_min_ideal m i (E : 'A_(m, nG)) :
  E != 0 -> (E <= 'R_i)%MS -> mx_ideal R_G E -> (E :=: 'R_i)%MS.
Admitted.

Section IrrComponent.

 
 

Variables (n : nat) (rG : mx_representation F G n).
Local Notation E_G := (enveloping_algebra_mx rG).

Let not_rsim_op0 (iG j : sG) A :
    mx_rsim rG (socle_repr iG) -> iG != j -> (A \in 'R_j)%MS ->
  gring_op rG A = 0.
Admitted.

Definition irr_comp := odflt 1%irr [pick i | gring_op rG 'e_i != 0].
Local Notation iG := irr_comp.

Hypothesis irrG : mx_irreducible rG.

Lemma rsim_irr_comp : mx_rsim rG (irr_repr iG).
Admitted.

Lemma irr_comp'_op0 j A : j != iG -> (A \in 'R_j)%MS -> gring_op rG A = 0.
Admitted.

Lemma irr_comp_envelop : ('R_iG *m lin_mx (gring_op rG) :=: E_G)%MS.
Admitted.

Lemma ker_irr_comp_op : ('R_iG :&: kermx (lin_mx (gring_op rG)))%MS = 0.
Admitted.

Lemma regular_op_inj :
  {in [pred A | (A \in 'R_iG)%MS] &, injective (gring_op rG)}.
Admitted.

Lemma rank_irr_comp : \rank 'R_iG = \rank E_G.
Admitted.

End IrrComponent.

Lemma irr_comp_rsim n1 n2 rG1 rG2 :
  @mx_rsim _ G n1 rG1 n2 rG2 -> irr_comp rG1 = irr_comp rG2.
Admitted.

Lemma irr_reprK i : irr_comp (irr_repr i) = i.
Admitted.

Lemma irr_repr'_op0 i j A :
  j != i -> (A \in 'R_j)%MS -> gring_op (irr_repr i) A = 0.
Admitted.

Lemma op_Wedderburn_id i : gring_op (irr_repr i) 'e_i = 1%:M.
Admitted.

Lemma irr_comp_id (M : 'M_nG) (modM : mxmodule aG M) (iM : sG) :
  mxsimple aG M -> (M <= iM)%MS -> irr_comp (submod_repr modM) = iM.
Admitted.

Lemma irr1_repr x : x \in G -> irr_repr 1 x = 1%:M.
Admitted.

Hypothesis splitG : group_splitting_field G.

Lemma rank_Wedderburn_subring i : \rank 'R_i = ('n_i ^ 2)%N.
Admitted.

Lemma sum_irr_degree : (\sum_i 'n_i ^ 2 = nG)%N.
Admitted.

Lemma irr_mx_mult i : socle_mult i = 'n_i.
Admitted.

Lemma mxtrace_regular :
  {in G, forall x, \tr (aG x) = \sum_i \tr (socle_repr i x) *+ 'n_i}.
Admitted.

Definition linear_irr := [set i | 'n_i == 1%N].

Lemma irr_degree_abelian : abelian G -> forall i, 'n_i = 1%N.
Admitted.

Lemma linear_irr_comp i : 'n_i = 1%N -> (i :=: socle_base i)%MS.
Admitted.

Lemma Wedderburn_subring_center i : ('Z('R_i) :=: mxvec 'e_i)%MS.
Admitted.

Lemma Wedderburn_center :
  ('Z(R_G) :=: \matrix_(i < #|sG|) mxvec 'e_(enum_val i))%MS.
Admitted.

Lemma card_irr : #|sG| = tG.
Admitted.

Section CenterMode.

Variable i : sG.

Let i0 := Ordinal (irr_degree_gt0 i).

Definition irr_mode x := irr_repr i x i0 i0.

Lemma irr_mode1 : irr_mode 1 = 1.
Admitted.

Lemma irr_center_scalar : {in 'Z(G), forall x, irr_repr i x = (irr_mode x)%:M}.
Admitted.

Lemma irr_modeM : {in 'Z(G) &, {morph irr_mode : x y / (x * y)%g >-> x * y}}.
Admitted.

Lemma irr_modeX n : {in 'Z(G), {morph irr_mode : x / (x ^+ n)%g >-> x ^+ n}}.
Admitted.

Lemma irr_mode_unit : {in 'Z(G), forall x, irr_mode x \is a GRing.unit}.
Admitted.

Lemma irr_mode_neq0 : {in 'Z(G), forall x, irr_mode x != 0}.
Admitted.

Lemma irr_modeV : {in 'Z(G), {morph irr_mode : x / (x^-1)%g >-> x^-1}}.
Admitted.

End CenterMode.

Lemma irr1_mode x : x \in G -> irr_mode 1 x = 1.
Admitted.

End Regular.

Local Notation "[ 1 sG ]" := (principal_comp sG) : irrType_scope.

Section LinearIrr.

Variables (gT : finGroupType) (G : {group gT}).

Lemma card_linear_irr (sG : irrType G) :
    [char F]^'.-group G -> group_splitting_field G ->
  #|linear_irr sG| = #|G : G^`(1)|%g.
Admitted.

Lemma primitive_root_splitting_abelian (z : F) :
  #|G|.-primitive_root z -> abelian G -> group_splitting_field G.
Admitted.

Lemma cycle_repr_structure x (sG : irrType G) :
    G :=: <[x]> -> [char F]^'.-group G -> group_splitting_field G ->
  exists2 w : F, #|G|.-primitive_root w &
  exists iphi : 'I_#|G| -> sG,
  [/\ bijective iphi,
      #|sG| = #|G|,
      forall i, irr_mode (iphi i) x = w ^+ i
    & forall i, irr_repr (iphi i) x = (w ^+ i)%:M].
Admitted.

Lemma splitting_cyclic_primitive_root :
    cyclic G -> [char F]^'.-group G -> group_splitting_field G ->
  classically {z : F | #|G|.-primitive_root z}.
Admitted.

End LinearIrr.

End FieldRepr.

Arguments rfix_mx {F gT G%g n%N} rG H%g.
Arguments gset_mx F {gT} G%g A%g.
Arguments classg_base F {gT} G%g _%g : extra scopes.
Arguments irrType F {gT} G%g.

Arguments mxmoduleP {F gT G n rG m U}.
Arguments envelop_mxP {F gT G n rG A}.
Arguments hom_mxP {F gT G n rG m f W}.
Arguments mx_Maschke [F gT G n] rG _ [U].
Arguments rfix_mxP {F gT G n rG m W}.
Arguments cyclic_mxP {F gT G n rG u v}.
Arguments annihilator_mxP {F gT G n rG u A}.
Arguments row_hom_mxP {F gT G n rG u v}.
Arguments mxsimple_isoP {F gT G n rG U V}.
Arguments socle_exists [F gT G n].
Arguments socleP {F gT G n rG sG0 W W'}.
Arguments mx_abs_irrP {F gT G n rG}.
Arguments socle_rsimP {F gT G n rG sG W1 W2}.

Arguments val_submod {F n U m} W.
Arguments in_submod {F n} U {m} W.
Arguments val_submodK {F n U m} W : rename.
Arguments in_submodK {F n U m} [W] sWU.
Arguments val_submod_inj {F n U m} [W1 W2] : rename.

Arguments val_factmod {F n U m} W.
Arguments in_factmod {F n} U {m} W.
Arguments val_factmodK {F n U m} W : rename.
Arguments in_factmodK {F n} U {m} [W] sWU.
Arguments val_factmod_inj {F n U m} [W1 W2] : rename.

Notation "'Cl" := (Clifford_action _) : action_scope.

Arguments gring_row {R gT G} A.
Arguments gring_rowK {F gT G} [A] RG_A.

Bind Scope irrType_scope with socle_sort.
Notation "[ 1 sG ]" := (principal_comp sG) : irrType_scope.
Arguments irr_degree {F gT G%G sG} i%irr.
Arguments irr_repr {F gT G%G sG} i%irr _%g : extra scopes.
Arguments irr_mode {F gT G%G sG} i%irr z%g : rename.
Notation "''n_' i" := (irr_degree i) : group_ring_scope.
Notation "''R_' i" := (Wedderburn_subring i) : group_ring_scope.
Notation "''e_' i" := (Wedderburn_id i) : group_ring_scope.

Section DecideRed.

Import MatrixFormula.
Local Notation term := GRing.term.
Local Notation True := GRing.True.
Local Notation And := GRing.And (only parsing).
Local Notation morphAnd f := ((big_morph f) true andb).
Local Notation eval := GRing.eval.
Local Notation holds := GRing.holds.
Local Notation qf_form := GRing.qf_form.
Local Notation qf_eval := GRing.qf_eval.

Section Definitions.

Variables (F : fieldType) (gT : finGroupType) (G : {group gT}) (n : nat).
Variable rG : mx_representation F G n.

Definition mxmodule_form (U : 'M[term F]_n) :=
  \big[And/True]_(x in G) submx_form (mulmx_term U (mx_term (rG x))) U.

Lemma mxmodule_form_qf U : qf_form (mxmodule_form U).
Admitted.

Lemma eval_mxmodule U e :
  qf_eval e (mxmodule_form U) = mxmodule rG (eval_mx e U).
Admitted.

Definition mxnonsimple_form (U : 'M[term F]_n) :=
  let V := vec_mx (row_var F (n * n) 0) in
  let nzV := (~ mxrank_form 0 V)%T in
  let properVU := (submx_form V U /\ ~ submx_form U V)%T in
  (Exists_row_form (n * n) 0 (mxmodule_form V /\ nzV /\ properVU))%T.

End Definitions.

Variables (F : decFieldType) (gT : finGroupType) (G : {group gT}) (n : nat).
Variable rG : mx_representation F G n.

Definition mxnonsimple_sat U :=
  GRing.sat (@row_env _ (n * n) [::]) (mxnonsimple_form rG (mx_term U)).

Lemma mxnonsimpleP U :
  U != 0 -> reflect (mxnonsimple rG U) (mxnonsimple_sat U).
Admitted.

Lemma dec_mxsimple_exists (U : 'M_n) :
  mxmodule rG U -> U != 0 -> {V | mxsimple rG V & V <= U}%MS.
Admitted.

Lemma dec_mx_reducible_semisimple U :
  mxmodule rG U -> mx_completely_reducible rG U -> mxsemisimple rG U.
Admitted.

Lemma DecSocleType : socleType rG.
Admitted.

End DecideRed.

Prenex Implicits mxmodule_form mxnonsimple_form mxnonsimple_sat.

 
Section ChangeOfField.

Variables (aF rF : fieldType) (f : {rmorphism aF -> rF}).
Local Notation "A ^f" := (map_mx (GRing.RMorphism.apply f) A) : ring_scope.
Variables (gT : finGroupType) (G : {group gT}).

Section OneRepresentation.

Variables (n : nat) (rG : mx_representation aF G n).
Local Notation rGf := (map_repr f rG).

Lemma map_rfix_mx H : (rfix_mx rG H)^f = rfix_mx rGf H.
Admitted.

Lemma rcent_map A : rcent rGf A^f = rcent rG A.
Admitted.

Lemma rstab_map m (U : 'M_(m, n)) : rstab rGf U^f = rstab rG U.
Admitted.

Lemma rstabs_map m (U : 'M_(m, n)) : rstabs rGf U^f = rstabs rG U.
Admitted.

Lemma centgmx_map A : centgmx rGf A^f = centgmx rG A.
Admitted.

Lemma mxmodule_map m (U : 'M_(m, n)) : mxmodule rGf U^f = mxmodule rG U.
Admitted.

Lemma mxsimple_map (U : 'M_n) : mxsimple rGf U^f -> mxsimple rG U.
Admitted.

Lemma mx_irr_map : mx_irreducible rGf -> mx_irreducible rG.
Admitted.

Lemma rker_map : rker rGf = rker rG.
Admitted.

Lemma map_mx_faithful : mx_faithful rGf = mx_faithful rG.
Admitted.

Lemma map_mx_abs_irr :
  mx_absolutely_irreducible rGf = mx_absolutely_irreducible rG.
Admitted.

End OneRepresentation.

Lemma mx_rsim_map n1 n2 rG1 rG2 :
  @mx_rsim _ _ G n1 rG1 n2 rG2 -> mx_rsim (map_repr f rG1) (map_repr f rG2).
Admitted.

Lemma map_section_repr n (rG : mx_representation aF G n) rGf U V
                       (modU : mxmodule rG U) (modV : mxmodule rG V)
                       (modUf : mxmodule rGf U^f) (modVf : mxmodule rGf V^f) :
    map_repr f rG =1 rGf ->
  mx_rsim (map_repr f (section_repr modU modV)) (section_repr modUf modVf).
Admitted.

Lemma map_regular_subseries U i (modU : mx_subseries (regular_repr aF G) U)
   (modUf : mx_subseries (regular_repr rF G) [seq M^f | M <- U]) :
  mx_rsim (map_repr f (subseries_repr i modU)) (subseries_repr i modUf).
Admitted.

Lemma extend_group_splitting_field :
  group_splitting_field aF G -> group_splitting_field rF G.
Admitted.

End ChangeOfField.

 
 
 
 
 
 
Module Import MatrixGenField.

 
 
 
Record gen_of {F : fieldType} {gT : finGroupType} {G : {group gT}} {n' : nat}
              {rG : mx_representation F G n'.+1} {A : 'M[F]_n'.+1}
              (irrG : mx_irreducible rG) (cGA : centgmx rG A) :=
   Gen {rVval : 'rV[F]_(degree_mxminpoly A)}.

Local Arguments rVval {F gT G%G n'%N rG A%R irrG cGA} x%R : rename.
Bind Scope ring_scope with gen_of.

Section GenField.

Variables (F : fieldType) (gT : finGroupType) (G : {group gT}) (n' : nat).
Local Notation n := n'.+1.
Variables (rG : mx_representation F G n) (A : 'M[F]_n).

Local Notation d := (degree_mxminpoly A).
Local Notation Ad := (powers_mx A d).
Local Notation pA := (mxminpoly A).
Let d_gt0 := mxminpoly_nonconstant A.
Local Notation irr := mx_irreducible.

Hypotheses (irrG : irr rG) (cGA : centgmx rG A).

Notation FA := (gen_of irrG cGA).
Let inFA := Gen irrG cGA.

Canonical gen_subType := Eval hnf in [newType for rVval : FA -> 'rV_d].
Definition gen_eqMixin := Eval hnf in [eqMixin of FA by <:].
Canonical gen_eqType := Eval hnf in EqType FA gen_eqMixin.
Definition gen_choiceMixin := [choiceMixin of FA by <:].
Canonical gen_choiceType := Eval hnf in ChoiceType FA gen_choiceMixin.

Definition gen0 := inFA 0.
Definition genN (x : FA) := inFA (- val x).
Definition genD (x y : FA) := inFA (val x + val y).

Lemma gen_addA : associative genD.
Admitted.

Lemma gen_addC : commutative genD.
Admitted.

Lemma gen_add0r : left_id gen0 genD.
Admitted.

Lemma gen_addNr : left_inverse gen0 genN genD.
Admitted.

Definition gen_zmodMixin := ZmodMixin gen_addA gen_addC gen_add0r gen_addNr.
Canonical gen_zmodType := Eval hnf in ZmodType FA gen_zmodMixin.

Definition pval (x : FA) := rVpoly (val x).

Definition mxval (x : FA) := horner_mx A (pval x).

Definition gen (x : F) := inFA (poly_rV x%:P).

Lemma genK x : mxval (gen x) = x%:M.
Admitted.

Lemma mxval_inj : injective mxval.
Admitted.

Lemma mxval0 : mxval 0 = 0.
Admitted.

Lemma mxvalN : {morph mxval : x / - x}.
Admitted.

Lemma mxvalD : {morph mxval : x y / x + y}.
Admitted.

Definition mxval_sum := big_morph mxval mxvalD mxval0.

Definition gen1 := inFA (poly_rV 1).
Definition genM x y := inFA (poly_rV (pval x * pval y %% pA)).
Definition genV x := inFA (poly_rV (mx_inv_horner A (mxval x)^-1)).

Lemma mxval_gen1 : mxval gen1 = 1%:M.
Admitted.

Lemma mxval_genM : {morph mxval : x y / genM x y >-> x *m y}.
Admitted.

Lemma mxval_genV : {morph mxval : x / genV x >-> invmx x}.
Admitted.

Lemma gen_mulA : associative genM.
Admitted.

Lemma gen_mulC : commutative genM.
Admitted.

Lemma gen_mul1r : left_id gen1 genM.
Admitted.

Lemma gen_mulDr : left_distributive genM +%R.
Admitted.

Lemma gen_ntriv : gen1 != 0.
Admitted.

Definition gen_ringMixin :=
  ComRingMixin gen_mulA gen_mulC gen_mul1r gen_mulDr gen_ntriv.
Canonical gen_ringType := Eval hnf in RingType FA gen_ringMixin.
Canonical gen_comRingType := Eval hnf in ComRingType FA gen_mulC.

Lemma mxval1 : mxval 1 = 1%:M.
Admitted.

Lemma mxvalM : {morph mxval : x y / x * y >-> x *m y}.
Admitted.

Lemma mxval_sub : additive mxval.
Admitted.
Canonical mxval_additive := Additive mxval_sub.

Lemma mxval_is_multiplicative : multiplicative mxval.
Admitted.
Canonical mxval_rmorphism := AddRMorphism mxval_is_multiplicative.

Lemma mxval_centg x : centgmx rG (mxval x).
Admitted.

Lemma gen_mulVr : GRing.Field.axiom genV.
Admitted.

Lemma gen_invr0 : genV 0 = 0.
Admitted.

Definition gen_unitRingMixin := FieldUnitMixin gen_mulVr gen_invr0.
Canonical gen_unitRingType :=
  Eval hnf in UnitRingType FA gen_unitRingMixin.
Canonical gen_comUnitRingType := Eval hnf in [comUnitRingType of FA].
Definition gen_fieldMixin :=
  @FieldMixin _ _ _ _ : GRing.Field.mixin_of gen_unitRingType.
Definition gen_idomainMixin := FieldIdomainMixin gen_fieldMixin.
Canonical gen_idomainType := Eval hnf in IdomainType FA gen_idomainMixin.
Canonical gen_fieldType := Eval hnf in FieldType FA gen_fieldMixin.

Lemma mxvalV : {morph mxval : x / x^-1 >-> invmx x}.
Admitted.

Lemma gen_is_rmorphism : rmorphism gen.
Admitted.
Canonical gen_additive := Additive gen_is_rmorphism.
Canonical gen_rmorphism := RMorphism gen_is_rmorphism.

 
 

Definition groot := inFA (poly_rV ('X %% pA)).

Lemma mxval_groot : mxval groot = A.
Admitted.

Lemma mxval_grootX k : mxval (groot ^+ k) = A ^+ k.
Admitted.

Lemma map_mxminpoly_groot : (map_poly gen pA).[groot] = 0.
Admitted.

 
 

Lemma non_linear_gen_reducible :
  d > 1 -> mxnonsimple (map_repr gen_rmorphism rG) 1%:M.
Admitted.

 
 
 
 
 
 
 
 
 

Definition subbase nA (B : 'rV_nA) : 'M_(nA * d, n) :=
  \matrix_ik mxvec (\matrix_(i, k) (row (B 0 i) (A ^+ k))) 0 ik.

Lemma gen_dim_ex_proof : exists nA, [exists B : 'rV_nA, row_free (subbase B)].
Admitted.

Lemma gen_dim_ub_proof nA :
  [exists B : 'rV_nA, row_free (subbase B)] -> (nA <= n)%N.
Admitted.

Definition gen_dim := ex_maxn gen_dim_ex_proof gen_dim_ub_proof.
Notation nA := gen_dim.

Definition gen_base : 'rV_nA := odflt 0 [pick B | row_free (subbase B)].
Definition base := subbase gen_base.

Lemma base_free : row_free base.
Admitted.

Lemma base_full : row_full base.
Admitted.

Lemma gen_dim_factor : (nA * d)%N = n.
Admitted.

Lemma gen_dim_gt0 : nA > 0.
Admitted.

Section Bijection.

Variable m : nat.

Definition in_gen (W : 'M[F]_(m, n)) : 'M[FA]_(m, nA) :=
  \matrix_(i, j) inFA (row j (vec_mx (row i W *m pinvmx base))).

Definition val_gen (W : 'M[FA]_(m, nA)) : 'M[F]_(m, n) :=
  \matrix_i (mxvec (\matrix_j val (W i j)) *m base).

Lemma in_genK : cancel in_gen val_gen.
Admitted.

Lemma val_genK : cancel val_gen in_gen.
Admitted.

Lemma in_gen0 : in_gen 0 = 0.
Admitted.

Lemma val_gen0 : val_gen 0 = 0.
Admitted.

Lemma in_genN : {morph in_gen : W / - W}.
Admitted.

Lemma val_genN : {morph val_gen : W / - W}.
Admitted.

Lemma in_genD : {morph in_gen : U V / U + V}.
Admitted.

Lemma val_genD : {morph val_gen : U V / U + V}.
Admitted.

Definition in_gen_sum := big_morph in_gen in_genD in_gen0.
Definition val_gen_sum := big_morph val_gen val_genD val_gen0.

Lemma in_genZ a : {morph in_gen : W / a *: W >-> gen a *: W}.
Admitted.

End Bijection.

Prenex Implicits val_genK in_genK.

Lemma val_gen_rV (w : 'rV_nA) :
  val_gen w = mxvec (\matrix_j val (w 0 j)) *m base.
Admitted.

Section Bijection2.

Variable m : nat.

Lemma val_gen_row W (i : 'I_m) : val_gen (row i W) = row i (val_gen W).
Admitted.

Lemma in_gen_row W (i : 'I_m) : in_gen (row i W) = row i (in_gen W).
Admitted.

Lemma row_gen_sum_mxval W (i : 'I_m) :
  row i (val_gen W) = \sum_j row (gen_base 0 j) (mxval (W i j)).
Admitted.

Lemma val_genZ x : {morph @val_gen m : W / x *: W >-> W *m mxval x}.
Admitted.

End Bijection2.

Lemma submx_in_gen m1 m2 (U : 'M_(m1, n)) (V : 'M_(m2, n)) :
  (U <= V -> in_gen U <= in_gen V)%MS.
Admitted.

Lemma submx_in_gen_eq m1 m2 (U : 'M_(m1, n)) (V : 'M_(m2, n)) :
  (V *m A <= V -> (in_gen U <= in_gen V) = (U <= V))%MS.
Admitted.

Definition gen_mx g := \matrix_i in_gen (row (gen_base 0 i) (rG g)).

Let val_genJmx m :
  {in G, forall g, {morph @val_gen m : W / W *m gen_mx g >-> W *m rG g}}.
Admitted.

Lemma gen_mx_repr : mx_repr G gen_mx.
Admitted.
Canonical gen_repr := MxRepresentation gen_mx_repr.
Local Notation rGA := gen_repr.

Lemma val_genJ m :
  {in G, forall g, {morph @val_gen m : W / W *m rGA g >-> W *m rG g}}.
Admitted.

Lemma in_genJ m :
  {in G, forall g, {morph @in_gen m : v / v *m rG g >-> v *m rGA g}}.
Admitted.

Lemma rfix_gen (H : {set gT}) :
  H \subset G -> (rfix_mx rGA H :=: in_gen (rfix_mx rG H))%MS.
Admitted.

Definition rowval_gen m U :=
  <<\matrix_ik
      mxvec (\matrix_(i < m, k < d) (row i (val_gen U) *m A ^+ k)) 0 ik>>%MS.

Lemma submx_rowval_gen m1 m2 (U : 'M_(m1, n)) (V : 'M_(m2, nA)) :
  (U <= rowval_gen V)%MS = (in_gen U <= V)%MS.
Admitted.

Lemma rowval_genK m (U : 'M_(m,  nA)) : (in_gen (rowval_gen U) :=: U)%MS.
Admitted.

Lemma rowval_gen_stable m (U : 'M_(m, nA)) :
  (rowval_gen U *m A <= rowval_gen U)%MS.
Admitted.

Lemma rstab_in_gen m (U : 'M_(m, n)) : rstab rGA (in_gen U) = rstab rG U.
Admitted.

Lemma rstabs_in_gen m (U : 'M_(m, n)) :
  rstabs rG U \subset rstabs rGA (in_gen U).
Admitted.

Lemma rstabs_rowval_gen m (U : 'M_(m, nA)) :
  rstabs rG (rowval_gen U) = rstabs rGA U.
Admitted.

Lemma mxmodule_rowval_gen m (U : 'M_(m, nA)) :
  mxmodule rG (rowval_gen U) = mxmodule rGA U.
Admitted.

Lemma gen_mx_irr : mx_irreducible rGA.
Admitted.

Lemma rker_gen : rker rGA = rker rG.
Admitted.

Lemma gen_mx_faithful : mx_faithful rGA = mx_faithful rG.
Admitted.

End GenField.

Section DecideGenField.

Import MatrixFormula.

Variable F : decFieldType.

Local Notation False := GRing.False.
Local Notation True := GRing.True.
Local Notation Bool b := (GRing.Bool b%bool).
Local Notation term := (GRing.term F).
Local Notation form := (GRing.formula F).

Local Notation morphAnd f := ((big_morph f) true andb).

Variables (gT : finGroupType) (G : {group gT}) (n' : nat).
Local Notation n := n'.+1.
Variables (rG : mx_representation F G n) (A : 'M[F]_n).
Hypotheses (irrG : mx_irreducible rG) (cGA : centgmx rG A).
Local Notation FA := (gen_of irrG cGA).
Local Notation inFA := (Gen irrG cGA).

Local Notation d := (degree_mxminpoly A).
Let d_gt0 : d > 0 := mxminpoly_nonconstant A.
Local Notation Ad := (powers_mx A d).

Let mxT (u : 'rV_d) := vec_mx (mulmx_term u (mx_term Ad)).

Let eval_mxT e u : eval_mx e (mxT u) = mxval (inFA (eval_mx e u)).
Admitted.

Let Ad'T := mx_term (pinvmx Ad).
Let mulT (u v : 'rV_d) := mulmx_term (mxvec (mulmx_term (mxT u) (mxT v))) Ad'T.

Lemma eval_mulT e u v :
  eval_mx e (mulT u v) = val (inFA (eval_mx e u) * inFA (eval_mx e v)).
Admitted.

Fixpoint gen_term t := match t with
| 'X_k => row_var _ d k
| x%:T => mx_term (val (x : FA))
| n1%:R => mx_term (val (n1%:R : FA))%R
| t1 + t2 => \row_i (gen_term t1 0%R i + gen_term t2 0%R i)
| - t1 => \row_i (- gen_term t1 0%R i)
| t1 *+ n1 => mulmx_term (mx_term n1%:R%:M)%R (gen_term t1)
| t1 * t2 => mulT (gen_term t1) (gen_term t2)
| t1^-1 => gen_term t1
| t1 ^+ n1 => iter n1 (mulT (gen_term t1)) (mx_term (val (1%R : FA)))
end%T.

Definition gen_env (e : seq FA) := row_env (map val e).

Lemma nth_map_rVval (e : seq FA) j : (map val e)`_j = val e`_j.
Admitted.

Lemma set_nth_map_rVval (e : seq FA) j v :
  set_nth 0 (map val e) j v = map val (set_nth 0 e j (inFA v)).
Admitted.

Lemma eval_gen_term e t :
  GRing.rterm t -> eval_mx (gen_env e) (gen_term t) = val (GRing.eval e t).
Admitted.

Fixpoint gen_form f := match f with
| Bool b => Bool b
| t1 == t2 => mxrank_form 0 (gen_term (t1 - t2))
| GRing.Unit t1 => mxrank_form 1 (gen_term t1)
| f1 /\ f2 => gen_form f1 /\ gen_form f2
| f1 \/ f2 =>  gen_form f1 \/ gen_form f2
| f1 ==> f2 => gen_form f1 ==> gen_form f2
| ~ f1 => ~ gen_form f1
| ('exists 'X_k, f1) => Exists_row_form d k (gen_form f1)
| ('forall 'X_k, f1) => ~ Exists_row_form d k (~ (gen_form f1))
end%T.

Lemma sat_gen_form e f : GRing.rformula f ->
  reflect (GRing.holds e f) (GRing.sat (gen_env e) (gen_form f)).
Proof.
have ExP := Exists_rowP; have set_val := set_nth_map_rVval.
elim: f e => //.
-
 by move=> b e _; apply: (iffP satP).
-
 rewrite /gen_form => t1 t2 e rt_t; set t := (_ - _)%T.
  have:= GRing.qf_evalP (gen_env e) (mxrank_form_qf 0 (gen_term t)).
  rewrite eval_mxrank mxrank_eq0 eval_gen_term // => tP.
  by rewrite (sameP satP tP) /= subr_eq0 val_eqE; apply: eqP.
-
 move=> f1 IH1 f2 IH2 s /= /andP[/(IH1 s)f1P /(IH2 s)f2P].
  by apply: (iffP satP) => [[/satP/f1P ? /satP/f2P] | [/f1P/satP ? /f2P/satP]].
