
(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "-projection-no-head-constant" "-w" "-redundant-canonical-projection" "-w" "-notation-overridden" "-w" "+duplicate-clear" "-w" "-ambiguous-paths" "-w" "+non-primitive-record" "-w" "+undeclared-scope" "-w" "+deprecated-hint-without-locality" "-w" "+deprecated-hint-rewrite-without-locality" "-w" "-elpi.add-const-for-axiom-or-sectionvar" "-w" "-opaque-let" "-w" "-argument-scope-delimiter" "-w" "-overwriting-delimiting-key" "-w" "-closed-notation-not-level-0" "-w" "-postfix-notation-not-level-1" "-w" "-deprecated-native-compiler-option" "-native-compiler" "ondemand" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/mathcomp/mathcomp" "mathcomp" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/HB" "HB" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/elpi" "elpi" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/elpi_elpi" "elpi_elpi" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/elpi_examples" "elpi_examples" "-I" "/github/workspace/builds/coq/coq-failing/_build_ci/mathcomp/mathcomp" "-top" "mathcomp.character.classfun") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 2537 lines to 103 lines, then from 116 lines to 1129 lines, then from 1134 lines to 287 lines, then from 300 lines to 1280 lines, then from 1285 lines to 292 lines, then from 305 lines to 1296 lines, then from 1300 lines to 533 lines *)
(* coqc version 8.21+alpha compiled with OCaml 4.14.1
   coqtop version runner-t7b1znuaq-project-4504-concurrent-5:/builds/coq/coq/_build/default,(HEAD detached at 995395a49c6a1) (995395a49c6a15a52eef2f9b0f48eebe4aaa49d6)
   Expected coqc runtime on this file: 5.577 sec *)








Require Stdlib.Init.Ltac.
Require Stdlib.Strings.String.
Require Stdlib.ssr.ssreflect.
Require Stdlib.ssr.ssrfun.
Require elpi_elpi.dummy.
Require elpi.elpi.
Require elpi.apps.locker.locker.
Require HB.structures.
Require mathcomp.ssreflect.ssreflect.
Require mathcomp.ssreflect.ssrnotations.
Require mathcomp.ssreflect.ssrfun.
Require Stdlib.ssr.ssrbool.
Require mathcomp.ssreflect.ssrbool.
Require mathcomp.ssreflect.eqtype.
Require Stdlib.NArith.BinNat.
Require Stdlib.PArith.BinPos.
Require Stdlib.NArith.Ndec.
Require Stdlib.setoid_ring.Ring.
Require mathcomp.ssreflect.ssrnat.
Require mathcomp.ssreflect.seq.
Require mathcomp.ssreflect.choice.
Require mathcomp.ssreflect.path.
Require mathcomp.ssreflect.div.
Require mathcomp.ssreflect.fintype.
Require mathcomp.ssreflect.tuple.
Require mathcomp.ssreflect.finfun.
Require mathcomp.ssreflect.bigop.
Require mathcomp.ssreflect.finset.
Require mathcomp.ssreflect.prime.
Require mathcomp.ssreflect.order.
Require mathcomp.ssreflect.binomial.
Require mathcomp.algebra.ssralg.
Require mathcomp.algebra.countalg.
Require mathcomp.ssreflect.ssrAC.
Require mathcomp.fingroup.fingroup.
Require mathcomp.algebra.poly.
Require mathcomp.algebra.ssrnum.
Require mathcomp.algebra.ssrint.
Require mathcomp.algebra.archimedean.
Require Stdlib.setoid_ring.Field_theory.
Require Stdlib.setoid_ring.Field_tac.
Require mathcomp.algebra.rat.
Require mathcomp.ssreflect.generic_quotient.
Require mathcomp.fingroup.morphism.
Require mathcomp.algebra.ring_quotient.
Require mathcomp.fingroup.perm.
Require mathcomp.algebra.polydiv.
Require mathcomp.fingroup.automorphism.
Require mathcomp.fingroup.quotient.
Require mathcomp.fingroup.action.
Require mathcomp.algebra.finalg.
Require mathcomp.algebra.zmodp.
Require mathcomp.algebra.matrix.
Require mathcomp.algebra.mxalgebra.
Require mathcomp.algebra.mxpoly.

Module Export AdmitTactic.
Module Import LocalFalse.
Inductive False : Prop := .
End LocalFalse.
Axiom proof_admitted : False.
Import Coq.Init.Ltac.
Tactic Notation "admit" := abstract case proof_admitted.
End AdmitTactic.

Module Export mathcomp_DOT_field_DOT_closed_field_WRAPPED.
Module Export closed_field.


Import HB.structures.
Import mathcomp.ssreflect.ssreflect.
Import mathcomp.ssreflect.ssrfun.
Import mathcomp.ssreflect.ssrbool.
Import mathcomp.ssreflect.eqtype.
Import mathcomp.ssreflect.choice.
Import mathcomp.ssreflect.ssrnat.
Import mathcomp.ssreflect.seq.
Import mathcomp.ssreflect.fintype.
Import mathcomp.ssreflect.generic_quotient.
Import mathcomp.ssreflect.bigop.
Import mathcomp.algebra.ssralg.
Import mathcomp.algebra.poly.
Import mathcomp.algebra.polydiv.
Import mathcomp.algebra.matrix.
Import mathcomp.algebra.mxpoly.
Import mathcomp.algebra.countalg.
Import mathcomp.algebra.ring_quotient.

























Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Module Export ClosedFieldQE.
Section ClosedFieldQE.

Variables (F : fieldType) (F_closed : GRing.closed_field_axiom F).

Notation fF := (@GRing.formula F).
Notation tF := (@GRing.term F).
Definition polyF := seq tF.

Notation cps T := ((T -> fF) -> fF).
Definition ret T1 : T1 -> cps T1. exact (fun x k => k x). Defined.
Definition bind T1 T2 (x : cps T1) (f : T1 -> cps T2) : cps T2. exact (fun k => x (fun x => f x k)). Defined.
Notation "''let' x <- y ; z" :=
  (bind y (fun x => z)) (at level 99, x at level 0, y at level 0,
    format "'[hv' ''let'  x  <-  y ;  '/' z ']'").
Definition cpsif T (c : fF) (t : T) (e : T) : cps T. exact (fun k => GRing.If c (k t) (k e)). Defined.
Notation "''if' c1 'then' c2 'else' c3" := (cpsif c1%T c2%T c3%T)
  (at level 200, right associativity, format
"'[hv   ' ''if'  c1  '/' '[' 'then'  c2  ']' '/' '[' 'else'  c3 ']' ']'").
Definition sizeT : polyF -> cps nat. exact ((fix loop p :=
  if p isn't c :: q then ret 0
  else 'let n <- loop q;
       if n is m.+1 then ret m.+2 else
       'if (c == 0) then 0%N else 1%N)). Defined.
Definition isnull (p : polyF) : cps bool. exact ('let n <- sizeT p; ret (n == 0)). Defined.
Definition lt_sizeT (p q : polyF) : cps bool. exact ('let n <- sizeT p; 'let m <- sizeT q; ret (n < m)). Defined.

Fixpoint lead_coefT p : cps tF :=
  if p is c :: q then
    'let l <- lead_coefT q; 'if (l == 0) then c else l
  else ret 0%T.
Fixpoint amulXnT (a : tF) (n : nat) : polyF. exact (if n is n'.+1 then 0%T :: (amulXnT a n') else [:: a]). Defined.

Fixpoint sumpT (p q : polyF) :=
  match p, q with a :: p, b :: q => (a + b)%T :: sumpT p q
                | [::], q => q | p, [::] => p end.

Fixpoint mulpT (p q : polyF) :=
  if p isn't a :: p then [::]
  else sumpT [seq (a * x)%T | x <- q] (0%T :: mulpT p q).
Definition opppT : polyF -> polyF. exact (map (GRing.Mul (- 1%T)%T)). Defined.

Definition natmulpT n : polyF -> polyF := map (GRing.Mul n%:R%T).

Fixpoint redivp_rec_loopT (q : polyF) sq cq (c : nat) (qq r : polyF)
  (n : nat) {struct n} : cps (nat * polyF * polyF) :=
  'let sr <- sizeT r;
  if sr < sq then ret (c, qq, r) else
  'let lr <- lead_coefT r;
  let m := amulXnT lr (sr - sq) in
  let qq1 := sumpT (mulpT qq [::cq]) m in
  let r1 := sumpT (mulpT r ([::cq])) (opppT (mulpT m q)) in
  if n is n1.+1 then redivp_rec_loopT q sq cq c.+1 qq1 r1 n1
  else ret (c.+1, qq1, r1).
Definition redivpT (p : polyF) (q : polyF) : cps (nat * polyF * polyF). exact ('let b <- isnull q;
  if b then ret (0, [::0%T], p) else
  'let sq <- sizeT q; 'let sp <- sizeT p;
  'let lq <- lead_coefT q;
  redivp_rec_loopT q sq lq 0 [::0%T] p sp). Defined.
Definition rmodpT (p : polyF) (q : polyF) : cps polyF. exact ('let d <- redivpT p q; ret d.2). Defined.
Definition rdivpT (p : polyF) (q : polyF) : cps polyF. exact ('let d <- redivpT p q; ret d.1.2). Defined.

Fixpoint rgcdp_loopT n (pp : polyF) (qq : polyF) : cps polyF :=
  'let rr <- rmodpT pp qq; 'let nrr <- isnull rr; if nrr then ret qq
    else if n is n1.+1 then rgcdp_loopT n1 qq rr else ret rr.
Definition rgcdpT (p : polyF) (q : polyF) : cps polyF. exact (let aux p1 q1 : cps polyF :=
    'let b <- isnull p1; if b then ret q1
    else 'let n <- sizeT p1; rgcdp_loopT n p1 q1 in
  'let b <- lt_sizeT p q; if b then aux q p else aux p q). Defined.
Fixpoint rgcdpTs (ps : seq polyF) : cps polyF. exact (if ps is p :: pr then 'let pr <- rgcdpTs pr; rgcdpT p pr else ret [::0%T]). Defined.

Fixpoint rgdcop_recT n (q : polyF) (p : polyF) :=
  if n is m.+1 then
    'let g <- rgcdpT p q; 'let sg <- sizeT g;
    if sg == 1 then ret p
    else 'let r <- rdivpT p g;
          rgdcop_recT m q r
  else 'let b <- isnull q; ret [::b%:R%T].

Definition rgdcopT q p := 'let sp <- sizeT p; rgdcop_recT sp q p.
Definition ex_elim_seq (ps : seq polyF) (q : polyF) : fF. exact (('let g <- rgcdpTs ps; 'let d <- rgdcopT q g;
  'let n <- sizeT d; ret (n != 1)) GRing.Bool). Defined.

Fixpoint abstrX (i : nat) (t : tF) :=
  match t with
    | 'X_n => if n == i then [::0; 1] else [::t]
    | - x => opppT (abstrX i x)
    | x + y => sumpT (abstrX i x) (abstrX i y)
    | x * y => mulpT (abstrX i x) (abstrX i y)
    | x *+ n => natmulpT n (abstrX i x)
    | x ^+ n => let ax := (abstrX i x) in iter n (mulpT ax) [::1]
    | _ => [::t]
  end%T.

Definition ex_elim (x : nat) (pqs : seq tF * seq tF) :=
  ex_elim_seq (map (abstrX x) pqs.1)
  (abstrX x (\big[GRing.Mul/1%T]_(q <- pqs.2) q)).

Lemma holds_ex_elim: GRing.valid_QE_proj ex_elim.
Admitted.

Lemma wf_ex_elim : GRing.wf_QE_proj ex_elim.
admit.
Defined.

End ClosedFieldQE.

HB.factory Record Field_isAlgClosed F of GRing.Field F := {
  solve_monicpoly : GRing.closed_field_axiom F;
}.

HB.builders Context F of Field_isAlgClosed F.
  HB.instance Definition _ := GRing.Field_QE_isDecField.Build F
    (@ClosedFieldQE.wf_ex_elim F)
    (ClosedFieldQE.holds_ex_elim solve_monicpoly).
  HB.instance Definition _ := GRing.DecField_isAlgClosed.Build F
    solve_monicpoly.
HB.end.
Import mathcomp.ssreflect.ssrfun.
Import mathcomp.algebra.ssralg.

Theorem Fundamental_Theorem_of_Algebraics :
  {L : closedFieldType &
     {conj : {rmorphism L -> L} | involutive conj & ~ conj =1 id}}.
Admitted.

Import HB.structures.
Import mathcomp.ssreflect.ssrbool.
Import mathcomp.ssreflect.ssrnat.
Import mathcomp.ssreflect.eqtype.
Import mathcomp.ssreflect.seq.
Import mathcomp.ssreflect.choice.
Import mathcomp.ssreflect.order.
Import mathcomp.algebra.poly.
Import mathcomp.algebra.mxpoly.
Import mathcomp.ssreflect.generic_quotient.
Import mathcomp.algebra.ssrnum.
Import mathcomp.algebra.rat.

Set Implicit Arguments.
Unset Strict Implicit.
Import GRing.Theory.
Local Open Scope ring_scope.

HB.factory Record isComplex L of GRing.ClosedField L  := {
  conj :  {rmorphism L -> L};
  conjK : involutive conj;
  conj_nt : ~ conj =1 id
}.

HB.builders Context L of isComplex L.

Definition sqrt x : L :=
  sval (sig_eqW (@solve_monicpoly _ 2%N (nth 0 [:: x]) isT)).

Lemma sqrtK x: sqrt x ^+ 2 = x.
Admitted.

Definition norm x := sqrt x * conj (sqrt x).

Lemma normK x : norm x ^+ 2 = x * conj x.
Admitted.

Lemma norm_eq0 x : norm x = 0 -> x = 0.
Admitted.

Lemma normM x y : norm (x * y) = norm x * norm y.
Admitted.

Definition le x y := norm (y - x) == y - x.
Definition lt x y := (y != x) && le x y.

Lemma pos_linear x y : le 0 x -> le 0 y -> le x y || le y x.
Admitted.

Lemma sposD x y : lt 0 x -> lt 0 y -> lt 0 (x + y).
Admitted.

Lemma normD x y : le (norm (x + y)) (norm x + norm y).
Admitted.

HB.instance Definition _ :=
  Num.IntegralDomain_isNumRing.Build L normD sposD norm_eq0
         pos_linear normM (fun x y => erefl (le x y))
                          (fun x y => erefl (lt x y)).

HB.instance Definition _ :=
  Num.NumField_isImaginary.Build L (sqrtK _) normK.

HB.end.

Module Type Specification.

Parameter type : Type.

Parameter conjMixin : Num.ClosedField type.

End Specification.

Module Implementation : Specification.

Definition L := tag Fundamental_Theorem_of_Algebraics.
Definition conjL : {rmorphism L -> L}.
Admitted.

Fact conjL_K : involutive conjL.
Admitted.

Fact conjL_nt : ~ conjL =1 id.
Admitted.
Definition L' : Type.
exact (eta L).
Defined.
HB.instance Definition _ := GRing.ClosedField.on L'.
HB.instance Definition _ := isComplex.Build L' conjL_K conjL_nt.

Notation cfType := (L' : closedFieldType).

Definition QtoL : {rmorphism _ -> _} := @ratr cfType.

Notation pQtoL := (map_poly QtoL).

Definition rootQtoL p_j :=
  if p_j.1 == 0 then 0 else
  (sval (closed_field_poly_normal (pQtoL p_j.1)))`_p_j.2.

Definition eq_root p_j q_k := rootQtoL p_j == rootQtoL q_k.

Fact eq_root_is_equiv : equiv_class_of eq_root.
Admitted.
Canonical eq_root_equiv := EquivRelPack eq_root_is_equiv.
Definition type : Type.
exact ({eq_quot eq_root}%qT).
Defined.
HB.instance Definition _ := Choice.on type.

Definition CtoL (u : type) := rootQtoL (repr u).

Fact CtoL_P u : integralOver QtoL (CtoL u).
Admitted.

Fact LtoC_subproof z : integralOver QtoL z -> {u | CtoL u = z}.
Admitted.

Definition LtoC z Az := sval (@LtoC_subproof z Az).

Definition zero := LtoC (integral0 _).
Definition add u v := LtoC (integral_add (CtoL_P u) (CtoL_P v)).
Definition opp u := LtoC (integral_opp (CtoL_P u)).

Fact addA : associative add.
Admitted.

Fact addC : commutative add.
Admitted.

Fact add0 : left_id zero add.
Admitted.

Fact addN : left_inverse zero opp add.
Admitted.

HB.instance Definition _ := GRing.isZmodule.Build type addA addC add0 addN.

Definition one := LtoC (integral1 _).
Definition mul u v := LtoC (integral_mul (CtoL_P u) (CtoL_P v)).
Definition inv u := LtoC (integral_inv (CtoL_P u)).

Fact mulA : associative mul.
Admitted.

Fact mulC : commutative mul.
Admitted.

Fact mul1 : left_id one mul.
Admitted.

Fact mulD : left_distributive mul +%R.
Admitted.

Fact one_nz : one != 0 :> type.
Admitted.

HB.instance Definition _ :=
  GRing.Zmodule_isComRing.Build type mulA mulC mul1 mulD one_nz.

Fact mulVf u :  u != 0 -> inv u * u = 1.
Admitted.

Fact inv0 : inv 0 = 0.
Admitted.

HB.instance Definition _ := GRing.ComRing_isField.Build type mulVf inv0.

Fact closedFieldAxiom : GRing.closed_field_axiom type.
Admitted.

HB.instance Definition _ := Field_isAlgClosed.Build type closedFieldAxiom.
Definition conj : {rmorphism type -> type}.
Admitted.

Lemma conjK : involutive conj.
Admitted.

Fact conj_nt : ~ conj =1 id.
Admitted.

HB.instance Definition _ := isComplex.Build type conjK conj_nt.

Definition conjMixin := Num.ClosedField.on type.

End Implementation.

#[export] HB.instance Definition _ := Implementation.conjMixin.
Import Implementation.

Notation algC := type.
Import mathcomp.ssreflect.ssreflect.
Import mathcomp.ssreflect.fintype.
Import mathcomp.ssreflect.finfun.
Import mathcomp.ssreflect.finset.
Import mathcomp.fingroup.fingroup.
Import GroupScope.
Import Num.Theory.
Local Open Scope ring_scope.

Section Defs.

Variable gT : finGroupType.

Definition is_class_fun (B : {set gT}) (f : {ffun gT -> algC}) :=
  [forall x, forall y in B, f (x ^ y) == f x] && (support f \subset B).

Variable B : {set gT}.
Local Notation G := <<B>>.

Record classfun : predArgType :=
  Classfun {cfun_val; _ : is_class_fun G cfun_val}.
Implicit Types phi psi xi : classfun.

Fact classfun_key : unit.
Admitted.
Definition Cfun := locked_with classfun_key (fun flag : nat => Classfun).

HB.instance Definition _ := [isSub for cfun_val].
HB.instance Definition _ := [Choice of classfun by <:].

Definition fun_of_cfun phi := cfun_val phi : gT -> algC.
Coercion fun_of_cfun : classfun >-> Funclass.

Fact cfun_zero_subproof : is_class_fun G (0 : {ffun _}).
Admitted.
Definition cfun_zero := Cfun 0 cfun_zero_subproof.

Fact cfun_comp_subproof f phi :
  f 0 = 0 -> is_class_fun G [ffun x => f (phi x)].
Admitted.
Definition cfun_comp f f0 phi := Cfun 0 (@cfun_comp_subproof f phi f0).
Definition cfun_opp := cfun_comp (oppr0 _).

Fact cfun_add_subproof phi psi : is_class_fun G [ffun x => phi x + psi x].
Admitted.
Definition cfun_add phi psi := Cfun 0 (cfun_add_subproof phi psi).

Definition cfun_scale a := cfun_comp (mulr0 a).

Fact cfun_addA : associative cfun_add.
Admitted.
Fact cfun_addC : commutative cfun_add.
Admitted.
Fact cfun_add0 : left_id cfun_zero cfun_add.
Admitted.
Fact cfun_addN : left_inverse cfun_zero cfun_opp cfun_add.
Admitted.

HB.instance Definition _ := GRing.isZmodule.Build classfun
  cfun_addA cfun_addC cfun_add0 cfun_addN.

Fact cfun_scaleA a b phi :
  cfun_scale a (cfun_scale b phi) = cfun_scale (a * b) phi.
Admitted.
Fact cfun_scale1 : left_id 1 cfun_scale.
Admitted.
Fact cfun_scaleDr : right_distributive cfun_scale +%R.
Admitted.
Fact cfun_scaleDl phi : {morph cfun_scale^~ phi : a b / a + b}.
Admitted.

HB.instance Definition _ := GRing.Zmodule_isLmodule.Build algC classfun
  cfun_scaleA cfun_scale1 cfun_scaleDr cfun_scaleDl.

Definition cfdot phi psi := #|B|%:R^-1 * \sum_(x in B) phi x * (psi x)^*.
Definition cfdotr psi phi := cfdot phi psi.

End Defs.

Notation "''CF' ( G )" := (classfun G) : type_scope.

Section DotProduct.

Variable (gT : finGroupType) (G : {group gT}).

Lemma cfdotr_is_linear xi : linear (cfdotr xi : 'CF(G) -> algC^o).
Proof.
move=> a phi psi; rewrite scalerAr -mulrDr; congr (_ * _).
