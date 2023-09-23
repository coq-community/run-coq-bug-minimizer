
(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "-projection-no-head-constant" "-w" "-redundant-canonical-projection" "-w" "-notation-overridden" "-w" "-deprecated-native-compiler-option" "-native-compiler" "ondemand" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/oddorder/theories" "odd_order" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/HB" "HB" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/elpi" "elpi" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/mathcomp" "mathcomp" "-top" "Top.bug_01") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 1375 lines to 60 lines, then from 73 lines to 1675 lines, then from 1680 lines to 90 lines, then from 103 lines to 2712 lines, then from 2715 lines to 148 lines, then from 161 lines to 2932 lines, then from 2936 lines to 147 lines, then from 160 lines to 1746 lines, then from 1749 lines to 189 lines, then from 202 lines to 1254 lines, then from 1259 lines to 145 lines, then from 158 lines to 976 lines, then from 981 lines to 153 lines, then from 166 lines to 775 lines, then from 779 lines to 245 lines, then from 239 lines to 175 lines, then from 188 lines to 604 lines, then from 609 lines to 168 lines, then from 181 lines to 1580 lines, then from 1585 lines to 231 lines, then from 244 lines to 1254 lines, then from 1259 lines to 261 lines, then from 274 lines to 1855 lines, then from 1859 lines to 261 lines, then from 274 lines to 3310 lines, then from 3315 lines to 2052 lines, then from 1806 lines to 484 lines, then from 497 lines to 2159 lines, then from 2164 lines to 571 lines, then from 584 lines to 3152 lines, then from 3155 lines to 2910 lines, then from 2767 lines to 646 lines, then from 659 lines to 3393 lines, then from 3398 lines to 3162 lines *)
(* coqc version 8.19+alpha compiled with OCaml 4.14.1
   coqtop version 728713d43dde:/builds/coq/coq/_build/default,(HEAD detached at 25e3b11) (25e3b11cee094cfce7e16d10e58d3b7b318ea70c)
   Expected coqc runtime on this file: 8.693 sec *)
Require Coq.Init.Ltac.
Require Coq.Bool.Bool.
Require Coq.Floats.PrimFloat.
Require Coq.NArith.BinNat.
Require Coq.NArith.Ndec.
Require Coq.Numbers.Cyclic.Int63.PrimInt63.
Require Coq.PArith.BinPos.
Require Coq.Strings.String.
Require Coq.setoid_ring.Ring.
Require Coq.ssr.ssrbool.
Require Coq.ssr.ssreflect.
Require Coq.ssr.ssrfun.
Require mathcomp.ssreflect.ssrnotations.
Require mathcomp.ssreflect.ssreflect.
Require elpi.elpi.
Require mathcomp.ssreflect.ssrfun.
Require mathcomp.ssreflect.ssrbool.
Require HB.structures.
Require mathcomp.ssreflect.eqtype.
Require mathcomp.ssreflect.ssrnat.
Require mathcomp.ssreflect.seq.
Require mathcomp.ssreflect.choice.
Require mathcomp.ssreflect.div.
Require mathcomp.ssreflect.path.
Require mathcomp.ssreflect.fintype.
Require mathcomp.ssreflect.tuple.
Require mathcomp.ssreflect.finfun.

Module Export AdmitTactic.
Module Import LocalFalse.
Inductive False : Prop := .
End LocalFalse.
Axiom proof_admitted : False.
Import Coq.Init.Ltac.
Tactic Notation "admit" := abstract case proof_admitted.
End AdmitTactic.

Module mathcomp_DOT_ssreflect_DOT_bigop_WRAPPED.
Module bigop.
 
 
Import HB.structures.
Import mathcomp.ssreflect.ssreflect mathcomp.ssreflect.ssrbool mathcomp.ssreflect.ssrfun mathcomp.ssreflect.eqtype mathcomp.ssreflect.ssrnat mathcomp.ssreflect.seq mathcomp.ssreflect.path.
Import mathcomp.ssreflect.div mathcomp.ssreflect.fintype mathcomp.ssreflect.tuple mathcomp.ssreflect.finfun.

 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope big_scope.

Reserved Notation "\big [ op / idx ]_ i F"
  (at level 36, F at level 36, op, idx at level 10, i at level 0,
     right associativity,
           format "'[' \big [ op / idx ]_ i '/  '  F ']'").
Reserved Notation "\big [ op / idx ]_ ( i <- r | P ) F"
  (at level 36, F at level 36, op, idx at level 10, i, r at level 50,
           format "'[' \big [ op / idx ]_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\big [ op / idx ]_ ( i <- r ) F"
  (at level 36, F at level 36, op, idx at level 10, i, r at level 50,
           format "'[' \big [ op / idx ]_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\big [ op / idx ]_ ( m <= i < n | P ) F"
  (at level 36, F at level 36, op, idx at level 10, m, i, n at level 50,
           format "'[' \big [ op / idx ]_ ( m  <=  i  <  n  |  P )  F ']'").
Reserved Notation "\big [ op / idx ]_ ( m <= i < n ) F"
  (at level 36, F at level 36, op, idx at level 10, i, m, n at level 50,
           format "'[' \big [ op / idx ]_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\big [ op / idx ]_ ( i | P ) F"
  (at level 36, F at level 36, op, idx at level 10, i at level 50,
           format "'[' \big [ op / idx ]_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\big [ op / idx ]_ ( i : t | P ) F"
  (at level 36, F at level 36, op, idx at level 10, i at level 50,
           format "'[' \big [ op / idx ]_ ( i   :  t   |  P ) '/  '  F ']'").
Reserved Notation "\big [ op / idx ]_ ( i : t ) F"
  (at level 36, F at level 36, op, idx at level 10, i at level 50,
           format "'[' \big [ op / idx ]_ ( i   :  t ) '/  '  F ']'").
Reserved Notation "\big [ op / idx ]_ ( i < n | P ) F"
  (at level 36, F at level 36, op, idx at level 10, i, n at level 50,
           format "'[' \big [ op / idx ]_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\big [ op / idx ]_ ( i < n ) F"
  (at level 36, F at level 36, op, idx at level 10, i, n at level 50,
           format "'[' \big [ op / idx ]_ ( i  <  n )  F ']'").
Reserved Notation "\big [ op / idx ]_ ( i 'in' A | P ) F"
  (at level 36, F at level 36, op, idx at level 10, i, A at level 50,
           format "'[' \big [ op / idx ]_ ( i  'in'  A  |  P ) '/  '  F ']'").
Reserved Notation "\big [ op / idx ]_ ( i 'in' A ) F"
  (at level 36, F at level 36, op, idx at level 10, i, A at level 50,
           format "'[' \big [ op / idx ]_ ( i  'in'  A ) '/  '  F ']'").

Reserved Notation "\sum_ i F"
  (at level 41, F at level 41, i at level 0,
           right associativity,
           format "'[' \sum_ i '/  '  F ']'").
Reserved Notation "\sum_ ( i <- r | P ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \sum_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\sum_ ( i <- r ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \sum_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\sum_ ( m <= i < n | P ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \sum_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\sum_ ( m <= i < n ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \sum_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\sum_ ( i | P ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \sum_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\sum_ ( i : t | P ) F"
  (at level 41, F at level 41, i at level 50).
 
Reserved Notation "\sum_ ( i : t ) F"
  (at level 41, F at level 41, i at level 50).
 
Reserved Notation "\sum_ ( i < n | P ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \sum_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\sum_ ( i < n ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \sum_ ( i  <  n ) '/  '  F ']'").
Reserved Notation "\sum_ ( i 'in' A | P ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \sum_ ( i  'in'  A  |  P ) '/  '  F ']'").
Reserved Notation "\sum_ ( i 'in' A ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \sum_ ( i  'in'  A ) '/  '  F ']'").

Reserved Notation "\max_ i F"
  (at level 41, F at level 41, i at level 0,
           format "'[' \max_ i '/  '  F ']'").
Reserved Notation "\max_ ( i <- r | P ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \max_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\max_ ( i <- r ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \max_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\max_ ( m <= i < n | P ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \max_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\max_ ( m <= i < n ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \max_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\max_ ( i | P ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \max_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\max_ ( i : t | P ) F"
  (at level 41, F at level 41, i at level 50).
 
Reserved Notation "\max_ ( i : t ) F"
  (at level 41, F at level 41, i at level 50).
 
Reserved Notation "\max_ ( i < n | P ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \max_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\max_ ( i < n ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \max_ ( i  <  n )  F ']'").
Reserved Notation "\max_ ( i 'in' A | P ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \max_ ( i  'in'  A  |  P ) '/  '  F ']'").
Reserved Notation "\max_ ( i 'in' A ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \max_ ( i  'in'  A ) '/  '  F ']'").

Reserved Notation "\prod_ i F"
  (at level 36, F at level 36, i at level 0,
           format "'[' \prod_ i '/  '  F ']'").
Reserved Notation "\prod_ ( i <- r | P ) F"
  (at level 36, F at level 36, i, r at level 50,
           format "'[' \prod_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\prod_ ( i <- r ) F"
  (at level 36, F at level 36, i, r at level 50,
           format "'[' \prod_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\prod_ ( m <= i < n | P ) F"
  (at level 36, F at level 36, i, m, n at level 50,
           format "'[' \prod_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\prod_ ( m <= i < n ) F"
  (at level 36, F at level 36, i, m, n at level 50,
           format "'[' \prod_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\prod_ ( i | P ) F"
  (at level 36, F at level 36, i at level 50,
           format "'[' \prod_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\prod_ ( i : t | P ) F"
  (at level 36, F at level 36, i at level 50).
 
Reserved Notation "\prod_ ( i : t ) F"
  (at level 36, F at level 36, i at level 50).
 
Reserved Notation "\prod_ ( i < n | P ) F"
  (at level 36, F at level 36, i, n at level 50,
           format "'[' \prod_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\prod_ ( i < n ) F"
  (at level 36, F at level 36, i, n at level 50,
           format "'[' \prod_ ( i  <  n ) '/  '  F ']'").
Reserved Notation "\prod_ ( i 'in' A | P ) F"
  (at level 36, F at level 36, i, A at level 50,
           format "'[' \prod_ ( i  'in'  A  |  P )  F ']'").
Reserved Notation "\prod_ ( i 'in' A ) F"
  (at level 36, F at level 36, i, A at level 50,
           format "'[' \prod_ ( i  'in'  A ) '/  '  F ']'").

Reserved Notation "\bigcup_ i F"
  (at level 41, F at level 41, i at level 0,
           format "'[' \bigcup_ i '/  '  F ']'").
Reserved Notation "\bigcup_ ( i <- r | P ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \bigcup_ ( i  <-  r  |  P ) '/  '  F ']'").
Reserved Notation "\bigcup_ ( i <- r ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \bigcup_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\bigcup_ ( m <= i < n | P ) F"
  (at level 41, F at level 41, m, i, n at level 50,
           format "'[' \bigcup_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\bigcup_ ( m <= i < n ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \bigcup_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\bigcup_ ( i | P ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \bigcup_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\bigcup_ ( i : t | P ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \bigcup_ ( i   :  t   |  P ) '/  '  F ']'").
Reserved Notation "\bigcup_ ( i : t ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \bigcup_ ( i   :  t ) '/  '  F ']'").
Reserved Notation "\bigcup_ ( i < n | P ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \bigcup_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\bigcup_ ( i < n ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \bigcup_ ( i  <  n ) '/  '  F ']'").
Reserved Notation "\bigcup_ ( i 'in' A | P ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \bigcup_ ( i  'in'  A  |  P ) '/  '  F ']'").
Reserved Notation "\bigcup_ ( i 'in' A ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \bigcup_ ( i  'in'  A ) '/  '  F ']'").

Reserved Notation "\bigcap_ i F"
  (at level 41, F at level 41, i at level 0,
           format "'[' \bigcap_ i '/  '  F ']'").
Reserved Notation "\bigcap_ ( i <- r | P ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \bigcap_ ( i  <-  r  |  P )  F ']'").
Reserved Notation "\bigcap_ ( i <- r ) F"
  (at level 41, F at level 41, i, r at level 50,
           format "'[' \bigcap_ ( i  <-  r ) '/  '  F ']'").
Reserved Notation "\bigcap_ ( m <= i < n | P ) F"
  (at level 41, F at level 41, m, i, n at level 50,
           format "'[' \bigcap_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\bigcap_ ( m <= i < n ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \bigcap_ ( m  <=  i  <  n ) '/  '  F ']'").
Reserved Notation "\bigcap_ ( i | P ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \bigcap_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\bigcap_ ( i : t | P ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \bigcap_ ( i   :  t   |  P ) '/  '  F ']'").
Reserved Notation "\bigcap_ ( i : t ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \bigcap_ ( i   :  t ) '/  '  F ']'").
Reserved Notation "\bigcap_ ( i < n | P ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \bigcap_ ( i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\bigcap_ ( i < n ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \bigcap_ ( i  <  n ) '/  '  F ']'").
Reserved Notation "\bigcap_ ( i 'in' A | P ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \bigcap_ ( i  'in'  A  |  P ) '/  '  F ']'").
Reserved Notation "\bigcap_ ( i 'in' A ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \bigcap_ ( i  'in'  A ) '/  '  F ']'").

Module SemiGroup.

HB.mixin Record isLaw T (op : T -> T -> T) := {
  opA : associative op;
}.

#[export]
HB.structure Definition Law T := {op of isLaw T op}.
Notation law := Law.type.

HB.mixin Record isCommutativeLaw T (op : T -> T -> T) := {
  opC : commutative op;
}.

#[export]
HB.structure Definition ComLaw T := {op of Law T op & isCommutativeLaw T op}.
Notation com_law := ComLaw.type.

HB.factory Record isComLaw T (op : T -> T -> T) := {
  opA : associative op;
  opC : commutative op;
}.

HB.builders Context T op of isComLaw T op.

HB.instance Definition _ := isLaw.Build T op opA.
HB.instance Definition _ := isCommutativeLaw.Build T op opC.

HB.end.

Module Import Exports.
HB.reexport.
End Exports.

Module Theory.

Section Theory.
Variables (T : Type).

Section Plain.
Variable mul : law T.
Lemma mulmA : associative mul.
Proof.
exact: opA.
Qed.
End Plain.

Section Commutative.
Variable mul : com_law T.
Lemma mulmC : commutative mul.
Proof.
exact: opC.
Qed.
Lemma mulmCA : left_commutative mul.
Proof.
by move=> x y z; rewrite !mulmA [_ x _]mulmC.
Qed.
Lemma mulmAC : right_commutative mul.
Proof.
by move=> x y z; rewrite -!mulmA [_ y _]mulmC.
Qed.
Lemma mulmACA : interchange mul mul.
Proof.
by move=> x y z t; rewrite -!mulmA [_ y _]mulmCA.
Qed.
End Commutative.

End Theory.

End Theory.

Include Theory.

End SemiGroup.
Export SemiGroup.Exports.

Module Monoid.

Export SemiGroup.

HB.mixin Record isMonoidLaw T (idm : T) (op : T -> T -> T) := {
  op1m : left_id idm op;
  opm1 : right_id idm op;
}.

#[export]
HB.structure Definition Law T idm :=
  {op of SemiGroup.Law T op & isMonoidLaw T idm op}.
Notation law := Law.type.

HB.factory Record isLaw T (idm : T) (op : T -> T -> T) := {
  opA : associative op;
  op1m : left_id idm op;
  opm1 : right_id idm op;
}.

HB.builders Context T idm op of isLaw T idm op.

HB.instance Definition _ := SemiGroup.isLaw.Build T op opA.
HB.instance Definition _ := isMonoidLaw.Build T idm op op1m opm1.

HB.end.

#[export]
HB.structure Definition ComLaw T idm :=
  {op of Law T idm op & isCommutativeLaw T op}.
Notation com_law := ComLaw.type.

HB.factory Record isComLaw T (idm : T) (op : T -> T -> T) := {
  opA : associative op;
  opC : commutative op;
  op1m : left_id idm op;
}.

HB.builders Context T idm op of isComLaw T idm op.

Lemma opm1 : right_id idm op.
Proof.
by move=> x; rewrite opC op1m.
Qed.

HB.instance Definition _ := isLaw.Build T idm op opA op1m opm1.
HB.instance Definition _ := isCommutativeLaw.Build T op opC.

HB.end.

HB.mixin Record isMulLaw T (zero : T) (mul : T -> T -> T) := {
  mul_zerol : left_zero zero mul;
  mul_zeror : right_zero zero mul;
}.

#[export]
HB.structure Definition MulLaw T zero := {mul of isMulLaw T zero mul}.
Notation mul_law := MulLaw.type.

HB.mixin Record isAddLaw T (mul : T -> T -> T) (op : T -> T -> T) := {
  mul_op_Dl : left_distributive mul op;
  mul_op_Dr : right_distributive mul op;
}.

#[export]
HB.structure Definition AddLaw T zero mul :=
  {add of ComLaw T zero add & isAddLaw T mul add}.
Notation add_law := AddLaw.type.

Module Import Exports.
HB.reexport.
End Exports.

Section CommutativeAxioms.

Variable (T : Type) (zero one : T) (mul add : T -> T -> T).
Hypothesis mulC : commutative mul.

Lemma mulC_id : left_id one mul -> right_id one mul.
Proof.
by move=> mul1x x; rewrite mulC.
Qed.

Lemma mulC_zero : left_zero zero mul -> right_zero zero mul.
Proof.
by move=> mul0x x; rewrite mulC.
Qed.

Lemma mulC_dist : left_distributive mul add -> right_distributive mul add.
Proof.
by move=> mul_addl x y z; rewrite !(mulC x).
Qed.

End CommutativeAxioms.

Module Theory.

Export SemiGroup.Theory.

Section Theory.
Variables (T : Type) (idm : T).

Section Plain.
Variable mul : law idm.
Lemma mul1m : left_id idm mul.
Proof.
exact: op1m.
Qed.
Lemma mulm1 : right_id idm mul.
Proof.
exact: opm1.
Qed.
Lemma iteropE n x : iterop n mul x idm = iter n (mul x) idm.
Proof.
by case: n => // n; rewrite iterSr mulm1 iteropS.
Qed.
End Plain.

Section Mul.
Variable mul : mul_law idm.
Lemma mul0m : left_zero idm mul.
Proof.
exact: mul_zerol.
Qed.
Lemma mulm0 : right_zero idm mul.
Proof.
exact: mul_zeror.
Qed.
End Mul.

Section Add.
Variables (mul : T -> T -> T) (add : add_law idm mul).
Lemma addmA : associative add.
Proof.
exact: mulmA.
Qed.
Lemma addmC : commutative add.
Proof.
exact: mulmC.
Qed.
Lemma addmCA : left_commutative add.
Proof.
exact: mulmCA.
Qed.
Lemma addmAC : right_commutative add.
Proof.
exact: mulmAC.
Qed.
Lemma add0m : left_id idm add.
Proof.
exact: mul1m.
Qed.
Lemma addm0 : right_id idm add.
Proof.
exact: mulm1.
Qed.
Lemma mulmDl : left_distributive mul add.
Proof.
exact: mul_op_Dl.
Qed.
Lemma mulmDr : right_distributive mul add.
Proof.
exact: mul_op_Dr.
Qed.
End Add.

Definition simpm := (mulm1, mulm0, mul1m, mul0m, mulmA).

End Theory.

End Theory.
Include SemiGroup.Theory.
Include Theory.

End Monoid.
Export Monoid.Exports.

Section PervasiveMonoids.

Import Monoid.

HB.instance Definition _ := isComLaw.Build bool true andb andbA andbC andTb.

HB.instance Definition _ := isMulLaw.Build bool false andb andFb andbF.
HB.instance Definition _ := isComLaw.Build bool false orb orbA orbC orFb.
HB.instance Definition _ := isMulLaw.Build bool true orb orTb orbT.
HB.instance Definition _ := isComLaw.Build bool false addb addbA addbC addFb.
HB.instance Definition _ := isAddLaw.Build bool andb orb andb_orl andb_orr.
HB.instance Definition _ := isAddLaw.Build bool orb andb orb_andl orb_andr.
HB.instance Definition _ := isAddLaw.Build bool andb addb andb_addl andb_addr.

HB.instance Definition _ := isComLaw.Build nat 0 addn addnA addnC add0n.
HB.instance Definition _ := isComLaw.Build nat 1 muln mulnA mulnC mul1n.
HB.instance Definition _ := isMulLaw.Build nat 0 muln mul0n muln0.
HB.instance Definition _ := isAddLaw.Build nat muln addn mulnDl mulnDr.

HB.instance Definition _ := isComLaw.Build nat 0 maxn maxnA maxnC max0n.
HB.instance Definition _ := isAddLaw.Build nat muln maxn maxnMl maxnMr.

HB.instance Definition _ := isComLaw.Build nat 0 gcdn gcdnA gcdnC gcd0n.
HB.instance Definition _ := isAddLaw.Build nat muln gcdn muln_gcdl muln_gcdr.

HB.instance Definition _ := isComLaw.Build nat 1 lcmn lcmnA lcmnC lcm1n.
HB.instance Definition _ := isAddLaw.Build nat muln lcmn muln_lcml muln_lcmr.

HB.instance Definition _ T := isLaw.Build (seq T) nil cat
  (@catA T) (@cat0s T) (@cats0 T).

End PervasiveMonoids.

 

Delimit Scope big_scope with BIG.
Open Scope big_scope.

 
 
 
 
 
 
Variant bigbody R I := BigBody of I & (R -> R -> R) & bool & R.

Definition applybig {R I} (body : bigbody R I) x :=
  let: BigBody _ op b v := body in if b then op v x else x.

Definition reducebig R I idx r (body : I -> bigbody R I) :=
  foldr (applybig \o body) idx r.

HB.lock Definition bigop := reducebig.
Canonical bigop_unlock := Unlockable bigop.unlock.

Definition index_iota m n := iota m (n - m).

Lemma mem_index_iota m n i : i \in index_iota m n = (m <= i < n).
Proof.
rewrite mem_iota; case le_m_i: (m <= i) => //=.
by rewrite -leq_subLR subSn // -subn_gt0 -subnDA subnKC // subn_gt0.
Qed.

 
 
 
 
 
 
 
 
 
 
Fact index_enum_key : unit.
Proof.
split.
Defined.
 
Definition index_enum (T : finType) :=
  locked_with index_enum_key (Finite.enum T).

Lemma deprecated_filter_index_enum T P : filter P (index_enum T) = enum P.
Proof.
by rewrite [index_enum T]unlock.
Qed.

Lemma mem_index_enum T i : i \in index_enum T.
Proof.
by rewrite [index_enum T]unlock -enumT mem_enum.
Qed.
#[global] Hint Resolve mem_index_enum : core.

Lemma index_enum_uniq T : uniq (index_enum T).
Proof.
by rewrite [index_enum T]unlock -enumT enum_uniq.
Qed.

Notation "\big [ op / idx ]_ ( i <- r | P ) F" :=
  (bigop idx r (fun i => BigBody i op P%B F)) : big_scope.
Notation "\big [ op / idx ]_ ( i <- r ) F" :=
  (bigop idx r (fun i => BigBody i op true F)) : big_scope.
Notation "\big [ op / idx ]_ ( m <= i < n | P ) F" :=
  (bigop idx (index_iota m n) (fun i : nat => BigBody i op P%B F))
     : big_scope.
Notation "\big [ op / idx ]_ ( m <= i < n ) F" :=
  (bigop idx (index_iota m n) (fun i : nat => BigBody i op true F))
     : big_scope.
Notation "\big [ op / idx ]_ ( i | P ) F" :=
  (bigop idx (index_enum _) (fun i => BigBody i op P%B F)) : big_scope.
Notation "\big [ op / idx ]_ i F" :=
  (bigop idx (index_enum _) (fun i => BigBody i op true F)) : big_scope.
Notation "\big [ op / idx ]_ ( i : t | P ) F" :=
  (bigop idx (index_enum _) (fun i : t => BigBody i op P%B F))
     (only parsing) : big_scope.
Notation "\big [ op / idx ]_ ( i : t ) F" :=
  (bigop idx (index_enum _) (fun i : t => BigBody i op true F))
     (only parsing) : big_scope.
Notation "\big [ op / idx ]_ ( i < n | P ) F" :=
  (\big[op/idx]_(i : ordinal n | P%B) F) : big_scope.
Notation "\big [ op / idx ]_ ( i < n ) F" :=
  (\big[op/idx]_(i : ordinal n) F) : big_scope.
Notation "\big [ op / idx ]_ ( i 'in' A | P ) F" :=
  (\big[op/idx]_(i | (i \in A) && P) F) : big_scope.
Notation "\big [ op / idx ]_ ( i 'in' A ) F" :=
  (\big[op/idx]_(i | i \in A) F) : big_scope.

Notation BIG_F := (F in \big[_/_]_(i <- _ | _) F i)%pattern.
Notation BIG_P := (P in \big[_/_]_(i <- _ | P i) _)%pattern.

Local Notation "+%N" := addn (at level 0, only parsing).
Notation "\sum_ ( i <- r | P ) F" :=
  (\big[+%N/0%N]_(i <- r | P%B) F%N) : nat_scope.
Notation "\sum_ ( i <- r ) F" :=
  (\big[+%N/0%N]_(i <- r) F%N) : nat_scope.
Notation "\sum_ ( m <= i < n | P ) F" :=
  (\big[+%N/0%N]_(m <= i < n | P%B) F%N) : nat_scope.
Notation "\sum_ ( m <= i < n ) F" :=
  (\big[+%N/0%N]_(m <= i < n) F%N) : nat_scope.
Notation "\sum_ ( i | P ) F" :=
  (\big[+%N/0%N]_(i | P%B) F%N) : nat_scope.
Notation "\sum_ i F" :=
  (\big[+%N/0%N]_i F%N) : nat_scope.
Notation "\sum_ ( i : t | P ) F" :=
  (\big[+%N/0%N]_(i : t | P%B) F%N) (only parsing) : nat_scope.
Notation "\sum_ ( i : t ) F" :=
  (\big[+%N/0%N]_(i : t) F%N) (only parsing) : nat_scope.
Notation "\sum_ ( i < n | P ) F" :=
  (\big[+%N/0%N]_(i < n | P%B) F%N) : nat_scope.
Notation "\sum_ ( i < n ) F" :=
  (\big[+%N/0%N]_(i < n) F%N) : nat_scope.
Notation "\sum_ ( i 'in' A | P ) F" :=
  (\big[+%N/0%N]_(i in A | P%B) F%N) : nat_scope.
Notation "\sum_ ( i 'in' A ) F" :=
  (\big[+%N/0%N]_(i in A) F%N) : nat_scope.

Local Notation "*%N" := muln (at level 0, only parsing).
Notation "\prod_ ( i <- r | P ) F" :=
  (\big[*%N/1%N]_(i <- r | P%B) F%N) : nat_scope.
Notation "\prod_ ( i <- r ) F" :=
  (\big[*%N/1%N]_(i <- r) F%N) : nat_scope.
Notation "\prod_ ( m <= i < n | P ) F" :=
  (\big[*%N/1%N]_(m <= i < n | P%B) F%N) : nat_scope.
Notation "\prod_ ( m <= i < n ) F" :=
  (\big[*%N/1%N]_(m <= i < n) F%N) : nat_scope.
Notation "\prod_ ( i | P ) F" :=
  (\big[*%N/1%N]_(i | P%B) F%N) : nat_scope.
Notation "\prod_ i F" :=
  (\big[*%N/1%N]_i F%N) : nat_scope.
Notation "\prod_ ( i : t | P ) F" :=
  (\big[*%N/1%N]_(i : t | P%B) F%N) (only parsing) : nat_scope.
Notation "\prod_ ( i : t ) F" :=
  (\big[*%N/1%N]_(i : t) F%N) (only parsing) : nat_scope.
Notation "\prod_ ( i < n | P ) F" :=
  (\big[*%N/1%N]_(i < n | P%B) F%N) : nat_scope.
Notation "\prod_ ( i < n ) F" :=
  (\big[*%N/1%N]_(i < n) F%N) : nat_scope.
Notation "\prod_ ( i 'in' A | P ) F" :=
  (\big[*%N/1%N]_(i in A | P%B) F%N) : nat_scope.
Notation "\prod_ ( i 'in' A ) F" :=
  (\big[*%N/1%N]_(i in A) F%N) : nat_scope.

Notation "\max_ ( i <- r | P ) F" :=
  (\big[maxn/0%N]_(i <- r | P%B) F%N) : nat_scope.
Notation "\max_ ( i <- r ) F" :=
  (\big[maxn/0%N]_(i <- r) F%N) : nat_scope.
Notation "\max_ ( i | P ) F" :=
  (\big[maxn/0%N]_(i | P%B) F%N) : nat_scope.
Notation "\max_ i F" :=
  (\big[maxn/0%N]_i F%N) : nat_scope.
Notation "\max_ ( i : I | P ) F" :=
  (\big[maxn/0%N]_(i : I | P%B) F%N) (only parsing) : nat_scope.
Notation "\max_ ( i : I ) F" :=
  (\big[maxn/0%N]_(i : I) F%N) (only parsing) : nat_scope.
Notation "\max_ ( m <= i < n | P ) F" :=
 (\big[maxn/0%N]_(m <= i < n | P%B) F%N) : nat_scope.
Notation "\max_ ( m <= i < n ) F" :=
 (\big[maxn/0%N]_(m <= i < n) F%N) : nat_scope.
Notation "\max_ ( i < n | P ) F" :=
 (\big[maxn/0%N]_(i < n | P%B) F%N) : nat_scope.
Notation "\max_ ( i < n ) F" :=
 (\big[maxn/0%N]_(i < n) F%N) : nat_scope.
Notation "\max_ ( i 'in' A | P ) F" :=
 (\big[maxn/0%N]_(i in A | P%B) F%N) : nat_scope.
Notation "\max_ ( i 'in' A ) F" :=
 (\big[maxn/0%N]_(i in A) F%N) : nat_scope.

 
Lemma big_load R (K K' : R -> Type) idx op I r (P : pred I) F :
  K (\big[op/idx]_(i <- r | P i) F i) * K' (\big[op/idx]_(i <- r | P i) F i)
  -> K' (\big[op/idx]_(i <- r | P i) F i).
Proof.
by case.
Qed.

Arguments big_load [R] K [K'] idx op [I].

Section Elim3.

Variables (R1 R2 R3 : Type) (K : R1 -> R2 -> R3 -> Type).
Variables (id1 : R1) (op1 : R1 -> R1 -> R1).
Variables (id2 : R2) (op2 : R2 -> R2 -> R2).
Variables (id3 : R3) (op3 : R3 -> R3 -> R3).

Hypothesis Kid : K id1 id2 id3.

Lemma big_rec3 I r (P : pred I) F1 F2 F3
    (K_F : forall i y1 y2 y3, P i -> K y1 y2 y3 ->
       K (op1 (F1 i) y1) (op2 (F2 i) y2) (op3 (F3 i) y3)) :
  K (\big[op1/id1]_(i <- r | P i) F1 i)
    (\big[op2/id2]_(i <- r | P i) F2 i)
    (\big[op3/id3]_(i <- r | P i) F3 i).
Proof.
by rewrite unlock; elim: r => //= i r; case: ifP => //; apply: K_F.
Qed.

Hypothesis Kop : forall x1 x2 x3 y1 y2 y3,
  K x1 x2 x3 -> K y1 y2 y3-> K (op1 x1 y1) (op2 x2 y2) (op3 x3 y3).
Lemma big_ind3 I r (P : pred I) F1 F2 F3
   (K_F : forall i, P i -> K (F1 i) (F2 i) (F3 i)) :
  K (\big[op1/id1]_(i <- r | P i) F1 i)
    (\big[op2/id2]_(i <- r | P i) F2 i)
    (\big[op3/id3]_(i <- r | P i) F3 i).
Proof.
by apply: big_rec3 => i x1 x2 x3 /K_F; apply: Kop.
Qed.

End Elim3.

Arguments big_rec3 [R1 R2 R3] K [id1 op1 id2 op2 id3 op3] _ [I r P F1 F2 F3].
Arguments big_ind3 [R1 R2 R3] K [id1 op1 id2 op2 id3 op3] _ _ [I r P F1 F2 F3].

Section Elim2.

Variables (R1 R2 : Type) (K : R1 -> R2 -> Type) (f : R2 -> R1).
Variables (id1 : R1) (op1 : R1 -> R1 -> R1).
Variables (id2 : R2) (op2 : R2 -> R2 -> R2).

Hypothesis Kid : K id1 id2.

Lemma big_rec2 I r (P : pred I) F1 F2
    (K_F : forall i y1 y2, P i -> K y1 y2 ->
       K (op1 (F1 i) y1) (op2 (F2 i) y2)) :
  K (\big[op1/id1]_(i <- r | P i) F1 i) (\big[op2/id2]_(i <- r | P i) F2 i).
Proof.
by rewrite unlock; elim: r => //= i r; case: ifP => //; apply: K_F.
Qed.

Hypothesis Kop : forall x1 x2 y1 y2,
  K x1 x2 -> K y1 y2 -> K (op1 x1 y1) (op2 x2 y2).
Lemma big_ind2 I r (P : pred I) F1 F2 (K_F : forall i, P i -> K (F1 i) (F2 i)) :
  K (\big[op1/id1]_(i <- r | P i) F1 i) (\big[op2/id2]_(i <- r | P i) F2 i).
Proof.
by apply: big_rec2 => i x1 x2 /K_F; apply: Kop.
Qed.

Hypotheses (f_op : {morph f : x y / op2 x y >-> op1 x y}) (f_id : f id2 = id1).
Lemma big_morph I r (P : pred I) F :
  f (\big[op2/id2]_(i <- r | P i) F i) = \big[op1/id1]_(i <- r | P i) f (F i).
Proof.
by rewrite unlock; elim: r => //= i r <-; rewrite -f_op -fun_if.
Qed.

End Elim2.

Arguments big_rec2 [R1 R2] K [id1 op1 id2 op2] _ [I r P F1 F2].
Arguments big_ind2 [R1 R2] K [id1 op1 id2 op2] _ _ [I r P F1 F2].
Arguments big_morph [R1 R2] f [id1 op1 id2 op2] _ _ [I].

Section Elim1.

Variables (R : Type) (K : R -> Type) (f : R -> R).
Variables (idx : R) (op op' : R -> R -> R).

Hypothesis Kid : K idx.

Lemma big_rec I r (P : pred I) F
    (Kop : forall i x, P i -> K x -> K (op (F i) x)) :
  K (\big[op/idx]_(i <- r | P i) F i).
Proof.
by rewrite unlock; elim: r => //= i r; case: ifP => //; apply: Kop.
Qed.

Hypothesis Kop : forall x y, K x -> K y -> K (op x y).
Lemma big_ind I r (P : pred I) F (K_F : forall i, P i -> K (F i)) :
  K (\big[op/idx]_(i <- r | P i) F i).
Proof.
by apply: big_rec => // i x /K_F /Kop; apply.
Qed.

Hypothesis Kop' : forall x y, K x -> K y -> op x y = op' x y.
Lemma eq_big_op I r (P : pred I) F (K_F : forall i, P i -> K (F i)) :
  \big[op/idx]_(i <- r | P i) F i = \big[op'/idx]_(i <- r | P i) F i.
Proof.
by elim/(big_load K): _; elim/big_rec2: _ => // i _ y Pi [Ky <-]; auto.
Qed.

Hypotheses (fM : {morph f : x y / op x y}) (f_id : f idx = idx).
Lemma big_endo I r (P : pred I) F :
  f (\big[op/idx]_(i <- r | P i) F i) = \big[op/idx]_(i <- r | P i) f (F i).
Proof.
exact: big_morph.
Qed.

End Elim1.

Arguments big_rec [R] K [idx op] _ [I r P F].
Arguments big_ind [R] K [idx op] _ _ [I r P F].
Arguments eq_big_op [R] K [idx op] op' _ _ _ [I].
Arguments big_endo [R] f [idx op] _ _ [I].

Section oAC.

Variables (T : Type) (op : T -> T -> T).

Definition AC_subdef of associative op & commutative op :=
  fun x => oapp (fun y => Some (oapp (op^~ y) y x)) x.
Definition oAC := nosimpl AC_subdef.

Hypothesis (opA : associative op) (opC : commutative op).

Local Notation oop := (oAC opA opC).

Lemma oACE x y : oop (Some x) (Some y) = some (op x y).
Proof.
by [].
Qed.

Lemma oopA_subdef : associative oop.
Proof.
by move=> [x|] [y|] [z|]//; rewrite /oAC/= opA.
Qed.

Lemma oopx1_subdef : left_id None oop.
Proof.
by case.
Qed.
Lemma oop1x_subdef : right_id None oop.
Proof.
by [].
Qed.

Lemma oopC_subdef : commutative oop.
Proof.
by move=> [x|] [y|]//; rewrite /oAC/= opC.
Qed.

HB.instance Definition _ := Monoid.isComLaw.Build (option T) None oop
  oopA_subdef oopC_subdef oopx1_subdef.

Context [x : T].

Lemma some_big_AC_mk_monoid [I : Type] r P (F : I -> T) :
  Some (\big[op/x]_(i <- r | P i) F i) =
    oop (\big[oop/None]_(i <- r | P i) Some (F i)) (Some x).
Proof.
by elim/big_rec2 : _ => //= i [y|] _ Pi [] -> //=; rewrite opA.
Qed.

Lemma big_AC_mk_monoid [I : Type] r P (F : I -> T) :
  \big[op/x]_(i <- r | P i) F i =
    odflt x (oop (\big[oop/None]_(i <- r | P i) Some (F i)) (Some x)).
Proof.
by apply: Some_inj; rewrite some_big_AC_mk_monoid.
Qed.

End oAC.

Section Extensionality.

Variables (R : Type) (idx : R) (op : R -> R -> R).

Section SeqExtension.

Variable I : Type.

Lemma foldrE r : foldr op idx r = \big[op/idx]_(x <- r) x.
Proof.
by rewrite unlock.
Qed.

Lemma big_filter r (P : pred I) F :
  \big[op/idx]_(i <- filter P r) F i = \big[op/idx]_(i <- r | P i) F i.
Proof.
by rewrite unlock; elim: r => //= i r <-; case (P i).
Qed.

Lemma big_filter_cond r (P1 P2 : pred I) F :
  \big[op/idx]_(i <- filter P1 r | P2 i) F i
     = \big[op/idx]_(i <- r | P1 i && P2 i) F i.
Proof.
rewrite -big_filter -(big_filter r); congr bigop.
by rewrite -filter_predI; apply: eq_filter => i; apply: andbC.
Qed.

Lemma eq_bigl r (P1 P2 : pred I) F :
    P1 =1 P2 ->
  \big[op/idx]_(i <- r | P1 i) F i = \big[op/idx]_(i <- r | P2 i) F i.
Proof.
by move=> eqP12; rewrite -!(big_filter r) (eq_filter eqP12).
Qed.

 
Lemma big_andbC r (P Q : pred I) F :
  \big[op/idx]_(i <- r | P i && Q i) F i
    = \big[op/idx]_(i <- r | Q i && P i) F i.
Proof.
by apply: eq_bigl => i; apply: andbC.
Qed.

Lemma eq_bigr r (P : pred I) F1 F2 : (forall i, P i -> F1 i = F2 i) ->
  \big[op/idx]_(i <- r | P i) F1 i = \big[op/idx]_(i <- r | P i) F2 i.
Proof.
by move=> eqF12; elim/big_rec2: _ => // i x _ /eqF12-> ->.
Qed.

Lemma eq_big r (P1 P2 : pred I) F1 F2 :
    P1 =1 P2 -> (forall i, P1 i -> F1 i = F2 i) ->
  \big[op/idx]_(i <- r | P1 i) F1 i = \big[op/idx]_(i <- r | P2 i) F2 i.
Proof.
by move/eq_bigl <-; move/eq_bigr->.
Qed.

Lemma congr_big r1 r2 (P1 P2 : pred I) F1 F2 :
    r1 = r2 -> P1 =1 P2 -> (forall i, P1 i -> F1 i = F2 i) ->
  \big[op/idx]_(i <- r1 | P1 i) F1 i = \big[op/idx]_(i <- r2 | P2 i) F2 i.
Proof.
by move=> <-{r2}; apply: eq_big.
Qed.

Lemma big_nil (P : pred I) F : \big[op/idx]_(i <- [::] | P i) F i = idx.
Proof.
by rewrite unlock.
Qed.

Lemma big_cons i r (P : pred I) F :
    let x := \big[op/idx]_(j <- r | P j) F j in
  \big[op/idx]_(j <- i :: r | P j) F j = if P i then op (F i) x else x.
Proof.
by rewrite unlock.
Qed.

Lemma big_map J (h : J -> I) r (P : pred I) F :
  \big[op/idx]_(i <- map h r | P i) F i
     = \big[op/idx]_(j <- r | P (h j)) F (h j).
Proof.
by rewrite unlock; elim: r => //= j r ->.
Qed.

Lemma big_nth x0 r (P : pred I) F :
  \big[op/idx]_(i <- r | P i) F i
     = \big[op/idx]_(0 <= i < size r | P (nth x0 r i)) (F (nth x0 r i)).
Proof.
by rewrite -[r in LHS](mkseq_nth x0) big_map /index_iota subn0.
Qed.

Lemma big_hasC r (P : pred I) F :
  ~~ has P r -> \big[op/idx]_(i <- r | P i) F i = idx.
Proof.
by rewrite -big_filter has_count -size_filter -eqn0Ngt unlock => /nilP->.
Qed.

Lemma big_pred0_eq (r : seq I) F : \big[op/idx]_(i <- r | false) F i = idx.
Proof.
by rewrite big_hasC // has_pred0.
Qed.

Lemma big_pred0 r (P : pred I) F :
  P =1 xpred0 -> \big[op/idx]_(i <- r | P i) F i = idx.
Proof.
by move/eq_bigl->; apply: big_pred0_eq.
Qed.

Lemma big_cat_nested r1 r2 (P : pred I) F :
    let x := \big[op/idx]_(i <- r2 | P i) F i in
  \big[op/idx]_(i <- r1 ++ r2 | P i) F i = \big[op/x]_(i <- r1 | P i) F i.
Proof.
by rewrite unlock /reducebig foldr_cat.
Qed.

Lemma big_catl r1 r2 (P : pred I) F :
    ~~ has P r2 ->
  \big[op/idx]_(i <- r1 ++ r2 | P i) F i = \big[op/idx]_(i <- r1 | P i) F i.
Proof.
by rewrite big_cat_nested => /big_hasC->.
Qed.

Lemma big_catr r1 r2 (P : pred I) F :
     ~~ has P r1 ->
  \big[op/idx]_(i <- r1 ++ r2 | P i) F i = \big[op/idx]_(i <- r2 | P i) F i.
Proof.
rewrite -big_filter -(big_filter r2) filter_cat.
by rewrite has_count -size_filter; case: filter.
Qed.

End SeqExtension.

Lemma big_map_id J (h : J -> R) r (P : pred R) :
  \big[op/idx]_(i <- map h r | P i) i
     = \big[op/idx]_(j <- r | P (h j)) h j.
Proof.
exact: big_map.
Qed.

Lemma big_condT (J : finType) (A : {pred J}) F :
  \big[op/idx]_(i in A | true) F i = \big[op/idx]_(i in A) F i.
Proof.
by apply: eq_bigl => i; exact: andbT.
Qed.

 
 
 
Lemma big_seq_cond (I : eqType) r (P : pred I) F :
  \big[op/idx]_(i <- r | P i) F i
    = \big[op/idx]_(i <- r | (i \in r) && P i) F i.
Proof.
by rewrite -!(big_filter r); congr bigop; apply: eq_in_filter => i ->.
Qed.

Lemma big_seq (I : eqType) (r : seq I) F :
  \big[op/idx]_(i <- r) F i = \big[op/idx]_(i <- r | i \in r) F i.
Proof.
by rewrite big_seq_cond big_andbC.
Qed.

Lemma eq_big_seq (I : eqType) (r : seq I) F1 F2 :
  {in r, F1 =1 F2} -> \big[op/idx]_(i <- r) F1 i = \big[op/idx]_(i <- r) F2 i.
Proof.
by move=> eqF; rewrite !big_seq (eq_bigr _ eqF).
Qed.

 
Lemma big_nat_cond m n (P : pred nat) F :
  \big[op/idx]_(m <= i < n | P i) F i
    = \big[op/idx]_(m <= i < n | (m <= i < n) && P i) F i.
Proof.
by rewrite big_seq_cond; apply: eq_bigl => i; rewrite mem_index_iota.
Qed.

Lemma big_nat m n F :
  \big[op/idx]_(m <= i < n) F i = \big[op/idx]_(m <= i < n | m <= i < n) F i.
Proof.
by rewrite big_nat_cond big_andbC.
Qed.

Lemma congr_big_nat m1 n1 m2 n2 P1 P2 F1 F2 :
    m1 = m2 -> n1 = n2 ->
    (forall i, m1 <= i < n2 -> P1 i = P2 i) ->
    (forall i, P1 i && (m1 <= i < n2) -> F1 i = F2 i) ->
  \big[op/idx]_(m1 <= i < n1 | P1 i) F1 i
    = \big[op/idx]_(m2 <= i < n2 | P2 i) F2 i.
Proof.
move=> <- <- eqP12 eqF12; rewrite big_seq_cond (big_seq_cond _ P2).
apply: eq_big => i; rewrite ?inE /= !mem_index_iota.
  by apply: andb_id2l; apply: eqP12.
by rewrite andbC; apply: eqF12.
Qed.

Lemma eq_big_nat m n F1 F2 :
    (forall i, m <= i < n -> F1 i = F2 i) ->
  \big[op/idx]_(m <= i < n) F1 i = \big[op/idx]_(m <= i < n) F2 i.
Proof.
by move=> eqF; apply: congr_big_nat.
Qed.

Lemma big_geq m n (P : pred nat) F :
  m >= n -> \big[op/idx]_(m <= i < n | P i) F i = idx.
Proof.
by move=> ge_m_n; rewrite /index_iota (eqnP ge_m_n) big_nil.
Qed.

Lemma big_ltn_cond m n (P : pred nat) F :
    m < n -> let x := \big[op/idx]_(m.+1 <= i < n | P i) F i in
  \big[op/idx]_(m <= i < n | P i) F i = if P m then op (F m) x else x.
Proof.
by case: n => [//|n] le_m_n; rewrite /index_iota subSn // big_cons.
Qed.

Lemma big_ltn m n F :
     m < n ->
  \big[op/idx]_(m <= i < n) F i = op (F m) (\big[op/idx]_(m.+1 <= i < n) F i).
Proof.
by move=> lt_mn; apply: big_ltn_cond.
Qed.

Lemma big_addn m n a (P : pred nat) F :
  \big[op/idx]_(m + a <= i < n | P i) F i =
     \big[op/idx]_(m <= i < n - a | P (i + a)) F (i + a).
Proof.
rewrite /index_iota -subnDA addnC iotaDl big_map.
by apply: eq_big => ? *; rewrite addnC.
Qed.

Lemma big_add1 m n (P : pred nat) F :
  \big[op/idx]_(m.+1 <= i < n | P i) F i =
     \big[op/idx]_(m <= i < n.-1 | P (i.+1)) F (i.+1).
Proof.
by rewrite -addn1 big_addn subn1; apply: eq_big => ? *; rewrite addn1.
Qed.

Lemma big_nat_recl n m F : m <= n ->
  \big[op/idx]_(m <= i < n.+1) F i =
     op (F m) (\big[op/idx]_(m <= i < n) F i.+1).
Proof.
by move=> lemn; rewrite big_ltn // big_add1.
Qed.

Lemma big_mkord n (P : pred nat) F :
  \big[op/idx]_(0 <= i < n | P i) F i = \big[op/idx]_(i < n | P i) F i.
Proof.
rewrite /index_iota subn0 -(big_map (@nat_of_ord n)).
by congr bigop; rewrite /index_enum 2!unlock val_ord_enum.
Qed.

Lemma big_nat_widen m n1 n2 (P : pred nat) F :
     n1 <= n2 ->
  \big[op/idx]_(m <= i < n1 | P i) F i
      = \big[op/idx]_(m <= i < n2 | P i && (i < n1)) F i.
Proof.
move=> len12; symmetry; rewrite -big_filter filter_predI big_filter.
have [ltn_trans eq_by_mem] := (ltn_trans, irr_sorted_eq ltn_trans ltnn).
congr bigop; apply: eq_by_mem; rewrite ?sorted_filter ?iota_ltn_sorted // => i.
rewrite mem_filter !mem_index_iota andbCA andbA andb_idr => // /andP[_].
by move/leq_trans->.
Qed.

Lemma big_ord_widen_cond n1 n2 (P : pred nat) (F : nat -> R) :
     n1 <= n2 ->
  \big[op/idx]_(i < n1 | P i) F i
      = \big[op/idx]_(i < n2 | P i && (i < n1)) F i.
Proof.
by move/big_nat_widen=> len12; rewrite -big_mkord len12 big_mkord.
Qed.

Lemma big_ord_widen n1 n2 (F : nat -> R) :
    n1 <= n2 ->
  \big[op/idx]_(i < n1) F i = \big[op/idx]_(i < n2 | i < n1) F i.
Proof.
by move=> le_n12; apply: (big_ord_widen_cond (predT)).
Qed.

Lemma big_ord_widen_leq n1 n2 (P : pred 'I_(n1.+1)) F :
    n1 < n2 ->
  \big[op/idx]_(i < n1.+1 | P i) F i
      = \big[op/idx]_(i < n2 | P (inord i) && (i <= n1)) F (inord i).
Proof.
move=> len12; pose g G i := G (inord i : 'I_(n1.+1)).
rewrite -(big_ord_widen_cond (g _ P) (g _ F) len12) {}/g.
by apply: eq_big => i *; rewrite inord_val.
Qed.

Lemma big_ord0 P F : \big[op/idx]_(i < 0 | P i) F i = idx.
Proof.
by rewrite big_pred0 => [|[]].
Qed.

Lemma big_mask_tuple I n m (t : n.-tuple I) (P : pred I) F :
  \big[op/idx]_(i <- mask m t | P i) F i
    = \big[op/idx]_(i < n | nth false m i && P (tnth t i)) F (tnth t i).
Proof.
rewrite [t in LHS]tuple_map_ord/= -map_mask big_map.
by rewrite mask_enum_ord big_filter_cond/= enumT.
Qed.

Lemma big_mask I r m (P : pred I) (F : I -> R) (r_ := tnth (in_tuple r)) :
  \big[op/idx]_(i <- mask m r | P i) F i
    = \big[op/idx]_(i < size r | nth false m i && P (r_ i)) F (r_ i).
Proof.
exact: (big_mask_tuple _ (in_tuple r)).
Qed.

Lemma big_tnth I r (P : pred I) F (r_ := tnth (in_tuple r)) :
  \big[op/idx]_(i <- r | P i) F i
    = \big[op/idx]_(i < size r | P (r_ i)) (F (r_ i)).
Admitted.

Lemma big_index_uniq (I : eqType) (r : seq I) (E : 'I_(size r) -> R) :
    uniq r ->
  \big[op/idx]_i E i = \big[op/idx]_(x <- r) oapp E idx (insub (index x r)).
Admitted.

Lemma big_tuple I n (t : n.-tuple I) (P : pred I) F :
  \big[op/idx]_(i <- t | P i) F i
     = \big[op/idx]_(i < n | P (tnth t i)) F (tnth t i).
Admitted.

Lemma big_ord_narrow_cond n1 n2 (P : pred 'I_n2) F (le_n12 : n1 <= n2) :
    let w := widen_ord le_n12 in
  \big[op/idx]_(i < n2 | P i && (i < n1)) F i
    = \big[op/idx]_(i < n1 | P (w i)) F (w i).
Admitted.

Lemma big_ord_narrow_cond_leq n1 n2 (P : pred _) F (le_n12 : n1 <= n2) :
    let w := @widen_ord n1.+1 n2.+1 le_n12 in
  \big[op/idx]_(i < n2.+1 | P i && (i <= n1)) F i
  = \big[op/idx]_(i < n1.+1 | P (w i)) F (w i).
Admitted.

Lemma big_ord_narrow n1 n2 F (le_n12 : n1 <= n2) :
    let w := widen_ord le_n12 in
  \big[op/idx]_(i < n2 | i < n1) F i = \big[op/idx]_(i < n1) F (w i).
Admitted.

Lemma big_ord_narrow_leq n1 n2 F (le_n12 : n1 <= n2) :
    let w := @widen_ord n1.+1 n2.+1 le_n12 in
  \big[op/idx]_(i < n2.+1 | i <= n1) F i = \big[op/idx]_(i < n1.+1) F (w i).
Admitted.

Lemma big_ord_recl n F :
  \big[op/idx]_(i < n.+1) F i =
     op (F ord0) (\big[op/idx]_(i < n) F (@lift n.+1 ord0 i)).
Admitted.

Lemma big_nseq_cond I n a (P : pred I) F :
  \big[op/idx]_(i <- nseq n a | P i) F i
    = if P a then iter n (op (F a)) idx else idx.
Admitted.

Lemma big_nseq I n a (F : I -> R):
  \big[op/idx]_(i <- nseq n a) F i = iter n (op (F a)) idx.
Admitted.

End Extensionality.

Variant big_enum_spec (I : finType) (P : pred I) : seq I -> Type :=
  BigEnumSpec e of
    forall R idx op (F : I -> R),
      \big[op/idx]_(i <- e) F i = \big[op/idx]_(i | P i) F i
  & uniq e /\ (forall i, i \in e = P i)
  & (let cP := [pred i | P i] in perm_eq e (enum cP) /\ size e = #|cP|)
  : big_enum_spec P e.

 
 
 
 
 
 
 
 
 
 
 
 
 
 

Lemma big_enumP I P : big_enum_spec P (filter P (index_enum I)).
Admitted.

Section BigConst.

Variables (R : Type) (idx : R) (op : R -> R -> R).

Lemma big_const_seq I r (P : pred I) x :
  \big[op/idx]_(i <- r | P i) x = iter (count P r) (op x) idx.
Admitted.

Lemma big_const (I : finType) (A : {pred I}) x :
  \big[op/idx]_(i in A) x = iter #|A| (op x) idx.
Admitted.

Lemma big_const_nat m n x :
  \big[op/idx]_(m <= i < n) x = iter (n - m) (op x) idx.
Admitted.

Lemma big_const_ord n x :
  \big[op/idx]_(i < n) x = iter n (op x) idx.
Admitted.

End BigConst.

Section Plain.

Variable R : Type.
Variable op : R -> R -> R.
Variable x : R.

Lemma big_seq1_id I (i : I) (F : I -> R) :
  \big[op/x]_(j <- [:: i]) F j = op (F i) x.
Admitted.

Lemma big_nat1_id n F : \big[op/x]_(n <= i < n.+1) F i = op (F n) x.
Admitted.

Lemma big_pred1_eq_id (I : finType) (i : I) F :
  \big[op/x]_(j | j == i) F j = op (F i) x.
Admitted.

Lemma big_pred1_id (I : finType) i (P : pred I) F :
  P =1 pred1 i -> \big[op/x]_(j | P j) F j = op (F i) x.
Admitted.

End Plain.

Section SemiGroupProperties.

Variable R : Type.

#[local] Notation opA := SemiGroup.opA.
#[local] Notation opC := SemiGroup.opC.

Section Id.

Variable op : SemiGroup.law R.

Variable x : R.
Hypothesis opxx : op x x = x.

Lemma big_const_idem I (r : seq I) P : \big[op/x]_(i <- r | P i) x = x.
Admitted.

Lemma big1_idem I r (P : pred I) F :
  (forall i, P i -> F i = x) -> \big[op/x]_(i <- r | P i) F i = x.
Admitted.

Lemma big_id_idem I (r : seq I) P F :
  op (\big[op/x]_(i <- r | P i) F i) x = \big[op/x]_(i <- r | P i) F i.
Admitted.

End Id.

Section Abelian.

Variable op : SemiGroup.com_law R.

Let opCA : left_commutative op.
Admitted.

Variable x : R.

Lemma big_rem_AC (I : eqType) (r : seq I) z (P : pred I) F : z \in r ->
  \big[op/x]_(y <- r | P y) F y
    = if P z then op (F z) (\big[op/x]_(y <- rem z r | P y) F y)
      else \big[op/x]_(y <- rem z r | P y) F y.
Admitted.

Lemma big_undup (I : eqType) (r : seq I) (P : pred I) F :
    idempotent op ->
  \big[op/x]_(i <- undup r | P i) F i = \big[op/x]_(i <- r | P i) F i.
Admitted.

Lemma perm_big (I : eqType) r1 r2 (P : pred I) F :
    perm_eq r1 r2 ->
  \big[op/x]_(i <- r1 | P i) F i = \big[op/x]_(i <- r2 | P i) F i.
Admitted.

Lemma big_enum_cond (I : finType) (A : {pred I}) (P : pred I) F :
  \big[op/x]_(i <- enum A | P i) F i = \big[op/x]_(i in A | P i) F i.
Admitted.

Lemma big_enum (I : finType) (A : {pred I}) F :
  \big[op/x]_(i <- enum A) F i = \big[op/x]_(i in A) F i.
Admitted.

Lemma big_uniq (I : finType) (r : seq I) F :
  uniq r -> \big[op/x]_(i <- r) F i = \big[op/x]_(i in r) F i.
Admitted.

Lemma bigD1 (I : finType) j (P : pred I) F :
  P j -> \big[op/x]_(i | P i) F i
    = op (F j) (\big[op/x]_(i | P i && (i != j)) F i).
Admitted.
Arguments bigD1 [I] j [P F].

Lemma bigD1_seq (I : eqType) (r : seq I) j F :
    j \in r -> uniq r ->
  \big[op/x]_(i <- r) F i = op (F j) (\big[op/x]_(i <- r | i != j) F i).
Admitted.

Lemma big_image_cond I (J : finType) (h : J -> I) (A : pred J) (P : pred I) F :
  \big[op/x]_(i <- [seq h j | j in A] | P i) F i
     = \big[op/x]_(j in A | P (h j)) F (h j).
Admitted.

Lemma big_image I (J : finType) (h : J -> I) (A : pred J) F :
  \big[op/x]_(i <- [seq h j | j in A]) F i = \big[op/x]_(j in A) F (h j).
Admitted.

Lemma cardD1x (I : finType) (A : pred I) j :
  A j -> #|SimplPred A| = 1 + #|[pred i | A i & i != j]|.
Admitted.
Arguments cardD1x [I A].

Lemma reindex_omap (I J : finType) (h : J -> I) h' (P : pred I) F :
    (forall i, P i -> omap h (h' i) = some i) ->
  \big[op/x]_(i | P i) F i =
    \big[op/x]_(j | P (h j) && (h' (h j) == some j)) F (h j).
Admitted.
Arguments reindex_omap [I J] h h' [P F].

Lemma reindex_onto (I J : finType) (h : J -> I) h' (P : pred I) F :
    (forall i, P i -> h (h' i) = i) ->
  \big[op/x]_(i | P i) F i =
    \big[op/x]_(j | P (h j) && (h' (h j) == j)) F (h j).
Admitted.
Arguments reindex_onto [I J] h h' [P F].

Lemma reindex (I J : finType) (h : J -> I) (P : pred I) F :
    {on [pred i | P i], bijective h} ->
  \big[op/x]_(i | P i) F i = \big[op/x]_(j | P (h j)) F (h j).
Admitted.
Arguments reindex [I J] h [P F].

Lemma reindex_inj (I : finType) (h : I -> I) (P : pred I) F :
  injective h -> \big[op/x]_(i | P i) F i = \big[op/x]_(j | P (h j)) F (h j).
Admitted.
Arguments reindex_inj [I h P F].

Lemma bigD1_ord n j (P : pred 'I_n) F :
  P j -> \big[op/x]_(i < n | P i) F i
    = op (F j) (\big[op/x]_(i < n.-1 | P (lift j i)) F (lift j i)).
Admitted.

Lemma big_enum_val_cond (I : finType) (A : pred I) (P : pred I) F :
  \big[op/x]_(x in A | P x) F x =
  \big[op/x]_(i < #|A| | P (enum_val i)) F (enum_val i).
Admitted.
Arguments big_enum_val_cond [I A] P F.

Lemma big_enum_rank_cond (I : finType) (A : pred I) z (zA : z \in A) P F
  (h := enum_rank_in zA) :
  \big[op/x]_(i < #|A| | P i) F i = \big[op/x]_(s in A | P (h s)) F (h s).
Admitted.
Arguments big_enum_rank_cond [I A z] zA P F.

Lemma big_nat_rev m n P F :
  \big[op/x]_(m <= i < n | P i) F i
     = \big[op/x]_(m <= i < n | P (m + n - i.+1)) F (m + n - i.+1).
Admitted.

Lemma big_rev_mkord m n P F :
 \big[op/x]_(m <= k < n | P k) F k
    = \big[op/x]_(k < n - m | P (n - k.+1)) F (n - k.+1).
Admitted.

Section Id.

Hypothesis opxx : op x x = x.

Lemma big_mkcond_idem I r (P : pred I) F :
  \big[op/x]_(i <- r | P i) F i = \big[op/x]_(i <- r) (if P i then F i else x).
Admitted.

Lemma big_mkcondr_idem I r (P Q : pred I) F :
  \big[op/x]_(i <- r | P i && Q i) F i =
    \big[op/x]_(i <- r | P i) (if Q i then F i else x).
Admitted.

Lemma big_mkcondl_idem I r (P Q : pred I) F :
  \big[op/x]_(i <- r | P i && Q i) F i =
    \big[op/x]_(i <- r | Q i) (if P i then F i else x).
Admitted.

Lemma big_rmcond_idem I (r : seq I) (P : pred I) F :
  (forall i, ~~ P i -> F i = x) ->
  \big[op/x]_(i <- r | P i) F i = \big[op/x]_(i <- r) F i.
Admitted.

Lemma big_rmcond_in_idem (I : eqType) (r : seq I) (P : pred I) F :
  (forall i, i \in r -> ~~ P i -> F i = x) ->
  \big[op/x]_(i <- r | P i) F i = \big[op/x]_(i <- r) F i.
Admitted.

Lemma big_cat_idem I r1 r2 (P : pred I) F :
  \big[op/x]_(i <- r1 ++ r2 | P i) F i =
    op (\big[op/x]_(i <- r1 | P i) F i) (\big[op/x]_(i <- r2 | P i) F i).
Admitted.

Lemma big_allpairs_dep_idem I1 (I2 : I1 -> Type) J (h : forall i1, I2 i1 -> J)
    (r1 : seq I1) (r2 : forall i1, seq (I2 i1)) (F : J -> R) :
  \big[op/x]_(i <- [seq h i1 i2 | i1 <- r1, i2 <- r2 i1]) F i =
    \big[op/x]_(i1 <- r1) \big[op/x]_(i2 <- r2 i1) F (h i1 i2).
Admitted.

Lemma big_allpairs_idem I1 I2 (r1 : seq I1) (r2 : seq I2) F :
  \big[op/x]_(i <- [seq (i1, i2) | i1 <- r1, i2 <- r2]) F i =
    \big[op/x]_(i1 <- r1) \big[op/x]_(i2 <- r2) F (i1, i2).
Admitted.

Lemma big_cat_nat_idem n m p (P : pred nat) F : m <= n -> n <= p ->
  \big[op/x]_(m <= i < p | P i) F i =
    op (\big[op/x]_(m <= i < n | P i) F i) (\big[op/x]_(n <= i < p | P i) F i).
Admitted.

Lemma big_split_idem I r (P : pred I) F1 F2 :
  \big[op/x]_(i <- r | P i) op (F1 i) (F2 i) =
    op (\big[op/x]_(i <- r | P i) F1 i) (\big[op/x]_(i <- r | P i) F2 i).
Admitted.

Lemma big_id_idem_AC I (r : seq I) P F :
  \big[op/x]_(i <- r | P i) op (F i) x = \big[op/x]_(i <- r | P i) F i.
Admitted.

Lemma bigID_idem I r (a P : pred I) F :
  \big[op/x]_(i <- r | P i) F i =
    op (\big[op/x]_(i <- r | P i && a i) F i)
       (\big[op/x]_(i <- r | P i && ~~ a i) F i).
Admitted.
Arguments bigID_idem [I r].

Lemma bigU_idem (I : finType) (A B : pred I) F :
    [disjoint A & B] ->
  \big[op/x]_(i in [predU A & B]) F i =
    op (\big[op/x]_(i in A) F i) (\big[op/x]_(i in B) F i).
Admitted.

Lemma partition_big_idem I (s : seq I)
      (J : finType) (P : pred I) (p : I -> J) (Q : pred J) F :
  (forall i, P i -> Q (p i)) ->
  \big[op/x]_(i <- s | P i) F i =
  \big[op/x]_(j : J | Q j) \big[op/x]_(i <- s | (P i) && (p i == j)) F i.
Admitted.

Arguments partition_big_idem [I s J P] p Q [F].

Lemma sig_big_dep_idem (I : finType) (J : I -> finType)
    (P : pred I) (Q : forall {i}, pred (J i)) (F : forall {i}, J i -> R) :
  \big[op/x]_(i | P i) \big[op/x]_(j : J i | Q j) F j =
  \big[op/x]_(p : {i : I & J i} | P (tag p) && Q (tagged p)) F (tagged p).
Admitted.

Lemma pair_big_dep_idem (I J : finType) (P : pred I) (Q : I -> pred J) F :
  \big[op/x]_(i | P i) \big[op/x]_(j | Q i j) F i j =
    \big[op/x]_(p | P p.1 && Q p.1 p.2) F p.1 p.2.
Admitted.

Lemma pair_big_idem (I J : finType) (P : pred I) (Q : pred J) F :
  \big[op/x]_(i | P i) \big[op/x]_(j | Q j) F i j =
    \big[op/x]_(p | P p.1 && Q p.2) F p.1 p.2.
Admitted.

Lemma pair_bigA_idem (I J : finType) (F : I -> J -> R) :
  \big[op/x]_i \big[op/x]_j F i j = \big[op/x]_p F p.1 p.2.
Admitted.

Lemma exchange_big_dep_idem I J rI rJ (P : pred I) (Q : I -> pred J)
                       (xQ : pred J) F :
    (forall i j, P i -> Q i j -> xQ j) ->
  \big[op/x]_(i <- rI | P i) \big[op/x]_(j <- rJ | Q i j) F i j =
    \big[op/x]_(j <- rJ | xQ j) \big[op/x]_(i <- rI | P i && Q i j) F i j.
Admitted.
Arguments exchange_big_dep_idem [I J rI rJ P Q] xQ [F].

Lemma exchange_big_idem I J rI rJ (P : pred I) (Q : pred J) F :
  \big[op/x]_(i <- rI | P i) \big[op/x]_(j <- rJ | Q j) F i j =
    \big[op/x]_(j <- rJ | Q j) \big[op/x]_(i <- rI | P i) F i j.
Admitted.

Lemma exchange_big_dep_nat_idem m1 n1 m2 n2 (P : pred nat) (Q : rel nat)
                           (xQ : pred nat) F :
    (forall i j, m1 <= i < n1 -> m2 <= j < n2 -> P i -> Q i j -> xQ j) ->
  \big[op/x]_(m1 <= i < n1 | P i) \big[op/x]_(m2 <= j < n2 | Q i j) F i j =
    \big[op/x]_(m2 <= j < n2 | xQ j)
       \big[op/x]_(m1 <= i < n1 | P i && Q i j) F i j.
Admitted.
Arguments exchange_big_dep_nat_idem [m1 n1 m2 n2 P Q] xQ [F].

Lemma exchange_big_nat_idem m1 n1 m2 n2 (P Q : pred nat) F :
  \big[op/x]_(m1 <= i < n1 | P i) \big[op/x]_(m2 <= j < n2 | Q j) F i j =
    \big[op/x]_(m2 <= j < n2 | Q j) \big[op/x]_(m1 <= i < n1 | P i) F i j.
Admitted.

End Id.

End Abelian.

End SemiGroupProperties.
Arguments big_undup [R op x I].
Arguments perm_big [R op x I r1 r2].
Arguments bigD1 [R op x I] j [P F].
Arguments reindex_omap [R op x I J] h h' [P F].
Arguments reindex_onto [R op x I J] h h' [P F].
Arguments reindex [R op x I J] h [P F].
Arguments reindex_inj [R op x I h P F].
Arguments big_enum_val_cond [R op x I A] P F.
Arguments big_enum_rank_cond [R op x I A z] zA P F.

Section MonoidProperties.

Import Monoid.Theory.

Variable R : Type.

Variable idx : R.
Local Notation "1" := idx.

Section Plain.

Variable op : Monoid.law 1.

Local Notation "*%M" := op (at level 0).
Local Notation "x * y" := (op x y).

Lemma foldlE x r : foldl *%M x r = \big[*%M/1]_(y <- x :: r) y.
Admitted.

Lemma foldl_idx r : foldl *%M 1 r = \big[*%M/1]_(x <- r) x.
Admitted.

Lemma eq_big_idx_seq idx' I r (P : pred I) F :
     right_id idx' *%M -> has P r ->
   \big[*%M/idx']_(i <- r | P i) F i = \big[*%M/1]_(i <- r | P i) F i.
Admitted.

Lemma eq_big_idx idx' (I : finType) i0 (P : pred I) F :
     P i0 -> right_id idx' *%M ->
  \big[*%M/idx']_(i | P i) F i = \big[*%M/1]_(i | P i) F i.
Admitted.

Lemma big1_eq I r (P : pred I) : \big[*%M/1]_(i <- r | P i) 1 = 1.
Admitted.

Lemma big1 I r (P : pred I) F :
  (forall i, P i -> F i = 1) -> \big[*%M/1]_(i <- r | P i) F i = 1.
Admitted.

Lemma big1_seq (I : eqType) r (P : pred I) F :
    (forall i, P i && (i \in r) -> F i = 1) ->
  \big[*%M/1]_(i <- r | P i) F i = 1.
Admitted.

Lemma big_seq1 I (i : I) F : \big[*%M/1]_(j <- [:: i]) F j = F i.
Admitted.

Lemma big_mkcond I r (P : pred I) F :
  \big[*%M/1]_(i <- r | P i) F i =
     \big[*%M/1]_(i <- r) (if P i then F i else 1).
Admitted.

Lemma big_mkcondr I r (P Q : pred I) F :
  \big[*%M/1]_(i <- r | P i && Q i) F i =
     \big[*%M/1]_(i <- r | P i) (if Q i then F i else 1).
Admitted.

Lemma big_mkcondl I r (P Q : pred I) F :
  \big[*%M/1]_(i <- r | P i && Q i) F i =
     \big[*%M/1]_(i <- r | Q i) (if P i then F i else 1).
Admitted.

Lemma big_rmcond I (r : seq I) (P : pred I) F :
  (forall i, ~~ P i -> F i = 1) ->
  \big[*%M/1]_(i <- r | P i) F i = \big[*%M/1]_(i <- r) F i.
Admitted.

Lemma big_rmcond_in (I : eqType) (r : seq I) (P : pred I) F :
  (forall i, i \in r -> ~~ P i -> F i = 1) ->
  \big[*%M/1]_(i <- r | P i) F i = \big[*%M/1]_(i <- r) F i.
Admitted.

Lemma big_cat I r1 r2 (P : pred I) F :
  \big[*%M/1]_(i <- r1 ++ r2 | P i) F i =
     \big[*%M/1]_(i <- r1 | P i) F i * \big[*%M/1]_(i <- r2 | P i) F i.
Admitted.

Lemma big_allpairs_dep I1 (I2 : I1 -> Type) J (h : forall i1, I2 i1 -> J)
    (r1 : seq I1) (r2 : forall i1, seq (I2 i1)) (F : J -> R) :
  \big[*%M/1]_(i <- [seq h i1 i2 | i1 <- r1, i2 <- r2 i1]) F i =
    \big[*%M/1]_(i1 <- r1) \big[*%M/1]_(i2 <- r2 i1) F (h i1 i2).
Admitted.

Lemma big_allpairs I1 I2 (r1 : seq I1) (r2 : seq I2) F :
  \big[*%M/1]_(i <- [seq (i1, i2) | i1 <- r1, i2 <- r2]) F i =
    \big[*%M/1]_(i1 <- r1) \big[op/idx]_(i2 <- r2) F (i1, i2).
Admitted.

Lemma big_pred1_eq (I : finType) (i : I) F :
  \big[*%M/1]_(j | j == i) F j = F i.
Admitted.

Lemma big_pred1 (I : finType) i (P : pred I) F :
  P =1 pred1 i -> \big[*%M/1]_(j | P j) F j = F i.
Admitted.

Lemma big_ord1_eq (F : nat -> R) i n :
  \big[op/idx]_(j < n | j == i :> nat) F j = if i < n then F i else idx.
Admitted.

Lemma big_ord1_cond_eq (F : nat -> R) (P : pred nat) i n :
  \big[op/idx]_(j < n | P j && (j == i :> nat)) F j =
    if (i < n) && P i then F i else idx.
Admitted.

Lemma big_cat_nat n m p (P : pred nat) F : m <= n -> n <= p ->
  \big[*%M/1]_(m <= i < p | P i) F i =
   (\big[*%M/1]_(m <= i < n | P i) F i) * (\big[*%M/1]_(n <= i < p | P i) F i).
Admitted.

Lemma big_nat_widenl (m1 m2 n : nat) (P : pred nat) F :
  m2 <= m1 ->
  \big[op/idx]_(m1 <= i < n | P i) F i =
  \big[op/idx]_(m2 <= i < n | P i && (m1 <= i)) F i.
Admitted.

Lemma big_geq_mkord (m n : nat) (P : pred nat) F :
  \big[op/idx]_(m <= i < n | P i) F i =
  \big[op/idx]_(i < n | P i && (m <= i)) F i.
Admitted.

Lemma big_nat1_eq (F : nat -> R) i m n :
  \big[op/idx]_(m <= j < n | j == i) F j = if m <= i < n then F i else idx.
Admitted.

Lemma big_nat1_cond_eq (F : nat -> R) (P : pred nat) i m n :
  \big[op/idx]_(m <= j < n | P j && (j == i)) F j =
    if (m <= i < n) && P i then F i else idx.
Admitted.

Lemma big_nat1 n F : \big[*%M/1]_(n <= i < n.+1) F i = F n.
Admitted.

Lemma big_nat_recr n m F : m <= n ->
  \big[*%M/1]_(m <= i < n.+1) F i = (\big[*%M/1]_(m <= i < n) F i) * F n.
Admitted.

Lemma big_nat_mul n k F :
  \big[*%M/1]_(0 <= i < n * k) F i =
  \big[*%M/1]_(0 <= i < n) \big[*%M/1]_(i * k <= j < i.+1 * k) F j.
Admitted.

Lemma big_ord_recr n F :
  \big[*%M/1]_(i < n.+1) F i =
     (\big[*%M/1]_(i < n) F (widen_ord (leqnSn n) i)) * F ord_max.
Admitted.

Lemma big_sumType (I1 I2 : finType) (P : pred (I1 + I2)) F :
  \big[*%M/1]_(i | P i) F i =
        (\big[*%M/1]_(i | P (inl _ i)) F (inl _ i))
      * (\big[*%M/1]_(i | P (inr _ i)) F (inr _ i)).
Admitted.

Lemma big_split_ord m n (P : pred 'I_(m + n)) F :
  \big[*%M/1]_(i | P i) F i =
        (\big[*%M/1]_(i | P (lshift n i)) F (lshift n i))
      * (\big[*%M/1]_(i | P (rshift m i)) F (rshift m i)).
Admitted.

Lemma big_flatten I rr (P : pred I) F :
  \big[*%M/1]_(i <- flatten rr | P i) F i
    = \big[*%M/1]_(r <- rr) \big[*%M/1]_(i <- r | P i) F i.
Admitted.

Lemma big_pmap J I (h : J -> option I) (r : seq J) F :
  \big[op/idx]_(i <- pmap h r) F i = \big[op/idx]_(j <- r) oapp F idx (h j).
Admitted.

Lemma telescope_big (f : nat -> nat -> R) (n m : nat) :
  (forall k, n < k < m -> op (f n k) (f k k.+1) = f n k.+1) ->
  \big[op/idx]_(n <= i < m) f i i.+1 = if n < m then f n m else idx.
Admitted.

End Plain.

Section Abelian.

Variable op : Monoid.com_law 1.

Local Notation "'*%M'" := op (at level 0).
Local Notation "x * y" := (op x y).

Lemma big_rem (I : eqType) r x (P : pred I) F :
    x \in r ->
  \big[*%M/1]_(y <- r | P y) F y
    = (if P x then F x else 1) * \big[*%M/1]_(y <- rem x r | P y) F y.
Admitted.

Lemma eq_big_idem (I : eqType) (r1 r2 : seq I) (P : pred I) F :
    idempotent *%M -> r1 =i r2 ->
  \big[*%M/1]_(i <- r1 | P i) F i = \big[*%M/1]_(i <- r2 | P i) F i.
Admitted.

Lemma big_undup_iterop_count (I : eqType) (r : seq I) (P : pred I) F :
  \big[*%M/1]_(i <- undup r | P i) iterop (count_mem i r) *%M (F i) 1
    = \big[*%M/1]_(i <- r | P i) F i.
Admitted.

Lemma big_split I r (P : pred I) F1 F2 :
  \big[*%M/1]_(i <- r | P i) (F1 i * F2 i) =
    \big[*%M/1]_(i <- r | P i) F1 i * \big[*%M/1]_(i <- r | P i) F2 i.
Admitted.

Lemma bigID I r (a P : pred I) F :
  \big[*%M/1]_(i <- r | P i) F i =
    \big[*%M/1]_(i <- r | P i && a i) F i *
    \big[*%M/1]_(i <- r | P i && ~~ a i) F i.
Admitted.
Arguments bigID [I r].

Lemma big_if I r (P Q : pred I) F G :
  \big[*%M/1]_(i <- r | P i) (if Q i then F i else G i) =
    \big[*%M/1]_(i <- r | P i && Q i) F i *
    \big[*%M/1]_(i <- r | P i && ~~ Q i) G i.
Admitted.

Lemma bigU (I : finType) (A B : pred I) F :
    [disjoint A & B] ->
  \big[*%M/1]_(i in [predU A & B]) F i =
    (\big[*%M/1]_(i in A) F i) * (\big[*%M/1]_(i in B) F i).
Admitted.

Lemma partition_big I (s : seq I)
      (J : finType) (P : pred I) (p : I -> J) (Q : pred J) F :
  (forall i, P i -> Q (p i)) ->
  \big[*%M/1]_(i <- s | P i) F i =
  \big[*%M/1]_(j : J | Q j) \big[*%M/1]_(i <- s | (P i) && (p i == j)) F i.
Admitted.

Arguments partition_big [I s J P] p Q [F].

Lemma big_enum_val (I : finType) (A : pred I) F :
  \big[op/idx]_(x in A) F x = \big[op/idx]_(i < #|A|) F (enum_val i).
Admitted.
Arguments big_enum_val [I A] F.

Lemma big_enum_rank (I : finType) (A : pred I) x (xA : x \in A) F
  (h := enum_rank_in xA) :
  \big[op/idx]_(i < #|A|) F i = \big[op/idx]_(s in A) F (h s).
Admitted.
Arguments big_enum_rank [I A x] xA F.

Lemma sig_big_dep (I : finType) (J : I -> finType)
    (P : pred I) (Q : forall {i}, pred (J i)) (F : forall {i}, J i -> R) :
  \big[op/idx]_(i | P i) \big[op/idx]_(j : J i | Q j) F j =
  \big[op/idx]_(p : {i : I & J i} | P (tag p) && Q (tagged p)) F (tagged p).
Admitted.

Lemma pair_big_dep (I J : finType) (P : pred I) (Q : I -> pred J) F :
  \big[*%M/1]_(i | P i) \big[*%M/1]_(j | Q i j) F i j =
    \big[*%M/1]_(p | P p.1 && Q p.1 p.2) F p.1 p.2.
Admitted.

Lemma pair_big (I J : finType) (P : pred I) (Q : pred J) F :
  \big[*%M/1]_(i | P i) \big[*%M/1]_(j | Q j) F i j =
    \big[*%M/1]_(p | P p.1 && Q p.2) F p.1 p.2.
Admitted.

Lemma pair_bigA (I J : finType) (F : I -> J -> R) :
  \big[*%M/1]_i \big[*%M/1]_j F i j = \big[*%M/1]_p F p.1 p.2.
Admitted.

Lemma exchange_big_dep I J rI rJ (P : pred I) (Q : I -> pred J)
                       (xQ : pred J) F :
    (forall i j, P i -> Q i j -> xQ j) ->
  \big[*%M/1]_(i <- rI | P i) \big[*%M/1]_(j <- rJ | Q i j) F i j =
    \big[*%M/1]_(j <- rJ | xQ j) \big[*%M/1]_(i <- rI | P i && Q i j) F i j.
Admitted.
Arguments exchange_big_dep [I J rI rJ P Q] xQ [F].

Lemma exchange_big I J rI rJ (P : pred I) (Q : pred J) F :
  \big[*%M/1]_(i <- rI | P i) \big[*%M/1]_(j <- rJ | Q j) F i j =
    \big[*%M/1]_(j <- rJ | Q j) \big[*%M/1]_(i <- rI | P i) F i j.
Admitted.

Lemma exchange_big_dep_nat m1 n1 m2 n2 (P : pred nat) (Q : rel nat)
                           (xQ : pred nat) F :
    (forall i j, m1 <= i < n1 -> m2 <= j < n2 -> P i -> Q i j -> xQ j) ->
  \big[*%M/1]_(m1 <= i < n1 | P i) \big[*%M/1]_(m2 <= j < n2 | Q i j) F i j =
    \big[*%M/1]_(m2 <= j < n2 | xQ j)
       \big[*%M/1]_(m1 <= i < n1 | P i && Q i j) F i j.
Admitted.
Arguments exchange_big_dep_nat [m1 n1 m2 n2 P Q] xQ [F].

Lemma exchange_big_nat m1 n1 m2 n2 (P Q : pred nat) F :
  \big[*%M/1]_(m1 <= i < n1 | P i) \big[*%M/1]_(m2 <= j < n2 | Q j) F i j =
    \big[*%M/1]_(m2 <= j < n2 | Q j) \big[*%M/1]_(m1 <= i < n1 | P i) F i j.
Admitted.

End Abelian.

End MonoidProperties.

Arguments big_filter [R idx op I].
Arguments big_filter_cond [R idx op I].
Arguments congr_big [R idx op I r1] r2 [P1] P2 [F1] F2.
Arguments eq_big [R idx op I r P1] P2 [F1] F2.
Arguments eq_bigl [R idx op I r P1] P2.
Arguments eq_bigr [R idx op I r P F1] F2.
Arguments eq_big_idx [R idx op idx' I] i0 [P F].
Arguments big_seq_cond [R idx op I r].
Arguments eq_big_seq [R idx op I r F1] F2.
Arguments congr_big_nat [R idx op m1 n1] m2 n2 [P1] P2 [F1] F2.
Arguments big_map [R idx op I J] h [r].
Arguments big_nth [R idx op I] x0 [r].
Arguments big_catl [R idx op I r1 r2 P F].
Arguments big_catr [R idx op I r1 r2 P F].
Arguments big_geq [R idx op m n P F].
Arguments big_ltn_cond [R idx op m n P F].
Arguments big_ltn [R idx op m n F].
Arguments big_addn [R idx op].
Arguments big_mkord [R idx op n].
Arguments big_nat_widen [R idx op].
Arguments big_nat_widenl [R idx op].
Arguments big_geq_mkord [R idx op].
Arguments big_ord_widen_cond [R idx op n1].
Arguments big_ord_widen [R idx op n1].
Arguments big_ord_widen_leq [R idx op n1].
Arguments big_ord_narrow_cond [R idx op n1 n2 P F].
Arguments big_ord_narrow_cond_leq [R idx op n1 n2 P F].
Arguments big_ord_narrow [R idx op n1 n2 F].
Arguments big_ord_narrow_leq [R idx op n1 n2 F].
Arguments big_mkcond [R idx op I r].
Arguments big1_eq [R idx op I].
Arguments big1_seq [R idx op I].
Arguments big1 [R idx op I].
Arguments big_pred1 [R idx op I] i [P F].
Arguments perm_big [R op x I r1] r2 [P F].
Arguments big_uniq [R op x I] r [F].
Arguments big_rem [R idx op I r] x [P F].
Arguments bigID [R idx op I r].
Arguments bigU [R idx op I].
Arguments bigD1 [R op x I] j [P F].
Arguments bigD1_seq [R op x I r] j [F].
Arguments bigD1_ord [R op x n] j [P F].
Arguments partition_big [R idx op I s J P] p Q [F].
Arguments reindex_omap [R op x I J] h h' [P F].
Arguments reindex_onto [R op x I J] h h' [P F].
Arguments reindex [R op x I J] h [P F].
Arguments reindex_inj [R op x I h P F].
Arguments big_enum_val_cond [R op x I A] P F.
Arguments big_enum_rank_cond [R op x I A z] zA P F.
Arguments big_enum_val [R idx op I A] F.
Arguments big_enum_rank [R idx op I A x] xA F.
Arguments sig_big_dep [R idx op I J].
Arguments pair_big_dep [R idx op I J].
Arguments pair_big [R idx op I J].
Arguments big_allpairs_dep {R idx op I1 I2 J h r1 r2 F}.
Arguments big_allpairs {R idx op I1 I2 r1 r2 F}.
Arguments exchange_big_dep [R idx op I J rI rJ P Q] xQ [F].
Arguments exchange_big_dep_nat [R idx op m1 n1 m2 n2 P Q] xQ [F].
Arguments big_ord_recl [R idx op].
Arguments big_ord_recr [R idx op].
Arguments big_nat_recl [R idx op].
Arguments big_nat_recr [R idx op].
Arguments big_pmap [R idx op J I] h [r].
Arguments telescope_big [R idx op] f [n m].

Section IncreasingSemiGroup.

Variables (R : Type) (op : SemiGroup.com_law R).
Variable le : rel R.
Hypothesis le_refl : reflexive le.
Hypothesis op_incr : forall x y, le x (op x y).
Context [x : R].

Local Notation opA := SemiGroup.opA.
Local Notation opC := SemiGroup.opC.

Lemma sub_le_big I [s] (P P' : {pred I}) (F : I -> R) :
    (forall i, P i -> P' i) ->
  le (\big[op/x]_(i <- s | P i) F i) (\big[op/x]_(i <- s | P' i) F i).
Admitted.

Lemma sub_le_big_seq (I : eqType) s s' P (F : I -> R) :
    (forall i, count_mem i s <= count_mem i s')%N ->
  le (\big[op/x]_(i <- s | P i) F i) (\big[op/x]_(i <- s' | P i) F i).
Admitted.

Lemma sub_le_big_seq_cond (I : eqType) s s' P P' (F : I -> R) :
    (forall i, count_mem i (filter P s) <= count_mem i (filter P' s'))%N ->
  le (\big[op/x]_(i <- s | P i) F i) (\big[op/x]_(i <- s' | P' i) F i).
Admitted.

Lemma uniq_sub_le_big (I : eqType) s s' P (F : I -> R) : uniq s -> uniq s' ->
    {subset s <= s'} ->
  le (\big[op/x]_(i <- s | P i) F i) (\big[op/x]_(i <- s' | P i) F i).
Admitted.

Lemma uniq_sub_le_big_cond (I : eqType) s s' P P' (F : I -> R) :
    uniq (filter P s) -> uniq (filter P' s') ->
    {subset [seq i <- s | P i] <= [seq i <- s' | P' i]} ->
  le (\big[op/x]_(i <- s | P i) F i) (\big[op/x]_(i <- s' | P' i) F i).
Admitted.

Section Id.

Hypothesis opK : idempotent op.

Lemma idem_sub_le_big (I : eqType) s s' P (F : I -> R) :
    {subset s <= s'} ->
  le (\big[op/x]_(i <- s | P i) F i) (\big[op/x]_(i <- s' | P i) F i).
Admitted.

Lemma idem_sub_le_big_cond (I : eqType) s s' P P' (F : I -> R) :
  {subset [seq i <- s | P i] <= [seq i <- s' | P' i]} ->
  le (\big[op/x]_(i <- s | P i) F i) (\big[op/x]_(i <- s' | P' i) F i).
Admitted.

End Id.

Lemma sub_in_le_big [I : eqType] (s : seq I) (P P' : {pred I}) (F : I -> R) :
    {in s, forall i, P i -> P' i} ->
  le (\big[op/x]_(i <- s | P i) F i) (\big[op/x]_(i <- s | P' i) F i).
Admitted.

Lemma le_big_ord n m [P : {pred nat}] [F : nat -> R] : (n <= m)%N ->
  le (\big[op/x]_(i < n | P i) F i) (\big[op/x]_(i < m | P i) F i).
Admitted.

Lemma subset_le_big [I : finType] [A A' P : {pred I}] (F : I -> R) :
    A \subset A' ->
  le (\big[op/x]_(i in A | P i) F i) (\big[op/x]_(i in A' | P i) F i).
Admitted.

Lemma le_big_nat_cond n m n' m' (P P' : {pred nat}) (F : nat -> R) :
    (n' <= n)%N -> (m <= m')%N -> (forall i, (n <= i < m)%N -> P i -> P' i) ->
  le (\big[op/x]_(n <= i < m | P i) F i) (\big[op/x]_(n' <= i < m' | P' i) F i).
Admitted.

Lemma le_big_nat n m n' m' [P] [F : nat -> R] : (n' <= n)%N -> (m <= m')%N ->
  le (\big[op/x]_(n <= i < m | P i) F i) (\big[op/x]_(n' <= i < m' | P i) F i).
Admitted.

Lemma le_big_ord_cond n m (P P' : {pred nat}) (F : nat -> R) :
    (n <= m)%N -> (forall i : 'I_n, P i -> P' i) ->
  le (\big[op/x]_(i < n | P i) F i) (\big[op/x]_(i < m | P' i) F i).
Admitted.

End IncreasingSemiGroup.

Section EqSupport.

Variables (R : eqType) (idx : R).

Section MonoidSupport.

Variables (op : Monoid.law idx) (I : Type).

Lemma eq_bigl_supp (r : seq I) (P1 : pred I) (P2 : pred I) (F : I -> R) :
  {in [pred x | F x != idx], P1 =1 P2} ->
  \big[op/idx]_(i <- r | P1 i) F i = \big[op/idx]_(i <- r | P2 i) F i.
Admitted.

End MonoidSupport.

Section ComoidSupport.

Variables (op : Monoid.com_law idx) (I : eqType).

Lemma perm_big_supp_cond [r s : seq I] [P : pred I] (F : I -> R) :
  perm_eq
    [seq i <- r | P i && (F i != idx)]
    [seq i <- s | P i && (F i != idx)] ->
  \big[op/idx]_(i <- r | P i) F i = \big[op/idx]_(i <- s | P i) F i.
Admitted.

Lemma perm_big_supp [r s : seq I] [P : pred I] (F : I -> R) :
  perm_eq [seq i <- r | F i != idx] [seq i <- s | F i != idx] ->
  \big[op/idx]_(i <- r | P i) F i = \big[op/idx]_(i <- s | P i) F i.
Admitted.

End ComoidSupport.

End EqSupport.

Arguments eq_bigl_supp [R idx op I r P1].
Arguments perm_big_supp_cond [R idx op I r s P].
Arguments perm_big_supp [R idx op I r s P].

Section Distributivity.

Import Monoid.Theory.

Variable R : Type.
Variables zero one : R.
Local Notation "0" := zero.
Local Notation "1" := one.
Variable times : Monoid.mul_law 0.
Local Notation "*%M" := times (at level 0).
Local Notation "x * y" := (times x y).
Variable plus : Monoid.add_law 0 *%M.
Local Notation "+%M" := plus (at level 0).
Local Notation "x + y" := (plus x y).

Lemma big_distrl I r a (P : pred I) F :
  \big[+%M/0]_(i <- r | P i) F i * a = \big[+%M/0]_(i <- r | P i) (F i * a).
Proof.
by rewrite (big_endo ( *%M^~ a)) ?mul0m // => x y; apply: mulmDl.
Qed.

Lemma big_distrr I r a (P : pred I) F :
  a * \big[+%M/0]_(i <- r | P i) F i = \big[+%M/0]_(i <- r | P i) (a * F i).
Proof.
by rewrite big_endo ?mulm0 // => x y; apply: mulmDr.
Qed.

Lemma big_distrlr I J rI rJ (pI : pred I) (pJ : pred J) F G :
  (\big[+%M/0]_(i <- rI | pI i) F i) * (\big[+%M/0]_(j <- rJ | pJ j) G j)
   = \big[+%M/0]_(i <- rI | pI i) \big[+%M/0]_(j <- rJ | pJ j) (F i * G j).
Admitted.

Lemma big_distr_big_dep (I J : finType) j0 (P : pred I) (Q : I -> pred J) F :
  \big[*%M/1]_(i | P i) \big[+%M/0]_(j | Q i j) F i j =
     \big[+%M/0]_(f in pfamily j0 P Q) \big[*%M/1]_(i | P i) F i (f i).
Admitted.

Lemma big_distr_big (I J : finType) j0 (P : pred I) (Q : pred J) F :
  \big[*%M/1]_(i | P i) \big[+%M/0]_(j | Q j) F i j =
     \big[+%M/0]_(f in pffun_on j0 P Q) \big[*%M/1]_(i | P i) F i (f i).
Admitted.

Lemma bigA_distr_big_dep (I J : finType) (Q : I -> pred J) F :
  \big[*%M/1]_i \big[+%M/0]_(j | Q i j) F i j
    = \big[+%M/0]_(f in family Q) \big[*%M/1]_i F i (f i).
Admitted.

Lemma bigA_distr_big (I J : finType) (Q : pred J) (F : I -> J -> R) :
  \big[*%M/1]_i \big[+%M/0]_(j | Q j) F i j
    = \big[+%M/0]_(f in ffun_on Q) \big[*%M/1]_i F i (f i).
Admitted.

Lemma bigA_distr_bigA (I J : finType) F :
  \big[*%M/1]_(i : I) \big[+%M/0]_(j : J) F i j
    = \big[+%M/0]_(f : {ffun I -> J}) \big[*%M/1]_i F i (f i).
Admitted.

End Distributivity.

Arguments big_distrl [R zero times plus I r].
Arguments big_distrr [R zero times plus I r].
Arguments big_distr_big_dep [R zero one times plus I J].
Arguments big_distr_big [R zero one times plus I J].
Arguments bigA_distr_big_dep [R zero one times plus I J].
Arguments bigA_distr_big [R zero one times plus I J].
Arguments bigA_distr_bigA [R zero one times plus I J].

Section BigBool.

Section Seq.

Variables (I : Type) (r : seq I) (P B : pred I).

Lemma big_has : \big[orb/false]_(i <- r) B i = has B r.
Admitted.

Lemma big_all : \big[andb/true]_(i <- r) B i = all B r.
Admitted.

Lemma big_has_cond : \big[orb/false]_(i <- r | P i) B i = has (predI P B) r.
Admitted.

Lemma big_all_cond :
  \big[andb/true]_(i <- r | P i) B i = all [pred i | P i ==> B i] r.
Admitted.

Lemma big_bool R (idx : R) (op : Monoid.com_law idx) (F : bool -> R):
  \big[op/idx]_(i : bool) F i = op (F true) (F false).
Admitted.

End Seq.

Section FinType.

Variables (I : finType) (P B : pred I).

Lemma big_orE : \big[orb/false]_(i | P i) B i = [exists (i | P i), B i].
Admitted.

Lemma big_andE : \big[andb/true]_(i | P i) B i = [forall (i | P i), B i].
Admitted.

End FinType.

End BigBool.

Section NatConst.

Variables (I : finType) (A : pred I).

Lemma sum_nat_const n : \sum_(i in A) n = #|A| * n.
Admitted.

Lemma sum1_card : \sum_(i in A) 1 = #|A|.
Admitted.

Lemma sum1_count J (r : seq J) (a : pred J) : \sum_(j <- r | a j) 1 = count a r.
Admitted.

Lemma sum1_size J (r : seq J) : \sum_(j <- r) 1 = size r.
Admitted.

Lemma prod_nat_const n : \prod_(i in A) n = n ^ #|A|.
Admitted.

Lemma sum_nat_const_nat n1 n2 n : \sum_(n1 <= i < n2) n = (n2 - n1) * n.
Admitted.

Lemma prod_nat_const_nat n1 n2 n : \prod_(n1 <= i < n2) n = n ^ (n2 - n1).
Admitted.

End NatConst.

Lemma telescope_sumn_in n m f : n <= m ->
  {in [pred i | n <= i <= m], {homo f : x y / x <= y}} ->
  \sum_(n <= k < m) (f k.+1 - f k) = f m - f n.
Admitted.

Lemma telescope_sumn n m f : {homo f : x y / x <= y} ->
  \sum_(n <= k < m) (f k.+1 - f k) = f m - f n.
Admitted.

Lemma sumnE r : sumn r = \sum_(i <- r) i.
Admitted.

Lemma card_bseq n (T : finType) : #|{bseq n of T}| = \sum_(i < n.+1) #|T| ^ i.
Admitted.

Lemma leqif_sum (I : finType) (P C : pred I) (E1 E2 : I -> nat) :
    (forall i, P i -> E1 i <= E2 i ?= iff C i) ->
  \sum_(i | P i) E1 i <= \sum_(i | P i) E2 i ?= iff [forall (i | P i), C i].
Admitted.

Lemma leq_sum I r (P : pred I) (E1 E2 : I -> nat) :
    (forall i, P i -> E1 i <= E2 i) ->
  \sum_(i <- r | P i) E1 i <= \sum_(i <- r | P i) E2 i.
Admitted.

Lemma sumnB I r (P : pred I) (E1 E2 : I -> nat) :
     (forall i, P i -> E1 i <= E2 i) ->
  \sum_(i <- r | P i) (E2 i - E1 i) =
  \sum_(i <- r | P i) E2 i - \sum_(i <- r | P i) E1 i.
Admitted.

Lemma sum_nat_eq0 (I : finType) (P : pred I) (E : I -> nat) :
  (\sum_(i | P i) E i == 0)%N = [forall (i | P i), E i == 0%N].
Admitted.

Lemma sum_nat_seq_eq0 I r (P : pred I) F :
  (\sum_(i <- r | P i) F i == 0)%N = all (fun i => P i ==> (F i == 0%N)) r.
Admitted.

Lemma sum_nat_seq_neq0 I r (P : pred I) F :
  (\sum_(i <- r | P i) F i != 0)%N = has (fun i => P i && (F i != 0)%N) r.
Admitted.

Lemma sum_nat_eq1 (I : finType) (P : pred I) (F : I -> nat) :
  reflect
    (exists i : I, [/\ P i, F i = 1 & forall j, j != i -> P j -> F j = 0]%N)
    (\sum_(i | P i) F i == 1)%N.
Admitted.

Lemma sum_nat_seq_eq1 (I : eqType) r (P : pred I) (F : I -> nat) :
    (\sum_(i <- r | P i) F i = 1)%N ->
  exists i, [/\ i \in r, P i, F i = 1
            & forall j, j != i -> j \in r -> P j -> F j = 0]%N.
Admitted.

Lemma prod_nat_seq_eq0 I r (P : pred I) F :
  (\prod_(i <- r | P i) F i == 0)%N = has (fun i => P i && (F i == 0%N)) r.
Admitted.

Lemma prod_nat_seq_neq0 I r (P : pred I) F :
  (\prod_(i <- r | P i) F i != 0)%N = all (fun i => P i ==> (F i != 0%N)) r.
Admitted.

Lemma prod_nat_seq_eq1 I r (P : pred I) F :
  (\prod_(i <- r | P i) F i == 1)%N = all (fun i => P i ==> (F i == 1%N)) r.
Admitted.

Lemma prod_nat_seq_neq1 I r (P : pred I) F :
  (\prod_(i <- r | P i) F i != 1)%N = has (fun i => P i && (F i != 1%N)) r.
Admitted.

Lemma leq_prod I r (P : pred I) (E1 E2 : I -> nat) :
    (forall i, P i -> E1 i <= E2 i) ->
  \prod_(i <- r | P i) E1 i <= \prod_(i <- r | P i) E2 i.
Admitted.

Lemma prodn_cond_gt0 I r (P : pred I) F :
  (forall i, P i -> 0 < F i) -> 0 < \prod_(i <- r | P i) F i.
Admitted.

Lemma prodn_gt0 I r (P : pred I) F :
  (forall i, 0 < F i) -> 0 < \prod_(i <- r | P i) F i.
Admitted.

Lemma leq_bigmax_seq (I : eqType) r (P : pred I) F i0 :
  i0 \in r -> P i0 -> F i0 <= \max_(i <- r | P i) F i.
Admitted.
Arguments leq_bigmax_seq [I r P F].

Lemma leq_bigmax_cond (I : finType) (P : pred I) F i0 :
  P i0 -> F i0 <= \max_(i | P i) F i.
Admitted.
Arguments leq_bigmax_cond [I P F].

Lemma leq_bigmax (I : finType) F (i0 : I) : F i0 <= \max_i F i.
Admitted.
Arguments leq_bigmax [I F].

Lemma bigmax_leqP (I : finType) (P : pred I) m F :
  reflect (forall i, P i -> F i <= m) (\max_(i | P i) F i <= m).
Admitted.

Lemma bigmax_leqP_seq (I : eqType) r (P : pred I) m F :
  reflect (forall i, i \in r -> P i -> F i <= m) (\max_(i <- r | P i) F i <= m).
Admitted.

Lemma bigmax_sup (I : finType) i0 (P : pred I) m F :
  P i0 -> m <= F i0 -> m <= \max_(i | P i) F i.
Admitted.
Arguments bigmax_sup [I] i0 [P m F].

Lemma bigmax_sup_seq (I : eqType) r i0 (P : pred I) m F :
  i0 \in r -> P i0 -> m <= F i0 -> m <= \max_(i <- r | P i) F i.
Admitted.
Arguments bigmax_sup_seq [I r] i0 [P m F].

Lemma bigmax_eq_arg (I : finType) i0 (P : pred I) F :
  P i0 -> \max_(i | P i) F i = F [arg max_(i > i0 | P i) F i].
Admitted.
Arguments bigmax_eq_arg [I] i0 [P F].

Lemma eq_bigmax_cond (I : finType) (A : pred I) F :
  #|A| > 0 -> {i0 | i0 \in A & \max_(i in A) F i = F i0}.
Admitted.

Lemma eq_bigmax (I : finType) F : #|I| > 0 -> {i0 : I | \max_i F i = F i0}.
Admitted.

Lemma expn_sum m I r (P : pred I) F :
  (m ^ (\sum_(i <- r | P i) F i) = \prod_(i <- r | P i) m ^ F i)%N.
Admitted.

Lemma dvdn_biglcmP (I : finType) (P : pred I) F m :
  reflect (forall i, P i -> F i %| m) (\big[lcmn/1%N]_(i | P i) F i %| m).
Admitted.

Lemma biglcmn_sup (I : finType) i0 (P : pred I) F m :
  P i0 -> m %| F i0 -> m %| \big[lcmn/1%N]_(i | P i) F i.
Admitted.
Arguments biglcmn_sup [I] i0 [P F m].

Lemma dvdn_biggcdP (I : finType) (P : pred I) F m :
  reflect (forall i, P i -> m %| F i) (m %| \big[gcdn/0]_(i | P i) F i).
Admitted.

Lemma biggcdn_inf (I : finType) i0 (P : pred I) F m :
  P i0 -> F i0 %| m -> \big[gcdn/0]_(i | P i) F i %| m.
Admitted.
Arguments biggcdn_inf [I] i0 [P F m].

End bigop.

End mathcomp_DOT_ssreflect_DOT_bigop_WRAPPED.
Module Export mathcomp_DOT_ssreflect_DOT_bigop.
Module Export mathcomp.
Module Export ssreflect.
Module bigop.
Include mathcomp_DOT_ssreflect_DOT_bigop_WRAPPED.bigop.
End bigop.

End ssreflect.

End mathcomp.

End mathcomp_DOT_ssreflect_DOT_bigop.
Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.

Import HB.structures.
Import mathcomp.ssreflect.ssreflect.
Import mathcomp.ssreflect.ssrbool.
Import mathcomp.ssreflect.ssrfun.
Import mathcomp.ssreflect.eqtype.
Import mathcomp.ssreflect.seq.
Import mathcomp.ssreflect.choice.
Import mathcomp.ssreflect.fintype.
Import mathcomp.ssreflect.finfun.
Import mathcomp.ssreflect.bigop.

Set Implicit Arguments.
Unset Strict Implicit.

Section SetType.

Variable T : finType.

Inductive set_type : predArgType := FinSet of {ffun pred T}.
Definition finfun_of_set A := let: FinSet f := A in f.
Definition set_of of phant T := set_type.
Identity Coercion type_of_set_of : set_of >-> set_type.

Definition set_isSub := Eval hnf in [isNew for finfun_of_set].
HB.instance Definition _ := set_isSub.
HB.instance Definition _ := [Finite of set_type by <:].

End SetType.

Delimit Scope set_scope with SET.
Open Scope set_scope.

Notation "{ 'set' T }" := (set_of (Phant T))
  (at level 0, format "{ 'set'  T }") : type_scope.
Notation "A :==: B" := (A == B :> {set _})
  (at level 70, no associativity, only parsing) : set_scope.
Notation "A :!=: B" := (A != B :> {set _})
  (at level 70, no associativity, only parsing) : set_scope.

HB.lock
Definition finset (T : finType) (P : pred T) : {set T} := @FinSet T (finfun P).

HB.lock
Definition pred_of_set T (A : set_type T) : fin_pred_sort (predPredType T)
:= val A.

Notation "[ 'set' x : T | P ]" := (finset (fun x : T => P%B))
  (at level 0, x at level 99, only parsing) : set_scope.
Notation "[ 'set' x | P ]" := [set x : _ | P]
  (at level 0, x, P at level 99, format "[ 'set'  x  |  P ]") : set_scope.
Notation "[ 'set' x 'in' A ]" := [set x | x \in A]
  (at level 0, x at level 99, format "[ 'set'  x  'in'  A ]") : set_scope.
Notation "[ 'set' x | P & Q ]" := [set x | P && Q ]
  (at level 0, x, P at level 99, format "[ 'set'  x  |  P  &  Q ]") : set_scope.
Notation "[ 'set' x 'in' A | P ]" := [set x | x \in A & P]
  (at level 0, x at level 99, format "[ 'set'  x  'in'  A  |  P ]") : set_scope.

Coercion pred_of_set: set_type >-> fin_pred_sort.

Section BasicSetTheory.

Variable T : finType.

Definition set0 := [set x : T | false].
Definition setTfor (phT : phant T) := [set x : T | true].

End BasicSetTheory.

Arguments set0 {T}.

Notation "[ 'set' : T ]" := (setTfor (Phant T))
  (at level 0, format "[ 'set' :  T ]") : set_scope.

Notation setT := [set: _] (only parsing).

HB.lock
Definition set1 (T : finType) (a : T) := [set x | x == a].

Section setOpsDefs.

Variable T : finType.
Implicit Types (a x : T) (A B D : {set T}) (P : {set {set T}}).

Definition setU A B := [set x | (x \in A) || (x \in B)].
Definition setI A B := [set x in A | x \in B].
Definition setC A := [set x | x \notin A].
Definition setD A B := [set x | x \notin B & x \in A].

End setOpsDefs.

Notation "[ 'set' a ]" := (set1 a)
  (at level 0, a at level 99, format "[ 'set'  a ]") : set_scope.
Notation "A :&: B" := (setI A B) : set_scope.
Notation "~: A" := (setC A) (at level 35, right associativity) : set_scope.
Notation "A :\: B" := (setD A B) : set_scope.

HB.lock
Definition imset (aT rT : finType) f mD := [set y in @image_mem aT rT f mD].

HB.lock
Definition imset2 (aT1 aT2 rT : finType) f (D1 : mem_pred aT1) (D2 : _ -> mem_pred aT2) :=
  [set y in @image_mem _ rT (uncurry f) (mem [pred u | D1 u.1 & D2 u.1 u.2])].

Definition preimset (aT : finType) rT f (R : mem_pred rT) :=
  [set x : aT | in_mem (f x) R].

Notation "f @^-1: A" := (preimset f (mem A)) (at level 24) : set_scope.
Notation "f @: A" := (imset f (mem A)) (at level 24) : set_scope.
Notation "f @2: ( A , B )" := (imset2 f (mem A) (fun _ => mem B))
  (at level 24, format "f  @2:  ( A ,  B )") : set_scope.

Notation "\bigcup_ ( i : t | P ) F" :=
  (\big[@setU _/set0]_(i : t | P%B) F%SET) (only parsing): set_scope.
Notation "\bigcap_ ( i | P ) F" :=
  (\big[@setI _/setT]_(i | P%B) F%SET) : set_scope.
Notation "\bigcap_ ( i : t | P ) F" :=
  (\big[@setI _/setT]_(i : t | P%B) F%SET) (only parsing): set_scope.
Notation "\bigcap_ ( i 'in' A ) F" :=
  (\big[@setI _/setT]_(i in A) F%SET) : set_scope.

Section MaxSetMinSet.

Variable T : finType.
Notation sT := {set T}.
Implicit Types A B C : sT.

Definition minset P A := [forall (B : sT | B \subset A), (B == A) == P B].

Fact maxset_key : unit.
Admitted.
Definition maxset P A :=
  minset (fun B => locked_with maxset_key P (~: B)) (~: A).

End MaxSetMinSet.

Import mathcomp.ssreflect.ssrnat.
Import mathcomp.ssreflect.div.

Fixpoint edivn2 q r := if r is r'.+2 then edivn2 q.+1 r' else (q, r).

Fixpoint elogn2 e q r {struct q} :=
  match q, r with
  | 0, _ | _, 0 => (e, q)
  | q'.+1, 1 => elogn2 e.+1 q' q'
  | q'.+1, r'.+2 => elogn2 e q' r'
  end.

Definition ifnz T n (x y : T) := if n is 0 then y else x.

Definition cons_pfactor (p e : nat) pd := ifnz e ((p, e) :: pd) pd.

Notation "p ^? e :: pd" := (cons_pfactor p e pd)
  (at level 30, e at level 30, pd at level 60) : nat_scope.

Section prime_decomp.

Local Fixpoint prime_decomp_rec m k a b c e :=
  let p := k.*2.+1 in
  if a is a'.+1 then
    if b - (ifnz e 1 k - c) is b'.+1 then
      [rec m, k, a', b', ifnz c c.-1 (ifnz e p.-2 1), e] else
    if (b == 0) && (c == 0) then
      let b' := k + a' in [rec b'.*2.+3, k, a', b', k.-1, e.+1] else
    let bc' := ifnz e (ifnz b (k, 0) (edivn2 0 c)) (b, c) in
    p ^? e :: ifnz a' [rec m, k.+1, a'.-1, bc'.1 + a', bc'.2, 0] [:: (m, 1)]
  else if (b == 0) && (c == 0) then [:: (p, e.+2)] else p ^? e :: [:: (m, 1)]
where "[ 'rec' m , k , a , b , c , e ]" := (prime_decomp_rec m k a b c e).

Definition prime_decomp n :=
  let: (e2, m2) := elogn2 0 n.-1 n.-1 in
  if m2 < 2 then 2 ^? e2 :: 3 ^? m2 :: [::] else
  let: (a, bc) := edivn m2.-2 3 in
  let: (b, c) := edivn (2 - bc) 2 in
  2 ^? e2 :: [rec m2.*2.+1, 1, a, b, c, 0].

End prime_decomp.

Definition primes n := unzip1 (prime_decomp n).

Definition nat_pred := simpl_pred nat.

Definition pdiv n := head 1 (primes n).
Coercion nat_pred_of_nat (p : nat) : nat_pred.
Admitted.

Section NatPreds.

Variables (n : nat) (pi : nat_pred).
Definition negn : nat_pred.
exact ([predC pi]).
Defined.
Definition pnat : pred nat.
exact (fun m => (m > 0) && all [in pi] (primes m)).
Defined.

End NatPreds.

Notation "pi ^'" := (negn pi) (at level 2, format "pi ^'") : nat_scope.

Notation "pi .-nat" := (pnat pi) (at level 2, format "pi .-nat") : nat_scope.

Declare Scope group_scope.
Delimit Scope Group_scope with G.
Open Scope group_scope.
Reserved Notation "#| B : A |" (at level 0, B, A at level 99,
  format "#| B  :  A |").
Reserved Notation "A <| B" (at level 70, no associativity).

HB.mixin Record isMulBaseGroup G := {
  mulg_subdef : G -> G -> G;
  oneg_subdef : G;
  invg_subdef : G -> G;
  mulgA_subproof : associative mulg_subdef ;
  mul1g_subproof : left_id oneg_subdef  mulg_subdef ;
  invgK_subproof : involutive invg_subdef ;
  invMg_subproof : {morph invg_subdef  : x y / mulg_subdef  x y >-> mulg_subdef  y x}
}.

#[arg_sort, short(type="baseFinGroupType")]
HB.structure Definition BaseFinGroup := { G of isMulBaseGroup G & Finite G }.
Section ElementOps.

Variable T : baseFinGroupType.
Notation rT := (BaseFinGroup.sort T).

Definition oneg : rT := Eval unfold oneg_subdef in @oneg_subdef T.
Definition mulg : T -> T -> rT := Eval unfold mulg_subdef in @mulg_subdef T.
Definition invg : T -> rT := Eval unfold invg_subdef in @invg_subdef T.
Definition expgn_rec (x : T) n : rT := iterop n mulg x oneg.

End ElementOps.

Definition expgn := nosimpl expgn_rec.

Notation "1" := (@oneg _) : group_scope.
Notation "x1 * x2" := (mulg x1 x2) : group_scope.
Notation "x ^-1" := (invg x) : group_scope.

HB.mixin Record BaseFinGroup_isGroup G of BaseFinGroup G := {
  mulVg_subproof : left_inverse (@oneg G) (@invg _) (@mulg _)
}.

#[short(type="finGroupType")]
HB.structure Definition FinGroup :=
  { G of BaseFinGroup_isGroup G & BaseFinGroup G }.

HB.factory Record isMulGroup G of Finite G := {
  mulg : G -> G -> G;
  oneg : G;
  invg : G -> G;
  mulgA : associative mulg;
  mul1g : left_id oneg mulg;
  mulVg : left_inverse oneg invg mulg;
}.

HB.builders Context G of isMulGroup G.
Infix "*" := mulg.

Lemma mk_invgK : involutive invg.
Admitted.

Lemma mk_invMg : {morph invg : x y / x * y >-> y * x}.
Admitted.

HB.instance Definition _ :=
  isMulBaseGroup.Build G mulgA mul1g mk_invgK mk_invMg.
HB.instance Definition _ := BaseFinGroup_isGroup.Build G mulVg.

HB.end.

Definition conjg (T : finGroupType) (x y : T) := y^-1 * (x * y).
Notation "x1 ^ x2" := (conjg x1 x2) : group_scope.

Definition commg (T : finGroupType) (x y : T) := x^-1 * x ^ y.

Prenex Implicits mulg invg expgn conjg commg.

Section BaseSetMulDef.

Variable gT : baseFinGroupType.
Implicit Types A B : {set gT}.

Definition set_mulg A B := mulg @2: (A, B).
Definition set_invg A := invg @^-1: A.

Lemma set_mul1g : left_id [set 1] set_mulg.
Admitted.

Lemma set_mulgA : associative set_mulg.
Admitted.

Lemma set_invgK : involutive set_invg.
Admitted.

Lemma set_invgM : {morph set_invg : A B / set_mulg A B >-> set_mulg B A}.
Admitted.

HB.instance Definition set_base_group := isMulBaseGroup.Build (set_type gT)
  set_mulgA set_mul1g set_invgK set_invgM.

End BaseSetMulDef.

Module Export GroupSet.
Definition sort (gT : baseFinGroupType) := {set gT}.
End GroupSet.
Identity Coercion GroupSet_of_sort : GroupSet.sort >-> set_of.

Module Type GroupSetBaseGroupSig.
Definition sort (gT : baseFinGroupType) := BaseFinGroup.arg_sort {set gT}.
End GroupSetBaseGroupSig.

Module MakeGroupSetBaseGroup (Gset_base : GroupSetBaseGroupSig).
Identity Coercion of_sort : Gset_base.sort >-> BaseFinGroup.arg_sort.
End MakeGroupSetBaseGroup.

Module Export GroupSetBaseGroup := MakeGroupSetBaseGroup GroupSet.

Section GroupSetMulDef.

Variable gT : finGroupType.
Implicit Types A B : {set gT}.
Definition rcoset A x := mulg^~ x @: A.
Definition rcosets A B := rcoset A @: B.
Definition indexg B A := #|rcosets A B|.

Definition conjugate A x := conjg^~ x @: A.

Definition commg_set A B := commg @2: (A, B).

Definition normaliser A := [set x | conjugate A x \subset A].
Definition centraliser A := \bigcap_(x in A) normaliser [set x].
Definition abelian A := A \subset centraliser A.
Definition normal A B := (A \subset B) && (B \subset normaliser A).

End GroupSetMulDef.

Notation "#| B : A |" := (indexg B A) : group_scope.

Notation "''N' ( A )" := (normaliser A) : group_scope.
Notation "A <| B" := (normal A B) : group_scope.

Section GroupSetMulProp.

Variable gT : finGroupType.
Implicit Types A B C D : {set gT}.

Definition group_set A := (1 \in A) && (A * A \subset A).

Structure group_type : Type := Group {
  gval :> GroupSet.sort gT;
  _ : group_set gval
}.
Definition group_of of phant gT : predArgType.
exact (group_type).
Defined.
Local Notation groupT := (group_of (Phant gT)).

HB.instance Definition _ := [isSub for gval].
#[hnf] HB.instance Definition _ := [Finite of group_type by <:].

Definition group (A : {set gT}) gA : groupT := @Group A gA.

End GroupSetMulProp.

Notation "{ 'group' gT }" := (group_of (Phant gT))
  (at level 0, format "{ 'group'  gT }") : type_scope.

HB.lock
Definition generated (gT : finGroupType) (A : {set gT}) :=
  \bigcap_(G : {group gT} | A \subset G) G.
Definition commutator (gT : finGroupType) (A B : {set gT}) := generated (commg_set A B).
Notation "<< A >>"  := (generated A) : group_scope.
Notation "[ ~: A1 , A2 , .. , An ]" :=
  (commutator .. (commutator A1 A2) .. An) : group_scope.

Section GroupInter.

Variable gT : finGroupType.

Lemma group_set_generated (A : {set gT}) : group_set <<A>>.
Admitted.

Canonical generated_group A := group (group_set_generated A).

End GroupInter.

Section MinMaxGroup.

Variable gT : finGroupType.
Implicit Types gP : pred {group gT}.

Definition maxgroup A gP := maxset (fun A => group_set A && gP <<A>>%G) A.
Definition mingroup A gP := minset (fun A => group_set A && gP <<A>>%G) A.

End MinMaxGroup.

Notation "[ 'max' A 'of' G | gP ]" :=
  (maxgroup A (fun G : {group _} => gP)) : group_scope.
Notation "[ 'max' G | gP ]" := [max gval G of G | gP] : group_scope.
Notation "[ 'min' A 'of' G | gP ]" :=
  (mingroup A (fun G : {group _} => gP)) : group_scope.
Notation "[ 'min' A 'of' G | gP & gQ ]" :=
  [min A of G | gP && gQ] : group_scope.

Section Cosets.

Variables (gT : finGroupType) (Q A : {set gT}).

Notation H := <<A>>.
Definition coset_range := [pred B in rcosets H 'N(A)].

Record coset_of : Type :=
  Coset { set_of_coset :> GroupSet.sort gT; _ : coset_range set_of_coset }.

HB.instance Definition _ := [isSub for set_of_coset].
#[hnf] HB.instance Definition _ := [Finite of coset_of by <:].

Lemma coset_one_proof : coset_range H.
admit.
Defined.
Definition coset_one := Coset coset_one_proof.

Lemma coset_range_mul (B C : coset_of) : coset_range (B * C).
admit.
Defined.

Definition coset_mul B C := Coset (coset_range_mul B C).

Lemma coset_range_inv (B : coset_of) : coset_range B^-1.
admit.
Defined.

Definition coset_inv B := Coset (coset_range_inv B).

Lemma coset_mulP : associative coset_mul.
admit.
Defined.

Lemma coset_oneP : left_id coset_one coset_mul.
admit.
Defined.

Lemma coset_invP : left_inverse coset_one coset_inv coset_mul.
admit.
Defined.

HB.instance Definition _ :=
  isMulGroup.Build coset_of coset_mulP coset_oneP coset_invP.
Definition quotient : {set coset_of}.
Admitted.

End Cosets.

Notation "A / H" := (quotient A H) : group_scope.

Section PgroupDefs.

Variable gT : finGroupType.
Implicit Type (x : gT) (A B : {set gT}) (pi : nat_pred) (p n : nat).

Definition pgroup pi A := pi.-nat #|A|.

Definition psubgroup pi A B := (B \subset A) && pgroup pi B.

Definition p_group A := pgroup (pdiv #|A|) A.

Definition Hall A B := (B \subset A) && coprime #|B| #|A : B|.

Definition pHall pi A B := [&& B \subset A, pgroup pi B & pi^'.-nat #|A : B|].

Definition Sylow A B := p_group B && Hall A B.

End PgroupDefs.

Notation "pi .-group" := (pgroup pi)
  (at level 2, format "pi .-group") : group_scope.

Notation "pi .-subgroup ( A )" := (psubgroup pi A)
  (at level 8, format "pi .-subgroup ( A )") : group_scope.

Notation "pi .-Hall ( G )" := (pHall pi G)
  (at level 8, format "pi .-Hall ( G )") : group_scope.

Notation "p .-Sylow ( G )" := (nat_pred_of_nat p).-Hall(G)
  (at level 8, format "p .-Sylow ( G )") : group_scope.

Section PcoreDef.

Variables (pi : nat_pred) (gT : finGroupType) (A : {set gT}).

Definition pcore := \bigcap_(G | [max G | pi.-subgroup(A) G]) G.

End PcoreDef.
Notation "''O_' pi ( G )" := (pcore pi G)
  (at level 8, pi at level 2, format "''O_' pi ( G )") : group_scope.

Definition derived_at_rec n (gT : finGroupType) (A : {set gT}) :=
  iter n (fun B => [~: B, B]) A.

Definition derived_at := nosimpl derived_at_rec.
Notation "G ^` ( n )" := (derived_at n G) : group_scope.

Section GroupDefs.

Variable gT : finGroupType.
Implicit Types A B U V : {set gT}.

Definition maximal A B := [max A of G | G \proper B].

Definition minnormal A B := [min A of G | G :!=: 1 & B \subset 'N(G)].

Definition simple A := minnormal A A.
End GroupDefs.

Section PropertiesDefs.

Variables (gT : finGroupType) (A : {set gT}).

Definition solvable :=
  [forall (G : {group gT} | G \subset A :&: [~: G, G]), G :==: 1].

End PropertiesDefs.

HB.mixin Record IsMinSimpleOddGroup gT of FinGroup gT := {
  mFT_odd_full : odd #|[set: gT]|;
  mFT_simple : simple [set: gT];
  mFT_nonSolvable : ~~ solvable [set: gT];
  mFT_min : forall M : {group gT}, M \proper [set: gT] -> solvable M
}.

#[short(type="minSimpleOddGroupType")]
HB.structure
Definition minSimpleOddGroup := { G of IsMinSimpleOddGroup G & FinGroup G }.

Notation TheMinSimpleOddGroup gT :=
  [set: BaseFinGroup.arg_sort gT]
  (only parsing).

Section MinSimpleOdd.

Variable gT : minSimpleOddGroupType.
Notation G := (TheMinSimpleOddGroup gT).

Definition minSimple_max_groups := [set M : {group gT} | maximal M G].

End MinSimpleOdd.

Notation "''M'" := (minSimple_max_groups _) : group_scope.
Reserved Notation "M `_ \sigma" (at level 3, format "M `_ \sigma").

Section Def.

Variable gT : finGroupType.

Variable M : {set gT}.

Definition sigma :=
  [pred p | [exists (P : {group gT} | p.-Sylow(M) P), 'N(P) \subset M]].
Definition sigma_core := 'O_sigma(M).

End Def.

Notation "\sigma ( M )" := (sigma M) : group_scope.
Notation "M `_ \sigma" := (sigma_core M) : group_scope.

Section Definitons.

Variable gT : minSimpleOddGroupType.
Implicit Type M X : {set gT}.

Fact kappa_key : unit.
Admitted.
Definition kappa_def M : nat_pred.
Admitted.
Definition kappa := locked_with kappa_key kappa_def.

Definition sigma_kappa M := [predU \sigma(M) & kappa M].

Definition TypeF_maxgroups := [set M in 'M | (kappa M)^'.-group M].

Definition TypeP_maxgroups := 'M :\: TypeF_maxgroups.

Definition TypeP1_maxgroups :=
  [set M in TypeP_maxgroups | (sigma_kappa M).-group M].

End Definitons.

Notation "\kappa ( M )" := (kappa M)
  (at level 8, format "\kappa ( M )") : group_scope.

Notation "''M_' ''P1'" := (TypeP1_maxgroups _)
  (at level 2, format "''M_' ''P1'") : group_scope.

Section Definitions.

Variables (gT : finGroupType) (M : {set gT}).

Definition Fitting_core :=
  <<\bigcup_(P : {group gT} | Sylow M P && (P <| M)) P>>.

End Definitions.

Notation "M `_ \F" := (Fitting_core M)
  (at level 3, format "M `_ \F") : group_scope.

Section Definitions.

Variable gT : minSimpleOddGroupType.

Implicit Types M U V W X : {set gT}.

Definition FTtype M :=
  if \kappa(M)^'.-group M then 1%N else
  if M`_\sigma != M^`(1) then 2 else
  if M`_\F == M`_\sigma then 5 else
  if abelian (M`_\sigma / M`_\F) then 3 else 4.

Definition FTcore M := if 0 < FTtype M <= 2 then M`_\F else M^`(1).

End Definitions.

Notation "M `_ \s" := (FTcore M) (at level 3, format "M `_ \s") : group_scope.

Variable gT : minSimpleOddGroupType.

Variable M : {group gT}.

Lemma FTtype_P1max : (M \in 'M_'P1) = (2 < FTtype M <= 5).
Admitted.

Lemma Msigma_eq_der1 : M \in 'M_'P1 -> M`_\sigma = M^`(1).
Admitted.

Lemma Fcore_eq_FTcore : reflect (M`_\F = M`_\s) (FTtype M \in pred3 1%N 2 5).
Proof.
rewrite /FTcore -mem_iota 3!inE orbA; case type12M: (_ || _); first by left.
move: type12M FTtype_P1max; rewrite /FTtype; do 2![case: ifP => // _] => _.
rewrite !(fun_if (leq^~ 5)) !(fun_if (leq 3)) !if_same /= => P1maxM.
rewrite Msigma_eq_der1 // !(fun_if (eq_op^~ 5)) if_same.
by rewrite [if _ then _ else _]andbT; apply: eqP.
