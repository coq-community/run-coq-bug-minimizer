
(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "-projection-no-head-constant" "-w" "-redundant-canonical-projection" "-w" "-notation-overridden" "-w" "-deprecated-native-compiler-option" "-native-compiler" "ondemand" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/oddorder/theories" "odd_order" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/HB" "HB" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/elpi" "elpi" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/mathcomp" "mathcomp" "-top" "Top.bug_01") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 1375 lines to 60 lines, then from 73 lines to 1675 lines, then from 1680 lines to 90 lines, then from 103 lines to 2712 lines, then from 2715 lines to 148 lines, then from 161 lines to 2932 lines, then from 2936 lines to 147 lines, then from 160 lines to 1746 lines, then from 1749 lines to 189 lines, then from 202 lines to 1254 lines, then from 1259 lines to 145 lines, then from 158 lines to 976 lines, then from 981 lines to 153 lines, then from 166 lines to 775 lines, then from 779 lines to 245 lines, then from 239 lines to 175 lines, then from 188 lines to 604 lines, then from 609 lines to 168 lines, then from 181 lines to 1580 lines, then from 1585 lines to 231 lines, then from 244 lines to 1254 lines, then from 1259 lines to 261 lines, then from 274 lines to 1855 lines, then from 1859 lines to 261 lines, then from 274 lines to 3310 lines, then from 3315 lines to 2052 lines, then from 1806 lines to 484 lines, then from 497 lines to 2159 lines, then from 2164 lines to 571 lines, then from 584 lines to 3152 lines, then from 3155 lines to 2910 lines, then from 2767 lines to 646 lines, then from 659 lines to 3393 lines, then from 3398 lines to 3162 lines, then from 3016 lines to 743 lines, then from 756 lines to 1264 lines, then from 1269 lines to 933 lines, then from 879 lines to 827 lines, then from 840 lines to 1556 lines, then from 1561 lines to 927 lines, then from 940 lines to 3367 lines, then from 3371 lines to 3182 lines, then from 2982 lines to 1060 lines, then from 1073 lines to 2149 lines, then from 2154 lines to 1882 lines, then from 1841 lines to 1076 lines, then from 1089 lines to 1786 lines, then from 1791 lines to 1392 lines, then from 1283 lines to 1245 lines, then from 1258 lines to 5992 lines, then from 5997 lines to 6156 lines, then from 5898 lines to 2800 lines, then from 2808 lines to 1432 lines, then from 1445 lines to 3621 lines, then from 3626 lines to 3173 lines *)
(* coqc version 8.19+alpha compiled with OCaml 4.14.1
   coqtop version 728713d43dde:/builds/coq/coq/_build/default,(HEAD detached at 25e3b11) (25e3b11cee094cfce7e16d10e58d3b7b318ea70c)
   Expected coqc runtime on this file: 5.973 sec *)
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

Module Export AdmitTactic.
Module Import LocalFalse.
Inductive False : Prop := .
End LocalFalse.
Axiom proof_admitted : False.
Import Coq.Init.Ltac.
Tactic Notation "admit" := abstract case proof_admitted.
End AdmitTactic.

Module Export mathcomp_DOT_ssreflect_DOT_ssrnat_WRAPPED.
Module Export ssrnat.
 
 
Import HB.structures.
Import mathcomp.ssreflect.ssreflect.
Import mathcomp.ssreflect.ssrfun.
Import mathcomp.ssreflect.ssrbool.
Import mathcomp.ssreflect.eqtype.
Import Coq.NArith.BinNat.
Export Coq.setoid_ring.Ring.

 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope coq_nat_scope.
Declare Scope nat_rec_scope.

 

#[global] Remove Hints plus_n_O plus_n_Sm mult_n_O mult_n_Sm : core.

 

Delimit Scope coq_nat_scope with coq_nat.

Notation "m + n" := (plus m n) : coq_nat_scope.
Notation "m - n" := (minus m n) : coq_nat_scope.
Notation "m * n" := (mult m n) : coq_nat_scope.
Notation "m <= n" := (le m n) : coq_nat_scope.
Notation "m < n" := (lt m n) : coq_nat_scope.
Notation "m >= n" := (ge m n) : coq_nat_scope.
Notation "m > n" := (gt m n) : coq_nat_scope.

 
 

Delimit Scope N_scope with num.
 
Set Warnings "-hiding-delimiting-key".
Delimit Scope nat_scope with N.
Set Warnings "hiding-delimiting-key".
Delimit Scope nat_rec_scope with Nrec.

 
 
 

Notation succn := Datatypes.S.
Notation predn := Peano.pred.

Notation "n .+1" := (succn n) (at level 2, left associativity,
  format "n .+1") : nat_scope.
Notation "n .+2" := n.+1.+1 (at level 2, left associativity,
  format "n .+2") : nat_scope.
Notation "n .+3" := n.+2.+1 (at level 2, left associativity,
  format "n .+3") : nat_scope.
Notation "n .+4" := n.+2.+2 (at level 2, left associativity,
  format "n .+4") : nat_scope.

Notation "n .-1" := (predn n) (at level 2, left associativity,
  format "n .-1") : nat_scope.
Notation "n .-2" := n.-1.-1 (at level 2, left associativity,
  format "n .-2") : nat_scope.

Lemma succnK : cancel succn predn.
Admitted.
Lemma succn_inj : injective succn.
Admitted.

 

Reserved Notation "n .*2" (at level 2, left associativity, format "n .*2").
Reserved Notation "n ./2" (at level 2, left associativity, format "n ./2").

 

Fixpoint eqn m n {struct m} :=
  match m, n with
  | 0, 0 => true
  | m'.+1, n'.+1 => eqn m' n'
  | _, _ => false
  end.

Lemma eqnP : Equality.axiom eqn.
Admitted.

HB.instance Definition _ := hasDecEq.Build nat eqnP.

Arguments eqn !m !n.
Arguments eqnP {x y}.

Lemma eqnE : eqn = eq_op.
Admitted.

Lemma eqSS m n : (m.+1 == n.+1) = (m == n).
Admitted.

Lemma nat_irrelevance (x y : nat) (E E' : x = y) : E = E'.
Admitted.

 

Definition addn_rec := plus.
Notation "m + n" := (addn_rec m n) : nat_rec_scope.

Definition addn := nosimpl addn_rec.
Notation "m + n" := (addn m n) : nat_scope.

Lemma addnE : addn = addn_rec.
Admitted.

Lemma plusE : plus = addn.
Admitted.

Lemma add0n : left_id 0 addn.
Admitted.
Lemma addSn m n : m.+1 + n = (m + n).+1.
Admitted.
Lemma add1n n : 1 + n = n.+1.
Admitted.

Lemma addn0 : right_id 0 addn.
Admitted.

Lemma addnS m n : m + n.+1 = (m + n).+1.
Admitted.

Lemma addSnnS m n : m.+1 + n = m + n.+1.
Admitted.

Lemma addnCA : left_commutative addn.
Admitted.

Lemma addnC : commutative addn.
Admitted.

Lemma addn1 n : n + 1 = n.+1.
Admitted.

Lemma addnA : associative addn.
Admitted.

Lemma addnAC : right_commutative addn.
Admitted.

Lemma addnCAC m n p : m + n + p = p + n + m.
Admitted.

Lemma addnACl m n p: m + n + p = n + (p + m).
Admitted.

Lemma addnACA : interchange addn addn.
Admitted.

Lemma addn_eq0 m n : (m + n == 0) = (m == 0) && (n == 0).
Admitted.

Lemma addn_eq1 m n :
  (m + n == 1) = ((m == 1) && (n == 0)) || ((m == 0) && (n == 1)).
Admitted.

Lemma eqn_add2l p m n : (p + m == p + n) = (m == n).
Admitted.

Lemma eqn_add2r p m n : (m + p == n + p) = (m == n).
Admitted.

Lemma addnI : right_injective addn.
Admitted.

Lemma addIn : left_injective addn.
Admitted.

Lemma addn2 m : m + 2 = m.+2.
Admitted.
Lemma add2n m : 2 + m = m.+2.
Admitted.
Lemma addn3 m : m + 3 = m.+3.
Admitted.
Lemma add3n m : 3 + m = m.+3.
Admitted.
Lemma addn4 m : m + 4 = m.+4.
Admitted.
Lemma add4n m : 4 + m = m.+4.
Admitted.

 
 

Definition subn_rec := minus.
Arguments subn_rec : simpl nomatch.
Notation "m - n" := (subn_rec m n) : nat_rec_scope.

Definition subn := nosimpl subn_rec.
Notation "m - n" := (subn m n) : nat_scope.

Lemma subnE : subn = subn_rec.
Admitted.
Lemma minusE : minus = subn.
Admitted.

Lemma sub0n : left_zero 0 subn.
Admitted.
Lemma subn0 : right_id 0 subn.
Admitted.
Lemma subnn : self_inverse 0 subn.
Admitted.

Lemma subSS n m : m.+1 - n.+1 = m - n.
Admitted.
Lemma subn1 n : n - 1 = n.-1.
Admitted.
Lemma subn2 n : (n - 2)%N = n.-2.
Admitted.

Lemma subnDl p m n : (p + m) - (p + n) = m - n.
Admitted.

Lemma subnDr p m n : (m + p) - (n + p) = m - n.
Admitted.

Lemma addnK n : cancel (addn^~ n) (subn^~ n).
Admitted.

Lemma addKn n : cancel (addn n) (subn^~ n).
Admitted.

Lemma subSnn n : n.+1 - n = 1.
Admitted.

Lemma subnDA m n p : n - (m + p) = (n - m) - p.
Admitted.

Lemma subnAC : right_commutative subn.
Admitted.

Lemma subnS m n : m - n.+1 = (m - n).-1.
Admitted.

Lemma subSKn m n : (m.+1 - n).-1 = m - n.
Admitted.

 

Definition leq m n := m - n == 0.

Notation "m <= n" := (leq m n) : nat_scope.
Notation "m < n"  := (m.+1 <= n) : nat_scope.
Notation "m >= n" := (n <= m) (only parsing) : nat_scope.
Notation "m > n"  := (n < m) (only parsing)  : nat_scope.

 
Definition geq := [rel m n | m >= n].
Definition ltn := [rel m n | m < n].
Definition gtn := [rel m n | m > n].

Notation "m <= n <= p" := ((m <= n) && (n <= p)) : nat_scope.
Notation "m < n <= p" := ((m < n) && (n <= p)) : nat_scope.
Notation "m <= n < p" := ((m <= n) && (n < p)) : nat_scope.
Notation "m < n < p" := ((m < n) && (n < p)) : nat_scope.

Lemma ltnS m n : (m < n.+1) = (m <= n).
Admitted.
Lemma leq0n n : 0 <= n.
Admitted.
Lemma ltn0Sn n : 0 < n.+1.
Admitted.
Lemma ltn0 n : n < 0 = false.
Admitted.
Lemma leqnn n : n <= n.
Admitted.
#[global] Hint Resolve leqnn : core.
Lemma ltnSn n : n < n.+1.
Admitted.
Lemma eq_leq m n : m = n -> m <= n.
Admitted.
Lemma leqnSn n : n <= n.+1.
Admitted.
#[global] Hint Resolve leqnSn : core.
Lemma leq_pred n : n.-1 <= n.
Admitted.
Lemma leqSpred n : n <= n.-1.+1.
Admitted.

Lemma ltn_predL n : (n.-1 < n) = (0 < n).
Admitted.

Lemma ltn_predRL m n : (m < n.-1) = (m.+1 < n).
Admitted.

Lemma ltn_predK m n : m < n -> n.-1.+1 = n.
Admitted.

Lemma prednK n : 0 < n -> n.-1.+1 = n.
Admitted.

Lemma leqNgt m n : (m <= n) = ~~ (n < m).
Admitted.

Lemma leqVgt m n : (m <= n) || (n < m).
Admitted.

Lemma ltnNge m n : (m < n) = ~~ (n <= m).
Admitted.

Lemma ltnn n : n < n = false.
Admitted.

Lemma leqn0 n : (n <= 0) = (n == 0).
Admitted.
Lemma lt0n n : (0 < n) = (n != 0).
Admitted.
Lemma lt0n_neq0 n : 0 < n -> n != 0.
Admitted.
Lemma eqn0Ngt n : (n == 0) = ~~ (n > 0).
Admitted.
Lemma neq0_lt0n n : (n == 0) = false -> 0 < n.
Admitted.
#[global] Hint Resolve lt0n_neq0 neq0_lt0n : core.

Lemma eqn_leq m n : (m == n) = (m <= n <= m).
Admitted.

Lemma anti_leq : antisymmetric leq.
Admitted.

Lemma neq_ltn m n : (m != n) = (m < n) || (n < m).
Admitted.

Lemma gtn_eqF m n : m < n -> n == m = false.
Admitted.

Lemma ltn_eqF m n : m < n -> m == n = false.
Admitted.

Lemma ltn_geF m n : m < n -> m >= n = false.
Admitted.

Lemma leq_gtF m n : m <= n -> m > n = false.
Admitted.

Lemma leq_eqVlt m n : (m <= n) = (m == n) || (m < n).
Admitted.

Lemma ltn_neqAle m n : (m < n) = (m != n) && (m <= n).
Admitted.

Lemma leq_trans n m p : m <= n -> n <= p -> m <= p.
Admitted.

Lemma leq_ltn_trans n m p : m <= n -> n < p -> m < p.
Admitted.

Lemma ltnW m n : m < n -> m <= n.
Admitted.
#[global] Hint Resolve ltnW : core.

Lemma leqW m n : m <= n -> m <= n.+1.
Admitted.

Lemma ltn_trans n m p : m < n -> n < p -> m < p.
Admitted.

Lemma leq_total m n : (m <= n) || (m >= n).
Admitted.

 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
Lemma ubnP m : {n | m < n}.
Admitted.
Lemma ltnSE m n : m < n.+1 -> m <= n.
Admitted.
Variant ubn_leq_spec m : nat -> Type := UbnLeq n of m <= n : ubn_leq_spec m n.
Variant ubn_geq_spec m : nat -> Type := UbnGeq n of m >= n : ubn_geq_spec m n.
Variant ubn_eq_spec m : nat -> Type := UbnEq n of m == n : ubn_eq_spec m n.
Lemma ubnPleq m : ubn_leq_spec m m.
Admitted.
Lemma ubnPgeq m : ubn_geq_spec m m.
Admitted.
Lemma ubnPeq m : ubn_eq_spec m m.
Admitted.
Lemma ltn_ind P : (forall n, (forall m, m < n -> P m) -> P n) -> forall n, P n.
Admitted.

 

Lemma leP m n : reflect (m <= n)%coq_nat (m <= n).
Admitted.
Arguments leP {m n}.

Lemma le_irrelevance m n le_mn1 le_mn2 : le_mn1 = le_mn2 :> (m <= n)%coq_nat.
Admitted.

Lemma ltP m n : reflect (m < n)%coq_nat (m < n).
Admitted.
Arguments ltP {m n}.

Lemma lt_irrelevance m n lt_mn1 lt_mn2 : lt_mn1 = lt_mn2 :> (m < n)%coq_nat.
Admitted.

 

Lemma leq_add2l p m n : (p + m <= p + n) = (m <= n).
Admitted.

Lemma ltn_add2l p m n : (p + m < p + n) = (m < n).
Admitted.

Lemma leq_add2r p m n : (m + p <= n + p) = (m <= n).
Admitted.

Lemma ltn_add2r p m n : (m + p < n + p) = (m < n).
Admitted.

Lemma leq_add m1 m2 n1 n2 : m1 <= n1 -> m2 <= n2 -> m1 + m2 <= n1 + n2.
Admitted.

Lemma leq_addl m n : n <= m + n.
Admitted.

Lemma leq_addr m n : n <= n + m.
Admitted.

Lemma ltn_addl m n p : m < n -> m < p + n.
Admitted.

Lemma ltn_addr m n p : m < n -> m < n + p.
Admitted.

Lemma addn_gt0 m n : (0 < m + n) = (0 < m) || (0 < n).
Admitted.

Lemma subn_gt0 m n : (0 < n - m) = (m < n).
Admitted.

Lemma subn_eq0 m n : (m - n == 0) = (m <= n).
Admitted.

Lemma leq_subLR m n p : (m - n <= p) = (m <= n + p).
Admitted.

Lemma leq_subr m n : n - m <= n.
Admitted.

Lemma ltn_subrR m n : (n < n - m) = false.
Admitted.

Lemma leq_subrR m n : (n <= n - m) = (m == 0) || (n == 0).
Admitted.

Lemma ltn_subrL m n : (n - m < n) = (0 < m) && (0 < n).
Admitted.

Lemma subnKC m n : m <= n -> m + (n - m) = n.
Admitted.

Lemma addnBn m n : m + (n - m) = m - n + n.
Admitted.

Lemma subnK m n : m <= n -> (n - m) + m = n.
Admitted.

Lemma addnBA m n p : p <= n -> m + (n - p) = m + n - p.
Admitted.

Lemma addnBAC m n p : n <= m -> m - n + p = m + p - n.
Admitted.

Lemma addnBCA m n p : p <= m -> p <= n -> m + (n - p) = n + (m - p).
Admitted.

Lemma addnABC m n p : p <= m -> p <= n -> m + (n - p) = m - p + n.
Admitted.

Lemma subnBA m n p : p <= n -> m - (n - p) = m + p - n.
Admitted.

Lemma subnA m n p : p <= n -> n <= m -> m - (n - p) = m - n + p.
Admitted.

Lemma subKn m n : m <= n -> n - (n - m) = m.
Admitted.

Lemma subSn m n : m <= n -> n.+1 - m = (n - m).+1.
Admitted.

Lemma subnSK m n : m < n -> (n - m.+1).+1 = n - m.
Admitted.

Lemma addnCBA m n p : p <= n -> m + (n - p) = n + m - p.
Admitted.

Lemma addnBr_leq n p m : n <= p -> m + (n - p) = m.
Admitted.

Lemma addnBl_leq m n p : m <= n -> m - n + p = p.
Admitted.

Lemma subnDAC m n p : m - (n + p) = m - p - n.
Admitted.

Lemma subnCBA m n p : p <= n ->	m - (n - p) = p + m - n.
Admitted.

Lemma subnBr_leq n p m : n <= p -> m - (n - p) = m.
Admitted.

Lemma subnBl_leq m n p : m <= n -> (m - n) - p = 0.
Admitted.

Lemma subnBAC m n p : p <= n -> n <= m -> m - (n - p) = p + (m - n).
Admitted.

Lemma subDnAC m n p : p <= n -> m + n - p = n - p + m.
Admitted.

Lemma subDnCA m n p : p <= m -> m + n - p = n + (m - p).
Admitted.

Lemma subDnCAC m n p : m <= p -> m + n - p = n - (p - m).
Admitted.

Lemma addnBC m n : m - n + n = n - m + m.
Admitted.

Lemma addnCB m n : m - n + n = m + (n - m).
Admitted.

Lemma addBnAC m n p : n <= m -> m - n + p = p + m - n.
Admitted.

Lemma addBnCAC m n p : n <= m -> n <= p -> m - n + p = p - n + m.
Admitted.

Lemma addBnA m n p : n <= m -> p <= n -> m - n + p = m - (n - p).
Admitted.

Lemma subBnAC m n p : m - n - p = m - (p + n).
Admitted.

Lemma predn_sub m n : (m - n).-1 = (m.-1 - n).
Admitted.

Lemma leq_sub2r p m n : m <= n -> m - p <= n - p.
Admitted.

Lemma leq_sub2l p m n : m <= n -> p - n <= p - m.
Admitted.

Lemma leq_sub m1 m2 n1 n2 : m1 <= m2 -> n2 <= n1 -> m1 - n1 <= m2 - n2.
Admitted.

Lemma ltn_sub2r p m n : p < n -> m < n -> m - p < n - p.
Admitted.

Lemma ltn_sub2l p m n : m < p -> m < n -> p - n < p - m.
Admitted.

Lemma ltn_subRL m n p : (n < p - m) = (m + n < p).
Admitted.

Lemma leq_psubRL m n p : 0 < n -> (n <= p - m) = (m + n <= p).
Admitted.

Lemma ltn_psubLR m n p : 0 < p -> (m - n < p) = (m < n + p).
Admitted.

Lemma leq_subRL m n p : m <= p -> (n <= p - m) = (m + n <= p).
Admitted.

Lemma ltn_subLR m n p : n <= m -> (m - n < p) = (m < n + p).
Admitted.

Lemma leq_subCl m n p : (m - n <= p) = (m - p <= n).
Admitted.

Lemma ltn_subCr m n p : (p < m - n) = (n < m - p).
Admitted.

Lemma leq_psubCr m n p : 0 < p -> 0 < n -> (p <= m - n) = (n <= m - p).
Admitted.

Lemma ltn_psubCl m n p : 0 < p -> 0 < n -> (m - n < p) = (m - p < n).
Admitted.

Lemma leq_subCr m n p : n <= m -> p <= m -> (p <= m - n) = (n <= m - p).
Admitted.

Lemma ltn_subCl m n p : n <= m -> p <= m -> (m - n < p) = (m - p < n).
Admitted.

Lemma leq_sub2rE p m n : p <= n -> (m - p <= n - p) = (m <= n).
Admitted.

Lemma leq_sub2lE m n p : n <= m -> (m - p <= m - n) = (n <= p).
Admitted.

Lemma ltn_sub2rE p m n : p <= m -> (m - p < n - p) = (m < n).
Admitted.

Lemma ltn_sub2lE m n p : p <= m -> (m - p < m - n) = (n < p).
Admitted.

Lemma eqn_sub2rE p m n : p <= m -> p <= n -> (m - p == n - p) = (m == n).
Admitted.

Lemma eqn_sub2lE m n p : p <= m -> n <= m -> (m - p == m - n) = (p == n).
Admitted.

 

Definition maxn m n := if m < n then n else m.

Definition minn m n := if m < n then m else n.

Lemma max0n : left_id 0 maxn.
Admitted.
Lemma maxn0 : right_id 0 maxn.
Admitted.

Lemma maxnC : commutative maxn.
Admitted.

Lemma maxnE m n : maxn m n = m + (n - m).
Admitted.

Lemma maxnAC : right_commutative maxn.
Admitted.

Lemma maxnA : associative maxn.
Admitted.

Lemma maxnCA : left_commutative maxn.
Admitted.

Lemma maxnACA : interchange maxn maxn.
Admitted.

Lemma maxn_idPl {m n} : reflect (maxn m n = m) (m >= n).
Admitted.

Lemma maxn_idPr {m n} : reflect (maxn m n = n) (m <= n).
Admitted.

Lemma maxnn : idempotent maxn.
Admitted.

Lemma leq_max m n1 n2 : (m <= maxn n1 n2) = (m <= n1) || (m <= n2).
Admitted.
Lemma leq_maxl m n : m <= maxn m n.
Admitted.
Lemma leq_maxr m n : n <= maxn m n.
Admitted.

Lemma gtn_max m n1 n2 : (m > maxn n1 n2) = (m > n1) && (m > n2).
Admitted.

Lemma geq_max m n1 n2 : (m >= maxn n1 n2) = (m >= n1) && (m >= n2).
Admitted.

Lemma maxnSS m n : maxn m.+1 n.+1 = (maxn m n).+1.
Admitted.

Lemma addn_maxl : left_distributive addn maxn.
Admitted.

Lemma addn_maxr : right_distributive addn maxn.
Admitted.

Lemma subn_maxl : left_distributive subn maxn.
Admitted.

Lemma min0n : left_zero 0 minn.
Admitted.
Lemma minn0 : right_zero 0 minn.
Admitted.

Lemma minnC : commutative minn.
Admitted.

Lemma addn_min_max m n : minn m n + maxn m n = m + n.
Admitted.

Lemma minnE m n : minn m n = m - (m - n).
Admitted.

Lemma minnAC : right_commutative minn.
Admitted.

Lemma minnA : associative minn.
Admitted.

Lemma minnCA : left_commutative minn.
Admitted.

Lemma minnACA : interchange minn minn.
Admitted.

Lemma minn_idPl {m n} : reflect (minn m n = m) (m <= n).
Admitted.

Lemma minn_idPr {m n} : reflect (minn m n = n) (m >= n).
Admitted.

Lemma minnn : idempotent minn.
Admitted.

Lemma leq_min m n1 n2 : (m <= minn n1 n2) = (m <= n1) && (m <= n2).
Admitted.

Lemma gtn_min m n1 n2 : (m > minn n1 n2) = (m > n1) || (m > n2).
Admitted.

Lemma geq_min m n1 n2 : (m >= minn n1 n2) = (m >= n1) || (m >= n2).
Admitted.

Lemma geq_minl m n : minn m n <= m.
Admitted.
Lemma geq_minr m n : minn m n <= n.
Admitted.

Lemma addn_minr : right_distributive addn minn.
Admitted.

Lemma addn_minl : left_distributive addn minn.
Admitted.

Lemma subn_minl : left_distributive subn minn.
Admitted.

Lemma minnSS m n : minn m.+1 n.+1 = (minn m n).+1.
Admitted.

 
Lemma maxnK m n : minn (maxn m n) m = m.
Admitted.

Lemma maxKn m n : minn n (maxn m n) = n.
Admitted.

Lemma minnK m n : maxn (minn m n) m = m.
Admitted.

Lemma minKn m n : maxn n (minn m n) = n.
Admitted.

 
Lemma maxn_minl : left_distributive maxn minn.
Admitted.

Lemma maxn_minr : right_distributive maxn minn.
Admitted.

Lemma minn_maxl : left_distributive minn maxn.
Admitted.

Lemma minn_maxr : right_distributive minn maxn.
Admitted.

 

Variant leq_xor_gtn m n : nat -> nat -> nat -> nat -> bool -> bool -> Set :=
  | LeqNotGtn of m <= n : leq_xor_gtn m n m m n n true false
  | GtnNotLeq of n < m  : leq_xor_gtn m n n n m m false true.

Lemma leqP m n : leq_xor_gtn m n (minn n m) (minn m n) (maxn n m) (maxn m n)
                                 (m <= n) (n < m).
Admitted.

Variant ltn_xor_geq m n : nat -> nat -> nat -> nat -> bool -> bool -> Set :=
  | LtnNotGeq of m < n  : ltn_xor_geq m n m m n n false true
  | GeqNotLtn of n <= m : ltn_xor_geq m n n n m m true false.

Lemma ltnP m n : ltn_xor_geq m n (minn n m) (minn m n) (maxn n m) (maxn m n)
                                 (n <= m) (m < n).
Admitted.

Variant eqn0_xor_gt0 n : bool -> bool -> Set :=
  | Eq0NotPos of n = 0 : eqn0_xor_gt0 n true false
  | PosNotEq0 of n > 0 : eqn0_xor_gt0 n false true.

Lemma posnP n : eqn0_xor_gt0 n (n == 0) (0 < n).
Admitted.

Variant compare_nat m n : nat -> nat -> nat -> nat ->
                          bool -> bool -> bool -> bool -> bool -> bool -> Set :=
  | CompareNatLt of m < n :
      compare_nat m n m m n n false false false true false true
  | CompareNatGt of m > n :
      compare_nat m n n n m m false false true false true false
  | CompareNatEq of m = n :
      compare_nat m n m m m m true true true true false false.

Lemma ltngtP m n :
  compare_nat m n (minn n m) (minn m n) (maxn n m) (maxn m n)
                  (n == m) (m == n) (n <= m) (m <= n) (n < m) (m < n).
Admitted.

 
Lemma subn_if_gt T m n F (E : T) :
  (if m.+1 - n is m'.+1 then F m' else E) = (if n <= m then F (m - n) else E).
Admitted.

Notation leqLHS := (X in (X <= _)%N)%pattern.
Notation leqRHS := (X in (_ <= X)%N)%pattern.
Notation ltnLHS := (X in (X < _)%N)%pattern.
Notation ltnRHS := (X in (_ < X)%N)%pattern.

 

Section ExMinn.

Variable P : pred nat.
Hypothesis exP : exists n, P n.

Inductive acc_nat i : Prop := AccNat0 of P i | AccNatS of acc_nat i.+1.

Lemma find_ex_minn : {m | P m & forall n, P n -> n >= m}.
Admitted.

Definition ex_minn := s2val find_ex_minn.

Inductive ex_minn_spec : nat -> Type :=
  ExMinnSpec m of P m & (forall n, P n -> n >= m) : ex_minn_spec m.

Lemma ex_minnP : ex_minn_spec ex_minn.
Admitted.

End ExMinn.

Section ExMaxn.

Variables (P : pred nat) (m : nat).
Hypotheses (exP : exists i, P i) (ubP : forall i, P i -> i <= m).

Lemma ex_maxn_subproof : exists i, P (m - i).
Admitted.

Definition ex_maxn := m - ex_minn ex_maxn_subproof.

Variant ex_maxn_spec : nat -> Type :=
  ExMaxnSpec i of P i & (forall j, P j -> j <= i) : ex_maxn_spec i.

Lemma ex_maxnP : ex_maxn_spec ex_maxn.
Admitted.

End ExMaxn.

Lemma eq_ex_minn P Q exP exQ : P =1 Q -> @ex_minn P exP = @ex_minn Q exQ.
Admitted.

Lemma eq_ex_maxn (P Q : pred nat) m n exP ubP exQ ubQ :
  P =1 Q -> @ex_maxn P m exP ubP = @ex_maxn Q n exQ ubQ.
Admitted.

Section Iteration.

Variable T : Type.
Implicit Types m n : nat.
Implicit Types x y : T.
Implicit Types S : {pred T}.

Definition iter n f x :=
  let fix loop m := if m is i.+1 then f (loop i) else x in loop n.

Definition iteri n f x :=
  let fix loop m := if m is i.+1 then f i (loop i) else x in loop n.

Definition iterop n op x :=
  let f i y := if i is 0 then x else op x y in iteri n f.

Lemma iterSr n f x : iter n.+1 f x = iter n f (f x).
Admitted.

Lemma iterS n f x : iter n.+1 f x = f (iter n f x).
Admitted.

Lemma iterD n m f x : iter (n + m) f x = iter n f (iter m f x).
Admitted.

Lemma iteriS n f x : iteri n.+1 f x = f n (iteri n f x).
Admitted.

Lemma iteropS idx n op x : iterop n.+1 op x idx = iter n (op x) x.
Admitted.

Lemma eq_iter f f' : f =1 f' -> forall n, iter n f =1 iter n f'.
Admitted.

Lemma iter_fix n f x : f x = x -> iter n f x = x.
Admitted.

Lemma eq_iteri f f' : f =2 f' -> forall n, iteri n f =1 iteri n f'.
Admitted.

Lemma eq_iterop n op op' : op =2 op' -> iterop n op =2 iterop n op'.
Admitted.

Lemma iter_in f S i : {homo f : x / x \in S} -> {homo iter i f : x / x \in S}.
Admitted.

End Iteration.

Lemma iter_succn m n : iter n succn m = m + n.
Admitted.

Lemma iter_succn_0 n : iter n succn 0 = n.
Admitted.

Lemma iter_predn m n : iter n predn m = m - n.
Admitted.

 

Definition muln_rec := mult.
Notation "m * n" := (muln_rec m n) : nat_rec_scope.

Definition muln := nosimpl muln_rec.
Notation "m * n" := (muln m n) : nat_scope.

Lemma multE : mult = muln.
Admitted.
Lemma mulnE : muln = muln_rec.
Admitted.

Lemma mul0n : left_zero 0 muln.
Admitted.
Lemma muln0 : right_zero 0 muln.
Admitted.
Lemma mul1n : left_id 1 muln.
Admitted.
Lemma mulSn m n : m.+1 * n = n + m * n.
Admitted.
Lemma mulSnr m n : m.+1 * n = m * n + n.
Admitted.

Lemma mulnS m n : m * n.+1 = m + m * n.
Admitted.
Lemma mulnSr m n : m * n.+1 = m * n + m.
Admitted.

Lemma iter_addn m n p : iter n (addn m) p = m * n + p.
Admitted.

Lemma iter_addn_0 m n : iter n (addn m) 0 = m * n.
Admitted.

Lemma muln1 : right_id 1 muln.
Admitted.

Lemma mulnC : commutative muln.
Admitted.

Lemma mulnDl : left_distributive muln addn.
Admitted.

Lemma mulnDr : right_distributive muln addn.
Admitted.

Lemma mulnBl : left_distributive muln subn.
Admitted.

Lemma mulnBr : right_distributive muln subn.
Admitted.

Lemma mulnA : associative muln.
Admitted.

Lemma mulnCA : left_commutative muln.
Admitted.

Lemma mulnAC : right_commutative muln.
Admitted.

Lemma mulnACA : interchange muln muln.
Admitted.

Lemma muln_eq0 m n : (m * n == 0) = (m == 0) || (n == 0).
Admitted.

Lemma muln_eq1 m n : (m * n == 1) = (m == 1) && (n == 1).
Admitted.

Lemma muln_gt0 m n : (0 < m * n) = (0 < m) && (0 < n).
Admitted.

Lemma leq_pmull m n : n > 0 -> m <= n * m.
Admitted.

Lemma leq_pmulr m n : n > 0 -> m <= m * n.
Admitted.

Lemma leq_mul2l m n1 n2 : (m * n1 <= m * n2) = (m == 0) || (n1 <= n2).
Admitted.

Lemma leq_mul2r m n1 n2 : (n1 * m <= n2 * m) = (m == 0) || (n1 <= n2).
Admitted.

Lemma leq_mul m1 m2 n1 n2 : m1 <= n1 -> m2 <= n2 -> m1 * m2 <= n1 * n2.
Admitted.

Lemma eqn_mul2l m n1 n2 : (m * n1 == m * n2) = (m == 0) || (n1 == n2).
Admitted.

Lemma eqn_mul2r m n1 n2 : (n1 * m == n2 * m) = (m == 0) || (n1 == n2).
Admitted.

Lemma leq_pmul2l m n1 n2 : 0 < m -> (m * n1 <= m * n2) = (n1 <= n2).
Admitted.
Arguments leq_pmul2l [m n1 n2].

Lemma leq_pmul2r m n1 n2 : 0 < m -> (n1 * m <= n2 * m) = (n1 <= n2).
Admitted.
Arguments leq_pmul2r [m n1 n2].

Lemma eqn_pmul2l m n1 n2 : 0 < m -> (m * n1 == m * n2) = (n1 == n2).
Admitted.
Arguments eqn_pmul2l [m n1 n2].

Lemma eqn_pmul2r m n1 n2 : 0 < m -> (n1 * m == n2 * m) = (n1 == n2).
Admitted.
Arguments eqn_pmul2r [m n1 n2].

Lemma ltn_mul2l m n1 n2 : (m * n1 < m * n2) = (0 < m) && (n1 < n2).
Admitted.

Lemma ltn_mul2r m n1 n2 : (n1 * m < n2 * m) = (0 < m) && (n1 < n2).
Admitted.

Lemma ltn_pmul2l m n1 n2 : 0 < m -> (m * n1 < m * n2) = (n1 < n2).
Admitted.
Arguments ltn_pmul2l [m n1 n2].

Lemma ltn_pmul2r m n1 n2 : 0 < m -> (n1 * m < n2 * m) = (n1 < n2).
Admitted.
Arguments ltn_pmul2r [m n1 n2].

Lemma ltn_Pmull m n : 1 < n -> 0 < m -> m < n * m.
Admitted.

Lemma ltn_Pmulr m n : 1 < n -> 0 < m -> m < m * n.
Admitted.

Lemma ltn_mul m1 m2 n1 n2 : m1 < n1 -> m2 < n2 -> m1 * m2 < n1 * n2.
Admitted.

Lemma maxnMr : right_distributive muln maxn.
Admitted.

Lemma maxnMl : left_distributive muln maxn.
Admitted.

Lemma minnMr : right_distributive muln minn.
Admitted.

Lemma minnMl : left_distributive muln minn.
Admitted.

Lemma iterM (T : Type) (n m : nat) (f : T -> T) :
  iter (n * m) f =1 iter n (iter m f).
Admitted.

 

Definition expn_rec m n := iterop n muln m 1.
Notation "m ^ n" := (expn_rec m n) : nat_rec_scope.
Definition expn := nosimpl expn_rec.
Notation "m ^ n" := (expn m n) : nat_scope.

Lemma expnE : expn = expn_rec.
Admitted.

Lemma expn0 m : m ^ 0 = 1.
Admitted.
Lemma expn1 m : m ^ 1 = m.
Admitted.
Lemma expnS m n : m ^ n.+1 = m * m ^ n.
Admitted.
Lemma expnSr m n : m ^ n.+1 = m ^ n * m.
Admitted.

Lemma iter_muln m n p : iter n (muln m) p = m ^ n * p.
Admitted.

Lemma iter_muln_1 m n : iter n (muln m) 1 = m ^ n.
Admitted.

Lemma exp0n n : 0 < n -> 0 ^ n = 0.
Admitted.

Lemma exp1n n : 1 ^ n = 1.
Admitted.

Lemma expnD m n1 n2 : m ^ (n1 + n2) = m ^ n1 * m ^ n2.
Admitted.

Lemma expnMn m1 m2 n : (m1 * m2) ^ n = m1 ^ n * m2 ^ n.
Admitted.

Lemma expnM m n1 n2 : m ^ (n1 * n2) = (m ^ n1) ^ n2.
Admitted.

Lemma expnAC m n1 n2 : (m ^ n1) ^ n2 = (m ^ n2) ^ n1.
Admitted.

Lemma expn_gt0 m n : (0 < m ^ n) = (0 < m) || (n == 0).
Admitted.

Lemma expn_eq0 m e : (m ^ e == 0) = (m == 0) && (e > 0).
Admitted.

Lemma ltn_expl m n : 1 < m -> n < m ^ n.
Admitted.

Lemma leq_exp2l m n1 n2 : 1 < m -> (m ^ n1 <= m ^ n2) = (n1 <= n2).
Admitted.

Lemma ltn_exp2l m n1 n2 : 1 < m -> (m ^ n1 < m ^ n2) = (n1 < n2).
Admitted.

Lemma eqn_exp2l m n1 n2 : 1 < m -> (m ^ n1 == m ^ n2) = (n1 == n2).
Admitted.

Lemma expnI m : 1 < m -> injective (expn m).
Admitted.

Lemma leq_pexp2l m n1 n2 : 0 < m -> n1 <= n2 -> m ^ n1 <= m ^ n2.
Admitted.

Lemma ltn_pexp2l m n1 n2 : 0 < m -> m ^ n1 < m ^ n2 -> n1 < n2.
Admitted.

Lemma ltn_exp2r m n e : e > 0 -> (m ^ e < n ^ e) = (m < n).
Admitted.

Lemma leq_exp2r m n e : e > 0 -> (m ^ e <= n ^ e) = (m <= n).
Admitted.

Lemma eqn_exp2r m n e : e > 0 -> (m ^ e == n ^ e) = (m == n).
Admitted.

Lemma expIn e : e > 0 -> injective (expn^~ e).
Admitted.

Lemma iterX (T : Type) (n m : nat) (f : T -> T) :
  iter (n ^ m) f =1 iter m (iter n) f.
Admitted.

 

Fixpoint fact_rec n := if n is n'.+1 then n * fact_rec n' else 1.

Definition factorial := nosimpl fact_rec.

Notation "n `!" := (factorial n) (at level 2, format "n `!") : nat_scope.

Lemma factE : factorial = fact_rec.
Admitted.

Lemma fact0 : 0`! = 1.
Admitted.

Lemma factS n : (n.+1)`!  = n.+1 * n`!.
Admitted.

Lemma fact_gt0 n : n`! > 0.
Admitted.

Lemma fact_geq n : n <= n`!.
Admitted.

Lemma ltn_fact m n : 0 < m -> m < n -> m`! < n`!.
Admitted.

 

Coercion nat_of_bool (b : bool) := if b then 1 else 0.

Lemma leq_b1 (b : bool) : b <= 1.
Admitted.

Lemma addn_negb (b : bool) : ~~ b + b = 1.
Admitted.

Lemma eqb0 (b : bool) : (b == 0 :> nat) = ~~ b.
Admitted.

Lemma eqb1 (b : bool) : (b == 1 :> nat) = b.
Admitted.

Lemma lt0b (b : bool) : (b > 0) = b.
Admitted.

Lemma sub1b (b : bool) : 1 - b = ~~ b.
Admitted.

Lemma mulnb (b1 b2 : bool) : b1 * b2 = b1 && b2.
Admitted.

Lemma mulnbl (b : bool) n : b * n = (if b then n else 0).
Admitted.

Lemma mulnbr (b : bool) n : n * b = (if b then n else 0).
Admitted.

Fixpoint odd n := if n is n'.+1 then ~~ odd n' else false.

Lemma oddS n : odd n.+1 = ~~ odd n.
Admitted.

Lemma oddb (b : bool) : odd b = b.
Admitted.

Lemma oddD m n : odd (m + n) = odd m (+) odd n.
Admitted.

Lemma oddB m n : n <= m -> odd (m - n) = odd m (+) odd n.
Admitted.

Lemma oddN i m : odd m = false -> i <= m -> odd (m - i) = odd i.
Admitted.

Lemma oddM m n : odd (m * n) = odd m && odd n.
Admitted.

Lemma oddX m n : odd (m ^ n) = (n == 0) || odd m.
Admitted.

 

Fixpoint double_rec n := if n is n'.+1 then n'.*2%Nrec.+2 else 0
where "n .*2" := (double_rec n) : nat_rec_scope.

Definition double := nosimpl double_rec.
Notation "n .*2" := (double n) : nat_scope.

Lemma doubleE : double = double_rec.
Admitted.

Lemma double0 : 0.*2 = 0.
Admitted.

Lemma doubleS n : n.+1.*2 = n.*2.+2.
Admitted.

Lemma double_pred n : n.-1.*2 = n.*2.-2.
Admitted.

Lemma addnn n : n + n = n.*2.
Admitted.

Lemma mul2n m : 2 * m = m.*2.
Admitted.

Lemma muln2 m : m * 2 = m.*2.
Admitted.

Lemma doubleD m n : (m + n).*2 = m.*2 + n.*2.
Admitted.

Lemma doubleB m n : (m - n).*2 = m.*2 - n.*2.
Admitted.

Lemma leq_double m n : (m.*2 <= n.*2) = (m <= n).
Admitted.

Lemma ltn_double m n : (m.*2 < n.*2) = (m < n).
Admitted.

Lemma ltn_Sdouble m n : (m.*2.+1 < n.*2) = (m < n).
Admitted.

Lemma leq_Sdouble m n : (m.*2 <= n.*2.+1) = (m <= n).
Admitted.

Lemma odd_double n : odd n.*2 = false.
Admitted.

Lemma double_gt0 n : (0 < n.*2) = (0 < n).
Admitted.

Lemma double_eq0 n : (n.*2 == 0) = (n == 0).
Admitted.

Lemma doubleMl m n : (m * n).*2 = m.*2 * n.
Admitted.

Lemma doubleMr m n : (m * n).*2 = m * n.*2.
Admitted.

 

Fixpoint half (n : nat) : nat := if n is n'.+1 then uphalf n' else n
with   uphalf (n : nat) : nat := if n is n'.+1 then n'./2.+1 else n
where "n ./2" := (half n) : nat_scope.

Lemma uphalfE n : uphalf n = n.+1./2.
Admitted.

Lemma doubleK : cancel double half.
Admitted.

Definition half_double := doubleK.
Definition double_inj := can_inj doubleK.

Lemma uphalf_double n : uphalf n.*2 = n.
Admitted.

Lemma uphalf_half n : uphalf n = odd n + n./2.
Admitted.

Lemma odd_double_half n : odd n + n./2.*2 = n.
Admitted.

Lemma halfK n : n./2.*2 = n - odd n.
Admitted.

Lemma uphalfK n : (uphalf n).*2 = odd n + n.
Admitted.

Lemma odd_halfK n : odd n -> n./2.*2 = n.-1.
Admitted.

Lemma even_halfK n : ~~ odd n -> n./2.*2 = n.
Admitted.

Lemma odd_uphalfK n : odd n -> (uphalf n).*2 = n.+1.
Admitted.

Lemma even_uphalfK n : ~~ odd n -> (uphalf n).*2 = n.
Admitted.

Lemma half_bit_double n (b : bool) : (b + n.*2)./2 = n.
Admitted.

Lemma halfD m n : (m + n)./2 = (odd m && odd n) + (m./2 + n./2).
Admitted.

Lemma half_leq m n : m <= n -> m./2 <= n./2.
Admitted.

Lemma geq_half_double m n : (m <= n./2) = (m.*2 <= n).
Admitted.

Lemma ltn_half_double m n : (m./2 < n) = (m < n.*2).
Admitted.

Lemma leq_half_double m n : (m./2 <= n) = (m <= n.*2.+1).
Admitted.

Lemma gtn_half_double m n : (n < m./2) = (n.*2.+1 < m).
Admitted.

Lemma half_gt0 n : (0 < n./2) = (1 < n).
Admitted.

Lemma uphalf_leq m n : m <= n -> uphalf m <= uphalf n.
Admitted.

Lemma leq_uphalf_double m n : (uphalf m <= n) = (m <= n.*2).
Admitted.

Lemma geq_uphalf_double m n : (m <= uphalf n) = (m.*2 <= n.+1).
Admitted.

Lemma gtn_uphalf_double m n : (n < uphalf m) = (n.*2 < m).
Admitted.

Lemma ltn_uphalf_double m n : (uphalf m < n) = (m.+1 < n.*2).
Admitted.

Lemma uphalf_gt0 n : (0 < uphalf n) = (0 < n).
Admitted.

Lemma odd_geq m n : odd n -> (m <= n) = (m./2.*2 <= n).
Admitted.

Lemma odd_ltn m n : odd n -> (n < m) = (n < m./2.*2).
Admitted.

Lemma odd_gt0 n : odd n -> n > 0.
Admitted.

Lemma odd_gt2 n : odd n -> n > 1 -> n > 2.
Admitted.

 

Lemma mulnn m : m * m = m ^ 2.
Admitted.

Lemma sqrnD m n : (m + n) ^ 2 = m ^ 2 + n ^ 2 + 2 * (m * n).
Admitted.

Lemma sqrnB m n : n <= m -> (m - n) ^ 2 = m ^ 2 + n ^ 2 - 2 * (m * n).
Admitted.

Lemma sqrnD_sub m n : n <= m -> (m + n) ^ 2 - 4 * (m * n) = (m - n) ^ 2.
Admitted.

Lemma subn_sqr m n : m ^ 2 - n ^ 2 = (m - n) * (m + n).
Admitted.

Lemma ltn_sqr m n : (m ^ 2 < n ^ 2) = (m < n).
Admitted.

Lemma leq_sqr m n : (m ^ 2 <= n ^ 2) = (m <= n).
Admitted.

Lemma sqrn_gt0 n : (0 < n ^ 2) = (0 < n).
Admitted.

Lemma eqn_sqr m n : (m ^ 2 == n ^ 2) = (m == n).
Admitted.

Lemma sqrn_inj : injective (expn ^~ 2).
Admitted.

 
 
 
 
 
 
 
 
 

Definition leqif m n C := ((m <= n) * ((m == n) = C))%type.

Notation "m <= n ?= 'iff' C" := (leqif m n C) : nat_scope.

Coercion leq_of_leqif m n C (H : m <= n ?= iff C) := H.1 : m <= n.

Lemma leqifP m n C : reflect (m <= n ?= iff C) (if C then m == n else m < n).
Admitted.

Lemma leqif_refl m C : reflect (m <= m ?= iff C) C.
Admitted.

Lemma leqif_trans m1 m2 m3 C12 C23 :
  m1 <= m2 ?= iff C12 -> m2 <= m3 ?= iff C23 -> m1 <= m3 ?= iff C12 && C23.
Admitted.

Lemma mono_leqif f : {mono f : m n / m <= n} ->
  forall m n C, (f m <= f n ?= iff C) = (m <= n ?= iff C).
Admitted.

Lemma leqif_geq m n : m <= n -> m <= n ?= iff (m >= n).
Admitted.

Lemma leqif_eq m n : m <= n -> m <= n ?= iff (m == n).
Admitted.

Lemma geq_leqif a b C : a <= b ?= iff C -> (b <= a) = C.
Admitted.

Lemma ltn_leqif a b C : a <= b ?= iff C -> (a < b) = ~~ C.
Admitted.

Lemma ltnNleqif x y C : x <= y ?= iff ~~ C -> (x < y) = C.
Admitted.

Lemma eq_leqif x y C : x <= y ?= iff C -> (x == y) = C.
Admitted.

Lemma eqTleqif x y C : x <= y ?= iff C -> C -> x = y.
Admitted.

Lemma leqif_add m1 n1 C1 m2 n2 C2 :
    m1 <= n1 ?= iff C1 -> m2 <= n2 ?= iff C2 ->
  m1 + m2 <= n1 + n2 ?= iff C1 && C2.
Admitted.

Lemma leqif_mul m1 n1 C1 m2 n2 C2 :
    m1 <= n1 ?= iff C1 -> m2 <= n2 ?= iff C2 ->
  m1 * m2 <= n1 * n2 ?= iff (n1 * n2 == 0) || (C1 && C2).
Admitted.

Lemma nat_Cauchy m n : 2 * (m * n) <= m ^ 2 + n ^ 2 ?= iff (m == n).
Admitted.

Lemma nat_AGM2 m n : 4 * (m * n) <= (m + n) ^ 2 ?= iff (m == n).
Admitted.

Section ContraLeq.
Implicit Types (b : bool) (m n : nat) (P : Prop).

Lemma contraTleq b m n : (n < m -> ~~ b) -> (b -> m <= n).
Admitted.

Lemma contraTltn b m n : (n <= m -> ~~ b) -> (b -> m < n).
Admitted.

Lemma contraPleq P m n : (n < m -> ~ P) -> (P -> m <= n).
Admitted.

Lemma contraPltn P m n : (n <= m -> ~ P) -> (P -> m < n).
Admitted.

Lemma contraNleq b m n : (n < m -> b) -> (~~ b -> m <= n).
Admitted.

Lemma contraNltn b m n : (n <= m -> b) -> (~~ b -> m < n).
Admitted.

Lemma contra_not_leq P m n : (n < m -> P) -> (~ P -> m <= n).
Admitted.

Lemma contra_not_ltn P m n : (n <= m -> P) -> (~ P -> m < n).
Admitted.

Lemma contraFleq b m n : (n < m -> b) -> (b = false -> m <= n).
Admitted.

Lemma contraFltn b m n : (n <= m -> b) -> (b = false -> m < n).
Admitted.

Lemma contra_leqT b m n : (~~ b -> m < n) -> (n <= m -> b).
Admitted.

Lemma contra_ltnT b m n : (~~ b -> m <= n) -> (n < m -> b).
Admitted.

Lemma contra_leqN b m n : (b -> m < n) -> (n <= m -> ~~ b).
Admitted.

Lemma contra_ltnN b m n : (b -> m <= n) -> (n < m -> ~~ b).
Admitted.

Lemma contra_leq_not P m n : (P -> m < n) -> (n <= m -> ~ P).
Admitted.

Lemma contra_ltn_not P m n : (P -> m <= n) -> (n < m -> ~ P).
Admitted.

Lemma contra_leqF b m n : (b -> m < n) -> (n <= m -> b = false).
Admitted.

Lemma contra_ltnF b m n : (b -> m <= n) -> (n < m -> b = false).
Admitted.

Lemma contra_leq m n p q : (q < p -> n < m) -> (m <= n -> p <= q).
Admitted.

Lemma contra_leq_ltn m n p q : (q <= p -> n < m) -> (m <= n -> p < q).
Admitted.

Lemma contra_ltn_leq m n p q : (q < p -> n <= m) -> (m < n -> p <= q).
Admitted.

Lemma contra_ltn m n p q : (q <= p -> n <= m) -> (m < n -> p < q).
Admitted.

End ContraLeq.

Section Monotonicity.
Variable T : Type.

Lemma homo_ltn_in (D : {pred nat}) (f : nat -> T) (r : T -> T -> Prop) :
  (forall y x z, r x y -> r y z -> r x z) ->
  {in D &, forall i j k, i < k < j -> k \in D} ->
  {in D, forall i, i.+1 \in D -> r (f i) (f i.+1)} ->
  {in D &, {homo f : i j / i < j >-> r i j}}.
Admitted.

Lemma homo_ltn (f : nat -> T) (r : T -> T -> Prop) :
  (forall y x z, r x y -> r y z -> r x z) ->
  (forall i, r (f i) (f i.+1)) -> {homo f : i j / i < j >-> r i j}.
Admitted.

Section NatToNat.

End NatToNat.
End Monotonicity.

Section NumberInterpretation.

Section Trec.

End Trec.

End NumberInterpretation.
Module Export mathcomp_DOT_ssreflect_DOT_seq_WRAPPED.
Module Export seq.

Import HB.structures.
Import mathcomp.ssreflect.ssreflect.
Import mathcomp.ssreflect.ssrfun.
Import mathcomp.ssreflect.ssrbool.
Import mathcomp.ssreflect.eqtype.

Set Implicit Arguments.
Unset Strict Implicit.

Declare Scope seq_scope.
Open Scope seq_scope.

Notation seq := list.
Notation Nil T := (@nil T) (only parsing).

Infix "::" := cons : seq_scope.

Notation "[ :: ]" := nil (at level 0, format "[ :: ]") : seq_scope.

Notation "[ :: x1 ]" := (x1 :: [::])
  (at level 0, format "[ ::  x1 ]") : seq_scope.

Notation "[ :: x1 ; x2 ; .. ; xn ]" := (x1 :: x2 :: .. [:: xn] ..)
  (at level 0, format "[ :: '['  x1 ; '/'  x2 ; '/'  .. ; '/'  xn ']' ]"
  ) : seq_scope.

Section Sequences.

Variable T : Type.

Variable x0 : T.
Implicit Type s : seq T.

Fixpoint size s := if s is _ :: s' then (size s').+1 else 0.
Definition head s := if s is x :: _ then x else x0.

Fixpoint cat s1 s2 := if s1 is x :: s1' then x :: s1' ++ s2 else s2
where "s1 ++ s2" := (cat s1 s2) : seq_scope.

Section SeqFind.

Variable a : pred T.

Fixpoint filter s :=
  if s is x :: s' then if a x then x :: filter s' else filter s' else [::].

Fixpoint count s := if s is x :: s' then a x + count s' else 0.

Fixpoint all s := if s is x :: s' then a x && all s' else true.

End SeqFind.

Fixpoint drop n s {struct s} :=
  match s, n with
  | _ :: s', n'.+1 => drop n' s'
  | _, _ => s
  end.

Fixpoint take n s {struct s} :=
  match s, n with
  | x :: s', n'.+1 => x :: take n' s'
  | _, _ => [::]
  end.

Definition rot n s := drop n s ++ take n s.

Definition rotr n s := rot (size s - n) s.

Fixpoint catrev s1 s2 := if s1 is x :: s1' then catrev s1' (x :: s2) else s2.

End Sequences.
Prenex Implicits cat take drop rot rotr catrev.

Notation count_mem x := (count (pred_of_simpl (pred1 x))).

Section EqSeq.

Variables (n0 : nat) (T : eqType) (x0 : T).
Implicit Types (x y z : T) (s : seq T).

Fixpoint eqseq s1 s2 {struct s2} :=
  match s1, s2 with
  | [::], [::] => true
  | x1 :: s1', x2 :: s2' => (x1 == x2) && eqseq s1' s2'
  | _, _ => false
  end.

Lemma eqseqP : Equality.axiom eqseq.
admit.
Defined.

HB.instance Definition _ := hasDecEq.Build (seq T) eqseqP.

Fixpoint mem_seq (s : seq T) :=
  if s is y :: s' then xpredU1 y (mem_seq s') else xpred0.

Definition seq_eqclass := seq T.
Coercion pred_of_seq (s : seq_eqclass) : {pred T}.
exact (mem_seq s).
Defined.

Canonical seq_predType := PredType (pred_of_seq : seq T -> pred T).

Lemma in_cons y s x : (x \in y :: s) = (x == y) || (x \in s).
admit.
Defined.

Lemma mem_seq1 x y : (x \in [:: y]) = (x == y).
admit.
Defined.

Fixpoint uniq s := if s is x :: s' then (x \notin s') && uniq s' else true.

Fixpoint undup s :=
  if s is x :: s' then if x \in s' then undup s' else x :: undup s' else [::].

End EqSeq.

Definition inE := (mem_seq1, in_cons, inE).

Section Map.

Variables (n0 : nat) (T1 : Type) (x1 : T1).
Variables (T2 : Type) (x2 : T2) (f : T1 -> T2).

Fixpoint map s := if s is x :: s' then f x :: map s' else [::].

End Map.

Notation "[ 'seq' E | i <- s ]" := (map (fun i => E) s)
  (at level 0, E at level 99, i binder,
   format "[ '[hv' 'seq'  E '/ '  |  i  <-  s ] ']'") : seq_scope.

Section Pmap.

Variables (aT rT : Type) (f : aT -> option rT) (g : rT -> aT).

Fixpoint pmap s :=
  if s is x :: s' then let r := pmap s' in oapp (cons^~ r) r (f x) else [::].

End Pmap.

Fixpoint iota m n := if n is n'.+1 then m :: iota m.+1 n' else [::].

Lemma mem_iota m n i : (i \in iota m n) = (m <= i < m + n).
Admitted.

Section FoldRight.

Variables (T : Type) (R : Type) (f : T -> R -> R) (z0 : R).

Fixpoint foldr s := if s is x :: s' then f x (foldr s') else z0.

End FoldRight.

Section Zip.

Variables (S T : Type) (r : S -> T -> bool).

Definition unzip1 := map (@fst S T).

End Zip.

Section Flatten.

Variable T : Type.

Definition flatten := foldr cat (Nil T).

End Flatten.

Notation "[ 'seq' E | x <- s , y <- t ]" :=
  (flatten [seq [seq E | y <- t] | x <- s])
  (at level 0, E at level 99, x binder, y binder,
   format "[ '[hv' 'seq'  E '/ '  |  x  <-  s , '/   '  y  <-  t ] ']'")
   : seq_scope.

End seq.
Module Export mathcomp.
Module Export ssreflect.
Module Export seq.
Include mathcomp_DOT_ssreflect_DOT_seq_WRAPPED.seq.
End seq.

Import HB.structures.
Import mathcomp.ssreflect.ssreflect.
Import mathcomp.ssreflect.ssrfun.
Import mathcomp.ssreflect.ssrbool.
Import mathcomp.ssreflect.eqtype.
Import mathcomp.ssreflect.seq.

Set Implicit Arguments.

Module Export CodeSeq.

Definition code := foldr (fun n m => 2 ^ n * m.*2.+1) 0.

Fixpoint decode_rec (v q r : nat) {struct q} :=
  match q, r with
  | 0, _         => [:: v]
  | q'.+1, 0     => v :: [rec 0, q', q']
  | q'.+1, 1     => [rec v.+1, q', q']
  | q'.+1, r'.+2 => [rec v, q', r']
  end where "[ 'rec' v , q , r ]" := (decode_rec v q r).

Definition decode n := if n is 0 then [::] else [rec 0, n.-1, n.-1].

Section OtherEncodings.

Variables T T1 T2 : Type.

Definition tag_of_pair (p : T1 * T2) := @Tagged T1 p.1 (fun _ => T2) p.2.
Definition pair_of_tag (u : {i : T1 & T2}) := (tag u, tagged u).
Lemma tag_of_pairK : cancel tag_of_pair pair_of_tag.
admit.
Defined.

End OtherEncodings.

HB.mixin Record hasChoice T := Mixin {
  find_subdef : pred T -> nat -> option T;
  choice_correct_subdef {P n x} : find_subdef P n = Some x -> P x;
  choice_complete_subdef {P : pred T} :
    (exists x, P x) -> exists n, find_subdef P n;
  choice_extensional_subdef {P Q : pred T} :
    P =1 Q -> find_subdef P =1 find_subdef Q
}.

#[short(type="choiceType")]
HB.structure Definition Choice := { T of hasChoice T & hasDecEq T}.

Section ChoiceTheory.

Section OneType.

Variable T : choiceType.

Section CanChoice.

Variables (sT : Type) (f : sT -> T).

Lemma PCanHasChoice f' : pcancel f f' -> hasChoice sT.
Admitted.

HB.instance Definition _ f' (fK : pcancel f f') : hasChoice (pcan_type fK) :=
  PCanHasChoice fK.
HB.instance Definition _ f' (fK : cancel f f') : hasChoice (can_type fK) :=
  PCanHasChoice (can_pcan fK).

End CanChoice.

Fact seq_hasChoice : hasChoice (seq T).
Admitted.
HB.instance Definition _ := seq_hasChoice.

End OneType.

Section TagChoice.

Variables (I : choiceType) (T_ : I -> choiceType).

Fact tagged_hasChoice : hasChoice {i : I & T_ i}.
Admitted.
HB.instance Definition _ := tagged_hasChoice.

End TagChoice.

Fact nat_hasChoice : hasChoice nat.
Admitted.
HB.instance Definition _ := nat_hasChoice.

End ChoiceTheory.

HB.mixin Record Choice_isCountable (T : Type) : Type := {
    pickle : T -> nat;
    unpickle : nat -> option T;
    pickleK : pcancel pickle unpickle
}.

#[short(type="countType")]
HB.structure Definition Countable := { T of Choice T & Choice_isCountable T }.

HB.factory Record isCountable (T : Type) : Type := {
  pickle : T -> nat;
  unpickle : nat -> option T;
  pickleK : pcancel pickle unpickle
}.
HB.builders Context T of isCountable T.
  HB.instance Definition _ := Choice_isCountable.Build T pickleK.
HB.end.

Section CountableTheory.

Variable T : countType.

Lemma pcan_pickleK sT f f' :
  @pcancel T sT f f' -> pcancel (pickle \o f) (pcomp f' unpickle).
Admitted.

Definition PCanIsCountable sT (f : sT -> T) f' (fK : pcancel f f') :=
  isCountable.Build sT (pcan_pickleK fK).

Definition CanIsCountable sT f f' (fK : cancel f f') :=
  @PCanIsCountable sT _ _ (can_pcan fK).

HB.instance Definition _ sT (f : sT -> T) f' (fK : pcancel f f') :
  isCountable (pcan_type fK) := PCanIsCountable fK.
HB.instance Definition _ sT (f : sT -> T) f' (fK : cancel f f') :
  isCountable (can_type fK) := CanIsCountable fK.

#[hnf] HB.instance Definition _ (P : pred T) (sT : subType P) :=
  Countable.copy (sub_type sT) (pcan_type valK).

Definition pickle_seq s := CodeSeq.code (map (@pickle T) s).
Definition unpickle_seq n := Some (pmap (@unpickle T) (CodeSeq.decode n)).
Lemma pickle_seqK : pcancel pickle_seq unpickle_seq.
Admitted.

HB.instance Definition _ := isCountable.Build (seq T) pickle_seqK.

End CountableTheory.

Notation "[ 'Countable' 'of' T 'by' <: ]" :=
    (Countable.copy T%type (sub_type T%type))
  (at level 0, format "[ 'Countable'  'of'  T  'by'  <: ]") : form_scope.

#[short(type="subCountType")]
HB.structure Definition SubCountable T (P : pred T) :=
  { sT of Countable sT & isSub T P sT}.

Section TagCountType.

Variables (I : countType) (T_ : I -> countType).

Definition pickle_tagged (u : {i : I & T_ i}) :=
  CodeSeq.code [:: pickle (tag u); pickle (tagged u)].
Definition unpickle_tagged s :=
  if CodeSeq.decode s is [:: ni; nx] then
    obind (fun i => omap (@Tagged I i T_) (unpickle nx)) (unpickle ni)
  else None.
Lemma pickle_taggedK : pcancel pickle_tagged unpickle_tagged.
Admitted.

HB.instance Definition _ :=
  Choice_isCountable.Build {i : I & T_ i} pickle_taggedK.

End TagCountType.

Section CountableDataTypes.

Implicit Type T : countType.

Lemma nat_pickleK : pcancel id (@Some nat).
Admitted.
HB.instance Definition _ := Choice_isCountable.Build nat nat_pickleK.

HB.instance Definition _ := Countable.copy bool (can_type oddb).

HB.instance Definition _ T1 T2 :=
  Countable.copy (T1 * T2)%type (can_type (@tag_of_pairK T1 T2)).

End CountableDataTypes.

Definition edivn_rec d :=
  fix loop m q := if m - d is m'.+1 then loop m' q.+1 else (q, m).

Definition edivn m d := if d > 0 then edivn_rec d.-1 m 0 else (0, m).

Definition modn_rec d := fix loop m := if m - d is m'.+1 then loop m' else m.

Definition modn m d := if d > 0 then modn_rec d.-1 m else m.

Notation "m %% d" := (modn m d) : nat_scope.

Fixpoint gcdn_rec m n :=
  let n' := n %% m in if n' is 0 then m else
  if m - n'.-1 is m'.+1 then gcdn_rec (m' %% n') n' else n'.

Definition gcdn := nosimpl gcdn_rec.

Definition coprime m n := gcdn m n == 1.
Unset Strict Implicit.

Definition finite_axiom (T : eqType) e :=
  forall x : T, count_mem x e = 1.

HB.mixin Record isFinite T of Equality T := {
  enum_subdef : seq T;
  enumP_subdef : finite_axiom enum_subdef
}.

#[short(type="finType")]
HB.structure Definition Finite := {T of isFinite T & Countable T }.

Module Export FiniteNES.
Module Export Finite.

HB.lock Definition enum T := isFinite.enum_subdef (Finite.class T).

Notation axiom := finite_axiom.

Lemma uniq_enumP (T : eqType) e : uniq e -> e =i T -> axiom e.
Admitted.

End Finite.

Definition fin_pred_sort (T : finType) (pT : predType T) := pred_sort pT.
Identity Coercion pred_sort_of_fin : fin_pred_sort >-> pred_sort.

Definition enum_mem T (mA : mem_pred _) := filter mA (Finite.enum T).
Notation enum A := (enum_mem (mem A)).

HB.lock Definition card (T : finType) (mA : mem_pred T) := size (enum_mem mA).

Notation "#| A |" := (card (mem A))
  (at level 0, A at level 99, format "#| A |") : nat_scope.

Definition pred0b (T : finType) (P : pred T) := #|P| == 0.

Module FiniteQuant.

Variant quantified := Quantified of bool.

Bind Scope fin_quant_scope with quantified.

Notation "F ^*" := (Quantified F) (at level 2).
Notation "F ^~" := (~~ F) (at level 2).

Section Definitions.

Variable T : finType.
Implicit Types (B : quantified) (x y : T).

Definition quant0b Bp := pred0b [pred x : T | let: F^* := Bp x x in F].
Definition all_in C B x y := let: F^* := B in (C ==> F)^~^*.
Definition ex_in C B x y :=  let: F^* := B in (C && F)^*.

End Definitions.
Notation "[ x : T | B ]" := (quant0b (fun x : T => B x)) (at level 0, x name).

Module Export Exports.

Notation ", F" := F^* (at level 200, format ", '/ '  F") : fin_quant_scope.
Notation "[ 'forall' ( x : T | C ) B ]" := [x : T | all_in C B]
  (at level 0, x at level 99, B at level 200, only parsing) : bool_scope.
Notation "[ 'exists' ( x : T | C ) B ]" := [x : T | ex_in C B]^~
  (at level 0, x at level 99, B at level 200, only parsing) : bool_scope.

End Exports.

End FiniteQuant.
Export FiniteQuant.Exports.

HB.lock
Definition subset (T : finType) (A B : mem_pred T) : bool := pred0b (predD A B).

Notation "A \subset B" := (subset (mem A) (mem B))
  (at level 70, no associativity) : bool_scope.

Definition proper T A B := @subset T A B && ~~ subset B A.
Notation "A \proper B" := (proper (mem A) (mem B))
  (at level 70, no associativity) : bool_scope.

Section OpsTheory.

Variable T : finType.

Implicit Types (A B C D : {pred T}) (P Q : pred T) (x y : T) (s : seq T).

Section EnumPick.

Lemma mem_enum A : enum A =i A.
Admitted.

End EnumPick.

End OpsTheory.

Definition image_mem T T' f mA : seq T' := map f (@enum_mem T mA).

Definition codom T T' f := @image_mem T T' f (mem T).

Lemma bool_enumP : Finite.axiom [:: true; false].
Admitted.
HB.instance Definition _ := isFinite.Build bool bool_enumP.

Local Notation enumF T := (Finite.enum T).

Section TransferFinTypeFromCount.

Variables (eT : countType) (fT : finType) (f : eT -> fT).

Lemma pcan_enumP g : pcancel f g -> Finite.axiom (undup (pmap g (enumF fT))).
Admitted.

End TransferFinTypeFromCount.

Section TransferFinType.

Variables (eT : Type) (fT : finType) (f : eT -> fT).

HB.instance Definition _ (g : fT -> option eT) (fK : pcancel f g) :=
  isFinite.Build (pcan_type fK) (@pcan_enumP (pcan_type fK) fT f g fK).

End TransferFinType.

HB.factory Record SubCountable_isFinite (T : finType) P (sT : Type)
  of SubCountable T P sT := { }.

HB.builders Context (T : finType) (P : pred T) (sT : Type)
  (a : SubCountable_isFinite T P sT).
Definition sub_enum : seq sT.
Admitted.

Lemma mem_sub_enum u : u \in sub_enum.
Admitted.

Lemma sub_enum_uniq : uniq sub_enum.
Admitted.

HB.instance Definition SubFinMixin := isFinite.Build sT
  (Finite.uniq_enumP sub_enum_uniq mem_sub_enum).
HB.end.

HB.instance Definition _ (T : finType) (P : pred T) (sT : subType P) :=
  (SubCountable_isFinite.Build _ _ (sub_type sT)).

Notation "[ 'Finite' 'of' T 'by' <: ]" := (Finite.copy T%type (sub_type T%type))
  (at level 0, format "[ 'Finite'  'of'  T  'by'  <: ]") : form_scope.

Section ProdFinType.

Variable T1 T2 : finType.

Definition prod_enum := [seq (x1, x2) | x1 <- enum T1, x2 <- enum T2].

Lemma prod_enumP : Finite.axiom prod_enum.
Admitted.

HB.instance Definition _ := isFinite.Build (T1 * T2)%type prod_enumP.

End ProdFinType.

Section TagFinType.

Variables (I : finType) (T_ : I -> finType).

Definition tag_enum :=
  flatten [seq [seq Tagged T_ x | x <- enumF (T_ i)] | i <- enumF I].

Lemma tag_enumP : Finite.axiom tag_enum.
Admitted.

HB.instance Definition _ := isFinite.Build {i : I & T_ i} tag_enumP.

End TagFinType.

Section TupleDef.

Variables (n : nat) (T : Type).

Structure tuple_of : Type := Tuple {tval :> seq T; _ : size tval == n}.

HB.instance Definition _ := [isSub for tval].

Definition tuple t mkT : tuple_of :=
  mkT (let: Tuple _ tP := t return size t == n in tP).

End TupleDef.

Notation "n .-tuple" := (tuple_of n)
  (at level 2, format "n .-tuple") : type_scope.

Notation "[ 'tuple' 'of' s ]" := (tuple (fun sP => @Tuple _ _ s sP))
  (at level 0, format "[ 'tuple'  'of'  s ]") : form_scope.

Section SeqTuple.

Variables (n m : nat) (T U rT : Type).
Implicit Type t : n.-tuple T.

Lemma map_tupleP f t : @size rT (map f t) == n.
admit.
Defined.
Canonical map_tuple f t := Tuple (map_tupleP f t).

End SeqTuple.

HB.instance Definition _ n (T : countType) :=
  [Countable of n.-tuple T by <:].

Module Type FinTupleSig.
Section FinTupleSig.
Variables (n : nat) (T : finType).
Parameter enum : seq (n.-tuple T).
Axiom enumP : Finite.axiom enum.
End FinTupleSig.
End FinTupleSig.

Module FinTuple : FinTupleSig.
Section FinTuple.
Variables (n : nat) (T : finType).
Definition enum : seq (n.-tuple T).
Admitted.

Lemma enumP : Finite.axiom enum.
Admitted.

End FinTuple.
End FinTuple.

Section UseFinTuple.

Variables (n : nat) (T : finType).

HB.instance Definition _ := isFinite.Build (n.-tuple T) (@FinTuple.enumP n T).

Lemma enum_tupleP (A : {pred T}) : size (enum A) == #|A|.
admit.
Defined.
Canonical enum_tuple A := Tuple (enum_tupleP A).

Section ImageTuple.

Variables (T' : Type) (f : T -> T') (A : {pred T}).
Canonical codom_tuple : #|T|.-tuple T'.
exact ([tuple of codom f]).
Defined.

End ImageTuple.

End UseFinTuple.

Section Def.

Variables (aT : finType) (rT : aT -> Type).

Inductive finfun_on : seq aT -> Type :=
| finfun_nil                            : finfun_on [::]
| finfun_cons x s of rT x & finfun_on s : finfun_on (x :: s).
Local Fixpoint finfun_rec (g : forall x, rT x) s : finfun_on s.
Admitted.

Local Fixpoint fun_of_fin_rec x s (f_s : finfun_on s) : x \in s -> rT x :=
  if f_s is finfun_cons x1 s1 y1 f_s1 then
    if eqP is ReflectT Dx in reflect _ Dxb return Dxb || (x \in s1) -> rT x then
      fun=> ecast x (rT x) (esym Dx) y1
    else fun_of_fin_rec f_s1
  else fun isF =>  False_rect (rT x) (notF isF).

Variant finfun_of (ph : phant (forall x, rT x)) : predArgType :=
  FinfunOf of finfun_on (enum aT).

Definition dfinfun_of ph := finfun_of ph.

Definition fun_of_fin ph (f : finfun_of ph) x :=
  let: FinfunOf f_aT := f in fun_of_fin_rec f_aT (mem_enum aT x).

End Def.

Coercion fun_of_fin : finfun_of >-> Funclass.

Notation "{ 'ffun' fT }" := (finfun_of (Phant fT))
  (at level 0, format "{ 'ffun'  '[hv' fT ']' }") : type_scope.

Notation "{ 'dffun' fT }" := (dfinfun_of (Phant fT))
  (at level 0, format "{ 'dffun'  '[hv' fT ']' }") : type_scope.

Local Notation finPi aT rT := (forall x : Finite.sort aT, rT x) (only parsing).

HB.lock Definition finfun aT rT g :=
  FinfunOf (Phant (finPi aT rT)) (finfun_rec g (enum aT)).

Section DepPlainTheory.
Variables (aT : finType) (rT : aT -> Type).
Notation fT := {ffun finPi aT rT}.
Implicit Type f : fT.

Definition total_fun g x := Tagged rT (g x : rT x).

Definition tfgraph f := codom_tuple (total_fun f).
Local Definition tfgraph_inv (G : #|aT|.-tuple {x : aT & rT x}) : option fT.
Admitted.

Local Lemma tfgraphK : pcancel tfgraph tfgraph_inv.
Admitted.

End DepPlainTheory.
Arguments tfgraphK {aT rT} f : rename.

Section InheritedStructures.

Variable aT : finType.
Notation dffun_aT rT rS := {dffun forall x : aT, rT x : rS}.

#[hnf] HB.instance Definition _ rT := Finite.copy (dffun_aT rT finType)
  (pcan_type tfgraphK).
#[hnf] HB.instance Definition _ (rT : finType) :=
  Finite.copy {ffun aT -> rT} {dffun forall _, rT}.

End InheritedStructures.

Declare Scope big_scope.
Reserved Notation "\big [ op / idx ]_ ( i | P ) F"
  (at level 36, F at level 36, op, idx at level 10, i at level 50,
           format "'[' \big [ op / idx ]_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\big [ op / idx ]_ ( i : t | P ) F"
  (at level 36, F at level 36, op, idx at level 10, i at level 50,
           format "'[' \big [ op / idx ]_ ( i   :  t   |  P ) '/  '  F ']'").
Reserved Notation "\big [ op / idx ]_ ( i 'in' A ) F"
  (at level 36, F at level 36, op, idx at level 10, i, A at level 50,
           format "'[' \big [ op / idx ]_ ( i  'in'  A ) '/  '  F ']'").
Reserved Notation "\bigcup_ ( i : t | P ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \bigcup_ ( i   :  t   |  P ) '/  '  F ']'").
Reserved Notation "\bigcap_ ( i | P ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \bigcap_ ( i  |  P ) '/  '  F ']'").
Reserved Notation "\bigcap_ ( i : t | P ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \bigcap_ ( i   :  t   |  P ) '/  '  F ']'").
Reserved Notation "\bigcap_ ( i 'in' A ) F"
  (at level 41, F at level 41, i, A at level 50,
           format "'[' \bigcap_ ( i  'in'  A ) '/  '  F ']'").

Module Export SemiGroup.

HB.mixin Record isLaw T (op : T -> T -> T) := {
  opA : associative op;
}.

HB.factory Record isComLaw T (op : T -> T -> T) := {
  opA : associative op;
  opC : commutative op;
}.

HB.builders Context T op of isComLaw T op.

HB.instance Definition _ := isLaw.Build T op opA.

HB.end.

Module Import Exports.
End Exports.

End SemiGroup.

HB.factory Record isLaw T (idm : T) (op : T -> T -> T) := {
  opA : associative op;
  op1m : left_id idm op;
  opm1 : right_id idm op;
}.

HB.builders Context T idm op of isLaw T idm op.

HB.instance Definition _ := SemiGroup.isLaw.Build T op opA.

HB.end.

HB.factory Record isComLaw T (idm : T) (op : T -> T -> T) := {
  opA : associative op;
  opC : commutative op;
  op1m : left_id idm op;
}.

HB.builders Context T idm op of isComLaw T idm op.

Lemma opm1 : right_id idm op.
Admitted.

HB.instance Definition _ := isLaw.Build T idm op opA op1m opm1.

HB.end.

Open Scope big_scope.

Variant bigbody R I := BigBody of I & (R -> R -> R) & bool & R.

Definition applybig {R I} (body : bigbody R I) x :=
  let: BigBody _ op b v := body in if b then op v x else x.

Definition reducebig R I idx r (body : I -> bigbody R I) :=
  foldr (applybig \o body) idx r.

HB.lock Definition bigop := reducebig.

Fact index_enum_key : unit.
Admitted.

Definition index_enum (T : finType) :=
  locked_with index_enum_key (Finite.enum T).
Notation "\big [ op / idx ]_ ( i | P ) F" :=
  (bigop idx (index_enum _) (fun i => BigBody i op P%B F)) : big_scope.
Notation "\big [ op / idx ]_ ( i : t | P ) F" :=
  (bigop idx (index_enum _) (fun i : t => BigBody i op P%B F))
     (only parsing) : big_scope.
Notation "\big [ op / idx ]_ ( i 'in' A ) F" :=
  (\big[op/idx]_(i | i \in A) F) : big_scope.

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
