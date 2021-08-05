(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "-projection-no-head-constant" "-w" "-redundant-canonical-projection" "-w" "-notation-overridden" "-w" "+duplicate-clear" "-w" "-ambiguous-paths" "-w" "+non-primitive-record" "-w" "+undeclared-scope" "-w" "-deprecated-hint-without-locality" "-w" "-deprecated-ident-entry" "-w" "-deprecated-native-compiler-option" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/mathcomp/mathcomp" "mathcomp" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-I" "/github/workspace/builds/coq/coq-failing/_build_ci/mathcomp/mathcomp" "-top" "bug_01" "-native-compiler" "ondemand") -*- *)
(* File reduced by coq-bug-finder from original input, then from 5975 lines to 4644 lines, then from 4288 lines to 258 lines, then from 311 lines to 2273 lines, then from 2277 lines to 373 lines, then from 424 lines to 3656 lines, then from 3659 lines to 414 lines, then from 464 lines to 3258 lines, then from 3262 lines to 611 lines, then from 661 lines to 3802 lines, then from 3806 lines to 2026 lines *)
(* coqc version 8.15+alpha compiled with OCaml 4.12.0
   coqtop version 8.15+alpha *)
Declare ML Module "ltac_plugin".
Module Export AdmitTactic.
Module Import LocalFalse.
Inductive False := .
End LocalFalse.
Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.
End AdmitTactic.
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
Require mathcomp.ssreflect.choice.
Require mathcomp.ssreflect.path.
Require mathcomp.ssreflect.fintype.
Require mathcomp.ssreflect.tuple.
Require mathcomp.ssreflect.finfun.
Require mathcomp.ssreflect.div.
Require mathcomp.ssreflect.bigop.
Require mathcomp.ssreflect.finset.
Require mathcomp.ssreflect.prime.
Require mathcomp.fingroup.fingroup.
Require mathcomp.ssreflect.binomial.
Require mathcomp.fingroup.morphism.
Require mathcomp.fingroup.perm.
Require mathcomp.ssreflect.order.
Require mathcomp.algebra.ssralg.
Require mathcomp.fingroup.automorphism.
Require mathcomp.fingroup.quotient.
Require mathcomp.fingroup.action.
Require mathcomp.ssreflect.generic_quotient.
Require mathcomp.algebra.ring_quotient.
Require mathcomp.algebra.countalg.
Require mathcomp.algebra.finalg.
Require mathcomp.algebra.zmodp.
Require mathcomp.algebra.matrix.
Module Export mathcomp_DOT_algebra_DOT_mxalgebra_WRAPPED.
Module Export mxalgebra.
Import mathcomp.ssreflect.ssreflect.
Import mathcomp.ssreflect.ssrbool.
Import mathcomp.ssreflect.ssrfun.
Import mathcomp.ssreflect.eqtype.
Import mathcomp.ssreflect.ssrnat.
Import mathcomp.ssreflect.seq.
Import mathcomp.ssreflect.choice.
Import mathcomp.ssreflect.fintype.
Import mathcomp.ssreflect.finfun.
Import mathcomp.ssreflect.bigop.
Import mathcomp.ssreflect.finset.
Import mathcomp.fingroup.fingroup.
Import mathcomp.fingroup.perm.
Import mathcomp.ssreflect.order.
Import mathcomp.ssreflect.div.
Import mathcomp.ssreflect.prime.
Import mathcomp.ssreflect.binomial.
Import mathcomp.algebra.ssralg.
Import mathcomp.algebra.finalg.
Import mathcomp.algebra.zmodp.
Import mathcomp.algebra.matrix.

 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope matrix_set_scope.

Import GroupScope.
Import GRing.Theory.
Local Open Scope ring_scope.

Reserved Notation "\rank A" (at level 10, A at level 8, format "\rank  A").
Reserved Notation "A ^C"    (at level 8, format "A ^C").

Notation "''A_' ( m , n )" := 'M_(m, n ^ 2)
  (at level 8, format "''A_' ( m ,  n )") : type_scope.

Notation "''A_' ( n )" := 'A_(n ^ 2, n)
  (at level 8, only parsing) : type_scope.

Notation "''A_' n" := 'A_(n)
  (at level 8, n at next level, format "''A_' n") : type_scope.

Notation "''A' [ F ]_ ( m , n )" := 'M[F]_(m, n ^ 2)
  (at level 8, only parsing) : type_scope.

Notation "''A' [ F ]_ ( n )" := 'A[F]_(n ^ 2, n)
  (at level 8, only parsing) : type_scope.

Notation "''A' [ F ]_ n" := 'A[F]_(n)
  (at level 8, n at level 2, only parsing) : type_scope.

Delimit Scope matrix_set_scope with MS.

Local Notation simp := (Monoid.Theory.simpm, oppr0).

 
 
 

Section RowSpaceTheory.

Variable F : fieldType.
Implicit Types m n p r : nat.

Local Notation "''M_' ( m , n )" := 'M[F]_(m, n) : type_scope.
Local Notation "''M_' n" := 'M[F]_(n, n) : type_scope.

 
 

Fixpoint Gaussian_elimination {m n} : 'M_(m, n) -> 'M_m * 'M_n * nat :=
  match m, n with
  | _.+1, _.+1 => fun A : 'M_(1 + _, 1 + _) =>
    if [pick ij | A ij.1 ij.2 != 0] is Some (i, j) then
      let a := A i j in let A1 := xrow i 0 (xcol j 0 A) in
      let u := ursubmx A1 in let v := a^-1 *: dlsubmx A1 in
      let: (L, U, r) := Gaussian_elimination (drsubmx A1 - v *m u) in
      (xrow i 0 (block_mx 1 0 v L), xcol j 0 (block_mx a%:M u 0 U), r.+1)
    else (1%:M, 1%:M, 0%N)
  | _, _ => fun _ => (1%:M, 1%:M, 0%N)
  end.

Section Defs.

Variables (m n : nat) (A : 'M_(m, n)).

Fact Gaussian_elimination_key : unit.
admit.
Defined.

Let LUr := locked_with Gaussian_elimination_key (@Gaussian_elimination) m n A.

Definition col_ebase := LUr.1.1.
Definition row_ebase := LUr.1.2.
Definition mxrank := if [|| m == 0 | n == 0]%N then 0%N else LUr.2.

Definition row_free := mxrank == m.
Definition row_full := mxrank == n.

Definition row_base : 'M_(mxrank, n) := pid_mx mxrank *m row_ebase.
Definition col_base : 'M_(m, mxrank) := col_ebase *m pid_mx mxrank.

Definition complmx : 'M_n := copid_mx mxrank *m row_ebase.
Definition kermx : 'M_m := copid_mx mxrank *m invmx col_ebase.
Definition cokermx : 'M_n := invmx row_ebase *m copid_mx mxrank.

Definition pinvmx : 'M_(n, m) :=
  invmx row_ebase *m pid_mx mxrank *m invmx col_ebase.

End Defs.

Arguments mxrank {m%N n%N} A%MS.
Local Notation "\rank A" := (mxrank A) : nat_scope.
Arguments complmx {m%N n%N} A%MS.
Local Notation "A ^C" := (complmx A) : matrix_set_scope.

Definition submx_def := idfun (fun m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)) =>
  A *m cokermx B == 0).
Fact submx_key : unit.
admit.
Defined.
Definition submx := locked_with submx_key submx_def.
Canonical submx_unlockable := [unlockable fun submx].

Arguments submx {m1%N m2%N n%N} A%MS B%MS : rename.
Local Notation "A <= B" := (submx A B) : matrix_set_scope.
Local Notation "A <= B <= C" := ((A <= B) && (B <= C))%MS : matrix_set_scope.
Local Notation "A == B" := (A <= B <= A)%MS : matrix_set_scope.

Definition ltmx m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)) :=
  (A <= B)%MS && ~~ (B <= A)%MS.
Arguments ltmx {m1%N m2%N n%N} A%MS B%MS.
Local Notation "A < B" := (ltmx A B) : matrix_set_scope.

Definition eqmx m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)) :=
  prod (\rank A = \rank B)
       (forall m3 (C : 'M_(m3, n)),
            ((A <= C) = (B <= C)) * ((C <= A) = (C <= B)))%MS.
Arguments eqmx {m1%N m2%N n%N} A%MS B%MS.
Local Notation "A :=: B" := (eqmx A B) : matrix_set_scope.

Notation stablemx V f := (V%MS *m f%R <= V%MS)%MS.

Section LtmxIdentities.

Variables (m1 m2 n : nat) (A : 'M_(m1, n)) (B : 'M_(m2, n)).

Lemma ltmxE : (A < B)%MS = ((A <= B)%MS && ~~ (B <= A)%MS).
admit.
Defined.

Lemma ltmxW : (A < B)%MS -> (A <= B)%MS.
admit.
Defined.

Lemma ltmxEneq : (A < B)%MS = (A <= B)%MS && ~~ (A == B)%MS.
admit.
Defined.

Lemma submxElt : (A <= B)%MS = (A == B)%MS || (A < B)%MS.
admit.
Defined.

End LtmxIdentities.

 
 
 
 
 
 
 
 
 
 
 
Let qidmx m n (A : 'M_(m, n)) :=
  if m == n then A == pid_mx n else row_full A.
Let equivmx m n (A : 'M_(m, n)) idA (B : 'M_n) :=
  (B == A)%MS && (qidmx B == idA).
Let equivmx_spec m n (A : 'M_(m, n)) idA (B : 'M_n) :=
  prod (B :=: A)%MS (qidmx B = idA).
Definition genmx_witness m n (A : 'M_(m, n)) : 'M_n :=
  if row_full A then 1%:M else pid_mx (\rank A) *m row_ebase A.
Definition genmx_def := idfun (fun m n (A : 'M_(m, n)) =>
   choose (equivmx A (row_full A)) (genmx_witness A) : 'M_n).
Fact genmx_key : unit.
admit.
Defined.
Definition genmx := locked_with genmx_key genmx_def.
Canonical genmx_unlockable := [unlockable fun genmx].
Local Notation "<< A >>" := (genmx A) : matrix_set_scope.

 
 
 
Let addsmx_nop m n (A : 'M_(m, n)) := conform_mx <<A>>%MS A.
Definition addsmx_def := idfun (fun m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)) =>
  if A == 0 then addsmx_nop B else if B == 0 then addsmx_nop A else
  <<col_mx A B>>%MS : 'M_n).
Fact addsmx_key : unit.
admit.
Defined.
Definition addsmx := locked_with addsmx_key addsmx_def.
Canonical addsmx_unlockable := [unlockable fun addsmx].
Arguments addsmx {m1%N m2%N n%N} A%MS B%MS : rename.
Local Notation "A + B" := (addsmx A B) : matrix_set_scope.
Local Notation "\sum_ ( i | P ) B" := (\big[addsmx/0]_(i | P) B%MS)
  : matrix_set_scope.
Local Notation "\sum_ ( i <- r | P ) B" := (\big[addsmx/0]_(i <- r | P) B%MS)
  : matrix_set_scope.

 
 
 
 
 
 
 
 
 
 
 
 
 
Let capmx_witness m n (A : 'M_(m, n)) :=
  if row_full A then conform_mx 1%:M A else <<A>>%MS.
Let capmx_norm m n (A : 'M_(m, n)) :=
  choose (equivmx A (qidmx A)) (capmx_witness A).
Let capmx_nop m n (A : 'M_(m, n)) := conform_mx (capmx_norm A) A.
Definition capmx_gen m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)) :=
  lsubmx (kermx (col_mx A B)) *m A.
Definition capmx_def := idfun (fun m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)) =>
  if qidmx A then capmx_nop B else
  if qidmx B then capmx_nop A else
  if row_full B then capmx_norm A else capmx_norm (capmx_gen A B) : 'M_n).
Fact capmx_key : unit.
admit.
Defined.
Definition capmx := locked_with capmx_key capmx_def.
Canonical capmx_unlockable := [unlockable fun capmx].
Arguments capmx {m1%N m2%N n%N} A%MS B%MS : rename.
Local Notation "A :&: B" := (capmx A B) : matrix_set_scope.
Local Notation "\bigcap_ ( i | P ) B" := (\big[capmx/1%:M]_(i | P) B)
  : matrix_set_scope.

Definition diffmx_def := idfun (fun m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)) =>
  <<capmx_gen A (capmx_gen A B)^C>>%MS : 'M_n).
Fact diffmx_key : unit.
admit.
Defined.
Definition diffmx := locked_with diffmx_key diffmx_def.
Canonical diffmx_unlockable := [unlockable fun diffmx].
Arguments diffmx {m1%N m2%N n%N} A%MS B%MS : rename.
Local Notation "A :\: B" := (diffmx A B) : matrix_set_scope.

Definition proj_mx n (U V : 'M_n) : 'M_n := pinvmx (col_mx U V) *m col_mx U 0.

Local Notation GaussE := Gaussian_elimination.

Fact mxrankE m n (A : 'M_(m, n)) : \rank A = (GaussE A).2.
admit.
Defined.

Lemma rank_leq_row m n (A : 'M_(m, n)) : \rank A <= m.
admit.
Defined.

Lemma row_leq_rank m n (A : 'M_(m, n)) : (m <= \rank A) = row_free A.
admit.
Defined.

Lemma rank_leq_col m n (A : 'M_(m, n)) : \rank A <= n.
admit.
Defined.

Lemma col_leq_rank m n (A : 'M_(m, n)) : (n <= \rank A) = row_full A.
admit.
Defined.

Lemma eq_row_full m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)) :
  (A :=: B)%MS -> row_full A = row_full B.
admit.
Defined.

Let unitmx1F := @unitmx1 F.
Lemma row_ebase_unit m n (A : 'M_(m, n)) : row_ebase A \in unitmx.
admit.
Defined.

Lemma col_ebase_unit m n (A : 'M_(m, n)) : col_ebase A \in unitmx.
admit.
Defined.
Hint Resolve rank_leq_row rank_leq_col row_ebase_unit col_ebase_unit : core.

Lemma mulmx_ebase m n (A : 'M_(m, n)) :
  col_ebase A *m pid_mx (\rank A) *m row_ebase A = A.
admit.
Defined.

Lemma mulmx_base m n (A : 'M_(m, n)) : col_base A *m row_base A = A.
admit.
Defined.

Lemma mulmx1_min_rank r m n (A : 'M_(m, n)) M N :
  M *m A *m N = 1%:M :> 'M_r -> r <= \rank A.
admit.
Defined.
Arguments mulmx1_min_rank [r m n A].

Lemma mulmx_max_rank r m n (M : 'M_(m, r)) (N : 'M_(r, n)) :
  \rank (M *m N) <= r.
admit.
Defined.
Arguments mulmx_max_rank [r m n].

Lemma mxrank_tr m n (A : 'M_(m, n)) : \rank A^T = \rank A.
admit.
Defined.

Lemma mxrank_add m n (A B : 'M_(m, n)) : \rank (A + B)%R <= \rank A + \rank B.
admit.
Defined.

Lemma mxrankM_maxl m n p (A : 'M_(m, n)) (B : 'M_(n, p)) :
  \rank (A *m B) <= \rank A.
admit.
Defined.

Lemma mxrankM_maxr m n p (A : 'M_(m, n)) (B : 'M_(n, p)) :
  \rank (A *m B) <= \rank B.
admit.
Defined.

Lemma mxrank_scale m n a (A : 'M_(m, n)) : \rank (a *: A) <= \rank A.
admit.
Defined.

Lemma mxrank_scale_nz m n a (A : 'M_(m, n)) :
   a != 0 -> \rank (a *: A) = \rank A.
admit.
Defined.

Lemma mxrank_opp m n (A : 'M_(m, n)) : \rank (- A) = \rank A.
admit.
Defined.

Lemma mxrank0 m n : \rank (0 : 'M_(m, n)) = 0%N.
admit.
Defined.

Lemma mxrank_eq0 m n (A : 'M_(m, n)) : (\rank A == 0%N) = (A == 0).
admit.
Defined.

Lemma mulmx_coker m n (A : 'M_(m, n)) : A *m cokermx A = 0.
admit.
Defined.

Lemma submxE m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)) :
  (A <= B)%MS = (A *m cokermx B == 0).
admit.
Defined.

Lemma mulmxKpV m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)) :
  (A <= B)%MS -> A *m pinvmx B *m B = A.
admit.
Defined.

Lemma mulmxVp m n (A : 'M[F]_(m, n)) : row_free A -> A *m pinvmx A = 1%:M.
admit.
Defined.

Lemma mulmxKp p m n (B : 'M[F]_(m, n)) : row_free B ->
  cancel ((@mulmx _ p _ _)^~ B) (mulmx^~ (pinvmx B)).
admit.
Defined.

Lemma submxP m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)) :
  reflect (exists D, A = D *m B) (A <= B)%MS.
admit.
Defined.
Arguments submxP {m1 m2 n A B}.

Lemma submx_refl m n (A : 'M_(m, n)) : (A <= A)%MS.
admit.
Defined.
Hint Resolve submx_refl : core.

Lemma submxMl m n p (D : 'M_(m, n)) (A : 'M_(n, p)) : (D *m A <= A)%MS.
admit.
Defined.

Lemma submxMr m1 m2 n p (A : 'M_(m1, n)) (B : 'M_(m2, n)) (C : 'M_(n, p)) :
  (A <= B)%MS -> (A *m C <= B *m C)%MS.
admit.
Defined.

Lemma mulmx_sub m n1 n2 p (C : 'M_(m, n1)) A (B : 'M_(n2, p)) :
  (A <= B -> C *m A <= B)%MS.
admit.
Defined.

Lemma submx_trans m1 m2 m3 n
                 (A : 'M_(m1, n)) (B : 'M_(m2, n)) (C : 'M_(m3, n)) :
  (A <= B -> B <= C -> A <= C)%MS.
admit.
Defined.

Lemma ltmx_sub_trans m1 m2 m3 n
                     (A : 'M_(m1, n)) (B : 'M_(m2, n)) (C : 'M_(m3, n)) :
  (A < B)%MS -> (B <= C)%MS -> (A < C)%MS.
admit.
Defined.

Lemma sub_ltmx_trans m1 m2 m3 n
                     (A : 'M_(m1, n)) (B : 'M_(m2, n)) (C : 'M_(m3, n)) :
  (A <= B)%MS -> (B < C)%MS -> (A < C)%MS.
admit.
Defined.

Lemma ltmx_trans m n : transitive (@ltmx m m n).
admit.
Defined.

Lemma ltmx_irrefl m n : irreflexive (@ltmx m m n).
admit.
Defined.

Lemma sub0mx m1 m2 n (A : 'M_(m2, n)) : ((0 : 'M_(m1, n)) <= A)%MS.
admit.
Defined.

Lemma submx0null m1 m2 n (A : 'M[F]_(m1, n)) :
  (A <= (0 : 'M_(m2, n)))%MS -> A = 0.
admit.
Defined.

Lemma submx0 m n (A : 'M_(m, n)) : (A <= (0 : 'M_n))%MS = (A == 0).
admit.
Defined.

Lemma lt0mx m n (A : 'M_(m, n)) : ((0 : 'M_n) < A)%MS = (A != 0).
admit.
Defined.

Lemma ltmx0 m n (A : 'M[F]_(m, n)) : (A < (0 : 'M_n))%MS = false.
admit.
Defined.

Lemma eqmx0P m n (A : 'M_(m, n)) : reflect (A = 0) (A == (0 : 'M_n))%MS.
admit.
Defined.

Lemma eqmx_eq0 m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)) :
  (A :=: B)%MS -> (A == 0) = (B == 0).
admit.
Defined.

Lemma addmx_sub m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m1, n)) (C : 'M_(m2, n)) :
  (A <= C)%MS -> (B <= C)%MS -> ((A + B)%R <= C)%MS.
admit.
Defined.

Lemma rowsub_sub m1 m2 n (f : 'I_m2 -> 'I_m1) (A : 'M_(m1, n)) :
  (rowsub f A <= A)%MS.
admit.
Defined.

Lemma summx_sub m1 m2 n (B : 'M_(m2, n))
                I (r : seq I) (P : pred I) (A_ : I -> 'M_(m1, n)) :
  (forall i, P i -> A_ i <= B)%MS -> ((\sum_(i <- r | P i) A_ i)%R <= B)%MS.
admit.
Defined.

Lemma scalemx_sub m1 m2 n a (A : 'M_(m1, n)) (B : 'M_(m2, n)) :
  (A <= B)%MS -> (a *: A <= B)%MS.
admit.
Defined.

Lemma row_sub m n i (A : 'M_(m, n)) : (row i A <= A)%MS.
admit.
Defined.

Lemma eq_row_sub m n v (A : 'M_(m, n)) i : row i A = v -> (v <= A)%MS.
admit.
Defined.
Arguments eq_row_sub [m n v A].

Lemma nz_row_sub m n (A : 'M_(m, n)) : (nz_row A <= A)%MS.
admit.
Defined.

Lemma row_subP m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)) :
  reflect (forall i, row i A <= B)%MS (A <= B)%MS.
admit.
Defined.
Arguments row_subP {m1 m2 n A B}.

Lemma rV_subP m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)) :
  reflect (forall v : 'rV_n, v <= A -> v <= B)%MS (A <= B)%MS.
admit.
Defined.
Arguments rV_subP {m1 m2 n A B}.

Lemma row_subPn m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)) :
  reflect (exists i, ~~ (row i A <= B)%MS) (~~ (A <= B)%MS).
admit.
Defined.

Lemma sub_rVP n (u v : 'rV_n) : reflect (exists a, u = a *: v) (u <= v)%MS.
admit.
Defined.

Lemma rank_rV n (v : 'rV_n) : \rank v = (v != 0).
admit.
Defined.

Lemma rowV0Pn m n (A : 'M_(m, n)) :
  reflect (exists2 v : 'rV_n, v <= A & v != 0)%MS (A != 0).
admit.
Defined.

Lemma rowV0P m n (A : 'M_(m, n)) :
  reflect (forall v : 'rV_n, v <= A -> v = 0)%MS (A == 0).
admit.
Defined.

Lemma submx_full m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)) :
  row_full B -> (A <= B)%MS.
admit.
Defined.

Lemma row_fullP m n (A : 'M_(m, n)) :
  reflect (exists B, B *m A = 1%:M) (row_full A).
admit.
Defined.
Arguments row_fullP {m n A}.

Lemma row_full_inj m n p A : row_full A -> injective (@mulmx _ m n p A).
admit.
Defined.

Lemma row_freeP m n (A : 'M_(m, n)) :
  reflect (exists B, A *m B = 1%:M) (row_free A).
admit.
Defined.

Lemma row_free_inj m n p A : row_free A -> injective ((@mulmx _ m n p)^~ A).
admit.
Defined.

 
 
Definition row_free_injr m n p A : row_free A -> injective (mulmxr A) :=
  @row_free_inj m n p A.

Lemma row_free_unit n (A : 'M_n) : row_free A = (A \in unitmx).
admit.
Defined.

Lemma row_full_unit n (A : 'M_n) : row_full A = (A \in unitmx).
admit.
Defined.

Lemma mxrank_unit n (A : 'M_n) : A \in unitmx -> \rank A = n.
admit.
Defined.

Lemma mxrank1 n : \rank (1%:M : 'M_n) = n.
admit.
Defined.

Lemma mxrank_delta m n i j : \rank (delta_mx i j : 'M_(m, n)) = 1%N.
admit.
Defined.

Lemma mxrankS m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)) :
  (A <= B)%MS -> \rank A <= \rank B.
admit.
Defined.

Lemma submx1 m n (A : 'M_(m, n)) : (A <= 1%:M)%MS.
admit.
Defined.

Lemma sub1mx m n (A : 'M_(m, n)) : (1%:M <= A)%MS = row_full A.
admit.
Defined.

Lemma ltmx1 m n (A : 'M_(m, n)) : (A < 1%:M)%MS = ~~ row_full A.
admit.
Defined.

Lemma lt1mx m n (A : 'M_(m, n)) : (1%:M < A)%MS = false.
admit.
Defined.

Lemma pinvmxE n (A : 'M[F]_n) : A \in unitmx -> pinvmx A = invmx A.
admit.
Defined.

Lemma mulVpmx m n (A : 'M[F]_(m, n)) : row_full A -> pinvmx A *m A = 1%:M.
admit.
Defined.

Lemma pinvmx_free m n (A : 'M[F]_(m, n)) : row_full A -> row_free (pinvmx A).
admit.
Defined.

Lemma pinvmx_full m n (A : 'M[F]_(m, n)) : row_free A -> row_full (pinvmx A).
admit.
Defined.

Lemma eqmxP m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)) :
  reflect (A :=: B)%MS (A == B)%MS.
admit.
Defined.
Arguments eqmxP {m1 m2 n A B}.

Lemma rV_eqP m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)) :
  reflect (forall u : 'rV_n, (u <= A) = (u <= B))%MS (A == B)%MS.
admit.
Defined.

Lemma eqmx_refl m1 n (A : 'M_(m1, n)) : (A :=: A)%MS.
admit.
Defined.

Lemma eqmx_sym m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)) :
  (A :=: B)%MS -> (B :=: A)%MS.
admit.
Defined.

Lemma eqmx_trans m1 m2 m3 n (A : 'M_(m1, n)) (B : 'M_(m2, n)) (C : 'M_(m3, n)) :
  (A :=: B)%MS -> (B :=: C)%MS -> (A :=: C)%MS.
admit.
Defined.

Lemma eqmx_rank m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)) :
  (A == B)%MS -> \rank A = \rank B.
admit.
Defined.

Lemma lt_eqmx m1 m2 m3 n (A : 'M_(m1, n)) (B : 'M_(m2, n)) :
    (A :=: B)%MS ->
  forall C : 'M_(m3, n), (((A < C) = (B < C))%MS * ((C < A) = (C < B))%MS)%type.
admit.
Defined.

Lemma eqmxMr m1 m2 n p (A : 'M_(m1, n)) (B : 'M_(m2, n)) (C : 'M_(n, p)) :
  (A :=: B)%MS -> (A *m C :=: B *m C)%MS.
admit.
Defined.

Lemma eqmxMfull m n p (A : 'M_(m, n)) (B : 'M_(n, p)) :
  row_full A -> (A *m B :=: B)%MS.
admit.
Defined.

Lemma eqmx0 m n : ((0 : 'M[F]_(m, n)) :=: (0 : 'M_n))%MS.
admit.
Defined.

Lemma eqmx_scale m n a (A : 'M_(m, n)) : a != 0 -> (a *: A :=: A)%MS.
admit.
Defined.

Lemma eqmx_opp m n (A : 'M_(m, n)) : (- A :=: A)%MS.
admit.
Defined.

Lemma submxMfree m1 m2 n p (A : 'M_(m1, n)) (B : 'M_(m2, n)) (C : 'M_(n, p)) :
  row_free C -> (A *m C <= B *m C)%MS = (A <= B)%MS.
admit.
Defined.

Lemma eqmxMfree m1 m2 n p (A : 'M_(m1, n)) (B : 'M_(m2, n)) (C : 'M_(n, p)) :
  row_free C -> (A *m C :=: B *m C)%MS -> (A :=: B)%MS.
admit.
Defined.

Lemma mxrankMfree m n p (A : 'M_(m, n)) (B : 'M_(n, p)) :
  row_free B -> \rank (A *m B) = \rank A.
admit.
Defined.

Lemma eq_row_base m n (A : 'M_(m, n)) : (row_base A :=: A)%MS.
admit.
Defined.

Lemma row_base0 (m n : nat) : row_base (0 : 'M[F]_(m, n)) = 0.
admit.
Defined.

Let qidmx_eq1 n (A : 'M_n) : qidmx A = (A == 1%:M).
admit.
Defined.

Let genmx_witnessP m n (A : 'M_(m, n)) :
  equivmx A (row_full A) (genmx_witness A).
admit.
Defined.

Lemma genmxE m n (A : 'M_(m, n)) : (<<A>> :=: A)%MS.
admit.
Defined.

Lemma eq_genmx m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)) :
  (A :=: B -> <<A>> = <<B>>)%MS.
admit.
Defined.

Lemma genmxP m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)) :
  reflect (<<A>> = <<B>>)%MS (A == B)%MS.
admit.
Defined.
Arguments genmxP {m1 m2 n A B}.

Lemma genmx0 m n : <<0 : 'M_(m, n)>>%MS = 0.
admit.
Defined.

Lemma genmx1 n : <<1%:M : 'M_n>>%MS = 1%:M.
admit.
Defined.

Lemma genmx_id m n (A : 'M_(m, n)) : (<<<<A>>>> = <<A>>)%MS.
admit.
Defined.

Lemma row_base_free m n (A : 'M_(m, n)) : row_free (row_base A).
admit.
Defined.

Lemma mxrank_gen m n (A : 'M_(m, n)) : \rank <<A>> = \rank A.
admit.
Defined.

Lemma col_base_full m n (A : 'M_(m, n)) : row_full (col_base A).
admit.
Defined.
Hint Resolve row_base_free col_base_full : core.

Lemma mxrank_leqif_sup m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)) :
  (A <= B)%MS -> \rank A <= \rank B ?= iff (B <= A)%MS.
admit.
Defined.

Lemma mxrank_leqif_eq m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)) :
  (A <= B)%MS -> \rank A <= \rank B ?= iff (A == B)%MS.
admit.
Defined.

Lemma ltmxErank m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)) :
  (A < B)%MS = (A <= B)%MS && (\rank A < \rank B).
admit.
Defined.

Lemma rank_ltmx m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)) :
  (A < B)%MS -> \rank A < \rank B.
admit.
Defined.

Lemma eqmx_cast m1 m2 n (A : 'M_(m1, n)) e :
  ((castmx e A : 'M_(m2, n)) :=: A)%MS.
admit.
Defined.

Lemma row_full_castmx m1 m2 n (A : 'M_(m1, n)) e :
  row_full (castmx e A  : 'M_(m2, n)) = row_full A.
admit.
Defined.

Lemma row_free_castmx m1 m2 n (A : 'M_(m1, n)) e :
  row_free (castmx e A  : 'M_(m2, n)) = row_free A.
admit.
Defined.

Lemma eqmx_conform m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)) :
  (conform_mx A B :=: A \/ conform_mx A B :=: B)%MS.
admit.
Defined.

Let eqmx_sum_nop m n (A : 'M_(m, n)) : (addsmx_nop A :=: A)%MS.
admit.
Defined.

Lemma rowsub_comp_sub (m n p q : nat) f (g : 'I_n -> 'I_p) (A : 'M_(m, q)) :
   (rowsub (f \o g) A <= rowsub f A)%MS.
admit.
Defined.

Lemma submx_rowsub (m n p q : nat) (h : 'I_n -> 'I_p) f g (A : 'M_(m, q)) :
  f =1 g \o h -> (rowsub f A <= rowsub g A)%MS.
admit.
Defined.
Arguments submx_rowsub [m1 m2 m3 n] h [f g A] _ : rename.

Lemma eqmx_rowsub_comp_perm (m1 m2 n : nat) (s : 'S_m2) f (A : 'M_(m1, n)) :
  (rowsub (f \o s) A :=: rowsub f A)%MS.
admit.
Defined.

Lemma eqmx_rowsub_comp (m n p q : nat) f (g : 'I_n -> 'I_p) (A : 'M_(m, q)) :
  p <= n -> injective g -> (rowsub (f \o g) A :=: rowsub f A)%MS.
admit.
Defined.

Lemma eqmx_rowsub (m n p q : nat) (h : 'I_n -> 'I_p) f g (A : 'M_(m, q)) :
  injective h -> p <= n -> f =1 g \o h -> (rowsub f A :=: rowsub g A)%MS.
admit.
Defined.
Arguments eqmx_rowsub [m1 m2 m3 n] h [f g A] _ : rename.

Section AddsmxSub.

Variable (m1 m2 n : nat) (A : 'M[F]_(m1, n)) (B : 'M[F]_(m2, n)).

Lemma col_mx_sub m3 (C : 'M_(m3, n)) :
  (col_mx A B <= C)%MS = (A <= C)%MS && (B <= C)%MS.
admit.
Defined.

Lemma addsmxE : (A + B :=: col_mx A B)%MS.
admit.
Defined.

Lemma addsmx_sub m3 (C : 'M_(m3, n)) :
  (A + B <= C)%MS = (A <= C)%MS && (B <= C)%MS.
admit.
Defined.

Lemma addsmxSl : (A <= A + B)%MS.
admit.
Defined.

Lemma addsmxSr : (B <= A + B)%MS.
admit.
Defined.

Lemma addsmx_idPr : reflect (A + B :=: B)%MS (A <= B)%MS.
admit.
Defined.

Lemma addsmx_idPl : reflect (A + B :=: A)%MS (B <= A)%MS.
admit.
Defined.

End AddsmxSub.

Lemma adds0mx m1 m2 n (B : 'M_(m2, n)) : ((0 : 'M_(m1, n)) + B :=: B)%MS.
admit.
Defined.

Lemma addsmx0 m1 m2 n (A : 'M_(m1, n)) : (A + (0 : 'M_(m2, n)) :=: A)%MS.
admit.
Defined.

Let addsmx_nop_eq0 m n (A : 'M_(m, n)) : (addsmx_nop A == 0) = (A == 0).
admit.
Defined.

Let addsmx_nop0 m n : addsmx_nop (0 : 'M_(m, n)) = 0.
admit.
Defined.

Let addsmx_nop_id n (A : 'M_n) : addsmx_nop A = A.
admit.
Defined.

Lemma addsmxC m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)) : (A + B = B + A)%MS.
admit.
Defined.

Lemma adds0mx_id m1 n (B : 'M_n) : ((0 : 'M_(m1, n)) + B)%MS = B.
admit.
Defined.

Lemma addsmx0_id m2 n (A : 'M_n) : (A + (0 : 'M_(m2, n)))%MS = A.
admit.
Defined.

Lemma addsmxA m1 m2 m3 n (A : 'M_(m1, n)) (B : 'M_(m2, n)) (C : 'M_(m3, n)) :
  (A + (B + C) = A + B + C)%MS.
admit.
Defined.

Canonical addsmx_monoid n :=
  Monoid.Law (@addsmxA n n n n) (@adds0mx_id n n) (@addsmx0_id n n).
Canonical addsmx_comoid n := Monoid.ComLaw (@addsmxC n n n).

Lemma addsmxMr m1 m2 n p (A : 'M_(m1, n)) (B : 'M_(m2, n)) (C : 'M_(n, p)) :
  ((A + B)%MS *m C :=: A *m C + B *m C)%MS.
admit.
Defined.

Lemma addsmxS m1 m2 m3 m4 n (A : 'M_(m1, n)) (B : 'M_(m2, n))
                            (C : 'M_(m3, n)) (D : 'M_(m4, n)) :
  (A <= C -> B <= D -> A + B <= C + D)%MS.
admit.
Defined.

Lemma addmx_sub_adds m m1 m2 n (A : 'M_(m, n)) (B : 'M_(m, n))
                               (C : 'M_(m1, n)) (D : 'M_(m2, n)) :
  (A <= C -> B <= D -> (A + B)%R <= C + D)%MS.
admit.
Defined.

Lemma addsmx_addKl n m1 m2 (A : 'M_(m1, n)) (B C : 'M_(m2, n)) :
  (B <= A)%MS -> (A + (B + C)%R :=: A + C)%MS.
admit.
Defined.

Lemma addsmx_addKr n m1 m2 (A B : 'M_(m1, n)) (C : 'M_(m2, n)) :
  (B <= C)%MS -> ((A + B)%R + C :=: A + C)%MS.
admit.
Defined.

Lemma adds_eqmx m1 m2 m3 m4 n (A : 'M_(m1, n)) (B : 'M_(m2, n))
                              (C : 'M_(m3, n)) (D : 'M_(m4, n)) :
  (A :=: C -> B :=: D -> A + B :=: C + D)%MS.
admit.
Defined.

Lemma genmx_adds m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)) :
  (<<(A + B)%MS>> = <<A>> + <<B>>)%MS.
admit.
Defined.

Lemma sub_addsmxP m1 m2 m3 n
                  (A : 'M_(m1, n)) (B : 'M_(m2, n)) (C : 'M_(m3, n)) :
  reflect (exists u, A = u.1 *m B + u.2 *m C) (A <= B + C)%MS.
admit.
Defined.
Arguments sub_addsmxP {m1 m2 m3 n A B C}.

Variable I : finType.
Implicit Type P : pred I.

Lemma genmx_sums P n (B_ : I -> 'M_n) :
  <<(\sum_(i | P i) B_ i)%MS>>%MS = (\sum_(i | P i) <<B_ i>>)%MS.
admit.
Defined.

Lemma sumsmx_sup i0 P m n (A : 'M_(m, n)) (B_ : I -> 'M_n) :
  P i0 -> (A <= B_ i0)%MS -> (A <= \sum_(i | P i) B_ i)%MS.
admit.
Defined.
Arguments sumsmx_sup i0 [P m n A B_].

Lemma sumsmx_subP P m n (A_ : I -> 'M_n) (B : 'M_(m, n)) :
  reflect (forall i, P i -> A_ i <= B)%MS (\sum_(i | P i) A_ i <= B)%MS.
admit.
Defined.

Lemma summx_sub_sums P m n (A : I -> 'M[F]_(m, n)) B :
    (forall i, P i -> A i <= B i)%MS ->
  ((\sum_(i | P i) A i)%R <= \sum_(i | P i) B i)%MS.
admit.
Defined.

Lemma sumsmxS P n (A B : I -> 'M[F]_n) :
    (forall i, P i -> A i <= B i)%MS ->
  (\sum_(i | P i) A i <= \sum_(i | P i) B i)%MS.
admit.
Defined.

Lemma eqmx_sums P n (A B : I -> 'M[F]_n) :
    (forall i, P i -> A i :=: B i)%MS ->
  (\sum_(i | P i) A i :=: \sum_(i | P i) B i)%MS.
admit.
Defined.

Lemma sub_sums_genmxP P m n p (A : 'M_(m, p)) (B_ : I -> 'M_(n, p)) :
  reflect (exists u_ : I -> 'M_(m, n), A = \sum_(i | P i) u_ i *m B_ i)
          (A <= \sum_(i | P i) <<B_ i>>)%MS.
admit.
Defined.

Lemma sub_sumsmxP P m n (A : 'M_(m, n)) (B_ : I -> 'M_n) :
  reflect (exists u_, A = \sum_(i | P i) u_ i *m B_ i)
          (A <= \sum_(i | P i) B_ i)%MS.
admit.
Defined.

Lemma sumsmxMr_gen P m n A (B : 'M[F]_(m, n)) :
  ((\sum_(i | P i) A i)%MS *m B :=: \sum_(i | P i) <<A i *m B>>)%MS.
admit.
Defined.

Lemma sumsmxMr P n (A_ : I -> 'M[F]_n) (B : 'M_n) :
  ((\sum_(i | P i) A_ i)%MS *m B :=: \sum_(i | P i) (A_ i *m B))%MS.
admit.
Defined.

Lemma rank_pid_mx m n r : r <= m -> r <= n -> \rank (pid_mx r : 'M_(m, n)) = r.
admit.
Defined.

Lemma rank_copid_mx n r : r <= n -> \rank (copid_mx r : 'M_n) = (n - r)%N.
admit.
Defined.

Lemma mxrank_compl m n (A : 'M_(m, n)) : \rank A^C = (n - \rank A)%N.
admit.
Defined.

Lemma mxrank_ker m n (A : 'M_(m, n)) : \rank (kermx A) = (m - \rank A)%N.
admit.
Defined.

Lemma kermx_eq0 n m (A : 'M_(m, n)) : (kermx A == 0) = row_free A.
admit.
Defined.

Lemma mxrank_coker m n (A : 'M_(m, n)) : \rank (cokermx A) = (n - \rank A)%N.
admit.
Defined.

Lemma cokermx_eq0 n m (A : 'M_(m, n)) : (cokermx A == 0) = row_full A.
admit.
Defined.

Lemma mulmx_ker m n (A : 'M_(m, n)) : kermx A *m A = 0.
admit.
Defined.

Lemma mulmxKV_ker m n p (A : 'M_(n, p)) (B : 'M_(m, n)) :
  B *m A = 0 -> B *m col_ebase A *m kermx A = B.
admit.
Defined.

Lemma sub_kermxP p m n (A : 'M_(m, n)) (B : 'M_(p, m)) :
  reflect (B *m A = 0) (B <= kermx A)%MS.
admit.
Defined.

Lemma sub_kermx p m n (A : 'M_(m, n)) (B : 'M_(p, m)) :
  (B <= kermx A)%MS = (B *m A == 0).
admit.
Defined.

Lemma kermx0 m n : (kermx (0 : 'M_(m, n)) :=: 1%:M)%MS.
admit.
Defined.

Lemma mulmx_free_eq0 m n p (A : 'M_(m, n)) (B : 'M_(n, p)) :
  row_free B -> (A *m B == 0) = (A == 0).
admit.
Defined.

Lemma inj_row_free m n (A : 'M_(m, n)) :
  (forall v : 'rV_m, v *m A = 0 -> v = 0) -> row_free A.
admit.
Defined.

Lemma row_freePn m n (M : 'M[F]_(m, n)) :
 reflect (exists i, (row i M <= row' i M)%MS) (~~ row_free M).
admit.
Defined.

Lemma negb_row_free m n (M : 'M[F]_(m, n)) :
  ~~ row_free M = [exists i, (row i M <= row' i M)%MS].
admit.
Defined.

Lemma mulmx0_rank_max m n p (A : 'M_(m, n)) (B : 'M_(n, p)) :
  A *m B = 0 -> \rank A + \rank B <= n.
admit.
Defined.

Lemma mxrank_Frobenius m n p q (A : 'M_(m, n)) B (C : 'M_(p, q)) :
  \rank (A *m B) + \rank (B *m C) <= \rank B + \rank (A *m B *m C).
admit.
Defined.

Lemma mxrank_mul_min m n p (A : 'M_(m, n)) (B : 'M_(n, p)) :
  \rank A + \rank B - n <= \rank (A *m B).
admit.
Defined.

Lemma addsmx_compl_full m n (A : 'M_(m, n)) : row_full (A + A^C)%MS.
admit.
Defined.

Lemma sub_capmx_gen m1 m2 m3 n (A : 'M_(m1, n)) (B : 'M_(m2, n)) (C : 'M_(m3, n)) :
  (A <= capmx_gen B C)%MS = (A <= B)%MS && (A <= C)%MS.
admit.
Defined.

Let capmx_witnessP m n (A : 'M_(m, n)) : equivmx A (qidmx A) (capmx_witness A).
admit.
Defined.

Let capmx_normP m n (A : 'M_(m, n)) : equivmx_spec A (qidmx A) (capmx_norm A).
admit.
Defined.

Let capmx_norm_eq m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)) :
  qidmx A = qidmx B -> (A == B)%MS -> capmx_norm A = capmx_norm B.
admit.
Defined.

Let capmx_nopP m n (A : 'M_(m, n)) : equivmx_spec A (qidmx A) (capmx_nop A).
admit.
Defined.

Let sub_qidmx m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)) :
  qidmx B -> (A <= B)%MS.
admit.
Defined.

Let qidmx_cap m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)) :
  qidmx (A :&: B)%MS = qidmx A && qidmx B.
admit.
Defined.

Let capmx_eq_norm m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)) :
  qidmx A = qidmx B -> (A :&: B)%MS = capmx_norm (A :&: B)%MS.
admit.
Defined.

Lemma capmxE m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)) :
  (A :&: B :=: capmx_gen A B)%MS.
admit.
Defined.

Lemma capmxSl m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)) : (A :&: B <= A)%MS.
admit.
Defined.

Lemma sub_capmx m m1 m2 n (A : 'M_(m, n)) (B : 'M_(m1, n)) (C : 'M_(m2, n)) :
  (A <= B :&: C)%MS = (A <= B)%MS && (A <= C)%MS.
admit.
Defined.

Lemma capmxC m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)) : (A :&: B = B :&: A)%MS.
admit.
Defined.

Lemma capmxSr m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)) : (A :&: B <= B)%MS.
admit.
Defined.

Lemma capmx_idPr n m1 m2 (A : 'M_(m1, n)) (B : 'M_(m2, n)) :
  reflect (A :&: B :=: B)%MS (B <= A)%MS.
admit.
Defined.

Lemma capmx_idPl n m1 m2 (A : 'M_(m1, n)) (B : 'M_(m2, n)) :
  reflect (A :&: B :=: A)%MS (A <= B)%MS.
admit.
Defined.

 

Section MaxRankSubMatrix.

End MaxRankSubMatrix.

Section SumExpr.

Section Binary.
End Binary.

Section Nary.
End Nary.

End SumExpr.

Section BinaryDirect.

End BinaryDirect.

Section NaryDirect.

End NaryDirect.

Section SubDaddsmx.

End SubDaddsmx.

Section SubDsumsmx.

End SubDsumsmx.

Section Eigenspace.

End Eigenspace.

End RowSpaceTheory.
Notation "\rank A" := (mxrank A) : nat_scope.
Notation "A <= B" := (submx A B) : matrix_set_scope.

Section Stability.

Section FixedDim.

End FixedDim.

Section Commutation.

End Commutation.

End Stability.

Section DirectSums.

End DirectSums.

Section CardGL.

End CardGL.

Section MatrixAlgebra.

Section CentMxDef.

End CentMxDef.

End MatrixAlgebra.

 
Section MapMatrixSpaces.

End MapMatrixSpaces.

Section RowColDiagBlockMatrix.

End RowColDiagBlockMatrix.
Module Export mathcomp_DOT_algebra_DOT_mxalgebra.
Module Export mathcomp.
Module Export algebra.
Module Export mxalgebra.
End mxalgebra.

End algebra.

End mathcomp.

End mathcomp_DOT_algebra_DOT_mxalgebra.
Module Export mathcomp.
Module Export algebra.
Module poly.
Import mathcomp.ssreflect.ssreflect.
Import mathcomp.ssreflect.ssrbool.
Import mathcomp.ssreflect.ssrfun.
Import mathcomp.ssreflect.eqtype.
Import mathcomp.ssreflect.ssrnat.
Import mathcomp.ssreflect.seq.
Import mathcomp.ssreflect.choice.
Import mathcomp.ssreflect.fintype.
Import mathcomp.algebra.ssralg.

Set Implicit Arguments.
Unset Strict Implicit.

Import GRing.Theory.
Local Open Scope ring_scope.
Reserved Notation "c %:P" (at level 2, format "c %:P").
Reserved Notation "''X^' n" (at level 3, n at level 2, format "''X^' n").
Reserved Notation "\poly_ ( i < n ) E"
  (at level 36, E at level 36, i, n at level 50,
   format "\poly_ ( i  <  n )  E").

Section Polynomial.

Variable R : ringType.

Record polynomial := Polynomial {polyseq :> seq R; _ : last 1 polyseq != 0}.

Canonical polynomial_subType := Eval hnf in [subType for polyseq].
Definition polynomial_eqMixin := Eval hnf in [eqMixin of polynomial by <:].
Canonical polynomial_eqType := Eval hnf in EqType polynomial polynomial_eqMixin.
Definition polynomial_choiceMixin := [choiceMixin of polynomial by <:].
Canonical polynomial_choiceType :=
  Eval hnf in ChoiceType polynomial polynomial_choiceMixin.

Definition poly_of of phant R := polynomial.

End Polynomial.
Notation "{ 'poly' T }" := (poly_of (Phant T)).

Section PolynomialTheory.

Variable R : ringType.
Implicit Types (a b c x y z : R) (p q r d : {poly R}).
Canonical poly_eqType := Eval hnf in [eqType of {poly R}].

Definition lead_coef p := p`_(size p).-1.

Definition poly_nil := @Polynomial R [::] (oner_neq0 R).
Definition polyC c : {poly R} := insubd poly_nil [:: c].

Local Notation "c %:P" := (polyC c).

Definition cons_poly c p : {poly R} :=
  if p is Polynomial ((_ :: _) as s) ns then
    @Polynomial R (c :: s) ns
  else c%:P.

Definition Poly := foldr cons_poly 0%:P.

Definition poly_expanded_def n E := Poly (mkseq E n).
Fact poly_key : unit.
admit.
Defined.
Definition poly := locked_with poly_key poly_expanded_def.
Local Notation "\poly_ ( i < n ) E" := (poly n (fun i : nat => E)).

Definition add_poly_def p q := \poly_(i < maxn (size p) (size q)) (p`_i + q`_i).
Fact add_poly_key : unit.
admit.
Defined.
Definition add_poly := locked_with add_poly_key add_poly_def.

Definition opp_poly_def p := \poly_(i < size p) - p`_i.
Fact opp_poly_key : unit.
admit.
Defined.
Definition opp_poly := locked_with opp_poly_key opp_poly_def.

Fact add_polyA : associative add_poly.
admit.
Defined.

Fact add_polyC : commutative add_poly.
admit.
Defined.

Fact add_poly0 : left_id 0%:P add_poly.
admit.
Defined.

Fact add_polyN : left_inverse 0%:P opp_poly add_poly.
admit.
Defined.

Definition poly_zmodMixin :=
  ZmodMixin add_polyA add_polyC add_poly0 add_polyN.

Canonical poly_zmodType := Eval hnf in ZmodType {poly R} poly_zmodMixin.

Definition mul_poly_def p q :=
  \poly_(i < (size p + size q).-1) (\sum_(j < i.+1) p`_j * q`_(i - j)).
Fact mul_poly_key : unit.
admit.
Defined.
Definition mul_poly := locked_with mul_poly_key mul_poly_def.

Fact mul_polyA : associative mul_poly.
admit.
Defined.

Fact mul_1poly : left_id 1%:P mul_poly.
admit.
Defined.

Fact mul_poly1 : right_id 1%:P mul_poly.
admit.
Defined.

Fact mul_polyDl : left_distributive mul_poly +%R.
admit.
Defined.

Fact mul_polyDr : right_distributive mul_poly +%R.
admit.
Defined.

Fact poly1_neq0 : 1%:P != 0 :> {poly R}.
admit.
Defined.

Definition poly_ringMixin :=
  RingMixin mul_polyA mul_1poly mul_poly1 mul_polyDl mul_polyDr poly1_neq0.

Canonical poly_ringType := Eval hnf in RingType {poly R} poly_ringMixin.

Definition scale_poly_def a (p : {poly R}) := \poly_(i < size p) (a * p`_i).
Fact scale_poly_key : unit.
admit.
Defined.
Definition scale_poly := locked_with scale_poly_key scale_poly_def.

Fact scale_polyA a b p : scale_poly a (scale_poly b p) = scale_poly (a * b) p.
admit.
Defined.

Fact scale_1poly : left_id 1 scale_poly.
admit.
Defined.

Fact scale_polyDr a : {morph scale_poly a : p q / p + q}.
admit.
Defined.

Fact scale_polyDl p : {morph scale_poly^~ p : a b / a + b}.
admit.
Defined.

Definition poly_lmodMixin :=
  LmodMixin scale_polyA scale_1poly scale_polyDr scale_polyDl.

Canonical poly_lmodType :=
  Eval hnf in LmodType R {poly R} poly_lmodMixin.

Definition polyX_def := Poly [:: 0; 1].
Fact polyX_key : unit.
admit.
Defined.
Definition polyX : {poly R} := locked_with polyX_key polyX_def.
Fixpoint horner_rec s x := if s is a :: s' then horner_rec s' x * x + a else 0.
Definition horner p := horner_rec p.

End PolynomialTheory.
Notation "\poly_ ( i < n ) E" := (poly n (fun i => E)) : ring_scope.
Notation "c %:P" := (polyC c) : ring_scope.
Notation "'X" := (polyX _) : ring_scope.
Notation "''X^' n" := ('X ^+ n) : ring_scope.
Notation "p .[ x ]" := (horner p x) : ring_scope.

Section MapPoly.

Section Definitions.

Variables (aR rR : ringType) (f : aR -> rR).

Definition map_poly (p : {poly aR}) := \poly_(i < size p) f p`_i.

Definition commr_rmorph u := forall x, GRing.comm u (f x).

Definition horner_morph u of commr_rmorph u := fun p => (map_poly p).[u].

End Definitions.

End MapPoly.

End poly.
Import mathcomp.ssreflect.ssreflect.
Import mathcomp.ssreflect.ssrfun.
Import mathcomp.ssreflect.ssrbool.
Import mathcomp.ssreflect.eqtype.
Import mathcomp.ssreflect.ssrnat.
Import mathcomp.ssreflect.seq.
Import mathcomp.algebra.ssralg.
Import mathcomp.algebra.poly.

Set Implicit Arguments.
Local Open Scope ring_scope.

Section RingPseudoDivision.

Variable R : ringType.

Definition redivp_rec (q : {poly R}) :=
  let sq := size q in
  let cq := lead_coef q in
   fix loop (k : nat) (qq r : {poly R})(n : nat) {struct n} :=
    if size r < sq then (k, qq, r) else
    let m := (lead_coef r) *: 'X^(size r - sq) in
    let qq1 := qq * cq%:P + m in
    let r1 := r * cq%:P - m * q in
       if n is n1.+1 then loop k.+1 qq1 r1 n1 else (k.+1, qq1, r1).

Definition redivp_expanded_def p q :=
   if q == 0 then (0%N, 0, p) else redivp_rec q 0 0 p (size p).
Fact redivp_key : unit.
admit.
Defined.
Definition redivp : {poly R} -> {poly R} -> nat * {poly R} * {poly R} :=
  locked_with redivp_key redivp_expanded_def.

End RingPseudoDivision.

Section IDomainPseudoDivisionDefs.

Variable R : idomainType.
Implicit Type p q r d : {poly R}.

Definition edivp_expanded_def p q :=
  let: (k, d, r) as edvpq := redivp p q in
  if lead_coef q \in GRing.unit then
    (0%N, (lead_coef q)^-k *: d, (lead_coef q)^-k *: r)
  else edvpq.
Fact edivp_key : unit.
admit.
Defined.
Definition edivp := locked_with edivp_key edivp_expanded_def.
Definition modp p q := (edivp p q).2.

End IDomainPseudoDivisionDefs.
Notation "m %% d" := (modp m d) : ring_scope.
Import mathcomp.ssreflect.fintype.
Import mathcomp.ssreflect.tuple.
Import mathcomp.ssreflect.finfun.
Import mathcomp.ssreflect.bigop.
Import mathcomp.algebra.zmodp.
Import mathcomp.algebra.matrix.
Unset Strict Implicit.

Section RowPoly.

Variables (R : ringType) (d : nat).
Implicit Types u v : 'rV[R]_d.
Implicit Types p q : {poly R}.

Definition rVpoly v := \poly_(k < d) (if insub k is Some i then v 0 i else 0).
Definition poly_rV p := \row_(i < d) p`_i.

End RowPoly.
Arguments poly_rV {R d}.

Section HornerMx.

Variables (R : comRingType) (n' : nat).
Local Notation n := n'.+1.

Section OneMatrix.

Variable A : 'M[R]_n.

Definition horner_mx := horner_morph (comm_mx_scalar^~ A).

Definition powers_mx d := \matrix_(i < d) mxvec (A ^+ i).

End OneMatrix.

End HornerMx.

Section MinPoly.

Variables (F : fieldType) (n' : nat).
Local Notation n := n'.+1.
Variable A : 'M[F]_n.

Fact degree_mxminpoly_proof : exists d, \rank (powers_mx A d.+1) <= d.
admit.
Defined.
Definition degree_mxminpoly := ex_minn degree_mxminpoly_proof.
Local Notation d := degree_mxminpoly.
Local Notation Ad := (powers_mx A d).

Definition mx_inv_horner B := rVpoly (mxvec B *m pinvmx Ad).

Definition mxminpoly := 'X^d - mx_inv_horner (A ^+ d).

End MinPoly.

Section MatrixFormula.

Variable F : fieldType.
Local Notation Add := GRing.Add (only parsing).
Local Notation Bool b := (GRing.Bool b%bool).
Local Notation term := (GRing.term F).
Local Notation form := (GRing.formula F).
Local Notation eval := GRing.eval.
Local Notation holds := GRing.holds.
Local Notation qf_form := GRing.qf_form.
Local Notation qf_eval := GRing.qf_eval.

Definition eval_mx (e : seq F) := @map_mx term F (eval e).

Definition mx_term := @map_mx F term GRing.Const.

Definition mulmx_term m n p (A : 'M[term]_(m, n)) (B : 'M_(n, p)) :=
  \matrix_(i, k) (\big[Add/0]_j (A i j * B j k))%T.

Let Schur m n (A : 'M[term]_(1 + m, 1 + n)) (a := A 0 0) :=
  \matrix_(i, j) (drsubmx A i j - a^-1 * dlsubmx A i 0%R * ursubmx A 0%R j)%T.

Fixpoint mxrank_form (r m n : nat) : 'M_(m, n) -> form :=
  match m, n return 'M_(m, n) -> form with
  | m'.+1, n'.+1 => fun A : 'M_(1 + m', 1 + n') =>
    let nzA k := A k.1 k.2 != 0 in
    let xSchur k := Schur (xrow k.1 0%R (xcol k.2 0%R A)) in
    let recf k := Bool (r > 0) /\ mxrank_form r.-1 (xSchur k) in
    GRing.Pick nzA recf (Bool (r == 0%N))
  | _, _ => fun _ => Bool (r == 0%N)
  end%T.

Lemma mxrank_form_qf r m n (A : 'M_(m, n)) : qf_form (mxrank_form r A).
admit.
Defined.

Lemma eval_mxrank e r m n (A : 'M_(m, n)) :
  qf_eval e (mxrank_form r A) = (\rank (eval_mx e A) == r).
admit.
Defined.

Section Env.

Variable d : nat.

Definition seq_of_rV (v : 'rV_d) : seq F := fgraph [ffun i => v 0 i].

Definition row_var k : 'rV[term]_d := \row_i ('X_(k * d + i))%T.

Definition row_env (e : seq 'rV_d) := flatten (map seq_of_rV e).

Definition Exists_row_form k (f : form) :=
  foldr GRing.Exists f (codom (fun i : 'I_d => k * d + i)%N).

Lemma Exists_rowP e k f :
  d > 0 ->
   ((exists v : 'rV[F]_d, holds (row_env (set_nth 0 e k v)) f)
      <-> holds (row_env e) (Exists_row_form k f)).
admit.
Defined.

End Env.

End MatrixFormula.
Import mathcomp.ssreflect.choice.
Import mathcomp.ssreflect.finset.
Import mathcomp.fingroup.fingroup.
Unset Printing Implicit Defensive.
Import GRing.Theory.

Section RingRepr.

Variable R : comUnitRingType.

Section OneRepresentation.

Variable gT : finGroupType.

Definition mx_repr (G : {set gT}) n (r : gT -> 'M[R]_n) :=
  r 1%g = 1%:M /\ {in G &, {morph r : x y / (x * y)%g >-> x *m y}}.

Structure mx_representation G n :=
  MxRepresentation { repr_mx :> gT -> 'M_n; _ : mx_repr G repr_mx }.

Variables (G : {group gT}) (n : nat) (rG : mx_representation G n).

Section CentHom.

Variable f : 'M[R]_n.

Definition rcent := [set x in G | f *m rG x == rG x *m f].

Definition centgmx := G \subset rcent.

End CentHom.

End OneRepresentation.

End RingRepr.

Section FieldRepr.

Variable F : fieldType.

Section OneRepresentation.

Variable gT : finGroupType.

Variables (G : {group gT}) (n : nat) (rG : mx_representation F G n).

Section Stabilisers.

Variables (m : nat) (U : 'M[F]_(m, n)).

Definition rstabs := [set x in G | U *m rG x <= U]%MS.

Definition mxmodule := G \subset rstabs.

End Stabilisers.

Definition mxsimple (V : 'M_n) :=
  [/\ mxmodule V, V != 0 &
      forall U : 'M_n, mxmodule U -> (U <= V)%MS -> U != 0 -> (V <= U)%MS].

Definition mx_irreducible := mxsimple 1%:M.

End OneRepresentation.

End FieldRepr.

Record gen_of {F : fieldType} {gT : finGroupType} {G : {group gT}} {n' : nat}
              {rG : mx_representation F G n'.+1} {A : 'M[F]_n'.+1}
              (irrG : mx_irreducible rG) (cGA : centgmx rG A) :=
   Gen {rVval : 'rV[F]_(degree_mxminpoly A)}.

Local Arguments rVval {F gT G%G n'%N rG A%R irrG cGA} x%R : rename.

Section GenField.

Variables (F : fieldType) (gT : finGroupType) (G : {group gT}) (n' : nat).
Local Notation n := n'.+1.
Variables (rG : mx_representation F G n) (A : 'M[F]_n).

Local Notation d := (degree_mxminpoly A).
Local Notation pA := (mxminpoly A).
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
admit.
Defined.

Lemma gen_addC : commutative genD.
admit.
Defined.

Lemma gen_add0r : left_id gen0 genD.
admit.
Defined.

Lemma gen_addNr : left_inverse gen0 genN genD.
admit.
Defined.

Definition gen_zmodMixin := ZmodMixin gen_addA gen_addC gen_add0r gen_addNr.
Canonical gen_zmodType := Eval hnf in ZmodType FA gen_zmodMixin.

Definition pval (x : FA) := rVpoly (val x).

Definition mxval (x : FA) := horner_mx A (pval x).

Definition gen1 := inFA (poly_rV 1).
Definition genM x y := inFA (poly_rV (pval x * pval y %% pA)).
Definition genV x := inFA (poly_rV (mx_inv_horner A (mxval x)^-1)).

Lemma gen_mulA : associative genM.
admit.
Defined.

Lemma gen_mulC : commutative genM.
admit.
Defined.

Lemma gen_mul1r : left_id gen1 genM.
admit.
Defined.

Lemma gen_mulDr : left_distributive genM +%R.
admit.
Defined.

Lemma gen_ntriv : gen1 != 0.
admit.
Defined.

Definition gen_ringMixin :=
  ComRingMixin gen_mulA gen_mulC gen_mul1r gen_mulDr gen_ntriv.
Canonical gen_ringType := Eval hnf in RingType FA gen_ringMixin.
Canonical gen_comRingType := Eval hnf in ComRingType FA gen_mulC.

Lemma gen_mulVr : GRing.Field.axiom genV.
admit.
Defined.

Lemma gen_invr0 : genV 0 = 0.
admit.
Defined.

Definition gen_unitRingMixin := FieldUnitMixin gen_mulVr gen_invr0.
Canonical gen_unitRingType :=
  Eval hnf in UnitRingType FA gen_unitRingMixin.

End GenField.

Variable F : decFieldType.
Local Notation Bool b := (GRing.Bool b%bool).

Variables (gT : finGroupType) (G : {group gT}) (n' : nat).
Local Notation n := n'.+1.
Variables (rG : mx_representation F G n) (A : 'M[F]_n).
Hypotheses (irrG : mx_irreducible rG) (cGA : centgmx rG A).
Local Notation FA := (gen_of irrG cGA).
Local Notation inFA := (Gen irrG cGA).

Local Notation d := (degree_mxminpoly A).
Local Notation Ad := (powers_mx A d).

Let mxT (u : 'rV_d) := vec_mx (mulmx_term u (mx_term Ad)).

Let Ad'T := mx_term (pinvmx Ad).
Let mulT (u v : 'rV_d) := mulmx_term (mxvec (mulmx_term (mxT u) (mxT v))) Ad'T.

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

Lemma set_nth_map_rVval (e : seq FA) j v :
  set_nth 0 (map val e) j v = map val (set_nth 0 e j (inFA v)).
admit.
Defined.

Lemma eval_gen_term e t :
  GRing.rterm t -> eval_mx (gen_env e) (gen_term t) = val (GRing.eval e t).
admit.
Defined.

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
