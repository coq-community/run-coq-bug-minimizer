(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "-projection-no-head-constant" "-w" "-redundant-canonical-projection" "-w" "-notation-overridden" "-w" "+duplicate-clear" "-w" "-ambiguous-paths" "-w" "+non-primitive-record" "-w" "+undeclared-scope" "-w" "-deprecated-hint-without-locality" "-w" "-deprecated-ident-entry" "-w" "-deprecated-native-compiler-option" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/mathcomp/mathcomp" "mathcomp" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-I" "/github/workspace/builds/coq/coq-failing/_build_ci/mathcomp/mathcomp" "-top" "bug_01" "-native-compiler" "ondemand") -*- *)
(* File reduced by coq-bug-finder from original input, then from 5976 lines to 4914 lines, then from 4559 lines to 258 lines, then from 312 lines to 2285 lines, then from 2290 lines to 373 lines, then from 425 lines to 3660 lines, then from 3664 lines to 414 lines, then from 465 lines to 3264 lines, then from 3269 lines to 2886 lines, then from 2755 lines to 611 lines, then from 662 lines to 3802 lines, then from 3807 lines to 646 lines, then from 696 lines to 5297 lines, then from 5302 lines to 5208 lines *)
(* coqc version 8.15+alpha compiled with OCaml 4.13.0
   coqtop version runner-0277ea0f-project-6138686-concurrent-0:/builds/coq/coq/_build/default,(HEAD detached at 3aaf20f) (3aaf20f513cc7b2633d7aed182d34a363fcb5dfa)
   Expected coqc runtime on this file: 3.514 sec *)
Declare ML Module "ltac_plugin".
Module Export AdmitTactic.
Module Import LocalFalse.
Inductive False : Prop := .
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
Module Export mathcomp_DOT_algebra_DOT_matrix_WRAPPED.
Module Export matrix.
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
Import mathcomp.algebra.countalg.

 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.
Import GRing.Theory.
Local Open Scope ring_scope.

Reserved Notation "''M_' n"     (at level 8, n at level 2, format "''M_' n").
Reserved Notation "''rV_' n"    (at level 8, n at level 2, format "''rV_' n").
Reserved Notation "''cV_' n"    (at level 8, n at level 2, format "''cV_' n").
Reserved Notation "''M_' ( n )" (at level 8).
 
Reserved Notation "''M_' ( m , n )" (at level 8, format "''M_' ( m ,  n )").
Reserved Notation "''M[' R ]_ n"    (at level 8, n at level 2).
 
Reserved Notation "''rV[' R ]_ n"   (at level 8, n at level 2).
 
Reserved Notation "''cV[' R ]_ n"   (at level 8, n at level 2).
 
Reserved Notation "''M[' R ]_ ( n )"     (at level 8).
 
Reserved Notation "''M[' R ]_ ( m , n )" (at level 8).
 

Reserved Notation "\matrix_ i E"
  (at level 36, E at level 36, i at level 2,
   format "\matrix_ i  E").
Reserved Notation "\matrix_ ( i < n ) E"
  (at level 36, E at level 36, i, n at level 50).
 
Reserved Notation "\matrix_ ( i , j ) E"
  (at level 36, E at level 36, i, j at level 50,
   format "\matrix_ ( i ,  j )  E").
Reserved Notation "\matrix[ k ]_ ( i , j ) E"
  (at level 36, E at level 36, i, j at level 50,
   format "\matrix[ k ]_ ( i ,  j )  E").
Reserved Notation "\matrix_ ( i < m , j < n ) E"
  (at level 36, E at level 36, i, m, j, n at level 50).
 
Reserved Notation "\matrix_ ( i , j < n ) E"
  (at level 36, E at level 36, i, j, n at level 50).
 
Reserved Notation "\row_ j E"
  (at level 36, E at level 36, j at level 2,
   format "\row_ j  E").
Reserved Notation "\row_ ( j < n ) E"
  (at level 36, E at level 36, j, n at level 50).
 
Reserved Notation "\col_ j E"
  (at level 36, E at level 36, j at level 2,
   format "\col_ j  E").
Reserved Notation "\col_ ( j < n ) E"
  (at level 36, E at level 36, j, n at level 50).
 
Reserved Notation "\mxblock_ ( i , j ) E"
  (at level 36, E at level 36, i, j at level 50,
   format "\mxblock_ ( i ,  j )  E").
Reserved Notation "\mxblock_ ( i < m , j < n ) E"
  (at level 36, E at level 36, i, m, j, n at level 50).
 
Reserved Notation "\mxblock_ ( i , j < n ) E"
  (at level 36, E at level 36, i, j, n at level 50).
 
Reserved Notation "\mxrow_ j E"
  (at level 36, E at level 36, j at level 2,
   format "\mxrow_ j  E").
Reserved Notation "\mxrow_ ( j < n ) E"
  (at level 36, E at level 36, j, n at level 50).
 
Reserved Notation "\mxcol_ j E"
  (at level 36, E at level 36, j at level 2,
   format "\mxcol_ j  E").
Reserved Notation "\mxcol_ ( j < n ) E"
  (at level 36, E at level 36, j, n at level 50).
 
Reserved Notation "\mxdiag_ j E"
  (at level 36, E at level 36, j at level 2,
   format "\mxdiag_ j  E").
Reserved Notation "\mxdiag_ ( j < n ) E"
  (at level 36, E at level 36, j, n at level 50).
 

Reserved Notation "x %:M"   (at level 8, format "x %:M").
Reserved Notation "A *m B" (at level 40, left associativity, format "A  *m  B").
Reserved Notation "A ^T"    (at level 8, format "A ^T").
Reserved Notation "\tr A"   (at level 10, A at level 8, format "\tr  A").
Reserved Notation "\det A"  (at level 10, A at level 8, format "\det  A").
Reserved Notation "\adj A"  (at level 10, A at level 8, format "\adj  A").

Local Notation simp := (Monoid.Theory.simpm, oppr0).

 
 
 

Section MatrixDef.

Variable R : Type.
Variables m n : nat.

 
 
 

Variant matrix : predArgType := Matrix of {ffun 'I_m * 'I_n -> R}.

Definition mx_val A := let: Matrix g := A in g.

Canonical matrix_subType := Eval hnf in [newType for mx_val].

Fact matrix_key : unit.
admit.
Defined.
Definition matrix_of_fun_def F := Matrix [ffun ij => F ij.1 ij.2].
Definition matrix_of_fun k := locked_with k matrix_of_fun_def.
Canonical matrix_unlockable k := [unlockable fun matrix_of_fun k].

Definition fun_of_matrix A (i : 'I_m) (j : 'I_n) := mx_val A (i, j).

Coercion fun_of_matrix : matrix >-> Funclass.

Lemma mxE k F : matrix_of_fun k F =2 F.
admit.
Defined.

Lemma matrixP (A B : matrix) : A =2 B <-> A = B.
admit.
Defined.

Lemma eq_mx k F1 F2 : (F1 =2 F2) -> matrix_of_fun k F1 = matrix_of_fun k F2.
admit.
Defined.

End MatrixDef.

Arguments eq_mx {R m n k} [F1] F2 eq_F12.

Bind Scope ring_scope with matrix.

Notation "''M[' R ]_ ( m , n )" := (matrix R m n) (only parsing): type_scope.
Notation "''rV[' R ]_ n" := 'M[R]_(1, n) (only parsing) : type_scope.
Notation "''cV[' R ]_ n" := 'M[R]_(n, 1) (only parsing) : type_scope.
Notation "''M[' R ]_ n" := 'M[R]_(n, n) (only parsing) : type_scope.
Notation "''M[' R ]_ ( n )" := 'M[R]_n (only parsing) : type_scope.
Notation "''M_' ( m , n )" := 'M[_]_(m, n) : type_scope.
Notation "''rV_' n" := 'M_(1, n) : type_scope.
Notation "''cV_' n" := 'M_(n, 1) : type_scope.
Notation "''M_' n" := 'M_(n, n) : type_scope.
Notation "''M_' ( n )" := 'M_n (only parsing) : type_scope.

Notation "\matrix[ k ]_ ( i , j ) E" := (matrix_of_fun k (fun i j => E)) :
   ring_scope.

Notation "\matrix_ ( i < m , j < n ) E" :=
  (@matrix_of_fun _ m n matrix_key (fun i j => E)) (only parsing) : ring_scope.

Notation "\matrix_ ( i , j < n ) E" :=
  (\matrix_(i < n, j < n) E) (only parsing) : ring_scope.

Notation "\matrix_ ( i , j ) E" := (\matrix_(i < _, j < _) E) : ring_scope.

Notation "\matrix_ ( i < m ) E" :=
  (\matrix_(i < m, j < _) @fun_of_matrix _ 1 _ E 0 j)
  (only parsing) : ring_scope.
Notation "\matrix_ i E" := (\matrix_(i < _) E) : ring_scope.

Notation "\col_ ( i < n ) E" := (@matrix_of_fun _ n 1 matrix_key (fun i _ => E))
  (only parsing) : ring_scope.
Notation "\col_ i E" := (\col_(i < _) E) : ring_scope.

Notation "\row_ ( j < n ) E" := (@matrix_of_fun _ 1 n matrix_key (fun _ j => E))
  (only parsing) : ring_scope.
Notation "\row_ j E" := (\row_(j < _) E) : ring_scope.

Definition matrix_eqMixin (R : eqType) m n :=
  Eval hnf in [eqMixin of 'M[R]_(m, n) by <:].
Canonical matrix_eqType (R : eqType) m n:=
  Eval hnf in EqType 'M[R]_(m, n) (matrix_eqMixin R m n).
Definition matrix_choiceMixin (R : choiceType) m n :=
  [choiceMixin of 'M[R]_(m, n) by <:].
Canonical matrix_choiceType (R : choiceType) m n :=
  Eval hnf in ChoiceType 'M[R]_(m, n) (matrix_choiceMixin R m n).
Definition matrix_countMixin (R : countType) m n :=
  [countMixin of 'M[R]_(m, n) by <:].
Canonical matrix_countType (R : countType) m n :=
  Eval hnf in CountType 'M[R]_(m, n) (matrix_countMixin R m n).
Canonical matrix_subCountType (R : countType) m n :=
  Eval hnf in [subCountType of 'M[R]_(m, n)].
Definition matrix_finMixin (R : finType) m n :=
  [finMixin of 'M[R]_(m, n) by <:].
Canonical matrix_finType (R : finType) m n :=
  Eval hnf in FinType 'M[R]_(m, n) (matrix_finMixin R m n).
Canonical matrix_subFinType (R : finType) m n :=
  Eval hnf in [subFinType of 'M[R]_(m, n)].

Lemma card_mx (F : finType) m n : (#|{: 'M[F]_(m, n)}| = #|F| ^ (m * n))%N.
admit.
Defined.

#[deprecated(since="mathcomp 1.13.0", note="Use card_mx instead.")]
Notation card_matrix := card_mx.

 
 
 

Section MatrixStructural.

Variable R : Type.

 
Fact const_mx_key : unit.
admit.
Defined.
Definition const_mx m n a : 'M[R]_(m, n) := \matrix[const_mx_key]_(i, j) a.
Arguments const_mx {m n}.

Section FixedDim.
 

Variables m n : nat.
Implicit Type A : 'M[R]_(m, n).

 
Definition castmx m' n' (eq_mn : (m = m') * (n = n')) A : 'M_(m', n') :=
  let: erefl in _ = m' := eq_mn.1 return 'M_(m', n') in
  let: erefl in _ = n' := eq_mn.2 return 'M_(m, n') in A.

Definition conform_mx m' n' B A :=
  match m =P m', n =P n' with
  | ReflectT eq_m, ReflectT eq_n => castmx (eq_m, eq_n) A
  | _, _ => B
  end.

 
Fact trmx_key : unit.
admit.
Defined.
Definition trmx A := \matrix[trmx_key]_(i, j) A j i.

 
Fact row_perm_key : unit.
admit.
Defined.
Definition row_perm (s : 'S_m) A := \matrix[row_perm_key]_(i, j) A (s i) j.
Fact col_perm_key : unit.
admit.
Defined.
Definition col_perm (s : 'S_n) A := \matrix[col_perm_key]_(i, j) A i (s j).

 
Definition xrow i1 i2 := row_perm (tperm i1 i2).
Definition xcol j1 j2 := col_perm (tperm j1 j2).

 
Definition row i0 A := \row_j A i0 j.
Definition col j0 A := \col_i A i j0.

 
Definition row' i0 A := \matrix_(i, j) A (lift i0 i) j.
Definition col' j0 A := \matrix_(i, j) A i (lift j0 j).

 
Definition mxsub m' n' f g A := \matrix_(i < m', j < n') A (f i) (g j).
Local Notation colsub g := (mxsub id g).
Local Notation rowsub f := (mxsub f id).

Lemma castmx_const m' n' (eq_mn : (m = m') * (n = n')) a :
  castmx eq_mn (const_mx a) = const_mx a.
admit.
Defined.

Lemma trmx_const a : trmx (const_mx a) = const_mx a.
admit.
Defined.

Lemma row_perm_const s a : row_perm s (const_mx a) = const_mx a.
admit.
Defined.

Lemma col_perm_const s a : col_perm s (const_mx a) = const_mx a.
admit.
Defined.

Lemma xrow_const i1 i2 a : xrow i1 i2 (const_mx a) = const_mx a.
admit.
Defined.

Lemma xcol_const j1 j2 a : xcol j1 j2 (const_mx a) = const_mx a.
admit.
Defined.

Lemma rowP (u v : 'rV[R]_n) : u 0 =1 v 0 <-> u = v.
admit.
Defined.

Lemma rowK u_ i0 : row i0 (\matrix_i u_ i) = u_ i0.
admit.
Defined.

Lemma row_matrixP A B : (forall i, row i A = row i B) <-> A = B.
admit.
Defined.

Lemma colP (u v : 'cV[R]_m) : u^~ 0 =1 v^~ 0 <-> u = v.
admit.
Defined.

Lemma row_const i0 a : row i0 (const_mx a) = const_mx a.
admit.
Defined.

Lemma col_const j0 a : col j0 (const_mx a) = const_mx a.
admit.
Defined.

Lemma row'_const i0 a : row' i0 (const_mx a) = const_mx a.
admit.
Defined.

Lemma col'_const j0 a : col' j0 (const_mx a) = const_mx a.
admit.
Defined.

Lemma col_perm1 A : col_perm 1 A = A.
admit.
Defined.

Lemma row_perm1 A : row_perm 1 A = A.
admit.
Defined.

Lemma col_permM s t A : col_perm (s * t) A = col_perm s (col_perm t A).
admit.
Defined.

Lemma row_permM s t A : row_perm (s * t) A = row_perm s (row_perm t A).
admit.
Defined.

Lemma col_row_permC s t A :
  col_perm s (row_perm t A) = row_perm t (col_perm s A).
admit.
Defined.

Lemma rowEsub i : row i = rowsub (fun=> i).
admit.
Defined.
Lemma colEsub j : col j = colsub (fun=> j).
admit.
Defined.

Lemma row'Esub i : row' i = rowsub (lift i).
admit.
Defined.
Lemma col'Esub j : col' j = colsub (lift j).
admit.
Defined.

Lemma row_permEsub s : row_perm s = rowsub s.
admit.
Defined.

Lemma col_permEsub s : col_perm s = colsub s.
admit.
Defined.

Lemma xrowEsub i1 i2 : xrow i1 i2 = rowsub (tperm i1 i2).
admit.
Defined.

Lemma xcolEsub j1 j2 : xcol j1 j2 = colsub (tperm j1 j2).
admit.
Defined.

Lemma mxsub_id : mxsub id id =1 id.
admit.
Defined.

Lemma eq_mxsub m' n' f f' g g' : f =1 f' -> g =1 g' ->
  @mxsub m' n' f g =1 mxsub f' g'.
admit.
Defined.

Lemma eq_rowsub m' (f f' : 'I_m' -> 'I_m) : f =1 f' -> rowsub f =1 rowsub f'.
admit.
Defined.

Lemma eq_colsub n' (g g' : 'I_n' -> 'I_n) : g =1 g' -> colsub g =1 colsub g'.
admit.
Defined.

Lemma mxsub_eq_id f g : f =1 id -> g =1 id -> mxsub f g =1 id.
admit.
Defined.

Lemma mxsub_eq_colsub n' f g : f =1 id -> @mxsub _ n' f g =1 colsub g.
admit.
Defined.

Lemma mxsub_eq_rowsub m' f g : g =1 id -> @mxsub m' _ f g =1 rowsub f.
admit.
Defined.

Lemma mxsub_ffunl m' n' f g : @mxsub m' n' (finfun f) g =1 mxsub f g.
admit.
Defined.

Lemma mxsub_ffunr m' n' f g : @mxsub m' n' f (finfun g) =1 mxsub f g.
admit.
Defined.

Lemma mxsub_ffun m' n' f g : @mxsub m' n' (finfun f) (finfun g) =1 mxsub f g.
admit.
Defined.

Lemma mxsub_const m' n' f g a : @mxsub m' n' f g (const_mx a) = const_mx a.
admit.
Defined.

End FixedDim.

Local Notation colsub g := (mxsub id g).
Local Notation rowsub f := (mxsub f id).
Local Notation "A ^T" := (trmx A) : ring_scope.

Lemma castmx_id m n erefl_mn (A : 'M_(m, n)) : castmx erefl_mn A = A.
admit.
Defined.

Lemma castmx_comp m1 n1 m2 n2 m3 n3 (eq_m1 : m1 = m2) (eq_n1 : n1 = n2)
                                    (eq_m2 : m2 = m3) (eq_n2 : n2 = n3) A :
  castmx (eq_m2, eq_n2) (castmx (eq_m1, eq_n1) A)
    = castmx (etrans eq_m1 eq_m2, etrans eq_n1 eq_n2) A.
admit.
Defined.

Lemma castmxK m1 n1 m2 n2 (eq_m : m1 = m2) (eq_n : n1 = n2) :
  cancel (castmx (eq_m, eq_n)) (castmx (esym eq_m, esym eq_n)).
admit.
Defined.

Lemma castmxKV m1 n1 m2 n2 (eq_m : m1 = m2) (eq_n : n1 = n2) :
  cancel (castmx (esym eq_m, esym eq_n)) (castmx (eq_m, eq_n)).
admit.
Defined.

 
Lemma castmx_sym m1 n1 m2 n2 (eq_m : m1 = m2) (eq_n : n1 = n2) A1 A2 :
  A1 = castmx (eq_m, eq_n) A2 -> A2 = castmx (esym eq_m, esym eq_n) A1.
admit.
Defined.

Lemma eq_castmx m1 n1 m2 n2 (eq_mn eq_mn' : (m1 = m2) * (n1 = n2)) :
  castmx eq_mn =1 castmx eq_mn'.
admit.
Defined.

Lemma castmxE m1 n1 m2 n2 (eq_mn : (m1 = m2) * (n1 = n2)) A i j :
  castmx eq_mn A i j =
     A (cast_ord (esym eq_mn.1) i) (cast_ord (esym eq_mn.2) j).
admit.
Defined.

Lemma conform_mx_id m n (B A : 'M_(m, n)) : conform_mx B A = A.
admit.
Defined.

Lemma nonconform_mx m m' n n' (B : 'M_(m', n')) (A : 'M_(m, n)) :
  (m != m') || (n != n') -> conform_mx B A = B.
admit.
Defined.

Lemma conform_castmx m1 n1 m2 n2 m3 n3
                     (e_mn : (m2 = m3) * (n2 = n3)) (B : 'M_(m1, n1)) A :
  conform_mx B (castmx e_mn A) = conform_mx B A.
admit.
Defined.

Lemma trmxK m n : cancel (@trmx m n) (@trmx n m).
admit.
Defined.

Lemma trmx_inj m n : injective (@trmx m n).
admit.
Defined.

Lemma trmx_cast m1 n1 m2 n2 (eq_mn : (m1 = m2) * (n1 = n2)) A :
  (castmx eq_mn A)^T = castmx (eq_mn.2, eq_mn.1) A^T.
admit.
Defined.

Lemma trmx_conform m' n' m n (B : 'M_(m', n')) (A : 'M_(m, n)) :
  (conform_mx B A)^T = conform_mx B^T A^T.
admit.
Defined.

Lemma tr_row_perm m n s (A : 'M_(m, n)) : (row_perm s A)^T = col_perm s A^T.
admit.
Defined.

Lemma tr_col_perm m n s (A : 'M_(m, n)) : (col_perm s A)^T = row_perm s A^T.
admit.
Defined.

Lemma tr_xrow m n i1 i2 (A : 'M_(m, n)) : (xrow i1 i2 A)^T = xcol i1 i2 A^T.
admit.
Defined.

Lemma tr_xcol m n j1 j2 (A : 'M_(m, n)) : (xcol j1 j2 A)^T = xrow j1 j2 A^T.
admit.
Defined.

Lemma row_id n i (V : 'rV_n) : row i V = V.
admit.
Defined.

Lemma col_id n j (V : 'cV_n) : col j V = V.
admit.
Defined.

Lemma row_eq m1 m2 n i1 i2 (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)) :
  row i1 A1 = row i2 A2 -> A1 i1 =1 A2 i2.
admit.
Defined.

Lemma col_eq m n1 n2 j1 j2 (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)) :
  col j1 A1 = col j2 A2 -> A1^~ j1 =1 A2^~ j2.
admit.
Defined.

Lemma row'_eq m n i0 (A B : 'M_(m, n)) :
  row' i0 A = row' i0 B -> {in predC1 i0, A =2 B}.
admit.
Defined.

Lemma col'_eq m n j0 (A B : 'M_(m, n)) :
  col' j0 A = col' j0 B -> forall i, {in predC1 j0, A i =1 B i}.
admit.
Defined.

Lemma tr_row m n i0 (A : 'M_(m, n)) : (row i0 A)^T = col i0 A^T.
admit.
Defined.

Lemma tr_row' m n i0 (A : 'M_(m, n)) : (row' i0 A)^T = col' i0 A^T.
admit.
Defined.

Lemma tr_col m n j0 (A : 'M_(m, n)) : (col j0 A)^T = row j0 A^T.
admit.
Defined.

Lemma tr_col' m n j0 (A : 'M_(m, n)) : (col' j0 A)^T = row' j0 A^T.
admit.
Defined.

Lemma mxsub_comp m1 m2 m3 n1 n2 n3
  (f : 'I_m2 -> 'I_m1) (f' : 'I_m3 -> 'I_m2)
  (g : 'I_n2 -> 'I_n1) (g' : 'I_n3 -> 'I_n2) (A : 'M_(m1, n1)) :
  mxsub (f \o f') (g \o g') A = mxsub f' g' (mxsub f g A).
admit.
Defined.

Lemma rowsub_comp m1 m2 m3 n
  (f : 'I_m2 -> 'I_m1) (f' : 'I_m3 -> 'I_m2) (A : 'M_(m1, n)) :
  rowsub (f \o f') A = rowsub f' (rowsub f A).
admit.
Defined.

Lemma colsub_comp m n n2 n3
  (g : 'I_n2 -> 'I_n) (g' : 'I_n3 -> 'I_n2) (A : 'M_(m, n)) :
  colsub (g \o g') A = colsub g' (colsub g A).
admit.
Defined.

Lemma mxsubrc m1 m2 n n2 f g (A : 'M_(m1, n)) :
  mxsub f g A = rowsub f (colsub g A) :> 'M_(m2, n2).
admit.
Defined.

Lemma mxsubcr m1 m2 n n2 f g (A : 'M_(m1, n)) :
  mxsub f g A = colsub g (rowsub f A) :> 'M_(m2, n2).
admit.
Defined.

Lemma rowsub_cast m1 m2 n (eq_m : m1 = m2) (A : 'M_(m2, n)) :
  rowsub (cast_ord eq_m) A = castmx (esym eq_m, erefl) A.
admit.
Defined.

Lemma colsub_cast m n1 n2 (eq_n : n1 = n2) (A : 'M_(m, n2)) :
  colsub (cast_ord eq_n) A = castmx (erefl, esym eq_n) A.
admit.
Defined.

Lemma mxsub_cast m1 m2 n1 n2 (eq_m : m1 = m2) (eq_n : n1 = n2) A :
  mxsub (cast_ord eq_m) (cast_ord eq_n) A = castmx (esym eq_m, esym eq_n) A.
admit.
Defined.

Lemma castmxEsub m1 m2 n1 n2 (eq_mn : (m1 = m2) * (n1 = n2)) A :
  castmx eq_mn A = mxsub (cast_ord (esym eq_mn.1)) (cast_ord (esym eq_mn.2)) A.
admit.
Defined.

Lemma trmx_mxsub m1 m2 n1 n2 f g (A : 'M_(m1, n1)) :
  (mxsub f g A)^T = mxsub g f A^T :> 'M_(n2, m2).
admit.
Defined.

Lemma row_mxsub m1 m2 n1 n2
    (f : 'I_m2 -> 'I_m1) (g : 'I_n2 -> 'I_n1) (A : 'M_(m1, n1)) i :
  row i (mxsub f g A) = row (f i) (colsub g A).
admit.
Defined.

Lemma col_mxsub m1 m2 n1 n2
    (f : 'I_m2 -> 'I_m1) (g : 'I_n2 -> 'I_n1) (A : 'M_(m1, n1)) i :
 col i (mxsub f g A) = col (g i) (rowsub f A).
admit.
Defined.

Lemma row_rowsub m1 m2 n (f : 'I_m2 -> 'I_m1) (A : 'M_(m1, n)) i :
  row i (rowsub f A) = row (f i) A.
admit.
Defined.

Lemma col_colsub m n1 n2 (g : 'I_n2 -> 'I_n1) (A : 'M_(m, n1)) i :
  col i (colsub g A) = col (g i) A.
admit.
Defined.

Section CutPaste.

Variables m m1 m2 n n1 n2 : nat.

 

Fact row_mx_key : unit.
admit.
Defined.
Definition row_mx (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)) : 'M[R]_(m, n1 + n2) :=
  \matrix[row_mx_key]_(i, j)
     match split j with inl j1 => A1 i j1 | inr j2 => A2 i j2 end.

Fact col_mx_key : unit.
admit.
Defined.
Definition col_mx (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)) : 'M[R]_(m1 + m2, n) :=
  \matrix[col_mx_key]_(i, j)
     match split i with inl i1 => A1 i1 j | inr i2 => A2 i2 j end.

 
 
 

Fact lsubmx_key : unit.
admit.
Defined.
Definition lsubmx (A : 'M[R]_(m, n1 + n2)) :=
  \matrix[lsubmx_key]_(i, j) A i (lshift n2 j).

Fact rsubmx_key : unit.
admit.
Defined.
Definition rsubmx (A : 'M[R]_(m, n1 + n2)) :=
  \matrix[rsubmx_key]_(i, j) A i (rshift n1 j).

Fact usubmx_key : unit.
admit.
Defined.
Definition usubmx (A : 'M[R]_(m1 + m2, n)) :=
  \matrix[usubmx_key]_(i, j) A (lshift m2 i) j.

Fact dsubmx_key : unit.
admit.
Defined.
Definition dsubmx (A : 'M[R]_(m1 + m2, n)) :=
  \matrix[dsubmx_key]_(i, j) A (rshift m1 i) j.

Lemma row_mxEl A1 A2 i j : row_mx A1 A2 i (lshift n2 j) = A1 i j.
admit.
Defined.

Lemma row_mxKl A1 A2 : lsubmx (row_mx A1 A2) = A1.
admit.
Defined.

Lemma row_mxEr A1 A2 i j : row_mx A1 A2 i (rshift n1 j) = A2 i j.
admit.
Defined.

Lemma row_mxKr A1 A2 : rsubmx (row_mx A1 A2) = A2.
admit.
Defined.

Lemma hsubmxK A : row_mx (lsubmx A) (rsubmx A) = A.
admit.
Defined.

Lemma col_mxEu A1 A2 i j : col_mx A1 A2 (lshift m2 i) j = A1 i j.
admit.
Defined.

Lemma col_mxKu A1 A2 : usubmx (col_mx A1 A2) = A1.
admit.
Defined.

Lemma col_mxEd A1 A2 i j : col_mx A1 A2 (rshift m1 i) j = A2 i j.
admit.
Defined.

Lemma col_mxKd A1 A2 : dsubmx (col_mx A1 A2) = A2.
admit.
Defined.

Lemma lsubmxEsub : lsubmx = colsub (lshift _).
admit.
Defined.

Lemma rsubmxEsub : rsubmx = colsub (@rshift _ _).
admit.
Defined.

Lemma usubmxEsub : usubmx = rowsub (lshift _).
admit.
Defined.

Lemma dsubmxEsub  : dsubmx = rowsub (@rshift _ _).
admit.
Defined.

Lemma eq_row_mx A1 A2 B1 B2 : row_mx A1 A2 = row_mx B1 B2 -> A1 = B1 /\ A2 = B2.
admit.
Defined.

Lemma eq_col_mx A1 A2 B1 B2 : col_mx A1 A2 = col_mx B1 B2 -> A1 = B1 /\ A2 = B2.
admit.
Defined.

Lemma row_mx_const a : row_mx (const_mx a) (const_mx a) = const_mx a.
admit.
Defined.

Lemma col_mx_const a : col_mx (const_mx a) (const_mx a) = const_mx a.
admit.
Defined.

Lemma row_usubmx A i : row i (usubmx A) = row (lshift m2 i) A.
admit.
Defined.

Lemma row_dsubmx A i : row i (dsubmx A) = row (rshift m1 i) A.
admit.
Defined.

Lemma col_lsubmx A i : col i (lsubmx A) = col (lshift n2 i) A.
admit.
Defined.

Lemma col_rsubmx A i : col i (rsubmx A) = col (rshift n1 i) A.
admit.
Defined.

End CutPaste.

Lemma row_thin_mx m n (A : 'M_(m,0)) (B : 'M_(m,n)) : row_mx A B = B.
admit.
Defined.

Lemma col_flat_mx m n (A : 'M_(0,n)) (B : 'M_(m,n)) : col_mx A B = B.
admit.
Defined.

Lemma trmx_lsub m n1 n2 (A : 'M_(m, n1 + n2)) : (lsubmx A)^T = usubmx A^T.
admit.
Defined.

Lemma trmx_rsub m n1 n2 (A : 'M_(m, n1 + n2)) : (rsubmx A)^T = dsubmx A^T.
admit.
Defined.

Lemma tr_row_mx m n1 n2 (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)) :
  (row_mx A1 A2)^T = col_mx A1^T A2^T.
admit.
Defined.

Lemma tr_col_mx m1 m2 n (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)) :
  (col_mx A1 A2)^T = row_mx A1^T A2^T.
admit.
Defined.

Lemma trmx_usub m1 m2 n (A : 'M_(m1 + m2, n)) : (usubmx A)^T = lsubmx A^T.
admit.
Defined.

Lemma trmx_dsub m1 m2 n (A : 'M_(m1 + m2, n)) : (dsubmx A)^T = rsubmx A^T.
admit.
Defined.

Lemma vsubmxK m1 m2 n (A : 'M_(m1 + m2, n)) : col_mx (usubmx A) (dsubmx A) = A.
admit.
Defined.

Lemma cast_row_mx m m' n1 n2 (eq_m : m = m') A1 A2 :
  castmx (eq_m, erefl _) (row_mx A1 A2)
    = row_mx (castmx (eq_m, erefl n1) A1) (castmx (eq_m, erefl n2) A2).
admit.
Defined.

Lemma cast_col_mx m1 m2 n n' (eq_n : n = n') A1 A2 :
  castmx (erefl _, eq_n) (col_mx A1 A2)
    = col_mx (castmx (erefl m1, eq_n) A1) (castmx (erefl m2, eq_n) A2).
admit.
Defined.

 
Lemma row_mxA m n1 n2 n3 (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)) (A3 : 'M_(m, n3)) :
  let cast := (erefl m, esym (addnA n1 n2 n3)) in
  row_mx A1 (row_mx A2 A3) = castmx cast (row_mx (row_mx A1 A2) A3).
admit.
Defined.
Definition row_mxAx := row_mxA.
 

 
Lemma col_mxA m1 m2 m3 n (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)) (A3 : 'M_(m3, n)) :
  let cast := (esym (addnA m1 m2 m3), erefl n) in
  col_mx A1 (col_mx A2 A3) = castmx cast (col_mx (col_mx A1 A2) A3).
admit.
Defined.
Definition col_mxAx := col_mxA.
 

Lemma row_row_mx m n1 n2 i0 (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)) :
  row i0 (row_mx A1 A2) = row_mx (row i0 A1) (row i0 A2).
admit.
Defined.

Lemma col_col_mx m1 m2 n j0 (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)) :
  col j0 (col_mx A1 A2) = col_mx (col j0 A1) (col j0 A2).
admit.
Defined.

Lemma row'_row_mx m n1 n2 i0 (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)) :
  row' i0 (row_mx A1 A2) = row_mx (row' i0 A1) (row' i0 A2).
admit.
Defined.

Lemma col'_col_mx m1 m2 n j0 (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)) :
  col' j0 (col_mx A1 A2) = col_mx (col' j0 A1) (col' j0 A2).
admit.
Defined.

Lemma colKl m n1 n2 j1 (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)) :
  col (lshift n2 j1) (row_mx A1 A2) = col j1 A1.
admit.
Defined.

Lemma colKr m n1 n2 j2 (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)) :
  col (rshift n1 j2) (row_mx A1 A2) = col j2 A2.
admit.
Defined.

Lemma rowKu m1 m2 n i1 (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)) :
  row (lshift m2 i1) (col_mx A1 A2) = row i1 A1.
admit.
Defined.

Lemma rowKd m1 m2 n i2 (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)) :
  row (rshift m1 i2) (col_mx A1 A2) = row i2 A2.
admit.
Defined.

Lemma col'Kl m n1 n2 j1 (A1 : 'M_(m, n1.+1)) (A2 : 'M_(m, n2)) :
  col' (lshift n2 j1) (row_mx A1 A2) = row_mx (col' j1 A1) A2.
admit.
Defined.

Lemma row'Ku m1 m2 n i1 (A1 : 'M_(m1.+1, n)) (A2 : 'M_(m2, n)) :
  row' (lshift m2 i1) (@col_mx m1.+1 m2 n A1 A2) = col_mx (row' i1 A1) A2.
admit.
Defined.

Lemma mx'_cast m n : 'I_n -> (m + n.-1)%N = (m + n).-1.
admit.
Defined.

Lemma col'Kr m n1 n2 j2 (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)) :
  col' (rshift n1 j2) (@row_mx m n1 n2 A1 A2)
    = castmx (erefl m, mx'_cast n1 j2) (row_mx A1 (col' j2 A2)).
admit.
Defined.

Lemma row'Kd m1 m2 n i2 (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)) :
  row' (rshift m1 i2) (col_mx A1 A2)
    = castmx (mx'_cast m1 i2, erefl n) (col_mx A1 (row' i2 A2)).
admit.
Defined.

Section Block.

Variables m1 m2 n1 n2 : nat.

 
 

Definition block_mx Aul Aur Adl Adr : 'M_(m1 + m2, n1 + n2) :=
  col_mx (row_mx Aul Aur) (row_mx Adl Adr).

Lemma eq_block_mx Aul Aur Adl Adr Bul Bur Bdl Bdr :
 block_mx Aul Aur Adl Adr = block_mx Bul Bur Bdl Bdr ->
  [/\ Aul = Bul, Aur = Bur, Adl = Bdl & Adr = Bdr].
admit.
Defined.

Lemma block_mx_const a :
  block_mx (const_mx a) (const_mx a) (const_mx a) (const_mx a) = const_mx a.
admit.
Defined.

Section CutBlock.

Variable A : matrix R (m1 + m2) (n1 + n2).

Definition ulsubmx := lsubmx (usubmx A).
Definition ursubmx := rsubmx (usubmx A).
Definition dlsubmx := lsubmx (dsubmx A).
Definition drsubmx := rsubmx (dsubmx A).

Lemma submxK : block_mx ulsubmx ursubmx dlsubmx drsubmx = A.
admit.
Defined.

Lemma ulsubmxEsub : ulsubmx = mxsub (lshift _) (lshift _) A.
admit.
Defined.

Lemma dlsubmxEsub : dlsubmx = mxsub (@rshift _ _) (lshift _) A.
admit.
Defined.

Lemma ursubmxEsub : ursubmx = mxsub (lshift _) (@rshift _ _) A.
admit.
Defined.

Lemma drsubmxEsub : drsubmx = mxsub (@rshift _ _) (@rshift _ _) A.
admit.
Defined.

End CutBlock.

Section CatBlock.

Variables (Aul : 'M[R]_(m1, n1)) (Aur : 'M[R]_(m1, n2)).
Variables (Adl : 'M[R]_(m2, n1)) (Adr : 'M[R]_(m2, n2)).

Let A := block_mx Aul Aur Adl Adr.

Lemma block_mxEul i j : A (lshift m2 i) (lshift n2 j) = Aul i j.
admit.
Defined.
Lemma block_mxKul : ulsubmx A = Aul.
admit.
Defined.

Lemma block_mxEur i j : A (lshift m2 i) (rshift n1 j) = Aur i j.
admit.
Defined.
Lemma block_mxKur : ursubmx A = Aur.
admit.
Defined.

Lemma block_mxEdl i j : A (rshift m1 i) (lshift n2 j) = Adl i j.
admit.
Defined.
Lemma block_mxKdl : dlsubmx A = Adl.
admit.
Defined.

Lemma block_mxEdr i j : A (rshift m1 i) (rshift n1 j) = Adr i j.
admit.
Defined.
Lemma block_mxKdr : drsubmx A = Adr.
admit.
Defined.

Lemma block_mxEv : A = col_mx (row_mx Aul Aur) (row_mx Adl Adr).
admit.
Defined.

End CatBlock.

End Block.

Section TrCutBlock.

Variables m1 m2 n1 n2 : nat.
Variable A : 'M[R]_(m1 + m2, n1 + n2).

Lemma trmx_ulsub : (ulsubmx A)^T = ulsubmx A^T.
admit.
Defined.

Lemma trmx_ursub : (ursubmx A)^T = dlsubmx A^T.
admit.
Defined.

Lemma trmx_dlsub : (dlsubmx A)^T = ursubmx A^T.
admit.
Defined.

Lemma trmx_drsub : (drsubmx A)^T = drsubmx A^T.
admit.
Defined.

End TrCutBlock.

Section TrBlock.
Variables m1 m2 n1 n2 : nat.
Variables (Aul : 'M[R]_(m1, n1)) (Aur : 'M[R]_(m1, n2)).
Variables (Adl : 'M[R]_(m2, n1)) (Adr : 'M[R]_(m2, n2)).

Lemma tr_block_mx :
 (block_mx Aul Aur Adl Adr)^T = block_mx Aul^T Adl^T Aur^T Adr^T.
admit.
Defined.

Lemma block_mxEh :
  block_mx Aul Aur Adl Adr = row_mx (col_mx Aul Adl) (col_mx Aur Adr).
admit.
Defined.
End TrBlock.

 
Lemma block_mxA m1 m2 m3 n1 n2 n3
   (A11 : 'M_(m1, n1)) (A12 : 'M_(m1, n2)) (A13 : 'M_(m1, n3))
   (A21 : 'M_(m2, n1)) (A22 : 'M_(m2, n2)) (A23 : 'M_(m2, n3))
   (A31 : 'M_(m3, n1)) (A32 : 'M_(m3, n2)) (A33 : 'M_(m3, n3)) :
  let cast := (esym (addnA m1 m2 m3), esym (addnA n1 n2 n3)) in
  let row1 := row_mx A12 A13 in let col1 := col_mx A21 A31 in
  let row3 := row_mx A31 A32 in let col3 := col_mx A13 A23 in
  block_mx A11 row1 col1 (block_mx A22 A23 A32 A33)
    = castmx cast (block_mx (block_mx A11 A12 A21 A22) col3 row3 A33).
admit.
Defined.
Definition block_mxAx := block_mxA.
 

Section Induction.

Lemma row_ind m (P : forall n, 'M[R]_(m, n) -> Type) :
    (forall A, P 0%N A) ->
    (forall n c A, P n A -> P (1 + n)%N (row_mx c A)) ->
  forall n A, P n A.
admit.
Defined.

Lemma col_ind n (P : forall m, 'M[R]_(m, n) -> Type) :
    (forall A, P 0%N A) ->
    (forall m r A, P m A -> P (1 + m)%N (col_mx r A)) ->
  forall m A, P m A.
admit.
Defined.

Lemma mx_ind (P : forall m n, 'M[R]_(m, n) -> Type) :
    (forall m A, P m 0%N A) ->
    (forall n A, P 0%N n A) ->
    (forall m n x r c A, P m n A -> P (1 + m)%N (1 + n)%N (block_mx x r c A)) ->
  forall m n A, P m n A.
admit.
Defined.
Definition matrix_rect := mx_ind.
Definition matrix_rec := mx_ind.
Definition matrix_ind := mx_ind.

Lemma sqmx_ind (P : forall n, 'M[R]_n -> Type) :
    (forall A, P 0%N A) ->
    (forall n x r c A, P n A -> P (1 + n)%N (block_mx x r c A)) ->
  forall n A, P n A.
admit.
Defined.

Lemma ringmx_ind (P : forall n, 'M[R]_n.+1 -> Type) :
    (forall x, P 0%N x) ->
    (forall n x (r : 'rV_n.+1) (c : 'cV_n.+1) A,
       P n A -> P (1 + n)%N (block_mx x r c A)) ->
  forall n A, P n A.
admit.
Defined.

Lemma mxsub_ind
    (weight : forall m n, 'M[R]_(m, n) -> nat)
    (sub : forall m n m' n', ('I_m' -> 'I_m) -> ('I_n' -> 'I_n) -> Prop)
    (P : forall m n, 'M[R]_(m, n) -> Type) :
    (forall m n (A : 'M[R]_(m, n)),
      (forall m' n' f g, weight m' n' (mxsub f g A) < weight m n A ->
                         sub m n m' n' f g ->
                         P m' n' (mxsub f g A)) -> P m n A) ->
  forall m n A, P m n A.
admit.
Defined.

End Induction.

 
Section VecMatrix.

Variables m n : nat.

Lemma mxvec_cast : #|{:'I_m * 'I_n}| = (m * n)%N.
admit.
Defined.

Definition mxvec_index (i : 'I_m) (j : 'I_n) :=
  cast_ord mxvec_cast (enum_rank (i, j)).

Variant is_mxvec_index : 'I_(m * n) -> Type :=
  IsMxvecIndex i j : is_mxvec_index (mxvec_index i j).

Lemma mxvec_indexP k : is_mxvec_index k.
admit.
Defined.

Coercion pair_of_mxvec_index k (i_k : is_mxvec_index k) :=
  let: IsMxvecIndex i j := i_k in (i, j).

Definition mxvec (A : 'M[R]_(m, n)) :=
  castmx (erefl _, mxvec_cast) (\row_k A (enum_val k).1 (enum_val k).2).

Fact vec_mx_key : unit.
admit.
Defined.
Definition vec_mx (u : 'rV[R]_(m * n)) :=
  \matrix[vec_mx_key]_(i, j) u 0 (mxvec_index i j).

Lemma mxvecE A i j : mxvec A 0 (mxvec_index i j) = A i j.
admit.
Defined.

Lemma mxvecK : cancel mxvec vec_mx.
admit.
Defined.

Lemma vec_mxK : cancel vec_mx mxvec.
admit.
Defined.

Lemma curry_mxvec_bij : {on 'I_(m * n), bijective (prod_curry mxvec_index)}.
admit.
Defined.

End VecMatrix.

End MatrixStructural.

Arguments const_mx {R m n}.
Arguments row_mxA {R m n1 n2 n3 A1 A2 A3}.
Arguments col_mxA {R m1 m2 m3 n A1 A2 A3}.
Arguments block_mxA
  {R m1 m2 m3 n1 n2 n3 A11 A12 A13 A21 A22 A23 A31 A32 A33}.
Prenex Implicits castmx trmx trmxK lsubmx rsubmx usubmx dsubmx row_mx col_mx.
Prenex Implicits block_mx ulsubmx ursubmx dlsubmx drsubmx.
Prenex Implicits mxvec vec_mx mxvec_indexP mxvecK vec_mxK.
Arguments trmx_inj {R m n} [A1 A2] eqA12t : rename.

Notation "A ^T" := (trmx A) : ring_scope.
Notation colsub g := (mxsub id g).
Notation rowsub f := (mxsub f id).

Arguments eq_mxsub [R m n m' n' f] f' [g] g' _.
Arguments eq_rowsub [R m n m' f] f' _.
Arguments eq_colsub [R m n n' g] g' _.

 
Section MapMatrix.

Variables (aT rT : Type) (f : aT -> rT).

Fact map_mx_key : unit.
admit.
Defined.
Definition map_mx m n (A : 'M_(m, n)) := \matrix[map_mx_key]_(i, j) f (A i j).

Notation "A ^f" := (map_mx A) : ring_scope.

Section OneMatrix.

Variables (m n : nat) (A : 'M[aT]_(m, n)).

Lemma map_trmx : A^f^T = A^T^f.
admit.
Defined.

Lemma map_const_mx a : (const_mx a)^f = const_mx (f a) :> 'M_(m, n).
admit.
Defined.

Lemma map_row i : (row i A)^f = row i A^f.
admit.
Defined.

Lemma map_col j : (col j A)^f = col j A^f.
admit.
Defined.

Lemma map_row' i0 : (row' i0 A)^f = row' i0 A^f.
admit.
Defined.

Lemma map_col' j0 : (col' j0 A)^f = col' j0 A^f.
admit.
Defined.

Lemma map_mxsub m' n' g h : (@mxsub _ _ _  m' n' g h A)^f = mxsub g h A^f.
admit.
Defined.

Lemma map_row_perm s : (row_perm s A)^f = row_perm s A^f.
admit.
Defined.

Lemma map_col_perm s : (col_perm s A)^f = col_perm s A^f.
admit.
Defined.

Lemma map_xrow i1 i2 : (xrow i1 i2 A)^f = xrow i1 i2 A^f.
admit.
Defined.

Lemma map_xcol j1 j2 : (xcol j1 j2 A)^f = xcol j1 j2 A^f.
admit.
Defined.

Lemma map_castmx m' n' c : (castmx c A)^f = castmx c A^f :> 'M_(m', n').
admit.
Defined.

Lemma map_conform_mx m' n' (B : 'M_(m', n')) :
  (conform_mx B A)^f = conform_mx B^f A^f.
admit.
Defined.

Lemma map_mxvec : (mxvec A)^f = mxvec A^f.
admit.
Defined.

Lemma map_vec_mx (v : 'rV_(m * n)) : (vec_mx v)^f = vec_mx v^f.
admit.
Defined.

End OneMatrix.

Section Block.

Variables m1 m2 n1 n2 : nat.
Variables (Aul : 'M[aT]_(m1, n1)) (Aur : 'M[aT]_(m1, n2)).
Variables (Adl : 'M[aT]_(m2, n1)) (Adr : 'M[aT]_(m2, n2)).
Variables (Bh : 'M[aT]_(m1, n1 + n2)) (Bv : 'M[aT]_(m1 + m2, n1)).
Variable B : 'M[aT]_(m1 + m2, n1 + n2).

Lemma map_row_mx : (row_mx Aul Aur)^f = row_mx Aul^f Aur^f.
admit.
Defined.

Lemma map_col_mx : (col_mx Aul Adl)^f = col_mx Aul^f Adl^f.
admit.
Defined.

Lemma map_block_mx :
  (block_mx Aul Aur Adl Adr)^f = block_mx Aul^f Aur^f Adl^f Adr^f.
admit.
Defined.

Lemma map_lsubmx : (lsubmx Bh)^f = lsubmx Bh^f.
admit.
Defined.

Lemma map_rsubmx : (rsubmx Bh)^f = rsubmx Bh^f.
admit.
Defined.

Lemma map_usubmx : (usubmx Bv)^f = usubmx Bv^f.
admit.
Defined.

Lemma map_dsubmx : (dsubmx Bv)^f = dsubmx Bv^f.
admit.
Defined.

Lemma map_ulsubmx : (ulsubmx B)^f = ulsubmx B^f.
admit.
Defined.

Lemma map_ursubmx : (ursubmx B)^f = ursubmx B^f.
admit.
Defined.

Lemma map_dlsubmx : (dlsubmx B)^f = dlsubmx B^f.
admit.
Defined.

Lemma map_drsubmx : (drsubmx B)^f = drsubmx B^f.
admit.
Defined.

End Block.

End MapMatrix.

Arguments map_mx {aT rT} f {m n} A.

Section MultipleMapMatrix.
Context {R S T : Type} {m n : nat}.
Local Notation "M ^ phi" := (map_mx phi M).

Lemma map_mx_comp (f : R -> S) (g : S -> T)
  (M : 'M_(m, n)) : M ^ (g \o f) = (M ^ f) ^ g.
admit.
Defined.

Lemma eq_in_map_mx (g f : R -> S) (M : 'M_(m, n)) :
  (forall i j, f (M i j) = g (M i j)) -> M ^ f = M ^ g.
admit.
Defined.

Lemma eq_map_mx (g f : R -> S) : f =1 g ->
  forall (M : 'M_(m, n)), M ^ f = M ^ g.
admit.
Defined.

Lemma map_mx_id_in (f : R -> R) (M : 'M_(m, n)) :
  (forall i j, f (M i j) = M i j) -> M ^ f = M.
admit.
Defined.

Lemma map_mx_id (f : R -> R) : f =1 id -> forall M : 'M_(m, n), M ^ f = M.
admit.
Defined.

End MultipleMapMatrix.
Arguments eq_map_mx {R S m n} g [f].
Arguments eq_in_map_mx {R S m n} g [f M].
Arguments map_mx_id_in {R m n} [f M].
Arguments map_mx_id {R m n} [f].

 
 
 

Section MatrixZmodule.

Variable V : zmodType.

Section FixedDim.

Variables m n : nat.
Implicit Types A B : 'M[V]_(m, n).

Fact oppmx_key : unit.
admit.
Defined.
Fact addmx_key : unit.
admit.
Defined.
Definition oppmx A := \matrix[oppmx_key]_(i, j) (- A i j).
Definition addmx A B := \matrix[addmx_key]_(i, j) (A i j + B i j).
 
 
 

Lemma addmxA : associative addmx.
admit.
Defined.

Lemma addmxC : commutative addmx.
admit.
Defined.

Lemma add0mx : left_id (const_mx 0) addmx.
admit.
Defined.

Lemma addNmx : left_inverse (const_mx 0) oppmx addmx.
admit.
Defined.

Definition matrix_zmodMixin := ZmodMixin addmxA addmxC add0mx addNmx.

Canonical matrix_zmodType := Eval hnf in ZmodType 'M[V]_(m, n) matrix_zmodMixin.

Lemma mulmxnE A d i j : (A *+ d) i j = A i j *+ d.
admit.
Defined.

Lemma summxE I r (P : pred I) (E : I -> 'M_(m, n)) i j :
  (\sum_(k <- r | P k) E k) i j = \sum_(k <- r | P k) E k i j.
admit.
Defined.

Lemma const_mx_is_additive : additive const_mx.
admit.
Defined.
Canonical const_mx_additive := Additive const_mx_is_additive.

End FixedDim.

Section Additive.

Variables (m n p q : nat) (f : 'I_p -> 'I_q -> 'I_m) (g : 'I_p -> 'I_q -> 'I_n).

Definition swizzle_mx k (A : 'M[V]_(m, n)) :=
  \matrix[k]_(i, j) A (f i j) (g i j).

Lemma swizzle_mx_is_additive k : additive (swizzle_mx k).
admit.
Defined.
Canonical swizzle_mx_additive k := Additive (swizzle_mx_is_additive k).

End Additive.

Local Notation SwizzleAdd op := [additive of op as swizzle_mx _ _ _].

Canonical trmx_additive m n := SwizzleAdd (@trmx V m n).
Canonical row_additive m n i := SwizzleAdd (@row V m n i).
Canonical col_additive m n j := SwizzleAdd (@col V m n j).
Canonical row'_additive m n i := SwizzleAdd (@row' V m n i).
Canonical col'_additive m n j := SwizzleAdd (@col' V m n j).
Canonical mxsub_additive m n m' n' f g := SwizzleAdd (@mxsub V m n m' n' f g).
Canonical row_perm_additive m n s := SwizzleAdd (@row_perm V m n s).
Canonical col_perm_additive m n s := SwizzleAdd (@col_perm V m n s).
Canonical xrow_additive m n i1 i2 := SwizzleAdd (@xrow V m n i1 i2).
Canonical xcol_additive m n j1 j2 := SwizzleAdd (@xcol V m n j1 j2).
Canonical lsubmx_additive m n1 n2 := SwizzleAdd (@lsubmx V m n1 n2).
Canonical rsubmx_additive m n1 n2 := SwizzleAdd (@rsubmx V m n1 n2).
Canonical usubmx_additive m1 m2 n := SwizzleAdd (@usubmx V m1 m2 n).
Canonical dsubmx_additive m1 m2 n := SwizzleAdd (@dsubmx V m1 m2 n).
Canonical vec_mx_additive m n := SwizzleAdd (@vec_mx V m n).
Canonical mxvec_additive m n :=
  Additive (can2_additive (@vec_mxK V m n) mxvecK).

Lemma flatmx0 n : all_equal_to (0 : 'M_(0, n)).
admit.
Defined.

Lemma thinmx0 n : all_equal_to (0 : 'M_(n, 0)).
admit.
Defined.

Lemma trmx0 m n : (0 : 'M_(m, n))^T = 0.
admit.
Defined.

Lemma row0 m n i0 : row i0 (0 : 'M_(m, n)) = 0.
admit.
Defined.

Lemma col0 m n j0 : col j0 (0 : 'M_(m, n)) = 0.
admit.
Defined.

Lemma mxvec_eq0 m n (A : 'M_(m, n)) : (mxvec A == 0) = (A == 0).
admit.
Defined.

Lemma vec_mx_eq0 m n (v : 'rV_(m * n)) : (vec_mx v == 0) = (v == 0).
admit.
Defined.

Lemma row_mx0 m n1 n2 : row_mx 0 0 = 0 :> 'M_(m, n1 + n2).
admit.
Defined.

Lemma col_mx0 m1 m2 n : col_mx 0 0 = 0 :> 'M_(m1 + m2, n).
admit.
Defined.

Lemma block_mx0 m1 m2 n1 n2 : block_mx 0 0 0 0 = 0 :> 'M_(m1 + m2, n1 + n2).
admit.
Defined.

Lemma opp_row_mx m n1 n2 (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)) :
  - row_mx A1 A2 = row_mx (- A1) (- A2).
admit.
Defined.

Lemma opp_col_mx m1 m2 n (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)) :
  - col_mx A1 A2 = col_mx (- A1) (- A2).
admit.
Defined.

Lemma opp_block_mx m1 m2 n1 n2 (Aul : 'M_(m1, n1)) Aur Adl (Adr : 'M_(m2, n2)) :
  - block_mx Aul Aur Adl Adr = block_mx (- Aul) (- Aur) (- Adl) (- Adr).
admit.
Defined.

Lemma add_row_mx m n1 n2 (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)) B1 B2 :
  row_mx A1 A2 + row_mx B1 B2 = row_mx (A1 + B1) (A2 + B2).
admit.
Defined.

Lemma add_col_mx m1 m2 n (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)) B1 B2 :
  col_mx A1 A2 + col_mx B1 B2 = col_mx (A1 + B1) (A2 + B2).
admit.
Defined.

Lemma add_block_mx m1 m2 n1 n2 (Aul : 'M_(m1, n1)) Aur Adl (Adr : 'M_(m2, n2))
                   Bul Bur Bdl Bdr :
  let A := block_mx Aul Aur Adl Adr in let B := block_mx Bul Bur Bdl Bdr in
  A + B = block_mx (Aul + Bul) (Aur + Bur) (Adl + Bdl) (Adr + Bdr).
admit.
Defined.

Lemma row_mx_eq0 (m n1 n2 : nat) (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)):
  (row_mx A1 A2 == 0) = (A1 == 0) && (A2 == 0).
admit.
Defined.

Lemma col_mx_eq0 (m1 m2 n : nat) (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)):
  (col_mx A1 A2 == 0) = (A1 == 0) && (A2 == 0).
admit.
Defined.

Lemma block_mx_eq0 m1 m2 n1 n2 (Aul : 'M_(m1, n1)) Aur Adl (Adr : 'M_(m2, n2)) :
  (block_mx Aul Aur Adl Adr == 0) =
  [&& Aul == 0, Aur == 0, Adl == 0 & Adr == 0].
admit.
Defined.

Lemma trmx_eq0  m n (A : 'M_(m, n)) : (A^T == 0) = (A == 0).
admit.
Defined.

Lemma matrix_eq0 m n (A : 'M_(m, n)) :
  (A == 0) = [forall i, forall j, A i j == 0].
admit.
Defined.

Lemma matrix0Pn m n (A : 'M_(m, n)) : reflect (exists i j, A i j != 0) (A != 0).
admit.
Defined.

Lemma rV0Pn n (v : 'rV_n) : reflect (exists i, v 0 i != 0) (v != 0).
admit.
Defined.

Lemma cV0Pn n (v : 'cV_n) : reflect (exists i, v i 0 != 0) (v != 0).
admit.
Defined.

Definition nz_row m n (A : 'M_(m, n)) :=
  oapp (fun i => row i A) 0 [pick i | row i A != 0].

Lemma nz_row_eq0 m n (A : 'M_(m, n)) : (nz_row A == 0) = (A == 0).
admit.
Defined.

Definition is_diag_mx m n (A : 'M[V]_(m, n)) :=
  [forall i : 'I__, forall j : 'I__, (i != j :> nat) ==> (A i j == 0)].

Lemma is_diag_mxP m n (A : 'M[V]_(m, n)) :
  reflect (forall i j : 'I__, i != j :> nat -> A i j = 0) (is_diag_mx A).
admit.
Defined.

Lemma mx0_is_diag m n : is_diag_mx (0 : 'M[V]_(m, n)).
admit.
Defined.

Lemma mx11_is_diag (M : 'M_1) : is_diag_mx M.
admit.
Defined.

Definition is_trig_mx m n (A : 'M[V]_(m, n)) :=
  [forall i : 'I__, forall j : 'I__, (i < j)%N ==> (A i j == 0)].

Lemma is_trig_mxP m n (A : 'M[V]_(m, n)) :
  reflect (forall i j : 'I__, (i < j)%N -> A i j = 0) (is_trig_mx A).
admit.
Defined.

Lemma is_diag_mx_is_trig m n (A : 'M[V]_(m, n)) : is_diag_mx A -> is_trig_mx A.
admit.
Defined.

Lemma mx0_is_trig m n : is_trig_mx (0 : 'M[V]_(m, n)).
admit.
Defined.

Lemma mx11_is_trig (M : 'M_1) : is_trig_mx M.
admit.
Defined.

Lemma is_diag_mxEtrig m n (A : 'M[V]_(m, n)) :
  is_diag_mx A = is_trig_mx A && is_trig_mx A^T.
admit.
Defined.

Lemma is_diag_trmx  m n (A : 'M[V]_(m, n)) : is_diag_mx A^T = is_diag_mx A.
admit.
Defined.

Lemma ursubmx_trig m1 m2 n1 n2 (A : 'M[V]_(m1 + m2, n1 + n2)) :
  m1 <= n1 -> is_trig_mx A -> ursubmx A = 0.
admit.
Defined.

Lemma dlsubmx_diag m1 m2 n1 n2 (A : 'M[V]_(m1 + m2, n1 + n2)) :
  n1 <= m1 -> is_diag_mx A -> dlsubmx A = 0.
admit.
Defined.

Lemma ulsubmx_trig m1 m2 n1 n2 (A : 'M[V]_(m1 + m2, n1 + n2)) :
  is_trig_mx A -> is_trig_mx (ulsubmx A).
admit.
Defined.

Lemma drsubmx_trig m1 m2 n1 n2 (A : 'M[V]_(m1 + m2, n1 + n2)) :
  m1 <= n1 -> is_trig_mx A -> is_trig_mx (drsubmx A).
admit.
Defined.

Lemma ulsubmx_diag m1 m2 n1 n2 (A : 'M[V]_(m1 + m2, n1 + n2)) :
  is_diag_mx A -> is_diag_mx (ulsubmx A).
admit.
Defined.

Lemma drsubmx_diag m1 m2 n1 n2 (A : 'M[V]_(m1 + m2, n1 + n2)) :
  m1 = n1 -> is_diag_mx A -> is_diag_mx (drsubmx A).
admit.
Defined.

Lemma is_trig_block_mx m1 m2 n1 n2 ul ur dl dr : m1 = n1 ->
  @is_trig_mx (m1 + m2) (n1 + n2) (block_mx ul ur dl dr) =
  [&& ur == 0, is_trig_mx ul & is_trig_mx dr].
admit.
Defined.

Lemma trigmx_ind (P : forall m n, 'M_(m, n) -> Type) :
  (forall m, P m 0%N 0) ->
  (forall n, P 0%N n 0) ->
  (forall m n x c A, is_trig_mx A ->
    P m n A -> P (1 + m)%N (1 + n)%N (block_mx x 0 c A)) ->
  forall m n A, is_trig_mx A -> P m n A.
admit.
Defined.

Lemma trigsqmx_ind (P : forall n, 'M[V]_n -> Type) : (P 0%N 0) ->
  (forall n x c A, is_trig_mx A -> P n A -> P (1 + n)%N (block_mx x 0 c A)) ->
  forall n A, is_trig_mx A -> P n A.
admit.
Defined.

Lemma is_diag_block_mx m1 m2 n1 n2 ul ur dl dr : m1 = n1 ->
  @is_diag_mx (m1 + m2) (n1 + n2) (block_mx ul ur dl dr) =
  [&& ur == 0, dl == 0, is_diag_mx ul & is_diag_mx dr].
admit.
Defined.

Lemma diagmx_ind (P : forall m n, 'M_(m, n) -> Type) :
  (forall m, P m 0%N 0) ->
  (forall n, P 0%N n 0) ->
  (forall m n x c A, is_diag_mx A ->
    P m n A -> P (1 + m)%N (1 + n)%N (block_mx x 0 c A)) ->
  forall m n A, is_diag_mx A -> P m n A.
admit.
Defined.

Lemma diagsqmx_ind (P : forall n, 'M[V]_n -> Type) :
    (P 0%N 0) ->
  (forall n x c A, is_diag_mx A -> P n A -> P (1 + n)%N (block_mx x 0 c A)) ->
  forall n A, is_diag_mx A -> P n A.
admit.
Defined.

End MatrixZmodule.

Arguments is_diag_mx {V m n}.
Arguments is_diag_mxP {V m n A}.
Arguments is_trig_mx {V m n}.
Arguments is_trig_mxP {V m n A}.

Section FinZmodMatrix.
Variables (V : finZmodType) (m n : nat).
Local Notation MV := 'M[V]_(m, n).

Canonical matrix_finZmodType := Eval hnf in [finZmodType of MV].
Canonical matrix_baseFinGroupType :=
  Eval hnf in [baseFinGroupType of MV for +%R].
Canonical matrix_finGroupType := Eval hnf in [finGroupType of MV for +%R].
End FinZmodMatrix.

 
Section MapZmodMatrix.

Variables (aR rR : zmodType) (f : {additive aR -> rR}) (m n : nat).
Local Notation "A ^f" := (map_mx f A) : ring_scope.
Implicit Type A : 'M[aR]_(m, n).

Lemma map_mx0 : 0^f = 0 :> 'M_(m, n).
admit.
Defined.

Lemma map_mxN A : (- A)^f = - A^f.
admit.
Defined.

Lemma map_mxD A B : (A + B)^f = A^f + B^f.
admit.
Defined.

Lemma map_mxB A B : (A - B)^f = A^f - B^f.
admit.
Defined.

Definition map_mx_sum := big_morph _ map_mxD map_mx0.

Canonical map_mx_additive := Additive map_mxB.

End MapZmodMatrix.

 
 
 

Section MatrixAlgebra.

Variable R : ringType.

Section RingModule.

 

Variables m n : nat.
Implicit Types A B : 'M[R]_(m, n).

Fact scalemx_key : unit.
admit.
Defined.
Definition scalemx x A := \matrix[scalemx_key]_(i, j) (x * A i j).

 
Fact delta_mx_key : unit.
admit.
Defined.
Definition delta_mx i0 j0 : 'M[R]_(m, n) :=
  \matrix[delta_mx_key]_(i, j) ((i == i0) && (j == j0))%:R.

Local Notation "x *m: A" := (scalemx x A) (at level 40) : ring_scope.

Lemma scale1mx A : 1 *m: A = A.
admit.
Defined.

Lemma scalemxDl A x y : (x + y) *m: A = x *m: A + y *m: A.
admit.
Defined.

Lemma scalemxDr x A B : x *m: (A + B) = x *m: A + x *m: B.
admit.
Defined.

Lemma scalemxA x y A : x *m: (y *m: A) = (x * y) *m: A.
admit.
Defined.

Definition matrix_lmodMixin :=
  LmodMixin scalemxA scale1mx scalemxDr scalemxDl.

Canonical matrix_lmodType :=
  Eval hnf in LmodType R 'M[R]_(m, n) matrix_lmodMixin.

Lemma scalemx_const a b : a *: const_mx b = const_mx (a * b).
admit.
Defined.

Lemma matrix_sum_delta A :
  A = \sum_(i < m) \sum_(j < n) A i j *: delta_mx i j.
admit.
Defined.

End RingModule.

Section StructuralLinear.

Lemma swizzle_mx_is_scalable m n p q f g k :
  scalable (@swizzle_mx R m n p q f g k).
admit.
Defined.
Canonical swizzle_mx_scalable m n p q f g k :=
  AddLinear (@swizzle_mx_is_scalable m n p q f g k).

Local Notation SwizzleLin op := [linear of op as swizzle_mx _ _ _].

Canonical trmx_linear m n := SwizzleLin (@trmx R m n).
Canonical row_linear m n i := SwizzleLin (@row R m n i).
Canonical col_linear m n j := SwizzleLin (@col R m n j).
Canonical row'_linear m n i := SwizzleLin (@row' R m n i).
Canonical col'_linear m n j := SwizzleLin (@col' R m n j).
Canonical mxsub_linear m n m' n' f g := SwizzleLin (@mxsub R m n m' n' f g).
Canonical row_perm_linear m n s := SwizzleLin (@row_perm R m n s).
Canonical col_perm_linear m n s := SwizzleLin (@col_perm R m n s).
Canonical xrow_linear m n i1 i2 := SwizzleLin (@xrow R m n i1 i2).
Canonical xcol_linear m n j1 j2 := SwizzleLin (@xcol R m n j1 j2).
Canonical lsubmx_linear m n1 n2 := SwizzleLin (@lsubmx R m n1 n2).
Canonical rsubmx_linear m n1 n2 := SwizzleLin (@rsubmx R m n1 n2).
Canonical usubmx_linear m1 m2 n := SwizzleLin (@usubmx R m1 m2 n).
Canonical dsubmx_linear m1 m2 n := SwizzleLin (@dsubmx R m1 m2 n).
Canonical vec_mx_linear m n := SwizzleLin (@vec_mx R m n).
Definition mxvec_is_linear m n := can2_linear (@vec_mxK R m n) mxvecK.
Canonical mxvec_linear m n := AddLinear (@mxvec_is_linear m n).

End StructuralLinear.

Lemma trmx_delta m n i j : (delta_mx i j)^T = delta_mx j i :> 'M[R]_(n, m).
admit.
Defined.

Lemma row_sum_delta n (u : 'rV_n) : u = \sum_(j < n) u 0 j *: delta_mx 0 j.
admit.
Defined.

Lemma delta_mx_lshift m n1 n2 i j :
  delta_mx i (lshift n2 j) = row_mx (delta_mx i j) 0 :> 'M_(m, n1 + n2).
admit.
Defined.

Lemma delta_mx_rshift m n1 n2 i j :
  delta_mx i (rshift n1 j) = row_mx 0 (delta_mx i j) :> 'M_(m, n1 + n2).
admit.
Defined.

Lemma delta_mx_ushift m1 m2 n i j :
  delta_mx (lshift m2 i) j = col_mx (delta_mx i j) 0 :> 'M_(m1 + m2, n).
admit.
Defined.

Lemma delta_mx_dshift m1 m2 n i j :
  delta_mx (rshift m1 i) j = col_mx 0 (delta_mx i j) :> 'M_(m1 + m2, n).
admit.
Defined.

Lemma vec_mx_delta m n i j :
  vec_mx (delta_mx 0 (mxvec_index i j)) = delta_mx i j :> 'M_(m, n).
admit.
Defined.

Lemma mxvec_delta m n i j :
  mxvec (delta_mx i j) = delta_mx 0 (mxvec_index i j) :> 'rV_(m * n).
admit.
Defined.

Lemma scale_row_mx m n1 n2 a (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)) :
  a *: row_mx A1 A2 = row_mx (a *: A1) (a *: A2).
admit.
Defined.

Lemma scale_col_mx m1 m2 n a (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)) :
  a *: col_mx A1 A2 = col_mx (a *: A1) (a *: A2).
admit.
Defined.

Lemma scale_block_mx m1 m2 n1 n2 a (Aul : 'M_(m1, n1)) (Aur : 'M_(m1, n2))
                                   (Adl : 'M_(m2, n1)) (Adr : 'M_(m2, n2)) :
  a *: block_mx Aul Aur Adl Adr
     = block_mx (a *: Aul) (a *: Aur) (a *: Adl) (a *: Adr).
admit.
Defined.

 

Fact diag_mx_key : unit.
admit.
Defined.
Definition diag_mx n (d : 'rV[R]_n) :=
  \matrix[diag_mx_key]_(i, j) (d 0 i *+ (i == j)).

Lemma tr_diag_mx n (d : 'rV_n) : (diag_mx d)^T = diag_mx d.
admit.
Defined.

Lemma diag_mx_is_linear n : linear (@diag_mx n).
admit.
Defined.
Canonical diag_mx_additive n := Additive (@diag_mx_is_linear n).
Canonical diag_mx_linear n := Linear (@diag_mx_is_linear n).

Lemma diag_mx_sum_delta n (d : 'rV_n) :
  diag_mx d = \sum_i d 0 i *: delta_mx i i.
admit.
Defined.

Lemma row_diag_mx n (d : 'rV_n) i :
  row i (diag_mx d) = d 0 i *: delta_mx 0 i.
admit.
Defined.

Lemma diag_mx_row m n (l : 'rV_n) (r : 'rV_m) :
  diag_mx (row_mx l r) = block_mx (diag_mx l) 0 0 (diag_mx r).
admit.
Defined.

Lemma diag_mxP n (A : 'M[R]_n) :
  reflect (exists d : 'rV_n, A = diag_mx d) (is_diag_mx A).
admit.
Defined.

Lemma diag_mx_is_diag n (r : 'rV[R]_n) : is_diag_mx (diag_mx r).
admit.
Defined.

Lemma diag_mx_is_trig n (r : 'rV[R]_n) : is_trig_mx (diag_mx r).
admit.
Defined.

 
Section ScalarMx.

Variable n : nat.

Fact scalar_mx_key : unit.
admit.
Defined.
Definition scalar_mx x : 'M[R]_n :=
  \matrix[scalar_mx_key]_(i , j) (x *+ (i == j)).
Notation "x %:M" := (scalar_mx x) : ring_scope.

Lemma diag_const_mx a : diag_mx (const_mx a) = a%:M :> 'M_n.
admit.
Defined.

Lemma tr_scalar_mx a : (a%:M)^T = a%:M.
admit.
Defined.

Lemma trmx1 : (1%:M)^T = 1%:M.
admit.
Defined.

Lemma scalar_mx_is_additive : additive scalar_mx.
admit.
Defined.
Canonical scalar_mx_additive := Additive scalar_mx_is_additive.

Lemma scale_scalar_mx a1 a2 : a1 *: a2%:M = (a1 * a2)%:M :> 'M_n.
admit.
Defined.

Lemma scalemx1 a : a *: 1%:M = a%:M.
admit.
Defined.

Lemma scalar_mx_sum_delta a : a%:M = \sum_i a *: delta_mx i i.
admit.
Defined.

Lemma mx1_sum_delta : 1%:M = \sum_i delta_mx i i.
admit.
Defined.

Lemma row1 i : row i 1%:M = delta_mx 0 i.
admit.
Defined.

Lemma col1 i : col i 1%:M = delta_mx i 0.
admit.
Defined.

Definition is_scalar_mx (A : 'M[R]_n) :=
  if insub 0%N is Some i then A == (A i i)%:M else true.

Lemma is_scalar_mxP A : reflect (exists a, A = a%:M) (is_scalar_mx A).
admit.
Defined.

Lemma scalar_mx_is_scalar a : is_scalar_mx a%:M.
admit.
Defined.

Lemma mx0_is_scalar : is_scalar_mx 0.
admit.
Defined.

Lemma scalar_mx_is_diag a : is_diag_mx (a%:M).
admit.
Defined.

Lemma is_scalar_mx_is_diag A : is_scalar_mx A -> is_diag_mx A.
admit.
Defined.

Lemma scalar_mx_is_trig a : is_trig_mx (a%:M).
admit.
Defined.

Lemma is_scalar_mx_is_trig A : is_scalar_mx A -> is_trig_mx A.
admit.
Defined.

End ScalarMx.

Notation "x %:M" := (scalar_mx _ x) : ring_scope.

Lemma mx11_scalar (A : 'M_1) : A = (A 0 0)%:M.
admit.
Defined.

Lemma scalar_mx_block n1 n2 a : a%:M = block_mx a%:M 0 0 a%:M :> 'M_(n1 + n2).
admit.
Defined.

 
Fact mulmx_key : unit.
admit.
Defined.
Definition mulmx {m n p} (A : 'M_(m, n)) (B : 'M_(n, p)) : 'M[R]_(m, p) :=
  \matrix[mulmx_key]_(i, k) \sum_j (A i j * B j k).

Local Notation "A *m B" := (mulmx A B) : ring_scope.

Lemma mulmxA m n p q (A : 'M_(m, n)) (B : 'M_(n, p)) (C : 'M_(p, q)) :
  A *m (B *m C) = A *m B *m C.
admit.
Defined.

Lemma mul0mx m n p (A : 'M_(n, p)) : 0 *m A = 0 :> 'M_(m, p).
admit.
Defined.

Lemma mulmx0 m n p (A : 'M_(m, n)) : A *m 0 = 0 :> 'M_(m, p).
admit.
Defined.

Lemma mulmxN m n p (A : 'M_(m, n)) (B : 'M_(n, p)) : A *m (- B) = - (A *m B).
admit.
Defined.

Lemma mulNmx m n p (A : 'M_(m, n)) (B : 'M_(n, p)) : - A *m B = - (A *m B).
admit.
Defined.

Lemma mulmxDl m n p (A1 A2 : 'M_(m, n)) (B : 'M_(n, p)) :
  (A1 + A2) *m B = A1 *m B + A2 *m B.
admit.
Defined.

Lemma mulmxDr m n p (A : 'M_(m, n)) (B1 B2 : 'M_(n, p)) :
  A *m (B1 + B2) = A *m B1 + A *m B2.
admit.
Defined.

Lemma mulmxBl m n p (A1 A2 : 'M_(m, n)) (B : 'M_(n, p)) :
  (A1 - A2) *m B = A1 *m B - A2 *m B.
admit.
Defined.

Lemma mulmxBr m n p (A : 'M_(m, n)) (B1 B2 : 'M_(n, p)) :
  A *m (B1 - B2) = A *m B1 - A *m B2.
admit.
Defined.

Lemma mulmx_suml m n p (A : 'M_(n, p)) I r P (B_ : I -> 'M_(m, n)) :
   (\sum_(i <- r | P i) B_ i) *m A = \sum_(i <- r | P i) B_ i *m A.
admit.
Defined.

Lemma mulmx_sumr m n p (A : 'M_(m, n)) I r P (B_ : I -> 'M_(n, p)) :
   A *m (\sum_(i <- r | P i) B_ i) = \sum_(i <- r | P i) A *m B_ i.
admit.
Defined.

Lemma scalemxAl m n p a (A : 'M_(m, n)) (B : 'M_(n, p)) :
  a *: (A *m B) = (a *: A) *m B.
admit.
Defined.
 

Lemma rowE m n i (A : 'M_(m, n)) : row i A = delta_mx 0 i *m A.
admit.
Defined.

Lemma colE m n i (A : 'M_(m, n)) : col i A = A *m delta_mx i 0.
admit.
Defined.

Lemma mul_rVP m n A B :((@mulmx 1 m n)^~ A =1 mulmx^~ B) <-> (A = B).
admit.
Defined.

Lemma row_mul m n p (i : 'I_m) A (B : 'M_(n, p)) :
  row i (A *m B) = row i A *m B.
admit.
Defined.

Lemma mulmx_sum_row m n (u : 'rV_m) (A : 'M_(m, n)) :
  u *m A = \sum_i u 0 i *: row i A.
admit.
Defined.

Lemma mxsub_mul m n m' n' p f g (A : 'M_(m, p)) (B : 'M_(p, n)) :
  mxsub f g (A *m B) = rowsub f A *m colsub g B :> 'M_(m', n').
admit.
Defined.

Lemma mul_rowsub_mx m n m' p f (A : 'M_(m, p)) (B : 'M_(p, n)) :
  rowsub f A *m B = rowsub f (A *m B) :> 'M_(m', n).
admit.
Defined.

Lemma mulmx_colsub m n n' p g (A : 'M_(m, p)) (B : 'M_(p, n)) :
  A *m colsub g B = colsub g (A *m B) :> 'M_(m, n').
admit.
Defined.

Lemma mul_delta_mx_cond m n p (j1 j2 : 'I_n) (i1 : 'I_m) (k2 : 'I_p) :
  delta_mx i1 j1 *m delta_mx j2 k2 = delta_mx i1 k2 *+ (j1 == j2).
admit.
Defined.

Lemma mul_delta_mx m n p (j : 'I_n) (i : 'I_m) (k : 'I_p) :
  delta_mx i j *m delta_mx j k = delta_mx i k.
admit.
Defined.

Lemma mul_delta_mx_0 m n p (j1 j2 : 'I_n) (i1 : 'I_m) (k2 : 'I_p) :
  j1 != j2 -> delta_mx i1 j1 *m delta_mx j2 k2 = 0.
admit.
Defined.

Lemma mul_diag_mx m n d (A : 'M_(m, n)) :
  diag_mx d *m A = \matrix_(i, j) (d 0 i * A i j).
admit.
Defined.

Lemma mul_mx_diag m n (A : 'M_(m, n)) d :
  A *m diag_mx d = \matrix_(i, j) (A i j * d 0 j).
admit.
Defined.

Lemma mulmx_diag n (d e : 'rV_n) :
  diag_mx d *m diag_mx e = diag_mx (\row_j (d 0 j * e 0 j)).
admit.
Defined.

Lemma mul_scalar_mx m n a (A : 'M_(m, n)) : a%:M *m A = a *: A.
admit.
Defined.

Lemma scalar_mxM n a b : (a * b)%:M = a%:M *m b%:M :> 'M_n.
admit.
Defined.

Lemma mul1mx m n (A : 'M_(m, n)) : 1%:M *m A = A.
admit.
Defined.

Lemma mulmx1 m n (A : 'M_(m, n)) : A *m 1%:M = A.
admit.
Defined.

Lemma rowsubE m m' n f (A : 'M_(m, n)) :
   rowsub f A = rowsub f 1%:M *m A :> 'M_(m', n).
admit.
Defined.

 

Lemma mul_col_perm m n p s (A : 'M_(m, n)) (B : 'M_(n, p)) :
  col_perm s A *m B = A *m row_perm s^-1 B.
admit.
Defined.

Lemma mul_row_perm m n p s (A : 'M_(m, n)) (B : 'M_(n, p)) :
  A *m row_perm s B = col_perm s^-1 A *m B.
admit.
Defined.

Lemma mul_xcol m n p j1 j2 (A : 'M_(m, n)) (B : 'M_(n, p)) :
  xcol j1 j2 A *m B = A *m xrow j1 j2 B.
admit.
Defined.

 

Definition perm_mx n s : 'M_n := row_perm s 1%:M.

Definition tperm_mx n i1 i2 : 'M_n := perm_mx (tperm i1 i2).

Lemma col_permE m n s (A : 'M_(m, n)) : col_perm s A = A *m perm_mx s^-1.
admit.
Defined.

Lemma row_permE m n s (A : 'M_(m, n)) : row_perm s A = perm_mx s *m A.
admit.
Defined.

Lemma xcolE m n j1 j2 (A : 'M_(m, n)) : xcol j1 j2 A = A *m tperm_mx j1 j2.
admit.
Defined.

Lemma xrowE m n i1 i2 (A : 'M_(m, n)) : xrow i1 i2 A = tperm_mx i1 i2 *m A.
admit.
Defined.

Lemma perm_mxEsub n s : @perm_mx n s = rowsub s 1%:M.
admit.
Defined.

Lemma tperm_mxEsub n i1 i2 : @tperm_mx n i1 i2 = rowsub (tperm i1 i2) 1%:M.
admit.
Defined.

Lemma tr_perm_mx n (s : 'S_n) : (perm_mx s)^T = perm_mx s^-1.
admit.
Defined.

Lemma tr_tperm_mx n i1 i2 : (tperm_mx i1 i2)^T = tperm_mx i1 i2 :> 'M_n.
admit.
Defined.

Lemma perm_mx1 n : perm_mx 1 = 1%:M :> 'M_n.
admit.
Defined.

Lemma perm_mxM n (s t : 'S_n) : perm_mx (s * t) = perm_mx s *m perm_mx t.
admit.
Defined.

Definition is_perm_mx n (A : 'M_n) := [exists s, A == perm_mx s].

Lemma is_perm_mxP n (A : 'M_n) :
  reflect (exists s, A = perm_mx s) (is_perm_mx A).
admit.
Defined.

Lemma perm_mx_is_perm n (s : 'S_n) : is_perm_mx (perm_mx s).
admit.
Defined.

Lemma is_perm_mx1 n : is_perm_mx (1%:M : 'M_n).
admit.
Defined.

Lemma is_perm_mxMl n (A B : 'M_n) :
  is_perm_mx A -> is_perm_mx (A *m B) = is_perm_mx B.
admit.
Defined.

Lemma is_perm_mx_tr n (A : 'M_n) : is_perm_mx A^T = is_perm_mx A.
admit.
Defined.

Lemma is_perm_mxMr n (A B : 'M_n) :
  is_perm_mx B -> is_perm_mx (A *m B) = is_perm_mx A.
admit.
Defined.

 

Fact pid_mx_key : unit.
admit.
Defined.
Definition pid_mx {m n} r : 'M[R]_(m, n) :=
  \matrix[pid_mx_key]_(i, j) ((i == j :> nat) && (i < r))%:R.

Lemma pid_mx_0 m n : pid_mx 0 = 0 :> 'M_(m, n).
admit.
Defined.

Lemma pid_mx_1 r : pid_mx r = 1%:M :> 'M_r.
admit.
Defined.

Lemma pid_mx_row n r : pid_mx r = row_mx 1%:M 0 :> 'M_(r, r + n).
admit.
Defined.

Lemma pid_mx_col m r : pid_mx r = col_mx 1%:M 0 :> 'M_(r + m, r).
admit.
Defined.

Lemma pid_mx_block m n r : pid_mx r = block_mx 1%:M 0 0 0 :> 'M_(r + m, r + n).
admit.
Defined.

Lemma tr_pid_mx m n r : (pid_mx r)^T = pid_mx r :> 'M_(n, m).
admit.
Defined.

Lemma pid_mx_minv m n r : pid_mx (minn m r) = pid_mx r :> 'M_(m, n).
admit.
Defined.

Lemma pid_mx_minh m n r : pid_mx (minn n r) = pid_mx r :> 'M_(m, n).
admit.
Defined.

Lemma mul_pid_mx m n p q r :
  (pid_mx q : 'M_(m, n)) *m (pid_mx r : 'M_(n, p)) = pid_mx (minn n (minn q r)).
admit.
Defined.

Lemma pid_mx_id m n p r :
  r <= n -> (pid_mx r : 'M_(m, n)) *m (pid_mx r : 'M_(n, p)) = pid_mx r.
admit.
Defined.

Definition copid_mx {n} r : 'M_n := 1%:M - pid_mx r.

Lemma mul_copid_mx_pid m n r :
  r <= m -> copid_mx r *m pid_mx r = 0 :> 'M_(m, n).
admit.
Defined.

Lemma mul_pid_mx_copid m n r :
  r <= n -> pid_mx r *m copid_mx r = 0 :> 'M_(m, n).
admit.
Defined.

Lemma copid_mx_id n r :
  r <= n -> copid_mx r *m copid_mx r = copid_mx r :> 'M_n.
admit.
Defined.

Lemma pid_mxErow m n (le_mn : m <= n) :
  pid_mx m = rowsub (widen_ord le_mn) 1%:M.
admit.
Defined.

Lemma pid_mxEcol m n (le_mn : m <= n) :
  pid_mx n = colsub (widen_ord le_mn) 1%:M.
admit.
Defined.

 
Lemma mul_mx_row m n p1 p2 (A : 'M_(m, n)) (Bl : 'M_(n, p1)) (Br : 'M_(n, p2)) :
  A *m row_mx Bl Br = row_mx (A *m Bl) (A *m Br).
admit.
Defined.

Lemma mul_col_mx m1 m2 n p (Au : 'M_(m1, n)) (Ad : 'M_(m2, n)) (B : 'M_(n, p)) :
  col_mx Au Ad *m B = col_mx (Au *m B) (Ad *m B).
admit.
Defined.

Lemma mul_row_col m n1 n2 p (Al : 'M_(m, n1)) (Ar : 'M_(m, n2))
                            (Bu : 'M_(n1, p)) (Bd : 'M_(n2, p)) :
  row_mx Al Ar *m col_mx Bu Bd = Al *m Bu + Ar *m Bd.
admit.
Defined.

Lemma mul_col_row m1 m2 n p1 p2 (Au : 'M_(m1, n)) (Ad : 'M_(m2, n))
                                (Bl : 'M_(n, p1)) (Br : 'M_(n, p2)) :
  col_mx Au Ad *m row_mx Bl Br
     = block_mx (Au *m Bl) (Au *m Br) (Ad *m Bl) (Ad *m Br).
admit.
Defined.

Lemma mul_row_block m n1 n2 p1 p2 (Al : 'M_(m, n1)) (Ar : 'M_(m, n2))
                                  (Bul : 'M_(n1, p1)) (Bur : 'M_(n1, p2))
                                  (Bdl : 'M_(n2, p1)) (Bdr : 'M_(n2, p2)) :
  row_mx Al Ar *m block_mx Bul Bur Bdl Bdr
   = row_mx (Al *m Bul + Ar *m Bdl) (Al *m Bur + Ar *m Bdr).
admit.
Defined.

Lemma mul_block_col m1 m2 n1 n2 p (Aul : 'M_(m1, n1)) (Aur : 'M_(m1, n2))
                                  (Adl : 'M_(m2, n1)) (Adr : 'M_(m2, n2))
                                  (Bu : 'M_(n1, p)) (Bd : 'M_(n2, p)) :
  block_mx Aul Aur Adl Adr *m col_mx Bu Bd
   = col_mx (Aul *m Bu + Aur *m Bd) (Adl *m Bu + Adr *m Bd).
admit.
Defined.

Lemma mulmx_block m1 m2 n1 n2 p1 p2 (Aul : 'M_(m1, n1)) (Aur : 'M_(m1, n2))
                                    (Adl : 'M_(m2, n1)) (Adr : 'M_(m2, n2))
                                    (Bul : 'M_(n1, p1)) (Bur : 'M_(n1, p2))
                                    (Bdl : 'M_(n2, p1)) (Bdr : 'M_(n2, p2)) :
  block_mx Aul Aur Adl Adr *m block_mx Bul Bur Bdl Bdr
    = block_mx (Aul *m Bul + Aur *m Bdl) (Aul *m Bur + Aur *m Bdr)
               (Adl *m Bul + Adr *m Bdl) (Adl *m Bur + Adr *m Bdr).
admit.
Defined.

Lemma mulmx_lsub m n p k (A : 'M_(m, n)) (B : 'M_(n, p + k)) :
  A *m lsubmx B = lsubmx (A *m B).
admit.
Defined.

Lemma mulmx_rsub m n p k (A : 'M_(m, n)) (B : 'M_(n, p + k)) :
  A *m rsubmx B = rsubmx (A *m B).
admit.
Defined.

Lemma mul_usub_mx m k n p (A : 'M_(m + k, n)) (B : 'M_(n, p)) :
  usubmx A *m B = usubmx (A *m B).
admit.
Defined.

Lemma mul_dsub_mx m k n p (A : 'M_(m + k, n)) (B : 'M_(n, p)) :
  dsubmx A *m B = dsubmx (A *m B).
admit.
Defined.

 
Section LinRowVector.

Variables m n : nat.

Fact lin1_mx_key : unit.
admit.
Defined.
Definition lin1_mx (f : 'rV[R]_m -> 'rV[R]_n) :=
  \matrix[lin1_mx_key]_(i, j) f (delta_mx 0 i) 0 j.

Variable f : {linear 'rV[R]_m -> 'rV[R]_n}.

Lemma mul_rV_lin1 u : u *m lin1_mx f = f u.
admit.
Defined.

End LinRowVector.

 
Section LinMatrix.

Variables m1 n1 m2 n2 : nat.

Definition lin_mx (f : 'M[R]_(m1, n1) -> 'M[R]_(m2, n2)) :=
  lin1_mx (mxvec \o f \o vec_mx).

Variable f : {linear 'M[R]_(m1, n1) -> 'M[R]_(m2, n2)}.

Lemma mul_rV_lin u : u *m lin_mx f = mxvec (f (vec_mx u)).
admit.
Defined.

Lemma mul_vec_lin A : mxvec A *m lin_mx f = mxvec (f A).
admit.
Defined.

Lemma mx_rV_lin u : vec_mx (u *m lin_mx f) = f (vec_mx u).
admit.
Defined.

Lemma mx_vec_lin A : vec_mx (mxvec A *m lin_mx f) = f A.
admit.
Defined.

End LinMatrix.

Canonical mulmx_additive m n p A := Additive (@mulmxBr m n p A).

Section Mulmxr.

Variables m n p : nat.
Implicit Type A : 'M[R]_(m, n).
Implicit Type B : 'M[R]_(n, p).

Definition mulmxr B A := mulmx A B.
Arguments mulmxr B A /.

Definition lin_mulmxr B := lin_mx (mulmxr B).

Lemma mulmxr_is_linear B : linear (mulmxr B).
admit.
Defined.
Canonical mulmxr_additive B := Additive (mulmxr_is_linear B).
Canonical mulmxr_linear B := Linear (mulmxr_is_linear B).

Lemma lin_mulmxr_is_linear : linear lin_mulmxr.
admit.
Defined.
Canonical lin_mulmxr_additive := Additive lin_mulmxr_is_linear.
Canonical lin_mulmxr_linear := Linear lin_mulmxr_is_linear.

End Mulmxr.
Arguments mulmxr {_ _ _} B A /.

 
Section Trace.

Variable n : nat.

Definition mxtrace (A : 'M[R]_n) := \sum_i A i i.
Local Notation "'\tr' A" := (mxtrace A) : ring_scope.

Lemma mxtrace_tr A : \tr A^T = \tr A.
admit.
Defined.

Lemma mxtrace_is_scalar : scalar mxtrace.
admit.
Defined.
Canonical mxtrace_additive := Additive mxtrace_is_scalar.
Canonical mxtrace_linear := Linear mxtrace_is_scalar.

Lemma mxtrace0 : \tr 0 = 0.
admit.
Defined.
Lemma mxtraceD A B : \tr (A + B) = \tr A + \tr B.
admit.
Defined.
Lemma mxtraceZ a A : \tr (a *: A) = a * \tr A.
admit.
Defined.

Lemma mxtrace_diag D : \tr (diag_mx D) = \sum_j D 0 j.
admit.
Defined.

Lemma mxtrace_scalar a : \tr a%:M = a *+ n.
admit.
Defined.

Lemma mxtrace1 : \tr 1%:M = n%:R.
admit.
Defined.

End Trace.
Local Notation "'\tr' A" := (mxtrace A) : ring_scope.

Lemma trace_mx11 (A : 'M_1) : \tr A = A 0 0.
admit.
Defined.

Lemma mxtrace_block n1 n2 (Aul : 'M_n1) Aur Adl (Adr : 'M_n2) :
  \tr (block_mx Aul Aur Adl Adr) = \tr Aul + \tr Adr.
admit.
Defined.

 
 
Section MatrixRing.

Variable n' : nat.
Local Notation n := n'.+1.

Lemma matrix_nonzero1 : 1%:M != 0 :> 'M_n.
admit.
Defined.

Definition matrix_ringMixin :=
  RingMixin (@mulmxA n n n n) (@mul1mx n n) (@mulmx1 n n)
            (@mulmxDl n n n) (@mulmxDr n n n) matrix_nonzero1.

Canonical matrix_ringType := Eval hnf in RingType 'M[R]_n matrix_ringMixin.
Canonical matrix_lAlgType := Eval hnf in LalgType R 'M[R]_n (@scalemxAl n n n).

Lemma mulmxE : mulmx = *%R.
admit.
Defined.
Lemma idmxE : 1%:M = 1 :> 'M_n.
admit.
Defined.

Lemma scalar_mx_is_multiplicative : multiplicative (@scalar_mx n).
admit.
Defined.
Canonical scalar_mx_rmorphism := AddRMorphism scalar_mx_is_multiplicative.

End MatrixRing.

Section LiftPerm.

 

Variable n : nat.

 

Definition lift0_perm s : 'S_n.+1 := lift_perm 0 0 s.

Lemma lift0_perm0 s : lift0_perm s 0 = 0.
admit.
Defined.

Lemma lift0_perm_lift s k' :
  lift0_perm s (lift 0 k') = lift (0 : 'I_n.+1) (s k').
admit.
Defined.

Lemma lift0_permK s : cancel (lift0_perm s) (lift0_perm s^-1).
admit.
Defined.

Lemma lift0_perm_eq0 s i : (lift0_perm s i == 0) = (i == 0).
admit.
Defined.

 

Definition lift0_mx A : 'M_(1 + n) := block_mx 1 0 0 A.

Lemma lift0_mx_perm s : lift0_mx (perm_mx s) = perm_mx (lift0_perm s).
admit.
Defined.

Lemma lift0_mx_is_perm s : is_perm_mx (lift0_mx (perm_mx s)).
admit.
Defined.

End LiftPerm.

Lemma exp_block_diag_mx m n (A: 'M_m.+1) (B : 'M_n.+1) k :
  (block_mx A 0 0 B) ^+ k = block_mx (A ^+ k) 0 0 (B ^+ k).
admit.
Defined.

 
 
 

 
Definition determinant n (A : 'M_n) : R :=
  \sum_(s : 'S_n) (-1) ^+ s * \prod_i A i (s i).

 
Definition cofactor n A (i j : 'I_n) : R :=
  (-1) ^+ (i + j) * determinant (row' i (col' j A)).

 
Fact adjugate_key : unit.
admit.
Defined.
Definition adjugate n (A : 'M_n) := \matrix[adjugate_key]_(i, j) cofactor A j i.

End MatrixAlgebra.

Arguments delta_mx {R m n}.
Arguments scalar_mx {R n}.
Arguments perm_mx {R n}.
Arguments tperm_mx {R n}.
Arguments pid_mx {R m n}.
Arguments copid_mx {R n}.
Arguments lin_mulmxr {R m n p}.
Prenex Implicits diag_mx is_scalar_mx.
Prenex Implicits mulmx mxtrace determinant cofactor adjugate.

Arguments is_scalar_mxP {R n A}.
Arguments mul_delta_mx {R m n p}.

Hint Extern 0 (is_true (is_diag_mx (scalar_mx _))) =>
  apply: scalar_mx_is_diag : core.
Hint Extern 0 (is_true (is_trig_mx (scalar_mx _))) =>
  apply: scalar_mx_is_trig : core.
Hint Extern 0 (is_true (is_diag_mx (diag_mx _))) =>
  apply: diag_mx_is_diag : core.
Hint Extern 0 (is_true (is_trig_mx (diag_mx _))) =>
  apply: diag_mx_is_trig : core.

Notation "a %:M" := (scalar_mx a) : ring_scope.
Notation "A *m B" := (mulmx A B) : ring_scope.
Arguments mulmxr {_ _ _ _} B A /.
Notation "\tr A" := (mxtrace A) : ring_scope.
Notation "'\det' A" := (determinant A) : ring_scope.
Notation "'\adj' A" := (adjugate A) : ring_scope.

 
Lemma trmx_mul_rev (R : ringType) m n p (A : 'M[R]_(m, n)) (B : 'M[R]_(n, p)) :
  (A *m B)^T = (B : 'M[R^c]_(n, p))^T *m (A : 'M[R^c]_(m, n))^T.
admit.
Defined.

Canonical matrix_countZmodType (M : countZmodType) m n :=
  [countZmodType of 'M[M]_(m, n)].
Canonical matrix_countRingType (R : countRingType) n :=
  [countRingType of 'M[R]_n.+1].
Canonical matrix_finLmodType (R : finRingType) m n :=
  [finLmodType R of 'M[R]_(m, n)].
Canonical matrix_finRingType (R : finRingType) n' :=
  Eval hnf in [finRingType of 'M[R]_n'.+1].
Canonical matrix_finLalgType (R : finRingType) n' :=
  [finLalgType R of 'M[R]_n'.+1].

 
Section MapRingMatrix.

Variables (aR rR : ringType) (f : {rmorphism aR -> rR}).
Local Notation "A ^f" := (map_mx f A) : ring_scope.

Section FixedSize.

Variables m n p : nat.
Implicit Type A : 'M[aR]_(m, n).

Lemma map_mxZ a A : (a *: A)^f = f a *: A^f.
admit.
Defined.

Lemma map_mxM A B : (A *m B)^f = A^f *m B^f :> 'M_(m, p).
admit.
Defined.

Lemma map_delta_mx i j : (delta_mx i j)^f = delta_mx i j :> 'M_(m, n).
admit.
Defined.

Lemma map_diag_mx d : (diag_mx d)^f = diag_mx d^f :> 'M_n.
admit.
Defined.

Lemma map_scalar_mx a : a%:M^f = (f a)%:M :> 'M_n.
admit.
Defined.

Lemma map_mx1 : 1%:M^f = 1%:M :> 'M_n.
admit.
Defined.

Lemma map_perm_mx (s : 'S_n) : (perm_mx s)^f = perm_mx s.
admit.
Defined.

Lemma map_tperm_mx (i1 i2 : 'I_n) : (tperm_mx i1 i2)^f = tperm_mx i1 i2.
admit.
Defined.

Lemma map_pid_mx r : (pid_mx r)^f = pid_mx r :> 'M_(m, n).
admit.
Defined.

Lemma trace_map_mx (A : 'M_n) : \tr A^f = f (\tr A).
admit.
Defined.

Lemma det_map_mx n' (A : 'M_n') : \det A^f = f (\det A).
admit.
Defined.

Lemma cofactor_map_mx (A : 'M_n) i j : cofactor A^f i j = f (cofactor A i j).
admit.
Defined.

Lemma map_mx_adj (A : 'M_n) : (\adj A)^f = \adj A^f.
admit.
Defined.

End FixedSize.

Lemma map_copid_mx n r : (copid_mx r)^f = copid_mx r :> 'M_n.
admit.
Defined.

Lemma map_mx_is_multiplicative n' (n := n'.+1) :
  multiplicative (map_mx f : 'M_n -> 'M_n).
admit.
Defined.

Canonical map_mx_rmorphism n' := AddRMorphism (map_mx_is_multiplicative n').

Lemma map_lin1_mx m n (g : 'rV_m -> 'rV_n) gf :
  (forall v, (g v)^f = gf v^f) -> (lin1_mx g)^f = lin1_mx gf.
admit.
Defined.

Lemma map_lin_mx m1 n1 m2 n2 (g : 'M_(m1, n1) -> 'M_(m2, n2)) gf :
  (forall A, (g A)^f = gf A^f) -> (lin_mx g)^f = lin_mx gf.
admit.
Defined.

End MapRingMatrix.

Section CommMx.
 
 
 
 
 
 
 
 
 
 
 
 
 
 

Context {R : ringType} {n : nat}.
Implicit Types (f g p : 'M[R]_n) (fs : seq 'M[R]_n) (d : 'rV[R]_n) (I : Type).

Definition comm_mx  f g : Prop := f *m g =  g *m f.
Definition comm_mxb f g : bool := f *m g == g *m f.

Lemma comm_mx_sym f g : comm_mx f g -> comm_mx g f.
admit.
Defined.

Lemma comm_mx_refl f : comm_mx f f.
admit.
Defined.

Lemma comm_mx0 f : comm_mx f 0.
admit.
Defined.
Lemma comm0mx f : comm_mx 0 f.
admit.
Defined.

Lemma comm_mx1 f : comm_mx f 1%:M.
admit.
Defined.

Lemma comm1mx f : comm_mx 1%:M f.
admit.
Defined.

Hint Resolve comm_mx0 comm0mx comm_mx1 comm1mx : core.

Lemma comm_mxN f g : comm_mx f g -> comm_mx f (- g).
admit.
Defined.

Lemma comm_mxN1 f : comm_mx f (- 1%:M).
admit.
Defined.

Lemma comm_mxD f g g' : comm_mx f g -> comm_mx f g' -> comm_mx f (g + g').
admit.
Defined.

Lemma comm_mxB f g g' : comm_mx f g -> comm_mx f g' -> comm_mx f (g - g').
admit.
Defined.

Lemma comm_mxM f g g' : comm_mx f g -> comm_mx f g' -> comm_mx f (g *m g').
admit.
Defined.

Lemma comm_mx_sum I (s : seq I) (P : pred I) (F : I -> 'M[R]_n) (f : 'M[R]_n) :
  (forall i : I, P i -> comm_mx f (F i)) -> comm_mx f (\sum_(i <- s | P i) F i).
admit.
Defined.

Lemma comm_mxP f g : reflect (comm_mx f g) (comm_mxb f g).
admit.
Defined.

Notation all_comm_mx fs := (all2rel comm_mxb fs).

Lemma all_comm_mxP fs :
  reflect {in fs &, forall f g, f *m g = g *m f} (all_comm_mx fs).
admit.
Defined.

Lemma all_comm_mx1 f : all_comm_mx [:: f].
admit.
Defined.

Lemma all_comm_mx2P f g : reflect (f *m g = g *m f) (all_comm_mx [:: f; g]).
admit.
Defined.

Lemma all_comm_mx_cons f fs :
  all_comm_mx (f :: fs) = all (comm_mxb f) fs && all_comm_mx fs.
admit.
Defined.

End CommMx.
Notation all_comm_mx := (allrel comm_mxb).

Lemma comm_mxE (R : ringType) (n : nat) : @comm_mx R n.+1 = @GRing.comm _.
admit.
Defined.

Section ComMatrix.
 
Variable R : comRingType.

Section AssocLeft.

Variables m n p : nat.
Implicit Type A : 'M[R]_(m, n).
Implicit Type B : 'M[R]_(n, p).

Lemma trmx_mul A B : (A *m B)^T = B^T *m A^T.
admit.
Defined.

Lemma scalemxAr a A B : a *: (A *m B) = A *m (a *: B).
admit.
Defined.

Lemma mulmx_is_scalable A : scalable (@mulmx _ m n p A).
admit.
Defined.
Canonical mulmx_linear A := AddLinear (mulmx_is_scalable A).

Definition lin_mulmx A : 'M[R]_(n * p, m * p) := lin_mx (mulmx A).

Lemma lin_mulmx_is_linear : linear lin_mulmx.
admit.
Defined.
Canonical lin_mulmx_additive := Additive lin_mulmx_is_linear.
Canonical lin_mulmx_linear := Linear lin_mulmx_is_linear.

End AssocLeft.

Section LinMulRow.

Variables m n : nat.

Definition lin_mul_row u : 'M[R]_(m * n, n) := lin1_mx (mulmx u \o vec_mx).

Lemma lin_mul_row_is_linear : linear lin_mul_row.
admit.
Defined.
Canonical lin_mul_row_additive := Additive lin_mul_row_is_linear.
Canonical lin_mul_row_linear := Linear lin_mul_row_is_linear.

Lemma mul_vec_lin_row A u : mxvec A *m lin_mul_row u = u *m A.
admit.
Defined.

End LinMulRow.

Lemma mxvec_dotmul m n (A : 'M[R]_(m, n)) u v :
  mxvec (u^T *m v) *m (mxvec A)^T = u *m A *m v^T.
admit.
Defined.

Section MatrixAlgType.

Variable n' : nat.
Local Notation n := n'.+1.

Canonical matrix_algType :=
  Eval hnf in AlgType R 'M[R]_n (fun k => scalemxAr k).

End MatrixAlgType.

Lemma diag_mxC n (d e : 'rV[R]_n) :
  diag_mx d *m diag_mx e = diag_mx e *m diag_mx d.
admit.
Defined.

Lemma diag_mx_comm n (d e : 'rV[R]_n) : comm_mx (diag_mx d) (diag_mx e).
admit.
Defined.

Lemma scalar_mxC m n a (A : 'M[R]_(m, n)) : A *m a%:M = a%:M *m A.
admit.
Defined.

Lemma mul_mx_scalar m n a (A : 'M[R]_(m, n)) : A *m a%:M = a *: A.
admit.
Defined.

Lemma comm_mx_scalar n a (A : 'M[R]_n) : comm_mx A a%:M.
admit.
Defined.

Lemma comm_scalar_mx n a (A : 'M[R]_n) : comm_mx a%:M A.
admit.
Defined.

Lemma mxtrace_mulC m n (A : 'M[R]_(m, n)) B :
   \tr (A *m B) = \tr (B *m A).
admit.
Defined.

 

Lemma determinant_multilinear n (A B C : 'M[R]_n) i0 b c :
    row i0 A = b *: row i0 B + c *: row i0 C ->
    row' i0 B = row' i0 A ->
    row' i0 C = row' i0 A ->
  \det A = b * \det B + c * \det C.
admit.
Defined.

Lemma determinant_alternate n (A : 'M[R]_n) i1 i2 :
  i1 != i2 -> A i1 =1 A i2 -> \det A = 0.
admit.
Defined.

Lemma det_tr n (A : 'M[R]_n) : \det A^T = \det A.
admit.
Defined.

Lemma det_perm n (s : 'S_n) : \det (perm_mx s) = (-1) ^+ s :> R.
admit.
Defined.

Lemma det1 n : \det (1%:M : 'M[R]_n) = 1.
admit.
Defined.

Lemma det_mx00 (A : 'M[R]_0) : \det A = 1.
admit.
Defined.

Lemma detZ n a (A : 'M[R]_n) : \det (a *: A) = a ^+ n * \det A.
admit.
Defined.

Lemma det0 n' : \det (0 : 'M[R]_n'.+1) = 0.
admit.
Defined.

Lemma det_scalar n a : \det (a%:M : 'M[R]_n) = a ^+ n.
admit.
Defined.

Lemma det_scalar1 a : \det (a%:M : 'M[R]_1) = a.
admit.
Defined.

Lemma det_mx11  (M : 'M[R]_1) : \det M = M 0 0.
admit.
Defined.

Lemma det_mulmx n (A B : 'M[R]_n) : \det (A *m B) = \det A * \det B.
admit.
Defined.

Lemma detM n' (A B : 'M[R]_n'.+1) : \det (A * B) = \det A * \det B.
admit.
Defined.

 
Lemma expand_cofactor n (A : 'M[R]_n) i j :
  cofactor A i j =
    \sum_(s : 'S_n | s i == j) (-1) ^+ s * \prod_(k | i != k) A k (s k).
admit.
Defined.

Lemma expand_det_row n (A : 'M[R]_n) i0 :
  \det A = \sum_j A i0 j * cofactor A i0 j.
admit.
Defined.

Lemma cofactor_tr n (A : 'M[R]_n) i j : cofactor A^T i j = cofactor A j i.
admit.
Defined.

Lemma cofactorZ n a (A : 'M[R]_n) i j :
  cofactor (a *: A) i j = a ^+ n.-1 * cofactor A i j.
admit.
Defined.

Lemma expand_det_col n (A : 'M[R]_n) j0 :
  \det A = \sum_i (A i j0 * cofactor A i j0).
admit.
Defined.

Lemma trmx_adj n (A : 'M[R]_n) : (\adj A)^T = \adj A^T.
admit.
Defined.

Lemma adjZ n a (A : 'M[R]_n) : \adj (a *: A) = a^+n.-1 *: \adj A.
admit.
Defined.

 
Lemma mul_mx_adj n (A : 'M[R]_n) : A *m \adj A = (\det A)%:M.
admit.
Defined.

 
Lemma mul_adj_mx n (A : 'M[R]_n) : \adj A *m A = (\det A)%:M.
admit.
Defined.

Lemma adj1 n : \adj (1%:M) = 1%:M :> 'M[R]_n.
admit.
Defined.

 
Lemma mulmx1C n (A B : 'M[R]_n) : A *m B = 1%:M -> B *m A = 1%:M.
admit.
Defined.

 
Lemma mulmx1_min m n (A : 'M[R]_(m, n)) B : A *m B = 1%:M -> m <= n.
admit.
Defined.

Lemma det_ublock n1 n2 Aul (Aur : 'M[R]_(n1, n2)) Adr :
  \det (block_mx Aul Aur 0 Adr) = \det Aul * \det Adr.
admit.
Defined.

Lemma det_lblock n1 n2 Aul (Adl : 'M[R]_(n2, n1)) Adr :
  \det (block_mx Aul 0 Adl Adr) = \det Aul * \det Adr.
admit.
Defined.

Lemma det_trig n (A : 'M[R]_n) : is_trig_mx A -> \det A = \prod_(i < n) A i i.
admit.
Defined.

Lemma det_diag n (d : 'rV[R]_n) : \det (diag_mx d) = \prod_i d 0 i.
admit.
Defined.

End ComMatrix.

Arguments lin_mul_row {R m n} u.
Arguments lin_mulmx {R m n p} A.
Arguments comm_mx_scalar {R n}.
Arguments comm_scalar_mx {R n}.
Arguments diag_mx_comm {R n}.

Canonical matrix_finAlgType (R : finComRingType) n' :=
  [finAlgType R of 'M[R]_n'.+1].

Hint Resolve comm_mx_scalar comm_scalar_mx : core.

#[deprecated(since="mathcomp 1.12.0", note="Use comm_mx_scalar instead.")]
Notation scalar_mx_comm := comm_mx_scalar (only parsing).

 
 
 

Section MatrixInv.

Variables R : comUnitRingType.

Section Defs.

Variable n : nat.
Implicit Type A : 'M[R]_n.

Definition unitmx : pred 'M[R]_n := fun A => \det A \is a GRing.unit.
Definition invmx A := if A \in unitmx then (\det A)^-1 *: \adj A else A.

Lemma unitmxE A : (A \in unitmx) = (\det A \is a GRing.unit).
admit.
Defined.

Lemma unitmx1 : 1%:M \in unitmx.
admit.
Defined.

Lemma unitmx_perm s : perm_mx s \in unitmx.
admit.
Defined.

Lemma unitmx_tr A : (A^T \in unitmx) = (A \in unitmx).
admit.
Defined.

Lemma unitmxZ a A : a \is a GRing.unit -> (a *: A \in unitmx) = (A \in unitmx).
admit.
Defined.

Lemma invmx1 : invmx 1%:M = 1%:M.
admit.
Defined.

Lemma invmxZ a A : a *: A \in unitmx -> invmx (a *: A) = a^-1 *: invmx A.
admit.
Defined.

Lemma invmx_scalar a : invmx (a%:M) = a^-1%:M.
admit.
Defined.

Lemma mulVmx : {in unitmx, left_inverse 1%:M invmx mulmx}.
admit.
Defined.

Lemma mulmxV : {in unitmx, right_inverse 1%:M invmx mulmx}.
admit.
Defined.

Lemma mulKmx m : {in unitmx, @left_loop _ 'M_(n, m) invmx mulmx}.
admit.
Defined.

Lemma mulKVmx m : {in unitmx, @rev_left_loop _ 'M_(n, m) invmx mulmx}.
admit.
Defined.

Lemma mulmxK m : {in unitmx, @right_loop 'M_(m, n) _ invmx mulmx}.
admit.
Defined.

Lemma mulmxKV m : {in unitmx, @rev_right_loop 'M_(m, n) _ invmx mulmx}.
admit.
Defined.

Lemma det_inv A : \det (invmx A) = (\det A)^-1.
admit.
Defined.

Lemma unitmx_inv A : (invmx A \in unitmx) = (A \in unitmx).
admit.
Defined.

Lemma unitmx_mul A B : (A *m B \in unitmx) = (A \in unitmx) && (B \in unitmx).
admit.
Defined.

Lemma trmx_inv (A : 'M_n) : (invmx A)^T = invmx (A^T).
admit.
Defined.

Lemma invmxK : involutive invmx.
admit.
Defined.

Lemma mulmx1_unit A B : A *m B = 1%:M -> A \in unitmx /\ B \in unitmx.
admit.
Defined.

Lemma intro_unitmx A B : B *m A = 1%:M /\ A *m B = 1%:M -> unitmx A.
admit.
Defined.

Lemma invmx_out : {in [predC unitmx], invmx =1 id}.
admit.
Defined.

End Defs.

Variable n' : nat.
Local Notation n := n'.+1.

Definition matrix_unitRingMixin :=
  UnitRingMixin (@mulVmx n) (@mulmxV n) (@intro_unitmx n) (@invmx_out n).
Canonical matrix_unitRing :=
  Eval hnf in UnitRingType 'M[R]_n matrix_unitRingMixin.
Canonical matrix_unitAlg := Eval hnf in [unitAlgType R of 'M[R]_n].

 

Lemma detV (A : 'M_n) : \det A^-1 = (\det A)^-1.
admit.
Defined.

Lemma unitr_trmx (A : 'M_n) : (A^T  \is a GRing.unit) = (A \is a GRing.unit).
admit.
Defined.

Lemma trmxV (A : 'M_n) : A^-1^T = (A^T)^-1.
admit.
Defined.

Lemma perm_mxV (s : 'S_n) : perm_mx s^-1 = (perm_mx s)^-1.
admit.
Defined.

Lemma is_perm_mxV (A : 'M_n) : is_perm_mx A^-1 = is_perm_mx A.
admit.
Defined.

End MatrixInv.

Prenex Implicits unitmx invmx invmxK.

Lemma block_diag_mx_unit (R : comUnitRingType) n1 n2
      (Aul : 'M[R]_n1) (Adr : 'M[R]_n2) :
  (block_mx Aul 0 0 Adr \in unitmx) = (Aul \in unitmx) && (Adr \in unitmx).
admit.
Defined.

Lemma invmx_block_diag (R : comUnitRingType) n1 n2
     (Aul : 'M[R]_n1) (Adr : 'M[R]_n2) :
  block_mx Aul 0 0 Adr \in unitmx ->
  invmx (block_mx Aul 0 0 Adr) = block_mx (invmx Aul) 0 0 (invmx Adr).
admit.
Defined.

Canonical matrix_countUnitRingType (R : countComUnitRingType) n :=
  [countUnitRingType of 'M[R]_n.+1].

 
Section FinUnitMatrix.

Variables (n : nat) (R : finComUnitRingType).

Canonical matrix_finUnitRingType n' :=
  Eval hnf in [finUnitRingType of 'M[R]_n'.+1].

Definition GLtype of phant R := {unit 'M[R]_n.-1.+1}.

Coercion GLval ph (u : GLtype ph) : 'M[R]_n.-1.+1 :=
  let: FinRing.Unit A _ := u in A.

End FinUnitMatrix.

Bind Scope group_scope with GLtype.
Arguments GLval {n%N R ph} u%g.

Notation "{ ''GL_' n [ R ] }" := (GLtype n (Phant R))
  (at level 0, n at level 2, format "{ ''GL_' n [ R ] }") : type_scope.
Notation "{ ''GL_' n ( p ) }" := {'GL_n['F_p]}
  (at level 0, n at level 2, p at level 10,
    format "{ ''GL_' n ( p ) }") : type_scope.

Section GL_unit.

Variables (n : nat) (R : finComUnitRingType).

Canonical GL_subType := [subType of {'GL_n[R]} for GLval].
Definition GL_eqMixin := Eval hnf in [eqMixin of {'GL_n[R]} by <:].
Canonical GL_eqType := Eval hnf in EqType {'GL_n[R]} GL_eqMixin.
Canonical GL_choiceType := Eval hnf in [choiceType of {'GL_n[R]}].
Canonical GL_countType := Eval hnf in [countType of {'GL_n[R]}].
Canonical GL_subCountType := Eval hnf in [subCountType of {'GL_n[R]}].
Canonical GL_finType := Eval hnf in [finType of {'GL_n[R]}].
Canonical GL_subFinType := Eval hnf in [subFinType of {'GL_n[R]}].
Canonical GL_baseFinGroupType := Eval hnf in [baseFinGroupType of {'GL_n[R]}].
Canonical GL_finGroupType := Eval hnf in [finGroupType of {'GL_n[R]}].
Definition GLgroup of phant R := [set: {'GL_n[R]}].
Canonical GLgroup_group ph := Eval hnf in [group of GLgroup ph].

Implicit Types u v : {'GL_n[R]}.

Lemma GL_1E : GLval 1 = 1.
admit.
Defined.
Lemma GL_VE u : GLval u^-1 = (GLval u)^-1.
admit.
Defined.
Lemma GL_VxE u : GLval u^-1 = invmx u.
admit.
Defined.
Lemma GL_ME u v : GLval (u * v) = GLval u * GLval v.
admit.
Defined.
Lemma GL_MxE u v : GLval (u * v) = u *m v.
admit.
Defined.
Lemma GL_unit u : GLval u \is a GRing.unit.
admit.
Defined.
Lemma GL_unitmx u : val u \in unitmx.
admit.
Defined.

Lemma GL_det u : \det u != 0.
admit.
Defined.

End GL_unit.

Notation "''GL_' n [ R ]" := (GLgroup n (Phant R))
  (at level 8, n at level 2, format "''GL_' n [ R ]") : group_scope.
Notation "''GL_' n ( p )" := 'GL_n['F_p]
  (at level 8, n at level 2, p at level 10,
   format "''GL_' n ( p )") : group_scope.
Notation "''GL_' n [ R ]" := (GLgroup_group n (Phant R)) : Group_scope.
Notation "''GL_' n ( p )" := (GLgroup_group n (Phant 'F_p)) : Group_scope.

 
 
 

Section MatrixDomain.

Variable R : idomainType.

Lemma scalemx_eq0 m n a (A : 'M[R]_(m, n)) :
  (a *: A == 0) = (a == 0) || (A == 0).
admit.
Defined.

Lemma scalemx_inj m n a :
  a != 0 -> injective ( *:%R a : 'M[R]_(m, n) -> 'M[R]_(m, n)).
admit.
Defined.

Lemma det0P n (A : 'M[R]_n) :
  reflect (exists2 v : 'rV[R]_n, v != 0 & v *m A = 0) (\det A == 0).
admit.
Defined.

End MatrixDomain.

Arguments det0P {R n A}.

 
 
Section MapFieldMatrix.

Variables (aF : fieldType) (rF : comUnitRingType) (f : {rmorphism aF -> rF}).
Local Notation "A ^f" := (map_mx f A) : ring_scope.

Lemma map_mx_inj {m n} : injective (map_mx f : 'M_(m, n) -> 'M_(m, n)).
admit.
Defined.

Lemma map_mx_is_scalar n (A : 'M_n) : is_scalar_mx A^f = is_scalar_mx A.
admit.
Defined.

Lemma map_unitmx n (A : 'M_n) : (A^f \in unitmx) = (A \in unitmx).
admit.
Defined.

Lemma map_mx_unit n' (A : 'M_n'.+1) :
  (A^f \is a GRing.unit) = (A \is a GRing.unit).
admit.
Defined.

Lemma map_invmx n (A : 'M_n) : (invmx A)^f = invmx A^f.
admit.
Defined.

Lemma map_mx_inv n' (A : 'M_n'.+1) : A^-1^f = A^f^-1.
admit.
Defined.

Lemma map_mx_eq0 m n (A : 'M_(m, n)) : (A^f == 0) = (A == 0).
admit.
Defined.

End MapFieldMatrix.

Arguments map_mx_inj {aF rF f m n} [A1 A2] eqA12f : rename.

 
 
 

Section CormenLUP.

Variable F : fieldType.

 
 
 
 

Fixpoint cormen_lup {n} :=
  match n return let M := 'M[F]_n.+1 in M -> M * M * M with
  | 0 => fun A => (1, 1, A)
  | _.+1 => fun A =>
    let k := odflt 0 [pick k | A k 0 != 0] in
    let A1 : 'M_(1 + _) := xrow 0 k A in
    let P1 : 'M_(1 + _) := tperm_mx 0 k in
    let Schur := ((A k 0)^-1 *: dlsubmx A1) *m ursubmx A1 in
    let: (P2, L2, U2) := cormen_lup (drsubmx A1 - Schur) in
    let P := block_mx 1 0 0 P2 *m P1 in
    let L := block_mx 1 0 ((A k 0)^-1 *: (P2 *m dlsubmx A1)) L2 in
    let U := block_mx (ulsubmx A1) (ursubmx A1) 0 U2 in
    (P, L, U)
  end.

Lemma cormen_lup_perm n (A : 'M_n.+1) : is_perm_mx (cormen_lup A).1.1.
admit.
Defined.

Lemma cormen_lup_correct n (A : 'M_n.+1) :
  let: (P, L, U) := cormen_lup A in P * A = L * U.
admit.
Defined.

Lemma cormen_lup_detL n (A : 'M_n.+1) : \det (cormen_lup A).1.2 = 1.
admit.
Defined.

Lemma cormen_lup_lower n A (i j : 'I_n.+1) :
  i <= j -> (cormen_lup A).1.2 i j = (i == j)%:R.
admit.
Defined.

Lemma cormen_lup_upper n A (i j : 'I_n.+1) :
  j < i -> (cormen_lup A).2 i j = 0 :> F.
admit.
Defined.

End CormenLUP.

Section mxOver.
Section mxOverType.
Context {m n : nat} {T : Type}.
Implicit Types (S : {pred T}).

Definition mxOver (S : {pred T}) :=
  [qualify a M : 'M[T]_(m, n) | [forall i, [forall j, M i j \in S]]].

Fact mxOver_key S : pred_key (mxOver S).
Proof.
by [].
Qed.
Canonical mxOver_keyed S := KeyedQualifier (mxOver_key S).

Lemma mxOverP {S : {pred T}} {M : 'M[T]__} :
  reflect (forall i j, M i j \in S) (M \is a mxOver S).
admit.
Defined.

Lemma mxOverS (S1 S2 : {pred T}) :
  {subset S1 <= S2} -> {subset mxOver S1 <= mxOver S2}.
admit.
Defined.

Lemma mxOver_const c S : c \in S -> const_mx c \is a mxOver S.
admit.
Defined.

Lemma mxOver_constE c S : (m > 0)%N -> (n > 0)%N ->
  (const_mx c \is a mxOver S) = (c \in S).
admit.
Defined.

End mxOverType.

Lemma thinmxOver {n : nat} {T : Type} (M : 'M[T]_(n, 0)) S : M \is a mxOver S.
admit.
Defined.

Lemma flatmxOver {n : nat} {T : Type} (M : 'M[T]_(0, n)) S : M \is a mxOver S.
admit.
Defined.

Section mxOverZmodule.
Context {M : zmodType} {m n : nat}.
Implicit Types (S : {pred M}).

Lemma mxOver0 S : 0 \in S -> 0 \is a @mxOver m n _ S.
admit.
Defined.

Section mxOverAdd.
Variables (S : {pred M}) (addS : addrPred S) (kS : keyed_pred addS).
Fact mxOver_add_subproof : addr_closed (@mxOver m n _ kS).
admit.
Defined.
Canonical mxOver_addrPred := AddrPred mxOver_add_subproof.
End mxOverAdd.

Section mxOverOpp.
Variables (S : {pred M}) (oppS : opprPred S) (kS : keyed_pred oppS).
Fact mxOver_opp_subproof : oppr_closed (@mxOver m n _ kS).
admit.
Defined.
Canonical mxOver_opprPred := OpprPred mxOver_opp_subproof.
End mxOverOpp.

Canonical mxOver_zmodPred (S : {pred M}) (zmodS : zmodPred S)
  (kS : keyed_pred zmodS) := ZmodPred (@mxOver_opp_subproof _ _ kS).

End mxOverZmodule.

Section mxOverRing.
Context {R : ringType} {m n : nat}.

Lemma mxOver_scalar S c : 0 \in S -> c \in S -> c%:M \is a @mxOver n n R S.
admit.
Defined.

Lemma mxOver_scalarE S c : (n > 0)%N ->
  (c%:M \is a @mxOver n n R S) = ((n > 1) ==> (0 \in S)) && (c \in S).
admit.
Defined.

Section mxOverScale.
Variables (S : {pred R}) (mulS : mulrPred S) (kS : keyed_pred mulS).
Lemma mxOverZ : {in kS & mxOver kS, forall a : R, forall v : 'M[R]_(m, n),
        a *: v \is a mxOver kS}.
admit.
Defined.
End mxOverScale.

Lemma mxOver_diag (S : {pred R}) k (D : 'rV[R]_k) :
   0 \in S -> D \is a mxOver S -> diag_mx D \is a mxOver S.
admit.
Defined.

Lemma mxOver_diagE (S : {pred R}) k (D : 'rV[R]_k) : k > 0 ->
  (diag_mx D \is a mxOver S) = ((k > 1) ==> (0 \in S)) && (D \is a mxOver S).
admit.
Defined.

Section mxOverMul.

Variables (S : predPredType R) (ringS : semiringPred S) (kS : keyed_pred ringS).

Lemma mxOverM p q r : {in mxOver kS & mxOver kS,
  forall u : 'M[R]_(p, q), forall v : 'M[R]_(q, r), u *m v \is a mxOver kS}.
admit.
Defined.

End mxOverMul.
End mxOverRing.

Section mxRingOver.
Context {R : ringType} {n : nat}.

Section semiring.
Variables (S : {pred R}) (ringS : semiringPred S) (kS : keyed_pred ringS).
Fact mxOver_mul_subproof : mulr_closed (@mxOver n.+1 n.+1 _ kS).
admit.
Defined.
Canonical mxOver_mulrPred := MulrPred mxOver_mul_subproof.
Canonical mxOver_semiringPred := SemiringPred mxOver_mul_subproof.
End semiring.

Canonical mxOver_subringPred (S : {pred R}) (ringS : subringPred S)
   (kS : keyed_pred ringS):= SubringPred (mxOver_mul_subproof kS).

End mxRingOver.
End mxOver.

#[deprecated(since="mathcomp 1.12.0", note="Use map_mxB instead.")]
Notation map_mx_sub := map_mxB (only parsing).

Section BlockMatrix.
Import tagnat.
Context {T : Type} {p q : nat} {p_ : 'I_p -> nat} {q_ : 'I_q -> nat}.
Notation sp := (\sum_i p_ i)%N.
Notation sq := (\sum_i q_ i)%N.
Implicit Type (s : 'I_sp) (t : 'I_sq).

Definition mxblock (B_ : forall i j, 'M[T]_(p_ i, q_ j)) :=
  \matrix_(j, k) B_ (sig1 j) (sig1 k) (sig2 j) (sig2 k).
Local Notation "\mxblock_ ( i , j ) E" := (mxblock (fun i j => E)) : ring_scope.

Definition mxrow m (B_ : forall j, 'M[T]_(m, q_ j)) :=
  \matrix_(j, k) B_ (sig1 k) j (sig2 k).
Local Notation "\mxrow_ i E" := (mxrow (fun i => E)) : ring_scope.

Definition mxcol n (B_ : forall i, 'M[T]_(p_ i, n)) :=
  \matrix_(j, k) B_ (sig1 j) (sig2 j) k.
Local Notation "\mxcol_ i E" := (mxcol (fun i => E)) : ring_scope.

Definition submxblock (A : 'M[T]_(sp, sq)) i j := mxsub  (Rank i) (Rank j) A.
Definition submxrow m (A : 'M[T]_(m, sq))    j := colsub          (Rank j) A.
Definition submxcol n (A : 'M[T]_(sp, n))  i   := rowsub (Rank i)          A.

Lemma mxblockEh B_ : \mxblock_(i, j) B_ i j = \mxrow_j \mxcol_i B_ i j.
admit.
Defined.

Lemma mxblockEv B_ : \mxblock_(i, j) B_ i j = \mxcol_i \mxrow_j B_ i j.
admit.
Defined.

Lemma submxblockEh A i j : submxblock A i j = submxcol (submxrow A j) i.
admit.
Defined.

Lemma submxblockEv A i j : submxblock A i j = submxrow (submxcol A i) j.
admit.
Defined.

Lemma mxblockK B_ i j : submxblock (\mxblock_(i, j) B_ i j) i j = B_ i j.
admit.
Defined.

Lemma mxrowK m B_ j : @submxrow m (\mxrow_j B_ j) j = B_ j.
admit.
Defined.

Lemma mxcolK n B_ i : @submxcol n (\mxcol_i B_ i) i = B_ i.
admit.
Defined.

Lemma submxrow_matrix B_ j :
  submxrow (\mxblock_(i, j) B_ i j) j = \mxcol_i B_ i j.
admit.
Defined.

Lemma submxcol_matrix B_ i :
  submxcol (\mxblock_(i, j) B_ i j) i = \mxrow_j B_ i j.
admit.
Defined.

Lemma submxblockK A : \mxblock_(i, j) (submxblock A i j) = A.
admit.
Defined.

Lemma submxrowK m (A : 'M[T]_(m, sq)) : \mxrow_j (submxrow A j) = A.
admit.
Defined.

Lemma submxcolK n (A : 'M[T]_(sp, n)) : \mxcol_i (submxcol A i) = A.
admit.
Defined.

Lemma mxblockP A B :
  (forall i j, submxblock A i j = submxblock B i j) <-> A = B.
admit.
Defined.

Lemma mxrowP m (A B : 'M_(m, sq)) :
  (forall j, submxrow A j = submxrow B j) <-> A = B.
admit.
Defined.

Lemma mxcolP n (A B : 'M_(sp, n)) :
  (forall i, submxcol A i = submxcol B i) <-> A = B.
admit.
Defined.

Lemma eq_mxblockP A_ B_ :
  (forall i j, A_ i j = B_ i j) <->
  (\mxblock_(i, j) A_ i j = \mxblock_(i, j) B_ i j).
admit.
Defined.

Lemma eq_mxblock A_ B_ :
  (forall i j, A_ i j = B_ i j) ->
  (\mxblock_(i, j) A_ i j = \mxblock_(i, j) B_ i j).
admit.
Defined.

Lemma eq_mxrowP m (A_ B_ : forall j, 'M[T]_(m, q_ j)) :
  (forall j, A_ j = B_ j) <-> (\mxrow_j A_ j = \mxrow_j B_ j).
admit.
Defined.

Lemma eq_mxrow m (A_ B_ : forall j, 'M[T]_(m, q_ j)) :
  (forall j, A_ j = B_ j) -> (\mxrow_j A_ j = \mxrow_j B_ j).
admit.
Defined.

Lemma eq_mxcolP n (A_ B_ : forall i, 'M[T]_(p_ i, n)) :
  (forall i, A_ i = B_ i) <-> (\mxcol_i A_ i = \mxcol_i B_ i).
admit.
Defined.

Lemma eq_mxcol n (A_ B_ : forall i, 'M[T]_(p_ i, n)) :
  (forall i, A_ i = B_ i) -> (\mxcol_i A_ i = \mxcol_i B_ i).
admit.
Defined.

Lemma row_mxrow m (B_ : forall j, 'M[T]_(m, q_ j)) i :
  row i (\mxrow_j B_ j) = \mxrow_j (row i (B_ j)).
admit.
Defined.

Lemma col_mxrow m (B_ : forall j, 'M[T]_(m, q_ j)) j :
  col j (\mxrow_j B_ j) = col (sig2 j) (B_ (sig1 j)).
admit.
Defined.

Lemma row_mxcol n (B_ : forall i, 'M[T]_(p_ i, n)) i :
  row i (\mxcol_i B_ i) = row (sig2 i) (B_ (sig1 i)).
admit.
Defined.

Lemma col_mxcol n (B_ : forall i, 'M[T]_(p_ i, n)) j :
  col j (\mxcol_i B_ i) = \mxcol_i (col j (B_ i)).
admit.
Defined.

Lemma row_mxblock B_ i :
  row i (\mxblock_(i, j) B_ i j) = \mxrow_j row (sig2 i) (B_ (sig1 i) j).
admit.
Defined.

Lemma col_mxblock B_ j :
  col j (\mxblock_(i, j) B_ i j) = \mxcol_i col (sig2 j) (B_ i (sig1 j)).
admit.
Defined.

End BlockMatrix.

Notation "\mxblock_ ( i < m , j < n ) E" :=
  (mxblock (fun (i : 'I_m) (j : 'I_ n) => E)) (only parsing) : ring_scope.
Notation "\mxblock_ ( i , j < n ) E" :=
  (\mxblock_(i < n, j < n) E) (only parsing) : ring_scope.
Notation "\mxblock_ ( i , j ) E" := (\mxblock_(i < _, j < _) E) : ring_scope.
Notation "\mxrow_ ( j < m ) E" := (mxrow (fun (j : 'I_m) => E))
  (only parsing) : ring_scope.
Notation "\mxrow_ j E" := (\mxrow_(j < _) E) : ring_scope.
Notation "\mxcol_ ( i < m ) E" := (mxcol (fun (i : 'I_m) => E))
  (only parsing) : ring_scope.
Notation "\mxcol_ i E" := (\mxcol_(i < _) E) : ring_scope.

Lemma tr_mxblock {T : Type} {p q : nat} {p_ : 'I_p -> nat} {q_ : 'I_q -> nat}
  (B_ : forall i j, 'M[T]_(p_ i, q_ j)) :
  (\mxblock_(i, j) B_ i j)^T = \mxblock_(i, j) (B_ j i)^T.
admit.
Defined.

Section SquareBlockMatrix.

Context {T : Type} {p : nat} {p_ : 'I_p -> nat}.
Notation sp := (\sum_i p_ i)%N.
Implicit Type (s : 'I_sp).

Lemma tr_mxrow n (B_ : forall j, 'M[T]_(n, p_ j)) :
  (\mxrow_j B_ j)^T = \mxcol_i (B_ i)^T.
admit.
Defined.

Lemma tr_mxcol n (B_ : forall i, 'M[T]_(p_ i, n)) :
  (\mxcol_i B_ i)^T = \mxrow_i (B_ i)^T.
admit.
Defined.

Lemma tr_submxblock (A : 'M[T]_sp) i j :
  (submxblock A i j)^T = (submxblock A^T j i).
admit.
Defined.

Lemma tr_submxrow n (A : 'M[T]_(n, sp)) j :
  (submxrow A j)^T = (submxcol A^T j).
admit.
Defined.

Lemma tr_submxcol n (A : 'M[T]_(sp, n)) i :
  (submxcol A i)^T = (submxrow A^T i).
admit.
Defined.

End SquareBlockMatrix.

Section BlockRowRecL.
Import tagnat.
Context {T : Type} {m : nat} {p_ : 'I_m.+1 -> nat}.
Notation sp := (\sum_i p_ i)%N.

Lemma mxsize_recl : (p_ ord0 + \sum_i p_ (lift ord0 i) = (\sum_i p_ i))%N.
admit.
Defined.

Lemma mxrow_recl n (B_ : forall j, 'M[T]_(n, p_ j)) :
  \mxrow_j B_ j = castmx (erefl, mxsize_recl)
    (row_mx (B_ 0) (\mxrow_j B_ (lift ord0 j))).
admit.
Defined.

End BlockRowRecL.

Lemma mxcol_recu {T : Type} {p : nat} {p_ : 'I_p.+1 -> nat} m
    (B_ : forall j, 'M[T]_(p_ j, m)) :
  \mxcol_j B_ j = castmx (mxsize_recl, erefl)
    (col_mx (B_ 0) (\mxcol_j B_ (lift ord0 j))).
admit.
Defined.

Section BlockMatrixRec.
Local Notation e := (mxsize_recl, mxsize_recl).
Local Notation l0 := (lift ord0).
Context {T : Type}.

Lemma mxblock_recu {p q : nat} {p_ : 'I_p.+1 -> nat} {q_ : 'I_q -> nat}
    (B_ : forall i j, 'M[T]_(p_ i, q_ j)) :
  \mxblock_(i, j) B_ i j = castmx (mxsize_recl, erefl) (col_mx
     (\mxrow_j B_ ord0 j)
     (\mxblock_(i, j) B_ (l0 i) j)).
admit.
Defined.

Lemma mxblock_recl {p q : nat} {p_ : 'I_p -> nat} {q_ : 'I_q.+1 -> nat}
    (B_ : forall i j, 'M[T]_(p_ i, q_ j)) :
  \mxblock_(i, j) B_ i j = castmx (erefl, mxsize_recl)
  (row_mx (\mxcol_i B_ i ord0) (\mxblock_(i, j) B_ i (l0 j))).
admit.
Defined.

Lemma mxblock_recul {p q : nat} {p_ : 'I_p.+1 -> nat} {q_ : 'I_q.+1 -> nat}
    (B_ : forall i j, 'M[T]_(p_ i, q_ j)) :
  \mxblock_(i, j) B_ i j = castmx e (block_mx
     (B_ 0 0)                  (\mxrow_j B_ ord0 (l0 j))
     (\mxcol_i B_ (l0 i) ord0) (\mxblock_(i, j) B_ (l0 i) (l0 j))).
admit.
Defined.

Lemma mxrowEblock {q : nat} {q_ : 'I_q -> nat} m
    (R_ : forall j, 'M[T]_(m, q_ j)) :
  (\mxrow_j R_ j) =
  castmx (big_ord1 _ (fun=> m), erefl) (\mxblock_(i < 1, j < q) R_ j).
admit.
Defined.

Lemma mxcolEblock {p : nat} {p_ : 'I_p -> nat} n
    (C_ : forall i, 'M[T]_(p_ i, n)) :
  (\mxcol_i C_ i) =
  castmx (erefl, big_ord1 _ (fun=> n)) (\mxblock_(i < p, j < 1) C_ i).
admit.
Defined.

Lemma mxEmxrow m n (A : 'M[T]_(m, n)) :
  A = castmx (erefl, big_ord1 _ (fun=> n)) (\mxrow__ A).
admit.
Defined.

Lemma mxEmxcol m n (A : 'M[T]_(m, n)) :
  A = castmx (big_ord1 _ (fun=> m), erefl) (\mxcol__ A).
admit.
Defined.

Lemma mxEmxblock m n (A : 'M[T]_(m, n)) :
  A = castmx (big_ord1 _ (fun=> m), big_ord1 _ (fun=> n))
             (\mxblock_(i < 1, j < 1) A).
admit.
Defined.

End BlockMatrixRec.

Section BlockRowZmod.
Context {V : zmodType} {q : nat} {q_ : 'I_q -> nat}.
Notation sq := (\sum_i q_ i)%N.
Implicit Type (s : 'I_sq).

Lemma mxrowD m (R_ R'_ : forall j, 'M[V]_(m, q_ j)) :
  \mxrow_j (R_ j + R'_ j) = \mxrow_j (R_ j) + \mxrow_j (R'_ j).
admit.
Defined.

Lemma mxrowN m (R_ : forall j, 'M[V]_(m, q_ j)) :
  \mxrow_j (- R_ j) = - \mxrow_j (R_ j).
admit.
Defined.

Lemma mxrowB m (R_ R'_ : forall j, 'M[V]_(m, q_ j)) :
  \mxrow_j (R_ j - R'_ j) = \mxrow_j (R_ j) - \mxrow_j (R'_ j).
admit.
Defined.

Lemma mxrow0 m : \mxrow_j (0 : 'M[V]_(m, q_ j)) = 0.
admit.
Defined.

Lemma mxrow_const m a : \mxrow_j (const_mx a : 'M[V]_(m, q_ j)) = const_mx a.
admit.
Defined.

Lemma mxrow_sum (J : finType) m
    (R_ : forall i j, 'M[V]_(m, q_ j)) (P : {pred J}) :
  \mxrow_j (\sum_(i | P i) R_ i j) = \sum_(i | P i) \mxrow_j (R_ i j).
admit.
Defined.

Lemma submxrowD m (B B' : 'M[V]_(m, sq)) j :
 submxrow (B + B') j = submxrow B j + submxrow B' j.
admit.
Defined.

Lemma submxrowN m (B : 'M[V]_(m, sq)) j :
 submxrow (- B) j = - submxrow B j.
admit.
Defined.

Lemma submxrowB m (B B' : 'M[V]_(m, sq)) j :
 submxrow (B - B') j = submxrow B j - submxrow B' j.
admit.
Defined.

Lemma submxrow0 m j : submxrow (0 : 'M[V]_(m, sq)) j = 0.
admit.
Defined.

Lemma submxrow_sum (J : finType) m
   (R_ : forall i, 'M[V]_(m, sq)) (P : {pred J}) j:
  submxrow (\sum_(i | P i) R_ i) j = \sum_(i | P i) submxrow (R_ i) j.
admit.
Defined.

End BlockRowZmod.

Section BlockRowRing.
Context {R : ringType} {n : nat} {q_ : 'I_n -> nat}.
Notation sq := (\sum_i q_ i)%N.
Implicit Type (s : 'I_sq).

Lemma mul_mxrow m n' (A : 'M[R]_(m, n')) (R_ : forall j, 'M[R]_(n', q_ j)) :
  A *m \mxrow_j R_ j= \mxrow_j (A *m R_ j).
admit.
Defined.

Lemma mul_submxrow m n' (A : 'M[R]_(m, n')) (B : 'M[R]_(n', sq)) j :
  A *m submxrow B j= submxrow (A *m B) j.
admit.
Defined.

End BlockRowRing.

Section BlockColZmod.
Context {V : zmodType} {n : nat} {p_ : 'I_n -> nat}.
Notation sp := (\sum_i p_ i)%N.
Implicit Type (s : 'I_sp).

Lemma mxcolD m (C_ C'_ : forall i, 'M[V]_(p_ i, m)) :
  \mxcol_i (C_ i + C'_ i) = \mxcol_i (C_ i) + \mxcol_i (C'_ i).
admit.
Defined.

Lemma mxcolN m (C_ : forall i, 'M[V]_(p_ i, m)) :
  \mxcol_i (- C_ i) = - \mxcol_i (C_ i).
admit.
Defined.

Lemma mxcolB m (C_ C'_ : forall i, 'M[V]_(p_ i, m)) :
  \mxcol_i (C_ i - C'_ i) = \mxcol_i (C_ i) - \mxcol_i (C'_ i).
admit.
Defined.

Lemma mxcol0 m : \mxcol_i (0 : 'M[V]_(p_ i, m)) = 0.
admit.
Defined.

Lemma mxcol_const m a : \mxcol_j (const_mx a : 'M[V]_(p_ j, m)) = const_mx a.
admit.
Defined.

Lemma mxcol_sum (I : finType) m (C_ : forall j i, 'M[V]_(p_ i, m)) (P : {pred I}):
  \mxcol_i (\sum_(j | P j) C_ j i) = \sum_(j | P j) \mxcol_i (C_ j i).
admit.
Defined.

Lemma submxcolD m (B B' : 'M[V]_(sp, m)) i :
 submxcol (B + B') i = submxcol B i + submxcol B' i.
admit.
Defined.

Lemma submxcolN m (B : 'M[V]_(sp, m)) i :
 submxcol (- B) i = - submxcol B i.
admit.
Defined.

Lemma submxcolB m (B B' : 'M[V]_(sp, m)) i :
 submxcol (B - B') i = submxcol B i - submxcol B' i.
admit.
Defined.

Lemma submxcol0 m i : submxcol (0 : 'M[V]_(sp, m)) i = 0.
admit.
Defined.

Lemma submxcol_sum (I : finType) m
   (C_ : forall j, 'M[V]_(sp, m)) (P : {pred I}) i :
  submxcol (\sum_(j | P j) C_ j) i = \sum_(j | P j) submxcol (C_ j) i.
admit.
Defined.

End BlockColZmod.

Section BlockColRing.
Context {R : ringType} {n : nat} {p_ : 'I_n -> nat}.
Notation sp := (\sum_i p_ i)%N.
Implicit Type (s : 'I_sp).

Lemma mxcol_mul n' m (C_ : forall i, 'M[R]_(p_ i, n')) (A : 'M[R]_(n', m)) :
  \mxcol_i C_ i *m A = \mxcol_i (C_ i *m A).
admit.
Defined.

Lemma submxcol_mul n' m (B : 'M[R]_(sp, n')) (A : 'M[R]_(n', m)) i :
  submxcol B i *m A = submxcol (B *m A) i.
admit.
Defined.

End BlockColRing.

Section BlockMatrixZmod.
Context {V : zmodType} {m n : nat}.
Context {p_ : 'I_m -> nat} {q_ : 'I_n -> nat}.
Notation sp := (\sum_i p_ i)%N.
Notation sq := (\sum_i q_ i)%N.

Lemma mxblockD (B_ B'_ : forall i j, 'M[V]_(p_ i, q_ j)) :
  \mxblock_(i, j) (B_ i j + B'_ i j) =
  \mxblock_(i, j) (B_ i j) + \mxblock_(i, j) (B'_ i j).
admit.
Defined.

Lemma mxblockN (B_ : forall i j, 'M[V]_(p_ i, q_ j)) :
  \mxblock_(i, j) (- B_ i j) = - \mxblock_(i, j) (B_ i j).
admit.
Defined.

Lemma mxblockB (B_ B'_ : forall i j, 'M[V]_(p_ i, q_ j)) :
  \mxblock_(i, j) (B_ i j - B'_ i j) =
  \mxblock_(i, j) (B_ i j) - \mxblock_(i, j) (B'_ i j).
admit.
Defined.

Lemma mxblock0 : \mxblock_(i, j) (0 : 'M[V]_(p_ i, q_ j)) = 0.
admit.
Defined.

Lemma mxblock_const a :
  \mxblock_(i, j) (const_mx a : 'M[V]_(p_ i, q_ j)) = const_mx a.
admit.
Defined.

Lemma mxblock_sum (I : finType)
    (B_ : forall k i j, 'M[V]_(p_ i, q_ j)) (P : {pred I}):
  \mxblock_(i, j) (\sum_(k | P k) B_ k i j) =
  \sum_(k | P k) \mxblock_(i, j) (B_ k i j).
admit.
Defined.

Lemma submxblockD (B B' : 'M[V]_(sp, sq)) i j :
 submxblock (B + B') i j = submxblock B i j + submxblock B' i j.
admit.
Defined.

Lemma submxblockN (B : 'M[V]_(sp, sq)) i j :
 submxblock (- B) i j = - submxblock B i j.
admit.
Defined.

Lemma submxblockB (B B' : 'M[V]_(sp, sq)) i j :
 submxblock (B - B') i j = submxblock B i j - submxblock B' i j.
admit.
Defined.

Lemma submxblock0 i j : submxblock (0 : 'M[V]_(sp, sq)) i j = 0.
admit.
Defined.

Lemma submxblock_sum (I : finType)
   (B_ : forall k, 'M[V]_(sp, sq)) (P : {pred I}) i j :
  submxblock (\sum_(k | P k) B_ k) i j = \sum_(k | P k) submxblock (B_ k) i j.
admit.
Defined.

End BlockMatrixZmod.

Section BlockMatrixRing.
Context {R : ringType} {p q : nat} {p_ : 'I_p -> nat} {q_ : 'I_q -> nat}.
Notation sp := (\sum_i p_ i)%N.
Notation sq := (\sum_i q_ i)%N.

Lemma mul_mxrow_mxcol m n
    (R_ : forall j, 'M[R]_(m, p_ j)) (C_ : forall i, 'M[R]_(p_ i, n)) :
  \mxrow_j R_ j *m \mxcol_i C_ i = \sum_i (R_ i *m C_ i).
admit.
Defined.

Lemma mul_mxcol_mxrow m
    (C_ : forall i, 'M[R]_(p_ i, m)) (R_ : forall j, 'M[R]_(m, q_ j)) :
  \mxcol_i C_ i*m \mxrow_j R_ j  = \mxblock_(i, j) (C_ i *m R_ j).
admit.
Defined.

Lemma mul_mxrow_mxblock m
    (R_ : forall i, 'M[R]_(m, p_ i)) (B_ : forall i j, 'M[R]_(p_ i, q_ j)) :
  \mxrow_i R_ i *m \mxblock_(i, j) B_ i j = \mxrow_j (\sum_i (R_ i *m B_ i j)).
admit.
Defined.

Lemma mul_mxblock_mxrow m
    (B_ : forall i j, 'M[R]_(q_ i, p_ j)) (C_ : forall i, 'M[R]_(p_ i, m)) :
  \mxblock_(i, j) B_ i j *m \mxcol_j C_ j = \mxcol_i (\sum_j (B_ i j *m C_ j)).
admit.
Defined.

End BlockMatrixRing.

Lemma mul_mxblock {R : ringType} {p q r : nat}
    {p_ : 'I_p -> nat} {q_ : 'I_q -> nat} {r_ : 'I_r -> nat}
    (A_ : forall i j, 'M[R]_(p_ i, q_ j)) (B_ : forall j k, 'M_(q_ j, r_ k)) :
  \mxblock_(i, j) A_ i j *m \mxblock_(j, k) B_ j k =
  \mxblock_(i, k) \sum_j (A_ i j *m B_ j k).
admit.
Defined.

Section SquareBlockMatrixZmod.
Import Order.TTheory.
Import tagnat.
Context {V : zmodType} {p : nat} {p_ : 'I_p -> nat}.
Notation sp := (\sum_i p_ i)%N.
Implicit Type (s : 'I_sp).

Lemma is_trig_mxblockP (B_ : forall i j, 'M[V]_(p_ i, p_ j)) :
  reflect [/\ forall (i j : 'I_p), (i < j)%N -> B_ i j = 0 &
              forall i, is_trig_mx (B_ i i)]
          (is_trig_mx (\mxblock_(i, j) B_ i j)).
admit.
Defined.

Lemma is_trig_mxblock (B_ : forall i j, 'M[V]_(p_ i, p_ j)) :
  is_trig_mx (\mxblock_(i, j) B_ i j) =
  ([forall i : 'I_p, forall j : 'I_p, (i < j)%N ==> (B_ i j == 0)] &&
   [forall i, is_trig_mx (B_ i i)]).
admit.
Defined.

Lemma is_diag_mxblockP (B_ : forall i j, 'M[V]_(p_ i, p_ j)) :
  reflect [/\ forall (i j : 'I_p), i != j -> B_ i j = 0 &
              forall i, is_diag_mx (B_ i i)]
          (is_diag_mx (\mxblock_(i, j) B_ i j)).
admit.
Defined.

Lemma is_diag_mxblock (B_ : forall i j, 'M[V]_(p_ i, p_ j)) :
  is_diag_mx (\mxblock_(i, j) B_ i j) =
  ([forall i : 'I_p, forall j : 'I_p, (i != j) ==> (B_ i j == 0)] &&
   [forall i, is_diag_mx (B_ i i)]).
admit.
Defined.

Definition mxdiag (B_ : forall i, 'M[V]_(p_ i)) : 'M[V]_(\sum_i p_ i) :=
  \mxblock_(j, k) if j == k then conform_mx 0 (B_ j) else 0.
Local Notation "\mxdiag_ i E" := (mxdiag (fun i => E)) : ring_scope.

Lemma submxblock_diag (B_  : forall i, 'M[V]_(p_ i)) i :
  submxblock (\mxdiag_i B_ i) i i = B_ i.
admit.
Defined.

Lemma eq_mxdiagP (B_ B'_ : forall i, 'M[V]_(p_ i)) :
  (forall i, B_ i = B'_ i) <-> (\mxdiag_i B_ i = \mxdiag_i B'_ i).
admit.
Defined.

Lemma eq_mxdiag (B_ B'_ : forall i, 'M[V]_(p_ i)) :
  (forall i, B_ i = B'_ i) -> (\mxdiag_i B_ i = \mxdiag_i B'_ i).
admit.
Defined.

Lemma mxdiagD (B_ B'_ : forall i, 'M[V]_(p_ i)) :
  \mxdiag_i (B_ i + B'_ i) = \mxdiag_i (B_ i) + \mxdiag_i (B'_ i).
admit.
Defined.

Lemma mxdiagN (B_ : forall i, 'M[V]_(p_ i)) :
  \mxdiag_i (- B_ i) = - \mxdiag_i (B_ i).
admit.
Defined.

Lemma mxdiagB (B_ B'_ : forall i, 'M[V]_(p_ i)) :
  \mxdiag_i (B_ i - B'_ i) = \mxdiag_i (B_ i) - \mxdiag_i (B'_ i).
admit.
Defined.

Lemma mxdiag0 : \mxdiag_i (0 : 'M[V]_(p_ i)) = 0.
admit.
Defined.

Lemma mxdiag_sum (I : finType) (B_ : forall k i, 'M[V]_(p_ i)) (P : {pred I}) :
  \mxdiag_i (\sum_(k | P k) B_ k i) = \sum_(k | P k) \mxdiag_i (B_ k i).
admit.
Defined.

Lemma tr_mxdiag (B_ : forall i, 'M[V]_(p_ i)) :
  (\mxdiag_i B_ i)^T = \mxdiag_i (B_ i)^T.
admit.
Defined.

Lemma row_mxdiag (B_ : forall i, 'M[V]_(p_ i)) k :
  let B'_ i := if sig1 k == i then conform_mx 0 (B_ i) else 0 in
  row k (\mxdiag_ i B_ i) = row (sig2 k) (\mxrow_i B'_ i).
admit.
Defined.

Lemma col_mxdiag (B_ : forall i, 'M[V]_(p_ i)) k :
  let B'_ i := if sig1 k == i then conform_mx 0 (B_ i) else 0 in
  col k (\mxdiag_ i B_ i) = col (sig2 k) (\mxcol_i B'_ i).
admit.
Defined.

End SquareBlockMatrixZmod.

Notation "\mxdiag_ ( i < n ) E" := (mxdiag (fun i : 'I_n => E))
  (only parsing) : ring_scope.
Notation "\mxdiag_ i E" := (\mxdiag_(i < _) E) : ring_scope.

Lemma mxdiag_recl {V : zmodType} {m : nat} {p_ : 'I_m.+1 -> nat}
    (B_ : forall i, 'M[V]_(p_ i)) :
  \mxdiag_i B_ i = castmx (mxsize_recl, mxsize_recl)
    (block_mx (B_ 0) 0 0 (\mxdiag_i B_ (lift ord0 i))).
admit.
Defined.

Section SquareBlockMatrixRing.
Import tagnat.
Context {R : ringType} {p : nat} {p_ : 'I_p -> nat}.
Notation sp := (\sum_i p_ i)%N.
Implicit Type (s : 'I_sp).

Lemma mxtrace_mxblock (B_ : forall i j, 'M[R]_(p_ i, p_ j)) :
  \tr (\mxblock_(i, j) B_ i j) = \sum_i \tr (B_ i i).
admit.
Defined.

Lemma mxdiagZ a : \mxdiag_i (a%:M : 'M[R]_(p_ i)) = a%:M.
admit.
Defined.

Lemma diag_mxrow (B_ : forall j, 'rV[R]_(p_ j)) :
  diag_mx (\mxrow_j B_ j) = \mxdiag_j (diag_mx (B_ j)).
admit.
Defined.

Lemma mxtrace_mxdiag (B_ : forall i, 'M[R]_(p_ i)) :
  \tr (\mxdiag_i B_ i) = \sum_i \tr (B_ i).
admit.
Defined.

Lemma mul_mxdiag_mxcol m
    (D_ : forall i, 'M[R]_(p_ i)) (C_ : forall i, 'M[R]_(p_ i, m)):
  \mxdiag_i D_ i *m \mxcol_i C_ i = \mxcol_i (D_ i *m C_ i).
admit.
Defined.

End SquareBlockMatrixRing.

Lemma mul_mxrow_mxdiag {R : ringType} {p : nat} {p_ : 'I_p -> nat} m
    (R_ : forall i, 'M[R]_(m, p_ i)) (D_ : forall i, 'M[R]_(p_ i)) :
  \mxrow_i R_ i *m \mxdiag_i D_ i = \mxrow_i (R_ i *m D_ i).
admit.
Defined.

Lemma mul_mxblock_mxdiag {R : ringType} {p q : nat}
  {p_ : 'I_p -> nat} {q_ : 'I_q -> nat}
    (B_ : forall i j, 'M[R]_(p_ i, q_ j)) (D_ : forall j, 'M[R]_(q_ j)) :
  \mxblock_(i, j) B_ i j *m \mxdiag_j D_ j = \mxblock_(i, j) (B_ i j *m D_ j).
admit.
Defined.

Lemma mul_mxdiag_mxblock {R : ringType} {p q : nat}
  {p_ : 'I_p -> nat} {q_ : 'I_q -> nat}
    (D_ : forall j, 'M[R]_(p_ j)) (B_ : forall i j, 'M[R]_(p_ i, q_ j)):
  \mxdiag_j D_ j *m \mxblock_(i, j) B_ i j = \mxblock_(i, j) (D_ i *m B_ i j).
admit.
Defined.

End matrix.

End mathcomp_DOT_algebra_DOT_matrix_WRAPPED.
Module Export mathcomp_DOT_algebra_DOT_matrix.
Module Export mathcomp.
Import mathcomp.ssreflect.ssreflect.
Import mathcomp.ssreflect.ssrbool.
Import mathcomp.ssreflect.ssrfun.
Import mathcomp.ssreflect.eqtype.
Import mathcomp.ssreflect.ssrnat.
Import mathcomp.ssreflect.fintype.
Import mathcomp.algebra.ssralg.
Import mathcomp.algebra.zmodp.

Set Implicit Arguments.
Unset Strict Implicit.

Declare Scope matrix_set_scope.
Local Open Scope ring_scope.

Reserved Notation "\rank A" (at level 10, A at level 8, format "\rank  A").

Delimit Scope matrix_set_scope with MS.

Section RowSpaceTheory.

Variable F : fieldType.

Local Notation "''M_' ( m , n )" := 'M[F]_(m, n) : type_scope.

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
Definition cokermx : 'M_n := invmx row_ebase *m copid_mx mxrank.

Definition pinvmx : 'M_(n, m) :=
  invmx row_ebase *m pid_mx mxrank *m invmx col_ebase.

End Defs.
Local Notation "\rank A" := (mxrank A) : nat_scope.

Definition submx_def := idfun (fun m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)) =>
  A *m cokermx B == 0).
Fact submx_key : unit.
admit.
Defined.
Definition submx := locked_with submx_key submx_def.

Lemma mxrank_eq0 m n (A : 'M_(m, n)) : (\rank A == 0%N) = (A == 0).
admit.
Defined.

End RowSpaceTheory.
Notation "\rank A" := (mxrank A) : nat_scope.
Notation "A <= B" := (submx A B) : matrix_set_scope.
Import mathcomp.ssreflect.seq.
Import mathcomp.ssreflect.choice.

Import GRing.Theory.
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

Section Definitions.

Variables (aR rR : ringType) (f : aR -> rR).

Definition map_poly (p : {poly aR}) := \poly_(i < size p) f p`_i.

Definition commr_rmorph u := forall x, GRing.comm u (f x).

Definition horner_morph u of commr_rmorph u := fun p => (map_poly p).[u].

End Definitions.

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
Import mathcomp.ssreflect.tuple.
Import mathcomp.ssreflect.finfun.
Import mathcomp.ssreflect.bigop.

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
Import mathcomp.ssreflect.finset.
Import mathcomp.fingroup.fingroup.
Unset Printing Implicit Defensive.

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
