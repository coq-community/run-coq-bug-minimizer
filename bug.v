
(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "-projection-no-head-constant" "-w" "-redundant-canonical-projection" "-w" "-notation-overridden" "-w" "-deprecated-native-compiler-option" "-native-compiler" "ondemand" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/oddorder/theories" "odd_order" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/HB" "HB" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/elpi" "elpi" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/mathcomp" "mathcomp" "-top" "Top.bug_01") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 1375 lines to 60 lines, then from 73 lines to 1675 lines, then from 1680 lines to 90 lines, then from 103 lines to 2712 lines, then from 2715 lines to 148 lines, then from 161 lines to 2932 lines, then from 2936 lines to 147 lines, then from 160 lines to 1746 lines, then from 1749 lines to 189 lines, then from 202 lines to 1254 lines, then from 1259 lines to 145 lines, then from 158 lines to 976 lines, then from 981 lines to 153 lines, then from 166 lines to 775 lines, then from 779 lines to 245 lines, then from 239 lines to 175 lines, then from 188 lines to 604 lines, then from 609 lines to 168 lines, then from 181 lines to 1580 lines, then from 1585 lines to 231 lines, then from 244 lines to 1254 lines, then from 1259 lines to 261 lines, then from 274 lines to 1855 lines, then from 1859 lines to 261 lines, then from 274 lines to 3310 lines, then from 3315 lines to 2052 lines, then from 1806 lines to 484 lines, then from 497 lines to 2159 lines, then from 2164 lines to 571 lines, then from 584 lines to 3152 lines, then from 3155 lines to 2910 lines, then from 2767 lines to 646 lines, then from 659 lines to 3393 lines, then from 3398 lines to 3162 lines, then from 3016 lines to 743 lines, then from 756 lines to 1264 lines, then from 1269 lines to 933 lines *)
(* coqc version 8.19+alpha compiled with OCaml 4.14.1
   coqtop version 728713d43dde:/builds/coq/coq/_build/default,(HEAD detached at 25e3b11) (25e3b11cee094cfce7e16d10e58d3b7b318ea70c)
   Expected coqc runtime on this file: 4.171 sec *)
Require mathcomp.ssreflect.tuple.

Module Export AdmitTactic.
Module Import LocalFalse.
End LocalFalse.
Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.
End AdmitTactic.

Module mathcomp_DOT_ssreflect_DOT_finfun_WRAPPED.
Module Export finfun.
 
 
Import HB.structures.
Import mathcomp.ssreflect.ssreflect.
Import mathcomp.ssreflect.ssrfun.
Import mathcomp.ssreflect.ssrbool.
Import mathcomp.ssreflect.eqtype.
Import mathcomp.ssreflect.seq.
Import mathcomp.ssreflect.choice.
Import mathcomp.ssreflect.fintype.
Import mathcomp.ssreflect.tuple.

 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 

Set Implicit Arguments.
Unset Strict Implicit.

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

Notation "[ 'ffun' x => E ]" := (@finfun _ (fun=> _) (fun x => E))
  (at level 0, x name, format "[ 'ffun'  x  =>  E ]") : fun_scope.

 

 
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

Section FinFunTuple.

End FinFunTuple.

Section FunPlainTheory.

End FunPlainTheory.

 

Section Support.

End Support.

Section EqTheory.

End EqTheory.

 

Section FinDepTheory.

End FinDepTheory.

Section FinFunTheory.

End FinFunTheory.

End finfun.

End mathcomp_DOT_ssreflect_DOT_finfun_WRAPPED.
Module Export mathcomp.
Module Export ssreflect.
Module finfun.
Include mathcomp_DOT_ssreflect_DOT_finfun_WRAPPED.finfun.
End finfun.

Import HB.structures.
Import mathcomp.ssreflect.ssreflect.
Import mathcomp.ssreflect.ssrbool.
Import mathcomp.ssreflect.ssrfun.
Import mathcomp.ssreflect.seq.
Import mathcomp.ssreflect.fintype.

Set Implicit Arguments.

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

Import mathcomp.ssreflect.eqtype.
Import mathcomp.ssreflect.choice.
Import mathcomp.ssreflect.finfun.
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
