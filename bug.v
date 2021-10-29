(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "-projection-no-head-constant" "-w" "-redundant-canonical-projection" "-w" "-notation-overridden" "-w" "+duplicate-clear" "-w" "-ambiguous-paths" "-w" "+non-primitive-record" "-w" "+undeclared-scope" "-w" "-deprecated-hint-without-locality" "-w" "-deprecated-ident-entry" "-w" "-deprecated-native-compiler-option" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/mathcomp/mathcomp" "mathcomp" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-I" "/github/workspace/builds/coq/coq-failing/_build_ci/mathcomp/mathcomp" "-top" "bug_01" "-native-compiler" "ondemand") -*- *)
(* File reduced by coq-bug-finder from original input, then from 5976 lines to 4694 lines, then from 4339 lines to 258 lines, then from 312 lines to 2285 lines, then from 2290 lines to 373 lines, then from 425 lines to 3660 lines, then from 3664 lines to 414 lines, then from 465 lines to 3264 lines, then from 3269 lines to 611 lines, then from 662 lines to 3802 lines, then from 3807 lines to 3169 lines, then from 2904 lines to 646 lines, then from 696 lines to 5297 lines, then from 5302 lines to 4579 lines, then from 4274 lines to 1107 lines, then from 1155 lines to 1545 lines, then from 1550 lines to 1142 lines, then from 1181 lines to 1929 lines, then from 1934 lines to 1273 lines, then from 1310 lines to 4393 lines, then from 4398 lines to 2101 lines, then from 1910 lines to 1439 lines, then from 1476 lines to 8115 lines, then from 8120 lines to 6470 lines, then from 5813 lines to 2147 lines, then from 2181 lines to 4718 lines, then from 4722 lines to 2489 lines, then from 2410 lines to 2250 lines, then from 2283 lines to 4355 lines, then from 4360 lines to 2344 lines, then from 2375 lines to 2874 lines, then from 2879 lines to 2461 lines, then from 2491 lines to 3201 lines, then from 3206 lines to 2586 lines, then from 2615 lines to 4985 lines, then from 4990 lines to 5296 lines, then from 5095 lines to 3003 lines, then from 3030 lines to 3747 lines, then from 3752 lines to 3223 lines, then from 3250 lines to 4313 lines, then from 4318 lines to 4257 lines *)
(* coqc version 8.15+alpha compiled with OCaml 4.13.0
   coqtop version runner-z3wu8uu--project-6138686-concurrent-0:/builds/coq/coq/_build/default,(HEAD detached at 0d1a2eb) (0d1a2eb7ba6a7719f37495807fb9fa49623ac075)
   Expected coqc runtime on this file: 1.956 sec *)
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
Module Export mathcomp_DOT_ssreflect_DOT_div_WRAPPED.
Module Export div.
Import mathcomp.ssreflect.ssreflect.
Import mathcomp.ssreflect.ssrfun.
Import mathcomp.ssreflect.ssrbool.
Import mathcomp.ssreflect.eqtype.
Import mathcomp.ssreflect.ssrnat.
Import mathcomp.ssreflect.seq.

 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

 

Definition edivn_rec d :=
  fix loop m q := if m - d is m'.+1 then loop m' q.+1 else (q, m).

Definition edivn m d := if d > 0 then edivn_rec d.-1 m 0 else (0, m).

Variant edivn_spec m d : nat * nat -> Type :=
  EdivnSpec q r of m = q * d + r & (d > 0) ==> (r < d) : edivn_spec m d (q, r).

Lemma edivnP m d : edivn_spec m d (edivn m d).
admit.
Defined.

Lemma edivn_eq d q r : r < d -> edivn (q * d + r) d = (q, r).
admit.
Defined.

Definition divn m d := (edivn m d).1.

Notation "m %/ d" := (divn m d) : nat_scope.

 

Definition modn_rec d := fix loop m := if m - d is m'.+1 then loop m' else m.

Definition modn m d := if d > 0 then modn_rec d.-1 m else m.

Notation "m %% d" := (modn m d) : nat_scope.
Notation "m = n %[mod d ]" := (m %% d = n %% d) : nat_scope.
Notation "m == n %[mod d ]" := (m %% d == n %% d) : nat_scope.
Notation "m <> n %[mod d ]" := (m %% d <> n %% d) : nat_scope.
Notation "m != n %[mod d ]" := (m %% d != n %% d) : nat_scope.

Lemma modn_def m d : m %% d = (edivn m d).2.
admit.
Defined.

Lemma edivn_def m d : edivn m d = (m %/ d, m %% d).
admit.
Defined.

Lemma divn_eq m d : m = m %/ d * d + m %% d.
admit.
Defined.

Lemma div0n d : 0 %/ d = 0.
admit.
Defined.
Lemma divn0 m : m %/ 0 = 0.
admit.
Defined.
Lemma mod0n d : 0 %% d = 0.
admit.
Defined.
Lemma modn0 m : m %% 0 = m.
admit.
Defined.

Lemma divn_small m d : m < d -> m %/ d = 0.
admit.
Defined.

Lemma divnMDl q m d : 0 < d -> (q * d + m) %/ d = q + m %/ d.
admit.
Defined.

Lemma mulnK m d : 0 < d -> m * d %/ d = m.
admit.
Defined.

Lemma mulKn m d : 0 < d -> d * m %/ d = m.
admit.
Defined.

Lemma expnB p m n : p > 0 -> m >= n -> p ^ (m - n) = p ^ m %/ p ^ n.
admit.
Defined.

Lemma modn1 m : m %% 1 = 0.
admit.
Defined.

Lemma divn1 m : m %/ 1 = m.
admit.
Defined.

Lemma divnn d : d %/ d = (0 < d).
admit.
Defined.

Lemma divnMl p m d : p > 0 -> p * m %/ (p * d) = m %/ d.
admit.
Defined.
Arguments divnMl [p m d].

Lemma divnMr p m d : p > 0 -> m * p %/ (d * p) = m %/ d.
admit.
Defined.
Arguments divnMr [p m d].

Lemma ltn_mod m d : (m %% d < d) = (0 < d).
admit.
Defined.

Lemma ltn_pmod m d : 0 < d -> m %% d < d.
admit.
Defined.

Lemma leq_trunc_div m d : m %/ d * d <= m.
admit.
Defined.

Lemma leq_mod m d : m %% d  <= m.
admit.
Defined.

Lemma leq_div m d : m %/ d <= m.
admit.
Defined.

Lemma ltn_ceil m d : 0 < d -> m < (m %/ d).+1 * d.
admit.
Defined.

Lemma ltn_divLR m n d : d > 0 -> (m %/ d < n) = (m < n * d).
admit.
Defined.

Lemma leq_divRL m n d : d > 0 -> (m <= n %/ d) = (m * d <= n).
admit.
Defined.

Lemma ltn_Pdiv m d : 1 < d -> 0 < m -> m %/ d < m.
admit.
Defined.

Lemma divn_gt0 d m : 0 < d -> (0 < m %/ d) = (d <= m).
admit.
Defined.

Lemma leq_div2r d m n : m <= n -> m %/ d <= n %/ d.
admit.
Defined.

Lemma leq_div2l m d e : 0 < d -> d <= e -> m %/ e <= m %/ d.
admit.
Defined.

Lemma edivnD m n d (offset := m %% d + n %% d >= d) : 0 < d ->
   edivn (m + n) d = (m %/ d + n %/ d + offset, m %% d + n %% d - offset * d).
admit.
Defined.

Lemma divnD m n d : 0 < d ->
  (m + n) %/ d = (m %/ d) + (n %/ d) + (m %% d + n %% d >= d).
admit.
Defined.

Lemma modnD m n d : 0 < d ->
  (m + n) %% d = m %% d + n %% d - (m %% d + n %% d >= d) * d.
admit.
Defined.

Lemma leqDmod m n d : 0 < d ->
  (d <= m %% d + n %% d) = ((m + n) %% d < n %% d).
admit.
Defined.

Lemma divnB n m d : 0 < d ->
  (m - n) %/ d = (m %/ d) - (n %/ d) - (m %% d < n %% d).
admit.
Defined.

Lemma modnB m n d : 0 < d -> n <= m ->
  (m - n) %% d = (m %% d < n %% d) * d + m %% d - n %% d.
admit.
Defined.

Lemma edivnB m n d (offset := m %% d < n %% d) : 0 < d -> n <= m ->
   edivn (m - n) d = (m %/ d - n %/ d - offset, offset * d + m %% d - n %% d).
admit.
Defined.

Lemma leq_divDl p m n : (m + n) %/ p <= m %/ p + n %/ p + 1.
admit.
Defined.

Lemma geq_divBl k m p : k %/ p - m %/ p <= (k - m) %/ p + 1.
admit.
Defined.

Lemma divnMA m n p : m %/ (n * p) = m %/ n %/ p.
admit.
Defined.

Lemma divnAC m n p : m %/ n %/ p =  m %/ p %/ n.
admit.
Defined.

Lemma modn_small m d : m < d -> m %% d = m.
admit.
Defined.

Lemma modn_mod m d : m %% d = m %[mod d].
admit.
Defined.

Lemma modnMDl p m d : p * d + m = m %[mod d].
admit.
Defined.

Lemma muln_modr p m d : p * (m %% d) = (p * m) %% (p * d).
admit.
Defined.

Lemma muln_modl p m d : (m %% d) * p = (m * p) %% (d * p).
admit.
Defined.

Lemma modn_divl m n d : (m %/ d) %% n = m %% (n * d) %/ d.
admit.
Defined.

Lemma modnDl m d : d + m = m %[mod d].
admit.
Defined.

Lemma modnDr m d : m + d = m %[mod d].
admit.
Defined.

Lemma modnn d : d %% d = 0.
admit.
Defined.

Lemma modnMl p d : p * d %% d = 0.
admit.
Defined.

Lemma modnMr p d : d * p %% d = 0.
admit.
Defined.

Lemma modnDml m n d : m %% d + n = m + n %[mod d].
admit.
Defined.

Lemma modnDmr m n d : m + n %% d = m + n %[mod d].
admit.
Defined.

Lemma modnDm m n d : m %% d + n %% d = m + n %[mod d].
admit.
Defined.

Lemma eqn_modDl p m n d : (p + m == p + n %[mod d]) = (m == n %[mod d]).
admit.
Defined.

Lemma eqn_modDr p m n d : (m + p == n + p %[mod d]) = (m == n %[mod d]).
admit.
Defined.

Lemma modnMml m n d : m %% d * n = m * n %[mod d].
admit.
Defined.

Lemma modnMmr m n d : m * (n %% d) = m * n %[mod d].
admit.
Defined.

Lemma modnMm m n d : m %% d * (n %% d) = m * n %[mod d].
admit.
Defined.

Lemma modn2 m : m %% 2 = odd m.
admit.
Defined.

Lemma divn2 m : m %/ 2 = m./2.
admit.
Defined.

Lemma odd_mod m d : odd d = false -> odd (m %% d) = odd m.
admit.
Defined.

Lemma modnXm m n a : (a %% n) ^ m = a ^ m %[mod n].
admit.
Defined.

 

Definition dvdn d m := m %% d == 0.

Notation "m %| d" := (dvdn m d) : nat_scope.

Lemma dvdnP d m : reflect (exists k, m = k * d) (d %| m).
admit.
Defined.
Arguments dvdnP {d m}.

Lemma dvdn0 d : d %| 0.
admit.
Defined.

Lemma dvd0n n : (0 %| n) = (n == 0).
admit.
Defined.

Lemma dvdn1 d : (d %| 1) = (d == 1).
admit.
Defined.

Lemma dvd1n m : 1 %| m.
admit.
Defined.

Lemma dvdn_gt0 d m : m > 0 -> d %| m -> d > 0.
admit.
Defined.

Lemma dvdnn m : m %| m.
admit.
Defined.

Lemma dvdn_mull d m n : d %| n -> d %| m * n.
admit.
Defined.

Lemma dvdn_mulr d m n : d %| m -> d %| m * n.
admit.
Defined.
Hint Resolve dvdn0 dvd1n dvdnn dvdn_mull dvdn_mulr : core.

Lemma dvdn_mul d1 d2 m1 m2 : d1 %| m1 -> d2 %| m2 -> d1 * d2 %| m1 * m2.
admit.
Defined.

Lemma dvdn_trans n d m : d %| n -> n %| m -> d %| m.
admit.
Defined.

Lemma dvdn_eq d m : (d %| m) = (m %/ d * d == m).
admit.
Defined.

Lemma dvdn2 n : (2 %| n) = ~~ odd n.
admit.
Defined.

Lemma dvdn_odd m n : m %| n -> odd n -> odd m.
admit.
Defined.

Lemma divnK d m : d %| m -> m %/ d * d = m.
admit.
Defined.

Lemma leq_divLR d m n : d %| m -> (m %/ d <= n) = (m <= n * d).
admit.
Defined.

Lemma ltn_divRL d m n : d %| m -> (n < m %/ d) = (n * d < m).
admit.
Defined.

Lemma eqn_div d m n : d > 0 -> d %| m -> (n == m %/ d) = (n * d == m).
admit.
Defined.

Lemma eqn_mul d m n : d > 0 -> d %| m -> (m == n * d) = (m %/ d == n).
admit.
Defined.

Lemma divn_mulAC d m n : d %| m -> m %/ d * n = m * n %/ d.
admit.
Defined.

Lemma muln_divA d m n : d %| n -> m * (n %/ d) = m * n %/ d.
admit.
Defined.

Lemma muln_divCA d m n : d %| m -> d %| n -> m * (n %/ d) = n * (m %/ d).
admit.
Defined.

Lemma divnA m n p : p %| n -> m %/ (n %/ p) = m * p %/ n.
admit.
Defined.

Lemma modn_dvdm m n d : d %| m -> n %% m = n %[mod d].
admit.
Defined.

Lemma dvdn_leq d m : 0 < m -> d %| m -> d <= m.
admit.
Defined.

Lemma gtnNdvd n d : 0 < n -> n < d -> (d %| n) = false.
admit.
Defined.

Lemma eqn_dvd m n : (m == n) = (m %| n) && (n %| m).
admit.
Defined.

Lemma dvdn_pmul2l p d m : 0 < p -> (p * d %| p * m) = (d %| m).
admit.
Defined.
Arguments dvdn_pmul2l [p d m].

Lemma dvdn_pmul2r p d m : 0 < p -> (d * p %| m * p) = (d %| m).
admit.
Defined.
Arguments dvdn_pmul2r [p d m].

Lemma dvdn_divLR p d m : 0 < p -> p %| d -> (d %/ p %| m) = (d %| m * p).
admit.
Defined.

Lemma dvdn_divRL p d m : p %| m -> (d %| m %/ p) = (d * p %| m).
admit.
Defined.

Lemma dvdn_div d m : d %| m -> m %/ d %| m.
admit.
Defined.

Lemma dvdn_exp2l p m n : m <= n -> p ^ m %| p ^ n.
admit.
Defined.

Lemma dvdn_Pexp2l p m n : p > 1 -> (p ^ m %| p ^ n) = (m <= n).
admit.
Defined.

Lemma dvdn_exp2r m n k : m %| n -> m ^ k %| n ^ k.
admit.
Defined.

Lemma divn_modl m n d : d %| n -> (m %% n) %/ d = (m %/ d) %% (n %/ d).
admit.
Defined.

Lemma dvdn_addr m d n : d %| m -> (d %| m + n) = (d %| n).
admit.
Defined.

Lemma dvdn_addl n d m : d %| n -> (d %| m + n) = (d %| m).
admit.
Defined.

Lemma dvdn_add d m n : d %| m -> d %| n -> d %| m + n.
admit.
Defined.

Lemma dvdn_add_eq d m n : d %| m + n -> (d %| m) = (d %| n).
admit.
Defined.

Lemma dvdn_subr d m n : n <= m -> d %| m -> (d %| m - n) = (d %| n).
admit.
Defined.

Lemma dvdn_subl d m n : n <= m -> d %| n -> (d %| m - n) = (d %| m).
admit.
Defined.

Lemma dvdn_sub d m n : d %| m -> d %| n -> d %| m - n.
admit.
Defined.

Lemma dvdn_exp k d m : 0 < k -> d %| m -> d %| (m ^ k).
admit.
Defined.

Lemma dvdn_fact m n : 0 < m <= n -> m %| n`!.
admit.
Defined.

Hint Resolve dvdn_add dvdn_sub dvdn_exp : core.

Lemma eqn_mod_dvd d m n : n <= m -> (m == n %[mod d]) = (d %| m - n).
admit.
Defined.

Lemma divnDMl q m d : 0 < d -> (m + q * d) %/ d = (m %/ d) + q.
admit.
Defined.

Lemma divnMBl q m d : 0 < d -> (q * d - m) %/ d = q - (m %/ d) - (~~ (d %| m)).
admit.
Defined.

Lemma divnBMl q m d : (m - q * d) %/ d = (m %/ d) - q.
admit.
Defined.

Lemma divnDl m n d : d %| m -> (m + n) %/ d = m %/ d + n %/ d.
admit.
Defined.

Lemma divnDr m n d : d %| n -> (m + n) %/ d = m %/ d + n %/ d.
admit.
Defined.

Lemma divnBl m n d : d %| m -> (m - n) %/ d = m %/ d - (n %/ d) - (~~ (d %| n)).
admit.
Defined.

Lemma divnBr m n d : d %| n -> (m - n) %/ d = m %/ d - n %/ d.
admit.
Defined.

Lemma edivnS m d : 0 < d -> edivn m.+1 d =
  if d %| m.+1 then ((m %/ d).+1, 0) else (m %/ d, (m %% d).+1).
admit.
Defined.

Lemma modnS m d : m.+1 %% d = if d %| m.+1 then 0 else (m %% d).+1.
admit.
Defined.

Lemma divnS m d : 0 < d -> m.+1 %/ d = (d %| m.+1) + m %/ d.
admit.
Defined.

Lemma divn_pred m d : m.-1 %/ d = (m %/ d) - (d %| m).
admit.
Defined.

Lemma modn_pred m d : d != 1 -> 0 < m ->
  m.-1 %% d = if d %| m then d.-1 else (m %% d).-1.
admit.
Defined.

Lemma edivn_pred m d : d != 1 -> 0 < m ->
  edivn m.-1 d = if d %| m then ((m %/ d).-1, d.-1) else (m %/ d, (m %% d).-1).
admit.
Defined.

 
 
 

Fixpoint gcdn_rec m n :=
  let n' := n %% m in if n' is 0 then m else
  if m - n'.-1 is m'.+1 then gcdn_rec (m' %% n') n' else n'.

Definition gcdn := nosimpl gcdn_rec.

Lemma gcdnE m n : gcdn m n = if m == 0 then n else gcdn (n %% m) m.
admit.
Defined.

Lemma gcdnn : idempotent gcdn.
admit.
Defined.

Lemma gcdnC : commutative gcdn.
admit.
Defined.

Lemma gcd0n : left_id 0 gcdn.
admit.
Defined.
Lemma gcdn0 : right_id 0 gcdn.
admit.
Defined.

Lemma gcd1n : left_zero 1 gcdn.
admit.
Defined.

Lemma gcdn1 : right_zero 1 gcdn.
admit.
Defined.

Lemma dvdn_gcdr m n : gcdn m n %| n.
admit.
Defined.

Lemma dvdn_gcdl m n : gcdn m n %| m.
admit.
Defined.

Lemma gcdn_gt0 m n : (0 < gcdn m n) = (0 < m) || (0 < n).
admit.
Defined.

Lemma gcdnMDl k m n : gcdn m (k * m + n) = gcdn m n.
admit.
Defined.

Lemma gcdnDl m n : gcdn m (m + n) = gcdn m n.
admit.
Defined.

Lemma gcdnDr m n : gcdn m (n + m) = gcdn m n.
admit.
Defined.

Lemma gcdnMl n m : gcdn n (m * n) = n.
admit.
Defined.

Lemma gcdnMr n m : gcdn n (n * m) = n.
admit.
Defined.

Lemma gcdn_idPl {m n} : reflect (gcdn m n = m) (m %| n).
admit.
Defined.

Lemma gcdn_idPr {m n} : reflect (gcdn m n = n) (n %| m).
admit.
Defined.

Lemma expn_min e m n : e ^ minn m n = gcdn (e ^ m) (e ^ n).
admit.
Defined.

Lemma gcdn_modr m n : gcdn m (n %% m) = gcdn m n.
admit.
Defined.

Lemma gcdn_modl m n : gcdn (m %% n) n = gcdn m n.
admit.
Defined.

 

Fixpoint Bezout_rec km kn qs :=
  if qs is q :: qs' then Bezout_rec kn (NatTrec.add_mul q kn km) qs'
  else (km, kn).

Fixpoint egcdn_rec m n s qs :=
  if s is s'.+1 then
    let: (q, r) := edivn m n in
    if r > 0 then egcdn_rec n r s' (q :: qs) else
    if odd (size qs) then qs else q.-1 :: qs
  else [::0].

Definition egcdn m n := Bezout_rec 0 1 (egcdn_rec m n n [::]).

Variant egcdn_spec m n : nat * nat -> Type :=
  EgcdnSpec km kn of km * m = kn * n + gcdn m n & kn * gcdn m n < m :
    egcdn_spec m n (km, kn).

Lemma egcd0n n : egcdn 0 n = (1, 0).
admit.
Defined.

Lemma egcdnP m n : m > 0 -> egcdn_spec m n (egcdn m n).
admit.
Defined.

Lemma Bezoutl m n : m > 0 -> {a | a < m & m %| gcdn m n + a * n}.
admit.
Defined.

Lemma Bezoutr m n : n > 0 -> {a | a < n & n %| gcdn m n + a * m}.
admit.
Defined.

 

Lemma dvdn_gcd p m n : p %| gcdn m n = (p %| m) && (p %| n).
admit.
Defined.

Lemma gcdnAC : right_commutative gcdn.
admit.
Defined.

Lemma gcdnA : associative gcdn.
admit.
Defined.

Lemma gcdnCA : left_commutative gcdn.
admit.
Defined.

Lemma gcdnACA : interchange gcdn gcdn.
admit.
Defined.

Lemma muln_gcdr : right_distributive muln gcdn.
admit.
Defined.

Lemma muln_gcdl : left_distributive muln gcdn.
admit.
Defined.

Lemma gcdn_def d m n :
    d %| m -> d %| n -> (forall d', d' %| m -> d' %| n -> d' %| d) ->
  gcdn m n = d.
admit.
Defined.

Lemma muln_divCA_gcd n m : n * (m %/ gcdn n m)  = m * (n %/ gcdn n m).
admit.
Defined.

 

Definition lcmn m n := m * n %/ gcdn m n.

Lemma lcmnC : commutative lcmn.
admit.
Defined.

Lemma lcm0n : left_zero 0 lcmn.
admit.
Defined.
Lemma lcmn0 : right_zero 0 lcmn.
admit.
Defined.

Lemma lcm1n : left_id 1 lcmn.
admit.
Defined.

Lemma lcmn1 : right_id 1 lcmn.
admit.
Defined.

Lemma muln_lcm_gcd m n : lcmn m n * gcdn m n = m * n.
admit.
Defined.

Lemma lcmn_gt0 m n : (0 < lcmn m n) = (0 < m) && (0 < n).
admit.
Defined.

Lemma muln_lcmr : right_distributive muln lcmn.
admit.
Defined.

Lemma muln_lcml : left_distributive muln lcmn.
admit.
Defined.

Lemma lcmnA : associative lcmn.
admit.
Defined.

Lemma lcmnCA : left_commutative lcmn.
admit.
Defined.

Lemma lcmnAC : right_commutative lcmn.
admit.
Defined.

Lemma lcmnACA : interchange lcmn lcmn.
admit.
Defined.

Lemma dvdn_lcml d1 d2 : d1 %| lcmn d1 d2.
admit.
Defined.

Lemma dvdn_lcmr d1 d2 : d2 %| lcmn d1 d2.
admit.
Defined.

Lemma dvdn_lcm d1 d2 m : lcmn d1 d2 %| m = (d1 %| m) && (d2 %| m).
admit.
Defined.

Lemma lcmnMl m n : lcmn m (m * n) = m * n.
admit.
Defined.

Lemma lcmnMr m n : lcmn n (m * n) = m * n.
admit.
Defined.

Lemma lcmn_idPr {m n} : reflect (lcmn m n = n) (m %| n).
admit.
Defined.

Lemma lcmn_idPl {m n} : reflect (lcmn m n = m) (n %| m).
admit.
Defined.

Lemma expn_max e m n : e ^ maxn m n = lcmn (e ^ m) (e ^ n).
admit.
Defined.

 

Definition coprime m n := gcdn m n == 1.

Lemma coprime1n n : coprime 1 n.
admit.
Defined.

Lemma coprimen1 n : coprime n 1.
admit.
Defined.

Lemma coprime_sym m n : coprime m n = coprime n m.
admit.
Defined.

Lemma coprime_modl m n : coprime (m %% n) n = coprime m n.
admit.
Defined.

Lemma coprime_modr m n : coprime m (n %% m) = coprime m n.
admit.
Defined.

Lemma coprime2n n : coprime 2 n = odd n.
admit.
Defined.

Lemma coprimen2 n : coprime n 2 = odd n.
admit.
Defined.

Lemma coprimeSn n : coprime n.+1 n.
admit.
Defined.

Lemma coprimenS n : coprime n n.+1.
admit.
Defined.

Lemma coprimePn n : n > 0 -> coprime n.-1 n.
admit.
Defined.

Lemma coprimenP n : n > 0 -> coprime n n.-1.
admit.
Defined.

Lemma coprimeP n m :
  n > 0 -> reflect (exists u, u.1 * n - u.2 * m = 1) (coprime n m).
admit.
Defined.

Lemma modn_coprime k n : 0 < k -> (exists u, (k * u) %% n = 1) -> coprime k n.
admit.
Defined.

Lemma Gauss_dvd m n p : coprime m n -> (m * n %| p) = (m %| p) && (n %| p).
admit.
Defined.

Lemma Gauss_dvdr m n p : coprime m n -> (m %| n * p) = (m %| p).
admit.
Defined.

Lemma Gauss_dvdl m n p : coprime m p -> (m %| n * p) = (m %| n).
admit.
Defined.

Lemma dvdn_double_leq m n : m %| n -> odd m -> ~~ odd n -> 0 < n -> m.*2 <= n.
admit.
Defined.

Lemma dvdn_double_ltn m n : m %| n.-1 -> odd m -> odd n -> 1 < n -> m.*2 < n.
admit.
Defined.

Lemma Gauss_gcdr p m n : coprime p m -> gcdn p (m * n) = gcdn p n.
admit.
Defined.

Lemma Gauss_gcdl p m n : coprime p n -> gcdn p (m * n) = gcdn p m.
admit.
Defined.

Lemma coprimeMr p m n : coprime p (m * n) = coprime p m && coprime p n.
admit.
Defined.

Lemma coprimeMl p m n : coprime (m * n) p = coprime m p && coprime n p.
admit.
Defined.

Lemma coprime_pexpl k m n : 0 < k -> coprime (m ^ k) n = coprime m n.
admit.
Defined.

Lemma coprime_pexpr k m n : 0 < k -> coprime m (n ^ k) = coprime m n.
admit.
Defined.

Lemma coprimeXl k m n : coprime m n -> coprime (m ^ k) n.
admit.
Defined.

Lemma coprimeXr k m n : coprime m n -> coprime m (n ^ k).
admit.
Defined.

Lemma coprime_dvdl m n p : m %| n -> coprime n p -> coprime m p.
admit.
Defined.

Lemma coprime_dvdr m n p : m %| n -> coprime p n -> coprime p m.
admit.
Defined.

Lemma coprime_egcdn n m : n > 0 -> coprime (egcdn n m).1 (egcdn n m).2.
admit.
Defined.

Lemma dvdn_pexp2r m n k : k > 0 -> (m ^ k %| n ^ k) = (m %| n).
admit.
Defined.

Section Chinese.

 
 
 

Variables m1 m2 : nat.
Hypothesis co_m12 : coprime m1 m2.

Lemma chinese_remainder x y :
  (x == y %[mod m1 * m2]) = (x == y %[mod m1]) && (x == y %[mod m2]).
admit.
Defined.

 
 
 

Definition chinese r1 r2 :=
  r1 * m2 * (egcdn m2 m1).1 + r2 * m1 * (egcdn m1 m2).1.

Lemma chinese_modl r1 r2 : chinese r1 r2 = r1 %[mod m1].
admit.
Defined.

Lemma chinese_modr r1 r2 : chinese r1 r2 = r2 %[mod m2].
admit.
Defined.

Lemma chinese_mod x : x = chinese (x %% m1) (x %% m2) %[mod m1 * m2].
admit.
Defined.

End Chinese.

#[deprecated(since="mathcomp 1.12.0", note="Use coprimeMl instead.")]
Notation coprime_mull := coprimeMl (only parsing).
#[deprecated(since="mathcomp 1.12.0", note="Use coprimeMr instead.")]
Notation coprime_mulr := coprimeMr (only parsing).
#[deprecated(since="mathcomp 1.12.0", note="Use coprimeXl instead.")]
Notation coprime_expl := coprimeXl (only parsing).
#[deprecated(since="mathcomp 1.12.0", note="Use coprimeXr instead.")]
Notation coprime_expr := coprimeXr (only parsing).

End div.

End mathcomp_DOT_ssreflect_DOT_div_WRAPPED.
Module Export mathcomp_DOT_ssreflect_DOT_div.
Module Export mathcomp.
Module Export ssreflect.
Module Export div.
Include mathcomp_DOT_ssreflect_DOT_div_WRAPPED.div.
End div.

End ssreflect.

End mathcomp.

End mathcomp_DOT_ssreflect_DOT_div.

Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.
Import mathcomp.ssreflect.ssreflect.
Import mathcomp.ssreflect.ssrfun.
Import mathcomp.ssreflect.ssrbool.
Import mathcomp.ssreflect.eqtype.
Import mathcomp.ssreflect.ssrnat.
Import mathcomp.ssreflect.seq.

Set Implicit Arguments.
Unset Strict Implicit.

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

Module Export Choice.

Section ClassDef.

Record mixin_of T := Mixin {
  find : pred T -> nat -> option T;
  _ : forall P n x, find P n = Some x -> P x;
  _ : forall P : pred T, (exists x, P x) -> exists n, find P n;
  _ : forall P Q : pred T, P =1 Q -> find P =1 find Q
}.
Record class_of T := Class {base : Equality.class_of T; mixin : mixin_of T}.
Local Coercion base : class_of >->  Equality.class_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Definition pack m :=
  fun b bT & phant_id (Equality.class bT) b => Pack (@Class T b m).

Definition eqType := @Equality.Pack cT class.

End ClassDef.
Coercion base : class_of >-> Equality.class_of.
Coercion sort : type >-> Sortclass.
Canonical eqType.
Notation choiceType := type.
Notation choiceMixin := mixin_of.
Notation ChoiceType T m := (@pack T m _ _ id).

Section ChoiceTheory.

Implicit Type T : choiceType.

Section OneType.

Variable T : choiceType.

Section CanChoice.

Variables (sT : Type) (f : sT -> T).

Lemma PcanChoiceMixin f' : pcancel f f' -> choiceMixin sT.
admit.
Defined.

Definition CanChoiceMixin f' (fK : cancel f f') :=
  PcanChoiceMixin (can_pcan fK).

End CanChoice.

Section SubChoice.

Variables (P : pred T) (sT : subType P).

Definition sub_choiceMixin := PcanChoiceMixin (@valK T P sT).
Definition sub_choiceClass := @Choice.Class sT (sub_eqMixin sT) sub_choiceMixin.
Canonical sub_choiceType := Choice.Pack sub_choiceClass.

End SubChoice.

Fact seq_choiceMixin : choiceMixin (seq T).
admit.
Defined.
Canonical seq_choiceType := Eval hnf in ChoiceType (seq T) seq_choiceMixin.

End OneType.

Section TagChoice.

Variables (I : choiceType) (T_ : I -> choiceType).

Fact tagged_choiceMixin : choiceMixin {i : I & T_ i}.
admit.
Defined.
Canonical tagged_choiceType :=
  Eval hnf in ChoiceType {i : I & T_ i} tagged_choiceMixin.

End TagChoice.

Fact nat_choiceMixin : choiceMixin nat.
admit.
Defined.
Canonical nat_choiceType := Eval hnf in ChoiceType nat nat_choiceMixin.

Definition bool_choiceMixin := CanChoiceMixin oddb.
Canonical bool_choiceType := Eval hnf in ChoiceType bool bool_choiceMixin.

Definition prod_choiceMixin T1 T2 := CanChoiceMixin (@tag_of_pairK T1 T2).
Canonical prod_choiceType T1 T2 :=
  Eval hnf in ChoiceType (T1 * T2) (prod_choiceMixin T1 T2).

End ChoiceTheory.
Notation "[ 'choiceMixin' 'of' T 'by' <: ]" :=
  (sub_choiceMixin _ : choiceMixin T)
  (at level 0, format "[ 'choiceMixin'  'of'  T  'by'  <: ]") : form_scope.

Module Countable.

Record mixin_of (T : Type) : Type := Mixin {
  pickle : T -> nat;
  unpickle : nat -> option T;
  pickleK : pcancel pickle unpickle
}.

Section ClassDef.
Record class_of T := Class { base : Choice.class_of T; mixin : mixin_of T }.
Local Coercion base : class_of >-> Choice.class_of.

Structure type : Type := Pack {sort : Type; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Definition pack m :=
  fun bT b & phant_id (Choice.class bT) b => Pack (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.

End ClassDef.

Module Export Exports.
Coercion mixin : class_of >-> mixin_of.
Coercion eqType : type >-> Equality.type.
Canonical choiceType.
Notation countType := type.
Notation CountType T m := (@pack T m _ _ id).
Notation CountMixin := Mixin.

End Exports.

End Countable.
Export Countable.Exports.

Definition unpickle T := Countable.unpickle (Countable.class T).
Definition pickle T := Countable.pickle (Countable.class T).
Arguments unpickle {T} n.
Arguments pickle {T} x.

Section CountableTheory.

Variable T : countType.

Lemma pcan_pickleK sT f f' :
  @pcancel T sT f f' -> pcancel (pickle \o f) (pcomp f' unpickle).
admit.
Defined.

Definition PcanCountMixin sT f f' (fK : pcancel f f') :=
  @CountMixin sT _ _ (pcan_pickleK fK).

Definition CanCountMixin sT f f' (fK : cancel f f') :=
  @PcanCountMixin sT _ _ (can_pcan fK).

Definition sub_countMixin P sT := PcanCountMixin (@valK T P sT).

Definition pickle_seq s := CodeSeq.code (map (@pickle T) s).
Definition unpickle_seq n := Some (pmap (@unpickle T) (CodeSeq.decode n)).
Lemma pickle_seqK : pcancel pickle_seq unpickle_seq.
admit.
Defined.

Definition seq_countMixin := CountMixin pickle_seqK.
Canonical seq_countType := Eval hnf in CountType (seq T) seq_countMixin.

End CountableTheory.

Notation "[ 'countMixin' 'of' T 'by' <: ]" :=
    (sub_countMixin _ : Countable.mixin_of T)
  (at level 0, format "[ 'countMixin'  'of'  T  'by'  <: ]") : form_scope.

Section SubCountType.

Variables (T : choiceType) (P : pred T).
Import Countable.

Structure subCountType : Type :=
  SubCountType {subCount_sort :> subType P; _ : mixin_of subCount_sort}.

Coercion sub_countType (sT : subCountType) :=
  Eval hnf in pack (let: SubCountType _ m := sT return mixin_of sT in m) id.
Canonical sub_countType.

Definition pack_subCountType U :=
  fun sT cT & sub_sort sT * sort cT -> U * U =>
  fun b m   & phant_id (Class b m) (class cT) => @SubCountType sT m.

End SubCountType.

Notation "[ 'subCountType' 'of' T ]" :=
    (@pack_subCountType _ _ T _ _ id _ _ id)
  (at level 0, format "[ 'subCountType'  'of'  T ]") : form_scope.

Section TagCountType.

Variables (I : countType) (T_ : I -> countType).

Definition pickle_tagged (u : {i : I & T_ i}) :=
  CodeSeq.code [:: pickle (tag u); pickle (tagged u)].
Definition unpickle_tagged s :=
  if CodeSeq.decode s is [:: ni; nx] then
    obind (fun i => omap (@Tagged I i T_) (unpickle nx)) (unpickle ni)
  else None.
Lemma pickle_taggedK : pcancel pickle_tagged unpickle_tagged.
admit.
Defined.

Definition tag_countMixin := CountMixin pickle_taggedK.
Canonical tag_countType := Eval hnf in CountType {i : I & T_ i} tag_countMixin.

End TagCountType.

Section CountableDataTypes.

Implicit Type T : countType.

Lemma nat_pickleK : pcancel id (@Some nat).
admit.
Defined.
Definition nat_countMixin := CountMixin nat_pickleK.
Canonical nat_countType := Eval hnf in CountType nat nat_countMixin.

Definition bool_countMixin := CanCountMixin oddb.
Canonical bool_countType := Eval hnf in CountType bool bool_countMixin.

Definition prod_countMixin T1 T2 := CanCountMixin (@tag_of_pairK T1 T2).
Canonical prod_countType T1 T2 :=
  Eval hnf in CountType (T1 * T2) (prod_countMixin T1 T2).

End CountableDataTypes.
Module Export mathcomp_DOT_ssreflect_DOT_fintype_WRAPPED.
Module Export fintype.
Import mathcomp.ssreflect.eqtype.

Declare Scope fin_quant_scope.

Module Finite.

Section RawMixin.

Variable T : eqType.

Definition axiom e := forall x : T, count_mem x e = 1.

Lemma uniq_enumP e : uniq e -> e =i T -> axiom e.
admit.
Defined.

Record mixin_of := Mixin {
  mixin_base : Countable.mixin_of T;
  mixin_enum : seq T;
  _ : axiom mixin_enum
}.

End RawMixin.

Section Mixins.

Variable T : countType.

Definition EnumMixin :=
  let: Countable.Pack _ (Countable.Class _ m) as cT := T
    return forall e : seq cT, axiom e -> mixin_of cT in
  @Mixin (EqType _ _) m.

Definition UniqMixin e Ue eT := @EnumMixin e (uniq_enumP Ue eT).

End Mixins.

Section ClassDef.
Record class_of T := Class {
  base : Choice.class_of T;
  mixin : mixin_of (Equality.Pack base)
}.
Definition base2 T c := Countable.Class (@base T c) (mixin_base (mixin c)).
Local Coercion base : class_of >-> Choice.class_of.

Structure type : Type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.

Definition pack b0 (m0 : mixin_of (EqType T b0)) :=
  fun bT b & phant_id (Choice.class bT) b =>
  fun m & phant_id m0 m => Pack (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition countType := @Countable.Pack cT (base2 class).

End ClassDef.

Module Import Exports.
Coercion mixin : class_of >-> mixin_of.
Coercion eqType : type >-> Equality.type.
Canonical choiceType.
Canonical countType.
Notation finType := type.
Notation FinType T m := (@pack T _ m _ _ id _ id).
Notation FinMixin := EnumMixin.
Notation UniqFinMixin := UniqMixin.
Notation "[ 'finType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'finType'  'of'  T ]") : form_scope.
End Exports.

Module Type EnumSig.
Parameter enum : forall cT : type, seq cT.
End EnumSig.

Module EnumDef : EnumSig.
Definition enum cT := mixin_enum (class cT).
End EnumDef.

Notation enum := EnumDef.enum.

End Finite.
Export Finite.Exports.

Definition fin_pred_sort (T : finType) (pT : predType T) := pred_sort pT.
Identity Coercion pred_sort_of_fin : fin_pred_sort >-> pred_sort.

Definition enum_mem T (mA : mem_pred _) := filter mA (Finite.enum T).
Notation enum A := (enum_mem (mem A)).
Definition pick (T : finType) (P : pred T) := ohead (enum P).

Notation "[ 'pick' x | P ]" := (pick (fun x => P%B))
  (at level 0, x ident, format "[ 'pick'  x  |  P  ]") : form_scope.

Local Notation card_type := (forall T : finType, mem_pred T -> nat).
Local Notation card_def := (fun T mA => size (enum_mem mA)).
Module Type CardDefSig.
Parameter card : card_type.
End CardDefSig.
Module CardDef : CardDefSig.
Definition card : card_type := card_def.
End CardDef.

Export CardDef.

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

Definition all B x y := let: F^* := B in F^~^*.

End Definitions.

Notation "[ x | B ]" := (quant0b (fun x => B x)) (at level 0, x ident).

Module Export Exports.

Notation ", F" := F^* (at level 200, format ", '/ '  F") : fin_quant_scope.

Notation "[ 'forall' x B ]" := [x | all B]
  (at level 0, x at level 99, B at level 200,
   format "[ '[hv' 'forall'  x B ] ']'") : bool_scope.

End Exports.

End FiniteQuant.
Export FiniteQuant.Exports.

Local Notation subset_type := (forall (T : finType) (A B : mem_pred T), bool).
Local Notation subset_def := (fun T A B => pred0b (predD A B)).
Module Type SubsetDefSig.
Parameter subset : subset_type.
End SubsetDefSig.
Module Export SubsetDef : SubsetDefSig.
Definition subset : subset_type := subset_def.
End SubsetDef.
Notation "A \subset B" := (subset (mem A) (mem B))
  (at level 70, no associativity) : bool_scope.

Section OpsTheory.

Variable T : finType.

Implicit Types (A B C D: {pred T}) (P Q : pred T) (x y : T) (s : seq T).

Section EnumPick.

Lemma mem_enum A : enum A =i A.
admit.
Defined.

End EnumPick.

End OpsTheory.

Section Quantifiers.

Variables (T : finType) (rT : T -> eqType).
Implicit Types (D P : pred T) (f : forall x, rT x).

Lemma eqfunP f1 f2 : reflect (forall x, f1 x = f2 x) [forall x, f1 x == f2 x].
admit.
Defined.

End Quantifiers.
Arguments eqfunP {T rT f1 f2}.

Section Injectiveb.

Variables (aT : finType) (rT : eqType) (f : aT -> rT).
Implicit Type D : {pred aT}.

Definition dinjectiveb D := uniq (map f (enum D)).

Definition injectiveb := dinjectiveb aT.

End Injectiveb.

Definition image_mem T T' f mA : seq T' := map f (@enum_mem T mA).
Notation image f A := (image_mem f (mem A)).

Definition codom T T' f := @image_mem T T' f (mem T).

Section Image.

Variable T : finType.
Implicit Type A : {pred T}.

Variables (T' : eqType) (f : T -> T').

Remark iinv_proof A y : y \in image f A -> {x | x \in A & f x = y}.
admit.
Defined.

Definition iinv A y fAy := s2val (@iinv_proof A y fAy).

End Image.

Lemma bool_enumP : Finite.axiom [:: true; false].
admit.
Defined.
Definition bool_finMixin := Eval hnf in FinMixin bool_enumP.
Canonical bool_finType := Eval hnf in FinType bool bool_finMixin.

Local Notation enumF T := (Finite.enum T).

Section TransferFinType.

Variables (eT : countType) (fT : finType) (f : eT -> fT).

Lemma pcan_enumP g : pcancel f g -> Finite.axiom (undup (pmap g (enumF fT))).
admit.
Defined.

Definition PcanFinMixin g fK := FinMixin (@pcan_enumP g fK).

End TransferFinType.

Section FinTypeForSub.

Variables (T : finType) (P : pred T) (sT : subCountType P).

Definition sub_enum : seq sT := pmap insub (enumF T).

Lemma mem_sub_enum u : u \in sub_enum.
admit.
Defined.

Lemma sub_enum_uniq : uniq sub_enum.
admit.
Defined.

Definition SubFinMixin := UniqFinMixin sub_enum_uniq mem_sub_enum.
Definition SubFinMixin_for (eT : eqType) of phant eT :=
  eq_rect _ Finite.mixin_of SubFinMixin eT.

End FinTypeForSub.

Notation "[ 'finMixin' 'of' T 'by' <: ]" :=
    (SubFinMixin_for (Phant T) (erefl _))
  (at level 0, format "[ 'finMixin'  'of'  T  'by'  <: ]") : form_scope.

Section OrdinalSub.

Variable n : nat.

Inductive ordinal : predArgType := Ordinal m of m < n.

Coercion nat_of_ord i := let: Ordinal m _ := i in m.

Canonical ordinal_subType := [subType for nat_of_ord].
Definition ordinal_eqMixin := Eval hnf in [eqMixin of ordinal by <:].
Canonical ordinal_eqType := Eval hnf in EqType ordinal ordinal_eqMixin.
Definition ordinal_choiceMixin := [choiceMixin of ordinal by <:].
Canonical ordinal_choiceType :=
  Eval hnf in ChoiceType ordinal ordinal_choiceMixin.
Definition ordinal_countMixin := [countMixin of ordinal by <:].
Canonical ordinal_countType := Eval hnf in CountType ordinal ordinal_countMixin.

Definition ord_enum : seq ordinal := pmap insub (iota 0 n).

Lemma ord_enum_uniq : uniq ord_enum.
admit.
Defined.

Lemma mem_ord_enum i : i \in ord_enum.
admit.
Defined.

Definition ordinal_finMixin :=
  Eval hnf in UniqFinMixin ord_enum_uniq mem_ord_enum.
Canonical ordinal_finType := Eval hnf in FinType ordinal ordinal_finMixin.

End OrdinalSub.

Notation "''I_' n" := (ordinal n)
  (at level 8, n at level 2, format "''I_' n").

Lemma cast_ord_proof n m (i : 'I_n) : n = m -> i < m.
admit.
Defined.
Definition cast_ord n m eq_n_m i := Ordinal (@cast_ord_proof n m i eq_n_m).

Section EnumRank.

Variable T : finType.
Implicit Type A : {pred T}.

Lemma enum_rank_subproof x0 A : x0 \in A -> 0 < #|A|.
admit.
Defined.

Definition enum_rank_in x0 A (Ax0 : x0 \in A) x :=
  insubd (Ordinal (@enum_rank_subproof x0 [eta A] Ax0)) (index x (enum A)).

Definition enum_rank x := @enum_rank_in x T (erefl true) x.

Lemma enum_default A : 'I_(#|A|) -> T.
admit.
Defined.

Definition enum_val A i := nth (@enum_default [eta A] i) (enum A) i.

End EnumRank.

Definition bump h i := (h <= i) + i.

Lemma lift_subproof n h (i : 'I_n.-1) : bump h i < n.
admit.
Defined.

Definition lift n (h : 'I_n) (i : 'I_n.-1) := Ordinal (lift_subproof h i).

Lemma lshift_subproof m n (i : 'I_m) : i < m + n.
admit.
Defined.

Lemma rshift_subproof m n (i : 'I_n) : m + i < m + n.
admit.
Defined.

Definition lshift m n (i : 'I_m) := Ordinal (lshift_subproof n i).
Definition rshift m n (i : 'I_n) := Ordinal (rshift_subproof m i).

Lemma split_subproof m n (i : 'I_(m + n)) : i >= m -> i - m < n.
admit.
Defined.

Definition split {m n} (i : 'I_(m + n)) : 'I_m + 'I_n :=
  match ltnP (i) m with
  | LtnNotGeq lt_i_m =>  inl _ (Ordinal lt_i_m)
  | GeqNotLtn ge_i_m =>  inr _ (Ordinal (split_subproof ge_i_m))
  end.

Section OrdinalPos.

Variable n' : nat.

Definition ord0 := Ordinal (ltn0Sn n').

End OrdinalPos.

Arguments ord0 {n'}.

Section ProdFinType.

Variable T1 T2 : finType.

Definition prod_enum := [seq (x1, x2) | x1 <- enum T1, x2 <- enum T2].

Lemma prod_enumP : Finite.axiom prod_enum.
admit.
Defined.

Definition prod_finMixin := Eval hnf in FinMixin prod_enumP.
Canonical prod_finType := Eval hnf in FinType (T1 * T2) prod_finMixin.

End ProdFinType.

Section TagFinType.

Variables (I : finType) (T_ : I -> finType).

Definition tag_enum :=
  flatten [seq [seq Tagged T_ x | x <- enumF (T_ i)] | i <- enumF I].

Lemma tag_enumP : Finite.axiom tag_enum.
admit.
Defined.

Definition tag_finMixin := Eval hnf in FinMixin tag_enumP.
Canonical tag_finType := Eval hnf in FinType {i : I & T_ i} tag_finMixin.

End TagFinType.

End fintype.
Module Export mathcomp.
Module Export ssreflect.
Module Export fintype.
Include mathcomp_DOT_ssreflect_DOT_fintype_WRAPPED.fintype.
End fintype.
Import mathcomp.ssreflect.eqtype.

Section TupleDef.

Variables (n : nat) (T : Type).

Structure tuple_of : Type := Tuple {tval :> seq T; _ : size tval == n}.

Canonical tuple_subType := Eval hnf in [subType for tval].

Implicit Type t : tuple_of.

Lemma tnth_default t : 'I_n -> T.
admit.
Defined.

Definition tnth t i := nth (tnth_default t i) t i.

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

Section EqTuple.

Variables (n : nat) (T : eqType).

Definition tuple_eqMixin := Eval hnf in [eqMixin of n.-tuple T by <:].
Canonical tuple_eqType := Eval hnf in EqType (n.-tuple T) tuple_eqMixin.

End EqTuple.

Definition tuple_choiceMixin n (T : choiceType) :=
  [choiceMixin of n.-tuple T by <:].

Canonical tuple_choiceType n (T : choiceType) :=
  Eval hnf in ChoiceType (n.-tuple T) (tuple_choiceMixin n T).

Definition tuple_countMixin n (T : countType) :=
  [countMixin of n.-tuple T by <:].

Canonical tuple_countType n (T : countType) :=
  Eval hnf in CountType (n.-tuple T) (tuple_countMixin n T).

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

Definition enum : seq (n.-tuple T) :=
  let extend e := flatten (codom (fun x => map (cons x) e)) in
  pmap insub (iter n extend [::[::]]).

Lemma enumP : Finite.axiom enum.
admit.
Defined.

End FinTuple.
End FinTuple.

Section UseFinTuple.

Variables (n : nat) (T : finType).

Definition tuple_finMixin := Eval hnf in FinMixin (@FinTuple.enumP n T).
Canonical tuple_finType := Eval hnf in FinType (n.-tuple T) tuple_finMixin.

Lemma enum_tupleP (A : {pred T}) : size (enum A) == #|A|.
admit.
Defined.
Canonical enum_tuple A := Tuple (enum_tupleP A).

Section ImageTuple.

Variables (T' : Type) (f : T -> T') (A : {pred T}).
Canonical codom_tuple : #|T|.-tuple T' := [tuple of codom f].

End ImageTuple.

End UseFinTuple.

Section Def.

Variables (aT : finType) (rT : aT -> Type).

Inductive finfun_on : seq aT -> Type :=
| finfun_nil                            : finfun_on [::]
| finfun_cons x s of rT x & finfun_on s : finfun_on (x :: s).

Local Fixpoint finfun_rec (g : forall x, rT x) s : finfun_on s :=
  if s is x1 :: s1 then finfun_cons (g x1) (finfun_rec g s1) else finfun_nil.

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
Local Notation finfun_def :=
  (fun aT rT g => FinfunOf (Phant (finPi aT rT)) (finfun_rec g (enum aT))).

Module Type FinfunDefSig.
Parameter finfun : forall aT rT, finPi aT rT -> {ffun finPi aT rT}.
End FinfunDefSig.

Module FinfunDef : FinfunDefSig.
Definition finfun := finfun_def.
End FinfunDef.

Notation finfun := FinfunDef.finfun.

Notation "[ 'ffun' x => E ]" := (@finfun _ (fun=> _) (fun x => E))
  (at level 0, x ident, format "[ 'ffun'  x  =>  E ]") : fun_scope.

Section DepPlainTheory.
Variables (aT : finType) (rT : aT -> Type).
Notation fT := {ffun finPi aT rT}.
Implicit Type f : fT.

Definition total_fun g x := Tagged rT (g x : rT x).

Definition tfgraph f := codom_tuple (total_fun f).

Local Definition tfgraph_inv (G : #|aT|.-tuple {x : aT & rT x}) : option fT :=
  if eqfunP isn't ReflectT Dtg then None else
  Some [ffun x => ecast x (rT x) (Dtg x) (tagged (tnth G (enum_rank x)))].

Local Lemma tfgraphK : pcancel tfgraph tfgraph_inv.
admit.
Defined.

End DepPlainTheory.
Arguments tfgraphK {aT rT} f : rename.

Section InheritedStructures.

Variable aT : finType.
Notation dffun_aT rT rS := {dffun forall x : aT, rT x : rS}.

Local Remark eqMixin rT : Equality.mixin_of (dffun_aT rT eqType).
admit.
Defined.
Canonical finfun_eqType (rT : eqType) :=
  EqType {ffun aT -> rT} (eqMixin (fun=> rT)).
Canonical dfinfun_eqType rT :=
  EqType (dffun_aT rT eqType) (eqMixin rT).

Local Remark choiceMixin rT : Choice.mixin_of (dffun_aT rT choiceType).
admit.
Defined.
Canonical finfun_choiceType (rT : choiceType) :=
  ChoiceType {ffun aT -> rT} (choiceMixin (fun=> rT)).
Canonical dfinfun_choiceType rT :=
  ChoiceType (dffun_aT rT choiceType) (choiceMixin rT).

Local Remark countMixin rT : Countable.mixin_of (dffun_aT rT countType).
admit.
Defined.
Canonical finfun_countType (rT : countType) :=
  CountType {ffun aT -> rT} (countMixin (fun => rT)).
Canonical dfinfun_countType rT :=
  CountType (dffun_aT rT countType) (countMixin rT).

Local Definition finMixin rT :=
  PcanFinMixin (tfgraphK : @pcancel _ (dffun_aT rT finType) _ _).
Canonical finfun_finType (rT : finType) :=
  FinType {ffun aT -> rT} (finMixin (fun=> rT)).

End InheritedStructures.

Section FunPlainTheory.

Variables (aT : finType) (rT : Type).
Notation fT := {ffun aT -> rT}.
Implicit Types (f : fT) (R : pred rT).

Definition fgraph f := codom_tuple f.

End FunPlainTheory.

Declare Scope big_scope.

Reserved Notation "\big [ op / idx ]_ i F"
  (at level 36, F at level 36, op, idx at level 10, i at level 0,
     right associativity,
           format "'[' \big [ op / idx ]_ i '/  '  F ']'").
Reserved Notation "\big [ op / idx ]_ ( i : t | P ) F"
  (at level 36, F at level 36, op, idx at level 10, i at level 50,
           format "'[' \big [ op / idx ]_ ( i   :  t   |  P ) '/  '  F ']'").
Reserved Notation "\big [ op / idx ]_ ( i : t ) F"
  (at level 36, F at level 36, op, idx at level 10, i at level 50,
           format "'[' \big [ op / idx ]_ ( i   :  t ) '/  '  F ']'").
Reserved Notation "\big [ op / idx ]_ ( i < n ) F"
  (at level 36, F at level 36, op, idx at level 10, i, n at level 50,
           format "'[' \big [ op / idx ]_ ( i  <  n )  F ']'").

Reserved Notation "\sum_ i F"
  (at level 41, F at level 41, i at level 0,
           right associativity,
           format "'[' \sum_ i '/  '  F ']'").

Reserved Notation "\sum_ ( i : t ) F"
  (at level 41, F at level 41, i at level 50).
Reserved Notation "\sum_ ( i < n ) F"
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \sum_ ( i  <  n ) '/  '  F ']'").

Reserved Notation "\prod_ i F"
  (at level 36, F at level 36, i at level 0,
           format "'[' \prod_ i '/  '  F ']'").
Reserved Notation "\bigcap_ ( i : t | P ) F"
  (at level 41, F at level 41, i at level 50,
           format "'[' \bigcap_ ( i   :  t   |  P ) '/  '  F ']'").

Module Export Monoid.

Module Import Exports.
End Exports.

Section CommutativeAxioms.

Variable (T : Type) (zero one : T) (mul add : T -> T -> T) (inv : T -> T).
Hypothesis mulC : commutative mul.

Lemma mulC_id : left_id one mul -> right_id one mul.
Proof.
by move=> mul1x x; rewrite mulC.
Qed.

Lemma mulC_dist : left_distributive mul add -> right_distributive mul add.
Proof.
by move=> mul_addl x y z; rewrite !(mulC x).
Qed.

End CommutativeAxioms.

Open Scope big_scope.

Variant bigbody R I := BigBody of I & (R -> R -> R) & bool & R.

Definition applybig {R I} (body : bigbody R I) x :=
  let: BigBody _ op b v := body in if b then op v x else x.

Definition reducebig R I idx r (body : I -> bigbody R I) :=
  foldr (applybig \o body) idx r.

Module Type BigOpSig.
Parameter bigop : forall R I, R -> seq I -> (I -> bigbody R I) -> R.
End BigOpSig.

Module BigOp : BigOpSig.
Definition bigop := reducebig.
End BigOp.

Notation bigop := BigOp.bigop (only parsing).

Fact index_enum_key : unit.
admit.
Defined.

Definition index_enum (T : finType) :=
  locked_with index_enum_key (Finite.enum T).
Notation "\big [ op / idx ]_ i F" :=
  (bigop idx (index_enum _) (fun i => BigBody i op true F)) : big_scope.
Notation "\big [ op / idx ]_ ( i : t | P ) F" :=
  (bigop idx (index_enum _) (fun i : t => BigBody i op P%B F))
     (only parsing) : big_scope.
Notation "\big [ op / idx ]_ ( i : t ) F" :=
  (bigop idx (index_enum _) (fun i : t => BigBody i op true F))
     (only parsing) : big_scope.
Notation "\big [ op / idx ]_ ( i < n ) F" :=
  (\big[op/idx]_(i : ordinal n) F) : big_scope.

Declare Scope set_scope.

Section SetType.

Variable T : finType.

Inductive set_type : predArgType := FinSet of {ffun pred T}.
Definition finfun_of_set A := let: FinSet f := A in f.
Definition set_of of phant T := set_type.
Identity Coercion type_of_set_of : set_of >-> set_type.

Canonical set_subType := Eval hnf in [newType for finfun_of_set].
Definition set_eqMixin := Eval hnf in [eqMixin of set_type by <:].
Canonical set_eqType := Eval hnf in EqType set_type set_eqMixin.
Definition set_choiceMixin := [choiceMixin of set_type by <:].
Canonical set_choiceType := Eval hnf in ChoiceType set_type set_choiceMixin.
Definition set_countMixin := [countMixin of set_type by <:].
Canonical set_countType := Eval hnf in CountType set_type set_countMixin.
Canonical set_subCountType := Eval hnf in [subCountType of set_type].
Definition set_finMixin := [finMixin of set_type by <:].
Canonical set_finType := Eval hnf in FinType set_type set_finMixin.

End SetType.

Delimit Scope set_scope with SET.
Open Scope set_scope.

Notation "{ 'set' T }" := (set_of (Phant T))
  (at level 0, format "{ 'set'  T }") : type_scope.

Local Notation finset_def := (fun T P => @FinSet T (finfun P)).

Local Notation pred_of_set_def := (fun T (A : set_type T) => val A : _ -> _).

Module Type SetDefSig.
Parameter finset : forall T : finType, pred T -> {set T}.
Parameter pred_of_set : forall T, set_type T -> fin_pred_sort (predPredType T).
End SetDefSig.

Module SetDef : SetDefSig.
Definition finset := finset_def.
Definition pred_of_set := pred_of_set_def.
End SetDef.

Notation finset := SetDef.finset.
Notation pred_of_set := SetDef.pred_of_set.

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
Definition setTfor (phT : phant T) := [set x : T | true].

End BasicSetTheory.

Notation "[ 'set' : T ]" := (setTfor (Phant T))
  (at level 0, format "[ 'set' :  T ]") : set_scope.

Notation setT := [set: _] (only parsing).

Section setOpsDefs.

Variable T : finType.
Implicit Types (a x : T) (A B D : {set T}) (P : {set {set T}}).

Definition set1 a := [set x | x == a].
Definition setI A B := [set x in A | x \in B].

End setOpsDefs.

Notation "[ 'set' a ]" := (set1 a)
  (at level 0, a at level 99, format "[ 'set'  a ]") : set_scope.

Local Notation imset_def :=
  (fun (aT rT : finType) f mD => [set y in @image_mem aT rT f mD]).
Local Notation imset2_def :=
  (fun (aT1 aT2 rT : finType) f (D1 : mem_pred aT1) (D2 : _ -> mem_pred aT2) =>
     [set y in @image_mem _ rT (prod_curry f)
                           (mem [pred u | D1 u.1 & D2 u.1 u.2])]).

Module Type ImsetSig.
Parameter imset : forall aT rT : finType,
 (aT -> rT) -> mem_pred aT -> {set rT}.
Parameter imset2 : forall aT1 aT2 rT : finType,
 (aT1 -> aT2 -> rT) -> mem_pred aT1 -> (aT1 -> mem_pred aT2) -> {set rT}.
End ImsetSig.

Module Imset : ImsetSig.
Definition imset := imset_def.
Definition imset2 := imset2_def.
End Imset.

Notation imset := Imset.imset.
Notation imset2 := Imset.imset2.
Definition preimset (aT : finType) rT f (R : mem_pred rT) :=
  [set x : aT | in_mem (f x) R].

Notation "f @^-1: A" := (preimset f (mem A)) (at level 24) : set_scope.
Notation "f @: A" := (imset f (mem A)) (at level 24) : set_scope.
Notation "f @2: ( A , B )" := (imset2 f (mem A) (fun _ => mem B))
  (at level 24, format "f  @2:  ( A ,  B )") : set_scope.

Notation "\bigcap_ ( i : t | P ) F" :=
  (\big[@setI _/setT]_(i : t | P%B) F%SET) (only parsing): set_scope.

Module Export ssralg.

Declare Scope ring_scope.
Declare Scope term_scope.
Reserved Notation "n %:R" (at level 2, left associativity, format "n %:R").

Reserved Notation "x %:T" (at level 2, left associativity, format "x %:T").
Reserved Notation "''X_' i" (at level 8, i at level 2, format "''X_' i").

Reserved Notation "''exists' ''X_' i , f"
  (at level 199, i at level 2, right associativity,
   format "'[hv' ''exists'  ''X_' i , '/ '  f ']'").
Reserved Notation "''forall' ''X_' i , f"
  (at level 199, i at level 2, right associativity,
   format "'[hv' ''forall'  ''X_' i , '/ '  f ']'").

Delimit Scope ring_scope with R.
Delimit Scope term_scope with T.
Local Open Scope ring_scope.

Module Import GRing.

Module Export Zmodule.

Record mixin_of (V : Type) : Type := Mixin {
  zero : V;
  opp : V -> V;
  add : V -> V -> V;
  _ : associative add;
  _ : commutative add;
  _ : left_id zero add;
  _ : left_inverse zero opp add
}.

Section ClassDef.
Record class_of T := Class { base : Choice.class_of T; mixin : mixin_of T }.
Local Coercion base : class_of >-> Choice.class_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Definition pack m :=
  fun bT b & phant_id (Choice.class bT) b => Pack (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> Choice.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Canonical eqType.
Canonical choiceType.
Notation zmodType := type.
Notation ZmodType T m := (@pack T m _ _ id).
Notation ZmodMixin := Mixin.
End Exports.

End Zmodule.

Definition zero V := Zmodule.zero (Zmodule.class V).
Definition opp V := Zmodule.opp (Zmodule.class V).
Definition add V := Zmodule.add (Zmodule.class V).

Local Notation "0" := (zero _) : ring_scope.
Local Notation "- x" := (opp x) : ring_scope.
Local Notation "+%R" := (@add _) : fun_scope.
Local Notation "x + y" := (add x y) : ring_scope.
Local Notation "x - y" := (x + - y) : ring_scope.

Definition natmul V x n := nosimpl iterop _ n +%R x (zero V).

Local Notation "x *+ n" := (natmul x n) : ring_scope.

Local Notation "s `_ i" := (nth 0 s i) : ring_scope.

Section ZmoduleTheory.

Variable V : zmodType.
Implicit Types x y : V.

Lemma subr_eq0 x y : (x - y == 0) = (x == y).
admit.
Defined.

End ZmoduleTheory.

Module Ring.

Record mixin_of (R : zmodType) : Type := Mixin {
  one : R;
  mul : R -> R -> R;
  _ : associative mul;
  _ : left_id one mul;
  _ : right_id one mul;
  _ : left_distributive mul +%R;
  _ : right_distributive mul +%R;
  _ : one != 0
}.

Definition EtaMixin R one mul mulA mul1x mulx1 mul_addl mul_addr nz1 :=
  let _ := @Mixin R one mul mulA mul1x mulx1 mul_addl mul_addr nz1 in
  @Mixin (Zmodule.Pack (Zmodule.class R)) _ _
     mulA mul1x mulx1 mul_addl mul_addr nz1.

Section ClassDef.
Record class_of (R : Type) : Type := Class {
  base : Zmodule.class_of R;
  mixin : mixin_of (Zmodule.Pack base)
}.
Local Coercion base : class_of >-> Zmodule.class_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Definition pack b0 (m0 : mixin_of (@Zmodule.Pack T b0)) :=
  fun bT b & phant_id (Zmodule.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition zmodType := @Zmodule.Pack cT class.

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> Zmodule.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Canonical eqType.
Canonical choiceType.
Canonical zmodType.
Notation ringType := type.
Notation RingType T m := (@pack T _ m _ _ id _ id).
Notation RingMixin := Mixin.
End Exports.

End Ring.
Import Ring.Exports.

Definition one (R : ringType) : R := Ring.one (Ring.class R).
Definition mul (R : ringType) : R -> R -> R := Ring.mul (Ring.class R).
Definition exp R x n := nosimpl iterop _ n (@mul R) x (one R).
Definition comm R x y := @mul R x y = mul y x.

Local Notation "1" := (one _) : ring_scope.
Local Notation "n %:R" := (1 *+ n) : ring_scope.
Local Notation "*%R" := (@mul _) : fun_scope.
Local Notation "x * y" := (mul x y) : ring_scope.
Local Notation "x ^+ n" := (exp x n) : ring_scope.

Section RingTheory.

Variable R : ringType.
Lemma oner_neq0 : 1 != 0 :> R.
admit.
Defined.

End RingTheory.

Module Export Lmodule.

Structure mixin_of (R : ringType) (V : zmodType) : Type := Mixin {
  scale : R -> V -> V;
  _ : forall a b v, scale a (scale b v) = scale (a * b) v;
  _ : left_id 1 scale;
  _ : right_distributive scale +%R;
  _ : forall v, {morph scale^~ v: a b / a + b}
}.

Section ClassDef.

Variable R : ringType.
Record class_of V := Class {
  base : Zmodule.class_of V;
  mixin : mixin_of R (Zmodule.Pack base)
}.

Structure type (phR : phant R) := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variable (phR : phant R) (T : Type) (cT : type phR).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Definition pack b0 (m0 : mixin_of R (@Zmodule.Pack T b0)) :=
  fun bT b & phant_id (Zmodule.class bT) b =>
  fun    m & phant_id m0 m => Pack phR (@Class T b m).

End ClassDef.

Module Import Exports.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Notation lmodType R := (type (Phant R)).
Notation LmodType R T m := (@pack _ (Phant R) T _ m _ _ id _ id).
Notation LmodMixin := Mixin.
End Exports.

End Lmodule.
Import Lmodule.Exports.

Definition scale (R : ringType) (V : lmodType R) : R -> V -> V :=
  Lmodule.scale (Lmodule.class V).

Module ComRing.

Definition RingMixin R one mul mulA mulC mul1x mul_addl :=
  let mulx1 := Monoid.mulC_id mulC mul1x in
  let mul_addr := Monoid.mulC_dist mulC mul_addl in
  @Ring.EtaMixin R one mul mulA mul1x mulx1 mul_addl mul_addr.

Section ClassDef.
Record class_of R :=
  Class {base : Ring.class_of R; mixin : commutative (Ring.mul base)}.
Local Coercion base : class_of >-> Ring.class_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variable (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Definition pack mul0 (m0 : @commutative T T mul0) :=
  fun bT b & phant_id (Ring.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition zmodType := @Zmodule.Pack cT class.
Definition ringType := @Ring.Pack cT class.

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> Ring.class_of.
Coercion sort : type >-> Sortclass.
Canonical eqType.
Canonical zmodType.
Canonical ringType.
Notation comRingType := type.
Notation ComRingType T m := (@pack T _ m _ _ id _ id).
Notation ComRingMixin := RingMixin.
End Exports.

End ComRing.
Import ComRing.Exports.

Module UnitRing.

Record mixin_of (R : ringType) : Type := Mixin {
  unit : pred R;
  inv : R -> R;
  _ : {in unit, left_inverse 1 inv *%R};
  _ : {in unit, right_inverse 1 inv *%R};
  _ : forall x y, y * x = 1 /\ x * y = 1 -> unit x;
  _ : {in [predC unit], inv =1 id}
}.

Definition EtaMixin R unit inv mulVr mulrV unitP inv_out :=
  let _ := @Mixin R unit inv mulVr mulrV unitP inv_out in
  @Mixin (Ring.Pack (Ring.class R)) unit inv mulVr mulrV unitP inv_out.

Section ClassDef.
Record class_of (R : Type) : Type := Class {
  base : Ring.class_of R;
  mixin : mixin_of (Ring.Pack base)
}.
Local Coercion base : class_of >-> Ring.class_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Definition pack b0 (m0 : mixin_of (@Ring.Pack T b0)) :=
  fun bT b & phant_id (Ring.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition zmodType := @Zmodule.Pack cT class.
Definition ringType := @Ring.Pack cT class.

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> Ring.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Canonical eqType.
Canonical zmodType.
Canonical ringType.
Notation unitRingType := type.
Notation UnitRingType T m := (@pack T _ m _ _ id _ id).
Notation UnitRingMixin := EtaMixin.
End Exports.

End UnitRing.
Import UnitRing.Exports.

Definition unit {R : unitRingType} :=
  [qualify a u : R | UnitRing.unit (UnitRing.class R) u].
Definition inv {R : unitRingType} : R -> R := UnitRing.inv (UnitRing.class R).

Local Notation "x ^-1" := (inv x).

Module ComUnitRing.

Section Mixin.

Variables (R : comRingType) (unit : pred R) (inv : R -> R).
Hypothesis mulVx : {in unit, left_inverse 1 inv *%R}.
Hypothesis unitPl : forall x y, y * x = 1 -> unit x.

Fact mulC_mulrV : {in unit, right_inverse 1 inv *%R}.
admit.
Defined.

Fact mulC_unitP x y : y * x = 1 /\ x * y = 1 -> unit x.
Proof.
by case=> yx _; apply: unitPl yx.
Qed.

Definition Mixin := UnitRingMixin mulVx mulC_mulrV mulC_unitP.

End Mixin.

Section ClassDef.
Record class_of (R : Type) : Type := Class {
  base : ComRing.class_of R;
  mixin : UnitRing.mixin_of (Ring.Pack base)
}.
Local Coercion base : class_of >-> ComRing.class_of.
Definition base2 R m := UnitRing.Class (@mixin R m).
Local Coercion base2 : class_of >-> UnitRing.class_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition zmodType := @Zmodule.Pack cT class.
Definition ringType := @Ring.Pack cT class.
Definition comRingType := @ComRing.Pack cT class.
Definition unitRingType := @UnitRing.Pack cT class.

End ClassDef.

Module Import Exports.
Coercion base2 : class_of >-> UnitRing.class_of.
Coercion sort : type >-> Sortclass.
Canonical eqType.
Canonical choiceType.
Canonical zmodType.
Canonical ringType.
Canonical comRingType.
Canonical unitRingType.
Notation comUnitRingType := type.
End Exports.

End ComUnitRing.
Import ComUnitRing.Exports.

Section TermDef.

Variable R : Type.

Inductive term : Type :=
| Var of nat
| Const of R
| NatConst of nat
| Add of term & term
| Opp of term
| NatMul of term & nat
| Mul of term & term
| Inv of term
| Exp of term & nat.

Inductive formula : Type :=
| Bool of bool
| Equal of term & term
| Unit of term
| And of formula & formula
| Or of formula & formula
| Implies of formula & formula
| Not of formula
| Exists of nat & formula
| Forall of nat & formula.

End TermDef.
Bind Scope term_scope with formula.
Arguments Add {R} t1%T t2%T.
Arguments And {R} f1%T f2%T.
Arguments Or {R} f1%T f2%T.
Arguments Exists {R} i%N f1%T.

Arguments Bool {R} b.
Arguments Const {R} x.

Notation True := (Bool true).
Notation False := (Bool false).

Local Notation "''X_' i" := (Var _ i) : term_scope.
Local Notation "n %:R" := (NatConst _ n) : term_scope.
Local Notation "x %:T" := (Const x) : term_scope.
Local Infix "+" := Add : term_scope.
Local Notation "- t" := (Opp t) : term_scope.
Local Infix "*" := Mul : term_scope.
Local Infix "*+" := NatMul : term_scope.
Local Notation "t ^-1" := (Inv t) : term_scope.
Local Infix "^+" := Exp : term_scope.
Local Infix "==" := Equal : term_scope.
Local Infix "/\" := And : term_scope.
Local Infix "\/" := Or : term_scope.
Local Infix "==>" := Implies : term_scope.
Local Notation "~ f" := (Not f) : term_scope.
Local Notation "''exists' ''X_' i , f" := (Exists i f) : term_scope.
Local Notation "''forall' ''X_' i , f" := (Forall i f) : term_scope.

Section EvalTerm.

Variable R : unitRingType.

Fixpoint eval (e : seq R) (t : term R) {struct t} : R :=
  match t with
  | ('X_i)%T => e`_i
  | (x%:T)%T => x
  | (n%:R)%T => n%:R
  | (t1 + t2)%T => eval e t1 + eval e t2
  | (- t1)%T => - eval e t1
  | (t1 *+ n)%T => eval e t1 *+ n
  | (t1 * t2)%T => eval e t1 * eval e t2
  | t1^-1%T => (eval e t1)^-1
  | (t1 ^+ n)%T => eval e t1 ^+ n
  end.

Fixpoint holds (e : seq R) (f : formula R) {struct f} : Prop :=
  match f with
  | Bool b => b
  | (t1 == t2)%T => eval e t1 = eval e t2
  | Unit t1 => eval e t1 \in unit
  | (f1 /\ f2)%T => holds e f1 /\ holds e f2
  | (f1 \/ f2)%T => holds e f1 \/ holds e f2
  | (f1 ==> f2)%T => holds e f1 -> holds e f2
  | (~ f1)%T => ~ holds e f1
  | ('exists 'X_i, f1)%T => exists x, holds (set_nth 0 e i x) f1
  | ('forall 'X_i, f1)%T => forall x, holds (set_nth 0 e i x) f1
  end.

Fixpoint rterm (t : term R) :=
  match t with
  | _^-1 => false
  | t1 + t2 | t1 * t2 => rterm t1 && rterm t2
  | - t1 | t1 *+ _ | t1 ^+ _ => rterm t1
  | _ => true
  end%T.

Fixpoint rformula (f : formula R) :=
  match f with
  | Bool _ => true
  | t1 == t2 => rterm t1 && rterm t2
  | Unit t1 => false
  | f1 /\ f2 | f1 \/ f2 | f1 ==> f2 => rformula f1 && rformula f2
  | ~ f1 | ('exists 'X__, f1) | ('forall 'X__, f1) => rformula f1
  end%T.

Fixpoint qf_form (f : formula R) :=
  match f with
  | Bool _ | _ == _ | Unit _ => true
  | f1 /\ f2 | f1 \/ f2 | f1 ==> f2 => qf_form f1 && qf_form f2
  | ~ f1 => qf_form f1
  | _ => false
  end%T.

Definition qf_eval e := fix loop (f : formula R) : bool :=
  match f with
  | Bool b => b
  | t1 == t2 => (eval e t1 == eval e t2)%bool
  | Unit t1 => eval e t1 \in unit
  | f1 /\ f2 => loop f1 && loop f2
  | f1 \/ f2 => loop f1 || loop f2
  | f1 ==> f2 => (loop f1 ==> loop f2)%bool
  | ~ f1 => ~~ loop f1
  |_ => false
  end%T.

Lemma qf_evalP e f : qf_form f -> reflect (holds e f) (qf_eval e f).
admit.
Defined.

Section Pick.

Variables (I : finType) (pred_f then_f : I -> formula R) (else_f : formula R).

Definition Pick :=
  \big[Or/False]_(p : {ffun pred I})
    ((\big[And/True]_i (if p i then pred_f i else ~ pred_f i))
    /\ (if pick p is Some i then then_f i else else_f))%T.

End Pick.

End EvalTerm.

Module IntegralDomain.

Definition axiom (R : ringType) :=
  forall x y : R, x * y = 0 -> (x == 0) || (y == 0).

Section ClassDef.
Record class_of (R : Type) : Type :=
  Class {base : ComUnitRing.class_of R; mixin : axiom (Ring.Pack base)}.
Local Coercion base : class_of >-> ComUnitRing.class_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variable (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition ringType := @Ring.Pack cT class.
Definition unitRingType := @UnitRing.Pack cT class.

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> ComUnitRing.class_of.
Coercion sort : type >-> Sortclass.
Canonical ringType.
Canonical unitRingType.
Notation idomainType := type.
End Exports.

End IntegralDomain.
Import IntegralDomain.Exports.

Module Export Field.

Definition mixin_of (R : unitRingType) := forall x : R, x != 0 -> x \in unit.

Section Mixins.

Definition axiom (R : ringType) inv := forall x : R, x != 0 -> inv x * x = 1.

Variables (R : comRingType) (inv : R -> R).
Hypotheses (mulVf : axiom inv) (inv0 : inv 0 = 0).

Fact intro_unit (x y : R) : y * x = 1 -> x != 0.
admit.
Defined.

Fact inv_out : {in predC (predC1 0), inv =1 id}.
Proof.
by move=> x /negbNE/eqP->.
Qed.

Definition UnitMixin := ComUnitRing.Mixin mulVf intro_unit inv_out.

End Mixins.

Section ClassDef.
Record class_of (F : Type) : Type := Class {
  base : IntegralDomain.class_of F;
  mixin : mixin_of (UnitRing.Pack base)
}.
Local Coercion base : class_of >-> IntegralDomain.class_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variable (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition comUnitRingType := @ComUnitRing.Pack cT class.
Definition idomainType := @IntegralDomain.Pack cT class.

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> IntegralDomain.class_of.
Coercion comUnitRingType : type >-> ComUnitRing.type.
Canonical idomainType.
Notation fieldType := type.
Notation FieldUnitMixin := UnitMixin.
End Exports.

End Field.

Module Export DecidableField.

Definition axiom (R : unitRingType) (s : seq R -> pred (formula R)) :=
  forall e f, reflect (holds e f) (s e f).

Record mixin_of (R : unitRingType) : Type :=
  Mixin { sat : seq R -> pred (formula R); satP : axiom sat}.

Section ClassDef.
Record class_of (F : Type) : Type :=
  Class {base : Field.class_of F; mixin : mixin_of (UnitRing.Pack base)}.
Local Coercion base : class_of >-> Field.class_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variable (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition comUnitRingType := @ComUnitRing.Pack cT class.
Definition fieldType := @Field.Pack cT class.

End ClassDef.

Module Export Exports.
Coercion mixin : class_of >-> mixin_of.
Coercion comUnitRingType : type >-> ComUnitRing.type.
Canonical fieldType.
Notation decFieldType := type.
End Exports.

End DecidableField.

Section DecidableFieldTheory.

Variable F : decFieldType.

Definition sat := DecidableField.sat (DecidableField.class F).

Lemma satP : DecidableField.axiom sat.
admit.
Defined.

End DecidableFieldTheory.

Module Export Theory.
Definition subr_eq0 := subr_eq0.
Definition oner_neq0 := oner_neq0.
Definition satP {F e f} := @satP F e f.

End Theory.

End GRing.
Export Zmodule.Exports.
Export Ring.Exports.
Export Lmodule.Exports.
Export UnitRing.Exports.
Export ComRing.Exports.
Export ComUnitRing.Exports.
Export IntegralDomain.Exports.
Export Field.Exports.
Export DecidableField.Exports.

Notation "0" := (zero _) : ring_scope.
Notation "- x" := (opp x) : ring_scope.
Notation "+%R" := (@add _) : fun_scope.
Notation "x + y" := (add x y) : ring_scope.
Notation "x - y" := (add x (- y)) : ring_scope.
Notation "x *+ n" := (natmul x n) : ring_scope.
Notation "s `_ i" := (seq.nth 0%R s%R i) : ring_scope.

Notation "1" := (one _) : ring_scope.
Notation "- 1" := (opp 1) : ring_scope.

Notation "n %:R" := (natmul 1 n) : ring_scope.
Notation "*%R" := (@mul _) : fun_scope.
Notation "x * y" := (mul x y) : ring_scope.
Notation "x ^+ n" := (exp x n) : ring_scope.
Notation "x ^-1" := (inv x) : ring_scope.
Notation "x ^- n" := (inv (x ^+ n)) : ring_scope.
Notation "a *: m" := (scale a m) : ring_scope.
Notation "\sum_ i F" :=
  (\big[+%R/0%R]_i F%R) : ring_scope.
Notation "\sum_ ( i : t ) F" :=
  (\big[+%R/0%R]_(i : t) F%R) (only parsing) : ring_scope.
Notation "\sum_ ( i < n ) F" :=
  (\big[+%R/0%R]_(i < n) F%R) : ring_scope.
Notation "\prod_ i F" :=
  (\big[*%R/1%R]_i F%R) : ring_scope.

Notation "''X_' i" := (Var _ i) : term_scope.
Notation "n %:R" := (NatConst _ n) : term_scope.
Notation "0" := 0%:R%T : term_scope.
Notation "x %:T" := (Const x) : term_scope.
Infix "+" := Add : term_scope.
Notation "- t" := (Opp t) : term_scope.
Notation "t - u" := (Add t (- u)) : term_scope.
Infix "*" := Mul : term_scope.
Infix "*+" := NatMul : term_scope.
Notation "t ^-1" := (Inv t) : term_scope.
Infix "^+" := Exp : term_scope.
Infix "==" := Equal : term_scope.
Notation "x != y" := (GRing.Not (x == y)) : term_scope.
Infix "/\" := And : term_scope.
Infix "\/" := Or : term_scope.
Infix "==>" := Implies : term_scope.
Notation "~ f" := (Not f) : term_scope.
Notation "''exists' ''X_' i , f" := (Exists i f) : term_scope.
Notation "''forall' ''X_' i , f" := (Forall i f) : term_scope.

End ssralg.

Declare Scope group_scope.
Declare Scope Group_scope.

Delimit Scope group_scope with g.
Delimit Scope Group_scope with G.
Open Scope group_scope.

Module Export FinGroup.

Record mixin_of (T : Type) : Type := BaseMixin {
  mul : T -> T -> T;
  one : T;
  inv : T -> T;
  _ : associative mul;
  _ : left_id one mul;
  _ : involutive inv;
  _ : {morph inv : x y / mul x y >-> mul y x}
}.

Structure base_type : Type := PackBase {
  sort : Type;
   _ : mixin_of sort;
   _ : Finite.class_of sort
}.

Definition arg_sort := sort.

Definition mixin T :=
  let: PackBase _ m _ := T return mixin_of (sort T) in m.

Definition finClass T :=
  let: PackBase _ _ m := T return Finite.class_of (sort T) in m.

Structure type : Type := Pack {
  base : base_type;
  _ : left_inverse (one (mixin base)) (inv (mixin base)) (mul (mixin base))
}.

Section Mixin.

Variables (T : Type) (one : T) (mul : T -> T -> T) (inv : T -> T).

Hypothesis mulA : associative mul.
Hypothesis mul1 : left_id one mul.
Hypothesis mulV : left_inverse one inv mul.
Notation "1" := one.
Infix "*" := mul.
Notation "x ^-1" := (inv x).

Lemma mk_invgK : involutive inv.
Proof.
have mulV21 x: x^-1^-1 * 1 = x by rewrite -(mulV x) mulA mulV mul1.
by move=> x; rewrite -[_ ^-1]mulV21 -(mul1 1) mulA !mulV21.
Qed.

Lemma mk_invMg : {morph inv : x y / x * y >-> y * x}.
admit.
Defined.

Definition Mixin := BaseMixin mulA mul1 mk_invgK mk_invMg.

End Mixin.

Definition pack_base T m :=
  fun c cT & phant_id (Finite.class cT) c => @PackBase T m c.

Section InheritedClasses.

Variable bT : base_type.
Local Notation T := (arg_sort bT).
Local Notation class := (finClass bT).
Canonical finType := Finite.Pack class.
Definition arg_finType := Eval hnf in [finType of T].

End InheritedClasses.
Coercion mixin : base_type >-> mixin_of.
Coercion base : type >-> base_type.
Coercion arg_finType : base_type >-> Finite.type.
Notation baseFinGroupType := base_type.
Notation finGroupType := type.
Notation BaseFinGroupType T m := (@pack_base T m _ _ id).
Notation FinGroupType := Pack.

Section ElementOps.

Variable T : baseFinGroupType.
Notation rT := (FinGroup.sort T).

Definition oneg : rT := FinGroup.one T.
Definition mulg : T -> T -> rT := FinGroup.mul T.
Definition invg : T -> rT := FinGroup.inv T.
Definition expgn_rec (x : T) n : rT := iterop n mulg x oneg.

End ElementOps.

Definition expgn := nosimpl expgn_rec.

Notation "1" := (oneg _) : group_scope.
Notation "x1 * x2" := (mulg x1 x2) : group_scope.
Notation "x ^-1" := (invg x) : group_scope.

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
admit.
Defined.

Lemma set_mulgA : associative set_mulg.
admit.
Defined.

Lemma set_invgK : involutive set_invg.
admit.
Defined.

Lemma set_invgM : {morph set_invg : A B / set_mulg A B >-> set_mulg B A}.
admit.
Defined.

Definition group_set_baseGroupMixin : FinGroup.mixin_of (set_type gT) :=
  FinGroup.BaseMixin set_mulgA set_mul1g set_invgK set_invgM.

Canonical group_set_baseGroupType :=
  Eval hnf in BaseFinGroupType (set_type gT) group_set_baseGroupMixin.

End BaseSetMulDef.

Module Export GroupSet.
Definition sort (gT : baseFinGroupType) := {set gT}.
Identity Coercion GroupSet_of_sort : GroupSet.sort >-> set_of.

Section GroupSetMulProp.

Variable gT : finGroupType.
Implicit Types A B C D : {set gT}.

Definition group_set A := (1 \in A) && (A * A \subset A).

Structure group_type : Type := Group {
  gval :> GroupSet.sort gT;
  _ : group_set gval
}.

Definition group_of of phant gT : predArgType := group_type.
Local Notation groupT := (group_of (Phant gT)).

Canonical group_subType := Eval hnf in [subType for gval].
Definition group_eqMixin := Eval hnf in [eqMixin of group_type by <:].
Canonical group_eqType := Eval hnf in EqType group_type group_eqMixin.
Definition group_choiceMixin := [choiceMixin of group_type by <:].
Canonical group_choiceType :=
  Eval hnf in ChoiceType group_type group_choiceMixin.
Definition group_countMixin := [countMixin of group_type by <:].
Canonical group_countType := Eval hnf in CountType group_type group_countMixin.
Canonical group_subCountType := Eval hnf in [subCountType of group_type].
Definition group_finMixin := [finMixin of group_type by <:].
Canonical group_finType := Eval hnf in FinType group_type group_finMixin.

Definition generated A := \bigcap_(G : groupT | A \subset G) G.
Definition cycle x := generated [set x].

End GroupSetMulProp.

Notation "{ 'group' gT }" := (group_of (Phant gT))
  (at level 0, format "{ 'group'  gT }") : type_scope.
Notation "<[ x ] >"  := (cycle x) : group_scope.

Module Export perm.
Import mathcomp.ssreflect.fintype.

Section PermDefSection.

Variable T : finType.

Inductive perm_type : predArgType :=
  Perm (pval : {ffun T -> T}) & injectiveb pval.
Definition pval p := let: Perm f _ := p in f.
Definition perm_of of phant T := perm_type.

Canonical perm_subType := Eval hnf in [subType for pval].
Definition perm_eqMixin := Eval hnf in [eqMixin of perm_type by <:].
Canonical perm_eqType := Eval hnf in EqType perm_type perm_eqMixin.
Definition perm_choiceMixin := [choiceMixin of perm_type by <:].
Canonical perm_choiceType := Eval hnf in ChoiceType perm_type perm_choiceMixin.
Definition perm_countMixin := [countMixin of perm_type by <:].
Canonical perm_countType := Eval hnf in CountType perm_type perm_countMixin.
Canonical perm_subCountType := Eval hnf in [subCountType of perm_type].
Definition perm_finMixin := [finMixin of perm_type by <:].
Canonical perm_finType := Eval hnf in FinType perm_type perm_finMixin.

Lemma perm_proof (f : T -> T) : injective f -> injectiveb (finfun f).
admit.
Defined.

End PermDefSection.

Notation "{ 'perm' T }" := (perm_of (Phant T))
  (at level 0, format "{ 'perm'  T }") : type_scope.

Notation "''S_' n" := {perm 'I_n}
  (at level 8, n at level 2, format "''S_' n").

Local Notation fun_of_perm_def := (fun T (u : perm_type T) => val u : T -> T).
Local Notation perm_def := (fun T f injf => Perm (@perm_proof T f injf)).

Module Type PermDefSig.
Parameter fun_of_perm : forall T, perm_type T -> T -> T.
Parameter perm : forall (T : finType) (f : T -> T), injective f -> {perm T}.
End PermDefSig.

Module PermDef : PermDefSig.
Definition fun_of_perm := fun_of_perm_def.
Definition perm := perm_def.
End PermDef.

Notation fun_of_perm := PermDef.fun_of_perm.
Notation perm := (@PermDef.perm _ _).
Coercion fun_of_perm : perm_type >-> Funclass.

Section Theory.

Variable T : finType.
Implicit Types (x y : T) (s t : {perm T}) (S : {set T}).

Lemma perm_inj {s} : injective s.
admit.
Defined.

Lemma perm_onto s : codom s =i predT.
admit.
Defined.

Definition perm_one := perm (@inj_id T).

Lemma perm_invK s : cancel (fun x => iinv (perm_onto s x)) s.
admit.
Defined.

Definition perm_inv s := perm (can_inj (perm_invK s)).

Definition perm_mul s t := perm (inj_comp (@perm_inj t) (@perm_inj s)).

Lemma perm_oneP : left_id perm_one perm_mul.
admit.
Defined.

Lemma perm_invP : left_inverse perm_one perm_inv perm_mul.
admit.
Defined.

Lemma perm_mulP : associative perm_mul.
admit.
Defined.

Definition perm_of_baseFinGroupMixin : FinGroup.mixin_of (perm_type T) :=
  FinGroup.Mixin perm_mulP perm_oneP perm_invP.
Canonical perm_baseFinGroupType :=
  Eval hnf in BaseFinGroupType (perm_type T) perm_of_baseFinGroupMixin.
Canonical perm_finGroupType := @FinGroupType perm_baseFinGroupType perm_invP.

Lemma tperm_proof x y : involutive [fun z => z with x |-> y, y |-> x].
admit.
Defined.

Definition tperm x y := perm (can_inj (tperm_proof x y)).

End Theory.

Section PermutationParity.

Variable T : finType.

Implicit Types (s t u v : {perm T}) (x y z a b : T).

Definition aperm x s := s x.
Definition porbit s x := aperm x @: <[s]>.
Definition porbits s := porbit s @: T.
Definition odd_perm (s : perm_type T) := odd #|T| (+) odd #|porbits s|.

End PermutationParity.

Coercion odd_perm : perm_type >-> bool.

End perm.

Section ZpDef.

Variable p' : nat.
Local Notation p := p'.+1.

Implicit Types x y z : 'I_p.

Definition inZp i := Ordinal (ltn_pmod i (ltn0Sn p')).

Definition Zp0 : 'I_p := ord0.
Definition Zp_opp x := inZp (p - x).
Definition Zp_add x y := inZp (x + y).

Lemma Zp_add0z : left_id Zp0 Zp_add.
admit.
Defined.

Lemma Zp_addNz : left_inverse Zp0 Zp_opp Zp_add.
admit.
Defined.

Lemma Zp_addA : associative Zp_add.
admit.
Defined.

Lemma Zp_addC : commutative Zp_add.
admit.
Defined.

Definition Zp_zmodMixin := ZmodMixin Zp_addA Zp_addC Zp_add0z Zp_addNz.
Canonical Zp_zmodType := Eval hnf in ZmodType 'I_p Zp_zmodMixin.

End ZpDef.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Reserved Notation "''M_' n"     (at level 8, n at level 2, format "''M_' n").
Reserved Notation "''rV_' n"    (at level 8, n at level 2, format "''rV_' n").

Reserved Notation "''M_' ( m , n )" (at level 8, format "''M_' ( m ,  n )").
Reserved Notation "''M[' R ]_ n"    (at level 8, n at level 2).

Reserved Notation "''rV[' R ]_ n"   (at level 8, n at level 2).

Reserved Notation "''M[' R ]_ ( m , n )" (at level 8).
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

Reserved Notation "\row_ j E"
  (at level 36, E at level 36, j at level 2,
   format "\row_ j  E").
Reserved Notation "\row_ ( j < n ) E"
  (at level 36, E at level 36, j, n at level 50).

Reserved Notation "x %:M"   (at level 8, format "x %:M").
Reserved Notation "A *m B" (at level 40, left associativity, format "A  *m  B").
Reserved Notation "\det A"  (at level 10, A at level 8, format "\det  A").
Reserved Notation "\adj A"  (at level 10, A at level 8, format "\adj  A").

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

Definition fun_of_matrix A (i : 'I_m) (j : 'I_n) := mx_val A (i, j).

Coercion fun_of_matrix : matrix >-> Funclass.

End MatrixDef.

Notation "''M[' R ]_ ( m , n )" := (matrix R m n) (only parsing): type_scope.
Notation "''rV[' R ]_ n" := 'M[R]_(1, n) (only parsing) : type_scope.
Notation "''M[' R ]_ n" := 'M[R]_(n, n) (only parsing) : type_scope.
Notation "''M_' ( m , n )" := 'M[_]_(m, n) : type_scope.
Notation "''rV_' n" := 'M_(1, n) : type_scope.
Notation "''M_' n" := 'M_(n, n) : type_scope.

Notation "\matrix[ k ]_ ( i , j ) E" := (matrix_of_fun k (fun i j => E)) :
   ring_scope.

Notation "\matrix_ ( i < m , j < n ) E" :=
  (@matrix_of_fun _ m n matrix_key (fun i j => E)) (only parsing) : ring_scope.

Notation "\matrix_ ( i , j ) E" := (\matrix_(i < _, j < _) E) : ring_scope.

Notation "\matrix_ ( i < m ) E" :=
  (\matrix_(i < m, j < _) @fun_of_matrix _ 1 _ E 0 j)
  (only parsing) : ring_scope.

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

Section MatrixStructural.

Variable R : Type.

Fact const_mx_key : unit.
admit.
Defined.
Definition const_mx m n a : 'M[R]_(m, n) := \matrix[const_mx_key]_(i, j) a.

Section FixedDim.

Variables m n : nat.
Implicit Type A : 'M[R]_(m, n).

Definition castmx m' n' (eq_mn : (m = m') * (n = n')) A : 'M_(m', n') :=
  let: erefl in _ = m' := eq_mn.1 return 'M_(m', n') in
  let: erefl in _ = n' := eq_mn.2 return 'M_(m, n') in A.

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

Definition row' i0 A := \matrix_(i, j) A (lift i0 i) j.
Definition col' j0 A := \matrix_(i, j) A i (lift j0 j).

End FixedDim.

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

End CutPaste.

Section Block.

Variables m1 m2 n1 n2 : nat.

Definition block_mx Aul Aur Adl Adr : 'M_(m1 + m2, n1 + n2) :=
  col_mx (row_mx Aul Aur) (row_mx Adl Adr).

Section CutBlock.

Variable A : matrix R (m1 + m2) (n1 + n2).
Definition ursubmx := rsubmx (usubmx A).
Definition dlsubmx := lsubmx (dsubmx A).
Definition drsubmx := rsubmx (dsubmx A).

End CutBlock.

End Block.

Section VecMatrix.

Variables m n : nat.

Lemma mxvec_cast : #|{:'I_m * 'I_n}| = (m * n)%N.
admit.
Defined.

Definition mxvec_index (i : 'I_m) (j : 'I_n) :=
  cast_ord mxvec_cast (enum_rank (i, j)).

Definition mxvec (A : 'M[R]_(m, n)) :=
  castmx (erefl _, mxvec_cast) (\row_k A (enum_val k).1 (enum_val k).2).

Fact vec_mx_key : unit.
admit.
Defined.
Definition vec_mx (u : 'rV[R]_(m * n)) :=
  \matrix[vec_mx_key]_(i, j) u 0 (mxvec_index i j).

End VecMatrix.

End MatrixStructural.

Arguments const_mx {R m n}.

Section MapMatrix.

Variables (aT rT : Type) (f : aT -> rT).

Fact map_mx_key : unit.
admit.
Defined.
Definition map_mx m n (A : 'M_(m, n)) := \matrix[map_mx_key]_(i, j) f (A i j).

End MapMatrix.

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

End FixedDim.

End MatrixZmodule.

Section MatrixAlgebra.

Variable R : ringType.

Section RingModule.

Variables m n : nat.
Implicit Types A B : 'M[R]_(m, n).

Fact scalemx_key : unit.
admit.
Defined.
Definition scalemx x A := \matrix[scalemx_key]_(i, j) (x * A i j).

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

End RingModule.

Section ScalarMx.

Variable n : nat.

Fact scalar_mx_key : unit.
admit.
Defined.
Definition scalar_mx x : 'M[R]_n :=
  \matrix[scalar_mx_key]_(i , j) (x *+ (i == j)).

End ScalarMx.

Notation "x %:M" := (scalar_mx _ x) : ring_scope.

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

Lemma mulmxDl m n p (A1 A2 : 'M_(m, n)) (B : 'M_(n, p)) :
  (A1 + A2) *m B = A1 *m B + A2 *m B.
admit.
Defined.

Lemma mulmxDr m n p (A : 'M_(m, n)) (B1 B2 : 'M_(n, p)) :
  A *m (B1 + B2) = A *m B1 + A *m B2.
admit.
Defined.

Lemma mul1mx m n (A : 'M_(m, n)) : 1%:M *m A = A.
admit.
Defined.

Lemma mulmx1 m n (A : 'M_(m, n)) : A *m 1%:M = A.
admit.
Defined.

Fact pid_mx_key : unit.
admit.
Defined.
Definition pid_mx {m n} r : 'M[R]_(m, n) :=
  \matrix[pid_mx_key]_(i, j) ((i == j :> nat) && (i < r))%:R.

Definition copid_mx {n} r : 'M_n := 1%:M - pid_mx r.

Section Trace.

Variable n : nat.

Definition mxtrace (A : 'M[R]_n) := \sum_i A i i.

End Trace.

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

End MatrixRing.

Definition determinant n (A : 'M_n) : R :=
  \sum_(s : 'S_n) (-1) ^+ s * \prod_i A i (s i).

Definition cofactor n A (i j : 'I_n) : R :=
  (-1) ^+ (i + j) * determinant (row' i (col' j A)).

Fact adjugate_key : unit.
admit.
Defined.
Definition adjugate n (A : 'M_n) := \matrix[adjugate_key]_(i, j) cofactor A j i.

End MatrixAlgebra.
Arguments scalar_mx {R n}.
Arguments pid_mx {R m n}.
Arguments copid_mx {R n}.
Prenex Implicits mulmx mxtrace determinant cofactor adjugate.

Notation "a %:M" := (scalar_mx a) : ring_scope.
Notation "A *m B" := (mulmx A B) : ring_scope.
Notation "'\det' A" := (determinant A) : ring_scope.
Notation "'\adj' A" := (adjugate A) : ring_scope.

Section CommMx.

Context {R : ringType} {n : nat}.
Implicit Types (f g p : 'M[R]_n) (fs : seq 'M[R]_n) (d : 'rV[R]_n) (I : Type).

Definition comm_mx  f g : Prop := f *m g =  g *m f.

End CommMx.

Section ComMatrix.

Variable R : comRingType.

Lemma comm_mx_scalar n a (A : 'M[R]_n) : comm_mx A a%:M.
admit.
Defined.

End ComMatrix.
Arguments comm_mx_scalar {R n}.

Section MatrixInv.

Variables R : comUnitRingType.

Section Defs.

Variable n : nat.

Definition unitmx : pred 'M[R]_n := fun A => \det A \is a GRing.unit.
Definition invmx A := if A \in unitmx then (\det A)^-1 *: \adj A else A.

Lemma mulVmx : {in unitmx, left_inverse 1%:M invmx mulmx}.
admit.
Defined.

Lemma mulmxV : {in unitmx, right_inverse 1%:M invmx mulmx}.
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

End MatrixInv.

Declare Scope matrix_set_scope.

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
