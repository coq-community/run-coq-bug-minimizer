
(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "-projection-no-head-constant" "-w" "-redundant-canonical-projection" "-w" "-notation-overridden" "-w" "-deprecated-native-compiler-option" "-native-compiler" "ondemand" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/oddorder/theories" "odd_order" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/HB" "HB" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/elpi" "elpi" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/mathcomp" "mathcomp" "-top" "Top.bug_01") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 1375 lines to 60 lines, then from 73 lines to 1675 lines, then from 1680 lines to 90 lines, then from 103 lines to 2712 lines, then from 2715 lines to 148 lines, then from 161 lines to 2932 lines, then from 2936 lines to 147 lines, then from 160 lines to 1746 lines, then from 1749 lines to 189 lines, then from 202 lines to 1254 lines, then from 1259 lines to 145 lines, then from 158 lines to 976 lines, then from 981 lines to 153 lines, then from 166 lines to 775 lines, then from 779 lines to 245 lines, then from 239 lines to 175 lines, then from 188 lines to 604 lines, then from 609 lines to 168 lines, then from 181 lines to 1580 lines, then from 1585 lines to 231 lines, then from 244 lines to 1254 lines, then from 1259 lines to 261 lines, then from 274 lines to 1855 lines, then from 1859 lines to 261 lines, then from 274 lines to 3310 lines, then from 3315 lines to 2052 lines, then from 1806 lines to 484 lines, then from 497 lines to 2159 lines, then from 2164 lines to 571 lines, then from 584 lines to 3152 lines, then from 3155 lines to 2910 lines, then from 2767 lines to 646 lines, then from 659 lines to 3393 lines, then from 3398 lines to 3162 lines, then from 3016 lines to 743 lines, then from 756 lines to 1264 lines, then from 1269 lines to 933 lines, then from 879 lines to 827 lines, then from 840 lines to 1556 lines, then from 1561 lines to 927 lines, then from 940 lines to 3367 lines, then from 3371 lines to 3182 lines, then from 2982 lines to 1060 lines, then from 1073 lines to 2149 lines, then from 2154 lines to 1882 lines, then from 1841 lines to 1076 lines, then from 1089 lines to 1786 lines, then from 1791 lines to 1392 lines, then from 1283 lines to 1245 lines, then from 1258 lines to 5992 lines, then from 5997 lines to 6156 lines, then from 5898 lines to 2800 lines *)
(* coqc version 8.19+alpha compiled with OCaml 4.14.1
   coqtop version 728713d43dde:/builds/coq/coq/_build/default,(HEAD detached at 25e3b11) (25e3b11cee094cfce7e16d10e58d3b7b318ea70c)
   Expected coqc runtime on this file: 5.802 sec *)
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

Module Export AdmitTactic.
Module Import LocalFalse.
Inductive False : Prop := .
End LocalFalse.
Axiom proof_admitted : False.
Import Coq.Init.Ltac.
Tactic Notation "admit" := abstract case proof_admitted.
End AdmitTactic.
Module Export mathcomp_DOT_ssreflect_DOT_seq_WRAPPED.
Module Export seq.

Import HB.structures.
Import mathcomp.ssreflect.ssreflect.
Import mathcomp.ssreflect.ssrfun.
Import mathcomp.ssreflect.ssrbool.
Import mathcomp.ssreflect.eqtype.
Import mathcomp.ssreflect.ssrnat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope seq_scope.

Reserved Notation "[ '<->' P0 ; P1 ; .. ; Pn ]"
  (at level 0, format "[ '<->' '['  P0 ;  '/' P1 ;  '/'  .. ;  '/'  Pn ']' ]").

Delimit Scope seq_scope with SEQ.
Open Scope seq_scope.

Notation seq := list.
Bind Scope seq_scope with list.
Arguments cons {T%type} x s%SEQ : rename.
Arguments nil {T%type} : rename.
Notation Cons T := (@cons T) (only parsing).
Notation Nil T := (@nil T) (only parsing).

Infix "::" := cons : seq_scope.

Notation "[ :: ]" := nil (at level 0, format "[ :: ]") : seq_scope.

Notation "[ :: x1 ]" := (x1 :: [::])
  (at level 0, format "[ ::  x1 ]") : seq_scope.

Notation "[ :: x & s ]" := (x :: s) (at level 0, only parsing) : seq_scope.

Notation "[ :: x1 , x2 , .. , xn & s ]" := (x1 :: x2 :: .. (xn :: s) ..)
  (at level 0, format
  "'[hv' [ :: '['  x1 , '/'  x2 , '/'  .. , '/'  xn ']' '/ '  &  s ] ']'"
  ) : seq_scope.

Notation "[ :: x1 ; x2 ; .. ; xn ]" := (x1 :: x2 :: .. [:: xn] ..)
  (at level 0, format "[ :: '['  x1 ; '/'  x2 ; '/'  .. ; '/'  xn ']' ]"
  ) : seq_scope.

Section Sequences.

Variable n0 : nat.

Variable T : Type.

Variable x0 : T.

Implicit Types x y z : T.
Implicit Types m n : nat.
Implicit Type s : seq T.

Fixpoint size s := if s is _ :: s' then (size s').+1 else 0.

Lemma size0nil s : size s = 0 -> s = [::].
Admitted.

Definition nilp s := size s == 0.

Lemma nilP s : reflect (s = [::]) (nilp s).
admit.
Defined.

Definition ohead s := if s is x :: _ then Some x else None.
Definition head s := if s is x :: _ then x else x0.

Definition behead s := if s is _ :: s' then s' else [::].

Lemma size_behead s : size (behead s) = (size s).-1.
Admitted.

Definition ncons n x := iter n (cons x).
Definition nseq n x := ncons n x [::].

Lemma size_ncons n x s : size (ncons n x s) = n + size s.
Admitted.

Lemma size_nseq n x : size (nseq n x) = n.
Admitted.

Fixpoint seqn_type n := if n is n'.+1 then T -> seqn_type n' else seq T.

Fixpoint seqn_rec f n : seqn_type n :=
  if n is n'.+1 return seqn_type n then
    fun x => seqn_rec (fun s => f (x :: s)) n'
  else f [::].
Definition seqn := seqn_rec id.

Fixpoint cat s1 s2 := if s1 is x :: s1' then x :: s1' ++ s2 else s2
where "s1 ++ s2" := (cat s1 s2) : seq_scope.

Lemma cat0s s : [::] ++ s = s.
Admitted.
Lemma cat1s x s : [:: x] ++ s = x :: s.
Admitted.
Lemma cat_cons x s1 s2 : (x :: s1) ++ s2 = x :: s1 ++ s2.
Admitted.

Lemma cat_nseq n x s : nseq n x ++ s = ncons n x s.
Admitted.

Lemma nseqD n1 n2 x : nseq (n1 + n2) x = nseq n1 x ++ nseq n2 x.
Admitted.

Lemma cats0 s : s ++ [::] = s.
Admitted.

Lemma catA s1 s2 s3 : s1 ++ s2 ++ s3 = (s1 ++ s2) ++ s3.
Admitted.

Lemma size_cat s1 s2 : size (s1 ++ s2) = size s1 + size s2.
Admitted.

Lemma cat_nilp s1 s2 : nilp (s1 ++ s2) = nilp s1 && nilp s2.
Admitted.

Fixpoint rcons s z := if s is x :: s' then x :: rcons s' z else [:: z].

Lemma rcons_cons x s z : rcons (x :: s) z = x :: rcons s z.
Admitted.

Lemma cats1 s z : s ++ [:: z] = rcons s z.
Admitted.

Fixpoint last x s := if s is x' :: s' then last x' s' else x.
Fixpoint belast x s := if s is x' :: s' then x :: (belast x' s') else [::].

Lemma lastI x s : x :: s = rcons (belast x s) (last x s).
Admitted.

Lemma last_cons x y s : last x (y :: s) = last y s.
Admitted.

Lemma size_rcons s x : size (rcons s x) = (size s).+1.
Admitted.

Lemma size_belast x s : size (belast x s) = size s.
Admitted.

Lemma last_cat x s1 s2 : last x (s1 ++ s2) = last (last x s1) s2.
Admitted.

Lemma last_rcons x s z : last x (rcons s z) = z.
Admitted.

Lemma belast_cat x s1 s2 :
  belast x (s1 ++ s2) = belast x s1 ++ belast (last x s1) s2.
Admitted.

Lemma belast_rcons x s z : belast x (rcons s z) = x :: s.
Admitted.

Lemma cat_rcons x s1 s2 : rcons s1 x ++ s2 = s1 ++ x :: s2.
Admitted.

Lemma rcons_cat x s1 s2 : rcons (s1 ++ s2) x = s1 ++ rcons s2 x.
Admitted.

Variant last_spec : seq T -> Type :=
  | LastNil        : last_spec [::]
  | LastRcons s x  : last_spec (rcons s x).

Lemma lastP s : last_spec s.
Admitted.

Lemma last_ind P :
  P [::] -> (forall s x, P s -> P (rcons s x)) -> forall s, P s.
Admitted.

Fixpoint nth s n {struct n} :=
  if s is x :: s' then if n is n'.+1 then @nth s' n' else x else x0.

Fixpoint set_nth s n y {struct n} :=
  if s is x :: s' then if n is n'.+1 then x :: @set_nth s' n' y else y :: s'
  else ncons n x0 [:: y].

Lemma nth0 s : nth s 0 = head s.
Admitted.

Lemma nth_default s n : size s <= n -> nth s n = x0.
Admitted.

Lemma if_nth s b n : b || (size s <= n) ->
  (if b then nth s n else x0) = nth s n.
Admitted.

Lemma nth_nil n : nth [::] n = x0.
Admitted.

Lemma nth_seq1 n x : nth [:: x] n = if n == 0 then x else x0.
Admitted.

Lemma last_nth x s : last x s = nth (x :: s) (size s).
Admitted.

Lemma nth_last s : nth s (size s).-1 = last x0 s.
Admitted.

Lemma nth_behead s n : nth (behead s) n = nth s n.+1.
Admitted.

Lemma nth_cat s1 s2 n :
  nth (s1 ++ s2) n = if n < size s1 then nth s1 n else nth s2 (n - size s1).
Admitted.

Lemma nth_rcons s x n :
  nth (rcons s x) n =
    if n < size s then nth s n else if n == size s then x else x0.
Admitted.

Lemma nth_rcons_default s i : nth (rcons s x0) i = nth s i.
Admitted.

Lemma nth_ncons m x s n :
  nth (ncons m x s) n = if n < m then x else nth s (n - m).
Admitted.

Lemma nth_nseq m x n : nth (nseq m x) n = (if n < m then x else x0).
Admitted.

Lemma eq_from_nth s1 s2 :
    size s1 = size s2 -> (forall i, i < size s1 -> nth s1 i = nth s2 i) ->
  s1 = s2.
Admitted.

Lemma size_set_nth s n y : size (set_nth s n y) = maxn n.+1 (size s).
Admitted.

Lemma set_nth_nil n y : set_nth [::] n y = ncons n x0 [:: y].
Admitted.

Lemma nth_set_nth s n y : nth (set_nth s n y) =1 [eta nth s with n |-> y].
Admitted.

Lemma set_set_nth s n1 y1 n2 y2 (s2 := set_nth s n2 y2) :
  set_nth (set_nth s n1 y1) n2 y2 = if n1 == n2 then s2 else set_nth s2 n1 y1.
Admitted.

Section SeqFind.

Variable a : pred T.

Fixpoint find s := if s is x :: s' then if a x then 0 else (find s').+1 else 0.

Fixpoint filter s :=
  if s is x :: s' then if a x then x :: filter s' else filter s' else [::].

Fixpoint count s := if s is x :: s' then a x + count s' else 0.

Fixpoint has s := if s is x :: s' then a x || has s' else false.

Fixpoint all s := if s is x :: s' then a x && all s' else true.

Lemma size_filter s : size (filter s) = count s.
Admitted.

Lemma has_count s : has s = (0 < count s).
Admitted.

Lemma count_size s : count s <= size s.
Admitted.

Lemma all_count s : all s = (count s == size s).
Admitted.

Lemma filter_all s : all (filter s).
Admitted.

Lemma all_filterP s : reflect (filter s = s) (all s).
admit.
Defined.

Lemma filter_id s : filter (filter s) = filter s.
Admitted.

Lemma has_find s : has s = (find s < size s).
Admitted.

Lemma find_size s : find s <= size s.
Admitted.

Lemma find_cat s1 s2 :
  find (s1 ++ s2) = if has s1 then find s1 else size s1 + find s2.
Admitted.

Lemma has_nil : has [::] = false.
Admitted.

Lemma has_seq1 x : has [:: x] = a x.
Admitted.

Lemma has_nseq n x : has (nseq n x) = (0 < n) && a x.
Admitted.

Lemma has_seqb (b : bool) x : has (nseq b x) = b && a x.
Admitted.

Lemma all_nil : all [::] = true.
Admitted.

Lemma all_seq1 x : all [:: x] = a x.
Admitted.

Lemma all_nseq n x : all (nseq n x) = (n == 0) || a x.
Admitted.

Lemma all_nseqb (b : bool) x : all (nseq b x) = b ==> a x.
Admitted.

Lemma filter_nseq n x : filter (nseq n x) = nseq (a x * n) x.
Admitted.

Lemma count_nseq n x : count (nseq n x) = a x * n.
Admitted.

Lemma find_nseq n x : find (nseq n x) = ~~ a x * n.
Admitted.

Lemma nth_find s : has s -> a (nth s (find s)).
Admitted.

Lemma before_find s i : i < find s -> a (nth s i) = false.
Admitted.

Lemma hasNfind s : ~~ has s -> find s = size s.
Admitted.

Lemma filter_cat s1 s2 : filter (s1 ++ s2) = filter s1 ++ filter s2.
Admitted.

Lemma filter_rcons s x :
  filter (rcons s x) = if a x then rcons (filter s) x else filter s.
Admitted.

Lemma count_cat s1 s2 : count (s1 ++ s2) = count s1 + count s2.
Admitted.

Lemma has_cat s1 s2 : has (s1 ++ s2) = has s1 || has s2.
Admitted.

Lemma has_rcons s x : has (rcons s x) = a x || has s.
Admitted.

Lemma all_cat s1 s2 : all (s1 ++ s2) = all s1 && all s2.
Admitted.

Lemma all_rcons s x : all (rcons s x) = a x && all s.
Admitted.

End SeqFind.

Lemma find_pred0 s : find pred0 s = size s.
Admitted.

Lemma find_predT s : find predT s = 0.
Admitted.

Lemma eq_find a1 a2 : a1 =1 a2 -> find a1 =1 find a2.
Admitted.

Lemma eq_filter a1 a2 : a1 =1 a2 -> filter a1 =1 filter a2.
Admitted.

Lemma eq_count a1 a2 : a1 =1 a2 -> count a1 =1 count a2.
Admitted.

Lemma eq_has a1 a2 : a1 =1 a2 -> has a1 =1 has a2.
Admitted.

Lemma eq_all a1 a2 : a1 =1 a2 -> all a1 =1 all a2.
Admitted.

Lemma all_filter (p q : pred T) xs :
  all p (filter q xs) = all [pred i | q i ==> p i] xs.
Admitted.

Section SubPred.

Variable (a1 a2 : pred T).
Hypothesis s12 : subpred a1 a2.

Lemma sub_find s : find a2 s <= find a1 s.
Admitted.

Lemma sub_has s : has a1 s -> has a2 s.
Admitted.

Lemma sub_count s : count a1 s <= count a2 s.
Admitted.

Lemma sub_all s : all a1 s -> all a2 s.
Admitted.

End SubPred.

Lemma filter_pred0 s : filter pred0 s = [::].
Admitted.

Lemma filter_predT s : filter predT s = s.
Admitted.

Lemma filter_predI a1 a2 s : filter (predI a1 a2) s = filter a1 (filter a2 s).
Admitted.

Lemma count_pred0 s : count pred0 s = 0.
Admitted.

Lemma count_predT s : count predT s = size s.
Admitted.

Lemma count_predUI a1 a2 s :
  count (predU a1 a2) s + count (predI a1 a2) s = count a1 s + count a2 s.
Admitted.

Lemma count_predC a s : count a s + count (predC a) s = size s.
Admitted.

Lemma count_filter a1 a2 s : count a1 (filter a2 s) = count (predI a1 a2) s.
Admitted.

Lemma has_pred0 s : has pred0 s = false.
Admitted.

Lemma has_predT s : has predT s = (0 < size s).
Admitted.

Lemma has_predC a s : has (predC a) s = ~~ all a s.
Admitted.

Lemma has_predU a1 a2 s : has (predU a1 a2) s = has a1 s || has a2 s.
Admitted.

Lemma all_pred0 s : all pred0 s = (size s == 0).
Admitted.

Lemma all_predT s : all predT s.
Admitted.

Lemma allT (a : pred T) s : (forall x, a x) -> all a s.
Admitted.

Lemma all_predC a s : all (predC a) s = ~~ has a s.
Admitted.

Lemma all_predI a1 a2 s : all (predI a1 a2) s = all a1 s && all a2 s.
Admitted.

Fixpoint drop n s {struct s} :=
  match s, n with
  | _ :: s', n'.+1 => drop n' s'
  | _, _ => s
  end.

Lemma drop_behead : drop n0 =1 iter n0 behead.
Admitted.

Lemma drop0 s : drop 0 s = s.
Admitted.

Lemma drop1 : drop 1 =1 behead.
Admitted.

Lemma drop_oversize n s : size s <= n -> drop n s = [::].
Admitted.

Lemma drop_size s : drop (size s) s = [::].
Admitted.

Lemma drop_cons x s :
  drop n0 (x :: s) = if n0 is n.+1 then drop n s else x :: s.
Admitted.

Lemma size_drop s : size (drop n0 s) = size s - n0.
Admitted.

Lemma drop_cat s1 s2 :
  drop n0 (s1 ++ s2) =
    if n0 < size s1 then drop n0 s1 ++ s2 else drop (n0 - size s1) s2.
Admitted.

Lemma drop_size_cat n s1 s2 : size s1 = n -> drop n (s1 ++ s2) = s2.
Admitted.

Lemma nconsK n x : cancel (ncons n x) (drop n).
Admitted.

Lemma drop_drop s n1 n2 : drop n1 (drop n2 s) = drop (n1 + n2) s.
Admitted.

Fixpoint take n s {struct s} :=
  match s, n with
  | x :: s', n'.+1 => x :: take n' s'
  | _, _ => [::]
  end.

Lemma take0 s : take 0 s = [::].
Admitted.

Lemma take_oversize n s : size s <= n -> take n s = s.
Admitted.

Lemma take_size s : take (size s) s = s.
Admitted.

Lemma take_cons x s :
  take n0 (x :: s) = if n0 is n.+1 then x :: (take n s) else [::].
Admitted.

Lemma drop_rcons s : n0 <= size s ->
  forall x, drop n0 (rcons s x) = rcons (drop n0 s) x.
Admitted.

Lemma cat_take_drop s : take n0 s ++ drop n0 s = s.
Admitted.

Lemma size_takel s : n0 <= size s -> size (take n0 s) = n0.
Admitted.

Lemma size_take s : size (take n0 s) = if n0 < size s then n0 else size s.
Admitted.

Lemma size_take_min s : size (take n0 s) = minn n0 (size s).
Admitted.

Lemma take_cat s1 s2 :
  take n0 (s1 ++ s2) =
    if n0 < size s1 then take n0 s1 else s1 ++ take (n0 - size s1) s2.
Admitted.

Lemma take_size_cat n s1 s2 : size s1 = n -> take n (s1 ++ s2) = s1.
Admitted.

Lemma takel_cat s1 s2 : n0 <= size s1 -> take n0 (s1 ++ s2) = take n0 s1.
Admitted.

Lemma nth_drop s i : nth (drop n0 s) i = nth s (n0 + i).
Admitted.

Lemma find_ltn p s i : has p (take i s) -> find p s < i.
Admitted.

Lemma has_take p s i : has p s -> has p (take i s) = (find p s < i).
Admitted.

Lemma has_take_leq (p : pred T) (s : seq T) i : i <= size s ->
  has p (take i s) = (find p s < i).
Admitted.

Lemma nth_take i : i < n0 -> forall s, nth (take n0 s) i = nth s i.
Admitted.

Lemma take_min i j s : take (minn i j) s = take i (take j s).
Admitted.

Lemma take_takel i j s : i <= j -> take i (take j s) = take i s.
Admitted.

Lemma take_taker i j s : j <= i -> take i (take j s) = take j s.
Admitted.

Lemma take_drop i j s : take i (drop j s) = drop j (take (i + j) s).
Admitted.

Lemma takeD i j s : take (i + j) s = take i s ++ take j (drop i s).
Admitted.

Lemma takeC i j s : take i (take j s) = take j (take i s).
Admitted.

Lemma take_nseq i j x : i <= j -> take i (nseq j x) = nseq i x.
Admitted.

Lemma drop_nseq i j x : drop i (nseq j x) = nseq (j - i) x.
Admitted.

Lemma drop_nth n s : n < size s -> drop n s = nth s n :: drop n.+1 s.
Admitted.

Lemma take_nth n s : n < size s -> take n.+1 s = rcons (take n s) (nth s n).
Admitted.

Definition rot n s := drop n s ++ take n s.

Lemma rot0 s : rot 0 s = s.
Admitted.

Lemma size_rot s : size (rot n0 s) = size s.
Admitted.

Lemma rot_oversize n s : size s <= n -> rot n s = s.
Admitted.

Lemma rot_size s : rot (size s) s = s.
Admitted.

Lemma has_rot s a : has a (rot n0 s) = has a s.
Admitted.

Lemma rot_size_cat s1 s2 : rot (size s1) (s1 ++ s2) = s2 ++ s1.
Admitted.

Definition rotr n s := rot (size s - n) s.

Lemma rotK : cancel (rot n0) (rotr n0).
Admitted.

Lemma rot_inj : injective (rot n0).
Admitted.

Fixpoint catrev s1 s2 := if s1 is x :: s1' then catrev s1' (x :: s2) else s2.

Definition rev s := catrev s [::].

Lemma catrev_catl s t u : catrev (s ++ t) u = catrev t (catrev s u).
Admitted.

Lemma catrev_catr s t u : catrev s (t ++ u) = catrev s t ++ u.
Admitted.

Lemma catrevE s t : catrev s t = rev s ++ t.
Admitted.

Lemma rev_cons x s : rev (x :: s) = rcons (rev s) x.
Admitted.

Lemma size_rev s : size (rev s) = size s.
Admitted.

Lemma rev_nilp s : nilp (rev s) = nilp s.
Admitted.

Lemma rev_cat s t : rev (s ++ t) = rev t ++ rev s.
Admitted.

Lemma rev_rcons s x : rev (rcons s x) = x :: rev s.
Admitted.

Lemma revK : involutive rev.
Admitted.

Lemma nth_rev n s : n < size s -> nth (rev s) n = nth s (size s - n.+1).
Admitted.

Lemma filter_rev a s : filter a (rev s) = rev (filter a s).
Admitted.

Lemma count_rev a s : count a (rev s) = count a s.
Admitted.

Lemma has_rev a s : has a (rev s) = has a s.
Admitted.

Lemma all_rev a s : all a (rev s) = all a s.
Admitted.

Lemma rev_nseq n x : rev (nseq n x) = nseq n x.
Admitted.

End Sequences.

Prenex Implicits size ncons nseq head ohead behead last rcons belast.
Arguments seqn {T} n.
Prenex Implicits cat take drop rot rotr catrev.
Prenex Implicits find count nth all has filter.
Arguments rev {T} s : simpl never.
Arguments nth : simpl nomatch.
Arguments set_nth : simpl nomatch.
Arguments take : simpl nomatch.
Arguments drop : simpl nomatch.

Arguments nilP {T s}.
Arguments all_filterP {T a s}.
Arguments rotK n0 {T} s : rename.
Arguments rot_inj {n0 T} [s1 s2] eq_rot_s12 : rename.
Arguments revK {T} s : rename.

Notation count_mem x := (count (pred_of_simpl (pred1 x))).

Infix "++" := cat : seq_scope.

Notation "[ 'seq' x <- s | C ]" := (filter (fun x => C%B) s)
 (at level 0, x at level 99,
  format "[ '[hv' 'seq'  x  <-  s '/ '  |  C ] ']'") : seq_scope.
Notation "[ 'seq' x <- s | C1 & C2 ]" := [seq x <- s | C1 && C2]
 (at level 0, x at level 99,
  format "[ '[hv' 'seq'  x  <-  s '/ '  |  C1 '/ '  &  C2 ] ']'") : seq_scope.
Notation "[ 'seq' ' x <- s | C ]" := (filter (fun x => C%B) s)
 (at level 0, x strict pattern,
  format "[ '[hv' 'seq'  ' x  <-  s '/ '  |  C ] ']'") : seq_scope.
Notation "[ 'seq' ' x <- s | C1 & C2 ]" := [seq x <- s | C1 && C2]
 (at level 0, x strict pattern,
  format "[ '[hv' 'seq'  ' x  <-  s '/ '  |  C1 '/ '  &  C2 ] ']'") : seq_scope.
Notation "[ 'seq' x : T <- s | C ]" := (filter (fun x : T => C%B) s)
 (at level 0, x at level 99, only parsing).
Notation "[ 'seq' x : T <- s | C1 & C2 ]" := [seq x : T <- s | C1 && C2]
 (at level 0, x at level 99, only parsing).

#[deprecated(since="mathcomp 1.16",
             note="Use take_takel or take_min instead")]
Notation take_take := take_takel.

Lemma seq_ind2 {S T} (P : seq S -> seq T -> Type) :
    P [::] [::] ->
    (forall x y s t, size s = size t -> P s t -> P (x :: s) (y :: t)) ->
  forall s t, size s = size t -> P s t.
Admitted.

Section FindSpec.
Variable (T : Type) (a : {pred T}) (s : seq T).

Variant find_spec : bool -> nat -> Type :=
| NotFound of ~~ has a s : find_spec false (size s)
| Found (i : nat) of i < size s & (forall x0, a (nth x0 s i)) &
  (forall x0 j, j < i -> a (nth x0 s j) = false) : find_spec true i.

Lemma findP : find_spec (has a s) (find a s).
Admitted.

End FindSpec.
Arguments findP {T}.

Section RotRcons.

Variable T : Type.
Implicit Types (x : T) (s : seq T).

Lemma rot1_cons x s : rot 1 (x :: s) = rcons s x.
Admitted.

Lemma rcons_inj s1 s2 x1 x2 :
  rcons s1 x1 = rcons s2 x2 :> seq T -> (s1, x1) = (s2, x2).
Admitted.

Lemma rcons_injl x : injective (rcons^~ x).
Admitted.

Lemma rcons_injr s : injective (rcons s).
Admitted.

End RotRcons.

Arguments rcons_inj {T s1 x1 s2 x2} eq_rcons : rename.
Arguments rcons_injl {T} x [s1 s2] eq_rcons : rename.
Arguments rcons_injr {T} s [x1 x2] eq_rcons : rename.

Section EqSeq.

Variables (n0 : nat) (T : eqType) (x0 : T).
Local Notation nth := (nth x0).
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

Lemma eqseqE : eqseq = eq_op.
Admitted.

Lemma eqseq_cons x1 x2 s1 s2 :
  (x1 :: s1 == x2 :: s2) = (x1 == x2) && (s1 == s2).
Admitted.

Lemma eqseq_cat s1 s2 s3 s4 :
  size s1 = size s2 -> (s1 ++ s3 == s2 ++ s4) = (s1 == s2) && (s3 == s4).
Admitted.

Lemma eqseq_rcons s1 s2 x1 x2 :
  (rcons s1 x1 == rcons s2 x2) = (s1 == s2) && (x1 == x2).
Admitted.

Lemma size_eq0 s : (size s == 0) = (s == [::]).
Admitted.

Lemma nilpE s : nilp s = (s == [::]).
Admitted.

Lemma has_filter a s : has a s = (filter a s != [::]).
Admitted.

Fixpoint mem_seq (s : seq T) :=
  if s is y :: s' then xpredU1 y (mem_seq s') else xpred0.

Definition seq_eqclass := seq T.
Identity Coercion seq_of_eqclass : seq_eqclass >-> seq.
Coercion pred_of_seq (s : seq_eqclass) : {pred T}. exact (mem_seq s). Defined.

Canonical seq_predType := PredType (pred_of_seq : seq T -> pred T).

Canonical mem_seq_predType := PredType mem_seq.

Lemma in_cons y s x : (x \in y :: s) = (x == y) || (x \in s).
admit.
Defined.

Lemma in_nil x : (x \in [::]) = false.
Admitted.

Lemma mem_seq1 x y : (x \in [:: y]) = (x == y).
admit.
Defined.

Let inE := (mem_seq1, in_cons, inE).

Lemma forall_cons {P : T -> Prop} {a s} :
  {in a::s, forall x, P x} <-> P a /\ {in s, forall x, P x}.
admit.
Defined.

Lemma exists_cons {P : T -> Prop} {a s} :
  (exists2 x, x \in a::s & P x) <-> P a \/ exists2 x, x \in s & P x.
admit.
Defined.

Lemma mem_seq2 x y z : (x \in [:: y; z]) = xpred2 y z x.
Admitted.

Lemma mem_seq3 x y z t : (x \in [:: y; z; t]) = xpred3 y z t x.
Admitted.

Lemma mem_seq4 x y z t u : (x \in [:: y; z; t; u]) = xpred4 y z t u x.
Admitted.

Lemma mem_cat x s1 s2 : (x \in s1 ++ s2) = (x \in s1) || (x \in s2).
Admitted.

Lemma mem_rcons s y : rcons s y =i y :: s.
Admitted.

Lemma mem_head x s : x \in x :: s.
Admitted.

Lemma mem_last x s : last x s \in x :: s.
Admitted.

Lemma mem_behead s : {subset behead s <= s}.
Admitted.

Lemma mem_belast s y : {subset belast y s <= y :: s}.
Admitted.

Lemma mem_nth s n : n < size s -> nth s n \in s.
Admitted.

Lemma mem_take s x : x \in take n0 s -> x \in s.
Admitted.

Lemma mem_drop s x : x \in drop n0 s -> x \in s.
Admitted.

Lemma last_eq s z x y : x != y -> z != y -> (last x s == y) = (last z s == y).
Admitted.

Section Filters.

Implicit Type a : pred T.

Lemma hasP {a s} : reflect (exists2 x, x \in s & a x) (has a s).
admit.
Defined.

Lemma allP {a s} : reflect {in s, forall x, a x} (all a s).
admit.
Defined.

Lemma hasPn a s : reflect {in s, forall x, ~~ a x} (~~ has a s).
admit.
Defined.

Lemma allPn a s : reflect (exists2 x, x \in s & ~~ a x) (~~ all a s).
admit.
Defined.

Lemma allss s : all [in s] s.
Admitted.

Lemma mem_filter a x s : (x \in filter a s) = a x && (x \in s).
Admitted.

Variables (a : pred T) (s : seq T) (A : T -> Prop).
Hypothesis aP : forall x, reflect (A x) (a x).

Lemma hasPP : reflect (exists2 x, x \in s & A x) (has a s).
Admitted.

Lemma allPP : reflect {in s, forall x, A x} (all a s).
Admitted.

End Filters.

Notation "'has_ view" := (hasPP _ (fun _ => view))
  (at level 4, right associativity, format "''has_' view").
Notation "'all_ view" := (allPP _ (fun _ => view))
  (at level 4, right associativity, format "''all_' view").

Section EqIn.

Variables a1 a2 : pred T.

Lemma eq_in_filter s : {in s, a1 =1 a2} -> filter a1 s = filter a2 s.
Admitted.

Lemma eq_in_find s : {in s, a1 =1 a2} -> find a1 s = find a2 s.
Admitted.

Lemma eq_in_count s : {in s, a1 =1 a2} -> count a1 s = count a2 s.
Admitted.

Lemma eq_in_all s : {in s, a1 =1 a2} -> all a1 s = all a2 s.
Admitted.

Lemma eq_in_has s : {in s, a1 =1 a2} -> has a1 s = has a2 s.
Admitted.

End EqIn.

Lemma eq_has_r s1 s2 : s1 =i s2 -> has^~ s1 =1 has^~ s2.
Admitted.

Lemma eq_all_r s1 s2 : s1 =i s2 -> all^~ s1 =1 all^~ s2.
Admitted.

Lemma has_sym s1 s2 : has [in s1] s2 = has [in s2] s1.
Admitted.

Lemma has_pred1 x s : has (pred1 x) s = (x \in s).
Admitted.

Lemma mem_rev s : rev s =i s.
Admitted.

Definition constant s := if s is x :: s' then all (pred1 x) s' else true.

Lemma all_pred1P x s : reflect (s = nseq (size s) x) (all (pred1 x) s).
Admitted.

Lemma all_pred1_constant x s : all (pred1 x) s -> constant s.
Admitted.

Lemma all_pred1_nseq x n : all (pred1 x) (nseq n x).
Admitted.

Lemma mem_nseq n x y : (y \in nseq n x) = (0 < n) && (y == x).
Admitted.

Lemma nseqP n x y : reflect (y = x /\ n > 0) (y \in nseq n x).
admit.
Defined.

Lemma constant_nseq n x : constant (nseq n x).
Admitted.

Lemma constantP s : reflect (exists x, s = nseq (size s) x) (constant s).
Admitted.

Fixpoint uniq s := if s is x :: s' then (x \notin s') && uniq s' else true.

Lemma cons_uniq x s : uniq (x :: s) = (x \notin s) && uniq s.
Admitted.

Lemma cat_uniq s1 s2 :
  uniq (s1 ++ s2) = [&& uniq s1, ~~ has [in s1] s2 & uniq s2].
Admitted.

Lemma uniq_catC s1 s2 : uniq (s1 ++ s2) = uniq (s2 ++ s1).
Admitted.

Lemma uniq_catCA s1 s2 s3 : uniq (s1 ++ s2 ++ s3) = uniq (s2 ++ s1 ++ s3).
Admitted.

Lemma rcons_uniq s x : uniq (rcons s x) = (x \notin s) && uniq s.
Admitted.

Lemma filter_uniq s a : uniq s -> uniq (filter a s).
Admitted.

Lemma rot_uniq s : uniq (rot n0 s) = uniq s.
Admitted.

Lemma rev_uniq s : uniq (rev s) = uniq s.
Admitted.

Lemma count_memPn x s : reflect (count_mem x s = 0) (x \notin s).
admit.
Defined.

Lemma count_uniq_mem s x : uniq s -> count_mem x s = (x \in s).
Admitted.

Lemma leq_uniq_countP x s1 s2 : uniq s1 ->
  reflect (x \in s1 -> x \in s2) (count_mem x s1 <= count_mem x s2).
Admitted.

Lemma leq_uniq_count s1 s2 : uniq s1 -> {subset s1 <= s2} ->
  (forall x, count_mem x s1 <= count_mem x s2).
Admitted.

Lemma filter_pred1_uniq s x : uniq s -> x \in s -> filter (pred1 x) s = [:: x].
Admitted.

Fixpoint undup s :=
  if s is x :: s' then if x \in s' then undup s' else x :: undup s' else [::].

Lemma size_undup s : size (undup s) <= size s.
Admitted.

Lemma mem_undup s : undup s =i s.
Admitted.

Lemma undup_uniq s : uniq (undup s).
Admitted.

Lemma undup_id s : uniq s -> undup s = s.
Admitted.

Lemma ltn_size_undup s : (size (undup s) < size s) = ~~ uniq s.
Admitted.

Lemma filter_undup p s : filter p (undup s) = undup (filter p s).
Admitted.

Lemma undup_nil s : undup s = [::] -> s = [::].
Admitted.

Lemma undup_cat s t :
  undup (s ++ t) = [seq x <- undup s | x \notin t] ++ undup t.
Admitted.

Lemma undup_rcons s x : undup (rcons s x) = rcons [seq y <- undup s | y != x] x.
Admitted.

Lemma count_undup s p : count p (undup s) <= count p s.
Admitted.

Definition index x := find (pred1 x).

Lemma index_size x s : index x s <= size s.
Admitted.

Lemma index_mem x s : (index x s < size s) = (x \in s).
Admitted.

Lemma memNindex x s :  x \notin s -> index x s = size s.
Admitted.

Lemma nth_index x s : x \in s -> nth s (index x s) = x.
Admitted.

Lemma index_cat x s1 s2 :
 index x (s1 ++ s2) = if x \in s1 then index x s1 else size s1 + index x s2.
Admitted.

Lemma index_ltn x s i : x \in take i s -> index x s < i.
Admitted.

Lemma in_take x s i : x \in s -> (x \in take i s) = (index x s < i).
Admitted.

Lemma in_take_leq x s i : i <= size s -> (x \in take i s) = (index x s < i).
Admitted.

Lemma nthK s: uniq s -> {in gtn (size s), cancel (nth s) (index^~ s)}.
Admitted.

Lemma index_uniq i s : i < size s -> uniq s -> index (nth s i) s = i.
Admitted.

Lemma index_head x s : index x (x :: s) = 0.
Admitted.

Lemma index_last x s : uniq (x :: s) -> index (last x s) (x :: s) = size s.
Admitted.

Lemma nth_uniq s i j :
  i < size s -> j < size s -> uniq s -> (nth s i == nth s j) = (i == j).
Admitted.

Lemma uniqPn s :
  reflect (exists i j, [/\ i < j, j < size s & nth s i = nth s j]) (~~ uniq s).
admit.
Defined.

Lemma uniqP s : reflect {in gtn (size s) &, injective (nth s)} (uniq s).
admit.
Defined.

Lemma mem_rot s : rot n0 s =i s.
Admitted.

Lemma eqseq_rot s1 s2 : (rot n0 s1 == rot n0 s2) = (s1 == s2).
Admitted.

Lemma drop_index s (n := index x0 s) : x0 \in s -> drop n s = x0 :: drop n.+1 s.
Admitted.

Lemma index_pivot x s1 s2 (s := s1 ++ x :: s2) : x \notin s1 ->
  index x s = size s1.
Admitted.

Lemma take_pivot x s2 s1 (s := s1 ++ x :: s2) : x \notin s1 ->
  take (index x s) s = s1.
Admitted.

Lemma rev_pivot x s1 s2 : rev (s1 ++ x :: s2) = rev s2 ++ x :: rev s1.
Admitted.

Lemma eqseq_pivot2l x s1 s2 s3 s4 : x \notin s1 -> x \notin s3 ->
  (s1 ++ x :: s2 == s3 ++ x :: s4) = (s1 == s3) && (s2 == s4).
Admitted.

Lemma eqseq_pivot2r x s1 s2 s3 s4 : x \notin s2 -> x \notin s4 ->
  (s1 ++ x :: s2 == s3 ++ x :: s4) = (s1 == s3) && (s2 == s4).
Admitted.

Lemma eqseq_pivotl x s1 s2 s3 s4 : x \notin s1 -> x \notin s2 ->
  (s1 ++ x :: s2 == s3 ++ x :: s4) = (s1 == s3) && (s2 == s4).
Admitted.

Lemma eqseq_pivotr x s1 s2 s3 s4 : x \notin s3 -> x \notin s4 ->
  (s1 ++ x :: s2 == s3 ++ x :: s4) = (s1 == s3) && (s2 == s4).
Admitted.

Lemma uniq_eqseq_pivotl x s1 s2 s3 s4 : uniq (s1 ++ x :: s2) ->
  (s1 ++ x :: s2 == s3 ++ x :: s4) = (s1 == s3) && (s2 == s4).
Admitted.

Lemma uniq_eqseq_pivotr x s1 s2 s3 s4 : uniq (s3 ++ x :: s4) ->
  (s1 ++ x :: s2 == s3 ++ x :: s4) = (s1 == s3) && (s2 == s4).
Admitted.

End EqSeq.
Arguments eqseq : simpl nomatch.

Section RotIndex.
Variables (T : eqType).
Implicit Types x y z : T.

Lemma rot_index s x (i := index x s) : x \in s ->
  rot i s = x :: (drop i.+1 s ++ take i s).
Admitted.

Variant rot_to_spec s x := RotToSpec i s' of rot i s = x :: s'.

Lemma rot_to s x : x \in s -> rot_to_spec s x.
Admitted.

End RotIndex.

Definition inE := (mem_seq1, in_cons, inE).

Prenex Implicits mem_seq1 constant uniq undup index.

Arguments eqseq {T} !_ !_.
Arguments pred_of_seq {T} s x /.
Arguments eqseqP {T x y}.
Arguments hasP {T a s}.
Arguments hasPn {T a s}.
Arguments allP {T a s}.
Arguments allPn {T a s}.
Arguments nseqP {T n x y}.
Arguments count_memPn {T x s}.
Arguments uniqPn {T} x0 {s}.
Arguments uniqP {T} x0 {s}.
Arguments forall_cons {T P a s}.
Arguments exists_cons {T P a s}.

#[export] Hint Extern 0 (is_true (all _ _)) =>
  apply: (allss : forall T s, all (mem_seq s) s) : core.

Section NthTheory.

Lemma nthP (T : eqType) (s : seq T) x x0 :
  reflect (exists2 i, i < size s & nth x0 s i = x) (x \in s).
Admitted.

Variable T : Type.
Implicit Types (a : pred T) (x : T).

Lemma has_nthP a s x0 :
  reflect (exists2 i, i < size s & a (nth x0 s i)) (has a s).
Admitted.

Lemma all_nthP a s x0 :
  reflect (forall i, i < size s -> a (nth x0 s i)) (all a s).
Admitted.

Lemma set_nthE s x0 n x :
  set_nth x0 s n x = if n < size s
    then take n s ++ x :: drop n.+1 s
    else s ++ ncons (n - size s) x0 [:: x].
Admitted.

Lemma count_set_nth a s x0 n x :
  count a (set_nth x0 s n x) =
    count a s + a x - a (nth x0 s n) * (n < size s) + (a x0) * (n - size s).
Admitted.

Lemma count_set_nth_ltn a s x0 n x : n < size s ->
  count a (set_nth x0 s n x) = count a s + a x - a (nth x0 s n).
Admitted.

Lemma count_set_nthF a s x0 n x : ~~ a x0 ->
  count a (set_nth x0 s n x) = count a s + a x - a (nth x0 s n).
Admitted.

End NthTheory.

Lemma set_nth_default T s (y0 x0 : T) n : n < size s -> nth x0 s n = nth y0 s n.
Admitted.

Lemma headI T s (x : T) : rcons s x = head x s :: behead (rcons s x).
Admitted.

Arguments nthP {T s x}.
Arguments has_nthP {T a s}.
Arguments all_nthP {T a s}.

Definition bitseq := seq bool.
#[hnf] HB.instance Definition _ := Equality.on bitseq.
Canonical bitseq_predType := Eval hnf in [predType of bitseq].

Section FindNth.
Variables (T : Type).
Implicit Types (x : T) (p : pred T) (s : seq T).

Variant split_find_nth_spec p : seq T -> seq T -> seq T -> T -> Type :=
  FindNth x s1 s2 of p x & ~~ has p s1 :
    split_find_nth_spec p (rcons s1 x ++ s2) s1 s2 x.

Lemma split_find_nth x0 p s (i := find p s) :
  has p s -> split_find_nth_spec p s (take i s) (drop i.+1 s) (nth x0 s i).
Admitted.

Variant split_find_spec p : seq T -> seq T -> seq T -> Type :=
  FindSplit x s1 s2 of p x & ~~ has p s1 :
    split_find_spec p (rcons s1 x ++ s2) s1 s2.

Lemma split_find p s (i := find p s) :
  has p s -> split_find_spec p s (take i s) (drop i.+1 s).
Admitted.

Lemma nth_rcons_cat_find x0 p s1 s2 x (s := rcons s1 x ++ s2) :
   p x -> ~~ has p s1 -> nth x0 s (find p s) = x.
Admitted.

End FindNth.

Fixpoint incr_nth v i {struct i} :=
  if v is n :: v' then if i is i'.+1 then n :: incr_nth v' i' else n.+1 :: v'
  else ncons i 0 [:: 1].
Arguments incr_nth : simpl nomatch.

Lemma nth_incr_nth v i j : nth 0 (incr_nth v i) j = (i == j) + nth 0 v j.
Admitted.

Lemma size_incr_nth v i :
  size (incr_nth v i) = if i < size v then size v else i.+1.
Admitted.

Lemma incr_nth_inj v : injective (incr_nth v).
Admitted.

Lemma incr_nthC v i j :
  incr_nth (incr_nth v i) j = incr_nth (incr_nth v j) i.
Admitted.

Section PermSeq.

Variable T : eqType.
Implicit Type s : seq T.

Definition perm_eq s1 s2 :=
  all [pred x | count_mem x s1 == count_mem x s2] (s1 ++ s2).

Lemma permP s1 s2 : reflect (count^~ s1 =1 count^~ s2) (perm_eq s1 s2).
Admitted.

Lemma perm_refl s : perm_eq s s.
Admitted.
Hint Resolve perm_refl : core.

Lemma perm_sym : symmetric perm_eq.
Admitted.

Lemma perm_trans : transitive perm_eq.
Admitted.

Notation perm_eql s1 s2 := (perm_eq s1 =1 perm_eq s2).
Notation perm_eqr s1 s2 := (perm_eq^~ s1 =1 perm_eq^~ s2).

Lemma permEl s1 s2 : perm_eql s1 s2 -> perm_eq s1 s2.
Admitted.

Lemma permPl s1 s2 : reflect (perm_eql s1 s2) (perm_eq s1 s2).
Admitted.

Lemma permPr s1 s2 : reflect (perm_eqr s1 s2) (perm_eq s1 s2).
Admitted.

Lemma perm_catC s1 s2 : perm_eql (s1 ++ s2) (s2 ++ s1).
Admitted.

Lemma perm_cat2l s1 s2 s3 : perm_eq (s1 ++ s2) (s1 ++ s3) = perm_eq s2 s3.
Admitted.

Lemma perm_catl s t1 t2 : perm_eq t1 t2 -> perm_eql (s ++ t1) (s ++ t2).
Admitted.

Lemma perm_cons x s1 s2 : perm_eq (x :: s1) (x :: s2) = perm_eq s1 s2.
Admitted.

Lemma perm_cat2r s1 s2 s3 : perm_eq (s2 ++ s1) (s3 ++ s1) = perm_eq s2 s3.
Admitted.

Lemma perm_catr s1 s2 t : perm_eq s1 s2 -> perm_eql (s1 ++ t) (s2 ++ t).
Admitted.

Lemma perm_cat s1 s2 t1 t2 :
  perm_eq s1 s2 -> perm_eq t1 t2 -> perm_eq (s1 ++ t1) (s2 ++ t2).
Admitted.

End PermSeq.

Section RotrLemmas.

End RotrLemmas.

Section RotCompLemmas.

End RotCompLemmas.

Section Mask.

End Mask.

Section EqMask.

End EqMask.

Section Subseq.

End Subseq.

Section Rem.

End Rem.

Section Map.

Variables (n0 : nat) (T1 : Type) (x1 : T1).
Variables (T2 : Type) (x2 : T2) (f : T1 -> T2).

Fixpoint map s := if s is x :: s' then f x :: map s' else [::].

End Map.

Notation "[ 'seq' E | i <- s ]" := (map (fun i => E) s)
  (at level 0, E at level 99, i binder,
   format "[ '[hv' 'seq'  E '/ '  |  i  <-  s ] ']'") : seq_scope.

Section MiscMask.

End MiscMask.

Section FilterSubseq.

End FilterSubseq.

Section EqMap.

End EqMap.

Section MapComp.

End MapComp.

Section Pmap.

Variables (aT rT : Type) (f : aT -> option rT) (g : rT -> aT).

Fixpoint pmap s :=
  if s is x :: s' then let r := pmap s' in oapp (cons^~ r) r (f x) else [::].

End Pmap.

Section EqPmap.

End EqPmap.

Section PmapSub.

End PmapSub.

Section EqPmapSub.

End EqPmapSub.

Fixpoint iota m n := if n is n'.+1 then m :: iota m.+1 n' else [::].

Lemma mem_iota m n i : (i \in iota m n) = (m <= i < m + n).
Admitted.

Section MakeSeq.

End MakeSeq.

Section MakeEqSeq.

End MakeEqSeq.

Section FoldRight.

Variables (T : Type) (R : Type) (f : T -> R -> R) (z0 : R).

Fixpoint foldr s := if s is x :: s' then f x (foldr s') else z0.

End FoldRight.

Section FoldRightComp.

End FoldRightComp.

Section FoldLeft.

End FoldLeft.

Section Folds.

End Folds.

Section Scan.

End Scan.

Section Zip.

Variables (S T : Type) (r : S -> T -> bool).

Definition unzip1 := map (@fst S T).

End Zip.

Section Flatten.

Variable T : Type.

Definition flatten := foldr cat (Nil T).

End Flatten.

Section EqFlatten.

End EqFlatten.

Notation "[ 'seq' E | x <- s , y <- t ]" :=
  (flatten [seq [seq E | y <- t] | x <- s])
  (at level 0, E at level 99, x binder, y binder,
   format "[ '[hv' 'seq'  E '/ '  |  x  <-  s , '/   '  y  <-  t ] ']'")
   : seq_scope.

Section PrefixSuffixInfix.

End PrefixSuffixInfix.

Section AllPairsDep.

End AllPairsDep.

Section AllPairsNonDep.

End AllPairsNonDep.

Section EqAllPairsDep.

End EqAllPairsDep.

Section MemAllPairs.

End MemAllPairs.

Section EqAllPairs.

End EqAllPairs.

Section AllRel.

End AllRel.

Section All2Rel.

End All2Rel.

Section Pairwise.

End Pairwise.

Section EqPairwise.

End EqPairwise.

Section Permutations.

End Permutations.

Section AllIff.

End AllIff.

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
Import mathcomp.ssreflect.ssrnat.
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
