(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "-projection-no-head-constant" "-w" "-redundant-canonical-projection" "-w" "-notation-overridden" "-w" "+duplicate-clear" "-w" "-ambiguous-paths" "-w" "+non-primitive-record" "-w" "+undeclared-scope" "-w" "-deprecated-hint-without-locality" "-w" "-deprecated-ident-entry" "-w" "-deprecated-native-compiler-option" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/mathcomp/mathcomp" "mathcomp" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-I" "/github/workspace/builds/coq/coq-failing/_build_ci/mathcomp/mathcomp" "-top" "bug_01" "-native-compiler" "ondemand") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 5928 lines to 3548 lines, then from 3193 lines to 243 lines, then from 256 lines to 2271 lines, then from 2276 lines to 354 lines, then from 367 lines to 3632 lines, then from 3636 lines to 378 lines, then from 391 lines to 3219 lines, then from 3224 lines to 1994 lines, then from 1866 lines to 544 lines, then from 557 lines to 3736 lines, then from 3741 lines to 575 lines, then from 588 lines to 5227 lines, then from 5232 lines to 5524 lines, then from 5216 lines to 999 lines, then from 1012 lines to 1438 lines, then from 1443 lines to 1030 lines, then from 1043 lines to 1818 lines, then from 1823 lines to 1153 lines, then from 1166 lines to 4273 lines, then from 4278 lines to 2340 lines, then from 2121 lines to 1282 lines, then from 1295 lines to 7959 lines, then from 7964 lines to 6665 lines, then from 6004 lines to 1976 lines, then from 1989 lines to 4548 lines, then from 4552 lines to 4757 lines, then from 4611 lines to 2065 lines, then from 2078 lines to 4171 lines, then from 4176 lines to 2158 lines, then from 2171 lines to 2689 lines, then from 2694 lines to 2404 lines, then from 2343 lines to 2268 lines, then from 2281 lines to 3009 lines, then from 3014 lines to 2385 lines, then from 2398 lines to 4785 lines, then from 4790 lines to 3022 lines, then from 2835 lines to 2716 lines, then from 2729 lines to 3461 lines, then from 3466 lines to 2926 lines, then from 2939 lines to 4017 lines, then from 4022 lines to 2962 lines, then from 2951 lines to 2935 lines, then from 2948 lines to 7131 lines, then from 7136 lines to 5927 lines *)
(* coqc version 8.15+alpha compiled with OCaml 4.13.0
   coqtop version runner-z3wu8uu--project-6138686-concurrent-0:/builds/coq/coq/_build/default,(HEAD detached at 0d1a2eb) (0d1a2eb7ba6a7719f37495807fb9fa49623ac075)
   Expected coqc runtime on this file: 2.467 sec *)
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

Declare ML Module "ltac_plugin".
Module Export AdmitTactic.
Module Import LocalFalse.
Inductive False : Prop := .
End LocalFalse.
Axiom proof_admitted : False.
Global Set Default Proof Mode "Classic".
Tactic Notation "admit" := abstract case proof_admitted.
End AdmitTactic.

Module Export mathcomp_DOT_ssreflect_DOT_seq_WRAPPED.
Module Export seq.
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

Lemma nth_nil n : nth [::] n = x0.
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

Lemma take_take i j : i <= j -> forall s, take i (take j s) = take i s.
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
Notation "[ 'seq' x : T <- s | C ]" := (filter (fun x : T => C%B) s)
 (at level 0, x at level 99, only parsing).
Notation "[ 'seq' x : T <- s | C1 & C2 ]" := [seq x : T <- s | C1 && C2]
 (at level 0, x at level 99, only parsing).

 
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

Canonical seq_eqMixin := EqMixin eqseqP.
Canonical seq_eqType := Eval hnf in EqType (seq T) seq_eqMixin.

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
Admitted.

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

Lemma allss s : all (mem s) s.
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

Lemma has_sym s1 s2 : has (mem s1) s2 = has (mem s2) s1.
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
  uniq (s1 ++ s2) = [&& uniq s1, ~~ has (mem s1) s2 & uniq s2].
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

 
 
 
 
 
 
 
Hint Extern 0 (is_true (all _ _)) =>
  apply: (allss : forall T s, all (mem_seq s) s) : core.

Section NthTheory.

Lemma nthP (T : eqType) (s : seq T) x x0 :
  reflect (exists2 i, i < size s & nth x0 s i = x) (x \in s).
Admitted.

Variable T : Type.

Lemma has_nthP (a : pred T) s x0 :
  reflect (exists2 i, i < size s & a (nth x0 s i)) (has a s).
Admitted.

Lemma all_nthP (a : pred T) s x0 :
  reflect (forall i, i < size s -> a (nth x0 s i)) (all a s).
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
Canonical bitseq_eqType := Eval hnf in [eqType of bitseq].
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

Lemma perm_catAC s1 s2 s3 : perm_eql ((s1 ++ s2) ++ s3) ((s1 ++ s3) ++ s2).
Admitted.

Lemma perm_catCA s1 s2 s3 : perm_eql (s1 ++ s2 ++ s3) (s2 ++ s1 ++ s3).
Admitted.

Lemma perm_catACA s1 s2 s3 s4 :
  perm_eql ((s1 ++ s2) ++ (s3 ++ s4)) ((s1 ++ s3) ++ (s2 ++ s4)).
Admitted.

Lemma perm_rcons x s : perm_eql (rcons s x) (x :: s).
Admitted.

Lemma perm_rot n s : perm_eql (rot n s) s.
Admitted.

Lemma perm_rotr n s : perm_eql (rotr n s) s.
Admitted.

Lemma perm_rev s : perm_eql (rev s) s.
Admitted.

Lemma perm_filter s1 s2 a :
  perm_eq s1 s2 -> perm_eq (filter a s1) (filter a s2).
Admitted.

Lemma perm_filterC a s : perm_eql (filter a s ++ filter (predC a) s) s.
Admitted.

Lemma perm_size s1 s2 : perm_eq s1 s2 -> size s1 = size s2.
Admitted.

Lemma perm_mem s1 s2 : perm_eq s1 s2 -> s1 =i s2.
Admitted.

Lemma perm_nilP s : reflect (s = [::]) (perm_eq s [::]).
Admitted.

Lemma perm_consP x s t :
  reflect (exists i u, rot i t = x :: u /\ perm_eq u s)
          (perm_eq t (x :: s)).
Admitted.

Lemma perm_has s1 s2 a : perm_eq s1 s2 -> has a s1 = has a s2.
Admitted.

Lemma perm_all s1 s2 a : perm_eq s1 s2 -> all a s1 = all a s2.
Admitted.

Lemma perm_small_eq s1 s2 : size s2 <= 1 -> perm_eq s1 s2 -> s1 = s2.
Admitted.

Lemma uniq_leq_size s1 s2 : uniq s1 -> {subset s1 <= s2} -> size s1 <= size s2.
Admitted.

Lemma leq_size_uniq s1 s2 :
  uniq s1 -> {subset s1 <= s2} -> size s2 <= size s1 -> uniq s2.
Admitted.

Lemma uniq_size_uniq s1 s2 :
  uniq s1 -> s1 =i s2 -> uniq s2 = (size s2 == size s1).
Admitted.

Lemma uniq_min_size s1 s2 :
    uniq s1 -> {subset s1 <= s2} -> size s2 <= size s1 ->
  (size s1 = size s2) * (s1 =i s2).
Admitted.

Lemma eq_uniq s1 s2 : size s1 = size s2 -> s1 =i s2 -> uniq s1 = uniq s2.
Admitted.

Lemma perm_uniq s1 s2 : perm_eq s1 s2 -> uniq s1 = uniq s2.
Admitted.

Lemma uniq_perm s1 s2 : uniq s1 -> uniq s2 -> s1 =i s2 -> perm_eq s1 s2.
Admitted.

Lemma perm_undup s1 s2 : s1 =i s2 -> perm_eq (undup s1) (undup s2).
Admitted.

Lemma count_mem_uniq s : (forall x, count_mem x s = (x \in s)) -> uniq s.
Admitted.

Lemma eq_count_undup a s1 s2 :
  {in a, s1 =i s2} -> count a (undup s1) = count a (undup s2).
Admitted.

Lemma catCA_perm_ind P :
    (forall s1 s2 s3, P (s1 ++ s2 ++ s3) -> P (s2 ++ s1 ++ s3)) ->
  (forall s1 s2, perm_eq s1 s2 -> P s1 -> P s2).
Admitted.

Lemma catCA_perm_subst R F :
    (forall s1 s2 s3, F (s1 ++ s2 ++ s3) = F (s2 ++ s1 ++ s3) :> R) ->
  (forall s1 s2, perm_eq s1 s2 -> F s1 = F s2).
Admitted.

End PermSeq.

Notation perm_eql s1 s2 := (perm_eq s1 =1 perm_eq s2).
Notation perm_eqr s1 s2 := (perm_eq^~ s1 =1 perm_eq^~ s2).

Arguments permP {T s1 s2}.
Arguments permPl {T s1 s2}.
Arguments permPr {T s1 s2}.
Prenex Implicits perm_eq.
Hint Resolve perm_refl : core.

Section RotrLemmas.

Variables (n0 : nat) (T : Type) (T' : eqType).
Implicit Types (x : T) (s : seq T).

Lemma size_rotr s : size (rotr n0 s) = size s.
Admitted.

Lemma mem_rotr (s : seq T') : rotr n0 s =i s.
Admitted.

Lemma rotr_size_cat s1 s2 : rotr (size s2) (s1 ++ s2) = s2 ++ s1.
Admitted.

Lemma rotr1_rcons x s : rotr 1 (rcons s x) = x :: s.
Admitted.

Lemma has_rotr a s : has a (rotr n0 s) = has a s.
Admitted.

Lemma rotr_uniq (s : seq T') : uniq (rotr n0 s) = uniq s.
Admitted.

Lemma rotrK : cancel (@rotr T n0) (rot n0).
Admitted.

Lemma rotr_inj : injective (@rotr T n0).
Admitted.

Lemma take_rev s : take n0 (rev s) = rev (drop (size s - n0) s).
Admitted.

Lemma rev_take s : rev (take n0 s) = drop (size s - n0) (rev s).
Admitted.

Lemma drop_rev s : drop n0 (rev s) = rev (take (size s - n0) s).
Admitted.

Lemma rev_drop s : rev (drop n0 s) = take (size s - n0) (rev s).
Admitted.

Lemma rev_rotr s : rev (rotr n0 s) = rot n0 (rev s).
Admitted.

Lemma rev_rot s : rev (rot n0 s) = rotr n0 (rev s).
Admitted.

End RotrLemmas.

Arguments rotrK n0 {T} s : rename.
Arguments rotr_inj {n0 T} [s1 s2] eq_rotr_s12 : rename.

Section RotCompLemmas.

Variable T : Type.
Implicit Type s : seq T.

Lemma rotD m n s : m + n <= size s -> rot (m + n) s = rot m (rot n s).
Admitted.

Lemma rotS n s : n < size s -> rot n.+1 s = rot 1 (rot n s).
Admitted.

Lemma rot_add_mod m n s : n <= size s -> m <= size s ->
  rot m (rot n s) = rot (if m + n <= size s then m + n else m + n - size s) s.
Admitted.

Lemma rot_minn n s : rot n s = rot (minn n (size s)) s.
Admitted.

Definition rot_add s n m (k := size s) (p := minn m k + minn n k) :=
  locked (if p <= k then p else p - k).

Lemma leq_rot_add n m s : rot_add s n m <= size s.
Admitted.

Lemma rot_addC n m s : rot_add s n m = rot_add s m n.
Admitted.

Lemma rot_rot_add n m s : rot m (rot n s) = rot (rot_add s n m) s.
Admitted.

Lemma rot_rot m n s : rot m (rot n s) = rot n (rot m s).
Admitted.

Lemma rot_rotr m n s : rot m (rotr n s) = rotr n (rot m s).
Admitted.

Lemma rotr_rotr m n s : rotr m (rotr n s) = rotr n (rotr m s).
Admitted.

End RotCompLemmas.

Section Mask.

Variables (n0 : nat) (T : Type).
Implicit Types (m : bitseq) (s : seq T).

Fixpoint mask m s {struct m} :=
  match m, s with
  | b :: m', x :: s' => if b then x :: mask m' s' else mask m' s'
  | _, _ => [::]
  end.

Lemma mask_false s n : mask (nseq n false) s = [::].
Admitted.

Lemma mask_true s n : size s <= n -> mask (nseq n true) s = s.
Admitted.

Lemma mask0 m : mask m [::] = [::].
Admitted.

Lemma mask0s s : mask [::] s = [::].
Admitted.

Lemma mask1 b x : mask [:: b] [:: x] = nseq b x.
Admitted.

Lemma mask_cons b m x s : mask (b :: m) (x :: s) = nseq b x ++ mask m s.
Admitted.

Lemma size_mask m s : size m = size s -> size (mask m s) = count id m.
Admitted.

Lemma mask_cat m1 m2 s1 s2 :
  size m1 = size s1 -> mask (m1 ++ m2) (s1 ++ s2) = mask m1 s1 ++ mask m2 s2.
Admitted.

Lemma mask_rcons b m x s : size m = size s ->
  mask (rcons m b) (rcons s x) = mask m s ++ nseq b x.
Admitted.

Lemma all_mask a m s : all a s -> all a (mask m s).
Admitted.

Lemma has_mask_cons a b m x s :
  has a (mask (b :: m) (x :: s)) = b && a x || has a (mask m s).
Admitted.

Lemma has_mask a m s : has a (mask m s) -> has a s.
Admitted.

Lemma rev_mask m s : size m = size s -> rev (mask m s) = mask (rev m) (rev s).
Admitted.

Lemma mask_rot m s : size m = size s ->
   mask (rot n0 m) (rot n0 s) = rot (count id (take n0 m)) (mask m s).
Admitted.

Lemma resize_mask m s : {m1 | size m1 = size s & mask m s = mask m1 s}.
Admitted.

Lemma takeEmask i s : take i s = mask (nseq i true) s.
Admitted.

Lemma dropEmask i s :
  drop i s = mask (nseq i false ++ nseq (size s - i) true) s.
Admitted.

End Mask.
Arguments mask _ !_ !_.

Section EqMask.

Variables (n0 : nat) (T : eqType).
Implicit Types (s : seq T) (m : bitseq).

Lemma mem_mask_cons x b m y s :
  (x \in mask (b :: m) (y :: s)) = b && (x == y) || (x \in mask m s).
Admitted.

Lemma mem_mask x m s : x \in mask m s -> x \in s.
Admitted.

Lemma in_mask x m s :
  uniq s -> x \in mask m s = (x \in s) && nth false m (index x s).
Admitted.

Lemma mask_uniq s : uniq s -> forall m, uniq (mask m s).
Admitted.

Lemma mem_mask_rot m s :
  size m = size s -> mask (rot n0 m) (rot n0 s) =i mask m s.
Admitted.

End EqMask.

Section Subseq.

Variable T : eqType.
Implicit Type s : seq T.

Fixpoint subseq s1 s2 :=
  if s2 is y :: s2' then
    if s1 is x :: s1' then subseq (if x == y then s1' else s1) s2' else true
  else s1 == [::].

Lemma sub0seq s : subseq [::] s.
Admitted.

Lemma subseq0 s : subseq s [::] = (s == [::]).
Admitted.

Lemma subseq_refl s : subseq s s.
Admitted.
Hint Resolve subseq_refl : core.

Lemma subseqP s1 s2 :
  reflect (exists2 m, size m = size s2 & s1 = mask m s2) (subseq s1 s2).
Admitted.

Lemma mask_subseq m s : subseq (mask m s) s.
Admitted.

Lemma subseq_trans : transitive subseq.
Admitted.

Lemma cat_subseq s1 s2 s3 s4 :
  subseq s1 s3 -> subseq s2 s4 -> subseq (s1 ++ s2) (s3 ++ s4).
Admitted.

Lemma prefix_subseq s1 s2 : subseq s1 (s1 ++ s2).
Admitted.

Lemma suffix_subseq s1 s2 : subseq s2 (s1 ++ s2).
Admitted.

Lemma take_subseq s i : subseq (take i s) s.
Admitted.

Lemma drop_subseq s i : subseq (drop i s) s.
Admitted.

Lemma mem_subseq s1 s2 : subseq s1 s2 -> {subset s1 <= s2}.
Admitted.

Lemma sub1seq x s : subseq [:: x] s = (x \in s).
Admitted.

Lemma size_subseq s1 s2 : subseq s1 s2 -> size s1 <= size s2.
Admitted.

Lemma size_subseq_leqif s1 s2 :
  subseq s1 s2 -> size s1 <= size s2 ?= iff (s1 == s2).
Admitted.

Lemma subseq_cons s x : subseq s (x :: s).
Admitted.

Lemma cons_subseq s1 s2 x : subseq (x :: s1) s2 -> subseq s1 s2.
Admitted.

Lemma subseq_rcons s x : subseq s (rcons s x).
Admitted.

Lemma subseq_uniq s1 s2 : subseq s1 s2 -> uniq s2 -> uniq s1.
Admitted.

Lemma take_uniq s n : uniq s -> uniq (take n s).
Admitted.

Lemma drop_uniq s n : uniq s -> uniq (drop n s).
Admitted.

Lemma undup_subseq s : subseq (undup s) s.
Admitted.

Lemma subseq_rev s1 s2 : subseq (rev s1) (rev s2) = subseq s1 s2.
Admitted.

Lemma subseq_cat2l s s1 s2 : subseq (s ++ s1) (s ++ s2) = subseq s1 s2.
Admitted.

Lemma subseq_cat2r s s1 s2 : subseq (s1 ++ s) (s2 ++ s) = subseq s1 s2.
Admitted.

Lemma subseq_rot p s n :
  subseq p s -> exists2 k, k <= n & subseq (rot k p) (rot n s).
Admitted.

End Subseq.

Prenex Implicits subseq.
Arguments subseqP {T s1 s2}.

Hint Resolve subseq_refl : core.

Section Rem.

Variables (T : eqType) (x : T).

Fixpoint rem s := if s is y :: t then (if y == x then t else y :: rem t) else s.

Lemma rem_cons y s : rem (y :: s) = if y == x then s else y :: rem s.
Admitted.

Lemma remE s : rem s = take (index x s) s ++ drop (index x s).+1 s.
Admitted.

Lemma rem_id s : x \notin s -> rem s = s.
Admitted.

Lemma perm_to_rem s : x \in s -> perm_eq s (x :: rem s).
Admitted.

Lemma size_rem s : x \in s -> size (rem s) = (size s).-1.
Admitted.

Lemma rem_subseq s : subseq (rem s) s.
Admitted.

Lemma rem_uniq s : uniq s -> uniq (rem s).
Admitted.

Lemma mem_rem s : {subset rem s <= s}.
Admitted.

Lemma rem_filter s : uniq s -> rem s = filter (predC1 x) s.
Admitted.

Lemma mem_rem_uniq s : uniq s -> rem s =i [predD1 s & x].
Admitted.

Lemma mem_rem_uniqF s : uniq s -> x \in rem s = false.
Admitted.

Lemma count_rem P s : count P (rem s) = count P s - (x \in s) && P x.
Admitted.

Lemma count_mem_rem y s : count_mem y (rem s) = count_mem y s - (x == y).
Admitted.

End Rem.

Section Map.

Variables (n0 : nat) (T1 : Type) (x1 : T1).
Variables (T2 : Type) (x2 : T2) (f : T1 -> T2).

Fixpoint map s := if s is x :: s' then f x :: map s' else [::].

Lemma map_cons x s : map (x :: s) = f x :: map s.
Admitted.

Lemma map_nseq x : map (nseq n0 x) = nseq n0 (f x).
Admitted.

Lemma map_cat s1 s2 : map (s1 ++ s2) = map s1 ++ map s2.
Admitted.

Lemma size_map s : size (map s) = size s.
Admitted.

Lemma behead_map s : behead (map s) = map (behead s).
Admitted.

Lemma nth_map n s : n < size s -> nth x2 (map s) n = f (nth x1 s n).
Admitted.

Lemma map_rcons s x : map (rcons s x) = rcons (map s) (f x).
Admitted.

Lemma last_map s x : last (f x) (map s) = f (last x s).
Admitted.

Lemma belast_map s x : belast (f x) (map s) = map (belast x s).
Admitted.

Lemma filter_map a s : filter a (map s) = map (filter (preim f a) s).
Admitted.

Lemma find_map a s : find a (map s) = find (preim f a) s.
Admitted.

Lemma has_map a s : has a (map s) = has (preim f a) s.
Admitted.

Lemma all_map a s : all a (map s) = all (preim f a) s.
Admitted.

Lemma count_map a s : count a (map s) = count (preim f a) s.
Admitted.

Lemma map_take s : map (take n0 s) = take n0 (map s).
Admitted.

Lemma map_drop s : map (drop n0 s) = drop n0 (map s).
Admitted.

Lemma map_rot s : map (rot n0 s) = rot n0 (map s).
Admitted.

Lemma map_rotr s : map (rotr n0 s) = rotr n0 (map s).
Admitted.

Lemma map_rev s : map (rev s) = rev (map s).
Admitted.

Lemma map_mask m s : map (mask m s) = mask m (map s).
Admitted.

Lemma inj_map : injective f -> injective map.
Admitted.

End Map.

Notation "[ 'seq' E | i <- s ]" := (map (fun i => E) s)
  (at level 0, E at level 99, i ident,
   format "[ '[hv' 'seq'  E '/ '  |  i  <-  s ] ']'") : seq_scope.

Notation "[ 'seq' E | i <- s & C ]" := [seq E | i <- [seq i <- s | C]]
  (at level 0, E at level 99, i ident,
   format "[ '[hv' 'seq'  E '/ '  |  i  <-  s '/ '  &  C ] ']'") : seq_scope.

Notation "[ 'seq' E | i : T <- s ]" := (map (fun i : T => E) s)
  (at level 0, E at level 99, i ident, only parsing) : seq_scope.

Notation "[ 'seq' E | i : T <- s & C ]" :=
  [seq E | i : T <- [seq i : T <- s | C]]
  (at level 0, E at level 99, i ident, only parsing) : seq_scope.

Notation "[ 'seq' E : R | i <- s ]" := (@map _ R (fun i => E) s)
  (at level 0, E at level 99, i ident, only parsing) : seq_scope.

Notation "[ 'seq' E : R | i <- s & C ]" := [seq E : R | i <- [seq i <- s | C]]
  (at level 0, E at level 99, i ident, only parsing) : seq_scope.

Notation "[ 'seq' E : R | i : T <- s ]" := (@map T R (fun i : T => E) s)
  (at level 0, E at level 99, i ident, only parsing) : seq_scope.

Notation "[ 'seq' E : R | i : T <- s & C ]" :=
  [seq E : R | i : T <- [seq i : T <- s | C]]
  (at level 0, E at level 99, i ident, only parsing) : seq_scope.

Lemma filter_mask T a (s : seq T) : filter a s = mask (map a s) s.
Admitted.

Lemma all_sigP T a (s : seq T) : all a s -> {s' : seq (sig a) | s = map sval s'}.
Admitted.

Section MiscMask.

Lemma leq_count_mask T (P : {pred T}) m s : count P (mask m s) <= count P s.
Admitted.

Variable (T : eqType).
Implicit Types (s : seq T) (m : bitseq).

Lemma mask_filter s m : uniq s -> mask m s = [seq i <- s | i \in mask m s].
Admitted.

Lemma leq_count_subseq P s1 s2 : subseq s1 s2 -> count P s1 <= count P s2.
Admitted.

Lemma count_maskP s1 s2 :
  (forall x, count_mem x s1 <= count_mem x s2) <->
    exists2 m : bitseq, size m = size s2 & perm_eq s1 (mask m s2).
Admitted.

Lemma count_subseqP s1 s2 :
  (forall x, count_mem x s1 <= count_mem x s2) <->
    exists2 s, subseq s s2 & perm_eq s1 s.
Admitted.

End MiscMask.

Section FilterSubseq.

Variable T : eqType.
Implicit Types (s : seq T) (a : pred T).

Lemma filter_subseq a s : subseq (filter a s) s.
Admitted.

Lemma subseq_filter s1 s2 a :
  subseq s1 (filter a s2) = all a s1 && subseq s1 s2.
Admitted.

Lemma subseq_uniqP s1 s2 :
  uniq s2 -> reflect (s1 = filter (mem s1) s2) (subseq s1 s2).
Admitted.

Lemma uniq_subseq_pivot x (s1 s2 s3 s4 : seq T) (s := s3 ++ x :: s4) :
  uniq s -> subseq (s1 ++ x :: s2) s = (subseq s1 s3 && subseq s2 s4).
Admitted.

Lemma perm_to_subseq s1 s2 :
  subseq s1 s2 -> {s3 | perm_eq s2 (s1 ++ s3)}.
Admitted.

Lemma subseq_rem x : {homo rem x : s1 s2 / @subseq T s1 s2}.
Admitted.

End FilterSubseq.

Arguments subseq_uniqP [T s1 s2].

Section EqMap.

Variables (n0 : nat) (T1 : eqType) (x1 : T1).
Variables (T2 : eqType) (x2 : T2) (f : T1 -> T2).
Implicit Type s : seq T1.

Lemma map_f s x : x \in s -> f x \in map f s.
Admitted.

Lemma mapP s y : reflect (exists2 x, x \in s & y = f x) (y \in map f s).
admit.
Defined.

Lemma map_uniq s : uniq (map f s) -> uniq s.
Admitted.

Lemma map_inj_in_uniq s : {in s &, injective f} -> uniq (map f s) = uniq s.
Admitted.

Lemma map_subseq s1 s2 : subseq s1 s2 -> subseq (map f s1) (map f s2).
Admitted.

Lemma nth_index_map s x0 x :
  {in s &, injective f} -> x \in s -> nth x0 s (index (f x) (map f s)) = x.
Admitted.

Lemma perm_map s t : perm_eq s t -> perm_eq (map f s) (map f t).
Admitted.

Lemma sub_map s1 s2 : {subset s1 <= s2} -> {subset map f s1 <= map f s2}.
Admitted.

Lemma eq_mem_map s1 s2 : s1 =i s2 -> map f s1 =i map f s2.
Admitted.

Hypothesis Hf : injective f.

Lemma mem_map s x : (f x \in map f s) = (x \in s).
Admitted.

Lemma index_map s x : index (f x) (map f s) = index x s.
Admitted.

Lemma map_inj_uniq s : uniq (map f s) = uniq s.
Admitted.

Lemma undup_map_inj s : undup (map f s) = map f (undup s).
Admitted.

Lemma perm_map_inj s t : perm_eq (map f s) (map f t) -> perm_eq s t.
Admitted.

End EqMap.

Arguments mapP {T1 T2 f s y}.

Lemma map_of_seq (T1 : eqType) T2 (s : seq T1) (fs : seq T2) (y0 : T2) :
  {f | uniq s -> size fs = size s -> map f s = fs}.
Admitted.

Section MapComp.

Variable T1 T2 T3 : Type.

Lemma map_id (s : seq T1) : map id s = s.
Admitted.

Lemma eq_map (f1 f2 : T1 -> T2) : f1 =1 f2 -> map f1 =1 map f2.
Admitted.

Lemma map_comp (f1 : T2 -> T3) (f2 : T1 -> T2) s :
  map (f1 \o f2) s = map f1 (map f2 s).
Admitted.

Lemma mapK (f1 : T1 -> T2) (f2 : T2 -> T1) :
  cancel f1 f2 -> cancel (map f1) (map f2).
Admitted.

End MapComp.

Lemma eq_in_map (T1 : eqType) T2 (f1 f2 : T1 -> T2) (s : seq T1) :
  {in s, f1 =1 f2} <-> map f1 s = map f2 s.
Admitted.

Lemma map_id_in (T : eqType) f (s : seq T) : {in s, f =1 id} -> map f s = s.
Admitted.

 

Section Pmap.

Variables (aT rT : Type) (f : aT -> option rT) (g : rT -> aT).

Fixpoint pmap s :=
  if s is x :: s' then let r := pmap s' in oapp (cons^~ r) r (f x) else [::].

Lemma map_pK : pcancel g f -> cancel (map g) pmap.
Admitted.

Lemma size_pmap s : size (pmap s) = count [eta f] s.
Admitted.

Lemma pmapS_filter s : map some (pmap s) = map f (filter [eta f] s).
Admitted.

Hypothesis fK : ocancel f g.

Lemma pmap_filter s : map g (pmap s) = filter [eta f] s.
Admitted.

Lemma pmap_cat s t : pmap (s ++ t) = pmap s ++ pmap t.
Admitted.

Lemma all_pmap (p : pred rT) s :
  all p (pmap s) = all [pred i | oapp p true (f i)] s.
Admitted.

End Pmap.

Lemma eq_in_pmap (aT : eqType) rT (f1 f2 : aT -> option rT) s :
  {in s, f1 =1 f2} -> pmap f1 s = pmap f2 s.
Admitted.

Lemma eq_pmap aT rT (f1 f2 : aT -> option rT) :
  f1 =1 f2 -> pmap f1 =1 pmap f2.
Admitted.

Section EqPmap.

Variables (aT rT : eqType) (f : aT -> option rT) (g : rT -> aT).

Lemma mem_pmap s u : (u \in pmap f s) = (Some u \in map f s).
Admitted.

Hypothesis fK : ocancel f g.

Lemma can2_mem_pmap : pcancel g f -> forall s u, (u \in pmap f s) = (g u \in s).
Admitted.

Lemma pmap_uniq s : uniq s -> uniq (pmap f s).
Admitted.

Lemma perm_pmap s t : perm_eq s t -> perm_eq (pmap f s) (pmap f t).
Admitted.

End EqPmap.

Section PmapSub.

Variables (T : Type) (p : pred T) (sT : subType p).

Lemma size_pmap_sub s : size (pmap (insub : T -> option sT) s) = count p s.
Admitted.

End PmapSub.

Section EqPmapSub.

Variables (T : eqType) (p : pred T) (sT : subType p).
Let insT : T -> option sT. exact (insub). Defined.

Lemma mem_pmap_sub s u : (u \in pmap insT s) = (val u \in s).
Admitted.

Lemma pmap_sub_uniq s : uniq s -> uniq (pmap insT s).
Admitted.

End EqPmapSub.

 

Fixpoint iota m n := if n is n'.+1 then m :: iota m.+1 n' else [::].

Lemma size_iota m n : size (iota m n) = n.
Admitted.

Lemma iotaD m n1 n2 : iota m (n1 + n2) = iota m n1 ++ iota (m + n1) n2.
Admitted.

Lemma iotaDl m1 m2 n : iota (m1 + m2) n = map (addn m1) (iota m2 n).
Admitted.

Lemma nth_iota p m n i : i < n -> nth p (iota m n) i = m + i.
Admitted.

Lemma mem_iota m n i : (i \in iota m n) = (m <= i < m + n).
Admitted.

Lemma iota_uniq m n : uniq (iota m n).
Admitted.

Lemma take_iota k m n : take k (iota m n) = iota m (minn k n).
Admitted.

Lemma drop_iota k m n : drop k (iota m n) = iota (m + k) (n - k).
Admitted.

Lemma filter_iota_ltn m n j : j <= n ->
  [seq i <- iota m n | i < m + j] = iota m j.
Admitted.

Lemma filter_iota_leq n m j : j < n ->
  [seq i <- iota m n | i <= m + j] = iota m j.+1.
Admitted.

 

Section MakeSeq.

Variables (T : Type) (x0 : T).

Definition mkseq f n : seq T := map f (iota 0 n).

Lemma size_mkseq f n : size (mkseq f n) = n.
Admitted.

Lemma eq_mkseq f g : f =1 g -> mkseq f =1 mkseq g.
Admitted.

Lemma nth_mkseq f n i : i < n -> nth x0 (mkseq f n) i = f i.
Admitted.

Lemma mkseq_nth s : mkseq (nth x0 s) (size s) = s.
Admitted.

Variant mkseq_spec s : seq T -> Type :=
| MapIota n f : s = mkseq f n -> mkseq_spec s (mkseq f n).

Lemma mkseqP s : mkseq_spec s s.
Admitted.

Lemma map_nth_iota0 s i :
  i <= size s -> [seq nth x0 s j | j <- iota 0 i] = take i s.
Admitted.

Lemma map_nth_iota s i j : j <= size s - i ->
  [seq nth x0 s k | k <- iota i j] = take j (drop i s).
Admitted.

End MakeSeq.

Section MakeEqSeq.

Variable T : eqType.

Lemma mkseq_uniq (f : nat -> T) n : injective f -> uniq (mkseq f n).
Admitted.

Lemma perm_iotaP {s t : seq T} x0 (It := iota 0 (size t)) :
  reflect (exists2 Is, perm_eq Is It & s = map (nth x0 t) Is) (perm_eq s t).
Admitted.

End MakeEqSeq.

Arguments perm_iotaP {T s t}.

Section FoldRight.

Variables (T : Type) (R : Type) (f : T -> R -> R) (z0 : R).

Fixpoint foldr s := if s is x :: s' then f x (foldr s') else z0.

End FoldRight.

Section FoldRightComp.

Variables (T1 T2 : Type) (h : T1 -> T2).
Variables (R : Type) (f : T2 -> R -> R) (z0 : R).

Lemma foldr_cat s1 s2 : foldr f z0 (s1 ++ s2) = foldr f (foldr f z0 s2) s1.
Admitted.

Lemma foldr_rcons s x : foldr f z0 (rcons s x) = foldr f (f x z0) s.
Admitted.

Lemma foldr_map s : foldr f z0 (map h s) = foldr (fun x z => f (h x) z) z0 s.
Admitted.

End FoldRightComp.

 

Definition sumn := foldr addn 0.

Lemma sumn_nseq x n : sumn (nseq n x) = x * n.
Admitted.

Lemma sumn_cat s1 s2 : sumn (s1 ++ s2) = sumn s1 + sumn s2.
Admitted.

Lemma sumn_count T (a : pred T) s : sumn [seq a i : nat | i <- s] = count a s.
Admitted.

Lemma sumn_rcons s n : sumn (rcons s n) = sumn s + n.
Admitted.

Lemma perm_sumn s1 s2 : perm_eq s1 s2 -> sumn s1 = sumn s2.
Admitted.

Lemma sumn_rot s n : sumn (rot n s) = sumn s.
Admitted.

Lemma sumn_rev s : sumn (rev s) = sumn s.
Admitted.

Lemma natnseq0P s : reflect (s = nseq (size s) 0) (sumn s == 0).
Admitted.

Section FoldLeft.

Variables (T R : Type) (f : R -> T -> R).

Fixpoint foldl z s := if s is x :: s' then foldl (f z x) s' else z.

Lemma foldl_rev z s : foldl z (rev s) = foldr (fun x z => f z x) z s.
Admitted.

Lemma foldl_cat z s1 s2 : foldl z (s1 ++ s2) = foldl (foldl z s1) s2.
Admitted.

Lemma foldl_rcons z s x : foldl z (rcons s x) = f (foldl z s) x.
Admitted.

End FoldLeft.

Section Scan.

Variables (T1 : Type) (x1 : T1) (T2 : Type) (x2 : T2).
Variables (f : T1 -> T1 -> T2) (g : T1 -> T2 -> T1).

Fixpoint pairmap x s := if s is y :: s' then f x y :: pairmap y s' else [::].

Lemma size_pairmap x s : size (pairmap x s) = size s.
Admitted.

Lemma pairmap_cat x s1 s2 :
  pairmap x (s1 ++ s2) = pairmap x s1 ++ pairmap (last x s1) s2.
Admitted.

Lemma nth_pairmap s n : n < size s ->
  forall x, nth x2 (pairmap x s) n = f (nth x1 (x :: s) n) (nth x1 s n).
Admitted.

Fixpoint scanl x s :=
  if s is y :: s' then let x' := g x y in x' :: scanl x' s' else [::].

Lemma size_scanl x s : size (scanl x s) = size s.
Admitted.

Lemma scanl_cat x s1 s2 :
  scanl x (s1 ++ s2) = scanl x s1 ++ scanl (foldl g x s1) s2.
Admitted.

Lemma scanl_rcons x s1 y  :
  scanl x (rcons s1 y) =  rcons (scanl x s1) (foldl g x (rcons s1 y)).
Admitted.

Lemma nth_cons_scanl s n : n <= size s ->
  forall x, nth x1 (x :: scanl x s) n = foldl g x (take n s).
Admitted.

Lemma nth_scanl s n : n < size s ->
  forall x, nth x1 (scanl x s) n = foldl g x (take n.+1 s).
Admitted.

Lemma scanlK :
  (forall x, cancel (g x) (f x)) -> forall x, cancel (scanl x) (pairmap x).
Admitted.

Lemma pairmapK :
  (forall x, cancel (f x) (g x)) -> forall x, cancel (pairmap x) (scanl x).
Admitted.

End Scan.

Prenex Implicits mask map pmap foldr foldl scanl pairmap.

Section Zip.

Variables (S T : Type) (r : S -> T -> bool).

Fixpoint zip (s : seq S) (t : seq T) {struct t} :=
  match s, t with
  | x :: s', y :: t' => (x, y) :: zip s' t'
  | _, _ => [::]
  end.

Definition unzip1 := map (@fst S T).
Definition unzip2 := map (@snd S T).

Fixpoint all2 s t :=
  match s, t with
  | [::], [::] => true
  | x :: s, y :: t => r x y && all2 s t
  | _, _ => false
  end.

Lemma zip_unzip s : zip (unzip1 s) (unzip2 s) = s.
Admitted.

Lemma unzip1_zip s t : size s <= size t -> unzip1 (zip s t) = s.
Admitted.

Lemma unzip2_zip s t : size t <= size s -> unzip2 (zip s t) = t.
Admitted.

Lemma size1_zip s t : size s <= size t -> size (zip s t) = size s.
Admitted.

Lemma size2_zip s t : size t <= size s -> size (zip s t) = size t.
Admitted.

Lemma size_zip s t : size (zip s t) = minn (size s) (size t).
Admitted.

Lemma zip_cat s1 s2 t1 t2 :
  size s1 = size t1 -> zip (s1 ++ s2) (t1 ++ t2) = zip s1 t1 ++ zip s2 t2.
Admitted.

Lemma nth_zip x y s t i :
  size s = size t -> nth (x, y) (zip s t) i = (nth x s i, nth y t i).
Admitted.

Lemma nth_zip_cond p s t i :
   nth p (zip s t) i
     = (if i < size (zip s t) then (nth p.1 s i, nth p.2 t i) else p).
Admitted.

Lemma zip_rcons s t x y :
  size s = size t -> zip (rcons s x) (rcons t y) = rcons (zip s t) (x, y).
Admitted.

Lemma rev_zip s t : size s = size t -> rev (zip s t) = zip (rev s) (rev t).
Admitted.

Lemma all2E s t :
  all2 s t = (size s == size t) && all [pred xy | r xy.1 xy.2] (zip s t).
Admitted.

Lemma zip_map I f g (s : seq I) :
  zip (map f s) (map g s) = [seq (f i, g i) | i <- s].
Admitted.

End Zip.

Prenex Implicits zip unzip1 unzip2 all2.

Lemma eqseq_all (T : eqType) (s t : seq T) : (s == t) = all2 eq_op s t.
Admitted.

Lemma eq_map_all I (T : eqType) (f g : I -> T) (s : seq I) :
  (map f s == map g s) = all [pred xy | xy.1 == xy.2] [seq (f i, g i) | i <- s].
Admitted.

Section Flatten.

Variable T : Type.
Implicit Types (s : seq T) (ss : seq (seq T)).

Definition flatten := foldr cat (Nil T).
Definition shape := map (@size T).
Fixpoint reshape sh s :=
  if sh is n :: sh' then take n s :: reshape sh' (drop n s) else [::].

Definition flatten_index sh r c := sumn (take r sh) + c.
Definition reshape_index sh i := find (pred1 0) (scanl subn i.+1 sh).
Definition reshape_offset sh i := i - sumn (take (reshape_index sh i) sh).

Lemma size_flatten ss : size (flatten ss) = sumn (shape ss).
Admitted.

Lemma flatten_cat ss1 ss2 : flatten (ss1 ++ ss2) = flatten ss1 ++ flatten ss2.
Admitted.

Lemma size_reshape sh s : size (reshape sh s) = size sh.
Admitted.

Lemma nth_reshape (sh : seq nat) l n :
  nth [::] (reshape sh l) n = take (nth 0 sh n) (drop (sumn (take n sh)) l).
Admitted.

Lemma flattenK ss : reshape (shape ss) (flatten ss) = ss.
Admitted.

Lemma reshapeKr sh s : size s <= sumn sh -> flatten (reshape sh s) = s.
Admitted.

Lemma reshapeKl sh s : size s >= sumn sh -> shape (reshape sh s) = sh.
Admitted.

Lemma flatten_rcons ss s : flatten (rcons ss s) = flatten ss ++ s.
Admitted.

Lemma flatten_seq1 s : flatten [seq [:: x] | x <- s] = s.
Admitted.

Lemma count_flatten ss P :
  count P (flatten ss) = sumn [seq count P x | x <- ss].
Admitted.

Lemma filter_flatten ss (P : pred T) :
  filter P (flatten ss) = flatten [seq filter P i | i <- ss].
Admitted.

Lemma rev_flatten ss :
  rev (flatten ss) = flatten (rev (map rev ss)).
Admitted.

Lemma nth_shape ss i : nth 0 (shape ss) i = size (nth [::] ss i).
Admitted.

Lemma shape_rev ss : shape (rev ss) = rev (shape ss).
Admitted.

Lemma eq_from_flatten_shape ss1 ss2 :
  flatten ss1 = flatten ss2 -> shape ss1 = shape ss2 -> ss1 = ss2.
Admitted.

Lemma rev_reshape sh s :
  size s = sumn sh -> rev (reshape sh s) = map rev (reshape (rev sh) (rev s)).
Admitted.

Lemma reshape_rcons s sh n (m := sumn sh) :
  m + n = size s ->
  reshape (rcons sh n) s = rcons (reshape sh (take m s)) (drop m s).
Admitted.

Lemma flatten_indexP sh r c :
  c < nth 0 sh r -> flatten_index sh r c < sumn sh.
Admitted.

Lemma reshape_indexP sh i : i < sumn sh -> reshape_index sh i < size sh.
Admitted.

Lemma reshape_offsetP sh i :
  i < sumn sh -> reshape_offset sh i < nth 0 sh (reshape_index sh i).
Admitted.

Lemma reshape_indexK sh i :
  flatten_index sh (reshape_index sh i) (reshape_offset sh i) = i.
Admitted.

Lemma flatten_indexKl sh r c :
  c < nth 0 sh r -> reshape_index sh (flatten_index sh r c) = r.
Admitted.

Lemma flatten_indexKr sh r c :
  c < nth 0 sh r -> reshape_offset sh (flatten_index sh r c) = c.
Admitted.

Lemma nth_flatten x0 ss i (r := reshape_index (shape ss) i) :
  nth x0 (flatten ss) i = nth x0 (nth [::] ss r) (reshape_offset (shape ss) i).
Admitted.

Lemma reshape_leq sh i1 i2
  (r1 := reshape_index sh i1) (c1 := reshape_offset sh i1)
  (r2 := reshape_index sh i2) (c2 := reshape_offset sh i2) :
  (i1 <= i2) = ((r1 < r2) || ((r1 == r2) && (c1 <= c2))).
Admitted.

End Flatten.

Prenex Implicits flatten shape reshape.

Lemma map_flatten S T (f : T -> S) ss :
  map f (flatten ss) = flatten (map (map f) ss).
Admitted.

Lemma flatten_map1 (S T : Type) (f : S -> T) s :
  flatten [seq [:: f x] | x <- s] = map f s.
Admitted.

Lemma undup_flatten_nseq n (T : eqType) (s : seq T) : 0 < n ->
  undup (flatten (nseq n s)) = undup s.
Admitted.

Lemma sumn_flatten (ss : seq (seq nat)) :
  sumn (flatten ss) = sumn (map sumn ss).
Admitted.

Lemma map_reshape T S (f : T -> S) sh s :
  map (map f) (reshape sh s) = reshape sh (map f s).
Admitted.

Section EqFlatten.

Variables S T : eqType.

Lemma flattenP (A : seq (seq T)) x :
  reflect (exists2 s, s \in A & x \in s) (x \in flatten A).
admit.
Defined.
Arguments flattenP {A x}.

Lemma flatten_mapP (A : S -> seq T) s y :
  reflect (exists2 x, x \in s & y \in A x) (y \in flatten (map A s)).
Admitted.

Lemma perm_flatten (ss1 ss2 : seq (seq T)) :
  perm_eq ss1 ss2 -> perm_eq (flatten ss1) (flatten ss2).
Admitted.

End EqFlatten.

Arguments flattenP {T A x}.
Arguments flatten_mapP {S T A s y}.

Notation "[ 'seq' E | x <- s , y <- t ]" :=
  (flatten [seq [seq E | y <- t] | x <- s])
  (at level 0, E at level 99, x ident, y ident,
   format "[ '[hv' 'seq'  E '/ '  |  x  <-  s , '/   '  y  <-  t ] ']'")
   : seq_scope.
Notation "[ 'seq' E | x : S <- s , y : T <- t ]" :=
  (flatten [seq [seq E | y : T <- t] | x : S  <- s])
  (at level 0, E at level 99, x ident, y ident, only parsing) : seq_scope.
Notation "[ 'seq' E : R | x : S <- s , y : T <- t ]" :=
  (flatten [seq [seq E : R | y : T <- t] | x : S  <- s])
  (at level 0, E at level 99, x ident, y ident, only parsing) : seq_scope.
Notation "[ 'seq' E : R | x <- s , y <- t ]" :=
  (flatten [seq [seq E : R | y <- t] | x  <- s])
  (at level 0, E at level 99, x ident, y ident, only parsing) : seq_scope.

Section AllPairsDep.

Variables (S S' : Type) (T T' : S -> Type) (R : Type).
Implicit Type f : forall x, T x -> R.

Definition allpairs_dep f s t := [seq f x y | x <- s, y <- t x].

Lemma size_allpairs_dep f s t :
  size [seq f x y | x <- s, y <- t x] = sumn [seq size (t x) | x <- s].
Admitted.

Lemma allpairs0l f t : [seq f x y | x <- [::], y <- t x] = [::].
Admitted.

Lemma allpairs0r f s : [seq f x y | x <- s, y <- [::]] = [::].
Admitted.

Lemma allpairs1l f x t :
   [seq f x y | x <- [:: x], y <- t x] = [seq f x y | y <- t x].
Admitted.

Lemma allpairs1r f s y :
  [seq f x y | x <- s, y <- [:: y x]] = [seq f x (y x) | x <- s].
Admitted.

Lemma allpairs_cons f x s t :
  [seq f x y | x <- x :: s, y <- t x] =
    [seq f x y | y <- t x] ++ [seq f x y | x <- s, y <- t x].
Admitted.

Lemma eq_allpairs (f1 f2 : forall x, T x -> R) s t :
    (forall x, f1 x =1 f2 x) ->
  [seq f1 x y | x <- s, y <- t x] = [seq f2 x y | x <- s, y <- t x].
Admitted.

Lemma eq_allpairsr (f : forall x, T x -> R) s t1 t2 : (forall x, t1 x = t2 x) ->
  [seq f x y | x <- s, y <- t1 x] = [seq f x y | x <- s, y <- t2 x].
Admitted.

Lemma allpairs_cat f s1 s2 t :
  [seq f x y | x <- s1 ++ s2, y <- t x] =
    [seq f x y | x <- s1, y <- t x] ++ [seq f x y | x <- s2, y <- t x].
Admitted.

Lemma allpairs_rcons f x s t :
  [seq f x y | x <- rcons s x, y <- t x] =
    [seq f x y | x <- s, y <- t x] ++ [seq f x y | y <- t x].
Admitted.

Lemma allpairs_mapl f (g : S' -> S) s t :
  [seq f x y | x <- map g s, y <- t x] = [seq f (g x) y | x <- s, y <- t (g x)].
Admitted.

Lemma allpairs_mapr f (g : forall x, T' x -> T x) s t :
  [seq f x y | x <- s, y <- map (g x) (t x)] =
    [seq f x (g x y) | x <- s, y <- t x].
Admitted.

End AllPairsDep.

Arguments allpairs_dep {S T R} f s t /.

Lemma map_allpairs S T R R' (g : R' -> R) f s t :
  map g [seq f x y | x : S <- s, y : T x <- t x] =
    [seq g (f x y) | x <- s, y <- t x].
Admitted.

Section AllPairsNonDep.

Variables (S T R : Type) (f : S -> T -> R).
Implicit Types (s : seq S) (t : seq T).

Definition allpairs s t := [seq f x y | x <- s, y <- t].

Lemma size_allpairs s t : size [seq f x y | x <- s, y <- t] = size s * size t.
Admitted.

End AllPairsNonDep.

Arguments allpairs {S T R} f s t /.

Section EqAllPairsDep.

Variables (S : eqType) (T : S -> eqType).
Implicit Types (R : eqType) (s : seq S) (t : forall x, seq (T x)).

Lemma allpairsPdep R (f : forall x, T x -> R) s t (z : R) :
  reflect (exists x y, [/\ x \in s, y \in t x & z = f x y])
          (z \in [seq f x y | x <- s, y <- t x]).
Admitted.

Variable R : eqType.
Implicit Type f : forall x, T x -> R.

Lemma allpairs_f_dep f s t x y :
  x \in s -> y \in t x -> f x y \in [seq f x y | x <- s, y <- t x].
Admitted.

Lemma eq_in_allpairs_dep f1 f2 s t :
    {in s, forall x, {in t x, f1 x =1 f2 x}} <->
  [seq f1 x y : R | x <- s, y <- t x] = [seq f2 x y | x <- s, y <- t x].
Admitted.

Lemma mem_allpairs_dep f s1 t1 s2 t2 :
    s1 =i s2 -> {in s1, forall x, t1 x =i t2 x} ->
  [seq f x y | x <- s1, y <- t1 x] =i [seq f x y | x <- s2, y <- t2 x].
Admitted.

Lemma allpairs_uniq_dep f s t (st := [seq Tagged T y | x <- s, y <- t x]) :
  let g (p : {x : S & T x}) : R := f (tag p) (tagged p) in
    uniq s -> {in s, forall x, uniq (t x)} -> {in st &, injective g} ->
  uniq [seq f x y | x <- s, y <- t x].
Admitted.

End EqAllPairsDep.

Arguments allpairsPdep {S T R f s t z}.

Section MemAllPairs.

Variables (S : Type) (T : S -> Type) (R : eqType).
Implicit Types (f : forall x, T x -> R) (s : seq S).

Lemma perm_allpairs_catr f s t1 t2 :
  perm_eql [seq f x y | x <- s, y <- t1 x ++ t2 x]
           ([seq f x y | x <- s, y <- t1 x] ++ [seq f x y | x <- s, y <- t2 x]).
Admitted.

Lemma mem_allpairs_catr f s y0 t :
  [seq f x y | x <- s, y <- y0 x ++ t x] =i
    [seq f x y | x <- s, y <- y0 x] ++ [seq f x y | x <- s, y <- t x].
Admitted.

Lemma perm_allpairs_consr f s y0 t :
  perm_eql [seq f x y | x <- s, y <- y0 x :: t x]
           ([seq f x (y0 x) | x <- s] ++ [seq f x y | x <- s, y <- t x]).
Admitted.

Lemma mem_allpairs_consr f s t y0 :
  [seq f x y | x <- s, y <- y0 x :: t x] =i
  [seq f x (y0 x) | x <- s] ++ [seq f x y | x <- s, y <- t x].
Admitted.

Lemma allpairs_rconsr f s y0 t :
  perm_eql [seq f x y | x <- s, y <- rcons (t x) (y0 x)]
           ([seq f x y | x <- s, y <- t x] ++ [seq f x (y0 x) | x <- s]).
Admitted.

Lemma mem_allpairs_rconsr f s t y0 :
  [seq f x y | x <- s, y <- rcons (t x) (y0 x)] =i
    ([seq f x y | x <- s, y <- t x] ++ [seq f x (y0 x) | x <- s]).
Admitted.

End MemAllPairs.

Lemma all_allpairsP
      (S : eqType) (T : S -> eqType) (R : Type)
      (p : pred R) (f : forall x : S, T x -> R)
      (s : seq S) (t : forall x : S, seq (T x)) :
  reflect (forall (x : S) (y : T x), x \in s -> y \in t x -> p (f x y))
          (all p [seq f x y | x <- s, y <- t x]).
Admitted.

Arguments all_allpairsP {S T R p f s t}.

Section EqAllPairs.

Variables S T R : eqType.
Implicit Types (f : S -> T -> R) (s : seq S) (t : seq T).

Lemma allpairsP f s t (z : R) :
  reflect (exists p, [/\ p.1 \in s, p.2 \in t & z = f p.1 p.2])
          (z \in [seq f x y | x <- s, y <- t]).
Admitted.

Lemma allpairs_f f s t x y :
  x \in s -> y \in t -> f x y \in [seq f x y | x <- s, y <- t].
Admitted.

Lemma eq_in_allpairs f1 f2 s t :
    {in s & t, f1 =2 f2} <->
  [seq f1 x y : R | x <- s, y <- t] = [seq f2 x y | x <- s, y <- t].
Admitted.

Lemma mem_allpairs f s1 t1 s2 t2 :
    s1 =i s2 -> t1 =i t2 ->
  [seq f x y | x <- s1, y <- t1] =i [seq f x y | x <- s2, y <- t2].
Admitted.

Lemma allpairs_uniq f s t (st := [seq (x, y) | x <- s, y <- t]) :
    uniq s -> uniq t -> {in st &, injective (prod_curry f)} ->
  uniq [seq f x y | x <- s, y <- t].
Admitted.

End EqAllPairs.

Arguments allpairsP {S T R f s t z}.
Arguments perm_nilP {T s}.
Arguments perm_consP {T x s t}.

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
Import mathcomp.ssreflect.ssreflect.
Import mathcomp.ssreflect.ssrfun.
Import mathcomp.ssreflect.ssrbool.
Import mathcomp.ssreflect.ssrnat.

Set Implicit Arguments.
Unset Strict Implicit.

Definition modn_rec d := fix loop m := if m - d is m'.+1 then loop m' else m.

Definition modn m d := if d > 0 then modn_rec d.-1 m else m.

Notation "m %% d" := (modn m d) : nat_scope.

Lemma ltn_pmod m d : 0 < d -> m %% d < d.
Admitted.

Import mathcomp.ssreflect.eqtype.

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
Admitted.

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
Admitted.
Canonical seq_choiceType := Eval hnf in ChoiceType (seq T) seq_choiceMixin.

End OneType.

Section TagChoice.

Variables (I : choiceType) (T_ : I -> choiceType).

Fact tagged_choiceMixin : choiceMixin {i : I & T_ i}.
Admitted.
Canonical tagged_choiceType :=
  Eval hnf in ChoiceType {i : I & T_ i} tagged_choiceMixin.

End TagChoice.

Fact nat_choiceMixin : choiceMixin nat.
Admitted.
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
Admitted.

Definition PcanCountMixin sT f f' (fK : pcancel f f') :=
  @CountMixin sT _ _ (pcan_pickleK fK).

Definition CanCountMixin sT f f' (fK : cancel f f') :=
  @PcanCountMixin sT _ _ (can_pcan fK).

Definition sub_countMixin P sT := PcanCountMixin (@valK T P sT).

Definition pickle_seq s := CodeSeq.code (map (@pickle T) s).
Definition unpickle_seq n := Some (pmap (@unpickle T) (CodeSeq.decode n)).
Lemma pickle_seqK : pcancel pickle_seq unpickle_seq.
Admitted.

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
Admitted.

Definition tag_countMixin := CountMixin pickle_taggedK.
Canonical tag_countType := Eval hnf in CountType {i : I & T_ i} tag_countMixin.

End TagCountType.

Section CountableDataTypes.

Implicit Type T : countType.

Lemma nat_pickleK : pcancel id (@Some nat).
Admitted.
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

Module Finite.

Section RawMixin.

Variable T : eqType.

Definition axiom e := forall x : T, count_mem x e = 1.

Lemma uniq_enumP e : uniq e -> e =i T -> axiom e.
Admitted.

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
Module Type CardDefSig.
Parameter card : card_type.
End CardDefSig.
Module CardDef : CardDefSig.
Definition card : card_type.
Admitted.
End CardDef.

Export CardDef.

Notation "#| A |" := (card (mem A))
  (at level 0, A at level 99, format "#| A |") : nat_scope.

Local Notation subset_type := (forall (T : finType) (A B : mem_pred T), bool).
Module Type SubsetDefSig.
Parameter subset : subset_type.
End SubsetDefSig.
Module Export SubsetDef : SubsetDefSig.
Definition subset : subset_type.
Admitted.
End SubsetDef.
Notation "A \subset B" := (subset (mem A) (mem B))
  (at level 70, no associativity) : bool_scope.

Section OpsTheory.

Variable T : finType.

Implicit Types (A B C D: {pred T}) (P Q : pred T) (x y : T) (s : seq T).

Section EnumPick.

Lemma mem_enum A : enum A =i A.
Admitted.

End EnumPick.

End OpsTheory.

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
Admitted.

Definition iinv A y fAy := s2val (@iinv_proof A y fAy).

End Image.

Lemma bool_enumP : Finite.axiom [:: true; false].
Admitted.
Definition bool_finMixin := Eval hnf in FinMixin bool_enumP.
Canonical bool_finType := Eval hnf in FinType bool bool_finMixin.

Local Notation enumF T := (Finite.enum T).

Section TransferFinType.

Variables (eT : countType) (fT : finType) (f : eT -> fT).

Lemma pcan_enumP g : pcancel f g -> Finite.axiom (undup (pmap g (enumF fT))).
Admitted.

Definition PcanFinMixin g fK := FinMixin (@pcan_enumP g fK).

End TransferFinType.

Section FinTypeForSub.

Variables (T : finType) (P : pred T) (sT : subCountType P).
Definition sub_enum : seq sT.
Admitted.

Lemma mem_sub_enum u : u \in sub_enum.
Admitted.

Lemma sub_enum_uniq : uniq sub_enum.
Admitted.

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
Definition ord_enum : seq ordinal.
Admitted.

Lemma ord_enum_uniq : uniq ord_enum.
Admitted.

Lemma mem_ord_enum i : i \in ord_enum.
Admitted.

Definition ordinal_finMixin :=
  Eval hnf in UniqFinMixin ord_enum_uniq mem_ord_enum.
Canonical ordinal_finType := Eval hnf in FinType ordinal ordinal_finMixin.

End OrdinalSub.

Notation "''I_' n" := (ordinal n)
  (at level 8, n at level 2, format "''I_' n").

Lemma cast_ord_proof n m (i : 'I_n) : n = m -> i < m.
Admitted.
Definition cast_ord n m eq_n_m i := Ordinal (@cast_ord_proof n m i eq_n_m).

Section EnumRank.

Variable T : finType.
Implicit Type A : {pred T}.

Lemma enum_rank_subproof x0 A : x0 \in A -> 0 < #|A|.
Admitted.

Definition enum_rank_in x0 A (Ax0 : x0 \in A) x :=
  insubd (Ordinal (@enum_rank_subproof x0 [eta A] Ax0)) (index x (enum A)).

Definition enum_rank x := @enum_rank_in x T (erefl true) x.

Lemma enum_default A : 'I_(#|A|) -> T.
Admitted.

Definition enum_val A i := nth (@enum_default [eta A] i) (enum A) i.

End EnumRank.

Definition bump h i := (h <= i) + i.

Lemma lift_subproof n h (i : 'I_n.-1) : bump h i < n.
Admitted.

Definition lift n (h : 'I_n) (i : 'I_n.-1) := Ordinal (lift_subproof h i).

Lemma lshift_subproof m n (i : 'I_m) : i < m + n.
Admitted.

Lemma rshift_subproof m n (i : 'I_n) : m + i < m + n.
Admitted.

Definition lshift m n (i : 'I_m) := Ordinal (lshift_subproof n i).
Definition rshift m n (i : 'I_n) := Ordinal (rshift_subproof m i).
Definition split {m n} (i : 'I_(m + n)) : 'I_m + 'I_n.
Admitted.

Section ProdFinType.

Variable T1 T2 : finType.

Definition prod_enum := [seq (x1, x2) | x1 <- enum T1, x2 <- enum T2].

Lemma prod_enumP : Finite.axiom prod_enum.
Admitted.

Definition prod_finMixin := Eval hnf in FinMixin prod_enumP.
Canonical prod_finType := Eval hnf in FinType (T1 * T2) prod_finMixin.

End ProdFinType.

Section TagFinType.

Variables (I : finType) (T_ : I -> finType).

Definition tag_enum :=
  flatten [seq [seq Tagged T_ x | x <- enumF (T_ i)] | i <- enumF I].

Lemma tag_enumP : Finite.axiom tag_enum.
Admitted.

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
Definition enum : seq (n.-tuple T).
Admitted.

Lemma enumP : Finite.axiom enum.
Admitted.

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
Local Definition tfgraph_inv (G : #|aT|.-tuple {x : aT & rT x}) : option fT.
Admitted.

Local Lemma tfgraphK : pcancel tfgraph tfgraph_inv.
Admitted.

End DepPlainTheory.
Arguments tfgraphK {aT rT} f : rename.

Section InheritedStructures.

Variable aT : finType.
Notation dffun_aT rT rS := {dffun forall x : aT, rT x : rS}.

Local Remark eqMixin rT : Equality.mixin_of (dffun_aT rT eqType).
Admitted.
Canonical finfun_eqType (rT : eqType) :=
  EqType {ffun aT -> rT} (eqMixin (fun=> rT)).
Canonical dfinfun_eqType rT :=
  EqType (dffun_aT rT eqType) (eqMixin rT).

Local Remark choiceMixin rT : Choice.mixin_of (dffun_aT rT choiceType).
Admitted.
Canonical finfun_choiceType (rT : choiceType) :=
  ChoiceType {ffun aT -> rT} (choiceMixin (fun=> rT)).
Canonical dfinfun_choiceType rT :=
  ChoiceType (dffun_aT rT choiceType) (choiceMixin rT).

Local Remark countMixin rT : Countable.mixin_of (dffun_aT rT countType).
Admitted.
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
Admitted.

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

Module Type ImsetSig.
Parameter imset : forall aT rT : finType,
 (aT -> rT) -> mem_pred aT -> {set rT}.
End ImsetSig.

Module Imset : ImsetSig.
Definition imset := imset_def.
End Imset.

Notation imset := Imset.imset.
Notation "f @: A" := (imset f (mem A)) (at level 24) : set_scope.

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
Admitted.

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
Definition one (R : ringType) : R.
exact (Ring.one (Ring.class R)).
Defined.
Definition mul (R : ringType) : R -> R -> R.
exact (Ring.mul (Ring.class R)).
Defined.
Definition exp R x n := nosimpl iterop _ n (@mul R) x (one R).
Definition comm R x y := @mul R x y = mul y x.

Local Notation "1" := (one _) : ring_scope.
Local Notation "n %:R" := (1 *+ n) : ring_scope.
Local Notation "*%R" := (@mul _) : fun_scope.
Local Notation "x * y" := (mul x y) : ring_scope.
Local Notation "x ^+ n" := (exp x n) : ring_scope.

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
Variable (phR : phant R) (T : Type) (cT : type phR).

Definition pack b0 (m0 : mixin_of R (@Zmodule.Pack T b0)) :=
  fun bT b & phant_id (Zmodule.class bT) b =>
  fun    m & phant_id m0 m => Pack phR (@Class T b m).

End ClassDef.

Module Import Exports.
Coercion sort : type >-> Sortclass.
Notation lmodType R := (type (Phant R)).
Notation LmodType R T m := (@pack _ (Phant R) T _ m _ _ id _ id).
Notation LmodMixin := Mixin.
End Exports.

End Lmodule.
Import Lmodule.Exports.
Definition scale (R : ringType) (V : lmodType R) : R -> V -> V.
Admitted.

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
Definition inv {R : unitRingType} : R -> R.
Admitted.

Local Notation "x ^-1" := (inv x).

Module ComUnitRing.

Section Mixin.

Variables (R : comRingType) (unit : pred R) (inv : R -> R).
Hypothesis mulVx : {in unit, left_inverse 1 inv *%R}.
Hypothesis unitPl : forall x y, y * x = 1 -> unit x.

Fact mulC_mulrV : {in unit, right_inverse 1 inv *%R}.
Admitted.

Fact mulC_unitP x y : y * x = 1 /\ x * y = 1 -> unit x.
Admitted.

Definition Mixin := UnitRingMixin mulVx mulC_mulrV mulC_unitP.

End Mixin.

Section ClassDef.
Record class_of (R : Type) : Type := Class {
  base : ComRing.class_of R;
  mixin : UnitRing.mixin_of (Ring.Pack base)
}.
Definition base2 R m := UnitRing.Class (@mixin R m).
Local Coercion base2 : class_of >-> UnitRing.class_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition ringType := @Ring.Pack cT class.
Definition unitRingType := @UnitRing.Pack cT class.

End ClassDef.

Module Import Exports.
Coercion base : class_of >-> ComRing.class_of.
Coercion base2 : class_of >-> UnitRing.class_of.
Coercion sort : type >-> Sortclass.
Canonical ringType.
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
Fixpoint eval (e : seq R) (t : term R) {struct t} : R.
exact (match t with
  | ('X_i)%T => e`_i
  | (x%:T)%T => x
  | (n%:R)%T => n%:R
  | (t1 + t2)%T => eval e t1 + eval e t2
  | (- t1)%T => - eval e t1
  | (t1 *+ n)%T => eval e t1 *+ n
  | (t1 * t2)%T => eval e t1 * eval e t2
  | t1^-1%T => (eval e t1)^-1
  | (t1 ^+ n)%T => eval e t1 ^+ n
  end).
Defined.
Fixpoint holds (e : seq R) (f : formula R) {struct f} : Prop.
exact (match f with
  | Bool b => b
  | (t1 == t2)%T => eval e t1 = eval e t2
  | Unit t1 => eval e t1 \in unit
  | (f1 /\ f2)%T => holds e f1 /\ holds e f2
  | (f1 \/ f2)%T => holds e f1 \/ holds e f2
  | (f1 ==> f2)%T => holds e f1 -> holds e f2
  | (~ f1)%T => ~ holds e f1
  | ('exists 'X_i, f1)%T => exists x, holds (set_nth 0 e i x) f1
  | ('forall 'X_i, f1)%T => forall x, holds (set_nth 0 e i x) f1
  end).
Defined.

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
Admitted.

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
Admitted.

Fact inv_out : {in predC (predC1 0), inv =1 id}.
Admitted.

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

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
Definition zmodType := @Zmodule.Pack cT class.
Definition ringType := @Ring.Pack cT class.
Definition comRingType := @ComRing.Pack cT class.
Definition comUnitRingType := @ComUnitRing.Pack cT class.
Definition idomainType := @IntegralDomain.Pack cT class.

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> IntegralDomain.class_of.
Canonical eqType.
Canonical choiceType.
Canonical zmodType.
Canonical ringType.
Canonical comRingType.
Coercion comUnitRingType : type >-> ComUnitRing.type.
Canonical comUnitRingType.
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
Definition comRingType := @ComRing.Pack cT class.
Definition comUnitRingType := @ComUnitRing.Pack cT class.
Definition fieldType := @Field.Pack cT class.

End ClassDef.

Module Export Exports.
Coercion mixin : class_of >-> mixin_of.
Canonical comRingType.
Coercion comUnitRingType : type >-> ComUnitRing.type.
Canonical fieldType.
Notation decFieldType := type.
End Exports.

End DecidableField.

Section DecidableFieldTheory.

Variable F : decFieldType.

Definition sat := DecidableField.sat (DecidableField.class F).

Lemma satP : DecidableField.axiom sat.
Admitted.

End DecidableFieldTheory.

Module Export Theory.
Definition subr_eq0 := subr_eq0.
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
Infix "*" := mul.

Lemma mk_invgK : involutive inv.
Admitted.

Lemma mk_invMg : {morph inv : x y / x * y >-> y * x}.
Admitted.

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
Coercion base : type >-> base_type.
Coercion arg_finType : base_type >-> Finite.type.
Notation baseFinGroupType := base_type.
Notation finGroupType := type.
Notation BaseFinGroupType T m := (@pack_base T m _ _ id).
Notation FinGroupType := Pack.

Section ElementOps.

Variable T : baseFinGroupType.
Notation rT := (FinGroup.sort T).
Definition oneg : rT.
Admitted.
Definition mulg : T -> T -> rT.
Admitted.

End ElementOps.

Notation "1" := (oneg _) : group_scope.
Notation "x1 * x2" := (mulg x1 x2) : group_scope.

Section BaseSetMulDef.

Variable gT : baseFinGroupType.
Definition group_set_baseGroupMixin : FinGroup.mixin_of (set_type gT).
Admitted.

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
Definition group_of of phant gT : predArgType.
exact (group_type).
Defined.
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
Admitted.

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
Admitted.

Lemma perm_onto s : codom s =i predT.
Admitted.

Definition perm_one := perm (@inj_id T).

Lemma perm_invK s : cancel (fun x => iinv (perm_onto s x)) s.
Admitted.

Definition perm_inv s := perm (can_inj (perm_invK s)).

Definition perm_mul s t := perm (inj_comp (@perm_inj t) (@perm_inj s)).

Lemma perm_oneP : left_id perm_one perm_mul.
Admitted.

Lemma perm_invP : left_inverse perm_one perm_inv perm_mul.
Admitted.

Lemma perm_mulP : associative perm_mul.
Admitted.
Definition perm_of_baseFinGroupMixin : FinGroup.mixin_of (perm_type T).
exact (FinGroup.Mixin perm_mulP perm_oneP perm_invP).
Defined.
Canonical perm_baseFinGroupType :=
  Eval hnf in BaseFinGroupType (perm_type T) perm_of_baseFinGroupMixin.
Canonical perm_finGroupType := @FinGroupType perm_baseFinGroupType perm_invP.

Lemma tperm_proof x y : involutive [fun z => z with x |-> y, y |-> x].
Admitted.

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
Definition Zp0 : 'I_p.
Admitted.
Definition Zp_opp x := inZp (p - x).
Definition Zp_add x y := inZp (x + y).

Lemma Zp_add0z : left_id Zp0 Zp_add.
Admitted.

Lemma Zp_addNz : left_inverse Zp0 Zp_opp Zp_add.
Admitted.

Lemma Zp_addA : associative Zp_add.
Admitted.

Lemma Zp_addC : commutative Zp_add.
Admitted.

Definition Zp_zmodMixin := ZmodMixin Zp_addA Zp_addC Zp_add0z Zp_addNz.
Canonical Zp_zmodType := Eval hnf in ZmodType 'I_p Zp_zmodMixin.

End ZpDef.
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
Admitted.
Definition const_mx m n a : 'M[R]_(m, n) := \matrix[const_mx_key]_(i, j) a.

Section FixedDim.

Variables m n : nat.
Implicit Type A : 'M[R]_(m, n).

Definition castmx m' n' (eq_mn : (m = m') * (n = n')) A : 'M_(m', n') :=
  let: erefl in _ = m' := eq_mn.1 return 'M_(m', n') in
  let: erefl in _ = n' := eq_mn.2 return 'M_(m, n') in A.

Fact row_perm_key : unit.
Admitted.
Definition row_perm (s : 'S_m) A := \matrix[row_perm_key]_(i, j) A (s i) j.
Fact col_perm_key : unit.
Admitted.
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
Admitted.

Definition mxvec_index (i : 'I_m) (j : 'I_n) :=
  cast_ord mxvec_cast (enum_rank (i, j)).

Definition mxvec (A : 'M[R]_(m, n)) :=
  castmx (erefl _, mxvec_cast) (\row_k A (enum_val k).1 (enum_val k).2).

Fact vec_mx_key : unit.
Admitted.
Definition vec_mx (u : 'rV[R]_(m * n)) :=
  \matrix[vec_mx_key]_(i, j) u 0 (mxvec_index i j).

End VecMatrix.

End MatrixStructural.

Arguments const_mx {R m n}.

Section MapMatrix.

Variables (aT rT : Type) (f : aT -> rT).

Fact map_mx_key : unit.
Admitted.
Definition map_mx m n (A : 'M_(m, n)) := \matrix[map_mx_key]_(i, j) f (A i j).

End MapMatrix.

Section MatrixZmodule.

Variable V : zmodType.

Section FixedDim.

Variables m n : nat.
Implicit Types A B : 'M[V]_(m, n).

Fact oppmx_key : unit.
Admitted.
Fact addmx_key : unit.
Admitted.
Definition oppmx A := \matrix[oppmx_key]_(i, j) (- A i j).
Definition addmx A B := \matrix[addmx_key]_(i, j) (A i j + B i j).

Lemma addmxA : associative addmx.
Admitted.

Lemma addmxC : commutative addmx.
Admitted.

Lemma add0mx : left_id (const_mx 0) addmx.
Admitted.

Lemma addNmx : left_inverse (const_mx 0) oppmx addmx.
Admitted.

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
Admitted.
Definition scalemx x A := \matrix[scalemx_key]_(i, j) (x * A i j).

Local Notation "x *m: A" := (scalemx x A) (at level 40) : ring_scope.

Lemma scale1mx A : 1 *m: A = A.
Admitted.

Lemma scalemxDl A x y : (x + y) *m: A = x *m: A + y *m: A.
Admitted.

Lemma scalemxDr x A B : x *m: (A + B) = x *m: A + x *m: B.
Admitted.

Lemma scalemxA x y A : x *m: (y *m: A) = (x * y) *m: A.
Admitted.

Definition matrix_lmodMixin :=
  LmodMixin scalemxA scale1mx scalemxDr scalemxDl.

Canonical matrix_lmodType :=
  Eval hnf in LmodType R 'M[R]_(m, n) matrix_lmodMixin.

End RingModule.

Section ScalarMx.

Variable n : nat.

Fact scalar_mx_key : unit.
Admitted.
Definition scalar_mx x : 'M[R]_n :=
  \matrix[scalar_mx_key]_(i , j) (x *+ (i == j)).

End ScalarMx.

Notation "x %:M" := (scalar_mx _ x) : ring_scope.

Fact mulmx_key : unit.
Admitted.
Definition mulmx {m n p} (A : 'M_(m, n)) (B : 'M_(n, p)) : 'M[R]_(m, p) :=
  \matrix[mulmx_key]_(i, k) \sum_j (A i j * B j k).

Local Notation "A *m B" := (mulmx A B) : ring_scope.

Lemma mulmxA m n p q (A : 'M_(m, n)) (B : 'M_(n, p)) (C : 'M_(p, q)) :
  A *m (B *m C) = A *m B *m C.
Admitted.

Lemma mulmxDl m n p (A1 A2 : 'M_(m, n)) (B : 'M_(n, p)) :
  (A1 + A2) *m B = A1 *m B + A2 *m B.
Admitted.

Lemma mulmxDr m n p (A : 'M_(m, n)) (B1 B2 : 'M_(n, p)) :
  A *m (B1 + B2) = A *m B1 + A *m B2.
Admitted.

Lemma mul1mx m n (A : 'M_(m, n)) : 1%:M *m A = A.
Admitted.

Lemma mulmx1 m n (A : 'M_(m, n)) : A *m 1%:M = A.
Admitted.

Section Trace.

Variable n : nat.

Definition mxtrace (A : 'M[R]_n) := \sum_i A i i.

End Trace.

Section MatrixRing.

Variable n' : nat.
Local Notation n := n'.+1.

Lemma matrix_nonzero1 : 1%:M != 0 :> 'M_n.
Admitted.

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
Admitted.
Definition adjugate n (A : 'M_n) := \matrix[adjugate_key]_(i, j) cofactor A j i.

End MatrixAlgebra.
Arguments scalar_mx {R n}.
Prenex Implicits mulmx mxtrace determinant cofactor adjugate.

Notation "a %:M" := (scalar_mx a) : ring_scope.
Notation "A *m B" := (mulmx A B) : ring_scope.
Notation "'\det' A" := (determinant A) : ring_scope.
Notation "'\adj' A" := (adjugate A) : ring_scope.

Section CommMx.

Context {R : ringType} {n : nat}.
Implicit Types (f g p : 'M[R]_n) (fs : seq 'M[R]_n) (d : 'rV[R]_n) (I : Type).
Definition comm_mx  f g : Prop.
exact (f *m g =  g *m f).
Defined.

End CommMx.

Section ComMatrix.

Variable R : comRingType.

Lemma comm_mx_scalar n a (A : 'M[R]_n) : comm_mx A a%:M.
Admitted.

End ComMatrix.
Arguments comm_mx_scalar {R n}.

Section MatrixInv.

Variables R : comUnitRingType.

Section Defs.

Variable n : nat.
Definition unitmx : pred 'M[R]_n.
Admitted.
Definition invmx A := if A \in unitmx then (\det A)^-1 *: \adj A else A.

Lemma mulVmx : {in unitmx, left_inverse 1%:M invmx mulmx}.
Admitted.

Lemma mulmxV : {in unitmx, right_inverse 1%:M invmx mulmx}.
Admitted.

Lemma intro_unitmx A B : B *m A = 1%:M /\ A *m B = 1%:M -> unitmx A.
Admitted.

Lemma invmx_out : {in [predC unitmx], invmx =1 id}.
Admitted.

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
Admitted.

Let LUr := locked_with Gaussian_elimination_key (@Gaussian_elimination) m n A.
Definition mxrank := if [|| m == 0 | n == 0]%N then 0%N else LUr.2.
Definition cokermx : 'M_n.
Admitted.
Definition pinvmx : 'M_(n, m).
Admitted.

End Defs.
Local Notation "\rank A" := (mxrank A) : nat_scope.

Definition submx_def := idfun (fun m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)) =>
  A *m cokermx B == 0).
Fact submx_key : unit.
Admitted.
Definition submx := locked_with submx_key submx_def.

Lemma mxrank_eq0 m n (A : 'M_(m, n)) : (\rank A == 0%N) = (A == 0).
Admitted.

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

Definition lead_coef p := p`_(size p).-1.
Definition polyC c : {poly R}.
Admitted.

Local Notation "c %:P" := (polyC c).
Definition cons_poly c p : {poly R}.
Admitted.

Definition Poly := foldr cons_poly 0%:P.

Definition poly_expanded_def n E := Poly (mkseq E n).
Fact poly_key : unit.
Admitted.
Definition poly := locked_with poly_key poly_expanded_def.
Local Notation "\poly_ ( i < n ) E" := (poly n (fun i : nat => E)).

Definition add_poly_def p q := \poly_(i < maxn (size p) (size q)) (p`_i + q`_i).
Fact add_poly_key : unit.
Admitted.
Definition add_poly := locked_with add_poly_key add_poly_def.

Definition opp_poly_def p := \poly_(i < size p) - p`_i.
Fact opp_poly_key : unit.
Admitted.
Definition opp_poly := locked_with opp_poly_key opp_poly_def.

Fact add_polyA : associative add_poly.
Admitted.

Fact add_polyC : commutative add_poly.
Admitted.

Fact add_poly0 : left_id 0%:P add_poly.
Admitted.

Fact add_polyN : left_inverse 0%:P opp_poly add_poly.
Admitted.

Definition poly_zmodMixin :=
  ZmodMixin add_polyA add_polyC add_poly0 add_polyN.

Canonical poly_zmodType := Eval hnf in ZmodType {poly R} poly_zmodMixin.

Definition mul_poly_def p q :=
  \poly_(i < (size p + size q).-1) (\sum_(j < i.+1) p`_j * q`_(i - j)).
Fact mul_poly_key : unit.
Admitted.
Definition mul_poly := locked_with mul_poly_key mul_poly_def.

Fact mul_polyA : associative mul_poly.
Admitted.

Fact mul_1poly : left_id 1%:P mul_poly.
Admitted.

Fact mul_poly1 : right_id 1%:P mul_poly.
Admitted.

Fact mul_polyDl : left_distributive mul_poly +%R.
Admitted.

Fact mul_polyDr : right_distributive mul_poly +%R.
Admitted.

Fact poly1_neq0 : 1%:P != 0 :> {poly R}.
Admitted.

Definition poly_ringMixin :=
  RingMixin mul_polyA mul_1poly mul_poly1 mul_polyDl mul_polyDr poly1_neq0.

Canonical poly_ringType := Eval hnf in RingType {poly R} poly_ringMixin.

Definition scale_poly_def a (p : {poly R}) := \poly_(i < size p) (a * p`_i).
Fact scale_poly_key : unit.
Admitted.
Definition scale_poly := locked_with scale_poly_key scale_poly_def.

Fact scale_polyA a b p : scale_poly a (scale_poly b p) = scale_poly (a * b) p.
Admitted.

Fact scale_1poly : left_id 1 scale_poly.
Admitted.

Fact scale_polyDr a : {morph scale_poly a : p q / p + q}.
Admitted.

Fact scale_polyDl p : {morph scale_poly^~ p : a b / a + b}.
Admitted.

Definition poly_lmodMixin :=
  LmodMixin scale_polyA scale_1poly scale_polyDr scale_polyDl.

Canonical poly_lmodType :=
  Eval hnf in LmodType R {poly R} poly_lmodMixin.
Definition polyX : {poly R}.
Admitted.
Fixpoint horner_rec s x := if s is a :: s' then horner_rec s' x * x + a else 0.
Definition horner p := horner_rec p.

End PolynomialTheory.
Notation "\poly_ ( i < n ) E" := (poly n (fun i => E)) : ring_scope.
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
Definition redivp : {poly R} -> {poly R} -> nat * {poly R} * {poly R}.
Admitted.

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
Admitted.
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
Admitted.
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
Admitted.

Lemma eval_mxrank e r m n (A : 'M_(m, n)) :
  qf_eval e (mxrank_form r A) = (\rank (eval_mx e A) == r).
Admitted.

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
Admitted.

End Env.

End MatrixFormula.
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

Definition gen1 := inFA (poly_rV 1).
Definition genM x y := inFA (poly_rV (pval x * pval y %% pA)).
Definition genV x := inFA (poly_rV (mx_inv_horner A (mxval x)^-1)).

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

Lemma gen_mulVr : GRing.Field.axiom genV.
Admitted.

Lemma gen_invr0 : genV 0 = 0.
Admitted.

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
