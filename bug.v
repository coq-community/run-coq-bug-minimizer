(* -*- mode: coq; coq-prog-args: ("-emacs" "-w" "-deprecated-native-compiler-option,-native-compiler-disabled" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/msl" "VST.msl" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/sepcomp" "VST.sepcomp" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/veric" "VST.veric" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/floyd" "VST.floyd" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/progs" "VST.progs" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/concurrency" "VST.concurrency" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/atomics" "VST.atomics" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/wand_demo" "wand_demo" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/sha" "sha" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/hmacfcf" "hmacfcf" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/tweetnacl20140427" "tweetnacl20140427" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/hmacdrbg" "hmacdrbg" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/aes" "aes" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/mailbox" "mailbox" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/lib" "compcert.lib" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/common" "compcert.common" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/x86_32" "compcert.x86_32" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/x86" "compcert.x86" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/cfrontend" "compcert.cfrontend" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/export" "compcert.export" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Flocq" "Flocq" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-top" "bug_01" "-native-compiler" "ondemand") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 2430 lines to 4 lines, then from 17 lines to 2017 lines, then from 2018 lines to 186 lines, then from 200 lines to 1181 lines, then from 1187 lines to 184 lines, then from 198 lines to 2668 lines, then from 2670 lines to 224 lines, then from 238 lines to 743 lines, then from 749 lines to 225 lines, then from 239 lines to 755 lines, then from 761 lines to 234 lines, then from 248 lines to 1669 lines, then from 1671 lines to 330 lines, then from 344 lines to 1282 lines, then from 1287 lines to 340 lines, then from 354 lines to 929 lines, then from 935 lines to 341 lines, then from 355 lines to 2252 lines, then from 2232 lines to 351 lines, then from 365 lines to 800 lines, then from 802 lines to 364 lines, then from 378 lines to 853 lines, then from 858 lines to 435 lines, then from 449 lines to 599 lines, then from 603 lines to 459 lines, then from 473 lines to 796 lines, then from 802 lines to 467 lines, then from 481 lines to 1447 lines, then from 1453 lines to 499 lines, then from 513 lines to 1949 lines, then from 1953 lines to 594 lines, then from 608 lines to 887 lines, then from 892 lines to 800 lines, then from 805 lines to 636 lines, then from 649 lines to 749 lines, then from 755 lines to 641 lines, then from 655 lines to 991 lines, then from 990 lines to 640 lines, then from 654 lines to 835 lines, then from 841 lines to 640 lines, then from 654 lines to 1475 lines, then from 1481 lines to 661 lines, then from 675 lines to 2571 lines, then from 2572 lines to 685 lines, then from 699 lines to 804 lines, then from 810 lines to 704 lines, then from 718 lines to 2159 lines, then from 2162 lines to 753 lines, then from 767 lines to 1424 lines, then from 1428 lines to 761 lines, then from 775 lines to 2786 lines, then from 2791 lines to 834 lines, then from 848 lines to 1050 lines, then from 1056 lines to 827 lines, then from 841 lines to 1967 lines, then from 1973 lines to 841 lines, then from 848 lines to 833 lines, then from 846 lines to 3494 lines, then from 3500 lines to 847 lines, then from 861 lines to 1643 lines, then from 1649 lines to 856 lines, then from 870 lines to 2363 lines, then from 2369 lines to 860 lines, then from 874 lines to 5852 lines, then from 5857 lines to 935 lines, then from 949 lines to 1035 lines, then from 1040 lines to 938 lines, then from 952 lines to 2995 lines, then from 3000 lines to 1416 lines, then from 1357 lines to 1015 lines, then from 1028 lines to 2352 lines, then from 2352 lines to 1018 lines, then from 1032 lines to 1358 lines, then from 1363 lines to 1028 lines, then from 1042 lines to 2449 lines, then from 2455 lines to 1057 lines, then from 1071 lines to 1157 lines, then from 1163 lines to 1071 lines, then from 1085 lines to 2006 lines, then from 2009 lines to 1079 lines, then from 1093 lines to 9102 lines, then from 9095 lines to 1811 lines, then from 1825 lines to 2371 lines, then from 2377 lines to 1834 lines, then from 1848 lines to 2249 lines, then from 2255 lines to 2056 lines *)
(* coqc version 8.16+alpha compiled with OCaml 4.13.0
   coqtop version runner-j1aldqxs-project-6138686-concurrent-0:/builds/coq/coq/_build/default,(HEAD detached at 3e1f200) (3e1f2002ec2d419c1713214c705fbfa902e28604)
   Modules that could not be inlined: VST.floyd.jmeq_lemmas, Flocq.IEEE754.Bits
   Expected coqc runtime on this file: 1.229 sec *)
Declare ML Module "ltac_plugin".
Module Export AdmitTactic.
Module Import LocalFalse.
Inductive False : Prop := .
End LocalFalse.
Axiom proof_admitted : False.
Global Set Default Proof Mode "Classic".
Tactic Notation "admit" := abstract case proof_admitted.
End AdmitTactic.
Require VST.msl.base.
Import VST.msl.base.

Require VST.msl.eq_dec.
Import VST.msl.eq_dec.

Require VST.msl.sepalg.
Import VST.msl.sepalg.

Require VST.msl.boolean_alg.
Import VST.msl.boolean_alg.

Require Coq.funind.Recdef.

Require Coq.ZArith.ZArith.
Import Coq.ZArith.ZArith.

Module Share <: SHARE_MODEL.

  Inductive ShareTree : Set :=
  | Leaf : bool -> ShareTree
  | Node : ShareTree -> ShareTree -> ShareTree
  .
Fixpoint canonicalTree (x:ShareTree) : Prop.
Admitted.

  Inductive shareTreeOrd : ShareTree -> ShareTree -> Prop :=
  | Leaf_Ord : forall b1 b2, implb b1 b2 = true ->
       shareTreeOrd (Leaf b1) (Leaf b2)
  | LeafNode_Ord : forall b l r,
       shareTreeOrd (Node (Leaf b) (Leaf b)) (Node l r) ->
       shareTreeOrd (Leaf b) (Node l r)
  | NodeLeaf_Ord : forall b l r,
       shareTreeOrd (Node l r) (Node (Leaf b) (Leaf b)) ->
       shareTreeOrd (Node l r) (Leaf b)
  | Node_Ord : forall l1 l2 r1 r2,
       shareTreeOrd l1 l2 ->
       shareTreeOrd r1 r2 ->
       shareTreeOrd (Node l1 r1) (Node l2 r2)
  .

  Definition canonTree :=  { t:ShareTree | canonicalTree t }.

  Module BA <: BOOLEAN_ALGEBRA.
    Definition t := canonTree.
    Definition Ord (x y:canonTree) := shareTreeOrd (proj1_sig x) (proj1_sig y).
Definition lub (x y:canonTree) : canonTree.
Admitted.
Definition glb (x y:canonTree) : canonTree.
Admitted.
Definition top : canonTree.
Admitted.
Definition bot : canonTree.
Admitted.
Definition comp (x:canonTree) : canonTree.
Admitted.

    Lemma ord_refl : forall x, Ord x x.
Admitted.

    Lemma ord_trans : forall x y z, Ord x y -> Ord y z -> Ord x z.
Admitted.

    Lemma ord_antisym : forall x y, Ord x y -> Ord y x -> x = y.
Admitted.

    Lemma lub_upper1 : forall x y, Ord x (lub x y).
Admitted.

    Lemma lub_upper2 : forall x y, Ord y (lub x y).
Admitted.

    Lemma lub_least : forall x y z,
      Ord x z -> Ord y z -> Ord (lub x y) z.
Admitted.

    Lemma glb_lower1 : forall x y, Ord (glb x y) x.
Admitted.

    Lemma glb_lower2 : forall x y, Ord (glb x y) y.
Admitted.

    Lemma glb_greatest : forall x y z,
      Ord z x -> Ord z y -> Ord z (glb x y).
Admitted.

    Lemma top_correct : forall x, Ord x top.
Admitted.

    Lemma bot_correct : forall x, Ord bot x.
Admitted.

    Lemma comp1 : forall x, lub x (comp x) = top.
Admitted.

    Lemma comp2 : forall x, glb x (comp x) = bot.
Admitted.

    Lemma nontrivial : top <> bot.
Admitted.

    Lemma distrib1 : forall x y z,
      glb x (lub y z) = lub (glb x y) (glb x z).
Admitted.

  End BA.

  Module BAF := BA_Facts BA.
  Include BAF.

    Definition rel (a x:t) : t.
Admitted.

    Lemma rel_inj_r : forall a1 a2 x, x <> bot -> rel a1 x = rel a2 x -> a1 = a2.
Admitted.

    Lemma rel_inj_l : forall a x y, a <> bot -> rel a x = rel a y -> x = y.
Admitted.

    Lemma rel_assoc : forall x y z, rel x (rel y z) = rel (rel x y) z.
Admitted.

    Lemma rel_bot1 : forall a, rel a bot = bot.
Admitted.

    Lemma rel_bot2 : forall x, rel bot x = bot.
Admitted.

    Lemma rel_top1 : forall a, rel a top = a.
Admitted.

    Lemma rel_top2 : forall x, rel top x = x.
Admitted.

    Lemma rel_preserves_glb : forall a x y, rel a (glb x y) = glb (rel a x) (rel a y).
Admitted.

    Lemma rel_preserves_lub : forall a x y, rel a (lub x y) = lub (rel a x) (rel a y).
Admitted.

    Definition leftTree : canonTree.
Admitted.

    Definition rightTree : canonTree.
Admitted.

    Definition split (x:canonTree) := (rel x leftTree, rel x rightTree).

    Lemma split_disjoint : forall x1 x2 x,
      split x = (x1, x2) -> glb x1 x2 = bot.
Admitted.

    Lemma split_together : forall x1 x2 x,
      split x = (x1, x2) -> lub x1 x2 = x.
Admitted.

    Lemma split_nontrivial : forall x1 x2 x,
      split x = (x1, x2) ->
        (x1 = bot \/ x2 = bot) ->
        x = bot.
Admitted.

    Inductive isTokenFactory' : ShareTree -> nat -> Prop :=
      | isTokFac_0 : isTokenFactory' (Leaf true) O
      | isTokFac_S_true : forall t n,
          isTokenFactory' t (S n) ->
          isTokenFactory' (Node (Leaf true) t) (S n)
      | isTokFac_S_false : forall t n,
          isTokenFactory' t n ->
          isTokenFactory' (Node (Leaf false) t) (S n).

    Inductive isToken' : ShareTree -> nat -> Prop :=
      | isTok_0 : isToken' (Leaf false) O
      | isTok_S_true : forall t n,
          isToken' t n ->
          isToken' (Node (Leaf true) t) (S n)
      | isTok_S_false : forall t n,
          isToken' t (S n) ->
          isToken' (Node (Leaf false) t) (S n).

    Definition isTokenFactory (x:t) (n:nat) := isTokenFactory' (proj1_sig x) n.
    Definition isToken (x:t) (n:nat) := isToken' (proj1_sig x) n.
Definition split_token (n:nat) (tok:t) : t * t.
Admitted.

    Lemma split_token_correct : forall n1 n2 tok tok1 tok2,
      isToken tok (n1+n2) ->
      split_token n1 tok = (tok1,tok2) ->
        isToken tok1 n1 /\
        isToken tok2 n2 /\
        join tok1 tok2 tok.
Admitted.
Definition create_token (n:nat) (fac:t) : t*t.
Admitted.

    Lemma create_token_correct : forall fac fac' tok x n,
      create_token n fac = (fac',tok) ->
      isTokenFactory fac x ->
         isTokenFactory fac' (n+x) /\
        isToken tok n /\
        join fac' tok fac.
Admitted.

    Local Open Scope nat_scope.

    Lemma absorbToken : forall fac fac' tok x n,
      isTokenFactory fac' (n+x) ->
      isToken tok n ->
      join fac' tok fac ->
      isTokenFactory fac x.
Admitted.

    Lemma mergeToken : forall tok1 n1 tok2 n2 tok',
      isToken tok1 n1 ->
      isToken tok2 n2 ->
      join tok1 tok2 tok' ->
      isToken tok' (n1+n2).
Admitted.

    Lemma factoryOverlap : forall f1 f2 n1 n2,
      isTokenFactory f1 n1 -> isTokenFactory f2 n2 -> glb f1 f2 <> bot.
Admitted.

    Lemma fullFactory : forall x, isTokenFactory x 0 <-> x = top.
Admitted.

    Lemma identityToken : forall x, isToken x 0 <-> x = bot.
Admitted.

    Lemma nonidentityToken : forall x n, (n > 0)%nat -> isToken x n -> x <> bot.
Admitted.

    Lemma nonidentityFactory : forall x n, isTokenFactory x n -> x <> bot.
Admitted.
Instance EqDec_share : EqDec t.
Admitted.

   Program Definition tree_decompose (ct : canonTree) :(canonTree * canonTree) :=
     let (t, pf) := ct in
     match t with
     |Leaf b => (Leaf b, Leaf b)
     |Node t1 t2 => (t1 ,t2)
     end.
Admit Obligations.
Instance decompose_tree : decomposible t.
exact (Decomposible tree_decompose).
Defined.
Fixpoint tree_heightP (t : ShareTree) : nat.
Admitted.

  Definition tree_height (t : canonTree) := tree_heightP (proj1_sig t).
  Definition tree_height_zero (t : canonTree) : {tree_height t = 0} + {tree_height t <> 0}.
Admitted.
Instance tree_heightable : heightable t.
exact (Heightable tree_height tree_height_zero).
Defined.

  Function unrel (t1 : t) (t2 : t) {measure tree_height t1} : t :=
   match t1 with
    | exist _ (Leaf b) _ => t2
    | _ => let (ltr1, rtr1) := decompose t1 in
           let (ltr2, rtr2) := decompose t2 in
              match ltr1 with
               | exist _ (Leaf true) _ => ltr2
               | exist _ (Leaf false) _ => unrel rtr1 rtr2
               | _ => unrel ltr1 ltr2
              end
   end.
Admitted.

Lemma unrel_rel: forall x sh,
    nonidentity x -> unrel x (rel x sh) = sh.
Admitted.
Definition Lsh  : Share.t.
exact (fst (Share.split Share.top)).
Defined.
Definition Rsh  : Share.t.
exact (snd (Share.split Share.top)).
Defined.
Definition splice (a b: t) : t.
exact (Share.lub (rel Lsh a) (rel Rsh b)).
Defined.

 Lemma unrel_splice_L:
  forall a b, unrel Lsh (splice a b) = a.
Admitted.

 Lemma unrel_splice_R:
  forall a b, unrel Rsh (splice a b) = b.
Admitted.

Lemma contains_Lsh_e:
   forall sh,
       join_sub Lsh sh -> unrel Lsh sh = top.
Admitted.

 Lemma contains_Rsh_e: forall sh,
       join_sub Rsh sh ->
       unrel Rsh sh = top.
Admitted.
Definition tree_round_left (n : nat) (t : canonTree) : option canonTree.
Admitted.
Instance  roundableL_tree : roundableLeft t.
exact (RoundableLeft tree_round_left).
Defined.
Definition tree_round_right (n : nat) (t : canonTree) : option canonTree.
Admitted.
Instance  roundableR_tree : roundableRight t.
exact (RoundableRight tree_round_right).
Defined.
Definition tree_avg (n : nat) (t1 t2 : canonTree) : option canonTree.
Admitted.
Instance avgable_tree : avgable t.
exact (Avgable tree_avg).
Defined.
Definition recompose (tt : (canonTree*canonTree)): canonTree.
Admitted.

  Lemma tree_round_left_zero : forall t, roundL 0 t = None.
Admitted.

  Lemma tree_round_left_identity : forall n t, height t < n ->
                                               roundL n t = Some t.
Admitted.

  Lemma tree_round_left_join : forall n t1 t2 t3 t1' t2' t3',
    join t1 t2 t3 ->
    roundL n t1 = Some t1' ->
    roundL n t2 = Some t2' ->
    roundL n t3 = Some t3' ->
    join t1' t2' t3'.
Admitted.

  Lemma tree_round_left_None : forall n t,
   n < height t ->
   roundL n t = None.
Admitted.

  Lemma tree_round_left_decrease : forall n t,
   S n = height t ->
   exists t', roundL (S n) t = Some t' /\ height t' <= n.
Admitted.

  Lemma tree_round_left_Some : forall n t,
   height t <= S n ->
   exists t', roundL (S n) t = Some t'.
Admitted.

  Lemma tree_round_left_height_compare : forall t t' n,
   roundL n t = Some t' ->
   height t' < n.
Admitted.

  Lemma tree_round_right_identity : forall n t,
   height t < n ->
   roundR n t = Some t.
Admitted.

  Lemma tree_round_right_join : forall n t1 t2 t3 t1' t2' t3',
    join t1 t2 t3 ->
    roundR n t1 = Some t1' ->
    roundR n t2 = Some t2' ->
    roundR n t3 = Some t3' ->
    join t1' t2' t3'.
Admitted.

  Lemma tree_round_right_None : forall n t,
   n < height t ->
   roundR n t = None.
Admitted.

  Lemma tree_round_right_decrease : forall n t,
   S n = height t ->
   exists t', roundR (S n) t = Some t' /\ height t' <= n.
Admitted.

 Lemma tree_round_right_Some : forall n t,
   height t <= S n ->
   exists t', roundR (S n) t = Some t'.
Admitted.

  Lemma tree_round_right_height_compare : forall t t' n,
   roundR n t = Some t' ->
   height t' < n.
Admitted.

  Lemma tree_round_right_zero : forall t, roundR 0 t = None.
Admitted.

  Lemma tree_avg_identity : forall n t,
   height t < n ->
   avg n t t = Some t.
Admitted.

  Lemma tree_avg_None : forall n t1 t2,
   n <= max (height t1) (height t2) ->
   avg n t1 t2 = None.
Admitted.

  Lemma tree_avg_round2avg : forall n t1 t2 t3,
   roundL n t3 = Some t1 ->
   roundR n t3 = Some t2 ->
   avg n t1 t2 = Some t3.
Admitted.

  Lemma tree_avg_avg2round : forall n t1 t2 t3,
   avg n t1 t2 = Some t3 ->
   roundL n t3 = Some t1 /\
   roundR n t3 = Some t2.
Admitted.

  Lemma tree_avg_join : forall n t11 t12 t13 t21 t22 t23 t31 t32 t33,
   avg n t11 t12 =  Some t13 ->
   avg n t21 t22 = Some t23 ->
   avg n t31 t32 = Some t33 ->
   join t11 t21 t31 ->
   join t12 t22 t32 ->
   join t13 t23 t33.
Admitted.

  Lemma tree_avg_ex: forall n t1 t2,
   height t1 < n ->
   height t2 < n ->
   exists t3, avg n t1 t2 = Some t3.
Admitted.

  Lemma avg_share_correct: forall n s,
   (height s <= S n)%nat ->
   exists s', exists s'',
    roundL (S n) s = Some s' /\
    roundR (S n) s = Some s'' /\
    avg (S n) s' s'' = Some s.
Admitted.

  Lemma decompose_recompose: forall t,
        decompose (recompose t) = t.
Admitted.

  Lemma recompose_decompose: forall t,
        recompose(decompose t) = t.
Admitted.

 Lemma decompose_height : forall n t1 t2 t3,
  height t1 = S n ->
  decompose t1 = (t2, t3) ->
  height t2 <= n /\ height t3 <= n.
Admitted.

 Lemma decompose_join : forall t1 t11 t12 t2 t21 t22 t3 t31 t32,
    decompose t1 = (t11, t12) ->
    decompose t2 = (t21, t22) ->
    decompose t3 = (t31, t32) ->
    (join t1 t2 t3 <->
    (join t11 t21 t31 /\ join t12 t22 t32)).
Admitted.
Definition countBLeafCT (n : nat) (s : canonTree) : nat.
Admitted.

Lemma decompose_height_le : forall n s s1 s2,
 decompose s = (s1,s2) ->
 height s <= S n ->
 height s1 <= n /\ height s2 <= n.
Admitted.

Lemma decompose_le: forall s1 s2 s11 s12 s21 s22,
 (s1 <= s2)%ba ->
 decompose s1 = (s11,s12) ->
 decompose s2 = (s21,s22) ->
 (s11 <= s21)%ba /\ (s12 <= s22)%ba.
Admitted.

Lemma decompose_diff: forall s1 s2 s11 s12 s21 s22,
 s1 <> s2 ->
 decompose s1 = (s11,s12) ->
 decompose s2 = (s21,s22) ->
 s11 <> s21 \/ s12 <> s22.
Admitted.

Lemma countBLeafCT_decompose : forall n s s1 s2,
 decompose s = (s1,s2) ->
 countBLeafCT (S n) s = countBLeafCT n s1 + countBLeafCT n s2.
Admitted.

Lemma countBLeafCT_le : forall n s1 s2,
  (s1 <= s2)%ba -> countBLeafCT n s1 <= countBLeafCT n s2.
Admitted.

Lemma countBLeafCT_lt : forall n s1 s2,
  (s1 <= s2)%ba ->
   s1 <> s2 ->
   height s2 <= n ->
   countBLeafCT n s1 < countBLeafCT n s2.
Admitted.
Fixpoint power (base : nat) (exp : nat) : nat.
Admitted.

Lemma countBLeafCT_limit: forall n s, countBLeafCT n s <= power 2 n.
Admitted.

Lemma countBLeafCT_bot: forall n, countBLeafCT n bot = 0.
Admitted.

Lemma countBLeafCT_top: forall n, countBLeafCT n top = power 2 n.
Admitted.

Lemma countBLeafCT_positive : forall s n,
 height s <= n -> bot <> s ->
 0 < countBLeafCT n s.
Admitted.

Lemma countBLeafCT_mono_le: forall n1 n2 s,
 n1 <= n2 ->
 countBLeafCT n1 s <= countBLeafCT n2 s .
Admitted.

Lemma countBLeafCT_mono_diff: forall n1 n2 s1 s2,
 n1 <= n2 ->
 (s1 <= s2)%ba ->
 countBLeafCT n1 s2 - countBLeafCT n1 s1 <= countBLeafCT n2 s2 - countBLeafCT n2 s1.
Admitted.

Lemma countBLeafCT_mono_lt: forall n1 n2 s,
 n1 < n2 ->
 0 < countBLeafCT n1 s ->
 countBLeafCT n1 s < countBLeafCT n2 s .
Admitted.

 Lemma tree_height_glb_limit: forall n s1 s2,
  height s1 <= n ->
  height s2 <= n ->
  height (glb s1 s2) <= n.
Admitted.

 Lemma height_glb1 : forall s1 s2,
  height s1 <= tree_height s2->
  height (glb s1 s2) <= height s2.
Admitted.

 Lemma tree_height_lub_limit: forall n s1 s2,
  height s1 <= n ->
  height s2 <= n ->
  height (lub s1 s2) <= n.
Admitted.

 Lemma height_lub1 : forall s1 s2,
  height s1 <= height s2->
  height (lub s1 s2) <= height s2.
Admitted.

 Lemma height_comp: forall s, height (comp s)= height s.
Admitted.

 Lemma countBLeafCT_join_le: forall n s1 s2 s3,
  join s1 s2 s3 ->
  countBLeafCT n s1 + countBLeafCT n s2 <= countBLeafCT n s3.
Admitted.

Lemma countBLeafCT_join_eq: forall n s1 s2 s3,
 join s1 s2 s3 ->
 height s1 <= n ->
 height s2 <= n ->
 countBLeafCT n s1 + countBLeafCT n s2 = countBLeafCT n s3.
Admitted.
Definition share_metric (n : nat) (s : canonTree) : nat.
Admitted.

 Lemma share_metric_nerr : forall s n,
  height s < n ->
  0 < share_metric n s.
Admitted.

 Lemma share_metric_err  : forall s n,
  n <= height s ->
  share_metric n s = 0.
Admitted.

 Lemma share_metric_height_monotonic : forall s n1 n2,
  n1<=n2 ->
  share_metric n1 s <= share_metric n2 s.
Admitted.

 Lemma share_metric_lub : forall s s' n,
  ~(s'<=s)%ba->
  0 < share_metric n s ->
  0 < share_metric n (lub s s') ->
  (share_metric n s<share_metric n (lub s s')).
Admitted.

 Lemma share_metric_glb : forall s s' n,
  ~(s<=s')%ba->
  0 < share_metric n s ->
  0 < share_metric n (glb s s') ->
 (share_metric n (glb s s') < share_metric n s)%nat.
Admitted.

 Lemma share_metric_dif_monotonic: forall s1 s2 n n0,
 (s1<=s2)%ba -> n<=n0 ->
  height s1 < n ->
  height s2 < n ->
 (share_metric n s2 - share_metric n s1 <=
  share_metric n0 s2 - share_metric n0 s1).
Admitted.

 Lemma leq_dec : forall (x y : t), {(x <= y)%ba} + {~ (x <= y)%ba}.
Admitted.

 Lemma height_top : height top = 0.
Admitted.

 Lemma height_bot: height bot = 0.
Admitted.

 Lemma height_zero_eq: forall t,
  height t = 0 -> {t = top} + {t = bot}.
Admitted.
Definition add (x y : canonTree) : option canonTree.
Admitted.

 Lemma add_join : forall t1 t2 t3,
  add t1 t2 = Some t3 <-> join t1 t2 t3.
Admitted.
Definition sub (x y : canonTree) : option canonTree.
Admitted.

 Lemma sub_join : forall t1 t2 t3,
  sub t1 t2 = Some t3 <-> join t2 t3 t1.
Admitted.

 Lemma decompose_share_height_no_increase: forall sh sh' sh'' ,
  decompose sh = (sh',sh'')->
  height sh' <= height sh /\ height sh'' <= height sh.
Admitted.

Lemma top_unrel: forall a,
 unrel top a = a.
Admitted.

Lemma bot_unrel: forall a,
 unrel bot a = a.
Admitted.

Lemma decompose_lub: forall t1 t11 t12 t2 t21 t22 t3 t31 t32,
 decompose t1 = (t11,t12) ->
 decompose t2 = (t21,t22) ->
 decompose t3 = (t31,t32) ->
 (lub t1 t2 = t3 <-> (lub t11 t21 = t31 /\ lub t12 t22 = t32)).
Admitted.

Lemma decompose_glb: forall t1 t11 t12 t2 t21 t22 t3 t31 t32,
 decompose t1 = (t11,t12) ->
 decompose t2 = (t21,t22) ->
 decompose t3 = (t31,t32) ->
 (glb t1 t2 = t3 <-> (glb t11 t21 = t31 /\ glb t12 t22 = t32)).
Admitted.

Lemma unrel_lub: forall a b1 b2,
 unrel a (lub b1 b2) = lub (unrel a b1) (unrel a b2).
Admitted.

Lemma unrel_glb: forall a b1 b2,
 unrel a (glb b1 b2) = glb (unrel a b1) (unrel a b2).
Admitted.

Lemma unrel_bot: forall a,
 unrel a bot = bot.
Admitted.

Lemma unrel_top: forall a,
 unrel a top = top.
Admitted.

Lemma unrel_join: forall x a b c,
 join a b c ->
 join (unrel x a) (unrel x b) (unrel x c).
Admitted.

Lemma unrel_disjoint: forall a a',
 a <> bot ->
 glb a a' = bot ->
 unrel a a' = bot.
Admitted.

Lemma decompose_height_zero: forall s sL sR,
  decompose s = (sL,sR) ->
  height s = 0 ->
  sL = s /\ sR = s.
Admitted.

Lemma decompose_equal: forall a b aL aR bL bR,
 decompose a = (aL,aR) ->
 decompose b = (bL,bR) ->
 (a = b <-> aL = bL /\ aR = bR).
Admitted.

Lemma decompose_nonzero: forall sL sR s,
 decompose s = (sL,sR) ->
 (s <> bot <-> sL <> bot \/ sR <> bot).
Admitted.

Lemma tree_avg_equal: forall sL sR sL' sR' s n,
 avg n sL sR = Some s ->
 avg n sL' sR' = Some s ->
 sL = sL' /\ sR = sR'.
Admitted.

Lemma tree_avg_zero: forall sL sR s n,
  avg n sL sR = Some s ->
  (s = bot <-> sL = bot /\ sR = bot).
Admitted.

Lemma tree_avg_nonzero: forall sL sR s n,
  avg n sL sR = Some s ->
  (s <> bot <-> sL <> bot \/ sR <> bot).
Admitted.

Lemma tree_avg_bound: forall sL sR s n,
  avg n sL sR = Some s -> (height s <= n)%nat.
Admitted.

Lemma Lsh_recompose: Lsh = recompose (top, bot).
Admitted.

Lemma Rsh_recompose: Rsh = recompose (bot,top).
Admitted.

Lemma decompose_Rsh: forall sh,
 unrel Rsh sh = snd (decompose sh).
Admitted.

Lemma decompose_Lsh: forall sh,
 unrel Lsh sh = fst (decompose sh).
Admitted.

Lemma rel_Lsh: forall sh,
rel Lsh sh = recompose (sh,bot).
Admitted.

Lemma rel_Rsh: forall sh,
rel Rsh sh = recompose (bot,sh).
Admitted.

Lemma lub_rel_recompose: forall sh1 sh2,
lub (rel Lsh sh1) (rel Rsh sh2) = recompose (sh1,sh2).
Admitted.

End Share.
Require VST.msl.knot_shims.
Require Coq.Logic.ClassicalFacts.
Require Coq.Logic.FunctionalExtensionality.
Require VST.msl.Axioms.
Require Coq.Logic.EqdepFacts.
Require VST.msl.Extensionality.
Require Coq.Lists.List.
Require Coq.Bool.Bool.
Require Coq.Relations.Relations.
Require Coq.micromega.Lia.
Require VST.msl.base.
Require Coq.funind.Recdef.
Require Coq.Wellfounded.Wellfounded.
Require VST.msl.ageable.
Require VST.msl.functors.
Require VST.msl.sepalg.
Require VST.msl.sepalg_generators.
Require VST.msl.sepalg_functors.
Require VST.msl.age_sepalg.
Require VST.msl.knot_full_variant.

Module Export VST_DOT_msl_DOT_knot_full_sa_WRAPPED.
Module Export knot_full_sa.
 
Import VST.msl.base.
Local Open Scope nat_scope.
Import VST.msl.ageable.
Import VST.msl.functors.
Import VST.msl.sepalg.
Import VST.msl.sepalg_functors.
Import VST.msl.sepalg_generators.
Import VST.msl.age_sepalg.
Import VST.msl.knot_full_variant.

Module Type KNOT_FULL_BASIC_INPUT.
  Parameter F: MixVariantFunctor.functor.
End KNOT_FULL_BASIC_INPUT.

Module Type KNOT_FULL_SA_INPUT.
  Declare Module KI: KNOT_FULL_BASIC_INPUT.
  Import MixVariantFunctor.
  Import KI.

  Parameter Join_F: forall A, Join (F A).
Existing Instance Join_F.
  Parameter paf_F : pafunctor F Join_F.
  Parameter Perm_F: forall A, Perm_alg (F A).
  Parameter Sep_F: forall A, Sep_alg (F A).
End KNOT_FULL_SA_INPUT.

Module Type KNOT_BASIC.
  Declare Module KI:KNOT_FULL_BASIC_INPUT.
  Import MixVariantFunctor.
  Import KI.
  Parameter knot: Type.
  Parameter ageable_knot : ageable knot.
  Existing Instance ageable_knot.

  Parameter predicate: Type.
  Parameter squash : (nat * F predicate) -> knot.
  Parameter unsquash : knot -> (nat * F predicate).
  Parameter approx : nat -> predicate -> predicate.

  Axiom squash_unsquash : forall k:knot, squash (unsquash k) = k.

  Axiom unsquash_squash : forall (n:nat) (f:F predicate),
    unsquash (squash (n,f)) = (n, fmap F (approx n) (approx n) f).

  Axiom knot_age1 : forall k:knot,
    age1 k =
    match unsquash k with
    | (O,_) => None
    | (S n,x) => Some (squash (n,x))
    end.

  Axiom knot_level : forall k:knot,
    level k = fst (unsquash k).

End KNOT_BASIC.

Module Type KNOT_BASIC_LEMMAS.

  Declare Module K: KNOT_BASIC.
  Import MixVariantFunctor.
  Import K.KI.
  Import K.

  Axiom unsquash_inj : forall k1 k2,
    unsquash k1 = unsquash k2 ->
    k1 = k2.

  Axiom unsquash_approx : forall k n Fp,
    unsquash k = (n, Fp) ->
    Fp = fmap F (approx n) (approx n) Fp.
  Arguments unsquash_approx [k n Fp] _.

  Axiom approx_approx1 : forall m n,
    approx n = approx n oo approx (m+n).

  Axiom approx_approx2 : forall m n,
    approx n = approx (m+n) oo approx n.

End KNOT_BASIC_LEMMAS.

Module Type KNOT_FULL_SA.
  Declare Module KI: KNOT_FULL_BASIC_INPUT.
  Declare Module KSAI: KNOT_FULL_SA_INPUT with Module KI := KI.
  Declare Module K: KNOT_BASIC with Module KI := KI.
  Declare Module KL: KNOT_BASIC_LEMMAS with Module K := K.

  Import KI.
  Import KSAI.
  Import K.
  Import KL.

  Parameter Join_knot: Join knot.
 Existing Instance Join_knot.
  Parameter Perm_knot : Perm_alg knot.
 Existing Instance Perm_knot.
  Parameter Sep_knot : Sep_alg knot.
 Existing Instance Sep_knot.
Instance Join_nat_F: Join (nat * F predicate). exact (Join_prod nat  (Join_equiv nat) (F predicate) _). Defined.
Instance Perm_nat_F : Perm_alg (nat * F predicate). exact (@Perm_prod nat _ _ _ (Perm_equiv _) (Perm_F _)). Defined.
Instance Sep_nat_F : Sep_alg (nat * F predicate). exact (@Sep_prod nat _ _ _ (Sep_equiv _) (Sep_F predicate)). Defined.

  Axiom join_unsquash : forall x1 x2 x3 : knot,
    join x1 x2 x3 = join (unsquash x1) (unsquash x2) (unsquash x3).
  Axiom core_unsquash : forall x, core x = squash (core (unsquash x)).

  Axiom asa_knot : Age_alg knot.

End KNOT_FULL_SA.

Module KnotFullSa
  (KSAI': KNOT_FULL_SA_INPUT)
  (K': KNOT_BASIC with Module KI:=KSAI'.KI)
  (KL': KNOT_BASIC_LEMMAS with Module K:=K'):
  KNOT_FULL_SA with Module KI := KSAI'.KI
               with Module KSAI := KSAI'
               with Module K:=K'
               with Module KL := KL'.

  Module KI := KSAI'.KI.
  Module KSAI := KSAI'.
  Module K := K'.
  Module KL := KL'.

  Import MixVariantFunctor.
  Import MixVariantFunctorLemmas.
  Import KI.
  Import KSAI.
  Import K.
  Import KL.
Instance Join_nat_F: Join (nat * F predicate). exact (Join_prod nat  (Join_equiv nat) (F predicate) _). Defined.
Instance Perm_nat_F : Perm_alg (nat * F predicate). exact (@Perm_prod nat _ _ _ (Perm_equiv _) (Perm_F _)). Defined.
Instance Sep_nat_F: Sep_alg (nat * F predicate). exact (@Sep_prod nat _ _ _ (Sep_equiv _) (Sep_F predicate)). Defined.

  Lemma unsquash_squash_join_hom : join_hom (unsquash oo squash).
Admitted.
Instance Join_knot : Join knot. exact (Join_preimage knot (nat * F predicate) Join_nat_F unsquash). Defined.

  Lemma join_unsquash : forall x1 x2 x3,
    join x1 x2 x3 =
    join (unsquash x1) (unsquash x2) (unsquash x3).
Admitted.
Instance Perm_knot : Perm_alg knot. exact (Perm_preimage _ _ _ _ unsquash squash squash_unsquash unsquash_squash_join_hom). Defined.
Instance Sep_knot: Sep_alg knot. exact (Sep_preimage _ _ _  unsquash squash squash_unsquash unsquash_squash_join_hom). Defined.

  Lemma core_unsquash : forall x, core x = squash (core (unsquash x)).
Admitted.

  Lemma age_join1 :
    forall x y z x' : K'.knot,
      join x y z ->
      age x x' ->
      exists y' : K'.knot,
        exists z' : K'.knot, join x' y' z' /\ age y y' /\ age z z'.
Admitted.

  Lemma age_join2 :
    forall x y z z' : K'.knot,
      join x y z ->
      age z z' ->
      exists x' : K'.knot,
        exists y' : K'.knot, join x' y' z' /\ age x x' /\ age y y'.
Admitted.

  Lemma unage_join1 : forall x x' y' z', join x' y' z' -> age x x' ->
    exists y, exists z, join x y z /\ age y y' /\ age z z'.
Admitted.

  Lemma unage_join2 :
    forall z x' y' z', join x' y' z' -> age z z' ->
      exists x, exists y, join x y z /\ age x x' /\ age y y'.
Admitted.

  Theorem asa_knot : @Age_alg knot _ K.ageable_knot.
Admitted.

End KnotFullSa.

End knot_full_sa.

End VST_DOT_msl_DOT_knot_full_sa_WRAPPED.
Module Export VST_DOT_msl_DOT_knot_full_sa.
Module Export VST.
Module Export msl.
Module Export knot_full_sa.
Include VST_DOT_msl_DOT_knot_full_sa_WRAPPED.knot_full_sa.
End knot_full_sa.

End msl.

End VST.

End VST_DOT_msl_DOT_knot_full_sa.

Instance cross_split_fun: forall A (JOIN: Join A) (key: Type),
          Cross_alg A -> Cross_alg (key -> A).
Proof.
repeat intro.
pose (f (x: key) := projT1 (X (a x) (b x) (c x) (d x) (z x) (H x) (H0 x))).
pose (g (x: key) := projT2 (X (a x) (b x) (c x) (d x) (z x) (H x) (H0 x))).
pose (ac (x: key) := fst (fst (fst (f x)))).
pose (ad (x: key) := snd (fst (fst (f x)))).
pose (bc (x: key) := snd (fst (f x))).
pose (bd (x: key) := snd (f x)).
exists (ac,ad,bc,bd).
unfold ac, ad, bc, bd, f; clear ac ad bc bd f.
repeat split; intro x; simpl;
generalize (g x);  destruct (projT1 (X (a x) (b x) (c x) (d x) (z x) (H x) (H0 x))) as [[[? ?] ?] ?]; simpl; intuition.
Qed.
Definition share : Type.
exact (Share.t).
Defined.
Section SM.

End SM.
Export VST.msl.ageable.
Export VST.msl.knot_shims.
Export VST.msl.knot_full_sa.
Export VST.msl.predicates_hered.
Export VST.msl.functors.
Export VST.msl.sepalg_functors.

Export MixVariantFunctor.
Export MixVariantFunctorGenerator.
Export Coq.ZArith.Znumtheory.
Definition peq: forall (x y: positive), {x = y} + {x <> y}.
Admitted.

Section POSITIVE_ITERATION.

End POSITIVE_ITERATION.

Section LIST_FOLD.

End LIST_FOLD.

Section FORALL2.

End FORALL2.
Definition proj_sumbool {P Q: Prop} (a: {P} + {Q}) : bool.
Admitted.

Coercion proj_sumbool: sumbool >-> bool.

Section DECIDABLE_EQUALITY.

End DECIDABLE_EQUALITY.

Section DECIDABLE_PREDICATE.

End DECIDABLE_PREDICATE.

Section LEX_ORDER.

End LEX_ORDER.

Lemma if_false: forall (A: Prop) (E: {A}+{~A}) (T: Type) (B C: T), ~A -> (if E then B else C) = C.
Admitted.

Tactic Notation "if_tac" :=
  match goal with |- context [if ?a then _ else _] =>
    lazymatch type of a with
    | sumbool _ _ =>destruct a as [?H | ?H]
    | bool => fail "Use simple_if_tac instead of if_tac, since your expression"a" has type bool"
    | ?t => fail "Use if_tac only for sumbool; your expression"a" has type" t
   end end.

Definition nonempty_share (sh: share) :=
       sepalg.nonidentity sh.
Definition readable_share (sh: share) :=
       nonempty_share (Share.glb Share.Rsh sh).
Require Coq.Classes.EquivDec.

Module Type TREE.
End TREE.

Module PTree <: TREE.
  Definition elt := positive.

  Inductive tree' (A: Type) : Type :=
  | Node001: tree' A -> tree' A
  | Node010: A -> tree' A
  | Node011: A -> tree' A -> tree' A
  | Node100: tree' A -> tree' A
  | Node101: tree' A -> tree' A ->tree' A
  | Node110: tree' A -> A -> tree' A
  | Node111: tree' A -> A -> tree' A -> tree' A.

  Inductive tree (A: Type) : Type :=
  | Empty : tree A
  | Nodes: tree' A -> tree A.

  Definition t := tree.
Definition get {A} (p: positive) (m: tree A) : option A.
Admitted.

  Section TREE_CASE.

  End TREE_CASE.

  Section TREE_REC.

  End TREE_REC.

  Section TREE_REC2.

  End TREE_REC2.

  Section TREE_IND.

  End TREE_IND.

  Section BOOLEAN_EQUALITY.

  End BOOLEAN_EQUALITY.

  Section COMBINE.

  End COMBINE.

Section TREE_FOLD_IND.

End TREE_FOLD_IND.

Section TREE_FOLD_REC.

End TREE_FOLD_REC.

Section MEASURE.

End MEASURE.

Section FORALL_EXISTS.

End FORALL_EXISTS.

Section BOOLEAN_EQUALITY.

End BOOLEAN_EQUALITY.

Section EXTENSIONAL_EQUALITY.

End EXTENSIONAL_EQUALITY.

Section OF_LIST.

End OF_LIST.

Notation "a ! b" := (PTree.get b a) (at level 1).
Require Flocq.IEEE754.Bits.
Module Export Archi.

Definition ptr64 := false.

Module Type WORDSIZE.
End WORDSIZE.

Module Make(WS: WORDSIZE).
Definition modulus : Z.
Admitted.
Definition max_unsigned : Z.
Admitted.
Definition max_signed : Z.
Admitted.
Definition min_signed : Z.
Admitted.

Record int: Type := mkint { intval: Z; intrange: -1 < intval < modulus }.
Definition unsigned (n: int) : Z.
Admitted.
Definition signed (n: int) : Z.
Admitted.
Definition repr (x: Z) : int.
Admitted.

Definition zero := repr 0.
Definition one  := repr 1.
Definition mone := repr (-1).
Definition eq (x y: int) : bool.
Admitted.

End Make.

Module Export Wordsize_32.
End Wordsize_32.

Module Int := Make(Wordsize_32).

Notation int := Int.int.

Module Export Wordsize_8.
End Wordsize_8.

Module Byte := Make(Wordsize_8).

Notation byte := Byte.int.

Module Export Wordsize_64.
End Wordsize_64.

Module Int64.

Include Make(Wordsize_64).

End Int64.

Notation int64 := Int64.int.

Module Export Wordsize_Ptrofs.
End Wordsize_Ptrofs.

Module Ptrofs.

Include Make(Wordsize_Ptrofs).
Definition to_int (x: int): Int.int.
Admitted.
Definition to_int64 (x: int): Int64.int.
Admitted.

Section AGREE32.

End AGREE32.

Section AGREE64.

End AGREE64.

End Ptrofs.

Notation ptrofs := Ptrofs.int.
Import Flocq.IEEE754.Bits.

Definition float := binary64.

Definition float32 := binary32.

Definition ident := positive.

Definition ident_eq := peq.

Record calling_convention : Type := mkcallconv {
  cc_vararg: option Z;
  cc_unproto: bool;
  cc_structret: bool
}.
Definition block : Type.
exact (positive).
Defined.

Inductive val: Type :=
  | Vundef: val
  | Vint: int -> val
  | Vlong: int64 -> val
  | Vfloat: float -> val
  | Vsingle: float32 -> val
  | Vptr: block -> ptrofs -> val.

Definition Vptrofs (n: ptrofs) :=
  if Archi.ptr64 then Vlong (Ptrofs.to_int64 n) else Vint (Ptrofs.to_int n).

Inductive quantity : Type := Q32 | Q64.

Inductive memval: Type :=
  | Undef: memval
  | Byte: byte -> memval
  | Fragment: val -> quantity -> nat -> memval.

Inductive signedness : Type :=
  | Signed: signedness
  | Unsigned: signedness.

Inductive intsize : Type :=
  | I8: intsize
  | I16: intsize
  | I32: intsize
  | IBool: intsize.

Inductive floatsize : Type :=
  | F32: floatsize
  | F64: floatsize.

Record attr : Type := mk_attr {
  attr_volatile: bool;
  attr_alignas: option N
}.

Inductive type : Type :=
  | Tvoid: type
  | Tint: intsize -> signedness -> attr -> type
  | Tlong: signedness -> attr -> type
  | Tfloat: floatsize -> attr -> type
  | Tpointer: type -> attr -> type
  | Tarray: type -> Z -> attr -> type
  | Tfunction: typelist -> type -> calling_convention -> type
  | Tstruct: ident -> attr -> type
  | Tunion: ident -> attr -> type
with typelist : Type :=
  | Tnil: typelist
  | Tcons: type -> typelist -> typelist.

Inductive struct_or_union : Type := Struct | Union.
Definition members : Type.
Admitted.

Record composite : Type := {
  co_su: struct_or_union;
  co_members: members;
  co_attr: attr;
  co_sizeof: Z;
  co_alignof: Z;
  co_rank: nat;
  co_sizeof_pos: co_sizeof >= 0;
  co_alignof_two_p: exists n, co_alignof = two_power_nat n;
  co_sizeof_alignof: (co_alignof | co_sizeof)
}.
Definition composite_env : Type.
exact (PTree.t composite).
Defined.
Fixpoint complete_type (env: composite_env) (t: type) : bool.
Admitted.
Fixpoint alignof (env: composite_env) (t: type) : Z.
Admitted.
Fixpoint sizeof (env: composite_env) (t: type) : Z.
Admitted.

Definition composite_env_consistent (env: composite_env) : Prop.
Admitted.

Section cuof.

Context (cenv: composite_env).
Definition composite_env_complete_legal_cosu_type: Prop.
Admitted.

End cuof.

Definition hardware_alignof_env_consistent (cenv: composite_env) (ha_env: PTree.t Z): Prop.
Admitted.
Definition hardware_alignof_env_complete (cenv: composite_env) (ha_env: PTree.t Z): Prop.
Admitted.

Module Type LEGAL_ALIGNAS.

  Parameter legal_alignas_obs: Type.

End LEGAL_ALIGNAS.

Module LegalAlignasDefsGen (LegalAlignas: LEGAL_ALIGNAS).

  Import LegalAlignas.
Definition legal_alignas_env_consistent (cenv: composite_env) (ha_env: PTree.t Z) (la_env: PTree.t legal_alignas_obs): Prop.
Admitted.
Definition legal_alignas_env_complete (cenv: composite_env) (la_env: PTree.t legal_alignas_obs): Prop.
Admitted.
Definition legal_alignas_env_sound (cenv: composite_env) (ha_env: PTree.t Z) (la_env: PTree.t legal_alignas_obs): Prop.
Admitted.

End LegalAlignasDefsGen.

Module Type LEGAL_ALIGNAS_FACTS.

  Declare Module LegalAlignas: LEGAL_ALIGNAS.
  Module LegalAlignasDefs := LegalAlignasDefsGen (LegalAlignas).
Export LegalAlignas.
Export LegalAlignasDefs.

End LEGAL_ALIGNAS_FACTS.

Module LegalAlignasStrong <: LEGAL_ALIGNAS.

Section legal_alignas.
Definition legal_alignas_obs: Type.
Admitted.

End legal_alignas.

End LegalAlignasStrong.

Module LegalAlignasStrongFacts: LEGAL_ALIGNAS_FACTS with Module LegalAlignas := LegalAlignasStrong.

Module LegalAlignas := LegalAlignasStrong.
Module LegalAlignasDefs := LegalAlignasDefsGen (LegalAlignas).

End LegalAlignasStrongFacts.

Module Export LegalAlignasFacts := LegalAlignasStrongFacts.
Definition composite_legal_fieldlist (co: composite): Prop.
Admitted.

Definition composite_env_legal_fieldlist env :=
  forall (id : positive) (co : composite),
    env ! id = Some co -> composite_legal_fieldlist co.
Class compspecs := mkcompspecs {
  cenv_cs : composite_env;
  cenv_consistent: composite_env_consistent cenv_cs;
  cenv_legal_fieldlist: composite_env_legal_fieldlist cenv_cs;
  cenv_legal_su: composite_env_complete_legal_cosu_type cenv_cs;
  ha_env_cs: PTree.t Z;
  ha_env_cs_consistent: hardware_alignof_env_consistent cenv_cs ha_env_cs;
  ha_env_cs_complete: hardware_alignof_env_complete cenv_cs ha_env_cs;
  la_env_cs: PTree.t legal_alignas_obs;
  la_env_cs_consistent: legal_alignas_env_consistent cenv_cs ha_env_cs la_env_cs;
  la_env_cs_complete: legal_alignas_env_complete cenv_cs la_env_cs;
  la_env_cs_sound: legal_alignas_env_sound cenv_cs ha_env_cs la_env_cs
}.

Existing Class composite_env.
Existing Instance cenv_cs.

Module Type ADR_VAL.
Parameter address : Type.

Parameter kind: Type.
End ADR_VAL.

Inductive TypeTree: Type :=
  | ConstType: Type -> TypeTree
  | CompspecsType: TypeTree
  | Mpred: TypeTree
  | DependentType: nat -> TypeTree
  | ProdType: TypeTree -> TypeTree -> TypeTree
  | ArrowType: TypeTree -> TypeTree -> TypeTree
  | SigType: forall (I : Type), (I -> TypeTree) -> TypeTree
  | PiType: forall (I : Type), (I -> TypeTree) -> TypeTree
  | ListType: TypeTree -> TypeTree.
Definition dependent_type_functor_rec (ts: list Type): TypeTree -> functor.
Admitted.

Module Type STRAT_MODEL.
  Declare Module AV : ADR_VAL.
Definition f_pre_rmap : functor.
Admitted.
Instance Join_pre_rmap (A: Type) : Join (f_pre_rmap A).
Admitted.
  Declare Instance Sep_pre_rmap: forall (A: Type), Sep_alg (f_pre_rmap A).
  Parameter paf_pre_rmap : @pafunctor f_pre_rmap Join_pre_rmap.

End STRAT_MODEL.

Module StratModel (AV' : ADR_VAL) : STRAT_MODEL with Module AV:=AV'.
  Module AV := AV'.
  Import AV.
Definition preds: functor.
Admitted.

  Inductive res (PRED : Type) : Type :=
    | NO':  forall sh: Share.t, ~(readable_share sh) -> res PRED
    | YES': forall sh: Share.t, readable_share sh -> kind -> preds PRED -> res PRED
    | PURE': kind -> preds PRED -> res PRED.
Definition res_fmap (A B:Type) (f:A->B) (g:B->A)(x:res A) : res B.
Admitted.

  Lemma ff_res : functorFacts res res_fmap.
Admitted.
Definition f_res : functor.
exact (Functor ff_res).
Defined.
Definition ghost (PRED : Type) : Type.
Admitted.
Definition ghost_fmap (A B:Type) (f:A->B) (g:B->A)(x:ghost A) : ghost B.
Admitted.

  Lemma ff_ghost : functorFacts ghost ghost_fmap.
Admitted.
Definition f_ghost : functor.
exact (Functor ff_ghost).
Defined.

  Definition pre_rmap (A:Type) := ((address -> res A) * ghost A)%type.
Definition f_pre_rmap : functor.
exact (fpair (ffunc (fconst address) f_res) f_ghost).
Defined.
Instance Join_pre_rmap (A: Type) : Join (pre_rmap A).
Admitted.
Definition paf_pre_rmap : @pafunctor f_pre_rmap Join_pre_rmap.
Admitted.
Definition Sep_pre_rmap (A: Type): Sep_alg (pre_rmap A).
Admitted.

End StratModel.

Module Type RMAPS.
  Declare Module AV:ADR_VAL.

  Parameter rmap : Type.
  Axiom ag_rmap: ageable rmap.
 Existing Instance ag_rmap.

End RMAPS.

Module Rmaps (AV':ADR_VAL): RMAPS with Module AV:=AV'.
  Module Export AV:=AV'.

  Module SM := StratModel(AV).
  Import SM.

  Module Export TyF.

    Definition F := f_pre_rmap.
  End TyF.

  Module TyFSA <: KNOT_FULL_SA_INPUT with Module KI:=TyF.
    Module KI := TyF.
Instance Join_F: forall A, Join (F A).
exact (_).
Defined.
Definition Perm_F : forall A, Perm_alg (F A).
Admitted.
    Definition Sep_F := Sep_pre_rmap.
    Definition paf_F := paf_pre_rmap.
  End TyFSA.

  Module K := Knot_MixVariantHeredProp(TyF).

  Definition rmap := K.knot.
Instance ag_rmap : ageable rmap.
Admitted.

End Rmaps.
Module Export Cop.

Inductive unary_operation : Type :=
  | Onotbool : unary_operation
  | Onotint : unary_operation
  | Oneg : unary_operation
  | Oabsfloat : unary_operation.

Inductive binary_operation : Type :=
  | Oadd : binary_operation
  | Osub : binary_operation
  | Omul : binary_operation
  | Odiv : binary_operation
  | Omod : binary_operation
  | Oand : binary_operation
  | Oor : binary_operation
  | Oxor : binary_operation
  | Oshl : binary_operation
  | Oshr : binary_operation
  | Oeq: binary_operation
  | One: binary_operation
  | Olt: binary_operation
  | Ogt: binary_operation
  | Ole: binary_operation
  | Oge: binary_operation.

Inductive expr : Type :=
  | Econst_int: int -> type -> expr
  | Econst_float: float -> type -> expr
  | Econst_single: float32 -> type -> expr
  | Econst_long: int64 -> type -> expr
  | Evar: ident -> type -> expr
  | Etempvar: ident -> type -> expr
  | Ederef: expr -> type -> expr
  | Eaddrof: expr -> type -> expr
  | Eunop: unary_operation -> expr -> type -> expr
  | Ebinop: binary_operation -> expr -> expr -> type -> expr
  | Ecast: expr -> type -> expr
  | Efield: expr -> ident -> type -> expr
  | Esizeof: type -> type -> expr
  | Ealignof: type -> type -> expr.
Definition typeof (e: expr) : type.
Admitted.

Definition address : Type.
Admitted.

Class NatDed (A: Type) := mkNatDed {
  andp: A -> A -> A;
  orp: A -> A -> A;
  exp: forall {T:Type}, (T -> A) -> A;
  allp: forall {T:Type}, (T -> A) -> A;
  imp: A -> A -> A;
  prop: Prop -> A;
  derives: A -> A -> Prop;
  pred_ext: forall P Q, derives P Q -> derives Q P -> P=Q;
  derives_refl: forall P, derives P P;
  derives_trans: forall P Q R, derives P Q -> derives Q R -> derives P R;
  TT := prop True;
  FF := prop False;
  andp_right:  forall X P Q:A, derives X P -> derives X Q -> derives X (andp P Q);
  andp_left1:  forall P Q R:A, derives P R -> derives (andp P Q) R;
  andp_left2:  forall P Q R:A, derives Q R -> derives (andp P Q) R;
  orp_left: forall P Q R, derives P R -> derives Q R -> derives (orp P Q) R;
  orp_right1: forall P Q R, derives P Q -> derives P (orp Q R);
  orp_right2: forall P Q R, derives P R -> derives P (orp Q R);
  exp_right: forall {B: Type} (x:B) (P: A) (Q: B -> A),
                        derives P (Q x) -> derives P (exp Q);
  exp_left: forall {B: Type} (P: B -> A) (Q: A),
                      (forall x, derives (P x) Q) -> derives (exp P) Q;
  allp_left: forall {B}(P: B -> A) x Q, derives (P x) Q -> derives (allp P) Q;
  allp_right: forall {B}(P: A) (Q: B -> A),  (forall v, derives P (Q v)) -> derives P (allp Q);
  imp_andp_adjoint: forall P Q R, derives (andp P Q) R <-> derives P (imp Q R);
  prop_left: forall (P: Prop) Q, (P -> derives TT Q) -> derives (prop P) Q;
  prop_right: forall (P: Prop) Q, P -> derives Q (prop P);
  prop_imp_prop_left: forall (P Q: Prop), derives (imp (prop P) (prop Q)) (prop (P -> Q));
  allp_prop_left: forall {B: Type} (P: B -> Prop), derives (allp (fun b => prop (P b))) (prop (forall b, P b))

}.

Program Instance LiftNatDed (A B: Type) {ND: NatDed B} : NatDed (A -> B) :=
 mkNatDed (A -> B)
      (fun P Q x => andp (P x) (Q x))
      (fun P Q x => orp (P x) (Q x))
      (fun T (F: T -> A -> B) (a: A) => exp (fun x => F x a))
      (fun T (F: T -> A -> B) (a: A) => allp (fun x => F x a))
      (fun P Q x => imp (P x) (Q x))
      (fun P x => prop P)
      (fun P Q => forall x, derives (P x) (Q x))
     _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _.
Admit Obligations.

Definition typesig := (list type * type)%type.

Inductive kind : Type := VAL : memval -> kind
                                   | LK : forall n i : Z, kind
                                   | FUN:  typesig -> calling_convention -> kind.

Module CompCert_AV <: ADR_VAL.

Definition address := address.
Definition kind := kind.

End CompCert_AV.

Module R := Rmaps (CompCert_AV).
Export R.
Definition force_val (v: option val) : val.
Admitted.

Definition force_val1 (f: val -> option val) (v: val) := force_val (f v).
Definition force_val2 (f: val -> val -> option val) (v1 v2: val) := force_val (f v1 v2).

Definition is_long (v: val) :=
 match v with Vlong i => True | _ => False end.

Definition isptr v :=
   match v with | Vptr _ _ => True | _ => False end.

Structure Lift := mkLift {
         lift_S: Type;
         lift_T: Type;
         lift_prod : Type;
         lift_last: Type;
         lifted:> Type;
         lift_curry: lift_T -> lift_prod -> lift_last;
         lift_uncurry_open: ((lift_S -> lift_prod) -> (lift_S -> lift_last)) -> lifted
}.

Definition Tend (S: Type) (A: Type) :=
    mkLift S A unit A
          (S -> A)
          (fun f _ => f)
          (fun f => f (fun _: S => tt)).
Canonical Structure Tarrow (A: Type) (H: Lift) :=
    mkLift (lift_S H)
      (A -> lift_T H)
      (prod A (lift_prod H))
      (lift_last H)
      ((lift_S H -> A) -> lifted H)
      (fun f x => match x with (x1,x2) => lift_curry H (f x1) x2 end)
      (fun f x => lift_uncurry_open H (fun y: lift_S H -> lift_prod H => f (fun z => (x z, y z)))).

Set Implicit Arguments.
Definition liftx {H: Lift} (f: lift_T H) : lifted H.
Admitted.
Notation "'`' x" := (liftx x) (at level 10, x at next level).

Notation "'`(' x ')'" := (liftx (x : _)).
Module Export Map.
Section map.
Variables (B : Type).

Definition t := positive -> option B.
Definition get (h: t) (a:positive) : option B.
exact (h a).
Defined.
Definition set (a:positive) (v: B) (h: t) : t.
exact (fun i => if ident_eq i a then Some v else h i).
Defined.

Lemma gso h x y v : x<>y -> get (set x v h) y = get h y.
unfold get, set; intros; if_tac; intuition.
Qed.

End map.

Section FUNSPEC.

Definition genviron := Map.t block.

Definition venviron := Map.t (block * type).

Definition tenviron := Map.t val.

Inductive environ : Type :=
 mkEnviron: forall (ge: genviron) (ve: venviron) (te: tenviron), environ.
Definition te_of (rho: environ) : tenviron.
Admitted.

Definition mpred := pred rmap.
Definition AssertTT (A: TypeTree): TypeTree.
Admitted.
Definition ArgsTT (A: TypeTree): TypeTree.
Admitted.
Definition super_non_expansive {A: TypeTree}
  (P: forall ts, dependent_type_functor_rec ts (AssertTT A) mpred): Prop.
Admitted.
Definition args_super_non_expansive {A: TypeTree}
  (P: forall ts, dependent_type_functor_rec ts (ArgsTT A) mpred): Prop.
Admitted.

Inductive funspec :=
   mk_funspec: typesig -> calling_convention -> forall (A: TypeTree)
     (P: forall ts, dependent_type_functor_rec ts (ArgsTT A) mpred)
     (Q: forall ts, dependent_type_functor_rec ts (AssertTT A) mpred)
     (P_ne: args_super_non_expansive P) (Q_ne: super_non_expansive Q),
     funspec.

End FUNSPEC.

Arguments sizeof {env} !t / .
Arguments alignof {env} !t / .

Definition eval_id (id: ident) (rho: environ) := force_val (Map.get (te_of rho) id).
Canonical Structure LiftEnviron := Tend environ.

Definition is_int (sz: intsize) (sg: signedness) (v: val) :=
  match v with
  | Vint i =>
    match sz, sg with
    | I8, Signed => Byte.min_signed <= Int.signed i <= Byte.max_signed
    | I8, Unsigned => Int.unsigned i <= Byte.max_unsigned
    | I16, Signed => -two_p (16-1) <= Int.signed i <= two_p (16-1) -1
    | I16, Unsigned => Int.unsigned i <= two_p 16 - 1
    | I32, _ => True
    | IBool, _ => i = Int.zero \/ i = Int.one
    end
  | _ => False
  end.
Definition tc_val (ty: type) : val -> Prop.
Admitted.

Inductive Annotation :=
  WeakAnnotation : (environ -> mpred) -> Annotation
| StrongAnnotation : (environ -> mpred) -> Annotation.

Inductive tycontext : Type :=
  mk_tycontext : forall (tyc_temps: PTree.t type)
                        (tyc_vars: PTree.t type)
                        (tyc_ret: type)
                        (tyc_globty: PTree.t type)
                        (tyc_globsp: PTree.t funspec)
                        (tyc_annot: PTree.t Annotation),
                             tycontext.

Module Export Clight_Cop2.
Definition sem_cast (t1 t2: type): val -> option val.
Admitted.
Definition sem_unary_operation
            (op: Cop.unary_operation) (ty: type) (v: val): option val.
Admitted.
Definition sem_binary_operation'
    {CS: compspecs} (op: Cop.binary_operation)
    (t1:type) (t2: type) : val -> val -> option val.
Admitted.

Definition eval_unop (op: Cop.unary_operation) (t1 : type) :=
       force_val1 (Clight_Cop2.sem_unary_operation op t1).

Definition eval_binop {CS:compspecs} (op: Cop.binary_operation) (t1 t2 : type) :=
       force_val2 (Clight_Cop2.sem_binary_operation'  op t1 t2).

Definition eval_cast (t1 t2 : type) :=
  force_val1 (sem_cast t1 t2).
Definition eval_field {CS: compspecs} (ty: type) (fld: ident) : val -> val.
Admitted.
Definition eval_var (id:ident) (ty: type) (rho: environ) : val.
Admitted.

Fixpoint eval_expr {CS: compspecs} (e: expr) : environ -> val :=
 match e with
 | Econst_int i ty => `(Vint i)
 | Econst_long i ty => `(Vlong i)
 | Econst_float f ty => `(Vfloat f)
 | Econst_single f ty => `(Vsingle f)
 | Etempvar id ty => eval_id id
 | Eaddrof a ty => eval_lvalue a
 | Eunop op a ty =>  `(eval_unop op (typeof a)) (eval_expr a)
 | Ebinop op a1 a2 ty =>
                  `(eval_binop op (typeof a1) (typeof a2)) (eval_expr a1) (eval_expr a2)
 | Ecast a ty => `(eval_cast (typeof a) ty) (eval_expr a)
 | Evar id ty => eval_var id ty
 | Ederef a ty => eval_expr a
 | Efield a i ty => `(eval_field (typeof a) i) (eval_lvalue a)
 | Esizeof t ty => `(if complete_type cenv_cs t
                             then Vptrofs (Ptrofs.repr (sizeof t)) else Vundef)
 | Ealignof t ty => `(if complete_type cenv_cs t
                             then Vptrofs (Ptrofs.repr (alignof t)) else Vundef)
 end

 with eval_lvalue {CS: compspecs} (e: expr) : environ -> val :=
 match e with
 | Evar id ty => eval_var id ty
 | Ederef a ty => eval_expr a
 | Efield a i ty => `(eval_field (typeof a) i) (eval_lvalue a)
 | _  => `Vundef
 end.
Definition eval_expropt {CS: compspecs} (e: option expr) : environ -> option val.
exact (match e with Some e' => `(@Some val) (eval_expr e')  | None => `None end).
Defined.

Inductive tc_error :=
| op_result_type : expr -> tc_error
| arg_type : expr -> tc_error
| pp_compare_size_0 : type -> tc_error
| pp_compare_size_exceed : type -> tc_error
| invalid_cast : type -> type -> tc_error
| invalid_cast_result : type -> type -> tc_error
| invalid_expression : expr -> tc_error
| var_not_in_tycontext : tycontext -> positive  -> tc_error
| mismatch_context_type : type -> type -> tc_error
| deref_byvalue : type -> tc_error
| volatile_load : type -> tc_error
| invalid_field_access : expr -> tc_error
| invalid_composite_name: ident -> tc_error
| invalid_struct_field : ident   -> ident   -> tc_error
| invalid_lvalue : expr -> tc_error
| wrong_signature : tc_error
| int_or_ptr_type_error : tc_error
| miscellaneous_typecheck_error : tc_error.

Inductive tc_assert :=
| tc_FF: tc_error -> tc_assert
| tc_TT : tc_assert
| tc_andp': tc_assert -> tc_assert -> tc_assert
| tc_orp' : tc_assert -> tc_assert -> tc_assert
| tc_nonzero': expr -> tc_assert
| tc_iszero': expr -> tc_assert
| tc_isptr: expr -> tc_assert
| tc_isint: expr -> tc_assert
| tc_islong: expr -> tc_assert
| tc_test_eq': expr -> expr -> tc_assert
| tc_test_order': expr -> expr -> tc_assert
| tc_ilt': expr -> int -> tc_assert
| tc_llt': expr -> int64 -> tc_assert
| tc_Zle: expr -> Z -> tc_assert
| tc_Zge: expr -> Z -> tc_assert
| tc_samebase: expr -> expr -> tc_assert
| tc_nodivover': expr -> expr -> tc_assert
| tc_initialized: PTree.elt -> type -> tc_assert
| tc_nosignedover: (Z->Z->Z) -> expr -> expr -> tc_assert.
Definition valid_pointer (p: val) : mpred.
Admitted.
Definition weak_valid_pointer (p: val) : mpred.
Admitted.

Lemma nth_error_in_bounds: forall {A} (l: list A) i, (O <= i < length l)%nat
  -> exists x, nth_error l i = value x.
Proof.
intros until i; intros H.
revert i l H.
induction i; destruct l; intros; simpl in *;
  try solve [eauto|lia].
apply IHi; lia.
Qed.

Class Inhabitant (A: Type) := default : A.
Instance Inhabitant_pair {T1 T2 : Type} {x1: Inhabitant T1} {x2: Inhabitant T2} : Inhabitant (T1*T2)%type.
exact ((x1,x2)).
Defined.

Lemma nth_map':
  forall {A B} (f: A -> B) d d' i al,
  (i < length al)%nat ->
   nth i (map f al) d = f (nth i al d').
Admitted.

Definition Znth {X}{d: Inhabitant X} n (xs: list X) :=
  if (Z_lt_dec n 0) then default else nth (Z.to_nat n) xs d.

Lemma Znth_map:
  forall {A:Type} {da: Inhabitant A}{B:Type}{db: Inhabitant B} i (f: A -> B) (al: list A),
  0 <= i < Zlength al ->
  Znth i (map f al)  = f (Znth i al).
Proof.
unfold Znth.
intros.
rewrite if_false by lia.
rewrite if_false by lia.
rewrite nth_map' with (d' := da); auto.
apply Nat2Z.inj_lt.
rewrite Z2Nat.id by lia.
change (Inhabitant A) with A.
rewrite <- Zlength_correct.
lia.
Qed.

Lemma Znth_combine : forall {A B} {a: Inhabitant A} {b: Inhabitant B} i (l1: list A) (l2: list B),
   Zlength l1 = Zlength l2 ->
  Znth i (combine l1 l2) = (Znth i l1, Znth i l2).
Proof.
  intros; unfold Znth.
  destruct (Z_lt_dec i 0); auto.
  apply combine_nth.
  rewrite !Zlength_correct in *; lia.
Qed.
Instance Nveric: NatDed mpred.
Admitted.

Definition denote_tc_iszero v : mpred :=
         match v with
         | Vint i => prop (is_true (Int.eq i Int.zero))
         | Vlong i => prop (is_true (Int64.eq i Int64.zero))
         | _ => FF
         end.

Definition denote_tc_nonzero v : mpred :=
         match v with
         | Vint i => prop (i <> Int.zero)
         | Vlong i =>prop (i <> Int64.zero)
         | _ => FF end.

Definition denote_tc_igt i v : mpred :=
     match v with
     | Vint i1 => prop (Int.unsigned i1 < Int.unsigned i)
     | _ => FF
     end.

Definition denote_tc_lgt l v : mpred :=
     match v with
     | Vlong l1 => prop (Int64.unsigned l1 < Int64.unsigned l)
     | _ => FF
     end.
Definition Zoffloat (f:float): option Z.
Admitted.
Definition Zofsingle (f: float32): option Z.
Admitted.

Definition denote_tc_Zge z v : mpred :=
          match v with
                     | Vfloat f => match Zoffloat f with
                                    | Some n => prop (z >= n)
                                    | None => FF
                                   end
                     | Vsingle f => match Zofsingle f with
                                    | Some n => prop (z >= n)
                                    | None => FF
                                   end
                     | _ => FF
                  end.

Definition denote_tc_Zle z v : mpred :=
          match v with
                     | Vfloat f => match Zoffloat f with
                                    | Some n => prop (z <= n)
                                    | None => FF
                                   end
                     | Vsingle f => match Zofsingle f with
                                    | Some n => prop (z <= n)
                                    | None => FF
                                   end
                     | _ => FF
                  end.

Definition sameblock v1 v2 : bool :=
         match v1, v2 with
          | Vptr b1 _, Vptr b2 _ => peq b1 b2
          | _, _ => false
         end.

Definition denote_tc_samebase v1 v2 : mpred :=
       prop (is_true (sameblock v1 v2)).

Definition denote_tc_nodivover v1 v2 : mpred :=
match v1, v2 with
          | Vint n1, Vint n2 => prop (~(n1 = Int.repr Int.min_signed /\ n2 = Int.mone))
          | Vlong n1, Vlong n2 => prop (~(n1 = Int64.repr Int64.min_signed /\ n2 = Int64.mone))
          | Vint n1, Vlong n2 => TT
          | Vlong n1, Vint n2 => prop (~ (n1 = Int64.repr Int64.min_signed  /\ n2 = Int.mone))
          | _ , _ => FF
        end.

Definition denote_tc_nosignedover (op: Z->Z->Z) (s: signedness) v1 v2 : mpred :=
 match v1,v2 with
 | Vint n1, Vint n2 =>
   prop (Int.min_signed <= op (Int.signed n1) (Int.signed n2) <= Int.max_signed)
 | Vlong n1, Vlong n2 =>
   prop (Int64.min_signed <= op (Int64.signed n1) (Int64.signed n2) <= Int64.max_signed)
 | Vint n1, Vlong n2 =>
   prop (Int64.min_signed <= op ((if s then Int.signed else Int.unsigned) n1) (Int64.signed n2) <= Int64.max_signed)
 | Vlong n1, Vint n2 =>
   prop (Int64.min_signed <= op (Int64.signed n1) ((if s then Int.signed else Int.unsigned)  n2) <= Int64.max_signed)
 | _, _ => FF
 end.

Definition denote_tc_initialized id ty rho : mpred :=
    prop (exists v, Map.get (te_of rho) id = Some v
               /\ tc_val ty v).

Definition denote_tc_isptr v : mpred :=
  prop (isptr v).

Definition denote_tc_isint v : mpred :=
  prop (is_int I32 Signed v).

Definition denote_tc_islong v : mpred :=
  prop (is_long v).

Definition test_eq_ptrs v1 v2 : mpred :=
  if sameblock v1 v2
  then (andp (weak_valid_pointer v1) (weak_valid_pointer v2))
  else (andp (valid_pointer v1) (valid_pointer v2)).

Definition test_order_ptrs v1 v2 : mpred :=
  if sameblock v1 v2
  then (andp (weak_valid_pointer v1) (weak_valid_pointer v2))
  else FF.

Definition denote_tc_test_eq v1 v2 : mpred :=
 match v1, v2 with
 | Vint i, Vint j =>
     if Archi.ptr64 then FF else andp (prop (i = Int.zero)) (prop (j = Int.zero))
 | Vlong i, Vlong j =>
     if Archi.ptr64 then andp (prop (i = Int64.zero)) (prop (j = Int64.zero)) else FF
 | Vint i, Vptr _ _ =>
      if Archi.ptr64 then FF else andp (prop (i = Int.zero)) (weak_valid_pointer v2)
 | Vlong i, Vptr _ _ =>
      if Archi.ptr64 then andp (prop (i = Int64.zero)) (weak_valid_pointer v2) else FF
 | Vptr _ _, Vint i =>
      if Archi.ptr64 then FF else andp (prop (i = Int.zero)) (weak_valid_pointer v1)
 | Vptr _ _, Vlong i =>
      if Archi.ptr64 then andp (prop (i = Int64.zero)) (weak_valid_pointer v1) else FF
 | Vptr _ _, Vptr _ _ =>
      test_eq_ptrs v1 v2
 | _, _ => FF
 end.

Definition denote_tc_test_order v1 v2 : mpred :=
 match v1, v2 with
 | Vint i, Vint j => if Archi.ptr64 then FF else andp (prop (i = Int.zero)) (prop (j = Int.zero))
 | Vlong i, Vlong j => if Archi.ptr64 then andp (prop (i = Int64.zero)) (prop (j = Int64.zero)) else FF
 | Vptr _ _, Vptr _ _ =>
      test_order_ptrs v1 v2
 | _, _ => FF
 end.
Definition typecheck_error (e: tc_error) : Prop.
Admitted.

Fixpoint denote_tc_assert {CS: compspecs} (a: tc_assert) : environ -> mpred :=
  match a with
  | tc_FF msg => `(prop (typecheck_error msg))
  | tc_TT => TT
  | tc_andp' b c => fun rho => andp (denote_tc_assert b rho) (denote_tc_assert c rho)
  | tc_orp' b c => `orp (denote_tc_assert b) (denote_tc_assert c)
  | tc_nonzero' e => `denote_tc_nonzero (eval_expr e)
  | tc_isptr e => `denote_tc_isptr (eval_expr e)
  | tc_isint e => `denote_tc_isint (eval_expr e)
  | tc_islong e => `denote_tc_islong (eval_expr e)
  | tc_test_eq' e1 e2 => `denote_tc_test_eq (eval_expr e1) (eval_expr e2)
  | tc_test_order' e1 e2 => `denote_tc_test_order (eval_expr e1) (eval_expr e2)
  | tc_ilt' e i => `(denote_tc_igt i) (eval_expr e)
  | tc_llt' e i => `(denote_tc_lgt i) (eval_expr e)
  | tc_Zle e z => `(denote_tc_Zge z) (eval_expr e)
  | tc_Zge e z => `(denote_tc_Zle z) (eval_expr e)
  | tc_samebase e1 e2 => `denote_tc_samebase (eval_expr e1) (eval_expr e2)
  | tc_nodivover' v1 v2 => `denote_tc_nodivover (eval_expr v1) (eval_expr v2)
  | tc_initialized id ty => denote_tc_initialized id ty
  | tc_iszero' e => `denote_tc_iszero (eval_expr e)
  | tc_nosignedover op e1 e2 =>
     match typeof e1, typeof e2 with
     | Tlong _ _, Tint _ Unsigned _ => `(denote_tc_nosignedover op Unsigned) (eval_expr e1) (eval_expr e2)
     | Tint _ Unsigned _, Tlong _ _ => `(denote_tc_nosignedover op Unsigned) (eval_expr e1) (eval_expr e2)
     | _, _ =>  `(denote_tc_nosignedover op Signed) (eval_expr e1) (eval_expr e2)
     end
 end.
Require VST.floyd.jmeq_lemmas.
