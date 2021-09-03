(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "-deprecated-native-compiler-option" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/metacoq/template-coq/theories" "MetaCoq.Template" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/metacoq/pcuic/theories" "MetaCoq.PCUIC" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/metacoq/safechecker/theories" "MetaCoq.SafeChecker" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Equations" "Equations" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-I" "/github/workspace/builds/coq/coq-failing/_build_ci/metacoq/template-coq/build" "-top" "bug_01" "-native-compiler" "no") -*- *)
(* File reduced by coq-bug-finder from original input, then from 419 lines to 163 lines, then from 310 lines to 591 lines, then from 594 lines to 174 lines, then from 320 lines to 1716 lines, then from 1716 lines to 203 lines, then from 318 lines to 1849 lines, then from 1849 lines to 579 lines, then from 691 lines to 1070 lines, then from 1070 lines to 594 lines, then from 705 lines to 2430 lines, then from 2426 lines to 728 lines, then from 835 lines to 982 lines, then from 985 lines to 755 lines, then from 863 lines to 2799 lines, then from 2799 lines to 931 lines, then from 1035 lines to 2914 lines, then from 2913 lines to 1076 lines, then from 1175 lines to 2095 lines, then from 2097 lines to 1105 lines, then from 1195 lines to 1369 lines, then from 1373 lines to 1155 lines, then from 1245 lines to 1363 lines, then from 1367 lines to 1165 lines, then from 1253 lines to 2291 lines, then from 2290 lines to 1773 lines, then from 1794 lines to 1692 lines, then from 1780 lines to 2513 lines, then from 2516 lines to 1707 lines, then from 1788 lines to 2241 lines, then from 2240 lines to 1833 lines, then from 1913 lines to 4126 lines, then from 4109 lines to 2297 lines, then from 2370 lines to 2417 lines, then from 2420 lines to 2303 lines, then from 2377 lines to 2796 lines, then from 2798 lines to 2386 lines, then from 2458 lines to 2501 lines, then from 2505 lines to 2394 lines, then from 2464 lines to 2700 lines, then from 2702 lines to 2678 lines, then from 2680 lines to 2411 lines, then from 2481 lines to 2691 lines, then from 2693 lines to 2419 lines, then from 2481 lines to 2737 lines, then from 2740 lines to 2451 lines, then from 2511 lines to 4491 lines, then from 4483 lines to 2470 lines, then from 2527 lines to 2558 lines, then from 2562 lines to 2476 lines, then from 2534 lines to 2667 lines, then from 2670 lines to 2486 lines, then from 2542 lines to 2631 lines, then from 2633 lines to 2498 lines, then from 2553 lines to 3644 lines, then from 3641 lines to 3953 lines *)
(* coqc version 8.15+alpha compiled with OCaml 4.05.0
   coqtop version 8.15+alpha *)
Declare ML Module "ltac_plugin".
Module Export AdmitTactic.
Module Import LocalFalse.
Inductive False := .
End LocalFalse.
Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.
End AdmitTactic.
Require Coq.MSets.MSetList.
Require Coq.MSets.MSetProperties.
Require Coq.Bool.Bool.
Require Coq.Arith.Arith.
Require Coq.micromega.Lia.
Require Coq.Lists.SetoidList.
Require Coq.Strings.String.
Require Coq.ZArith.ZArith.
Require Coq.extraction.Extraction.
Require Coq.Unicode.Utf8_core.
Require Equations.Init.
Require Equations.Signature.
Require Equations.CoreTactics.
Require Coq.Relations.Relation_Definitions.
Require Coq.Program.Wf.
Require Equations.Prop.Logic.
Require Equations.Prop.Classes.
Require Coq.Program.Tactics.
Require Equations.Prop.EqDec.
Require Equations.Prop.DepElim.
Require Coq.Relations.Relations.
Require Equations.Prop.Constants.
Require Coq.Bool.Bvector.
Require Coq.Lists.List.
Require Coq.Arith.Wf_nat.
Require Coq.Wellfounded.Wellfounded.
Require Coq.Relations.Relation_Operators.
Require Coq.Wellfounded.Lexicographic_Product.
Require Coq.Logic.FunctionalExtensionality.
Require Equations.Prop.Subterm.
Require Equations.Prop.FunctionalInduction.
Require Equations.Prop.Tactics.
Require Equations.Prop.NoConfusion.
Require Equations.Prop.EqDecInstances.
Require Equations.Prop.Loader.
Require Equations.Prop.Telescopes.
Require Equations.Prop.Equations.
Require MetaCoq.Template.utils.MCPrelude.
Require Coq.ssr.ssreflect.
Require Coq.Classes.CRelationClasses.
Require Equations.Type.Logic.
Require Equations.Type.Relation.
Require Equations.Type.Relation_Properties.
Require MetaCoq.Template.utils.MCRelations.
Module MetaCoq_DOT_Template_DOT_utils_DOT_MCList_WRAPPED.
Module MCList.
Import Coq.Bool.Bool Coq.Arith.Arith Coq.micromega.Lia Coq.Lists.SetoidList.
Import MetaCoq.Template.utils.MCPrelude MetaCoq.Template.utils.MCRelations.

Export ListNotations.

Arguments firstn : simpl nomatch.
Arguments skipn : simpl nomatch.

Notation "#| l |" := (List.length l) (at level 0, l at level 99, format "#| l |").
Arguments nil {_}, _.

Lemma app_tip_assoc {A} (l : list A) x l' : (l ++ [x]) ++ l' = l ++ (x :: l').
Proof.
now rewrite <- app_assoc.
Qed.

Fixpoint fold_left_i_aux {A B} (f : A -> nat -> B -> A) (n0 : nat) (l : list B)
         (a0 : A) {struct l} : A
  := match l with
     | [] => a0
     | b :: l => fold_left_i_aux f (S n0) l (f a0 n0 b)
     end.
Definition fold_left_i {A B} f := @fold_left_i_aux A B f 0.

Fixpoint mapi_rec {A B} (f : nat -> A -> B) (l : list A) (n : nat) : list B :=
  match l with
  | [] => []
  | hd :: tl => f n hd :: mapi_rec f tl (S n)
  end.

Definition mapi {A B} (f : nat -> A -> B) (l : list A) := mapi_rec f l 0.

Program Fixpoint safe_nth {A} (l : list A) (n : nat | n < List.length l) : A :=
  match l with
  | nil => _
  | hd :: tl =>
    match n with
    | 0 => hd
    | S n => safe_nth tl n
    end
  end.
Next Obligation.
  exfalso.
simpl in H.
inversion H.
Defined.
Next Obligation.
  simpl in H.
auto with arith.
Defined.

Lemma nth_error_safe_nth {A} n (l : list A) (isdecl : n < Datatypes.length l) :
  nth_error l n = Some (safe_nth l (exist _ n isdecl)).
Proof.
  revert n isdecl; induction l; intros.
  - inversion isdecl.
  - destruct n as [| n']; simpl.
    reflexivity.
    simpl in IHl.
    simpl in isdecl.
    now rewrite <- IHl.
Qed.

Definition rev {A} (l : list A) : list A :=
  let fix aux (l : list A) (acc : list A) : list A :=
      match l with
      | [] => acc
      | x :: l => aux l (x :: acc)
      end
  in aux l [].

Definition rev_map {A B} (f : A -> B) (l : list A) : list B :=
  let fix aux (l : list A) (acc : list B) : list B :=
      match l with
      | [] => acc
      | x :: l => aux l (f x :: acc)
      end
  in aux l [].

Fact rev_cons :
  forall {A} {l} {a : A},
    rev (a :: l) = (rev l ++ [a])%list.
Proof.
  intro A.
  unfold rev.
  match goal with
  | |- forall l a, ?faux _ _ = _ => set (aux := faux)
  end.
  assert (h : forall l acc, aux l acc = (aux l [] ++ acc)%list).
  { intro l.
induction l ; intro acc.
    - cbn.
reflexivity.
    - cbn.
rewrite (IHl [a]).
rewrite IHl.
      change (a :: acc) with ([a] ++ acc)%list.
      auto with datatypes.
  }
  intros l a.
  apply h.
Defined.

Fact rev_map_cons :
  forall {A B} {f : A -> B} {l} {a : A},
    rev_map f (a :: l) = (rev_map f l ++ [f a])%list.
Proof.
  intros A B f.
  unfold rev_map.
  match goal with
  | |- forall l a, ?faux _ _ = _ => set (aux := faux)
  end.
  assert (h : forall l acc, aux l acc = (aux l [] ++ acc)%list).
  { intro l.
induction l ; intro acc.
    - cbn.
reflexivity.
    - cbn.
rewrite (IHl [f a]).
rewrite IHl.
      change (f a :: acc) with ([f a] ++ acc)%list.
      auto with datatypes.
  }
  intros l a.
  apply h.
Defined.

Fact rev_length :
  forall {A} {l : list A},
    List.length (rev l) = List.length l.
Proof.
  intro A.
  unfold rev.
  match goal with
  | |- context [ List.length (?faux _ _) ] => set (aux := faux)
  end.
  assert (h : forall l acc, List.length (aux l acc) = (List.length acc + List.length l)%nat).
  { intro l.
induction l ; intro acc.
    - cbn.
auto with arith.
    - cbn.
rewrite IHl.
cbn.
auto with arith.
  }
  intro l.
apply h.
Defined.

Fact rev_map_length :
  forall {A B} {f : A -> B} {l : list A},
    List.length (rev_map f l) = List.length l.
Proof.
  intros A B f.
  unfold rev_map.
  match goal with
  | |- context [ List.length (?faux _ _) ] => set (aux := faux)
  end.
  assert (h : forall l acc, List.length (aux l acc) =
                       (List.length acc + List.length l)%nat).
  { intro l.
induction l ; intro acc.
    - cbn.
auto with arith.
    - cbn.
rewrite IHl.
cbn.
auto with arith.
  }
  intro l.
apply h.
Defined.

Fact rev_map_app :
  forall {A B} {f : A -> B} {l1 l2},
    (rev_map f (l1 ++ l2) = rev_map f l2 ++ rev_map f l1)%list.
Proof.
  intros A B f l1 l2.
revert B f l2.
  induction l1 ; intros B f l2.
  - simpl.
cbn.
rewrite app_nil_r.
reflexivity.
  - simpl.
rewrite !rev_map_cons.
rewrite IHl1.
    rewrite app_assoc.
reflexivity.
Defined.

Lemma map_map_compose :
  forall (A B C : Type) (f : A -> B) (g : B -> C) (l : list A),
    map g (map f l) = map (fun x => g (f x)) l.
Proof.
apply map_map.
Qed.

Lemma map_id_f {A} (l : list A) (f : A -> A) :
  (forall x, f x = x) ->
  map f l = l.
Proof.
  induction l; intros; simpl; try easy.
  rewrite H.
f_equal.
eauto.
Qed.

Section Reverse_Induction.
  Context {A : Type}.
  Lemma rev_list_ind :
    forall P:list A-> Type,
      P [] ->
        (forall (a:A) (l:list A), P (List.rev l) -> P (List.rev (a :: l))) ->
        forall l:list A, P (Coq.Lists.List.rev l).
  Proof.
    induction l; auto.
  Qed.

  Theorem rev_ind :
    forall P:list A -> Type,
      P [] ->
      (forall (x:A) (l:list A), P l -> P (l ++ [x])) -> forall l:list A, P l.
  Proof.
    intros.
    generalize (rev_involutive l).
    intros E; rewrite <- E.
    apply (rev_list_ind P).
    auto.

    simpl.
    intros.
    apply (X0 a (List.rev l0)).
    auto.
  Qed.

End Reverse_Induction.

Lemma skipn_nil :
  forall {A} n, @skipn A n [] = [].
Proof.
  intros A [| n] ; reflexivity.
Qed.

Lemma skipn_S {A} a (l : list A) n : skipn (S n) (a :: l) = skipn n l.
Proof.
reflexivity.
Qed.

Lemma mapi_ext_size {A B} (f g : nat -> A -> B) l k :
  (forall k' x, k' < k + #|l| -> f k' x = g k' x) ->
  mapi_rec f l k = mapi_rec g l k.
Proof.
  intros Hl.
generalize (Le.le_refl k).
generalize k at 1 3 4.
  induction l in k, Hl |- *.
simpl.
auto.
  intros.
simpl in *.
erewrite Hl; try lia.
  f_equal.
eapply (IHl (S k)); try lia.
intros.
apply Hl.
lia.
Qed.

Lemma map_ext_size {A B} (f g : nat -> A -> B) l :
  (forall k x, k < #|l| -> f k x = g k x) ->
  mapi f l = mapi g l.
Proof.
  intros Hl.
unfold mapi.
apply mapi_ext_size.
simpl.
auto.
Qed.

Lemma firstn_map {A B} n (f : A -> B) l : firstn n (map f l) = map f (firstn n l).
Proof.
  revert l; induction n.
reflexivity.
  destruct l; simpl in *; congruence.
Qed.

Lemma mapi_rec_compose {A B C} (g : nat -> B -> C) (f : nat -> A -> B) k l :
  mapi_rec g (mapi_rec f l k) k = mapi_rec (fun k x => g k (f k x)) l k.
Proof.
  induction l in k |- *; simpl; auto.
now rewrite IHl.
Qed.

Lemma mapi_compose {A B C} (g : nat -> B -> C) (f : nat -> A -> B) l :
  mapi g (mapi f l) = mapi (fun k x => g k (f k x)) l.
Proof.
apply mapi_rec_compose.
Qed.

Lemma map_ext {A B : Type} (f g : A -> B) (l : list A) :
  (forall x, f x = g x) ->
  map f l = map g l.
Proof.
  intros.
  induction l; trivial.
  intros.
simpl.
rewrite H.
congruence.
Defined.
Import Coq.ssr.ssreflect.

Lemma map_skipn {A B} (f : A -> B) (l : list A) (n : nat) : map f (skipn n l) = skipn n (map f l).
Proof.
  elim: n l => l // IHn.
  by case => //.
Qed.

Lemma nth_error_map {A B} (f : A -> B) n l : nth_error (map f l) n = option_map f (nth_error l n).
Proof.
  elim: n l; case => // IHn l /=.
  - by case: l => //.
  - by case => //.
Qed.

Lemma map_nil {A B} (f : A -> B) (l : list A) : l <> [] -> map f l <> [].
Proof.
induction l; simpl; congruence.
Qed.
#[global]
Hint Resolve map_nil : wf.

Inductive nth_error_Spec {A} (l : list A) (n : nat) : option A -> Type :=
| nth_error_Spec_Some x : nth_error l n = Some x -> n < length l -> nth_error_Spec l n (Some x)
| nth_error_Spec_None : length l <= n -> nth_error_Spec l n None.

Lemma mapi_rec_eqn {A B} (f : nat -> A -> B) (l : list A) a n :
  mapi_rec f (a :: l) n = f n a :: mapi_rec f l (S n).
Proof.
simpl.
f_equal.
Qed.

Lemma nth_error_mapi_rec {A B} (f : nat -> A -> B) n k l :
  nth_error (mapi_rec f l k) n = option_map (f (n + k)) (nth_error l n).
Proof.
  induction l in n, k |- *.
  - destruct n; reflexivity.
  - destruct n; simpl.
    + reflexivity.
    + rewrite IHl.
by rewrite <- Nat.add_succ_comm.
Qed.

Lemma nth_error_mapi {A B} (f : nat -> A -> B) n l :
  nth_error (mapi f l) n = option_map (f n) (nth_error l n).
Proof.
  unfold mapi; rewrite nth_error_mapi_rec.
  now rewrite -> Nat.add_0_r.
Qed.

Lemma nth_error_Some_length {A} {l : list A} {n t} : nth_error l n = Some t -> n < length l.
Proof.
rewrite <- nth_error_Some.
destruct (nth_error l n); congruence.
Qed.

Lemma nth_error_Some_non_nil {A} (l : list A) (n : nat) (x : A) : nth_error l n = Some x -> l <> [].
Proof.
  destruct l, n; simpl; congruence.
Qed.

Lemma nth_error_Some' {A} l n : (∑ x : A, nth_error l n = Some x) <~> n < length l.
Proof.
  revert n.
induction l; destruct n; simpl.
  - split; [now destruct 1 | intros H'; elimtype False; inversion H'].
  - split; [now destruct 1 | intros H'; elimtype False; inversion H'].
  - split; now intuition eauto with arith.
  - destruct (IHl n); split; intros; auto with arith.
Qed.

Lemma nth_error_spec {A} (l : list A) (n : nat) : nth_error_Spec l n (nth_error l n).
Proof.
  destruct nth_error eqn:Heq.
  constructor; auto.
now apply nth_error_Some_length in Heq.
  constructor; auto.
now apply nth_error_None in Heq.
Qed.

Lemma nth_error_app_left {A} (l l' : list A) n t : nth_error l n = Some t -> nth_error (l ++ l') n = Some t.
Proof.
induction l in n |- *; destruct n; simpl; try congruence.
auto.
Qed.

Lemma nth_error_nil {A} n : nth_error (nil A) n = None.
Proof.
destruct n; auto.
Qed.
Hint Rewrite @nth_error_nil.

Fixpoint chop {A} (n : nat) (l : list A) :=
  match n with
  | 0 => ([], l)
  | S n =>
    match l with
    | hd :: tl =>
      let '(l, r) := chop n tl in
      (hd :: l, r)
    | [] => ([], [])
    end
  end.

Lemma nth_map {A} (f : A -> A) n l d :
  (d = f d) ->
  nth n (map f l) d = f (nth n l d).
Proof.
  induction n in l |- *; destruct l; simpl; auto.
Qed.

Lemma mapi_map {A B C} (f : nat -> B -> C) (l : list A) (g : A -> B) :
  mapi f (map g l) = mapi (fun i x => f i (g x)) l.
Proof.
  unfold mapi.
generalize 0.
induction l; simpl; congruence.
Qed.

Lemma map_mapi {A B C} (f : nat -> A -> B) (l : list A) (g : B -> C) :
  map g (mapi f l) = mapi (fun i x => g (f i x)) l.
Proof.
  unfold mapi.
generalize 0.
induction l; simpl; congruence.
Qed.

Lemma chop_map {A B} (f : A -> B) n l l' l'' :
  chop n l = (l', l'') -> chop n (map f l) = (map f l', map f l'').
Proof.
  induction n in l, l', l'' |- *; destruct l; try intros [= <- <-]; simpl; try congruence.
  destruct (chop n l) eqn:Heq.
specialize (IHn _ _ _ Heq).
  intros [= <- <-].
now rewrite IHn.
Qed.

Lemma chop_n_app {A} {l l' : list A} {n} : n = length l -> chop n (l ++ l') = (l, l').
Proof.
  intros ->.
induction l; simpl; try congruence.
  now rewrite IHl.
Qed.

Lemma mapi_mapi {A B C} (g : nat -> A -> B) (f : nat -> B -> C) (l : list A) :
  mapi f (mapi g l) = mapi (fun n x => f n (g n x)) l.
Proof.
unfold mapi.
generalize 0.
induction l; simpl; try congruence.
Qed.

Lemma mapi_cst_map {A B} (f : A -> B) l : mapi (fun _ => f) l = map f l.
Proof.
  unfold mapi.
generalize 0.
induction l; cbn; auto.
intros.
now rewrite IHl.
Qed.

Lemma mapi_rec_ext {A B} (f g : nat -> A -> B) (l : list A) n :
  (forall k x, n <= k -> k < length l + n -> f k x = g k x) ->
  mapi_rec f l n = mapi_rec g l n.
Proof.
  intros Hfg.
induction l in n, Hfg |- *; simpl; try congruence.
  intros.
rewrite Hfg; simpl; try lia.
f_equal.
  rewrite IHl; auto.
intros.
apply Hfg.
simpl; lia.
simpl.
lia.
Qed.

Lemma mapi_ext {A B} (f g : nat -> A -> B) (l : list A) :
  (forall n x, f n x = g n x) ->
  mapi f l = mapi g l.
Proof.
intros; now apply mapi_rec_ext.
Qed.

Lemma mapi_rec_Sk {A B} (f : nat -> A -> B) (l : list A) k :
  mapi_rec f l (S k) = mapi_rec (fun n x => f (S n) x) l k.
Proof.
  induction l in k |- *; simpl; congruence.
Qed.

Lemma mapi_rec_add {A B : Type} (f : nat -> A -> B) (l : list A) (n k : nat) :
  mapi_rec f l (n + k) = mapi_rec (fun (k : nat) (x : A) => f (n + k) x) l k.
Proof.
  induction l in n, k |- *; simpl; auto.
  f_equal.
rewrite (IHl (S n) k).
rewrite mapi_rec_Sk.
  eapply mapi_rec_ext.
intros.
f_equal.
lia.
Qed.

Lemma mapi_rec_app {A B} (f : nat -> A -> B) (l l' : list A) n :
  (mapi_rec f (l ++ l') n = mapi_rec f l n ++ mapi_rec f l' (length l + n))%list.
Proof.
  induction l in n |- *; simpl; try congruence.
  rewrite IHl.
f_equal.
now rewrite <- Nat.add_succ_comm.
Qed.

Lemma mapi_app {A B} (f : nat -> A -> B) (l l' : list A) :
  (mapi f (l ++ l') = mapi f l ++ mapi (fun n x => f (length l + n) x) l')%list.
Proof.
  unfold mapi; rewrite mapi_rec_app.
  f_equal.
generalize 0.
  induction l'; intros.
reflexivity.
rewrite mapi_rec_eqn.
  change (S (length l + n)) with (S (length l) + n).
  rewrite (Nat.add_succ_comm _ n).
now rewrite IHl'.
Qed.

Lemma rev_mapi_rec {A B} (f : nat -> A -> B) (l : list A) n k : k <= n ->
  List.rev (mapi_rec f l (n - k)) = mapi_rec (fun k x => f (Nat.pred (length l) + n - k) x) (List.rev l) k.
Proof.
  unfold mapi.
revert n k.
  induction l using rev_ind; simpl; try congruence.
  intros.
rewrite rev_unit.
simpl.
  rewrite mapi_rec_app rev_app_distr; simpl.
rewrite IHl; auto.
simpl.
  rewrite app_length.
simpl.
f_equal.
f_equal.
lia.
rewrite mapi_rec_Sk.
  apply mapi_rec_ext.
intros.
f_equal.
rewrite List.rev_length in H1.
  rewrite Nat.add_1_r.
simpl; lia.
Qed.

Lemma rev_mapi {A B} (f : nat -> A -> B) (l : list A) :
  List.rev (mapi f l) = mapi (fun k x => f (Nat.pred (length l) - k) x) (List.rev l).
Proof.
  unfold mapi.
change 0 with (0 - 0) at 1.
  rewrite rev_mapi_rec; auto.
now rewrite Nat.add_0_r.
Qed.

Lemma mapi_rec_rev {A B} (f : nat -> A -> B) (l : list A) n :
  mapi_rec f (List.rev l) n = List.rev (mapi (fun k x => f (length l + n - S k) x) l).
Proof.
  unfold mapi.
revert n.
  induction l using rev_ind; simpl; try congruence.
  intros.
rewrite rev_unit.
simpl.
  rewrite IHl mapi_rec_app.
  simpl.
rewrite rev_unit.
f_equal.
  rewrite app_length.
simpl.
f_equal.
lia.
  rewrite app_length.
simpl.
  f_equal.
eapply mapi_rec_ext.
intros.
  f_equal.
lia.
Qed.

Lemma mapi_rev {A B} (f : nat -> A -> B) (l : list A) :
  mapi f (List.rev l) = List.rev (mapi (fun k x => f (length l - S k) x) l).
Proof.
unfold mapi at 1.
rewrite mapi_rec_rev.
now rewrite Nat.add_0_r.
Qed.

Lemma mapi_rec_length {A B} (f : nat -> A -> B) (l : list A) n :
  length (mapi_rec f l n) = length l.
Proof.
induction l in n |- *; simpl; try congruence.
Qed.

Lemma mapi_length {A B} (f : nat -> A -> B) (l : list A) :
  length (mapi f l) = length l.
Proof.
apply mapi_rec_length.
Qed.

Lemma skipn_length {A} n (l : list A) : n <= length l -> length (skipn n l) = length l - n.
Proof.
  induction l in n |- *; destruct n; simpl; auto.
  intros.
rewrite IHl; auto with arith.
Qed.

Lemma combine_map_id {A B} (l : list (A * B)) :
 l = combine (map fst l) (map snd l).
Proof.
  induction l ; simpl; try easy.
  destruct a.
now f_equal.
Qed.

Local Ltac invs H := inversion H; subst; clear H.

Lemma last_inv A (l1 l2 : list A) x y :
  (l1 ++ [x] = l2 ++ [y] -> l1 = l2 /\ x = y)%list.
Proof.
  revert l2.
induction l1; cbn; intros.
  - destruct l2; cbn in H; invs H.
eauto.
destruct l2; invs H2.
  - destruct l2; invs H.
destruct l1; invs H2.
    eapply IHl1 in H2 as [].
split; congruence.
Qed.

Lemma skipn_all2 :
  forall {A n} (l : list A),
    #|l| <= n ->
         skipn n l = [].
Proof.
  intros A n l h.
revert l h.
  induction n ; intros l h.
  - destruct l.
    + reflexivity.
    + cbn in h.
inversion h.
  - destruct l.
    + reflexivity.
    + simpl.
apply IHn.
cbn in h.
lia.
Qed.

Lemma not_empty_map {A B} (f : A -> B) l : l <> [] -> map f l <> [].
Proof.
  intro H; destruct l; intro e; now apply H.
Qed.

Lemma nth_error_skipn_add A l m n (a : A) :
  nth_error l (m + n) = Some a ->
  nth_error (skipn m l) n = Some a.
Proof.
  induction m in n, l |- *.
  - cbn.
destruct l; firstorder.
  - cbn.
destruct l.
    + inversion 1.
    + eapply IHm.
Qed.

Lemma skipn_all_app :
  forall A (l1 l2 : list A),
    skipn #|l1| (l1 ++ l2) = l2.
Proof.
  intros A l1 l2.
  induction l1 in l2 |- *.
  - reflexivity.
  - simpl.
eauto.
Qed.

Lemma rev_map_spec {A B} (f : A -> B) (l : list A) :
  rev_map f l = List.rev (map f l).
Proof.
  unfold rev_map.
  rewrite -(app_nil_r (List.rev (map f l))).
  generalize (@nil B).
  induction l; simpl; auto.
intros l0.
  rewrite IHl.
now rewrite -app_assoc.
Qed.

Lemma skipn_0 {A} (l : list A) : skipn 0 l = l.
Proof.
reflexivity.
Qed.

Lemma skipn_0_eq {A} (l : list A) n : n = 0 -> skipn n l = l.
Proof.
intros ->; apply skipn_0.
Qed.

Lemma skipn_n_Sn {A} n s (x : A) xs : skipn n s = x :: xs -> skipn (S n) s = xs.
Proof.
  induction n in s, x, xs |- *.
  - unfold skipn.
now intros ->.
  - destruct s; simpl.
intros H; discriminate.
apply IHn.
Qed.

Lemma skipn_all {A} (l : list A) : skipn #|l| l = [].
Proof.
  induction l; simpl; auto.
Qed.

Lemma skipn_app_le {A} n (l l' : list A) : n <= #|l| -> skipn n (l ++ l') = skipn n l ++ l'.
Proof.
  induction l in n, l' |- *; simpl; auto.
  intros Hn.
destruct n; try lia.
reflexivity.
  intros Hn.
destruct n.
reflexivity.
  rewrite !skipn_S.
apply IHl.
lia.
Qed.

Lemma skipn_mapi_rec {A B} n (f : nat -> A -> B) k (l : list A) :
  skipn n (mapi_rec f l k) =
  mapi_rec f (skipn n l) (n + k).
Proof.
  induction n in f, l, k |- *.
  - now rewrite !skipn_0.
  - destruct l.
    * reflexivity.
    * simpl.
rewrite IHn.
      now rewrite Nat.add_succ_r.
Qed.

Lemma firstn_ge {A} (l : list A) n : #|l| <= n -> firstn n l = l.
Proof.
  induction l in n |- *; simpl; intros; auto.
now rewrite firstn_nil.
  destruct n; simpl.
lia.
rewrite IHl; auto.
lia.
Qed.

Lemma firstn_0 {A} (l : list A) n : n = 0 -> firstn n l = [].
Proof.
  intros ->.
reflexivity.
Qed.

Lemma skipn_firstn_skipn {A} (l : list A) n : skipn n (firstn (S n) l) ++ skipn (S n) l = skipn n l.
Proof.
  induction l in n |- *; simpl; auto.
now rewrite app_nil_r.
  destruct n=> /=; auto.
Qed.

Lemma firstn_firstn_firstn {A} (l : list A) n : firstn n (firstn (S n) l) = firstn n l.
Proof.
  induction l in n |- *; simpl; auto.
  destruct n=> /=; auto.
now rewrite IHl.
Qed.

Lemma skipn_eq_cons {A} n (l : list A) hd tl : skipn n l = hd :: tl ->
  (nth_error l n = Some hd) /\ (skipn (S n) l = tl).
Proof.
  induction n in l, hd, tl |- *.
  - rewrite skipn_0 => ->.
now simpl.
  - destruct l as [|hd' tl'].
    * rewrite skipn_nil.
discriminate.
    * simpl.
apply IHn.
Qed.

Fixpoint split_at_aux {A} (n : nat) (acc : list A) (l : list A) : list A * list A :=
  match n with
  | 0 => (List.rev acc, l)
  | S n' =>
    match l with
    | [] => (List.rev acc, [])
    | hd :: l' => split_at_aux n' (hd :: acc) l'
    end
  end.

Definition split_at {A} (n : nat) (l : list A) : list A * list A :=
  split_at_aux n [] l.

Lemma split_at_aux_firstn_skipn {A} n acc (l : list A) : split_at_aux n acc l = (List.rev acc ++ firstn n l, skipn n l).
Proof.
  induction n in acc, l |- *; destruct l; simpl; auto.
  now rewrite app_nil_r.
  now rewrite app_nil_r.
  now rewrite app_nil_r.
  rewrite IHn.
simpl.
  now rewrite -app_assoc /=.
Qed.

Lemma split_at_firstn_skipn {A} n (l : list A) : split_at n l = (firstn n l, skipn n l).
Proof.
  now rewrite /split_at split_at_aux_firstn_skipn /= //.
Qed.

Lemma rev_app :
  forall A (l l' : list A),
    (rev (l ++ l') = rev l' ++ rev l)%list.
Proof.
  intros A l l'.
  induction l in l' |- *.
  - simpl.
change (rev (nil A)) with (nil A).
    rewrite app_nil_r.
reflexivity.
  - simpl.
rewrite rev_cons.
rewrite IHl.
    rewrite rev_cons.
rewrite app_assoc.
reflexivity.
Qed.

Lemma rev_invol :
  forall A (l : list A),
    rev (rev l) = l.
Proof.
  intros A l.
induction l ; eauto.
  rewrite rev_cons.
rewrite rev_app.
simpl.
  rewrite IHl.
reflexivity.
Qed.

Lemma list_ind_rev :
  forall A (P : list A -> Prop),
    P nil ->
    (forall a l, P l -> P (l ++ [a])%list) ->
    forall l, P l.
Proof.
  intros A P h1 h2 l.
  rewrite <- rev_invol.
  generalize (rev l).
clear l.
intro l.
  induction l ; auto.
  rewrite rev_cons.
eauto.
Qed.

Lemma list_rect_rev :
  forall A (P : list A -> Type),
    P nil ->
    (forall a l, P l -> P (l ++ [a])%list) ->
    forall l, P l.
Proof.
  intros A P h1 h2 l.
  rewrite <- rev_invol.
  generalize (rev l).
clear l.
intro l.
  induction l ; auto.
  rewrite rev_cons.
eauto.
Qed.

Lemma last_app {A} (l l' : list A) d : l' <> [] -> last (l ++ l') d = last l' d.
Proof.
  revert l'.
induction l; simpl; auto.
intros.
  destruct l.
simpl.
destruct l'; congruence.
simpl.
  specialize (IHl _ H).
apply IHl.
Qed.

Lemma last_nonempty_eq {A} {l : list A} {d d'} : l <> [] -> last l d = last l d'.
Proof.
  induction l; simpl; try congruence.
  intros.
destruct l; auto.
apply IHl.
congruence.
Qed.

Lemma nth_error_removelast {A} (args : list A) n :
  n < Nat.pred #|args| -> nth_error args n = nth_error (removelast args) n.
Proof.
  induction n in args |- *; destruct args; intros; auto.
  simpl.
destruct args.
inversion H.
reflexivity.
  simpl.
rewrite IHn.
simpl in H.
auto with arith.
  destruct args, n; reflexivity.
Qed.

Lemma nth_error_skipn {A} n (l : list A) i : nth_error (skipn n l) i = nth_error l (n + i).
Proof.
  induction l in n, i |- *; destruct n; simpl; auto.
    by case: i.
Qed.

Lemma skipn_skipn {A} n m (l : list A) : skipn n (skipn m l) = skipn (m + n) l.
Proof.
  induction m in n, l |- *.
auto.
  simpl.
destruct l.
destruct n; reflexivity.
  now rewrite skipn_S skipn_S.
Qed.

Lemma skipn_nth_error {A} (l : list A) i :
  match nth_error l i with
  | Some a => skipn i l = a :: skipn (S i) l
  | None => skipn i l = []
  end.
Proof.
  induction l in i |- *.
destruct i.
reflexivity.
reflexivity.
  destruct i.
simpl.
reflexivity.
  simpl.
specialize (IHl i).
destruct nth_error.
  rewrite [skipn _ _]IHl.
reflexivity.
  rewrite [skipn _ _]IHl.
reflexivity.
Qed.

Lemma nth_error_app_ge {A} (l l' : list A) (v : nat) :
  length l <= v ->
  nth_error (l ++ l') v = nth_error l' (v - length l).
Proof.
  revert v; induction l; simpl; intros.
  now rewrite Nat.sub_0_r.
  destruct v.
lia.
  simpl.
rewrite IHl; auto with arith.
Qed.

Lemma nth_error_app_lt {A} (l l' : list A) (v : nat) :
  v < length l ->
  nth_error (l ++ l') v = nth_error l v.
Proof.
  revert v; induction l; simpl; intros.
easy.
  destruct v; trivial.
  simpl.
rewrite IHl; auto with arith.
Qed.

Lemma nth_error_rev {A} (l : list A) i : i < #|l| ->
  nth_error l i = nth_error (List.rev l) (#|l| - S i).
Proof.
  revert l.
induction i.
destruct l; simpl; auto.
  induction l using rev_ind; simpl.
auto.
  rewrite rev_app_distr.
simpl.
  rewrite app_length.
simpl.
  replace (#|l| + 1 - 0) with (S #|l|) by lia.
simpl.
  rewrite Nat.sub_0_r in IHl.
auto with arith.

  destruct l.
simpl; auto.
simpl.
intros.
rewrite IHi.
lia.
  assert (#|l| - S i < #|l|) by lia.
  rewrite nth_error_app_lt.
rewrite List.rev_length; auto.
  reflexivity.
Qed.

Lemma nth_error_rev_inv {A} (l : list A) i :
  i < #|l| ->
  nth_error (List.rev l) i = nth_error l (#|l| - S i).
Proof.
  intros Hi.
  rewrite nth_error_rev ?List.rev_length; auto.
  now rewrite List.rev_involutive.
Qed.

Lemma nth_error_snoc {A} (l : list A) (a : A) (l' : list A) i :
  i = #|l| ->
  nth_error (l ++ a :: l') i = Some a.
Proof.
  intros ->.
  rewrite nth_error_app_ge; [easy|].
  now rewrite Nat.sub_diag.
Qed.

Lemma map_inj :
  forall A B (f : A -> B) l l',
    (forall x y, f x = f y -> x = y) ->
    map f l = map f l' ->
    l = l'.
Proof.
  intros A B f l l' h e.
  induction l in l', e |- *.
  - destruct l' ; try discriminate.
reflexivity.
  - destruct l' ; try discriminate.
inversion e.
    f_equal ; eauto.
Qed.

Section ListSize.
  Context {A} (size : A -> nat).

  Fixpoint list_size (l : list A) : nat :=
    match l with
    | [] =>  0
    | a :: v => S (size a + list_size v)
    end.

  Lemma list_size_app (l l' : list A)
    : list_size (l ++ l') = list_size l + list_size l'.
  Proof.
    induction l; simpl.
reflexivity.
    rewrite IHl; lia.
  Qed.

  Lemma list_size_rev (l : list A)
    : list_size (rev l) = list_size l.
  Proof.
    induction l; simpl.
reflexivity.
    rewrite rev_cons list_size_app IHl; cbn; lia.
  Qed.

  Lemma list_size_length (l : list A)
    : list_size l >= length l.
  Proof.
    induction l; simpl; lia.
  Qed.

End ListSize.

Section ListSizeMap.
  Context {A} (sizeA : A -> nat).
  Context {B} (sizeB : B -> nat).

  Lemma list_size_map (f : A -> B) l :
    list_size sizeB (map f l) = list_size (fun x => sizeB (f x)) l.
  Proof.
    induction l; simpl; eauto.
  Qed.

  Lemma list_size_mapi_rec_eq (l : list A) (f : nat -> A -> B) k :
    (forall i x, sizeB (f i x) = sizeA x) ->
    list_size sizeB (mapi_rec f l k) = list_size sizeA l.
  Proof.
    intro H.
induction l in k |- *.
reflexivity.
    simpl.
rewrite IHl.
rewrite H.
lia.
  Qed.

  Lemma list_size_mapi_eq (l : list A) (f : nat -> A -> B) :
    (forall i x, sizeB (f i x) = sizeA x) ->
    list_size sizeB (mapi f l) = list_size sizeA l.
  Proof.
    unfold mapi.
intros.
now apply list_size_mapi_rec_eq.
  Qed.

  Lemma list_size_map_eq (l : list A) (f : A -> B) :
    (forall x, sizeA x = sizeB (f x)) ->
    list_size sizeB (map f l) = list_size sizeA l.
  Proof.
    intros.
    induction l; simpl; auto.
  Qed.

  Lemma list_size_mapi_rec_le (l : list A) (f : nat -> A -> B) k :
    (forall i x, sizeB (f i x) <= sizeA x) ->
    list_size sizeB (mapi_rec f l k) <= list_size sizeA l.
  Proof.
    intro H.
induction l in k |- *.
reflexivity.
    simpl.
specialize (H k a).
specialize (IHl (S k)).
lia.
  Qed.

  Lemma list_size_mapi_le (l : list A) (f : nat -> A -> B) :
    (forall i x, sizeB (f i x) <= sizeA x) ->
    list_size sizeB (mapi f l) <= list_size sizeA l.
  Proof.
    unfold mapi.
intros.
now apply list_size_mapi_rec_le.
  Qed.

  Lemma list_size_map_le (l : list A) (f : A -> B) :
    (forall x, sizeB (f x) <= sizeA x) ->
    list_size sizeB (map f l) <= list_size sizeA l.
  Proof.
    intros.
    induction l; simpl; auto.
specialize (H a).
    lia.
  Qed.

End ListSizeMap.

Lemma list_size_map_hom {A} (size : A -> nat) (l : list A) (f : A -> A) :
  (forall x, size x = size (f x)) ->
  list_size size (map f l) = list_size size l.
Proof.
  intros.
  induction l; simpl; auto.
Defined.

Lemma InA_In_eq {A} x (l : list A) : InA Logic.eq x l <-> In x l.
Proof.
  etransitivity.
eapply InA_alt.
  firstorder.
now subst.
Qed.

Lemma forallb_rev {A} (p : A -> bool) l :
  forallb p (List.rev l) = forallb p l.
Proof.
  induction l using rev_ind; simpl; try congruence.
  rewrite rev_unit forallb_app.
simpl.
rewrite <- IHl.
  now rewrite andb_comm andb_true_r.
Qed.

Fixpoint unfold {A} (n : nat) (f : nat -> A) : list A :=
  match n with
  | 0 => []
  | S n => unfold n f ++ [f n]
  end.

Lemma mapi_irrel_list {A B} (f : nat -> A) (l l' : list B) :
  #|l| = #|l'| ->
  mapi (fun i (x : B) => f i) l = mapi (fun i x => f i) l'.
Proof.
  induction l in f, l' |- *; destruct l' => //; simpl; auto.
  intros [= eq].
unfold mapi.
simpl.
f_equal.
  rewrite !mapi_rec_Sk.
  now rewrite [mapi_rec _ _ _](IHl (fun x => (f (S x))) l').
Qed.

Lemma mapi_unfold {A B} (f : nat -> B) l : mapi (fun i (x : A) => f i) l = unfold #|l| f.
Proof.
  unfold mapi.
  induction l in f |- *; simpl; auto.
  rewrite mapi_rec_Sk.
  rewrite -IHl.
rewrite -(mapi_rec_Sk (fun i x => f i) l 0).
  change [f #|l|] with (mapi_rec (fun i x => f i) [a] #|l|).
  rewrite -(Nat.add_0_r #|l|).
rewrite -mapi_rec_app.
  change (f 0 :: _) with (mapi (fun i x => f i) (a :: l)).
  apply mapi_irrel_list.
simpl.
rewrite app_length /=; lia.
Qed.

Lemma unfold_length {A} (f : nat -> A) m : #|unfold m f| = m.
Proof.
  induction m; simpl; rewrite ?app_length /=; auto.
lia.
Qed.

Lemma nth_error_unfold {A} (f : nat -> A) m n : n < m <-> nth_error (unfold m f) n = Some (f n).
Proof.
  induction m in n |- *; split; intros Hn; try lia.
  - simpl in Hn.
rewrite nth_error_nil in Hn.
discriminate.
  - destruct (Classes.eq_dec n m); [subst|].
    * simpl.
rewrite nth_error_app_ge unfold_length // Nat.sub_diag /= //.
    * simpl.
rewrite nth_error_app_lt ?unfold_length //; try lia.
      apply IHm; lia.
  - simpl in Hn.
eapply nth_error_Some_length in Hn.
    rewrite app_length /= unfold_length in Hn.
lia.
Qed.

Lemma nth_error_unfold_inv {A} (f : nat -> A) m n t : nth_error (unfold m f) n = Some t -> t = (f n).
Proof.
  induction m in n |- *; intros Hn; try lia.
  - simpl in Hn.
rewrite nth_error_nil in Hn.
discriminate.
  - simpl in Hn.
    pose proof (nth_error_Some_length Hn).
    rewrite app_length /= unfold_length in H.
    destruct (Classes.eq_dec n m); [subst|].
    * simpl.
revert Hn.
rewrite nth_error_app_ge unfold_length // Nat.sub_diag /= //; congruence.
    * simpl.
revert Hn.
rewrite nth_error_app_lt ?unfold_length //; try lia.
auto.
Qed.

Lemma In_unfold_inj {A} (f : nat -> A) n i :
  (forall i j, f i = f j -> i = j) ->
  In (f i) (unfold n f) -> i < n.
Proof.
  intros hf.
  induction n; simpl => //.
  intros H; apply in_app_or in H.
  destruct H.
  - specialize (IHn H).
lia.
  - simpl in H.
destruct H; [apply hf in H|].
    * subst.
auto.
    * destruct H.
Qed.

Lemma forallb_unfold {A} (f : A -> bool) (g : nat -> A) n :
  (forall x, x < n -> f (g x)) ->
  forallb f (unfold n g).
Proof.
  intros fg.
  induction n; simpl; auto.
  rewrite forallb_app IHn //.
  intros x lt; rewrite fg //.
lia.
  rewrite /= fg //.
Qed.

Lemma forallb_mapi {A B} (p : B -> bool) (f : nat -> B) l :
  (forall i, i < #|l| -> p (f i)) ->
  forallb p (mapi (fun i (x : A) => f i) l).
Proof.
  intros Hp.
rewrite (mapi_unfold f).
  induction #|l| in *; simpl; auto.
  rewrite forallb_app.
simpl.
now rewrite Hp // !andb_true_r.
Qed.

Lemma fold_left_andb_forallb {A} P l x :
  fold_left (fun b x => P x && b) l (P x) = @forallb A P (x :: l).
Proof.
  cbn.
rewrite <- fold_left_rev_right.
rewrite <- forallb_rev.
  induction (List.rev l); cbn.
  - now rewrite andb_true_r.
  - rewrite IHl0.
rewrite !andb_assoc.
    f_equal.
now rewrite andb_comm.
Qed.

Lemma nth_nth_error {A} n l (d : A) :
  nth n l d = match nth_error l n with
              | Some x => x
              | None => d
              end.
Proof.
  symmetry.
apply nth_default_eq.
Qed.

Lemma nth_nth_error' {A} {i} {l : list A} {d v} :
  nth i l d = v ->
  (nth_error l i = Some v) +
  (nth_error l i = None /\ v = d).
Proof.
  move: i v.
elim: l => [|hd tl IH] //.
  - case => /= //; now right.
  - case => /= // _ <-.
now left.
Qed.

Lemma firstn_add {A} x y (args : list A) : firstn (x + y) args = firstn x args ++ firstn y (skipn x args).
Proof.
  induction x in y, args |- *.
simpl.
reflexivity.
  simpl.
destruct args; simpl.
  now rewrite firstn_nil.
  rewrite IHx.
now rewrite app_comm_cons.
Qed.

Lemma firstn_app_left (A : Type) (n : nat) (l1 l2 : list A) k :
  k = #|l1| + n ->
  firstn k (l1 ++ l2) = l1 ++ firstn n l2.
Proof.
intros ->; apply firstn_app_2.
Qed.

Lemma skipn_all_app_eq {A} n (l l' : list A) : n = #|l| -> skipn n (l ++ l') = l'.
Proof.
  move->.
apply skipn_all_app.
Qed.

Lemma rev_case {A} (P : list A -> Type) :
  P nil -> (forall l x, P (l ++ [x])) -> forall l, P l.
Proof.
  intros; now apply rev_ind.
Qed.

Lemma firstn_length_le_inv {A} n (l : list A) : #|firstn n l| = n -> n <= #|l|.
Proof.
  induction l in n |- *; simpl; auto with arith;
  destruct n; simpl; auto with arith.
discriminate.
Qed.

End MCList.

End MetaCoq_DOT_Template_DOT_utils_DOT_MCList_WRAPPED.
Module Export MetaCoq_DOT_Template_DOT_utils_DOT_MCList.
Module Export MetaCoq.
Module Export Template.
Module Export utils.
Module MCList.
Include MetaCoq_DOT_Template_DOT_utils_DOT_MCList_WRAPPED.MCList.
End MCList.

End utils.

End Template.

End MetaCoq.

End MetaCoq_DOT_Template_DOT_utils_DOT_MCList.
Require Coq.Floats.SpecFloat.
Require Equations.Type.FunctionalExtensionality.
Require Equations.Type.WellFounded.

Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.

Notation "p .1" := (fst p)
  (at level 2, left associativity, format "p .1") : pair_scope.
Notation "p .2" := (snd p)
  (at level 2, left associativity, format "p .2") : pair_scope.
Open Scope pair_scope.

Notation "x × y" := (prod x y ) (at level 80, right associativity).

Definition on_snd {A B C} (f : B -> C) (p : A * B) :=
  (fst p, f (snd p)).

Definition test_snd {A B} (f : B -> bool) (p : A * B) :=
  f (snd p).
Import Coq.Lists.List.

Fixpoint map_option_out {A} (l : list (option A)) : option (list A) :=
  match l with
  | nil => Some nil
  | hd :: tl => match hd, map_option_out tl with
                | Some hd, Some tl => Some (hd :: tl)
                | _, _ => None
                end
  end.

Record squash (A : Type) : Prop := sq { _ : A }.

Notation "∥ T ∥" := (squash T) (at level 10).

Ltac sq :=
  repeat match goal with
  | H : ∥ _ ∥ |- _ => case H; clear H; intro H
  end; try eapply sq.
Import MetaCoq.Template.utils.MCList.

Inductive All {A} (P : A -> Type) : list A -> Type :=
    All_nil : All P []
  | All_cons : forall (x : A) (l : list A),
                  P x -> All P l -> All P (x :: l).

Inductive Alli {A} (P : nat -> A -> Type) (n : nat) : list A -> Type :=
| Alli_nil : Alli P n []
| Alli_cons hd tl : P n hd -> Alli P (S n) tl -> Alli P n (hd :: tl).

Inductive All2 {A B : Type} (R : A -> B -> Type) : list A -> list B -> Type :=
  All2_nil : All2 R [] []
| All2_cons : forall (x : A) (y : B) (l : list A) (l' : list B),
    R x y -> All2 R l l' -> All2 R (x :: l) (y :: l').

Inductive OnOne2 {A : Type} (P : A -> A -> Type) : list A -> list A -> Type :=
| OnOne2_hd hd hd' tl : P hd hd' -> OnOne2 P (hd :: tl) (hd' :: tl)
| OnOne2_tl hd tl tl' : OnOne2 P tl tl' -> OnOne2 P (hd :: tl) (hd :: tl').
Import Coq.Strings.Ascii.
Import Coq.Strings.String.

Definition bool_compare (x y : bool) : comparison :=
  if x then if y then Eq else Gt else if y then Lt else Eq.

Local Notation " c ?? y " := (match c with Eq => y | Lt => Lt | Gt => Gt end)
                               (at level 100).

Definition ascii_compare x y :=
  let 'Ascii a b c d e f g h := x in
  let 'Ascii a' b' c' d' e' f' g' h' := y in
  bool_compare a a'
    ?? bool_compare b b'
    ?? bool_compare c c'
    ?? bool_compare d d'
    ?? bool_compare e e'
    ?? bool_compare f f'
    ?? bool_compare g g'
    ?? bool_compare h h'.

Fixpoint string_compare x y :=
  match x, y with
  | EmptyString, EmptyString => Eq
  | String a s, String b s' =>
    match ascii_compare a b with
    | Eq => string_compare s s'
    | Lt => Lt
    | Gt => Gt
    end
  | EmptyString, String _ _ => Lt
  | String _ _, EmptyString => Gt
  end.

Definition string_lt x y : Prop := string_compare x y = Lt.
Export MetaCoq.Template.utils.MCPrelude.
Export MetaCoq.Template.utils.MCRelations.

Class Monad@{d c} (m : Type@{d} -> Type@{c}) : Type :=
{ ret : forall {t : Type@{d}}, t -> m t
; bind : forall {t u : Type@{d}}, m t -> (t -> m u) -> m u
}.
  Delimit Scope monad_scope with monad.

  Notation "x <- c1 ;; c2" := (@bind _ _ _ _ c1 (fun x => c2))
    (at level 100, c1 at next level, right associativity) : monad_scope.

Instance option_monad : Monad option :=
  {| ret A a := Some a ;
     bind A B m f :=
       match m with
       | Some a => f a
       | None => None
       end
  |}.

Open Scope monad.

Export Coq.Bool.Bool.
Export Coq.ZArith.ZArith.

Global Set Asymmetric Patterns.
Notation "A * B" := (prod A B) : type_scope2.
Global Open Scope type_scope2.
Import Coq.Floats.SpecFloat.
Import Equations.Prop.Equations.

Definition ident   := string.

Definition dirpath := list ident.

Inductive modpath :=
| MPfile  (dp : dirpath)
| MPbound (dp : dirpath) (id : ident) (i : nat)
| MPdot   (mp : modpath) (id : ident).
Derive NoConfusion EqDec for modpath.

Definition kername := modpath × ident.

Inductive name : Set :=
| nAnon
| nNamed (_ : ident).

Inductive relevance : Set := Relevant | Irrelevant.

Record binder_annot (A : Type) := mkBindAnn { binder_name : A; binder_relevance : relevance }.

Arguments mkBindAnn {_}.
Arguments binder_name {_}.
Arguments binder_relevance {_}.

Definition eq_binder_annot {A} (b b' : binder_annot A) : Prop :=
  b.(binder_relevance) = b'.(binder_relevance).

Definition aname := binder_annot name.

Record inductive : Set := mkInd { inductive_mind : kername ;
                                  inductive_ind : nat }.

Definition projection : Set := inductive * nat   * nat  .

Inductive global_reference :=
| VarRef : ident -> global_reference
| ConstRef : kername -> global_reference
| IndRef : inductive -> global_reference
| ConstructRef : inductive -> nat -> global_reference.

Definition kername_eq_dec (k k0 : kername) : {k = k0} + {k <> k0} := Classes.eq_dec k k0.

Definition eq_kername (k k0 : kername) : bool :=
  match kername_eq_dec k k0 with
  | left _ => true
  | right _ => false
  end.

Inductive recursivity_kind :=
  | Finite
  | CoFinite
  | BiFinite  .

Record def term := mkdef {
  dname : aname;
  dtype : term;
  dbody : term;
  rarg  : nat    }.

Arguments dname {term} _.
Arguments dtype {term} _.
Arguments dbody {term} _.
Arguments rarg {term} _.

Definition map_def {A B} (tyf bodyf : A -> B) (d : def A) :=
  {| dname := d.(dname); dtype := tyf d.(dtype); dbody := bodyf d.(dbody); rarg := d.(rarg) |}.

Definition mfixpoint term := list (def term).

Definition test_def {A} (tyf bodyf : A -> bool) (d : def A) :=
  tyf d.(dtype) && bodyf d.(dbody).

Definition uint_size := 63.
Definition uint_wB := (2 ^ (Z.of_nat uint_size))%Z.
Definition uint63_model := { z : Z | ((0 <=? z) && (z <? uint_wB))%Z }.

Definition prec := 53%Z.
Definition emax := 1024%Z.

Definition float64_model := sig (valid_binary prec emax).

Class checker_flags := {

  check_univs : bool ;

  prop_sub_type : bool ;

  indices_matter : bool
}.
Module Export Universes.
Import Coq.MSets.MSetProperties.

Record valuation :=
  { valuation_mono : string -> positive ;
    valuation_poly : nat -> nat }.

Inductive universes :=
  | UProp
  | USProp
  | UType (i : nat).

Class Evaluable (A : Type) := val : valuation -> A -> nat.

Inductive allowed_eliminations : Set :=
| IntoSProp
| IntoPropSProp
| IntoSetPropSProp
| IntoAny.

Module Level.
  Inductive t_ : Set :=
  | lSet
  | Level (_ : string)
  | Var (_ : nat)  .

  Definition t := t_.

  Definition is_var (l : t) :=
    match l with
    | Var _ => true
    | _ => false
    end.

  Global Instance Evaluable : Evaluable t
    := fun v l => match l with
               | lSet =>  (0%nat)
               | Level s => (Pos.to_nat (v.(valuation_mono) s))
               | Var x => (v.(valuation_poly) x)
               end.

  Definition compare (l1 l2 : t) : comparison :=
    match l1, l2 with
    | lSet, lSet => Eq
    | lSet, _ => Lt
    | _, lSet => Gt
    | Level s1, Level s2 => string_compare s1 s2
    | Level _, _ => Lt
    | _, Level _ => Gt
    | Var n, Var m => Nat.compare n m
    end.

  Definition eq : t -> t -> Prop := eq.
  Definition eq_equiv : Equivalence eq := _.

  Definition eq_dec (l1 l2 : t) : {l1 = l2}+{l1 <> l2}.
admit.
Defined.

  Inductive lt_ : t -> t -> Prop :=
  | ltSetLevel s : lt_ lSet (Level s)
  | ltSetVar n : lt_ lSet (Var n)
  | ltLevelLevel s s' : string_lt s s' -> lt_ (Level s) (Level s')
  | ltLevelVar s n : lt_ (Level s) (Var n)
  | ltVarVar n n' : Nat.lt n n' -> lt_ (Var n) (Var n').

  Definition lt := lt_.

  Definition lt_strorder : StrictOrder lt.
admit.
Defined.

  Definition lt_compat : Proper (eq ==> eq ==> iff) lt.
admit.
Defined.

  Definition compare_spec :
    forall x y : t, CompareSpec (x = y) (lt x y) (lt y x) (compare x y).
admit.
Defined.

  Definition eq_leibniz (x y : t) : eq x y -> x = y := id.

End Level.

Module LevelSet := MSetList.MakeWithLeibniz Level.
Module LevelSetProp := WPropertiesOn Level LevelSet.

Module UnivExpr.

  Definition t := (Level.t * nat)%type.

  Global Instance Evaluable : Evaluable t
    := fun v l => (snd l + val v (fst l)).

  Definition succ (l : t) := (fst l, S (snd l)).

  Definition get_level (e : t) : Level.t := fst e.

  Definition make (l : Level.t) : t := (l, 0%nat).
  Definition type1 : t := (Level.lSet, 1%nat).

  Definition eq : t -> t -> Prop := eq.

  Definition eq_equiv : Equivalence eq := _.

  Inductive lt_ : t -> t -> Prop :=
  | ltUnivExpr1 l n n' : (n < n')%nat -> lt_ (l, n) (l, n')
  | ltUnivExpr2 l l' b b' : Level.lt l l' -> lt_ (l, b) (l', b').

  Definition lt := lt_.

  Global Instance lt_strorder : StrictOrder lt.
admit.
Defined.

  Definition lt_compat : Proper (Logic.eq ==> Logic.eq ==> iff) lt.
admit.
Defined.

  Definition compare (x y : t) : comparison :=
    match x, y with
    | (l1, b1), (l2, b2) =>
      match Level.compare l1 l2 with
      | Eq => Nat.compare b1 b2
      | x => x
      end
    end.

  Definition compare_spec :
    forall x y : t, CompareSpec (x = y) (lt x y) (lt y x) (compare x y).
admit.
Defined.

  Definition eq_dec (l1 l2 : t) : {l1 = l2} + {l1 <> l2}.
admit.
Defined.

  Definition eq_leibniz (x y : t) : eq x y -> x = y := id.

End UnivExpr.

Module UnivExprSet := MSetList.MakeWithLeibniz UnivExpr.

Module Universe.

  Record t0 := { t_set : UnivExprSet.t ;
                 t_ne  : UnivExprSet.is_empty t_set = false }.

  Inductive t_ :=
    lProp | lSProp | lType (_ : t0).

  Definition t := t_.

  Coercion t_set : t0 >-> UnivExprSet.t.

  Definition make' (e : UnivExpr.t) : t0
    := {| t_set := UnivExprSet.singleton e;
          t_ne := eq_refl |}.

  Definition make (l : Level.t) : t :=
    lType (make' (UnivExpr.make l)).

  Program Definition add (e : UnivExpr.t) (u : t0) : t0
    := {| t_set := UnivExprSet.add e u |}.
Admit Obligations.

  Definition add_list : list UnivExpr.t -> t0 -> t0
    := List.fold_left (fun u e => add e u).

  Definition is_sprop (u : t) : bool :=
    match u with
      | lSProp => true
      | _ => false
    end.

  Definition is_prop (u : t) : bool :=
    match u with
      | lProp => true
      | _ => false
    end.
  Definition type1 : t := lType (make' UnivExpr.type1).

  Program Definition exprs (u : t0) : UnivExpr.t * list UnivExpr.t
    := match UnivExprSet.elements u with
       | [] => False_rect _ _
       | e :: l => (e, l)
       end.
Admit Obligations.

  Definition map (f : UnivExpr.t -> UnivExpr.t) (u : t0) : t0 :=
    let '(e, l) := exprs u in
    add_list (List.map f l) (make' (f e)).

  Definition super (l : t) : t :=
    match l with
    | lSProp => type1
    | lProp => type1
    | lType l => lType (map UnivExpr.succ l)
    end.

  Program Definition sup0 (u v : t0) : t0 :=
    {| t_set := UnivExprSet.union u v |}.
Admit Obligations.

  Definition sup (u v : t) : t :=
    match u,v with
    | lSProp, lProp => lProp
    | lProp, lSProp => lProp
    | (lSProp | lProp), u' => u'
    | u', (lSProp | lProp) => u'
    | lType l1, lType l2  => lType (sup0 l1 l2)
    end.

  Definition sort_of_product (domsort rangsort : t) :=

    if Universe.is_prop rangsort || Universe.is_sprop rangsort then rangsort
    else Universe.sup domsort rangsort.

  Global Instance Evaluable' : Evaluable t0
    := fun v u => let '(e, u) := Universe.exprs u in
               List.fold_left (fun n e => Nat.max (val v e) n) u (val v e).

  Definition univ_val :=
    fun v u => match u with
            | lSProp => USProp
            | lProp => UProp
            | lType l => UType (val v l)
            end.

End Universe.

Definition is_propositional u :=
  Universe.is_prop u || Universe.is_sprop u.

Coercion Universe.t_set : Universe.t0 >-> UnivExprSet.t.
Delimit Scope univ_scope with u.

Module Export ConstraintType.
  Inductive t_ : Set := Le (z : Z) | Eq.

  Definition t := t_.

  Inductive lt_ : t -> t -> Prop :=
  | LeLe n m : (n < m)%Z -> lt_ (Le n) (Le m)
  | LeEq n : lt_ (Le n) Eq.
  Definition lt := lt_.

  Definition compare (x y : t) : comparison :=
    match x, y with
    | Le n, Le m => Z.compare n m
    | Le _, Eq => Datatypes.Lt
    | Eq, Eq => Datatypes.Eq
    | Eq, _  => Datatypes.Gt
    end.
End ConstraintType.

Module UnivConstraint.
  Definition t : Set := Level.t * ConstraintType.t * Level.t.

  Definition eq : t -> t -> Prop := eq.
  Definition eq_equiv : Equivalence eq := _.

  Inductive lt_ : t -> t -> Prop :=
  | lt_Level2 l1 t l2 l2' : Level.lt l2 l2' -> lt_ (l1, t, l2) (l1, t, l2')
  | lt_Cstr l1 t t' l2 l2' : ConstraintType.lt t t' -> lt_ (l1, t, l2) (l1, t', l2')
  | lt_Level1 l1 l1' t t' l2 l2' : Level.lt l1 l1' -> lt_ (l1, t, l2) (l1', t', l2').
  Definition lt := lt_.

  Lemma lt_strorder : StrictOrder lt.
admit.
Defined.

  Lemma lt_compat : Proper (eq ==> eq ==> iff) lt.
admit.
Defined.

  Definition compare : t -> t -> comparison :=
    fun '(l1, t, l2) '(l1', t', l2') =>
      Pos.switch_Eq (Pos.switch_Eq (Level.compare l2 l2')
                                   (ConstraintType.compare t t'))
                    (Level.compare l1 l1').

  Lemma compare_spec x y
    : CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
admit.
Defined.

  Lemma eq_dec x y : {eq x y} + {~ eq x y}.
admit.
Defined.

  Definition eq_leibniz (x y : t) : eq x y -> x = y := id.
End UnivConstraint.

Module ConstraintSet := MSetList.MakeWithLeibniz UnivConstraint.

Module Export Instance.

  Definition t : Set := list Level.t.

  Definition empty : t := [].
End Instance.

Module Export UContext.
  Definition t := list name × (Instance.t × ConstraintSet.t).

  Definition instance : t -> Instance.t := fun x => fst (snd x).
End UContext.

Module Export AUContext.
  Definition t := list name × ConstraintSet.t.
  Definition repr (x : t) : UContext.t :=
    let (u, cst) := x in
    (u, (mapi (fun i _ => Level.Var i) u, cst)).

  Definition levels (uctx : t) : LevelSet.t :=
    LevelSetProp.of_list (fst (snd (repr uctx))).
End AUContext.

Module Export ContextSet.
  Definition t := LevelSet.t × ConstraintSet.t.

  Definition empty : t := (LevelSet.empty, ConstraintSet.empty).
End ContextSet.

Module Export Variance.

  Inductive t :=
  | Irrelevant : t
  | Covariant : t
  | Invariant : t.

Inductive universes_decl : Type :=
| Monomorphic_ctx (ctx : ContextSet.t)
| Polymorphic_ctx (cst : AUContext.t).

Definition monomorphic_udecl u :=
  match u with
  | Monomorphic_ctx ctx => ctx
  | _ => ContextSet.empty
  end.

Definition levels_of_udecl u :=
  match u with
  | Monomorphic_ctx ctx => fst ctx
  | Polymorphic_ctx ctx => AUContext.levels ctx
  end.

Definition constraints_of_udecl u :=
  match u with
  | Monomorphic_ctx ctx => snd ctx
  | Polymorphic_ctx ctx => snd (snd (AUContext.repr ctx))
  end.

Definition univ_le_n {cf:checker_flags} n u u' :=
  match u, u' with
  | UProp, UProp
  | USProp, USProp => (n = 0)%Z
  | UType u, UType u' => (Z.of_nat u <= Z.of_nat u' - n)%Z
  | UProp, UType u =>
    if prop_sub_type then True else False
  | _, _ => False
  end.
Notation "x <= y" := (univ_le_n 0 x y) : univ_scope.

Section Univ.
  Context {cf:checker_flags}.

  Inductive satisfies0 (v : valuation) : UnivConstraint.t -> Prop :=
  | satisfies0_Lt (l l' : Level.t) (z : Z) : (Z.of_nat (val v l) <= Z.of_nat (val v l') - z)%Z
                         -> satisfies0 v (l, ConstraintType.Le z, l')
  | satisfies0_Eq (l l' : Level.t) : val v l = val v l'
                         -> satisfies0 v (l, ConstraintType.Eq, l').

  Definition satisfies v : ConstraintSet.t -> Prop :=
    ConstraintSet.For_all (satisfies0 v).

  Definition consistent ctrs := exists v, satisfies v ctrs.

  Definition eq_universe0 (φ : ConstraintSet.t) u u' :=
    forall v, satisfies v φ -> (Universe.univ_val v u = Universe.univ_val v u').

  Definition leq_universe0 (φ : ConstraintSet.t) u u' :=
    forall v, satisfies v φ -> (Universe.univ_val v u <= Universe.univ_val v u')%u.

  Definition eq_universe φ u u'
    := if check_univs then eq_universe0 φ u u' else True.

  Definition leq_universe φ u u'
    := if check_univs then leq_universe0 φ u u' else True.

  Definition valid_constraints0 φ ctrs
    := forall v, satisfies v φ -> satisfies v ctrs.

  Definition valid_constraints φ ctrs
    := if check_univs then valid_constraints0 φ ctrs else True.

  Definition is_allowed_elimination0
             φ (into : Universe.t) (allowed : allowed_eliminations) : Prop :=
    forall v,
      satisfies v φ ->
      match allowed, Universe.univ_val v into with
      | IntoSProp, USProp
      | IntoPropSProp, (UProp | USProp)
      | IntoSetPropSProp, (UProp | USProp | UType 0)
      | IntoAny, _ => True
      | _, _ => False
      end.

  Definition is_allowed_elimination φ into allowed :=
    if check_univs then is_allowed_elimination0 φ into allowed else True.

  Definition allowed_eliminations_subset (a a' : allowed_eliminations) : bool :=
    match a, a' with
    | IntoSProp, _
    | IntoPropSProp, (IntoPropSProp | IntoSetPropSProp | IntoAny)
    | IntoSetPropSProp, (IntoSetPropSProp | IntoAny)
    | IntoAny, IntoAny => true
    | _, _ => false
    end.

End Univ.

Class UnivSubst A := subst_instance : Instance.t -> A -> A.

Instance subst_instance_level : UnivSubst Level.t :=
  fun u l => match l with
            Level.lSet | Level.Level _ => l
          | Level.Var n => List.nth n u Level.lSet
          end.

Instance subst_instance_cstr : UnivSubst UnivConstraint.t :=
  fun u c => (subst_instance_level u c.1.1, c.1.2, subst_instance_level u c.2).

Instance subst_instance_cstrs : UnivSubst ConstraintSet.t :=
  fun u ctrs => ConstraintSet.fold (fun c => ConstraintSet.add (subst_instance_cstr u c))
                                ctrs ConstraintSet.empty.

Instance subst_instance_level_expr : UnivSubst UnivExpr.t :=
  fun u e => match e with
          | (Level.lSet, _)
          | (Level.Level _, _) => e
          | (Level.Var n, b) =>
            match nth_error u n with
            | Some l => (l,b)
            | None => (Level.lSet, b)
            end
          end.

Instance subst_instance_univ0 : UnivSubst Universe.t0 :=
  fun u => Universe.map (subst_instance_level_expr u).

Instance subst_instance_univ : UnivSubst Universe.t :=
  fun u e => match e with
          | Universe.lProp | Universe.lSProp => e
          | Universe.lType l => Universe.lType (subst_instance u l)
          end.

Instance subst_instance_instance : UnivSubst Instance.t :=
  fun u u' => List.map (subst_instance_level u) u'.

Module Type Term.

  Parameter Inline term : Type.

  Parameter Inline tRel : nat -> term.
  Parameter Inline tSort : Universe.t -> term.
  Parameter Inline tProd : aname -> term -> term -> term.
  Parameter Inline tLetIn : aname -> term -> term -> term -> term.
  Parameter Inline tProj : projection -> term -> term.
  Parameter Inline mkApps : term -> list term -> term.

End Term.

Module Environment (T : Term).

  Import T.

  Record context_decl := mkdecl {
    decl_name : aname ;
    decl_body : option term ;
    decl_type : term
  }.

  Definition vass x A :=
    {| decl_name := x ; decl_body := None ; decl_type := A |}.

  Definition vdef x t A :=
    {| decl_name := x ; decl_body := Some t ; decl_type := A |}.

  Definition context := list context_decl.

  Definition snoc {A} (Γ : list A) (d : A) := d :: Γ.

  Notation " Γ ,, d " := (snoc Γ d) (at level 20, d at next level).

  Definition map_decl f (d : context_decl) :=
    {| decl_name := d.(decl_name);
       decl_body := option_map f d.(decl_body);
       decl_type := f d.(decl_type) |}.

  Definition map_context f c :=
    List.map (map_decl f) c.

  Definition fold_context f (Γ : context) : context :=
    List.rev (mapi (fun k' decl => map_decl (f k') decl) (List.rev Γ)).

  Record one_inductive_body := {
    ind_name : ident;
    ind_type : term;
    ind_kelim : allowed_eliminations;
    ind_ctors : list (ident * term
                      * nat  );
    ind_projs : list (ident * term);
    ind_relevance : relevance   }.

  Record mutual_inductive_body := {
    ind_finite : recursivity_kind;
    ind_npars : nat;
    ind_params : context;
    ind_bodies : list one_inductive_body ;
    ind_universes : universes_decl;
    ind_variance : option (list Universes.Variance.t) }.

  Record constant_body := {
      cst_type : term;
      cst_body : option term;
      cst_universes : universes_decl }.

  Inductive global_decl :=
  | ConstantDecl : constant_body -> global_decl
  | InductiveDecl : mutual_inductive_body -> global_decl.

  Definition global_env := list (kername * global_decl).

  Definition global_env_ext : Type := global_env * universes_decl.

  Definition fst_ctx : global_env_ext -> global_env := fst.
  Coercion fst_ctx : global_env_ext >-> global_env.

  Definition app_context (Γ Γ' : context) : context := Γ' ++ Γ.
  Notation "Γ ,,, Γ'" :=
    (app_context Γ Γ') (at level 25, Γ' at next level, left associativity).

  Definition mkProd_or_LetIn d t :=
    match d.(decl_body) with
    | None => tProd d.(decl_name) d.(decl_type) t
    | Some b => tLetIn d.(decl_name) b d.(decl_type) t
    end.

  Definition it_mkProd_or_LetIn (l : context) (t : term) :=
    List.fold_left (fun acc d => mkProd_or_LetIn d acc) l t.

  Fixpoint reln (l : list term) (p : nat) (Γ0 : list context_decl) {struct Γ0} : list term :=
    match Γ0 with
    | [] => l
    | {| decl_body := Some _ |} :: hyps => reln l (p + 1) hyps
    | {| decl_body := None |} :: hyps => reln (tRel p :: l) (p + 1) hyps
    end.

  Definition to_extended_list_k Γ k := reln [] k Γ.
  Definition to_extended_list Γ := to_extended_list_k Γ 0.

  Definition arities_context (l : list one_inductive_body) :=
    rev_map (fun ind => vass (mkBindAnn (nNamed ind.(ind_name))
                            (ind.(ind_relevance))) ind.(ind_type)) l.

  Fixpoint context_assumptions (Γ : context) :=
    match Γ with
    | [] => 0
    | d :: Γ =>
      match d.(decl_body) with
      | Some _ => context_assumptions Γ
      | None => S (context_assumptions Γ)
      end
    end.

  Fixpoint lookup_env (Σ : global_env) (kn : kername) : option global_decl :=
    match Σ with
    | nil => None
    | d :: tl =>
      if eq_kername kn d.1 then Some d.2
      else lookup_env tl kn
    end.
End Environment.

Module Type EnvironmentSig (T : Term).
 Include Environment T.
End EnvironmentSig.
Module Export Reflect.

Class ReflectEq A := {
  eqb : A -> A -> bool ;
  eqb_spec : forall x y : A, reflect (x = y) (eqb x y)
}.

#[program] Instance reflect_kername : ReflectEq kername := {
  eqb := eq_kername
}.
Admit Obligations.

Instance reflect_recursivity_kind : ReflectEq recursivity_kind.
admit.
Defined.

Module Lookup (T : Term) (E : EnvironmentSig T).
Import E.

  Definition declared_constant (Σ : global_env) (id : kername) decl : Prop :=
    lookup_env Σ id = Some (ConstantDecl decl).

  Definition declared_minductive Σ mind decl :=
    lookup_env Σ mind = Some (InductiveDecl decl).

  Definition declared_inductive Σ mdecl ind decl :=
    declared_minductive Σ (inductive_mind ind) mdecl /\
    List.nth_error mdecl.(ind_bodies) (inductive_ind ind) = Some decl.

  Definition declared_constructor Σ mdecl idecl cstr cdecl : Prop :=
    declared_inductive Σ mdecl (fst cstr) idecl /\
    List.nth_error idecl.(ind_ctors) (snd cstr) = Some cdecl.

  Definition declared_projection Σ mdecl idecl (proj : projection) pdecl
  : Prop :=
    declared_inductive Σ mdecl (fst (fst proj)) idecl /\
    List.nth_error idecl.(ind_projs) (snd proj) = Some pdecl /\
    mdecl.(ind_npars) = snd (fst proj).

  Definition on_udecl_decl {A} (F : universes_decl -> A) d : A :=
  match d with
  | ConstantDecl cb => F cb.(cst_universes)
  | InductiveDecl mb => F mb.(ind_universes)
  end.

  Definition monomorphic_udecl_decl := on_udecl_decl monomorphic_udecl.

  Definition monomorphic_levels_decl := fst ∘ monomorphic_udecl_decl.

  Definition monomorphic_constraints_decl := snd ∘ monomorphic_udecl_decl.

  Definition universes_decl_of_decl := on_udecl_decl (fun x => x).

  Definition abstract_instance decl :=
    match decl with
    | Monomorphic_ctx _ => Instance.empty
    | Polymorphic_ctx auctx => UContext.instance (AUContext.repr auctx)
    end.

  Definition global_levels (Σ : global_env) : LevelSet.t :=
    fold_right
      (fun decl lvls => LevelSet.union (monomorphic_levels_decl decl.2) lvls)
      (LevelSet.singleton (Level.lSet)) Σ.

  Definition global_constraints (Σ : global_env) : ConstraintSet.t :=
    fold_right (fun decl ctrs =>
        ConstraintSet.union (monomorphic_constraints_decl decl.2) ctrs
      ) ConstraintSet.empty Σ.

  Definition global_ext_levels (Σ : global_env_ext) : LevelSet.t :=
    LevelSet.union (levels_of_udecl (snd Σ)) (global_levels Σ.1).

  Definition global_ext_constraints (Σ : global_env_ext) : ConstraintSet.t :=
    ConstraintSet.union
      (constraints_of_udecl (snd Σ))
      (global_constraints Σ.1).

  Coercion global_ext_constraints : global_env_ext >-> ConstraintSet.t.

  Definition consistent_instance `{checker_flags} (lvs : LevelSet.t) (φ : ConstraintSet.t) uctx (u : Instance.t) :=
    match uctx with
    | Monomorphic_ctx c => List.length u = 0
    | Polymorphic_ctx c =>

      forallb (fun l => LevelSet.mem l lvs) u /\
      List.length u = List.length c.1 /\
      valid_constraints φ (subst_instance_cstrs u c.2)
    end.

  Definition consistent_instance_ext `{checker_flags} Σ :=
    consistent_instance (global_ext_levels Σ) (global_ext_constraints Σ).

End Lookup.

Module Type LookupSig (T : Term) (E : EnvironmentSig T).
  Include Lookup T E.
End LookupSig.

Module EnvTyping (T : Term) (E : EnvironmentSig T).
Import T.
Import E.

  Section TypeLocal.
    Context (typing : forall (Γ : context), term -> option term -> Type).

    Inductive All_local_env : context -> Type :=
    | localenv_nil :
        All_local_env []

    | localenv_cons_abs Γ na t :
        All_local_env Γ ->
        typing Γ t None ->
        All_local_env (Γ ,, vass na t)

    | localenv_cons_def Γ na b t :
        All_local_env Γ ->
        typing Γ t None ->
        typing Γ b (Some t) ->
        All_local_env (Γ ,, vdef na b t).
  End TypeLocal.

  Inductive context_relation (P : context -> context -> context_decl -> context_decl -> Type)
            : forall (Γ Γ' : context), Type :=
  | ctx_rel_nil : context_relation P nil nil
  | ctx_rel_vass na na' T U Γ Γ' :
      context_relation P Γ Γ' ->
      P Γ Γ' (vass na T) (vass na' U) ->
      context_relation P (vass na T :: Γ) (vass na' U :: Γ')
  | ctx_rel_def na na' t T u U Γ Γ' :
      context_relation P Γ Γ' ->
      P Γ Γ' (vdef na t T) (vdef na' u U) ->
      context_relation P (vdef na t T :: Γ) (vdef na' u U :: Γ').

  Definition lift_typing (P : global_env_ext -> context -> term -> term -> Type) :
  (global_env_ext -> context -> term -> option term -> Type) :=
    fun Σ Γ t T =>
      match T with
      | Some T => P Σ Γ t T
      | None => { s : Universe.t & P Σ Γ t (tSort s) }
      end.

  End EnvTyping.

Module Type EnvTypingSig (T : Term) (E : EnvironmentSig T).
  Include EnvTyping T E.
End EnvTypingSig.

Module Type Typing (T : Term) (E : EnvironmentSig T) (ET : EnvTypingSig T E).
Import T.
Import E.

  Parameter (conv : forall `{checker_flags}, global_env_ext -> context -> term -> term -> Type).
  Parameter (cumul : forall `{checker_flags}, global_env_ext -> context -> term -> term -> Type).

  Parameter (wf_universe : global_env_ext -> Universe.t -> Prop).

  Parameter Inline smash_context : context -> context -> context.
  Parameter Inline lift_context : nat -> nat -> context -> context.
  Parameter Inline expand_lets : context -> term -> term.
  Parameter Inline expand_lets_ctx : context -> context -> context.
  Parameter Inline subst_telescope : list term -> nat -> context -> context.
  Parameter Inline subst_instance_context : Instance.t -> context -> context.
  Parameter Inline subst_instance_constr : Instance.t -> term  -> term.
  Parameter Inline lift : nat -> nat -> term -> term.
  Parameter Inline subst : list term -> nat -> term -> term.
  Parameter Inline inds : kername -> Instance.t -> list one_inductive_body -> list term.

  Parameter destArity : term -> option (context * Universe.t).
  Parameter Inline closedn : nat -> term -> bool.

End Typing.

Module DeclarationTyping (T : Term) (E : EnvironmentSig T)
  (ET : EnvTypingSig T E) (Ty : Typing T E ET) (L : LookupSig T E).
Import T.
Import E.
Import Ty.
Import L.
Import ET.

  Section ContextConversion.
    Context {cf : checker_flags}.
    Context (Σ : global_env_ext).

    Inductive cumul_decls (Γ Γ' : context) : forall (x y : context_decl), Type :=
    | cumul_vass na na' T T' :
        eq_binder_annot na na' ->
        cumul Σ Γ T T' ->
        cumul_decls Γ Γ' (vass na T) (vass na' T')

    | cumul_vdef_body na na' b b' T T' :
        eq_binder_annot na na' ->
        conv Σ Γ b b' ->
        cumul Σ Γ T T' ->
        cumul_decls Γ Γ' (vdef na b T) (vdef na' b' T').
  End ContextConversion.

  Definition cumul_ctx_rel {cf:checker_flags} Σ Γ Δ Δ' :=
    context_relation (fun Δ Δ' => cumul_decls Σ (Γ ,,, Δ) (Γ ,,, Δ')) Δ Δ'.

  Section GlobalMaps.

    Context {cf: checker_flags}.
    Context (P : global_env_ext -> context -> term -> option term -> Type).

    Definition on_context Σ ctx :=
      All_local_env (P Σ) ctx.

    Fixpoint type_local_ctx Σ (Γ Δ : context) (u : Universe.t) : Type :=
      match Δ with
      | [] => wf_universe Σ u
      | {| decl_body := None; decl_type := t |} :: Δ => (type_local_ctx Σ Γ Δ u * (P Σ (Γ ,,, Δ) t (Some (tSort u))))
      | {| decl_body := Some b; decl_type := t |} :: Δ => (type_local_ctx Σ Γ Δ u * (P Σ (Γ ,,, Δ) t None * P Σ (Γ ,,, Δ) b (Some t)))
      end.

    Fixpoint sorts_local_ctx Σ (Γ Δ : context) (us : list Universe.t) : Type :=
      match Δ, us with
      | [], [] => unit
      | {| decl_body := None; decl_type := t |} :: Δ, u :: us =>
        (sorts_local_ctx Σ Γ Δ us * (P Σ (Γ ,,, Δ) t (Some (tSort u))))
      | {| decl_body := Some b; decl_type := t |} :: Δ, us =>
        (sorts_local_ctx Σ Γ Δ us * (P Σ (Γ ,,, Δ) t None * P Σ (Γ ,,, Δ) b (Some t)))
      | _, _ => False
      end.

    Inductive ctx_inst Σ (Γ : context) : list term -> context -> Type :=
    | ctx_inst_nil : ctx_inst Σ Γ [] []
    | ctx_inst_ass na t i inst Δ :
      P Σ Γ i (Some t) ->
      ctx_inst Σ Γ inst (subst_telescope [i] 0 Δ) ->
      ctx_inst Σ Γ (i :: inst) (vass na t :: Δ)
    | ctx_inst_def na b t inst Δ :
      ctx_inst Σ Γ inst (subst_telescope [b] 0 Δ) ->
      ctx_inst Σ Γ inst (vdef na b t :: Δ).

    Implicit Types (mdecl : mutual_inductive_body) (idecl : one_inductive_body) (cdecl : ident * term * nat).

    Definition on_type Σ Γ T := P Σ Γ T None.

    Definition cdecl_type cdecl := cdecl.1.2.
    Definition cdecl_args cdecl := cdecl.2.

    Record constructor_shape :=
      { cshape_args : context;

        cshape_indices : list term;

        cshape_sorts : list Universe.t;

      }.

    Definition ind_realargs (o : one_inductive_body) :=
      match destArity o.(ind_type) with
      | Some (ctx, _) => #|smash_context [] ctx|
      | _ => 0
      end.

    Inductive positive_cstr_arg mdecl ctx : term -> Type :=
    | positive_cstr_arg_closed t :
      closedn #|ctx| t ->
      positive_cstr_arg mdecl ctx t

    | positive_cstr_arg_concl l k i :

      #|ctx| <= k -> k < #|ctx| + #|mdecl.(ind_bodies)| ->
      All (closedn #|ctx|) l ->
      nth_error (List.rev mdecl.(ind_bodies)) (k - #|ctx|) = Some i ->
      #|l| = ind_realargs i ->
      positive_cstr_arg mdecl ctx (mkApps (tRel k) l)

    | positive_cstr_arg_let na b ty t :
      positive_cstr_arg mdecl ctx (subst [b] 0 t) ->
      positive_cstr_arg mdecl ctx (tLetIn na b ty t)

    | positive_cstr_arg_ass na ty t :
      closedn #|ctx| ty ->
      positive_cstr_arg mdecl (vass na ty :: ctx) t ->
      positive_cstr_arg mdecl ctx (tProd na ty t).

    Inductive positive_cstr mdecl i (ctx : context) : term -> Type :=
    | positive_cstr_concl indices :
      let headrel : nat :=
        (#|mdecl.(ind_bodies)| - S i + #|ctx|)%nat in
      All (closedn #|ctx|) indices ->
      positive_cstr mdecl i ctx (mkApps (tRel headrel) indices)

    | positive_cstr_let na b ty t :
      positive_cstr mdecl i ctx (subst [b] 0 t) ->
      positive_cstr mdecl i ctx (tLetIn na b ty t)

    | positive_cstr_ass na ty t :
      positive_cstr_arg mdecl ctx ty ->
      positive_cstr mdecl i (vass na ty :: ctx) t ->
      positive_cstr mdecl i ctx (tProd na ty t).

    Definition lift_level n l :=
      match l with
      | Level.lSet | Level.Level _ => l
      | Level.Var k => Level.Var (n + k)
      end.

    Definition lift_instance n l :=
      map (lift_level n) l.

    Definition lift_constraint n (c : Level.t * ConstraintType.t * Level.t) :=
      let '((l, r), l') := c in
      ((lift_level n l, r), lift_level n l').

    Definition lift_constraints n cstrs :=
      ConstraintSet.fold (fun elt acc => ConstraintSet.add (lift_constraint n elt) acc)
        cstrs ConstraintSet.empty.

    Definition level_var_instance n (inst : list name) :=
      mapi_rec (fun i _ => Level.Var i) inst n.

    Fixpoint variance_cstrs (v : list Variance.t) (u u' : Instance.t) :=
      match v, u, u' with
      | _, [], [] => ConstraintSet.empty
      | v :: vs, u :: us, u' :: us' =>
        match v with
        | Variance.Irrelevant => variance_cstrs vs us us'
        | Variance.Covariant => ConstraintSet.add (u, ConstraintType.Le 0, u') (variance_cstrs vs us us')
        | Variance.Invariant => ConstraintSet.add (u, ConstraintType.Eq, u') (variance_cstrs vs us us')
        end
      | _, _, _ =>   ConstraintSet.empty
      end.

    Definition variance_universes univs v :=
      match univs with
      | Monomorphic_ctx ctx => None
      | Polymorphic_ctx auctx =>
        let (inst, cstrs) := auctx in
        let u' := level_var_instance 0 inst in
        let u := lift_instance #|inst| u' in
        let cstrs := ConstraintSet.union cstrs (lift_constraints #|inst| cstrs) in
        let cstrv := variance_cstrs v u u' in
        let auctx' := (inst ++ inst, ConstraintSet.union cstrs cstrv) in
        Some (Polymorphic_ctx auctx', u, u')
      end.

    Definition ind_arities mdecl := arities_context (ind_bodies mdecl).

    Definition ind_respects_variance Σ mdecl v indices :=
      let univs := ind_universes mdecl in
      match variance_universes univs v with
      | Some (univs, u, u') =>
        cumul_ctx_rel (Σ, univs) (subst_instance_context u (smash_context [] (ind_params mdecl)))
          (subst_instance_context u (expand_lets_ctx (ind_params mdecl) (smash_context [] indices)))
          (subst_instance_context u' (expand_lets_ctx (ind_params mdecl) (smash_context [] indices)))
      | None => False
      end.

    Definition cstr_respects_variance Σ mdecl v cs :=
      let univs := ind_universes mdecl in
      match variance_universes univs v with
      | Some (univs, u, u') =>
        cumul_ctx_rel (Σ, univs) (subst_instance_context u (ind_arities mdecl ,,, smash_context [] (ind_params mdecl)))
          (subst_instance_context u (expand_lets_ctx (ind_params mdecl) (smash_context [] (cshape_args cs))))
          (subst_instance_context u' (expand_lets_ctx (ind_params mdecl) (smash_context [] (cshape_args cs)))) *
        All2
          (conv (Σ, univs) (subst_instance_context u (ind_arities mdecl ,,, smash_context [] (ind_params mdecl ,,, cshape_args cs))))
          (map (subst_instance_constr u ∘ expand_lets (ind_params mdecl ,,, cshape_args cs)) (cshape_indices cs))
          (map (subst_instance_constr u' ∘ expand_lets (ind_params mdecl ,,, cshape_args cs)) (cshape_indices cs))
      | None => False
      end.

    Record on_constructor Σ mdecl i idecl ind_indices cdecl (cshape : constructor_shape) := {

      cstr_args_length : context_assumptions (cshape_args cshape) = cdecl_args cdecl;

      cstr_concl_head := tRel (#|mdecl.(ind_bodies)|
      - S i
      + #|mdecl.(ind_params)|
      + #|cshape_args cshape|);

      cstr_eq : cdecl_type cdecl =
       it_mkProd_or_LetIn mdecl.(ind_params)
                          (it_mkProd_or_LetIn (cshape_args cshape)
                              (mkApps cstr_concl_head
                              (to_extended_list_k mdecl.(ind_params) #|cshape_args cshape|
                                ++ cshape_indices cshape)));

      on_ctype : on_type Σ (arities_context mdecl.(ind_bodies)) (cdecl_type cdecl);
      on_cargs :
        sorts_local_ctx Σ (arities_context mdecl.(ind_bodies) ,,, mdecl.(ind_params))
                      cshape.(cshape_args) cshape.(cshape_sorts);
      on_cindices :
        ctx_inst Σ (arities_context mdecl.(ind_bodies) ,,, mdecl.(ind_params) ,,, cshape.(cshape_args))
                      cshape.(cshape_indices)
                      (List.rev (lift_context #|cshape.(cshape_args)| 0 ind_indices));

      on_ctype_positive :
        positive_cstr mdecl i [] (cdecl_type cdecl);

      on_ctype_variance :
        forall v, ind_variance mdecl = Some v ->
        cstr_respects_variance Σ mdecl v cshape
    }.

    Definition on_constructors Σ mdecl i idecl ind_indices :=
      All2 (on_constructor Σ mdecl i idecl ind_indices).

    Fixpoint projs ind npars k :=
      match k with
      | 0 => []
      | S k' => (tProj ((ind, npars), k') (tRel 0)) :: projs ind npars k'
      end.

    Definition on_projection mdecl mind i cshape (k : nat) (p : ident * term) :=
      let Γ := smash_context [] (cshape.(cshape_args) ++ mdecl.(ind_params)) in
      match nth_error Γ (context_assumptions cshape.(cshape_args) - S k) with
      | None => False
      | Some decl =>
        let u := abstract_instance mdecl.(ind_universes) in
        let ind := {| inductive_mind := mind; inductive_ind := i |} in

        (binder_name (decl_name decl) = nNamed (fst p)) /\
        (snd p = subst (inds mind u mdecl.(ind_bodies)) (S (ind_npars mdecl))
              (subst (projs ind mdecl.(ind_npars) k) 0
                (lift 1 k (decl_type decl))))
      end.

    Record on_projections mdecl mind i idecl (ind_indices : context) cshape :=
      { on_projs_record : #|idecl.(ind_ctors)| = 1;

        on_projs_noidx : #|ind_indices| = 0;

        on_projs_elim : idecl.(ind_kelim) = IntoAny;

        on_projs_all : #|idecl.(ind_projs)| = context_assumptions (cshape_args cshape);

        on_projs : Alli (on_projection mdecl mind i cshape) 0 idecl.(ind_projs) }.

    Definition check_constructors_smaller φ cshapes ind_sort :=
      Forall (fun cs =>
        Forall (fun argsort => leq_universe φ argsort ind_sort) cs.(cshape_sorts)) cshapes.

    Definition elim_sort_prop_ind (ind_ctors_sort : list constructor_shape) :=
      match ind_ctors_sort with
      | [] =>   IntoAny
      | [ s ] =>
        if forallb Universes.is_propositional (cshape_sorts s) then
          IntoAny
        else
          IntoPropSProp
      | _ =>   IntoPropSProp
      end.

    Definition elim_sort_sprop_ind (ind_ctors_sort : list constructor_shape) :=
      match ind_ctors_sort with
      | [] =>   IntoAny
      | _ =>   IntoSProp
      end.

    Definition check_ind_sorts (Σ : global_env_ext)
              params kelim ind_indices cshapes ind_sort : Type :=
      if Universe.is_prop ind_sort then

        allowed_eliminations_subset kelim (elim_sort_prop_ind cshapes)
      else if Universe.is_sprop ind_sort then

        allowed_eliminations_subset kelim (elim_sort_sprop_ind cshapes)
      else

        check_constructors_smaller Σ cshapes ind_sort
        × if indices_matter then
            type_local_ctx Σ params ind_indices ind_sort
          else True.

    Record on_ind_body Σ mind mdecl i idecl :=
      {
        ind_indices : context;
        ind_sort : Universe.t;
        ind_arity_eq : idecl.(ind_type)
                      = it_mkProd_or_LetIn mdecl.(ind_params)
                                (it_mkProd_or_LetIn ind_indices (tSort ind_sort));

        onArity : on_type Σ [] idecl.(ind_type);

        ind_cshapes : list constructor_shape;

        onConstructors :
          on_constructors Σ mdecl i idecl ind_indices idecl.(ind_ctors) ind_cshapes;

        onProjections :
          idecl.(ind_projs) <> [] ->
          match ind_cshapes return Type with
          | [ o ] =>
            on_projections mdecl mind i idecl ind_indices o
          | _ => False
          end;

        ind_sorts :
          check_ind_sorts Σ mdecl.(ind_params) idecl.(ind_kelim)
                          ind_indices ind_cshapes ind_sort;

        onIndices :

          forall v, ind_variance mdecl = Some v ->
          ind_respects_variance Σ mdecl v ind_indices
      }.

    Definition on_variance univs (variances : option (list Variance.t)) :=
      match univs with
      | Monomorphic_ctx _ => variances = None
      | Polymorphic_ctx auctx =>
        match variances with
        | None => True
        | Some v => List.length v = #|UContext.instance (AUContext.repr auctx)|
        end
      end.

    Record on_inductive Σ mind mdecl :=
      { onInductives : Alli (on_ind_body Σ mind mdecl) 0 mdecl.(ind_bodies);

        onParams : on_context Σ mdecl.(ind_params);
        onNpars : context_assumptions mdecl.(ind_params) = mdecl.(ind_npars);
        onVariance : on_variance mdecl.(ind_universes) mdecl.(ind_variance);
      }.

    Definition on_constant_decl Σ d :=
      match d.(cst_body) with
      | Some trm => P Σ [] trm (Some d.(cst_type))
      | None => on_type Σ [] d.(cst_type)
      end.

    Definition on_global_decl Σ kn decl :=
      match decl with
      | ConstantDecl d => on_constant_decl Σ d
      | InductiveDecl inds => on_inductive Σ kn inds
      end.

    Definition fresh_global (s : kername) : global_env -> Prop :=
      Forall (fun g => g.1 <> s).

    Definition satisfiable_udecl `{checker_flags} Σ φ
      := consistent (global_ext_constraints (Σ, φ)).

    Definition on_udecl `{checker_flags} Σ (udecl : universes_decl)
      := let levels := levels_of_udecl udecl in
        let global_levels := global_levels Σ in
        let all_levels := LevelSet.union levels global_levels in
        LevelSet.For_all (fun l => ~ LevelSet.In l global_levels) levels
        /\ ConstraintSet.For_all (fun '(l1,_,l2) => LevelSet.In l1 all_levels
                                                /\ LevelSet.In l2 all_levels)
                                (constraints_of_udecl udecl)
        /\ match udecl with
          | Monomorphic_ctx ctx =>  LevelSet.for_all (negb ∘ Level.is_var) ctx.1
          | _ => True
          end
        /\ satisfiable_udecl Σ udecl.

    Inductive on_global_env `{checker_flags} : global_env -> Type :=
    | globenv_nil : on_global_env []
    | globenv_decl Σ kn d :
        on_global_env Σ ->
        fresh_global kn Σ ->
        let udecl := universes_decl_of_decl d in
        on_udecl Σ udecl ->
        on_global_decl (Σ, udecl) kn d ->
        on_global_env (Σ ,, (kn, d)).

  End GlobalMaps.

  Definition Forall_decls_typing `{checker_flags}
            (P : global_env_ext -> context -> term -> term -> Type)
    := on_global_env (lift_typing P).

  End DeclarationTyping.

Variant prim_tag :=
  | primInt
  | primFloat.

Inductive prim_model (term : Type) : prim_tag -> Type :=
| primIntModel (i : uint63_model) : prim_model term primInt
| primFloatModel (f : float64_model) : prim_model term primFloat.

Definition prim_val term := ∑ t : prim_tag, prim_model term t.

Inductive term :=
| tRel (n : nat)
| tVar (i : ident)
| tEvar (n : nat) (l : list term)
| tSort (u : Universe.t)
| tProd (na : aname) (A B : term)
| tLambda (na : aname) (A t : term)
| tLetIn (na : aname) (b B t : term)
| tApp (u v : term)
| tConst (k : kername) (ui : Instance.t)
| tInd (ind : inductive) (ui : Instance.t)
| tConstruct (ind : inductive) (n : nat) (ui : Instance.t)
| tCase (indn : inductive * nat) (p c : term) (brs : list (nat * term))
| tProj (p : projection) (c : term)
| tFix (mfix : mfixpoint term) (idx : nat)
| tCoFix (mfix : mfixpoint term) (idx : nat)

| tPrim (prim : prim_val term).

Fixpoint mkApps t us :=
  match us with
  | nil => t
  | u :: us => mkApps (tApp t u) us
  end.

Module PCUICTerm <: Term.

  Definition term := term.

  Definition tRel := tRel.
  Definition tSort := tSort.
  Definition tProd := tProd.
  Definition tLetIn := tLetIn.
  Definition tProj := tProj.
  Definition mkApps := mkApps.

End PCUICTerm.

Module PCUICEnvironment := Environment PCUICTerm.
Include PCUICEnvironment.

Module PCUICLookup := Lookup PCUICTerm PCUICEnvironment.
Include PCUICLookup.

Fixpoint decompose_app_rec (t : term) l :=
  match t with
  | tApp f a => decompose_app_rec f (a :: l)
  | _ => (t, l)
  end.

Definition decompose_app t := decompose_app_rec t [].

Definition isConstruct_app t :=
  match fst (decompose_app t) with
  | tConstruct _ _ _ => true
  | _ => false
  end.

Fixpoint decompose_prod_assum (Γ : context) (t : term) : context * term :=
  match t with
  | tProd n A B => decompose_prod_assum (Γ ,, vass n A) B
  | tLetIn na b bty b' => decompose_prod_assum (Γ ,, vdef na b bty) b'
  | _ => (Γ, t)
  end.

Fixpoint destArity Γ (t : term) :=
  match t with
  | tProd na t b => destArity (Γ ,, vass na t) b
  | tLetIn na b b_ty b' => destArity (Γ ,, vdef na b b_ty) b'
  | tSort s => Some (Γ, s)
  | _ => None
  end.

Fixpoint lift n k t : term :=
  match t with
  | tRel i => tRel (if Nat.leb k i then (n + i) else i)
  | tEvar ev args => tEvar ev (List.map (lift n k) args)
  | tLambda na T M => tLambda na (lift n k T) (lift n (S k) M)
  | tApp u v => tApp (lift n k u) (lift n k v)
  | tProd na A B => tProd na (lift n k A) (lift n (S k) B)
  | tLetIn na b t b' => tLetIn na (lift n k b) (lift n k t) (lift n (S k) b')
  | tCase ind p c brs =>
    let brs' := List.map (on_snd (lift n k)) brs in
    tCase ind (lift n k p) (lift n k c) brs'
  | tProj p c => tProj p (lift n k c)
  | tFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (lift n k) (lift n k')) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (lift n k) (lift n k')) mfix in
    tCoFix mfix' idx
  | x => x
  end.

Notation lift0 n := (lift n 0).

Definition lift_context n k (Γ : context) : context :=
  fold_context (fun k' => lift n (k' + k)) Γ.

Fixpoint subst s k u :=
  match u with
  | tRel n =>
    if Nat.leb k n then
      match nth_error s (n - k) with
      | Some b => lift0 k b
      | None => tRel (n - List.length s)
      end
    else tRel n
  | tEvar ev args => tEvar ev (List.map (subst s k) args)
  | tLambda na T M => tLambda na (subst s k T) (subst s (S k) M)
  | tApp u v => tApp (subst s k u) (subst s k v)
  | tProd na A B => tProd na (subst s k A) (subst s (S k) B)
  | tLetIn na b ty b' => tLetIn na (subst s k b) (subst s k ty) (subst s (S k) b')
  | tCase ind p c brs =>
    let brs' := List.map (on_snd (subst s k)) brs in
    tCase ind (subst s k p) (subst s k c) brs'
  | tProj p c => tProj p (subst s k c)
  | tFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (subst s k) (subst s k')) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (subst s k) (subst s k')) mfix in
    tCoFix mfix' idx
  | x => x
  end.

Notation subst0 t := (subst t 0).
Definition subst1 t k u := subst [t] k u.
Notation subst10 t := (subst1 t 0).
Notation "M { j := N }" := (subst1 N j M) (at level 10, right associativity).

Definition subst_telescope s k Γ :=
  mapi (fun k' x => map_decl (subst s (k + k')) x) Γ.

Definition subst_context s k (Γ : context) : context :=
  fold_context (fun k' => subst s (k' + k)) Γ.

Fixpoint smash_context (Γ Γ' : context) : context :=
  match Γ' with
  | {| decl_body := Some b |} :: Γ' => smash_context (subst_context [b] 0 Γ) Γ'
  | {| decl_body := None |} as d :: Γ' => smash_context (Γ ++ [d]) Γ'
  | [] => Γ
  end.

Fixpoint extended_subst (Γ : context) (n : nat)
    :=
  match Γ with
  | nil => nil
  | cons d vs =>
    match decl_body d with
    | Some b =>

      let s := extended_subst vs n in

      let b' := lift (context_assumptions vs + n) #|s| b in

      let b' := subst0 s b' in

      b' :: s
    | None => tRel n :: extended_subst vs (S n)
    end
  end.

Definition expand_lets_k Γ k t :=
  (subst (extended_subst Γ 0) k (lift (context_assumptions Γ) (k + #|Γ|) t)).

Definition expand_lets Γ t := expand_lets_k Γ 0 t.

Definition expand_lets_k_ctx Γ k Δ :=
  (subst_context (extended_subst Γ 0) k (lift_context (context_assumptions Γ) (k + #|Γ|) Δ)).

Definition expand_lets_ctx Γ Δ := expand_lets_k_ctx Γ 0 Δ.

Fixpoint closedn k (t : term) : bool :=
  match t with
  | tRel i => Nat.ltb i k
  | tEvar ev args => List.forallb (closedn k) args
  | tLambda _ T M | tProd _ T M => closedn k T && closedn (S k) M
  | tApp u v => closedn k u && closedn k v
  | tLetIn na b t b' => closedn k b && closedn k t && closedn (S k) b'
  | tCase ind p c brs =>
    let brs' := List.forallb (test_snd (closedn k)) brs in
    closedn k p && closedn k c && brs'
  | tProj p c => closedn k c
  | tFix mfix idx =>
    let k' := List.length mfix + k in
    List.forallb (test_def (closedn k) (closedn k')) mfix
  | tCoFix mfix idx =>
    let k' := List.length mfix + k in
    List.forallb (test_def (closedn k) (closedn k')) mfix
  | _ => true
  end.

Definition fix_context (m : mfixpoint term) : context :=
  List.rev (mapi (fun i d => vass d.(dname) (lift0 i d.(dtype))) m).

Definition R_universe_instance R :=
  fun u u' => Forall2 R (List.map Universe.make u) (List.map Universe.make u').

Definition R_universe_variance (Re Rle : Universe.t -> Universe.t -> Prop) v u u' :=
  match v with
  | Variance.Irrelevant => True
  | Variance.Covariant => Rle (Universe.make u) (Universe.make u')
  | Variance.Invariant => Re (Universe.make u) (Universe.make u')
  end.

Fixpoint R_universe_instance_variance Re Rle v u u' :=
  match u, u' return Prop with
  | u :: us, u' :: us' =>
    match v with
    | [] => R_universe_instance_variance Re Rle v us us'

    | v :: vs => R_universe_variance Re Rle v u u' /\
        R_universe_instance_variance Re Rle vs us us'
    end
  | [], [] => True
  | _, _ => False
  end.

Definition lookup_minductive Σ mind :=
  match lookup_env Σ mind with
  | Some (InductiveDecl decl) => Some decl
  | _ => None
  end.

Definition lookup_inductive Σ ind :=
  match lookup_minductive Σ (inductive_mind ind) with
  | Some mdecl =>
    match nth_error mdecl.(ind_bodies) (inductive_ind ind) with
    | Some idecl => Some (mdecl, idecl)
    | None => None
    end
  | None => None
  end.

Definition lookup_constructor Σ ind k :=
  match lookup_inductive Σ ind with
  | Some (mdecl, idecl) =>
    match nth_error idecl.(ind_ctors) k with
    | Some cdecl => Some (mdecl, idecl, cdecl)
    | None => None
    end
  | _ => None
  end.

Definition global_variance Σ gr napp :=
  match gr with
  | IndRef ind =>
    match lookup_inductive Σ ind with
    | Some (mdecl, idecl) =>
      match destArity [] idecl.(ind_type) with
      | Some (ctx, _) => if (context_assumptions ctx) <=? napp then mdecl.(ind_variance)
        else None
      | None => None
      end
    | None => None
    end
  | ConstructRef ind k =>
    match lookup_constructor Σ ind k with
    | Some (mdecl, idecl, cdecl) =>
      if (cdecl.2 + mdecl.(ind_npars))%nat <=? napp then

        Some []
      else None
    | _ => None
    end
  | _ => None
  end.

Definition R_opt_variance Re Rle v :=
  match v with
  | Some v => R_universe_instance_variance Re Rle v
  | None => R_universe_instance Re
  end.

Definition R_global_instance Σ Re Rle gr napp :=
  R_opt_variance Re Rle (global_variance Σ gr napp).

Inductive eq_term_upto_univ_napp Σ (Re Rle : Universe.t -> Universe.t -> Prop) (napp : nat) : term -> term -> Type :=
| eq_Rel n  :
    eq_term_upto_univ_napp Σ Re Rle napp (tRel n) (tRel n)

| eq_Evar e args args' :
    All2 (eq_term_upto_univ_napp Σ Re Re 0) args args' ->
    eq_term_upto_univ_napp Σ Re Rle napp (tEvar e args) (tEvar e args')

| eq_Var id :
    eq_term_upto_univ_napp Σ Re Rle napp (tVar id) (tVar id)

| eq_Sort s s' :
    Rle s s' ->
    eq_term_upto_univ_napp Σ Re Rle napp (tSort s) (tSort s')

| eq_App t t' u u' :
    eq_term_upto_univ_napp Σ Re Rle (S napp) t t' ->
    eq_term_upto_univ_napp Σ Re Re 0 u u' ->
    eq_term_upto_univ_napp Σ Re Rle napp (tApp t u) (tApp t' u')

| eq_Const c u u' :
    R_universe_instance Re u u' ->
    eq_term_upto_univ_napp Σ Re Rle napp (tConst c u) (tConst c u')

| eq_Ind i u u' :
    R_global_instance Σ Re Rle (IndRef i) napp u u' ->
    eq_term_upto_univ_napp Σ Re Rle napp (tInd i u) (tInd i u')

| eq_Construct i k u u' :
    R_global_instance Σ Re Rle (ConstructRef i k) napp u u' ->
    eq_term_upto_univ_napp Σ Re Rle napp (tConstruct i k u) (tConstruct i k u')

| eq_Lambda na na' ty ty' t t' :
    eq_binder_annot na na' ->
    eq_term_upto_univ_napp Σ Re Re 0 ty ty' ->
    eq_term_upto_univ_napp Σ Re Rle 0 t t' ->
    eq_term_upto_univ_napp Σ Re Rle napp (tLambda na ty t) (tLambda na' ty' t')

| eq_Prod na na' a a' b b' :
    eq_binder_annot na na' ->
    eq_term_upto_univ_napp Σ Re Re 0 a a' ->
    eq_term_upto_univ_napp Σ Re Rle 0 b b' ->
    eq_term_upto_univ_napp Σ Re Rle napp (tProd na a b) (tProd na' a' b')

| eq_LetIn na na' t t' ty ty' u u' :
    eq_binder_annot na na' ->
    eq_term_upto_univ_napp Σ Re Re 0 t t' ->
    eq_term_upto_univ_napp Σ Re Re 0 ty ty' ->
    eq_term_upto_univ_napp Σ Re Rle 0 u u' ->
    eq_term_upto_univ_napp Σ Re Rle napp (tLetIn na t ty u) (tLetIn na' t' ty' u')

| eq_Case indn p p' c c' brs brs' :
    eq_term_upto_univ_napp Σ Re Re 0 p p' ->
    eq_term_upto_univ_napp Σ Re Re 0 c c' ->
    All2 (fun x y =>
      (fst x = fst y) *
      eq_term_upto_univ_napp Σ Re Re 0 (snd x) (snd y)
    ) brs brs' ->
    eq_term_upto_univ_napp Σ Re Rle napp (tCase indn p c brs) (tCase indn p' c' brs')

| eq_Proj p c c' :
    eq_term_upto_univ_napp Σ Re Re 0 c c' ->
    eq_term_upto_univ_napp Σ Re Rle napp (tProj p c) (tProj p c')

| eq_Fix mfix mfix' idx :
    All2 (fun x y =>
      eq_term_upto_univ_napp Σ Re Re 0 x.(dtype) y.(dtype) *
      eq_term_upto_univ_napp Σ Re Re 0 x.(dbody) y.(dbody) *
      (x.(rarg) = y.(rarg)) *
      eq_binder_annot x.(dname) y.(dname)
    )%type mfix mfix' ->
    eq_term_upto_univ_napp Σ Re Rle napp (tFix mfix idx) (tFix mfix' idx)

| eq_CoFix mfix mfix' idx :
    All2 (fun x y =>
      eq_term_upto_univ_napp Σ Re Re 0 x.(dtype) y.(dtype) *
      eq_term_upto_univ_napp Σ Re Re 0 x.(dbody) y.(dbody) *
      (x.(rarg) = y.(rarg)) *
      eq_binder_annot x.(dname) y.(dname)
    ) mfix mfix' ->
    eq_term_upto_univ_napp Σ Re Rle napp (tCoFix mfix idx) (tCoFix mfix' idx)

| eq_Prim i : eq_term_upto_univ_napp Σ Re Rle napp (tPrim i) (tPrim i).

Notation eq_term_upto_univ Σ Re Rle := (eq_term_upto_univ_napp Σ Re Rle 0).

Definition eq_term `{checker_flags} Σ φ :=
  eq_term_upto_univ Σ (eq_universe φ) (eq_universe φ).

Definition leq_term `{checker_flags} Σ φ :=
  eq_term_upto_univ Σ (eq_universe φ) (leq_universe φ).

Definition upto_names := eq_term_upto_univ [] eq eq.

Instance subst_instance_constr : UnivSubst term :=
  fix subst_instance_constr u c {struct c} : term :=
  match c with
  | tRel _ | tVar _ => c
  | tEvar ev args => tEvar ev (List.map (subst_instance_constr u) args)
  | tSort s => tSort (subst_instance_univ u s)
  | tConst c u' => tConst c (subst_instance_instance u u')
  | tInd i u' => tInd i (subst_instance_instance u u')
  | tConstruct ind k u' => tConstruct ind k (subst_instance_instance u u')
  | tLambda na T M => tLambda na (subst_instance_constr u T) (subst_instance_constr u M)
  | tApp f v => tApp (subst_instance_constr u f) (subst_instance_constr u v)
  | tProd na A B => tProd na (subst_instance_constr u A) (subst_instance_constr u B)
  | tLetIn na b ty b' => tLetIn na (subst_instance_constr u b) (subst_instance_constr u ty)
                                (subst_instance_constr u b')
  | tCase ind p c brs =>
    let brs' := List.map (on_snd (subst_instance_constr u)) brs in
    tCase ind (subst_instance_constr u p) (subst_instance_constr u c) brs'
  | tProj p c => tProj p (subst_instance_constr u c)
  | tFix mfix idx =>
    let mfix' := List.map (map_def (subst_instance_constr u) (subst_instance_constr u)) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let mfix' := List.map (map_def (subst_instance_constr u) (subst_instance_constr u)) mfix in
    tCoFix mfix' idx
  | tPrim _ => c
  end.

Instance subst_instance_context : UnivSubst context
  := map_context ∘ subst_instance_constr.
Import Equations.Type.Relation.

Definition tDummy := tVar String.EmptyString.

Definition iota_red npar c args brs :=
  (mkApps (snd (List.nth c brs (0, tDummy))) (List.skipn npar args)).

Definition fix_subst (l : mfixpoint term) :=
  let fix aux n :=
      match n with
      | 0 => []
      | S n => tFix l n :: aux n
      end
  in aux (List.length l).

Definition unfold_fix (mfix : mfixpoint term) (idx : nat) :=
  match List.nth_error mfix idx with
  | Some d => Some (d.(rarg), subst0 (fix_subst mfix) d.(dbody))
  | None => None
  end.

Definition cofix_subst (l : mfixpoint term) :=
  let fix aux n :=
      match n with
      | 0 => []
      | S n => tCoFix l n :: aux n
      end
  in aux (List.length l).

Definition unfold_cofix (mfix : mfixpoint term) (idx : nat) :=
  match List.nth_error mfix idx with
  | Some d => Some (d.(rarg), subst0 (cofix_subst mfix) d.(dbody))
  | None => None
  end.

Definition is_constructor n ts :=
  match List.nth_error ts n with
  | Some a => isConstruct_app a
  | None => false
  end.

Inductive red1 (Σ : global_env) (Γ : context) : term -> term -> Type :=

| red_beta na t b a :
    red1 Σ Γ (tApp (tLambda na t b) a) (subst10 a b)

| red_zeta na b t b' :
    red1 Σ Γ (tLetIn na b t b') (subst10 b b')

| red_rel i body :
    option_map decl_body (nth_error Γ i) = Some (Some body) ->
    red1 Σ Γ (tRel i) (lift0 (S i) body)

| red_iota ind pars c u args p brs :
    red1 Σ Γ (tCase (ind, pars) p (mkApps (tConstruct ind c u) args) brs)
         (iota_red pars c args brs)

| red_fix mfix idx args narg fn :
    unfold_fix mfix idx = Some (narg, fn) ->
    is_constructor narg args = true ->
    red1 Σ Γ (mkApps (tFix mfix idx) args) (mkApps fn args)

| red_cofix_case ip p mfix idx args narg fn brs :
    unfold_cofix mfix idx = Some (narg, fn) ->
    red1 Σ Γ (tCase ip p (mkApps (tCoFix mfix idx) args) brs)
         (tCase ip p (mkApps fn args) brs)

| red_cofix_proj p mfix idx args narg fn :
    unfold_cofix mfix idx = Some (narg, fn) ->
    red1 Σ Γ (tProj p (mkApps (tCoFix mfix idx) args))
         (tProj p (mkApps fn args))

| red_delta c decl body (isdecl : declared_constant Σ c decl) u :
    decl.(cst_body) = Some body ->
    red1 Σ Γ (tConst c u) (subst_instance_constr u body)

| red_proj i pars narg args u arg:
    nth_error args (pars + narg) = Some arg ->
    red1 Σ Γ (tProj (i, pars, narg) (mkApps (tConstruct i 0 u) args)) arg

| abs_red_l na M M' N : red1 Σ Γ M M' -> red1 Σ Γ (tLambda na M N) (tLambda na M' N)
| abs_red_r na M M' N : red1 Σ (Γ ,, vass na N) M M' -> red1 Σ Γ (tLambda na N M) (tLambda na N M')

| letin_red_def na b t b' r : red1 Σ Γ b r -> red1 Σ Γ (tLetIn na b t b') (tLetIn na r t b')
| letin_red_ty na b t b' r : red1 Σ Γ t r -> red1 Σ Γ (tLetIn na b t b') (tLetIn na b r b')
| letin_red_body na b t b' r : red1 Σ (Γ ,, vdef na b t) b' r -> red1 Σ Γ (tLetIn na b t b') (tLetIn na b t r)

| case_red_pred ind p p' c brs : red1 Σ Γ p p' -> red1 Σ Γ (tCase ind p c brs) (tCase ind p' c brs)
| case_red_discr ind p c c' brs : red1 Σ Γ c c' -> red1 Σ Γ (tCase ind p c brs) (tCase ind p c' brs)
| case_red_brs ind p c brs brs' :
    OnOne2 (on_Trel_eq (red1 Σ Γ) snd fst) brs brs' ->
    red1 Σ Γ (tCase ind p c brs) (tCase ind p c brs')

| proj_red p c c' : red1 Σ Γ c c' -> red1 Σ Γ (tProj p c) (tProj p c')

| app_red_l M1 N1 M2 : red1 Σ Γ M1 N1 -> red1 Σ Γ (tApp M1 M2) (tApp N1 M2)
| app_red_r M2 N2 M1 : red1 Σ Γ M2 N2 -> red1 Σ Γ (tApp M1 M2) (tApp M1 N2)

| prod_red_l na M1 M2 N1 : red1 Σ Γ M1 N1 -> red1 Σ Γ (tProd na M1 M2) (tProd na N1 M2)
| prod_red_r na M2 N2 M1 : red1 Σ (Γ ,, vass na M1) M2 N2 ->
                               red1 Σ Γ (tProd na M1 M2) (tProd na M1 N2)

| evar_red ev l l' : OnOne2 (red1 Σ Γ) l l' -> red1 Σ Γ (tEvar ev l) (tEvar ev l')

| fix_red_ty mfix0 mfix1 idx :
    OnOne2 (on_Trel_eq (red1 Σ Γ) dtype (fun x => (dname x, dbody x, rarg x))) mfix0 mfix1 ->
    red1 Σ Γ (tFix mfix0 idx) (tFix mfix1 idx)

| fix_red_body mfix0 mfix1 idx :
    OnOne2 (on_Trel_eq (red1 Σ (Γ ,,, fix_context mfix0)) dbody (fun x => (dname x, dtype x, rarg x)))
           mfix0 mfix1 ->
    red1 Σ Γ (tFix mfix0 idx) (tFix mfix1 idx)

| cofix_red_ty mfix0 mfix1 idx :
    OnOne2 (on_Trel_eq (red1 Σ Γ) dtype (fun x => (dname x, dbody x, rarg x))) mfix0 mfix1 ->
    red1 Σ Γ (tCoFix mfix0 idx) (tCoFix mfix1 idx)

| cofix_red_body mfix0 mfix1 idx :
    OnOne2 (on_Trel_eq (red1 Σ (Γ ,,, fix_context mfix0)) dbody (fun x => (dname x, dtype x, rarg x))) mfix0 mfix1 ->
    red1 Σ Γ (tCoFix mfix0 idx) (tCoFix mfix1 idx).

Definition red Σ Γ := clos_refl_trans (red1 Σ Γ).

Lemma refl_red Σ Γ t : red Σ Γ t t.
admit.
Defined.

Lemma red1_red Σ Γ t u : red1 Σ Γ t u -> red Σ Γ t u.
admit.
Defined.

#[global]
Hint Resolve red1_red refl_red : core pcuic.

Reserved Notation " Σ ;;; Γ |- t : T " (at level 50, Γ, t, T at next level).
Reserved Notation " Σ ;;; Γ |- t <= u " (at level 50, Γ, t, u at next level).
Reserved Notation " Σ ;;; Γ |- t = u " (at level 50, Γ, t, u at next level).

Inductive cumul `{checker_flags} (Σ : global_env_ext) (Γ : context) : term -> term -> Type :=
| cumul_refl t u : leq_term Σ.1 (global_ext_constraints Σ) t u -> Σ ;;; Γ |- t <= u
| cumul_red_l t u v : red1 Σ.1 Γ t v -> Σ ;;; Γ |- v <= u -> Σ ;;; Γ |- t <= u
| cumul_red_r t u v : Σ ;;; Γ |- t <= v -> red1 Σ.1 Γ u v -> Σ ;;; Γ |- t <= u

where " Σ ;;; Γ |- t <= u " := (cumul Σ Γ t u) : type_scope.

Inductive conv `{checker_flags} (Σ : global_env_ext) (Γ : context) : term -> term -> Type :=
| conv_refl t u : eq_term Σ.1 (global_ext_constraints Σ) t u -> Σ ;;; Γ |- t = u
| conv_red_l t u v : red1 Σ Γ t v -> Σ ;;; Γ |- v = u -> Σ ;;; Γ |- t = u
| conv_red_r t u v : Σ ;;; Γ |- t = v -> red1 (fst Σ) Γ u v -> Σ ;;; Γ |- t = u

where " Σ ;;; Γ |- t = u " := (@conv _ Σ Γ t u) : type_scope.
Module Export PCUICTyping.

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

Definition inds ind u (l : list one_inductive_body) :=
  let fix aux n :=
      match n with
      | 0 => []
      | S n => tInd (mkInd ind n) u :: aux n
      end
  in aux (List.length l).

Definition type_of_constructor mdecl (cdecl : ident * term * nat) (c : inductive * nat) (u : list Level.t) :=
  let mind := inductive_mind (fst c) in
  subst0 (inds mind u mdecl.(ind_bodies)) (subst_instance_constr u (snd (fst cdecl))).

Definition extends (Σ Σ' : global_env) :=
  { Σ'' & Σ' = Σ'' ++ Σ }.

Module PCUICEnvTyping := EnvTyping PCUICTerm PCUICEnvironment.
Include PCUICEnvTyping.

Class GuardChecker :=
{
  fix_guard : global_env_ext -> context -> mfixpoint term -> bool ;

  cofix_guard : global_env_ext -> context -> mfixpoint term -> bool ;

  fix_guard_red1 Σ Γ mfix mfix' idx :
      fix_guard Σ Γ mfix ->
      red1 Σ Γ (tFix mfix idx) (tFix mfix' idx) ->
      fix_guard Σ Γ mfix' ;

  fix_guard_eq_term Σ Γ  mfix mfix' idx :
      fix_guard Σ Γ mfix ->
      upto_names (tFix mfix idx) (tFix mfix' idx) ->
      fix_guard Σ Γ mfix' ;

  fix_guard_lift Σ Γ Γ' Γ'' mfix :
    let k' := (#|mfix| + #|Γ'|)%nat in
    let mfix' := map (map_def (lift #|Γ''| #|Γ'|) (lift #|Γ''| k')) mfix in
    fix_guard Σ (Γ ,,, Γ') mfix ->
    fix_guard Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') mfix' ;

  fix_guard_subst Σ Γ Γ' Δ mfix s k :
    let k' := (#|mfix| + k)%nat in
    let mfix' := map (map_def (subst s k) (subst s k')) mfix in
    fix_guard Σ (Γ ,,, Γ' ,,, Δ) mfix ->
    fix_guard Σ (Γ ,,, subst_context s 0 Δ) mfix' ;

  fix_guard_subst_instance {cf:checker_flags} Σ Γ mfix u univs :
    consistent_instance_ext (Σ.1, univs) Σ.2 u ->
    fix_guard Σ Γ mfix ->
    fix_guard (Σ.1, univs) (subst_instance_context u Γ) (map (map_def (subst_instance_constr u) (subst_instance_constr u))
                    mfix) ;

  fix_guard_extends Σ Γ mfix Σ' :
    fix_guard Σ Γ mfix ->
    extends Σ.1 Σ' ->
    fix_guard Σ' Γ mfix ;

  cofix_guard_red1 Σ Γ mfix mfix' idx :
    cofix_guard Σ Γ mfix ->
    red1 Σ Γ (tCoFix mfix idx) (tCoFix mfix' idx) ->
    cofix_guard Σ Γ mfix' ;

  cofix_guard_eq_term Σ Γ mfix mfix' idx :
    cofix_guard Σ Γ mfix ->
    upto_names (tCoFix mfix idx) (tCoFix mfix' idx) ->
    cofix_guard Σ Γ mfix' ;

  cofix_guard_lift Σ Γ Γ' Γ'' mfix :
    let k' := (#|mfix| + #|Γ'|)%nat in
    let mfix' := map (map_def (lift #|Γ''| #|Γ'|) (lift #|Γ''| k')) mfix in
    cofix_guard Σ (Γ ,,, Γ') mfix ->
    cofix_guard Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') mfix' ;

  cofix_guard_subst Σ Γ Γ' Δ mfix s k :
    let k' := (#|mfix| + k)%nat in
    let mfix' := map (map_def (subst s k) (subst s k')) mfix in
    cofix_guard Σ (Γ ,,, Γ' ,,, Δ) mfix ->
    cofix_guard Σ (Γ ,,, subst_context s 0 Δ) mfix' ;

  cofix_guard_subst_instance {cf:checker_flags} Σ Γ mfix u univs :
    consistent_instance_ext (Σ.1, univs) Σ.2 u ->
    cofix_guard Σ Γ mfix ->
    cofix_guard (Σ.1, univs) (subst_instance_context u Γ) (map (map_def (subst_instance_constr u) (subst_instance_constr u))
                    mfix) ;

  cofix_guard_extends Σ Γ mfix Σ' :
    cofix_guard Σ Γ mfix ->
    extends Σ.1 Σ' ->
    cofix_guard Σ' Γ mfix }.

Axiom guard_checking : GuardChecker.
Existing Instance guard_checking.

Fixpoint instantiate_params_subst params pars s ty :=
  match params with
  | [] => match pars with
          | [] => Some (s, ty)
          | _ :: _ => None
          end
  | d :: params =>
    match d.(decl_body), ty with
    | None, tProd _ _ B =>
      match pars with
      | hd :: tl => instantiate_params_subst params tl (hd :: s) B
      | [] => None
      end
    | Some b, tLetIn _ _ _ b' => instantiate_params_subst params pars (subst0 s b :: s) b'
    | _, _ => None
    end
  end.

Definition instantiate_params (params : context) (pars : list term) (ty : term) : option term :=
  match instantiate_params_subst (List.rev params) pars [] ty with
  | Some (s, ty) => Some (subst0 s ty)
  | None => None
  end.

Definition build_branches_type ind mdecl idecl params u p : list (option (nat × term)) :=
  let inds := inds ind.(inductive_mind) u mdecl.(ind_bodies) in
  let branch_type i '(id, t, ar) :=
    let ty := subst0 inds (subst_instance_constr u t) in
    match instantiate_params (subst_instance_context u mdecl.(ind_params)) params ty with
    | Some ty =>
      let '(sign, ccl) := decompose_prod_assum [] ty in
      let nargs := List.length sign in
      let allargs := snd (decompose_app ccl) in
      let '(paramrels, args) := chop mdecl.(ind_npars) allargs in
      let cstr := tConstruct ind i u in
      let args := (args ++ [mkApps cstr (paramrels ++ to_extended_list sign)]) in
      Some (ar, it_mkProd_or_LetIn sign (mkApps (lift0 nargs p) args))
    | None => None
    end
  in mapi branch_type idecl.(ind_ctors).

Definition build_case_predicate_type ind mdecl idecl params u ps : option term :=
  X <- instantiate_params (subst_instance_context u (ind_params mdecl)) params
                         (subst_instance_constr u (ind_type idecl)) ;;
  X <- destArity [] X ;;
  let inddecl :=
      {| decl_name := mkBindAnn (nNamed idecl.(ind_name)) idecl.(ind_relevance);
         decl_body := None;
         decl_type := mkApps (tInd ind u) (map (lift0 #|X.1|) params ++ to_extended_list X.1) |} in
  ret (it_mkProd_or_LetIn (X.1 ,, inddecl) (tSort ps)).

Definition destInd (t : term) :=
  match t with
  | tInd ind u => Some (ind, u)
  | _ => None
  end.

Definition isCoFinite (r : recursivity_kind) :=
  match r with
  | CoFinite => true
  | _ => false
  end.

Definition check_recursivity_kind (Σ : global_env) ind r :=
  match lookup_env Σ ind with
  | Some (InductiveDecl mib) => Reflect.eqb mib.(ind_finite) r
  | _ => false
  end.

Definition check_one_fix d :=
  let '{| dname := na;
         dtype := ty;
         dbody := b;
         rarg := arg |} := d in
  let '(ctx, ty) := decompose_prod_assum [] ty in
  match nth_error (List.rev (smash_context [] ctx)) arg with
  | Some argd =>
    let (hd, args) := decompose_app argd.(decl_type) in
    match destInd hd with
    | Some (mkInd mind _, u) => Some mind
    | None => None
    end
  | None => None
  end.

Definition wf_fixpoint (Σ : global_env) mfix :=
  let checks := map check_one_fix mfix in
  match map_option_out checks with
  | Some (ind :: inds) =>

    forallb (Reflect.eqb ind) inds &&
    check_recursivity_kind Σ ind Finite
  | _ => false
  end.

Definition check_one_cofix d :=
  let '{| dname := na;
         dtype := ty;
         dbody := b;
         rarg := arg |} := d in
  let '(ctx, ty) := decompose_prod_assum [] ty in
  let (hd, args) := decompose_app ty in
  match destInd hd with
  | Some (mkInd ind _, u) => Some ind
  | None => None
  end.

Definition wf_cofixpoint (Σ : global_env) mfix :=
  let checks := map check_one_cofix mfix in
  match map_option_out checks with
  | Some (ind :: inds) =>

    forallb (Reflect.eqb ind) inds &&
    check_recursivity_kind Σ ind CoFinite
  | _ => false
  end.

Definition wf_universe Σ s :=
  match s with
  | Universe.lProp
  | Universe.lSProp => True
  | Universe.lType u =>
    forall l, UnivExprSet.In l u -> LevelSet.In (UnivExpr.get_level l) (global_ext_levels Σ)
  end.

Reserved Notation "'wf_local' Σ Γ " (at level 9, Σ, Γ at next level).

Inductive typing `{checker_flags} (Σ : global_env_ext) (Γ : context) : term -> term -> Type :=
| type_Rel n decl :
    wf_local Σ Γ ->
    nth_error Γ n = Some decl ->
    Σ ;;; Γ |- tRel n : lift0 (S n) decl.(decl_type)

| type_Sort s :
    wf_local Σ Γ ->
    wf_universe Σ s ->
    Σ ;;; Γ |- tSort s : tSort (Universe.super s)

| type_Prod na A B s1 s2 :
    Σ ;;; Γ |- A : tSort s1 ->
    Σ ;;; Γ ,, vass na A |- B : tSort s2 ->
    Σ ;;; Γ |- tProd na A B : tSort (Universe.sort_of_product s1 s2)

| type_Lambda na A t s1 B :
    Σ ;;; Γ |- A : tSort s1 ->
    Σ ;;; Γ ,, vass na A |- t : B ->
    Σ ;;; Γ |- tLambda na A t : tProd na A B

| type_LetIn na b B t s1 A :
    Σ ;;; Γ |- B : tSort s1 ->
    Σ ;;; Γ |- b : B ->
    Σ ;;; Γ ,, vdef na b B |- t : A ->
    Σ ;;; Γ |- tLetIn na b B t : tLetIn na b B A

| type_App t na A B s u :

    Σ ;;; Γ |- tProd na A B : tSort s ->
    Σ ;;; Γ |- t : tProd na A B ->
    Σ ;;; Γ |- u : A ->
    Σ ;;; Γ |- tApp t u : B{0 := u}

| type_Const cst u :
    wf_local Σ Γ ->
    forall decl,
    declared_constant Σ.1 cst decl ->
    consistent_instance_ext Σ decl.(cst_universes) u ->
    Σ ;;; Γ |- (tConst cst u) : subst_instance_constr u decl.(cst_type)

| type_Ind ind u :
    wf_local Σ Γ ->
    forall mdecl idecl,
    declared_inductive Σ.1 mdecl ind idecl ->
    consistent_instance_ext Σ mdecl.(ind_universes) u ->
    Σ ;;; Γ |- (tInd ind u) : subst_instance_constr u idecl.(ind_type)

| type_Construct ind i u :
    wf_local Σ Γ ->
    forall mdecl idecl cdecl,
    declared_constructor Σ.1 mdecl idecl (ind, i) cdecl ->
    consistent_instance_ext Σ mdecl.(ind_universes) u ->
    Σ ;;; Γ |- (tConstruct ind i u) : type_of_constructor mdecl cdecl (ind, i) u

| type_Case indnpar u p c brs args :
    let ind := indnpar.1 in
    let npar := indnpar.2 in
    forall mdecl idecl,
    declared_inductive Σ.1 mdecl ind idecl ->
    mdecl.(ind_npars) = npar ->
    let params := List.firstn npar args in
    forall ps pty, build_case_predicate_type ind mdecl idecl params u ps = Some pty ->
    Σ ;;; Γ |- p : pty ->
    is_allowed_elimination Σ ps idecl.(ind_kelim) ->
    Σ ;;; Γ |- c : mkApps (tInd ind u) args ->
    isCoFinite mdecl.(ind_finite) = false ->
    forall btys, map_option_out (build_branches_type ind mdecl idecl params u p) = Some btys ->
    All2 (fun br bty => (br.1 = bty.1) * (Σ ;;; Γ |- br.2 : bty.2) *

      (∑ s, Σ ;;; Γ |- bty.2 : tSort s)) brs btys ->
    Σ ;;; Γ |- tCase indnpar p c brs : mkApps p (skipn npar args ++ [c])

| type_Proj p c u :
    forall mdecl idecl pdecl,
    declared_projection Σ.1 mdecl idecl p pdecl ->
    forall args,
    Σ ;;; Γ |- c : mkApps (tInd (fst (fst p)) u) args ->
    #|args| = ind_npars mdecl ->
    let ty := snd pdecl in
    Σ ;;; Γ |- tProj p c : subst0 (c :: List.rev args) (subst_instance_constr u ty)

| type_Fix mfix n decl :
    fix_guard Σ Γ mfix ->
    nth_error mfix n = Some decl ->
    wf_local Σ Γ ->
    All (fun d => {s & Σ ;;; Γ |- d.(dtype) :  tSort s}) mfix ->
    All (fun d => (Σ ;;; Γ ,,, fix_context mfix |- d.(dbody) : lift0 #|fix_context mfix| d.(dtype))) mfix ->
    wf_fixpoint Σ.1 mfix ->
    Σ ;;; Γ |- tFix mfix n : decl.(dtype)

| type_CoFix mfix n decl :
    cofix_guard Σ Γ mfix ->
    nth_error mfix n = Some decl ->
    wf_local Σ Γ ->
    All (fun d => {s & Σ ;;; Γ |- d.(dtype) :  tSort s}) mfix ->
    All (fun d => Σ ;;; Γ ,,, fix_context mfix |- d.(dbody) : lift0 #|fix_context mfix| d.(dtype)) mfix ->
    wf_cofixpoint Σ.1 mfix ->
    Σ ;;; Γ |- tCoFix mfix n : decl.(dtype)

| type_Cumul t A B s :
    Σ ;;; Γ |- t : A ->
    Σ ;;; Γ |- B : tSort s ->
    Σ ;;; Γ |- A <= B -> Σ ;;; Γ |- t : B

where " Σ ;;; Γ |- t : T " := (typing Σ Γ t T)
and "'wf_local' Σ Γ " := (All_local_env (lift_typing typing Σ) Γ).

Module PCUICTypingDef <: Typing PCUICTerm PCUICEnvironment PCUICEnvTyping.
  Definition wf_universe := @wf_universe.
  Definition conv := @conv.
  Definition cumul := @cumul.
  Definition smash_context := smash_context.
  Definition expand_lets := expand_lets.
  Definition expand_lets_ctx := expand_lets_ctx.
  Definition lift_context := lift_context.
  Definition subst_telescope := subst_telescope.
  Definition subst_instance_context := subst_instance_context.
  Definition subst_instance_constr := subst_instance_constr.
  Definition subst := subst.
  Definition lift := lift.
  Definition inds := inds.
  Definition closedn := closedn.
  Definition destArity := destArity [].
End PCUICTypingDef.

Module PCUICDeclarationTyping :=
  DeclarationTyping
    PCUICTerm
    PCUICEnvironment
    PCUICEnvTyping
    PCUICTypingDef
    PCUICLookup.
Include PCUICDeclarationTyping.

Definition wf `{checker_flags} := Forall_decls_typing typing.

End PCUICTyping.

Section Lemmata.
  Context {cf : checker_flags}.

  Inductive cored Σ Γ: term -> term -> Prop :=
  | cored1 : forall u v, red1 Σ Γ u v -> cored Σ Γ v u
  | cored_trans : forall u v w, cored Σ Γ v u -> red1 Σ Γ v w -> cored Σ Γ w u.

  Context (Σ : global_env_ext).

  Inductive welltyped Σ Γ t : Prop :=
  | iswelltyped A : Σ ;;; Γ |- t : A -> welltyped Σ Γ t.

  Lemma cored_red_trans :
    forall Γ u v w,
      red Σ Γ u v ->
      red1 Σ Γ v w ->
      cored Σ Γ w u.
admit.
Defined.

  Lemma red_neq_cored :
    forall Γ u v,
      red Σ Γ u v ->
      u <> v ->
      cored Σ Γ v u.
admit.
Defined.

End Lemmata.

Section Normalisation.

  Context {cf : checker_flags}.
  Context (Σ : global_env_ext).

  Axiom normalisation :
    forall Γ t,
      welltyped Σ Γ t ->
      Acc (cored (fst Σ) Γ) t.

End Normalisation.
Import Coq.ssr.ssreflect.

Lemma Acc_no_loop X (R : X -> X -> Prop) t : Acc R t -> R t t -> False.
admit.
Defined.

Inductive term_direct_subterm : term -> term -> Type :=
| term_direct_subterm_4_1 : forall (na : aname) (A B : term),
  term_direct_subterm B (tProd na A B)
| term_direct_subterm_4_2 : forall (na : aname) (A B : term),
  term_direct_subterm A (tProd na A B)
| term_direct_subterm_5_1 : forall (na : aname) (A t : term),
  term_direct_subterm t (tLambda na A t)
| term_direct_subterm_5_2 : forall (na : aname) (A t : term),
  term_direct_subterm A (tLambda na A t)
| term_direct_subterm_6_1 : forall (na : aname) (b B t : term),
  term_direct_subterm t (tLetIn na b B t)
| term_direct_subterm_6_2 : forall (na : aname) (b B t : term),
  term_direct_subterm B (tLetIn na b B t)
| term_direct_subterm_6_3 : forall (na : aname) (b B t : term),
  term_direct_subterm b (tLetIn na b B t)
| term_direct_subterm_7_1 : forall u v : term,
  term_direct_subterm v (tApp u v)
| term_direct_subterm_7_2 : forall u v : term,
  term_direct_subterm u (tApp u v)
| term_direct_subterm_11_1 : forall (indn : inductive × nat)
     (p c : term) (brs : list (nat × term)),
   term_direct_subterm c (tCase indn p c brs)
| term_direct_subterm_11_2 : forall (indn : inductive × nat)
  (p c : term) (brs : list (nat × term)),
  term_direct_subterm p (tCase indn p c brs)
| term_direct_subterm_12_1 : forall (p : projection) (c : term),
  term_direct_subterm c (tProj p c).

Definition term_direct_subterm_context (t u : term) (p : term_direct_subterm t u) : context :=
  match p with
  | term_direct_subterm_4_1 na A B => [vass na A]
  | term_direct_subterm_5_1 na A t => [vass na A]
  | term_direct_subterm_6_1 na b B t => [vdef na b B]
  | _ => []
  end.
Definition term_subterm := Relation.trans_clos term_direct_subterm.

Fixpoint term_subterm_context {t u : term} (p : term_subterm t u) : context :=
  match p with
  | Relation.t_step y xy => term_direct_subterm_context _ _ xy
  | Relation.t_trans y z rxy ryz =>
    term_subterm_context rxy ++ term_subterm_context ryz
  end.

Definition term_subterm_wf : Equations.Type.WellFounded.well_founded term_subterm.
admit.
Defined.

Definition redp Σ Γ t u := Relation.trans_clos (red1 Σ Γ) t u.

Instance redp_trans Σ Γ : CRelationClasses.Transitive (redp Σ Γ).
admit.
Defined.

Lemma cored_redp Σ Γ t u : cored Σ Γ u t <-> ∥ redp Σ Γ t u ∥.
admit.
Defined.

Section fix_sigma.
  Context {cf : checker_flags}.
  Context {Σ : global_env_ext} {HΣ : ∥wf Σ∥}.

  Lemma term_subterm_red1 {Γ s s' t} {ts : term_subterm s t} :
    red1 Σ (Γ ,,, term_subterm_context ts) s s' ->
    exists t', ∥ red1 Σ Γ t t' × ∑ ts' : term_subterm s' t', term_subterm_context ts' = term_subterm_context ts ∥.
admit.
Defined.

  Lemma term_subterm_redp {Γ s s' t} {ts : term_subterm s t} :
    redp Σ (Γ ,,, term_subterm_context ts) s s' ->
    exists t', ∥ redp Σ Γ t t' × ∑ ts' : term_subterm s' t', term_subterm_context ts' = term_subterm_context ts ∥.
admit.
Defined.

  Definition hnf_subterm_rel : Relation_Definitions.relation (∑ Γ t, welltyped Σ Γ t) :=
    fun '(Γ2; t2; H) '(Γ1; t1; H2) =>
    ∥∑ t', red (fst Σ) Γ1 t1 t' × ∑ ts : term_subterm t2 t', Γ2 = (Γ1 ,,, term_subterm_context ts) ∥.

  Ltac sq' := try (destruct HΣ; clear HΣ);
    repeat match goal with
    | H : ∥ _ ∥ |- _ => destruct H; try clear H
    end; try eapply sq.

  Definition wf_hnf_subterm_rel : WellFounded hnf_subterm_rel.
  Proof.
    intros (Γ & s & H).
sq'.
    induction (normalisation Σ Γ s H) as [s _ IH].
    induction (term_subterm_wf s) as [s _ IH_sub] in Γ, H, IH |- *.
    econstructor.
    intros (Γ' & t2 & ?) [(t' & r & ts & eqctx)].
    eapply Relation_Properties.clos_rt_rtn1 in r.
inversion r.
    +
 subst.
eapply IH_sub; auto.
      intros.
      inversion H0.
      *
 subst.
        destruct (term_subterm_red1 X0) as [t'' [[redt' [tst' Htst']]]].
        eapply IH.
econstructor.
eauto.
red.
        sq.
exists t''.
split; eauto.
exists tst'.
now rewrite Htst'.
      *
 subst.
eapply cored_redp in H2 as [].
        pose proof (term_subterm_redp X1) as [t'' [[redt' [tst' Htst']]]].
        rewrite -Htst' in X0.
        destruct (term_subterm_red1 X0) as [t''' [[redt'' [tst'' Htst'']]]].
        eapply IH.
        eapply cored_redp.
sq.
transitivity t''; eauto.
        constructor; eauto.
        split.
        exists t'''.
split; auto.
exists tst''.
        now rewrite Htst'' Htst'.
    +
 subst.
eapply IH.
      *
 eapply red_neq_cored.
        eapply Relation_Properties.clos_rtn1_rt.
exact r.
        intros ?.
subst.
        eapply Relation_Properties.clos_rtn1_rt in X1.
        eapply cored_red_trans in X0; [| exact X1 ].
        eapply Acc_no_loop in X0.
eauto.
        eapply @normalisation; eauto.
      *
 split.
exists t'.
split; eauto.
    Grab Existential Variables.
