
(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "-deprecated-native-compiler-option" "-native-compiler" "no" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/metacoq/utils/theories" "MetaCoq.Utils" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/metacoq/common/theories" "MetaCoq.Common" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/metacoq/pcuic/theories" "MetaCoq.PCUIC" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Equations" "Equations" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-top" "MetaCoq.PCUIC.Syntax.PCUICInduction") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 686 lines to 155 lines, then from 168 lines to 375 lines, then from 380 lines to 212 lines, then from 225 lines to 1846 lines, then from 1847 lines to 422 lines, then from 435 lines to 825 lines, then from 829 lines to 471 lines, then from 484 lines to 1866 lines, then from 1869 lines to 304 lines, then from 317 lines to 3116 lines, then from 3087 lines to 413 lines, then from 426 lines to 1354 lines, then from 1355 lines to 459 lines, then from 472 lines to 1068 lines, then from 1073 lines to 478 lines, then from 491 lines to 628 lines, then from 633 lines to 482 lines, then from 495 lines to 811 lines, then from 815 lines to 487 lines, then from 500 lines to 4878 lines, then from 4877 lines to 4965 lines *)
(* coqc version 8.20+alpha compiled with OCaml 4.09.0
   coqtop version runner-cabngxqim-project-4504-concurrent-0:/builds/coq/coq/_build/default,(HEAD detached at cf8b86fadbc1c) (cf8b86fadbc1c3d0e41b3d5581bd378fe4080a66)
   Expected coqc runtime on this file: 6.001 sec *)








Require Coq.Init.Ltac.
Require Coq.ZArith.ZArith.
Require MetaCoq.Utils.LibHypsNaming.
Require Coq.Numbers.Cyclic.Int63.Uint63.
Require Coq.Floats.PrimFloat.
Require Coq.Floats.SpecFloat.
Require Coq.Floats.FloatOps.
Require Coq.Numbers.HexadecimalString.
Require Coq.Strings.String.
Require Coq.ssr.ssrbool.
Require Coq.ssr.ssreflect.
Require Coq.NArith.NArith.
Require Coq.micromega.Lia.
Require Coq.extraction.Extraction.
Require Coq.Unicode.Utf8_core.
Require Equations.Init.
Require Equations.Signature.
Require Equations.CoreTactics.
Require Coq.Relations.Relation_Definitions.
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
Require Coq.Program.Wf.
Require Coq.Logic.FunctionalExtensionality.
Require Equations.Prop.Subterm.
Require Equations.Prop.FunctionalInduction.
Require Equations.Prop.Tactics.
Require Equations.Prop.NoConfusion.
Require Equations.Prop.EqDecInstances.
Require Equations.Prop.Loader.
Require Equations.Prop.Telescopes.
Require Equations.Prop.Equations.
Require Coq.Structures.OrderedType.
Require Coq.Structures.Orders.
Require MetaCoq.Utils.MCCompare.
Require MetaCoq.Utils.ReflectEq.
Require Coq.Strings.Byte.
Require Coq.NArith.BinNat.
Require MetaCoq.Utils.ByteCompare.
Require Coq.Logic.Eqdep_dec.
Require MetaCoq.Utils.ByteCompareSpec.
Require Coq.Structures.OrdersAlt.
Require MetaCoq.Utils.bytestring.
Require Coq.Init.Decimal.
Require Coq.Numbers.DecimalString.
Require MetaCoq.Utils.MCString.
Require MetaCoq.Common.Primitive.
Require Coq.MSets.MSetList.
Require Coq.Arith.Arith.
Require Coq.Bool.Bool.
Require Coq.Classes.CRelationClasses.
Require Coq.Classes.Morphisms.
Require Coq.Classes.RelationClasses.
Require Coq.Lists.SetoidList.
Require Coq.Strings.Ascii.
Require Coq.Unicode.Utf8.
Require Coq.btauto.Algebra.
Require MetaCoq.Utils.MCSquash.
Require Equations.Type.Logic.
Require MetaCoq.Utils.MCProd.
Require Equations.Type.Relation.
Require Equations.Type.Relation_Properties.
Require MetaCoq.Utils.MCRelations.
Require MetaCoq.Utils.MCPrelude.
Require MetaCoq.Utils.MCReflect.
Require MetaCoq.Utils.MCList.
Require MetaCoq.Utils.MCOption.

Module Export AdmitTactic.
Module Import LocalFalse.
Inductive False : Prop := .
End LocalFalse.
Axiom proof_admitted : False.
Import Coq.Init.Ltac.
Tactic Notation "admit" := abstract case proof_admitted.
End AdmitTactic.

Module MetaCoq_DOT_Utils_DOT_All_Forall_WRAPPED.
Module All_Forall.
Import Coq.Lists.List Coq.Bool.Bool Coq.Arith.Arith Coq.ssr.ssreflect Coq.ssr.ssrbool Coq.Classes.Morphisms Coq.micromega.Lia Coq.Unicode.Utf8.
Import MetaCoq.Utils.MCPrelude MetaCoq.Utils.MCReflect MetaCoq.Utils.MCList MetaCoq.Utils.MCRelations MetaCoq.Utils.MCProd MetaCoq.Utils.MCOption.
Import Equations.Prop.Equations.

Import ListNotations.

Derive Signature for Forall Forall2.




Inductive All {A} (P : A -> Type) : list A -> Type :=
    All_nil : All P []
  | All_cons : forall (x : A) (l : list A),
                  P x -> All P l -> All P (x :: l).
Arguments All {A} P%_type _.
Arguments All_nil {_ _}.
Arguments All_cons {_ _ _ _}.
Derive Signature NoConfusion for All.
#[global] Hint Constructors All : core.

Inductive Alli {A} (P : nat -> A -> Type) (n : nat) : list A -> Type :=
| Alli_nil : Alli P n []
| Alli_cons hd tl : P n hd -> Alli P (S n) tl -> Alli P n (hd :: tl).
Arguments Alli_nil {_ _ _}.
Arguments Alli_cons {_ _ _ _ _}.
Derive Signature for Alli.
Derive NoConfusionHom for Alli.

Inductive All2 {A B : Type} (R : A -> B -> Type) : list A -> list B -> Type :=
  All2_nil : All2 R [] []
| All2_cons : forall (x : A) (y : B) (l : list A) (l' : list B),
    R x y -> All2 R l l' -> All2 R (x :: l) (y :: l').
Arguments All2_nil {_ _ _}.
Arguments All2_cons {_ _ _ _ _ _ _}.
Derive Signature for All2.
Derive NoConfusionHom for All2.
#[global] Hint Constructors All2 : core.

Lemma All2_tip {A} {P} (t u : A) : P t u -> All2 P [t] [u].
Proof.
now repeat constructor.
Qed.
#[global] Hint Resolve All2_tip : core.

Inductive All2_dep {A B : Type} {R : A -> B -> Type} (R' : forall a b, R a b -> Type) : forall {xs ys}, All2 R xs ys -> Type :=
| All2_dep_nil : All2_dep R' All2_nil
| All2_dep_cons : forall (x : A) (y : B) (l : list A) (l' : list B) (r : R x y) (rs : All2 R l l'),
    R' x y r -> All2_dep R' rs -> All2_dep R' (All2_cons r rs).
Arguments All2_dep_nil {_ _ _ _}.
Arguments All2_dep_cons {_ _ _ _ _ _ _ _ _ _} _ _.
Derive Signature for All2_dep.
Derive NoConfusionHom for All2_dep.
#[global] Hint Constructors All2_dep : core.

Inductive Forall2_dep {A B : Type} {R : A -> B -> Prop} (R' : forall a b, R a b -> Prop) : forall {xs ys}, Forall2 R xs ys -> Prop :=
| Forall2_dep_nil : Forall2_dep R' (@Forall2_nil _ _ _)
| Forall2_dep_cons : forall (x : A) (y : B) (l : list A) (l' : list B) (r : R x y) (rs : Forall2 R l l'),
    R' x y r -> Forall2_dep R' rs -> Forall2_dep R' (@Forall2_cons _ _ _ _ _ _ _ r rs).
Arguments Forall2_dep_nil {_ _ _ _}.
Arguments Forall2_dep_cons {_ _ _ _ _ _ _ _ _ _} _ _.
Derive Signature for Forall2_dep.
#[global] Hint Constructors Forall2_dep : core.

Inductive All2i {A B : Type} (R : nat -> A -> B -> Type) (n : nat)
  : list A -> list B -> Type :=
| All2i_nil : All2i R n [] []
| All2i_cons :
    forall x y l r,
      R n x y ->
      All2i R (S n) l r ->
      All2i R n (x :: l) (y :: r).
Arguments All2i_nil {_ _ _ _}.
Arguments All2i_cons {_ _ _ _ _ _ _ _}.

Derive Signature NoConfusionHom for All2i.

Inductive All3 {A B C : Type} (R : A -> B -> C -> Type) : list A -> list B -> list C -> Type :=
  All3_nil : All3 R [] [] []
| All3_cons : forall (x : A) (y : B) (z : C) (l : list A) (l' : list B) (l'' : list C),
    R x y z -> All3 R l l' l'' -> All3 R (x :: l) (y :: l') (z :: l'').
Arguments All3_nil {_ _ _ _}.
Arguments All3_cons {_ _ _ _ _ _ _ _ _ _}.

Inductive Forall3 {A B C : Type} (R : A -> B -> C -> Type) : list A -> list B -> list C -> Prop :=
  Forall3_nil : Forall3 R [] [] []
| Forall3_cons : forall (x : A) (y : B) (z : C) (l : list A) (l' : list B) (l'' : list C),
    R x y z -> Forall3 R l l' l'' -> Forall3 R (x :: l) (y :: l') (z :: l'').
Arguments Forall3_nil {_ _ _ _}.
Arguments Forall3_cons {_ _ _ _ _ _ _ _ _ _}.

#[global] Hint Constructors All3 Forall3 : core.
Derive Signature for All3 Forall3.
Derive NoConfusionHom for All3.

Definition invert_Forall2 {A B R l l'} (a : @Forall2 A B R l l')
  := match a in Forall2 _ l l'
           return
           match l, l' return @Forall2 A B R l l' -> Prop with
           | [], [] => fun a => Forall2_nil _ = a
           | [], _ | _, [] => fun _ => False
           | x :: xs, y :: ys
             => fun a => sigP (fun v => Forall2_cons _ _ (proj1 v) (proj2 v) = a)
           end a
     with
     | Forall2_nil _ => eq_refl
     | Forall2_cons _ _ r a => existP _ (conj r a) eq_refl
     end.
Import EqNotations.
Definition invert_Forall2_dep {A B R R' l l' a} (a' : @Forall2_dep A B R R' l l' a)
  := match a' in @Forall2_dep _ _ _ _ l l' a
           return
           match l, l' return forall a, @Forall2_dep A B R R' l l' a -> Prop with
           | [], [] => fun a a' => (rew [Forall2_dep _] invert_Forall2 a in Forall2_dep_nil) = a'
           | [], _ | _, [] => fun _ _ => False
           | x :: xs, y :: ys
             => fun a a' => sigP (fun v => (rew projP2 (invert_Forall2 a) in Forall2_dep_cons (proj1 v) (proj2 v)) = a')
           end a a'
     with
     | Forall2_dep_nil => eq_refl
     | Forall2_dep_cons r a => existP _ (conj r a) eq_refl
     end.

Definition Forall2_rect A B R (P : forall x y, Forall2 R x y -> Type)
  (Hn : P [] [] (@Forall2_nil _ _ _))
  (Hc : forall x y l l' r (a : Forall2 R l l'),
      P l l' a -> P (x :: l) (y :: l') (Forall2_cons _ _ r a))
  : forall l l' (a : @Forall2 A B R l l'), P l l' a.
Proof.
  fix F 1.
  destruct l as [|x xs], l' as [|y ys]; intro H;
    first [ specialize (F xs ys) | clear F ].
  all: generalize (invert_Forall2 H); cbn; try solve [ destruct 1 ].
  {
 intro; subst; exact Hn.
}
  {
 intro H'.
    specialize (Hc x y xs ys (proj1 (projP1 H')) (proj2 (projP1 H')) (F _)).
    destruct (projP2 H').
    exact Hc.
}
Defined.

Definition Forall2_rec A B R (P : forall x y, Forall2 R x y -> Set)
  (Hn : P [] [] (@Forall2_nil _ _ _))
  (Hc : forall x y l l' r (a : Forall2 R l l'),
      P l l' a -> P (x :: l) (y :: l') (Forall2_cons _ _ r a))
  : forall l l' (a : @Forall2 A B R l l'), P l l' a
  := @Forall2_rect A B R P Hn Hc.

Definition Forall2_dep_rect A B R R' (P : forall x y a, @Forall2_dep A B R R' x y a -> Type)
  (Hn : P [] [] (@Forall2_nil _ _ _) Forall2_dep_nil)
  (Hc : forall x y l l' r rs r' (a : Forall2_dep R' rs),
      P l l' rs a -> P (x :: l) (y :: l') (Forall2_cons _ _ r rs) (Forall2_dep_cons r' a))
  : forall l l' a (a' : @Forall2_dep A B R R' l l' a), P l l' a a'.
Proof.
  intros l l' a a'.
  induction a; generalize (invert_Forall2_dep a'); cbn.
  {
 intro; subst; exact Hn.
}
  {
 intro H'.
    specialize (Hc _ _ _ _ _ _ (proj1 (projP1 H')) (proj2 (projP1 H')) (IHa _)).
    destruct (projP2 H').
    exact Hc.
}
Defined.

Definition Forall2_dep_rec A B R R' (P : forall x y a, @Forall2_dep A B R R' x y a -> Set)
  (Hn : P [] [] (@Forall2_nil _ _ _) Forall2_dep_nil)
  (Hc : forall x y l l' r rs r' (a : Forall2_dep R' rs),
      P l l' rs a -> P (x :: l) (y :: l') (Forall2_cons _ _ r rs) (Forall2_dep_cons r' a))
  : forall l l' a (a' : @Forall2_dep A B R R' l l' a), P l l' a a'
  := @Forall2_dep_rect A B R R' P Hn Hc.

Section alli.
  Context {A} (p : nat -> A -> bool).
  Fixpoint alli (n : nat) (l : list A) : bool :=
  match l with
  | [] => true
  | hd :: tl => p n hd && alli (S n) tl
  end.
End alli.

Lemma alli_ext {A} (p q : nat -> A -> bool) n (l : list A) :
  (forall i, p i =1 q i) ->
  alli p n l = alli q n l.
Proof.
  intros hfg.
  induction l in n |- *; simpl; auto.
  now rewrite IHl.
Qed.

#[global] Instance alli_proper {A} :
   Proper ((pointwise_relation nat (pointwise_relation A eq)) ==> eq ==> eq ==> eq) alli.
Proof.
  intros f g fg.
  intros ? ? -> ? ? ->.
  now apply alli_ext.
Qed.

Lemma alli_impl {A} (p q : nat -> A -> bool) n (l : list A) :
  (forall i x, p i x -> q i x) ->
  alli p n l -> alli q n l.
Proof.
  intros hpq.
induction l in n |- *; simpl; auto.
  move/andb_and => [pna a'].
  rewrite (hpq _ _ pna).
  now apply IHl.
Qed.

Lemma allbiP {A} (P : nat -> A -> Type) (p : nat -> A -> bool) n l :
  (forall i x, reflectT (P i x) (p i x)) ->
  reflectT (Alli P n l) (alli p n l).
Proof.
  intros Hp.
  apply equiv_reflectT.
  -
 induction 1; rewrite /= // IHX // andb_true_r.
    now destruct (Hp n hd).
  -
 induction l in n |- *; rewrite /= //.
constructor.
    move/andb_and => [pa pl].
    constructor; auto.
now destruct (Hp n a).
Qed.

Lemma alli_Alli {A} (p : nat -> A -> bool) n l :
  alli p n l <~> Alli p n l.
Proof.
  destruct (allbiP p p n l).
  -
 intros.
destruct (p i x); now constructor.
  -
 split; eauto.
  -
 split; eauto.
by [].
Qed.

Lemma alli_shiftn {A} n k p (l : list A) :
  alli p (n + k) l = alli (fun i => p (n + i)) k l.
Proof.
  induction l in n, k, p |- *; simpl; auto.
f_equal.
  rewrite (IHl (S n) k p) (IHl 1 k _).
  apply alli_ext => x.
  now rewrite Nat.add_succ_r.
Qed.

Section alli.
  Context {A} (p q : nat -> A -> bool) (l l' : list A).

  Lemma alli_app n :
    alli p n (l ++ l') =
    alli p n l && alli p (#|l| + n) l'.
  Proof using Type.
    induction l in n |- *; simpl; auto.
    now rewrite IHl0 Nat.add_succ_r andb_assoc.
  Qed.

  Lemma alli_shift n :
    alli p n l = alli (fun i => p (n + i)) 0 l.
  Proof using Type.
    induction l in n, p |- *; simpl; auto.
    rewrite IHl0 (IHl0 _ 1) Nat.add_0_r.
    f_equal.
apply alli_ext => x.
    now rewrite Nat.add_succ_r.
  Qed.

  Lemma alli_map {B} (f : B -> A) n bs : alli p n (map f bs) = alli (fun i => p i ∘ f) n bs.
  Proof using Type.
    induction bs in n |- *; simpl; auto.
    now rewrite IHbs.
  Qed.
End alli.

Lemma alli_mapi {A B} (f : nat -> A -> bool) (g : nat -> B -> A) n l :
  alli f n (mapi_rec g l n) = alli (fun i x => f i (g i x)) n l.
Proof.
  revert n; induction l => n; simpl; auto.
  now rewrite IHl.
Qed.

Section Forallb2.
  Context {A B} (f : A -> B -> bool).

  Fixpoint forallb2 l l' :=
    match l, l' with
    | hd :: tl, hd' :: tl' => f hd hd' && forallb2 tl tl'
    | [], [] => true
    | _, _ => false
    end.

End Forallb2.

Section Forallb3.
  Context {A B C} (f : A -> B -> C -> bool).

  Fixpoint forallb3 l l' l'' :=
    match l, l', l'' with
    | hd :: tl, hd' :: tl', hd'' :: tl'' => f hd hd' hd'' && forallb3 tl tl' tl''
    | [], [], [] => true
    | _, _, _ => false
    end.

End Forallb3.

Lemma forallb2_refl :
  forall A (R : A -> A -> bool),
    (forall x, R x x) ->
    forall l, forallb2 R l l.
Proof.
  intros A R R_refl l.
  induction l.
  -
 reflexivity.
  -
 simpl.
rewrite R_refl.
assumption.
Qed.

Lemma forallb2_map :
  forall A B C D (R : A -> B -> bool) f g (l : list C) (l' : list D),
    forallb2 R (map f l) (map g l') =
    forallb2 (fun x y => R (f x) (g y)) l l'.
Proof.
  intros A B C D R f g l l'.
  induction l in l' |- *.
  -
 destruct l' => //.
  -
 destruct l' => /= //; rewrite IHl //.
Qed.

Lemma forall_map_spec {A B} {l} {f g : A -> B} :
  Forall (fun x => f x = g x) l <->
  map f l = map g l.
Proof.
  split.
  induction 1; simpl; trivial.
  now rewrite IHForall H.
  induction l => /= // [=] Ha Hl; constructor; auto.
Qed.

Lemma forall_map_id_spec {A} {l} {f : A -> A} :
  Forall (fun x => f x = x) l <-> map f l = l.
Proof.
  rewrite -{3}(map_id l).
apply forall_map_spec.
Qed.

Lemma forallb_Forall {A} (p : A -> bool) l
  : Forall p l <-> is_true (forallb p l).
Proof.
  split.
  induction 1; rewrite /= // H IHForall //.
  induction l; rewrite /= //.
rewrite andb_and.
  intros [pa pl].
  constructor; auto.
Qed.

Lemma forallbP {A} (P : A -> Prop) (p : A -> bool) l :
  (forall x, reflect (P x) (p x)) ->
  reflect (Forall P l) (forallb p l).
Proof.
  intros Hp.
  apply iff_reflect; change (forallb p l = true) with (forallb p l : Prop); split.
  -
 induction 1; rewrite /= // IHForall // andb_true_r.
    now destruct (Hp x).
  -
 induction l; rewrite /= //.
rewrite andb_and.
    intros [pa pl].
    constructor; auto.
now destruct (Hp a).
Qed.

Lemma forallb_ext {A} (p q : A -> bool) : p =1 q -> forallb p =1 forallb q.
Proof.
  intros hpq l.
  induction l; simpl; auto.
  now rewrite (hpq a) IHl.
Qed.

#[global] Instance forallb_proper {A} : Proper (`=1` ==> eq ==> eq) (@forallb A).
Proof.
  intros f g Hfg ? ? ->.
now apply forallb_ext.
Qed.

Lemma forallbP_cond {A} (P Q : A -> Prop) (p : A -> bool) l :
  Forall Q l ->
  (forall x, Q x -> reflect (P x) (p x)) -> reflect (Forall P l) (forallb p l).
Proof.
  intros HQ Hp.
  apply iff_reflect; split.
  -
 induction HQ; intros HP; depelim HP; rewrite /= // IHHQ // andb_true_r.
    now destruct (Hp x H).
  -
 induction HQ; rewrite /= //.
move/andb_and => [pa pl].
    constructor; auto.
now destruct (Hp _ H).
Qed.

Lemma nth_error_forallb {A} {p : A -> bool} {l : list A} {n x} :
  nth_error l n = Some x -> forallb p l -> p x.
Proof.
  intros Hnth HPl.
  induction l in n, Hnth, HPl |- * => //.
  -
 rewrite nth_error_nil in Hnth => //.
  -
 destruct n => /=; noconf Hnth.
    *
 now move: HPl => /= /andb_and.
    *
 eapply IHl; tea.
now move: HPl => /andb_and.
Qed.

Lemma forallb_nth_error {A} P l n :
  @forallb A P l -> on_Some_or_None P (nth_error l n).
Proof.
  induction l in n |- *.
  -
 intros _.
destruct n; constructor.
  -
 intro H.
apply forallb_Forall in H.
    inv H.
destruct n; cbn; auto.
    now apply forallb_Forall in H1; eauto.
Qed.

Lemma map_eq_inj {A B} (f g : A -> B) l: map f l = map g l ->
                                         All (fun x => f x = g x) l.
Proof.
  induction l.
simpl.
constructor.
simpl.
intros [=].
constructor; auto.
Qed.



Lemma Forall_mix {A} (P Q : A -> Prop) : forall l, Forall P l -> Forall Q l -> Forall (fun x => P x /\ Q x) l.
Proof.
  intros l Hl Hq.
induction Hl; inv Hq; constructor; auto.
Qed.

Lemma Forall_skipn {A} (P : A -> Prop) n l : Forall P l -> Forall P (skipn n l).
Proof.
  intros H.
revert n; induction H; intros n.
rewrite skipn_nil; auto.
  destruct n; simpl.
  -
 rewrite /skipn.
constructor; auto.
  -
 now auto.
Qed.

Lemma Forall_firstn {A} (P : A -> Prop) n l : Forall P l -> Forall P (firstn n l).
Proof.
  intros H.
revert n; induction H; intros n.
rewrite firstn_nil; auto.
  destruct n; simpl.
  -
 constructor; auto.
  -
 constructor; auto.
Qed.

Lemma forallb2_All2 {A B : Type} {p : A -> B -> bool}
      {l : list A} {l' : list B}:
  is_true (forallb2 p l l') -> All2 (fun x y => is_true (p x y)) l l'.
Proof.
  induction l in l' |- *; destruct l'; simpl; intros; try congruence.
  -
 constructor.
  -
 constructor.
revert H; rewrite andb_and; intros [px pl].
auto.
    apply IHl.
revert H; rewrite andb_and; intros [px pl].
auto.
Qed.

Lemma All2_forallb2 {A B : Type} {p : A -> B -> bool}
      {l : list A} {l' : list B} :
  All2 (fun x y => is_true (p x y)) l l' -> is_true (forallb2 p l l').
Proof.
  induction 1; simpl; intros; try congruence.
  rewrite andb_and.
intuition auto.
Qed.

Lemma forallb3_All3 {A B C : Type} {p : A -> B -> C -> bool}
      {l : list A} {l' : list B} {l'' : list C}:
  is_true (forallb3 p l l' l'') -> All3 (fun x y z => is_true (p x y z)) l l' l''.
Proof.
  induction l in l', l'' |- *; destruct l', l''; simpl; intros; try congruence.
  -
 constructor.
  -
 constructor.
revert H; rewrite andb_and; intros [px pl].
auto.
    apply IHl.
revert H; rewrite andb_and; intros [px pl].
auto.
Qed.

Lemma All3_forallb3 {A B C : Type} {p : A -> B -> C -> bool}
      {l : list A} {l' : list B} {l'' : list C} :
  All3 (fun x y z => is_true (p x y z)) l l' l'' -> is_true (forallb3 p l l' l'').
Proof.
  induction 1; simpl; intros; try congruence.
  rewrite andb_and.
intuition auto.
Qed.

Lemma All3P {A B C : Type} {p : A -> B -> C -> bool} {l l' l''} :
  reflectT (All3 p l l' l'') (forallb3 p l l' l'').
Proof.
  apply equiv_reflectT.
apply All3_forallb3.
apply forallb3_All3.
Qed.

Lemma All2_refl {A} {P : A -> A -> Type} l :
  (forall x, P x x) ->
  All2 P l l.
Proof.
  intros HP.
induction l; constructor; auto.
Qed.

Lemma forallb2_app {A B} (p : A -> B -> bool) l l' q q' :
  is_true (forallb2 p l l' && forallb2 p q q')
  -> is_true (forallb2 p (l ++ q) (l' ++ q')).
Proof.
  induction l in l' |- *; destruct l'; simpl; try congruence.
  move=> /andb_and[/andb_and[pa pl] pq].
now rewrite pa IHl // pl pq.
Qed.

Lemma All2_map_equiv {A B C D} {R : C -> D -> Type} {f : A -> C} {g : B -> D} {l l'} :
  All2 (fun x y => R (f x) (g y)) l l' <~> All2 R (map f l) (map g l').
Proof.
  split.
  -
 induction 1; simpl; constructor; try congruence; try assumption.
  -
 induction l in l' |- *; destruct l'; intros H; depelim H; constructor; auto.
Qed.

Lemma All2_map {A B C D} {R : C -> D -> Type} {f : A -> C} {g : B -> D} {l l'} :
  All2 (fun x y => R (f x) (g y)) l l' -> All2 R (map f l) (map g l').
Proof.
apply All2_map_equiv.
Qed.

Lemma All2_map_inv {A B C D} {R : C -> D -> Type} {f : A -> C} {g : B -> D} {l l'} :
  All2 R (map f l) (map g l') -> All2 (fun x y => R (f x) (g y)) l l'.
Proof.
apply All2_map_equiv.
Qed.

Lemma All2_tip_l {A B} {R : A -> B -> Type} x y : All2 R [x] y -> ∑ y', (y = [y']) * R x y'.
Proof.
  intros a; depelim a.
depelim a.
exists y0; split => //.
Qed.

Lemma All2i_All2i_mix {A B} {P Q : nat -> A -> B -> Type}
      {n} {l : list A} {l' : list B} :
  All2i P n l l' -> All2i Q n l l' -> All2i (fun i x y => (P i x y * Q i x y)%type) n l l'.
Proof.
  induction 2; simpl; intros; constructor.
  inv X; intuition auto.
  apply IHX0.
inv X; intuition auto.
Qed.

Lemma All2i_nth_error {A B} {P : nat -> A -> B -> Type} {l l' n x c k} :
  All2i P k l l' ->
  nth_error l n = Some x ->
  nth_error l' n = Some c ->
  P (k + n)%nat x c.
Proof.
  induction 1 in n |- *.
  *
 rewrite !nth_error_nil => //.
  *
 destruct n.
    +
 simpl.
intros [= <-] [= <-].
now rewrite Nat.add_0_r.
    +
 simpl.
intros hnth hnth'.
specialize (IHX _ hnth hnth').
      now rewrite Nat.add_succ_r.
Qed.



















Lemma All2_All_mix_left {A B} {P : A -> Type} {Q : A -> B -> Type}
      {l : list A} {l' : list B} :
  All P l -> All2 Q l l' -> All2 (fun x y => (P x * Q x y)%type) l l'.
Proof.
  induction 2; simpl; intros; constructor.
  inv X; intuition auto.
  apply IHX0.
inv X; intuition auto.
Qed.

Lemma All2_All_mix_right {A B} {P : B -> Type} {Q : A -> B -> Type}
      {l : list A} {l' : list B} :
  All P l' -> All2 Q l l' -> All2 (fun x y => (Q x y * P y)%type) l l'.
Proof.
  induction 2; simpl; intros; constructor.
  inv X; intuition auto.
  apply IHX0.
inv X; intuition auto.
Qed.

Lemma All2i_All_mix_left {A B} {P : A -> Type} {Q : nat -> A -> B -> Type}
      {n} {l : list A} {l' : list B} :
  All P l -> All2i Q n l l' -> All2i (fun i x y => (P x * Q i x y)%type) n l l'.
Proof.
  induction 2; simpl; intros; constructor.
  inv X; intuition auto.
  apply IHX0.
inv X; intuition auto.
Qed.

Lemma All2i_All_mix_right {A B} {P : B -> Type} {Q : nat -> A -> B -> Type}
      {n} {l : list A} {l' : list B} :
  All P l' -> All2i Q n l l' -> All2i (fun i x y => (Q i x y * P y)%type) n l l'.
Proof.
  induction 2; simpl; intros; constructor.
  inv X; intuition auto.
  apply IHX0.
inv X; intuition auto.
Qed.

Lemma All2i_All2_mix_left {A B} {P : A -> B -> Type} {Q : nat -> A -> B -> Type}
      {n} {l : list A} {l' : list B} :
  All2 P l l' -> All2i Q n l l' -> All2i (fun i x y => (P x y * Q i x y)%type) n l l'.
Proof.
  induction 2; simpl; intros; constructor.
  inv X; intuition auto.
  apply IHX0.
inv X; intuition auto.
Qed.

Lemma All2_All2_All2 {A B C} {P Q R} (l : list A) (l' : list B) (l'' : list C) :
  All2 P l l' -> All2 Q l' l'' ->
  (forall x y z, P x y -> Q y z -> R x z) ->
  All2 R l l''.
Proof.
  induction 1 in l'' |- *; intros a; depelim a; constructor; eauto.
Qed.

Lemma Forall_All {A : Type} (P : A -> Prop) l :
  Forall P l -> All P l.
Proof.
  induction l; intros H; constructor; auto.
inv H.
auto.
  apply IHl.
inv H; auto.
Qed.

Lemma All_Forall {A : Type} (P : A -> Prop) l :
  All P l -> Forall P l.
Proof.
induction 1; constructor; auto.
Qed.

Lemma forallb_All {A} (p : A -> bool) l : is_true (forallb p l) -> All p l.
Proof.
  move/forallb_Forall.
apply Forall_All.
Qed.

Lemma All_forallb {A} (p : A -> bool) l : All p l -> is_true (forallb p l).
Proof.
  move/All_Forall.
apply forallb_Forall.
Qed.

Lemma All_firstn {A} {P : A -> Type} {l} {n} : All P l -> All P (firstn n l).
Proof.
intros HPL; induction HPL in n |- * ; simpl; destruct n; try econstructor; eauto.
Qed.

Lemma All_skipn {A} {P : A -> Type} {l} {n} : All P l -> All P (skipn n l).
Proof.
intros HPL; induction HPL in n |- * ; simpl; destruct n; try econstructor; eauto.
Qed.

Lemma All_app {A} {P : A -> Type} {l l'} : All P (l ++ l') -> All P l * All P l'.
Proof.
  induction l; simpl; auto.
intros H; depelim H; constructor; intuition auto.
Qed.

Lemma All_app_inv {A} (P : A -> Type) l l' : All P l -> All P l' -> All P (l ++ l').
Proof.
  intros Hl Hl'.
induction Hl.
apply Hl'.
  constructor; intuition auto.
Defined.

Lemma All_True {A} l : All (fun x : A => True) l.
Proof.
  induction l; intuition auto.
Qed.

Lemma All_tip {A} {P : A -> Type} {a : A} : P a <~> All P [a].
Proof.
split; intros.
repeat constructor; auto.
now depelim X.
Qed.

Lemma All_mix {A} {P : A -> Type} {Q : A -> Type} {l} :
  All P l -> All Q l -> All (fun x => (P x * Q x)%type) l.
Proof.
induction 1; intros Hq; inv Hq; constructor; auto.
Qed.

Lemma All2_All_left {A B} {P : A -> B -> Type} {Q : A -> Type} {l l'} :
  All2 P l l' ->
  (forall x y, P x y -> Q x) ->
  All Q l.
Proof.
  intros HF H.
induction HF; constructor; eauto.
Qed.

Lemma All2_All_right {A B} {P : A -> B -> Type} {Q : B -> Type} {l l'} :
  All2 P l l' ->
  (forall x y, P x y -> Q y) ->
  All Q l'.
Proof.
  intros HF H.
induction HF; constructor; eauto.
Qed.

Lemma All2_right {A B} {P : B -> Type} {l : list A} {l'} :
  All2 (fun x y => P y) l l' -> All P l'.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma All2_impl_All2 {A B} {P Q : A -> B -> Type} {l l'} :
    All2 P l l' ->
    All2 (fun x y => P x y -> Q x y) l l' ->
    All2 Q l l'.
Proof.
  induction 1; inversion 1; constructor; auto.
Qed.

Lemma All2_impl {A B} {P Q : A -> B -> Type} {l l'} :
    All2 P l l' ->
    (forall x y, P x y -> Q x y) ->
    All2 Q l l'.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma All2_eq_eq {A} (l l' : list A) : l = l' -> All2 (fun x y => x = y) l l'.
Proof.
  intros ->.
induction l';  constructor; auto.
Qed.

Lemma All2_reflexivity {A} {P : A -> A -> Type} :
  CRelationClasses.Reflexive P -> CRelationClasses.Reflexive (All2 P).
Proof.
  intros hp x.
eapply All2_refl.
intros; reflexivity.
Qed.

Lemma All2_symmetry {A} (R : A -> A -> Type) :
  CRelationClasses.Symmetric R ->
  CRelationClasses.Symmetric (All2 R).
Proof.
  intros HR x y l.
  induction l; constructor; auto.
Qed.

Lemma All2_transitivity {A} (R : A -> A -> Type) :
  CRelationClasses.Transitive R ->
  CRelationClasses.Transitive (All2 R).
Proof.
  intros HR x y z l; induction l in z |- *; auto.
  intros H; inv H.
constructor; eauto.
Qed.

Lemma All2_apply {A B C} {D : A -> B -> C -> Type} {l : list B} {l' : list C} :
  forall (a : A),
    All2 (fun x y => forall a : A, D a x y) l l' ->
    All2 (fun x y => D a x y) l l'.
Proof.
  intros a all.
eapply (All2_impl all); auto.
Qed.

Lemma All2_apply_arrow {A B C} {D : B -> C -> Type} {l : list B} {l' : list C} :
  A -> All2 (fun x y => A -> D x y) l l' ->
  All2 (fun x y => D x y) l l'.
Proof.
  intros a all.
eapply (All2_impl all); auto.
Qed.

Lemma All2_apply_dep_arrow {B C} {A} {D : B -> C -> Type} {l : list B} {l' : list C} :
  All A l ->
  All2 (fun x y => A x -> D x y) l l' ->
  All2 D l l'.
Proof.
  intros a all.
  eapply All2_All_mix_left in all; tea.
  eapply (All2_impl all); intuition auto.
Qed.

Lemma All2_apply_dep_All {B C} {A} {D : C -> Type} {l : list B} {l' : list C} :
  All A l ->
  All2 (fun x y => A x -> D y) l l' ->
  All D l'.
Proof.
  intros a all.
  eapply All2_All_mix_left in all; tea.
  eapply All2_impl in all.
2:{
 intros x y [ha hd].
exact (hd ha).
}
  eapply All2_All_right; tea.
auto.
Qed.

Lemma All2P {A B : Type} {P : A -> B -> Type} {p : A -> B -> bool} {l l'} :
  (forall x y, reflectT (P x y) (p x y)) ->
  reflectT (All2 P l l') (forallb2 p l l').
Proof.
  intro H.
  apply equiv_reflectT; intro X.
  -
 eapply All2_forallb2, All2_impl with (1 := X).
    move => x y /H //.
  -
 apply forallb2_All2 in X.
    eapply All2_impl with (1 := X).
    move => x y /H //.
Qed.

Lemma All2i_All_left {A B} {P : nat -> A -> B -> Type} {Q : A -> Type} {n l l'} :
  All2i P n l l' ->
  (forall i x y, P i x y -> Q x) ->
  All Q l.
Proof.
  intros HF H.
induction HF; constructor; eauto.
Qed.

Lemma All2i_All_right {A B} {P : nat -> A -> B -> Type} {Q : B -> Type} {n l l'} :
  All2i P n l l' ->
  (forall i x y, P i x y -> Q y) ->
  All Q l'.
Proof.
  intros HF H.
induction HF; constructor; eauto.
Qed.

Lemma All2_dep_impl {A B} {P : A -> B -> Type} {P' Q' : forall a b, P a b -> Type} {l l'} {a : All2 P l l'} :
    All2_dep P' a ->
    (forall x y r, P' x y r -> Q' x y r) ->
    All2_dep Q' a.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma All_refl {A} (P : A -> Type) l : (forall x, P x) -> All P l.
Proof.
  intros Hp; induction l; constructor; auto.
Qed.

Lemma All_rev_map {A B} (P : A -> Type) f (l : list B) : All (fun x => P (f x)) l -> All P (rev_map f l).
Proof.
induction 1.
constructor.
rewrite rev_map_cons.
apply All_app_inv; auto.
Qed.

Lemma All_rev (A : Type) (P : A -> Type) (l : list A) : All P l -> All P (List.rev l).
Proof.
  induction l using rev_ind.
constructor.
rewrite rev_app_distr.
  simpl.
intros X; apply All_app in X as [? ?].
inversion a0; intuition auto.
Qed.

Lemma All_rev_inv {A} (P : A -> Type) (l : list A) : All P (List.rev l) -> All P l.
Proof.
  induction l using rev_ind.
constructor.
  intros.
rewrite rev_app_distr in X.
simpl.
  apply All_app in X as [Allx Alll].
inv Allx.
   apply All_app_inv; intuition eauto.
Qed.

Lemma All_impl_All {A} {P Q} {l : list A} : All P l -> All (fun x => P x -> Q x) l -> All Q l.
Proof.
induction 1; inversion 1; constructor; intuition auto.
Qed.

Lemma Alli_impl_Alli {A} {P Q} (l : list A) {n} : Alli P n l -> Alli (fun n x => P n x -> Q n x) n l -> Alli Q n l.
Proof.
induction 1; inversion 1; constructor; intuition auto.
Defined.

Lemma All_impl {A} {P Q} {l : list A} : All P l -> (forall x, P x -> Q x) -> All Q l.
Proof.
induction 1; try constructor; intuition auto.
Qed.

Lemma Alli_impl {A} {P Q} (l : list A) {n} : Alli P n l -> (forall n x, P n x -> Q n x) -> Alli Q n l.
Proof.
induction 1; try constructor; intuition auto.
Defined.

Lemma All_map {A B} {P : B -> Type} {f : A -> B} {l : list A} :
  All (fun x => P (f x)) l -> All P (map f l).
Proof.
induction 1; constructor; auto.
Qed.

Lemma All_map_inv {A B} (P : B -> Type) (f : A -> B) l : All P (map f l) -> All (fun x => P (f x)) l.
Proof.
induction l; intros Hf; inv Hf; try constructor; eauto.
Qed.

Lemma In_All {A} {P : A -> Type} l :
    (∀ x : A, In x l -> P x) -> All P l.
Proof.
  induction l; cbn; constructor; auto.
Qed.

Lemma All_nth_error :
  forall A P l i x,
    @All A P l ->
    nth_error l i = Some x ->
    P x.
Proof.
  intros A P l i x h e.
  induction h in i, x, e |- *.
  -
 destruct i.
all: discriminate.
  -
 destruct i.
    +
 simpl in e.
inversion e.
subst.
clear e.
      assumption.
    +
 simpl in e.
eapply IHh in e.
      assumption.
Qed.

Lemma Alli_mix {A} {P : nat -> A -> Type} {Q : nat -> A -> Type} {n l} :
  Alli P n l -> Alli Q n l -> Alli (fun n x => (P n x * Q n x)%type) n l.
Proof.
induction 1; intros Hq; inv Hq; constructor; auto.
Qed.

Lemma Alli_All {A} {P : nat -> A -> Type} {Q : A -> Type} {l n} :
  Alli P n l ->
  (forall n x, P n x -> Q x) ->
  All Q l.
Proof.
induction 1; constructor; eauto.
Qed.

Lemma Alli_app {A} (P : nat -> A -> Type) n l l' : Alli P n (l ++ l') -> Alli P n l * Alli P (length l + n) l'.
Proof.
  induction l in n, l' |- *; intros H.
split; try constructor.
apply H.
  inversion_clear H.
split; intuition auto.
constructor; auto.
eapply IHl; eauto.
  simpl.
replace (S (#|l| + n)) with (#|l| + S n) by lia.
  eapply IHl; eauto.
Qed.

Lemma Alli_nth_error :
  forall A P k l i x,
    @Alli A P k l ->
    nth_error l i = Some x ->
    P (k + i) x.
Proof.
  intros A P k l i x h e.
  induction h in i, x, e |- *.
  -
 destruct i.
all: discriminate.
  -
 destruct i.
    +
 simpl in e.
inversion e.
subst.
clear e.
      replace (n + 0) with n by lia.
      assumption.
    +
 simpl in e.
eapply IHh in e.
      replace (n + S i) with (S n + i) by lia.
      assumption.
Qed.

Lemma forall_nth_error_All :
  forall {A} (P : A -> Type) l,
    (forall i x, nth_error l i = Some x -> P x) ->
    All P l.
Proof.
  intros A P l h.
  induction l.
  -
 constructor.
  -
 constructor.
    +
 specialize (h 0 a eq_refl).
assumption.
    +
 eapply IHl.
intros i x e.
eapply (h (S i)).
assumption.
Qed.

Lemma forall_nth_error_Alli :
  forall {A} (P : nat -> A -> Type) k l,
    (forall i x, nth_error l i = Some x -> P (k + i) x) ->
    Alli P k l.
Proof.
  intros A P k l h.
  induction l in k, h |- *.
  -
 constructor.
  -
 constructor.
    +
 specialize (h 0 a eq_refl).
now rewrite Nat.add_0_r in h.
    +
 apply IHl.
intros.
specialize (h (S i) x H).
      simpl.
now replace (S (k + i)) with (k + S i) by lia.
Qed.

Lemma Alli_mapi {A B} {P : nat -> B -> Type} (f : nat -> A -> B) k l :
  Alli (fun n a => P n (f n a)) k l <~> Alli P k (mapi_rec f l k).
Proof.
  split.
  {
 induction 1.
simpl.
constructor.
    simpl.
constructor; eauto.
}
  {
 induction l in k |- *.
simpl.
constructor.
    simpl.
intros.
inversion X.
constructor; eauto.
}
Qed.

Lemma Alli_shift {A} {P : nat -> A -> Type} k l :
  Alli (fun x => P (S x)) k l ->
  Alli P (S k) l.
Proof.
  induction 1; simpl; constructor; auto.
Qed.

Lemma Alli_refl {A} (P : nat -> A -> Type) n (l : list A) :
  (forall n x, P n x) -> Alli P n l.
Proof.
  intros H.
induction l in n |- *; constructor; auto.
Defined.

Lemma Alli_rev {A} {P : nat -> A -> Type} k l :
  Alli P k l ->
  Alli (fun k' => P (Nat.pred #|l| - k' + k)) 0 (List.rev l).
Proof.
  revert k.
  induction l using rev_ind; simpl; intros; try constructor.
  eapply Alli_app in X.
intuition.
  rewrite rev_app_distr.
rewrite app_length.
  simpl.
constructor.
  replace (Nat.pred (#|l| + 1) - 0) with #|l| by lia.
  inversion b.
eauto.
specialize (IHl _ a).
  eapply Alli_shift.
eapply Alli_impl.
eauto.
  simpl; intros.
  now replace (Nat.pred (#|l| + 1) - S n) with (Nat.pred #|l| - n) by lia.
Qed.

Lemma Alli_rev_inv {A: Type} (P : nat -> A -> Type) (k : nat) (l : list A) :
  Alli P k (List.rev l) ->
  Alli (fun k' : nat => P (Nat.pred #|l| - k' + k)) 0 l.
Proof.
  intros alli.
  eapply Alli_rev in alli.
rewrite List.rev_involutive in alli.
  now len in alli.
Qed.

Lemma Alli_app_inv {A} {P} {l l' : list A} {n} : Alli P n l -> Alli P (n + #|l|) l' -> Alli P n (l ++ l').
Proof.
  induction 1; simpl; auto.
 now rewrite Nat.add_0_r.
  rewrite Nat.add_succ_r.
simpl in IHX.
  intros H; specialize (IHX H).
  constructor; auto.
Qed.

Lemma Alli_rev_nth_error {A} (l : list A) n P x :
  Alli P 0 (List.rev l) ->
  nth_error l n = Some x ->
  P (#|l| - S n) x.
Proof.
  induction l in x, n |- *; simpl.
  {
 rewrite nth_error_nil; discriminate.
}
  move/Alli_app => [Alll Alla].
inv Alla.
clear X0.
  destruct n as [|n'].
  -
 move=> [=] <-.
rewrite List.rev_length Nat.add_0_r in X.
    now rewrite Nat.sub_0_r.
  -
 simpl.
eauto.
Qed.

Lemma Alli_shiftn {A} {P : nat -> A -> Type} k l n :
  Alli (fun x => P (n + x)) k l -> Alli P (n + k) l.
Proof.
  induction 1; simpl; constructor; auto.
  now rewrite Nat.add_succ_r in IHX.
Qed.

Lemma Alli_shiftn_inv {A} {P : nat -> A -> Type} k l n :
  Alli P (n + k) l -> Alli (fun x => P (n + x)) k l.
Proof.
  induction l in n, k |- *; simpl; constructor; auto.
  inv X; auto.
inv X; auto.
apply IHl.
  now rewrite Nat.add_succ_r.
Qed.

Lemma Alli_All_mix {A} {P : nat -> A -> Type} (Q : A -> Type) k l :
  Alli P k l -> All Q l -> Alli (fun k x => (P k x) * Q x)%type k l.
Proof.
  induction 1; constructor; try inversion X0; intuition auto.
Qed.

Inductive OnOne2 {A : Type} (P : A -> A -> Type) : list A -> list A -> Type :=
| OnOne2_hd hd hd' tl : P hd hd' -> OnOne2 P (hd :: tl) (hd' :: tl)
| OnOne2_tl hd tl tl' : OnOne2 P tl tl' -> OnOne2 P (hd :: tl) (hd :: tl').
Derive Signature NoConfusion for OnOne2.

Lemma OnOne2_All_mix_left {A} {P : A -> A -> Type} {Q : A -> Type} {l l'} :
  All Q l -> OnOne2 P l l' -> OnOne2 (fun x y => (P x y * Q x)%type) l l'.
Proof.
  intros H; induction 1; constructor; try inv H; intuition.
Qed.

Lemma OnOne2_All_mix_both {A} {P : A -> A -> Type} {Q R : A -> Type} {l l'} :
  All Q l -> All R l' -> OnOne2 P l l' -> OnOne2 (fun x y => (P x y × Q x × R y)%type) l l'.
Proof.
  intros H H'; induction 1; constructor; try inv H; try inv H'; intuition.
Qed.

Lemma OnOne2_app {A} (P : A -> A -> Type) l tl tl' : OnOne2 P tl tl' -> OnOne2 P (l ++ tl) (l ++ tl').
Proof.
induction l; simpl; try constructor; auto.
Qed.

Lemma OnOne2_app_r {A} (P : A -> A -> Type) l l' tl :
  OnOne2 P l l' ->
  OnOne2 P (l ++ tl) (l' ++ tl).
Proof.
induction 1; constructor; auto.
Qed.

Lemma OnOne2_length {A} {P} {l l' : list A} : OnOne2 P l l' -> #|l| = #|l'|.
Proof.
induction 1; simpl; congruence.
Qed.

Lemma OnOne2_mapP {A B} {P} {l l' : list A} (f : A -> B) :
  OnOne2 (on_rel P f) l l' -> OnOne2 P (map f l) (map f l').
Proof.
induction 1; simpl; constructor; try congruence; try assumption.
Qed.

Lemma OnOne2_map {A B} {P : B -> B -> Type} {l l' : list A} (f : A -> B) :
  OnOne2 (on_Trel P f) l l' -> OnOne2 P (map f l) (map f l').
Proof.
induction 1; simpl; constructor; try congruence; try assumption.
Qed.

Lemma OnOne2_sym {A} (P : A -> A -> Type) l l' : OnOne2 (fun x y => P y x) l' l -> OnOne2 P l l'.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma OnOne2_exist {A} (P : A -> A -> Type) (Q : A -> A -> Type) l l' :
  OnOne2 P l l' ->
  (forall x y, P x y -> ∑ z, Q x z × Q y z) ->
  ∑ r, (OnOne2 Q l r × OnOne2 Q l' r).
Proof.
  intros H HPQ.
induction H.
  -
 destruct (HPQ _ _ p).
destruct p0.
    now exists (x :: tl); intuition constructor.
               -
 destruct IHOnOne2 as [r [? ?]].
                 now exists (hd :: r); intuition constructor.
Qed.


Lemma OnOne2_ind_l :
  forall A (R : list A -> A -> A -> Type)
    (P : forall L l l', OnOne2 (R L) l l' -> Type),
    (forall L x y l (r : R L x y), P L (x :: l) (y :: l) (OnOne2_hd _ _ _ l r)) ->
    (forall L x l l' (h : OnOne2 (R L) l l'),
        P L l l' h ->
        P L (x :: l) (x :: l') (OnOne2_tl _ x _ _ h)
    ) ->
    forall l l' h, P l l l' h.
Proof.
  intros A R P hhd htl l l' h.
induction h ; eauto.
Qed.

Lemma OnOne2_impl_exist_and_All :
  forall A (l1 l2 l3 : list A) R1 R2 R3,
    OnOne2 R1 l1 l2 ->
    All2 R2 l3 l2 ->
    (forall x x' y, R1 x y -> R2 x' y -> ∑ z : A, R3 x z × R2 x' z) ->
    ∑ l4, OnOne2 R3 l1 l4 × All2 R2 l3 l4.
Proof.
  intros A l1 l2 l3 R1 R2 R3 h1 h2 h.
  induction h1 in l3, h2 |- *.
  -
 destruct l3.
    +
 inversion h2.
    +
 inversion h2.
subst.
    specialize (h _ _ _ p X) as hh.
    destruct hh as [? [? ?]].
    eexists.
constructor.
      *
 constructor.
eassumption.
      *
 constructor ; eauto.
  -
 destruct l3.
    +
 inversion h2.
    +
 inversion h2.
subst.
    specialize (IHh1 _ X0).
destruct IHh1 as [? [? ?]].
    eexists.
constructor.
      *
 eapply OnOne2_tl.
eassumption.
      *
 constructor ; eauto.
Qed.

Lemma OnOne2_impl_exist_and_All_r :
  forall A (l1 l2 l3 : list A) R1 R2 R3,
    OnOne2 R1 l1 l2 ->
    All2 R2 l2 l3 ->
    (forall x x' y, R1 x y -> R2 y x' -> ∑ z : A, R3 x z × R2 z x') ->
    ∑ l4, ( OnOne2 R3 l1 l4 × All2 R2 l4 l3 ).
Proof.
  intros A l1 l2 l3 R1 R2 R3 h1 h2 h.
  induction h1 in l3, h2 |- *.
  -
 destruct l3.
    +
 inversion h2.
    +
 inversion h2.
subst.
      specialize (h _ _ _ p X) as hh.
      destruct hh as [? [? ?]].
      eexists.
split.
      *
 constructor.
eassumption.
      *
 constructor ; eauto.
  -
 destruct l3.
    +
 inversion h2.
    +
 inversion h2.
subst.
      specialize (IHh1 _ X0).
destruct IHh1 as [? [? ?]].
      eexists.
split.
      *
 eapply OnOne2_tl.
eassumption.
      *
 constructor ; eauto.
Qed.

Lemma OnOne2_split :
  forall A (P : A -> A -> Type) l l',
    OnOne2 P l l' ->
    ∑ x y u v,
      P x y ×
      (l = u ++ x :: v /\
      l' = u ++ y :: v).
Proof.
  intros A P l l' h.
  induction h.
  -
 exists hd, hd', [], tl.
    intuition eauto.
  -
 destruct IHh as [x [y [u [v ?]]]].
    exists x, y, (hd :: u), v.
    intuition eauto.
all: subst.
all: reflexivity.
Qed.

Lemma OnOne2_impl {A} {P Q} {l l' : list A} :
  OnOne2 P l l' ->
  (forall x y, P x y -> Q x y) ->
  OnOne2 Q l l'.
Proof.
  induction 1; constructor; intuition eauto.
Qed.

Lemma OnOne2_nth_error {A} (l l' : list A) n t P :
  OnOne2 P l l' ->
  nth_error l n = Some t ->
  ∑ t', (nth_error l' n = Some t') *
  ((t = t') + (P t t')).
Proof.
  induction 1 in n |- *.
  destruct n; simpl.
  -
 intros [= ->].
exists hd'; intuition auto.
  -
 exists t.
intuition auto.
  -
 destruct n; simpl; auto.
    intros [= ->].
exists t; intuition auto.
Qed.

Lemma OnOne2_nth_error_r {A} (l l' : list A) n t' P :
  OnOne2 P l l' ->
  nth_error l' n = Some t' ->
  ∑ t, (nth_error l n = Some t) *
  ((t = t') + (P t t')).
Proof.
  induction 1 in n |- *.
  destruct n; simpl.
  -
 intros [= ->].
exists hd; intuition auto.
  -
 exists t'.
intuition auto.
  -
 destruct n; simpl; auto.
    intros [= ->].
exists t'; intuition auto.
Qed.

Lemma OnOne2_impl_All_r {A} (P : A -> A -> Type) (Q : A -> Type) l l' :
  (forall x y, Q x -> P x y -> Q y) ->
  OnOne2 P l l' -> All Q l -> All Q l'.
Proof.
  intros HPQ.
  induction 1; intros H; depelim H; constructor; auto.
  now eapply HPQ.
Qed.

Lemma OnOne2_All2_All2 {A : Type} {l1 l2 l3 : list A} {R1 R2 R3  : A -> A -> Type} :
  OnOne2 R1 l1 l2 ->
  All2 R2 l1 l3 ->
  (forall x y, R2 x y -> R3 x y) ->
  (forall x y z : A, R1 x y -> R2 x z -> R3 y z) ->
  All2 R3 l2 l3.
Proof.
  intros o.
induction o in l3 |- *.
  intros H; depelim H.
  intros Hf Hf'.
specialize (Hf'  _ _ _ p r).
constructor; auto.
  eapply All2_impl; eauto.
  intros H; depelim H.
  intros Hf.
specialize (IHo _ H Hf).
  constructor; auto.
Qed.

Lemma OnOne2_All_All {A : Type} {l1 l2 : list A} {R1  : A -> A -> Type} {R2 R3 : A -> Type} :
  OnOne2 R1 l1 l2 ->
  All R2 l1 ->
  (forall x, R2 x -> R3 x) ->
  (forall x y : A, R1 x y -> R2 x -> R3 y) ->
  All R3 l2.
Proof.
  intros o.
induction o.
  intros H; depelim H.
  intros Hf Hf'.
specialize (Hf' _ _ p r).
constructor; auto.
  eapply All_impl; eauto.
  intros H; depelim H.
  intros Hf.
specialize (IHo H Hf).
  constructor; auto.
Qed.

Lemma OnOne2_map_inv {A} {P : A -> A -> Type} (l : list A) (l' : list A) (f : A -> A) :
  (forall x y, P (f x) y -> ∑ y', y = f y') ->
  OnOne2 P (List.map f l) l' ->
  ∑ l'', OnOne2 (fun x y => P (f x) (f y)) l l''.
Proof.
  intros hp.
  induction l in l' |- *.
  -
 intros o; depelim o; constructor.
  -
 intros o; depelim o.
specialize (IHl l).
    destruct (hp _ _ p).
subst hd'.
    eexists.
econstructor.
exact p.
    destruct (IHl _ o).
    eexists.
now econstructor 2.
Qed.

Inductive OnOne2i {A : Type} (P : nat -> A -> A -> Type) : nat -> list A -> list A -> Type :=
| OnOne2i_hd i hd hd' tl : P i hd hd' -> OnOne2i P i (hd :: tl) (hd' :: tl)
| OnOne2i_tl i hd tl tl' : OnOne2i P (S i) tl tl' -> OnOne2i P i (hd :: tl) (hd :: tl').
Derive Signature NoConfusion for OnOne2i.

Lemma OnOne2i_All_mix_left {A} {P : nat -> A -> A -> Type} {Q : A -> Type} {i l l'} :
  All Q l -> OnOne2i P i l l' -> OnOne2i (fun i x y => (P i x y * Q x)%type) i l l'.
Proof.
  intros H; induction 1; constructor; try inv H; intuition.
Qed.

Lemma OnOne2i_app {A} (P : nat -> A -> A -> Type) {i l tl tl'} :
  OnOne2i P (#|l| + i) tl tl' ->
  OnOne2i P i (l ++ tl) (l ++ tl').
Proof.
induction l in i |- *; simpl; try constructor; eauto.
  eapply IHl.
now rewrite Nat.add_succ_r.
Qed.

Lemma OnOne2i_app_r {A} (P : nat -> A -> A -> Type) i l l' tl :
  OnOne2i P i l l' ->
  OnOne2i P i (l ++ tl) (l' ++ tl).
Proof.
induction 1; constructor; auto.
Qed.

Lemma OnOne2i_length {A} {P} {i} {l l' : list A} : OnOne2i P i l l' -> #|l| = #|l'|.
Proof.
induction 1; simpl; congruence.
Qed.

Lemma OnOne2i_mapP {A B} {P} {i} {l l' : list A} (f : A -> B) :
  OnOne2i (fun i => on_rel (P i) f) i l l' -> OnOne2i P i (map f l) (map f l').
Proof.
induction 1; simpl; constructor; try congruence; try assumption.
Qed.

Lemma OnOne2i_map {A B} {P : nat -> B -> B -> Type} {i} {l l' : list A} (f : A -> B) :
  OnOne2i (fun i => on_Trel (P i) f) i l l' -> OnOne2i P i (map f l) (map f l').
Proof.
induction 1; simpl; constructor; try congruence; try assumption.
Qed.

Lemma OnOne2i_sym {A} (P : nat -> A -> A -> Type) i l l' : OnOne2i (fun i x y => P i y x) i l' l -> OnOne2i P i l l'.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma OnOne2i_exist {A} (P : nat -> A -> A -> Type) (Q : nat -> A -> A -> Type) i l l' :
  OnOne2i P i l l' ->
  (forall i x y, P i x y -> ∑ z, Q i x z × Q i y z) ->
  ∑ r, (OnOne2i Q i l r × OnOne2i Q i l' r).
Proof.
  intros H HPQ.
induction H.
  -
 destruct (HPQ _ _ _ p).
destruct p0.
    now exists (x :: tl); intuition constructor.
               -
 destruct IHOnOne2i as [r [? ?]].
                 now exists (hd :: r); intuition constructor.
Qed.


Lemma OnOne2i_ind_l :
  forall A (R : list A -> nat -> A -> A -> Type)
    (P : forall L i l l', OnOne2i (R L) i l l' -> Type),
    (forall L i x y l (r : R L i x y), P L i (x :: l) (y :: l) (OnOne2i_hd _ _ _ _ l r)) ->
    (forall L i x l l' (h : OnOne2i (R L) (S i) l l'),
        P L (S i) l l' h ->
        P L i (x :: l) (x :: l') (OnOne2i_tl _ i x _ _ h)
    ) ->
    forall i l l' h, P l i l l' h.
Proof.
  intros A R P hhd htl i l l' h.
induction h ; eauto.
Qed.

Lemma OnOne2i_impl_exist_and_All :
  forall A i (l1 l2 l3 : list A) R1 R2 R3,
    OnOne2i R1 i l1 l2 ->
    All2 R2 l3 l2 ->
    (forall i x x' y, R1 i x y -> R2 x' y -> ∑ z : A, R3 i x z × R2 x' z) ->
    ∑ l4, OnOne2i R3 i l1 l4 × All2 R2 l3 l4.
Proof.
  intros A i l1 l2 l3 R1 R2 R3 h1 h2 h.
  induction h1 in l3, h2 |- *.
  -
 destruct l3.
    +
 inversion h2.
    +
 inversion h2.
subst.
    specialize (h _ _ _ _ p X) as hh.
    destruct hh as [? [? ?]].
    eexists.
constructor.
      *
 constructor.
eassumption.
      *
 constructor ; eauto.
  -
 destruct l3.
    +
 inversion h2.
    +
 inversion h2.
subst.
    specialize (IHh1 _ X0).
destruct IHh1 as [? [? ?]].
    eexists.
constructor.
      *
 eapply OnOne2i_tl.
eassumption.
      *
 constructor ; eauto.
Qed.

Lemma OnOne2i_impl_exist_and_All_r :
  forall A i (l1 l2 l3 : list A) R1 R2 R3,
    OnOne2i R1 i l1 l2 ->
    All2 R2 l2 l3 ->
    (forall i x x' y, R1 i x y -> R2 y x' -> ∑ z : A, R3 i x z × R2 z x') ->
    ∑ l4, ( OnOne2i R3 i l1 l4 × All2 R2 l4 l3 ).
Proof.
  intros A i l1 l2 l3 R1 R2 R3 h1 h2 h.
  induction h1 in l3, h2 |- *.
  -
 destruct l3.
    +
 inversion h2.
    +
 inversion h2.
subst.
      specialize (h _ _ _ _ p X) as hh.
      destruct hh as [? [? ?]].
      eexists.
split.
      *
 constructor.
eassumption.
      *
 constructor ; eauto.
  -
 destruct l3.
    +
 inversion h2.
    +
 inversion h2.
subst.
      specialize (IHh1 _ X0).
destruct IHh1 as [? [? ?]].
      eexists.
split.
      *
 eapply OnOne2i_tl.
eassumption.
      *
 constructor ; eauto.
Qed.

Lemma OnOne2i_split :
  forall A (P : nat -> A -> A -> Type) i l l',
    OnOne2i P i l l' ->
    ∑ i x y u v,
      P i x y ×
      (l = u ++ x :: v /\
      l' = u ++ y :: v).
Proof.
  intros A P i l l' h.
  induction h.
  -
 exists i, hd, hd', [], tl.
    intuition eauto.
  -
 destruct IHh as [i' [x [y [u [v ?]]]]].
    exists i', x, y, (hd :: u), v.
    intuition eauto.
all: subst.
all: reflexivity.
Qed.

Lemma OnOne2i_impl {A} {P Q} {i} {l l' : list A} :
  OnOne2i P i l l' ->
  (forall i x y, P i x y -> Q i x y) ->
  OnOne2i Q i l l'.
Proof.
  induction 1; constructor; intuition eauto.
Qed.

Lemma OnOne2i_nth_error {A} (l l' : list A) i n t P :
  OnOne2i P i l l' ->
  nth_error l n = Some t ->
  ∑ t', (nth_error l' n = Some t') *
  ((t = t') + (P (i + n)%nat t t')).
Proof.
  induction 1 in n |- *.
  destruct n; simpl.
  -
 intros [= ->].
exists hd'; rewrite Nat.add_0_r; intuition auto.
  -
 exists t.
intuition auto.
  -
 destruct n; simpl; rewrite ?Nat.add_succ_r /=.
    intros [= ->].
exists t; intuition auto.
    apply IHX.
Qed.

Lemma OnOne2i_nth_error_r {A} i (l l' : list A) n t' P :
  OnOne2i P i l l' ->
  nth_error l' n = Some t' ->
  ∑ t, (nth_error l n = Some t) *
  ((t = t') + (P (i + n)%nat t t')).
Proof.
  induction 1 in n |- *.
  destruct n; simpl.
  -
 intros [= ->].
rewrite Nat.add_0_r; exists hd; intuition auto.
  -
 exists t'.
intuition auto.
  -
 destruct n; simpl; auto.
    intros [= ->].
exists t'; intuition auto.
    rewrite Nat.add_succ_r; apply IHX.
Qed.

Inductive OnOne2All {A B : Type} (P : B -> A -> A -> Type) : list B -> list A -> list A -> Type :=
| OnOne2All_hd b bs hd hd' tl : P b hd hd' -> #|bs| = #|tl| -> OnOne2All P (b :: bs) (hd :: tl) (hd' :: tl)
| OnOne2All_tl b bs hd tl tl' : OnOne2All P bs tl tl' -> OnOne2All P (b :: bs) (hd :: tl) (hd :: tl').
Derive Signature NoConfusion for OnOne2All.

Lemma OnOne2All_All_mix_left {A B} {P : B -> A -> A -> Type} {Q : A -> Type} {i l l'} :
  All Q l -> OnOne2All P i l l' -> OnOne2All (fun i x y => (P i x y * Q x)%type) i l l'.
Proof.
  intros H; induction 1; constructor; try inv H; intuition.
Qed.

Lemma OnOne2All_All2_mix_left {A B} {P : B -> A -> A -> Type} {Q : B -> A -> Type} {i l l'} :
  All2 Q i l -> OnOne2All P i l l' -> OnOne2All (fun i x y => (P i x y * Q i x)%type) i l l'.
Proof.
  intros a; induction 1; constructor; try inv a; intuition.
Qed.

Lemma OnOne2All_app {A B} (P : B -> A -> A -> Type) {i i' l tl tl'} :
  OnOne2All P i tl tl' ->
  #|i'| = #|l| ->
  OnOne2All P (i' ++ i) (l ++ tl) (l ++ tl').
Proof.
induction l in i, i' |- *; simpl; try constructor; eauto.
  destruct i' => //.
  intros.
destruct i' => //.
simpl.
constructor.
  eapply IHl; auto.
Qed.

Lemma OnOne2All_length {A B} {P} {i : list B} {l l' : list A} : OnOne2All P i l l' -> #|l| = #|l'|.
Proof.
induction 1; simpl; congruence.
Qed.

Lemma OnOne2All_length2 {A B} {P} {i : list B} {l l' : list A} : OnOne2All P i l l' -> #|i| = #|l|.
Proof.
induction 1; simpl; congruence.
Qed.

Lemma OnOne2All_mapP {A B I} {P} {i : list I} {l l' : list A} (f : A -> B) :
  OnOne2All (fun i => on_rel (P i) f) i l l' -> OnOne2All P i (map f l) (map f l').
Proof.
induction 1; simpl; constructor; try congruence; try assumption.
now rewrite map_length.
Qed.

Lemma OnOne2All_map {A I B} {P : I -> B -> B -> Type} {i : list I} {l l' : list A} (f : A -> B) :
  OnOne2All (fun i => on_Trel (P i) f) i l l' -> OnOne2All P i (map f l) (map f l').
Proof.
induction 1; simpl; constructor; try congruence; try assumption.
now rewrite map_length.
Qed.

Lemma OnOne2All_map_all {A B I I'} {P} {i : list I} {l l' : list A} (g : I -> I') (f : A -> B) :
  OnOne2All (fun i => on_Trel (P (g i)) f) i l l' -> OnOne2All P (map g i) (map f l) (map f l').
Proof.
induction 1; simpl; constructor; try congruence; try assumption.
now rewrite !map_length.
Qed.

Lemma OnOne2All_sym {A B} (P : B -> A -> A -> Type) i l l' : OnOne2All (fun i x y => P i y x) i l' l -> OnOne2All P i l l'.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma OnOne2All_exist {A B} (P : B -> A -> A -> Type) (Q : B -> A -> A -> Type) i l l' :
  OnOne2All P i l l' ->
  (forall i x y, P i x y -> ∑ z, Q i x z × Q i y z) ->
  ∑ r, (OnOne2All Q i l r × OnOne2All Q i l' r).
Proof.
  intros H HPQ.
induction H.
  -
 destruct (HPQ _ _ _ p).
destruct p0.
    now exists (x :: tl); intuition constructor.
               -
 destruct IHOnOne2All as [r [? ?]].
                 now exists (hd :: r); intuition constructor.
Qed.


Lemma OnOne2All_ind_l :
  forall A B (R : list A -> B -> A -> A -> Type)
    (P : forall L i l l', OnOne2All (R L) i l l' -> Type),
    (forall L b bs x y l (r : R L b x y) (len : #|bs| = #|l|),
      P L (b :: bs) (x :: l) (y :: l) (OnOne2All_hd _ _ _ _ _ l r len)) ->
    (forall L b bs x l l' (h : OnOne2All (R L) bs l l'),
        P L bs l l' h ->
        P L (b :: bs) (x :: l) (x :: l') (OnOne2All_tl _ _ _ x _ _ h)
    ) ->
    forall i l l' h, P l i l l' h.
Proof.
  intros A B R P hhd htl i l l' h.
induction h ; eauto.
Qed.

Lemma OnOne2All_impl_exist_and_All :
  forall A B (i : list B) (l1 l2 l3 : list A) R1 R2 R3,
    OnOne2All R1 i l1 l2 ->
    All2 R2 l3 l2 ->
    (forall i x x' y, R1 i x y -> R2 x' y -> ∑ z : A, R3 i x z × R2 x' z) ->
    ∑ l4, OnOne2All R3 i l1 l4 × All2 R2 l3 l4.
Proof.
  intros A B i l1 l2 l3 R1 R2 R3 h1 h2 h.
  induction h1 in l3, h2 |- *.
  -
 destruct l3.
    +
 inversion h2.
    +
 inversion h2.
subst.
    specialize (h _ _ _ _ p X) as hh.
    destruct hh as [? [? ?]].
    eexists.
constructor.
      *
 constructor; eassumption.
      *
 constructor ; eauto.
  -
 destruct l3.
    +
 inversion h2.
    +
 inversion h2.
subst.
    specialize (IHh1 _ X0).
destruct IHh1 as [? [? ?]].
    eexists.
constructor.
      *
 eapply OnOne2All_tl.
eassumption.
      *
 constructor ; eauto.
Qed.

Lemma OnOne2All_impl_exist_and_All_r :
  forall A B (i : list B) (l1 l2 l3 : list A) R1 R2 R3,
    OnOne2All R1 i l1 l2 ->
    All2 R2 l2 l3 ->
    (forall i x x' y, R1 i x y -> R2 y x' -> ∑ z : A, R3 i x z × R2 z x') ->
    ∑ l4, ( OnOne2All R3 i l1 l4 × All2 R2 l4 l3 ).
Proof.
  intros A B i l1 l2 l3 R1 R2 R3 h1 h2 h.
  induction h1 in l3, h2 |- *.
  -
 destruct l3.
    +
 inversion h2.
    +
 inversion h2.
subst.
      specialize (h _ _ _ _ p X) as hh.
      destruct hh as [? [? ?]].
      eexists.
split.
      *
 constructor; eassumption.
      *
 constructor ; eauto.
  -
 destruct l3.
    +
 inversion h2.
    +
 inversion h2.
subst.
      specialize (IHh1 _ X0).
destruct IHh1 as [? [? ?]].
      eexists.
split.
      *
 eapply OnOne2All_tl.
eassumption.
      *
 constructor ; eauto.
Qed.

Lemma OnOne2All_split :
  forall A B (P : B -> A -> A -> Type) i l l',
    OnOne2All P i l l' ->
    ∑ i x y u v,
      P i x y ×
      (l = u ++ x :: v /\
      l' = u ++ y :: v).
Proof.
  intros A B P i l l' h.
  induction h.
  -
 exists b, hd, hd', [], tl.
    intuition eauto.
  -
 destruct IHh as [i' [x [y [u [v ?]]]]].
    exists i', x, y, (hd :: u), v.
    intuition eauto.
all: subst.
all: reflexivity.
Qed.

Lemma OnOne2All_impl {A B} {P Q} {i : list B} {l l' : list A} :
  OnOne2All P i l l' ->
  (forall i x y, P i x y -> Q i x y) ->
  OnOne2All Q i l l'.
Proof.
  induction 1; constructor; intuition eauto.
Qed.

Lemma OnOne2All_nth_error {A B} {i : list B} (l l' : list A) n t P :
  OnOne2All P i l l' ->
  nth_error l n = Some t ->
  ∑ t', (nth_error l' n = Some t') *
  ((t = t') + (∑ i', (nth_error i n = Some i') * P i' t t')).
Proof.
  induction 1 in n |- *.
  destruct n; simpl.
  -
 intros [= ->].
exists hd'.
intuition auto.
now right; exists b.
  -
 intros hnth.
exists t; intuition auto.
  -
 destruct n; simpl; rewrite ?Nat.add_succ_r /=; auto.
    intros [= ->].
exists t; intuition auto.
Qed.

Lemma OnOne2All_nth_error_r {A B} (i : list B) (l l' : list A) n t' P :
  OnOne2All P i l l' ->
  nth_error l' n = Some t' ->
  ∑ t, (nth_error l n = Some t) *
  ((t = t') + (∑ i', (nth_error i n = Some i') * P i' t t')).
Proof.
  induction 1 in n |- *.
  destruct n; simpl.
  -
 intros [= ->].
exists hd; intuition auto.
    now right; exists b.
  -
 exists t'.
intuition auto.
  -
 destruct n; simpl; auto.
    intros [= ->].
exists t'; intuition auto.
Qed.

Lemma OnOne2All_impl_All_r {A B} (P : B -> A -> A -> Type) (Q : A -> Type) i l l' :
  (forall i x y, Q x -> P i x y -> Q y) ->
  OnOne2All P i l l' -> All Q l -> All Q l'.
Proof.
  intros HPQ.
  induction 1; intros H; depelim H; constructor; auto.
  now eapply HPQ.
Qed.

Lemma OnOne2All_nth_error_impl {A B} (P : A -> B -> B -> Type) il l l' :
  OnOne2All P il l l' ->
  OnOne2All (fun i x y => (∑ ni, nth_error il ni = Some i) × P i x y) il l l'.
Proof.
  induction 1.
  -
 econstructor => //.
    split => //.
    exists 0; reflexivity.
  -
 constructor.
eapply (OnOne2All_impl IHX).
    intros i x y [[ni hni] ?].
    split; auto.
exists (S ni).
apply hni.
Qed.

Lemma All2_Forall2 {A B} {P : A -> B -> Prop} {l l'} :
  All2 P l l' -> Forall2 P l l'.
Proof.
  induction 1; eauto.
Qed.


Lemma Forall2_All2 {A B} {P : A -> B -> Prop} l l' : Forall2 P l l' -> All2 P l l'.
Proof.
  intros f; induction l in l', f |- *; destruct l'; try constructor; auto.
  exfalso.
inv f.
  exfalso.
inv f.
  inv f; auto.
  apply IHl.
inv f; auto.
Qed.

Lemma All2_map_left_equiv {A B C} {P : A -> C -> Type} {l l'} {f : B -> A} :
  All2 (fun x y => P (f x) y) l l' <~> All2 P (map f l) l'.
Proof.
intros.
rewrite -{2}(map_id l').
eapply All2_map_equiv; eauto.
Qed.

Lemma All2_map_right_equiv {A B C} {P : A -> C -> Type} {l l'} {f : B -> C} :
  All2 (fun x y => P x (f y)) l l' <~> All2 P  l (map f l').
Proof.
intros.
rewrite -{2}(map_id l).
eapply All2_map_equiv; eauto.
Qed.

Lemma All2_map_left {A B C} {P : A -> C -> Type} {l l'} {f : B -> A} :
  All2 (fun x y => P (f x) y) l l' -> All2 P (map f l) l'.
Proof.
apply All2_map_left_equiv.
Qed.

Lemma All2_map_left' {A B  C} (P : A -> B -> Type) l l' (f : C -> A) :
  All2 P (map f l) l' -> All2 (fun x y => P (f x) y) l l'.
Proof.
intros.
rewrite - (map_id l') in X.
eapply All2_map_inv; eauto.
Qed.

Lemma All2_map_right {A B C} {P : A -> C -> Type} {l l'} {f : B -> C} :
  All2 (fun x y => P x (f y)) l l' -> All2 P l (map f l').
Proof.
apply All2_map_right_equiv.
Qed.

Definition All2_map_left_inv {A B C} {P : A -> C -> Type} {l l'} {f : B -> A} :
  All2 P (map f l) l' -> All2 (fun x y => P (f x) y) l l' := (snd All2_map_left_equiv).
Definition All2_map_right_inv {A B C} {P : A -> C -> Type} {l l'} {f : B -> C} :
  All2 P l (map f l') -> All2 (fun x y => P x (f y)) l l' := (snd All2_map_right_equiv).

Lemma All2_undep {A B R R' l l' a}
  : @All2 A B R' l l' <~> @All2_dep A B R (fun x y _ => R' x y) l l' a.
Proof.
  split; [ induction a; inversion 1 | induction 1 ]; constructor; subst; eauto.
Qed.

Lemma Forall2_undep {A B R R' l l' a}
  : @Forall2 A B R' l l' <-> @Forall2_dep A B R (fun x y _ => R' x y) l l' a.
Proof.
  split; [ induction a using Forall2_rect; inversion 1 | induction 1 ]; constructor; subst; eauto.
Qed.

Lemma All2_All2_mix {A B} {P Q : A -> B -> Type} l l' :
  All2 P l l' ->
  All2 Q l l' ->
  All2 (fun x y => P x y × Q x y) l l'.
Proof.
  induction 1; intros H; depelim H; constructor; auto.
Qed.

Lemma All2_mix {A} {P Q : A -> A -> Type} {l l'} :
  All2 P l l' -> All2 Q l l' -> All2 (fun x y => (P x y * Q x y))%type l l'.
Proof.
  induction 1; intros HQ; inv HQ; constructor; eauto.
Qed.

Lemma All2_mix_inv {A} {P Q : A -> A -> Type} {l l'} :
  All2 (fun x y => (P x y * Q x y))%type l l' ->
  (All2 P l l' * All2 Q l l').
Proof.
  induction 1; split; constructor; intuition eauto.
Qed.

Lemma All_reflect_reflect_All2 {A B} R (P : A -> B -> Type) (p : A -> B -> bool) l l' :
  All (fun x => forall y, R y -> reflectT (P x y) (p x y)) l ->
  All R l' ->
  reflectT (All2 P l l') (forallb2 p l l').
Proof.
  intros X' XP.
  apply equiv_reflectT; intro X.
  -
 apply All2_All_mix_left with (1 := X'), All2_All_mix_right with (1 := XP) in X.
    eapply All2_forallb2, All2_impl with (1 := X).
    move => x y [] [] H /H //.
  -
 apply forallb2_All2, All2_All_mix_left with (1 := X'), All2_All_mix_right with (1 := XP) in X.
    eapply All2_impl with (1 := X).
    move => x y [] [] H /H //.
Qed.

Lemma All2_reflect_reflect_All2 {A B} (P : A -> B -> Type) (p : A -> B -> bool) l l' :
  All2 (fun x y => reflectT (P x y) (p x y)) l l' ->
  reflectT (All2 P l l') (forallb2 p l l').
Proof.
  intro X'.
  apply equiv_reflectT; intro X.
  -
 apply All2_All2_mix with (1 := X') in X.
    eapply All2_forallb2, All2_impl with (1 := X).
    move => x y [] H /H //.
  -
 apply forallb2_All2, All2_All2_mix with (1 := X') in X.
    eapply All2_impl with (1 := X).
    move => x y [] H /H //.
Qed.

Lemma All3_Forall3 {A B C} {P : A -> B -> C -> Prop} {l l' l''} :
  All3 P l l' l'' -> Forall3 P l l' l''.
Proof.
  induction 1; auto.
Qed.


Lemma Forall3_All3 {A B C} {P : A -> B -> C -> Prop} l l' l'' : Forall3 P l l' l'' -> All3 P l l' l''.
Proof.
  intros f; induction l in l', l'', f |- *; destruct l', l''; try constructor; auto.
  1-6: exfalso; inv f.
  inv f; auto.
  apply IHl.
inv f; auto.
Qed.

Lemma All_map_eq {A B} {l} {f g : A -> B} :
  All (fun x => f x = g x) l ->
  map f l = map g l.
Proof.
  induction 1; simpl; trivial.
  now rewrite IHX p.
Qed.

Lemma All_map_id {A} {l} {f : A -> A} :
  All (fun x => f x = x) l ->
  map f l = l.
Proof.
  induction 1; simpl; trivial.
  now rewrite IHX p.
Qed.

Lemma forall_forallb_map_spec {A B : Type} {P : A -> Prop} {p : A -> bool}
      {l : list A} {f g : A -> B} :
    Forall P l -> is_true (forallb p l) ->
    (forall x : A, P x -> is_true (p x) -> f x = g x) -> map f l = map g l.
Proof.
  induction 1; simpl; trivial.
  rewrite andb_and.
intros [px pl] Hx.
  f_equal.
now apply Hx.
now apply IHForall.
Qed.

Lemma forall_forallb_forallb_spec {A : Type} {P : A -> Prop} {p : A -> bool}
      {l : list A} {f : A -> bool} :
    Forall P l -> is_true (forallb p l) ->
    (forall x : A, P x -> is_true (p x) -> is_true (f x)) -> is_true (forallb f l).
Proof.
  induction 1; simpl; trivial.
  rewrite !andb_and.
intros [px pl] Hx.
eauto.
Qed.

Lemma Forall_map {A B} (P : B -> Prop) (f : A -> B) l : Forall (fun x => P (f x)) l -> Forall P (map f l).
Proof.
  induction 1; constructor; auto.
Qed.

Lemma Forall_map_inv {A B} (P : B -> Prop) (f : A -> B) l : Forall P (map f l) -> Forall (fun x => P (f x)) l.
Proof.
induction l; intros Hf; inv Hf; try constructor; eauto.
Qed.

Lemma Forall_impl_Forall {A} {P Q : A -> Prop} {l} :
  Forall P l -> Forall (fun x => P x -> Q x) l -> Forall Q l.
Proof.
  induction 1; inversion 1; constructor; auto.
Qed.

Lemma Forall_impl {A} {P Q : A -> Prop} {l} :
  Forall P l -> (forall x, P x -> Q x) -> Forall Q l.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma Forall_app {A} (P : A -> Prop) l l' : Forall P (l ++ l') -> Forall P l /\ Forall P l'.
Proof.
  induction l; intros H.
split; try constructor.
apply H.
  inversion_clear H.
split; intuition auto.
Qed.

Lemma Forall_last {A} (P : A -> Prop) a l : l <> [] -> Forall P l -> P (last l a).
Proof.
  intros.
induction H0.
  -
 congruence.
  -
 destruct l.
    +
 cbn.
eauto.
    +
 cbn.
eapply IHForall.
congruence.
Qed.

Lemma All_safe_nth {A} {P : A -> Type} {Γ n} (isdecl : n < length Γ) : All P Γ ->
   P (safe_nth Γ (exist _ n isdecl)).
Proof.
  induction 1 in n, isdecl |- *.
  exfalso.
inversion isdecl.
  destruct n.
simpl.
auto.
  simpl in *.
eapply IHX.
Qed.

Definition size := nat.





Section All_size.
  Context {A} (P : A -> Type) (fn : forall x1, P x1 -> size).
  Fixpoint all_size {l1 : list A} (f : All P l1) : size :=
  match f with
  | All_nil => 0
  | All_cons px pl => fn _ px + all_size pl
  end.
End All_size.

Section Alli_size.
  Context {A} (P : nat -> A -> Type) (fn : forall n x1, P n x1 -> size).
  Fixpoint alli_size {l1 : list A} {n} (f : Alli P n l1) : size :=
  match f with
  | Alli_nil => 0
  | Alli_cons px pl => fn _ _ px + alli_size pl
  end.
End Alli_size.

Section All2_size.
  Context {A B} (P : A -> B -> Type) (fn : forall x1 x2, P x1 x2 -> size).
  Fixpoint all2_size {l1 l2} (f : All2 P l1 l2) : size :=
  match f with
  | All2_nil => 0
  | All2_cons rxy rll' => fn _ _ rxy + all2_size rll'
  end.
End All2_size.

Section All2i_size.
  Context {A B} (P : nat -> A -> B -> Type) (fn : forall i x1 x2, P i x1 x2 -> size).
  Fixpoint all2i_size {n l1 l2} (f : All2i P n l1 l2) : size :=
  match f with
  | All2i_nil => 0
  | All2i_cons rxy rll' => fn _ _ _ rxy + all2i_size rll'
  end.
End All2i_size.

Lemma All2i_impl {A B R R' n l l'} :
    @All2i A B R n l l' ->
    (forall i x y, R i x y -> R' i x y) ->
    All2i R' n l l'.
Proof.
  intros ha h.
  induction ha.
1: constructor.
  constructor.
2: assumption.
  eapply h.
assumption.
Qed.

Lemma All2_non_nil {A B} (P : A -> B -> Type) (l : list A) (l' : list B) :
  All2 P l l' -> l <> nil -> l' <> nil.
Proof.
  induction 1; congruence.
Qed.

Lemma nth_error_forall {A} {P : A -> Prop} {l : list A} {n x} :
  nth_error l n = Some x -> Forall P l -> P x.
Proof.
  intros Hnth HPl.
induction HPl in n, Hnth |- *.
destruct n; discriminate.
  revert Hnth.
destruct n.
now intros [= ->].
  intros H'; eauto.
Qed.

Lemma nth_error_all {A} {P : A -> Type} {l : list A} {n x} :
  nth_error l n = Some x -> All P l -> P x.
Proof.
  intros Hnth HPl.
  induction l in n, Hnth, HPl |- *.
destruct n; discriminate.
  destruct n; cbn in Hnth.
  -
 inversion Hnth.
subst.
inversion HPl.
eauto.
  -
 eapply IHl.
eassumption.
inversion HPl.
eassumption.
Defined.

Lemma nth_error_alli {A} {P : nat -> A -> Type} {l : list A} {n x} {k} :
  nth_error l n = Some x -> Alli P k l -> P (k + n) x.
Proof.
  intros Hnth HPl.
induction HPl in n, Hnth |- *.
  destruct n; discriminate.
  revert Hnth.
destruct n.
intros [= ->].
now rewrite Nat.add_0_r.
  intros H'; eauto.
rewrite <- Nat.add_succ_comm.
eauto.
Qed.

Lemma All_map_id' {A} {P : A -> Type} {l} {f} :
  All P l ->
  (forall x, P x -> f x = x) ->
  map f l = l.
Proof.
  induction 1; simpl; f_equal; intuition auto.
  f_equal; auto.
Qed.

Lemma Alli_mapi_spec {A B} {P : nat -> A -> Type} {l} {f g : nat -> A -> B} {n} :
  Alli P n l -> (forall n x, P n x -> f n x = g n x) ->
  mapi_rec f l n = mapi_rec g l n.
Proof.
  induction 1; simpl; trivial.
  intros Heq.
rewrite Heq; f_equal; auto.
Qed.

Lemma Alli_mapi_id {A} {P : nat -> A -> Type} {l} {f} {n} :
  Alli P n l ->
  (forall n x, P n x -> f n x = x) ->
  mapi_rec f l n = l.
Proof.
  induction 1; simpl; f_equal; intuition auto.
  f_equal; eauto.
Qed.

Lemma Alli_map_id {A} {P : nat -> A -> Type} {l} {f} {n} :
  Alli P n l ->
  (forall n x, P n x -> f x = x) ->
  map f l = l.
Proof.
  induction 1; simpl; f_equal; intuition auto.
  f_equal; eauto.
Qed.

Lemma forallb_map {A B} (f : A -> B) (l : list A) p :
  forallb p (map f l) = forallb (fun x => p (f x)) l.
Proof.
  induction l in p, f |- *; simpl; rewrite ?andb_and;
    intuition (f_equal; auto).
Qed.

Lemma forallb_mapi {A B} (f f' : nat -> A -> B) (g g' : B -> bool) l :
  (forall n x, nth_error l n = Some x -> g (f n x) = g' (f' n x)) ->
  forallb g (mapi f l) = forallb g' (mapi f' l).
Proof.
  unfold mapi.
  intros.
  assert
    (forall (n : nat) (x : A), nth_error l n = Some x -> g (f (0 + n) x) = g' (f' (0 + n) x)).
  {
 intros n x.
now apply H.
}
  clear H.
  revert H0.
  generalize 0.
  induction l; cbn; auto.
  intros n hfg.
f_equal.
specialize (hfg 0).
rewrite Nat.add_0_r in hfg.
now apply hfg.
  eapply IHl.
intros.
replace (S n + n0) with (n + S n0) by lia.
eapply hfg.
  now cbn.
Qed.

Lemma forallb_mapi_impl {A B} (f f' : nat -> A -> B) (g g' : B -> bool) l :
  (forall n x, nth_error l n = Some x -> g (f n x) -> g' (f' n x)) ->
  forallb g (mapi f l) -> forallb g' (mapi f' l).
Proof.
  unfold mapi.
  intros hfg.
  assert
    (forall (n : nat) (x : A), nth_error l n = Some x -> g (f (0 + n) x) -> g' (f' (0 + n) x)).
  {
 intros n x ?.
now apply hfg.
}
  clear hfg.
  revert H.
  generalize 0.
  induction l; cbn; auto.
  intros n hfg.
move/andP => [] hg hf.
  pose proof (hfg 0).
rewrite Nat.add_0_r in H.
apply H in hg => //.
rewrite hg /=.
  eapply IHl.
intros.
replace (S n + n0) with (n + S n0) by lia.
eapply hfg.
now cbn.
  now rewrite Nat.add_succ_r.
assumption.
Qed.

Lemma All_forallb' {A} P (l : list A) (p : A -> bool) :
  All P l ->
  (forall x, P x -> is_true (p x)) ->
  is_true (forallb p l).
Proof.
  induction 1 in p |- *; simpl; rewrite ?andb_and;
    intuition auto.
Qed.

Lemma forallb_Forall' {A} (P : A -> Prop) (l : list A) p :
  is_true (forallb p l) ->
  (forall x, is_true (p x) -> P x) ->
  Forall P l.
Proof.
  induction l in p |- *; simpl.
constructor.
  intros.
constructor; eauto; rewrite -> andb_and in H; intuition eauto.
Qed.

Lemma forallb_skipn {A} (p : A -> bool) n l :
  is_true (forallb p l) ->
  is_true (forallb p (skipn n l)).
Proof.
  induction l in n |- *; destruct n; simpl; try congruence.
  intros.
apply IHl.
rewrite -> andb_and in H; intuition.
Qed.

Lemma Forall_forallb_eq_forallb {A} (P : A -> Prop) (p q : A -> bool) l :
  Forall P l ->
  (forall x, P x -> p x = q x) ->
  forallb p l = forallb q l.
Proof.
  induction 1; simpl; intuition (f_equal; auto).
Qed.

Lemma forallb2_length {A B} (p : A -> B -> bool) l l' : is_true (forallb2 p l l') -> length l = length l'.
Proof.
  induction l in l' |- *; destruct l'; simpl; try congruence.
  rewrite !andb_and.
intros [Hp Hl].
erewrite IHl; eauto.
Qed.

Lemma map_option_Some X (L : list (option X)) t : map_option_out L = Some t -> All2 (fun x y => x = Some y) L t.
Proof.
  intros.
induction L in t, H |- *; cbn in *.
  -
 inv H.
econstructor.
  -
 destruct a.
destruct (map_option_out L).
all:inv H.
eauto.
Qed.

Lemma Alli_map_option_out_mapi_Some_spec {A B} (f g : nat -> A -> option B) l t P :
  Alli P 0 l ->
  (forall i x t, P i x -> f i x = Some t -> g i x = Some t) ->
  map_option_out (mapi f l) = Some t ->
  map_option_out (mapi g l) = Some t.
Proof.
  unfold mapi.
generalize 0.
  move => n Ha Hfg.
move: t.
  induction Ha; try constructor; auto.
  move=> t /=.
case E: (f n hd) => [b|]; try congruence.
  rewrite (Hfg n _ _ p E).
  case E' : map_option_out => [b'|]; try congruence.
  move=> [= <-].
now rewrite (IHHa _ E').
Qed.


Lemma All_mapi {A B} P f l k :
  Alli (fun i x => P (f i x)) k l -> All P (@mapi_rec A B f l k).
Proof.
  induction 1; simpl; constructor; auto.
Qed.

Lemma All_Alli {A} {P : A -> Type} {Q : nat -> A -> Type} {l n} :
  All P l ->
  (forall n x, P x -> Q n x) ->
  Alli Q n l.
Proof.
  intro H.
revert n.
induction H; constructor; eauto.
Qed.

Lemma All2_All_left_pack {A B} {P : A -> B -> Type} {l l'} :
  All2 P l l' -> Alli (fun i x => ∑ y, (nth_error l i = Some x /\ nth_error l' i = Some y) * P x y) 0 l.
Proof.
  intros HF.
induction HF; constructor; intuition eauto.
  exists y; intuition eauto.
clear -IHHF.
  revert IHHF.
generalize l at 1 3.
intros.
apply Alli_shift.
  now simpl.
Qed.

Lemma map_option_out_All {A} P (l : list (option A)) l' :
  (All (on_Some_or_None P) l) ->
  map_option_out l = Some l' ->
  All P l'.
Proof.
  induction 1 in l' |- *; cbn; inversion 1; subst; try constructor.
  destruct x; [|discriminate].
  case_eq (map_option_out l); [|intro e; rewrite e in H1; discriminate].
  intros l0 e; rewrite e in H1; inversion H1; subst.
  constructor; auto.
Qed.

Lemma Forall_forallb {A} P (l : list A) (p : A -> bool) :
  Forall P l ->
  (forall x, P x -> is_true (p x)) ->
  is_true (forallb p l).
Proof.
  induction 1 in p |- *; simpl; rewrite ?andb_and;
    intuition auto.
Qed.

Lemma Forall2_right {A B} (P : B -> Prop) (l : list A) (l' : list B) :
  Forall2 (fun x y => P y) l l' -> List.Forall (fun x => P x) l'.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma Forall2_non_nil {A B} (P : A -> B -> Prop) (l : list A) (l' : list B) :
  Forall2 P l l' -> l <> nil -> l' <> nil.
Proof.
  induction 1; congruence.
Qed.

Lemma Forall2_length {A B} {P : A -> B -> Prop} {l l'} : Forall2 P l l' -> #|l| = #|l'|.
Proof.
induction 1; simpl; auto.
Qed.

Lemma Forall2_triv {A B} {l : list A} {l' : list B} : #|l| = #|l'| -> Forall2 (fun _ _ => True) l l'.
Proof.
induction l in l' |- *; destruct l' => //=.
auto.
Qed.

Lemma Forall2_app_r {A} (P : A -> A -> Prop) l l' r r' : Forall2 P (l ++ [r]) (l' ++ [r']) ->
                                                         (Forall2 P l l') /\ (P r r').
Proof.
  induction l in l', r |- *; simpl; intros; destruct l'; simpl in *; inversion H; subst.
  -
 intuition.
  -
 destruct l'; cbn in *.
    +
 inversion H5.
    +
 inversion H5.
  -
 destruct l; cbn in *.
    +
 inversion H5.
    +
 inversion H5.
  -
 specialize (IHl _ _ H5).
intuition auto.
Qed.

Lemma Forall2_map_inv :
  forall {A B A' B'} (R : A' -> B' -> Prop) (f : A -> A')
    (g : B -> B') (l : list A) (l' : list B),
    Forall2 R (map f l) (map g l') ->
    Forall2 (fun x y => R (f x) (g y)) l l'.
Proof.
  intros A B A' B' R f g l l' h.
  induction l in l', h |- * ; destruct l' ; try solve [ inversion h ].
  -
 constructor.
  -
 constructor.
    +
 inversion h.
subst.
assumption.
    +
 eapply IHl.
inversion h.
assumption.
Qed.

Lemma Forall2_tip_l {A B} {R : A -> B -> Prop} x y : Forall2 R [x] y -> exists y', (y = [y']) /\ R x y'.
Proof.
  intros a; depelim a.
depelim a.
exists y0; split => //.
Qed.

Lemma All2_length {A B} {P : A -> B -> Type} {l l'} : All2 P l l' -> #|l| = #|l'|.
Proof.
induction 1; simpl; auto.
Qed.

Lemma All2_nth_error_None {A B} {P : A -> B -> Type} {l l'} n :
  All2 P l l' ->
  nth_error l n = None ->
  nth_error l' n = None.
Proof.
  intros Hall.
revert n.
  induction Hall; destruct n; simpl; try congruence.
auto.
Qed.

Lemma All2_app_inv_l : forall (A B : Type) (R : A -> B -> Type),
    forall l1 l2 r,
      All2 R (l1 ++ l2) r ->
      ∑ r1 r2,
        (r = r1 ++ r2)%list ×
        All2 R l1 r1 ×
        All2 R l2 r2.
Proof.
  intros.
revert l2 r X.
induction l1; intros; cbn in *.
  -
 exists [], r.
eauto.
  -
 depelim X.
    apply IHl1 in X as (?&?&?&?&?).
    subst.
    eexists _, _.
    split; [|split; eauto]; auto.
Qed.

Lemma All2_app_inv_r :
  forall A B R l r1 r2,
    @All2 A B R l (r1 ++ r2) ->
    ∑ l1 l2,
      (l = l1 ++ l2)%list ×
      All2 R l1 r1 ×
      All2 R l2 r2.
Proof.
  intros A B R l r1 r2 h.
  induction r1 in l, r1, r2, h |- *.
  -
 exists [], l; eauto.
  -
 depelim h.
    apply IHr1 in h as (?&?&?&?&?).
    subst.
    eexists _, _.
    split; [|split; eauto]; auto.
Qed.

Lemma All2_app_inv :
  forall A B (P : A -> B -> Type) l1 l2 r1 r2,
    #|l1| = #|r1| ->
    All2 P (l1 ++ l2) (r1 ++ r2) ->
    All2 P l1 r1 × All2 P l2 r2.
Proof.
  intros A B P l1 l2 r1 r2 e h.
  apply All2_app_inv_l in h as (w1&w2&e1&h1&h2).
  apply app_inj_length_l in e1 as (->&->); auto.
  apply All2_length in h1.
  apply All2_length in h2.
  congruence.
Qed.

Lemma All2_rect_rev : forall (A B : Type) (R : A -> B -> Type) (P : forall (l : list A) (l0 : list B), Type),
    P [] [] ->
    (forall (x : A) (y : B) (l : list A) (l' : list B) (r : R x y) (a : All2 R l l'),
        P l l' -> P (l ++ [x])%list (l' ++ [y]))%list ->
    forall (l : list A) (l0 : list B) (a : All2 R l l0), P l l0.
Proof.
  intros.
revert l0 a.
induction l using rev_ind; cbn; intros.
  -
 inv a.
eauto.
  -
 eapply All2_app_inv_l in a as (?&?&?&?&?).
subst.
    inv a0.
inv X2.
eauto.
Qed.

Lemma All2_ind_rev : forall (A B : Type) (R : A -> B -> Type) (P : forall (l : list A) (l0 : list B), Prop),
    P [] [] ->
    (forall (x : A) (y : B) (l : list A) (l' : list B) (r : R x y) (a : All2 R l l'),
        P l l' -> P (l ++ [x])%list (l' ++ [y]))%list ->
    forall (l : list A) (l0 : list B) (a : All2 R l l0), P l l0.
Proof.
  intros.
  eapply All2_rect_rev; eauto.
Qed.

Lemma All2_app :
  forall (A B : Type) (R : A -> B -> Type),
  forall l1 l2 l1' l2',
    All2 R l1 l1' ->
    All2 R l2 l2' ->
    All2 R (l1 ++ l2) (l1' ++ l2').
Proof.
  induction 1 ; cbn ; eauto.
Qed.

Lemma All2_rev (A B : Type) (P : A -> B -> Type) l l' :
  All2 P l l' ->
  All2 P (List.rev l) (List.rev l').
Proof.
  induction 1.
constructor.
  simpl.
eapply All2_app; auto.
Qed.

Lemma All_All2_flex {A B} (P : A -> Type) (Q : A -> B -> Type) l l' :
  All P l ->
  (forall x y, In y l' -> P x -> Q x y) ->
  length l' = length l ->
  All2 Q l l'.
Proof.
  intros H1 H2 Hl.
  induction H1 in l', H2, Hl |- *; destruct l'; depelim Hl.
  -
 econstructor.
  -
 econstructor; firstorder.
eapply IHAll; firstorder.
Qed.

Lemma All_All_All2 {A} (P Q : A -> Prop) l l' :
  All P l -> All Q l' -> #|l| = #|l'| -> All2 (fun x y => P x /\ Q y) l l'.
Proof.
  induction l in l' |- *; destruct l'; simpl; auto => //.
  intros ha hb.
specialize (IHl l'); depelim ha; depelim hb.
  constructor; auto.
Qed.

Lemma All2_impl_In {A B} {P Q : A -> B -> Type} {l l'} :
  All2 P l l' ->
  (forall x y, In x l -> In y l' -> P x y -> Q x y) ->
  All2 Q l l'.
Proof.
  revert l'.
induction l; intros; inversion X.
  -
 econstructor.
  -
 subst.
econstructor.
 eapply X0.
firstorder.
firstorder.
eauto.
    eapply IHl.
eauto.
intros.
    eapply X0.
now right.
now right.
eauto.
Qed.

Lemma Forall2_skipn A B (P : A -> B -> Prop) l l' n:
  Forall2 P l l' -> Forall2 P (skipn n l) (skipn n l').
Proof.
  revert l l'; induction n; intros.
  -
 unfold skipn.
eauto.
  -
 cbv [skipn].
fold (@skipn A n).
fold (@skipn B n).
    inversion H; subst.
econstructor.
    eauto.
Qed.

Lemma Forall2_nth_error_Some {A B} {P : A -> B -> Prop} {l l'} n t :
  Forall2 P l l' ->
  nth_error l n = Some t ->
  exists t' : B, (nth_error l' n = Some t') /\ P t t'.
Proof.
  intros Hall.
revert n.
  induction Hall; destruct n; simpl; try congruence.
intros [= ->].
exists y.
intuition auto.
  eauto.
Qed.

Lemma Forall2_impl {A B} {P Q : A -> B -> Prop} {l l'} :
    Forall2 P l l' ->
    (forall x y, P x y -> Q x y) ->
    Forall2 Q l l'.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma app_Forall :
  forall A P (l1 l2 : list A),
    Forall P l1 ->
    Forall P l2 ->
    Forall P (l1 ++ l2).
Proof.
  intros A P l1 l2 h1 h2.
  revert l2 h2.
  induction h1 ; intros l2 h2.
  -
 assumption.
  -
 cbn.
constructor ; try assumption.
    eapply IHh1.
assumption.
Qed.

Lemma rev_Forall :
  forall A P l,
    Forall P l ->
    Forall P (@List.rev A l).
Proof.
  intros A P l h.
  induction l.
  -
 cbn.
constructor.
  -
 cbn.
inversion h; subst.
    specialize (IHl ltac:(assumption)).
    eapply app_Forall ; try assumption.
    repeat constructor.
assumption.
Qed.

Lemma Forall2_impl' {A B} {P Q : A -> B -> Prop} {l l'} :
    Forall2 P l l' ->
    Forall (fun x => forall y, P x y -> Q x y) l ->
    Forall2 Q l l'.
Proof.
  induction 1; constructor;
    inversion H1; intuition.
Qed.

Lemma Forall2_Forall {A R l} : @Forall2 A A R l l -> Forall (fun x => R x x) l.
Proof.
  induction l.
constructor.
  inversion 1; constructor; intuition.
Qed.

Lemma All2_All {A R l} : @All2 A A R l l -> All (fun x => R x x) l.
Proof.
  induction l.
constructor.
  inversion 1; constructor; intuition.
Qed.

Lemma Forall_Forall2 {A R l} : Forall (fun x => R x x) l -> @Forall2 A A R l l.
Proof.
  induction l.
constructor.
  inversion 1; constructor; intuition.
Qed.

Lemma Forall_True {A} {P : A -> Prop} l : (forall x, P x) -> Forall P l.
Proof.
  intro H.
induction l; now constructor.
Qed.

Lemma Forall2_True {A B} {R : A -> B -> Prop} l l'
  : (forall x y, R x y) -> #|l| = #|l'| -> Forall2 R l l'.
Proof.
  intro H.
revert l'; induction l; simpl;
    intros [] e; try discriminate e; constructor.
  easy.
  apply IHl.
now apply eq_add_S.
Qed.

Lemma Forall2_map {A B A' B'} (R : A' -> B' -> Prop) (f : A -> A') (g : B -> B') l l'
  : Forall2 (fun x y => R (f x) (g y)) l l' -> Forall2 R (map f l) (map g l').
Proof.
  induction 1; constructor; auto.
Qed.

Lemma Forall2_map_right {A B C} (P : A -> B -> Prop) (f : C -> B) (l : list A) (l' : list C) :
  Forall2 P l (map f l') <-> Forall2 (fun x y => P x (f y)) l l'.
Proof.
  split; intros.
  +
 eapply Forall2_map_inv.
now rewrite map_id.
  +
 rewrite -(map_id l).
now eapply Forall2_map.
Qed.

Lemma Forall2_and {A B} (R R' : A -> B -> Prop) l l'
  : Forall2 R l l' -> Forall2 R' l l' -> Forall2 (fun x y => R x y /\ R' x y) l l'.
Proof.
  induction 1.
  intro; constructor.
  inversion_clear 1.
  constructor; intuition.
Defined.

Lemma Forall_Forall2_and {A B} {R : A -> B -> Prop} {P l l'}
  : Forall2 R l l' -> Forall P l -> Forall2 (fun x y => P x /\ R x y) l l'.
Proof.
  induction 1.
  intro; constructor.
  inversion_clear 1.
  constructor; intuition.
Defined.

Lemma Forall_Forall2_and' {A B} {R : A -> B -> Prop} {P l l'}
  : Forall2 R l l' -> Forall P l' -> Forall2 (fun x y => R x y /\ P y) l l'.
Proof.
  induction 1.
  intro; constructor.
  inversion_clear 1.
  constructor; intuition.
Defined.

Lemma Forall2_nth :
  forall A B P l l' n (d : A) (d' : B),
    Forall2 P l l' ->
    P d d' ->
    P (nth n l d) (nth n l' d').
Proof.
  intros A B P l l' n d d' h hd.
  induction n in l, l', h |- *.
  -
 destruct h.
    +
 assumption.
    +
 assumption.
  -
 destruct h.
    +
 assumption.
    +
 simpl.
apply IHn.
assumption.
Qed.

Lemma Forall2_nth_error_Some_l :
  forall A B (P : A -> B -> Prop) l l' n t,
    nth_error l n = Some t ->
    Forall2 P l l' ->
    exists t',
      nth_error l' n = Some t' /\
      P t t'.
Proof.
  intros A B P l l' n t e h.
  induction n in l, l', t, e, h |- *.
  -
 destruct h.
    +
 cbn in e.
discriminate.
    +
 cbn in e.
inversion e.
subst.
      exists y.
split ; auto.
  -
 destruct h.
    +
 cbn in e.
discriminate.
    +
 cbn in e.
apply IHn with (l' := l') in e ; assumption.
Qed.

Lemma Forall2_nth_error_Some_r :
  forall A B (P : A -> B -> Prop) l l' n t,
    nth_error l' n = Some t ->
    Forall2 P l l' ->
    exists t',
      nth_error l n = Some t' /\
      P t' t.
Proof.
  intros A B P l l' n t e h.
  induction n in l, l', t, e, h |- *.
  -
 destruct h.
    +
 cbn in e.
discriminate.
    +
 cbn in e.
inversion e.
subst.
      exists x.
split ; auto.
  -
 destruct h.
    +
 cbn in e.
discriminate.
    +
 cbn in e.
apply IHn with (l := l) in e ; assumption.
Qed.

Lemma Forall2_nth_error_None_l :
  forall A B (P : A -> B -> Prop) l l' n,
    nth_error l n = None ->
    Forall2 P l l' ->
    nth_error l' n = None.
Proof.
  intros A B P l l' n e h.
  induction n in l, l', e, h |- *.
  -
 destruct h.
    +
 reflexivity.
    +
 cbn in e.
discriminate e.
  -
 destruct h.
    +
 reflexivity.
    +
 cbn in e.
cbn.
eapply IHn ; eauto.
Qed.

Lemma Forall2_trans :
  forall A (P : A -> A -> Prop),
    RelationClasses.Transitive P ->
    RelationClasses.Transitive (Forall2 P).
Proof.
  intros A P hP l1 l2 l3 h1 h2.
  induction h1 in l3, h2 |- *.
  -
 inversion h2.
constructor.
  -
 inversion h2.
constructor.
    +
 eapply hP ; eauto.
    +
 eapply IHh1 ; eauto.
Qed.

Lemma Forall2_rev :
  forall A B R l l',
    @Forall2 A B R l l' ->
    Forall2 R (List.rev l) (List.rev l').
Proof.
  intros A B R l l' h.
  induction h.
  -
 constructor.
  -
 cbn.
eapply Forall2_app ; eauto.
Qed.


Lemma Forall2_mapi :
  forall A B A' B' (R : A' -> B' -> Prop) (f : nat -> A -> A') (g : nat -> B -> B') l l',
    Forall2 (fun x y => forall i, R (f i x) (g i y)) l l' ->
    Forall2 R (mapi f l) (mapi g l').
Proof.
  intros A B A' B' R f g l l' h.
  unfold mapi.
generalize 0.
intro i.
  induction h in i |- *.
  -
 constructor.
  -
 cbn.
constructor ; eauto.
Qed.

Lemma All2_trans {A} (P : A -> A -> Type) :
  CRelationClasses.Transitive P ->
  CRelationClasses.Transitive (All2 P).
Proof.
  intros HP x y z H.
induction H in z |- *.
  intros Hyz.
inv Hyz.
constructor.
  intros Hyz.
inv Hyz.
constructor; auto.
  now transitivity y.
Qed.

Lemma All2_trans' {A B C}
      (P : A -> B -> Type) (Q : B -> C -> Type) (R : A -> C -> Type)
      (H : forall x y z, P x y × Q y z -> R x z) {l1 l2 l3}
  : All2 P l1 l2 -> All2 Q l2 l3 -> All2 R l1 l3.
Proof.
  induction 1 in l3 |- *.
  -
 inversion 1; constructor.
  -
 inversion 1; subst.
constructor; eauto.
Qed.

Lemma All2_nth :
  forall A B P l l' n (d : A) (d' : B),
    All2 P l l' ->
    P d d' ->
    P (nth n l d) (nth n l' d').
Proof.
  intros A B P l l' n d d' h hd.
  induction n in l, l', h |- *.
  -
 destruct h.
    +
 assumption.
    +
 assumption.
  -
 destruct h.
    +
 assumption.
    +
 simpl.
apply IHn.
assumption.
Qed.

Lemma All2_mapi :
  forall A B A' B' (R : A' -> B' -> Type) (f : nat -> A -> A') (g : nat -> B -> B') l l',
    All2 (fun x y => forall i, R (f i x) (g i y)) l l' ->
    All2 R (mapi f l) (mapi g l').
Proof.
  intros A B A' B' R f g l l' h.
  unfold mapi.
generalize 0.
intro i.
  induction h in i |- *.
  -
 constructor.
  -
 cbn.
constructor ; eauto.
Qed.

Lemma All2_skipn :
  forall A B R l l' n,
    @All2 A B R l l' ->
    @All2 A B R (skipn n l) (skipn n l').
Proof.
  intros A B R l l' n h.
  induction h in n |- *.
  all: destruct n ; try econstructor ; eauto.
Qed.

Lemma All2_right_triv {A B} {l : list A} {l' : list B} P :
  All P l' -> #|l| = #|l'| -> All2 (fun _ b => P b) l l'.
Proof.
  induction 1 in l |- *.
  all: cbn.
  all: intros.
  all: destruct l.
  all: cbn in *.
  all: try (exfalso ; lia).
  all: try solve [ econstructor; eauto ].
Qed.

Lemma All_repeat {A} {n P} x :
  P x -> @All A P (repeat x n).
Proof.
  induction n; cbn; econstructor; eauto.
Qed.

Lemma Forall2_Forall_right {A B} {P : A -> B -> Prop} {Q : B -> Prop} {l l'} :
  Forall2 P l l' ->
  (forall x y, P x y -> Q y) ->
  Forall Q l'.
Proof.
  intros HF H.
induction HF; constructor; eauto.
Qed.

Lemma All2_from_nth_error A B L1 L2 (P : A -> B -> Type) :
  #|L1| = #|L2| ->
                (forall n x1 x2, n < #|L1| -> nth_error L1 n = Some x1
                                      -> nth_error L2 n = Some x2
                                      -> P x1 x2) ->
                All2 P L1 L2.
Proof.
  revert L2; induction L1; cbn; intros.
  -
 destruct L2; inv H.
econstructor.
  -
 destruct L2; inversion H.
econstructor.
    eapply (X 0); cbn; eauto.
lia.
    eapply IHL1.
eauto.
    intros.
eapply (X (S n)); cbn; eauto.
lia.
Qed.

Lemma All2_nth_error {A B} {P : A -> B -> Type} {l l'} n t t' :
  All2 P l l' ->
  nth_error l n = Some t ->
  nth_error l' n = Some t' ->
  P t t'.
Proof.
  intros Hall.
revert n.
  induction Hall; destruct n; simpl; try congruence.
  eauto.
Defined.

Lemma All2_dep_from_nth_error A B L1 L2 (P : A -> B -> Type) (P' : forall a b, P a b -> Type) (H : All2 P L1 L2) :
  (forall n x1 x2 (_ : n < #|L1|)
          (H1 : nth_error L1 n = Some x1)
          (H2 : nth_error L2 n = Some x2),
      P' x1 x2 (All2_nth_error n x1 x2 H H1 H2)) ->
  All2_dep P' H.
Proof.
  induction H; cbn; intro H'; constructor.
  {
 specialize (H' 0 _ _ ltac:(lia) eq_refl eq_refl); cbn in H'.
    exact H'.
}
  {
 apply IHAll2; intros n x1 x2 Hn H1 H2.
    specialize (H' (S n) _ _ ltac:(lia) H1 H2); cbn in H'.
    exact H'.
}
Qed.

Lemma All2_dep_nth_error {A B} {P : A -> B -> Type} {P' : forall a b, P a b -> Type} {l l'} n t t' {H : All2 P l l'}
  (H' : All2_dep P' H)
  (H1 : nth_error l n = Some t)
  (H2 : nth_error l' n = Some t') :
  P' t t' (All2_nth_error n t t' H H1 H2).
Proof.
  generalize dependent n; induction H'; destruct n; cbn; try congruence.
  {
 intros H1 H2.
    set (k := f_equal _ H1); clearbody k; cbn in k; clear H1; subst.
    set (k := f_equal _ H2); clearbody k; cbn in k; clear H2; subst.
    cbn.
    assumption.
}
  {
 exact (IHH' _).
}
Qed.

Lemma Forall2_from_nth_error A B L1 L2 (P : A -> B -> Prop) :
  #|L1| = #|L2| ->
                (forall n x1 x2, n < #|L1| -> nth_error L1 n = Some x1
                                      -> nth_error L2 n = Some x2
                                      -> P x1 x2) ->
                Forall2 P L1 L2.
Proof.
  revert L2; induction L1; cbn; intros.
  -
 destruct L2; inv H.
econstructor.
  -
 destruct L2; inversion H.
econstructor.
    eapply (H0 0); cbn; eauto.
lia.
    eapply IHL1.
eauto.
    intros.
eapply (H0 (S n)); cbn; eauto.
lia.
Qed.

Lemma Forall2_nth_error {A B} {P : A -> B -> Prop} {l l'} n t t' :
  Forall2 P l l' ->
  nth_error l n = Some t ->
  nth_error l' n = Some t' ->
  P t t'.
Proof.
  intros Hall.
revert n.
  induction Hall; destruct n; simpl; try congruence.
  eauto.
Defined.

Lemma Forall2_dep_from_nth_error A B L1 L2 (P : A -> B -> Prop) (P' : forall a b, P a b -> Prop) (H : Forall2 P L1 L2) :
  (forall n x1 x2 (_ : n < #|L1|)
          (H1 : nth_error L1 n = Some x1)
          (H2 : nth_error L2 n = Some x2),
      P' x1 x2 (Forall2_nth_error n x1 x2 H H1 H2)) ->
  Forall2_dep P' H.
Proof.
  induction H using Forall2_rect; cbn; intro H'; constructor.
  {
 specialize (H' 0 _ _ ltac:(lia) eq_refl eq_refl); cbn in H'.
    exact H'.
}
  {
 apply IHForall2; intros n x1 x2 Hn H1 H2.
    specialize (H' (S n) _ _ ltac:(lia) H1 H2); cbn in H'.
    exact H'.
}
Qed.

Lemma Forall2_dep_nth_error {A B} {P : A -> B -> Prop} {P' : forall a b, P a b -> Prop} {l l'} n t t' {H : Forall2 P l l'}
  (H' : Forall2_dep P' H)
  (H1 : nth_error l n = Some t)
  (H2 : nth_error l' n = Some t') :
  P' t t' (Forall2_nth_error n t t' H H1 H2).
Proof.
  generalize dependent n; induction H'; destruct n; cbn; try congruence.
  {
 intros H1 H2.
    set (k := f_equal _ H1); clearbody k; cbn in k; clear H1; subst.
    set (k := f_equal _ H2); clearbody k; cbn in k; clear H2; subst.
    cbn.
    assumption.
}
  {
 exact (IHH' _).
}
Qed.
Import MetaCoq.Utils.MCSquash.

Lemma All2_swap :
  forall A B R l l',
    @All2 A B R l l' ->
    All2 (fun x y => R y x) l' l.
Proof.
  intros A B R l l' h.
  induction h ; eauto.
Qed.

Lemma All2_firstn :
  forall A B R l l' n,
    @All2 A B R l l' ->
    @All2 A B R (firstn n l) (firstn n l').
Proof.
  intros A B R l l' n h.
  induction h in n |- *.
  all: destruct n ; try econstructor ; eauto.
Qed.

Lemma All2_impl' {A B} {P Q : A -> B -> Type} {l : list A} {l' : list B}
  : All2 P l l' -> All (fun x => forall y, P x y -> Q x y) l -> All2 Q l l'.
Proof.
  induction 1.
constructor.
  intro XX; inv XX.
  constructor; auto.
Defined.

Lemma All_All2 {A} {P : A -> A -> Type} {Q} {l : list A} :
  All Q l ->
  (forall x, Q x -> P x x) ->
  All2 P l l.
Admitted.


Lemma All2_nth_error_Some {A B} {P : A -> B -> Type} {l l'} n t :
  All2 P l l' ->
  nth_error l n = Some t ->
  { t' : B & (nth_error l' n = Some t') * P t t'}%type.
Admitted.

Lemma All2_nth_error_Some_r {A B} {P : A -> B -> Type} {l l'} n t' :
  All2 P l l' ->
  nth_error l' n = Some t' ->
  ∑ t, nth_error l n = Some t × P t t'.
Admitted.

Lemma All2_same {A} {P : A -> A -> Type} l : (forall x, P x x) -> All2 P l l.
Admitted.

Lemma All2_prod {A B} P Q (l : list A) (l' : list B) : All2 P l l' -> All2 Q l l' -> All2 (Trel_conj P Q) l l'.
Proof.
  induction 1; inversion 1; subst; auto.
Defined.

Lemma All2_prod_inv :
  forall A B (P : A -> B -> Type) Q l l',
    All2 (Trel_conj P Q) l l' ->
    All2 P l l' × All2 Q l l'.
Admitted.

Lemma All2_sym {A} (P : A -> A -> Type) l l' :
  All2 P l l' -> All2 (fun x y => P y x) l' l.
Admitted.

Lemma All2_symP {A} (P : A -> A -> Type) :
  CRelationClasses.Symmetric P ->
  CRelationClasses.Symmetric (All2 P).
Admitted.

Lemma Forall2_symP {A} (P : A -> A -> Prop) :
  RelationClasses.Symmetric P ->
  RelationClasses.Symmetric (Forall2 P).
Admitted.

Lemma All_All2_All2_mix {A B} (P : B -> B -> Type) (Q R : A -> B -> Type) l l' l'' :
  All (fun x => forall y z, Q x y -> R x z -> ∑ v, P y v * P z v) l -> All2 Q l l' -> All2 R l l'' ->
  ∑ l''', All2 P l' l''' * All2 P l'' l'''.
Admitted.

Lemma All2_nth_error_Some_right {A} {P : A -> A -> Type} {l l'} n t :
  All2 P l l' ->
  nth_error l' n = Some t ->
  { t' : A & (nth_error l n = Some t') * P t' t}%type.
Admitted.

Lemma All_forallb_map_spec {A B : Type} {P : A -> Type} {p : A -> bool}
      {l : list A} {f g : A -> B} :
    All P l -> forallb p l ->
    (forall x : A, P x -> p x -> f x = g x) -> map f l = map g l.
Admitted.

Lemma All_forallb_forallb_spec {A : Type} {P : A -> Type} {p : A -> bool}
      {l : list A} {f : A -> bool} :
    All P l -> forallb p l ->
    (forall x : A, P x -> p x -> f x) -> forallb f l.
Admitted.

Lemma All_forallb_eq_forallb {A} (P : A -> Type) (p q : A -> bool) l :
  All P l ->
  (forall x, P x -> p x = q x) ->
  forallb p l = forallb q l.
Admitted.

Lemma forallb_nth {A} (l : list A) (n : nat) P d :
  forallb P l -> n < #|l| -> exists x, (nth n l d = x) /\ P x.
Admitted.

Lemma forallb_nth' {A} {l : list A} {P} n d :
  forallb P l -> {exists x, (nth n l d = x) /\ P x} + {nth n l d = d}.
Admitted.

Lemma forallb_impl {A} (p q : A -> bool) l :
  (forall x, In x l -> p x -> q x) -> forallb p l -> forallb q l.
Admitted.

Lemma forallb_iff {A} (p q : A -> bool) l :
  (forall x, In x l -> p x <-> q x) -> forallb p l = forallb q l.
Admitted.

Lemma All2_eq :
  forall A (l l' : list A),
    All2 eq l l' ->
    l = l'.
Admitted.

Lemma All_prod_inv :
  forall A P Q l,
    All (fun x : A => P x × Q x) l ->
    All P l × All Q l.
Admitted.

Lemma All_pair {A} (P Q : A -> Type) l :
  All (fun x => P x × Q x) l <~> (All P l × All Q l).
Admitted.

Lemma All_prod :
  forall A P Q l,
    All P l ->
    All Q l ->
    All (fun x : A => P x × Q x) l.
Admitted.

Lemma All2i_mapi :
  forall A B C D R f g l l',
    @All2i A B (fun i x y => R i (f i x) (g i y)) 0 l l' ->
    @All2i C D R 0 (mapi f l) (mapi g l').
Admitted.

Lemma All2i_app :
  forall A B R n l1 l2 r1 r2,
    @All2i A B R n l1 r1 ->
    All2i R (n + #|l1|) l2 r2 ->
    All2i R n (l1 ++ l2) (r1 ++ r2).
Admitted.



Lemma All2i_mapi_rec {A B C D} (R : nat -> A -> B -> Type)
      (l : list C) (l' : list D) (f : nat -> C -> A) (g : nat -> D -> B) n :
  All2i (fun n x y => R n (f n x) (g n y)) n l l' ->
  All2i R n (mapi_rec f l n) (mapi_rec g l' n).
Admitted.

Lemma All2i_trivial {A B} (R : nat -> A -> B -> Type) (H : forall n x y, R n x y) n l l' :
  #|l| = #|l'| -> All2i R n l l'.
Admitted.

Lemma All2i_rev :
  forall A B R l l' n,
    @All2i A B R n l l' ->
    All2i (fun i x y => R (n + #|l| - (S i)) x y) 0 (List.rev l) (List.rev l').
Admitted.

Section All2i_len.

  

  Hint Constructors All2i : pcuic.

  Inductive All2i_len {A B : Type} (R : nat -> A -> B -> Type) : list A -> list B -> Type :=
    All2i_len_nil : All2i_len R [] []
  | All2i_len_cons : forall (x : A) (y : B) (l : list A) (l' : list B),
          R (List.length l) x y -> All2i_len R l l' -> All2i_len R (x :: l) (y :: l').
  Hint Constructors All2i_len : core pcuic.

  Lemma All2i_len_app {A B} (P : nat -> A -> B -> Type) l0 l0' l1 l1' :
    All2i_len P l0' l1' ->
    All2i_len (fun n => P (n + #|l0'|)) l0 l1 ->
    All2i_len P (l0 ++ l0') (l1 ++ l1').
Admitted.

  Lemma All2i_len_length {A B} (P : nat -> A -> B -> Type) l l' :
    All2i_len P l l' -> #|l| = #|l'|.
Admitted.

  Lemma All2i_len_impl {A B} (P Q : nat -> A -> B -> Type) l l' :
    All2i_len P l l' -> (forall n x y, P n x y -> Q n x y) -> All2i_len Q l l'.
Admitted.

  Lemma All2i_len_rev {A B} (P : nat -> A -> B -> Type) l l' :
    All2i_len P l l' ->
    All2i_len (fun n => P (#|l| - S n)) (List.rev l) (List.rev l').
Admitted.

  Lemma All2i_rev_ctx {A B} (R : nat -> A -> B -> Type) (n : nat) (l : list A) (l' : list B) :
    All2i_len R l l' -> All2i R 0 (List.rev l) (List.rev l').
Admitted.

  Lemma All2i_rev_ctx_gen {A B} (R : nat -> A -> B -> Type) (n : nat) (l : list A) (l' : list B) :
    All2i R n l l' -> All2i_len (fun m => R (n + m)) (List.rev l) (List.rev l').
Admitted.

  Lemma All2i_rev_ctx_inv {A B} (R : nat -> A -> B -> Type) (l : list A) (l' : list B) :
    All2i R 0 l l' -> All2i_len R (List.rev l) (List.rev l').
Admitted.

End All2i_len.

Lemma All_sq {A} {P : A -> Type} {l}
  : All (fun x => ∥ P x ∥) l -> ∥ All P l ∥.
Admitted.

Lemma All2_sq {A B} {R : A -> B -> Type} {l1 l2}
  : All2 (fun x y => ∥ R x y ∥) l1 l2 -> ∥ All2 R l1 l2 ∥.
Admitted.

Lemma All_All2_refl {A : Type} {R} {l : list A} :
  All (fun x : A => R x x) l -> All2 R l l.
Admitted.

Lemma All2_app_r {A} (P : A -> A -> Type) l l' r r' :
  All2 P (l ++ [r]) (l' ++ [r']) -> (All2 P l l') * (P r r').
Admitted.

Lemma Forall2_eq {A} l l'
  : @Forall2 A A eq l l' -> l = l'.
Admitted.

Lemma Forall2_map' {A B A' B'} (R : A' -> B' -> Prop) (f : A -> A') (g : B -> B') l l'
  : Forall2 R (map f l) (map g l') -> Forall2 (fun x y => R (f x) (g y)) l l'.
Admitted.

Lemma Forall2_same :
  forall A (P : A -> A -> Prop) l,
    (forall x, P x x) ->
    Forall2 P l l.
Admitted.

Lemma Forall2_sym :
  forall A B (P : A -> B -> Prop) l l',
    Forall2 P l l' ->
    Forall2 (fun x y => P y x) l' l.
Admitted.

Lemma forallb2_Forall2 :
  forall A B (p : A -> B -> bool) l l',
    forallb2 p l l' ->
    Forall2 (fun x y => p x y) l l'.
Admitted.

Lemma forallb2P {A B} (P : A -> B -> Prop) (p : A -> B -> bool) l l' :
  (forall x y, reflect (P x y) (p x y)) ->
  reflect (Forall2 P l l') (forallb2 p l l').
Admitted.

Lemma forallb3_Forall3 :
  forall A B C (p : A -> B -> C -> bool) l l' l'',
    forallb3 p l l' l'' ->
    Forall3 (fun x y z => p x y z) l l' l''.
Admitted.

Lemma forallb3P {A B C} (P : A -> B -> C -> Prop) (p : A -> B -> C -> bool) l l' l'' :
  (forall x y z, reflect (P x y z) (p x y z)) ->
  reflect (Forall3 P l l' l'') (forallb3 p l l' l'').
Admitted.



Lemma All2_In {A B} (P : A -> B -> Type) l l' x : In x l ->
  All2 P l l' -> ∥ ∑ x', P x x' ∥.
Admitted.

Lemma All2_In_right {A B} (P : A -> B -> Type) l l' x' : In x' l' ->
  All2 P l l' -> ∥ ∑ x, P x x' ∥.
Admitted.

Lemma All_In {A} (P : A -> Type) l x : In x l ->
  All P l -> ∥ P x ∥.
Admitted.

Lemma In_Forall {A} {P : A -> Prop} l :
  (forall x, In x l -> P x) ->
  Forall P l.
Admitted.

Lemma All_forall {X Y} (f:X->Y->Prop) xs:
  All (fun a => forall b, f a b) xs ->
  (forall b, All (fun a => f a b) xs).
Admitted.

Lemma All2i_map {A B C D} (R : nat -> C -> D -> Type) (f : A -> C) (g : B -> D) n l l' :
  All2i (fun i x y => R i (f x) (g y)) n l l' -> All2i R n (map f l) (map g l').
Admitted.

Lemma All2i_map_right {B C D} (R : nat -> C -> D -> Type) (g : B -> D) n l l' :
  All2i (fun i x y => R i x (g y)) n l l' -> All2i R n l (map g l').
Admitted.

Lemma All2i_nth_impl_gen {A B} (R : nat -> A -> B -> Type) n l l' :
  All2i R n l l' ->
  All2i (fun i x y =>
    (if i <? n then False
    else nth_error l (i - n) = Some x) × R i x y) n l l'.
Admitted.

Lemma All2i_nth_hyp {A B} (R : nat -> A -> B -> Type) l l' :
  All2i R 0 l l' ->
  All2i (fun i x y => nth_error l i = Some x × R i x y) 0 l l'.
Admitted.

Lemma All2i_nth_error_l {A B} (P : nat -> A -> B -> Type) l l' n x k :
  All2i P k l l' ->
  nth_error l n = Some x ->
  ∑ c, nth_error l' n = Some c × P (k + n)%nat x c.
Admitted.

Lemma All2i_nth_error_r {A B} (P : nat ->A -> B -> Type) l l' n x k :
  All2i P k l l' ->
  nth_error l' n = Some x ->
  ∑ c, nth_error l n = Some c × P (k + n)%nat c x.
Admitted.

Lemma All2i_app_inv_l {X Y} (R : nat -> X -> Y -> Type) n xs xs' l :
  All2i R n (xs ++ xs') l ->
  ∑ ys ys',
  l = ys ++ ys' × All2i R n xs ys × All2i R (n + #|xs|) xs' ys'.
Admitted.

Lemma All2i_app_inv_r {X Y} (R : nat -> X -> Y -> Type) n l ys ys' :
  All2i R n l (ys ++ ys') ->
  ∑ xs xs',
  l = xs ++ xs' × All2i R n xs ys × All2i R (n + #|xs|) xs' ys'.
Admitted.

Lemma All2i_length {X Y} (R : nat -> X -> Y -> Type) n xs ys :
  All2i R n xs ys ->
  #|xs| = #|ys|.
Admitted.

Lemma All2i_app_inv {X Y} (R : nat -> X -> Y -> Type) n xs xs' ys ys' :
  All2i R n (xs ++ xs') (ys ++ ys') ->
  #|xs| = #|ys| ->
                All2i R n xs ys × All2i R (n + #|xs|) xs' ys'.
Admitted.

Lemma All2i_All2 {A B} {P : nat -> A -> B -> Type} {Q : A -> B -> Type} n l l' :
  All2i P n l l' ->
  (forall i x y, P i x y -> Q x y) ->
  All2 Q l l'.
Admitted.

Lemma All2i_All2_All2i_All2i {A B C n} {P : nat -> A -> B -> Type} {Q : B -> C -> Type} {R : nat -> A -> C -> Type}
  {S : nat -> A -> C -> Type} {l l' l''} :
  All2i P n l l' ->
  All2 Q l' l'' ->
  All2i R n l l'' ->
  (forall n x y z, P n x y -> Q y z -> R n x z -> S n x z) ->
  All2i S n l l''.
Admitted.

Lemma All2i_All2_All2 {A B C} {P : nat -> A -> B -> Type} {Q R : B -> C -> Type} {n l l' l''} :
  All2i P n l l' ->
  All2 Q l' l'' ->
  (forall n x y z, P n x y -> Q y z -> R y z) ->
  All2 R l' l''.
Admitted.

Inductive All_fold {A} (P : list A -> A -> Type) : list A -> Type :=
  | All_fold_nil : All_fold P nil
  | All_fold_cons {d Γ} : All_fold P Γ -> P Γ d -> All_fold P (d :: Γ).

Derive Signature NoConfusionHom for All_fold.

Lemma All_fold_tip {A : Type} (P : list A -> A -> Type) {x} : All_fold P [x] -> P [] x.
Admitted.

Inductive All2_fold {A} (P : list A -> list A -> A -> A -> Type)
            : list A -> list A -> Type :=
| All2_fold_nil : All2_fold P nil nil
| All2_fold_cons {d d' Γ Γ'} : All2_fold P Γ Γ' -> P Γ Γ' d d' -> All2_fold P (d :: Γ) (d' :: Γ').

Derive Signature NoConfusion for All2_fold.

Definition All_over {A B} (P : list B -> list B -> A -> A -> Type) (Γ Γ' : list B) :=
  fun Δ Δ' => P (Δ ++ Γ) (Δ' ++ Γ').

Lemma All2_fold_from_nth_error A L1 L2 P :
  #|L1| = #|L2| ->
                (forall n x1 x2, n < #|L1| -> nth_error L1 n = Some x1
                                           -> nth_error L2 n = Some x2
                                           -> P (skipn (S n) L1) (skipn (S n) L2) x1 x2) ->
                @All2_fold A P L1 L2.
Admitted.

Lemma All2_fold_app {A} {P} {Γ Γ' Γl Γr : list A} :
  All2_fold P Γ Γl ->
  All2_fold (All_over P Γ Γl) Γ' Γr ->
  All2_fold P (Γ' ++ Γ) (Γr ++ Γl).
Admitted.

Lemma All2_fold_length {A P} {Γ Γ' : list A} :
  All2_fold P Γ Γ' -> #|Γ| = #|Γ'|.
Admitted.

Lemma All2_fold_impl {A P Q} {Γ Γ' : list A} :
  All2_fold P Γ Γ' -> (forall Γ Γ' d d', P Γ Γ' d d' -> Q Γ Γ' d d') ->
  All2_fold Q Γ Γ'.
Admitted.

Lemma All_fold_app_inv {A} {P} (Γ Δ : list A) :
  All_fold P (Γ ++ Δ) ->
  All_fold P Δ × All_fold (fun Γ => P (Γ ++ Δ)) Γ.
Admitted.

Lemma All2_fold_All_fold_mix_left {A} P Q (Γ Γ' : list A) :
  All_fold P Γ ->
  All2_fold Q Γ Γ' ->
  All2_fold (fun Γ Γ' d d' => P Γ d × Q Γ Γ' d d') Γ Γ'.
Admitted.

Lemma All2_fold_All_fold_mix_right {A} P Q (Γ Γ' : list A) :
  All_fold P Γ' ->
  All2_fold Q Γ Γ' ->
  All2_fold (fun Γ Γ' d d' => P Γ' d' × Q Γ Γ' d d') Γ Γ'.
Admitted.

Lemma All2_fold_All_fold_mix_left_inv {A} P Q (Γ Γ' : list A) :
  All2_fold (fun Γ Γ' d d' => P Γ d × Q Γ Γ' d d') Γ Γ' ->
  All_fold P Γ × All2_fold Q Γ Γ'.
Admitted.

Lemma All2_fold_All_right {A P} {Γ Γ' : list A} :
  All2_fold (fun _ Γ _ d => P Γ d) Γ Γ' ->
  All_fold P Γ'.
Admitted.

Lemma All2_fold_All_left {A P} {Γ Γ' : list A} :
  All2_fold (fun Γ _ d _ => P Γ d) Γ Γ' ->
  All_fold P Γ.
Admitted.

Section All_fold.
  Context {A} {P : list A -> A -> Type}.

  Lemma All_fold_impl Q Γ :
    All_fold P Γ ->
    (forall Γ x, P Γ x -> Q Γ x) ->
    All_fold Q Γ.
Admitted.

  Lemma All_fold_app Γ Δ :
    All_fold (fun Γ => P (Γ ++ Δ)) Γ ->
    All_fold P Δ ->
    All_fold P (Γ ++ Δ).
Admitted.
End All_fold.

Section Alli_All_fold.
  Context {A : Type}.
  Lemma Alli_All_fold {P : nat -> A -> Type} {n Γ} :
    Alli P n Γ <~>
    All_fold (fun Γ d => P (n + #|Γ|) d) (List.rev Γ).
Admitted.

  Lemma Alli_rev_All_fold (P : nat -> A -> Type) n Γ :
    Alli P n (List.rev Γ) ->
    All_fold (fun Γ d => P (n + #|Γ|) d) Γ.
Admitted.

  Lemma All_fold_Alli_rev (P : nat -> A -> Type) n Γ :
    All_fold (fun Γ d => P (n + #|Γ|) d) Γ ->
    Alli P n (List.rev Γ).
Admitted.
End Alli_All_fold.

Section All2_fold.
  Context {A} {P : list A -> list A -> A -> A -> Type}.

  Lemma All2_fold_All2 (Q : A -> A -> Type) {Γ Δ : list A} :
    All2_fold (fun _ _ => Q) Γ Δ <~>
    All2 Q Γ Δ.
Admitted.

  Lemma All2_fold_refl: (forall Δ x, P Δ Δ x x) ->
    forall Δ : list A, All2_fold P Δ Δ.
Admitted.

  Lemma All2_fold_trans  :
    (forall Γ Γ' Γ'' x y z,
        All2_fold P Γ Γ' ->
        All2_fold P Γ' Γ'' ->
        All2_fold P Γ Γ'' ->
        P Γ Γ' x y -> P Γ' Γ'' y z -> P Γ Γ'' x z) ->
    CRelationClasses.Transitive (All2_fold P).
Admitted.

  Lemma All2_fold_sym :
    (forall Γ Γ' x y,
        All2_fold P Γ Γ' ->
        All2_fold P Γ' Γ ->
        P Γ Γ' x y -> P Γ' Γ y x) ->
    CRelationClasses.Symmetric (All2_fold P).
Admitted.

  Lemma All2_fold_flip Γ Δ :
    All2_fold P Γ Δ ->
    All2_fold (fun Γ Γ' x y => P Γ' Γ y x) Δ Γ.
Admitted.

  Lemma All2_fold_app_inv Γ Γ' Δ Δ' :
    #|Δ| = #|Δ'| ->
    All2_fold P (Δ ++ Γ) (Δ' ++ Γ') ->
    All2_fold P Γ Γ' * All2_fold (fun Δ Δ' => P (Δ ++ Γ) (Δ' ++ Γ')) Δ Δ'.
Admitted.

  Lemma All2_fold_app_inv_l Γ Γ' Δ Δ' :
    #|Γ| = #|Γ'| ->
    All2_fold P (Δ ++ Γ) (Δ' ++ Γ') ->
    All2_fold P Γ Γ' * All2_fold (fun Δ Δ' => P (Δ ++ Γ) (Δ' ++ Γ')) Δ Δ'.
Admitted.

  Lemma All2_fold_impl_ind {P' Γ Δ} :
    All2_fold P Γ Δ ->
    (forall Γ Δ d d',
      All2_fold P Γ Δ ->
      All2_fold P' Γ Δ ->
      P Γ Δ d d' ->
      P' Γ Δ d d') ->
    All2_fold P' Γ Δ.
Admitted.

  Lemma All2_fold_impl_len {Q} {Γ Δ : list A} :
    All2_fold P Γ Δ ->
    (forall Γ Δ T U, #|Γ| = #|Δ| -> P Γ Δ T U -> Q Γ Δ T U) ->
    All2_fold Q Γ Δ.
Admitted.

  Lemma All2_fold_forallb2 (Pb : A -> A -> bool) Γ Δ :
    All2_fold (fun _ _ => Pb) Γ Δ ->
    forallb2 Pb Γ Δ.
Admitted.

  Lemma All2_fold_nth {n Γ Γ' d} :
    All2_fold P Γ Γ' -> nth_error Γ n = Some d ->
    { d' & ((nth_error Γ' n = Some d') *
            let Γs := skipn (S n) Γ in
            let Γs' := skipn (S n) Γ' in
            All2_fold P Γs Γs' *
            P Γs Γs' d d')%type }.
Admitted.

  Lemma All2_fold_nth_r {n Γ Γ' d'} :
    All2_fold P Γ Γ' -> nth_error Γ' n = Some d' ->
    { d & ((nth_error Γ n = Some d) *
          let Γs := skipn (S n) Γ in
          let Γs' := skipn (S n) Γ' in
          All2_fold P Γs Γs' *
          P Γs Γs' d d')%type }.
Admitted.

  Lemma All2_fold_prod {Q} {Γ Δ} :
    All2_fold P Γ Δ ->
    All2_fold Q Γ Δ ->
    All2_fold (fun Γ Δ x y => P Γ Δ x y × Q Γ Δ x y) Γ Δ.
Admitted.

  Lemma All2_fold_prod_inv {Q} {Γ Δ} :
    All2_fold (fun Γ Δ x y => P Γ Δ x y × Q Γ Δ x y) Γ Δ ->
    All2_fold P Γ Δ × All2_fold Q Γ Δ.
Admitted.

End All2_fold.

Lemma All_fold_prod {A} (P : list A -> A -> Type) Q Γ Δ :
  #|Γ| = #|Δ| ->
  All_fold P Γ ->
  All_fold P Δ ->
  (forall Δ Δ' x y,
    All_fold P Δ ->
    All_fold P Δ' ->
    All2_fold Q Δ Δ' -> P Δ x -> P Δ' y -> Q Δ Δ' x y) ->
  All2_fold Q Γ Δ.
Admitted.

Lemma All2_fold_All_fold_mix {A P Q} {l l' : list A} :
  All2_fold P l l' ->
  All_fold Q l ->
  All_fold Q l' ->
  All2_fold (fun Γ Γ' x y => Q Γ x × Q Γ' y × P Γ Γ' x y) l l'.
Admitted.

Lemma All2_fold_All_fold_mix_inv {A} {P Q} {l l' : list A} :
  All2_fold (fun Γ Γ' x y => Q Γ x × Q Γ' y × P Γ Γ' x y) l l' ->
  All2_fold P l l' × All_fold Q l × All_fold Q l'.
Admitted.

Lemma All_fold_All2_fold_impl {A} {P Q} {Γ : list A} :
  All_fold P Γ ->
  (forall Γ d, All_fold P Γ -> All2_fold Q Γ Γ -> P Γ d -> Q Γ Γ d d) ->
  All2_fold Q Γ Γ.
Admitted.

Lemma All_fold_All2_fold {A P} {Γ : list A} :
  All_fold (fun Γ d => P Γ Γ d d) Γ <~>
  All2_fold P Γ Γ.
Admitted.

Lemma All_remove_last {A} (P : A -> Type) l : All P l -> All P (remove_last l).
Admitted.

Lemma All3_map_all {A B C} {A' B' C'} P (l : list A') (l' : list B') (l'' : list C')
  (f : A' -> A) (g : B' -> B) (h : C' -> C) :
  All3 (fun x y z => P (f x) (g y) (h z)) l l' l'' ->
  All3 P (map f l) (map g l') (map h l'').
Admitted.

Lemma OnOne2All_All3 {A B} P Q (l : list A) (l' : list B) (l'' : list B) :
  (forall x y z, P x y z -> Q x y z) ->
  (forall x y, Q x y y) ->
  OnOne2All P l l' l'' ->
  All3 Q l l' l''.
Admitted.

Set Equations Transparent.

Section map_All.
  Context {A B C} {Q : C -> Type} {P : C -> A  -> Prop}
    (fn : forall (x : A) , (forall (y:C),  Q y -> P y x) -> B).

  Equations? map_All (l : list A) (Hl : forall y, Q y -> ∥ All (P y) l ∥) : list B :=
  | [], _ := []
  | x :: xs, h := fn x _ :: map_All xs _.
  Proof.
all:clear fn map_All.
    -
 specialize (h y X).
sq.
now depelim h.
    -
 specialize (h y X).
sq.
now depelim h.
  Qed.
End map_All.

Section make_All.
  Context {A} {B : A -> Type} (f : forall x : A, B x).

  Equations make_All (l : list A) : All B l :=
  | [] := All_nil
  | hd :: tl := All_cons (f hd) (make_All tl).
End make_All.

Section make_All_All.
  Context {A} {B : A -> Type} {C : A -> Type} (f : forall x : A, B x -> C x).

  Equations make_All_All {l : list A} (a : All B l) : All C l :=
  | All_nil := All_nil
  | All_cons bhd btl := All_cons (f _ bhd) (make_All_All btl).
End make_All_All.

Lemma All_map_All {A B C} {Q : C -> Type} {P : C -> A -> Prop}
  {Q' : B -> Type} {R : C -> A -> Prop}
  f args (ha: forall y : C, Q y -> ∥ All (R y) args ∥) :
  (forall y : C, Q y -> All (P y) args) ->
  (forall x y rx, P y x -> Q' (f x rx)) ->
  forall y, Q y -> All Q' (map_All f args ha).
Admitted.

Lemma map_All_length {A B C : Type} {Q : C -> Type} {P : C -> A -> Prop}
  (fn : forall x : A, (forall y : C, Q y -> P y x) -> B)
  (l : list A) (Hl : forall y : C, Q y -> ∥ All (P y) l ∥) :
  #|map_All fn l Hl| = #|l|.
Admitted.
#[export] Hint Rewrite @map_All_length : len.

Lemma nth_error_map_All {A B C} {Q : C -> Type} {P : C -> A  -> Prop}
  (fn : forall (x : A) , (forall (y:C),  Q y -> P y x) -> B) :
  forall l : list A, forall H : (forall y : C, Q y -> ∥ All (P y) l ∥),
  forall n x,
    nth_error l n = Some x ->
    exists D, nth_error (map_All fn l H) n = Some (fn x D).
Admitted.

Section map_All2.
  Context {A B} {P Q : A -> B -> Type} (f : forall {x y}, P x y -> Q x y).

  Equations map_All2 {l l'} (a : All2 P l l') : All2 Q l l' :=
  | All2_nil := All2_nil
  | All2_cons hd tl := All2_cons (f _ _ hd) (map_All2 tl).
End map_All2.

Lemma All2_map2_left {A B C D E} {P : E -> A -> Type} Q (R : B -> D -> Type) {f : B -> C -> E} {l l' l'' l'''} :
  All2 R l l''' ->
  All2 Q l' l'' ->
  #|l| = #|l'| ->
  (forall x y z w, R x w -> Q y z -> P (f x y) z) ->
  All2 P (map2 f l l') l''.
Admitted.

Lemma All2_map2_left_All3 {A B C} {P : A -> A -> Type} {f : B -> C -> A} {l l' l''} :
  All3 (fun x y z => P (f x y) z) l l' l'' ->
  All2 P (map2 f l l') l''.
Admitted.

Lemma All3_impl {A B C} {P Q : A -> B -> C -> Type} {l l' l''} :
  All3 P l l' l'' ->
  (forall x y z, P x y z -> Q x y z) ->
  All3 Q l l' l''.
Admitted.

Lemma Forall3_impl {A B C} {P Q : A -> B -> C -> Prop} {l l' l''} :
  Forall3 P l l' l'' ->
  (forall x y z, P x y z -> Q x y z) ->
  Forall3 Q l l' l''.
Admitted.

Lemma Forall3_Forall2_left {A B C} {P : A -> B -> C -> Prop} {Q : A -> B -> Prop} {l l' l''} :
  Forall3 P l l' l'' ->
  (forall x y z, P x y z -> Q x y) ->
  Forall2 Q l l'.
Admitted.

Lemma Forall3_Forall2_edges {A B C} {P : A -> B -> C -> Prop} {Q : A -> C -> Prop} {l l' l''} :
  Forall3 P l l' l'' ->
  (forall x y z, P x y z -> Q x z) ->
  Forall2 Q l l''.
Admitted.

Lemma Forall3_Forall2_right {A B C} {P : A -> B -> C -> Prop} {Q : B -> C -> Prop} {l l' l''} :
  Forall3 P l l' l'' ->
  (forall x y z, P x y z -> Q y z) ->
  Forall2 Q l' l''.
Admitted.

Lemma Forall2_Forall2_Forall3 {A B C} {P : A -> B -> Prop} {Q : B -> C -> Prop} {l l' l''} :
  Forall2 P l l' ->
  Forall2 Q l' l'' ->
  Forall3 (fun x y z => P x y /\ Q y z) l l' l''.
Admitted.

Lemma Forall3_symP {A B} (P : B -> A -> A -> Prop) :
  (forall b, RelationClasses.Symmetric (P b)) ->
  forall l, RelationClasses.Symmetric (Forall3 P l).
Admitted.

Lemma Forall3_transP {A B} (P : B -> A -> A -> Prop) :
  (forall b, RelationClasses.Transitive (P b)) ->
  forall l, RelationClasses.Transitive (Forall3 P l).
Admitted.

Lemma Forall3_antisymP {A B} (P P' : B -> A -> A -> Prop) :
  (forall b x y, P b x y -> P b y x -> P' b x y) ->
  forall l l' l'', Forall3 P l l' l'' -> Forall3 P l l'' l' -> Forall3 P' l l' l''.
Admitted.

Lemma Forall3_map_inv {A B C A' B' C'} (R : A' -> B' -> C' -> Prop) (f : A -> A') (g : B -> B') (h : C -> C') l l' l'' :
  Forall3 R (map f l) (map g l') (map h l'') ->
  Forall3 (fun x y z => R (f x) (g y) (h z)) l l' l''.
Admitted.

Lemma Forall3_map {A B C A' B' C'} (R : A' -> B' -> C' -> Prop) (f : A -> A') (g : B -> B') (h : C -> C') l l' l'' :
  Forall3 (fun x y z => R (f x) (g y) (h z)) l l' l'' ->
  Forall3 R (map f l) (map g l') (map h l'').
Admitted.

Lemma map2_app {A B C} (f : A -> B -> C) l0 l0' l1 l1' :
  #|l0| = #|l1| -> #|l0'| = #|l1'| ->
  map2 f (l0 ++ l0') (l1 ++ l1') =
  map2 f l0 l1 ++ map2 f l0' l1'.
Admitted.

Lemma All1_map2_right_inv {A B C} R (g : A -> B -> C) l l' : #|l| = #|l'| ->  All2 R l (map2 g l l') ->  All2 (fun x y => R x (g x y)) l l'.
Admitted.

Lemma All1_map2_right {A B C} R (g : A -> B -> C) l l' : All2 (fun x y => R x (g x y)) l l' -> All2 R l (map2 g l l').
Admitted.

Lemma All1i_map2_right {A B C} k R (g : A -> B -> C) l l' : All2i (fun i x y => R i x (g x y)) k l l' -> All2i R k l (map2 g l l').
Admitted.

Lemma All1i_Alli_mix_left {A B k Q R} {l : list A} {l' : list B}
  : Alli Q k l -> All2i R k l l' -> All2i (fun i x y => Q i x * R i x y)%type k l l'.
Admitted.

Lemma All_Alli_swap_iff A B P
  : forall ls1 ls2 n, (@All A (fun x => @Alli B (P x) n ls1) ls2) <~> (@Alli B (fun n y => @All A (fun x => P x n y) ls2) n ls1).
Admitted.

Lemma All_eta3 {A B C P} ls
  : @All (A * B * C)%type (fun '(a, b, c) => P a b c) ls <~> All (fun abc => P abc.1.1 abc.1.2 abc.2) ls.
Admitted.

Local Ltac All2_All_swap_t_step :=
  first [ progress intros
        | progress subst
        | let is_ctor_list x :=
            lazymatch x with
            | nil => idtac
            | cons _ _ => idtac
            end in
          match goal with
          | [ H : All2 _ ?x ?y |- _ ]
            => first [ is_ctor_list x | is_ctor_list y ];
               inversion H; clear H
          | [ H : All2_fold _ ?x ?y |- _ ]
            => first [ is_ctor_list x | is_ctor_list y ];
               inversion H; clear H
          | [ H : All _ ?x |- _ ]
            => is_ctor_list x; inversion H; clear H
          | [ |- (_ :: _ = []) + _ ] => right
          | [ |- (?x = ?x) + _ ] => left
          end
        | exactly_once constructor
        | solve [ eauto
                | first [ eapply All2_impl | eapply All2_fold_impl | eapply All_impl ]; tea; cbn; intros *; (inversion 1 + constructor); subst; eauto ]
        | congruence
        | now apply All_refl; constructor
        | apply All2_from_nth_error => //; lia
        | progress cbn in *
        | match goal with
          | [ H : ?x <> ?x \/ ?A |- _ ]
            => (assert A by now destruct H); clear H
          end ].

Lemma All2_All_swap A B C P
  : forall ls1 ls2 ls3,
    @All2 A B (fun x y => @All C (P x y) ls1) ls2 ls3 -> @All C (fun z => @All2 A B (fun x y => P x y z) ls2 ls3) ls1.
Admitted.

Lemma All_All2_swap_sum A B C P
  : forall ls1 ls2 ls3,
    @All C (fun z => @All2 A B (fun x y => P x y z) ls2 ls3) ls1 -> (ls1 = []) + (@All2 A B (fun x y => @All C (P x y) ls1) ls2 ls3).
Admitted.

Lemma All_All2_swap A B C P
  : forall ls1 ls2 ls3,
    ls1 <> [] \/ List.length ls2 = List.length ls3 -> @All C (fun z => @All2 A B (fun x y => P x y z) ls2 ls3) ls1 -> @All2 A B (fun x y => @All C (P x y) ls1) ls2 ls3.
Admitted.

Lemma All2_fold_All_swap A B P
  : forall ls1 ls2 ls3,
    @All2_fold A (fun l1 l2 x y => @All B (P l1 l2 x y) ls1) ls2 ls3 -> @All B (fun z => @All2_fold A (fun l1 l2 x y => P l1 l2 x y z) ls2 ls3) ls1.
Admitted.

Lemma All_All2_fold_swap_sum A B P
  : forall ls1 ls2 ls3,
    @All B (fun z => @All2_fold A (fun l1 l2 x y => P l1 l2 x y z) ls2 ls3) ls1 -> (ls1 = []) + (@All2_fold A (fun l1 l2 x y => @All B (P l1 l2 x y) ls1) ls2 ls3).
Admitted.

Lemma All_All2_fold_swap A B P
  : forall ls1 ls2 ls3,
    ls1 <> [] \/ List.length ls2 = List.length ls3 -> @All B (fun z => @All2_fold A (fun l1 l2 x y => P l1 l2 x y z) ls2 ls3) ls1 -> @All2_fold A (fun l1 l2 x y => @All B (P l1 l2 x y) ls1) ls2 ls3.
Admitted.

Lemma All2_map2_right {A B C} {l : list A} {l' : list B} (f : A -> B -> C) P :
  All2 (fun x y => P x (f x y)) l l' ->
  All2 P l (map2 f l l').
Admitted.

Lemma All2i_map2_right {A B C} {n} {l : list A} {l' : list B} (f : A -> B -> C) P :
  All2i (fun n x y => P n x (f x y)) n l l' ->
  All2i P n l (map2 f l l').
Admitted.

Lemma All2_map2_right_inv {A B C} R (g : A -> B -> C) l l' : #|l| = #|l'| ->  All2 R l (map2 g l l') ->  All2 (fun x y => R x (g x y)) l l'.
Admitted.

Lemma All2i_Alli_mix_left {A B k Q R} {l : list A} {l' : list B}
  : Alli Q k l -> All2i R k l l' -> All2i (fun i x y => (Q i x * R i x y)%type) k l l'.
Admitted.

End All_Forall.

End MetaCoq_DOT_Utils_DOT_All_Forall_WRAPPED.
Module Export MetaCoq_DOT_Utils_DOT_All_Forall.
Module Export MetaCoq.
Module Export Utils.
Module All_Forall.
Include MetaCoq_DOT_Utils_DOT_All_Forall_WRAPPED.All_Forall.
End All_Forall.

End Utils.

End MetaCoq.

End MetaCoq_DOT_Utils_DOT_All_Forall.
Export MetaCoq.Utils.MCPrelude.
Export MetaCoq.Utils.All_Forall.
Export MetaCoq.Utils.MCList.
Export MetaCoq.Utils.MCOption.
Export MetaCoq.Utils.MCProd.
Export MetaCoq.Utils.bytestring.
Export Coq.ZArith.ZArith.
Export Coq.micromega.Lia.

Global Set Asymmetric Patterns.

Definition ident   := string.

Definition dirpath := list ident.

Inductive modpath :=
| MPfile  (dp : dirpath)
| MPbound (dp : dirpath) (id : ident) (i : nat)
| MPdot   (mp : modpath) (id : ident).

Definition kername := modpath × ident.

Record inductive : Set := mkInd { inductive_mind : kername ;
                                  inductive_ind : nat }.

Record projection := mkProjection
  { proj_ind : inductive;
    proj_npars : nat;
    proj_arg : nat  }.

Inductive name : Set :=
| nAnon
| nNamed (_ : ident).

Inductive relevance : Set := Relevant | Irrelevant.

Record binder_annot (A : Type) := mkBindAnn { binder_name : A; binder_relevance : relevance }.

Definition aname := binder_annot name.

Record case_info := mk_case_info {
  ci_ind : inductive;
  ci_npar : nat;

  ci_relevance : relevance }.

Record def term := mkdef {
  dname : aname;
  dtype : term;
  dbody : term;
  rarg  : nat   }.
Arguments dtype {term} _.
Arguments dbody {term} _.

Definition mfixpoint term := list (def term).

Definition tFixProp {A} (P P' : A -> Type) (m : mfixpoint A) :=
  All (fun x : def A => P x.(dtype) * P' x.(dbody))%type m.

Section Contexts.
  Context {term : Type}.

  Record context_decl := mkdecl {
    decl_name : aname ;
    decl_body : option term ;
    decl_type : term
  }.
End Contexts.

Arguments context_decl : clear implicits.

Definition ondecl {A} (P : A -> Type) (d : context_decl A) :=
  option_default P d.(decl_body) unit × P d.(decl_type).

Notation onctx P := (All (ondecl P)).

Import Coq.MSets.MSetList.

Module Level.
  Inductive t_ : Set :=
  | lzero
  | level (_ : string)
  | lvar (_ : nat) .

  Definition t := t_.

  Inductive lt_ : t -> t -> Prop :=
  | ltSetLevel s : lt_ lzero (level s)
  | ltSetlvar n : lt_ lzero (lvar n)
  | ltLevelLevel s s' : StringOT.lt s s' -> lt_ (level s) (level s')
  | ltLevellvar s n : lt_ (level s) (lvar n)
  | ltlvarlvar n n' : Nat.lt n n' -> lt_ (lvar n) (lvar n').

  Definition lt := lt_.

End Level.

Module LevelExpr.
  Definition t := (Level.t * nat)%type.
Definition eq : t -> t -> Prop.
exact (eq).
Defined.
Definition eq_equiv : Equivalence eq.
Admitted.

  Inductive lt_ : t -> t -> Prop :=
  | ltLevelExpr1 l n n' : (n < n')%nat -> lt_ (l, n) (l, n')
  | ltLevelExpr2 l l' b b' : Level.lt l l' -> lt_ (l, b) (l', b').

  Definition lt := lt_.

  Global Instance lt_strorder : StrictOrder lt.
Admitted.

  Definition lt_compat : Proper (Logic.eq ==> Logic.eq ==> iff) lt.
Admitted.
Definition compare (x y : t) : comparison.
Admitted.

  Definition compare_spec :
    forall x y : t, CompareSpec (x = y) (lt x y) (lt y x) (compare x y).
Admitted.
Definition eq_dec : forall (l1 l2 : t), {l1 = l2} + {l1 <> l2}.
Admitted.
Definition eq_leibniz (x y : t) : eq x y -> x = y.
Admitted.

End LevelExpr.

Module LevelExprSet := MSetList.MakeWithLeibniz LevelExpr.

Record nonEmptyLevelExprSet
  := { t_set : LevelExprSet.t ;
       t_ne  : LevelExprSet.is_empty t_set = false }.

Module Universe.

  Definition t := nonEmptyLevelExprSet.
Definition lt : t -> t -> Prop.
Admitted.
End Universe.

Module Instance.
Definition t : Set.
exact (list Level.t).
Defined.
End Instance.

Module Sort.
  Inductive t_ {univ} :=
    sProp | sSProp | sType (_ : univ).
  Arguments t_ : clear implicits.

  Definition t := t_ Universe.t.

  Inductive lt_ {univ univ_lt} : t_ univ -> t_ univ -> Prop :=
  | ltPropSProp : lt_ sProp sSProp
  | ltPropType s : lt_ sProp (sType s)
  | ltSPropType s : lt_ sSProp (sType s)
  | ltTypeType s1 s2 : univ_lt s1 s2 -> lt_ (sType s1) (sType s2).
  Arguments lt_ {univ} univ_lt.

  Definition lt := lt_ Universe.lt.

  Module OT <: OrderedType.
    Definition t := t.
#[local] Definition eq : t -> t -> Prop.
exact (eq).
Defined.
#[local] Definition eq_equiv : Equivalence eq.
Admitted.
    Definition lt := lt.
    #[local] Instance lt_strorder : StrictOrder lt.
Admitted.

    Definition lt_compat : Proper (eq ==> eq ==> iff) lt.
Admitted.
Definition compare (x y : t) : comparison.
Admitted.
    Lemma compare_spec x y : CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
Admitted.
    Definition eq_dec (x y : t) : {x = y} + {x <> y}.
Admitted.
  End OT.
End Sort.
Notation sort := Sort.t.

Module Type Term.

  Parameter Inline term : Type.
End Term.

Module Type TermDecide (Import T : Term).
End TermDecide.

Module TermDecideReflectInstances (Import T : Term) (Import TDec : TermDecide T).
End TermDecideReflectInstances.

Module Environment (T : Term).

  Import T.

  Notation context_decl := (context_decl term).

  Definition context := list context_decl.

End Environment.
Module Export PCUICPrimitive.
Import MetaCoq.Common.Primitive.

Record array_model {term : Type} :=
  { array_level : Level.t;
    array_type : term;
    array_default : term;
    array_value : list term }.

Arguments array_model : clear implicits.

Inductive prim_model (term : Type) : prim_tag -> Type :=
| primIntModel (i : PrimInt63.int) : prim_model term primInt
| primFloatModel (f : PrimFloat.float) : prim_model term primFloat
| primArrayModel (a : array_model term) : prim_model term primArray.

Definition prim_val term := ∑ t : prim_tag, prim_model term t.
Definition tPrimProp {term} (P : term -> Type) (p : PCUICPrimitive.prim_val term) : Type.
exact (match p.π2 return Type with
  | primIntModel f => unit
  | primFloatModel f => unit
  | primArrayModel a => P a.(array_type) × P a.(array_default) × All P a.(array_value)
  end).
Defined.
Module Export PCUICAst.

Record predicate {term} := mk_predicate {
  pparams : list term;
  puinst : Instance.t;
  pcontext : list (context_decl term);

  preturn : term;  }.
Arguments predicate : clear implicits.

Section Branch.
  Context {term : Type}.

  Record branch := mk_branch {
    bcontext : list (context_decl term);

    bbody : term;  }.

End Branch.
Arguments branch : clear implicits.

Inductive term :=
| tRel (n : nat)
| tVar (i : ident)
| tEvar (n : nat) (l : list term)
| tSort (u : sort)
| tProd (na : aname) (A B : term)
| tLambda (na : aname) (A t : term)
| tLetIn (na : aname) (b B t : term)
| tApp (u v : term)
| tConst (k : kername) (ui : Instance.t)
| tInd (ind : inductive) (ui : Instance.t)
| tConstruct (ind : inductive) (n : nat) (ui : Instance.t)
| tCase (indn : case_info) (p : predicate term) (c : term) (brs : list (branch term))
| tProj (p : projection) (c : term)
| tFix (mfix : mfixpoint term) (idx : nat)
| tCoFix (mfix : mfixpoint term) (idx : nat)
| tPrim (prim : prim_val term).

Notation prim_val := (prim_val term).

Module PCUICTerm <: Term.

  Definition term := term.
End PCUICTerm.

Module PCUICEnvironment := Environment PCUICTerm.
Export PCUICEnvironment.

Definition tCasePredProp {term}
            (Pparams Preturn : term -> Type)
            (p : predicate term) :=
  All Pparams p.(pparams) ×
  onctx Pparams p.(pcontext) ×
  Preturn p.(preturn).

Definition tCaseBrsProp {A} (P : A -> Type) (l : list (branch A)) :=
  All (fun x => onctx P (bcontext x) × P (bbody x)) l.

Definition def_size (size : term -> nat) (x : def term)
  := size (dtype x) + size (dbody x).

Definition mfixpoint_size (size : term -> nat) (l : mfixpoint term) :=
  list_size (def_size size) l.

Definition decl_size (size : term -> nat) (x : context_decl) :=
  size (decl_type x) + option_default size (decl_body x) 0.

Definition context_size (size : term -> nat) (l : context) :=
  list_size (decl_size size) l.

Definition branch_size (size : term -> nat) (br : branch term) :=
  context_size size br.(bcontext) + size br.(bbody).

Definition predicate_size (size : term -> nat) (p : PCUICAst.predicate term) :=
  list_size size p.(pparams) +
  context_size size p.(pcontext) +
  size p.(preturn).
Definition prim_size (size : term -> nat) (p : prim_val) : nat.
exact (match p.π2 return nat with
  | primIntModel f => 0
  | primFloatModel f => 0
  | primArrayModel a => size a.(array_type) + size a.(array_default) + list_size size a.(array_value)
  end).
Defined.

Fixpoint size t : nat :=
  match t with
  | tRel i => 1
  | tEvar ev args => S (list_size size args)
  | tLambda na T M => S (size T + size M)
  | tApp u v => S (size u + size v)
  | tProd na A B => S (size A + size B)
  | tLetIn na b t b' => S (size b + size t + size b')
  | tCase ind p c brs => S (predicate_size size p +
    size c + list_size (branch_size size) brs)
  | tProj p c => S (size c)
  | tFix mfix idx => S (mfixpoint_size size mfix)
  | tCoFix mfix idx => S (mfixpoint_size size mfix)
  | tPrim p => S (prim_size size p)
  | _ => 1
  end.
Import MetaCoq.Utils.LibHypsNaming.
Import Equations.Prop.Equations.

Lemma term_ind_size_app :
  forall (P : term -> Type),
    (forall (n : nat), P (tRel n)) ->
    (forall (i : ident), P (tVar i)) ->
    (forall (n : nat) (l : list term), All (P) l -> P (tEvar n l)) ->
    (forall s, P (tSort s)) ->
    (forall (n : aname) (t : term), P t -> forall t0 : term, P t0 -> P (tProd n t t0)) ->
    (forall (n : aname) (t : term), P t -> forall t0 : term, P t0 -> P (tLambda n t t0)) ->
    (forall (n : aname) (t : term),
        P t -> forall t0 : term, P t0 -> forall t1 : term, P t1 ->
                                                   P (tLetIn n t t0 t1)) ->
    (forall (t u : term),
        (forall t', size t' < size (tApp t u) -> P t') ->
        P t -> P u -> P (tApp t u)) ->
    (forall s (u : list Level.t), P (tConst s u)) ->
    (forall (i : inductive) (u : list Level.t), P (tInd i u)) ->
    (forall (i : inductive) (n : nat) (u : list Level.t), P (tConstruct i n u)) ->
    (forall (ci : case_info) (p : PCUICAst.predicate term) (c : term) (brs : list (branch term)),
        tCasePredProp P P p -> P c ->
        tCaseBrsProp P brs -> P (tCase ci p c brs)) ->
    (forall (s : projection) (t : term), P t -> P (tProj s t)) ->
    (forall (m : mfixpoint term) (n : nat),
        tFixProp P P m -> P (tFix m n)) ->
    (forall (m : mfixpoint term) (n : nat),
        tFixProp (P) P m -> P (tCoFix m n)) ->
    (forall p, tPrimProp P p -> P (tPrim p)) ->
    forall (t : term), P t.
Proof.
  intros.
  revert t.
set(foo:=CoreTactics.the_end_of_the_section).
intros.
  Subterm.rec_wf_rel aux t (MR lt size); unfold MR in *; simpl.
clear H0.
  assert (auxl : forall {A} (l : list A) (f : A -> term), list_size (fun x => size (f x)) l < size pr1 ->
                                                            All (fun x => P (f x)) l).
  {
 induction l; constructor.
eapply aux.
red.
simpl in H.
lia.
apply IHl.
simpl in H.
lia.
}
  assert (forall m, list_size (fun x : def term => size (dtype x)) m < S (mfixpoint_size size m)).
  {
 clear.
unfold mfixpoint_size, def_size.
induction m.
simpl.
auto.
simpl.
lia.
}
  assert (forall m, list_size (fun x : def term => size (dbody x)) m < S (mfixpoint_size size m)).
  {
 clear.
unfold mfixpoint_size, def_size.
induction m.
simpl.
auto.
simpl.
lia.
}

  move aux at top.
move auxl at top.

  !destruct pr1; eauto;
    try match reverse goal with
          |- context [tFix _ _] => idtac
        | H : _ |- _ => solve [apply H; (eapply aux || eapply auxl); red; simpl; try lia]
        end.

  *
 eapply X10.
2:{
 apply aux; simpl.
simpl; lia.
}
    repeat split.
    +
 revert aux; simpl; unfold predicate_size.
      induction (pparams hh0); constructor; auto.
      apply aux.
simpl.
lia.
      apply IHl; intros.
apply aux; simpl; lia.
    +
 revert aux; simpl; unfold predicate_size.
      induction (pcontext hh0); constructor; auto.
      destruct a as [na [b|] ty]; constructor; simpl;
      try (apply aux; cbn; lia).
exact tt.
      apply IHl; intros.
apply aux; simpl; lia.
    +
 apply aux; simpl.
unfold predicate_size.
lia.
    +
 red.
      revert aux; simpl.
      clear.
      induction hh1; simpl; constructor; auto.
      revert aux.
unfold branch_size.
      induction (bcontext a); split; try constructor; auto.
      apply aux.
lia.
      destruct a0 as [na [b|] ty]; constructor; simpl;
      try (apply aux; cbn; lia).
exact tt.
      apply IHl; intros.
apply aux; simpl; lia.
      apply aux.
lia.
      apply IHhh1.
intros.
apply aux.
lia.

  *
 eapply X12; try (apply aux; red; simpl; lia).
    red.
apply All_pair.
split; apply auxl; simpl; auto.

  *
 eapply X13; try (apply aux; red; simpl; lia).
    red.
apply All_pair.
split; apply auxl; simpl; auto.

  *
 eapply X14.
    destruct hh, p; cbn; intuition auto.
    1-2:(eapply aux; cbn; lia).
    eapply (auxl _ (array_value a) id).
    change (fun x => size (id x)) with size.
cbn; lia.
Defined.
