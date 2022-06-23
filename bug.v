(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "-deprecated-native-compiler-option" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/category_theory" "Category" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Equations" "Equations" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-top" "TList" "-native-compiler" "no") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 681 lines to 271 lines *)
(* coqc version 8.17+alpha compiled with OCaml 4.09.0
   coqtop version 
   Expected coqc runtime on this file: 1.640 sec *)
Require Coq.Bool.Bool.
Require Coq.Classes.CEquivalence.
Require Coq.Classes.CRelationClasses.
Require Coq.Classes.CMorphisms.
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
Require Equations.Type.Logic.
Require Equations.Type.Relation.
Require Equations.Type.Relation_Properties.
Require Equations.Type.FunctionalExtensionality.
Require Equations.Type.WellFounded.
Require Equations.Type.Classes.
Require Equations.Type.EqDec.
Require Coq.Init.Datatypes.
Require Coq.Program.Program.
Require Category.Lib.Foundation.
Require Category.Lib.Setoid.
Require Category.Lib.Tactics.
Require Coq.NArith.NArith.
Require Category.Lib.Datatypes.
Require Category.Lib.
Require Coq.Arith.EqNat.

Declare ML Module "coq-core.plugins.ltac".
Module Export AdmitTactic.
Module Import LocalFalse.
Inductive False : Prop := .
End LocalFalse.
Axiom proof_admitted : False.
Global Set Default Proof Mode "Classic".
Tactic Notation "admit" := abstract case proof_admitted.
End AdmitTactic.
Set Warnings "-notation-overridden".
Set Warnings "-deprecated-hint-without-locality".
Import Coq.Bool.Bool.

Open Scope lazy_bool_scope.
Import Coq.Classes.CEquivalence.
Export Coq.Classes.CRelationClasses.
Import Coq.Classes.CMorphisms.
Import Equations.Prop.Equations.
Import Equations.Type.EqDec.
Set Equations With UIP.
Import Category.Lib.

Inductive tlist {A : Type} (B : A -> A -> Type) : A -> A -> Type :=
  | tnil : forall i : A, tlist B i i
  | tcons : forall i j k : A, B i j -> tlist B j k -> tlist B i k.

Derive Signature for tlist.
Derive NoConfusion for tlist.
Derive Subterm for tlist.
Next Obligation.
Admitted.

Arguments tnil {A B i}.
Arguments tcons {A B i} j {k} x xs.

Notation "x ::: xs" := (tcons _ x xs) (at level 60, right associativity).

Section TList.

Context {A : Type}.
Context {B : A -> A -> Type}.

Fixpoint tlist_length {i j} (xs : tlist B i j) : nat :=
  match xs with
  | tnil => 0
  | tcons x _ xs => 1 + tlist_length xs
  end.

 

Equations tlist_app {i j k} (xs : tlist B i j) (ys : tlist B j k) :
  tlist B i k :=
  tlist_app tnil ys := ys;
  tlist_app xs tnil := xs;
  tlist_app (@tcons _ _ _ _ _ x xs) ys := x ::: tlist_app xs ys.

Notation "xs +++ ys" := (tlist_app xs ys) (at level 60, right associativity).

Equations tlist_uncons {i j} (xs : tlist B i j) :
  option { z : A & B i z * tlist B z j }%type :=
  tlist_uncons tnil := None;
  tlist_uncons (@tcons _ _ _ _ _ x xs) := Some (_; (x, xs)).

Equations tlist_map {i j A' C} {f : A -> A'}
          (g : forall i j : A, B i j -> C (f i) (f j))
          (xs : tlist B i j) : tlist C (f i) (f j) :=
  tlist_map _ tnil := tnil;
  tlist_map g (@tcons _ _ _ _ _ x xs) := g _ _ x ::: tlist_map g xs.

Equations tlist_mapv {i j C}
          (g : forall i j : A, B i j -> C)
          (xs : tlist B i j) : list C :=
  tlist_mapv _ tnil := nil;
  tlist_mapv g (@tcons _ _ _ _ _ x xs) := g _ _ x :: tlist_mapv g xs.

Equations tlist_head {i j} (xs : tlist B i j) :
  option { z : A & B i z }%type :=
  tlist_head tnil := None;
  tlist_head (@tcons _ _ _ _ _ x xs) := Some (_; x).

Equations tlist_tail {i j} (xs : tlist B i j) :
  option { z : A & tlist B z j }%type :=
  tlist_tail tnil := None;
  tlist_tail (@tcons _ _ _ _ _ x xs) := Some (_; xs).

Equations tlist_init {i j} (xs : tlist B i j) :
  option { z : A & tlist B i z }%type :=
  tlist_init tnil := None;
  tlist_init (@tcons _ _ _ _ _ x xs) with tlist_init xs := {
    | None => Some (_; tnil);
    | Some (existT ys) => Some (_; (x ::: ys))
  }.

Equations tlist_last {i j} (xs : tlist B i j) :
  option { z : A & B z j }%type :=
  tlist_last tnil := None;
  tlist_last (@tcons _ _ _ _ _ x xs) with xs := {
    | tnil => Some (_; x);
    | @tcons _ _ _ _ _ y ys => tlist_last ys
  }.

Equations tlist_rev (flip : forall x y : A, B x y -> B y x)
          {i j} (xs : tlist B i j) : tlist B j i :=
  tlist_rev flip tnil := tnil;
  tlist_rev flip (@tcons _ _ _ _ _ x xs) :=
    tlist_rev flip xs +++ flip _ _ x ::: tnil.

Fixpoint tlist_concat {i j} (xs : tlist (tlist B) i j) : tlist B i j :=
  match xs with
  | tnil => tnil
  | tcons _ x xs => x +++ tlist_concat xs
  end.

Context `{AE : EqDec A}.
Context `{BE : forall i j, EqDec (B i j)}.

Import EqNotations.

 
 

Equations tlist_eq_dec {i j : A} (x y : tlist B i j) : {x = y} + {x ≠ y} :=
  tlist_eq_dec tnil tnil := left eq_refl;
  tlist_eq_dec tnil _ := in_right;
  tlist_eq_dec _ tnil := in_right;
  tlist_eq_dec (@tcons _ _ _ m _ x xs) (@tcons _ _ _ o _ y ys)
    with @eq_dec _ AE m o := {
      | left H with @eq_dec _ (BE _ _) x (rew <- [fun x => B _ x] H in y) := {
          | left _ with tlist_eq_dec xs (rew <- [fun x => tlist B x _] H in ys) := {
             | left _ => left _;
             | _ => in_right
            };
          | _ => in_right
        };
      | _ => in_right
    }.
Next Obligation.
  simpl_eq; intros.
  apply n.
  inv H.
  apply Eqdep_dec.inj_pair2_eq_dec in H1; [|apply eq_dec].
  apply Eqdep_dec.inj_pair2_eq_dec in H1; [|apply eq_dec].
  assumption.
Defined.
Next Obligation.
  simpl_eq; intros.
  apply n.
  inv H.
  apply Eqdep_dec.inj_pair2_eq_dec in H1; [|apply eq_dec].
  apply Eqdep_dec.inj_pair2_eq_dec in H1; [|apply eq_dec].
  assumption.
Defined.

Lemma tlist_app_tnil_l {i j} (xs : tlist B i j) :
  tnil +++ xs = xs.
Proof.
now destruct xs.
Qed.

Lemma tlist_app_cons {i j k} (x : B i j) (xs : tlist B j k) :
  x ::: xs = (x ::: tnil) +++ xs.
Proof.
now destruct xs.
Qed.

Lemma tlist_app_comm_cons {i j k l} (x : B i j)
      (xs : tlist B j k) (ys : tlist B k l) :
  x ::: (xs +++ ys) = (x ::: xs) +++ ys.
Proof.
now destruct xs, ys.
Qed.

Lemma tlist_app_assoc {i j k l}
      (xs : tlist B i j) (ys : tlist B j k) (zs : tlist B k l) :
  (xs +++ ys) +++ zs = xs +++ (ys +++ zs).
Proof.
  induction xs; auto.
  now rewrite <- !tlist_app_comm_cons, IHxs.
Qed.

Context `{forall i j, Setoid (B i j)}.

Equations tlist_equiv {i j : A} (x y : tlist B i j) : Type :=
  tlist_equiv tnil tnil := True;
  tlist_equiv tnil _ := False;
  tlist_equiv _ tnil := False;
  tlist_equiv (@tcons _ _ _ m _ x xs) (@tcons _ _ _ o _ y ys)
    with eq_dec m o := {
      | left H =>
         equiv x (rew <- [fun x => B _ x] H in y) *
         tlist_equiv xs (rew <- [fun x => tlist B x _] H in ys);
      | right _ => False
    }.

Global Program Instance tlist_equiv_Equivalence {i j} :
  Equivalence (@tlist_equiv i j).
Next Obligation.
  repeat intro.
  induction x; simpl.
    constructor.
  rewrite tlist_equiv_equation_4.
  unfold tlist_equiv_clause_4.
  rewrite EqDec.peq_dec_refl.
  split.
    apply Equivalence_Reflexive.
  apply IHx.
Qed.
Next Obligation.
  repeat intro.
  induction x; simpl.
    dependent elimination y as [tnil]; auto.
  dependent elimination y as [tcons _ y ys]; auto.
  rewrite tlist_equiv_equation_4 in *.
  destruct (eq_dec j _); [|contradiction].
  subst.
  rewrite EqDec.peq_dec_refl.
  destruct X.
  split.
    now apply Equivalence_Symmetric.
  apply IHx, t.
Qed.
