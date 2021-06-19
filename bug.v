(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "-deprecated-native-compiler-option" "-w" "-deprecated-appcontext -notation-overridden" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/fiat_parsers/src" "Fiat" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/fiat_parsers/Bedrock" "Bedrock" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-I" "/github/workspace/builds/coq/coq-failing/_build_ci/fiat_parsers/src/Common/Tactics" "-top" "bug_01" "-native-compiler" "no" "-require-import" "Coq.Compat.AdmitAxiom" "-native-compiler" "no") -*- *)
(* File reduced by coq-bug-finder from original input, then from 916 lines to 386 lines, then from 507 lines to 948 lines, then from 951 lines to 417 lines, then from 538 lines to 916 lines, then from 919 lines to 447 lines, then from 567 lines to 917 lines, then from 921 lines to 475 lines, then from 595 lines to 831 lines, then from 834 lines to 516 lines, then from 634 lines to 1027 lines, then from 1031 lines to 795 lines, then from 910 lines to 2027 lines, then from 2031 lines to 1799 lines, then from 1801 lines to 806 lines, then from 918 lines to 1029 lines, then from 1033 lines to 887 lines, then from 999 lines to 1506 lines, then from 1510 lines to 1022 lines, then from 1110 lines to 1322 lines, then from 1325 lines to 1054 lines, then from 1142 lines to 1195 lines, then from 1199 lines to 1173 lines, then from 1176 lines to 1076 lines, then from 1161 lines to 1456 lines, then from 1459 lines to 1237 lines, then from 1310 lines to 1462 lines, then from 1466 lines to 1257 lines, then from 1325 lines to 1458 lines, then from 1462 lines to 1287 lines, then from 1353 lines to 1483 lines, then from 1487 lines to 1294 lines, then from 1360 lines to 1530 lines, then from 1534 lines to 1530 lines, then from 1530 lines to 1370 lines, then from 1435 lines to 1479 lines, then from 1483 lines to 1382 lines, then from 1447 lines to 1598 lines, then from 1602 lines to 1400 lines, then from 1461 lines to 2272 lines, then from 2275 lines to 1688 lines, then from 1691 lines to 1498 lines, then from 1556 lines to 1843 lines, then from 1847 lines to 1527 lines, then from 1585 lines to 1869 lines, then from 1873 lines to 1659 lines, then from 1712 lines to 1965 lines, then from 1969 lines to 1785 lines, then from 1807 lines to 1755 lines, then from 1808 lines to 2104 lines, then from 2108 lines to 1790 lines, then from 1841 lines to 2002 lines, then from 2006 lines to 1809 lines, then from 1859 lines to 2559 lines, then from 2563 lines to 2189 lines *)
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
Require Coq.MSets.MSetPositive.
Require Coq.MSets.MSetProperties.
Require Coq.Sets.Ensembles.
Require Coq.Strings.String.
Require Coq.Strings.Ascii.
Require Coq.Arith.Arith.
Require Coq.ZArith.BinInt.
Require Coq.NArith.BinNat.
Require Coq.Bool.Bool.
Require Coq.Classes.Morphisms.
Require Coq.Compat.Coq814.
Require Coq.ZArith.BinIntDef.
Require Coq.PArith.BinPosDef.
Require Coq.NArith.BinNatDef.
Require Coq.Reals.Rdefinitions.
Require Coq.Numbers.Cyclic.Int63.Int63.
Require Coq.Numbers.Cyclic.Int31.Int31.
Require Coq.micromega.Lia.
Require Coq.Lists.List.
Require Coq.Vectors.Vector.
Require Coq.funind.FunInd.
Require Fiat.Common.Coq__8_4__8_5__Compat.
Require Fiat.Common.BoolFacts.
Require Coq.Lists.SetoidList.
Require Coq.Logic.Eqdep_dec.
Require Coq.Numbers.Natural.Peano.NPeano.
Require Coq.ZArith.ZArith.
Require Coq.Setoids.Setoid.
Require Coq.Classes.RelationClasses.
Require Coq.Program.Program.
Require Fiat.Common.Tactics.SplitInContext.
Require Fiat.Common.Tactics.Combinators.
Require Fiat.Common.Tactics.FreeIn.
Require Fiat.Common.Tactics.SetoidSubst.
Require Fiat.Common.Tactics.Head.
Require Fiat.Common.Tactics.BreakMatch.
Require Fiat.Common.Tactics.FoldIsTrue.
Require Fiat.Common.Tactics.SpecializeBy.
Require Fiat.Common.Tactics.DestructHyps.
Require Fiat.Common.Tactics.DestructSig.
Require Fiat.Common.Tactics.DestructHead.
Require Fiat.Common.
Module Export Fiat_DOT_Common_DOT_Equality.
Module Export Fiat.
Module Export Common.
Module Export Equality.
Import Coq.Lists.List.
Import Coq.Lists.SetoidList.
Import Coq.Bool.Bool.
Import Coq.Strings.Ascii.
Import Coq.Strings.String.
Import Coq.Logic.Eqdep_dec.
Import Fiat.Common.

Set Implicit Arguments.
Local Close Scope nat_scope.

Definition concat_1p {A x y} (p : x = y :> A) : eq_trans eq_refl p = p.
admit.
Defined.
Definition concat_p1 {A x y} (p : x = y :> A) : eq_trans p eq_refl = p.
admit.
Defined.
Definition concat_pV {A x y} (p : x = y :> A) : eq_trans p (eq_sym p) = eq_refl.
admit.
Defined.
Definition concat_Vp {A x y} (p : x = y :> A) : eq_trans (eq_sym p) p = eq_refl.
admit.
Defined.
Definition transport_pp {A} {P : A -> Type} {x y z} (p : x = y) (q : y = z) (k : P x)
: eq_rect _ P k _ (eq_trans p q) = eq_rect _ P (eq_rect _ P k _ p) _ q.
admit.
Defined.
Lemma transport_const {A P x y} (p : x = y :> A) k
: eq_rect _ (fun _ : A => P) k _ p = k.
admit.
Defined.
Lemma ap_const {A B x y} (b : B) (p : x = y :> A)
: f_equal (fun _ => b) p = eq_refl.
admit.
Defined.
Lemma inv_pp {A x y z} (p : x = y :> A) (q : y = z :> A)
: eq_sym (eq_trans p q) = eq_trans (eq_sym q) (eq_sym p).
admit.
Defined.
Lemma inv_V {A x y} (p : x = y :> A)
: eq_sym (eq_sym p) = p.
admit.
Defined.

Section sigT.
  Definition pr1_path {A} {P : A -> Type} {u v : sigT P} (p : u = v)
  : projT1 u = projT1 v
    := f_equal (@projT1 _ _) p.

  Definition pr2_path {A} {P : A -> Type} {u v : sigT P} (p : u = v)
  : eq_rect _ _ (projT2 u) _ (pr1_path p) = projT2 v.
admit.
Defined.

  Definition path_sigT_uncurried {A : Type} (P : A -> Type) (u v : sigT P)
             (pq : {p : projT1 u = projT1 v & eq_rect _ _ (projT2 u) _ p = projT2 v})
  : u = v.
admit.
Defined.

  Definition path_sigT {A : Type} (P : A -> Type) (u v : sigT P)
             (p : projT1 u = projT1 v) (q : eq_rect _ _ (projT2 u) _ p = projT2 v)
  : u = v
    := path_sigT_uncurried u v (existT _ p q).

  Definition path_sigT_nondep {A B : Type} (u v : @sigT A (fun _ => B))
             (p : projT1 u = projT1 v) (q : projT2 u = projT2 v)
  : u = v
    := @path_sigT _ _ u v p (eq_trans (transport_const _ _) q).

  Lemma eq_rect_sigT {A x} {P : A -> Type} (Q : forall a, P a -> Prop) (u : sigT (Q x)) {y} (H : x = y)
  : eq_rect x (fun a => sigT (Q a)) u y H
    = existT
        (Q y)
        (eq_rect x P (projT1 u) y H)
        match H in (_ = y) return Q y (eq_rect x P (projT1 u) y H) with
          | eq_refl => projT2 u
        end.
admit.
Defined.
End sigT.

Section sig.
  Definition proj1_sig_path {A} {P : A -> Prop} {u v : sig P} (p : u = v)
  : proj1_sig u = proj1_sig v
    := f_equal (@proj1_sig _ _) p.

  Definition proj2_sig_path {A} {P : A -> Prop} {u v : sig P} (p : u = v)
  : eq_rect _ _ (proj2_sig u) _ (proj1_sig_path p) = proj2_sig v.
admit.
Defined.

  Definition path_sig_uncurried {A : Type} (P : A -> Prop) (u v : sig P)
             (pq : {p : proj1_sig u = proj1_sig v | eq_rect _ _ (proj2_sig u) _ p = proj2_sig v})
  : u = v.
admit.
Defined.

  Definition path_sig {A : Type} (P : A -> Prop) (u v : sig P)
             (p : proj1_sig u = proj1_sig v) (q : eq_rect _ _ (proj2_sig u) _ p = proj2_sig v)
  : u = v
    := path_sig_uncurried u v (exist _ p q).

  Lemma eq_rect_sig {A x} {P : A -> Type} (Q : forall a, P a -> Prop) (u : sig (Q x)) {y} (H : x = y)
  : eq_rect x (fun a => sig (Q a)) u y H
    = exist
        (Q y)
        (eq_rect x P (proj1_sig u) y H)
        match H in (_ = y) return Q y (eq_rect x P (proj1_sig u) y H) with
          | eq_refl => proj2_sig u
        end.
admit.
Defined.
End sig.

Section ex.
  Definition path_ex_uncurried' {A : Type} (P : A -> Prop) {u1 v1 : A} {u2 : P u1} {v2 : P v1}
             (pq : exists p : u1 = v1, eq_rect _ _ u2 _ p = v2)
  : ex_intro P u1 u2 = ex_intro P v1 v2.
admit.
Defined.

  Definition path_ex' {A : Type} (P : A -> Prop) (u1 v1 : A) (u2 : P u1) (v2 : P v1)
             (p : u1 = v1) (q : eq_rect _ _ u2 _ p = v2)
  : ex_intro P u1 u2 = ex_intro P v1 v2
    := path_ex_uncurried' P (ex_intro _ p q).

  Lemma eq_rect_ex {A x} {P : A -> Type} (Q : forall a, P a -> Prop) (u : ex (Q x)) {y} (H : x = y)
  : eq_rect x (fun a => ex (Q a)) u y H
    = match u with
        | ex_intro u1 u2
          => ex_intro
               (Q y)
               (eq_rect x P u1 y H)
               match H in (_ = y) return Q y (eq_rect x P u1 y H) with
                 | eq_refl => u2
               end
      end.
admit.
Defined.
End ex.

Lemma eq_rect_const {A x P} (u : P) {y} (H : x = y)
: @eq_rect A x (fun _ => P) u y H = u.
admit.
Defined.

Lemma in_map_iff_injective {A B} (f : A -> B) (l : list A) (y : A)
      (f_injective : forall x, f x = f y -> x = y)
: In (f y) (map f l) <-> In y l.
admit.
Defined.

Section option.
  Context {A : Type}.

  Definition option_code (x y : option A) : Prop
    := match x, y with
         | Some x', Some y' => x' = y'
         | None, None => True
         | _, _ => False
       end.

  Definition option_code_idpath {x} : option_code x x
    := match x return option_code x x with
         | Some _ => eq_refl
         | None => I
       end.

  Definition option_encode {x y} (p : x = y) : option_code x y
    := eq_rect _ _ option_code_idpath _ p.

  Definition option_decode {x y} : option_code x y -> x = y
    := match x, y return option_code x y -> x = y with
         | Some x', Some y' => @f_equal _ _ (@Some _) _ _
         | None, None => fun _ => eq_refl
         | _, _ => fun H => match H : False with end
       end.

  Definition option_deenecode {x y} (p : x = y)
  : option_decode (option_encode p) = p.
admit.
Defined.

  Definition option_endecode {x y} (p : option_code x y)
  : option_encode (option_decode p) = p.
admit.
Defined.

  Definition Some_injective {x y : A} : Some x = Some y -> x = y
    := option_encode.
End option.

Section sum.
  Context {A B : Type}.

  Definition sum_code (x y : A + B) : Prop
    := match x, y with
         | inl x', inl y' => x' = y'
         | inr x', inr y' => x' = y'
         | _, _ => False
       end.

  Definition sum_code_idpath {x} : sum_code x x
    := match x return sum_code x x with
         | inl _ => eq_refl
         | inr _ => eq_refl
       end.

  Definition sum_encode {x y} (p : x = y) : sum_code x y
    := eq_rect _ _ sum_code_idpath _ p.

  Definition sum_decode {x y} : sum_code x y -> x = y
    := match x, y return sum_code x y -> x = y with
         | inl x', inl y' => @f_equal _ _ (@inl _ _) _ _
         | inr x', inr y' => @f_equal _ _ (@inr _ _) _ _
         | _, _ => fun H => match H : False with end
       end.

  Definition sum_deenecode {x y} (p : x = y)
  : sum_decode (sum_encode p) = p.
admit.
Defined.

  Definition sum_endecode {x y} (p : sum_code x y)
  : sum_encode (sum_decode p) = p.
admit.
Defined.

  Definition inl_injective {x y : A} : inl x = inl y -> x = y
    := sum_encode.

  Definition inr_injective {x y : B} : inr x = inr y -> x = y
    := sum_encode.
End sum.

Definition prod_dec {A B}
           (HA : forall a b : A, {a = b} + {a <> b})
           (HB : forall a b : B, {a = b} + {a <> b})
: forall a b : A * B, {a = b} + {a <> b}.
admit.
Defined.

Definition option_dec {A}
           (H : forall a b : A, {a = b} + {a <> b})
: forall a b : option A, {a = b} + {a <> b}.
admit.
Defined.

Class BoolDecR A := beq : A -> A -> bool.
Global Arguments beq {A _} _ _.
Class BoolDec_bl `{BoolDecR A} (R : relation A)
  := bl : forall x y, beq x y = true -> R x y.
Global Arguments bl {A _ R _} [_ _] _.
Class BoolDec_lb `{BoolDecR A} (R : relation A)
  := lb : forall x y, R x y -> beq x y = true.
Global Arguments lb {A _ R _} [_ _] _.

Definition beq_true_iff `{BoolDecR A} {R : relation A}
           {_ : BoolDec_bl R} {_ : BoolDec_lb R}
           x y
  : beq x y <-> R x y.
admit.
Defined.

Section lift.
  Context {A : Type} {R : relation A}
          {dec : @BoolDecR A}
          {Hbl : @BoolDec_bl A dec R}
          {Hlb : @BoolDec_lb A dec R}.

  Instance beq_Reflexive {_ : @Reflexive A R} : Reflexive beq.
admit.
Defined.

  Instance beq_Symmetric {_ : @Symmetric A R} : Symmetric beq.
admit.
Defined.

  Instance beq_Transitive {_ : @Transitive A R} : Transitive beq.
admit.
Defined.

  Instance beq_Asymmetric {_ : @Asymmetric A R} : Asymmetric beq.
admit.
Defined.

  Instance beq_Antisymmetric {ER} {_ : Equivalence ER} {_ : @Antisymmetric A ER _ R}
  : Antisymmetric A ER beq.
admit.
Defined.
End lift.

Section of_dec.
  Context {A} {R : relation A}
          (dec : forall x y, {R x y} + {~R x y}).
End of_dec.

Section to_dec.
End to_dec.
Scheme Equality for string.

Module Export ImproperlyRecursiveProdBeq.
  Scheme Equality for prod.
End ImproperlyRecursiveProdBeq.

Definition prod_beq {A B} eq_A eq_B (x y : A * B) : bool
  := Eval unfold ImproperlyRecursiveProdBeq.prod_beq in
      @ImproperlyRecursiveProdBeq.prod_beq A B eq_A eq_B (fst x, snd x) (fst y, snd y).

Section beq_correct.
End beq_correct.

Section In.
  Section list_bin.
    Context {A} (eq_A : A -> A -> bool) (a : A).

    Fixpoint list_bin (ls : list A) : bool
      := match ls with
           | nil => false
           | x::xs => orb (list_bin xs) (eq_A x a)
         end.
  End list_bin.
End In.

End Equality.

End Common.

End Fiat.

End Fiat_DOT_Common_DOT_Equality.

Module Export Fiat_DOT_Common_DOT_Instances.
Module Export Fiat.
Module Export Common.
Module Export Instances.
Import Coq.Classes.Morphisms.
Export Fiat.Common.Coq__8_4__8_5__Compat.
Global Instance drop_0_Proper {A B RA RB} {f : B}
       {H : Proper RB f}
: Proper (RA ==> RB) (fun _ : A => f).
admit.
Defined.
Global Instance and_iff_iff_iff_Proper : Proper (iff ==> iff ==> iff) and | 1
  := _.

End Instances.

End Common.

End Fiat.

End Fiat_DOT_Common_DOT_Instances.

Module Export Fiat_DOT_Common_DOT_List_DOT_Operations.
Module Export Fiat.
Module Export Common.
Module Export List.
Module Export Operations.

Import Coq.Lists.List.

Module Export List.

 Definition uniquize {A} (beq : A -> A -> bool) (ls : list A) : list A
    := fold_right
         (fun x xs => if list_bin beq x xs then xs else x::xs)
         nil
         ls.

  Fixpoint up_to (n : nat) : list nat :=
    match n with
      | 0 => nil
      | S n' => n'::up_to n'
    end.

  End List.

End Operations.

End List.

End Common.

End Fiat.

End Fiat_DOT_Common_DOT_List_DOT_Operations.

Module Export Fiat_DOT_Common_DOT_LogicFacts.
Module Export Fiat.
Module Export Common.
Module Export LogicFacts.

Section LogicFacts.
  Lemma ex_distr_or A B C
  : (exists x : A, B x \/ C x) <-> ((exists x : A, B x) \/ (exists x : A, C x)).
admit.
Defined.
  Lemma forall_distr_and {A B C}
    : (forall x : A, B x /\ C x) <-> ((forall x, B x) /\ (forall x, C x)).
admit.
Defined.
  Lemma ex_eq_and {A P} y
    : (exists x : A, y = x /\ P x) <-> P y.
admit.
Defined.
  Lemma ex_eq'_and {A P} y
    : (exists x : A, x = y /\ P x) <-> P y.
admit.
Defined.
  Lemma ex_eq_snd_and {A B C} x
    : (exists y : A * B, snd y = x /\ C y) <-> (exists y : A, C (y, x)).
admit.
Defined.
  Lemma ex_eq'_snd_and {A B C} x
    : (exists y : A * B, x = snd y /\ C y) <-> (exists y : A, C (y, x)).
admit.
Defined.
  Lemma ex_eq_fst_and {A B C} x
    : (exists y : A * B, fst y = x /\ C y) <-> (exists y : B, C (x, y)).
admit.
Defined.
  Lemma ex_eq'_fst_and {A B C} x
    : (exists y : A * B, x = fst y /\ C y) <-> (exists y : B, C (x, y)).
admit.
Defined.
  Lemma forall_eq_and {A C} {D : _ -> Prop} x
    : (forall y : A, y = x /\ C y -> D y) <-> (C x -> D x).
admit.
Defined.
  Lemma forall_eq'_and {A C} {D : _ -> Prop} x
    : (forall y : A, x = y /\ C y -> D y) <-> (C x -> D x).
admit.
Defined.
  Lemma forall_eq_snd_and {A B C} {D : _ -> Prop} x
    : (forall y : A * B, snd y = x /\ C y -> D y) <-> (forall y : A, C (y, x) -> D (y, x)).
admit.
Defined.
  Lemma forall_eq'_snd_and {A B C} {D : _ -> Prop} x
    : (forall y : A * B, x = snd y /\ C y -> D y) <-> (forall y : A, C (y, x) -> D (y, x)).
admit.
Defined.
  Lemma forall_eq_fst_and {A B C} {D : _ -> Prop} x
    : (forall y : A * B, fst y = x /\ C y -> D y) <-> (forall y : B, C (x, y) -> D (x, y)).
admit.
Defined.
  Lemma forall_eq'_fst_and {A B C} {D : _ -> Prop} x
    : (forall y : A * B, x = fst y /\ C y -> D y) <-> (forall y : B, C (x, y) -> D (x, y)).
admit.
Defined.
  Lemma False_iff {P : Prop}
    : ~P -> (P <-> False).
admit.
Defined.
  Lemma False_impl_iff_True {P : Prop}
    : (False -> P) <-> True.
admit.
Defined.
End LogicFacts.
Ltac setoid_rewrite_logic_step :=
  first [ rewrite_strat repeat topdown hints logic
        | setoid_rewrite ex_distr_or
        | setoid_rewrite forall_distr_and
        | setoid_rewrite ex_eq'_and
        | setoid_rewrite ex_eq'_fst_and
        | setoid_rewrite ex_eq'_snd_and
        | setoid_rewrite ex_eq_and
        | setoid_rewrite ex_eq_fst_and
        | setoid_rewrite ex_eq_snd_and
        | setoid_rewrite forall_eq'_and
        | setoid_rewrite forall_eq'_fst_and
        | setoid_rewrite forall_eq'_snd_and
        | setoid_rewrite forall_eq_and
        | setoid_rewrite forall_eq_fst_and
        | setoid_rewrite forall_eq_snd_and
        | setoid_rewrite False_impl_iff_True ].
Ltac setoid_rewrite_logic := repeat setoid_rewrite_logic_step.

End LogicFacts.

End Common.

End Fiat.

End Fiat_DOT_Common_DOT_LogicFacts.

Module Export Fiat_DOT_Common_DOT_MSetExtensions.
Module Export Fiat.
Module Export Common.
Module Export MSetExtensions.
Export Coq.MSets.MSetInterface.
Import Coq.MSets.MSetProperties.
Import Fiat.Common.

Module MSetExtensionsOn (E: DecidableType) (Import M: WSetsOn E).
  Module Export BasicProperties := WPropertiesOn E M.

  Tactic Notation "setoid_rewrite_in_all" "guarded" tactic3(guard_tac) open_constr(lem) :=
    idtac;
    match goal with
    | [ |- ?G ] => guard_tac G; rewrite !lem
    | [ H : ?T |- _ ] => guard_tac T; rewrite !lem in H
    | [ |- ?G ] => guard_tac G; setoid_rewrite lem
    | [ H : ?T |- _ ] => guard_tac T; setoid_rewrite lem in H
    end.

  Tactic Notation "setoid_rewrite_in_all" "guarded" tactic3(guard_tac) "<-" open_constr(lem) :=
    idtac;
    match goal with
    | [ |- ?G ] => guard_tac G; rewrite <- !lem
    | [ H : ?T |- _ ] => guard_tac T; rewrite <- !lem in H
    | [ |- ?G ] => guard_tac G; setoid_rewrite <- lem
    | [ H : ?T |- _ ] => guard_tac T; setoid_rewrite <- lem in H
    end.

  Ltac eq_bools_to_is_trues :=
    idtac;
    let x := match goal with |- ?x = ?y :> bool => x end in
    let y := match goal with |- x = ?y :> bool => y end in
    let Hx := fresh in
    let Hy := fresh in
    destruct x eqn:Hx;
    [ symmetry
    | destruct y eqn:Hy;
      [ rewrite <- Hx; clear Hx
      | reflexivity ] ];
    fold_is_true.

  Ltac eq_bools_to_is_trues_in H :=
    idtac;
    let x := match type of H with ?x = ?y :> bool => x end in
    let y := match type of H with x = ?y :> bool => y end in
    let Hx := fresh in
    let Hy := fresh in
    destruct x eqn:Hx;
    [ symmetry
    | destruct y eqn:Hy;
      [ rewrite <- Hx; clear Hx
      | reflexivity ] ];
    fold_is_true.
  Ltac eq_bools_to_is_trues_in_all :=
    idtac;
    match goal with
    | [ H : _ = _ :> bool |- _ ]
      => eq_bools_to_is_trues_in H
    end.

  Ltac to_caps_step :=
    first [ setoid_rewrite_in_all guarded(fun T => match T with
                                                | context[subset _ _ = true] => idtac
                                                | context[is_true (subset _ _)] => idtac
                                                end)
                                  subset_spec
          | setoid_rewrite_in_all guarded(fun T => match T with
                                                | context[equal _ _ = true] => idtac
                                                | context[is_true (equal _ _)] => idtac
                                                end)
                                  equal_spec
          | setoid_rewrite_in_all guarded(fun T => match T with context[_ = false] => idtac end)
                                  <- not_true_iff_false
          | setoid_rewrite_in_all guarded(fun T => match T with
                                                | context[negb _ = true] => idtac
                                                | context[is_true (negb _)] => idtac
                                                end)
                                  negb_true_iff
          | setoid_rewrite_in_all guarded(fun T => match T with
                                                | context[mem _ _ = true] => idtac
                                                | context[is_true (mem _ _)] => idtac
                                                end)
                                  mem_spec
          | progress fold_is_true
          | progress eq_bools_to_is_trues
          | progress eq_bools_to_is_trues_in_all ].
  Ltac to_caps := repeat to_caps_step.

  Ltac simplify_sets_step :=
    idtac;
    match goal with
    | [ H : ?x [<=] ?y, H' : ?y [<=] ?x |- _ ]
      => pose proof (subset_antisym H H');
         clear H H'
    | [ H : context[subset ?x ?y] |- _ ]
      => match type of H with
         | context[subset y x] => fail 1
         | _ => idtac
         end;
         progress replace (equal y x) with (equal x y)
           in H by auto with sets
    | [ |- context[subset ?x ?y] ]
      => match goal with
         | [ |- context[subset y x] ] => fail 1
         | _ => idtac
         end;
         progress replace (equal y x) with (equal x y)
           by auto with sets
    | _ => setoid_subst_rel Equal
    end.

  Ltac simplify_sets := repeat simplify_sets_step.

  Ltac push_In_step :=
    first [ progress unfold Equal in *
          | setoid_rewrite_in_all guarded(fun T => match T with context[In _ (union _ _)] => idtac end)
                                  union_spec
          | setoid_rewrite_in_all guarded(fun T => match T with context[In _ (inter _ _)] => idtac end)
                                  inter_spec
          | setoid_rewrite_in_all guarded(fun T => match T with context[In _ (filter _ _)] => idtac end)
                                  filter_spec; [ | let H := fresh in intros ?? H; hnf in H; substs; reflexivity.. ] ].

  Ltac push_In := repeat push_In_step.
End MSetExtensionsOn.

Module MSetExtensions (M: Sets) := MSetExtensionsOn M.E M.

End MSetExtensions.

End Common.

End Fiat.

End Fiat_DOT_Common_DOT_MSetExtensions.

Module Export Fiat_DOT_Common_DOT_NatFacts.
Module Export Fiat.
Module Export Common.
Module Export NatFacts.

Lemma min_def {x y} : min x y = x - (x - y).
admit.
Defined.
Lemma max_def {x y} : max x y = x + (y - x).
admit.
Defined.
Ltac handle_min_max_for_omega :=
  repeat match goal with
         | [ H : context[min _ _] |- _ ] => rewrite !min_def in H
         | [ H : context[max _ _] |- _ ] => rewrite !max_def in H
         | [ |- context[min _ _] ] => rewrite !min_def
         | [ |- context[max _ _] ] => rewrite !max_def
         end.
Ltac omega_with_min_max :=
  handle_min_max_for_omega;
  omega.

End NatFacts.

End Common.

End Fiat.

End Fiat_DOT_Common_DOT_NatFacts.

Module Export Fiat_DOT_Common_DOT_Wf.
Module Export Fiat.
Module Export Common.
Module Export Wf.

Section wf.
  Global Instance well_founded_subrelation {A}
    : Proper (flip subrelation ==> impl) (@well_founded A).
admit.
Defined.

  Section wf_prodA.
    Context A B (eqA RA : relation A) (RB : relation B).

    Definition prod_relationA : relation (A * B)
      := fun ab a'b' =>
           RA (fst ab) (fst a'b') \/ (eqA (fst a'b') (fst ab) /\ RB (snd ab) (snd a'b')).

    Context (prod_relationA_Proper
             : forall b'', Proper (eqA ==> impl) (fun a => Acc prod_relationA (a, b''))).

    Global Instance prod_relationA_Proper_from_Equivalence
          (RA_Proper : Proper (eq ==> eqA ==> flip impl) RA)
          (eqA_Proper : Proper (eqA ==> eq ==> flip impl) eqA)
      : forall b'', Proper (eqA ==> impl) (fun a => Acc prod_relationA (a, b'')).
admit.
Defined.

    Section step.
      Context (well_founded_prod_relationA_helper
               : forall a b (wf_A : Acc RA a) (wf_B : well_founded RB),
                  Acc prod_relationA (a, b)).

      Definition well_founded_prod_relationA_helper_step
                 a b
                 (wf_A : Acc RA a) (wf_B : well_founded RB)
                 (wf_B_rec : forall (fa : forall y : A, RA y a -> Acc RA y) b' (wf_B' : Acc RB b'), Acc prod_relationA (a, b'))
        : Acc prod_relationA (a, b)
        := match wf_A with
           | Acc_intro fa => @wf_B_rec fa b (wf_B b)
           end.
      Definition wf_B_rec_step
                 (wf_B : well_founded RB)
                 a (fa : forall y : A, RA y a -> Acc RA y)
                 (wf_B_rec : forall b' (wf_B' : Acc RB b'), Acc prod_relationA (a, b'))
                 b' (wf_B' : Acc RB b')
        :  Acc prod_relationA (a, b').
      Proof.
        refine (Acc_intro _ _).
        intros [a'' b''] [pf'|[pfa pfb]].
        {
 refine (@well_founded_prod_relationA_helper
                    _ _
                    (fa _ pf')
                    wf_B).
}
        {
 refine match wf_B' with
                 | Acc_intro fb => @prod_relationA_Proper
                                     _ _ _ pfa
                                     (@wf_B_rec _ (fb _ pfb))
                 end.
}
      Defined.
    End step.

    Fixpoint well_founded_prod_relationA_helper
             a b
             (wf_A : Acc RA a) (wf_B : well_founded RB) {struct wf_A}
      : Acc prod_relationA (a, b)
      := @well_founded_prod_relationA_helper_step
           a b wf_A wf_B
           (fun fa
            => fix wf_B_rec b' (wf_B' : Acc RB b') : Acc prod_relationA (a, b')
            := @wf_B_rec_step
                 (@well_founded_prod_relationA_helper)
                 wf_B
                 a fa (@wf_B_rec)
                 b' wf_B').

    Definition well_founded_prod_relationA : well_founded RA -> well_founded RB -> well_founded prod_relationA.
    Proof.
      intros wf_A wf_B [a b]; hnf in *.
      apply well_founded_prod_relationA_helper; auto.
    Defined.
  End wf_prodA.

  End wf.

End Wf.

End Common.

End Fiat.

End Fiat_DOT_Common_DOT_Wf.

Module Export Fiat_DOT_Common_DOT_MSetBoundedLattice.
Module Export Fiat.
Module Export Common.
Module Export MSetBoundedLattice.

Module MSetBoundedLatticeOn (E: OrderedType) (Import M: SetsOn E).

  Definition lift_ltb (x y : t) : bool
    := ((subset x y) && negb (equal x y)).

  End MSetBoundedLatticeOn.

Module MSetBoundedLattice (M: S) := MSetBoundedLatticeOn M.E M.

End MSetBoundedLattice.

End Common.

End Fiat.

End Fiat_DOT_Common_DOT_MSetBoundedLattice.

Module Export Fiat_DOT_Common_DOT_Notations.
Module Export Fiat.
Module Export Common.
Module Export Notations.
Reserved Infix "⊔" (at level 80).

End Notations.

End Common.

End Fiat.

End Fiat_DOT_Common_DOT_Notations.

Module Export Fiat_DOT_Parsers_DOT_StringLike_DOT_Core.
Module Export Fiat.
Module Export Parsers.
Module Export StringLike.
Module Export Core.

Local Coercion is_true : bool >-> Sortclass.

Module Export StringLike.
  Class StringLikeMin {Char : Type} :=
    {
      String :> Type;
      char_at_matches : nat -> String -> (Char -> bool) -> bool;
      unsafe_get : nat -> String -> Char;
      length : String -> nat
    }.

  Class StringLike {Char : Type} {HSLM : @StringLikeMin Char} :=
    {
      is_char : String -> Char -> bool;
      take : nat -> String -> String;
      drop : nat -> String -> String;
      get : nat -> String -> option Char;
      bool_eq : String -> String -> bool;
      beq : relation String := fun x y => bool_eq x y
    }.

  Arguments StringLikeMin : clear implicits.
  Arguments StringLike Char {HSLM}.
  Delimit Scope string_like_scope with string_like.
  Infix "=s" := (@beq _ _ _) (at level 70, no associativity) : type_scope.
  Notation "s ~= [ ch ]" := (is_char s ch) (at level 70, no associativity) : string_like_scope.
  Local Open Scope string_like_scope.

  Class StringLikeProperties (Char : Type) `{StringLike Char} :=
    {
      singleton_unique : forall s ch ch', s ~= [ ch ] -> s ~= [ ch' ] -> ch = ch';
      singleton_exists : forall s, length s = 1 -> exists ch, s ~= [ ch ];
      char_at_matches_correct : forall s n P ch, get n s = Some ch -> (char_at_matches n s P = P ch);
      get_0 : forall s ch, take 1 s ~= [ ch ] <-> get 0 s = Some ch;
      get_S : forall n s, get (S n) s = get n (drop 1 s);
      unsafe_get_correct : forall n s ch, get n s = Some ch -> unsafe_get n s = ch;
      length_singleton : forall s ch, s ~= [ ch ] -> length s = 1;
      bool_eq_char : forall s s' ch, s ~= [ ch ] -> s' ~= [ ch ] -> s =s s';
      is_char_Proper :> Proper (beq ==> eq ==> eq) is_char;
      length_Proper :> Proper (beq ==> eq) length;
      take_Proper :> Proper (eq ==> beq ==> beq) take;
      drop_Proper :> Proper (eq ==> beq ==> beq) drop;
      bool_eq_Equivalence :> Equivalence beq;
      bool_eq_empty : forall str str', length str = 0 -> length str' = 0 -> str =s str';
      take_short_length : forall str n, n <= length str -> length (take n str) = n;
      take_long : forall str n, length str <= n -> take n str =s str;
      take_take : forall str n m, take n (take m str) =s take (min n m) str;
      drop_length : forall str n, length (drop n str) = length str - n;
      drop_0 : forall str, drop 0 str =s str;
      drop_drop : forall str n m, drop n (drop m str) =s drop (n + m) str;
      drop_take : forall str n m, drop n (take m str) =s take (m - n) (drop n str);
      take_drop : forall str n m, take n (drop m str) =s drop m (take (n + m) str);
      bool_eq_from_get : forall str str', (forall n, get n str = get n str') -> str =s str';
      strings_nontrivial : forall n, exists str, length str = n
    }.

  Arguments StringLikeProperties Char {_ _}.
End StringLike.

End Core.

End StringLike.

End Parsers.

End Fiat.

End Fiat_DOT_Parsers_DOT_StringLike_DOT_Core.

Module Export Fiat.
Module Export Parsers.
Module Export ContextFreeGrammar.
Module Export Core.
Export Fiat.Parsers.StringLike.Core.

End Core.

Section syntax.
  Context {Char : Type}.

  Inductive RCharExpr :=
  | rbeq (ch : Char)
  | ror (_ _ : RCharExpr)
  | rand (_ _ : RCharExpr)
  | rneg (_ : RCharExpr)
  | rcode_le_than (code : BinNums.N)
  | rcode_ge_than (code : BinNums.N).

  Inductive ritem :=
  | RTerminal (_ : RCharExpr)
  | RNonTerminal (_ : String.string).

  Definition rproduction := list ritem.
  Definition rproductions := list rproduction.
End syntax.
Global Arguments rproductions : clear implicits.

Section semantics.
  Context {Char : Type}.

  Class interp_RCharExpr_data :=
    { irbeq : Char -> Char -> bool;
      irN_of : Char -> BinNums.N }.
End semantics.

Global Arguments interp_RCharExpr_data : clear implicits.

Import Coq.Strings.String.

Class NoDupR {T} beq (ls : list T) := nodupr : uniquize beq ls = ls.

Record pregrammar Char :=
  {
    pregrammar_rproductions : list (string * rproductions Char);
    pregrammar_idata : interp_RCharExpr_data Char;
    pregrammar_rnonterminals : list string
    := map fst pregrammar_rproductions;
    rnonterminals_unique
    : NoDupR string_beq pregrammar_rnonterminals;
    RLookup_idx : nat -> rproductions Char
    := fun n => nth n (map snd pregrammar_rproductions) nil
  }.

Module Export Definitions.

Local Coercion is_true : bool >-> Sortclass.
Delimit Scope grammar_fixedpoint_scope with fixedpoint.
Local Open Scope grammar_fixedpoint_scope.

Inductive lattice_for T := top | constant (_ : T) | bottom.
Scheme Equality for lattice_for.

Arguments bottom {_}.
Arguments top {_}.
Notation "'⊥'" := bottom : grammar_fixedpoint_scope.
Notation "'⊤'" := top : grammar_fixedpoint_scope.

Global Instance lattice_for_Equivalence {T} {beq : T -> T -> bool}
       {H : Equivalence beq}
  : Equivalence (lattice_for_beq beq).
admit.
Defined.

Definition lattice_for_lt {T} (lt : T -> T -> bool) (x y : lattice_for T)
  := match x, y with
     | ⊤, ⊤ => false
     | constant x', constant y' => lt x' y'
     | ⊥, ⊥ => false
     | _, ⊤ => true
     | ⊤, _ => false
     | _, constant _ => true
     | constant _, _ => false
     end.

Global Instance lattice_for_lt_Proper {T} {beq lt : T -> T -> bool}
       {H : Proper (beq ==> beq ==> eq) lt}
  : Proper (lattice_for_beq beq ==> lattice_for_beq beq ==> eq) (lattice_for_lt lt).
admit.
Defined.

Definition lattice_for_lub {T} (lub : T -> T -> lattice_for T) (x y : lattice_for T)
  := match x, y with
     | ⊤, ⊤ => ⊤
     | constant x', constant y' => lub x' y'
     | ⊥, ⊥ => ⊥
     | ⊤, _
     | _, ⊤
       => ⊤
     | ⊥, v
     | v, ⊥
       => v
     end.

Section lub_correct.
  Context {T} (beq : T -> T -> bool) (lt : T -> T -> bool) (lub : T -> T -> lattice_for T).

  Local Notation "x <= y" := (orb (lattice_for_beq beq x y) (lattice_for_lt lt x y)).

  Context (lub_correct_l : forall x y, constant x <= lub x y)
          (lub_correct_r : forall x y, constant y <= lub x y)
          (beq_Reflexive : Reflexive beq).

  Lemma lattice_for_lub_correct_l x y
    : x <= lattice_for_lub lub x y.
  Proof.
    clear lub_correct_r.
    destruct x as [|x|], y as [|y|]; try reflexivity.
    {
 exact (lub_correct_l x y).
}
    {
 simpl.
      rewrite (reflexivity x : is_true (beq x x)).
      reflexivity.
}
  Qed.

  Lemma lattice_for_lub_correct_r x y
    : y <= lattice_for_lub lub x y.
  Proof.
    clear lub_correct_l.
    destruct x as [|x|], y as [|y|]; try reflexivity.
    {
 exact (lub_correct_r x y).
}
    {
 simpl.
      rewrite (reflexivity y : is_true (beq y y)).
      reflexivity.
}
  Qed.

  Global Instance lattice_for_lub_Proper
         {lub_Proper : Proper (beq ==> beq ==> lattice_for_beq beq) lub}
    : Proper (lattice_for_beq beq ==> lattice_for_beq beq ==> lattice_for_beq beq) (lattice_for_lub lub).
admit.
Defined.
End lub_correct.

Definition lattice_for_gt_well_founded {T} {lt : T -> T -> bool}
           (gt_wf : well_founded (Basics.flip lt))
  : well_founded (Basics.flip (lattice_for_lt lt)).
admit.
Defined.

Global Instance lattice_for_lt_Transitive {T} {lt : T -> T -> bool} {_ : Transitive lt}
  : Transitive (lattice_for_lt lt).
admit.
Defined.

Class grammar_fixedpoint_lattice_data prestate :=
  { state :> _ := lattice_for prestate;
    prestate_lt : prestate -> prestate -> bool;
    state_lt : state -> state -> bool
    := lattice_for_lt prestate_lt;
    prestate_beq : prestate -> prestate -> bool;
    state_beq : state -> state -> bool
    := lattice_for_beq prestate_beq;
    prestate_le s1 s2 := (prestate_beq s1 s2 || prestate_lt s1 s2)%bool;
    state_le s1 s2 := (state_beq s1 s2 || state_lt s1 s2)%bool;
    prestate_beq_Equivalence : Equivalence prestate_beq;
    state_beq_Equivalence : Equivalence state_beq
    := lattice_for_Equivalence;
    preleast_upper_bound : prestate -> prestate -> state;
    least_upper_bound : state -> state -> state
    := lattice_for_lub preleast_upper_bound;
    preleast_upper_bound_correct_l
    : forall a b, state_le (constant a) (preleast_upper_bound a b);
    preleast_upper_bound_correct_r
    : forall a b, state_le (constant b) (preleast_upper_bound a b);
    least_upper_bound_correct_l
    : forall a b, state_le a (least_upper_bound a b)
    := lattice_for_lub_correct_l prestate_beq prestate_lt preleast_upper_bound preleast_upper_bound_correct_l _;
    least_upper_bound_correct_r
    : forall a b, state_le b (least_upper_bound a b)
    := lattice_for_lub_correct_r prestate_beq prestate_lt preleast_upper_bound preleast_upper_bound_correct_r _;
    prestate_gt_wf : well_founded (Basics.flip prestate_lt);
    state_gt_wf : well_founded (Basics.flip state_lt)
    := lattice_for_gt_well_founded prestate_gt_wf;
    preleast_upper_bound_Proper : Proper (prestate_beq ==> prestate_beq ==> state_beq) preleast_upper_bound;
    least_upper_bound_Proper : Proper (state_beq ==> state_beq ==> state_beq) least_upper_bound
    := @lattice_for_lub_Proper _ _ _ _;
    prestate_lt_Proper : Proper (prestate_beq ==> prestate_beq ==> eq) prestate_lt;
    state_lt_Proper : Proper (state_beq ==> state_beq ==> eq) state_lt
    := lattice_for_lt_Proper;
    prestate_lt_Transitive : Transitive prestate_lt;
    state_lt_Transitive : Transitive state_lt
    := lattice_for_lt_Transitive }.
Global Existing Instance state_beq_Equivalence.
Global Existing Instance state_lt_Proper.
Global Existing Instance least_upper_bound_Proper.

Infix "<=" := (@state_le _ _) : grammar_fixedpoint_scope.
Infix "⊔" := (@least_upper_bound _ _) : grammar_fixedpoint_scope.

Global Instance lattice_for_rect_Proper_85 {A}
  : Proper (eq ==> forall_relation (fun _ => eq) ==> eq ==> eq ==> Basics.flip Basics.impl)
           (@lattice_for_rect A (fun _ => Prop)) | 3.
admit.
Defined.

Lemma lattice_for_rect_pull {A B C} f t c b v
  : f (@lattice_for_rect A (fun _ => B) t c b v)
    = @lattice_for_rect A (fun _ => C) (f t) (fun x => f (c x)) (f b) v.
admit.
Defined.

End Definitions.

Module Export AsciiLattice.
Import Coq.Strings.Ascii.
Import Coq.MSets.MSetPositive.

Module PositiveSetBoundedLattice := MSetBoundedLattice PositiveSet.
Module Import PositiveSetExtensions := MSetExtensions PositiveSet.

Section gen.
  Global Instance positive_set_fpdata
    : grammar_fixedpoint_lattice_data PositiveSet.t.
admit.
Defined.
End gen.

Definition max_ascii := Eval compute in BinPos.Pos.of_nat (S (nat_of_ascii (Ascii true true true true true true true true))).

End AsciiLattice.

Module Export Properties.
Import Fiat.Common.
Local Open Scope grammar_fixedpoint_scope.

Global Instance state_beq_Proper_Proper {prestate} {d : grammar_fixedpoint_lattice_data prestate}
  : Proper (state_beq ==> state_beq ==> eq) state_beq.
admit.
Defined.

Global Instance state_beq_Proper_le {prestate} {d : grammar_fixedpoint_lattice_data prestate}
  : Proper (state_beq ==> state_beq ==> eq) state_le.
admit.
Defined.

Global Instance state_le_Transitive {T d} : Transitive (@state_le T d).
admit.
Defined.

Lemma bottom_lub_r {prestate} {d : grammar_fixedpoint_lattice_data prestate} (s : state)
  : (s ⊔ ⊥) = s.
admit.
Defined.

Lemma bottom_lub_l {prestate} {d : grammar_fixedpoint_lattice_data prestate} (s : state)
  : (⊥ ⊔ s) = s.
admit.
Defined.

Global Instance state_le_Antisymmetric {prestate} {fpdata : grammar_fixedpoint_lattice_data prestate}
  : Antisymmetric _ state_beq state_le.
admit.
Defined.

End Properties.

Module Export FromAbstractInterpretationDefinitions.
Import Coq.Sets.Ensembles.
Import Fiat.Parsers.ContextFreeGrammar.Core.
Local Coercion is_true : bool >-> Sortclass.
Local Open Scope grammar_fixedpoint_scope.

Section general_fold.
  Context {Char : Type}
          {T : Type}.

  Definition lattice_for_combine_production combine_production
    : lattice_for T -> lattice_for T -> lattice_for T
    := fun x y => match x, y with
                  | ⊥, _
                  | _, ⊥
                    => ⊥
                  | ⊤, _
                  | _, ⊤
                    => ⊤
                  | constant x', constant y'
                    => combine_production x' y'
                  end.

  Global Instance lattice_for_combine_production_Proper
         {prestate_beq : T -> T -> bool}
         {precombine_production}
         {H : Proper (prestate_beq ==> prestate_beq ==> lattice_for_beq prestate_beq) precombine_production}
    : Proper (lattice_for_beq prestate_beq ==> lattice_for_beq prestate_beq ==> lattice_for_beq prestate_beq) (lattice_for_combine_production precombine_production).
admit.
Defined.

  Context {fpdata : @grammar_fixedpoint_lattice_data T}.

  Class AbstractInterpretation :=
    { on_terminal : (Char -> bool) -> lattice_for T;
      on_nil_production : lattice_for T;
      precombine_production : T -> T -> lattice_for T;
      combine_production : lattice_for T -> lattice_for T -> lattice_for T
      := lattice_for_combine_production precombine_production;
      precombine_production_Proper : Proper (prestate_beq ==> prestate_beq ==> state_beq) precombine_production;
      combine_production_Proper : Proper (state_beq ==> state_beq ==> state_beq) combine_production
      := lattice_for_combine_production_Proper }.

  Global Existing Instance precombine_production_Proper.

  End general_fold.

Section on_ensembles.
  Context {Char : Type} {HSLM : StringLikeMin Char} {HSL : StringLike Char}.

  Definition ensemble_on_terminal (P : Char -> bool) : Ensemble String
    := (fun str => exists ch, is_true (P ch) /\ str ~= [ ch ])%string_like.

  Definition ensemble_on_nil_production : Ensemble String
    := (fun str => length str = 0).

  Definition ensemble_combine_production : Ensemble String -> Ensemble String -> Ensemble String
    := fun P1 P2 => fun str => exists n, P1 (take n str) /\ P2 (drop n str).

  Definition ensemble_least_upper_bound : Ensemble String -> Ensemble String -> Ensemble String
    := fun P1 P2 => fun str => P1 str \/ P2 str.
End on_ensembles.

Section fold_correctness.
  Context {Char : Type} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char}.
  Context {T : Type}.
  Context {fpdata : @grammar_fixedpoint_lattice_data T}
          {aidata : @AbstractInterpretation Char T fpdata}.
  Context (G : pregrammar Char)
          (prerelated : Ensemble String -> T -> Prop).

  Definition lattice_for_related (P : Ensemble String) (st : lattice_for T) : Prop
    := match st with
       | ⊤ => True
       | ⊥ => forall str, ~P str
       | constant n => prerelated P n
       end.

  Section related.
    Local Notation related := lattice_for_related.

    Global Instance lattice_for_related_ext {_ : Proper ((beq ==> iff) ==> prestate_beq ==> iff) prerelated}
      : Proper ((beq ==> iff) ==> state_beq ==> iff) related | 2.
    Proof.
      intros ?? H' [|?|] [|?|] ?; simpl in *;
        try tauto;
        try congruence;
        try (apply H; assumption);
        try setoid_rewrite H';
        try setoid_rewrite (fun x => H' x x (reflexivity _));
        try reflexivity.
    Qed.

    Global Instance lattice_for_combine_production_Proper_le
           {precombine_production'}
           {H : Proper (prestate_le ==> prestate_le ==> state_le) precombine_production'}
      : Proper (state_le ==> state_le ==> state_le) (lattice_for_combine_production precombine_production').
admit.
Defined.
  End related.

  Class AbstractInterpretationCorrectness :=
    { prerelated_ext : Proper ((beq ==> iff) ==> prestate_beq ==> iff) prerelated;
      related : Ensemble String -> state -> Prop
      := lattice_for_related;
      related_ext : Proper ((beq ==> iff) ==> state_beq ==> iff) related
      := lattice_for_related_ext;
      related_monotonic : forall s0 s1, s0 <= s1 -> (forall v, related v s0 -> related v s1);
      lub_correct
      : forall P1 st1,
          related P1 st1
          -> forall P2 st2,
            related P2 st2
            -> related (ensemble_least_upper_bound P1 P2) (least_upper_bound st1 st2);
      on_terminal_correct
      : forall P,
          related (ensemble_on_terminal P) (on_terminal P);
      on_nil_production_correct
      : related ensemble_on_nil_production on_nil_production;
      precombine_production_Proper_le
      : Proper (prestate_le ==> prestate_le ==> state_le) precombine_production;
      combine_production_Proper_le
      : Proper (state_le ==> state_le ==> state_le) combine_production
      := _;
      combine_production_correct
      : forall P1 st1,
          related P1 st1
          -> forall P2 st2,
            related P2 st2
            -> related (ensemble_combine_production P1 P2) (combine_production st1 st2)
    }.
End fold_correctness.

End FromAbstractInterpretationDefinitions.
Import Fiat.Common.BoolFacts.
Import Fiat.Common.

Global Instance prod_fixedpoint_lattice {prestate0 prestate1}
       {fpldata0 : grammar_fixedpoint_lattice_data prestate0}
       {fpldata1 : grammar_fixedpoint_lattice_data prestate1}
  : grammar_fixedpoint_lattice_data (@state _ fpldata0 * @state _ fpldata1).
Proof.
  refine {| prestate_lt x y := ((state_le (fst x) (fst y) && state_le (snd x) (snd y))
                                  && negb (state_beq (fst x) (fst y) && state_beq (snd x) (snd y)));
            prestate_beq := Equality.prod_beq state_beq state_beq;
            preleast_upper_bound x y
            := constant (least_upper_bound (fst x) (fst y), least_upper_bound (snd x) (snd y)) |};
  try abstract (
        repeat match goal with
               | _ => progress unfold Equality.prod_beq
               | [ |- RelationClasses.Equivalence _ ]
                 => split; repeat intro
               | [ |- well_founded _ ] => fail 1
               | [ |- is_true (?R ?x ?x) ] => reflexivity
               | [ |- is_true true ] => reflexivity
               | [ |- ?R ?x ?x ] => reflexivity
               | _ => congruence
               | [ |- Proper _ _ ] => unfold Proper, respectful
               | [ |- Transitive _ ] => intros ???; cbv beta
               | _ => progress intros
               | [ H : and _ _ |- _ ] => destruct H
               | [ H : prod _ _ |- _ ] => destruct H
               | _ => progress simpl in *
               | [ H : is_true (state_beq ?x ?y) |- _ ]
                 => rewrite H in *; clear x H
               | [ H : is_true (state_beq ?x ?y) |- _ ]
                 => clear x H
               | [ |- context[(?x <= least_upper_bound ?x ?y)%fixedpoint] ]
                 => replace (x <= least_upper_bound x y)%fixedpoint
                    with true by (symmetry; apply least_upper_bound_correct_l)
               | [ |- context[(?y <= least_upper_bound ?x ?y)%fixedpoint] ]
                 => replace (y <= least_upper_bound x y)%fixedpoint
                    with true by (symmetry; apply least_upper_bound_correct_r)
               | [ H : is_true true |- _ ] => clear H
               | [ H : is_true ?x |- context[?x] ]
                 => progress replace x with true by (symmetry; exact H)
               | [ H : is_true ?x, H' : context[?x] |- _ ]
                 => progress replace x with true in H' by (symmetry; exact H)
               | [ H : context[@state_beq ?A ?B ?x ?x] |- _ ]
                 => replace (@state_beq A B x x) with true in H by (symmetry; change (is_true (@state_beq A B x x)); reflexivity)
               | [ H : is_true (?R ?x ?y), H' : is_true (?R ?y ?z) |- _ ]
                 => unique pose proof (transitivity (R := R) H H' : is_true (R x z))
               | [ H : is_true (@state_le ?A ?B ?x ?y), H' : is_true (state_le ?y ?x) |- _ ]
                 => unique pose proof (@antisymmetry _ (@state_beq A B) _ (@state_le A B) _ x y H H' : is_true (state_beq x y))
               | [ |- context[is_true (negb ?x)] ]
                 => destruct x eqn:?; simpl; fold_is_true
               | _ => progress bool_congr_setoid
               | [ |- and _ _ ] => split
               end
      ).
  {
 unfold flip.
    eapply well_founded_subrelation; [ | eapply well_founded_prod_relationA with (eqA := state_beq) ];
      [ .. | eapply state_gt_wf | eapply state_gt_wf ].
    {
 intros x y H.
      unfold prod_relationA, flip, state_le, state in *.
      revert H.
      generalize (@state_lt _ fpldata0).
      generalize (@state_lt _ fpldata1).
      generalize (@state_beq _ fpldata0).
      generalize (@state_beq _ fpldata1).
      unfold state.
      clear.
 admit.
}
    {
 apply prod_relationA_Proper_from_Equivalence; try exact _; [].
      unfold flip; intros ??? x y H H'; subst.
      rewrite H; assumption.
}
 }
Defined.

Global Instance prod_fixedpoint_lattice' {prestate0 prestate1}
       {fpldata0 : grammar_fixedpoint_lattice_data prestate0}
       {fpldata1 : grammar_fixedpoint_lattice_data prestate1}
  : grammar_fixedpoint_lattice_data (lattice_for prestate0 * lattice_for prestate1)
  := prod_fixedpoint_lattice.
Import Fiat.Parsers.StringLike.Core.

Section String.
  Context {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char}.

  Lemma take_length {str n}
  : length (take n str) = min n (length str).
admit.
Defined.

  Global Instance beq_subrelation_pointwise_iff {A} {R : relation A}
    : subrelation (beq ==> R)%signature (pointwise_relation String R).
  Proof.
    intros f g H x.
    specialize (H x x (reflexivity _)); assumption.
  Qed.
End String.

Module Export ProdAbstractInterpretationDefinitions.
Import Coq.Sets.Ensembles.

Lemma simplify_bool_expr a b (Himpl : is_true a -> is_true b)
  : (a || (b && negb a))%bool = b.
admit.
Defined.

Lemma simplify_bool_expr' a b (Himpl : is_true a -> is_true b)
  : (a || (b && negb a))%bool -> b.
admit.
Defined.

Section aidata.
  Context {Char : Type} {T T0 T1}
          {fpldata : grammar_fixedpoint_lattice_data T}
          {fpldata0 : grammar_fixedpoint_lattice_data T0}
          {fpldata1 : grammar_fixedpoint_lattice_data T1}.

  Definition prod_on_terminal
             (on_terminal0 : (Char -> bool) -> lattice_for T0)
             (on_terminal1 : (Char -> bool) -> lattice_for T1)
    : (Char -> bool) -> lattice_for (lattice_for T0 * lattice_for T1)
    := fun P => constant (on_terminal0 P, on_terminal1 P).

  Definition prod_on_nil_production
             (on_nil_production0 : lattice_for T0)
             (on_nil_production1 : lattice_for T1)
    : lattice_for (lattice_for T0 * lattice_for T1)
    := constant (on_nil_production0, on_nil_production1).

  Definition prod_precombine_production_dep
             (precombine_production0 : T0 -> T0 -> lattice_for T0)
             (precombine_production1 : lattice_for T0 -> lattice_for T0 -> T1 -> T1 -> lattice_for T1)
    : (lattice_for T0 * lattice_for T1) -> (lattice_for T0 * lattice_for T1) -> lattice_for (lattice_for T0 * lattice_for T1)
    := fun x y => constant (lattice_for_combine_production precombine_production0 (fst x) (fst y),
                            lattice_for_combine_production (precombine_production1 (fst x) (fst y)) (snd x) (snd y)).

  Definition prod_precombine_production_nondep
             (precombine_production0 : T0 -> T0 -> lattice_for T0)
             (precombine_production1 : T1 -> T1 -> lattice_for T1)
    : (lattice_for T0 * lattice_for T1) -> (lattice_for T0 * lattice_for T1) -> lattice_for (lattice_for T0 * lattice_for T1)
    := fun x y => constant (lattice_for_combine_production precombine_production0 (fst x) (fst y),
                            lattice_for_combine_production precombine_production1 (snd x) (snd y)).

  Global Instance prod_precombine_production_dep_Proper
         {precombine_production0 : T0 -> T0 -> lattice_for T0}
         {precombine_production1 : lattice_for T0 -> lattice_for T0 -> T1 -> T1 -> lattice_for T1}
         {HP0 : Proper (prestate_beq ==> prestate_beq ==> state_beq) precombine_production0}
         {HP1 : Proper (state_beq ==> state_beq ==> prestate_beq ==> prestate_beq ==> state_beq) precombine_production1}
    : Proper (prestate_beq ==> prestate_beq ==> state_beq) (prod_precombine_production_dep precombine_production0 precombine_production1).
admit.
Defined.

  Definition prod_aidata_dep
             (on_terminal0 : (Char -> bool) -> lattice_for T0)
             (on_nil_production0 : lattice_for T0)
             (precombine_production0 : T0 -> T0 -> lattice_for T0)
             (on_terminal1 : (Char -> bool) -> lattice_for T1)
             (on_nil_production1 : lattice_for T1)
             (precombine_production1 : lattice_for T0 -> lattice_for T0 -> T1 -> T1 -> lattice_for T1)
             (precombine_production0_Proper
              : Proper (prestate_beq ==> prestate_beq ==> state_beq) precombine_production0)
             (precombine_production1_Proper
              : Proper (state_beq ==> state_beq ==> prestate_beq ==> prestate_beq ==> state_beq) precombine_production1)
    : @AbstractInterpretation Char (lattice_for T0 * lattice_for T1) prod_fixedpoint_lattice'.
  Proof.
    refine {| on_terminal := prod_on_terminal on_terminal0 on_terminal1;
              on_nil_production := prod_on_nil_production on_nil_production0 on_nil_production1;
              precombine_production := prod_precombine_production_dep precombine_production0 precombine_production1 |}.
  Defined.

  Global Instance prod_precombine_production_dep_Proper_le
         {precombine_production0 : T0 -> T0 -> lattice_for T0}
         {precombine_production1 : lattice_for T0 -> lattice_for T0 -> T1 -> T1 -> lattice_for T1}
         {HP0 : Proper (prestate_le ==> prestate_le ==> state_le) precombine_production0}
         {HP1 : Proper (state_le ==> state_le ==> prestate_le ==> prestate_le ==> state_le) precombine_production1}
    : Proper (prestate_le ==> prestate_le ==> state_le) (prod_precombine_production_dep precombine_production0 precombine_production1).
admit.
Defined.

  Global Instance prod_precombine_production_nondep_dep_Proper_le
         {precombine_production0 : lattice_for T -> lattice_for T -> T0 -> T0 -> lattice_for T0}
         {precombine_production1 : lattice_for T -> lattice_for T -> T1 -> T1 -> lattice_for T1}
         {HP0 : Proper (state_le ==> state_le ==> prestate_le ==> prestate_le ==> state_le) precombine_production0}
         {HP1 : Proper (state_le ==> state_le ==> prestate_le ==> prestate_le ==> state_le) precombine_production1}
    : Proper (state_le ==> state_le ==> prestate_le ==> prestate_le ==> state_le) (fun x y => prod_precombine_production_nondep (precombine_production0 x y) (precombine_production1 x y)).
admit.
Defined.
End aidata.

Section aicdata.
  Context {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char}
          {T0 T1}
          {fpldata0 : grammar_fixedpoint_lattice_data T0}
          {fpldata1 : grammar_fixedpoint_lattice_data T1}
          (prerelated0 : Ensemble String -> T0 -> Prop)
          (prerelated1 : Ensemble String -> T1 -> Prop).

  Definition prod_prerelated : Ensemble String -> (lattice_for T0 * lattice_for T1) -> Prop
    := fun P st
       => lattice_for_related prerelated0 P (fst st)
          /\ lattice_for_related prerelated1 P (snd st).

  Local Ltac t_step :=
    idtac;
    match goal with
    | _ => intro
    | _ => progress unfold prod_prerelated, ensemble_least_upper_bound, ensemble_combine_production in *
    | _ => progress simpl in *
    | [ |- and _ True ] => split; [ | tauto ]
    | [ |- and True _ ] => split; [ tauto | ]
    | [ H : ?R _ _, H' : is_true _ |- _ ] => specialize (H _ _ H')
    | [ H : ?R _ _, H' : ?R' _ _ |- _ ] => specialize (H _ _ H')
    | _ => progress destruct_head and
    | [ H : is_true (Equality.prod_beq _ _ _ _) |- _ ]
      => unfold Equality.prod_beq in H;
         apply Bool.andb_true_iff in H
    | _ => progress fold_is_true
    | _ => progress destruct_head prod
    | _ => progress destruct_head ex
    | [ |- (lattice_for_related _ _ _ /\ lattice_for_related _ _ _)
           <-> (lattice_for_related _ _ _ /\ lattice_for_related _ _ _) ]
      => apply and_iff_iff_iff_Proper
    | [ H : is_true (state_beq ?x ?y) |- _ ]
      => lazymatch goal with
         | [ |- context[x] ]
           => fail
         | [ |- context[y] ]
           => fail
         | _ => clear dependent x
         end
    | _ => solve [ unfold not in *; eauto; destruct_head or; eauto ]
    | [ H : context[(_ ⊔ ⊥)%fixedpoint] |- _ ]
      => setoid_rewrite bottom_lub_r in H
    | [ H : context[(⊥ ⊔ _)%fixedpoint] |- _ ]
      => setoid_rewrite bottom_lub_l in H
    | _ => progress rewrite ?bottom_lub_r, ?bottom_lub_l
    | [ H : is_true (state_le ?x ?y) |- _ ] => is_var x; destruct x
    | [ H : is_true (state_le ?x ?y) |- _ ] => is_var y; destruct y
    | [ H : is_true (_ || (_ && negb _)) |- _ ]
      => apply simplify_bool_expr' in H; [ | unfold state_le; bool_congr_setoid; tauto ];
         try apply Bool.andb_true_iff in H
    | [ x : lattice_for (_ * _) |- _ ] => destruct x
    | [ x : lattice_for _ |- _ ] => destruct x
    | _ => congruence
    | _ => tauto
    | [ H : (_ ==> _)%signature (?f _) (?g _) |- _ ]
      => lazymatch goal with
         | [ |- context[f] ]
           => fail
         | [ |- context[g] ]
           => fail
         | _ => clear dependent f
         end
    | _ => progress setoid_subst_rel (beq ==> iff)%signature
    | [ |- and _ _ ] => split
    end.

  Local Ltac t := repeat t_step.

  Global Instance prod_prerelated_ext
         {prerelated0_ext : Proper ((beq ==> iff) ==> prestate_beq ==> iff) prerelated0}
         {prerelated1_ext : Proper ((beq ==> iff) ==> prestate_beq ==> iff) prerelated1}
    : Proper ((beq ==> iff) ==> prestate_beq ==> iff) prod_prerelated.
  Proof.
t.
Qed.

  Lemma prod_related_monotonic
         {related0_monotonic : forall s0 s1, (s0 <= s1)%fixedpoint -> forall v, lattice_for_related prerelated0 v s0 -> lattice_for_related prerelated0 v s1}
         {related1_monotonic : forall s0 s1, (s0 <= s1)%fixedpoint -> forall v, lattice_for_related prerelated1 v s0 -> lattice_for_related prerelated1 v s1}
    : forall s0 s1, (s0 <= s1)%fixedpoint -> forall v, lattice_for_related prod_prerelated v s0 -> lattice_for_related prod_prerelated v s1.
admit.
Defined.

  Lemma prod_lub_correct
        (lub0_correct : forall P1 st1,
            lattice_for_related prerelated0 P1 st1
            -> forall P2 st2,
              lattice_for_related prerelated0 P2 st2
              -> lattice_for_related prerelated0 (ensemble_least_upper_bound P1 P2) (st1 ⊔ st2)%fixedpoint)
        (lub1_correct : forall P1 st1,
            lattice_for_related prerelated1 P1 st1
            -> forall P2 st2,
              lattice_for_related prerelated1 P2 st2
              -> lattice_for_related prerelated1 (ensemble_least_upper_bound P1 P2) (st1 ⊔ st2)%fixedpoint)
    : forall P1 st1,
      lattice_for_related prod_prerelated P1 st1
      -> forall P2 st2,
        lattice_for_related prod_prerelated P2 st2
        -> lattice_for_related prod_prerelated (ensemble_least_upper_bound P1 P2) (st1 ⊔ st2)%fixedpoint.
admit.
Defined.

  Lemma prod_on_terminal_correct
        (on_terminal0 : (Char -> bool) -> lattice_for T0)
        (on_terminal1 : (Char -> bool) -> lattice_for T1)
        (on_terminal0_correct : forall P, lattice_for_related prerelated0 (ensemble_on_terminal P) (on_terminal0 P))
        (on_terminal1_correct : forall P, lattice_for_related prerelated1 (ensemble_on_terminal P) (on_terminal1 P))
    : forall P, lattice_for_related prod_prerelated (ensemble_on_terminal P) (prod_on_terminal on_terminal0 on_terminal1 P).
admit.
Defined.

  Lemma prod_on_nil_production_correct
        (on_nil_production0 : lattice_for T0)
        (on_nil_production1 : lattice_for T1)
        (on_nil_production0_correct : lattice_for_related prerelated0 ensemble_on_nil_production on_nil_production0)
        (on_nil_production1_correct : lattice_for_related prerelated1 ensemble_on_nil_production on_nil_production1)
    : lattice_for_related prod_prerelated ensemble_on_nil_production (prod_on_nil_production on_nil_production0 on_nil_production1).
admit.
Defined.

  Lemma prod_combine_production_dep_correct
        (precombine_production0 : T0 -> T0 -> lattice_for T0)
        (precombine_production1 : lattice_for T0 -> lattice_for T0 -> T1 -> T1 -> lattice_for T1)
        (combine_production0_correct : forall P1 st1,
            lattice_for_related prerelated0 P1 st1
            -> forall P2 st2,
              lattice_for_related prerelated0 P2 st2
              -> lattice_for_related prerelated0 (ensemble_combine_production P1 P2) (lattice_for_combine_production precombine_production0 st1 st2))
        (combine_production1_correct : forall P1 st1 st10,
            lattice_for_related prerelated0 P1 st10
            -> lattice_for_related prerelated1 P1 st1
            -> forall P2 st2 st20,
              lattice_for_related prerelated0 P2 st20
              -> lattice_for_related prerelated1 P2 st2
              -> lattice_for_related prerelated1 (ensemble_combine_production P1 P2) (lattice_for_combine_production (precombine_production1 st10 st20) st1 st2))
    : forall P1 st1,
      lattice_for_related prod_prerelated P1 st1
      -> forall P2 st2,
        lattice_for_related prod_prerelated P2 st2
        -> lattice_for_related prod_prerelated (ensemble_combine_production P1 P2) (lattice_for_combine_production (prod_precombine_production_dep precombine_production0 precombine_production1) st1 st2).
admit.
Defined.

  Lemma prod_combine_production_nondep_correct_specific
        (precombine_production0 : T0 -> T0 -> lattice_for T0)
        (precombine_production1 : T1 -> T1 -> lattice_for T1)
        P1 st1
        (Hrel1 : lattice_for_related prod_prerelated P1 st1)
        P2 st2
        (Hrel2 : lattice_for_related prod_prerelated P2 st2)
        (combine_production0_correct
         : forall st1v,
            st1 = constant st1v
            -> forall st2v,
              st2 = constant st2v
              -> lattice_for_related prerelated0 (ensemble_combine_production P1 P2) (lattice_for_combine_production precombine_production0 (fst st1v) (fst st2v)))
        (combine_production1_correct
         : forall st1v,
            st1 = constant st1v
            -> forall st2v,
              st2 = constant st2v
              -> lattice_for_related prerelated1 (ensemble_combine_production P1 P2) (lattice_for_combine_production precombine_production1 (snd st1v) (snd st2v)))
    : lattice_for_related prod_prerelated (ensemble_combine_production P1 P2) (lattice_for_combine_production (prod_precombine_production_nondep precombine_production0 precombine_production1) st1 st2).
admit.
Defined.
End aicdata.

Global Arguments prod_prerelated_ext {_ _ _ _ T0 T1 _ _ prerelated0 prerelated1} _ _ _ _ _ _ _ _.
Global Arguments prod_related_monotonic {_ _ T0 T1 _ _ prerelated0 prerelated1} _ _ _ _ _ _ _.
Global Arguments prod_lub_correct {_ _ T0 T1 _ _ prerelated0 prerelated1} _ _ _ _ _ _ _ _.
Global Arguments prod_on_terminal_correct {_ _ _ T0 T1 prerelated0 prerelated1 on_terminal0 on_terminal1} _ _ _.
Global Arguments prod_on_nil_production_correct {_ _ T0 T1 prerelated0 prerelated1 on_nil_production0 on_nil_production1} _ _.
Global Arguments prod_precombine_production_dep_Proper_le {T0 T1 _ _ precombine_production0 precombine_production1} _ _ _ _ _ _ _ _.
Global Arguments prod_combine_production_dep_correct {_ _ _ T0 T1 prerelated0 prerelated1 precombine_production0 precombine_production1} _ _ _ _ _ _ _ _.
Global Arguments prod_precombine_production_nondep_dep_Proper_le {T T0 T1 _ _ _ precombine_production0 precombine_production1} _ _ _ _ _ _ _ _ _ _ _ _ _ _.

End ProdAbstractInterpretationDefinitions.

Local Open Scope grammar_fixedpoint_scope.

Inductive nonemptyT := nonempty | could_be_empty.

Global Instance might_be_empty_lattice : grammar_fixedpoint_lattice_data nonemptyT.
admit.
Defined.

Global Instance might_be_empty_aidata {Char} : @AbstractInterpretation Char nonemptyT _.
admit.
Defined.

Section correctness.
  Context {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char}.

  Definition might_be_empty_accurate
             (P : String -> Prop) (nonemptyv : nonemptyT)
    : Prop
    := nonemptyv = nonempty -> forall str, P str -> length str <> 0.

  Global Instance might_be_empty_aicdata
    : AbstractInterpretationCorrectness might_be_empty_accurate.
admit.
Defined.
End correctness.

Definition might_be_emptyT := lattice_for nonemptyT.
Coercion collapse_might_be_empty (x : might_be_emptyT) : bool
  := match x with
     | ⊤ => true
     | constant could_be_empty => true
     | constant nonempty => false
     | ⊥ => false
     end.
Local Open Scope string_like_scope.

Section forall_chars.
  Context {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char}.

  Definition forall_chars (str : String) (P : Char -> Prop)
    := forall n ch,
         take 1 (drop n str) ~= [ ch ]
         -> P ch.

  Global Instance forall_chars_Proper
  : Proper (beq ==> pointwise_relation _ impl ==> impl) forall_chars.
admit.
Defined.

  Lemma forall_chars_nil (str : String) P
  : length str = 0 -> forall_chars str P.
admit.
Defined.

  Lemma forall_chars__split (str : String) P n
  : forall_chars str P
    <-> (forall_chars (take n str) P /\ forall_chars (drop n str) P).
admit.
Defined.

  Lemma forall_chars_singleton (str : String) P ch
  : str ~= [ ch ] -> (P ch <-> forall_chars str P).
admit.
Defined.
End forall_chars.

Section for_first_char.
  Context {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char}.

  Definition for_first_char (str : String) (P : Char -> Prop)
    := forall ch,
         take 1 str ~= [ ch ]
         -> P ch.

  Global Instance for_first_char_Proper
  : Proper (beq ==> pointwise_relation _ impl ==> impl) for_first_char.
admit.
Defined.

  Lemma for_first_char_nil (str : String) P
  : length str = 0 -> for_first_char str P.
admit.
Defined.

  Lemma for_first_char_singleton (str : String) P ch
  : str ~= [ ch ] -> (P ch <-> for_first_char str P).
admit.
Defined.

  Lemma for_first_char__split (str : String) P n
  : for_first_char str P
    <-> ((n = 0 /\ for_first_char (drop n str) P)
         \/ (n <> 0 /\ for_first_char (take n str) P)).
admit.
Defined.
End for_first_char.

Section for_last_char.
  Context {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char}.

  Definition for_last_char (str : String) (P : Char -> Prop)
    := forall ch,
         drop (pred (length str)) str ~= [ ch ]
         -> P ch.

  Global Instance for_last_char_Proper
  : Proper (beq ==> pointwise_relation _ impl ==> impl) for_last_char.
admit.
Defined.

  Lemma for_last_char_nil (str : String) P
  : length str = 0 -> for_last_char str P.
admit.
Defined.

  Lemma for_last_char_singleton (str : String) P ch
  : str ~= [ ch ] -> (P ch <-> for_last_char str P).
admit.
Defined.

  Lemma for_last_char__split (str : String) P n
  : for_last_char str P
    <-> ((n < length str /\ for_last_char (drop n str) P)
         \/ (n >= length str /\ for_last_char (take n str) P)).
admit.
Defined.
End for_last_char.

Import Coq.MSets.MSetPositive.

Definition all_possible_ascii' : PositiveSet.t
  := List.fold_right
       PositiveSet.add
       PositiveSet.empty
       (List.map (fun x => BinPos.Pos.of_nat (S x))
                 (Operations.List.up_to (S (Ascii.nat_of_ascii (Ascii.Ascii true true true true true true true true))))).

Definition all_possible_ascii : PositiveSet.t
  := Eval compute in all_possible_ascii'.

Definition pos_of_ascii (x : Ascii.ascii) : BinNums.positive
  := match Ascii.N_of_ascii x with
     | BinNums.N0 => max_ascii
     | BinNums.Npos x => x
     end.

Lemma ascii_of_pos_of_ascii x : Ascii.ascii_of_pos (pos_of_ascii x) = x.
admit.
Defined.

Definition all_but (P : Ascii.ascii -> bool) : PositiveSet.t
  := PositiveSet.filter (fun n => negb (P (Ascii.ascii_of_pos n))) all_possible_ascii.

Lemma not_In_all_but P ch
  : (~PositiveSet.In (pos_of_ascii ch) (all_but P)) <-> P ch.
admit.
Defined.

  Definition possible_terminals_prestate
    := (@state _ might_be_empty_lattice
        * lattice_for
            (lattice_for
               (@state _ positive_set_fpdata
                * @state _ positive_set_fpdata )
             * @state _ positive_set_fpdata ))%type.

  Global Instance possible_terminals_aidata : @AbstractInterpretation Ascii.ascii possible_terminals_prestate _.
  Proof.
    refine (@prod_aidata_dep
              _ _ _ _ _
              on_terminal
              (@on_nil_production Ascii.ascii _ _ might_be_empty_aidata)
              (@precombine_production Ascii.ascii _ _ might_be_empty_aidata)
              (prod_on_terminal
                 (prod_on_terminal
                    (fun P => constant (all_but P))
                    (fun P => constant (all_but P)))
                 (fun P => constant (all_but P)))
              (prod_on_nil_production
                 (prod_on_nil_production
                    (constant all_possible_ascii)
                    (constant all_possible_ascii))
                 (constant all_possible_ascii))
              (fun xmbe ymbe
               => prod_precombine_production_nondep
                    (prod_precombine_production_nondep
                       (fun x' y'
                        => constant (if collapse_might_be_empty xmbe
                                     then PositiveSet.inter x' y'
                                     else x'))
                       (fun x' y'
                        => constant (if collapse_might_be_empty ymbe
                                     then PositiveSet.inter x' y'
                                     else y')))
                    (fun x' y'
                     => constant (PositiveSet.inter x' y')))
              _ _).
    intros x0 y0 H0 x1 y1 H1 x2 y2 H2 x3 y3 H3.
    repeat match goal with
           | [ H : is_true (state_beq ?x ?y) |- context[collapse_might_be_empty ?x] ]
             => replace (collapse_might_be_empty x)
                with (collapse_might_be_empty y)
               by (rewrite H; reflexivity);
                  clear x H
           end.
    repeat first [ eapply @prod_precombine_production_nondep_Proper
                 | eassumption
                 | match goal with
                   | [ |- context[collapse_might_be_empty ?v] ]
                     => destruct (collapse_might_be_empty v)
                   end ];
      clear; admit.
  Defined.

Section correctness.
  Context {HSLM : StringLikeMin Ascii.ascii} {HSL : StringLike Ascii.ascii} {HSLP : StringLikeProperties Ascii.ascii}.

  Definition possible_accurate
    : forall (P : String -> Prop) (st : possible_terminals_prestate), Prop
    := prod_prerelated
         might_be_empty_accurate
         (prod_prerelated
            (prod_prerelated
               (fun P st
                => forall str, P str -> for_first_char str (fun ch => ~PositiveSet.In (pos_of_ascii ch) st))
               (fun P st
                => forall str, P str -> for_last_char str (fun ch => ~PositiveSet.In (pos_of_ascii ch) st)))
            (fun P st
             => forall str, P str -> forall_chars str (fun ch => ~PositiveSet.In (pos_of_ascii ch) st))).

  Local Ltac pull_lattice_for_rect :=
    repeat lazymatch goal with
           | [ |- context G[match ?v with ⊤ => ?T | ⊥ => ?B | constant x => @?C x end] ]
             => let RT := type of T in
                let G' := context G[lattice_for_rect (fun _ => RT) T C B v] in
                change G'
           | [ |- context G[fun k : ?KT => match @?v k with ⊤ => @?T k | ⊥ => @?B k | constant x => @?C k x end] ]
             => let RT := match type of T with forall k, @?RT k => RT end in
                let G' := context G[fun k : KT => lattice_for_rect (fun _ => RT k) (T k) (C k) (B k) (v k)] in
                change G'; cbv beta
           | [ |- context G[fun k : ?KT => ?f match @?v k with ⊤ => @?T k | ⊥ => @?B k | constant x => @?C k x end (@?arg k)] ]
             => let RT := match type of T with forall k, @?RT k => RT end in
                let G' := context G[fun k : KT => f (lattice_for_rect (fun _ => RT k) (T k) (C k) (B k) (v k)) (arg k)] in
                change G'; cbv beta
           | [ |- context G[fun k : ?KT => ?f (@?arg k) match @?v k with ⊤ => @?T k | ⊥ => @?B k | constant x => @?C k x end] ]
             => let RT := match type of T with forall k, @?RT k => RT end in
                let G' := context G[fun k : KT => f (arg k) (lattice_for_rect (fun _ => RT k) (T k) (C k) (B k) (v k))] in
                change G'; cbv beta
           end;
    rewrite !(fun A T T' x y z => lattice_for_rect_pull (A := A) (lattice_for_rect (T := T) (fun _ => T') x y z));
    setoid_rewrite (fun A T T' x y z => lattice_for_rect_pull (A := A) (lattice_for_rect (T := T) (fun _ => T') x y z)).

  Local Ltac handle_match_two_lattice_either_bottom_same :=
    idtac;
    lazymatch goal with
    | [ |- match ?l1 with ⊤ => match ?l2 with _ => _ end | ⊥ => ?P | _ => _ end ]
      => let H := fresh in
         assert (H : (l1 = ⊥ \/ l2 = ⊥) \/ (l1 <> ⊥ /\ l2 <> ⊥))
           by (destruct l1;
               [ destruct l2; [ right; split; congruence.. | left; right; reflexivity ]..
               | left; left; reflexivity ]);
         destruct H as [H|H];
         [ cut P; [ destruct l1, l2; trivial; destruct H; congruence | ]
         | destruct l1, l2, H; try exact I; try congruence; [] ]
    end.

  Local Ltac clear_unused_T T :=
    repeat match goal with
           | [ x : T |- _ ]
             => lazymatch goal with
                | [ |- context[x] ] => fail
                | _ => clear dependent x
                end
           end.

  Local Ltac t_step :=
    idtac;
    match goal with
    | [ |- ?R ?x ?x ] => reflexivity
    | _ => assumption
    | _ => congruence
    | _ => tauto
    | _ => progress unfold Proper, respectful, possible_accurate, flip, PositiveSetBoundedLattice.lift_ltb, ensemble_least_upper_bound, ensemble_on_terminal, ensemble_on_nil_production, prestate_le, ensemble_combine_production, Equality.prod_beq, might_be_empty_accurate in *
    | _ => progress intros
    | _ => progress simpl in *
    | [ H : is_true (?a || (?b && negb ?a)) |- _ ]
      => apply simplify_bool_expr' in H;
         [ | clear; unfold state_le; simpl; bool_congr_setoid; tauto ]
    | [ |- context[(?a || (?b && negb ?a))%bool] ]
      => rewrite (@simplify_bool_expr a b) by (clear; unfold state_le; simpl; bool_congr_setoid; tauto)
    | [ H : forall x y, _ -> (?f x <-> ?g y) |- _ ]
      => setoid_rewrite (fun x => H x x (reflexivity _));
         clear f H
    | [ H : lattice_for_related _ _ ?x |- _ ] => is_var x; destruct x
    | [ |- lattice_for_related _ _ ?x ] => is_var x; destruct x
    | [ H : ?x = ?x -> _ |- _ ] => specialize (H eq_refl)
    | _ => progress destruct_head ex
    | _ => progress destruct_head and
    | _ => progress subst
    | _ => progress bool_congr_setoid
    | _ => progress PositiveSetExtensions.simplify_sets
    | _ => progress PositiveSetExtensions.to_caps
    | [ H : is_true (is_char ?str _) |- forall_chars ?str _ ]
      => setoid_rewrite <- (forall_chars_singleton _ _ _ H)
    | [ H : is_true (is_char ?str _) |- for_first_char ?str _ ]
      => setoid_rewrite <- (for_first_char_singleton _ _ _ H)
    | [ H : is_true (is_char ?str _) |- for_last_char ?str _ ]
      => setoid_rewrite <- (for_last_char_singleton _ _ _ H)
    | _ => progress autorewrite with sets in *
    | [ H : PositiveSet.Subset ?x _ |- forall_chars _ (fun ch => ~PositiveSet.In _ ?x) ]
      => setoid_subst x
    | [ H : PositiveSet.Subset ?x _ |- for_first_char _ (fun ch => ~PositiveSet.In _ ?x) ]
      => setoid_subst x
    | [ H : PositiveSet.Subset ?x _ |- for_last_char _ (fun ch => ~PositiveSet.In _ ?x) ]
      => setoid_subst x
    | _ => solve [ eauto using forall_chars_nil, for_first_char_nil, for_last_char_nil with nocore
                 | auto with sets
                 | exfalso; unfold not in *; eauto with nocore ]
    | _ => progress PositiveSetExtensions.push_In
    | [ H : forall str, ?P str -> forall_chars str _, H' : ?P _ |- _ ]
      => unique pose proof (H _ H')
    | [ H : forall str, ?P str -> for_first_char str _, H' : ?P _ |- _ ]
      => unique pose proof (H _ H')
    | [ H : forall str, ?P str -> for_last_char str _, H' : ?P _ |- _ ]
      => unique pose proof (H _ H')
    | _ => eapply forall_chars_Proper; [ reflexivity | intros ?? | eassumption ];
           cbv beta in *; tauto
    | _ => progress destruct_head or
    | _ => progress destruct_head nonemptyT
    | [ |- ~(or _ _) ] => intro
    | _ => setoid_rewrite not_In_all_but
    | [ H : forall v, ~?P v |- context[?P _] ]
      => setoid_rewrite (fun v => False_iff (H v))
    | _ => progress setoid_rewrite_logic
    | [ H : forall_chars (take ?n ?str) (fun ch => ~@?P ch),
            H' : forall_chars (drop ?n ?str) (fun ch => ~@?P' ch)
        |- forall_chars ?str (fun ch => ~(@?P ch /\ @?P' ch)) ]
      => setoid_rewrite (forall_chars__split str _ n); split
    | [ H : for_first_char ?str (fun ch => ~@?P ch) |- for_first_char ?str (fun ch => ~(@?P ch /\ @?P' ch)) ]
      => eapply for_first_char_Proper; [ reflexivity | intros ?? | eexact H ]
    | [ H : for_first_char ?str (fun ch => ~@?P' ch) |- for_first_char ?str (fun ch => ~(@?P ch /\ @?P' ch)) ]
      => eapply for_first_char_Proper; [ reflexivity | intros ?? | eexact H ]
    | [ H : for_last_char ?str (fun ch => ~@?P ch) |- for_last_char ?str (fun ch => ~(@?P ch /\ @?P' ch)) ]
      => eapply for_last_char_Proper; [ reflexivity | intros ?? | eexact H ]
    | [ H : for_last_char ?str (fun ch => ~@?P' ch) |- for_last_char ?str (fun ch => ~(@?P ch /\ @?P' ch)) ]
      => eapply for_last_char_Proper; [ reflexivity | intros ?? | eexact H ]
    | [ H : for_first_char (drop ?x ?str) _, H' : for_first_char (take ?x ?str) _ |- for_first_char ?str _ ]
      => rewrite (for_first_char__split str _ x); destruct x; [ left | right ]; (split; [ omega | ])
    | [ H : for_last_char (drop ?x ?str) _, H' : for_last_char (take ?x ?str) _ |- for_last_char ?str _ ]
      => rewrite (for_last_char__split str _ x); destruct (Compare_dec.le_lt_dec (length str) x); [ right | left ]; (split; [ assumption | ])
    | [ H : forall str, ?P str -> length str <> 0, H' : ?P (take 0 ?str') |- _ ]
      => exfalso; apply (H _ H'); rewrite take_length; omega_with_min_max
    | [ H : forall str, ?P str -> length str <> 0, Hlt : (length ?str' <= ?x)%nat, H' : ?P (drop ?x ?str') |- _ ]
      => exfalso; apply (H _ H'); rewrite drop_length; omega_with_min_max
    | [ |- context[collapse_might_be_empty ?st] ]
      => is_var st; destruct st
    | [ H : PositiveSet.Subset ?x _ |- PositiveSet.Subset (PositiveSet.inter _ _) _ ]
      => progress setoid_subst_rel PositiveSet.Subset; auto with sets
    | _ => rewrite ascii_of_pos_of_ascii
    end.

  Local Ltac t := repeat t_step.

  Global Instance constant_inter_Proper
    : Proper (prestate_le ==> prestate_le ==> state_le) (fun x' y' => constant (PositiveSet.inter x' y')).
admit.
Defined.

  Local Ltac t_combine_pre :=
    repeat first [ assumption
                 | progress intros
                 | progress subst
                 | progress cbv [prod_prerelated ensemble_combine_production lattice_for_related might_be_empty_accurate lattice_for_combine_production] in *
                 | progress simpl in *
                 | progress destruct_head prod
                 | progress destruct_head and
                 | progress clear_unused_T (lattice_for PositiveSet.t) ].
  Local Ltac t_combine :=
    t_combine_pre;
    pull_lattice_for_rect;
    unfold lattice_for_rect; simpl; handle_match_two_lattice_either_bottom_same;
    t.

  Local Obligation Tactic := intros.

  Global Program Instance possible_aicdata
    : AbstractInterpretationCorrectness possible_accurate
    := { prerelated_ext
         := prod_prerelated_ext
              (@prerelated_ext Ascii.ascii _ _ _ _ _ _ _ might_be_empty_aicdata)
              (prod_prerelated_ext (prod_prerelated_ext _ _) _);
         related_monotonic
         := prod_related_monotonic
              (@related_monotonic Ascii.ascii _ _ _ _ _ _ _ might_be_empty_aicdata)
              (prod_related_monotonic (prod_related_monotonic _ _) _);
         lub_correct
         := prod_lub_correct
              (@lub_correct Ascii.ascii _ _ _ _ _ _ _ might_be_empty_aicdata)
              (prod_lub_correct (prod_lub_correct _ _) _);
         on_terminal_correct
         := prod_on_terminal_correct
              (@on_terminal_correct Ascii.ascii _ _ _ _ _ _ _ might_be_empty_aicdata)
              (prod_on_terminal_correct (prod_on_terminal_correct _ _) _);
         on_nil_production_correct
         := prod_on_nil_production_correct
              (@on_nil_production_correct Ascii.ascii _ _ _ _ _ _ _ might_be_empty_aicdata)
              (prod_on_nil_production_correct (prod_on_nil_production_correct _ _) _);
         precombine_production_Proper_le
         := prod_precombine_production_dep_Proper_le
              (@precombine_production_Proper_le Ascii.ascii _ _ _ _ _ _ _ might_be_empty_aicdata)
              (prod_precombine_production_nondep_dep_Proper_le (prod_precombine_production_nondep_dep_Proper_le _ _) _);
         combine_production_correct
         := prod_combine_production_dep_correct
              (@combine_production_correct Ascii.ascii _ _ _ _ _ _ _ might_be_empty_aicdata)
              (fun P1 st1 st10 R10 R1 P2 st2 st20 R20 R2
               => prod_combine_production_nondep_correct_specific
                    _ _ _ _ _ _ _ _
                    (fun st1v Hst1v st2v Hst2v
                     => prod_combine_production_nondep_correct_specific
                          _ _ _ _ _ _ _ _ _ _)
                    _)
       }.
  Next Obligation.
admit.
Defined.
  Next Obligation.
admit.
Defined.
  Next Obligation.
admit.
Defined.
  Next Obligation.
admit.
Defined.
  Next Obligation.
admit.
Defined.
  Next Obligation.
admit.
Defined.
  Next Obligation.
admit.
Defined.
  Next Obligation.
admit.
Defined.
  Next Obligation.
admit.
Defined.
  Next Obligation.
admit.
Defined.
  Next Obligation.
admit.
Defined.
  Next Obligation.
admit.
Defined.
  Next Obligation.
admit.
Defined.
  Next Obligation.
admit.
Defined.
  Next Obligation.
admit.
Defined.
  Next Obligation.
admit.
Defined.
  Next Obligation.
admit.
Defined.
  Next Obligation.
admit.
Defined.
  Next Obligation.
admit.
Defined.
  Next Obligation.
admit.
Defined.
  Next Obligation.
admit.
Defined.
  Next Obligation.
admit.
Defined.
  Next Obligation.
{
 t_combine.
