(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "-deprecated-native-compiler-option" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/metacoq/template-coq/theories" "MetaCoq.Template" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/metacoq/pcuic/theories" "MetaCoq.PCUIC" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/metacoq/safechecker/theories" "MetaCoq.SafeChecker" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Equations" "Equations" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-I" "/github/workspace/builds/coq/coq-failing/_build_ci/metacoq/template-coq/build" "-top" "bug_01" "-native-compiler" "no") -*- *)
(* File reduced by coq-bug-finder from original input, then from 419 lines to 163 lines, then from 310 lines to 591 lines, then from 594 lines to 174 lines, then from 320 lines to 1716 lines, then from 1716 lines to 203 lines, then from 318 lines to 1849 lines, then from 1849 lines to 579 lines, then from 691 lines to 1070 lines, then from 1070 lines to 594 lines, then from 705 lines to 2430 lines, then from 2426 lines to 728 lines, then from 835 lines to 982 lines, then from 985 lines to 755 lines, then from 863 lines to 2799 lines, then from 2799 lines to 931 lines, then from 1035 lines to 2914 lines, then from 2913 lines to 1076 lines, then from 1175 lines to 2095 lines, then from 2097 lines to 1105 lines, then from 1195 lines to 1369 lines, then from 1373 lines to 1155 lines, then from 1245 lines to 1363 lines, then from 1367 lines to 1165 lines, then from 1253 lines to 2291 lines, then from 2290 lines to 1773 lines, then from 1794 lines to 1692 lines, then from 1780 lines to 2513 lines, then from 2516 lines to 1707 lines, then from 1788 lines to 2241 lines, then from 2240 lines to 1833 lines, then from 1913 lines to 4126 lines, then from 4109 lines to 2297 lines, then from 2370 lines to 2417 lines, then from 2420 lines to 2303 lines, then from 2377 lines to 2796 lines, then from 2798 lines to 2386 lines, then from 2458 lines to 2501 lines, then from 2505 lines to 2394 lines, then from 2464 lines to 2700 lines, then from 2702 lines to 2678 lines *)
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
Require Coq.Init.Nat.
Require Coq.ZArith.ZArith.
Require Coq.Bool.Bool.
Require Coq.Strings.String.
Require Coq.micromega.Lia.
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
Require Coq.Arith.Arith.
Require Coq.ssr.ssreflect.
Require Coq.Lists.SetoidList.
Require Coq.Classes.CRelationClasses.
Require Equations.Type.Logic.
Require Equations.Type.Relation.
Require Equations.Type.Relation_Properties.
Require MetaCoq.Template.utils.MCRelations.
Require MetaCoq.Template.utils.MCList.
Require Coq.Classes.RelationClasses.
Require MetaCoq.Template.utils.MCProd.
Require MetaCoq.Template.utils.MCOption.
Require MetaCoq.Template.utils.MCSquash.
Require MetaCoq.Template.utils.All_Forall.
Require MetaCoq.Template.utils.MCArith.
Require Coq.Structures.OrderedType.
Require Coq.Strings.Ascii.
Require MetaCoq.Template.utils.MCCompare.
Require MetaCoq.Template.utils.MCEquality.
Require Coq.Init.Decimal.
Require Coq.Numbers.DecimalString.
Require MetaCoq.Template.utils.MCString.
Require MetaCoq.Template.utils.MCUtils.
Module Export MetaCoq_DOT_Template_DOT_monad_utils_WRAPPED.
Module Export monad_utils.
Import Coq.Arith.Arith.
Import Coq.Lists.List.
Import MetaCoq.Template.utils.All_Forall.
Import MetaCoq.Template.utils.MCSquash.
Import Equations.Prop.Equations.
Coercion is_true : bool >-> Sortclass.

Import ListNotations.

Set Universe Polymorphism.

Class Monad@{d c} (m : Type@{d} -> Type@{c}) : Type :=
{ ret : forall {t : Type@{d}}, t -> m t
; bind : forall {t u : Type@{d}}, m t -> (t -> m u) -> m u
}.

Class MonadExc E (m : Type -> Type) : Type :=
{ raise : forall {T}, E -> m T
; catch : forall {T}, m T -> (E -> m T) -> m T
}.

Module Export MCMonadNotation.
  Declare Scope monad_scope.
  Delimit Scope monad_scope with monad.

  Notation "c >>= f" := (@bind _ _ _ _ c f) (at level 50, left associativity) : monad_scope.
  Notation "f =<< c" := (@bind _ _ _ _ c f) (at level 51, right associativity) : monad_scope.

  Notation "'mlet' x <- c1 ;; c2" := (@bind _ _ _ _ c1 (fun x => c2))
    (at level 100, c1 at next level, right associativity, x pattern) : monad_scope.

  Notation "'mlet' ' pat <- c1 ;; c2" := (@bind _ _ _ _ c1 (fun x => match x with pat => c2 end))
    (at level 100, pat pattern, c1 at next level, right associativity) : monad_scope.

  Notation "x <- c1 ;; c2" := (@bind _ _ _ _ c1 (fun x => c2))
    (at level 100, c1 at next level, right associativity) : monad_scope.

  Notation "' pat <- c1 ;; c2" := (@bind _ _ _ _ c1 (fun x => match x with pat => c2 end))
    (at level 100, pat pattern, c1 at next level, right associativity) : monad_scope.

  Notation "e1 ;; e2" := (_ <- e1%monad ;; e2%monad)%monad
    (at level 100, right associativity) : monad_scope.
End MCMonadNotation.

Import MCMonadNotation.

Instance option_monad : Monad option :=
  {| ret A a := Some a ;
     bind A B m f :=
       match m with
       | Some a => f a
       | None => None
       end
  |}.

Open Scope monad.

Section MapOpt.
  Context {A} (f : A -> option A).

  Fixpoint mapopt (l : list A) : option (list A) :=
    match l with
    | nil => ret nil
    | x :: xs => x' <- f x ;;
                xs' <- mapopt xs ;;
                ret (x' :: xs')
    end.
End MapOpt.

Section MonadOperations.
  Context {T : Type -> Type} {M : Monad T}.
  Context {A B} (f : A -> T B).
  Fixpoint monad_map (l : list A)
    : T (list B)
    := match l with
       | nil => ret nil
       | x :: l => x' <- f x ;;
                  l' <- monad_map l ;;
                  ret (x' :: l')
       end.

  Context (g : A -> B -> T A).
  Fixpoint monad_fold_left (l : list B) (x : A) : T A
    := match l with
       | nil => ret x
       | y :: l => x' <- g x y ;;
                   monad_fold_left l x'
       end.

  Fixpoint monad_fold_right (l : list B) (x : A) : T A
       := match l with
          | nil => ret x
          | y :: l => l' <- monad_fold_right l x ;;
                      g l' y
          end.

  Context (h : nat -> A -> T B).
  Fixpoint monad_map_i_aux (n0 : nat) (l : list A) : T (list B)
    := match l with
       | nil => ret nil
       | x :: l => x' <- (h n0 x) ;;
                   l' <- (monad_map_i_aux (S n0) l) ;;
                   ret (x' :: l')
       end.

  Definition monad_map_i := @monad_map_i_aux 0.
End MonadOperations.

Definition monad_iter {T : Type -> Type} {M A} (f : A -> T unit) (l : list A) : T unit
  := @monad_fold_left T M _ _ (fun _ => f) l tt.

Fixpoint monad_All {T : Type -> Type} {M : Monad T} {A} {P} (f : forall x, T (P x)) l : T (@All A P l) := match l with
   | [] => ret All_nil
   | a :: l => X <- f a ;;
              Y <- monad_All f l ;;
              ret (All_cons X Y)
   end.

Fixpoint monad_All2 {T : Type -> Type} {E} {M : Monad T} {M' : MonadExc E T} wrong_sizes
  {A B R} (f : forall x y, T (R x y)) l1 l2 : T (@All2 A B R l1 l2) :=
  match l1, l2 with
   | [], [] => ret All2_nil
   | a :: l1, b :: l2 => X <- f a b ;;
                        Y <- monad_All2 wrong_sizes f l1 l2 ;;
                        ret (All2_cons X Y)
   | _, _ => raise wrong_sizes
   end.

Definition monad_prod {T} {M : Monad T} {A B} (x : T A) (y : T B): T (A * B)%type
  := X <- x ;; Y <- y ;; ret (X, Y).

 
Definition check_dec {T : Type -> Type} {E : Type} {M : Monad T} {M' : MonadExc E T} (e : E) {P}
  (H : {P} + {~ P}) : T P
  := match H with
  | left x => ret x
  | right _ => raise e
  end.

Definition check_eq_true {T : Type -> Type} {E : Type} {M : Monad T} {M' : MonadExc E T} (b : bool) (e : E) : T b :=
  if b return T b then ret eq_refl else raise e.

Definition check_eq_nat {T : Type -> Type} {E : Type} {M : Monad T} {M' : MonadExc E T} n m (e : E) : T (n = m) :=
  match PeanoNat.Nat.eq_dec n m with
  | left p => ret p
  | right p => raise e
  end.

Program Fixpoint monad_Alli {T : Type -> Type} {M : Monad T} {A} {P} (f : forall n x, T (∥ P n x ∥)) l n
  : T (∥ @Alli A P n l ∥)
  := match l with
      | [] => ret (sq Alli_nil)
      | a :: l => X <- f n a ;;
                  Y <- monad_Alli f l (S n) ;;
                  ret _
      end.
Admit Obligations.

Program Fixpoint monad_Alli_All {T : Type -> Type} {M : Monad T} {A} {P} {Q} (f : forall n x, ∥ Q x ∥ -> T (∥ P n x ∥)) l n :
  ∥ All Q l ∥ -> T (∥ @Alli A P n l ∥)
  := match l with
      | [] => fun _ => ret (sq Alli_nil)
      | a :: l => fun allq => X <- f n a _ ;;
                  Y <- monad_Alli_All f l (S n) _ ;;
                  ret _
      end.
Admit Obligations.
Admit Obligations.
Admit Obligations.

Section monad_Alli_nth.
  Context {T} {M : Monad T} {A} {P : nat -> A -> Type}.
  Program Fixpoint monad_Alli_nth_gen l k
    (f : forall n x, nth_error l n = Some x -> T (∥ P (k + n) x ∥)) :
    T (∥ @Alli A P k l ∥)
    := match l with
      | [] => ret (sq Alli_nil)
      | a :: l => X <- f 0 a _ ;;
                  Y <- monad_Alli_nth_gen l (S k) (fun n x hnth => px <- f (S n) x hnth;; ret _) ;;
                  ret _
      end.
Admit Obligations.
Admit Obligations.

  Definition monad_Alli_nth l (f : forall n x, nth_error l n = Some x -> T (∥ P n x ∥)) : T (∥ @Alli A P 0 l ∥) :=
    monad_Alli_nth_gen l 0 f.

End monad_Alli_nth.

Section MonadAllAll.
  Context {T : Type -> Type} {M : Monad T} {A} {P : A -> Type} {Q} (f : forall x, ∥ Q x ∥ -> T (∥ P x ∥)).
  Program Fixpoint monad_All_All l : ∥ All Q l ∥ -> T (∥ All P l ∥) :=
    match l return ∥ All Q l ∥ -> T (∥ All P l ∥) with
      | [] => fun _ => ret (sq All_nil)
      | a :: l => fun allq =>
      X <- f a _ ;;
      Y <- monad_All_All l _ ;;
      ret _
      end.
Admit Obligations.
Admit Obligations.
Admit Obligations.
End MonadAllAll.
End monad_utils.

End MetaCoq_DOT_Template_DOT_monad_utils_WRAPPED.
Module Export MetaCoq_DOT_Template_DOT_monad_utils.
Module Export MetaCoq.
Module Export Template.
Module Export monad_utils.
Include MetaCoq_DOT_Template_DOT_monad_utils_WRAPPED.monad_utils.
End monad_utils.

End Template.

End MetaCoq.

End MetaCoq_DOT_Template_DOT_monad_utils.
Require Coq.Floats.SpecFloat.
Require Equations.Type.FunctionalExtensionality.
Require Equations.Type.WellFounded.

Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.
Export Coq.Bool.Bool.
Export Coq.ZArith.ZArith.
Export Coq.Strings.String.
Export MetaCoq.Template.utils.MCUtils.
Export MetaCoq.Template.monad_utils.

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
