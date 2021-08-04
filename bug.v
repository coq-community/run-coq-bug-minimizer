(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "+implicit-core-hint-db,+implicits-in-term,+non-reversible-notation,+deprecated-intros-until-0,+deprecated-focus,+unused-intro-pattern,+deprecated-hint-constr,+fragile-hint-constr,+variable-collision,+unexpected-implicit-declaration,+omega-is-deprecated,+non-recursive" "-w" "-notation-overridden,-undeclared-scope,-deprecated-hint-rewrite-without-locality" "-w" "-notation-overridden,-undeclared-scope" "-w" "-deprecated-native-compiler-option" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/rewriter/src/Rewriter" "Rewriter" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-I" "/github/workspace/builds/coq/coq-failing/_build_ci/rewriter/src/Rewriter/Util/plugins" "-top" "Reify" "-native-compiler" "no") -*- *)
(* File reduced by coq-bug-finder from original input, then from 1339 lines to 138 lines, then from 226 lines to 1841 lines, then from 1844 lines to 333 lines, then from 419 lines to 1383 lines, then from 1386 lines to 678 lines, then from 754 lines to 990 lines, then from 994 lines to 679 lines, then from 755 lines to 1033 lines, then from 1037 lines to 692 lines, then from 766 lines to 2817 lines, then from 2820 lines to 874 lines, then from 937 lines to 1437 lines, then from 1440 lines to 876 lines, then from 897 lines to 1338 lines, then from 1341 lines to 1263 lines *)
(* coqc version 8.15+alpha compiled with OCaml 4.12.0
   coqtop version 8.15+alpha *)
Declare ML Module "ltac_plugin".
Module Export AdmitTactic.
Module Import LocalFalse.
Inductive False := .
End LocalFalse.
Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.
End AdmitTactic.
Require Coq.FSets.FMapPositive.
Require Coq.Classes.Morphisms.
Require Rewriter.Util.GlobalSettings.
Require Rewriter.Util.FixCoqMistakes.
Require Rewriter.Util.Notations.
Require Rewriter.Util.CPSNotations.
Require Coq.Relations.Relation_Definitions.
Require Rewriter.Util.Tactics.Head.
Require Rewriter.Util.Tactics.BreakMatch.
Require Rewriter.Util.Tactics.DestructHyps.
Require Rewriter.Util.Tactics.DestructHead.
Module Export Rewriter_DOT_Util_DOT_Option_WRAPPED.
Module Export Option.
Import Coq.Classes.Morphisms.
Import Coq.Relations.Relation_Definitions.
Import Rewriter.Util.Tactics.BreakMatch.
Import Rewriter.Util.Tactics.DestructHead.
Import Rewriter.Util.Notations.

Scheme Equality for option.
Arguments option_beq {_} _ _ _.

 
Definition option_rect_nodep {A P} : (A -> P) -> P -> option A -> P
  := @option_rect A (fun _ => P).
Global Instance option_rect_nodep_Proper {A P}
  : Proper ((eq ==> eq) ==> eq ==> eq ==> eq) (@option_rect_nodep A P) | 10.
admit.
Defined.

Module Thunked.
  Definition option_rect {A} P (S_case : A -> P) (N_case : unit -> P) (o : option A) : P
    := Datatypes.option_rect (fun _ => P) S_case (N_case tt) o.
  Global Instance option_rect_Proper {A P}
    : Proper ((eq ==> eq) ==> (eq ==> eq) ==> eq ==> eq) (@option_rect A P) | 10.
admit.
Defined.
End Thunked.
 
Global Strategy expand [option_rect_nodep Thunked.option_rect].

Definition option_beq_hetero {A B} (AB_beq : A -> B -> bool) (x : option A) (y : option B) : bool
  := match x, y with
     | Some x, Some y => AB_beq x y
     | None, None => true
     | Some _, _
     | None, _
       => false
     end.

 
Definition lift {A} (x : option (option A)) : option (option A)
  := match x with
     | Some None => None  
     | Some (Some x) => Some (Some x)
     | None => Some None
     end.

Notation map := option_map (only parsing).
 

Definition bind {A B} (v : option A) (f : A -> option B) : option B
  := match v with
     | Some v => f v
     | None => None
     end.

Definition sequence {A} (v1 v2 : option A) : option A
  := match v1 with
     | Some v => Some v
     | None => v2
     end.
Definition sequence_return {A} (v1 : option A) (v2 : A) : A
  := match v1 with
     | Some v => v
     | None => v2
     end.
Global Arguments sequence {A} !v1 v2.
Global Arguments sequence_return {A} !v1 v2.
Notation or_else := sequence (only parsing).
 
Notation value := sequence_return (only parsing).
Notation get_default := sequence_return (only parsing).

Module Export Notations.
  Delimit Scope option_scope with option.
  Bind Scope option_scope with option.

  Notation "'olet' x .. y <- X ; B" := (bind X (fun x => .. (fun y => B%option) .. )) : option_scope.
  Notation "A <- X ; B" := (bind X (fun A => B%option)) : option_scope.
  Infix ";;" := sequence : option_scope.
  Infix ";;;" := sequence_return : option_scope.
End Notations.
Local Open Scope option_scope.

Definition combine {A B} (x : option A) (y : option B) : option (A * B)
  := match x, y with
     | Some x, Some y => Some (x, y)
     | _, _ => None
     end.

Section Relations.
  Definition option_eq {A B} eq (x : option A) (y : option B) :=
    match x with
    | None    => y = None
    | Some ax => match y with
                 | None => False
                 | Some ay => eq ax ay
                 end
    end.

  Local Ltac t :=
    cbv; repeat (break_match || intro || intuition congruence ||
                 solve [ apply reflexivity
                       | apply symmetry; eassumption
                       | eapply transitivity; eassumption
                       | eauto ] ).

  Global Instance Reflexive_option_eq {T} {R} {Reflexive_R:@Reflexive T R}
    : Reflexive (option_eq R) | 1.
admit.
Defined.

  Lemma option_eq_sym {A B} {R1 R2 : _ -> _ -> Prop} (HR : forall v1 v2, R1 v1 v2 -> R2 v2 v1)
    : forall v1 v2, @option_eq A B R1 v1 v2 -> option_eq R2 v2 v1.
admit.
Defined.

  Lemma option_eq_trans {A B C} {R1 R2 R3 : _ -> _ -> Prop}
        (HR : forall v1 v2 v3, R1 v1 v2 -> R2 v2 v3 -> R3 v1 v3)
    : forall v1 v2 v3, @option_eq A B R1 v1 v2 -> @option_eq B C R2 v2 v3 -> @option_eq A C R3 v1 v3.
admit.
Defined.

  Global Instance Transitive_option_eq {T} {R} {Transitive_R:@Transitive T R}
    : Transitive (option_eq R) | 1 := option_eq_trans Transitive_R.

  Global Instance Symmetric_option_eq {T} {R} {Symmetric_R:@Symmetric T R}
    : Symmetric (option_eq R) | 1 := option_eq_sym Symmetric_R.

  Global Instance Equivalence_option_eq {T} {R} {Equivalence_R:@Equivalence T R}
    : Equivalence (option_eq R).
admit.
Defined.
End Relations.

Lemma option_bl_hetero {A B} {AB_beq : A -> B -> bool} {AB_R : A -> B -> Prop}
      (AB_bl : forall x y, AB_beq x y = true -> AB_R x y)
      {x y}
  : option_beq_hetero AB_beq x y = true -> option_eq AB_R x y.
admit.
Defined.

Lemma option_lb_hetero {A B} {AB_beq : A -> B -> bool} {AB_R : A -> B -> Prop}
      (AB_lb : forall x y, AB_R x y -> AB_beq x y = true)
      {x y}
  : option_eq AB_R x y -> option_beq_hetero AB_beq x y = true.
admit.
Defined.

Lemma option_beq_hetero_uniform {A : Type} A_beq {x y}
  : option_beq_hetero A_beq x y = @option_beq A A_beq x y.
admit.
Defined.

Lemma option_bl_hetero_eq {A}
      {A_beq : A -> A -> bool}
      (A_bl : forall x y, A_beq x y = true -> x = y)
      {x y}
  : option_beq_hetero A_beq x y = true -> x = y.
admit.
Defined.

Lemma option_lb_hetero_eq {A}
      {A_beq : A -> A -> bool}
      (A_lb : forall x y, x = y -> A_beq x y = true)
      {x y}
  : x = y -> option_beq_hetero A_beq x y = true.
admit.
Defined.

Global Instance bind_Proper {A B}
  : Proper (eq ==> (pointwise_relation _ eq) ==> eq) (@bind A B).
admit.
Defined.

Global Instance bind_Proper_pointwise_option_eq {A B RB}
  : Proper (eq ==> (pointwise_relation _ (option_eq RB)) ==> option_eq RB) (@bind A B) | 90.
admit.
Defined.

Lemma bind_Proper_option_eq_hetero {A A' B B'} {RA RB : _ -> _ -> Prop}
      a a' (HA : option_eq RA a a') b b' (HB : forall a a', RA a a' -> option_eq RB (b a) (b' a'))
  : option_eq RB (@bind A B a b) (@bind A' B' a' b').
admit.
Defined.

Global Instance bind_Proper_option_eq {A B RA RB}
  : Proper (option_eq RA ==> (RA ==> option_eq RB) ==> option_eq RB) (@bind A B) | 100.
admit.
Defined.

Global Instance Proper_option_rect_nd_changebody
      {A B:Type} {RB:relation B} {a:option A}
  : Proper (pointwise_relation _ RB ==> RB ==> RB) (fun S N => option_rect (fun _ => B) S N a).
admit.
Defined.

 

Global Instance Proper_option_rect_nd_changevalue
      {A B RA RB} some {Proper_some: Proper (RA==>RB) some}
  : Proper (RB ==> option_eq RA ==> RB) (@option_rect A (fun _ => B) some).
admit.
Defined.

Lemma bind_zero_l {A B} f : @bind A B None f = None.
admit.
Defined.
Lemma bind_zero_r {A B} v : @bind A B v (fun _ => None) = None.
admit.
Defined.
Lemma bind_zero_r_ext {A B} v f : (forall v, f v = None) -> @bind A B v f = None.
admit.
Defined.

Lemma option_rect_false_returns_true_iff
      {T} {R} {reflexiveR:Reflexive R}
      (f:T->bool) {Proper_f:Proper(R==>eq)f} (o:option T) :
  option_rect (fun _ => bool) f false o = true <-> exists s:T, option_eq R o (Some s) /\ f s = true.
admit.
Defined.

Lemma option_rect_false_returns_true_iff_eq
      {T} (f:T->bool) (o:option T) :
  option_rect (fun _ => bool) f false o = true <-> exists s:T, Logic.eq o (Some s) /\ f s = true.
admit.
Defined.

Lemma option_rect_option_map : forall {A B C} (f:A->B) some none v,
    option_rect (fun _ => C) (fun x => some (f x)) none v = option_rect (fun _ => C) some none (option_map f v).
admit.
Defined.

Lemma option_map_map : forall {A B C} (f:A->B) (g:B->C) v,
    option_map g (option_map f v) = option_map (fun v => g (f v)) v.
admit.
Defined.

Lemma option_rect_function {A B C S' N' v} f
  : f (option_rect (fun _ : option A => option B) S' N' v)
    = option_rect (fun _ : option A => C) (fun x => f (S' x)) (f N') v.
admit.
Defined.

Definition option_leq_to_eq {A} (x y : option A) : x = y -> option_eq eq x y.
admit.
Defined.

Definition option_eq_to_leq {A} (x y : option A) : option_eq eq x y -> x = y.
admit.
Defined.

Lemma option_leq_to_eq_to_leq {A x y} v : @option_eq_to_leq A x y (@option_leq_to_eq A x y v) = v.
admit.
Defined.

Lemma option_eq_to_leq_to_eq {A x y} v : @option_leq_to_eq A x y (@option_eq_to_leq A x y v) = v.
admit.
Defined.

Lemma UIP_None {A} (p q : @None A = @None A) : p = q.
admit.
Defined.

Definition is_None {A} (x : option A) : bool
  := match x with
     | Some _ => false
     | None => true
     end.

Definition is_Some {A} (x : option A) : bool
  := match x with
     | Some _ => true
     | None => false
     end.

Lemma is_None_eq_None_iff {A x} : @is_None A x = true <-> x = None.
admit.
Defined.

Definition invert_Some {A} (x : option A) : match x with
                                            | Some _ => A
                                            | None => unit
                                            end
  := match x with
     | Some x' => x'
     | None => tt
     end.

Lemma invert_eq_Some {A x y} (p : Some x = Some y) : { pf : x = y | @option_eq_to_leq A (Some x) (Some y) pf = p }.
admit.
Defined.

Definition always_invert_Some {A} (x : option A) {pf : x <> None} : A
  := match x return x <> None -> A with
     | Some v => fun _ => v
     | None => fun pf => False_rect _ (pf eq_refl)
     end pf.

Lemma push_always_invert_Some' {A B} (f : A -> B) (x : option A)
      (pf : x <> None)
      (pf' : option_map f x <> None)
  : f (@always_invert_Some _ x pf) = @always_invert_Some _ (option_map f x) pf'.
admit.
Defined.

Definition pull_always_invert_Some {A B} (f : A -> B) (x : option A)
      (pf : option_map f x <> None)
  : f (@always_invert_Some _ x (fun H => pf (f_equal (option_map f) H)))
    = @always_invert_Some _ (option_map f x) pf
  := push_always_invert_Some' f x _ pf.

Lemma option_map_neq_None_iff {A B} (f : A -> B) x
  : x <> None <-> option_map f x <> None.
admit.
Defined.

Definition push_always_invert_Some {A B} (f : A -> B) (x : option A)
      (pf : x <> None)
  : f (@always_invert_Some _ x pf)
    = @always_invert_Some _ (option_map f x)
                         (proj1 (option_map_neq_None_iff f x) pf)
  := push_always_invert_Some' f x pf _.

Definition always_invert_Some_bind' {A B} (x : option A) (f : A -> option B)
           pf pf' pf''
  : @always_invert_Some _ (bind x f) pf
    = @always_invert_Some _ (f (@always_invert_Some _ x pf')) pf''.
admit.
Defined.

Lemma bind_neq_None_iff {A B} (x : option A) (f : A -> option B)
  : (bind x f <> None) <-> (x <> None /\ forall pf, f (@always_invert_Some _ x pf) <> None).
admit.
Defined.

Lemma bind_neq_None_iff' {A B} (x : option A) (f : A -> option B)
  : (bind x f <> None) <-> (exists pf : x <> None, f (@always_invert_Some _ x pf) <> None).
admit.
Defined.

Definition push_always_invert_Some_bind {A B} (x : option A) (f : A -> option B)
           pf
           (pf' := proj1 (proj1 (bind_neq_None_iff x f) pf))
           (pf'' := proj2 (proj1 (bind_neq_None_iff x f) pf) pf')
  : @always_invert_Some _ (bind x f) pf
    = @always_invert_Some _ (f (@always_invert_Some _ x pf')) pf''
  := always_invert_Some_bind' x f _ _ _.

Definition pull_always_invert_Some_bind {A B} (x : option A) (f : A -> option B)
           pf pf'
           (pf'' := proj2 (bind_neq_None_iff' x f) (ex_intro _ pf pf'))
  : @always_invert_Some _ (f (@always_invert_Some _ x pf)) pf'
    = @always_invert_Some _ (bind x f) pf''
  := eq_sym (always_invert_Some_bind' x f _ _ _).

End Option.

End Rewriter_DOT_Util_DOT_Option_WRAPPED.
Module Export Rewriter_DOT_Util_DOT_Option.
Module Export Rewriter.
Module Export Util.
Module Export Option.
Include Rewriter_DOT_Util_DOT_Option_WRAPPED.Option.
End Option.

End Util.

End Rewriter.

End Rewriter_DOT_Util_DOT_Option.
Require Coq.MSets.MSetPositive.

Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.
Import Coq.Bool.Bool.

Notation reflect_rel P b := (forall x y, reflect (P x y) (b x y)).
Module Export Language.
Import Coq.ZArith.ZArith.
Import Rewriter.Util.CPSNotations.
Import Rewriter.Util.Notations.
Module Export Compilers.
  Module type.
    Inductive type {base_type : Type} := base (t : base_type) | arrow (s d : type).
    Global Arguments type : clear implicits.

    Fixpoint final_codomain {base_type} (t : type base_type) : base_type
      := match t with
         | base t
           => t
         | arrow s d => @final_codomain base_type d
         end.

    Fixpoint interp {base_type} (base_interp : base_type -> Type) (t : type base_type) : Type
      := match t with
         | base t => base_interp t
         | arrow s d => @interp _ base_interp s -> @interp _ base_interp d
         end.

    Class try_make_transport_cpsT {base : Type}
      := try_make_transport_cpsv : forall (P : base -> Type) t1 t2, ~> option (P t1 -> P t2).
    Global Arguments try_make_transport_cpsT : clear implicits.

    End type.
  Notation type := type.type.
  Delimit Scope etype_scope with etype.
  Bind Scope etype_scope with type.type.
  Global Arguments type.base {_} _%etype.
  Infix "->" := type.arrow : etype_scope.
  Module base.
    Module Export type.
      Inductive type {base_type : Type} := type_base (t : base_type) | prod (A B : type) | list (A : type) | option (A : type) | unit.
      Global Arguments type : clear implicits.
    End type.
    Notation type := type.type.

    Fixpoint interp {base} (base_interp : base -> Type) (ty : type base)
      := match ty with
         | type.type_base t => base_interp t
         | type.unit => Datatypes.unit
         | type.prod A B => interp base_interp A * interp base_interp B
         | type.list A => Datatypes.list (interp base_interp A)
         | type.option A => Datatypes.option (interp base_interp A)
         end%type.

  End base.
  Infix "*" := base.type.prod : etype_scope.
  Notation "()" := base.type.unit : etype_scope.

  Module pattern.
    Module base.
      Module Export type.
        Inductive type {base_type : Type} := var (p : positive) | type_base (t : base_type) | prod (A B : type) | list (A : type) | option (A : type) | unit.
        Global Arguments type : clear implicits.
      End type.
      Notation type := type.type.

      Module Export Notations.
        Delimit Scope ptype_scope with ptype.
        Delimit Scope pbtype_scope with pbtype.
        Notation "A * B" := (type.prod A%ptype B%ptype) : ptype_scope.
        Notation "A * B" := (type.prod A%pbtype B%pbtype) : pbtype_scope.
        Notation "A -> B" := (@type.arrow (base.type _) A%ptype B%ptype) : ptype_scope.
      End Notations.
    End base.
    Notation type base := (type.type (base.type base)).
  End pattern.
  Export pattern.base.Notations.

  Module Export expr.
    Section with_var.
      Context {base_type : Type}.
      Local Notation type := (type base_type).
      Context {ident : type -> Type}
              {var : type -> Type}.

      Inductive expr : type -> Type :=
      | Ident {t} (idc : ident t) : expr t
      | Var {t} (v : var t) : expr t
      | Abs {s d} (f : var s -> expr d) : expr (s -> d)
      | App {s d} (f : expr (s -> d)) (x : expr s) : expr d
      | LetIn {A B} (x : expr A) (f : var A -> expr B) : expr B
      .
    End with_var.

    Module Export Notations.
      Delimit Scope expr_scope with expr.
      Infix "@" := App : expr_scope.
    End Notations.
  End expr.

  Module Export ident.
    Section generic.
      Context {base : Type}
              {base_interp : base -> Type}.
      Local Notation base_type := (@base.type base).
      Local Notation type := (@type.type base_type).
      Local Notation base_type_interp := (@base.interp base base_interp).
      Context {ident var : type -> Type}.
      Class BuildIdentT :=
        {
          ident_Literal : forall {t}, base_interp t -> ident (type.base (base.type.type_base t));
          ident_nil : forall {t}, ident (type.base (base.type.list t));
          ident_cons : forall {t}, ident (type.base t -> type.base (base.type.list t) -> type.base (base.type.list t));
          ident_Some : forall {t}, ident (type.base t -> type.base (base.type.option t));
          ident_None : forall {t}, ident (type.base (base.type.option t));
          ident_pair : forall {A B}, ident (type.base A -> type.base B -> type.base (A * B));
          ident_tt : ident (type.base base.type.unit)
        }.
      Context {buildIdent : BuildIdentT}.

      Local Notation expr := (@expr.expr base_type ident var).

      Definition reify_list {t} (ls : list (expr (type.base t))) : expr (type.base (base.type.list t))
        := Datatypes.list_rect
             (fun _ => _)
             (expr.Ident ident_nil)
             (fun x _ xs => expr.Ident ident_cons @ x @ xs)%expr
             ls.

      Definition reify_option {t} (v : option (expr (type.base t))) : expr (type.base (base.type.option t))
        := Datatypes.option_rect
             (fun _ => _)
             (fun x => expr.Ident ident_Some @ x)%expr
             (expr.Ident ident_None)
             v.

      Fixpoint smart_Literal {t:base_type} : base_type_interp t -> expr (type.base t)
        := match t with
           | base.type.type_base t => fun v => expr.Ident (ident_Literal v)
           | base.type.prod A B
             => fun '((a, b) : base_type_interp A * base_type_interp B)
                => expr.Ident ident_pair @ (@smart_Literal A a) @ (@smart_Literal B b)
           | base.type.list A
             => fun v : list (base_type_interp A)
                => reify_list (List.map (@smart_Literal A) v)
           | base.type.option A
             => fun v : option (base_type_interp A)
                => reify_option (option_map (@smart_Literal A) v)
           | base.type.unit => fun _ => expr.Ident ident_tt
           end%expr.

      End generic.
    Global Arguments BuildIdentT {base base_interp} ident, {base} base_interp ident.

    End ident.

  Module Import invert_expr.
    End invert_expr.

  Module DefaultValue.

    Module Export type.
      Module Export base.
        Class DefaultT {base : Type} {base_interp : base -> Type}
          := defaultv : forall {t}, base_interp t.

        Section with_base.
          Context {base : Type}
                  {base_interp : base -> Type}.
          Local Notation base_type_interp := (@base.interp base base_interp).
          Context {baseDefault : @DefaultT base base_interp}.

          Fixpoint default {t : base.type base} : base_type_interp t
            := match t with
               | base.type.type_base t => defaultv (t:=t)
               | base.type.unit => tt
               | base.type.list _ => nil
               | base.type.prod A B
                 => (@default A, @default B)
               | base.type.option A => None
               end.
        End with_base.

      End base.

      End type.

    End DefaultValue.

  End Compilers.
    Module Export UnderLets.
    Section with_var.
      Context {base_type : Type}.
      Local Notation type := (type base_type).
      Context {ident : type -> Type}
              {var : type -> Type}.
      Local Notation expr := (@expr base_type ident var).

      Inductive UnderLets {T : Type} :=
      | Base (v : T)
      | UnderLet {A} (x : expr A) (f : var A -> UnderLets).
    End with_var.
      Global Arguments UnderLets : clear implicits.

Local Set Primitive Projections.

Module Export IdentifiersLibrary.
Import Coq.FSets.FMapPositive.
Import Coq.MSets.MSetPositive.
Import Coq.Lists.List.

Import EqNotations.
Module Export Compilers.

  Local Notation type_of_list := (fold_right (fun A B => prod A B) unit).

  Fixpoint lift_type_of_list_map {A} {ls : list A} {P1 P2 : A -> Type} (F : forall a, P1 a -> P2 a) {struct ls}
    : type_of_list (List.map P1 ls) -> type_of_list (List.map P2 ls)
    := match ls return type_of_list (List.map P1 ls) -> type_of_list (List.map P2 ls) with
       | nil => fun x => x
       | T :: Ts
         => fun v_vs
            => (F T (fst v_vs),
                @lift_type_of_list_map A Ts P1 P2 F (snd v_vs))
       end.

  Module pattern.
    Notation EvarMap_at base := (PositiveMap.t (Compilers.base.type base)).
    Notation EvarMap := (EvarMap_at _).
    Export Language.Compilers.pattern.
    Module base.
      Export Language.Compilers.pattern.base.

      Section with_base.
        Context {base : Type}.

        Local Notation type := (type base).

        Fixpoint relax (t : Compilers.base.type base) : type
          := match t with
             | Compilers.base.type.type_base t => type.type_base t
             | Compilers.base.type.prod A B => type.prod (relax A) (relax B)
             | Compilers.base.type.list A => type.list (relax A)
             | Compilers.base.type.option A => type.option (relax A)
             | Compilers.base.type.unit => type.unit
             end.

        Definition lookup_default (p : positive) (evar_map : EvarMap) : Compilers.base.type base
          := match PositiveMap.find p evar_map with
             | Datatypes.Some t => t
             | Datatypes.None => Compilers.base.type.unit
             end.

        Fixpoint subst_default (ptype : type) (evar_map : EvarMap) : Compilers.base.type base
          := match ptype with
             | type.var p => lookup_default p evar_map
             | type.type_base t => Compilers.base.type.type_base t
             | type.prod A B
               => Compilers.base.type.prod (subst_default A evar_map) (subst_default B evar_map)
             | type.list A => Compilers.base.type.list (subst_default A evar_map)
             | type.option A => Compilers.base.type.option (subst_default A evar_map)
             | type.unit => Compilers.base.type.unit
             end.

        Fixpoint collect_vars (t : type) : PositiveSet.t
          := match t with
             | type.var p => PositiveSet.add p PositiveSet.empty
             | type.unit
             | type.type_base _
               => PositiveSet.empty
             | type.prod A B => PositiveSet.union (collect_vars A) (collect_vars B)
             | type.list A => collect_vars A
             | type.option A => collect_vars A
             end.
      End with_base.
    End base.

    Module Export type.
      Section with_base.
        Context {base : Type}.

        Local Notation type := (type base).

        Fixpoint relax (t : type.type (Compilers.base.type base)) : type
          := match t with
             | type.base t => type.base (base.relax t)
             | type.arrow s d => type.arrow (relax s) (relax d)
             end.

        Fixpoint subst_default (ptype : type) (evar_map : EvarMap) : type.type (Compilers.base.type base)
          := match ptype with
             | type.base t => type.base (base.subst_default t evar_map)
             | type.arrow A B => type.arrow (subst_default A evar_map) (subst_default B evar_map)
             end.

        Fixpoint collect_vars (t : type) : PositiveSet.t
          := match t with
             | type.base t => base.collect_vars t
             | type.arrow s d => PositiveSet.union (collect_vars s) (collect_vars d)
             end.
      End with_base.
    End type.

    Module Export Raw.
      Module Export ident.
        Inductive kind_of_type := GallinaType (_ : Type) | BaseBaseType | BaseType.
        Definition Type_of_kind_of_type (base : Type) (T : kind_of_type)
          := match T with
             | GallinaType T => T
             | BaseBaseType => base
             | BaseType => Compilers.base.type.type base
             end.

        Notation type_of_list_of_kind base ls
          := (type_of_list (List.map (@Type_of_kind_of_type base) ls)).

        Section with_base.
          Context {base : Type}.
          Local Notation ctype := (type.type (Compilers.base.type base)).
          Context {cident : ctype -> Type}.
          Local Notation type_of_list_of_kind ls := (type_of_list_of_kind base ls).

          Record preident_infos :=
            {
              dep_types : list Type;
              indep_types : list kind_of_type;
              indep_args : type_of_list dep_types -> list Type;
              to_type : forall d : type_of_list dep_types, type_of_list_of_kind indep_types -> Compilers.type (Compilers.base.type base);
              to_ident : forall (d : type_of_list dep_types) (i : type_of_list_of_kind indep_types), type_of_list (indep_args d) -> cident (to_type d i)
            }.

          Record ident_infos :=
            {
              preinfos :> preident_infos;
              dep_types_dec_transparent : forall x y : type_of_list (dep_types preinfos), {x = y} + {x <> y};
              indep_args_beq : _;
              indep_args_reflect
              : forall x, reflect_rel (@eq (type_of_list (indep_args preinfos x))) (indep_args_beq x);
              indep_types_beq : _;
              indep_types_reflect
              : reflect_rel (@eq (type_of_list_of_kind (indep_types preinfos))) indep_types_beq;
            }.

          Definition ident_args (pi : preident_infos)
            := { t : type_of_list (dep_types pi) & type_of_list_of_kind (indep_types pi) * type_of_list (indep_args pi t) }%type.

          Definition assemble_ident {pi} (args : ident_args pi)
            := to_ident pi (projT1 args) (Datatypes.fst (projT2 args)) (Datatypes.snd (projT2 args)).

          Section __.
            Context (ident : Set)
                    (all_idents : list ident)
                    (ident_index : ident -> nat)
                    (ident_index_idempotent : forall idc, List.nth_error all_idents (ident_index idc) = Some idc)
                    (eta_ident_cps_gen
                     : forall (T : ident -> Type)
                              (f : forall idc, T idc),
                        { f' : forall idc, T idc | forall idc, f' idc = f idc }).

            Context (ident_infos_of : ident -> ident_infos)
                    (split_ident_gen
                     : forall {t} (idc : cident t),
                        { ridc : ident & { args : ident_args (ident_infos_of ridc)
                                         | { pf : _ = _
                                           | idc = rew [cident] pf in assemble_ident args } } }).

            Definition prefull_types : ident -> Type
              := fun idc => ident_args (ident_infos_of idc).
            Definition full_types : ident -> Type
              := proj1_sig (@eta_ident_cps_gen _ prefull_types).
          End __.
        End with_base.
      End ident.
    End Raw.

    Module Export ident.
      Definition Type_of_kind_of_type (base : Type) (T : Raw.ident.kind_of_type)
        := match T with
           | Raw.ident.GallinaType T => T
           | Raw.ident.BaseBaseType => base
           | Raw.ident.BaseType => pattern.base.type.type base
           end.

      Notation full_type_of_list_of_kind base ls
        := (type_of_list (List.map (Raw.ident.Type_of_kind_of_type base) ls)).

      Notation type_of_list_of_kind base ls
        := (type_of_list (List.map (Type_of_kind_of_type base) ls)).

      Section with_base.
        Context {base : Type}.
        Local Notation ctype := (type.type (Compilers.base.type base)).
        Local Notation type := (type base).
        Context {cident : ctype -> Type}.

        Local Notation Type_of_kind_of_type := (Type_of_kind_of_type base).
        Local Notation full_type_of_list_of_kind ls := (full_type_of_list_of_kind base ls).
        Local Notation type_of_list_of_kind ls := (type_of_list_of_kind base ls).

        Definition relax_kind_of_type {T} : Raw.ident.Type_of_kind_of_type base T -> Type_of_kind_of_type T
          := match T with
             | Raw.ident.GallinaType _
             | Raw.ident.BaseBaseType
               => fun x => x
             | Raw.ident.BaseType => pattern.base.relax
             end.
        Definition subst_default_kind_of_type (evm : EvarMap) {T} : Type_of_kind_of_type T -> Raw.ident.Type_of_kind_of_type base T
          := match T with
             | Raw.ident.GallinaType _
             | Raw.ident.BaseBaseType
               => fun x => x
             | Raw.ident.BaseType => fun t => pattern.base.subst_default t evm
             end.

        Section __.
          Context (raw_ident : Set)
                  (all_raw_idents : list raw_ident)
                  (raw_ident_index : raw_ident -> nat)
                  (raw_ident_index_idempotent : forall idc, List.nth_error all_raw_idents (raw_ident_index idc) = Some idc)
                  (eta_raw_ident_cps_gen
                   : forall (T : raw_ident -> Type)
                            (f : forall idc, T idc),
                      { f' : forall idc, T idc | forall idc, f' idc = f idc }).
          Context (raw_ident_infos_of : raw_ident -> Raw.ident.ident_infos)
                  (split_raw_ident_gen
                   : forall t (idc : cident t),
                      { ridc : raw_ident
                               & { args : Raw.ident.ident_args (preinfos (raw_ident_infos_of ridc))
                                 | { pf : _ = _
                                   | idc = rew [cident] pf in Raw.ident.assemble_ident args } } }).
          Context (ident : type -> Type)
                  (all_idents : list { T : Type & T })
                  (eta_ident_cps_gen
                   : forall (T : forall t, ident t -> Type)
                            (f : forall t idc, T t idc),
                      { f' : forall t idc, T t idc | forall t idc, f' t idc = f t idc })
                  (eta_ident_cps_gen_expand_literal
                   : forall (T : forall t, ident t -> Type)
                            (f : forall t idc, T t idc),
                      { f' : forall t idc, T t idc | forall t idc, f' t idc = f t idc }).

          Context (split_types
                   : forall t (idc : ident t), { ridc : raw_ident & type_of_list (dep_types (preinfos (raw_ident_infos_of ridc))) * type_of_list_of_kind (indep_types (preinfos (raw_ident_infos_of ridc))) }%type)
                  (add_types_from_raw_sig
                   : forall (ridc : raw_ident)
                            (dt : type_of_list (dep_types (preinfos (raw_ident_infos_of ridc))))
                            (idt : type_of_list_of_kind (indep_types (preinfos (raw_ident_infos_of ridc)))),
                      { t : _ & { idc : ident t | @split_types _ idc = existT _ ridc (dt, idt) } }).

          Definition split_types_subst_default : forall {t} (idc : ident t) (evm : EvarMap), { ridc : raw_ident & type_of_list (dep_types (preinfos (raw_ident_infos_of ridc))) * full_type_of_list_of_kind (indep_types (preinfos (raw_ident_infos_of ridc))) }%type
            := fun {t} idc evm
               => let res := @split_types t idc in
                  existT _ (projT1 res) (Datatypes.fst (projT2 res),
                                         lift_type_of_list_map (@subst_default_kind_of_type evm) (Datatypes.snd (projT2 res))).

          Definition prearg_types : forall {t} (idc : ident t), list Type
            := (fun {t} idc
                => let st := @split_types t idc in
                   let pi := preinfos (raw_ident_infos_of (projT1 st)) in
                   indep_args pi (Datatypes.fst (projT2 st))).
          Definition arg_types : forall {t} (idc : ident t), list Type
            := proj1_sig (@eta_ident_cps_gen _ (@prearg_types)).
        End __.
      End with_base.

      Module Export GoalType.

        Class package {base : Type} {ident : type.type (Compilers.base.type base) -> Type} :=
          {
            all_base : list base;
            all_idents : list { T : Type & T };
            ident_index : forall t, ident t -> nat;
            eta_ident_cps_gen
            : forall {T : forall t, ident t -> Type}
                     (f : forall t idc, T t idc),
                { f' : forall t idc, T t idc | forall t idc, f' t idc = f t idc };
            eta_ident_cps_gen_expand_literal
            : forall {T : forall t, ident t -> Type}
                     (f : forall t idc, T t idc),
                { f' : forall t idc, T t idc | forall t idc, f' t idc = f t idc };
            eta_ident_cps
            : forall (T : _ -> Type) t (idc : ident t)
                     (f : forall t', ident t' -> T t'),
                T t;
            simple_idents : list { t : _ & ident t };

            raw_ident : Set;
            all_raw_idents : list raw_ident;
            raw_ident_index : raw_ident -> nat;
            raw_ident_index_idempotent : forall idc, List.nth_error all_raw_idents (raw_ident_index idc) = Some idc;
            eta_raw_ident_cps_gen
            : forall {T : raw_ident -> Type}
                     (f : forall idc, T idc),
                { f' : forall idc, T idc | forall idc, f' idc = f idc };
            raw_ident_infos_of : raw_ident -> Raw.ident.ident_infos;
            split_raw_ident_gen
            : forall {t} (idc : ident t),
                { ridc : raw_ident
                         & { args : Raw.ident.ident_args (preinfos (raw_ident_infos_of ridc))
                           | { pf : _ = _
                             | idc = rew [ident] pf in Raw.ident.assemble_ident args } } };
            invert_bind_args : forall {t} (idc : ident t) (pidc : raw_ident), Datatypes.option (@Raw.ident.full_types base ident raw_ident (@eta_raw_ident_cps_gen) raw_ident_infos_of pidc);
            invert_bind_args_unknown : forall {t} (idc : ident t) (pidc : raw_ident), Datatypes.option (@Raw.ident.full_types base ident raw_ident (@eta_raw_ident_cps_gen) raw_ident_infos_of pidc);

            pattern_ident : type base -> Type;
            all_pattern_idents : list { T : Type & T };
            eta_pattern_ident_cps_gen
            : forall (T : forall t, pattern_ident t -> Type)
                     (f : forall t idc, T t idc),
                { f' : forall t idc, T t idc | forall t idc, f' t idc = f t idc };
            eta_pattern_ident_cps_gen_expand_literal
            : forall (T : forall t, pattern_ident t -> Type)
                     (f : forall t idc, T t idc),
                { f' : forall t idc, T t idc | forall t idc, f' t idc = f t idc };

            split_types
            : forall t (idc : pattern_ident t), { ridc : raw_ident & type_of_list (dep_types (preinfos (raw_ident_infos_of ridc))) * ident.type_of_list_of_kind base (indep_types (preinfos (raw_ident_infos_of ridc))) }%type;
            add_types_from_raw_sig
            : forall (ridc : raw_ident)
                     (dt : type_of_list (dep_types (preinfos (raw_ident_infos_of ridc))))
                     (idt : ident.type_of_list_of_kind base (indep_types (preinfos (raw_ident_infos_of ridc)))),
                { t : _ & { idc : pattern_ident t | @split_types _ idc = existT _ ridc (dt, idt) } };
            to_type_split_types_subst_default_eq
            : forall t idc evm,
                Raw.ident.to_type
                  (preinfos (raw_ident_infos_of (projT1 (@ident.split_types_subst_default base ident raw_ident raw_ident_infos_of pattern_ident split_types t idc evm))))
                  (Datatypes.fst (projT2 (@ident.split_types_subst_default base ident raw_ident raw_ident_infos_of pattern_ident split_types t idc evm)))
                  (Datatypes.snd (projT2 (@ident.split_types_subst_default base ident raw_ident raw_ident_infos_of pattern_ident split_types t idc evm)))
                = type.subst_default t evm;
            projT1_add_types_from_raw_sig_eq
            : forall t idc,
                projT1
                  (add_types_from_raw_sig
                     (projT1 (@split_raw_ident_gen t idc))
                     (projT1 (proj1_sig (projT2 (@split_raw_ident_gen t idc))))
                     (lift_type_of_list_map
                        (@ident.relax_kind_of_type base)
                        (Datatypes.fst (projT2 (proj1_sig (projT2 (@split_raw_ident_gen t idc)))))))
                = type.relax t;
            arg_types_unfolded : forall t (idc : pattern_ident t), list Type;
            to_typed_unfolded : forall t (idc : pattern_ident t) (evm : EvarMap), type_of_list (@arg_types_unfolded _ idc) -> ident (type.subst_default t evm);
            type_of_list_arg_types_beq_unfolded : forall t idc, type_of_list (@arg_types_unfolded t idc) -> type_of_list (@arg_types_unfolded t idc) -> bool;
            of_typed_ident_unfolded : forall t (idc : ident t), pattern_ident (type.relax t);
            arg_types_of_typed_ident_unfolded : forall t (idc : ident t), type_of_list (arg_types_unfolded _ (of_typed_ident_unfolded _ idc));
            unify : forall {t t'} (pidc : pattern_ident t) (idc : ident t')  , Datatypes.option (type_of_list (@ident.arg_types base ident raw_ident raw_ident_infos_of pattern_ident eta_pattern_ident_cps_gen split_types t pidc));
            unify_unknown : forall {t t'} (pidc : pattern_ident t) (idc : ident t')  , Datatypes.option (type_of_list (@ident.arg_types base ident raw_ident raw_ident_infos_of pattern_ident eta_pattern_ident_cps_gen split_types t pidc))
          }.

        Notation arg_types_of p := (@ident.arg_types _ _ (@raw_ident _ _ p) (@raw_ident_infos_of _ _ p) (@pattern_ident _ _ p) (@eta_pattern_ident_cps_gen _ _ p) (@split_types _ _ p)).
        Notation arg_types := (@arg_types_of _).
      End GoalType.
    End ident.
  End pattern.
Module Export Rewriter.
Module Export Compilers.

  Notation EvarMap := Compilers.pattern.EvarMap.
  Module pattern.
    Export IdentifiersLibrary.Compilers.pattern.

    Module Export type.
      Section with_base.
        Context {base : Type}
                (base_beq : base -> base -> bool).

        Local Notation forall_vars_body K LS EVM0
          := (fold_right
                (fun i k evm => forall t : Compilers.base.type base, k (PositiveMap.add i t evm))
                K
                LS
                EVM0).

        Definition forall_vars (p : PositiveSet.t) (k : EvarMap -> Type)
          := forall_vars_body k (List.rev (PositiveSet.elements p)) (PositiveMap.empty _).

        Definition under_forall_vars {p k1 k2}
                   (F : forall evm, k1 evm -> k2 evm)
          : forall_vars p k1 -> forall_vars p k2
          := list_rect
               (fun ls
                => forall evm0, forall_vars_body k1 ls evm0 -> forall_vars_body k2 ls evm0)
               F
               (fun x xs rec evm0 K1 t => rec _ (K1 t))
               (List.rev (PositiveSet.elements p))
               (PositiveMap.empty _).
      End with_base.
    End type.

    Inductive pattern {base} {ident : type base -> Type} : type base -> Type :=
    | Wildcard (t : type base) : pattern t
    | Ident {t} (idc : ident t) : pattern t
    | App {s d} (f : pattern (s -> d)) (x : pattern s) : pattern d.

    Module Export Notations.
      Delimit Scope pattern_scope with pattern.
      Bind Scope pattern_scope with pattern.
      Infix "@" := App : pattern_scope.
      Notation "# x" := (Ident x) : pattern_scope.
    End Notations.

    Record > anypattern {base} {ident : type base -> Type}
      := { type_of_anypattern : type base;
           pattern_of_anypattern :> @pattern base ident type_of_anypattern }.

    Fixpoint collect_vars {base ident}
             {t} (p : @pattern base ident t) : PositiveSet.t
      := match p with
         | Wildcard t => type.collect_vars t
         | Ident t idc => type.collect_vars t
         | App s d f x => PositiveSet.union (@collect_vars _ _ _ x) (@collect_vars _ _ _ f)
         end.
  End pattern.
  Export pattern.Notations.

  Module Export RewriteRules.
    Module Export Compile.
      Section with_var0.
        Context {base_type} {ident var : type.type base_type -> Type}.
        Local Notation type := (type.type base_type).
        Local Notation expr := (@expr.expr base_type ident var).
        Local Notation UnderLets := (@UnderLets.UnderLets base_type ident var).
        Let type_base (t : base_type) : type := type.base t.
        Coercion type_base : base_type >-> type.

        Fixpoint value' (with_lets : bool) (t : type)
          := match t with
             | type.base t
               => if with_lets then UnderLets (expr t) else expr t
             | type.arrow s d
               => value' false s -> value' true d
             end.
        Definition value := value' false.
      End with_var0.
      Section with_var.
        Local Notation type_of_list_cps
          := (fold_right (fun a K => a -> K)).
        Context {base : Type}
                {try_make_transport_base_type_cps : type.try_make_transport_cpsT base}
                (base_beq : base -> base -> bool).
        Local Notation base_type := (base.type base).
        Local Notation pattern_base_type := (pattern.base.type base).
        Context {ident var : type.type base_type -> Type}
                (eta_ident_cps : forall (T : type.type base_type -> Type) t (idc : ident t)
                                        (f : forall t', ident t' -> T t'),
                    T t)
                {pident : type.type pattern_base_type -> Type}
                (pident_arg_types : forall t, pident t -> list Type)
                (pident_unify pident_unify_unknown : forall t t' (idc : pident t) (idc' : ident t'), option (type_of_list (pident_arg_types t idc)))
                {raw_pident : Type}
                (strip_types : forall t, pident t -> raw_pident)
                (raw_pident_beq : raw_pident -> raw_pident -> bool)

                (full_types : raw_pident -> Type)
                (invert_bind_args invert_bind_args_unknown : forall t (idc : ident t) (pidc : raw_pident), option (full_types pidc))
                (type_of_raw_pident : forall (pidc : raw_pident), full_types pidc -> type.type base_type)
                (raw_pident_to_typed : forall (pidc : raw_pident) (args : full_types pidc), ident (type_of_raw_pident pidc args))
                (raw_pident_is_simple : raw_pident -> bool).

        Local Notation type := (type.type base_type).
        Local Notation pattern := (@pattern.pattern base pident).
        Local Notation anypattern := (@pattern.anypattern base pident).
        Local Notation UnderLets := (@UnderLets.UnderLets base_type ident var).
        Local Notation value := (@value base_type ident var).

        Definition under_type_of_list_cps {A1 A2 ls}
                   (F : A1 -> A2)
          : type_of_list_cps A1 ls -> type_of_list_cps A2 ls
          := list_rect
               (fun ls
                => type_of_list_cps A1 ls -> type_of_list_cps A2 ls)
               F
               (fun T Ts rec f x => rec (f x))
               ls.

        Fixpoint unification_resultT' {var} {t} (p : pattern t) (evm : EvarMap) : Type
          := match p return Type with
             | pattern.Wildcard t => var (pattern.type.subst_default t evm)
             | pattern.Ident t idc => type_of_list (pident_arg_types t idc)
             | pattern.App s d f x
               => @unification_resultT' var _ f evm * @unification_resultT' var _ x evm
             end%type.

        Fixpoint with_unification_resultT' {var} {t} (p : pattern t) (evm : EvarMap) (K : Type) : Type
          := match p return Type with
             | pattern.Wildcard t => var (pattern.type.subst_default t evm) -> K
             | pattern.Ident t idc => type_of_list_cps K (pident_arg_types t idc)
             | pattern.App s d f x
               => @with_unification_resultT' var _ f evm (@with_unification_resultT' var _ x evm K)
             end%type.

        Fixpoint under_with_unification_resultT' {var t p evm K1 K2}
                 (F : K1 -> K2)
                 {struct p}
          : @with_unification_resultT' var t p evm K1 -> @with_unification_resultT' var t p evm K2
          := match p return with_unification_resultT' p evm K1 -> with_unification_resultT' p evm K2 with
             | pattern.Wildcard t => fun f v => F (f v)
             | pattern.Ident t idc => under_type_of_list_cps F
             | pattern.App s d f x
               => @under_with_unification_resultT'
                    _ _ f evm _ _
                    (@under_with_unification_resultT' _ _ x evm _ _ F)
             end.

        Definition with_unification_resultT {var t} (p : pattern t) (K : type -> Type) : Type
          := pattern.type.forall_vars
               (pattern.collect_vars p)
               (fun evm => @with_unification_resultT' var t p evm (K (pattern.type.subst_default t evm))).

        Definition under_with_unification_resultT {var t p K1 K2}
                 (F : forall evm, K1 (pattern.type.subst_default t evm) -> K2 (pattern.type.subst_default t evm))
          : @with_unification_resultT var t p K1 -> @with_unification_resultT var t p K2
          := pattern.type.under_forall_vars
               (fun evm => under_with_unification_resultT' (F evm)).

        Local Notation expr_maybe_do_again should_do_again
          := (@expr.expr base_type ident (if should_do_again then value else var)).

        Local Notation deep_rewrite_ruleTP_gen' should_do_again with_opt under_lets t
          := (match (expr_maybe_do_again should_do_again t) with
              | x0 => match (if under_lets then UnderLets x0 else x0) with
                      | x1 => if with_opt then option x1 else x1
                      end
              end).

        Definition with_unif_rewrite_ruleTP_gen {var t} (p : pattern t) (should_do_again : bool) (with_opt : bool) (under_lets : bool)
          := @with_unification_resultT var t p (fun t => deep_rewrite_ruleTP_gen' should_do_again with_opt under_lets t).

        Record rewrite_rule_data {t} {p : pattern t} :=
          { rew_should_do_again : bool;
            rew_with_opt : bool;
            rew_under_lets : bool;
            rew_replacement : @with_unif_rewrite_ruleTP_gen value t p rew_should_do_again rew_with_opt rew_under_lets }.

        Definition rewrite_ruleTP
          := (fun p : anypattern => @rewrite_rule_data _ (pattern.pattern_of_anypattern p)).

        End with_var.

      End Compile.

    End RewriteRules.
End Compilers.
  Export Rewriter.Compilers.
      Import pattern.ident.GoalType.
      Section make_rewrite_rules.
          Context {base : Type}.
          Local Notation base_type := (base.type base).
          Local Notation type := (type.type base_type).
          Context {base_interp : base -> Type}
                  {ident : type -> Type}
                  {ident_interp : forall t, ident t -> type.interp (base.interp base_interp) t}
                  {BuildIdentT : @ident.BuildIdentT base base_interp ident}
                  {baseDefault : @DefaultValue.type.base.DefaultT base base_interp}
                  {pkg : @package base ident}
                  {var : type -> Type}.
          Local Notation value := (@value base_type ident var).
          Local Notation pattern := (@pattern.pattern base pattern_ident).
          Local Notation pbase_type := (pattern.base.type base).
          Local Notation ptype := (type.type pbase_type).
          Let type_base {base} (t : base.type base) : type.type (base.type base) := type.base t.
          Let ptype_base {base} (t : pattern.base.type base) : type.type (pattern.base.type base) := type.base t.
          Let type_base' (t : base) : base_type := base.type.type_base t.
          Let ptype_base' (t : base) : pbase_type := pattern.base.type.type_base t.
          Let type_base'' (t : base) : type := type.base (base.type.type_base t).
          Let ptype_base'' (t : base) : ptype := type.base (pattern.base.type.type_base t).
          Coercion ptype_base'' : base >-> ptype.
          Coercion ptype_base : pbase_type >-> ptype.
          Local Notation collect_vars := (@pattern.collect_vars base pattern_ident).
          Local Notation with_unification_resultT' := (@with_unification_resultT' base pattern_ident (@arg_types) value).
          Local Notation with_unification_resultT := (@with_unification_resultT base pattern_ident (@arg_types) value).
          Local Notation under_with_unification_resultT := (@under_with_unification_resultT base pattern_ident (@arg_types) value).
          Local Notation rewrite_ruleTP := (@rewrite_ruleTP base ident var pattern_ident (@arg_types)).
          Local Notation rewrite_rule_data := (@rewrite_rule_data base ident var pattern_ident (@arg_types)).

          Definition make_base_Literal_pattern_folded (t : base) : pattern t
            :=
              pattern.Ident (of_typed_ident_unfolded (type_base'' t) (ident.ident_Literal (t:=t) (DefaultValue.type.base.default (t:=type_base' t)))).

          Context (pident_pair : forall A B : pbase_type, pattern_ident (A -> B -> A * B)%ptype).

          Fixpoint make_Literal_pattern (t : pbase_type) : option (pattern t)
            := match t return option (pattern t) with
               | pattern.base.type.var _ => None
               | pattern.base.type.type_base t => Some (make_base_Literal_pattern_folded t)
               | pattern.base.type.prod A B
                 => (a <- make_Literal_pattern A;
                       b <- make_Literal_pattern B;
                       Some ((#(pident_pair _ _) @ a @ b)%pattern))
               | pattern.base.type.unit => None
               | pattern.base.type.list A => None
               | pattern.base.type.option A => None
               end%option.

          Fixpoint make_interp_rewrite_pattern {t}
            : pattern t -> option (pattern (type.final_codomain t))
            := match t return pattern t -> option (pattern (type.final_codomain t)) with
               | type.base t
                 => fun p => Some p
               | type.arrow (type.base s) d
                 => fun p => (x <- make_Literal_pattern s; @make_interp_rewrite_pattern d (pattern.App p x))%option
               | type.arrow _ _ => fun _ => None
               end.

          Context (cast_Literal_base_pattern_interp
                   : forall (evm : EvarMap) (t : base),
                      unification_resultT' (var:=var) (@arg_types) (make_base_Literal_pattern_folded t) evm
                      -> base.interp base_interp (pattern.base.subst_default (ptype_base' t) evm)).

          Definition strip_collect_vars
                     {s : pbase_type} {d : ptype}
                     {p : pattern (type.base s -> d)%ptype}
                     (p_res : pattern.type.forall_vars
                                (collect_vars p)
                                (fun evm =>
                                   with_unification_resultT'
                                     p evm
                                     (type.interp (base.interp base_interp) (pattern.type.subst_default (type.base s -> d)%ptype evm))))
            : forall (rec : forall x : pattern (type.base s),
                         pattern.type.forall_vars (PositiveSet.union (collect_vars x) (collect_vars p))
                                                  (fun evm =>
                                                     with_unification_resultT'
                                                       p evm
                                                       (with_unification_resultT'
                                                          x evm
                                                          (type.interp (base.interp base_interp) (pattern.type.subst_default d evm))))
                         -> match make_interp_rewrite_pattern (p @ x) with
                            | Some p' => @rewrite_rule_data _ p'
                            | None => True
                            end),
              match (x <- make_Literal_pattern s;
                       make_interp_rewrite_pattern (p @ x))%option with
              | Some p' => @rewrite_rule_data _ p'
              | None => True
              end.
admit.
Defined.

          Fixpoint make_interp_rewrite'_helper {t}
            : forall (p : pattern t)
                     (base_rewrite : with_unification_resultT p (type.interp (base.interp base_interp)))
                     (p' := make_interp_rewrite_pattern p),
              match p' return Type with
              | Some p' => rewrite_ruleTP {| pattern.pattern_of_anypattern := p' |}
              | None => True
              end
            := match t return (forall (p : pattern t)
                                      (base_rewrite : with_unification_resultT p (type.interp (base.interp base_interp)))
                                      (p' := make_interp_rewrite_pattern p),
                                  match p' return Type with
                                  | Some p' => rewrite_ruleTP {| pattern.pattern_of_anypattern := p' |}
                                  | None => True
                                  end)
               with
               | type.base t
                 => fun p base_rewrite
                    => {| rew_should_do_again := false;
                          rew_with_opt := false;
                          rew_under_lets := false;
                          rew_replacement
                          := under_with_unification_resultT
                               (fun evm v => ident.smart_Literal v)
                               base_rewrite |}
               | type.arrow (type.base s) d
                 => fun p base_rewrite
                    => let rec_call
                           := fun x => @make_interp_rewrite'_helper d (p @ x)%pattern in
                       strip_collect_vars base_rewrite rec_call
               | type.arrow _ _
                 => fun _ _ => I
               end.
