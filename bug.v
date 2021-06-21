(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "+implicit-core-hint-db,+implicits-in-term,+non-reversible-notation,+deprecated-intros-until-0,+deprecated-focus,+unused-intro-pattern,+deprecated-hint-constr,+fragile-hint-constr,+variable-collision,+unexpected-implicit-declaration,+omega-is-deprecated,+non-recursive" "-w" "-notation-overridden,-undeclared-scope,-deprecated-hint-rewrite-without-locality" "-w" "-notation-overridden,-undeclared-scope" "-w" "-deprecated-native-compiler-option" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/rewriter/src/Rewriter" "Rewriter" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-I" "/github/workspace/builds/coq/coq-failing/_build_ci/rewriter/src/Rewriter/Util/plugins" "-top" "UnderLetsProofs" "-native-compiler" "no") -*- *)
(* File reduced by coq-bug-finder from original input, then from 2099 lines to 52 lines, then from 134 lines to 406 lines, then from 410 lines to 215 lines, then from 297 lines to 2309 lines, then from 2308 lines to 382 lines, then from 460 lines to 1634 lines, then from 1635 lines to 736 lines, then from 811 lines to 2856 lines, then from 2859 lines to 1296 lines, then from 1360 lines to 1854 lines, then from 1857 lines to 1306 lines, then from 1337 lines to 1570 lines, then from 1574 lines to 1341 lines, then from 1365 lines to 1421 lines, then from 1425 lines to 1359 lines, then from 1383 lines to 1461 lines, then from 1465 lines to 1366 lines, then from 1388 lines to 1823 lines, then from 1826 lines to 1383 lines, then from 1403 lines to 1502 lines, then from 1505 lines to 1414 lines, then from 1433 lines to 1491 lines, then from 1495 lines to 1445 lines, then from 1464 lines to 1600 lines, then from 1604 lines to 1530 lines, then from 1548 lines to 1568 lines, then from 1572 lines to 1549 lines *)
(* coqc version 8.15+alpha compiled with OCaml 4.12.0
   coqtop version 8.15+alpha *)
Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.
Require Rewriter.Util.LetIn.
Module Export Rewriter_DOT_Util_DOT_Tactics_DOT_Head.
Module Export Rewriter.
Module Export Util.
Module Export Tactics.
Module Export Head.

Ltac head expr :=
  match expr with
  | ?f _ => head f
  | _ => expr
  end.

End Head.

End Tactics.

End Util.

End Rewriter.

End Rewriter_DOT_Util_DOT_Tactics_DOT_Head.
Require Coq.Strings.String.
Module Export Rewriter_DOT_Util_DOT_Tactics_DOT_BreakMatch.
Module Export Rewriter.
Module Export Util.
Module Export Tactics.
Module Export BreakMatch.
Ltac set_match_refl_hyp v' only_when :=
  lazymatch goal with
  | [ H : context G[match ?e with _ => _ end eq_refl] |- _ ]
    => only_when e;
       let T := fresh in
       evar (T : Type); evar (v' : T);
       subst T;
       let vv := (eval cbv delta [v'] in v') in
       let G' := context G[vv] in
       let G''' := context G[v'] in
       let G'' := type of H in
       unify G' G'';
       change G''' in H
  end.
Ltac destruct_by_existing_equation match_refl_hyp :=
  let v := (eval cbv delta [match_refl_hyp] in match_refl_hyp) in
  lazymatch v with
  | match ?e with _ => _ end (@eq_refl ?T ?e)
    => let H := fresh in
       let e' := fresh in
       pose e as e';
       change e with e' in (value of match_refl_hyp) at 1;
       first [ pose (@eq_refl T e : e = e') as H;
               change (@eq_refl T e) with H in (value of match_refl_hyp);
               clearbody H e'
             | pose (@eq_refl T e : e' = e) as H;
               change (@eq_refl T e) with H in (value of match_refl_hyp);
               clearbody H e' ];
       destruct e'; subst match_refl_hyp
  end.
Ltac destruct_rewrite_sumbool e :=
  let H := fresh in
  destruct e as [H|H];
  try lazymatch type of H with
      | ?LHS = ?RHS
        => lazymatch RHS with
           | context[LHS] => fail
           | _ => idtac
           end;
           rewrite ?H; rewrite ?H in *;
           repeat match goal with
                  | [ |- context G[LHS] ]
                    => let LHS' := fresh in
                       pose LHS as LHS';
                       let G' := context G[LHS'] in
                       change G';
                       replace LHS' with RHS by (subst LHS'; symmetry; apply H);
                       subst LHS'
                  end
      end.
Ltac break_match_hyps_step only_when :=
  match goal with
  | [ H : context[match ?e with _ => _ end] |- _ ]
    => only_when e; is_var e; destruct e
  | [ H : context[match ?e with _ => _ end] |- _ ]
    => only_when e;
       match type of e with
       | sumbool _ _ => destruct_rewrite_sumbool e
       end
  | [ H : context[if ?e then _ else _] |- _ ]
    => only_when e; destruct e eqn:?
  | [ H : context[match ?e with _ => _ end] |- _ ]
    => only_when e; destruct e eqn:?
  | _ => let v := fresh in set_match_refl_hyp v only_when; destruct_by_existing_equation v
  end.
Ltac break_innermost_match_hyps_step :=
  break_match_hyps_step ltac:(fun v => lazymatch v with
                                       | context[match _ with _ => _ end] => fail
                                       | _ => idtac
                                       end).
Ltac break_innermost_match_hyps := repeat break_innermost_match_hyps_step.

End BreakMatch.

End Tactics.

End Util.

End Rewriter.

End Rewriter_DOT_Util_DOT_Tactics_DOT_BreakMatch.
Module Export Rewriter_DOT_Util_DOT_Tactics_DOT_DestructHyps.
Module Export Rewriter.
Module Export Util.
Module Export Tactics.
Module Export DestructHyps.

Ltac do_one_match_then matcher do_tac tac :=
  idtac;
  match goal with
  | [ H : ?T |- _ ]
    => matcher T; do_tac H;
       try match type of H with
           | T => clear H
           end;
       tac
  end.

Ltac do_all_matches_then matcher do_tac tac :=
  repeat do_one_match_then matcher do_tac tac.

Ltac destruct_all_matches_then matcher tac :=
  do_all_matches_then matcher ltac:(fun H => destruct H) tac.
Ltac destruct_all_matches' matcher := destruct_all_matches_then matcher idtac.

End DestructHyps.

End Tactics.

End Util.

End Rewriter.

End Rewriter_DOT_Util_DOT_Tactics_DOT_DestructHyps.
Module Export Rewriter.
Module Export Util.
Module Export Tactics.
Module Export DestructHead.

Ltac destruct_head_matcher T HT :=
  match head HT with
  | T => idtac
  end.
Ltac destruct_head' T := destruct_all_matches' ltac:(destruct_head_matcher T).

Ltac destruct_one_head'_sig := match goal with H : sig _ |- _ => destruct H end.
Ltac destruct_head'_sig := repeat destruct_one_head'_sig.

Ltac destruct_one_head'_and := match goal with H : and _ _ |- _ => destruct H end.
Ltac destruct_head'_and := repeat destruct_one_head'_and.

Ltac destruct_one_head'_or := match goal with H : or _ _ |- _ => destruct H end.
Ltac destruct_head'_or := repeat destruct_one_head'_or.

Ltac destruct_one_head'_False := match goal with H : False |- _ => destruct H end.
Ltac destruct_head'_False := repeat destruct_one_head'_False.

End DestructHead.

End Tactics.

End Util.

End Rewriter.
Module Export Util.
Module Export Option.
Import Rewriter.Util.Notations.

Definition bind {A B} (v : option A) (f : A -> option B) : option B
  := match v with
     | Some v => f v
     | None => None
     end.

Module Export Notations.
  Delimit Scope option_scope with option.
  Notation "A <- X ; B" := (bind X (fun A => B%option)) : option_scope.
End Notations.

End Option.

End Util.
Import Coq.Lists.List.

Module Export Option.
  Module Export List.
    Definition lift {A} (ls : list (option A)) : option (list A)
      := fold_right (fun x xs => x <- x; xs <- xs; Some (x :: xs))%option
                    (Some nil)
                    ls.
Import Rewriter.Util.Notations.

Delimit Scope cps_scope with cps.

Definition cpscall {R} (f:forall{T}(continuation:R->T),T) {T} (continuation:R->T)
:= @f T continuation.
Notation "x' <- v ; C" := (cpscall v%cps (fun x' => C%cps)) : cps_scope.

Notation "~> R" := (forall T (_:R->T), T) : type_scope.

Notation "A ~> R" := (A -> ~>R) : type_scope.

Definition cpsreturn {T} (x:T) := x.

Notation "'return' x" := (cpsreturn (fun T (continuation:_->T) => continuation x)) : cps_scope.

Definition cpsbind {A B} (v:~> A) (f:A ~> B) : ~> B
  := fun T k => (a <- v; fa <- f a; k fa)%cps.

Definition cps_option_bind {A B} (v:~> option A) (f:A ~> option B) : ~> option B
  := cpsbind v (fun x' T k => match x' with Some x' => f x' T k | None => k None end).
Notation "x' <-- v ; C" := (cps_option_bind v%cps (fun x' => C%cps)) : cps_scope.

Section prod.

  Definition path_prod_uncurried {A B : Type} (u v : prod A B)
             (pq : prod (fst u = fst v) (snd u = snd v))
    : u = v.
admit.
Defined.

  Definition path_prod_rect {A B} {u v : @prod A B} (P : u = v -> Type)
             (f : forall p q, P (path_prod_uncurried u v (p, q)))
    : forall p, P p.
admit.
Defined.
End prod.

Ltac simpl_proj_pair_in H :=
  repeat match type of H with
         | context G[fst (pair ?x ?p)]
           => let G' := context G[x] in change G' in H
         | context G[snd (pair ?x ?p)]
           => let G' := context G[p] in change G' in H
         end.
Ltac induction_path_prod H :=
  let H0 := fresh H in
  let H1 := fresh H in
  induction H as [H0 H1] using path_prod_rect;
  simpl_proj_pair_in H0;
  simpl_proj_pair_in H1.
Ltac inversion_prod_step :=
  match goal with
  | [ H : _ = pair _ _ |- _ ]
    => induction_path_prod H
  | [ H : pair _ _ = _ |- _ ]
    => induction_path_prod H
  end.
Ltac inversion_prod := repeat inversion_prod_step.
Module Export Reflect.
Import Coq.Bool.Bool.

Lemma reflect_to_dec {P b1 b2} : reflect P b1 -> (b1 = b2) -> (if b2 then P else ~P).
admit.
Defined.

Definition mark {T} (v : T) := v.

Existing Class reflect.
Notation reflect_rel P b := (forall x y, reflect (P x y) (b x y)).
Module Export Language.
Import Coq.Classes.Morphisms.
Import Coq.Relations.Relation_Definitions.
Import Rewriter.Util.LetIn.

Import EqNotations.
Module Export Compilers.
  Module Export type.
    Inductive type {base_type : Type} := base (t : base_type) | arrow (s d : type).
    Global Arguments type : clear implicits.

    Fixpoint final_codomain {base_type} (t : type base_type) : base_type
      := match t with
         | base t
           => t
         | arrow s d => @final_codomain base_type d
         end.

    Fixpoint for_each_lhs_of_arrow {base_type} (f : type base_type -> Type) (t : type base_type) : Type
      := match t with
         | base t => unit
         | arrow s d => f s * @for_each_lhs_of_arrow _ f d
         end.

    Fixpoint interp {base_type} (base_interp : base_type -> Type) (t : type base_type) : Type
      := match t with
         | base t => base_interp t
         | arrow s d => @interp _ base_interp s -> @interp _ base_interp d
         end.

    Fixpoint related {base_type} {base_interp : base_type -> Type} (R : forall t, relation (base_interp t)) {t : type base_type}
      : relation (interp base_interp t)
      := match t with
         | base t => R t
         | arrow s d => @related _ _ R s ==> @related _ _ R d
         end%signature.

    Notation eqv := (@related _ _ (fun _ => eq)).

    Class try_make_transport_cpsT {base : Type}
      := try_make_transport_cpsv : forall (P : base -> Type) t1 t2, ~> option (P t1 -> P t2).

    Class try_make_transport_cps_correctT {base : Type}
          {base_beq : base -> base -> bool}
          {try_make_transport_cps : @type.try_make_transport_cpsT base}
          {reflect_base_beq : reflect_rel (@eq base) base_beq}
      := try_make_transport_cps_correctP
         : forall P t1 t2,
          try_make_transport_cps P t1 t2
          = fun T k
            => k match Sumbool.sumbool_of_bool (base_beq t1 t2) with
                 | left pf => Some (rew [fun t => P t1 -> P t] (reflect_to_dec _ pf) in id)
                 | right _ => None
                 end.
    Global Arguments try_make_transport_cps_correctT base {_ _ _}.

    Section transport_cps.
      Context {base_type : Type}.
      Context {try_make_transport_base_type_cps : @try_make_transport_cpsT base_type}.

      Fixpoint try_make_transport_cps (P : type base_type -> Type) (t1 t2 : type base_type)
        : ~> option (P t1 -> P t2)
        := match t1, t2 with
           | base t1, base t2 => try_make_transport_base_type_cps (fun t => P (base t)) t1 t2
           | arrow s1 d1, arrow s2 d2
             => (trs <-- try_make_transport_cps (fun s => P (arrow s _)) _ _;
                  trd <-- try_make_transport_cps (fun d => P (arrow _ d)) _ _;
                return (Some (fun v => trd (trs v))))
           | base _, _
           | arrow _ _, _
             => (return None)
           end%cps.

      Definition try_transport_cps (P : type base_type -> Type) (t1 t2 : type base_type) (v : P t1) : ~> option (P t2)
        := (tr <-- try_make_transport_cps P t1 t2;
            return (Some (tr v)))%cps.

      Definition try_transport (P : type base_type -> Type) (t1 t2 : type base_type) (v : P t1) : option (P t2)
        := try_transport_cps P t1 t2 v _ id.
    End transport_cps.
  End type.
  Delimit Scope etype_scope with etype.
  Bind Scope etype_scope with type.type.
  Global Arguments type.base {_} _%etype.
  Infix "->" := type.arrow : etype_scope.
  Infix "==" := type.eqv : type_scope.
  Module base.
    Module type.
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

    Fixpoint try_make_transport_cps
             {base}
             {try_make_transport_base_type_cps : @type.try_make_transport_cpsT base}
             (P : type base -> Type) (t1 t2 : type base)
      : ~> option (P t1 -> P t2)
      := match t1, t2 with
         | type.type_base t1, type.type_base t2
           => type.try_make_transport_cpsv (fun t => P (type.type_base t)) t1 t2
         | type.unit, type.unit
           => (return (Some (fun x => x)))
         | type.prod A B, type.prod A' B'
           => (trA <-- try_make_transport_cps (fun A => P (type.prod A _)) _ _;
                trB <-- try_make_transport_cps (fun B => P (type.prod _ B)) _ _;
              return (Some (fun v => trB (trA v))))
         | type.list A, type.list A' => try_make_transport_cps (fun A => P (type.list A)) A A'
         | type.option A, type.option A' => try_make_transport_cps (fun A => P (type.option A)) A A'
         | type.type_base _, _
         | type.prod _ _, _
         | type.list _, _
         | type.option _, _
         | type.unit, _
           => (return None)
         end%cps.

    Global Hint Extern 1 (@type.try_make_transport_cpsT (type ?base)) => notypeclasses refine (@try_make_transport_cps base _) : typeclass_instances.

  End base.
  Infix "*" := base.type.prod : etype_scope.

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

    Fixpoint interp {base_type ident} {interp_base_type : base_type -> Type}
             (interp_ident : forall t, ident t -> type.interp interp_base_type t)
             {t} (e : @expr base_type ident (type.interp interp_base_type) t)
      : type.interp interp_base_type t
      := match e in expr t return type.interp _ t with
         | Ident t idc => interp_ident _ idc
         | Var t v => v
         | Abs s d f => fun x : type.interp interp_base_type s
                        => @interp _ _ _ interp_ident _ (f x)
         | App s d f x => (@interp _ _ _ interp_ident _ f)
                            (@interp _ _ _ interp_ident _ x)
         | LetIn A B x f
           => dlet y := @interp _ _ _ interp_ident _ x in
               @interp _ _ _ interp_ident _ (f y)
         end.

    Module Export Notations.
      Delimit Scope expr_scope with expr.
      Delimit Scope expr_pat_scope with expr_pat.
      Bind Scope expr_scope with expr.
      Infix "@" := App : expr_scope.
      Notation "'$' x" := (Var x) : expr_scope.
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

    Module Export Notations.
      Notation "# x" := (expr.Ident x) (only parsing) : expr_pat_scope.
      Notation "# x" := (@expr.Ident _ _ _ _ x) : expr_scope.
      Notation "x @ y" := (expr.App x%expr_pat y%expr_pat) (only parsing) : expr_pat_scope.

      Notation "( x , y , .. , z )" := (expr.App (expr.App (#ident_pair) .. (expr.App (expr.App (#ident_pair) x%expr) y%expr) .. ) z%expr) : expr_scope.
      Notation "x :: y" := (#ident_cons @ x @ y)%expr : expr_scope.
      Notation "[ ]" := (#ident_nil)%expr : expr_scope.
    End Notations.
  End ident.

  Module Import invert_expr.
    Section with_var_gen.
      Context {base_type} {ident var : type base_type -> Type}.
      Local Notation expr := (@expr base_type ident var).
      Local Notation if_arrow f t
        := (match t return Type with
            | type.arrow s d => f s d
            | type.base _ => unit
            end) (only parsing).
      Definition invert_Ident {t} (e : expr t)
        : option (ident t)
        := match e with
           | expr.Ident t idc => Some idc
           | _ => None
           end.
      Definition invert_App_cps {t P Q} (e : expr t)
                 (F1 : forall s d, expr (s -> d) -> P s d)
                 (F2 : forall t, expr t -> Q t)
        : option { s : _ & P s t * Q s }%type
        := match e with
           | expr.App A B f x => Some (existT _ A (F1 _ _ f, F2 _ x))
           | _ => None
           end.
      Definition invert_App {t} (e : expr t)
        : option { s : _ & expr (s -> t) * expr s }%type
        := invert_App_cps e (fun _ _ x => x) (fun _ x => x).
      Definition invert_Abs {s d} (e : expr (s -> d))
        : option (var s -> expr d)%type
        := match e in expr.expr t return option (if_arrow (fun s d => var s -> expr d) t) with
           | expr.Abs s d f => Some f
           | _ => None
           end.
      Definition invert_LetIn {t} (e : expr t)
        : option { s : _ & expr s * (var s -> expr t) }%type
        := match e with
           | expr.LetIn A B x f => Some (existT _ A (x, f))
           | _ => None
           end.
      Definition invert_App2_cps {t P Q R} (e : expr t)
                 (F1 : forall s d, expr (s -> d) -> P s d)
                 (F2 : forall t, expr t -> Q t)
                 (F3 : forall t, expr t -> R t)
        : option { ss' : _ & P (fst ss') (snd ss' -> t)%etype * Q (fst ss') * R (snd ss') }%type
        := (v1 <- invert_App_cps e (fun _ _ f => invert_App_cps f F1 F2) F3;
           let '(existT s (v2, r)) := v1 in
           v2 <- v2;
           let '(existT s' (p, q)) := v2 in
           Some (existT _ (s', s) (p, q, r)))%option.
      Definition invert_App2 {t} (e : expr t)
        : option { ss' : _ & expr (fst ss' -> snd ss' -> t) * expr (fst ss') * expr (snd ss') }%type
        := invert_App2_cps e (fun _ _ x => x) (fun _ x => x) (fun _ x => x).
      Definition invert_AppIdent_cps {t P} (e : expr t)
                 (F : forall t, expr t -> P t)
        : option { s : _ & ident (s -> t) * P s }%type
        := (e <- invert_App_cps e (fun _ _ f => f) F;
           let '(existT s (f, x)) := e in
           f' <- invert_Ident f;
           Some (existT _ s (f', x)))%option.
      Definition invert_AppIdent {t} (e : expr t)
        : option { s : _ & ident (s -> t) * expr s }%type
        := invert_AppIdent_cps e (fun _ x => x).
      Definition invert_AppIdent2_cps {t Q R} (e : expr t)
                 (F1 : forall t, expr t -> Q t)
                 (F2 : forall t, expr t -> R t)
        : option { ss' : _ & ident (fst ss' -> snd ss' -> t) * Q (fst ss') * R (snd ss') }%type
        := (e <- invert_App2_cps e (fun _ _ x => x) F1 F2;
           let '(existT ss' (f, x, x')) := e in
           f' <- invert_Ident f;
           Some (existT _ ss' (f', x, x')))%option.
      Definition invert_AppIdent2 {t} (e : expr t)
        : option { ss' : _ & ident (fst ss' -> snd ss' -> t) * expr (fst ss') * expr (snd ss') }%type
        := invert_AppIdent2_cps e (fun _ x => x) (fun _ x => x).
      Definition invert_Var {t} (e : expr t)
        : option (var t)
        := match e with
           | expr.Var t v => Some v
           | _ => None
           end.

      Fixpoint App_curried {t} : expr t -> type.for_each_lhs_of_arrow expr t -> expr (type.base (type.final_codomain t))
        := match t with
           | type.base t => fun e _ => e
           | type.arrow s d => fun e x => @App_curried d (e @ (fst x)) (snd x)
           end.
      Fixpoint invert_App_curried {t} (e : expr t)
        : type.for_each_lhs_of_arrow expr t -> { t' : _ & expr t' * type.for_each_lhs_of_arrow expr t' }%type
        := match e in expr.expr t return type.for_each_lhs_of_arrow expr t -> { t' : _ & expr t' * type.for_each_lhs_of_arrow expr t' }%type with
           | expr.App s d f x
             => fun args
                => @invert_App_curried _ f (x, args)
           | e => fun args => existT _ _ (e, args)
           end.
      Definition invert_AppIdent_curried {t} (e : expr t)
        : option { t' : _ & ident t' * type.for_each_lhs_of_arrow expr t' }%type
        := match t return expr t -> _ with
           | type.base _ => fun e => let 'existT t (f, args) := invert_App_curried e tt in
                                     (idc <- invert_Ident f;
                                        Some (existT _ t (idc, args)))%option
           | _ => fun _ => None
           end e.
    End with_var_gen.

    Section with_container.
      Context {base : Type}
              {base_interp : base -> Type}
              {try_make_transport_base_type_cps : @type.try_make_transport_cpsT base}.
      Local Notation base_type := (@base.type base).
      Local Notation type := (@type.type base_type).
      Context {ident var : type -> Type}.
      Class InvertIdentT :=
        {
          invert_ident_Literal : forall {t}, ident t -> option (type.interp (base.interp base_interp) t);
          is_nil : forall {t}, ident t -> bool;
          is_cons : forall {t}, ident t -> bool;
          is_Some : forall {t}, ident t -> bool;
          is_None : forall {t}, ident t -> bool;
          is_pair : forall {t}, ident t -> bool;
          is_tt : forall {t}, ident t -> bool
        }.
      Context {invertIdent : InvertIdentT}.

      Section correctness_class.
        Context {buildIdent : ident.BuildIdentT base_interp ident}.

        Class BuildInvertIdentCorrectT :=
          {
            invert_ident_Literal_correct
            : forall {t idc v},
              invert_ident_Literal (t:=t) idc = Some v
              <-> match t return ident t -> type.interp (base.interp base_interp) t -> Prop with
                  | type.base (base.type.type_base t)
                    => fun idc v => idc = ident.ident_Literal (t:=t) v
                  | _ => fun _ _ => False
                  end idc v;
            is_nil_correct
            : forall {t idc},
                is_nil (t:=t) idc = true
                <-> match t return ident t -> Prop with
                    | type.base (base.type.list t)
                      => fun idc => idc = ident.ident_nil (t:=t)
                    | _ => fun _ => False
                    end idc;
            is_cons_correct
            : forall {t idc},
                is_cons (t:=t) idc = true
                <-> match t return ident t -> Prop with
                    | type.base t -> type.base (base.type.list _) -> type.base (base.type.list _)
                      => fun idc => existT _ _ idc = existT _ _ (ident.ident_cons (t:=t)) :> sigT ident
                    | _ => fun _ => False
                    end%etype idc;
            is_Some_correct
            : forall {t idc},
                is_Some (t:=t) idc = true
                <-> match t return ident t -> Prop with
                    | type.base t -> type.base (base.type.option _)
                      => fun idc => existT _ _ idc = existT _ _ (ident.ident_Some (t:=t)) :> sigT ident
                    | _ => fun _ => False
                    end%etype idc;
            is_None_correct
            : forall {t idc},
                is_None (t:=t) idc = true
                <-> match t return ident t -> Prop with
                    | type.base (base.type.option t)
                      => fun idc => idc = ident.ident_None (t:=t)
                    | _ => fun _ => False
                    end idc;
            is_pair_correct
            : forall {t idc},
                is_pair (t:=t) idc = true
                <-> match t return ident t -> Prop with
                    | type.base A -> type.base B -> type.base (base.type.prod _ _)
                      => fun idc => existT _ _ idc = existT _ _ (ident.ident_pair (A:=A) (B:=B)) :> sigT ident
                    | _ => fun _ => False
                    end%etype idc;
            is_tt_correct
            : forall {t idc},
                is_tt (t:=t) idc = true
                <-> match t return ident t -> Prop with
                    | type.base base.type.unit
                      => fun idc => idc = ident.ident_tt
                    | _ => fun _ => False
                    end%etype idc;
          }.
      End correctness_class.

      Local Notation expr := (@expr.expr base_type ident var).
      Local Notation try_transportP P := (@type.try_transport _ _ P _ _).
      Local Notation try_transport := (try_transportP _).
      Let base' {bt} (x : Compilers.base.type bt) : type.type _ := type.base x.
      Local Coercion base' : base.type >-> type.type.

      Fixpoint reflect_list_cps' {t} (e : expr t)
        : ~> option (list (expr (type.base match t return base_type with
                                           | type.base (base.type.list t) => t
                                           | _ => base.type.unit
                                           end)))
        := match e in expr.expr t
                 return ~> option (list (expr (type.base match t return base_type with
                                                         | type.base (base.type.list t) => t
                                                         | _ => base.type.unit
                                                         end)))
           with
           | #maybe_nil => if is_nil maybe_nil then (return (Some nil)) else (return None)
           | #maybe_cons @ x @ xs
             => if is_cons maybe_cons
                then (x' <-- type.try_transport_cps expr _ _ x;
                        xs' <-- @reflect_list_cps' _ xs;
                        xs' <-- type.try_transport_cps (fun t => list (expr (type.base match t return base_type with
                                                                                                                                                 | type.base (base.type.list t) => t
                                                                                                                                                 | _ => base.type.unit
                                                                                                                                                 end))) _ _ xs';
                      return (Some (x' :: xs')%list))
                else (return None)
           | _ => (return None)
           end%expr_pat%expr%cps.

      Definition reflect_list_cps {t} (e : expr (type.base (base.type.list t)))
        : ~> option (list (expr (type.base t)))
        := reflect_list_cps' e.
      Global Arguments reflect_list_cps {t} e [T] k.

      Definition reflect_list {t} (e : expr (type.base (base.type.list t)))
        : option (list (expr (type.base t)))
        := reflect_list_cps e id.

      Definition invert_pair_cps {t P Q} (e : expr t)
                 (F1 : forall t, expr t -> P t)
                 (F2 : forall t, expr t -> Q t)
                 (A := match t with type.base (base.type.prod A B) => A | _ => t end)
                 (B := match t with type.base (base.type.prod A B) => B | _ => t end)
        : option (P A * Q B)
        := (v <- invert_AppIdent2_cps e F1 F2;
           let '(existT _ (maybe_pair, a, b)) := v in
           if is_pair maybe_pair
           then a <- try_transport a; b <- try_transport b; Some (a, b)%core
           else None)%option.
      Definition invert_pair {A B} (e : expr (A * B))
        : option (expr A * expr B)
        := invert_pair_cps e (fun _ x => x) (fun _ x => x).
      Definition invert_Literal {t} (e : expr t)
        : option (type.interp (base.interp base_interp) t)
        := match e with
           | expr.Ident _ idc => invert_ident_Literal idc
           | _ => None
           end%expr_pat%expr.
      Definition invert_nil {t} (e : expr (base.type.list t)) : bool
        := match invert_Ident e with
           | Some maybe_nil => is_nil maybe_nil
           | _ => false
           end.
      Definition invert_None {t} (e : expr (base.type.option t)) : bool
        := match invert_Ident e with
           | Some maybe_None => is_None maybe_None
           | _ => false
           end.
      Definition invert_Some {t} (e : expr (base.type.option t))
        : option (expr t)
        := match e with
           | #maybe_Some @ v
             => if is_Some maybe_Some
                then try_transport v
                else None
           | _ => None
           end%expr_pat.
      Definition invert_tt (e : expr base.type.unit) : bool
        := match invert_Ident e with
           | Some maybe_tt => is_tt maybe_tt
           | _ => false
           end.

      Definition reflect_option {t} (e : expr (base.type.option t))
        : option (option (expr t))
        := match invert_None e, invert_Some e with
           | true, _ => Some None
           | _, Some x => Some (Some x)
           | false, None => None
           end.

      Definition invert_cons_cps {t P Q} (e : expr t)
                 (F1 : forall t, expr t -> P t)
                 (F2 : forall t, expr t -> Q t)
                 (A := match t with type.base (base.type.list A) => A | _ => base.type.unit end)
        : option (P A * Q (base.type.list A))
        := (v <- invert_AppIdent2_cps e F1 F2;
           let '(existT _ (maybe_cons, a, b)) := v in
           if is_cons maybe_cons
           then a <- try_transport a; b <- try_transport b; Some (a, b)%core
           else None)%option.

      Definition invert_cons {t} (e : expr (base.type.list t))
        : option (expr t * expr (base.type.list t))
        := invert_cons_cps e (fun _ x => x) (fun _ x => x).

      Fixpoint reflect_smart_Literal {t : base_type} : expr t -> option (base.interp base_interp t)
        := match t with
           | base.type.type_base t => invert_Literal
           | base.type.prod A B
             => fun e => ab <- invert_pair e;
                           a <- @reflect_smart_Literal A (fst ab);
                           b <- @reflect_smart_Literal B (snd ab);
                           Some (a, b)
           | base.type.list A
             => fun e => e <- reflect_list e;
                           Option.List.lift (List.map (@reflect_smart_Literal A) e)
           | base.type.option A
             => fun e => e <- reflect_option e;
                           match e with
                           | Some e => option_map (@Some _) (@reflect_smart_Literal A e)
                           | None => Some None
                           end
           | base.type.unit => fun e => if invert_tt e then Some tt else None
           end%option.
    End with_container.
  End invert_expr.

  End Compilers.

End Language.
Import EqNotations.
Module Export Compilers.

  Module Export type.

    Section with_base.
      Context {base_type : Type}.
      Local Notation type := (type.type base_type).

      Section encode_decode.
        Definition code (t1 t2 : type) : Prop
          := match t1, t2 with
             | type.base t1, type.base t2 => t1 = t2
             | type.arrow s1 d1, type.arrow s2 d2 => s1 = s2 /\ d1 = d2
             | type.base _, _
             | type.arrow _ _, _
               => False
             end.
        Definition decode (x y : type) : code x y -> x = y.
        Proof.
destruct x, y; intro p; try assumption; destruct p; (apply f_equal || apply f_equal2); (assumption || reflexivity).
Defined.

        Definition path_rect {x y : type} (Q : x = y -> Type)
                   (f : forall p, Q (decode x y p))
          : forall p, Q p.
admit.
Defined.
      End encode_decode.

      Lemma preinvert_one_type (P : type -> Type) t (Q : P t -> Type)
        : (forall t' (v : P t') (pf : t' = t), Q (rew [P] pf in v)) -> (forall (v : P t), Q v).
admit.
Defined.
    End with_base.

    Ltac induction_type_in_using H rect :=
      induction H as [H] using (rect _ _ _);
      cbv [code] in H;
      let H1 := fresh H in
      let H2 := fresh H in
      try lazymatch type of H with
          | False => exfalso; exact H
          | True => destruct H
          | _ /\ _ => destruct H as [H1 H2]
          end.
    Ltac inversion_type_step :=
      first [ lazymatch goal with
              | [ H : ?x = ?x :> type.type _ |- _ ] => clear H
              | [ H : ?x = ?y :> type.type _ |- _ ] => subst x || subst y
              end
            | lazymatch goal with
              | [ H : _ = type.base _ |- _ ]
                => induction_type_in_using H @path_rect
              | [ H : type.base _ = _ |- _ ]
                => induction_type_in_using H @path_rect
              | [ H : _ = type.arrow _ _ |- _ ]
                => induction_type_in_using H @path_rect
              | [ H : type.arrow _ _ = _ |- _ ]
                => induction_type_in_using H @path_rect
              end ];
      cbv [decode] in *;
      cbn [f_equal f_equal2 eq_rect decode] in *.
    Ltac inversion_type := repeat inversion_type_step.
    Ltac generalize_one_eq_var e :=
      match goal with
      | [ |- ?G ] => change (mark G)
      end;
      revert dependent e;
      lazymatch goal with
      | [ |- forall e' : ?P ?t, @?Q e' ]
        => refine (@preinvert_one_type _ P t Q _)
      end;
      intros ? e ?; intros; cbv [mark].

    Ltac invert_one e :=
      generalize_one_eq_var e;
      destruct e;
      try discriminate;
      type.inversion_type.

    End type.

  Module Export expr.

    Ltac invert_match_step :=
      match goal with
      | [ H : context[match ?e with expr.Var _ _ => _ | _ => _ end] |- _ ]
        => type.invert_one e
      | [ |- context[match ?e with expr.Var _ _ => _ | _ => _ end] ]
        => type.invert_one e
      end.

    Ltac invert_match := repeat invert_match_step.

    Section with_var.
      Context {base_type : Type}
              {ident var : type.type base_type -> Type}.
      Local Notation expr := (@expr.expr base_type ident var).

      Section encode_decode.

        Lemma invert_App_cps_id {t P Q e F1 F2} : @invert_expr.invert_App_cps _ _ _ t P Q e F1 F2 = option_map (fun '(existT s (x, y)) => existT _ s (F1 _ _ x, F2 _ y)) (@invert_expr.invert_App base_type ident var _ e).
admit.
Defined.
        Lemma invert_App2_cps_id {t P Q R e F1 F2 F3} : @invert_expr.invert_App2_cps _ _ _ t P Q R e F1 F2 F3 = option_map (fun '(existT ss' (x, y, z)) => existT _ ss' (F1 _ _ x, F2 _ y, F3 _ z)) (@invert_expr.invert_App2 base_type ident var _ e).
admit.
Defined.
        Lemma invert_AppIdent_cps_id {t P e F} : @invert_expr.invert_AppIdent_cps _ _ _ t P e F = option_map (fun '(existT s (idc, x)) => existT _ s (idc, F _ x)) (@invert_expr.invert_AppIdent base_type ident var _ e).
admit.
Defined.
        Lemma invert_AppIdent2_cps_id {t Q R e F1 F2} : @invert_expr.invert_AppIdent2_cps _ _ _ t Q R e F1 F2 = option_map (fun '(existT ss' (idc, x, y)) => existT _ ss' (idc, F1 _ x, F2 _ y)) (@invert_expr.invert_AppIdent2 base_type ident var _ e).
admit.
Defined.

        Lemma invert_Ident_Some {t} {e : expr t} {v} : invert_expr.invert_Ident e = Some v -> e = expr.Ident v.
admit.
Defined.
        Lemma invert_Var_Some {t} {e : expr t} {v} : invert_expr.invert_Var e = Some v -> e = expr.Var v.
admit.
Defined.
        Lemma invert_Abs_Some {s d} {e : expr (s -> d)} {v} : invert_expr.invert_Abs e = Some v -> e = expr.Abs v.
admit.
Defined.
        Lemma invert_App_Some {t} {e : expr t} {v} : invert_expr.invert_App e = Some v -> e = expr.App (fst (projT2 v)) (snd (projT2 v)).
admit.
Defined.
        Lemma invert_LetIn_Some {t} {e : expr t} {v} : invert_expr.invert_LetIn e = Some v -> e = expr.LetIn (fst (projT2 v)) (snd (projT2 v)).
admit.
Defined.
        Lemma invert_App2_Some {t} {e : expr t} {v} : invert_expr.invert_App2 e = Some v -> e = expr.App (expr.App (fst (fst (projT2 v))) (snd (fst (projT2 v)))) (snd (projT2 v)).
admit.
Defined.
        Lemma invert_AppIdent_Some {t} {e : expr t} {v} : invert_expr.invert_AppIdent e = Some v -> e = expr.App (expr.Ident (fst (projT2 v))) (snd (projT2 v)).
admit.
Defined.
        Lemma invert_AppIdent2_Some {t} {e : expr t} {v} : invert_expr.invert_AppIdent2 e = Some v -> e = expr.App (expr.App (expr.Ident (fst (fst (projT2 v)))) (snd (fst (projT2 v)))) (snd (projT2 v)).
admit.
Defined.
        Lemma invert_App_curried_Some_sig {t} {e : expr t} {args} {v}
          : invert_expr.invert_App_curried e args = v
            -> { pf : type.final_codomain _ = type.final_codomain t
               | invert_expr.App_curried e args = rew [fun t => expr (type.base t)] pf in invert_expr.App_curried (fst (projT2 v)) (snd (projT2 v)) }.
admit.
Defined.
        Lemma invert_AppIdent_curried_Some_sig {t} {e : expr t} {v}
          : invert_expr.invert_AppIdent_curried e = Some v
            -> { pf : type.base (type.final_codomain _) = t
               | e = rew pf in invert_expr.App_curried (expr.Ident (fst (projT2 v))) (snd (projT2 v)) }.
admit.
Defined.
      End encode_decode.
    End with_var.

    Ltac invert_subst_simple_step_helper guard_tac :=
      match goal with
      | [ H : @invert_expr.invert_Var ?base_type ?ident ?var ?t ?e = Some _ |- _ ]
        => guard_tac H; apply (@invert_Var_Some base_type ident var t e) in H
      | [ H : @invert_expr.invert_Ident ?base_type ?ident ?var ?t ?e = Some _ |- _ ]
        => guard_tac H; apply (@invert_Ident_Some base_type ident var t e) in H
      | [ H : @invert_expr.invert_LetIn ?base_type ?ident ?var ?t ?e = Some _ |- _ ]
        => guard_tac H; apply (@invert_LetIn_Some base_type ident var t e) in H
      | [ H : @invert_expr.invert_App ?base_type ?ident ?var ?t ?e = Some _ |- _ ]
        => guard_tac H; apply (@invert_App_Some base_type ident var t e) in H
      | [ H : @invert_expr.invert_Abs ?base_type ?ident ?var ?s ?d ?e = Some _ |- _ ]
        => guard_tac H; apply (@invert_Abs_Some base_type ident var s d e) in H
      | [ H : @invert_expr.invert_App2 ?base_type ?ident ?var ?t ?e = Some _ |- _ ]
        => guard_tac H; apply (@invert_App2_Some base_type ident var t e) in H
      | [ H : @invert_expr.invert_AppIdent ?base_type ?ident ?var ?t ?e = Some _ |- _ ]
        => guard_tac H; apply (@invert_AppIdent_Some base_type ident var t e) in H
      | [ H : @invert_expr.invert_AppIdent2 ?base_type ?ident ?var ?t ?e = Some _ |- _ ]
        => guard_tac H; apply (@invert_AppIdent2_Some base_type ident var t e) in H
      | [ H : @invert_expr.invert_App_curried ?base_type ?ident ?var ?t ?e ?args = ?v |- _ ]
        => guard_tac H; apply (@invert_App_curried_Some_sig base_type ident var t e args) in H
      | [ H : @invert_expr.invert_AppIdent_curried ?base_type ?ident ?var ?t ?e = Some ?v |- _ ]
        => guard_tac H; apply (@invert_AppIdent_curried_Some_sig base_type ident var t e) in H
      | [ H : context[@invert_expr.invert_App_cps ?base_type ?ident ?var ?t ?P ?Q ?e ?F1 ?F2] |- _ ]
        => guard_tac H; rewrite (@invert_App_cps_id base_type ident var t P Q e F1 F2) in H; cbv [option_map] in H
      | [ H : context[@invert_expr.invert_App2_cps ?base_type ?ident ?var ?t ?P ?Q ?R ?e ?F1 ?F2 ?F3] |- _ ]
        => guard_tac H; rewrite (@invert_App2_cps_id base_type ident var t P Q R e F1 F2 F3) in H; cbv [option_map] in H
      | [ H : context[@invert_expr.invert_AppIdent_cps ?base_type ?ident ?var ?t ?P ?e ?F1] |- _ ]
        => guard_tac H; rewrite (@invert_AppIdent_cps_id base_type ident var t P e F1) in H; cbv [option_map] in H
      | [ H : context[@invert_expr.invert_AppIdent2_cps ?base_type ?ident ?var ?t ?P ?Q ?e ?F1 ?F2] |- _ ]
        => guard_tac H; rewrite (@invert_AppIdent2_cps_id base_type ident var t P Q e F1 F2) in H; cbv [option_map] in H
      end.

    Section with_container.
      Import invert_expr.
      Context {base : Type}
              {base_interp : base -> Type}
              {try_make_transport_base_cps : @type.try_make_transport_cpsT base}
              {base_beq : base -> base -> bool}.
      Local Notation base_type := (@base.type base).
      Local Notation type := (@type.type base_type).
      Context {ident : type -> Type}.
      Context {invertIdent : @InvertIdentT base base_interp ident}.
      Context {buildIdent : @ident.BuildIdentT base base_interp ident}.

      Lemma invert_ident_Literal_ident_Literal
        : forall {t v}, invert_ident_Literal (ident.ident_Literal (t:=t) v) = Some v.
admit.
Defined.
      Let base' {bt} (x : Compilers.base.type bt) : type.type _ := type.base x.
      Local Coercion base' : base.type >-> type.type.

      Section with_var1.
        Context {var : type -> Type}.

        Local Notation expr := (@expr.expr base_type ident var).

        Lemma invert_pair_cps_id {A B P Q e F1 F2} : @invert_expr.invert_pair_cps _ _ _ _ _ _ (A * B) P Q e F1 F2 = option_map (fun '(a, b) => (F1 _ a, F2 _ b)) (invert_expr.invert_pair (var:=var) e).
admit.
Defined.
        Lemma invert_cons_cps_id {t P Q e F1 F2} : @invert_expr.invert_cons_cps _ _ _ _ _ _ (base.type.list t) P Q e F1 F2 = option_map (fun '(a, b) => (F1 _ a, F2 _ b)) (invert_expr.invert_cons (var:=var) e).
admit.
Defined.

        Lemma invert_pair_Some {A B} {e : expr (A * B)} {v}
          : invert_expr.invert_pair e = Some v -> e = (fst v, snd v)%expr.
admit.
Defined.
        Lemma invert_Literal_Some {t} {e : expr t} {v}
          : invert_expr.invert_Literal e = Some v -> match t return expr t -> type.interp (base.interp base_interp) t -> Prop with
                                                     | type.base (base.type.type_base t) => fun e v => e = expr.Ident (ident.ident_Literal (t:=t) v)
                                                     | _ => fun _ _ => False
                                                     end e v.
admit.
Defined.
        Lemma invert_nil_Some {t} {e : expr (base.type.list t)}
          : invert_expr.invert_nil e = true -> e = []%expr.
admit.
Defined.
        Lemma invert_cons_Some {t} {e : expr (base.type.list t)} {v}
          : invert_expr.invert_cons e = Some v -> e = (fst v :: snd v)%expr.
admit.
Defined.
        Lemma invert_None_Some {t} {e : expr (base.type.option t)}
          : invert_expr.invert_None e = true -> e = (#ident.ident_None)%expr.
admit.
Defined.
        Lemma invert_Some_Some {t} {e : expr (base.type.option t)} {v}
          : invert_expr.invert_Some e = Some v -> e = (#ident.ident_Some @ v)%expr.
admit.
Defined.
        Lemma invert_tt_Some {e : expr base.type.unit}
          : invert_expr.invert_tt e = true -> e = (#ident.ident_tt)%expr.
admit.
Defined.

        Lemma invert_pair_ident_pair {A B} {v1 v2}
          : invert_expr.invert_pair (var:=var) (A:=A) (B:=B) (v1, v2) = Some (v1, v2).
admit.
Defined.
        Lemma invert_Literal_ident_Literal {t} {v}
          : invert_expr.invert_Literal (var:=var) (#(ident.ident_Literal (t:=t) v)) = Some v.
admit.
Defined.
        Lemma invert_nil_ident_nil {t}
          : invert_expr.invert_nil (var:=var) (#(ident.ident_nil (t:=t))) = true.
admit.
Defined.
        Lemma invert_cons_ident_cons {t} {x xs}
          : invert_expr.invert_cons (var:=var) (t:=t) (x :: xs) = Some (x, xs).
admit.
Defined.
        Lemma invert_None_ident_None {t}
          : invert_expr.invert_None (var:=var) (#(ident.ident_None (t:=t))) = true.
admit.
Defined.
        Lemma invert_Some_ident_Some {t x}
          : invert_expr.invert_Some (var:=var) (#(ident.ident_Some (t:=t)) @ x) = Some x.
admit.
Defined.
        Lemma invert_tt_ident_tt
          : invert_expr.invert_tt (var:=var) (#(ident.ident_tt)) = true.
admit.
Defined.

        Lemma reify_option_None {t} : reify_option None = (#ident.ident_None)%expr :> expr (base.type.option t).
admit.
Defined.
        Lemma reify_option_Some {t} (x : expr (type.base t)) : reify_option (Some x) = (#ident.ident_Some @ x)%expr.
admit.
Defined.
        Lemma reflect_option_ident_None {t} : reflect_option (var:=var) (#(ident.ident_None (t:=t))) = Some None.
admit.
Defined.
        Lemma reflect_option_ident_Some {t e} : reflect_option (var:=var) (#(ident.ident_Some (t:=t)) @ e) = Some (Some e).
admit.
Defined.
        Lemma reflect_option_Some {t} {e : expr (base.type.option t)} {v} : invert_expr.reflect_option e = Some v -> e = reify_option v.
admit.
Defined.
        Lemma reflect_option_Some_None {t} {e : expr (base.type.option t)} : invert_expr.reflect_option e = Some None -> e = (#ident.ident_None)%expr.
admit.
Defined.

        Lemma reify_list_nil {t} : reify_list nil = ([])%expr :> expr (base.type.list t).
admit.
Defined.
        Lemma reify_list_cons {t} (x : expr (type.base t)) xs : reify_list (x :: xs) = (x :: reify_list xs)%expr.
admit.
Defined.
        Lemma reflect_list_Some {t} {e : expr (base.type.list t)} {v} : invert_expr.reflect_list e = Some v -> e = reify_list v.
admit.
Defined.
        Lemma reflect_list_Some_nil {t} {e : expr (base.type.list t)} : invert_expr.reflect_list e = Some nil -> e = (#ident.ident_nil)%expr.
admit.
Defined.
        Lemma reflect_smart_Literal_Some {t} {e : expr (type.base t)} {v}
          : reflect_smart_Literal (t:=t) e = Some v -> e = ident.smart_Literal (t:=t) v.
admit.
Defined.

        End with_var1.

      End with_container.

    Ltac invert_subst_step_helper guard_tac :=
      first [ invert_subst_simple_step_helper guard_tac
            | match goal with
              | [ H : invert_expr.invert_pair ?e = Some _ |- _ ] => guard_tac H; apply invert_pair_Some in H
              | [ H : context[invert_expr.invert_pair_cps ?e ?F1 ?F2] |- _ ] => guard_tac H; rewrite invert_pair_cps_id in H; cbv [option_map] in H
              | [ H : invert_expr.invert_Literal ?e = Some _ |- _ ] => guard_tac H; apply invert_Literal_Some in H
              | [ H : invert_expr.reflect_smart_Literal ?e = Some _ |- _ ] => guard_tac H; apply reflect_smart_Literal_Some in H
              | [ H : invert_expr.invert_nil ?e = true |- _ ] => guard_tac H; apply invert_nil_Some in H
              | [ H : invert_expr.invert_cons ?e = Some _ |- _ ] => guard_tac H; apply invert_cons_Some in H
              | [ H : context[invert_expr.invert_cons_cps ?e ?F1 ?F2] |- _ ] => guard_tac H; rewrite invert_cons_cps_id in H; cbv [option_map] in H
              | [ H : invert_expr.invert_tt ?e = true |- _ ] => guard_tac H; apply invert_tt_Some in H
              | [ H : invert_expr.reflect_list ?e = Some _ |- _ ]
                => guard_tac H; first [ apply reflect_list_Some_nil in H | apply reflect_list_Some in H ];
                   rewrite ?reify_list_cons, ?reify_list_nil in H
              | [ H : invert_expr.invert_None ?e = true |- _ ] => guard_tac H; apply invert_None_Some in H
              | [ H : invert_expr.invert_Some ?e = Some _ |- _ ] => guard_tac H; apply invert_Some_Some in H
              | [ H : invert_expr.reflect_option ?e = Some _ |- _ ]
                => guard_tac H; first [ apply reflect_option_Some_None in H | apply reflect_option_Some in H ];
                   rewrite ?reify_option_Some, ?reify_option_None in H
              | [ H : context[invert_expr.invert_pair (_, _)] |- _ ] => guard_tac H; rewrite invert_pair_ident_pair in H
              | [ H : context[invert_expr.invert_Literal (#(ident.ident_Literal (t:=?T) ?V))] |- _ ] => guard_tac H; rewrite (invert_Literal_ident_Literal (t:=T) (v:=V)) in H
              | [ H : context[invert_expr.invert_ident_Literal (ident.ident_Literal (t:=?T) ?V)] |- _ ] => guard_tac H; rewrite (expr.invert_ident_Literal_ident_Literal (t:=T) (v:=V)) in H
              | [ H : context[invert_expr.invert_nil [] ] |- _ ] => guard_tac H; rewrite invert_nil_ident_nil in H
              | [ H : context[invert_expr.invert_cons (_ :: _)] |- _ ] => guard_tac H; rewrite invert_cons_ident_cons in H
              | [ H : context[invert_expr.invert_None (#ident.ident_None)] |- _ ] => guard_tac H; rewrite invert_None_ident_None in H
              | [ H : context[invert_expr.invert_Some (#ident.ident_Some @ _)] |- _ ] => guard_tac H; rewrite invert_Some_ident_Some in H
              | [ H : context[invert_expr.invert_tt (#ident.ident_tt)] |- _ ] => guard_tac H; rewrite invert_tt_ident_tt in H
              | [ H : context[invert_expr.reflect_option (#ident.ident_None)] |- _ ] => guard_tac H; rewrite reflect_option_ident_None in H
              | [ H : context[invert_expr.reflect_option (#ident.ident_Some @ _)] |- _ ] => guard_tac H; rewrite reflect_option_ident_Some in H
              end ].
    Ltac invert_subst_step :=
      first [ progress cbv beta iota in *
            | invert_subst_step_helper ltac:(fun _ => idtac)
            | subst ].
    Ltac invert_subst := repeat invert_subst_step.
  End expr.
End Compilers.
    Module Export expr.
    Section with_ty.
      Context {base_type}
              {ident : type.type base_type -> Type}.
      Section with_var.
        Context {var1 var2 : type.type base_type -> Type}.
        Local Notation wfvP := (fun t => (var1 t * var2 t)%type).
        Local Notation wfvT := (list (sigT wfvP)).

        Local Notation expr1 := (@expr.expr base_type ident var1).
        Local Notation expr2 := (@expr.expr base_type ident var2).
        Inductive wf : wfvT -> forall {t}, expr1 t -> expr2 t -> Prop :=
        | WfIdent
          : forall G {t} (idc : ident t), wf G (expr.Ident idc) (expr.Ident idc)
        | WfVar
          : forall G {t} (v1 : var1 t) (v2 : var2 t), List.In (existT _ t (v1, v2)) G -> wf G (expr.Var v1) (expr.Var v2)
        | WfAbs
          : forall G {s d} (f1 : var1 s -> expr1 d) (f2 : var2 s -> expr2 d),
            (forall (v1 : var1 s) (v2 : var2 s), wf (existT _ s (v1, v2) :: G) (f1 v1) (f2 v2))
            -> wf G (expr.Abs f1) (expr.Abs f2)
        | WfApp
          : forall G {s d}
                   (f1 : expr1 (s -> d)) (f2 : expr2 (s -> d)) (wf_f : wf G f1 f2)
                   (x1 : expr1 s) (x2 : expr2 s) (wf_x : wf G x1 x2),
            wf G (expr.App f1 x1) (expr.App f2 x2)
        | WfLetIn
          : forall G {A B}
                   (x1 : expr1 A) (x2 : expr2 A) (wf_x : wf G x1 x2)
                   (f1 : var1 A -> expr1 B) (f2 : var2 A -> expr2 B),
            (forall (v1 : var1 A) (v2 : var2 A), wf (existT _ A (v1, v2) :: G) (f1 v1) (f2 v2))
            -> wf G (expr.LetIn x1 f1) (expr.LetIn x2 f2).

        Section inversion.
          Local Notation "x == y" := (existT wfvP _ (x, y)).

          Definition wf_code (G : wfvT) {t} (e1 : expr1 t) : forall (e2 : expr2 t), Prop
            := match e1 in expr.expr t return expr2 t -> Prop with
               | expr.Ident t idc1
                 => fun e2
                    => match invert_expr.invert_Ident e2 with
                       | Some idc2 => idc1 = idc2
                       | None => False
                       end
               | expr.Var t v1
                 => fun e2
                    => match invert_expr.invert_Var e2 with
                       | Some v2 => List.In (v1 == v2) G
                       | None => False
                       end
               | expr.Abs s d f1
                 => fun e2
                    => match invert_expr.invert_Abs e2 with
                       | Some f2 => forall v1 v2, wf (existT _ s (v1, v2) :: G) (f1 v1) (f2 v2)
                       | None => False
                       end
               | expr.App s1 d f1 x1
                 => fun e2
                    => match invert_expr.invert_App e2 with
                       | Some (existT s2 (f2, x2))
                         => { pf : s1 = s2
                            | wf G (rew [fun s => expr1 (s -> d)] pf in f1) f2 /\ wf G (rew [expr1] pf in x1) x2 }
                       | None => False
                       end
               | expr.LetIn s1 d x1 f1
                 => fun e2
                    => match invert_expr.invert_LetIn e2 with
                       | Some (existT s2 (x2, f2))
                         => { pf : s1 = s2
                            | wf G (rew [expr1] pf in x1) x2
                              /\ forall v1 v2, wf (existT _ s2 (rew [var1] pf in v1, v2) :: G) (f1 v1) (f2 v2) }
                       | None => False
                       end
               end.

          Definition wf_encode {G t e1 e2} (v : @wf G t e1 e2) : @wf_code G t e1 e2.
admit.
Defined.
        End inversion.
      End with_var.

      End with_ty.

    Ltac is_expr_constructor arg :=
      lazymatch arg with
      | expr.Ident _ => idtac
      | expr.Var _ => idtac
      | expr.App _ _ => idtac
      | expr.LetIn _ _ => idtac
      | expr.Abs _ => idtac
      end.

    Ltac inversion_wf_step_gen guard_tac :=
      let postprocess H :=
          (cbv [wf_code wf_code] in H;
           simpl in H;
           try match type of H with
               | True => clear H
               | False => exfalso; exact H
               end) in
      match goal with
      | [ H : wf _ ?x ?y |- _ ]
        => guard_tac x y;
          apply wf_encode in H; postprocess H
      | [ H : wf ?x ?y |- _ ]
        => guard_tac x y;
          apply wf_encode in H; postprocess H
      end.
    Ltac inversion_wf_step_constr :=
      inversion_wf_step_gen ltac:(fun x y => is_expr_constructor x; is_expr_constructor y).
    Ltac inversion_wf_step_var :=
      inversion_wf_step_gen ltac:(fun x y => first [ is_var x; is_var y; fail 1 | idtac ]).
    Ltac inversion_wf_step := first [ inversion_wf_step_constr | inversion_wf_step_var ].
    Ltac inversion_wf := repeat inversion_wf_step.

    Section wf_properties.
      Context {base_type}
              {ident : type.type base_type -> Type}.
      Local Notation wf := (@wf base_type ident).

      Lemma wf_Proper_list {var1 var2} G1 G2
            (HG1G2 : forall t v1 v2, List.In (existT _ t (v1, v2)) G1 -> List.In (existT _ t (v1, v2)) G2)
            t e1 e2
            (Hwf : @wf var1 var2 G1 t e1 e2)
        : @wf var1 var2 G2 t e1 e2.
admit.
Defined.
    End wf_properties.

    Ltac wf_safe_t_step :=
    first [ progress intros
          | progress subst
          | progress inversion_sigma
          | progress inversion_prod
          | progress destruct_head'_sig
          | progress destruct_head'_and
          | progress destruct_head' False
          | progress cbn [List.In eq_rect] in *
          | match goal with
            | [ |- expr.wf _ _ _ ] => constructor
            end
          | solve [ eauto using conj, eq_refl, or_introl, or_intror with nocore ]
          | progress destruct_head'_or
          | match goal with
            | [ |- context[List.In _ (_ ++ _)%list] ] => rewrite in_app_iff
            | [ H : context[List.In _ (_ ++ _)%list] |- _ ] => rewrite in_app_iff in H
            | [ H : context[expr.wf _ _ _] |- expr.wf _ _ _ ]
              => eapply H; clear H; eauto with nocore; solve [ repeat wf_safe_t_step ]
            end
          | match goal with
            | [ |- _ \/ _ ] => constructor; solve [ repeat wf_safe_t_step ]
            end ].
  Ltac wf_unsafe_t_step :=
    first [ solve [ eauto with nocore ]
          | match goal with
            | [ H : context[expr.wf _ _ _] |- expr.wf _ _ _ ]
              => eapply H; eauto with nocore; match goal with |- ?G => tryif has_evar G then fail else idtac end
            | [ |- expr.wf _ _ _ ]
              => eapply expr.wf_Proper_list; [ | solve [ eauto with nocore ] ]
            end ].
  Ltac wf_safe_t := repeat wf_safe_t_step.
  Ltac wf_t_step := first [ wf_safe_t_step | wf_unsafe_t_step ].
  Ltac wf_t := repeat wf_t_step.
  Import invert_expr.

  Module Export SubstVarLike.
    Section with_ident.
      Context {base_type : Type}.
      Local Notation type := (type.type base_type).
      Context {ident : type -> Type}.
      Local Notation expr := (@expr.expr base_type ident).
      Section with_var.
        Context {var : type -> Type}.
        Section with_ident_like.
          Context (ident_is_good : forall t, ident t -> bool).
          Fixpoint is_recursively_var_or_ident {t} (e : @expr var t) : bool
            := match e with
               | expr.Ident t idc => ident_is_good _ idc
               | expr.Var t v => true
               | expr.Abs s d f => false
               | expr.App s d f x
                 => andb (@is_recursively_var_or_ident _ f)
                         (@is_recursively_var_or_ident _ x)
               | expr.LetIn A B x f => false
               end.
        End with_ident_like.
      End with_var.
    End with_ident.

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

      Fixpoint splice {A B} (x : @UnderLets A) (e : A -> @UnderLets B) : @UnderLets B
        := match x with
           | Base v => e v
           | UnderLet A x f => UnderLet x (fun v => @splice _ _ (f v) e)
           end.

      Fixpoint to_expr {t} (x : @UnderLets (expr t)) : expr t
        := match x with
           | Base v => v
           | UnderLet A x f
             => expr.LetIn x (fun v => @to_expr _ (f v))
           end.
      Fixpoint of_expr {t} (x : expr t) : @UnderLets (expr t)
        := match x in expr.expr t return @UnderLets (expr t) with
           | expr.LetIn A B x f
             => UnderLet x (fun v => @of_expr B (f v))
           | e => Base e
           end.
    End with_var.
      Global Arguments UnderLets : clear implicits.
      Delimit Scope under_lets_scope with under_lets.
      Bind Scope under_lets_scope with UnderLets.UnderLets.
      Notation "x <-- y ; f" := (UnderLets.splice y (fun x => f%under_lets)) : under_lets_scope.

    Section reify.
      Context {base : Type}
              {base_interp : base -> Type}
              {try_make_transport_base_type_cps : @type.try_make_transport_cpsT base}.
      Local Notation base_type := (@base.type base).
      Local Notation type := (@type.type base_type).
      Context {ident : type -> Type}.
      Context {invertIdent : @InvertIdentT base base_interp ident}.
      Context {buildIdent : @ident.BuildIdentT base base_interp ident}.
      Context (ident_is_var_like : forall t, ident t -> bool).
      Let base' {bt} (x : Compilers.base.type bt) : type.type _ := type.base x.
      Local Coercion base' : base.type >-> type.type.
      Section with_var.
        Context {var : type -> Type}.
        Local Notation UnderLets := (@UnderLets.UnderLets base_type ident var).
        Local Notation is_var_like := (@SubstVarLike.is_recursively_var_or_ident base_type ident var (@ident_is_var_like)).

        Let default_reify_and_let_binds_base_cps {t : base_type} : expr t -> forall T, (expr t -> UnderLets T) -> UnderLets T
          := fun e T k
             => match invert_expr.invert_Var e with
                | Some v => k ($v)%expr
                | None => if is_var_like e
                          then k e
                          else UnderLets.UnderLet e (fun v => k ($v)%expr)
                end.

        Fixpoint reify_and_let_binds_base_cps {t : base_type} : expr t -> forall T, (expr t -> UnderLets T) -> UnderLets T
          := match t return expr t -> forall T, (expr t -> UnderLets T) -> UnderLets T with
             | base.type.type_base t
               => fun e T k
                  => match invert_Literal e with
                     | Some v => k (expr.Ident (@ident.ident_Literal _ _ _ buildIdent _ v))
                     | None => @default_reify_and_let_binds_base_cps _ e T k
                     end
             | base.type.prod A B
               => fun e T k
                  => match invert_pair e with
                     | Some (a, b)
                       => @reify_and_let_binds_base_cps
                            A a _
                            (fun ae
                             => @reify_and_let_binds_base_cps
                                  B b _
                                  (fun be
                                   => k (ae, be)%expr))
                     | None => @default_reify_and_let_binds_base_cps _ e T k
                     end
             | base.type.list A
               => fun e T k
                  => match reflect_list e with
                     | Some ls
                       => list_rect
                            _
                            (fun k => k []%expr)
                            (fun x _ rec k
                             => @reify_and_let_binds_base_cps
                                  A x _
                                  (fun xe
                                   => rec (fun xse => k (xe :: xse)%expr)))
                            ls
                            k
                     | None => @default_reify_and_let_binds_base_cps _ e T k
                     end
             | base.type.option A
               => fun e T k
                  => match reflect_option e with
                     | Some ls
                       => option_rect
                            _
                            (fun x k
                             => @reify_and_let_binds_base_cps
                                  A x _
                                  (fun xe
                                   => k (#ident.ident_Some @ xe)%expr))
                            (fun k => k (#ident.ident_None)%expr)
                            ls
                            k
                     | None => @default_reify_and_let_binds_base_cps _ e T k
                     end
             | base.type.unit
               => fun e T k
                  => if is_var_like e
                     then k (#ident.ident_tt)%expr
                     else UnderLets.UnderLet e (fun v => k (#ident.ident_tt)%expr)
             end%under_lets.

        Fixpoint let_bind_return {t} : expr t -> expr t
          := match t return expr t -> expr t with
             | type.base t
               => fun e => to_expr (v <-- of_expr e; reify_and_let_binds_base_cps v _ Base)
             | type.arrow s d
               => fun e
                  => expr.Abs (fun v => @let_bind_return
                                          d
                                          match invert_Abs e with
                                          | Some f => f v
                                          | None => e @ $v
                                          end%expr)
             end.
      End with_var.
    End reify.

Import Coq.Classes.Morphisms.

    Section reify.
      Context {base : Type}.
      Local Notation base_type := (@base.type base).
      Local Notation type := (@type.type base_type).
      Context {ident : type -> Type}
              {base_interp : base -> Type}
              {base_beq : base -> base -> bool}
              {reflect_base_beq : Reflect.reflect_rel (@eq base) base_beq}
              {try_make_transport_base_type_cps : @type.try_make_transport_cpsT base}
              {invertIdent : @InvertIdentT base base_interp ident}
              {buildIdent : @ident.BuildIdentT base base_interp ident}
              {buildInvertIdentCorrect : BuildInvertIdentCorrectT}
              {try_make_transport_base_cps_correct : type.try_make_transport_cps_correctT base}.
      Context (ident_is_var_like : forall t, ident t -> bool).
        Context {ident_interp : forall t, ident t -> type.interp (base.interp base_interp) t}
                {ident_interp_Proper : forall t : type, Proper (eq ==> type.eqv) (ident_interp t)}.
        Local Notation interp := (expr.interp (@ident_interp)).

        Lemma interp_let_bind_return {t} (e1 e2 : expr t)
              G
              (HG : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> v1 == v2)
              (Hwf : expr.wf G e1 e2)
          : interp (let_bind_return ident_is_var_like e1) == interp e2.
        Proof using buildInvertIdentCorrect ident_interp_Proper try_make_transport_base_cps_correct.
          revert dependent G; induction t; intros; cbn [let_bind_return type.eqv expr.interp] in *; cbv [invert_Abs respectful] in *;
            repeat first [ progress wf_safe_t
                         | progress expr.invert_subst
                         | progress expr.invert_match
                         | progress expr.inversion_wf
                         | progress break_innermost_match_hyps
                         | progress destruct_head'_False
                         | solve [ wf_t ]
                         | match goal with
                           | [ H : _ |- expr.interp _ (let_bind_return _ ?e0) == expr.interp _ ?e ?v ]
                             => eapply (H e0 (e @ $v)%expr (cons _ _)); [ .. | solve [ wf_t ] ]; solve [ wf_t ]
                           | [ H : _ |- expr.interp _ (let_bind_return _ ?e0) == expr.interp _ ?e ?v ]
                             => cbn [expr.interp]; eapply H; [ | solve [ wf_t ] ]; solve [ wf_t ]
                           end ];
            [].
