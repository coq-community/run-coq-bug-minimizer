(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "+implicit-core-hint-db,+implicits-in-term,+non-reversible-notation,+deprecated-intros-until-0,+deprecated-focus,+unused-intro-pattern,+deprecated-hint-constr,+fragile-hint-constr,+variable-collision,+unexpected-implicit-declaration,+omega-is-deprecated,+non-recursive" "-w" "-notation-overridden,-undeclared-scope,-deprecated-hint-rewrite-without-locality" "-w" "-notation-overridden,-undeclared-scope" "-w" "-deprecated-native-compiler-option" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/rewriter/src/Rewriter" "Rewriter" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-I" "/github/workspace/builds/coq/coq-failing/_build_ci/rewriter/src/Rewriter/Util/plugins" "-top" "bug_01" "-native-compiler" "ondemand") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 1265 lines to 130 lines, then from 143 lines to 1834 lines, then from 1838 lines to 326 lines, then from 339 lines to 1377 lines, then from 1381 lines to 624 lines, then from 637 lines to 882 lines, then from 887 lines to 625 lines, then from 638 lines to 980 lines, then from 985 lines to 637 lines, then from 650 lines to 2764 lines, then from 2768 lines to 931 lines, then from 940 lines to 772 lines, then from 785 lines to 1336 lines, then from 1340 lines to 774 lines, then from 787 lines to 1237 lines, then from 1241 lines to 767 lines, then from 780 lines to 846 lines, then from 851 lines to 768 lines, then from 781 lines to 994 lines, then from 999 lines to 770 lines *)
(* coqc version 8.15+alpha compiled with OCaml 4.13.0
   coqtop version runner-z3wu8uu--project-6138686-concurrent-0:/builds/coq/coq/_build/default,(HEAD detached at 0d1a2eb) (0d1a2eb7ba6a7719f37495807fb9fa49623ac075)
   Expected coqc runtime on this file: 4.400 sec *)
Require Coq.FSets.FMapPositive.
Require Rewriter.Util.GlobalSettings.
Require Coq.MSets.MSetPositive.
Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.
Reserved Infix "@" (left associativity, at level 11).
Reserved Notation "A <- X ; B" (at level 70, X at next level, right associativity, format "'[v' A  <-  X ; '/' B ']'").
Reserved Notation "~> R" (at level 70).

Notation "~> R" := (forall T (_:R->T), T) : type_scope.
Definition bind {A B} (v : option A) (f : A -> option B) : option B.
Admitted.
  Delimit Scope option_scope with option.
  Notation "A <- X ; B" := (bind X (fun A => B%option)) : option_scope.

Import Coq.Bool.Bool.

Notation reflect_rel P b := (forall x y, reflect (P x y) (b x y)).
Module Export Language.
Import Coq.ZArith.ZArith.
Module Export Compilers.
  Module type.
    Inductive type {base_type : Type} := base (t : base_type) | arrow (s d : type).
    Global Arguments type : clear implicits.
Fixpoint final_codomain {base_type} (t : type base_type) : base_type.
exact (match t with
         | base t
           => t
         | arrow s d => @final_codomain base_type d
         end).
Defined.
Fixpoint interp {base_type} (base_interp : base_type -> Type) (t : type base_type) : Type.
exact (match t with
         | base t => base_interp t
         | arrow s d => @interp _ base_interp s -> @interp _ base_interp d
         end).
Defined.

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
Fixpoint smart_Literal {t:base_type} : base_type_interp t -> expr (type.base t).
Admitted.

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
    : type_of_list (List.map P1 ls) -> type_of_list (List.map P2 ls).
Admitted.

  Module pattern.
    Notation EvarMap_at base := (PositiveMap.t (Compilers.base.type base)).
    Notation EvarMap := (EvarMap_at _).
    Export Language.Compilers.pattern.
    Module base.
      Export Language.Compilers.pattern.base.

      Section with_base.
        Context {base : Type}.

        Local Notation type := (type base).

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
      End with_base.
    End base.

    Module Export type.
      Section with_base.
        Context {base : Type}.

        Local Notation type := (type base).
Fixpoint relax (t : type.type (Compilers.base.type base)) : type.
Admitted.

        Fixpoint subst_default (ptype : type) (evar_map : EvarMap) : type.type (Compilers.base.type base)
          := match ptype with
             | type.base t => type.base (base.subst_default t evar_map)
             | type.arrow A B => type.arrow (subst_default A evar_map) (subst_default B evar_map)
             end.
Fixpoint collect_vars (t : type) : PositiveSet.t.
Admitted.
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
Definition prefull_types : ident -> Type.
exact (fun idc => ident_args (ident_infos_of idc)).
Defined.
Definition full_types : ident -> Type.
exact (proj1_sig (@eta_ident_cps_gen _ prefull_types)).
Defined.
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
Definition relax_kind_of_type {T} : Raw.ident.Type_of_kind_of_type base T -> Type_of_kind_of_type T.
admit.
Defined.
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
Definition prearg_types : forall {t} (idc : ident t), list Type.
exact ((fun {t} idc
                => let st := @split_types t idc in
                   let pi := preinfos (raw_ident_infos_of (projT1 st)) in
                   indep_args pi (Datatypes.fst (projT2 st)))).
Defined.
Definition arg_types : forall {t} (idc : ident t), list Type.
exact (proj1_sig (@eta_ident_cps_gen _ (@prearg_types))).
Defined.
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
          : forall_vars p k1 -> forall_vars p k2.
admit.
Defined.
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
    End Notations.

    Record > anypattern {base} {ident : type base -> Type}
      := { type_of_anypattern : type base;
           pattern_of_anypattern :> @pattern base ident type_of_anypattern }.

    Fixpoint collect_vars {base ident}
             {t} (p : @pattern base ident t) : PositiveSet.t.
exact (match p with
         | Wildcard t => type.collect_vars t
         | Ident t idc => type.collect_vars t
         | App s d f x => PositiveSet.union (@collect_vars _ _ _ x) (@collect_vars _ _ _ f)
         end).
Defined.
  End pattern.
  Export pattern.Notations.
      Section with_var0.
        Context {base_type} {ident var : type.type base_type -> Type}.
        Local Notation type := (type.type base_type).
        Local Notation expr := (@expr.expr base_type ident var).
        Local Notation UnderLets := (@UnderLets.UnderLets base_type ident var).
Let type_base (t : base_type) : type.
Admitted.
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
          : type_of_list_cps A1 ls -> type_of_list_cps A2 ls.
admit.
Defined.

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
Let type_base' (t : base) : base_type.
exact (base.type.type_base t).
Defined.
Let ptype_base' (t : base) : pbase_type.
exact (pattern.base.type.type_base t).
Defined.
Let type_base'' (t : base) : type.
exact (type.base (base.type.type_base t)).
Defined.
Let ptype_base'' (t : base) : ptype.
exact (type.base (pattern.base.type.type_base t)).
Defined.
          Coercion ptype_base'' : base >-> ptype.
          Coercion ptype_base : pbase_type >-> ptype.
          Local Notation collect_vars := (@pattern.collect_vars base pattern_ident).
          Local Notation with_unification_resultT' := (@with_unification_resultT' base pattern_ident (@arg_types) value).
          Local Notation with_unification_resultT := (@with_unification_resultT base pattern_ident (@arg_types) value).
          Local Notation under_with_unification_resultT := (@under_with_unification_resultT base pattern_ident (@arg_types) value).
          Local Notation rewrite_ruleTP := (@rewrite_ruleTP base ident var pattern_ident (@arg_types)).
          Local Notation rewrite_rule_data := (@rewrite_rule_data base ident var pattern_ident (@arg_types)).
Definition make_base_Literal_pattern_folded (t : base) : pattern t.
Admitted.

          Context (pident_pair : forall A B : pbase_type, pattern_ident (A -> B -> A * B)%ptype).
Fixpoint make_Literal_pattern (t : pbase_type) : option (pattern t).
Admitted.
Fixpoint make_interp_rewrite_pattern {t}
            : pattern t -> option (pattern (type.final_codomain t)).
exact (match t return pattern t -> option (pattern (type.final_codomain t)) with
               | type.base t
                 => fun p => Some p
               | type.arrow (type.base s) d
                 => fun p => (x <- make_Literal_pattern s; @make_interp_rewrite_pattern d (pattern.App p x))%option
               | type.arrow _ _ => fun _ => None
               end).
Defined.

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
Admitted.

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
