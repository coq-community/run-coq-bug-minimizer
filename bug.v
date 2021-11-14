(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "-notation-overridden" "-w" "-deprecated-native-compiler-option" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/fiat_crypto_legacy/src" "Crypto" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/fiat_crypto_legacy/bbv/src/bbv" "bbv" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/fiat_crypto_legacy/coqprime/src/Coqprime" "Coqprime" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-I" "/github/workspace/builds/coq/coq-failing/_build_ci/fiat_crypto_legacy/coqprime/src" "-top" "bug_01" "-native-compiler" "no") -*- *)
(* File reduced by coq-bug-finder from original input, then from 297 lines to 70 lines, then from 82 lines to 315 lines, then from 320 lines to 240 lines, then from 252 lines to 335 lines, then from 340 lines to 255 lines, then from 267 lines to 291 lines, then from 296 lines to 256 lines, then from 268 lines to 283 lines, then from 288 lines to 255 lines, then from 267 lines to 509 lines, then from 514 lines to 262 lines, then from 274 lines to 438 lines, then from 443 lines to 268 lines, then from 280 lines to 450 lines, then from 455 lines to 315 lines, then from 327 lines to 566 lines, then from 571 lines to 451 lines, then from 463 lines to 566 lines, then from 571 lines to 479 lines, then from 491 lines to 611 lines, then from 616 lines to 489 lines, then from 501 lines to 633 lines, then from 638 lines to 518 lines, then from 530 lines to 701 lines, then from 706 lines to 602 lines, then from 614 lines to 776 lines, then from 781 lines to 677 lines, then from 689 lines to 814 lines, then from 819 lines to 717 lines, then from 729 lines to 810 lines, then from 815 lines to 753 lines, then from 765 lines to 871 lines, then from 876 lines to 765 lines, then from 777 lines to 892 lines, then from 897 lines to 813 lines, then from 825 lines to 949 lines, then from 954 lines to 854 lines, then from 866 lines to 942 lines, then from 947 lines to 859 lines, then from 871 lines to 1007 lines, then from 1012 lines to 900 lines, then from 912 lines to 899 lines, then from 911 lines to 992 lines, then from 997 lines to 956 lines, then from 968 lines to 1320 lines, then from 1324 lines to 967 lines, then from 979 lines to 1223 lines, then from 1228 lines to 985 lines, then from 997 lines to 1143 lines, then from 1148 lines to 1001 lines, then from 1013 lines to 1162 lines, then from 1167 lines to 1019 lines, then from 1031 lines to 1165 lines, then from 1170 lines to 1028 lines, then from 1040 lines to 1482 lines, then from 1486 lines to 1038 lines, then from 1050 lines to 1256 lines, then from 1260 lines to 1058 lines, then from 1070 lines to 1367 lines, then from 1371 lines to 1075 lines, then from 1087 lines to 1250 lines, then from 1255 lines to 1150 lines, then from 1162 lines to 1546 lines, then from 1551 lines to 1161 lines, then from 1173 lines to 1909 lines, then from 1914 lines to 1772 lines, then from 1784 lines to 1772 lines, then from 1784 lines to 2124 lines, then from 2129 lines to 1782 lines, then from 1794 lines to 1981 lines, then from 1986 lines to 1883 lines, then from 1895 lines to 2026 lines, then from 2031 lines to 1897 lines, then from 1909 lines to 1884 lines, then from 1896 lines to 2024 lines, then from 2029 lines to 1919 lines, then from 1931 lines to 1958 lines, then from 1963 lines to 1915 lines, then from 1927 lines to 2088 lines, then from 2093 lines to 2025 lines, then from 2036 lines to 1966 lines, then from 1978 lines to 2022 lines, then from 2027 lines to 1967 lines, then from 1979 lines to 2039 lines, then from 2045 lines to 2001 lines, then from 2014 lines to 2216 lines, then from 2221 lines to 2062 lines, then from 2074 lines to 2048 lines, then from 2060 lines to 2215 lines, then from 2221 lines to 2127 lines, then from 2140 lines to 2532 lines, then from 2538 lines to 2156 lines, then from 2168 lines to 2141 lines, then from 2153 lines to 2243 lines, then from 2249 lines to 2198 lines, then from 2211 lines to 2331 lines, then from 2337 lines to 2211 lines, then from 2224 lines to 2379 lines, then from 2385 lines to 2397 lines *)
(* coqc version 8.15+alpha compiled with OCaml 4.13.0
   coqtop version runner-ed2dce3a-project-6138686-concurrent-0:/builds/coq/coq/_build/default,(HEAD detached at dd7710d) (dd7710ddc27f4261696e0fa0a64ae693bcf5fc90)
   Modules that could not be inlined: bbv.Word
   Expected coqc runtime on this file: 6.385 sec *)
Require Coq.Classes.Morphisms.
Require Crypto.Util.GlobalSettings.
Require Crypto.Util.FixCoqMistakes.
Require Coq.Relations.Relation_Definitions.
Require Crypto.Util.Tactics.GetGoal.
Require Crypto.Util.Notations.
Require Crypto.Util.LetIn.
Require Crypto.Compilers.Syntax.
Require Coq.Lists.List.
Require Coq.micromega.Lia.
Require Crypto.Util.Tactics.Head.
Require Crypto.Util.Tactics.BreakMatch.
Require Crypto.Util.Tactics.DestructHyps.
Require Crypto.Util.Tactics.DestructHead.
Require Crypto.Util.Option.
Require Coq.Classes.RelationClasses.
Require Crypto.Util.IffT.
Require Crypto.Util.Isomorphism.
Require Crypto.Util.HProp.
Require Crypto.Util.Equality.
Require Crypto.Util.Prod.
Require Crypto.Util.Tactics.SpecializeBy.
Require Coq.Logic.Eqdep_dec.
Require Crypto.Util.Sigma.
Require Coq.ZArith.BinInt.
Require Coq.ZArith.ZArith_dec.
Require Coq.NArith.BinNat.
Require Crypto.Util.Decidable.
Require Coq.Arith.Arith.
Require Coq.ZArith.ZArith.
Require Coq.Arith.Peano_dec.
Require Coq.Numbers.Natural.Peano.NPeano.
Require Coq.NArith.NArith.
Require Crypto.Util.NatUtil.
Require Coq.Numbers.BinNums.
Require Crypto.Util.Pointed.
Require Crypto.Util.Tactics.Test.
Require Crypto.Util.Tactics.Not.
Require Crypto.Util.Tactics.DoWithHyp.
Require Crypto.Util.Tactics.RewriteHyp.
Require Coq.Lists.SetoidList.
Require Crypto.Util.ListUtil.
Require Crypto.Util.Tuple.
Require Crypto.Compilers.Tuple.
Require Crypto.Compilers.SmartMap.
Require Crypto.Compilers.Named.Context.
Require Coq.Setoids.Setoid.
Require Crypto.Util.PointedProp.
Require Coq.Arith.Div2.
Require Coq.Bool.Bool.
Require Coq.Logic.EqdepFacts.
Require Coq.Program.Tactics.
Require Coq.Program.Equality.
Require Coq.setoid_ring.Ring.
Require Coq.setoid_ring.Ring_polynom.
Require bbv.Nomega.
Require bbv.ZLib.
Require bbv.N_Z_nat_conversions.
Require bbv.NatLib.
Require bbv.NLib.
Require Coq.Logic.Eqdep.
Require bbv.DepEq.
Require bbv.DepEqNat.
Require bbv.ReservedNotations.
Require bbv.Word.
Require Coq.FSets.FMapPositive.

Declare ML Module "ltac_plugin".
Module Export AdmitTactic.
Module Import LocalFalse.
Inductive False : Prop := .
End LocalFalse.
Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.
End AdmitTactic.

Module Export Crypto_DOT_Compilers_DOT_Named_DOT_Syntax_WRAPPED.
Module Export Syntax.
 
Import Crypto.Compilers.Syntax.
Import Crypto.Compilers.Named.Context.
Import Crypto.Util.PointedProp.
Import Crypto.Util.Notations.
Import Crypto.Util.LetIn.

Local Open Scope ctype_scope.
Local Open Scope expr_scope.
Delimit Scope nexpr_scope with nexpr.
Module Export Named.
  Section language.
    Context (base_type_code : Type)
            (interp_base_type : base_type_code -> Type)
            (op : flat_type base_type_code -> flat_type base_type_code -> Type)
            (Name : Type).

    Local Notation flat_type := (flat_type base_type_code).
    Local Notation type := (type base_type_code).
    Local Notation interp_type := (interp_type interp_base_type).
    Local Notation interp_flat_type_gen := interp_flat_type.
    Local Notation interp_flat_type := (interp_flat_type interp_base_type).

    Inductive exprf : flat_type -> Type :=
    | TT : exprf Unit
    | Var {t : base_type_code} : Name -> exprf (Tbase t)
    | Op {t1 tR} : op t1 tR -> exprf t1 -> exprf tR
    | LetIn : forall {tx}, interp_flat_type_gen (fun _ => Name) tx -> exprf tx -> forall {tC}, exprf tC -> exprf tC
    | Pair : forall {t1}, exprf t1 -> forall {t2}, exprf t2 -> exprf (Prod t1 t2).
    Bind Scope nexpr_scope with exprf.
    Inductive expr : type -> Type :=
    | Abs {src dst} : interp_flat_type_gen (fun _ => Name) src -> exprf dst -> expr (Arrow src dst).
    Bind Scope nexpr_scope with expr.
    Definition Abs_name {t} (e : expr t) : interp_flat_type_gen (fun _ => Name) (domain t)
      := match e with Abs _ _ n f => n end.
    Definition invert_Abs {t} (e : expr t) : exprf (codomain t)
      := match e with Abs _ _ n f => f end.

    Section with_val_context.
      Context (Context : Context Name interp_base_type)
              (interp_op : forall src dst, op src dst -> interp_flat_type src -> interp_flat_type dst).

      Fixpoint interpf
               {t} (ctx : Context) (e : exprf t)
        : option (interp_flat_type t)
        := match e in exprf t return option (interp_flat_type t) with
           | Var t' x => lookupb t' ctx x
           | TT => Some tt
           | Pair _ ex _ ey
             => match @interpf _ ctx ex, @interpf _ ctx ey with
                | Some xv, Some yv => Some (xv, yv)%core
                | None, _ | _, None => None
                end
           | Op _ _ opc args
             => option_map (@interp_op _ _ opc) (@interpf _ ctx args)
           | LetIn _ n ex _ eC
             => match @interpf _ ctx ex with
                | Some xv
                  => dlet x := xv in
                     @interpf _ (extend ctx n x) eC
                | None => None
                end
           end.

      Definition interp {t} (ctx : Context) (e : expr t)
        : interp_flat_type (domain t) -> option (interp_flat_type (codomain t))
        := fun v => @interpf _ (extend ctx (Abs_name e) v) (invert_Abs e).

      Definition Interp {t} (e : expr t)
        : interp_flat_type (domain t) -> option (interp_flat_type (codomain t))
        := interp empty e.
    End with_val_context.
  End language.
End Named.

Global Arguments TT {_ _ _}.
Global Arguments Var {_ _ _ _} _.
Global Arguments Op {_ _ _ _ _} _ _.
Global Arguments LetIn {_ _ _} _ _ _ {_} _.
Global Arguments Pair {_ _ _ _} _ {_} _.
Global Arguments Abs {_ _ _ _ _} _ _.
Global Arguments invert_Abs {_ _ _ _} _.
Global Arguments Abs_name {_ _ _ _} _.
Global Arguments interpf {_ _ _ _ _ interp_op t ctx} _.
Global Arguments interp {_ _ _ _ _ interp_op t ctx} _ _.
Global Arguments Interp {_ _ _ _ _ interp_op t} _ _.

Notation "'nlet' x := A 'in' b" := (LetIn _ x A%nexpr b%nexpr) : nexpr_scope.
Notation "'nlet' x : tx := A 'in' b" := (LetIn tx%ctype x%core A%nexpr b%nexpr) : nexpr_scope.
Notation "'λn'  x .. y , t" := (Abs x .. (Abs y t%nexpr) .. ) : nexpr_scope.
Notation "( x , y , .. , z )" := (Pair .. (Pair x%nexpr y%nexpr) .. z%nexpr) : nexpr_scope.
Notation "()" := TT : nexpr_scope.

End Syntax.

End Crypto_DOT_Compilers_DOT_Named_DOT_Syntax_WRAPPED.
Module Export Crypto_DOT_Compilers_DOT_Named_DOT_Syntax.
Module Export Crypto.
Module Export Compilers.
Module Export Named.
Module Export Syntax.
Include Crypto_DOT_Compilers_DOT_Named_DOT_Syntax_WRAPPED.Syntax.
End Syntax.

End Named.

End Compilers.

End Crypto.

End Crypto_DOT_Compilers_DOT_Named_DOT_Syntax.
Import Crypto.Compilers.SmartMap.
Import Crypto.Compilers.Syntax.
Import Crypto.Compilers.Named.Context.
Import Crypto.Compilers.Named.Syntax.
Import Crypto.Util.PointedProp.
  Section language.
    Context {base_type_code Name : Type}
            {op : flat_type base_type_code -> flat_type base_type_code -> Type}.
    Section with_var.
      Context {var}
              (Context : @Context base_type_code Name var).

      Section gen.
        Context (quantify : forall tx, (interp_flat_type var tx -> option pointed_Prop) -> option pointed_Prop).

        Fixpoint wff_gen (ctx : Context) {t} (e : @exprf base_type_code op Name t) : option pointed_Prop
          := match e with
             | TT => Some trivial
             | Var t n => match lookupb t ctx n return bool with
                          | Some _ => true
                          | None => false
                          end
             | Op _ _ op args => @wff_gen ctx _ args
             | LetIn _ n ex _ eC => @wff_gen ctx _ ex
                                    /\ quantify _ (fun v => @wff_gen (extend ctx n v) _ eC)
             | Pair _ ex _ ey => @wff_gen ctx _ ex /\ @wff_gen ctx _ ey
             end%option_pointed_prop.
      End gen.
    End with_var.

    Section unit.
      Context (Context : @Context base_type_code Name (fun _ => unit)).

      Local Notation TT := (SmartValf _ (fun _ => tt) _).
      Definition wff_unit := wff_gen Context (fun tx f => f TT).
      Definition wf_unit ctx {t} (e : @expr base_type_code op Name t) : option pointed_Prop
        := @wff_unit (extend ctx (Abs_name e) TT) _ (invert_Abs e).
    End unit.
  End language.
Global Arguments wf_unit {_ _ _ _} ctx {t} _.
Import Crypto.Compilers.Syntax.
Import Crypto.Util.Notations.

Ltac solve_wf_side_condition := solve [ eassumption | eauto 250 with wf ].

Section language.
  Context {base_type_code : Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}.
  Local Notation exprf := (@exprf base_type_code op).
  Local Notation expr := (@expr base_type_code op).
  Local Notation Expr := (@Expr base_type_code op).

  Section with_var.
    Context {var1 var2 : base_type_code -> Type}.
    Local Notation eP := (fun t => var1 t * var2 t)%type (only parsing).
    Local Notation "x == y" := (existT eP _ (x, y)%core).
    Fixpoint flatten_binding_list {t} (x : interp_flat_type var1 t) (y : interp_flat_type var2 t) : list (sigT eP)
      := (match t return interp_flat_type var1 t -> interp_flat_type var2 t -> list _ with
          | Tbase _ => fun x y => (x == y) :: nil
          | Unit => fun x y => nil
          | Prod t0 t1 => fun x y => @flatten_binding_list _ (snd x) (snd y) ++ @flatten_binding_list _ (fst x) (fst y)
          end x y)%list.

    Inductive wff : list (sigT eP) -> forall {t}, @exprf var1 t -> @exprf var2 t -> Prop :=
    | WfTT : forall G, @wff G _ TT TT
    | WfVar : forall G (t : base_type_code) x x', List.In (x == x') G -> @wff G (Tbase t) (Var x) (Var x')
    | WfOp : forall G {t} {tR} (e : @exprf var1 t) (e' : @exprf var2 t) op,
        wff G e e'
        -> wff G (Op (tR := tR) op e) (Op (tR := tR) op e')
    | WfLetIn : forall G t1 t2 e1 e1' (e2 : interp_flat_type var1 t1 -> @exprf var1 t2) e2',
        wff G e1 e1'
        -> (forall x1 x2, wff (flatten_binding_list x1 x2 ++ G) (e2 x1) (e2' x2))
        -> wff G (LetIn e1 e2) (LetIn e1' e2')
    | WfPair : forall G {t1} {t2} (e1: @exprf var1 t1) (e2: @exprf var1 t2)
                      (e1': @exprf var2 t1) (e2': @exprf var2 t2),
        wff G e1 e1'
        -> wff G e2 e2'
        -> wff G (Pair e1 e2) (Pair e1' e2').
    Inductive wf : forall {t}, @expr var1 t -> @expr var2 t -> Prop :=
    | WfAbs : forall A B e e',
        (forall x x', @wff (flatten_binding_list x x') B (e x) (e' x'))
        -> @wf (Arrow A B) (Abs e) (Abs e').
  End with_var.

  Definition Wf {t} (E : @Expr t) := forall var1 var2, wf (E var1) (E var2).
End language.
Section language.
  Context {base_type_code : Type}
          {interp_base_type : base_type_code -> Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}.

  Local Notation flat_type := (flat_type base_type_code).

  Section with_var.
    Context {var : base_type_code -> Type}.

    Local Notation exprf := (@exprf base_type_code op var).
    Definition invert_Op {t} (e : exprf t) : option { t1 : flat_type & op t1 t * exprf t1 }%type
      := match e with Op _ _ opc args => Some (existT _ _ (opc, args)) | _ => None end.

    End with_var.
End language.
Section language.
  Context (let_bind_op_args : bool)
          {base_type_code : Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}.
  Local Notation Expr := (@Expr base_type_code op).

  Section with_var.
    Context {var : base_type_code -> Type}.
    Local Notation exprf := (@exprf base_type_code op var).
    Local Notation expr := (@expr base_type_code op var).

    Section under_lets.
      Fixpoint under_letsf' (bind_pairs : bool) {t} (e : exprf t)
        : forall {tC} (C : interp_flat_type var t + exprf t -> exprf tC), exprf tC
        := match e in Syntax.exprf _ _ t return forall {tC} (C : interp_flat_type var t + exprf t -> exprf tC), exprf tC with
           | LetIn _ ex _ eC
             => fun _ C => @under_letsf' true _ ex _ (fun v =>
                           match v with
                           | inl v => @under_letsf' false _ (eC v) _ C
                           | inr v => LetIn v (fun v => @under_letsf' false _ (eC v) _ C)
                           end)
           | TT => fun _ C => C (inl tt)
           | Var _ x => fun _ C => C (inl x)
           | Op _ _ op args as e
             => if let_bind_op_args
                then fun _ C => LetIn e (fun v => C (inl v))
                else fun _ C => C (inr e)
           | Pair A x B y => fun _ C => @under_letsf' bind_pairs A x _ (fun x =>
                                        @under_letsf' bind_pairs B y _ (fun y =>
                                        match x, y, bind_pairs with
                                        | inl x, inl y, _ => C (inl (x, y))
                                        | inl x, inr y, false => C (inr (Pair (SmartVarf x) y))
                                        | inr x, inl y, false => C (inr (Pair x (SmartVarf y)))
                                        | inr x, inr y, false => C (inr (Pair x y))
                                        | inl x, inr y, true => LetIn y (fun y => C (inl (x, y)))
                                        | inr x, inl y, true => LetIn x (fun x => C (inl (x, y)))
                                        | inr x, inr y, true => LetIn x (fun x => LetIn y (fun y => C (inl (x, y))))
                                        end))
           end.
      Definition under_letsf {t} (e : exprf t)
                 {tC} (C : exprf t -> exprf tC)
        : exprf tC
        := under_letsf' false e (fun v => match v with inl v => C (SmartVarf v) | inr v => C v end).
    End under_lets.

    Fixpoint linearizef_gen {t} (e : exprf t) : exprf t
      := match e in Syntax.exprf _ _ t return exprf t with
         | LetIn _ ex _ eC
           => under_letsf (LetIn (@linearizef_gen _ ex) (fun x => @linearizef_gen _ (eC x))) (fun x => x)
         | TT => TT
         | Var _ x => Var x
         | Op _ _ op args
           => if let_bind_op_args
              then under_letsf (@linearizef_gen _ args) (fun args => LetIn (Op op args) SmartVarf)
              else under_letsf (@linearizef_gen _ args) (fun args => Op op args)
         | Pair A ex B ey
           => under_letsf (Pair (@linearizef_gen _ ex) (@linearizef_gen _ ey)) (fun v => v)
         end.

    Definition linearize_gen {t} (e : expr t) : expr t
      := match e in Syntax.expr _ _ t return expr t with
         | Abs _ _ f => Abs (fun x => linearizef_gen (f x))
         end.
  End with_var.

  Definition Linearize_gen {t} (e : Expr t) : Expr t
    := fun var => linearize_gen (e _).
End language.

Definition linearizef {base_type_code op var t} e
  := @linearizef_gen false base_type_code op var t e.
Definition a_normalf {base_type_code op var t} e
  := @linearizef_gen true base_type_code op var t e.
Definition linearize {base_type_code op var t} e
  := @linearize_gen false base_type_code op var t e.
Definition a_normal {base_type_code op var t} e
  := @linearize_gen true base_type_code op var t e.
Definition Linearize {base_type_code op t} e
  := @Linearize_gen false base_type_code op t e.
Definition ANormal {base_type_code op t} e
  := @Linearize_gen true base_type_code op t e.
Section language.
  Context {base_type_code : Type}
          {interp_base_type : base_type_code -> Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}
          {interp_op : forall src dst, op src dst -> interp_flat_type interp_base_type src -> interp_flat_type interp_base_type dst}.
  Local Notation Expr := (@Expr base_type_code op).

  Section gen.
    Context (let_bind_op_args : bool).

    Lemma interpf_linearizef_gen {t} e
      : interpf interp_op (linearizef_gen let_bind_op_args (t:=t) e) = interpf interp_op e.
Admitted.

    Lemma interp_linearize_gen {t} e
      : forall x, interp interp_op (linearize_gen let_bind_op_args (t:=t) e) x = interp interp_op e x.
Admitted.

    Lemma InterpLinearize_gen {t} (e : Expr t)
      : forall x, Interp interp_op (Linearize_gen let_bind_op_args e) x = Interp interp_op e x.
Admitted.
  End gen.

  Definition interpf_linearizef {t} e
    : interpf interp_op (linearizef (t:=t) e) = interpf interp_op e
    := interpf_linearizef_gen _ e.
  Definition interpf_a_normalf {t} e
    : interpf interp_op (a_normalf (t:=t) e) = interpf interp_op e
    := interpf_linearizef_gen _ e.

  Definition interp_linearize {t} e
    : forall x, interp interp_op (linearize (t:=t) e) x = interp interp_op e x
    := interp_linearize_gen _ e.
  Definition interp_a_normal {t} e
    : forall x, interp interp_op (a_normal (t:=t) e) x = interp interp_op e x
    := interp_linearize_gen _ e.

  Definition InterpLinearize {t} (e : Expr t)
    : forall x, Interp interp_op (Linearize e) x = Interp interp_op e x
    := InterpLinearize_gen _ e.
  Definition InterpANormal {t} (e : Expr t)
    : forall x, Interp interp_op (ANormal e) x = Interp interp_op e x
    := InterpLinearize_gen _ e.
End language.
Hint Rewrite @InterpLinearize_gen @interp_linearize_gen @interpf_linearizef_gen @InterpLinearize @interp_linearize @interpf_linearizef @InterpANormal @interp_a_normal @interpf_a_normalf : reflective_interp.
Section language.
  Context {base_type_code : Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}.
  Local Notation exprf := (@exprf base_type_code op).
  Local Notation expr := (@expr base_type_code op).
  Local Notation Expr := (@Expr base_type_code op).

  Section with_var.
    Context {var : base_type_code -> Type}.
    Context (rewrite_op_expr : forall src dst (opc : op src dst),
                exprf (var:=var) src -> exprf (var:=var) dst).

    Fixpoint rewrite_opf {t} (e : @exprf var t) : @exprf var t
      := match e in Syntax.exprf _ _ t return @exprf var t with
         | LetIn tx ex tC eC
           => LetIn (@rewrite_opf tx ex) (fun x => @rewrite_opf tC (eC x))
         | Var _ x => Var x
         | TT => TT
         | Pair tx ex ty ey
           => Pair (@rewrite_opf tx ex) (@rewrite_opf ty ey)
         | Op t1 tR opc args => rewrite_op_expr _ _ opc (@rewrite_opf t1 args)
         end.

    Definition rewrite_op {t} (e : @expr var t) : @expr var t
      := match e in Syntax.expr _ _ t return @expr var t with
         | Abs _ _ f => Abs (fun x => rewrite_opf (f x))
         end.
  End with_var.

  Definition RewriteOp
             (rewrite_op_expr : forall var src dst, op src dst -> @exprf var src -> @exprf var dst)
             {t} (e : Expr t)
    : Expr t
    := fun var => rewrite_op (rewrite_op_expr _) (e _).
End language.
Export bbv.Word.
Import Coq.ZArith.ZArith.

Definition word32 := word 32.

Definition word64 := word 64.

Definition word128 := word 128.

Definition word_case {T : nat -> Type} (logsz : nat)
           (case32 : T 5)
           (case64 : T 6)
           (case128 : T 7)
           (default : forall k, T k)
  : T logsz
  := match logsz return T logsz with
     | 5 => case32
     | 6 => case64
     | 7 => case128
     | logsz' => default _
     end.

Definition wordT logsz := word_case (T:=fun _ => Set) logsz word32 word64 word128 (fun logsz => word (2^logsz)).

Definition word_case_dep {T : nat -> Set -> Type} (logsz : nat)
           (case32 : T 5 word32)
           (case64 : T 6 word64)
           (case128 : T 7 word128)
           (default : forall k, T k (word (2^k)))
  : T logsz (wordT logsz)
  := match logsz return T logsz (wordT logsz) with
     | 5 => case32
     | 6 => case64
     | 7 => case128
     | logsz' => default _
     end.

Definition ZToWord_gen {sz} (v : Z) : word sz := NToWord _ (Z.to_N v).
Definition wordToZ_gen {sz} (v : word sz) : Z := Z.of_N (wordToN v).

Definition ZToWord32 : Z -> word32 := @ZToWord_gen _.
Definition word32ToZ : word32 -> Z := @wordToZ_gen _.

Definition ZToWord64 : Z -> word64 := @ZToWord_gen _.
Definition word64ToZ : word64 -> Z := @wordToZ_gen _.

Definition ZToWord128 : Z -> word128 := @ZToWord_gen _.
Definition word128ToZ : word128 -> Z := @wordToZ_gen _.

Definition ZToWord {logsz}
  := word_case_dep (T:=fun _ word => Z -> word)
                   logsz ZToWord32 ZToWord64 ZToWord128 (fun _ => @ZToWord_gen _).
Definition wordToZ {logsz}
  := word_case_dep (T:=fun _ word => word -> Z)
                   logsz word32ToZ word64ToZ word128ToZ (fun _ => @wordToZ_gen _).

Infix ">>" := Z.shiftr : Z_scope.
Infix "&'" := Z.land : Z_scope.
Module Export Definitions.
Import Crypto.Util.LetIn.
Local Open Scope Z_scope.

Module Export Z.

  Definition zselect (cond zero_case nonzero_case : Z) :=
    if cond =? 0 then zero_case else nonzero_case.

  Definition get_carry (bitwidth : Z) (v : Z) : Z * Z
    := (v mod 2^bitwidth, v / 2^bitwidth).
  Definition add_with_carry (c : Z) (x y : Z) : Z
    := c + x + y.
  Definition add_with_get_carry (bitwidth : Z) (c : Z) (x y : Z) : Z * Z
    := dlet v := add_with_carry c x y in get_carry bitwidth v.

  Definition get_borrow (bitwidth : Z) (v : Z) : Z * Z
    := let '(v, c) := get_carry bitwidth v in
       (v, -c).
  Definition sub_with_borrow (c : Z) (x y : Z) : Z
    := add_with_carry (-c) x (-y).
  Definition sub_with_get_borrow (bitwidth : Z) (c : Z) (x y : Z) : Z * Z
    := dlet v := sub_with_borrow c x y in get_borrow bitwidth v.

  Definition mul_split_at_bitwidth (bitwidth : Z) (x y : Z) : Z * Z
    := dlet xy := x * y in
       (if Z.geb bitwidth 0
        then xy &' Z.ones bitwidth
        else xy mod 2^bitwidth,
        if Z.geb bitwidth 0
        then xy >> bitwidth
        else xy / 2^bitwidth).
End Z.

End Definitions.
Definition id_with_alt {A} (value : A) (value_for_alt : A) : A
:= value.
  Section language.
    Context {base_type_code : Type}
            {op : flat_type base_type_code -> flat_type base_type_code -> Type}
            {Name : Type}.
    Section with_var.
      Context {var : base_type_code -> Type}
              {Context : Context Name var}
              (failb : forall t, @Syntax.exprf base_type_code op var (Tbase t)).

      Local Notation failf t
        := (SmartPairf (SmartValf _ failb t)).

      Fixpoint interpf_to_phoas
               (ctx : Context)
               {t} (e : @Named.exprf base_type_code op Name t)
               {struct e}
        : @Syntax.exprf base_type_code op var t
        := match e in Named.exprf _ _ _ t return @Syntax.exprf base_type_code op var t with
           | Named.Var t' x
             => match lookupb t' ctx x with
                | Some v => Var v
                | None => failf _
                end
           | Named.TT => TT
           | Named.Pair tx ex ty ey
             => Pair (@interpf_to_phoas ctx tx ex) (@interpf_to_phoas ctx ty ey)
           | Named.Op _ _ opc args
             => Op opc (@interpf_to_phoas ctx _ args)
           | Named.LetIn _ n ex _ eC
             => LetIn (@interpf_to_phoas ctx _ ex)
                      (fun v
                       => @interpf_to_phoas (extend ctx n v) _ eC)
           end.

      Definition interp_to_phoas
                 (ctx : Context)
                 {t} (e : @Named.expr base_type_code op Name t)
        : @Syntax.expr base_type_code op var (domain t -> codomain t)
        := Abs (fun v => interpf_to_phoas (extend ctx (Abs_name e) v) (invert_Abs e)).
    End with_var.

    Section all.
      Context {Context : forall var, @Context base_type_code Name var}
              (failb : forall var t, @Syntax.exprf base_type_code op var (Tbase t)).
      Definition InterpToPHOAS_gen
                 (ctx : forall var, Context var)
                 {t} (e : @Named.expr base_type_code op Name t)
        : @Syntax.Expr base_type_code op (domain t -> codomain t)
        := fun var => interp_to_phoas (failb var) (ctx var) e.

      Definition InterpToPHOAS {t} e
        := @InterpToPHOAS_gen (fun var => empty) t e.
    End all.
  End language.

Module Crypto_DOT_Compilers_DOT_Z_DOT_Syntax_WRAPPED.
Module Export Syntax.
Local Set Decidable Equality Schemes.
Inductive base_type := TZ | TWord (logsz : nat).

Inductive op : flat_type base_type -> flat_type base_type -> Type :=
| OpConst {T} (z : Z) : op Unit (Tbase T)
| Add T1 T2 Tout : op (Tbase T1 * Tbase T2) (Tbase Tout)
| Sub T1 T2 Tout : op (Tbase T1 * Tbase T2) (Tbase Tout)
| Mul T1 T2 Tout : op (Tbase T1 * Tbase T2) (Tbase Tout)
| Shl T1 T2 Tout : op (Tbase T1 * Tbase T2) (Tbase Tout)
| Shr T1 T2 Tout : op (Tbase T1 * Tbase T2) (Tbase Tout)
| Land T1 T2 Tout : op (Tbase T1 * Tbase T2) (Tbase Tout)
| Lor T1 T2 Tout : op (Tbase T1 * Tbase T2) (Tbase Tout)
| Opp T Tout : op (Tbase T) (Tbase Tout)
| IdWithAlt T1 T2 Tout : op (Tbase T1 * Tbase T2) (Tbase Tout)
| Zselect T1 T2 T3 Tout : op (Tbase T1 * Tbase T2 * Tbase T3) (Tbase Tout)
| MulSplit (bitwidth : Z) T1 T2 Tout1 Tout2 : op (Tbase T1 * Tbase T2) (Tbase Tout1 * Tbase Tout2)
| AddWithCarry T1 T2 T3 Tout : op (Tbase T1 * Tbase T2 * Tbase T3) (Tbase Tout)
| AddWithGetCarry (bitwidth : Z) T1 T2 T3 Tout1 Tout2 : op (Tbase T1 * Tbase T2 * Tbase T3) (Tbase Tout1 * Tbase Tout2)
| SubWithBorrow T1 T2 T3 Tout : op (Tbase T1 * Tbase T2 * Tbase T3) (Tbase Tout)
| SubWithGetBorrow (bitwidth : Z) T1 T2 T3 Tout1 Tout2 : op (Tbase T1 * Tbase T2 * Tbase T3) (Tbase Tout1 * Tbase Tout2)
.

Definition interp_base_type (v : base_type) : Type :=
  match v with
  | TZ => Z
  | TWord logsz => wordT logsz
  end.

Definition interpToZ {t} : interp_base_type t -> Z
  := match t with
     | TZ => fun x => x
     | TWord _ => wordToZ
     end.
Definition ZToInterp {t} : Z -> interp_base_type t
  := match t return Z -> interp_base_type t with
     | TZ => fun x => x
     | TWord _ => ZToWord
     end.
Definition cast_const {t1 t2} (v : interp_base_type t1) : interp_base_type t2
  := ZToInterp (interpToZ v).

Local Notation eta x := (fst x, snd x).
Local Notation eta3 x := (eta (fst x), snd x).

Definition lift_op {src dst}
           (srcv:=SmartValf (fun _ => base_type) (fun t => t) src)
           (dstv:=SmartValf (fun _ => base_type) (fun t => t) dst)
           (ff:=fun t0 (v : interp_flat_type _ t0) t => SmartFlatTypeMap (var':=fun _ => base_type) (fun _ _ => t) v)
           (srcf:=ff src srcv) (dstf:=ff dst dstv)
           (srcZ:=srcf TZ) (dstZ:=dstf TZ)
           (opZ : interp_flat_type interp_base_type srcZ -> interp_flat_type interp_base_type dstZ)
  : interp_flat_type interp_base_type src
    -> interp_flat_type interp_base_type dst
  := fun xy
     => SmartFlatTypeMapUnInterp
         (fun _ _ => cast_const)
         (opZ (SmartFlatTypeMapInterp2 (fun _ _ => cast_const) _ xy)).

Definition Zinterp_op src dst (f : op src dst)
           (asZ := fun t0 => SmartFlatTypeMap (var':=fun _ => base_type) (fun _ _ => TZ) (SmartValf (fun _ => base_type) (fun t => t) t0))
  : interp_flat_type interp_base_type (asZ src) -> interp_flat_type interp_base_type (asZ dst)
  := match f in op src dst return interp_flat_type interp_base_type (asZ src) -> interp_flat_type interp_base_type (asZ dst) with
     | OpConst _ v => fun _ => cast_const (t1:=TZ) v
     | Add _ _ _ => fun xy => fst xy + snd xy
     | Sub _ _ _ => fun xy => fst xy - snd xy
     | Mul _ _ _ => fun xy => fst xy * snd xy
     | Shl _ _ _ => fun xy => Z.shiftl (fst xy) (snd xy)
     | Shr _ _ _ => fun xy => Z.shiftr (fst xy) (snd xy)
     | Land _ _ _ => fun xy => Z.land (fst xy) (snd xy)
     | Lor _ _ _ => fun xy => Z.lor (fst xy) (snd xy)
     | Opp _ _ => fun x => Z.opp x
     | IdWithAlt _ _ _ => fun xy => id_with_alt (fst xy) (snd xy)
     | Zselect _ _ _ _ => fun ctf => let '(c, t, f) := eta3 ctf in Z.zselect c t f
     | MulSplit bitwidth _ _ _ _ => fun xy => Z.mul_split_at_bitwidth bitwidth (fst xy) (snd xy)
     | AddWithCarry _ _ _ _ => fun cxy => let '(c, x, y) := eta3 cxy in Z.add_with_carry c x y
     | AddWithGetCarry bitwidth _ _ _ _ _ => fun cxy => let '(c, x, y) := eta3 cxy in Z.add_with_get_carry bitwidth c x y
     | SubWithBorrow _ _ _ _ => fun cxy => let '(c, x, y) := eta3 cxy in Z.sub_with_borrow c x y
     | SubWithGetBorrow bitwidth _ _ _ _ _ => fun cxy => let '(c, x, y) := eta3 cxy in Z.sub_with_get_borrow bitwidth c x y
     end%Z.

Definition interp_op src dst (f : op src dst) : interp_flat_type interp_base_type src -> interp_flat_type interp_base_type dst
  := lift_op (Zinterp_op src dst f).

Notation Expr := (Expr base_type op).
Notation Interp := (Interp interp_op).

End Syntax.

End Crypto_DOT_Compilers_DOT_Z_DOT_Syntax_WRAPPED.
Module Export Crypto.
Module Export Compilers.
Module Export Z.
Module Syntax.
Include Crypto_DOT_Compilers_DOT_Z_DOT_Syntax_WRAPPED.Syntax.
End Syntax.
Module Export Equality.
Import Crypto.Compilers.Z.Syntax.

Definition base_type_eq_semidec_transparent (t1 t2 : base_type)
  : option (t1 = t2)
  := match base_type_eq_dec t1 t2 with
     | left pf => Some pf
     | right _ => None
     end.

End Equality.
Module Export ArithmeticSimplifier.
Import Crypto.Compilers.Z.Syntax.

Section language.
  Context (convert_adc_to_sbb : bool).
  Local Notation exprf := (@exprf base_type op).

  Section with_var.
    Context {var : base_type -> Type}.

    Inductive inverted_expr t :=
    | const_of (v : Z)
    | gen_expr (e : exprf (var:=var) (Tbase t))
    | neg_expr (e : exprf (var:=var) (Tbase t)).

    Fixpoint interp_as_expr_or_const {t} (x : exprf (var:=var) t)
      : option (interp_flat_type inverted_expr t)
      := match x in Syntax.exprf _ _ t return option (interp_flat_type _ t) with
         | Op t1 (Tbase _) opc args
           => Some (match opc in op src dst
                          return exprf dst
                                 -> exprf src
                                 -> match dst with
                                    | Tbase t => inverted_expr t
                                    | Prod _ _ => True
                                    | _ => inverted_expr TZ
                                    end
                    with
                    | OpConst _ z => fun _ _ => const_of _ z
                    | Opp TZ TZ => fun _ args => neg_expr _ args
                    | MulSplit _ _ _ _ _ => fun _ _ => I
                    | AddWithGetCarry _ _ _ _ _ _ => fun _ _ => I
                    | SubWithGetBorrow _ _ _ _ _ _ => fun _ _ => I
                    | _ => fun e _ => gen_expr _ e
                    end (Op opc args) args)
         | TT => Some tt
         | Var t v => Some (gen_expr _ (Var v))
         | Op _ _ _ _
         | LetIn _ _ _ _
           => None
         | Pair tx ex ty ey
           => match @interp_as_expr_or_const tx ex, @interp_as_expr_or_const ty ey with
              | Some vx, Some vy => Some (vx, vy)
              | _, None | None, _ => None
              end
         end.

    Fixpoint uninterp_expr_or_const {t} : interp_flat_type inverted_expr t -> exprf (var:=var) t
      := match t with
         | Tbase T => fun e => match e with
                               | const_of v => Op (OpConst v) TT
                               | gen_expr e => e
                               | neg_expr e => Op (Opp _ _) e
                               end
         | Unit => fun _ => TT
         | Prod A B => fun (ab : interp_flat_type _ A * interp_flat_type _ B)
                       => Pair (@uninterp_expr_or_const A (fst ab))
                               (@uninterp_expr_or_const B (snd ab))
         end.

    Definition simplify_op_expr {src dst} (opc : op src dst)
      : exprf (var:=var) src -> exprf (var:=var) dst
      := match opc in op src dst return exprf src -> exprf dst with
         | Add TZ TZ TZ as opc
           => fun args
              => match interp_as_expr_or_const args with
                 | Some (const_of l, const_of r)
                   => Op (OpConst (interp_op _ _ opc (l, r))) TT
                 | Some (const_of v, gen_expr e)
                 | Some (gen_expr e, const_of v)
                   => if (v =? 0)%Z
                      then e
                      else Op opc args
                 | Some (const_of v, neg_expr e)
                 | Some (neg_expr e, const_of v)
                   => if (v =? 0)%Z
                      then Op (Opp _ _) e
                      else Op opc args
                 | Some (gen_expr ep, neg_expr en)
                 | Some (neg_expr en, gen_expr ep)
                   => Op (Sub _ _ _) (Pair ep en)
                 | _ => Op opc args
                 end
         | Add T1 T2 Tout as opc
           => fun args
              => match interp_as_expr_or_const args with
                 | Some (const_of v, gen_expr e)
                   => if (v =? 0)%Z
                      then match base_type_eq_semidec_transparent T2 Tout with
                           | Some pf => eq_rect _ (fun t => exprf (Tbase t)) e _ pf
                           | None => Op opc args
                           end
                      else Op opc args
                 | Some (gen_expr e, const_of v)
                   => if (v =? 0)%Z
                      then match base_type_eq_semidec_transparent T1 Tout with
                           | Some pf => eq_rect _ (fun t => exprf (Tbase t)) e _ pf
                           | None => Op opc args
                           end
                      else Op opc args
                 | _ => Op opc args
                 end
         | Sub TZ TZ TZ as opc
           => fun args
              => match interp_as_expr_or_const args with
                 | Some (const_of l, const_of r)
                   => Op (OpConst (interp_op _ _ opc (l, r))) TT
                 | Some (gen_expr e, const_of v)
                   => if (v =? 0)%Z
                      then e
                      else Op opc args
                 | Some (neg_expr e, const_of v)
                   => if (v =? 0)%Z
                      then Op (Opp _ _) e
                      else Op opc args
                 | Some (gen_expr e1, neg_expr e2)
                   => Op (Add _ _ _) (Pair e1 e2)
                 | Some (neg_expr e1, neg_expr e2)
                   => Op (Sub _ _ _) (Pair e2 e1)
                 | _ => Op opc args
                 end
         | Mul TZ TZ TZ as opc
           => fun args
              => match interp_as_expr_or_const args with
                 | Some (const_of l, const_of r)
                   => Op (OpConst (interp_op _ _ opc (l, r))) TT
                 | Some (const_of v, gen_expr e)
                 | Some (gen_expr e, const_of v)
                   => if (v =? 0)%Z
                      then Op (OpConst 0%Z) TT
                      else if (v =? 1)%Z
                           then e
                           else if (v =? -1)%Z
                                then Op (Opp _ _) e
                                else Op opc args
                 | Some (const_of v, neg_expr e)
                 | Some (neg_expr e, const_of v)
                   => if (v =? 0)%Z
                      then Op (OpConst 0%Z) TT
                      else if (v =? 1)%Z
                           then Op (Opp _ _) e
                           else if (v =? -1)%Z
                                then e
                                else if (v >? 0)%Z
                                     then Op (Opp _ _) (Op opc (Pair (Op (OpConst v) TT) e))
                                     else Op opc args
                 | Some (gen_expr e1, neg_expr e2)
                 | Some (neg_expr e1, gen_expr e2)
                   => Op (Opp _ _) (Op (Mul _ _ TZ) (Pair e1 e2))
                 | Some (neg_expr e1, neg_expr e2)
                   => Op (Mul _ _ _) (Pair e1 e2)
                 | _ => Op opc args
                 end
         | Mul (TWord bw1 as T1) (TWord bw2 as T2) (TWord bwout as Tout) as opc
           => fun args
              => let sz1 := (2^Z.of_nat (2^bw1))%Z in
                 let sz2 := (2^Z.of_nat (2^bw2))%Z in
                 let szout := (2^Z.of_nat (2^bwout))%Z in
                 match interp_as_expr_or_const args with
                 | Some (const_of l, const_of r)
                   => Op (OpConst (((Z.max 0 l mod sz1) * (Z.max 0 r mod sz2)) mod szout)%Z) TT
                 | Some (const_of v, gen_expr e)
                   => if ((Z.max 0 v mod sz1) mod szout =? 0)%Z
                      then Op (OpConst 0%Z) TT
                      else if ((Z.max 0 v mod sz1) mod szout =? 1)%Z
                           then match base_type_eq_semidec_transparent T2 Tout with
                                | Some pf => eq_rect _ (fun t => exprf (Tbase t)) e _ pf
                                | None => Op opc args
                                end
                           else Op opc args
                 | Some (gen_expr e, const_of v)
                   => if ((Z.max 0 v mod sz2) mod szout =? 0)%Z
                      then Op (OpConst 0%Z) TT
                      else if ((Z.max 0 v mod sz2) mod szout =? 1)%Z
                           then match base_type_eq_semidec_transparent T1 Tout with
                                | Some pf => eq_rect _ (fun t => exprf (Tbase t)) e _ pf
                                | None => Op opc args
                                end
                           else Op opc args
                 | _ => Op opc args
                 end
         | Shl TZ TZ TZ as opc
         | Shr TZ TZ TZ as opc
           => fun args
              => match interp_as_expr_or_const args with
                 | Some (const_of l, const_of r)
                   => Op (OpConst (interp_op _ _ opc (l, r))) TT
                 | Some (gen_expr e, const_of v)
                   => if (v =? 0)%Z
                      then e
                      else Op opc args
                 | Some (neg_expr e, const_of v)
                   => if (v =? 0)%Z
                      then Op (Opp _ _) e
                      else Op opc args
                 | _ => Op opc args
                 end
         | Land TZ TZ TZ as opc
           => fun args
              => match interp_as_expr_or_const args with
                 | Some (const_of l, const_of r)
                   => Op (OpConst (interp_op _ _ opc (l, r))) TT
                 | Some (const_of v, gen_expr _)
                 | Some (gen_expr _, const_of v)
                 | Some (const_of v, neg_expr _)
                 | Some (neg_expr _, const_of v)
                   => if (v =? 0)%Z
                      then Op (OpConst 0%Z) TT
                      else Op opc args
                 | _ => Op opc args
                 end
         | Lor TZ TZ TZ as opc
           => fun args
              => match interp_as_expr_or_const args with
                 | Some (const_of l, const_of r)
                   => Op (OpConst (interp_op _ _ opc (l, r))) TT
                 | Some (const_of v, gen_expr e)
                 | Some (gen_expr e, const_of v)
                   => if (v =? 0)%Z
                      then e
                      else Op opc args
                 | Some (const_of v, neg_expr e)
                 | Some (neg_expr e, const_of v)
                   => if (v =? 0)%Z
                      then Op (Opp _ _) e
                      else Op opc args
                 | _ => Op opc args
                 end
         | Opp TZ TZ as opc
           => fun args
              => match interp_as_expr_or_const args with
                 | Some (const_of v)
                   => Op (OpConst (interp_op _ _ opc v)) TT
                 | Some (neg_expr e)
                   => e
                 | _
                   => Op opc args
                 end
         | MulSplit bitwidth (TWord bw1 as T1) (TWord bw2 as T2) (TWord bwout1 as Tout1) (TWord bwout2 as Tout2) as opc
           => fun args
              => let sz1 := (2^Z.of_nat (2^bw1))%Z in
                 let sz2 := (2^Z.of_nat (2^bw2))%Z in
                 let szout1 := (2^Z.of_nat (2^bwout1))%Z in
                 let szout2 := (2^Z.of_nat (2^bwout2))%Z in
                 match interp_as_expr_or_const args with
                 | Some (const_of l, const_of r)
                   => let '(a, b) := Z.mul_split_at_bitwidth bitwidth (Z.max 0 l mod sz1) (Z.max 0 r mod sz2) in
                      Pair (Op (OpConst (a mod szout1)%Z) TT)
                           (Op (OpConst (b mod szout2)%Z) TT)
                 | Some (const_of v, gen_expr e)
                   => let v' := (Z.max 0 v mod sz1)%Z in
                      if (v' =? 0)%Z
                      then Pair (Op (OpConst 0%Z) TT) (Op (OpConst 0%Z) TT)
                      else if ((v' =? 1) && (2^Z.of_nat (2^bw2) <=? 2^bitwidth))%Z%bool
                           then match base_type_eq_semidec_transparent T2 Tout1 with
                                | Some pf => Pair (eq_rect _ (fun t => exprf (Tbase t)) e _ pf)
                                                  (Op (OpConst 0%Z) TT)
                                | None => Op opc args
                                end
                           else Op opc args
                 | Some (gen_expr e, const_of v)
                   => let v' := (Z.max 0 v mod sz2)%Z in
                      if (v' =? 0)%Z
                      then Pair (Op (OpConst 0%Z) TT) (Op (OpConst 0%Z) TT)
                      else if ((v' =? 1) && (2^Z.of_nat (2^bw1) <=? 2^bitwidth))%Z%bool
                           then match base_type_eq_semidec_transparent T1 Tout1 with
                                | Some pf => Pair (eq_rect _ (fun t => exprf (Tbase t)) e _ pf)
                                                  (Op (OpConst 0%Z) TT)
                                | None => Op opc args
                                end
                           else Op opc args
                 | _ => Op opc args
                 end
         | IdWithAlt (TWord _ as T1) _ (TWord _ as Tout) as opc
           => fun args
              => match base_type_eq_semidec_transparent T1 Tout with
                 | Some pf
                   => match interp_as_expr_or_const args with
                      | Some (const_of c, _)
                        => Op (OpConst c) TT
                      | Some (neg_expr e, _)
                        => Op (Opp _ _) e
                      | Some (gen_expr e, _)
                        => eq_rect _ (fun t => exprf (Tbase t)) e _ pf
                      | None
                        => Op opc args
                      end
                 | None
                   => Op opc args
                 end
         | IdWithAlt TZ TZ TZ as opc
           => fun args
              => match interp_as_expr_or_const args with
                 | Some (gen_expr e1, gen_expr e2)
                   => match invert_Op e1, invert_Op e2 with
                      | Some (existT _ (Add TZ TZ TZ as opc1, args1)),
                        Some (existT _ (Add TZ TZ TZ as opc2, args2))
                      | Some (existT _ (Sub TZ TZ TZ as opc1, args1)),
                        Some (existT _ (Sub TZ TZ TZ as opc2, args2))
                      | Some (existT _ (Mul TZ TZ TZ as opc1, args1)),
                        Some (existT _ (Mul TZ TZ TZ as opc2, args2))
                        => match interp_as_expr_or_const args1, interp_as_expr_or_const args2 with
                           | Some (gen_expr e1, const_of c1),
                             Some (gen_expr e2, const_of c2)
                             => if Z.eqb c1 c2
                                then Op opc1 (Op opc (e1, e2), Op (OpConst c1) TT)%expr
                                else Op opc args
                           | _, _
                             => Op opc args
                           end
                      | _, _
                        => Op opc args
                      end
                 | Some (neg_expr e1, neg_expr e2)
                   => Op (Opp _ _) (Op opc (e1, e2)%expr)
                 | Some (const_of c1, const_of c2)
                   => Op (OpConst c1) TT
                 | _
                   => Op opc args
                 end
         | IdWithAlt _ _ (TWord _ as Tout) as opc
           => fun args
              => match interp_as_expr_or_const args with
                 | Some (gen_expr e1, _)
                   => match invert_Op e1 with
                      | Some (existT _ (Add (TWord _) (TWord _) TZ as opc1, args1))
                        => Op (Add _ _ Tout) args1
                      | Some (existT _ (Sub (TWord _) (TWord _) TZ as opc1, args1))
                        => Op (Sub _ _ Tout) args1
                      | Some (existT _ (Mul (TWord _) (TWord _) TZ as opc1, args1))
                        => Op (Mul _ _ Tout) args1
                      | _
                        => Op opc args
                      end
                 | _
                   => Op opc args
                 end
         | Zselect TZ TZ TZ TZ as opc
           => fun args
              => match interp_as_expr_or_const args with
                 | Some (const_of c, x, y)
                   => match (c =? 0)%Z, x, y with
                      | true, const_of c, _
                      | false, _, const_of c
                        => Op (OpConst c) TT
                      | true, gen_expr e, _
                      | false, _, gen_expr e
                        => e
                      | true, neg_expr e, _
                      | false, _, neg_expr e
                        => Op (Opp TZ TZ) e
                      end
                 | Some (neg_expr e, x, y)
                   => let x := uninterp_expr_or_const (t:=Tbase _) x in
                      let y := uninterp_expr_or_const (t:=Tbase _) y in
                      Op (Zselect TZ TZ TZ TZ) (e, x, y)%expr
                 | _ => Op opc args
                 end
         | AddWithCarry TZ TZ TZ TZ as opc
           => fun args
              => let first_pass
                     := match interp_as_expr_or_const args with
                        | Some (const_of c, const_of x, const_of y)
                          => Some (Op (OpConst (interp_op _ _ opc (c, x, y))) TT)
                        | Some (gen_expr e, const_of c1, const_of c2)
                        | Some (const_of c1, gen_expr e, const_of c2)
                        | Some (const_of c1, const_of c2, gen_expr e)
                          => if (c1 + c2 =? 0)%Z
                             then Some e
                             else None
                        | _ => None
                        end in
                 match first_pass with
                 | Some e => e
                 | None
                   => if convert_adc_to_sbb
                      then match interp_as_expr_or_const args with
                           | Some (const_of c, const_of x, const_of y)
                             => Op (OpConst (interp_op _ _ opc (c, x, y))) TT
                           | Some (c, gen_expr x, y)
                             => let y' := match y with
                                          | const_of y => if (y <? 0)%Z
                                                          then Some (Op (OpConst (-y)) TT)
                                                          else None
                                          | neg_expr y => Some y
                                          | gen_expr _ => None
                                          end in
                                match y' with
                                | Some y => Op (SubWithBorrow TZ TZ TZ TZ)
                                               (match c with
                                                | const_of c => Op (OpConst (-c)) TT
                                                | neg_expr c => c
                                                | gen_expr c => Op (Opp TZ TZ) c
                                                end,
                                                x, y)%expr
                                | None => Op opc args
                                end
                           | _ => Op opc args
                           end
                      else Op opc args
                 end
         | AddWithGetCarry bw TZ TZ TZ TZ TZ as opc
           => fun args
              => if convert_adc_to_sbb
                 then match interp_as_expr_or_const args with
                      | Some (const_of c, const_of x, const_of y)
                        => let '(v, c) := interp_op _ _ opc (c, x, y) in
                           (Op (OpConst v) TT, Op (OpConst c) TT)%expr
                      | Some (c, gen_expr x, y)
                        => let y' := match y with
                                     | const_of y => if (y <? 0)%Z
                                                     then Some (Op (OpConst (-y)) TT)
                                                     else None
                                     | neg_expr y => Some y
                                     | gen_expr _ => None
                                     end in
                           let c' := match c with
                                     | const_of c => if (c <? 0)%Z
                                                     then Some (Op (OpConst (-c)) TT)
                                                     else None
                                     | neg_expr c => Some c
                                     | gen_expr _ => None
                                     end in
                           match c', y' with
                           | _, Some y => LetIn (Op (SubWithGetBorrow bw TZ TZ TZ TZ TZ)
                                                    (match c with
                                                     | const_of c => Op (OpConst (-c)) TT
                                                     | neg_expr c => c
                                                     | gen_expr c => Op (Opp TZ TZ) c
                                                     end,
                                                     x, y)%expr)
                                                (fun '(v, c) => (Var v, Op (Opp TZ TZ) (Var c))%expr)
                           | Some c, _ => LetIn (Op (SubWithGetBorrow bw TZ TZ TZ TZ TZ)
                                                    (c,
                                                     x,
                                                     match y with
                                                     | const_of y => Op (OpConst (-y)) TT
                                                     | neg_expr y => y
                                                     | gen_expr y => Op (Opp TZ TZ) y
                                                     end)%expr)
                                                (fun '(v, c) => (Var v, Op (Opp TZ TZ) (Var c))%expr)
                           | None, None => Op opc args
                           end
                      | Some (c, const_of x, y)
                        => let y' := match y with
                                     | const_of y => if (y <? 0)%Z
                                                     then Some (Op (OpConst (-y)) TT)
                                                     else None
                                     | neg_expr y => Some y
                                     | gen_expr _ => None
                                     end in
                           let c' := match c with
                                     | const_of c => if (c <? 0)%Z
                                                     then Some (Op (OpConst (-c)) TT)
                                                     else None
                                     | neg_expr c => Some c
                                     | gen_expr _ => None
                                     end in
                           match c', y' with
                           | _, Some y => LetIn (Op (SubWithGetBorrow bw TZ TZ TZ TZ TZ)
                                                    (match c with
                                                     | const_of c => Op (OpConst (-c)) TT
                                                     | neg_expr c => c
                                                     | gen_expr c => Op (Opp TZ TZ) c
                                                     end,
                                                     Op (OpConst x) TT, y)%expr)
                                                (fun '(v, c) => (Var v, Op (Opp TZ TZ) (Var c))%expr)
                           | Some c, _ => LetIn (Op (SubWithGetBorrow bw TZ TZ TZ TZ TZ)
                                                    (c,
                                                     Op (OpConst x) TT,
                                                     match y with
                                                     | const_of y => Op (OpConst (-y)) TT
                                                     | neg_expr y => y
                                                     | gen_expr y => Op (Opp TZ TZ) y
                                                     end)%expr)
                                                (fun '(v, c) => (Var v, Op (Opp TZ TZ) (Var c))%expr)
                           | None, None => Op opc args
                           end
                      | _ => Op opc args
                      end
                 else Op opc args
         | AddWithGetCarry bw (TWord bw1 as T1) (TWord bw2 as T2) (TWord bw3 as T3) (TWord bwout as Tout) Tout2 as opc
           => fun args
              => let pass0
                     := if ((0 <=? bw)%Z && (2^Z.of_nat (2^bw1) + 2^Z.of_nat (2^bw2) + 2^Z.of_nat (2^bw3) - 3 <=? 2^bw - 1)%Z)%nat%bool
                        then Some (Pair (LetIn args (fun '(a, b, c) => Op (Add _ _ _) (Pair (Op (Add _ _ Tout) (Pair (Var a) (Var b))) (Var c))))
                                        (Op (OpConst 0) TT))
                        else None
                 in
                 match pass0 with
                 | Some e => e
                 | None
                   => match interp_as_expr_or_const args with
                      | Some (const_of c, const_of x, const_of y)
                        => if ((c =? 0) && (x =? 0) && (y =? 0))%Z%bool
                           then Pair (Op (OpConst 0) TT) (Op (OpConst 0) TT)
                           else Op opc args
                      | Some (gen_expr e, const_of c1, const_of c2)
                        => match base_type_eq_semidec_transparent T1 Tout with
                           | Some pf
                             => if ((c1 =? 0) && (c2 =? 0) && (2^Z.of_nat bw1 <=? bw))%Z%bool
                                then Pair (eq_rect _ (fun t => exprf (Tbase t)) e _ pf) (Op (OpConst 0) TT)
                                else Op opc args
                           | None
                             => Op opc args
                           end
                      | Some (const_of c1, gen_expr e, const_of c2)
                        => match base_type_eq_semidec_transparent T2 Tout with
                           | Some pf
                             => if ((c1 =? 0) && (c2 =? 0) && (2^Z.of_nat bw2 <=? bw))%Z%bool
                                then Pair (eq_rect _ (fun t => exprf (Tbase t)) e _ pf) (Op (OpConst 0) TT)
                                else Op opc args
                           | None
                             => Op opc args
                           end
                      | Some (const_of c1, const_of c2, gen_expr e)
                        => match base_type_eq_semidec_transparent T3 Tout with
                           | Some pf
                             => if ((c1 =? 0) && (c2 =? 0) && (2^Z.of_nat bw3 <=? bw))%Z%bool
                                then Pair (eq_rect _ (fun t => exprf (Tbase t)) e _ pf) (Op (OpConst 0) TT)
                                else Op opc args
                           | None
                             => Op opc args
                           end
                      | _ => Op opc args
                      end
                 end
         | SubWithBorrow TZ TZ TZ TZ as opc
           => fun args
              => if convert_adc_to_sbb
                 then match interp_as_expr_or_const args with
                      | Some (const_of c, const_of x, const_of y)
                        => Op (OpConst (interp_op _ _ opc (c, x, y))) TT
                      | Some (c, gen_expr x, y)
                        => let y' := match y with
                                     | const_of y => if (y <? 0)%Z
                                                     then Some (Op (OpConst (-y)) TT)
                                                     else None
                                     | neg_expr y => Some y
                                     | gen_expr _ => None
                                     end in
                           match y' with
                           | Some y => Op (AddWithCarry TZ TZ TZ TZ)
                                          (match c with
                                           | const_of c => Op (OpConst (-c)) TT
                                           | neg_expr c => c
                                           | gen_expr c => Op (Opp TZ TZ) c
                                           end,
                                           x, y)%expr
                           | None => Op opc args
                           end
                      | _ => Op opc args
                      end
                 else Op opc args
         | SubWithGetBorrow bw TZ TZ TZ TZ TZ as opc
           => fun args
              => if convert_adc_to_sbb
                 then match interp_as_expr_or_const args with
                      | Some (const_of c, const_of x, const_of y)
                        => let '(v, c) := interp_op _ _ opc (c, x, y) in
                           (Op (OpConst v) TT, Op (OpConst c) TT)%expr
                      | Some (c, gen_expr x, y)
                        => let y' := match y with
                                     | const_of y => if (y <? 0)%Z
                                                     then Some (Op (OpConst (-y)) TT)
                                                     else None
                                     | neg_expr y => Some y
                                     | gen_expr _ => None
                                     end in
                           match y' with
                           | Some y => LetIn (Op (AddWithGetCarry bw TZ TZ TZ TZ TZ)
                                                 (match c with
                                                  | const_of c => Op (OpConst (-c)) TT
                                                  | neg_expr c => c
                                                  | gen_expr c => Op (Opp TZ TZ) c
                                                  end,
                                                  x, y)%expr)
                                             (fun '(v, c) => (Var v, Op (Opp TZ TZ) (Var c))%expr)
                           | None => Op opc args
                           end
                      | _ => Op opc args
                      end
                 else Op opc args
         | Sub _ _ _ as opc
         | Mul _ _ _ as opc
         | Shl _ _ _ as opc
         | Shr _ _ _ as opc
         | Land _ _ _ as opc
         | Lor _ _ _ as opc
         | OpConst _ _ as opc
         | Opp _ _ as opc
         | IdWithAlt _ _ _ as opc
         | Zselect _ _ _ _ as opc
         | MulSplit _ _ _ _ _ as opc
         | AddWithCarry _ _ _ _ as opc
         | AddWithGetCarry _ _ _ _ _ _ as opc
         | SubWithBorrow _ _ _ _ as opc
         | SubWithGetBorrow _ _ _ _ _ _ as opc
           => Op opc
         end.
  End with_var.

  Definition SimplifyArith {t} (e : Expr t) : Expr t
    := @RewriteOp base_type op (@simplify_op_expr) t e.
End language.

End ArithmeticSimplifier.
Module Export ArithmeticSimplifierInterp.
Import Crypto.Compilers.Z.Syntax.

Lemma InterpSimplifyArith {convert_adc_to_sbb} {t} (e : Expr t)
  : forall x, Interp (SimplifyArith convert_adc_to_sbb e) x = Interp e x.
Admitted.

Hint Rewrite @InterpSimplifyArith : reflective_interp.

End ArithmeticSimplifierInterp.

Module Export Crypto_DOT_Compilers_DOT_Inline_WRAPPED.
Module Export Inline.
Section language.
  Context {base_type_code : Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}.

  Local Notation flat_type := (flat_type base_type_code).
  Let Tbase := @Tbase base_type_code.
  Local Coercion Tbase : base_type_code >-> Syntax.flat_type.
  Local Notation exprf := (@exprf base_type_code op).
  Local Notation expr := (@expr base_type_code op).
  Local Notation Expr := (@Expr base_type_code op).

  Section with_var.
    Context {var : base_type_code -> Type}.

    Inductive inline_directive : flat_type -> Type :=
    | default_inline {t} (e : @exprf var t) : inline_directive t
    | inline {t} (e : interp_flat_type (fun t => @exprf var (Tbase t)) t) : inline_directive t
    | no_inline {t} (e : @exprf var t) : inline_directive t
    | partial_inline
        {tx tC}
        (ex : @exprf var tx)
        (eC : interp_flat_type var tx -> interp_flat_type (fun t => @exprf var (Tbase t)) tC)
      : inline_directive tC.

    Context (postprocess : forall {t}, @exprf var t -> inline_directive t).
    Local Arguments postprocess {t}.

    Fixpoint inline_const_genf {t} (e : @exprf (@exprf var) t) : @exprf var t
      := match e in Syntax.exprf _ _ t return @exprf var t with
         | LetIn tx ex tC eC
           => match postprocess (@inline_const_genf _ ex) in inline_directive t' return (interp_flat_type _ t' -> @exprf var tC) -> @exprf var tC with
              | default_inline _ ex
                => match ex in Syntax.exprf _ _ t' return (interp_flat_type _ t' -> @exprf var tC) -> @exprf var tC with
                   | TT => fun eC => eC tt
                   | Var _ x => fun eC => eC (Var x)
                   | ex => fun eC => LetIn ex (fun x => eC (SmartVarVarf x))
                   end
              | no_inline _ ex
                => fun eC => LetIn ex (fun x => eC (SmartVarVarf x))
              | inline _ ex => fun eC => eC ex
              | partial_inline _ _ ex eC'
                => fun eC => LetIn ex (fun x => eC (eC' x))
              end (fun x => @inline_const_genf _ (eC x))
         | Var _ x => x
         | TT => TT
         | Pair _ ex _ ey => Pair (@inline_const_genf _ ex) (@inline_const_genf _ ey)
         | Op _ _ op args => Op op (@inline_const_genf _ args)
         end.

    Definition inline_const_gen {t} (e : @expr (@exprf var) t) : @expr var t
      := match e in Syntax.expr _ _ t return @expr var t with
         | Abs _ _ f => Abs (fun x => inline_const_genf (f (SmartVarVarf x)))
         end.

    Section with_is_const.
      Context (is_const : forall s d, op s d -> bool).

      Definition postprocess_for_const (t : flat_type) (v : @exprf var t) : inline_directive t
        := if match v with Op _ _ op _ => @is_const _ _ op | _ => false end
           then match t return @exprf _ t -> inline_directive t with
                | Syntax.Tbase _ => @inline (Tbase _)
                | _ => @default_inline _
                end v
           else default_inline v.
    End with_is_const.
  End with_var.

  Definition InlineConstGen (postprocess : forall var t, @exprf var t -> @inline_directive var t)
             {t} (e : Expr t) : Expr t
    := fun var => inline_const_gen (postprocess _) (e _).
  Definition InlineConst is_const {t}
    := @InlineConstGen (fun var => postprocess_for_const is_const) t.
End language.

End Inline.

End Crypto_DOT_Compilers_DOT_Inline_WRAPPED.
Module Export Crypto_DOT_Compilers_DOT_InlineWf_WRAPPED.
Module Export InlineWf.
Section language.
  Context {base_type_code : Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}.
  Local Notation Expr := (@Expr base_type_code op).

  Lemma Wf_InlineConst is_const {t} (e : Expr t)
        (Hwf : Wf e)
    : Wf (InlineConst is_const e).
Admitted.
End language.

End InlineWf.

End Crypto_DOT_Compilers_DOT_InlineWf_WRAPPED.
Module Export Crypto_DOT_Compilers_DOT_InlineInterp_WRAPPED.
Module Export InlineInterp.
Section language.
  Context (base_type_code : Type).
  Context (interp_base_type : base_type_code -> Type).
  Context (op : flat_type base_type_code -> flat_type base_type_code -> Type).
  Context (interp_op : forall src dst, op src dst -> interp_flat_type interp_base_type src -> interp_flat_type interp_base_type dst).
  Local Notation Expr := (@Expr base_type_code op).

  Lemma InterpInlineConst is_const {t} (e : Expr t)
        (wf : Wf e)
    : forall x, Interp interp_op (InlineConst is_const e) x = Interp interp_op e x.
Admitted.
End language.

End InlineInterp.

End Crypto_DOT_Compilers_DOT_InlineInterp_WRAPPED.
Module Export Util.
Import Crypto.Compilers.Z.Syntax.
Definition is_const s d (v : op s d) : bool
  := match v with OpConst _ _ => true | _ => false end.
Arguments is_const [s d] v.
Definition is_opp s d (v : op s d) : bool
  := match v with Opp _ _ => true | _ => false end.
Arguments is_opp [s d] v.
Definition is_const_or_opp s d (v : op s d) : bool
  := (is_const v || is_opp v)%bool.

End Util.
Module Export Inline.
Import Crypto.Compilers.Z.Syntax.

Definition InlineConstAndOpp {t} (e : Expr t) : Expr t
  := @InlineConst base_type op (is_const_or_opp) t e.

Definition InlineConst {t} (e : Expr t) : Expr t
  := @InlineConst base_type op (is_const) t e.

End Inline.
Module Export InlineInterp.
Import Crypto.Compilers.Z.Syntax.

Definition InterpInlineConstAndOpp {interp_base_type interp_op} {t} (e : Expr t) (Hwf : Wf e)
  : forall x, Compilers.Syntax.Interp interp_op (InlineConstAndOpp e) x = Compilers.Syntax.Interp interp_op e x
  := @InterpInlineConst _ interp_base_type _ _ _ t e Hwf.

Definition InterpInlineConst {interp_base_type interp_op} {t} (e : Expr t) (Hwf : Wf e)
  : forall x, Compilers.Syntax.Interp interp_op (InlineConst e) x = Compilers.Syntax.Interp interp_op e x
  := @InterpInlineConst _ interp_base_type _ _ _ t e Hwf.

Hint Rewrite @InterpInlineConstAndOpp @InterpInlineConst using solve_wf_side_condition : reflective_interp.

End InlineInterp.
Module Export InlineWf.
Import Crypto.Compilers.Z.Syntax.

Definition Wf_InlineConstAndOpp {t} (e : Expr t) (Hwf : Wf e)
  : Wf (InlineConstAndOpp e)
  := @Wf_InlineConst _ _ _ t e Hwf.

Definition Wf_InlineConst {t} (e : Expr t) (Hwf : Wf e)
  : Wf (InlineConst e)
  := @Wf_InlineConst _ _ _ t e Hwf.

Hint Resolve Wf_InlineConstAndOpp Wf_InlineConst : wf.

End InlineWf.
Section language.
  Context {base_type_code : Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}.
  Local Notation Expr := (@Expr base_type_code op).

  Section gen.
    Context (let_bind_op_args : bool).

    Lemma Wf_Linearize_gen {t} (e : Expr t) : Wf e -> Wf (Linearize_gen let_bind_op_args e).
Admitted.
  End gen.

  Definition Wf_Linearize {t} (e : Expr t) : Wf e -> Wf (Linearize e)
    := Wf_Linearize_gen _ e.
  Definition Wf_ANormal {t} (e : Expr t) : Wf e -> Wf (ANormal e)
    := Wf_Linearize_gen _ e.
End language.

Hint Resolve Wf_Linearize_gen Wf_Linearize Wf_ANormal : wf.
Module Export ArithmeticSimplifierWf.
Import Crypto.Compilers.Z.Syntax.

Lemma Wf_SimplifyArith {convert_adc_to_sbb} {t} (e : Expr t)
      (Hwf : Wf e)
  : Wf (SimplifyArith convert_adc_to_sbb e).
Admitted.

Hint Resolve Wf_SimplifyArith : wf.

End ArithmeticSimplifierWf.
Import Coq.FSets.FMapInterface.
Import Crypto.Compilers.Named.Context.

Module FMapContextFun (E : DecidableType) (W : WSfun E).
  Section ctx.
    Context (E_eq_l : forall x y, E.eq x y -> x = y)
            base_type_code (var : base_type_code -> Type)
            (base_type_code_beq : base_type_code -> base_type_code -> bool)
            (base_type_code_bl_transparent : forall x y, base_type_code_beq x y = true -> x = y)
            (base_type_code_lb : forall x y, x = y -> base_type_code_beq x y = true).

    Definition var_cast {a b} (x : var a) : option (var b)
      := match Sumbool.sumbool_of_bool (base_type_code_beq a b), Sumbool.sumbool_of_bool (base_type_code_beq b b) with
         | left pf, left pf' => match eq_trans (base_type_code_bl_transparent _ _ pf) (eq_sym (base_type_code_bl_transparent _ _ pf')) with
                                | eq_refl => Some x
                                end
         | right _, _ | _, right _ => None
         end.
    Definition FMapContext : @Context base_type_code W.key var
      := {| ContextT := W.t { t : _ & var t };
            lookupb t ctx n
            := match W.find n ctx with
               | Some (existT t' v)
                 => var_cast v
               | None => None
               end;
            extendb t ctx n v
            := W.add n (existT _ t v) ctx;
            removeb t ctx n
            := W.remove n ctx;
            empty := W.empty _ |}.
  End ctx.

  Section ctx_nd.
    Context {base_type_code var : Type}.

    Definition FMapContext_nd : @Context base_type_code W.key (fun _ => var)
      := {| ContextT := W.t var;
            lookupb t ctx n := W.find n ctx;
            extendb t ctx n v := W.add n v ctx;
            removeb t ctx n := W.remove n ctx;
            empty := W.empty _ |}.
  End ctx_nd.
End FMapContextFun.

Module FMapContext (W : WS) := FMapContextFun W.E W.
Import Coq.FSets.FMapPositive.

Module PositiveContext := FMapContext PositiveMap.
Notation PositiveContext := PositiveContext.FMapContext.
Notation PositiveContext_nd := PositiveContext.FMapContext_nd.
Section language.
  Context {base_type_code : Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}.

  Local Notation flat_type := (flat_type base_type_code).
  Local Notation Expr := (@Expr base_type_code op).

  Fixpoint count_pairs (t : flat_type) : nat
    := match t with
       | Tbase _ => 1
       | Unit => 0
       | Prod A B => count_pairs A + count_pairs B
       end%nat.

  Section with_var.
    Context {var : base_type_code -> Type}
            (mkVar : forall t, var t).

    Local Notation exprf := (@exprf base_type_code op var).
    Local Notation expr := (@expr base_type_code op var).

    Section gen.
      Context (count_type_let : flat_type -> nat).
      Context (count_type_abs : flat_type -> nat).

      Fixpoint count_lets_genf {t} (e : exprf t) : nat
        := match e with
           | LetIn tx _ _ eC
             => count_type_let tx + @count_lets_genf _ (eC (SmartValf var mkVar tx))
           | Op _ _ _ e => @count_lets_genf _ e
           | Pair _ ex _ ey => @count_lets_genf _ ex + @count_lets_genf _ ey
           | _ => 0
           end.
      Definition count_lets_gen {t} (e : expr t) : nat
        := match e with
           | Abs tx _ f => count_type_abs tx + @count_lets_genf _ (f (SmartValf _ mkVar tx))
           end.
    End gen.
    Definition count_binders {t} (e : expr t) : nat
      := count_lets_gen count_pairs count_pairs e.
  End with_var.
  Definition CountBinders {t} (e : Expr t) : nat
    := count_binders (fun _ => tt) (e _).
End language.

Module Export Crypto_DOT_Compilers_DOT_Named_DOT_CountLets_WRAPPED.
Module Export CountLets.
Import Crypto.Compilers.Named.Syntax.
Section language.
  Context {base_type_code : Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}
          {Name : Type}.

  Local Notation flat_type := (flat_type base_type_code).

  Local Notation exprf := (@Named.exprf base_type_code op Name).
  Local Notation expr := (@Named.expr base_type_code op Name).

  Section gen.
    Context (count_type_let : flat_type -> nat).
    Context (count_type_abs : flat_type -> nat).

    Fixpoint count_lets_genf {t} (e : exprf t) : nat
      := match e with
         | LetIn tx _ _ _ eC
           => count_type_let tx + @count_lets_genf _ eC
         | Op _ _ _ e => @count_lets_genf _ e
         | Pair _ ex _ ey => @count_lets_genf _ ex + @count_lets_genf _ ey
         | _ => 0
         end.
    Definition count_lets_gen {t} (e : expr t) : nat
      := match e with
         | Abs tx _ _ f => count_type_abs tx + @count_lets_genf _ f
         end.
  End gen.
  Definition count_binders {t} (e : expr t) : nat
    := count_lets_gen count_pairs count_pairs e.
End language.

End CountLets.
Module Export Compilers.
Module Export Named.
Module Export CountLets.
Include Crypto_DOT_Compilers_DOT_Named_DOT_CountLets_WRAPPED.CountLets.
End CountLets.

End Named.

End Compilers.

Section language.
  Context {base_type_code : Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}.
  Definition DefaultNamesFor {t} (e : Expr base_type_code op t) : list positive
    := map BinPos.Pos.of_succ_nat (seq 0 (CountBinders e)).
End language.

Module Export Named.
  Section language.
    Context {base_type_code : Type}
            {op : flat_type base_type_code -> flat_type base_type_code -> Type}.
    Definition default_names_for {Name} {t} (e : Named.expr base_type_code op Name t) : list positive
      := map BinPos.Pos.of_succ_nat (seq 0 (Named.CountLets.count_binders e)).
  End language.
Module Export NameUtil.
Local Notation eta x := (fst x, snd x).

Section language.
  Context {base_type_code : Type}
          {Name : Type}.

  Section monad.
    Context (MName : Type) (force : MName -> option Name).
    Fixpoint split_mnames
             (t : flat_type base_type_code) (ls : list MName)
      : option (interp_flat_type (fun _ => Name) t) * list MName
      := match t return option (@interp_flat_type base_type_code (fun _ => Name) t) * _ with
         | Tbase _
           => match ls with
              | cons n ls'
                => match force n with
                   | Some n => (Some n, ls')
                   | None => (None, ls')
                   end
              | nil => (None, nil)
              end
         | Unit => (Some tt, ls)
         | Prod A B
           => let '(a, ls) := eta (@split_mnames A ls) in
              let '(b, ls) := eta (@split_mnames B ls) in
              (match a, b with
               | Some a', Some b' => Some (a', b')
               | _, _ => None
               end,
               ls)
         end.
  End monad.
  Definition split_onames := @split_mnames (option Name) (fun x => x).
End language.

End NameUtil.
Section language.
  Context (base_type_code : Type)
          (op : flat_type base_type_code -> flat_type base_type_code -> Type)
          (Name : Type).
  Local Notation exprf := (@exprf base_type_code op (fun _ => Name)).
  Local Notation expr := (@expr base_type_code op (fun _ => Name)).
  Local Notation nexprf := (@Named.exprf base_type_code op Name).
  Local Notation nexpr := (@Named.expr base_type_code op Name).

  Fixpoint ocompilef {t} (e : exprf t) (ls : list (option Name)) {struct e}
    : option (nexprf t)
    := match e in @Syntax.exprf _ _ _ t return option (nexprf t) with
       | TT => Some Named.TT
       | Var _ x => Some (Named.Var x)
       | Op _ _ op args => option_map (Named.Op op) (@ocompilef _ args ls)
       | LetIn tx ex _ eC
         => match @ocompilef _ ex nil, split_onames tx ls with
            | Some x, (Some n, ls')%core
              => option_map (fun C => Named.LetIn tx n x C) (@ocompilef _ (eC n) ls')
            | _, _ => None
            end
       | Pair _ ex _ ey => match @ocompilef _ ex nil, @ocompilef _ ey nil with
                           | Some x, Some y => Some (Named.Pair x y)
                           | _, _ => None
                           end
       end.

  Definition ocompile {t} (e : expr t) (ls : list (option Name))
    : option (nexpr t)
    := match e in @Syntax.expr _ _ _ t return option (nexpr t) with
       | Abs src _ f
         => match split_onames src ls with
            | (Some n, ls')%core
              => option_map (Named.Abs n) (@ocompilef _ (f n) ls')
            | _ => None
            end
       end.
  Definition compile {t} (e : expr t) (ls : list Name) := @ocompile t e (List.map (@Some _) ls).
End language.
Global Arguments compile {_ _ _ _} e ls.
Import Crypto.Compilers.Named.Syntax.

Local Notation eta x := (fst x, snd x).
Section language.
  Context (base_type_code : Type)
          (op : flat_type base_type_code -> flat_type base_type_code -> Type).
  Local Notation exprf := (@exprf base_type_code op).
  Local Notation expr := (@expr base_type_code op).

  Section internal.
    Context (InName OutName : Type)
            {InContext : Context InName (fun _ : base_type_code => OutName)}
            {ReverseContext : Context OutName (fun _ : base_type_code => InName)}
            (InName_beq : InName -> InName -> bool).

    Definition register_reassignf_step
               (register_reassignf : forall (ctxi : InContext) (ctxr : ReverseContext)
                                            {t} (e : exprf InName t) (new_names : list (option OutName)),
                   option (exprf OutName t))
               (ctxi : InContext) (ctxr : ReverseContext)
               {t} (e : exprf InName t) (new_names : list (option OutName))
      : option (exprf OutName t)
      := match e in Named.exprf _ _ _ t return option (exprf _ t) with
         | TT => Some TT
         | Var t' name => match lookupb t' ctxi name with
                          | Some new_name
                            => match lookupb t' ctxr new_name with
                               | Some name'
                                 => if InName_beq name name'
                                    then Some (Var new_name)
                                    else None
                               | None => None
                               end
                          | None => None
                          end
         | Op _ _ op args
           => option_map (Op op) (@register_reassignf ctxi ctxr _ args new_names)
         | LetIn tx n ex _ eC
           => let '(n', new_names') := eta (split_onames tx new_names) in
              match n', @register_reassignf ctxi ctxr _ ex nil with
              | Some n', Some x
                => let ctxi := extend ctxi n n' in
                   let ctxr := extend ctxr n' n in
                   option_map (LetIn tx n' x) (@register_reassignf ctxi ctxr _ eC new_names')
              | _, _
                => let ctxi := remove ctxi n in
                   @register_reassignf ctxi ctxr _ eC new_names'
              end
         | Pair _ ex _ ey
           => match @register_reassignf ctxi ctxr _ ex nil, @register_reassignf ctxi ctxr _ ey nil with
              | Some x, Some y
                => Some (Pair x y)
              | _, _ => None
              end
         end.
    Fixpoint register_reassignf ctxi ctxr {t} e new_names
      := @register_reassignf_step (@register_reassignf) ctxi ctxr t e new_names.

    Definition register_reassign (ctxi : InContext) (ctxr : ReverseContext)
             {t} (e : expr InName t) (new_names : list (option OutName))
      : option (expr OutName t)
      := match e in Named.expr _ _ _ t return option (expr _ t) with
         | Abs src _ n f
           => let '(n', new_names') := eta (split_onames src new_names) in
              match n' with
              | Some n'
                => let ctxi := extend (t:=src) ctxi n n' in
                   let ctxr := extend (t:=src) ctxr n' n in
                   option_map (Abs n') (register_reassignf ctxi ctxr f new_names')
              | None => None
              end
         end.
  End internal.
End language.

Global Arguments register_reassign {_ _ _ _ _ _} _ ctxi ctxr {t} e _.

Inductive liveness := live | dead.
Fixpoint merge_liveness (ls1 ls2 : list liveness) :=
  match ls1, ls2 with
  | cons x xs, cons y ys
    => cons match x, y with
            | live, _
            | _, live
              => live
            | dead, dead
              => dead
            end
            (@merge_liveness xs ys)
  | nil, ls
  | ls, nil
    => ls
  end.

Section language.
  Context (base_type_code : Type)
          (op : flat_type base_type_code -> flat_type base_type_code -> Type).
  Local Notation exprf := (@exprf base_type_code op).
  Local Notation expr := (@expr base_type_code op).

  Section internal.
    Context (Name : Type)
            (OutName : Type)
            {Context : Context Name (fun _ : base_type_code => list liveness)}.

    Definition compute_livenessf_step
               (compute_livenessf : forall (ctx : Context) {t} (e : exprf Name t) (prefix : list liveness), list liveness)
               (ctx : Context)
               {t} (e : exprf Name t) (prefix : list liveness)
      : list liveness
      := match e with
         | TT => prefix
         | Var t' name => match lookup (Tbase t') ctx name with
                          | Some ls => ls
                          | _ => nil
                          end
         | Op _ _ op args
           => @compute_livenessf ctx _ args prefix
         | LetIn tx n ex _ eC
           => let lx := @compute_livenessf ctx _ ex prefix in
              let lx := merge_liveness lx (prefix ++ repeat live (count_pairs tx)) in
              let ctx := extend ctx n (SmartValf _ (fun _ => lx) tx) in
              @compute_livenessf ctx _ eC (prefix ++ repeat dead (count_pairs tx))
         | Pair _ ex _ ey
           => merge_liveness (@compute_livenessf ctx _ ex prefix)
                             (@compute_livenessf ctx _ ey prefix)
         end.

    Fixpoint compute_livenessf ctx {t} e prefix
      := @compute_livenessf_step (@compute_livenessf) ctx t e prefix.

    Definition compute_liveness (ctx : Context)
             {t} (e : expr Name t) (prefix : list liveness)
      : list liveness
      := match e with
         | Abs src _ n f
           => let prefix := prefix ++ repeat live (count_pairs src) in
              let ctx := extend (t:=src) ctx n (SmartValf _ (fun _ => prefix) src) in
              compute_livenessf ctx f prefix
         end.

    Section insert_dead.
      Context (default_out : option OutName).

      Fixpoint insert_dead_names_gen (ls : list liveness) (lsn : list OutName)
        : list (option OutName)
        := match ls with
           | nil => nil
           | cons live xs
             => match lsn with
                | cons n lsn' => Some n :: @insert_dead_names_gen xs lsn'
                | nil => default_out :: @insert_dead_names_gen xs nil
                end
           | cons dead xs
             => None :: @insert_dead_names_gen xs lsn
           end.
      Definition insert_dead_names {t} (e : expr Name t)
        := insert_dead_names_gen (compute_liveness empty e nil).
    End insert_dead.
  End internal.
End language.
Global Arguments insert_dead_names {_ _ _ _ _} default_out {t} e lsn.
Module Export DeadCodeElimination.
Import Crypto.Util.LetIn.
Section language.
  Context (base_type_code : Type)
          (op : flat_type base_type_code -> flat_type base_type_code -> Type)
          (Name : Type)
          {base_type_code_beq : base_type_code -> base_type_code -> bool}
          (base_type_code_bl : forall t1 t2, base_type_code_beq t1 t2 = true -> t1 = t2)
          {Context : Context Name (fun _ : base_type_code => positive)}.
  Local Notation nexpr := (@Named.expr base_type_code op Name).

  Local Notation PContext var := (@PositiveContext base_type_code var base_type_code_beq base_type_code_bl).

  Definition EliminateDeadCode
             {t} (e : @Named.expr base_type_code op _ t) (ls : list Name)
    : option (nexpr t)
    := Let_In (insert_dead_names (Context:=PositiveContext_nd) None e ls)
              (fun names => register_reassign (InContext:=PContext _) (ReverseContext:=Context) Pos.eqb empty empty e names).
End language.

End DeadCodeElimination.
Import Crypto.Compilers.Z.Syntax.

Section language.
  Context {Name : Type}
          {Context : Context Name (fun _ : base_type => positive)}.

  Definition EliminateDeadCode {t} e ls
    := @EliminateDeadCode base_type op Name _ internal_base_type_dec_bl Context t e ls.
End language.

Section language.
  Context {base_type_code}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}
          {Name : Type}.

  Local Notation exprf := (@exprf base_type_code op Name).

  Fixpoint get_names_of_type {t} : interp_flat_type (fun _ : base_type_code => Name) t -> list Name
    := match t with
       | Tbase T => fun n => n::nil
       | Unit => fun _ => nil
       | Prod A B => fun ab : interp_flat_type _ A * interp_flat_type _ B
                     => @get_names_of_type _ (fst ab) ++ @get_names_of_type _ (snd ab)
       end.

  Fixpoint get_namesf {t} (e : exprf t) : list Name
    := match e with
       | TT => nil
       | Var _ x => x::nil
       | Op _ _ opc args => @get_namesf _ args
       | LetIn tx nx ex tC eC
         => get_names_of_type nx ++   @get_namesf _ eC
       | Pair _ ex _ ey
         => @get_namesf _ ex ++ @get_namesf _ ey
       end.
End language.
Import Crypto.Compilers.Syntax.
Import Crypto.Compilers.Z.Syntax.

Section named.
  Context {Name : Type}
          (name_beq : Name -> Name -> bool).
  Import Crypto.Compilers.Named.Syntax.
  Local Notation exprf := (@exprf base_type op Name).
  Local Notation expr := (@expr base_type op Name).

  Local Notation tZ := (Tbase TZ).
  Local Notation ADC bw c x y := (Op (@AddWithGetCarry bw TZ TZ TZ TZ TZ)
                                     (Pair (Pair (t1:=tZ) c (t2:=tZ) x) (t2:=tZ) y)).
  Local Notation ADD bw x y := (ADC bw (Op (OpConst 0) TT) x y).
  Local Notation ADX x y := (Op (@Add TZ TZ TZ) (Pair (t1:=tZ) x (t2:=tZ) y)).
  Local Infix "=Z?" := Z.eqb.
  Local Infix "=n?" := name_beq.

  Definition is_const_or_var {t} (v : exprf t)
    := match v with
       | Var _ _ => true
       | Op _ _ (OpConst _ _) TT => true
       | _ => false
       end.

  Fixpoint name_list_has_duplicate (ls : list Name) : bool
    := match ls with
       | nil => false
       | cons n ns
         => orb (name_list_has_duplicate ns)
                (List.fold_left orb (List.map (name_beq n) ns) false)
       end.

  Definition invertT t
    := option ((Name * Name * Z * exprf tZ * exprf tZ)
               * (Name * Name * Z * exprf tZ * Name)
               * (((Name * Name * Name) * exprf t)
                  + exprf t)).

  Definition invert_for_do_rewrite_step1 {t} (e : exprf t)
    : option ((Name * Name * Z * exprf tZ * exprf tZ) * exprf t)
    := match e in Named.exprf _ _ _ t return option ((Name * Name * Z * exprf tZ * exprf tZ) * exprf t) with
       | (nlet (a2, c1) : tZ * tZ := (ADD bw1 a b as ex0) in P0)
         => Some ((a2, c1, bw1, a, b), P0)
       | _ => None
       end%core%nexpr%bool.
  Definition invert_for_do_rewrite_step2 {t} (e : exprf t)
    : option ((Name * Name * Z * exprf tZ * Name) * exprf t)
    := match e in Named.exprf _ _ _ t return option ((Name * Name * Z * exprf tZ * Name) * exprf t) with
       | (nlet (s , c2) : tZ * tZ := (ADD bw2 c0 (Var TZ a2') as ex1) in P1)
         => Some ((s, c2, bw2, c0, a2'), P1)
       | _ => None
       end%core%nexpr%bool.
  Definition invert_for_do_rewrite_step3 {t} (e : exprf t)
    : option ((Name * Name * Name) * exprf t)
    := match e in Named.exprf _ _ _ t return option ((Name * Name * Name) * exprf t) with
       | (nlet c        : tZ      := (ADX (Var TZ c1') (Var TZ c2') as ex2) in P)
         => Some ((c, c1', c2'), P)
       | _ => None
       end%core%nexpr%bool.

  Definition invert_for_do_rewrite {t} (e : exprf t)
    : invertT t
    := match invert_for_do_rewrite_step1 e with
       | Some ((a2, c1, bw1, a, b), P0)
         => match invert_for_do_rewrite_step2 P0 with
            | Some ((s, c2, bw2, c0, a2'), P1)
              => match match invert_for_do_rewrite_step3 P1 with
                       | Some ((c, c1', c2'), P)
                         => if (((bw1 =Z? bw2) && (a2 =n? a2') && (c1 =n? c1') && (c2 =n? c2'))
                                  && (is_const_or_var c0 && is_const_or_var a && is_const_or_var b)
                                  && negb (name_list_has_duplicate (a2::c1::s::c2::c::nil ++ get_namesf c0 ++ get_namesf a ++ get_namesf b)%list))
                            then Some ((a2, c1, bw1, a, b),
                                       (s, c2, bw2, c0, a2'),
                                       inl ((c, c1', c2'), P))
                            else None
                       | None => None
                       end with
                 | Some v => Some v
                 | None => if (((bw1 =Z? bw2) && (a2 =n? a2'))
                                 && (is_const_or_var c0 && is_const_or_var a && is_const_or_var b)
                                 && negb (name_list_has_duplicate (a2::c1::s::c2::nil ++ get_namesf c0 ++ get_namesf a ++ get_namesf b)%list))
                           then Some ((a2, c1, bw1, a, b),
                                      (s, c2, bw2, c0, a2'),
                                      inr P1)
                           else None
                 end
            | None => None
            end
       | None => None
       end%core%nexpr%bool.

  Definition do_rewrite {t} (e : exprf t)
    : exprf t
    := match invert_for_do_rewrite e with
       | Some ((a2, c1, bw1, a, b),
               (s, c2, bw2, c0, a2'),
               inl ((c, c1', c2'), P))
         => (nlet (a2, c1) : tZ * tZ := ADD bw1 a b in
             nlet (s , c2) : tZ * tZ := ADD bw2 c0 (Var a2') in
             nlet c        : tZ      := ADX (Var c1') (Var c2') in
             nlet (s, c)   : tZ * tZ := ADC bw1 c0 a b in
             P)
       | Some ((a2, c1, bw1, a, b),
               (s, c2, bw2, c0, a2'),
               inr P)
         => (nlet (a2, c1) : tZ * tZ := ADD bw1 a b in
             nlet (s , c2) : tZ * tZ := ADD bw2 c0 (Var a2') in
             nlet s        : tZ      := (nlet (s, c1) : tZ * tZ := ADC bw1 c0 a b in Var s) in
             P)
       | None
         => e
       end%core%nexpr.

  Definition rewrite_exprf_prestep
             (rewrite_exprf : forall {t} (e : exprf t), exprf t)
             {t} (e : exprf t)
    : exprf t
    := match e in Named.exprf _ _ _ t return exprf t with
       | TT => TT
       | Var _ n => Var n
       | Op _ _ opc args
         => Op opc (@rewrite_exprf _ args)
       | (nlet nx := ex in eC)
         => (nlet nx := @rewrite_exprf _ ex in @rewrite_exprf _ eC)
       | Pair tx ex ty ey
         => Pair (@rewrite_exprf tx ex) (@rewrite_exprf ty ey)
       end%nexpr.

  Fixpoint rewrite_exprf {t} (e : exprf t) : exprf t
    := do_rewrite (@rewrite_exprf_prestep (@rewrite_exprf) t e).

  Definition rewrite_expr {t} (e : expr t) : expr t
    := match e in Named.expr _ _ _ t return expr t with
       | Abs _ _ n f => Abs n (rewrite_exprf f)
       end.
End named.
  Local Notation PContext var := (PositiveContext _ var _ internal_base_type_dec_bl).

  Definition RewriteAdc {t} (e : Expr t)
    : Expr t
    := let is_good e' := match option_map (wf_unit (Context:=PContext _) empty) e' with
                         | Some (Some trivial) => true
                         | _ => false
                         end in
       let interp_to_phoas := InterpToPHOAS (Context:=fun var => PContext var)
                                            (fun _ t => Op (OpConst 0%Z) TT) in
       let e' := compile (e _) (DefaultNamesFor e) in
       let e' := option_map (rewrite_expr Pos.eqb) e' in
       let good := is_good e' in
       let e' := match e' with
                 | Some e'
                   => let ls := Named.default_names_for e' in
                      match EliminateDeadCode (Context:=PContext _) e' ls with
                      | Some e'' => Some e''
                      | None => Some e'
                      end
                 | None => None
                 end in
       let good := good && is_good e' in
       if good
       then let e' := option_map interp_to_phoas e' in
            match e' with
            | Some e'
              => match t return Expr (Arrow (domain t) (codomain t)) -> Expr t with
                 | Arrow _ _ => fun x => x
                 end e'
            | None => e
            end
       else e.

  Lemma Wf_RewriteAdc {t} (e : Expr t) (Hwf : Wf e)
  : Wf (RewriteAdc e).
Admitted.

Hint Resolve Wf_RewriteAdc : wf.

  Lemma InterpRewriteAdc
        {t} (e : Expr t) (Hwf : Wf e)
  : forall x, Compilers.Syntax.Interp interp_op (RewriteAdc e) x = Compilers.Syntax.Interp interp_op e x.
Admitted.

Hint Rewrite @InterpRewriteAdc using solve_wf_side_condition : reflective_interp.
Class with_default (T : Type) (default : T) := defaulted : T.

Tactic Notation "transparent" "assert" "(" ident(name) ":" constr(type) ")" :=
  simple refine (let name := (_ : type) in _).

Ltac cache_term_with_type_by_gen ty abstract_tac id :=
  let id' := fresh id in
  let dummy := match goal with
               | _ => transparent assert ( id' : ty );
                      [ abstract_tac id'
                      | ]
               end in
  let ret := (eval cbv [id'] in id') in
  let dummy := match goal with
               | _ => clear id'
               end in
  ret.
Ltac cache_proof_with_type_by ty tac id :=
  cache_term_with_type_by_gen ty ltac:(fun id' => abstract tac using id') id.
Import Crypto.Compilers.Syntax.
Import Crypto.Util.Tactics.Head.
Import Crypto.Util.NatUtil.
Import Crypto.Util.Tactics.Not.

Section lang.
  Context {base_type}
          {op : flat_type base_type -> flat_type base_type -> Type}
          {interp_base_type : base_type -> Type}
          {interp_op : forall s d, op s d
                                   -> interp_flat_type interp_base_type s
                                   -> interp_flat_type interp_base_type d}.
  Local Notation Expr := (@Expr base_type op).
  Local Notation Interp := (@Interp base_type interp_base_type op interp_op).

  Definition packaged_expr_functionP A :=
    (fun F : Expr A -> Expr A
     => forall e',
         Wf e'
         -> Wf (F e')
            /\ forall v, Interp (F e') v = Interp e' v).
  Local Notation packaged_expr_function A :=
    (sig (packaged_expr_functionP A)).

  Definition id_package {A} : packaged_expr_function A
    := exist (packaged_expr_functionP A)
             id
             (fun e' Wfe' => conj Wfe' (fun v => eq_refl)).

  Inductive reified_transformation :=
  | base (idx : nat)
  | transform (idx : nat) (rest : reified_transformation)
  | cond (test : bool) (iftrue iffalse : reified_transformation).
  Fixpoint denote {A}
           (ls : list (packaged_expr_function A))
           (ls' : list { x : Expr A | Wf x })
           default
           (f : reified_transformation)
    := match f with
       | base idx => proj1_sig (List.nth_default default ls' idx)
       | transform idx rest
         => proj1_sig (List.nth_default id_package ls idx)
                      (denote ls ls' default rest)
       | cond test iftrue iffalse
         => if test
            then denote ls ls' default iftrue
            else denote ls ls' default iffalse
       end.
  Fixpoint reduce (f : reified_transformation) : reified_transformation
    := match f with
       | base idx => base idx
       | transform idx rest => reduce rest
       | cond test iftrue iffalse
         => match reduce iftrue, reduce iffalse with
            | base idx0 as t, base idx1 as f
              => if nat_beq idx0 idx1
                 then base idx0
                 else cond test t f
            | t, f => cond test t f
            end
       end.
  Lemma Wf_denote_iff_True A ctx es d f : Wf (@denote A ctx es d f) <-> True.
Admitted.
  Lemma Interp_denote_reduce A ctx es d f
    : forall v, Interp (@denote A ctx es d f) v = Interp (@denote A nil es d (reduce f)) v.
Admitted.
End lang.

Local Ltac find ctx f :=
  lazymatch ctx with
  | (exist _ f _ :: _)%list => constr:(0)
  | (_ :: ?ctx)%list
    => let v := find ctx f in
       constr:(S v)
  end.

Local Ltac reify_transformation interp_base_type interp_op ctx es T cont :=
  let reify_transformation := reify_transformation interp_base_type interp_op in
  let ExprA := type of T in
  let packageP := lazymatch type of T with
                 | @Expr ?base_type_code ?op ?A
                   => constr:(@packaged_expr_functionP base_type_code op interp_base_type interp_op A)
                 end in
  let es := lazymatch es with
            | tt => constr:(@nil { x : ExprA | Wf x })
            | _ => es
            end in
  let ctx := lazymatch ctx with
             | tt => constr:(@nil (sig packageP))
             | _ => ctx
             end in
  lazymatch T with
  | ?f ?e
    => let ctx := lazymatch ctx with
                  | context[exist _ f _] => ctx
                  | _ => let hf := head f in
                         let fId := fresh hf in
                         let rfPf :=
                             cache_proof_with_type_by
                               (packageP f)
                               ltac:(refine (fun e Hwf
                                             => (fun Hwf'
                                                 => conj Hwf' (fun v => _)) _);
                                     [ autorewrite with reflective_interp; reflexivity
                                     | auto with wf ])
                                      fId in
                         constr:(cons (exist packageP f rfPf)
                                      ctx)
                  end in
       reify_transformation
         ctx es e
         ltac:(fun ctx es re
               => let idx := find ctx f in
                  cont ctx es (transform idx re))
  | match ?b with true => ?t | false => ?f end
    => reify_transformation
         ctx es t
         ltac:(fun ctx es rt
               => reify_transformation
                    ctx es f
                    ltac:(fun ctx es rf
                          => reify_transformation
                               ctx es t
                               ltac:(fun ctx es rt
                                     => cont ctx es (cond b rt rf))))
  | _ => let es := lazymatch es with
                   | context[exist _ T _] => es
                   | _
                     => let Hwf := lazymatch goal with
                                   | [ Hwf : Wf T |- _ ] => Hwf

                                   | _
                                     => let Hwf := fresh "Hwf" in
                                        cache_proof_with_type_by
                                          (Wf T)
                                          ltac:(idtac; solve_wf_side_condition)
                                                 Hwf
                                   end in
                        constr:(cons (exist Wf T Hwf) es)
                   end in
         let idx := find es T in
         cont ctx es (base idx)
  end.
Ltac finish_rewrite_reflective_interp_cached :=
  rewrite ?Wf_denote_iff_True;
  cbv [reduce nat_beq];
  try (rewrite Interp_denote_reduce;
       cbv [reduce nat_beq];
       cbv [denote List.nth_default List.nth_error];
       cbn [proj1_sig]).
Ltac rewrite_reflective_interp_cached_then ctx es cont :=
  let e := match goal with
           | [ |- context[@Interp _ _ _ _ _ ?e] ]
             => let test := match goal with _ => not is_var e end in
                e
           end in
  lazymatch goal with
  | [ |- context[@Interp ?base_type ?interp_base_type ?op ?interp_op _ e] ]
    => reify_transformation
         interp_base_type interp_op ctx es e
         ltac:(fun ctx es r
               => lazymatch es with
                  | cons ?default _
                    => change e with (denote ctx es default r)
                  end;
                  finish_rewrite_reflective_interp_cached;
                  cont ctx es)
  end.
Ltac rewrite_reflective_interp_cached :=
  rewrite_reflective_interp_cached_then tt tt ltac:(fun _ _ => idtac).
Import Crypto.Compilers.Z.Syntax.

Record PipelineOptions :=
  {
    anf            : with_default bool false;
    adc_fusion     : with_default bool true;
  }.

Definition PostWfPreBoundsPipeline
           (opts : PipelineOptions)
           {t} (e : Expr t)
  : Expr t
  := let e := InlineConst e in
     let e := InlineConst (Linearize (SimplifyArith false e)) in
     let e := InlineConst (Linearize (SimplifyArith false e)) in
     let e := InlineConst (Linearize (SimplifyArith false e)) in
     let e := InlineConst (Linearize (SimplifyArith false e)) in
     let e := InlineConst (Linearize (SimplifyArith false e)) in
     let e := InlineConst (Linearize (SimplifyArith false e)) in
     let e := InlineConst (Linearize (SimplifyArith false e)) in
     let e := InlineConst (Linearize (SimplifyArith false e)) in
     let e := InlineConst (Linearize (SimplifyArith false e)) in
     let e := if opts.(anf) then InlineConst (ANormal e) else e in
     let e := if opts.(adc_fusion) then RewriteAdc e else e in
     let e := InlineConstAndOpp (Linearize (SimplifyArith true e)) in
     let e := if opts.(anf) then InlineConstAndOpp (ANormal e) else e in
     let e := InlineConstAndOpp (Linearize (SimplifyArith true e)) in
     let e := InlineConstAndOpp (Linearize (SimplifyArith true e)) in
     let e := InlineConstAndOpp (Linearize (SimplifyArith true e)) in
     let e := InlineConstAndOpp (Linearize (SimplifyArith true e)) in
     let e := InlineConstAndOpp (Linearize (SimplifyArith true e)) in
     let e := InlineConstAndOpp (Linearize (SimplifyArith true e)) in
     let e := InlineConstAndOpp (Linearize (SimplifyArith true e)) in
     let e := InlineConstAndOpp (Linearize (SimplifyArith true e)) in

     e.
Import Crypto.Util.Tactics.BreakMatch.

  Definition PostWfPreBoundsPipelineCorrect
             opts
             {t}
             (e : Expr t)
             (Hwf : Wf e)
             (e' := PostWfPreBoundsPipeline opts e)
    : (forall v, Interp e' v = Interp e v) /\ Wf e'.
  Proof using Type.

    unfold PostWfPreBoundsPipeline in *; subst e'.
    break_match_hyps.

    rewrite_reflective_interp_cached.
