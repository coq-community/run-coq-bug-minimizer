(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "-notation-overridden" "-w" "-deprecated-native-compiler-option" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/fiat_crypto_legacy/src" "Crypto" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/fiat_crypto_legacy/bbv/src/bbv" "bbv" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/fiat_crypto_legacy/coqprime/src/Coqprime" "Coqprime" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-I" "/github/workspace/builds/coq/coq-failing/_build_ci/fiat_crypto_legacy/coqprime/src" "-top" "Definition" "-native-compiler" "no") -*- *)
(* File reduced by coq-bug-finder from original input, then from 297 lines to 70 lines, then from 82 lines to 315 lines, then from 320 lines to 240 lines, then from 252 lines to 335 lines, then from 340 lines to 255 lines, then from 267 lines to 291 lines, then from 296 lines to 256 lines, then from 268 lines to 283 lines, then from 288 lines to 255 lines, then from 267 lines to 509 lines, then from 514 lines to 262 lines, then from 274 lines to 438 lines, then from 443 lines to 268 lines, then from 280 lines to 450 lines, then from 455 lines to 315 lines, then from 327 lines to 566 lines, then from 571 lines to 451 lines, then from 463 lines to 566 lines, then from 571 lines to 479 lines, then from 491 lines to 611 lines, then from 616 lines to 489 lines, then from 501 lines to 633 lines, then from 638 lines to 518 lines, then from 530 lines to 701 lines, then from 706 lines to 602 lines, then from 614 lines to 776 lines, then from 781 lines to 677 lines, then from 689 lines to 814 lines, then from 819 lines to 717 lines, then from 729 lines to 810 lines, then from 815 lines to 753 lines, then from 765 lines to 871 lines, then from 876 lines to 765 lines, then from 777 lines to 892 lines, then from 897 lines to 813 lines, then from 825 lines to 949 lines, then from 954 lines to 854 lines, then from 866 lines to 942 lines, then from 947 lines to 859 lines, then from 871 lines to 1007 lines, then from 1012 lines to 900 lines *)
(* coqc version 8.15+alpha compiled with OCaml 4.13.0
   coqtop version runner-ed2dce3a-project-6138686-concurrent-0:/builds/coq/coq/_build/default,(HEAD detached at dd7710d) (dd7710ddc27f4261696e0fa0a64ae693bcf5fc90)
   Expected coqc runtime on this file: 1.938 sec *)
Require Crypto.Compilers.LinearizeInterp.
Require Crypto.Compilers.Z.ArithmeticSimplifierInterp.
Require Crypto.Compilers.Z.InlineInterp.
Require Crypto.Compilers.Z.InlineWf.
Require Crypto.Compilers.LinearizeWf.
Require Crypto.Compilers.Z.ArithmeticSimplifierWf.
Require Crypto.Compilers.Named.InterpretToPHOAS.
Require Coq.FSets.FMapPositive.
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

Import Crypto.Compilers.Syntax.
Import Crypto.Compilers.SmartMap.
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
Import Coq.Numbers.BinNums.
Import Crypto.Compilers.Named.Syntax.
Import Crypto.Compilers.Syntax.

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
Import Crypto.Compilers.Named.Context.
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
Import Coq.PArith.BinPos.
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
Import Coq.ZArith.ZArith.
Import Crypto.Compilers.Syntax.
Import Crypto.Compilers.Z.Syntax.
Import Crypto.Util.Notations.

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
Import Crypto.Compilers.Named.InterpretToPHOAS.
Import Crypto.Compilers.Named.Wf.
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
Import Crypto.Compilers.Wf.

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
Import Crypto.Compilers.Linearize.
Import Crypto.Compilers.Z.ArithmeticSimplifier.
Import Crypto.Compilers.Z.Inline.

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
