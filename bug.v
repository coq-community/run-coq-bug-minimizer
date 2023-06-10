
(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "+implicit-core-hint-db,+implicits-in-term,+non-reversible-notation,+deprecated-intros-until-0,+deprecated-focus,+unused-intro-pattern,+variable-collision,+unexpected-implicit-declaration,+omega-is-deprecated,+deprecated-instantiate-syntax,+non-recursive,+undeclared-scope,+deprecated-hint-rewrite-without-locality,+deprecated-hint-without-locality,+deprecated-instance-without-locality,+deprecated-typeclasses-transparency-without-locality,unsupported-attributes" "-w" "-notation-overridden,-deprecated-hint-constr,-fragile-hint-constr,-native-compiler-disabled,-ambiguous-paths,-masking-absolute-name" "-w" "-deprecated-native-compiler-option" "-native-compiler" "ondemand" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/fiat_crypto/src" "Crypto" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/fiat_crypto/rupicola/bedrock2/deps/coqutil/src/coqutil" "coqutil" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/fiat_crypto/rupicola/src/Rupicola" "Rupicola" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/fiat_crypto/rupicola/bedrock2/bedrock2/src/bedrock2" "bedrock2" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/fiat_crypto/rupicola/bedrock2/bedrock2/src/bedrock2Examples" "bedrock2Examples" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/fiat_crypto/rupicola/bedrock2/compiler/src/compiler" "compiler" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/fiat_crypto/rupicola/bedrock2/deps/riscv-coq/src/riscv" "riscv" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Bignums" "Bignums" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Coqprime" "Coqprime" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Rewriter" "Rewriter" "-top" "Top.bug_01") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 1498 lines to 11 lines, then from 24 lines to 324 lines, then from 329 lines to 52 lines, then from 65 lines to 384 lines, then from 389 lines to 57 lines, then from 70 lines to 840 lines, then from 845 lines to 118 lines, then from 131 lines to 380 lines, then from 385 lines to 130 lines, then from 143 lines to 339 lines, then from 344 lines to 132 lines, then from 150 lines to 132 lines, then from 145 lines to 478 lines, then from 484 lines to 255 lines, then from 269 lines to 501 lines, then from 506 lines to 351 lines, then from 365 lines to 694 lines, then from 699 lines to 825 lines, then from 833 lines to 357 lines, then from 370 lines to 564 lines, then from 570 lines to 377 lines, then from 391 lines to 987 lines, then from 992 lines to 377 lines, then from 391 lines to 3948 lines, then from 3948 lines to 4401 lines, then from 4405 lines to 389 lines, then from 402 lines to 615 lines, then from 621 lines to 464 lines, then from 478 lines to 431 lines, then from 444 lines to 700 lines, then from 706 lines to 435 lines, then from 449 lines to 476 lines, then from 482 lines to 549 lines, then from 567 lines to 439 lines, then from 452 lines to 668 lines, then from 674 lines to 440 lines, then from 454 lines to 524 lines, then from 530 lines to 442 lines, then from 456 lines to 475 lines, then from 481 lines to 475 lines *)
(* coqc version 8.18+alpha compiled with OCaml 4.14.1
   coqtop version runner-vxtc-u6t-project-6138686-concurrent-0:/builds/coq/coq/_build/default,(HEAD detached at d7ce6d9) (d7ce6d9deac92848bd8420d857a18a96a87da88b)
   Modules that could not be inlined: Rewriter.Util.plugins.RewriterBuildRegistry
   Expected coqc runtime on this file: 7.475 sec *)
Require Coq.Init.Ltac.
Require Coq.Classes.Morphisms.
Require Rewriter.Util.GlobalSettings.
Require Rewriter.Util.FixCoqMistakes.
Require Rewriter.Util.Notations.
Require Ltac2.Init.
Require Coq.Lists.List.
Require Coq.Classes.RelationClasses.
Require Rewriter.Util.IffT.
Require Rewriter.Util.Isomorphism.
Require Rewriter.Util.HProp.
Require Rewriter.Util.Equality.
Require Rewriter.Util.PrimitiveProd.
Require Rewriter.Util.PrimitiveHList.
Require Rewriter.Util.InductiveHList.
Require Rewriter.Language.PreCommon.
Require Rewriter.Language.Pre.
Require Coq.Bool.Bool.
Require Rewriter.Util.Bool.
Require Coq.Logic.Eqdep_dec.
Require Coq.NArith.NArith.
Require Coq.Arith.Arith.
Require Coq.Numbers.Natural.Peano.NPeano.
Require Coq.Relations.Relation_Definitions.
Require Coq.micromega.Lia.
Require Rewriter.Util.NatUtil.
Require Coq.Lists.SetoidList.
Require Coq.Arith.Peano_dec.
Require Coq.ZArith.ZArith.
Require Coq.Numbers.BinNums.
Require Rewriter.Util.Pointed.
Require Rewriter.Util.plugins.RewriterBuildRegistry.
Ltac subst_evars :=
  repeat match goal with
         | [ e := ?E |- _ ] => is_evar E; subst e
         end.
Import Coq.Lists.List.
Import Coq.Classes.Morphisms.

  #[export] Instance Proper_filter_eq {A} : Proper ((eq ==> eq) ==> eq ==> eq) (@filter A).
Admitted.
Reserved Infix "<<" (at level 30, no associativity).
Reserved Infix ">>" (at level 30, no associativity).
Reserved Infix "&'" (at level 50).
Import Coq.ZArith.BinInt.

Infix ">>" := Z.shiftr : Z_scope.
Infix "<<" := Z.shiftl : Z_scope.
Infix "&'" := Z.land : Z_scope.

Class Decidable (P : Prop) := dec : {P} + {~P}.
Arguments dec _%type_scope {_}.
Notation DecidableRel R := (forall x y, Decidable (R x y)).
Global Instance dec_eq_Z : DecidableRel (@eq Z) | 10.
Admitted.
Local Open Scope Z_scope.

Module Export Z.

  Definition zselect (cond zero_case nonzero_case : Z) :=
    if cond =? 0 then zero_case else nonzero_case.

  Definition add_modulo x y modulus :=
    if (modulus <=? x + y) then (x + y) - modulus else (x + y).
Definition lnot_modulo (v : Z) (modulus : Z) : Z.
Admitted.
Definition bneg (v : Z) : Z.
Admitted.

  Definition cc_m s x := if dec (2 ^ (Z.log2 s) = s) then x >> (Z.log2 s - 1) else x / (s / 2).

  Definition rshi s hi lo n :=
       let k := Z.log2 s in
       if dec (2 ^ k = s)
       then ((lo + (hi << k)) >> n) &' (Z.ones k)
       else ((lo + hi * s) >> n) mod s.

  Definition truncating_shiftl bw x n := (x << n) mod (2^bw).
Definition add_with_carry (c : Z) (x y : Z) : Z.
Admitted.
Definition add_get_carry_full (bound : Z) (x y : Z) : Z * Z.
Admitted.
Definition add_with_get_carry_full (bound : Z) (c x y : Z) : Z * Z.
Admitted.
Definition sub_get_borrow_full (bound : Z) (x y : Z) : Z * Z.
Admitted.
Definition sub_with_get_borrow_full (bound : Z) (c x y : Z) : Z * Z.
Admitted.
Definition mul_split (s x y : Z) : Z * Z.
Admitted.
Definition mul_high (s x y : Z) : Z.
Admitted.
Definition ltz (x y : Z) : Z.
Admitted.
Definition combine_at_bitwidth (bitwidth lo hi : Z) : Z.
Admitted.

  Definition value_barrier (x : Z) := x.

  Fixpoint update_nth {T} n f (xs:list T) {struct n} :=
        match n with
        | O => match xs with
                                 | nil => nil
                                 | x'::xs' => f x'::xs'
                                 end
        | S n' =>  match xs with
                                 | nil => nil
                                 | x'::xs' => x'::update_nth n' f xs'
                                 end
  end.

Import Coq.Bool.Bool.

Notation reflect_rel P b := (forall x y, reflect (P x y) (b x y)).

Module Export Crypto_DOT_Util_DOT_ZRange_WRAPPED.
Module Export ZRange.

Declare Scope zrange_scope.

Record zrange := { lower : Z ; upper : Z }.
Bind Scope zrange_scope with zrange.
Scheme Minimality for zrange Sort Type.
Definition zrange_beq (x y : zrange) : bool.
Admitted.

Global Instance reflect_zrange_eq : reflect_rel (@eq zrange) zrange_beq | 10.
Admitted.

End ZRange.

End Crypto_DOT_Util_DOT_ZRange_WRAPPED.

Module Export ZRange.
Definition normalize (v : zrange) : zrange.
Admitted.
Definition opp (v : zrange) : zrange.
Admitted.
    Notation "- x" := (opp x) : zrange_scope.
Export Rewriter.Language.Pre.

Module Export ident.
  Section cast.
Definition is_more_pos_than_neg (r : zrange) (v : BinInt.Z) : bool.
Admitted.
Let cast_outside_of_range (r : zrange) (v : BinInt.Z) : BinInt.Z.
Admitted.

    Definition cast (r : zrange) (x : BinInt.Z)
      := let r := ZRange.normalize r in
         if (lower r <=? x) && (x <=? upper r)
         then x
         else if is_more_pos_than_neg r x
              then cast_outside_of_range r x
              else -cast_outside_of_range (-r) (-x).
    Definition cast2 (r : zrange * zrange) (x : BinInt.Z * BinInt.Z)
      := (cast (Datatypes.fst r) (Datatypes.fst x),
          cast (Datatypes.snd r) (Datatypes.snd x)).
  End cast.

  Section comment.
    Definition comment {A} (x : A) := tt.

    Definition comment_no_keep {A} (x : A) := tt.
  End comment.

  Module Export fancy.
    Module Export with_wordmax.
      Section with_wordmax.
        Context (log2wordmax : BinInt.Z).
Definition add (imm : Z) : Z * Z -> Z * Z.
Admitted.
Definition addc (imm : Z) : Z * Z * Z -> Z * Z.
Admitted.
Definition sub (imm : Z) : Z * Z -> Z * Z.
Admitted.
Definition subb (imm : Z) : Z * Z * Z -> Z * Z.
Admitted.
Definition mulll : Z * Z -> Z.
Admitted.
Definition mullh : Z * Z -> Z.
Admitted.
Definition mulhl : Z * Z -> Z.
Admitted.
Definition mulhh : Z * Z -> Z.
Admitted.
Definition selm : Z * Z * Z -> Z.
Admitted.
Definition rshi (n : Z) : Z * Z -> Z.
Admitted.
      End with_wordmax.
    End with_wordmax.

    Definition add : (Z * Z) * (Z * Z) -> Z * Z
      := Eval cbv [with_wordmax.add] in fun x => with_wordmax.add (fst (fst x)) (snd (fst x)) (snd x).
    Definition addc : (Z * Z) * (Z * Z * Z) -> Z * Z
      := Eval cbv [with_wordmax.addc] in fun x => with_wordmax.addc (fst (fst x)) (snd (fst x)) (snd x).
    Definition sub : (Z * Z) * (Z * Z) -> Z * Z
      := Eval cbv [with_wordmax.sub] in fun x => with_wordmax.sub (fst (fst x)) (snd (fst x)) (snd x).
    Definition subb : (Z * Z) * (Z * Z * Z) -> Z * Z
      := Eval cbv [with_wordmax.subb] in fun x => with_wordmax.subb (fst (fst x)) (snd (fst x)) (snd x).
    Definition mulll : Z * (Z * Z) -> Z
      := Eval cbv [with_wordmax.mulll] in fun x => with_wordmax.mulll (fst x) (snd x).
    Definition mullh : Z * (Z * Z) -> Z
      := Eval cbv [with_wordmax.mullh] in fun x => with_wordmax.mullh (fst x) (snd x).
    Definition mulhl : Z * (Z * Z) -> Z
      := Eval cbv [with_wordmax.mulhl] in fun x => with_wordmax.mulhl (fst x) (snd x).
    Definition mulhh : Z * (Z * Z) -> Z
      := Eval cbv [with_wordmax.mulhh] in fun x => with_wordmax.mulhh (fst x) (snd x).
    Definition selm : Z * (Z * Z * Z) -> Z
      := Eval cbv [with_wordmax.selm] in fun x => with_wordmax.selm (fst x) (snd x).
    Definition rshi : (Z * Z) * (Z * Z) -> Z
      := Eval cbv [with_wordmax.rshi] in fun x => with_wordmax.rshi (fst (fst x)) (snd (fst x)) (snd x).
Definition selc : Z * Z * Z -> Z.
Admitted.
Definition sell : Z * Z * Z -> Z.
Admitted.
Definition addm : Z * Z * Z -> Z.
Admitted.

Notation prod_rect_nodep := Rewriter.Util.Prod.prod_rect_nodep (only parsing).
Notation nat_rect_arrow_nodep := Rewriter.Util.NatUtil.nat_rect_arrow_nodep (only parsing).
Notation list_rect_arrow_nodep := Rewriter.Util.ListUtil.list_rect_arrow_nodep (only parsing).
Notation bool_rect_nodep := Rewriter.Util.Bool.bool_rect_nodep (only parsing).

Module Export Thunked.
  Notation bool_rect := Rewriter.Util.Bool.Thunked.bool_rect (only parsing).
  Notation list_rect := Rewriter.Util.ListUtil.Thunked.list_rect (only parsing).
  Notation list_case := Rewriter.Util.ListUtil.Thunked.list_case (only parsing).
  Notation nat_rect := Rewriter.Util.NatUtil.Thunked.nat_rect (only parsing).
  Notation option_rect := Rewriter.Util.Option.Thunked.option_rect (only parsing).
Definition var_like_idents : InductiveHList.hlist.
Admitted.
Definition base_type_list_named : InductiveHList.hlist.
exact ([with_name Z BinInt.Z
      ; with_name bool Datatypes.bool
      ; with_name nat Datatypes.nat
      ; with_name zrange ZRange.zrange
      ; with_name string String.string]%hlist).
Defined.
Definition all_ident_named_interped : InductiveHList.hlist.
exact ([with_name ident_Literal (@ident.literal)
      ; with_name ident_comment (@ident.comment)
      ; with_name ident_comment_no_keep (@ident.comment_no_keep)
      ; with_name ident_value_barrier (@Z.value_barrier)
      ; with_name ident_Nat_succ Nat.succ
      ; with_name ident_Nat_pred Nat.pred
      ; with_name ident_Nat_max Nat.max
      ; with_name ident_Nat_mul Nat.mul
      ; with_name ident_Nat_add Nat.add
      ; with_name ident_Nat_sub Nat.sub
      ; with_name ident_Nat_eqb Nat.eqb
      ; with_name ident_nil (@Datatypes.nil)
      ; with_name ident_cons (@Datatypes.cons)
      ; with_name ident_tt Datatypes.tt
      ; with_name ident_pair (@Datatypes.pair)
      ; with_name ident_fst (@Datatypes.fst)
      ; with_name ident_snd (@Datatypes.snd)
      ; with_name ident_prod_rect (@prod_rect_nodep)
      ; with_name ident_bool_rect (@Thunked.bool_rect)
      ; with_name ident_bool_rect_nodep (@bool_rect_nodep)
      ; with_name ident_nat_rect (@Thunked.nat_rect)
      ; with_name ident_eager_nat_rect (ident.eagerly (@Thunked.nat_rect))
      ; with_name ident_nat_rect_arrow (@nat_rect_arrow_nodep)
      ; with_name ident_eager_nat_rect_arrow (ident.eagerly (@nat_rect_arrow_nodep))
      ; with_name ident_list_rect (@Thunked.list_rect)
      ; with_name ident_eager_list_rect (ident.eagerly (@Thunked.list_rect))
      ; with_name ident_list_rect_arrow (@list_rect_arrow_nodep)
      ; with_name ident_eager_list_rect_arrow (ident.eagerly (@list_rect_arrow_nodep))
      ; with_name ident_list_case (@Thunked.list_case)
      ; with_name ident_List_length (@List.length)
      ; with_name ident_List_seq (@List.seq)
      ; with_name ident_List_firstn (@List.firstn)
      ; with_name ident_List_skipn (@List.skipn)
      ; with_name ident_List_repeat (@repeat)
      ; with_name ident_List_combine (@List.combine)
      ; with_name ident_List_map (@List.map)
      ; with_name ident_List_app (@List.app)
      ; with_name ident_List_rev (@List.rev)
      ; with_name ident_List_flat_map (@List.flat_map)
      ; with_name ident_List_partition (@List.partition)
      ; with_name ident_List_filter (@List.filter)
      ; with_name ident_List_fold_right (@List.fold_right)
      ; with_name ident_List_update_nth (@update_nth)
      ; with_name ident_List_nth_default (@nth_default)
      ; with_name ident_eager_List_nth_default (ident.eagerly (@nth_default))
      ; with_name ident_Z_add Z.add
      ; with_name ident_Z_mul Z.mul
      ; with_name ident_Z_pow Z.pow
      ; with_name ident_Z_sub Z.sub
      ; with_name ident_Z_opp Z.opp
      ; with_name ident_Z_div Z.div
      ; with_name ident_Z_modulo Z.modulo
      ; with_name ident_Z_eqb Z.eqb
      ; with_name ident_Z_leb Z.leb
      ; with_name ident_Z_ltb Z.ltb
      ; with_name ident_Z_geb Z.geb
      ; with_name ident_Z_gtb Z.gtb
      ; with_name ident_Z_log2 Z.log2
      ; with_name ident_Z_log2_up Z.log2_up
      ; with_name ident_Z_of_nat Z.of_nat
      ; with_name ident_Z_to_nat Z.to_nat
      ; with_name ident_Z_shiftr Z.shiftr
      ; with_name ident_Z_shiftl Z.shiftl
      ; with_name ident_Z_land Z.land
      ; with_name ident_Z_lor Z.lor
      ; with_name ident_Z_min Z.min
      ; with_name ident_Z_max Z.max
      ; with_name ident_Z_mul_split Z.mul_split
      ; with_name ident_Z_mul_high Z.mul_high
      ; with_name ident_Z_add_get_carry Z.add_get_carry_full
      ; with_name ident_Z_add_with_carry Z.add_with_carry
      ; with_name ident_Z_add_with_get_carry Z.add_with_get_carry_full
      ; with_name ident_Z_sub_get_borrow Z.sub_get_borrow_full
      ; with_name ident_Z_sub_with_get_borrow Z.sub_with_get_borrow_full
      ; with_name ident_Z_ltz Z.ltz
      ; with_name ident_Z_zselect Z.zselect
      ; with_name ident_Z_add_modulo Z.add_modulo
      ; with_name ident_Z_truncating_shiftl Z.truncating_shiftl
      ; with_name ident_Z_bneg Z.bneg
      ; with_name ident_Z_lnot_modulo Z.lnot_modulo
      ; with_name ident_Z_lxor Z.lxor
      ; with_name ident_Z_rshi Z.rshi
      ; with_name ident_Z_cc_m Z.cc_m
      ; with_name ident_Z_combine_at_bitwidth Z.combine_at_bitwidth
      ; with_name ident_Z_cast ident.cast
      ; with_name ident_Z_cast2 ident.cast2
      ; with_name ident_Some (@Datatypes.Some)
      ; with_name ident_None (@Datatypes.None)
      ; with_name ident_option_rect (@Thunked.option_rect)
      ; with_name ident_Build_zrange ZRange.Build_zrange
      ; with_name ident_zrange_rect (@ZRange.zrange_rect_nodep)
      ; with_name ident_fancy_add ident.fancy.add
      ; with_name ident_fancy_addc ident.fancy.addc
      ; with_name ident_fancy_sub ident.fancy.sub
      ; with_name ident_fancy_subb ident.fancy.subb
      ; with_name ident_fancy_mulll ident.fancy.mulll
      ; with_name ident_fancy_mullh ident.fancy.mullh
      ; with_name ident_fancy_mulhl ident.fancy.mulhl
      ; with_name ident_fancy_mulhh ident.fancy.mulhh
      ; with_name ident_fancy_rshi ident.fancy.rshi
      ; with_name ident_fancy_selc ident.fancy.selc
      ; with_name ident_fancy_selm ident.fancy.selm
      ; with_name ident_fancy_sell ident.fancy.sell
      ; with_name ident_fancy_addm ident.fancy.addm
     ]%hlist).
Defined.
Definition scraped_data : ScrapedData.t.
exact ({| ScrapedData.base_type_list_named := base_type_list_named
        ; ScrapedData.all_ident_named_interped := all_ident_named_interped |}).
Defined.

Declare ML Module "coq-rewriter.rewriter_build".

Module Export Compilers.
  Import IdentifiersBasicGenerate.Compilers.Basic.
  Rewriter Emit Inductives From Scraped
           {| ScrapedData.base_type_list_named := base_type_list_named ; ScrapedData.all_ident_named_interped := all_ident_named_interped |}
           As base ident raw_ident pattern_ident.

  Definition package : GoalType.package_with_args scraped_data var_like_idents base ident.
  Proof.
Tactic.make_package.
Defined.
Module Export APINotations.
Import Ltac2.Ltac2.
Module Export Compilers.
  Export Reify.Compilers.
  Import IdentifiersBasicGenerate.Compilers.Basic.Tactic.

  Definition exprInfo : Classes.ExprInfoT := Eval hnf in GoalType.exprInfo package.

  Global Existing Instances
         baseHasNat
         baseHasNatCorrect
         try_make_base_transport_cps_correct
         buildEagerIdent
         buildInterpEagerIdentCorrect
         toRestrictedIdent
         toFromRestrictedIdent
         buildInterpIdentCorrect
         invertIdent
         buildInvertIdentCorrect
         base_default
         exprInfo
  .
  Ltac2 mk_reify_base_type () :=
    let package := reify_package_of_package 'package in
    reify_base_type_via_reify_package package.
  Ltac2 mk_reify_type () :=
    let package := reify_package_of_package 'package in
    reify_type_via_reify_package package.
  Ltac2 mk_reify_ident_opt () :=
    let package := reify_package_of_package 'package in
    reify_ident_via_reify_package_opt package.
  Ltac2 reify_type (ty : constr) : constr := mk_reify_type () ty.
  #[deprecated(since="8.15",note="Use Ltac2 instead.")]
   Ltac reify_type term :=
    let f := ltac2:(term
                    |- Control.refine (fun () => reify_type (Option.get (Ltac1.to_constr term)))) in
    constr:(ltac:(f term)).

  Module Export base.

    Notation type := (@base.type base) (only parsing).
    Notation base_interp := Compilers.base_interp (only parsing).
    Notation interp := (base.interp Compilers.base_interp) (only parsing).
  End base.

  Ltac2 _Reify_rhs () : unit :=
    let reify_base_type := mk_reify_base_type () in
    let reify_ident_opt := mk_reify_ident_opt () in
    expr._Reify_rhs 'base.type 'ident reify_base_type reify_ident_opt '@base.interp '@ident_interp ().
  Ltac Reify_rhs _ :=
    ltac2:(_Reify_rhs ()).

  Module Import invert_expr.

    End invert_expr.

  End Compilers.

End APINotations.

    Notation Expr := (@expr.Expr base.type ident).

    Notation Interp := (@expr.Interp base.type ident base.interp (@ident_interp)).

    Notation reify_type t := (ltac:(let rt := reify_type t in exact rt)) (only parsing).
    Notation reify_type_of e := (reify_type ((fun t (_ : t) => t) _ e)) (only parsing).

Import Coq.Relations.Relation_Definitions.
Import Language.Wf.Compilers.

Fixpoint pointwise_equal {t} : relation (type.interp base.interp t)
  := match t with
     | type.base t => Logic.eq
     | type.arrow s d
       => fun (f g : type.interp base.interp s -> type.interp base.interp d)
          => forall x, pointwise_equal (f x) (g x)
     end.
Definition is_reification_of' {t} (e : Expr t) (v : type.interp base.interp t) : Prop.
exact (pointwise_equal (Interp e) v /\ Wf e).
Defined.

Notation is_reification_of rop op
  := (match @is_reification_of' (reify_type_of op) rop op with
      | T
        => ltac:(
             let T := (eval cbv [pointwise_equal is_reification_of' T] in T) in
             let T := (eval cbn [type.interp base.interp base.base_interp] in T) in
             exact T)
      end)
       (only parsing).

Ltac cache_reify _ :=
  split;
  [ intros;
    etransitivity;
    [
    | repeat match goal with |- _ = ?f' ?x => is_var x; apply (f_equal (fun f => f _)) end;
      Reify_rhs ();
      reflexivity ];
    subst_evars;
    reflexivity
  | prove_Wf () ].
Import Coq.ZArith.ZArith.

Derive reified_id_gen
       SuchThat (is_reification_of reified_id_gen (@id (list Z)))
       As reified_id_gen_correct.
Proof.
Time cache_reify ().
