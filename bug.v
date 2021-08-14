(* -*- mode: coq; coq-prog-args: ("-emacs" "-w" "-ssr-search-moved" "-w" "-deprecated-hint-without-locality" "-w" "-deprecated-instance-without-locality" "-w" "-deprecated-hint-rewrite-without-locality" "-w" "+deprecated-tactic-notation" "-w" "-notation-overridden,-redundant-canonical-projection" "-w" "-deprecated-native-compiler-option" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/src" "Perennial" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/stdpp/theories" "stdpp" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/iris/iris" "iris" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/iris/iris_deprecated" "iris.deprecated" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/iris/iris_staging" "iris.staging" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/iris/iris_heap_lang" "iris.heap_lang" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/coqutil/src/coqutil" "coqutil" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/Goose" "Goose" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/record-update/src" "RecordUpdate" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/coq-tactical/src" "Tactical" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/iris-named-props/src" "iris_named_props" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-top" "bug_01" "-native-compiler" "ondemand") -*- *)
(* File reduced by coq-bug-finder from original input, then from 738 lines to 49 lines, then from 288 lines to 475 lines, then from 479 lines to 110 lines, then from 349 lines to 841 lines, then from 844 lines to 110 lines, then from 346 lines to 1710 lines, then from 1712 lines to 183 lines, then from 411 lines to 1059 lines, then from 1063 lines to 452 lines, then from 485 lines to 254 lines, then from 480 lines to 590 lines, then from 593 lines to 254 lines, then from 478 lines to 716 lines, then from 720 lines to 268 lines, then from 491 lines to 2117 lines, then from 2118 lines to 547 lines, then from 656 lines to 441 lines, then from 655 lines to 1250 lines, then from 1253 lines to 543 lines, then from 752 lines to 918 lines, then from 921 lines to 604 lines, then from 799 lines to 905 lines, then from 909 lines to 649 lines, then from 842 lines to 949 lines, then from 953 lines to 857 lines *)
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
Require Coq.QArith.QArith_base.
Require Coq.QArith.Qcanon.
Require Coq.Sorting.Permutation.
Require Coq.Logic.EqdepFacts.
Require Coq.PArith.PArith.
Require Coq.NArith.NArith.
Require Coq.ZArith.ZArith.
Require Coq.Numbers.Natural.Peano.NPeano.
Require Coq.QArith.QArith.
Require Coq.Classes.Morphisms.
Require Coq.Classes.RelationClasses.
Require Coq.Lists.List.
Require Coq.Bool.Bool.
Require Coq.Setoids.Setoid.
Require Coq.Init.Peano.
Require Coq.Unicode.Utf8.
Require Coq.Program.Basics.
Require Coq.Program.Syntax.
Require stdpp.options.
Require stdpp.base.
Require stdpp.proof_irrel.
Require stdpp.decidable.
Require Coq.micromega.Lia.
Require stdpp.tactics.
Require stdpp.option.
Require stdpp.numbers.
Require stdpp.list.
Require stdpp.list_numbers.
Require stdpp.fin.
Require stdpp.countable.
Require stdpp.vector.
Require stdpp.finite.
Require Coq.ssr.ssreflect.
Require stdpp.orders.
Require Coq.Arith.Wf_nat.
Require stdpp.sets.
Require stdpp.relations.
Require stdpp.fin_sets.
Require stdpp.listset.
Require stdpp.lexico.
Require stdpp.prelude.
Require iris.prelude.options.
Require iris.prelude.prelude.
Require iris.algebra.ofe.
Require iris.algebra.monoid.
Require iris.algebra.cmra.
Require iris.algebra.proofmode_classes.
Require iris.algebra.frac.
Require iris.algebra.updates.
Require iris.algebra.local_updates.
Require iris.algebra.dfrac.
Require iris.algebra.agree.
Require stdpp.functions.
Require Coq.Strings.Ascii.
Require Coq.Strings.String.
Require stdpp.strings.
Require stdpp.pretty.
Require stdpp.infinite.
Require stdpp.fin_maps.
Require stdpp.fin_map_dom.
Require stdpp.mapset.
Require stdpp.pmap.
Require stdpp.propset.
Require stdpp.gmap.
Require stdpp.gmultiset.
Require iris.algebra.big_op.
Require iris.algebra.view.
Require iris.algebra.auth.
Require iris.algebra.lib.frac_auth.
Require stdpp.coPset.
Require iris.bi.notation.
Require iris.bi.interface.
Require iris.bi.derived_connectives.
Require iris.bi.weakestpre.
Require iris.proofmode.base.
Require stdpp.namespaces.
Require stdpp.hlist.
Require iris.bi.extensions.
Require iris.bi.derived_laws.
Require iris.bi.derived_laws_later.
Require iris.algebra.list.
Require iris.algebra.gmap.
Require iris.bi.big_op.
Require iris.bi.internal_eq.
Require iris.bi.plainly.
Require iris.bi.updates.
Require iris.bi.embedding.
Require iris.bi.bi.
Require stdpp.telescopes.
Require iris.bi.telescopes.
Require iris.proofmode.tokens.
Require iris.proofmode.sel_patterns.
Require iris.proofmode.intro_patterns.
Require iris.proofmode.spec_patterns.
Require iris.proofmode.environments.
Require iris.proofmode.ident_name.
Require iris.proofmode.modalities.
Require iris.proofmode.classes.
Require iris.proofmode.modality_instances.
Require iris.proofmode.coq_tactics.
Require iris.proofmode.reduction.
Require Ltac2.Init.
Require Ltac2.Int.
Require Ltac2.Message.
Require Ltac2.Control.
Require Ltac2.Bool.
Require Ltac2.Array.
Require Ltac2.Char.
Require Ltac2.Constr.
Require Ltac2.Std.
Require Ltac2.Env.
Require Ltac2.List.
Require Ltac2.Fresh.
Require Ltac2.Ident.
Require Ltac2.Ind.
Require Ltac2.Ltac1.
Require Ltac2.Option.
Require Ltac2.Pattern.
Require Ltac2.Printf.
Require Ltac2.String.
Require Ltac2.Notations.
Require Ltac2.Ltac2.
Require Coq.Init.Byte.
Require iris.proofmode.string_ident.
Require iris.proofmode.notation.
Require iris.proofmode.ltac_tactics.
Require stdpp.nat_cancel.
Require iris.proofmode.class_instances.
Require iris.proofmode.class_instances_later.
Require iris.proofmode.class_instances_updates.
Require iris.proofmode.class_instances_embedding.
Require iris.proofmode.class_instances_plainly.
Require iris.proofmode.class_instances_internal_eq.
Require iris.proofmode.frame_instances.
Require iris.proofmode.proofmode.
Require iris.proofmode.tactics.
Require iris.algebra.gset.
Require iris.algebra.coPset.
Require iris.algebra.functions.
Require iris.algebra.cofe_solver.
Require iris.base_logic.upred.
Require iris.base_logic.bi.
Require iris.base_logic.derived.
Require iris.base_logic.proofmode.
Require iris.algebra.csum.
Require iris.algebra.excl.
Require iris.algebra.lib.excl_auth.
Require iris.algebra.lib.gmap_view.
Require iris.base_logic.algebra.
Require iris.base_logic.base_logic.
Require iris.base_logic.lib.iprop.
Require iris.base_logic.lib.own.
Require Perennial.base_logic.lib.own.
Require iris.algebra.vector.
Require Perennial.base_logic.lib.iprop.
Require iris.bi.lib.fractional.
Require Perennial.algebra.auth_frac.
Require Perennial.algebra.mlist.
Require Perennial.base_logic.lib.wsat.
Require Perennial.base_logic.lib.fancy_updates.
Require Perennial.base_logic.lib.crash_token.
Require Perennial.base_logic.lib.ncfupd.
Require Perennial.program_logic.language.
Require Perennial.base_logic.lib.fupd_level.
Require Perennial.base_logic.lib.ae_invariants.
Require Perennial.base_logic.lib.invariants.
Require Perennial.base_logic.lib.fancy_updates2.
Require Perennial.program_logic.step_fupd_extra.
Require Perennial.program_logic.ae_invariants_mutable.
Require Perennial.base_logic.base_logic.
Require Perennial.Helpers.ipm.
Require Perennial.algebra.laterN.
Require Perennial.algebra.atleast.
Require Perennial.algebra.big_op.big_sepL.
Require Perennial.algebra.own_discrete.
Require Perennial.program_logic.ectx_language.
Require Perennial.program_logic.crash_weakestpre.
Require Perennial.program_logic.weakestpre.
Require Perennial.base_logic.lib.frac_coPset.
Require Coq.Arith.Min.
Require iris.algebra.reservation_map.
Require Perennial.algebra.na_heap.
Require stdpp.binders.
Require Perennial.Helpers.Transitions.
Module Export locations.
Export Perennial.algebra.blocks.

Record loc := Loc { loc_car : Z; loc_off : Z }.

Instance loc_eq_decision : EqDecision loc.
admit.
Defined.

 
Lemma loc_car_inj : forall x : loc, {| loc_car := loc_car x; loc_off := loc_off x |} = x.
admit.
Defined.
Instance loc_countable : Countable loc :=
  inj_countable' (λ x, (loc_car x, loc_off x)) (fun i => {| loc_car := i.1; loc_off := i.2 |}) loc_car_inj.

Program Instance locs_BlockAddr: BlockAddr loc :=
  {| addr_decode := λ l, (loc_car l, loc_off l);
     addr_encode := λ l, {| loc_car := fst l; loc_off := snd l |} |}.
Admit Obligations.

Definition loc_add (l : loc) (off : Z) : loc := addr_plus_off l off.

Notation "l +ₗ off" :=
  (loc_add l off) (at level 50, left associativity) : stdpp_scope.

End locations.
Module Export Interface.
Local Open Scope Z_scope.

Module Export word.
  Class word {width : Z} := {
    rep : Type;

    unsigned : rep -> Z;
    signed : rep -> Z;
    of_Z : Z -> rep;

    add : rep -> rep -> rep;
    sub : rep -> rep -> rep;
    opp : rep -> rep;

    or : rep -> rep -> rep;
    and : rep -> rep -> rep;
    xor : rep -> rep -> rep;
    not : rep -> rep;
    ndn : rep -> rep -> rep;

    mul : rep -> rep -> rep;
    mulhss : rep -> rep -> rep;
    mulhsu : rep -> rep -> rep;
    mulhuu : rep -> rep -> rep;

    divu : rep -> rep -> rep;
    divs : rep -> rep -> rep;
    modu : rep -> rep -> rep;
    mods : rep -> rep -> rep;

    slu : rep -> rep -> rep;
    sru : rep -> rep -> rep;
    srs : rep -> rep -> rep;

    eqb : rep -> rep -> bool;
    ltu : rep -> rep -> bool;
    lts : rep -> rep -> bool;

    gtu x y := ltu y x;
    gts x y := lts y x;

    swrap z := (z + 2^(width-1)) mod 2^width - 2^(width-1);

    sextend: Z -> rep -> rep;
  }.
  Arguments word : clear implicits.
End word.
Global Coercion word.rep : word >-> Sortclass.
Module Export Naive.

Definition minimize_eq_proof{A: Type}(eq_dec: forall (x y: A), {x = y} + {x <> y}){x y: A}    (pf: x = y): x = y :=
  match eq_dec x y with
  | left p => p
  | right n => match n pf: False with end
  end.

Section WithWidth.
  Context {width : Z}.
  Let wrap_value z := z mod (2^width).
  Let swrap_value z := wrap_value (z + 2 ^ (width - 1)) - 2 ^ (width - 1).
  Record rep := mk { unsigned : Z ; _unsigned_in_range : wrap_value unsigned = unsigned }.

  Definition wrap (z:Z) : rep :=
    mk (wrap_value z) (minimize_eq_proof Z.eq_dec (Zdiv.Zmod_mod z _)).
  Definition signed w := swrap_value (unsigned w).

  Definition word : word.word width := {|
    word.rep := rep;
    word.unsigned := unsigned;
    word.signed := signed;
    of_Z := wrap;

    add x y := wrap (Z.add (unsigned x) (unsigned y));
    sub x y := wrap (Z.sub (unsigned x) (unsigned y));
    opp x := wrap (Z.opp (unsigned x));

    or x y := wrap (Z.lor (unsigned x) (unsigned y));
    and x y := wrap (Z.land (unsigned x) (unsigned y));
    xor x y := wrap (Z.lxor (unsigned x) (unsigned y));
    not x := wrap (Z.lnot (unsigned x));
    ndn x y := wrap (Z.ldiff (unsigned x) (unsigned y));

    mul x y := wrap (Z.mul (unsigned x) (unsigned y));
    mulhss x y := wrap (Z.mul (signed x) (signed y) / 2^width);
    mulhsu x y := wrap (Z.mul (signed x) (unsigned y) / 2^width);
    mulhuu x y := wrap (Z.mul (unsigned x) (unsigned y) / 2^width);

    divu x y := wrap (Z.div (unsigned x) (unsigned y));
    divs x y := wrap (Z.quot (signed x) (signed y));
    modu x y := wrap (Z.modulo (unsigned x) (unsigned y));
    mods x y := wrap (Z.rem (signed x) (signed y));

    slu x y := wrap (Z.shiftl (unsigned x) (unsigned y));
    sru x y := wrap (Z.shiftr (unsigned x) (unsigned y));
    srs x y := wrap (Z.shiftr (signed x) (unsigned y));

    eqb x y := Z.eqb (unsigned x) (unsigned y);
    ltu x y := Z.ltb (unsigned x) (unsigned y);
    lts x y := Z.ltb (signed x) (signed y);

    sextend oldwidth z := wrap ((unsigned z + 2^(oldwidth-1)) mod 2^oldwidth - 2^(oldwidth-1));
  |}.
End WithWidth.
Arguments word : clear implicits.
Notation word8 := (word 8%Z).
Notation word32 := (word 32%Z).
Notation word64 := (word 64%Z).

Record u64_rep := Word64 { u64_car : Naive.word64 }.
Record u32_rep := Word32 { u32_car : Naive.word32 }.
Record u8_rep := Word8 { u8_car : Naive.word8 }.
  Import Interface.word.
  Notation "'lift1' f" := (fun w => Word64 (f w.(u64_car))) (at level 10, only parsing).
  Notation "'lift2' f" := (fun w1 w2 => Word64 (f w1.(u64_car) w2.(u64_car))) (at level 10, only parsing).
  Instance u64 : word 64 :=
    {|
      rep := u64_rep;
      unsigned w := unsigned w.(u64_car);
      signed w := signed (w.(u64_car));
      of_Z z := Word64 (of_Z z);
      add := lift2 add;
      sub := lift2 sub;
      opp := lift1 opp;
      or := lift2 or;
      and := lift2 and;
      xor := lift2 xor;
      not := lift1 not;
      ndn := lift2 ndn;
      mul := lift2 mul;
      mulhss := lift2 mulhss;
      mulhsu := lift2 mulhsu;
      mulhuu := lift2 mulhuu;
      divu := lift2 divu;
      divs := lift2 divs;
      modu := lift2 modu;
      mods := lift2 mods;
      slu := lift2 slu;
      sru := lift2 sru;
      srs := lift2 srs;
      eqb w1 w2 := eqb w1.(u64_car) w2.(u64_car);
      ltu w1 w2 := ltu w1.(u64_car) w2.(u64_car);
      lts w1 w2 := lts w1.(u64_car) w2.(u64_car);
      sextend width' := lift1 (sextend width');
    |}.
  Notation "'lift1' f" := (fun w => Word32 (f w.(u32_car))) (at level 10, only parsing).
  Notation "'lift2' f" := (fun w1 w2 => Word32 (f w1.(u32_car) w2.(u32_car))) (at level 10, only parsing).
  Instance u32 : word 32 :=
    {|
      rep := u32_rep;
      unsigned w := unsigned w.(u32_car);
      signed w := signed (w.(u32_car));
      of_Z z := Word32 (of_Z z);
      add := lift2 add;
      sub := lift2 sub;
      opp := lift1 opp;
      or := lift2 or;
      and := lift2 and;
      xor := lift2 xor;
      not := lift1 not;
      ndn := lift2 ndn;
      mul := lift2 mul;
      mulhss := lift2 mulhss;
      mulhsu := lift2 mulhsu;
      mulhuu := lift2 mulhuu;
      divu := lift2 divu;
      divs := lift2 divs;
      modu := lift2 modu;
      mods := lift2 mods;
      slu := lift2 slu;
      sru := lift2 sru;
      srs := lift2 srs;
      eqb w1 w2 := eqb w1.(u32_car) w2.(u32_car);
      ltu w1 w2 := ltu w1.(u32_car) w2.(u32_car);
      lts w1 w2 := lts w1.(u32_car) w2.(u32_car);
      sextend width' := lift1 (sextend width');
    |}.
  Notation "'lift1' f" := (fun w => Word8 (f w.(u8_car))) (at level 10, only parsing).
  Notation "'lift2' f" := (fun w1 w2 => Word8 (f w1.(u8_car) w2.(u8_car))) (at level 10, only parsing).
  Instance u8 : word 8 :=
    {|
      rep := u8_rep;
      unsigned w := unsigned w.(u8_car);
      signed w := signed (w.(u8_car));
      of_Z z := Word8 (of_Z z);
      add := lift2 add;
      sub := lift2 sub;
      opp := lift1 opp;
      or := lift2 or;
      and := lift2 and;
      xor := lift2 xor;
      not := lift1 not;
      ndn := lift2 ndn;
      mul := lift2 mul;
      mulhss := lift2 mulhss;
      mulhsu := lift2 mulhsu;
      mulhuu := lift2 mulhuu;
      divu := lift2 divu;
      divs := lift2 divs;
      modu := lift2 modu;
      mods := lift2 mods;
      slu := lift2 slu;
      sru := lift2 sru;
      srs := lift2 srs;
      eqb w1 w2 := eqb w1.(u8_car) w2.(u8_car);
      ltu w1 w2 := ltu w1.(u8_car) w2.(u8_car);
      lts w1 w2 := lts w1.(u8_car) w2.(u8_car);
      sextend width' := lift1 (sextend width');
    |}.
Module Export Perennial_DOT_goose_lang_DOT_lang_WRAPPED.
Module Export lang.
Export stdpp.binders.
Import Perennial.Helpers.Transitions.

Module Export goose_lang.

Definition proph_id := positive.

Class ffi_syntax :=
  mkExtOp {
      ffi_opcode: Set;
      ffi_opcode_eq_dec :> EqDecision ffi_opcode;
      ffi_opcode_countable :> Countable ffi_opcode;
      ffi_val: Type;
      ffi_val_eq_dec :> EqDecision ffi_val;
      ffi_val_countable :> Countable ffi_val;
    }.

Class ffi_model :=
  mkFfiModel {
      ffi_state : Type;
      ffi_global_state : Type;
      ffi_state_inhabited :> Inhabited ffi_state;
      ffi_global_state_inhabited :> Inhabited ffi_global_state;
    }.

Section external.

Context {ext : ffi_syntax}.

Inductive base_lit : Type :=
  | LitInt (n : u64) | LitInt32 (n : u32) | LitBool (b : bool) | LitByte (n : u8)
  | LitString (s : string) | LitUnit | LitPoison
  | LitLoc (l : loc) | LitProphecy (p: proph_id).
Inductive un_op : Set :=

  | NegOp | MinusUnOp | ToUInt64Op | ToUInt32Op | ToUInt8Op | ToStringOp.
Inductive bin_op : Set :=
  | PlusOp | MinusOp | MultOp | QuotOp | RemOp
  | AndOp | OrOp | XorOp
  | ShiftLOp | ShiftROp
  | LeOp | LtOp | EqOp
  | OffsetOp (k:Z)
.

Inductive prim_op0 :=

| PanicOp (s: string)

| ArbitraryIntOp
.

Inductive prim_op1 :=
  | PrepareWriteOp

  | StartReadOp
  | FinishReadOp

  | LoadOp
  | InputOp
  | OutputOp
.

Inductive prim_op2 :=
 | AllocNOp
 | FinishStoreOp
.

Inductive arity : Set := args0 | args1 | args2.
Definition prim_op (ar:arity) : Set :=
  match ar with
  | args0 => prim_op0
  | args1 => prim_op1
  | args2 => prim_op2
  end.

Inductive expr :=

  | Val (v : val)

  | Var (x : string)
  | Rec (f x : binder) (e : expr)
  | App (e1 e2 : expr)

  | UnOp (op : un_op) (e : expr)
  | BinOp (op : bin_op) (e1 e2 : expr)
  | If (e0 e1 e2 : expr)

  | Pair (e1 e2 : expr)
  | Fst (e : expr)
  | Snd (e : expr)

  | InjL (e : expr)
  | InjR (e : expr)
  | Case (e0 : expr) (e1 : expr) (e2 : expr)

  | Fork (e : expr)
  | Atomically (e: expr) (e : expr)

  | Primitive0 (op: prim_op args0)
  | Primitive1 (op: prim_op args1) (e : expr)
  | Primitive2 (op: prim_op args2) (e1 e2 : expr)

  | CmpXchg (e0 : expr) (e1 : expr) (e2 : expr)

  | ExternalOp (op: ffi_opcode) (e: expr)

  | NewProph
  | Resolve (e0 : expr) (e1 : expr) (e2 : expr)
with val :=
  | LitV (l : base_lit)
  | RecV (f x : binder) (e : expr)
  | PairV (v1 v2 : val)
  | InjLV (v : val)
  | InjRV (v : val)

  | ExtV (ev : ffi_val)
.

Fixpoint flatten_struct (v: val) : list val :=
  match v with
  | PairV v1 v2 => flatten_struct v1 ++ flatten_struct v2
  | LitV LitUnit => []
  | _ => [v]
  end.

Context {ffi : ffi_model}.

Inductive naMode :=
  | Writing
  | Reading (n:nat).

Notation nonAtomic T := (naMode * T)%type.

Inductive event :=
  | In_ev (sel v:base_lit)
  | Out_ev (v:base_lit)
  | Crash_ev
.

Definition Trace := list event.

Definition Oracle := Trace -> forall (sel:u64), u64.

Record state : Type := {
  heap: gmap loc (nonAtomic val);
  world: ffi_state;
  trace: Trace;
  oracle: Oracle;
}.
Definition global_state : Type := ffi_global_state.

Class ffi_semantics :=
  {
    ffi_step : ffi_opcode -> val -> transition (state*global_state) val;
    ffi_crash_step : ffi_state -> ffi_state -> Prop;
  }.

End external.
End goose_lang.

End lang.
Module Export Perennial.
Module Export goose_lang.
Module Export lang.
Include Perennial_DOT_goose_lang_DOT_lang_WRAPPED.lang.
End lang.
Module Export Perennial_DOT_goose_lang_DOT_notation_WRAPPED.
Module Export notation.
Export Perennial.goose_lang.lang.
Notation "( e1 , e2 , .. , en )" := (PairV .. (PairV e1 e2) .. en) : val_scope.

End notation.
Module Export Perennial.
Module Export goose_lang.
Module Export notation.
Include Perennial_DOT_goose_lang_DOT_notation_WRAPPED.notation.
End notation.

End goose_lang.

End Perennial.
Notation MapNilV def := (InjLV def).

Module Export typing.

Class val_types :=
  { ext_tys: Type; }.

Section val_types.
  Context {val_tys: val_types}.
  Inductive base_ty :=
  | uint64BT
  | uint32BT
  | byteBT
  | boolBT
  | unitBT
  | stringBT.

  Inductive ty :=
  | baseT (t:base_ty)
  | prodT (t1 t2: ty)
  | listT (t1: ty)
  | sumT (t1 t2: ty)
  | arrowT (t1 t2: ty)
  | arrayT (t: ty)
  | structRefT (ts: list ty)

  | mapValT (vt: ty)
  | extT (x: ext_tys)
  .
  Definition uint64T := baseT uint64BT.
  Definition uint32T := baseT uint32BT.
  Definition byteT   := baseT byteBT.
  Definition boolT   := baseT boolBT.
  Definition unitT   := baseT unitBT.
  Definition stringT := baseT stringBT.

End val_types.

Class ext_types (ext:ffi_syntax) :=
  { val_tys :> val_types;

    get_ext_tys: val -> ty * ty -> Prop;
  }.

Section goose_lang.
  Context `{ext_ty: ext_types}.

  Fixpoint has_zero (t:ty): Prop :=
    match t with
    | baseT _ => True

    | mapValT t => False
    | prodT t1 t2 => has_zero t1 ∧ has_zero t2
    | listT t => has_zero t
    | sumT t1 t2 => has_zero t1
    | arrowT _ t2 => has_zero t2
    | arrayT _ => True
    | structRefT _ => True
    | extT _ => False
    end.

  Fixpoint ty_size (t:ty) : Z :=
    match t with
    | prodT t1 t2 => ty_size t1 + ty_size t2
    | extT x => 1
    | baseT unitBT => 0
    | _ => 1
    end.

End goose_lang.
Hint Extern 1 (has_zero _) => (compute; intuition idtac) : val_ty.

End typing.
Import iris.algebra.lib.frac_auth.
Import iris.algebra.numbers.
Import iris.algebra.excl.
Export Perennial.program_logic.weakestpre.
Export Perennial.base_logic.lib.frac_coPset.
Export Perennial.algebra.na_heap.
Export Perennial.goose_lang.notation.

Class ffi_interp (ffi: ffi_model) :=
  { ffiG: gFunctors -> Set;
    ffi_local_names : Set;
    ffi_global_names : Set;
    ffi_get_local_names : ∀ Σ, ffiG Σ → ffi_local_names;
    ffi_get_global_names : ∀ Σ, ffiG Σ → ffi_global_names;
    ffi_update_local : ∀ Σ, ffiG Σ → ffi_local_names → ffiG Σ;
    ffi_update_get_local: ∀ Σ hF names, ffi_get_local_names Σ (ffi_update_local _ hF names) = names;
    ffi_update_get_global: ∀ Σ hF names, ffi_get_global_names Σ (ffi_update_local _ hF names) =
                                         ffi_get_global_names Σ hF;
    ffi_get_update: ∀ Σ hF, ffi_update_local Σ hF (ffi_get_local_names _ hF) = hF;
    ffi_update_update: ∀ Σ hF names1 names2, ffi_update_local Σ (ffi_update_local Σ hF names1) names2
                                     = ffi_update_local Σ hF names2;
    ffi_ctx: ∀ `{ffiG Σ}, ffi_state -> iProp Σ;
    ffi_global_ctx: ∀ `{ffiG Σ}, ffi_global_state -> iProp Σ;
    ffi_global_ctx_nolocal : ∀ Σ hF names,
        @ffi_global_ctx Σ (ffi_update_local Σ hF names) = @ffi_global_ctx Σ hF;
    ffi_local_start: ∀ `{ffiG Σ}, ffi_state -> ffi_global_state -> iProp Σ;
    ffi_restart: ∀ `{ffiG Σ}, ffi_state -> iProp Σ;
    ffi_crash_rel: ∀ Σ, ffiG Σ → ffi_state → ffiG Σ → ffi_state → iProp Σ;
    ffi_crash_rel_pers: ∀ Σ (Hold Hnew: ffiG Σ) σ σ', Persistent (ffi_crash_rel Σ Hold σ Hnew σ');
  }.

Section goose_lang.
Context `{ffi_sem: ffi_semantics}.
Context `{!ffi_interp ffi}.

Definition traceO := leibnizO (list event).
Definition OracleO := leibnizO (Oracle).

Record tr_names := {
  trace_name : gname;
  oracle_name : gname;
}.

Class traceG (Σ: gFunctors) := {
  trace_inG :> inG Σ (authR (optionUR (exclR traceO)));
  oracle_inG :> inG Σ (authR (optionUR (exclR OracleO)));
  trace_tr_names : tr_names;
}.

Record cr_names := {
  credit_name : gname;
  coPset_name : gname;
}.

Class creditGS (Σ: gFunctors) := {
  credit_inG :> inG Σ (authR natUR);
  frac_coPset_inG :> inG Σ (frac_coPsetR);
  credit_cr_names : cr_names;
}.

Class heapGS Σ := HeapGS {
  heapG_invG : invGS Σ;
  heapG_crashG : crashG Σ;
  heapG_ffiG : ffiG Σ;
  heapG_na_heapG :> na_heapG loc val Σ;
  heapG_traceG :> traceG Σ;
  heapG_creditG :> creditGS Σ;
}.

End goose_lang.

Section goose_lang.
  Context {ext} {ext_ty: ext_types ext}.

  Inductive lit_ty : base_lit -> ty -> Prop :=
  | int_ty x : lit_ty (LitInt x) uint64T
  | int32_ty x : lit_ty (LitInt32 x) uint32T
  | int8_ty x : lit_ty (LitByte x) byteT
  | bool_ty x : lit_ty (LitBool x) boolT
  | string_ty x : lit_ty (LitString x) stringT
  | unit_ty : lit_ty LitUnit unitT
  | loc_array_ty x t : lit_ty (LitLoc x) (arrayT t)
  | loc_struct_ty x ts : lit_ty (LitLoc x) (structRefT ts)
  .

  Inductive val_ty : val -> ty -> Prop :=
  | base_ty l t : lit_ty l t -> val_ty (LitV l) t
  | val_ty_pair v1 t1 v2 t2 : val_ty v1 t1 ->
                              val_ty v2 t2 ->
                              val_ty (PairV v1 v2) (prodT t1 t2)
  | nil_ty t : val_ty (InjLV (LitV LitUnit)) (listT t)
  | sum_ty_l v1 t1 t2 : val_ty v1 t1 ->
                        val_ty (InjLV v1) (sumT t1 t2)
  | sum_ty_r v2 t1 t2 : val_ty v2 t2 ->
                        val_ty (InjRV v2) (sumT t1 t2)
  | map_def_ty v t : val_ty v t ->
                     val_ty (MapNilV v) (mapValT t)
  | map_cons_ty k v mv' t : val_ty mv' (mapValT t) ->
                            val_ty k uint64T ->
                            val_ty v t ->
                            val_ty (InjRV (k, v, mv')%V) (mapValT t)
  | rec_ty f x e t1 t2 : val_ty (RecV f x e) (arrowT t1 t2)
  | ext_val_ty x T : val_ty (ExtV x) (extT T)
  .

  Theorem val_ty_len {v t} :
    val_ty v t ->
    length (flatten_struct v) = Z.to_nat (ty_size t).
admit.
Defined.

  Theorem flatten_struct_inj v1 v2 t :
    val_ty v1 t ->
    val_ty v2 t ->
    flatten_struct v1 = flatten_struct v2 ->
    v1 = v2.
admit.
Defined.

End goose_lang.

Ltac val_ty :=
  solve [ repeat lazymatch goal with
                 | |- val_ty _ _ =>
                   first [ by auto with val_ty nocore | constructor ]
                 | |- lit_ty _ _ => constructor
                 | _ => fail 3 "not a val_ty goal"
                 end ].

Hint Extern 2 (val_ty _ _) => val_ty : core.
  Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
  Context {ext_ty: ext_types ext}.

  Definition struct_mapsto_def l (q:Qp) (t:ty) (v: val): iProp Σ :=
    (([∗ list] j↦vj ∈ flatten_struct v, (l +ₗ j) ↦{q} vj) ∗ ⌜val_ty v t⌝)%I.
  Definition struct_mapsto_aux : seal (@struct_mapsto_def).
admit.
Defined.
  Definition struct_mapsto := struct_mapsto_aux.(unseal).

  Notation "l ↦[ t ]{ q } v" := (struct_mapsto l q t v%V)
                                   (at level 20, q at level 50, t at level 50,
                                    format "l  ↦[ t ]{ q }  v") : bi_scope.

  Theorem struct_mapsto_ty q l v t :
    l ↦[t]{q} v -∗ ⌜val_ty v t⌝.
admit.
Defined.

  Local Lemma struct_mapsto_agree_flatten l t q1 v1 q2 v2 :
    length (flatten_struct v1) = length (flatten_struct v2) ->
    l ↦[t]{q1} v1 -∗ l ↦[t]{q2} v2 -∗
    ⌜flatten_struct v1 = flatten_struct v2⌝.
admit.
Defined.

  Theorem struct_mapsto_agree l t q1 v1 q2 v2 :
    l ↦[t]{q1} v1 -∗ l ↦[t]{q2} v2 -∗
    ⌜v1 = v2⌝.
  Proof.
    iIntros "Hl1 Hl2".
    iDestruct (struct_mapsto_ty with "Hl1") as %Hty1.
    iDestruct (struct_mapsto_ty with "Hl2") as %Hty2.
    pose proof (val_ty_len Hty1).
    pose proof (val_ty_len Hty2).
    iDestruct (struct_mapsto_agree_flatten with "Hl1 Hl2") as %Heq.
    {
 congruence.
}
    iPureIntro.
    eapply flatten_struct_inj; eauto.
