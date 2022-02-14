(* -*- mode: coq; coq-prog-args: ("-emacs" "-w" "-ssr-search-moved" "-w" "-deprecated-hint-without-locality" "-w" "-deprecated-instance-without-locality" "-w" "-deprecated-hint-rewrite-without-locality" "-w" "-deprecated-typeclasses-transparency-without-locality" "-w" "+deprecated-tactic-notation" "-w" "-notation-overridden,-redundant-canonical-projection" "-w" "-deprecated-native-compiler-option,-native-compiler-disabled" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/src" "Perennial" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/stdpp/theories" "stdpp" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/iris/iris" "iris" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/iris/iris_deprecated" "iris.deprecated" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/iris/iris_staging" "iris.staging" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/iris/iris_heap_lang" "iris.heap_lang" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/coqutil/src/coqutil" "coqutil" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/Goose" "Goose" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/record-update/src" "RecordUpdate" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/coq-tactical/src" "Tactical" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/iris-named-props/src" "iris_named_props" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-top" "disk" "-native-compiler" "ondemand") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 607 lines to 139 lines, then from 152 lines to 1701 lines, then from 1706 lines to 268 lines, then from 281 lines to 1117 lines, then from 1122 lines to 305 lines, then from 318 lines to 720 lines, then from 725 lines to 319 lines, then from 332 lines to 2187 lines, then from 2189 lines to 1585 lines *)
(* coqc version 8.16+alpha compiled with OCaml 4.13.0
   coqtop version runner-xxurkrix-project-6138686-concurrent-0:/builds/coq/coq/_build/default,(HEAD detached at 9c1f2f1) (9c1f2f1407dd487a2130de494bbce11207ed7f06)
   Expected coqc runtime on this file: 12.018 sec *)
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
Require stdpp.well_founded.
Require stdpp.countable.
Require stdpp.orders.
Require stdpp.vector.
Require stdpp.finite.
Require stdpp.sets.
Require stdpp.relations.
Require Coq.Strings.Ascii.
Require Coq.Strings.String.
Require stdpp.strings.
Require stdpp.pretty.
Require stdpp.infinite.
Require stdpp.fin_sets.
Require stdpp.fin_maps.
Require stdpp.fin_map_dom.
Require stdpp.mapset.
Require stdpp.pmap.
Require stdpp.propset.
Require stdpp.gmap.
Require Coq.ssr.ssreflect.
Require stdpp.listset.
Require stdpp.lexico.
Require stdpp.prelude.
Require iris.prelude.options.
Require iris.prelude.prelude.
Require iris.algebra.ofe.
Require iris.algebra.monoid.
Require iris.bi.notation.
Require iris.bi.interface.
Require iris.bi.derived_connectives.
Require iris.bi.extensions.
Require iris.bi.derived_laws.
Require iris.bi.derived_laws_later.
Require stdpp.functions.
Require stdpp.gmultiset.
Require iris.algebra.big_op.
Require iris.algebra.list.
Require iris.algebra.cmra.
Require iris.algebra.updates.
Require iris.algebra.local_updates.
Require iris.algebra.gset.
Require iris.algebra.proofmode_classes.
Require iris.algebra.gmap.
Require iris.bi.big_op.
Require stdpp.coPset.
Require iris.bi.internal_eq.
Require iris.bi.plainly.
Require iris.bi.updates.
Require iris.bi.embedding.
Require iris.bi.bi.
Require stdpp.namespaces.
Require iris.proofmode.base.
Require iris.proofmode.ident_name.
Require iris.proofmode.modalities.
Require iris.proofmode.classes.
Require stdpp.nat_cancel.
Require stdpp.telescopes.
Require iris.bi.telescopes.
Require iris.proofmode.modality_instances.
Require stdpp.hlist.
Require iris.proofmode.tokens.
Require iris.proofmode.sel_patterns.
Require iris.proofmode.intro_patterns.
Require iris.proofmode.spec_patterns.
Require iris.proofmode.environments.
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
Require iris.proofmode.class_instances.
Require iris.bi.lib.fractional.
Require iris.proofmode.class_instances_later.
Require iris.proofmode.class_instances_updates.
Require iris.proofmode.class_instances_embedding.
Require iris.proofmode.class_instances_plainly.
Require iris.proofmode.class_instances_internal_eq.
Require iris.proofmode.frame_instances.
Require iris.proofmode.proofmode.
Require iris.proofmode.tactics.
Require iris.algebra.frac.
Require iris.algebra.dfrac.
Require iris.algebra.agree.
Require iris.algebra.view.
Require iris.algebra.auth.
Require iris.algebra.lib.gmap_view.
Require iris.algebra.coPset.
Require iris.algebra.reservation_map.
Require iris.algebra.functions.
Require iris.algebra.cofe_solver.
Require iris.base_logic.upred.
Require iris.base_logic.bi.
Require iris.base_logic.derived.
Require iris.base_logic.proofmode.
Require iris.algebra.csum.
Require iris.algebra.excl.
Require iris.algebra.lib.excl_auth.
Require iris.base_logic.algebra.
Require iris.base_logic.base_logic.
Require iris.base_logic.lib.iprop.
Require iris.base_logic.lib.own.
Require iris.base_logic.lib.ghost_map.
Require iris.base_logic.lib.gen_heap.
Require Perennial.base_logic.lib.gen_heap.
Require Perennial.base_logic.base_logic.
Require Perennial.base_logic.lib.own.
Require iris.algebra.vector.
Require Perennial.base_logic.lib.iprop.
Require Perennial.algebra.auth_frac.
Require Perennial.algebra.mlist.
Require Perennial.base_logic.lib.wsat.
Require Perennial.base_logic.lib.fancy_updates.
Require Perennial.base_logic.lib.fupd_level.
Require Perennial.Helpers.ipm.
Require Perennial.algebra.laterN.
Require Perennial.algebra.atleast.
Require Perennial.algebra.big_op.big_sepL.
Require Perennial.algebra.own_discrete.
Require Perennial.Helpers.gset.
Require Perennial.Helpers.Map.
Require Perennial.base_logic.lib.ghost_map.
Require Perennial.algebra.gen_heap_names.
Require iris.algebra.lib.frac_auth.
Require Perennial.program_logic.language.
Require Perennial.program_logic.ectx_language.
Require iris.bi.weakestpre.
Require Perennial.base_logic.lib.crash_token.
Require Perennial.base_logic.lib.ncfupd.
Require Perennial.base_logic.lib.ae_invariants.
Require Perennial.base_logic.lib.invariants.
Require Perennial.base_logic.lib.fancy_updates2.
Require Perennial.program_logic.step_fupd_extra.
Require Perennial.program_logic.ae_invariants_mutable.
Require Perennial.program_logic.cfupd.
Require Perennial.program_logic.crash_weakestpre.
Require Perennial.program_logic.weakestpre.
Require Perennial.program_logic.lifting.
Require Perennial.program_logic.ectx_lifting.
Require Perennial.base_logic.lib.frac_coPset.
Require Coq.Arith.Min.
Require iris.algebra.cmra_big_op.
Require iris.algebra.numbers.
Require Perennial.algebra.blocks.
Require Perennial.algebra.na_heap.
Require Coq.Program.Equality.
Require RecordUpdate.RecordSet.
Require stdpp.binders.
Require Perennial.program_logic.ectxi_language.
Require Perennial.Helpers.CountableTactics.
Require Perennial.Helpers.Transitions.
Require Perennial.program_logic.crash_lang.
Require Perennial.goose_lang.locations.
Require coqutil.Datatypes.PrimitivePair.
Require coqutil.Datatypes.HList.
Require coqutil.Z.Lia.
Require Coq.btauto.Btauto.
Require coqutil.Z.bitblast.
Require Coq.ZArith.BinInt.
Require coqutil.Z.div_mod_to_equations.
Require coqutil.Z.BitOps.
Require Coq.ZArith.BinIntDef.
Require coqutil.sanity.
Require coqutil.Word.Interface.
Require Coq.ZArith.Zpow_facts.
Require coqutil.Z.PushPullMod.
Require Coq.setoid_ring.Ring_theory.
Require coqutil.Tactics.autoforward.
Require Coq.Arith.PeanoNat.
Require Coq.Arith.Compare_dec.
Require coqutil.Decidable.
Require coqutil.Word.Properties.
Require coqutil.Word.Naive.
Require Perennial.Helpers.LittleEndian.
Require Perennial.Helpers.Integers.

Declare ML Module "coq-core.plugins.ltac".
Module Export AdmitTactic.
Module Import LocalFalse.
Inductive False : Prop := .
End LocalFalse.
Axiom proof_admitted : False.
Global Set Default Proof Mode "Classic".
Tactic Notation "admit" := abstract case proof_admitted.
End AdmitTactic.

Module Export Perennial_DOT_goose_lang_DOT_lang_WRAPPED.
Module Export lang.
Import Coq.Program.Equality.
Import RecordUpdate.RecordSet.
Export stdpp.binders.
Export stdpp.strings.
Import stdpp.gmap.
Export iris.algebra.ofe.
Export Perennial.program_logic.language.
Export Perennial.program_logic.ectx_language.
Export Perennial.program_logic.ectxi_language.
Import Perennial.Helpers.CountableTactics.
Import Perennial.Helpers.Transitions.
Export Perennial.program_logic.crash_lang.
Export Perennial.goose_lang.locations.
Export Perennial.Helpers.Integers.
Set Default Proof Using "Type".

Open Scope Z_scope.

 

Delimit Scope expr_scope with E.
Delimit Scope val_scope with V.

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

Bind Scope expr_scope with expr.
Bind Scope val_scope with val.

Notation Panic s := (Primitive0 (PanicOp s)).
Notation ArbitraryInt := (Primitive0 ArbitraryIntOp).
Notation AllocN := (Primitive2 AllocNOp).
Notation PrepareWrite := (Primitive1 PrepareWriteOp).
Notation FinishStore := (Primitive2 FinishStoreOp).
Notation StartRead := (Primitive1 StartReadOp).
Notation FinishRead := (Primitive1 FinishReadOp).
Notation Load := (Primitive1 LoadOp).
Notation Input := (Primitive1 InputOp).
Notation Output := (Primitive1 OutputOp).

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

 
Definition Free {T} (v:T): nonAtomic T := (Reading 0, v).

Inductive event :=
  | In_ev (sel v:base_lit)
  | Out_ev (v:base_lit)
  | Crash_ev
.

 
Definition Trace := list event.

Definition add_event (ev: event) (ts: Trace) : Trace := cons ev ts.

Definition add_crash (ts: Trace) : Trace :=
  match ts with
  | Crash_ev::ts' => ts
  | _ => add_event Crash_ev ts
  end.

Definition Oracle := Trace -> forall (sel:u64), u64.

Instance Oracle_Inhabited: Inhabited Oracle := populate (fun _ _ => word.of_Z 0).

 
Record state : Type := {
  heap: gmap loc (nonAtomic val);
  world: ffi_state;
  trace: Trace;
  oracle: Oracle;
}.
Definition global_state : Type := ffi_global_state.

Global Instance eta_state : Settable _ := settable! Build_state <heap; world; trace; oracle>.

 
Class ffi_semantics :=
  {
    ffi_step : ffi_opcode -> val -> transition (state*global_state) expr;
    ffi_crash_step : ffi_state -> ffi_state -> Prop;
  }.
Context {ffi_semantics: ffi_semantics}.

Inductive goose_crash : state -> state -> Prop :=
  | GooseCrash σ w w' :
     w = σ.(world) ->
     ffi_crash_step w w' ->
     goose_crash σ (set trace add_crash (set world (fun _ => w') (set heap (fun _ => ∅) σ)))
.

 
Definition observation : Type := proph_id * (val * val).

Notation of_val := Val (only parsing).

Definition to_val (e : expr) : option val :=
  match e with
  | Val v => Some v
  | _ => None
  end.

 
Definition lit_is_unboxed (l: base_lit) : Prop :=
  match l with
   
  | LitProphecy _ | LitPoison => False
  | _ => True
  end.
Definition val_is_unboxed (v : val) : Prop :=
  match v with
  | LitV l => lit_is_unboxed l
  | InjLV (LitV l) => lit_is_unboxed l
  | InjRV (LitV l) => lit_is_unboxed l
  | _ => False
  end.

Global Instance lit_is_unboxed_dec l : Decision (lit_is_unboxed l).
Admitted.
Global Instance val_is_unboxed_dec v : Decision (val_is_unboxed v).
Admitted.

 
Definition vals_compare_safe (vl v1 : val) : Prop :=
  val_is_unboxed vl ∨ val_is_unboxed v1.
Global Arguments vals_compare_safe !_ !_ /.

 
Lemma to_of_val v : to_val (of_val v) = Some v.
Admitted.

Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Admitted.

Global Instance of_val_inj : Inj (=) (=) of_val.
Admitted.

Global Instance base_lit_eq_dec : EqDecision base_lit.
Admitted.
Global Instance un_op_eq_dec : EqDecision un_op.
Admitted.
Global Instance bin_op_eq_dec : EqDecision bin_op.
Admitted.
Global Instance arity_eq_dec : EqDecision arity.
Admitted.
Global Instance prim_op0_eq_dec : EqDecision prim_op0.
Admitted.
Global Instance prim_op1_eq_dec : EqDecision prim_op1.
Admitted.
Global Instance prim_op2_eq_dec : EqDecision prim_op2.
Admitted.
Global Instance prim_op_eq_dec ar : EqDecision (prim_op ar).
Admitted.
Global Instance expr_eq_dec : EqDecision expr.
Admitted.
Global Instance val_eq_dec : EqDecision val.
Admitted.

Definition enc_base_lit :=
(λ l, match l with
  | LitInt n => (inl (inl (inl (inl n))), None)
  | LitInt32 n => (inl (inl (inl (inr n))), None)
  | LitByte n => (inl (inl (inr n)), None)
  | LitBool b => (inl (inr b), None)
  | LitUnit => (inr (inl false), None)
  | LitString s => (inr (inr (inr s)), None)
  | LitPoison => (inr (inl true), None)
  | LitLoc l => (inr (inr (inl l)), None)
  | LitProphecy p => (inr (inl false), Some p)
  end).

Definition dec_base_lit :=
(λ l, match l with
  | (inl (inl (inl (inl n))), None) => LitInt n
  | (inl (inl (inl (inr n))), None) => LitInt32 n
  | (inl (inl (inr n)), None) => LitByte n
  | (inl (inr b), None) => LitBool b
  | (inr (inl false), None) => LitUnit
  | (inr (inr (inr s)), None) => LitString s
  | (inr (inl true), None) => LitPoison
  | (inr (inr (inl l)), None) => LitLoc l
  | (_, Some p) => LitProphecy p
  end).

Definition base_lit_enc_retract : forall l, dec_base_lit (enc_base_lit l) = l.
Admitted.

Global Instance base_lit_countable : Countable base_lit :=
  inj_countable' enc_base_lit dec_base_lit base_lit_enc_retract.

Global Instance un_op_finite : Countable un_op.
Admitted.

Global Instance bin_op_countable : Countable bin_op.
Admitted.

Instance prim_op0_countable : Countable prim_op0.
Admitted.

Instance prim_op1_countable : Countable prim_op1.
Admitted.

Instance prim_op2_countable : Countable prim_op2.
Admitted.

Definition prim_op' : Set := prim_op0 + prim_op1 + prim_op2.

Definition a_prim_op {ar} (op: prim_op ar) : prim_op'.
Admitted.

 
Inductive basic_type :=
  | stringVal (s:string)
  | binderVal (b:binder)
  | intVal (z:u64)
  | litVal (l: base_lit)
  | un_opVal (op:un_op)
  | bin_opVal (op:bin_op)
  | primOpVal (op:prim_op')
  | externOp (op:ffi_opcode)
  | externVal (ev:ffi_val)
.

Instance basic_type_eq_dec : EqDecision basic_type.
Admitted.
Instance basic_type_countable : Countable basic_type.
Admitted.

Definition to_prim_op : {f: forall ar (op: prim_op'), prim_op ar |
                         forall ar op, f ar (a_prim_op op) = op}.
Admitted.

Definition to_prim_op_correct := proj2_sig to_prim_op.

Global Instance expr_countable : Countable expr.
Admitted.
Global Instance val_countable : Countable val.
Admitted.

Global Instance state_inhabited : Inhabited state :=
  populate {| heap := inhabitant; world := inhabitant; trace := inhabitant; oracle := inhabitant; |}.
Global Instance val_inhabited : Inhabited val := populate (LitV LitUnit).
Global Instance expr_inhabited : Inhabited expr. exact (populate (Val inhabitant)). Defined.

Canonical Structure stateO := leibnizO state.
Canonical Structure locO := leibnizO loc.
Canonical Structure valO := leibnizO val.
Canonical Structure exprO := leibnizO expr.

 
Inductive ectx_item :=
  | AppLCtx (v2 : val)
  | AppRCtx (e1 : expr)
  | UnOpCtx (op : un_op)
  | BinOpLCtx (op : bin_op) (e2 : expr)
  | BinOpRCtx (op : bin_op) (v1 : val)
  | IfCtx (e1 e2 : expr)
  | PairLCtx (e2 : expr)
  | PairRCtx (v1 : val)
  | FstCtx
  | SndCtx
  | InjLCtx
  | InjRCtx
  | CaseCtx (e1 : expr) (e2 : expr)
  | Primitive1Ctx  (op: prim_op args1)
  | Primitive2LCtx (op: prim_op args2) (e2 : expr)
  | Primitive2RCtx (op: prim_op args2) (v1 : val)
   
  | ExternalOpCtx (op : ffi_opcode)
  | CmpXchgLCtx (e1 : expr) (e2 : expr)
  | CmpXchgMCtx (v1 : val) (e2 : expr)
  | CmpXchgRCtx (v1 : val) (v2 : val)
  | ResolveLCtx (ctx : ectx_item) (v1 : val) (v2 : val)
  | ResolveMCtx (e0 : expr) (v2 : val)
  | ResolveRCtx (e0 : expr) (e1 : expr)
  | AtomicallyCtx (e0 : expr).
Fixpoint fill_item (Ki : ectx_item) (e : expr) : expr. exact (match Ki with
  | AppLCtx v2 => App e (of_val v2)
  | AppRCtx e1 => App e1 e
  | UnOpCtx op => UnOp op e
  | BinOpLCtx op e2 => BinOp op e e2
  | BinOpRCtx op v1 => BinOp op (Val v1) e
  | IfCtx e1 e2 => If e e1 e2
  | PairLCtx e2 => Pair e e2
  | PairRCtx v1 => Pair (Val v1) e
  | FstCtx => Fst e
  | SndCtx => Snd e
  | InjLCtx => InjL e
  | InjRCtx => InjR e
  | CaseCtx e1 e2 => Case e e1 e2
  | Primitive1Ctx op => Primitive1 op e
  | Primitive2LCtx op e2 => Primitive2 op e e2
  | Primitive2RCtx op v1 => Primitive2 op (Val v1) e
   
  | ExternalOpCtx op => ExternalOp op e
  | CmpXchgLCtx e1 e2 => CmpXchg e e1 e2
  | CmpXchgMCtx v0 e2 => CmpXchg (Val v0) e e2
  | CmpXchgRCtx v0 v1 => CmpXchg (Val v0) (Val v1) e
  | ResolveLCtx K v1 v2 => Resolve (fill_item K e) (Val v1) (Val v2)
  | ResolveMCtx ex v2 => Resolve ex e (Val v2)
  | ResolveRCtx ex e1 => Resolve ex e1 e
  | AtomicallyCtx e1 => Atomically e e1
  end). Defined.
Fixpoint subst (x : string) (v : val) (e : expr)  : expr. exact (match e with
  | Val _ => e
  | Var y => if decide (x = y) then Val v else Var y
  | Rec f y e =>
     Rec f y $ if decide (BNamed x ≠ f ∧ BNamed x ≠ y) then subst x v e else e
  | App e1 e2 => App (subst x v e1) (subst x v e2)
  | UnOp op e => UnOp op (subst x v e)
  | BinOp op e1 e2 => BinOp op (subst x v e1) (subst x v e2)
  | If e0 e1 e2 => If (subst x v e0) (subst x v e1) (subst x v e2)
  | Pair e1 e2 => Pair (subst x v e1) (subst x v e2)
  | Fst e => Fst (subst x v e)
  | Snd e => Snd (subst x v e)
  | InjL e => InjL (subst x v e)
  | InjR e => InjR (subst x v e)
  | Case e0 e1 e2 => Case (subst x v e0) (subst x v e1) (subst x v e2)
  | Fork e => Fork (subst x v e)
  | Atomically el e => Atomically (subst x v el) (subst x v e)
  | Primitive0 op => Primitive0 op
  | Primitive1 op e => Primitive1 op (subst x v e)
  | Primitive2 op e1 e2 => Primitive2 op (subst x v e1) (subst x v e2)
   
  | ExternalOp op e => ExternalOp op (subst x v e)
  | CmpXchg e0 e1 e2 => CmpXchg (subst x v e0) (subst x v e1) (subst x v e2)
  | NewProph => NewProph
  | Resolve ex e1 e2 => Resolve (subst x v ex) (subst x v e1) (subst x v e2)
  end). Defined.
Definition subst' (mx : binder) (v : val) : expr → expr. exact (match mx with BNamed x => subst x v | BAnon => id end). Defined.
Definition un_op_eval (op : un_op) (v : val) : option val. exact (match op, v with
  | NegOp, LitV (LitBool b) => Some $ LitV $ LitBool (negb b)
  | NegOp, LitV (LitInt n) => Some $ LitV $ LitInt (word.not n)
  | NegOp, LitV (LitInt32 n) => Some $ LitV $ LitInt32 (word.not n)
  | NegOp, LitV (LitByte n) => Some $ LitV $ LitByte (word.not n)
  | ToUInt64Op, LitV (LitInt v) => Some $ LitV $ LitInt v
  | ToUInt64Op, LitV (LitInt32 v) => Some $ LitV $ LitInt (u32_to_u64 v)
  | ToUInt64Op, LitV (LitByte v) => Some $ LitV $ LitInt (u8_to_u64 v)
  | ToUInt32Op, LitV (LitInt v) => Some $ LitV $ LitInt32 (u32_from_u64 v)
  | ToUInt32Op, LitV (LitInt32 v) => Some $ LitV $ LitInt32 v
  | ToUInt32Op, LitV (LitByte v) => Some $ LitV $ LitInt32 (u8_to_u32 v)
  | ToUInt8Op, LitV (LitInt v) => Some $ LitV $ LitByte (u8_from_u64 v)
  | ToUInt8Op, LitV (LitInt32 v) => Some $ LitV $ LitByte (u8_from_u32 v)
  | ToUInt8Op, LitV (LitByte v) => Some $ LitV $ LitByte v
  | ToStringOp, LitV (LitByte v) => Some $ LitV $ LitString (u8_to_string v)
  | _, _ => None
  end). Defined.
Definition bin_op_eval_word (op : bin_op) {width} {word: Interface.word width} (n1 n2 : word) : option word. exact (match op with
  | PlusOp => Some $ word.add (word:=word) n1 n2
  | MinusOp => Some $ word.sub (word:=word) n1 n2
  | MultOp => Some $ (word.mul (word:=word) n1 n2)
  | QuotOp => Some $ (word.divu (word:=word) n1 n2)
  | RemOp => Some $ (word.modu (word:=word) n1 n2)
  | AndOp => Some $ (word.and (word:=word) n1 n2)
  | OrOp => Some $ (word.or (word:=word) n1 n2)
  | XorOp => Some $ (word.xor (word:=word) n1 n2)
  | ShiftLOp => Some $ (word.slu (word:=word) n1 n2)
  | ShiftROp => Some $ (word.sru (word:=word) n1 n2)
  | _ => None
  end). Defined.
Definition bin_op_eval_shift (op : bin_op) {width} {word: Interface.word width} (n1 n2 : word) : option word. exact (if decide (op = ShiftLOp ∨ op = ShiftROp) then
    bin_op_eval_word op n1 n2
  else None). Defined.
Definition bin_op_eval_compare (op : bin_op) {width} {word: Interface.word width} (n1 n2 : word) : option bool. exact (match op with
  | LeOp => Some $ bool_decide (word.unsigned n1 <= word.unsigned n2)
  | LtOp => Some $ bool_decide (word.unsigned n1 < word.unsigned n2)
  | EqOp => Some $ bool_decide (word.unsigned n1 = word.unsigned n2)
  | _ => None
  end). Defined.
Definition bin_op_eval_bool (op : bin_op) (b1 b2 : bool) : option base_lit. exact (match op with
  | PlusOp | MinusOp | MultOp | QuotOp | RemOp => None  
  | AndOp => Some (LitBool (b1 && b2))
  | OrOp => Some (LitBool (b1 || b2))
  | XorOp => Some (LitBool (xorb b1 b2))
  | ShiftLOp | ShiftROp => None  
  | LeOp | LtOp => None  
  | EqOp => Some (LitBool (bool_decide (b1 = b2)))
  | OffsetOp _ => None  
  end). Defined.
Definition bin_op_eval_string (op : bin_op) (s1 s2 : string) : option base_lit. exact (match op with
  | PlusOp => Some $ LitString (s1 ++ s2)
  | _ => None
  end). Defined.

 
Fixpoint is_comparable v :=
  match v with
  | RecV _ _ _ | ExtV _ => False
  | PairV v1 v2 => is_comparable v1 ∧ is_comparable v2
  | InjLV v => is_comparable v
  | InjRV v => is_comparable v
  | _ => True
  end.
Global Instance is_comparable_decide v : Decision (is_comparable v).
Admitted.
Definition bin_op_eval_eq (v1 v2 : val) : option base_lit. exact (if decide (is_comparable v1 ∧ is_comparable v2) then
    Some $ LitBool $ bool_decide (v1 = v2)
  else None). Defined.
Definition bin_op_eval (op : bin_op) (v1 v2 : val) : option val. exact (if decide (op = EqOp) then LitV <$> bin_op_eval_eq v1 v2
  else
    match v1, v2 with
    | LitV (LitInt n1), LitV (LitInt n2) =>
      LitV <$> ((LitInt <$> bin_op_eval_word op n1 n2)
                  ∪ (LitBool <$> bin_op_eval_compare op n1 n2))
    | LitV (LitInt32 n1), LitV (LitInt32 n2) =>
      LitV <$> ((LitInt32 <$> bin_op_eval_word op n1 n2)
                  ∪ (LitBool <$> bin_op_eval_compare op n1 n2))
    | LitV (LitByte n1), LitV (LitByte n2) =>
      LitV <$> ((LitByte <$> bin_op_eval_word op n1 n2)
                  ∪ (LitBool <$> bin_op_eval_compare op n1 n2))

     
    | LitV (LitByte n1), LitV (LitInt n2) =>
      LitV <$> (LitByte <$> bin_op_eval_shift op n1 (u8_from_u64 n2))
    | LitV (LitByte n1), LitV (LitInt32 n2) =>
      LitV <$> (LitByte <$> bin_op_eval_shift op n1 (u8_from_u32 n2))
    | LitV (LitInt32 n1), LitV (LitInt n2) =>
      LitV <$> (LitInt32 <$> bin_op_eval_shift op n1 (u32_from_u64 n2))
    | LitV (LitInt32 n1), LitV (LitByte n2) =>
      LitV <$> (LitInt32 <$> bin_op_eval_shift op n1 (u8_to_u32 n2))
    | LitV (LitInt n1), LitV (LitByte n2) =>
      LitV <$> (LitInt <$> bin_op_eval_shift op n1 (u8_to_u64 n2))
    | LitV (LitInt n1), LitV (LitInt32 n2) =>
      LitV <$> (LitInt <$> bin_op_eval_shift op n1 (u32_to_u64 n2))

    | LitV (LitBool b1), LitV (LitBool b2) => LitV <$> bin_op_eval_bool op b1 b2
    | LitV (LitString s1), LitV (LitString s2) => LitV <$> bin_op_eval_string op s1 s2
    | LitV (LitLoc l), LitV (LitInt off) => match op with
                                           | OffsetOp k =>
                                             Some $ LitV $ LitLoc (l +ₗ k * (int.Z (off: u64)))
                                           | _ => None
                                           end
    | _, _ => None
    end). Defined.
Definition state_insert_list (l: loc) (vs: list val) (σ: state): state. exact (set heap (λ h, heap_array l (fmap Free vs) ∪ h) σ). Defined.
Definition concat_replicate {A} (n: nat) (l: list A): list A. exact (concat (replicate n l)). Defined.
Definition state_init_heap (l : loc) (n : Z) (v : val) (σ : state) : state. exact (state_insert_list l (concat_replicate (Z.to_nat n) (flatten_struct v)) σ). Defined.

Lemma state_init_heap_singleton l v σ :
  state_init_heap l 1 v σ = state_insert_list l (flatten_struct v) σ.
Admitted.

Definition is_Free {A} (mna: option (nonAtomic A)) := exists x, mna = Some (Free x).
Global Instance is_Free_dec A (x: option (nonAtomic A)) : Decision (is_Free x).
Admitted.

Definition is_Writing {A} (mna: option (nonAtomic A)) := exists x, mna = Some (Writing, x).
Global Instance is_Writing_dec A (x: option (nonAtomic A)) : Decision (is_Writing x).
Admitted.

Existing Instances r_mbind r_mret r_fmap.
Definition ret_expr {state} (e:expr): transition state (list observation * expr * list expr). exact (ret ([],e,[])). Defined.
Definition atomically {state} (tr: transition state val): transition state (list observation * expr * list expr). exact ((λ v, ([], Val v, [])) <$> tr). Defined.
Definition atomicallyM {state} (tr: transition state expr): transition state (list observation * expr * list expr). exact ((λ v, ([], v, [])) <$> tr). Defined.

Definition isFresh (σg: state*global_state) (l: loc) :=
  (forall i, l +ₗ i ≠ null ∧ σg.1.(heap) !! (l +ₗ i) = None)%Z ∧
  (addr_offset l = 0).

Lemma addr_base_non_null_offset l:
  l ≠ null → (addr_offset l = 0)%Z →
  addr_base l ≠ null.
Admitted.

Lemma addr_base_non_null l:
  addr_base l ≠ null →
  l ≠ null.
Admitted.

Lemma plus_off_preserves_non_null l:
  addr_base l ≠ null →
  ∀ z, l ≠ addr_plus_off null z.
Admitted.

Theorem isFresh_not_null σ l :
  isFresh σ l -> l ≠ null.
Admitted.

Theorem isFresh_offset0 σ l :
  isFresh σ l -> addr_offset l = 0.
Admitted.

Theorem isFresh_base σ l :
  isFresh σ l -> addr_base l = l.
Admitted.

Theorem fresh_locs_isFresh σg :
  isFresh σg (fresh_locs (dom (gset loc) σg.1.(heap))).
admit.
Defined.

Definition gen_isFresh σg : {l: loc | isFresh σg l}.
Proof.
  refine (exist _ (fresh_locs (dom (gset loc) σg.1.(heap))) _).
  by apply fresh_locs_isFresh.
Defined.
Global Instance alloc_gen : GenPred loc (state*global_state) (isFresh). exact (fun _ σ => Some (gen_isFresh σ)). Defined.
Definition allocateN : transition (state*global_state) loc. exact (suchThat (isFresh)). Defined.

 

Instance gen_anyInt Σ: GenPred u64 Σ (fun _ _ => True).
Admitted.
Definition arbitraryInt {state}: transition state u64. exact (suchThat (fun _ _ => True)). Defined.

Fixpoint transition_repeat (n:nat) {Σ T} (t: T → transition Σ T) (init:T) : transition Σ T :=
  match n with
  | 0%nat => ret init
  | S n => Transitions.bind (t init) (transition_repeat n t)
  end.
Definition transition_star {Σ T} (t : T → transition Σ T) (init:T) : transition Σ T. exact (n ← suchThat (gen:=fun _ _ => None) (fun _ (_:nat) => True);
  transition_repeat n t init). Defined.
Definition modifyσ (f : state → state) : transition (state*global_state) (). exact (modify (λ '(σ, g), (f σ, g))). Defined.
Definition head_trans (e: expr) :
 transition (state * global_state) (list observation * expr * list expr). exact (match e with
  | Rec f x e => atomically $ ret $ RecV f x e
  | Pair (Val v1) (Val v2) => atomically $ ret $ PairV v1 v2
  | InjL (Val v) => atomically $ ret $ InjLV v
  | InjR (Val v) => atomically $ ret $ InjRV v
  | App (Val (RecV f x e1)) (Val v2) =>
    ret_expr $ subst' x v2 (subst' f (RecV f x e1) e1)
  | UnOp op (Val v) => atomically $ unwrap $ un_op_eval op v
  | BinOp op (Val v1) (Val v2) => atomically $ unwrap $ bin_op_eval op v1 v2
  | If (Val (LitV (LitBool b))) e1 e2 => ret_expr $ if b then e1 else e2
  | Fst (Val (PairV v1 v2)) => atomically $ ret v1
  | Snd (Val (PairV v1 v2)) => atomically $ ret v2
  | Case (Val (InjLV v)) e1 e2 => ret_expr $ App e1 (Val v)
  | Case (Val (InjRV v)) e1 e2 => ret_expr $ App e2 (Val v)
  | Fork e => ret ([], Val $ LitV LitUnit, [e])
   
  | Atomically _ _ => undefined
  | ArbitraryInt =>
    atomically
      (x ← arbitraryInt;
      ret $ LitV $ LitInt x)
  | AllocN (Val (LitV (LitInt n))) (Val v) =>
    atomically
      (check (0 < int.Z n)%Z;;
       l ← allocateN;
       modifyσ (state_init_heap l (int.Z n) v);;
       ret $ LitV $ LitLoc l)
   | StartRead (Val (LitV (LitLoc l))) =>  
     atomically
       (nav ← reads (λ '(σ,g), σ.(heap) !! l) ≫= unwrap;
        match nav with
        | (Reading n, v) =>
          modifyσ (set heap <[l:=(Reading (S n), v)]>);;
          ret v
        | _ => undefined
        end)
   | FinishRead (Val (LitV (LitLoc l))) =>  
     atomically
       (nav ← reads (λ '(σ,g), σ.(heap) !! l) ≫= unwrap;
        match nav with
        | (Reading (S n), v) =>
          modifyσ (set heap <[l:=(Reading n, v)]>);;
                 ret $ LitV $ LitUnit
        | _ => undefined
        end)
   | Load (Val (LitV (LitLoc l))) =>  
     atomically
       (nav ← reads (λ '(σ,g), σ.(heap) !! l) ≫= unwrap;
        match nav with
        | (Reading _, v) => ret v
        | _ => undefined
        end)
  | PrepareWrite (Val (LitV (LitLoc l))) =>  
    atomically
      (v ← (reads (λ '(σ,g), σ.(heap) !! l) ≫= unwrap);
        match v with
        | (Reading 0, v) =>
          modifyσ (set heap <[l:=(Writing, v)]>);;
          ret $ LitV $ LitUnit
        | _ => undefined
        end)
  | FinishStore (Val (LitV (LitLoc l))) (Val v) =>  
    atomically
      (nav ← reads (λ '(σ,g), σ.(heap) !! l);
       check (is_Writing nav);;
       modifyσ (set heap <[l:=Free v]>);;
       ret $ LitV $ LitUnit)
  | ExternalOp op (Val v) => atomicallyM $ ffi_step op v
  | Input (Val (LitV (LitInt selv))) =>
    atomically
      (x ← reads (λ '(σ,g), σ.(oracle) σ.(trace) selv);
      modifyσ (set trace (add_event (In_ev (LitInt selv) (LitInt x))));;
      ret $ LitV $ LitInt $ x)
  | Output (Val (LitV v)) =>
    atomically
      (modifyσ (set trace (add_event (Out_ev v)));;
       ret $ LitV $ LitUnit)
  | CmpXchg (Val (LitV (LitLoc l))) (Val v1) (Val v2) =>
    atomically
      (nav ← reads (λ '(σ,g), σ.(heap) !! l) ≫= unwrap;
      match nav with
      | (Reading n, vl) =>
        check (vals_compare_safe vl v1);;
        when (vl = v1) (check (n = 0%nat);; modifyσ (set heap <[l:=Free v2]>));;
        ret $ PairV vl (LitV $ LitBool (bool_decide (vl = v1)))
      | _ => undefined
      end)
  | _ => undefined
  end). Defined.
Definition head_step:
    expr -> state -> global_state -> list observation -> expr -> state -> global_state -> list expr -> Prop. exact (fun e s g κs e' s' g' efs =>
      relation.denote (head_trans e) (s,g) (s',g') (κs, e', efs)). Defined.
Definition fill' (K : list (ectx_item)) (e : expr) : expr. exact (foldl (flip fill_item) e K). Defined.

Inductive prim_step' (e1 : expr) (σ1 : state) (g1 : global_state) (κ : list (observation))
    (e2 : expr) (σ2 : state) (g2 : global_state) (efs : list (expr)) : Prop :=
  Ectx_step' K e1' e2' :
    e1 = fill' K e1' → e2 = fill' K e2' →
    head_step e1' σ1 g1 κ e2' σ2 g2 efs → prim_step' e1 σ1 g1 κ e2 σ2 g2 efs.

Definition irreducible' (e : expr) (σ : state) (g : global_state) :=
  ∀ κ e' σ' g' efs, ¬prim_step' e σ g κ e' σ' g' efs.
Definition stuck' (e : expr) (σ : state) (g : global_state) :=
  to_val e = None ∧ irreducible' e σ g.

Definition prim_step'_safe e s g :=
  (∀ e' s' g', rtc (λ '(e, (s, g)) '(e', (s', g')), prim_step' e s g [] e' s' g' []) (e, (s, g)) (e', (s', g')) →
            ¬ stuck' e' s' g'
               
  ).

Inductive head_step_atomic:
    expr -> state -> global_state -> list observation -> expr -> state -> global_state -> list expr -> Prop :=
 | head_step_trans : ∀ e s g κs e' s' g' efs,
     head_step e s g κs e' s' g' efs →
     head_step_atomic e s g κs e' s' g' efs
 | head_step_atomically : ∀ (vl : val) e s g κs v' s' g',
     rtc (λ '(e, (s, g)) '(e', (s', g')), prim_step' e s g [] e' s' g' []) (e, (s, g)) (Val (InjRV v'), (s', g')) →
     prim_step'_safe e s g →
     head_step_atomic (Atomically (of_val vl) e) s g κs (Val (InjRV v')) s' g' []
 | head_step_atomically_fail : ∀ vl e s g κs,
      
     prim_step'_safe e s g →
     head_step_atomic (Atomically (of_val vl) e) s g κs (Val (InjLV (LitV LitUnit))) s g []
.

Lemma head_step_atomic_inv e s g κs e' s' g' efs :
  head_step_atomic e s g κs e' s' g' efs →
  (∀ el e'', e ≠ Atomically el e'') →
  head_step e s g κs e' s' g' efs.
Admitted.

 
Global Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
Admitted.

Lemma fill_item_val Ki e :
  is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
Admitted.

Lemma fill_item_val_inv Ki v v' :
  is_Some (to_val (fill_item Ki (of_val v))) → is_Some (to_val (fill_item Ki (of_val v'))).
Admitted.

Lemma suchThat_false state T (s1 s2: state) (v: T) :
  relation.suchThat (fun _ _ => False) s1 s2 v -> False.
Admitted.

Hint Resolve suchThat_false : core.

Lemma val_head_stuck e1 σ1 g1 κ e2 σ2 g2 efs :
  head_step e1 σ1 g1 κ e2 σ2 g2 efs → to_val e1 = None.
Admitted.

Lemma val_head_atomic_stuck e1 σ1 g1 κ e2 σ2 g2 efs :
  head_step_atomic e1 σ1 g1 κ e2 σ2 g2 efs → to_val e1 = None.
Admitted.

Lemma head_ctx_step_val Ki e σ1 g1 κ e2 σ2 g2 efs :
  head_step (fill_item Ki e) σ1 g1 κ e2 σ2 g2 efs → is_Some (to_val e).
Admitted.

Lemma head_ctx_step_atomic_val Ki e σ1 g1 κ e2 σ2 g2 efs :
  head_step_atomic (fill_item Ki e) σ1 g1 κ e2 σ2 g2 efs → is_Some (to_val e).
Admitted.

Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
  to_val e1 = None → to_val e2 = None →
  fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
Admitted.

Lemma alloc_fresh v (n: u64) σ g :
  let l := fresh_locs (dom (gset loc) σ.(heap)) in
  (0 < int.Z n)%Z →
  head_step_atomic (AllocN ((Val $ LitV $ LitInt $ n)) (Val v)) σ g []
            (Val $ LitV $ LitLoc l) (state_init_heap l (int.Z n) v σ) g [].
Admitted.

Lemma arbitrary_int_step σ g :
  head_step_atomic (ArbitraryInt) σ g []
            (Val $ LitV $ LitInt $ U64 0) σ g [].
Admitted.

 

Lemma goose_lang_mixin : EctxiLanguageMixin of_val to_val fill_item head_step_atomic.
Admitted.

End external.
End goose_lang.

 

 
Export goose_lang.

Arguments ffi_semantics ext ffi : clear implicits.
Arguments goose_lang.goose_lang_mixin {ext} {ffi} ffi_semantics.

Section goose.
  Context {ext: ffi_syntax} {ffi: ffi_model}
          {ffi_semantics: ffi_semantics ext ffi}.
  Canonical Structure goose_ectxi_lang := (EctxiLanguage (goose_lang.goose_lang_mixin ffi_semantics)).
  Canonical Structure goose_ectx_lang := (EctxLanguageOfEctxi goose_ectxi_lang).
  Canonical Structure goose_lang := (LanguageOfEctx goose_ectx_lang).
Canonical Structure goose_crash_lang : crash_semantics goose_lang. exact ({| crash_prim_step := goose_crash |}). Defined.

 
Lemma to_val_fill_some K e v : to_val (fill K e) = Some v → K = [] ∧ e = Val v.
Admitted.

Lemma prim_step_to_val_is_head_step e σ1 g1 κs w σ2 g2 efs :
  prim_step e σ1 g1 κs (Val w) σ2 g2 efs → head_step_atomic (ffi_semantics:=ffi_semantics) e σ1 g1 κs (Val w) σ2 g2 efs.
Admitted.

Lemma head_prim_step_trans e σ g κ e' σ' g' efs :
  head_step e σ g κ e' σ' g' efs →
  ectx_language.prim_step e σ g κ e' σ' g' efs.
Admitted.

Lemma head_prim_step_trans' e σ g κ e' σ' g' efs :
  head_step e σ g κ e' σ' g' efs →
  prim_step' e σ g κ e' σ' g' efs.
Admitted.

Definition head_reducible' (e : expr) (σ : state) (g : global_state) :=
  ∃ κ e' σ' g' efs, head_step e σ g κ e' σ' g' efs.
Definition head_irreducible' (e : expr) (σ : state) (g : global_state) :=
  ∀ κ e' σ' g' efs, ¬head_step e σ g κ e' σ' g' efs.
Definition reducible' (e : expr) (σ : state) (g : global_state) :=
  ∃ κ e' σ' g' efs, prim_step' e σ g κ e' σ' g' efs.

Lemma prim_head_reducible' e σ g :
  reducible' e σ g → sub_redexes_are_values e → head_reducible' e σ g.
Admitted.

Lemma not_reducible' e σ g : ¬reducible' e σ g ↔ irreducible' e σ g.
Admitted.
Lemma not_head_reducible' e σ g : ¬head_reducible' e σ g ↔ head_irreducible' e σ g.
Admitted.

Lemma prim_head_irreducible' e σ g :
  head_irreducible' e σ g → sub_redexes_are_values e → irreducible' e σ g.
Admitted.

Class LanguageCtx' (K : expr → expr) : Prop :=
  { fill_not_val' : ∀ e, to_val e = None → to_val (K e) = None;
    fill_step' : ∀ e1 σ1 g1 κ e2 σ2 g2 efs,
                  prim_step' e1 σ1 g1 κ e2 σ2 g2 efs → prim_step' (K e1) σ1 g1 κ (K e2) σ2 g2 efs;
    fill_step_inv' e1' σ1 g1 κ e2 σ2 g2 efs :
      to_val e1' = None → prim_step' (K e1') σ1 g1 κ e2 σ2 g2 efs →
      ∃ e2', e2 = K e2' ∧ prim_step' e1' σ1 g1 κ e2' σ2 g2 efs
  }.

Lemma fill_comp' K1 K2 e : fill' K1 (fill' K2 e) = fill' (comp_ectx K1 K2) e.
Admitted.

Lemma head_redex_unique K K' e e' σ g :
  fill' K e = fill' K' e' →
  head_reducible e σ g →
  head_reducible e' σ g →
  K = K' ∧ e = e'.
Admitted.

Global Instance ectx_lang_ctx' K : LanguageCtx' (fill K).
Admitted.

Instance id_ctx' : LanguageCtx' (fun x => x).
Admitted.

Instance comp_ctx' K K':
  LanguageCtx' K →
  LanguageCtx' K' →
  LanguageCtx' (λ x, K' (K x)).
Admitted.

Lemma stuck'_fill K `{Hctx: LanguageCtx' K}  e σ g :
  stuck' e σ g → stuck' (K e) σ g.
Admitted.

Definition trace_observable e r σ g tr :=
  ∃ σ2 g2 t2 stat, erased_rsteps (CS:=goose_crash_lang) r ([e], (σ, g)) (t2, (σ2, g2)) stat ∧ σ2.(trace) = tr.
Definition trace_prefix (tr: Trace) (tr': Trace) : Prop. exact (prefix tr tr'). Defined.

Lemma ExternalOp_fill_inv K o e1 e2:
  ExternalOp o e1 = fill K e2 →
  (ExternalOp o e1 = e2 ∨ ∃ K1 K2, K = K1 ++ K2 ∧ e1 = fill K1 e2).
Admitted.

Lemma ExternalOp_fill_item_inv Ki o e1 e2:
  ExternalOp o e1 = fill_item Ki e2 →
  e1 = e2.
Admitted.

Lemma Panic_fill_item_inv Ki msg e:
  Primitive0 (PanicOp msg) = fill_item Ki e →
  False.
Admitted.

Lemma Var_fill_item_inv Ki x e:
  Var x = fill_item Ki e →
  False.
Admitted.

Lemma ExternalOp_sub_redexes o e:
  is_Some (to_val e) →
  sub_redexes_are_values (ExternalOp o e).
Admitted.

Lemma Var_sub_redexes x:
  sub_redexes_are_values (Var x).
Admitted.

Lemma stuck_ExternalOp' σ g o e:
  is_Some (to_val e) →
  head_irreducible' (ExternalOp o e) σ g →
  stuck' (ExternalOp o e) σ g.
Admitted.

Lemma stuck_Var σ g x :
  stuck (Var x) σ g.
Admitted.

Lemma stuck_ExternalOp σ g o e:
  is_Some (to_val e) →
  head_irreducible (ExternalOp o e) σ g →
  stuck (ExternalOp o e) σ g.
Admitted.

Lemma stuck_Panic' σ g msg:
  stuck' (Primitive0 (PanicOp msg)) σ g.
Admitted.

Lemma stuck_Panic σ g msg:
  stuck (Primitive0 (PanicOp msg)) σ g.
Admitted.

Lemma atomically_not_stuck_body_safe (l: val) e σ g :
  ¬ stuck (Atomically (of_val l) e) σ g →
  prim_step'_safe e σ g.
Admitted.

Definition null_non_alloc {V} (h : gmap loc V) :=
  ∀ off, h !! (addr_plus_off null off) = None.

Definition neg_non_alloc {V} (h : gmap loc V) :=
  ∀ l, is_Some (h !! l) → 0 < loc_car l.

Lemma fresh_alloc_equiv_null_non_alloc σ v:
  null_non_alloc (<[fresh_locs (dom (gset loc) σ.(heap)):=v]> σ.(heap)) ↔
  null_non_alloc (σ.(heap)).
Admitted.

Lemma upd_equiv_null_non_alloc σ l v:
  is_Some (heap σ !! l) →
  null_non_alloc (<[l:=v]> σ.(heap)) ↔
  null_non_alloc (σ.(heap)).
Admitted.

End goose.

Bind Scope expr_scope with expr.
Bind Scope val_scope with val.

Notation Panic s := (Primitive0 (PanicOp s)).
Notation ArbitraryInt := (Primitive0 ArbitraryIntOp).
Notation AllocN := (Primitive2 AllocNOp).
Notation PrepareWrite := (Primitive1 PrepareWriteOp).
Notation FinishStore := (Primitive2 FinishStoreOp).
Notation StartRead := (Primitive1 StartReadOp).
Notation FinishRead := (Primitive1 FinishReadOp).
Notation Load := (Primitive1 LoadOp).
Notation Input := (Primitive1 InputOp).
Notation Output := (Primitive1 OutputOp).
Notation nonAtomic T := (naMode * T)%type.

End lang.

End Perennial_DOT_goose_lang_DOT_lang_WRAPPED.
Module Export Perennial_DOT_goose_lang_DOT_lang.
Module Export Perennial.
Module Export goose_lang.
Module Export lang.
Include Perennial_DOT_goose_lang_DOT_lang_WRAPPED.lang.
End lang.

End goose_lang.

End Perennial.

End Perennial_DOT_goose_lang_DOT_lang.

Module Export Perennial_DOT_goose_lang_DOT_notation_WRAPPED.
Module Export notation.
Export Perennial.goose_lang.lang.

Notation "# l" := (LitV l%Z%V%stdpp) (at level 8, format "# l").

Notation "()" := LitUnit : val_scope.

End notation.
Module Export Perennial.
Module Export goose_lang.
Module Export notation.
Include Perennial_DOT_goose_lang_DOT_notation_WRAPPED.notation.
End notation.

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

  | ptrT

  | structRefT (ts: list ty)

  | mapValT (vt: ty)
  | extT (x: ext_tys)
  .

End val_types.

Class ext_types (ext:ffi_syntax) :=
  { val_tys :> val_types;

    get_ext_tys: val -> ty * ty -> Prop;
  }.

Module Export Perennial_DOT_goose_lang_DOT_lifting_WRAPPED.
Module Export lifting.
Import iris.algebra.lib.frac_auth.
Import iris.algebra.numbers.
Import iris.algebra.excl.
Export Perennial.program_logic.weakestpre.
Export Perennial.base_logic.lib.frac_coPset.
Export Perennial.algebra.na_heap.
Export Perennial.goose_lang.notation.

Class ffi_interp (ffi: ffi_model) :=
  { ffiLocalGS: gFunctors -> Set;
    ffiGlobalGS: gFunctors -> Set;
    ffi_global_ctx: ∀ `{ffiGlobalGS Σ}, ffi_global_state -> iProp Σ;
    ffi_local_ctx: ∀ `{ffiLocalGS Σ}, ffi_state -> iProp Σ;
    ffi_global_start: ∀ `{ffiGlobalGS Σ}, ffi_global_state -> iProp Σ;
    ffi_local_start: ∀ `{ffiLocalGS Σ}, ffi_state -> iProp Σ;

    ffi_restart: ∀ `{ffiLocalGS Σ}, ffi_state -> iProp Σ;
    ffi_crash_rel: ∀ Σ, ffiLocalGS Σ → ffi_state → ffiLocalGS Σ → ffi_state → iProp Σ;
  }.

Arguments ffi_local_ctx {ffi FfiInterp Σ} : rename.
Arguments ffi_global_ctx {ffi FfiInterp Σ} : rename.

Section goose_lang.
Context `{ffi_sem: ffi_semantics}.
Context `{!ffi_interp ffi}.

Definition traceO := leibnizO (list event).
Definition OracleO := leibnizO (Oracle).

Record tr_names := {
  trace_name : gname;
  oracle_name : gname;
}.

Class traceGS (Σ: gFunctors) := {
  trace_inG :> inG Σ (authR (optionUR (exclR traceO)));
  oracle_inG :> inG Σ (authR (optionUR (exclR OracleO)));
  trace_tr_names : tr_names;
}.

Definition trace_auth `{hT: traceGS Σ} (l: Trace) :=
  own (trace_name (trace_tr_names)) (● (Excl' (l: traceO))).
Definition oracle_auth `{hT: traceGS Σ} (o: Oracle) :=
  own (oracle_name (trace_tr_names)) (● (Excl' (o: OracleO))).

Record cr_names := {
  credit_name : gname;
  coPset_name : gname;
}.

Class creditGS (Σ: gFunctors) := {
  credit_inG :> inG Σ (authR natUR);
  frac_coPset_inG :> inG Σ (frac_coPsetR);
  credit_cr_names : cr_names;
}.

Section creditGS_defs.
Context `{creditGS Σ}.
Definition cred_frag (n : nat) : iProp Σ.
Admitted.
Definition cred_auth (ns : nat) : iProp Σ.
Admitted.
Definition pinv_tok q E := ownfCP (coPset_name (credit_cr_names)) q E.

Definition cred_interp ns : iProp Σ :=
  cred_auth ns ∗ cred_frag 0.

End creditGS_defs.

Class gooseGlobalGS Σ := GooseGlobalGS {
  goose_invGS : invGS Σ;
  goose_creditGS :> creditGS Σ;
  goose_ffiGlobalGS : ffiGlobalGS Σ;
}.

Class gooseLocalGS Σ := GooseLocalGS {
  goose_crashGS : crashGS Σ;
  goose_ffiLocalGS : ffiLocalGS Σ;
  goose_na_heapGS :> na_heapGS loc val Σ;
  goose_traceGS :> traceGS Σ;
}.
Definition tls (na: naMode) : lock_state.
Admitted.

Definition borrowN := nroot.@"borrow".
Definition crash_borrow_ginv_number : nat.
Admitted.
Definition crash_borrow_ginv `{!invGS Σ} `{creditGS Σ}
  := (inv borrowN (cred_frag crash_borrow_ginv_number)).

Global Program Instance goose_irisGS `{G: !gooseGlobalGS Σ}:
  irisGS goose_lang Σ := {
  iris_invGS := goose_invGS;
  num_laters_per_step := (λ n, 3 ^ (n + 1))%nat;
  step_count_next := (λ n, 10 * (n + 1))%nat;
  global_state_interp g ns mj D κs :=
    (ffi_global_ctx goose_ffiGlobalGS g ∗
     @crash_borrow_ginv _ goose_invGS _ ∗
     cred_interp ns ∗
     ⌜(/ 2 < mj ≤ 1) ⌝%Qp ∗
     pinv_tok mj D)%I;
  fork_post _ := True%I;
}.
Admit Obligations.

Global Program Instance goose_generationGS `{L: !gooseLocalGS Σ}:
  generationGS goose_lang Σ := {
  iris_crashGS := goose_crashGS;
  state_interp σ nt :=
    (na_heap_ctx tls σ.(heap) ∗ ffi_local_ctx goose_ffiLocalGS σ.(world)
      ∗ trace_auth σ.(trace) ∗ oracle_auth σ.(oracle))%I;
}.

End goose_lang.

End lifting.
Module Export Perennial.
Module Export goose_lang.
Module Export lifting.
Include Perennial_DOT_goose_lang_DOT_lifting_WRAPPED.lifting.
End lifting.
Import RecordUpdate.RecordSet.
Import Perennial.algebra.gen_heap_names.
Import Perennial.program_logic.ectx_lifting.
Import Perennial.Helpers.Transitions.
Import Perennial.goose_lang.lifting.

Inductive DiskOp := ReadOp | WriteOp | SizeOp.
Instance eq_DiskOp : EqDecision DiskOp.
Admitted.

Instance DiskOp_fin : Countable DiskOp.
Admitted.

Definition disk_op : ffi_syntax.
Proof.
  refine (mkExtOp DiskOp _ _ () _ _).
Defined.
Definition disk_ty: ext_types disk_op.
Admitted.
Definition block_bytes: nat.
Admitted.
Definition Block := vec byte block_bytes.

Definition disk_state := gmap Z Block.

Definition disk_model : ffi_model.
Proof.
  refine (mkFfiModel disk_state () _ _).
Defined.
Definition Block_to_vals {ext: ffi_syntax} (bl:Block) : list val.
Admitted.

Class diskGS Σ := DiskGS
  { diskG_gen_heapG :> gen_heap.gen_heapGS Z Block Σ; }.

  Existing Instances disk_op disk_model disk_ty.

  Existing Instances r_mbind r_fmap.
Definition disk_size (d: gmap Z Block): Z.
Admitted.
Definition ffi_step (op: DiskOp) (v: val): transition (state*global_state) expr.
exact (match op, v with
    | ReadOp, LitV (LitInt a) =>
      b ← reads (λ '(σ,g), σ.(world) !! int.Z a) ≫= unwrap;
      l ← allocateN;
      modify (λ '(σ,g), (state_insert_list l (Block_to_vals b) σ, g));;
      ret $ Val $ #(LitLoc l)
    | WriteOp, PairV (LitV (LitInt a)) (LitV (LitLoc l)) =>
      _ ← reads (λ '(σ,g), σ.(world) !! int.Z a) ≫= unwrap;

      b ← suchThat (gen:=fun _ _ => None) (λ '(σ,g) b, (forall (i:Z), 0 <= i -> i < 4096 ->
                match σ.(heap) !! (l +ₗ i) with
                | Some (Reading _, v) => Block_to_vals b !! Z.to_nat i = Some v
                | _ => False
                end));
      modify (λ '(σ,g), (set world <[ int.Z a := b ]> σ, g));;
      ret $ Val $ #()
    | SizeOp, LitV LitUnit =>
      sz ← reads (λ '(σ,g), disk_size σ.(world));
      ret $ Val $ LitV $ LitInt (word.of_Z sz)
    | _, _ => undefined
    end).
Defined.

  Instance disk_semantics : ffi_semantics disk_op disk_model :=
    { ffi_step := ffi_step;
      ffi_crash_step := eq; }.

  Program Instance disk_interp: ffi_interp disk_model :=
    {| ffiLocalGS := diskGS;
       ffiGlobalGS _ := ()%type;
       ffi_local_ctx Σ _ (d: @ffi_state disk_model) := gen_heap.gen_heap_interp d;
       ffi_global_ctx _ _ _ := True%I;
       ffi_local_start Σ _ (d: @ffi_state disk_model) :=
                      ([∗ map] l↦v ∈ d, (gen_heap.mapsto (L:=Z) (V:=Block) l (DfracOwn 1) v))%I;
       ffi_global_start _ _ _ := True%I;
       ffi_restart := fun _ _ (d: @ffi_state disk_model) => True%I;
       ffi_crash_rel Σ hF1 σ1 hF2 σ2 := ⌜ hF1 = hF2 ∧ σ1 = σ2 ⌝%I;
    |}.
  Context `{!gooseGlobalGS Σ, !gooseLocalGS Σ}.
Instance goose_diskGS : diskGS Σ.
exact (goose_ffiLocalGS).
Defined.

  Notation "l d↦{ dq } v" := (gen_heap.mapsto (L:=Z) (V:=Block) l dq v%V)
                             (at level 20, dq at level 50, format "l  d↦{ dq }  v") : bi_scope.

  Ltac inv_head_step :=
    repeat match goal with
        | _ => progress simplify_map_eq/=
        | H : to_val _ = Some _ |- _ => apply of_to_val in H
        | H : head_step ?e _ _ _ _ _ _ _ |- _ =>
          try (is_var e; fail 1);
          inversion H; subst; clear H
        | H : ffi_step _ _ _ _ _ |- _ =>
          inversion H; subst; clear H
        end.

  Definition mapsto_block (l: loc) (q: Qp) (b: Block) :=
    ([∗ map] l ↦ v ∈ heap_array l (Block_to_vals b), l ↦{q} v)%I.

  Lemma wp_ReadOp s E (a: u64) q b :
    {{{ ▷ int.Z a d↦{q} b }}}
      ExternalOp ReadOp (Val $ LitV $ LitInt a) @ s; E
    {{{ l, RET LitV (LitLoc l); int.Z a d↦{q} b ∗
                                  mapsto_block l 1 b }}}.
  Proof.
    iIntros (Φ) ">Ha HΦ".
iApply wp_lift_atomic_head_step_no_fork; first by auto.
    iIntros (σ1 g1 ns mj D κ κs nt) "(Hσ&Hd&Htr) Hg !>".
    cbv [ffi_local_ctx disk_interp].
    iDestruct (@gen_heap_valid with "Hd Ha") as %?.
    iSplit.
    {
 iPureIntro.
      eexists _, _, _, _, _; simpl.
      constructor 1.
      rewrite /head_step /=.
      monad_simpl.
      simpl.
      monad_simpl.
      econstructor; [ eapply relation.suchThat_gen0; reflexivity | ].
      monad_simpl.
}
    iNext; iIntros (v2 σ2 g2 efs Hstep).
    apply head_step_atomic_inv in Hstep; [ | by inversion 1 ].
    iMod (global_state_interp_le with "Hg") as "$".
    {
 apply step_count_next_incr.
}
    inv_head_step.
    monad_inv.
    iMod (na_heap_alloc_list tls _ l (Block_to_vals b) (Reading O) with "Hσ")
      as "(Hσ & Hblock & Hl)".
