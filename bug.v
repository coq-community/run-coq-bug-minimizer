(* -*- mode: coq; coq-prog-args: ("-emacs" "-w" "-ssr-search-moved" "-w" "-deprecated-hint-without-locality" "-w" "-deprecated-instance-without-locality" "-w" "-deprecated-hint-rewrite-without-locality" "-w" "+deprecated-tactic-notation" "-w" "-notation-overridden,-redundant-canonical-projection" "-w" "-deprecated-native-compiler-option" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/src" "Perennial" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/stdpp/theories" "stdpp" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/iris/iris" "iris" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/iris/iris_deprecated" "iris.deprecated" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/iris/iris_staging" "iris.staging" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/iris/iris_heap_lang" "iris.heap_lang" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/coqutil/src/coqutil" "coqutil" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/Goose" "Goose" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/record-update/src" "RecordUpdate" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/coq-tactical/src" "Tactical" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/iris-named-props/src" "iris_named_props" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-top" "bug_01" "-native-compiler" "ondemand") -*- *)
(* File reduced by coq-bug-finder from original input, then from 738 lines to 49 lines, then from 288 lines to 475 lines, then from 479 lines to 110 lines, then from 349 lines to 841 lines, then from 844 lines to 110 lines, then from 346 lines to 1710 lines, then from 1712 lines to 183 lines, then from 411 lines to 1059 lines, then from 1063 lines to 452 lines, then from 485 lines to 254 lines, then from 480 lines to 590 lines, then from 593 lines to 254 lines, then from 478 lines to 716 lines, then from 720 lines to 268 lines, then from 491 lines to 2117 lines, then from 2118 lines to 547 lines *)
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
Require Perennial.program_logic.weakestpre.
Require Perennial.base_logic.lib.frac_coPset.
Require Perennial.algebra.na_heap.
Require stdpp.binders.
Require Perennial.Helpers.Transitions.
Require Perennial.goose_lang.locations.
Require Perennial.Helpers.Integers.
Module Export Perennial_DOT_goose_lang_DOT_lang_WRAPPED.
Module Export lang.
Export stdpp.binders.
Import Perennial.Helpers.Transitions.
Export Perennial.goose_lang.locations.
Export Perennial.Helpers.Integers.

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

Section goose.

End goose.

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
