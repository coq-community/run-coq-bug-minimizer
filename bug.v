(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "-notation-overridden" "-w" "-redundant-canonical-projection" "-w" "-deprecated-native-compiler-option" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/iris_examples/theories" "iris_examples" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Autosubst" "Autosubst" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/iris" "iris" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/stdpp" "stdpp" "-top" "Top.bug_01" "-native-compiler" "ondemand") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 81 lines to 59 lines, then from 72 lines to 296 lines, then from 301 lines to 73 lines, then from 86 lines to 644 lines, then from 649 lines to 86 lines, then from 99 lines to 483 lines, then from 488 lines to 129 lines, then from 142 lines to 619 lines, then from 624 lines to 125 lines, then from 138 lines to 893 lines, then from 898 lines to 138 lines, then from 151 lines to 623 lines, then from 628 lines to 397 lines, then from 409 lines to 177 lines, then from 190 lines to 333 lines, then from 338 lines to 202 lines, then from 215 lines to 546 lines, then from 551 lines to 220 lines, then from 233 lines to 935 lines, then from 938 lines to 273 lines, then from 286 lines to 670 lines, then from 675 lines to 610 lines, then from 610 lines to 303 lines, then from 316 lines to 874 lines, then from 879 lines to 529 lines, then from 539 lines to 523 lines, then from 536 lines to 727 lines, then from 732 lines to 528 lines, then from 541 lines to 785 lines, then from 790 lines to 821 lines, then from 819 lines to 589 lines, then from 602 lines to 1005 lines, then from 1010 lines to 669 lines, then from 677 lines to 664 lines, then from 677 lines to 1187 lines, then from 1191 lines to 616 lines, then from 629 lines to 1264 lines, then from 1269 lines to 648 lines, then from 661 lines to 1069 lines, then from 1074 lines to 819 lines, then from 832 lines to 700 lines, then from 713 lines to 1036 lines, then from 1041 lines to 716 lines, then from 729 lines to 1095 lines, then from 1100 lines to 735 lines, then from 748 lines to 1226 lines, then from 1231 lines to 781 lines, then from 794 lines to 1229 lines, then from 1234 lines to 806 lines, then from 819 lines to 1224 lines, then from 1229 lines to 1102 lines *)
(* coqc version 8.18+alpha compiled with OCaml 4.14.0
   coqtop version runner-q6hytnfs-project-6138686-concurrent-0:/builds/coq/coq/_build/default,(HEAD detached at 41fd2ab) (41fd2ab2f7d875b43ff3442483386100b081bd29)
   Expected coqc runtime on this file: 7.038 sec *)
Require Coq.Program.Tactics.
Require Coq.Arith.Plus.
Require Coq.Lists.List.
Require Coq.Logic.FunctionalExtensionality.
Require Autosubst.Autosubst_Basics.
Require Autosubst.Autosubst_MMap.
Require Autosubst.Autosubst_Classes.
Require Autosubst.Autosubst_Tactics.
Require Autosubst.Autosubst_Lemmas.
Require Autosubst.Autosubst_Derive.
Require Autosubst.Autosubst_MMapInstances.
Require Autosubst.Autosubst.
Require Coq.Bool.Bool.
Require Coq.Classes.Morphisms.
Require Coq.Classes.RelationClasses.
Require Coq.Init.Byte.
Require Coq.Init.Peano.
Require Coq.Logic.EqdepFacts.
Require Coq.NArith.NArith.
Require Coq.Numbers.Natural.Peano.NPeano.
Require Coq.PArith.PArith.
Require Coq.Program.Basics.
Require Coq.Program.Syntax.
Require Coq.QArith.QArith.
Require Coq.QArith.QArith_base.
Require Coq.QArith.Qcanon.
Require Coq.Setoids.Setoid.
Require Coq.Sorting.Permutation.
Require Coq.Strings.Ascii.
Require Coq.Strings.String.
Require Coq.Unicode.Utf8.
Require Coq.ZArith.ZArith.
Require Coq.micromega.Lia.
Require Coq.ssr.ssreflect.
Require Ltac2.Ltac2.
Require stdpp.options.
Require stdpp.base.
Require stdpp.proof_irrel.
Require stdpp.decidable.
Require stdpp.tactics.
Require stdpp.option.
Require stdpp.numbers.
Require stdpp.list.
Require stdpp.list_numbers.
Require stdpp.fin.
Require stdpp.well_founded.
Require stdpp.countable.
Require stdpp.vector.
Require stdpp.finite.
Require stdpp.orders.
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
Require iris.algebra.agree.
Require iris.algebra.updates.
Require iris.algebra.local_updates.
Require iris.algebra.proofmode_classes.
Require iris.algebra.frac.
Require iris.algebra.dfrac.
Require stdpp.functions.
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
Require stdpp.coPset.
Require iris.algebra.coPset.
Require iris.algebra.cofe_solver.
Require iris.algebra.csum.
Require iris.algebra.excl.
Require iris.algebra.functions.
Require iris.algebra.list.
Require iris.algebra.gset.
Require iris.algebra.gmap.
Require iris.algebra.lib.dfrac_agree.
Require iris.algebra.lib.excl_auth.
Require iris.algebra.lib.gmap_view.
Require iris.algebra.numbers.
Require iris.algebra.reservation_map.
Require iris.bi.notation.
Require iris.bi.interface.
Require iris.bi.derived_connectives.
Require iris.bi.extensions.
Require iris.bi.derived_laws.
Require iris.bi.derived_laws_later.
Require iris.bi.big_op.
Require iris.bi.internal_eq.
Require iris.bi.plainly.
Require iris.bi.updates.
Require iris.base_logic.upred.
Require iris.base_logic.bi.
Require iris.bi.embedding.
Require iris.bi.bi.
Require iris.base_logic.derived.
Require iris.base_logic.algebra.
Require stdpp.namespaces.
Require iris.proofmode.base.
Require iris.proofmode.ident_name.
Require iris.proofmode.modalities.
Require iris.proofmode.classes.
Require iris.base_logic.proofmode.
Require iris.base_logic.base_logic.
Require iris.base_logic.lib.iprop.
Require stdpp.hlist.
Require stdpp.telescopes.
Require iris.bi.telescopes.
Require iris.proofmode.tokens.
Require iris.proofmode.sel_patterns.
Require iris.proofmode.intro_patterns.
Require iris.proofmode.spec_patterns.
Require iris.proofmode.environments.
Require iris.proofmode.modality_instances.
Require iris.proofmode.coq_tactics.
Require iris.proofmode.reduction.
Require iris.proofmode.string_ident.
Require iris.proofmode.notation.
Require iris.proofmode.ltac_tactics.
Require iris.proofmode.classes_make.
Require iris.proofmode.class_instances.
Require stdpp.nat_cancel.
Require iris.proofmode.class_instances_later.
Require iris.proofmode.class_instances_updates.
Require iris.proofmode.class_instances_embedding.
Require iris.proofmode.class_instances_plainly.
Require iris.proofmode.class_instances_internal_eq.
Require iris.proofmode.class_instances_frame.
Require iris.proofmode.class_instances_make.
Require iris.proofmode.proofmode.
Require iris.proofmode.tactics.
Require iris.base_logic.lib.own.
Require iris.base_logic.lib.later_credits.
Require iris.base_logic.lib.wsat.

Declare ML Module "coq-core.plugins.ltac".
Module Export AdmitTactic.
Module Import LocalFalse.
Inductive False : Prop := .
End LocalFalse.
Axiom proof_admitted : False.
Global Set Default Proof Mode "Classic".
Tactic Notation "admit" := abstract case proof_admitted.
End AdmitTactic.

Module Export iris_DOT_base_logic_DOT_lib_DOT_fancy_updates_WRAPPED.
Module Export fancy_updates.
Export stdpp.coPset.
Import iris.algebra.gmap.
Import iris.algebra.auth.
Import iris.algebra.agree.
Import iris.algebra.gset.
Import iris.algebra.coPset.
Import iris.proofmode.proofmode.
Export iris.base_logic.lib.own.
Import iris.base_logic.lib.wsat.
Export iris.base_logic.lib.later_credits.
Import iris.prelude.options.
Export wsatGS.
Import uPred.
Import le_upd_if.

 
Inductive has_lc := HasLc | HasNoLc.

Class invGpreS (Σ : gFunctors) : Set := InvGpreS {
  invGpreS_wsat : wsatGpreS Σ;
  invGpreS_lc : lcGpreS Σ;
}.

Class invGS_gen (hlc : has_lc) (Σ : gFunctors) : Set := InvG {
  invGS_wsat : wsatGS Σ;
  invGS_lc : lcGS Σ;
}.
Global Hint Mode invGS_gen - - : typeclass_instances.
Global Hint Mode invGpreS - : typeclass_instances.
Local Existing Instances invGpreS_wsat invGpreS_lc.
 
Global Existing Instances invGS_lc invGS_wsat.

Notation invGS := (invGS_gen HasLc).
Definition invΣ : gFunctors. exact (#[wsatΣ; lcΣ]). Defined.
Global Instance subG_invΣ {Σ} : subG invΣ Σ → invGpreS Σ.
Admitted.

Local Definition uPred_fupd_def `{!invGS_gen hlc Σ} (E1 E2 : coPset) (P : iProp Σ) : iProp Σ :=
  wsat ∗ ownE E1 -∗ le_upd_if (if hlc is HasLc then true else false) (◇ (wsat ∗ ownE E2 ∗ P)).
Local Definition uPred_fupd_aux : seal (@uPred_fupd_def).
Admitted.
Definition uPred_fupd := uPred_fupd_aux.(unseal).
Global Arguments uPred_fupd {hlc Σ _}.
Local Lemma uPred_fupd_unseal `{!invGS_gen hlc Σ} : @fupd _ uPred_fupd = uPred_fupd_def.
Admitted.

Lemma uPred_fupd_mixin `{!invGS_gen hlc Σ} : BiFUpdMixin (uPredI (iResUR Σ)) uPred_fupd.
Admitted.
Global Instance uPred_bi_fupd `{!invGS_gen hlc Σ} : BiFUpd (uPredI (iResUR Σ)). exact ({| bi_fupd_mixin := uPred_fupd_mixin |}). Defined.

Global Instance uPred_bi_bupd_fupd `{!invGS_gen hlc Σ} : BiBUpdFUpd (uPredI (iResUR Σ)).
Admitted.

 
Global Instance uPred_bi_fupd_plainly_no_lc `{!invGS_gen HasNoLc Σ} :
  BiFUpdPlainly (uPredI (iResUR Σ)).
Admitted.

 

 
Lemma lc_fupd_elim_later `{!invGS_gen HasLc Σ} E P :
   £ 1 -∗ (▷ P) -∗ |={E}=> P.
Admitted.

 
Lemma lc_fupd_add_later `{!invGS_gen HasLc Σ} E1 E2 P :
  £ 1 -∗ (▷ |={E1, E2}=> P) -∗ |={E1, E2}=> P.
Admitted.

 

 
Lemma fupd_soundness_no_lc `{!invGpreS Σ} E1 E2 (P : iProp Σ) `{!Plain P} m :
  (∀ `{Hinv: !invGS_gen HasNoLc Σ}, £ m ⊢ |={E1,E2}=> P) → ⊢ P.
Admitted.

Lemma fupd_soundness_lc `{!invGpreS Σ} n E1 E2 (P : iProp Σ) `{!Plain P} :
  (∀ `{Hinv: !invGS_gen HasLc Σ}, £ n ⊢@{iPropI Σ} |={E1,E2}=> P) → ⊢ P.
Admitted.

 
Lemma fupd_soundness_gen `{!invGpreS Σ} (P : iProp Σ) `{!Plain P}
  (hlc : has_lc) n E1 E2 :
  (∀ `{Hinv : invGS_gen hlc Σ},
    £ n ={E1,E2}=∗ P) →
  ⊢ P.
Admitted.

 

Lemma step_fupdN_soundness_no_lc `{!invGpreS Σ} (P : iProp Σ) `{!Plain P} n m :
  (∀ `{Hinv: !invGS_gen HasNoLc Σ}, £ m ⊢@{iPropI Σ} |={⊤,∅}=> |={∅}▷=>^n P) →
  ⊢ P.
Admitted.

Lemma step_fupdN_soundness_no_lc' `{!invGpreS Σ} (P : iProp Σ) `{!Plain P} n m :
  (∀ `{Hinv: !invGS_gen HasNoLc Σ}, £ m ⊢@{iPropI Σ} |={⊤}[∅]▷=>^n P) →
  ⊢ P.
Admitted.

Lemma step_fupdN_soundness_lc `{!invGpreS Σ} (P : iProp Σ) `{!Plain P} n m :
  (∀ `{Hinv: !invGS_gen HasLc Σ}, £ m ⊢@{iPropI Σ} |={⊤,∅}=> |={∅}▷=>^n P) →
  ⊢ P.
Admitted.

Lemma step_fupdN_soundness_lc' `{!invGpreS Σ} (P : iProp Σ) `{!Plain P} n m :
  (∀ `{Hinv: !invGS_gen hlc Σ}, £ m ⊢@{iPropI Σ} |={⊤}[∅]▷=>^n P) →
  ⊢ P.
Admitted.

 
Lemma step_fupdN_soundness_gen `{!invGpreS Σ} (P : iProp Σ) `{!Plain P}
  (hlc : has_lc) (n m : nat) :
  (∀ `{Hinv : invGS_gen hlc Σ},
    £ m ={⊤,∅}=∗ |={∅}▷=>^n P) →
  ⊢ P.
Admitted.

End fancy_updates.

End iris_DOT_base_logic_DOT_lib_DOT_fancy_updates_WRAPPED.
Module Export iris_DOT_base_logic_DOT_lib_DOT_fancy_updates.
Module Export iris.
Module Export base_logic.
Module Export lib.
Module Export fancy_updates.
Include iris_DOT_base_logic_DOT_lib_DOT_fancy_updates_WRAPPED.fancy_updates.
End fancy_updates.

End lib.

End base_logic.

End iris.

End iris_DOT_base_logic_DOT_lib_DOT_fancy_updates.
Import iris.algebra.lib.gmap_view.
Export iris.base_logic.lib.own.

Class ghost_mapG Σ (K V : Type) `{Countable K} := GhostMapG {
  ghost_map_inG : inG Σ (gmap_viewR K (leibnizO V));
}.

Section definitions.
  Context `{ghost_mapG Σ K V}.
Local Definition ghost_map_auth_def
      (γ : gname) (q : Qp) (m : gmap K V) : iProp Σ.
Admitted.
  Local Definition ghost_map_auth_aux : seal (@ghost_map_auth_def).
Admitted.
  Definition ghost_map_auth := ghost_map_auth_aux.(unseal).
Local Definition ghost_map_elem_def
      (γ : gname) (k : K) (dq : dfrac) (v : V) : iProp Σ.
Admitted.
  Local Definition ghost_map_elem_aux : seal (@ghost_map_elem_def).
Admitted.
  Definition ghost_map_elem := ghost_map_elem_aux.(unseal).
End definitions.

Notation "k ↪[ γ ]{ dq } v" := (ghost_map_elem γ k dq v)
  (at level 20, γ at level 50, dq at level 50, format "k  ↪[ γ ]{ dq }  v") : bi_scope.
Notation "k ↪[ γ ]□ v" := (k ↪[γ]{DfracDiscarded} v)%I
  (at level 20, γ at level 50) : bi_scope.

Export stdpp.namespaces.
Import iris.algebra.reservation_map.

Class gen_heapGpreS (L V : Type) (Σ : gFunctors) `{Countable L} := {
  gen_heapGpreS_heap : ghost_mapG Σ L V;
  gen_heapGpreS_meta : ghost_mapG Σ L gname;
  gen_heapGpreS_meta_data : inG Σ (reservation_mapR (agreeR positiveO));
}.
Local Existing Instances gen_heapGpreS_meta_data gen_heapGpreS_heap gen_heapGpreS_meta.

Class gen_heapGS (L V : Type) (Σ : gFunctors) `{Countable L} := GenHeapGS {
  gen_heap_inG : gen_heapGpreS L V Σ;
  gen_heap_name : gname;
  gen_meta_name : gname
}.
Local Existing Instance gen_heap_inG.
Global Arguments gen_heap_name {L V Σ _ _} _ : assert.
Global Arguments gen_meta_name {L V Σ _ _} _ : assert.

Section definitions.
  Context `{Countable L, hG : !gen_heapGS L V Σ}.

  Definition gen_heap_interp (σ : gmap L V) : iProp Σ := ∃ m : gmap L gname,

    ⌜ dom m ⊆ dom σ ⌝ ∗
    ghost_map_auth (gen_heap_name hG) 1 σ ∗
    ghost_map_auth (gen_meta_name hG) 1 m.

  Local Definition mapsto_def (l : L) (dq : dfrac) (v: V) : iProp Σ :=
    l ↪[gen_heap_name hG]{dq} v.
  Local Definition mapsto_aux : seal (@mapsto_def).
Admitted.
  Definition mapsto := mapsto_aux.(unseal).

  Local Definition meta_token_def (l : L) (E : coPset) : iProp Σ :=
    ∃ γm, l ↪[gen_meta_name hG]□ γm ∗ own γm (reservation_map_token E).
  Local Definition meta_token_aux : seal (@meta_token_def).
Admitted.
  Definition meta_token := meta_token_aux.(unseal).
End definitions.
Local Notation "l ↦ v" := (mapsto l (DfracOwn 1) v)
  (at level 20, format "l  ↦  v") : bi_scope.

Lemma gen_heap_init `{Countable L, !gen_heapGpreS L V Σ} σ :
  ⊢ |==> ∃ _ : gen_heapGS L V Σ,
    gen_heap_interp σ ∗ ([∗ map] l ↦ v ∈ σ, l ↦ v) ∗ ([∗ map] l ↦ _ ∈ σ, meta_token l ⊤).
Admitted.
Export iris.base_logic.lib.fancy_updates.

Local Definition inv_def `{!invGS_gen hlc Σ} (N : namespace) (P : iProp Σ) : iProp Σ :=
  □ ∀ E, ⌜↑N ⊆ E⌝ → |={E,E ∖ ↑N}=> ▷ P ∗ (▷ P ={E ∖ ↑N,E}=∗ True).
Local Definition inv_aux : seal (@inv_def).
Admitted.
Definition inv := inv_aux.(unseal).
Global Arguments inv {hlc Σ _} N P.

Section inv.
  Context `{!invGS_gen hlc Σ}.

  Global Instance inv_contractive N : Contractive (inv N).
Admitted.

  Global Instance inv_persistent N P : Persistent (inv N P).
Admitted.

  Lemma inv_alloc N E P : ▷ P ={E}=∗ inv N P.
Admitted.

End inv.
Delimit Scope expr_scope with E.

Inductive stuckness := NotStuck | MaybeStuck.

Class Wp (PROP EXPR VAL A : Type) :=
  wp : A → coPset → EXPR → (VAL → PROP) → PROP.

Notation "'WP' e @ s ; E {{ Φ } }" := (wp s E e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.

Notation "'WP' e @ s ; E {{ v , Q } }" := (wp s E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' 'WP'  e  '/' @  '[' s ;  '/' E  ']' '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e {{ v , Q } }" := (wp NotStuck ⊤ e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' 'WP'  e  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Module Export language.

Section language_mixin.
  Context {expr val state observation : Type}.
  Context (of_val : val → expr).
  Context (to_val : expr → option val).

  Context (prim_step : expr → state → list observation → expr → state → list expr → Prop).

  Record LanguageMixin := {
    mixin_to_of_val v : to_val (of_val v) = Some v;
    mixin_of_to_val e v : to_val e = Some v → of_val v = e;
    mixin_val_stuck e σ κ e' σ' efs : prim_step e σ κ e' σ' efs → to_val e = None
  }.
End language_mixin.

Structure language := Language {
  expr : Type;
  val : Type;
  state : Type;
  observation : Type;
  of_val : val → expr;
  to_val : expr → option val;
  prim_step : expr → state → list observation → expr → state → list expr → Prop;
  language_mixin : LanguageMixin of_val to_val prim_step
}.
Global Arguments of_val {_} _.
Global Arguments to_val {_} _.
Global Arguments prim_step {_} _ _ _ _ _ _.

Definition cfg (Λ : language) := (list (expr Λ) * state Λ)%type.

Section language.
  Context {Λ : language}.

  Definition reducible (e : expr Λ) (σ : state Λ) :=
    ∃ κ e' σ' efs, prim_step e σ κ e' σ' efs.
  Definition not_stuck (e : expr Λ) (σ : state Λ) :=
    is_Some (to_val e) ∨ reducible e σ.

  Inductive step (ρ1 : cfg Λ) (κ : list (observation Λ)) (ρ2 : cfg Λ) : Prop :=
    | step_atomic e1 σ1 e2 σ2 efs t1 t2 :
       ρ1 = (t1 ++ e1 :: t2, σ1) →
       ρ2 = (t1 ++ e2 :: t2 ++ efs, σ2) →
       prim_step e1 σ1 κ e2 σ2 efs →
       step ρ1 κ ρ2.

  Definition erased_step (ρ1 ρ2 : cfg Λ) := ∃ κ, step ρ1 κ ρ2.

End language.

End language.

Class irisGS_gen (hlc : has_lc) (Λ : language) (Σ : gFunctors) := IrisG {
  iris_invGS :> invGS_gen hlc Σ;

  state_interp : state Λ → nat → list (observation Λ) → nat → iProp Σ;

  fork_post : val Λ → iProp Σ;

  num_laters_per_step : nat → nat;

  state_interp_mono σ ns κs nt:
    state_interp σ ns κs nt ={∅}=∗ state_interp σ (S ns) κs nt
}.
Global Arguments IrisG {hlc Λ Σ}.

Notation irisGS := (irisGS_gen HasLc).
Local Definition wp_def `{!irisGS_gen hlc Λ Σ} : Wp (iProp Σ) (expr Λ) (val Λ) stuckness.
Admitted.
Local Definition wp_aux : seal (@wp_def).
Admitted.
Definition wp' := wp_aux.(unseal).
Global Existing Instance wp'.

Section wp.
Context `{!irisGS_gen hlc Λ Σ}.
Lemma wp_fupd s E e Φ : WP e @ s; E {{ v, |={E}=> Φ v }} ⊢ WP e @ s; E {{ Φ }}.
Admitted.
Lemma wp_wand_r s E e Φ Ψ :
  WP e @ s; E {{ Φ }} ∗ (∀ v, Φ v -∗ Ψ v) ⊢ WP e @ s; E {{ Ψ }}.
Admitted.
End wp.

Record adequate {Λ} (s : stuckness) (e1 : expr Λ) (σ1 : state Λ)
    (φ : val Λ → state Λ → Prop) := {
  adequate_result t2 σ2 v2 :
   rtc erased_step ([e1], σ1) (of_val v2 :: t2, σ2) → φ v2 σ2;
  adequate_not_stuck t2 σ2 e2 :
   s = NotStuck →
   rtc erased_step ([e1], σ1) (t2, σ2) →
   e2 ∈ t2 → not_stuck e2 σ2
}.

Lemma wp_adequacy_gen (hlc : has_lc) Σ Λ `{!invGpreS Σ} s e σ φ :
  (∀ `{Hinv : !invGS_gen hlc Σ} κs,
     ⊢ |={⊤}=> ∃
         (stateI : state Λ → list (observation Λ) → iProp Σ)
         (fork_post : val Λ → iProp Σ),
       let _ : irisGS_gen hlc Λ Σ :=
           IrisG Hinv (λ σ _ κs _, stateI σ κs) fork_post (λ _, 0)
                 (λ _ _ _ _, fupd_intro _ _)
       in
       stateI σ κs ∗ WP e @ s; ⊤ {{ v, ⌜φ v⌝ }}) →
  adequate s e σ (λ v _, φ v).
Admitted.

Definition wp_adequacy := wp_adequacy_gen HasLc.
Global Arguments wp_adequacy _ _ {_}.
Module Export ectx_language.

Section ectx_language_mixin.
  Context {expr val ectx state observation : Type}.
  Context (of_val : val → expr).
  Context (to_val : expr → option val).
  Context (empty_ectx : ectx).
  Context (comp_ectx : ectx → ectx → ectx).
  Context (fill : ectx → expr → expr).
  Context (head_step : expr → state → list observation → expr → state → list expr → Prop).

  Record EctxLanguageMixin := {
    mixin_to_of_val v : to_val (of_val v) = Some v;
    mixin_of_to_val e v : to_val e = Some v → of_val v = e;
    mixin_val_head_stuck e1 σ1 κ e2 σ2 efs :
      head_step e1 σ1 κ e2 σ2 efs → to_val e1 = None;

    mixin_fill_empty e : fill empty_ectx e = e;
    mixin_fill_comp K1 K2 e : fill K1 (fill K2 e) = fill (comp_ectx K1 K2) e;
    mixin_fill_inj K : Inj (=) (=) (fill K);
    mixin_fill_val K e : is_Some (to_val (fill K e)) → is_Some (to_val e);

    mixin_step_by_val K' K_redex e1' e1_redex σ1 κ e2 σ2 efs :
      fill K' e1' = fill K_redex e1_redex →
      to_val e1' = None →
      head_step e1_redex σ1 κ e2 σ2 efs →
      ∃ K'', K_redex = comp_ectx K' K'';

    mixin_head_ctx_step_val K e σ1 κ e2 σ2 efs :
      head_step (fill K e) σ1 κ e2 σ2 efs → is_Some (to_val e) ∨ K = empty_ectx;
  }.
End ectx_language_mixin.

Structure ectxLanguage := EctxLanguage {
  expr : Type;
  val : Type;
  ectx : Type;
  state : Type;
  observation : Type;

  of_val : val → expr;
  to_val : expr → option val;
  empty_ectx : ectx;
  comp_ectx : ectx → ectx → ectx;
  fill : ectx → expr → expr;
  head_step : expr → state → list observation → expr → state → list expr → Prop;

  ectx_language_mixin :
    EctxLanguageMixin of_val to_val empty_ectx comp_ectx fill head_step
}.
Global Arguments of_val {_} _.
Global Arguments to_val {_} _.
Global Arguments fill {_} _ _.
Global Arguments head_step {_} _ _ _ _ _ _.

Section ectx_language.
  Context {Λ : ectxLanguage}.

  Inductive prim_step (e1 : expr Λ) (σ1 : state Λ) (κ : list (observation Λ))
      (e2 : expr Λ) (σ2 : state Λ) (efs : list (expr Λ)) : Prop :=
    Ectx_step K e1' e2' :
      e1 = fill K e1' → e2 = fill K e2' →
      head_step e1' σ1 κ e2' σ2 efs → prim_step e1 σ1 κ e2 σ2 efs.

  Definition ectx_lang_mixin : LanguageMixin of_val to_val prim_step.
Admitted.
End ectx_language.
Definition LanguageOfEctx (Λ : ectxLanguage) : language.
exact (let '@EctxLanguage E V C St K of_val to_val empty comp fill head mix := Λ in
  @Language E V St K of_val to_val _
    (@ectx_lang_mixin (@EctxLanguage E V C St K of_val to_val empty comp fill head mix))).
Defined.

End ectx_language.

Section ectxi_language_mixin.
  Context {expr val ectx_item state observation : Type}.
  Context (of_val : val → expr).
  Context (to_val : expr → option val).
  Context (fill_item : ectx_item → expr → expr).
  Context (head_step : expr → state → list observation → expr → state → list expr → Prop).

  Record EctxiLanguageMixin := {
    mixin_to_of_val v : to_val (of_val v) = Some v;
    mixin_of_to_val e v : to_val e = Some v → of_val v = e;
    mixin_val_stuck e1 σ1 κ e2 σ2 efs : head_step e1 σ1 κ e2 σ2 efs → to_val e1 = None;

    mixin_fill_item_val Ki e : is_Some (to_val (fill_item Ki e)) → is_Some (to_val e);

    mixin_fill_item_inj Ki : Inj (=) (=) (fill_item Ki);

    mixin_fill_item_no_val_inj Ki1 Ki2 e1 e2 :
      to_val e1 = None → to_val e2 = None →
      fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2;

    mixin_head_ctx_step_val Ki e σ1 κ e2 σ2 efs :
      head_step (fill_item Ki e) σ1 κ e2 σ2 efs → is_Some (to_val e);
  }.
End ectxi_language_mixin.

Structure ectxiLanguage := EctxiLanguage {
  expr : Type;
  val : Type;
  ectx_item : Type;
  state : Type;
  observation : Type;

  of_val : val → expr;
  to_val : expr → option val;
  fill_item : ectx_item → expr → expr;
  head_step : expr → state → list observation → expr → state → list expr → Prop;

  ectxi_language_mixin :
    EctxiLanguageMixin of_val to_val fill_item head_step
}.

Global Arguments EctxiLanguage {_ _ _ _ _ _ _ _ _} _.
Global Arguments of_val {_} _.
Global Arguments to_val {_} _.
Global Arguments head_step {_} _ _ _ _ _ _.

Section ectxi_language.
  Context {Λ : ectxiLanguage}.
  Notation ectx := (list (ectx_item Λ)).
Definition fill (K : ectx) (e : expr Λ) : expr Λ.
Admitted.

  Definition ectxi_lang_ectx_mixin :
    EctxLanguageMixin of_val to_val [] (flip (++)) fill head_step.
Admitted.
End ectxi_language.
Definition EctxLanguageOfEctxi (Λ : ectxiLanguage) : ectxLanguage.
exact (let '@EctxiLanguage E V C St K of_val to_val fill head mix := Λ in
  @EctxLanguage E V (list C) St K of_val to_val _ _ _ _
    (@ectxi_lang_ectx_mixin (@EctxiLanguage E V C St K of_val to_val fill head mix))).
Defined.
Export Autosubst.Autosubst.

Reserved Notation "⟦ τ ⟧" (at level 0, τ at level 70).
Reserved Notation "⟦ τ ⟧ₑ" (at level 0, τ at level 70).
Reserved Notation "⟦ Γ ⟧*" (at level 0, Γ at level 70).

Module Export F_mu_ref_conc.
  Definition loc := positive.

  Inductive binop := Add | Sub | Mult | Eq | Le | Lt.

  Inductive expr :=
  | Var (x : var)
  | Rec (e : {bind 2 of expr})
  | App (e1 e2 : expr)
  | Lam (e : {bind expr})
  | LetIn (e1 : expr) (e2 : {bind expr})
  | Seq (e1 e2 : expr)

  | Unit
  | Nat (n : nat)
  | Bool (b : bool)
  | BinOp (op : binop) (e1 e2 : expr)

  | If (e0 e1 e2 : expr)

  | Pair (e1 e2 : expr)
  | Fst (e : expr)
  | Snd (e : expr)

  | InjL (e : expr)
  | InjR (e : expr)
  | Case (e0 : expr) (e1 : {bind expr}) (e2 : {bind expr})

  | Fold (e : expr)
  | Unfold (e : expr)

  | TLam (e : expr)
  | TApp (e : expr)

  | Pack (e : expr)
  | UnpackIn (e1 : expr) (e2 : {bind expr})

  | Fork (e : expr)

  | Loc (l : loc)
  | Alloc (e : expr)
  | Load (e : expr)
  | Store (e1 : expr) (e2 : expr)

  | CAS (e0 : expr) (e1 : expr) (e2 : expr)

  | FAA (e1 : expr) (e2 : expr).
  Global Instance Ids_expr : Ids expr.
Admitted.
  Global Instance Rename_expr : Rename expr.
Admitted.
  Global Instance Subst_expr : Subst expr.
Admitted.
  Global Instance SubstLemmas_expr : SubstLemmas expr.
Admitted.

  Notation "#♭ b" := (Bool b) (at level 20).
  Notation "#n n" := (Nat n) (at level 20).

  Inductive val :=
  | RecV (e : {bind 1 of expr})
  | LamV (e : {bind expr})
  | TLamV (e : {bind 1 of expr})
  | PackV (v : val)
  | UnitV
  | NatV (n : nat)
  | BoolV (b : bool)
  | PairV (v1 v2 : val)
  | InjLV (v : val)
  | InjRV (v : val)
  | FoldV (v : val)
  | LocV (l : loc).
Definition binop_eval (op : binop) : nat → nat → val.
Admitted.
Fixpoint of_val (v : val) : expr.
Admitted.
Fixpoint to_val (e : expr) : option val.
Admitted.

  Inductive ectx_item :=
  | AppLCtx (e2 : expr)
  | AppRCtx (v1 : val)
  | LetInCtx (e2 : expr)
  | SeqCtx (e2 : expr)
  | TAppCtx
  | PackCtx
  | UnpackInCtx (e2 : expr)
  | PairLCtx (e2 : expr)
  | PairRCtx (v1 : val)
  | BinOpLCtx (op : binop) (e2 : expr)
  | BinOpRCtx (op : binop) (v1 : val)
  | FstCtx
  | SndCtx
  | InjLCtx
  | InjRCtx
  | CaseCtx (e1 : {bind expr}) (e2 : {bind expr})
  | IfCtx (e1 : {bind expr}) (e2 : {bind expr})
  | FoldCtx
  | UnfoldCtx
  | AllocCtx
  | LoadCtx
  | StoreLCtx (e2 : expr)
  | StoreRCtx (v1 : val)
  | CasLCtx (e1 : expr)  (e2 : expr)
  | CasMCtx (v0 : val) (e2 : expr)
  | CasRCtx (v0 : val) (v1 : val)
  | FAALCtx (e2 : expr)
  | FAARCtx (v1 : val).
Definition fill_item (Ki : ectx_item) (e : expr) : expr.
Admitted.
Definition state : Type.
exact (gmap loc val).
Defined.

  Inductive head_step : expr → state → list Empty_set → expr → state → list expr → Prop :=

  | BetaS e1 e2 v2 σ :
      to_val e2 = Some v2 →
      head_step (App (Rec e1) e2) σ [] e1.[(Rec e1), e2/] σ []

  | LamBetaS e1 e2 v2 σ :
      to_val e2 = Some v2 →
      head_step (App (Lam e1) e2) σ [] e1.[e2/] σ []

  | LetInBetaS e1 e2 v2 σ :
      to_val e1 = Some v2 →
      head_step (LetIn e1 e2) σ [] e2.[e1/] σ []

  | SeqBetaS e1 e2 v2 σ :
      to_val e1 = Some v2 →
      head_step (Seq e1 e2) σ [] e2 σ []

  | FstS e1 v1 e2 v2 σ :
      to_val e1 = Some v1 → to_val e2 = Some v2 →
      head_step (Fst (Pair e1 e2)) σ [] e1 σ []
  | SndS e1 v1 e2 v2 σ :
      to_val e1 = Some v1 → to_val e2 = Some v2 →
      head_step (Snd (Pair e1 e2)) σ [] e2 σ []

  | CaseLS e0 v0 e1 e2 σ :
      to_val e0 = Some v0 →
      head_step (Case (InjL e0) e1 e2) σ [] e1.[e0/] σ []
  | CaseRS e0 v0 e1 e2 σ :
      to_val e0 = Some v0 →
      head_step (Case (InjR e0) e1 e2) σ [] e2.[e0/] σ []

  | BinOpS op a b σ :
      head_step (BinOp op (#n a) (#n b)) σ [] (of_val (binop_eval op a b)) σ []

  | IfFalse e1 e2 σ :
      head_step (If (#♭ false) e1 e2) σ [] e2 σ []
  | IfTrue e1 e2 σ :
      head_step (If (#♭ true) e1 e2) σ [] e1 σ []

  | Unfold_Fold e v σ :
      to_val e = Some v →
      head_step (Unfold (Fold e)) σ [] e σ []

  | TBeta e σ :
      head_step (TApp (TLam e)) σ [] e σ []

  | UnpackS e1 v e2 σ :
      to_val e1 = Some v →
      head_step (UnpackIn (Pack e1) e2) σ [] e2.[e1/] σ []

  | ForkS e σ:
      head_step (Fork e) σ [] Unit σ [e]

  | AllocS e v σ l :
     to_val e = Some v → σ !! l = None →
     head_step (Alloc e) σ [] (Loc l) (<[l:=v]>σ) []
  | LoadS l v σ :
     σ !! l = Some v →
     head_step (Load (Loc l)) σ [] (of_val v) σ []
  | StoreS l e v σ :
     to_val e = Some v → is_Some (σ !! l) →
     head_step (Store (Loc l) e) σ [] Unit (<[l:=v]>σ) []

  | CasFailS l e1 v1 e2 v2 vl σ :
     to_val e1 = Some v1 → to_val e2 = Some v2 →
     σ !! l = Some vl → vl ≠ v1 →
     head_step (CAS (Loc l) e1 e2) σ [] (#♭ false) σ []
  | CasSucS l e1 v1 e2 v2 σ :
     to_val e1 = Some v1 → to_val e2 = Some v2 →
     σ !! l = Some v1 →
     head_step (CAS (Loc l) e1 e2) σ [] (#♭ true) (<[l:=v2]>σ) []
  | FAAS l m e2 k σ :
      to_val e2 = Some (NatV k) →
      σ !! l = Some (NatV m) →
      head_step (FAA (Loc l) e2) σ [] (#n m) (<[l:=NatV (m + k)]>σ) [].

  Lemma lang_mixin : EctxiLanguageMixin of_val to_val fill_item head_step.
Admitted.
  Canonical Structure exprO := leibnizO expr.

Canonical Structure F_mu_ref_conc_ectxi_lang :=
  EctxiLanguage F_mu_ref_conc.lang_mixin.
Canonical Structure F_mu_ref_conc_ectx_lang :=
  EctxLanguageOfEctxi F_mu_ref_conc_ectxi_lang.
Canonical Structure F_mu_ref_conc_lang :=
  LanguageOfEctx F_mu_ref_conc_ectx_lang.

Class heapIG Σ := HeapIG {
  heapI_invG : invGS Σ;
  heapI_gen_heapG :> gen_heapGS loc val Σ;
}.

Global Instance heapIG_irisG `{heapIG Σ} : irisGS F_mu_ref_conc_lang Σ := {
  iris_invGS := heapI_invG;
  num_laters_per_step _ := 0;
  state_interp σ  _ _ _ := gen_heap_interp σ;
  fork_post _ := True%I;
  state_interp_mono _ _ _ _ := fupd_intro _ _
}.
Notation "l ↦ᵢ v" := (mapsto (L:=loc) (V:=val) l (DfracOwn 1) v)
  (at level 20, format "l  ↦ᵢ  v") : bi_scope.

Module Export iris_examples_DOT_logrel_DOT_F_mu_ref_conc_DOT_binary_DOT_rules_WRAPPED.
Module Export rules.
Import iris.algebra.excl.
Import iris.proofmode.proofmode.

Definition specN := nroot .@ "spec".
Definition tpoolUR : ucmra.
exact (gmapUR nat (exclR exprO)).
Defined.
Definition heapUR (L V : Type) `{Countable L} : ucmra.
exact (gmapUR L (prodR fracR (agreeR (leibnizO V)))).
Defined.
Definition cfgUR := prodUR tpoolUR (heapUR loc val).
Definition to_tpool : list expr → tpoolUR.
Admitted.
Definition to_heap {L V} `{Countable L} : gmap L V → heapUR L V.
exact (fmap (λ v, (1%Qp, to_agree (v : leibnizO V)))).
Defined.

Class cfgSG Σ := CFGSG { cfg_inG :> inG Σ (authR cfgUR); cfg_name : gname }.

Section definitionsS.
  Context `{cfgSG Σ, invGS Σ}.
Definition heapS_mapsto (l : loc) (q : Qp) (v: val) : iProp Σ.
Admitted.
Definition tpool_mapsto (j : nat) (e: expr) : iProp Σ.
Admitted.
Definition spec_inv (ρ : cfg F_mu_ref_conc_lang) : iProp Σ.
exact ((∃ tp σ, own cfg_name (● (to_tpool tp, to_heap σ))
                 ∗ ⌜rtc erased_step ρ (tp,σ)⌝)%I).
Defined.
Definition spec_ctx : iProp Σ.
exact ((∃ ρ, inv specN (spec_inv ρ))%I).
Defined.
End definitionsS.
Notation "l ↦ₛ v" := (heapS_mapsto l 1 v) (at level 20) : bi_scope.
Notation "j ⤇ e" := (tpool_mapsto j e) (at level 20) : bi_scope.

Section conversions.

  Lemma to_tpool_valid es : ✓ to_tpool es.
Admitted.

End conversions.

End rules.
Include iris_examples_DOT_logrel_DOT_F_mu_ref_conc_DOT_binary_DOT_rules_WRAPPED.rules.

Inductive type :=
  | TUnit : type
  | TNat : type
  | TBool : type
  | TProd : type → type → type
  | TSum : type → type → type
  | TArrow : type → type → type
  | TRec (τ : {bind 1 of type})
  | TVar (x : var)
  | TForall (τ : {bind 1 of type})
  | TExist (τ : {bind 1 of type})
  | Tref (τ : type).
Fixpoint env_subst (vs : list val) : var → expr.
exact (match vs with
  | [] => ids
  | v :: vs' => (of_val v) .: env_subst vs'
  end).
Defined.

Section persistent_pred.
  Context (A : Type) (PROP : bi).

  Record persistent_pred := PersPred {
    pers_pred_car :> A → PROP;
    pers_pred_persistent x : Persistent (pers_pred_car x)
  }.
Local Instance persistent_pred_equiv : Equiv persistent_pred.
Admitted.
Local Instance persistent_pred_dist : Dist persistent_pred.
exact (λ n Φ Φ', ∀ x, Φ x ≡{n}≡ Φ' x).
Defined.
  Definition persistent_pred_ofe_mixin : OfeMixin persistent_pred.
Admitted.
  Canonical Structure persistent_predO :=
    Ofe persistent_pred persistent_pred_ofe_mixin.

  Global Instance persistent_pred_car_ne n :
    Proper (dist n ==> (=) ==> dist n)
      pers_pred_car.
Admitted.

End persistent_pred.

Global Arguments PersPred {_ _} _%I {_}.
Import iris.proofmode.proofmode.
Definition logN : namespace.
Admitted.

Section logrel.
  Context `{heapIG Σ, cfgSG Σ}.
  Notation D := (persistent_predO (val * val) (iPropI Σ)).
Definition interp_expr (τi : listO D -n> D) (Δ : listO D)
      (ee : expr * expr) : iProp Σ.
exact ((∀ j K,
    j ⤇ fill K (ee.2) -∗
    WP ee.1 {{ v, ∃ v', j ⤇ fill K (of_val v') ∗ τi Δ (v, v') }})%I).
Defined.

  Program Definition interp_ref_inv (ll : loc * loc) : D -n> iPropO Σ := λne τi,
    (∃ vv, ll.1 ↦ᵢ vv.1 ∗ ll.2 ↦ₛ vv.2 ∗ τi vv)%I.
  Solve Obligations with solve_proper.

  Program Definition interp_ref
      (interp : listO D -n> D) : listO D -n> D :=
    λne Δ,
    PersPred (λ ww,
            ∃ ll, ⌜ww = (LocV (ll.1), LocV (ll.2))⌝ ∧
                  inv (logN .@ ll) (interp_ref_inv ll (interp Δ)))%I.
  Solve Obligations with solve_proper.
Fixpoint interp (τ : type) : listO D -n> D.
Admitted.
  Notation "⟦ τ ⟧" := (interp τ).
Definition interp_env (Γ : list type)
      (Δ : listO D) (vvs : list (val * val)) : iProp Σ.
exact ((⌜length Γ = length vvs⌝ ∗ [∗] zip_with (λ τ, ⟦ τ ⟧ Δ) Γ vvs)%I).
Defined.

End logrel.
Notation "⟦ τ ⟧ₑ" := (interp_expr (interp τ)).
Notation "⟦ Γ ⟧*" := (interp_env Γ).

Section bin_log_def.
  Context `{heapIG Σ, cfgSG Σ}.
Definition bin_log_related (Γ : list type) (e e' : expr) (τ : type) : iProp Σ.
exact (tc_opaque (□ ∀ Δ vvs,
      spec_ctx ∧ ⟦ Γ ⟧* Δ vvs -∗
      ⟦ τ ⟧ₑ Δ (e.[env_subst (vvs.*1)], e'.[env_subst (vvs.*2)]))%I).
Defined.

End bin_log_def.

Notation "Γ ⊨ e '≤log≤' e' : τ" :=
  (bin_log_related Γ e e' τ) (at level 74, e, e', τ at next level).

Module Export iris_examples_DOT_logrel_DOT_F_mu_ref_conc_DOT_unary_DOT_logrel_WRAPPED.

Section logrel.
  Context `{heapIG Σ}.
  Notation D := (persistent_predO val (iPropI Σ)).

  Program Definition interp_ref_inv (l : loc) : D -n> iPropO Σ := λne τi,
    (∃ v, l ↦ᵢ v ∗ τi v)%I.
  Solve Obligations with solve_proper.

  Program Definition interp_ref (interp : listO D -n> D) : listO D -n> D :=
    λne Δ,
    PersPred (λ w, ∃ l, ⌜w = LocV l⌝ ∧
                      inv (logN .@ l) (interp_ref_inv l (interp Δ)))%I.
  Solve Obligations with solve_proper.
Fixpoint interp (τ : type) : listO D -n> D.
Admitted.
  Notation "⟦ τ ⟧" := (interp τ).
Definition interp_env (Γ : list type)
      (Δ : listO D) (vs : list val) : iProp Σ.
exact ((⌜length Γ = length vs⌝ ∗ [∗] zip_with (λ τ, ⟦ τ ⟧ Δ) Γ vs)%I).
Defined.
  Notation "⟦ Γ ⟧*" := (interp_env Γ).

  Lemma interp_env_nil Δ : ⊢ ⟦ [] ⟧* Δ [].
Admitted.
End logrel.

Lemma basic_soundness Σ `{heapPreIG Σ, inG Σ (authR cfgUR)}
    e e' τ v thp hp :
  (∀ `{heapIG Σ, cfgSG Σ}, ⊢ [] ⊨ e ≤log≤ e' : τ) →
  rtc erased_step ([e], ∅) (of_val v :: thp, hp) →
  (∃ thp' hp' v', rtc erased_step ([e'], ∅) (of_val v' :: thp', hp')).
Proof.
  intros Hlog Hsteps.
  cut (adequate NotStuck e ∅ (λ _ _, ∃ thp' h v, rtc erased_step ([e'], ∅) (of_val v :: thp', h))).
  {
 destruct 1; naive_solver.
}
  eapply (wp_adequacy Σ _); iIntros (Hinv ?).
  iMod (gen_heap_init (∅: state)) as (Hheap) "[Hh _]".
  iMod (own_alloc (● (to_tpool [e'], ∅)
    ⋅ ◯ ((to_tpool [e'] : tpoolUR, ∅) : cfgUR))) as (γc) "[Hcfg1 Hcfg2]".
  {
 apply auth_both_valid_discrete.
split=>//.
split=>//.
apply to_tpool_valid.
}
  set (Hcfg := CFGSG _ _ γc).
  iMod (inv_alloc specN _ (spec_inv ([e'], ∅)) with "[Hcfg1]") as "#Hcfg".
  {
 iNext.
iExists [e'], ∅.
rewrite /to_heap fmap_empty.
auto.
}
  set (HeapΣ := (HeapIG Σ Hinv Hheap)).
  iExists (λ σ _, gen_heap_interp σ), (λ _, True%I); iFrame.
  iApply wp_fupd.
iApply wp_wand_r.
  iSplitL.
  -
 iPoseProof ((Hlog _ _)) as "Hrel".
    iSpecialize ("Hrel" $! [] [] with "[]").
    {
 iSplit.
      -
 by iExists ([e'], ∅).
      -
 by iApply (@interp_env_nil Σ HeapΣ []).
}
    simpl.
    replace e with e.[env_subst[]] at 2 by by asimpl.
    iApply ("Hrel" $! 0 []).
    {
 rewrite /tpool_mapsto.
asimpl.
