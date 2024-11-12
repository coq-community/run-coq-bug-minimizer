
(* -*- mode: coq; coq-prog-args: ("-emacs" "-w" "-ssr-search-moved" "-w" "+deprecated-instance-without-locality" "-w" "+ambiguous-paths" "-w" "+deprecated-hint-rewrite-without-locality" "-w" "-deprecated-field-instance-without-locality" "-w" "+deprecated-tactic-notation" "-w" "-deprecated-since-8.19" "-w" "-deprecated-since-8.20" "-w" "-deprecated-from-Coq" "-w" "-deprecated-dirpath-Coq" "-w" "-notation-incompatible-prefix" "-w" "-deprecated-typeclasses-transparency-without-locality" "-w" "-notation-overridden,-redundant-canonical-projection,-unknown-warning,-argument-scope-delimiter" "-w" "-deprecated-native-compiler-option,-native-compiler-disabled" "-native-compiler" "ondemand" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/src" "Perennial" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/stdpp/stdpp" "stdpp" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/stdpp/stdpp_unstable" "stdpp.unstable" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/stdpp/stdpp_bitvector" "stdpp.bitvector" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/iris/iris" "iris" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/iris/iris_deprecated" "iris.deprecated" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/iris/iris_unstable" "iris.unstable" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/iris/iris_heap_lang" "iris.heap_lang" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/coqutil/src/coqutil" "coqutil" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/Goose" "Goose" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/record-update/src" "RecordUpdate" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/coq-tactical/src" "Tactical" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/external/iris-named-props/src" "iris_named_props" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/new_trusted_code" "New.code" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/new_code_axioms" "New.code" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/new_partial_axioms" "New.code_axioms" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/perennial/new" "New" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-top" "Top.bug_01") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 1066 lines to 167 lines, then from 180 lines to 368 lines, then from 373 lines to 168 lines, then from 181 lines to 855 lines, then from 857 lines to 177 lines, then from 190 lines to 549 lines, then from 554 lines to 194 lines, then from 207 lines to 743 lines, then from 748 lines to 248 lines, then from 261 lines to 446 lines, then from 451 lines to 249 lines, then from 262 lines to 842 lines, then from 847 lines to 260 lines, then from 273 lines to 624 lines, then from 624 lines to 278 lines, then from 291 lines to 478 lines, then from 483 lines to 279 lines, then from 292 lines to 558 lines, then from 563 lines to 279 lines, then from 292 lines to 689 lines, then from 694 lines to 309 lines, then from 322 lines to 1312 lines, then from 1316 lines to 426 lines, then from 439 lines to 919 lines, then from 924 lines to 474 lines, then from 487 lines to 1254 lines, then from 1259 lines to 659 lines, then from 660 lines to 533 lines, then from 546 lines to 841 lines, then from 846 lines to 542 lines, then from 555 lines to 674 lines, then from 679 lines to 553 lines, then from 566 lines to 969 lines, then from 974 lines to 588 lines, then from 601 lines to 766 lines, then from 771 lines to 587 lines, then from 600 lines to 772 lines, then from 777 lines to 589 lines, then from 602 lines to 962 lines, then from 967 lines to 603 lines, then from 616 lines to 1930 lines, then from 1935 lines to 642 lines, then from 655 lines to 2993 lines, then from 2998 lines to 1687 lines, then from 1700 lines to 3137 lines, then from 3142 lines to 2116 lines *)
(* coqc version 9.0+alpha compiled with OCaml 4.14.1
   coqtop version runner-t7b1znuaq-project-4504-concurrent-0:/builds/coq/coq/_build/default,(HEAD detached at c04db99c8cfbe3) (c04db99c8cfbe3fa002bf604971eb5b0e09656d4)
   Expected coqc runtime on this file: 1.718 sec *)
Require iris.algebra.coPset.
Require iris.proofmode.class_instances_make.
Require iris.proofmode.class_instances_frame.
Require stdpp.hlist.
Require iris.proofmode.string_ident.
Require iris.proofmode.spec_patterns.
Require iris.proofmode.intro_patterns.
Require iris.proofmode.reduction.
Export iris.bi.telescopes.
Export iris.proofmode.base.
Export iris.proofmode.environments.
Export iris.proofmode.classes.
Import env_notations.

Local Open Scope lazy_bool_scope.


Section tactics.
Context {PROP : bi}.
Implicit Types P Q : PROP.


Lemma tac_start P : envs_entails (Envs Enil Enil 1) P → ⊢ P.
Admitted.

Class AffineEnv (Γ : env PROP) := affine_env : Forall Affine Γ.

Lemma tac_emp_intro Δ : AffineEnv (env_spatial Δ) → envs_entails Δ emp.
Admitted.

Lemma tac_assumption Δ i p P Q :
  envs_lookup i Δ = Some (p,P) →
  FromAssumption p P Q →
  (let Δ' := envs_delete true i p Δ in
   if env_spatial_is_nil Δ' then TCTrue
   else TCOr (Absorbing Q) (AffineEnv (env_spatial Δ'))) →
  envs_entails Δ Q.
Admitted.

Lemma tac_rename Δ i j p P Q :
  envs_lookup i Δ = Some (p,P) →
  match envs_simple_replace i p (Esnoc Enil j P) Δ with
  | None => False
  | Some Δ' => envs_entails Δ' Q
  end →
  envs_entails Δ Q.
Admitted.

Lemma tac_clear Δ i p P Q :
  envs_lookup i Δ = Some (p,P) →
  (if p then TCTrue else TCOr (Affine P) (Absorbing Q)) →
  envs_entails (envs_delete true i p Δ) Q →
  envs_entails Δ Q.
Admitted.


Lemma tac_ex_falso Δ Q : envs_entails Δ False → envs_entails Δ Q.
Admitted.


Lemma tac_pure_intro Δ Q φ a :
  FromPure a Q φ →
  (if a then AffineEnv (env_spatial Δ) else TCTrue) →
  φ →
  envs_entails Δ Q.
Admitted.

Lemma tac_pure Δ i p P φ Q :
  envs_lookup i Δ = Some (p, P) →
  IntoPure P φ →
  (if p then TCTrue else TCOr (Affine P) (Absorbing Q)) →
  (φ → envs_entails (envs_delete true i p Δ) Q) → envs_entails Δ Q.
Admitted.


Lemma tac_intuitionistic Δ i j p P P' Q :
  envs_lookup i Δ = Some (p, P) →
  IntoPersistent p P P' →
  (if p then TCTrue else TCOr (Affine P) (Absorbing Q)) →
  match envs_replace i p true (Esnoc Enil j P') Δ with
  | None => False
  | Some Δ' => envs_entails Δ' Q
  end →
  envs_entails Δ Q.
Admitted.

Lemma tac_spatial Δ i j p P P' Q :
  envs_lookup i Δ = Some (p, P) →
  (if p then FromAffinely P' P else TCEq P' P) →
  match envs_replace i p false (Esnoc Enil j P') Δ with
  | None => False
  | Some Δ' => envs_entails Δ' Q
  end →
  envs_entails Δ Q.
Admitted.


Lemma tac_impl_intro Δ i P P' Q R :
  FromImpl R P Q →
  (if env_spatial_is_nil Δ then TCTrue else Persistent P) →
  FromAffinely P' P →
  match envs_app false (Esnoc Enil i P') Δ with
  | None => False
  | Some Δ' => envs_entails Δ' Q
  end →
  envs_entails Δ R.
Admitted.
Lemma tac_impl_intro_intuitionistic Δ i P P' Q R :
  FromImpl R P Q →
  IntoPersistent false P P' →
  match envs_app true (Esnoc Enil i P') Δ with
  | None => False
  | Some Δ' => envs_entails Δ' Q
  end →
  envs_entails Δ R.
Admitted.

Lemma tac_wand_intro Δ i P Q R :
  FromWand R P Q →
  match envs_app false (Esnoc Enil i P) Δ with
  | None => False
  | Some Δ' => envs_entails Δ' Q
  end →
  envs_entails Δ R.
Admitted.

Lemma tac_wand_intro_intuitionistic Δ i P P' Q R :
  FromWand R P Q →
  IntoPersistent false P P' →
  TCOr (Affine P) (Absorbing Q) →
  match envs_app true (Esnoc Enil i P') Δ with
  | None => False
  | Some Δ' => envs_entails Δ' Q
  end →
  envs_entails Δ R.
Admitted.


Lemma tac_specialize remove_intuitionistic Δ i p j q P1 P2 R Q :
  envs_lookup i Δ = Some (p, P1) →
  let Δ' := envs_delete remove_intuitionistic i p Δ in
  envs_lookup j Δ' = Some (q, R) →
  IntoWand q p R P1 P2 →
  match envs_replace j q (p &&& q) (Esnoc Enil j P2) Δ' with
  | Some Δ'' => envs_entails Δ'' Q
  | None => False
  end → envs_entails Δ Q.
Admitted.

Lemma tac_specialize_assert Δ j (q am neg : bool) js R P1 P2 P1' Q :
  envs_lookup j Δ = Some (q, R) →
  IntoWand q false R P1 P2 →
  (if am then AddModal P1' P1 Q else TCEq P1' P1) →
  match
    '(Δ1,Δ2) ← envs_split (if neg is true then Right else Left)
                          js (envs_delete true j q Δ);
    Δ2' ← envs_app (negb am &&& q &&& env_spatial_is_nil Δ1) (Esnoc Enil j P2) Δ2;
    Some (Δ1,Δ2') 
  with
  | Some (Δ1,Δ2') =>
     
     envs_entails Δ1 P1' ∧ envs_entails Δ2' Q
  | None => False
  end → envs_entails Δ Q.
Admitted.

Lemma tac_unlock_emp Δ Q : envs_entails Δ Q → envs_entails Δ (emp ∗ locked Q).
Admitted.
Lemma tac_unlock_True Δ Q : envs_entails Δ Q → envs_entails Δ (True ∗ locked Q).
Admitted.
Lemma tac_unlock Δ Q : envs_entails Δ Q → envs_entails Δ (locked Q).
Admitted.

Lemma tac_specialize_frame Δ j (q am : bool) R P1 P2 P1' Q Q' :
  envs_lookup j Δ = Some (q, R) →
  IntoWand q false R P1 P2 →
  (if am then AddModal P1' P1 Q else TCEq P1' P1) →
  envs_entails (envs_delete true j q Δ) (P1' ∗ locked Q') →
  Q' = (P2 -∗ Q)%I →
  envs_entails Δ Q.
Admitted.

Lemma tac_specialize_assert_pure Δ j q a R P1 P2 φ Q :
  envs_lookup j Δ = Some (q, R) →
  IntoWand q false R P1 P2 →
  FromPure a P1 φ →
  φ →
  match envs_simple_replace j q (Esnoc Enil j P2) Δ with
  | None => False
  | Some Δ' => envs_entails Δ' Q
  end →
  envs_entails Δ Q.
Admitted.

Lemma tac_specialize_assert_intuitionistic Δ j q P1 P1' P2 R Q :
  envs_lookup j Δ = Some (q, R) →
  IntoWand q true R P1 P2 →
  Persistent P1 →
  IntoAbsorbingly P1' P1 →
  envs_entails (envs_delete true j q Δ) P1' →
  match envs_simple_replace j q (Esnoc Enil j P2) Δ with
  | Some Δ'' => envs_entails Δ'' Q
  | None => False
  end → envs_entails Δ Q.
Admitted.

Lemma tac_specialize_intuitionistic_helper Δ j q P R R' Q :
  envs_lookup j Δ = Some (q,P) →
  (if q then TCTrue else BiAffine PROP) →
  envs_entails Δ (<absorb> R) →
  IntoPersistent false R R' →
  match envs_replace j q true (Esnoc Enil j R') Δ with
  | Some Δ'' => envs_entails Δ'' Q
  | None => False
  end → envs_entails Δ Q.
Admitted.


Lemma tac_specialize_intuitionistic_helper_done Δ i q P :
  envs_lookup i Δ = Some (q,P) →
  envs_entails Δ (<absorb> P).
Admitted.

Lemma tac_revert Δ i Q :
  match envs_lookup_delete true i Δ with
  | Some (p,P,Δ') => envs_entails Δ' ((if p then □ P else P)%I -∗ Q)
  | None => False
  end →
  envs_entails Δ Q.
Admitted.

Definition IntoEmpValid (φ : Type) (P : PROP) := φ → ⊢ P.

Lemma into_emp_valid_here φ P : AsEmpValid φ P → IntoEmpValid φ P.
Admitted.
Lemma into_emp_valid_impl (φ ψ : Type) P :
  φ → IntoEmpValid ψ P → IntoEmpValid (φ → ψ) P.
Admitted.
Lemma into_emp_valid_forall {A} (φ : A → Type) P x :
  IntoEmpValid (φ x) P → IntoEmpValid (∀ x : A, φ x) P.
Admitted.
Lemma into_emp_valid_tforall {TT : tele} (φ : TT → Prop) P x :
  IntoEmpValid (φ x) P → IntoEmpValid (∀.. x : TT, φ x) P.
Admitted.
Lemma into_emp_valid_proj φ P : IntoEmpValid φ P → φ → ⊢ P.
Admitted.


Lemma tac_pose_proof Δ j P Q :
  (⊢ P) →
  match envs_app true (Esnoc Enil j P) Δ with
  | None => False
  | Some Δ' => envs_entails Δ' Q
  end →
  envs_entails Δ Q.
Admitted.

Lemma tac_pose_proof_hyp Δ i j Q :
  match envs_lookup_delete false i Δ with
  | None => False
  | Some (p, P, Δ') =>
    match envs_app p (Esnoc Enil j P) Δ' with
    | None => False
    | Some Δ'' => envs_entails Δ'' Q
    end
  end →
  envs_entails Δ Q.
Admitted.


Lemma tac_and_destruct Δ i p j1 j2 P P1 P2 Q :
  envs_lookup i Δ = Some (p, P) →
  (if p then IntoAnd true P P1 P2 else IntoSep P P1 P2) →
  match envs_simple_replace i p (Esnoc (Esnoc Enil j1 P1) j2 P2) Δ with
  | None => False
  | Some Δ' => envs_entails Δ' Q
  end →
  envs_entails Δ Q.
Admitted.


Lemma tac_and_destruct_choice Δ i p d j P P1 P2 Q :
  envs_lookup i Δ = Some (p, P) →
  (if p then IntoAnd p P P1 P2 : Type else
    TCOr (IntoAnd p P P1 P2) (TCAnd (IntoSep P P1 P2)
      (if d is Left then TCOr (Affine P2) (Absorbing Q)
       else TCOr (Affine P1) (Absorbing Q)))) →
  match envs_simple_replace i p (Esnoc Enil j (if d is Left then P1 else P2)) Δ with
  | None => False
  | Some Δ' => envs_entails Δ' Q
  end → envs_entails Δ Q.
Admitted.


Lemma tac_frame_pure Δ (φ : Prop) P Q :
  φ → Frame true ⌜φ⌝ P Q → envs_entails Δ Q → envs_entails Δ P.
Admitted.

Lemma tac_frame Δ i p R P Q :
  envs_lookup i Δ = Some (p, R) →
  Frame p R P Q →
  envs_entails (envs_delete false i p Δ) Q → envs_entails Δ P.
Admitted.

Lemma tac_or_destruct Δ i p j1 j2 P P1 P2 Q :
  envs_lookup i Δ = Some (p, P) → IntoOr P P1 P2 →
  match envs_simple_replace i p (Esnoc Enil j1 P1) Δ,
        envs_simple_replace i p (Esnoc Enil j2 P2) Δ with
  | Some Δ1, Some Δ2 => envs_entails Δ1 Q ∧ envs_entails Δ2 Q
  | _, _ => False
  end →
  envs_entails Δ Q.
Admitted.


Lemma tac_forall_intro {A} Δ (Φ : A → PROP) Q name :
  FromForall Q Φ name →
  ( 
   let _ := name in
   ∀ a, envs_entails Δ (Φ a)) →
  envs_entails Δ Q.
Admitted.

Lemma tac_forall_specialize {A} Δ i p P (Φ : A → PROP) Q :
  envs_lookup i Δ = Some (p, P) → IntoForall P Φ →
  (∃ x : A,
      match envs_simple_replace i p (Esnoc Enil i (Φ x)) Δ with
      | None => False
      | Some Δ' => envs_entails Δ' Q
      end) →
  envs_entails Δ Q.
Admitted.


Lemma tac_exist {A} Δ P (Φ : A → PROP) :
  FromExist P Φ → (∃ a, envs_entails Δ (Φ a)) → envs_entails Δ P.
Admitted.

Lemma tac_exist_destruct {A} Δ i p j P (Φ : A → PROP) (name: ident_name) Q :
  envs_lookup i Δ = Some (p, P) → IntoExist P Φ name →
  ( 
    let _ := name in
    ∀ a,
     match envs_simple_replace i p (Esnoc Enil j (Φ a)) Δ with
     | Some Δ' => envs_entails Δ' Q
     | None => False
     end) →
  envs_entails Δ Q.
Admitted.


Lemma tac_modal_elim Δ i j p p' φ P' P Q Q' :
  envs_lookup i Δ = Some (p, P) →
  ElimModal φ p p' P P' Q Q' →
  φ →
  match envs_replace i p p' (Esnoc Enil j P') Δ with
  | None => False
  | Some Δ' => envs_entails Δ' Q'
  end →
  envs_entails Δ Q.
Admitted.
End tactics.



Class TransformIntuitionisticEnv {PROP1 PROP2} (M : modality PROP1 PROP2)
    (C : PROP2 → PROP1 → Prop) (Γin : env PROP2) (Γout : env PROP1) := {
  transform_intuitionistic_env :
    (∀ P Q, C P Q → □ P ⊢ M (□ Q)) →
    (∀ P Q, M P ∧ M Q ⊢ M (P ∧ Q)) →
    <affine> env_and_persistently Γin ⊢ M (<affine> env_and_persistently Γout);
  transform_intuitionistic_env_wf : env_wf Γin → env_wf Γout;
  transform_intuitionistic_env_dom i : Γin !! i = None → Γout !! i = None;
}.


Class TransformSpatialEnv {PROP1 PROP2} (M : modality PROP1 PROP2)
    (C : PROP2 → PROP1 → Prop) (Γin : env PROP2) (Γout : env PROP1)
    (filtered : bool) := {
  transform_spatial_env :
    (∀ P Q, C P Q → P ⊢ M Q) →
    ([∗] Γin) ⊢ M ([∗] Γout) ∗ if filtered then True else emp;
  transform_spatial_env_wf : env_wf Γin → env_wf Γout;
  transform_spatial_env_dom i : Γin !! i = None → Γout !! i = None;
}.


Inductive IntoModalIntuitionisticEnv {PROP2} : ∀ {PROP1} (M : modality PROP1 PROP2)
    (Γin : env PROP2) (Γout : env PROP1), modality_action PROP1 PROP2 → Prop :=
  | MIEnvIsEmpty_intuitionistic {PROP1} (M : modality PROP1 PROP2) :
     IntoModalIntuitionisticEnv M Enil Enil MIEnvIsEmpty
  | MIEnvForall_intuitionistic (M : modality PROP2 PROP2) (C : PROP2 → Prop) Γ :
     TCForall C (env_to_list Γ) →
     IntoModalIntuitionisticEnv M Γ Γ (MIEnvForall C)
  | MIEnvTransform_intuitionistic {PROP1}
       (M : modality PROP1 PROP2) (C : PROP2 → PROP1 → Prop) Γin Γout :
     TransformIntuitionisticEnv M C Γin Γout →
     IntoModalIntuitionisticEnv M Γin Γout (MIEnvTransform C)
  | MIEnvClear_intuitionistic {PROP1 : bi} (M : modality PROP1 PROP2) Γ :
     IntoModalIntuitionisticEnv M Γ Enil MIEnvClear
  | MIEnvId_intuitionistic (M : modality PROP2 PROP2) Γ :
     IntoModalIntuitionisticEnv M Γ Γ MIEnvId.
Existing Class IntoModalIntuitionisticEnv.
Global Existing Instances MIEnvIsEmpty_intuitionistic MIEnvForall_intuitionistic
  MIEnvTransform_intuitionistic MIEnvClear_intuitionistic MIEnvId_intuitionistic.


Inductive IntoModalSpatialEnv {PROP2} : ∀ {PROP1} (M : modality PROP1 PROP2)
    (Γin : env PROP2) (Γout : env PROP1), modality_action PROP1 PROP2 → bool → Prop :=
  | MIEnvIsEmpty_spatial {PROP1} (M : modality PROP1 PROP2) :
     IntoModalSpatialEnv M Enil Enil MIEnvIsEmpty false
  | MIEnvForall_spatial (M : modality PROP2 PROP2) (C : PROP2 → Prop) Γ :
     TCForall C (env_to_list Γ) →
     IntoModalSpatialEnv M Γ Γ (MIEnvForall C) false
  | MIEnvTransform_spatial {PROP1}
       (M : modality PROP1 PROP2) (C : PROP2 → PROP1 → Prop) Γin Γout fi :
     TransformSpatialEnv M C Γin Γout fi →
     IntoModalSpatialEnv M Γin Γout (MIEnvTransform C) fi
  | MIEnvClear_spatial {PROP1 : bi} (M : modality PROP1 PROP2) Γ :
     IntoModalSpatialEnv M Γ Enil MIEnvClear false
  | MIEnvId_spatial (M : modality PROP2 PROP2) Γ :
     IntoModalSpatialEnv M Γ Γ MIEnvId false.
Existing Class IntoModalSpatialEnv.
Global Existing Instances MIEnvIsEmpty_spatial MIEnvForall_spatial
  MIEnvTransform_spatial MIEnvClear_spatial MIEnvId_spatial.

Section tac_modal_intro.
  Context {PROP1 PROP2 : bi} (M : modality PROP1 PROP2).

  
  Lemma tac_modal_intro {A} φ (sel : A) Γp Γs n Γp' Γs' Q Q' fi :
    FromModal φ M sel Q' Q →
    IntoModalIntuitionisticEnv M Γp Γp' (modality_intuitionistic_action M) →
    IntoModalSpatialEnv M Γs Γs' (modality_spatial_action M) fi →
    (if fi then Absorbing Q' else TCTrue) →
    φ →
    envs_entails (Envs Γp' Γs' n) Q → envs_entails (Envs Γp Γs n) Q'.
Admitted.
End tac_modal_intro.
Import stdpp.namespaces.
Import stdpp.hlist.
Import iris.proofmode.intro_patterns.
Import iris.proofmode.spec_patterns.
Import iris.proofmode.sel_patterns.
Import iris.proofmode.reduction.
Import iris.proofmode.string_ident.

Ltac iSolveSideCondition :=
  lazymatch goal with
  | |- pm_error ?err => fail "" err
  | _ => split_and?; try solve [ fast_done | solve_ndisj | tc_solve ]
  end.

Ltac pretty_ident H :=
  lazymatch H with
  | INamed ?H => H
  | ?H => H
  end.

Ltac iGetCtx :=
  lazymatch goal with
  | |- envs_entails ?Δ _ => Δ
  | |- context[ envs_split _ _ ?Δ ] => Δ
  end.

Ltac iMissingHypsCore Δ Hs :=
  let Hhyps := pm_eval (envs_dom Δ) in
  eval vm_compute in (list_difference Hs Hhyps).

Ltac iTypeOf H :=
  let Δ := match goal with |- envs_entails ?Δ _ => Δ end in
  pm_eval (envs_lookup H Δ).

Ltac iBiOfGoal :=
  match goal with |- @envs_entails ?PROP _ _ => PROP end.

Tactic Notation "iStartProof" :=
  lazymatch goal with
  | |- (let _ := _ in _) => fail "iStartProof: goal is a `let`, use `simpl`,"
                                 "`intros x`, `iIntros (x)`, or `iIntros ""%x"""
  | |- envs_entails _ _ => idtac
  | |- ?φ => notypeclasses refine (as_emp_valid_2 φ _ _);
               [tc_solve || fail "iStartProof: not a BI assertion:" φ
               |notypeclasses refine (tac_start _ _)]
  end.

Ltac iFresh :=

  let start :=
    lazymatch goal with
    | _ => iStartProof
    end in
  let c :=
    lazymatch goal with
    | |- envs_entails (Envs _ _ ?c) _ => c
    end in
  let inc :=
    lazymatch goal with
    | |- envs_entails (Envs ?Δp ?Δs _) ?Q =>
      let c' := eval vm_compute in (Pos.succ c) in
      change_no_check (envs_entails (Envs Δp Δs c') Q)
    end in
  constr:(IAnon c).

Tactic Notation "iRename" constr(H1) "into" constr(H2) :=
  eapply tac_rename with H1 H2 _ _;
    [pm_reflexivity ||
     let H1 := pretty_ident H1 in
     fail "iRename:" H1 "not found"
    |pm_reduce;
     lazymatch goal with
       | |- False =>
         let H2 := pretty_ident H2 in
         fail "iRename:" H2 "not fresh"
       | _ => idtac
     end].

Inductive esel_pat :=
  | ESelPure
  | ESelIdent :  bool → ident → esel_pat.

Local Ltac iElaborateSelPat_go pat Δ Hs :=
  lazymatch pat with
  | [] => eval cbv in Hs
  | SelPure :: ?pat =>  iElaborateSelPat_go pat Δ (ESelPure :: Hs)
  | SelIntuitionistic :: ?pat =>
    let Hs' := pm_eval (env_dom (env_intuitionistic Δ)) in
    let Δ' := pm_eval (envs_clear_intuitionistic Δ) in
    iElaborateSelPat_go pat Δ' ((ESelIdent true <$> Hs') ++ Hs)
  | SelSpatial :: ?pat =>
    let Hs' := pm_eval (env_dom (env_spatial Δ)) in
    let Δ' := pm_eval (envs_clear_spatial Δ) in
    iElaborateSelPat_go pat Δ' ((ESelIdent false <$> Hs') ++ Hs)
  | SelIdent ?H :: ?pat =>
    lazymatch pm_eval (envs_lookup_delete false H Δ) with
    | Some (?p,_,?Δ') =>  iElaborateSelPat_go pat Δ' (ESelIdent p H :: Hs)
    | None =>
      let H := pretty_ident H in
      fail "iElaborateSelPat:" H "not found"
    end
  end.

Ltac iElaborateSelPat pat :=
  lazymatch goal with
  | |- envs_entails ?Δ _ =>
    let pat := sel_pat.parse pat in iElaborateSelPat_go pat Δ (@nil esel_pat)
  end.

Local Ltac iClearHyp H :=
  eapply tac_clear with H _ _;
    [pm_reflexivity ||
     let H := pretty_ident H in
     fail "iClear:" H "not found"
    |pm_reduce; tc_solve ||
     let H := pretty_ident H in
     let P := match goal with |- TCOr (Affine ?P) _ => P end in
     fail "iClear:" H ":" P "not affine and the goal not absorbing"
    |pm_reduce].

Local Ltac iClear_go Hs :=
  lazymatch Hs with
  | [] => idtac
  | ESelPure :: ?Hs => clear; iClear_go Hs
  | ESelIdent _ ?H :: ?Hs => iClearHyp H; iClear_go Hs
  end.
Tactic Notation "iClear" constr(Hs) :=
  iStartProof; let Hs := iElaborateSelPat Hs in iClear_go Hs.

Tactic Notation "iExact" constr(H) :=
  eapply tac_assumption with H _ _;
    [pm_reflexivity ||
     let H := pretty_ident H in
     fail "iExact:" H "not found"
    |tc_solve ||
     let H := pretty_ident H in
     let P := match goal with |- FromAssumption _ ?P _ => P end in
     fail "iExact:" H ":" P "does not match goal"
    |pm_reduce; tc_solve ||
     let H := pretty_ident H in
     fail "iExact: remaining hypotheses not affine and the goal not absorbing"].

Tactic Notation "iExFalso" :=
  iStartProof;
  apply tac_ex_falso.

Local Tactic Notation "iIntuitionistic" constr(H) "as" constr(H') :=
  eapply tac_intuitionistic with H H' _ _ _;
    [pm_reflexivity ||
     let H := pretty_ident H in
     fail "iIntuitionistic:" H "not found"
    |tc_solve ||
     let P := match goal with |- IntoPersistent _ ?P _ => P end in
     fail "iIntuitionistic:" P "not persistent"
    |pm_reduce; tc_solve ||
     let P := match goal with |- TCOr (Affine ?P) _ => P end in
     fail "iIntuitionistic:" P "not affine and the goal not absorbing"
    |pm_reduce;
     lazymatch goal with
     | |- False =>
       let H' := pretty_ident H' in
       fail "iIntuitionistic:" H' "not fresh"
     | _ => idtac
     end].

Local Tactic Notation "iSpatial" constr(H) "as" constr(H') :=
  eapply tac_spatial with H H' _ _ _;
    [pm_reflexivity ||
     let H := pretty_ident H in
     fail "iSpatial:" H "not found"
    |pm_reduce; tc_solve
    |pm_reduce;
     lazymatch goal with
     | |- False =>
       let H' := pretty_ident H' in
       fail "iSpatial:" H' "not fresh"
     | _ => idtac
     end].

Tactic Notation "iPure" constr(H) "as" simple_intropattern(pat) :=
  eapply tac_pure with H _ _ _;
    [pm_reflexivity ||
     let H := pretty_ident H in
     fail "iPure:" H "not found"
    |tc_solve ||
     let P := match goal with |- IntoPure ?P _ => P end in
     fail "iPure:" P "not pure"
    |pm_reduce; tc_solve ||
     let P := match goal with |- TCOr (Affine ?P) _ => P end in
     fail "iPure:" P "not affine and the goal not absorbing"
    |pm_reduce; intros pat].

Tactic Notation "iEmpIntro" :=
  iStartProof;
  eapply tac_emp_intro;
    [pm_reduce; tc_solve ||
     fail "iEmpIntro: spatial context contains non-affine hypotheses"].

Tactic Notation "iPureIntro" :=
  iStartProof;
  eapply tac_pure_intro;
    [tc_solve ||
     let P := match goal with |- FromPure _ ?P _ => P end in
     fail "iPureIntro:" P "not pure"
    |pm_reduce; tc_solve ||
     fail "iPureIntro: spatial context contains non-affine hypotheses"
    |].

Ltac iFrameFinish :=
  pm_prettify;
  try match goal with
  | |- envs_entails _ True => by iPureIntro
  | |- envs_entails _ emp => iEmpIntro
  end.

Ltac iFramePure t :=
  iStartProof;
  let φ := type of t in
  eapply (tac_frame_pure _ _ _ _ t);
    [tc_solve || fail "iFrame: cannot frame" φ
    |iFrameFinish].

Ltac iFrameHyp H :=
  iStartProof;
  eapply tac_frame with H _ _ _;
    [pm_reflexivity ||
     let H := pretty_ident H in
     fail "iFrame:" H "not found"
    |tc_solve ||
     let R := match goal with |- Frame _ ?R _ _ => R end in
     fail "iFrame: cannot frame" R
    |pm_reduce; iFrameFinish].

Ltac iFrameAnyPure :=
  repeat match goal with H : _ |- _ => iFramePure H end.

Ltac iFrameAnyIntuitionistic :=
  iStartProof;
  let rec go Hs :=
    match Hs with [] => idtac | ?H :: ?Hs => repeat iFrameHyp H; go Hs end in
  match goal with
  | |- envs_entails ?Δ _ =>

     let Hs := eval lazy in (env_dom (env_intuitionistic Δ)) in go Hs
  end.

Ltac iFrameAnySpatial :=
  iStartProof;
  let rec go Hs :=
    match Hs with [] => idtac | ?H :: ?Hs => try iFrameHyp H; go Hs end in
  match goal with
  | |- envs_entails ?Δ _ =>

     let Hs := eval lazy in (env_dom (env_spatial Δ)) in go Hs
  end.

Local Ltac _iFrame_go Hs :=
  lazymatch Hs with
  | [] => idtac
  | SelPure :: ?Hs => iFrameAnyPure; _iFrame_go Hs
  | SelIntuitionistic :: ?Hs => iFrameAnyIntuitionistic; _iFrame_go Hs
  | SelSpatial :: ?Hs => iFrameAnySpatial; _iFrame_go Hs
  | SelIdent ?H :: ?Hs => iFrameHyp H; _iFrame_go Hs
  end.

Ltac _iFrame0 Hs :=
  let Hs := sel_pat.parse Hs in
  _iFrame_go Hs.

Tactic Notation "iFrame" := iFrameAnySpatial.
Tactic Notation "iFrame" constr(Hs) := _iFrame0 Hs.

Local Tactic Notation "iIntro" "(" simple_intropattern(x) ")" :=

  (

    intros x
  ) || (

    iStartProof;
    lazymatch goal with
    | |- envs_entails _ _ =>
      eapply tac_forall_intro;
        [tc_solve ||
         let P := match goal with |- FromForall ?P _ _ => P end in
         fail "iIntro: cannot turn" P "into a universal quantifier"
        |let name := lazymatch goal with
                     | |- let _ := (λ name, _) in _ => name
                     end in
         pm_prettify;
         let y := fresh name in
         intros y; revert y; intros x
         ]
    end).

Local Tactic Notation "iIntro" constr(H) :=
  iStartProof;
  first
  [
    eapply tac_impl_intro with H _ _ _;
      [tc_solve
      |pm_reduce; tc_solve ||
       let P := lazymatch goal with |- Persistent ?P => P end in
       let H := pretty_ident H in
       fail 1 "iIntro: introducing non-persistent" H ":" P
              "into non-empty spatial context"
      |tc_solve
      |pm_reduce;
       let H := pretty_ident H in
        lazymatch goal with
        | |- False =>
          let H := pretty_ident H in
          fail 1 "iIntro:" H "not fresh"
        | _ => idtac
        end]
  |
    eapply tac_wand_intro with H _ _;
      [tc_solve
      | pm_reduce;
        lazymatch goal with
        | |- False =>
          let H := pretty_ident H in
          fail 1 "iIntro:" H "not fresh"
        | _ => idtac
        end]
  | let H := pretty_ident H in
    fail 1 "iIntro: could not introduce" H ", goal is not a wand or implication" ].

Local Tactic Notation "iIntro" "#" constr(H) :=
  iStartProof;
  first
  [
   eapply tac_impl_intro_intuitionistic with H _ _ _;
     [tc_solve
     |tc_solve ||
      let P := match goal with |- IntoPersistent _ ?P _ => P end in
      fail 1 "iIntro:" P "not persistent"
     |pm_reduce;
      lazymatch goal with
      | |- False =>
        let H := pretty_ident H in
        fail 1 "iIntro:" H "not fresh"
      | _ => idtac
      end]
  |
   eapply tac_wand_intro_intuitionistic with H _ _ _;
     [tc_solve
     |tc_solve ||
      let P := match goal with |- IntoPersistent _ ?P _ => P end in
      fail 1 "iIntro:" P "not intuitionistic"
     |tc_solve ||
      let P := match goal with |- TCOr (Affine ?P) _ => P end in
      fail 1 "iIntro:" P "not affine and the goal not absorbing"
     |pm_reduce;
      lazymatch goal with
      | |- False =>
        let H := pretty_ident H in
        fail 1 "iIntro:" H "not fresh"
      | _ => idtac
      end]
  |fail 1 "iIntro: nothing to introduce"].

Local Tactic Notation "iIntro" constr(H) "as" constr(p) :=
  lazymatch p with
  | true => iIntro #H
  | _ =>  iIntro H
  end.

Local Tactic Notation "iIntroForall" :=
  lazymatch goal with
  | |- ∀ _, ?P => fail
  | |- ∀ _, _ => intro
  | |- let _ := _ in _ => intro
  | |- _ =>
    iStartProof;
    lazymatch goal with
    | |- envs_entails _ (∀ x : _, _) => let x' := fresh x in iIntro (x')
    end
  end.
Local Tactic Notation "iIntro" :=
  lazymatch goal with
  | |- _ → ?P => intro
  | |- _ =>
    iStartProof;
    lazymatch goal with
    | |- envs_entails _ (_ -∗ _) => iIntro (?) || let H := iFresh in iIntro #H || iIntro H
    | |- envs_entails _ (_ → _) => iIntro (?) || let H := iFresh in iIntro #H || iIntro H
    end
  end.

Tactic Notation "iRevertHyp" constr(H) "with" tactic1(tac) :=
  eapply tac_revert with H;
    [lazymatch goal with
     | |- match envs_lookup_delete true ?i ?Δ with _ => _ end =>
        lazymatch eval pm_eval in (envs_lookup_delete true i Δ) with
        | Some (?p,_,_) => pm_reduce; tac p
        | None =>
           let H := pretty_ident H in
           fail "iRevert:" H "not found"
        end
     end].

Record iTrm {X As S} :=
  ITrm { itrm : X ; itrm_vars : hlist As ; itrm_hyps : S }.
Global Arguments ITrm {_ _ _} _ _ _.
Notation "( H 'with' pat )" := (ITrm H hnil pat) (at level 0).

Tactic Notation "iPoseProofCoreHyp" constr(H) "as" constr(Hnew) :=
  let Δ := iGetCtx in
  notypeclasses refine (tac_pose_proof_hyp _ H Hnew _ _);
    pm_reduce;
    lazymatch goal with
    | |- False =>
      let lookup := pm_eval (envs_lookup_delete false H Δ) in
      lazymatch lookup with
      | None =>
        let H := pretty_ident H in
        fail "iPoseProof:" H "not found"
      | _ =>
        let Hnew := pretty_ident Hnew in
        fail "iPoseProof:" Hnew "not fresh"
      end
    | _ => idtac
    end.

Ltac iIntoEmpValid_go :=
  lazymatch goal with
  | |- IntoEmpValid (let _ := _ in _) _ =>

    lazy zeta; iIntoEmpValid_go
  | |- IntoEmpValid (?φ → ?ψ) _ =>

    notypeclasses refine (into_emp_valid_impl _ _ _ _ _);
      [|iIntoEmpValid_go]
  | |- IntoEmpValid (∀ _, _) _ =>

    notypeclasses refine (into_emp_valid_forall _ _ _ _); iIntoEmpValid_go
  | |- IntoEmpValid (∀.. _, _) _ =>

    notypeclasses refine (into_emp_valid_tforall _ _ _ _); iIntoEmpValid_go
  | |- _ =>
    first
      [
       notypeclasses refine (into_emp_valid_impl _ _ _ _ _);
         [|iIntoEmpValid_go]
      |
       notypeclasses refine (into_emp_valid_forall _ _ _ _); iIntoEmpValid_go
      |
       notypeclasses refine (into_emp_valid_tforall _ _ _ _); iIntoEmpValid_go
      |
       notypeclasses refine (into_emp_valid_here _ _ _) ]
  end.

Ltac iIntoEmpValid :=

  iIntoEmpValid_go;
    [..
    |tc_solve ||
     let φ := lazymatch goal with |- AsEmpValid ?φ _ => φ end in
     fail "iPoseProof:" φ "not a BI assertion"].

Tactic Notation "iPoseProofCoreLem" open_constr(lem) "as" tactic3(tac) :=
  let Hnew := iFresh in
  notypeclasses refine (tac_pose_proof _ Hnew _ _ (into_emp_valid_proj _ _ _ lem) _);
    [iIntoEmpValid
    |pm_reduce;
     lazymatch goal with
     | |- False =>
       let Hnew := pretty_ident Hnew in
       fail "iPoseProof:" Hnew "not fresh"
     | _ => tac Hnew
     end];

  try tc_solve.

Local Ltac iSpecializeArgs_go H xs :=
  lazymatch xs with
  | hnil => idtac
  | hcons ?x ?xs =>
     notypeclasses refine (tac_forall_specialize _ H _ _ _ _ _ _ _);
       [pm_reflexivity ||
        let H := pretty_ident H in
        fail "iSpecialize:" H "not found"
       |tc_solve ||
        let P := match goal with |- IntoForall ?P _ => P end in
        fail "iSpecialize: cannot instantiate" P "with" x
       |lazymatch goal with
        | |- ∃ _ : ?A, _ =>
          notypeclasses refine (@ex_intro A _ x _)
        end; [shelve..|pm_reduce; iSpecializeArgs_go H xs]]
  end.
Local Tactic Notation "iSpecializeArgs" constr(H) open_constr(xs) :=
  iSpecializeArgs_go H xs.

Ltac iSpecializePat_go H1 pats :=
  let solve_to_wand H1 :=
    tc_solve ||
    let P := match goal with |- IntoWand _ _ ?P _ _ => P end in
    fail "iSpecialize:" P "not an implication/wand" in
  let solve_done d :=
    lazymatch d with
    | true =>
       first [ done
             | let Q := match goal with |- envs_entails _ ?Q => Q end in
               fail 1 "iSpecialize: cannot solve" Q "using done"
             | let Q := match goal with |- ?Q => Q end in
               fail 1 "iSpecialize: cannot solve" Q "using done" ]
    | false => idtac
    end in
  let Δ := iGetCtx in
  lazymatch pats with
    | [] => idtac
    | SIdent ?H2 [] :: ?pats =>

       notypeclasses refine (tac_specialize false _ H2 _ H1 _ _ _ _ _ _ _ _ _);
         [pm_reflexivity ||
          let H2 := pretty_ident H2 in
          fail "iSpecialize:" H2 "not found"
         |pm_reflexivity ||
          let H1 := pretty_ident H1 in
          fail "iSpecialize:" H1 "not found"
         |tc_solve ||
          let P := match goal with |- IntoWand _ _ ?P ?Q _ => P end in
          let Q := match goal with |- IntoWand _ _ ?P ?Q _ => Q end in
          fail "iSpecialize: cannot instantiate" P "with" Q
         |pm_reduce; iSpecializePat_go H1 pats]
    | SIdent ?H2 ?pats1 :: ?pats =>

       let H2tmp := iFresh in
       iPoseProofCoreHyp H2 as H2tmp;

       iRevertHyp H1 with (fun p =>
         iSpecializePat_go H2tmp pats1;
           [..
           |iIntro H1 as p]);

         [..
         |
          notypeclasses refine (tac_specialize true _ H2tmp _ H1 _ _ _ _ _ _ _ _ _);
            [pm_reflexivity ||
             let H2tmp := pretty_ident H2tmp in
             fail "iSpecialize:" H2tmp "not found"
            |pm_reflexivity ||
             let H1 := pretty_ident H1 in
             fail "iSpecialize:" H1 "not found"
            |tc_solve ||
             let P := match goal with |- IntoWand _ _ ?P ?Q _ => P end in
             let Q := match goal with |- IntoWand _ _ ?P ?Q _ => Q end in
             fail "iSpecialize: cannot instantiate" P "with" Q
            |pm_reduce; iSpecializePat_go H1 pats]]
    | SPureGoal ?d :: ?pats =>
       notypeclasses refine (tac_specialize_assert_pure _ H1 _ _ _ _ _ _ _ _ _ _ _ _);
         [pm_reflexivity ||
          let H1 := pretty_ident H1 in
          fail "iSpecialize:" H1 "not found"
         |solve_to_wand H1
         |tc_solve ||
          let Q := match goal with |- FromPure _ ?Q _ => Q end in
          fail "iSpecialize:" Q "not pure"
         |solve_done d
         |pm_reduce;
          iSpecializePat_go H1 pats]
    | SGoal (SpecGoal GIntuitionistic false ?Hs_frame [] ?d) :: ?pats =>
       notypeclasses refine (tac_specialize_assert_intuitionistic _ H1 _ _ _ _ _ _ _ _ _ _ _ _);
         [pm_reflexivity ||
          let H1 := pretty_ident H1 in
          fail "iSpecialize:" H1 "not found"
         |solve_to_wand H1
         |tc_solve ||
          let Q := match goal with |- Persistent ?Q => Q end in
          fail "iSpecialize:" Q "not persistent"
         |tc_solve
         |pm_reduce; iFrame Hs_frame; solve_done d
         |pm_reduce; iSpecializePat_go H1 pats]
    | SGoal (SpecGoal GIntuitionistic _ _ _ _) :: ?pats =>
       fail "iSpecialize: cannot select hypotheses for intuitionistic premise"
    | SGoal (SpecGoal ?m ?lr ?Hs_frame ?Hs ?d) :: ?pats =>
       let Hs' := eval cbv in (if lr then Hs else Hs_frame ++ Hs) in
       notypeclasses refine (tac_specialize_assert _ H1 _
           (if m is GModal then true else false) lr Hs' _ _ _ _ _ _ _ _ _);
         [pm_reflexivity ||
          let H1 := pretty_ident H1 in
          fail "iSpecialize:" H1 "not found"
         |solve_to_wand H1
         |tc_solve || fail "iSpecialize: goal not a modality"
         |pm_reduce;
          lazymatch goal with
          | |- False =>
            let Hs' := iMissingHypsCore Δ Hs' in
            fail "iSpecialize: hypotheses" Hs' "not found"
          | _ =>
            notypeclasses refine (conj _ _);
              [iFrame Hs_frame; solve_done d
              |iSpecializePat_go H1 pats]
          end]
    | SAutoFrame GIntuitionistic :: ?pats =>
       notypeclasses refine (tac_specialize_assert_intuitionistic _ H1 _ _ _ _ _ _ _ _ _ _ _ _);
         [pm_reflexivity ||
          let H1 := pretty_ident H1 in
          fail "iSpecialize:" H1 "not found"
         |solve_to_wand H1
         |tc_solve ||
          let Q := match goal with |- Persistent ?Q => Q end in
          fail "iSpecialize:" Q "not persistent"
         |tc_solve ||
          fail "iSpecialize: Cannot find IntoAbsorbingly;"
               "this should not happen, please report a bug"
         |pm_reduce; solve [iFrame "∗ #"]
         |pm_reduce; iSpecializePat_go H1 pats]
    | SAutoFrame ?m :: ?pats =>
       notypeclasses refine (tac_specialize_frame _ H1 _
           (if m is GModal then true else false) _ _ _ _ _ _ _ _ _ _ _);
         [pm_reflexivity ||
          let H1 := pretty_ident H1 in
          fail "iSpecialize:" H1 "not found"
         |solve_to_wand H1
         |tc_solve || fail "iSpecialize: goal not a modality"
         |pm_reduce;
          first
            [notypeclasses refine (tac_unlock_emp _ _ _)
            |notypeclasses refine (tac_unlock_True _ _ _)
            |iFrame "∗ #"; notypeclasses refine (tac_unlock _ _ _)
            |let P :=
               match goal with |- envs_entails _ (?P ∗ locked _)%I => P end in
             fail 1 "iSpecialize: premise" P "cannot be solved by framing"]
         |exact eq_refl]; iIntro H1; iSpecializePat_go H1 pats
    end.

Local Tactic Notation "iSpecializePat" open_constr(H) constr(pat) :=
  let pats := spec_pat.parse pat in iSpecializePat_go H pats.

Fixpoint use_tac_specialize_intuitionistic_helper {M}
    (Δ : envs M) (pats : list spec_pat) : bool :=
  match pats with
  | [] => false
  | SPureGoal _ :: pats =>
     use_tac_specialize_intuitionistic_helper Δ pats
  | SAutoFrame _ :: _ => true
  | SIdent H _ :: pats =>
     match envs_lookup_delete false H Δ with
     | Some (false, _, Δ) => true
     | Some (true, _, Δ) => use_tac_specialize_intuitionistic_helper Δ pats
     | None => false
     end
  | SGoal (SpecGoal GModal _ _ _ _) :: _ => false
  | SGoal (SpecGoal GIntuitionistic _ _ _ _) :: pats =>
     use_tac_specialize_intuitionistic_helper Δ pats
  | SGoal (SpecGoal GSpatial neg Hs_frame Hs _) :: pats =>
     match envs_split (if neg is true then Right else Left)
                      (if neg then Hs else pm_app Hs_frame Hs) Δ with
     | Some (Δ1,Δ2) => if env_spatial_is_nil Δ1
                       then use_tac_specialize_intuitionistic_helper Δ2 pats
                       else true
     | None => false
     end
  end.

Tactic Notation "iSpecializeCore" open_constr(H)
    "with" open_constr(xs) open_constr(pat) "as" constr(p) :=
  let p := intro_pat_intuitionistic p in
  let pat := spec_pat.parse pat in
  let H :=
    lazymatch type of H with
    | string => constr:(INamed H)
    | _ => H
    end in
  iSpecializeArgs H xs; [..|
    lazymatch type of H with
    | ident =>
       let pat := spec_pat.parse pat in
       let Δ := iGetCtx in

       let b := eval lazy [use_tac_specialize_intuitionistic_helper] in
         (if p then use_tac_specialize_intuitionistic_helper Δ pat else false) in
       lazymatch eval pm_eval in b with
       | true =>

          lazymatch iTypeOf H with
          | Some (?q, _) =>
             let PROP := iBiOfGoal in

             lazymatch eval lazy in (q || tc_to_bool (BiAffine PROP)) with
             | true =>
                notypeclasses refine (tac_specialize_intuitionistic_helper _ H _ _ _ _ _ _ _ _ _ _);
                  [pm_reflexivity

                  |pm_reduce; tc_solve

                  |iSpecializePat H pat;
                    [..
                    |notypeclasses refine (tac_specialize_intuitionistic_helper_done _ H _ _ _);
                     pm_reflexivity]
                  |tc_solve ||
                   let Q := match goal with |- IntoPersistent _ ?Q _ => Q end in
                   fail "iSpecialize:" Q "not persistent"
                  |pm_reduce ]
             | false => iSpecializePat H pat
             end
          | None =>
             let H := pretty_ident H in
             fail "iSpecialize:" H "not found"
          end
       | false => iSpecializePat H pat
       end
    | _ => fail "iSpecialize:" H "should be a hypothesis, use iPoseProof instead"
    end].

Tactic Notation "iSpecializeCore" open_constr(t) "as" constr(p) :=
  lazymatch type of t with
  | string => iSpecializeCore t with hnil "" as p
  | ident => iSpecializeCore t with hnil "" as p
  | _ =>
    lazymatch t with
    | ITrm ?H ?xs ?pat => iSpecializeCore H with xs pat as p
    | _ => fail "iSpecialize:" t "should be a proof mode term"
    end
  end.

Tactic Notation "iPoseProofCore" open_constr(lem)
    "as" constr(p) tactic3(tac) :=
  iStartProof;
  let t := lazymatch lem with ITrm ?t ?xs ?pat => t | _ => lem end in
  let t := lazymatch type of t with string => constr:(INamed t) | _ => t end in
  let spec_tac Htmp :=
    lazymatch lem with
    | ITrm _ ?xs ?pat => iSpecializeCore (ITrm Htmp xs pat) as p
    | _ => idtac
    end in
  lazymatch type of t with
  | ident =>
     let Htmp := iFresh in
     iPoseProofCoreHyp t as Htmp; spec_tac Htmp; [..|tac Htmp]
  | _ => iPoseProofCoreLem t as (fun Htmp => spec_tac Htmp; [..|tac Htmp])
  end.

Tactic Notation "iOrDestruct" constr(H) "as" constr(H1) constr(H2) :=
  eapply tac_or_destruct with H _ H1 H2 _ _ _;
    [pm_reflexivity ||
     let H := pretty_ident H in
     fail "iOrDestruct:" H "not found"
    |tc_solve ||
     let P := match goal with |- IntoOr ?P _ _ => P end in
     fail "iOrDestruct: cannot destruct" P
    | pm_reduce;
      lazymatch goal with
      | |- False =>
        let H1 := pretty_ident H1 in
        let H2 := pretty_ident H2 in
        fail "iOrDestruct:" H1 "or" H2 "not fresh"
      |  _ => split
      end].

Local Tactic Notation "iAndDestruct" constr(H) "as" constr(H1) constr(H2) :=
  eapply tac_and_destruct with H _ H1 H2 _ _ _;
    [pm_reflexivity ||
     let H := pretty_ident H in
     fail "iAndDestruct:" H "not found"
    |pm_reduce; tc_solve ||
     let P :=
       lazymatch goal with
       | |- IntoSep ?P _ _ => P
       | |- IntoAnd _ ?P _ _ => P
       end in
     fail "iAndDestruct: cannot destruct" P
    |pm_reduce;
     lazymatch goal with
       | |- False =>
         let H1 := pretty_ident H1 in
         let H2 := pretty_ident H2 in
         fail "iAndDestruct:" H1 "or" H2 "not fresh"
       | _ => idtac
     end].

Local Tactic Notation "iAndDestructChoice" constr(H) "as" constr(d) constr(H') :=
  eapply tac_and_destruct_choice with H _ d H' _ _ _;
    [pm_reflexivity || fail "iAndDestructChoice:" H "not found"
    |pm_reduce; tc_solve ||
     let P := match goal with |- TCOr (IntoAnd _ ?P _ _) _ => P end in
     fail "iAndDestructChoice: cannot destruct" P
    |pm_reduce;
     lazymatch goal with
     | |- False =>
       let H' := pretty_ident H' in
       fail "iAndDestructChoice:" H' "not fresh"
     | _ => idtac
     end].

Ltac _iExists x :=
  iStartProof;
  eapply tac_exist;
    [tc_solve ||
     let P := match goal with |- FromExist ?P _ => P end in
     fail "iExists:" P "not an existential"
    |pm_prettify; eexists x
      ].

Tactic Notation "iExists" ne_uconstr_list_sep(xs,",") :=
  ltac1_list_iter _iExists xs.

Local Tactic Notation "iExistDestruct" constr(H)
    "as" simple_intropattern(x) constr(Hx) :=
  eapply tac_exist_destruct with H _ Hx _ _ _;
    [pm_reflexivity ||
     let H := pretty_ident H in
     fail "iExistDestruct:" H "not found"
    |tc_solve ||
     let P := match goal with |- IntoExist ?P _ _ => P end in
     fail "iExistDestruct: cannot destruct" P|];
    let name := lazymatch goal with
                | |- let _ := (λ name, _) in _ => name
                end in
    intros _;
    let y := fresh name in
    intros y; pm_reduce;
    lazymatch goal with
    | |- False =>
      let Hx := pretty_ident Hx in
      fail "iExistDestruct:" Hx "not fresh"
    | _ => revert y; intros x
    end.

Tactic Notation "iModIntro" uconstr(sel) :=
  iStartProof;
  notypeclasses refine (tac_modal_intro _ _ sel _ _ _ _ _ _ _ _ _ _ _ _ _ _);
    [tc_solve ||
     fail "iModIntro: the goal is not a modality"
    |tc_solve ||
     let s := lazymatch goal with |- IntoModalIntuitionisticEnv _ _ _ ?s => s end in
     lazymatch eval hnf in s with
     | MIEnvForall ?C => fail "iModIntro: intuitionistic context does not satisfy" C
     | MIEnvIsEmpty => fail "iModIntro: intuitionistic context is non-empty"
     end
    |tc_solve ||
     let s := lazymatch goal with |- IntoModalSpatialEnv _ _ _ ?s _ => s end in
     lazymatch eval hnf in s with
     | MIEnvForall ?C => fail "iModIntro: spatial context does not satisfy" C
     | MIEnvIsEmpty => fail "iModIntro: spatial context is non-empty"
     end
    |pm_reduce; tc_solve ||
     fail "iModIntro: cannot filter spatial context when goal is not absorbing"
    |iSolveSideCondition
    |pm_prettify
      ].
Tactic Notation "iModIntro" := iModIntro _.

Tactic Notation "iModCore" constr(H) "as" constr(H') :=
  eapply tac_modal_elim with H H' _ _ _ _ _ _;
    [pm_reflexivity || fail "iMod:" H "not found"
    |tc_solve ||
     let P := match goal with |- ElimModal _ _ _ ?P _ _ _ => P end in
     let Q := match goal with |- ElimModal _ _ _ _ _ ?Q _ => Q end in
     fail "iMod: cannot eliminate modality" P "in" Q
    |iSolveSideCondition
    |pm_reduce;
     lazymatch goal with
     | |- False =>
       let H' := pretty_ident H' in
       fail "iMod:" H' "not fresh"
     | _ => pm_prettify
     end].

Local Ltac ident_for_pat pat :=
  lazymatch pat with
  | IIdent ?x => x
  | _ => let x := iFresh in x
  end.

Local Ltac ident_for_pat_default pat default :=
  lazymatch pat with
  | IIdent ?x => x
  | _ =>
    lazymatch default with
    | IAnon _ => default
    | _ => let x := iFresh in x
    end
  end.

Local Ltac iDestructHypGo Hz pat0 pat :=
  lazymatch pat with
  | IFresh =>
     lazymatch Hz with
     | IAnon _ => idtac
     | INamed ?Hz => let Hz' := iFresh in iRename Hz into Hz'
     end
  | IDrop => iClearHyp Hz
  | IFrame => iFrameHyp Hz
  | IIdent Hz => idtac
  | IIdent ?y => iRename Hz into y
  | IList [[]] => iExFalso; iExact Hz

  | IList [[?pat1; IDrop]] =>
     let x := ident_for_pat_default pat1 Hz in
     iAndDestructChoice Hz as Left x;
     iDestructHypGo x pat0 pat1
  | IList [[IDrop; ?pat2]] =>
     let x := ident_for_pat_default pat2 Hz in
     iAndDestructChoice Hz as Right x;
     iDestructHypGo x pat0 pat2

  | IList [[IPure IGallinaAnon; ?pat2]] =>
     let x := ident_for_pat_default pat2 Hz in
     iExistDestruct Hz as ? x; iDestructHypGo x pat0 pat2
  | IList [[IPure (IGallinaNamed ?s); ?pat2]] =>
     let x := fresh in
     let y := ident_for_pat_default pat2 Hz in
     iExistDestruct Hz as x y;
     rename_by_string x s;
     iDestructHypGo y pat0 pat2
  | IList [[?pat1; ?pat2]] =>

     let x1 := ident_for_pat_default pat1 Hz in
     let x2 := ident_for_pat pat2 in
     iAndDestruct Hz as x1 x2;
     iDestructHypGo x1 pat0 pat1; iDestructHypGo x2 pat0 pat2
  | IList [_ :: _ :: _] => fail "iDestruct:" pat0 "has too many conjuncts"
  | IList [[_]] => fail "iDestruct:" pat0 "has just a single conjunct"

  | IList [[?pat1];[?pat2]] =>
     let x1 := ident_for_pat_default pat1 Hz in
     let x2 := ident_for_pat_default pat2 Hz in
     iOrDestruct Hz as x1 x2;
     [iDestructHypGo x1 pat0 pat1|iDestructHypGo x2 pat0 pat2]

  | IList (_ :: _ :: _ :: _) => fail "iDestruct:" pat0 "has too many disjuncts"

  | IList [_;_] => fail "iDestruct: in" pat0 "a disjunct has multiple patterns"

  | IPure IGallinaAnon => iPure Hz as ?
  | IPure (IGallinaNamed ?s) =>
     let x := fresh in
     iPure Hz as x;
     rename_by_string x s
  | IRewrite Right => iPure Hz as ->
  | IRewrite Left => iPure Hz as <-
  | IIntuitionistic ?pat =>
    let x := ident_for_pat_default pat Hz in
    iIntuitionistic Hz as x; iDestructHypGo x pat0 pat
  | ISpatial ?pat =>
    let x := ident_for_pat_default pat Hz in
    iSpatial Hz as x; iDestructHypGo x pat0 pat
  | IModalElim ?pat =>
    let x := ident_for_pat_default pat Hz in
    iModCore Hz as x; iDestructHypGo x pat0 pat
  | _ => fail "iDestruct:" pat0 "is not supported due to" pat
  end.
Local Ltac iDestructHypFindPat Hgo pat found pats :=
  lazymatch pats with
  | [] =>
    lazymatch found with
    | true => pm_prettify
    | false => fail "iDestruct:" pat "should contain exactly one proper introduction pattern"
    end
  | ISimpl :: ?pats => simpl; iDestructHypFindPat Hgo pat found pats
  | IClear ?H :: ?pats => iClear H; iDestructHypFindPat Hgo pat found pats
  | IClearFrame ?H :: ?pats => iFrame H; iDestructHypFindPat Hgo pat found pats
  | ?pat1 :: ?pats =>
     lazymatch found with
     | false => iDestructHypGo Hgo pat pat1; iDestructHypFindPat Hgo pat true pats
     | true => fail "iDestruct:" pat "should contain exactly one proper introduction pattern"
     end
  end.

Ltac _iDestructHyp0 H pat :=
  let pats := intro_pat.parse pat in
  iDestructHypFindPat H pat false pats.
Ltac _iDestructHyp H xs pat :=
  ltac1_list_iter ltac:(fun x => iExistDestruct H as x H) xs;
  _iDestructHyp0 H pat.

Tactic Notation "iDestructHyp" constr(H) "as" constr(pat) :=
  _iDestructHyp0 H pat.

Ltac _iIntros_go pats startproof :=
  lazymatch pats with
  | [] =>
    lazymatch startproof with
    | true => iStartProof
    | false => idtac
    end

  | IPure (IGallinaNamed ?s) :: ?pats =>
     let i := fresh in
     iIntro (i);
     rename_by_string i s;
     _iIntros_go pats startproof
  | IPure IGallinaAnon :: ?pats => iIntro (?); _iIntros_go pats startproof
  | IIntuitionistic (IIdent ?H) :: ?pats => iIntro #H; _iIntros_go pats false
  | IDrop :: ?pats => iIntro _; _iIntros_go pats startproof
  | IIdent ?H :: ?pats => iIntro H; _iIntros_go pats startproof

  | IPureIntro :: ?pats => iPureIntro; _iIntros_go pats false
  | IModalIntro :: ?pats => iModIntro; _iIntros_go pats false
  | IForall :: ?pats => repeat iIntroForall; _iIntros_go pats startproof
  | IAll :: ?pats => repeat (iIntroForall || iIntro); _iIntros_go pats startproof

  | ISimpl :: ?pats => simpl; _iIntros_go pats startproof
  | IClear ?H :: ?pats => iClear H; _iIntros_go pats false
  | IClearFrame ?H :: ?pats => iFrame H; _iIntros_go pats false
  | IDone :: ?pats => try done; _iIntros_go pats startproof

  | IIntuitionistic ?pat :: ?pats =>
     let H := iFresh in iIntro #H; iDestructHyp H as pat; _iIntros_go pats false
  | ?pat :: ?pats =>
     let H := iFresh in iIntro H; iDestructHyp H as pat; _iIntros_go pats false
  end.

Ltac _iIntros0 pat :=
  let pats := intro_pat.parse pat in

  lazymatch pats with
  | [] => idtac
  | _ => _iIntros_go pats true
  end.
Ltac _iIntros xs pat :=
  ltac1_list_iter ltac:(fun x => iIntro (x)) xs;
  _iIntros0 pat.
Tactic Notation "iIntros" "(" ne_simple_intropattern_list(xs) ")" constr(pat) :=
  _iIntros xs pat.

Tactic Notation "iDestructCore" open_constr(lem) "as" constr(p) tactic3(tac) :=
  let intro_destruct n :=
    let rec go n' :=
      lazymatch n' with
      | 0 => fail "iDestruct: cannot introduce" n "hypotheses"
      | 1 => repeat iIntroForall; let H := iFresh in iIntro H; tac H
      | S ?n' => repeat iIntroForall; let H := iFresh in iIntro H; go n'
      end in
    intros; go n in
  lazymatch type of lem with
  | nat => intro_destruct lem
  | Z =>

     let n := eval cbv in (Z.to_nat lem) in intro_destruct n
  | ident => tac lem
  | string => tac constr:(INamed lem)
  | _ => iPoseProofCore lem as p tac
  end.
Tactic Notation "iMod" open_constr(lem) "as" "(" ne_simple_intropattern_list(xs) ")"
    constr(pat) :=
  iDestructCore lem as false (fun H => iModCore H as H; last _iDestructHyp H xs pat).

Global Hint Extern 0 (envs_entails _ _) => iPureIntro; try done : core.

Lemma from_assumption_exact {PROP : bi} p (P : PROP) : FromAssumption p P P.
Admitted.
Global Hint Extern 0 (FromAssumption _ _ _) =>
  notypeclasses refine (from_assumption_exact _ _); shelve : typeclass_instances.

Lemma from_exist_exist {PROP : bi} {A} (Φ : A → PROP) : FromExist (∃ a, Φ a) Φ.
Admitted.
Global Hint Extern 0 (FromExist _ _) =>
  notypeclasses refine (from_exist_exist _) : typeclass_instances.

Section class_instances.
Context {PROP : bi}.
Implicit Types P Q R : PROP.

Global Instance as_emp_valid_emp_valid P : AsEmpValid0 (⊢ P) P | 0.
Admitted.
Global Instance from_pure_pure φ : @FromPure PROP false ⌜φ⌝ φ.
Admitted.
Global Instance into_persistent_intuitionistically p P Q :
  IntoPersistent true P Q → IntoPersistent p (□ P) Q | 0.
Admitted.
Global Instance into_persistent_here P : IntoPersistent true P P | 1.
Admitted.

Global Instance into_wand_wand p q P Q P' :
  FromAssumption q P P' → IntoWand p q (P' -∗ Q) P Q.
Admitted.

Global Instance from_wand_wand P1 P2 : FromWand (P1 -∗ P2) P1 P2.
Admitted.

Global Instance into_sep_sep P Q : IntoSep (P ∗ Q) P Q.
Admitted.

Global Instance into_exist_exist {A} (Φ : A → PROP) name :
  AsIdentName Φ name → IntoExist (bi_exist Φ) Φ name.
Admitted.
End class_instances.

Section class_instances_updates.
Context {PROP : bi}.
Implicit Types P Q R : PROP.

Global Instance from_modal_bupd `{!BiBUpd PROP} P :
  FromModal True modality_id (|==> P) (|==> P) P.
Admitted.

Global Instance elim_modal_bupd `{!BiBUpd PROP} p P Q :
  ElimModal True p false (|==> P) P (|==> Q) (|==> Q).
Admitted.
End class_instances_updates.
Export iris.algebra.cmra.

Record agree (A : Type) : Type := {
  agree_car : list A;
  agree_not_nil : bool_decide (agree_car = []) = false
}.
Global Arguments agree_car {_} _.
Definition to_agree {A} (a : A) : agree A.
Admitted.

Section agree.
Context {A : ofe}.
Local Instance agree_dist : Dist (agree A).
Admitted.
Local Instance agree_equiv : Equiv (agree A).
Admitted.

Definition agree_ofe_mixin : OfeMixin (agree A).
Admitted.
Canonical Structure agreeO := Ofe (agree A) agree_ofe_mixin.
Local Instance agree_validN_instance : ValidN (agree A).
Admitted.
Local Instance agree_valid_instance : Valid (agree A).
Admitted.

Local Program Instance agree_op_instance : Op (agree A) := λ x y,
  {| agree_car := agree_car x ++ agree_car y |}.
Admit Obligations.
Local Instance agree_pcore_instance : PCore (agree A).
Admitted.

Definition agree_cmra_mixin : CmraMixin (agree A).
Admitted.
Canonical Structure agreeR : cmra.
exact (Cmra (agree A) agree_cmra_mixin).
Defined.

End agree.
Global Arguments agreeR : clear implicits.

Notation frac := Qp (only parsing).
  Canonical Structure fracO := leibnizO frac.
Local Instance frac_valid_instance : Valid frac.
Admitted.
Local Instance frac_pcore_instance : PCore frac.
Admitted.
Local Instance frac_op_instance : Op frac.
Admitted.

  Definition frac_ra_mixin : RAMixin frac.
Admitted.
  Canonical Structure fracR := discreteR frac frac_ra_mixin.

Inductive dfrac :=
  | DfracOwn : Qp → dfrac
  | DfracDiscarded : dfrac
  | DfracBoth : Qp → dfrac.

Declare Custom Entry dfrac.
Notation "" := (DfracOwn 1) (in custom dfrac).

Structure view_rel (A : ofe) (B : ucmra) := ViewRel {
  view_rel_holds :> nat → A → B → Prop;
  view_rel_mono n1 n2 a1 a2 b1 b2 :
    view_rel_holds n1 a1 b1 →
    a1 ≡{n2}≡ a2 →
    b2 ≼{n2} b1 →
    n2 ≤ n1 →
    view_rel_holds n2 a2 b2;
  view_rel_validN n a b :
    view_rel_holds n a b → ✓{n} b;
  view_rel_unit n :
    ∃ a, view_rel_holds n a ε
}.
Global Arguments ViewRel {_ _} _ _.

Record view {A B} (rel : nat → A → B → Prop) :=
  View { view_auth_proj : option (dfrac * agree A) ; view_frag_proj : B }.

Section ofe.
  Context {A B : ofe} (rel : nat → A → B → Prop).
Local Instance view_equiv : Equiv (view rel).
Admitted.
Local Instance view_dist : Dist (view rel).
Admitted.

  Definition view_ofe_mixin : OfeMixin (view rel).
Admitted.
  Canonical Structure viewO := Ofe (view rel) view_ofe_mixin.
End ofe.

Section cmra.
  Context {A B} (rel : view_rel A B).
Local Instance view_valid_instance : Valid (view rel).
Admitted.
Local Instance view_validN_instance : ValidN (view rel).
Admitted.
Local Instance view_pcore_instance : PCore (view rel).
Admitted.
Local Instance view_op_instance : Op (view rel).
Admitted.

  Lemma view_cmra_mixin : CmraMixin (view rel).
Admitted.
  Canonical Structure viewR := Cmra (view rel) view_cmra_mixin.
Local Instance view_empty_instance : Unit (view rel).
Admitted.
  Lemma view_ucmra_mixin : UcmraMixin (view rel).
Admitted.
  Canonical Structure viewUR := Ucmra (view rel) view_ucmra_mixin.

End cmra.
Definition viewO_map {A A' B B' : ofe}
    {rel : nat → A → B → Prop} {rel' : nat → A' → B' → Prop}
    (f : A -n> A') (g : B -n> B') : viewO rel -n> viewO rel'.
Admitted.
Definition auth_view_rel_raw {A : ucmra} (n : nat) (a b : A) : Prop.
Admitted.
Lemma auth_view_rel_raw_mono (A : ucmra) n1 n2 (a1 a2 b1 b2 : A) :
  auth_view_rel_raw n1 a1 b1 →
  a1 ≡{n2}≡ a2 →
  b2 ≼{n2} b1 →
  n2 ≤ n1 →
  auth_view_rel_raw n2 a2 b2.
Admitted.
Lemma auth_view_rel_raw_valid (A : ucmra) n (a b : A) :
  auth_view_rel_raw n a b → ✓{n} b.
Admitted.
Lemma auth_view_rel_raw_unit (A : ucmra) n :
  ∃ a : A, auth_view_rel_raw n a ε.
Admitted.
Canonical Structure auth_view_rel {A : ucmra} : view_rel A A.
exact (ViewRel auth_view_rel_raw (auth_view_rel_raw_mono A)
          (auth_view_rel_raw_valid A) (auth_view_rel_raw_unit A)).
Defined.

Notation auth A := (view (A:=A) (B:=A) auth_view_rel_raw).
Definition authR (A : ucmra) : cmra.
exact (viewR (A:=A) (B:=A) auth_view_rel).
Defined.
Definition authUR (A : ucmra) : ucmra.
exact (viewUR (A:=A) (B:=A) auth_view_rel).
Defined.
Definition auth_auth {A: ucmra} : dfrac → A → auth A.
Admitted.
Definition auth_frag {A: ucmra} : A → auth A.
Admitted.

Notation "● dq a" := (auth_auth dq a)
  (at level 20, dq custom dfrac at level 1, format "● dq  a").
Notation "◯ a" := (auth_frag a) (at level 20).

Program Definition authURF (F : urFunctor) : urFunctor := {|
  urFunctor_car A _ B _ := authUR (urFunctor_car F A B);
  urFunctor_map A1 _ A2 _ B1 _ B2 _ fg :=
    viewO_map (urFunctor_map F fg) (urFunctor_map F fg)
|}.
Admit Obligations.

Program Definition authRF (F : urFunctor) : rFunctor := {|
  rFunctor_car A _ B _ := authR (urFunctor_car F A B);
  rFunctor_map A1 _ A2 _ B1 _ B2 _ fg :=
    viewO_map (urFunctor_map F fg) (urFunctor_map F fg)
|}.
Solve Obligations with apply authURF.

Record uPred (M : ucmra) : Type := UPred {
  uPred_holds : nat → M → Prop;

  uPred_mono n1 n2 x1 x2 :
    uPred_holds n1 x1 → x1 ≼{n2} x2 → n2 ≤ n1 → uPred_holds n2 x2
}.

Local Coercion uPred_holds : uPred >-> Funclass.
Bind Scope bi_scope with uPred.

Section cofe.
  Context {M : ucmra}.
Local Instance uPred_equiv : Equiv (uPred M).
Admitted.
Local Instance uPred_dist : Dist (uPred M).
Admitted.
  Definition uPred_ofe_mixin : OfeMixin (uPred M).
Admitted.
Canonical Structure uPredO : ofe.
exact (Ofe (uPred M) uPred_ofe_mixin).
Defined.

  Program Definition uPred_compl : Compl uPredO := λ c,
    {| uPred_holds n x := ∀ n', n' ≤ n → ✓{n'} x → c n' n' x |}.
Admit Obligations.
  Global Program Instance uPred_cofe : Cofe uPredO := {| compl := uPred_compl |}.
Admit Obligations.
End cofe.
Global Arguments uPredO : clear implicits.

Inductive uPred_entails {M} (P Q : uPred M) : Prop :=
  { uPred_in_entails : ∀ n x, ✓{n} x → P n x → Q n x }.
Global Hint Resolve uPred_mono : uPred_def.

Local Program Definition uPred_pure_def {M} (φ : Prop) : uPred M :=
  {| uPred_holds n x := φ |}.
Solve Obligations with done.
Local Definition uPred_pure_aux : seal (@uPred_pure_def).
Admitted.
Definition uPred_pure := uPred_pure_aux.(unseal).
Global Arguments uPred_pure {M}.

Local Program Definition uPred_and_def {M} (P Q : uPred M) : uPred M :=
  {| uPred_holds n x := P n x ∧ Q n x |}.
Solve Obligations with naive_solver eauto 2 with uPred_def.
Local Definition uPred_and_aux : seal (@uPred_and_def).
Admitted.
Definition uPred_and := uPred_and_aux.(unseal).
Global Arguments uPred_and {M}.

Local Program Definition uPred_or_def {M} (P Q : uPred M) : uPred M :=
  {| uPred_holds n x := P n x ∨ Q n x |}.
Solve Obligations with naive_solver eauto 2 with uPred_def.
Local Definition uPred_or_aux : seal (@uPred_or_def).
Admitted.
Definition uPred_or := uPred_or_aux.(unseal).
Global Arguments uPred_or {M}.

Local Program Definition uPred_impl_def {M} (P Q : uPred M) : uPred M :=
  {| uPred_holds n x := ∀ n' x',
       x ≼ x' → n' ≤ n → ✓{n'} x' → P n' x' → Q n' x' |}.
Admit Obligations.
Local Definition uPred_impl_aux : seal (@uPred_impl_def).
Admitted.
Definition uPred_impl := uPred_impl_aux.(unseal).
Global Arguments uPred_impl {M}.

Local Program Definition uPred_forall_def {M A} (Ψ : A → uPred M) : uPred M :=
  {| uPred_holds n x := ∀ a, Ψ a n x |}.
Solve Obligations with naive_solver eauto 2 with uPred_def.
Local Definition uPred_forall_aux : seal (@uPred_forall_def).
Admitted.
Definition uPred_forall := uPred_forall_aux.(unseal).

Local Program Definition uPred_exist_def {M A} (Ψ : A → uPred M) : uPred M :=
  {| uPred_holds n x := ∃ a, Ψ a n x |}.
Solve Obligations with naive_solver eauto 2 with uPred_def.
Local Definition uPred_exist_aux : seal (@uPred_exist_def).
Admitted.
Definition uPred_exist := uPred_exist_aux.(unseal).

Local Program Definition uPred_sep_def {M} (P Q : uPred M) : uPred M :=
  {| uPred_holds n x := ∃ x1 x2, x ≡{n}≡ x1 ⋅ x2 ∧ P n x1 ∧ Q n x2 |}.
Admit Obligations.
Local Definition uPred_sep_aux : seal (@uPred_sep_def).
Admitted.
Definition uPred_sep := uPred_sep_aux.(unseal).
Global Arguments uPred_sep {M}.

Local Program Definition uPred_wand_def {M} (P Q : uPred M) : uPred M :=
  {| uPred_holds n x := ∀ n' x',
       n' ≤ n → ✓{n'} (x ⋅ x') → P n' x' → Q n' (x ⋅ x') |}.
Admit Obligations.
Local Definition uPred_wand_aux : seal (@uPred_wand_def).
Admitted.
Definition uPred_wand := uPred_wand_aux.(unseal).
Global Arguments uPred_wand {M}.

Local Program Definition uPred_plainly_def {M} (P : uPred M) : uPred M :=
  {| uPred_holds n x := P n ε |}.
Solve Obligations with naive_solver eauto using uPred_mono, ucmra_unit_validN.

Local Program Definition uPred_persistently_def {M} (P : uPred M) : uPred M :=
  {| uPred_holds n x := P n (core x) |}.
Solve Obligations with naive_solver eauto using uPred_mono, cmra_core_monoN.
Local Definition uPred_persistently_aux : seal (@uPred_persistently_def).
Admitted.
Definition uPred_persistently := uPred_persistently_aux.(unseal).
Global Arguments uPred_persistently {M}.

Local Program Definition uPred_later_def {M} (P : uPred M) : uPred M :=
  {| uPred_holds n x := match n return _ with 0 => True | S n' => P n' x end |}.
Admit Obligations.
Local Definition uPred_later_aux : seal (@uPred_later_def).
Admitted.
Definition uPred_later := uPred_later_aux.(unseal).
Global Arguments uPred_later {M}.
Definition uPred_emp {M} : uPred M.
Admitted.

Lemma uPred_bi_mixin (M : ucmra) :
  BiMixin
    uPred_entails uPred_emp uPred_pure uPred_and uPred_or uPred_impl
    (@uPred_forall M) (@uPred_exist M) uPred_sep uPred_wand.
Admitted.

Lemma uPred_bi_persistently_mixin (M : ucmra) :
  BiPersistentlyMixin
    uPred_entails uPred_emp uPred_and
    (@uPred_exist M) uPred_sep uPred_persistently.
Admitted.

Lemma uPred_bi_later_mixin (M : ucmra) :
  BiLaterMixin
    uPred_entails uPred_pure uPred_or uPred_impl
    (@uPred_forall M) (@uPred_exist M) uPred_sep uPred_persistently uPred_later.
Admitted.
Canonical Structure uPredI (M : ucmra) : bi.
exact ({| bi_ofe_mixin := ofe_mixin_of (uPred M);
     bi_bi_mixin := uPred_bi_mixin M;
     bi_bi_later_mixin := uPred_bi_later_mixin M;
     bi_bi_persistently_mixin := uPred_bi_persistently_mixin M |}).
Defined.
Global Instance uPred_bi_bupd M : BiBUpd (uPredI M).
Admitted.
Import iris.algebra.gmap.

Structure gFunctor := GFunctor {
  gFunctor_F :> rFunctor;
  gFunctor_map_contractive : rFunctorContractive gFunctor_F;
}.

Record gFunctors := GFunctors {
  gFunctors_len : nat;
  gFunctors_lookup : fin gFunctors_len → gFunctor
}.

Definition gid (Σ : gFunctors) := fin (gFunctors_len Σ).

Definition gname := positive.
Definition iResUR (Σ : gFunctors) : ucmra.
Admitted.
  Notation iProp Σ := (uPred (iResUR Σ)).
  Notation iPropO Σ := (uPredO (iResUR Σ)).

Class inG (Σ : gFunctors) (A : cmra) := InG {
  inG_id : gid Σ;
  inG_apply := rFunctor_apply (gFunctors_lookup Σ inG_id);
  inG_prf : A = inG_apply (iPropO Σ) _;
}.
Local Definition own_def `{!inG Σ A} (γ : gname) (a : A) : iProp Σ.
Admitted.
Local Definition own_aux : seal (@own_def).
Admitted.
Definition own := own_aux.(unseal).
Global Arguments own {Σ A _} γ a.

Section cmra_mlist.

  Context (A: Type) `{EqDecision A}.
  Implicit Types (D: list A).

  Inductive mlist :=
    | MList D : mlist
    | MListBot : mlist.

  Inductive mlist_equiv : Equiv mlist :=
    | MList_equiv D1 D2:
        D1 = D2 → MList D1 ≡ MList D2
    | MListBot_equiv : MListBot ≡ MListBot.

  Existing Instance mlist_equiv.
  Local Instance mlist_equiv_Equivalence : @Equivalence mlist equiv.
Admitted.
Canonical Structure mlistC : ofe.
exact (discreteO mlist).
Defined.
Local Instance mlist_valid : Valid mlist.
Admitted.
Local Instance mlist_op : Op mlist.
Admitted.
Local Instance mlist_PCore : PCore mlist.
Admitted.
Local Instance mlist_unit : Unit mlist.
Admitted.

  Definition mlist_ra_mixin : RAMixin mlist.
Admitted.

  Canonical Structure mlistR := discreteR mlist mlist_ra_mixin.

  Definition mlist_ucmra_mixin : UcmraMixin mlist.
Admitted.

  Canonical Structure mlistUR :=
    Ucmra mlist mlist_ucmra_mixin.

End cmra_mlist.

Global Arguments MList {_} _.

Definition fmlistUR (A: Type) {Heq: EqDecision A} := authUR (mlistUR A).
Class fmlistG (A: Type) {Heq: EqDecision A} Σ :=
  { #[global] fmlist_inG :: inG Σ (fmlistUR A) }.

Section fmlist_props.
Context `{fmlistG A Σ}.
Definition fmlist_lb γ l := own γ (◯ (MList l)).
Definition fmlist_idx γ i a := (∃ l, ⌜ l !! i = Some a ⌝ ∗ fmlist_lb γ l)%I.

End fmlist_props.
Local Instance nat_valid_instance : Valid nat.
Admitted.
Local Instance nat_pcore_instance : PCore nat.
Admitted.
Local Instance nat_op_instance : Op nat.
Admitted.
  Lemma nat_ra_mixin : RAMixin nat.
Admitted.
Canonical Structure natR : cmra.
exact (discreteR nat nat_ra_mixin).
Defined.
Local Instance nat_unit_instance : Unit nat.
Admitted.
  Lemma nat_ucmra_mixin : UcmraMixin nat.
Admitted.
Canonical Structure natUR : ucmra.
exact (Ucmra nat nat_ucmra_mixin).
Defined.

Class lcGpreS (Σ : gFunctors) := LcGpreS {
  #[local] lcGpreS_inG :: inG Σ (authR natUR)
}.

Class lcGS (Σ : gFunctors) := LcGS {
  #[local] lcGS_inG :: inG Σ (authR natUR);
  lcGS_name : gname;
}.
Import iris.algebra.gset.
Import iris.algebra.coPset.

Inductive bi_schema :=
| bi_sch_emp : bi_schema
| bi_sch_pure : Prop → bi_schema
| bi_sch_and : bi_schema → bi_schema → bi_schema
| bi_sch_or : bi_schema → bi_schema → bi_schema
| bi_sch_forall : ∀ A, (A → bi_schema) → bi_schema
| bi_sch_exist : ∀ A, (A → bi_schema) → bi_schema
| bi_sch_sep : bi_schema → bi_schema → bi_schema
| bi_sch_wand : bi_schema → bi_schema → bi_schema
| bi_sch_persistently : bi_schema → bi_schema
| bi_sch_later : bi_schema → bi_schema
| bi_sch_bupd : bi_schema → bi_schema

| bi_sch_var_fixed : nat → bi_schema
| bi_sch_var_mut : nat → bi_schema
| bi_sch_wsat : bi_schema
| bi_sch_ownE : (nat → coPset) → bi_schema.

Canonical Structure bi_schemaO := leibnizO bi_schema.

Record invariant_level_names := { invariant_name : gname; }.

Global Instance invariant_level_names_eq_dec : EqDecision (invariant_level_names).
Admitted.
  Class invGpreS (Σ : gFunctors) : Set := WsatPreG {
    #[global] inv_inPreG :: inG Σ (authR (gmapUR positive
                                    (prodR (agreeR (prodO (listO (laterO (iPropO Σ))) bi_schemaO))
                                           (optionR (prodR fracR (agreeR (listO (laterO (iPropO Σ)))))))));
    #[global] enabled_inPreG :: inG Σ coPset_disjR;
    #[global] disabled_inPreG :: inG Σ (gset_disjR positive);
    #[global] mlist_inPreG :: fmlistG (invariant_level_names) Σ;
    inv_lcPreG : lcGpreS Σ;
  }.

  Class invGS (Σ : gFunctors) : Set := WsatG {
    #[global] inv_inG :: invGpreS Σ;
    #[global] invGS_lc :: lcGS Σ;
    inv_list_name : gname;
    enabled_name : gname;
    disabled_name : gname;
  }.

Definition invariant_unfold {Σ} {n} sch (Ps : vec (iProp Σ) n) : agree (list (later (iPropO Σ)) * bi_schema) :=
  to_agree ((λ P, Next P) <$> (vec_to_list Ps), sch).
Definition inv_mut_unfold {Σ} {n} q (Ps : vec (iProp Σ) n) : option (frac * (agree (list (later (iPropO Σ))))) :=
  Some (q%Qp, to_agree ((λ P, Next P) <$> (vec_to_list Ps))).
Definition ownI `{!invGS Σ} {n} (lvl: nat) (i : positive) (sch: bi_schema) (Ps : vec (iProp Σ) n) : iProp Σ :=
  (∃ γs, fmlist_idx inv_list_name lvl γs ∗
         own (invariant_name γs) (◯ {[ i := (invariant_unfold sch Ps, ε) ]})).

Definition ownI_mut `{!invGS Σ} {n} (lvl: nat) (i : positive) q (Qs : vec (iProp Σ) n) : iProp Σ :=
  (∃ (l: agree (list (later (iPropO Σ)) * bi_schema)) γs, fmlist_idx inv_list_name lvl γs ∗
         own (invariant_name γs) (◯ {[ i := (l, inv_mut_unfold q Qs) ]})).
Definition ownE `{!invGS Σ} (E : coPset) : iProp Σ.
Admitted.
Definition ownD `{!invGS Σ} (E : gset positive) : iProp Σ.
Admitted.

Definition inv_cmra_fmap `{!invGS Σ} (v: (list (iProp Σ) * bi_schema) * list (iProp Σ)) :=
  let '((Ps, sch), Qs) := v in
  (invariant_unfold sch (list_to_vec Ps), inv_mut_unfold 1%Qp (list_to_vec Qs)).

Fixpoint bi_schema_pre `{!invGS Σ} n (Ps Ps_mut: list (iProp Σ)) wsat (sch: bi_schema) :=
  match sch with
  | bi_sch_emp => emp
  | bi_sch_pure φ => ⌜φ⌝
  | bi_sch_and sch1 sch2 => bi_schema_pre n Ps Ps_mut wsat sch1 ∧ bi_schema_pre n Ps Ps_mut wsat sch2
  | bi_sch_or sch1 sch2 => bi_schema_pre n Ps Ps_mut wsat sch1 ∨ bi_schema_pre n Ps Ps_mut wsat sch2
  | bi_sch_forall A sch => ∀ (a: A),  bi_schema_pre n Ps Ps_mut wsat (sch a)
  | bi_sch_exist A sch => ∃ (a: A),  bi_schema_pre n Ps Ps_mut wsat (sch a)
  | bi_sch_sep sch1 sch2 => bi_schema_pre n Ps Ps_mut wsat sch1 ∗ bi_schema_pre n Ps Ps_mut wsat sch2
  | bi_sch_wand sch1 sch2 => bi_schema_pre n Ps Ps_mut wsat sch1 -∗ bi_schema_pre n Ps Ps_mut wsat sch2
  | bi_sch_persistently sch => <pers> bi_schema_pre n Ps Ps_mut wsat sch
  | bi_sch_later sch => ▷ bi_schema_pre n Ps Ps_mut wsat sch
  | bi_sch_bupd sch => |==> bi_schema_pre n Ps Ps_mut wsat sch
  | bi_sch_var_fixed i =>
    match (Ps !! i) with
    | None => emp
    | Some P => P
    end
  | bi_sch_var_mut i =>
    match (Ps_mut !! i) with
    | None => emp
    | Some P => P
    end
  | bi_sch_wsat => wsat
  | bi_sch_ownE E => ownE (E n)
  end%I.

Definition wsat_pre `{!invGS Σ} n bi_schema_interp :=
  (∃ I : gmap positive ((list (iProp Σ) * bi_schema) * list (iProp Σ)),
        (∃ γs, fmlist_idx inv_list_name n γs ∗
             own (invariant_name γs) (● (inv_cmra_fmap <$> I : gmap _ _))) ∗
        [∗ map] i ↦ Qs ∈ I, (bi_schema_interp (bi_later <$> Qs.1.1) (bi_later <$> Qs.2) Qs.1.2 ∗
                             ownI_mut n i (1/2)%Qp (list_to_vec Qs.2) ∗
                             ownD {[i]}) ∨
                            ownE {[i]})%I.

Fixpoint bi_schema_interp `{!invGS Σ} n (Ps Ps_mut: list (iProp Σ)) sch {struct n} :=
  match n with
  | O => bi_schema_pre O Ps Ps_mut True%I sch
  | S n' => bi_schema_pre (S n') Ps Ps_mut (wsat_pre n' (bi_schema_interp n') ∗ wsat n')%I sch
  end
  with
  wsat `{!invGS Σ} n :=
  match n with
    | S n =>
  (∃ I : gmap positive ((list (iProp Σ) * bi_schema) * list (iProp Σ)),
        (∃ γs, fmlist_idx inv_list_name n γs ∗
             own (invariant_name γs) (● (inv_cmra_fmap <$> I : gmap _ _))) ∗
        [∗ map] i ↦ Qs ∈ I, (bi_schema_interp n (bi_later <$> Qs.1.1) (bi_later <$> Qs.2) Qs.1.2 ∗
                             ownI_mut n i (1/2)%Qp (list_to_vec Qs.2) ∗
                             ownD {[i]}) ∨
                            ownE {[i]})
    ∗ wsat n
    | O => True
  end%I.

Section wsat.
Context `{!invGS Σ}.

Lemma ownI_alloc {n m} φ sch lvl (Ps: vec _ n) (Ps_mut: vec _ m):
  (∀ E : gset positive, ∃ i, i ∉ E ∧ φ i) →
  wsat (S lvl) ∗
  bi_schema_interp lvl (bi_later <$> (vec_to_list Ps)) (bi_later <$> (vec_to_list Ps_mut)) sch ==∗
  ∃ i, ⌜φ i⌝ ∗ wsat (S lvl) ∗ ownI lvl i sch Ps ∗ ownI_mut lvl i (1/2)%Qp Ps_mut.
Admitted.

End wsat.

Section schema_test_mut.
Context `{!invGS Σ}.
Definition bi_sch_bupd_factory (Q P: bi_schema) : bi_schema.
Admitted.

Definition ownI_full_bupd_factory lvl i q Q P :=
  (∃ n (Qs: vec _ n), ownI lvl i (bi_sch_bupd_factory (bi_sch_var_mut O) (bi_sch_var_fixed O)) (list_to_vec [P]) ∗
   ownI_mut lvl i q Qs ∗ ⌜ default True%I (vec_to_list Qs !! 0) = Q ⌝)%I.

Lemma ownI_bupd_factory_alloc lvl φ Q P :
  (∀ E : gset positive, ∃ i, i ∉ E ∧ φ i) →
  wsat (S lvl) ∗ (▷ Q ∗ □ (▷ Q ==∗ ▷ Q ∗ ▷ P))
       ==∗ ∃ i, ⌜φ i⌝ ∗ wsat (S lvl) ∗ ownI_full_bupd_factory lvl i (1/2)%Qp Q P.
Proof.
  iIntros (?) "(Hw&(HQ&#Hfactory))".
iMod (ownI_alloc with "[$Hw HQ]") as (i) "(?&?&?&?)"; eauto; last first.
  {
 iModIntro.
iExists i.
iFrame.
instantiate (1:= list_to_vec [Q]).
rewrite //=.
}
  repeat (rewrite ?bi_schema_interp_unfold //=).
