(* -*- mode: coq; coq-prog-args: ("-emacs" "-w" "-deprecated-native-compiler-option,-native-compiler-disabled" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/msl" "VST.msl" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/sepcomp" "VST.sepcomp" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/veric" "VST.veric" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/floyd" "VST.floyd" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/progs" "VST.progs" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/concurrency" "VST.concurrency" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/atomics" "VST.atomics" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/wand_demo" "wand_demo" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/sha" "sha" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/hmacfcf" "hmacfcf" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/tweetnacl20140427" "tweetnacl20140427" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/hmacdrbg" "hmacdrbg" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/aes" "aes" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/mailbox" "mailbox" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/lib" "compcert.lib" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/common" "compcert.common" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/x86_32" "compcert.x86_32" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/x86" "compcert.x86" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/cfrontend" "compcert.cfrontend" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/export" "compcert.export" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Flocq" "Flocq" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-top" "SeparationLogicFacts" "-native-compiler" "ondemand") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 2430 lines to 4 lines, then from 17 lines to 2017 lines, then from 2018 lines to 186 lines, then from 200 lines to 1181 lines, then from 1187 lines to 184 lines, then from 198 lines to 2668 lines, then from 2670 lines to 224 lines, then from 238 lines to 743 lines, then from 749 lines to 225 lines, then from 239 lines to 755 lines, then from 761 lines to 234 lines, then from 248 lines to 1669 lines, then from 1671 lines to 330 lines, then from 344 lines to 1282 lines, then from 1287 lines to 340 lines, then from 354 lines to 929 lines, then from 935 lines to 341 lines, then from 355 lines to 2252 lines, then from 2232 lines to 351 lines, then from 365 lines to 800 lines, then from 802 lines to 364 lines, then from 378 lines to 853 lines, then from 858 lines to 435 lines, then from 449 lines to 599 lines, then from 603 lines to 459 lines, then from 473 lines to 796 lines, then from 802 lines to 467 lines, then from 481 lines to 1447 lines, then from 1453 lines to 499 lines, then from 513 lines to 1949 lines, then from 1953 lines to 594 lines, then from 608 lines to 887 lines, then from 892 lines to 800 lines *)
(* coqc version 8.16+alpha compiled with OCaml 4.13.0
   coqtop version runner-j1aldqxs-project-6138686-concurrent-0:/builds/coq/coq/_build/default,(HEAD detached at 3e1f200) (3e1f2002ec2d419c1713214c705fbfa902e28604)
   Modules that could not be inlined: VST.floyd.jmeq_lemmas
   Expected coqc runtime on this file: 1.246 sec *)
Declare ML Module "ltac_plugin".
Module Export AdmitTactic.
Module Import LocalFalse.
Inductive False : Prop := .
End LocalFalse.
Axiom proof_admitted : False.
Global Set Default Proof Mode "Classic".
Tactic Notation "admit" := abstract case proof_admitted.
End AdmitTactic.
Require VST.msl.msl_standard.
Import VST.msl.msl_standard.

Require VST.veric.shares.
Import VST.veric.shares.

Require VST.veric.compspecs.
Import VST.veric.compspecs.

Module Type ADR_VAL.
Parameter address : Type.

Parameter kind: Type.
End ADR_VAL.

Inductive TypeTree: Type :=
  | ConstType: Type -> TypeTree
  | CompspecsType: TypeTree
  | Mpred: TypeTree
  | DependentType: nat -> TypeTree
  | ProdType: TypeTree -> TypeTree -> TypeTree
  | ArrowType: TypeTree -> TypeTree -> TypeTree
  | SigType: forall (I : Type), (I -> TypeTree) -> TypeTree
  | PiType: forall (I : Type), (I -> TypeTree) -> TypeTree
  | ListType: TypeTree -> TypeTree.
Definition dependent_type_functor_rec (ts: list Type): TypeTree -> functor.
Admitted.

Module Type STRAT_MODEL.
  Declare Module AV : ADR_VAL.
Definition f_pre_rmap : functor.
Admitted.
Instance Join_pre_rmap (A: Type) : Join (f_pre_rmap A).
Admitted.
  Declare Instance Sep_pre_rmap: forall (A: Type), Sep_alg (f_pre_rmap A).
  Parameter paf_pre_rmap : @pafunctor f_pre_rmap Join_pre_rmap.

End STRAT_MODEL.

Module StratModel (AV' : ADR_VAL) : STRAT_MODEL with Module AV:=AV'.
  Module AV := AV'.
  Import AV.
Definition preds: functor.
Admitted.

  Inductive res (PRED : Type) : Type :=
    | NO':  forall sh: Share.t, ~(readable_share sh) -> res PRED
    | YES': forall sh: Share.t, readable_share sh -> kind -> preds PRED -> res PRED
    | PURE': kind -> preds PRED -> res PRED.
Definition res_fmap (A B:Type) (f:A->B) (g:B->A)(x:res A) : res B.
Admitted.

  Lemma ff_res : functorFacts res res_fmap.
Admitted.
Definition f_res : functor.
exact (Functor ff_res).
Defined.
Definition ghost (PRED : Type) : Type.
Admitted.
Definition ghost_fmap (A B:Type) (f:A->B) (g:B->A)(x:ghost A) : ghost B.
Admitted.

  Lemma ff_ghost : functorFacts ghost ghost_fmap.
Admitted.
Definition f_ghost : functor.
exact (Functor ff_ghost).
Defined.

  Definition pre_rmap (A:Type) := ((address -> res A) * ghost A)%type.
Definition f_pre_rmap : functor.
exact (fpair (ffunc (fconst address) f_res) f_ghost).
Defined.
Instance Join_pre_rmap (A: Type) : Join (pre_rmap A).
Admitted.
Definition paf_pre_rmap : @pafunctor f_pre_rmap Join_pre_rmap.
Admitted.
Definition Sep_pre_rmap (A: Type): Sep_alg (pre_rmap A).
Admitted.

End StratModel.

Module Type RMAPS.
  Declare Module AV:ADR_VAL.

  Parameter rmap : Type.
  Axiom ag_rmap: ageable rmap.
 Existing Instance ag_rmap.

End RMAPS.

Module Rmaps (AV':ADR_VAL): RMAPS with Module AV:=AV'.
  Module Export AV:=AV'.

  Module SM := StratModel(AV).
  Import SM.

  Module Export TyF.

    Definition F := f_pre_rmap.
  End TyF.

  Module TyFSA <: KNOT_FULL_SA_INPUT with Module KI:=TyF.
    Module KI := TyF.
Instance Join_F: forall A, Join (F A).
exact (_).
Defined.
Definition Perm_F : forall A, Perm_alg (F A).
Admitted.
    Definition Sep_F := Sep_pre_rmap.
    Definition paf_F := paf_pre_rmap.
  End TyFSA.

  Module K := Knot_MixVariantHeredProp(TyF).

  Definition rmap := K.knot.
Instance ag_rmap : ageable rmap.
Admitted.

End Rmaps.
Require VST.veric.Clight_base.
Import VST.veric.Clight_base.

Require Coq.Logic.ClassicalFacts.
Require Coq.Logic.FunctionalExtensionality.
Require VST.msl.Axioms.
Require Coq.Logic.EqdepFacts.
Require VST.msl.Extensionality.

Module Export VST_DOT_msl_DOT_seplog_WRAPPED.
Module Export seplog.
Import VST.msl.Extensionality.

Class NatDed (A: Type) := mkNatDed {
  andp: A -> A -> A;
  orp: A -> A -> A;
  exp: forall {T:Type}, (T -> A) -> A;
  allp: forall {T:Type}, (T -> A) -> A;
  imp: A -> A -> A;
  prop: Prop -> A;
  derives: A -> A -> Prop;
  pred_ext: forall P Q, derives P Q -> derives Q P -> P=Q;
  derives_refl: forall P, derives P P;
  derives_trans: forall P Q R, derives P Q -> derives Q R -> derives P R;
  TT := prop True;
  FF := prop False;
  andp_right:  forall X P Q:A, derives X P -> derives X Q -> derives X (andp P Q);
  andp_left1:  forall P Q R:A, derives P R -> derives (andp P Q) R;
  andp_left2:  forall P Q R:A, derives Q R -> derives (andp P Q) R;
  orp_left: forall P Q R, derives P R -> derives Q R -> derives (orp P Q) R;
  orp_right1: forall P Q R, derives P Q -> derives P (orp Q R);
  orp_right2: forall P Q R, derives P R -> derives P (orp Q R);
  exp_right: forall {B: Type} (x:B) (P: A) (Q: B -> A),
                        derives P (Q x) -> derives P (exp Q);
  exp_left: forall {B: Type} (P: B -> A) (Q: A),
                      (forall x, derives (P x) Q) -> derives (exp P) Q;
  allp_left: forall {B}(P: B -> A) x Q, derives (P x) Q -> derives (allp P) Q;
  allp_right: forall {B}(P: A) (Q: B -> A),  (forall v, derives P (Q v)) -> derives P (allp Q);
  imp_andp_adjoint: forall P Q R, derives (andp P Q) R <-> derives P (imp Q R);
  prop_left: forall (P: Prop) Q, (P -> derives TT Q) -> derives (prop P) Q;
  prop_right: forall (P: Prop) Q, P -> derives Q (prop P);
  prop_imp_prop_left: forall (P Q: Prop), derives (imp (prop P) (prop Q)) (prop (P -> Q));
  allp_prop_left: forall {B: Type} (P: B -> Prop), derives (allp (fun b => prop (P b))) (prop (forall b, P b))
 
}.

Program Instance LiftNatDed (A B: Type) {ND: NatDed B} : NatDed (A -> B) :=
 mkNatDed (A -> B)
      (fun P Q x => andp (P x) (Q x))
      (fun P Q x => orp (P x) (Q x))
      (fun T (F: T -> A -> B) (a: A) => exp (fun x => F x a))
      (fun T (F: T -> A -> B) (a: A) => allp (fun x => F x a))
      (fun P Q x => imp (P x) (Q x))
      (fun P x => prop P)
      (fun P Q => forall x, derives (P x) (Q x))
     _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _.
Admit Obligations.
Admit Obligations.
Admit Obligations.
Admit Obligations.
Admit Obligations.
Admit Obligations.
Admit Obligations.
Admit Obligations.
Admit Obligations.
Admit Obligations.
Admit Obligations.
Admit Obligations.
Admit Obligations.
Admit Obligations.
Admit Obligations.
Admit Obligations.
Admit Obligations.
Admit Obligations.

Declare Scope logic.
Delimit Scope logic with logic.
Local Open Scope logic.
Declare Scope logic_derives.
Notation "P '|--' Q" := (derives P%logic Q%logic) (at level 80, no associativity) : logic_derives.
Open Scope logic_derives.
Notation "'EX' x .. y , P " :=
  (exp (fun x => .. (exp (fun y => P%logic)) ..)) (at level 65, x binder, y binder, right associativity) : logic.
Notation "'ALL' x .. y , P " :=
  (allp (fun x => .. (allp (fun y => P%logic)) ..)) (at level 65, x binder, y binder, right associativity) : logic.
Infix "||" := orp (at level 50, left associativity) : logic.
Infix "&&" := andp (at level 40, left associativity) : logic.
Notation "P '-->' Q" := (imp P Q) (at level 55, right associativity) : logic.
Notation "P '<-->' Q" := (andp (imp P Q) (imp Q P)) (at level 57, no associativity) : logic.
Notation "'!!' e" := (prop e) (at level 15) : logic.

Class SepLog (A: Type) {ND: NatDed A} := mkSepLog {
  emp: A;
  sepcon: A -> A -> A;
  wand: A -> A -> A;
  ewand: A -> A -> A;
  sepcon_assoc: forall P Q R, sepcon (sepcon P Q) R = sepcon P (sepcon Q R);
  sepcon_comm:  forall P Q, sepcon P Q = sepcon Q P;
  wand_sepcon_adjoint: forall (P Q R: A),  (sepcon P Q |-- R) <-> (P |-- wand Q R);
  sepcon_andp_prop: forall P Q R, sepcon P (!!Q && R) = !!Q && (sepcon P R);
  sepcon_derives: forall P P' Q Q' : A, (P |-- P') -> (Q |-- Q') -> sepcon P Q |-- sepcon P' Q';
  ewand_sepcon: forall (P Q R : A),  ewand (sepcon P Q) R = ewand P (ewand Q R);
  ewand_TT_sepcon: forall (P Q R: A),
                         andp (sepcon P Q) (ewand R TT) |--
                               sepcon (andp P (ewand R TT)) (andp Q (ewand R TT));
  exclude_elsewhere: forall P Q: A, sepcon P Q |-- sepcon (andp P (ewand Q TT)) Q;
  ewand_conflict: forall P Q R, (sepcon P Q |-- FF) -> andp P (ewand Q R) |-- FF
}.

Notation "P '*' Q" := (sepcon P Q) : logic.
Notation "P '-*' Q" := (wand P Q) (at level 60, right associativity) : logic.

Instance LiftSepLog (A B: Type) {NB: NatDed B}{SB: SepLog B} : SepLog (A -> B).
Admitted.

Class ClassicalSep  (A: Type) {ND: NatDed A}{SL: SepLog A} := mkCS {
   sepcon_emp: forall P, P * emp = P
}.

Instance LiftClassicalSep (A B: Type)  {NB: NatDed B}{SB: SepLog B}{CB: ClassicalSep B} :
        ClassicalSep (A -> B).
Admitted.

Definition  extensible {A}{ND: NatDed A}{SL: SepLog A}(P:A) := sepcon P TT |-- P.

Class IntuitionisticSep (A: Type) {ND: NatDed A}{SL: SepLog A} := mkIS {
   all_extensible: forall P, extensible P
}.

Instance LiftIntuitionisticSep (A B: Type)  {NB: NatDed B}{SB: SepLog B}{IB: IntuitionisticSep B} :
        IntuitionisticSep (A -> B).
Admitted.

Class Indir (A: Type) {ND: NatDed A} := mkIndir {
  later: A -> A;
  now_later: forall P: A, P |-- later P;
  later_K: forall P Q, later (P --> Q) |-- later P --> later Q;
  later_allp: forall T (F: T -> A),  later (allp F) = ALL x:T, later (F x);
  later_exp: forall T (F: T-> A), EX x:T, later (F x) |-- later (exp F);
  later_exp': forall T (any:T) F, later (exp F) = EX x:T, later (F x);
  later_exp'': forall T F, later (exp F) |-- (EX x:T, later (F x)) || later FF;
  later_imp: forall P Q,  later(P --> Q) = later P --> later Q;
  later_prop: forall PP: Prop, later (!! PP) |-- !! PP || later FF;
  loeb: forall P,   (later P |-- P) ->  TT |-- P
}.

Notation "'|>' e" := (later e) (at level 20, right associativity): logic.

Instance LiftIndir (A: Type) (B: Type)  {NB: NatDed B}{IXB: Indir B} :
         @Indir (A -> B) (LiftNatDed A B).
Admitted.

Class SepIndir (A: Type) {NA: NatDed A}{SA: SepLog A}{IA: Indir A} := mkSepIndir {
  later_sepcon: forall P Q, |> (P * Q) = |>P * |>Q;
  later_wand: forall P Q, |> (P -* Q) = |>P -* |>Q;
  later_ewand: forall P Q, |> (ewand P Q) = ewand (|>P) (|>Q)
}.

Instance LiftSepIndir  (A: Type) (B: Type)  {NB: NatDed B} {SB: SepLog B}{IB: Indir B}{SIB: SepIndir B} :
     @SepIndir (A -> B) (LiftNatDed A B) (LiftSepLog A B) (LiftIndir A B).
Admitted.

Class CorableSepLog (A: Type) {ND: NatDed A}{SL: SepLog A}:= mkCorableSepLog {
  corable: A -> Prop;
  corable_prop: forall P, corable (!! P);
  corable_andp: forall P Q, corable P -> corable Q -> corable (P && Q);
  corable_orp: forall P Q, corable P -> corable Q -> corable (P || Q);
  corable_imp: forall P Q, corable P -> corable Q -> corable (P --> Q);
  corable_allp: forall {B: Type} (P:  B -> A), (forall b, corable (P b)) -> corable (allp P);
  corable_exp: forall {B: Type} (P:  B -> A), (forall b, corable (P b)) -> corable (exp P);
  corable_sepcon: forall P Q, corable P -> corable Q -> corable (P * Q);
  corable_wand: forall P Q, corable P -> corable Q -> corable (P -* Q);
  corable_andp_sepcon1: forall P Q R, corable P ->  (P && Q) * R = P && (Q * R)
}.

Instance LiftCorableSepLog (A: Type) (B: Type) {NB: NatDed B} {SB: SepLog B} {CSL: CorableSepLog B} : @CorableSepLog (A -> B) (LiftNatDed A B) (LiftSepLog A B).
Admitted.

Class CorableIndir (A: Type) {ND: NatDed A}{SL: SepLog A}{CSL: CorableSepLog A}{ID: Indir A} :=
  corable_later: forall P, corable P -> corable (|> P).

Instance LiftCorableIndir (A: Type) (B: Type) {NB: NatDed B} {SB: SepLog B} {CSL: CorableSepLog B} {ID: Indir B} {CI: CorableIndir B}: @CorableIndir (A -> B) (LiftNatDed A B) (LiftSepLog A B) (LiftCorableSepLog A B) (LiftIndir A B).
Admitted.

Lemma orp_comm: forall {A: Type} `{NatDed A} (P Q: A), P || Q = Q || P.
Admitted.

End seplog.

End VST_DOT_msl_DOT_seplog_WRAPPED.
Module Export VST_DOT_msl_DOT_seplog.
Module Export VST.
Module Export msl.
Module Export seplog.
Include VST_DOT_msl_DOT_seplog_WRAPPED.seplog.
End seplog.

End msl.

End VST.

End VST_DOT_msl_DOT_seplog.
Export VST.msl.seplog.

Definition typesig := (list type * type)%type.

Inductive kind : Type := VAL : memval -> kind
                                   | LK : forall n i : Z, kind
                                   | FUN:  typesig -> calling_convention -> kind.

Module CompCert_AV <: ADR_VAL.

Definition address := address.
Definition kind := kind.

End CompCert_AV.

Module R := Rmaps (CompCert_AV).
Export R.
Definition force_val (v: option val) : val.
Admitted.

Definition force_val1 (f: val -> option val) (v: val) := force_val (f v).
Definition force_val2 (f: val -> val -> option val) (v1 v2: val) := force_val (f v1 v2).

Definition is_long (v: val) :=
 match v with Vlong i => True | _ => False end.

Definition isptr v :=
   match v with | Vptr _ _ => True | _ => False end.

Structure Lift := mkLift {
         lift_S: Type;
         lift_T: Type;
         lift_prod : Type;
         lift_last: Type;
         lifted:> Type;
         lift_curry: lift_T -> lift_prod -> lift_last;
         lift_uncurry_open: ((lift_S -> lift_prod) -> (lift_S -> lift_last)) -> lifted
}.

Definition Tend (S: Type) (A: Type) :=
    mkLift S A unit A
          (S -> A)
          (fun f _ => f)
          (fun f => f (fun _: S => tt)).
Canonical Structure Tarrow (A: Type) (H: Lift) :=
    mkLift (lift_S H)
      (A -> lift_T H)
      (prod A (lift_prod H))
      (lift_last H)
      ((lift_S H -> A) -> lifted H)
      (fun f x => match x with (x1,x2) => lift_curry H (f x1) x2 end)
      (fun f x => lift_uncurry_open H (fun y: lift_S H -> lift_prod H => f (fun z => (x z, y z)))).

Set Implicit Arguments.
Definition liftx {H: Lift} (f: lift_T H) : lifted H.
Admitted.
Notation "'`' x" := (liftx x) (at level 10, x at next level).

Notation "'`(' x ')'" := (liftx (x : _)).
Module Export Map.
Section map.
Variables (B : Type).

Definition t := positive -> option B.
Definition get (h: t) (a:positive) : option B.
exact (h a).
Defined.
Definition set (a:positive) (v: B) (h: t) : t.
exact (fun i => if ident_eq i a then Some v else h i).
Defined.

Lemma gso h x y v : x<>y -> get (set x v h) y = get h y.
unfold get, set; intros; if_tac; intuition.
Qed.

End map.

Section FUNSPEC.

Definition genviron := Map.t block.

Definition venviron := Map.t (block * type).

Definition tenviron := Map.t val.

Inductive environ : Type :=
 mkEnviron: forall (ge: genviron) (ve: venviron) (te: tenviron), environ.
Definition te_of (rho: environ) : tenviron.
Admitted.

Definition mpred := pred rmap.
Definition AssertTT (A: TypeTree): TypeTree.
Admitted.
Definition ArgsTT (A: TypeTree): TypeTree.
Admitted.
Definition super_non_expansive {A: TypeTree}
  (P: forall ts, dependent_type_functor_rec ts (AssertTT A) mpred): Prop.
Admitted.
Definition args_super_non_expansive {A: TypeTree}
  (P: forall ts, dependent_type_functor_rec ts (ArgsTT A) mpred): Prop.
Admitted.

Inductive funspec :=
   mk_funspec: typesig -> calling_convention -> forall (A: TypeTree)
     (P: forall ts, dependent_type_functor_rec ts (ArgsTT A) mpred)
     (Q: forall ts, dependent_type_functor_rec ts (AssertTT A) mpred)
     (P_ne: args_super_non_expansive P) (Q_ne: super_non_expansive Q),
     funspec.

End FUNSPEC.

Arguments sizeof {env} !t / .
Arguments alignof {env} !t / .

Definition eval_id (id: ident) (rho: environ) := force_val (Map.get (te_of rho) id).
Canonical Structure LiftEnviron := Tend environ.
Import compcert.lib.Maps.

Definition is_int (sz: intsize) (sg: signedness) (v: val) :=
  match v with
  | Vint i =>
    match sz, sg with
    | I8, Signed => Byte.min_signed <= Int.signed i <= Byte.max_signed
    | I8, Unsigned => Int.unsigned i <= Byte.max_unsigned
    | I16, Signed => -two_p (16-1) <= Int.signed i <= two_p (16-1) -1
    | I16, Unsigned => Int.unsigned i <= two_p 16 - 1
    | I32, _ => True
    | IBool, _ => i = Int.zero \/ i = Int.one
    end
  | _ => False
  end.
Definition tc_val (ty: type) : val -> Prop.
Admitted.

Inductive Annotation :=
  WeakAnnotation : (environ -> mpred) -> Annotation
| StrongAnnotation : (environ -> mpred) -> Annotation.

Inductive tycontext : Type :=
  mk_tycontext : forall (tyc_temps: PTree.t type)
                        (tyc_vars: PTree.t type)
                        (tyc_ret: type)
                        (tyc_globty: PTree.t type)
                        (tyc_globsp: PTree.t funspec)
                        (tyc_annot: PTree.t Annotation),
                             tycontext.

Module Export Clight_Cop2.
Definition sem_cast (t1 t2: type): val -> option val.
Admitted.
Definition sem_unary_operation
            (op: Cop.unary_operation) (ty: type) (v: val): option val.
Admitted.
Definition sem_binary_operation'
    {CS: compspecs} (op: Cop.binary_operation)
    (t1:type) (t2: type) : val -> val -> option val.
Admitted.

Definition eval_unop (op: Cop.unary_operation) (t1 : type) :=
       force_val1 (Clight_Cop2.sem_unary_operation op t1).

Definition eval_binop {CS:compspecs} (op: Cop.binary_operation) (t1 t2 : type) :=
       force_val2 (Clight_Cop2.sem_binary_operation'  op t1 t2).

Definition eval_cast (t1 t2 : type) :=
  force_val1 (sem_cast t1 t2).
Definition eval_field {CS: compspecs} (ty: type) (fld: ident) : val -> val.
Admitted.
Definition eval_var (id:ident) (ty: type) (rho: environ) : val.
Admitted.

Fixpoint eval_expr {CS: compspecs} (e: expr) : environ -> val :=
 match e with
 | Econst_int i ty => `(Vint i)
 | Econst_long i ty => `(Vlong i)
 | Econst_float f ty => `(Vfloat f)
 | Econst_single f ty => `(Vsingle f)
 | Etempvar id ty => eval_id id
 | Eaddrof a ty => eval_lvalue a
 | Eunop op a ty =>  `(eval_unop op (typeof a)) (eval_expr a)
 | Ebinop op a1 a2 ty =>
                  `(eval_binop op (typeof a1) (typeof a2)) (eval_expr a1) (eval_expr a2)
 | Ecast a ty => `(eval_cast (typeof a) ty) (eval_expr a)
 | Evar id ty => eval_var id ty
 | Ederef a ty => eval_expr a
 | Efield a i ty => `(eval_field (typeof a) i) (eval_lvalue a)
 | Esizeof t ty => `(if complete_type cenv_cs t
                             then Vptrofs (Ptrofs.repr (sizeof t)) else Vundef)
 | Ealignof t ty => `(if complete_type cenv_cs t
                             then Vptrofs (Ptrofs.repr (alignof t)) else Vundef)
 end

 with eval_lvalue {CS: compspecs} (e: expr) : environ -> val :=
 match e with
 | Evar id ty => eval_var id ty
 | Ederef a ty => eval_expr a
 | Efield a i ty => `(eval_field (typeof a) i) (eval_lvalue a)
 | _  => `Vundef
 end.
Definition eval_expropt {CS: compspecs} (e: option expr) : environ -> option val.
exact (match e with Some e' => `(@Some val) (eval_expr e')  | None => `None end).
Defined.

Inductive tc_error :=
| op_result_type : expr -> tc_error
| arg_type : expr -> tc_error
| pp_compare_size_0 : type -> tc_error
| pp_compare_size_exceed : type -> tc_error
| invalid_cast : type -> type -> tc_error
| invalid_cast_result : type -> type -> tc_error
| invalid_expression : expr -> tc_error
| var_not_in_tycontext : tycontext -> positive  -> tc_error
| mismatch_context_type : type -> type -> tc_error
| deref_byvalue : type -> tc_error
| volatile_load : type -> tc_error
| invalid_field_access : expr -> tc_error
| invalid_composite_name: ident -> tc_error
| invalid_struct_field : ident   -> ident   -> tc_error
| invalid_lvalue : expr -> tc_error
| wrong_signature : tc_error
| int_or_ptr_type_error : tc_error
| miscellaneous_typecheck_error : tc_error.

Inductive tc_assert :=
| tc_FF: tc_error -> tc_assert
| tc_TT : tc_assert
| tc_andp': tc_assert -> tc_assert -> tc_assert
| tc_orp' : tc_assert -> tc_assert -> tc_assert
| tc_nonzero': expr -> tc_assert
| tc_iszero': expr -> tc_assert
| tc_isptr: expr -> tc_assert
| tc_isint: expr -> tc_assert
| tc_islong: expr -> tc_assert
| tc_test_eq': expr -> expr -> tc_assert
| tc_test_order': expr -> expr -> tc_assert
| tc_ilt': expr -> int -> tc_assert
| tc_llt': expr -> int64 -> tc_assert
| tc_Zle: expr -> Z -> tc_assert
| tc_Zge: expr -> Z -> tc_assert
| tc_samebase: expr -> expr -> tc_assert
| tc_nodivover': expr -> expr -> tc_assert
| tc_initialized: PTree.elt -> type -> tc_assert
| tc_nosignedover: (Z->Z->Z) -> expr -> expr -> tc_assert.
Definition valid_pointer (p: val) : mpred.
Admitted.
Definition weak_valid_pointer (p: val) : mpred.
Admitted.

Lemma nth_error_in_bounds: forall {A} (l: list A) i, (O <= i < length l)%nat
  -> exists x, nth_error l i = value x.
Proof.
intros until i; intros H.
revert i l H.
induction i; destruct l; intros; simpl in *;
  try solve [eauto|lia].
apply IHi; lia.
Qed.

Class Inhabitant (A: Type) := default : A.
Instance Inhabitant_pair {T1 T2 : Type} {x1: Inhabitant T1} {x2: Inhabitant T2} : Inhabitant (T1*T2)%type.
exact ((x1,x2)).
Defined.

Lemma nth_map':
  forall {A B} (f: A -> B) d d' i al,
  (i < length al)%nat ->
   nth i (map f al) d = f (nth i al d').
Admitted.

Definition Znth {X}{d: Inhabitant X} n (xs: list X) :=
  if (Z_lt_dec n 0) then default else nth (Z.to_nat n) xs d.

Lemma Znth_map:
  forall {A:Type} {da: Inhabitant A}{B:Type}{db: Inhabitant B} i (f: A -> B) (al: list A),
  0 <= i < Zlength al ->
  Znth i (map f al)  = f (Znth i al).
Proof.
unfold Znth.
intros.
rewrite if_false by lia.
rewrite if_false by lia.
rewrite nth_map' with (d' := da); auto.
apply Nat2Z.inj_lt.
rewrite Z2Nat.id by lia.
change (Inhabitant A) with A.
rewrite <- Zlength_correct.
lia.
Qed.

Lemma Znth_combine : forall {A B} {a: Inhabitant A} {b: Inhabitant B} i (l1: list A) (l2: list B),
   Zlength l1 = Zlength l2 ->
  Znth i (combine l1 l2) = (Znth i l1, Znth i l2).
Proof.
  intros; unfold Znth.
  destruct (Z_lt_dec i 0); auto.
  apply combine_nth.
  rewrite !Zlength_correct in *; lia.
Qed.
Instance Nveric: NatDed mpred.
Admitted.

Definition denote_tc_iszero v : mpred :=
         match v with
         | Vint i => prop (is_true (Int.eq i Int.zero))
         | Vlong i => prop (is_true (Int64.eq i Int64.zero))
         | _ => FF
         end.

Definition denote_tc_nonzero v : mpred :=
         match v with
         | Vint i => prop (i <> Int.zero)
         | Vlong i =>prop (i <> Int64.zero)
         | _ => FF end.

Definition denote_tc_igt i v : mpred :=
     match v with
     | Vint i1 => prop (Int.unsigned i1 < Int.unsigned i)
     | _ => FF
     end.

Definition denote_tc_lgt l v : mpred :=
     match v with
     | Vlong l1 => prop (Int64.unsigned l1 < Int64.unsigned l)
     | _ => FF
     end.
Definition Zoffloat (f:float): option Z.
Admitted.
Definition Zofsingle (f: float32): option Z.
Admitted.

Definition denote_tc_Zge z v : mpred :=
          match v with
                     | Vfloat f => match Zoffloat f with
                                    | Some n => prop (z >= n)
                                    | None => FF
                                   end
                     | Vsingle f => match Zofsingle f with
                                    | Some n => prop (z >= n)
                                    | None => FF
                                   end
                     | _ => FF
                  end.

Definition denote_tc_Zle z v : mpred :=
          match v with
                     | Vfloat f => match Zoffloat f with
                                    | Some n => prop (z <= n)
                                    | None => FF
                                   end
                     | Vsingle f => match Zofsingle f with
                                    | Some n => prop (z <= n)
                                    | None => FF
                                   end
                     | _ => FF
                  end.

Definition sameblock v1 v2 : bool :=
         match v1, v2 with
          | Vptr b1 _, Vptr b2 _ => peq b1 b2
          | _, _ => false
         end.

Definition denote_tc_samebase v1 v2 : mpred :=
       prop (is_true (sameblock v1 v2)).

Definition denote_tc_nodivover v1 v2 : mpred :=
match v1, v2 with
          | Vint n1, Vint n2 => prop (~(n1 = Int.repr Int.min_signed /\ n2 = Int.mone))
          | Vlong n1, Vlong n2 => prop (~(n1 = Int64.repr Int64.min_signed /\ n2 = Int64.mone))
          | Vint n1, Vlong n2 => TT
          | Vlong n1, Vint n2 => prop (~ (n1 = Int64.repr Int64.min_signed  /\ n2 = Int.mone))
          | _ , _ => FF
        end.

Definition denote_tc_nosignedover (op: Z->Z->Z) (s: signedness) v1 v2 : mpred :=
 match v1,v2 with
 | Vint n1, Vint n2 =>
   prop (Int.min_signed <= op (Int.signed n1) (Int.signed n2) <= Int.max_signed)
 | Vlong n1, Vlong n2 =>
   prop (Int64.min_signed <= op (Int64.signed n1) (Int64.signed n2) <= Int64.max_signed)
 | Vint n1, Vlong n2 =>
   prop (Int64.min_signed <= op ((if s then Int.signed else Int.unsigned) n1) (Int64.signed n2) <= Int64.max_signed)
 | Vlong n1, Vint n2 =>
   prop (Int64.min_signed <= op (Int64.signed n1) ((if s then Int.signed else Int.unsigned)  n2) <= Int64.max_signed)
 | _, _ => FF
 end.

Definition denote_tc_initialized id ty rho : mpred :=
    prop (exists v, Map.get (te_of rho) id = Some v
               /\ tc_val ty v).

Definition denote_tc_isptr v : mpred :=
  prop (isptr v).

Definition denote_tc_isint v : mpred :=
  prop (is_int I32 Signed v).

Definition denote_tc_islong v : mpred :=
  prop (is_long v).

Definition test_eq_ptrs v1 v2 : mpred :=
  if sameblock v1 v2
  then (andp (weak_valid_pointer v1) (weak_valid_pointer v2))
  else (andp (valid_pointer v1) (valid_pointer v2)).

Definition test_order_ptrs v1 v2 : mpred :=
  if sameblock v1 v2
  then (andp (weak_valid_pointer v1) (weak_valid_pointer v2))
  else FF.

Definition denote_tc_test_eq v1 v2 : mpred :=
 match v1, v2 with
 | Vint i, Vint j =>
     if Archi.ptr64 then FF else andp (prop (i = Int.zero)) (prop (j = Int.zero))
 | Vlong i, Vlong j =>
     if Archi.ptr64 then andp (prop (i = Int64.zero)) (prop (j = Int64.zero)) else FF
 | Vint i, Vptr _ _ =>
      if Archi.ptr64 then FF else andp (prop (i = Int.zero)) (weak_valid_pointer v2)
 | Vlong i, Vptr _ _ =>
      if Archi.ptr64 then andp (prop (i = Int64.zero)) (weak_valid_pointer v2) else FF
 | Vptr _ _, Vint i =>
      if Archi.ptr64 then FF else andp (prop (i = Int.zero)) (weak_valid_pointer v1)
 | Vptr _ _, Vlong i =>
      if Archi.ptr64 then andp (prop (i = Int64.zero)) (weak_valid_pointer v1) else FF
 | Vptr _ _, Vptr _ _ =>
      test_eq_ptrs v1 v2
 | _, _ => FF
 end.

Definition denote_tc_test_order v1 v2 : mpred :=
 match v1, v2 with
 | Vint i, Vint j => if Archi.ptr64 then FF else andp (prop (i = Int.zero)) (prop (j = Int.zero))
 | Vlong i, Vlong j => if Archi.ptr64 then andp (prop (i = Int64.zero)) (prop (j = Int64.zero)) else FF
 | Vptr _ _, Vptr _ _ =>
      test_order_ptrs v1 v2
 | _, _ => FF
 end.
Definition typecheck_error (e: tc_error) : Prop.
Admitted.

Fixpoint denote_tc_assert {CS: compspecs} (a: tc_assert) : environ -> mpred :=
  match a with
  | tc_FF msg => `(prop (typecheck_error msg))
  | tc_TT => TT
  | tc_andp' b c => fun rho => andp (denote_tc_assert b rho) (denote_tc_assert c rho)
  | tc_orp' b c => `orp (denote_tc_assert b) (denote_tc_assert c)
  | tc_nonzero' e => `denote_tc_nonzero (eval_expr e)
  | tc_isptr e => `denote_tc_isptr (eval_expr e)
  | tc_isint e => `denote_tc_isint (eval_expr e)
  | tc_islong e => `denote_tc_islong (eval_expr e)
  | tc_test_eq' e1 e2 => `denote_tc_test_eq (eval_expr e1) (eval_expr e2)
  | tc_test_order' e1 e2 => `denote_tc_test_order (eval_expr e1) (eval_expr e2)
  | tc_ilt' e i => `(denote_tc_igt i) (eval_expr e)
  | tc_llt' e i => `(denote_tc_lgt i) (eval_expr e)
  | tc_Zle e z => `(denote_tc_Zge z) (eval_expr e)
  | tc_Zge e z => `(denote_tc_Zle z) (eval_expr e)
  | tc_samebase e1 e2 => `denote_tc_samebase (eval_expr e1) (eval_expr e2)
  | tc_nodivover' v1 v2 => `denote_tc_nodivover (eval_expr v1) (eval_expr v2)
  | tc_initialized id ty => denote_tc_initialized id ty
  | tc_iszero' e => `denote_tc_iszero (eval_expr e)
  | tc_nosignedover op e1 e2 =>
     match typeof e1, typeof e2 with
     | Tlong _ _, Tint _ Unsigned _ => `(denote_tc_nosignedover op Unsigned) (eval_expr e1) (eval_expr e2)
     | Tint _ Unsigned _, Tlong _ _ => `(denote_tc_nosignedover op Unsigned) (eval_expr e1) (eval_expr e2)
     | _, _ =>  `(denote_tc_nosignedover op Signed) (eval_expr e1) (eval_expr e2)
     end
 end.
Require VST.floyd.jmeq_lemmas.
