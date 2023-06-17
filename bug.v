
(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "-deprecated-native-compiler-option" "-native-compiler" "no" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/metacoq/utils/theories" "MetaCoq.Utils" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/metacoq/common/theories" "MetaCoq.Common" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/metacoq/pcuic/theories" "MetaCoq.PCUIC" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Equations" "Equations" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-top" "Top.bug_01") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 2038 lines to 90 lines, then from 103 lines to 2399 lines, then from 2401 lines to 305 lines, then from 318 lines to 2211 lines, then from 2215 lines to 322 lines, then from 335 lines to 615 lines, then from 620 lines to 337 lines, then from 350 lines to 939 lines, then from 942 lines to 384 lines, then from 397 lines to 1614 lines, then from 1613 lines to 397 lines, then from 410 lines to 822 lines, then from 827 lines to 400 lines, then from 413 lines to 1872 lines, then from 1873 lines to 663 lines, then from 676 lines to 933 lines, then from 938 lines to 670 lines, then from 683 lines to 2715 lines, then from 2716 lines to 1827 lines, then from 1786 lines to 677 lines, then from 690 lines to 1815 lines, then from 1816 lines to 761 lines, then from 774 lines to 3583 lines, then from 3559 lines to 964 lines, then from 977 lines to 1854 lines, then from 1856 lines to 1562 lines *)
(* coqc version 8.18+alpha compiled with OCaml 4.09.0
   coqtop version runner-vxtc-u6t-project-6138686-concurrent-0:/builds/coq/coq/_build/default,(HEAD detached at ea07289) (ea07289c2f91dc651a9c72195bde8fa5c3b41ad8)
   Expected coqc runtime on this file: 2.256 sec *)
Require Coq.Init.Ltac.
Require Coq.Numbers.Cyclic.Int63.Uint63.
Require Coq.Floats.PrimFloat.
Require Coq.Floats.SpecFloat.
Require Coq.Floats.FloatOps.
Require Coq.ZArith.ZArith.
Require Coq.Numbers.HexadecimalString.
Require Coq.Strings.String.
Require Coq.ssr.ssrbool.
Require Coq.ssr.ssreflect.
Require Coq.NArith.NArith.
Require Coq.micromega.Lia.
Require Coq.extraction.Extraction.
Require Coq.Unicode.Utf8_core.
Require Equations.Init.
Require Equations.Signature.
Require Equations.CoreTactics.
Require Coq.Relations.Relation_Definitions.
Require Equations.Prop.Logic.
Require Equations.Prop.Classes.
Require Coq.Program.Tactics.
Require Equations.Prop.EqDec.
Require Equations.Prop.DepElim.
Require Coq.Relations.Relations.
Require Equations.Prop.Constants.
Require Coq.Bool.Bvector.
Require Coq.Lists.List.
Require Coq.Arith.Wf_nat.
Require Coq.Wellfounded.Wellfounded.
Require Coq.Relations.Relation_Operators.
Require Coq.Wellfounded.Lexicographic_Product.
Require Coq.Program.Wf.
Require Coq.Logic.FunctionalExtensionality.
Require Equations.Prop.Subterm.
Require Equations.Prop.FunctionalInduction.
Require Equations.Prop.Tactics.
Require Equations.Prop.NoConfusion.
Require Equations.Prop.EqDecInstances.
Require Equations.Prop.Loader.
Require Equations.Prop.Telescopes.
Require Equations.Prop.Equations.
Require Coq.Structures.OrderedType.
Require Coq.Structures.Orders.
Require MetaCoq.Utils.MCCompare.
Require MetaCoq.Utils.ReflectEq.
Require Coq.Strings.Byte.
Require Coq.NArith.BinNat.
Require MetaCoq.Utils.ByteCompare.
Require MetaCoq.Utils.ByteCompareSpec.
Require Coq.Structures.OrdersAlt.
Require MetaCoq.Utils.bytestring.
Require Coq.Init.Decimal.
Require Coq.Numbers.DecimalString.
Require MetaCoq.Utils.MCString.
Require MetaCoq.Common.Primitive.
Require Coq.Arith.Arith.
Require Coq.Bool.Bool.
Require Coq.Classes.CRelationClasses.
Require Coq.Classes.Morphisms.
Require Coq.Classes.RelationClasses.
Require Coq.FSets.FMapAVL.
Require Coq.FSets.FMapFacts.
Require Coq.FSets.FMapFullAVL.
Require Coq.FSets.FMapInterface.
Require Coq.FSets.FMapList.
Require Coq.Init.Nat.
Require Coq.Lists.SetoidList.
Require Coq.MSets.MSetAVL.
Require Coq.MSets.MSetDecide.
Require Coq.MSets.MSetFacts.
Require Coq.MSets.MSetInterface.
Require Coq.MSets.MSetList.
Require Coq.MSets.MSetProperties.
Require Coq.Setoids.Setoid.
Require Coq.Strings.Ascii.
Require Coq.Structures.Equalities.
Require Coq.Structures.OrderedTypeAlt.
Require Coq.Structures.OrderedTypeEx.
Require Coq.Unicode.Utf8.
Require Ltac2.Init.
Require MetaCoq.Utils.MCEquality.
Require MetaCoq.Utils.MCSquash.
Require MetaCoq.Utils.MCTactics.DestructHyps.
Require MetaCoq.Utils.MCTactics.FindHyp.
Require MetaCoq.Utils.MCTactics.Head.
Require MetaCoq.Utils.MCTactics.SpecializeBy.
Require MetaCoq.Utils.MCTactics.SplitInContext.
Require MetaCoq.Utils.MCTactics.Zeta1.
Require Ltac2.Ltac1.
Require Ltac2.Message.
Require MetaCoq.Utils.MCTactics.UniquePose.
Require Ltac2.Control.
Require MetaCoq.Utils.MCTactics.DestructHead.
Require MetaCoq.Utils.MCTactics.GeneralizeOverHoles.
Require MetaCoq.Utils.MCTactics.SpecializeAllWays.
Require MetaCoq.Utils.MCArith.
Require Equations.Type.Logic.
Require MetaCoq.Utils.MCProd.
Require Equations.Type.Relation.
Require Equations.Type.Relation_Properties.
Require MetaCoq.Utils.MCTactics.InHypUnderBindersDo.
Require MetaCoq.Utils.MCTactics.SpecializeUnderBindersBy.
Require MetaCoq.Utils.MCRelations.
Require MetaCoq.Utils.MCPrelude.
Require MetaCoq.Utils.MCReflect.
Require MetaCoq.Utils.MCMSets.
Require MetaCoq.Utils.MCList.
Require MetaCoq.Utils.MCOption.
Require MetaCoq.Utils.All_Forall.
Require MetaCoq.Utils.monad_utils.
Require MetaCoq.Utils.MCUtils.
Require MetaCoq.Utils.utils.
Require MetaCoq.Utils.MCFSets.
Require MetaCoq.Common.Kernames.

Module Export AdmitTactic.
Module Import LocalFalse.
Inductive False : Prop := .
End LocalFalse.
Axiom proof_admitted : False.
Import Coq.Init.Ltac.
Tactic Notation "admit" := abstract case proof_admitted.
End AdmitTactic.

Module Export MetaCoq_DOT_Common_DOT_BasicAst_WRAPPED.
Module Export BasicAst.
Import Coq.ssr.ssreflect.
Import Coq.Classes.Morphisms.
Import Coq.Structures.Orders.
Import Coq.Setoids.Setoid.
Import MetaCoq.Utils.utils.
Export MetaCoq.Common.Kernames.
Import Equations.Prop.Equations.

 
Inductive name : Set :=
| nAnon
| nNamed (_ : ident).
Derive NoConfusion EqDec for name.

Inductive relevance : Set := Relevant | Irrelevant.
Derive NoConfusion EqDec for relevance.

 
Record binder_annot (A : Type) := mkBindAnn { binder_name : A; binder_relevance : relevance }.

Arguments mkBindAnn {_}.
Arguments binder_name {_}.
Arguments binder_relevance {_}.

Derive NoConfusion for binder_annot.

#[global] Instance eqdec_binder_annot (A : Type) (e : Classes.EqDec A) : Classes.EqDec (binder_annot A).
Admitted.
Definition map_binder_annot {A B} (f : A -> B) (b : binder_annot A) : binder_annot B. exact ({| binder_name := f b.(binder_name); binder_relevance := b.(binder_relevance) |}). Defined.
Definition eq_binder_annot {A B} (b : binder_annot A) (b' : binder_annot B) : Prop. exact (b.(binder_relevance) = b'.(binder_relevance)). Defined.

 
Definition aname := binder_annot name.
#[global] Instance anqme_eqdec : Classes.EqDec aname. exact (_). Defined.
Definition eqb_binder_annot {A} (b b' : binder_annot A) : bool. exact (match Classes.eq_dec b.(binder_relevance) b'.(binder_relevance) with
  | left _ => true
  | right _ => false
  end). Defined.

Definition string_of_name (na : name) :=
  match na with
  | nAnon => "_"
  | nNamed n => n
  end.

Definition string_of_relevance (r : relevance) :=
  match r with
  | Relevant => "Relevant"
  | Irrelevant => "Irrelevant"
  end.

 
Inductive cast_kind : Set :=
| VmCast
| NativeCast
| Cast.
Derive NoConfusion EqDec for cast_kind.

Record case_info := mk_case_info {
  ci_ind : inductive;
  ci_npar : nat;
   
  ci_relevance : relevance }.
Derive NoConfusion EqDec for case_info.

Definition string_of_case_info ci :=
  "(" ^ string_of_inductive ci.(ci_ind) ^ "," ^
  string_of_nat ci.(ci_npar) ^ "," ^
   
  string_of_relevance ci.(ci_relevance) ^ ")".

Inductive recursivity_kind :=
  | Finite  
  | CoFinite  
  | BiFinite  .
Derive NoConfusion EqDec for recursivity_kind.

 
Inductive conv_pb :=
  | Conv
  | Cumul.
Derive NoConfusion EqDec for conv_pb.
Definition conv_pb_leqb (pb1 pb2 : conv_pb) : bool. exact (match pb1, pb2 with
     | Cumul, Conv => false
     | _, _ => true
     end). Defined.

 
Definition fresh_evar_id : nat.
Admitted.

 
Record def term := mkdef {
  dname : aname;  
  dtype : term;
  dbody : term;  
  rarg  : nat    }.

Arguments dname {term} _.
Arguments dtype {term} _.
Arguments dbody {term} _.
Arguments rarg {term} _.

Derive NoConfusion for def.
#[global] Instance def_eq_dec {A} : Classes.EqDec A -> Classes.EqDec (def A).
Admitted.

Definition string_of_def {A} (f : A -> string) (def : def A) :=
  "(" ^ string_of_name (binder_name (dname def))
      ^ "," ^ string_of_relevance (binder_relevance (dname def))
      ^ "," ^ f (dtype def)
      ^ "," ^ f (dbody def)
      ^ "," ^ string_of_nat (rarg def) ^ ")".

Definition print_def {A} (f : A -> string) (g : A -> string) (def : def A) :=
  string_of_name (binder_name (dname def)) ^ " { struct " ^ string_of_nat (rarg def) ^ " }" ^
                 " : " ^ f (dtype def) ^ " := " ^ nl ^ g (dbody def).

Definition map_def {A B} (tyf bodyf : A -> B) (d : def A) :=
  {| dname := d.(dname); dtype := tyf d.(dtype); dbody := bodyf d.(dbody); rarg := d.(rarg) |}.

Lemma map_dtype {A B} (f : A -> B) (g : A -> B) (d : def A) :
  f (dtype d) = dtype (map_def f g d).
Admitted.

Lemma map_dbody {A B} (f : A -> B) (g : A -> B) (d : def A) :
  g (dbody d) = dbody (map_def f g d).
Admitted.

Definition mfixpoint term := list (def term).

Definition test_def {A} (tyf bodyf : A -> bool) (d : def A) :=
  tyf d.(dtype) && bodyf d.(dbody).

Definition tFixProp {A} (P P' : A -> Type) (m : mfixpoint A) :=
  All (fun x : def A => P x.(dtype) * P' x.(dbody))%type m.

Lemma map_def_map_def {A B C} (f f' : B -> C) (g g' : A -> B) (d : def A) :
  map_def f f' (map_def g g' d) = map_def (f ∘ g) (f' ∘ g') d.
Admitted.

Lemma compose_map_def {A B C} (f f' : B -> C) (g g' : A -> B) :
  (map_def f f') ∘ (map_def g g') = map_def (f ∘ g) (f' ∘ g').
Admitted.

Lemma map_def_id {t} x : map_def (@id t) (@id t) x = id x.
Admitted.
#[global] Hint Rewrite @map_def_id @map_id : map.

Lemma map_def_spec {A B} (P P' : A -> Type) (f f' g g' : A -> B) (x : def A) :
  P' x.(dbody) -> P x.(dtype) -> (forall x, P x -> f x = g x) ->
  (forall x, P' x -> f' x = g' x) ->
  map_def f f' x = map_def g g' x.
Admitted.

#[global] Hint Extern 10 (_ < _)%nat => lia : all.
#[global] Hint Extern 10 (_ <= _)%nat => lia : all.
#[global] Hint Extern 10 (@eq nat _ _) => lia : all.
#[global] Hint Extern 0 (_ = _) => progress f_equal : all.
#[global] Hint Unfold on_snd snd : all.

Lemma on_snd_eq_id_spec {A B} (f : B -> B) (x : A * B) :
  f (snd x) = snd x <->
  on_snd f x = x.
Admitted.
#[global] Hint Resolve -> on_snd_eq_id_spec : all.
#[global] Hint Resolve -> on_snd_eq_spec : all.

Lemma map_def_eq_spec {A B} (f f' g g' : A -> B) (x : def A) :
  f (dtype x) = g (dtype x) ->
  f' (dbody x) = g' (dbody x) ->
  map_def f f' x = map_def g g' x.
Admitted.
#[global] Hint Resolve map_def_eq_spec : all.

Lemma map_def_id_spec {A} (f f' : A -> A) (x : def A) :
  f (dtype x) = (dtype x) ->
  f' (dbody x) = (dbody x) ->
  map_def f f' x = x.
Admitted.
#[global] Hint Resolve map_def_id_spec : all.

Lemma tfix_map_spec {A B} {P P' : A -> Type} {l} {f f' g g' : A -> B} :
  tFixProp P P' l -> (forall x, P x -> f x = g x) ->
  (forall x, P' x -> f' x = g' x) ->
  map (map_def f f') l = map (map_def g g') l.
Admitted.

Variant typ_or_sort_ {term} := Typ (T : term) | Sort.
Arguments typ_or_sort_ : clear implicits.

Definition typ_or_sort_map {T T'} (f: T -> T') t :=
  match t with
  | Typ T => Typ (f T)
  | Sort => Sort
  end.

Definition typ_or_sort_default {T A} (f: T -> A) t d :=
  match t with
  | Typ T => f T
  | Sort => d
  end.

Section Contexts.
  Context {term : Type}.
   

  Record context_decl := mkdecl {
    decl_name : aname ;
    decl_body : option term ;
    decl_type : term
  }.
  Derive NoConfusion for context_decl.
End Contexts.

Arguments context_decl : clear implicits.
Definition map_decl {term term'} (f : term -> term') (d : context_decl term) : context_decl term'. exact ({| decl_name := d.(decl_name);
     decl_body := option_map f d.(decl_body);
     decl_type := f d.(decl_type) |}). Defined.

Lemma compose_map_decl {term term' term''} (g : term -> term') (f : term' -> term'') x :
  map_decl f (map_decl g x) = map_decl (f ∘ g) x.
Admitted.

Lemma map_decl_ext {term term'} (f g : term -> term') x : (forall x, f x = g x) -> map_decl f x = map_decl g x.
Admitted.

#[global] Instance map_decl_proper {term term'} : Proper (`=1` ==> Logic.eq ==> Logic.eq) (@map_decl term term').
Admitted.

#[global] Instance map_decl_pointwise {term term'} : Proper (`=1` ==> `=1`) (@map_decl term term').
Admitted.
 

Definition map_context {term term'} (f : term -> term') (c : list (context_decl term)) :=
  List.map (map_decl f) c.

#[global] Instance map_context_proper {term term'} : Proper (`=1` ==> Logic.eq ==> Logic.eq) (@map_context term term').
Admitted.

Lemma map_context_length {term term'} (f : term -> term') l : #|map_context f l| = #|l|.
Admitted.
#[global] Hint Rewrite @map_context_length : len.
Definition test_decl {term} (f : term -> bool) (d : context_decl term) : bool. exact (option_default f d.(decl_body) true && f d.(decl_type)). Defined.

#[global] Instance test_decl_proper {term} : Proper (`=1` ==> Logic.eq ==> Logic.eq) (@test_decl term).
Admitted.

Definition snoc {A} (Γ : list A) (d : A) := d :: Γ.

Notation " Γ ,, d " := (snoc Γ d) (at level 20, d at next level).

Definition ondecl {A} (P : A -> Type) (d : context_decl A) :=
  P d.(decl_type) × option_default P d.(decl_body) unit.

Notation onctx P := (All (ondecl P)).

Section ContextMap.
  Context {term term' : Type} (f : nat -> term -> term').
Fixpoint mapi_context (c : list (context_decl term)) : list (context_decl term'). exact (match c with
    | d :: Γ => map_decl (f #|Γ|) d :: mapi_context Γ
    | [] => []
  end). Defined.
End ContextMap.

#[global] Instance mapi_context_proper {term term'} : Proper (`=2` ==> Logic.eq ==> Logic.eq) (@mapi_context term term').
Admitted.

Lemma mapi_context_length {term} (f : nat -> term -> term) l : #|mapi_context f l| = #|l|.
Admitted.
#[global] Hint Rewrite @mapi_context_length : len.

Section ContextTest.
  Context {term : Type} (f : term -> bool).
Fixpoint test_context (c : list (context_decl term)) : bool. exact (match c with
    | d :: Γ => test_context Γ && test_decl f d
    | [] => true
    end). Defined.
End ContextTest.

#[global] Instance test_context_proper {term} : Proper (`=1` ==> Logic.eq ==> Logic.eq) (@test_context term).
Admitted.

Section ContextTestK.
  Context {term : Type} (f : nat -> term -> bool) (k : nat).
Fixpoint test_context_k (c : list (context_decl term)) : bool. exact (match c with
    | d :: Γ => test_context_k Γ && test_decl (f (#|Γ| + k)) d
    | [] => true
    end). Defined.
End ContextTestK.

#[global] Instance test_context_k_proper {term} : Proper (`=1` ==> Logic.eq ==> Logic.eq ==> Logic.eq) (@test_context_k term).
Admitted.

Section Contexts.
  Context {term term' term'' : Type}.
  Notation context term := (list (context_decl term)).

  Lemma test_decl_impl (f g : term -> bool) x : (forall x, f x -> g x) ->
    test_decl f x -> test_decl g x.
Admitted.

  Definition onctx_k (P : nat -> term -> Type) k (ctx : context term) :=
    Alli (fun i d => ondecl (P (Nat.pred #|ctx| - i + k)) d) 0 ctx.

  Lemma ondeclP {P : term -> Type} {p : term -> bool} {d : context_decl term} :
    (forall x, reflectT (P x) (p x)) ->
    reflectT (ondecl P d) (test_decl p d).
Admitted.

  Lemma onctxP {p : term -> bool} {ctx : context term} :
    reflectT (onctx p ctx) (test_context p ctx).
Admitted.

  Lemma map_decl_type (f : term -> term') decl : f (decl_type decl) = decl_type (map_decl f decl).
Admitted.

  Lemma map_decl_body (f : term -> term') decl : option_map f (decl_body decl) = decl_body (map_decl f decl).
admit.
Defined.

  Lemma map_decl_id : @map_decl term term id =1 id.
Admitted.

  Lemma option_map_decl_body_map_decl (f : term -> term') x :
    option_map decl_body (option_map (map_decl f) x) =
    option_map (option_map f) (option_map decl_body x).
Admitted.

  Lemma option_map_decl_type_map_decl (f : term -> term') x :
    option_map decl_type (option_map (map_decl f) x) =
    option_map f (option_map decl_type x).
Admitted.

  Definition fold_context_k (f : nat -> term -> term') Γ :=
    List.rev (mapi (fun k' decl => map_decl (f k') decl) (List.rev Γ)).

  Arguments fold_context_k f Γ%list_scope.

  Lemma fold_context_k_alt f Γ :
    fold_context_k f Γ =
    mapi (fun k' d => map_decl (f (Nat.pred (length Γ) - k')) d) Γ.
Admitted.

  Lemma mapi_context_fold f Γ :
    mapi_context f Γ = fold_context_k f Γ.
Admitted.

  Lemma fold_context_k_tip f d : fold_context_k f [d] = [map_decl (f 0) d].
Admitted.

  Lemma fold_context_k_length f Γ : length (fold_context_k f Γ) = length Γ.
Admitted.

  Lemma fold_context_k_snoc0 f Γ d :
    fold_context_k f (d :: Γ) = fold_context_k f Γ ,, map_decl (f (length Γ)) d.
Admitted.

  Lemma fold_context_k_app f Γ Δ :
    fold_context_k f (Δ ++ Γ)
    = fold_context_k (fun k => f (length Γ + k)) Δ ++ fold_context_k f Γ.
Admitted.

  Local Set Keyed Unification.

  Equations mapi_context_In (ctx : context term) (f : nat -> forall (x : context_decl term), In x ctx -> context_decl term) : context term :=
  mapi_context_In nil _ := nil;
  mapi_context_In (cons x xs) f := cons (f #|xs| x _) (mapi_context_In xs (fun n x H => f n x _)).

  Lemma mapi_context_In_spec (f : nat -> term -> term) (ctx : context term) :
    mapi_context_In ctx (fun n (x : context_decl term) (_ : In x ctx) => map_decl (f n) x) =
    mapi_context f ctx.
Admitted.

  Equations fold_context_In (ctx : context term) (f : context term -> forall (x : context_decl term), In x ctx -> context_decl term) : context term :=
  fold_context_In nil _ := nil;
  fold_context_In (cons x xs) f :=
    let xs' := fold_context_In xs (fun n x H => f n x _) in
    cons (f xs' x _) xs'.

  Equations fold_context (f : context term -> context_decl term -> context_decl term) (ctx : context term) : context term :=
    fold_context f nil := nil;
    fold_context f (cons x xs) :=
      let xs' := fold_context f xs in
      cons (f xs' x ) xs'.

  Lemma fold_context_length f Γ : #|fold_context f Γ| = #|Γ|.
Admitted.

  Lemma fold_context_In_spec (f : context term -> context_decl term -> context_decl term) (ctx : context term) :
    fold_context_In ctx (fun n (x : context_decl term) (_ : In x ctx) => f n x) =
    fold_context f ctx.
Admitted.

  #[global]
  Instance fold_context_Proper : Proper (`=2` ==> `=1`) fold_context.
Admitted.
Definition forget_types (c : list (BasicAst.context_decl term)) : list aname. exact (map decl_name c). Defined.

End Contexts.
#[global] Hint Rewrite @fold_context_length @fold_context_k_length : len.

Section Contexts.
  Context {term term' term'' : Type}.
  Notation context term := (list (context_decl term)).

  Lemma fold_context_k_id (x : context term) : fold_context_k (fun i x => x) x = x.
Admitted.

  Lemma fold_context_k_compose (f : nat -> term' -> term) (g : nat -> term'' -> term') Γ :
    fold_context_k f (fold_context_k g Γ) =
    fold_context_k (fun i => f i ∘ g i) Γ.
Admitted.

  Lemma fold_context_k_ext (f g : nat -> term' -> term) Γ :
    f =2 g ->
    fold_context_k f Γ = fold_context_k g Γ.
Admitted.

  #[global] Instance fold_context_k_proper : Proper (pointwise_relation nat (pointwise_relation _ Logic.eq) ==> Logic.eq ==> Logic.eq)
    (@fold_context_k term' term).
Admitted.

  Lemma alli_fold_context_k_prop (f : nat -> context_decl term -> bool) (g : nat -> term' -> term) ctx :
    alli f 0 (fold_context_k g ctx) =
    alli (fun i x => f i (map_decl (g (Nat.pred #|ctx| - i)) x)) 0 ctx.
Admitted.

  Lemma test_decl_map_decl f g x : (@test_decl term) f (map_decl g x) = @test_decl term (f ∘ g) x.
Admitted.

  Lemma map_fold_context_k (f : term' -> term) (g : nat -> term'' -> term') ctx :
    map (map_decl f) (fold_context_k g ctx) = fold_context_k (fun i => f ∘ g i) ctx.
Admitted.

  Lemma map_context_mapi_context (f : term' -> term) (g : nat -> term'' -> term') (ctx : list (BasicAst.context_decl term'')) :
    map_context f (mapi_context g ctx) =
    mapi_context (fun i => f ∘ g i) ctx.
Admitted.

  Lemma mapi_context_map (f : nat -> term' -> term) (g : context_decl term'' -> context_decl term') ctx :
    mapi_context f (map g ctx) = mapi (fun i => map_decl (f (Nat.pred #|ctx| - i)) ∘ g) ctx.
Admitted.

  Lemma map_context_map (f : term' -> term) (g : context_decl term'' -> context_decl term') ctx :
    map_context f (map g ctx) = map (map_decl f ∘ g) ctx.
Admitted.

  Lemma map_map_context (f : context_decl term' -> term) (g : term'' -> term') ctx :
    map f (map_context g ctx) = map (f ∘ map_decl g) ctx.
Admitted.

  Lemma fold_context_k_map (f : nat -> term' -> term) (g : term'' -> term') Γ :
    fold_context_k f (map_context g Γ) =
    fold_context_k (fun k => f k ∘ g) Γ.
Admitted.

  Lemma fold_context_k_map_comm (f : nat -> term -> term) (g : term -> term) Γ :
    (forall i x, f i (g x) = g (f i x)) ->
    fold_context_k f (map_context g Γ) = map_context g (fold_context_k f Γ).
Admitted.

  Lemma mapi_context_map_context (f : nat -> term' -> term) (g : term'' -> term') ctx :
    mapi_context f (map_context g ctx) =
    mapi_context (fun i => f i ∘ g) ctx.
Admitted.

  Lemma map_mapi_context (f : context_decl term' -> term) (g : nat -> term'' -> term') ctx :
    map f (mapi_context g ctx) = mapi (fun i => f ∘ map_decl (g (Nat.pred #|ctx| - i))) ctx.
Admitted.

  Lemma map_context_id (ctx : context term) : map_context id ctx = ctx.
Admitted.

End Contexts.
Module Export Universes.
Import Coq.MSets.MSetList.
Import MetaCoq.Utils.utils.

Module Level.
  Inductive t_ : Set :=
  | lzero
  | level (_ : string)
  | lvar (_ : nat)  .

  Definition t := t_.
Definition compare (l1 l2 : t) : comparison.
Admitted.
Definition eq : t -> t -> Prop.
exact (eq).
Defined.
Definition eq_equiv : Equivalence eq.
Admitted.

  Inductive lt_ : t -> t -> Prop :=
  | ltSetLevel s : lt_ lzero (level s)
  | ltSetlvar n : lt_ lzero (lvar n)
  | ltLevelLevel s s' : StringOT.lt s s' -> lt_ (level s) (level s')
  | ltLevellvar s n : lt_ (level s) (lvar n)
  | ltlvarlvar n n' : Nat.lt n n' -> lt_ (lvar n) (lvar n').

  Definition lt := lt_.

  Definition lt_strorder : StrictOrder lt.
Admitted.

  Definition lt_compat : Proper (eq ==> eq ==> iff) lt.
Admitted.

  Definition compare_spec :
    forall x y : t, CompareSpec (x = y) (lt x y) (lt y x) (compare x y).
Admitted.
Definition eq_dec : forall (l1 l2 : t), {l1 = l2}+{l1 <> l2}.
Admitted.

End Level.

Module LevelSet := MSetAVL.Make Level.

Module LevelExpr.

  Definition t := (Level.t * nat)%type.
Definition eq : t -> t -> Prop.
exact (eq).
Defined.
Definition eq_equiv : Equivalence eq.
Admitted.

  Inductive lt_ : t -> t -> Prop :=
  | ltLevelExpr1 l n n' : (n < n')%nat -> lt_ (l, n) (l, n')
  | ltLevelExpr2 l l' b b' : Level.lt l l' -> lt_ (l, b) (l', b').

  Definition lt := lt_.

  Global Instance lt_strorder : StrictOrder lt.
Admitted.

  Definition lt_compat : Proper (Logic.eq ==> Logic.eq ==> iff) lt.
Admitted.
Definition compare (x y : t) : comparison.
Admitted.

  Definition compare_spec :
    forall x y : t, CompareSpec (x = y) (lt x y) (lt y x) (compare x y).
Admitted.
Definition eq_dec : forall (l1 l2 : t), {l1 = l2} + {l1 <> l2}.
Admitted.
Definition eq_leibniz (x y : t) : eq x y -> x = y.
Admitted.

End LevelExpr.

Module LevelExprSet := MSetList.MakeWithLeibniz LevelExpr.

Record nonEmptyLevelExprSet
  := { t_set : LevelExprSet.t ;
       t_ne  : LevelExprSet.is_empty t_set = false }.

Module Export LevelAlgExpr.

  Definition t := nonEmptyLevelExprSet.
Definition lt : t -> t -> Prop.
Admitted.
End LevelAlgExpr.

Inductive allowed_eliminations : Set :=
  | IntoSProp
  | IntoPropSProp
  | IntoSetPropSProp
  | IntoAny.

Module Export Universe.
  Inductive t_ :=
    lProp | lSProp | lType (_ : LevelAlgExpr.t).

  Definition t := t_.

  Inductive lt_ : t -> t -> Prop :=
  | ltPropSProp : lt_ lProp lSProp
  | ltPropType s : lt_ lProp (lType s)
  | ltSPropType s : lt_ lSProp (lType s)
  | ltTypeType s1 s2 : LevelAlgExpr.lt s1 s2 -> lt_ (lType s1) (lType s2).

  Definition lt := lt_.

  Module OT <: OrderedType.
    Definition t := t.
#[local] Definition eq : t -> t -> Prop.
exact (eq).
Defined.
#[local] Definition eq_equiv : Equivalence eq.
Admitted.
    Definition lt := lt.
    #[local] Instance lt_strorder : StrictOrder lt.
Admitted.

    Definition lt_compat : Proper (eq ==> eq ==> iff) lt.
Admitted.
Definition compare (x y : t) : comparison.
Admitted.
    Lemma compare_spec x y : CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
Admitted.
    Definition eq_dec (x y : t) : {x = y} + {x <> y}.
Admitted.
  End OT.
End Universe.

Module Export ConstraintType.
  Inductive t_ : Set := Le (z : Z) | Eq.

  Definition t := t_.

  Inductive lt_ : t -> t -> Prop :=
  | LeLe n m : (n < m)%Z -> lt_ (Le n) (Le m)
  | LeEq n : lt_ (Le n) Eq.
  Definition lt := lt_.
End ConstraintType.

Module Export UnivConstraint.
Definition t : Set.
exact (Level.t * ConstraintType.t * Level.t).
Defined.
Definition eq : t -> t -> Prop.
Admitted.
Definition eq_equiv : Equivalence eq.
Admitted.

  Inductive lt_ : t -> t -> Prop :=
  | lt_Level2 l1 t l2 l2' : Level.lt l2 l2' -> lt_ (l1, t, l2) (l1, t, l2')
  | lt_Cstr l1 t t' l2 l2' : ConstraintType.lt t t' -> lt_ (l1, t, l2) (l1, t', l2')
  | lt_Level1 l1 l1' t t' l2 l2' : Level.lt l1 l1' -> lt_ (l1, t, l2) (l1', t', l2').
  Definition lt := lt_.

  Lemma lt_strorder : StrictOrder lt.
Admitted.

  Lemma lt_compat : Proper (eq ==> eq ==> iff) lt.
Admitted.
Definition compare : t -> t -> comparison.
Admitted.

  Lemma compare_spec x y
    : CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
Admitted.

  Lemma eq_dec x y : {eq x y} + {~ eq x y}.
Admitted.
End UnivConstraint.

Module ConstraintSet := MSetAVL.Make UnivConstraint.

Module Export Instance.
Definition t : Set.
Admitted.
End Instance.

Module Export AUContext.
  Definition t := list name × ConstraintSet.t.
End AUContext.

Module Export ContextSet.
  Definition t := LevelSet.t × ConstraintSet.t.
End ContextSet.

Module Export Variance.

  Inductive t :=
  | Irrelevant : t
  | Covariant : t
  | Invariant : t.

Inductive universes_decl : Type :=
| Monomorphic_ctx
| Polymorphic_ctx (cst : AUContext.t).

Class UnivSubst A := subst_instance : Instance.t -> A -> A.
#[global] Instance subst_instance_univ : UnivSubst Universe.t.
Admitted.
#[global] Instance subst_instance_instance : UnivSubst Instance.t.
Admitted.

Module Type Term.

  Parameter Inline term : Type.

  Parameter Inline tRel : nat -> term.

  Parameter Inline lift : nat -> nat -> term -> term.
  Parameter Inline subst : list term -> nat -> term -> term.
  Parameter Inline subst_instance_constr : UnivSubst term.
End Term.

Module Type TermDecide (Import T : Term).
End TermDecide.

Module Export Retroknowledge.

  Record t := mk_retroknowledge {
    retro_int63 : option kername;
    retro_float64 : option kername;
  }.

Module Environment (T : Term).

  Import T.
  #[global] Existing Instance subst_instance_constr.

  Notation context_decl := (context_decl term).

  Definition vass x A : context_decl :=
    {| decl_name := x ; decl_body := None ; decl_type := A |}.

  Definition vdef x t A : context_decl :=
    {| decl_name := x ; decl_body := Some t ; decl_type := A |}.

  Definition context := list context_decl.

  Definition subst_context s k (Γ : context) : context :=
    fold_context_k (fun k' => subst s (k' + k)) Γ.
Global Instance subst_instance_context : UnivSubst context.
exact (map_context ∘ subst_instance).
Defined.

  Fixpoint context_assumptions (Γ : context) :=
    match Γ with
    | [] => 0
    | d :: Γ =>
      match d.(decl_body) with
      | Some _ => context_assumptions Γ
      | None => S (context_assumptions Γ)
      end
    end.

  Fixpoint extended_subst (Γ : context) (n : nat)
    :=
  match Γ with
  | nil => nil
  | cons d vs =>
    match decl_body d with
    | Some b =>

      let s := extended_subst vs n in

      let b' := lift (context_assumptions vs + n) #|s| b in

      let b' := subst s 0 b' in

      b' :: s
    | None => tRel n :: extended_subst vs (S n)
    end
  end.

  Definition expand_lets_k Γ k t :=
    (subst (extended_subst Γ 0) k (lift (context_assumptions Γ) (k + #|Γ|) t)).

  Definition expand_lets Γ t := expand_lets_k Γ 0 t.
Definition fix_context (m : mfixpoint term) : context.
Admitted.

  Record constructor_body := {
    cstr_name : ident;

    cstr_args : context;
    cstr_indices : list term;
    cstr_type : term;

    cstr_arity : nat;
  }.

  Record projection_body := {
    proj_name : ident;

    proj_relevance : relevance;
    proj_type : term;
  }.

  Record one_inductive_body := {
    ind_name : ident;
    ind_indices : context;
    ind_sort : Universe.t;
    ind_type : term;
    ind_kelim : allowed_eliminations;
    ind_ctors : list constructor_body;
    ind_projs : list projection_body;
    ind_relevance : relevance   }.

  Record mutual_inductive_body := {
    ind_finite : recursivity_kind;
    ind_npars : nat;
    ind_params : context;
    ind_bodies : list one_inductive_body ;
    ind_universes : universes_decl;
    ind_variance : option (list Universes.Variance.t) }.

  Record constant_body := {
    cst_type : term;
    cst_body : option term;
    cst_universes : universes_decl;
    cst_relevance : relevance }.

  Inductive global_decl :=
  | ConstantDecl : constant_body -> global_decl
  | InductiveDecl : mutual_inductive_body -> global_decl.

  Definition global_declarations := list (kername * global_decl).

  Record global_env := mk_global_env
    { universes : ContextSet.t;
      declarations : global_declarations;
      retroknowledge : Retroknowledge.t }.
Definition app_context (Γ Γ' : context) : context.
Admitted.
  Notation "Γ ,,, Γ'" :=
    (app_context Γ Γ') (at level 25, Γ' at next level, left associativity).

End Environment.

Module Type EnvironmentSig (T : Term).
 Include Environment T.
End EnvironmentSig.

Module Type EnvironmentDecide (T : Term) (Import E : EnvironmentSig T).
End EnvironmentDecide.

Module Type TermUtils (T: Term) (E: EnvironmentSig T).

End TermUtils.
Module Export EnvironmentTyping.
Import Coq.ssr.ssreflect.
Import MetaCoq.Common.Primitive.

Module Lookup (T : Term) (E : EnvironmentSig T).
Import E.

  Definition declared_constant (Σ : global_env) id decl := In (id,ConstantDecl decl) (declarations Σ).

End Lookup.

  Inductive prim_model (term : Type) : prim_tag -> Type :=
| primIntModel (i : PrimInt63.int) : prim_model term primInt
| primFloatModel (f : PrimFloat.float) : prim_model term primFloat.

Definition prim_val term := ∑ t : prim_tag, prim_model term t.

Record predicate {term} := mk_predicate {
  pparams : list term;
  puinst : Instance.t;
  pcontext : list (context_decl term);

  preturn : term;   }.
Arguments predicate : clear implicits.

Section map_predicate.
  Context {term term' : Type}.
  Context (uf : Instance.t -> Instance.t).
  Context (paramf preturnf : term -> term').
  Context (pcontextf : list (context_decl term) -> list (context_decl term')).

  Definition map_predicate (p : predicate term) :=
    {| pparams := map paramf p.(pparams);
        puinst := uf p.(puinst);
        pcontext := pcontextf p.(pcontext);
        preturn := preturnf p.(preturn) |}.

End map_predicate.

Section map_predicate_k.
  Context {term : Type}.
  Context (uf : Instance.t -> Instance.t).
  Context (f : nat -> term -> term).

  Definition map_predicate_k k (p : predicate term) :=
    {| pparams := map (f k) p.(pparams);
        puinst := uf p.(puinst);
        pcontext := p.(pcontext);
        preturn := f (#|p.(pcontext)| + k) p.(preturn) |}.

End map_predicate_k.

Section Branch.
  Context {term : Type}.

  Record branch := mk_branch {
    bcontext : list (context_decl term);

    bbody : term;   }.

End Branch.
Arguments branch : clear implicits.

Section map_branch.
  Context {term term' : Type}.
  Context (f : term -> term').
  Context (g : list (BasicAst.context_decl term) -> list (BasicAst.context_decl term')).

  Definition map_branch (b : branch term) :=
  {| bcontext := g b.(bcontext);
      bbody := f b.(bbody) |}.
End map_branch.

Section map_branch_k.
  Context {term term' : Type}.
  Context (f : nat -> term -> term').
  Context (g : list (BasicAst.context_decl term) -> list (BasicAst.context_decl term')).
  Definition map_branch_k k (b : branch term) :=
  {| bcontext := g b.(bcontext);
     bbody := f (#|b.(bcontext)| + k) b.(bbody) |}.
End map_branch_k.

Notation map_branches_k f h k brs :=
  (List.map (map_branch_k f h k) brs).

Inductive term :=
| tRel (n : nat)
| tVar (i : ident)
| tEvar (n : nat) (l : list term)
| tSort (u : Universe.t)
| tProd (na : aname) (A B : term)
| tLambda (na : aname) (A t : term)
| tLetIn (na : aname) (b B t : term)
| tApp (u v : term)
| tConst (k : kername) (ui : Instance.t)
| tInd (ind : inductive) (ui : Instance.t)
| tConstruct (ind : inductive) (n : nat) (ui : Instance.t)
| tCase (indn : case_info) (p : predicate term) (c : term) (brs : list (branch term))
| tProj (p : projection) (c : term)
| tFix (mfix : mfixpoint term) (idx : nat)
| tCoFix (mfix : mfixpoint term) (idx : nat)
| tPrim (prim : prim_val term).

Fixpoint mkApps t us :=
  match us with
  | nil => t
  | u :: us => mkApps (tApp t u) us
  end.

Fixpoint lift n k t : term :=
  match t with
  | tRel i => tRel (if Nat.leb k i then (n + i) else i)
  | tEvar ev args => tEvar ev (List.map (lift n k) args)
  | tLambda na T M => tLambda na (lift n k T) (lift n (S k) M)
  | tApp u v => tApp (lift n k u) (lift n k v)
  | tProd na A B => tProd na (lift n k A) (lift n (S k) B)
  | tLetIn na b t b' => tLetIn na (lift n k b) (lift n k t) (lift n (S k) b')
  | tCase ind p c brs =>
    let p' := map_predicate_k id (lift n) k p in
    let brs' := map_branches_k (lift n) id k brs in
    tCase ind p' (lift n k c) brs'
  | tProj p c => tProj p (lift n k c)
  | tFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (lift n k) (lift n k')) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (lift n k) (lift n k')) mfix in
    tCoFix mfix' idx
  | x => x
  end.

Notation lift0 n := (lift n 0).

Fixpoint subst s k u :=
  match u with
  | tRel n =>
    if Nat.leb k n then
      match nth_error s (n - k) with
      | Some b => lift0 k b
      | None => tRel (n - List.length s)
      end
    else tRel n
  | tEvar ev args => tEvar ev (List.map (subst s k) args)
  | tLambda na T M => tLambda na (subst s k T) (subst s (S k) M)
  | tApp u v => tApp (subst s k u) (subst s k v)
  | tProd na A B => tProd na (subst s k A) (subst s (S k) B)
  | tLetIn na b ty b' => tLetIn na (subst s k b) (subst s k ty) (subst s (S k) b')
  | tCase ind p c brs =>
    let p' := map_predicate_k id (subst s) k p in
    let brs' := map_branches_k (subst s) id k brs in
    tCase ind p' (subst s k c) brs'
  | tProj p c => tProj p (subst s k c)
  | tFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (subst s k) (subst s k')) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (subst s k) (subst s k')) mfix in
    tCoFix mfix' idx
  | x => x
  end.

Notation subst0 t := (subst t 0).
Definition subst1 t k u := subst [t] k u.
Notation "M { j := N }" := (subst1 N j M) (at level 10, right associativity).
#[global]
Instance subst_instance_constr : UnivSubst term.
exact (fix subst_instance_constr u c {struct c} : term :=
  match c with
  | tRel _ | tVar _ => c
  | tEvar ev args => tEvar ev (List.map (subst_instance_constr u) args)
  | tSort s => tSort (subst_instance_univ u s)
  | tConst c u' => tConst c (subst_instance_instance u u')
  | tInd i u' => tInd i (subst_instance_instance u u')
  | tConstruct ind k u' => tConstruct ind k (subst_instance_instance u u')
  | tLambda na T M => tLambda na (subst_instance_constr u T) (subst_instance_constr u M)
  | tApp f v => tApp (subst_instance_constr u f) (subst_instance_constr u v)
  | tProd na A B => tProd na (subst_instance_constr u A) (subst_instance_constr u B)
  | tLetIn na b ty b' => tLetIn na (subst_instance_constr u b) (subst_instance_constr u ty)
                                (subst_instance_constr u b')
  | tCase ind p c brs =>
    let p' := map_predicate (subst_instance_instance u) (subst_instance_constr u) (subst_instance_constr u) id p in
    let brs' := List.map (map_branch (subst_instance_constr u) id) brs in
    tCase ind p' (subst_instance_constr u c) brs'
  | tProj p c => tProj p (subst_instance_constr u c)
  | tFix mfix idx =>
    let mfix' := List.map (map_def (subst_instance_constr u) (subst_instance_constr u)) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let mfix' := List.map (map_def (subst_instance_constr u) (subst_instance_constr u)) mfix in
    tCoFix mfix' idx
  | tPrim _ => c
  end).
Defined.

Module PCUICTerm <: Term.

  Definition term := term.

  Definition tRel := tRel.

  Definition lift := lift.
  Definition subst := subst.
  Definition subst_instance_constr := subst_instance.
End PCUICTerm.

Module PCUICEnvironment := Environment PCUICTerm.
Export PCUICEnvironment.

Module PCUICLookup := EnvironmentTyping.Lookup PCUICTerm PCUICEnvironment.
Include PCUICLookup.
Definition set_preturn (p : predicate term) (pret' : term) : predicate term.
Admitted.
Definition set_pparams (p : predicate term) (pars' : list term) : predicate term.
Admitted.

Fixpoint decompose_app_rec (t : term) l :=
  match t with
  | tApp f a => decompose_app_rec f (a :: l)
  | _ => (t, l)
  end.

Definition decompose_app t := decompose_app_rec t [].

Definition isConstruct_app t :=
  match fst (decompose_app t) with
  | tConstruct _ _ _ => true
  | _ => false
  end.

Definition inst_case_context params puinst (pctx : context) :=
  subst_context (List.rev params) 0 (subst_instance puinst pctx).

Definition inst_case_predicate_context (p : predicate term) :=
  inst_case_context p.(pparams) p.(puinst) p.(pcontext).

Definition inst_case_branch_context (p : predicate term) (br : branch term) :=
  inst_case_context p.(pparams) p.(puinst) br.(bcontext).

Definition iota_red npar p args br :=
  subst (List.rev (List.skipn npar args)) 0
    (expand_lets (inst_case_branch_context p br) (bbody br)).

Definition fix_subst (l : mfixpoint term) :=
  let fix aux n :=
      match n with
      | 0 => []
      | S n => tFix l n :: aux n
      end
  in aux (List.length l).

Definition unfold_fix (mfix : mfixpoint term) (idx : nat) :=
  match List.nth_error mfix idx with
  | Some d => Some (d.(rarg), subst0 (fix_subst mfix) d.(dbody))
  | None => None
  end.

Definition cofix_subst (l : mfixpoint term) :=
  let fix aux n :=
      match n with
      | 0 => []
      | S n => tCoFix l n :: aux n
      end
  in aux (List.length l).

Definition unfold_cofix (mfix : mfixpoint term) (idx : nat) :=
  match List.nth_error mfix idx with
  | Some d => Some (d.(rarg), subst0 (cofix_subst mfix) d.(dbody))
  | None => None
  end.

Definition is_constructor n ts :=
  match List.nth_error ts n with
  | Some a => isConstruct_app a
  | None => false
  end.
#[global]
Instance subst_instance_list A `{UnivSubst A} : UnivSubst (list A).
exact (fun u => List.map (subst_instance u)).
Defined.

Lemma subst_instance_lift u c n k :
  subst_instance u (lift n k c) = lift n k (subst_instance u c).
Admitted.

Lemma subst_instance_mkApps u f a :
  subst_instance u (mkApps f a) =
  mkApps (subst_instance u f) (map (subst_instance u) a).
Admitted.

Lemma subst_instance_subst u c (s : list term) k :
  subst_instance u (subst s k c) = subst (subst_instance u s) k (subst_instance u c).
Admitted.

Section compare_decls.

  Context {eq_term leq_term : term -> term -> Type}.
  Inductive compare_decls  : context_decl -> context_decl -> Type :=
  | compare_vass {na T na' T'} :
    eq_binder_annot na na' ->
    leq_term T T' ->
    compare_decls (vass na T) (vass na' T')
  | compare_vdef {na b T na' b' T'} :
    eq_binder_annot na na' ->
    eq_term b b' ->
    leq_term T T' ->
    compare_decls (vdef na b T) (vdef na' b' T').
End compare_decls.

#[global]
Hint Constructors compare_decls : pcuic.

Reserved Notation " Σ ;;; Γ |- t ⇝ u " (at level 50, Γ, t, u at next level).

Inductive red1 (Σ : global_env) (Γ : context) : term -> term -> Type :=

| red_beta na t b a :
  Σ ;;; Γ |- tApp (tLambda na t b) a ⇝ b {0 := a}

| red_zeta na b t b' :
  Σ ;;; Γ |- tLetIn na b t b' ⇝ b' {0 := b}

| red_rel i body :
    option_map decl_body (nth_error Γ i) = Some (Some body) ->
    Σ ;;; Γ |- tRel i ⇝ lift0 (S i) body

| red_iota ci c u args p brs br :
    nth_error brs c = Some br ->
    #|args| = (ci.(ci_npar) + context_assumptions br.(bcontext))%nat ->
    Σ ;;; Γ |- tCase ci p (mkApps (tConstruct ci.(ci_ind) c u) args) brs
        ⇝ iota_red ci.(ci_npar) p args br

| red_fix mfix idx args narg fn :
    unfold_fix mfix idx = Some (narg, fn) ->
    is_constructor narg args = true ->
    Σ ;;; Γ |- mkApps (tFix mfix idx) args ⇝ mkApps fn args

| red_cofix_case ip p mfix idx args narg fn brs :
    unfold_cofix mfix idx = Some (narg, fn) ->
    Σ ;;; Γ |- tCase ip p (mkApps (tCoFix mfix idx) args) brs ⇝
         tCase ip p (mkApps fn args) brs

| red_cofix_proj p mfix idx args narg fn :
    unfold_cofix mfix idx = Some (narg, fn) ->
    Σ ;;; Γ |- tProj p (mkApps (tCoFix mfix idx) args) ⇝ tProj p (mkApps fn args)

| red_delta c decl body (isdecl : declared_constant Σ c decl) u :
    decl.(cst_body) = Some body ->
    Σ ;;; Γ |- tConst c u ⇝ subst_instance u body

| red_proj p args u arg:
    nth_error args (p.(proj_npars) + p.(proj_arg)) = Some arg ->
    Σ ;;; Γ |- tProj p (mkApps (tConstruct p.(proj_ind) 0 u) args) ⇝ arg

| abs_red_l na M M' N : Σ ;;; Γ |- M ⇝ M' -> Σ ;;; Γ |- tLambda na M N ⇝ tLambda na M' N
| abs_red_r na M M' N : Σ ;;; Γ ,, vass na N |- M ⇝ M' -> Σ ;;; Γ |- tLambda na N M ⇝ tLambda na N M'

| letin_red_def na b t b' r : Σ ;;; Γ |- b ⇝ r -> Σ ;;; Γ |- tLetIn na b t b' ⇝ tLetIn na r t b'
| letin_red_ty na b t b' r : Σ ;;; Γ |- t ⇝ r -> Σ ;;; Γ |- tLetIn na b t b' ⇝ tLetIn na b r b'
| letin_red_body na b t b' r : Σ ;;; Γ ,, vdef na b t |- b' ⇝ r -> Σ ;;; Γ |- tLetIn na b t b' ⇝ tLetIn na b t r

| case_red_param ci p params' c brs :
    OnOne2 (fun t u => Σ ;;; Γ |- t ⇝ u) p.(pparams) params' ->
    Σ ;;; Γ |- tCase ci p c brs ⇝ tCase ci (set_pparams p params') c brs

| case_red_return ci p preturn' c brs :
  Σ ;;; Γ ,,, inst_case_predicate_context p |- p.(preturn) ⇝ preturn' ->
  Σ ;;; Γ |- tCase ci p c brs ⇝ tCase ci (set_preturn p preturn') c brs

| case_red_discr ci p c c' brs :
  Σ ;;; Γ |- c ⇝ c' -> Σ ;;; Γ |- tCase ci p c brs ⇝ tCase ci p c' brs

| case_red_brs ci p c brs brs' :
    OnOne2 (fun br br' =>
      on_Trel_eq (fun t u => Σ ;;; Γ ,,, inst_case_branch_context p br |- t ⇝ u) bbody bcontext br br')
      brs brs' ->
    Σ ;;; Γ |- tCase ci p c brs ⇝ tCase ci p c brs'

| proj_red p c c' : Σ ;;; Γ |- c ⇝ c' -> Σ ;;; Γ |- tProj p c ⇝ tProj p c'

| app_red_l M1 N1 M2 : Σ ;;; Γ |- M1 ⇝ N1 -> Σ ;;; Γ |- tApp M1 M2 ⇝ tApp N1 M2
| app_red_r M2 N2 M1 : Σ ;;; Γ |- M2 ⇝ N2 -> Σ ;;; Γ |- tApp M1 M2 ⇝ tApp M1 N2

| prod_red_l na M1 M2 N1 : Σ ;;; Γ |- M1 ⇝ N1 -> Σ ;;; Γ |- tProd na M1 M2 ⇝ tProd na N1 M2
| prod_red_r na M2 N2 M1 : Σ ;;; Γ ,, vass na M1 |- M2 ⇝ N2 ->
                           Σ ;;; Γ |- tProd na M1 M2 ⇝ tProd na M1 N2

| evar_red ev l l' : OnOne2 (fun t u => Σ ;;; Γ |- t ⇝ u) l l' -> Σ ;;; Γ |- tEvar ev l ⇝ tEvar ev l'

| fix_red_ty mfix0 mfix1 idx :
    OnOne2 (on_Trel_eq (fun t u => Σ ;;; Γ |- t ⇝ u) dtype (fun x => (dname x, dbody x, rarg x))) mfix0 mfix1 ->
    Σ ;;; Γ |- tFix mfix0 idx ⇝ tFix mfix1 idx

| fix_red_body mfix0 mfix1 idx :
    OnOne2 (on_Trel_eq (fun t u => Σ ;;; Γ ,,, fix_context mfix0 |- t ⇝ u) dbody (fun x => (dname x, dtype x, rarg x)))
           mfix0 mfix1 ->
    Σ ;;; Γ |- tFix mfix0 idx ⇝ tFix mfix1 idx

| cofix_red_ty mfix0 mfix1 idx :
    OnOne2 (on_Trel_eq (fun t u => Σ ;;; Γ |- t ⇝ u) dtype (fun x => (dname x, dbody x, rarg x))) mfix0 mfix1 ->
    Σ ;;; Γ |- tCoFix mfix0 idx ⇝ tCoFix mfix1 idx

| cofix_red_body mfix0 mfix1 idx :
    OnOne2 (on_Trel_eq (fun t u => Σ ;;; Γ ,,, fix_context mfix0 |- t ⇝ u) dbody (fun x => (dname x, dtype x, rarg x))) mfix0 mfix1 ->
    Σ ;;; Γ |- tCoFix mfix0 idx ⇝ tCoFix mfix1 idx
where " Σ ;;; Γ |- t ⇝ u " := (red1 Σ Γ t u).

Lemma red1_ind_all :
  forall (Σ : global_env) (P : context -> term -> term -> Type),

       (forall (Γ : context) (na : aname) (t b a : term),
        P Γ (tApp (tLambda na t b) a) (b {0 := a})) ->

       (forall (Γ : context) (na : aname) (b t b' : term), P Γ (tLetIn na b t b') (b' {0 := b})) ->

       (forall (Γ : context) (i : nat) (body : term),
        option_map decl_body (nth_error Γ i) = Some (Some body) -> P Γ (tRel i) ((lift0 (S i)) body)) ->

       (forall (Γ : context) (ci : case_info) (c : nat) (u : Instance.t) (args : list term)
          (p : predicate term) (brs : list (branch term)) br,
          nth_error brs c = Some br ->
          #|args| = (ci.(ci_npar) + context_assumptions br.(bcontext))%nat ->
          P Γ (tCase ci p (mkApps (tConstruct ci.(ci_ind) c u) args) brs)
              (iota_red ci.(ci_npar) p args br)) ->

       (forall (Γ : context) (mfix : mfixpoint term) (idx : nat) (args : list term) (narg : nat) (fn : term),
        unfold_fix mfix idx = Some (narg, fn) ->
        is_constructor narg args = true -> P Γ (mkApps (tFix mfix idx) args) (mkApps fn args)) ->

       (forall (Γ : context) ci (p : predicate term) (mfix : mfixpoint term) (idx : nat)
          (args : list term) (narg : nat) (fn : term) (brs : list (branch term)),
        unfold_cofix mfix idx = Some (narg, fn) ->
        P Γ (tCase ci p (mkApps (tCoFix mfix idx) args) brs) (tCase ci p (mkApps fn args) brs)) ->

       (forall (Γ : context) (p : projection) (mfix : mfixpoint term) (idx : nat) (args : list term)
          (narg : nat) (fn : term),
        unfold_cofix mfix idx = Some (narg, fn) -> P Γ (tProj p (mkApps (tCoFix mfix idx) args)) (tProj p (mkApps fn args))) ->

       (forall (Γ : context) c (decl : constant_body) (body : term),
        declared_constant Σ c decl ->
        forall u : Instance.t, cst_body decl = Some body -> P Γ (tConst c u) (subst_instance u body)) ->

       (forall (Γ : context) p (args : list term) (u : Instance.t)
         (arg : term),
           nth_error args (p.(proj_npars) + p.(proj_arg)) = Some arg ->
           P Γ (tProj p (mkApps (tConstruct p.(proj_ind) 0 u) args)) arg) ->

       (forall (Γ : context) (na : aname) (M M' N : term),
        red1 Σ Γ M M' -> P Γ M M' -> P Γ (tLambda na M N) (tLambda na M' N)) ->

       (forall (Γ : context) (na : aname) (M M' N : term),
        red1 Σ (Γ,, vass na N) M M' -> P (Γ,, vass na N) M M' -> P Γ (tLambda na N M) (tLambda na N M')) ->

       (forall (Γ : context) (na : aname) (b t b' r : term),
        red1 Σ Γ b r -> P Γ b r -> P Γ (tLetIn na b t b') (tLetIn na r t b')) ->

       (forall (Γ : context) (na : aname) (b t b' r : term),
        red1 Σ Γ t r -> P Γ t r -> P Γ (tLetIn na b t b') (tLetIn na b r b')) ->

       (forall (Γ : context) (na : aname) (b t b' r : term),
        red1 Σ (Γ,, vdef na b t) b' r -> P (Γ,, vdef na b t) b' r -> P Γ (tLetIn na b t b') (tLetIn na b t r)) ->

       (forall (Γ : context) (ci : case_info) p params' c brs,
          OnOne2 (Trel_conj (red1 Σ Γ) (P Γ)) p.(pparams) params' ->
           P Γ (tCase ci p c brs)
               (tCase ci (set_pparams p params') c brs)) ->

       (forall (Γ : context) (ci : case_info) p preturn' c brs,
          red1 Σ (Γ ,,, inst_case_predicate_context p) p.(preturn) preturn' ->
          P (Γ ,,, inst_case_predicate_context p) p.(preturn) preturn' ->
          P Γ (tCase ci p c brs)
              (tCase ci (set_preturn p preturn') c brs)) ->

       (forall (Γ : context) (ind : case_info) (p : predicate term) (c c' : term) (brs : list (branch term)),
        red1 Σ Γ c c' -> P Γ c c' -> P Γ (tCase ind p c brs) (tCase ind p c' brs)) ->

       (forall (Γ : context) ci p c brs brs',
          OnOne2 (fun br br' =>
          (on_Trel_eq (Trel_conj (red1 Σ (Γ ,,, inst_case_branch_context p br))
            (P (Γ ,,, inst_case_branch_context p br)))
            bbody bcontext br br')) brs brs' ->
          P Γ (tCase ci p c brs) (tCase ci p c brs')) ->

       (forall (Γ : context) (p : projection) (c c' : term), red1 Σ Γ c c' -> P Γ c c' ->
                                                             P Γ (tProj p c) (tProj p c')) ->

       (forall (Γ : context) (M1 N1 : term) (M2 : term), red1 Σ Γ M1 N1 -> P Γ M1 N1 ->
                                                         P Γ (tApp M1 M2) (tApp N1 M2)) ->

       (forall (Γ : context) (M2 N2 : term) (M1 : term), red1 Σ Γ M2 N2 -> P Γ M2 N2 ->
                                                         P Γ (tApp M1 M2) (tApp M1 N2)) ->

       (forall (Γ : context) (na : aname) (M1 M2 N1 : term),
        red1 Σ Γ M1 N1 -> P Γ M1 N1 -> P Γ (tProd na M1 M2) (tProd na N1 M2)) ->

       (forall (Γ : context) (na : aname) (M2 N2 M1 : term),
        red1 Σ (Γ,, vass na M1) M2 N2 -> P (Γ,, vass na M1) M2 N2 -> P Γ (tProd na M1 M2) (tProd na M1 N2)) ->

       (forall (Γ : context) (ev : nat) (l l' : list term),
           OnOne2 (Trel_conj (red1 Σ Γ) (P Γ)) l l' -> P Γ (tEvar ev l) (tEvar ev l')) ->

       (forall (Γ : context) (mfix0 mfix1 : list (def term)) (idx : nat),
        OnOne2 (on_Trel_eq (Trel_conj (red1 Σ Γ) (P Γ)) dtype (fun x => (dname x, dbody x, rarg x))) mfix0 mfix1 ->
        P Γ (tFix mfix0 idx) (tFix mfix1 idx)) ->

       (forall (Γ : context) (mfix0 mfix1 : list (def term)) (idx : nat),
        OnOne2 (on_Trel_eq (Trel_conj (red1 Σ (Γ ,,, fix_context mfix0))
                                      (P (Γ ,,, fix_context mfix0))) dbody
                           (fun x => (dname x, dtype x, rarg x))) mfix0 mfix1 ->
        P Γ (tFix mfix0 idx) (tFix mfix1 idx)) ->

       (forall (Γ : context) (mfix0 mfix1 : list (def term)) (idx : nat),
        OnOne2 (on_Trel_eq (Trel_conj (red1 Σ Γ) (P Γ)) dtype (fun x => (dname x, dbody x, rarg x))) mfix0 mfix1 ->
        P Γ (tCoFix mfix0 idx) (tCoFix mfix1 idx)) ->

       (forall (Γ : context) (mfix0 mfix1 : list (def term)) (idx : nat),
        OnOne2 (on_Trel_eq (Trel_conj (red1 Σ (Γ ,,, fix_context mfix0))
                                      (P (Γ ,,, fix_context mfix0))) dbody
                           (fun x => (dname x, dtype x, rarg x))) mfix0 mfix1 ->
        P Γ (tCoFix mfix0 idx) (tCoFix mfix1 idx)) ->

       forall (Γ : context) (t t0 : term), red1 Σ Γ t t0 -> P Γ t t0.
Admitted.

Set Default Goal Selector "!".
Global Instance subst_instance_def {A} `(UnivSubst A) : UnivSubst (def A).
exact (fun u => map_def (subst_instance u) (subst_instance u)).
Defined.
Global Instance subst_instance_predicate : UnivSubst (predicate term).
exact (fun u => map_predicate (subst_instance u) (subst_instance u) (subst_instance u) id).
Defined.

Lemma fix_subst_instance_subst u mfix :
  subst_instance u (fix_subst mfix) = fix_subst (subst_instance u mfix).
Admitted.

Lemma iota_red_subst_instance pars p args br u :
  subst_instance u (iota_red pars p args br)
  = iota_red pars (subst_instance u p) (List.map (subst_instance u) args) (map_branch (subst_instance u) id br).
Admitted.

Lemma red1_subst_instance Σ Γ u s t :
  red1 Σ Γ s t ->
  red1 Σ (subst_instance u Γ)
       (subst_instance u s) (subst_instance u t).
Proof.
  intros X0.
pose proof I as X.
  intros.
induction X0 using red1_ind_all.
  all: try (cbn; econstructor; eauto; fail).
  -
 cbn.
rewrite subst_instance_subst.
econstructor.
  -
 cbn.
rewrite subst_instance_subst.
econstructor.
  -
 cbn.
rewrite subst_instance_lift.
econstructor.
    unfold subst_instance.
    unfold option_map in *.
destruct (nth_error Γ) eqn:E; inversion H.
    unfold map_context.
rewrite nth_error_map E.
cbn.
    rewrite map_decl_body.
destruct c.
cbn in H1.
subst.
    reflexivity.
  -
 cbn.
rewrite subst_instance_mkApps.
cbn.
    rewrite iota_red_subst_instance.
    change (bcontext br) with (bcotext (map_branch (subst_instance u) br)).
    eapply red_iota; eauto with pcuic.
    *
 rewrite nth_error_map H //.
    *
 simpl.
now len.
  -
 cbn.
rewrite !subst_instance_mkApps.
cbn.
    econstructor.
    +
 unfold unfold_fix in *.
destruct (nth_error mfix idx) eqn:E.
      *
 inversion H.
        rewrite nth_error_map E.
cbn.
        destruct d.
cbn in *.
cbn in *; try congruence.
        f_equal.
f_equal.
        now rewrite subst_instance_subst fix_subst_instance_subst.
