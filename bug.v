(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "-notation-overridden" "-w" "-extraction-reserved-identifier" "-w" "-extraction-opaque-accessed" "-w" "-ambiguous-paths" "-w" "-duplicate-clear" "-w" "-deprecated-hint-without-locality" "-w" "-deprecated-hint-rewrite-without-locality" "-w" "-deprecated-instance-without-locality" "-w" "-deprecated-native-compiler-option" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/jasmin/proofs/3rdparty" "Jasmin" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/jasmin/proofs/arch" "Jasmin" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/jasmin/proofs/compiler" "Jasmin" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/jasmin/proofs/lang" "Jasmin" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/jasmin/proofs/ssrmisc" "Jasmin" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/CoqWord" "CoqWord" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/mathcomp" "mathcomp" "-top" "bug_01" "-native-compiler" "no") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 1590 lines to 15 lines, then from 28 lines to 275 lines, then from 274 lines to 85 lines, then from 98 lines to 516 lines, then from 515 lines to 136 lines, then from 149 lines to 605 lines, then from 600 lines to 147 lines, then from 160 lines to 334 lines, then from 339 lines to 179 lines, then from 192 lines to 323 lines, then from 328 lines to 183 lines, then from 196 lines to 367 lines, then from 372 lines to 193 lines, then from 206 lines to 1355 lines, then from 1360 lines to 308 lines, then from 321 lines to 470 lines, then from 473 lines to 310 lines, then from 323 lines to 627 lines, then from 632 lines to 362 lines, then from 375 lines to 1134 lines, then from 1137 lines to 411 lines, then from 424 lines to 561 lines, then from 566 lines to 420 lines, then from 433 lines to 1085 lines, then from 1090 lines to 983 lines, then from 982 lines to 467 lines, then from 480 lines to 828 lines, then from 833 lines to 468 lines, then from 481 lines to 1346 lines, then from 1351 lines to 496 lines, then from 509 lines to 2216 lines, then from 2221 lines to 511 lines, then from 524 lines to 1185 lines, then from 1190 lines to 543 lines, then from 557 lines to 666 lines, then from 670 lines to 553 lines, then from 567 lines to 956 lines, then from 959 lines to 890 lines, then from 881 lines to 588 lines, then from 601 lines to 879 lines, then from 883 lines to 644 lines, then from 658 lines to 914 lines, then from 919 lines to 651 lines, then from 665 lines to 1518 lines, then from 1522 lines to 758 lines, then from 772 lines to 2450 lines, then from 2455 lines to 1178 lines *)
(* coqc version 8.17+alpha compiled with OCaml 4.14.0
   coqtop version runner-j2nyww-s-project-6138686-concurrent-0:/builds/coq/coq/_build/default,(HEAD detached at 3721187) (3721187d6f240344abae25acb1ace86ff72c88c2)
   Modules that could not be inlined: CoqWord.word
   Expected coqc runtime on this file: 3.068 sec *)
Require Coq.FSets.FMaps.
Require Coq.FSets.FMapAVL.
Require Coq.FSets.FSetAVL.
Require Coq.ssr.ssreflect.
Require mathcomp.ssreflect.ssreflect.
Require Coq.ssr.ssrfun.
Require mathcomp.ssreflect.ssrnotations.
Require mathcomp.ssreflect.ssrfun.
Require Coq.ssr.ssrbool.
Require mathcomp.ssreflect.ssrbool.
Require mathcomp.ssreflect.eqtype.
Require Coq.NArith.BinNat.
Require Coq.PArith.BinPos.
Require Coq.NArith.Ndec.
Require Coq.setoid_ring.Ring.
Require mathcomp.ssreflect.ssrnat.
Require mathcomp.ssreflect.seq.
Require mathcomp.ssreflect.choice.
Require mathcomp.ssreflect.path.
Require mathcomp.ssreflect.div.
Require mathcomp.ssreflect.fintype.
Require mathcomp.ssreflect.fingraph.
Require mathcomp.ssreflect.tuple.
Require mathcomp.ssreflect.finfun.
Require mathcomp.ssreflect.bigop.
Require mathcomp.ssreflect.prime.
Require mathcomp.ssreflect.finset.
Require mathcomp.ssreflect.order.
Require mathcomp.ssreflect.binomial.
Require mathcomp.ssreflect.generic_quotient.
Require mathcomp.ssreflect.ssrAC.
Require mathcomp.ssreflect.all_ssreflect.
Require Coq.Unicode.Utf8.
Require Coq.ZArith.ZArith.
Require Coq.Setoids.Setoid.
Require Coq.Classes.Morphisms.
Require Coq.Classes.CMorphisms.
Require Coq.Classes.CRelationClasses.
Require Jasmin.xseq.
Require Jasmin.oseq.
Require Coq.micromega.Psatz.
Require mathcomp.algebra.ssralg.
Require mathcomp.fingroup.fingroup.
Require mathcomp.algebra.ring_quotient.
Require mathcomp.algebra.countalg.
Require mathcomp.algebra.poly.
Require mathcomp.algebra.ssrnum.
Require mathcomp.fingroup.morphism.
Require mathcomp.fingroup.perm.
Require mathcomp.fingroup.automorphism.
Require mathcomp.fingroup.quotient.
Require mathcomp.fingroup.action.
Require mathcomp.algebra.finalg.
Require mathcomp.algebra.polydiv.
Require mathcomp.algebra.zmodp.
Require mathcomp.algebra.matrix.
Require mathcomp.algebra.mxalgebra.
Require mathcomp.algebra.mxpoly.
Require mathcomp.algebra.polyXY.
Require mathcomp.algebra.ssrint.
Require Coq.setoid_ring.Field_theory.
Require Coq.setoid_ring.Field_tac.
Require mathcomp.algebra.rat.
Require mathcomp.algebra.vector.
Require mathcomp.algebra.intdiv.
Require mathcomp.algebra.interval.
Require mathcomp.algebra.fraction.
Require mathcomp.algebra.all_algebra.
Require Coq.Arith.Arith.
Require CoqWord.ssrZ.
Require CoqWord.word.

Declare ML Module "coq-core.plugins.ltac".
Module Export AdmitTactic.
Module Import LocalFalse.
Inductive False : Prop := .
End LocalFalse.
Axiom proof_admitted : False.
Global Set Default Proof Mode "Classic".
Tactic Notation "admit" := abstract case proof_admitted.
End AdmitTactic.

Module Export Jasmin_DOT_utils_WRAPPED.
Module Export utils.
 
Import mathcomp.ssreflect.all_ssreflect.
Import Coq.Unicode.Utf8.
Import Coq.ZArith.ZArith.
Import Coq.Setoids.Setoid.
Import Coq.Classes.Morphisms.
Import Coq.Classes.CMorphisms.
Import Coq.Classes.CRelationClasses.
Import Jasmin.xseq.
Import Jasmin.oseq.
Import CoqWord.ssrZ.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope Z_scope.

 
Module Export FinIsCount.
Section FinIsCount.
Variable (T : eqType) (enum : seq T) (A : Finite.axiom enum).

Definition pickle (x : T) :=
  seq.index x enum.

Definition unpickle (n : nat) :=
  nth None [seq some x | x <- enum] n.

Definition pickleK : pcancel pickle unpickle.
Admitted.
End FinIsCount.
End FinIsCount.

Class eqTypeC (T:Type) :=
  { beq : T -> T -> bool
  ; ceqP: Equality.axiom beq }.

Section EqType.

Context {T:Type} {ceqT : eqTypeC T}.
Definition ceqT_eqMixin := Equality.Mixin ceqP.
Definition ceqT_eqType  := Eval hnf in EqType T ceqT_eqMixin.

End EqType.

Notation "x == y ::> T" := (eq_op (T:= @ceqT_eqType T _) x y)
  (at level 70, y at next level) : bool_scope.

Notation "x == y ::>" := (eq_op (T:= @ceqT_eqType _ _) x y)
  (at level 70, y at next level) : bool_scope.

Class finTypeC (T:Type) :=
  { _eqC   :> eqTypeC T
  ; cenum  : seq T
  ; cenumP : @Finite.axiom ceqT_eqType cenum
  }.

Section FinType.

Context `{cfinT:finTypeC}.

Definition cfinT_choiceMixin :=
  PcanChoiceMixin (FinIsCount.pickleK cenumP).
Definition cfinT_choiceType :=
  Eval hnf in ChoiceType ceqT_eqType cfinT_choiceMixin.

Definition cfinT_countMixin :=
  PcanCountMixin (FinIsCount.pickleK cenumP).
Definition cfinT_countType :=
  Eval hnf in @Countable.pack T cfinT_countMixin cfinT_choiceType _ (fun x => x).

Definition cfinT_finMixin :=
  @Finite.EnumMixin cfinT_countType _ cenumP.
Definition cfinT_finType :=
  Eval hnf in
    (@Finite.pack T ceqT_eqMixin cfinT_finMixin cfinT_choiceType _ (fun x => x) _ (fun x => x)).

Lemma mem_cenum : cenum =i ceqT_eqType.
Admitted.

End FinType.

Module FinMap.

Section Section.

Context `{cfinT:finTypeC} (U:Type).

 

Definition map := @finfun_of cfinT_finType (fun _ => U) (Phant _).

Definition of_fun :=
  @FinfunDef.finfun cfinT_finType (fun _ => U).
Definition set (m:map) (x: T) (y:U) : map. exact (of_fun (fun z : T => if z == x ::> then y else m z)). Defined.

End Section.

End FinMap.

 
Lemma reflect_inj (T:eqType) (U:Type) (f:T -> U) a b :
  injective f -> reflect (a = b) (a == b) -> reflect (f a = f b) (a == b).
Admitted.

 
 

Instance and3_impl_morphism :
  Proper (Basics.impl ==> Basics.impl ==> Basics.impl ==> Basics.impl) and3 | 1.
Admitted.

Instance and3_iff_morphism :
  Proper (iff ==> iff ==> iff ==> iff) and3.
Admitted.

Instance and4_impl_morphism :
  Proper (Basics.impl ==> Basics.impl ==> Basics.impl ==> Basics.impl ==> Basics.impl) and4 | 1.
Admitted.

Instance and4_iff_morphism :
  Proper (iff ==> iff ==> iff ==> iff ==> iff) and4.
Admitted.

Instance and5_impl_morphism :
  Proper (Basics.impl ==> Basics.impl ==> Basics.impl ==> Basics.impl ==> Basics.impl ==> Basics.impl) and5 | 1.
Admitted.

Instance and5_iff_morphism :
  Proper (iff ==> iff ==> iff ==> iff ==> iff ==> iff) and5.
Admitted.

 

Variant result (E : Type) (A : Type) : Type :=
| Ok of A
| Error of E.

Arguments Error {E} {A} s.

Definition is_ok (E A:Type) (r:result E A) := if r is Ok a then true else false.

Lemma is_ok_ok (E A:Type) (a:A) : is_ok (Ok E a).
Admitted.
Hint Resolve is_ok_ok : core.

Lemma is_okP (E A:Type) (r:result E A) : reflect (exists (a:A), r = Ok E a) (is_ok r).
Admitted.

Section ResultEqType.

Variable E A : eqType.
Definition result_eq (r1 r2: result E A): bool. exact (match r1, r2 with
  | Ok a1, Ok a2 => a1 == a2
  | Error e1, Error e2 => e1 == e2
  | _, _ => false
  end). Defined.

Lemma result_eqP : Equality.axiom result_eq.
Admitted.

End ResultEqType.

Module Result.

Definition bind eT aT rT (f : aT -> result eT rT) g :=
  match g with
  | Ok x    => f x
  | Error s => Error s
  end.

End Result.
Notation rbind := Result.bind.
Notation ok    := (@Ok _).

Notation "m >>= f" := (rbind f m) (at level 25, left associativity).
Notation "'Let' x ':=' m 'in' body" := (m >>= (fun x => body)) (x name, at level 25).

Variant error :=
 | ErrOob | ErrAddrUndef | ErrAddrInvalid | ErrStack | ErrType.

Definition exec t := result error t.

Definition type_error {t} := @Error _ t ErrType.

Section FOLDM.

End FOLDM.

Section FOLD2.

End FOLD2.

 
 
Section ALLM.

End ALLM.

Section MAP2.

End MAP2.

Section Subseq.

End Subseq.

Section All2.

Section DifferentTypes.

  Section Ind.

  End Ind.

End DifferentTypes.

Section SameType.

  Section AnyRelation.

  End AnyRelation.

  Section Eqb.

  End Eqb.

End SameType.

End All2.

Section Map2.

End Map2.

Section Map3.

End Map3.

Section MAPI.

End MAPI.

Section FIND_MAP.

Section DEF.

End DEF.

End FIND_MAP.

 
 
 

Section CTRANS.

  Definition ctrans c1 c2 := nosimpl (
    match c1, c2 with
    | Eq, _  => Some c2
    | _ , Eq => Some c1
    | Lt, Lt => Some Lt
    | Gt, Gt => Some Gt
    | _ , _  => None
    end).

End CTRANS.

 

Scheme Equality for comparison.

Lemma comparison_beqP : Equality.axiom comparison_beq.
Admitted.

Canonical comparison_eqMixin := EqMixin comparison_beqP.
Canonical comparison_eqType := Eval hnf in EqType comparison comparison_eqMixin.

 

Class Cmp {T:Type} (cmp:T -> T -> comparison) := {
    cmp_sym    : forall x y, cmp x y = CompOpp (cmp y x);
    cmp_ctrans : forall y x z c, ctrans (cmp x y) (cmp y z) = Some c -> cmp x z = c;
    cmp_eq     : forall {x y}, cmp x y = Eq -> x = y;
  }.

Definition gcmp {T:Type} {cmp:T -> T -> comparison} {C:Cmp cmp} := cmp.

Section CMP.

  Context {T:Type} {cmp:T -> T -> comparison} {C:Cmp cmp}.

  Definition cmp_le x1 x2 := gcmp x2 x1 != Lt.

End CMP.
Notation "m <= n" := (cmp_le m n) : cmp_scope.
Delimit Scope cmp_scope with CMP.

Section EqCMP.

End EqCMP.

Section LEX.

End LEX.

Section MIN.

End MIN.

Coercion Zpos : positive >-> Z.

Lemma pos_eqP : Equality.axiom Pos.eqb.
Admitted.

Definition pos_eqMixin := EqMixin pos_eqP.
Canonical  pos_eqType  := EqType positive pos_eqMixin.

 
Definition funname := positive.

Definition get_fundef {T} (p: seq (funname * T)) (f: funname) :=
  assoc p f.

 

Definition lprod ts tr :=
  foldr (fun t tr => t -> tr) tr ts.

Fixpoint ltuple (ts:list Type) : Type :=
  match ts with
  | [::]   => unit
  | [::t1] => t1
  | t1::ts => t1 * ltuple ts
  end.

End utils.
Module Export Jasmin.
Module Export utils.
Include Jasmin_DOT_utils_WRAPPED.utils.
End utils.
Import Coq.FSets.FMaps.
Import mathcomp.ssreflect.all_ssreflect.

Module Type CmpType.

  Parameter t : eqType.

  Parameter cmp : t -> t -> comparison.

End CmpType.

Module MkOrdT (T:CmpType) <: OrderedType.

  Definition t := Equality.sort T.t.

  Definition eq x y := T.cmp x y = Eq.
  Definition lt x y := T.cmp x y = Lt.

  Lemma eq_refl x: eq x x.
Admitted.

  Lemma eq_sym x y: eq x y -> eq y x.
Admitted.

  Lemma eq_trans x y z: eq x y -> eq y z -> eq x z.
Admitted.

  Lemma lt_trans x y z: lt x y -> lt y z -> lt x z.
Admitted.

  Lemma lt_not_eq x y: lt x y -> ~ eq x y.
Admitted.
Definition compare x y : Compare lt eq x y.
Admitted.

  Definition eq_dec x y: {eq x y} + {~ eq x y}.
Admitted.

End MkOrdT.

Module Type CompuEqDec.

  Parameter t: eqType.

End CompuEqDec.

Module Type MAP.

End MAP.

Module Mmake (K':CmpType) <: MAP.

  Module K := K'.

  Module Ordered := MkOrdT K.

  Module Map := FMapAVL.Make Ordered.

  Definition t (T:Type) := Map.t T.

  End Mmake.

Module DMmake (K:CmpType) (E:CompuEqDec with Definition t := K.t).

End DMmake.

Import Coq.ZArith.ZArith.

Import CoqWord.ssrZ.
Module Export CmpZ.

  Definition t := [eqType of Z].
Definition cmp : t -> t -> comparison.
Admitted.

End CmpZ.

Module Mz := Mmake CmpZ.

Module MkMOrdT (T:CmpType) <: Orders.OrderedType.

  Definition t := Equality.sort T.t.

  Definition eq := @Logic.eq t.

  Lemma eq_equiv : Equivalence eq.
Admitted.

  Definition lt x y := T.cmp x y = Lt.

  Lemma lt_strorder : StrictOrder lt.
Admitted.

  Lemma lt_compat : Proper (eq ==> eq ==> iff) lt.
Admitted.
Definition compare : t -> t -> comparison.
Admitted.

  Lemma compare_spec :
     forall x y : t, CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
Admitted.

  Lemma eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
Admitted.

End MkMOrdT.

Module Smake (T:CmpType).
  Module Ordered := MkMOrdT T.
  Include (MSetAVL.Make Ordered).
End Smake.
Export Coq.Strings.String.

Scheme Equality for String.string.

Lemma string_eqP : Equality.axiom string_beq.
Admitted.

Definition string_eqMixin := EqMixin string_eqP.
Canonical  string_eqType  := EqType string string_eqMixin.

Module Export Jasmin_DOT_wsize_WRAPPED.
Module Export wsize.
Import Jasmin.utils.

Variant wsize :=
  | U8
  | U16
  | U32
  | U64
  | U128
  | U256.

Variant velem := VE8 | VE16 | VE32 | VE64.

Variant pelem :=
| PE1 | PE2 | PE4 | PE8 | PE16 | PE32 | PE64 | PE128.

Variant signedness :=
  | Signed
  | Unsigned.

Definition wsize_cmp s s' :=
  match s, s' with
  | U8, U8 => Eq
  | U8, (U16 | U32 | U64 | U128 | U256)  => Lt
  | U16, U8 => Gt
  | U16, U16 => Eq
  | U16, (U32 | U64 | U128 | U256) => Lt
  | U32, (U8 | U16) => Gt
  | U32, U32 => Eq
  | U32, (U64 | U128 | U256) => Lt
  | U64, (U8 | U16 | U32) => Gt
  | U64, U64 => Eq
  | U64, ( U128 | U256) => Lt
  | U128, (U8 | U16 | U32 | U64) => Gt
  | U128, U128 => Eq
  | U128, U256 => Lt
  | U256, (U8 | U16 | U32 | U64 | U128) => Gt
  | U256, U256 => Eq
  end.

#[export]
Instance wsizeO : Cmp wsize_cmp.
Admitted.

Variant safe_cond :=
  | NotZero of wsize & nat
  | AllInit of wsize & positive & nat.

End wsize.
Module Export Jasmin.
Module Export wsize.
Include Jasmin_DOT_wsize_WRAPPED.wsize.
End wsize.

Variant stype : Set :=
| sbool
| sint
| sarr  of positive
| sword of wsize.

Notation sword8   := (sword U8).

Scheme Equality for stype.

Lemma stype_axiom : Equality.axiom stype_beq.
Admitted.

Definition stype_eqMixin     := Equality.Mixin stype_axiom.
Canonical  stype_eqType      := Eval hnf in EqType stype stype_eqMixin.

Definition is_sword t := if t is sword _ then true else false.

Definition is_sarr t := if t is sarr _ then true else false.

Definition vundef_type (t:stype) :=
  match t with
  | sword _ => sword8
  | sarr _  => sarr 1
  | _       => t
  end.

Definition compat_type t1 t2 :=
  match t1 with
  | sint    => t2 == sint
  | sbool   => t2 == sbool
  | sword _ => is_sword t2
  | sarr _  => is_sarr t2
  end.

Module Type IDENT.

  Parameter ident : eqType.

End IDENT.

Module Ident <: IDENT.

  Definition ident := [eqType of string].

End Ident.

Set Implicit Arguments.
Unset Strict Implicit.

Module MvMake (I:IDENT).
Import I.

  Record var := Var { vtype : stype; vname : ident }.

  Definition var_beq (v1 v2:var) :=
    let (t1,n1) := v1 in
    let (t2,n2) := v2 in
    (t1 == t2) && (n1 == n2).

  Lemma var_eqP : Equality.axiom var_beq.
Admitted.

  Definition var_eqMixin := EqMixin var_eqP.
  Canonical  var_eqType  := EqType var var_eqMixin.

  End MvMake.

Module Var := MvMake Ident.
Export Var.

Module Export CmpVar.

  Definition t := [eqType of var].
Definition cmp : t -> t -> comparison.
Admitted.

End CmpVar.

Module Sv := Smake CmpVar.
Import mathcomp.algebra.all_algebra.
Import CoqWord.word.
Export Jasmin.wsize.
Definition wsize_size_minus_1 (s: wsize) : nat.
Admitted.
Definition wsize_size (sz: wsize) : Z.
Admitted.

Definition word := fun sz =>
  [comRingType of (wsize_size_minus_1 sz).+1.-word].

Notation u8   := (word U8).
Definition zero_extend sz sz' (w: word sz') : word sz.
Admitted.

Definition word_uincl sz1 sz2 (w1:word sz1) (w2:word sz2) :=
  (sz1 <= sz2)%CMP && (w1 == zero_extend sz1 w2).

Local Open Scope Z_scope.

Section POINTER.

Context (pointer: eqType).

Class pointer_op (pointer: eqType) : Type := PointerOp {

  add : pointer -> Z -> pointer;
  sub : pointer -> pointer -> Z;
  p_to_z : pointer -> Z;

  add_sub : forall p k, add p (sub k p) = k;
  sub_add : forall p k, 0 <= k < wsize_size U256 -> sub (add p k) p = k;
  add_0   : forall p, add p 0 = p;

}.

Class coreMem (core_mem: Type) := CoreMem {
  get : core_mem -> pointer -> exec u8;
  set : core_mem -> pointer -> u8 -> exec core_mem;
  valid8 : core_mem -> pointer -> bool;
  setP :
    forall m p w p' m',
      set m p w = ok m' ->
      get m' p' = if p == p' then ok w else get m p';
  valid8P : forall m p w, reflect (exists m', set m p w = ok m') (valid8 m p);
  get_valid8 : forall m p w, get m p = ok w -> valid8 m p;
  valid8_set : forall m p w m' p', set m p w = ok m' -> valid8 m' p' = valid8 m p';
}.

End POINTER.
Section CoreMem.

  Context {pointer: eqType} {Pointer: pointer_op pointer}.
  Context {core_mem: Type} {CM: coreMem pointer core_mem}.
Definition read (m: core_mem) (ptr: pointer) (sz: wsize) : exec (word sz).
Admitted.

End CoreMem.
Import Coq.Unicode.Utf8.

Variant arr_access :=
  | AAdirect
  | AAscale.

Module Export WArray.

  Record array (s:positive)  :=
    { arr_data : Mz.t u8 }.

  Local Notation pointer := [eqType of Z].

  Instance PointerZ : pointer_op pointer | 1.
Admitted.

  Section WITH_POINTER_DATA.

  Section CM.
    Variable (s:positive).
Global Instance array_CM : coreMem pointer (array s).
Admitted.

  End CM.

  Definition uincl {len1 len2} (a1 : array len1) (a2 : array len2) :=
    (len1 <= len2)%Z /\
    ∀ i w, read a1 i U8 = ok w -> read a2 i U8 = ok w.

  End WITH_POINTER_DATA.
Definition sem_t (t : stype) : Type.
Admitted.

Definition sem_prod ts tr := lprod (map sem_t ts) tr.
Definition sem_ot (t:stype) : Type.
Admitted.

Definition sem_tuple ts := ltuple (map sem_ot ts).

Variant value : Type :=
  | Vbool  :> bool -> value
  | Vint   :> Z    -> value
  | Varr   : forall len, WArray.array len -> value
  | Vword  : forall s, word s -> value
  | Vundef : forall (t:stype), is_sarr t = false -> value.

Definition values := seq value.

Definition type_of_val v :=
  match v with
  | Vbool _ => sbool
  | Vint  _ => sint
  | Varr n _ => sarr n
  | Vword s _ => sword s
  | Vundef t _ => vundef_type t
  end.

Definition value_uincl (v1 v2:value) :=
  match v1, v2 with
  | Vbool b1, Vbool b2 => b1 = b2
  | Vint n1, Vint n2   => n1 = n2
  | Varr n1 t1, Varr n2 t2 => WArray.uincl t1 t2
  | Vword sz1 w1, Vword sz2 w2 => word_uincl w1 w2
  | Vundef t _, _ => compat_type t (type_of_val v2)
  | _, _ => False
  end.
Definition of_val t : value -> exec (sem_t t).
Admitted.
Fixpoint list_ltuple (ts:list stype) : sem_tuple ts -> values.
Admitted.

Fixpoint app_sopn T ts : sem_prod ts (exec T) → values → exec T :=
  match ts return sem_prod ts (exec T) → values → exec T with
  | [::] => λ (o : exec T) (vs: values), if vs is [::] then o else type_error
  | t :: ts => λ (o: sem_t t → sem_prod ts (exec T)) (vs: values),
    if vs is v :: vs
    then Let v := of_val t v in app_sopn (o v) vs
    else type_error
  end.

Arguments app_sopn {T} ts _ _.

Definition app_sopn_v tin tout (semi: sem_prod tin (exec (sem_tuple tout))) vs :=
  Let t := app_sopn _ semi vs in
  ok (list_ltuple t).

Variant implicit_arg : Type :=
  | IArflag of var
  | IAreg   of var
  .

Variant arg_desc :=
| ADImplicit  of implicit_arg
| ADExplicit  of nat & option var.

Record instruction_desc := mkInstruction {
  str      : unit -> string;
  tin      : list stype;
  i_in     : seq arg_desc;
  tout     : list stype;
  i_out    : seq arg_desc;
  semi     : sem_prod tin (exec (sem_tuple tout));
  semu     : forall vs vs' v,
                List.Forall2 value_uincl vs vs' ->
                app_sopn_v semi vs = ok v ->
                exists2 v', app_sopn_v semi vs' = ok v' & List.Forall2 value_uincl v v';
  wsizei   : wsize;
  i_safe   : seq safe_cond;
}.

Variant prim_constructor (asm_op:Type) :=
  | PrimP of wsize & (option wsize -> wsize -> asm_op)
  | PrimM of (option wsize -> asm_op)
  | PrimV of (option wsize -> signedness -> velem -> wsize -> asm_op)
  | PrimX of (option wsize -> wsize -> wsize -> asm_op)
  | PrimVV of (option wsize -> velem -> wsize -> velem -> wsize -> asm_op)
  .

Class asmOp (asm_op : Type) := {
  _eqT           :> eqTypeC asm_op
  ; asm_op_instr : asm_op -> instruction_desc
  ; prim_string   : list (string * prim_constructor asm_op)
}.

Definition asm_op_t {asm_op} {asmop : asmOp asm_op} := asm_op.

Section ASM_OP.
Context `{asmop : asmOp}.

Variant sopn :=
| Ocopy     of wsize & positive
| Onop
| Omulu     of wsize
| Oaddcarry of wsize
| Osubcarry of wsize
| Oasm      of asm_op_t.

End ASM_OP.

Variant syscall_t : Type :=
  | RandomBytes of positive.

Variant cmp_kind :=
  | Cmp_int
  | Cmp_w of signedness & wsize.

Variant op_kind :=
  | Op_int
  | Op_w of wsize.

Variant sop1 :=
| Oword_of_int of wsize
| Oint_of_word of wsize
| Osignext of wsize & wsize
| Ozeroext of wsize & wsize
| Onot
| Olnot of wsize
| Oneg  of op_kind
.

Variant sop2 :=
| Obeq
| Oand
| Oor

| Oadd  of op_kind
| Omul  of op_kind
| Osub  of op_kind
| Odiv  of cmp_kind
| Omod  of cmp_kind

| Oland of wsize
| Olor  of wsize
| Olxor of wsize
| Olsr  of wsize
| Olsl  of op_kind
| Oasr  of op_kind

| Oeq   of op_kind
| Oneq  of op_kind
| Olt   of cmp_kind
| Ole   of cmp_kind
| Ogt   of cmp_kind
| Oge   of cmp_kind

| Ovadd of velem & wsize
| Ovsub of velem & wsize
| Ovmul of velem & wsize
| Ovlsr of velem & wsize
| Ovlsl of velem & wsize
| Ovasr of velem & wsize
.

Variant combine_flags :=
| CF_LT    of signedness
| CF_LE    of signedness
| CF_EQ
| CF_NEQ
| CF_GE    of signedness
| CF_GT    of signedness
.

Variant opN :=
| Opack of wsize & pelem
| Ocombine_flags of combine_flags
.

Definition var_info := positive.

Record var_i := VarI {
  v_var :> var;
  v_info : var_info
}.

Variant v_scope :=
  | Slocal
  | Sglob.

Record gvar := Gvar { gv : var_i; gs : v_scope }.

Inductive pexpr : Type :=
| Pconst :> Z -> pexpr
| Pbool  :> bool -> pexpr
| Parr_init : positive → pexpr
| Pvar   :> gvar -> pexpr
| Pget   : arr_access -> wsize -> gvar -> pexpr -> pexpr
| Psub   : arr_access -> wsize -> positive -> gvar -> pexpr -> pexpr
| Pload  : wsize -> var_i -> pexpr -> pexpr
| Papp1  : sop1 -> pexpr -> pexpr
| Papp2  : sop2 -> pexpr -> pexpr -> pexpr
| PappN of opN & seq pexpr
| Pif    : stype -> pexpr -> pexpr -> pexpr -> pexpr.

Notation pexprs := (seq pexpr).

Variant lval : Type :=
| Lnone `(var_info) `(stype)
| Lvar  `(var_i)
| Lmem  `(wsize) `(var_i) `(pexpr)
| Laset `(arr_access) `(wsize) `(var_i) `(pexpr)
| Lasub `(arr_access) `(wsize) `(positive) `(var_i) `(pexpr).

Notation lvals := (seq lval).

Definition instr_info := positive.

Section ASM_OP.

Definition fun_info := positive.

End ASM_OP.

Module Export one_varmap.

Record ovm_syscall_sig_t :=
  { scs_vin : seq var; scs_vout : seq var }.

Class one_varmap_info := {
  syscall_sig  : syscall_t -> ovm_syscall_sig_t;
  all_vars     : Sv.t;
  callee_saved : Sv.t;
  vflags       : Sv.t;
  vflagsP      : forall x, Sv.In x vflags -> vtype x = sbool
}.

Definition label := positive.

Definition remote_label := (funname * label)%type.

Section ASM_OP.

Context `{asmop:asmOp}.

Variant linstr_r :=
  | Lopn   : lvals -> sopn -> pexprs -> linstr_r
  | Lsyscall : syscall_t -> linstr_r
  | Lalign : linstr_r
  | Llabel : label -> linstr_r
  | Lgoto  : remote_label -> linstr_r
  | Ligoto : pexpr -> linstr_r
  | LstoreLabel : var -> label -> linstr_r
  | Lcond  : pexpr -> label -> linstr_r
.

Record linstr : Type := MkLI { li_ii : instr_info; li_i : linstr_r }.

Definition lcmd := seq linstr.

Record lfundef := LFundef {
 lfd_info : fun_info;
 lfd_align : wsize;
 lfd_tyin : seq stype;
 lfd_arg  : seq var_i;
 lfd_body : lcmd;
 lfd_tyout : seq stype;
 lfd_res  : seq var_i;
 lfd_export: bool;
 lfd_callee_saved: seq var;
 lfd_total_stack: Z;
}.

End ASM_OP.

Section PairFoldLeft.

  Variables (T R : Type) (f : R -> T → T → R).

  Fixpoint pairfoldl z t s :=
    if s is x :: s'
    then pairfoldl (f z t x) x s'
    else z.

End PairFoldLeft.

Module Type EqType.

  Parameter T : eqType.

End EqType.

Module Type UnionFind.

End UnionFind.

Module NaiveUnionFind(E : EqType) <: UnionFind.
Definition S : eqType.
exact (E.T).
Defined.

  Definition unionfind_r := seq (S * S).

  Definition is_labeled (T : Type) (l : S) (pl : S * T) := (l == pl.1).

  Definition is_pair (T : eqType) (pl1 pl2 : S * T) := (pl1.1 == pl2.1) && (pl1.2 == pl2.2).

  Definition find_r (uf : unionfind_r) (l : S) :=
    (nth (l,l) uf (seq.find (is_labeled l) uf)).2.

  Definition well_formed (uf : unionfind_r) :=
    uniq (map (fun pl => pl.1) uf) /\
    forall l : S , has (is_labeled l) uf -> has (is_pair (find_r uf l, find_r uf l)) uf.

  Record unionfind_i : Type := mkUF {
    uf :> seq (S * S); _ : well_formed uf;
  }.

  Definition unionfind := unionfind_i.
Definition empty : unionfind.
Admitted.
Definition union (uf : unionfind) (x y : S) : unionfind.
Admitted.

  Definition find (uf : unionfind) (x : S) :=
    find_r uf x.

End NaiveUnionFind.

Module LblEqType <: EqType.
  Definition T := [eqType of label].
End LblEqType.

Module LUF := NaiveUnionFind(LblEqType).

Section ASM_OP.
Context `{asmop : asmOp}.

Section LprogSem.

  Definition setfb fd fb : lfundef :=
    LFundef
      fd.(lfd_info)
      fd.(lfd_align)
      fd.(lfd_tyin)
      fd.(lfd_arg)
      fb
      fd.(lfd_tyout)
      fd.(lfd_res)
      fd.(lfd_export)
      fd.(lfd_callee_saved)
      fd.(lfd_total_stack)
  .

End LprogSem.

Section Tunneling.

  Definition Linstr_align := (MkLI xH Lalign).

  Definition tunnel_chart fn uf c c' :=
    match c, c' with
    | {| li_i := Llabel l |}, {| li_i := Llabel l' |} =>
        LUF.union uf l l'
    | {| li_i := Llabel l |}, {| li_i := Lgoto (fn',l') |} =>
        if fn == fn' then LUF.union uf l l' else uf
    | _, _ => uf
    end.

  Definition tunnel_plan fn uf (lc : lcmd) :=
    pairfoldl (tunnel_chart fn) uf Linstr_align lc.

  Definition tunnel_bore fn uf c :=
    match c with
      | MkLI ii li =>
        match li with
          | Lgoto (fn',l') => MkLI ii (if fn == fn' then Lgoto (fn', LUF.find uf l') else Lgoto (fn',l'))
          | Lcond pe l' => MkLI ii (Lcond pe (LUF.find uf l'))
          | _ => MkLI ii li
        end
    end.

  Definition tunnel_head fn uf lc :=
    map (tunnel_bore fn uf) lc.

  Definition tunnel_engine fn (lc lc' : lcmd) : lcmd :=
    tunnel_head fn (tunnel_plan fn LUF.empty lc) lc'.

  Definition tunnel_lcmd fn lc :=
    tunnel_engine fn lc lc.

  Definition tunnel_lfundef fn fd :=
    setfb fd (tunnel_lcmd fn (lfd_body fd)).

  Definition tunnel_funcs :=
    map (fun f => (f.1, tunnel_lfundef f.1 f.2)).

End Tunneling.

End ASM_OP.
Context {asm_op} {asmop : asmOp asm_op} {ovm_i : one_varmap.one_varmap_info}.

  Lemma get_fundef_tunnel_funcs lf fn :
    get_fundef (tunnel_funcs lf) fn =
    match get_fundef lf fn with
    | Some fd => Some (tunnel_lfundef fn fd)
    | None => None
    end.
