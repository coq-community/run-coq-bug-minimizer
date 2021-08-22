(* -*- mode: coq; coq-prog-args: ("-emacs" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/msl" "VST.msl" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/sepcomp" "VST.sepcomp" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/veric" "VST.veric" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/floyd" "VST.floyd" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/progs" "VST.progs" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/concurrency" "VST.concurrency" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/atomics" "VST.atomics" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/wand_demo" "wand_demo" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/sha" "sha" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/hmacfcf" "hmacfcf" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/tweetnacl20140427" "tweetnacl20140427" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/hmacdrbg" "hmacdrbg" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/aes" "aes" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/mailbox" "mailbox" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/lib" "compcert.lib" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/common" "compcert.common" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/x86_32" "compcert.x86_32" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/x86" "compcert.x86" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/cfrontend" "compcert.cfrontend" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/exportclight" "compcert.exportclight" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Flocq" "Flocq" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-top" "bug_01" "-native-compiler" "no" "-native-compiler" "no") -*- *)
(* File reduced by coq-bug-finder from original input, then from 981 lines to 48 lines, then from 177 lines to 227 lines, then from 231 lines to 58 lines, then from 187 lines to 753 lines, then from 757 lines to 78 lines, then from 197 lines to 969 lines, then from 973 lines to 86 lines, then from 194 lines to 1059 lines, then from 1063 lines to 113 lines, then from 217 lines to 504 lines, then from 501 lines to 113 lines, then from 216 lines to 350 lines, then from 354 lines to 115 lines, then from 218 lines to 2333 lines, then from 2329 lines to 134 lines, then from 223 lines to 123 lines, then from 224 lines to 1656 lines, then from 1658 lines to 442 lines, then from 541 lines to 1816 lines, then from 1814 lines to 450 lines, then from 548 lines to 446 lines, then from 544 lines to 587 lines, then from 591 lines to 461 lines, then from 546 lines to 1447 lines, then from 1448 lines to 466 lines, then from 549 lines to 1160 lines, then from 1162 lines to 747 lines, then from 737 lines to 530 lines, then from 613 lines to 996 lines, then from 1000 lines to 419 lines, then from 500 lines to 812 lines, then from 815 lines to 420 lines, then from 499 lines to 1328 lines, then from 1329 lines to 913 lines, then from 896 lines to 431 lines, then from 511 lines to 576 lines, then from 580 lines to 437 lines, then from 515 lines to 2099 lines, then from 2103 lines to 497 lines, then from 563 lines to 471 lines, then from 551 lines to 698 lines, then from 702 lines to 472 lines, then from 538 lines to 1631 lines, then from 1635 lines to 479 lines, then from 544 lines to 3159 lines, then from 3163 lines to 2508 lines *)
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
Require Coq.Strings.String.
Require Coq.ZArith.ZArith.
Require Coq.ZArith.Znumtheory.
Require Coq.Lists.List.
Require Coq.Bool.Bool.
Require Coq.micromega.Lia.
Require Coq.Relations.Relations.
Require compcert.lib.Coqlib.
Require Coq.Classes.Equivalence.
Require Coq.Classes.EquivDec.
Require compcert.lib.Maps.
Require compcert.common.Errors.
Require Coq.Logic.Eqdep_dec.
Require Coq.ZArith.Zquot.
Require Coq.ZArith.Zwf.
Require Coq.micromega.Psatz.
Require compcert.lib.Zbits.
Require Flocq.IEEE754.Binary.
Require Flocq.IEEE754.Bits.
Require compcert.x86_32.Archi.
Require compcert.lib.Integers.
Require Flocq.Core.Core.
Require Flocq.Core.Digits.
Require Flocq.Calc.Operations.
Require Flocq.Calc.Round.
Require Flocq.Calc.Bracket.
Require Flocq.Prop.Sterbenz.
Require Coq.Reals.Reals.
Require Flocq.Prop.Round_odd.
Require compcert.lib.IEEE754_extra.
Require Coq.Program.Program.
Require compcert.lib.Floats.
Require compcert.common.AST.
Module Export compcert_DOT_common_DOT_Values_WRAPPED.
Module Export Values.
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 

 
Import compcert.lib.Coqlib.
Import compcert.common.AST.
Import compcert.lib.Integers.
Import compcert.lib.Floats.

Definition block : Type := positive.
Definition eq_block := peq.

 

Inductive val: Type :=
  | Vundef: val
  | Vint: int -> val
  | Vlong: int64 -> val
  | Vfloat: float -> val
  | Vsingle: float32 -> val
  | Vptr: block -> ptrofs -> val.

Definition Vzero: val := Vint Int.zero.
Definition Vone: val := Vint Int.one.
Definition Vmone: val := Vint Int.mone.

Definition Vtrue: val := Vint Int.one.
Definition Vfalse: val := Vint Int.zero.

Definition Vnullptr :=
  if Archi.ptr64 then Vlong Int64.zero else Vint Int.zero.

Definition Vptrofs (n: ptrofs) :=
  if Archi.ptr64 then Vlong (Ptrofs.to_int64 n) else Vint (Ptrofs.to_int n).

 

 

Module Export Val.

Definition eq (x y: val): {x=y} + {x<>y}.
admit.
Defined.
Global Opaque eq.

Definition has_type (v: val) (t: typ) : Prop :=
  match v, t with
  | Vundef, _ => True
  | Vint _, Tint => True
  | Vlong _, Tlong => True
  | Vfloat _, Tfloat => True
  | Vsingle _, Tsingle => True
  | Vptr _ _, Tint => Archi.ptr64 = false
  | Vptr _ _, Tlong => Archi.ptr64 = true
  | (Vint _ | Vsingle _), Tany32 => True
  | Vptr _ _, Tany32 => Archi.ptr64 = false
  | _, Tany64 => True
  | _, _ => False
  end.

Fixpoint has_type_list (vl: list val) (tl: list typ) {struct vl} : Prop :=
  match vl, tl with
  | nil, nil => True
  | v1 :: vs, t1 :: ts => has_type v1 t1 /\ has_type_list vs ts
  | _, _ => False
  end.

Definition has_opttype (v: val) (ot: option typ) : Prop :=
  match ot with
  | None => v = Vundef
  | Some t => has_type v t
  end.

Lemma Vptr_has_type:
  forall b ofs, has_type (Vptr b ofs) Tptr.
admit.
Defined.

Lemma Vnullptr_has_type:
  has_type Vnullptr Tptr.
admit.
Defined.

Lemma has_subtype:
  forall ty1 ty2 v,
  subtype ty1 ty2 = true -> has_type v ty1 -> has_type v ty2.
admit.
Defined.

Lemma has_subtype_list:
  forall tyl1 tyl2 vl,
  subtype_list tyl1 tyl2 = true -> has_type_list vl tyl1 -> has_type_list vl tyl2.
admit.
Defined.

Definition has_type_dec (v: val) (t: typ) : { has_type v t } + { ~ has_type v t }.
admit.
Defined.

Definition has_rettype (v: val) (r: rettype) : Prop :=
  match r, v with
  | Tret t, _ => has_type v t
  | Tint8signed, Vint n => n = Int.sign_ext 8 n
  | Tint8unsigned, Vint n => n = Int.zero_ext 8 n
  | Tint16signed, Vint n => n = Int.sign_ext 16 n
  | Tint16unsigned, Vint n => n = Int.zero_ext 16 n
  | _, Vundef => True
  | _, _ => False
  end.

Lemma has_proj_rettype: forall v r,
  has_rettype v r -> has_type v (proj_rettype r).
admit.
Defined.

 

Inductive bool_of_val: val -> bool -> Prop :=
  | bool_of_val_int:
      forall n, bool_of_val (Vint n) (negb (Int.eq n Int.zero)).

 

Definition neg (v: val) : val :=
  match v with
  | Vint n => Vint (Int.neg n)
  | _ => Vundef
  end.

Definition negf (v: val) : val :=
  match v with
  | Vfloat f => Vfloat (Float.neg f)
  | _ => Vundef
  end.

Definition absf (v: val) : val :=
  match v with
  | Vfloat f => Vfloat (Float.abs f)
  | _ => Vundef
  end.

Definition negfs (v: val) : val :=
  match v with
  | Vsingle f => Vsingle (Float32.neg f)
  | _ => Vundef
  end.

Definition absfs (v: val) : val :=
  match v with
  | Vsingle f => Vsingle (Float32.abs f)
  | _ => Vundef
  end.

Definition maketotal (ov: option val) : val :=
  match ov with Some v => v | None => Vundef end.

Definition intoffloat (v: val) : option val :=
  match v with
  | Vfloat f => option_map Vint (Float.to_int f)
  | _ => None
  end.

Definition intuoffloat (v: val) : option val :=
  match v with
  | Vfloat f => option_map Vint (Float.to_intu f)
  | _ => None
  end.

Definition floatofint (v: val) : option val :=
  match v with
  | Vint n => Some (Vfloat (Float.of_int n))
  | _ => None
  end.

Definition floatofintu (v: val) : option val :=
  match v with
  | Vint n => Some (Vfloat (Float.of_intu n))
  | _ => None
  end.

Definition intofsingle (v: val) : option val :=
  match v with
  | Vsingle f => option_map Vint (Float32.to_int f)
  | _ => None
  end.

Definition intuofsingle (v: val) : option val :=
  match v with
  | Vsingle f => option_map Vint (Float32.to_intu f)
  | _ => None
  end.

Definition singleofint (v: val) : option val :=
  match v with
  | Vint n => Some (Vsingle (Float32.of_int n))
  | _ => None
  end.

Definition singleofintu (v: val) : option val :=
  match v with
  | Vint n => Some (Vsingle (Float32.of_intu n))
  | _ => None
  end.

Definition negint (v: val) : val :=
  match v with
  | Vint n => Vint (Int.neg n)
  | _ => Vundef
  end.

Definition notint (v: val) : val :=
  match v with
  | Vint n => Vint (Int.not n)
  | _ => Vundef
  end.

Definition of_bool (b: bool): val := if b then Vtrue else Vfalse.

Definition boolval (v: val) : val :=
  match v with
  | Vint n => of_bool (negb (Int.eq n Int.zero))
  | Vptr b ofs => Vtrue
  | _ => Vundef
  end.

Definition notbool (v: val) : val :=
  match v with
  | Vint n => of_bool (Int.eq n Int.zero)
  | Vptr b ofs => Vfalse
  | _ => Vundef
  end.

Definition zero_ext (nbits: Z) (v: val) : val :=
  match v with
  | Vint n => Vint(Int.zero_ext nbits n)
  | _ => Vundef
  end.

Definition sign_ext (nbits: Z) (v: val) : val :=
  match v with
  | Vint n => Vint(Int.sign_ext nbits n)
  | _ => Vundef
  end.

Definition singleoffloat (v: val) : val :=
  match v with
  | Vfloat f => Vsingle (Float.to_single f)
  | _ => Vundef
  end.

Definition floatofsingle (v: val) : val :=
  match v with
  | Vsingle f => Vfloat (Float.of_single f)
  | _ => Vundef
  end.

Definition add (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 => Vint(Int.add n1 n2)
  | Vptr b1 ofs1, Vint n2 => if Archi.ptr64 then Vundef else Vptr b1 (Ptrofs.add ofs1 (Ptrofs.of_int n2))
  | Vint n1, Vptr b2 ofs2 => if Archi.ptr64 then Vundef else Vptr b2 (Ptrofs.add ofs2 (Ptrofs.of_int n1))
  | _, _ => Vundef
  end.

Definition sub (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 => Vint(Int.sub n1 n2)
  | Vptr b1 ofs1, Vint n2 => if Archi.ptr64 then Vundef else Vptr b1 (Ptrofs.sub ofs1 (Ptrofs.of_int n2))
  | Vptr b1 ofs1, Vptr b2 ofs2 =>
      if Archi.ptr64 then Vundef else
      if eq_block b1 b2 then Vint(Ptrofs.to_int (Ptrofs.sub ofs1 ofs2)) else Vundef
  | _, _ => Vundef
  end.

Definition mul (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 => Vint(Int.mul n1 n2)
  | _, _ => Vundef
  end.

Definition mulhs (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 => Vint(Int.mulhs n1 n2)
  | _, _ => Vundef
  end.

Definition mulhu (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 => Vint(Int.mulhu n1 n2)
  | _, _ => Vundef
  end.

Definition divs (v1 v2: val): option val :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
      if Int.eq n2 Int.zero
      || Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone
      then None
      else Some(Vint(Int.divs n1 n2))
  | _, _ => None
  end.

Definition mods (v1 v2: val): option val :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
      if Int.eq n2 Int.zero
      || Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone
      then None
      else Some(Vint(Int.mods n1 n2))
  | _, _ => None
  end.

Definition divu (v1 v2: val): option val :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
      if Int.eq n2 Int.zero then None else Some(Vint(Int.divu n1 n2))
  | _, _ => None
  end.

Definition modu (v1 v2: val): option val :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
      if Int.eq n2 Int.zero then None else Some(Vint(Int.modu n1 n2))
  | _, _ => None
  end.

Definition add_carry (v1 v2 cin: val): val :=
  match v1, v2, cin with
  | Vint n1, Vint n2, Vint c => Vint(Int.add_carry n1 n2 c)
  | _, _, _ => Vundef
  end.

Definition sub_overflow (v1 v2: val) : val :=
  match v1, v2 with
  | Vint n1, Vint n2 => Vint(Int.sub_overflow n1 n2 Int.zero)
  | _, _ => Vundef
  end.

Definition negative (v: val) : val :=
  match v with
  | Vint n => Vint (Int.negative n)
  | _ => Vundef
  end.

Definition and (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 => Vint(Int.and n1 n2)
  | _, _ => Vundef
  end.

Definition or (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 => Vint(Int.or n1 n2)
  | _, _ => Vundef
  end.

Definition xor (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 => Vint(Int.xor n1 n2)
  | _, _ => Vundef
  end.

Definition shl (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
     if Int.ltu n2 Int.iwordsize
     then Vint(Int.shl n1 n2)
     else Vundef
  | _, _ => Vundef
  end.

Definition shr (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
     if Int.ltu n2 Int.iwordsize
     then Vint(Int.shr n1 n2)
     else Vundef
  | _, _ => Vundef
  end.

Definition shr_carry (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
     if Int.ltu n2 Int.iwordsize
     then Vint(Int.shr_carry n1 n2)
     else Vundef
  | _, _ => Vundef
  end.

Definition shrx (v1 v2: val): option val :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
     if Int.ltu n2 (Int.repr 31)
     then Some(Vint(Int.shrx n1 n2))
     else None
  | _, _ => None
  end.

Definition shru (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
     if Int.ltu n2 Int.iwordsize
     then Vint(Int.shru n1 n2)
     else Vundef
  | _, _ => Vundef
  end.

Definition rol (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 => Vint(Int.rol n1 n2)
  | _, _ => Vundef
  end.

Definition rolm (v: val) (amount mask: int): val :=
  match v with
  | Vint n => Vint(Int.rolm n amount mask)
  | _ => Vundef
  end.

Definition ror (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 => Vint(Int.ror n1 n2)
  | _, _ => Vundef
  end.

Definition addf (v1 v2: val): val :=
  match v1, v2 with
  | Vfloat f1, Vfloat f2 => Vfloat(Float.add f1 f2)
  | _, _ => Vundef
  end.

Definition subf (v1 v2: val): val :=
  match v1, v2 with
  | Vfloat f1, Vfloat f2 => Vfloat(Float.sub f1 f2)
  | _, _ => Vundef
  end.

Definition mulf (v1 v2: val): val :=
  match v1, v2 with
  | Vfloat f1, Vfloat f2 => Vfloat(Float.mul f1 f2)
  | _, _ => Vundef
  end.

Definition divf (v1 v2: val): val :=
  match v1, v2 with
  | Vfloat f1, Vfloat f2 => Vfloat(Float.div f1 f2)
  | _, _ => Vundef
  end.

Definition floatofwords (v1 v2: val) : val :=
  match v1, v2 with
  | Vint n1, Vint n2 => Vfloat (Float.from_words n1 n2)
  | _, _ => Vundef
  end.

Definition addfs (v1 v2: val): val :=
  match v1, v2 with
  | Vsingle f1, Vsingle f2 => Vsingle(Float32.add f1 f2)
  | _, _ => Vundef
  end.

Definition subfs (v1 v2: val): val :=
  match v1, v2 with
  | Vsingle f1, Vsingle f2 => Vsingle(Float32.sub f1 f2)
  | _, _ => Vundef
  end.

Definition mulfs (v1 v2: val): val :=
  match v1, v2 with
  | Vsingle f1, Vsingle f2 => Vsingle(Float32.mul f1 f2)
  | _, _ => Vundef
  end.

Definition divfs (v1 v2: val): val :=
  match v1, v2 with
  | Vsingle f1, Vsingle f2 => Vsingle(Float32.div f1 f2)
  | _, _ => Vundef
  end.

 

Definition longofwords (v1 v2: val) : val :=
  match v1, v2 with
  | Vint n1, Vint n2 => Vlong (Int64.ofwords n1 n2)
  | _, _ => Vundef
  end.

Definition loword (v: val) : val :=
  match v with
  | Vlong n  => Vint (Int64.loword n)
  | _ => Vundef
  end.

Definition hiword (v: val) : val :=
  match v with
  | Vlong n  => Vint (Int64.hiword n)
  | _ => Vundef
  end.

Definition negl (v: val) : val :=
  match v with
  | Vlong n => Vlong (Int64.neg n)
  | _ => Vundef
  end.

Definition notl (v: val) : val :=
  match v with
  | Vlong n => Vlong (Int64.not n)
  | _ => Vundef
  end.

Definition longofint (v: val) : val :=
  match v with
  | Vint n => Vlong (Int64.repr (Int.signed n))
  | _ => Vundef
  end.

Definition longofintu (v: val) : val :=
  match v with
  | Vint n => Vlong (Int64.repr (Int.unsigned n))
  | _ => Vundef
  end.

Definition longoffloat (v: val) : option val :=
  match v with
  | Vfloat f => option_map Vlong (Float.to_long f)
  | _ => None
  end.

Definition longuoffloat (v: val) : option val :=
  match v with
  | Vfloat f => option_map Vlong (Float.to_longu f)
  | _ => None
  end.

Definition longofsingle (v: val) : option val :=
  match v with
  | Vsingle f => option_map Vlong (Float32.to_long f)
  | _ => None
  end.

Definition longuofsingle (v: val) : option val :=
  match v with
  | Vsingle f => option_map Vlong (Float32.to_longu f)
  | _ => None
  end.

Definition floatoflong (v: val) : option val :=
  match v with
  | Vlong n => Some (Vfloat (Float.of_long n))
  | _ => None
  end.

Definition floatoflongu (v: val) : option val :=
  match v with
  | Vlong n => Some (Vfloat (Float.of_longu n))
  | _ => None
  end.

Definition singleoflong (v: val) : option val :=
  match v with
  | Vlong n => Some (Vsingle (Float32.of_long n))
  | _ => None
  end.

Definition singleoflongu (v: val) : option val :=
  match v with
  | Vlong n => Some (Vsingle (Float32.of_longu n))
  | _ => None
  end.

Definition addl (v1 v2: val): val :=
  match v1, v2 with
  | Vlong n1, Vlong n2 => Vlong(Int64.add n1 n2)
  | Vptr b1 ofs1, Vlong n2 => if Archi.ptr64 then Vptr b1 (Ptrofs.add ofs1 (Ptrofs.of_int64 n2)) else Vundef
  | Vlong n1, Vptr b2 ofs2 => if Archi.ptr64 then Vptr b2 (Ptrofs.add ofs2 (Ptrofs.of_int64 n1)) else Vundef
  | _, _ => Vundef
  end.

Definition subl (v1 v2: val): val :=
  match v1, v2 with
  | Vlong n1, Vlong n2 => Vlong(Int64.sub n1 n2)
  | Vptr b1 ofs1, Vlong n2 =>
      if Archi.ptr64 then Vptr b1 (Ptrofs.sub ofs1 (Ptrofs.of_int64 n2)) else Vundef
  | Vptr b1 ofs1, Vptr b2 ofs2 =>
      if negb Archi.ptr64 then Vundef else
      if eq_block b1 b2 then Vlong(Ptrofs.to_int64 (Ptrofs.sub ofs1 ofs2)) else Vundef
  | _, _ => Vundef
  end.

Definition mull (v1 v2: val): val :=
  match v1, v2 with
  | Vlong n1, Vlong n2 => Vlong(Int64.mul n1 n2)
  | _, _ => Vundef
  end.

Definition mull' (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 => Vlong(Int64.mul' n1 n2)
  | _, _ => Vundef
  end.

Definition mullhs (v1 v2: val): val :=
  match v1, v2 with
  | Vlong n1, Vlong n2 => Vlong(Int64.mulhs n1 n2)
  | _, _ => Vundef
  end.

Definition mullhu (v1 v2: val): val :=
  match v1, v2 with
  | Vlong n1, Vlong n2 => Vlong(Int64.mulhu n1 n2)
  | _, _ => Vundef
  end.

Definition divls (v1 v2: val): option val :=
  match v1, v2 with
  | Vlong n1, Vlong n2 =>
      if Int64.eq n2 Int64.zero
      || Int64.eq n1 (Int64.repr Int64.min_signed) && Int64.eq n2 Int64.mone
      then None
      else Some(Vlong(Int64.divs n1 n2))
  | _, _ => None
  end.

Definition modls (v1 v2: val): option val :=
  match v1, v2 with
  | Vlong n1, Vlong n2 =>
      if Int64.eq n2 Int64.zero
      || Int64.eq n1 (Int64.repr Int64.min_signed) && Int64.eq n2 Int64.mone
      then None
      else Some(Vlong(Int64.mods n1 n2))
  | _, _ => None
  end.

Definition divlu (v1 v2: val): option val :=
  match v1, v2 with
  | Vlong n1, Vlong n2 =>
      if Int64.eq n2 Int64.zero then None else Some(Vlong(Int64.divu n1 n2))
  | _, _ => None
  end.

Definition modlu (v1 v2: val): option val :=
  match v1, v2 with
  | Vlong n1, Vlong n2 =>
      if Int64.eq n2 Int64.zero then None else Some(Vlong(Int64.modu n1 n2))
  | _, _ => None
  end.

Definition addl_carry (v1 v2 cin: val): val :=
  match v1, v2, cin with
  | Vlong n1, Vlong n2, Vlong c => Vlong(Int64.add_carry n1 n2 c)
  | _, _, _ => Vundef
  end.

Definition subl_overflow (v1 v2: val) : val :=
  match v1, v2 with
  | Vlong n1, Vlong n2 => Vint (Int.repr (Int64.unsigned (Int64.sub_overflow n1 n2 Int64.zero)))
  | _, _ => Vundef
  end.

Definition negativel (v: val) : val :=
  match v with
  | Vlong n => Vint (Int.repr (Int64.unsigned (Int64.negative n)))
  | _ => Vundef
  end.

Definition andl (v1 v2: val): val :=
  match v1, v2 with
  | Vlong n1, Vlong n2 => Vlong(Int64.and n1 n2)
  | _, _ => Vundef
  end.

Definition orl (v1 v2: val): val :=
  match v1, v2 with
  | Vlong n1, Vlong n2 => Vlong(Int64.or n1 n2)
  | _, _ => Vundef
  end.

Definition xorl (v1 v2: val): val :=
  match v1, v2 with
  | Vlong n1, Vlong n2 => Vlong(Int64.xor n1 n2)
  | _, _ => Vundef
  end.

Definition shll (v1 v2: val): val :=
  match v1, v2 with
  | Vlong n1, Vint n2 =>
     if Int.ltu n2 Int64.iwordsize'
     then Vlong(Int64.shl' n1 n2)
     else Vundef
  | _, _ => Vundef
  end.

Definition shrl (v1 v2: val): val :=
  match v1, v2 with
  | Vlong n1, Vint n2 =>
     if Int.ltu n2 Int64.iwordsize'
     then Vlong(Int64.shr' n1 n2)
     else Vundef
  | _, _ => Vundef
  end.

Definition shrlu (v1 v2: val): val :=
  match v1, v2 with
  | Vlong n1, Vint n2 =>
     if Int.ltu n2 Int64.iwordsize'
     then Vlong(Int64.shru' n1 n2)
     else Vundef
  | _, _ => Vundef
  end.

Definition shrxl (v1 v2: val): option val :=
  match v1, v2 with
  | Vlong n1, Vint n2 =>
     if Int.ltu n2 (Int.repr 63)
     then Some(Vlong(Int64.shrx' n1 n2))
     else None
  | _, _ => None
  end.

Definition shrl_carry (v1 v2: val): val :=
  match v1, v2 with
  | Vlong n1, Vint n2 =>
     if Int.ltu n2 Int64.iwordsize'
     then Vlong(Int64.shr_carry' n1 n2)
     else Vundef
  | _, _ => Vundef
  end.

Definition roll (v1 v2: val): val :=
  match v1, v2 with
  | Vlong n1, Vint n2 => Vlong(Int64.rol n1 (Int64.repr (Int.unsigned n2)))
  | _, _ => Vundef
  end.

Definition rorl (v1 v2: val): val :=
  match v1, v2 with
  | Vlong n1, Vint n2 => Vlong(Int64.ror n1 (Int64.repr (Int.unsigned n2)))
  | _, _ => Vundef
  end.

Definition rolml (v: val) (amount: int) (mask: int64): val :=
  match v with
  | Vlong n => Vlong(Int64.rolm n (Int64.repr (Int.unsigned amount)) mask)
  | _ => Vundef
  end.

Definition zero_ext_l (nbits: Z) (v: val) : val :=
  match v with
  | Vlong n => Vlong(Int64.zero_ext nbits n)
  | _ => Vundef
  end.

Definition sign_ext_l (nbits: Z) (v: val) : val :=
  match v with
  | Vlong n => Vlong(Int64.sign_ext nbits n)
  | _ => Vundef
  end.

 

Section COMPARISONS.

Variable valid_ptr: block -> Z -> bool.
Let weak_valid_ptr (b: block) (ofs: Z) := valid_ptr b ofs || valid_ptr b (ofs - 1).

Definition cmp_bool (c: comparison) (v1 v2: val): option bool :=
  match v1, v2 with
  | Vint n1, Vint n2 => Some (Int.cmp c n1 n2)
  | _, _ => None
  end.

Definition cmp_different_blocks (c: comparison): option bool :=
  match c with
  | Ceq => Some false
  | Cne => Some true
  | _   => None
  end.

Definition cmpu_bool (c: comparison) (v1 v2: val): option bool :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
      Some (Int.cmpu c n1 n2)
  | Vint n1, Vptr b2 ofs2 =>
      if Archi.ptr64 then None else
      if Int.eq n1 Int.zero && weak_valid_ptr b2 (Ptrofs.unsigned ofs2)
      then cmp_different_blocks c
      else None
  | Vptr b1 ofs1, Vptr b2 ofs2 =>
      if Archi.ptr64 then None else
      if eq_block b1 b2 then
        if weak_valid_ptr b1 (Ptrofs.unsigned ofs1)
           && weak_valid_ptr b2 (Ptrofs.unsigned ofs2)
        then Some (Ptrofs.cmpu c ofs1 ofs2)
        else None
      else
        if valid_ptr b1 (Ptrofs.unsigned ofs1)
           && valid_ptr b2 (Ptrofs.unsigned ofs2)
        then cmp_different_blocks c
        else None
  | Vptr b1 ofs1, Vint n2 =>
      if Archi.ptr64 then None else
      if Int.eq n2 Int.zero && weak_valid_ptr b1 (Ptrofs.unsigned ofs1)
      then cmp_different_blocks c
      else None
  | _, _ => None
  end.

Definition cmpf_bool (c: comparison) (v1 v2: val): option bool :=
  match v1, v2 with
  | Vfloat f1, Vfloat f2 => Some (Float.cmp c f1 f2)
  | _, _ => None
  end.

Definition cmpfs_bool (c: comparison) (v1 v2: val): option bool :=
  match v1, v2 with
  | Vsingle f1, Vsingle f2 => Some (Float32.cmp c f1 f2)
  | _, _ => None
  end.

Definition cmpl_bool (c: comparison) (v1 v2: val): option bool :=
  match v1, v2 with
  | Vlong n1, Vlong n2 => Some (Int64.cmp c n1 n2)
  | _, _ => None
  end.

Definition cmplu_bool (c: comparison) (v1 v2: val): option bool :=
  match v1, v2 with
  | Vlong n1, Vlong n2 => Some (Int64.cmpu c n1 n2)
  | Vlong n1, Vptr b2 ofs2 =>
      if negb Archi.ptr64 then None else
      if Int64.eq n1 Int64.zero && weak_valid_ptr b2 (Ptrofs.unsigned ofs2)
      then cmp_different_blocks c
      else None
  | Vptr b1 ofs1, Vptr b2 ofs2 =>
      if negb Archi.ptr64 then None else
      if eq_block b1 b2 then
        if weak_valid_ptr b1 (Ptrofs.unsigned ofs1)
           && weak_valid_ptr b2 (Ptrofs.unsigned ofs2)
        then Some (Ptrofs.cmpu c ofs1 ofs2)
        else None
      else
        if valid_ptr b1 (Ptrofs.unsigned ofs1)
           && valid_ptr b2 (Ptrofs.unsigned ofs2)
        then cmp_different_blocks c
        else None
  | Vptr b1 ofs1, Vlong n2 =>
      if negb Archi.ptr64 then None else
      if Int64.eq n2 Int64.zero && weak_valid_ptr b1 (Ptrofs.unsigned ofs1)
      then cmp_different_blocks c
      else None
  | _, _ => None
  end.

Definition of_optbool (ob: option bool): val :=
  match ob with Some true => Vtrue | Some false => Vfalse | None => Vundef end.

Definition cmp (c: comparison) (v1 v2: val): val :=
  of_optbool (cmp_bool c v1 v2).

Definition cmpu (c: comparison) (v1 v2: val): val :=
  of_optbool (cmpu_bool c v1 v2).

Definition cmpf (c: comparison) (v1 v2: val): val :=
  of_optbool (cmpf_bool c v1 v2).

Definition cmpfs (c: comparison) (v1 v2: val): val :=
  of_optbool (cmpfs_bool c v1 v2).

Definition cmpl (c: comparison) (v1 v2: val): option val :=
  option_map of_bool (cmpl_bool c v1 v2).

Definition cmplu (c: comparison) (v1 v2: val): option val :=
  option_map of_bool (cmplu_bool c v1 v2).

Definition maskzero_bool (v: val) (mask: int): option bool :=
  match v with
  | Vint n => Some (Int.eq (Int.and n mask) Int.zero)
  | _ => None
  end.

End COMPARISONS.

 

Definition offset_ptr (v: val) (delta: ptrofs) : val :=
  match v with
  | Vptr b ofs => Vptr b (Ptrofs.add ofs delta)
  | _ => Vundef
  end.

 

Definition normalize (v: val) (ty: typ) : val :=
  match v, ty with
  | Vundef, _ => Vundef
  | Vint _, Tint => v
  | Vlong _, Tlong => v
  | Vfloat _, Tfloat => v
  | Vsingle _, Tsingle => v
  | Vptr _ _, (Tint | Tany32) => if Archi.ptr64 then Vundef else v
  | Vptr _ _, Tlong => if Archi.ptr64 then v else Vundef
  | (Vint _ | Vsingle _), Tany32 => v
  | _, Tany64 => v
  | _, _ => Vundef
  end.

Lemma normalize_type:
  forall v ty, has_type (normalize v ty) ty.
admit.
Defined.

Lemma normalize_idem:
  forall v ty, has_type v ty -> normalize v ty = v.
admit.
Defined.

 

Definition select (cmp: option bool) (v1 v2: val) (ty: typ) :=
  match cmp with
  | Some b => normalize (if b then v1 else v2) ty
  | None => Vundef
  end.

 

Definition load_result (chunk: memory_chunk) (v: val) :=
  match chunk, v with
  | Mint8signed, Vint n => Vint (Int.sign_ext 8 n)
  | Mint8unsigned, Vint n => Vint (Int.zero_ext 8 n)
  | Mint16signed, Vint n => Vint (Int.sign_ext 16 n)
  | Mint16unsigned, Vint n => Vint (Int.zero_ext 16 n)
  | Mint32, Vint n => Vint n
  | Mint32, Vptr b ofs => if Archi.ptr64 then Vundef else Vptr b ofs
  | Mint64, Vlong n => Vlong n
  | Mint64, Vptr b ofs => if Archi.ptr64 then Vptr b ofs else Vundef
  | Mfloat32, Vsingle f => Vsingle f
  | Mfloat64, Vfloat f => Vfloat f
  | Many32, (Vint _ | Vsingle _) => v
  | Many32, Vptr _ _ => if Archi.ptr64 then Vundef else v
  | Many64, _ => v
  | _, _ => Vundef
  end.

Lemma load_result_rettype:
  forall chunk v, has_rettype (load_result chunk v) (rettype_of_chunk chunk).
admit.
Defined.

Lemma load_result_type:
  forall chunk v, has_type (load_result chunk v) (type_of_chunk chunk).
admit.
Defined.

Lemma load_result_same:
  forall v ty, has_type v ty -> load_result (chunk_of_type ty) v = v.
admit.
Defined.

 

Theorem cast8unsigned_and:
  forall x, zero_ext 8 x = and x (Vint(Int.repr 255)).
admit.
Defined.

Theorem cast16unsigned_and:
  forall x, zero_ext 16 x = and x (Vint(Int.repr 65535)).
admit.
Defined.

Theorem bool_of_val_of_bool:
  forall b1 b2, bool_of_val (of_bool b1) b2 -> b1 = b2.
admit.
Defined.

Theorem bool_of_val_of_optbool:
  forall ob b, bool_of_val (of_optbool ob) b -> ob = Some b.
admit.
Defined.

Theorem notbool_negb_1:
  forall b, of_bool (negb b) = notbool (of_bool b).
admit.
Defined.

Theorem notbool_negb_2:
  forall b, of_bool b = notbool (of_bool (negb b)).
admit.
Defined.

Theorem notbool_negb_3:
  forall ob, of_optbool (option_map negb ob) = notbool (of_optbool ob).
admit.
Defined.

Theorem notbool_idem2:
  forall b, notbool(notbool(of_bool b)) = of_bool b.
admit.
Defined.

Theorem notbool_idem3:
  forall x, notbool(notbool(notbool x)) = notbool x.
admit.
Defined.

Theorem notbool_idem4:
  forall ob, notbool (notbool (of_optbool ob)) = of_optbool ob.
admit.
Defined.

Theorem add_commut: forall x y, add x y = add y x.
admit.
Defined.

Theorem add_assoc: forall x y z, add (add x y) z = add x (add y z).
admit.
Defined.

Theorem add_permut: forall x y z, add x (add y z) = add y (add x z).
admit.
Defined.

Theorem add_permut_4:
  forall x y z t, add (add x y) (add z t) = add (add x z) (add y t).
admit.
Defined.

Theorem neg_zero: neg Vzero = Vzero.
admit.
Defined.

Theorem neg_add_distr: forall x y, neg(add x y) = add (neg x) (neg y).
admit.
Defined.

Theorem sub_zero_r: forall x, sub Vzero x = neg x.
admit.
Defined.

Theorem sub_add_opp: forall x y, sub x (Vint y) = add x (Vint (Int.neg y)).
admit.
Defined.

Theorem sub_opp_add: forall x y, sub x (Vint (Int.neg y)) = add x (Vint y).
admit.
Defined.

Theorem sub_add_l:
  forall v1 v2 i, sub (add v1 (Vint i)) v2 = add (sub v1 v2) (Vint i).
admit.
Defined.

Theorem sub_add_r:
  forall v1 v2 i, sub v1 (add v2 (Vint i)) = add (sub v1 v2) (Vint (Int.neg i)).
admit.
Defined.

Theorem mul_commut: forall x y, mul x y = mul y x.
admit.
Defined.

Theorem mul_assoc: forall x y z, mul (mul x y) z = mul x (mul y z).
admit.
Defined.

Theorem mul_add_distr_l:
  forall x y z, mul (add x y) z = add (mul x z) (mul y z).
admit.
Defined.

Theorem mul_add_distr_r:
  forall x y z, mul x (add y z) = add (mul x y) (mul x z).
admit.
Defined.

Theorem mul_pow2:
  forall x n logn,
  Int.is_power2 n = Some logn ->
  mul x (Vint n) = shl x (Vint logn).
admit.
Defined.

Theorem mods_divs:
  forall x y z,
  mods x y = Some z -> exists v, divs x y = Some v /\ z = sub x (mul v y).
admit.
Defined.

Theorem modu_divu:
  forall x y z,
  modu x y = Some z -> exists v, divu x y = Some v /\ z = sub x (mul v y).
admit.
Defined.

Theorem modls_divls:
  forall x y z,
  modls x y = Some z -> exists v, divls x y = Some v /\ z = subl x (mull v y).
admit.
Defined.

Theorem modlu_divlu:
  forall x y z,
  modlu x y = Some z -> exists v, divlu x y = Some v /\ z = subl x (mull v y).
admit.
Defined.

Theorem divs_pow2:
  forall x n logn y,
  Int.is_power2 n = Some logn -> Int.ltu logn (Int.repr 31) = true ->
  divs x (Vint n) = Some y ->
  shrx x (Vint logn) = Some y.
admit.
Defined.

Theorem divs_one:
  forall s , divs (Vint s) (Vint Int.one) = Some (Vint s).
admit.
Defined.

Theorem divu_pow2:
  forall x n logn y,
  Int.is_power2 n = Some logn ->
  divu x (Vint n) = Some y ->
  shru x (Vint logn) = y.
admit.
Defined.

Theorem divu_one:
  forall s, divu (Vint s) (Vint Int.one) = Some (Vint s).
admit.
Defined.

Theorem modu_pow2:
  forall x n logn y,
  Int.is_power2 n = Some logn ->
  modu x (Vint n) = Some y ->
  and x (Vint (Int.sub n Int.one)) = y.
admit.
Defined.

Theorem and_commut: forall x y, and x y = and y x.
admit.
Defined.

Theorem and_assoc: forall x y z, and (and x y) z = and x (and y z).
admit.
Defined.

Theorem or_commut: forall x y, or x y = or y x.
admit.
Defined.

Theorem or_assoc: forall x y z, or (or x y) z = or x (or y z).
admit.
Defined.

Theorem xor_commut: forall x y, xor x y = xor y x.
admit.
Defined.

Theorem xor_assoc: forall x y z, xor (xor x y) z = xor x (xor y z).
admit.
Defined.

Theorem not_xor: forall x, notint x = xor x (Vint Int.mone).
admit.
Defined.

Theorem shl_mul: forall x y, mul x (shl Vone y) = shl x y.
admit.
Defined.

Theorem shl_rolm:
  forall x n,
  Int.ltu n Int.iwordsize = true ->
  shl x (Vint n) = rolm x n (Int.shl Int.mone n).
admit.
Defined.

Theorem shll_rolml:
  forall x n,
  Int.ltu n Int64.iwordsize' = true ->
  shll x (Vint n) = rolml x n (Int64.shl Int64.mone (Int64.repr (Int.unsigned n))).
admit.
Defined.

Theorem shru_rolm:
  forall x n,
  Int.ltu n Int.iwordsize = true ->
  shru x (Vint n) = rolm x (Int.sub Int.iwordsize n) (Int.shru Int.mone n).
admit.
Defined.

Theorem shrlu_rolml:
  forall x n,
    Int.ltu n Int64.iwordsize' = true ->
    shrlu x (Vint n) = rolml x (Int.sub Int64.iwordsize' n) (Int64.shru Int64.mone (Int64.repr (Int.unsigned n))).
admit.
Defined.

Theorem shrx_carry:
  forall x y z,
  shrx x y = Some z ->
  add (shr x y) (shr_carry x y) = z.
admit.
Defined.

Theorem shrx_shr:
  forall x y z,
  shrx x y = Some z ->
  exists p, exists q,
    x = Vint p /\ y = Vint q /\
    z = shr (if Int.lt p Int.zero then add x (Vint (Int.sub (Int.shl Int.one q) Int.one)) else x) (Vint q).
admit.
Defined.

Theorem shrx_shr_2:
  forall n x z,
  shrx x (Vint n) = Some z ->
  z = (if Int.eq n Int.zero then x else
         shr (add x (shru (shr x (Vint (Int.repr 31)))
                    (Vint (Int.sub (Int.repr 32) n))))
             (Vint n)).
admit.
Defined.

Theorem or_rolm:
  forall x n m1 m2,
  or (rolm x n m1) (rolm x n m2) = rolm x n (Int.or m1 m2).
admit.
Defined.

Theorem rolm_rolm:
  forall x n1 m1 n2 m2,
  rolm (rolm x n1 m1) n2 m2 =
    rolm x (Int.modu (Int.add n1 n2) Int.iwordsize)
           (Int.and (Int.rol m1 n2) m2).
admit.
Defined.

Theorem rolm_zero:
  forall x m,
  rolm x Int.zero m = and x (Vint m).
admit.
Defined.

Theorem addl_commut: forall x y, addl x y = addl y x.
admit.
Defined.

Theorem addl_assoc: forall x y z, addl (addl x y) z = addl x (addl y z).
admit.
Defined.

Theorem addl_permut: forall x y z, addl x (addl y z) = addl y (addl x z).
admit.
Defined.

Theorem addl_permut_4:
  forall x y z t, addl (addl x y) (addl z t) = addl (addl x z) (addl y t).
admit.
Defined.

Theorem negl_addl_distr: forall x y, negl(addl x y) = addl (negl x) (negl y).
admit.
Defined.

Theorem subl_addl_opp: forall x y, subl x (Vlong y) = addl x (Vlong (Int64.neg y)).
admit.
Defined.

Theorem subl_opp_addl: forall x y, subl x (Vlong (Int64.neg y)) = addl x (Vlong y).
admit.
Defined.

Theorem subl_addl_l:
  forall v1 v2 i, subl (addl v1 (Vlong i)) v2 = addl (subl v1 v2) (Vlong i).
admit.
Defined.

Theorem subl_addl_r:
  forall v1 v2 i, subl v1 (addl v2 (Vlong i)) = addl (subl v1 v2) (Vlong (Int64.neg i)).
admit.
Defined.

Theorem mull_commut: forall x y, mull x y = mull y x.
admit.
Defined.

Theorem mull_assoc: forall x y z, mull (mull x y) z = mull x (mull y z).
admit.
Defined.

Theorem mull_addl_distr_l:
  forall x y z, mull (addl x y) z = addl (mull x z) (mull y z).
admit.
Defined.

Theorem mull_addl_distr_r:
  forall x y z, mull x (addl y z) = addl (mull x y) (mull x z).
admit.
Defined.

Theorem andl_commut: forall x y, andl x y = andl y x.
admit.
Defined.

Theorem andl_assoc: forall x y z, andl (andl x y) z = andl x (andl y z).
admit.
Defined.

Theorem orl_commut: forall x y, orl x y = orl y x.
admit.
Defined.

Theorem orl_assoc: forall x y z, orl (orl x y) z = orl x (orl y z).
admit.
Defined.

Theorem xorl_commut: forall x y, xorl x y = xorl y x.
admit.
Defined.

Theorem xorl_assoc: forall x y z, xorl (xorl x y) z = xorl x (xorl y z).
admit.
Defined.

Theorem notl_xorl: forall x, notl x = xorl x (Vlong Int64.mone).
admit.
Defined.

Theorem divls_pow2:
  forall x n logn y,
  Int64.is_power2' n = Some logn -> Int.ltu logn (Int.repr 63) = true ->
  divls x (Vlong n) = Some y ->
  shrxl x (Vint logn) = Some y.
admit.
Defined.

Theorem divls_one:
  forall n, divls (Vlong n) (Vlong Int64.one) = Some (Vlong n).
admit.
Defined.

Theorem divlu_pow2:
  forall x n logn y,
  Int64.is_power2' n = Some logn ->
  divlu x (Vlong n) = Some y ->
  shrlu x (Vint logn) = y.
admit.
Defined.

Theorem divlu_one:
  forall n, divlu (Vlong n) (Vlong Int64.one) = Some (Vlong n).
admit.
Defined.

Theorem modlu_pow2:
  forall x n logn y,
  Int64.is_power2 n = Some logn ->
  modlu x (Vlong n) = Some y ->
  andl x (Vlong (Int64.sub n Int64.one)) = y.
admit.
Defined.

Theorem shrxl_carry:
  forall x y z,
  shrxl x y = Some z ->
  addl (shrl x y) (shrl_carry x y) = z.
admit.
Defined.

Theorem shrxl_shrl_2:
  forall n x z,
  shrxl x (Vint n) = Some z ->
  z = (if Int.eq n Int.zero then x else
         shrl (addl x (shrlu (shrl x (Vint (Int.repr 63)))
                      (Vint (Int.sub (Int.repr 64) n))))
              (Vint n)).
admit.
Defined.

Theorem negate_cmp_bool:
  forall c x y, cmp_bool (negate_comparison c) x y = option_map negb (cmp_bool c x y).
admit.
Defined.

Theorem negate_cmpu_bool:
  forall valid_ptr c x y,
  cmpu_bool valid_ptr (negate_comparison c) x y = option_map negb (cmpu_bool valid_ptr c x y).
admit.
Defined.

Theorem negate_cmpl_bool:
  forall c x y, cmpl_bool (negate_comparison c) x y = option_map negb (cmpl_bool c x y).
admit.
Defined.

Theorem negate_cmplu_bool:
  forall valid_ptr c x y,
  cmplu_bool valid_ptr (negate_comparison c) x y = option_map negb (cmplu_bool valid_ptr c x y).
admit.
Defined.

Lemma not_of_optbool:
  forall ob, of_optbool (option_map negb ob) = notbool (of_optbool ob).
admit.
Defined.

Theorem negate_cmp:
  forall c x y,
  cmp (negate_comparison c) x y = notbool (cmp c x y).
admit.
Defined.

Theorem negate_cmpu:
  forall valid_ptr c x y,
  cmpu valid_ptr (negate_comparison c) x y =
    notbool (cmpu valid_ptr c x y).
admit.
Defined.

Theorem swap_cmp_bool:
  forall c x y,
  cmp_bool (swap_comparison c) x y = cmp_bool c y x.
admit.
Defined.

Theorem swap_cmpu_bool:
  forall valid_ptr c x y,
  cmpu_bool valid_ptr (swap_comparison c) x y =
    cmpu_bool valid_ptr c y x.
admit.
Defined.

Theorem swap_cmpl_bool:
  forall c x y,
  cmpl_bool (swap_comparison c) x y = cmpl_bool c y x.
admit.
Defined.

Theorem swap_cmplu_bool:
  forall valid_ptr c x y,
  cmplu_bool valid_ptr (swap_comparison c) x y = cmplu_bool valid_ptr c y x.
admit.
Defined.

Theorem negate_cmpf_eq:
  forall v1 v2, notbool (cmpf Cne v1 v2) = cmpf Ceq v1 v2.
admit.
Defined.

Theorem negate_cmpf_ne:
  forall v1 v2, notbool (cmpf Ceq v1 v2) = cmpf Cne v1 v2.
admit.
Defined.

Theorem cmpf_le:
  forall v1 v2, cmpf Cle v1 v2 = or (cmpf Clt v1 v2) (cmpf Ceq v1 v2).
admit.
Defined.

Theorem cmpf_ge:
  forall v1 v2, cmpf Cge v1 v2 = or (cmpf Cgt v1 v2) (cmpf Ceq v1 v2).
admit.
Defined.

Theorem cmp_ne_0_optbool:
  forall ob, cmp Cne (of_optbool ob) (Vint Int.zero) = of_optbool ob.
admit.
Defined.

Theorem cmp_eq_1_optbool:
  forall ob, cmp Ceq (of_optbool ob) (Vint Int.one) = of_optbool ob.
admit.
Defined.

Theorem cmp_eq_0_optbool:
  forall ob, cmp Ceq (of_optbool ob) (Vint Int.zero) = of_optbool (option_map negb ob).
admit.
Defined.

Theorem cmp_ne_1_optbool:
  forall ob, cmp Cne (of_optbool ob) (Vint Int.one) = of_optbool (option_map negb ob).
admit.
Defined.

Theorem cmpu_ne_0_optbool:
  forall valid_ptr ob,
  cmpu valid_ptr Cne (of_optbool ob) (Vint Int.zero) = of_optbool ob.
admit.
Defined.

Theorem cmpu_eq_1_optbool:
  forall valid_ptr ob,
  cmpu valid_ptr Ceq (of_optbool ob) (Vint Int.one) = of_optbool ob.
admit.
Defined.

Theorem cmpu_eq_0_optbool:
  forall valid_ptr ob,
  cmpu valid_ptr Ceq (of_optbool ob) (Vint Int.zero) = of_optbool (option_map negb ob).
admit.
Defined.

Theorem cmpu_ne_1_optbool:
  forall valid_ptr ob,
  cmpu valid_ptr Cne (of_optbool ob) (Vint Int.one) = of_optbool (option_map negb ob).
admit.
Defined.

Lemma zero_ext_and:
  forall n v,
  0 <= n ->
  Val.zero_ext n v = Val.and v (Vint (Int.repr (two_p n - 1))).
admit.
Defined.

Lemma zero_ext_andl:
  forall n v,
  0 <= n ->
  Val.zero_ext_l n v = Val.andl v (Vlong (Int64.repr (two_p n - 1))).
admit.
Defined.

Lemma rolm_lt_zero:
  forall v, rolm v Int.one Int.one = cmp Clt v (Vint Int.zero).
admit.
Defined.

Lemma rolm_ge_zero:
  forall v,
  xor (rolm v Int.one Int.one) (Vint Int.one) = cmp Cge v (Vint Int.zero).
admit.
Defined.

 

Inductive lessdef: val -> val -> Prop :=
  | lessdef_refl: forall v, lessdef v v
  | lessdef_undef: forall v, lessdef Vundef v.

Lemma lessdef_same:
  forall v1 v2, v1 = v2 -> lessdef v1 v2.
admit.
Defined.

Lemma lessdef_trans:
  forall v1 v2 v3, lessdef v1 v2 -> lessdef v2 v3 -> lessdef v1 v3.
admit.
Defined.

Inductive lessdef_list: list val -> list val -> Prop :=
  | lessdef_list_nil:
      lessdef_list nil nil
  | lessdef_list_cons:
      forall v1 v2 vl1 vl2,
      lessdef v1 v2 -> lessdef_list vl1 vl2 ->
      lessdef_list (v1 :: vl1) (v2 :: vl2).

Global Hint Resolve lessdef_refl lessdef_undef lessdef_list_nil lessdef_list_cons : core.

Lemma lessdef_list_inv:
  forall vl1 vl2, lessdef_list vl1 vl2 -> vl1 = vl2 \/ In Vundef vl1.
admit.
Defined.

Lemma lessdef_list_trans:
  forall vl1 vl2, lessdef_list vl1 vl2 -> forall vl3, lessdef_list vl2 vl3 -> lessdef_list vl1 vl3.
admit.
Defined.

 

Lemma load_result_lessdef:
  forall chunk v1 v2,
  lessdef v1 v2 -> lessdef (load_result chunk v1) (load_result chunk v2).
admit.
Defined.

Lemma zero_ext_lessdef:
  forall n v1 v2, lessdef v1 v2 -> lessdef (zero_ext n v1) (zero_ext n v2).
admit.
Defined.

Lemma sign_ext_lessdef:
  forall n v1 v2, lessdef v1 v2 -> lessdef (sign_ext n v1) (sign_ext n v2).
admit.
Defined.

Lemma singleoffloat_lessdef:
  forall v1 v2, lessdef v1 v2 -> lessdef (singleoffloat v1) (singleoffloat v2).
admit.
Defined.

Lemma add_lessdef:
  forall v1 v1' v2 v2',
  lessdef v1 v1' -> lessdef v2 v2' -> lessdef (add v1 v2) (add v1' v2').
admit.
Defined.

Lemma addl_lessdef:
  forall v1 v1' v2 v2',
  lessdef v1 v1' -> lessdef v2 v2' -> lessdef (addl v1 v2) (addl v1' v2').
admit.
Defined.

Lemma cmpu_bool_lessdef:
  forall valid_ptr valid_ptr' c v1 v1' v2 v2' b,
  (forall b ofs, valid_ptr b ofs = true -> valid_ptr' b ofs = true) ->
  lessdef v1 v1' -> lessdef v2 v2' ->
  cmpu_bool valid_ptr c v1 v2 = Some b ->
  cmpu_bool valid_ptr' c v1' v2' = Some b.
admit.
Defined.

Lemma cmplu_bool_lessdef:
  forall valid_ptr valid_ptr' c v1 v1' v2 v2' b,
  (forall b ofs, valid_ptr b ofs = true -> valid_ptr' b ofs = true) ->
  lessdef v1 v1' -> lessdef v2 v2' ->
  cmplu_bool valid_ptr c v1 v2 = Some b ->
  cmplu_bool valid_ptr' c v1' v2' = Some b.
admit.
Defined.

Lemma of_optbool_lessdef:
  forall ob ob',
  (forall b, ob = Some b -> ob' = Some b) ->
  lessdef (of_optbool ob) (of_optbool ob').
admit.
Defined.

Lemma longofwords_lessdef:
  forall v1 v2 v1' v2',
  lessdef v1 v1' -> lessdef v2 v2' -> lessdef (longofwords v1 v2) (longofwords v1' v2').
admit.
Defined.

Lemma loword_lessdef:
  forall v v', lessdef v v' -> lessdef (loword v) (loword v').
admit.
Defined.

Lemma hiword_lessdef:
  forall v v', lessdef v v' -> lessdef (hiword v) (hiword v').
admit.
Defined.

Lemma offset_ptr_zero:
  forall v, lessdef (offset_ptr v Ptrofs.zero) v.
admit.
Defined.

Lemma offset_ptr_assoc:
  forall v d1 d2, offset_ptr (offset_ptr v d1) d2 = offset_ptr v (Ptrofs.add d1 d2).
admit.
Defined.

Lemma lessdef_normalize:
  forall v ty, lessdef (normalize v ty) v.
admit.
Defined.

Lemma normalize_lessdef:
  forall v v' ty, lessdef v v' -> lessdef (normalize v ty) (normalize v' ty).
admit.
Defined.

Lemma select_lessdef:
  forall ob ob' v1 v1' v2 v2' ty,
  ob = None \/ ob = ob' ->
  lessdef v1 v1' -> lessdef v2 v2' ->
  lessdef (select ob v1 v2 ty) (select ob' v1' v2' ty).
admit.
Defined.

 

 

Definition meminj : Type := block -> option (block * Z).

 

Inductive inject (mi: meminj): val -> val -> Prop :=
  | inject_int:
      forall i, inject mi (Vint i) (Vint i)
  | inject_long:
      forall i, inject mi (Vlong i) (Vlong i)
  | inject_float:
      forall f, inject mi (Vfloat f) (Vfloat f)
  | inject_single:
      forall f, inject mi (Vsingle f) (Vsingle f)
  | inject_ptr:
      forall b1 ofs1 b2 ofs2 delta,
      mi b1 = Some (b2, delta) ->
      ofs2 = Ptrofs.add ofs1 (Ptrofs.repr delta) ->
      inject mi (Vptr b1 ofs1) (Vptr b2 ofs2)
  | val_inject_undef: forall v,
      inject mi Vundef v.

Global Hint Constructors inject : core.

Inductive inject_list (mi: meminj): list val -> list val-> Prop:=
  | inject_list_nil :
      inject_list mi nil nil
  | inject_list_cons : forall v v' vl vl' ,
      inject mi v v' -> inject_list mi vl vl'->
      inject_list mi (v :: vl) (v' :: vl').

Global Hint Resolve inject_list_nil inject_list_cons : core.

Lemma inject_ptrofs:
  forall mi i, inject mi (Vptrofs i) (Vptrofs i).
admit.
Defined.

Global Hint Resolve inject_ptrofs : core.

Section VAL_INJ_OPS.

Variable f: meminj.

Lemma load_result_inject:
  forall chunk v1 v2,
  inject f v1 v2 ->
  inject f (Val.load_result chunk v1) (Val.load_result chunk v2).
admit.
Defined.

Remark add_inject:
  forall v1 v1' v2 v2',
  inject f v1 v1' ->
  inject f v2 v2' ->
  inject f (Val.add v1 v2) (Val.add v1' v2').
admit.
Defined.

Remark sub_inject:
  forall v1 v1' v2 v2',
  inject f v1 v1' ->
  inject f v2 v2' ->
  inject f (Val.sub v1 v2) (Val.sub v1' v2').
admit.
Defined.

Remark addl_inject:
  forall v1 v1' v2 v2',
  inject f v1 v1' ->
  inject f v2 v2' ->
  inject f (Val.addl v1 v2) (Val.addl v1' v2').
admit.
Defined.

Remark subl_inject:
  forall v1 v1' v2 v2',
  inject f v1 v1' ->
  inject f v2 v2' ->
  inject f (Val.subl v1 v2) (Val.subl v1' v2').
admit.
Defined.

Lemma offset_ptr_inject:
  forall v v' ofs, inject f v v' -> inject f (offset_ptr v ofs) (offset_ptr v' ofs).
admit.
Defined.

Lemma cmp_bool_inject:
  forall c v1 v2 v1' v2' b,
  inject f v1 v1' ->
  inject f v2 v2' ->
  Val.cmp_bool c v1 v2 = Some b ->
  Val.cmp_bool c v1' v2' = Some b.
admit.
Defined.

Variable (valid_ptr1 valid_ptr2 : block -> Z -> bool).

Let weak_valid_ptr1 b ofs := valid_ptr1 b ofs || valid_ptr1 b (ofs - 1).
Let weak_valid_ptr2 b ofs := valid_ptr2 b ofs || valid_ptr2 b (ofs - 1).

Hypothesis valid_ptr_inj:
  forall b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  valid_ptr1 b1 (Ptrofs.unsigned ofs) = true ->
  valid_ptr2 b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true.

Hypothesis weak_valid_ptr_inj:
  forall b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  weak_valid_ptr1 b1 (Ptrofs.unsigned ofs) = true ->
  weak_valid_ptr2 b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true.

Hypothesis weak_valid_ptr_no_overflow:
  forall b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  weak_valid_ptr1 b1 (Ptrofs.unsigned ofs) = true ->
  0 <= Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) <= Ptrofs.max_unsigned.

Hypothesis valid_different_ptrs_inj:
  forall b1 ofs1 b2 ofs2 b1' delta1 b2' delta2,
  b1 <> b2 ->
  valid_ptr1 b1 (Ptrofs.unsigned ofs1) = true ->
  valid_ptr1 b2 (Ptrofs.unsigned ofs2) = true ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  b1' <> b2' \/
  Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta1)) <> Ptrofs.unsigned (Ptrofs.add ofs2 (Ptrofs.repr delta2)).

Lemma cmpu_bool_inject:
  forall c v1 v2 v1' v2' b,
  inject f v1 v1' ->
  inject f v2 v2' ->
  Val.cmpu_bool valid_ptr1 c v1 v2 = Some b ->
  Val.cmpu_bool valid_ptr2 c v1' v2' = Some b.
admit.
Defined.

Lemma cmplu_bool_inject:
  forall c v1 v2 v1' v2' b,
  inject f v1 v1' ->
  inject f v2 v2' ->
  Val.cmplu_bool valid_ptr1 c v1 v2 = Some b ->
  Val.cmplu_bool valid_ptr2 c v1' v2' = Some b.
admit.
Defined.

Lemma longofwords_inject:
  forall v1 v2 v1' v2',
  inject f v1 v1' -> inject f v2 v2' -> inject f (Val.longofwords v1 v2) (Val.longofwords v1' v2').
admit.
Defined.

Lemma loword_inject:
  forall v v', inject f v v' -> inject f (Val.loword v) (Val.loword v').
admit.
Defined.

Lemma hiword_inject:
  forall v v', inject f v v' -> inject f (Val.hiword v) (Val.hiword v').
admit.
Defined.

Lemma normalize_inject:
  forall v v' ty, inject f v v' -> inject f (normalize v ty) (normalize v' ty).
admit.
Defined.

Lemma select_inject:
  forall ob ob' v1 v1' v2 v2' ty,
  ob = None \/ ob = ob' ->
  inject f v1 v1' -> inject f v2 v2' ->
  inject f (select ob v1 v2 ty) (select ob' v1' v2' ty).
admit.
Defined.

End VAL_INJ_OPS.

End Val.

Notation meminj := Val.meminj.

 

Definition inject_incr (f1 f2: meminj) : Prop :=
  forall b b' delta, f1 b = Some(b', delta) -> f2 b = Some(b', delta).

Lemma inject_incr_refl :
   forall f , inject_incr f f .
admit.
Defined.

Lemma inject_incr_trans :
  forall f1 f2 f3,
  inject_incr f1 f2 -> inject_incr f2 f3 -> inject_incr f1 f3 .
admit.
Defined.

Lemma val_inject_incr:
  forall f1 f2 v v',
  inject_incr f1 f2 ->
  Val.inject f1 v v' ->
  Val.inject f2 v v'.
admit.
Defined.

Lemma val_inject_list_incr:
  forall f1 f2 vl vl' ,
  inject_incr f1 f2 -> Val.inject_list f1 vl vl' ->
  Val.inject_list f2 vl vl'.
admit.
Defined.

Global Hint Resolve inject_incr_refl val_inject_incr val_inject_list_incr : core.

Lemma val_inject_lessdef:
  forall v1 v2, Val.lessdef v1 v2 <-> Val.inject (fun b => Some(b, 0)) v1 v2.
admit.
Defined.

Lemma val_inject_list_lessdef:
  forall vl1 vl2, Val.lessdef_list vl1 vl2 <-> Val.inject_list (fun b => Some(b, 0)) vl1 vl2.
admit.
Defined.

 

Definition inject_id : meminj := fun b => Some(b, 0).

Lemma val_inject_id:
  forall v1 v2,
  Val.inject inject_id v1 v2 <-> Val.lessdef v1 v2.
admit.
Defined.

 

Definition compose_meminj (f f': meminj) : meminj :=
  fun b =>
    match f b with
    | None => None
    | Some(b', delta) =>
        match f' b' with
        | None => None
        | Some(b'', delta') => Some(b'', delta + delta')
        end
    end.

Lemma val_inject_compose:
  forall f f' v1 v2 v3,
  Val.inject f v1 v2 -> Val.inject f' v2 v3 ->
  Val.inject (compose_meminj f f') v1 v3.
admit.
Defined.

End Values.

End compcert_DOT_common_DOT_Values_WRAPPED.
Module Export compcert_DOT_common_DOT_Values.
Module Export compcert.
Module Export common.
Module Export Values.
Include compcert_DOT_common_DOT_Values_WRAPPED.Values.
End Values.

End common.

End compcert.

End compcert_DOT_common_DOT_Values.
Require Coq.Logic.ClassicalFacts.
Require Coq.Logic.FunctionalExtensionality.
Require VST.msl.Axioms.
Require Coq.Logic.EqdepFacts.
Require VST.msl.Extensionality.
Require VST.msl.base.
Require VST.msl.sig_isomorphism.
Require VST.msl.functors.
Require Coq.funind.Recdef.
Require Coq.Wellfounded.Wellfounded.
Require VST.msl.ageable.
Require VST.msl.knot.
Require VST.msl.knot_full_variant.
Require VST.msl.predicates_hered.
Require VST.msl.knot_shims.
Require VST.msl.eq_dec.
Require VST.msl.sepalg.
Require Coq.Structures.GenericMinMax.
Require VST.msl.boolean_alg.
Require Coq.Numbers.Natural.Peano.NPeano.
Require Coq.Arith.Max.
Require VST.msl.tree_shares.

Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.
Import compcert.lib.Integers.
Import compcert.common.Values.

Inductive quantity : Type := Q32 | Q64.

Inductive memval: Type :=
  | Undef: memval
  | Byte: byte -> memval
  | Fragment: val -> quantity -> nat -> memval.

Export compcert.common.AST.
Module Export Ctypes.
Import compcert.lib.Coqlib.

Inductive signedness : Type :=
  | Signed: signedness
  | Unsigned: signedness.

Inductive intsize : Type :=
  | I8: intsize
  | I16: intsize
  | I32: intsize
  | IBool: intsize.

Inductive floatsize : Type :=
  | F32: floatsize
  | F64: floatsize.

Record attr : Type := mk_attr {
  attr_volatile: bool;
  attr_alignas: option N
}.

Inductive type : Type :=
  | Tvoid: type
  | Tint: intsize -> signedness -> attr -> type
  | Tlong: signedness -> attr -> type
  | Tfloat: floatsize -> attr -> type
  | Tpointer: type -> attr -> type
  | Tarray: type -> Z -> attr -> type
  | Tfunction: typelist -> type -> calling_convention -> type
  | Tstruct: ident -> attr -> type
  | Tunion: ident -> attr -> type
with typelist : Type :=
  | Tnil: typelist
  | Tcons: type -> typelist -> typelist.

End Ctypes.
Module Export ghost.
Import VST.msl.sepalg.

Class Ghost := { G : Type; valid : G -> Prop;
  Join_G :> Join G; Sep_G :> Sep_alg G; Perm_G :> Perm_alg G;

  join_valid : forall a b c, join a b c -> valid c -> valid a }.

Import VST.msl.base.

Section JOIN_EQUIV.

  Instance Join_equiv (A: Type) : Join A := fun x y z => x=y/\y=z.
End JOIN_EQUIV.

Section SepAlgProd.

  Variables (A: Type) (Ja: Join A).
  Variables (B: Type) (Jb: Join B) .

  Instance Join_prod : Join (A*B) :=
               fun (x y z:A*B) =>  join (fst x) (fst y) (fst z) /\ join (snd x) (snd y) (snd z).

End SepAlgProd.
Existing Instance Join_prod.

Module Type KNOT_FULL_BASIC_INPUT.
End KNOT_FULL_BASIC_INPUT.

Module Type KNOT_FULL_SA_INPUT.
  Declare Module KI: KNOT_FULL_BASIC_INPUT.
End KNOT_FULL_SA_INPUT.
Module Export psepalg.

Section DISCRETE.

  Instance Join_discrete (A : Type): Join A := fun a1 a2 a3 : A => False.

  Instance Perm_discrete (A: Type)  : @Perm_alg A (Join_discrete A).
admit.
Defined.
End DISCRETE.

Set Implicit Arguments.

Section SA_LOWER.
  Variable A : Type.
  Variable Pj_A: Join A.
  Variable PA_A : Perm_alg A.

  Inductive lower_join: option A -> option A -> option A -> Prop :=
  | lower_None1: forall a, lower_join None a a
  | lower_None2: forall a, lower_join a None a
  | lower_Some: forall a1 a2 a3,  join a1 a2 a3 ->
        lower_join (Some a1) (Some a2) (Some a3).

  Instance Join_lower: Join (option A) := lower_join.

  Instance Perm_lower: @Perm_alg (option A) Join_lower.
  Proof.
   constructor; intros.

   inv H; inv H0; try constructor.
f_equal.
  apply (join_eq H1 H3).

    icase d; [ |  exists c; inv H; inv H0; split; constructor; auto].
    icase e; [ | exists a; inv H0; inv H; split; constructor; auto].
    icase c; [ | exists b; inv H; inv H0; split; constructor; auto].
    icase a; [ | exists (Some a1); inv H; inv H0; split; try constructor; auto].
    icase b; [ | exists (Some a2); inv H; inv H0; split; constructor; auto].
    assert (join a a3 a0) by (inv H; auto).
    assert (join a0 a2 a1) by (inv H0; auto).
    destruct (join_assoc H1 H2) as [f [? ?]]; exists (Some f); split; constructor; auto.

    inv H; constructor; auto.

    inv H; inv H0; auto.
f_equal.
apply (join_positivity H1 H4).
 Qed.

 Instance Sep_lower: @Sep_alg _ Join_lower.
admit.
Defined.

End SA_LOWER.

Existing Instance Join_lower.
Existing Instance Sep_lower.

Instance Perm_option (T : Type)  : @Perm_alg (option T) (@Join_lower T (@Join_discrete T)) :=
    @Perm_lower T  (@Join_discrete T) (Perm_discrete T).

End psepalg.
Import VST.msl.boolean_alg.

Module Share : SHARE_MODEL := tree_shares.Share.

Definition share : Type := Share.t.
Export VST.msl.ageable.
Export VST.msl.knot_shims.
Export VST.msl.predicates_hered.
Export VST.msl.functors.

Export MixVariantFunctor.
Export MixVariantFunctorGenerator.

Definition nonempty_share (sh: share) :=
       sepalg.nonidentity sh.
Definition readable_share (sh: share) :=
       nonempty_share (Share.glb Share.Rsh sh).

Module Type ADR_VAL.
Parameter address : Type.

Parameter kind: Type.
End ADR_VAL.

Inductive TypeTree: Type :=
  | ConstType: Type -> TypeTree
  | Mpred: TypeTree
  | DependentType: nat -> TypeTree
  | ProdType: TypeTree -> TypeTree -> TypeTree
  | ArrowType: TypeTree -> TypeTree -> TypeTree
  | SigType: forall (I : Type), (I -> TypeTree) -> TypeTree
  | PiType: forall (I : Type), (I -> TypeTree) -> TypeTree
  | ListType: TypeTree -> TypeTree.

Definition dependent_type_functor_rec (ts: list Type): TypeTree -> functor :=
  fix dtfr (T: TypeTree): functor :=
  match T with
  | ConstType A => fconst A
  | Mpred => fidentity
  | DependentType n => fconst (nth n ts unit)
  | ProdType T1 T2 => fpair (dtfr T1) (dtfr T2)
  | ArrowType T1 T2 => ffunc (dtfr T1) (dtfr T2)
  | SigType _ f => fsig (fun i => dtfr (f i))
  | PiType _ f => fpi (fun i => dtfr (f i))
  | ListType T => flist (dtfr T)
  end.

Definition fpreds: functor :=
  fsig (fun T: TypeTree =>
    fpi (fun ts: list Type => dependent_type_functor_rec ts T)).

Module Type STRAT_MODEL.
  Declare Module AV : ADR_VAL.
  Import AV.

  Inductive res (PRED : Type) : Type :=
    | NO':  forall sh: Share.t, ~(readable_share sh) -> res PRED
    | YES': forall sh: Share.t, readable_share sh -> kind -> fpreds PRED -> res PRED
    | PURE': kind -> fpreds PRED -> res PRED.

  Definition res_fmap (A B:Type) (f:A->B) (g:B->A)(x:res A) : res B :=
    match x with
      | NO' rsh nsh => NO' B rsh nsh
      | YES' sh rsh k pds => YES' B sh rsh k (fmap fpreds f g pds)
      | PURE' k pds => PURE' B k (fmap fpreds f g pds)
    end.
  Axiom ff_res : functorFacts res res_fmap.
  Definition f_res : functor := Functor ff_res.

  Definition ghost (PRED : Type) : Type :=
    list (option ({g: Ghost & {a: @G g | ghost.valid a}} * fpreds PRED)%type).

  Definition ghost_fmap (A B:Type) (f:A->B) (g:B->A)(x:ghost A) : ghost B :=
    fmap (flist (foption (fpair (fconst _) fpreds))) f g x.

  Axiom ff_ghost : functorFacts ghost ghost_fmap.
  Definition f_ghost : functor := Functor ff_ghost.

  Definition f_pre_rmap : functor :=
    fpair (ffunc (fconst address) f_res) f_ghost.

End STRAT_MODEL.

Module StratModel (AV' : ADR_VAL) : STRAT_MODEL with Module AV:=AV'.
  Module AV := AV'.
  Import AV.

  Definition preds: functor :=
    fsig (fun T: TypeTree =>
      fpi (fun ts: list Type => dependent_type_functor_rec ts T)).

  Inductive res (PRED : Type) : Type :=
    | NO':  forall sh: Share.t, ~(readable_share sh) -> res PRED
    | YES': forall sh: Share.t, readable_share sh -> kind -> preds PRED -> res PRED
    | PURE': kind -> preds PRED -> res PRED.

  Definition res_fmap (A B:Type) (f:A->B) (g:B->A)(x:res A) : res B :=
    match x with
      | NO' rsh nsh => NO' B rsh nsh
      | YES' sh rsh k pds => YES' B sh rsh k (fmap preds f g pds)
      | PURE' k pds => PURE' B k (fmap preds f g pds)
    end.

  Lemma ff_res : functorFacts res res_fmap.
admit.
Defined.

  Definition f_res : functor := Functor ff_res.

  Definition ghost (PRED : Type) : Type :=
    list (option ({g: Ghost & {a: @G g | ghost.valid a}} * fpreds PRED)%type).

  Definition ghost_fmap (A B:Type) (f:A->B) (g:B->A)(x:ghost A) : ghost B :=
    fmap (flist (foption (fpair (fconst _) fpreds))) f g x.

  Lemma ff_ghost : functorFacts ghost ghost_fmap.
admit.
Defined.

  Definition f_ghost : functor := Functor ff_ghost.
  Definition f_pre_rmap : functor :=
    fpair (ffunc (fconst address) f_res) f_ghost.

End StratModel.

Module Type RMAPS.
  Declare Module AV:ADR_VAL.

  Parameter rmap : Type.
  Axiom ag_rmap: ageable rmap.
 Existing Instance ag_rmap.

  Inductive preds : Type :=
    SomeP : forall A : TypeTree,
      (forall ts: list Type, dependent_type_functor_rec ts A (pred rmap)) -> preds.

  Definition NoneP := SomeP (ConstType unit) (fun _ => tt).

  Definition preds_fmap (f g: pred rmap -> pred rmap) (x:preds) : preds :=
    match x with SomeP A Q => SomeP A (fmap (fpi _) f g Q)
    end.

  Definition ghost : Type := list (option ({g: Ghost & {a: @G g | ghost.valid a}} * preds)%type).

  Instance preds_join : Join _ := Join_equiv preds.

  Inductive ghost_elem_join : Join {g: Ghost & {a: @G g | ghost.valid a}} :=
  | elem_join_I g a b c va vb vc: join a b c ->
    ghost_elem_join (existT _ g (exist _ a va)) (existT _ g (exist _ b vb))
                    (existT _ g (exist _ c vc)).
  Existing Instance ghost_elem_join.

  Inductive ghost_join : Join ghost :=
  | ghost_join_nil_l m: ghost_join nil m m
  | ghost_join_nil_r m: ghost_join m nil m
  | ghost_join_cons a1 a2 m1 m2 a3 m3: join a1 a2 a3 -> ghost_join m1 m2 m3 ->
      ghost_join (a1 :: m1) (a2 :: m2) (a3 :: m3).
  Existing Instance ghost_join.

  Definition ghost_fmap (f g:pred rmap -> pred rmap)(x:ghost) : ghost :=
    map (option_map (fun '(a, b) => (a, preds_fmap f g b))) x.

  Program Definition approx (n:nat) (p: pred rmap) : pred rmap :=
    fun w => level w < n /\ p w.
Admit Obligations.

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
  End TyFSA.

  Module K := Knot_MixVariantHeredProp(TyF).

  Definition rmap := K.knot.
  Instance ag_rmap : ageable rmap := K.ageable_knot.

  Inductive preds : Type :=
    SomeP : forall A : TypeTree,
    (forall ts: list Type, dependent_type_functor_rec ts A (pred rmap)) -> preds.

  Definition NoneP := SomeP (ConstType unit) (fun _ => tt).

  Definition ghost : Type := list (option ({g: Ghost & {a: @G g | ghost.valid a}} * preds)%type).

  Instance preds_join : Join _ := Join_equiv preds.

  Inductive ghost_elem_join : Join {g: Ghost & {a: @G g | ghost.valid a}} :=
  | elem_join_I g a b c va vb vc: join a b c ->
    ghost_elem_join (existT _ g (exist _ a va)) (existT _ g (exist _ b vb))
                    (existT _ g (exist _ c vc)).
  Existing Instance ghost_elem_join.

  Inductive ghost_join : Join ghost :=
  | ghost_join_nil_l m: ghost_join nil m m
  | ghost_join_nil_r m: ghost_join m nil m
  | ghost_join_cons a1 a2 m1 m2 a3 m3: join a1 a2 a3 -> ghost_join m1 m2 m3 ->
      ghost_join (a1 :: m1) (a2 :: m2) (a3 :: m3).
  Definition preds_fmap (f g:(pred rmap)->(pred rmap)) (x:preds) : preds :=
    match x with SomeP A ls => SomeP A (fmap (fpi _) f g ls) end.

  Definition ghost_fmap (f g:pred rmap -> pred rmap)(x:ghost) : ghost :=
    map (option_map (fun '(a, b) => (a, preds_fmap f g b))) x.

  Program Definition approx (n:nat) (p: (pred rmap)) : (pred rmap) :=
    fun w => level w < n /\ p w.
Admit Obligations.

End Rmaps.

Module Rmaps_Lemmas (R0: RMAPS).

Ltac inj_pair_tac :=
 match goal with H: (@existT ?U ?P ?p ?x = @existT _ _ _ ?y) |- _ =>
   generalize (@inj_pair2 U P p x y H); clear H; intro; try (subst x || subst y)
 end.

End Rmaps_Lemmas.
Import compcert.lib.Coqlib.

Definition address : Type := (block * Z)%type.

Definition typesig := (list type * type)%type.

Inductive kind : Type := VAL : memval -> kind
                                   | LK : forall n i : Z, kind
                                   | FUN:  typesig -> calling_convention -> kind.

Module CompCert_AV <: ADR_VAL.

Definition address := address.
Definition kind := kind.

End CompCert_AV.

Module R := Rmaps (CompCert_AV).
Module RML := Rmaps_Lemmas(R).

Export RML.
Export R.

Fixpoint make_join (a c : ghost) : ghost :=
  match a, c with
  | nil, _ => c
  | _, nil => nil
  | None :: a', x :: c' => x :: make_join a' c'
  | _ :: a', None :: c' => None :: make_join a' c'
  | Some (ga, pa) :: a', Some (gc, _) :: c' => Some (gc, pa) :: make_join a' c'
  end.

Global Program Instance pos_PCM (P : Ghost) : Ghost := { G := option (share * G);
  valid a := match a with Some (sh, _) => sh <> Share.bot | _ => True end;
  Join_G a b c := match a, b, c with
  | Some (sha, a'), Some (shb, b'), Some (shc, c') =>
      sha <> Share.bot /\ shb <> Share.bot /\ sepalg.join sha shb shc /\ join a' b' c'
  | Some (sh, a), None, Some c' | None, Some (sh, a), Some c' => c' = (sh, a)
  | None, None, None => True
  | _, _, _ => False
  end  }.
Admit Obligations.

Definition completable {P : Ghost} (a: @G (pos_PCM P)) r := exists x, join a x (Some (Share.top, r)).

Global Program Instance ref_PCM (P : Ghost) : Ghost :=
{ valid a := valid (fst a) /\ match snd a with Some r => completable (fst a) r | None => True end;
  Join_G a b c := @Join_G (pos_PCM P) (fst a) (fst b) (fst c) /\
    @psepalg.Join_lower _ (psepalg.Join_discrete _) (snd a) (snd b) (snd c)  }.
Admit Obligations.

Program Instance exclusive_PCM A : Ghost :=
  { valid a := True; Join_G := Join_lower (Join_discrete A)  }.

Definition ext_PCM Z : Ghost := ref_PCM (exclusive_PCM Z).

Lemma valid_ext_ref : forall {Z} (ora : Z), @valid (ext_PCM _) (None, Some (Some ora)).
admit.
Defined.

Definition ext_ref {Z} (ora : Z) : {g : Ghost & {a : G | valid a}} :=
  existT _ (ext_PCM _) (exist _ _ (valid_ext_ref ora)).

Lemma make_join_ext : forall (ora : Z) a c n,
  join_sub (Some (ext_ref ora, NoneP) :: nil) c ->
  joins (ghost_fmap (approx n) (approx n) a) (ghost_fmap (approx n) (approx n) c) ->
  join_sub (Some (ext_ref ora, NoneP) :: nil) (make_join a c).
Proof.
  destruct a; auto; simpl.
  intros ?? [? HC] [? J].
  inv J.
  {
 destruct c; inv H1; inv HC.
}
  destruct c; inv H1.
  inv H2.
  {
 destruct o; inv H0; inv HC.
    *
 eexists; constructor; constructor.
    *
 eexists; constructor; eauto; constructor.
}
  {
 destruct o0; inv H1; inv HC.
    inv H3.
}
  destruct o as [[]|], o0 as [[]|]; inv H; inv H0.
  destruct a0; inv H1; simpl in *.
  inv H0.
  assert (@ghost.valid (ext_PCM Z) (None, None)) as Hv.
  {
 simpl; auto.
}
  inv HC.
  -
 eexists; constructor; constructor.
    destruct p; inv H1; inj_pair_tac.
    instantiate (1 := (existT _ (ext_PCM Z) (exist _ _ Hv), _)); repeat constructor; simpl.
    rewrite <- H0; auto.
