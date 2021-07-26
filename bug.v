(* -*- mode: coq; coq-prog-args: ("-emacs" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/msl" "VST.msl" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/sepcomp" "VST.sepcomp" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/veric" "VST.veric" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/floyd" "VST.floyd" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/progs" "VST.progs" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/concurrency" "VST.concurrency" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/wand_demo" "wand_demo" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/sha" "sha" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/hmacfcf" "hmacfcf" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/tweetnacl20140427" "tweetnacl20140427" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/hmacdrbg" "hmacdrbg" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/aes" "aes" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/mailbox" "mailbox" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/atomics" "atomics" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/lib" "compcert.lib" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/common" "compcert.common" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/x86_32" "compcert.x86_32" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/x86" "compcert.x86" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/cfrontend" "compcert.cfrontend" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/exportclight" "compcert.exportclight" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Flocq" "Flocq" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-top" "bug_01" "-native-compiler" "no" "-native-compiler" "no") -*- *)
(* File reduced by coq-bug-finder from original input, then from 2095 lines to 10 lines, then from 233 lines to 355 lines, then from 342 lines to 9 lines, then from 228 lines to 441 lines, then from 444 lines to 10 lines, then from 209 lines to 618 lines, then from 622 lines to 46 lines, then from 244 lines to 2186 lines, then from 2185 lines to 45 lines, then from 186 lines to 1500 lines, then from 1500 lines to 125 lines, then from 265 lines to 1073 lines, then from 1076 lines to 748 lines, then from 887 lines to 1328 lines, then from 1332 lines to 750 lines, then from 886 lines to 2399 lines, then from 2377 lines to 760 lines, then from 885 lines to 1257 lines, then from 1257 lines to 877 lines, then from 1002 lines to 1435 lines, then from 1438 lines to 956 lines, then from 1042 lines to 1193 lines, then from 1195 lines to 985 lines, then from 1070 lines to 1352 lines, then from 1356 lines to 1003 lines, then from 1089 lines to 2394 lines, then from 2395 lines to 1149 lines, then from 1233 lines to 1831 lines, then from 1834 lines to 1185 lines, then from 1267 lines to 1296 lines, then from 1300 lines to 1177 lines, then from 1253 lines to 1400 lines, then from 1404 lines to 1192 lines, then from 1261 lines to 1570 lines, then from 1573 lines to 1201 lines, then from 1268 lines to 1428 lines, then from 1432 lines to 1214 lines, then from 1279 lines to 2037 lines, then from 2041 lines to 1246 lines, then from 1303 lines to 3101 lines, then from 3100 lines to 1577 lines, then from 1627 lines to 3211 lines, then from 3215 lines to 2816 lines, then from 2681 lines to 1842 lines, then from 1888 lines to 2981 lines, then from 2985 lines to 1844 lines, then from 1889 lines to 4504 lines, then from 4508 lines to 1937 lines, then from 1981 lines to 2732 lines, then from 2736 lines to 1962 lines, then from 2003 lines to 3469 lines, then from 3473 lines to 2164 lines, then from 2202 lines to 7053 lines, then from 7056 lines to 2319 lines, then from 2354 lines to 2436 lines, then from 2439 lines to 2340 lines, then from 2374 lines to 3488 lines, then from 3492 lines to 2362 lines, then from 2396 lines to 2602 lines, then from 2606 lines to 2519 lines *)
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
Require Coq.Classes.Equivalence.
Require Coq.Classes.EquivDec.
Require Coq.Strings.String.
Require Coq.ZArith.ZArith.
Require Coq.ZArith.Znumtheory.
Require Coq.Lists.List.
Require Coq.Bool.Bool.
Require Coq.micromega.Lia.
Require Coq.Relations.Relations.
Require compcert.lib.Coqlib.
Require compcert.lib.Maps.
Module Export compcert_DOT_common_DOT_Errors_WRAPPED.
Module Export Errors.
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 

 
Import Coq.Strings.String.
Import compcert.lib.Coqlib.

Close Scope string_scope.

Set Implicit Arguments.

 

 

Inductive errcode: Type :=
  | MSG: string -> errcode
  | CTX: positive -> errcode     
  | POS: positive -> errcode.
   

Definition errmsg: Type := list errcode.

Definition msg (s: string) : errmsg := MSG s :: nil.

 

 

Inductive res (A: Type) : Type :=
| OK: A -> res A
| Error: errmsg -> res A.

Arguments Error [A].

 

Definition bind (A B: Type) (f: res A) (g: A -> res B) : res B :=
  match f with
  | OK x => g x
  | Error msg => Error msg
  end.

Definition bind2 (A B C: Type) (f: res (A * B)) (g: A -> B -> res C) : res C :=
  match f with
  | OK (x, y) => g x y
  | Error msg => Error msg
  end.

 

Notation "'do' X <- A ; B" := (bind A (fun X => B))
 (at level 200, X ident, A at level 100, B at level 200)
 : error_monad_scope.

Notation "'do' ( X , Y ) <- A ; B" := (bind2 A (fun X Y => B))
 (at level 200, X ident, Y ident, A at level 100, B at level 200)
 : error_monad_scope.

Remark bind_inversion:
  forall (A B: Type) (f: res A) (g: A -> res B) (y: B),
  bind f g = OK y ->
  exists x, f = OK x /\ g x = OK y.
admit.
Defined.

Remark bind2_inversion:
  forall (A B C: Type) (f: res (A*B)) (g: A -> B -> res C) (z: C),
  bind2 f g = OK z ->
  exists x, exists y, f = OK (x, y) /\ g x y = OK z.
admit.
Defined.

 

Definition assertion_failed {A: Type} : res A := Error(msg "Assertion failed").

Notation "'assertion' A ; B" := (if A then B else assertion_failed)
  (at level 200, A at level 100, B at level 200)
  : error_monad_scope.

 

Local Open Scope error_monad_scope.

Fixpoint mmap (A B: Type) (f: A -> res B) (l: list A) {struct l} : res (list B) :=
  match l with
  | nil => OK nil
  | hd :: tl => do hd' <- f hd; do tl' <- mmap f tl; OK (hd' :: tl')
  end.

Remark mmap_inversion:
  forall (A B: Type) (f: A -> res B) (l: list A) (l': list B),
  mmap f l = OK l' ->
  list_forall2 (fun x y => f x = OK y) l l'.
admit.
Defined.

End Errors.

End compcert_DOT_common_DOT_Errors_WRAPPED.
Module Export compcert_DOT_common_DOT_Errors.
Module Export compcert.
Module Export common.
Module Export Errors.
Include compcert_DOT_common_DOT_Errors_WRAPPED.Errors.
End Errors.

End common.

End compcert.

End compcert_DOT_common_DOT_Errors.
Require Flocq.IEEE754.Bits.
Require Flocq.Core.Core.
Require Coq.ZArith.Zquot.
Require Flocq.Core.Digits.
Require Flocq.Calc.Operations.
Require Flocq.Calc.Round.
Require Flocq.Calc.Bracket.
Require Flocq.Prop.Sterbenz.
Require Flocq.IEEE754.Binary.
Require Coq.Reals.Reals.
Require Coq.micromega.Psatz.
Require Flocq.Prop.Round_odd.
Require Coq.Logic.Eqdep_dec.
Require compcert.lib.IEEE754_extra.

Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.
Import compcert.lib.Coqlib.

Fixpoint P_mod_two_p (p: positive) (n: nat) {struct n} : Z :=
  match n with
  | O => 0
  | S m =>
      match p with
      | xH => 1
      | xO q => Z.double (P_mod_two_p q m)
      | xI q => Z.succ_double (P_mod_two_p q m)
      end
  end.

Definition Zshiftin (b: bool) (x: Z) : Z :=
  if b then Z.succ_double x else Z.double x.

Definition Zzero_ext (n: Z) (x: Z) : Z :=
  Z.iter n
    (fun rec x => Zshiftin (Z.odd x) (rec (Z.div2 x)))
    (fun x => 0)
    x.

Definition Zsign_ext (n: Z) (x: Z) : Z :=
  Z.iter (Z.pred n)
    (fun rec x => Zshiftin (Z.odd x) (rec (Z.div2 x)))
    (fun x => if Z.odd x && zlt 0 n then -1 else 0)
    x.
Module Export Archi.

Definition ptr64 := false.

Definition align_int64 := 4%Z.
Definition align_float64 := 4%Z.

Definition default_nan_64 := (true, iter_nat 51 _ xO xH).
Definition default_nan_32 := (true, iter_nat 22 _ xO xH).

Definition choose_nan_64 (l: list (bool * positive)) : bool * positive :=
  match l with nil => default_nan_64 | n :: _ => n end.

Definition choose_nan_32 (l: list (bool * positive)) : bool * positive :=
  match l with nil => default_nan_32 | n :: _ => n end.

Definition float_of_single_preserves_sNaN := false.

End Archi.

Inductive comparison : Type :=
  | Ceq : comparison
  | Cne : comparison
  | Clt : comparison
  | Cle : comparison
  | Cgt : comparison
  | Cge : comparison.

Module Type WORDSIZE.
  Parameter wordsize: nat.
End WORDSIZE.

Module Make(WS: WORDSIZE).

Definition wordsize: nat := WS.wordsize.
Definition modulus : Z := two_power_nat wordsize.
Definition half_modulus : Z := modulus / 2.
Definition max_unsigned : Z := modulus - 1.
Definition max_signed : Z := half_modulus - 1.
Definition min_signed : Z := - half_modulus.

Record int: Type := mkint { intval: Z; intrange: -1 < intval < modulus }.

Definition Z_mod_modulus (x: Z) : Z :=
  match x with
  | Z0 => 0
  | Zpos p => P_mod_two_p p wordsize
  | Zneg p => let r := P_mod_two_p p wordsize in if zeq r 0 then 0 else modulus - r
  end.

Lemma Z_mod_modulus_range':
  forall x, -1 < Z_mod_modulus x < modulus.
admit.
Defined.

Definition unsigned (n: int) : Z := intval n.

Definition signed (n: int) : Z :=
  let x := unsigned n in
  if zlt x half_modulus then x else x - modulus.

Definition repr (x: Z) : int :=
  mkint (Z_mod_modulus x) (Z_mod_modulus_range' x).

Definition zero := repr 0.
Definition one  := repr 1.
Definition mone := repr (-1).

Definition eq (x y: int) : bool :=
  if zeq (unsigned x) (unsigned y) then true else false.
Definition lt (x y: int) : bool :=
  if zlt (signed x) (signed y) then true else false.
Definition ltu (x y: int) : bool :=
  if zlt (unsigned x) (unsigned y) then true else false.

Definition neg (x: int) : int := repr (- unsigned x).

Definition add (x y: int) : int :=
  repr (unsigned x + unsigned y).
Definition sub (x y: int) : int :=
  repr (unsigned x - unsigned y).
Definition mul (x y: int) : int :=
  repr (unsigned x * unsigned y).

Definition divs (x y: int) : int :=
  repr (Z.quot (signed x) (signed y)).
Definition mods (x y: int) : int :=
  repr (Z.rem (signed x) (signed y)).

Definition divu (x y: int) : int :=
  repr (unsigned x / unsigned y).
Definition modu (x y: int) : int :=
  repr ((unsigned x) mod (unsigned y)).

Definition and (x y: int): int := repr (Z.land (unsigned x) (unsigned y)).
Definition or (x y: int): int := repr (Z.lor (unsigned x) (unsigned y)).
Definition xor (x y: int) : int := repr (Z.lxor (unsigned x) (unsigned y)).

Definition not (x: int) : int := xor x mone.

Definition shl (x y: int): int := repr (Z.shiftl (unsigned x) (unsigned y)).
Definition shru (x y: int): int := repr (Z.shiftr (unsigned x) (unsigned y)).
Definition shr (x y: int): int := repr (Z.shiftr (signed x) (unsigned y)).

Definition zero_ext (n: Z) (x: int) : int := repr (Zzero_ext n (unsigned x)).
Definition sign_ext (n: Z) (x: int) : int := repr (Zsign_ext n (unsigned x)).

Definition cmp (c: comparison) (x y: int) : bool :=
  match c with
  | Ceq => eq x y
  | Cne => negb (eq x y)
  | Clt => lt x y
  | Cle => negb (lt y x)
  | Cgt => lt y x
  | Cge => negb (lt x y)
  end.

Definition cmpu (c: comparison) (x y: int) : bool :=
  match c with
  | Ceq => eq x y
  | Cne => negb (eq x y)
  | Clt => ltu x y
  | Cle => negb (ltu y x)
  | Cgt => ltu y x
  | Cge => negb (ltu x y)
  end.

End Make.

Module Export Wordsize_32.
  Definition wordsize := 32%nat.
End Wordsize_32.

Module Int := Make(Wordsize_32).

Notation int := Int.int.

Module Export Wordsize_64.
  Definition wordsize := 64%nat.
End Wordsize_64.

Module Int64.

Include Make(Wordsize_64).

Definition loword (n: int) : Int.int := Int.repr (unsigned n).

End Int64.

Notation int64 := Int64.int.

Module Export Wordsize_Ptrofs.
  Definition wordsize := if Archi.ptr64 then 64%nat else 32%nat.
End Wordsize_Ptrofs.

Module Ptrofs.

Include Make(Wordsize_Ptrofs).

Definition to_int (x: int): Int.int := Int.repr (unsigned x).

Definition to_int64 (x: int): Int64.int := Int64.repr (unsigned x).

Definition of_int (x: Int.int) : int := repr (Int.unsigned x).

Definition of_intu := of_int.

Definition of_ints (x: Int.int) : int := repr (Int.signed x).

Definition of_int64 (x: Int64.int) : int := repr (Int64.unsigned x).

End Ptrofs.

Notation ptrofs := Ptrofs.int.
Import Flocq.IEEE754.Binary.
Import Flocq.IEEE754.Bits.
Import Flocq.Core.Core.
Import compcert.lib.IEEE754_extra.
Import ListNotations.

Definition float := binary64.

Definition float32 := binary32.

Definition cmp_of_comparison (c: comparison) (x: option Datatypes.comparison) : bool :=
  match c with
  | Ceq =>
      match x with Some Eq => true | _ => false end
  | Cne =>
      match x with Some Eq => false | _ => true end
  | Clt =>
      match x with Some Lt => true | _ => false end
  | Cle =>
      match x with Some(Lt|Eq) => true | _ => false end
  | Cgt =>
      match x with Some Gt => true | _ => false end
  | Cge =>
      match x with Some(Gt|Eq) => true | _ => false end
  end.

Definition quiet_nan_64_payload (p: positive) :=
  Z.to_pos (P_mod_two_p (Pos.lor p ((iter_nat xO 51 1%positive))) 52%nat).

Lemma quiet_nan_64_proof: forall p, nan_pl 53 (quiet_nan_64_payload p) = true.
admit.
Defined.

Definition quiet_nan_64 (sp: bool * positive) : {x :float | is_nan _ _ x = true} :=
  let (s, p) := sp in
  exist _ (B754_nan 53 1024 s (quiet_nan_64_payload p) (quiet_nan_64_proof p)) (eq_refl true).

Definition default_nan_64 := quiet_nan_64 Archi.default_nan_64.

Definition quiet_nan_32_payload (p: positive) :=
  Z.to_pos (P_mod_two_p (Pos.lor p ((iter_nat xO 22 1%positive))) 23%nat).

Lemma quiet_nan_32_proof: forall p, nan_pl 24 (quiet_nan_32_payload p) = true.
admit.
Defined.

Definition quiet_nan_32 (sp: bool * positive) : {x :float32 | is_nan _ _ x = true} :=
  let (s, p) := sp in
  exist _ (B754_nan 24 128 s (quiet_nan_32_payload p) (quiet_nan_32_proof p)) (eq_refl true).

Definition default_nan_32 := quiet_nan_32 Archi.default_nan_32.

Local Notation __ := (eq_refl Datatypes.Lt).

Module Export Float.

Definition expand_nan_payload (p: positive) := Pos.shiftl_nat p 29.

Lemma expand_nan_proof (p : positive) :
  nan_pl 24 p = true ->
  nan_pl 53 (expand_nan_payload p) = true.
admit.
Defined.

Definition expand_nan s p H : {x | is_nan _ _ x = true} :=
  exist _ (B754_nan 53 1024 s (expand_nan_payload p) (expand_nan_proof p H)) (eq_refl true).

Definition of_single_nan (f : float32) : { x : float | is_nan _ _ x = true } :=
  match f with
  | B754_nan s p H =>
    if Archi.float_of_single_preserves_sNaN
    then expand_nan s p H
    else quiet_nan_64 (s, expand_nan_payload p)
  | _ => default_nan_64
  end.

Definition reduce_nan_payload (p: positive) :=

  Pos.shiftr_nat (quiet_nan_64_payload p) 29.

Definition to_single_nan (f : float) : { x : float32 | is_nan _ _ x = true } :=
  match f with
  | B754_nan s p H => quiet_nan_32 (s, reduce_nan_payload p)
  | _ => default_nan_32
  end.

Definition neg_nan (f : float) : { x : float | is_nan _ _ x = true } :=
  match f with
  | B754_nan s p H => exist _ (B754_nan 53 1024 (negb s) p H) (eq_refl true)
  | _ => default_nan_64
  end.

Definition abs_nan (f : float) : { x : float | is_nan _ _ x = true } :=
  match f with
  | B754_nan s p H => exist _ (B754_nan 53 1024 false p H) (eq_refl true)
  | _ => default_nan_64
  end.

Definition cons_pl (x: float) (l: list (bool * positive)) :=
  match x with B754_nan s p _ => (s, p) :: l | _ => l end.

Definition binop_nan (x y: float) : {x : float | is_nan _ _ x = true} :=
  quiet_nan_64 (Archi.choose_nan_64 (cons_pl x (cons_pl y []))).

Definition zero: float := B754_zero _ _ false.

Definition neg: float -> float := Bopp _ _ neg_nan.

Definition abs: float -> float := Babs _ _ abs_nan.

Definition add: float -> float -> float :=
  Bplus 53 1024 __ __ binop_nan mode_NE.

Definition sub: float -> float -> float :=
  Bminus 53 1024 __ __ binop_nan mode_NE.

Definition mul: float -> float -> float :=
  Bmult 53 1024 __ __ binop_nan mode_NE.

Definition div: float -> float -> float :=
  Bdiv 53 1024 __ __ binop_nan mode_NE.

Definition compare (f1 f2: float) : option Datatypes.comparison :=
  Bcompare 53 1024 f1 f2.
Definition cmp (c:comparison) (f1 f2: float) : bool :=
  cmp_of_comparison c (compare f1 f2).

Definition of_single: float32 -> float := Bconv _ _ 53 1024 __ __ of_single_nan mode_NE.
Definition to_single: float -> float32 := Bconv _ _ 24 128 __ __ to_single_nan mode_NE.

Definition to_int (f:float): option int :=
  option_map Int.repr (ZofB_range _ _ f Int.min_signed Int.max_signed).
Definition to_intu (f:float): option int :=
  option_map Int.repr (ZofB_range _ _ f 0 Int.max_unsigned).
Definition to_long (f:float): option int64 :=
  option_map Int64.repr (ZofB_range _ _ f Int64.min_signed Int64.max_signed).
Definition to_longu (f:float): option int64 :=
  option_map Int64.repr (ZofB_range _ _ f 0 Int64.max_unsigned).

Definition of_int (n:int): float :=
  BofZ 53 1024 __ __ (Int.signed n).
Definition of_intu (n:int): float:=
  BofZ 53 1024 __ __ (Int.unsigned n).

Definition of_long (n:int64): float :=
  BofZ 53 1024 __ __ (Int64.signed n).
Definition of_longu (n:int64): float:=
  BofZ 53 1024 __ __ (Int64.unsigned n).

Module Export Float32.

Definition neg_nan (f : float32) : { x : float32 | is_nan _ _ x = true } :=
  match f with
  | B754_nan s p H => exist _ (B754_nan 24 128 (negb s) p H) (eq_refl true)
  | _ => default_nan_32
  end.

Definition cons_pl (x: float32) (l: list (bool * positive)) :=
  match x with B754_nan s p _ => (s, p) :: l | _ => l end.

Definition binop_nan (x y: float32) : {x : float32 | is_nan _ _ x = true} :=
  quiet_nan_32 (Archi.choose_nan_32 (cons_pl x (cons_pl y []))).

Definition zero: float32 := B754_zero _ _ false.

Definition neg: float32 -> float32 := Bopp _ _ neg_nan.

Definition add: float32 -> float32 -> float32 :=
  Bplus 24 128 __ __ binop_nan mode_NE.

Definition sub: float32 -> float32 -> float32 :=
  Bminus 24 128 __ __ binop_nan mode_NE.

Definition mul: float32 -> float32 -> float32 :=
  Bmult 24 128 __ __ binop_nan mode_NE.

Definition div: float32 -> float32 -> float32 :=
  Bdiv 24 128 __ __ binop_nan mode_NE.

Definition compare (f1 f2: float32) : option Datatypes.comparison :=
  Bcompare 24 128 f1 f2.
Definition cmp (c:comparison) (f1 f2: float32) : bool :=
  cmp_of_comparison c (compare f1 f2).

Definition to_int (f:float32): option int :=
  option_map Int.repr (ZofB_range _ _ f Int.min_signed Int.max_signed).
Definition to_intu (f:float32): option int :=
  option_map Int.repr (ZofB_range _ _ f 0 Int.max_unsigned).
Definition to_long (f:float32): option int64 :=
  option_map Int64.repr (ZofB_range _ _ f Int64.min_signed Int64.max_signed).
Definition to_longu (f:float32): option int64 :=
  option_map Int64.repr (ZofB_range _ _ f 0 Int64.max_unsigned).

Definition of_int (n:int): float32 :=
  BofZ 24 128 __ __ (Int.signed n).
Definition of_intu (n:int): float32 :=
  BofZ 24 128 __ __ (Int.unsigned n).

Definition of_long (n:int64): float32 :=
  BofZ 24 128 __ __ (Int64.signed n).
Definition of_longu (n:int64): float32 :=
  BofZ 24 128 __ __ (Int64.unsigned n).

Definition ident := positive.

Definition ident_eq := peq.

Record calling_convention : Type := mkcallconv {
  cc_vararg: option Z;
  cc_unproto: bool;
  cc_structret: bool
}.

Inductive memory_chunk : Type :=
  | Mint8signed
  | Mint8unsigned
  | Mint16signed
  | Mint16unsigned
  | Mint32
  | Mint64
  | Mfloat32
  | Mfloat64
  | Many32
  | Many64.

Definition Mptr : memory_chunk := if Archi.ptr64 then Mint64 else Mint32.

Definition block : Type := positive.
Definition eq_block := peq.

Inductive val: Type :=
  | Vundef: val
  | Vint: int -> val
  | Vlong: int64 -> val
  | Vfloat: float -> val
  | Vsingle: float32 -> val
  | Vptr: block -> ptrofs -> val.
Definition Vone: val := Vint Int.one.

Definition Vtrue: val := Vint Int.one.
Definition Vfalse: val := Vint Int.zero.

Definition Vptrofs (n: ptrofs) :=
  if Archi.ptr64 then Vlong (Ptrofs.to_int64 n) else Vint (Ptrofs.to_int n).

Module Export Val.

Definition of_bool (b: bool): val := if b then Vtrue else Vfalse.

Section COMPARISONS.

Variable valid_ptr: block -> Z -> bool.
Let weak_valid_ptr (b: block) (ofs: Z) := valid_ptr b ofs || valid_ptr b (ofs - 1).

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

End COMPARISONS.

Module Export Memdata.

Definition align_chunk (chunk: memory_chunk) : Z :=
  match chunk with
  | Mint8signed => 1
  | Mint8unsigned => 1
  | Mint16signed => 2
  | Mint16unsigned => 2
  | Mint32 => 4
  | Mint64 => 8
  | Mfloat32 => 4
  | Mfloat64 => 4
  | Many32 => 4
  | Many64 => 4
  end.
Import compcert.lib.Maps.

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

Definition noattr := {| attr_volatile := false; attr_alignas := None |}.

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

Lemma intsize_eq: forall (s1 s2: intsize), {s1=s2} + {s1<>s2}.
admit.
Defined.

Definition attr_of_type (ty: type) :=
  match ty with
  | Tvoid => noattr
  | Tint sz si a => a
  | Tlong si a => a
  | Tfloat sz a => a
  | Tpointer elt a => a
  | Tarray elt sz a => a
  | Tfunction args res cc => noattr
  | Tstruct id a => a
  | Tunion id a => a
  end.

Definition change_attributes (f: attr -> attr) (ty: type) : type :=
  match ty with
  | Tvoid => ty
  | Tint sz si a => Tint sz si (f a)
  | Tlong si a => Tlong si (f a)
  | Tfloat sz a => Tfloat sz (f a)
  | Tpointer elt a => Tpointer elt (f a)
  | Tarray elt sz a => Tarray elt sz (f a)
  | Tfunction args res cc => ty
  | Tstruct id a => Tstruct id (f a)
  | Tunion id a => Tunion id (f a)
  end.

Definition remove_attributes (ty: type) : type :=
  change_attributes (fun _ => noattr) ty.

Inductive struct_or_union : Type := Struct | Union.

Definition members : Type := list (ident * type).

Record composite : Type := {
  co_su: struct_or_union;
  co_members: members;
  co_attr: attr;
  co_sizeof: Z;
  co_alignof: Z;
  co_rank: nat;
  co_sizeof_pos: co_sizeof >= 0;
  co_alignof_two_p: exists n, co_alignof = two_power_nat n;
  co_sizeof_alignof: (co_alignof | co_sizeof)
}.

Definition composite_env : Type := PTree.t composite.

Definition typeconv (ty: type) : type :=
  match ty with
  | Tint (I8 | I16 | IBool) _ _ => Tint I32 Signed noattr
  | Tarray t sz a       => Tpointer t noattr
  | Tfunction _ _ _     => Tpointer ty noattr
  | _                   => remove_attributes ty
  end.

Fixpoint complete_type (env: composite_env) (t: type) : bool :=
  match t with
  | Tvoid => false
  | Tint _ _ _ => true
  | Tlong _ _ => true
  | Tfloat _ _ => true
  | Tpointer _ _ => true
  | Tarray t' _ _ => complete_type env t'
  | Tfunction _ _ _ => false
  | Tstruct id _ | Tunion id _ =>
      match env!id with Some co => true | None => false end
  end.

Definition align_attr (a: attr) (al: Z) : Z :=
  match attr_alignas a with
  | Some l => two_p (Z.of_N l)
  | None => al
  end.

Fixpoint alignof (env: composite_env) (t: type) : Z :=
  align_attr (attr_of_type t)
   (match t with
      | Tvoid => 1
      | Tint I8 _ _ => 1
      | Tint I16 _ _ => 2
      | Tint I32 _ _ => 4
      | Tint IBool _ _ => 1
      | Tlong _ _ => Archi.align_int64
      | Tfloat F32 _ => 4
      | Tfloat F64 _ => Archi.align_float64
      | Tpointer _ _ => if Archi.ptr64 then 8 else 4
      | Tarray t' _ _ => alignof env t'
      | Tfunction _ _ _ => 1
      | Tstruct id _ | Tunion id _ =>
          match env!id with Some co => co_alignof co | None => 1 end
    end).

Fixpoint sizeof (env: composite_env) (t: type) : Z :=
  match t with
  | Tvoid => 1
  | Tint I8 _ _ => 1
  | Tint I16 _ _ => 2
  | Tint I32 _ _ => 4
  | Tint IBool _ _ => 1
  | Tlong _ _ => 8
  | Tfloat F32 _ => 4
  | Tfloat F64 _ => 8
  | Tpointer _ _ => if Archi.ptr64 then 8 else 4
  | Tarray t' n _ => sizeof env t' * Z.max 0 n
  | Tfunction _ _ _ => 1
  | Tstruct id _ | Tunion id _ =>
      match env!id with Some co => co_sizeof co | None => 0 end
  end.

Fixpoint alignof_composite (env: composite_env) (m: members) : Z :=
  match m with
  | nil => 1
  | (id, t) :: m' => Z.max (alignof env t) (alignof_composite env m')
  end.

Fixpoint sizeof_struct (env: composite_env) (cur: Z) (m: members) : Z :=
  match m with
  | nil => cur
  | (id, t) :: m' => sizeof_struct env (align cur (alignof env t) + sizeof env t) m'
  end.

Fixpoint sizeof_union (env: composite_env) (m: members) : Z :=
  match m with
  | nil => 0
  | (id, t) :: m' => Z.max (sizeof env t) (sizeof_union env m')
  end.

Fixpoint field_offset_rec (env: composite_env) (id: ident) (fld: members) (pos: Z)
                          {struct fld} : res Z :=
  match fld with
  | nil => Error (MSG "Unknown field " :: CTX id :: nil)
  | (id', t) :: fld' =>
      if ident_eq id id'
      then OK (align pos (alignof env t))
      else field_offset_rec env id fld' (align pos (alignof env t) + sizeof env t)
  end.

Definition field_offset (env: composite_env) (id: ident) (fld: members) : res Z :=
  field_offset_rec env id fld 0.

Fixpoint field_type (id: ident) (fld: members) {struct fld} : res type :=
  match fld with
  | nil => Error (MSG "Unknown field " :: CTX id :: nil)
  | (id', t) :: fld' => if ident_eq id id' then OK t else field_type id fld'
  end.

Inductive mode: Type :=
  | By_value: memory_chunk -> mode
  | By_reference: mode
  | By_copy: mode
  | By_nothing: mode.

Definition access_mode (ty: type) : mode :=
  match ty with
  | Tint I8 Signed _ => By_value Mint8signed
  | Tint I8 Unsigned _ => By_value Mint8unsigned
  | Tint I16 Signed _ => By_value Mint16signed
  | Tint I16 Unsigned _ => By_value Mint16unsigned
  | Tint I32 _ _ => By_value Mint32
  | Tint IBool _ _ => By_value Mint8unsigned
  | Tlong _ _ => By_value Mint64
  | Tfloat F32 _ => By_value Mfloat32
  | Tfloat F64 _ => By_value Mfloat64
  | Tvoid => By_nothing
  | Tpointer _ _ => By_value Mptr
  | Tarray _ _ _ => By_reference
  | Tfunction _ _ _ => By_reference
  | Tstruct _ _ => By_copy
  | Tunion _ _ => By_copy
end.

Fixpoint rank_type (ce: composite_env) (t: type) : nat :=
  match t with
  | Tarray t' _ _ => S (rank_type ce t')
  | Tstruct id _ | Tunion id _ =>
      match ce!id with
      | None => O
      | Some co => S (co_rank co)
      end
  | _ => O
  end.

Fixpoint rank_members (ce: composite_env) (m: members) : nat :=
  match m with
  | nil => 0%nat
  | (id, t) :: m => Init.Nat.max (rank_type ce t) (rank_members ce m)
  end.

Definition sizeof_composite (env: composite_env) (su: struct_or_union) (m: members) : Z :=
  match su with
  | Struct => sizeof_struct env 0 m
  | Union  => sizeof_union env m
  end.

Fixpoint complete_members (env: composite_env) (m: members) : bool :=
  match m with
  | nil => true
  | (id, t) :: m' => complete_type env t && complete_members env m'
  end.

Record composite_consistent (env: composite_env) (co: composite) : Prop := {
  co_consistent_complete:
     complete_members env (co_members co) = true;
  co_consistent_alignof:
     co_alignof co = align_attr (co_attr co) (alignof_composite env (co_members co));
  co_consistent_sizeof:
     co_sizeof co = align (sizeof_composite env (co_su co) (co_members co)) (co_alignof co);
  co_consistent_rank:
     co_rank co = rank_members env (co_members co)
}.

Definition composite_env_consistent (env: composite_env) : Prop :=
  forall id co, env!id = Some co -> composite_consistent env co.
Module Export Cop.

Inductive unary_operation : Type :=
  | Onotbool : unary_operation
  | Onotint : unary_operation
  | Oneg : unary_operation
  | Oabsfloat : unary_operation.

Inductive binary_operation : Type :=
  | Oadd : binary_operation
  | Osub : binary_operation
  | Omul : binary_operation
  | Odiv : binary_operation
  | Omod : binary_operation
  | Oand : binary_operation
  | Oor : binary_operation
  | Oxor : binary_operation
  | Oshl : binary_operation
  | Oshr : binary_operation
  | Oeq: binary_operation
  | One: binary_operation
  | Olt: binary_operation
  | Ogt: binary_operation
  | Ole: binary_operation
  | Oge: binary_operation.

Inductive classify_cast_cases : Type :=
  | cast_case_pointer
  | cast_case_i2i (sz2:intsize) (si2:signedness)
  | cast_case_f2f
  | cast_case_s2s
  | cast_case_f2s
  | cast_case_s2f
  | cast_case_i2f (si1: signedness)
  | cast_case_i2s (si1: signedness)
  | cast_case_f2i (sz2:intsize) (si2:signedness)
  | cast_case_s2i (sz2:intsize) (si2:signedness)
  | cast_case_l2l
  | cast_case_i2l (si1: signedness)
  | cast_case_l2i (sz2: intsize) (si2: signedness)
  | cast_case_l2f (si1: signedness)
  | cast_case_l2s (si1: signedness)
  | cast_case_f2l (si2:signedness)
  | cast_case_s2l (si2:signedness)
  | cast_case_i2bool
  | cast_case_l2bool
  | cast_case_f2bool
  | cast_case_s2bool
  | cast_case_struct (id1 id2: ident)
  | cast_case_union  (id1 id2: ident)
  | cast_case_void
  | cast_case_default.

Definition classify_cast (tfrom tto: type) : classify_cast_cases :=
  match tto, tfrom with

  | Tvoid, _ => cast_case_void

  | Tint IBool _ _, Tint _ _ _ => cast_case_i2bool
  | Tint IBool _ _, Tlong _ _ => cast_case_l2bool
  | Tint IBool _ _, Tfloat F64 _ => cast_case_f2bool
  | Tint IBool _ _, Tfloat F32 _ => cast_case_s2bool
  | Tint IBool _ _, (Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ _) =>
      if Archi.ptr64 then cast_case_l2bool else cast_case_i2bool

  | Tint sz2 si2 _, Tint _ _ _ =>
      if Archi.ptr64 then cast_case_i2i sz2 si2
      else if intsize_eq sz2 I32 then cast_case_pointer
      else cast_case_i2i sz2 si2
  | Tint sz2 si2 _, Tlong _ _ => cast_case_l2i sz2 si2
  | Tint sz2 si2 _, Tfloat F64 _ => cast_case_f2i sz2 si2
  | Tint sz2 si2 _, Tfloat F32 _ => cast_case_s2i sz2 si2
  | Tint sz2 si2 _, (Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ _) =>
      if Archi.ptr64 then cast_case_l2i sz2 si2
      else if intsize_eq sz2 I32 then cast_case_pointer
      else cast_case_i2i sz2 si2

  | Tlong _ _, Tlong _ _ =>
      if Archi.ptr64 then cast_case_pointer else cast_case_l2l
  | Tlong _ _, Tint sz1 si1 _ => cast_case_i2l si1
  | Tlong si2 _, Tfloat F64 _ => cast_case_f2l si2
  | Tlong si2 _, Tfloat F32 _ => cast_case_s2l si2
  | Tlong si2 _, (Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ _) =>
      if Archi.ptr64 then cast_case_pointer else cast_case_i2l si2

  | Tfloat F64 _, Tint sz1 si1 _ => cast_case_i2f si1
  | Tfloat F32 _, Tint sz1 si1 _ => cast_case_i2s si1
  | Tfloat F64 _, Tlong si1 _ => cast_case_l2f si1
  | Tfloat F32 _, Tlong si1 _ => cast_case_l2s si1
  | Tfloat F64 _, Tfloat F64 _ => cast_case_f2f
  | Tfloat F32 _, Tfloat F32 _ => cast_case_s2s
  | Tfloat F64 _, Tfloat F32 _ => cast_case_s2f
  | Tfloat F32 _, Tfloat F64 _ => cast_case_f2s

  | Tpointer _ _, Tint _ si _ =>
      if Archi.ptr64 then cast_case_i2l si else cast_case_pointer
  | Tpointer _ _, Tlong _ _ =>
      if Archi.ptr64 then cast_case_pointer else cast_case_l2i I32 Unsigned
  | Tpointer _ _, (Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ _) => cast_case_pointer

  | Tstruct id2 _, Tstruct id1 _ => cast_case_struct id1 id2
  | Tunion id2 _, Tunion id1 _ => cast_case_union id1 id2

  | _, _ => cast_case_default
  end.

Definition cast_int_int (sz: intsize) (sg: signedness) (i: int) : int :=
  match sz, sg with
  | I8, Signed => Int.sign_ext 8 i
  | I8, Unsigned => Int.zero_ext 8 i
  | I16, Signed => Int.sign_ext 16 i
  | I16, Unsigned => Int.zero_ext 16 i
  | I32, _ => i
  | IBool, _ => if Int.eq i Int.zero then Int.zero else Int.one
  end.

Definition cast_int_float (si: signedness) (i: int) : float :=
  match si with
  | Signed => Float.of_int i
  | Unsigned => Float.of_intu i
  end.

Definition cast_float_int (si : signedness) (f: float) : option int :=
  match si with
  | Signed => Float.to_int f
  | Unsigned => Float.to_intu f
  end.

Definition cast_int_single (si: signedness) (i: int) : float32 :=
  match si with
  | Signed => Float32.of_int i
  | Unsigned => Float32.of_intu i
  end.

Definition cast_single_int (si : signedness) (f: float32) : option int :=
  match si with
  | Signed => Float32.to_int f
  | Unsigned => Float32.to_intu f
  end.

Definition cast_int_long (si: signedness) (i: int) : int64 :=
  match si with
  | Signed => Int64.repr (Int.signed i)
  | Unsigned => Int64.repr (Int.unsigned i)
  end.

Definition cast_long_float (si: signedness) (i: int64) : float :=
  match si with
  | Signed => Float.of_long i
  | Unsigned => Float.of_longu i
  end.

Definition cast_long_single (si: signedness) (i: int64) : float32 :=
  match si with
  | Signed => Float32.of_long i
  | Unsigned => Float32.of_longu i
  end.

Definition cast_float_long (si : signedness) (f: float) : option int64 :=
  match si with
  | Signed => Float.to_long f
  | Unsigned => Float.to_longu f
  end.

Definition cast_single_long (si : signedness) (f: float32) : option int64 :=
  match si with
  | Signed => Float32.to_long f
  | Unsigned => Float32.to_longu f
  end.

Inductive classify_neg_cases : Type :=
  | neg_case_i(s: signedness)
  | neg_case_f
  | neg_case_s
  | neg_case_l(s: signedness)
  | neg_default.

Definition classify_neg (ty: type) : classify_neg_cases :=
  match ty with
  | Tint I32 Unsigned _ => neg_case_i Unsigned
  | Tint _ _ _ => neg_case_i Signed
  | Tfloat F64 _ => neg_case_f
  | Tfloat F32 _ => neg_case_s
  | Tlong si _ => neg_case_l si
  | _ => neg_default
  end.

Inductive classify_notint_cases : Type :=
  | notint_case_i(s: signedness)
  | notint_case_l(s: signedness)
  | notint_default.

Definition classify_notint (ty: type) : classify_notint_cases :=
  match ty with
  | Tint I32 Unsigned _ => notint_case_i Unsigned
  | Tint _ _ _ => notint_case_i Signed
  | Tlong si _ => notint_case_l si
  | _ => notint_default
  end.

Inductive binarith_cases: Type :=
  | bin_case_i (s: signedness)
  | bin_case_l (s: signedness)
  | bin_case_f
  | bin_case_s
  | bin_default.

Definition classify_binarith (ty1: type) (ty2: type) : binarith_cases :=
  match ty1, ty2 with
  | Tint I32 Unsigned _, Tint _ _ _ => bin_case_i Unsigned
  | Tint _ _ _, Tint I32 Unsigned _ => bin_case_i Unsigned
  | Tint _ _ _, Tint _ _ _ => bin_case_i Signed
  | Tlong Signed _, Tlong Signed _ => bin_case_l Signed
  | Tlong _ _, Tlong _ _ => bin_case_l Unsigned
  | Tlong sg _, Tint _ _ _ => bin_case_l sg
  | Tint _ _ _, Tlong sg _ => bin_case_l sg
  | Tfloat F32 _, Tfloat F32 _ => bin_case_s
  | Tfloat _ _, Tfloat _ _ => bin_case_f
  | Tfloat F64 _, (Tint _ _ _ | Tlong _ _) => bin_case_f
  | (Tint _ _ _ | Tlong _ _), Tfloat F64 _ => bin_case_f
  | Tfloat F32 _, (Tint _ _ _ | Tlong _ _) => bin_case_s
  | (Tint _ _ _ | Tlong _ _), Tfloat F32 _ => bin_case_s
  | _, _ => bin_default
  end.

Definition binarith_type (c: binarith_cases) : type :=
  match c with
  | bin_case_i sg => Tint I32 sg noattr
  | bin_case_l sg => Tlong sg noattr
  | bin_case_f    => Tfloat F64 noattr
  | bin_case_s    => Tfloat F32 noattr
  | bin_default   => Tvoid
  end.

Inductive classify_add_cases : Type :=
  | add_case_pi (ty: type) (si: signedness)
  | add_case_pl (ty: type)
  | add_case_ip (si: signedness) (ty: type)
  | add_case_lp (ty: type)
  | add_default.

Definition classify_add (ty1: type) (ty2: type) :=
  match typeconv ty1, typeconv ty2 with
  | Tpointer ty _, Tint _ si _ => add_case_pi ty si
  | Tpointer ty _, Tlong _ _ => add_case_pl ty
  | Tint _ si _, Tpointer ty _ => add_case_ip si ty
  | Tlong _ _, Tpointer ty _ => add_case_lp ty
  | _, _ => add_default
  end.

Definition ptrofs_of_int (si: signedness) (n: int) : ptrofs :=
  match si with
  | Signed => Ptrofs.of_ints n
  | Unsigned => Ptrofs.of_intu n
  end.

Definition sem_add_ptr_int (cenv: composite_env) (ty: type) (si: signedness) (v1 v2: val): option val :=
  match v1, v2 with
  | Vptr b1 ofs1, Vint n2 =>
      let n2 := ptrofs_of_int si n2 in
      Some (Vptr b1 (Ptrofs.add ofs1 (Ptrofs.mul (Ptrofs.repr (sizeof cenv ty)) n2)))
  | Vint n1, Vint n2 =>
      if Archi.ptr64 then None else Some (Vint (Int.add n1 (Int.mul (Int.repr (sizeof cenv ty)) n2)))
  | Vlong n1, Vint n2 =>
      let n2 := cast_int_long si n2 in
      if Archi.ptr64 then Some (Vlong (Int64.add n1 (Int64.mul (Int64.repr (sizeof cenv ty)) n2))) else None
  | _,  _ => None
  end.

Definition sem_add_ptr_long (cenv: composite_env) (ty: type) (v1 v2: val): option val :=
  match v1, v2 with
  | Vptr b1 ofs1, Vlong n2 =>
      let n2 := Ptrofs.of_int64 n2 in
      Some (Vptr b1 (Ptrofs.add ofs1 (Ptrofs.mul (Ptrofs.repr (sizeof cenv ty)) n2)))
  | Vint n1, Vlong n2 =>
      let n2 := Int.repr (Int64.unsigned n2) in
      if Archi.ptr64 then None else Some (Vint (Int.add n1 (Int.mul (Int.repr (sizeof cenv ty)) n2)))
  | Vlong n1, Vlong n2 =>
      if Archi.ptr64 then Some (Vlong (Int64.add n1 (Int64.mul (Int64.repr (sizeof cenv ty)) n2))) else None
  | _,  _ => None
  end.

Inductive classify_sub_cases : Type :=
  | sub_case_pi (ty: type) (si: signedness)
  | sub_case_pp (ty: type)
  | sub_case_pl (ty: type)
  | sub_default.

Definition classify_sub (ty1: type) (ty2: type) :=
  match typeconv ty1, typeconv ty2 with
  | Tpointer ty _, Tint _ si _ => sub_case_pi ty si
  | Tpointer ty _ , Tpointer _ _ => sub_case_pp ty
  | Tpointer ty _, Tlong _ _ => sub_case_pl ty
  | _, _ => sub_default
  end.

Inductive classify_shift_cases : Type:=
  | shift_case_ii(s: signedness)
  | shift_case_ll(s: signedness)
  | shift_case_il(s: signedness)
  | shift_case_li(s: signedness)
  | shift_default.

Definition classify_shift (ty1: type) (ty2: type) :=
  match typeconv ty1, typeconv ty2 with
  | Tint I32 Unsigned _, Tint _ _ _ => shift_case_ii Unsigned
  | Tint _ _ _, Tint _ _ _ => shift_case_ii Signed
  | Tint I32 Unsigned _, Tlong _ _ => shift_case_il Unsigned
  | Tint _ _ _, Tlong _ _ => shift_case_il Signed
  | Tlong s _, Tint _ _ _ => shift_case_li s
  | Tlong s _, Tlong _ _ => shift_case_ll s
  | _,_  => shift_default
  end.

Inductive classify_cmp_cases : Type :=
  | cmp_case_pp
  | cmp_case_pi (si: signedness)
  | cmp_case_ip (si: signedness)
  | cmp_case_pl
  | cmp_case_lp
  | cmp_default.

Definition classify_cmp (ty1: type) (ty2: type) :=
  match typeconv ty1, typeconv ty2 with
  | Tpointer _ _ , Tpointer _ _ => cmp_case_pp
  | Tpointer _ _ , Tint _ si _ => cmp_case_pi si
  | Tint _ si _, Tpointer _ _ => cmp_case_ip si
  | Tpointer _ _ , Tlong _ _ => cmp_case_pl
  | Tlong _ _ , Tpointer _ _ => cmp_case_lp
  | _, _ => cmp_default
  end.

Inductive expr : Type :=
  | Econst_int: int -> type -> expr
  | Econst_float: float -> type -> expr
  | Econst_single: float32 -> type -> expr
  | Econst_long: int64 -> type -> expr
  | Evar: ident -> type -> expr
  | Etempvar: ident -> type -> expr
  | Ederef: expr -> type -> expr
  | Eaddrof: expr -> type -> expr
  | Eunop: unary_operation -> expr -> type -> expr
  | Ebinop: binary_operation -> expr -> expr -> type -> expr
  | Ecast: expr -> type -> expr
  | Efield: expr -> ident -> type -> expr
  | Esizeof: type -> type -> expr
  | Ealignof: type -> type -> expr.

Definition typeof (e: expr) : type :=
  match e with
  | Econst_int _ ty => ty
  | Econst_float _ ty => ty
  | Econst_single _ ty => ty
  | Econst_long _ ty => ty
  | Evar _ ty => ty
  | Etempvar _ ty => ty
  | Ederef _ ty => ty
  | Eaddrof _ ty => ty
  | Eunop _ _ ty => ty
  | Ebinop _ _ _ ty => ty
  | Ecast _ ty => ty
  | Efield _ _ ty => ty
  | Esizeof _ ty => ty
  | Ealignof _ ty => ty
  end.

Import Coq.Logic.EqdepFacts.

Module EqdepElim: EqdepElimination.
Lemma eq_rect_eq :
    forall (U:Type) (p:U) (Q:U -> Type) (x:Q p) (h:p = p),
      x = eq_rect p Q x p h.
admit.
Defined.
End EqdepElim.

Module EqdepTh := EqdepTheory EqdepElim.
Export EqdepTh.

Tactic Notation "if_tac" :=
  match goal with |- context [if ?a then _ else _] =>
    lazymatch type of a with
    | sumbool _ _ =>destruct a as [?H | ?H]
    | bool => fail "Use simple_if_tac instead of if_tac, since your expression"a" has type bool"
    | ?t => fail "Use if_tac only for sumbool; your expression"a" has type" t
   end end.

Fixpoint id_in_list (id: ident) (ids: list ident) : bool :=
 match ids with i::ids' => orb (Pos.eqb id i) (id_in_list id ids') | _ => false end.

Fixpoint compute_list_norepet (ids: list ident) : bool :=
 match ids with
 | id :: ids' => if id_in_list id ids' then false else compute_list_norepet ids'
 | nil => true
 end.

Section cuof.

Context (cenv: composite_env).

Fixpoint complete_legal_cosu_type t :=
  match t with
  | Tarray t' _ _ => complete_legal_cosu_type t'
  | Tstruct id _ => match cenv ! id with
                    | Some co => match co_su co with
                                 | Struct => true
                                 | Union => false
                                 end
                    | _ => false
                    end
  | Tunion id _ => match cenv ! id with
                   | Some co => match co_su co with
                                | Struct => false
                                | Union => true
                                end
                   | _ => false
                   end
  | Tfunction _ _ _
  | Tvoid => false
  | _ => true
  end.

Fixpoint composite_complete_legal_cosu_type (m: members): bool :=
  match m with
  | nil => true
  | (_, t) :: m' => complete_legal_cosu_type t && composite_complete_legal_cosu_type m'
  end.

Definition composite_env_complete_legal_cosu_type: Prop :=
  forall (id : positive) (co : composite),
    cenv ! id = Some co -> composite_complete_legal_cosu_type (co_members co) = true.

End cuof.

Section align_compatible_rec.

Context (cenv: composite_env).

Inductive align_compatible_rec: type -> Z -> Prop :=
| align_compatible_rec_by_value: forall t ch z, access_mode t = By_value ch -> (Memdata.align_chunk ch | z) -> align_compatible_rec t z
| align_compatible_rec_Tarray: forall t n a z, (forall i, 0 <= i < n -> align_compatible_rec t (z + sizeof cenv t * i)) -> align_compatible_rec (Tarray t n a) z
| align_compatible_rec_Tstruct: forall i a co z, cenv ! i = Some co -> (forall i0 t0 z0, field_type i0 (co_members co) = Errors.OK t0 -> field_offset cenv i0 (co_members co) = Errors.OK z0 -> align_compatible_rec t0 (z + z0)) -> align_compatible_rec (Tstruct i a) z
| align_compatible_rec_Tunion: forall i a co z, cenv ! i = Some co -> (forall i0 t0, field_type i0 (co_members co) = Errors.OK t0 -> align_compatible_rec t0 z) -> align_compatible_rec (Tunion i a) z.

End align_compatible_rec.

Fixpoint hardware_alignof (ha_env: PTree.t Z) t: Z :=
  match t with
  | Tarray t' _ _ => hardware_alignof ha_env t'
  | Tstruct id _ =>
      match ha_env ! id with
      | Some ha => ha
      | None => 1
      end
  | Tunion id _ =>
      match ha_env ! id with
      | Some ha => ha
      | None => 1
      end
  | _ => match access_mode t with
         | By_value ch => Memdata.align_chunk ch
         | _ => 1
         end
  end.

Fixpoint hardware_alignof_composite (ha_env: PTree.t Z) (m: members): Z :=
  match m with
  | nil => 1
  | (_, t) :: m' => Z.max (hardware_alignof ha_env t) (hardware_alignof_composite ha_env m')
  end.

Definition hardware_alignof_env_consistent (cenv: composite_env) (ha_env: PTree.t Z): Prop :=
  forall i co ha,
    cenv ! i = Some co ->
    ha_env ! i = Some ha ->
    ha = hardware_alignof_composite ha_env (co_members co).

Definition hardware_alignof_env_complete (cenv: composite_env) (ha_env: PTree.t Z): Prop :=
  forall i,
    (exists co, cenv ! i = Some co) <->
    (exists ha, ha_env ! i = Some ha).

Module Type LEGAL_ALIGNAS.

  Parameter legal_alignas_obs: Type.
  Parameter legal_alignas_type: composite_env -> PTree.t Z -> PTree.t legal_alignas_obs -> type -> legal_alignas_obs.
  Parameter legal_alignas_composite: composite_env -> PTree.t Z -> PTree.t legal_alignas_obs -> composite -> legal_alignas_obs.
  Parameter is_aligned_aux: legal_alignas_obs -> Z -> Z -> bool.

End LEGAL_ALIGNAS.

Module LegalAlignasDefsGen (LegalAlignas: LEGAL_ALIGNAS).

  Import LegalAlignas.

  Definition legal_alignas_env_consistent (cenv: composite_env) (ha_env: PTree.t Z) (la_env: PTree.t legal_alignas_obs): Prop :=
    forall i co la,
      cenv ! i = Some co ->
      la_env ! i = Some la ->
      la = legal_alignas_composite cenv ha_env la_env co.

  Definition legal_alignas_env_complete (cenv: composite_env) (la_env: PTree.t legal_alignas_obs): Prop :=
    forall i,
      (exists co, cenv ! i = Some co) <->
      (exists la, la_env ! i = Some la).

  Definition is_aligned cenv ha_env la_env (t: type) (ofs: Z): bool := is_aligned_aux (legal_alignas_type cenv ha_env la_env t) (hardware_alignof ha_env t) ofs.

  Definition legal_alignas_env_sound (cenv: composite_env) (ha_env: PTree.t Z) (la_env: PTree.t legal_alignas_obs): Prop :=
    forall ofs t,
      complete_legal_cosu_type cenv t = true ->
      is_aligned cenv ha_env la_env t ofs = true ->
      align_compatible_rec cenv t ofs.

End LegalAlignasDefsGen.

Module Type LEGAL_ALIGNAS_FACTS.

  Declare Module LegalAlignas: LEGAL_ALIGNAS.
  Module LegalAlignasDefs := LegalAlignasDefsGen (LegalAlignas).
Export LegalAlignas.
Export LegalAlignasDefs.

End LEGAL_ALIGNAS_FACTS.

Module LegalAlignasStrong <: LEGAL_ALIGNAS.

Section legal_alignas.

Context (cenv: composite_env) (ha_env: PTree.t Z).

Definition legal_alignas_obs: Type := bool.

Fixpoint legal_alignas_type (la_env: PTree.t bool) t: bool :=
  match t with
  | Tarray t' _ _ => (sizeof cenv t' mod hardware_alignof ha_env t' =? 0) && legal_alignas_type la_env t'
  | Tstruct id _ =>
      match la_env ! id with
      | Some la => la
      | None => false
      end
  | Tunion id _ =>
      match la_env ! id with
      | Some la => la
      | None => false
      end
  | _ => match access_mode t with
         | By_value ch => true
         | _ => false
         end
  end.

Fixpoint legal_alignas_struct_members_rec (la_env: PTree.t bool) (m: members) (pos: Z): bool :=
  match m with
  | nil => true
  | (_, t) :: m' => (align pos (alignof cenv t) mod hardware_alignof ha_env t =? 0) && (legal_alignas_type la_env t) && (legal_alignas_struct_members_rec la_env m' (align pos (alignof cenv t) + sizeof cenv t))
  end.

Fixpoint legal_alignas_union_members_rec (la_env: PTree.t bool) (m: members): bool :=
  match m with
  | nil => true
  | (_, t) :: m' => (legal_alignas_type la_env t) && (legal_alignas_union_members_rec la_env m')
  end.

Definition legal_alignas_composite (la_env: PTree.t bool) (co: composite): bool :=
  match co_su co with
  | Struct => legal_alignas_struct_members_rec la_env (co_members co) 0
  | Union => legal_alignas_union_members_rec la_env (co_members co)
  end.

Definition is_aligned_aux (b: bool) (ha: Z) (ofs: Z) := b && ((ofs mod ha) =? 0).

End legal_alignas.

End LegalAlignasStrong.

Module LegalAlignasStrongFacts: LEGAL_ALIGNAS_FACTS with Module LegalAlignas := LegalAlignasStrong.

Module LegalAlignas := LegalAlignasStrong.
Module LegalAlignasDefs := LegalAlignasDefsGen (LegalAlignas).

End LegalAlignasStrongFacts.

Module Export LegalAlignasFacts := LegalAlignasStrongFacts.

Definition force_val (v: option val) : val :=
 match v with Some v' => v' | None => Vundef end.

Definition force_val1 (f: val -> option val) (v: val) := force_val (f v).
Definition force_val2 (f: val -> val -> option val) (v1 v2: val) := force_val (f v1 v2).

Definition force_ptr (v: val) : val :=
              match v with Vptr l ofs => v | _ => Vundef  end.

Definition always {A B: Type} (b: B) (a: A) := b.

Definition offset_val (ofs: Z) (v: val) : val :=
  match v with
  | Vptr b z => Vptr b (Ptrofs.add z (Ptrofs.repr ofs))
  | _ => Vundef
 end.

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

Definition lift S {A B} (f : A -> B) (a : S -> A) (x: S) : B := f (a x).

Definition liftx {H: Lift} (f: lift_T H) : lifted H :=
  lift_uncurry_open H (lift (lift_curry H f)).
Notation "'`' x" := (liftx x) (at level 10, x at next level).

Notation "'`(' x ')'" := (liftx (x : _)).
Module Export Map.
Section map.
Variables (B : Type).

Definition t := positive -> option B.

Definition get (h: t) (a:positive) : option B := h a.

Definition set (a:positive) (v: B) (h: t) : t :=
  fun i => if ident_eq i a then Some v else h i.

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

Definition ge_of (rho: environ) : genviron :=
  match rho with mkEnviron ge ve te => ge end.

Definition ve_of (rho: environ) : venviron :=
  match rho with mkEnviron ge ve te => ve end.

Definition te_of (rho: environ) : tenviron :=
  match rho with mkEnviron ge ve te => te end.

End FUNSPEC.

Definition members_no_replicate (m: members) : bool :=
  compute_list_norepet (map fst m).

Definition composite_legal_fieldlist (co: composite): Prop :=
  members_no_replicate (co_members co) = true.

Definition composite_env_legal_fieldlist env :=
  forall (id : positive) (co : composite),
    env ! id = Some co -> composite_legal_fieldlist co.

Class compspecs := mkcompspecs {
  cenv_cs : composite_env;
  cenv_consistent: composite_env_consistent cenv_cs;
  cenv_legal_fieldlist: composite_env_legal_fieldlist cenv_cs;
  cenv_legal_su: composite_env_complete_legal_cosu_type cenv_cs;
  ha_env_cs: PTree.t Z;
  ha_env_cs_consistent: hardware_alignof_env_consistent cenv_cs ha_env_cs;
  ha_env_cs_complete: hardware_alignof_env_complete cenv_cs ha_env_cs;
  la_env_cs: PTree.t legal_alignas_obs;
  la_env_cs_consistent: legal_alignas_env_consistent cenv_cs ha_env_cs la_env_cs;
  la_env_cs_complete: legal_alignas_env_complete cenv_cs la_env_cs;
  la_env_cs_sound: legal_alignas_env_sound cenv_cs ha_env_cs la_env_cs
}.

Existing Class composite_env.
Existing Instance cenv_cs.

Arguments sizeof {env} !t / .
Arguments alignof {env} !t / .

Definition eval_id (id: ident) (rho: environ) := force_val (Map.get (te_of rho) id).

Definition env_set (rho: environ) (x: ident) (v: val) : environ :=
  mkEnviron (ge_of rho) (ve_of rho) (Map.set x v (te_of rho)).
Canonical Structure LiftEnviron := Tend environ.

Module Export Cop2.

Definition eqb_option {A} (f: A -> A -> bool) (x y: option A) : bool :=
  match x, y with
  | None, None => true
  | Some x' , Some y' => f x' y'
 | _, _ => false
  end.

Definition eqb_attr (a b: attr) : bool :=
 match a, b with
 | mk_attr av an, mk_attr bv bn => eqb av bv && eqb_option N.eqb an bn
 end.

Definition eqb_floatsize (a b: floatsize) : bool :=
 match a , b with
 | F32, F32 => true
 | F64, F64 => true
 | _, _ => false
 end.

Definition eqb_ident : ident -> ident -> bool := Pos.eqb.

Definition eqb_intsize (a b: intsize) : bool :=
 match a , b with
 | I8, I8 => true
 | I16, I16 => true
 | I32, I32 => true
 | IBool, IBool => true
 | _, _ => false
 end.

Definition eqb_signedness (a b : signedness) :=
 match a, b with
 | Signed, Signed => true
 | Unsigned, Unsigned => true
 | _, _ => false
 end.

Definition eqb_calling_convention (a b: calling_convention) :=
 andb (eqb_option Z.eqb (cc_vararg a) (cc_vararg b))
     (andb  (eqb (cc_unproto a) (cc_unproto b))
      (eqb (cc_structret a) (cc_structret b))).

Fixpoint eqb_type (a b: type) {struct a} : bool :=
 match a, b with
 | Tvoid, Tvoid => true
 | Tint ia sa aa, Tint ib sb ab => andb (eqb_intsize ia ib)
                                                    (andb (eqb_signedness sa sb) (eqb_attr aa ab))
 | Tlong sa aa, Tlong sb ab => andb (eqb_signedness sa sb) (eqb_attr aa ab)
 | Tfloat sa aa, Tfloat sb ab => andb (eqb_floatsize sa sb) (eqb_attr aa ab)
 | Tpointer ta aa, Tpointer tb ab => andb (eqb_type ta tb) (eqb_attr aa ab)
 | Tarray ta sa aa, Tarray tb sb ab => andb (eqb_type ta tb)
                                                                   (andb (Zeq_bool sa sb) (eqb_attr aa ab))
 | Tfunction sa ta ca, Tfunction sb tb cb =>
       andb (andb (eqb_typelist sa sb) (eqb_type ta tb)) (eqb_calling_convention ca cb)
 | Tstruct ia aa, Tstruct ib ab => andb (eqb_ident ia ib) (eqb_attr aa ab)
 | Tunion ia aa, Tunion ib ab => andb (eqb_ident ia ib) (eqb_attr aa ab)
 | _, _ => false
 end
with eqb_typelist (a b: typelist)  {struct a}: bool :=
  match a, b with
  | Tcons ta ra, Tcons tb rb => andb (eqb_type ta tb) (eqb_typelist ra rb)
  | Tnil, Tnil => true
  | _ , _ => false
  end.

Definition log2_sizeof_pointer : N :=
  ltac:(let n := eval compute in
  (N.log2 (Z.to_N (@sizeof (PTree.empty _) (Tpointer Tvoid noattr))))
   in exact (n)).

Definition int_or_ptr_type : type :=
  Tpointer Tvoid {| attr_volatile := false; attr_alignas := Some log2_sizeof_pointer |}.

Definition bool_val_i (v : val) : option bool :=
match v with
      | Vint n => Some (negb (Int.eq n Int.zero))
      | _ => None
      end.

Definition bool_val_p (v : val) : option bool :=
match v with
      | Vint n => if Archi.ptr64 then None else Some (negb (Int.eq n Int.zero))
      | Vlong n => if Archi.ptr64 then Some (negb (Int64.eq n Int64.zero)) else None
      | Vptr b ofs => Some true
      | _ => None
      end.

Definition bool_val_s (v : val) : option bool :=
 match v with
      | Vsingle f => Some (negb (Float32.cmp Ceq f Float32.zero))
      | _ => None
      end.

Definition bool_val_f (v : val) : option bool :=
 match v with
      | Vfloat f => Some (negb (Float.cmp Ceq f Float.zero))
      | _ => None
      end.

Definition bool_val_l (v : val) : option bool :=
 match v with
      | Vlong n => Some (negb (Int64.eq n Int64.zero))
      | Vptr b ofs =>
          if negb Archi.ptr64 then None else Some true
      | _ => None
      end.

Definition bool_val (t: type) : val -> option bool :=
  match t with
  | Tint _ _ _ => bool_val_i
  | Tpointer _ _ => if  eqb_type t int_or_ptr_type then (fun _ => None) else bool_val_p
  | Tfloat F64 _ => bool_val_f
  | Tfloat F32 _ => bool_val_s
  | Tlong _ _ => bool_val_l
  | _ => fun v => None
  end.

Definition closed_wrt_vars {B} (S: ident -> Prop) (F: environ -> B) : Prop :=
  forall rho te',
     (forall i, S i \/ Map.get (te_of rho) i = Map.get te' i) ->
     F rho = F (mkEnviron (ge_of rho) (ve_of rho) te').

Definition subst {A} (x: ident) (v: environ -> val) (P: environ -> A) : environ -> A :=
   fun s => P (env_set s x (v s)).
Module Export Clight_Cop2.

Definition sem_cast_pointer (v : val) : option val := Some v.

Definition sem_cast_i2i sz2 si2 (v : val) : option val :=
match v with
      | Vint i => Some (Vint (Cop.cast_int_int sz2 si2 i))
      | _ => None
      end.

Definition sem_cast_i2bool (v: val) : option val :=
      match v with
      | Vint n =>
          Some(Vint(if Int.eq n Int.zero then Int.zero else Int.one))
      | Vptr b ofs =>
          if Archi.ptr64 then None else Some Vone
      | _ => None
      end.

Definition sem_cast_l2bool (v: val) : option val :=
      match v with
      | Vlong n =>
          Some(Vint(if Int64.eq n Int64.zero then Int.zero else Int.one))
      | Vptr b ofs =>
          if negb Archi.ptr64 then None else Some Vone
      | _ => None
      end.

Definition sem_cast_l2l (v : val) : option val :=
 match v with
      | Vlong n => Some (Vlong n)
      | _ => None
      end.

Definition sem_cast_i2l si (v : val) : option val :=
 match v with
      | Vint n => Some(Vlong (Cop.cast_int_long si n))
      | _ => None
      end.

Definition sem_cast_l2i sz si (v : val) : option val :=
match v with
      | Vlong n => Some(Vint (Cop.cast_int_int sz si (Int.repr (Int64.unsigned n))))
      | _ => None
      end.

Definition sem_cast_struct id1 id2 (v : val) : option val :=
match v with
      | Vptr b ofs =>
          if ident_eq id1 id2 then Some v else None
      | _ => None
      end.

Definition sem_cast_union id1 id2 (v : val) : option val :=
match v with
      | Vptr b ofs =>
          if ident_eq id1 id2 then Some v else None
      | _ => None
      end.

Definition sem_cast_f2f (v: val) : option val :=
      match v with
      | Vfloat f => Some (Vfloat f)
      | _ => None
      end.

Definition sem_cast_s2s (v: val) : option val :=
      match v with
      | Vsingle f => Some (Vsingle f)
      | _ => None
      end.

Definition sem_cast_s2f (v: val) : option val :=
      match v with
      | Vsingle f => Some (Vfloat (Float.of_single f))
      | _ => None
      end.

 Definition sem_cast_f2s (v: val) : option val :=
      match v with
      | Vfloat f => Some (Vsingle (Float.to_single f))
      | _ => None
      end.

 Definition sem_cast_i2f si1 (v: val) : option val :=
      match v with
      | Vint i => Some (Vfloat (Cop.cast_int_float si1 i))
      | _ => None
      end.

 Definition sem_cast_i2s si1 (v: val) : option val :=
      match v with
      | Vint i => Some (Vsingle (Cop.cast_int_single si1 i))
      | _ => None
      end.

 Definition sem_cast_f2i sz2 si2 (v: val) : option val :=
      match v with
      | Vfloat f =>
          match Cop.cast_float_int si2 f with
          | Some i => Some (Vint (Cop.cast_int_int sz2 si2 i))
          | None => None
          end
      | _ => None
      end.

Definition sem_cast_s2i sz2 si2 (v: val) : option val :=
      match v with
      | Vsingle f =>
          match Cop.cast_single_int si2 f with
          | Some i => Some (Vint (Cop.cast_int_int sz2 si2 i))
          | None => None
          end
      | _ => None
      end.

Definition sem_cast_f2bool (v: val) : option val :=
      match v with
      | Vfloat f =>
          Some(Vint(if Float.cmp Ceq f Float.zero then Int.zero else Int.one))
      | _ => None
      end.

Definition sem_cast_s2bool (v: val) : option val :=
      match v with
      | Vsingle f =>
          Some(Vint(if Float32.cmp Ceq f Float32.zero then Int.zero else Int.one))
      | _ => None
      end.

 Definition sem_cast_l2f si1 (v: val) : option val :=
      match v with
      | Vlong i => Some (Vfloat (Cop.cast_long_float si1 i))
      | _ => None
      end.

 Definition sem_cast_l2s si1 (v: val) : option val :=
      match v with
      | Vlong i => Some (Vsingle (Cop.cast_long_single si1 i))
      | _ => None
      end.

 Definition sem_cast_f2l si2 (v: val) : option val :=
      match v with
      | Vfloat f =>
          match Cop.cast_float_long si2 f with
          | Some i => Some (Vlong i)
          | None => None
          end
      | _ => None
      end.

Definition sem_cast_s2l si2 (v: val) : option val :=
      match v with
      | Vsingle f =>
          match Cop.cast_single_long si2 f with
          | Some i => Some (Vlong i)
          | None => None
          end
      | _ => None
      end.

Definition sem_cast (t1 t2: type): val -> option val :=
  match classify_cast t1 t2 with
  | cast_case_pointer => sem_cast_pointer
  | Cop.cast_case_i2i sz2 si2 => sem_cast_i2i sz2 si2
  | Cop.cast_case_f2f => sem_cast_f2f
  | Cop.cast_case_s2s => sem_cast_s2s
  | Cop.cast_case_s2f => sem_cast_s2f
  | Cop.cast_case_f2s => sem_cast_f2s
  | Cop.cast_case_i2f si1 => sem_cast_i2f si1
  | Cop.cast_case_i2s si1 => sem_cast_i2s si1
  | Cop.cast_case_f2i sz2 si2 => sem_cast_f2i sz2 si2
  | Cop.cast_case_s2i sz2 si2 => sem_cast_s2i sz2 si2
  | Cop.cast_case_i2bool => sem_cast_i2bool
  | Cop.cast_case_l2bool => sem_cast_l2bool
  | Cop.cast_case_f2bool => sem_cast_f2bool
  | Cop.cast_case_s2bool => sem_cast_s2bool
  | Cop.cast_case_l2l => sem_cast_l2l
  | Cop.cast_case_i2l si => sem_cast_i2l si
  | Cop.cast_case_l2i sz si => sem_cast_l2i sz si
  | Cop.cast_case_l2f si1 => sem_cast_l2f si1
  | Cop.cast_case_l2s si1 => sem_cast_l2s si1
  | Cop.cast_case_f2l si2 => sem_cast_f2l si2
  | Cop.cast_case_s2l si2 => sem_cast_s2l si2
  | Cop.cast_case_struct id1 id2 => sem_cast_struct id1 id2
  | Cop.cast_case_union id1 id2 => sem_cast_union id1 id2
  | Cop.cast_case_void =>
      fun v => Some v
  | Cop.cast_case_default =>
      fun v => None
 end.

Definition sem_notbool (t: type) (v: val) : option val :=
  option_map (fun b => Val.of_bool (negb b)) (Cop2.bool_val t v).

Definition sem_neg_i (v: val) : option val :=
      match v with
      | Vint n => Some (Vint (Int.neg n))
      | _ => None
      end.

Definition sem_neg_f (v: val) : option val :=
       match v with
      | Vfloat f => Some (Vfloat (Float.neg f))
      | _ => None
      end.

Definition sem_neg_s (v: val) : option val :=
       match v with
      | Vsingle f => Some (Vsingle (Float32.neg f))
      | _ => None
      end.

Definition sem_neg_l (v: val) : option val :=
      match v with
      | Vlong n => Some (Vlong (Int64.neg n))
      | _ => None
      end.

Definition sem_neg (t: type) : val -> option val :=
  match Cop.classify_neg t with
  | Cop.neg_case_i sg => sem_neg_i
  | Cop.neg_case_f => sem_neg_f
  | Cop.neg_case_s => sem_neg_s
  | Cop.neg_case_l sg => sem_neg_l
  | neg_default => fun v => None
  end.

Definition sem_absfloat_i sg (v: val) : option val :=
  match v with
      | Vint n => Some (Vfloat (Float.abs (Cop.cast_int_float sg n)))
      | _ => None
      end.

Definition sem_absfloat_f (v: val) :=
     match v with
      | Vfloat f => Some (Vfloat (Float.abs f))
      | _ => None
      end.

Definition sem_absfloat_s (v: val) :=
      match v with
      | Vsingle f => Some (Vfloat (Float.abs (Float.of_single f)))
      | _ => None
      end.

Definition sem_absfloat_l sg v :=
      match v with
      | Vlong n => Some (Vfloat (Float.abs (Cop.cast_long_float sg n)))
      | _ => None
      end.

Definition sem_absfloat (ty: type)  : val -> option val :=
  match Cop.classify_neg ty with
  | Cop.neg_case_i sg => sem_absfloat_i sg
  | Cop.neg_case_f => sem_absfloat_f
  | Cop.neg_case_s => sem_absfloat_s
   | Cop.neg_case_l sg => sem_absfloat_l sg
  | neg_default => fun v => None
  end.

Definition sem_notint_i (v:val) : option val :=
      match v with
      | Vint n => Some (Vint (Int.not n))
      | _ => None
      end.

Definition sem_notint_l (v:val) : option val :=
      match v with
      | Vlong n => Some (Vlong (Int64.not n))
      | _ => None
      end.

Definition sem_notint (t: type)  : val -> option val :=
  match Cop.classify_notint t with
  | Cop.notint_case_i sg => sem_notint_i
  | Cop.notint_case_l sg => sem_notint_l
  | notint_default => fun v => None
  end.

Definition both_int (f: int -> int -> option val) (cast1 cast2: val -> option val) (v1 v2: val) :=
 match cast1 v1, cast2 v2 with Some (Vint v1'), Some (Vint v2') => f v1' v2' | _, _ => None end.

Definition both_long (f: int64 -> int64 -> option val) (cast1 cast2: val -> option val) (v1 v2: val) :=
 match cast1 v1, cast2 v2 with Some (Vlong v1'), Some (Vlong v2') => f v1' v2' | _, _ => None end.

Definition both_float (f: float -> float -> option val) (cast1 cast2: val -> option val) (v1 v2: val) :=
 match cast1 v1, cast2 v2 with Some (Vfloat v1'), Some (Vfloat v2') => f v1' v2' | _, _ => None end.

Definition both_single (f: float32 -> float32 -> option val) (cast1 cast2: val -> option val) (v1 v2: val) :=
 match cast1 v1, cast2 v2 with Some (Vsingle v1'), Some (Vsingle v2') => f v1' v2' | _, _ => None end.

Definition sem_binarith
    (sem_int: signedness -> int -> int -> option val)
    (sem_long: signedness -> int64 -> int64 -> option val)
    (sem_float: float -> float -> option val)
    (sem_single: float32 -> float32 -> option val)
    (t1: type) (t2: type)
   : forall (v1: val) (v2: val), option val :=
  let c := Cop.classify_binarith t1 t2 in
  let t := Cop.binarith_type c in
  match c with
  | Cop.bin_case_i sg => both_int (sem_int sg) (sem_cast t1 t) (sem_cast t2 t)
  | Cop.bin_case_f => both_float (sem_float) (sem_cast t1 t) (sem_cast t2 t)
  | Cop.bin_case_s => both_single (sem_single) (sem_cast t1 t) (sem_cast t2 t)
  | Cop.bin_case_l sg => both_long (sem_long sg) (sem_cast t1 t) (sem_cast t2 t)
  | bin_default => fun _ _ => None
  end.

Definition sem_add_ptr_int {CS: compspecs} ty si v1 v2 :=
  if complete_type cenv_cs ty
  then Cop.sem_add_ptr_int cenv_cs ty si v1 v2
  else None.

Definition sem_add_int_ptr {CS: compspecs} ty si v1 v2 :=
 if complete_type cenv_cs ty
  then Cop.sem_add_ptr_int cenv_cs ty si v2 v1
  else None.

Definition sem_add_ptr_long {CS: compspecs} ty v1 v2 :=
 if complete_type cenv_cs ty
  then Cop.sem_add_ptr_long cenv_cs ty v1 v2
  else None.

Definition sem_add_long_ptr {CS: compspecs} ty v1 v2 :=
 if complete_type cenv_cs ty
  then Cop.sem_add_ptr_long cenv_cs ty v2 v1
  else None.

Definition sem_add {CS: compspecs} (t1:type) (t2:type):  val->val->option val :=
  match classify_add t1 t2 with
  | add_case_pi ty si =>
      sem_add_ptr_int ty si
  | add_case_pl ty =>
      sem_add_ptr_long ty
  | add_case_ip si ty =>
      sem_add_int_ptr ty si
  | add_case_lp ty =>
      sem_add_long_ptr ty
  | add_default =>
      sem_binarith
        (fun sg n1 n2 => Some(Vint(Int.add n1 n2)))
        (fun sg n1 n2 => Some(Vlong(Int64.add n1 n2)))
        (fun n1 n2 => Some(Vfloat(Float.add n1 n2)))
        (fun n1 n2 => Some(Vsingle(Float32.add n1 n2)))
        t1 t2
  end.

Definition sem_sub_pi {CS: compspecs} (ty:type) (si: signedness) (v1 v2 : val) : option val :=
    if complete_type cenv_cs ty
     then match v1, v2 with
      | Vptr b1 ofs1, Vint n2 =>
          let n2 := ptrofs_of_int si n2 in
          Some (Vptr b1 (Ptrofs.sub ofs1 (Ptrofs.mul (Ptrofs.repr (sizeof ty)) n2)))
      | Vint n1, Vint n2 =>
          if Archi.ptr64 then None else Some (Vint (Int.sub n1 (Int.mul (Int.repr (sizeof ty)) n2)))
      | Vlong n1, Vint n2 =>
          let n2 := cast_int_long si n2 in
          if Archi.ptr64 then Some (Vlong (Int64.sub n1 (Int64.mul (Int64.repr (sizeof ty)) n2))) else None
      | _,  _ => None
      end
  else None.

Definition sem_sub_pl {CS: compspecs} (ty:type) (v1 v2 : val) : option val :=
     if complete_type cenv_cs ty
     then match v1, v2 with
      | Vptr b1 ofs1, Vlong n2 =>
          let n2 := Ptrofs.of_int64 n2 in
          Some (Vptr b1 (Ptrofs.sub ofs1 (Ptrofs.mul (Ptrofs.repr (sizeof ty)) n2)))
      | Vint n1, Vlong n2 =>
          let n2 := Int.repr (Int64.unsigned n2) in
          if Archi.ptr64 then None else Some (Vint (Int.sub n1 (Int.mul (Int.repr (sizeof ty)) n2)))
      | Vlong n1, Vlong n2 =>
          if Archi.ptr64 then Some (Vlong (Int64.sub n1 (Int64.mul (Int64.repr (sizeof ty)) n2))) else None
      | _,  _ => None
      end
     else None.

Definition sem_sub_pp {CS: compspecs} (ty:type) (v1 v2 : val) : option val :=
     if complete_type cenv_cs ty
     then match v1,v2 with
      | Vptr b1 ofs1, Vptr b2 ofs2 =>
          if eq_block b1 b2 then
            let sz := sizeof ty in
            if zlt 0 sz && zle sz Ptrofs.max_signed
            then Some (Vptrofs (Ptrofs.divs (Ptrofs.sub ofs1 ofs2) (Ptrofs.repr sz)))
            else None
          else None
      | _, _ => None
      end
      else None.

Definition sem_sub_default (t1 t2:type) (v1 v2 : val) : option val :=
 sem_binarith
        (fun sg n1 n2 => Some(Vint(Int.sub n1 n2)))
        (fun sg n1 n2 => Some(Vlong(Int64.sub n1 n2)))
        (fun n1 n2 => Some(Vfloat(Float.sub n1 n2)))
        (fun n1 n2 => Some(Vsingle(Float32.sub n1 n2)))
        t1 t2 v1 v2.

Definition sem_sub {CS: compspecs} (t1:type) (t2:type) : val -> val -> option val :=
  match Cop.classify_sub t1 t2 with
  | Cop.sub_case_pi ty si=> sem_sub_pi  ty si
  | Cop.sub_case_pl ty => sem_sub_pl  ty
  | Cop.sub_case_pp ty => sem_sub_pp ty
  | sub_default => sem_sub_default t1 t2
  end.

Definition sem_mul (t1:type) (t2:type) (v1:val)  (v2: val)  : option val :=
  sem_binarith
    (fun sg n1 n2 => Some(Vint(Int.mul n1 n2)))
    (fun sg n1 n2 => Some(Vlong(Int64.mul n1 n2)))
    (fun n1 n2 => Some(Vfloat(Float.mul n1 n2)))
    (fun n1 n2 => Some(Vsingle(Float32.mul n1 n2)))
    t1 t2 v1 v2.

Definition sem_div (t1:type) (t2:type) (v1:val)  (v2: val) : option val :=
  sem_binarith
    (fun sg n1 n2 => Some(Vint (match sg with | Signed => Int.divs | Unsigned => Int.divu end n1 n2)))
    (fun sg n1 n2 => Some(Vlong (match sg with | Signed => Int64.divs | Unsigned => Int64.divu end n1 n2)))
    (fun n1 n2 => Some(Vfloat(Float.div n1 n2)))
    (fun n1 n2 => Some(Vsingle(Float32.div n1 n2)))
    t1 t2 v1 v2.

Definition sem_mod (t1:type) (t2:type) (v1:val)  (v2: val) : option val :=
  sem_binarith
    (fun sg n1 n2 => Some(Vint (match sg with | Signed => Int.mods | Unsigned => Int.modu end n1 n2)))
    (fun sg n1 n2 => Some(Vlong (match sg with | Signed => Int64.mods | Unsigned => Int64.modu end n1 n2)))
    (fun n1 n2 => None)
    (fun n1 n2 => None)
    t1 t2 v1 v2.

Definition sem_and (t1:type) (t2:type) (v1:val) (v2: val) : option val :=
  sem_binarith
    (fun sg n1 n2 => Some(Vint(Int.and n1 n2)))
    (fun sg n1 n2 => Some(Vlong(Int64.and n1 n2)))
    (fun n1 n2 => None)
    (fun n1 n2 => None)
    t1 t2 v1 v2.

Definition sem_or (t1:type) (t2:type) (v1:val)  (v2: val) : option val :=
  sem_binarith
    (fun sg n1 n2 => Some(Vint(Int.or n1 n2)))
    (fun sg n1 n2 => Some(Vlong(Int64.or n1 n2)))
    (fun n1 n2 => None)
    (fun n1 n2 => None)
    t1 t2 v1 v2.

Definition sem_xor (t1:type) (t2:type) (v1:val)  (v2: val) : option val :=
  sem_binarith
    (fun sg n1 n2 => Some(Vint(Int.xor n1 n2)))
    (fun sg n1 n2 => Some(Vlong(Int64.xor n1 n2)))
    (fun n1 n2 => None)
    (fun n1 n2 => None)
    t1 t2 v1 v2.

Definition sem_shift_ii sem_int (sg:signedness) v1 v2 : option val :=
      match v1, v2 with
      | Vint n1, Vint n2 =>
            Some(Vint(sem_int sg n1 n2))
      | _, _ => None
      end.

Definition sem_shift_il sem_int (sg:signedness) v1 v2 : option val :=
match v1, v2 with
      | Vint n1, Vlong n2 =>
            Some(Vint(sem_int sg n1 (Int64.loword n2)))
      | _, _ => None
      end.

Definition sem_shift_li sem_long (sg:signedness) v1 v2 : option val :=
match v1, v2 with
      | Vlong n1, Vint n2 =>
            Some(Vlong(sem_long sg n1 (Int64.repr (Int.unsigned n2))))
      | _, _ => None
      end.

Definition sem_shift_ll sem_long (sg:signedness) v1 v2 : option val :=
 match v1, v2 with
      | Vlong n1, Vlong n2 =>
            Some(Vlong(sem_long sg n1 n2))
      | _, _ => None
      end.

Definition sem_shift
    (t1: type) (t2: type) (sem_int: signedness -> int -> int -> int)
    (sem_long: signedness -> int64 -> int64 -> int64) : val -> val -> option val :=
  match Cop.classify_shift t1 t2 with
  | Cop.shift_case_ii sg => sem_shift_ii sem_int sg
  | Cop.shift_case_il sg => sem_shift_il sem_int sg
  | Cop.shift_case_li sg => sem_shift_li sem_long sg
  | Cop.shift_case_ll sg => sem_shift_ll sem_long sg
  | shift_default => fun v1 v2 => None
  end.

Definition sem_shl (t1:type) (t2:type) (v1:val) (v2: val)  : option val :=
  sem_shift  t1 t2
    (fun sg n1 n2 => Int.shl n1 n2)
    (fun sg n1 n2 => Int64.shl n1 n2)
    v1 v2.

Definition sem_shr (t1:type) (t2:type) (v1:val) (v2: val)  : option val :=
  sem_shift  t1 t2
    (fun sg n1 n2 => match sg with Signed => Int.shr n1 n2 | Unsigned => Int.shru n1 n2 end)
    (fun sg n1 n2 => match sg with Signed => Int64.shr n1 n2 | Unsigned => Int64.shru n1 n2 end)
    v1 v2.

Definition true2 (b : block) (i : Z) := true.

Definition sem_cmp_pp c v1 v2 :=
  option_map Val.of_bool
   (if Archi.ptr64
    then Val.cmplu_bool true2 c v1 v2
    else Val.cmpu_bool true2 c v1 v2).

Definition sem_cmp_pi si c v1 v2 :=
      match v2 with
      | Vint n2 => sem_cmp_pp c v1 (Vptrofs (ptrofs_of_int si n2))
      | Vptr _ _ => if Archi.ptr64 then None else sem_cmp_pp c v1 v2
      | _ => None
      end.

Definition sem_cmp_ip si c v1 v2 :=
      match v1 with
      | Vint n1 => sem_cmp_pp c (Vptrofs (ptrofs_of_int si n1)) v2
      | Vptr _ _ => if Archi.ptr64 then None else sem_cmp_pp c v1 v2
      | _ => None
      end.

Definition sem_cmp_pl c v1 v2 :=
      match v2 with
      | Vlong n2 => sem_cmp_pp c v1 (Vptrofs (Ptrofs.of_int64 n2))
      | Vptr _ _ => if Archi.ptr64 then sem_cmp_pp c v1 v2 else None
      | _ => None
      end.

Definition sem_cmp_lp c v1 v2 :=
      match v1 with
      | Vlong n1 => sem_cmp_pp c (Vptrofs (Ptrofs.of_int64 n1)) v2
      | Vptr _ _ => if Archi.ptr64 then sem_cmp_pp c v1 v2 else None
      | _ => None
      end.

Definition sem_cmp_default c t1 t2 :=
 sem_binarith
        (fun sg n1 n2 =>
            Some(Val.of_bool(match sg with Signed => Int.cmp c n1 n2 | Unsigned => Int.cmpu c n1 n2 end)))
        (fun sg n1 n2 =>
            Some(Val.of_bool(match sg with Signed => Int64.cmp c n1 n2 | Unsigned => Int64.cmpu c n1 n2 end)))
        (fun n1 n2 =>
            Some(Val.of_bool(Float.cmp c n1 n2)))
        (fun n1 n2 =>
            Some(Val.of_bool(Float32.cmp c n1 n2)))
        t1 t2 .

Definition sem_cmp (c:comparison) (t1: type) (t2: type) : val -> val ->  option val :=
  match Cop.classify_cmp t1 t2 with
  | Cop.cmp_case_pp =>
     if orb (eqb_type t1 int_or_ptr_type) (eqb_type t2 int_or_ptr_type)
            then (fun _ _ => None)
     else sem_cmp_pp c
  | Cop.cmp_case_pi si =>
     if eqb_type t1 int_or_ptr_type
            then (fun _ _ => None)
     else sem_cmp_pi si c
  | Cop.cmp_case_ip si =>
     if eqb_type t2 int_or_ptr_type
            then (fun _ _ => None)
     else sem_cmp_ip si c
  | Cop.cmp_case_pl =>
     if eqb_type t1 int_or_ptr_type
            then (fun _ _ => None)
     else sem_cmp_pl c
  | Cop.cmp_case_lp =>
     if eqb_type t2 int_or_ptr_type
            then (fun _ _ => None)
     else sem_cmp_lp c
  | Cop.cmp_default => sem_cmp_default c t1 t2
  end.

Definition sem_unary_operation
            (op: Cop.unary_operation) (ty: type) (v: val): option val :=
  match op with
  | Cop.Onotbool => sem_notbool ty v
  | Cop.Onotint => sem_notint ty v
  | Cop.Oneg => sem_neg ty v
  | Cop.Oabsfloat => sem_absfloat ty v
  end.

Definition sem_binary_operation'
    {CS: compspecs} (op: Cop.binary_operation)
    (t1:type) (t2: type) : val -> val -> option val :=
  match op with
  | Cop.Oadd => sem_add t1 t2
  | Cop.Osub => sem_sub t1 t2
  | Cop.Omul => sem_mul t1 t2
  | Cop.Omod => sem_mod t1 t2
  | Cop.Odiv => sem_div t1 t2
  | Cop.Oand => sem_and t1 t2
  | Cop.Oor  => sem_or t1 t2
  | Cop.Oxor  => sem_xor t1 t2
  | Cop.Oshl => sem_shl t1 t2
  | Cop.Oshr  => sem_shr t1 t2
  | Cop.Oeq => sem_cmp Ceq t1 t2
  | Cop.One => sem_cmp Cne t1 t2
  | Cop.Olt => sem_cmp Clt t1 t2
  | Cop.Ogt => sem_cmp Cgt t1 t2
  | Cop.Ole => sem_cmp Cle t1 t2
  | Cop.Oge => sem_cmp Cge t1 t2
  end.

Definition eval_unop (op: Cop.unary_operation) (t1 : type) :=
       force_val1 (Clight_Cop2.sem_unary_operation op t1).

Definition eval_binop {CS:compspecs} (op: Cop.binary_operation) (t1 t2 : type) :=
       force_val2 (Clight_Cop2.sem_binary_operation'  op t1 t2).

Definition eval_cast (t1 t2 : type) :=
  force_val1 (sem_cast t1 t2).

Definition eval_field {CS: compspecs} (ty: type) (fld: ident) : val -> val :=
          match ty with
             | Tstruct id att =>
                 match cenv_cs ! id with
                 | Some co =>
                         match field_offset cenv_cs fld (co_members co) with
                         | Errors.OK delta => offset_val delta
                         | _ => always Vundef
                         end
                 | _ => always Vundef
                 end
             | Tunion id att =>
                 match cenv_cs ! id with
                 | Some co => force_ptr
                 | _ => always Vundef
                 end
             | _ => always Vundef
          end.

Definition eval_var (id:ident) (ty: type) (rho: environ) : val :=
                         match Map.get (ve_of rho) id with
                         | Some (b,ty') => if eqb_type ty ty'
                                                    then Vptr b Ptrofs.zero
                                                    else Vundef
                         | None =>
                            match Map.get (ge_of rho) id with
                            | Some b => Vptr b Ptrofs.zero
                            | None => Vundef
                            end
                        end.

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

Fixpoint eval_exprlist {CS: compspecs} (et: list type) (el:list expr) : environ -> list val :=
 match et, el with
 | t::et', e::el' =>
    `(@cons val) (`force_val (`(sem_cast (typeof e) t) (eval_expr e))) (eval_exprlist et' el')
 | _, _ => `nil
 end.

Definition JMeq {A:Type} (x:A) {B:Type} (y: B): Prop :=
  {H: @eq Type A B | @eq_rect Type A (fun T: Type => T) x B H = y}.

Lemma JMeq_inl: forall (A: Type) (B: Type) (C: Type) (D: Type) (x: A) (y: C), @eq Type B D -> JMeq x y -> @JMeq (A + B) (inl x) (C + D) (inl y).
Proof.
  intros.
  destruct H0 as [?H ?H].
  pose (f_equal2 :=
          fun (A1 : Type) (A2 : Type) (B : Type) (f : forall (_ : A1) (_ : A2), B)
            (x1 y1 : A1) (x2 y2 : A2) (H : @eq A1 x1 y1) =>
          match H in (eq _ y) return (forall _ : @eq A2 x2 y2, @eq B (f x1 x2) (f y y2)) with
          | eq_refl => fun H0 : @eq A2 x2 y2 => match H0 in (eq _ y) return (@eq B (f x1 x2) (f x1 y)) with
                                                | eq_refl => @eq_refl B (f x1 x2)
                                                end
          end).
  exists (f_equal2 _ _ _ sum _ _ _ _ H0 H).
  destruct H, H0.
  rewrite <- H1.
  unfold f_equal2.
  simpl.
  apply eq_refl.
Qed.

Lemma list_func_JMeq': forall {A: Type} {B: Type} (a: list A) (b: list B) (a': A) (b': B) (f: forall X, list X -> X -> X), JMeq a b -> JMeq a' b' -> JMeq (f A a a') (f B b b').
Proof.
  intros.
  destruct H as [?H ?H], H0 as [?H ?H].
  exists H0.
  rewrite <- H1, <- H2.
  destruct H0.
  simpl.
  rewrite <- eq_rect_eq.
  apply eq_refl.
Qed.

Lemma closed_wrt_map_subst':
   forall {A: Type} id e (Q: list (environ -> A)),
         Forall (closed_wrt_vars (eq id)) Q ->
         @map (LiftEnviron A) _ (subst id e) Q = Q.
