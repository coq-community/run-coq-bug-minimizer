(* -*- mode: coq; coq-prog-args: ("-emacs" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/msl" "VST.msl" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/sepcomp" "VST.sepcomp" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/veric" "VST.veric" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/floyd" "VST.floyd" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/progs" "VST.progs" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/concurrency" "VST.concurrency" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/wand_demo" "wand_demo" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/sha" "sha" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/hmacfcf" "hmacfcf" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/tweetnacl20140427" "tweetnacl20140427" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/hmacdrbg" "hmacdrbg" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/aes" "aes" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/mailbox" "mailbox" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/atomics" "atomics" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/lib" "compcert.lib" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/common" "compcert.common" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/x86_32" "compcert.x86_32" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/x86" "compcert.x86" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/cfrontend" "compcert.cfrontend" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/exportclight" "compcert.exportclight" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Flocq" "Flocq" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-top" "bug_01" "-native-compiler" "no" "-native-compiler" "no") -*- *)
(* File reduced by coq-bug-finder from original input, then from 700 lines to 38 lines, then from 264 lines to 2576 lines, then from 2559 lines to 78 lines, then from 302 lines to 424 lines, then from 411 lines to 78 lines, then from 297 lines to 510 lines, then from 513 lines to 79 lines, then from 286 lines to 1490 lines, then from 1492 lines to 80 lines, then from 286 lines to 852 lines, then from 854 lines to 219 lines, then from 423 lines to 1272 lines, then from 1271 lines to 233 lines, then from 431 lines to 2373 lines, then from 2372 lines to 276 lines, then from 437 lines to 647 lines, then from 651 lines to 284 lines, then from 426 lines to 1740 lines, then from 1740 lines to 287 lines, then from 428 lines to 1236 lines, then from 1239 lines to 289 lines, then from 425 lines to 1938 lines, then from 1916 lines to 327 lines, then from 463 lines to 779 lines, then from 783 lines to 329 lines, then from 457 lines to 2085 lines, then from 2086 lines to 343 lines, then from 467 lines to 900 lines, then from 903 lines to 483 lines, then from 605 lines to 1910 lines, then from 1911 lines to 639 lines, then from 759 lines to 1357 lines, then from 1360 lines to 686 lines, then from 804 lines to 1176 lines, then from 1176 lines to 806 lines, then from 905 lines to 787 lines, then from 905 lines to 2763 lines, then from 2762 lines to 834 lines, then from 948 lines to 1230 lines, then from 1234 lines to 861 lines, then from 975 lines to 1840 lines, then from 1844 lines to 882 lines, then from 990 lines to 1277 lines, then from 1274 lines to 882 lines, then from 989 lines to 1123 lines, then from 1127 lines to 893 lines, then from 1000 lines to 2432 lines, then from 2434 lines to 1500 lines, then from 1565 lines to 1275 lines, then from 1381 lines to 2656 lines, then from 2654 lines to 1283 lines, then from 1389 lines to 2973 lines, then from 2977 lines to 1698 lines, then from 1653 lines to 1536 lines, then from 1642 lines to 1789 lines, then from 1793 lines to 1569 lines, then from 1661 lines to 2754 lines, then from 2758 lines to 1712 lines, then from 1774 lines to 1683 lines, then from 1774 lines to 4389 lines, then from 4393 lines to 1744 lines, then from 1834 lines to 2585 lines, then from 2589 lines to 1873 lines, then from 1888 lines to 1773 lines, then from 1860 lines to 3326 lines, then from 3330 lines to 1821 lines, then from 1897 lines to 6748 lines, then from 6751 lines to 3832 lines *)
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
Require VST.msl.simple_CCC.
Require Coq.Logic.ClassicalFacts.
Require Coq.Logic.FunctionalExtensionality.
Require VST.msl.Axioms.
Require Coq.Logic.EqdepFacts.
Require VST.msl.Extensionality.
Require VST.msl.seplog.
Require Coq.Setoids.Setoid.
Require Coq.Lists.List.
Require Coq.Bool.Bool.
Require Coq.Relations.Relations.
Require Coq.micromega.Lia.
Require VST.msl.base.
Require Coq.funind.Recdef.
Require Coq.Wellfounded.Wellfounded.
Require VST.msl.ageable.
Require VST.msl.sepalg.
Require VST.msl.sepalg_generators.
Require VST.msl.age_sepalg.
Require VST.msl.predicates_hered.
Require VST.msl.eq_dec.
Require VST.msl.psepalg.
Require VST.msl.cjoins.
Require VST.msl.cross_split.
Require VST.msl.predicates_sl.
Require VST.msl.subtypes.
Require VST.msl.subtypes_sl.
Require VST.msl.predicates_rec.
Require VST.msl.contractive.
Require Coq.Structures.GenericMinMax.
Require VST.msl.boolean_alg.
Require VST.msl.functors.
Require VST.msl.knot_full_variant.
Require VST.msl.sig_isomorphism.
Require Coq.Logic.Eqdep_dec.
Require VST.msl.knot.
Require VST.msl.knot_shims.
Require VST.msl.sepalg_functors.
Require VST.msl.knot_full_sa.
Require VST.msl.corable.
Require VST.msl.combiner_sa.
Require Coq.Numbers.Natural.Peano.NPeano.
Require Coq.ZArith.ZArith.
Require Coq.Arith.Max.
Require VST.msl.tree_shares.
Require VST.msl.shares.
Require VST.msl.pshares.
Require VST.msl.msl_standard.
Require VST.msl.normalize.
Require VST.msl.alg_seplog.
Require VST.msl.ghost.
Require VST.msl.ghost_seplog.
Require VST.msl.log_normalize.
Require Coq.Classes.Equivalence.
Require Coq.Classes.EquivDec.
Require Coq.Strings.String.
Require Coq.ZArith.Znumtheory.
Require compcert.lib.Coqlib.
Require compcert.lib.Maps.
Require compcert.common.Errors.
Require Coq.ZArith.Zquot.
Require Coq.ZArith.Zwf.
Require Coq.micromega.Psatz.
Require compcert.lib.Zbits.
Require Flocq.IEEE754.Binary.
Require Flocq.IEEE754.Bits.
Require compcert.x86_32.Archi.
Module Export compcert_DOT_lib_DOT_Integers_WRAPPED.
Module Export Integers.
Import Coq.Logic.Eqdep_dec.
Import Coq.ZArith.Zquot.
Import Coq.ZArith.Zwf.
Import compcert.lib.Coqlib.
Import compcert.lib.Zbits.

 

Inductive comparison : Type :=
  | Ceq : comparison                
  | Cne : comparison                
  | Clt : comparison                
  | Cle : comparison                
  | Cgt : comparison                
  | Cge : comparison.
              

Definition negate_comparison (c: comparison): comparison :=
  match c with
  | Ceq => Cne
  | Cne => Ceq
  | Clt => Cge
  | Cle => Cgt
  | Cgt => Cle
  | Cge => Clt
  end.

Definition swap_comparison (c: comparison): comparison :=
  match c with
  | Ceq => Ceq
  | Cne => Cne
  | Clt => Cgt
  | Cle => Cge
  | Cgt => Clt
  | Cge => Cle
  end.

 

Module Type WORDSIZE.
  Parameter wordsize: nat.
  Axiom wordsize_not_zero: wordsize <> 0%nat.
End WORDSIZE.

 
Local Unset Elimination Schemes.
Local Unset Case Analysis Schemes.

Module Make(WS: WORDSIZE).

Definition wordsize: nat := WS.wordsize.
Definition zwordsize: Z := Z.of_nat wordsize.
Definition modulus : Z := two_power_nat wordsize.
Definition half_modulus : Z := modulus / 2.
Definition max_unsigned : Z := modulus - 1.
Definition max_signed : Z := half_modulus - 1.
Definition min_signed : Z := - half_modulus.

Remark wordsize_pos: zwordsize > 0.
admit.
Defined.

Remark modulus_power: modulus = two_p zwordsize.
admit.
Defined.

Remark modulus_gt_one: modulus > 1.
admit.
Defined.

Remark modulus_pos: modulus > 0.
admit.
Defined.

Global Hint Resolve modulus_pos: ints.

 

 

Record int: Type := mkint { intval: Z; intrange: -1 < intval < modulus }.

 

Definition Z_mod_modulus (x: Z) : Z :=
  match x with
  | Z0 => 0
  | Zpos p => P_mod_two_p p wordsize
  | Zneg p => let r := P_mod_two_p p wordsize in if zeq r 0 then 0 else modulus - r
  end.

Lemma Z_mod_modulus_range:
  forall x, 0 <= Z_mod_modulus x < modulus.
Proof (Z_mod_two_p_range wordsize).

Lemma Z_mod_modulus_range':
  forall x, -1 < Z_mod_modulus x < modulus.
admit.
Defined.

Lemma Z_mod_modulus_eq:
  forall x, Z_mod_modulus x = x mod modulus.
Proof (Z_mod_two_p_eq wordsize).

 

Definition unsigned (n: int) : Z := intval n.

Definition signed (n: int) : Z :=
  let x := unsigned n in
  if zlt x half_modulus then x else x - modulus.

 

Definition repr (x: Z) : int :=
  mkint (Z_mod_modulus x) (Z_mod_modulus_range' x).

Definition zero := repr 0.
Definition one  := repr 1.
Definition mone := repr (-1).
Definition iwordsize := repr zwordsize.

Lemma mkint_eq:
  forall x y Px Py, x = y -> mkint x Px = mkint y Py.
admit.
Defined.

Lemma eq_dec: forall (x y: int), {x = y} + {x <> y}.
admit.
Defined.

 

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

Definition rol (x y: int) : int :=
  let n := (unsigned y) mod zwordsize in
  repr (Z.lor (Z.shiftl (unsigned x) n) (Z.shiftr (unsigned x) (zwordsize - n))).
Definition ror (x y: int) : int :=
  let n := (unsigned y) mod zwordsize in
  repr (Z.lor (Z.shiftr (unsigned x) n) (Z.shiftl (unsigned x) (zwordsize - n))).

Definition rolm (x a m: int): int := and (rol x a) m.

 

Definition shrx (x y: int): int :=
  divs x (shl one y).

 

Definition mulhu (x y: int): int := repr ((unsigned x * unsigned y) / modulus).
Definition mulhs (x y: int): int := repr ((signed x * signed y) / modulus).

 

Definition negative (x: int): int :=
  if lt x zero then one else zero.

Definition add_carry (x y cin: int): int :=
  if zlt (unsigned x + unsigned y + unsigned cin) modulus then zero else one.

Definition add_overflow (x y cin: int): int :=
  let s := signed x + signed y + signed cin in
  if zle min_signed s && zle s max_signed then zero else one.

Definition sub_borrow (x y bin: int): int :=
  if zlt (unsigned x - unsigned y - unsigned bin) 0 then one else zero.

Definition sub_overflow (x y bin: int): int :=
  let s := signed x - signed y - signed bin in
  if zle min_signed s && zle s max_signed then zero else one.

 

Definition shr_carry (x y: int) : int :=
  if lt x zero && negb (eq (and x (sub (shl one y) one)) zero)
  then one else zero.

 

Definition zero_ext (n: Z) (x: int) : int := repr (Zzero_ext n (unsigned x)).
Definition sign_ext (n: Z) (x: int) : int := repr (Zsign_ext n (unsigned x)).

 

Definition one_bits (x: int) : list int :=
  List.map repr (Z_one_bits wordsize (unsigned x) 0).

 

Definition is_power2 (x: int) : option int :=
  match Z_is_power2 (unsigned x) with
  | Some i => Some (repr i)
  | None => None
  end.

 

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

Definition is_false (x: int) : Prop := x = zero.
Definition is_true  (x: int) : Prop := x <> zero.
Definition notbool  (x: int) : int  := if eq x zero then one else zero.

 

Definition divmodu2 (nhi nlo: int) (d: int) : option (int * int) :=
  if eq_dec d zero then None else
   (let (q, r) := Z.div_eucl (unsigned nhi * modulus + unsigned nlo) (unsigned d) in
    if zle q max_unsigned then Some(repr q, repr r) else None).

Definition divmods2 (nhi nlo: int) (d: int) : option (int * int) :=
  if eq_dec d zero then None else
   (let (q, r) := Z.quotrem (signed nhi * modulus + unsigned nlo) (signed d) in
    if zle min_signed q && zle q max_signed then Some(repr q, repr r) else None).

 

 

Remark half_modulus_power:
  half_modulus = two_p (zwordsize - 1).
admit.
Defined.

Remark half_modulus_modulus: modulus = 2 * half_modulus.
admit.
Defined.

 

Remark half_modulus_pos: half_modulus > 0.
admit.
Defined.

Remark min_signed_neg: min_signed < 0.
admit.
Defined.

Remark max_signed_pos: max_signed >= 0.
admit.
Defined.

Remark wordsize_max_unsigned: zwordsize <= max_unsigned.
admit.
Defined.

Remark two_wordsize_max_unsigned: 2 * zwordsize - 1 <= max_unsigned.
admit.
Defined.

Remark max_signed_unsigned: max_signed < max_unsigned.
admit.
Defined.

Lemma unsigned_repr_eq:
  forall x, unsigned (repr x) = Z.modulo x modulus.
admit.
Defined.

Lemma signed_repr_eq:
  forall x, signed (repr x) = if zlt (Z.modulo x modulus) half_modulus then Z.modulo x modulus else Z.modulo x modulus - modulus.
admit.
Defined.

 

 

Definition eqm := eqmod modulus.

Lemma eqm_refl: forall x, eqm x x.
Proof (eqmod_refl modulus).
Global Hint Resolve eqm_refl: ints.

Lemma eqm_refl2:
  forall x y, x = y -> eqm x y.
Proof (eqmod_refl2 modulus).
Global Hint Resolve eqm_refl2: ints.

Lemma eqm_sym: forall x y, eqm x y -> eqm y x.
Proof (eqmod_sym modulus).
Global Hint Resolve eqm_sym: ints.

Lemma eqm_trans: forall x y z, eqm x y -> eqm y z -> eqm x z.
Proof (eqmod_trans modulus).
Global Hint Resolve eqm_trans: ints.

Lemma eqm_small_eq:
  forall x y, eqm x y -> 0 <= x < modulus -> 0 <= y < modulus -> x = y.
Proof (eqmod_small_eq modulus).
Global Hint Resolve eqm_small_eq: ints.

Lemma eqm_add:
  forall a b c d, eqm a b -> eqm c d -> eqm (a + c) (b + d).
Proof (eqmod_add modulus).
Global Hint Resolve eqm_add: ints.

Lemma eqm_neg:
  forall x y, eqm x y -> eqm (-x) (-y).
Proof (eqmod_neg modulus).
Global Hint Resolve eqm_neg: ints.

Lemma eqm_sub:
  forall a b c d, eqm a b -> eqm c d -> eqm (a - c) (b - d).
Proof (eqmod_sub modulus).
Global Hint Resolve eqm_sub: ints.

Lemma eqm_mult:
  forall a b c d, eqm a c -> eqm b d -> eqm (a * b) (c * d).
Proof (eqmod_mult modulus).
Global Hint Resolve eqm_mult: ints.

Lemma eqm_same_bits:
  forall x y,
  (forall i, 0 <= i < zwordsize -> Z.testbit x i = Z.testbit y i) ->
  eqm x y.
Proof (eqmod_same_bits wordsize).

Lemma same_bits_eqm:
  forall x y i,
  eqm x y ->
  0 <= i < zwordsize ->
  Z.testbit x i = Z.testbit y i.
Proof (same_bits_eqmod wordsize).

 

Lemma eqm_samerepr: forall x y, eqm x y -> repr x = repr y.
admit.
Defined.

Lemma eqm_unsigned_repr:
  forall z, eqm z (unsigned (repr z)).
admit.
Defined.
Global Hint Resolve eqm_unsigned_repr: ints.

Lemma eqm_unsigned_repr_l:
  forall a b, eqm a b -> eqm (unsigned (repr a)) b.
admit.
Defined.
Global Hint Resolve eqm_unsigned_repr_l: ints.

Lemma eqm_unsigned_repr_r:
  forall a b, eqm a b -> eqm a (unsigned (repr b)).
admit.
Defined.
Global Hint Resolve eqm_unsigned_repr_r: ints.

Lemma eqm_signed_unsigned:
  forall x, eqm (signed x) (unsigned x).
admit.
Defined.

Theorem unsigned_range:
  forall i, 0 <= unsigned i < modulus.
admit.
Defined.
Global Hint Resolve unsigned_range: ints.

Theorem unsigned_range_2:
  forall i, 0 <= unsigned i <= max_unsigned.
admit.
Defined.
Global Hint Resolve unsigned_range_2: ints.

Theorem signed_range:
  forall i, min_signed <= signed i <= max_signed.
admit.
Defined.

Theorem repr_unsigned:
  forall i, repr (unsigned i) = i.
admit.
Defined.
Global Hint Resolve repr_unsigned: ints.

Lemma repr_signed:
  forall i, repr (signed i) = i.
admit.
Defined.
Global Hint Resolve repr_signed: ints.

Opaque repr.

Lemma eqm_repr_eq: forall x y, eqm x (unsigned y) -> repr x = y.
admit.
Defined.

Theorem unsigned_repr:
  forall z, 0 <= z <= max_unsigned -> unsigned (repr z) = z.
admit.
Defined.
Global Hint Resolve unsigned_repr: ints.

Theorem signed_repr:
  forall z, min_signed <= z <= max_signed -> signed (repr z) = z.
admit.
Defined.

Theorem signed_eq_unsigned:
  forall x, unsigned x <= max_signed -> signed x = unsigned x.
admit.
Defined.

Theorem signed_positive:
  forall x, signed x >= 0 <-> unsigned x <= max_signed.
admit.
Defined.

 

Theorem unsigned_zero: unsigned zero = 0.
admit.
Defined.

Theorem unsigned_one: unsigned one = 1.
admit.
Defined.

Theorem unsigned_mone: unsigned mone = modulus - 1.
admit.
Defined.

Theorem signed_zero: signed zero = 0.
admit.
Defined.

Theorem signed_one: zwordsize > 1 -> signed one = 1.
admit.
Defined.

Theorem signed_mone: signed mone = -1.
admit.
Defined.

Theorem one_not_zero: one <> zero.
admit.
Defined.

Theorem unsigned_repr_wordsize:
  unsigned iwordsize = zwordsize.
admit.
Defined.

 

Theorem eq_sym:
  forall x y, eq x y = eq y x.
admit.
Defined.

Theorem eq_spec: forall (x y: int), if eq x y then x = y else x <> y.
admit.
Defined.

Theorem eq_true: forall x, eq x x = true.
admit.
Defined.

Theorem eq_false: forall x y, x <> y -> eq x y = false.
admit.
Defined.

Theorem same_if_eq: forall x y, eq x y = true -> x = y.
admit.
Defined.

Theorem eq_signed:
  forall x y, eq x y = if zeq (signed x) (signed y) then true else false.
admit.
Defined.

 

Theorem add_unsigned: forall x y, add x y = repr (unsigned x + unsigned y).
admit.
Defined.

Theorem add_signed: forall x y, add x y = repr (signed x + signed y).
admit.
Defined.

Theorem add_commut: forall x y, add x y = add y x.
admit.
Defined.

Theorem add_zero: forall x, add x zero = x.
admit.
Defined.

Theorem add_zero_l: forall x, add zero x = x.
admit.
Defined.

Theorem add_assoc: forall x y z, add (add x y) z = add x (add y z).
admit.
Defined.

Theorem add_permut: forall x y z, add x (add y z) = add y (add x z).
admit.
Defined.

Theorem add_neg_zero: forall x, add x (neg x) = zero.
admit.
Defined.

Theorem unsigned_add_carry:
  forall x y,
  unsigned (add x y) = unsigned x + unsigned y - unsigned (add_carry x y zero) * modulus.
admit.
Defined.

Corollary unsigned_add_either:
  forall x y,
  unsigned (add x y) = unsigned x + unsigned y
  \/ unsigned (add x y) = unsigned x + unsigned y - modulus.
admit.
Defined.

 

Theorem neg_repr: forall z, neg (repr z) = repr (-z).
admit.
Defined.

Theorem neg_zero: neg zero = zero.
admit.
Defined.

Theorem neg_involutive: forall x, neg (neg x) = x.
admit.
Defined.

Theorem neg_add_distr: forall x y, neg(add x y) = add (neg x) (neg y).
admit.
Defined.

 

Theorem sub_zero_l: forall x, sub x zero = x.
admit.
Defined.

Theorem sub_zero_r: forall x, sub zero x = neg x.
admit.
Defined.

Theorem sub_add_opp: forall x y, sub x y = add x (neg y).
admit.
Defined.

Theorem sub_idem: forall x, sub x x = zero.
admit.
Defined.

Theorem sub_add_l: forall x y z, sub (add x y) z = add (sub x z) y.
admit.
Defined.

Theorem sub_add_r: forall x y z, sub x (add y z) = add (sub x z) (neg y).
admit.
Defined.

Theorem sub_shifted:
  forall x y z,
  sub (add x z) (add y z) = sub x y.
admit.
Defined.

Theorem sub_signed:
  forall x y, sub x y = repr (signed x - signed y).
admit.
Defined.

Theorem unsigned_sub_borrow:
  forall x y,
  unsigned (sub x y) = unsigned x - unsigned y + unsigned (sub_borrow x y zero) * modulus.
admit.
Defined.

 

Theorem mul_commut: forall x y, mul x y = mul y x.
admit.
Defined.

Theorem mul_zero: forall x, mul x zero = zero.
admit.
Defined.

Theorem mul_one: forall x, mul x one = x.
admit.
Defined.

Theorem mul_mone: forall x, mul x mone = neg x.
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

Theorem neg_mul_distr_l:
  forall x y, neg(mul x y) = mul (neg x) y.
admit.
Defined.

Theorem neg_mul_distr_r:
   forall x y, neg(mul x y) = mul x (neg y).
admit.
Defined.

Theorem mul_signed:
  forall x y, mul x y = repr (signed x * signed y).
admit.
Defined.

 

Lemma modu_divu_Euclid:
  forall x y, y <> zero -> x = add (mul (divu x y) y) (modu x y).
admit.
Defined.

Theorem modu_divu:
  forall x y, y <> zero -> modu x y = sub x (mul (divu x y) y).
admit.
Defined.

Lemma mods_divs_Euclid:
  forall x y, x = add (mul (divs x y) y) (mods x y).
admit.
Defined.

Theorem mods_divs:
  forall x y, mods x y = sub x (mul (divs x y) y).
admit.
Defined.

Theorem divu_one:
  forall x, divu x one = x.
admit.
Defined.

Theorem divs_one:
  forall x, zwordsize > 1 -> divs x one = x.
admit.
Defined.

Theorem modu_one:
  forall x, modu x one = zero.
admit.
Defined.

Theorem divs_mone:
  forall x, divs x mone = neg x.
admit.
Defined.

Theorem mods_mone:
  forall x, mods x mone = zero.
admit.
Defined.

Theorem divmodu2_divu_modu:
  forall n d,
  d <> zero -> divmodu2 zero n d = Some (divu n d, modu n d).
admit.
Defined.

Lemma unsigned_signed:
  forall n, unsigned n = if lt n zero then signed n + modulus else signed n.
admit.
Defined.

Theorem divmods2_divs_mods:
  forall n d,
  d <> zero -> n <> repr min_signed \/ d <> mone ->
  divmods2 (if lt n zero then mone else zero) n d = Some (divs n d, mods n d).
admit.
Defined.

 

Definition testbit (x: int) (i: Z) : bool := Z.testbit (unsigned x) i.

Lemma testbit_repr:
  forall x i,
  0 <= i < zwordsize ->
  testbit (repr x) i = Z.testbit x i.
admit.
Defined.

Lemma same_bits_eq:
  forall x y,
  (forall i, 0 <= i < zwordsize -> testbit x i = testbit y i) ->
  x = y.
admit.
Defined.

Lemma bits_above:
  forall x i, i >= zwordsize -> testbit x i = false.
admit.
Defined.

Lemma bits_below:
  forall x i, i < 0 -> testbit x i = false.
admit.
Defined.

Lemma bits_zero:
  forall i, testbit zero i = false.
admit.
Defined.

Remark bits_one: forall n, testbit one n = zeq n 0.
admit.
Defined.

Lemma bits_mone:
  forall i, 0 <= i < zwordsize -> testbit mone i = true.
admit.
Defined.

Hint Rewrite bits_zero bits_mone : ints.

Lemma sign_bit_of_unsigned:
  forall x, testbit x (zwordsize - 1) = if zlt (unsigned x) half_modulus then false else true.
admit.
Defined.

Lemma bits_signed:
  forall x i, 0 <= i ->
  Z.testbit (signed x) i = testbit x (if zlt i zwordsize then i else zwordsize - 1).
admit.
Defined.

Lemma bits_le:
  forall x y,
  (forall i, 0 <= i < zwordsize -> testbit x i = true -> testbit y i = true) ->
  unsigned x <= unsigned y.
admit.
Defined.

 

Lemma bits_and:
  forall x y i, 0 <= i < zwordsize ->
  testbit (and x y) i = testbit x i && testbit y i.
admit.
Defined.

Lemma bits_or:
  forall x y i, 0 <= i < zwordsize ->
  testbit (or x y) i = testbit x i || testbit y i.
admit.
Defined.

Lemma bits_xor:
  forall x y i, 0 <= i < zwordsize ->
  testbit (xor x y) i = xorb (testbit x i) (testbit y i).
admit.
Defined.

Lemma bits_not:
  forall x i, 0 <= i < zwordsize ->
  testbit (not x) i = negb (testbit x i).
admit.
Defined.

Hint Rewrite bits_and bits_or bits_xor bits_not: ints.

Theorem and_commut: forall x y, and x y = and y x.
admit.
Defined.

Theorem and_assoc: forall x y z, and (and x y) z = and x (and y z).
admit.
Defined.

Theorem and_zero: forall x, and x zero = zero.
admit.
Defined.

Corollary and_zero_l: forall x, and zero x = zero.
admit.
Defined.

Theorem and_mone: forall x, and x mone = x.
admit.
Defined.

Corollary and_mone_l: forall x, and mone x = x.
admit.
Defined.

Theorem and_idem: forall x, and x x = x.
admit.
Defined.

Theorem or_commut: forall x y, or x y = or y x.
admit.
Defined.

Theorem or_assoc: forall x y z, or (or x y) z = or x (or y z).
admit.
Defined.

Theorem or_zero: forall x, or x zero = x.
admit.
Defined.

Corollary or_zero_l: forall x, or zero x = x.
admit.
Defined.

Theorem or_mone: forall x, or x mone = mone.
admit.
Defined.

Theorem or_idem: forall x, or x x = x.
admit.
Defined.

Theorem and_or_distrib:
  forall x y z,
  and x (or y z) = or (and x y) (and x z).
admit.
Defined.

Corollary and_or_distrib_l:
  forall x y z,
  and (or x y) z = or (and x z) (and y z).
admit.
Defined.

Theorem or_and_distrib:
  forall x y z,
  or x (and y z) = and (or x y) (or x z).
admit.
Defined.

Corollary or_and_distrib_l:
  forall x y z,
  or (and x y) z = and (or x z) (or y z).
admit.
Defined.

Theorem and_or_absorb: forall x y, and x (or x y) = x.
admit.
Defined.

Theorem or_and_absorb: forall x y, or x (and x y) = x.
admit.
Defined.

Theorem xor_commut: forall x y, xor x y = xor y x.
admit.
Defined.

Theorem xor_assoc: forall x y z, xor (xor x y) z = xor x (xor y z).
admit.
Defined.

Theorem xor_zero: forall x, xor x zero = x.
admit.
Defined.

Corollary xor_zero_l: forall x, xor zero x = x.
admit.
Defined.

Theorem xor_idem: forall x, xor x x = zero.
admit.
Defined.

Theorem xor_zero_one: xor zero one = one.
admit.
Defined.

Theorem xor_one_one: xor one one = zero.
admit.
Defined.

Theorem xor_zero_equal: forall x y, xor x y = zero -> x = y.
admit.
Defined.

Theorem xor_is_zero: forall x y, eq (xor x y) zero = eq x y.
admit.
Defined.

Theorem and_xor_distrib:
  forall x y z,
  and x (xor y z) = xor (and x y) (and x z).
admit.
Defined.

Theorem and_le:
  forall x y, unsigned (and x y) <= unsigned x.
admit.
Defined.

Theorem or_le:
  forall x y, unsigned x <= unsigned (or x y).
admit.
Defined.

 

Theorem not_involutive:
  forall (x: int), not (not x) = x.
admit.
Defined.

Theorem not_zero:
  not zero = mone.
admit.
Defined.

Theorem not_mone:
  not mone = zero.
admit.
Defined.

Theorem not_or_and_not:
  forall x y, not (or x y) = and (not x) (not y).
admit.
Defined.

Theorem not_and_or_not:
  forall x y, not (and x y) = or (not x) (not y).
admit.
Defined.

Theorem and_not_self:
  forall x, and x (not x) = zero.
admit.
Defined.

Theorem or_not_self:
  forall x, or x (not x) = mone.
admit.
Defined.

Theorem xor_not_self:
  forall x, xor x (not x) = mone.
admit.
Defined.

Lemma unsigned_not:
  forall x, unsigned (not x) = max_unsigned - unsigned x.
admit.
Defined.

Theorem not_neg:
  forall x, not x = add (neg x) mone.
admit.
Defined.

Theorem neg_not:
  forall x, neg x = add (not x) one.
admit.
Defined.

Theorem sub_add_not:
  forall x y, sub x y = add (add x (not y)) one.
admit.
Defined.

Theorem sub_add_not_3:
  forall x y b,
  b = zero \/ b = one ->
  sub (sub x y) b = add (add x (not y)) (xor b one).
admit.
Defined.

Theorem sub_borrow_add_carry:
  forall x y b,
  b = zero \/ b = one ->
  sub_borrow x y b = xor (add_carry x (not y) (xor b one)) one.
admit.
Defined.

 

Lemma Z_add_is_or:
  forall i, 0 <= i ->
  forall x y,
  (forall j, 0 <= j <= i -> Z.testbit x j && Z.testbit y j = false) ->
  Z.testbit (x + y) i = Z.testbit x i || Z.testbit y i.
admit.
Defined.

Theorem add_is_or:
  forall x y,
  and x y = zero ->
  add x y = or x y.
admit.
Defined.

Theorem xor_is_or:
  forall x y, and x y = zero -> xor x y = or x y.
admit.
Defined.

Theorem add_is_xor:
  forall x y,
  and x y = zero ->
  add x y = xor x y.
admit.
Defined.

Theorem add_and:
  forall x y z,
  and y z = zero ->
  add (and x y) (and x z) = and x (or y z).
admit.
Defined.

 

Lemma bits_shl:
  forall x y i,
  0 <= i < zwordsize ->
  testbit (shl x y) i =
  if zlt i (unsigned y) then false else testbit x (i - unsigned y).
admit.
Defined.

Lemma bits_shru:
  forall x y i,
  0 <= i < zwordsize ->
  testbit (shru x y) i =
  if zlt (i + unsigned y) zwordsize then testbit x (i + unsigned y) else false.
admit.
Defined.

Lemma bits_shr:
  forall x y i,
  0 <= i < zwordsize ->
  testbit (shr x y) i =
  testbit x (if zlt (i + unsigned y) zwordsize then i + unsigned y else zwordsize - 1).
admit.
Defined.

Hint Rewrite bits_shl bits_shru bits_shr: ints.

Theorem shl_zero: forall x, shl x zero = x.
admit.
Defined.

Lemma bitwise_binop_shl:
  forall f f' x y n,
  (forall x y i, 0 <= i < zwordsize -> testbit (f x y) i = f' (testbit x i) (testbit y i)) ->
  f' false false = false ->
  f (shl x n) (shl y n) = shl (f x y) n.
admit.
Defined.

Theorem and_shl:
  forall x y n,
  and (shl x n) (shl y n) = shl (and x y) n.
admit.
Defined.

Theorem or_shl:
  forall x y n,
  or (shl x n) (shl y n) = shl (or x y) n.
admit.
Defined.

Theorem xor_shl:
  forall x y n,
  xor (shl x n) (shl y n) = shl (xor x y) n.
admit.
Defined.

Lemma ltu_inv:
  forall x y, ltu x y = true -> 0 <= unsigned x < unsigned y.
admit.
Defined.

Lemma ltu_iwordsize_inv:
  forall x, ltu x iwordsize = true -> 0 <= unsigned x < zwordsize.
admit.
Defined.

Theorem shl_shl:
  forall x y z,
  ltu y iwordsize = true ->
  ltu z iwordsize = true ->
  ltu (add y z) iwordsize = true ->
  shl (shl x y) z = shl x (add y z).
admit.
Defined.

Theorem sub_ltu:
  forall x y,
    ltu x y = true ->
    0 <= unsigned y - unsigned x <= unsigned y.
admit.
Defined.

Theorem shru_zero: forall x, shru x zero = x.
admit.
Defined.

Lemma bitwise_binop_shru:
  forall f f' x y n,
  (forall x y i, 0 <= i < zwordsize -> testbit (f x y) i = f' (testbit x i) (testbit y i)) ->
  f' false false = false ->
  f (shru x n) (shru y n) = shru (f x y) n.
admit.
Defined.

Theorem and_shru:
  forall x y n,
  and (shru x n) (shru y n) = shru (and x y) n.
admit.
Defined.

Theorem or_shru:
  forall x y n,
  or (shru x n) (shru y n) = shru (or x y) n.
admit.
Defined.

Theorem xor_shru:
  forall x y n,
  xor (shru x n) (shru y n) = shru (xor x y) n.
admit.
Defined.

Theorem shru_shru:
  forall x y z,
  ltu y iwordsize = true ->
  ltu z iwordsize = true ->
  ltu (add y z) iwordsize = true ->
  shru (shru x y) z = shru x (add y z).
admit.
Defined.

Theorem shr_zero: forall x, shr x zero = x.
admit.
Defined.

Lemma bitwise_binop_shr:
  forall f f' x y n,
  (forall x y i, 0 <= i < zwordsize -> testbit (f x y) i = f' (testbit x i) (testbit y i)) ->
  f (shr x n) (shr y n) = shr (f x y) n.
admit.
Defined.

Theorem and_shr:
  forall x y n,
  and (shr x n) (shr y n) = shr (and x y) n.
admit.
Defined.

Theorem or_shr:
  forall x y n,
  or (shr x n) (shr y n) = shr (or x y) n.
admit.
Defined.

Theorem xor_shr:
  forall x y n,
  xor (shr x n) (shr y n) = shr (xor x y) n.
admit.
Defined.

Theorem shr_shr:
  forall x y z,
  ltu y iwordsize = true ->
  ltu z iwordsize = true ->
  ltu (add y z) iwordsize = true ->
  shr (shr x y) z = shr x (add y z).
admit.
Defined.

Theorem and_shr_shru:
  forall x y z,
  and (shr x z) (shru y z) = shru (and x y) z.
admit.
Defined.

Theorem shr_and_shru_and:
  forall x y z,
  shru (shl z y) y = z ->
  and (shr x y) z = and (shru x y) z.
admit.
Defined.

Theorem shru_lt_zero:
  forall x,
  shru x (repr (zwordsize - 1)) = if lt x zero then one else zero.
admit.
Defined.

Theorem shr_lt_zero:
  forall x,
  shr x (repr (zwordsize - 1)) = if lt x zero then mone else zero.
admit.
Defined.

 

Lemma bits_rol:
  forall x y i,
  0 <= i < zwordsize ->
  testbit (rol x y) i = testbit x ((i - unsigned y) mod zwordsize).
admit.
Defined.

Lemma bits_ror:
  forall x y i,
  0 <= i < zwordsize ->
  testbit (ror x y) i = testbit x ((i + unsigned y) mod zwordsize).
admit.
Defined.

Hint Rewrite bits_rol bits_ror: ints.

Theorem shl_rolm:
  forall x n,
  ltu n iwordsize = true ->
  shl x n = rolm x n (shl mone n).
admit.
Defined.

Theorem shru_rolm:
  forall x n,
  ltu n iwordsize = true ->
  shru x n = rolm x (sub iwordsize n) (shru mone n).
admit.
Defined.

Theorem rol_zero:
  forall x,
  rol x zero = x.
admit.
Defined.

Lemma bitwise_binop_rol:
  forall f f' x y n,
  (forall x y i, 0 <= i < zwordsize -> testbit (f x y) i = f' (testbit x i) (testbit y i)) ->
  rol (f x y) n = f (rol x n) (rol y n).
admit.
Defined.

Theorem rol_and:
  forall x y n,
  rol (and x y) n = and (rol x n) (rol y n).
admit.
Defined.

Theorem rol_or:
  forall x y n,
  rol (or x y) n = or (rol x n) (rol y n).
admit.
Defined.

Theorem rol_xor:
  forall x y n,
  rol (xor x y) n = xor (rol x n) (rol y n).
admit.
Defined.

Theorem rol_rol:
  forall x n m,
  Z.divide zwordsize modulus ->
  rol (rol x n) m = rol x (modu (add n m) iwordsize).
admit.
Defined.

Theorem rolm_zero:
  forall x m,
  rolm x zero m = and x m.
admit.
Defined.

Theorem rolm_rolm:
  forall x n1 m1 n2 m2,
  Z.divide zwordsize modulus ->
  rolm (rolm x n1 m1) n2 m2 =
    rolm x (modu (add n1 n2) iwordsize)
           (and (rol m1 n2) m2).
admit.
Defined.

Theorem or_rolm:
  forall x n m1 m2,
  or (rolm x n m1) (rolm x n m2) = rolm x n (or m1 m2).
admit.
Defined.

Theorem ror_rol:
  forall x y,
  ltu y iwordsize = true ->
  ror x y = rol x (sub iwordsize y).
admit.
Defined.

Theorem ror_rol_neg:
  forall x y, (zwordsize | modulus) -> ror x y = rol x (neg y).
admit.
Defined.

Theorem or_ror:
  forall x y z,
  ltu y iwordsize = true ->
  ltu z iwordsize = true ->
  add y z = iwordsize ->
  ror x z = or (shl x y) (shru x z).
admit.
Defined.

 

Remark is_power2_inv:
  forall n logn,
  is_power2 n = Some logn ->
  Z_is_power2 (unsigned n) = Some (unsigned logn) /\ 0 <= unsigned logn < zwordsize.
admit.
Defined.

Lemma is_power2_rng:
  forall n logn,
  is_power2 n = Some logn ->
  0 <= unsigned logn < zwordsize.
admit.
Defined.

Theorem is_power2_range:
  forall n logn,
  is_power2 n = Some logn -> ltu logn iwordsize = true.
admit.
Defined.

Lemma is_power2_correct:
  forall n logn,
  is_power2 n = Some logn ->
  unsigned n = two_p (unsigned logn).
admit.
Defined.

Remark two_p_range:
  forall n,
  0 <= n < zwordsize ->
  0 <= two_p n <= max_unsigned.
admit.
Defined.

Lemma is_power2_two_p:
  forall n, 0 <= n < zwordsize ->
  is_power2 (repr (two_p n)) = Some (repr n).
admit.
Defined.

 

 

Lemma shl_mul_two_p:
  forall x y,
  shl x y = mul x (repr (two_p (unsigned y))).
admit.
Defined.

Theorem shl_mul:
  forall x y,
  shl x y = mul x (shl one y).
admit.
Defined.

Theorem mul_pow2:
  forall x n logn,
  is_power2 n = Some logn ->
  mul x n = shl x logn.
admit.
Defined.

Theorem shifted_or_is_add:
  forall x y n,
  0 <= n < zwordsize ->
  unsigned y < two_p n ->
  or (shl x (repr n)) y = repr(unsigned x * two_p n + unsigned y).
admit.
Defined.

 

Lemma shru_div_two_p:
  forall x y,
  shru x y = repr (unsigned x / two_p (unsigned y)).
admit.
Defined.

Theorem divu_pow2:
  forall x n logn,
  is_power2 n = Some logn ->
  divu x n = shru x logn.
admit.
Defined.

 

Lemma shr_div_two_p:
  forall x y,
  shr x y = repr (signed x / two_p (unsigned y)).
admit.
Defined.

Theorem divs_pow2:
  forall x n logn,
  is_power2 n = Some logn ->
  divs x n = shrx x logn.
admit.
Defined.

 

Theorem modu_and:
  forall x n logn,
  is_power2 n = Some logn ->
  modu x n = and x (sub n one).
admit.
Defined.

 

Theorem shrx_zero:
  forall x, zwordsize > 1 -> shrx x zero = x.
admit.
Defined.

Theorem shrx_shr:
  forall x y,
  ltu y (repr (zwordsize - 1)) = true ->
  shrx x y = shr (if lt x zero then add x (sub (shl one y) one) else x) y.
admit.
Defined.

Theorem shrx_shr_2:
  forall x y,
  ltu y (repr (zwordsize - 1)) = true ->
  shrx x y = shr (add x (shru (shr x (repr (zwordsize - 1))) (sub iwordsize y))) y.
admit.
Defined.

Theorem shrx_carry:
  forall x y,
  ltu y (repr (zwordsize - 1)) = true ->
  shrx x y = add (shr x y) (shr_carry x y).
admit.
Defined.

 

Lemma shr_shru_positive:
  forall x y,
  signed x >= 0 ->
  shr x y = shru x y.
admit.
Defined.

Lemma and_positive:
  forall x y, signed y >= 0 -> signed (and x y) >= 0.
admit.
Defined.

Theorem shr_and_is_shru_and:
  forall x y z,
  lt y zero = false -> shr (and x y) z = shru (and x y) z.
admit.
Defined.

 

Lemma bits_zero_ext:
  forall n x i, 0 <= i ->
  testbit (zero_ext n x) i = if zlt i n then testbit x i else false.
admit.
Defined.

Lemma bits_sign_ext:
  forall n x i, 0 <= i < zwordsize ->
  testbit (sign_ext n x) i = testbit x (if zlt i n then i else n - 1).
admit.
Defined.

Hint Rewrite bits_zero_ext bits_sign_ext: ints.

Theorem zero_ext_above:
  forall n x, n >= zwordsize -> zero_ext n x = x.
admit.
Defined.

Theorem zero_ext_below:
  forall n x, n <= 0 -> zero_ext n x = zero.
admit.
Defined.

Theorem sign_ext_above:
  forall n x, n >= zwordsize -> sign_ext n x = x.
admit.
Defined.

Theorem sign_ext_below:
  forall n x, n <= 0 -> sign_ext n x = zero.
admit.
Defined.

Theorem zero_ext_and:
  forall n x, 0 <= n -> zero_ext n x = and x (repr (two_p n - 1)).
admit.
Defined.

Theorem zero_ext_mod:
  forall n x, 0 <= n < zwordsize ->
  unsigned (zero_ext n x) = Z.modulo (unsigned x) (two_p n).
admit.
Defined.

Theorem zero_ext_widen:
  forall x n n', 0 <= n <= n' ->
  zero_ext n' (zero_ext n x) = zero_ext n x.
admit.
Defined.

Theorem sign_ext_widen:
  forall x n n', 0 < n <= n' ->
  sign_ext n' (sign_ext n x) = sign_ext n x.
admit.
Defined.

Theorem sign_zero_ext_widen:
  forall x n n', 0 <= n < n' ->
  sign_ext n' (zero_ext n x) = zero_ext n x.
admit.
Defined.

Theorem zero_ext_narrow:
  forall x n n', 0 <= n <= n' ->
  zero_ext n (zero_ext n' x) = zero_ext n x.
admit.
Defined.

Theorem sign_ext_narrow:
  forall x n n', 0 < n <= n' ->
  sign_ext n (sign_ext n' x) = sign_ext n x.
admit.
Defined.

Theorem zero_sign_ext_narrow:
  forall x n n', 0 < n <= n' ->
  zero_ext n (sign_ext n' x) = zero_ext n x.
admit.
Defined.

Theorem zero_ext_idem:
  forall n x, 0 <= n -> zero_ext n (zero_ext n x) = zero_ext n x.
admit.
Defined.

Theorem sign_ext_idem:
  forall n x, 0 < n -> sign_ext n (sign_ext n x) = sign_ext n x.
admit.
Defined.

Theorem sign_ext_zero_ext:
  forall n x, 0 < n -> sign_ext n (zero_ext n x) = sign_ext n x.
admit.
Defined.

Theorem zero_ext_sign_ext:
  forall n x, 0 < n -> zero_ext n (sign_ext n x) = zero_ext n x.
admit.
Defined.

Theorem sign_ext_equal_if_zero_equal:
  forall n x y, 0 < n ->
  zero_ext n x = zero_ext n y ->
  sign_ext n x = sign_ext n y.
admit.
Defined.

Theorem shru_shl:
  forall x y z, ltu y iwordsize = true -> ltu z iwordsize = true ->
  shru (shl x y) z =
  if ltu z y then shl (zero_ext (zwordsize - unsigned y) x) (sub y z)
             else zero_ext (zwordsize - unsigned z) (shru x (sub z y)).
admit.
Defined.

Corollary zero_ext_shru_shl:
  forall n x,
  0 < n < zwordsize ->
  let y := repr (zwordsize - n) in
  zero_ext n x = shru (shl x y) y.
admit.
Defined.

Theorem shr_shl:
  forall x y z, ltu y iwordsize = true -> ltu z iwordsize = true ->
  shr (shl x y) z =
  if ltu z y then shl (sign_ext (zwordsize - unsigned y) x) (sub y z)
             else sign_ext (zwordsize - unsigned z) (shr x (sub z y)).
admit.
Defined.

Corollary sign_ext_shr_shl:
  forall n x,
  0 < n < zwordsize ->
  let y := repr (zwordsize - n) in
  sign_ext n x = shr (shl x y) y.
admit.
Defined.

 

Lemma zero_ext_range:
  forall n x, 0 <= n < zwordsize -> 0 <= unsigned (zero_ext n x) < two_p n.
admit.
Defined.

Lemma eqmod_zero_ext:
  forall n x, 0 <= n < zwordsize -> eqmod (two_p n) (unsigned (zero_ext n x)) (unsigned x).
admit.
Defined.

 

Lemma sign_ext_range:
  forall n x, 0 < n < zwordsize -> -two_p (n-1) <= signed (sign_ext n x) < two_p (n-1).
admit.
Defined.

Lemma eqmod_sign_ext':
  forall n x, 0 < n < zwordsize ->
  eqmod (two_p n) (unsigned (sign_ext n x)) (unsigned x).
admit.
Defined.

Lemma eqmod_sign_ext:
  forall n x, 0 < n < zwordsize ->
  eqmod (two_p n) (signed (sign_ext n x)) (unsigned x).
admit.
Defined.

 

Lemma shl_zero_ext:
  forall n m x, 0 <= n ->
  shl (zero_ext n x) m = zero_ext (n + unsigned m) (shl x m).
admit.
Defined.

Lemma shl_sign_ext:
  forall n m x, 0 < n ->
  shl (sign_ext n x) m = sign_ext (n + unsigned m) (shl x m).
admit.
Defined.

Lemma shru_zero_ext:
  forall n m x, 0 <= n ->
  shru (zero_ext (n + unsigned m) x) m = zero_ext n (shru x m).
admit.
Defined.

Lemma shru_zero_ext_0:
  forall n m x, n <= unsigned m ->
  shru (zero_ext n x) m = zero.
admit.
Defined.

Lemma shr_sign_ext:
  forall n m x, 0 < n -> n + unsigned m < zwordsize ->
  shr (sign_ext (n + unsigned m) x) m = sign_ext n (shr x m).
admit.
Defined.

Lemma zero_ext_shru_min:
  forall s x n, ltu n iwordsize = true ->
  zero_ext s (shru x n) = zero_ext (Z.min s (zwordsize - unsigned n)) (shru x n).
admit.
Defined.

Lemma sign_ext_shr_min:
  forall s x n, ltu n iwordsize = true ->
  sign_ext s (shr x n) = sign_ext (Z.min s (zwordsize - unsigned n)) (shr x n).
admit.
Defined.

Lemma shl_zero_ext_min:
  forall s x n, ltu n iwordsize = true ->
  shl (zero_ext s x) n = shl (zero_ext (Z.min s (zwordsize - unsigned n)) x) n.
admit.
Defined.

Lemma shl_sign_ext_min:
  forall s x n, ltu n iwordsize = true ->
  shl (sign_ext s x) n = shl (sign_ext (Z.min s (zwordsize - unsigned n)) x) n.
admit.
Defined.

 

Theorem one_bits_range:
  forall x i, In i (one_bits x) -> ltu i iwordsize = true.
admit.
Defined.

Fixpoint int_of_one_bits (l: list int) : int :=
  match l with
  | nil => zero
  | a :: b => add (shl one a) (int_of_one_bits b)
  end.

Theorem one_bits_decomp:
  forall x, x = int_of_one_bits (one_bits x).
admit.
Defined.

 

Theorem negate_cmp:
  forall c x y, cmp (negate_comparison c) x y = negb (cmp c x y).
admit.
Defined.

Theorem negate_cmpu:
  forall c x y, cmpu (negate_comparison c) x y = negb (cmpu c x y).
admit.
Defined.

Theorem swap_cmp:
  forall c x y, cmp (swap_comparison c) x y = cmp c y x.
admit.
Defined.

Theorem swap_cmpu:
  forall c x y, cmpu (swap_comparison c) x y = cmpu c y x.
admit.
Defined.

Lemma translate_eq:
  forall x y d,
  eq (add x d) (add y d) = eq x y.
admit.
Defined.

Lemma translate_ltu:
  forall x y d,
  0 <= unsigned x + unsigned d <= max_unsigned ->
  0 <= unsigned y + unsigned d <= max_unsigned ->
  ltu (add x d) (add y d) = ltu x y.
admit.
Defined.

Theorem translate_cmpu:
  forall c x y d,
  0 <= unsigned x + unsigned d <= max_unsigned ->
  0 <= unsigned y + unsigned d <= max_unsigned ->
  cmpu c (add x d) (add y d) = cmpu c x y.
admit.
Defined.

Lemma translate_lt:
  forall x y d,
  min_signed <= signed x + signed d <= max_signed ->
  min_signed <= signed y + signed d <= max_signed ->
  lt (add x d) (add y d) = lt x y.
admit.
Defined.

Theorem translate_cmp:
  forall c x y d,
  min_signed <= signed x + signed d <= max_signed ->
  min_signed <= signed y + signed d <= max_signed ->
  cmp c (add x d) (add y d) = cmp c x y.
admit.
Defined.

Theorem notbool_isfalse_istrue:
  forall x, is_false x -> is_true (notbool x).
admit.
Defined.

Theorem notbool_istrue_isfalse:
  forall x, is_true x -> is_false (notbool x).
admit.
Defined.

Theorem ltu_range_test:
  forall x y,
  ltu x y = true -> unsigned y <= max_signed ->
  0 <= signed x < unsigned y.
admit.
Defined.

Theorem lt_sub_overflow:
  forall x y,
  xor (sub_overflow x y zero) (negative (sub x y)) = if lt x y then one else zero.
admit.
Defined.

End Make.

 

Module Export Wordsize_32.
  Definition wordsize := 32%nat.
  Remark wordsize_not_zero: wordsize <> 0%nat.
admit.
Defined.
End Wordsize_32.

Module Int := Make(Wordsize_32).

Notation int := Int.int.

Module Export Wordsize_8.
  Definition wordsize := 8%nat.
  Remark wordsize_not_zero: wordsize <> 0%nat.
admit.
Defined.
End Wordsize_8.

Module Byte := Make(Wordsize_8).

Notation byte := Byte.int.

Module Export Wordsize_64.
  Definition wordsize := 64%nat.
  Remark wordsize_not_zero: wordsize <> 0%nat.
admit.
Defined.
End Wordsize_64.

Module Int64.

Include Make(Wordsize_64).

End Int64.

Notation int64 := Int64.int.

 

Module Export Wordsize_Ptrofs.
  Definition wordsize := if Archi.ptr64 then 64%nat else 32%nat.
  Remark wordsize_not_zero: wordsize <> 0%nat.
admit.
Defined.
End Wordsize_Ptrofs.

Module Ptrofs.

Include Make(Wordsize_Ptrofs).

Section AGREE32.

End AGREE32.

Section AGREE64.

End AGREE64.

End Ptrofs.

Notation ptrofs := Ptrofs.int.

End Integers.
Module Export Floats.
Import compcert.lib.Coqlib.
Import Flocq.IEEE754.Binary.
Import Flocq.IEEE754.Bits.

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

Module Export Float.

Definition zero: float := B754_zero _ _ false.

Definition compare (f1 f2: float) : option Datatypes.comparison :=
  Bcompare 53 1024 f1 f2.
Definition cmp (c:comparison) (f1 f2: float) : bool :=
  cmp_of_comparison c (compare f1 f2).
Definition of_bits (b: int64): float := b64_of_bits (Int64.unsigned b).

End Float.

Module Export Float32.

Definition zero: float32 := B754_zero _ _ false.

Definition compare (f1 f2: float32) : option Datatypes.comparison :=
  Bcompare 24 128 f1 f2.
Definition cmp (c:comparison) (f1 f2: float32) : bool :=
  cmp_of_comparison c (compare f1 f2).
Definition of_bits (b: int): float32 := b32_of_bits (Int.unsigned b).

End Float32.

End Floats.
Module Export AST.
Import compcert.lib.Coqlib.

Definition ident := positive.

Definition ident_eq := peq.

Inductive typ : Type :=
  | Tint
  | Tfloat
  | Tlong
  | Tsingle
  | Tany32
  | Tany64.

Definition Tptr : typ := if Archi.ptr64 then Tlong else Tint.

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

End AST.
Module Export Values.

Import compcert.lib.Coqlib.

Definition block : Type := positive.

Inductive val: Type :=
  | Vundef: val
  | Vint: int -> val
  | Vlong: int64 -> val
  | Vfloat: float -> val
  | Vsingle: float32 -> val
  | Vptr: block -> ptrofs -> val.

Definition Vtrue: val := Vint Int.one.
Definition Vfalse: val := Vint Int.zero.

Module Val.

Definition eq (x y: val): {x=y} + {x<>y}.
admit.
Defined.

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

Definition of_bool (b: bool): val := if b then Vtrue else Vfalse.

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

End Val.

End Values.
Module Export Memdata.

Import compcert.lib.Coqlib.

Definition size_chunk (chunk: memory_chunk) : Z :=
  match chunk with
  | Mint8signed => 1
  | Mint8unsigned => 1
  | Mint16signed => 2
  | Mint16unsigned => 2
  | Mint32 => 4
  | Mint64 => 8
  | Mfloat32 => 4
  | Mfloat64 => 8
  | Many32 => 4
  | Many64 => 8
  end.

Definition size_chunk_nat (chunk: memory_chunk) : nat :=
  Z.to_nat(size_chunk chunk).

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

Inductive quantity : Type := Q32 | Q64.

Definition quantity_eq (q1 q2: quantity) : {q1 = q2} + {q1 <> q2}.
admit.
Defined.

Definition size_quantity_nat (q: quantity) :=
  match q with Q32 => 4%nat | Q64 => 8%nat end.

Inductive memval: Type :=
  | Undef: memval
  | Byte: byte -> memval
  | Fragment: val -> quantity -> nat -> memval.

Fixpoint int_of_bytes (l: list byte): Z :=
  match l with
  | nil => 0
  | b :: l' => Byte.unsigned b + int_of_bytes l' * 256
  end.

Definition rev_if_be (l: list byte) : list byte :=
  if Archi.big_endian then List.rev l else l.

Definition decode_int (b: list byte) : Z :=
  int_of_bytes (rev_if_be b).

Fixpoint proj_bytes (vl: list memval) : option (list byte) :=
  match vl with
  | nil => Some nil
  | Byte b :: vl' =>
      match proj_bytes vl' with None => None | Some bl => Some(b :: bl) end
  | _ => None
  end.

Fixpoint check_value (n: nat) (v: val) (q: quantity) (vl: list memval)
                       {struct n} : bool :=
  match n, vl with
  | O, nil => true
  | S m, Fragment v' q' m' :: vl' =>
      Val.eq v v' && quantity_eq q q' && Nat.eqb m m' && check_value m v q vl'
  | _, _ => false
  end.

Definition proj_value (q: quantity) (vl: list memval) : val :=
  match vl with
  | Fragment v q' n :: vl' =>
      if check_value (size_quantity_nat q) v q vl then v else Vundef
  | _ => Vundef
  end.

Definition decode_val (chunk: memory_chunk) (vl: list memval) : val :=
  match proj_bytes vl with
  | Some bl =>
      match chunk with
      | Mint8signed => Vint(Int.sign_ext 8 (Int.repr (decode_int bl)))
      | Mint8unsigned => Vint(Int.zero_ext 8 (Int.repr (decode_int bl)))
      | Mint16signed => Vint(Int.sign_ext 16 (Int.repr (decode_int bl)))
      | Mint16unsigned => Vint(Int.zero_ext 16 (Int.repr (decode_int bl)))
      | Mint32 => Vint(Int.repr(decode_int bl))
      | Mint64 => Vlong(Int64.repr(decode_int bl))
      | Mfloat32 => Vsingle(Float32.of_bits (Int.repr (decode_int bl)))
      | Mfloat64 => Vfloat(Float.of_bits (Int64.repr (decode_int bl)))
      | Many32 => Vundef
      | Many64 => Vundef
      end
  | None =>
      match chunk with
      | Mint32 => if Archi.ptr64 then Vundef else Val.load_result chunk (proj_value Q32 vl)
      | Many32 => Val.load_result chunk (proj_value Q32 vl)
      | Mint64 => if Archi.ptr64 then Val.load_result chunk (proj_value Q64 vl) else Vundef
      | Many64 => Val.load_result chunk (proj_value Q64 vl)
      | _ => Vundef
      end
  end.

End Memdata.
Module VST_DOT_veric_DOT_base_WRAPPED.
Module Export base.
Export compcert.lib.Coqlib.
Export compcert.lib.Maps.

Fixpoint id_in_list (id: ident) (ids: list ident) : bool :=
 match ids with i::ids' => orb (Pos.eqb id i) (id_in_list id ids') | _ => false end.

Fixpoint compute_list_norepet (ids: list ident) : bool :=
 match ids with
 | id :: ids' => if id_in_list id ids' then false else compute_list_norepet ids'
 | nil => true
 end.

Lemma Vint_inj: forall x y, Vint x = Vint y -> x=y.
admit.
Defined.

Definition nullval : val :=
  if Archi.ptr64 then Vlong Int64.zero else Vint Int.zero.
End base.

End VST_DOT_veric_DOT_base_WRAPPED.
Module Export VST.
Module Export veric.
Module base.
Include VST_DOT_veric_DOT_base_WRAPPED.base.
End base.
Module Export Ctypes.
Import compcert.lib.Coqlib.
Import compcert.lib.Maps.
Import compcert.common.Errors.

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

Definition type_is_volatile (ty: type) : bool :=
  match access_mode ty with
  | By_value _ => attr_volatile (attr_of_type ty)
  | _          => false
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

Definition typ_of_type (t: type) : AST.typ :=
  match t with
  | Tvoid => AST.Tint
  | Tint _ _ _ => AST.Tint
  | Tlong _ _ => AST.Tlong
  | Tfloat F32 _ => AST.Tsingle
  | Tfloat F64 _ => AST.Tfloat
  | Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ _ | Tstruct _ _ | Tunion _ _ => AST.Tptr
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

End Ctypes.
Import VST.msl.msl_standard.

Definition nonempty_share (sh: share) :=
       sepalg.nonidentity sh.
Definition readable_share (sh: share) :=
       nonempty_share (Share.glb Share.Rsh sh).

Lemma readable_share_dec:
  forall sh, {readable_share sh}+{~ readable_share sh}.
admit.
Defined.
Module Export rmaps.
Import VST.msl.ghost.

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

  Inductive res_join (PRED : Type) : f_res PRED -> f_res PRED -> f_res PRED -> Prop :=
    | res_join_NO1 : forall sh1 nsh1 sh2 nsh2 sh3 nsh3,
                               join sh1 sh2 sh3 ->
                               res_join PRED (NO' PRED sh1 nsh1) (NO' PRED sh2 nsh2)
                                     (NO' PRED sh3 nsh3)
    | res_join_NO2 : forall sh1 nsh1 sh2 rsh2 sh3 rsh3 k p,
                               join sh1 sh2 sh3 ->
                               res_join PRED (NO' PRED sh1 nsh1) (YES' PRED sh2 rsh2 k p)
                                   (YES' PRED sh3 rsh3 k p)
    | res_join_NO3 : forall sh1 rsh1 sh2 nsh2 sh3 rsh3 k p,
                               join sh1 sh2 sh3 ->
                               res_join PRED (YES' PRED sh1 rsh1 k p) (NO' PRED sh2 nsh2)
                                   (YES' PRED sh3 rsh3 k p)
    | res_join_YES : forall sh1 rsh1 sh2 rsh2 sh3 rsh3 k p,
                              join sh1 sh2 sh3 ->
              res_join PRED (YES' PRED sh1 rsh1 k p) (YES' PRED sh2 rsh2 k p) (YES' PRED sh3 rsh3 k p)
    | res_join_PURE : forall k p, res_join PRED (PURE' PRED k p) (PURE' PRED k p) (PURE' PRED k p).

  Definition ghost (PRED : Type) : Type :=
    list (option ({g: Ghost & {a: @G g | ghost.valid a}} * fpreds PRED)%type).

  Definition ghost_fmap (A B:Type) (f:A->B) (g:B->A)(x:ghost A) : ghost B :=
    fmap (flist (foption (fpair (fconst _) fpreds))) f g x.

  Axiom ff_ghost : functorFacts ghost ghost_fmap.
  Definition f_ghost : functor := Functor ff_ghost.

  Instance preds_join PRED : Join _ := Join_equiv (fpreds PRED).

  Inductive ghost_elem_join : Join {g: Ghost & {a: @G g | ghost.valid a}} :=
  | elem_join_I g a b c va vb vc: join a b c ->
    ghost_elem_join (existT _ g (exist _ a va)) (existT _ g (exist _ b vb))
                    (existT _ g (exist _ c vc)).
  Existing Instance ghost_elem_join.

  Inductive ghost_join PRED : Join (ghost PRED) :=
  | ghost_join_nil_l m: ghost_join PRED nil m m
  | ghost_join_nil_r m: ghost_join PRED m nil m
  | ghost_join_cons a1 a2 m1 m2 a3 m3: join a1 a2 a3 -> ghost_join PRED m1 m2 m3 ->
      ghost_join PRED (a1 :: m1) (a2 :: m2) (a3 :: m3).

  Definition f_pre_rmap : functor :=
    fpair (ffunc (fconst address) f_res) f_ghost.

  Instance Join_pre_rmap (A: Type) : Join (f_pre_rmap A) :=
            Join_prod _ (Join_fun address (res A) (res_join A)) _ (ghost_join A).

  Declare Instance Perm_pre_rmap: forall (A: Type), Perm_alg (f_pre_rmap A).
  Declare Instance Sep_pre_rmap: forall (A: Type), Sep_alg (f_pre_rmap A).
  Parameter paf_pre_rmap : @pafunctor f_pre_rmap Join_pre_rmap.

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

  Inductive res_join (PRED : Type) : f_res PRED -> f_res PRED -> f_res PRED -> Prop :=
    | res_join_NO1 : forall sh1 nsh1 sh2 nsh2 sh3 nsh3,
                               join sh1 sh2 sh3 ->
                               res_join PRED (NO' PRED sh1 nsh1) (NO' PRED sh2 nsh2)
                                     (NO' PRED sh3 nsh3)
    | res_join_NO2 : forall sh1 nsh1 sh2 rsh2 sh3 rsh3 k p,
                               join sh1 sh2 sh3 ->
                               res_join PRED (NO' PRED sh1 nsh1) (YES' PRED sh2 rsh2 k p)
                                   (YES' PRED sh3 rsh3 k p)
    | res_join_NO3 : forall sh1 rsh1 sh2 nsh2 sh3 rsh3 k p,
                               join sh1 sh2 sh3 ->
                               res_join PRED (YES' PRED sh1 rsh1 k p) (NO' PRED sh2 nsh2)
                                   (YES' PRED sh3 rsh3 k p)
    | res_join_YES : forall sh1 rsh1 sh2 rsh2 sh3 rsh3 k p,
                              join sh1 sh2 sh3 ->
              res_join PRED (YES' PRED sh1 rsh1 k p) (YES' PRED sh2 rsh2 k p) (YES' PRED sh3 rsh3 k p)
    | res_join_PURE : forall k p, res_join PRED (PURE' PRED k p) (PURE' PRED k p) (PURE' PRED k p).

  Instance pa_rj : forall PRED, @Perm_alg _ (res_join PRED).
admit.
Defined.

  Instance sa_rj : forall PRED, @Sep_alg _ (res_join PRED).
admit.
Defined.

  Definition paf_res : @pafunctor f_res res_join.
admit.
Defined.

  Definition ghost (PRED : Type) : Type :=
    list (option ({g: Ghost & {a: @G g | ghost.valid a}} * fpreds PRED)%type).

  Definition ghost_fmap (A B:Type) (f:A->B) (g:B->A)(x:ghost A) : ghost B :=
    fmap (flist (foption (fpair (fconst _) fpreds))) f g x.

  Lemma ff_ghost : functorFacts ghost ghost_fmap.
admit.
Defined.

  Definition f_ghost : functor := Functor ff_ghost.

  Instance preds_join PRED : Join _ := Join_equiv (fpreds PRED).

  Inductive ghost_elem_join : Join {g: Ghost & {a: @G g | ghost.valid a}} :=
  | elem_join_I g a b c va vb vc: join a b c ->
    ghost_elem_join (existT _ g (exist _ a va)) (existT _ g (exist _ b vb))
                    (existT _ g (exist _ c vc)).
  Existing Instance ghost_elem_join.

  Inductive ghost_join PRED : Join (ghost PRED) :=
  | ghost_join_nil_l m: ghost_join PRED nil m m
  | ghost_join_nil_r m: ghost_join PRED m nil m
  | ghost_join_cons a1 a2 m1 m2 a3 m3: join a1 a2 a3 -> ghost_join PRED m1 m2 m3 ->
      ghost_join PRED (a1 :: m1) (a2 :: m2) (a3 :: m3).

  Instance pa_gj : forall PRED, @Perm_alg _ (ghost_join PRED).
admit.
Defined.

  Instance sa_gj : forall PRED, @Sep_alg _ (ghost_join PRED).
admit.
Defined.

  Definition paf_ghost : @pafunctor f_ghost ghost_join.
admit.
Defined.

  Definition pre_rmap (A:Type) := ((address -> res A) * ghost A)%type.
  Definition f_pre_rmap : functor :=
    fpair (ffunc (fconst address) f_res) f_ghost.

  Notation Join_obj A := (Join_prod _ (Join_fun address (res A) (res_join A)) _ (ghost_join A)).

  Instance Join_pre_rmap (A: Type) : Join (pre_rmap A) :=
    Join_obj A.

  Definition paf_pre_rmap : @pafunctor f_pre_rmap Join_pre_rmap :=
    paf_pair (paf_fun address paf_res) paf_ghost.

  Definition Perm_pre_rmap (A: Type): Perm_alg (pre_rmap A) :=
    Perm_prod (Perm_fun address _ _ _) (pa_gj A).

  Definition Sep_pre_rmap (A: Type): Sep_alg (pre_rmap A) :=
    Sep_prod (Sep_fun address _ _ _) (sa_gj A).

End StratModel.

Module Type RMAPS.
  Declare Module AV:ADR_VAL.
  Import AV.

  Parameter rmap : Type.
  Axiom Join_rmap: Join rmap.
Existing Instance Join_rmap.
  Axiom Perm_rmap: Perm_alg rmap.
Existing Instance Perm_rmap.
  Axiom Sep_rmap: Sep_alg rmap.
Existing Instance Sep_rmap.
  Axiom ag_rmap: ageable rmap.
 Existing Instance ag_rmap.
  Axiom Age_rmap: Age_alg rmap.
 Existing Instance Age_rmap.

  Inductive preds : Type :=
    SomeP : forall A : TypeTree,
      (forall ts: list Type, dependent_type_functor_rec ts A (pred rmap)) -> preds.

  Definition NoneP := SomeP (ConstType unit) (fun _ => tt).

  Inductive resource : Type :=
    | NO: forall sh: Share.t, ~(readable_share sh) -> resource
    | YES: forall sh: Share.t, readable_share sh -> kind -> preds -> resource
    | PURE: kind -> preds -> resource.

  Inductive res_join : resource -> resource -> resource -> Prop :=
   | res_join_NO1 : forall sh1 nsh1 sh2 nsh2 sh3 nsh3
                 (RJ: join sh1 sh2 sh3),
                 res_join (NO sh1 nsh1) (NO sh2 nsh2) (NO sh3 nsh3)
   | res_join_NO2 : forall sh1 rsh1 sh2 nsh2 sh3 rsh3 k p
                 (RJ: join sh1 sh2 sh3),
                 res_join (YES sh1 rsh1 k p) (NO sh2 nsh2) (YES sh3 rsh3 k p)
   | res_join_NO3 : forall sh1 nsh1 sh2 rsh2 sh3 rsh3 k p
                 (RJ: join sh1 sh2 sh3),
                 res_join (NO sh1 nsh1) (YES sh2 rsh2 k p) (YES sh3 rsh3 k p)
   | res_join_YES : forall sh1 rsh1 sh2 rsh2 sh3 rsh3 k p
                 (RJ: join sh1 sh2 sh3),
        res_join (YES sh1 rsh1 k p) (YES sh2 rsh2 k p) (YES sh3 rsh3 k p)
   | res_join_PURE : forall k p, res_join (PURE k p) (PURE k p) (PURE k p).

  Instance Join_resource: Join resource := res_join.

  Definition preds_fmap (f g: pred rmap -> pred rmap) (x:preds) : preds :=
    match x with SomeP A Q => SomeP A (fmap (fpi _) f g Q)
    end.

  Definition ghost : Type := list (option ({g: Ghost & {a: @G g | ghost.valid a}} * preds)%type).

  Instance preds_join : Join _ := Join_equiv preds.

  Definition rmap' := ((address -> resource) * ghost)%type.
  Parameter unsquash : rmap -> (nat * rmap').

  Definition resource_at (phi:rmap) : address -> resource := fst (snd (unsquash phi)).
  Infix "@" := resource_at (at level 50, no associativity).
  Definition ghost_of (phi:rmap) : ghost := snd (snd (unsquash phi)).

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

    Instance Join_F: forall A, Join (F A) := _.
    Definition Perm_F : forall A, Perm_alg (F A) := Perm_pre_rmap.
    Definition Sep_F := Sep_pre_rmap.
    Definition paf_F := paf_pre_rmap.
  End TyFSA.

  Module K := Knot_MixVariantHeredProp(TyF).
  Module KL := KnotLemmas_MixVariantHeredProp(K).
  Module KSa := KnotFullSa(TyFSA)(K)(KL).

  Definition rmap := K.knot.
  Instance Join_rmap: Join rmap := KSa.Join_knot.
  Instance Perm_rmap : Perm_alg rmap:= KSa.Perm_knot.
  Instance Sep_rmap : Sep_alg rmap:= KSa.Sep_knot.
  Instance ag_rmap : ageable rmap := K.ageable_knot.
  Instance Age_rmap: Age_alg rmap := KSa.asa_knot.

  Inductive preds : Type :=
    SomeP : forall A : TypeTree,
    (forall ts: list Type, dependent_type_functor_rec ts A (pred rmap)) -> preds.

  Definition NoneP := SomeP (ConstType unit) (fun _ => tt).

  Inductive resource : Type :=
    | NO: forall sh: Share.t, ~ readable_share sh -> resource
    | YES: forall sh: Share.t, readable_share sh -> kind -> preds -> resource
    | PURE: kind -> preds -> resource.

  Definition res2resource (r: res (pred rmap)) : resource :=
    match r with
      | NO' sh nsh => NO sh nsh
      | YES' sh rsh k (existT A l) => YES sh rsh k (SomeP A l)
      | PURE' k (existT A l) => PURE k (SomeP A l)
    end.

  Definition ghost : Type := list (option ({g: Ghost & {a: @G g | ghost.valid a}} * preds)%type).

  Definition p2pred (p: fpreds (pred rmap)) : preds :=
    match p with existT A P => SomeP A P end.

  Definition g2ghost (r: SM.ghost (pred rmap)) : ghost :=
    map (option_map (fun '(a, b) => (a, p2pred b))) r.

  Inductive res_join : resource -> resource -> resource -> Prop :=
   | res_join_NO1 : forall sh1 nsh1 sh2 nsh2 sh3 nsh3
                 (RJ: join sh1 sh2 sh3),
                 res_join (NO sh1 nsh1) (NO sh2 nsh2) (NO sh3 nsh3)
   | res_join_NO2 : forall sh1 rsh1 sh2 nsh2 sh3 rsh3 k p
                 (RJ: join sh1 sh2 sh3),
                 res_join (YES sh1 rsh1 k p) (NO sh2 nsh2) (YES sh3 rsh3 k p)
   | res_join_NO3 : forall sh1 nsh1 sh2 rsh2 sh3 rsh3 k p
                 (RJ: join sh1 sh2 sh3),
                 res_join (NO sh1 nsh1) (YES sh2 rsh2 k p) (YES sh3 rsh3 k p)
   | res_join_YES : forall sh1 rsh1 sh2 rsh2 sh3 rsh3 k p
                 (RJ: join sh1 sh2 sh3),
        res_join (YES sh1 rsh1 k p) (YES sh2 rsh2 k p) (YES sh3 rsh3 k p)
   | res_join_PURE : forall k p, res_join (PURE k p) (PURE k p) (PURE k p).

  Instance Join_resource: Join resource := res_join.

  Instance preds_join : Join _ := Join_equiv preds.

  Inductive ghost_join : Join ghost :=
  | ghost_join_nil_l m: ghost_join nil m m
  | ghost_join_nil_r m: ghost_join m nil m
  | ghost_join_cons a1 a2 m1 m2 a3 m3: join a1 a2 a3 -> ghost_join m1 m2 m3 ->
      ghost_join (a1 :: m1) (a2 :: m2) (a3 :: m3).

  Definition rmap' := ((address->resource) * ghost)%type.
  Definition preds_fmap (f g:(pred rmap)->(pred rmap)) (x:preds) : preds :=
    match x with SomeP A ls => SomeP A (fmap (fpi _) f g ls) end.

  Definition pre_rmap2rmap' (f: f_pre_rmap (pred rmap)) : rmap' :=
      (fun l : address => res2resource (fst f l), g2ghost (snd f)).

  Definition unsquash (phi:rmap) : (nat * rmap') :=
    match K.unsquash phi with (n,rm) => (n, pre_rmap2rmap' rm) end.
  Definition resource_at (phi:rmap) : address -> resource := fst (snd (unsquash phi)).
  Definition ghost_of (phi:rmap) : ghost := snd (snd (unsquash phi)).

  Program Definition approx (n:nat) (p: (pred rmap)) : (pred rmap) :=
    fun w => level w < n /\ p w.
Admit Obligations.

End Rmaps.
Import compcert.lib.Coqlib.

Definition address : Type := (block * Z)%type.

Definition adr_range (base: address) (size: Z) (loc: address) : Prop :=
 match base, loc with
 | (b, ofs) , (b', ofs') => b=b' /\ (ofs <= ofs' < ofs + size)
 end.

Lemma adr_range_dec: forall base n loc, {adr_range base n loc} + {~adr_range base n loc}.
admit.
Defined.
Import VST.veric.base.

Definition typesig := (list type * type)%type.

Inductive kind : Type := VAL : memval -> kind
                                   | LK : forall n i : Z, kind
                                   | FUN:  typesig -> calling_convention -> kind.

Definition isVAL (k: kind) := match k with | VAL _ => True | _ => False end.
Definition isFUN (k: kind) := match k with | FUN _ _ => True | _ => False end.

Module CompCert_AV <: ADR_VAL.

Definition address := address.
Definition kind := kind.

End CompCert_AV.

Module R := Rmaps (CompCert_AV).
Export R.
Module Export val_lemmas.

Definition is_long (v: val) :=
 match v with Vlong i => True | _ => False end.
Definition is_float (v: val) :=
 match v with Vfloat i => True | _ => False end.
Definition is_single (v: val) :=
 match v with Vsingle i => True | _ => False end.

Definition is_pointer_or_null (v: val) :=
 match v with
 | Vint i => if Archi.ptr64 then False else  i = Int.zero
 | Vlong i => if Archi.ptr64 then i=Int64.zero else False
 | Vptr _ _ => True
 | _ => False
 end.

Definition is_pointer_or_integer (v: val) :=
 match v with
 | Vint i => if Archi.ptr64 then False else True
 | Vlong i => if Archi.ptr64 then True else False
 | Vptr _ _ => True
 | _ => False
 end.

Definition isptr v :=
   match v with | Vptr _ _ => True | _ => False end.
Module Export res_predicates.
Local Open Scope pred.

Definition spec : Type :=  forall (sh: Share.t) (l: AV.address), pred rmap.

Program Definition yesat_raw (pp: preds) (k: kind)
                           (sh: share) (rsh: readable_share sh) (l: address) : pred rmap :=
   fun phi => phi @ l = YES sh rsh k (preds_fmap (approx (level phi)) (approx (level phi)) pp).
Admit Obligations.

Program Definition yesat (pp: preds) (k: kind) : spec :=
 fun (sh: share) (l: AV.address) (m: rmap) =>
  exists rsh, yesat_raw pp k sh rsh l m.

Program Definition pureat (pp: preds) (k: kind) (l: AV.address): pred rmap :=
       fun phi => phi @ l = PURE k (preds_fmap (approx (level phi)) (approx (level phi)) pp).

Program Definition noat (l: AV.address) : pred rmap :=
    fun m => identity (m @ l).

Definition resource_share (r: resource) : option share :=
 match r with
 | YES sh _ _ _ => Some sh
 | NO sh _ => Some sh
 | PURE _ _ => None
 end.

Definition nonlock (r: resource) : Prop :=
 match r with
 | YES _ _ k _ => isVAL k \/ isFUN k
 | NO _ _ => True
 | PURE _ _ => False
 end.

Program Definition nonlockat (l: AV.address): pred rmap :=
  fun m => nonlock (m @ l).

Program Definition shareat (l: AV.address) (sh: share): pred rmap :=
  fun m => resource_share (m @ l) = Some sh.

Program Definition jam {A} {JA: Join A}{PA: Perm_alg A}{agA: ageable A}{AgeA: Age_alg A} {B: Type} {S': B -> Prop} (S: forall l, {S' l}+{~ S' l}) (P Q: B -> pred A) : B -> pred A :=
  fun (l: B) m => if S l then P l m else Q l m.

Program Definition noghost : pred rmap := fun m => identity (ghost_of m).
Admit Obligations.

Definition nonlock_permission_bytes (sh: share) (a: address) (n: Z) : pred rmap :=
  andp (allp (jam (adr_range_dec a n) (fun i => shareat i sh && nonlockat i) noat)) noghost.

Definition address_mapsto (ch: memory_chunk) (v: val) : spec :=
        fun (sh: Share.t) (l: AV.address) =>
           EX bl: list memval,
               !! (length bl = size_chunk_nat ch  /\ decode_val ch bl = v /\ (align_chunk ch | snd l))  &&
                (allp (jam (adr_range_dec l (size_chunk ch))
                                    (fun loc => yesat NoneP (VAL (nth (Z.to_nat (snd loc - snd l)) bl Undef)) sh loc)
                                    noat)) && noghost.

End res_predicates.

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

Definition tc_val (ty: type) : val -> Prop :=
 match ty with
 | Tint sz sg _ => is_int sz sg
 | Tlong _ _ => is_long
 | Tfloat F64 _ => is_float
 | Tfloat F32 _ => is_single
 | Tpointer _ _ => if eqb_type ty int_or_ptr_type then is_pointer_or_integer else is_pointer_or_null
 | Tarray _ _ _ | Tfunction _ _ _ => is_pointer_or_null
 | Tstruct _ _ => isptr
 | Tunion _ _ => isptr
 | _ => fun _ => False
 end.

Definition tc_val' t v := v <> Vundef -> tc_val t v.
Import Coq.Structures.Orders.

Module CompositeRankOrder <: TotalLeBool.
  Definition t := (positive * composite)%type.
  Definition leb (x y: t) := Nat.leb (co_rank (snd y)) (co_rank (snd x)).

  Theorem leb_total : forall a1 a2, leb a1 a2 = true \/ leb a2 a1 = true.
admit.
Defined.

End CompositeRankOrder.

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

Lemma align_compatible_rec_by_value_inv : forall t ch z,
  access_mode t = By_value ch ->
  align_compatible_rec t z -> (Memdata.align_chunk ch | z).
admit.
Defined.

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

Definition strict_bool_val (v: val) (t: type) : option bool :=
   match v, t with
   | Vint n, Tint _ _ _ => Some (negb (Int.eq n Int.zero))
   | Vlong n, Tlong _ _ => Some (negb (Int64.eq n Int64.zero))
   | (Vint n), (Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ _ ) =>
            if Archi.ptr64 then None else if Int.eq n Int.zero then Some false else None
   | Vlong n, (Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ _ ) =>
            if Archi.ptr64 then if Int64.eq n Int64.zero then Some false else None else None
   | Vptr b ofs, (Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ _ ) => Some true
   | Vfloat f, Tfloat F64 _ => Some (negb(Float.cmp Ceq f Float.zero))
   | Vsingle f, Tfloat F32 _ => Some (negb(Float32.cmp Ceq f Float32.zero))
   | _, _ => None
   end.

Definition type_is_by_value (t:type) : bool :=
  match t with
  | Tint _ _ _
  | Tlong _ _
  | Tfloat _ _
  | Tpointer _ _ => true
  | _ => false
  end.
Module Map.
Section map.
Variables (B : Type).

Definition t := positive -> option B.

Definition empty : t := fun _ => None.

End map.

End Map.

Section FUNSPEC.

Definition genviron := Map.t block.

Definition venviron := Map.t (block * type).

Definition tenviron := Map.t val.

Inductive environ : Type :=
 mkEnviron: forall (ge: genviron) (ve: venviron) (te: tenviron), environ.

Definition ve_of (rho: environ) : venviron :=
  match rho with mkEnviron ge ve te => ve end.

Definition mpred := pred rmap.

Definition argsEnviron:Type := genviron * (list val).

Definition AssertTT (A: TypeTree): TypeTree :=
  ArrowType A (ArrowType (ConstType environ) Mpred).

Definition ArgsTT (A: TypeTree): TypeTree :=
  ArrowType A (ArrowType (ConstType argsEnviron) Mpred).

Definition SpecArgsTT (A: TypeTree): TypeTree :=
  ArrowType A
  (PiType bool (fun b => ArrowType (ConstType
                                         (if b
                                          then argsEnviron
                                          else environ))
                                    Mpred)).

Definition super_non_expansive {A: TypeTree}
  (P: forall ts, dependent_type_functor_rec ts (AssertTT A) mpred): Prop :=
  forall n ts
    (x: functors.MixVariantFunctor._functor
                         (rmaps.dependent_type_functor_rec ts A) mpred)
    (rho: environ),
  approx n (P ts x rho) = approx n (P ts (fmap _ (approx n) (approx n) x) rho).

Definition args_super_non_expansive {A: TypeTree}
  (P: forall ts, dependent_type_functor_rec ts (ArgsTT A) mpred): Prop :=
  forall n ts
    (x: functors.MixVariantFunctor._functor
                         (rmaps.dependent_type_functor_rec ts A) mpred)
    (gargs: argsEnviron),
  @eq mpred (approx n (P ts x gargs)) (approx n (P ts (fmap _ (approx n) (approx n) x) gargs)).

Inductive funspec :=
   mk_funspec: typesig -> calling_convention -> forall (A: TypeTree)
     (P: forall ts, dependent_type_functor_rec ts (ArgsTT A) mpred)
     (Q: forall ts, dependent_type_functor_rec ts (AssertTT A) mpred)
     (P_ne: args_super_non_expansive P) (Q_ne: super_non_expansive Q),
     funspec.

End FUNSPEC.

Definition packPQ {A: rmaps.TypeTree}
  (P: forall ts, dependent_type_functor_rec ts (ArgsTT A) mpred)
  (Q: forall ts, dependent_type_functor_rec ts (AssertTT A) mpred):
  forall ts, dependent_type_functor_rec ts (SpecArgsTT A) mpred.
admit.
Defined.

Definition members_no_replicate (m: members) : bool :=
  compute_list_norepet (map fst m).

Lemma size_chunk_sizeof: forall env t ch, access_mode t = By_value ch -> sizeof env t = Memdata.size_chunk ch.
admit.
Defined.

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
Module Export mapsto_memory_block.

Local Open Scope pred.

Definition mapsto (sh: Share.t) (t: type) (v1 v2 : val): mpred :=
  match access_mode t with
  | By_value ch =>
   match type_is_volatile t with
   | false =>
    match v1 with
     | Vptr b ofs =>
       if readable_share_dec sh
       then (!!tc_val t v2 &&
             address_mapsto ch v2 sh (b, Ptrofs.unsigned ofs)) ||
            (!! (v2 = Vundef) &&
             EX v2':val, address_mapsto ch v2' sh (b, Ptrofs.unsigned ofs))
       else !! (tc_val' t v2 /\ (align_chunk ch | Ptrofs.unsigned ofs)) && nonlock_permission_bytes sh (b, Ptrofs.unsigned ofs) (size_chunk ch)
     | _ => FF
    end
    | _ => FF
    end
  | _ => FF
  end.

Definition mapsto_ sh t v1 := mapsto sh t v1 Vundef.

Fixpoint memory_block' (sh: share) (n: nat) (b: block) (i: Z) : mpred :=
  match n with
  | O => emp
  | S n' => mapsto_ sh (Tint I8 Unsigned noattr) (Vptr b (Ptrofs.repr i))
         * memory_block' sh n' b (i+1)
 end.

Definition memory_block (sh: share) (n: Z) (v: val) : mpred :=
 match v with
 | Vptr b ofs => (!!(Ptrofs.unsigned ofs + n < Ptrofs.modulus)) && memory_block' sh (Z.to_nat n) b (Ptrofs.unsigned ofs)
 | _ => FF
 end.

Lemma mapsto__memory_block: forall sh b ofs t ch,
  access_mode t = By_value ch ->
  type_is_volatile t = false ->
  (align_chunk ch | Ptrofs.unsigned ofs) ->
  Ptrofs.unsigned ofs + size_chunk ch < Ptrofs.modulus ->
  mapsto_ sh t (Vptr b ofs) = memory_block sh (size_chunk ch) (Vptr b ofs).
admit.
Defined.
Definition tint := Tint I32 Signed noattr.
Definition tlong := Tlong Signed noattr.

Definition argsHaveTyps (vals:list val) (types: list type): Prop:=
  Forall2 (fun v t => v<>Vundef -> Val.has_type v t) vals (map typ_of_type types).

Definition funspec_sub (f1 f2 : funspec): Prop :=
match f1 with
| mk_funspec tpsig1 cc1 A1 P1 Q1 _ _ =>
    match f2 with
    | mk_funspec tpsig2 cc2 A2 P2 Q2 _ _ =>
        (tpsig1=tpsig2 /\ cc1=cc2) /\
        forall ts2 (x2:dependent_type_functor_rec ts2 A2 mpred) (gargs:argsEnviron),
        ((!! (argsHaveTyps(snd gargs)(fst tpsig1)) && P2 ts2 x2 gargs)
         |-- (EX ts1:_,  EX (x1:dependent_type_functor_rec ts1 A1 mpred), EX F:_,
                           (F * (P1 ts1 x1 gargs)) &&
                               (!! (forall rho',
                                           ((!!(ve_of rho' = Map.empty (block * type))) &&
                                                 (F * (Q1 ts1 x1 rho')))
                                         |-- (Q2 ts2 x2 rho')))))
    end
end.

Definition func_at (f: funspec): address -> pred rmap :=
  match f with
   | mk_funspec fsig cc A P Q _ _ => pureat (SomeP (SpecArgsTT A) (packPQ P Q)) (FUN fsig cc)
  end.

Definition func_ptr (f: funspec) (v: val): mpred :=
  EX b: block, !! (v = Vptr b Ptrofs.zero) && (EX gs: funspec, !!(funspec_sub gs f) && func_at gs (b, 0)).

Definition typed_true (t: type) (v: val)  : Prop := strict_bool_val v t
= Some true.

Definition typed_false (t: type)(v: val) : Prop := strict_bool_val v t =
                                                   Some false.

Lemma func_ptr_isptr: forall spec f, func_ptr spec f |-- !! val_lemmas.isptr f.
admit.
Defined.
Module Export expr.

Definition sizeof {cs: compspecs} t := @Ctypes.sizeof (@cenv_cs cs) t.

Definition size_compatible {C: compspecs} t p :=
  match p with
  | Vptr b i_ofs => Ptrofs.unsigned i_ofs + sizeof t < Ptrofs.modulus
  | _ => True
  end.
Export VST.msl.seplog.
Export VST.msl.log_normalize.

Definition align_compatible {C: compspecs} t p :=
  match p with
  | Vptr b i_ofs => align_compatible_rec cenv_cs t (Ptrofs.unsigned i_ofs)
  | _ => True
  end.

Definition ptr_eq (v1 v2: val) : Prop :=
      match v1,v2 with
      | Vint n1, Vint n2 =>  Archi.ptr64 = false /\ Int.cmpu Ceq n1 n2 = true  /\ Int.cmpu Ceq n1 (Int.repr 0) = true
      | Vlong n1, Vlong n2 =>  Archi.ptr64 = true /\ Int64.cmpu Ceq n1 n2 = true  /\ Int64.cmpu Ceq n1 (Int64.repr 0) = true
      | Vptr b1 ofs1,  Vptr b2 ofs2  =>
            b1=b2 /\ Ptrofs.cmpu Ceq ofs1 ofs2 = true
      | _,_ => False
      end.

Lemma ptr_eq_e: forall v1 v2, ptr_eq v1 v2 -> v1=v2.
admit.
Defined.

Definition headptr (v: val): Prop :=
  exists b,  v = Vptr b Ptrofs.zero.

Lemma headptr_isptr: forall v,
  headptr v -> isptr v.
admit.
Defined.

Lemma typed_false_ptr:
  forall {t a v},  typed_false (Tpointer t a) v -> v=nullval.
admit.
Defined.

Lemma typed_true_ptr:
  forall {t a v},  typed_true (Tpointer t a) v -> isptr v.
admit.
Defined.

Lemma typed_false_of_bool:
 forall x, typed_false tint (Val.of_bool x) -> (x=false).
admit.
Defined.

Lemma typed_true_of_bool:
 forall x, typed_true tint (Val.of_bool x) -> (x=true).
admit.
Defined.

Lemma typed_false_tint:
 Archi.ptr64=false ->
 forall v, typed_false tint v -> v=nullval.
admit.
Defined.

Lemma typed_false_tlong:
 Archi.ptr64=true ->
 forall v, typed_false tlong v -> v=nullval.
admit.
Defined.

Lemma typed_false_tint_Vint:
  forall v, typed_false tint (Vint v) -> v = Int.zero.
admit.
Defined.

Lemma typed_true_tint_Vint:
  forall v, typed_true tint (Vint v) -> v <> Int.zero.
admit.
Defined.

Lemma typed_true_tlong_Vlong:
  forall v, typed_true tlong (Vlong v) -> v <> Int64.zero.
admit.
Defined.

Ltac intro_redundant P :=
 match goal with H: P |- _ => idtac end.

Ltac fancy_intro_discriminate H := idtac.

Ltac fancy_intro aggressive :=
 lazymatch goal with |- ~ _ => red | _ => idtac end;
 lazymatch goal with
 | |- ?P -> _ => match type of P with Prop => idtac end
 end;
 tryif
 lazymatch goal with |- ?P -> _ =>
     lazymatch P with
     | ptr_eq ?v1 ?v2 => intro_redundant (v1=v2)
     | Vint ?x = Vint ?y => constr_eq x y + intro_redundant (x=y)
     | tc_val ?ty ?v =>
         lazymatch ty with
         | Tint ?sz ?sg _ => intro_redundant(is_int sz sg v)
         | Tlong _ _ => intro_redundant(is_long v)
         | Tfloat F32 _ => intro_redundant(is_single v)
         | Tfloat F64 _ => intro_redundant(is_float v)
         | Tpointer _ _ =>
           tryif (unify ty int_or_ptr_type)
           then intro_redundant (is_pointer_or_integer v)
           else intro_redundant (is_pointer_or_null v)
         | Tarray _ _ _ =>  intro_redundant (is_pointer_or_null v)
         | Tfunction _ _ _ =>  intro_redundant (is_pointer_or_null v)
         | _ =>  intro_redundant (isptr v)
         end
     | ?x = ?y => constr_eq x y + intro_redundant P
     | _ => intro_redundant P + unify P True
    end
   end
   then intros _
   else
 let H := fresh in
 intro H;
 try simple apply ptr_eq_e in H;
 try simple apply Vint_inj in H;
 try lazymatch type of H with
 | tc_val _ _ => unfold tc_val in H; try change (eqb_type _ _) with false in H; cbv iota in H
 | ?x = ?y => tryif constr_eq aggressive true
                     then first [subst x | subst y
                                    | is_var x; rewrite H
                                    | is_var y; rewrite <- H
                                    | try fancy_intro_discriminate H]
                     else (try fancy_intro_discriminate H)
 | headptr (_ ?x) => let Hx1 := fresh "HP" x in
                     let Hx2 := fresh "P" x in
                       rename H into Hx1;
                       pose proof headptr_isptr _ Hx1 as Hx2
 | headptr ?x => let Hx1 := fresh "HP" x in
                 let Hx2 := fresh "P" x in
                   rename H into Hx1;
                   pose proof headptr_isptr _ Hx1 as Hx2
 | isptr ?x => let Hx := fresh "P" x in rename H into Hx
 | is_pointer_or_null ?x => let Hx := fresh "PN" x in rename H into Hx
 | typed_false _ _ =>
        first [simple apply typed_false_of_bool in H
               | apply typed_false_tint_Vint in H
               | apply (typed_false_tint (eq_refl _)) in H
               | apply (typed_false_tlong (eq_refl _)) in H
               | apply typed_false_ptr in H
               | idtac ]
 | typed_true _ _ =>
        first [simple apply typed_true_of_bool in H
               | apply typed_true_tint_Vint in H
               | apply typed_true_tlong_Vlong in H
               | apply typed_true_ptr in H
               | idtac ]
 end.

Ltac fancy_intros aggressive :=
 repeat lazymatch goal with
  | |- (_ <= _ < _) -> _ => fancy_intro aggressive
  | |- (_ < _ <= _) -> _ => fancy_intro aggressive
  | |- (_ <= _ <= _) -> _ => fancy_intro aggressive
  | |- (_ < _ < _) -> _ => fancy_intro aggressive
  | |- (?A /\ ?B) -> ?C => apply (@and_ind A B C)
  | |- _ -> _ => fancy_intro aggressive
  end.
#[export] Hint Resolve TT_right : core.

#[export] Hint Resolve func_ptr_isptr: saturate_local.

Lemma saturate_aux20:
 forall (P Q: mpred) P' Q' ,
    P |-- !! P' ->
    Q |-- !! Q' ->
    P * Q |-- !! (P' /\ Q').
admit.
Defined.

Lemma saturate_aux21x:
  forall (P Q S: mpred),
   P |-- S ->
   S && P |-- Q -> P |-- Q.
admit.
Defined.

Ltac check_mpreds2 R :=
 lazymatch R with
 | @sepcon mpred _ _ ?a ?b => check_mpreds2 a; check_mpreds2 b
 | _ => match type of R with ?t =>
                          first [constr_eq t mpred
                                 | fail 10 "The conjunct" R "has type" t "but should have type mpred; these two types may be convertible but they are not identical"]
                     end
 | nil => idtac
 end.

Ltac saturate_local :=
 match goal with |- ?R |-- _ => check_mpreds2 R end;
 simple eapply saturate_aux21x;
 [repeat simple apply saturate_aux20;

    auto with nocore saturate_local;
     simple apply prop_True_right
 | simple apply derives_extract_prop;
   match goal with |- _ -> ?A =>
       let P := fresh "P" in set (P := A);
       fancy_intros true;
       subst P
      end
 ].

Lemma access_mode_by_value: forall t, type_is_by_value t = true -> exists ch, access_mode t = By_value ch.
admit.
Defined.

Section COMPSPECS.

Context {cs: compspecs}.

Lemma memory_block_mapsto_:
  forall sh t p,
   type_is_by_value t = true ->
   type_is_volatile t = false ->
   size_compatible t p ->
   align_compatible t p ->
   memory_block sh (sizeof t) p = mapsto_ sh t p.
Proof.
  intros.
  assert (isptr p \/ ~isptr p) by (destruct p; simpl; auto).
  destruct H3.
destruct p; try contradiction.
  +
 simpl in H1, H2.
    destruct (access_mode_by_value _ H) as [ch ?].
    unfold expr.sizeof, Ctypes.sizeof in *; erewrite size_chunk_sizeof in H1 |- * by eauto.
    rewrite mapsto_memory_block.mapsto__memory_block with (ch := ch); auto.
    eapply align_compatible_rec_by_value_inv in H2; [| eassumption].
    auto.
  +
 apply pred_ext; saturate_local; try contradiction.
