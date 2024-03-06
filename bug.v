
(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-native-compiler" "no" "-w" "-undeclared-scope" "-w" "-omega-is-deprecated" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/compcert/lib" "compcert.lib" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/compcert/common" "compcert.common" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/compcert/x86_32" "compcert.x86_32" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/compcert/x86" "compcert.x86" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/compcert/backend" "compcert.backend" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/compcert/cfrontend" "compcert.cfrontend" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/compcert/driver" "compcert.driver" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/compcert/export" "compcert.export" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/compcert/cparser" "compcert.cparser" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Flocq" "Flocq" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/MenhirLib" "MenhirLib" "-top" "Top.bug_01") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 496 lines to 90 lines, then from 103 lines to 1133 lines, then from 1138 lines to 99 lines, then from 112 lines to 1006 lines, then from 1010 lines to 103 lines, then from 116 lines to 1437 lines, then from 1441 lines to 446 lines, then from 459 lines to 2743 lines, then from 2748 lines to 450 lines, then from 463 lines to 757 lines, then from 762 lines to 466 lines, then from 479 lines to 1080 lines, then from 1085 lines to 485 lines, then from 498 lines to 1157 lines, then from 1162 lines to 470 lines, then from 483 lines to 950 lines, then from 954 lines to 472 lines, then from 485 lines to 937 lines, then from 940 lines to 478 lines, then from 491 lines to 655 lines, then from 660 lines to 481 lines, then from 494 lines to 1336 lines, then from 1341 lines to 487 lines, then from 500 lines to 820 lines, then from 825 lines to 490 lines, then from 503 lines to 861 lines, then from 866 lines to 517 lines, then from 530 lines to 1338 lines, then from 1343 lines to 519 lines, then from 532 lines to 817 lines, then from 822 lines to 509 lines, then from 522 lines to 3176 lines, then from 3181 lines to 515 lines, then from 528 lines to 2008 lines, then from 2012 lines to 663 lines, then from 676 lines to 1088 lines, then from 1092 lines to 709 lines, then from 722 lines to 1252 lines, then from 1257 lines to 977 lines, then from 963 lines to 715 lines, then from 728 lines to 2259 lines, then from 2264 lines to 696 lines, then from 709 lines to 1964 lines, then from 1969 lines to 703 lines, then from 716 lines to 1039 lines, then from 1043 lines to 707 lines, then from 720 lines to 2153 lines, then from 2155 lines to 713 lines, then from 726 lines to 1414 lines, then from 1418 lines to 711 lines, then from 724 lines to 1460 lines, then from 1465 lines to 718 lines, then from 731 lines to 1097 lines, then from 1102 lines to 720 lines, then from 733 lines to 2859 lines, then from 2864 lines to 722 lines, then from 735 lines to 5583 lines, then from 5588 lines to 2459 lines, then from 2413 lines to 946 lines, then from 959 lines to 1861 lines, then from 1866 lines to 675 lines, then from 688 lines to 1053 lines, then from 1051 lines to 680 lines, then from 693 lines to 868 lines, then from 873 lines to 685 lines, then from 698 lines to 2121 lines, then from 2126 lines to 691 lines, then from 704 lines to 1263 lines, then from 1267 lines to 695 lines, then from 708 lines to 1407 lines, then from 1411 lines to 701 lines, then from 714 lines to 911 lines, then from 916 lines to 703 lines, then from 716 lines to 2399 lines, then from 2404 lines to 709 lines, then from 722 lines to 1508 lines, then from 1511 lines to 712 lines, then from 725 lines to 1384 lines, then from 1389 lines to 765 lines, then from 778 lines to 944 lines, then from 949 lines to 764 lines, then from 777 lines to 2373 lines, then from 2378 lines to 761 lines, then from 774 lines to 1974 lines, then from 1978 lines to 762 lines, then from 775 lines to 1443 lines, then from 1448 lines to 772 lines, then from 785 lines to 3135 lines, then from 3139 lines to 778 lines, then from 791 lines to 1159 lines, then from 1164 lines to 905 lines, then from 911 lines to 780 lines, then from 793 lines to 2890 lines, then from 2895 lines to 786 lines, then from 799 lines to 1674 lines, then from 1678 lines to 786 lines, then from 799 lines to 1374 lines, then from 1378 lines to 842 lines, then from 855 lines to 2183 lines, then from 2188 lines to 938 lines, then from 951 lines to 3380 lines, then from 3384 lines to 849 lines, then from 862 lines to 1254 lines, then from 1259 lines to 850 lines, then from 863 lines to 1534 lines, then from 1538 lines to 924 lines, then from 937 lines to 1388 lines, then from 1393 lines to 948 lines, then from 961 lines to 2597 lines, then from 2602 lines to 1076 lines, then from 1089 lines to 1404 lines, then from 1408 lines to 1204 lines, then from 1217 lines to 1276 lines, then from 1281 lines to 1214 lines, then from 1227 lines to 3770 lines, then from 3774 lines to 1225 lines, then from 1238 lines to 2533 lines, then from 2537 lines to 1643 lines, then from 1656 lines to 2382 lines, then from 2387 lines to 1684 lines, then from 1697 lines to 2535 lines, then from 2540 lines to 1854 lines, then from 1867 lines to 2813 lines, then from 2816 lines to 2664 lines, then from 2614 lines to 1920 lines, then from 1933 lines to 4200 lines, then from 4204 lines to 2010 lines, then from 2023 lines to 3883 lines, then from 3887 lines to 2045 lines, then from 2058 lines to 4062 lines, then from 4067 lines to 2121 lines, then from 2134 lines to 2434 lines, then from 2439 lines to 2210 lines, then from 2223 lines to 4136 lines, then from 4136 lines to 2259 lines, then from 2272 lines to 6893 lines, then from 6898 lines to 3569 lines, then from 3582 lines to 4885 lines, then from 4889 lines to 3594 lines *)
(* coqc version 8.20+alpha compiled with OCaml 4.14.1
   coqtop version runner-cabngxqim-project-4504-concurrent-5:/builds/coq/coq/_build/default,(HEAD detached at c78d2c737036) (c78d2c737036dcf9c23a328abe0955d20a415e43)
   Expected coqc runtime on this file: 1.058 sec *)
Require compcert.cfrontend.Ctypes.
Require compcert.common.Memdata.
Require Coq.FSets.FSets.

 

Inductive permission: Type :=
  | Freeable: permission
  | Writable: permission
  | Readable: permission
  | Nonempty: permission.

 

Inductive perm_order: permission -> permission -> Prop :=
  | perm_refl:  forall p, perm_order p p
  | perm_F_any: forall p, perm_order Freeable p
  | perm_W_R:   perm_order Writable Readable
  | perm_any_N: forall p, perm_order p Nonempty.

 

Inductive perm_kind: Type :=
  | Max: perm_kind
  | Cur: perm_kind.

Module Type MEM.

End MEM.
Import compcert.lib.Coqlib.
Import compcert.lib.Maps.
Import compcert.common.AST.
Import compcert.lib.Integers.
Import compcert.common.Values.
Export compcert.common.Memdata.

Local Notation "a # b" := (PMap.get b a) (at level 1).

Module Mem <: MEM.

Definition perm_order'' (po1 po2: option permission) :=
  match po1, po2 with
  | Some p1, Some p2 => perm_order p1 p2
  | _, None => True
  | None, Some _ => False
 end.

Record mem' : Type := mkmem {
  mem_contents: PMap.t (ZMap.t memval);
  mem_access: PMap.t (Z -> perm_kind -> option permission);

  nextblock: block;
  access_max:
    forall b ofs, perm_order'' (mem_access#b ofs Max) (mem_access#b ofs Cur);
  nextblock_noaccess:
    forall b ofs k, ~(Plt b nextblock) -> mem_access#b ofs k = None;
  contents_default:
    forall b, fst mem_contents#b = Undef
}.

Definition mem := mem'.

Definition valid_block (m: mem) (b: block) := Plt b (nextblock m).

Theorem valid_not_valid_diff:
  forall m b b', valid_block m b -> ~(valid_block m b') -> b <> b'.
Admitted.
Definition perm (m: mem) (b: block) (ofs: Z) (k: perm_kind) (p: permission) : Prop.
Admitted.

Theorem perm_implies:
  forall m b ofs k p1 p2, perm m b ofs k p1 -> perm_order p1 p2 -> perm m b ofs k p2.
Admitted.

Theorem perm_cur_max:
  forall m b ofs p, perm m b ofs Cur p -> perm m b ofs Max p.
Admitted.

Theorem perm_cur:
  forall m b ofs k p, perm m b ofs Cur p -> perm m b ofs k p.
Admitted.

Theorem perm_max:
  forall m b ofs k p, perm m b ofs k p -> perm m b ofs Max p.
Admitted.

Theorem perm_valid_block:
  forall m b ofs k p, perm m b ofs k p -> valid_block m b.
Admitted.
Definition range_perm (m: mem) (b: block) (lo hi: Z) (k: perm_kind) (p: permission) : Prop.
exact (forall ofs, lo <= ofs < hi -> perm m b ofs k p).
Defined.

Theorem range_perm_implies:
  forall m b lo hi k p1 p2,
  range_perm m b lo hi k p1 -> perm_order p1 p2 -> range_perm m b lo hi k p2.
Admitted.

Lemma range_perm_dec:
  forall m b lo hi k p, {range_perm m b lo hi k p} + {~ range_perm m b lo hi k p}.
Admitted.
Definition valid_access (m: mem) (chunk: memory_chunk) (b: block) (ofs: Z) (p: permission): Prop.
exact (range_perm m b ofs (ofs + size_chunk chunk) Cur p
  /\ (align_chunk chunk | ofs)).
Defined.

Theorem valid_access_implies:
  forall m chunk b ofs p1 p2,
  valid_access m chunk b ofs p1 -> perm_order p1 p2 ->
  valid_access m chunk b ofs p2.
Admitted.

Theorem valid_access_valid_block:
  forall m chunk b ofs,
  valid_access m chunk b ofs Nonempty ->
  valid_block m b.
Admitted.

Lemma valid_access_perm:
  forall m chunk b ofs k p,
  valid_access m chunk b ofs p ->
  perm m b ofs k p.
Admitted.

Lemma valid_access_dec:
  forall m chunk b ofs p,
  {valid_access m chunk b ofs p} + {~ valid_access m chunk b ofs p}.
Admitted.
Definition valid_pointer (m: mem) (b: block) (ofs: Z): bool.
Admitted.

Theorem valid_pointer_nonempty_perm:
  forall m b ofs,
  valid_pointer m b ofs = true <-> perm m b ofs Cur Nonempty.
Admitted.

Theorem valid_pointer_valid_access:
  forall m b ofs,
  valid_pointer m b ofs = true <-> valid_access m Mint8unsigned b ofs Nonempty.
Admitted.

Definition weak_valid_pointer (m: mem) (b: block) (ofs: Z) :=
  valid_pointer m b ofs || valid_pointer m b (ofs - 1).

Lemma weak_valid_pointer_spec:
  forall m b ofs,
  weak_valid_pointer m b ofs = true <->
    valid_pointer m b ofs = true \/ valid_pointer m b (ofs - 1) = true.
Admitted.
Lemma valid_pointer_implies:
  forall m b ofs,
  valid_pointer m b ofs = true -> weak_valid_pointer m b ofs = true.
Admitted.

Program Definition empty: mem :=
  mkmem (PMap.init (ZMap.init Undef))
        (PMap.init (fun ofs k => None))
        1%positive _ _ _.

Program Definition alloc (m: mem) (lo hi: Z) :=
  (mkmem (PMap.set m.(nextblock)
                   (ZMap.init Undef)
                   m.(mem_contents))
         (PMap.set m.(nextblock)
                   (fun ofs k => if zle lo ofs && zlt ofs hi then Some Freeable else None)
                   m.(mem_access))
         (Pos.succ m.(nextblock))
         _ _ _,
   m.(nextblock)).
Definition free (m: mem) (b: block) (lo hi: Z): option mem.
Admitted.
Fixpoint free_list (m: mem) (l: list (block * Z * Z)) {struct l}: option mem.
exact (match l with
  | nil => Some m
  | (b, lo, hi) :: l' =>
      match free m b lo hi with
      | None => None
      | Some m' => free_list m' l'
      end
  end).
Defined.
Definition load (chunk: memory_chunk) (m: mem) (b: block) (ofs: Z): option val.
Admitted.
Definition loadv (chunk: memory_chunk) (m: mem) (addr: val) : option val.
exact (match addr with
  | Vptr b ofs => load chunk m b (Ptrofs.unsigned ofs)
  | _ => None
  end).
Defined.
Definition loadbytes (m: mem) (b: block) (ofs n: Z): option (list memval).
Admitted.
Fixpoint setN (vl: list memval) (p: Z) (c: ZMap.t memval) {struct vl}: ZMap.t memval.
Admitted.

Program Definition store (chunk: memory_chunk) (m: mem) (b: block) (ofs: Z) (v: val): option mem :=
  if valid_access_dec m chunk b ofs Writable then
    Some (mkmem (PMap.set b
                          (setN (encode_val chunk v) ofs (m.(mem_contents)#b))
                          m.(mem_contents))
                m.(mem_access)
                m.(nextblock)
                _ _ _)
  else
    None.
Admit Obligations.
Definition storev (chunk: memory_chunk) (m: mem) (addr v: val) : option mem.
exact (match addr with
  | Vptr b ofs => store chunk m b (Ptrofs.unsigned ofs) v
  | _ => None
  end).
Defined.

Program Definition storebytes (m: mem) (b: block) (ofs: Z) (bytes: list memval) : option mem :=
  if range_perm_dec m b ofs (ofs + Z.of_nat (length bytes)) Cur Writable then
    Some (mkmem
             (PMap.set b (setN bytes ofs (m.(mem_contents)#b)) m.(mem_contents))
             m.(mem_access)
             m.(nextblock)
             _ _ _)
  else
    None.

Program Definition drop_perm (m: mem) (b: block) (lo hi: Z) (p: permission): option mem :=
  if range_perm_dec m b lo hi Cur Freeable then
    Some (mkmem m.(mem_contents)
                (PMap.set b
                        (fun ofs k => if zle lo ofs && zlt ofs hi then Some p else m.(mem_access)#b ofs k)
                        m.(mem_access))
                m.(nextblock) _ _ _)
  else None.
Admit Obligations.

Theorem nextblock_empty: nextblock empty = 1%positive.
Admitted.

Theorem perm_empty: forall b ofs k p, ~perm empty b ofs k p.
Admitted.

Theorem valid_access_empty: forall chunk b ofs p, ~valid_access empty chunk b ofs p.
Admitted.

Theorem valid_access_load:
  forall m chunk b ofs,
  valid_access m chunk b ofs Readable ->
  exists v, load chunk m b ofs = Some v.
Admitted.

Theorem load_valid_access:
  forall m chunk b ofs v,
  load chunk m b ofs = Some v ->
  valid_access m chunk b ofs Readable.
Admitted.

Theorem load_type:
  forall m chunk b ofs v,
  load chunk m b ofs = Some v ->
  Val.has_type v (type_of_chunk chunk).
Admitted.

Theorem load_rettype:
  forall m chunk b ofs v,
  load chunk m b ofs = Some v ->
  Val.has_rettype v (rettype_of_chunk chunk).
Admitted.

Theorem load_cast:
  forall m chunk b ofs v,
  load chunk m b ofs = Some v ->
  match chunk with
  | Mint8signed => v = Val.sign_ext 8 v
  | Mint8unsigned => v = Val.zero_ext 8 v
  | Mint16signed => v = Val.sign_ext 16 v
  | Mint16unsigned => v = Val.zero_ext 16 v
  | _ => True
  end.
Admitted.

Theorem load_int8_signed_unsigned:
  forall m b ofs,
  load Mint8signed m b ofs = option_map (Val.sign_ext 8) (load Mint8unsigned m b ofs).
Admitted.

Theorem load_int16_signed_unsigned:
  forall m b ofs,
  load Mint16signed m b ofs = option_map (Val.sign_ext 16) (load Mint16unsigned m b ofs).
Admitted.

Theorem range_perm_loadbytes:
  forall m b ofs len,
  range_perm m b ofs (ofs + len) Cur Readable ->
  exists bytes, loadbytes m b ofs len = Some bytes.
Admitted.

Theorem loadbytes_range_perm:
  forall m b ofs len bytes,
  loadbytes m b ofs len = Some bytes ->
  range_perm m b ofs (ofs + len) Cur Readable.
Admitted.

Theorem loadbytes_load:
  forall chunk m b ofs bytes,
  loadbytes m b ofs (size_chunk chunk) = Some bytes ->
  (align_chunk chunk | ofs) ->
  load chunk m b ofs = Some(decode_val chunk bytes).
Admitted.

Theorem load_loadbytes:
  forall chunk m b ofs v,
  load chunk m b ofs = Some v ->
  exists bytes, loadbytes m b ofs (size_chunk chunk) = Some bytes
             /\ v = decode_val chunk bytes.
Admitted.

Theorem loadbytes_length:
  forall m b ofs n bytes,
  loadbytes m b ofs n = Some bytes ->
  length bytes = Z.to_nat n.
Admitted.

Theorem loadbytes_empty:
  forall m b ofs n,
  n <= 0 -> loadbytes m b ofs n = Some nil.
Admitted.

Theorem loadbytes_concat:
  forall m b ofs n1 n2 bytes1 bytes2,
  loadbytes m b ofs n1 = Some bytes1 ->
  loadbytes m b (ofs + n1) n2 = Some bytes2 ->
  n1 >= 0 -> n2 >= 0 ->
  loadbytes m b ofs (n1 + n2) = Some(bytes1 ++ bytes2).
Admitted.

Theorem loadbytes_split:
  forall m b ofs n1 n2 bytes,
  loadbytes m b ofs (n1 + n2) = Some bytes ->
  n1 >= 0 -> n2 >= 0 ->
  exists bytes1, exists bytes2,
     loadbytes m b ofs n1 = Some bytes1
  /\ loadbytes m b (ofs + n1) n2 = Some bytes2
  /\ bytes = bytes1 ++ bytes2.
Admitted.

Theorem valid_access_store:
  forall m1 chunk b ofs v,
  valid_access m1 chunk b ofs Writable ->
  { m2: mem | store chunk m1 b ofs v = Some m2 }.
Admitted.

Section STORE.
Variable chunk: memory_chunk.
Variable m1: mem.
Variable b: block.
Variable ofs: Z.
Variable v: val.
Variable m2: mem.
Hypothesis STORE: store chunk m1 b ofs v = Some m2.

Theorem perm_store_1:
  forall b' ofs' k p, perm m1 b' ofs' k p -> perm m2 b' ofs' k p.
Admitted.

Theorem perm_store_2:
  forall b' ofs' k p, perm m2 b' ofs' k p -> perm m1 b' ofs' k p.
Admitted.

Theorem nextblock_store:
  nextblock m2 = nextblock m1.
Admitted.

Theorem store_valid_block_1:
  forall b', valid_block m1 b' -> valid_block m2 b'.
Admitted.

Theorem store_valid_block_2:
  forall b', valid_block m2 b' -> valid_block m1 b'.
Admitted.

Theorem store_valid_access_1:
  forall chunk' b' ofs' p,
  valid_access m1 chunk' b' ofs' p -> valid_access m2 chunk' b' ofs' p.
Admitted.

Theorem store_valid_access_2:
  forall chunk' b' ofs' p,
  valid_access m2 chunk' b' ofs' p -> valid_access m1 chunk' b' ofs' p.
Admitted.

Theorem store_valid_access_3:
  valid_access m1 chunk b ofs Writable.
Admitted.

Theorem load_store_similar:
  forall chunk',
  size_chunk chunk' = size_chunk chunk ->
  align_chunk chunk' <= align_chunk chunk ->
  exists v', load chunk' m2 b ofs = Some v' /\ decode_encode_val v chunk chunk' v'.
Admitted.

Theorem load_store_same:
  load chunk m2 b ofs = Some (Val.load_result chunk v).
Admitted.

Theorem load_store_other:
  forall chunk' b' ofs',
  b' <> b
  \/ ofs' + size_chunk chunk' <= ofs
  \/ ofs + size_chunk chunk <= ofs' ->
  load chunk' m2 b' ofs' = load chunk' m1 b' ofs'.
Admitted.

Theorem loadbytes_store_same:
  loadbytes m2 b ofs (size_chunk chunk) = Some(encode_val chunk v).
Admitted.

Theorem loadbytes_store_other:
  forall b' ofs' n,
  b' <> b
  \/ n <= 0
  \/ ofs' + n <= ofs
  \/ ofs + size_chunk chunk <= ofs' ->
  loadbytes m2 b' ofs' n = loadbytes m1 b' ofs' n.
Admitted.

End STORE.
Definition compat_pointer_chunks (chunk1 chunk2: memory_chunk) : Prop.
exact (match chunk1, chunk2 with
  | (Mint32 | Many32), (Mint32 | Many32) => True
  | (Mint64 | Many64), (Mint64 | Many64) => True
  | _, _ => False
  end).
Defined.

Theorem load_pointer_store:
  forall chunk m1 b ofs v m2 chunk' b' ofs' v_b v_o,
  store chunk m1 b ofs v = Some m2 ->
  load chunk' m2 b' ofs' = Some(Vptr v_b v_o) ->
  (v = Vptr v_b v_o /\ compat_pointer_chunks chunk chunk' /\ b' = b /\ ofs' = ofs)
  \/ (b' <> b \/ ofs' + size_chunk chunk' <= ofs \/ ofs + size_chunk chunk <= ofs').
Admitted.

Theorem load_store_pointer_overlap:
  forall chunk m1 b ofs v_b v_o m2 chunk' ofs' v,
  store chunk m1 b ofs (Vptr v_b v_o) = Some m2 ->
  load chunk' m2 b ofs' = Some v ->
  ofs' <> ofs ->
  ofs' + size_chunk chunk' > ofs ->
  ofs + size_chunk chunk > ofs' ->
  v = Vundef.
Admitted.

Theorem load_store_pointer_mismatch:
  forall chunk m1 b ofs v_b v_o m2 chunk' v,
  store chunk m1 b ofs (Vptr v_b v_o) = Some m2 ->
  load chunk' m2 b ofs = Some v ->
  ~compat_pointer_chunks chunk chunk' ->
  v = Vundef.
Admitted.

Theorem store_signed_unsigned_8:
  forall m b ofs v,
  store Mint8signed m b ofs v = store Mint8unsigned m b ofs v.
Admitted.

Theorem store_signed_unsigned_16:
  forall m b ofs v,
  store Mint16signed m b ofs v = store Mint16unsigned m b ofs v.
Admitted.

Theorem store_int8_zero_ext:
  forall m b ofs n,
  store Mint8unsigned m b ofs (Vint (Int.zero_ext 8 n)) =
  store Mint8unsigned m b ofs (Vint n).
Admitted.

Theorem store_int8_sign_ext:
  forall m b ofs n,
  store Mint8signed m b ofs (Vint (Int.sign_ext 8 n)) =
  store Mint8signed m b ofs (Vint n).
Admitted.

Theorem store_int16_zero_ext:
  forall m b ofs n,
  store Mint16unsigned m b ofs (Vint (Int.zero_ext 16 n)) =
  store Mint16unsigned m b ofs (Vint n).
Admitted.

Theorem store_int16_sign_ext:
  forall m b ofs n,
  store Mint16signed m b ofs (Vint (Int.sign_ext 16 n)) =
  store Mint16signed m b ofs (Vint n).
Admitted.

Theorem range_perm_storebytes:
  forall m1 b ofs bytes,
  range_perm m1 b ofs (ofs + Z.of_nat (length bytes)) Cur Writable ->
  { m2 : mem | storebytes m1 b ofs bytes = Some m2 }.
Admitted.

Theorem storebytes_store:
  forall m1 b ofs chunk v m2,
  storebytes m1 b ofs (encode_val chunk v) = Some m2 ->
  (align_chunk chunk | ofs) ->
  store chunk m1 b ofs v = Some m2.
Admitted.

Theorem store_storebytes:
  forall m1 b ofs chunk v m2,
  store chunk m1 b ofs v = Some m2 ->
  storebytes m1 b ofs (encode_val chunk v) = Some m2.
Admitted.

Section STOREBYTES.
Variable m1: mem.
Variable b: block.
Variable ofs: Z.
Variable bytes: list memval.
Variable m2: mem.
Hypothesis STORE: storebytes m1 b ofs bytes = Some m2.

Theorem perm_storebytes_1:
  forall b' ofs' k p, perm m1 b' ofs' k p -> perm m2 b' ofs' k p.
Admitted.

Theorem perm_storebytes_2:
  forall b' ofs' k p, perm m2 b' ofs' k p -> perm m1 b' ofs' k p.
Admitted.

Theorem storebytes_valid_access_1:
  forall chunk' b' ofs' p,
  valid_access m1 chunk' b' ofs' p -> valid_access m2 chunk' b' ofs' p.
Admitted.

Theorem storebytes_valid_access_2:
  forall chunk' b' ofs' p,
  valid_access m2 chunk' b' ofs' p -> valid_access m1 chunk' b' ofs' p.
Admitted.

Theorem nextblock_storebytes:
  nextblock m2 = nextblock m1.
Admitted.

Theorem storebytes_valid_block_1:
  forall b', valid_block m1 b' -> valid_block m2 b'.
Admitted.

Theorem storebytes_valid_block_2:
  forall b', valid_block m2 b' -> valid_block m1 b'.
Admitted.

Theorem storebytes_range_perm:
  range_perm m1 b ofs (ofs + Z.of_nat (length bytes)) Cur Writable.
Admitted.

Theorem loadbytes_storebytes_same:
  loadbytes m2 b ofs (Z.of_nat (length bytes)) = Some bytes.
Admitted.

Theorem loadbytes_storebytes_other:
  forall b' ofs' len,
  len >= 0 ->
  b' <> b
  \/ ofs' + len <= ofs
  \/ ofs + Z.of_nat (length bytes) <= ofs' ->
  loadbytes m2 b' ofs' len = loadbytes m1 b' ofs' len.
Admitted.

Theorem load_storebytes_other:
  forall chunk b' ofs',
  b' <> b
  \/ ofs' + size_chunk chunk <= ofs
  \/ ofs + Z.of_nat (length bytes) <= ofs' ->
  load chunk m2 b' ofs' = load chunk m1 b' ofs'.
Admitted.

End STOREBYTES.

Theorem storebytes_concat:
  forall m b ofs bytes1 m1 bytes2 m2,
  storebytes m b ofs bytes1 = Some m1 ->
  storebytes m1 b (ofs + Z.of_nat(length bytes1)) bytes2 = Some m2 ->
  storebytes m b ofs (bytes1 ++ bytes2) = Some m2.
Admitted.

Theorem storebytes_split:
  forall m b ofs bytes1 bytes2 m2,
  storebytes m b ofs (bytes1 ++ bytes2) = Some m2 ->
  exists m1,
     storebytes m b ofs bytes1 = Some m1
  /\ storebytes m1 b (ofs + Z.of_nat(length bytes1)) bytes2 = Some m2.
Admitted.

Section ALLOC.

Variable m1: mem.
Variables lo hi: Z.
Variable m2: mem.
Variable b: block.
Hypothesis ALLOC: alloc m1 lo hi = (m2, b).

Theorem nextblock_alloc:
  nextblock m2 = Pos.succ (nextblock m1).
Admitted.

Theorem alloc_result:
  b = nextblock m1.
Admitted.

Theorem valid_block_alloc:
  forall b', valid_block m1 b' -> valid_block m2 b'.
Admitted.

Theorem fresh_block_alloc:
  ~(valid_block m1 b).
Admitted.

Theorem valid_new_block:
  valid_block m2 b.
Admitted.

Theorem valid_block_alloc_inv:
  forall b', valid_block m2 b' -> b' = b \/ valid_block m1 b'.
Admitted.

Theorem perm_alloc_1:
  forall b' ofs k p, perm m1 b' ofs k p -> perm m2 b' ofs k p.
Admitted.

Theorem perm_alloc_2:
  forall ofs k, lo <= ofs < hi -> perm m2 b ofs k Freeable.
Admitted.

Theorem perm_alloc_inv:
  forall b' ofs k p,
  perm m2 b' ofs k p ->
  if eq_block b' b then lo <= ofs < hi else perm m1 b' ofs k p.
Admitted.

Theorem perm_alloc_3:
  forall ofs k p, perm m2 b ofs k p -> lo <= ofs < hi.
Admitted.

Theorem perm_alloc_4:
  forall b' ofs k p, perm m2 b' ofs k p -> b' <> b -> perm m1 b' ofs k p.
Admitted.

Theorem valid_access_alloc_other:
  forall chunk b' ofs p,
  valid_access m1 chunk b' ofs p ->
  valid_access m2 chunk b' ofs p.
Admitted.

Theorem valid_access_alloc_same:
  forall chunk ofs,
  lo <= ofs -> ofs + size_chunk chunk <= hi -> (align_chunk chunk | ofs) ->
  valid_access m2 chunk b ofs Freeable.
Admitted.

Theorem valid_access_alloc_inv:
  forall chunk b' ofs p,
  valid_access m2 chunk b' ofs p ->
  if eq_block b' b
  then lo <= ofs /\ ofs + size_chunk chunk <= hi /\ (align_chunk chunk | ofs)
  else valid_access m1 chunk b' ofs p.
Admitted.

Theorem load_alloc_unchanged:
  forall chunk b' ofs,
  valid_block m1 b' ->
  load chunk m2 b' ofs = load chunk m1 b' ofs.
Admitted.

Theorem load_alloc_other:
  forall chunk b' ofs v,
  load chunk m1 b' ofs = Some v ->
  load chunk m2 b' ofs = Some v.
Admitted.

Theorem load_alloc_same:
  forall chunk ofs v,
  load chunk m2 b ofs = Some v ->
  v = Vundef.
Admitted.

Theorem load_alloc_same':
  forall chunk ofs,
  lo <= ofs -> ofs + size_chunk chunk <= hi -> (align_chunk chunk | ofs) ->
  load chunk m2 b ofs = Some Vundef.
Admitted.

End ALLOC.

Theorem range_perm_free:
  forall m1 b lo hi,
  range_perm m1 b lo hi Cur Freeable ->
  { m2: mem | free m1 b lo hi = Some m2 }.
Admitted.

Section FREE.

Variable m1: mem.
Variable bf: block.
Variables lo hi: Z.
Variable m2: mem.
Hypothesis FREE: free m1 bf lo hi = Some m2.

Theorem free_range_perm:
  range_perm m1 bf lo hi Cur Freeable.
Admitted.

Theorem nextblock_free:
  nextblock m2 = nextblock m1.
Admitted.

Theorem valid_block_free_1:
  forall b, valid_block m1 b -> valid_block m2 b.
Admitted.

Theorem valid_block_free_2:
  forall b, valid_block m2 b -> valid_block m1 b.
Admitted.

Theorem perm_free_1:
  forall b ofs k p,
  b <> bf \/ ofs < lo \/ hi <= ofs ->
  perm m1 b ofs k p ->
  perm m2 b ofs k p.
Admitted.

Theorem perm_free_2:
  forall ofs k p, lo <= ofs < hi -> ~ perm m2 bf ofs k p.
Admitted.

Theorem perm_free_3:
  forall b ofs k p,
  perm m2 b ofs k p -> perm m1 b ofs k p.
Admitted.

Theorem valid_access_free_1:
  forall chunk b ofs p,
  valid_access m1 chunk b ofs p ->
  b <> bf \/ lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs ->
  valid_access m2 chunk b ofs p.
Admitted.

Theorem valid_access_free_2:
  forall chunk ofs p,
  lo < hi -> ofs + size_chunk chunk > lo -> ofs < hi ->
  ~(valid_access m2 chunk bf ofs p).
Admitted.

Theorem valid_access_free_inv_1:
  forall chunk b ofs p,
  valid_access m2 chunk b ofs p ->
  valid_access m1 chunk b ofs p.
Admitted.

Theorem valid_access_free_inv_2:
  forall chunk ofs p,
  valid_access m2 chunk bf ofs p ->
  lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs.
Admitted.

Theorem load_free:
  forall chunk b ofs,
  b <> bf \/ lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs ->
  load chunk m2 b ofs = load chunk m1 b ofs.
Admitted.

End FREE.

Theorem range_perm_drop_1:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' -> range_perm m b lo hi Cur Freeable.
Admitted.

Theorem range_perm_drop_2:
  forall m b lo hi p,
  range_perm m b lo hi Cur Freeable -> {m' | drop_perm m b lo hi p = Some m' }.
Admitted.

Section DROP.

Variable m: mem.
Variable b: block.
Variable lo hi: Z.
Variable p: permission.
Variable m': mem.
Hypothesis DROP: drop_perm m b lo hi p = Some m'.

Theorem nextblock_drop:
  nextblock m' = nextblock m.
Admitted.

Theorem drop_perm_valid_block_1:
  forall b', valid_block m b' -> valid_block m' b'.
Admitted.

Theorem drop_perm_valid_block_2:
  forall b', valid_block m' b' -> valid_block m b'.
Admitted.

Theorem perm_drop_1:
  forall ofs k, lo <= ofs < hi -> perm m' b ofs k p.
Admitted.

Theorem perm_drop_2:
  forall ofs k p', lo <= ofs < hi -> perm m' b ofs k p' -> perm_order p p'.
Admitted.

Theorem perm_drop_3:
  forall b' ofs k p', b' <> b \/ ofs < lo \/ hi <= ofs -> perm m b' ofs k p' -> perm m' b' ofs k p'.
Admitted.

Theorem perm_drop_4:
  forall b' ofs k p', perm m' b' ofs k p' -> perm m b' ofs k p'.
Admitted.

Theorem load_drop:
  forall chunk b' ofs,
  b' <> b \/ ofs + size_chunk chunk <= lo \/ hi <= ofs \/ perm_order p Readable ->
  load chunk m' b' ofs = load chunk m b' ofs.
Admitted.

End DROP.

Record mem_inj (f: meminj) (m1 m2: mem) : Prop :=
  mk_mem_inj {
    mi_perm:
      forall b1 b2 delta ofs k p,
      f b1 = Some(b2, delta) ->
      perm m1 b1 ofs k p ->
      perm m2 b2 (ofs + delta) k p;
    mi_align:
      forall b1 b2 delta chunk ofs p,
      f b1 = Some(b2, delta) ->
      range_perm m1 b1 ofs (ofs + size_chunk chunk) Max p ->
      (align_chunk chunk | delta);
    mi_memval:
      forall b1 ofs b2 delta,
      f b1 = Some(b2, delta) ->
      perm m1 b1 ofs Cur Readable ->
      memval_inject f (ZMap.get ofs m1.(mem_contents)#b1) (ZMap.get (ofs+delta) m2.(mem_contents)#b2)
  }.
Definition meminj_no_overlap (f: meminj) (m: mem) : Prop.
Admitted.
Definition inj_offset_aligned (delta: Z) (size: Z) : Prop.
exact (forall chunk, size_chunk chunk <= size -> (align_chunk chunk | delta)).
Defined.

Record extends' (m1 m2: mem) : Prop :=
  mk_extends {
    mext_next: nextblock m1 = nextblock m2;
    mext_inj:  mem_inj inject_id m1 m2;
    mext_perm_inv: forall b ofs k p,
      perm m2 b ofs k p ->
      perm m1 b ofs k p \/ ~perm m1 b ofs Max Nonempty
  }.

Definition extends := extends'.

Theorem extends_refl:
  forall m, extends m m.
Admitted.

Theorem load_extends:
  forall chunk m1 m2 b ofs v1,
  extends m1 m2 ->
  load chunk m1 b ofs = Some v1 ->
  exists v2, load chunk m2 b ofs = Some v2 /\ Val.lessdef v1 v2.
Admitted.

Theorem loadv_extends:
  forall chunk m1 m2 addr1 addr2 v1,
  extends m1 m2 ->
  loadv chunk m1 addr1 = Some v1 ->
  Val.lessdef addr1 addr2 ->
  exists v2, loadv chunk m2 addr2 = Some v2 /\ Val.lessdef v1 v2.
Admitted.

Theorem loadbytes_extends:
  forall m1 m2 b ofs len bytes1,
  extends m1 m2 ->
  loadbytes m1 b ofs len = Some bytes1 ->
  exists bytes2, loadbytes m2 b ofs len = Some bytes2
              /\ list_forall2 memval_lessdef bytes1 bytes2.
Admitted.

Theorem store_within_extends:
  forall chunk m1 m2 b ofs v1 m1' v2,
  extends m1 m2 ->
  store chunk m1 b ofs v1 = Some m1' ->
  Val.lessdef v1 v2 ->
  exists m2',
     store chunk m2 b ofs v2 = Some m2'
  /\ extends m1' m2'.
Admitted.

Theorem store_outside_extends:
  forall chunk m1 m2 b ofs v m2',
  extends m1 m2 ->
  store chunk m2 b ofs v = Some m2' ->
  (forall ofs', perm m1 b ofs' Cur Readable -> ofs <= ofs' < ofs + size_chunk chunk -> False) ->
  extends m1 m2'.
Admitted.

Theorem storev_extends:
  forall chunk m1 m2 addr1 v1 m1' addr2 v2,
  extends m1 m2 ->
  storev chunk m1 addr1 v1 = Some m1' ->
  Val.lessdef addr1 addr2 ->
  Val.lessdef v1 v2 ->
  exists m2',
     storev chunk m2 addr2 v2 = Some m2'
  /\ extends m1' m2'.
Admitted.

Theorem storebytes_within_extends:
  forall m1 m2 b ofs bytes1 m1' bytes2,
  extends m1 m2 ->
  storebytes m1 b ofs bytes1 = Some m1' ->
  list_forall2 memval_lessdef bytes1 bytes2 ->
  exists m2',
     storebytes m2 b ofs bytes2 = Some m2'
  /\ extends m1' m2'.
Admitted.

Theorem storebytes_outside_extends:
  forall m1 m2 b ofs bytes2 m2',
  extends m1 m2 ->
  storebytes m2 b ofs bytes2 = Some m2' ->
  (forall ofs', perm m1 b ofs' Cur Readable -> ofs <= ofs' < ofs + Z.of_nat (length bytes2) -> False) ->
  extends m1 m2'.
Admitted.

Theorem alloc_extends:
  forall m1 m2 lo1 hi1 b m1' lo2 hi2,
  extends m1 m2 ->
  alloc m1 lo1 hi1 = (m1', b) ->
  lo2 <= lo1 -> hi1 <= hi2 ->
  exists m2',
     alloc m2 lo2 hi2 = (m2', b)
  /\ extends m1' m2'.
Admitted.

Theorem free_left_extends:
  forall m1 m2 b lo hi m1',
  extends m1 m2 ->
  free m1 b lo hi = Some m1' ->
  extends m1' m2.
Admitted.

Theorem free_right_extends:
  forall m1 m2 b lo hi m2',
  extends m1 m2 ->
  free m2 b lo hi = Some m2' ->
  (forall ofs k p, perm m1 b ofs k p -> lo <= ofs < hi -> False) ->
  extends m1 m2'.
Admitted.

Theorem free_parallel_extends:
  forall m1 m2 b lo hi m1',
  extends m1 m2 ->
  free m1 b lo hi = Some m1' ->
  exists m2',
     free m2 b lo hi = Some m2'
  /\ extends m1' m2'.
Admitted.

Theorem valid_block_extends:
  forall m1 m2 b,
  extends m1 m2 ->
  (valid_block m1 b <-> valid_block m2 b).
Admitted.

Theorem perm_extends:
  forall m1 m2 b ofs k p,
  extends m1 m2 -> perm m1 b ofs k p -> perm m2 b ofs k p.
Admitted.

Theorem valid_access_extends:
  forall m1 m2 chunk b ofs p,
  extends m1 m2 -> valid_access m1 chunk b ofs p -> valid_access m2 chunk b ofs p.
Admitted.

Theorem valid_pointer_extends:
  forall m1 m2 b ofs,
  extends m1 m2 -> valid_pointer m1 b ofs = true -> valid_pointer m2 b ofs = true.
Admitted.

Theorem weak_valid_pointer_extends:
  forall m1 m2 b ofs,
  extends m1 m2 ->
  weak_valid_pointer m1 b ofs = true -> weak_valid_pointer m2 b ofs = true.
Admitted.

Record inject' (f: meminj) (m1 m2: mem) : Prop :=
  mk_inject {
    mi_inj:
      mem_inj f m1 m2;
    mi_freeblocks:
      forall b, ~(valid_block m1 b) -> f b = None;
    mi_mappedblocks:
      forall b b' delta, f b = Some(b', delta) -> valid_block m2 b';
    mi_no_overlap:
      meminj_no_overlap f m1;
    mi_representable:
      forall b b' delta ofs,
      f b = Some(b', delta) ->
      perm m1 b (Ptrofs.unsigned ofs) Max Nonempty \/ perm m1 b (Ptrofs.unsigned ofs - 1) Max Nonempty ->
      delta >= 0 /\ 0 <= Ptrofs.unsigned ofs + delta <= Ptrofs.max_unsigned;
    mi_perm_inv:
      forall b1 ofs b2 delta k p,
      f b1 = Some(b2, delta) ->
      perm m2 b2 (ofs + delta) k p ->
      perm m1 b1 ofs k p \/ ~perm m1 b1 ofs Max Nonempty
  }.
Definition inject := inject'.

Theorem valid_block_inject_1:
  forall f m1 m2 b1 b2 delta,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  valid_block m1 b1.
Admitted.

Theorem valid_block_inject_2:
  forall f m1 m2 b1 b2 delta,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  valid_block m2 b2.
Admitted.

Theorem perm_inject:
  forall f m1 m2 b1 b2 delta ofs k p,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  perm m1 b1 ofs k p -> perm m2 b2 (ofs + delta) k p.
Admitted.

Theorem valid_access_inject:
  forall f m1 m2 chunk b1 ofs b2 delta p,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  valid_access m1 chunk b1 ofs p ->
  valid_access m2 chunk b2 (ofs + delta) p.
Admitted.

Theorem valid_pointer_inject:
  forall f m1 m2 b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  valid_pointer m1 b1 ofs = true ->
  valid_pointer m2 b2 (ofs + delta) = true.
Admitted.

Theorem weak_valid_pointer_inject:
  forall f m1 m2 b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  weak_valid_pointer m1 b1 ofs = true ->
  weak_valid_pointer m2 b2 (ofs + delta) = true.
Admitted.

Lemma address_inject:
  forall f m1 m2 b1 ofs1 b2 delta p,
  inject f m1 m2 ->
  perm m1 b1 (Ptrofs.unsigned ofs1) Cur p ->
  f b1 = Some (b2, delta) ->
  Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)) = Ptrofs.unsigned ofs1 + delta.
Admitted.

Theorem weak_valid_pointer_inject_no_overflow:
  forall f m1 m2 b ofs b' delta,
  inject f m1 m2 ->
  weak_valid_pointer m1 b (Ptrofs.unsigned ofs) = true ->
  f b = Some(b', delta) ->
  0 <= Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) <= Ptrofs.max_unsigned.
Admitted.

Theorem valid_pointer_inject_no_overflow:
  forall f m1 m2 b ofs b' delta,
  inject f m1 m2 ->
  valid_pointer m1 b (Ptrofs.unsigned ofs) = true ->
  f b = Some(b', delta) ->
  0 <= Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) <= Ptrofs.max_unsigned.
Admitted.

Theorem valid_pointer_inject_val:
  forall f m1 m2 b ofs b' ofs',
  inject f m1 m2 ->
  valid_pointer m1 b (Ptrofs.unsigned ofs) = true ->
  Val.inject f (Vptr b ofs) (Vptr b' ofs') ->
  valid_pointer m2 b' (Ptrofs.unsigned ofs') = true.
Admitted.

Theorem weak_valid_pointer_inject_val:
  forall f m1 m2 b ofs b' ofs',
  inject f m1 m2 ->
  weak_valid_pointer m1 b (Ptrofs.unsigned ofs) = true ->
  Val.inject f (Vptr b ofs) (Vptr b' ofs') ->
  weak_valid_pointer m2 b' (Ptrofs.unsigned ofs') = true.
Admitted.

Theorem inject_no_overlap:
  forall f m1 m2 b1 b2 b1' b2' delta1 delta2 ofs1 ofs2,
  inject f m1 m2 ->
  b1 <> b2 ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  perm m1 b1 ofs1 Max Nonempty ->
  perm m1 b2 ofs2 Max Nonempty ->
  b1' <> b2' \/ ofs1 + delta1 <> ofs2 + delta2.
Admitted.

Theorem different_pointers_inject:
  forall f m m' b1 ofs1 b2 ofs2 b1' delta1 b2' delta2,
  inject f m m' ->
  b1 <> b2 ->
  valid_pointer m b1 (Ptrofs.unsigned ofs1) = true ->
  valid_pointer m b2 (Ptrofs.unsigned ofs2) = true ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  b1' <> b2' \/
  Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta1)) <>
  Ptrofs.unsigned (Ptrofs.add ofs2 (Ptrofs.repr delta2)).
Admitted.

Theorem load_inject:
  forall f m1 m2 chunk b1 ofs b2 delta v1,
  inject f m1 m2 ->
  load chunk m1 b1 ofs = Some v1 ->
  f b1 = Some (b2, delta) ->
  exists v2, load chunk m2 b2 (ofs + delta) = Some v2 /\ Val.inject f v1 v2.
Admitted.

Theorem loadv_inject:
  forall f m1 m2 chunk a1 a2 v1,
  inject f m1 m2 ->
  loadv chunk m1 a1 = Some v1 ->
  Val.inject f a1 a2 ->
  exists v2, loadv chunk m2 a2 = Some v2 /\ Val.inject f v1 v2.
Admitted.

Theorem loadbytes_inject:
  forall f m1 m2 b1 ofs len b2 delta bytes1,
  inject f m1 m2 ->
  loadbytes m1 b1 ofs len = Some bytes1 ->
  f b1 = Some (b2, delta) ->
  exists bytes2, loadbytes m2 b2 (ofs + delta) len = Some bytes2
              /\ list_forall2 (memval_inject f) bytes1 bytes2.
Admitted.

Theorem store_mapped_inject:
  forall f chunk m1 b1 ofs v1 n1 m2 b2 delta v2,
  inject f m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  f b1 = Some (b2, delta) ->
  Val.inject f v1 v2 ->
  exists n2,
    store chunk m2 b2 (ofs + delta) v2 = Some n2
    /\ inject f n1 n2.
Admitted.

Theorem store_unmapped_inject:
  forall f chunk m1 b1 ofs v1 n1 m2,
  inject f m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  f b1 = None ->
  inject f n1 m2.
Admitted.

Theorem store_outside_inject:
  forall f m1 m2 chunk b ofs v m2',
  inject f m1 m2 ->
  (forall b' delta ofs',
    f b' = Some(b, delta) ->
    perm m1 b' ofs' Cur Readable ->
    ofs <= ofs' + delta < ofs + size_chunk chunk -> False) ->
  store chunk m2 b ofs v = Some m2' ->
  inject f m1 m2'.
Admitted.

Theorem storev_mapped_inject:
  forall f chunk m1 a1 v1 n1 m2 a2 v2,
  inject f m1 m2 ->
  storev chunk m1 a1 v1 = Some n1 ->
  Val.inject f a1 a2 ->
  Val.inject f v1 v2 ->
  exists n2,
    storev chunk m2 a2 v2 = Some n2 /\ inject f n1 n2.
Admitted.

Theorem storebytes_mapped_inject:
  forall f m1 b1 ofs bytes1 n1 m2 b2 delta bytes2,
  inject f m1 m2 ->
  storebytes m1 b1 ofs bytes1 = Some n1 ->
  f b1 = Some (b2, delta) ->
  list_forall2 (memval_inject f) bytes1 bytes2 ->
  exists n2,
    storebytes m2 b2 (ofs + delta) bytes2 = Some n2
    /\ inject f n1 n2.
Admitted.

Theorem storebytes_unmapped_inject:
  forall f m1 b1 ofs bytes1 n1 m2,
  inject f m1 m2 ->
  storebytes m1 b1 ofs bytes1 = Some n1 ->
  f b1 = None ->
  inject f n1 m2.
Admitted.

Theorem storebytes_outside_inject:
  forall f m1 m2 b ofs bytes2 m2',
  inject f m1 m2 ->
  (forall b' delta ofs',
    f b' = Some(b, delta) ->
    perm m1 b' ofs' Cur Readable ->
    ofs <= ofs' + delta < ofs + Z.of_nat (length bytes2) -> False) ->
  storebytes m2 b ofs bytes2 = Some m2' ->
  inject f m1 m2'.
Admitted.

Theorem alloc_right_inject:
  forall f m1 m2 lo hi b2 m2',
  inject f m1 m2 ->
  alloc m2 lo hi = (m2', b2) ->
  inject f m1 m2'.
Admitted.

Theorem alloc_left_unmapped_inject:
  forall f m1 m2 lo hi m1' b1,
  inject f m1 m2 ->
  alloc m1 lo hi = (m1', b1) ->
  exists f',
     inject f' m1' m2
  /\ inject_incr f f'
  /\ f' b1 = None
  /\ (forall b, b <> b1 -> f' b = f b).
Admitted.

Theorem alloc_left_mapped_inject:
  forall f m1 m2 lo hi m1' b1 b2 delta,
  inject f m1 m2 ->
  alloc m1 lo hi = (m1', b1) ->
  valid_block m2 b2 ->
  0 <= delta <= Ptrofs.max_unsigned ->
  (forall ofs k p, perm m2 b2 ofs k p -> delta = 0 \/ 0 <= ofs < Ptrofs.max_unsigned) ->
  (forall ofs k p, lo <= ofs < hi -> perm m2 b2 (ofs + delta) k p) ->
  inj_offset_aligned delta (hi-lo) ->
  (forall b delta' ofs k p,
   f b = Some (b2, delta') ->
   perm m1 b ofs k p ->
   lo + delta <= ofs + delta' < hi + delta -> False) ->
  exists f',
     inject f' m1' m2
  /\ inject_incr f f'
  /\ f' b1 = Some(b2, delta)
  /\ (forall b, b <> b1 -> f' b = f b).
Admitted.

Theorem alloc_parallel_inject:
  forall f m1 m2 lo1 hi1 m1' b1 lo2 hi2,
  inject f m1 m2 ->
  alloc m1 lo1 hi1 = (m1', b1) ->
  lo2 <= lo1 -> hi1 <= hi2 ->
  exists f', exists m2', exists b2,
  alloc m2 lo2 hi2 = (m2', b2)
  /\ inject f' m1' m2'
  /\ inject_incr f f'
  /\ f' b1 = Some(b2, 0)
  /\ (forall b, b <> b1 -> f' b = f b).
Admitted.

Theorem free_inject:
  forall f m1 l m1' m2 b lo hi m2',
  inject f m1 m2 ->
  free_list m1 l = Some m1' ->
  free m2 b lo hi = Some m2' ->
  (forall b1 delta ofs k p,
    f b1 = Some(b, delta) ->
    perm m1 b1 ofs k p -> lo <= ofs + delta < hi ->
    exists lo1, exists hi1, In (b1, lo1, hi1) l /\ lo1 <= ofs < hi1) ->
  inject f m1' m2'.
Admitted.

Theorem free_parallel_inject:
  forall f m1 m2 b lo hi m1' b' delta,
  inject f m1 m2 ->
  free m1 b lo hi = Some m1' ->
  f b = Some(b', delta) ->
  exists m2',
     free m2 b' (lo + delta) (hi + delta) = Some m2'
  /\ inject f m1' m2'.
Admitted.

Lemma drop_outside_inject: forall f m1 m2 b lo hi p m2',
  inject f m1 m2 ->
  drop_perm m2 b lo hi p = Some m2' ->
  (forall b' delta ofs k p,
    f b' = Some(b, delta) ->
    perm m1 b' ofs k p -> lo <= ofs + delta < hi -> False) ->
  inject f m1 m2'.
Admitted.
Definition flat_inj (thr: block) : meminj.
exact (fun (b: block) => if plt b thr then Some(b, 0) else None).
Defined.

Definition inject_neutral (thr: block) (m: mem) :=
  mem_inj (flat_inj thr) m m.

Theorem neutral_inject:
  forall m, inject_neutral (nextblock m) m -> inject (flat_inj (nextblock m)) m m.
Admitted.

Theorem empty_inject_neutral:
  forall thr, inject_neutral thr empty.
Admitted.

Theorem alloc_inject_neutral:
  forall thr m lo hi b m',
  alloc m lo hi = (m', b) ->
  inject_neutral thr m ->
  Plt (nextblock m) thr ->
  inject_neutral thr m'.
Admitted.

Theorem store_inject_neutral:
  forall chunk m b ofs v m' thr,
  store chunk m b ofs v = Some m' ->
  inject_neutral thr m ->
  Plt b thr ->
  Val.inject (flat_inj thr) v v ->
  inject_neutral thr m'.
Admitted.

Theorem drop_inject_neutral:
  forall m b lo hi p m' thr,
  drop_perm m b lo hi p = Some m' ->
  inject_neutral thr m ->
  Plt b thr ->
  inject_neutral thr m'.
Admitted.

End Mem.

Notation mem := Mem.mem.
Import compcert.lib.Floats.
Import compcert.cfrontend.Ctypes.

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

Inductive incr_or_decr : Type := Incr | Decr.
Definition sem_cast (v: val) (t1 t2: type) (m: mem): option val.
Admitted.
Definition bool_val (v: val) (t: type) (m: mem) : option bool.
Admitted.
Definition sem_unary_operation
            (op: unary_operation) (v: val) (ty: type) (m: mem): option val.
Admitted.
Definition sem_binary_operation
    (cenv: composite_env)
    (op: binary_operation)
    (v1: val) (t1: type) (v2: val) (t2:type)
    (m: mem): option val.
Admitted.
Definition chunk_for_carrier (sz: intsize) : memory_chunk.
Admitted.
Definition bitsize_carrier (sz: intsize) : Z.
Admitted.
Definition bitfield_extract (sz: intsize) (sg: signedness) (pos width: Z) (c: int) : int.
Admitted.

Inductive load_bitfield: type -> intsize -> signedness -> Z -> Z -> mem -> val -> val -> Prop :=
  | load_bitfield_intro: forall sz sg1 attr sg pos width m addr c,
      0 <= pos -> 0 < width <= bitsize_intsize sz -> pos + width <= bitsize_carrier sz ->
      sg1 = (if zlt width (bitsize_intsize sz) then Signed else sg) ->
      Mem.loadv (chunk_for_carrier sz) m addr = Some (Vint c) ->
      load_bitfield (Tint sz sg1 attr) sz sg pos width m addr
                    (Vint (bitfield_extract sz sg pos width c)).

Module Export compcert_DOT_cfrontend_DOT_Csyntax_WRAPPED.
Module Export Csyntax.

Inductive expr : Type :=
  | Eval (v: val) (ty: type)
  | Evar (x: ident) (ty: type)
  | Efield (l: expr) (f: ident) (ty: type)

  | Evalof (l: expr) (ty: type)
  | Ederef (r: expr) (ty: type)
  | Eaddrof (l: expr) (ty: type)
  | Eunop (op: unary_operation) (r: expr) (ty: type)

  | Ebinop (op: binary_operation) (r1 r2: expr) (ty: type)

  | Ecast (r: expr) (ty: type)
  | Eseqand (r1 r2: expr) (ty: type)
  | Eseqor (r1 r2: expr) (ty: type)
  | Econdition (r1 r2 r3: expr) (ty: type)
  | Esizeof (ty': type) (ty: type)
  | Ealignof (ty': type) (ty: type)
  | Eassign (l: expr) (r: expr) (ty: type)
  | Eassignop (op: binary_operation) (l: expr) (r: expr) (tyres ty: type)

  | Epostincr (id: incr_or_decr) (l: expr) (ty: type)

  | Ecomma (r1 r2: expr) (ty: type)
  | Ecall (r1: expr) (rargs: exprlist) (ty: type)

  | Ebuiltin (ef: external_function) (tyargs: typelist) (rargs: exprlist) (ty: type)

  | Eloc (b: block) (ofs: ptrofs) (bf: bitfield) (ty: type)

  | Eparen (r: expr) (tycast: type) (ty: type)

with exprlist : Type :=
  | Enil
  | Econs (r1: expr) (rl: exprlist).
Definition typeof (a: expr) : type.
Admitted.

Definition label := ident.

Inductive statement : Type :=
  | Sskip : statement
  | Sdo : expr -> statement
  | Ssequence : statement -> statement -> statement
  | Sifthenelse : expr  -> statement -> statement -> statement
  | Swhile : expr -> statement -> statement
  | Sdowhile : expr -> statement -> statement
  | Sfor: statement -> expr -> statement -> statement -> statement
  | Sbreak : statement
  | Scontinue : statement
  | Sreturn : option expr -> statement
  | Sswitch : expr -> labeled_statements -> statement
  | Slabel : label -> statement -> statement
  | Sgoto : label -> statement

with labeled_statements : Type :=
  | LSnil: labeled_statements
  | LScons: option Z -> statement -> labeled_statements -> labeled_statements.

Record function : Type := mkfunction {
  fn_return: type;
  fn_callconv: calling_convention;
  fn_params: list (ident * type);
  fn_vars: list (ident * type);
  fn_body: statement
}.

Definition fundef := Ctypes.fundef function.
Definition type_of_fundef (f: fundef) : type.
Admitted.

Definition program := Ctypes.program function.

End Csyntax.
Module Export compcert.
Module Export cfrontend.
Module Export Csyntax.
Include compcert_DOT_cfrontend_DOT_Csyntax_WRAPPED.Csyntax.
End Csyntax.
Import compcert.common.AST.

Set Implicit Arguments.

Module Export Senv.

Record t: Type := mksenv {

  find_symbol: ident -> option block;
  public_symbol: ident -> bool;
  invert_symbol: block -> option ident;
  block_is_volatile: block -> bool;
  nextblock: block;

  find_symbol_injective:
    forall id1 id2 b, find_symbol id1 = Some b -> find_symbol id2 = Some b -> id1 = id2;
  invert_find_symbol:
    forall id b, invert_symbol b = Some id -> find_symbol id = Some b;
  find_invert_symbol:
    forall id b, find_symbol id = Some b -> invert_symbol b = Some id;
  public_symbol_exists:
    forall id, public_symbol id = true -> exists b, find_symbol id = Some b;
  find_symbol_below:
    forall id b, find_symbol id = Some b -> Plt b nextblock;
  block_is_volatile_below:
    forall b, block_is_volatile b = true -> Plt b nextblock
}.

Module Export Genv.

Section GENV.

Variable F: Type.

Variable V: Type.

Record t: Type := mkgenv {
  genv_public: list ident;
  genv_symb: PTree.t block;
  genv_defs: PTree.t (globdef F V);
  genv_next: block;
  genv_symb_range: forall id b, PTree.get id genv_symb = Some b -> Plt b genv_next;
  genv_defs_range: forall b g, PTree.get b genv_defs = Some g -> Plt b genv_next;
  genv_vars_inj: forall id1 id2 b,
    PTree.get id1 genv_symb = Some b -> PTree.get id2 genv_symb = Some b -> id1 = id2
}.
Definition find_symbol (ge: t) (id: ident) : option block.
Admitted.
Definition symbol_address (ge: t) (id: ident) (ofs: ptrofs) : val.
Admitted.
Definition find_funct_ptr (ge: t) (b: block) : option F.
Admitted.
Definition add_globals (ge: t) (gl: list (ident * globdef F V)) : t.
Admitted.

Program Definition empty_genv (pub: list ident): t :=
  @mkgenv pub (PTree.empty _) (PTree.empty _) 1%positive _ _ _.

Definition globalenv (p: program F V) :=
  add_globals (empty_genv p.(prog_public)) p.(prog_defs).

Definition to_senv (ge: t) : Senv.t.
Admitted.

Section INITMEM.

Variable ge: t.
Fixpoint alloc_globals (m: mem) (gl: list (ident * globdef F V))
                       {struct gl} : option mem.
Admitted.

End INITMEM.

Definition init_mem (p: program F V) :=
  alloc_globals (globalenv p) Mem.empty p.(prog_defs).

End GENV.

End Genv.

Coercion Genv.to_senv: Genv.t >-> Senv.t.

Inductive eventval: Type :=
  | EVint: int -> eventval
  | EVlong: int64 -> eventval
  | EVfloat: float -> eventval
  | EVsingle: float32 -> eventval
  | EVptr_global: ident -> ptrofs -> eventval.

Inductive event: Type :=
  | Event_syscall: string -> list eventval -> eventval -> event
  | Event_vload: memory_chunk -> ident -> ptrofs -> eventval -> event
  | Event_vstore: memory_chunk -> ident -> ptrofs -> eventval -> event
  | Event_annot: string -> list eventval -> event.

Definition trace := list event.
Definition E0 : trace.
Admitted.
Definition Eapp (t1 t2: trace) : trace.
Admitted.

Infix "**" := Eapp (at level 60, right associativity).

Definition extcall_sem : Type.
exact (Senv.t -> list val -> mem -> trace -> val -> mem -> Prop).
Defined.
Definition external_call (ef: external_function): extcall_sem.
Admitted.

Section EVAL_BUILTIN_ARG.

Variable A: Type.
Variable ge: Senv.t.
Variable e: A -> val.
Variable sp: val.
Variable m: mem.
Definition eval_builtin_args (al: list (builtin_arg A)) (vl: list val) : Prop.
Admitted.

End EVAL_BUILTIN_ARG.

Section CLOSURES.

Variable genv: Type.
Variable state: Type.

Variable step: genv -> state -> trace -> state -> Prop.

Inductive star (ge: genv): state -> trace -> state -> Prop :=
  | star_refl: forall s,
      star ge s E0 s
  | star_step: forall s1 t1 s2 t2 s3 t,
      step ge s1 t1 s2 -> star ge s2 t2 s3 -> t = t1 ** t2 ->
      star ge s1 t s3.

Inductive plus (ge: genv): state -> trace -> state -> Prop :=
  | plus_left: forall s1 t1 s2 t2 s3 t,
      step ge s1 t1 s2 -> star ge s2 t2 s3 -> t = t1 ** t2 ->
      plus ge s1 t s3.

End CLOSURES.

Record semantics : Type := Semantics_gen {
  state: Type;
  genvtype: Type;
  step : genvtype -> state -> trace -> state -> Prop;
  initial_state: state -> Prop;
  final_state: state -> int -> Prop;
  globalenv: genvtype;
  symbolenv: Senv.t
}.

Definition Semantics {state funtype vartype: Type}
                     (step: Genv.t funtype vartype -> state -> trace -> state -> Prop)
                     (initial_state: state -> Prop)
                     (final_state: state -> int -> Prop)
                     (globalenv: Genv.t funtype vartype) :=
  {| state := state;
     genvtype := Genv.t funtype vartype;
     step := step;
     initial_state := initial_state;
     final_state := final_state;
     globalenv := globalenv;
     symbolenv := Genv.to_senv globalenv |}.

Notation " 'Step' L " := (step L (globalenv L)) (at level 1) : smallstep_scope.
Notation " 'Star' L " := (star (step L) (globalenv L)) (at level 1) : smallstep_scope.
Notation " 'Plus' L " := (plus (step L) (globalenv L)) (at level 1) : smallstep_scope.
Open Scope smallstep_scope.

Definition safe (L: semantics) (s: state L) : Prop.
Admitted.

Record bsim_properties (L1 L2: semantics) (index: Type)
                       (order: index -> index -> Prop)
                       (match_states: index -> state L1 -> state L2 -> Prop) : Prop := {
    bsim_order_wf: well_founded order;
    bsim_initial_states_exist:
      forall s1, initial_state L1 s1 -> exists s2, initial_state L2 s2;
    bsim_match_initial_states:
      forall s1 s2, initial_state L1 s1 -> initial_state L2 s2 ->
      exists i, exists s1', initial_state L1 s1' /\ match_states i s1' s2;
    bsim_match_final_states:
      forall i s1 s2 r,
      match_states i s1 s2 -> safe L1 s1 -> final_state L2 s2 r ->
      exists s1', Star L1 s1 E0 s1' /\ final_state L1 s1' r;
    bsim_progress:
      forall i s1 s2,
      match_states i s1 s2 -> safe L1 s1 ->
      (exists r, final_state L2 s2 r) \/
      (exists t, exists s2', Step L2 s2 t s2');
    bsim_simulation:
      forall s2 t s2', Step L2 s2 t s2' ->
      forall i s1, match_states i s1 s2 -> safe L1 s1 ->
      exists i', exists s1',
         (Plus L1 s1 t s1' \/ (Star L1 s1 t s1' /\ order i' i))
      /\ match_states i' s1' s2';
    bsim_public_preserved:
      forall id, Senv.public_symbol (symbolenv L2) id = Senv.public_symbol (symbolenv L1) id
  }.

Arguments bsim_properties: clear implicits.

Inductive backward_simulation (L1 L2: semantics) : Prop :=
  Backward_simulation (index: Type)
                      (order: index -> index -> Prop)
                      (match_states: index -> state L1 -> state L2 -> Prop)
                      (props: bsim_properties L1 L2 index order match_states).

Module Export Csem.
Import compcert.cfrontend.Ctypes.
Import compcert.cfrontend.Csyntax.

Record genv := { genv_genv :> Genv.t fundef type; genv_cenv :> composite_env }.

Definition globalenv (p: program) :=
  {| genv_genv := Genv.globalenv p; genv_cenv := p.(prog_comp_env) |}.

Definition env := PTree.t (block * type).

Section SEMANTICS.

Variable ge: genv.

Inductive cont: Type :=
  | Kstop: cont
  | Kdo: cont -> cont
  | Kseq: statement -> cont -> cont
  | Kifthenelse: statement -> statement -> cont -> cont
  | Kwhile1: expr -> statement -> cont -> cont
  | Kwhile2: expr -> statement -> cont -> cont
  | Kdowhile1: expr -> statement -> cont -> cont
  | Kdowhile2: expr -> statement -> cont -> cont
  | Kfor2: expr -> statement -> statement -> cont -> cont
  | Kfor3: expr -> statement -> statement -> cont -> cont
  | Kfor4: expr -> statement -> statement -> cont -> cont
  | Kswitch1: labeled_statements -> cont -> cont
  | Kswitch2: cont -> cont
  | Kreturn: cont -> cont
  | Kcall: function ->
           env ->
           (expr -> expr) ->
           type ->
           cont -> cont.

Inductive state: Type :=
  | State
      (f: function)
      (s: statement)
      (k: cont)
      (e: env)
      (m: mem) : state
  | ExprState
      (f: function)
      (r: expr)
      (k: cont)
      (e: env)
      (m: mem) : state
  | Callstate
      (fd: fundef)
      (args: list val)
      (k: cont)
      (m: mem) : state
  | Returnstate
      (res: val)
      (k: cont)
      (m: mem) : state
  | Stuckstate.
Definition step (S: state) (t: trace) (S': state) : Prop.
Admitted.

End SEMANTICS.

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall b f m0,
      let ge := globalenv p in
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      type_of_fundef f = Tfunction Tnil type_int32s cc_default ->
      initial_state p (Callstate f nil Kstop m0).

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall r m,
      final_state (Returnstate (Vint r) Kstop m) r.

Definition semantics (p: program) :=
  Semantics_gen step (initial_state p) final_state (globalenv p) (globalenv p).

Module Export compcert_DOT_cfrontend_DOT_Clight_WRAPPED.
Module Export Clight.
Import compcert.common.Errors.

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
Definition typeof (e: expr) : type.
Admitted.

Inductive statement : Type :=
  | Sskip : statement
  | Sassign : expr -> expr -> statement
  | Sset : ident -> expr -> statement
  | Scall: option ident -> expr -> list expr -> statement
  | Sbuiltin: option ident -> external_function -> typelist -> list expr -> statement
  | Ssequence : statement -> statement -> statement
  | Sifthenelse : expr  -> statement -> statement -> statement
  | Sloop: statement -> statement -> statement
  | Sbreak : statement
  | Scontinue : statement
  | Sreturn : option expr -> statement
  | Sswitch : expr -> labeled_statements -> statement
  | Slabel : label -> statement -> statement
  | Sgoto : label -> statement

with labeled_statements : Type :=
  | LSnil: labeled_statements
  | LScons: option Z -> statement -> labeled_statements -> labeled_statements.

Record function : Type := mkfunction {
  fn_return: type;
  fn_callconv: calling_convention;
  fn_params: list (ident * type);
  fn_vars: list (ident * type);
  fn_temps: list (ident * type);
  fn_body: statement
}.

Definition fundef := Ctypes.fundef function.

Definition program := Ctypes.program function.

Definition temp_env := PTree.t val.

Inductive deref_loc (ty: type) (m: mem) (b: block) (ofs: ptrofs) :
                                             bitfield -> val -> Prop :=
  | deref_loc_value: forall chunk v,
      access_mode ty = By_value chunk ->
      Mem.loadv chunk m (Vptr b ofs) = Some v ->
      deref_loc ty m b ofs Full v
  | deref_loc_reference:
      access_mode ty = By_reference ->
      deref_loc ty m b ofs Full (Vptr b ofs)
  | deref_loc_copy:
      access_mode ty = By_copy ->
      deref_loc ty m b ofs Full (Vptr b ofs)
  | deref_loc_bitfield: forall sz sg pos width v,
      load_bitfield ty sz sg pos width m (Vptr b ofs) v ->
      deref_loc ty m b ofs (Bits sz sg pos width) v.

Section SEMANTICS.

Variable ge: genv.

Section EXPR.

Variable e: env.
Variable le: temp_env.
Variable m: mem.

Inductive eval_expr: expr -> val -> Prop :=
  | eval_Econst_int:   forall i ty,
      eval_expr (Econst_int i ty) (Vint i)
  | eval_Econst_float:   forall f ty,
      eval_expr (Econst_float f ty) (Vfloat f)
  | eval_Econst_single:   forall f ty,
      eval_expr (Econst_single f ty) (Vsingle f)
  | eval_Econst_long:   forall i ty,
      eval_expr (Econst_long i ty) (Vlong i)
  | eval_Etempvar:  forall id ty v,
      le!id = Some v ->
      eval_expr (Etempvar id ty) v
  | eval_Eaddrof: forall a ty loc ofs,
      eval_lvalue a loc ofs Full ->
      eval_expr (Eaddrof a ty) (Vptr loc ofs)
  | eval_Eunop:  forall op a ty v1 v,
      eval_expr a v1 ->
      sem_unary_operation op v1 (typeof a) m = Some v ->
      eval_expr (Eunop op a ty) v
  | eval_Ebinop: forall op a1 a2 ty v1 v2 v,
      eval_expr a1 v1 ->
      eval_expr a2 v2 ->
      sem_binary_operation ge op v1 (typeof a1) v2 (typeof a2) m = Some v ->
      eval_expr (Ebinop op a1 a2 ty) v
  | eval_Ecast:   forall a ty v1 v,
      eval_expr a v1 ->
      sem_cast v1 (typeof a) ty m = Some v ->
      eval_expr (Ecast a ty) v
  | eval_Esizeof: forall ty1 ty,
      eval_expr (Esizeof ty1 ty) (Vptrofs (Ptrofs.repr (sizeof ge ty1)))
  | eval_Ealignof: forall ty1 ty,
      eval_expr (Ealignof ty1 ty) (Vptrofs (Ptrofs.repr (alignof ge ty1)))
  | eval_Elvalue: forall a loc ofs bf v,
      eval_lvalue a loc ofs bf ->
      deref_loc (typeof a) m loc ofs bf v ->
      eval_expr a v

with eval_lvalue: expr -> block -> ptrofs -> bitfield -> Prop :=
  | eval_Evar_local:   forall id l ty,
      e!id = Some(l, ty) ->
      eval_lvalue (Evar id ty) l Ptrofs.zero Full
  | eval_Evar_global: forall id l ty,
      e!id = None ->
      Genv.find_symbol ge id = Some l ->
      eval_lvalue (Evar id ty) l Ptrofs.zero Full
  | eval_Ederef: forall a ty l ofs,
      eval_expr a (Vptr l ofs) ->
      eval_lvalue (Ederef a ty) l ofs Full
 | eval_Efield_struct:   forall a i ty l ofs id co att delta bf,
      eval_expr a (Vptr l ofs) ->
      typeof a = Tstruct id att ->
      ge.(genv_cenv)!id = Some co ->
      field_offset ge i (co_members co) = OK (delta, bf) ->
      eval_lvalue (Efield a i ty) l (Ptrofs.add ofs (Ptrofs.repr delta)) bf
 | eval_Efield_union:   forall a i ty l ofs id co att delta bf,
      eval_expr a (Vptr l ofs) ->
      typeof a = Tunion id att ->
      ge.(genv_cenv)!id = Some co ->
      union_field_offset ge i (co_members co) = OK (delta, bf) ->
      eval_lvalue (Efield a i ty) l (Ptrofs.add ofs (Ptrofs.repr delta)) bf.

End EXPR.

End SEMANTICS.

End Clight.
Module Export compcert.
Module Export cfrontend.
Module Export Clight.
Include compcert_DOT_cfrontend_DOT_Clight_WRAPPED.Clight.
End Clight.
Definition makeseq (l: list statement) : statement.
Admitted.

Section SIMPL_EXPR.
Fixpoint eval_simpl_expr (a: expr) : option val.
Admitted.

Function makeif (a: expr) (s1 s2: statement) : statement :=
  match eval_simpl_expr a with
  | Some v =>
      match bool_val v (typeof a) Mem.empty with
      | Some b => if b then s1 else s2
      | None   => Sifthenelse a s1 s2
      end
  | None => Sifthenelse a s1 s2
  end.
Definition Ederef' (a: expr) (t: type) : expr.
Admitted.
Definition Eaddrof' (a: expr) (t: type) : expr.
Admitted.
Definition transl_incrdecr (id: incr_or_decr) (a: expr) (ty: type) : expr.
Admitted.
Definition make_set (bf: bitfield) (id: ident) (l: expr) : statement.
Admitted.
Definition make_assign (bf: bitfield) (l r: expr) : statement.
Admitted.
Definition make_assign_value (bf: bitfield) (r: expr): expr.
Admitted.

Inductive set_destination : Type :=
  | SDbase (tycast ty: type) (tmp: ident)
  | SDcons (tycast ty: type) (tmp: ident) (sd: set_destination).

Inductive destination : Type :=
  | For_val
  | For_effects
  | For_set (sd: set_destination).
Fixpoint do_set (sd: set_destination) (a: expr) : list statement.
Admitted.

End SIMPL_EXPR.
Import compcert.common.Errors.

Section SPEC.

Variable ce: composite_env.
Definition final (dst: destination) (a: expr) : list statement.
Admitted.
Definition tr_is_bitfield_access (l: expr) (bf: bitfield) : Prop.
Admitted.

Inductive tr_rvalof: type -> expr -> list statement -> expr -> list ident -> Prop :=
  | tr_rvalof_nonvol: forall ty a tmp,
      type_is_volatile ty = false ->
      tr_rvalof ty a nil a tmp
  | tr_rvalof_vol: forall ty a t bf tmp,
      type_is_volatile ty = true -> In t tmp ->
      tr_is_bitfield_access a bf ->
      tr_rvalof ty a (make_set bf t a :: nil) (Etempvar t ty) tmp.

Inductive tr_expr: temp_env -> destination -> Csyntax.expr -> list statement -> expr -> list ident -> Prop :=
  | tr_var: forall le dst id ty tmp,
      tr_expr le dst (Csyntax.Evar id ty)
              (final dst (Evar id ty)) (Evar id ty) tmp
  | tr_deref: forall le dst e1 ty sl1 a1 tmp,
      tr_expr le For_val e1 sl1 a1 tmp ->
      tr_expr le dst (Csyntax.Ederef e1 ty)
              (sl1 ++ final dst (Ederef' a1 ty)) (Ederef' a1 ty) tmp
  | tr_field: forall le dst e1 f ty sl1 a1 tmp,
      tr_expr le For_val e1 sl1 a1 tmp ->
      tr_expr le dst (Csyntax.Efield e1 f ty)
              (sl1 ++ final dst (Efield a1 f ty)) (Efield a1 f ty) tmp
  | tr_val_effect: forall le v ty any tmp,
      tr_expr le For_effects (Csyntax.Eval v ty) nil any tmp
  | tr_val_value: forall le v ty a tmp,
      typeof a = ty ->
      (forall tge e le' m,
         (forall id, In id tmp -> le'!id = le!id) ->
         eval_expr tge e le' m a v) ->
      tr_expr le For_val (Csyntax.Eval v ty)
                           nil a tmp
  | tr_val_set: forall le sd v ty a any tmp,
      typeof a = ty ->
      (forall tge e le' m,
         (forall id, In id tmp -> le'!id = le!id) ->
         eval_expr tge e le' m a v) ->
      tr_expr le (For_set sd) (Csyntax.Eval v ty)
                   (do_set sd a) any tmp
  | tr_sizeof: forall le dst ty' ty tmp,
      tr_expr le dst (Csyntax.Esizeof ty' ty)
                   (final dst (Esizeof ty' ty))
                   (Esizeof ty' ty) tmp
  | tr_alignof: forall le dst ty' ty tmp,
      tr_expr le dst (Csyntax.Ealignof ty' ty)
                   (final dst (Ealignof ty' ty))
                   (Ealignof ty' ty) tmp
  | tr_valof: forall le dst e1 ty tmp sl1 a1 tmp1 sl2 a2 tmp2,
      tr_expr le For_val e1 sl1 a1 tmp1 ->
      tr_rvalof (Csyntax.typeof e1) a1 sl2 a2 tmp2 ->
      list_disjoint tmp1 tmp2 -> incl tmp1 tmp -> incl tmp2 tmp ->
      tr_expr le dst (Csyntax.Evalof e1 ty)
                    (sl1 ++ sl2 ++ final dst a2)
                    a2 tmp
  | tr_addrof: forall le dst e1 ty tmp sl1 a1,
      tr_expr le For_val e1 sl1 a1 tmp ->
      tr_expr le dst (Csyntax.Eaddrof e1 ty)
                   (sl1 ++ final dst (Eaddrof' a1 ty))
                   (Eaddrof' a1 ty) tmp
  | tr_unop: forall le dst op e1 ty tmp sl1 a1,
      tr_expr le For_val e1 sl1 a1 tmp ->
      tr_expr le dst (Csyntax.Eunop op e1 ty)
                   (sl1 ++ final dst (Eunop op a1 ty))
                   (Eunop op a1 ty) tmp
  | tr_binop: forall le dst op e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 tmp,
      tr_expr le For_val e1 sl1 a1 tmp1 ->
      tr_expr le For_val e2 sl2 a2 tmp2 ->
      list_disjoint tmp1 tmp2 -> incl tmp1 tmp -> incl tmp2 tmp ->
      tr_expr le dst (Csyntax.Ebinop op e1 e2 ty)
                   (sl1 ++ sl2 ++ final dst (Ebinop op a1 a2 ty))
                   (Ebinop op a1 a2 ty) tmp
  | tr_cast_effects: forall le e1 ty sl1 a1 any tmp,
      tr_expr le For_effects e1 sl1 a1 tmp ->
      tr_expr le For_effects (Csyntax.Ecast e1 ty)
                   sl1
                   any tmp
  | tr_cast_val: forall le dst e1 ty sl1 a1 tmp,
      tr_expr le For_val e1 sl1 a1 tmp ->
      tr_expr le dst (Csyntax.Ecast e1 ty)
                   (sl1 ++ final dst (Ecast a1 ty))
                   (Ecast a1 ty) tmp
  | tr_seqand_val: forall le e1 e2 ty sl1 a1 tmp1 t sl2 a2 tmp2 tmp,
      tr_expr le For_val e1 sl1 a1 tmp1 ->
      tr_expr le (For_set (SDbase type_bool ty t)) e2 sl2 a2 tmp2 ->
      list_disjoint tmp1 tmp2 ->
      incl tmp1 tmp -> incl tmp2 tmp -> In t tmp ->
      tr_expr le For_val (Csyntax.Eseqand e1 e2 ty)
                    (sl1 ++ makeif a1 (makeseq sl2)
                                      (Sset t (Econst_int Int.zero ty)) :: nil)
                    (Etempvar t ty) tmp
  | tr_seqand_effects: forall le e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 any tmp,
      tr_expr le For_val e1 sl1 a1 tmp1 ->
      tr_expr le For_effects e2 sl2 a2 tmp2 ->
      list_disjoint tmp1 tmp2 ->
      incl tmp1 tmp -> incl tmp2 tmp ->
      tr_expr le For_effects (Csyntax.Eseqand e1 e2 ty)
                    (sl1 ++ makeif a1 (makeseq sl2) Sskip :: nil)
                    any tmp
  | tr_seqand_set: forall le sd e1 e2 ty sl1 a1 tmp1 t sl2 a2 tmp2 any tmp,
      tr_expr le For_val e1 sl1 a1 tmp1 ->
      tr_expr le (For_set (SDcons type_bool ty t sd)) e2 sl2 a2 tmp2 ->
      list_disjoint tmp1 tmp2 ->
      incl tmp1 tmp -> incl tmp2 tmp -> In t tmp ->
      tr_expr le (For_set sd) (Csyntax.Eseqand e1 e2 ty)
                    (sl1 ++ makeif a1 (makeseq sl2)
                                      (makeseq (do_set sd (Econst_int Int.zero ty))) :: nil)
                    any tmp
  | tr_seqor_val: forall le e1 e2 ty sl1 a1 tmp1 t sl2 a2 tmp2 tmp,
      tr_expr le For_val e1 sl1 a1 tmp1 ->
      tr_expr le (For_set (SDbase type_bool ty t)) e2 sl2 a2 tmp2 ->
      list_disjoint tmp1 tmp2 ->
      incl tmp1 tmp -> incl tmp2 tmp -> In t tmp ->
      tr_expr le For_val (Csyntax.Eseqor e1 e2 ty)
                    (sl1 ++ makeif a1 (Sset t (Econst_int Int.one ty))
                                      (makeseq sl2) :: nil)
                    (Etempvar t ty) tmp
  | tr_seqor_effects: forall le e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 any tmp,
      tr_expr le For_val e1 sl1 a1 tmp1 ->
      tr_expr le For_effects e2 sl2 a2 tmp2 ->
      list_disjoint tmp1 tmp2 ->
      incl tmp1 tmp -> incl tmp2 tmp ->
      tr_expr le For_effects (Csyntax.Eseqor e1 e2 ty)
                    (sl1 ++ makeif a1 Sskip (makeseq sl2) :: nil)
                    any tmp
  | tr_seqor_set: forall le sd e1 e2 ty sl1 a1 tmp1 t sl2 a2 tmp2 any tmp,
      tr_expr le For_val e1 sl1 a1 tmp1 ->
      tr_expr le (For_set (SDcons type_bool ty t sd)) e2 sl2 a2 tmp2 ->
      list_disjoint tmp1 tmp2 ->
      incl tmp1 tmp -> incl tmp2 tmp -> In t tmp ->
      tr_expr le (For_set sd) (Csyntax.Eseqor e1 e2 ty)
                    (sl1 ++ makeif a1 (makeseq (do_set sd (Econst_int Int.one ty)))
                                      (makeseq sl2) :: nil)
                    any tmp
  | tr_condition_val: forall le e1 e2 e3 ty sl1 a1 tmp1 sl2 a2 tmp2 sl3 a3 tmp3 t tmp,
      tr_expr le For_val e1 sl1 a1 tmp1 ->
      tr_expr le (For_set (SDbase ty ty t)) e2 sl2 a2 tmp2 ->
      tr_expr le (For_set (SDbase ty ty t)) e3 sl3 a3 tmp3 ->
      list_disjoint tmp1 tmp2 ->
      list_disjoint tmp1 tmp3 ->
      incl tmp1 tmp -> incl tmp2 tmp ->  incl tmp3 tmp -> In t tmp ->
      tr_expr le For_val (Csyntax.Econdition e1 e2 e3 ty)
                      (sl1 ++ makeif a1 (makeseq sl2) (makeseq sl3) :: nil)
                      (Etempvar t ty) tmp
  | tr_condition_effects: forall le e1 e2 e3 ty sl1 a1 tmp1 sl2 a2 tmp2 sl3 a3 tmp3 any tmp,
      tr_expr le For_val e1 sl1 a1 tmp1 ->
      tr_expr le For_effects e2 sl2 a2 tmp2 ->
      tr_expr le For_effects e3 sl3 a3 tmp3 ->
      list_disjoint tmp1 tmp2 ->
      list_disjoint tmp1 tmp3 ->
      incl tmp1 tmp -> incl tmp2 tmp -> incl tmp3 tmp ->
      tr_expr le For_effects (Csyntax.Econdition e1 e2 e3 ty)
                       (sl1 ++ makeif a1 (makeseq sl2) (makeseq sl3) :: nil)
                       any tmp
  | tr_condition_set: forall le sd t e1 e2 e3 ty sl1 a1 tmp1 sl2 a2 tmp2 sl3 a3 tmp3 any tmp,
      tr_expr le For_val e1 sl1 a1 tmp1 ->
      tr_expr le (For_set (SDcons ty ty t sd)) e2 sl2 a2 tmp2 ->
      tr_expr le (For_set (SDcons ty ty t sd)) e3 sl3 a3 tmp3 ->
      list_disjoint tmp1 tmp2 ->
      list_disjoint tmp1 tmp3 ->
      incl tmp1 tmp -> incl tmp2 tmp -> incl tmp3 tmp -> In t tmp ->
      tr_expr le (For_set sd) (Csyntax.Econdition e1 e2 e3 ty)
                       (sl1 ++ makeif a1 (makeseq sl2) (makeseq sl3) :: nil)
                       any tmp
  | tr_assign_effects: forall le e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 bf any tmp,
      tr_expr le For_val e1 sl1 a1 tmp1 ->
      tr_expr le For_val e2 sl2 a2 tmp2 ->
      list_disjoint tmp1 tmp2 ->
      incl tmp1 tmp -> incl tmp2 tmp ->
      tr_is_bitfield_access a1 bf ->
      tr_expr le For_effects (Csyntax.Eassign e1 e2 ty)
                      (sl1 ++ sl2 ++ make_assign bf a1 a2 :: nil)
                      any tmp
  | tr_assign_val: forall le dst e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 t tmp ty1 ty2 bf,
      tr_expr le For_val e1 sl1 a1 tmp1 ->
      tr_expr le For_val e2 sl2 a2 tmp2 ->
      incl tmp1 tmp -> incl tmp2 tmp ->
      list_disjoint tmp1 tmp2 ->
      In t tmp -> ~In t tmp1 -> ~In t tmp2 ->
      ty1 = Csyntax.typeof e1 ->
      ty2 = Csyntax.typeof e2 ->
      tr_is_bitfield_access a1 bf ->
      tr_expr le dst (Csyntax.Eassign e1 e2 ty)
                   (sl1 ++ sl2 ++
                    Sset t (Ecast a2 ty1) ::
                    make_assign bf a1 (Etempvar t ty1) ::
                    final dst (make_assign_value bf (Etempvar t ty1)))
                   (make_assign_value bf (Etempvar t ty1)) tmp
  | tr_assignop_effects: forall le op e1 e2 tyres ty ty1 sl1 a1 tmp1 sl2 a2 tmp2 bf sl3 a3 tmp3 any tmp,
      tr_expr le For_val e1 sl1 a1 tmp1 ->
      tr_expr le For_val e2 sl2 a2 tmp2 ->
      ty1 = Csyntax.typeof e1 ->
      tr_rvalof ty1 a1 sl3 a3 tmp3 ->
      list_disjoint tmp1 tmp2 -> list_disjoint tmp1 tmp3 -> list_disjoint tmp2 tmp3 ->
      incl tmp1 tmp -> incl tmp2 tmp -> incl tmp3 tmp ->
      tr_is_bitfield_access a1 bf ->
      tr_expr le For_effects (Csyntax.Eassignop op e1 e2 tyres ty)
                      (sl1 ++ sl2 ++ sl3 ++ make_assign bf a1 (Ebinop op a3 a2 tyres) :: nil)
                      any tmp
  | tr_assignop_val: forall le dst op e1 e2 tyres ty sl1 a1 tmp1 sl2 a2 tmp2 sl3 a3 tmp3 t bf tmp ty1,
      tr_expr le For_val e1 sl1 a1 tmp1 ->
      tr_expr le For_val e2 sl2 a2 tmp2 ->
      tr_rvalof ty1 a1 sl3 a3 tmp3 ->
      list_disjoint tmp1 tmp2 -> list_disjoint tmp1 tmp3 -> list_disjoint tmp2 tmp3 ->
      incl tmp1 tmp -> incl tmp2 tmp -> incl tmp3 tmp ->
      In t tmp -> ~In t tmp1 -> ~In t tmp2 -> ~In t tmp3 ->
      ty1 = Csyntax.typeof e1 ->
      tr_is_bitfield_access a1 bf ->
      tr_expr le dst (Csyntax.Eassignop op e1 e2 tyres ty)
                   (sl1 ++ sl2 ++ sl3 ++
                    Sset t (Ecast (Ebinop op a3 a2 tyres) ty1) ::
                    make_assign bf a1 (Etempvar t ty1) ::
                    final dst (make_assign_value bf (Etempvar t ty1)))
                   (make_assign_value bf (Etempvar t ty1)) tmp
  | tr_postincr_effects: forall le id e1 ty ty1 sl1 a1 tmp1 sl2 a2 tmp2 bf any tmp,
      tr_expr le For_val e1 sl1 a1 tmp1 ->
      tr_rvalof ty1 a1 sl2 a2 tmp2 ->
      ty1 = Csyntax.typeof e1 ->
      incl tmp1 tmp -> incl tmp2 tmp ->
      list_disjoint tmp1 tmp2 ->
      tr_is_bitfield_access a1 bf ->
      tr_expr le For_effects (Csyntax.Epostincr id e1 ty)
                      (sl1 ++ sl2 ++ make_assign bf a1 (transl_incrdecr id a2 ty1) :: nil)
                      any tmp
  | tr_postincr_val: forall le dst id e1 ty sl1 a1 tmp1 bf t ty1 tmp,
      tr_expr le For_val e1 sl1 a1 tmp1 ->
      incl tmp1 tmp -> In t tmp -> ~In t tmp1 ->
      ty1 = Csyntax.typeof e1 ->
      tr_is_bitfield_access a1 bf ->
      tr_expr le dst (Csyntax.Epostincr id e1 ty)
                   (sl1 ++ make_set bf t a1 ::
                    make_assign bf a1 (transl_incrdecr id (Etempvar t ty1) ty1) ::
                    final dst (Etempvar t ty1))
                   (Etempvar t ty1) tmp
  | tr_comma: forall le dst e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 tmp,
      tr_expr le For_effects e1 sl1 a1 tmp1 ->
      tr_expr le dst e2 sl2 a2 tmp2 ->
      list_disjoint tmp1 tmp2 ->
      incl tmp1 tmp -> incl tmp2 tmp ->
      tr_expr le dst (Csyntax.Ecomma e1 e2 ty) (sl1 ++ sl2) a2 tmp
  | tr_call_effects: forall le e1 el2 ty sl1 a1 tmp1 sl2 al2 tmp2 any tmp,
      tr_expr le For_val e1 sl1 a1 tmp1 ->
      tr_exprlist le el2 sl2 al2 tmp2 ->
      list_disjoint tmp1 tmp2 ->
      incl tmp1 tmp -> incl tmp2 tmp ->
      tr_expr le For_effects (Csyntax.Ecall e1 el2 ty)
                   (sl1 ++ sl2 ++ Scall None a1 al2 :: nil)
                   any tmp
  | tr_call_val: forall le dst e1 el2 ty sl1 a1 tmp1 sl2 al2 tmp2 t tmp,
      dst <> For_effects ->
      tr_expr le For_val e1 sl1 a1 tmp1 ->
      tr_exprlist le el2 sl2 al2 tmp2 ->
      list_disjoint tmp1 tmp2 -> In t tmp ->
      incl tmp1 tmp -> incl tmp2 tmp ->
      tr_expr le dst (Csyntax.Ecall e1 el2 ty)
                   (sl1 ++ sl2 ++ Scall (Some t) a1 al2 :: final dst (Etempvar t ty))
                   (Etempvar t ty) tmp
  | tr_builtin_effects: forall le ef tyargs el ty sl al tmp1 any tmp,
      tr_exprlist le el sl al tmp1 ->
      incl tmp1 tmp ->
      tr_expr le For_effects (Csyntax.Ebuiltin ef tyargs el ty)
                   (sl ++ Sbuiltin None ef tyargs al :: nil)
                   any tmp
  | tr_builtin_val: forall le dst ef tyargs el ty sl al tmp1 t tmp,
      dst <> For_effects ->
      tr_exprlist le el sl al tmp1 ->
      In t tmp -> incl tmp1 tmp ->
      tr_expr le dst (Csyntax.Ebuiltin ef tyargs el ty)
                   (sl ++ Sbuiltin (Some t) ef tyargs al :: final dst (Etempvar t ty))
                   (Etempvar t ty) tmp
  | tr_paren_val: forall le e1 tycast ty sl1 a1 t tmp,
      tr_expr le (For_set (SDbase tycast ty t)) e1 sl1 a1 tmp ->
      In t tmp ->
      tr_expr le For_val (Csyntax.Eparen e1 tycast ty)
                       sl1
                       (Etempvar t ty) tmp
  | tr_paren_effects: forall le e1 tycast ty sl1 a1 tmp any,
      tr_expr le For_effects e1 sl1 a1 tmp ->
      tr_expr le For_effects (Csyntax.Eparen e1 tycast ty) sl1 any tmp
  | tr_paren_set: forall le t sd e1 tycast ty sl1 a1 tmp any,
      tr_expr le (For_set (SDcons tycast ty t sd)) e1 sl1 a1 tmp ->
      In t tmp ->
      tr_expr le (For_set sd) (Csyntax.Eparen e1 tycast ty) sl1 any tmp

with tr_exprlist: temp_env -> Csyntax.exprlist -> list statement -> list expr -> list ident -> Prop :=
  | tr_nil: forall le tmp,
      tr_exprlist le Csyntax.Enil nil nil tmp
  | tr_cons: forall le e1 el2 sl1 a1 tmp1 sl2 al2 tmp2 tmp,
      tr_expr le For_val e1 sl1 a1 tmp1 ->
      tr_exprlist le el2 sl2 al2 tmp2 ->
      list_disjoint tmp1 tmp2 ->
      incl tmp1 tmp -> incl tmp2 tmp ->
      tr_exprlist le (Csyntax.Econs e1 el2) (sl1 ++ sl2) (a1 :: al2) tmp.

Section TR_TOP.

Variable ge: genv.
Variable e: env.
Variable le: temp_env.
Variable m: mem.

Inductive tr_top: destination -> Csyntax.expr -> list statement -> expr -> list ident -> Prop :=
  | tr_top_val_val: forall v ty a tmp,
      typeof a = ty -> eval_expr ge e le m a v ->
      tr_top For_val (Csyntax.Eval v ty) nil a tmp
  | tr_top_base: forall dst r sl a tmp,
      tr_expr le dst r sl a tmp ->
      tr_top dst r sl a tmp.

End TR_TOP.

Inductive tr_expression: Csyntax.expr -> statement -> expr -> Prop :=
  | tr_expression_intro: forall r sl a tmps,
      (forall ge e le m, tr_top ge e le m For_val r sl a tmps) ->
      tr_expression r (makeseq sl) a.

Inductive tr_expr_stmt: Csyntax.expr -> statement -> Prop :=
  | tr_expr_stmt_intro: forall r sl a tmps,
      (forall ge e le m, tr_top ge e le m For_effects r sl a tmps) ->
      tr_expr_stmt r (makeseq sl).

Inductive tr_if: Csyntax.expr -> statement -> statement -> statement -> Prop :=
  | tr_if_intro: forall r s1 s2 sl a tmps,
      (forall ge e le m, tr_top ge e le m For_val r sl a tmps) ->
      tr_if r s1 s2 (makeseq (sl ++ makeif a s1 s2 :: nil)).

Inductive tr_stmt: Csyntax.statement -> statement -> Prop :=
  | tr_skip:
      tr_stmt Csyntax.Sskip Sskip
  | tr_do: forall r s,
      tr_expr_stmt r s ->
      tr_stmt (Csyntax.Sdo r) s
  | tr_seq: forall s1 s2 ts1 ts2,
      tr_stmt s1 ts1 -> tr_stmt s2 ts2 ->
      tr_stmt (Csyntax.Ssequence s1 s2) (Ssequence ts1 ts2)
  | tr_ifthenelse_empty: forall r s' a,
      tr_expression r s' a ->
      tr_stmt (Csyntax.Sifthenelse r Csyntax.Sskip Csyntax.Sskip) (Ssequence s' Sskip)
  | tr_ifthenelse: forall r s1 s2 s' a ts1 ts2,
      tr_expression r s' a ->
      tr_stmt s1 ts1 -> tr_stmt s2 ts2 ->
      tr_stmt (Csyntax.Sifthenelse r s1 s2) (Ssequence s' (Sifthenelse a ts1 ts2))
  | tr_while: forall r s1 s' ts1,
      tr_if r Sskip Sbreak s' ->
      tr_stmt s1 ts1 ->
      tr_stmt (Csyntax.Swhile r s1)
              (Sloop (Ssequence s' ts1) Sskip)
  | tr_dowhile: forall r s1 s' ts1,
      tr_if r Sskip Sbreak s' ->
      tr_stmt s1 ts1 ->
      tr_stmt (Csyntax.Sdowhile r s1)
              (Sloop ts1 s')
  | tr_for_1: forall r s3 s4 s' ts3 ts4,
      tr_if r Sskip Sbreak s' ->
      tr_stmt s3 ts3 ->
      tr_stmt s4 ts4 ->
      tr_stmt (Csyntax.Sfor Csyntax.Sskip r s3 s4)
              (Sloop (Ssequence s' ts4) ts3)
  | tr_for_2: forall s1 r s3 s4 s' ts1 ts3 ts4,
      tr_if r Sskip Sbreak s' ->
      s1 <> Csyntax.Sskip ->
      tr_stmt s1 ts1 ->
      tr_stmt s3 ts3 ->
      tr_stmt s4 ts4 ->
      tr_stmt (Csyntax.Sfor s1 r s3 s4)
              (Ssequence ts1 (Sloop (Ssequence s' ts4) ts3))
  | tr_break:
      tr_stmt Csyntax.Sbreak Sbreak
  | tr_continue:
      tr_stmt Csyntax.Scontinue Scontinue
  | tr_return_none:
      tr_stmt (Csyntax.Sreturn None) (Sreturn None)
  | tr_return_some: forall r s' a,
      tr_expression r s' a ->
      tr_stmt (Csyntax.Sreturn (Some r)) (Ssequence s' (Sreturn (Some a)))
  | tr_switch: forall r ls s' a tls,
      tr_expression r s' a ->
      tr_lblstmts ls tls ->
      tr_stmt (Csyntax.Sswitch r ls) (Ssequence s' (Sswitch a tls))
  | tr_label: forall lbl s ts,
      tr_stmt s ts ->
      tr_stmt (Csyntax.Slabel lbl s) (Slabel lbl ts)
  | tr_goto: forall lbl,
      tr_stmt (Csyntax.Sgoto lbl) (Sgoto lbl)

with tr_lblstmts: Csyntax.labeled_statements -> labeled_statements -> Prop :=
  | tr_ls_nil:
      tr_lblstmts Csyntax.LSnil LSnil
  | tr_ls_cons: forall c s ls ts tls,
      tr_stmt s ts ->
      tr_lblstmts ls tls ->
      tr_lblstmts (Csyntax.LScons c s ls) (LScons c ts tls).

Inductive tr_function: Csyntax.function -> Clight.function -> Prop :=
  | tr_function_intro: forall f tf,
      tr_stmt f.(Csyntax.fn_body) tf.(fn_body) ->
      fn_return tf = Csyntax.fn_return f ->
      fn_callconv tf = Csyntax.fn_callconv f ->
      fn_params tf = Csyntax.fn_params f ->
      fn_vars tf = Csyntax.fn_vars f ->
      tr_function f tf.

End SPEC.

Inductive tr_fundef (p: Csyntax.program): Csyntax.fundef -> Clight.fundef -> Prop :=
  | tr_internal: forall f tf,
      tr_function p.(prog_comp_env) f tf ->
      tr_fundef p (Internal f) (Internal tf)
  | tr_external: forall ef targs tres cconv,
      tr_fundef p (External ef targs tres cconv) (External ef targs tres cconv).
Module Export SimplExprproof.
Import compcert.common.Linking.

Definition match_prog (p: Csyntax.program) (tp: Clight.program) :=
    match_program_gen tr_fundef eq p p tp
 /\ prog_types tp = prog_types p.

Global Instance TransfSimplExprLink : TransfLink match_prog.
Admitted.
Module Export Compopts.

Parameter optim_tailcalls: unit -> bool.

Parameter optim_constprop: unit -> bool.

Parameter optim_CSE: unit -> bool.

Parameter optim_redundancy: unit -> bool.

Parameter debug: unit -> bool.

Import Coq.FSets.FSets.

Module OrderedPositive <: OrderedType.

Definition t := positive.
Definition eq (x y: t) := x = y.
Definition lt := Plt.

Lemma eq_refl : forall x : t, eq x x.
Proof (@eq_refl t).
Lemma eq_sym : forall x y : t, eq x y -> eq y x.
Proof (@eq_sym t).
Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
Proof (@eq_trans t).
Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
Proof Plt_trans.
Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
Proof Plt_ne.
Lemma compare : forall x y : t, Compare lt eq x y.
Admitted.
Definition eq_dec : forall x y, { eq x y } + { ~ eq x y }.
Admitted.

End OrderedPositive.

Module OrderedZ <: OrderedType.

Definition t := Z.
Definition eq (x y: t) := x = y.
Definition lt := Z.lt.

Lemma eq_refl : forall x : t, eq x x.
Proof (@eq_refl t).
Lemma eq_sym : forall x y : t, eq x y -> eq y x.
Proof (@eq_sym t).
Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
Proof (@eq_trans t).
Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
Proof Z.lt_trans.
Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
Admitted.
Lemma compare : forall x y : t, Compare lt eq x y.
Admitted.
Definition eq_dec : forall x y, { eq x y } + { ~ eq x y }.
Admitted.

End OrderedZ.

Module OrderedInt <: OrderedType.

Definition t := int.
Definition eq (x y: t) := x = y.
Definition lt (x y: t) := Int.unsigned x < Int.unsigned y.

Lemma eq_refl : forall x : t, eq x x.
Proof (@eq_refl t).
Lemma eq_sym : forall x y : t, eq x y -> eq y x.
Proof (@eq_sym t).
Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
Proof (@eq_trans t).
Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
Admitted.
Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
Admitted.
Lemma compare : forall x y : t, Compare lt eq x y.
Admitted.
Definition eq_dec : forall x y, { eq x y } + { ~ eq x y }.
Admitted.

End OrderedInt.

Module OrderedIndexed(A: INDEXED_TYPE) <: OrderedType.

Definition t := A.t.
Definition eq (x y: t) := x = y.
Definition lt (x y: t) := Plt (A.index x) (A.index y).

Lemma eq_refl : forall x : t, eq x x.
Proof (@eq_refl t).
Lemma eq_sym : forall x y : t, eq x y -> eq y x.
Proof (@eq_sym t).
Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
Proof (@eq_trans t).

Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
Admitted.

Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
Admitted.

Lemma compare : forall x y : t, Compare lt eq x y.
Admitted.

Lemma eq_dec : forall x y, { eq x y } + { ~ eq x y }.
Admitted.

End OrderedIndexed.

Module OrderedPair (A B: OrderedType) <: OrderedType.

Definition t := (A.t * B.t)%type.

Definition eq (x y: t) :=
  A.eq (fst x) (fst y) /\ B.eq (snd x) (snd y).

Lemma eq_refl : forall x : t, eq x x.
Admitted.

Lemma eq_sym : forall x y : t, eq x y -> eq y x.
Admitted.

Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
Admitted.

Definition lt (x y: t) :=
  A.lt (fst x) (fst y) \/
  (A.eq (fst x) (fst y) /\ B.lt (snd x) (snd y)).

Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
Admitted.

Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
Admitted.

Lemma compare : forall x y : t, Compare lt eq x y.
Admitted.

Lemma eq_dec : forall x y, { eq x y } + { ~ eq x y }.
Admitted.

End OrderedPair.
Import compcert.common.AST.

Inductive condition : Type :=
  | Ccomp (c: comparison)
  | Ccompu (c: comparison)
  | Ccompimm (c: comparison) (n: int)
  | Ccompuimm (c: comparison) (n: int)
  | Ccompl (c: comparison)
  | Ccomplu (c: comparison)
  | Ccomplimm (c: comparison) (n: int64)
  | Ccompluimm (c: comparison) (n: int64)
  | Ccompf (c: comparison)
  | Cnotcompf (c: comparison)
  | Ccompfs (c: comparison)
  | Cnotcompfs (c: comparison)
  | Cmaskzero (n: int)
  | Cmasknotzero (n: int).

Inductive addressing: Type :=
  | Aindexed: Z -> addressing
  | Aindexed2: Z -> addressing
  | Ascaled: Z -> Z -> addressing
  | Aindexed2scaled: Z -> Z -> addressing

  | Aglobal: ident -> ptrofs -> addressing
  | Abased: ident -> ptrofs -> addressing
  | Abasedscaled: Z -> ident -> ptrofs -> addressing
  | Ainstack: ptrofs -> addressing.

Inductive operation : Type :=
  | Omove
  | Ointconst (n: int)
  | Olongconst (n: int64)
  | Ofloatconst (n: float)
  | Osingleconst (n: float32)
  | Oindirectsymbol (id: ident)

  | Ocast8signed
  | Ocast8unsigned
  | Ocast16signed
  | Ocast16unsigned
  | Oneg
  | Osub
  | Omul
  | Omulimm (n: int)
  | Omulhs
  | Omulhu
  | Odiv
  | Odivu
  | Omod
  | Omodu
  | Oand
  | Oandimm (n: int)
  | Oor
  | Oorimm (n: int)
  | Oxor
  | Oxorimm (n: int)
  | Onot
  | Oshl
  | Oshlimm (n: int)
  | Oshr
  | Oshrimm (n: int)
  | Oshrximm (n: int)
  | Oshru
  | Oshruimm (n: int)
  | Ororimm (n: int)
  | Oshldimm (n: int)
  | Olea (a: addressing)

  | Omakelong
  | Olowlong
  | Ohighlong
  | Ocast32signed
  | Ocast32unsigned
  | Onegl
  | Oaddlimm (n: int64)
  | Osubl
  | Omull
  | Omullimm (n: int64)
  | Omullhs
  | Omullhu
  | Odivl
  | Odivlu
  | Omodl
  | Omodlu
  | Oandl
  | Oandlimm (n: int64)
  | Oorl
  | Oorlimm (n: int64)
  | Oxorl
  | Oxorlimm (n: int64)
  | Onotl
  | Oshll
  | Oshllimm (n: int)
  | Oshrl
  | Oshrlimm (n: int)
  | Oshrxlimm (n: int)
  | Oshrlu
  | Oshrluimm (n: int)
  | Ororlimm (n: int)
  | Oleal (a: addressing)

  | Onegf
  | Oabsf
  | Oaddf
  | Osubf
  | Omulf
  | Odivf
  | Omaxf
  | Ominf
  | Onegfs
  | Oabsfs
  | Oaddfs
  | Osubfs
  | Omulfs
  | Odivfs
  | Osingleoffloat
  | Ofloatofsingle

  | Ointoffloat
  | Ofloatofint
  | Ointofsingle
  | Osingleofint
  | Olongoffloat
  | Ofloatoflong
  | Olongofsingle
  | Osingleoflong

  | Ocmp (cond: condition)
  | Osel: condition -> typ -> operation.

Inductive mreg: Type :=

  | AX | BX | CX | DX | SI | DI | BP
  | R8 | R9 | R10 | R11 | R12 | R13 | R14 | R15

  | X0 | X1 | X2 | X3 | X4 | X5 | X6 | X7
  | X8 | X9 | X10 | X11 | X12 | X13 | X14 | X15

  | FP0.

Lemma mreg_eq: forall (r1 r2: mreg), {r1 = r2} + {r1 <> r2}.
Admitted.

Module IndexedMreg <: INDEXED_TYPE.
  Definition t := mreg.
  Definition eq := mreg_eq.
Definition index (r: mreg): positive.
Admitted.
  Lemma index_inj:
    forall r1 r2, index r1 = index r2 -> r1 = r2.
Admitted.
End IndexedMreg.
Definition destroyed_by_builtin (ef: external_function): list mreg.
Admitted.

Inductive slot: Type :=
  | Local
  | Incoming
  | Outgoing.

Lemma slot_eq: forall (p q: slot), {p = q} + {p <> q}.
Admitted.

Inductive loc : Type :=
  | R (r: mreg)
  | S (sl: slot) (pos: Z) (ty: typ).

Module Loc.

  Lemma eq: forall (p q: loc), {p = q} + {p <> q}.
Admitted.

End Loc.

Module IndexedTyp <: INDEXED_TYPE.
  Definition t := typ.
  Definition index (x: t) :=
    match x with
    | Tany32 => 1%positive
    | Tint => 2%positive
    | Tsingle => 3%positive
    | Tany64 => 4%positive
    | Tfloat => 5%positive
    | Tlong => 6%positive
    end.
  Lemma index_inj: forall x y, index x = index y -> x = y.
Admitted.
  Definition eq := typ_eq.
End IndexedTyp.

Module OrderedTyp := OrderedIndexed(IndexedTyp).

Module IndexedSlot <: INDEXED_TYPE.
  Definition t := slot.
  Definition index (x: t) :=
    match x with Local => 1%positive | Incoming => 2%positive | Outgoing => 3%positive end.
  Lemma index_inj: forall x y, index x = index y -> x = y.
Admitted.
  Definition eq := slot_eq.
End IndexedSlot.

Module OrderedSlot := OrderedIndexed(IndexedSlot).

Module OrderedLoc <: OrderedType.
  Definition t := loc.
  Definition eq (x y: t) := x = y.
  Definition lt (x y: t) :=
    match x, y with
    | R r1, R r2 => Plt (IndexedMreg.index r1) (IndexedMreg.index r2)
    | R _, S _ _ _ => True
    | S _ _ _, R _ => False
    | S sl1 ofs1 ty1, S sl2 ofs2 ty2 =>
        OrderedSlot.lt sl1 sl2 \/ (sl1 = sl2 /\
        (ofs1 < ofs2 \/ (ofs1 = ofs2 /\ OrderedTyp.lt ty1 ty2)))
    end.
  Lemma eq_refl : forall x : t, eq x x.
  Proof (@eq_refl t).
  Lemma eq_sym : forall x y : t, eq x y -> eq y x.
  Proof (@eq_sym t).
  Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
  Proof (@eq_trans t).
  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
Admitted.
  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
Admitted.
  Definition compare : forall x y : t, Compare lt eq x y.
Admitted.
  Definition eq_dec := Loc.eq.

End OrderedLoc.
Module Export SimplLocalsproof.
Import compcert.cfrontend.Clight.
Definition match_prog (p tp: program) : Prop.
Admitted.

Global Instance TransfSimplLocalsLink : TransfLink match_prog.
Admitted.

Module Export compcert_DOT_backend_DOT_Cminor_WRAPPED.
Module Export Cminor.

Inductive stmt : Type :=
  | Sskip: stmt
  | Sassign : ident -> expr -> stmt
  | Sstore : memory_chunk -> expr -> expr -> stmt
  | Scall : option ident -> signature -> expr -> list expr -> stmt
  | Stailcall: signature -> expr -> list expr -> stmt
  | Sbuiltin : option ident -> external_function -> list expr -> stmt
  | Sseq: stmt -> stmt -> stmt
  | Sifthenelse: expr -> stmt -> stmt -> stmt
  | Sloop: stmt -> stmt
  | Sblock: stmt -> stmt
  | Sexit: nat -> stmt
  | Sswitch: bool -> expr -> list (Z * nat) -> nat -> stmt
  | Sreturn: option expr -> stmt
  | Slabel: label -> stmt -> stmt
  | Sgoto: label -> stmt.

Record function : Type := mkfunction {
  fn_sig: signature;
  fn_params: list ident;
  fn_vars: list ident;
  fn_stackspace: Z;
  fn_body: stmt
}.

Definition fundef := AST.fundef function.
Definition program := AST.program fundef unit.

End Cminor.
Module Export compcert.
Module Export backend.
Module Export Cminor.
Include compcert_DOT_backend_DOT_Cminor_WRAPPED.Cminor.
End Cminor.
Module Export Csharpminor.

Record function : Type := mkfunction {
  fn_sig: signature;
  fn_params: list ident;
  fn_vars: list (ident * Z);
  fn_temps: list ident;
  fn_body: stmt
}.

Definition fundef := AST.fundef function.
Definition program : Type.
exact (AST.program fundef unit).
Defined.

Module Export Cshmgenproof.
Definition match_prog (p: Clight.program) (tp: Csharpminor.program) : Prop.
Admitted.

Global Instance TransfCshmgenLink : TransfLink match_prog.
Admitted.
Import compcert.backend.Cminor.
Definition transl_function (f: Csharpminor.function): res function.
Admitted.
Definition transl_fundef (f: Csharpminor.fundef): res fundef.
exact (transf_partial_fundef transl_function f).
Defined.
Module Export Cminorgenproof.

Definition match_prog (p: Csharpminor.program) (tp: Cminor.program) :=
  match_program (fun cu f tf => transl_fundef f = OK tf) eq p tp.

Module Export CminorSel.

Record function : Type := mkfunction {
  fn_sig: signature;
  fn_params: list ident;
  fn_vars: list ident;
  fn_stackspace: Z;
  fn_body: stmt
}.

Definition fundef := AST.fundef function.
Definition program := AST.program fundef unit.

Module Export Selectionproof.
Definition match_fundef (cunit: Cminor.program) (f: Cminor.fundef) (tf: CminorSel.fundef) : Prop.
Admitted.

Definition match_prog (p: Cminor.program) (tp: CminorSel.program) :=
  match_program match_fundef eq p tp.

Global Instance TransfSelectionLink : TransfLink match_prog.
Admitted.
Definition reg: Type.
exact (positive).
Defined.
Module Export RTL.

Definition node := positive.

Inductive instruction: Type :=
  | Inop: node -> instruction

  | Iop: operation -> list reg -> reg -> node -> instruction

  | Iload: memory_chunk -> addressing -> list reg -> reg -> node -> instruction

  | Istore: memory_chunk -> addressing -> list reg -> reg -> node -> instruction

  | Icall: signature -> reg + ident -> list reg -> reg -> node -> instruction

  | Itailcall: signature -> reg + ident -> list reg -> instruction

  | Ibuiltin: external_function -> list (builtin_arg reg) -> builtin_res reg -> node -> instruction

  | Icond: condition -> list reg -> node -> node -> instruction

  | Ijumptable: reg -> list node -> instruction

  | Ireturn: option reg -> instruction.
Definition code: Type.
exact (PTree.t instruction).
Defined.

Record function: Type := mkfunction {
  fn_sig: signature;
  fn_params: list reg;
  fn_stacksize: Z;
  fn_code: code;
  fn_entrypoint: node
}.

Definition fundef := AST.fundef function.

Definition program := AST.program fundef unit.
Definition transl_function (f: CminorSel.function) : Errors.res RTL.function.
Admitted.

Definition transl_fundef := transf_partial_fundef transl_function.
Module Export RTLgenproof.

Definition match_prog (p: CminorSel.program) (tp: RTL.program) :=
  match_program (fun cu f tf => transl_fundef f = Errors.OK tf) eq p tp.
Definition transf_function (f: function) : function.
Admitted.
Definition transf_fundef (fd: fundef) : fundef.
exact (AST.transf_fundef transf_function fd).
Defined.
Module Export Tailcallproof.

Definition match_prog (p tp: RTL.program) :=
  match_program (fun cu f tf => tf = transf_fundef f) eq p tp.
Definition funenv : Type.
Admitted.
Definition funenv_program (p: program) : funenv.
Admitted.

Definition transf_function (fenv: funenv) (f: function) : Errors.res function.
Admitted.
Definition transf_fundef (fenv: funenv) (fd: fundef) : Errors.res fundef.
exact (AST.transf_partial_fundef (transf_function fenv) fd).
Defined.
Module Export Inliningproof.

Definition match_prog (prog tprog: program) :=
  match_program (fun cunit f tf => transf_fundef (funenv_program cunit) f = OK tf) eq prog tprog.

Definition transf_function (f: function) : function.
Admitted.
Definition transf_fundef (fd: fundef) : fundef.
exact (AST.transf_fundef transf_function fd).
Defined.
Module Export Renumberproof.

Definition match_prog (p tp: RTL.program) :=
  match_program (fun ctx f tf => tf = transf_fundef f) eq p tp.

Section MATCH.

Inductive aptr : Type :=
  | Pbot
  | Gl (id: ident) (ofs: ptrofs)
  | Glo (id: ident)
  | Glob
  | Stk (ofs: ptrofs)
  | Stack
  | Nonstack
  | Ptop.

Inductive aval : Type :=
  | Vbot
  | I (n: int)
  | Uns (p: aptr) (n: Z)
  | Sgn (p: aptr) (n: Z)
  | L (n: int64)
  | F (f: float)
  | FS (f: float32)
  | Num (p: aptr)
  | Ptr (p: aptr)
  | Ifptr (p: aptr).

Inductive acontent : Type :=
 | ACval (chunk: memory_chunk) (av: aval).

Record ablock : Type := ABlock {
  ab_contents: ZTree.t acontent;
  ab_summary: aptr
}.

Definition romem := PTree.t ablock.

End MATCH.
Definition romem_for (p: program) : romem.
Admitted.
Definition transf_function (rm: romem) (f: function) : function.
Admitted.
Definition transf_fundef (rm: romem) (fd: fundef) : fundef.
exact (AST.transf_fundef (transf_function rm) fd).
Defined.
Module Export Constpropproof.

Definition match_prog (prog tprog: program) :=
  match_program (fun cu f tf => tf = transf_fundef (romem_for cu) f) eq prog tprog.

Definition transf_function (rm: romem) (f: function) : res function.
Admitted.
Definition transf_fundef (rm: romem) (f: fundef) : res fundef.
exact (AST.transf_partial_fundef (transf_function rm) f).
Defined.
Module Export CSEproof.

Definition match_prog (prog tprog: RTL.program) :=
  match_program (fun cu f tf => transf_fundef (romem_for cu) f = OK tf) eq prog tprog.
Module Export Deadcodeproof.

Definition match_prog (prog tprog: RTL.program) :=
  match_program (fun cu f tf => transf_fundef (romem_for cu) f = OK tf) eq prog tprog.

Module Export Unusedglobproof.
Definition match_prog (p tp: program) : Prop.
Admitted.

Global Instance TransfSelectionLink : TransfLink match_prog.
Admitted.

Module Export compcert_DOT_backend_DOT_LTL_WRAPPED.
Module Export LTL.

Record function: Type := mkfunction {
  fn_sig: signature;
  fn_stacksize: Z;
  fn_code: code;
  fn_entrypoint: node
}.

Definition fundef := AST.fundef function.

Definition program := AST.program fundef unit.

End LTL.
Module Export compcert.
Module Export backend.
Module Export LTL.
Include compcert_DOT_backend_DOT_LTL_WRAPPED.LTL.
End LTL.

Inductive equation_kind : Type := Full | Low | High.

Record equation := Eq {
  ekind: equation_kind;
  ereg: reg;
  eloc: loc
}.

Module IndexedEqKind <: INDEXED_TYPE.
  Definition t := equation_kind.
  Definition index (x: t) :=
    match x with Full => 1%positive | Low => 2%positive | High => 3%positive end.
  Lemma index_inj: forall x y, index x = index y -> x = y.
Admitted.
  Definition eq (x y: t) : {x=y} + {x<>y}.
Admitted.
End IndexedEqKind.

Module OrderedEqKind := OrderedIndexed(IndexedEqKind).

Module OrderedEquation <: OrderedType.
  Definition t := equation.
  Definition eq (x y: t) := x = y.
  Definition lt (x y: t) :=
    Plt (ereg x) (ereg y) \/ (ereg x = ereg y /\
    (OrderedLoc.lt (eloc x) (eloc y) \/ (eloc x = eloc y /\
    OrderedEqKind.lt (ekind x) (ekind y)))).
  Lemma eq_refl : forall x : t, eq x x.
  Proof (@eq_refl t).
  Lemma eq_sym : forall x y : t, eq x y -> eq y x.
  Proof (@eq_sym t).
  Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
  Proof (@eq_trans t).
  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
Admitted.
  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
Admitted.
  Definition compare : forall x y : t, Compare lt eq x y.
Admitted.
  Definition eq_dec (x y: t) : {x = y} + {x <> y}.
Admitted.
End OrderedEquation.

Module OrderedEquation' <: OrderedType.
  Definition t := equation.
  Definition eq (x y: t) := x = y.
  Definition lt (x y: t) :=
    OrderedLoc.lt (eloc x) (eloc y) \/ (eloc x = eloc y /\
    (Plt (ereg x) (ereg y) \/ (ereg x = ereg y /\
    OrderedEqKind.lt (ekind x) (ekind y)))).
  Lemma eq_refl : forall x : t, eq x x.
  Proof (@eq_refl t).
  Lemma eq_sym : forall x y : t, eq x y -> eq y x.
  Proof (@eq_sym t).
  Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
  Proof (@eq_trans t).
  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
Admitted.
  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
Admitted.
  Definition compare : forall x y : t, Compare lt eq x y.
Admitted.
Definition eq_dec: forall (x y: t), {x = y} + {x <> y}.
Admitted.
End OrderedEquation'.
Definition transf_function (f: RTL.function) : res LTL.function.
Admitted.
Definition transf_fundef (fd: RTL.fundef) : res LTL.fundef.
exact (AST.transf_partial_fundef transf_function fd).
Defined.
Module Export Allocproof.

Definition match_prog (p: RTL.program) (tp: LTL.program) :=
  match_program (fun _ f tf => transf_fundef f = OK tf) eq p tp.
Import compcert.common.AST.
Import compcert.backend.LTL.
Definition tunnel_function (f: LTL.function) : LTL.function.
Admitted.
Definition tunnel_fundef (f: LTL.fundef) : LTL.fundef.
exact (transf_fundef tunnel_function f).
Defined.
Module Export Tunnelingproof.

Definition match_prog (p tp: program) :=
  match_program (fun ctx f tf => tf = tunnel_fundef f) eq p tp.
Module Export Linear.

Record function: Type := mkfunction {
  fn_sig: signature;
  fn_stacksize: Z;
  fn_code: code
}.

Definition fundef := AST.fundef function.

Definition program := AST.program fundef unit.
Definition transf_function (f: LTL.function) : res Linear.function.
Admitted.
Definition transf_fundef (f: LTL.fundef) : res Linear.fundef.
exact (AST.transf_partial_fundef transf_function f).
Defined.
Module Export Linearizeproof.

Definition match_prog (p: LTL.program) (tp: Linear.program) :=
  match_program (fun ctx f tf => transf_fundef f = OK tf) eq p tp.
Definition transf_function (f: function) : function.
Admitted.
Definition transf_fundef (f: fundef) : fundef.
exact (AST.transf_fundef transf_function f).
Defined.
Module Export CleanupLabelsproof.

Definition match_prog (p tp: Linear.program) :=
  match_program (fun ctx f tf => tf = transf_fundef f) eq p tp.
Definition transf_function (f: function) : res function.
Admitted.
Definition transf_fundef (fd: fundef) : res fundef.
exact (AST.transf_partial_fundef transf_function fd).
Defined.
Module Export Debugvarproof.

Definition match_prog (p tp: program) :=
  match_program (fun _ f tf => transf_fundef f = OK tf) eq p tp.

Module Export Mach.

Record function: Type := mkfunction
  { fn_sig: signature;
    fn_code: code;
    fn_stacksize: Z;
    fn_link_ofs: ptrofs;
    fn_retaddr_ofs: ptrofs }.

Definition fundef := AST.fundef function.

Definition program := AST.program fundef unit.
Definition transf_function (f: Linear.function) : res Mach.function.
Admitted.
Definition transf_fundef (f: Linear.fundef) : res Mach.fundef.
exact (AST.transf_partial_fundef transf_function f).
Defined.
Module Export Stackingproof.

Definition match_prog (p: Linear.program) (tp: Mach.program) :=
  match_program (fun _ f tf => transf_fundef f = OK tf) eq p tp.

Module Export Asm.

Inductive ireg: Type :=
  | RAX | RBX | RCX | RDX | RSI | RDI | RBP | RSP
  | R8  | R9  | R10 | R11 | R12 | R13 | R14 | R15.

Inductive freg: Type :=
  | XMM0  | XMM1  | XMM2  | XMM3  | XMM4  | XMM5  | XMM6  | XMM7
  | XMM8  | XMM9  | XMM10 | XMM11 | XMM12 | XMM13 | XMM14 | XMM15.

Inductive crbit: Type :=
  | ZF | CF | PF | SF | OF.

Inductive preg: Type :=
  | PC: preg
  | IR: ireg -> preg
  | FR: freg -> preg
  | ST0: preg
  | CR: crbit -> preg
  | RA: preg.

Coercion IR: ireg >-> preg.

Inductive addrmode: Type :=
  | Addrmode (base: option ireg)
             (ofs: option (ireg * Z))
             (const: Z + ident * ptrofs).

Inductive testcond: Type :=
  | Cond_e | Cond_ne
  | Cond_b | Cond_be | Cond_ae | Cond_a
  | Cond_l | Cond_le | Cond_ge | Cond_g
  | Cond_p | Cond_np.

Inductive instruction: Type :=

  | Pmov_rr (rd: ireg) (r1: ireg)
  | Pmovl_ri (rd: ireg) (n: int)
  | Pmovq_ri (rd: ireg) (n: int64)
  | Pmov_rs (rd: ireg) (id: ident)
  | Pmovl_rm (rd: ireg) (a: addrmode)
  | Pmovq_rm (rd: ireg) (a: addrmode)
  | Pmovl_mr (a: addrmode) (rs: ireg)
  | Pmovq_mr (a: addrmode) (rs: ireg)
  | Pmovsd_ff (rd: freg) (r1: freg)
  | Pmovsd_fi (rd: freg) (n: float)
  | Pmovsd_fm (rd: freg) (a: addrmode)
  | Pmovsd_mf (a: addrmode) (r1: freg)
  | Pmovss_fi (rd: freg) (n: float32)
  | Pmovss_fm (rd: freg) (a: addrmode)
  | Pmovss_mf (a: addrmode) (r1: freg)
  | Pfldl_m (a: addrmode)
  | Pfstpl_m (a: addrmode)
  | Pflds_m (a: addrmode)
  | Pfstps_m (a: addrmode)

  | Pmovb_mr (a: addrmode) (rs: ireg)
  | Pmovw_mr (a: addrmode) (rs: ireg)
  | Pmovzb_rr (rd: ireg) (rs: ireg)
  | Pmovzb_rm (rd: ireg) (a: addrmode)
  | Pmovsb_rr (rd: ireg) (rs: ireg)
  | Pmovsb_rm (rd: ireg) (a: addrmode)
  | Pmovzw_rr (rd: ireg) (rs: ireg)
  | Pmovzw_rm (rd: ireg) (a: addrmode)
  | Pmovsw_rr (rd: ireg) (rs: ireg)
  | Pmovsw_rm (rd: ireg) (a: addrmode)
  | Pmovzl_rr (rd: ireg) (rs: ireg)
  | Pmovsl_rr (rd: ireg) (rs: ireg)
  | Pmovls_rr (rd: ireg)
  | Pcvtsd2ss_ff (rd: freg) (r1: freg)
  | Pcvtss2sd_ff (rd: freg) (r1: freg)
  | Pcvttsd2si_rf (rd: ireg) (r1: freg)
  | Pcvtsi2sd_fr (rd: freg) (r1: ireg)
  | Pcvttss2si_rf (rd: ireg) (r1: freg)
  | Pcvtsi2ss_fr (rd: freg) (r1: ireg)
  | Pcvttsd2sl_rf (rd: ireg) (r1: freg)
  | Pcvtsl2sd_fr (rd: freg) (r1: ireg)
  | Pcvttss2sl_rf (rd: ireg) (r1: freg)
  | Pcvtsl2ss_fr (rd: freg) (r1: ireg)

  | Pleal (rd: ireg) (a: addrmode)
  | Pleaq (rd: ireg) (a: addrmode)
  | Pnegl (rd: ireg)
  | Pnegq (rd: ireg)
  | Paddl_ri (rd: ireg) (n: int)
  | Paddq_ri (rd: ireg) (n: int64)
  | Psubl_rr (rd: ireg) (r1: ireg)
  | Psubq_rr (rd: ireg) (r1: ireg)
  | Pimull_rr (rd: ireg) (r1: ireg)
  | Pimulq_rr (rd: ireg) (r1: ireg)
  | Pimull_ri (rd: ireg) (n: int)
  | Pimulq_ri (rd: ireg) (n: int64)
  | Pimull_r (r1: ireg)
  | Pimulq_r (r1: ireg)
  | Pmull_r (r1: ireg)
  | Pmulq_r (r1: ireg)
  | Pcltd
  | Pcqto
  | Pdivl (r1: ireg)
  | Pdivq (r1: ireg)
  | Pidivl (r1: ireg)
  | Pidivq (r1: ireg)
  | Pandl_rr (rd: ireg) (r1: ireg)
  | Pandq_rr (rd: ireg) (r1: ireg)
  | Pandl_ri (rd: ireg) (n: int)
  | Pandq_ri (rd: ireg) (n: int64)
  | Porl_rr (rd: ireg) (r1: ireg)
  | Porq_rr (rd: ireg) (r1: ireg)
  | Porl_ri (rd: ireg) (n: int)
  | Porq_ri (rd: ireg) (n: int64)
  | Pxorl_r (rd: ireg)
  | Pxorq_r (rd: ireg)
  | Pxorl_rr (rd: ireg) (r1: ireg)
  | Pxorq_rr (rd: ireg) (r1: ireg)
  | Pxorl_ri (rd: ireg) (n: int)
  | Pxorq_ri (rd: ireg) (n: int64)
  | Pnotl (rd: ireg)
  | Pnotq (rd: ireg)
  | Psall_rcl (rd: ireg)
  | Psalq_rcl (rd: ireg)
  | Psall_ri (rd: ireg) (n: int)
  | Psalq_ri (rd: ireg) (n: int)
  | Pshrl_rcl (rd: ireg)
  | Pshrq_rcl (rd: ireg)
  | Pshrl_ri (rd: ireg) (n: int)
  | Pshrq_ri (rd: ireg) (n: int)
  | Psarl_rcl (rd: ireg)
  | Psarq_rcl (rd: ireg)
  | Psarl_ri (rd: ireg) (n: int)
  | Psarq_ri (rd: ireg) (n: int)
  | Pshld_ri (rd: ireg) (r1: ireg) (n: int)
  | Prorl_ri (rd: ireg) (n: int)
  | Prorq_ri (rd: ireg) (n: int)
  | Pcmpl_rr (r1 r2: ireg)
  | Pcmpq_rr (r1 r2: ireg)
  | Pcmpl_ri (r1: ireg) (n: int)
  | Pcmpq_ri (r1: ireg) (n: int64)
  | Ptestl_rr (r1 r2: ireg)
  | Ptestq_rr (r1 r2: ireg)
  | Ptestl_ri (r1: ireg) (n: int)
  | Ptestq_ri (r1: ireg) (n: int64)
  | Pcmov (c: testcond) (rd: ireg) (r1: ireg)
  | Psetcc (c: testcond) (rd: ireg)

  | Paddd_ff (rd: freg) (r1: freg)
  | Psubd_ff (rd: freg) (r1: freg)
  | Pmuld_ff (rd: freg) (r1: freg)
  | Pdivd_ff (rd: freg) (r1: freg)
  | Pnegd (rd: freg)
  | Pabsd (rd: freg)
  | Pcomisd_ff (r1 r2: freg)
  | Pxorpd_f (rd: freg)
  | Padds_ff (rd: freg) (r1: freg)
  | Psubs_ff (rd: freg) (r1: freg)
  | Pmuls_ff (rd: freg) (r1: freg)
  | Pdivs_ff (rd: freg) (r1: freg)
  | Pnegs (rd: freg)
  | Pabss (rd: freg)
  | Pcomiss_ff (r1 r2: freg)
  | Pxorps_f (rd: freg)

  | Pjmp_l (l: label)
  | Pjmp_s (symb: ident) (sg: signature)
  | Pjmp_r (r: ireg) (sg: signature)
  | Pjcc (c: testcond)(l: label)
  | Pjcc2 (c1 c2: testcond)(l: label)
  | Pjmptbl (r: ireg) (tbl: list label)
  | Pcall_s (symb: ident) (sg: signature)
  | Pcall_r (r: ireg) (sg: signature)
  | Pret

  | Pmov_rm_a (rd: ireg) (a: addrmode)
  | Pmov_mr_a (a: addrmode) (rs: ireg)
  | Pmovsd_fm_a (rd: freg) (a: addrmode)
  | Pmovsd_mf_a (a: addrmode) (r1: freg)

  | Plabel(l: label)
  | Pallocframe(sz: Z)(ofs_ra ofs_link: ptrofs)
  | Pfreeframe(sz: Z)(ofs_ra ofs_link: ptrofs)
  | Pbuiltin(ef: external_function)(args: list (builtin_arg preg))(res: builtin_res preg)

  | Padcl_ri (rd: ireg) (n: int)
  | Padcl_rr (rd: ireg) (r2: ireg)
  | Paddl_mi (a: addrmode) (n: int)
  | Paddl_rr (rd: ireg) (r2: ireg)
  | Pbsfl (rd: ireg) (r1: ireg)
  | Pbsfq (rd: ireg) (r1: ireg)
  | Pbsrl (rd: ireg) (r1: ireg)
  | Pbsrq (rd: ireg) (r1: ireg)
  | Pbswap64 (rd: ireg)
  | Pbswap32 (rd: ireg)
  | Pbswap16 (rd: ireg)
  | Pcfi_adjust (n: int)
  | Pfmadd132 (rd: freg) (r2: freg) (r3: freg)
  | Pfmadd213 (rd: freg) (r2: freg) (r3: freg)
  | Pfmadd231 (rd: freg) (r2: freg) (r3: freg)
  | Pfmsub132 (rd: freg) (r2: freg) (r3: freg)
  | Pfmsub213 (rd: freg) (r2: freg) (r3: freg)
  | Pfmsub231 (rd: freg) (r2: freg) (r3: freg)
  | Pfnmadd132 (rd: freg) (r2: freg) (r3: freg)
  | Pfnmadd213 (rd: freg) (r2: freg) (r3: freg)
  | Pfnmadd231 (rd: freg) (r2: freg) (r3: freg)
  | Pfnmsub132 (rd: freg) (r2: freg) (r3: freg)
  | Pfnmsub213 (rd: freg) (r2: freg) (r3: freg)
  | Pfnmsub231 (rd: freg) (r2: freg) (r3: freg)
  | Pmaxsd (rd: freg) (r2: freg)
  | Pminsd (rd: freg) (r2: freg)
  | Pmovb_rm (rd: ireg) (a: addrmode)
  | Pmovq_rf (rd: ireg) (r1: freg)
  | Pmovsq_mr  (a: addrmode) (rs: freg)
  | Pmovsq_rm (rd: freg) (a: addrmode)
  | Pmovsb
  | Pmovsw
  | Pmovw_rm (rd: ireg) (ad: addrmode)
  | Pnop
  | Prep_movsl
  | Psbbl_rr (rd: ireg) (r2: ireg)
  | Psqrtsd (rd: freg) (r1: freg)
  | Psubl_ri (rd: ireg) (n: int)
  | Psubq_ri (rd: ireg) (n: int64).
Record function : Type := mkfunction { fn_sig: signature; fn_code: code }.
Definition fundef := AST.fundef function.
Definition program := AST.program fundef unit.

Lemma preg_eq: forall (x y: preg), {x=y} + {x<>y}.
Admitted.

Module PregEq.
  Definition t := preg.
  Definition eq := preg_eq.
End PregEq.

Module Pregmap := EMap(PregEq).

Definition regset := Pregmap.t val.
Definition genv := Genv.t fundef unit.
Notation "a # b" := (a b) (at level 1, only parsing) : asm.
Notation "a # b <- c" := (Pregmap.set b c a) (at level 1, b at next level) : asm.

Open Scope asm.

Fixpoint undef_regs (l: list preg) (rs: regset) : regset :=
  match l with
  | nil => rs
  | r :: l' => undef_regs l' (rs#r <- Vundef)
  end.
Definition set_pair (p: rpair preg) (v: val) (rs: regset) : regset.
Admitted.

Fixpoint set_res (res: builtin_res preg) (v: val) (rs: regset) : regset :=
  match res with
  | BR r => rs#r <- v
  | BR_none => rs
  | BR_splitlong hi lo => set_res lo (Val.loword v) (set_res hi (Val.hiword v) rs)
  end.

Section RELSEM.
Fixpoint find_instr (pos: Z) (c: code) {struct c} : option instruction.
Admitted.

Variable ge: genv.

Inductive outcome: Type :=
  | Next: regset -> mem -> outcome
  | Stuck: outcome.
Definition nextinstr_nf (rs: regset) : regset.
Admitted.
Definition exec_instr (f: function) (i: instruction) (rs: regset) (m: mem) : outcome.
Admitted.
Definition preg_of (r: mreg) : preg.
Admitted.
Definition undef_caller_save_regs (rs: regset) : regset.
Admitted.
Definition extcall_arguments
    (rs: regset) (m: mem) (sg: signature) (args: list val) : Prop.
Admitted.
Definition loc_external_result (sg: signature) : rpair preg.
Admitted.

Inductive state: Type :=
  | State: regset -> mem -> state.

Inductive step: state -> trace -> state -> Prop :=
  | exec_step_internal:
      forall b ofs f i rs m rs' m',
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Ptrofs.unsigned ofs) f.(fn_code) = Some i ->
      exec_instr f i rs m = Next rs' m' ->
      step (State rs m) E0 (State rs' m')
  | exec_step_builtin:
      forall b ofs f ef args res rs m vargs t vres rs' m',
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Ptrofs.unsigned ofs) f.(fn_code) = Some (Pbuiltin ef args res) ->
      eval_builtin_args ge rs (rs RSP) m args vargs ->
      external_call ef ge vargs m t vres m' ->
      rs' = nextinstr_nf
             (set_res res vres
               (undef_regs (map preg_of (destroyed_by_builtin ef)) rs)) ->
      step (State rs m) t (State rs' m')
  | exec_step_external:
      forall b ef args res rs m t rs' m',
      rs PC = Vptr b Ptrofs.zero ->
      Genv.find_funct_ptr ge b = Some (External ef) ->
      extcall_arguments rs m (ef_sig ef) args ->
      external_call ef ge args m t res m' ->
      rs' = (set_pair (loc_external_result (ef_sig ef)) res (undef_caller_save_regs rs)) #PC <- (rs RA) ->
      step (State rs m) t (State rs' m').

End RELSEM.

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall m0,
      Genv.init_mem p = Some m0 ->
      let ge := Genv.globalenv p in
      let rs0 :=
        (Pregmap.init Vundef)
        # PC <- (Genv.symbol_address ge p.(prog_main) Ptrofs.zero)
        # RA <- Vnullptr
        # RSP <- Vnullptr in
      initial_state p (State rs0 m0).

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall rs m r,
      rs#PC = Vnullptr ->
      rs#RAX = Vint r ->
      final_state (State rs m) r.

Definition semantics (p: program) :=
  Semantics step (initial_state p) final_state (Genv.globalenv p).
Import compcert.common.AST.
Definition transf_function (f: Mach.function) : res Asm.function.
Admitted.
Definition transf_fundef (f: Mach.fundef) : res Asm.fundef.
exact (transf_partial_fundef transf_function f).
Defined.
Module Export Asmgenproof.

Definition match_prog (p: Mach.program) (tp: Asm.program) :=
  match_program (fun _ f tf => transf_fundef f = OK tf) eq p tp.

End Asmgenproof.
Definition transf_c_program (p: Csyntax.program) : res Asm.program.
Admitted.
Definition match_if {A: Type} (flag: unit -> bool) (R: A -> A -> Prop): A -> A -> Prop.
Admitted.

Global Instance TransfIfLink {A: Type} {LA: Linker A}
                      (flag: unit -> bool) (transf: A -> A -> Prop) (TL: TransfLink transf)
                      : TransfLink (match_if flag transf).
Admitted.

Local Open Scope linking_scope.

Definition CompCert's_passes :=
      mkpass SimplExprproof.match_prog
  ::: mkpass SimplLocalsproof.match_prog
  ::: mkpass Cshmgenproof.match_prog
  ::: mkpass Cminorgenproof.match_prog
  ::: mkpass Selectionproof.match_prog
  ::: mkpass RTLgenproof.match_prog
  ::: mkpass (match_if Compopts.optim_tailcalls Tailcallproof.match_prog)
  ::: mkpass Inliningproof.match_prog
  ::: mkpass Renumberproof.match_prog
  ::: mkpass (match_if Compopts.optim_constprop Constpropproof.match_prog)
  ::: mkpass (match_if Compopts.optim_constprop Renumberproof.match_prog)
  ::: mkpass (match_if Compopts.optim_CSE CSEproof.match_prog)
  ::: mkpass (match_if Compopts.optim_redundancy Deadcodeproof.match_prog)
  ::: mkpass Unusedglobproof.match_prog
  ::: mkpass Allocproof.match_prog
  ::: mkpass Tunnelingproof.match_prog
  ::: mkpass Linearizeproof.match_prog
  ::: mkpass CleanupLabelsproof.match_prog
  ::: mkpass (match_if Compopts.debug Debugvarproof.match_prog)
  ::: mkpass Stackingproof.match_prog
  ::: mkpass Asmgenproof.match_prog
  ::: pass_nil _.
Definition match_prog: Csyntax.program -> Asm.program -> Prop.
exact (pass_match (compose_passes CompCert's_passes)).
Defined.

Theorem transf_c_program_match:
  forall p tp,
  transf_c_program p = OK tp ->
  match_prog p tp.
Admitted.

Theorem separate_transf_c_program_correct:
  forall c_units asm_units c_program,
  nlist_forall2 (fun cu tcu => transf_c_program cu = OK tcu) c_units asm_units ->
  link_list c_units = Some c_program ->
  exists asm_program,
      link_list asm_units = Some asm_program
   /\ backward_simulation (Csem.semantics c_program) (Asm.semantics asm_program).
Proof.
  intros.
  assert (nlist_forall2 match_prog c_units asm_units).
  {
 eapply nlist_forall2_imply.
eauto.
simpl; intros.
apply transf_c_program_match; auto.
}
  assert (exists asm_program, link_list asm_units = Some asm_program /\ match_prog c_program asm_program).
  {
 eapply link_list_compose_passes; eauto.
