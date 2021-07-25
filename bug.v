(* -*- mode: coq; coq-prog-args: ("-emacs" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/msl" "VST.msl" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/sepcomp" "VST.sepcomp" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/veric" "VST.veric" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/floyd" "VST.floyd" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/progs" "VST.progs" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/concurrency" "VST.concurrency" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/wand_demo" "wand_demo" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/sha" "sha" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/hmacfcf" "hmacfcf" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/tweetnacl20140427" "tweetnacl20140427" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/hmacdrbg" "hmacdrbg" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/aes" "aes" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/mailbox" "mailbox" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/atomics" "atomics" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/lib" "compcert.lib" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/common" "compcert.common" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/x86_32" "compcert.x86_32" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/x86" "compcert.x86" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/cfrontend" "compcert.cfrontend" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/vst/compcert/exportclight" "compcert.exportclight" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Flocq" "Flocq" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-top" "closed_lemmas" "-native-compiler" "no" "-native-compiler" "no") -*- *)
(* File reduced by coq-bug-finder from original input, then from 2095 lines to 10 lines, then from 233 lines to 355 lines, then from 342 lines to 9 lines, then from 228 lines to 441 lines, then from 444 lines to 10 lines, then from 209 lines to 618 lines, then from 622 lines to 46 lines, then from 244 lines to 2186 lines, then from 2185 lines to 45 lines, then from 186 lines to 1500 lines, then from 1500 lines to 125 lines, then from 265 lines to 1073 lines, then from 1076 lines to 748 lines, then from 887 lines to 1328 lines, then from 1332 lines to 750 lines, then from 886 lines to 2399 lines, then from 2377 lines to 760 lines, then from 885 lines to 1257 lines, then from 1257 lines to 877 lines, then from 1002 lines to 1435 lines, then from 1438 lines to 956 lines, then from 1042 lines to 1193 lines, then from 1195 lines to 985 lines, then from 1070 lines to 1352 lines, then from 1356 lines to 1003 lines, then from 1089 lines to 2394 lines, then from 2395 lines to 1149 lines, then from 1233 lines to 1831 lines, then from 1834 lines to 1185 lines, then from 1267 lines to 1296 lines, then from 1300 lines to 1177 lines, then from 1253 lines to 1400 lines, then from 1404 lines to 1192 lines, then from 1261 lines to 1570 lines, then from 1573 lines to 1201 lines, then from 1268 lines to 1428 lines, then from 1432 lines to 1214 lines, then from 1279 lines to 2037 lines, then from 2041 lines to 1246 lines, then from 1303 lines to 3101 lines, then from 3100 lines to 1577 lines, then from 1627 lines to 3211 lines, then from 3215 lines to 2816 lines *)
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
Require Coq.micromega.Psatz.
Require Coq.ZArith.Zquot.
Require compcert.lib.Zbits.
Require Flocq.IEEE754.Binary.
Require Flocq.IEEE754.Bits.
Require compcert.x86_32.Archi.
Require Coq.Classes.Equivalence.
Require Coq.Classes.EquivDec.
Require compcert.lib.Maps.
Require compcert.common.Errors.
Require Coq.Logic.Eqdep_dec.
Require Coq.ZArith.Zwf.
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
Require compcert.common.Values.
Require compcert.common.Memdata.
Require Coq.Logic.ClassicalFacts.
Require Coq.Logic.FunctionalExtensionality.
Require compcert.lib.Axioms.
Require compcert.common.Linking.
Module compcert_DOT_cfrontend_DOT_Ctypes_WRAPPED.
Module Ctypes.
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 

 
Import compcert.lib.Axioms compcert.lib.Coqlib compcert.lib.Maps compcert.common.Errors.
Import compcert.common.AST compcert.common.Linking.

 

 

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
Proof.
  decide equality.
Defined.

Lemma type_eq: forall (ty1 ty2: type), {ty1=ty2} + {ty1<>ty2}
with typelist_eq: forall (tyl1 tyl2: typelist), {tyl1=tyl2} + {tyl1<>tyl2}.
Proof.
  assert (forall (x y: signedness), {x=y} + {x<>y}) by decide equality.
  assert (forall (x y: floatsize), {x=y} + {x<>y}) by decide equality.
  assert (forall (x y: attr), {x=y} + {x<>y}).
  {
 decide equality.
decide equality.
apply N.eq_dec.
apply bool_dec.
}
  generalize ident_eq zeq bool_dec ident_eq intsize_eq; intros.
  decide equality.
  decide equality.
  decide equality.
  decide equality.
Defined.

Opaque type_eq typelist_eq.

 

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

 

Definition attr_union (a1 a2: attr) : attr :=
  {| attr_volatile := a1.(attr_volatile) || a2.(attr_volatile);
     attr_alignas :=
       match a1.(attr_alignas), a2.(attr_alignas) with
       | None, al => al
       | al, None => al
       | Some n1, Some n2 => Some (N.max n1 n2)
       end
  |}.

Definition merge_attributes (ty: type) (a: attr) : type :=
  change_attributes (attr_union a) ty.

 

Inductive struct_or_union : Type := Struct | Union.

Definition members : Type := list (ident * type).

Inductive composite_definition : Type :=
  Composite (id: ident) (su: struct_or_union) (m: members) (a: attr).

Definition name_composite_def (c: composite_definition) : ident :=
  match c with Composite id su m a => id end.

Definition composite_def_eq (x y: composite_definition): {x=y} + {x<>y}.
Proof.
  decide equality.
-
 decide equality.
decide equality.
apply N.eq_dec.
apply bool_dec.
-
 apply list_eq_dec.
decide equality.
apply type_eq.
apply ident_eq.
-
 decide equality.
-
 apply ident_eq.
Defined.

Global Opaque composite_def_eq.

 

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

 

 

Definition type_int32s := Tint I32 Signed noattr.
Definition type_bool := Tint IBool Signed noattr.

 

Definition typeconv (ty: type) : type :=
  match ty with
  | Tint (I8 | I16 | IBool) _ _ => Tint I32 Signed noattr
  | Tarray t sz a       => Tpointer t noattr
  | Tfunction _ _ _     => Tpointer ty noattr
  | _                   => remove_attributes ty
  end.

 

Definition default_argument_conversion (ty: type) : type :=
  match ty with
  | Tint (I8 | I16 | IBool) _ _ => Tint I32 Signed noattr
  | Tfloat _ _          => Tfloat F64 noattr
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

Definition complete_or_function_type (env: composite_env) (t: type) : bool :=
  match t with
  | Tfunction _ _ _ => true
  | _ => complete_type env t
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

Remark align_attr_two_p:
  forall al a,
  (exists n, al = two_power_nat n) ->
  (exists n, align_attr a al = two_power_nat n).
Proof.
  intros.
unfold align_attr.
destruct (attr_alignas a).
  exists (N.to_nat n).
rewrite two_power_nat_two_p.
rewrite N_nat_Z.
auto.
  auto.
Qed.

Lemma alignof_two_p:
  forall env t, exists n, alignof env t = two_power_nat n.
Proof.
  induction t; apply align_attr_two_p; simpl.
  exists 0%nat; auto.
  destruct i.
    exists 0%nat; auto.
    exists 1%nat; auto.
    exists 2%nat; auto.
    exists 0%nat; auto.
    unfold Archi.align_int64.
destruct Archi.ptr64; ((exists 2%nat; reflexivity) || (exists 3%nat; reflexivity)).
  destruct f.
    exists 2%nat; auto.
    unfold Archi.align_float64.
destruct Archi.ptr64; ((exists 2%nat; reflexivity) || (exists 3%nat; reflexivity)).
  exists (if Archi.ptr64 then 3%nat else 2%nat); destruct Archi.ptr64; auto.
  apply IHt.
  exists 0%nat; auto.
  destruct (env!i).
apply co_alignof_two_p.
exists 0%nat; auto.
  destruct (env!i).
apply co_alignof_two_p.
exists 0%nat; auto.
Qed.

Lemma alignof_pos:
  forall env t, alignof env t > 0.
Proof.
  intros.
destruct (alignof_two_p env t) as [n EQ].
rewrite EQ.
apply two_power_nat_pos.
Qed.

 

 

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

Lemma sizeof_pos:
  forall env t, sizeof env t >= 0.
admit.
Defined.

 

Fixpoint naturally_aligned (t: type) : Prop :=
  attr_alignas (attr_of_type t) = None /\
  match t with
  | Tarray t' _ _ => naturally_aligned t'
  | _ => True
  end.

Lemma sizeof_alignof_compat:
  forall env t, naturally_aligned t -> (alignof env t | sizeof env t).
admit.
Defined.

 

 

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

Lemma alignof_composite_two_p:
  forall env m, exists n, alignof_composite env m = two_power_nat n.
admit.
Defined.

Lemma alignof_composite_pos:
  forall env m a, align_attr a (alignof_composite env m) > 0.
admit.
Defined.

Lemma sizeof_struct_incr:
  forall env m cur, cur <= sizeof_struct env cur m.
admit.
Defined.

Lemma sizeof_union_pos:
  forall env m, 0 <= sizeof_union env m.
admit.
Defined.

 

 

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

 

Remark field_offset_rec_in_range:
  forall env id ofs ty fld pos,
  field_offset_rec env id fld pos = OK ofs -> field_type id fld = OK ty ->
  pos <= ofs /\ ofs + sizeof env ty <= sizeof_struct env pos fld.
admit.
Defined.

Lemma field_offset_in_range:
  forall env fld id ofs ty,
  field_offset env id fld = OK ofs -> field_type id fld = OK ty ->
  0 <= ofs /\ ofs + sizeof env ty <= sizeof_struct env 0 fld.
admit.
Defined.

 

Lemma field_offset_no_overlap:
  forall env id1 ofs1 ty1 id2 ofs2 ty2 fld,
  field_offset env id1 fld = OK ofs1 -> field_type id1 fld = OK ty1 ->
  field_offset env id2 fld = OK ofs2 -> field_type id2 fld = OK ty2 ->
  id1 <> id2 ->
  ofs1 + sizeof env ty1 <= ofs2 \/ ofs2 + sizeof env ty2 <= ofs1.
admit.
Defined.

 

Lemma field_offset_prefix:
  forall env id ofs fld2 fld1,
  field_offset env id fld1 = OK ofs ->
  field_offset env id (fld1 ++ fld2) = OK ofs.
admit.
Defined.

 

Lemma field_offset_aligned:
  forall env id fld ofs ty,
  field_offset env id fld = OK ofs -> field_type id fld = OK ty ->
  (alignof env ty | ofs).
admit.
Defined.

 

 

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

 

 

Fixpoint alignof_blockcopy (env: composite_env) (t: type) : Z :=
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
  | Tarray t' _ _ => alignof_blockcopy env t'
  | Tfunction _ _ _ => 1
  | Tstruct id _ | Tunion id _ =>
      match env!id with
      | Some co => Z.min 8 (co_alignof co)
      | None => 1
      end
  end.

Lemma alignof_blockcopy_1248:
  forall env ty, let a := alignof_blockcopy env ty in a = 1 \/ a = 2 \/ a = 4 \/ a = 8.
admit.
Defined.

Lemma alignof_blockcopy_pos:
  forall env ty, alignof_blockcopy env ty > 0.
admit.
Defined.

Lemma sizeof_alignof_blockcopy_compat:
  forall env ty, (alignof_blockcopy env ty | sizeof env ty).
admit.
Defined.

 

 

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

 

 

Fixpoint type_of_params (params: list (ident * type)) : typelist :=
  match params with
  | nil => Tnil
  | (id, ty) :: rem => Tcons ty (type_of_params rem)
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

Definition rettype_of_type (t: type) : AST.rettype :=
  match t with
  | Tvoid => AST.Tvoid
  | Tint I32 _ _ => AST.Tint
  | Tint I8 Signed _ => AST.Tint8signed
  | Tint I8 Unsigned _ => AST.Tint8unsigned
  | Tint I16 Signed _ => AST.Tint16signed
  | Tint I16 Unsigned _ => AST.Tint16unsigned
  | Tint IBool _ _ => AST.Tint8unsigned
  | Tlong _ _ => AST.Tlong
  | Tfloat F32 _ => AST.Tsingle
  | Tfloat F64 _ => AST.Tfloat
  | Tpointer _ _ => AST.Tptr
  | Tarray _ _ _ | Tfunction _ _ _ | Tstruct _ _ | Tunion _ _ => AST.Tvoid
  end.

Fixpoint typlist_of_typelist (tl: typelist) : list AST.typ :=
  match tl with
  | Tnil => nil
  | Tcons hd tl => typ_of_type hd :: typlist_of_typelist tl
  end.

Definition signature_of_type (args: typelist) (res: type) (cc: calling_convention): signature :=
  mksignature (typlist_of_typelist args) (rettype_of_type res) cc.

 

Definition sizeof_composite (env: composite_env) (su: struct_or_union) (m: members) : Z :=
  match su with
  | Struct => sizeof_struct env 0 m
  | Union  => sizeof_union env m
  end.

Lemma sizeof_composite_pos:
  forall env su m, 0 <= sizeof_composite env su m.
admit.
Defined.

Fixpoint complete_members (env: composite_env) (m: members) : bool :=
  match m with
  | nil => true
  | (id, t) :: m' => complete_type env t && complete_members env m'
  end.

Lemma complete_member:
  forall env id t m,
  In (id, t) m -> complete_members env m = true -> complete_type env t = true.
admit.
Defined.

 

Program Definition composite_of_def
     (env: composite_env) (id: ident) (su: struct_or_union) (m: members) (a: attr)
     : res composite :=
  match env!id, complete_members env m return _ with
  | Some _, _ =>
      Error (MSG "Multiple definitions of struct or union " :: CTX id :: nil)
  | None, false =>
      Error (MSG "Incomplete struct or union " :: CTX id :: nil)
  | None, true =>
      let al := align_attr a (alignof_composite env m) in
      OK {| co_su := su;
            co_members := m;
            co_attr := a;
            co_sizeof := align (sizeof_composite env su m) al;
            co_alignof := al;
            co_rank := rank_members env m;
            co_sizeof_pos := _;
            co_alignof_two_p := _;
            co_sizeof_alignof := _ |}
  end.
Next Obligation.
  apply Z.le_ge.
eapply Z.le_trans.
eapply sizeof_composite_pos.
  apply align_le; apply alignof_composite_pos.
Defined.
Next Obligation.
  apply align_attr_two_p.
apply alignof_composite_two_p.
Defined.
Next Obligation.
  apply align_divides.
apply alignof_composite_pos.
Defined.

 

Local Open Scope error_monad_scope.

Fixpoint add_composite_definitions (env: composite_env) (defs: list composite_definition) : res composite_env :=
  match defs with
  | nil => OK env
  | Composite id su m a :: defs =>
      do co <- composite_of_def env id su m a;
      add_composite_definitions (PTree.set id co env) defs
  end.

Definition build_composite_env (defs: list composite_definition) :=
  add_composite_definitions (PTree.empty _) defs.

 

Section STABILITY.

Variables env env': composite_env.
Hypothesis extends: forall id co, env!id = Some co -> env'!id = Some co.

Lemma alignof_stable:
  forall t, complete_type env t = true -> alignof env' t = alignof env t.
admit.
Defined.

Lemma sizeof_stable:
  forall t, complete_type env t = true -> sizeof env' t = sizeof env t.
admit.
Defined.

Lemma complete_type_stable:
  forall t, complete_type env t = true -> complete_type env' t = true.
admit.
Defined.

Lemma rank_type_stable:
  forall t, complete_type env t = true -> rank_type env' t = rank_type env t.
admit.
Defined.

Lemma alignof_composite_stable:
  forall m, complete_members env m = true -> alignof_composite env' m = alignof_composite env m.
admit.
Defined.

Lemma sizeof_struct_stable:
  forall m pos, complete_members env m = true -> sizeof_struct env' pos m = sizeof_struct env pos m.
admit.
Defined.

Lemma sizeof_union_stable:
  forall m, complete_members env m = true -> sizeof_union env' m = sizeof_union env m.
admit.
Defined.

Lemma sizeof_composite_stable:
  forall su m, complete_members env m = true -> sizeof_composite env' su m = sizeof_composite env su m.
admit.
Defined.

Lemma complete_members_stable:
  forall m, complete_members env m = true -> complete_members env' m = true.
admit.
Defined.

Lemma rank_members_stable:
  forall m, complete_members env m = true -> rank_members env' m = rank_members env m.
admit.
Defined.

End STABILITY.

Lemma add_composite_definitions_incr:
  forall id co defs env1 env2,
  add_composite_definitions env1 defs = OK env2 ->
  env1!id = Some co -> env2!id = Some co.
admit.
Defined.

 

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

Lemma composite_consistent_stable:
  forall (env env': composite_env)
         (EXTENDS: forall id co, env!id = Some co -> env'!id = Some co)
         co,
  composite_consistent env co -> composite_consistent env' co.
admit.
Defined.

Lemma composite_of_def_consistent:
  forall env id su m a co,
  composite_of_def env id su m a = OK co ->
  composite_consistent env co.
admit.
Defined.

Theorem build_composite_env_consistent:
  forall defs env, build_composite_env defs = OK env -> composite_env_consistent env.
admit.
Defined.

 

Theorem build_composite_env_charact:
  forall id su m a defs env,
  build_composite_env defs = OK env ->
  In (Composite id su m a) defs ->
  exists co, env!id = Some co /\ co_members co = m /\ co_attr co = a /\ co_su co = su.
admit.
Defined.

Theorem build_composite_env_domain:
  forall env defs id co,
  build_composite_env defs = OK env ->
  env!id = Some co ->
  In (Composite id (co_su co) (co_members co) (co_attr co)) defs.
admit.
Defined.

 

Remark rank_type_members:
  forall ce id t m, In (id, t) m -> (rank_type ce t <= rank_members ce m)%nat.
admit.
Defined.

Lemma rank_struct_member:
  forall ce id a co id1 t1,
  composite_env_consistent ce ->
  ce!id = Some co ->
  In (id1, t1) (co_members co) ->
  (rank_type ce t1 < rank_type ce (Tstruct id a))%nat.
admit.
Defined.

Lemma rank_union_member:
  forall ce id a co id1 t1,
  composite_env_consistent ce ->
  ce!id = Some co ->
  In (id1, t1) (co_members co) ->
  (rank_type ce t1 < rank_type ce (Tunion id a))%nat.
admit.
Defined.

 

 

Set Implicit Arguments.

Section PROGRAMS.

Variable F: Type.

 

Inductive fundef : Type :=
  | Internal: F -> fundef
  | External: external_function -> typelist -> type -> calling_convention -> fundef.

 

Record program : Type := {
  prog_defs: list (ident * globdef fundef type);
  prog_public: list ident;
  prog_main: ident;
  prog_types: list composite_definition;
  prog_comp_env: composite_env;
  prog_comp_env_eq: build_composite_env prog_types = OK prog_comp_env
}.

Definition program_of_program (p: program) : AST.program fundef type :=
  {| AST.prog_defs := p.(prog_defs);
     AST.prog_public := p.(prog_public);
     AST.prog_main := p.(prog_main) |}.

Coercion program_of_program: program >-> AST.program.

Program Definition make_program (types: list composite_definition)
                                (defs: list (ident * globdef fundef type))
                                (public: list ident)
                                (main: ident) : res program :=
  match build_composite_env types with
  | Error e => Error e
  | OK ce =>
      OK {| prog_defs := defs;
            prog_public := public;
            prog_main := main;
            prog_types := types;
            prog_comp_env := ce;
            prog_comp_env_eq := _ |}
  end.

End PROGRAMS.

Arguments External {F} _ _ _ _.

Unset Implicit Arguments.

 

 

Program Instance Linker_types : Linker type := {
  link := fun t1 t2 => if type_eq t1 t2 then Some t1 else None;
  linkorder := fun t1 t2 => t1 = t2
}.
Next Obligation.
  destruct (type_eq x y); inv H.
auto.
Defined.

Global Opaque Linker_types.

 

Definition check_compat_composite (l: list composite_definition) (cd: composite_definition) : bool :=
  List.forallb
    (fun cd' =>
      if ident_eq (name_composite_def cd') (name_composite_def cd) then composite_def_eq cd cd' else true)
    l.

Definition filter_redefs (l1 l2: list composite_definition) :=
  let names1 := map name_composite_def l1 in
  List.filter (fun cd => negb (In_dec ident_eq (name_composite_def cd) names1)) l2.

Definition link_composite_defs (l1 l2: list composite_definition): option (list composite_definition) :=
  if List.forallb (check_compat_composite l2) l1
  then Some (l1 ++ filter_redefs l1 l2)
  else None.

Lemma link_composite_def_inv:
  forall l1 l2 l,
  link_composite_defs l1 l2 = Some l ->
     (forall cd1 cd2, In cd1 l1 -> In cd2 l2 -> name_composite_def cd2 = name_composite_def cd1 -> cd2 = cd1)
  /\ l = l1 ++ filter_redefs l1 l2
  /\ (forall x, In x l <-> In x l1 \/ In x l2).
admit.
Defined.

Program Instance Linker_composite_defs : Linker (list composite_definition) := {
  link := link_composite_defs;
  linkorder := @List.incl composite_definition
}.
Next Obligation.
  apply incl_refl.
Defined.
Next Obligation.
  red; intros; eauto.
Defined.
Next Obligation.
  apply link_composite_def_inv in H; destruct H as (A & B & C).
  split; red; intros; apply C; auto.
Defined.

 

Lemma add_composite_definitions_append:
  forall l1 l2 env env'',
  add_composite_definitions env (l1 ++ l2) = OK env'' <->
  exists env', add_composite_definitions env l1 = OK env' /\ add_composite_definitions env' l2 = OK env''.
admit.
Defined.

Lemma composite_eq:
  forall su1 m1 a1 sz1 al1 r1 pos1 al2p1 szal1
         su2 m2 a2 sz2 al2 r2 pos2 al2p2 szal2,
  su1 = su2 -> m1 = m2 -> a1 = a2 -> sz1 = sz2 -> al1 = al2 -> r1 = r2 ->
  Build_composite su1 m1 a1 sz1 al1 r1 pos1 al2p1 szal1 = Build_composite su2 m2 a2 sz2 al2 r2 pos2 al2p2 szal2.
admit.
Defined.

Lemma composite_of_def_eq:
  forall env id co,
  composite_consistent env co ->
  env!id = None ->
  composite_of_def env id (co_su co) (co_members co) (co_attr co) = OK co.
admit.
Defined.

Lemma composite_consistent_unique:
  forall env co1 co2,
  composite_consistent env co1 ->
  composite_consistent env co2 ->
  co_su co1 = co_su co2 ->
  co_members co1 = co_members co2 ->
  co_attr co1 = co_attr co2 ->
  co1 = co2.
admit.
Defined.

Lemma composite_of_def_stable:
  forall (env env': composite_env)
         (EXTENDS: forall id co, env!id = Some co -> env'!id = Some co)
         id su m a co,
  env'!id = None ->
  composite_of_def env id su m a = OK co ->
  composite_of_def env' id su m a = OK co.
admit.
Defined.

Lemma link_add_composite_definitions:
  forall l0 env0,
  build_composite_env l0 = OK env0 ->
  forall l env1 env1' env2,
  add_composite_definitions env1 l = OK env1' ->
  (forall id co, env1!id = Some co -> env2!id = Some co) ->
  (forall id co, env0!id = Some co -> env2!id = Some co) ->
  (forall id, env2!id = if In_dec ident_eq id (map name_composite_def l0) then env0!id else env1!id) ->
  ((forall cd1 cd2, In cd1 l0 -> In cd2 l -> name_composite_def cd2 = name_composite_def cd1 -> cd2 = cd1)) ->
  { env2' |
      add_composite_definitions env2 (filter_redefs l0 l) = OK env2'
  /\ (forall id co, env1'!id = Some co -> env2'!id = Some co)
  /\ (forall id co, env0!id = Some co -> env2'!id = Some co) }.
admit.
Defined.

Theorem link_build_composite_env:
  forall l1 l2 l env1 env2,
  build_composite_env l1 = OK env1 ->
  build_composite_env l2 = OK env2 ->
  link l1 l2 = Some l ->
  { env |
     build_composite_env l = OK env
  /\ (forall id co, env1!id = Some co -> env!id = Some co)
  /\ (forall id co, env2!id = Some co -> env!id = Some co) }.
admit.
Defined.

 

Definition link_fundef {F: Type} (fd1 fd2: fundef F) :=
  match fd1, fd2 with
  | Internal _, Internal _ => None
  | External ef1 targs1 tres1 cc1, External ef2 targs2 tres2 cc2 =>
      if external_function_eq ef1 ef2
      && typelist_eq targs1 targs2
      && type_eq tres1 tres2
      && calling_convention_eq cc1 cc2
      then Some (External ef1 targs1 tres1 cc1)
      else None
  | Internal f, External ef targs tres cc =>
      match ef with EF_external id sg => Some (Internal f) | _ => None end
  | External ef targs tres cc, Internal f =>
      match ef with EF_external id sg => Some (Internal f) | _ => None end
  end.

Inductive linkorder_fundef {F: Type}: fundef F -> fundef F -> Prop :=
  | linkorder_fundef_refl: forall fd,
      linkorder_fundef fd fd
  | linkorder_fundef_ext_int: forall f id sg targs tres cc,
      linkorder_fundef (External (EF_external id sg) targs tres cc) (Internal f).

Program Instance Linker_fundef (F: Type): Linker (fundef F) := {
  link := link_fundef;
  linkorder := linkorder_fundef
}.
Next Obligation.
  constructor.
Defined.
Next Obligation.
  inv H; inv H0; constructor.
Defined.
Next Obligation.
  destruct x, y; simpl in H.
+
 discriminate.
+
 destruct e; inv H.
split; constructor.
+
 destruct e; inv H.
split; constructor.
+
 destruct (external_function_eq e e0 && typelist_eq t t1 && type_eq t0 t2 && calling_convention_eq c c0) eqn:A; inv H.
  InvBooleans.
subst.
split; constructor.
Defined.

Remark link_fundef_either:
  forall (F: Type) (f1 f2 f: fundef F), link f1 f2 = Some f -> f = f1 \/ f = f2.
admit.
Defined.

Global Opaque Linker_fundef.

 

Definition lift_option {A: Type} (opt: option A) : { x | opt = Some x } + { opt = None }.
Proof.
  destruct opt.
left; exists a; auto.
right; auto.
Defined.

Definition link_program {F:Type} (p1 p2: program F): option (program F) :=
  match link (program_of_program p1) (program_of_program p2) with
  | None => None
  | Some p =>
      match lift_option (link p1.(prog_types) p2.(prog_types)) with
      | inright _ => None
      | inleft (exist typs EQ) =>
          match link_build_composite_env
                   p1.(prog_types) p2.(prog_types) typs
                   p1.(prog_comp_env) p2.(prog_comp_env)
                   p1.(prog_comp_env_eq) p2.(prog_comp_env_eq) EQ with
          | exist env (conj P Q) =>
              Some {| prog_defs := p.(AST.prog_defs);
                      prog_public := p.(AST.prog_public);
                      prog_main := p.(AST.prog_main);
                      prog_types := typs;
                      prog_comp_env := env;
                      prog_comp_env_eq := P |}
          end
      end
  end.

Definition linkorder_program {F: Type} (p1 p2: program F) : Prop :=
     linkorder (program_of_program p1) (program_of_program p2)
  /\ (forall id co, p1.(prog_comp_env)!id = Some co -> p2.(prog_comp_env)!id = Some co).

Program Instance Linker_program (F: Type): Linker (program F) := {
  link := link_program;
  linkorder := linkorder_program
}.
Next Obligation.
  split.
apply linkorder_refl.
auto.
Defined.
Next Obligation.
  destruct H, H0.
split.
eapply linkorder_trans; eauto.
  intros; auto.
Defined.
Next Obligation.
  revert H.
unfold link_program.
  destruct (link (program_of_program x) (program_of_program y)) as [p|] eqn:LP; try discriminate.
  destruct (lift_option (link (prog_types x) (prog_types y))) as [[typs EQ]|EQ]; try discriminate.
  destruct (link_build_composite_env (prog_types x) (prog_types y) typs
       (prog_comp_env x) (prog_comp_env y) (prog_comp_env_eq x)
       (prog_comp_env_eq y) EQ) as (env & P & Q & R).
  destruct (link_linkorder _ _ _ LP).
  intros X; inv X.
  split; split; auto.
Defined.

Global Opaque Linker_program.

 

Section LINK_MATCH_PROGRAM.

Context {F G: Type}.
Variable match_fundef: fundef F -> fundef G -> Prop.

Hypothesis link_match_fundef:
  forall f1 tf1 f2 tf2 f,
  link f1 f2 = Some f ->
  match_fundef f1 tf1 -> match_fundef f2 tf2 ->
  exists tf, link tf1 tf2 = Some tf /\ match_fundef f tf.

Let match_program (p: program F) (tp: program G) : Prop :=
    Linking.match_program (fun ctx f tf => match_fundef f tf) eq p tp
 /\ prog_types tp = prog_types p.

Theorem link_match_program:
  forall p1 p2 tp1 tp2 p,
  link p1 p2 = Some p -> match_program p1 tp1 -> match_program p2 tp2 ->
  exists tp, link tp1 tp2 = Some tp /\ match_program p tp.
admit.
Defined.

End LINK_MATCH_PROGRAM.

End Ctypes.

End compcert_DOT_cfrontend_DOT_Ctypes_WRAPPED.
Module Export compcert_DOT_cfrontend_DOT_Ctypes.
Module Export compcert.
Module Export cfrontend.
Module Ctypes.
Include compcert_DOT_cfrontend_DOT_Ctypes_WRAPPED.Ctypes.
End Ctypes.

End cfrontend.

End compcert.

End compcert_DOT_cfrontend_DOT_Ctypes.

Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.
Module Export Cop.

Import compcert.lib.Coqlib.
Import compcert.common.AST.
Import compcert.lib.Integers.
Import compcert.lib.Floats.
Import compcert.common.Values.
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
Export compcert.lib.Maps.

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
