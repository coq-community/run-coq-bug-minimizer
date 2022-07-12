(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "-notation-overridden" "-w" "-extraction-reserved-identifier" "-w" "-extraction-opaque-accessed" "-w" "-ambiguous-paths" "-w" "-duplicate-clear" "-w" "-deprecated-hint-without-locality" "-w" "-deprecated-hint-rewrite-without-locality" "-w" "-deprecated-instance-without-locality" "-w" "-deprecated-native-compiler-option" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/jasmin/proofs/3rdparty" "Jasmin" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/jasmin/proofs/arch" "Jasmin" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/jasmin/proofs/compiler" "Jasmin" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/jasmin/proofs/lang" "Jasmin" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/jasmin/proofs/ssrmisc" "Jasmin" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/CoqWord" "CoqWord" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/mathcomp" "mathcomp" "-top" "tunneling_proof" "-native-compiler" "no") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 1590 lines to 15 lines, then from 28 lines to 275 lines, then from 274 lines to 85 lines, then from 98 lines to 516 lines, then from 515 lines to 136 lines, then from 149 lines to 605 lines, then from 600 lines to 147 lines, then from 160 lines to 334 lines, then from 339 lines to 179 lines, then from 192 lines to 323 lines, then from 328 lines to 183 lines, then from 196 lines to 367 lines, then from 372 lines to 193 lines, then from 206 lines to 1355 lines, then from 1360 lines to 308 lines, then from 321 lines to 470 lines, then from 473 lines to 310 lines, then from 323 lines to 627 lines, then from 632 lines to 362 lines, then from 375 lines to 1134 lines, then from 1137 lines to 411 lines, then from 424 lines to 561 lines, then from 566 lines to 420 lines, then from 433 lines to 1085 lines, then from 1090 lines to 983 lines *)
(* coqc version 8.17+alpha compiled with OCaml 4.14.0
   coqtop version runner-j2nyww-s-project-6138686-concurrent-0:/builds/coq/coq/_build/default,(HEAD detached at 3721187) (3721187d6f240344abae25acb1ace86ff72c88c2)
   Expected coqc runtime on this file: 3.862 sec *)
Require Coq.Setoids.Setoid.
Require Coq.Classes.Morphisms.
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
Require Coq.ZArith.ZArith.
Require Coq.Strings.String.
Require Coq.Unicode.Utf8.
Require Coq.Classes.CMorphisms.
Require Coq.Classes.CRelationClasses.
Require Jasmin.xseq.
Require Jasmin.oseq.
Require Coq.micromega.Psatz.
Require Coq.Arith.Arith.
Require CoqWord.ssrZ.
Require Jasmin.utils.
Require Coq.FSets.FMaps.
Require Coq.FSets.FMapAVL.
Require Coq.FSets.FSetAVL.
Require Coq.MSets.MSets.
Require Jasmin.gen_map.
Require Jasmin.strings.
Require Jasmin.wsize.
Require Jasmin.type.
Require Jasmin.ident.
Require Jasmin.var.
Require Jasmin.array.
Require CoqWord.word.
Require Coq.NArith.NArith.
Require Coq.setoid_ring.Ring_polynom.
Require Jasmin.ssrring.
Require Coq.ZArith.Zquot.
Require Jasmin.word.
Require Coq.Classes.RelationClasses.
Require Jasmin.memory_model.
Require Jasmin.memory_example.
Require Coq.micromega.Lia.
Require Jasmin.low_memory.

Declare ML Module "coq-core.plugins.ltac".
Module Export AdmitTactic.
Module Import LocalFalse.
Inductive False : Prop := .
End LocalFalse.
Axiom proof_admitted : False.
Global Set Default Proof Mode "Classic".
Tactic Notation "admit" := abstract case proof_admitted.
End AdmitTactic.

Module Export Jasmin_DOT_warray_.
Module Export Jasmin.
Module warray_.
 

 
Export Coq.ZArith.ZArith Coq.Setoids.Setoid Coq.Classes.Morphisms.
Import mathcomp.ssreflect.all_ssreflect mathcomp.algebra.all_algebra.
Import CoqWord.ssrZ.
Import Coq.micromega.Psatz Jasmin.xseq.
Export Jasmin.utils Jasmin.array Jasmin.gen_map Jasmin.type Jasmin.word Jasmin.low_memory.
Import Coq.Unicode.Utf8 Coq.ZArith.ZArith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Variant arr_access :=
  | AAdirect
  | AAscale.

Scheme Equality for arr_access.

Lemma arr_access_eq_axiom : Equality.axiom arr_access_beq.
Proof.
  move=> x y;apply:(iffP idP).
  +
 by apply: internal_arr_access_dec_bl.
  by apply: internal_arr_access_dec_lb.
Qed.

Definition arr_access_eqMixin     := Equality.Mixin arr_access_eq_axiom.
Canonical  arr_access_eqType      := Eval hnf in EqType arr_access arr_access_eqMixin.

Local Open Scope Z_scope.

Definition arr_size (ws:wsize) (len:positive)  :=
   (wsize_size ws * len).

Lemma arr_sizeE ws len : arr_size ws len = (wsize_size ws * len).
Proof.
done.
Qed.

Lemma ge0_arr_size ws len : 0 <= arr_size ws len.
Proof.
rewrite arr_sizeE; have := wsize_size_pos ws; nia.
Qed.

Opaque arr_size.

Definition mk_scale (aa:arr_access) ws :=
  if aa is AAscale then wsize_size ws else 1.

Module WArray.

  Record array (s:positive)  :=
    { arr_data : Mz.t u8 }.

  Definition empty (s:positive) : array s :=
    {| arr_data := Mz.empty _ |}.

  Local Notation pointer := [eqType of Z].

   
  Instance PointerZ : pointer_op pointer | 1.
  Proof.
    refine {| add x y := (x + y)%Z
            ; sub x y := (x - y)%Z
            ; p_to_z x := x        |}.
    -
 abstract (move => /= ??; ring).
    -
 abstract (move => /= ???; ring).
    -
 abstract (move => /= ?; ring).
  Defined.

  Lemma addE x y : add x y = (x + y)%Z.
  Proof.
by [].
Qed.

  Lemma subE x y : sub x y = (x - y)%Z.
  Proof.
by [].
Qed.

  Lemma p_to_zE x : p_to_z x = x.
  Proof.
by [].
Qed.

  Global Opaque PointerZ.

  Section WITH_POINTER_DATA.
  Context {pd: PointerData}.

  Lemma is_align_scale (p:pointer) ws : is_align (p * mk_scale AAscale ws)%Z ws.
  Proof.
by rewrite /is_align /mk_scale /= Z_mod_mult.
Qed.

  Lemma arr_is_align i ws :
    is_align (wrepr Uptr i) ws = is_align i ws.
  Proof.
    by rewrite /is_align p_to_zE memory_model.p_to_zE wunsigned_repr mod_wbase_wsize_size.
  Qed.

  Section CM.
    Variable (s:positive).

    Definition in_bound (_:array s) p := (0 <=? p) && (p <? s).

    Lemma in_boundP m p : reflect (0 <= p < s) (in_bound m p).
    Proof.
by apply (iffP andP); rewrite !zify.
Qed.

    Definition is_init (m:array s) (i:pointer) :=
      match Mz.get m.(arr_data) i with
      | Some _ => true
      | None   => false
      end.

    Definition get8 (m:array s) (i:pointer) :=
      Let _ := assert (in_bound m i) ErrOob in
      Let _ := assert (is_init m i) ErrAddrUndef in
      ok (odflt 0%R (Mz.get m.(arr_data) i)).

    Definition set8 (m:array s) (i:pointer) (v:u8) : result _ (array s):=
      Let _ := assert (in_bound m i) ErrOob in
      ok {| arr_data := Mz.set m.(arr_data) i v |}.

    Lemma valid8P m p w : reflect (exists m', set8 m p w = ok m') (in_bound m p).
    Proof.
      by (rewrite /set8; case: in_bound => /=; constructor); [eexists; eauto | move=> []].
    Qed.

    Lemma get_valid8 m p w : get8 m p = ok w -> in_bound m p.
    Proof.
by rewrite /get8; t_xrbindP.
Qed.

    Lemma valid8_set m p w m' p' : set8 m p w = ok m' -> in_bound m' p' = in_bound m p'.
    Proof.
by rewrite /set8; t_xrbindP => _ <-.
Qed.

    Lemma set8P m p w p' m' :
      set8 m p w = ok m' ->
      get8 m' p' = if p == p' then ok w else get8 m p'.
    Proof.
      rewrite /get8 /set8 => /dup[] /valid8_set ->; t_xrbindP => hb <-.
      case heq: in_bound => //=; last by case: eqP => // h;move: heq; rewrite -h hb.
      by rewrite /is_init /= Mz.setP; case: eqP.
    Qed.

    Global Instance array_CM : coreMem pointer (array s) :=
      CoreMem set8P valid8P get_valid8 valid8_set.

    Definition in_range (p:pointer) (ws:wsize) :=
      ((0 <=? p) && (p + wsize_size ws <=? s))%Z.

    Lemma in_rangeP p ws:
      reflect (0 <= p /\ p + wsize_size ws <= s)%Z (in_range p ws).
    Proof.
      rewrite /in_range; case: andP => h; constructor; move: h; rewrite !zify; Psatz.nia.
    Qed.

    Lemma validw_in_range m p ws : validw m p ws = (is_align p ws && in_range p ws).
    Proof.
      apply (sameP (validwP m p ws)).
      apply (iffP andP).
      +
 move=> [] ? /in_rangeP ?;split => // k hk.
        by rewrite -valid8_validw /valid8 /= /in_bound !zify !addE; Psatz.lia.
      move=> [] ? h; split => //; apply /in_rangeP.
      move: (wsize_size_pos ws) (h 0) (h (wsize_size ws - 1)).
      by rewrite add_0 addE -!valid8_validw /array_CM /valid8 /in_bound !zify; Psatz.lia.
    Qed.

  End CM.

  Definition get len (aa:arr_access) ws (a:array len) (p:Z) :=
    CoreMem.read a (p * mk_scale aa ws)%Z ws.

  Definition set {len ws} (a:array len) aa p (v:word ws) : exec (array len) :=
    CoreMem.write a (p * mk_scale aa ws)%Z v.

  Definition fcopy ws len (a t: WArray.array len) i j :=
    foldM (fun i t =>
             Let w := get AAscale ws a i in set t AAscale i w) t
          (ziota i j).

  Definition copy ws p (a:array (Z.to_pos (arr_size ws p))) :=
    fcopy ws a (WArray.empty _) 0 p.

  Definition fill len (l:list u8) : exec (array len) :=
    Let _ := assert (Pos.to_nat len == size l) ErrType in
    Let pt :=
      foldM (fun w pt =>
             Let t := set pt.2 AAscale pt.1 w in
             ok (pt.1 + 1, t)) (0%Z, empty len) l in
    ok pt.2.

  Definition get_sub_data (aa:arr_access) ws len (a:Mz.t u8) p :=
     let size := arr_size ws len in
     let start := (p * mk_scale aa ws)%Z in
     foldr (fun i data =>
       match Mz.get a (start + i) with
       | None => Mz.remove data i
       | Some w => Mz.set data i w
       end) (Mz.empty _) (ziota 0 size).

  Definition get_sub lena (aa:arr_access) ws len (a:array lena) p  : exec (array (Z.to_pos (arr_size ws len))) :=
     let size := arr_size ws len in
     let start := (p * mk_scale aa ws)%Z in
     if (0 <=? start) && (start + size <=? lena) then
       ok (Build_array (Z.to_pos size) (get_sub_data aa ws len (arr_data a) p))
     else Error ErrOob.

  Definition set_sub_data (aa:arr_access) ws len (a:Mz.t u8) p (b:Mz.t u8) :=
    let size := arr_size ws len in
    let start := (p * mk_scale aa ws)%Z in
    foldr (fun i data =>
      match Mz.get b i with
      | None => Mz.remove data (start + i)
      | Some w => Mz.set data (start + i) w
      end) a (ziota 0 size).

  Definition set_sub lena (aa:arr_access) ws len (a:array lena) p (b:array (Z.to_pos (arr_size ws len))) : exec (array lena) :=
    let size := arr_size ws len in
    let start := (p * mk_scale aa ws)%Z in
    if (0 <=? start) && (start + size <=? lena) then
      ok (Build_array lena (set_sub_data aa ws len (arr_data a) p (arr_data b)))
    else Error ErrOob.

  Definition cast len len' (a:array len) : result error (array len') :=
    if (len' <=? len)%Z then ok {| arr_data := a.(arr_data) |}
    else type_error.

  Definition uincl {len1 len2} (a1 : array len1) (a2 : array len2) :=
    (len1 <= len2)%Z /\
    ∀ i w, read a1 i U8 = ok w -> read a2 i U8 = ok w.

  Lemma uincl_refl len (a: array len) : uincl a a.
  Proof.
by split => //; reflexivity.
Qed.

  Lemma uincl_trans {len1 len2 len3}
    (a2: array len2) (a1: array len1) (a3: array len3) :
    uincl a1 a2 -> uincl a2 a3 -> uincl a1 a3.
  Proof.
    move=> [l1 h1] [l2 h2]; split; first by lia.
    by move=> ?? /h1 /h2.
  Qed.

  End WITH_POINTER_DATA.

  Lemma castK len (a:array len) : WArray.cast len a = ok a.
  Proof.
by rewrite /cast Z.leb_refl; case: a.
Qed.

  Lemma cast_len len1 len2 (t2:WArray.array len2) t1: WArray.cast len1 t2 = ok t1 -> len1 <= len2.
  Proof.
by rewrite /cast; case: ZleP.
Qed.

  Lemma cast_empty len1 len2 :
    WArray.cast len1 (empty len2) = if len1 <=? len2 then ok (empty len1) else type_error.
Admitted.

  Lemma cast_empty_ok len1 len2 t:
    WArray.cast len1 (empty len2) = ok t -> t = empty len1.
Admitted.

  Lemma cast_get8 len1 len2 (m : array len2) m' :
    cast len1 m = ok m' ->
    forall k,
      read m' k U8 =
        if k <? len1 then read m k U8 else Error ErrOob.
Admitted.

  Lemma cast_uincl len1 len2 (t2 : WArray.array len2) t1 :
    cast len1 t2 = ok t1 -> uincl t1 t2.
Admitted.

  Lemma uincl_cast len1 len2 (a1: array len1) (a2:array len2) len a1' :
    uincl a1 a2 ->
    cast len a1 = ok a1' ->
    exists a2', cast len a2 = ok a2' /\ uincl a1' a2'.
Admitted.

  Lemma mk_scale_U8 aa : mk_scale aa U8 = 1%Z.
Admitted.

  Lemma get8_read len (m : array len) aa k :
    get aa U8 m k = read m k U8.
Admitted.

  Lemma set_get8 len (m m':array len) aa p ws (v: word ws) :
    set m aa p v = ok m' ->
    forall k,
      read m' k U8 =
        let i := (k - p * mk_scale aa ws)%Z in
         if ((0 <=? i) && (i <? wsize_size ws))%Z then ok (LE.wread8 v i)
         else read m k U8.
Admitted.

  Lemma setP len (m m':array len) p1 p2 ws (v: word ws) :
    set m AAscale p1 v = ok m' ->
    get AAscale ws m' p2 = if p1 == p2 then ok v else get AAscale ws m p2.
Admitted.

  Lemma setP_eq len (m m':array len) p1 ws (v: word ws) :
    set m AAscale p1 v = ok m' ->
    get AAscale ws m' p1 = ok v.
Admitted.

  Lemma setP_neq len (m m':array len) p1 p2 ws (v: word ws) :
    p1 != p2 ->
    set m AAscale p1 v = ok m' ->
    get AAscale ws m' p2 = get AAscale ws m p2.
Admitted.

  Lemma mk_scale_bound aa ws : (1 <= mk_scale aa ws <= wsize_size ws)%Z.
Admitted.

  Lemma get_bound ws len aa (t:array len) i w :
    get aa ws t i = ok w ->
    [/\ 0 <= i * mk_scale aa ws,
        i * mk_scale aa ws + wsize_size ws <= len &
        is_align (i * mk_scale aa ws) ws]%Z.
Admitted.

  Lemma set_bound ws len aa (a t:array len) i (w:word ws) :
    set a aa i w = ok t ->
    [/\ 0 <= i * mk_scale aa ws,
        i * mk_scale aa ws +  wsize_size ws <= len &
        is_align (i * mk_scale aa ws) ws]%Z.
Admitted.

  Lemma get_empty (n:positive) off :
    read (empty n) off U8 = if (0 <=? off) && (off <? n) then Error ErrAddrUndef else Error ErrOob.
Admitted.

  Lemma get0 (n:positive) off : (0 <= off ∧ off < n)%Z ->
    read (empty n) off U8 = Error ErrAddrUndef.
Admitted.

  Lemma uincl_empty len len' (t:array len') :
    Zpos len <= len' -> uincl (empty len) t.
Admitted.

  Lemma uincl_validw {len1 len2} (a1 : array len1) (a2 : array len2) ws i :
    uincl a1 a2 -> validw a1 i ws -> validw a2 i ws.
Admitted.

  Lemma uincl_get {len1 len2} (a1 : array len1) (a2 : array len2) aa ws i w :
    uincl a1 a2 ->
    get aa ws a1 i = ok w ->
    get aa ws a2 i = ok w.
Admitted.

  Lemma uincl_set {ws len1 len2} (a1 a1': array len1) (a2: array len2) aa i (w:word ws) :
    uincl a1 a2 ->
    set a1 aa i w = ok a1' ->
    exists a2', set a2 aa i w = ok a2' /\ uincl a1' a2'.
Admitted.

  Lemma fcopy_uincl ws len (a t1 t2 a1 : array len) i j:
    uincl t1 t2 ->
    fcopy ws a t1 i j = ok a1 ->
    exists2 a2, fcopy ws a t2 i j = ok a2 & uincl a1 a2.
Admitted.

  Lemma uincl_copy ws p a1 a2 a1' :
     uincl a1 a2 ->
     @copy ws p a1 = ok a1' ->
     @copy ws p a2 = ok a1'.
Admitted.

  Definition fill_size len l a :
    fill len l = ok a ->
    Pos.to_nat len = size l.
Admitted.

  Lemma fill_get8 len l a :
    fill len l = ok a ->
    forall k,
      read a k U8 =
        if (0 <=? k) && (k <? len) then ok (nth 0%R l (Z.to_nat k))
        else Error ErrOob.
Admitted.

  Lemma set_sub_data_get8 aa ws a len p t k:
    Mz.get (@set_sub_data aa ws len a p t) k =
      let i := (k - p * mk_scale aa ws)%Z in
      if (0 <=? i) && (i <? arr_size ws len) then Mz.get t i
      else Mz.get a k.
Admitted.

  Lemma set_sub_get8 aa ws lena a len p t a' :
    @set_sub lena aa ws len a p t = ok a' ->
    forall k,
      read a' k U8 =
        let i := (k - p * mk_scale aa ws)%Z in
        if (0 <=? i) && (i <? arr_size ws len) then read t i U8
        else read a k U8.
Admitted.

  Lemma set_sub_bound aa ws lena a len p t a' :
    @set_sub lena aa ws len a p t = ok a' ->
    0 <= p * mk_scale aa ws /\ p * mk_scale aa ws + arr_size ws len <= lena.
Admitted.

  Lemma get_sub_data_get8 aa ws a len p k:
    Mz.get (get_sub_data aa ws len a p) k =
      let start := (p * mk_scale aa ws)%Z in
      if (0 <=? k) && (k <? arr_size ws len) then Mz.get a (start + k)
      else None.
Admitted.

  Lemma get_sub_get8 aa ws lena a len p a' :
    @get_sub lena aa ws len a p = ok a' ->
    forall k,
      read a' k U8 =
        let start := (p * mk_scale aa ws)%Z in
        if (0 <=? k) && (k <? arr_size ws len) then read a (start + k) U8
        else Error ErrOob.
Admitted.

  Lemma get_sub_bound aa ws lena a len p a' :
    @get_sub lena aa ws len a p = ok a' ->
    0 <= p * mk_scale aa ws /\ p * mk_scale aa ws + arr_size ws len <= lena.
Admitted.

  Lemma uincl_get_sub {len1 len2} (a1 : array len1) (a2 : array len2)
      aa ws len i t1 :
    uincl a1 a2 ->
    get_sub aa ws len a1 i = ok t1 ->
    exists2 t2, get_sub aa ws len a2 i = ok t2 & uincl t1 t2.
Admitted.

  Lemma uincl_set_sub {ws len1 len2 len} (a1 a1': array len1) (a2: array len2) aa i
        (t1 t2:array (Z.to_pos (arr_size ws len))) :
    uincl a1 a2 -> uincl t1 t2 ->
    set_sub aa a1 i t1 = ok a1' ->
    exists2 a2', set_sub aa a2 i t2 = ok a2' & uincl a1' a2'.
Admitted.

End WArray.

Hint Resolve WArray.uincl_refl : core.

End warray_.

End Jasmin.

End Jasmin_DOT_warray_.
Import mathcomp.ssreflect.all_ssreflect.
Import mathcomp.algebra.all_algebra.
Export Jasmin.strings.
Export Jasmin.warray_.
Definition sem_t (t : stype) : Type.
Admitted.

Definition sem_prod ts tr := lprod (map sem_t ts) tr.
Definition sem_ot (t:stype) : Type.
Admitted.

Definition sem_tuple ts := ltuple (map sem_ot ts).
Import Coq.Unicode.Utf8.

Set Implicit Arguments.
Unset Strict Implicit.

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

Import Jasmin.var.

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
