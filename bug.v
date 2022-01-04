(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "-deprecated-native-compiler-option" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/bedrock2/bedrock2/src/bedrock2" "bedrock2" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/bedrock2/bedrock2/src/bedrock2Examples" "bedrock2Examples" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/bedrock2/deps/coqutil/src/coqutil" "coqutil" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-top" "bug_01" "-async-proofs-tac-j" "1" "-native-compiler" "no") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 717 lines to 555 lines, then from 568 lines to 1468 lines, then from 1472 lines to 694 lines, then from 703 lines to 575 lines, then from 588 lines to 979 lines, then from 982 lines to 820 lines, then from 833 lines to 1403 lines, then from 1408 lines to 969 lines, then from 971 lines to 832 lines, then from 845 lines to 991 lines, then from 996 lines to 851 lines, then from 864 lines to 888 lines, then from 893 lines to 967 lines, then from 973 lines to 854 lines, then from 867 lines to 924 lines, then from 929 lines to 862 lines, then from 875 lines to 967 lines, then from 972 lines to 897 lines, then from 906 lines to 872 lines, then from 885 lines to 1355 lines, then from 1360 lines to 1170 lines, then from 1183 lines to 1590 lines, then from 1595 lines to 1372 lines *)
(* coqc version 8.16+alpha compiled with OCaml 4.13.0
   coqtop version runner-ns46nmmj-project-6138686-concurrent-0:/builds/coq/coq/_build/default,(HEAD detached at 5820455) (58204555aaac561f1cef980bf74a3ef045f3a9bb)
   Expected coqc runtime on this file: 26.972 sec *)
Require Coq.ZArith.BinIntDef.
Require Coq.Strings.String.
Require coqutil.Macros.subst.
Require coqutil.Macros.unique.
Require coqutil.sanity.
Require Coq.Numbers.BinNums.
Require bedrock2.Syntax.
Require Ltac2.Init.
Require Ltac2.Int.
Require Ltac2.Message.
Require Ltac2.Control.
Require Ltac2.Bool.
Require Ltac2.Array.
Require Ltac2.Char.
Require Ltac2.Constr.
Require Ltac2.Std.
Require Ltac2.Env.
Require Ltac2.List.
Require Ltac2.Fresh.
Require Ltac2.Ident.
Require Ltac2.Ind.
Require Ltac2.Ltac1.
Require Ltac2.Option.
Require Ltac2.Pattern.
Require Ltac2.Printf.
Require Ltac2.String.
Require Ltac2.Notations.
Require Ltac2.Ltac2.
Require coqutil.Macros.ident_to_string.
Require bedrock2.NotationsCustomEntry.
Require Coq.Lists.List.
Require bedrock2.ReversedListNotations.
Require bedrock2.TracePredicate.
Require Coq.ZArith.BinInt.
Require Coq.ZArith.ZArith.
Require Coq.Strings.HexString.
Require coqutil.Z.HexNotation.
Require coqutil.Word.Interface.
Require Coq.Init.Byte.
Require Coq.Strings.Byte.
Require coqutil.Byte.
Require Coq.micromega.Lia.
Require coqutil.Z.Lia.
Require Coq.ZArith.Zpow_facts.
Require coqutil.Z.div_mod_to_equations.
Require Coq.btauto.Btauto.
Require coqutil.Z.PushPullMod.
Require Coq.setoid_ring.Ring_theory.
Require coqutil.Z.bitblast.
Require coqutil.Tactics.autoforward.
Require Coq.Arith.PeanoNat.
Require Coq.Arith.Compare_dec.
Require Coq.NArith.NArith.
Require coqutil.Decidable.
Require coqutil.Word.Properties.
Require coqutil.Z.BitOps.
Require Coq.setoid_ring.ZArithRing.
Require coqutil.Z.prove_Zeq_bitwise.
Require coqutil.Tactics.destr.
Require coqutil.Tactics.forward.
Require coqutil.Tactics.Tactics.
Require coqutil.Datatypes.Option.
Require Coq.Sorting.Permutation.
Require coqutil.Datatypes.List.
Require coqutil.Word.LittleEndianList.
Require bedrock2Examples.lightbulb_spec.
Require coqutil.Tactics.letexists.
Require coqutil.Tactics.eabstract.
Require coqutil.Tactics.ident_of_string.
Require coqutil.Datatypes.PrimitivePair.
Require coqutil.Datatypes.HList.
Require coqutil.dlet.
Require Coq.Classes.Morphisms.
Require Coq.Classes.RelationClasses.
Require Coq.Logic.PropExtensionality.
Require Coq.Logic.FunctionalExtensionality.
Require Coq.Program.Tactics.
Require coqutil.Datatypes.PropSet.
Require coqutil.Map.Interface.
Require coqutil.Word.Bitwidth.
Require coqutil.Map.Properties.
Require bedrock2.Lift1Prop.
Require bedrock2.Map.Separation.
Require coqutil.Tactics.syntactic_unify.
Require coqutil.Tactics.rdelta.
Require bedrock2.Map.SeparationLogic.
Require bedrock2.Notations.
Require coqutil.Map.MapKeys.
Require coqutil.Map.OfFunc.
Require coqutil.Map.OfListWord.
Require bedrock2.MetricLogging.
Require bedrock2.Memory.
Require bedrock2.Semantics.
Require bedrock2.Markers.
Require bedrock2.WeakestPrecondition.
Require bedrock2.WeakestPreconditionProperties.
Require bedrock2.Loops.
Require coqutil.Tactics.eplace.
Require bedrock2.Array.
Require coqutil.Macros.symmetry.
Require Coq.setoid_ring.Ring_tac.
Require bedrock2.ptsto_bytes.
Require bedrock2.Scalars.
Require Coq.Logic.Eqdep_dec.

Declare ML Module "ltac_plugin".
Module Export AdmitTactic.
Module Import LocalFalse.
Inductive False : Prop := .
End LocalFalse.
Axiom proof_admitted : False.
Global Set Default Proof Mode "Classic".
Tactic Notation "admit" := abstract case proof_admitted.
End AdmitTactic.

Module Export coqutil_DOT_Map_DOT_SortedList_WRAPPED.
Module Export SortedList.
Import coqutil.Macros.subst.
Import coqutil.Macros.unique.
Import coqutil.Map.Interface.
Definition minimize_eq_proof{A: Type}(eq_dec: forall (x y: A), {x = y} + {x <> y}){x y: A}    (pf: x = y): x = y. exact (match eq_dec x y with
  | left p => p
  | right n => match n pf: False with end
  end). Defined.

Module Import parameters.
  Class parameters := {
    key : Type;
    value : Type;
    ltb : key -> key -> bool
  }.

  Class strict_order {T} {ltb : T -> T -> bool}: Prop := {
    ltb_antirefl : forall k, ltb k k = false;
    ltb_trans : forall k1 k2 k3, ltb k1 k2 = true -> ltb k2 k3 = true -> ltb k1 k3 = true;
    ltb_total : forall k1 k2, ltb k1 k2 = false -> ltb k2 k1 = false -> k1 = k2;
  }.
  Global Arguments strict_order {_} _.
End parameters.
Notation parameters := parameters.parameters.

Section SortedList.
Local Set Default Proof Using "All".
  Context {p : unique! parameters} {ok : strict_order ltb}.

  Local Definition eqb k1 k2 := andb (negb (ltb k1 k2)) (negb (ltb k2 k1)).

  Fixpoint put m (k:key) (v:value) : list (key * value) :=
    match m with
    | nil => cons (k, v) nil
    | cons (k', v') m' =>
      match ltb k k', ltb k' k with
      |   true, _ => cons (k, v) m
      |   false, false => cons (k, v) m'
      |   false, true => cons (k', v') (put m' k v)
      end
    end.

  Fixpoint remove m (k:key) : list (key * value) :=
    match m with
    | nil => nil
    | cons (k', v') m' =>
      match ltb k k', ltb k' k with
      |   true, _ => m
      |   false, false => m'
      |   false, true => cons (k', v') (remove m' k)
      end
    end.

  Fixpoint sorted (m : list (key * value)) :=
    match m with
    | cons (k1, _) ((cons (k2, _) m'') as m') => andb (ltb k1 k2) (sorted m')
    | _ => true
    end.

  Record rep := { value : list (key * value) ; _value_ok : sorted value = true }.

  Lemma ltb_antisym k1 k2 (H:eqb k1 k2 = false) : ltb k1 k2 = negb (ltb k2 k1).
Admitted.

  Lemma sorted_put m k v : sorted m = true -> sorted (put m k v) = true.
Admitted.

  Lemma sorted_remove m k : sorted m = true -> sorted (remove m k) = true.
Admitted.
Definition lookup(l: list (key * parameters.value))(k: key): option parameters.value. exact (match List.find (fun p => eqb k (fst p)) l with
    | Some (_, v) => Some v
    | None => None
    end). Defined.

  Lemma eqb_refl: forall x: key, eqb x x = true.
Admitted.

  Lemma eqb_true: forall k1 k2, eqb k1 k2 = true <-> k1 = k2.
Admitted.
Definition map : map.map key parameters.value. exact (let wrapped_put m k v := Build_rep (put (value m) k v) (minimize_eq_proof Bool.bool_dec (sorted_put _ _ _ (_value_ok m))) in
    let wrapped_remove m k := Build_rep (remove (value m) k) (minimize_eq_proof Bool.bool_dec (sorted_remove _ _ (_value_ok m))) in
    {|
    map.rep := rep;
    map.empty := Build_rep nil eq_refl;
    map.get m k := lookup (value m) k;
    map.put := wrapped_put;
    map.remove := wrapped_remove;
    map.fold R f r0 m := List.fold_right (fun '(k, v) r => f r k v) r0 (value m);
  |}). Defined.

  Lemma eq_value {x y : rep} : value x = value y -> x = y.
Admitted.
End SortedList.
Arguments map : clear implicits.
Module Export ProgramLogic.
Import bedrock2.Syntax.
Import coqutil.Tactics.letexists.
Import coqutil.Tactics.eabstract.
Import coqutil.Tactics.rdelta.
Import coqutil.Tactics.ident_of_string.
Import bedrock2.WeakestPrecondition.
Import bedrock2.Map.SeparationLogic.

Definition spec_of (procname:String.string) := list (String.string * (list String.string * list String.string * Syntax.cmd.cmd)) -> Prop.
Existing Class spec_of.
Import coqutil.Map.Interface.

  Definition sepclause_of_map {key value map} (m : @map.rep key value map)
    : map.rep -> Prop := Logic.eq m.
  Coercion sepclause_of_map : Interface.map.rep >-> Funclass.

Goal True.
  assert_succeeds epose (fun k v M (m : @Interface.map.rep k v M) => m _).
Abort.

Section bindcmd.
  Context {T : Type}.
Fixpoint bindcmd (c : Syntax.cmd) (k : Syntax.cmd -> T) {struct c} : T.
exact (match c with
    | cmd.cond e c1 c2 => bindcmd c1 (fun c1 => bindcmd c2 (fun c2 => let c := cmd.cond e c1 c2 in k c))
    | cmd.seq c1 c2 => bindcmd c1 (fun c1 => bindcmd c2 (fun c2 => let c := cmd.seq c1 c2 in k c))
    | cmd.while e c => bindcmd c (fun c => let c := cmd.while e c in k c)
    | c => k c
    end).
Defined.
End bindcmd.

Fixpoint callees (c : Syntax.cmd) : list String.string :=
  match c with
  | cmd.cond _ c1 c2 | cmd.seq c1 c2 => callees c1 ++ callees c2
  | cmd.while _ c | cmd.stackalloc _ _ c => callees c
  | cmd.call _ f _ => cons f nil
  | _ => nil
  end.

Ltac assuming_correctness_of_in callees functions P :=
  lazymatch callees with
  | nil => P
  | cons ?f ?callees =>
    let f_spec := lazymatch constr:(_:spec_of f) with ?x => x end in
    constr:(f_spec functions -> ltac:(let t := assuming_correctness_of_in callees functions P in exact t))
  end.
Local Notation function_t := ((String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type).
Local Notation functions_t := (list function_t).

Ltac program_logic_goal_for_function proc :=
  let __ := constr:(proc : function_t) in
  let fname := eval cbv in (fst proc) in
  let callees := eval cbv in (callees (snd (snd proc))) in
  let spec := lazymatch constr:(_:spec_of fname) with ?s => s end in
  constr:(forall functions : functions_t, ltac:(
    let s := assuming_correctness_of_in callees functions (spec (cons proc functions)) in
    exact s)).
Definition program_logic_goal_for (_ : function_t) (P : Prop) := P.

Notation "program_logic_goal_for_function! proc" := (program_logic_goal_for proc ltac:(
   let x := program_logic_goal_for_function proc in exact x))
  (at level 10, only parsing).

Ltac normalize_body_of_function f := eval cbv in f.

Ltac bind_body_of_function f_ :=
  let f := normalize_body_of_function f_ in
  let fname := open_constr:(_) in
  let fargs := open_constr:(_) in
  let frets := open_constr:(_) in
  let fbody := open_constr:(_) in
  let funif := open_constr:((fname, (fargs, frets, fbody))) in
  unify f funif;
  let G := lazymatch goal with |- ?G => G end in
  let P := lazymatch eval pattern f_ in G with ?P _ => P end in
  change (bindcmd fbody (fun c : Syntax.cmd => P (fname, (fargs, frets, c))));
  cbv beta iota delta [bindcmd]; intros.

Ltac enter f :=
  cbv beta delta [program_logic_goal_for]; intros;
  bind_body_of_function f;
  lazymatch goal with |- ?s _ => cbv beta delta [s] end.

Ltac straightline_cleanup :=
  match goal with

  | x : Word.Interface.word.rep _ |- _ => clear x
  | x : Init.Byte.byte |- _ => clear x
  | x : Semantics.trace |- _ => clear x
  | x : Syntax.cmd |- _ => clear x
  | x : Syntax.expr |- _ => clear x
  | x : coqutil.Map.Interface.map.rep |- _ => clear x
  | x : BinNums.Z |- _ => clear x
  | x : unit |- _ => clear x
  | x : bool |- _ => clear x
  | x : list _ |- _ => clear x
  | x : nat |- _ => clear x

  | x := _ : Word.Interface.word.rep _ |- _ => clear x
  | x := _ : Init.Byte.byte |- _ => clear x
  | x := _ : Semantics.trace |- _ => clear x
  | x := _ : Syntax.cmd |- _ => clear x
  | x := _ : Syntax.expr |- _ => clear x
  | x := _ : coqutil.Map.Interface.map.rep |- _ => clear x
  | x := _ : BinNums.Z |- _ => clear x
  | x := _ : unit |- _ => clear x
  | x := _ : bool |- _ => clear x
  | x := _ : list _ |- _ => clear x
  | x := _ : nat |- _ => clear x
  | |- forall _, _ => intros
  | |- let _ := _ in _ => intros
  | |- dlet.dlet ?v (fun x => ?P) => change (let x := v in P); intros
  | _ => progress (cbn [Semantics.interp_binop] in * )
  | H: exists _, _ |- _ => destruct H
  | H: _ /\ _ |- _ => destruct H
  | x := ?y |- ?G => is_var y; subst x
  | H: ?x = ?y |- _ => constr_eq x y; clear H
  | H: ?x = ?y |- _ => is_var x; is_var y; assert_fails (idtac; let __ := eval cbv [x] in x in idtac); subst x
  | H: ?x = ?y |- _ => is_var x; is_var y; assert_fails (idtac; let __ := eval cbv [y] in y in idtac); subst y
  | H: ?x = ?v |- _ =>
    is_var x;
    assert_fails (idtac; let __ := eval cbv delta [x] in x in idtac);
    lazymatch v with context[x] => fail | _ => idtac end;
    let x' := fresh x in
    rename x into x';
    simple refine (let x := v in _);
    change (x' = x) in H;
    symmetry in H;
    destruct H
  end.

Ltac straightline_stackalloc :=
  match goal with Hanybytes: Memory.anybytes ?a ?n ?mStack |- _ =>
  let m := match goal with H : map.split ?mCobined ?m mStack |- _ => m end in
  let mCombined := match goal with H : map.split ?mCobined ?m mStack |- _ => mCobined end in
  let Hsplit := match goal with H : map.split ?mCobined ?m mStack |- _ => H end in
  let Hm := multimatch goal with H : _ m |- _ => H end in
  let Hm' := fresh Hm in
  let Htmp := fresh in
  let Pm := match type of Hm with ?P m => P end in
  assert_fails (idtac; match goal with Halready : (Separation.sep Pm (Array.array Separation.ptsto (Interface.word.of_Z (BinNums.Zpos BinNums.xH)) a _) mCombined) |- _ => idtac end);
  rename Hm into Hm';
  let stack := fresh "stack" in
  let stack_length := fresh "length_" stack in
  destruct (Array.anybytes_to_array_1 mStack a n Hanybytes) as (stack&Htmp&stack_length);
  epose proof (ex_intro _ m (ex_intro _ mStack (conj Hsplit (conj Hm' Htmp)))
  : Separation.sep _ (Array.array Separation.ptsto (Interface.word.of_Z (BinNums.Zpos BinNums.xH)) a _) mCombined) as Hm;
  clear Htmp;
  try (let m' := fresh m in rename m into m'); rename mCombined into m;
  ( assert (BinInt.Z.of_nat (Datatypes.length stack) = n)
  by (rewrite stack_length; apply (ZifyInst.of_nat_to_nat_eq n))
  || fail 2 "negative stackalloc of size" n )
  end.

Ltac straightline_stackdealloc :=
  lazymatch goal with |- exists _ _, Memory.anybytes ?a ?n _ /\ map.split ?m _ _ /\ _ =>
  let Hm := multimatch goal with Hm : _ m |- _ => Hm end in
  let stack := match type of Hm with context [Array.array Separation.ptsto _ a ?stack] => stack end in
  let length_stack := match goal with H : Datatypes.length stack = _ |- _ => H end in
  let Hm' := fresh Hm in
  pose proof Hm as Hm';
  let Psep := match type of Hm with ?P _ => P end in
  let Htmp := fresh "Htmp" in
  eassert (Lift1Prop.iff1 Psep (Separation.sep _ (Array.array Separation.ptsto (Interface.word.of_Z (BinNums.Zpos BinNums.xH)) a stack))) as Htmp
  by ecancel || fail "failed to find stack frame in" Psep "using ecancel";
  eapply (fun m => proj1 (Htmp m)) in Hm;
  let m' := fresh m in
  rename m into m';
  let mStack := fresh in
  destruct Hm as (m&mStack&Hsplit&Hm&Harray1); move Hm at bottom;
  pose proof Array.array_1_to_anybytes _ _ _ Harray1 as Hanybytes;
  rewrite length_stack in Hanybytes;
  refine (ex_intro _ m (ex_intro _ mStack (conj Hanybytes (conj Hsplit _))));
  clear Htmp Hsplit mStack Harray1 Hanybytes
  end.

Ltac rename_to_different H := once (idtac;
  let G := fresh H in
  rename H into G;
  assert_succeeds (set (H := Set))).
Ltac ensure_free H :=
  match constr:(Set) with
  | _ => assert_succeeds (set (H := Set))
  | _ => rename_to_different H
  end.

Ltac straightline :=
  match goal with
  | _ => straightline_cleanup
  | |- program_logic_goal_for ?f _ =>
    enter f; intros;
    unfold1_call_goal; cbv match beta delta [call_body];
    lazymatch goal with |- if ?test then ?T else _ =>
      replace test with true by reflexivity; change T end;
    cbv match beta delta [WeakestPrecondition.func]
  | |- WeakestPrecondition.cmd _ (cmd.set ?s ?e) _ _ _ ?post =>
    unfold1_cmd_goal; cbv beta match delta [cmd_body];
    let x := ident_of_string s in
    ensure_free x;

    letexists _ as x; split; [solve [repeat straightline]|]
  | |- cmd _ ?c _ _ _ ?post =>
    let c := eval hnf in c in
    lazymatch c with
    | cmd.while _ _ => fail
    | cmd.cond _ _ _ => fail
    | cmd.interact _ _ _ => fail
    | _ => unfold1_cmd_goal; cbv beta match delta [cmd_body]
    end
  | |- @list_map _ _ (get _) _ _ => unfold1_list_map_goal; cbv beta match delta [list_map_body]
  | |- @list_map _ _ (expr _ _) _ _ => unfold1_list_map_goal; cbv beta match delta [list_map_body]
  | |- @list_map _ _ _ nil _ => cbv beta match fix delta [list_map list_map_body]
  | |- expr _ _ _ _ => unfold1_expr_goal; cbv beta match delta [expr_body]
  | |- dexpr _ _ _ _ => cbv beta delta [dexpr]
  | |- dexprs _ _ _ _ => cbv beta delta [dexprs]
  | |- literal _ _ => cbv beta delta [literal]
  | |- get _ _ _ => cbv beta delta [get]
  | |- load _ _ _ _ => cbv beta delta [load]
  | |- @Loops.enforce ?width ?word ?locals ?names ?values ?map =>
    let values := eval cbv in values in
    change (@Loops.enforce width word locals names values map);
    exact (conj (eq_refl values) eq_refl)
  | |- @eq (@coqutil.Map.Interface.map.rep String.string Interface.word.rep _) _ _ =>
    eapply SortedList.eq_value; exact eq_refl
  | |- @map.get String.string Interface.word.rep ?M ?m ?k = Some ?e' =>
    let e := rdelta e' in
    is_evar e;
    once (let v := multimatch goal with x := context[@map.put _ _ M _ k ?v] |- _ => v end in

          unify e v; exact (eq_refl (Some v)))
  | |- @coqutil.Map.Interface.map.get String.string Interface.word.rep _ _ _ = Some ?v =>
    let v' := rdelta v in is_evar v'; (change v with v'); exact eq_refl
  | |- ?x = ?y =>
    let y := rdelta y in is_evar y; change (x=y); exact eq_refl
  | |- ?x = ?y =>
    let x := rdelta x in is_evar x; change (x=y); exact eq_refl
  | |- ?x = ?y =>
    let x := rdelta x in let y := rdelta y in constr_eq x y; exact eq_refl
  | |- store Syntax.access_size.one _ _ _ _ =>
    eapply Scalars.store_one_of_sep; [solve[ecancel_assumption]|]
  | |- store Syntax.access_size.two _ _ _ _ =>
    eapply Scalars.store_two_of_sep; [solve[ecancel_assumption]|]
  | |- store Syntax.access_size.four _ _ _ _ =>
    eapply Scalars.store_four_of_sep; [solve[ecancel_assumption]|]
  | |- store Syntax.access_size.word _ _ _ _ =>
    eapply Scalars.store_word_of_sep; [solve[ecancel_assumption]|]
  | |- bedrock2.Memory.load Syntax.access_size.one ?m ?a = Some ?ev =>
    try subst ev; refine (@Scalars.load_one_of_sep _ _ _ _ _ _ _ _ _ _); ecancel_assumption
  | |- @bedrock2.Memory.load _ ?word ?mem Syntax.access_size.two ?m ?a = Some ?ev =>
    try subst ev; refine (@Scalars.load_two_of_sep _ word _ mem _ a _ _ m _); ecancel_assumption
  | |- @bedrock2.Memory.load _ ?word ?mem Syntax.access_size.four ?m ?a = Some ?ev =>
    try subst ev; refine (@Scalars.load_four_of_sep_32bit _ word _ mem _ eq_refl a _ _ m _); ecancel_assumption
  | |- @bedrock2.Memory.load _ ?word ?mem Syntax.access_size.four ?m ?a = Some ?ev =>
    try subst ev; refine (@Scalars.load_four_of_sep _ word _ mem _ a _ _ m _); ecancel_assumption
  | |- @bedrock2.Memory.load _ ?word ?mem Syntax.access_size.word ?m ?a = Some ?ev =>
    try subst ev; refine (@Scalars.load_word_of_sep _ word _ mem _ a _ _ m _); ecancel_assumption
  | |- exists l', Interface.map.of_list_zip ?ks ?vs = Some l' /\ _ =>
    letexists; split; [exact eq_refl|]
  | |- exists l', Interface.map.putmany_of_list_zip ?ks ?vs ?l = Some l' /\ _ =>
    letexists; split; [exact eq_refl|]
  | |- exists x, ?P /\ ?Q =>
    let x := fresh x in refine (let x := _ in ex_intro (fun x => P /\ Q) x _);
                        split; [solve [repeat straightline]|]
  | |- exists x, Markers.split (?P /\ ?Q) =>
    let x := fresh x in refine (let x := _ in ex_intro (fun x => P /\ Q) x _);
                        split; [solve [repeat straightline]|]
  | |- Markers.unique (exists x, Markers.split (?P /\ ?Q)) =>
    let x := fresh x in refine (let x := _ in ex_intro (fun x => P /\ Q) x _);
                        split; [solve [repeat straightline]|]
  | |- Markers.unique (Markers.left ?G) =>
    change G;
    unshelve (idtac; repeat match goal with
                     | |- Markers.split (?P /\ Markers.right ?Q) =>
                       split; [eabstract (repeat straightline) | change Q]
                     | |- exists _, _ => letexists
                     end); []
  | |- Markers.split ?G => change G; split
  | |- True => exact I
  | |- False \/ _ => right
  | |- _ \/ False => left
  | |- BinInt.Z.modulo ?z (Memory.bytes_per_word _) = BinInt.Z0 /\ _ =>
      lazymatch Coq.setoid_ring.InitialRing.isZcst z with
      | true => split; [exact eq_refl|]
      end
  | |- _ => straightline_stackalloc
  | |- _ => straightline_stackdealloc
  end.

Ltac straightline_call :=
  lazymatch goal with
  | |- WeakestPrecondition.call ?functions ?callee _ _ _ _ =>
    let callee_spec := lazymatch constr:(_:spec_of callee) with ?s => s end in
    let Hcall := lazymatch goal with H: callee_spec functions |- _ => H end in
    eapply WeakestPreconditionProperties.Proper_call; cycle -1;
      [ eapply Hcall | try eabstract (solve [Morphisms.solve_proper]) .. ];
      [ .. | intros ? ? ? ?]
  end.
Module Export String.
Export Coq.Strings.String.

Lemma ltb_antirefl : forall k, ltb k k = false.
Admitted.

Lemma ltb_trans : forall k1 k2 k3, ltb k1 k2 = true -> ltb k2 k3 = true -> ltb k1 k3 = true.
Admitted.

Lemma ltb_total : forall k1 k2, ltb k1 k2 = false -> ltb k2 k1 = false -> k1 = k2.
Admitted.
Module Export SortedListString.

Local Instance string_strict_order: @SortedList.parameters.strict_order _ String.ltb
  := { ltb_antirefl := String.ltb_antirefl
       ; ltb_trans := String.ltb_trans
       ; ltb_total := String.ltb_total }.
Definition Build_parameters T := SortedList.parameters.Build_parameters String.string T String.ltb.
Definition map T := SortedList.map (Build_parameters T) string_strict_order.
Import Coq.ZArith.ZArith.
Export coqutil.Word.Bitwidth.

Instance BW32: Bitwidth 32 := {
  width_cases := or_introl eq_refl
}.
Import bedrock2.Syntax.
Import bedrock2.Semantics.
Import List.ListNotations.

Section WithParameters.
  Context {word: word.word 32} {mem: Interface.map.map word Byte.byte}.
Global Instance ext_spec: ExtSpec.
Admitted.

  Global Instance ext_spec_ok : ext_spec.ok ext_spec.
Admitted.
Global Instance locals: Interface.map.map String.string word.
exact (SortedListString.map _).
Defined.
Global Instance env: Interface.map.map String.string (list String.string * list String.string * cmd).
Admitted.
Global Instance locals_ok: Interface.map.ok locals.
Admitted.
Global Instance env_ok: Interface.map.ok env.
Admitted.
End WithParameters.
Import bedrock2.NotationsCustomEntry.
Import coqutil.Z.HexNotation.
Import coqutil.Z.Lia.
Import coqutil.Byte.
Local Open Scope string_scope.
Local Open Scope list_scope.

Section WithParameters.
  Context {word: word.word 32} {mem: map.map word Byte.byte}.

  Definition mmio_event_abstraction_relation
    (h : lightbulb_spec.OP word)
    (l : mem * string * list word * (mem * list word)) :=
    Logic.or
      (exists a v, h = ("st", a, v) /\ l = (map.empty, "MMIOWRITE", [a; v], (map.empty, [])))
      (exists a v, h = ("ld", a, v) /\ l = (map.empty, "MMIOREAD", [a], (map.empty, [v]))).
  Definition mmio_trace_abstraction_relation := List.Forall2 mmio_event_abstraction_relation.
End WithParameters.
Import coqutil.Word.Properties.
Local Open Scope Z_scope.

Lemma Z__range_add a0 a a1 (Ha: a0 <= a < a1) b0 b b1 (Hb : b0 <= b < b1)
      : a0+b0 <= a+b < a1 + b1 - 1.
Admitted.

Lemma Z__range_sub a0 a a1 (Ha: a0 <= a < a1) b0 b b1 (Hb : b0 <= b < b1)
      : a0-b1+1 <= a-b < a1 - b0.
Admitted.
Lemma Z__range_div_pos_const_r n0 n n1 (Hn : n0 <= n < n1) d (Hd : 0 < d)
  : n0/d <= n/d < n1/d + 1.
Admitted.
Lemma boundscheck {x0 x x1} (H: x0 <= x < x1) {X0 X1} (Hcheck : andb (X0 <=? x0) (x1 <=? X1) = true) : X0 <= x < X1.
Admitted.
Lemma boundscheck_lt {x0 x x1} (H: x0 <= x < x1) {X1} (Hcheck: Z.ltb x1 X1 = true) : x < X1.
Admitted.
Lemma bounded_constant c : c <= c < c+1.
Admitted.

Ltac named_pose_proof pf :=
  let H := fresh in
  let __ := match constr:(Set) with _ => pose proof pf as H end in
  H.
Ltac named_pose_asfresh pf x :=
  let H := fresh x in
  let __ := match constr:(Set) with _ => pose pf as H end in
  H.

Ltac named_pose_asfresh_or_id x n :=
  let y := match constr:(Set) with _ => named_pose_asfresh x n | _ => x end in
  y.

Ltac requireZcst z :=
  lazymatch Coq.setoid_ring.InitialRing.isZcst z with
  | true => idtac
  end.
Ltac requireZcstExpr e :=
  match e with
  | Z.pred ?x => requireZcstExpr x
  | Z.succ ?x => requireZcstExpr x
  | Z.ones ?x => requireZcstExpr x
  | Z.opp ?x => requireZcstExpr x
  | Z.lnot ?x => requireZcstExpr x
  | Z.log2 ?x => requireZcstExpr x
  | Z.log2_up ?x => requireZcstExpr x
  | Z.add ?x ?y => requireZcstExpr x; requireZcstExpr y
  | Z.sub ?x ?y => requireZcstExpr x; requireZcstExpr y
  | Z.mul ?x ?y => requireZcstExpr x; requireZcstExpr y
  | Z.div ?x ?y => requireZcstExpr x; requireZcstExpr y
  | Z.modulo ?x ?y => requireZcstExpr x; requireZcstExpr y
  | Z.quot ?x ?y => requireZcstExpr x; requireZcstExpr y
  | Z.rem ?x ?y => requireZcstExpr x; requireZcstExpr y
  | Z.pow ?x ?y => requireZcstExpr x; requireZcstExpr y
  | Z.shiftl ?x ?y => requireZcstExpr x; requireZcstExpr y
  | Z.shiftr ?x ?y => requireZcstExpr x; requireZcstExpr y
  | Z.land ?x ?y => requireZcstExpr x; requireZcstExpr y
  | Z.lor ?x ?y => requireZcstExpr x; requireZcstExpr y
  | Z.lxor ?x ?y => requireZcstExpr x; requireZcstExpr y
  | Z.ldiff ?x ?y => requireZcstExpr x; requireZcstExpr y
  | Z.clearbit ?x ?y => requireZcstExpr x; requireZcstExpr y
  | Z.setbit ?x ?y => requireZcstExpr x; requireZcstExpr y
  | Z.min ?x ?y => requireZcstExpr x; requireZcstExpr y
  | Z.max ?x ?y => requireZcstExpr x; requireZcstExpr y
  | Z.gcd ?x ?y => requireZcstExpr x; requireZcstExpr y
  | Z.lcm ?x ?y => requireZcstExpr x; requireZcstExpr y
  | _ => requireZcst e
  end.

Ltac zsimp x :=
  match constr:(Set) with
  | _ => let __ := requireZcstExpr x in let y := eval cbv in x in y
  | _ => x
  end.

Local Notation "zbsimp! H" :=
  (ltac:(
     lazymatch type of H with
           ?L <= ?X < ?R =>
           let L := zsimp L in
           let R := zsimp R in
           exact ((H : L <= X < R))
         end
  )) (at level 10, only parsing).

Ltac rbounded e :=
  let re := rdelta e in
  match goal with
  | H :  _ <= e < _ |- _ => H
  | _ =>
    match re with
    | word.unsigned ?a =>
      named_pose_proof (zbsimp! (Properties.word.unsigned_range a : _ <= e < _))
    | Z.div ?a ?b =>
      let __ := match constr:(Set) with _ => requireZcstExpr b end in
      let Ha := rbounded a in
      named_pose_proof (zbsimp! (Z__range_div_pos_const_r _ a _ Ha b ltac:(eapply Z.ltb_lt; exact eq_refl) : _ <= e < _))
    | Z.modulo ?a ?b =>
      let __ := match constr:(Set) with _ => requireZcstExpr b end in
      named_pose_proof (zbsimp! (Z.mod_pos_bound a b ltac:(eapply Z.ltb_lt; exact eq_refl) : _ <= e < _))
    | ?op ?a ?b =>
      let Ha := rbounded a in
      let Hb := rbounded b in
      let a0 := match type of Ha with ?a0 <= _ < ?a1 => a0 end in
      let a1 := match type of Ha with ?a0 <= _ < ?a1 => a1 end in
      let b0 := match type of Hb with ?b0 <= _ < ?b1 => b0 end in
      let b1 := match type of Hb with ?b0 <= _ < ?b1 => b1 end in
      match op with
      | Z.add => named_pose_proof (zbsimp! (Z__range_add a0 a a1 Ha b0 b b1 Hb : a0 + b0 <= e < a1 + b1 - 1))
      | Z.sub => named_pose_proof (zbsimp! (Z__range_sub a0 a a1 Ha b0 b b1 Hb : a0-b1+1 <= e < a1-b0))
      | Z.mul => named_pose_proof (zbsimp! (Z__range_mul_nonneg a0 a a1 Ha b0 b b1 Hb (Zle_bool_imp_le 0 a0 eq_refl) (Zle_bool_imp_le 0 b0 eq_refl) : _ <= e < _))

      end
    end
  | _ =>
    let __ := match constr:(Set) with _ => requireZcstExpr re end in
    constr:(zbsimp! (bounded_constant e))
  end.

Definition absint_eq {T} := @eq T.
Definition absint_eq_refl {T} v := ((@eq_refl T v) : @absint_eq T v v).
Local Infix "=~>" := absint_eq (at level 70, no associativity).

Module Export unsigned.
  Section WithWord.
    Context {width : Z} {word : word.word width} {word_ok : word.ok word}.
    Local Notation "absint_lemma! pf" := (ltac:(
      cbv [absint_eq] in *;
      etransitivity; [ eapply pf | ]; cycle -1;
        [unshelve (repeat match goal with
          | |- _ => progress unfold word.wrap in *
          | |-context [Z.shiftr ?x (word.unsigned ?y)] => assert_fails(is_evar x||is_evar y);
            setoid_rewrite (Z.shiftr_div_pow2 x (word.unsigned y) (proj1 (Properties.word.unsigned_range _)))
          | |-context [Z.shiftl ?x (word.unsigned ?y)] => assert_fails(is_evar x||is_evar y);
            setoid_rewrite (Z.shiftl_mul_pow2 x (word.unsigned y) (proj1 (Properties.word.unsigned_range _)))
          | |-context [?x mod (2^?y)] => assert_fails(is_evar x||is_evar y);
            rewrite (Z.mod_small x (2^y)) by shelve
          | |-context [word.unsigned ?x] => assert_fails(is_evar x);
            erewrite (_:word.unsigned _=_) by shelve
          end; exact eq_refl)
        |..];

        [> (repeat match goal with
                   | H: ?P |- ?G => assert_fails (has_evar P || has_evar G); rewrite H
                   end;
            match reverse goal with H : ?e |- ?G => is_evar e; unify e G; exact H end).. ]
      )) (at level 10, only parsing).

    Definition absint_add (x y : word.rep) ux Hx uy Hy Hbounds : _ =~> _ :=
      absint_lemma! (word.unsigned_add x y).
    Definition absint_sub (x y : word.rep) ux Hx uy Hy Hbounds : word.unsigned _ =~> _ :=
      absint_lemma! (word.unsigned_sub x y).
    Definition absint_mul (x y : word.rep) ux Hx uy Hy Hbounds : word.unsigned _ =~> _ :=
      absint_lemma! (word.unsigned_mul x y).
    Definition absint_and (x y : word.rep) ux Hx uy Hy : word.unsigned _ =~> _ :=
      absint_lemma! (Properties.word.unsigned_and_nowrap x y).
    Definition absint_or (x y : word.rep) ux Hx uy Hy : word.unsigned _ =~> _ :=
      absint_lemma! (Properties.word.unsigned_or_nowrap x y).
    Definition absint_xor (x y : word.rep) ux Hx uy Hy : word.unsigned _ =~> _ :=
      absint_lemma! (Properties.word.unsigned_xor_nowrap x y).
    Definition absint_ndn (x y : word.rep) ux Hx uy Hy : word.unsigned _ =~> _ :=
      absint_lemma! (Properties.word.unsigned_ndn_nowrap x y).
    Definition absint_sru (x y : word.rep) ux Hx uy Hy Hshift  : word.unsigned _ =~> _ :=
      absint_lemma! (Properties.word.unsigned_sru_nowrap x y).
    Definition absint_slu (x y : word.rep) ux Hx uy Hy Hrange Hshift : word.unsigned _ =~> _ :=
      absint_lemma! (word.unsigned_slu x y).
    Implicit Types (x y : word).

    Lemma absint_mask_r x y ux (Hx : word.unsigned x = ux) uy (Hy : word.unsigned y = uy) (Huy : uy = Z.ones (Z.log2 uy+1)):
       word.unsigned (word.and x y) =~> Z.modulo ux (uy+1).
Admitted.
    Lemma absint_mask_l y x uy (Hy : word.unsigned y = uy) ux (Hx : word.unsigned x = ux) (Huy : uy = Z.ones (Z.log2 uy+1)):
       word.unsigned (word.and y x) =~> Z.modulo ux (uy+1).
Admitted.
  End WithWord.

  Ltac zify_expr e :=
    let re := rdelta e in
    lazymatch type of e with
    | @word.rep ?width ?word_parameters =>
      match re with
      | _ => match goal with H: word.unsigned e =~> _ |- _ => H end
      | word.of_Z ?a =>
        let Ba := rbounded a in
        named_pose_proof (word.unsigned_of_Z_nowrap a (boundscheck (X0:=0) (X1:=2^width) Ba (eq_refl true)) : @absint_eq Z (@word.unsigned _ word_parameters e) a)
      | word.and ?a ?b =>
        let Ha := zify_expr a in let Ra := lazymatch type of Ha with _ =~> ?x => x end in
        let Hb := zify_expr b in let Rb := lazymatch type of Hb with _ =~> ?x => x end in
        named_pose_proof (absint_mask_r a b Ra Ha Rb Hb eq_refl : @absint_eq Z (@word.unsigned _ word_parameters e) (Z.modulo Ra (Rb+1)))
      | word.and ?a ?b =>
        let Ha := zify_expr a in let Ra := lazymatch type of Ha with _ =~> ?x => x end in
        let Hb := zify_expr b in let Rb := lazymatch type of Hb with _ =~> ?x => x end in
        named_pose_proof (absint_mask_l a b Ra Ha Rb Hb eq_refl : @absint_eq Z (@word.unsigned _ word_parameters e) (Z.modulo Rb (Ra+1)))
      | ?op ?a ?b =>
        let Ha := zify_expr a in let Ra := lazymatch type of Ha with _ =~> ?x => x end in
        let Hb := zify_expr b in let Rb := lazymatch type of Hb with _ =~> ?x => x end in
        match op with
        | word.and =>
          named_pose_proof constr:(absint_and a b Ra Ha Rb Hb : @absint_eq Z (@word.unsigned _ word_parameters e) (Z.land Ra Rb))
        | word.or =>
          named_pose_proof constr:(absint_or a b Ra Ha Rb Hb : @absint_eq Z (@word.unsigned _ word_parameters e) (Z.lor Ra Rb))
        | word.xor =>
          named_pose_proof constr:(absint_xor a b Ra Ha Rb Hb : @absint_eq Z (@word.unsigned _ word_parameters e) (Z.lxor Ra Rb))
        | word.ndn =>
          named_pose_proof constr:(absint_ndn a b Ra Ha Rb Hb : @absint_eq Z (@word.unsigned _ word_parameters e) (Z.ldiff Ra Rb))

        | word.add =>
          let Re := named_pose_asfresh_or_id constr:(Ra+Rb) e in
          let Be := rbounded Re in
          let Hbounds := match type of Be with ?x0 <= ?x < ?x1 =>
                           constr:(@boundscheck x0 x x1 Be 0 (2^width) (@eq_refl bool true)) end in
          named_pose_proof constr:(absint_add a b Ra Ha Rb Hb Hbounds : @absint_eq Z (@word.unsigned _ word_parameters e) Re)
        | word.sub =>
          let Re := named_pose_asfresh_or_id constr:(Ra-Rb) e in
          let Be := rbounded Re in
          let Hbounds := match type of Be with ?x0 <= ?x < ?x1 =>
                           constr:(@boundscheck x0 x x1 Be 0 (2^width) (@eq_refl bool true)) end in
          named_pose_proof constr:(absint_sub a b Ra Ha Rb Hb Hbounds : @absint_eq Z (@word.unsigned _ word_parameters e) Re)
        | word.mul =>
          let Re := named_pose_asfresh_or_id constr:(Ra*Rb) e in
          let Be := rbounded Re in
          let Hbounds := match type of Be with ?x0 <= ?x < ?x1 =>
                           constr:(@boundscheck x0 x x1 Be 0 (2^width) (@eq_refl bool true)) end in
          named_pose_proof constr:(absint_mul a b Ra Ha Rb Hb Hbounds : @absint_eq Z (@word.unsigned _ word_parameters e) Re)

        | word.sru =>
          let Re := named_pose_asfresh_or_id constr:((Ra / 2^Rb)) e in
          let Bb := rbounded Rb in
          let pf := constr:(absint_sru a b Ra Ha Rb Hb (@boundscheck_lt _ Rb _ Bb width eq_refl): @absint_eq Z (@word.unsigned _ word_parameters e) Re) in
          named_pose_proof pf
        | word.slu =>
          let Re := named_pose_asfresh_or_id constr:((Ra * 2^Rb)) e in
          let Bb := rbounded Rb in
          let Be := rbounded Re in
          named_pose_proof (absint_slu a b Ra Ha Rb Hb (boundscheck (X0:=0) (X1:=2^width) Be (eq_refl true)) (@boundscheck_lt _ Rb _ Bb width eq_refl): @absint_eq Z (@word.unsigned _ word_parameters e) Re)
        | _ =>
          constr:(@absint_eq_refl Z (@word.unsigned _ word_parameters e))

        end
      | _ =>
        constr:(@absint_eq_refl Z (@word.unsigned _ word_parameters e))
      end
    | Z =>
      match e with
      | _ => match goal with H: e =~> _ |- _ => H end
      | word.unsigned ?a => zify_expr a
      | _ => constr:(@absint_eq_refl Z e)
      end
    end.
Import bedrock2.TracePredicate.
Import TracePredicateNotations.

Section WithParameters.
  Context {word: word.word 32} {mem: map.map word Byte.byte}.
Global Instance spec_of_lan9250_readword : ProgramLogic.spec_of "lan9250_readword".
exact (fun functions => forall t m a,
    (0x0 <= Word.Interface.word.unsigned a < 0x400) ->
    WeakestPrecondition.call functions "lan9250_readword" t m [a] (fun T M RETS =>
      M = m /\
      exists ret err, RETS = [ret; err] /\
      exists iol, T = iol ++ t /\
      exists ioh, mmio_trace_abstraction_relation ioh iol /\ Logic.or
        (word.unsigned err <> 0 /\ (any +++ lightbulb_spec.spi_timeout _) ioh)
        (word.unsigned err = 0 /\ lightbulb_spec.lan9250_fastread4 _ a ret ioh))).
Defined.
End WithParameters.
Import coqutil.Macros.symmetry.
Import bedrock2.WeakestPrecondition.
Import bedrock2.Array.
Import bedrock2.Scalars.

Section WithParameters.
  Context {word: word.word 32} {mem: map.map word Byte.byte}.
  Context {word_ok: word.ok word} {mem_ok: map.ok mem}.

  Definition recvEthernet :=
    ("recvEthernet", (["buf"], ["num_bytes";"err"], bedrock_func_body:(
      num_bytes = $0;
      unpack! read, err = lan9250_readword(coq:(Ox"7C"));
      require !err else { err = $-1 };
      require (read & coq:((2^8-1)*2^16)) else { err = $1 };
      unpack! read, err = lan9250_readword($0x40);
      require !err else { err = $-1 };

      num_bytes = read >> $16 & coq:(2^14-1);

      num_bytes = (num_bytes + coq:(4-1)) >> $2;
      num_bytes = num_bytes + num_bytes;
      num_bytes = num_bytes + num_bytes;

      require (num_bytes < coq:(1520 + 1)) else { err = $2 };

      i = $0; while (i < num_bytes) {
        unpack! read, err = lan9250_readword($0);
        if err { err = $-1; i = num_bytes }
        else { store4(buf + i, read); i = i + $4 }
      }
      ))).
Import Coq.Init.Datatypes.
  Local Notation bytes := (array scalar8 (word.of_Z 1)).
  Local Infix "*" := (sep).
  Local Infix "*" := (sep) : type_scope.
  Import bedrock2Examples.lightbulb_spec.
Instance spec_of_recvEthernet : spec_of "recvEthernet".
exact (fun functions =>
    forall p_addr (buf:list byte) R m t,
      (array scalar8 (word.of_Z 1) p_addr buf * R) m ->
      length buf = 1520%nat ->
      WeakestPrecondition.call functions "recvEthernet" t m [p_addr] (fun t' m' rets =>
        exists bytes_written err, rets = [bytes_written; err] /\
        exists iol, t' = iol ++ t /\
        exists ioh, mmio_trace_abstraction_relation ioh iol /\ Logic.or
          (word.unsigned err = 0 /\
            exists recv buf, (bytes p_addr recv * bytes (word.add p_addr bytes_written) buf * R) m' /\ lan9250_recv _ recv ioh /\
            word.unsigned bytes_written + Z.of_nat (length buf) = 1520%Z /\
            Z.of_nat (length recv) = word.unsigned bytes_written)
          (word.unsigned err <> 0 /\ exists buf, (array scalar8 (word.of_Z 1) p_addr buf * R) m' /\ length buf = 1520%nat /\ (
             word.unsigned err = 1 /\ lan9250_recv_no_packet _ ioh \/
             word.unsigned err = 2 /\ lan9250_recv_packet_too_long _ ioh \/
             word.unsigned err = 2^32-1 /\ TracePredicate.concat TracePredicate.any (spi_timeout word) ioh
            ))
        )).
Defined.
  Local Ltac trans_ltu :=
    match goal with
    | H : word.unsigned ?v <> 0 |- _ =>
        let v := rdelta.rdelta v in
        let __ := lazymatch v with if word.ltu _ _ then word.of_Z 1 else word.of_Z 0 => I end in
        eapply Properties.word.if_nonzero in H; rewrite word.unsigned_ltu in H; eapply Z.ltb_lt in H
    | H : word.unsigned ?v = 0 |- _ =>
        let v := rdelta.rdelta v in
        let __ := lazymatch v with if word.ltu _ _ then word.of_Z 1 else word.of_Z 0 => I end in
        eapply Word.Properties.word.if_zero in H; rewrite word.unsigned_ltu in H; eapply Z.ltb_nlt in H
  end.
  Local Ltac split_if :=
    lazymatch goal with
      |- WeakestPrecondition.cmd _ ?c _ _ _ ?post =>
      let c := eval hnf in c in
          lazymatch c with
          | cmd.cond _ _ _ => letexists; split; [solve[repeat straightline]|split]
          end
    end.

  Local Hint Mode map.map - - : typeclass_instances.

  Local Ltac prove_ext_spec :=
    lazymatch goal with
    | |- ext_spec _ _ _ _ _ => split; [shelve|]; split; [trivial|]
    end.

  Local Ltac zify_unsigned :=
    repeat match goal with
    | |- context[word.unsigned ?e] => let H := unsigned.zify_expr e in rewrite H; pose proof H
    | G : context[word.unsigned ?e] |- _ => let H := unsigned.zify_expr e in rewrite H in G; pose proof H
    end;
    repeat match goal with H:absint_eq ?x ?x |- _ => clear H end;
    repeat match goal with H:?A |- _ => clear H; match goal with G:A |- _ => idtac end end.

  Add Ring wring : (Properties.word.ring_theory (word := word))
        (preprocess [autorewrite with rew_word_morphism],
         morphism (Properties.word.ring_morph (word := word)),
         constants [Properties.word_cst]).

  Lemma recvEthernet_ok : program_logic_goal_for_function! recvEthernet.
  Proof.
    straightline.
    rename H into Hcall; clear H0 H1.
rename H2 into H.
rename H3 into H0.
    repeat (straightline || split_if || straightline_call || eauto 99 || prove_ext_spec).
    1, 3: rewrite word.unsigned_of_Z; cbv - [Z.le Z.lt]; clear; blia.

    3: {

    refine (Loops.tailrec_earlyout
      (HList.polymorphic_list.cons (list byte) (HList.polymorphic_list.cons (mem -> Prop) HList.polymorphic_list.nil))
      ["buf";"num_bytes";"i";"read";"err"]
      (fun v scratch R t m buf num_bytes_loop i read err => PrimitivePair.pair.mk (
        word.unsigned err = 0 /\ word.unsigned i <= word.unsigned num_bytes /\
        v = word.unsigned i /\ (bytes (word.add buf i) scratch * R) m /\
        Z.of_nat (List.length scratch) = word.unsigned (word.sub num_bytes i) /\
        word.unsigned i mod 4 = word.unsigned num_bytes mod 4 /\
        num_bytes_loop = num_bytes)
      (fun T M BUF NUM_BYTES I READ ERR =>
         NUM_BYTES = num_bytes_loop /\
         exists RECV, (bytes (word.add buf i) RECV * R) M /\
         List.length RECV = List.length scratch /\
         exists iol, T = iol ++ t /\ exists ioh, mmio_trace_abstraction_relation ioh iol /\
         (word.unsigned ERR = 0 /\ lan9250_readpacket _ RECV ioh \/
          word.unsigned ERR = 2^32-1 /\ TracePredicate.concat TracePredicate.any (spi_timeout _) ioh ) )
      )
      _ _ _ _ _ _ _ _);

    cbn [HList.hlist.foralls HList.tuple.foralls
         HList.hlist.existss HList.tuple.existss
         HList.hlist.apply  HList.tuple.apply
         HList.hlist
         List.repeat Datatypes.length
         HList.polymorphic_list.repeat HList.polymorphic_list.length
         PrimitivePair.pair._1 PrimitivePair.pair._2] in *;
      repeat (straightline || split_if || eapply interact_nomem || eauto 99).
    {
 exact (Z.gt_wf (word.unsigned num_bytes)).
}
    1: repeat (refine (conj _ _)); eauto.
    {
 subst i.
rewrite word.unsigned_of_Z.
      eapply Properties.word.unsigned_range.
}
    1: zify_unsigned.
    1: replace (word.add p_addr i) with p_addr by (subst i; ring).
    1: rewrite <- (List.firstn_skipn (Z.to_nat (word.unsigned (word.sub num_bytes i) ) )  _) in H.
    1: SeparationLogic.seprewrite_in (symmetry! @bytearray_index_merge) H; [|ecancel_assumption].
      1,2,3:
      repeat match goal with
      | |- ?x = ?x => exact (eq_refl x)
      | _ => progress trans_ltu
      | _ => progress zify_unsigned
      | _ => progress rewrite ?Znat.Z2Nat.id by blia
      | H: _ |- _ => progress (rewrite ?Znat.Z2Nat.id in H by blia)
      | _ => rewrite List.length_firstn_inbounds by blia
      | _ => progress rewrite ?Z.sub_0_r
      end; repeat straightline.
      {
 repeat match goal with x:= _ |- context[?x]  => subst x end.
clear.
Z.div_mod_to_equations.
blia.
}

      {
 straightline_call; repeat straightline.
        {
 rewrite word.unsigned_of_Z.
cbv; clear.
intuition congruence.
}
        split_if; do 6 straightline.

        {
 straightline.
          straightline.
          straightline.
          straightline.

          do 5 eexists; split; [repeat straightline|]; [].
          left.
          repeat straightline.
          {
 subst br0.
rewrite word.unsigned_ltu, Z.ltb_irrefl, word.unsigned_of_Z; exact eq_refl.
}
          split; eauto.
          eexists; split; eauto.
          split; eauto.
          eexists; split.
          {
 subst a; eauto.
}
          eexists; split; eauto.
          right; split.
          {
 subst err.
rewrite word.unsigned_of_Z.
exact eq_refl.
}
          intuition eauto.
}

        do 4 straightline.
        trans_ltu.
        match goal with
          | H: context[word.unsigned (word.sub ?a ?b)] |- _ =>
              pose proof Properties.word.unsigned_range a;
              pose proof Properties.word.unsigned_range b;
              let H := fresh in
              pose proof word.unsigned_sub a b as H;
              unfold word.wrap in H;
              rewrite Z.mod_small in H by blia
        end.
        match goal with H10 : _ ?a0 |- store _ ?a0 _ _ _ => rewrite <- (List.firstn_skipn 4 _) in H10;
          SeparationLogic.seprewrite_in (symmetry! @bytearray_index_merge) H10 end.
        {
 instantiate (1:= word.of_Z 4).
          rewrite word.unsigned_of_Z.
          rewrite List.length_firstn_inbounds; [exact eq_refl|].
Z.div_mod_to_equations.
blia.
}
        do 2 straightline.
        match goal with H12:_|-_ => seprewrite_in @scalar32_of_bytes H12 end.
1: reflexivity.
        {
 eapply List.length_firstn_inbounds; Z.div_mod_to_equations; blia.
}
        straightline.

        do 3 straightline.

        do 5 letexists.
split.
{
 repeat straightline.
}
        right.
do 3 letexists.
        repeat split; repeat straightline; repeat split.
        {
 intuition idtac.
}
        {
 subst i.
          rewrite word.unsigned_add; cbv [word.wrap]; rewrite Z.mod_small;
          replace (word.unsigned (word.of_Z 4)) with 4.
          2,4: rewrite word.unsigned_of_Z; exact eq_refl.
          1,2: try (Z.div_mod_to_equations; blia).
}
        {
 replace (word.add x9 i)
            with (word.add (word.add x9 x11) (word.of_Z 4)) by (subst i; ring).
          ecancel_assumption.
}
        {
 repeat match goal with x1 := _ |- _ => subst x1; rewrite List.length_skipn; rewrite Znat.Nat2Z.inj_sub end.
          {
 repeat match goal with H5:_|-_=>rewrite H5 end; subst i.
            progress replace (word.sub num_bytes (word.add x11 (word.of_Z 4)))
              with (word.sub (word.sub num_bytes x11) (word.of_Z 4)) by ring.
            rewrite (word.unsigned_sub _ (word.of_Z 4)).
            unfold word.wrap.
rewrite Z.mod_small.
            all: replace (word.unsigned (word.of_Z 4)) with 4 by (rewrite word.unsigned_of_Z; exact eq_refl).
            all: change (Z.of_nat 4) with 4.
            all : Z.div_mod_to_equations; blia.
}
          Z.div_mod_to_equations; blia.
}
        {
 subst i.
          rewrite word.unsigned_add.
unfold word.wrap.
rewrite (Z.mod_small _ (2 ^ 32)).
          {
 revert dependent x11.
clear -word_ok.
            replace (word.unsigned (word.of_Z 4)) with 4 by (rewrite word.unsigned_of_Z; exact eq_refl).
            intros.
            Z.div_mod_to_equations.
blia.
}
          replace (word.unsigned (word.of_Z 4)) with 4 by (rewrite word.unsigned_of_Z; exact eq_refl).
          Z.div_mod_to_equations.
          blia.
}
        {
 repeat match goal with |- context [?x] => is_var x; subst x end.
          rewrite word.unsigned_add.
unfold word.wrap.
rewrite Z.mod_small.
          {
 replace (word.unsigned (word.of_Z 4)) with 4 by (rewrite word.unsigned_of_Z; exact eq_refl).
blia.
}
          replace (word.unsigned (word.of_Z 4)) with 4 by (rewrite word.unsigned_of_Z; exact eq_refl).
          Z.div_mod_to_equations.
blia.
}
        {
 subst v'.
subst i.
          rewrite word.unsigned_add.
          replace (word.unsigned (word.of_Z 4)) with 4 by (rewrite word.unsigned_of_Z; exact eq_refl).
          unfold word.wrap.
rewrite (Z.mod_small _ (2 ^ 32)); Z.div_mod_to_equations; blia.
}

        {
 letexists; repeat split.
          {
 repeat match goal with x := _ |- _ => is_var x; subst x end; subst.
            cbv [scalar32 truncated_word truncate_word truncate_Z truncated_scalar littleendian ptsto_bytes.ptsto_bytes] in *.
            progress replace (word.add x9 (word.add x11 (word.of_Z 4))) with
                    (word.add (word.add x9 x11) (word.of_Z 4)) in * by ring.
            SeparationLogic.seprewrite_in (@bytearray_index_merge) H25.
            {
 rewrite word.unsigned_of_Z; exact eq_refl.
}
 {
 ecancel_assumption.
}
 }
          {
 subst RECV.
rewrite List.app_length.
            rewrite H26.
subst x22.
rewrite List.length_skipn.
            unshelve erewrite (_ : length (HList.tuple.to_list _) = 4%nat); [exact eq_refl|].
            enough ((4 <= length x7)%nat) by blia.
            Z.div_mod_to_equations; blia.
}
          cbv [truncate_word truncate_Z] in *.
          repeat match goal with x := _ |- _ => is_var x; subst x end; subst.
          eexists; split.
          {
 rewrite List.app_assoc; eauto.
}
          eexists; split.
          {
 eapply List.Forall2_app; eauto.
 }
          rewrite HList.tuple.to_list_of_list.
          destruct H29; [left|right]; repeat (straightline || split || eauto using TracePredicate.any_app_more).
          eapply TracePredicate.concat_app; eauto.
          unshelve erewrite (_ : LittleEndianList.le_combine _ = word.unsigned x10); rewrite ?word.of_Z_unsigned; try solve [intuition idtac].
          {
            etransitivity.
            1: eapply (LittleEndianList.le_combine_split 4).
            eapply Properties.word.wrap_unsigned.
}
 }
 }

      {
 split; eauto.
eexists; split; eauto.
split; eauto.
exists nil; split; eauto.
        eexists; split; [constructor|].
        left.
split; eauto.
        enough (Hlen : length x7 = 0%nat) by (destruct x7; try solve[inversion Hlen]; exact eq_refl).
        PreOmega.zify.
        rewrite H13.
        subst br.
        rewrite word.unsigned_ltu in H11.
        destruct (word.unsigned x11 <? word.unsigned num_bytes) eqn:HJ.
        {
 rewrite word.unsigned_of_Z in H11.
inversion H11.
}
        eapply Z.ltb_nlt in HJ.
        revert dependent x7; revert dependent num_bytes; revert dependent x11; clear -word_ok; intros.
        unshelve erewrite (_:x11 = num_bytes) in *.
        {
 eapply Properties.word.unsigned_inj.
Z.div_mod_to_equations; blia.
}
        rewrite word.unsigned_sub, Z.sub_diag; exact eq_refl.
}
      repeat straightline.
      repeat letexists.
split.
{
 repeat straightline.
}
      eexists _, _.
split.
{
 exact eq_refl.
}

      repeat straightline.
      subst i.
      match goal with H: _ |- _ =>
        progress repeat (unshelve erewrite (_ : forall x, word.add x (word.of_Z 0) = x) in H; [intros; ring|]);
        progress repeat (unshelve erewrite (_ : forall x, word.sub x (word.of_Z 0) = x) in H; [intros; ring|])
      end.
      eexists; split.
      1: {
 repeat match goal with |- context [?x] => match type of x with list _ => subst x end end.
        repeat rewrite List.app_assoc.
f_equal.
}
      eexists; split.
      1:repeat eapply List.Forall2_app; eauto.
      destruct H14; [left|right]; repeat straightline; repeat split; eauto.
      {
 trans_ltu;
        replace (word.unsigned (word.of_Z 1521)) with 1521 in *
          by (rewrite word.unsigned_of_Z; exact eq_refl).
          eexists _, _; repeat split.
        {
 SeparationLogic.ecancel_assumption.
}
        {
 revert dependent x2.
revert dependent x6.
intros.
          destruct H5; repeat straightline; try contradiction.
          destruct H9; repeat straightline; try contradiction.
          eexists _, _; split.
          {
 rewrite <-!List.app_assoc.
eauto using concat_app.
}
          split; [zify_unsigned; eauto|].
        {
 cbv beta delta [lan9250_decode_length].
          rewrite H11.
rewrite List.firstn_length, Znat.Nat2Z.inj_min.
          replace (word.sub num_bytes (word.of_Z 0)) with num_bytes by ring.
          rewrite ?Znat.Z2Nat.id by eapply word.unsigned_range.
          transitivity (word.unsigned num_bytes); [blia|exact eq_refl].
}
 }
        {
 pose proof word.unsigned_range num_bytes.
          rewrite List.length_skipn.
blia.
}
        rewrite H11, List.length_firstn_inbounds, ?Znat.Z2Nat.id.
        all: try (zify_unsigned; blia).
        }
      {
 repeat match goal with H : _ |- _ => rewrite H; intro HX; solve[inversion HX] end.
}
      {
 trans_ltu;
        replace (word.unsigned (word.of_Z 1521)) with 1521 in * by
          (rewrite word.unsigned_of_Z; exact eq_refl).
        eexists _; split; eauto; repeat split; try blia.
        {
 SeparationLogic.seprewrite_in @bytearray_index_merge H10.
          {
 rewrite H11.
            1: replace (word.sub num_bytes (word.of_Z 0)) with num_bytes by ring.
            rewrite List.length_firstn_inbounds, ?Znat.Z2Nat.id.
            1:exact eq_refl.
            1:eapply word.unsigned_range.
            rewrite ?Znat.Z2Nat.id by eapply word.unsigned_range.
            blia.
}
          eassumption.
}
        {
 1:rewrite List.app_length, List.length_skipn, H11, List.firstn_length.
          replace (word.sub num_bytes (word.of_Z 0)) with num_bytes by ring.
          enough (Z.to_nat (word.unsigned num_bytes) <= length buf)%nat by blia.
          rewrite ?Znat.Z2Nat.id by eapply word.unsigned_range; blia.
}
        right.
right.
split; eauto using TracePredicate.any_app_more.
}
 }

    all: repeat letexists; split; repeat straightline;
      eexists _, _; split; [ exact eq_refl | ].
    all: eexists; split;
      [repeat match goal with |- context [?x] => match type of x with list _ => subst x end end;
      rewrite ?List.app_assoc; eauto|].
    all: eexists; split;
      [repeat eapply List.Forall2_app; eauto|].
    all:
      right; subst err;
      split; [intro HX; rewrite word.unsigned_of_Z in HX; inversion HX|].
    all : repeat ((eexists; split; [solve[eauto]|]) || (split; [solve[eauto]|])).
    all : rewrite !word.unsigned_of_Z.

    {
 left; split; [exact eq_refl|] || right.
      left; split; [exact eq_refl|] || right.
            split; [exact eq_refl|].
        intuition eauto using TracePredicate.any_app_more.
}
    {
 left; split; [exact eq_refl|] || right.
      left; split; [exact eq_refl|] || right.
            split; [exact eq_refl|].
        intuition eauto using TracePredicate.any_app_more.
}
    {
 left; split; [exact eq_refl|] || right.
      left; split; [exact eq_refl|].
      eexists _, _; split.
      1:eapply TracePredicate.concat_app; try intuition eassumption.
      subst v0.
      rewrite word.unsigned_ltu in H6.
      destruct (word.unsigned num_bytes <? word.unsigned (word.of_Z 1521)) eqn:?.
      all : rewrite word.unsigned_of_Z in Heqb, H6; try inversion H6.
      eapply Z.ltb_nlt in Heqb; revert Heqb.
      repeat match goal with |- context [?x] => match type of x with _ => subst x end end.
      cbv [lan9250_decode_length].
split.
2: cbn in *; blia.
      subst v.
rewrite word.unsigned_and_nowrap, word.unsigned_of_Z in H2.
eapply H2.
}
    {
 left.
      split; [exact eq_refl|].
      eexists; split; intuition eauto.
}
  Defined.
