
(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-noinit" "-indices-matter" "-w" "-deprecated-native-compiler-option" "-native-compiler" "no" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/hott/theories" "HoTT" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/hott/contrib" "HoTT.Contrib" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/hott/test" "HoTT.Tests" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-top" "HoTT.Algebra.AbSES.Pullback") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 514 lines to 57 lines, then from 70 lines to 965 lines, then from 970 lines to 92 lines, then from 105 lines to 679 lines, then from 683 lines to 115 lines, then from 128 lines to 280 lines, then from 285 lines to 130 lines, then from 143 lines to 533 lines, then from 538 lines to 142 lines, then from 155 lines to 502 lines, then from 507 lines to 238 lines, then from 251 lines to 1225 lines, then from 1229 lines to 372 lines, then from 385 lines to 793 lines, then from 798 lines to 397 lines, then from 410 lines to 1005 lines, then from 1007 lines to 448 lines, then from 461 lines to 975 lines, then from 978 lines to 495 lines, then from 508 lines to 630 lines, then from 635 lines to 496 lines, then from 509 lines to 733 lines, then from 738 lines to 500 lines, then from 513 lines to 1685 lines, then from 1690 lines to 566 lines, then from 579 lines to 673 lines, then from 678 lines to 571 lines, then from 584 lines to 727 lines, then from 732 lines to 583 lines, then from 596 lines to 711 lines, then from 716 lines to 605 lines, then from 618 lines to 694 lines, then from 699 lines to 606 lines, then from 619 lines to 1007 lines, then from 1011 lines to 607 lines, then from 620 lines to 1016 lines, then from 1021 lines to 609 lines, then from 622 lines to 1305 lines, then from 1305 lines to 633 lines, then from 646 lines to 2899 lines, then from 2902 lines to 704 lines, then from 717 lines to 1574 lines, then from 1575 lines to 725 lines, then from 738 lines to 1222 lines, then from 1226 lines to 760 lines, then from 773 lines to 1074 lines, then from 1079 lines to 786 lines, then from 799 lines to 850 lines, then from 855 lines to 789 lines, then from 802 lines to 1372 lines, then from 1376 lines to 792 lines, then from 805 lines to 1027 lines, then from 1032 lines to 794 lines, then from 807 lines to 944 lines, then from 949 lines to 796 lines, then from 809 lines to 1013 lines, then from 1018 lines to 801 lines, then from 814 lines to 1620 lines, then from 1615 lines to 837 lines, then from 850 lines to 885 lines, then from 890 lines to 851 lines, then from 864 lines to 1416 lines, then from 1421 lines to 911 lines, then from 924 lines to 1062 lines, then from 1064 lines to 987 lines, then from 1000 lines to 1042 lines, then from 1047 lines to 998 lines, then from 1011 lines to 1275 lines, then from 1280 lines to 1028 lines, then from 1041 lines to 1279 lines, then from 1284 lines to 1088 lines, then from 1101 lines to 1185 lines, then from 1190 lines to 1087 lines, then from 1100 lines to 1830 lines, then from 1833 lines to 1090 lines, then from 1103 lines to 1971 lines, then from 1975 lines to 1226 lines *)
(* coqc version 8.20+alpha compiled with OCaml 4.09.0
   coqtop version runner-cabngxqim-project-4504-concurrent-0:/builds/coq/coq/_build/default,(HEAD detached at cf8b86fadbc1c) (cf8b86fadbc1c3d0e41b3d5581bd378fe4080a66)
   Expected coqc runtime on this file: 0.485 sec *)
Require HoTT.WildCat.Core.
Require HoTT.Basics.Contractible.
Module Export Equivalences.
Import HoTT.Basics.Overture.
Import HoTT.Basics.PathGroupoids.
Import HoTT.Basics.Tactics.





Generalizable Variables A B C f g.


Global Instance isequiv_idmap (A : Type) : IsEquiv idmap | 0 :=
  Build_IsEquiv A A idmap idmap (fun _ => 1) (fun _ => 1) (fun _ => 1).
Definition equiv_idmap (A : Type) : A <~> A.
exact (Build_Equiv A A idmap _).
Defined.

Arguments equiv_idmap {A} , A.
Global Instance isequiv_compose `{IsEquiv A B f} `{IsEquiv B C g}
  : IsEquiv (g o f) | 1000.
Admitted.
Definition equiv_compose {A B C : Type} (g : B -> C) (f : A -> B)
  `{IsEquiv B C g} `{IsEquiv A B f}
  : A <~> C.
exact (Build_Equiv A C (g o f) _).
Defined.
Definition equiv_compose' {A B C : Type} (g : B <~> C) (f : A <~> B)
  : A <~> C.
exact (equiv_compose g f).
Defined.


Notation "g 'oE' f" := (equiv_compose' g%equiv f%equiv) : equiv_scope.


Section EquivTransport.

End EquivTransport.



Section Adjointify.

  Context {A B : Type} (f : A -> B) (g : B -> A).
  Context (isretr : f o g == idmap) (issect : g o f == idmap).

  
  Let issect' := fun x =>
    ap g (ap f (issect x)^)  @  ap g (isretr (f x))  @  issect x.

  Local Definition is_adjoint' (a : A) : isretr (f a) = ap f (issect' a).
Admitted.
Definition isequiv_adjointify : IsEquiv f.
Admitted.
Definition equiv_adjointify : A <~> B.
exact (Build_Equiv A B f isequiv_adjointify).
Defined.

End Adjointify.


Global Instance isequiv_pr1 {A : Type} (P : A -> Type) `{forall x, Contr (P x)}
  : IsEquiv (@pr1 A P).
Admitted.


Ltac multi_assumption :=
  multimatch goal with
    
    [ H : ?A |- _ ] => exact H
  end.













Ltac decomposing_intros_with_paths :=
  let x := fresh in
  intros x; cbn in x;
  multimatch type of x with
  | _ =>
    try match type of x with
        | 
          ?a = ?b => fail 1
        | 
          forall y:?A, ?B => fail 1
        | _ => elim x; clear x
        end;
    try decomposing_intros_with_paths
  | ?a = ?b =>
    
    ((move x before b; 
      revert dependent b;
      assert_fails (move b at top); 
      refine (paths_ind _ _ _)) +
     
     (move x before a;
      revert dependent a;
      assert_fails (move a at top);
      refine (paths_ind_r _ _ _)));
    try decomposing_intros_with_paths
  end.


Ltac build_record_with_evars :=
  (cbn; multi_assumption + (unshelve econstructor; build_record_with_evars)) +
  
  (match goal with
     |- ?G => let x := fresh in evar (x : G); exact x
   end; build_record_with_evars).


Ltac make_equiv_contr_basedpaths :=
  snrefine (equiv_adjointify _ _ _ _);
    
    [ decomposing_intros_with_paths; solve [ unshelve build_record_with_evars ]
    | decomposing_intros_with_paths; solve [ unshelve build_record_with_evars ]
    | decomposing_intros_with_paths; exact idpath
    | decomposing_intros_with_paths; exact idpath ].







End Equivalences.
Import HoTT.Basics.Overture.

Definition transport_paths_Fl {A B : Type} {f : A -> B} {x1 x2 : A} {y : B}
  (p : x1 = x2) (q : f x1 = y)
  : transport (fun x => f x = y) p q = (ap f p)^ @ q.
Admitted.
Reserved Infix "∘" (at level 40, left associativity).
Module Export Decimal.

Inductive uint : Type0 :=
 | Nil
 | D0 (_:uint)
 | D1 (_:uint)
 | D2 (_:uint)
 | D3 (_:uint)
 | D4 (_:uint)
 | D5 (_:uint)
 | D6 (_:uint)
 | D7 (_:uint)
 | D8 (_:uint)
 | D9 (_:uint).

Notation zero := (D0 Nil).

Variant int : Type0 := Pos (d:uint) | Neg (d:uint).

Variant decimal : Type0 :=
 | Decimal (i:int) (f:uint)
 | DecimalExp (i:int) (f:uint) (e:int).

Register uint as num.uint.type.
Register int as num.int.type.
Register decimal as num.decimal.type.

Fixpoint revapp (d d' : uint) :=
  match d with
  | Nil => d'
  | D0 d => revapp d (D0 d')
  | D1 d => revapp d (D1 d')
  | D2 d => revapp d (D2 d')
  | D3 d => revapp d (D3 d')
  | D4 d => revapp d (D4 d')
  | D5 d => revapp d (D5 d')
  | D6 d => revapp d (D6 d')
  | D7 d => revapp d (D7 d')
  | D8 d => revapp d (D8 d')
  | D9 d => revapp d (D9 d')
  end.

Definition rev d := revapp d Nil.

Module Export Little.

Fixpoint succ d :=
  match d with
  | Nil => D1 Nil
  | D0 d => D1 d
  | D1 d => D2 d
  | D2 d => D3 d
  | D3 d => D4 d
  | D4 d => D5 d
  | D5 d => D6 d
  | D6 d => D7 d
  | D7 d => D8 d
  | D8 d => D9 d
  | D9 d => D0 (succ d)
  end.
Module Export Hexadecimal.

Inductive uint : Type0 :=
 | Nil
 | D0 (_:uint)
 | D1 (_:uint)
 | D2 (_:uint)
 | D3 (_:uint)
 | D4 (_:uint)
 | D5 (_:uint)
 | D6 (_:uint)
 | D7 (_:uint)
 | D8 (_:uint)
 | D9 (_:uint)
 | Da (_:uint)
 | Db (_:uint)
 | Dc (_:uint)
 | Dd (_:uint)
 | De (_:uint)
 | Df (_:uint).

Variant int : Type0 := Pos (d:uint) | Neg (d:uint).

Variant hexadecimal : Type0 :=
 | Hexadecimal (i:int) (f:uint)
 | HexadecimalExp (i:int) (f:uint) (e:Decimal.int).

Register uint as num.hexadecimal_uint.type.
Register int as num.hexadecimal_int.type.
Register hexadecimal as num.hexadecimal.type.
Module Export Numeral.

Variant uint : Type0 := UIntDec (u:Decimal.uint) | UIntHex (u:Hexadecimal.uint).

Variant int : Type0 := IntDec (i:Decimal.int) | IntHex (i:Hexadecimal.int).

Variant numeral : Type0 := Dec (d:Decimal.decimal) | Hex (h:Hexadecimal.hexadecimal).

Register uint as num.num_uint.type.
Register int as num.num_int.type.
Register numeral as num.number.type.
Module Export Nat.

Fixpoint tail_add n m :=
  match n with
    | O => m
    | S n => tail_add n (S m)
  end.

Fixpoint tail_addmul r n m :=
  match n with
    | O => r
    | S n => tail_addmul (tail_add m r) n m
  end.

Definition tail_mul n m := tail_addmul O n m.

Local Notation ten := (S (S (S (S (S (S (S (S (S (S O)))))))))).

Fixpoint of_uint_acc (d:Decimal.uint)(acc:nat) :=
  match d with
  | Decimal.Nil => acc
  | Decimal.D0 d => of_uint_acc d (tail_mul ten acc)
  | Decimal.D1 d => of_uint_acc d (S (tail_mul ten acc))
  | Decimal.D2 d => of_uint_acc d (S (S (tail_mul ten acc)))
  | Decimal.D3 d => of_uint_acc d (S (S (S (tail_mul ten acc))))
  | Decimal.D4 d => of_uint_acc d (S (S (S (S (tail_mul ten acc)))))
  | Decimal.D5 d => of_uint_acc d (S (S (S (S (S (tail_mul ten acc))))))
  | Decimal.D6 d => of_uint_acc d (S (S (S (S (S (S (tail_mul ten acc)))))))
  | Decimal.D7 d => of_uint_acc d (S (S (S (S (S (S (S (tail_mul ten acc))))))))
  | Decimal.D8 d => of_uint_acc d (S (S (S (S (S (S (S (S (tail_mul ten acc)))))))))
  | Decimal.D9 d => of_uint_acc d (S (S (S (S (S (S (S (S (S (tail_mul ten acc))))))))))
  end.

Definition of_uint (d:Decimal.uint) := of_uint_acc d O.

Local Notation sixteen := (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))).

Fixpoint of_hex_uint_acc (d:Hexadecimal.uint)(acc:nat) :=
  match d with
  | Hexadecimal.Nil => acc
  | Hexadecimal.D0 d => of_hex_uint_acc d (tail_mul sixteen acc)
  | Hexadecimal.D1 d => of_hex_uint_acc d (S (tail_mul sixteen acc))
  | Hexadecimal.D2 d => of_hex_uint_acc d (S (S (tail_mul sixteen acc)))
  | Hexadecimal.D3 d => of_hex_uint_acc d (S (S (S (tail_mul sixteen acc))))
  | Hexadecimal.D4 d => of_hex_uint_acc d (S (S (S (S (tail_mul sixteen acc)))))
  | Hexadecimal.D5 d => of_hex_uint_acc d (S (S (S (S (S (tail_mul sixteen acc))))))
  | Hexadecimal.D6 d => of_hex_uint_acc d (S (S (S (S (S (S (tail_mul sixteen acc)))))))
  | Hexadecimal.D7 d => of_hex_uint_acc d (S (S (S (S (S (S (S (tail_mul sixteen acc))))))))
  | Hexadecimal.D8 d => of_hex_uint_acc d (S (S (S (S (S (S (S (S (tail_mul sixteen acc)))))))))
  | Hexadecimal.D9 d => of_hex_uint_acc d (S (S (S (S (S (S (S (S (S (tail_mul sixteen acc))))))))))
  | Hexadecimal.Da d => of_hex_uint_acc d (S (S (S (S (S (S (S (S (S (S (tail_mul sixteen acc)))))))))))
  | Hexadecimal.Db d => of_hex_uint_acc d (S (S (S (S (S (S (S (S (S (S (S (tail_mul sixteen acc))))))))))))
  | Hexadecimal.Dc d => of_hex_uint_acc d (S (S (S (S (S (S (S (S (S (S (S (S (tail_mul sixteen acc)))))))))))))
  | Hexadecimal.Dd d => of_hex_uint_acc d (S (S (S (S (S (S (S (S (S (S (S (S (S (tail_mul sixteen acc))))))))))))))
  | Hexadecimal.De d => of_hex_uint_acc d (S (S (S (S (S (S (S (S (S (S (S (S (S (S (tail_mul sixteen acc)))))))))))))))
  | Hexadecimal.Df d => of_hex_uint_acc d (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (tail_mul sixteen acc))))))))))))))))
  end.

Definition of_hex_uint (d:Hexadecimal.uint) := of_hex_uint_acc d O.

Definition of_num_uint (d:Numeral.uint) :=
  match d with
  | Numeral.UIntDec d => of_uint d
  | Numeral.UIntHex d => of_hex_uint d
  end.

Fixpoint to_little_uint n acc :=
  match n with
  | O => acc
  | S n => to_little_uint n (Decimal.Little.succ acc)
  end.

Definition to_uint n :=
  Decimal.rev (to_little_uint n Decimal.zero).

Definition to_num_uint n := Numeral.UIntDec (to_uint n).

Number Notation nat of_num_uint to_num_uint (abstract after 5001) : nat_scope.
Module Export Trunc.

Local Set Universe Minimization ToSet.
Generalizable Variables A B m n f.
Definition nat_to_trunc_index@{} (n : nat) : trunc_index.
Admitted.
Definition int_to_trunc_index@{} (v : Decimal.int) : option trunc_index.
exact (match v with
     | Decimal.Pos d => Some (nat_to_trunc_index (Nat.of_uint d))
     | Decimal.Neg d => match Nat.of_uint d with
                        | 2%nat => Some minus_two
                        | 1%nat => Some (minus_two.+1)
                        | 0%nat => Some (minus_two.+2)
                        | _ => None
                        end
     end).
Defined.
Definition num_int_to_trunc_index@{} (v : Numeral.int) : option trunc_index.
exact (match v with
  | Numeral.IntDec v => int_to_trunc_index v
  | Numeral.IntHex _ => None
  end).
Defined.

Fixpoint trunc_index_to_little_uint@{} n acc :=
  match n with
  | minus_two => acc
  | minus_two.+1 => acc
  | minus_two.+2 => acc
  | trunc_S n => trunc_index_to_little_uint n (Decimal.Little.succ acc)
  end.

Definition trunc_index_to_int@{} n :=
  match n with
  | minus_two => Decimal.Neg (Nat.to_uint 2)
  | minus_two.+1 => Decimal.Neg (Nat.to_uint 1)
  | n => Decimal.Pos (Decimal.rev (trunc_index_to_little_uint n Decimal.zero))
  end.

Definition trunc_index_to_num_int@{} n :=
  Numeral.IntDec (trunc_index_to_int n).

Number Notation trunc_index num_int_to_trunc_index trunc_index_to_num_int
  : trunc_scope.

Global Instance istrunc_succ {n : trunc_index} {A : Type} `{IsTrunc n A}
  : IsTrunc n.+1 A | 1000.
Admitted.

Class IsTruncMap (n : trunc_index) {X Y : Type} (f : X -> Y)
  := istruncmap_fiber : forall y:Y, IsTrunc n (hfiber f y).

Notation IsEmbedding := (IsTruncMap (-1)).

Theorem path_ishprop `{H : IsHProp A}
  : forall x y : A, x = y.
Admitted.

End Trunc.

Module Export HoTT_DOT_Basics_WRAPPED.
Module Export Basics.
Export HoTT.Basics.Overture.
Export HoTT.Basics.PathGroupoids.
Export HoTT.Basics.Contractible.
Export HoTT.Basics.Tactics.

End Basics.
Module Export HoTT.
Module Export Basics.
Include HoTT_DOT_Basics_WRAPPED.Basics.
End Basics.
Module Export Sigma.

Generalizable Variables X A B C f g n.
Definition path_sigma {A : Type} (P : A -> Type) (u v : sig P)
           (p : u.1 = v.1) (q : p # u.2 = v.2)
: u = v.
Admitted.
Definition path_sigma' {A : Type} (P : A -> Type) {x x' : A} {y : P x} {y' : P x'}
           (p : x = x') (q : p # y = y')
: (x;y) = (x';y').
Admitted.

Definition transport_sigma' {A B : Type} {C : A -> B -> Type}
           {x1 x2 : A} (p : x1 = x2) (yz : { y : B & C x1 y })
: transport (fun x => { y : B & C x y }) p yz =
  (yz.1 ; transport (fun x => C x yz.1) p yz.2).
Admitted.
Definition functor_sigma `{P : A -> Type} `{Q : B -> Type}
           (f : A -> B) (g : forall a, P a -> Q (f a))
: sig P -> sig Q.
exact (fun u => (f u.1 ; g u.1 u.2)).
Defined.

Global Instance istrunc_sigma `{P : A -> Type}
         `{IsTrunc n A} `{forall a, IsTrunc n (P a)}
: IsTrunc n (sig P) | 100.
Admitted.
Definition path_sigma_hprop {A : Type} {P : A -> Type}
           `{forall x, IsHProp (P x)}
           (u v : sig P)
: u.1 = v.1 -> u = v.
Admitted.

End Sigma.
Import HoTT.WildCat.Core.
Global Instance isgraph_type@{u v} : IsGraph@{v u} Type@{u}.
exact (Build_IsGraph Type@{u} (fun a b => a -> b)).
Defined.
Global Instance is2graph_type : Is2Graph Type.
exact (fun x y => Build_IsGraph _ (fun f g => f == g)).
Defined.
Definition path_unit (z z' : Unit) : z = z'.
Admitted.
Global Instance contr_unit : Contr Unit | 0.
Admitted.

Lemma cancelL_isembedding {A B C : Type} `{IsHSet B} {f : A -> B} {g : B -> C} `{IsEmbedding (g o f)}
  : IsEmbedding f.
Admitted.

Monomorphic Axiom Univalence : Type0.
Existing Class Univalence.

Definition functor_hfiber2 {A B C D}
           {f : A -> B} {g : C -> D} {h : A -> C} {k : B -> D}
           (p : k o f == g o h) {b : B} {b' : D} (q : k b = b')
  : hfiber f b -> hfiber g b'.
Proof.
  srapply functor_sigma.
  -
 exact h.
  -
 intros a e.
exact ((p a)^ @ ap k e @ q).
Defined.

Global Instance isequiv_functor_hfiber2 {A B C D}
       {f : A -> B} {g : C -> D} {h : A -> C} {k : B -> D}
       `{IsEquiv A C h} `{IsEquiv B D k}
       (p : k o f == g o h) {b : B} {b' : D} (q : k b = b')
  : IsEquiv (functor_hfiber2 p q).
Admitted.
Definition equiv_functor_hfiber2 {A B C D}
           {f : A -> B} {g : C -> D} {h : A <~> C} {k : B <~> D}
           (p : k o f == g o h) {b : B} {b' : D} (q : k b = b')
  : hfiber f b <~> hfiber g b'.
exact (Build_Equiv _ _ (functor_hfiber2 p q) _).
Defined.

Definition Pullback {A B C} (f : B -> A) (g : C -> A)
  := { b : B & { c : C & f b = g c }}.
Definition pullback_pr1 {A B C} {f : B -> A} {g : C -> A}
: Pullback f g -> B.
exact ((fun z => z.1)).
Defined.
Definition pullback_pr2 {A B C} {f : B -> A} {g : C -> A}
: Pullback f g -> C.
exact ((fun z => z.2.1)).
Defined.
Definition pullback_along' {A B C} (g : C -> A) (f : B -> A)
: Pullback f g -> C.
exact (fun z => z.2.1).
Defined.

Notation "g ^*'" := (pullback_along' g) : function_scope.

Definition hfiber_pullback_along' {A B C} (g : C -> A) (f : B -> A) (c:C)
: hfiber (g ^*' f) c <~> hfiber f (g c).
Proof.
  make_equiv_contr_basedpaths.
Defined.

Definition hfiber_pullback_along_pointed {A B C} {c : C} {a : A}
           (g : C -> A) (f : B -> A) (p : g c = a)
  : hfiber (g ^*' f) c <~> hfiber f a.
Proof.
  refine (_ oE hfiber_pullback_along' _ _ _); cbn.
  srapply (equiv_functor_hfiber2 (h:=equiv_idmap) (k:=equiv_idmap)).
  -
 reflexivity.
  -
 assumption.
Defined.

Local Open Scope nat_scope.

  Definition ExtensionAlong@{a b p m} {A : Type@{a}} {B : Type@{b}} (f : A -> B)
             (P : B -> Type@{p}) (d : forall x:A, P (f x))
    :=
       sig@{m m} (fun (s : forall y:B, P y) => forall x:A, s (f x) = d x).

  Fixpoint ExtendableAlong@{i j k l}
           (n : nat) {A : Type@{i}} {B : Type@{j}}
           (f : A -> B) (C : B -> Type@{k}) : Type@{l}
    := match n with
         | 0 => Unit
         | S n => (forall (g : forall a, C (f a)),
                     ExtensionAlong@{i j k l} f C g) *
                  forall (h k : forall b, C b),
                    ExtendableAlong n f (fun b => h b = k b)
       end.
Definition ooExtendableAlong@{i j k l}
             {A : Type@{i}} {B : Type@{j}}
             (f : A -> B) (C : B -> Type@{k}) : Type@{l}.
exact (forall n : nat, ExtendableAlong@{i j k l} n f C).
Defined.

Record Subuniverse@{i} :=
{
  In_internal : Type@{i} -> Type@{i} ;
  hprop_inO_internal : Funext -> forall (T : Type@{i}),
      IsHProp (In_internal T) ;
  inO_equiv_inO_internal : forall (T U : Type@{i}) (T_inO : In_internal T)
                                  (f : T -> U) {feq : IsEquiv f},
      In_internal U ;
}.

Class In (O : Subuniverse) (T : Type) := in_internal : In_internal O T.

Class PreReflects@{i} (O : Subuniverse@{i}) (T : Type@{i}) :=
{
  O_reflector : Type@{i} ;
  O_inO : In O O_reflector ;
  to : T -> O_reflector ;
}.

Arguments O_reflector O T {_}.
Arguments to O T {_}.

Class Reflects@{i} (O : Subuniverse@{i}) (T : Type@{i})
      `{PreReflects@{i} O T} :=
{
  extendable_to_O : forall {Q : Type@{i}} {Q_inO : In O Q},
      ooExtendableAlong (to O T) (fun _ => Q)
}.

Record ReflectiveSubuniverse@{i} :=
{
  rsu_subuniv : Subuniverse@{i} ;
  rsu_prereflects : forall (T : Type@{i}), PreReflects rsu_subuniv T ;
  rsu_reflects : forall (T : Type@{i}), Reflects rsu_subuniv T ;
}.

Coercion rsu_subuniv : ReflectiveSubuniverse >-> Subuniverse.
Global Existing Instance rsu_prereflects.
Definition rsu_reflector (O : ReflectiveSubuniverse) (T : Type) : Type.
exact (O_reflector O T).
Defined.

Coercion rsu_reflector : ReflectiveSubuniverse >-> Funclass.

Class IsConnected (O : ReflectiveSubuniverse@{i}) (A : Type@{i})
  := isconnected_contr_O : Contr@{i} (O A).

Class IsConnMap (O : ReflectiveSubuniverse@{i})
      {A : Type@{i}} {B : Type@{i}} (f : A -> B)
  := isconnected_hfiber_conn_map

     : forall b:B, IsConnected@{i} O (hfiber@{i i} f b).

Section ConnectedMaps.
  Context (O : ReflectiveSubuniverse@{i}).

  Definition conn_map_homotopic {A B : Type} (f g : A -> B) (h : f == g)
  : IsConnMap O f -> IsConnMap O g.
Admitted.

  Global Instance conn_map_pullback' {A B C}
         (g : C -> A) (f : B -> A) `{IsConnMap O _ _ f}
  : IsConnMap O (g^*' f).
Admitted.
Definition cancelL_equiv_conn_map {A B C : Type} (f : A -> B) (g : B <~> C)
         `{IsConnMap O _ _ (g o f)}
    : IsConnMap O f.
Admitted.

  End ConnectedMaps.

Class ReflectsD@{i} (O' O : Subuniverse@{i}) (T : Type@{i})
      `{PreReflects@{i} O' T} :=
{
  extendable_to_OO :
    forall (Q : O_reflector O' T -> Type@{i}) {Q_inO : forall x, In O (Q x)},
      ooExtendableAlong (to O' T) Q
}.

Record Modality@{i} := Build_Modality'
{
  modality_subuniv : Subuniverse@{i} ;
  modality_prereflects : forall (T : Type@{i}),
      PreReflects modality_subuniv T ;
  modality_reflectsD : forall (T : Type@{i}),
      ReflectsD modality_subuniv modality_subuniv T ;
}.

Definition modality_to_reflective_subuniverse (O : Modality@{i})
  : ReflectiveSubuniverse@{i}.
Admitted.

Coercion modality_to_reflective_subuniverse : Modality >-> ReflectiveSubuniverse.

Definition Tr (n : trunc_index) : Modality.
Admitted.

Notation IsSurjection := (IsConnMap (Tr (-1))).

Ltac intros_of_type A :=
  repeat match goal with |- forall (a : A), _ => intro a end.

Section Induced_category.
  Context {A B : Type} (f : A -> B).

  Local Instance isgraph_induced `{IsGraph B} : IsGraph A.
  Proof.
    nrapply Build_IsGraph.
    intros a1 a2.
    exact (f a1 $-> f a2).
  Defined.

  Local Instance is01cat_induced `{Is01Cat B} : Is01Cat A.
  Proof.
    nrapply Build_Is01Cat; intros_of_type A; cbn.
    +
 apply Id.
    +
 apply cat_comp.
  Defined.

End Induced_category.

Class IsPointedCat (A : Type) `{Is1Cat A} := {
  zero_object : A;
  isinitial_zero_object : IsInitial zero_object;
  isterminal_zero_object : IsTerminal zero_object;
}.

Global Existing Instance isinitial_zero_object.
Global Existing Instance isterminal_zero_object.
Definition zero_morphism {A : Type} `{IsPointedCat A} {a b : A} : a $-> b.
exact ((mor_initial _ b) $o (mor_terminal a _)).
Defined.

Declare Scope pointed_scope.

Local Open Scope pointed_scope.
Notation "[ X , x ]" := (Build_pType X x) : pointed_scope.

Record pFam (A : pType) := { pfam_pr1 :> A -> Type; dpoint : pfam_pr1 (point A)}.

Arguments Build_pFam {A} _ _.
Arguments dpoint {A} P : rename.
Definition pfam_const {A : pType} (B : pType) : pFam A.
exact (Build_pFam (fun _ => pointed_type B) (point B)).
Defined.

Record pForall (A : pType) (P : pFam A) := {
  pointed_fun : forall x, P x ;
  dpoint_eq : pointed_fun (point A) = dpoint P ;
}.

Arguments dpoint_eq {A P} f : rename.
Coercion pointed_fun : pForall >-> Funclass.

Notation "A ->* B" := (pForall A (pfam_const B)) : pointed_scope.
Definition Build_pMap (A B : pType) (f : A -> B) (p : f (point A) = point B)
  : A ->* B.
exact (Build_pForall A (pfam_const B) f p).
Defined.
Definition point_eq {A B : pType} (f : A ->* B)
  : f (point A) = point B.
Admitted.
Definition pmap_compose {A B C : pType} (g : B ->* C) (f : A ->* B)
  : A ->* C.
exact (Build_pMap A C (g o f) (ap g (point_eq f) @ point_eq g)).
Defined.

Infix "o*" := pmap_compose : pointed_scope.
Definition pfam_phomotopy {A : pType} {P : pFam A} (f g : pForall A P) : pFam A.
exact (Build_pFam (fun x => f x = g x) (dpoint_eq f @ (dpoint_eq g)^)).
Defined.

Definition pHomotopy {A : pType} {P : pFam A} (f g : pForall A P)
  := pForall A (pfam_phomotopy f g).

Infix "==*" := pHomotopy : pointed_scope.
Definition Build_pHomotopy {A : pType} {P : pFam A} {f g : pForall A P}
  (p : f == g) (q : p (point A) = dpoint_eq f @ (dpoint_eq g)^)
  : f ==* g.
exact (Build_pForall A (pfam_phomotopy f g) p q).
Defined.

Definition point_htpy {A : pType} {P : pFam A} {f g : pForall A P}
  (h : f ==* g) : h (point A) @ dpoint_eq g = dpoint_eq f.
Admitted.
Definition pointed_fam {A : pType} (B : A -> pType) : pFam A.
exact (Build_pFam (pointed_type o B) (point (B (point A)))).
Defined.
Definition point_pforall {A : pType} (B : A -> pType) : pForall A (pointed_fam B).
exact (Build_pForall A (pointed_fam B) (fun x => point (B x)) 1).
Defined.
Definition pconst {A B : pType} : A ->* B.
exact (point_pforall (fun _ => B)).
Defined.

Definition phomotopy_homotopy_hset {X Y : pType} `{IsHSet Y} {f g : X ->* Y} (h : f == g)
  : f ==* g.
Proof.
  apply (Build_pHomotopy h).
  apply path_ishprop.
Defined.
Global Instance ispointed_fiber {A B : pType} (f : A ->* B) : IsPointed (hfiber f (point B)).
exact ((point A; point_eq f)).
Defined.
Definition pfiber {A B : pType} (f : A ->* B) : pType.
exact ([hfiber f (point B), _]).
Defined.
Module Export canonical_names.
Delimit Scope mc_scope with mc.
Global Open Scope mc_scope.

Generalizable Variables A B f g x y.

Notation " g ∘ f " := (Compose g f)%mc.

Definition id {A : Type} (a : A) := a.

Class SgOp A := sg_op: A -> A -> A.
Class MonUnit A := mon_unit: A.
Class Negate A := negate: A -> A.

Module Export BinOpNotations.
Infix "*" := sg_op : mc_mult_scope.
Notation "(.*.)" := sg_op (only parsing) : mc_mult_scope.
Notation "(-)" := negate (only parsing) : mc_scope.
End BinOpNotations.

Class LeftIdentity {A B} (op : A -> B -> B) (x : A): Type
  := left_identity: forall y, op x y = y.
Class RightIdentity {A B} (op : A -> B -> A) (y : B): Type
  := right_identity: forall x, op x y = x.

Class LeftInverse {A} {B} {C} (op : A -> B -> C) (inv : B -> A) (unit : C)
  := left_inverse: forall x, op (inv x) x = unit.
Class RightInverse {A} {B} {C} (op : A -> B -> C) (inv : A -> B) (unit : C)
  := right_inverse: forall x, op x (inv x) = unit.

Class Commutative {B A} (f : A -> A -> B) : Type
  := commutativity: forall x y, f x y = f y x.

Class HeteroAssociative {A B C AB BC ABC}
  (fA_BC: A -> BC -> ABC) (fBC: B -> C -> BC)
  (fAB_C: AB -> C -> ABC) (fAB : A -> B -> AB): Type
  := associativity : forall x y z, fA_BC x (fBC y z) = fAB_C (fAB x y) z.
Class Associative {A} (f : A -> A -> A)
  := simple_associativity : HeteroAssociative f f f f.

Section cancellation.
  Context `(op : A -> A -> A) (z : A).

  Class LeftCancellation := left_cancellation : forall x y, op z x = op z y -> x = y.
End cancellation.

End canonical_names.

Section upper_classes.
  Context (A : Type@{i}).

  Local Open Scope mc_mult_scope.

  Class IsSemiGroup {Aop: SgOp A} :=
    { sg_set : IsHSet A
    ; sg_ass : Associative (.*.) }.
    #[export] Existing Instances sg_set sg_ass.

  Class IsMonoid {Aop : SgOp A} {Aunit : MonUnit A} :=
    { monoid_semigroup : IsSemiGroup
    ; monoid_left_id : LeftIdentity (.*.) mon_unit
    ; monoid_right_id : RightIdentity (.*.) mon_unit }.
  #[export] Existing Instances
    monoid_semigroup
    monoid_left_id
    monoid_right_id.

  Class IsGroup {Aop : SgOp A} {Aunit : MonUnit A} {Anegate : Negate A} :=
    { group_monoid : @IsMonoid (.*.) Aunit
    ; negate_l : LeftInverse (.*.) (-) mon_unit
    ; negate_r : RightInverse (.*.) (-) mon_unit }.
  #[export] Existing Instances
    group_monoid
    negate_l
    negate_r.

End upper_classes.

Section morphism_classes.

  Section sgmorphism_classes.
  Context {A B : Type} {Aop : SgOp A} {Bop : SgOp B}
    {Aunit : MonUnit A} {Bunit : MonUnit B}.

  Local Open Scope mc_mult_scope.

  Class IsSemiGroupPreserving (f : A -> B) :=
    preserves_sg_op : forall x y, f (x * y) = f x * f y.

  Class IsUnitPreserving (f : A -> B) :=
    preserves_mon_unit : f mon_unit = mon_unit.

  Class IsMonoidPreserving (f : A -> B) :=
    { monmor_sgmor : IsSemiGroupPreserving f
    ; monmor_unitmor : IsUnitPreserving f }.
  #[export] Existing Instances monmor_sgmor monmor_unitmor.
  End sgmorphism_classes.

  End morphism_classes.

Local Open Scope mc_mult_scope.
Generalizable Variables G H A B C f g.

Section group_props.
  Context `{IsGroup G}.

  Global Instance group_cancelL : forall z : G, LeftCancellation (.*.) z.
Admitted.

End group_props.

Section id_mor.

  Context `{SgOp A} `{MonUnit A}.

  Global Instance id_sg_morphism : IsSemiGroupPreserving (@id A).
Admitted.

End id_mor.

Section compose_mor.

  Context
    `{SgOp A} `{MonUnit A}
    `{SgOp B} `{MonUnit B}
    `{SgOp C} `{MonUnit C}
    (f : A -> B) (g : B -> C).

  Local Instance compose_sg_morphism : IsSemiGroupPreserving f -> IsSemiGroupPreserving g ->
    IsSemiGroupPreserving (g ∘ f).
Admitted.

End compose_mor.

#[export]
Hint Extern 4 (IsSemiGroupPreserving (_ o _)) =>
  class_apply @compose_sg_morphism : typeclass_instances.

Record Group := {
  group_type :> Type;
  group_sgop :: SgOp group_type;
  group_unit :: MonUnit group_type;
  group_inverse :: Negate group_type;
  group_isgroup :: IsGroup group_type;
}.
Arguments group_unit {_}.

Section GroupLaws.
  Context {G : Group} (x y z : G).
  Definition grp_unit_l := left_identity x.
  Definition grp_unit_r := right_identity x.

End GroupLaws.
Global Instance ispointed_group (G : Group)
  : IsPointed G.
exact (@mon_unit G _).
Defined.
Definition ptype_group : Group -> pType.
exact (fun G => [G, _]).
Defined.

Coercion ptype_group : Group >-> pType.

Record GroupHomomorphism (G H : Group) := Build_GroupHomomorphism' {
  grp_homo_map :> group_type G -> group_type H;
  grp_homo_ishomo :: IsMonoidPreserving grp_homo_map;
}.
Definition pmap_GroupHomomorphism {G H : Group} (f : GroupHomomorphism G H) : G ->* H.
exact (Build_pMap G H f (@monmor_unitmor _ _ _ _ _ _ _ (@grp_homo_ishomo G H f))).
Defined.
Coercion pmap_GroupHomomorphism : GroupHomomorphism >-> pForall.

Definition grp_homo_unit {G H} (f : GroupHomomorphism G H)
  : f (mon_unit) = mon_unit.
Admitted.

Definition grp_homo_op {G H} (f : GroupHomomorphism G H)
  : forall x y : G, f (x * y) = f x * f y.
Admitted.

Definition Build_GroupHomomorphism {G H : Group}
  (f : G -> H) {h : IsSemiGroupPreserving f}
  : GroupHomomorphism G H.
Proof.
  srapply (Build_GroupHomomorphism' _ _ f).
  split.
  1: exact h.
  unfold IsUnitPreserving.
  apply (group_cancelL (f mon_unit)).
  refine (_ @ (grp_unit_r _)^).
  refine (_ @ ap _ (monoid_left_id _ mon_unit)).
  symmetry.
  apply h.
Defined.
Definition grp_homo_id {G : Group} : GroupHomomorphism G G.
exact (Build_GroupHomomorphism idmap).
Defined.

Definition grp_homo_compose {G H K : Group}
  : GroupHomomorphism H K -> GroupHomomorphism G H -> GroupHomomorphism G K.
Proof.
  intros f g.
  srapply (Build_GroupHomomorphism (f o g)).
Defined.

Record GroupIsomorphism (G H : Group) := Build_GroupIsomorphism {
  grp_iso_homo :> GroupHomomorphism G H;
  isequiv_group_iso :: IsEquiv grp_iso_homo;
}.
Global Instance isgraph_group : IsGraph Group.
exact (Build_IsGraph Group GroupHomomorphism).
Defined.
Global Instance is01cat_group : Is01Cat Group.
exact (Build_Is01Cat Group _ (@grp_homo_id) (@grp_homo_compose)).
Defined.

Local Notation grp_homo_map' A B := (@grp_homo_map A B : _ -> (group_type A $-> _)).
Global Instance is2graph_group : Is2Graph Group.
exact (fun A B => isgraph_induced (grp_homo_map' A B)).
Defined.

Global Instance is1cat_group : Is1Cat Group.
Admitted.

Definition grp_trivial : Group.
Proof.
  refine (Build_Group Unit (fun _ _ => tt) tt (fun _ => tt) _).
  repeat split; try exact _; by intros [].
Defined.

Definition grp_trivial_rec (G : Group) : GroupHomomorphism grp_trivial G.
Proof.
  snrapply Build_GroupHomomorphism.
  1: exact (fun _ => group_unit).
  intros ??; symmetry; apply grp_unit_l.
Defined.

Definition grp_trivial_corec (G : Group) : GroupHomomorphism G grp_trivial.
Admitted.

Global Instance ispointedcat_group : IsPointedCat Group.
Proof.
  snrapply Build_IsPointedCat.
  -
 exact grp_trivial.
  -
 intro G.
    exists (grp_trivial_rec G).
    intros g []; cbn.
    exact (grp_homo_unit g)^.
  -
 intro G.
    exists (grp_trivial_corec G).
    intros g x; cbn.
    apply path_unit.
Defined.
Definition grp_homo_const {G H : Group} : GroupHomomorphism G H.
exact (zero_morphism).
Defined.

Section GrpPullback.

  Context {A B C : Group} (f : B $-> A) (g : C $-> A).

  Local Instance grp_pullback_sgop : SgOp (Pullback f g).
  Proof.
    intros [b [c p]] [d [e q]].
    refine (b * d; c * e; _).
    refine (grp_homo_op f b d @ (_ @ _) @ (grp_homo_op g c e)^).
    -
 exact (ap (fun y:A => f b * y) q).
    -
 exact (ap (fun x:A => x * g e) p).
  Defined.

  Local Instance grp_pullback_sgop_associative
    : Associative grp_pullback_sgop.
Admitted.

  Local Instance grp_pullback_issemigroup : IsSemiGroup (Pullback f g) := {}.
Local Instance grp_pullback_mon_unit : MonUnit (Pullback f g).
Admitted.

  Local Instance grp_pullback_leftidentity
    : LeftIdentity grp_pullback_sgop grp_pullback_mon_unit.
Admitted.

  Local Instance grp_pullback_rightidentity
    : RightIdentity grp_pullback_sgop grp_pullback_mon_unit.
Admitted.

  Local Instance ismonoid_grp_pullback : IsMonoid (Pullback f g) := {}.

  Local Instance grp_pullback_negate : Negate (Pullback f g).
Admitted.

  Local Instance grp_pullback_leftinverse
    : LeftInverse grp_pullback_sgop grp_pullback_negate grp_pullback_mon_unit.
Admitted.

  Local Instance grp_pullback_rightinverse
    : RightInverse grp_pullback_sgop grp_pullback_negate grp_pullback_mon_unit.
Admitted.

  Global Instance isgroup_grp_pullback : IsGroup (Pullback f g) := {}.
Definition grp_pullback : Group.
exact (Build_Group (Pullback f g) _ _ _ _).
Defined.

  Definition grp_pullback_pr1 : grp_pullback $-> B.
  Proof.
    snrapply Build_GroupHomomorphism.
    -
 apply pullback_pr1.
    -
 intros x y.
reflexivity.
  Defined.

  Definition grp_pullback_pr2 : grp_pullback $-> C.
  Proof.
    snrapply Build_GroupHomomorphism.
    -
 apply pullback_pr2.
    -
 intros x y.
reflexivity.
  Defined.

  Proposition grp_pullback_corec {X : Group}
              (b : X $-> B) (c : X $-> C)
              (p : f o b == g o c)
    : X $-> grp_pullback.
  Proof.
    snrapply Build_GroupHomomorphism.
    -
 exact (fun x => (b x; c x; p x)).
    -
 intros x y.
      srapply path_sigma.
      +
 simpl.
        apply (grp_homo_op b).
      +
 unfold pr2.
        refine (transport_sigma' _ _ @ _).
unfold pr1.
        apply path_sigma_hprop.
        simpl.
        apply (grp_homo_op c).
  Defined.

End GrpPullback.

Record AbGroup := {
  abgroup_group : Group;
  abgroup_commutative : Commutative (@group_sgop abgroup_group);
}.

Coercion abgroup_group : AbGroup >-> Group.
Global Instance isgraph_abgroup : IsGraph AbGroup.
exact (isgraph_induced abgroup_group).
Defined.
Global Instance is01cat_abgroup : Is01Cat AbGroup.
exact (is01cat_induced abgroup_group).
Defined.

Section AbPullback.

  Context {A B C : AbGroup} (f : B $-> A) (g : C $-> A).

  Global Instance ab_pullback_commutative
    : Commutative (@group_sgop (grp_pullback f g)).
Admitted.
Definition ab_pullback
    : AbGroup.
exact (Build_AbGroup (grp_pullback f g) _).
Defined.

End AbPullback.

Definition IsComplex {F X Y} (i : F ->* X) (f : X ->* Y)
  := (f o* i ==* pconst).

Definition cxfib {F X Y : pType} {i : F ->* X} {f : X ->* Y}
  (cx : IsComplex i f)
  : F ->* pfiber f.
Proof.
  srapply Build_pMap.
  -
 exact (fun x => (i x; cx x)).
  -
 cbn.
refine (path_sigma' _ (point_eq i) _); cbn.
    refine (transport_paths_Fl _ _ @ _).
    apply moveR_Vp.
    exact ((concat_p1 _)^ @ point_htpy cx).
Defined.

Cumulative Class IsExact (n : Modality) {F X Y : pType} (i : F ->* X) (f : X ->* Y) :=
{
  cx_isexact : IsComplex i f ;
  conn_map_isexact : IsConnMap n (cxfib cx_isexact)
}.
Import HoTT.Basics.

Record AbSES' {B A : AbGroup@{u}} := Build_AbSES {
    middle :  AbGroup@{u};
    inclusion : A $-> middle;
    projection : middle $-> B;
    isembedding_inclusion : IsEmbedding inclusion;
    issurjection_projection : IsSurjection projection;
    isexact_inclusion_projection : IsExact (Tr (-1)) inclusion projection;
  }.

Coercion middle : AbSES' >-> AbGroup.

Global Existing Instances isembedding_inclusion issurjection_projection isexact_inclusion_projection.

Arguments AbSES' B A : clear implicits.
Arguments Build_AbSES {B A}.

Global Instance ispointed_abses {B A : AbGroup@{u}}
  : IsPointed (AbSES' B A).
Admitted.
Definition AbSES (B A : AbGroup@{u}) : pType.
exact ([AbSES' B A, _]).
Defined.

Definition abses_path_data_iso
  {B A : AbGroup@{u}} (E F : AbSES B A)
  := {phi : GroupIsomorphism E F
            & (phi $o inclusion _ == inclusion _)
              * (projection _ == projection _ $o phi)}.

Proposition equiv_path_abses_iso `{Univalence}
  {B A : AbGroup@{u}} {E F : AbSES' B A}
  : abses_path_data_iso E F <~> E = F.
Admitted.

Definition abses_pullback {A B B' : AbGroup} (f : B' $-> B)
  : AbSES B A -> AbSES B' A.
Proof.
  intro E.
  snrapply (Build_AbSES (ab_pullback (projection E) f)
                        (grp_pullback_corec _ _ (inclusion _) grp_homo_const _)
                        (grp_pullback_pr2 (projection _) f)).
  -
 intro x.
    nrefine (_ @ (grp_homo_unit f)^).
    apply isexact_inclusion_projection.
  -
 exact (cancelL_isembedding (g:= grp_pullback_pr1 _ _)).
  -
 rapply conn_map_pullback'.
  -
 snrapply Build_IsExact.
    +
 snrapply phomotopy_homotopy_hset.
      *
 exact _.
      *
 reflexivity.
    +
 nrefine (cancelL_equiv_conn_map
                 _ _ (hfiber_pullback_along_pointed f (projection _) (grp_homo_unit _))).
      nrefine (conn_map_homotopic _ _ _ _ (conn_map_isexact (IsExact:=isexact_inclusion_projection _))).
      intro a.
      by apply path_sigma_hprop.
Defined.

Definition abses_pullback_id `{Univalence} {A B : AbGroup}
  : abses_pullback (A:=A) (@grp_homo_id B) == idmap.
Proof.
  intro E.
  apply equiv_path_abses_iso; srefine (_; (_, _)).
  1: rapply (Build_GroupIsomorphism _ _ (grp_pullback_pr1 _ _)).
  1: reflexivity.
  intros [a [p q]]; cbn.
  exact q^.
Defined.
