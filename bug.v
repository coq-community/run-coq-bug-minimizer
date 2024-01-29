
(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "-parsing" "-w" "+undeclared-scope" "-w" "+non-primitive-record" "-w" "-ambiguous-paths" "-w" "-redundant-canonical-projection" "-w" "-projection-no-head-constant" "-w" "-deprecated-native-compiler-option" "-native-compiler" "ondemand" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/analysis/classical" "mathcomp.classical" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/analysis/theories" "mathcomp.analysis" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/HB" "HB" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/elpi" "elpi" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/mathcomp" "mathcomp" "-top" "Top.bug_01") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 1520 lines to 102 lines, then from 115 lines to 7080 lines, then from 7084 lines to 5514 lines, then from 5204 lines to 214 lines, then from 227 lines to 8975 lines, then from 8977 lines to 9174 lines, then from 8558 lines to 3022 lines, then from 3030 lines to 641 lines, then from 654 lines to 3374 lines, then from 3378 lines to 3344 lines, then from 3149 lines to 2937 lines, then from 2945 lines to 2872 lines, then from 2880 lines to 2758 lines, then from 2766 lines to 2622 lines, then from 2630 lines to 2480 lines, then from 2488 lines to 2302 lines, then from 2310 lines to 2048 lines, then from 2056 lines to 1781 lines, then from 1789 lines to 1215 lines, then from 1223 lines to 1119 lines, then from 1137 lines to 891 lines, then from 904 lines to 4337 lines, then from 4342 lines to 4269 lines, then from 4063 lines to 2355 lines, then from 2363 lines to 992 lines, then from 1005 lines to 1959 lines, then from 1964 lines to 2248 lines, then from 2194 lines to 1028 lines, then from 1046 lines to 1010 lines, then from 1023 lines to 1109 lines, then from 1115 lines to 1008 lines, then from 1027 lines to 1008 lines, then from 1021 lines to 2291 lines, then from 2297 lines to 1497 lines, then from 1344 lines to 1170 lines, then from 1183 lines to 7798 lines, then from 7804 lines to 8295 lines, then from 8038 lines to 6547 lines, then from 6555 lines to 4896 lines, then from 4904 lines to 2829 lines, then from 2837 lines to 1739 lines, then from 1757 lines to 1434 lines, then from 1447 lines to 8252 lines, then from 0 lines to 8252 lines, then from 8263 lines to 7611 lines, then from 6945 lines to 6086 lines, then from 6094 lines to 4654 lines, then from 4662 lines to 3198 lines, then from 3206 lines to 2308 lines, then from 2326 lines to 1833 lines, then from 1846 lines to 1907 lines, then from 1913 lines to 1826 lines, then from 1840 lines to 10763 lines, then from 10767 lines to 12343 lines, then from 11737 lines to 9895 lines, then from 9903 lines to 8999 lines, then from 9007 lines to 7924 lines, then from 7932 lines to 6365 lines, then from 6373 lines to 4472 lines, then from 4480 lines to 2859 lines, then from 2876 lines to 2066 lines, then from 2079 lines to 6165 lines, then from 6168 lines to 5694 lines, then from 5526 lines to 3390 lines, then from 3398 lines to 2248 lines, then from 2266 lines to 2055 lines, then from 2068 lines to 4666 lines, then from 4671 lines to 4197 lines, then from 4057 lines to 2205 lines, then from 2223 lines to 2079 lines, then from 2092 lines to 2611 lines, then from 2617 lines to 2213 lines, then from 2169 lines to 2112 lines, then from 2125 lines to 4601 lines, then from 4607 lines to 3910 lines, then from 3720 lines to 2295 lines, then from 2313 lines to 2163 lines, then from 2176 lines to 2909 lines, then from 2915 lines to 2366 lines, then from 2295 lines to 2216 lines, then from 2229 lines to 6981 lines, then from 6987 lines to 6442 lines, then from 6185 lines to 3403 lines, then from 3411 lines to 2242 lines, then from 2255 lines to 4425 lines, then from 4431 lines to 4296 lines, then from 4077 lines to 2288 lines *)
(* coqc version 8.20+alpha compiled with OCaml 4.14.1
   coqtop version 532fcf76d13e:/builds/coq/coq/_build/default,(HEAD detached at 26c84c7) (26c84c7924a0b719c579dacbad84a61567e196e9)
   Expected coqc runtime on this file: 6.058 sec *)
Require mathcomp.ssreflect.eqtype.
Require HB.structures.
Import mathcomp.ssreflect.ssreflect.

Notation succn := Datatypes.S.

Notation "n .+1" := (succn n) (at level 2, left associativity,
  format "n .+1") : nat_scope.

Section ExMinn.

End ExMinn.

Section ExMaxn.

End ExMaxn.

Section Iteration.

Variable T : Type.
Implicit Types x y : T.

Definition iteri n f x :=
  let fix loop m := if m is i.+1 then f i (loop i) else x in loop n.

Definition iterop n op x :=
  let f i y := if i is 0 then x else op x y in iteri n f.

End Iteration.

Coercion nat_of_bool (b : bool) := if b then 1 else 0.

Section ContraLeq.

End ContraLeq.

Section Monotonicity.

Section NatToNat.

End NatToNat.
End Monotonicity.

Section NumberInterpretation.

Section Trec.

End Trec.

End NumberInterpretation.
Import mathcomp.ssreflect.ssrfun.
Import mathcomp.ssreflect.ssrbool.
Import mathcomp.ssreflect.eqtype.

Set Implicit Arguments.
Unset Strict Implicit.

Declare Scope seq_scope.
Open Scope seq_scope.

Notation seq := list.

Infix "::" := cons : seq_scope.

Notation "[ :: ]" := nil (at level 0, format "[ :: ]") : seq_scope.

Section Sequences.

Variable T : Type.

Section SeqFind.

Variable a : pred T.

Fixpoint filter s :=
  if s is x :: s' then if a x then x :: filter s' else filter s' else [::].

Fixpoint count s := if s is x :: s' then a x + count s' else 0.

End SeqFind.

End Sequences.

Notation count_mem x := (count (pred_of_simpl (pred1 x))).

Module Export Choice.

Section ClassDef.

Record mixin_of T := Mixin {
  find : pred T -> nat -> option T;
  _ : forall P n x, find P n = Some x -> P x;
  _ : forall P : pred T, (exists x, P x) -> exists n, find P n;
  _ : forall P Q : pred T, P =1 Q -> find P =1 find Q
}.
Record class_of T := Class {base : Equality.class_of T; mixin : mixin_of T}.
Local Coercion base : class_of >->  Equality.class_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Definition pack m :=
  fun b bT & phant_id (Equality.class bT) b => Pack (@Class T b m).

Definition eqType := @Equality.Pack cT class.

End ClassDef.
Coercion base : class_of >-> Equality.class_of.
Coercion sort : type >-> Sortclass.
Canonical eqType.
Notation choiceType := type.
Notation ChoiceType T m := (@pack T m _ _ id).

Section ChoiceTheory.

Section OneType.

Variable T : choiceType.
Implicit Types P Q : pred T.

Lemma sig2W P Q : (exists2 x, P x & Q x) -> {x | P x & Q x}.
Admitted.

End OneType.

End ChoiceTheory.

Module Export Countable.

Record mixin_of (T : Type) : Type := Mixin {
  pickle : T -> nat;
  unpickle : nat -> option T;
  pickleK : pcancel pickle unpickle
}.
Import mathcomp.ssreflect.eqtype.

Module Finite.

Section RawMixin.

Variable T : eqType.

Definition axiom e := forall x : T, count_mem x e = 1.

Record mixin_of := Mixin {
  mixin_base : Countable.mixin_of T;
  mixin_enum : seq T;
  _ : axiom mixin_enum
}.

End RawMixin.

Section ClassDef.
Record class_of T := Class {
  base : Choice.class_of T;
  mixin : mixin_of (Equality.Pack base)
}.
Local Coercion base : class_of >-> Choice.class_of.

Structure type : Type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Definition eqType := @Equality.Pack cT class.

End ClassDef.

Module Import Exports.
Coercion mixin : class_of >-> mixin_of.
Coercion eqType : type >-> Equality.type.
Notation finType := type.
End Exports.

Module Type EnumSig.
Parameter enum : forall cT : type, seq cT.
End EnumSig.

Module EnumDef : EnumSig.
Definition enum cT := mixin_enum (class cT).
End EnumDef.

Notation enum := EnumDef.enum.

End Finite.
Export Finite.Exports.

Definition enum_mem T (mA : mem_pred _) := filter mA (Finite.enum T).
Notation enum A := (enum_mem (mem A)).

Section Def.

Variables (aT : finType) (rT : aT -> Type).

Inductive finfun_on : seq aT -> Type :=
| finfun_nil                            : finfun_on [::]
| finfun_cons x s of rT x & finfun_on s : finfun_on (x :: s).
Local Fixpoint finfun_rec (g : forall x, rT x) s : finfun_on s.
Admitted.

Variant finfun_of (ph : phant (forall x, rT x)) : predArgType :=
  FinfunOf of finfun_on (enum aT).

End Def.

Notation "{ 'ffun' fT }" := (finfun_of (Phant fT))
  (at level 0, format "{ 'ffun'  '[hv' fT ']' }") : type_scope.

Local Notation finPi aT rT := (forall x : Finite.sort aT, rT x) (only parsing).
Local Notation finfun_def :=
  (fun aT rT g => FinfunOf (Phant (finPi aT rT)) (finfun_rec g (enum aT))).

Module Type FinfunDefSig.
Parameter finfun : forall aT rT, finPi aT rT -> {ffun finPi aT rT}.
End FinfunDefSig.

Module FinfunDef : FinfunDefSig.
Definition finfun := finfun_def.
End FinfunDef.

Notation finfun := FinfunDef.finfun.

Declare Scope set_scope.

Section SetType.

Variable T : finType.

Inductive set_type : predArgType := FinSet of {ffun pred T}.
Definition set_of of phant T := set_type.

End SetType.
Open Scope set_scope.

Notation "{ 'set' T }" := (set_of (Phant T))
  (at level 0, format "{ 'set'  T }") : type_scope.

Local Notation finset_def := (fun T P => @FinSet T (finfun P)).

Module Type SetDefSig.
Parameter finset : forall T : finType, pred T -> {set T}.
End SetDefSig.

Module SetDef : SetDefSig.
Definition finset := finset_def.
End SetDef.

Notation finset := SetDef.finset.

Notation "[ 'set' x : T | P ]" := (finset (fun x : T => P%B))
  (at level 0, x at level 99, only parsing) : set_scope.
Notation "[ 'set' x | P ]" := [set x : _ | P]
  (at level 0, x, P at level 99, format "[ 'set'  x  |  P ]") : set_scope.

Reserved Notation "f @` A" (at level 24).
Reserved Notation "A `&` B" (at level 48, left associativity).
Reserved Notation "A `<=` B" (at level 70, no associativity).
Module Export mathcomp_DOT_ssreflect_DOT_order_WRAPPED.
Module Export order.

Declare Scope order_scope.

Delimit Scope order_scope with O.
Local Open Scope order_scope.

Module Export Order.

Module POrder.
Section ClassDef.

Record mixin_of (T0 : Type) (b : Equality.class_of T0)
                (T := Equality.Pack b) := Mixin {
  le : rel T;
  lt : rel T;
  _  : forall x y, lt x y = (y != x) && (le x y);
  _  : reflexive     le;
  _  : antisymmetric le;
  _  : transitive    le;
}.
Record class_of (T : Type) := Class {
  base  : Choice.class_of T;
  mixin : mixin_of base;
}.

Local Coercion base : class_of >-> Choice.class_of.

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.

Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (disp : unit) (cT : type disp).

Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.
End ClassDef.

Module Export Exports.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Canonical eqType.
Canonical choiceType.
Notation porderType := type.
End Exports.

End POrder.
Import POrder.Exports.

Section POrderDef.

Variable (disp : unit) (T : porderType disp).
Definition le : rel T.
Admitted.
Local Notation "x <= y" := (le x y) : order_scope.
Definition lt : rel T.
Admitted.
Local Notation "x < y" := (lt x y) : order_scope.
Definition leif (x y : T) C : Prop := ((x <= y) * ((x == y) = C))%type.

Definition lteif x y C := if C then x <= y else x < y.

End POrderDef.

Prenex Implicits lt le leif lteif.

Module Import POSyntax.

Notation "<=%O" := le : function_scope.

Notation "x <= y" := (le x y) : order_scope.
Notation "x <= y :> T" := ((x : T) <= (y : T)) (only parsing) : order_scope.
Notation "x >= y" := (y <= x) (only parsing) : order_scope.

Notation "x < y"  := (lt x y) : order_scope.
Notation "x < y :> T" := ((x : T) < (y : T)) (only parsing) : order_scope.
Notation "x > y"  := (y < x) (only parsing) : order_scope.

End POSyntax.

Module Export Lattice.
Section ClassDef.

Record mixin_of (T0 : Type) (b : POrder.class_of T0)
                (T := POrder.Pack tt b) := Mixin {
  meet : T -> T -> T;
  join : T -> T -> T;
  _ : commutative meet;
  _ : commutative join;
  _ : associative meet;
  _ : associative join;
  _ : forall y x, meet x (join x y) = x;
  _ : forall y x, join x (meet x y) = x;
  _ : forall x y, (x <= y) = (meet x y == x);
}.
Record class_of (T : Type) := Class {
  base  : POrder.class_of T;
  mixin : mixin_of base;
}.

Structure type (disp : unit) := Pack { sort; _ : class_of sort }.
End ClassDef.

Module Export Exports.
Coercion sort : type >-> Sortclass.
Notation latticeType  := type.
End Exports.
End Lattice.

Section LatticeDef.
Context {disp : unit} {T : latticeType disp}.
Definition meet : T -> T -> T.
Admitted.
Definition join : T -> T -> T.
Admitted.

End LatticeDef.

Module Import LatticeSyntax.

End LatticeSyntax.

Module Import BLatticeSyntax.

End BLatticeSyntax.

Module Import TBLatticeSyntax.

End TBLatticeSyntax.

Module Export DistrLattice.
Section ClassDef.

Record mixin_of (T0 : Type) (b : Lattice.class_of T0)
                (T := Lattice.Pack tt b) := Mixin {
  _ : @left_distributive T T meet join;
}.
End ClassDef.

End DistrLattice.

Module Import CBDistrLatticeSyntax.
End CBDistrLatticeSyntax.

Module Import CTBDistrLatticeSyntax.
End CTBDistrLatticeSyntax.

Module Export Total.
Section ClassDef.

Definition mixin_of T0 (b : POrder.class_of T0) (T := POrder.Pack tt b) :=
  total (<=%O : rel T).

End ClassDef.

End Total.

Module Import DualSyntax.

End DualSyntax.

Module Import POrderTheory.
End POrderTheory.

Module Import DualPOrder.
End DualPOrder.

Module Import DualLattice.
End DualLattice.

Module Import LatticeTheoryMeet.
End LatticeTheoryMeet.

Module Import LatticeTheoryJoin.
End LatticeTheoryJoin.

Module Import DistrLatticeTheory.
End DistrLatticeTheory.

Module Import TotalTheory.
End TotalTheory.

Module Import BLatticeTheory.
End BLatticeTheory.

Module Import DualTBLattice.
End DualTBLattice.

Module Import TBLatticeTheory.
End TBLatticeTheory.

Module Import BDistrLatticeTheory.
End BDistrLatticeTheory.

Module Import DualTBDistrLattice.
End DualTBDistrLattice.

Module Import TBDistrLatticeTheory.
End TBDistrLatticeTheory.

Module Import CBDistrLatticeTheory.
End CBDistrLatticeTheory.

Module Import CTBDistrLatticeTheory.
End CTBDistrLatticeTheory.

Module Import ProdSyntax.

End ProdSyntax.

Module Import LexiSyntax.

End LexiSyntax.

Module Import DualOrder.
End DualOrder.

Module Import EnumVal.
End EnumVal.

Module Export Syntax.
Export POSyntax.
End Syntax.

End Order.

Export Order.POrder.Exports.

End order.
Module Export mathcomp.
Module Export ssreflect.
Module Export order.
Include mathcomp_DOT_ssreflect_DOT_order_WRAPPED.order.
End order.
Module Export mathcomp_DOT_algebra_DOT_ssralg_WRAPPED.
Module Export ssralg.

Declare Scope ring_scope.
Reserved Notation "f \+ g" (at level 50, left associativity).
Reserved Notation "f \* g" (at level 40, left associativity).

Delimit Scope ring_scope with R.
Local Open Scope ring_scope.

Module Import GRing.

Module Export Zmodule.

Record mixin_of (V : Type) : Type := Mixin {
  zero : V;
  opp : V -> V;
  add : V -> V -> V;
  _ : associative add;
  _ : commutative add;
  _ : left_id zero add;
  _ : left_inverse zero opp add
}.

Section ClassDef.
Record class_of T := Class { base : Choice.class_of T; mixin : mixin_of T }.
Local Coercion base : class_of >-> Choice.class_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.

Definition pack m :=
  fun bT b & phant_id (Choice.class bT) b => Pack (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition choiceType := @Choice.Pack cT class.

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> Choice.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Canonical choiceType.
Notation zmodType := type.
Notation ZmodType T m := (@pack T m _ _ id).
Notation ZmodMixin := Mixin.
Notation "[ 'zmodType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'zmodType'  'of'  T ]") : form_scope.
End Exports.

End Zmodule.

Definition zero V := Zmodule.zero (Zmodule.class V).
Definition opp V := Zmodule.opp (Zmodule.class V).
Definition add V := Zmodule.add (Zmodule.class V).

Local Notation "0" := (zero _) : ring_scope.
Local Notation "+%R" := (@add _) : function_scope.
Local Notation "x + y" := (add x y) : ring_scope.

Definition natmul V x n := nosimpl iterop _ n +%R x (zero V).

Module Ring.

Record mixin_of (R : zmodType) : Type := Mixin {
  one : R;
  mul : R -> R -> R;
  _ : associative mul;
  _ : left_id one mul;
  _ : right_id one mul;
  _ : left_distributive mul +%R;
  _ : right_distributive mul +%R;
  _ : one != 0
}.

Section ClassDef.
Record class_of (R : Type) : Type := Class {
  base : Zmodule.class_of R;
  mixin : mixin_of (Zmodule.Pack base)
}.
Local Coercion base : class_of >-> Zmodule.class_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.

Definition pack b0 (m0 : mixin_of (@Zmodule.Pack T b0)) :=
  fun bT b & phant_id (Zmodule.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m).

Definition eqType := @Equality.Pack cT class.
Definition zmodType := @Zmodule.Pack cT class.

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> Zmodule.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Canonical eqType.
Coercion zmodType : type >-> Zmodule.type.
Canonical zmodType.
Notation ringType := type.
Notation RingType T m := (@pack T _ m _ _ id _ id).
Notation RingMixin := Mixin.
Notation "[ 'ringType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'ringType'  'of'  T ]") : form_scope.
End Exports.

End Ring.
Import Ring.Exports.
Definition one (R : ringType) : R.
Admitted.
Definition mul (R : ringType) : R -> R -> R.
exact (Ring.mul (Ring.class R)).
Defined.
Definition exp R x n := nosimpl iterop _ n (@mul R) x (one R).

Local Notation "1" := (one _) : ring_scope.
Local Notation "*%R" := (@mul _) : function_scope.
Local Notation "x * y" := (mul x y) : ring_scope.
Local Notation "x ^+ n" := (exp x n) : ring_scope.

Section RingTheory.

Variable R : ringType.
Implicit Types x y : R.

Lemma mulrA : @associative R *%R.
Admitted.
Lemma mul1r : @left_id R R 1 *%R.
Admitted.
Lemma mulrDl : @left_distributive R R *%R +%R.
Admitted.
Lemma mulrDr : @right_distributive R R *%R +%R.
Admitted.
Lemma expr2 x : x ^+ 2 = x * x.
Admitted.

End RingTheory.

Module Lmodule.

Structure mixin_of (R : ringType) (V : zmodType) : Type := Mixin {
  scale : R -> V -> V;
  _ : forall a b v, scale a (scale b v) = scale (a * b) v;
  _ : left_id 1 scale;
  _ : right_distributive scale +%R;
  _ : forall v, {morph scale^~ v: a b / a + b}
}.

Section ClassDef.

Variable R : ringType.
Record class_of V := Class {
  base : Zmodule.class_of V;
  mixin : mixin_of R (Zmodule.Pack base)
}.

Structure type (phR : phant R) := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variable (phR : phant R) (T : Type) (cT : type phR).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.

Definition pack b0 (m0 : mixin_of R (@Zmodule.Pack T b0)) :=
  fun bT b & phant_id (Zmodule.class bT) b =>
  fun    m & phant_id m0 m => Pack phR (@Class T b m).

End ClassDef.

Module Import Exports.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Notation lmodType R := (type (Phant R)).
Notation LmodType R T m := (@pack _ (Phant R) T _ m _ _ id _ id).
End Exports.

End Lmodule.
Import Lmodule.Exports.
Definition scale (R : ringType) (V : lmodType R) : R -> V -> V.
exact (Lmodule.scale (Lmodule.class V)).
Defined.

Module Export Lalgebra.

Section ClassDef.

Variable R : ringType.

Structure type (phR : phant R) := Pack {sort; _ : class_of sort}.

End ClassDef.

Module Export Exports.
Notation lalgType R := (type (Phant R)).
End Exports.

End Lalgebra.

Definition regular R : Type := R.
Local Notation "R ^o" := (regular R) (at level 2, format "R ^o") : type_scope.

Section LalgebraTheory.

Variables (R : ringType) (A : lalgType R).
Canonical regular_zmodType := [zmodType of R^o].
Canonical regular_ringType := [ringType of R^o].

Definition regular_lmodMixin :=
  let mkMixin := @Lmodule.Mixin R regular_zmodType (@mul R) in
  mkMixin (@mulrA R) (@mul1r R) (@mulrDr R) (fun v a b => mulrDl a b v).

Canonical regular_lmodType := LmodType R R^o regular_lmodMixin.

End LalgebraTheory.

Section LiftedZmod.
Variables (U : Type) (V : zmodType).
Definition null_fun_head (phV : phant V) of U : V.
Admitted.
Definition add_fun (f g : U -> V) x := f x + g x.
End LiftedZmod.

Section LiftedRing.
Variables (R : ringType) (T : Type).
Implicit Type f : T -> R.
Definition mul_fun f g x := f x * g x.
End LiftedRing.

Notation null_fun V := (null_fun_head (Phant V)) (only parsing).

Module ComRing.

Section ClassDef.
Record class_of R :=
  Class {base : Ring.class_of R; mixin : commutative (Ring.mul base)}.
Local Coercion base : class_of >-> Ring.class_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variable (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition ringType := @Ring.Pack cT class.

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> Ring.class_of.
Coercion sort : type >-> Sortclass.
Canonical ringType.
Notation comRingType := type.
End Exports.

End ComRing.
Import ComRing.Exports.

Section ComRingTheory.

Variable R : comRingType.
Lemma mulrACA : @interchange R *%R *%R.
Admitted.

End ComRingTheory.

Module UnitRing.

Record mixin_of (R : ringType) : Type := Mixin {
  unit : pred R;
  inv : R -> R;
  _ : {in unit, left_inverse 1 inv *%R};
  _ : {in unit, right_inverse 1 inv *%R};
  _ : forall x y, y * x = 1 /\ x * y = 1 -> unit x;
  _ : {in [predC unit], inv =1 id}
}.

Section ClassDef.
Record class_of (R : Type) : Type := Class {
  base : Ring.class_of R;
  mixin : mixin_of (Ring.Pack base)
}.
Local Coercion base : class_of >-> Ring.class_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition ringType := @Ring.Pack cT class.

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> Ring.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion ringType : type >-> Ring.type.
Notation unitRingType := type.
End Exports.

End UnitRing.
Import UnitRing.Exports.

Definition unit {R : unitRingType} :=
  [qualify a u : R | UnitRing.unit (UnitRing.class R) u].

Module Export ComUnitRing.

Section ClassDef.
Record class_of (R : Type) : Type := Class {
  base : ComRing.class_of R;
  mixin : UnitRing.mixin_of (Ring.Pack base)
}.
Definition base2 R m := UnitRing.Class (@mixin R m).

End ClassDef.

Module Import Exports.
Coercion base : class_of >-> ComRing.class_of.
Coercion base2 : class_of >-> UnitRing.class_of.
End Exports.

End ComUnitRing.
Import ComUnitRing.Exports.

Module Export IntegralDomain.

Definition axiom (R : ringType) :=
  forall x y : R, x * y = 0 -> (x == 0) || (y == 0).

Section ClassDef.
Record class_of (R : Type) : Type :=
  Class {base : ComUnitRing.class_of R; mixin : axiom (Ring.Pack base)}.

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> ComUnitRing.class_of.
End Exports.

End IntegralDomain.

Module Export Field.

Definition mixin_of (R : unitRingType) := forall x : R, x != 0 -> x \in unit.

End Field.

Module Export Theory.
Definition expr2 := expr2.
Definition mulrACA := mulrACA.

End Theory.

End GRing.
Export Zmodule.Exports.
Export Ring.Exports.
Export UnitRing.Exports.
Export ComUnitRing.Exports.
Export IntegralDomain.Exports.

Notation "0" := (zero _) : ring_scope.
Notation "- x" := (opp x) : ring_scope.
Notation "x + y" := (add x y) : ring_scope.
Notation "x - y" := (add x (- y)) : ring_scope.
Notation "x *+ n" := (natmul x n) : ring_scope.

Notation "1" := (one _) : ring_scope.
Notation "x * y" := (mul x y) : ring_scope.
Notation "x ^+ n" := (exp x n) : ring_scope.

Notation "*:%R" := (@scale _ _) : function_scope.
Notation "\0" := (null_fun _) : ring_scope.
Notation "f \+ g" := (add_fun f g) : ring_scope.
Notation "f \* g" := (mul_fun f g) : ring_scope.

Notation "R ^o" := (regular R) (at level 2, format "R ^o") : type_scope.
Canonical regular_ringType.
Canonical regular_lmodType.

End ssralg.
Module Export mathcomp.
Module Export algebra.
Module Export ssralg.
Include mathcomp_DOT_algebra_DOT_ssralg_WRAPPED.ssralg.
End ssralg.
Local Open Scope ring_scope.

Fact ring_display : unit.
Admitted.

Module Export Num.

Record normed_mixin_of (R T : zmodType)
       (Rorder : Order.POrder.mixin_of (Equality.class R))
       (le_op := Order.POrder.le Rorder)
  := NormedMixin {
  norm_op : T -> R;
  _ : forall x y, le_op (norm_op (x + y)) (norm_op x + norm_op y);
  _ : forall x, norm_op x = 0 -> x = 0;
  _ : forall x n, norm_op (x *+ n) = norm_op x *+ n;
  _ : forall x, norm_op (- x) = norm_op x;
}.

Record mixin_of (R : ringType)
       (Rorder : Order.POrder.mixin_of (Equality.class R))
       (le_op := Order.POrder.le Rorder) (lt_op := Order.POrder.lt Rorder)
       (normed : @normed_mixin_of R R Rorder) (norm_op := norm_op normed)
  := Mixin {
  _ : forall x y, lt_op 0 x -> lt_op 0 y -> lt_op 0 (x + y);
  _ : forall x y, le_op 0 x -> le_op 0 y -> le_op x y || le_op y x;
  _ : {morph norm_op : x y / x * y};
  _ : forall x y, (le_op x y) = (norm_op (y - x) == y - x);
}.

Local Notation ring_for T b := (@GRing.Ring.Pack T b).

Module Export NumDomain.

Section ClassDef.
Record class_of T := Class {
  base : GRing.IntegralDomain.class_of T;
  order_mixin : Order.POrder.mixin_of (Equality.class (ring_for T base));
  normed_mixin : normed_mixin_of (ring_for T base) order_mixin;
  mixin : mixin_of normed_mixin;
}.

Local Coercion base : class_of >-> GRing.IntegralDomain.class_of.
Local Coercion order_base T (class_of_T : class_of T) :=
  @Order.POrder.Class _ class_of_T (order_mixin class_of_T).

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c  as cT' := cT return class_of cT' in c.
Definition ringType := @GRing.Ring.Pack cT class.
Definition comRingType := @GRing.ComRing.Pack cT class.
Definition unitRingType := @GRing.UnitRing.Pack cT class.
Definition porderType := @Order.POrder.Pack ring_display cT class.
Definition porder_zmodType := @GRing.Zmodule.Pack porderType class.

End ClassDef.

Module Export Exports.
Coercion base  : class_of >-> GRing.IntegralDomain.class_of.
Coercion order_base : class_of >-> Order.POrder.class_of.
Canonical ringType.
Canonical comRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical porderType.
Canonical porder_zmodType.
Notation numDomainType := type.
End Exports.

End NumDomain.

Local Notation num_for T b := (@NumDomain.Pack T b).

Module Export NormedZmodule.

Section ClassDef.

Variable R : numDomainType.
Record class_of (T : Type) := Class {
  base : GRing.Zmodule.class_of T;
  mixin : @normed_mixin_of R (@GRing.Zmodule.Pack T base) (NumDomain.class R);
}.

Local Coercion base : class_of >-> GRing.Zmodule.class_of.

Structure type (phR : phant R) :=
  Pack { sort; _ : class_of sort }.
Local Coercion sort : type >-> Sortclass.

Variables (phR : phant R) (T : Type) (cT : type phR).

Definition class := let: Pack _ c := cT return class_of cT in c.
Definition zmodType := @GRing.Zmodule.Pack cT class.

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> GRing.Zmodule.class_of.
Coercion zmodType : type >-> GRing.Zmodule.type.
Notation normedZmodType R := (type (Phant R)).
End Exports.

End NormedZmodule.

Module NumDomain_joins.
Import NumDomain.
Section NumDomain_joins.

Variables (T : Type) (cT : type).

Notation class := (class cT).
Definition normedZmodType : normedZmodType cT.
exact (@NormedZmodule.Pack
     cT (Phant cT) cT (NormedZmodule.Class (NumDomain.normed_mixin class))).
Defined.

End NumDomain_joins.

Module Export Exports.
Coercion normedZmodType : type >-> NormedZmodule.type.
Canonical normedZmodType.
End Exports.
End NumDomain_joins.
Export NumDomain_joins.Exports.

Module Import Def.
Definition normr (R : numDomainType) (T : normedZmodType R) : T -> R.
Admitted.
Arguments normr {R T} x.

End Def.

Notation norm := normr (only parsing).

Module Import Syntax.

Notation "`| x |" := (norm x) : ring_scope.

Notation "x <= y" := (le x y) : ring_scope.

End Syntax.

Section ExtensionAxioms.

Variable R : numDomainType.
Definition real_closed_axiom : Prop.
Admitted.

End ExtensionAxioms.

Module NumField.

Section ClassDef.
Record class_of R := Class {
  base  : NumDomain.class_of R;
  mixin : GRing.Field.mixin_of (num_for R base);
}.
Local Coercion base : class_of >-> NumDomain.class_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition numDomainType := @NumDomain.Pack cT class.

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> NumDomain.class_of.
Coercion numDomainType : type >-> NumDomain.type.
Notation numFieldType := type.
End Exports.

End NumField.
Import NumField.Exports.

Module Export RealField.

Section ClassDef.
Record class_of R := Class {
  base  : NumField.class_of R;
  nmixin : Order.Lattice.mixin_of base;
  lmixin : Order.DistrLattice.mixin_of (Order.Lattice.Class nmixin);
  tmixin : Order.Total.mixin_of base;
}.

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> NumField.class_of.
End Exports.

End RealField.

Module RealClosedField.

Section ClassDef.
Record class_of R := Class {
  base : RealField.class_of R;
  mixin : real_closed_axiom (num_for R base)
}.
Local Coercion base : class_of >-> RealField.class_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition zmodType := @GRing.Zmodule.Pack cT class.
Definition ringType := @GRing.Ring.Pack cT class.
Definition porderType := @Order.POrder.Pack ring_display cT class.
Definition numDomainType := @NumDomain.Pack cT class.
Definition numFieldType := @NumField.Pack cT class.

End ClassDef.

Module Export Exports.
Coercion sort : type >-> Sortclass.
Canonical zmodType.
Canonical ringType.
Canonical porderType.
Canonical numDomainType.
Canonical numFieldType.
Notation rcfType := Num.RealClosedField.type.
End Exports.

End RealClosedField.
Import RealClosedField.Exports.

Module Import Internals.

Section RealClosed.
Variable R : rcfType.

Fact sqrtr_subproof (x : R) :
  exists2 y, 0 <= y & (if 0 <= x then y ^+ 2 == x else y == 0) : bool.
Admitted.

End RealClosed.

End Internals.

Module Import ExtraDef.

Definition sqrtr {R} x := s2val (sig2W (@sqrtr_subproof R x)).

End ExtraDef.
Notation sqrt := sqrtr.

Section NumIntegralDomainTheory.

Variable R : numDomainType.
Definition normrM : {morph norm : x y / (x : R) * y}.
Admitted.

Section NormedZmoduleTheory.

Variable V : normedZmodType R.
Implicit Types (v w : V).

Lemma normr_ge0 v : 0 <= `|v|.
Admitted.

End NormedZmoduleTheory.

End NumIntegralDomainTheory.
#[global] Hint Extern 0 (is_true (0 <= norm _)) => apply: normr_ge0 : core.

Section NumDomainOperationTheory.

Variable R : numDomainType.
Implicit Types x y z t : R.

Lemma ler_pM x1 y1 x2 y2 :
  0 <= x1 -> 0 <= x2 -> x1 <= y1 -> x2 <= y2 -> x1 * x2 <= y1 * y2.
Admitted.

End NumDomainOperationTheory.
#[deprecated(since="mathcomp 1.17.0", note="Use ler_pM instead.")]
Notation ler_pmul := ler_pM.

Section RealClosedFieldTheory.

Variable R : rcfType.
Implicit Types a x y : R.

Lemma sqr_sqrtr a : 0 <= a -> sqrt a ^+ 2 = a.
Admitted.

End RealClosedFieldTheory.

Import mathcomp.ssreflect.order.
Reserved Notation "x %:num" (at level 2, format "x %:num").
Local Open Scope order_scope.
Declare Scope snum_sign_scope.
Delimit Scope snum_sign_scope with snum_sign.
Declare Scope snum_nullity_scope.
Delimit Scope snum_nullity_scope with snum_nullity.
Variant nullity := NonZero | MaybeZero.
Coercion nullity_bool nz := if nz is NonZero then true else false.

Variant sign := EqZero | NonNeg | NonPos.
Variant real := Sign of sign | AnySign.
Variant reality := Real of real | Arbitrary.

Definition wider_nullity xnz ynz :=
  match xnz, ynz with
  | MaybeZero, _
  | NonZero, NonZero => true
  | NonZero, MaybeZero => false
  end.
Definition wider_sign xs ys :=
  match xs, ys with
  | NonNeg, NonNeg | NonNeg, EqZero
  | NonPos, NonPos | NonPos, EqZero
  | EqZero, EqZero => true
  | NonNeg, NonPos | NonPos, NonNeg
  | EqZero, NonPos | EqZero, NonNeg => false
  end.
Definition wider_real xr yr :=
  match xr, yr with
  | AnySign, _ => true
  | Sign sx, Sign sy => wider_sign sx sy
  | Sign _, AnySign => false
  end.
Definition wider_reality xr yr :=
  match xr, yr with
  | Arbitrary, _ => true
  | Real xr, Real yr => wider_real xr yr
  | Real _, Arbitrary => false
  end.

Module Export Signed.
Section Signed.
Context (disp : unit) (T : porderType disp) (x0 : T).
Definition reality_cond (n : reality) (x : T) :=
  match n with
  | Real (Sign EqZero) => x == x0
  | Real (Sign NonNeg) => x >= x0
  | Real (Sign NonPos) => x <= x0
  | Real AnySign       => (x0 <= x) || (x <= x0)
  | Arbitrary          => true
  end.

Record def (nz : nullity) (cond : reality) := Def {
  r :> T;
  #[canonical=no]
  P : (nz ==> (r != x0)) && reality_cond cond r
}.

End Signed.

Notation spec x0 nz cond x :=
  ((nullity_bool nz%snum_nullity ==> (x != x0))
   && (reality_cond x0 cond%snum_sign x)).

Definition mk {d T} x0 nz cond r P : @def d T x0 nz cond :=
  @Def d T x0 nz cond r P.
Coercion Sign : sign >-> real.
Coercion Real : real >-> reality.
Bind Scope snum_sign_scope with sign.
Notation ">=0" := NonNeg : snum_sign_scope.
Notation "!=0" := NonZero : snum_nullity_scope.
Notation "{ 'compare' x0 & nz & cond }" := (def x0 nz cond) : type_scope.
Notation "{ 'num' R & nz & cond }" := (def (0%R : R) nz cond) : ring_scope.
Notation "{ > x0 }" := (def x0 NonZero NonNeg) : type_scope.
Notation "x %:num" := (r x) : ring_scope.
Definition posnum (R : numDomainType) of phant R := {> 0%R : R}.
Notation "{ 'posnum' R }" := (@posnum _ (Phant R))  : ring_scope.

Class unify {T} f (x y : T) := Unify : f x y = true.
Class unify' {T} f (x y : T) := Unify' : f x y = true.
#[global] Instance unify'P {T} f (x y : T) : unify' f x y -> unify f x y.
Admitted.
#[global]
Hint Extern 0 (unify' _ _ _) => vm_compute; reflexivity : typeclass_instances.

Notation unify_nz nzx nzy :=
  (unify wider_nullity nzx%snum_nullity nzy%snum_nullity).
Notation unify_r rx ry :=
  (unify wider_reality rx%snum_sign ry%snum_sign).

Section Theory.
Context {d : unit} {T : porderType d} {x0 : T}
  {nz : nullity} {cond : reality}.
Local Notation sT := {compare x0 & nz & cond}.
Implicit Type x : sT.

Lemma gt0 x : unify_nz !=0 nz -> unify_r >=0 cond -> x0 < x%:num :> T.
Admitted.

Lemma ge0 x : unify_r >=0 cond -> x0 <= x%:num :> T.
Admitted.

End Theory.
Arguments ge0 {d T x0 nz cond} _ {_}.

#[global] Hint Extern 0 (is_true (0%R < _)%O) => solve [apply: gt0] : core.

Section RcfStability.
Context {R : rcfType}.

Definition sqrt_nonzero_subdef (xnz : nullity) (xr : reality) :=
  if xr is Real (Sign >=0) then xnz else MaybeZero.

Lemma sqrt_snum_subproof xnz xr (x : {num R & xnz & xr})
    (nz := sqrt_nonzero_subdef xnz xr) :
  Signed.spec 0 nz >=0 (Num.sqrt x%:num).
Admitted.

Canonical sqrt_snum xnz xr (x : {num R & xnz & xr}) :=
  Signed.mk (sqrt_snum_subproof x).

End RcfStability.

CoInductive posnum_spec (R : numDomainType) (x : R) :
  R -> bool -> bool -> bool -> Type :=
| IsPosnum (p : {posnum R}) : posnum_spec x (p%:num) false true true.

Lemma posnumP (R : numDomainType) (x : R) : 0 < x ->
  posnum_spec x x (x == 0) (0 <= x) (0 < x).
Admitted.
Export mathcomp.algebra.ssralg.

Lemma cid2 (A : Type) (P Q : A -> Prop) :
  (exists2 x : A, P x & Q x) -> {x : A | P x & Q x}.
Admitted.

Lemma pselect (P : Prop): {P} + {~P}.
Admitted.

Lemma gen_choiceMixin {T : Type} : Choice.mixin_of T.
Admitted.

Definition asbool (P : Prop) := if pselect P then true else false.

Notation "`[< P >]" := (asbool P) : bool_scope.

Lemma asboolT (P : Prop) : P -> `[<P>].
Admitted.

Definition gen_eq (T : Type) (u v : T) := `[<u = v>].
Lemma gen_eqP (T : Type) : Equality.axiom (@gen_eq T).
Admitted.
Definition gen_eqMixin {T : Type} := EqMixin (@gen_eqP T).

Canonical arrow_eqType (T : Type) (T' : eqType) :=
  EqType (T -> T') gen_eqMixin.
Canonical arrow_choiceType (T : Type) (T' : choiceType) :=
  ChoiceType (T -> T') gen_choiceMixin.

Canonical Prop_eqType := EqType Prop gen_eqMixin.
Canonical Prop_choiceType := ChoiceType Prop gen_choiceMixin.

Declare Scope classical_set_scope.

Definition set T := T -> Prop.
Definition in_set T (A : set T) : pred T.
Admitted.
Canonical set_predType T := @PredType T (set T) (@in_set T).
Local Open Scope classical_set_scope.
Delimit Scope classical_set_scope with classic.
Definition mkset {T} (P : T -> Prop) : set T.
exact (P).
Defined.

Notation "[ 'set' x : T | P ]" := (mkset (fun x : T => P)) : classical_set_scope.
Notation "[ 'set' x | P ]" := [set x : _ | P] : classical_set_scope.

Definition image {T rT} (A : set T) (f : T -> rT) :=
  [set y | exists2 x, A x & f x = y].

Section basic_definitions.
Context {T rT : Type}.
Implicit Types (T : Type) (A B : set T) (f : T -> rT) (Y : set rT).

Definition setT := [set _ : T | True].
Definition setI A B := [set x | A x /\ B x].

Definition subset A B := forall t, A t -> B t.

End basic_definitions.
Notation "[ 'set' : T ]" := (@setT T) : classical_set_scope.
Notation "A `&` B" := (setI A B) : classical_set_scope.

Notation "A `<=` B" := (subset A B) : classical_set_scope.
Notation "f @` A" := (image A f) (only parsing) : classical_set_scope.

Module Export Pointed.

Definition point_of (T : Type) := T.

Record class_of (T : Type) := Class {
  base : Choice.class_of T;
  mixin : point_of T
}.

Section ClassDef.

Structure type := Pack { sort; _ : class_of sort }.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c := cT return class_of cT in c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).
Local Coercion base : class_of >-> Choice.class_of.

Definition pack m :=
  fun bT b of phant_id (Choice.class bT) b => @Pack T (Class b m).
Definition choiceType := @Choice.Pack cT xclass.

End ClassDef.

Module Export Exports.

Coercion sort : type >-> Sortclass.
Coercion mixin : class_of >-> point_of.
Canonical choiceType.
Notation pointedType := type.
Notation PointedType T m := (@pack T m _ _ idfun).

End Exports.

End Pointed.
Definition point {M : pointedType} : M.
Admitted.

Canonical arrow_pointedType (T : Type) (T' : pointedType) :=
  PointedType (T -> T') (fun=> point).
Canonical Prop_pointedType := PointedType Prop False.

Notation "B \; A" :=
  ([set xy | exists2 z, A (xy.1, z) & B (z, xy.2)]) : classical_set_scope.
Import HB.structures.

Reserved Notation "''oinv_' f" (at level 8, f at level 2, format "''oinv_' f").

Section MainProperties.
Context {aT rT}  (A : set aT) (B : set rT) (f : aT -> rT).
Definition set_fun := {homo f : x / A x >-> B x}.
Definition set_surj := B `<=` f @` A.
End MainProperties.

HB.mixin Record isFun {aT rT} (A : set aT) (B : set rT) (f : aT -> rT) :=
  { funS : set_fun A B f }.
HB.structure Definition Fun {aT rT} (A : set aT) (B : set rT) :=
  { f of isFun _ _ A B f }.

HB.mixin Record OInv {aT rT} (f : aT -> rT) := { oinv : rT -> option aT }.
HB.structure Definition OInversible aT rT := {f of OInv aT rT f}.
Notation "{ 'oinv' aT >-> rT }" := (@OInversible.type aT rT) : type_scope.
Definition phant_oinv aT rT (f : {oinv aT >-> rT})
  of phantom (_ -> _) f := @oinv _ _ f.
Notation "''oinv_' f" := (@phant_oinv _ _ _ (Phantom (_ -> _) f%FUN)).

HB.structure Definition OInvFun aT rT A B :=
  {f of OInv aT rT f & isFun aT rT A B f}.

HB.mixin Record OInv_Inv {aT rT} (f : aT -> rT) of OInv _ _ f := {
  inv : rT -> aT;
  oliftV : olift inv = 'oinv_f
}.

HB.factory Record Inv {aT rT} (f : aT -> rT) := { inv : rT -> aT  }.
HB.builders Context {aT rT} (f : aT -> rT) of Inv _ _ f.
  HB.instance Definition _ := OInv.Build _ _ f (olift inv).
  HB.instance Definition _ := OInv_Inv.Build _ _ f erefl.
HB.end.

HB.structure Definition Inversible aT rT := {f of Inv aT rT f}.
Notation "{ 'inv' aT >->  rT }" := (@Inversible.type aT rT) : type_scope.
Definition phant_inv aT rT (f : {inv aT >-> rT}) of phantom (_ -> _) f :=
  @inv _ _ f.
Notation "f ^-1" := (@phant_inv _ _ _ (Phantom (_ -> _) f%FUN)) : fun_scope.

HB.structure Definition InvFun aT rT A B :=
  {f of Inv aT rT f & isFun aT rT A B f}.

HB.mixin Record OInv_CanV {aT rT} {A : set aT} {B : set rT}
  (f : aT -> rT) of OInv _ _ f := {
    oinvS : {homo 'oinv_f : x / B x >-> (some @` A) x};
    oinvK : {in B, ocancel 'oinv_f f};
  }.

HB.factory Record OCanV {aT rT} {A : set aT} {B : set rT} (f : aT -> rT) := {
    oinv; oinvS : {homo oinv : x / B x >-> (some @` A) x};
          oinvK : {in B, ocancel oinv f};
  }.
HB.builders Context {aT rT} {A : set aT} {B : set rT} (f : aT -> rT)
   of OCanV _ _ A B f.
 HB.instance Definition _ := OInv.Build _ _ f oinv.
 HB.instance Definition _ := OInv_CanV.Build _ _ A B f oinvS oinvK.
HB.end.

HB.structure Definition Surject {aT rT A B} := {f of @OCanV aT rT A B f}.

HB.structure Definition SurjFun aT rT A B :=
  {f of @Surject aT rT A B f & @Fun _ _ A B f}.

HB.structure Definition SplitSurj aT rT A B :=
  {f of @Surject aT rT A B f & @Inv _ _ f}.

HB.structure Definition SplitSurjFun aT rT A B :=
   {f of @SplitSurj aT rT A B f & @Fun _ _ A B f}.

HB.mixin Record OInv_Can aT rT (A : set aT) (f : aT -> rT) of OInv _ _ f :=
  { funoK : {in A, pcancel f 'oinv_f} }.

HB.structure Definition Inject aT rT A :=
  {f of OInv aT rT f & OInv_Can aT rT A f}.

HB.structure Definition SplitInj aT rT (A : set aT) :=
  {f of @Inv aT rT f & @Inject aT rT A f}.

HB.structure Definition SplitInjFun aT rT (A : set aT) (B : set rT) :=
  {f of @SplitInj _ rT A f & @isFun _ _ A B f}.

HB.factory Record Inv_Can {aT rT} {A : set aT} (f : aT -> rT) of Inv _ _ f :=
  { funK : {in A, cancel f f^-1} }.
HB.builders Context {aT rT} A (f : aT -> rT) of @Inv_Can _ _ A f.
  Local Lemma funoK: {in A, pcancel f 'oinv_f}.
Admitted.
  HB.instance Definition _ := OInv_Can.Build _ _ A f funoK.
HB.end.

HB.factory Record Inv_CanV {aT rT} {A : set aT} {B : set rT} (f : aT -> rT)
     of Inv aT rT f := {
  invS : {homo f^-1 : x / B x >-> A x};
  invK : {in B, cancel f^-1 f};
}.
HB.builders Context {aT rT} {A : set aT} {B : set rT} (f : aT -> rT)
    of Inv_CanV _ _ A B f.
  #[local] Lemma oinvK : {in B, ocancel 'oinv_f f}.
Admitted.
  #[local] Lemma oinvS : {homo 'oinv_f : x / B x >-> (some @` A) x}.
Admitted.
  HB.instance Definition _ := OInv_CanV.Build _ _ _ _ f oinvS oinvK.
HB.end.

HB.factory Record CanV {aT rT} {A : set aT} {B : set rT} (f : aT -> rT) :=
  { inv; invS : {homo inv : x / B x >-> A x}; invK : {in B, cancel inv f}; }.
HB.builders Context {aT rT} {A : set aT} {B : set rT} (f : aT -> rT) of CanV _ _ A B f.
 HB.instance Definition _ := Inv.Build _ _ f inv.
HB.end.

HB.factory Record OInv_Can2 {aT rT} {A : set aT} {B : set rT} (f : aT -> rT) of
  @OInv _ _ f :=
  {
    funS :  {homo f : x / A x >-> B x};
    oinvS : {homo 'oinv_f : x / B x >-> (some @` A) x};
    funoK : {in A, pcancel f 'oinv_f};
    oinvK : {in B, ocancel 'oinv_f f};
  }.
HB.builders Context {aT rT} A B (f : aT -> rT) of OInv_Can2 _ _ A B f.
  HB.instance Definition _ := isFun.Build aT rT _ _ f funS.
HB.end.

HB.factory Record OCan2 {aT rT} {A : set aT} {B : set rT} (f : aT -> rT) :=
   { oinv; funS :  {homo f : x / A x >-> B x};
           oinvS : {homo oinv : x / B x >-> (some @` A) x};
           funoK : {in A, pcancel f oinv};
           oinvK : {in B, ocancel oinv f};
   }.
HB.builders Context {aT rT} A B (f : aT -> rT) of OCan2 _ _ A B f.
  HB.instance Definition _ := OInv.Build aT rT f oinv.
HB.end.

HB.factory Record Can {aT rT} {A : set aT} (f : aT -> rT) :=
  { inv; funK : {in A, cancel f inv} }.
HB.builders Context {aT rT} A (f : aT -> rT) of @Can _ _ A f.

 HB.instance Definition _ := Inv.Build _ _ f inv.
HB.end.

HB.factory Record Inv_Can2 {aT rT} {A : set aT} {B : set rT} (f : aT -> rT) of
   Inv _ _ f :=
   { funS : {homo f : x / A x >-> B x};
     invS : {homo f^-1 : x / B x >-> A x};
     funK : {in A, cancel f f^-1};
     invK : {in B, cancel f^-1 f};
   }.
HB.builders Context {aT rT} A B (f : aT -> rT) of Inv_Can2 _ _ A B f.
  HB.instance Definition _ := isFun.Build aT rT A B f funS.
HB.end.

HB.factory Record Can2 {aT rT} {A : set aT} {B : set rT} (f : aT -> rT) :=
  { inv; funS : {homo f : x / A x >-> B x};
         invS : {homo inv : x / B x >-> A x};
         funK : {in A, cancel f inv};
         invK : {in B, cancel inv f};
   }.
HB.builders Context {aT rT} A B (f : aT -> rT) of Can2 _ _ A B f.
  HB.instance Definition _ := Inv.Build aT rT f inv.
HB.end.

HB.factory Record SplitInjFun_CanV {aT rT} {A : set aT} {B : set rT} (f : aT -> rT) of
     @SplitInjFun _ _ A B f :=
  { invS : {homo f^-1 : x / B x >-> A x}; injV : {in B &, injective f^-1} }.
HB.builders Context {aT rT} {A : set aT} {B : set rT} (f : aT -> rT) of SplitInjFun_CanV _ _ A B f.
  Local Lemma invK : {in B, cancel f^-1 f}.
Admitted.
  HB.instance Definition _ := Inv_CanV.Build aT rT A B f invS invK.
HB.end.

HB.factory Record BijTT {aT rT} (f : aT -> rT) := { bij : bijective f }.
HB.builders Context {aT rT} f of BijTT aT rT f.
  Local Lemma exg : {g | cancel f g /\ cancel g f}.
Admitted.
  HB.instance Definition _ := Can2.Build aT rT setT setT f
    (fun x y => y) (fun x y => y)
    (in1W (projT2 exg).1) (in1W (projT2 exg).2).
HB.end.

Section surj_oinv.
Context {aT rT} {A : set aT} {B : set rT} {f : aT -> rT} (fsurj : set_surj A B f).

Let surjective_oinv (y : rT) :=
  if pselect (B y) is left By then some (projT1 (cid2 (fsurj By))) else None.

Lemma surjective_oinvK : {in B, ocancel surjective_oinv f}.
Admitted.

Lemma surjective_oinvS : set_fun B (some @` A) surjective_oinv.
Admitted.
End surj_oinv.
Coercion surjective_ocanV {aT rT} {A : set aT} {B : set rT} {f : aT -> rT}
    (fS : set_surj A B f) :=
  OCanV.Build aT rT A B f (surjective_oinvS fS) (surjective_oinvK fS).

Section funin_surj.
Context {aT rT : Type}.

Definition funin (A : set aT) (f : aT -> rT) := f.

Context {A : set aT} {B : set rT} (f : aT -> rT).

HB.instance Definition _ : OCanV _ _ A (f @` A) (funin A f) :=
   ((fun _ => id) : set_surj A (f @` A) f).

End funin_surj.
Notation "[ 'fun' f 'in' A ]" := (funin A f)
  (at level 0, f at next level,
   format "[ 'fun'  f  'in'  A ]") : function_scope.

HB.factory Record Inj {aT rT} (A : set aT) (f : aT -> rT) :=
   { inj : {in A &, injective f} }.
HB.builders Context {aT rT} A (f : aT -> rT) of Inj _ _ A f.
  HB.instance Definition _ := OInversible.copy f [fun f in A].
HB.end.

HB.factory Record SurjFun_Inj {aT rT} {A : set aT} {B : set rT} (f : aT -> rT) of
   @SurjFun _ _ A B f := { inj : {in A &, injective f} }.
HB.builders Context {aT rT} {A : set aT} {B : set rT} (f : aT -> rT) of
    @SurjFun_Inj _ _ A B f.
  Let fcan : OInv_Can aT rT A f.
Admitted.
 HB.instance Definition _ := fcan.
HB.end.

HB.factory Record SplitSurjFun_Inj {aT rT} {A : set aT} {B : set rT} (f : aT -> rT) of
     @SplitSurjFun _ _ A B f :=
   { inj : {in A &, injective f} }.
HB.builders Context {aT rT} {A : set aT} {B : set rT} (f : aT -> rT) of
    @SplitSurjFun_Inj _ _ A B f.
  Local Lemma funK : {in A, cancel f f^-1%FUN}.
Admitted.
  HB.instance Definition _ := Inv_Can.Build aT rT _ f funK.
HB.end.

Section function_space.
Definition cst {T T' : Type} (x : T') : T -> T'.
Admitted.

Program Definition fct_zmodMixin (T : Type) (M : zmodType) :=
  @ZmodMixin (T -> M) \0 (fun f x => - f x) (fun f g => f \+ g) _ _ _ _.
Admit Obligations.
Canonical fct_zmodType T (M : zmodType) := ZmodType (T -> M) (fct_zmodMixin T M).

Program Definition fct_ringMixin (T : pointedType) (M : ringType) :=
  @RingMixin [zmodType of T -> M] (cst 1) (fun f g => f \* g)
             _ _ _ _ _ _.
Admit Obligations.
Canonical fct_ringType (T : pointedType) (M : ringType) :=
  RingType (T -> M) (fct_ringMixin T M).

End function_space.

Module Export topology.
Reserved Notation "'\forall' x '\near' x_0 , P"
  (at level 200, x name, P at level 200,
   format "'\forall'  x  '\near'  x_0 ,  P").
Reserved Notation "x \is_near F" (at level 10, format "x  \is_near  F").

Module Export Filtered.

Definition nbhs_of U T := T -> set (set U).
Record class_of U T := Class {
  base : Pointed.class_of T;
  nbhs_op : nbhs_of U T
}.

Section ClassDef.
Variable U : Type.

Structure type := Pack { sort; _ : class_of U sort }.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c := cT return class_of U cT in c.

Definition clone c of phant_id class c := @Pack T c.

Definition pack m :=
  fun bT b of phant_id (Pointed.class bT) b => @Pack T (Class b m).

End ClassDef.

Structure source Z Y := Source {
  source_type :> Type;
  _ : (source_type -> Z) -> set (set Y)
}.
Definition source_filter Z Y (F : source Z Y) : (F -> Z) -> set (set Y).
exact (let: Source X f := F in f).
Defined.

Module Export Exports.
Coercion sort : type >-> Sortclass.
Coercion base : class_of >-> Pointed.class_of.
Coercion nbhs_op : class_of >-> nbhs_of.
Notation filteredType := type.
Notation FilteredType U T m := (@pack U T m _ _ idfun).
Notation "[ 'filteredType' U 'of' T 'for' cT ]" :=  (@clone U T cT _ idfun)
  (at level 0, format "[ 'filteredType'  U  'of'  T  'for'  cT ]") : form_scope.

Canonical default_arrow_filter Y (Z : pointedType) (X : source Z Y) :=
  FilteredType Y (X -> Z) (@source_filter _ _ X).
Canonical source_filter_filter Y :=
  @Source Prop _ (_ -> Prop) (fun x : (set (set Y)) => x).

End Exports.
End Filtered.
Definition nbhs {U} {T : filteredType U} : T -> set (set U).
exact (Filtered.nbhs_op (Filtered.class T)).
Defined.
Definition filter_from {I T : Type} (D : set I) (B : I -> set T) : set (set T).
Admitted.

Section Near.

Local Notation "{ 'all1' P }" := (forall x, P x : Prop) (at level 0).
Local Notation ph := (phantom _).

Definition prop_near1 {X} {fX : filteredType X} (x : fX)
   P (phP : ph {all1 P}) := nbhs x P.

End Near.

Notation "{ 'near' x , P }" := (@prop_near1 _ _ x _ (inPhantom P)) : type_scope.
Notation "'\forall' x '\near' x_0 , P" := {near x_0, forall x, P} : type_scope.

Definition filter_of X (fX : filteredType X) (x : fX) of phantom fX x :=
   nbhs x.
Notation "[ 'filter' 'of' x ]" :=
  (@filter_of _ _ _ (Phantom _ x)) : classical_set_scope.

Class Filter {T : Type} (F : set (set T)) := {
  filterT : F setT ;
  filterI : forall P Q : set T, F P -> F Q -> F (P `&` Q) ;
  filterS : forall P Q : set T, P `<=` Q -> F P -> F Q
}.

Class ProperFilter' {T : Type} (F : set (set T)) := {
  filter_not_empty : not (F (fun _ => False)) ;
  filter_filter' : Filter F
}.

Notation ProperFilter := ProperFilter'.

Lemma filter_setT (T' : Type) : Filter [set: set T'].
Admitted.

Structure filter_on T := FilterType {
  filter :> (T -> Prop) -> Prop;
  _ : Filter filter
}.
Definition filter_class T (F : filter_on T) : Filter F.
Admitted.
Arguments FilterType {T} _ _.
#[global] Existing Instance filter_class.

Canonical filter_on_eqType T := EqType (filter_on T) gen_eqMixin.
Canonical filter_on_choiceType T :=
  ChoiceType (filter_on T) gen_choiceMixin.
Canonical filter_on_PointedType T :=
  PointedType (filter_on T) (FilterType _ (filter_setT T)).
Canonical filter_on_FilteredType T :=
  FilteredType T (filter_on T) (@filter T).

Record in_filter T (F : set (set T)) := InFilter {
  prop_in_filter_proj : T -> Prop;
  prop_in_filterP_proj : F prop_in_filter_proj
}.

Module Type PropInFilterSig.
Axiom t : forall (T : Type) (F : set (set T)), in_filter F -> T -> Prop.
End PropInFilterSig.
Module PropInFilter : PropInFilterSig.
Definition t := prop_in_filter_proj.
End PropInFilter.

Notation prop_of := PropInFilter.t.
Notation "x \is_near F" := (@PropInFilter.t _ F _ x).
Definition in_filterT T F (FF : Filter F) : @in_filter T F.
Admitted.
Canonical in_filterI T F (FF : Filter F) (P Q : @in_filter T F) :=
  InFilter (filterI (prop_in_filterP_proj P) (prop_in_filterP_proj Q)).

Lemma filter_near_of T F (P : @in_filter T F) (Q : set T) : Filter F ->
  (forall x, prop_of P x -> Q x) -> F Q.
Admitted.

Fact near_key : unit.
Admitted.

Lemma mark_near (P : Prop) : locked_with near_key P -> P.
Admitted.

Lemma near_acc T F (P : @in_filter T F) (Q : set T) (FF : Filter F)
   (FQ : \forall x \near F, Q x) :
   locked_with near_key (forall x, prop_of (in_filterI FF P (InFilter FQ)) x -> Q x).
Admitted.

Lemma near_skip_subproof T F (P Q : @in_filter T F) (G : set T) (FF : Filter F) :
   locked_with near_key (forall x, prop_of P x -> G x) ->
   locked_with near_key (forall x, prop_of (in_filterI FF P Q) x -> G x).
Admitted.

Tactic Notation "near=>" ident(x) := apply: filter_near_of => x ?.

Ltac just_discharge_near x :=
  tryif match goal with Hx : x \is_near _ |- _ => move: (x) (Hx); apply: mark_near end
        then idtac else fail "the variable" x "is not a ""near"" variable".
Ltac near_skip :=
  match goal with |- locked_with near_key (forall _, @PropInFilter.t _ _ ?P _ -> _) =>
    tryif is_evar P then fail "nothing to skip" else apply: near_skip_subproof end.

Tactic Notation "near:" ident(x) :=
  just_discharge_near x;
  tryif do ![apply: near_acc; first shelve|near_skip]
  then idtac
  else fail "the goal depends on variables introduced after" x.

Ltac end_near := do ?exact: in_filterT.

Module Export Topological.

Record mixin_of (T : Type) (nbhs : T -> set (set T)) := Mixin {
  open : set (set T) ;
  nbhs_pfilter : forall p : T, ProperFilter (nbhs p) ;
  nbhsE : forall p : T, nbhs p =
    [set A : set T | exists B : set T, [/\ open B, B p & B `<=` A] ] ;
  openE : open = [set A : set T | A `<=` nbhs^~ A ]
}.

Record class_of (T : Type) := Class {
  base : Filtered.class_of T T;
  mixin : mixin_of (Filtered.nbhs_op base)
}.

Section ClassDef.

Structure type := Pack { sort; _ : class_of sort }.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c := cT return class_of cT in c.

Definition pack nbhs' (m : @mixin_of T nbhs') :=
  fun bT (b : Filtered.class_of T T) of phant_id (@Filtered.class T bT) b =>
  fun m'   of phant_id m (m' : @mixin_of T (Filtered.nbhs_op b)) =>
  @Pack T (@Class _ b m').

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> Filtered.class_of.
Coercion mixin : class_of >-> mixin_of.
Notation topologicalType := type.
Notation TopologicalType T m := (@pack T _ m _ _ idfun _ idfun).

End Exports.

End Topological.

Section TopologyOfFilter.

Context {T : Type} {nbhs' : T -> set (set T)}.
Hypothesis (nbhs'_filter : forall p : T, ProperFilter (nbhs' p)).
Hypothesis (nbhs'_singleton : forall (p : T) (A : set T), nbhs' p A -> A p).
Hypothesis (nbhs'_nbhs' : forall (p : T) (A : set T), nbhs' p A -> nbhs' p (nbhs'^~ A)).

Definition open_of_nbhs := [set A : set T | A `<=` nbhs'^~ A].

Program Definition topologyOfFilterMixin : Topological.mixin_of nbhs' :=
  @Topological.Mixin T nbhs' open_of_nbhs _ _ _.
Admit Obligations.

End TopologyOfFilter.

Local Notation "A ^-1" := ([set xy | A (xy.2, xy.1)]) : classical_set_scope.

Local Notation "'to_set' A x" := ([set y | A (x, y)])
  (at level 0, A at level 0) : classical_set_scope.

Definition nbhs_ {T T'} (ent : set (set (T * T'))) (x : T) :=
  filter_from ent (fun A => to_set A x).

Module Export Uniform.

Record mixin_of (M : Type) (nbhs : M -> set (set M)) := Mixin {
  entourage : (M * M -> Prop) -> Prop ;
  entourage_filter : Filter entourage ;
  entourage_refl : forall A, entourage A -> [set xy | xy.1 = xy.2] `<=` A ;
  entourage_inv : forall A, entourage A -> entourage (A^-1)%classic ;
  entourage_split_ex :
    forall A, entourage A -> exists2 B, entourage B & B \; B `<=` A ;
  nbhsE : nbhs = nbhs_ entourage
}.

Record class_of (M : Type) := Class {
  base : Topological.class_of M;
  mixin : mixin_of (Filtered.nbhs_op base)
}.

Section ClassDef.

Structure type := Pack { sort; _ : class_of sort }.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c := cT return class_of cT in c.

Definition pack nbhs (m : @mixin_of T nbhs) :=
  fun bT (b : Topological.class_of T) of phant_id (@Topological.class bT) b =>
  fun m'   of phant_id m (m' : @mixin_of T (Filtered.nbhs_op b)) =>
  @Pack T (@Class _ b m').

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> Topological.class_of.
Coercion mixin : class_of >-> mixin_of.
Notation uniformType := type.
Notation UniformType T m := (@pack T _ m _ _ idfun _ idfun).
Notation UniformMixin := Mixin.

End Exports.

End Uniform.

Section UniformTopology.

Program Definition topologyOfEntourageMixin (T : Type)
  (nbhs : T -> set (set T)) (m : Uniform.mixin_of nbhs) :
  Topological.mixin_of nbhs := topologyOfFilterMixin _ _ _.
Admit Obligations.

End UniformTopology.

Definition entourage_ {R : numDomainType} {T T'} (ball : T -> R -> set T') :=
  @filter_from R _ [set x | 0 < x] (fun e => [set xy | ball xy.1 e xy.2]).

Module Export PseudoMetric.

Record mixin_of (R : numDomainType) (M : Type)
    (entourage : set (set (M * M))) := Mixin {
  ball : M -> R -> M -> Prop ;
  ball_center : forall x (e : R), 0 < e -> ball x e x ;
  ball_sym : forall x y (e : R), ball x e y -> ball y e x ;
  ball_triangle :
    forall x y z e1 e2, ball x e1 y -> ball y e2 z -> ball x (e1 + e2) z;
  entourageE : entourage = entourage_ ball
}.

Record class_of (R : numDomainType) (M : Type) := Class {
  base : Uniform.class_of M;
  mixin : mixin_of R (Uniform.entourage base)
}.

Section ClassDef.
Variable R : numDomainType.
Structure type := Pack { sort; _ : class_of R sort }.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c := cT return class_of R cT in c.

Definition clone c of phant_id class c := @Pack T c.

Definition pack ent (m : @mixin_of R T ent) :=
  fun bT (b : Uniform.class_of T) of phant_id (@Uniform.class bT) b =>
  fun m'   of phant_id m (m' : @mixin_of R T (Uniform.entourage b)) =>
  @Pack T (@Class R _ b m').

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> Uniform.class_of.
Coercion mixin : class_of >-> mixin_of.
Notation pseudoMetricType := type.
Notation PseudoMetricType T m := (@pack _ T _ m _ _ idfun _ idfun).
Notation PseudoMetricMixin := Mixin.
Notation "[ 'pseudoMetricType' R 'of' T 'for' cT ]" := (@clone R T cT _ idfun)
  (at level 0, format "[ 'pseudoMetricType'  R  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'pseudoMetricType' R 'of' T ]" := (@clone R T _ _ id)
  (at level 0, format "[ 'pseudoMetricType'  R  'of'  T ]") : form_scope.

End Exports.

End PseudoMetric.

Section PseudoMetricUniformity.

Program Definition uniformityOfBallMixin (R : numFieldType) (T : Type)
  (ent : set (set (T * T))) (nbhs : T -> set (set T)) (nbhsE : nbhs = nbhs_ ent)
  (m : PseudoMetric.mixin_of R ent) : Uniform.mixin_of nbhs :=
  UniformMixin _ _ _ _ nbhsE.
Admit Obligations.

End PseudoMetricUniformity.

Definition ball {R : numDomainType} {M : pseudoMetricType R} :=
  PseudoMetric.ball (PseudoMetric.class M).

Definition nbhs_ball_ {R : numDomainType} {T T'} (ball : T -> R -> set T')
  (x : T) := @filter_from R _ [set e | e > 0] (ball x).

Definition pointed_of_zmodule (R : zmodType) : pointedType.
exact (PointedType R 0).
Defined.

Definition ball_
  (R : numDomainType) (V : zmodType) (norm : V -> R) (x : V) (e : R) :=
  [set y | norm (x - y) < e].
Definition filtered_of_normedZmod (K : numDomainType) (R : normedZmodType K)
  : filteredType R.
exact (Filtered.Pack (Filtered.Class
    (@Pointed.class (pointed_of_zmodule R))
    (nbhs_ball_ (ball_ (fun x => `|x|))))).
Defined.

Section pseudoMetric_of_normedDomain.
Variables (K : numDomainType) (R : normedZmodType K).
Lemma ball_norm_center (x : R) (e : K) : 0 < e -> ball_ Num.norm x e x.
Admitted.
Lemma ball_norm_symmetric (x y : R) (e : K) :
  ball_ Num.norm x e y -> ball_ Num.norm y e x.
Admitted.
Lemma ball_norm_triangle (x y z : R) (e1 e2 : K) :
  ball_ Num.norm x e1 y -> ball_ Num.norm y e2 z -> ball_ Num.norm x (e1 + e2) z.
Admitted.
Definition pseudoMetric_of_normedDomain
  : PseudoMetric.mixin_of K (@entourage_ K R R (ball_ (fun x => `|x|))).
exact (PseudoMetricMixin ball_norm_center ball_norm_symmetric ball_norm_triangle erefl).
Defined.
Lemma nbhs_ball_normE :
  @nbhs_ball_ K R R (ball_ Num.norm) = nbhs_ (entourage_ (ball_ Num.norm)).
Admitted.
End pseudoMetric_of_normedDomain.

Module Export regular_topology.

Section regular_topology.
Local Canonical filteredType (R : numDomainType) : filteredType R.
exact ([filteredType R of R^o for filtered_of_normedZmod R]).
Defined.
Local Canonical topologicalType (R : numFieldType) : topologicalType.
exact (TopologicalType R^o (topologyOfEntourageMixin (uniformityOfBallMixin
      (@nbhs_ball_normE _ _) (pseudoMetric_of_normedDomain _)))).
Defined.
Local Canonical uniformType (R : numFieldType) : uniformType.
exact (UniformType R^o (uniformityOfBallMixin
                     (@nbhs_ball_normE _ _) (pseudoMetric_of_normedDomain _))).
Defined.
Local Canonical pseudoMetricType (R : numFieldType) :=
  PseudoMetricType R^o (@pseudoMetric_of_normedDomain R R).
End regular_topology.

Module Export Exports.
Canonical pseudoMetricType.
End Exports.

End regular_topology.

Module Export numFieldTopology.

Section numFieldType.
Variable (R : numFieldType).
Local Canonical numField_pseudoMetricType :=
  [pseudoMetricType R of R for [pseudoMetricType R of R^o]].
End numFieldType.

Module Export Exports.
Coercion numField_pseudoMetricType : numFieldType >-> pseudoMetricType.
End Exports.

End numFieldTopology.

End topology.

Module Export PseudoMetricNormedZmodule.
Section ClassDef.
Variable R : numDomainType.
Record mixin_of (T : normedZmodType R) (ent : set (set (T * T)))
    (m : PseudoMetric.mixin_of R ent) := Mixin {
  _ : PseudoMetric.ball m = ball_ (fun x => `| x |) }.

Record class_of (T : Type) := Class {
  base : Num.NormedZmodule.class_of R T;
  pointed_mixin : Pointed.point_of T ;
  nbhs_mixin : Filtered.nbhs_of T T ;
  topological_mixin : @Topological.mixin_of T nbhs_mixin ;
  uniform_mixin : @Uniform.mixin_of T nbhs_mixin ;
  pseudoMetric_mixin :
    @PseudoMetric.mixin_of R T (Uniform.entourage uniform_mixin) ;
  mixin : @mixin_of (Num.NormedZmodule.Pack _ base) _ pseudoMetric_mixin
}.
Local Coercion base : class_of >-> Num.NormedZmodule.class_of.

Structure type (phR : phant R) :=
  Pack { sort; _ : class_of sort }.
Local Coercion sort : type >-> Sortclass.

Variables (phR : phant R) (T : Type) (cT : type phR).

Definition class := let: Pack _ c := cT return class_of cT in c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).
Definition pack (b0 : Num.NormedZmodule.class_of R T) lm0 um0
  (m0 : @mixin_of (@Num.NormedZmodule.Pack R (Phant R) T b0) lm0 um0) :=
  fun bT (b : Num.NormedZmodule.class_of R T)
      & phant_id (@Num.NormedZmodule.class R (Phant R) bT) b =>
  fun uT (u : PseudoMetric.class_of R T) & phant_id (@PseudoMetric.class R uT) u =>
  fun (m : @mixin_of (Num.NormedZmodule.Pack _ b) _ u) & phant_id m m0 =>
  @Pack phR T (@Class T b u u u u u m).
Definition zmodType := @GRing.Zmodule.Pack cT xclass.
Definition normedZmodType := @Num.NormedZmodule.Pack R phR cT xclass.

End ClassDef.

Module Export Exports.
Coercion base : class_of >-> Num.NormedZmodule.class_of.
Coercion sort : type >-> Sortclass.
Canonical zmodType.
Canonical normedZmodType.
Notation pseudoMetricNormedZmodType R := (type (Phant R)).
Notation PseudoMetricNormedZmodType R T m :=
  (@pack _ (Phant R) T _ _ _ m _ _ idfun _ _ idfun _ idfun).
End Exports.

End PseudoMetricNormedZmodule.

Record mixin_of (K : numDomainType)
  (V : pseudoMetricNormedZmodType K) (scale : K -> V -> V) := Mixin {
  _ : forall (l : K) (x : V), `| scale l x | = `| l | * `| x |;
}.

Section ClassDef.

Variable K : numDomainType.

Record class_of (T : Type) := Class {
  base : PseudoMetricNormedZmodule.class_of K T ;
  lmodmixin : GRing.Lmodule.mixin_of K (GRing.Zmodule.Pack base) ;
  mixin : @mixin_of K (PseudoMetricNormedZmodule.Pack (Phant K) base)
                      (GRing.Lmodule.scale lmodmixin)
}.
Local Coercion base : class_of >-> PseudoMetricNormedZmodule.class_of.

Structure type (phK : phant K) :=
  Pack { sort; _ : class_of sort }.
Local Coercion sort : type >-> Sortclass.

Variables (phK : phant K) (T : Type) (cT : type phK).

Definition class := let: Pack _ c := cT return class_of cT in c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack b0 l0
                (m0 : @mixin_of K (@PseudoMetricNormedZmodule.Pack K (Phant K) T b0)
                                (GRing.Lmodule.scale l0)) :=
  fun bT b & phant_id (@PseudoMetricNormedZmodule.class K (Phant K) bT) b =>
  fun l & phant_id l0 l =>
  fun m & phant_id m0 m => Pack phK (@Class T b l m).
Definition zmodType := @GRing.Zmodule.Pack cT xclass.
Definition normedZmodType := @Num.NormedZmodule.Pack K phK cT xclass.
End ClassDef.
Coercion sort : type >-> Sortclass.
Canonical zmodType.
Canonical normedZmodType.
Notation normedModType K := (type (Phant K)).
Notation NormedModType K T m := (@pack _ (Phant K) T _ _ m _ _ idfun _ idfun _ idfun).
Notation NormedModMixin := Mixin.

Module Export regular_topology.

Section regular_topology.
Local Canonical pseudoMetricNormedZmodType (R : numFieldType) :=
  @PseudoMetricNormedZmodType
    R R^o
    (PseudoMetricNormedZmodule.Mixin (erefl : @ball _ R = ball_ Num.norm)).
Local Canonical normedModType (R : numFieldType) :=
  NormedModType R R^o (@NormedModMixin _ _ ( *:%R : R -> R^o -> _) (@normrM _)).
End regular_topology.

Module Export Exports.
Canonical normedModType.
End Exports.

End regular_topology.
Import GRing.Theory.

Reserved Notation "{o_ F f }" (at level 0, F at level 0, format "{o_ F  f }").

Reserved Notation "[o_ x e 'of' f ]" (at level 0, x, e at level 0, only parsing).
Reserved Notation "f '=o_' F h"
  (at level 70, no associativity,
   F at level 0, h at next level,
   format "f  '=o_' F  h").
Definition the_tag : unit.
Admitted.
Definition gen_tag : unit.
Admitted.

Section Domination.
Context {K : numDomainType} {T : Type} {V W : normedModType K}.

Let littleo_def (F : set (set T)) (f : T -> V) (g : T -> W) :=
  forall eps, 0 < eps -> \forall x \near F, `|f x| <= eps * `|g x|.

Structure littleo_type (F : set (set T)) (g : T -> W) := Littleo {
  littleo_fun :> T -> V;
  _ : `[< littleo_def F littleo_fun g >]
}.
Notation "{o_ F f }" := (littleo_type F f).

Canonical littleo_subtype (F : set (set T)) (g : T -> W) :=
  [subType for (@littleo_fun F g)].

Lemma littleo_class (F : set (set T)) (g : T -> W) (f : {o_F g}) :
  `[< littleo_def F f g >].
Admitted.

Definition littleo_clone (F : set (set T)) (g : T -> W) (f : T -> V) (fT : {o_F g}) c
  of phant_id (littleo_class fT) c := @Littleo F g f c.
Notation "[littleo 'of' f ]" := (@littleo_clone _ _ f _ _ idfun).

Lemma littleo0_subproof F (g : T -> W) :
  Filter F -> littleo_def F (0 : T -> V) g.
Admitted.

Canonical littleo0 (F : filter_on T) g :=
  Littleo (asboolT (@littleo0_subproof F g _)).

Definition the_littleo (_ : unit) (F : filter_on T)
  (phF : phantom (set (set T)) F) f h := littleo_fun (insubd (littleo0 F h) f).
Arguments the_littleo : simpl never, clear implicits.

Lemma littleoE (tag : unit) (F : filter_on T)
   (phF : phantom (set (set T)) F) f h :
   littleo_def F f h -> the_littleo tag F phF f h = f.
Admitted.

Canonical the_littleo_littleo (tag : unit) (F : filter_on T)
  (phF : phantom (set (set T)) F) f h := [littleo of the_littleo tag F phF f h].

Variant littleo_spec (F : set (set T)) (g : T -> W) : (T -> V) -> Type :=
  LittleoSpec f of littleo_def F f g : littleo_spec F g f.

Lemma littleo (F : set (set T)) (g : T -> W) (f : {o_F g}) : littleo_spec F g f.
Admitted.

End Domination.

Arguments the_littleo {_ _ _ _} _ _ _ _ _ : simpl never.
Local Notation PhantomF x := (Phantom _ [filter of x]).

Notation mklittleo tag x := (the_littleo tag _ (PhantomF x)).

Notation "[o_ x e 'of' f ]" := (mklittleo gen_tag x f e).
Notation "f '=o_' F h" := (f%function = (mklittleo the_tag F f h)).

Variables (R : rcfType) (pT : pointedType).

Lemma mulo (F : filter_on pT) (h1 h2 f g : pT -> R^o) :
  [o_F h1 of f] * [o_F h2 of g] =o_F (h1 * h2).
Proof.
rewrite [in RHS]littleoE // => _/posnumP[e]; near=> x.
rewrite [`|_|]normrM -(sqr_sqrtr (ge0 e)) expr2.
rewrite (@normrM _ (h1 x) (h2 x)) mulrACA ler_pmul //; near: x;
by have [/= h] := littleo; apply.
Unshelve.
all: by end_near.
Qed.
