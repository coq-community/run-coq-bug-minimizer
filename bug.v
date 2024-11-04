
(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "-parsing" "-w" "+undeclared-scope" "-w" "+non-primitive-record" "-w" "-ambiguous-paths" "-w" "-redundant-canonical-projection" "-w" "-projection-no-head-constant" "-w" "-deprecated-native-compiler-option" "-native-compiler" "ondemand" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/analysis/classical" "mathcomp.classical" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/analysis/reals" "mathcomp.reals" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/analysis/reals_stdlib" "mathcomp.reals_stdlib" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/analysis/altreals" "mathcomp.altreals" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/analysis/theories" "mathcomp.analysis" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/analysis/analysis_stdlib" "mathcomp.analysis_stdlib" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/HB" "HB" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/elpi" "elpi" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/elpi_elpi" "elpi_elpi" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/elpi_examples" "elpi_examples" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/mathcomp" "mathcomp" "-top" "mathcomp.analysis.topology_theory.weak_topology") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 228 lines to 53 lines, then from 66 lines to 391 lines, then from 396 lines to 88 lines, then from 101 lines to 1093 lines, then from 1098 lines to 222 lines, then from 235 lines to 338 lines, then from 343 lines to 235 lines, then from 248 lines to 1960 lines, then from 1965 lines to 819 lines *)
(* coqc version 9.0+alpha compiled with OCaml 4.14.1
   coqtop version runner-cabngxqim-project-4504-concurrent-1:/builds/coq/coq/_build/default,(HEAD detached at a02978623a9293) (a02978623a9293b816f014cc609ae0f92aed5d57)
   Expected coqc runtime on this file: 8.406 sec *)








Require Stdlib.Init.Ltac.
Require Stdlib.Bool.Bool.
Require Stdlib.Floats.PrimFloat.
Require Stdlib.NArith.BinNat.
Require Stdlib.NArith.Ndec.
Require Stdlib.Numbers.Cyclic.Int63.PrimInt63.
Require Stdlib.PArith.BinPos.
Require Stdlib.Strings.PrimString.
Require Stdlib.Strings.String.
Require Stdlib.setoid_ring.Field_tac.
Require Stdlib.setoid_ring.Field_theory.
Require Stdlib.setoid_ring.Ring.
Require Stdlib.ssr.ssrbool.
Require Stdlib.ssr.ssreflect.
Require Stdlib.ssr.ssrfun.
Require mathcomp.ssreflect.ssrnotations.
Require elpi_elpi.dummy.
Require mathcomp.ssreflect.ssreflect.
Require mathcomp.ssreflect.ssrfun.
Require mathcomp.ssreflect.ssrbool.
Require elpi.elpi.
Require elpi.apps.locker.locker.
Require HB.structures.
Require mathcomp.ssreflect.eqtype.
Require mathcomp.ssreflect.ssrnat.
Require mathcomp.ssreflect.seq.
Require mathcomp.ssreflect.choice.
Require mathcomp.ssreflect.div.
Require mathcomp.ssreflect.path.
Require mathcomp.ssreflect.fintype.
Require mathcomp.ssreflect.fingraph.
Require mathcomp.ssreflect.generic_quotient.
Require mathcomp.ssreflect.tuple.
Require mathcomp.ssreflect.finfun.
Require mathcomp.ssreflect.bigop.
Require mathcomp.ssreflect.finset.
Require mathcomp.ssreflect.prime.
Require mathcomp.ssreflect.ssrAC.
Require mathcomp.finmap.finmap.
Require mathcomp.fingroup.fingroup.
Require mathcomp.ssreflect.binomial.
Require mathcomp.ssreflect.order.
Require mathcomp.algebra.ssralg.
Require mathcomp.fingroup.morphism.
Require mathcomp.algebra.countalg.
Require mathcomp.algebra.poly.
Require mathcomp.algebra.ring_quotient.
Require mathcomp.fingroup.perm.
Require mathcomp.algebra.polydiv.
Require mathcomp.fingroup.automorphism.
Require mathcomp.fingroup.quotient.
Require mathcomp.ssreflect.all_ssreflect.
Require mathcomp.fingroup.action.
Require mathcomp.algebra.fraction.
Require mathcomp.algebra.ssrnum.
Require mathcomp.algebra.interval.
Require mathcomp.algebra.ssrint.
Require mathcomp.algebra.archimedean.
Require mathcomp.algebra.finalg.
Require mathcomp.algebra.zmodp.
Require mathcomp.algebra.matrix.
Require mathcomp.algebra.rat.
Require mathcomp.algebra.mxalgebra.
Require mathcomp.algebra.vector.
Require mathcomp.algebra.mxpoly.
Require mathcomp.algebra.polyXY.
Require mathcomp.algebra.qpoly.
Require mathcomp.classical.mathcomp_extra.
Require mathcomp.classical.boolp.
Require mathcomp.classical.contra.
Require mathcomp.classical.wochoice.
Require mathcomp.algebra.intdiv.
Require mathcomp.classical.classical_sets.
Require mathcomp.classical.functions.
Require mathcomp.algebra.all_algebra.
Require mathcomp.classical.cardinality.
Require mathcomp.classical.set_interval.
Require mathcomp.classical.fsbigop.

Module Export AdmitTactic.
Module Import LocalFalse.
Inductive False : Prop := .
End LocalFalse.
Axiom proof_admitted : False.
Import Coq.Init.Ltac.
Tactic Notation "admit" := abstract case proof_admitted.
End AdmitTactic.

Module Export mathcomp_DOT_classical_DOT_filter_WRAPPED.
Module Export filter.

Import HB.structures.
Import mathcomp.ssreflect.all_ssreflect.
Import mathcomp.algebra.all_algebra.
Import mathcomp.finmap.finmap.
Import mathcomp.ssreflect.generic_quotient.
Import mathcomp.algebra.archimedean.
Import mathcomp.classical.boolp.
Import mathcomp.classical.classical_sets.
Import mathcomp.classical.functions.
Import mathcomp.classical.wochoice.
Import mathcomp.classical.cardinality.
Import mathcomp.classical.mathcomp_extra.
Import mathcomp.classical.fsbigop.
Import mathcomp.classical.set_interval.
































































































































































Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Obligation Tactic := idtac.
Import Order.TTheory.
Import GRing.Theory.
Import Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Reserved Notation "{ 'near' x , P }" (at level 0, format "{ 'near'  x ,  P }").
Reserved Notation "'\forall' x '\near' x_0 , P"
  (at level 200, x name, P at level 200,
   format "'\forall'  x  '\near'  x_0 ,  P").
Reserved Notation "'\near' x , P"
  (at level 200, x at level 99, P at level 200,
   format "'\near'  x ,  P", only parsing).
Reserved Notation "{ 'near' x & y , P }"
  (at level 0, format "{ 'near'  x  &  y ,  P }").
Reserved Notation "'\forall' x '\near' x_0 & y '\near' y_0 , P"
  (at level 200, x name, y name, P at level 200,
   format "'\forall'  x  '\near'  x_0  &  y  '\near'  y_0 ,  P").
Reserved Notation "'\forall' x & y '\near' z , P"
  (at level 200, x name, y name, P at level 200,
   format "'\forall'  x  &  y  '\near'  z ,  P").
Reserved Notation "'\near' x & y , P"
  (at level 200, x, y at level 99, P at level 200,
   format "'\near'  x  &  y ,  P", only parsing).

Reserved Notation "F `=>` G" (at level 70, format "F  `=>`  G").
Reserved Notation "F --> G" (at level 70, format "F  -->  G").
Reserved Notation "[ 'lim' F 'in' T ]" (format "[ 'lim'  F  'in'  T ]").
Reserved Notation "[ 'cvg' F 'in' T ]" (format "[ 'cvg'  F  'in'  T ]").
Reserved Notation "x \is_near F" (at level 10, format "x  \is_near  F").
Reserved Notation "E @[ x --> F ]"
  (at level 60, x name, format "E  @[ x  -->  F ]").
Reserved Notation "E @[ x \oo ]"
  (at level 60, x name, format "E  @[ x  \oo ]").
Reserved Notation "f @ F" (at level 60, format "f  @  F").
Reserved Notation "E `@[ x --> F ]"
  (at level 60, x name, format "E  `@[ x  -->  F ]").
Reserved Notation "f `@ F" (at level 60, format "f  `@  F").

Definition set_system U := set (set U).
Identity Coercion set_system_to_set : set_system >-> set.

HB.mixin Record isFiltered U T := {
  nbhs : T -> set_system U
}.

#[short(type="filteredType")]
HB.structure Definition Filtered (U : Type) := {T of Choice T & isFiltered U T}.
Arguments nbhs {_ _} _ _ : simpl never.

#[short(type="pfilteredType")]
HB.structure Definition PointedFiltered (U : Type) := {T of Pointed T & isFiltered U T}.

HB.instance Definition _ T := Equality.on (set_system T).
HB.instance Definition _ T := Choice.on (set_system T).
HB.instance Definition _ T := Pointed.on (set_system T).
HB.instance Definition _ T := isFiltered.Build T (set_system T) id.

HB.mixin Record selfFiltered T := {}.

HB.factory Record hasNbhs T := { nbhs : T -> set_system T }.
HB.builders Context T of hasNbhs T.
  HB.instance Definition _ := isFiltered.Build T T nbhs.
  HB.instance Definition _ := selfFiltered.Build T.
HB.end.

#[short(type="nbhsType")]
HB.structure Definition Nbhs := {T of Choice T & hasNbhs T}.

#[short(type="pnbhsType")]
HB.structure Definition PointedNbhs := {T of Pointed T & hasNbhs T}.
Definition filter_from {I T : Type} (D : set I) (B : I -> set T) :
  set_system T. exact ([set P | exists2 i, D i & B i `<=` P]). Defined.


HB.instance Definition _ m n X (Z : filteredType X) :=
  isFiltered.Build 'M[X]_(m, n) 'M[Z]_(m, n) (fun mx => filter_from
    [set P | forall i j, nbhs (mx i j) (P i j)]
    (fun P => [set my : 'M[X]_(m, n) | forall i j, P i j (my i j)])).

HB.instance Definition _ m n (X : nbhsType) := selfFiltered.Build 'M[X]_(m, n).
Definition filter_prod {T U : Type}
  (F : set_system T) (G : set_system U) : set_system (T * U). exact (filter_from (fun P => F P.1 /\ G P.2) (fun P => P.1 `*` P.2)). Defined.

Section Near.

Local Notation "{ 'all1' P }" := (forall x, P x : Prop) (at level 0).
Local Notation "{ 'all2' P }" := (forall x y, P x y : Prop) (at level 0).
Local Notation "{ 'all3' P }" := (forall x y z, P x y z: Prop) (at level 0).
Local Notation ph := (phantom _).

Definition prop_near1 {X} {fX : filteredType X} (x : fX)
   P (phP : ph {all1 P}) := nbhs x P.

Definition prop_near2 {X X'} {fX : filteredType X} {fX' : filteredType X'}
  (x : fX) (x' : fX') := fun P of ph {all2 P} =>
  filter_prod (nbhs x) (nbhs x') (fun x => P x.1 x.2).

End Near.

Notation "{ 'near' x , P }" := (@prop_near1 _ _ x _ (inPhantom P)) : type_scope.
Notation "'\forall' x '\near' x_0 , P" := {near x_0, forall x, P} : type_scope.
Notation "'\near' x , P" := (\forall x \near x, P) : type_scope.
Notation "{ 'near' x & y , P }" :=
  (@prop_near2 _ _ _ _ x y _ (inPhantom P)) : type_scope.
Notation "'\forall' x '\near' x_0 & y '\near' y_0 , P" :=
  {near x_0 & y_0, forall x y, P} : type_scope.
Notation "'\forall' x & y '\near' z , P" :=
  {near z & z, forall x y, P} : type_scope.
Notation "'\near' x & y , P" := (\forall x \near x & y \near y, P) : type_scope.
Arguments prop_near1 : simpl never.
Arguments prop_near2 : simpl never.

Lemma nearE {T} {F : set_system T} (P : set T) :
  (\forall x \near F, P x) = F P.
Admitted.

Lemma eq_near {T} {F : set_system T} (P Q : set T) :
  (forall x, P x <-> Q x) ->
  (\forall x \near F, P x) = (\forall x \near F, Q x).
Admitted.

Lemma nbhs_filterE {T : Type} (F : set_system T) : nbhs F = F.
Admitted.

Module Export NbhsFilter.
Definition nbhs_simpl := (@nbhs_filterE).
End NbhsFilter.

Definition cvg_to {T : Type} (F G : set_system T) := G `<=` F.
Notation "F `=>` G" := (cvg_to F G) : classical_set_scope.

Lemma cvg_refl T (F : set_system T) : F `=>` F.
Admitted.
Arguments cvg_refl {T F}.
#[global] Hint Resolve cvg_refl : core.

Lemma cvg_trans T (G F H : set_system T) :
  (F `=>` G) -> (G `=>` H) -> (F `=>` H).
Admitted.

Notation "F --> G" := (cvg_to (nbhs F) (nbhs G)) : classical_set_scope.
Definition type_of_filter {T} (F : set_system T) := T.

Definition lim_in {U : Type} (T : pfilteredType U) :=
  fun F : set_system U => get (fun l : T => F --> l).
Notation "[ 'lim' F 'in' T ]" := (@lim_in _ T (nbhs F)) : classical_set_scope.
Definition lim {T : pnbhsType} (F : set_system T) := [lim F in T].
Notation "[ 'cvg' F 'in' T ]" := (F --> [lim F in T]) : classical_set_scope.
Notation cvg F := (F --> lim F).


Definition eventually := filter_from setT (fun N => [set n | (N <= n)%N]).
Notation "'\oo'" := eventually : classical_set_scope.

Section FilteredTheory.

HB.instance Definition _ X1 X2 (Z1 : filteredType X1) (Z2 : filteredType X2) :=
  isFiltered.Build (X1 * X2)%type (Z1 * Z2)%type
    (fun x => filter_prod (nbhs x.1) (nbhs x.2)).

HB.instance Definition _ (X1 X2 : nbhsType)  :=
  selfFiltered.Build (X1 * X2)%type.

Lemma cvg_prod T {U U' V V' : filteredType T} (x : U) (l : U') (y : V) (k : V') :
  x --> l -> y --> k -> (x, y) --> (l, k).
Admitted.

Lemma cvg_in_ex {U : Type} (T : pfilteredType U) (F : set_system U) :
  [cvg F in T] <-> (exists l : T, F --> l).
Admitted.

Lemma cvg_ex (T : pnbhsType) (F : set_system T) :
  cvg F <-> (exists l : T, F --> l).
Admitted.

Lemma cvg_inP {U : Type} (T : pfilteredType U) (F : set_system U) (l : T) :
  F --> l -> [cvg F in T].
Admitted.

Lemma cvgP (T : pnbhsType) (F : set_system T) (l : T) : F --> l -> cvg F.
Admitted.

Lemma cvg_in_toP {U : Type} (T : pfilteredType U) (F : set_system U) (l : T) :
  [cvg F in T] -> [lim F in T] = l -> F --> l.
Admitted.

Lemma cvg_toP (T : pnbhsType) (F : set_system T) (l : T) :
  cvg F -> lim F = l -> F --> l.
Admitted.

Lemma dvg_inP {U : Type} (T : pfilteredType U) (F : set_system U) :
  ~ [cvg F in T] -> [lim F in T] = point.
Admitted.

Lemma dvgP (T : pnbhsType) (F : set_system T) : ~ cvg F -> lim F = point.
Admitted.

Lemma cvg_inNpoint {U} (T : pfilteredType U) (F : set_system U) :
  [lim F in T] != point -> [cvg F in T].
Admitted.

Lemma cvgNpoint (T : pnbhsType) (F : set_system T) : lim F != point -> cvg F.
Admitted.

End FilteredTheory.
Arguments cvg_inP {U T F} l.
Arguments dvg_inP {U} T {F}.
Arguments cvgP {T F} l.
Arguments dvgP {T F}.

Lemma nbhs_nearE {U} {T : filteredType U} (x : T) (P : set U) :
  nbhs x P = \near x, P x.
Admitted.

Lemma near_nbhs {U} {T : filteredType U} (x : T) (P : set U) :
  (\forall x \near nbhs x, P x) = \near x, P x.
Admitted.

Lemma near2_curry {U V} (F : set_system U) (G : set_system V) (P : U -> set V) :
  {near F & G, forall x y, P x y} = {near (F, G), forall x, P x.1 x.2}.
Admitted.

Lemma near2_pair {U V} (F : set_system U) (G : set_system V) (P : set (U * V)) :
  {near F & G, forall x y, P (x, y)} = {near (F, G), forall x, P x}.
Admitted.

Definition near2E := (@near2_curry, @near2_pair).

Lemma filter_of_nearI (X : Type) (fX : filteredType X)
  (x : fX) : forall P,
  nbhs x P = @prop_near1 X fX x P (inPhantom (forall x, P x)).
Admitted.



Class Filter {T : Type} (F : set_system T) := {
  filterT : F setT ;
  filterI : forall P Q : set T, F P -> F Q -> F (P `&` Q) ;
  filterS : forall P Q : set T, P `<=` Q -> F P -> F Q
}.
Global Hint Mode Filter - ! : typeclass_instances.

Class ProperFilter {T : Type} (F : set_system T) := {
  filter_not_empty : ~ F set0 ;
  filter_filter : Filter F
}.

Structure filter_on T := FilterType {
  filter :> set_system T;
  _ : Filter filter
}.
Definition filter_class T (F : filter_on T) : Filter F. exact (let: FilterType _ class := F in class). Defined.
Arguments FilterType {T} _ _.
#[global] Existing Instance filter_class.



Section frechet_filter.

End frechet_filter.

Section at_point.

End at_point.

















Section within.

End within.


Section NearSet.

End NearSet.

Section PrincipalFilters.

End PrincipalFilters.

Section UltraFilters.

End UltraFilters.

Section filter_supremums.

Definition finI_from (I : choiceType) T (D : set I) (f : I -> set T) :=
  [set \bigcap_(i in [set` D']) f i |
    D' in [set A : {fset I} | {subset A <= D}]].

End filter_supremums.

Module Export mathcomp_DOT_classical_DOT_all_classical_WRAPPED.
Module Export all_classical.
Export mathcomp.classical.classical_sets.
Export mathcomp.classical.set_interval.

End all_classical.
Module Export mathcomp.
Module Export classical.
Module Export all_classical.
Include mathcomp_DOT_classical_DOT_all_classical_WRAPPED.all_classical.
End all_classical.

Import HB.structures.
Import mathcomp.ssreflect.all_ssreflect.
Import mathcomp.classical.all_classical.

Set Implicit Arguments.
Unset Strict Implicit.

Local Open Scope classical_set_scope.

HB.mixin Record Nbhs_isTopological (T : Type) of Nbhs T := {
  open : set_system T;
  nbhs_pfilter_subproof : forall p : T, ProperFilter (nbhs p) ;
  nbhsE_subproof : forall p : T, nbhs p =
    [set A : set T | exists B : set T, [/\ open B, B p & B `<=` A] ] ;
  openE_subproof : open = [set A : set T | A `<=` nbhs^~ A ]
}.

#[short(type="topologicalType")]
HB.structure Definition Topological :=
  {T of Nbhs T & Nbhs_isTopological T}.

Section Topological1.
Context {T : topologicalType}.
Lemma nbhs_filter (p : T) : Filter (nbhs p).
Admitted.

Canonical nbhs_filter_on (x : T) := FilterType (nbhs x) (@nbhs_filter x).

Definition interior (A : set T) := (@nbhs _ T)^~ A.

Local Notation "A ^°" := (interior A).

Lemma openE : open = [set A : set T | A `<=` A^°].
Admitted.

End Topological1.

HB.factory Record Nbhs_isNbhsTopological T of Nbhs T := {
  nbhs_filter : forall p : T, ProperFilter (nbhs p);
  nbhs_singleton : forall (p : T) (A : set T), nbhs p A -> A p;
  nbhs_nbhs : forall (p : T) (A : set T), nbhs p A -> nbhs p (nbhs^~ A);
}.

HB.builders Context T of Nbhs_isNbhsTopological T.

Definition open_of_nbhs := [set A : set T | A `<=` nbhs^~ A].

Let nbhsE_subproof (p : T) :
  nbhs p = [set A | exists B, [/\ open_of_nbhs B, B p & B `<=` A] ].
Admitted.

Let openE_subproof : open_of_nbhs = [set A : set T | A `<=` nbhs^~ A].
Admitted.

HB.instance Definition _ := Nbhs_isTopological.Build T
  nbhs_filter nbhsE_subproof openE_subproof.

HB.end.

Definition nbhs_of_open (T : Type) (op : set T -> Prop) (p : T) (A : set T) :=
  exists B, [/\ op B, B p & B `<=` A].

HB.factory Record isOpenTopological T of Choice T := {
  op : set T -> Prop;
  opT : op setT;
  opI : forall (A B : set T), op A -> op B -> op (A `&` B);
  op_bigU : forall (I : Type) (f : I -> set T), (forall i, op (f i)) ->
    op (\bigcup_i f i);
}.

HB.builders Context T of isOpenTopological T.

HB.instance Definition _ := hasNbhs.Build T (nbhs_of_open op).

Let nbhs_pfilter_subproof (p : T) : ProperFilter (nbhs p).
Admitted.

Let nbhsE_subproof (p : T) :
  nbhs p = [set A | exists B, [/\ op B, B p & B `<=` A] ].
Admitted.

Let openE_subproof : op = [set A : set T | A `<=` nbhs^~ A].
Admitted.

HB.instance Definition _ := Nbhs_isTopological.Build T
  nbhs_pfilter_subproof nbhsE_subproof openE_subproof.

HB.end.

HB.factory Record isBaseTopological T of Choice T := {
  I : pointedType;
  D : set I;
  b : I -> (set T);
  b_cover : \bigcup_(i in D) b i = setT;
  b_join : forall i j t, D i -> D j -> b i t -> b j t ->
    exists k, [/\ D k, b k t & b k `<=` b i `&` b j];
}.

HB.builders Context T of isBaseTopological T.

Definition open_from := [set \bigcup_(i in D') b i | D' in subset^~ D].

Let open_fromT : open_from setT.
Admitted.

Let open_fromI (A B : set T) : open_from A -> open_from B ->
  open_from (A `&` B).
Admitted.

Let open_from_bigU (I0 : Type) (f : I0 -> set T) :
  (forall i, open_from (f i)) -> open_from (\bigcup_i f i).
Admitted.

HB.instance Definition _ := isOpenTopological.Build T
  open_fromT open_fromI open_from_bigU.

HB.end.

HB.factory Record isSubBaseTopological T of Choice T := {
  I : pointedType;
  D : set I;
  b : I -> (set T);
}.

HB.builders Context T of isSubBaseTopological T.

Local Notation finI_from := (finI_from D b).

Let finI_from_cover : \bigcup_(A in finI_from) A = setT.
Admitted.

Let finI_from_join A B t : finI_from A -> finI_from B -> A t -> B t ->
  exists k, [/\ finI_from k, k t & k `<=` A `&` B].
Admitted.

HB.instance Definition _ := isBaseTopological.Build T
  finI_from_cover finI_from_join.

HB.end.

Import mathcomp.algebra.all_algebra.
Local Open Scope ring_scope.

HB.mixin Record Order_isNbhs d (T : Type) of Nbhs T & Order.Total d T := {

  itv_nbhsE : forall x : T, nbhs x = filter_from
    (fun i => itv_open_ends i /\ x \in i)
    (fun i => [set` i])
}.

#[short(type="orderTopologicalType")]
HB.structure Definition OrderTopological d :=
  { T of Topological T & Order.Total d T & Order_isNbhs d T }.
Definition order_topology (T : Type) : Type.
exact (T).
Defined.

Section induced_order_topology.

Context {d} {T : orderType d}.

Local Notation oT := (order_topology T).

HB.instance Definition _ := isPointed.Build (interval T) (`]-oo,+oo[).

HB.instance Definition _ := Order.Total.on oT.
HB.instance Definition _ := @isSubBaseTopological.Build oT
  (interval T) (itv_is_ray) (fun i => [set` i]).

Lemma order_nbhs_itv (x : oT) : nbhs x = filter_from
    (fun i => itv_open_ends i /\ x \in i)
    (fun i => [set` i]).
Admitted.

HB.instance Definition _ := Order_isNbhs.Build _ oT order_nbhs_itv.
End induced_order_topology.
Definition weak_topology {S : Type} {T : Type}
  (f : S -> T) : Type.
exact (S).
Defined.

Section Weak_Topology.
Variable (S : choiceType) (T : topologicalType) (f : S -> T).
Local Notation W := (weak_topology f).

Definition wopen := [set f @^-1` A | A in open].

Local Lemma wopT : wopen [set: W].
Admitted.

Local Lemma wopI (A B : set W) : wopen A -> wopen B -> wopen (A `&` B).
Admitted.

Local Lemma wop_bigU (I : Type) (g : I -> set W) :
  (forall i, wopen (g i)) -> wopen (\bigcup_i g i).
Admitted.

HB.instance Definition _ := Choice.on W.
HB.instance Definition _ :=
  isOpenTopological.Build W wopT wopI wop_bigU.

End Weak_Topology.

Section weak_order_refine.
Context {d} {X : orderTopologicalType d} {Y : subType X}.
Let OrdU : orderTopologicalType d.
exact (order_topology (sub_type Y)).
Defined.
Let WeakU : topologicalType.
exact (@weak_topology (sub_type Y) X val).
Defined.

Lemma open_order_weak (U : set Y) : @open OrdU U -> @open WeakU U.
Proof.
rewrite ?openE /= /interior => + x Ux => /(_ x Ux); rewrite itv_nbhsE /=.
move=> [][][[]l|[]] [[]r|[]][][]//= _ xlr /filterS; apply.
-
 exists `]l, r[%classic; split => //=; exists `]\val l, \val r[%classic.
