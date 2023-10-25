
(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "-parsing" "-w" "+undeclared-scope" "-w" "+non-primitive-record" "-w" "-ambiguous-paths" "-w" "-redundant-canonical-projection" "-w" "-projection-no-head-constant" "-w" "-deprecated-native-compiler-option" "-native-compiler" "ondemand" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/analysis/classical" "mathcomp.classical" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/analysis/theories" "mathcomp.analysis" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/HB" "HB" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/elpi" "elpi" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/mathcomp" "mathcomp" "-top" "Top.bug_01") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 579 lines to 89 lines, then from 102 lines to 6293 lines, then from 6296 lines to 5465 lines, then from 5180 lines to 3737 lines, then from 3745 lines to 105 lines, then from 118 lines to 8258 lines, then from 8262 lines to 8652 lines, then from 8138 lines to 4974 lines *)
(* coqc version 8.19+alpha compiled with OCaml 4.14.1
   coqtop version 28f8ca807578:/builds/coq/coq/_build/default,(HEAD detached at e3a3a61) (e3a3a6145f06cd1cd15ecb40292486f2f4783b7d)
   Expected coqc runtime on this file: 5.850 sec *)
Require Coq.Init.Ltac.
Require Coq.Bool.Bool.
Require Coq.Floats.PrimFloat.
Require Coq.NArith.BinNat.
Require Coq.NArith.Ndec.
Require Coq.Numbers.Cyclic.Int63.PrimInt63.
Require Coq.PArith.BinPos.
Require Coq.Setoids.Setoid.
Require Coq.Strings.String.
Require Coq.setoid_ring.Field_tac.
Require Coq.setoid_ring.Field_theory.
Require Coq.setoid_ring.Ring.
Require Coq.ssr.ssrbool.
Require Coq.ssr.ssreflect.
Require Coq.ssr.ssrfun.
Require mathcomp.ssreflect.ssrnotations.
Require mathcomp.ssreflect.ssreflect.
Require elpi.elpi.
Require mathcomp.ssreflect.ssrfun.
Require mathcomp.ssreflect.ssrbool.
Require mathcomp.ssreflect.eqtype.
Require HB.structures.
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
Require mathcomp.algebra.ring_quotient.
Require mathcomp.fingroup.perm.
Require mathcomp.algebra.countalg.
Require mathcomp.fingroup.automorphism.
Require mathcomp.algebra.poly.
Require mathcomp.fingroup.quotient.
Require mathcomp.ssreflect.all_ssreflect.
Require mathcomp.algebra.polydiv.
Require mathcomp.classical.boolp.
Require mathcomp.fingroup.action.
Require mathcomp.algebra.fraction.
Require mathcomp.algebra.ssrnum.
Require mathcomp.algebra.interval.
Require mathcomp.algebra.ssrint.
Require mathcomp.algebra.finalg.
Require mathcomp.algebra.zmodp.
Require mathcomp.algebra.rat.
Require mathcomp.algebra.matrix.
Require mathcomp.algebra.mxalgebra.
Require mathcomp.algebra.vector.
Require mathcomp.algebra.mxpoly.
Require mathcomp.classical.mathcomp_extra.
Require mathcomp.algebra.polyXY.
Require mathcomp.analysis.signed.
Require mathcomp.algebra.qpoly.
Require mathcomp.algebra.intdiv.
Require mathcomp.classical.classical_sets.
Require mathcomp.algebra.all_algebra.
Require mathcomp.classical.functions.
Require mathcomp.classical.cardinality.
Require mathcomp.classical.set_interval.
Require mathcomp.classical.fsbigop.
Require mathcomp.analysis.reals.

Module Export AdmitTactic.
Module Import LocalFalse.
Inductive False : Prop := .
End LocalFalse.
Axiom proof_admitted : False.
Import Coq.Init.Ltac.
Tactic Notation "admit" := abstract case proof_admitted.
End AdmitTactic.
Module mathcomp_DOT_analysis_DOT_topology_WRAPPED.
Module Export topology.
Import mathcomp.ssreflect.all_ssreflect.
Import mathcomp.algebra.all_algebra.
Import mathcomp.finmap.finmap.
Import mathcomp.ssreflect.generic_quotient.
Import mathcomp.classical.boolp.
Import mathcomp.classical.classical_sets.
Import mathcomp.classical.functions.
Import mathcomp.classical.cardinality.
Import mathcomp.classical.mathcomp_extra.
Import mathcomp.classical.fsbigop.
Import mathcomp.analysis.reals.
Import mathcomp.analysis.signed.

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
Reserved Notation "[ 'filter' 'of' x ]" (format "[ 'filter'  'of'  x ]").
Reserved Notation "F `=>` G" (at level 70, format "F  `=>`  G").
Reserved Notation "F --> G" (at level 70, format "F  -->  G").
Reserved Notation "[ 'lim' F 'in' T ]" (format "[ 'lim'  F  'in'  T ]").
Reserved Notation "[ 'cvg' F 'in' T ]" (format "[ 'cvg'  F  'in'  T ]").
Reserved Notation "x \is_near F" (at level 10, format "x  \is_near  F").
Reserved Notation "E @[ x --> F ]"
  (at level 60, x name, format "E  @[ x  -->  F ]").
Reserved Notation "f @ F" (at level 60, format "f  @  F").
Reserved Notation "E `@[ x --> F ]"
  (at level 60, x name, format "E  `@[ x  -->  F ]").
Reserved Notation "f `@ F" (at level 60, format "f  `@  F").
Reserved Notation "A ^°" (at level 1, format "A ^°").
Reserved Notation "[ 'locally' P ]" (at level 0, format "[ 'locally'  P ]").
Reserved Notation "x ^'" (at level 2, format "x ^'").
Reserved Notation "{ 'within' A , 'continuous' f }"
  (at level 70, A at level 69, format "{ 'within'  A ,  'continuous'  f }").
Reserved Notation "{ 'uniform`' A -> V }"
  (at level 0, A at level 69, format "{ 'uniform`'  A  ->  V }").
Reserved Notation "{ 'uniform' U -> V }"
  (at level 0, U at level 69, format "{ 'uniform'  U  ->  V }").
Reserved Notation "{ 'uniform' A , F --> f }"
  (at level 0, A at level 69, F at level 69,
   format "{ 'uniform'  A ,  F  -->  f }").
Reserved Notation "{ 'uniform' , F --> f }"
  (at level 0, F at level 69,
   format "{ 'uniform' ,  F  -->  f }").
Reserved Notation "{ 'ptws' U -> V }"
  (at level 0, U at level 69, format "{ 'ptws'  U  ->  V }").
Reserved Notation "{ 'ptws' , F --> f }"
  (at level 0, F at level 69, format "{ 'ptws' ,  F  -->  f }").
Reserved Notation "{ 'family' fam , U -> V }"
  (at level 0, U at level 69, format "{ 'family'  fam ,  U  ->  V }").
Reserved Notation "{ 'family' fam , F --> f }"
  (at level 0, F at level 69, format "{ 'family'  fam ,  F  -->  f }").

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Obligation Tactic := idtac.
Import Order.TTheory.
Import GRing.Theory.
Import Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section bigmaxmin.
Local Notation max := Order.max.
Local Notation min := Order.min.
Local Open Scope order_scope.
Variables (d : unit) (T : orderType d) (x : T) (I : finType) (P : pred I)
          (m : T) (F : I -> T).

Lemma bigmax_geP : reflect (m <= x \/ exists2 i, P i & m <= F i)
                           (m <= \big[max/x]_(i | P i) F i).
Admitted.

Lemma bigmax_gtP : reflect (m < x \/ exists2 i, P i & m < F i)
                           (m < \big[max/x]_(i | P i) F i).
Admitted.

Lemma bigmin_leP : reflect (x <= m \/ exists2 i, P i & F i <= m)
                           (\big[min/x]_(i | P i) F i <= m).
Admitted.

Lemma bigmin_ltP : reflect (x < m \/ exists2 i, P i & F i < m)
                           (\big[min/x]_(i | P i) F i < m).
Admitted.

End bigmaxmin.

Definition monotonous d (T : porderType d) (pT : predType T) (A : pT) (f : T -> T) :=
  {in A &, {mono f : x y / (x <= y)%O}} \/ {in A &, {mono f : x y /~ (x <= y)%O}}.

Lemma and_prop_in (T : Type) (p : mem_pred T) (P Q : T -> Prop) :
  {in p, forall x, P x /\ Q x} <->
  {in p, forall x, P x} /\ {in p, forall x, Q x}.
Admitted.

Lemma mem_inc_segment d (T : porderType d) (a b : T) (f : T -> T) :
    {in `[a, b] &, {mono f : x y / (x <= y)%O}} ->
  {homo f : x / x \in `[a, b] >-> x \in `[f a, f b]}.
Admitted.

Lemma mem_dec_segment d (T : porderType d) (a b : T) (f : T -> T) :
    {in `[a, b] &, {mono f : x y /~ (x <= y)%O}} ->
  {homo f : x / x \in `[a, b] >-> x \in `[f b, f a]}.
Admitted.

Section Linear1.
Context (R : ringType) (U : lmodType R) (V : zmodType) (s : R -> V -> V).
Canonical linear_eqType := EqType {linear U -> V | s} gen_eqMixin.
Canonical linear_choiceType := ChoiceType {linear U -> V | s} gen_choiceMixin.
End Linear1.
Section Linear2.
Context (R : ringType) (U : lmodType R) (V : zmodType) (s : R -> V -> V)
        (s_law : GRing.Scale.law s).
Canonical linear_pointedType := PointedType {linear U -> V | GRing.Scale.op s_law}
                                            (@GRing.null_fun_linear R U V s s_law).
End Linear2.

Module Filtered.

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
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of U xT).
Local Coercion base : class_of >-> Pointed.class_of.

Definition pack m :=
  fun bT b of phant_id (Pointed.class bT) b => @Pack T (Class b m).

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition fpointedType := @Pointed.Pack cT xclass.

End ClassDef.

Structure source Z Y := Source {
  source_type :> Type;
  _ : (source_type -> Z) -> set (set Y)
}.
Definition source_filter Z Y (F : source Z Y) : (F -> Z) -> set (set Y) :=
  let: Source X f := F in f.

Module Export Exports.
Coercion sort : type >-> Sortclass.
Coercion base : class_of >-> Pointed.class_of.
Coercion nbhs_op : class_of >-> nbhs_of.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion fpointedType : type >-> Pointed.type.
Canonical fpointedType.
Notation filteredType := type.
Notation FilteredType U T m := (@pack U T m _ _ idfun).
Notation "[ 'filteredType' U 'of' T 'for' cT ]" :=  (@clone U T cT _ idfun)
  (at level 0, format "[ 'filteredType'  U  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'filteredType' U 'of' T ]" := (@clone U T _ _ id)
  (at level 0, format "[ 'filteredType'  U  'of'  T ]") : form_scope.

Canonical default_arrow_filter Y (Z : pointedType) (X : source Z Y) :=
  FilteredType Y (X -> Z) (@source_filter _ _ X).
Canonical source_filter_filter Y :=
  @Source Prop _ (_ -> Prop) (fun x : (set (set Y)) => x).
Canonical source_filter_filter' Y :=
  @Source Prop _ (set _) (fun x : (set (set Y)) => x).

End Exports.
End Filtered.
Export Filtered.Exports.

Definition nbhs {U} {T : filteredType U} : T -> set (set U) :=
  Filtered.nbhs_op (Filtered.class T).
Arguments nbhs {U T} _ _ : simpl never.
Definition filter_from {I T : Type} (D : set I) (B : I -> set T) : set (set T). exact ([set P | exists2 i, D i & B i `<=` P]). Defined.
Canonical matrix_filtered m n X (Z : filteredType X) : filteredType 'M[X]_(m, n). exact (FilteredType 'M[X]_(m, n) 'M[Z]_(m, n) (fun mx => filter_from
    [set P | forall i j, nbhs (mx i j) (P i j)]
    (fun P => [set my : 'M[X]_(m, n) | forall i j, P i j (my i j)]))). Defined.
Definition filter_prod {T U : Type}
  (F : set (set T)) (G : set (set U)) : set (set (T * U)). exact (filter_from (fun P => F P.1 /\ G P.2) (fun P => P.1 `*` P.2)). Defined.

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

Lemma nearE {T} {F : set (set T)} (P : set T) : (\forall x \near F, P x) = F P.
Admitted.

Lemma eq_near {T} {F : set (set T)} (P Q : set T) :
   (forall x, P x <-> Q x) ->
   (\forall x \near F, P x) = (\forall x \near F, Q x).
Admitted.

Definition filter_of X (fX : filteredType X) (x : fX) of phantom fX x :=
   nbhs x.
Notation "[ 'filter' 'of' x ]" :=
  (@filter_of _ _ _ (Phantom _ x)) : classical_set_scope.
Arguments filter_of _ _ _ _ _ /.

Lemma filter_of_filterE {T : Type} (F : set (set T)) : [filter of F] = F.
Admitted.

Lemma nbhs_filterE {T : Type} (F : set (set T)) : nbhs F = F.
Admitted.

Module Export NbhsFilter.
Definition nbhs_simpl := (@filter_of_filterE, @nbhs_filterE).
End NbhsFilter.

Definition cvg_to {T : Type} (F G : set (set T)) := G `<=` F.
Notation "F `=>` G" := (cvg_to F G) : classical_set_scope.
Lemma cvg_refl T (F : set (set T)) : F `=>` F.
Admitted.
Arguments cvg_refl {T F}.
#[global] Hint Resolve cvg_refl : core.

Lemma cvg_trans T (G F H : set (set T)) :
  (F `=>` G) -> (G `=>` H) -> (F `=>` H).
Admitted.

Notation "F --> G" := (cvg_to [filter of F] [filter of G]) : classical_set_scope.
Definition type_of_filter {T} (F : set (set T)) := T.

Definition lim_in {U : Type} (T : filteredType U) :=
  fun F : set (set U) => get (fun l : T => F --> l).
Notation "[ 'lim' F 'in' T ]" := (@lim_in _ T [filter of F]) : classical_set_scope.
Notation lim F := [lim F in [filteredType _ of @type_of_filter _ [filter of F]]].
Notation "[ 'cvg' F 'in' T ]" := (F --> [lim F in T]) : classical_set_scope.
Notation cvg F := [cvg F in [filteredType _ of @type_of_filter _ [filter of F]]].

Section FilteredTheory.
Canonical filtered_prod X1 X2 (Z1 : filteredType X1)
  (Z2 : filteredType X2) : filteredType (X1 * X2). exact (FilteredType (X1 * X2) (Z1 * Z2)
    (fun x => filter_prod (nbhs x.1) (nbhs x.2))). Defined.

Lemma cvg_prod T {U U' V V' : filteredType T} (x : U) (l : U') (y : V) (k : V') :
  x --> l -> y --> k -> (x, y) --> (l, k).
Admitted.

Lemma cvg_ex {U : Type} (T : filteredType U) (F : set (set U)) :
  [cvg F in T] <-> (exists l : T, F --> l).
Admitted.

Lemma cvgP {U : Type} (T : filteredType U) (F : set (set U)) (l : T) :
   F --> l -> [cvg F in T].
Admitted.

Lemma cvg_toP {U : Type} (T : filteredType U) (F : set (set U)) (l : T) :
   [cvg F in T] -> [lim F in T] = l -> F --> l.
Admitted.

Lemma dvgP {U : Type} (T : filteredType U) (F : set (set U)) :
  ~ [cvg F in T] -> [lim F in T] = point.
Admitted.

Lemma cvgNpoint {U} (T : filteredType U) (F : set (set U)) :
  [lim F in T] != point -> [cvg F in T].
Admitted.

End FilteredTheory.
Arguments cvgP {U T F} l.
Arguments dvgP {U} T {F}.

Lemma nbhs_nearE {U} {T : filteredType U} (x : T) (P : set U) :
  nbhs x P = \near x, P x.
Admitted.

Lemma near_nbhs {U} {T : filteredType U} (x : T) (P : set U) :
  (\forall x \near nbhs x, P x) = \near x, P x.
Admitted.

Lemma near2_curry {U V} (F : set (set U)) (G : set (set V)) (P : U -> set V) :
  {near F & G, forall x y, P x y} = {near (F, G), forall x, P x.1 x.2}.
Admitted.

Lemma near2_pair {U V} (F : set (set U)) (G : set (set V)) (P : set (U * V)) :
  {near F & G, forall x y, P (x, y)} = {near (F, G), forall x, P x}.
Admitted.

Definition near2E := (@near2_curry, @near2_pair).

Lemma filter_of_nearI (X : Type) (fX : filteredType X)
  (x : fX) (ph : phantom fX x) : forall P,
  @filter_of X fX x ph P = @prop_near1 X fX x P (inPhantom (forall x, P x)).
Admitted.

Module Export NearNbhs.
Definition near_simpl := (@near_nbhs, @nbhs_nearE, filter_of_nearI).
Ltac near_simpl := rewrite ?near_simpl.
End NearNbhs.

Lemma near_swap {U V} (F : set (set U)) (G : set (set V)) (P : U -> set V) :
  (\forall x \near F & y \near G, P x y) = (\forall y \near G & x \near F, P x y).
Admitted.

Class Filter {T : Type} (F : set (set T)) := {
  filterT : F setT ;
  filterI : forall P Q : set T, F P -> F Q -> F (P `&` Q) ;
  filterS : forall P Q : set T, P `<=` Q -> F P -> F Q
}.
Global Hint Mode Filter - ! : typeclass_instances.

Class ProperFilter' {T : Type} (F : set (set T)) := {
  filter_not_empty : not (F (fun _ => False)) ;
  filter_filter' : Filter F
}.

Global Existing Instance filter_filter'.
Global Hint Mode ProperFilter' - ! : typeclass_instances.
Arguments filter_not_empty {T} F {_}.

Notation ProperFilter := ProperFilter'.

Lemma filter_setT (T' : Type) : Filter [set: set T'].
Admitted.

Lemma filterP_strong T (F : set (set T)) {FF : Filter F} (P : set T) :
  (exists Q : set T, exists FQ  : F Q, forall x : T, Q x -> P x) <-> F P.
Admitted.

Structure filter_on T := FilterType {
  filter :> (T -> Prop) -> Prop;
  _ : Filter filter
}.
Definition filter_class T (F : filter_on T) : Filter F. exact (let: FilterType _ class := F in class). Defined.
Arguments FilterType {T} _ _.
#[global] Existing Instance filter_class.

Coercion filter_filter' : ProperFilter >-> Filter.

Structure pfilter_on T := PFilterPack {
  pfilter :> (T -> Prop) -> Prop;
  _ : ProperFilter pfilter
}.
Definition pfilter_class T (F : pfilter_on T) : ProperFilter F. exact (let: PFilterPack _ class := F in class). Defined.
Arguments PFilterPack {T} _ _.
#[global] Existing Instance pfilter_class.

Canonical pfilter_filter_on T (F : pfilter_on T) :=
  FilterType F (pfilter_class F).
Coercion pfilter_filter_on : pfilter_on >-> filter_on.
Definition PFilterType {T} (F : (T -> Prop) -> Prop)
  {fF : Filter F} (fN0 : not (F set0)) :=
  PFilterPack F (Build_ProperFilter' fN0 fF).
Arguments PFilterType {T} F {fF} fN0.

Canonical filter_on_eqType T := EqType (filter_on T) gen_eqMixin.
Canonical filter_on_choiceType T :=
  ChoiceType (filter_on T) gen_choiceMixin.
Canonical filter_on_PointedType T :=
  PointedType (filter_on T) (FilterType _ (filter_setT T)).
Canonical filter_on_FilteredType T :=
  FilteredType T (filter_on T) (@filter T).

Global Instance filter_on_Filter T (F : filter_on T) : Filter F.
Admitted.
Global Instance pfilter_on_ProperFilter T (F : pfilter_on T) : ProperFilter F.
Admitted.

Lemma nbhs_filter_onE T (F : filter_on T) : nbhs F = nbhs (filter F).
Admitted.
Definition nbhs_simpl := (@nbhs_simpl, @nbhs_filter_onE).

Lemma near_filter_onE T (F : filter_on T) (P : set T) :
  (\forall x \near F, P x) = \forall x \near filter F, P x.
Admitted.
Definition near_simpl := (@near_simpl, @near_filter_onE).

Program Definition trivial_filter_on T := FilterType [set setT : set T] _.
Admit Obligations.
Canonical trivial_filter_on.

Lemma filter_nbhsT {T : Type} (F : set (set T)) :
   Filter F -> nbhs F setT.
Admitted.
#[global] Hint Resolve filter_nbhsT : core.

Lemma nearT {T : Type} (F : set (set T)) : Filter F -> \near F, True.
Admitted.
#[global] Hint Resolve nearT : core.

Lemma filter_not_empty_ex {T : Type} (F : set (set T)) :
    (forall P, F P -> exists x, P x) -> ~ F set0.
Admitted.

Definition Build_ProperFilter {T : Type} (F : set (set T))
  (filter_ex : forall P, F P -> exists x, P x)
  (filter_filter : Filter F) :=
  Build_ProperFilter' (filter_not_empty_ex filter_ex) (filter_filter).

Lemma filter_ex_subproof {T : Type} (F : set (set T)) :
     ~ F set0 -> (forall P, F P -> exists x, P x).
Admitted.

Definition filter_ex {T : Type} (F : set (set T)) {FF : ProperFilter F} :=
  filter_ex_subproof (filter_not_empty F).
Arguments filter_ex {T F FF _}.

Lemma filter_getP {T : pointedType} (F : set (set T)) {FF : ProperFilter F}
      (P : set T) : F P -> P (get P).
Admitted.

Record in_filter T (F : set (set T)) := InFilter {
  prop_in_filter_proj : T -> Prop;
  prop_in_filterP_proj : F prop_in_filter_proj
}.

Module Type PropInFilterSig.
Axiom t : forall (T : Type) (F : set (set T)), in_filter F -> T -> Prop.
Axiom tE : t = prop_in_filter_proj.
End PropInFilterSig.
Module PropInFilter : PropInFilterSig.
Definition t := prop_in_filter_proj.
Lemma tE : t = prop_in_filter_proj.
Admitted.
End PropInFilter.

Notation prop_of := PropInFilter.t.
Definition prop_ofE := PropInFilter.tE.
Notation "x \is_near F" := (@PropInFilter.t _ F _ x).
Definition is_nearE := prop_ofE.

Lemma prop_ofP T F (iF : @in_filter T F) : F (prop_of iF).
Admitted.
Definition in_filterT T F (FF : Filter F) : @in_filter T F. exact (InFilter (filterT)). Defined.
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

Ltac under_near i tac := near=> i; tac; near: i.
Tactic Notation "near=>" ident(i) "do" tactic1(tac) := under_near i ltac:(tac).
Tactic Notation "near=>" ident(i) "do" "[" tactic4(tac) "]" := near=> i do tac.
Tactic Notation "near" "do" tactic1(tac) :=
  let i := fresh "i" in under_near i ltac:(tac).
Tactic Notation "near" "do" "[" tactic4(tac) "]" := near do tac.

Lemma have_near (U : Type) (fT : filteredType U) (x : fT) (P : Prop) :
  ProperFilter (nbhs x) -> (\forall x \near x, P) -> P.
Admitted.
Arguments have_near {U fT} x.

Tactic Notation "near" constr(F) "=>" ident(x) :=
  apply: (have_near F); near=> x.

Lemma near T (F : set (set T)) P (FP : F P) (x : T)
  (Px : prop_of (InFilter FP) x) : P x.
Admitted.
Arguments near {T F P} FP x Px.

Lemma nearW {T : Type} {F : set (set T)} (P : T -> Prop) :
  Filter F -> (forall x, P x) -> (\forall x \near F, P x).
Admitted.

Lemma filterE {T : Type} {F : set (set T)} :
  Filter F -> forall P : set T, (forall x, P x) -> F P.
Admitted.

Lemma filter_app (T : Type) (F : set (set T)) :
  Filter F -> forall P Q : set T, F (fun x => P x -> Q x) -> F P -> F Q.
Admitted.

Lemma filter_app2 (T : Type) (F : set (set T)) :
  Filter F -> forall P Q R : set T,  F (fun x => P x -> Q x -> R x) ->
  F P -> F Q -> F R.
Admitted.

Lemma filter_app3 (T : Type) (F : set (set T)) :
  Filter F -> forall P Q R S : set T, F (fun x => P x -> Q x -> R x -> S x) ->
  F P -> F Q -> F R -> F S.
Admitted.

Lemma filterS2 (T : Type) (F : set (set T)) :
  Filter F -> forall P Q R : set T, (forall x, P x -> Q x -> R x) ->
  F P -> F Q -> F R.
Admitted.

Lemma filterS3 (T : Type) (F : set (set T)) :
  Filter F -> forall P Q R S : set T, (forall x, P x -> Q x -> R x -> S x) ->
  F P -> F Q -> F R -> F S.
Admitted.

Lemma filter_const {T : Type} {F} {FF: @ProperFilter T F} (P : Prop) :
  F (fun=> P) -> P.
Admitted.

Lemma in_filter_from {I T : Type} (D : set I) (B : I -> set T) (i : I) :
  D i -> filter_from D B (B i).
Admitted.

Lemma near_andP {T : Type} F (b1 b2 : T -> Prop) : Filter F ->
  (\forall x \near F, b1 x /\ b2 x) <->
    (\forall x \near F, b1 x) /\ (\forall x \near F, b2 x).
Admitted.

Lemma nearP_dep {T U} {F : set (set T)} {G : set (set U)}
   {FF : Filter F} {FG : Filter G} (P : T -> U -> Prop) :
  (\forall x \near F & y \near G, P x y) ->
  \forall x \near F, \forall y \near G, P x y.
Admitted.

Lemma filter2P T U (F : set (set T)) (G : set (set U))
  {FF : Filter F} {FG : Filter G} (P : set (T * U)) :
  (exists2 Q : set T * set U, F Q.1 /\ G Q.2
     & forall (x : T) (y : U), Q.1 x -> Q.2 y -> P (x, y))
   <-> \forall x \near (F, G), P x.
Admitted.

Lemma filter_ex2 {T U : Type} (F : set (set T)) (G : set (set U))
  {FF : ProperFilter F} {FG : ProperFilter G} (P : set T) (Q : set U) :
    F P -> G Q -> exists x : T, exists2 y : U, P x & Q y.
Admitted.
Arguments filter_ex2 {T U F G FF FG _ _}.

Lemma filter_fromP {I T : Type} (D : set I) (B : I -> set T) (F : set (set T)) :
  Filter F -> F `=>` filter_from D B <-> forall i, D i -> F (B i).
Admitted.

Lemma filter_fromTP {I T : Type} (B : I -> set T) (F : set (set T)) :
  Filter F -> F `=>` filter_from setT B <-> forall i, F (B i).
Admitted.

Lemma filter_from_filter {I T : Type} (D : set I) (B : I -> set T) :
  (exists i : I, D i) ->
  (forall i j, D i -> D j -> exists2 k, D k & B k `<=` B i `&` B j) ->
  Filter (filter_from D B).
Admitted.

Lemma filter_fromT_filter {I T : Type} (B : I -> set T) :
  (exists _ : I, True) ->
  (forall i j, exists k, B k `<=` B i `&` B j) ->
  Filter (filter_from setT B).
Admitted.

Lemma filter_from_proper {I T : Type} (D : set I) (B : I -> set T) :
  Filter (filter_from D B) ->
  (forall i, D i -> B i !=set0) ->
  ProperFilter (filter_from D B).
Admitted.

Lemma filter_bigI T (I : choiceType) (D : {fset I}) (f : I -> set T)
  (F : set (set T)) :
  Filter F -> (forall i, i \in D -> F (f i)) ->
  F (\bigcap_(i in [set i | i \in D]) f i).
Admitted.

Lemma filter_forall T (I : finType) (f : I -> set T) (F : set (set T)) :
    Filter F -> (forall i : I, \forall x \near F, f i x) ->
  \forall x \near F, forall i, f i x.
Admitted.

Lemma filter_imply [T : Type] [P : Prop] [f : set T] [F : set (set T)] :
  Filter F -> (P -> \near F, f F) -> \near F, P -> f F.
Admitted.

Definition fmap {T U : Type} (f : T -> U) (F : set (set T)) :=
  [set P | F (f @^-1` P)].
Arguments fmap _ _ _ _ _ /.

Lemma fmapE {U V : Type} (f : U -> V)
  (F : set (set U)) (P : set V) : fmap f F P = F (f @^-1` P).
Admitted.

Notation "E @[ x --> F ]" :=
  (fmap (fun x => E) [filter of F]) : classical_set_scope.
Notation "f @ F" := (fmap f [filter of F]) : classical_set_scope.
Global Instance fmap_filter T U (f : T -> U) (F : set (set T)) :
  Filter F -> Filter (f @ F).
Admitted.

Global Instance fmap_proper_filter T U (f : T -> U) (F : set (set T)) :
  ProperFilter F -> ProperFilter (f @ F).
Admitted.
Definition fmap_proper_filter' := fmap_proper_filter.

Definition fmapi {T U : Type} (f : T -> set U) (F : set (set T)) :=
  [set P | \forall x \near F, exists y, f x y /\ P y].

Notation "E `@[ x --> F ]" :=
  (fmapi (fun x => E) [filter of F]) : classical_set_scope.
Notation "f `@ F" := (fmapi f [filter of F]) : classical_set_scope.

Lemma fmapiE {U V : Type} (f : U -> set V)
  (F : set (set U)) (P : set V) :
  fmapi f F P = \forall x \near F, exists y, f x y /\ P y.
Admitted.

Global Instance fmapi_filter T U (f : T -> set U) (F : set (set T)) :
  infer {near F, is_totalfun f} -> Filter F -> Filter (f `@ F).
Admitted.

#[global] Typeclasses Opaque fmapi.

Global Instance fmapi_proper_filter
  T U (f : T -> U -> Prop) (F : set (set T)) :
  infer {near F, is_totalfun f} ->
  ProperFilter F -> ProperFilter (f `@ F).
Admitted.
Definition filter_map_proper_filter' := fmapi_proper_filter.

Lemma cvg_id T (F : set (set T)) : x @[x --> F] --> F.
Admitted.
Arguments cvg_id {T F}.

Lemma fmap_comp {A B C} (f : B -> C) (g : A -> B) F:
  Filter F -> (f \o g)%FUN @ F = f @ (g @ F).
Admitted.

Lemma appfilter U V (f : U -> V) (F : set (set U)) :
  f @ F = [set P : set _ | \forall x \near F, P (f x)].
Admitted.

Lemma cvg_app U V (F G : set (set U)) (f : U -> V) :
  F --> G -> f @ F --> f @ G.
Admitted.
Arguments cvg_app {U V F G} _.

Lemma cvgi_app U V (F G : set (set U)) (f : U -> set V) :
  F --> G -> f `@ F --> f `@ G.
Admitted.

Lemma cvg_comp T U V (f : T -> U) (g : U -> V)
  (F : set (set T)) (G : set (set U)) (H : set (set V)) :
  f @ F `=>` G -> g @ G `=>` H -> g \o f @ F `=>` H.
Admitted.

Lemma cvgi_comp T U V (f : T -> U) (g : U -> set V)
  (F : set (set T)) (G : set (set U)) (H : set (set V)) :
  f @ F `=>` G -> g `@ G `=>` H -> g \o f `@ F `=>` H.
Admitted.

Lemma near_eq_cvg {T U} {F : set (set T)} {FF : Filter F} (f g : T -> U) :
  {near F, f =1 g} -> g @ F `=>` f @ F.
Admitted.

Lemma eq_cvg (T T' : Type) (F : set (set T)) (f g : T -> T') (x : set (set T')) :
  f =1 g -> (f @ F --> x) = (g @ F --> x).
Admitted.

Lemma eq_is_cvg (T T' : Type) (fT : filteredType T') (F : set (set T)) (f g : T -> T') :
  f =1 g -> [cvg (f @ F) in fT] = [cvg (g @ F) in fT].
Admitted.

Lemma neari_eq_loc {T U} {F : set (set T)} {FF : Filter F} (f g : T -> set U) :
  {near F, f =2 g} -> g `@ F `=>` f `@ F.
Admitted.

Lemma cvg_near_const (T U : Type) (f : T -> U) (F : set (set T)) (G : set (set U)) :
  Filter F -> ProperFilter G ->
  (\forall y \near G, \forall x \near F, f x = y) -> f @ F --> G.
Admitted.
Definition globally {T : Type} (A : set T) : set (set T). exact ([set P : set T | forall x, A x -> P x]). Defined.
Arguments globally {T} A _ /.

Lemma globally0 {T : Type} (A : set T) : globally set0 A.
Admitted.

Global Instance globally_filter {T : Type} (A : set T) :
  Filter (globally A).
Admitted.

Global Instance globally_properfilter {T : Type} (A : set T) a :
  infer (A a) -> ProperFilter (globally A).
Admitted.

Section frechet_filter.
Variable T : Type.

Definition frechet_filter := [set S : set T | finite_set (~` S)].

Global Instance frechet_properfilter : infinite_set [set: T] ->
  ProperFilter frechet_filter.
Admitted.

End frechet_filter.

Global Instance frechet_properfilter_nat : ProperFilter (@frechet_filter nat).
Admitted.

Section at_point.

Context {T : Type}.
Definition at_point (a : T) (P : set T) : Prop. exact (P a). Defined.

Global Instance at_point_filter (a : T) : ProperFilter (at_point a).
Admitted.
Typeclasses Opaque at_point.

End at_point.

Global Instance filter_prod_filter T U (F : set (set T)) (G : set (set U)) :
  Filter F -> Filter G -> Filter (filter_prod F G).
Admitted.

Canonical prod_filter_on T U (F : filter_on T) (G : filter_on U) :=
  FilterType (filter_prod F G) (filter_prod_filter _ _).

Global Instance filter_prod_proper {T1 T2 : Type}
  {F : (T1 -> Prop) -> Prop} {G : (T2 -> Prop) -> Prop}
  {FF : ProperFilter F} {FG : ProperFilter G} :
  ProperFilter (filter_prod F G).
Admitted.
Definition filter_prod_proper' := @filter_prod_proper.

Lemma filter_prod1 {T U} {F : set (set T)} {G : set (set U)}
  {FG : Filter G} (P : set T) :
  (\forall x \near F, P x) -> \forall x \near F & _ \near G, P x.
Admitted.
Lemma filter_prod2 {T U} {F : set (set T)} {G : set (set U)}
  {FF : Filter F} (P : set U) :
  (\forall y \near G, P y) -> \forall _ \near F & y \near G, P y.
Admitted.

Program Definition in_filter_prod {T U} {F : set (set T)} {G : set (set U)}
  (P : in_filter F) (Q : in_filter G) : in_filter (filter_prod F G) :=
  @InFilter _ _ (fun x => prop_of P x.1 /\ prop_of Q x.2) _.
Admit Obligations.

Lemma near_pair {T U} {F : set (set T)} {G : set (set U)}
      {FF : Filter F} {FG : Filter G}
      (P : in_filter F) (Q : in_filter G) x :
       prop_of P x.1 -> prop_of Q x.2 -> prop_of (in_filter_prod P Q) x.
Admitted.

Lemma cvg_fst {T U F G} {FG : Filter G} :
  (@fst T U) @ filter_prod F G --> F.
Admitted.

Lemma cvg_snd {T U F G} {FF : Filter F} :
  (@snd T U) @ filter_prod F G --> G.
Admitted.

Lemma near_map {T U} (f : T -> U) (F : set (set T)) (P : set U) :
  (\forall y \near f @ F, P y) = (\forall x \near F, P (f x)).
Admitted.

Lemma near_map2 {T T' U U'} (f : T -> U) (g : T' -> U')
      (F : set (set T)) (G : set (set T')) (P : U -> set U') :
  Filter F -> Filter G ->
  (\forall y \near f @ F & y' \near g @ G, P y y') =
  (\forall x \near F     & x' \near G     , P (f x) (g x')).
Admitted.

Lemma near_mapi {T U} (f : T -> set U) (F : set (set T)) (P : set U) :
  (\forall y \near f `@ F, P y) = (\forall x \near F, exists y, f x y /\ P y).
Admitted.

Lemma filter_pair_set (T T' : Type) (F : set (set T)) (F' : set (set T')) :
   Filter F -> Filter F' ->
   forall (P : set T) (P' : set T') (Q : set (T * T')),
   (forall x x', P x -> P' x' -> Q (x, x')) -> F P /\ F' P' ->
   filter_prod F F' Q.
Admitted.

Lemma filter_pair_near_of (T T' : Type) (F : set (set T)) (F' : set (set T')) :
   Filter F -> Filter F' ->
   forall (P : @in_filter T F) (P' : @in_filter T' F') (Q : set (T * T')),
   (forall x x', prop_of P x -> prop_of P' x' -> Q (x, x')) ->
   filter_prod F F' Q.
Admitted.

Tactic Notation "near=>" ident(x) ident(y) :=
  (apply: filter_pair_near_of => x y ? ?).
Tactic Notation "near" constr(F) "=>" ident(x) ident(y) :=
  apply: (have_near F); near=> x y.

Module Export NearMap.
Definition near_simpl := (@near_simpl, @near_map, @near_mapi, @near_map2).
End NearMap.

Lemma cvg_pair {T U V F} {G : set (set U)} {H : set (set V)}
  {FF : Filter F} {FG : Filter G} {FH : Filter H} (f : T -> U) (g : T -> V) :
  f @ F --> G -> g @ F --> H ->
  (f x, g x) @[x --> F] --> (G, H).
Admitted.

Lemma cvg_comp2 {T U V W}
  {F : set (set T)} {G : set (set U)} {H : set (set V)} {I : set (set W)}
  {FF : Filter F} {FG : Filter G} {FH : Filter H}
  (f : T -> U) (g : T -> V) (h : U -> V -> W) :
  f @ F --> G -> g @ F --> H ->
  h (fst x) (snd x) @[x --> (G, H)] --> I ->
  h (f x) (g x) @[x --> F] --> I.
Admitted.
Arguments cvg_comp2 {T U V W F G H I FF FG FH f g h} _ _ _.
Definition cvg_to_comp_2 := @cvg_comp2.

Section within.
Context {T : Type}.
Implicit Types (D : set T) (F : set (set T)).

Definition within D F (P : set T) := {near F, D `<=` P}.
Arguments within : simpl never.

Lemma near_withinE D F (P : set T) :
  (\forall x \near within D F, P x) = {near F, D `<=` P}.
Admitted.

Lemma withinT F D : Filter F -> within D F D.
Admitted.

Lemma near_withinT F D : Filter F -> \forall x \near within D F, D x.
Admitted.

Lemma cvg_within {F} {FF : Filter F} D : within D F --> F.
Admitted.

Lemma withinET {F} {FF : Filter F} : within setT F = F.
Admitted.

End within.

Global Instance within_filter T D F : Filter F -> Filter (@within T D F).
Admitted.

#[global] Typeclasses Opaque within.

Canonical within_filter_on T D (F : filter_on T) :=
  FilterType (within D F) (within_filter _ _).

Definition subset_filter {T} (F : set (set T)) (D : set T) :=
  [set P : set {x | D x} | F [set x | forall Dx : D x, P (exist _ x Dx)]].
Arguments subset_filter {T} F D _.

Global Instance subset_filter_filter T F (D : set T) :
  Filter F -> Filter (subset_filter F D).
Admitted.
#[global] Typeclasses Opaque subset_filter.

Lemma subset_filter_proper {T F} {FF : Filter F} (D : set T) :
  (forall P, F P -> ~ ~ exists x, D x /\ P x) ->
  ProperFilter (subset_filter F D).
Admitted.

Section NearSet.

Context {T : choiceType} {Y : filteredType T}.
Context (F : set (set Y)) (PF : ProperFilter F).
Definition powerset_filter_from : set (set (set Y)). exact (filter_from
  [set M | [/\ M `<=` F,
    (forall E1 E2, M E1 -> F E2 -> E2 `<=` E1 -> M E2) & M !=set0 ] ]
  id). Defined.

Global Instance powerset_filter_from_filter : ProperFilter powerset_filter_from.
Admitted.

Lemma near_small_set : \forall E \near powerset_filter_from, F E.
Admitted.

Lemma small_set_sub (E : set Y) : F E ->
  \forall E' \near powerset_filter_from, E' `<=` E.
Admitted.

Lemma near_powerset_filter_fromP (P : set Y -> Prop) :
  (forall A B, A `<=` B -> P B -> P A) ->
  (\forall U \near powerset_filter_from, P U) <-> exists2 U, F U & P U.
Admitted.

Lemma powerset_filter_fromP C :
  F C -> powerset_filter_from [set W | F W /\ W `<=` C].
Admitted.

End NearSet.

Section PrincipalFilters.
Definition principal_filter {X : Type} (x : X) : set (set X). exact (globally [set x]). Defined.

Lemma principal_filterP {X} (x : X) (W : set X) : principal_filter x W <-> W x.
Admitted.

Lemma principal_filter_proper {X} (x : X) : ProperFilter (principal_filter x).
Admitted.

Canonical bool_discrete_filter := FilteredType bool bool principal_filter.

End PrincipalFilters.

Module Topological.

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

Definition clone c of phant_id class c := @Pack T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).
Local Coercion base : class_of >-> Filtered.class_of.
Local Coercion mixin : class_of >-> mixin_of.

Definition pack nbhs' (m : @mixin_of T nbhs') :=
  fun bT (b : Filtered.class_of T T) of phant_id (@Filtered.class T bT) b =>
  fun m'   of phant_id m (m' : @mixin_of T (Filtered.nbhs_op b)) =>
  @Pack T (@Class _ b m').

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition pointedType := @Pointed.Pack cT xclass.
Definition filteredType := @Filtered.Pack cT cT xclass.

End ClassDef.

Module Export Exports.

Coercion sort : type >-> Sortclass.
Coercion base : class_of >-> Filtered.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion pointedType : type >-> Pointed.type.
Canonical pointedType.
Coercion filteredType : type >-> Filtered.type.
Canonical filteredType.
Notation topologicalType := type.
Notation TopologicalType T m := (@pack T _ m _ _ idfun _ idfun).
Notation TopologicalMixin := Mixin.
Notation "[ 'topologicalType' 'of' T 'for' cT ]" :=  (@clone T cT _ idfun)
  (at level 0, format "[ 'topologicalType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'topologicalType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'topologicalType'  'of'  T ]") : form_scope.

End Exports.

End Topological.

Export Topological.Exports.

Section Topological1.

Context {T : topologicalType}.

Definition open := Topological.open (Topological.class T).

Definition open_nbhs (p : T) (A : set T) := open A /\ A p.

Definition basis (B : set (set T)) :=
  B `<=` open /\ forall x, filter_from [set U | B U /\ U x] id --> x.

Definition second_countable := exists2 B, countable B & basis B.

Global Instance nbhs_pfilter (p : T) : ProperFilter (nbhs p).
Admitted.
Typeclasses Opaque nbhs.

Lemma nbhs_filter (p : T) : Filter (nbhs p).
Admitted.

Canonical nbhs_filter_on (x : T) := FilterType (nbhs x) (@nbhs_filter x).

Lemma nbhsE (p : T) :
  nbhs p = [set A : set T | exists2 B : set T, open_nbhs p B & B `<=` A].
Admitted.

Lemma open_nbhsE (p : T) (A : set T) : open_nbhs p A = (open A /\ nbhs p A).
Admitted.

Definition interior (A : set T) := (@nbhs _ T)^~ A.

Local Notation "A ^°" := (interior A).

Lemma interior_subset (A : set T) : A^° `<=` A.
Admitted.

Lemma openE : open = [set A : set T | A `<=` A^°].
Admitted.

Lemma nbhs_singleton (p : T) (A : set T) : nbhs p A -> A p.
Admitted.

Lemma nbhs_interior (p : T) (A : set T) : nbhs p A -> nbhs p A^°.
Admitted.

Lemma open0 : open set0.
Admitted.

Lemma openT : open setT.
Admitted.

Lemma openI (A B : set T) : open A -> open B -> open (A `&` B).
Admitted.

Lemma bigcup_open (I : Type) (D : set I) (f : I -> set T) :
  (forall i, D i -> open (f i)) -> open (\bigcup_(i in D) f i).
Admitted.

Lemma openU (A B : set T) : open A -> open B -> open (A `|` B).
Admitted.

Lemma open_subsetE (A B : set T) : open A -> (A `<=` B) = (A `<=` B^°).
Admitted.

Lemma open_interior (A : set T) : open A^°.
Admitted.

Lemma interior_bigcup I (D : set I) (f : I -> set T) :
  \bigcup_(i in D) (f i)^° `<=` (\bigcup_(i in D) f i)^°.
Admitted.

Lemma open_nbhsT (p : T) : open_nbhs p setT.
Admitted.

Lemma open_nbhsI (p : T) (A B : set T) :
  open_nbhs p A -> open_nbhs p B -> open_nbhs p (A `&` B).
Admitted.

Lemma open_nbhs_nbhs (p : T) (A : set T) : open_nbhs p A -> nbhs p A.
Admitted.

Lemma interiorI (A B:set T): (A `&` B)^° = A^° `&` B^°.
Admitted.

End Topological1.

#[global] Hint Extern 0 (Filter (nbhs _)) =>
  solve [apply: nbhs_filter] : typeclass_instances.
#[global] Hint Extern 0 (ProperFilter (nbhs _)) =>
  solve [apply: nbhs_pfilter] : typeclass_instances.

Notation "A ^°" := (interior A) : classical_set_scope.

Notation continuous f := (forall x, f%function @ x --> f%function x).

Lemma near_fun (T T' : topologicalType) (f : T -> T') (x : T) (P : T' -> Prop) :
    {for x, continuous f} ->
  (\forall y \near f x, P y) -> (\near x, P (f x)).
Admitted.
Arguments near_fun {T T'} f x.

Lemma continuousP (S T : topologicalType) (f : S -> T) :
  continuous f <-> forall A, open A -> open (f @^-1` A).
Admitted.

Lemma continuous_comp (R S T : topologicalType) (f : R -> S) (g : S -> T) x :
  {for x, continuous f} -> {for (f x), continuous g} ->
  {for x, continuous (g \o f)}.
Admitted.

Lemma open_comp  {T U : topologicalType} (f : T -> U) (D : set U) :
  {in f @^-1` D, continuous f} -> open D -> open (f @^-1` D).
Admitted.

Lemma cvg_fmap {T: topologicalType} {U : topologicalType}
  (F : set (set T)) x (f : T -> U) :
   {for x, continuous f} -> F --> x -> f @ F --> f x.
Admitted.

Lemma near_join (T : topologicalType) (x : T) (P : set T) :
  (\near x, P x) -> \near x, \near x, P x.
Admitted.

Lemma near_bind (T : topologicalType) (P Q : set T) (x : T) :
  (\near x, (\near x, P x) -> Q x) -> (\near x, P x) -> \near x, Q x.
Admitted.

Lemma continuous_cvg {T : Type} {V U : topologicalType}
  (F : set (set T)) (FF : Filter F)
  (f : T -> V) (h : V -> U) (a : V) :
  {for a, continuous h} ->
  f @ F --> a -> (h \o f) @ F --> h a.
Admitted.

Lemma continuous_is_cvg {T : Type} {V U : topologicalType} [F : set (set T)]
  (FF : Filter F) (f : T -> V) (h : V -> U) :
  (forall l, f x @[x --> F] --> l -> {for l, continuous h}) ->
  cvg (f x @[x --> F]) -> cvg ((h \o f) x @[x --> F]).
Admitted.

Lemma continuous2_cvg {T : Type} {V W U : topologicalType}
  (F : set (set T)) (FF : Filter F)
  (f : T -> V) (g : T -> W) (h : V -> W -> U) (a : V) (b : W) :
  h z.1 z.2 @[z --> (a, b)] --> h a b ->
  f @ F --> a -> g @ F --> b -> (fun x => h (f x) (g x)) @ F --> h a b.
Admitted.

Lemma cvg_near_cst (T : Type) (U : topologicalType)
  (l : U) (f : T -> U) (F : set (set T)) {FF : Filter F} :
  (\forall x \near F, f x = l) -> f @ F --> l.
Admitted.
Arguments cvg_near_cst {T U} l {f F FF}.

Lemma is_cvg_near_cst (T : Type) (U : topologicalType)
  (l : U) (f : T -> U) (F : set (set T)) {FF : Filter F} :
  (\forall x \near F, f x = l) -> cvg (f @ F).
Admitted.
Arguments is_cvg_near_cst {T U} l {f F FF}.

Lemma near_cst_continuous (T U : topologicalType)
  (l : U) (f : T -> U) (x : T) :
  (\forall y \near x, f y = l) -> {for x, continuous f}.
Admitted.
Arguments near_cst_continuous {T U} l [f x].

Lemma cvg_cst (U : topologicalType) (x : U) (T : Type)
    (F : set (set T)) {FF : Filter F} :
  (fun _ : T => x) @ F --> x.
Admitted.
Arguments cvg_cst {U} x {T F FF}.
#[global] Hint Resolve cvg_cst : core.

Lemma is_cvg_cst (U : topologicalType) (x : U) (T : Type)
  (F : set (set T)) {FF : Filter F} :
  cvg ((fun _ : T => x) @ F).
Admitted.
Arguments is_cvg_cst {U} x {T F FF}.
#[global] Hint Resolve is_cvg_cst : core.

Lemma cst_continuous {T U : topologicalType} (x : U) :
  continuous (fun _ : T => x).
Admitted.

Section within_topologicalType.
Context {T : topologicalType} (A : set T).
Implicit Types B : set T.

Lemma within_nbhsW (x : T) : A x -> within A (nbhs x) `=>` globally A.
Admitted.

Definition locally_of (P : set (set T) -> Prop) of phantom Prop (P (globally A))
  := forall x, A x -> P (within A (nbhs x)).
Local Notation "[ 'locally' P ]" := (@locally_of _ _ _ (Phantom _ P)).

Lemma within_interior (x : T) : A^° x -> within A (nbhs x) = nbhs x.
Admitted.

Lemma within_subset B F : Filter F -> A `<=` B -> within A F `=>` within B F.
Admitted.

Lemma withinE F : Filter F ->
  within A F = [set U | exists2 V, F V & U `&` A = V `&` A].
Admitted.

Lemma fmap_within_eq {S : topologicalType} (F : set (set T)) (f g : T -> S) :
  Filter F -> {in A, f =1 g} -> f @ within A F --> g @ within A F.
Admitted.

End within_topologicalType.

Notation "[ 'locally' P ]" := (@locally_of _ _ _ (Phantom _ P)).

Section TopologyOfFilter.

Context {T : Type} {nbhs' : T -> set (set T)}.
Hypothesis (nbhs'_filter : forall p : T, ProperFilter (nbhs' p)).
Hypothesis (nbhs'_singleton : forall (p : T) (A : set T), nbhs' p A -> A p).
Hypothesis (nbhs'_nbhs' : forall (p : T) (A : set T), nbhs' p A -> nbhs' p (nbhs'^~ A)).

Definition open_of_nbhs := [set A : set T | A `<=` nbhs'^~ A].

Program Definition topologyOfFilterMixin : Topological.mixin_of nbhs' :=
  @Topological.Mixin T nbhs' open_of_nbhs _ _ _.
Admit Obligations.
Admit Obligations.

End TopologyOfFilter.

Section TopologyOfOpen.

Variable (T : Type) (op : set T -> Prop).
Hypothesis (opT : op setT).
Hypothesis (opI : forall (A B : set T), op A -> op B -> op (A `&` B)).
Hypothesis (op_bigU : forall (I : Type) (f : I -> set T),
  (forall i, op (f i)) -> op (\bigcup_i f i)).

Definition nbhs_of_open (p : T) (A : set T) :=
  exists B, [/\ op B, B p & B `<=` A].

Program Definition topologyOfOpenMixin : Topological.mixin_of nbhs_of_open :=
  @Topological.Mixin T nbhs_of_open op _ _ _.
Admit Obligations.
Admit Obligations.
Admit Obligations.

End TopologyOfOpen.

Section TopologyOfBase.

Definition open_from I T (D : set I) (b : I -> set T) :=
  [set \bigcup_(i in D') b i | D' in subset^~ D].

Lemma open_fromT I T (D : set I) (b : I -> set T) :
  \bigcup_(i in D) b i = setT -> open_from D b setT.
Admitted.

Variable (I : pointedType) (T : Type) (D : set I) (b : I -> (set T)).
Hypothesis (b_cover : \bigcup_(i in D) b i = setT).
Hypothesis (b_join : forall i j t, D i -> D j -> b i t -> b j t ->
  exists k, [/\ D k, b k t & b k `<=` b i `&` b j]).

Program Definition topologyOfBaseMixin :=
  @topologyOfOpenMixin _ (open_from D b) (open_fromT b_cover) _ _.
Admit Obligations.
Admit Obligations.

End TopologyOfBase.

Section filter_supremums.

Global Instance smallest_filter_filter {T : Type} (F : set (set T)) :
  Filter (smallest Filter F).
Admitted.

Fixpoint filterI_iter {T : Type} (F : set (set T)) (n : nat) :=
  if n is m.+1
  then [set P `&` Q |
    P in filterI_iter F m & Q in filterI_iter F m]
  else setT |` F.

Lemma filterI_iter_sub {T : Type} (F : set (set T)) :
  {homo filterI_iter F : i j / (i <= j)%N >-> i `<=` j}.
Admitted.

Lemma filterI_iterE {T : Type} (F : set (set T)) :
  smallest Filter F = filter_from (\bigcup_n (filterI_iter F n)) id.
Admitted.

Definition finI_from (I : choiceType) T (D : set I) (f : I -> set T) :=
  [set \bigcap_(i in [set` D']) f i |
    D' in [set A : {fset I} | {subset A <= D}]].

Lemma finI_from_cover (I : choiceType) T (D : set I) (f : I -> set T) :
  \bigcup_(A in finI_from D f) A = setT.
Admitted.

Lemma finI_from1 (I : choiceType) T (D : set I) (f : I -> set T) i :
  D i -> finI_from D f (f i).
Admitted.

Lemma finI_from_countable (I : pointedType) T (D : set I) (f : I -> set T) :
  countable D -> countable (finI_from D f).
Admitted.

Lemma finI_fromI {I : choiceType} T D (f : I -> set T) A B :
  finI_from D f A -> finI_from D f B -> finI_from D f (A `&` B) .
Admitted.

Lemma filterI_iter_finI {I : choiceType} T D (f : I -> set T) :
  finI_from D f = \bigcup_n (filterI_iter (f @` D) n).
Admitted.

Lemma smallest_filter_finI {T : choiceType} (D : set T) f :
  filter_from (finI_from D f) id = smallest (@Filter T) (f @` D).
Admitted.

End filter_supremums.

Section TopologyOfSubbase.

Variable (I : pointedType) (T : Type) (D : set I) (b : I -> set T).

Program Definition topologyOfSubbaseMixin :=
  @topologyOfBaseMixin _ _ (finI_from D b) id (finI_from_cover D b) _.
Admit Obligations.

End TopologyOfSubbase.

Section nat_topologicalType.
Let D : set nat. exact (setT). Defined.
Let b : nat -> set nat. exact (fun i => [set i]). Defined.
Let bT : \bigcup_(i in D) b i = setT.
Admitted.

Let bD : forall i j t, D i -> D j -> b i t -> b j t ->
  exists k, [/\ D k, b k t & b k `<=` b i `&` b j].
Admitted.

Definition nat_topologicalTypeMixin := topologyOfBaseMixin bT bD.
Canonical nat_filteredType := FilteredType nat nat (nbhs_of_open (open_from D b)).
Canonical nat_topologicalType := TopologicalType nat nat_topologicalTypeMixin.

End nat_topologicalType.

Definition eventually := filter_from setT (fun N => [set n | (N <= n)%N]).
Notation "'\oo'" := eventually : classical_set_scope.

Canonical eventually_filter_source X :=
   @Filtered.Source X _ nat (fun f => f @ \oo).

Global Instance eventually_filter : ProperFilter eventually.
Admitted.

Canonical eventually_filterType := FilterType eventually _.
Canonical eventually_pfilterType := PFilterType eventually (filter_not_empty _).

Lemma nbhs_infty_gt N : \forall n \near \oo, (N < n)%N.
Admitted.
#[global] Hint Resolve nbhs_infty_gt : core.

Lemma nbhs_infty_ge N : \forall n \near \oo, (N <= n)%N.
Admitted.

Lemma cvg_addnl N : addn N @ \oo --> \oo.
Admitted.

Lemma cvg_addnr N : addn^~ N --> \oo.
Admitted.

Lemma cvg_subnr N : subn^~ N --> \oo.
Admitted.

Lemma cvg_mulnl N : (N > 0)%N -> muln N --> \oo.
Admitted.

Lemma cvg_mulnr N :(N > 0)%N -> muln^~ N --> \oo.
Admitted.

Lemma cvg_divnr N : (N > 0)%N -> divn^~ N --> \oo.
Admitted.

Lemma near_inftyS (P : set nat) :
  (\forall x \near \oo, P (S x)) -> (\forall x \near \oo, P x).
Admitted.

Section infty_nat.
Local Open Scope nat_scope.

Let cvgnyP {F : set (set nat)} {FF : Filter F} : [<->
  F --> \oo;
  forall A, \forall x \near F, A <= x;
  forall A, \forall x \near F, A < x;
  \forall A \near \oo, \forall x \near F, A < x;
  \forall A \near \oo, \forall x \near F, A <= x ].
Admitted.

Section map.

Context {I : Type} {F : set (set I)} {FF : Filter F} (f : I -> nat).

Lemma cvgnyPge :
  f @ F --> \oo <-> forall A, \forall x \near F, A <= f x.
Admitted.

Lemma cvgnyPgt :
  f @ F --> \oo <-> forall A, \forall x \near F, A < f x.
Admitted.

Lemma cvgnyPgty :
  f @ F --> \oo <-> \forall A \near \oo, \forall x \near F, A < f x.
Admitted.

Lemma cvgnyPgey :
  f @ F --> \oo <-> \forall A \near \oo, \forall x \near F, A <= f x.
Admitted.

End map.

End infty_nat.

Section Prod_Topology.

Context {T U : topologicalType}.

Let prod_nbhs (p : T * U) := filter_prod (nbhs p.1) (nbhs p.2).

Lemma prod_nbhs_filter (p : T * U) : ProperFilter (prod_nbhs p).
Admitted.

Lemma prod_nbhs_singleton (p : T * U) (A : set (T * U)) : prod_nbhs p A -> A p.
Admitted.

Lemma prod_nbhs_nbhs (p : T * U) (A : set (T * U)) :
  prod_nbhs p A -> prod_nbhs p (prod_nbhs^~ A).
Admitted.

Definition prod_topologicalTypeMixin :=
  topologyOfFilterMixin prod_nbhs_filter prod_nbhs_singleton prod_nbhs_nbhs.

Canonical prod_topologicalType :=
  TopologicalType (T * U) prod_topologicalTypeMixin.

End Prod_Topology.

Section matrix_Topology.

Variables (m n : nat) (T : topologicalType).

Implicit Types M : 'M[T]_(m, n).

Lemma mx_nbhs_filter M : ProperFilter (nbhs M).
Admitted.

Lemma mx_nbhs_singleton M (A : set 'M[T]_(m, n)) : nbhs M A -> A M.
Admitted.

Lemma mx_nbhs_nbhs M (A : set 'M[T]_(m, n)) : nbhs M A -> nbhs M (nbhs^~ A).
Admitted.

Definition matrix_topologicalTypeMixin :=
  topologyOfFilterMixin mx_nbhs_filter mx_nbhs_singleton mx_nbhs_nbhs.

Canonical matrix_topologicalType :=
  TopologicalType 'M[T]_(m, n) matrix_topologicalTypeMixin.

End matrix_Topology.

Section Weak_Topology.

Variable (S : pointedType) (T : topologicalType) (f : S -> T).

Definition wopen := [set f @^-1` A | A in open].

Lemma wopT : wopen setT.
Admitted.

Lemma wopI (A B : set S) : wopen A -> wopen B -> wopen (A `&` B).
Admitted.

Lemma wop_bigU (I : Type) (g : I -> set S) :
  (forall i, wopen (g i)) -> wopen (\bigcup_i g i).
Admitted.

Definition weak_topologicalTypeMixin := topologyOfOpenMixin wopT wopI wop_bigU.

Let S_filteredClass := Filtered.Class (Pointed.class S) (nbhs_of_open wopen).
Definition weak_topologicalType :=
  Topological.Pack (@Topological.Class _ S_filteredClass
    weak_topologicalTypeMixin).

Lemma weak_continuous : continuous (f : weak_topologicalType -> T).
Admitted.

Lemma cvg_image (F : set (set S)) (s : S) :
  Filter F -> f @` setT = setT ->
  F --> (s : weak_topologicalType) <-> [set f @` A | A in F] --> f s.
Admitted.

End Weak_Topology.

Section Sup_Topology.

Variable (T : pointedType) (I : Type) (Tc : I -> Topological.class_of T).

Let TS := fun i => Topological.Pack (Tc i).

Definition sup_subbase := \bigcup_i (@open (TS i) : set (set T)).

Definition sup_topologicalTypeMixin := topologyOfSubbaseMixin sup_subbase id.

Definition sup_topologicalType :=
  Topological.Pack (@Topological.Class _ (Filtered.Class (Pointed.class T) _)
  sup_topologicalTypeMixin).

Lemma cvg_sup (F : set (set T)) (t : T) :
  Filter F -> F --> (t : sup_topologicalType) <-> forall i, F --> (t : TS i).
Admitted.

End Sup_Topology.

Section Product_Topology.

Variable (I : Type) (T : I -> topologicalType).

Definition product_topologicalType :=
  sup_topologicalType (fun i => Topological.class
    (weak_topologicalType (fun f : dep_arrow_pointedType T => f i))).

End Product_Topology.

Definition dnbhs {T : topologicalType} (x : T) :=
  within (fun y => y != x) (nbhs x).
Notation "x ^'" := (dnbhs x) : classical_set_scope.

Lemma dnbhsE (T : topologicalType) (x : T) : nbhs x = x^' `&` at_point x.
Admitted.

Global Instance dnbhs_filter {T : topologicalType} (x : T) : Filter x^'.
Admitted.
#[global] Typeclasses Opaque dnbhs.

Canonical dnbhs_filter_on (T : topologicalType)  (x : T) :=
  FilterType x^' (dnbhs_filter _).

Lemma cvg_fmap2 (T U : Type) (f : T -> U):
  forall (F G : set (set T)), G `=>` F -> f @ G `=>` f @ F.
Admitted.

Lemma cvg_within_filter {T U} {f : T -> U} (F : set (set T)) {FF : (Filter F) }
  (G : set (set U)) : forall (D : set T), (f @ F) --> G -> (f @ within D F) --> G.
Admitted.

Lemma cvg_app_within {T} {U : topologicalType} (f : T -> U) (F : set (set T))
  (D : set T): Filter F -> cvg (f @ F) -> cvg (f @ within D F).
Admitted.

Lemma nbhs_dnbhs {T : topologicalType} (x : T) : x^' `=>` nbhs x.
Admitted.

Lemma meets_openr {T : topologicalType} (F : set (set T)) (x : T) :
  F `#` nbhs x = F `#` open_nbhs x.
Admitted.

Lemma meets_openl {T : topologicalType} (F : set (set T)) (x : T) :
  nbhs x `#` F = open_nbhs x `#` F.
Admitted.

Lemma meets_globallyl T (A : set T) G :
  globally A `#` G = forall B, G B -> A `&` B !=set0.
Admitted.

Lemma meets_globallyr T F (B : set T) :
  F `#` globally B = forall A, F A -> A `&` B !=set0.
Admitted.

Lemma meetsxx T (F : set (set T)) (FF : Filter F) : F `#` F = ~ (F set0).
Admitted.

Lemma proper_meetsxx T (F : set (set T)) (FF : ProperFilter F) : F `#` F.
Admitted.

Section Closed.

Context {T : topologicalType}.

Definition closure (A : set T) :=
  [set p : T | forall B, nbhs p B -> A `&` B !=set0].

Lemma closure0 : closure set0 = set0 :> set T.
Admitted.

Lemma closureEnbhs A : closure A = [set p | globally A `#` nbhs p].
Admitted.

Lemma closureEonbhs A : closure A = [set p | globally A `#` open_nbhs p].
Admitted.

Lemma subset_closure (A : set T) : A `<=` closure A.
Admitted.

Lemma closureI (A B : set T) : closure (A `&` B) `<=` closure A `&` closure B.
Admitted.

Definition limit_point E := [set t : T |
  forall U, nbhs t U -> exists y, [/\ y != t, E y & U y]].

Lemma limit_pointEnbhs E :
  limit_point E = [set p | globally (E `\ p) `#` nbhs p].
Admitted.

Lemma limit_pointEonbhs E :
  limit_point E = [set p | globally (E `\ p) `#` open_nbhs p].
Admitted.

Lemma subset_limit_point E : limit_point E `<=` closure E.
Admitted.

Lemma closure_limit_point E : closure E = E `|` limit_point E.
Admitted.

Definition closed (D : set T) := closure D `<=` D.

Lemma open_closedC (D : set T) : open D -> closed (~` D).
Admitted.

Lemma closed_bigI {I} (D : set I) (f : I -> set T) :
  (forall i, D i -> closed (f i)) -> closed (\bigcap_(i in D) f i).
Admitted.

Lemma closedI (D E : set T) : closed D -> closed E -> closed (D `&` E).
Admitted.

Lemma closedT : closed setT.
Admitted.

Lemma closed0 : closed set0.
Admitted.

Lemma closedE : closed = [set A : set T | forall p, ~ (\near p, ~ A p) -> A p].
Admitted.

Lemma closed_openC (D : set T) : closed D -> open (~` D).
Admitted.

Lemma closedC (D : set T) : closed (~` D) = open D.
Admitted.

Lemma openC (D : set T) : open (~`D) = closed (D).
Admitted.

Lemma closed_closure (A : set T) : closed (closure A).
Admitted.

End Closed.

Lemma closed_comp {T U : topologicalType} (f : T -> U) (D : set U) :
  {in ~` f @^-1` D, continuous f} -> closed D -> closed (f @^-1` D).
Admitted.

Lemma closed_cvg {T} {V : topologicalType} {F} {FF : ProperFilter F}
    (u_ : T -> V) (A : V -> Prop) :

    closed A -> (\forall n \near F, A (u_ n)) ->
  forall l, u_ @ F --> l -> A l.
Admitted.
Arguments closed_cvg {T V F FF u_} _ _ _ _ _.

Lemma continuous_closedP (S T : topologicalType) (f : S -> T) :
  continuous f <-> forall A, closed A -> closed (f @^-1` A).
Admitted.

Lemma closedU (T : topologicalType) (D E : set T) :
  closed D -> closed E -> closed (D `|` E).
Admitted.

Lemma closed_bigsetU (T : topologicalType) (I : eqType) (s : seq I)
    (F : I -> set T) : (forall x, x \in s -> closed (F x)) ->
  closed (\big[setU/set0]_(x <- s) F x).
Admitted.

Lemma closed_bigcup (T : topologicalType) (I : choiceType) (A : set I)
    (F : I -> set T) :
    finite_set A -> (forall i, A i -> closed (F i)) ->
  closed (\bigcup_(i in A) F i).
Admitted.

Section closure_lemmas.
Variable T : topologicalType.
Implicit Types E A B U : set T.

Lemma closure_subset A B : A `<=` B -> closure A `<=` closure B.
Admitted.

Lemma closureE A : closure A = smallest closed A.
Admitted.

Lemma closureC E :
  ~` closure E = \bigcup_(x in [set U | open U /\ U `<=` ~` E]) x.
Admitted.

Lemma closure_id E : closed E <-> E = closure E.
Admitted.

End closure_lemmas.

Section Compact.

Context {T : topologicalType}.

Definition cluster (F : set (set T)) := [set p : T | F `#` nbhs p].

Lemma cluster_nbhs t : cluster (nbhs t) t.
Admitted.

Lemma clusterEonbhs F : cluster F = [set p | F `#` open_nbhs p].
Admitted.

Lemma clusterE F : cluster F = \bigcap_(A in F) (closure A).
Admitted.

Lemma closureEcluster E : closure E = cluster (globally E).
Admitted.

Lemma cvg_cluster F G : F --> G -> cluster F `<=` cluster G.
Admitted.

Lemma cluster_cvgE F :
  Filter F ->
  cluster F = [set p | exists2 G, ProperFilter G & G --> p /\ F `<=` G].
Admitted.

Lemma closureEcvg (E : set T):
  closure E =
  [set p | exists2 G, ProperFilter G & G --> p /\ globally E `<=` G].
Admitted.

Definition compact A := forall (F : set (set T)),
  ProperFilter F -> F A -> A `&` cluster F !=set0.

Lemma compact0 : compact set0.
Admitted.

Lemma subclosed_compact (A B : set T) :
  closed A -> compact B -> A `<=` B -> compact A.
Admitted.

Definition hausdorff_space := forall p q : T, cluster (nbhs p) q -> p = q.

Typeclasses Opaque within.
Global Instance within_nbhs_proper (A : set T) p :
  infer (closure A p) -> ProperFilter (within A (nbhs p)).
Admitted.

Lemma compact_closed (A : set T) : hausdorff_space -> compact A -> closed A.
Admitted.

Lemma compact_set1 (x : T) : compact [set x].
Admitted.

End Compact.
Arguments hausdorff_space : clear implicits.

Section ClopenSets.
Implicit Type T : topologicalType.

Definition clopen {T} (A : set T) := open A /\ closed A.

Lemma clopenI {T} (A B : set T) : clopen A -> clopen B -> clopen (A `&` B).
Admitted.

Lemma clopenU {T} (A B : set T) : clopen A -> clopen B -> clopen (A `|` B).
Admitted.

Lemma clopenC {T} (A B : set T) : clopen A -> clopen (~`A).
Admitted.

Lemma clopen0 {T} : @clopen T set0.
Admitted.

Lemma clopenT {T} : clopen [set: T].
Admitted.

Lemma clopen_comp {T U : topologicalType} (f : T -> U) (A : set U) :
 clopen A -> continuous f -> clopen (f @^-1` A).
Admitted.

End ClopenSets.

Section near_covering.
Context {X : topologicalType}.

Definition near_covering (K : set X) :=
  forall (I : Type) (F : set (set I)) (P : I -> X -> Prop),
  Filter F ->
  (forall x, K x -> \forall x' \near x & i \near F, P i x') ->
  \near F, K `<=` P F.

Let near_covering_compact : near_covering `<=` compact.
Admitted.

Let compact_near_covering : compact `<=` near_covering.
Admitted.

Lemma compact_near_coveringP A : compact A <-> near_covering A.
Admitted.

End near_covering.

Section Tychonoff.

Class UltraFilter T (F : set (set T)) := {
  ultra_proper :> ProperFilter F ;
  max_filter : forall G : set (set T), ProperFilter G -> F `<=` G -> G = F
}.

Lemma ultra_cvg_clusterE (T : topologicalType) (F : set (set T)) :
  UltraFilter F -> cluster F = [set p | F --> p].
Admitted.

Lemma ultraFilterLemma T (F : set (set T)) :
  ProperFilter F -> exists G, UltraFilter G /\ F `<=` G.
Admitted.

Lemma compact_ultra (T : topologicalType) :
  compact = [set A | forall F : set (set T),
  UltraFilter F -> F A -> A `&` [set p | F --> p] !=set0].
Admitted.

Lemma filter_image (T U : Type) (f : T -> U) (F : set (set T)) :
  Filter F -> f @` setT = setT -> Filter [set f @` A | A in F].
Admitted.

Lemma proper_image (T U : Type) (f : T -> U) (F : set (set T)) :
  ProperFilter F -> f @` setT = setT -> ProperFilter [set f @` A | A in F].
Admitted.

Lemma principal_filter_ultra {T : Type} (x : T) :
  UltraFilter (principal_filter x).
Admitted.

Lemma in_ultra_setVsetC T (F : set (set T)) (A : set T) :
  UltraFilter F -> F A \/ F (~` A).
Admitted.

Lemma ultra_image (T U : Type) (f : T -> U) (F : set (set T)) :
  UltraFilter F -> f @` setT = setT -> UltraFilter [set f @` A | A in F].
Admitted.

Lemma tychonoff (I : eqType) (T : I -> topologicalType)
  (A : forall i, set (T i)) :
  (forall i, compact (A i)) ->
  @compact (product_topologicalType T)
    [set f : forall i, T i | forall i, A i (f i)].
Admitted.

End Tychonoff.

Lemma compact_cluster_set1 {T : topologicalType} (x : T) F V :
  hausdorff_space T -> compact V -> nbhs x V ->
  ProperFilter F -> F V -> cluster F = [set x] -> F --> x.
Admitted.

Section Precompact.

Context {X : topologicalType}.

Lemma compactU (A B : set X) : compact A -> compact B -> compact (A `|` B).
Admitted.

Lemma bigsetU_compact I (F : I -> set X) (s : seq I) (P : pred I) :
    (forall i, P i -> compact (F i)) ->
  compact (\big[setU/set0]_(i <- s | P i) F i).
Admitted.

Definition compact_near (F : set (set X)) :=
  exists2 U, F U & compact U /\ closed U.

Definition precompact (C : set X) := compact_near (globally C).

Lemma precompactE (C : set X) : precompact C = compact (closure C).
Admitted.

Lemma precompact_subset (A B : set X) :
  A `<=` B -> precompact B -> precompact A.
Admitted.

Lemma compact_precompact (A B : set X) :
  hausdorff_space X -> compact A -> precompact A.
Admitted.

Lemma precompact_closed (A : set X) : closed A -> precompact A = compact A.
Admitted.

Definition locally_compact (A : set X) := [locally precompact A].

End Precompact.

Section product_spaces.
Context {I : eqType} {K : I -> topologicalType}.

Let PK := product_topologicalType K.

Lemma proj_continuous i : continuous (proj i : PK -> K i).
Admitted.

Lemma dfwith_continuous g (i : I) : continuous (dfwith g _ : K i -> PK).
Admitted.

Lemma proj_open i (A : set PK) : open A -> open (proj i @` A).
Admitted.

Lemma hausdorff_product :
  (forall x, hausdorff_space (K x)) -> hausdorff_space PK.
Admitted.

End product_spaces.

Definition finI (I : choiceType) T (D : set I) (f : I -> set T) :=
  forall D' : {fset I}, {subset D' <= D} ->
  \bigcap_(i in [set i | i \in D']) f i !=set0.

Lemma finI_filter (I : choiceType) T (D : set I) (f : I -> set T) :
  finI D f -> ProperFilter (filter_from (finI_from D f) id).
Admitted.

Lemma filter_finI (T : pointedType) (F : set (set T)) (D : set (set T))
  (f : set T -> set T) :
  ProperFilter F -> (forall A, D A -> F (f A)) -> finI D f.
Admitted.

Definition finite_subset_cover (I : choiceType) (D : set I)
    U (F : I -> set U) (A : set U) :=
  exists2 D' : {fset I}, {subset D' <= D} & A `<=` cover [set` D'] F.

Section Covers.

Variable T : topologicalType.

Definition cover_compact (A : set T) :=
  forall (I : choiceType) (D : set I) (f : I -> set T),
  (forall i, D i -> open (f i)) -> A `<=` cover D f ->
  finite_subset_cover D f A.

Definition open_fam_of (A : set T) I (D : set I) (f : I -> set T) :=
  exists2 g : I -> set T, (forall i, D i -> open (g i)) &
    forall i, D i -> f i = A `&` g i.

Lemma cover_compactE : cover_compact =
  [set A | forall (I : choiceType) (D : set I) (f : I -> set T),
    open_fam_of A D f ->
      A `<=` cover D f -> finite_subset_cover D f A].
Admitted.

Definition closed_fam_of (A : set T) I (D : set I) (f : I -> set T) :=
  exists2 g : I -> set T, (forall i, D i -> closed (g i)) &
    forall i, D i -> f i = A `&` g i.

Lemma compact_In0 :
  compact = [set A | forall (I : choiceType) (D : set I) (f : I -> set T),
    closed_fam_of A D f -> finI D f -> \bigcap_(i in D) f i !=set0].
Admitted.

Lemma compact_cover : compact = cover_compact.
Admitted.

End Covers.

Lemma finite_compact {X : topologicalType} (A : set X) :
  finite_set A -> compact A.
Admitted.

Lemma clopen_countable {T : topologicalType}:
  compact [set: T] -> @second_countable T -> countable (@clopen T).
Admitted.

Section separated_topologicalType.
Variable (T : topologicalType).
Implicit Types x y : T.

Local Open Scope classical_set_scope.

Definition kolmogorov_space := forall x y, x != y ->
  exists A : set T, (A \in nbhs x /\ y \in ~` A) \/ (A \in nbhs y /\ x \in ~` A).

Definition accessible_space := forall x y, x != y ->
  exists A : set T, open A /\ x \in A /\ y \in ~` A.

Lemma accessible_closed_set1 : accessible_space -> forall x, closed [set x].
Admitted.

Lemma accessible_kolmogorov : accessible_space -> kolmogorov_space.
Admitted.

Lemma accessible_finite_set_closed :
  accessible_space <-> forall A : set T, finite_set A -> closed A.
Admitted.
Definition close x y : Prop. exact (forall M, open_nbhs y M -> closure M x). Defined.

Lemma closeEnbhs x : close x = cluster (nbhs x).
Admitted.

Lemma closeEonbhs x : close x = [set y | open_nbhs x `#` open_nbhs y].
Admitted.

Lemma close_sym x y : close x y -> close y x.
Admitted.

Lemma cvg_close {F} {FF : ProperFilter F} x y : F --> x -> F --> y -> close x y.
Admitted.

Lemma close_refl x : close x x.
Admitted.
Hint Resolve close_refl : core.

Lemma close_cvg (F1 F2 : set (set T)) {FF2 : ProperFilter F2} :
  F1 --> F2 -> F2 --> F1 -> close (lim F1) (lim F2).
Admitted.

Lemma cvgx_close x y : x --> y -> close x y.
Admitted.

Lemma cvgi_close T' {F} {FF : ProperFilter F} (f : T' -> set T) (l l' : T) :
  {near F, is_fun f} -> f `@ F --> l -> f `@ F --> l' -> close l l'.
Admitted.
Definition cvg_toi_locally_close := @cvgi_close.

Lemma open_hausdorff : hausdorff_space T =
  forall x y, x != y ->
    exists2 AB, (x \in AB.1 /\ y \in AB.2) &
                [/\ open AB.1, open AB.2 & AB.1 `&` AB.2 == set0].
Admitted.

Definition hausdorff_accessible : hausdorff_space T -> accessible_space.
Admitted.

Hypothesis sep : hausdorff_space T.

Lemma closeE x y : close x y = (x = y).
Admitted.

Lemma close_eq x y : close x y -> x = y.
Admitted.

Lemma cvg_unique {F} {FF : ProperFilter F} : is_subset1 [set x : T | F --> x].
Admitted.

Lemma cvg_eq x y : x --> y -> x = y.
Admitted.

Lemma lim_id x : lim x = x.
Admitted.

Lemma cvg_lim {U : Type} {F} {FF : ProperFilter F} (f : U -> T) (l : T) :
  f @ F --> l -> lim (f @ F) = l.
Admitted.

Lemma lim_near_cst {U} {F} {FF : ProperFilter F} (l : T) (f : U -> T) :
   (\forall x \near F, f x = l) -> lim (f @ F) = l.
Admitted.

Lemma lim_cst {U} {F} {FF : ProperFilter F} (k : T) :
   lim ((fun _ : U => k) @ F) = k.
Admitted.

Lemma cvgi_unique {U : Type} {F} {FF : ProperFilter F} (f : U -> set T) :
  {near F, is_fun f} -> is_subset1 [set x : T | f `@ F --> x].
Admitted.

Lemma cvgi_lim {U} {F} {FF : ProperFilter F} (f : U -> T -> Prop) (l : T) :
  F (fun x : U => is_subset1 (f x)) ->
  f `@ F --> l -> lim (f `@ F) = l.
Admitted.

End separated_topologicalType.

#[deprecated(since="mathcomp-analysis 0.6.0", note="renamed to `cvg_lim`")]
Notation cvg_map_lim := cvg_lim.
#[deprecated(since="mathcomp-analysis 0.6.0", note="renamed to `cvgi_lim`")]
Notation cvgi_map_lim := cvgi_lim.

Section connected_sets.
Variable T : topologicalType.
Implicit Types A B C D : set T.

Definition connected A :=
  forall B, B !=set0 -> (exists2 C, open C & B = A `&` C) ->
  (exists2 C, closed C & B = A `&` C) -> B = A.

Lemma connected0 : connected (@set0 T).
Admitted.

Definition separated A B :=
  (closure A) `&` B = set0 /\ A `&` (closure B) = set0.

Lemma separatedC A B : separated A B = separated B A.
Admitted.

Lemma separated_disjoint A B : separated A B -> A `&` B = set0.
Admitted.

Lemma connectedPn A : ~ connected A <->
  exists E : bool -> set T, [/\ forall b, E b !=set0,
    A = E false `|` E true & separated (E false) (E true)].
Admitted.

Lemma connectedP A : connected A <->
  forall E : bool -> set T, ~ [/\ forall b, E b !=set0,
    A = E false `|` E true & separated (E false) (E true)].
Admitted.

Lemma connected_subset A B C : separated A B -> C `<=` A `|` B ->
  connected C -> C `<=` A \/ C `<=` B.
Admitted.

Lemma connected1 x : connected [set x].
Admitted.
Hint Resolve connected1 : core.

Lemma bigcup_connected I (A : I -> set T) (P : I -> Prop) :
  \bigcap_(i in P) (A i) !=set0 -> (forall i, P i -> connected (A i)) ->
  connected (\bigcup_(i in P) (A i)).
Admitted.

Lemma connectedU A B : A `&` B !=set0 -> connected A -> connected B ->
   connected (A `|` B).
Admitted.

Lemma connected_closure A : connected A -> connected (closure A).
Admitted.

Definition connected_component (A : set T) (x : T) :=
  \bigcup_(A in [set C : set T | [/\ C x, C `<=` A & connected C]]) A.

Lemma component_connected A x : connected (connected_component A x).
Admitted.

Lemma connected_component_sub A x : connected_component A x `<=` A.
Admitted.

Lemma connected_component_id A x :
  A x -> connected A -> connected_component A x = A.
Admitted.

Lemma connected_component_out A x :
  ~ A x -> connected_component A x = set0.
Admitted.

Lemma connected_component_max A B x : B x -> B `<=` A ->
  connected B -> B `<=` connected_component A x.
Admitted.

Lemma connected_component_refl A x : A x -> connected_component A x x.
Admitted.

Lemma connected_component_cover A :
  \bigcup_(A in connected_component A @` A) A = A.
Admitted.

Lemma connected_component_sym A x y :
  connected_component A x y -> connected_component A y x.
Admitted.

Lemma connected_component_trans A y x z :
    connected_component A x y -> connected_component A y z ->
  connected_component A x z.
Admitted.

Lemma same_connected_component A x y : connected_component A x y ->
  connected_component A x = connected_component A y.
Admitted.

Lemma component_closed A x : closed A -> closed (connected_component A x).
Admitted.

Lemma clopen_separatedP A : clopen A <-> separated A (~` A).
Admitted.

End connected_sets.
Arguments connected {T}.
Arguments connected_component {T}.
Section DiscreteTopology.
Section DiscreteMixin.
Context {X : Type}.

Lemma discrete_sing (p : X) (A : set X) : principal_filter p A -> A p.
Admitted.

Lemma discrete_nbhs (p : X) (A : set X) :
  principal_filter p A -> principal_filter p (principal_filter^~ A).
Admitted.

Definition discrete_topological_mixin :=
  topologyOfFilterMixin principal_filter_proper discrete_sing discrete_nbhs.

End DiscreteMixin.

Definition discrete_space (X : topologicalType) :=
  @nbhs X _ = @principal_filter X.

Context {X : topologicalType} {dsc: discrete_space X}.

Lemma discrete_open (A : set X) : open A.
Admitted.

Lemma discrete_set1 (x : X) : nbhs x [set x].
Admitted.

Lemma discrete_closed (A : set X) : closed A.
Admitted.

Lemma discrete_cvg (F : set (set X)) (x : X) :
  Filter F -> F --> x <-> F [set x].
Admitted.

Lemma discrete_hausdorff : hausdorff_space X.
Admitted.
Canonical bool_discrete_topology : topologicalType. exact (TopologicalType bool discrete_topological_mixin). Defined.

Lemma discrete_bool : discrete_space bool_discrete_topology.
admit.
Defined.

Lemma bool_compact : compact [set: bool].
Admitted.

End DiscreteTopology.

#[global] Hint Resolve discrete_bool : core.

Section perfect_sets.

Implicit Types (T : topologicalType).

Definition perfect_set {T} (A : set T) := closed A /\ limit_point A = A.

Lemma perfectTP {T} : perfect_set [set: T] <-> forall x : T, ~ open [set x].
Admitted.

Lemma perfect_prod {I : Type} (i : I) (K : I -> topologicalType) :
  perfect_set [set: K i] -> perfect_set [set: product_topologicalType K].
Admitted.

Lemma perfect_diagonal (K : nat_topologicalType -> topologicalType) :
  (forall i, exists (xy: K i * K i), xy.1 != xy.2) ->
  perfect_set [set: product_topologicalType K].
Admitted.

End perfect_sets.

Section totally_disconnected.
Implicit Types T : topologicalType.

Definition totally_disconnected {T} (A : set T) :=
  forall x, A x -> connected_component A x = [set x].

Definition zero_dimensional T :=
  (forall x y, x != y -> exists U : set T, [/\ clopen U, U x & ~ U y]).

Lemma zero_dimension_prod (I : choiceType) (T : I -> topologicalType) :
  (forall i, zero_dimensional (T i)) ->
  zero_dimensional (product_topologicalType T).
Admitted.

Lemma discrete_zero_dimension {T} : discrete_space T -> zero_dimensional T.
Admitted.

Lemma zero_dimension_totally_disconnected {T} :
  zero_dimensional T -> totally_disconnected [set: T].
Admitted.

Lemma totally_disconnected_cvg {T : topologicalType} (x : T) :
  hausdorff_space T -> zero_dimensional T -> compact [set: T] ->
  filter_from [set D : set T | D x /\ clopen D] id --> x.
Admitted.

End totally_disconnected.

Section set_nbhs.

Context {T : topologicalType} (A : set T).
Definition set_nbhs := \bigcap_(x in A) (nbhs x).

Global Instance set_nbhs_filter : Filter set_nbhs.
Admitted.

Global Instance set_nbhs_pfilter : A!=set0 -> ProperFilter set_nbhs.
Admitted.

Lemma set_nbhsP (B : set T) :
   set_nbhs B <-> (exists C, [/\ open C, A `<=` C & C `<=` B]).
Admitted.

End set_nbhs.

Local Notation "A ^-1" := ([set xy | A (xy.2, xy.1)]) : classical_set_scope.

Local Notation "'to_set' A x" := ([set y | A (x, y)])
  (at level 0, A at level 0) : classical_set_scope.

Definition nbhs_ {T T'} (ent : set (set (T * T'))) (x : T) :=
  filter_from ent (fun A => to_set A x).

Lemma nbhs_E {T T'} (ent : set (set (T * T'))) x :
  nbhs_ ent x = filter_from ent (fun A => to_set A x).
Admitted.

Module Uniform.

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

Definition clone c of phant_id class c := @Pack T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).
Local Coercion base : class_of >-> Topological.class_of.
Local Coercion mixin : class_of >-> mixin_of.

Definition pack nbhs (m : @mixin_of T nbhs) :=
  fun bT (b : Topological.class_of T) of phant_id (@Topological.class bT) b =>
  fun m'   of phant_id m (m' : @mixin_of T (Filtered.nbhs_op b)) =>
  @Pack T (@Class _ b m').

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition pointedType := @Pointed.Pack cT xclass.
Definition filteredType := @Filtered.Pack cT cT xclass.
Definition topologicalType := @Topological.Pack cT xclass.

End ClassDef.

Module Export Exports.

Coercion sort : type >-> Sortclass.
Coercion base : class_of >-> Topological.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion pointedType : type >-> Pointed.type.
Canonical pointedType.
Coercion filteredType : type >-> Filtered.type.
Canonical filteredType.
Coercion topologicalType : type >-> Topological.type.
Canonical topologicalType.
Notation uniformType := type.
Notation UniformType T m := (@pack T _ m _ _ idfun _ idfun).
Notation UniformMixin := Mixin.
Notation "[ 'uniformType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'uniformType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'uniformType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'uniformType'  'of'  T ]") : form_scope.

End Exports.

End Uniform.

Export Uniform.Exports.

Section UniformTopology.

Program Definition topologyOfEntourageMixin (T : Type)
  (nbhs : T -> set (set T)) (m : Uniform.mixin_of nbhs) :
  Topological.mixin_of nbhs := topologyOfFilterMixin _ _ _.
Admit Obligations.
Admit Obligations.
Admit Obligations.

End UniformTopology.

Definition entourage {M : uniformType} := Uniform.entourage (Uniform.class M).

Lemma nbhs_entourageE {M : uniformType} : nbhs_ (@entourage M) = nbhs.
Admitted.

Lemma entourage_sym {X Y : Type} E (x : X) (y : Y) :
  E (x, y) <-> (E ^-1)%classic (y, x).
Admitted.

Lemma filter_from_entourageE {M : uniformType} x :
  filter_from (@entourage M) (fun A => to_set A x) = nbhs x.
Admitted.

Module Export NbhsEntourage.
Definition nbhs_simpl :=
  (nbhs_simpl,@filter_from_entourageE,@nbhs_entourageE).
End NbhsEntourage.

Lemma nbhsP {M : uniformType} (x : M) P : nbhs x P <-> nbhs_ entourage x P.
Admitted.

Lemma filter_inv {T : Type} (F : set (set (T * T))) :
  Filter F -> Filter [set (V^-1)%classic | V in F].
Admitted.

Section uniformType1.
Context {M : uniformType}.

Lemma entourage_refl (A : set (M * M)) x : entourage A -> A (x, x).
Admitted.

Global Instance entourage_pfilter : ProperFilter (@entourage M).
Admitted.

Lemma entourageT : entourage [set: M * M].
Admitted.

Lemma entourage_inv (A : set (M * M)) : entourage A -> entourage (A^-1)%classic.
Admitted.

Lemma entourage_split_ex (A : set (M * M)) :
  entourage A -> exists2 B, entourage B & B \; B `<=` A.
Admitted.

Definition split_ent (A : set (M * M)) :=
  get (entourage `&` [set B | B \; B `<=` A]).

Lemma split_entP (A : set (M * M)) : entourage A ->
  entourage (split_ent A) /\ split_ent A \; split_ent A `<=` A.
Admitted.

Lemma entourage_split_ent (A : set (M * M)) : entourage A ->
  entourage (split_ent A).
Admitted.

Lemma subset_split_ent (A : set (M * M)) : entourage A ->
  split_ent A \; split_ent A `<=` A.
Admitted.

Lemma entourage_split (z x y : M) A : entourage A ->
  split_ent A (x,z) -> split_ent A (z,y) -> A (x,y).
Admitted.

Lemma nbhs_entourage (x : M) A : entourage A -> nbhs x (to_set A x).
Admitted.

Lemma cvg_entourageP F (FF : Filter F) (p : M) :
  F --> p <-> forall A, entourage A -> \forall q \near F, A (p, q).
Admitted.

Lemma cvg_entourage {F} {FF : Filter F} (y : M) :
  F --> y -> forall A, entourage A -> \forall y' \near F, A (y,y').
Admitted.

Lemma cvg_app_entourageP T (f : T -> M) F (FF : Filter F) p :
  f @ F --> p <-> forall A, entourage A -> \forall t \near F, A (p, f t).
Admitted.

Lemma entourage_invI (E : set (M * M)) :
  entourage E -> entourage (E `&` E^-1)%classic.
Admitted.

Lemma split_ent_subset (E : set (M * M)) : entourage E -> split_ent E `<=` E.
Admitted.

End uniformType1.

#[global]
Hint Extern 0 (entourage (split_ent _)) => exact: entourage_split_ent : core.
#[global]
Hint Extern 0 (entourage (get _)) => exact: entourage_split_ent : core.
#[global]
Hint Extern 0 (entourage (_^-1)%classic) => exact: entourage_inv : core.
Arguments entourage_split {M} z {x y A}.
#[global]
Hint Extern 0 (nbhs _ (to_set _ _)) => exact: nbhs_entourage : core.

Lemma ent_closure {M : uniformType} (x : M) E : entourage E ->
  closure (to_set (split_ent E) x) `<=` to_set E x.
Admitted.

Lemma continuous_withinNx {U V : uniformType} (f : U -> V) x :
  {for x, continuous f} <-> f @ x^' --> f x.
Admitted.

Definition countable_uniformity (T : uniformType) :=
  exists R : set (set (T * T)), [/\
    countable R,
    R `<=` entourage &
    forall P, entourage P -> exists2 Q, R Q & Q `<=` P].

Lemma countable_uniformityP {T : uniformType} :
  countable_uniformity T <-> exists2 f : nat -> set (T * T),
    (forall A, entourage A -> exists N, f N `<=` A) &
    (forall n, entourage (f n)).
Admitted.

Section uniform_closeness.

Variable (U : uniformType).

Lemma open_nbhs_entourage (x : U) (A : set (U * U)) :
  entourage A -> open_nbhs x (to_set A x)^°.
Admitted.

Lemma entourage_close (x y : U) : close x y = forall A, entourage A -> A (x, y).
Admitted.

Lemma close_trans (y x z : U) : close x y -> close y z -> close x z.
Admitted.

Lemma close_cvgxx (x y : U) : close x y -> x --> y.
Admitted.

Lemma cvg_closeP (F : set (set U)) (l : U) : ProperFilter F ->
  F --> l <-> ([cvg F in U] /\ close (lim F) l).
Admitted.

End uniform_closeness.

Definition unif_continuous (U V : uniformType) (f : U -> V) :=
  (fun xy => (f xy.1, f xy.2)) @ entourage --> entourage.

Section prod_Uniform.

Context {U V : uniformType}.
Implicit Types A : set ((U * V) * (U * V)).

Definition prod_ent :=
  [set A : set ((U * V) * (U * V)) |
    filter_prod (@entourage U) (@entourage V)
    [set ((xy.1.1,xy.2.1),(xy.1.2,xy.2.2)) | xy in A]].

Lemma prod_entP (A : set (U * U)) (B : set (V * V)) :
  entourage A -> entourage B ->
  prod_ent [set xy | A (xy.1.1, xy.2.1) /\ B (xy.1.2, xy.2.2)].
Admitted.

Lemma prod_ent_filter : Filter prod_ent.
Admitted.

Lemma prod_ent_refl A : prod_ent A -> [set xy | xy.1 = xy.2] `<=` A.
Admitted.

Lemma prod_ent_inv A : prod_ent A -> prod_ent (A^-1)%classic.
Admitted.

Lemma prod_ent_split A : prod_ent A -> exists2 B, prod_ent B & B \; B `<=` A.
Admitted.

Lemma prod_ent_nbhsE : nbhs = nbhs_ prod_ent.
Admitted.

Definition prod_uniformType_mixin :=
  Uniform.Mixin prod_ent_filter prod_ent_refl prod_ent_inv prod_ent_split
  prod_ent_nbhsE.

End prod_Uniform.

Canonical prod_uniformType (U V : uniformType) :=
  UniformType (U * V) (@prod_uniformType_mixin U V).

Section matrix_Uniform.

Variables (m n : nat) (T : uniformType).

Implicit Types A : set ('M[T]_(m, n) * 'M[T]_(m, n)).

Definition mx_ent :=
  filter_from
  [set P : 'I_m -> 'I_n -> set (T * T) | forall i j, entourage (P i j)]
  (fun P => [set MN : 'M[T]_(m, n) * 'M[T]_(m, n) |
    forall i j, P i j (MN.1 i j, MN.2 i j)]).

Lemma mx_ent_filter : Filter mx_ent.
Admitted.

Lemma mx_ent_refl A : mx_ent A -> [set MN | MN.1 = MN.2] `<=` A.
Admitted.

Lemma mx_ent_inv A : mx_ent A -> mx_ent (A^-1)%classic.
Admitted.

Lemma mx_ent_split A : mx_ent A -> exists2 B, mx_ent B & B \; B `<=` A.
Admitted.

Lemma mx_ent_nbhsE : nbhs = nbhs_ mx_ent.
Admitted.

Definition matrix_uniformType_mixin :=
  Uniform.Mixin mx_ent_filter mx_ent_refl mx_ent_inv mx_ent_split
  mx_ent_nbhsE.

Canonical matrix_uniformType :=
  UniformType 'M[T]_(m, n) matrix_uniformType_mixin.

End matrix_Uniform.

Lemma cvg_mx_entourageP (T : uniformType) m n (F : set (set 'M[T]_(m,n)))
  (FF : Filter F) (M : 'M[T]_(m,n)) :
  F --> M <->
  forall A, entourage A -> \forall N \near F,
  forall i j, A (M i j, (N : 'M[T]_(m,n)) i j).
Admitted.

Section fct_Uniform.

Variable (T : choiceType) (U : uniformType).

Definition fct_ent :=
  filter_from
  (@entourage U)
  (fun P => [set fg | forall t : T, P (fg.1 t, fg.2 t)]).

Lemma fct_ent_filter : Filter fct_ent.
Admitted.

Lemma fct_ent_refl A : fct_ent A -> [set fg | fg.1 = fg.2] `<=` A.
Admitted.

Lemma fct_ent_inv A : fct_ent A -> fct_ent (A^-1)%classic.
Admitted.

Lemma fct_ent_split A : fct_ent A -> exists2 B, fct_ent B & B \; B `<=` A.
Admitted.

Definition fct_uniformType_mixin :=
  UniformMixin fct_ent_filter fct_ent_refl fct_ent_inv fct_ent_split erefl.

Definition fct_topologicalTypeMixin :=
  topologyOfEntourageMixin fct_uniformType_mixin.

Canonical generic_source_filter := @Filtered.Source _ _ _ (nbhs_ fct_ent).
Canonical fct_topologicalType :=
  TopologicalType (T -> U) fct_topologicalTypeMixin.
Canonical fct_uniformType := UniformType (T -> U) fct_uniformType_mixin.

End fct_Uniform.

Lemma cvg_fct_entourageP (T : choiceType) (U : uniformType)
  (F : set (set (T -> U))) (FF : Filter F) (f : T -> U) :
  F --> f <->
  forall A, entourage A ->
  \forall g \near F, forall t, A (f t, g t).
Admitted.

Definition entourage_set (U : uniformType) (A : set ((set U) * (set U))) :=
  exists2 B, entourage B & forall PQ, A PQ -> forall p q,
    PQ.1 p -> PQ.2 q -> B (p,q).
Canonical set_filter_source (U : uniformType) :=
  @Filtered.Source Prop _ U (fun A => nbhs_ (@entourage_set U) A).

Definition entourage_ {R : numDomainType} {T T'} (ball : T -> R -> set T') :=
  @filter_from R _ [set x | 0 < x] (fun e => [set xy | ball xy.1 e xy.2]).

Lemma entourage_E {R : numDomainType} {T T'} (ball : T -> R -> set T') :
  entourage_ ball =
  @filter_from R _ [set x | 0 < x] (fun e => [set xy | ball xy.1 e xy.2]).
Admitted.
Definition map_pair {S U} (f : S -> U) (x : (S * S)) : (U * U). exact ((f x.1, f x.2)). Defined.

Section weak_uniform.

Variable (pS : pointedType) (U : uniformType) (f : pS -> U).

Let S := weak_topologicalType f.
Definition weak_ent : set (set (S * S)). exact (filter_from (@entourage U) (fun V => (map_pair f)@^-1` V)). Defined.

Lemma weak_ent_filter : Filter weak_ent.
Admitted.

Lemma weak_ent_refl A : weak_ent A -> [set fg | fg.1 = fg.2] `<=` A.
Admitted.

Lemma weak_ent_inv A : weak_ent A -> weak_ent (A^-1)%classic.
Admitted.

Lemma weak_ent_split A : weak_ent A -> exists2 B, weak_ent B & B \; B `<=` A.
Admitted.

Lemma weak_ent_nbhs : nbhs = nbhs_ weak_ent.
Admitted.

Definition weak_uniform_mixin :=
  @UniformMixin S nbhs weak_ent
    weak_ent_filter weak_ent_refl weak_ent_inv weak_ent_split weak_ent_nbhs.

Definition weak_uniformType :=
  UniformType S weak_uniform_mixin.

End weak_uniform.

Section sup_uniform.

Variable (T : pointedType) (Ii : Type) (Tc : Ii -> Uniform.class_of T).
Let I : choiceType. exact (classicType_choiceType Ii). Defined.
Let TS := fun i => Uniform.Pack (Tc i).
Let Tt := @sup_topologicalType T I Tc.
Let ent_of (p : I * set (T * T)) := `[< @entourage (TS p.1) p.2>].
Let IEnt := ChoiceType {p : (I * set (T * T)) | ent_of p} (sig_choiceMixin _).

Local Lemma IEnt_pointT (i : I) : ent_of (i, setT).
Admitted.
Definition sup_ent : (set (set (T * T))). exact (filter_from (finI_from [set: IEnt] (fun p => (projT1 p).2)) id). Defined.

Definition sup_ent_filter : Filter sup_ent.
Admitted.

Lemma sup_ent_refl A : sup_ent A -> [set fg | fg.1 = fg.2] `<=` A.
Admitted.

Lemma sup_ent_inv A : sup_ent A -> sup_ent (A^-1)%classic.
Admitted.

Lemma sup_ent_split A : sup_ent A -> exists2 B, sup_ent B & B \; B `<=` A.
Admitted.

Lemma sup_ent_nbhs : @nbhs Tt Tt = nbhs_ sup_ent.
Admitted.

Definition sup_uniform_mixin:=
  @UniformMixin Tt nbhs
    sup_ent sup_ent_filter sup_ent_refl sup_ent_inv sup_ent_split sup_ent_nbhs.

Definition sup_uniformType := UniformType Tt sup_uniform_mixin.

Lemma countable_sup_ent :
  countable [set: Ii] -> (forall n, countable_uniformity (TS n)) ->
  countable_uniformity sup_uniformType.
Admitted.

End sup_uniform.

Section product_uniform.

Variable (I : choiceType) (T : I -> uniformType).

Definition product_uniformType :=
  sup_uniformType (fun i => Uniform.class
    (weak_uniformType (fun f : dep_arrow_pointedType T => f i))).

End product_uniform.

Section discrete_uniform.

Context {T : topologicalType} {dsc: discrete_space T}.
Definition discrete_ent : set (set (T * T)). exact (globally (range (fun x => (x, x)))). Defined.

Program Definition discrete_uniform_mixin :=
  @UniformMixin T nbhs discrete_ent _ _ _ _ _.
Admit Obligations.
Admit Obligations.
Admit Obligations.
Admit Obligations.

Definition discrete_uniformType := UniformType T discrete_uniform_mixin.

End discrete_uniform.

Module PseudoMetric.

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
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of R xT).
Local Coercion base : class_of >-> Uniform.class_of.
Local Coercion mixin : class_of >-> mixin_of.

Definition pack ent (m : @mixin_of R T ent) :=
  fun bT (b : Uniform.class_of T) of phant_id (@Uniform.class bT) b =>
  fun m'   of phant_id m (m' : @mixin_of R T (Uniform.entourage b)) =>
  @Pack T (@Class R _ b m').

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition pointedType := @Pointed.Pack cT xclass.
Definition filteredType := @Filtered.Pack cT cT xclass.
Definition topologicalType := @Topological.Pack cT xclass.
Definition uniformType := @Uniform.Pack cT xclass.

End ClassDef.

Module Export Exports.

Coercion sort : type >-> Sortclass.
Coercion base : class_of >-> Uniform.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion pointedType : type >-> Pointed.type.
Canonical pointedType.
Coercion filteredType : type >-> Filtered.type.
Canonical filteredType.
Coercion topologicalType : type >-> Topological.type.
Canonical topologicalType.
Coercion uniformType : type >-> Uniform.type.
Canonical uniformType.
Notation pseudoMetricType := type.
Notation PseudoMetricType T m := (@pack _ T _ m _ _ idfun _ idfun).
Notation PseudoMetricMixin := Mixin.
Notation "[ 'pseudoMetricType' R 'of' T 'for' cT ]" := (@clone R T cT _ idfun)
  (at level 0, format "[ 'pseudoMetricType'  R  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'pseudoMetricType' R 'of' T ]" := (@clone R T _ _ id)
  (at level 0, format "[ 'pseudoMetricType'  R  'of'  T ]") : form_scope.

End Exports.

End PseudoMetric.

Export PseudoMetric.Exports.

Section PseudoMetricUniformity.

Let ball_le (R : numDomainType) (M : Type) (ent : set (set (M * M)))
    (m : PseudoMetric.mixin_of R ent) :
  forall (x : M), {homo PseudoMetric.ball m x : e1 e2 / e1 <= e2 >-> e1 `<=` e2}.
Admitted.

Program Definition uniformityOfBallMixin (R : numFieldType) (T : Type)
  (ent : set (set (T * T))) (nbhs : T -> set (set T)) (nbhsE : nbhs = nbhs_ ent)
  (m : PseudoMetric.mixin_of R ent) : Uniform.mixin_of nbhs :=
  UniformMixin _ _ _ _ nbhsE.
Admit Obligations.
Admit Obligations.
Admit Obligations.
Admit Obligations.

End PseudoMetricUniformity.

Definition ball {R : numDomainType} {M : pseudoMetricType R} :=
  PseudoMetric.ball (PseudoMetric.class M).

Lemma entourage_ballE {R : numDomainType} {M : pseudoMetricType R}
  : entourage_ (@ball R M) = entourage.
Admitted.

Lemma entourage_from_ballE {R : numDomainType} {M : pseudoMetricType R} :
  @filter_from R _ [set x : R | 0 < x]
    (fun e => [set xy | @ball R M xy.1 e xy.2]) = entourage.
Admitted.

Lemma entourage_ball {R : numDomainType} (M : pseudoMetricType R)
  (e : {posnum R}) : entourage [set xy : M * M | ball xy.1 e%:num xy.2].
Admitted.
#[global] Hint Resolve entourage_ball : core.

Definition nbhs_ball_ {R : numDomainType} {T T'} (ball : T -> R -> set T')
  (x : T) := @filter_from R _ [set e | e > 0] (ball x).

Definition nbhs_ball {R : numDomainType} {M : pseudoMetricType R} :=
  nbhs_ball_ (@ball R M).

Lemma nbhs_ballE {R : numDomainType} {M : pseudoMetricType R} : (@nbhs_ball R M) = nbhs.
Admitted.

Lemma filter_from_ballE {R : numDomainType} {M : pseudoMetricType R} x :
  @filter_from R _ [set x : R | 0 < x] (@ball R M x) = nbhs x.
Admitted.

Module Export NbhsBall.
Definition nbhs_simpl := (nbhs_simpl,@filter_from_ballE,@nbhs_ballE).
End NbhsBall.

Lemma nbhs_ballP {R : numDomainType} {M : pseudoMetricType R} (x : M) P :
  nbhs x P <-> nbhs_ball x P.
Admitted.

Lemma ball_center {R : numDomainType} (M : pseudoMetricType R) (x : M)
  (e : {posnum R}) : ball x e%:num x.
Admitted.
#[global] Hint Resolve ball_center : core.

Section pseudoMetricType_numDomainType.
Context {R : numDomainType} {M : pseudoMetricType R}.

Lemma ballxx (x : M) (e : R) : 0 < e -> ball x e x.
Admitted.

Lemma ball_sym (x y : M) (e : R) : ball x e y -> ball y e x.
Admitted.

Lemma ball_symE (x y : M) (e : R) : ball x e y = ball y e x.
Admitted.

Lemma ball_triangle (y x z : M) (e1 e2 : R) :
  ball x e1 y -> ball y e2 z -> ball x (e1 + e2) z.
Admitted.

Lemma nbhsx_ballx (x : M) (eps : {posnum R}) : nbhs x (ball x eps%:num).
Admitted.

Lemma open_nbhs_ball (x : M) (eps : {posnum R}) : open_nbhs x ((ball x eps%:num)^°).
Admitted.

Lemma le_ball (x : M) (e1 e2 : R) : e1 <= e2 -> ball x e1 `<=` ball x e2.
Admitted.

Global Instance entourage_proper_filter : ProperFilter (@entourage M).
Admitted.

Lemma near_ball (y : M) (eps : {posnum R}) :
   \forall y' \near y, ball y eps%:num y'.
Admitted.

Lemma fcvg_ballP {F} {FF : Filter F} (y : M) :
  F --> y <-> forall eps : R, 0 < eps -> \forall y' \near F, ball y eps y'.
Admitted.

Lemma __deprecated__cvg_ballPpos {F} {FF : Filter F} (y : M) :
  F --> y <-> forall eps : {posnum R}, \forall y' \near F, ball y eps%:num y'.
Admitted.
#[deprecated(since="mathcomp-analysis 0.6.0",
  note="use a combination of `cvg_ballP` and `posnumP`")]
Notation cvg_ballPpos := __deprecated__cvg_ballPpos.

Lemma fcvg_ball {F} {FF : Filter F} (y : M) :
  F --> y -> forall eps : R, 0 < eps -> \forall y' \near F, ball y eps y'.
Admitted.

Lemma cvg_ballP {T} {F} {FF : Filter F} (f : T -> M) y :
  f @ F --> y <-> forall eps : R, 0 < eps -> \forall x \near F, ball y eps (f x).
Admitted.

Lemma cvg_ball {T} {F} {FF : Filter F} (f : T -> M) y :
  f @ F --> y -> forall eps : R, 0 < eps -> \forall x \near F, ball y eps (f x).
Admitted.

Lemma cvgi_ballP T {F} {FF : Filter F} (f : T -> M -> Prop) y :
  f `@ F --> y <->
  forall eps : R, 0 < eps -> \forall x \near F, exists z, f x z /\ ball y eps z.
Admitted.
Definition cvg_toi_locally := @cvgi_ballP.

Lemma cvgi_ball T {F} {FF : Filter F} (f : T -> M -> Prop) y :
  f `@ F --> y ->
  forall eps : R, 0 < eps -> F [set x | exists z, f x z /\ ball y eps z].
Admitted.

End pseudoMetricType_numDomainType.
#[global] Hint Resolve nbhsx_ballx : core.
#[global] Hint Resolve close_refl : core.
Arguments close_cvg {T} F1 F2 {FF2} _.

#[deprecated(since="mathcomp-analysis 0.6.0", note="renamed `cvg_ball`")]
Notation app_cvg_locally := cvg_ball.

Section pseudoMetricType_numFieldType.
Context {R : numFieldType} {M : pseudoMetricType R}.

Lemma ball_split (z x y : M) (e : R) :
  ball x (e / 2) z -> ball z (e / 2) y -> ball x e y.
Admitted.

Lemma ball_splitr (z x y : M) (e : R) :
  ball z (e / 2) x -> ball z (e / 2) y -> ball x e y.
Admitted.

Lemma ball_splitl (z x y : M) (e : R) :
  ball x (e / 2) z -> ball y (e / 2) z -> ball x e y.
Admitted.

Lemma ball_close (x y : M) :
  close x y = forall eps : {posnum R}, ball x eps%:num y.
Admitted.

End pseudoMetricType_numFieldType.

Section ball_hausdorff.
Variables (R : numDomainType) (T : pseudoMetricType R).

Lemma ball_hausdorff : hausdorff_space T =
  forall (a b : T), a != b ->
  exists r : {posnum R} * {posnum R},
    ball a r.1%:num `&` ball b r.2%:num == set0.
Admitted.
End ball_hausdorff.

Section entourages.
Variable R : numDomainType.
Lemma unif_continuousP (U V : pseudoMetricType R) (f : U -> V) :
  unif_continuous f <->
  forall e, e > 0 -> exists2 d, d > 0 &
    forall x, ball x.1 d x.2 -> ball (f x.1) e (f x.2).
Admitted.
End entourages.

Lemma countable_uniformity_metric {R : realType} {T : pseudoMetricType R} :
  countable_uniformity T.
Admitted.

Section matrix_PseudoMetric.
Variables (m n : nat) (R : numDomainType) (T : pseudoMetricType R).
Implicit Types x y : 'M[T]_(m, n).
Definition mx_ball x (e : R) y := forall i j, ball (x i j) e (y i j).
Lemma mx_ball_center x (e : R) : 0 < e -> mx_ball x e x.
Admitted.
Lemma mx_ball_sym x y (e : R) : mx_ball x e y -> mx_ball y e x.
Admitted.
Lemma mx_ball_triangle x y z (e1 e2 : R) :
  mx_ball x e1 y -> mx_ball y e2 z -> mx_ball x (e1 + e2) z.
Admitted.

Lemma mx_entourage : entourage = entourage_ mx_ball.
Admitted.
Definition matrix_pseudoMetricType_mixin :=
  PseudoMetric.Mixin mx_ball_center mx_ball_sym mx_ball_triangle mx_entourage.
Canonical matrix_pseudoMetricType :=
  PseudoMetricType 'M[T]_(m, n) matrix_pseudoMetricType_mixin.
End matrix_PseudoMetric.

Section prod_PseudoMetric.
Context {R : numDomainType} {U V : pseudoMetricType R}.
Implicit Types (x y : U * V).
Definition prod_point : U * V. exact ((point, point)). Defined.
Definition prod_ball x (eps : R) y :=
  ball (fst x) eps (fst y) /\ ball (snd x) eps (snd y).
Lemma prod_ball_center x (eps : R) : 0 < eps -> prod_ball x eps x.
Admitted.
Lemma prod_ball_sym x y (eps : R) : prod_ball x eps y -> prod_ball y eps x.
Admitted.
Lemma prod_ball_triangle x y z (e1 e2 : R) :
  prod_ball x e1 y -> prod_ball y e2 z -> prod_ball x (e1 + e2) z.
Admitted.
Lemma prod_entourage : entourage = entourage_ prod_ball.
Admitted.
Definition prod_pseudoMetricType_mixin :=
  PseudoMetric.Mixin prod_ball_center prod_ball_sym prod_ball_triangle prod_entourage.
End prod_PseudoMetric.
Canonical prod_pseudoMetricType (R : numDomainType) (U V : pseudoMetricType R) :=
  PseudoMetricType (U * V) (@prod_pseudoMetricType_mixin R U V).

Section Nbhs_fct2.
Context {T : Type} {R : numDomainType} {U V : pseudoMetricType R}.
Lemma fcvg_ball2P {F : set (set U)} {G : set (set V)}
  {FF : Filter F} {FG : Filter G} (y : U) (z : V):
  (F, G) --> (y, z) <->
  forall eps : R, eps > 0 -> \forall y' \near F & z' \near G,
                ball y eps y' /\ ball z eps z'.
Admitted.

Lemma cvg_ball2P {I J} {F : set (set I)} {G : set (set J)}
  {FF : Filter F} {FG : Filter G} (f : I -> U) (g : J -> V) (y : U) (z : V):
  (f @ F, g @ G) --> (y, z) <->
  forall eps : R, eps > 0 -> \forall i \near F & j \near G,
                ball y eps (f i) /\ ball z eps (g j).
Admitted.

End Nbhs_fct2.

Section fct_PseudoMetric.
Variable (T : choiceType) (R : numFieldType) (U : pseudoMetricType R).
Definition fct_ball (x : T -> U) (eps : R) (y : T -> U) :=
  forall t : T, ball (x t) eps (y t).
Lemma fct_ball_center (x : T -> U) (e : R) : 0 < e -> fct_ball x e x.
Admitted.

Lemma fct_ball_sym (x y : T -> U) (e : R) : fct_ball x e y -> fct_ball y e x.
Admitted.
Lemma fct_ball_triangle (x y z : T -> U) (e1 e2 : R) :
  fct_ball x e1 y -> fct_ball y e2 z -> fct_ball x (e1 + e2) z.
Admitted.
Lemma fct_entourage : entourage = entourage_ fct_ball.
Admitted.
Definition fct_pseudoMetricType_mixin :=
  PseudoMetricMixin fct_ball_center fct_ball_sym fct_ball_triangle fct_entourage.
Canonical fct_pseudoMetricType := PseudoMetricType (T -> U) fct_pseudoMetricType_mixin.
End fct_PseudoMetric.

Definition quotient_topology (T : topologicalType) (Q : quotType T) := Q.

Section quotients.
Local Open Scope quotient_scope.
Context {T : topologicalType} {Q0 : quotType T}.

Let Q := quotient_topology Q0.

Canonical quotient_subtype := [subType Q of T by %/].
Canonical quotient_eq := EqType Q [eqMixin of Q by <:].
Canonical quotient_choice := ChoiceType Q  [choiceMixin of Q by <:].
Canonical quotient_pointed := PointedType Q (\pi_Q point).

Definition quotient_open U := open (\pi_Q @^-1` U).

Program Definition quotient_topologicalType_mixin :=
  @topologyOfOpenMixin Q quotient_open _ _ _.
Admit Obligations.
Admit Obligations.
Admit Obligations.

Let quotient_filtered := Filtered.Class (Pointed.class quotient_pointed)
  (nbhs_of_open quotient_open).

Canonical quotient_topologicalType := @Topological.Pack Q
  (@Topological.Class _ quotient_filtered quotient_topologicalType_mixin).

Let Q' := quotient_topologicalType.

Lemma pi_continuous : continuous (\pi_Q : T -> Q').
Admitted.

Lemma quotient_continuous {Z : topologicalType} (f : Q' -> Z) :
  continuous f <-> continuous (f \o \pi_Q).
Admitted.

Lemma repr_comp_continuous (Z : topologicalType) (g : T -> Z) :
  continuous g -> {homo g : a b / a == b %[mod Q] >-> a == b} ->
  continuous (g \o repr : Q' -> Z).
Admitted.

End quotients.

Section discrete_pseudoMetric.
Context {R : numDomainType} {T : topologicalType} {dsc : discrete_space T}.

Definition discrete_ball (x : T) (eps : R) y : Prop := x = y.

Lemma discrete_ball_center x (eps : R) : 0 < eps -> discrete_ball x eps x.
Admitted.

Program Definition discrete_pseudoMetricType_mixin :=
  @PseudoMetric.Mixin R T discrete_ent discrete_ball _ _ _ _.
Admit Obligations.
Admit Obligations.
Admit Obligations.
Admit Obligations.

Definition discrete_pseudoMetricType := PseudoMetricType
  (@discrete_uniformType _ dsc) discrete_pseudoMetricType_mixin.

End discrete_pseudoMetric.

Definition pseudoMetric_bool {R : realType} :=
  @discrete_pseudoMetricType R [topologicalType of bool] discrete_bool.

Definition cauchy {T : uniformType} (F : set (set T)) := (F, F) --> entourage.

Lemma cvg_cauchy {T : uniformType} (F : set (set T)) : Filter F ->
  [cvg F in T] -> cauchy F.
Admitted.

Module Complete.
Definition axiom (T : uniformType) :=
  forall (F : set (set T)), ProperFilter F -> cauchy F -> F --> lim F.
Section ClassDef.
Record class_of (T : Type) := Class {
  base : Uniform.class_of T ;
  mixin : axiom (Uniform.Pack base)
}.
Local Coercion base : class_of >-> Uniform.class_of.
Local Coercion mixin : class_of >-> Complete.axiom.
Structure type := Pack { sort; _ : class_of sort }.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c := cT return class_of cT in c.
Definition clone c of phant_id class c := @Pack T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).
Definition pack b0 (m0 : axiom (@Uniform.Pack T b0)) :=
  fun bT b of phant_id (@Uniform.class bT) b =>
  fun m of phant_id m m0 => @Pack T (@Class T b m).
Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition pointedType := @Pointed.Pack cT xclass.
Definition filteredType := @Filtered.Pack cT cT xclass.
Definition topologicalType := @Topological.Pack cT xclass.
Definition uniformType := @Uniform.Pack cT xclass.
End ClassDef.
Module Export Exports.
Coercion base : class_of >-> Uniform.class_of.
Coercion mixin : class_of >-> axiom.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion pointedType : type >-> Pointed.type.
Canonical pointedType.
Coercion filteredType : type >-> Filtered.type.
Canonical filteredType.
Coercion topologicalType : type >-> Topological.type.
Canonical topologicalType.
Coercion uniformType : type >-> Uniform.type.
Canonical uniformType.
Notation completeType := type.
Notation "[ 'completeType' 'of' T 'for' cT ]" :=  (@clone T cT _ idfun)
  (at level 0, format "[ 'completeType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'completeType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'completeType'  'of'  T ]") : form_scope.
Notation CompleteType T m := (@pack T _ m _ _ idfun _ idfun).
End Exports.
End Complete.
Export Complete.Exports.

Section completeType1.

Context {T : completeType}.

Lemma cauchy_cvg (F : set (set T)) (FF : ProperFilter F) :
  cauchy F -> cvg F.
Admitted.

Lemma cauchy_cvgP (F : set (set T)) (FF : ProperFilter F) : cauchy F <-> cvg F.
Admitted.

End completeType1.
Arguments cauchy_cvg {T} F {FF} _.
Arguments cauchy_cvgP {T} F {FF}.

Section matrix_Complete.

Variables (T : completeType) (m n : nat).

Lemma mx_complete (F : set (set 'M[T]_(m, n))) :
  ProperFilter F -> cauchy F -> cvg F.
Admitted.

Canonical matrix_completeType := CompleteType 'M[T]_(m, n) mx_complete.

End matrix_Complete.

Section fun_Complete.

Context {T : choiceType} {U : completeType}.

Lemma fun_complete (F : set (set (T -> U)))
  {FF :  ProperFilter F} : cauchy F -> cvg F.
Admitted.

Canonical fun_completeType := CompleteType (T -> U) fun_complete.

End fun_Complete.

Section Cvg_switch.
Context {T1 T2 : choiceType}.

Lemma cvg_switch_1 {U : uniformType}
  F1 {FF1 : ProperFilter F1} F2 {FF2 : Filter F2}
  (f : T1 -> T2 -> U) (g : T2 -> U) (h : T1 -> U) (l : U) :
  f @ F1 --> g -> (forall x1, f x1 @ F2 --> h x1) -> h @ F1 --> l ->
  g @ F2 --> l.
Admitted.

Lemma cvg_switch_2 {U : completeType}
  F1 {FF1 : ProperFilter F1} F2 {FF2 : ProperFilter F2}
  (f : T1 -> T2 -> U) (g : T2 -> U) (h : T1 -> U) :
  f @ F1 --> g -> (forall x, f x @ F2 --> h x) ->
  [cvg h @ F1 in U].
Admitted.

Lemma cvg_switch {U : completeType}
  F1 (FF1 : ProperFilter F1) F2 (FF2 : ProperFilter F2)
  (f : T1 -> T2 -> U) (g : T2 -> U) (h : T1 -> U) :
  f @ F1 --> g -> (forall x1, f x1 @ F2 --> h x1) ->
  exists l : U, h @ F1 --> l /\ g @ F2 --> l.
Admitted.

End Cvg_switch.

Definition cauchy_ex {R : numDomainType} {T : pseudoMetricType R} (F : set (set T)) :=
  forall eps : R, 0 < eps -> exists x, F (ball x eps).

Definition cauchy_ball {R : numDomainType} {T : pseudoMetricType R} (F : set (set T)) :=
  forall e, e > 0 -> \forall x & y \near F, ball x e y.

Lemma cauchy_ballP (R : numDomainType) (T  : pseudoMetricType R)
    (F : set (set T)) (FF : Filter F) :
  cauchy_ball F <-> cauchy F.
Admitted.
Arguments cauchy_ballP {R T} F {FF}.

Lemma cauchy_exP (R : numFieldType) (T : pseudoMetricType R)
    (F : set (set T)) (FF : Filter F) :
  cauchy_ex F -> cauchy F.
Admitted.
Arguments cauchy_exP {R T} F {FF}.

Lemma cauchyP (R : numFieldType) (T : pseudoMetricType R)
    (F : set (set T)) (PF : ProperFilter F) :
  cauchy F <-> cauchy_ex F.
Admitted.
Arguments cauchyP {R T} F {PF}.

Lemma compact_cauchy_cvg {T : uniformType} (U : set T) (F : set (set T)) :
  ProperFilter F -> cauchy F -> F U -> compact U -> cvg F.
Admitted.

Module CompletePseudoMetric.
Section ClassDef.
Variable R : numDomainType.
Record class_of (T : Type) := Class {
  base : PseudoMetric.class_of R T;
  mixin : Complete.axiom (Uniform.Pack base)
}.
Local Coercion base : class_of >-> PseudoMetric.class_of.
Definition base2 T m := Complete.Class (@mixin T m).
Local Coercion base2 : class_of >-> Complete.class_of.

Structure type := Pack { sort; _ : class_of sort }.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c := cT return class_of cT in c.
Definition clone c of phant_id class c := @Pack T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).
Definition pack :=
  fun bT b & phant_id (@PseudoMetric.class R bT) (b : PseudoMetric.class_of R T) =>
  fun mT m & phant_id (Complete.class mT) (@Complete.Class T b m) =>
  Pack (@Class T b m).
Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition pointedType := @Pointed.Pack cT xclass.
Definition filteredType := @Filtered.Pack cT cT xclass.
Definition topologicalType := @Topological.Pack cT xclass.
Definition uniformType := @Uniform.Pack cT xclass.
Definition completeType := @Complete.Pack cT xclass.
Definition pseudoMetricType := @PseudoMetric.Pack R cT xclass.
Definition pseudoMetric_completeType := @Complete.Pack pseudoMetricType xclass.
End ClassDef.
Module Export Exports.
Coercion base : class_of >-> PseudoMetric.class_of.
Coercion mixin : class_of >-> Complete.axiom.
Coercion base2 : class_of >-> Complete.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion pointedType : type >-> Pointed.type.
Canonical pointedType.
Coercion filteredType : type >-> Filtered.type.
Canonical filteredType.
Coercion topologicalType : type >-> Topological.type.
Canonical topologicalType.
Coercion uniformType : type >-> Uniform.type.
Canonical uniformType.
Coercion completeType : type >-> Complete.type.
Canonical completeType.
Coercion pseudoMetricType : type >-> PseudoMetric.type.
Canonical pseudoMetricType.
Canonical pseudoMetric_completeType.
Notation completePseudoMetricType := type.
Notation "[ 'completePseudoMetricType' 'of' T 'for' cT ]" :=  (@clone T cT _ idfun)
  (at level 0, format "[ 'completePseudoMetricType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'completePseudoMetricType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'completePseudoMetricType'  'of'  T ]") : form_scope.
Notation CompletePseudoMetricType T m := (@pack _ T _ _ id _ _ id).
End Exports.
End CompletePseudoMetric.
Export CompletePseudoMetric.Exports.

Canonical matrix_completePseudoMetricType (R : numFieldType)
  (T : completePseudoMetricType R) (m n : nat) :=
  CompletePseudoMetricType 'M[T]_(m, n) mx_complete.

Canonical fct_completePseudoMetricType (T : choiceType) (R : numFieldType)
  (U : completePseudoMetricType R) :=
  CompletePseudoMetricType (T -> U) fun_complete.
Definition pointed_of_zmodule (R : zmodType) : pointedType. exact (PointedType R 0). Defined.

Definition ball_
  (R : numDomainType) (V : zmodType) (norm : V -> R) (x : V) (e : R) :=
  [set y | norm (x - y) < e].
Arguments ball_ {R} {V} norm x e%R y /.

Lemma subset_ball_prop_in_itv (R : realDomainType) (x : R) e P :
  (ball_ Num.Def.normr x e `<=` P)%classic <->
  {in `](x - e), (x + e)[, forall y, P y}.
Admitted.

Lemma subset_ball_prop_in_itvcc (R : realDomainType) (x : R) e P : 0 < e ->
  (ball_ Num.Def.normr x (2 * e) `<=` P)%classic ->
  {in `[(x - e), (x + e)], forall y, P y}.
Admitted.

Global Instance ball_filter (R : realDomainType) (t : R) : Filter
  [set P | exists2 i : R, 0 < i & ball_ Num.norm t i `<=` P].
Admitted.

#[global] Hint Extern 0 (Filter [set P | exists2 i, _ & ball_ _ _ i `<=` P]) =>
  (apply: ball_filter) : typeclass_instances.
Definition filtered_of_normedZmod (K : numDomainType) (R : normedZmodType K)
  : filteredType R. exact (Filtered.Pack (Filtered.Class
    (@Pointed.class (pointed_of_zmodule R))
    (nbhs_ball_ (ball_ (fun x => `|x|))))). Defined.

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
  : PseudoMetric.mixin_of K (@entourage_ K R R (ball_ (fun x => `|x|))). exact (PseudoMetricMixin ball_norm_center ball_norm_symmetric ball_norm_triangle erefl). Defined.
Lemma nbhs_ball_normE :
  @nbhs_ball_ K R R (ball_ Num.norm) = nbhs_ (entourage_ (ball_ Num.norm)).
Admitted.
End pseudoMetric_of_normedDomain.

Module Export regular_topology.

Section regular_topology.
Local Canonical pointedType (R : zmodType) : pointedType. exact ([pointedType of R^o for pointed_of_zmodule R]). Defined.
Local Canonical filteredType (R : numDomainType) : filteredType R. exact ([filteredType R of R^o for filtered_of_normedZmod R]). Defined.
Local Canonical topologicalType (R : numFieldType) : topologicalType. exact (TopologicalType R^o (topologyOfEntourageMixin (uniformityOfBallMixin
      (@nbhs_ball_normE _ _) (pseudoMetric_of_normedDomain _)))). Defined.
Local Canonical uniformType (R : numFieldType) : uniformType. exact (UniformType R^o (uniformityOfBallMixin
                     (@nbhs_ball_normE _ _) (pseudoMetric_of_normedDomain _))). Defined.
Local Canonical pseudoMetricType (R : numFieldType) :=
  PseudoMetricType R^o (@pseudoMetric_of_normedDomain R R).
End regular_topology.

Module Export Exports.
Canonical pointedType.
Canonical filteredType.
Canonical topologicalType.
Canonical uniformType.
Canonical pseudoMetricType.
End Exports.

End regular_topology.
Export regular_topology.Exports.

Module Export numFieldTopology.

Section realType.
Variable (R : realType).
Local Canonical real_pointedType := [pointedType of R for [pointedType of R^o]].
Local Canonical real_filteredType :=
  [filteredType R of R for [filteredType R of R^o]].
Local Canonical real_topologicalType :=
  [topologicalType of R for [topologicalType of R^o]].
Local Canonical real_uniformType := [uniformType of R for [uniformType of R^o]].
Local Canonical real_pseudoMetricType :=
  [pseudoMetricType R of R for [pseudoMetricType R of R^o]].
End realType.

Section rcfType.
Variable (R : rcfType).
Local Canonical rcf_pointedType := [pointedType of R for [pointedType of R^o]].
Local Canonical rcf_filteredType :=
  [filteredType R of R for [filteredType R of R^o]].
Local Canonical rcf_topologicalType :=
  [topologicalType of R for [topologicalType of R^o]].
Local Canonical rcf_uniformType := [uniformType of R for [uniformType of R^o]].
Local Canonical rcf_pseudoMetricType :=
  [pseudoMetricType R of R for [pseudoMetricType R of R^o]].
End rcfType.

Section archiFieldType.
Variable (R : archiFieldType).
Local Canonical archiField_pointedType :=
  [pointedType of R for [pointedType of R^o]].
Local Canonical archiField_filteredType :=
  [filteredType R of R for [filteredType R of R^o]].
Local Canonical archiField_topologicalType :=
  [topologicalType of R for [topologicalType of R^o]].
Local Canonical archiField_uniformType :=
  [uniformType of R for [uniformType of R^o]].
Local Canonical archiField_pseudoMetricType :=
  [pseudoMetricType R of R for [pseudoMetricType R of R^o]].
End archiFieldType.

Section realFieldType.
Variable (R : realFieldType).
Local Canonical realField_pointedType :=
  [pointedType of R for [pointedType of R^o]].
Local Canonical realField_filteredType :=
  [filteredType R of R for [filteredType R of R^o]].
Local Canonical realField_topologicalType :=
  [topologicalType of R for [topologicalType of R^o]].
Local Canonical realField_uniformType :=
  [uniformType of R for [uniformType of R^o]].
Local Canonical realField_pseudoMetricType :=
  [pseudoMetricType R of R for [pseudoMetricType R of R^o]].
Definition pointed_latticeType := [latticeType of realField_pointedType].
Definition pointed_distrLatticeType :=
  [distrLatticeType of realField_pointedType].
Definition pointed_orderType := [orderType of realField_pointedType].
Definition pointed_realDomainType :=
  [realDomainType of realField_pointedType].
Definition filtered_latticeType := [latticeType of realField_filteredType].
Definition filtered_distrLatticeType :=
  [distrLatticeType of realField_filteredType].
Definition filtered_orderType := [orderType of realField_filteredType].
Definition filtered_realDomainType :=
  [realDomainType of realField_filteredType].
Definition topological_latticeType :=
  [latticeType of realField_topologicalType].
Definition topological_distrLatticeType :=
  [distrLatticeType of realField_topologicalType].
Definition topological_orderType := [orderType of realField_topologicalType].
Definition topological_realDomainType :=
  [realDomainType of realField_topologicalType].
Definition uniform_latticeType := [latticeType of realField_uniformType].
Definition uniform_distrLatticeType :=
  [distrLatticeType of realField_uniformType].
Definition uniform_orderType := [orderType of realField_uniformType].
Definition uniform_realDomainType := [realDomainType of realField_uniformType].
Definition pseudoMetric_latticeType :=
  [latticeType of realField_pseudoMetricType].
Definition pseudoMetric_distrLatticeType :=
  [distrLatticeType of realField_pseudoMetricType].
Definition pseudoMetric_orderType := [orderType of realField_pseudoMetricType].
Definition pseudoMetric_realDomainType :=
  [realDomainType of realField_pseudoMetricType].
End realFieldType.

Section numClosedFieldType.
Variable (R : numClosedFieldType).
Local Canonical numClosedField_pointedType :=
  [pointedType of R for [pointedType of R^o]].
Local Canonical numClosedField_filteredType :=
  [filteredType R of R for [filteredType R of R^o]].
Local Canonical numClosedField_topologicalType :=
  [topologicalType of R for [topologicalType of R^o]].
Local Canonical numClosedField_uniformType :=
  [uniformType of R for [uniformType of R^o]].
Local Canonical numClosedField_pseudoMetricType :=
  [pseudoMetricType R of R for [pseudoMetricType R of R^o]].
Definition pointed_decFieldType :=
  [decFieldType of numClosedField_pointedType].
Definition pointed_closedFieldType :=
  [closedFieldType of numClosedField_pointedType].
Definition filtered_decFieldType :=
  [decFieldType of numClosedField_filteredType].
Definition filtered_closedFieldType :=
  [closedFieldType of numClosedField_filteredType].
Definition topological_decFieldType :=
  [decFieldType of numClosedField_topologicalType].
Definition topological_closedFieldType :=
  [closedFieldType of numClosedField_topologicalType].
Definition uniform_decFieldType := [decFieldType of numClosedField_uniformType].
Definition uniform_closedFieldType :=
  [closedFieldType of numClosedField_uniformType].
Definition pseudoMetric_decFieldType :=
  [decFieldType of numClosedField_pseudoMetricType].
Definition pseudoMetric_closedFieldType :=
  [closedFieldType of numClosedField_pseudoMetricType].
End numClosedFieldType.

Section numFieldType.
Variable (R : numFieldType).
Local Canonical numField_pointedType :=
  [pointedType of R for [pointedType of R^o]].
Local Canonical numField_filteredType :=
  [filteredType R of R for [filteredType R of R^o]].
Local Canonical numField_topologicalType :=
  [topologicalType of R for [topologicalType of R^o]].
Local Canonical numField_uniformType :=
  [uniformType of R for [uniformType of R^o]].
Local Canonical numField_pseudoMetricType :=
  [pseudoMetricType R of R for [pseudoMetricType R of R^o]].
Definition pointed_ringType := [ringType of numField_pointedType].
Definition pointed_comRingType := [comRingType of numField_pointedType].
Definition pointed_unitRingType := [unitRingType of numField_pointedType].
Definition pointed_comUnitRingType := [comUnitRingType of numField_pointedType].
Definition pointed_idomainType := [idomainType of numField_pointedType].
Definition pointed_fieldType := [fieldType of numField_pointedType].
Definition pointed_porderType := [porderType of numField_pointedType].
Definition pointed_numDomainType := [numDomainType of numField_pointedType].
Definition filtered_ringType := [ringType of numField_filteredType].
Definition filtered_comRingType := [comRingType of numField_filteredType].
Definition filtered_unitRingType := [unitRingType of numField_filteredType].
Definition filtered_comUnitRingType :=
  [comUnitRingType of numField_filteredType].
Definition filtered_idomainType := [idomainType of numField_filteredType].
Definition filtered_fieldType := [fieldType of numField_filteredType].
Definition filtered_porderType := [porderType of numField_filteredType].
Definition filtered_numDomainType := [numDomainType of numField_filteredType].
Definition topological_ringType := [ringType of numField_topologicalType].
Definition topological_comRingType := [comRingType of numField_topologicalType].
Definition topological_unitRingType :=
  [unitRingType of numField_topologicalType].
Definition topological_comUnitRingType :=
  [comUnitRingType of numField_topologicalType].
Definition topological_idomainType := [idomainType of numField_topologicalType].
Definition topological_fieldType := [fieldType of numField_topologicalType].
Definition topological_porderType := [porderType of numField_topologicalType].
Definition topological_numDomainType :=
  [numDomainType of numField_topologicalType].
Definition uniform_ringType := [ringType of numField_uniformType].
Definition uniform_comRingType := [comRingType of numField_uniformType].
Definition uniform_unitRingType := [unitRingType of numField_uniformType].
Definition uniform_comUnitRingType := [comUnitRingType of numField_uniformType].
Definition uniform_idomainType := [idomainType of numField_uniformType].
Definition uniform_fieldType := [fieldType of numField_uniformType].
Definition uniform_porderType := [porderType of numField_uniformType].
Definition uniform_numDomainType := [numDomainType of numField_uniformType].
Definition pseudoMetric_ringType := [ringType of numField_pseudoMetricType].
Definition pseudoMetric_comRingType :=
  [comRingType of numField_pseudoMetricType].
Definition pseudoMetric_unitRingType :=
  [unitRingType of numField_pseudoMetricType].
Definition pseudoMetric_comUnitRingType :=
  [comUnitRingType of numField_pseudoMetricType].
Definition pseudoMetric_idomainType :=
  [idomainType of numField_pseudoMetricType].
Definition pseudoMetric_fieldType := [fieldType of numField_pseudoMetricType].
Definition pseudoMetric_porderType := [porderType of numField_pseudoMetricType].
Definition pseudoMetric_numDomainType :=
  [numDomainType of numField_pseudoMetricType].
End numFieldType.

Module Export Exports.

Canonical real_pointedType.
Canonical real_filteredType.
Canonical real_topologicalType.
Canonical real_uniformType.
Canonical real_pseudoMetricType.
Coercion real_pointedType : realType >-> pointedType.
Coercion real_filteredType : realType >-> filteredType.
Coercion real_topologicalType : realType >-> topologicalType.
Coercion real_uniformType : realType >-> uniformType.
Coercion real_pseudoMetricType : realType >-> pseudoMetricType.

Canonical rcf_pointedType.
Canonical rcf_filteredType.
Canonical rcf_topologicalType.
Canonical rcf_uniformType.
Canonical rcf_pseudoMetricType.
Coercion rcf_pointedType : rcfType >-> pointedType.
Coercion rcf_filteredType : rcfType >-> filteredType.
Coercion rcf_topologicalType : rcfType >-> topologicalType.
Coercion rcf_uniformType : rcfType >-> uniformType.
Coercion rcf_pseudoMetricType : rcfType >-> pseudoMetricType.

Canonical archiField_pointedType.
Canonical archiField_filteredType.
Canonical archiField_topologicalType.
Canonical archiField_uniformType.
Canonical archiField_pseudoMetricType.
Coercion archiField_pointedType : archiFieldType >-> pointedType.
Coercion archiField_filteredType : archiFieldType >-> filteredType.
Coercion archiField_topologicalType : archiFieldType >-> topologicalType.
Coercion archiField_uniformType : archiFieldType >-> uniformType.
Coercion archiField_pseudoMetricType : archiFieldType >-> pseudoMetricType.

Canonical realField_pointedType.
Canonical realField_filteredType.
Canonical realField_topologicalType.
Canonical realField_uniformType.
Canonical realField_pseudoMetricType.
Canonical pointed_latticeType.
Canonical pointed_distrLatticeType.
Canonical pointed_orderType.
Canonical pointed_realDomainType.
Canonical filtered_latticeType.
Canonical filtered_distrLatticeType.
Canonical filtered_orderType.
Canonical filtered_realDomainType.
Canonical topological_latticeType.
Canonical topological_distrLatticeType.
Canonical topological_orderType.
Canonical topological_realDomainType.
Canonical uniform_latticeType.
Canonical uniform_distrLatticeType.
Canonical uniform_orderType.
Canonical uniform_realDomainType.
Canonical pseudoMetric_latticeType.
Canonical pseudoMetric_distrLatticeType.
Canonical pseudoMetric_orderType.
Canonical pseudoMetric_realDomainType.
Coercion realField_pointedType : realFieldType >-> pointedType.
Coercion realField_filteredType : realFieldType >-> filteredType.
Coercion realField_topologicalType : realFieldType >-> topologicalType.
Coercion realField_uniformType : realFieldType >-> uniformType.
Coercion realField_pseudoMetricType : realFieldType >-> pseudoMetricType.

Canonical numClosedField_pointedType.
Canonical numClosedField_filteredType.
Canonical numClosedField_topologicalType.
Canonical numClosedField_uniformType.
Canonical numClosedField_pseudoMetricType.
Canonical pointed_decFieldType.
Canonical pointed_closedFieldType.
Canonical filtered_decFieldType.
Canonical filtered_closedFieldType.
Canonical topological_decFieldType.
Canonical topological_closedFieldType.
Canonical uniform_decFieldType.
Canonical uniform_closedFieldType.
Canonical pseudoMetric_decFieldType.
Canonical pseudoMetric_closedFieldType.
Coercion numClosedField_pointedType : numClosedFieldType >-> pointedType.
Coercion numClosedField_filteredType : numClosedFieldType >-> filteredType.
Coercion numClosedField_topologicalType :
  numClosedFieldType >-> topologicalType.
Coercion numClosedField_uniformType : numClosedFieldType >-> uniformType.
Coercion numClosedField_pseudoMetricType :
  numClosedFieldType >-> pseudoMetricType.

Canonical numField_pointedType.
Canonical numField_filteredType.
Canonical numField_topologicalType.
Canonical numField_uniformType.
Canonical numField_pseudoMetricType.
Canonical pointed_ringType.
Canonical pointed_comRingType.
Canonical pointed_unitRingType.
Canonical pointed_comUnitRingType.
Canonical pointed_idomainType.
Canonical pointed_fieldType.
Canonical pointed_porderType.
Canonical pointed_numDomainType.
Canonical filtered_ringType.
Canonical filtered_comRingType.
Canonical filtered_unitRingType.
Canonical filtered_comUnitRingType.
Canonical filtered_idomainType.
Canonical filtered_fieldType.
Canonical filtered_porderType.
Canonical filtered_numDomainType.
Canonical topological_ringType.
Canonical topological_comRingType.
Canonical topological_unitRingType.
Canonical topological_comUnitRingType.
Canonical topological_idomainType.
Canonical topological_fieldType.
Canonical topological_porderType.
Canonical topological_numDomainType.
Canonical uniform_ringType.
Canonical uniform_comRingType.
Canonical uniform_unitRingType.
Canonical uniform_comUnitRingType.
Canonical uniform_idomainType.
Canonical uniform_fieldType.
Canonical uniform_porderType.
Canonical uniform_numDomainType.
Canonical pseudoMetric_ringType.
Canonical pseudoMetric_comRingType.
Canonical pseudoMetric_unitRingType.
Canonical pseudoMetric_comUnitRingType.
Canonical pseudoMetric_idomainType.
Canonical pseudoMetric_fieldType.
Canonical pseudoMetric_porderType.
Canonical pseudoMetric_numDomainType.
Coercion numField_pointedType : numFieldType >-> pointedType.
Coercion numField_filteredType : numFieldType >-> filteredType.
Coercion numField_topologicalType : numFieldType >-> topologicalType.
Coercion numField_uniformType : numFieldType >-> uniformType.
Coercion numField_pseudoMetricType : numFieldType >-> pseudoMetricType.
End Exports.

End numFieldTopology.
Import numFieldTopology.Exports.

Global Instance Proper_dnbhs_regular_numFieldType (R : numFieldType) (x : R^o) :
  ProperFilter x^'.
Admitted.

Lemma Rhausdorff (R : realFieldType) : hausdorff_space R.
Admitted.

Section RestrictedUniformTopology.
Context {U : choiceType} (A : set U) {V : uniformType} .

Definition fct_RestrictedUniform := let _ := A in U -> V.
Definition fct_RestrictedUniformTopology :=
  @weak_uniformType
    ([pointedType of @fct_RestrictedUniform])
    (fct_uniformType [choiceType of { x : U | x \in A }] V)
    (@sigL U V A).

Canonical fct_RestrictUniformFilteredType:=
  [filteredType fct_RestrictedUniform of
      fct_RestrictedUniform for
      fct_RestrictedUniformTopology].

Canonical fct_RestrictUniformTopologicalType :=
  [topologicalType of fct_RestrictedUniform for fct_RestrictedUniformTopology].

Canonical fct_restrictedUniformType :=
  [uniformType of fct_RestrictedUniform for fct_RestrictedUniformTopology].

Lemma uniform_nbhs (f : fct_RestrictedUniformTopology) P:
  nbhs f P <-> (exists E, entourage E /\
    [set h | forall y, A y -> E(f y, h y)] `<=` P).
Admitted.

Lemma uniform_entourage :
  @entourage fct_restrictedUniformType =
  filter_from
    (@entourage V)
    (fun P => [set fg | forall t : U, A t -> P (fg.1 t, fg.2 t)]).
Admitted.

End RestrictedUniformTopology.

Notation "{ 'uniform`' A -> V }" := (@fct_RestrictedUniform _ A V) :
  classical_set_scope.
Notation "{ 'uniform' U -> V }" := ({uniform` [set: U] -> V}) :
  classical_set_scope.

Notation "{ 'uniform' A , F --> f }" :=
  (cvg_to [filter of F]
     (filter_of (Phantom (fct_RestrictedUniform A) f)))
   : classical_set_scope.
Notation "{ 'uniform' , F --> f }" :=
  (cvg_to [filter of F]
     (filter_of (Phantom (fct_RestrictedUniform setT) f)))
   : classical_set_scope.

Lemma restricted_cvgE {U : choiceType} {V : uniformType}
    (F : set (set (U -> V))) A (f : U -> V) :
  {uniform A, F --> f} = (F --> (f : {uniform` A -> V})).
Admitted.

Definition fct_Pointwise U (V: topologicalType) := U -> V.

Definition fct_PointwiseTopology (U : Type) (V : topologicalType) :=
  @product_topologicalType U (fun=> V).

Canonical fct_PointwiseFilteredType (U : Type) (V : topologicalType) :=
  [filteredType @fct_Pointwise U V of
     @fct_Pointwise U V for
     @fct_PointwiseTopology U V].

Canonical fct_PointwiseTopologicalType (U : Type) (V : topologicalType) :=
  [topologicalType of
     @fct_Pointwise U V for
     @fct_PointwiseTopology U V].

Notation "{ 'ptws' U -> V }" := (@fct_Pointwise U V).

Notation "{ 'ptws' , F --> f }" :=
  (cvg_to [filter of F] (filter_of (Phantom (@fct_Pointwise _ _) f)))
  : classical_set_scope.

Lemma pointwise_cvgE {U : Type} {V : topologicalType}
    (F : set (set(U -> V))) (A : set U) (f : U -> V) :
  {ptws, F --> f} = (F --> (f : {ptws U -> V})).
Admitted.

Section UniformCvgLemmas.
Context {U : choiceType} {V : uniformType}.

Lemma uniform_set1 F (f : U -> V) (x : U) :
  Filter F -> {uniform [set x], F --> f} = ((g x) @[g --> F] --> f x).
Admitted.

Lemma uniform_subset_nbhs (f : U -> V) (A B : set U) :
  B `<=` A -> nbhs (f : {uniform` A -> V}) `=>` nbhs (f : {uniform` B -> V}).
Admitted.

Lemma uniform_subset_cvg (f : U -> V) (A B : set U) F :
  Filter F -> B `<=` A -> {uniform A, F --> f} -> {uniform B, F --> f}.
Admitted.

Lemma pointwise_uniform_cvg  (f : U -> V) (F : set (set (U -> V))) :
  Filter F -> {uniform, F --> f} -> {ptws, F --> f}.
Admitted.

Lemma cvg_sigL (A : set U) (f : U -> V) (F : set (set (U -> V))) :
    Filter F ->
  {uniform A, F --> f} <->
  {uniform, sigL A @ F --> sigL A f}.
Admitted.

Lemma eq_in_close (A : set U) (f g : {uniform` A -> V}) :
  {in A, f =1 g} -> close f g.
Admitted.

Lemma hausdorrf_close_eq_in (A : set U) (f g : {uniform` A -> V}) :
  hausdorff_space V -> close f g = {in A, f =1 g}.
Admitted.

Lemma uniform_restrict_cvg
    (F : set (set (U -> V))) (f : U -> V) A : Filter F ->
  {uniform A, F --> f} <-> {uniform, restrict A @ F --> restrict A f}.
Admitted.

Lemma uniform_nbhsT (f : U -> V) :
  (nbhs (f : {uniform U -> V})) = nbhs (f : fct_topologicalType U V).
Admitted.

Lemma cvg_uniformU (f : U -> V) (F : set (set (U -> V))) A B : Filter F ->
  {uniform A, F --> f} -> {uniform B, F --> f} ->
  {uniform (A `|` B), F --> f}.
Admitted.

Lemma cvg_uniform_set0 (F : set (set (U -> V))) (f : U -> V) : Filter F ->
  {uniform set0, F --> f}.
Admitted.

Definition fct_UniformFamily (fam : (set U) -> Prop) := U -> V.

Definition family_cvg_uniformType (fam: set U -> Prop) :=
  @sup_uniformType  _
    (sigT fam)
    (fun k => Uniform.class (@fct_restrictedUniformType U (projT1 k) V)).

Canonical fct_UniformFamilyFilteredType fam :=
  [filteredType fct_UniformFamily fam of
    fct_UniformFamily fam for
    family_cvg_uniformType fam].

Canonical fct_UniformFamilyTopologicalType fam :=
  [topologicalType of
     fct_UniformFamily fam for
     family_cvg_uniformType fam].

Canonical fct_UniformFamilyUniformType fam :=
  [uniformType of
     fct_UniformFamily fam for
     family_cvg_uniformType fam].

Local Notation "{ 'family' fam , F --> f }" :=
  (cvg_to [filter of F] (filter_of (Phantom (fct_UniformFamily fam) f)))
  : classical_set_scope.

Lemma fam_cvgP (fam : set U -> Prop) (F : set (set (U -> V))) (f : U -> V) :
  Filter F -> {family fam, F --> f} <->
  (forall A : set U, fam A -> {uniform A, F --> f }).
Admitted.

Lemma family_cvg_subset (famA famB : set U -> Prop) (F : set (set (U -> V)))
    (f : U -> V) : Filter F ->
  famA `<=` famB -> {family famB, F --> f} -> {family famA, F --> f}.
Admitted.

Lemma family_cvg_finite_covers (famA famB : set U -> Prop)
  (F : set (set (U -> V))) (f : U -> V) : Filter F ->
  (forall P, famA P ->
    exists (I : choiceType) f,
      (forall i, famB (f i)) /\ finite_subset_cover [set: I] f P) ->
  {family famB, F --> f} -> {family famA, F --> f}.
Admitted.

End UniformCvgLemmas.

Notation "{ 'family' fam , U -> V }" :=  (@fct_UniformFamily U V fam).
Notation "{ 'family' fam , F --> f }" :=
  (cvg_to [filter of F] (filter_of (Phantom (fct_UniformFamily fam) f)))
  : classical_set_scope.

Lemma fam_cvgE {U : choiceType} {V : uniformType} (F : set (set (U -> V)))
    (f : U -> V) fam :
  {family fam, F --> f} = (F --> (f : {family fam, U -> V})).
Admitted.

Lemma fam_nbhs {U : choiceType} {V : uniformType} (fam : set U -> Prop)
    (A : set U) (E : set (V * V)) (f : {family fam, U -> V}) :
  entourage E -> fam A -> nbhs f [set g | forall y, A y -> E (f y, g y)].
Admitted.

Definition compactly_in {U : topologicalType} (A : set U) :=
  [set B | B `<=` A /\ compact B].

Lemma compact_cvg_within_compact {U : topologicalType} {V : uniformType}
    (C : set U) (F : set (set (U -> V))) (f : U -> V) :
  Filter F -> compact C ->
  {uniform C, F --> f} <-> {family compactly_in C, F --> f}.
Admitted.

Global Instance Proper_dnbhs_numFieldType (R : numFieldType) (x : R) :
  ProperFilter x^'.
Admitted.

Definition dense (T : topologicalType) (S : set T) :=
  forall (O : set T), O !=set0 -> open O -> O `&` S !=set0.

Lemma denseNE (T : topologicalType) (S : set T) : ~ dense S ->
  exists O, (exists x, open_nbhs x O) /\ (O `&` S = set0).
Admitted.

Lemma dense_rat (R : realType) : dense (@ratr R @` setT).
Admitted.

Section weak_pseudoMetric.
Context {R : realType} (pS : pointedType) (U : pseudoMetricType R) .
Variable (f : pS -> U).

Let S := weak_uniformType f.

Definition weak_ball (x : S) (r : R) (y : S) := ball (f x) r (f y).

Program Definition weak_pseudoMetricType_mixin :=
  @PseudoMetric.Mixin R S entourage weak_ball
  _ _ _ _.
Admit Obligations.
Admit Obligations.
Admit Obligations.
Admit Obligations.

Definition weak_pseudoMetricType :=
  PseudoMetricType S weak_pseudoMetricType_mixin.

Lemma weak_ballE (e : R) (x : weak_pseudoMetricType) :
  f@^-1` (ball (f x) e) = ball x e.
Admitted.

End weak_pseudoMetric.

Lemma compact_second_countable {R : realType} {T : pseudoMetricType R} :
  compact [set: T] -> @second_countable T.
Admitted.

Section countable_uniform.
Context {R : realType} {T : uniformType}.

Hypothesis cnt_unif : @countable_uniformity T.

Let f_ := projT1 (cid2 (iffLR countable_uniformityP cnt_unif)).

Local Lemma countableBase : forall A, entourage A -> exists N, f_ N `<=` A.
Admitted.

Let entF : forall n, entourage (f_ n).
Admitted.
Local Fixpoint g_ (n : nat) : set (T * T). exact (if n is S n then let W := split_ent (split_ent (g_ n)) `&` f_ n in W `&` W^-1
  else [set: T*T]). Defined.

Let entG (n : nat) : entourage (g_ n).
Admitted.

Local Lemma symG (n : nat) : ((g_ n)^-1)%classic = g_ n.
Admitted.

Local Lemma descendG1 n : g_ n.+1 `<=` g_ n.
Admitted.

Local Lemma descendG (n m: nat) : (m <= n)%N -> g_ n `<=` g_ m.
Admitted.

Local Lemma splitG3 n : g_ n.+1 \; g_ n.+1 \; g_ n.+1 `<=` g_ n.
Admitted.

Local Lemma gsubf n : g_ n.+1 `<=` f_ n.
Admitted.

Local Lemma countableBaseG A : entourage A -> exists N, g_ N `<=` A.
Admitted.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Definition distN (e : R) : nat. exact (`|floor e^-1|%N). Defined.

Local Lemma distN0 : distN 0 = 0%N.
Admitted.

Local Lemma distN_nat (n : nat): distN (n%:R^-1) = n.
Admitted.

Local Lemma distN_le e1 e2 : e1 > 0 -> e1 <= e2 -> (distN e2 <= distN e1)%N.
Admitted.

Local Fixpoint n_step_ball n x e z :=
  if n is n.+1 then exists y d1 d2,
    [/\ n_step_ball n x d1 y,
        0 < d1,
        0 < d2,
        g_ (distN d2) (y, z) &
        d1 + d2 = e]
  else e > 0 /\ g_ (distN e) (x, z).

Local Definition step_ball x e z := exists i, (n_step_ball i x e z).

Local Lemma n_step_ball_pos n x e z : n_step_ball n x e z -> 0 < e.
Admitted.

Local Lemma step_ball_pos x e z : step_ball x e z -> 0 < e.
Admitted.

Local Lemma entourage_nball e :
  0 < e -> entourage [set xy | step_ball xy.1 e xy.2].
Admitted.

Local Lemma n_step_ball_center x e : 0 < e -> n_step_ball 0 x e x.
Admitted.

Local Lemma step_ball_center x e : 0 < e -> step_ball x e x.
Admitted.

Local Lemma n_step_ball_triangle n m x y z d1 d2 :
  n_step_ball n x d1 y ->
  n_step_ball m y d2 z ->
  n_step_ball (n + m).+1 x (d1 + d2) z.
Admitted.

Local Lemma step_ball_triangle x y z d1 d2 :
  step_ball x d1 y -> step_ball y d2 z -> step_ball x (d1 + d2) z.
Admitted.

Local Lemma n_step_ball_sym n x y e :
  n_step_ball n x e y -> n_step_ball n y e x.
Admitted.

Local Lemma step_ball_sym x y e : step_ball x e y -> step_ball y e x.
Admitted.

Local Lemma n_step_ball_le n x e1 e2 :
  e1 <= e2 -> n_step_ball n x e1 `<=` n_step_ball n x e2.
Admitted.

Local Lemma step_ball_le x e1 e2 :
  e1 <= e2 -> step_ball x e1 `<=` step_ball x e2.
Admitted.

Local Lemma distN_half (n : nat) : n.+1%:R^-1 / (2:R) <= n.+2%:R^-1.
Admitted.

Local Lemma split_n_step_ball n x e1 e2 z :
  0 < e1 -> 0 < e2 -> n_step_ball n.+1 x (e1 + e2) z ->
    exists t1 t2 a b,
    [/\
      n_step_ball a x e1 t1,
      n_step_ball 0 t1 (e1 + e2) t2,
      n_step_ball b t2 e2 z &
      (a + b = n)%N
    ].
Admitted.

Local Lemma n_step_ball_le_g x n :
  n_step_ball 0 x n%:R^-1 `<=` [set y | g_ n (x,y)].
Admitted.

Local Lemma subset_n_step_ball n x N :
  n_step_ball n x N.+1%:R^-1 `<=` [set y | (g_ N) (x, y)].
Admitted.

Local Lemma subset_step_ball x N :
  step_ball x N.+1%:R^-1 `<=` [set y | (g_ N) (x, y)].
Admitted.

Local Lemma step_ball_entourage : entourage = entourage_ step_ball.
Admitted.

Definition countable_uniform_pseudoMetricType_mixin := PseudoMetric.Mixin
  step_ball_center step_ball_sym step_ball_triangle step_ball_entourage.

Lemma countable_uniform_bounded (x y : T) :
  let U := PseudoMetricType _ countable_uniform_pseudoMetricType_mixin
  in @ball _ U x 2 y.
Admitted.

End countable_uniform.

Section sup_pseudometric.
Variable (R : realType) (T : pointedType) (Ii : Type).
Variable (Tc : Ii -> PseudoMetric.class_of R T).

Hypothesis Icnt : countable [set: Ii].
Let I : choiceType. exact (classicType_choiceType Ii). Defined.
Let TS := fun i => PseudoMetric.Pack (Tc i).

Definition countable_uniformityT := @countable_sup_ent T Ii Tc Icnt
  (fun i => @countable_uniformity_metric _ (TS i)).

Definition sup_pseudoMetric_mixin := @countable_uniform_pseudoMetricType_mixin R
  (sup_uniformType Tc) countable_uniformityT.

Definition sup_pseudoMetricType :=
  PseudoMetricType (sup_uniformType Tc) sup_pseudoMetric_mixin.

End sup_pseudometric.

Section product_pseudometric.
Variable (R : realType) (Ii : countType) (Tc : Ii -> pseudoMetricType R).

Hypothesis Icnt : countable [set: Ii].

Definition product_pseudoMetricType :=
  sup_pseudoMetricType (fun i => PseudoMetric.class
    (weak_pseudoMetricType (fun f : dep_arrow_pointedType Tc => f i)))
    Icnt.

End product_pseudometric.

Definition subspace {T : Type} (A : set T) := T.
Arguments subspace {T} _ : simpl never.

Definition incl_subspace {T A} (x : subspace A) : T := x.

Section Subspace.
Context {T : topologicalType} (A : set T).
Definition nbhs_subspace (x : subspace A) : set (set (subspace A)). exact (if x \in A then within A (nbhs x) else globally [set x]). Defined.

Variant nbhs_subspace_spec x : Prop -> Prop -> bool -> set (set T) -> Type :=
  | WithinSubspace :
      A x -> nbhs_subspace_spec x True False true (within A (nbhs x))
  | WithoutSubspace :
    ~ A x -> nbhs_subspace_spec x False True false (globally [set x]).

Lemma nbhs_subspaceP x :
  nbhs_subspace_spec x (A x) (~ A x) (x \in A) (nbhs_subspace x).
Admitted.

Lemma nbhs_subspace_in (x : T) : A x -> within A (nbhs x) = nbhs_subspace x.
Admitted.

Lemma nbhs_subspace_out (x : T) : ~ A x -> globally [set x] = nbhs_subspace x.
Admitted.

Lemma nbhs_subspace_filter (x : subspace A) : ProperFilter (nbhs_subspace x).
Admitted.

Definition subspace_pointedType := PointedType (subspace A) point.

Canonical subspace_filteredType :=
  FilteredType (subspace A) (subspace A) nbhs_subspace.

Program Definition subspace_topologicalMixin :
  Topological.mixin_of (nbhs_subspace) := @topologyOfFilterMixin
    (subspace A) nbhs_subspace nbhs_subspace_filter _ _.
Admit Obligations.
Admit Obligations.

Canonical subspace_topologicalType :=
  TopologicalType (subspace A) subspace_topologicalMixin.

Lemma subspace_cvgP (F : set (set T)) (x : T) :
  Filter F -> A x ->
  (F --> (x : subspace A)) <-> (F --> within A (nbhs x)).
Admitted.

Lemma subspace_continuousP {S : topologicalType} (f : T -> S) :
  continuous (f : subspace A -> S) <->
  (forall x, A x -> f @ within A (nbhs x) --> f x) .
Admitted.

Lemma subspace_eq_continuous {S : topologicalType} (f g : subspace A -> S) :
  {in A, f =1 g} -> continuous f -> continuous g.
Admitted.

Lemma continuous_subspace_in {U : topologicalType} (f : subspace A -> U) :
  continuous f = {in A, continuous f}.
Admitted.

Lemma nbhs_subspace_interior (x : T) :
  A^° x -> nbhs x = (nbhs (x : subspace A)).
Admitted.

Lemma nbhs_subspace_ex (U : set T) (x : T) : A x ->
  nbhs (x : subspace A) U <->
  exists2 V, nbhs (x : T) V & U `&` A = V `&` A.
Admitted.

Lemma incl_subspace_continuous : continuous incl_subspace.
Admitted.

Section SubspaceOpen.

Lemma open_subspace1out (x : subspace A) : ~ A x -> open [set x].
Admitted.

Lemma open_subspace_out (U : set (subspace A)) : U `<=` ~` A -> open U.
Admitted.

Lemma open_subspaceT : open (A : set (subspace A)).
Admitted.

Lemma open_subspaceIT (U : set (subspace A)) : open (U `&` A) = open U.
Admitted.

Lemma open_subspaceTI (U : set (subspace A)) :
  open (A `&` U : set (subspace A)) = open U.
Admitted.

Lemma closed_subspaceT : closed (A : set (subspace A)).
Admitted.

Lemma open_subspaceP (U : set T) :
  open (U : set (subspace A)) <->
  exists V, open (V : set T) /\ V `&` A = U `&` A.
Admitted.

Lemma closed_subspaceP (U : set T) :
  closed (U : set (subspace A)) <->
  exists V, closed (V : set T) /\ V `&` A = U `&` A.
Admitted.

Lemma open_subspaceW (U : set T) :
  open (U : set T) -> open (U : set (subspace A)).
Admitted.

Lemma closed_subspaceW (U : set T) :
  closed (U : set T) -> closed (U : set (subspace A)).
Admitted.

Lemma open_setIS (U : set (subspace A)) : open A ->
  open (U `&` A : set T) = open U.
Admitted.

Lemma open_setSI (U : set (subspace A)) : open A -> open (A `&` U) = open U.
Admitted.

Lemma closed_setIS (U : set (subspace A)) : closed A ->
  closed (U `&` A : set T) = closed U.
Admitted.

Lemma closed_setSI (U : set (subspace A)) :
  closed A -> closed (A `&` U) = closed U.
Admitted.

Lemma closure_subspaceW (U : set T) :
  U `<=` A -> closure (U : set (subspace A)) = closure (U : set T) `&` A.
Admitted.

Lemma subspace_hausdorff :
  hausdorff_space T -> hausdorff_space [topologicalType of subspace A].
Admitted.
End SubspaceOpen.

Lemma compact_subspaceIP (U : set T) :
  compact (U `&` A : set (subspace A)) <-> compact (U `&` A : set T).
Admitted.

Lemma clopen_connectedP : connected A <->
  (forall U, @clopen (subspace_topologicalType) U ->
    U `<=` A  -> U !=set0 -> U = A).
Admitted.

End Subspace.
Global Instance subspace_filter {T : topologicalType}
     (A : set T) (x : subspace A) :
   Filter (nbhs_subspace x). exact (nbhs_subspace_filter x). Defined.
Global Instance subspace_proper_filter {T : topologicalType}
     (A : set T) (x : subspace A) :
   ProperFilter (nbhs_subspace x). exact (nbhs_subspace_filter x). Defined.

Notation "{ 'within' A , 'continuous' f }" := (forall x,
  cvg_to [filter of fmap f (filter_of (Phantom (subspace A) x))]
         [filter of f x]) : classical_set_scope.

Section SubspaceRelative.
Context {T : topologicalType}.
Implicit Types (U : topologicalType) (A B : set T).

Lemma nbhs_subspace_subset A B (x : T) :
  A `<=` B -> nbhs (x : subspace B) `<=` nbhs (x : subspace A).
Admitted.

Lemma continuous_subspaceW {U} A B (f : T -> U) :
  A `<=` B ->
  {within B, continuous f} -> {within A, continuous f}.
Admitted.

Lemma nbhs_subspaceT (x : T) : nbhs (x : subspace setT) = nbhs x.
Admitted.

Lemma continuous_subspaceT_for {U} A (f : T -> U) (x : T) :
  A x -> {for x, continuous f} -> {for x, continuous (f : subspace A -> U)}.
Admitted.

Lemma continuous_in_subspaceT {U} A (f : T -> U) :
  {in A, continuous f} -> {within A, continuous f}.
Admitted.

Lemma continuous_subspaceT {U} A (f : T -> U) :
  continuous f -> {within A, continuous f}.
Admitted.

Lemma continuous_open_subspace {U} A (f : T -> U) :
  open A -> {within A, continuous f} = {in A, continuous f}.
Admitted.

Lemma continuous_inP {U} A (f : T -> U) : open A ->
  {in A, continuous f} <-> forall X, open X -> open (A `&` f @^-1` X).
Admitted.

Lemma withinU_continuous {U} A B (f : T -> U) : closed A -> closed B ->
  {within A, continuous f} -> {within B, continuous f} ->
  {within A `|` B, continuous f}.
Admitted.

Lemma subspaceT_continuous {U} A (B : set U) (f : {fun A >-> B}) :
  {within A, continuous f} -> continuous (f : subspace A -> subspace B).
Admitted.

Lemma continuous_subspace0 {U} (f : T -> U) : {within set0, continuous f}.
Admitted.

Lemma continuous_subspace1 {U} (a : T) (f : T -> U) :
  {within [set a], continuous f}.
Admitted.

End SubspaceRelative.

Section SubspaceUniform.
Local Notation "A ^-1" := ([set xy | A (xy.2, xy.1)]) : classical_set_scope.
Context {X : uniformType} (A : set X).

Definition subspace_ent :=
  filter_from (@entourage X)
  (fun E => [set xy | (xy.1 = xy.2) \/ (A xy.1 /\ A xy.2 /\ E xy)]).

Program Definition subspace_uniformMixin :=
  @Uniform.Mixin (subspace A) (@nbhs_subspace _ _) subspace_ent _ _ _ _ _.
Admit Obligations.
Admit Obligations.
Admit Obligations.
Admit Obligations.
Admit Obligations.

Canonical subspace_uniformType :=
  UniformType (subspace A) subspace_uniformMixin.
End SubspaceUniform.

Section SubspacePseudoMetric.
Context {R : numDomainType} {X : pseudoMetricType R} (A : set X).

Definition subspace_ball (x : subspace A) (r : R) :=
  if x \in A then A `&` ball (x : X) r else [set x].

Program Definition subspace_pseudoMetricType_mixin :=
  @PseudoMetric.Mixin R (subspace A) (subspace_ent A) (subspace_ball)
  _ _ _ _.
Admit Obligations.
Admit Obligations.
Admit Obligations.
Admit Obligations.

Canonical subspace_pseudoMetricType :=
  PseudoMetricType (subspace A) subspace_pseudoMetricType_mixin.

End SubspacePseudoMetric.

Section SubspaceWeak.
Context {T : topologicalType} {U : pointedType}.
Variables (f : U -> T).

Let U' := weak_topologicalType f.

Lemma weak_subspace_open (A : set U') :
  open A -> open (f @` A : set (subspace (range f))).
Admitted.

End SubspaceWeak.

Definition separate_points_from_closed {I : Type} {T : topologicalType}
    {U_ : I -> topologicalType} (f_ : forall i, T -> U_ i) :=
  forall (U : set T) x,
  closed U -> ~ U x -> exists i, ~ (closure (f_ i @` U)) (f_ i x).

Section product_embeddings.
Context {I : choiceType} {T : topologicalType} {U_ : I -> topologicalType}.
Variable (f_ : forall i, T -> U_ i).

Hypothesis sepf : separate_points_from_closed f_.
Hypothesis ctsf : forall i, continuous (f_ i).

Let weakT := @sup_topologicalType T I
  (fun i => Topological.class (weak_topologicalType (f_ i))).

Let PU := product_topologicalType U_.

Local Notation sup_open := (@open weakT).
Local Notation "'weak_open' i" :=
  (@open (weak_topologicalType (f_ i))) (at level 0).
Local Notation natural_open := (@open T).

Lemma weak_sep_cvg (F : set (set T)) (x : T) :
  Filter F -> (F --> (x : T)) <-> (F --> (x : weakT)).
Admitted.

Lemma weak_sep_nbhsE x : @nbhs T T x = @nbhs T weakT x.
Admitted.

Lemma weak_sep_openE : @open T = @open weakT.
Admitted.
Definition join_product (x : T) : PU. exact (f_ ^~ x). Defined.

Lemma join_product_continuous : continuous join_product.
Admitted.

Local Notation prod_open :=
  (@open (subspace_topologicalType (range join_product))).

Lemma join_product_open (A : set T) : open A ->
  open ((join_product @` A) : set (subspace (range join_product))).
Admitted.

Lemma join_product_inj : accessible_space T -> set_inj [set: T] join_product.
Admitted.

Lemma join_product_weak : set_inj [set: T] join_product ->
  @open T = @open (weak_topologicalType join_product).
Admitted.

End product_embeddings.

Lemma continuous_compact {T U : topologicalType} (f : T -> U) A :
  {within A, continuous f} -> compact A -> compact (f @` A).
Admitted.

Lemma connected_continuous_connected (T U : topologicalType)
    (A : set T) (f : T -> U) :
  connected A -> {within A, continuous f} -> connected (f @` A).
Admitted.

Lemma uniform_limit_continuous {U : topologicalType} {V : uniformType}
    (F : set (set (U -> V))) (f : U -> V) :
  ProperFilter F -> (\forall g \near F, continuous (g : U -> V)) ->
  {uniform, F --> f} -> continuous f.
Admitted.

Lemma uniform_limit_continuous_subspace {U : topologicalType} {V : uniformType}
    (K : set U) (F : set (set (U -> V))) (f : subspace K -> V) :
  ProperFilter F -> (\forall g \near F, continuous (g : subspace K -> V)) ->
  {uniform K, F --> f} -> {within K, continuous f}.
Admitted.

Lemma continuous_localP {X Y : topologicalType} (f : X -> Y) :
  continuous f <->
  forall (x : X), \forall U \near powerset_filter_from (nbhs x),
    {within U, continuous f}.
Admitted.

Lemma totally_disconnected_prod (I : choiceType)
  (T : I -> topologicalType) (A : forall i, set (T i)) :
  (forall i, totally_disconnected (A i)) ->
  @totally_disconnected (product_topologicalType T)
    (fun f => forall i, A i (f i)).
Admitted.

Section UniformPointwise.
Context {U : topologicalType} {V : uniformType}.

Definition singletons {T : Type} := [set [set x] | x in [set: T]].

Lemma pointwise_cvg_family_singleton F (f: U -> V):
  Filter F -> {ptws, F --> f} = {family @singletons U, F --> f}.
Admitted.

Lemma pointwise_cvg_compact_family F (f : U -> V) :
  Filter F -> {family compact, F --> f} -> {ptws, F --> f}.
Admitted.

Lemma pointwise_cvgP F (f: U -> V):
  Filter F -> {ptws, F --> f} <-> forall (t : U), (fun g => g t) @ F --> f t.
Admitted.

End UniformPointwise.

Section gauges.

Let split_sym {T : uniformType} (W : set (T * T)) :=
  (split_ent W) `&` (split_ent W)^-1.

Section entourage_gauge.
Context {T : uniformType} (E : set (T * T)) (entE : entourage E).

Definition gauge :=
  filter_from [set: nat] (fun n => iter n split_sym (E `&` E^-1)).

Lemma iter_split_ent j : entourage (iter j split_sym (E `&` E^-1)).
Admitted.

Lemma gauge_ent A : gauge A -> entourage A.
Admitted.

Lemma gauge_filter : Filter gauge.
Admitted.

Lemma gauge_refl A : gauge A -> [set fg | fg.1 = fg.2] `<=` A.
Admitted.

Lemma gauge_inv A : gauge A -> gauge (A^-1)%classic.
Admitted.

Lemma gauge_split A : gauge A -> exists2 B, gauge B & B \; B `<=` A.
Admitted.

Definition gauge_uniformType_mixin :=
 UniformMixin gauge_filter gauge_refl gauge_inv gauge_split erefl.

Definition gauge_topologicalTypeMixin :=
  topologyOfEntourageMixin gauge_uniformType_mixin.

Definition gauge_filtered := FilteredType T T (nbhs_ gauge).
Definition gauge_topologicalType :=
  TopologicalType gauge_filtered gauge_topologicalTypeMixin.
Definition gauge_uniformType := UniformType
  gauge_topologicalType gauge_uniformType_mixin.

Lemma gauge_countable_uniformity : countable_uniformity gauge_uniformType.
Admitted.

Definition gauge_pseudoMetric_mixin {R : realType} :=
  @countable_uniform_pseudoMetricType_mixin R _ gauge_countable_uniformity.

Definition gauge_pseudoMetricType {R : realType} :=
  PseudoMetricType gauge_uniformType (@gauge_pseudoMetric_mixin R).

End entourage_gauge.

Lemma uniform_pseudometric_sup {R : realType} {T : uniformType} :
    @entourage T = @sup_ent T {E : set (T * T) | @entourage T E}
  (fun E => Uniform.class (@gauge_pseudoMetricType T (projT1 E) (projT2 E) R)).
Admitted.

End gauges.

Definition normal_space (T : topologicalType) :=
  forall A : set T, closed A ->
    set_nbhs A `<=` filter_from (set_nbhs A) closure.

Definition regular_space (T : topologicalType) :=
  forall a : T, nbhs a `<=` filter_from (nbhs a) closure.

Section ArzelaAscoli.
Context {X : topologicalType}.
Context {Y : uniformType}.
Context {hsdf : hausdorff_space Y}.
Implicit Types (I : Type).

Definition equicontinuous {I} (W : set I) (d : I -> (X -> Y)) :=
  forall x (E : set (Y * Y)), entourage E ->
    \forall y \near x, forall i, W i -> E(d i x, d i y).

Lemma equicontinuous_subset {I J} (W : set I) (V : set J)
    {fW : I -> X -> Y} {fV : J -> X -> Y} :
  fW @`W `<=` fV @` V -> equicontinuous V fV -> equicontinuous W fW.
Admitted.

Lemma equicontinuous_subset_id (W V : set (X -> Y)) :
  W `<=` V -> equicontinuous V id -> equicontinuous W id.
Admitted.

Lemma equicontinuous_continuous_for {I} (W : set I) (fW : I -> X -> Y) i x :
  {for x, equicontinuous W fW} -> W i -> {for x, continuous (fW i)}.
Admitted.

Lemma equicontinuous_continuous {I} (W : set I) (fW : I -> (X -> Y)) (i : I) :
  equicontinuous W fW -> W i -> continuous (fW i).
Admitted.

Definition pointwise_precompact {I} (W : set I) (d : I -> X -> Y) :=
  forall x, precompact [set (d i x) | i in W].

Lemma pointwise_precompact_subset {I J} (W : set I) (V : set J)
    {fW : I -> X -> Y} {fV : J -> X -> Y} :
  fW @` W `<=` fV @` V -> pointwise_precompact V fV ->
  pointwise_precompact W fW.
Admitted.

Lemma pointwise_precompact_precompact {I} (W : set I) (fW : I -> (X -> Y)) :
  pointwise_precompact W fW -> precompact ((fW @` W) : set {ptws X -> Y}).
Admitted.

Lemma uniform_pointwise_compact (W : set (X -> Y)) :
  compact (W : set (@fct_UniformFamily X Y compact)) ->
  compact (W : set {ptws X -> Y}).
Admitted.

Lemma precompact_pointwise_precompact (W : set {family compact, X -> Y}) :
  precompact W -> pointwise_precompact W id.
Admitted.

Lemma pointwise_cvg_entourage (x : X) (f : {ptws X -> Y}) E :
  entourage E -> \forall g \near f, E (f x, g x).
Admitted.

Lemma equicontinuous_closure (W : set {ptws X -> Y}) :
  equicontinuous W id -> equicontinuous (closure W) id.
Admitted.

Definition small_ent_sub := @small_set_sub _ _ (@entourage Y).

Lemma pointwise_compact_cvg (F : set (set {ptws X -> Y})) (f : {ptws X -> Y}) :
  ProperFilter F ->
  (\forall W \near powerset_filter_from F, equicontinuous W id) ->
  {ptws, F --> f} <-> {family compact, F --> f}.
Admitted.

Lemma pointwise_compact_closure (W : set (X -> Y)) :
  equicontinuous W id ->
  closure (W : set {family compact, X -> Y}) =
  closure (W : set {ptws X -> Y}).
Admitted.

Lemma pointwise_precompact_equicontinuous (W : set (X -> Y)) :
  pointwise_precompact W id ->
  equicontinuous W id ->
  precompact (W : set {family compact, X -> Y }).
Admitted.

Section precompact_equicontinuous.
Hypothesis lcptX : locally_compact [set: X].

Let compact_equicontinuous (W : set {family compact, X -> Y}) :
  (forall f, W f -> continuous f) ->
  compact (W : set {family compact, X -> Y}) ->
  equicontinuous W id.
Admitted.

Lemma precompact_equicontinuous (W : set {family compact, X -> Y}) :
  (forall f, W f -> continuous f) ->
  precompact (W : set {family compact, X -> Y}) ->
  equicontinuous W id.
Admitted.

End precompact_equicontinuous.

Theorem Ascoli (W : set {family compact, X -> Y}) :
    locally_compact [set: X] ->
  pointwise_precompact W id /\ equicontinuous W id <->
    (forall f, W f -> continuous f) /\
    precompact (W : set {family compact, X -> Y}).
Admitted.

End ArzelaAscoli.

End topology.

End mathcomp_DOT_analysis_DOT_topology_WRAPPED.
Module Export mathcomp_DOT_analysis_DOT_topology.
Module Export mathcomp.
Module Export analysis.
Module topology.
Include mathcomp_DOT_analysis_DOT_topology_WRAPPED.topology.
End topology.

End analysis.

End mathcomp.

End mathcomp_DOT_analysis_DOT_topology.
Import mathcomp.ssreflect.all_ssreflect.
Import mathcomp.algebra.ssralg.
Import mathcomp.algebra.ssrnum.
Import mathcomp.algebra.interval.
Import mathcomp.classical.mathcomp_extra.
Import mathcomp.classical.classical_sets.
Import mathcomp.analysis.topology.
Local Open Scope ring_scope.

Export topology.numFieldTopology.Exports.

Section open_closed_sets.

Variable R : realFieldType.

Lemma closed_le (y : R) : closed [set x : R | x <= y].
Admitted.

Lemma interval_closed a b : ~~ bound_side false a -> ~~ bound_side true b ->
  closed [set x : R^o | x \in Interval a b].
Admitted.

End open_closed_sets.
#[global] Hint Extern 0 (closed _) => now apply: closed_le : core.

Import HB.structures.
Import mathcomp.algebra.ssrint.
Import mathcomp.classical.cardinality.
Import mathcomp.classical.set_interval.
Import mathcomp.analysis.signed.
Import mathcomp.analysis.reals.
Import Order.TTheory.
Import GRing.Theory.
Import Num.Theory.

Local Open Scope classical_set_scope.

Definition indic {T} {R : ringType} (A : set T) (x : T) : R.
Admitted.
Reserved Notation "'\1_' A" (at level 8, A at level 2, format "'\1_' A") .
Notation "'\1_' A" := (indic A) : ring_scope.

HB.factory Record FiniteDecomp (T : pointedType) (R : ringType) (f : T -> R) :=
  { fimfunE : exists (r : seq R) (A_ : R -> set T),
      forall x, f x = \sum_(y <- r) (y * \1_(A_ y) x) }.
HB.builders Context T R f of @FiniteDecomp T R f.
  Lemma finite_subproof: @FiniteImage T R f.
Admitted.
  HB.instance Definition _ := finite_subproof.
HB.end.

Section Tietze.
Context {X : topologicalType} {R : realType}.

Lemma urysohn_ext_itv A B x y :
  closed A -> closed B -> A `&` B = set0 -> x < y ->
  exists f : X -> R, [/\ continuous f,
    f @` A `<=` [set x], f @` B `<=` [set y] & range f `<=` `[x, y]].
Admitted.

Context (A : set X).
Hypothesis clA : closed A.

Local Lemma tietze_step' (f : X -> R) (M : R) :
  0 < M -> {within A, continuous f} ->
  (forall x, A x -> `|f x| <= M) ->
  exists g : X -> R, [/\ continuous g,
     (forall x, A x -> `|f x - g x| <= 2/3 * M) &
     (forall x, `|g x| <= 1/3 * M)].
Proof.
move: M => _/posnumP[M] ctsf fA1.
have [] := @urysohn_ext_itv (A `&` f @^-1` `]-oo, -(1/3) * M%:num])
    (A `&` f @^-1` `[1/3 * M%:num,+oo[) (-(1/3) * M%:num) (1/3 * M%:num).
-
 by rewrite closed_setSI; exact: closed_comp.
-
 by rewrite closed_setSI; apply: closed_comp => //; exact: interval_closed.
-
 rewrite setIACA -preimage_setI eqEsubset; split => z // [_ []].
  rewrite !set_itvE/= => /[swap] /le_trans /[apply].
  by rewrite leNgt mulNr gtr_opp// mulr_gt0// divr_gt0.
-
 by rewrite mulNr gtr_opp// mulr_gt0.
move=> g [ctsg gL3 gR3 grng]; exists g; split => //; first last.
  by move=> x; rewrite ler_norml -mulNr; apply: grng; exists x.
move=> x Ax; have := fA1 _ Ax; rewrite 2!ler_norml => /andP[Mfx fxM].
have [xL|xL] := leP (f x) (-(1/3) * M%:num).
  have: [set g x | x in A `&` f@^-1` `]-oo, -(1/3) * M%:num]] (g x) by exists x.
  move/gL3=> ->; rewrite !mulNr opprK; apply/andP; split.
    by rewrite -ler_subl_addr -opprD -2!mulrDl natr1 divrr ?unitfE// mul1r.
  rewrite -ler_subr_addr -2!mulrBl -(@natrB _ 2 1)// (le_trans xL)//.
  by rewrite ler_pmul2r// ltW// gtr_opp// divr_gt0.
have [xR|xR] := lerP (1/3 * M%:num) (f x).
  have : [set g x | x in A `&` f@^-1` `[1/3 * M%:num, +oo[] (g x).
    by exists x => //; split => //; rewrite /= in_itv //= xR.
  move/gR3 => ->; apply/andP; split.
    rewrite ler_subr_addl -2!mulrBl (le_trans _ xR)// ler_pmul2r//.
    by rewrite ler_wpmul2r ?invr_ge0 ?ler0n// ler_subl_addl natr1 ler1n.
  by rewrite ler_subl_addl -2!mulrDl nat1r divrr ?mul1r// unitfE.
have /andP[ng3 pg3] : -(1/3) * M%:num <= g x <= 1/3 * M%:num.
  by apply: grng; exists x.
rewrite (intrD _ 1 1) !mulrDl; apply/andP; split.
