
(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "-parsing" "-w" "+undeclared-scope" "-w" "+non-primitive-record" "-w" "-ambiguous-paths" "-w" "-redundant-canonical-projection" "-w" "-projection-no-head-constant" "-w" "-deprecated-native-compiler-option" "-native-compiler" "ondemand" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/analysis/classical" "mathcomp.classical" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/analysis/theories" "mathcomp.analysis" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/HB" "HB" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/elpi" "elpi" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/mathcomp" "mathcomp" "-top" "Top.bug_01") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 1520 lines to 102 lines, then from 115 lines to 7080 lines, then from 7084 lines to 5514 lines, then from 5204 lines to 214 lines, then from 227 lines to 8975 lines, then from 8977 lines to 9174 lines, then from 8558 lines to 3022 lines, then from 3030 lines to 641 lines, then from 654 lines to 3374 lines, then from 3378 lines to 3344 lines, then from 3149 lines to 2937 lines, then from 2945 lines to 2872 lines, then from 2880 lines to 2758 lines, then from 2766 lines to 2622 lines *)
(* coqc version 8.20+alpha compiled with OCaml 4.14.1
   coqtop version 532fcf76d13e:/builds/coq/coq/_build/default,(HEAD detached at 26c84c7) (26c84c7924a0b719c579dacbad84a61567e196e9)
   Expected coqc runtime on this file: 29.967 sec *)
Require Coq.Init.Ltac.
Require Coq.ssr.ssreflect.
Require Coq.ssr.ssrfun.
Require Coq.ssr.ssrbool.
Require mathcomp.ssreflect.ssreflect.
Require mathcomp.ssreflect.ssrnotations.
Require mathcomp.ssreflect.ssrfun.
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
Require mathcomp.ssreflect.tuple.
Require mathcomp.ssreflect.finfun.
Require mathcomp.ssreflect.bigop.
Require mathcomp.ssreflect.finset.
Require mathcomp.ssreflect.prime.
Require mathcomp.ssreflect.order.
Require mathcomp.ssreflect.binomial.
Require mathcomp.algebra.ssralg.
Require mathcomp.ssreflect.ssrAC.
Require mathcomp.fingroup.fingroup.
Require mathcomp.ssreflect.generic_quotient.
Require mathcomp.algebra.ring_quotient.
Require mathcomp.algebra.countalg.
Require mathcomp.algebra.poly.
Require mathcomp.algebra.ssrnum.
Require mathcomp.algebra.ssrint.
Require mathcomp.ssreflect.fingraph.
Require mathcomp.ssreflect.all_ssreflect.
Require mathcomp.finmap.finmap.
Require Coq.setoid_ring.Field_theory.
Require Coq.setoid_ring.Field_tac.
Require mathcomp.algebra.rat.
Require mathcomp.algebra.interval.
Require mathcomp.classical.mathcomp_extra.
Require mathcomp.analysis.signed.
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
Require mathcomp.algebra.vector.
Require mathcomp.algebra.qpoly.
Require mathcomp.algebra.intdiv.
Require mathcomp.algebra.fraction.
Require mathcomp.algebra.all_algebra.
Require Coq.Bool.Bool.
Require Coq.Floats.PrimFloat.
Require Coq.Numbers.Cyclic.Int63.PrimInt63.
Require Coq.Strings.String.
Require elpi.elpi.
Require elpi.apps.locker.
Require HB.structures.
Require mathcomp.classical.boolp.
Require mathcomp.classical.classical_sets.

Module Export AdmitTactic.
Module Import LocalFalse.
Inductive False : Prop := .
End LocalFalse.
Axiom proof_admitted : False.
Import Coq.Init.Ltac.
Tactic Notation "admit" := abstract case proof_admitted.
End AdmitTactic.
Module Export mathcomp_DOT_classical_DOT_functions_WRAPPED.
Module Export functions.
Import mathcomp.ssreflect.all_ssreflect.
Import mathcomp.finmap.finmap.
Import mathcomp.algebra.ssralg.
Import mathcomp.algebra.ssrnum.
Import mathcomp.algebra.ssrint.
Import mathcomp.algebra.rat.
Import HB.structures.
Import mathcomp.classical.mathcomp_extra.
Import mathcomp.classical.boolp.
Import mathcomp.classical.classical_sets.
Add Search Blacklist "__canonical__".
Add Search Blacklist "__functions_".
Add Search Blacklist "_factory_".
Add Search Blacklist "_mixin_".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "f \_ D" (at level 10).
Reserved Notation "'{' 'fun' A '>->' B '}'"
  (format "'{' 'fun'  A  '>->'  B '}'").
Reserved Notation "'{' 'oinv' T '>->' U '}'"
  (format "'{' 'oinv'  T  '>->'  U '}'").
Reserved Notation "'{' 'inv' T '>->' U '}'"
  (format "'{' 'inv'  T  '>->'  U '}'").
Reserved Notation "'{' 'oinvfun' T '>->' U '}'"
  (format "'{' 'oinvfun'  T  '>->'  U '}'").
Reserved Notation "'{' 'invfun' T '>->' U '}'"
  (format "'{' 'invfun'  T  '>->'  U '}'").
Reserved Notation "'{' 'inj' A '>->' T '}'"
  (format "'{' 'inj'  A  '>->'  T '}'").
Reserved Notation "'{' 'splitinj' A '>->' T '}'"
  (format "'{' 'splitinj'  A  '>->'  T '}'").
Reserved Notation "'{' 'surj' A '>->' B '}'"
  (format "'{' 'surj'  A  '>->'  B '}'").
Reserved Notation "'{' 'splitsurj' A '>->' B '}'"
  (format "'{' 'splitsurj'  A  '>->'  B '}'").
Reserved Notation "'{' 'injfun' A '>->' B '}'"
  (format "'{' 'injfun'  A  '>->'  B '}'").
Reserved Notation "'{' 'surjfun' A '>->' B '}'"
  (format "'{' 'surjfun'  A  '>->'  B '}'").
Reserved Notation "'{' 'splitinjfun' A '>->' B '}'"
  (format "'{' 'splitinjfun'  A  '>->'  B '}'").
Reserved Notation "'{' 'splitsurjfun' A '>->' B '}'"
  (format "'{' 'splitsurjfun'  A  '>->'  B '}'").
Reserved Notation "'{' 'bij' A '>->' B '}'"
  (format "'{' 'bij'  A  '>->'  B '}'").
Reserved Notation "'{' 'splitbij' A '>->' B '}'"
  (format "'{' 'splitbij'  A  '>->'  B '}'").

Reserved Notation "[ 'fun' 'of' f ]" (format "[ 'fun'  'of'  f ]").
Reserved Notation "[ 'oinv' 'of' f ]" (format "[ 'oinv'  'of'  f ]").
Reserved Notation "[ 'inv' 'of' f ]" (format "[ 'inv'  'of'  f ]").
Reserved Notation "[ 'oinv' 'of' f ]" (format "[ 'oinv'  'of'  f ]").
Reserved Notation "[ 'inv' 'of' f ]" (format "[ 'inv'  'of'  f ]").
Reserved Notation "[ 'inj' 'of' f ]" (format "[ 'inj'  'of'  f ]").
Reserved Notation "[ 'splitinj' 'of' f ]" (format "[ 'splitinj'  'of'  f ]").
Reserved Notation "[ 'surj' 'of' f ]" (format "[ 'surj'  'of'  f ]").
Reserved Notation "[ 'splitsurj' 'of' f ]" (format "[ 'splitsurj'  'of'  f ]").
Reserved Notation "[ 'injfun' 'of' f ]" (format "[ 'injfun'  'of'  f ]").
Reserved Notation "[ 'surjfun' 'of' f ]" (format "[ 'surjfun'  'of'  f ]").
Reserved Notation "[ 'splitinjfun' 'of' f ]"
  (format "[ 'splitinjfun'  'of'  f ]").
Reserved Notation "[ 'splitsurjfun' 'of' f ]"
  (format "[ 'splitsurjfun'  'of'  f ]").
Reserved Notation "[ 'bij' 'of' f ]" (format "[ 'bij'  'of'  f ]").
Reserved Notation "[ 'splitbij' 'of' f ]" (format "[ 'splitbij'  'of'  f ]").

Reserved Notation "''oinv_' f" (at level 8, f at level 2, format "''oinv_' f").
Reserved Notation "''funS_' f" (at level 8, f at level 2, format "''funS_' f").
Reserved Notation "''mem_fun_' f"
  (at level 8, f at level 2, format  "''mem_fun_' f").
Reserved Notation "''oinvK_' f"
  (at level 8, f at level 2, format "''oinvK_' f").
Reserved Notation "''oinvS_' f"
  (at level 8, f at level 2, format "''oinvS_' f").
Reserved Notation "''oinvP_' f"
  (at level 8, f at level 2, format "''oinvP_' f").
Reserved Notation "''oinvT_' f"
  (at level 8, f at level 2, format "''oinvT_' f").
Reserved Notation "''invK_' f"
  (at level 8, f at level 2, format "''invK_' f").
Reserved Notation "''invS_' f"
  (at level 8, f at level 2, format "''invS_' f").
Reserved Notation "''funoK_' f"
  (at level 8, f at level 2, format "''funoK_' f").
Reserved Notation "''inj_' f"
  (at level 8, f at level 2, format "''inj_' f").
Reserved Notation "''funK_' f"
  (at level 8, f at level 2, format "''funK_' f").
Reserved Notation "''totalfun_' A"
  (at level 8, A at level 2, format "''totalfun_' A").
Reserved Notation "''surj_' f"
  (at level 8, f at level 2, format "''surj_' f").
Reserved Notation "''split_' a"
  (at level 8, a at level 2, format "''split_' a").
Reserved Notation "''bijTT_'  f"
  (at level 8, f at level 2, format "''bijTT_' f").
Reserved Notation "''bij_' f" (at level 8, f at level 2, format "''bij_' f").
Reserved Notation "''valL_' v" (at level 8, v at level 2, format "''valL_' v").
Reserved Notation "''valLfun_' v"
  (at level 8, v at level 2, format "''valLfun_' v").
Reserved Notation "''pinv_' dflt"
  (at level 8, dflt at level 2, format "''pinv_' dflt").
Reserved Notation "''pPbij_' dflt"
  (at level 8, dflt at level 2, format "''pPbij_' dflt").
Reserved Notation "''pPinj_' dflt"
  (at level 8, dflt at level 2, format "''pPinj_' dflt").
Reserved Notation "''injpPfun_' dflt"
  (at level 8, dflt at level 2, format "''injpPfun_' dflt").
Reserved Notation "''funpPinj_' dflt"
  (at level 8, dflt at level 2, format "''funpPinj_' dflt").

Local Open Scope classical_set_scope.

Section MainProperties.
Context {aT rT}  (A : set aT) (B : set rT) (f : aT -> rT).
Definition set_fun := {homo f : x / A x >-> B x}.
Definition set_surj := B `<=` f @` A.
Definition set_inj := {in A &, injective f}.
Definition set_bij := [/\ set_fun, set_inj & set_surj].
End MainProperties.

HB.mixin Record isFun {aT rT} (A : set aT) (B : set rT) (f : aT -> rT) :=
  { funS : set_fun A B f }.
HB.structure Definition Fun {aT rT} (A : set aT) (B : set rT) :=
  { f of isFun _ _ A B f }.
Notation "{ 'fun' A >-> B }" := (@Fun.type _ _ A B) : form_scope.
Notation "[ 'fun'  'of'  f ]" := [the {fun _ >-> _} of f : _ -> _] : form_scope.

HB.mixin Record OInv {aT rT} (f : aT -> rT) := { oinv : rT -> option aT }.
HB.structure Definition OInversible aT rT := {f of OInv aT rT f}.
Notation "{ 'oinv' aT >-> rT }" := (@OInversible.type aT rT) : type_scope.
Notation "[ 'oinv'  'of'  f ]" := [the {oinv _ >-> _} of f : _ -> _] :
  form_scope.
Definition phant_oinv aT rT (f : {oinv aT >-> rT})
  of phantom (_ -> _) f := @oinv _ _ f.
Notation "''oinv_' f" := (@phant_oinv _ _ _ (Phantom (_ -> _) f%FUN)).

HB.structure Definition OInvFun aT rT A B :=
  {f of OInv aT rT f & isFun aT rT A B f}.
Notation "{ 'oinvfun' A >-> B }" := (@OInvFun.type _ _ A B) : type_scope.
Notation "[ 'oinvfun'  'of'  f ]" :=
  [the {oinvfun _ >-> _} of f : _ -> _] : form_scope.

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
Notation "[ 'inv'  'of'  f ]" := [the {inv _ >-> _} of f : _ -> _] : form_scope.
Definition phant_inv aT rT (f : {inv aT >-> rT}) of phantom (_ -> _) f :=
  @inv _ _ f.
Notation "f ^-1" := (@inv _ _ f%FUN) (only printing) : fun_scope.
Notation "f ^-1" := (@inv _ _ f%function) (only printing) : function_scope.
Notation "f ^-1" := (@phant_inv _ _ _ (Phantom (_ -> _) f%FUN)) : fun_scope.
Notation "f ^-1" :=
  (@phant_inv _ _ _ (Phantom (_ -> _) f%function)) : function_scope.

HB.structure Definition InvFun aT rT A B :=
  {f of Inv aT rT f & isFun aT rT A B f}.
Notation "{ 'invfun' A >-> B }" := (@InvFun.type _ _ A B) : type_scope.
Notation "[ 'invfun'  'of'  f ]" :=
  [the {invfun _ >-> _} of f : _ -> _] : form_scope.

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
Notation "{ 'surj' A >-> B }" := (@Surject.type _ _ A B) : type_scope.
Notation "[ 'surj'  'of'  f ]" :=
  [the {surj _ >-> _} of f : _ -> _] : form_scope.

HB.structure Definition SurjFun aT rT A B :=
  {f of @Surject aT rT A B f & @Fun _ _ A B f}.
Notation "{ 'surjfun' A >-> B }" := (@SurjFun.type _ _ A B) : type_scope.
Notation "[ 'surjfun'  'of'  f ]" :=
  [the {surjfun _ >-> _} of f : _ -> _] : form_scope.

HB.structure Definition SplitSurj aT rT A B :=
  {f of @Surject aT rT A B f & @Inv _ _ f}.
Notation "{ 'splitsurj' A >-> B }" := (@SplitSurj.type _ _ A B) : type_scope.
Notation "[ 'splitsurj'  'of'  f ]" :=
  [the {splitsurj _ >-> _} of f : _ -> _] : form_scope.

HB.structure Definition SplitSurjFun aT rT A B :=
   {f of @SplitSurj aT rT A B f & @Fun _ _ A B f}.
Notation "{ 'splitsurjfun' A >-> B }" :=
  (@SplitSurjFun.type _ _ A B) : type_scope.
Notation "[ 'splitsurjfun'  'of'  f ]" :=
  [the {splitsurjfun _ >-> _} of f : _ -> _] : form_scope.

HB.mixin Record OInv_Can aT rT (A : set aT) (f : aT -> rT) of OInv _ _ f :=
  { funoK : {in A, pcancel f 'oinv_f} }.

HB.structure Definition Inject aT rT A :=
  {f of OInv aT rT f & OInv_Can aT rT A f}.
Notation "{ 'inj' A >-> rT }" := (@Inject.type _ rT A) : type_scope.
Notation "[ 'inj'  'of'  f ]" := [the {inj _ >-> _} of f : _ -> _] : form_scope.

HB.structure Definition InjFun {aT rT} (A : set aT) (B : set rT) :=
   { f of @Fun _ _ A B f & @Inject _ _ A f }.
Notation "{ 'injfun' A >-> B }" := (@InjFun.type _ _ A B) : type_scope.
Notation "[ 'injfun'  'of'  f ]" :=
  [the {injfun _ >-> _} of f : _ -> _] : form_scope.

HB.structure Definition SplitInj aT rT (A : set aT) :=
  {f of @Inv aT rT f & @Inject aT rT A f}.
Notation "{ 'splitinj' A >-> rT }" := (@SplitInj.type _ rT A) : type_scope.
Notation "[ 'splitinj'  'of'  f ]" :=
  [the {splitinj _ >-> _} of f : _ -> _] : form_scope.

HB.structure Definition SplitInjFun aT rT (A : set aT) (B : set rT) :=
  {f of @SplitInj _ rT A f & @isFun _ _ A B f}.
Notation "{ 'splitinjfun' A >-> B }" := (@SplitInjFun.type _ _ A B) : type_scope.
Notation "[ 'splitinjfun'  'of'  f ]" :=
  [the {splitinjfun _ >-> _} of f : _ -> _] : form_scope.

HB.structure Definition Bij {aT rT} {A : set aT} {B : set rT} :=
   {f of @InjFun _ _ A B f & @SurjFun _ _ A B f}.
Notation "{ 'bij' A >-> B }" := (@Bij.type _ _ A B) : type_scope.
Notation "[ 'bij'  'of'  f ]" := [the {bij _ >-> _} of f] : form_scope.

HB.structure Definition SplitBij {aT rT} {A : set aT} {B : set rT} :=
   {f of @SplitInjFun _ _ A B f & @SplitSurjFun _ _ A B f}.
Notation "{ 'splitbij' A >-> B }" := (@SplitBij.type _ _ A B) : type_scope.
Notation "[ 'splitbij'  'of'  f ]" := [the {splitbij _ >-> _} of f] : form_scope.

Module Export ShortFunSyntax.
Notation "A ~> B" := {fun A >-> B} (at level 70) : type_scope.
Notation "aT <=> rT" := {oinv aT >-> rT} (at level 70) : type_scope.
Notation "A <~ B" := {oinvfun A >-> B} (at level 70) : type_scope.
Notation "aT <<=> rT" := {inv aT >-> rT} (at level 70) : type_scope.
Notation "A <<~ B" := {invfun A >-> B} (at level 70) : type_scope.
Notation "A =>> B" := {surj A >-> B} (at level 70) : type_scope.
Notation "A ~>> B" := {surjfun A >-> B} (at level 70) : type_scope.
Notation "A ==>> B" := {splitsurj A >-> B} (at level 70) : type_scope.
Notation "A ~~>> B" := {splitsurjfun A >-> B} (at level 70) : type_scope.
Notation "A >=> rT" := {inj A >-> rT} (at level 70) : type_scope.
Notation "A >~> B" := {injfun A >-> B} (at level 70) : type_scope.
Notation "A >>=> rT" := {splitinj A >-> rT} (at level 70) : type_scope.
Notation "A >>~> B" := {splitinjfun A >-> B} (at level 70) : type_scope.
Notation "A <~> B" := {bij A >-> B} (at level 70) : type_scope.
Notation "A <<~> B" := {splitbij A >-> B} (at level 70) : type_scope.
End ShortFunSyntax.

Definition phant_funS aT rT (A : set aT) (B : set rT)
  (f : {fun A >-> B}) of phantom (_ -> _) f := @funS _ _ _ _ f.
Notation "'funS_  f" := (phant_funS (Phantom (_ -> _) f))
  (at level 8, f at level 2) : form_scope.
#[global] Hint Extern 0 (set_fun _ _ _) => solve [apply: funS] : core.
#[global] Hint Extern 0 (prop_in1 _ _) => solve [apply: funS] : core.

Definition fun_image_sub aT rT (A : set aT) (B : set rT) (f : {fun A >-> B}) :=
  image_subP.2 (@funS _ _ _ _ f).
Arguments fun_image_sub {aT rT A B}.
#[global] Hint Extern 0 (_ @` _ `<=` _) => solve [apply: fun_image_sub] : core.

Definition mem_fun aT rT (A : set aT) (B : set rT) (f : {fun A >-> B}) :=
  homo_setP.2 (@funS _ _ _ _ f).
#[global] Hint Extern 0 (prop_in1 _ _) => solve [apply: mem_fun] : core.

Definition phant_mem_fun aT rT (A : set aT) (B : set rT)
  (f : {fun A >-> B}) of phantom (_ -> _) f := homo_setP.2 (@funS _ _ _ _ f).
Notation "'mem_fun_  f" := (phant_mem_fun (Phantom (_ -> _) f))
  (at level 8, f at level 2) : form_scope.

Lemma some_inv {aT rT} (f : {inv aT >-> rT}) x : Some (f^-1 x) = 'oinv_f x.
Admitted.

Definition phant_oinvK aT rT (A : set aT) (B : set rT)
   (f : {surj A >-> B}) of phantom (_ -> _) f := @oinvK _ _ _ _ f.
Notation "'oinvK_ f" := (phant_oinvK (Phantom (_ -> _) f)) : form_scope.
#[global] Hint Resolve oinvK : core.

Definition phant_oinvS aT rT (A : set aT) (B : set rT)
   (f : {surj A >-> B}) of phantom (_ -> _) f := @oinvS _ _ _ _ f.
Notation "'oinvS_ f" := (phant_oinvS (Phantom (_ -> _) f)) : form_scope.
#[global] Hint Resolve oinvS : core.

Variant oinv_spec {aT} {rT} {A : set aT} {B : set rT} (f : {surj A >-> B}) y :
   rT -> option aT -> Type :=
  OInvSpec (x : aT) of A x & f x = y : oinv_spec f y (f x) (Some x).

Lemma oinvP aT rT (A : set aT) (B : set rT) (f : {surj A >-> B}) y :
  B y -> oinv_spec f y y ('oinv_f y).
Admitted.

Definition phant_oinvP aT rT (A : set aT) (B : set rT)
   (f : {surj A >-> B}) of phantom (_ -> _) f := @oinvP _ _ _ _ f.
Notation "'oinvP_ f" := (phant_oinvP (Phantom (_ -> _) f)) : form_scope.
#[global] Hint Resolve oinvP : core.

Lemma oinvT {aT rT} {A : set aT} {B : set rT} {f : {surj A >-> B}} x :
  B x -> 'oinv_f x.
Admitted.
Definition phant_oinvT aT rT (A : set aT) (B : set rT)
   (f : {surj A >-> B}) of phantom (_ -> _) f := @oinvT _ _ _ _ f.
Notation "'oinvT_ f" := (phant_oinvT (Phantom (_ -> _) f)) : form_scope.
#[global] Hint Resolve oinvT : core.

Lemma invK {aT rT} {A : set aT} {B : set rT} {f : {splitsurj A >-> B}} :
   {in B, cancel f^-1 f}.
Admitted.
Definition phant_invK aT rT (A : set aT) (B : set rT)
   (f : {splitsurj A >-> B}) of phantom (_ -> _) f := @invK _ _ _ _ f.
Notation "'invK_ f" := (phant_invK (Phantom (_ -> _) f)) : form_scope.
#[global] Hint Resolve invK : core.

Lemma invS {aT rT} {A : set aT} {B : set rT} {f : {splitsurj A >-> B}} :
  {homo f^-1 : x / B x >-> A x}.
Admitted.
Definition phant_invS aT rT (A : set aT) (B : set rT)
   {f : {splitsurjfun A >-> B}} of phantom (_ -> _) f := @invS _ _ _ _ f.
Notation "'invS_ f" := (phant_invS (Phantom (_ -> _) f)) : form_scope.
#[global] Hint Resolve invS : core.

Definition phant_funoK aT rT (A : set aT) (f : {inj A >-> rT})
  of phantom (_ -> _) f := @funoK _ _ _ f.
Notation "'funoK_ f" := (phant_funoK (Phantom (_ -> _) f)) : form_scope.
#[global] Hint Resolve funoK : core.
Definition inj {aT rT : nonPropType} {A : set aT} {f : {inj A >-> rT}} :
   {in A &, injective f}.
Admitted.
Definition phant_inj aT rT (A : set aT) (f : {inj A >-> rT}) of
   phantom (_ -> _) f := @inj _ _ _ f.
Notation "'inj_ f" := (phant_inj (Phantom (_ -> _) f)) : form_scope.
Definition inj_hint {aT rT} {A : set aT} {f : {inj A >-> rT}} :
   {in A &, injective f}.
Admitted.
#[global] Hint Extern 0 {in _ &, injective _} => solve [apply: inj_hint] : core.
#[global] Hint Extern 0 (set_inj _ _) => solve [apply: inj_hint] : core.

Lemma injT {aT rT} {f : {inj [set: aT] >-> rT}} : injective f.
Admitted.
#[global] Hint Extern 0 (injective _) => solve [apply: injT] : core.

Lemma funK {aT rT : Type} {A : set aT} {s : {splitinj A >-> rT}} :
  {in A, cancel s s^-1}.
Admitted.

Definition phant_funK aT rT (A : set aT) (f : {splitinj A >-> rT})
  of phantom (_ -> _) f := @funK _ _ _ f.
Notation "'funK_  f" := (phant_funK (Phantom (_ -> _) f)) : form_scope.
#[global] Hint Resolve funK : core.

Lemma funP {aT rT} {A : set aT} {B : set rT} (f g : {fun A >-> B}) :
  f = g <-> f =1 g.
Admitted.

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

Section OInverse.
Context {aT rT : Type} {A : set aT} {B : set rT}.

HB.instance Definition _ {f : {oinv aT >-> rT}} :=
  OInv.Build _ _ 'oinv_f (omap f).

Lemma oinvV {f : {oinv aT >-> rT}} : 'oinv_('oinv_f) = omap f.
Admitted.

HB.instance Definition _ (f : {surj A >-> B}) :=
  isFun.Build rT (option aT) B (some @` A) 'oinv_f oinvS.

Lemma surjoinv_inj_subproof (f : {surj A >-> B}) : OInv_Can _ _ B 'oinv_f.
Admitted.
HB.instance Definition _ f := surjoinv_inj_subproof f.

Lemma injoinv_surj_subproof (f : {injfun A >-> B}) :
  OInv_CanV _ _ B (some @` A) 'oinv_f.
Admitted.
HB.instance Definition _ (f : {injfun A >-> B}) := injoinv_surj_subproof f.

HB.instance Definition _ {f : {bij A >-> B}} := InjFun.on 'oinv_f.

End OInverse.

Section Inverse.
Context {aT rT : Type} {A : set aT} {B : set rT}.

HB.instance Definition _ (f : {inv aT >-> rT}) := Inv.Build rT aT f^-1 f.
HB.instance Definition _ (f : {inv aT >-> rT}) := Inversible.copy inv f^-1.

Lemma invV (f : {inv aT >-> rT}) : f^-1^-1 = f.
Admitted.

HB.instance Definition _ (f : {splitsurj A >-> B}) :=
  isFun.Build rT aT B A f^-1 invS.
HB.instance Definition _ (f : {splitsurj A >-> B}) := Fun.copy inv f^-1.
HB.instance Definition _ {f : {splitsurj A >-> B}} :=
  Inv_Can.Build _ _ _ f^-1 'invK_f.
HB.instance Definition _ (f : {splitinjfun A >-> B}) :=
  Inv_CanV.Build _ _ _ _ f^-1 funS funK.
HB.instance Definition _ {f : {splitbij A >-> B}} := InjFun.on f^-1.

End Inverse.

Section Some.
Context {T} {A : set T}.

HB.instance Definition _ := OInv.Build _ _ (@Some T) id.

Lemma oinv_some : 'oinv_(@Some T) = id.
Admitted.

Lemma some_can_subproof : @OInv_Can _ _ A (@Some T).
Admitted.
HB.instance Definition _ := some_can_subproof.

Lemma some_canV_subproof : OInv_CanV _ _ A (some @` A) (@Some T).
Admitted.
HB.instance Definition _  := some_canV_subproof.

Lemma some_fun_subproof : isFun _ _ A (some @` A) (@Some T).
Admitted.
HB.instance Definition _ := some_fun_subproof.

End Some.

Section OApply.
Context {aT rT} {A : set aT} {B : set rT} {b0 : rT}.
Local Notation oapp f := (oapp f b0).

HB.instance Definition _ {f : {oinv aT >-> rT}} :=
  Inv.Build _ _ (oapp f) 'oinv_f.

Lemma inv_oapp {f : {oinv aT >-> rT}} : (oapp f)^-1 = 'oinv_f.
Admitted.
Lemma oinv_oapp  {f : {oinv aT >-> rT}} : 'oinv_(oapp f) = olift 'oinv_f.
Admitted.
Lemma inv_oappV {f : {inv aT >-> rT}} : olift f^-1 = (oapp f)^-1.
Admitted.

Lemma oapp_can_subproof (f : {inj A >-> rT}) : Inv_Can _ _ (some @` A) (oapp f).
admit.
Defined.
HB.instance Definition _ f := oapp_can_subproof f.

Lemma oapp_surj_subproof (f : {surj A >-> B}) : Inv_CanV _ _ (some @` A) B (oapp f).
Admitted.
HB.instance Definition _  f := oapp_surj_subproof f.

Lemma oapp_fun_subproof (f : {fun A >-> B}) : isFun _ _ (some @` A) B (oapp f).
Admitted.
HB.instance Definition _ f := oapp_fun_subproof f.
HB.instance Definition _ (f : {oinvfun A >-> B}) := Fun.on (oapp f).
HB.instance Definition _ (f : {injfun A >-> B}) := Fun.on (oapp f).
HB.instance Definition _ (f : {surjfun A >-> B}) := Fun.on (oapp f).
HB.instance Definition _ (f : {bij A >-> B}) := Fun.on (oapp f).
HB.instance Definition _ (f : {splitbij A >-> B}) := Fun.on (oapp f).

End OApply.

Section OBind.
Context {aT rT} {A : set aT} {B : set (option rT)}.
Local Notation b f := (oapp f None).
Local Notation orT := (option rT).

HB.instance Definition _ {f : {oinv aT >-> orT}} :=
  Inv.Build _ _ (obind f) 'oinv_f.

Lemma inv_obind {f : {oinv aT >-> orT}} : (obind f)^-1 = 'oinv_f.
Admitted.
Lemma oinv_obind {f : {oinv aT >-> orT}} : 'oinv_(obind f) = olift 'oinv_f.
Admitted.
Lemma inv_obindV {f : {inv aT >-> orT}} : (obind f)^-1 = olift f^-1.
Admitted.

HB.instance Definition _ (f : {fun A >-> B}) := Fun.copy (obind f) (b f).
HB.instance Definition _ (f : {inj A >-> orT}) := Inject.copy (obind f) (b f).
HB.instance Definition _ (f : {injfun A >-> B}) := Fun.on (obind f).
HB.instance Definition _ (f : {surj A >-> B}) := Surject.copy (obind f) (b f).
HB.instance Definition _ (f : {surjfun A >-> B}) := Fun.on (obind f).
HB.instance Definition _ (f : {bij A >-> B}) := Fun.on (obind f).
End OBind.

Section Composition.
Context {aT rT sT} {A : set aT} {B : set rT} {C : set sT}.

Local Lemma comp_fun_subproof (f : {fun A >-> B}) (g : {fun B >-> C}) :
  isFun _ _ A C (g \o f).
Admitted.
HB.instance Definition _ f g := comp_fun_subproof f g.

Section OInv.
Context {f : {oinv aT >-> rT}} {g : {oinv rT >-> sT}}.
HB.instance Definition _ := OInv.Build _ _ (g \o f) (obind 'oinv_f \o 'oinv_g).
Lemma oinv_comp : 'oinv_(g \o f) = (obind 'oinv_f) \o 'oinv_g.
Admitted.
End OInv.

Section OInv.
Context {f : {inv aT >-> rT}} {g : {inv rT >-> sT}}.
Lemma some_comp_inv : olift (f^-1 \o g^-1) = 'oinv_(g \o f).
admit.
Defined.
HB.instance Definition _ := OInv_Inv.Build aT sT (g \o f) some_comp_inv.
Lemma inv_comp : (g \o f)^-1 = f^-1 \o g^-1.
Admitted.
End OInv.

Lemma comp_can_subproof (f : {injfun A >-> B}) (g : {inj B >-> sT}) :
  OInv_Can aT sT A (g \o f).
admit.
Defined.
HB.instance Definition _ f g := comp_can_subproof f g.

HB.instance Definition _ (f : {injfun A >-> B}) (g : {injfun B >-> C}) :=
  Inject.on (g \o f).
HB.instance Definition _ (f : {splitinjfun A >-> B})
  (g : {splitinj B >-> sT}) := Inject.on (g \o f).
HB.instance Definition _ (f : {splitinjfun A >-> B})
  (g : {splitinjfun B >-> C}) := Inject.on (g \o f).
End Composition.

Section Composition.
Context {aT rT sT} {A : set aT} {B : set rT} {C : set sT}.

Lemma comp_surj_subproof (f : {surj A >-> B}) (g : {surj B >-> C}) :
  OInv_CanV _ _ A C (g \o f).
Admitted.

HB.instance Definition _ f g := comp_surj_subproof f g.
HB.instance Definition _ (f : {splitsurj A >-> B}) (g : {splitsurj B >-> C}) :=
  Surject.on (g \o f).
HB.instance Definition _ (f : {surjfun A >-> B}) (g : {surjfun B >-> C}) :=
  Surject.on (g \o f).
HB.instance Definition _ (f : {splitsurjfun A >-> B})
  (g : {splitsurjfun B >-> C}) := Surject.on (g \o f).
HB.instance Definition _ (f : {bij A >-> B}) (g : {bij B >-> C}) :=
  Surject.on (g \o f).
HB.instance Definition _ (f : {splitbij A >-> B}) (g : {splitbij B >-> C}) :=
  Surject.on (g \o f).

End Composition.

Section totalfun.
Context {aT rT : Type}.
Definition totalfun_ (A : set aT) (f : aT -> rT) := f.
Context {A : set aT}.
Local Notation totalfun := (totalfun_ A).
HB.instance Definition _ (f : aT -> rT) :=
  isFun.Build _ _ A setT (totalfun f) (fun _ _ => I).
HB.instance Definition _ (f : {inj A >-> rT}) := Inject.on (totalfun f).
HB.instance Definition _ (f : {splitinj A >-> rT}) := SplitInj.on (totalfun f).
HB.instance Definition _ (f : {surj A >-> [set: rT]}) :=
  Surject.on (totalfun f).
HB.instance Definition _ (f : {splitsurj A >-> [set: rT]}) :=
  SplitSurj.on (totalfun f).
End totalfun.
Notation "''totalfun_' A" := (totalfun_ A) : form_scope.
Notation totalfun := (totalfun_ setT).

Section Olift.
Context {aT rT} {A : set aT} {B : set rT}.

HB.instance Definition _ {f : {oinv aT >-> rT}} := OInversible.on (olift f).

Lemma oinv_olift  {f : {oinv aT >-> rT}} : 'oinv_(olift f) = obind 'oinv_f.
Admitted.

HB.instance Definition _ (f : {inj A >-> rT}) :=
  Inject.copy (olift f) (olift ('totalfun_A f)).
HB.instance Definition _ (f : {surj A >-> B}) := Surject.on (olift f).
HB.instance Definition _ (f : {fun A >-> B}) := Fun.on (olift f).
HB.instance Definition _ (f : {oinvfun A >-> B}) := Fun.on (olift f).
HB.instance Definition _ (f : {injfun A >-> B}) := Fun.on (olift f).
HB.instance Definition _ (f : {surjfun A >-> B}) := Fun.on (olift f).
HB.instance Definition _ (f : {bij A >-> B}) := Fun.on (olift f).

End Olift.

Section Map.
Context {aT rT} {A : set aT} {B : set rT}.
Local Notation m f := (obind (olift f)).

HB.instance Definition _ (f : {fun A >-> B}) := Fun.copy (omap f) (m f).

HB.instance Definition _ {f : {oinv aT >-> rT}} :=
  Inv.Build _ _ (omap f) (obind 'oinv_f).

Lemma inv_omap {f : {oinv aT >-> rT}} : (omap f)^-1 = obind 'oinv_f.
Admitted.
Lemma oinv_omap {f : {oinv aT >-> rT}} : 'oinv_(omap f) = olift (obind 'oinv_f).
Admitted.
Lemma omapV {f : {inv aT >-> rT}} : omap f^-1 = (omap f)^-1.
Admitted.

HB.instance Definition _ (f : {oinvfun A >-> B}) := Fun.on (omap f).
HB.instance Definition _ (f : {inj A >-> rT}) := Inject.copy (omap f) (m f).
HB.instance Definition _ (f : {injfun A >-> B}) := Fun.on (omap f).
HB.instance Definition _ (f : {surj A >-> B}) := Surject.copy (omap f) (m f).
HB.instance Definition _ (f : {surjfun A >-> B}) := Fun.on (omap f).
HB.instance Definition _ (f : {bij A >-> B}) := Fun.on (omap f).
End Map.

HB.factory Record CanV {aT rT} {A : set aT} {B : set rT} (f : aT -> rT) :=
  { inv; invS : {homo inv : x / B x >-> A x}; invK : {in B, cancel inv f}; }.
HB.builders Context {aT rT} {A : set aT} {B : set rT} (f : aT -> rT) of CanV _ _ A B f.
 HB.instance Definition _ := Inv.Build _ _ f inv.
 HB.instance Definition _ := Inv_CanV.Build _ _ _ _ f invS invK.
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
  HB.instance Definition _ := OInv_Can.Build aT rT _ f funoK.
  HB.instance Definition _ := OInv_CanV.Build aT rT _ _ f oinvS oinvK.
HB.end.

HB.factory Record OCan2 {aT rT} {A : set aT} {B : set rT} (f : aT -> rT) :=
   { oinv; funS :  {homo f : x / A x >-> B x};
           oinvS : {homo oinv : x / B x >-> (some @` A) x};
           funoK : {in A, pcancel f oinv};
           oinvK : {in B, ocancel oinv f};
   }.
HB.builders Context {aT rT} A B (f : aT -> rT) of OCan2 _ _ A B f.
  HB.instance Definition _ := OInv.Build aT rT f oinv.
  HB.instance Definition _ := OInv_Can2.Build aT rT _ _ f funS oinvS funoK oinvK.
HB.end.

HB.factory Record Can {aT rT} {A : set aT} (f : aT -> rT) :=
  { inv; funK : {in A, cancel f inv} }.
HB.builders Context {aT rT} A (f : aT -> rT) of @Can _ _ A f.

 HB.instance Definition _ := Inv.Build _ _ f inv.
 HB.instance Definition _ := Inv_Can.Build _ _ _ f funK.
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
  HB.instance Definition _ := Inv_Can.Build aT rT A f funK.
  HB.instance Definition _ := @Inv_CanV.Build aT rT A B f invS invK.
HB.end.

HB.factory Record Can2 {aT rT} {A : set aT} {B : set rT} (f : aT -> rT) :=
  { inv; funS : {homo f : x / A x >-> B x};
         invS : {homo inv : x / B x >-> A x};
         funK : {in A, cancel f inv};
         invK : {in B, cancel inv f};
   }.
HB.builders Context {aT rT} A B (f : aT -> rT) of Can2 _ _ A B f.
  HB.instance Definition _ := Inv.Build aT rT f inv.
  HB.instance Definition _ := Inv_Can2.Build aT rT A B f funS invS funK invK.
HB.end.

HB.factory Record SplitInjFun_CanV {aT rT} {A : set aT} {B : set rT} (f : aT -> rT) of
     @SplitInjFun _ _ A B f :=
  { invS : {homo f^-1 : x / B x >-> A x}; injV : {in B &, injective f^-1} }.
HB.builders Context {aT rT} {A : set aT} {B : set rT} (f : aT -> rT) of SplitInjFun_CanV _ _ A B f.
  Let mem_inv := homo_setP.2 invS.
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

Section Psurj.
Context {aT rT} {A : set aT} {B : set rT} {f : aT -> rT} (fsurj : set_surj A B f).

#[local] HB.instance Definition _ : OCanV _ _ A B f := fsurj.
Definition surjection_of_surj := [surj of f].

Lemma Psurj : {s : {surj A >-> B} | f = s}.
Admitted.
End Psurj.
Coercion surjection_of_surj : set_surj >-> Surject.type.

Lemma oinv_surj {aT rT} {A : set aT} {B : set rT} {f : aT -> rT}
   (fS : set_surj A B f) y :
 'oinv_fS y = if pselect (B y) is left By then some (projT1 (cid2 (fS y By))) else None.
Admitted.

Lemma surj {aT rT} {A : set aT} {B : set rT} {f : {surj A >-> B}} : set_surj A B f.
Admitted.

Definition phant_surj aT rT (A : set aT) (B : set rT) (f : {surj A >-> B})
  of phantom (_ -> _) f := @surj _ _ _ _ f.
Notation "'surj_  f" := (phant_surj (Phantom (_ -> _) f)) : form_scope.
#[global] Hint Extern 0 (set_surj _ _ _) => solve [apply: surj] : core.

Section funin_surj.
Context {aT rT : Type}.

Definition funin (A : set aT) (f : aT -> rT) := f.

Context {A : set aT} {B : set rT} (f : aT -> rT).

Lemma set_fun_image : set_fun A (f @` A) f.
admit.
Defined.

HB.instance Definition _ :=
  @isFun.Build _ _ _ _ (funin A f) set_fun_image.

HB.instance Definition _ : OCanV _ _ A (f @` A) (funin A f) :=
   ((fun _ => id) : set_surj A (f @` A) f).

End funin_surj.
Notation "[ 'fun' f 'in' A ]" := (funin A f)
  (at level 0, f at next level,
   format "[ 'fun'  f  'in'  A ]") : function_scope.
#[global] Hint Resolve set_fun_image : core.

Section split.
Context {aT rT} (A : set aT) (B : set rT).
Definition split_ (dflt : rT -> aT) (f : aT -> rT) := f.

Context (dflt : rT -> aT).
Local Notation split := (split_ dflt).

HB.instance Definition _ (f : {fun A >-> B}) := Fun.on (split f).

Section oinv.
Context (f : {oinv aT >-> rT}).
Let g y := odflt (dflt y) ('oinv_f y).
HB.instance Definition _  := Inv.Build _ _ (split f) g.
Lemma splitV : (split f)^-1 = g.
Admitted.
End oinv.
HB.instance Definition _ (f : {oinvfun A >-> B}) := Fun.on (split f).

Lemma splitis_inj_subproof (f : {inj A >-> rT}) : Inv_Can _ _ A (split f).
Admitted.
HB.instance Definition _ f := splitis_inj_subproof f.
HB.instance Definition _ (f : {injfun A >-> B}) := Inject.on (split f).

Lemma splitid (f : {splitinjfun A >-> B}) : (split f)^-1 = f^-1.
Admitted.

Lemma splitsurj_subproof (f : {surj A >-> B}) : Inv_CanV _ _ A B (split f).
Admitted.

HB.instance Definition _ f := splitsurj_subproof f.
HB.instance Definition _ (f : {surjfun A >-> B}) := Surject.on (split f).
HB.instance Definition _ (f : {bij A >-> B}) := Surject.on (split f).

End split.
Notation "''split_' a" := (split_ a) : form_scope.
Notation split := 'split_point.

HB.factory Record Inj {aT rT} (A : set aT) (f : aT -> rT) :=
   { inj : {in A &, injective f} }.
HB.builders Context {aT rT} A (f : aT -> rT) of Inj _ _ A f.
  HB.instance Definition _ := OInversible.copy f [fun f in A].
  Lemma funoK : {in A, pcancel f 'oinv_f}.
Admitted.
  HB.instance Definition _ := OInv_Can.Build _ _ _ f funoK.
HB.end.

HB.factory Record SurjFun_Inj {aT rT} {A : set aT} {B : set rT} (f : aT -> rT) of
   @SurjFun _ _ A B f := { inj : {in A &, injective f} }.
HB.builders Context {aT rT} {A : set aT} {B : set rT} (f : aT -> rT) of
    @SurjFun_Inj _ _ A B f.
  Let g := f.
  HB.instance Definition _ := Inj.Build _ _ A g inj.
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

Section Inverses.
Context aT rT {A : set aT} {B : set rT}.
HB.instance Definition _ (f : {inj A >-> rT}) :=
  SurjFun_Inj.Build _ _ _ _ [fun f in A] 'inj_f.
End Inverses.

Section Pinj.
Context {aT rT} {A : set aT} {f : aT -> rT} (finj : {in A &, injective f}).
#[local] HB.instance Definition _ := Inj.Build _ _ _ f finj.
Lemma Pinj : {i : {inj A >-> rT} | f = i}.
Admitted.
End Pinj.

Section Pfun.
Context {aT rT} {A : set aT} {B : set rT} {f : aT -> rT}
  (ffun : {homo f : x / A x >-> B x}).
Let g : _ -> _ := f.
#[local] HB.instance Definition _ := isFun.Build _ _ _ _ g ffun.
Lemma Pfun : {i : {fun A >-> B} | f = i}.
Admitted.
End Pfun.

Section injPfun.
Context {aT rT} {A : set aT} {B : set rT} {f : {inj A >-> rT}}
   (ffun : {homo f : x / A x >-> B x}).
Let g : _ -> _ := f.
#[local] HB.instance Definition _ := Inject.on g.
#[local] HB.instance Definition _ := isFun.Build _ _ A B g ffun.
Lemma injPfun : {i : {injfun A >-> B} | f = i :> (_ -> _)}.
Admitted.
End injPfun.

Section funPinj.
Context {aT rT} {A : set aT} {B : set rT} {f : {fun A >-> B}}
  (finj : {in A &, injective f}).
Let g : _ -> _ := f.
#[local] HB.instance Definition _ := Fun.on g.
#[local] HB.instance Definition _ := Inj.Build _ _ _ g finj.
Lemma funPinj : {i : {injfun A >-> B} | f = i}.
Admitted.
End funPinj.

Section funPsurj.
Context {aT rT} {A : set aT} {B : set rT} {f : {fun A >-> B}}
        (fsurj : set_surj A B f).
Let g : _ -> _ := f.
#[local] HB.instance Definition _ := Fun.on g.
#[local] HB.instance Definition _ : OCanV _ _ A B g := fsurj.
Lemma funPsurj : {s : {surjfun A >-> B} | f = s}.
Admitted.
End funPsurj.

Section surjPfun.
Context {aT rT} {A : set aT} {B : set rT} {f : {surj A >-> B}}
   (ffun : {homo f : x / A x >-> B x}).
Let g : _ -> _ := f.
#[local] HB.instance Definition _ := Surject.on g.
#[local] HB.instance Definition _ := isFun.Build _ _ A B g ffun.
Lemma surjPfun : {s : {surjfun A >-> B} | f = s :> (_ -> _)}.
Admitted.
End surjPfun.

Section Psplitinj.
Context {aT rT} {A : set aT} {f : aT -> rT} {g} (funK : {in A, cancel f g}).
#[local] HB.instance Definition _ := Can.Build _ _ A f funK.
Lemma Psplitinj : {i : {splitinj A >-> rT} | f = i}.
Admitted.
End Psplitinj.

Section funPsplitinj.
Context {aT rT} {A : set aT} {B : set rT} {f : {fun A >-> B}}.
Context {g} (funK : {in A, cancel f g}).
Let f' : _ -> _ := f.
#[local] HB.instance Definition _ := Fun.on f'.
#[local] HB.instance Definition _ := Can.Build _ _ A f' funK.
Lemma funPsplitinj : {i : {splitinjfun A >-> B} | f = i}.
Admitted.
End funPsplitinj.

Lemma PsplitinjT {aT rT} {f : aT -> rT} {g} : cancel f g ->
  {i : {splitinj [set: aT] >-> rT} | f = i}.
Admitted.

Section funPsplitsurj.
Context {aT rT} {A : set aT} {B : set rT} {f : {fun A >-> B}}.
Context {g : {fun B >-> A}} (funK : {in B, cancel g f}).
Let f' : _ -> _ := f.
#[local] HB.instance Definition _ := Fun.on f'.
#[local] HB.instance Definition _ := CanV.Build _ _ A B f' funS funK.
Lemma funPsplitsurj : {s : {splitsurjfun A >-> B} | f = s :> (_ -> _)}.
Admitted.
End funPsplitsurj.

Lemma PsplitsurjT {aT rT} {f : aT -> rT} {g} : cancel g f ->
  {s : {splitsurjfun [set: aT] >-> [set: rT]} | f = s}.
Admitted.

HB.instance Definition _ T A := @Can2.Build T T A A idfun idfun
   (fun x y => y) (fun x y => y) (fun _ _ => erefl) (fun _ _ => erefl).

Section iter_inv.

Context {aT} {A : set aT}.

Local Lemma iter_fun_subproof n (f : {fun A >-> A}) : isFun _ _ A A (iter n f).
Admitted.

HB.instance Definition _ n f := iter_fun_subproof n f.

Section OInv.
Context {f : {oinv aT >-> aT}}.
HB.instance Definition _ n := OInv.Build _ _ (iter n f)
  (iter n (obind 'oinv_f) \o some).
Lemma oinv_iter n : 'oinv_(iter n f) = iter n (obind 'oinv_f) \o some.
Admitted.
End OInv.

Section OInv.
Context {f : {inv aT >-> aT}}.
Lemma some_iter_inv n : olift (iter n f^-1) = 'oinv_(iter n f).
admit.
Defined.
HB.instance Definition _ n := OInv_Inv.Build _ _ (iter n f) (some_iter_inv n).
Lemma inv_iter n : (iter n f)^-1 = iter n f^-1.
Admitted.
End OInv.

Lemma iter_can_subproof n (f : {injfun A >-> A}) : OInv_Can aT aT A (iter n f).
Admitted.

HB.instance Definition _ f g := iter_can_subproof f g.
HB.instance Definition _ n (f : {injfun A >-> A}) := Inject.on (iter n f).
HB.instance Definition _ n (f : {splitinjfun A >-> A}) := Inject.on (iter n f).
End iter_inv.

Section iter_surj.
Context {aT} {A : set aT}.

Lemma iter_surj_subproof n (f : {surj A >-> A}) : OInv_CanV _ _ A A (iter n f).
Admitted.

HB.instance Definition _ n f := iter_surj_subproof n f.
HB.instance Definition _ n (f : {splitsurj A >-> A}) := Surject.on (iter n f).
HB.instance Definition _ n (f : {surjfun A >-> A}) := Surject.on (iter n f).
HB.instance Definition _ n (f : {splitsurjfun A >-> A}) :=
  Surject.on (iter n f).
HB.instance Definition _ n (f : {bij A >-> A}) := Surject.on (iter n f).
HB.instance Definition _ n (f : {splitbij A >-> A}) := Surject.on (iter n f).

End iter_surj.

Section Unbind.
Context {aT rT} {A : set aT} {B : set rT} (dflt : aT -> rT).
Definition unbind (f : aT -> option rT) x := odflt (dflt x) (f x).

Lemma unbind_fun_subproof (f : {fun A >-> some @` B}) : isFun _ _ A B (unbind f).
Admitted.
HB.instance Definition _ f := unbind_fun_subproof f.

Section Oinv.
Context (f : {oinv aT >-> option rT}).
HB.instance Definition _ := OInv.Build _ _ (unbind f) ('oinv_f \o some).

Lemma oinv_unbind : 'oinv_(unbind f) = 'oinv_f \o some.
Admitted.
End Oinv.
HB.instance Definition _ (f : {oinvfun A >-> some @` B}) := Fun.on (unbind f).

Section Inv.
Context (f : {inv aT >-> option rT}).
Lemma inv_unbind_subproof : olift (f^-1 \o some) = 'oinv_(unbind f).
Admitted.
HB.instance Definition _ := OInv_Inv.Build _ _ (unbind f) inv_unbind_subproof.

Lemma inv_unbind : (unbind f)^-1 = f^-1 \o some.
Admitted.
End Inv.
HB.instance Definition _ (f : {invfun A >-> some @` B}) := Fun.on (unbind f).

Lemma unbind_inj_subproof (f : {injfun A >-> some @` B}) :
   @OInv_Can _ _ A (unbind f).
Admitted.
HB.instance Definition _ f := unbind_inj_subproof f.
HB.instance Definition _ (f : {splitinjfun A >-> some @` B}) :=
  Inject.on (unbind f).

Lemma unbind_surj_subproof (f : {surj A >-> some @` B}) :
   @OInv_CanV _ _ A B (unbind f).
Admitted.
HB.instance Definition _ f := unbind_surj_subproof f.
HB.instance Definition _ (f : {surjfun A >-> some @` B}) :=
  Surject.on (unbind f).
HB.instance Definition _ (f : {splitsurj A >-> some @` B}) :=
  Surject.on (unbind f).
HB.instance Definition _ (f : {splitsurjfun A >-> some @` B}) :=
  Surject.on (unbind f).
HB.instance Definition _ (f : {bij A >-> some @` B}) := Surject.on (unbind f).
HB.instance Definition _ (f : {splitbij A >-> some @` B}) := Bij.on (unbind f).

End Unbind.

Section Odflt.
Context {T} {A : set T} (x : T).

Lemma odflt_unbind : odflt x = unbind (fun=> x) idfun.
Admitted.

HB.instance Definition _ := Inv.Build _ _ (odflt x) some.

HB.instance Definition _ := SplitBij.copy (odflt x)
  [the {bij some @` A >-> A} of unbind (fun=> x) idfun].

End Odflt.

Section SubType.
Context {T : Type} {P : pred T} (sT : subType P) (x0 : sT).

HB.instance Definition _ := OInv.Build sT T val insub.

Lemma oinv_val : 'oinv_val = insub.
Admitted.

Lemma val_bij_subproof : OInv_Can2 sT T setT [set` P] val.
admit.
Defined.
HB.instance Definition _ := val_bij_subproof.

HB.instance Definition _ := Bij.copy insub 'oinv_val.
HB.instance Definition _ := SplitBij.copy (insubd x0)
   (odflt x0 \o 'split_(fun=> val x0) insub).

Lemma inv_insubd : (insubd x0)^-1 = val.
Admitted.

End SubType.
Definition to_setT {T} (x : T) : [set: T].
exact (@SigSub _ _ _ x (mem_set I : x \in setT)).
Defined.
HB.instance Definition _ T := Can.Build T [set: T] setT to_setT
  ((fun _ _ => erefl) : {in setT, cancel to_setT val}).
HB.instance Definition _ T := isFun.Build T _ setT setT to_setT (fun _ _ => I).
HB.instance Definition _ T :=
  SplitInjFun_CanV.Build T _ _ _ to_setT (fun x y => I) inj.
Definition setTbij {T} := [splitbij of @to_setT T].

Lemma inv_to_setT T : (@to_setT T)^-1 = val.
Admitted.

Section subfun.
Context {T} {A B : set T}.
Definition subfun (AB : A `<=` B) (a : A) : B.
Admitted.

Lemma subfun_inj {AB : A `<=` B} : injective (subfun AB).
Admitted.

HB.instance Definition _ (AB : A `<=` B) :=
  SurjFun.copy (subfun AB) [fun subfun AB in setT].
HB.instance Definition _  (AB : A `<=` B) :=
  SurjFun_Inj.Build A B setT (subfun AB @` setT) (subfun AB) (in2W subfun_inj).

End subfun.

Section subfun_eq.
Context {T} {A B : set T}.

Lemma subfun_imageT (AB : A `<=` B) (BA : B `<=` A) : subfun AB @` setT = setT.
Admitted.

Lemma subfun_inv_subproof (AB : A = B) :
  olift (subfun (subsetCW AB)) = 'oinv_(subfun (subsetW AB)).
Admitted.

HB.instance Definition _ (AB : A = B) :=
  OInv_Inv.Build A B (subfun (subsetW AB)) (subfun_inv_subproof AB).

End subfun_eq.

Section seteqfun.
Context {T : Type}.

Definition seteqfun {A B : set T} (AB : A = B) := subfun (subsetW AB).

Context {A B : set T} (AB : A = B).
HB.instance Definition _ := Inv.Build A B (seteqfun AB) (seteqfun (esym AB)).

Lemma seteqfun_can2_subproof : Inv_Can2 A B setT setT (seteqfun AB).
Admitted.
HB.instance Definition _ := seteqfun_can2_subproof.

End seteqfun.

Section incl.
Context  {T} {A B : set T}.
Definition incl (AB : A `<=` B) := @id T.

HB.instance Definition _ (AB : A `<=` B) := Inv.Build _ _ (incl AB) id.
HB.instance Definition _ (AB : A `<=` B) := isFun.Build _ _ A B (incl AB) AB.
HB.instance Definition _ (AB : A `<=` B) :=
  Inv_Can.Build _ _ A (incl AB) (fun _ _ => erefl).

Definition eqincl (AB : A = B) := incl (subsetW AB).
HB.instance Definition _ AB := Inversible.on (eqincl AB).
Lemma eqincl_surj AB : Inv_Can2 _ _ A B (eqincl AB).
Admitted.
HB.instance Definition _ AB := eqincl_surj AB.

End incl.
Notation inclT A := (incl (@subsetT _ _)).

Section mkfun.
Context {aT} {rT} {A : set aT} {B : set rT}.
Notation isfun f := {homo f : x / A x >-> B x}.
Definition mkfun f (fAB : isfun f) := f.
HB.instance Definition _ f fAB := @isFun.Build _ _ A B (@mkfun f fAB) fAB.
Definition mkfun_fun f fAB := [fun of @mkfun f fAB].
HB.instance Definition _ (f : {inj A >-> rT}) fAB := Inject.on (@mkfun f fAB).
HB.instance Definition _ (f : {splitinj A >-> rT}) fAB :=
  SplitInj.on (@mkfun f fAB).
HB.instance Definition _ (f : {surj A >-> B}) fAB :=
  Surject.on (@mkfun f fAB).
HB.instance Definition _ (f : {splitsurj A >-> B}) fAB :=
  SplitSurj.on (@mkfun f fAB).
End mkfun.

Section set_val.
Context {T} {A : set T}.
Definition set_val : A -> T.
exact (eqincl (set_mem_set A) \o val).
Defined.
HB.instance Definition _ := Bij.on set_val.
Lemma oinv_set_val : 'oinv_set_val = insub.
Admitted.
Lemma set_valE : set_val = val.
Admitted.
End set_val.

#[global]
Hint Extern 0 (is_true (set_val _ \in _)) => solve [apply: valP] : core.

HB.instance Definition _ T := CanV.Build T $|T| setT setT squash (fun _ _ => I)
                              (in1W unsquashK).
HB.instance Definition _ T := SplitInj.copy (@unsquash T) squash^-1%FUN.
Definition ssquash {T} := [splitsurj of @squash T].

HB.instance Definition _ (T : countType) :=
  Inj.Build _ _ setT (@choice.pickle T) (in2W (pcan_inj choice.pickleK)).
HB.instance Definition _ (T : countType) :=
  isFun.Build _ _ setT setT (@choice.pickle T) (fun _ _ => I).

Lemma set0fun_inj {P T} : injective (@set0fun P T).
Admitted.

HB.instance Definition _ P T :=
  Inj.Build (@set0 T) P setT set0fun (in2W set0fun_inj).
HB.instance Definition _ P T :=
  isFun.Build _ _ setT setT (@set0fun P T) (fun _ _ => I).

HB.instance Definition _ {m n} {eq_mn : m = n} :=
  Can2.Build 'I_m 'I_n setT setT (cast_ord eq_mn)
    (fun _ _ => I) (fun _ _ => I)
    (in1W (cast_ordK _)) (in1W (cast_ordKV _)).

HB.instance Definition _ (T : finType) :=
  Can2.Build T _ setT setT enum_rank (fun _ _ => I) (fun _ _ => I)
                                    (in1W enum_rankK) (in1W enum_valK).

HB.instance Definition _ (T : finType) :=
  Can2.Build _ T setT setT enum_val (fun _ _ => I) (fun _ _ => I)
                                    (in1W enum_valK) (in1W enum_rankK).
Definition finset_val {T : choiceType} {X : {fset T}} (x : X) : [set` X].
Admitted.
Definition val_finset {T : choiceType} {X : {fset T}} (x : [set` X]) : X.
Admitted.

Lemma finset_valK {T : choiceType} {X : {fset T}} :
  cancel (@finset_val T X) val_finset.
Admitted.

Lemma val_finsetK {T : choiceType} {X : {fset T}} :
  cancel (@val_finset T X) finset_val.
Admitted.

HB.instance Definition _  {T : choiceType} {X : {fset T}} :=
  Can2.Build X _ setT setT finset_val (fun _ _ => I) (fun _ _ => I)
             (in1W finset_valK) (in1W val_finsetK).
HB.instance Definition _  {T : choiceType} {X : {fset T}} :=
  Can2.Build _ X setT setT val_finset (fun _ _ => I) (fun _ _ => I)
             (in1W val_finsetK) (in1W finset_valK).

HB.instance Definition _ n := Can2.Build _ _ setT setT (@ordII n)
   (fun _ _ => I) (fun _ _ => I) (in1W ordIIK) (in1W IIordK).
HB.instance Definition _ n := SplitBij.copy (@IIord n) (ordII^-1).

Definition glue {T T'} {X Y : set T} {A B : set T'}
  of [disjoint X & Y] & [disjoint A & B] :=
  fun (f g : T -> T') (u : T) => if u \in X then f u else g u.

Section Glue12.
Context {T T'} {X Y : set T} {A B : set T'}.
Context {XY : [disjoint X & Y]} {AB : [disjoint A & B]}.
Local Notation gl := (glue XY AB).

Definition glue1 (f g : T -> T') : {in X, gl f g =1 f}.
Admitted.

Definition glue2 (f g : T -> T') : {in Y, gl f g =1 g}.
Admitted.
End Glue12.

Section Glue.
Context {T T'} {X Y : set T} {A B : set T'}.
Context {XY : [disjoint X & Y]} {AB : [disjoint A & B]}.
Local Notation gl := (glue XY AB).

Lemma glue_fun_subproof (f : {fun X >-> A}) (g : {fun Y >-> B}) :
  isFun T T' (X `|` Y) (A `|` B) (gl f g).
Admitted.
HB.instance Definition _ f g := glue_fun_subproof f g.

HB.instance Definition _ (f g : {oinv T >-> T'}) :=
  OInv.Build _ _ (gl f g) (glue AB (eqbRL disj_set_some XY) 'oinv_f 'oinv_g).

HB.instance Definition _  (f : {oinvfun X >-> A}) (g : {oinvfun Y >-> B}) :=
  OInversible.on (gl f g).

Lemma oinv_glue (f : {oinv T >-> T'}) (g : {oinv T >-> T'}) :
  'oinv_(gl f g) = glue AB (eqbRL disj_set_some XY) 'oinv_f 'oinv_g.
Admitted.

Lemma some_inv_glue_subproof (f g : {inv T >-> T'}) :
  some \o (glue AB XY f^-1 g^-1) = 'oinv_(gl f g).
Admitted.

HB.instance Definition _ (f g : {inv T >-> T'}) :=
  OInv_Inv.Build T T' (gl f g) (some_inv_glue_subproof f g).

HB.instance Definition _ (f : {invfun X >-> A}) (g : {invfun Y >-> B}) :=
  Inversible.on (gl f g).

Lemma inv_glue (f : {invfun X >-> A}) (g : {invfun Y >-> B}) :
  (gl f g)^-1 = glue AB XY f^-1 g^-1.
Admitted.

Lemma glueo_can_subproof (f : {injfun X >-> A}) (g : {injfun Y >-> B}) :
  OInv_Can _ _ (X `|` Y) (gl f g).
Admitted.
HB.instance Definition _ f g := glueo_can_subproof f g.

HB.instance Definition _ (f : {splitinjfun X >-> A})
  (g : {splitinjfun Y >-> B}) := Inject.on (gl f g).

Lemma glue_canv_subproof (f : {surj X >-> A}) (g : {surj Y >-> B}) :
  OInv_CanV _ _ (X `|` Y) (A `|` B) (gl f g).
Admitted.
HB.instance Definition _ f g := glue_canv_subproof f g.
HB.instance Definition _ (f : {surjfun X >-> A}) (g : {surjfun Y >-> B}) :=
  Surject.on (gl f g).
HB.instance Definition _ (f : {splitsurj X >-> A}) (g : {splitsurj Y >-> B}) :=
  Surject.on (gl f g).
HB.instance Definition _ (f : {splitsurjfun X >-> A}) (g : {splitsurjfun Y >-> B}) :=
  Surject.on (gl f g).
HB.instance Definition _ (f : {bij X >-> A}) (g : {bij Y >-> B}) :=
  Surject.on (gl f g).
HB.instance Definition _ (f : {splitbij X >-> A}) (g : {splitbij Y >-> B}) :=
  Surject.on (gl f g).

End Glue.

Section addition.
Context {V : zmodType} (x : V).

HB.instance Definition _ := Inv.Build V V (+%R x) (+%R (- x)).

Lemma inv_addr : (+%R x)^-1 = (+%R (- x)).
Admitted.

Lemma addr_can2_subproof : Inv_Can2 V V setT setT (+%R x).
Admitted.
HB.instance Definition _ := addr_can2_subproof.

End addition.

Section addition.
Context {V : zmodType} (x : V).

HB.instance Definition _ := Inv.Build V V (-%R) (-%R).

Lemma inv_oppr : (-%R)^-1 = (-%R).
Admitted.

Lemma oppr_can2_subproof : Inv_Can2 V V setT setT (-%R).
Admitted.
HB.instance Definition _ := oppr_can2_subproof.

End addition.

Section empty.
Context {T : emptyType} {T' : Type} {X : set T}.
Implicit Type Y : set T'.

HB.instance Definition _ := OInv.Build _ _ (@any T T') (fun=> None).

Lemma empty_can_subproof : OInv_Can T T' X any.
Admitted.
HB.instance Definition _ := empty_can_subproof.

Lemma empty_fun_subproof Y : isFun T T' X Y any.
Admitted.
HB.instance Definition _ Y := empty_fun_subproof Y.

Lemma empty_canv_subproof : OInv_CanV T T' X set0 any.
Admitted.
HB.instance Definition _ := empty_canv_subproof.

End empty.

Section surj_lemmas.
Variables aT rT : Type.
Implicit Types (A : set aT) (B : set rT) (f : aT -> rT).

Lemma surj_id A : set_surj A A (@idfun aT).
Admitted.

Lemma surj_set0 B f : set_surj set0 B f -> B = set0.
Admitted.

Lemma surjE f A B : set_surj A B f = (B `<=` f @` A).
Admitted.

Lemma surj_image_eq B A f : f @` A `<=` B -> set_surj A B f -> f @` A = B.
Admitted.

Lemma subl_surj A A' B f : A `<=` A' -> set_surj A B f -> set_surj A' B f.
Admitted.

Lemma subr_surj A B B' f : B' `<=` B -> set_surj A B f -> set_surj A B' f.
Admitted.

Lemma can_surj g f (A : set aT) (B : set rT) :
    {in B, cancel g f} -> g @` B `<=` A ->
  set_surj A B f.
Admitted.

Lemma surj_epi sT A B (f : aT -> rT) (g g' : rT -> sT) :
  set_surj A B f -> {in A, g \o f =1 g' \o f} -> {in B, g =1 g'}.
Admitted.

Lemma epiP A B (f : aT -> rT) : set_surj A B f <->
  forall sT (g g' : rT -> sT), {in A, g \o f =1 g' \o f} -> {in B, g =1 g'}.
Admitted.

End surj_lemmas.
Arguments can_surj {aT rT} g [f A B].
Arguments surj_epi {aT rT sT} A {B} f {g}.

Lemma surj_comp T1 T2 T3 (A : set T1) (B : set T2) (C : set T3) f g:
  set_surj A B f -> set_surj B C g -> set_surj A C (g \o f).
Admitted.

Lemma image_eq {aT rT} {A : set aT} {B : set rT} (f : {surjfun A >-> B}) : f @` A = B.
Admitted.

Lemma oinv_image_sub {aT rT : Type} {A : set aT} {B : set rT}
    (f : {surj A >-> B}) {C : set rT} :
  C `<=` B -> 'oinv_f @` C `<=` some @` (f @^-1` C).
Admitted.
Arguments oinv_image_sub {aT rT A B} f {C} _.

Lemma oinv_Iimage_sub {aT rT : Type} {A : set aT} (f : {inj A >-> rT}) {C : set rT} :
  C `<=` f @` A -> some @` (A `&` f @^-1` C) `<=` 'oinv_f @` C.
Admitted.
Arguments oinv_Iimage_sub {aT rT A} f {C} _.

Lemma oinv_sub_image {aT rT} {A : set aT} {B : set rT} {f : {bij A >-> B}}
   {C : set rT} (CB : C `<=` B) : 'oinv_f @` C = some @` (A `&` f @^-1` C).
Admitted.
Arguments oinv_sub_image {aT rT A B} f {C} _.

Lemma preimageEoinv {aT rT} {B : set rT} {f : {bij [set: aT] >-> B}}
   {C : set rT} (CB : C `<=` B) : some @` (f @^-1` C) = 'oinv_f @` C.
Admitted.
Arguments preimageEoinv {aT rT B} f {C} _.

Lemma inv_image_sub {aT rT : Type} {A : set aT} {B : set rT}
    (f : {splitsurj A >-> B}) {C : set rT} :
  C `<=` B -> f^-1 @` C `<=` f @^-1` C.
Admitted.
Arguments inv_image_sub {aT rT A B} f {C} _.

Lemma inv_Iimage_sub {aT rT : Type} {A : set aT} (f : {splitinj A >-> rT}) {C : set rT} :
  C `<=` f @` A ->  A `&` f @^-1` C `<=` f^-1 @` C.
Admitted.
Arguments inv_Iimage_sub {aT rT A} f {C} _.

Lemma inv_sub_image {aT rT} {A : set aT} {B : set rT} {f : {splitbij A >-> B}}
    {C : set rT} (CB : C `<=` B) :
  f^-1 @` C = A `&` f @^-1` C.
Admitted.
Arguments inv_sub_image {aT rT A B} f {C} _.

Lemma preimageEinv {aT rT} {B : set rT} {f : {splitbij [set: aT] >-> B}}
    {C : set rT} (CB : C `<=` B) : f @^-1` C = f^-1 @` C.
Admitted.
Arguments preimageEinv {aT rT B} f {C} _.

Lemma reindex_bigcup {aT rT I} (f : aT -> I) (P : set aT) (Q : set I)
    (F : I -> set rT) : set_fun P Q f -> set_surj P Q f ->
  \bigcup_(x in Q) F x = \bigcup_(x in P) F (f x).
Admitted.
Arguments reindex_bigcup {aT rT I} f P Q.

Lemma reindex_bigcap {aT rT I} (f : aT -> I) (P : set aT) (Q : set I)
    (F : I -> set rT) : set_fun P Q f -> set_surj P Q f ->
  \bigcap_(x in Q) F x = \bigcap_(x in P) F (f x).
Admitted.
Arguments reindex_bigcap {aT rT I} f P Q.

Lemma bigcap_bigcup T I J (D : set I) (E : set J) (F : I -> J -> set T) :
  J ->
  \bigcap_(i in D) \bigcup_(j in E) F i j =
  \bigcup_(f in set_fun D E) \bigcap_(i in D) F i (f i).
Admitted.

Lemma trivIset_inj T I (D : set I) (F : I -> set T) :
  (forall i, D i -> F i !=set0) -> trivIset D F -> set_inj D F.
Admitted.

Section set_bij_lemmas.
Context {aT rT : Type} {A : set aT} {B : set rT} {f : aT -> rT}.
Definition fun_set_bij of set_bij A B f := f.
Context (fbij : set_bij A B f).
Local Notation g := (fun_set_bij fbij).

Lemma set_bij_inj : {in A &, injective f}.
Admitted.

Lemma set_bij_homo : {homo f : x / A x >-> B x}.
Admitted.

Lemma set_bij_sub : f @` A `<=` B.
Admitted.

Lemma set_bij_surj : set_surj A B f.
Admitted.

HB.instance Definition _ : OCanV _ _ _ _ g := set_bij_surj.
HB.instance Definition _ := isFun.Build _ _ A B g set_bij_homo.
HB.instance Definition _ := SurjFun_Inj.Build _ _ A B g set_bij_inj.

End set_bij_lemmas.
Coercion fun_set_bij : set_bij >-> Funclass.

Coercion set_bij_bijfun aT rT (A : set aT) (B : set rT) (f : aT -> rT)
    (fS : set_bij A B f) := Bij.on (fun_set_bij fS).

Section Pbij.
Context {aT rT} {A : set aT} {B : set rT} {f : aT -> rT} (fbij : set_bij A B f).
#[local] HB.instance Definition _ : @Bij _ _ A B f := fbij.
Definition bij_of_set_bijection := [bij of f].
Lemma Pbij : {s : {bij A >-> B} | f = s}.
Admitted.
End Pbij.
Coercion bij_of_set_bijection : set_bij >-> Bij.type.

Lemma bij {aT rT} {A : set aT} {B : set rT} {f : {bij A >-> B}} : set_bij A B f.
Admitted.
Definition phant_bij aT rT (A : set aT) (B : set rT) (f : {bij A >-> B}) of
  phantom (_ -> _) f := @bij _ _ _ _ f.
Notation "''bij_' f" := (phant_bij (Phantom (_ -> _) f)) : form_scope.
#[global] Hint Extern 0 (set_bij _ _ _) => solve [apply: bij] : core.

Section PbijTT.
Context {aT rT} {f : aT -> rT} (fbijTT : bijective f).
#[local] HB.instance Definition _ := @BijTT.Build _ _ f fbijTT.
Definition bijection_of_bijective := [splitbij of f].
Lemma PbijTT : {s : {splitbij [set: aT] >-> [set: rT]} | f = s}.
Admitted.
End PbijTT.

Lemma setTT_bijective aT rT (f : aT -> rT) :
  set_bij [set: aT] [set: rT] f = bijective f.
Admitted.

Lemma bijTT {aT rT}  {f : {bij [set: aT] >-> [set: rT]}} : bijective f.
Admitted.
Definition phant_bijTT aT rT (f : {bij [set: aT] >-> [set: rT]})
   of phantom (_ -> _) f := @bijTT _ _ f.
Notation "''bijTT_'  f" := (phant_bijTT (Phantom (_ -> _) f)) : form_scope.
#[global] Hint Extern 0 (bijective _) => solve [apply: bijTT] : core.

Section patch.
Context {aT rT : Type} (d : aT -> rT) (A : set aT).
Definition patch (f : aT -> rT) u := if u \in A then f u else d u.

Lemma patchT f : {in A, patch f =1 f}.
Admitted.
Lemma patchN f : {in [predC A], patch f =1 d}.
Admitted.
Lemma patchC f : {in ~` A, patch f =1 d}.
Admitted.

HB.instance Definition _ f :=
  SurjFun.copy (patch f) [fun patch f in A].

Section inj.
Context (f : {inj A >-> rT}).
Let g := patch f.
Lemma patch_inj_subproof : Inj aT rT A g.
Admitted.
HB.instance Definition _ := patch_inj_subproof.
HB.instance Definition _ := Inject.copy (patch f) [fun g in A].
End inj.

End patch.
Notation restrict := (patch (fun=> point)).
Notation "f \_ D" := (restrict D f) : fun_scope.

Lemma patchE aT (rT : pointedType) (f : aT -> rT) (B : set aT) x :
  (f \_ B) x = if x \in B then f x else point.
Admitted.

Lemma patch_pred {I T} (D : {pred I}) (d f : I -> T) :
  patch d D f = fun i => if D i then f i else d i.
Admitted.

Lemma preimage_restrict (aT : Type) (rT : pointedType)
     (f : aT -> rT) (D : set aT) (B : set rT) :
  (f \_ D) @^-1` B = (if point \in B then ~` D else set0) `|` D `&` f @^-1` B.
Admitted.

Lemma comp_patch {aT rT sT : Type} (g : aT -> rT) D (f : aT -> rT) (h : rT -> sT) :
  h \o patch g D f = patch (h \o g) D (h \o f).
Admitted.

Lemma patch_setI {aT rT : Type} (g : aT -> rT) D D' (f : aT -> rT) :
   patch g (D `&` D') f = patch g D (patch g D' f).
Admitted.

Lemma patch_set0 {aT rT : Type} (g : aT -> rT) (f : aT -> rT) :
  patch g set0 f = g.
Admitted.

Lemma patch_setT {aT rT : Type} (g : aT -> rT) (f : aT -> rT) :
  patch g setT f = f.
Admitted.

Lemma restrict_comp {aT} {rT sT : pointedType} (h : rT -> sT) (f : aT -> rT) D :
  h point = point -> (h \o f) \_ D = h \o (f \_ D).
Admitted.
Arguments restrict_comp {aT rT sT} h f D.

Lemma trivIset_restr (T I : Type) (D D' : set I) (F : I -> set T) :
    trivIset D' (F \_ D) = trivIset (D `&` D') F.
Admitted.

Section RestrictionLeft.
Context {U V : Type} (v : V) {A : set U} {B : set V}.

Local Notation restrict := (patch (fun=> v) A).
Definition sigL (f : U -> V) : A -> V.
admit.
Defined.

Lemma sigL_isfun (f : {fun A >-> B}) : isFun _ _ [set: A] B (sigL f).
admit.
Defined.
HB.instance Definition _ (f : {fun A >-> B}) := sigL_isfun f.

Definition sigLfun (f : {fun A >-> B}) := [fun of sigL f].
Definition valL_ (f : A -> V) : U -> V.
exact (((@oapp _ _)^~ v) f \o 'oinv_set_val).
Defined.

Lemma valL_isfun (f : {fun [set: A] >-> B}) :
  isFun _ _ A B (valL_ (f : _ -> _)).
Admitted.
HB.instance Definition _ (f : {fun [set: A] >-> B}) := valL_isfun f.
Definition valLfun_ (f : {fun [set: A] >-> B}) := [fun of valL_ f].

Lemma sigLE (f : U -> V) x (xA : x \in A) :
  sigL f (SigSub xA) = f x.
admit.
Defined.

Lemma eq_sigLP (f g : U -> V):
  {in A, f =1 g} <-> sigL f = sigL g.
Admitted.

Lemma eq_sigLfunP (f g : {fun A >-> B}) :
  {in A, f =1 g} <-> sigLfun f = sigLfun g.
Admitted.

Lemma sigLK : valL_ \o sigL = restrict.
Admitted.

Lemma valLK : cancel valL_ sigL.
Admitted.

Lemma valLfunK : cancel valLfun_ sigLfun.
Admitted.

Lemma sigL_valL : sigL \o valL_ = id.
Admitted.

Lemma sigL_valLfun : sigLfun \o valLfun_ = id.
Admitted.

Lemma sigL_restrict : sigL \o restrict = sigL.
Admitted.

Lemma image_sigL  : range sigL = setT.
Admitted.

Lemma eq_restrictP (f g : U -> V): {in A, f =1 g} <-> restrict f = restrict g.
Admitted.

End RestrictionLeft.
Arguments sigL {U V} A f u /.
Arguments sigLE {U V} A f x.
Arguments valL_ {U V} v {A} f u /.
Notation "''valL_' v" := (valL_ v) : form_scope.
Notation "''valLfun_' v" := (valLfun_ v) : form_scope.
Notation valL := (valL_ point).

Section RestrictionRight.
Context {U V : Type} {A : set V}.
Definition sigR (f : {fun [set: U] >-> A}) (u : U) : A.
Admitted.
HB.instance Definition _ f := Fun.copy (sigR f) (totalfun _).

Definition valR (f : U -> A) := set_val \o totalfun f.
HB.instance Definition _ f := Fun.on (valR f).
Definition valR_fun (f : U -> A) : {fun [set: U] >-> A}.
exact ([fun of valR f]).
Defined.

Lemma sigRK (f : {fun [set: U] >-> A}) : valR (sigR f) = f.
Admitted.

Lemma sigR_funK (f : {fun [set: U] >-> A}) : valR_fun (sigR f) = f.
Admitted.

Lemma valRP (f : U -> A) x : A (valR f x).
Admitted.

Lemma valRK : cancel valR_fun sigR.
Admitted.

End RestrictionRight.
Arguments sigR {U V A} f u /.

Section RestrictionLeftInv.
Context {U V : Type} (v : V) {A : set U} {B : set V}.
Local Notation rl := (sigL A).
Local Notation rr := sigR.
Local Notation el := 'valL_v.
Local Notation er := valR.

HB.instance Definition _ (f : {oinv U >-> V}) :=
  @OInv.Build _ _ (rl f) (obind insub \o 'oinv_f).
HB.instance Definition _ (f : {oinvfun A >-> B}) := Fun.on (rl f).

Lemma oinv_sigL (f : {oinv U >-> V}) : 'oinv_(rl f) = obind insub \o 'oinv_f.
Admitted.

Lemma sigL_inj_subproof (f : {inj A >-> V}) : @OInv_Can _ _ setT (rl f).
admit.
Defined.
HB.instance Definition _ f := sigL_inj_subproof f.
HB.instance Definition _ (f : {injfun A >-> B}) := Fun.on (rl f).

Lemma sigL_surj_subproof (f : {surj A >-> B}) : @OInv_CanV _ _ setT B (rl f).
admit.
Defined.
HB.instance Definition _ f := sigL_surj_subproof f.
HB.instance Definition _ (f : {surjfun A >-> B}) := Fun.on (rl f).
HB.instance Definition _ (f : {bij A >-> B}) := Fun.on (rl f).

HB.instance Definition _ (f : {oinvfun [set: V] >-> A}) :=
  @OInv.Build _ _ (rr f) (rl 'oinv_f).

Lemma oinv_sigR (f : {oinvfun [set: V] >-> A}) :
  'oinv_(rr f) = (rl 'oinv_f).
Admitted.

Lemma sigR_inj_subproof (f : {injfun [set: V] >-> A}) :
   @OInv_Can _ _ setT (rr f).
admit.
Defined.
HB.instance Definition _ f := sigR_inj_subproof f.

Lemma sigR_surj_subproof (f : {surjfun [set: V] >-> A}) :
  @OInv_CanV _ _ setT setT (rr f).
admit.
Defined.
HB.instance Definition _ f := sigR_surj_subproof f.

Lemma sigR_some_inv (f : {invfun [set: V] >-> A}) :
  olift (rl f^-1) = 'oinv_(rr f).
Admitted.
HB.instance Definition _ (f : {bij [set: V] >-> A}) := Fun.on (rr f).

HB.instance Definition _ (f : {invfun [set: V] >-> A}) :=
   @OInv_Inv.Build _ _ (rr f) (rl f^-1) (sigR_some_inv f).

Lemma inv_sigR (f : {invfun [set: V] >-> A}) : (rr f)^-1 = (rl f^-1).
Admitted.

HB.instance Definition _ (f : {splitinjfun [set: V] >-> A}) := Inject.on (rr f).

HB.instance Definition _ (f : {splitsurjfun [set: V] >-> A}) := Surject.on (rr f).
HB.instance Definition _ (f : {splitbij [set: V] >-> A}) := Fun.on (rr f).

Lemma sigL_some_inv (f : {splitbij A >-> [set: V]}) :
  olift (rr [fun of f^-1]) = 'oinv_(rl f).
Admitted.
HB.instance Definition _ (f : {splitbij A >-> [set: V]}) :=
  OInv_Inv.Build _ _ (rl f) (sigL_some_inv f).

Lemma inv_sigL  (f : {splitbij A >-> [set: V]}) :
  (rl f)^-1 = (rr [fun of f^-1]).
Admitted.

HB.instance Definition _ (f : {oinv A >-> V}) :=
  @OInv.Build _ _ (el f) (omap set_val \o 'oinv_f).
HB.instance Definition _ (f : {oinvfun [set: A] >-> B}) := Fun.on (el f).

Lemma oinv_valL (f : {oinv A >-> V}) :
  'oinv_(el f) = omap set_val \o 'oinv_f.
Admitted.

Lemma oapp_comp_x {aT rT sT} (f : aT -> rT) (g : rT -> sT) (x : rT) y :
  oapp (g \o f) (g x) y = g (oapp f x y).
Admitted.

Lemma valL_inj_subproof (f : {inj [set: A] >-> V}) : @OInv_Can _ _ A (el f).
admit.
Defined.
HB.instance Definition _ f := valL_inj_subproof f.
HB.instance Definition _ (f : {injfun [set: A] >-> B}) := Inject.on (el f).

Lemma valL_surj_subproof (f : {surj [set: A] >-> B}) : @OInv_CanV _ _ A B (el f).
Admitted.
HB.instance Definition _ f := valL_surj_subproof f.
HB.instance Definition _ (f : {surjfun [set: A] >-> B}) := Surject.on (el f).
HB.instance Definition _ (f : {bij [set: A] >-> B}) := Surject.on (el f).

Lemma valL_some_inv (f : {inv A >-> V}) : olift (er f^-1) = 'oinv_(el f).
Admitted.
HB.instance Definition _ (f : {inv A >-> V}) :=
  OInv_Inv.Build _ _ (el f) (valL_some_inv f).
HB.instance Definition _ (f : {invfun [set: A] >-> B}) := Fun.on (el f).

Lemma inv_valL (f : {inv A >-> V}) : (el f)^-1 = er f^-1.
Admitted.

HB.instance Definition _ (f : {splitinj [set: A] >-> V}) := Inject.on (el f).
HB.instance Definition _ (f : {splitinjfun [set: A] >-> B}) := Fun.on (el f).

HB.instance Definition _ (f : {splitsurj [set: A] >-> B}) := Surject.on (el f).
HB.instance Definition _ (f : {splitsurjfun [set: A] >-> B}) := Fun.on (el f).
HB.instance Definition _ (f : {splitbij [set: A] >-> B}) := Fun.on (el f).

Lemma sigL_injP (f : U -> V) :
  injective (rl f) <-> {in A &, injective f}.
Admitted.

Lemma sigL_surjP (f : U -> V) :
  set_surj [set: A] B (rl f) <-> set_surj A B f.
Admitted.

Lemma sigL_funP (f : U -> V) :
  set_fun [set: A] B (rl f) <-> set_fun A B f.
Admitted.

Lemma sigL_bijP (f : U -> V) :
  set_bij [set: A] B (rl f) <-> set_bij A B f.
Admitted.

Lemma valL_injP (f : A -> V) : {in A &, injective (el f)} <-> injective f.
Admitted.

Lemma valL_surjP (f : A -> V) :
  set_surj A B (el f) <-> set_surj setT B f.
Admitted.

Lemma valLfunP (f : A -> V) :
  set_fun A B (el f) <-> set_fun setT B f.
Admitted.

End RestrictionLeftInv.

Section ExtentionLeftInv.

End ExtentionLeftInv.

Section Restrictions2.

End Restrictions2.

Section set_bij_basic_lemmas.

End set_bij_basic_lemmas.

Section set_bij_lemmas.

End set_bij_lemmas.

Section set_bij_lemmas.

End set_bij_lemmas.

Section pointed_inverse.

Section pPbij.
End pPbij.

Section pPinj.
End pPinj.

Section injpPfun.
End injpPfun.

Section funpPinj.
End funpPinj.

End pointed_inverse.

Section function_space.
Local Open Scope ring_scope.
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

Section function_space_lemmas.

End function_space_lemmas.

End functions.
Module Export topology.
Import mathcomp.ssreflect.all_ssreflect.
Import mathcomp.algebra.all_algebra.
Import mathcomp.classical.boolp.
Import mathcomp.classical.classical_sets.
Reserved Notation "'\forall' x '\near' x_0 , P"
  (at level 200, x name, P at level 200,
   format "'\forall'  x  '\near'  x_0 ,  P").
Reserved Notation "x \is_near F" (at level 10, format "x  \is_near  F").

Set Implicit Arguments.
Unset Strict Implicit.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

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
Import mathcomp.ssreflect.all_ssreflect.
Import mathcomp.algebra.ssralg.
Import mathcomp.algebra.ssrnum.
Import mathcomp.classical.classical_sets.

Set Implicit Arguments.
Unset Strict Implicit.
Import Num.Theory.
Local Open Scope ring_scope.

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
Import mathcomp.classical.boolp.
Import mathcomp.analysis.signed.
Import GRing.Theory.

Reserved Notation "{o_ F f }" (at level 0, F at level 0, format "{o_ F  f }").

Reserved Notation "[o_ x e 'of' f ]" (at level 0, x, e at level 0, only parsing).
Reserved Notation "f '=o_' F h"
  (at level 70, no associativity,
   F at level 0, h at next level,
   format "f  '=o_' F  h").
Local Open Scope classical_set_scope.
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
