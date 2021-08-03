(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "+implicit-core-hint-db,+implicits-in-term,+non-reversible-notation,+deprecated-intros-until-0,+deprecated-focus,+unused-intro-pattern,+variable-collision,+omega-is-deprecated,+deprecated-instantiate-syntax,+non-recursive" "-w" "-notation-overridden,-undeclared-scope,-deprecated-hint-rewrite-without-locality,-deprecated-hint-constr,-fragile-hint-constr,-native-compiler-disabled,-ambiguous-paths" "-w" "-deprecated-native-compiler-option" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/fiat_crypto/src" "Crypto" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/fiat_crypto/rupicola/src/Rupicola" "Rupicola" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/fiat_crypto/rupicola/bedrock2/bedrock2/src/bedrock2" "bedrock2" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/fiat_crypto/rupicola/bedrock2/bedrock2/src/bedrock2Examples" "bedrock2Examples" "-Q" "/github/workspace/builds/coq/coq-failing/_build_ci/fiat_crypto/rupicola/bedrock2/deps/coqutil/src/coqutil" "coqutil" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Bignums" "Bignums" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Coqprime" "Coqprime" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Rewriter" "Rewriter" "-I" "/github/workspace/builds/coq/coq-failing/_build_ci/fiat_crypto/rupicola/src" "-I" "/github/workspace/builds/coq/coq-failing/_build_ci/fiat_crypto/rupicola/bedrock2/bedrock2/src" "-I" "/github/workspace/builds/coq/coq-failing/_build_ci/fiat_crypto/rupicola/bedrock2/deps/coqutil/src" "-top" "Projective" "-native-compiler" "no") -*- *)
(* File reduced by coq-bug-finder from original input, then from 306 lines to 90 lines, then from 162 lines to 216 lines, then from 220 lines to 107 lines, then from 179 lines to 284 lines, then from 287 lines to 114 lines, then from 185 lines to 249 lines, then from 253 lines to 130 lines, then from 201 lines to 292 lines, then from 296 lines to 188 lines, then from 258 lines to 559 lines, then from 562 lines to 311 lines, then from 375 lines to 585 lines, then from 589 lines to 439 lines, then from 500 lines to 994 lines, then from 995 lines to 517 lines, then from 565 lines to 638 lines, then from 642 lines to 519 lines, then from 566 lines to 735 lines, then from 738 lines to 661 lines, then from 706 lines to 950 lines, then from 954 lines to 668 lines, then from 705 lines to 847 lines, then from 851 lines to 763 lines, then from 799 lines to 825 lines, then from 829 lines to 767 lines, then from 803 lines to 889 lines, then from 893 lines to 774 lines, then from 806 lines to 987 lines, then from 991 lines to 873 lines, then from 903 lines to 982 lines, then from 986 lines to 882 lines, then from 911 lines to 960 lines, then from 964 lines to 887 lines, then from 916 lines to 1127 lines, then from 1131 lines to 1066 lines *)
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
Require Coq.Classes.Morphisms.
Require Crypto.Util.GlobalSettings.
Require Crypto.Util.FixCoqMistakes.
Module Export Crypto_DOT_Util_DOT_Notations_WRAPPED.
Module Export Notations.
 
Export Crypto.Util.FixCoqMistakes.
Export Crypto.Util.GlobalSettings.

 

Reserved Notation "x -> y" (at level 99, right associativity, y at level 200).
Reserved Notation "()" (at level 0).
Reserved Infix "∘" (at level 40, left associativity).
Reserved Infix "∘ᶠ" (at level 40, left associativity).
Reserved Infix "∘f" (at level 40, left associativity).
Reserved Infix "'o'" (at level 40, left associativity).
Reserved Infix "==" (at level 70, no associativity).
Reserved Infix "===" (at level 70, no associativity).
Reserved Infix "====" (at level 70, no associativity).
Reserved Infix "=====" (at level 70, no associativity).
Reserved Infix "======" (at level 70, no associativity).
Reserved Infix "~=" (at level 70, no associativity).
Reserved Infix "=?" (at level 70, no associativity).
Reserved Infix "<?" (at level 70, no associativity).
Reserved Infix "<=?" (at level 70, no associativity).
Reserved Infix "!=?" (at level 70, no associativity).
Reserved Infix "?=" (at level 70, no associativity).
Reserved Infix "?<" (at level 70, no associativity).
Reserved Infix "=n?" (at level 70, no associativity).
Reserved Infix "=Z?" (at level 70, no associativity).
Reserved Infix "=ₙ?" (at level 70, no associativity).
Reserved Infix "=ℤ?" (at level 70, no associativity).
Reserved Infix "=ᶻ?" (at level 70, no associativity).
Reserved Infix "=ⁿ?" (at level 70, no associativity).
Reserved Notation "f ?" (at level 11, format "f ?", left associativity).
Reserved Notation "f [ ? ]" (at level 9, format "f [ ? ]").
Reserved Notation "f +" (at level 50, format "f +").
Reserved Notation "f *" (at level 40, format "f *").
 
Reserved Notation "x \in A"
  (at level 70, format "'[hv' x '/ '  \in  A ']'", no associativity).
Reserved Notation "x \notin A"
  (at level 70, format "'[hv' x '/ '  \notin  A ']'", no associativity).
Reserved Notation "x ∈ A"
  (at level 70, format "'[hv' x '/ '  ∈  A ']'", no associativity).
Reserved Notation "x ∉ A"
  (at level 70, format "'[hv' x '/ '  ∉  A ']'", no associativity).
Reserved Notation "x +' y" (at level 50, left associativity).
Reserved Notation "x -' y" (at level 50, left associativity).
Reserved Notation "x *' y" (at level 40, left associativity).
Reserved Notation "x /' y" (at level 40, left associativity).
Reserved Notation "-' x" (at level 35, right associativity).
Reserved Notation "/' x" (at level 35, right associativity).
Reserved Notation "x ^' y" (at level 30, right associativity).
Reserved Infix ".+" (at level 50).
Reserved Infix ".*" (at level 50).
Reserved Notation "' x" (at level 20, no associativity, format "' x").
Reserved Notation "x ^ 2" (at level 30, format "x ^ 2").
Reserved Notation "x ^ 3" (at level 30, format "x ^ 3").
Reserved Notation "2 ^ e" (at level 30, format "2 ^ e", only printing).
Reserved Infix "mod" (at level 40, no associativity).
Reserved Infix "mod'" (at level 40, no associativity).
Reserved Notation "'canonical' 'encoding' 'of' T 'as' B" (at level 50).
Reserved Notation "@ 'is_eq_dec' T R" (at level 10, T at level 8, R at level 8).
Reserved Infix "@" (left associativity, at level 11).
Reserved Infix "@1" (left associativity, at level 11).
Reserved Infix "@₁" (left associativity, at level 11).
Reserved Infix "@@@" (left associativity, at level 11).
Reserved Infix "<<'" (at level 30, no associativity).
Reserved Infix ">>'" (at level 30, no associativity).
Reserved Infix "<<" (at level 30, no associativity).
Reserved Infix ">>" (at level 30, no associativity).
Reserved Infix ">>>" (at level 30, no associativity).
Reserved Infix "&'" (at level 50).
 
Reserved Infix "&''" (at level 50).
Reserved Infix "|'" (at level 50).
Reserved Infix "∣" (at level 50).
Reserved Infix "∣'" (at level 50).
Reserved Infix "~=" (at level 70).
Reserved Infix "==" (at level 70, no associativity).
Reserved Notation "x == y  :>  T"
         (at level 70, y at next level, no associativity).
Reserved Infix "=~>" (at level 70, no associativity).
Reserved Infix "<~=" (at level 70, no associativity).
Reserved Infix "<~=~>" (at level 70, no associativity).
Reserved Infix "≡" (at level 70, no associativity).
Reserved Infix "≢" (at level 70, no associativity).
Reserved Infix "≡_n" (at level 70, no associativity).
Reserved Infix "≢_n" (at level 70, no associativity).
Reserved Infix "≡_r" (at level 70, no associativity).
Reserved Infix "≢_r" (at level 70, no associativity).
Reserved Infix "≡ᵣ" (at level 70, no associativity).
Reserved Infix "≢ᵣ" (at level 70, no associativity).
Reserved Infix "≡_p" (at level 70, no associativity).
Reserved Infix "≢_p" (at level 70, no associativity).
Reserved Infix "≡ₚ" (at level 70, no associativity).
Reserved Infix "≢ₚ" (at level 70, no associativity).
Reserved Infix "≡₃₂" (at level 70, no associativity).
Reserved Infix "≢₃₂" (at level 70, no associativity).
Reserved Infix "≡₆₄" (at level 70, no associativity).
Reserved Infix "≢₆₄" (at level 70, no associativity).
Reserved Infix "≡₁₂₈" (at level 70, no associativity).
Reserved Infix "≢₁₂₈" (at level 70, no associativity).
Reserved Infix "≡₂₅₆" (at level 70, no associativity).
Reserved Infix "≢₂₅₆" (at level 70, no associativity).
Reserved Infix "≡₅₁₂" (at level 70, no associativity).
Reserved Infix "≢₅₁₂" (at level 70, no associativity).
Reserved Infix "|||" (at level 50, left associativity).
Reserved Notation "A ||->{ f } B" (at level 50, left associativity).
 
Reserved Notation "A |||->{ f } B" (at level 50, left associativity).
 
 
Reserved Notation "<" (at level 71).
Reserved Notation ">" (at level 71).
Reserved Notation "<=" (at level 71).
Reserved Notation ">=" (at level 71).
Reserved Notation "≤" (at level 71).
Reserved Notation "≥" (at level 71).
Reserved Notation "a !== b" (at level 70, no associativity).
Reserved Notation "a ≢ b" (at level 70, no associativity).
Reserved Notation "$$ v" (at level 40).
Reserved Notation "& x" (at level 30).
Reserved Notation "** x" (at level 30).
Reserved Notation "A <- X ; B" (at level 70, X at next level, right associativity, format "'[v' A  <-  X ; '/' B ']'").
Reserved Notation "A <-- X ; B" (at level 70, X at next level, right associativity, format "'[v' A  <--  X ; '/' B ']'").
Reserved Notation "A <--- X ; B" (at level 70, X at next level, right associativity, format "'[v' A  <---  X ; '/' B ']'").
Reserved Notation "A <---- X ; B" (at level 70, X at next level, right associativity, format "'[v' A  <----  X ; '/' B ']'").
Reserved Notation "A <----- X ; B" (at level 70, X at next level, right associativity, format "'[v' A  <-----  X ; '/' B ']'").
Reserved Notation "A ;; B" (at level 70, right associativity, format "'[v' A ;; '/' B ']'").
Reserved Notation "A ';;L' B" (at level 70, right associativity, format "'[v' A ';;L' '/' B ']'").
Reserved Notation "A ';;R' B" (at level 70, right associativity, format "'[v' A ';;R' '/' B ']'").
Reserved Notation "A ;;->{ f } B" (at level 70, right associativity, format "'[v' A ;;->{ f } '/' B ']'").
Reserved Notation "A ;;; B" (at level 70, right associativity, format "'[v' A ;;; '/' B ']'").
Reserved Notation "u [ i ]" (at level 30).
Reserved Notation "v [[ i ]]" (at level 30).
Reserved Notation "u {{ i }}" (at level 30).
Reserved Notation "a # b" (at level 55, no associativity).
 
Reserved Notation "'olet' x .. y <- X ; Y"
         (at level 70, X at next level, x binder, y binder, right associativity, format "'[v' 'olet'  x  ..  y  <-  X ; '/' Y ']'").
Reserved Notation "'slet' x .. y <- X ; Y"
         (at level 70, X at next level, x binder, y binder, right associativity, format "'[v' 'slet'  x  ..  y  <-  X ; '/' Y ']'").
Reserved Notation "'plet' x := y 'in' z"
         (at level 200, z at level 200, format "'plet'  x  :=  y  'in' '//' z").
Reserved Notation "'subst_let' x := y 'in' z"
         (at level 200, z at level 200, format "'subst_let'  x  :=  y  'in' '//' z").
Reserved Notation "'nlet' x := A 'in' b"
         (at level 200, b at level 200, x at level 99, format "'nlet'  x  :=  A  'in' '//' b").
Reserved Notation "'nlet' x : tx := A 'in' b"
         (at level 200, b at level 200, x at level 99, format "'nlet'  x  :  tx  :=  A  'in' '//' b").
Reserved Notation "'slet' x .. y := A 'in' b"
         (at level 200, x binder, y binder, b at level 200, format "'slet'  x .. y  :=  A  'in' '//' b").
Reserved Notation "'llet' x := A 'in' b"
         (at level 200, b at level 200, format "'llet'  x  :=  A  'in' '//' b").
Reserved Notation "'expr_let' x := A 'in' b"
         (at level 200, b at level 200, format "'expr_let'  x  :=  A  'in' '//' b").
Reserved Notation "'mlet' x := A 'in' b"
         (at level 200, b at level 200, format "'mlet'  x  :=  A  'in' '//' b").
 
Reserved Notation "'dlet_nd' x .. y := v 'in' f"
         (at level 200, x binder, y binder, f at level 200, format "'dlet_nd'  x .. y  :=  v  'in' '//' f").
Reserved Notation "'dlet' x .. y := v 'in' f"
         (at level 200, x binder, y binder, f at level 200, format "'dlet'  x .. y  :=  v  'in' '//' f").
Reserved Notation "'pflet' x , pf := y 'in' f"
         (at level 200, f at level 200, format "'pflet'  x ,  pf  :=  y  'in' '//' f").

Notation "'subst_let' x := y 'in' z" := (match y return _ with x => z end) (only parsing).

Reserved Notation "'λ' x .. y , t" (at level 200, x binder, y binder, right associativity, format "'λ'  x .. y , '//' t").
Reserved Notation "'λn'  x .. y , t" (at level 200, right associativity).
Reserved Notation "x ::> ( max_bitwidth = v )"
         (at level 70, no associativity, format "x  ::>  ( max_bitwidth  =  v )").
Require Crypto.Algebra.NsatzTactic.

Tactic Notation "unique" "pose" "proof" constr(defn) :=
  let T := type of defn in
  match goal with
  | [ H : T |- _ ] => fail 1
  | _ => pose proof defn
  end.

Ltac debuglevel := constr:(0%nat).

Ltac solve_debugfail tac :=
  solve [tac] ||
        ( let dbg := debuglevel in
          match dbg with
          | O => idtac
          | _ => match goal with |- ?G => idtac "couldn't prove" G end
          end;
          fail).

Import Coq.Lists.List.

Module Export Nsatz.
  Import Algebra.NsatzTactic.
  Notation check_correct := check_correct.
  Notation PEevalR := PEevalR.
End Nsatz.
Lemma cring_sub_diag_iff {R zero eq sub} `{cring:Cring.Cring (R:=R) (ring0:=zero) (ring_eq:=eq) (sub:=sub)}
  : forall x y, eq (sub x y) zero <-> eq x y.
admit.
Defined.

Ltac get_goal := lazymatch goal with |- ?g => g end.

Ltac nsatz_equation_implications_to_list eq zero g :=
  lazymatch g with
  | eq ?p zero => constr:(p::nil)
  | eq ?p zero -> ?g => let l := nsatz_equation_implications_to_list eq zero g in constr:(p::l)
  end.

Ltac nsatz_reify_equations eq zero :=
  let g := get_goal in
  let lb := nsatz_equation_implications_to_list eq zero g in
  lazymatch (eval red in (Ncring_tac.list_reifyl (lterm:=lb))) with
    (?variables, ?le) =>
    lazymatch (eval compute in (List.rev le)) with
    | ?reified_goal::?reified_givens => constr:((variables, reified_givens, reified_goal))
    end
  end.

Ltac nsatz_get_free_variables reified_package :=
  lazymatch reified_package with (?fv, _, _) => fv end.

Ltac nsatz_get_reified_givens reified_package :=
  lazymatch reified_package with (_, ?givens, _) => givens end.

Ltac nsatz_get_reified_goal reified_package :=
  lazymatch reified_package with (_, _, ?goal) => goal end.
Import Coq.setoid_ring.Ring_polynom.

Module Import mynsatz_compute.
  Import Algebra.NsatzTactic.
  Global Ltac mynsatz_compute x := nsatz_compute x.
End mynsatz_compute.
Ltac nsatz_compute x := mynsatz_compute x.

Ltac nsatz_compute_to_goal sugar nparams reified_goal power reified_givens :=
  nsatz_compute (PEc sugar :: PEc nparams :: PEpow reified_goal power :: reified_givens).

Ltac nsatz_compute_get_leading_coefficient :=
  lazymatch goal with
    |- Logic.eq ((?a :: _ :: ?b) :: ?c) _ -> _ => a
  end.

Ltac nsatz_compute_get_certificate :=
  lazymatch goal with
    |- Logic.eq ((?a :: _ :: ?b) :: ?c) _ -> _ => constr:((c,b))
  end.

Ltac nsatz_rewrite_and_revert domain :=
  lazymatch type of domain with
  | @Integral_domain.Integral_domain ?F ?zero _ _ _ _ _ ?eq ?Fops ?FRing ?FCring =>
    lazymatch goal with
    | |- eq _ zero => idtac
    | |- eq _ _ => rewrite <-(cring_sub_diag_iff (cring:=FCring))
    end;
    repeat match goal with
           | [H : eq _ zero |- _ ] => revert H
           | [H : eq _ _ |- _ ] => rewrite <-(cring_sub_diag_iff (cring:=FCring)) in H; revert H
           end
  end.

Ltac nsatz_clear_duplicates_for_bug_4851 domain :=
  lazymatch type of domain with
  | @Integral_domain.Integral_domain _ _ _ _ _ _ _ ?eq _ _ _ =>
    repeat match goal with
           | [ H : eq ?x ?y, H' : eq ?x ?y |- _ ] => clear H'
           end
  end.

Ltac nsatz_nonzero :=
  try solve [apply Integral_domain.integral_domain_one_zero
            |apply Integral_domain.integral_domain_minus_one_zero
            |trivial
            |assumption].

Ltac nsatz_domain_sugar_power domain sugar power :=
  let nparams := constr:(BinInt.Zneg BinPos.xH) in
  lazymatch type of domain with
  | @Integral_domain.Integral_domain ?F ?zero _ _ _ _ _ ?eq ?Fops ?FRing ?FCring =>
    nsatz_clear_duplicates_for_bug_4851 domain;
    nsatz_rewrite_and_revert domain;
    let reified_package := nsatz_reify_equations eq zero in
    let fv := nsatz_get_free_variables reified_package in
    let interp := constr:(@Nsatz.PEevalR _ _ _ _ _ _ _ _ Fops fv) in
    let reified_givens := nsatz_get_reified_givens reified_package in
    let reified_goal := nsatz_get_reified_goal reified_package in
    nsatz_compute_to_goal sugar nparams reified_goal power reified_givens;
    let a := nsatz_compute_get_leading_coefficient in
    let crt := nsatz_compute_get_certificate in
    intros _  ; intros;
    apply (fun Haa refl cond => @Integral_domain.Rintegral_domain_pow _ _ _ _ _ _ _ _ _ _ _ domain (interp a) _ (BinNat.N.to_nat power) Haa (@Nsatz.check_correct _ _ _ _ _ _ _ _ _ _ FCring fv reified_givens (PEmul a (PEpow reified_goal power)) crt refl cond));
    [ nsatz_nonzero; cbv iota beta delta [Nsatz.PEevalR PEeval InitialRing.gen_phiZ InitialRing.gen_phiPOS]
    | solve [vm_cast_no_check (eq_refl true)]
    | solve [repeat (split; [assumption|]); exact I] ]
  end.

Ltac nsatz_guess_domain :=
  match goal with
  | |- ?eq _ _ => constr:(_:Integral_domain.Integral_domain (ring_eq:=eq))
  | |- not (?eq _ _) =>  constr:(_:Integral_domain.Integral_domain (ring_eq:=eq))
  | [H: ?eq _ _ |- _ ] =>  constr:(_:Integral_domain.Integral_domain (ring_eq:=eq))
  | [H: not (?eq _ _) |- _] =>  constr:(_:Integral_domain.Integral_domain (ring_eq:=eq))
  end.

Ltac nsatz_sugar_power sugar power :=
  let domain := nsatz_guess_domain in
  nsatz_domain_sugar_power domain sugar power.

Ltac nsatz_power power :=
  let power_N := (eval compute in (BinNat.N.of_nat power)) in
  nsatz_sugar_power BinInt.Z0 power_N.

Ltac nsatz := nsatz_power 1%nat.
Import Coq.NArith.NArith.

Definition factorize' (n : N) : N -> list N.
admit.
Defined.

Definition factorize (n : N) : list N := factorize' n 2%N.

Definition factorize_or_fail (n:N) : option (list N) :=
  let factors := factorize n in
  if N.eqb (List.fold_right N.mul 1%N factors) n then Some factors else None.

Ltac head expr :=
  match expr with
  | ?f _ => head f
  | _ => expr
  end.

Ltac set_match_refl v' only_when :=
  lazymatch goal with
  | [ |- context G[match ?e with _ => _ end eq_refl] ]
    => only_when e;
       let T := fresh in
       evar (T : Type); evar (v' : T);
       subst T;
       let vv := (eval cbv delta [v'] in v') in
       let G' := context G[vv] in
       let G''' := context G[v'] in
       lazymatch goal with |- ?G'' => unify G' G'' end;
       change G'''
  end.
Ltac set_match_refl_hyp v' only_when :=
  lazymatch goal with
  | [ H : context G[match ?e with _ => _ end eq_refl] |- _ ]
    => only_when e;
       let T := fresh in
       evar (T : Type); evar (v' : T);
       subst T;
       let vv := (eval cbv delta [v'] in v') in
       let G' := context G[vv] in
       let G''' := context G[v'] in
       let G'' := type of H in
       unify G' G'';
       change G''' in H
  end.
Ltac destruct_by_existing_equation match_refl_hyp :=
  let v := (eval cbv delta [match_refl_hyp] in match_refl_hyp) in
  lazymatch v with
  | match ?e with _ => _ end (@eq_refl ?T ?e)
    => let H := fresh in
       let e' := fresh in
       pose e as e';
       change e with e' in (value of match_refl_hyp) at 1;
       first [ pose (@eq_refl T e : e = e') as H;
               change (@eq_refl T e) with H in (value of match_refl_hyp);
               clearbody H e'
             | pose (@eq_refl T e : e' = e) as H;
               change (@eq_refl T e) with H in (value of match_refl_hyp);
               clearbody H e' ];
       destruct e'; subst match_refl_hyp
  end.
Ltac destruct_rewrite_sumbool e :=
  let H := fresh in
  destruct e as [H|H];
  try lazymatch type of H with
      | ?LHS = ?RHS
        => lazymatch RHS with
           | context[LHS] => fail
           | _ => idtac
           end;
           rewrite ?H; rewrite ?H in *;
           repeat match goal with
                  | [ |- context G[LHS] ]
                    => let LHS' := fresh in
                       pose LHS as LHS';
                       let G' := context G[LHS'] in
                       change G';
                       replace LHS' with RHS by (subst LHS'; symmetry; apply H);
                       subst LHS'
                  end
      end.
Ltac break_match_step only_when :=
  match goal with
  | [ |- context[match ?e with _ => _ end] ]
    => only_when e; is_var e; destruct e
  | [ |- context[match ?e with _ => _ end] ]
    => only_when e;
       match type of e with
       | sumbool _ _ => destruct_rewrite_sumbool e
       end
  | [ |- context[if ?e then _ else _] ]
    => only_when e; destruct e eqn:?
  | [ |- context[match ?e with _ => _ end] ]
    => only_when e; destruct e eqn:?
  | _ => let v := fresh in set_match_refl v only_when; destruct_by_existing_equation v
  end.
Ltac break_match_hyps_step only_when :=
  match goal with
  | [ H : context[match ?e with _ => _ end] |- _ ]
    => only_when e; is_var e; destruct e
  | [ H : context[match ?e with _ => _ end] |- _ ]
    => only_when e;
       match type of e with
       | sumbool _ _ => destruct_rewrite_sumbool e
       end
  | [ H : context[if ?e then _ else _] |- _ ]
    => only_when e; destruct e eqn:?
  | [ H : context[match ?e with _ => _ end] |- _ ]
    => only_when e; destruct e eqn:?
  | _ => let v := fresh in set_match_refl_hyp v only_when; destruct_by_existing_equation v
  end.
Ltac break_match := repeat break_match_step ltac:(fun _ => idtac).
Ltac break_match_hyps := repeat break_match_hyps_step ltac:(fun _ => idtac).
Module Export Decidable.

Class Decidable (P : Prop) := dec : {P} + {~P}.
Arguments dec _%type_scope {_}.
Notation DecidableRel R := (forall x y, Decidable (R x y)).

Lemma not_not P {d:Decidable P} : not (not P) <-> P.
admit.
Defined.
Module Export Crypto_DOT_Algebra_DOT_Hierarchy_WRAPPED.
Module Export Hierarchy.
Import Coq.Classes.Morphisms.

Section Algebra.
  Context {T:Type} {eq:T->T->Prop}.
  Local Infix "=" := eq : type_scope.
Local Notation "a <> b" := (not (a = b)) : type_scope.

  Section SingleOperation.
    Context {op:T->T->T}.

    Class is_associative := { associative : forall x y z, op x (op y z) = op (op x y) z }.

    Context {id:T}.

    Class is_left_identity := { left_identity : forall x, op id x = x }.
    Class is_right_identity := { right_identity : forall x, op x id = x }.

    Class monoid :=
      {
        monoid_is_associative : is_associative;
        monoid_is_left_identity : is_left_identity;
        monoid_is_right_identity : is_right_identity;

        monoid_op_Proper: Proper (respectful eq (respectful eq eq)) op;
        monoid_Equivalence : Equivalence eq
      }.
    Global Existing Instance monoid_is_associative.
    Global Existing Instance monoid_is_left_identity.
    Global Existing Instance monoid_is_right_identity.
    Global Existing Instance monoid_Equivalence.
    Global Existing Instance monoid_op_Proper.

    Context {inv:T->T}.
    Class is_left_inverse := { left_inverse : forall x, op (inv x) x = id }.
    Class is_right_inverse := { right_inverse : forall x, op x (inv x) = id }.

    Class group :=
      {
        group_monoid : monoid;
        group_is_left_inverse : is_left_inverse;
        group_is_right_inverse : is_right_inverse;

        group_inv_Proper: Proper (respectful eq eq) inv
      }.
    Global Existing Instance group_monoid.
    Global Existing Instance group_is_left_inverse.
    Global Existing Instance group_is_right_inverse.
    Global Existing Instance group_inv_Proper.

    Class is_commutative := { commutative : forall x y, op x y = op y x }.

    Record commutative_group :=
      {
        commutative_group_group : group;
        commutative_group_is_commutative : is_commutative
      }.
    Existing Class commutative_group.
    Global Existing Instance commutative_group_group.
    Global Existing Instance commutative_group_is_commutative.
  End SingleOperation.

  Section AddMul.
    Context {zero one:T}.
Local Notation "0" := zero.
Local Notation "1" := one.
    Context {opp:T->T}.
    Context {add:T->T->T} {sub:T->T->T} {mul:T->T->T}.
    Local Infix "+" := add.
Local Infix "-" := sub.
Local Infix "*" := mul.

    Class is_left_distributive := { left_distributive : forall a b c, a * (b + c) =  a * b + a * c }.
    Class is_right_distributive := { right_distributive : forall a b c, (b + c) * a = b * a + c * a }.

    Class ring :=
      {
        ring_commutative_group_add : commutative_group (op:=add) (id:=zero) (inv:=opp);
        ring_monoid_mul : monoid (op:=mul) (id:=one);
        ring_is_left_distributive : is_left_distributive;
        ring_is_right_distributive : is_right_distributive;

        ring_sub_definition : forall x y, x - y = x + opp y;

        ring_mul_Proper : Proper (respectful eq (respectful eq eq)) mul;
        ring_sub_Proper : Proper(respectful eq (respectful eq eq)) sub
      }.
    Global Existing Instance ring_commutative_group_add.
    Global Existing Instance ring_monoid_mul.
    Global Existing Instance ring_is_left_distributive.
    Global Existing Instance ring_is_right_distributive.
    Global Existing Instance ring_sub_Proper.

    Class commutative_ring :=
      {
        commutative_ring_ring : ring;
        commutative_ring_is_commutative : is_commutative (op:=mul)
      }.
    Global Existing Instance commutative_ring_ring.
    Global Existing Instance commutative_ring_is_commutative.

    Class is_zero_product_zero_factor :=
      { zero_product_zero_factor : forall x y, x*y = 0 -> x = 0 \/ y = 0 }.

    Class is_zero_neq_one := { zero_neq_one : zero <> one }.

    Class integral_domain :=
      {
        integral_domain_commutative_ring : commutative_ring;
        integral_domain_is_zero_product_zero_factor : is_zero_product_zero_factor;
        integral_domain_is_zero_neq_one : is_zero_neq_one
      }.
    Global Existing Instance integral_domain_commutative_ring.

    Context {inv:T->T} {div:T->T->T}.
    Class is_left_multiplicative_inverse := { left_multiplicative_inverse : forall x, x<>0 -> (inv x) * x = 1 }.

    Class field :=
      {
        field_commutative_ring : commutative_ring;
        field_is_left_multiplicative_inverse : is_left_multiplicative_inverse;
        field_is_zero_neq_one : is_zero_neq_one;

        field_div_definition : forall x y , div x y = x * inv y;

        field_inv_Proper : Proper (respectful eq eq) inv;
        field_div_Proper : Proper (respectful eq (respectful eq eq)) div
      }.
    Global Existing Instance field_commutative_ring.
    Global Existing Instance field_is_left_multiplicative_inverse.
    Global Existing Instance field_inv_Proper.
  End AddMul.

  Definition char_ge (zero:T) (inj:BinPos.positive->T) C := forall p, BinPos.Pos.lt p C -> not (eq (inj p) zero).

End Algebra.

End Hierarchy.
Module Export Algebra.
Module Export Hierarchy.
Include Crypto_DOT_Algebra_DOT_Hierarchy_WRAPPED.Hierarchy.

Lemma not_exfalso (P:Prop) (H:P->False) : not P.
admit.
Defined.
Module Export Ring.

Section Ring.
  Context {T eq zero one opp add sub mul} `{@ring T eq zero one opp add sub mul}.
  Local Infix "=" := eq : type_scope.
Local Notation "a <> b" := (not (a = b)) : type_scope.
  Local Notation "0" := zero.
Local Infix "-" := sub.

  Global Instance is_left_distributive_sub : is_left_distributive (eq:=eq)(add:=sub)(mul:=mul).
admit.
Defined.

  Global Instance is_right_distributive_sub : is_right_distributive (eq:=eq)(add:=sub)(mul:=mul).
admit.
Defined.

  Lemma neq_sub_neq_zero x y (Hxy:x<>y) : x-y <> 0.
  Proof using Type*.
    intro Hsub.
apply Hxy.
rewrite <-(left_identity y), <-Hsub, ring_sub_definition.
    rewrite <-associative, left_inverse, right_identity.
reflexivity.
  Qed.

  Global Instance Ncring_Ring_ops : @Ncring.Ring_ops T zero one add mul sub opp eq := {}.
  Global Instance Ncring_Ring : @Ncring.Ring T zero one add mul sub opp eq Ncring_Ring_ops.
  Proof using Type*.
    split; exact _ || cbv; intros; eauto using left_identity, right_identity, commutative, associative, right_inverse, left_distributive, right_distributive, ring_sub_definition with core typeclass_instances.
    -

      eapply @left_identity; eauto with typeclass_instances.
    -
 eapply @right_identity; eauto with typeclass_instances.
    -
 eapply associative.
    -
 intros; eapply right_distributive.
    -
 intros; eapply left_distributive.
  Qed.
End Ring.

Section TacticSupportCommutative.
  Context {T eq zero one opp add sub mul} `{@commutative_ring T eq zero one opp add sub mul}.

  Global Instance Cring_Cring_commutative_ring :
    @Cring.Cring T zero one add mul sub opp eq Ncring_Ring_ops Ncring_Ring.
admit.
Defined.
End TacticSupportCommutative.

Section of_Z.
  Context {R Req Rzero Rone Ropp Radd Rsub Rmul}
          {Rring : @ring R Req Rzero Rone Ropp Radd Rsub Rmul}.

  Fixpoint of_nat (n:nat) : R :=
    match n with
    | O => Rzero
    | S n' => Radd (of_nat n') Rone
    end.
  Definition of_Z (x:Z) : R :=
    match x with
    | Z0 => Rzero
    | Zpos p => of_nat (Pos.to_nat p)
    | Zneg p => Ropp (of_nat (Pos.to_nat p))
    end.
End of_Z.

Definition char_ge
           {R eq zero one opp add} {sub:R->R->R} {mul:R->R->R}
           C :=
  @Hierarchy.char_ge R eq zero (fun p => (@of_Z R zero one opp add) (BinInt.Z.pos p)) C.
Existing Class char_ge.
Module Export IntegralDomain.
  Section IntegralDomain.
    Context {T eq zero one opp add sub mul} `{@integral_domain T eq zero one opp add sub mul}.

    Global Instance Integral_domain :
      @Integral_domain.Integral_domain T zero one add mul sub opp eq Ring.Ncring_Ring_ops
                                       Ring.Ncring_Ring Ring.Cring_Cring_commutative_ring.
admit.
Defined.
  End IntegralDomain.

  Module Export _LargeCharacteristicReflective.
    Section ReflectiveNsatzSideConditionProver.
Import BinInt.
      Context {R eq zero one opp add sub mul}
              {ring:@Hierarchy.ring R eq zero one opp add sub mul}
              {zpzf:@Hierarchy.is_zero_product_zero_factor R eq zero mul}.

      Inductive coef :=
      | Coef_one
      | Coef_opp (_:coef)
      | Coef_add (_ _:coef)
      | Coef_mul (_ _:coef).
      Fixpoint denote (c:coef) : R :=
        match c with
        | Coef_one => one
        | Coef_opp c => opp (denote c)
        | Coef_add c1 c2 => add (denote c1) (denote c2)
        | Coef_mul c1 c2 => mul (denote c1) (denote c2)
        end.
      Fixpoint CtoZ (c:coef) : Z :=
        match c with
        | Coef_one => Z.one
        | Coef_opp c => Z.opp (CtoZ c)
        | Coef_add c1 c2 => Z.add (CtoZ c1) (CtoZ c2)
        | Coef_mul c1 c2 => Z.mul (CtoZ c1) (CtoZ c2)
        end.

      Section WithChar.
        Context C (char_ge_C:@Ring.char_ge R eq zero one opp add sub mul C) (HC: Pos.lt xH C).

        Definition is_factor_nonzero (n:N) : bool :=
          match n with N0 => false | N.pos p => BinPos.Pos.ltb p C end.

        Definition is_constant_nonzero (z:Z) : bool :=
          match factorize_or_fail (Z.abs_N z) with
          | Some factors => List.forallb is_factor_nonzero factors
          | None => false
          end.

        Fixpoint is_nonzero (c:coef) : bool :=
          match c with
          | Coef_one => true
          | Coef_opp c => is_nonzero c
          | Coef_mul c1 c2 => andb (is_nonzero c1) (is_nonzero c2)
          | _ => is_constant_nonzero (CtoZ c)
          end.
      End WithChar.

      Lemma is_nonzero_correct
            C
            (char_ge_C:@Ring.char_ge R eq zero one opp add sub mul C)
            c (refl:Logic.eq (andb (Pos.ltb xH C) (is_nonzero C c)) true)
        : denote c <> zero.
admit.
Defined.

    End ReflectiveNsatzSideConditionProver.

    Ltac reify one opp add mul x :=
      match x with
      | one => constr:(Coef_one)
      | opp ?a =>
        let a := reify one opp add mul a in
        constr:(Coef_opp a)
      | add ?a ?b =>
        let a := reify one opp add mul a in
        let b := reify one opp add mul b in
        constr:(Coef_add a b)
      | mul ?a ?b =>
        let a := reify one opp add mul a in
        let b := reify one opp add mul b in
        constr:(Coef_mul a b)
      end.
  End _LargeCharacteristicReflective.

  Ltac solve_constant_nonzero :=
    match goal with
    | |- not (?eq ?x _) =>
      let cg := constr:(_:Ring.char_ge (eq:=eq) _) in
      match type of cg with
        @Ring.char_ge ?R eq ?zero ?one ?opp ?add ?sub ?mul ?C =>
        let x' := _LargeCharacteristicReflective.reify one opp add mul x in
        let x' := constr:(@_LargeCharacteristicReflective.denote R one opp add mul x') in
        change (not (eq x' zero));
        apply (_LargeCharacteristicReflective.is_nonzero_correct(eq:=eq)(zero:=zero) C cg);
        (vm_cast_no_check (eq_refl true))
      end
    end.
Import Coq.Classes.RelationClasses.

Section Field.
  Context {T eq zero one opp add mul sub inv div} `{@field T eq zero one opp add sub mul inv div}.
  Local Notation "0" := zero.

  Lemma right_multiplicative_inverse : forall x : T, ~ eq x zero -> eq (mul x (inv x)) one.
  Proof using Type*.
    intros.
rewrite commutative.
auto using left_multiplicative_inverse.
  Qed.

  Context {eq_dec:DecidableRel eq}.

  Global Instance is_mul_nonzero_nonzero : @is_zero_product_zero_factor T eq 0 mul.
admit.
Defined.

  Global Instance integral_domain : @integral_domain T eq zero one opp add sub mul.
  Proof using Type*.
    split; auto using field_commutative_ring, field_is_zero_neq_one, is_mul_nonzero_nonzero.
  Qed.
End Field.

Ltac guess_field :=
  match goal with
  | |- ?eq _ _ =>  constr:(_:Hierarchy.field (eq:=eq))
  | |- not (?eq _ _) =>  constr:(_:Hierarchy.field (eq:=eq))
  | [H: ?eq _ _ |- _ ] =>  constr:(_:Hierarchy.field (eq:=eq))
  | [H: not (?eq _ _) |- _] =>  constr:(_:Hierarchy.field (eq:=eq))
  end.

Ltac goal_to_field_equality fld :=
  let eq := match type of fld with Hierarchy.field(eq:=?eq) => eq end in
  match goal with
  | [ |- eq _ _] => idtac
  | [ |- not (eq ?x ?y) ] => apply not_exfalso; intro; goal_to_field_equality fld
  | _ => exfalso;
         match goal with
         | H: not (eq _ _) |- _ => apply not_exfalso in H; apply H
         | _ => apply (field_is_zero_neq_one(field:=fld))
         end
  end.

Ltac inequalities_to_inverse_equations fld :=
  let eq := match type of fld with Hierarchy.field(eq:=?eq) => eq end in
  let zero := match type of fld with Hierarchy.field(zero:=?zero) => zero end in
  let div := match type of fld with Hierarchy.field(div:=?div) => div end in
  let sub := match type of fld with Hierarchy.field(sub:=?sub) => sub end in
  repeat match goal with
         | [H: not (eq _ _) |- _ ] =>
           lazymatch type of H with
           | not (eq ?d zero) =>
             unique pose proof (right_multiplicative_inverse(H:=fld) _ H)
           | not (eq zero ?d) =>
             unique pose proof (right_multiplicative_inverse(H:=fld) _ (symmetry(R:=fun a b => not (eq a b)) H))
           | not (eq ?x ?y) =>
             unique pose proof (right_multiplicative_inverse(H:=fld) _ (Ring.neq_sub_neq_zero _ _ H))
           end
         end.

Ltac unique_pose_implication pf :=
  let B := match type of pf with ?A -> ?B => B end in
  match goal with
             | [H:B|-_] => fail 1
             | _ => unique pose proof pf
  end.

Ltac inverses_to_conditional_equations fld :=
  let eq := match type of fld with Hierarchy.field(eq:=?eq) => eq end in
  let inv := match type of fld with Hierarchy.field(inv:=?inv) => inv end in
  repeat match goal with
         | |- context[inv ?d] =>
           unique_pose_implication constr:(right_multiplicative_inverse(H:=fld) d)
         | H: context[inv ?d] |- _ =>
           unique_pose_implication constr:(right_multiplicative_inverse(H:=fld) d)
         end.

Ltac clear_hypotheses_with_nonzero_requirements fld :=
  let eq := match type of fld with Hierarchy.field(eq:=?eq) => eq end in
  let zero := match type of fld with Hierarchy.field(zero:=?zero) => zero end in
  repeat match goal with
           [H: not (eq _ zero) -> _ |- _ ] => clear H
         end.

Ltac forward_nonzero fld solver_tac :=
  let eq := match type of fld with Hierarchy.field(eq:=?eq) => eq end in
  let zero := match type of fld with Hierarchy.field(zero:=?zero) => zero end in
  repeat match goal with
         | [H: not (eq ?x zero) -> _ |- _ ]
           => let H' := fresh in
              assert (H' : not (eq x zero)) by (clear_hypotheses_with_nonzero_requirements; solver_tac); specialize (H H')
         | [H: not (eq ?x zero) -> _ |- _ ]
           => let H' := fresh in
              assert (H' : not (eq x zero)) by (clear H; solver_tac); specialize (H H')
         end.

Ltac divisions_to_inverses fld :=
  rewrite ?(field_div_definition(field:=fld)) in *.

Ltac fsatz_solve_on fld :=
  goal_to_field_equality fld;
  forward_nonzero fld ltac:(fsatz_solve_on fld);
  nsatz;
  solve_debugfail ltac:(IntegralDomain.solve_constant_nonzero).

Ltac fsatz_prepare_hyps_on fld :=
  divisions_to_inverses fld;
  inequalities_to_inverse_equations fld;
  inverses_to_conditional_equations fld;
  forward_nonzero fld ltac:(fsatz_solve_on fld).

Ltac fsatz :=
  let fld := guess_field in
  fsatz_prepare_hyps_on fld;
  fsatz_solve_on fld.

Module Export W.
  Section WeierstrassCurves.

    Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv} {field:@Algebra.Hierarchy.field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv} {Feq_dec:Decidable.DecidableRel Feq} {char_ge_3:@Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul (BinNat.N.succ_pos (BinNat.N.two))}.
    Local Infix "=" := Feq : type_scope.
    Local Notation "x =? y" := (Decidable.dec (Feq x y)) (at level 70, no associativity) : type_scope.
    Local Infix "+" := Fadd.
Local Infix "*" := Fmul.
    Local Infix "-" := Fsub.
Local Infix "/" := Fdiv.
    Local Notation "- x" := (Fopp x).
    Local Notation "x ^ 2" := (x*x) (at level 30).
Local Notation "x ^ 3" := (x*x^2) (at level 30).
    Local Notation "'∞'" := unit : type_scope.
    Local Notation "'∞'" := (inr tt) : core_scope.

    Local Notation "( x , y )" := (inl (pair x y)).
    Local Open Scope core_scope.

    Context {a b: F}.

    Definition point := { P | match P with
                              | (x, y) => y^2 = x^3 + a*x + b
                              | ∞ => True
                              end }.
    Definition coordinates (P:point) : F*F + ∞ := let (xyi,_) := P in xyi.

    Definition eq (P1 P2:point) :=
      match coordinates P1, coordinates P2 with
      | (x1, y1), (x2, y2) => x1 = x2 /\ y1 = y2
      | ∞, ∞ => True
      | _, _ => False
      end.
 Local Notation "1" := Fone.
    Local Notation "2" := (1+1).
Local Notation "3" := (1+2).

    Program Definition add (P1 P2:point) : point :=
      match coordinates P1, coordinates P2 return F*F+∞ with
      | (x1, y1), (x2, y2) =>
        if x1 =? x2
        then
          if y2 =? -y1
          then ∞
          else let k := (3*x1^2+a)/(2*y1) in
               let x3 := k^2-x1-x2 in
               let y3 := k*(x1-x3)-y1 in
               (x3, y3)
        else let k := (y2-y1)/(x2-x1) in
             let x3 := k^2-x1-x2 in
             let y3 := k*(x1-x3)-y1 in
             (x3, y3)
      | ∞, ∞ => ∞
      | ∞, _ => coordinates P2
      | _, ∞ => coordinates P1
      end.
Admit Obligations.
  End WeierstrassCurves.
End W.

Ltac do_one_match_then matcher do_tac tac :=
  idtac;
  match goal with
  | [ H : ?T |- _ ]
    => matcher T; do_tac H;
       try match type of H with
           | T => clear H
           end;
       tac
  end.

Ltac do_all_matches_then matcher do_tac tac :=
  repeat do_one_match_then matcher do_tac tac.

Ltac destruct_all_matches_then matcher tac :=
  do_all_matches_then matcher ltac:(fun H => destruct H) tac.
Ltac destruct_all_matches' matcher := destruct_all_matches_then matcher idtac.

Ltac destruct_head_matcher T HT :=
  match head HT with
  | T => idtac
  end.
Ltac destruct_head' T := destruct_all_matches' ltac:(destruct_head_matcher T).

Ltac transparent_specialize_one H arg :=
  first [ let test := eval unfold H in H in idtac;
          let H' := fresh in rename H into H'; pose (H' arg) as H; subst H'
         | specialize (H arg) ].

Ltac guarded_specialize_by' tac guard_tac :=
  idtac;
  match goal with
  | [ H : ?A -> ?B |- _ ]
    => guard_tac H;
       let H' := fresh in
       assert (H' : A) by tac;
       transparent_specialize_one H H';
       try clear H'
  end.
Ltac specialize_by' tac := guarded_specialize_by' tac ltac:(fun _ => idtac).

Ltac specialize_by tac := repeat specialize_by' tac.
  Section Projective.
    Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv} {a b:F}
            {field:@Algebra.Hierarchy.field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {char_ge_3:@Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul (BinNat.N.succ_pos (BinNat.N.two))}
            {Feq_dec:DecidableRel Feq}.
    Local Infix "=" := Feq : type_scope.
Local Notation "a <> b" := (not (a = b)) : type_scope.
    Local Notation "0" := Fzero.
    Local Infix "+" := Fadd.
    Local Infix "*" := Fmul.
Local Infix "/" := Fdiv.
    Local Notation "x ^ 2" := (x*x).
Local Notation "x ^ 3" := (x*x^2).
    Local Notation Wpoint := (@W.point F Feq Fadd Fmul a b).

    Ltac t :=
      repeat match goal with
             | _ => solve [ discriminate | contradiction | trivial ]
             | _ => progress cbv zeta
             | _ => progress intros
             | _ => progress destruct_head' @W.point
             | _ => progress destruct_head' sum
             | _ => progress destruct_head' prod
             | _ => progress destruct_head' unit
             | _ => progress destruct_head' and
             | _ => progress specialize_by assumption
             | _ => progress cbv [W.eq W.add W.coordinates proj1_sig] in *
             | _ => progress break_match_hyps
             | _ => progress break_match
             | |- _ /\ _ => split | |- _ <-> _ => split
             | [H:~ _ <> _ |- _ ] => rewrite (not_not (_ = _)) in H
             | [H: not ?P, G: ?P -> _ |- _ ] => clear G
             | [H: ?P, G: not ?P -> _ |- _ ] => clear G
             | [H: ?x = ?x |- _ ] => clear H
             | [H: True |- _ ] => clear H
             end.

    Definition point : Type := { P : F*F*F | let '(X,Y,Z) := P in Y^2*Z = X^3 + a*X*Z^2 + b*Z^3 /\ (Z = 0 -> Y <> 0) }.

    Program Definition to_affine (P:point) : Wpoint :=
      match proj1_sig P return F*F+_ with
      | (X, Y, Z) =>
        if dec (Z = 0) then inr tt
        else inl (X/Z, Y/Z)
      end.

    Program Definition opp (P:point) : point :=
      match proj1_sig P return F*F*F with
      | (X, Y, Z) => (X, Fopp Y, Z)
      end.
Admit Obligations.

    Context (three_b:F) (three_b_correct: three_b = b+b+b).

    Let not_exceptional_y (P Q:point) :=
      match W.coordinates (W.add (to_affine P) (to_affine (opp Q))) return Prop with
      | inr _ => True
      | inl (_, y) => y <> 0
      end.

    Global Instance DecidableRel_not_exceptional_y : DecidableRel not_exceptional_y.
admit.
Defined.

    Lemma exceptional_P_neq_Q P Q (H:~not_exceptional_y P Q) :
      ~ W.eq (to_affine P) (to_affine Q).
    Proof using three_b_correct three_b.
      destruct P as [p ?]; destruct p as [p Z1]; destruct p as [X1 Y1].
      destruct Q as [q ?]; destruct q as [q Z2]; destruct q as [X2 Y2].
      cbv [not_exceptional_y opp to_affine] in *; clear not_exceptional_y.
      t; try exact id.
      all: repeat match goal with
                    [H:~ _ <> _ |- _ ] => rewrite (not_not (_ = _)) in H
                  end.
      all: intro HX; destruct HX; fsatz.
