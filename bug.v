(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "-deprecated-native-compiler-option" "-w" "-deprecated-appcontext -notation-overridden" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/fiat_parsers/src" "Fiat" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/fiat_parsers/Bedrock" "Bedrock" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-I" "/github/workspace/builds/coq/coq-failing/_build_ci/fiat_parsers/src/Common/Tactics" "-top" "bug_01" "-require-import" "Coq.Compat.AdmitAxiom" "-native-compiler" "no") -*- *)
(* File reduced by coq-bug-finder from original input, then from 916 lines to 349 lines, then from 470 lines to 917 lines, then from 920 lines to 364 lines, then from 485 lines to 869 lines, then from 872 lines to 377 lines, then from 497 lines to 853 lines, then from 857 lines to 401 lines, then from 521 lines to 763 lines, then from 766 lines to 432 lines, then from 551 lines to 950 lines, then from 954 lines to 700 lines, then from 817 lines to 1940 lines, then from 1944 lines to 711 lines, then from 825 lines to 942 lines, then from 946 lines to 920 lines, then from 923 lines to 795 lines, then from 909 lines to 1181 lines, then from 1185 lines to 975 lines, then from 1087 lines to 1600 lines, then from 1604 lines to 1223 lines, then from 1334 lines to 1410 lines, then from 1414 lines to 1267 lines, then from 1378 lines to 2006 lines, then from 2010 lines to 2035 lines, then from 2038 lines to 1410 lines, then from 1514 lines to 2063 lines, then from 2066 lines to 1589 lines, then from 1692 lines to 1910 lines, then from 1913 lines to 1643 lines, then from 1746 lines to 1633 lines, then from 1736 lines to 1795 lines, then from 1799 lines to 1651 lines, then from 1749 lines to 2050 lines, then from 2053 lines to 1819 lines, then from 1913 lines to 2158 lines, then from 2162 lines to 1922 lines, then from 1964 lines to 1867 lines, then from 1955 lines to 2113 lines, then from 2117 lines to 1920 lines, then from 2006 lines to 2145 lines, then from 2149 lines to 1961 lines, then from 2047 lines to 1952 lines, then from 2038 lines to 2139 lines, then from 2143 lines to 2019 lines, then from 2104 lines to 2240 lines, then from 2244 lines to 2084 lines, then from 2168 lines to 2344 lines, then from 2348 lines to 2344 lines *)
(* coqc version 8.15+alpha compiled with OCaml 4.05.0
   coqtop version runner-z3wu8uu--project-6138686-concurrent-0:/builds/coq/coq/_build/default,(HEAD detached at 2849986) (2849986551f681bd3a083e4f8a300d9b54edd1a0) *)
Declare ML Module "ltac_plugin".
Module Export AdmitTactic.
Module Import LocalFalse.
Inductive False := .
End LocalFalse.
Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.
End AdmitTactic.
Require Coq.FSets.FMapPositive.
Require Coq.MSets.MSetPositive.
Require Coq.FSets.FMapInterface.
Require Coq.Setoids.Setoid.
Require Coq.Program.Program.
Require Coq.Program.Wf.
Require Coq.Arith.Wf_nat.
Require Coq.Classes.Morphisms.
Require Coq.Init.Wf.
Require Coq.Lists.SetoidList.
Require Coq.Compat.Coq814.
Require Coq.Strings.Ascii.
Require Coq.Strings.String.
Require Coq.ZArith.BinIntDef.
Require Coq.PArith.BinPosDef.
Require Coq.NArith.BinNatDef.
Require Coq.Reals.Rdefinitions.
Require Coq.Numbers.Cyclic.Int63.Int63.
Require Coq.Numbers.Cyclic.Int31.Int31.
Require Coq.micromega.Lia.
Require Coq.Lists.List.
Require Coq.Vectors.Vector.
Require Coq.funind.FunInd.
Require Fiat.Common.Coq__8_4__8_5__Compat.
Require Fiat.Common.Wf.
Require Coq.FSets.FMapFacts.
Require Coq.Structures.OrderedTypeEx.
Require Coq.Numbers.Natural.Peano.NPeano.
Require Coq.ZArith.ZArith.
Require Coq.Classes.RelationClasses.
Require Fiat.Common.Tactics.SplitInContext.
Require Fiat.Common.Tactics.Combinators.
Require Fiat.Common.Tactics.FreeIn.
Require Fiat.Common.Tactics.SetoidSubst.
Require Fiat.Common.Tactics.Head.
Require Fiat.Common.Tactics.BreakMatch.
Require Fiat.Common.Tactics.FoldIsTrue.
Require Fiat.Common.Tactics.SpecializeBy.
Require Fiat.Common.Tactics.DestructHyps.
Require Fiat.Common.Tactics.DestructSig.
Require Fiat.Common.Tactics.DestructHead.
Require Fiat.Common.
Require Coq.Bool.Bool.
Require Coq.Structures.OrderedType.
Require Fiat.Common.SetEq.
Require Coq.Sorting.Permutation.
Require Coq.Arith.Arith.
Require Fiat.Common.List.FlattenList.
Require Fiat.Common.SetEqProperties.
Require Coq.ZArith.BinInt.
Require Coq.NArith.BinNat.
Require Fiat.Common.BoolFacts.
Require Coq.Logic.Eqdep_dec.
Require Fiat.Common.Equality.
Require Fiat.Common.List.Operations.
Require Coq.Program.Basics.
Require Fiat.Common.LogicFacts.
Require Fiat.Common.List.ListFacts.
Require Coq.Sets.Ensembles.
Require Fiat.Common.List.PermutationFacts.
Require Fiat.Common.Ensembles.EnsembleListEquivalence.
Require Fiat.Common.List.ListMorphisms.
Require Fiat.Common.SetoidClassInstances.
Require Fiat.Common.FMapExtensions.
Require Fiat.Common.LogicMorphisms.
Require Fiat.Common.FMapExtensions.LiftRelationInstances.
Require Fiat.Common.FMapExtensions.Wf.
Require Fiat.Common.StringOperations.
Require Fiat.Common.StringFacts.
Require Fiat.Common.Gensym.
Require Coq.MSets.MSetInterface.
Require Coq.MSets.MSetProperties.
Require Coq.MSets.MSetFacts.
Require Coq.MSets.MSetDecide.
Require Fiat.Common.Instances.
Require Fiat.Common.MSetExtensions.
Require Fiat.Common.Notations.
Require Coq.Relations.Relation_Definitions.
Module Export Fiat_DOT_Parsers_DOT_StringLike_DOT_Core_WRAPPED.
Module Export Core.
Import Coq.Relations.Relation_Definitions.
Import Coq.Classes.Morphisms.
Export Fiat.Common.Coq__8_4__8_5__Compat.

Local Coercion is_true : bool >-> Sortclass.

Global Set Keyed Unification.
 
Global Set Asymmetric Patterns.

Set Implicit Arguments.
Generalizable All Variables.

 

Reserved Notation "[ x ]".

Module Export StringLike.
  Class StringLikeMin {Char : Type} :=
    {
      String :> Type;
      char_at_matches : nat -> String -> (Char -> bool) -> bool;
      unsafe_get : nat -> String -> Char;
      length : String -> nat
    }.

  Class StringLike {Char : Type} {HSLM : @StringLikeMin Char} :=
    {
      is_char : String -> Char -> bool;
      take : nat -> String -> String;
      drop : nat -> String -> String;
      get : nat -> String -> option Char;
      bool_eq : String -> String -> bool;
      beq : relation String := fun x y => bool_eq x y
    }.

  Class StringIso {Char} {HSLM : @StringLikeMin Char} :=
    {
      of_string : list Char -> String
    }.

  Arguments StringLikeMin : clear implicits.
  Arguments StringLike Char {HSLM}.
  Arguments StringIso Char {HSLM}.
  Bind Scope string_like_scope with String.
  Delimit Scope string_like_scope with string_like.
  Infix "=s" := (@beq _ _ _) (at level 70, no associativity) : type_scope.
  Infix "=s" := (@bool_eq _ _ _) (at level 70, no associativity) : string_like_scope.
  Notation "s ~= [ ch ]" := (is_char s ch) (at level 70, no associativity) : string_like_scope.
  Local Open Scope string_like_scope.
  Local Open Scope type_scope.

  Definition fold' {Char} {HSLM} {HSL : @StringLike Char HSLM} {A}
             (f : Char -> A -> A)
             (init : A)
             (str : String) (len : nat)
  : A
    := nat_rect
         (fun _ => A)
         init
         (fun len' acc
          => match get (length str - S len') str with
               | Some ch => f ch acc
               | None => init
             end)
         len.

  Definition fold {Char} {HSLM} {HSL : @StringLike Char HSLM} {A}
             (f : Char -> A -> A)
             (init : A)
             (str : String)
  : A
    := fold' f init str (length str).

  Definition fold_lookahead' {Char} {HSLM} {HSL : @StringLike Char HSLM} {A}
             (f : Char -> option Char -> A -> A)
             (init : A)
             (str : String) (len : nat)
  : A
    := nat_rect
         (fun _ => A)
         init
         (fun len' acc
          => match get (length str - S len') str with
               | Some ch => f ch (get (length str - len') str) acc
               | None => init
             end)
         len.

  Definition fold_lookahead {Char} {HSLM} {HSL : @StringLike Char HSLM} {A}
             (f : Char -> option Char -> A -> A)
             (init : A)
             (str : String)
  : A
    := fold_lookahead' f init str (length str).

  Notation to_string str := (fold (@List.cons _) (@List.nil _) str).

  Definition str_le `{@StringLike Char HSLM} (s1 s2 : String)
    := length s1 < length s2 \/ s1 =s s2.
  Infix "≤s" := str_le (at level 70, right associativity).

  Notation substring n m str := (take m (drop n str)).

  Class StringLikeProperties (Char : Type) `{StringLike Char} :=
    {
      singleton_unique : forall s ch ch', s ~= [ ch ] -> s ~= [ ch' ] -> ch = ch';
      singleton_exists : forall s, length s = 1 -> exists ch, s ~= [ ch ];
      char_at_matches_correct : forall s n P ch, get n s = Some ch -> (char_at_matches n s P = P ch);
      get_0 : forall s ch, take 1 s ~= [ ch ] <-> get 0 s = Some ch;
      get_S : forall n s, get (S n) s = get n (drop 1 s);
      unsafe_get_correct : forall n s ch, get n s = Some ch -> unsafe_get n s = ch;
      length_singleton : forall s ch, s ~= [ ch ] -> length s = 1;
      bool_eq_char : forall s s' ch, s ~= [ ch ] -> s' ~= [ ch ] -> s =s s';
      is_char_Proper :> Proper (beq ==> eq ==> eq) is_char;
      length_Proper :> Proper (beq ==> eq) length;
      take_Proper :> Proper (eq ==> beq ==> beq) take;
      drop_Proper :> Proper (eq ==> beq ==> beq) drop;
      bool_eq_Equivalence :> Equivalence beq;
      bool_eq_empty : forall str str', length str = 0 -> length str' = 0 -> str =s str';
      take_short_length : forall str n, n <= length str -> length (take n str) = n;
      take_long : forall str n, length str <= n -> take n str =s str;
      take_take : forall str n m, take n (take m str) =s take (min n m) str;
      drop_length : forall str n, length (drop n str) = length str - n;
      drop_0 : forall str, drop 0 str =s str;
      drop_drop : forall str n m, drop n (drop m str) =s drop (n + m) str;
      drop_take : forall str n m, drop n (take m str) =s take (m - n) (drop n str);
      take_drop : forall str n m, take n (drop m str) =s drop m (take (n + m) str);
      bool_eq_from_get : forall str str', (forall n, get n str = get n str') -> str =s str';
      strings_nontrivial : forall n, exists str, length str = n
    }.

  Class StringIsoProperties {Char} {HSLM} {HSL : @StringLike Char HSLM} {HSI : @StringIso Char HSLM} :=
    {
      get_of_string : forall n str, get n (of_string str) = List.nth_error str n
    }.

  Class StringEqProperties {Char} {HSLM} {HSL : @StringLike Char HSLM} :=
    {
      bool_eq_bl : forall s s', s =s s' -> s = s';
      bool_eq_lb : forall s s', s = s' -> s =s s'
    }.

  Global Existing Instance Equivalence_Reflexive.
  Global Existing Instance Equivalence_Symmetric.
  Global Existing Instance Equivalence_Transitive.

  Arguments StringLikeProperties Char {_ _}.
  Arguments StringIsoProperties Char {_ _ _}.
  Arguments StringEqProperties Char {_ _}.
End StringLike.

 
Global Instance: forall T H,
    @Params (forall Char
                    (HSLM : StringLikeMin Char) (HSL : StringLike Char),
                String -> T Char)
            H
            3 := {}.

End Core.

End Fiat_DOT_Parsers_DOT_StringLike_DOT_Core_WRAPPED.
Module Export Fiat_DOT_Parsers_DOT_StringLike_DOT_Core.
Module Export Fiat.
Module Export Parsers.
Module Export StringLike.
Module Export Core.
Include Fiat_DOT_Parsers_DOT_StringLike_DOT_Core_WRAPPED.Core.
End Core.

End StringLike.

End Parsers.

End Fiat.

End Fiat_DOT_Parsers_DOT_StringLike_DOT_Core.

Module Export Fiat_DOT_Parsers_DOT_ContextFreeGrammar_DOT_Core_WRAPPED.
Module Export Core.
Import Coq.Strings.String.
Import Coq.Lists.List.
Export Fiat.Parsers.StringLike.Core.

Local Open Scope string_like_scope.

Section cfg.
  Context {Char : Type}.

  Section definitions.

    Inductive item :=
    | Terminal (_ : Char -> bool)
    | NonTerminal (_ : string).

    Definition production := list item.
    Definition productions := list production.

    Record grammar :=
      {
        Start_symbol :> string;
        Lookup :> string -> productions;
        Start_productions :> productions := Lookup Start_symbol;
        Valid_nonterminals : list string;
        Valid_productions : list productions := map Lookup Valid_nonterminals
      }.
  End definitions.

  Section parse.
    Context {HSLM} {HSL : @StringLike Char HSLM}.
    Variable G : grammar.

    Inductive parse_of (str : String) : productions -> Type :=
    | ParseHead : forall pat pats, parse_of_production str pat
                                   -> parse_of str (pat::pats)
    | ParseTail : forall pat pats, parse_of str pats
                                   -> parse_of str (pat::pats)
    with parse_of_production (str : String) : production -> Type :=
    | ParseProductionNil : length str = 0 -> parse_of_production str nil
    | ParseProductionCons : forall n pat pats,
                              parse_of_item (take n str) pat
                              -> parse_of_production (drop n str) pats
                              -> parse_of_production str (pat::pats)
    with parse_of_item (str : String) : item -> Type :=
    | ParseTerminal : forall ch P, is_true (P ch) -> is_true (str ~= [ ch ]) -> parse_of_item str (Terminal P)
    | ParseNonTerminal : forall nt,
                           List.In nt (Valid_nonterminals G)
                           -> parse_of str (Lookup G nt)
                           -> parse_of_item str (NonTerminal nt).
  End parse.
End cfg.

Arguments item _ : clear implicits.
Arguments production _ : clear implicits.
Arguments productions _ : clear implicits.
Arguments grammar _ : clear implicits.

End Core.
Module Export Fiat.
Module Export Parsers.
Module Export ContextFreeGrammar.
Module Export Core.
Include Fiat_DOT_Parsers_DOT_ContextFreeGrammar_DOT_Core_WRAPPED.Core.
End Core.

Module Export BaseTypes.
Import Coq.Lists.List.
Import Coq.Arith.Wf_nat.

Local Coercion is_true : bool >-> Sortclass.

Section recursive_descent_parser.
  Context {Char} {HSLM : StringLikeMin Char} {G : grammar Char}.

  Class parser_computational_predataT :=
    { nonterminals_listT : Type;
      nonterminal_carrierT : Type;
      of_nonterminal : String.string -> nonterminal_carrierT;
      to_nonterminal : nonterminal_carrierT -> String.string;
      production_carrierT : Type;
      to_production : production_carrierT -> production Char;
      nonterminal_to_production : nonterminal_carrierT -> list production_carrierT;
      production_tl : production_carrierT -> production_carrierT;
      production_carrier_valid : production_carrierT -> bool;
      initial_nonterminals_data : nonterminals_listT;
      nonterminals_length : nonterminals_listT -> nat;
      is_valid_nonterminal : nonterminals_listT -> nonterminal_carrierT -> bool;
      remove_nonterminal : nonterminals_listT -> nonterminal_carrierT -> nonterminals_listT }.

  Class parser_removal_dataT' {predata : parser_computational_predataT} :=
    { nonterminals_listT_R : nonterminals_listT -> nonterminals_listT -> Prop
      := ltof _ nonterminals_length;
      nonterminals_length_zero : forall ls,
                                   nonterminals_length ls = 0
                                   -> forall nt, is_valid_nonterminal ls nt = false;
      remove_nonterminal_dec : forall ls nonterminal,
                                 is_valid_nonterminal ls nonterminal
                                 -> nonterminals_listT_R (remove_nonterminal ls nonterminal) ls;
      remove_nonterminal_noninc : forall ls nonterminal,
                                    ~nonterminals_listT_R ls (remove_nonterminal ls nonterminal);
      initial_nonterminals_correct : forall nonterminal,
                                       is_valid_nonterminal initial_nonterminals_data (of_nonterminal nonterminal) <-> List.In nonterminal (Valid_nonterminals G);
      initial_nonterminals_correct' : forall nonterminal,
                                       is_valid_nonterminal initial_nonterminals_data nonterminal <-> List.In (to_nonterminal nonterminal) (Valid_nonterminals G);
      to_of_nonterminal : forall nonterminal,
                            List.In nonterminal (Valid_nonterminals G)
                            -> to_nonterminal (of_nonterminal nonterminal) = nonterminal;
      of_to_nonterminal : forall nonterminal,
                            is_valid_nonterminal initial_nonterminals_data nonterminal
                            -> of_nonterminal (to_nonterminal nonterminal) = nonterminal;
      production_tl_correct : forall p,
                                to_production (production_tl p) = tl (to_production p);
      nonterminal_to_production_correct
      : forall nt,
          List.In nt (Valid_nonterminals G)
          -> List.map to_production (nonterminal_to_production (of_nonterminal nt))
             = Lookup G nt;
      production_tl_valid
      : forall p,
          production_carrier_valid p -> production_carrier_valid (production_tl p);
      nonterminal_to_production_valid
      : forall nt,
          is_valid_nonterminal initial_nonterminals_data nt
          -> List.Forall production_carrier_valid (nonterminal_to_production nt);
      ntl_wf : well_founded nonterminals_listT_R
      := well_founded_ltof _ _;
      remove_nonterminal_1
      : forall ls ps ps',
          is_valid_nonterminal (remove_nonterminal ls ps) ps'
          -> is_valid_nonterminal ls ps';
      remove_nonterminal_2
      : forall ls ps ps',
          is_valid_nonterminal (remove_nonterminal ls ps) ps' = false
          <-> is_valid_nonterminal ls ps' = false \/ ps = ps' }.
End recursive_descent_parser.

End BaseTypes.

Section syntax.
  Context {Char : Type}.

  Inductive RCharExpr :=
  | rbeq (ch : Char)
  | ror (_ _ : RCharExpr)
  | rand (_ _ : RCharExpr)
  | rneg (_ : RCharExpr)
  | rcode_le_than (code : BinNums.N)
  | rcode_ge_than (code : BinNums.N).

  Inductive ritem :=
  | RTerminal (_ : RCharExpr)
  | RNonTerminal (_ : String.string).

  Definition rproduction := list ritem.
  Definition rproductions := list rproduction.
End syntax.
Global Arguments rproductions : clear implicits.

Section semantics.
  Context {Char : Type}.

  Class interp_RCharExpr_data :=
    { irbeq : Char -> Char -> bool;
      irN_of : Char -> BinNums.N }.
End semantics.

Global Arguments interp_RCharExpr_data : clear implicits.

Module Export PreNotations.
Import Coq.Strings.String.
Import Coq.Lists.List.
Import Fiat.Common.List.Operations.
Import Fiat.Common.Equality.
Import Fiat.Common.Gensym.

Class NoDupR {T} beq (ls : list T) := nodupr : uniquize beq ls = ls.

Definition list_to_productions {T} (default : T) (ls : list (string * T)) : string -> T
  := fun nt
     => option_rect
          (fun _ => T)
          snd
          default
          (find (fun k => string_beq nt (fst k)) ls).

Record pregrammar Char :=
  {
    pregrammar_rproductions : list (string * rproductions Char);
    pregrammar_idata : interp_RCharExpr_data Char;
    pregrammar_rnonterminals : list string
    := map fst pregrammar_rproductions;
    rnonterminals_unique
    : NoDupR string_beq pregrammar_rnonterminals;
    RLookup_idx : nat -> rproductions Char
    := fun n => nth n (map snd pregrammar_rproductions) nil
  }.

Record pregrammar' (Char : Type) :=
  {
    pregrammar_productions :> list (string * productions Char);
    pregrammar_nonterminals : list string
    := map fst pregrammar_productions;
    invalid_nonterminal : string
    := gensym pregrammar_nonterminals;
    Lookup_idx : nat -> productions Char
    := fun n => nth n (map snd pregrammar_productions) nil;
    Lookup_string : string -> productions Char
    := list_to_productions nil pregrammar_productions;
    nonterminals_unique
    : NoDupR string_beq pregrammar_nonterminals
  }.

Coercion grammar_of_pregrammar {Char} (g : pregrammar' Char) : grammar Char
  := {| Start_symbol := hd ""%string (pregrammar_nonterminals g);
        Lookup := Lookup_string g;
        Valid_nonterminals := (pregrammar_nonterminals g) |}.

End PreNotations.

Import Fiat.Common.List.Operations.
Import Fiat.Common.Equality.
Import Fiat.Parsers.ContextFreeGrammar.Core.
Import Fiat.Common.Gensym.

Definition default_nonterminal_carrierT : Type := nat.

Definition default_production_carrierT : Type
  := default_nonterminal_carrierT * (nat * nat).

Section grammar.
  Context {Char} {G : pregrammar' Char}.

  Local Notation valid_nonterminals := (List.map fst (pregrammar_productions G)).

  Definition some_invalid_nonterminal
    := gensym valid_nonterminals.

  Definition default_to_nonterminal
  : default_nonterminal_carrierT -> String.string
    := fun nt => List.nth nt valid_nonterminals some_invalid_nonterminal.

  Definition default_of_nonterminal
  : String.string -> default_nonterminal_carrierT
    := fun nt => List.first_index_default
                   (string_beq nt)
                   (List.length valid_nonterminals)
                   valid_nonterminals.

  Lemma list_to_productions_to_nonterminal nt
  : Lookup_string G (default_to_nonterminal nt)
    = Lookup_idx G nt.
admit.
Defined.

  Section index.
    Context (idx : default_production_carrierT).

    Let nt_idx := fst idx.
    Let nts := (Lookup_idx G nt_idx).
    Let ps_idx := List.length nts - S (fst (snd idx)).
    Let drop_count := snd (snd idx).
    Let ps := (List.nth ps_idx nts nil).

    Definition default_to_production : production Char
    := List.drop drop_count ps.

    Definition default_production_tl : default_production_carrierT
      := (nt_idx,
          (fst (snd idx),
           if Compare_dec.leb (S drop_count) (List.length ps)
           then S drop_count
           else drop_count)).

    Definition default_production_carrier_valid : bool
      := ((Compare_dec.leb (S nt_idx) (List.length (pregrammar_productions G)))
            && ((Compare_dec.leb (S (fst (snd idx))) (List.length nts))
                  && (Compare_dec.leb drop_count (List.length ps))))%bool.
  End index.
End grammar.

Module Export Definitions.
Import Coq.PArith.BinPos.
Import Coq.Classes.Morphisms.
Import Fiat.Common.Notations.

Local Coercion is_true : bool >-> Sortclass.
Delimit Scope grammar_fixedpoint_scope with fixedpoint.
Local Open Scope grammar_fixedpoint_scope.

Inductive lattice_for T := top | constant (_ : T) | bottom.
Scheme Equality for lattice_for.

Arguments bottom {_}.
Arguments top {_}.
Notation "'⊥'" := bottom : grammar_fixedpoint_scope.
Notation "'⊤'" := top : grammar_fixedpoint_scope.

Global Instance lattice_for_Equivalence {T} {beq : T -> T -> bool}
       {H : Equivalence beq}
  : Equivalence (lattice_for_beq beq).
admit.
Defined.

Definition lattice_for_lt {T} (lt : T -> T -> bool) (x y : lattice_for T)
  := match x, y with
     | ⊤, ⊤ => false
     | constant x', constant y' => lt x' y'
     | ⊥, ⊥ => false
     | _, ⊤ => true
     | ⊤, _ => false
     | _, constant _ => true
     | constant _, _ => false
     end.

Global Instance lattice_for_lt_Proper {T} {beq lt : T -> T -> bool}
       {H : Proper (beq ==> beq ==> eq) lt}
  : Proper (lattice_for_beq beq ==> lattice_for_beq beq ==> eq) (lattice_for_lt lt).
admit.
Defined.

Definition lattice_for_lub {T} (lub : T -> T -> lattice_for T) (x y : lattice_for T)
  := match x, y with
     | ⊤, ⊤ => ⊤
     | constant x', constant y' => lub x' y'
     | ⊥, ⊥ => ⊥
     | ⊤, _
     | _, ⊤
       => ⊤
     | ⊥, v
     | v, ⊥
       => v
     end.

Section lub_correct.
  Context {T} (beq : T -> T -> bool) (lt : T -> T -> bool) (lub : T -> T -> lattice_for T).

  Local Notation "x <= y" := (orb (lattice_for_beq beq x y) (lattice_for_lt lt x y)).

  Context (lub_correct_l : forall x y, constant x <= lub x y)
          (lub_correct_r : forall x y, constant y <= lub x y)
          (beq_Reflexive : Reflexive beq).

  Lemma lattice_for_lub_correct_l x y
    : x <= lattice_for_lub lub x y.
  Proof.
    clear lub_correct_r.
    destruct x as [|x|], y as [|y|]; try reflexivity.
    {
 exact (lub_correct_l x y).
}
    {
 simpl.
      rewrite (reflexivity x : is_true (beq x x)).
      reflexivity.
}
  Qed.

  Lemma lattice_for_lub_correct_r x y
    : y <= lattice_for_lub lub x y.
  Proof.
    clear lub_correct_l.
    destruct x as [|x|], y as [|y|]; try reflexivity.
    {
 exact (lub_correct_r x y).
}
    {
 simpl.
      rewrite (reflexivity y : is_true (beq y y)).
      reflexivity.
}
  Qed.

  Global Instance lattice_for_lub_Proper
         {lub_Proper : Proper (beq ==> beq ==> lattice_for_beq beq) lub}
    : Proper (lattice_for_beq beq ==> lattice_for_beq beq ==> lattice_for_beq beq) (lattice_for_lub lub).
admit.
Defined.
End lub_correct.

Definition lattice_for_gt_well_founded {T} {lt : T -> T -> bool}
           (gt_wf : well_founded (Basics.flip lt))
  : well_founded (Basics.flip (lattice_for_lt lt)).
admit.
Defined.

Global Instance lattice_for_lt_Transitive {T} {lt : T -> T -> bool} {_ : Transitive lt}
  : Transitive (lattice_for_lt lt).
admit.
Defined.

Class grammar_fixedpoint_lattice_data prestate :=
  { state :> _ := lattice_for prestate;
    prestate_lt : prestate -> prestate -> bool;
    state_lt : state -> state -> bool
    := lattice_for_lt prestate_lt;
    prestate_beq : prestate -> prestate -> bool;
    state_beq : state -> state -> bool
    := lattice_for_beq prestate_beq;
    prestate_le s1 s2 := (prestate_beq s1 s2 || prestate_lt s1 s2)%bool;
    state_le s1 s2 := (state_beq s1 s2 || state_lt s1 s2)%bool;
    prestate_beq_Equivalence : Equivalence prestate_beq;
    state_beq_Equivalence : Equivalence state_beq
    := lattice_for_Equivalence;
    preleast_upper_bound : prestate -> prestate -> state;
    least_upper_bound : state -> state -> state
    := lattice_for_lub preleast_upper_bound;
    preleast_upper_bound_correct_l
    : forall a b, state_le (constant a) (preleast_upper_bound a b);
    preleast_upper_bound_correct_r
    : forall a b, state_le (constant b) (preleast_upper_bound a b);
    least_upper_bound_correct_l
    : forall a b, state_le a (least_upper_bound a b)
    := lattice_for_lub_correct_l prestate_beq prestate_lt preleast_upper_bound preleast_upper_bound_correct_l _;
    least_upper_bound_correct_r
    : forall a b, state_le b (least_upper_bound a b)
    := lattice_for_lub_correct_r prestate_beq prestate_lt preleast_upper_bound preleast_upper_bound_correct_r _;
    prestate_gt_wf : well_founded (Basics.flip prestate_lt);
    state_gt_wf : well_founded (Basics.flip state_lt)
    := lattice_for_gt_well_founded prestate_gt_wf;
    preleast_upper_bound_Proper : Proper (prestate_beq ==> prestate_beq ==> state_beq) preleast_upper_bound;
    least_upper_bound_Proper : Proper (state_beq ==> state_beq ==> state_beq) least_upper_bound
    := @lattice_for_lub_Proper _ _ _ _;
    prestate_lt_Proper : Proper (prestate_beq ==> prestate_beq ==> eq) prestate_lt;
    state_lt_Proper : Proper (state_beq ==> state_beq ==> eq) state_lt
    := lattice_for_lt_Proper;
    prestate_lt_Transitive : Transitive prestate_lt;
    state_lt_Transitive : Transitive state_lt
    := lattice_for_lt_Transitive }.

Record grammar_fixedpoint_data :=
  { prestate : Type;
    lattice_data :> grammar_fixedpoint_lattice_data prestate;
    step_constraints : (default_nonterminal_carrierT -> state) -> (default_nonterminal_carrierT -> state -> state);
    step_constraints_ext : Proper (pointwise_relation _ state_beq ==> eq ==> state_beq ==> state_beq) step_constraints }.
Global Existing Instance state_beq_Equivalence.
Global Existing Instance state_lt_Proper.
Global Existing Instance least_upper_bound_Proper.
Global Arguments state {_ _}, {_} _.

Infix "<=" := (@state_le _ _) : grammar_fixedpoint_scope.
Infix "⊔" := (@least_upper_bound _ _) : grammar_fixedpoint_scope.

Definition nonterminal_to_positive (nt : default_nonterminal_carrierT) : positive
  := Pos.of_nat (S nt).
Definition positive_to_nonterminal (nt : positive) : default_nonterminal_carrierT
  := pred (Pos.to_nat nt).

End Definitions.
Module Export AsciiLattice.
Import Coq.Strings.Ascii.
Import Coq.MSets.MSetPositive.
Import Fiat.Common.MSetExtensions.
Module Import PositiveSetExtensions := MSetExtensions PositiveSet.

Section gen.
  Global Instance positive_set_fpdata
    : grammar_fixedpoint_lattice_data PositiveSet.t.
admit.
Defined.
End gen.

Definition max_ascii := Eval compute in BinPos.Pos.of_nat (S (nat_of_ascii (Ascii true true true true true true true true))).

End AsciiLattice.
Module Export Properties.
Import Fiat.Common.
Local Open Scope grammar_fixedpoint_scope.

Global Instance state_le_Reflexive {T d} : Reflexive (@state_le T d).
admit.
Defined.

Global Instance state_beq_Proper_Proper {prestate} {d : grammar_fixedpoint_lattice_data prestate}
  : Proper (state_beq ==> state_beq ==> eq) state_beq.
admit.
Defined.

Global Instance state_beq_Proper_le {prestate} {d : grammar_fixedpoint_lattice_data prestate}
  : Proper (state_beq ==> state_beq ==> eq) state_le.
admit.
Defined.

Global Instance state_le_Transitive {T d} : Transitive (@state_le T d).
admit.
Defined.

Lemma top_top {prestate} {d : grammar_fixedpoint_lattice_data prestate} (s : state)
  : s <= ⊤.
admit.
Defined.

Lemma bottom_lub_r {prestate} {d : grammar_fixedpoint_lattice_data prestate} (s : state)
  : (s ⊔ ⊥) = s.
admit.
Defined.

Lemma bottom_lub_l {prestate} {d : grammar_fixedpoint_lattice_data prestate} (s : state)
  : (⊥ ⊔ s) = s.
admit.
Defined.

Global Instance state_le_Proper_le' {state} {d : grammar_fixedpoint_lattice_data state}
: Proper (@state_le _ d ==> Basics.flip (@state_le _ d) ==> Basics.flip implb) (@state_le _ d).
admit.
Defined.

Global Instance state_le_Antisymmetric {prestate} {fpdata : grammar_fixedpoint_lattice_data prestate}
  : Antisymmetric _ state_beq state_le.
admit.
Defined.

End Properties.
Module Export RDPList.

Import Coq.Lists.List.
Import Coq.ZArith.ZArith.
Import Fiat.Common.

Section recursive_descent_parser_list.
  Context {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {HLSP : StringLikeProperties Char} {G : pregrammar' Char}
          (Char_beq : Char -> Char -> bool).
  Definition rdp_list_nonterminals_listT : Type := list nat.
  Notation rdp_list_nonterminal_carrierT := default_nonterminal_carrierT.

  Notation rdp_list_production_carrierT := default_production_carrierT.

  Definition list_bin_eq
    := Eval unfold list_bin in list_bin EqNat.beq_nat.

  Definition rdp_list_is_valid_nonterminal : rdp_list_nonterminals_listT -> rdp_list_nonterminal_carrierT -> bool
    := fun ls nt => list_bin_eq nt ls.

  Local Notation valid_nonterminals := (map fst (pregrammar_productions G)).

  Definition rdp_list_initial_nonterminals_data
  : rdp_list_nonterminals_listT
    := up_to (List.length valid_nonterminals).

  Definition rdp_list_of_nonterminal
  : String.string -> rdp_list_nonterminal_carrierT
    := default_of_nonterminal (G := G).
  Definition rdp_list_to_nonterminal
  : rdp_list_nonterminal_carrierT -> String.string
    := default_to_nonterminal (G := G).

  Definition rdp_list_to_production : rdp_list_production_carrierT -> production Char
    := default_to_production (G := G).

  Definition rdp_list_nonterminal_to_production : rdp_list_nonterminal_carrierT -> list rdp_list_production_carrierT
    := fun nt_idx
       => List.map
            (fun p_idx : nat => (nt_idx, (p_idx, 0)))
            (up_to (List.length (Lookup G (rdp_list_to_nonterminal nt_idx)))).

  Definition rdp_list_production_tl : rdp_list_production_carrierT -> rdp_list_production_carrierT
    := (default_production_tl (G := G)).

  Definition rdp_list_initial_nonterminals_correct'
  : forall nt,
      is_true (rdp_list_is_valid_nonterminal rdp_list_initial_nonterminals_data nt) <-> List.In (rdp_list_to_nonterminal nt) (Valid_nonterminals G).
admit.
Defined.

  Definition rdp_list_initial_nonterminals_correct
  : forall nt,
      is_true (rdp_list_is_valid_nonterminal rdp_list_initial_nonterminals_data (rdp_list_of_nonterminal nt)) <-> List.In nt (Valid_nonterminals G).
admit.
Defined.

  Lemma rdp_list_to_of_nonterminal
  : forall nt,
      List.In nt (Valid_nonterminals G)
      -> rdp_list_to_nonterminal (rdp_list_of_nonterminal nt) = nt.
admit.
Defined.

  Lemma rdp_list_of_to_nonterminal
  : forall nt,
      is_true (rdp_list_is_valid_nonterminal rdp_list_initial_nonterminals_data nt)
      -> rdp_list_of_nonterminal (rdp_list_to_nonterminal nt) = nt.
admit.
Defined.

  Definition rdp_list_production_carrier_valid
  : rdp_list_production_carrierT -> bool
    := default_production_carrier_valid (G := G).

  Lemma rdp_list_production_tl_correct
  : forall p,
      rdp_list_to_production (rdp_list_production_tl p) = tl (rdp_list_to_production p).
admit.
Defined.

  Lemma rdp_list_nonterminal_to_production_correct
  : forall nt,
      List.In nt (Valid_nonterminals G)
      -> List.map rdp_list_to_production (rdp_list_nonterminal_to_production (rdp_list_of_nonterminal nt))
         = Lookup G nt.
admit.
Defined.

  Lemma rdp_list_production_tl_valid
  : forall p,
      rdp_list_production_carrier_valid p -> rdp_list_production_carrier_valid (rdp_list_production_tl p).
admit.
Defined.

  Lemma rdp_list_nonterminal_to_production_valid
  : forall nt,
      rdp_list_is_valid_nonterminal rdp_list_initial_nonterminals_data nt
      -> List.Forall rdp_list_production_carrier_valid (rdp_list_nonterminal_to_production nt).
admit.
Defined.

  Definition filter_out_eq nt ls
    := Eval unfold filter_out in filter_out (EqNat.beq_nat nt) ls.

  Definition rdp_list_remove_nonterminal : rdp_list_nonterminals_listT -> rdp_list_nonterminal_carrierT -> rdp_list_nonterminals_listT
    := fun ls nt =>
         filter_out_eq nt ls.

  Definition rdp_list_nonterminals_listT_R : rdp_list_nonterminals_listT -> rdp_list_nonterminals_listT -> Prop
    := ltof _ (@List.length _).
  Lemma rdp_list_remove_nonterminal_dec : forall ls prods,
                                            @rdp_list_is_valid_nonterminal ls prods = true
                                            -> @rdp_list_nonterminals_listT_R (@rdp_list_remove_nonterminal ls prods) ls.
admit.
Defined.

  Lemma rdp_list_remove_nonterminal_1
  : forall ls ps ps',
      rdp_list_is_valid_nonterminal (rdp_list_remove_nonterminal ls ps) ps' = true
      -> rdp_list_is_valid_nonterminal ls ps' = true.
admit.
Defined.

  Lemma rdp_list_remove_nonterminal_2
  : forall ls ps ps',
      rdp_list_is_valid_nonterminal (rdp_list_remove_nonterminal ls ps) ps' = false
      <-> rdp_list_is_valid_nonterminal ls ps' = false \/ ps = ps'.
admit.
Defined.

  Lemma rdp_list_remove_nonterminal_noninc (ls : rdp_list_nonterminals_listT) nonterminal
  : ~ rdp_list_nonterminals_listT_R ls (rdp_list_remove_nonterminal ls nonterminal).
admit.
Defined.

  Lemma rdp_list_nonterminals_length_zero
  : forall ls,
      List.length ls = 0
      -> forall nt, rdp_list_is_valid_nonterminal ls nt = false.
admit.
Defined.

  Global Instance rdp_list_predata : @parser_computational_predataT Char
    := { nonterminals_listT := rdp_list_nonterminals_listT;
         initial_nonterminals_data := rdp_list_initial_nonterminals_data;
         of_nonterminal := rdp_list_of_nonterminal;
         to_nonterminal := rdp_list_to_nonterminal;
         production_carrierT := rdp_list_production_carrierT;
         to_production := rdp_list_to_production;
         nonterminal_to_production := rdp_list_nonterminal_to_production;
         production_tl := rdp_list_production_tl;
         production_carrier_valid := rdp_list_production_carrier_valid;
         is_valid_nonterminal := rdp_list_is_valid_nonterminal;
         remove_nonterminal := rdp_list_remove_nonterminal;
         nonterminals_length := @List.length _ }.

  Global Instance rdp_list_rdata' : @parser_removal_dataT' _ G rdp_list_predata
    := { nonterminals_length_zero := rdp_list_nonterminals_length_zero;
         remove_nonterminal_dec := rdp_list_remove_nonterminal_dec;
         remove_nonterminal_noninc := rdp_list_remove_nonterminal_noninc;
         to_of_nonterminal := rdp_list_to_of_nonterminal;
         of_to_nonterminal := rdp_list_of_to_nonterminal;
         production_tl_correct := rdp_list_production_tl_correct;
         nonterminal_to_production_correct := rdp_list_nonterminal_to_production_correct;
         production_tl_valid := rdp_list_production_tl_valid;
         nonterminal_to_production_valid := rdp_list_nonterminal_to_production_valid;
         initial_nonterminals_correct := rdp_list_initial_nonterminals_correct;
         initial_nonterminals_correct' := rdp_list_initial_nonterminals_correct';
         remove_nonterminal_1 := rdp_list_remove_nonterminal_1;
         remove_nonterminal_2 := rdp_list_remove_nonterminal_2 }.
End recursive_descent_parser_list.

End RDPList.

Module Export Fix.
Import Coq.FSets.FMapPositive.
Import Fiat.Common.FMapExtensions.Wf.
Import Fiat.Common.
Module PositiveMapExtensions := FMapExtensionsWf PositiveMap.
Local Open Scope grammar_fixedpoint_scope.

Section grammar_fixedpoint.
  Context {Char : Type}.

  Context (gdata : grammar_fixedpoint_data).

  Definition aggregate_state := PositiveMap.t (state gdata).

  Local Notation default_value := ⊤ (only parsing).

  Definition lookup_state (st : aggregate_state) (nt : default_nonterminal_carrierT)
    : state gdata
    := PositiveMapExtensions.find_default default_value (nonterminal_to_positive nt) st.

  Notation from_aggregate_state := lookup_state (only parsing).
  Definition aggregate_state_eq : aggregate_state -> aggregate_state -> bool
    := PositiveMapExtensions.lift_eqb state_beq default_value.
  Definition aggregate_state_lt (v1 v2 : aggregate_state) : bool
    := PositiveMapExtensions.lift_ltb state_beq state_le default_value v1 v2.

  Definition aggregate_state_lub_f : option (state gdata) -> option (state gdata) -> option (state gdata)
      := PositiveMapExtensions.defaulted_f default_value default_value least_upper_bound.

  Definition aggregate_state_lub (v1 v2 : aggregate_state) : aggregate_state
    := PositiveMap.map2 aggregate_state_lub_f v1 v2.

  Definition aggregate_prestep (v : aggregate_state) : aggregate_state
    := let helper := step_constraints gdata (from_aggregate_state v) in
       PositiveMap.mapi (fun nt => helper (positive_to_nonterminal nt)) v.

  Definition aggregate_step (v : aggregate_state) : aggregate_state
    := aggregate_state_lub v (aggregate_prestep v).

  Lemma aggregate_state_lt_wf : well_founded (Basics.flip aggregate_state_lt).
admit.
Defined.

  Section wrap_wf.
    Context {A R} (Rwf : @well_founded A R).

    Definition lt_wf_idx_step
               (lt_wf_idx : nat -> well_founded R)
               (n : nat)
      : well_founded R.
    Proof.
      destruct n.
      {
 clear -Rwf; abstract apply Rwf.
}
      {
 constructor; intros; apply lt_wf_idx; assumption.
}
    Defined.

    Fixpoint lt_wf_idx (n : nat) : well_founded R
      := lt_wf_idx_step (@lt_wf_idx) n.
  End wrap_wf.

  Definition aggregate_state_lt_wf_idx (n : nat) : well_founded (Basics.flip aggregate_state_lt)
    := lt_wf_idx aggregate_state_lt_wf n.

  Definition step_lt {st}
    : aggregate_state_eq st (aggregate_step st) = false -> Basics.flip aggregate_state_lt (aggregate_step st) st.
admit.
Defined.

  Global Instance from_aggregate_state_Proper
    : Proper (aggregate_state_eq ==> eq ==> state_beq) from_aggregate_state | 1.
admit.
Defined.

  Lemma lookup_state_aggregate_state_lub a b nt
    : lookup_state (aggregate_state_lub a b) nt = (lookup_state a nt ⊔ lookup_state b nt).
admit.
Defined.

  Lemma lookup_state_aggregate_prestep st nt
    : lookup_state (aggregate_prestep st) nt
      = option_rect (fun _ => _)
                    (fun _ => step_constraints gdata (lookup_state st) nt (lookup_state st nt))
                    default_value
                    (PositiveMap.find (nonterminal_to_positive nt) st).
admit.
Defined.

  Section with_initial.
    Context (initial_nonterminals_data : list default_nonterminal_carrierT).

    Definition aggregate_state_max : aggregate_state
      := List.fold_right
           (fun nt st => PositiveMap.add (nonterminal_to_positive nt) ⊥ st)
           (PositiveMap.empty _)
           initial_nonterminals_data.

    Definition pre_Fix_grammar_helper : aggregate_state -> aggregate_state
      := Fix
           (aggregate_state_lt_wf_idx (10 * List.length initial_nonterminals_data))
           (fun _ => aggregate_state)
           (fun st Fix_grammar_internal
            => let st' := aggregate_step st in
               match Sumbool.sumbool_of_bool (aggregate_state_eq st st') with
               | left pf => st
               | right pf => Fix_grammar_internal st' (step_lt pf)
               end).

    Definition pre_Fix_grammar : aggregate_state
      := pre_Fix_grammar_helper aggregate_state_max.

    Lemma pre_Fix_grammar_fixedpoint
      : aggregate_state_eq pre_Fix_grammar (aggregate_step pre_Fix_grammar).
admit.
Defined.
  End with_initial.

  Section with_grammar.
    Context (G : pregrammar' Char).

    Let predata := @rdp_list_predata _ G.
    Local Existing Instance predata.

    Lemma find_pre_Fix_grammar_to_lookup_state (nt : default_nonterminal_carrierT)
      : PositiveMap.find (nonterminal_to_positive nt) (pre_Fix_grammar initial_nonterminals_data)
        = if is_valid_nonterminal initial_nonterminals_data nt
          then Some (lookup_state (pre_Fix_grammar initial_nonterminals_data) nt)
          else None.
admit.
Defined.
  End with_grammar.
End grammar_fixedpoint.

End Fix.

Module opt.
  Section syntax.
    Context {T : Type}.

    Inductive item :=
    | Terminal (_ : T)
    | NonTerminal (nt : String.string) (_ : nat).

    Definition production := list item.
    Definition productions := list production.
  End syntax.

  Global Arguments item : clear implicits.
  Global Arguments production : clear implicits.
  Global Arguments productions : clear implicits.

  Section semantics.
    Context {Char : Type} {T : Type}.

    Class compile_item_data :=
      { on_terminal : (Char -> bool) -> T;
        nonterminal_names : list String.string;
        invalid_nonterminal : String.string }.

    Context {cidata : compile_item_data}.
    Definition compile_nonterminal nt
      := List.first_index_default (string_beq nt) (List.length nonterminal_names) nonterminal_names.
    Definition compile_item (expr : Core.item Char) : opt.item T
      := match expr with
         | Core.Terminal ch => Terminal (on_terminal ch)
         | Core.NonTerminal nt => NonTerminal nt (compile_nonterminal nt)
         end.

    Definition compile_production (expr : Core.production Char) : opt.production T
      := List.map compile_item expr.

    Definition compile_productions (expr : Core.productions Char) : opt.productions T
      := List.map compile_production expr.
  End semantics.

  Global Arguments compile_item_data : clear implicits.
End opt.

Module Export FromAbstractInterpretationDefinitions.
Import Coq.Sets.Ensembles.
Import Coq.Classes.Morphisms.
Local Coercion is_true : bool >-> Sortclass.
Local Open Scope grammar_fixedpoint_scope.

Section general_fold.
  Context {Char : Type}
          {T : Type}.

  Definition lattice_for_combine_production combine_production
    : lattice_for T -> lattice_for T -> lattice_for T
    := fun x y => match x, y with
                  | ⊥, _
                  | _, ⊥
                    => ⊥
                  | ⊤, _
                  | _, ⊤
                    => ⊤
                  | constant x', constant y'
                    => combine_production x' y'
                  end.

  Global Instance lattice_for_combine_production_Proper
         {prestate_beq : T -> T -> bool}
         {precombine_production}
         {H : Proper (prestate_beq ==> prestate_beq ==> lattice_for_beq prestate_beq) precombine_production}
    : Proper (lattice_for_beq prestate_beq ==> lattice_for_beq prestate_beq ==> lattice_for_beq prestate_beq) (lattice_for_combine_production precombine_production).
admit.
Defined.

  Context {fpdata : @grammar_fixedpoint_lattice_data T}.

  Class AbstractInterpretation :=
    { on_terminal : (Char -> bool) -> lattice_for T;
      on_nil_production : lattice_for T;
      precombine_production : T -> T -> lattice_for T;
      combine_production : lattice_for T -> lattice_for T -> lattice_for T
      := lattice_for_combine_production precombine_production;
      precombine_production_Proper : Proper (prestate_beq ==> prestate_beq ==> state_beq) precombine_production;
      combine_production_Proper : Proper (state_beq ==> state_beq ==> state_beq) combine_production
      := lattice_for_combine_production_Proper }.

  Global Existing Instance precombine_production_Proper.

  Context {aidata : AbstractInterpretation}.

  Context (G : pregrammar' Char).

  Global Instance compile_item_data_of_abstract_interpretation : opt.compile_item_data Char state
    := {| opt.on_terminal := on_terminal;
          opt.nonterminal_names := pregrammar_nonterminals G;
          opt.invalid_nonterminal := Gensym.gensym (pregrammar_nonterminals G) |}.

  Section with_compiled_productions.
    Context (compiled_productions : list (opt.productions state)).

    Definition opt_Lookup_idx (n : nat) : opt.productions state
      := List.nth n compiled_productions nil.
    Lemma eq_opt_Lookup_idx
          (Hcompiled_productions : List.map opt.compile_productions (List.map snd (pregrammar_productions G)) = compiled_productions)
          n
      : opt_Lookup_idx n = opt.compile_productions (Lookup_idx G n).
admit.
Defined.

    Definition fold_item'
               (fold_nt : default_nonterminal_carrierT -> state)
               (it : opt.item state)
      : state
      := match it with
         | opt.Terminal tv => tv
         | opt.NonTerminal nt nt_idx => fold_nt nt_idx
         end.

    Definition fold_production'
               (fold_nt : default_nonterminal_carrierT -> state)
               (its : opt.production state)
      := List.fold_right
           combine_production
           on_nil_production
           (List.map
              (fold_item' fold_nt)
              its).

    Definition fold_productions'
               (fold_nt : default_nonterminal_carrierT -> state)
               (its : opt.productions state)
      := List.fold_right
           least_upper_bound
           ⊥
           (List.map
              (fold_production' fold_nt)
              its).

    Definition fold_constraints
               (fold_nt : default_nonterminal_carrierT -> state)
               (nt : default_nonterminal_carrierT)
      : state
      := fold_productions'
           fold_nt
           (opt_Lookup_idx nt).

    Section extR.
      Context (R : state -> state -> Prop)
              (combine_production_Proper : Proper (R ==> R ==> R) combine_production)
              (lub_Proper : Proper (R ==> R ==> R) least_upper_bound)
              (R_Reflexive : Reflexive R).

      Lemma fold_item'_extR {f g} (ext : forall b, R (f b) (g b)) b
        : R (fold_item' f b) (fold_item' g b).
      Proof.
        unfold fold_item'.
        generalize (@of_nonterminal _ (@rdp_list_predata _ G)); simpl; intro.
        generalize on_terminal; intro.
        unfold state in *.
        simpl in *.
        clear -ext R_Reflexive.
 admit.
      Defined.

      Lemma fold_production'_extR {f g} (ext : forall b, R (f b) (g b)) b
        : R (fold_production' f b) (fold_production' g b).
      Proof.
        unfold fold_production'.
        induction b as [ | x ]; try reflexivity; simpl.
        apply combine_production_Proper; [ apply (fold_item'_extR ext) | apply IHb ].
      Defined.

      Lemma fold_productions'_extR {f g} (ext : forall b, R (f b) (g b)) b
        : R (fold_productions' f b) (fold_productions' g b).
      Proof.
        unfold fold_productions'.
        induction b as [ | x ]; try reflexivity; simpl.
        apply lub_Proper; [ apply (fold_production'_extR ext) | apply IHb ].
      Defined.

      Lemma fold_constraints_extR f g (H : forall x, R (f x) (g x)) nt
        : R (fold_constraints f nt) (fold_constraints g nt).
      Proof.
        unfold fold_constraints.
        apply fold_productions'_extR.
        intro; apply H.
      Defined.
    End extR.

    Global Instance fold_constraints_ProperR
           {R : state -> state -> Prop}
           {combine_production_Proper : Proper (R ==> R ==> R) combine_production}
           {lub_Proper : Proper (R ==> R ==> R) least_upper_bound}
           {R_Reflexive : Reflexive R}
      : Proper (pointwise_relation default_nonterminal_carrierT R ==> eq ==> R)
               fold_constraints
    | 10.
    Proof.
      intros f g H; repeat intro; subst.
      apply fold_constraints_extR; assumption.
    Defined.

    Global Instance fold_constraints_Proper_state_beq
      : Proper (pointwise_relation default_nonterminal_carrierT state_beq ==> eq ==> state_beq)
               fold_constraints
      := _.

    Definition fixedpoint_by_abstract_interpretation : grammar_fixedpoint_data.
    Proof.
      refine {| prestate := T;
                step_constraints folder nt st := fold_constraints folder nt;
                lattice_data := fpdata |}.
      {
 repeat intro; apply fold_constraints_Proper_state_beq; assumption.
}
    Defined.
  End with_compiled_productions.
End general_fold.

Section on_ensembles.
  Context {Char : Type} {HSLM : StringLikeMin Char} {HSL : StringLike Char}.

  Definition ensemble_on_terminal (P : Char -> bool) : Ensemble String
    := (fun str => exists ch, is_true (P ch) /\ str ~= [ ch ])%string_like.

  Definition ensemble_on_nil_production : Ensemble String
    := (fun str => length str = 0).

  Definition ensemble_combine_production : Ensemble String -> Ensemble String -> Ensemble String
    := fun P1 P2 => fun str => exists n, P1 (take n str) /\ P2 (drop n str).

  Definition ensemble_least_upper_bound : Ensemble String -> Ensemble String -> Ensemble String
    := fun P1 P2 => fun str => P1 str \/ P2 str.
End on_ensembles.

Section fold_correctness.
  Context {Char : Type} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char}.
  Context {T : Type}.
  Context {fpdata : @grammar_fixedpoint_lattice_data T}
          {aidata : @AbstractInterpretation Char T fpdata}.
  Context (G : pregrammar Char)
          (prerelated : Ensemble String -> T -> Prop).

  Definition lattice_for_related (P : Ensemble String) (st : lattice_for T) : Prop
    := match st with
       | ⊤ => True
       | ⊥ => forall str, ~P str
       | constant n => prerelated P n
       end.

  Section related.
    Local Notation related := lattice_for_related.

    Global Instance lattice_for_related_ext {_ : Proper ((beq ==> iff) ==> prestate_beq ==> iff) prerelated}
      : Proper ((beq ==> iff) ==> state_beq ==> iff) related | 2.
    Proof.
      intros ?? H' [|?|] [|?|] ?; simpl in *;
        try tauto;
        try congruence;
        try (apply H; assumption);
        try setoid_rewrite H';
        try setoid_rewrite (fun x => H' x x (reflexivity _));
        try reflexivity.
    Qed.

    Global Instance lattice_for_combine_production_Proper_le
           {precombine_production'}
           {H : Proper (prestate_le ==> prestate_le ==> state_le) precombine_production'}
      : Proper (state_le ==> state_le ==> state_le) (lattice_for_combine_production precombine_production').
admit.
Defined.
  End related.

  Class AbstractInterpretationCorrectness :=
    { prerelated_ext : Proper ((beq ==> iff) ==> prestate_beq ==> iff) prerelated;
      related : Ensemble String -> state -> Prop
      := lattice_for_related;
      related_ext : Proper ((beq ==> iff) ==> state_beq ==> iff) related
      := lattice_for_related_ext;
      related_monotonic : forall s0 s1, s0 <= s1 -> (forall v, related v s0 -> related v s1);
      lub_correct
      : forall P1 st1,
          related P1 st1
          -> forall P2 st2,
            related P2 st2
            -> related (ensemble_least_upper_bound P1 P2) (least_upper_bound st1 st2);
      on_terminal_correct
      : forall P,
          related (ensemble_on_terminal P) (on_terminal P);
      on_nil_production_correct
      : related ensemble_on_nil_production on_nil_production;
      precombine_production_Proper_le
      : Proper (prestate_le ==> prestate_le ==> state_le) precombine_production;
      combine_production_Proper_le
      : Proper (state_le ==> state_le ==> state_le) combine_production
      := _;
      combine_production_correct
      : forall P1 st1,
          related P1 st1
          -> forall P2 st2,
            related P2 st2
            -> related (ensemble_combine_production P1 P2) (combine_production st1 st2)
    }.
End fold_correctness.

Module Export FromAbstractInterpretation.
Import Fiat.Common.

Section fold_correctness.
  Context {Char : Type} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char}.
  Context {T : Type}.
  Context {fpdata : @grammar_fixedpoint_lattice_data T}
          {aidata : @AbstractInterpretation Char T fpdata}
          (prerelated : Ensemble String -> T -> Prop)
          {aicdata : AbstractInterpretationCorrectness prerelated}.
  Context (G : pregrammar' Char).
  Local Hint Immediate (compile_item_data_of_abstract_interpretation G) : typeclass_instances.
  Context (compiled_productions : list (opt.productions state))
          (Hcompiled_productions : List.map opt.compile_productions (List.map snd (pregrammar_productions G)) = compiled_productions).

  Let predata := @rdp_list_predata _ G.
  Local Existing Instance predata.

  Definition fold_grammar : aggregate_state (fixedpoint_by_abstract_interpretation G compiled_productions)
    := pre_Fix_grammar _ initial_nonterminals_data.

  Record ensemble_result (str : String) (fold_state : state) :=
    { er_ensemble :> Ensemble String;
      er_state :> state;
      er_related :> related er_ensemble er_state;
      er_correct :> Ensembles.In _ er_ensemble str;
      er_state_le :> er_state <= fold_state }.

  Definition er_lift {str st1 st2}
             (v : ensemble_result str st1)
             (Hle : st1 <= st2)
    : ensemble_result str st2
    := {| er_ensemble := v;
          er_state := v;
          er_related := er_related v;
          er_correct := er_correct v;
          er_state_le := transitivity (R := state_le) (er_state_le v) Hle |}.

  Definition er_combine_production n str st1 st2 (it : ensemble_result (take n str) st1) (its : ensemble_result (drop n str) st2)
    : ensemble_result str (combine_production st1 st2)
    := {| er_ensemble := ensemble_combine_production it its;
          er_state := combine_production (T := T) (it : state) (its : state);
          er_related := combine_production_correct it it (er_related it) its its (er_related its);
          er_correct := ex_intro _ n (conj (er_correct it) (er_correct its));
          er_state_le := combine_production_Proper_le (er_state_le it) (er_state_le its) |}.

  Instance flip_state_le_eta : subrelation (flip (C:=Prop) (fun x y => x <= y)) (fun x y : state => flip state_le x y).
admit.
Defined.

  Lemma fold_le nt st
        (H : st <= fold_productions' (lookup_state fold_grammar) (opt.compile_productions (Lookup_string G nt)))
    : st <= lookup_state fold_grammar (of_nonterminal nt).
  Proof.
    unfold fold_grammar.
    rewrite pre_Fix_grammar_fixedpoint.
    unfold aggregate_step.
    rewrite lookup_state_aggregate_state_lub, <- least_upper_bound_correct_r.
    rewrite lookup_state_aggregate_prestep, (find_pre_Fix_grammar_to_lookup_state _ G).
    let v := match goal with |- context[if ?v then _ else _] => v end in
    destruct v eqn:Hvalid; unfold option_rect; [ | apply top_top ].
    unfold step_constraints.
    unfold fixedpoint_by_abstract_interpretation at 3.
    unfold fold_constraints.
    erewrite eq_opt_Lookup_idx by (eassumption || reflexivity).
    rewrite <- list_to_productions_to_nonterminal.
    change (default_to_nonterminal ?nt) with (to_nonterminal nt).
    rewrite to_of_nonterminal by (eapply initial_nonterminals_correct; assumption).
    assumption.
  Qed.

  Definition lift_ensemble_result {str nt}
             (res : ensemble_result str (fold_productions' (lookup_state fold_grammar) (opt.compile_productions (G nt))))
    : ensemble_result str (lookup_state fold_grammar (of_nonterminal nt))
    := {| er_ensemble := er_ensemble res;
          er_state := er_state res;
          er_related := er_related res;
          er_correct := er_correct res;
          er_state_le := fold_le _ _ (er_state_le res) |}.

  Section step.
    Context (state_of_parse : forall str pats, parse_of G str pats -> ensemble_result str (fold_productions' (lookup_state fold_grammar) (opt.compile_productions pats)))
            (state_of_parse_production : forall str pat, parse_of_production G str pat -> ensemble_result str (fold_production' (lookup_state fold_grammar) (opt.compile_production pat)))
            (state_of_parse_item : forall str it, parse_of_item G str it -> ensemble_result str (fold_item' (lookup_state fold_grammar) (opt.compile_item it))).

    Definition state_of_parse_item'
               str it (p : parse_of_item G str it)
      : ensemble_result str (fold_item' (lookup_state fold_grammar) (opt.compile_item it))
      := match p in parse_of_item _ _ it return ensemble_result _ (fold_item' _ (opt.compile_item it)) with
         | ParseTerminal ch P Hch Hstr
           => {| er_state := on_terminal P;
                 er_ensemble := ensemble_on_terminal P;
                 er_related := on_terminal_correct P;
                 er_correct := ex_intro _ ch (conj Hch Hstr);
                 er_state_le := reflexivity (R := state_le) _ |}
         | ParseNonTerminal nt Hvalid p' => lift_ensemble_result (state_of_parse p')
         end.

    Definition state_of_parse_production'
               str pat (p : parse_of_production G str pat)
      : ensemble_result str (fold_production' (lookup_state fold_grammar) (opt.compile_production pat))
      := match p with
         | ParseProductionNil Hlen
           => {| er_state := on_nil_production;
                 er_ensemble := ensemble_on_nil_production;
                 er_related := on_nil_production_correct (prerelated := prerelated);
                 er_correct := Hlen;
                 er_state_le := reflexivity (R := state_le) _ |}
         | ParseProductionCons n pat pats p' p's
           => er_combine_production
                n
                str
                (state_of_parse_item p')
                (state_of_parse_production p's)
         end.

    Definition state_of_parse'
               str pats (p : parse_of G str pats)
      : ensemble_result str (fold_productions' (lookup_state fold_grammar) (opt.compile_productions pats))
      := match p in parse_of _ _ pats return ensemble_result _ (fold_productions' _ (opt.compile_productions pats)) with
         | ParseHead pat pats p' => er_lift (state_of_parse_production p') (least_upper_bound_correct_l _ _)
         | ParseTail pat pats p' => er_lift (state_of_parse p') (least_upper_bound_correct_r _ _)
         end.
  End step.

  Fixpoint state_of_parse str pats (p : parse_of G str pats)
    := @state_of_parse' (@state_of_parse) (@state_of_parse_production) str pats p
  with state_of_parse_production str pat (p : parse_of_production G str pat)
    := @state_of_parse_production' (@state_of_parse_production) (@state_of_parse_item) str pat p
  with state_of_parse_item str it (p : parse_of_item G str it)
    := @state_of_parse_item' (@state_of_parse) str it p.

  Lemma fold_grammar_correct_item str nt
        (p : parse_of_item G str (NonTerminal nt))
    : exists P, P str /\ related P (lookup_state fold_grammar (opt.compile_nonterminal nt)).
  Proof.
    pose proof (@state_of_parse_item _ _ p) as p'.
    unfold fold_item' in p'.
    exists (er_ensemble p').
    split; [ apply p' | ].
    eapply (related_monotonic _); apply p'.
  Qed.

  Lemma fold_grammar_correct_production str ps
        (p : parse_of_production G str ps)
    : exists P, P str /\ related P (fold_production' (lookup_state fold_grammar) (opt.compile_production ps)).
admit.
Defined.

  Lemma fold_grammar_correct str nt
        (p : parse_of G str (Lookup G nt))
    : exists P, P str /\ related P (lookup_state fold_grammar (of_nonterminal nt)).
admit.
Defined.
End fold_correctness.

Local Hint Immediate compile_item_data_of_abstract_interpretation : typeclass_instances.
Local Notation compiled_productions G
  := (List.map opt.compile_productions (List.map snd (pregrammar_productions G))).

Class fold_grammar_data {Char T} {fpdata : grammar_fixedpoint_lattice_data T}
      {aidata : AbstractInterpretation}
      (G : pregrammar' Char) :=
  { fgd_fold_grammar : aggregate_state (fixedpoint_by_abstract_interpretation G (compiled_productions G));
    fgd_fold_grammar_correct : pointwise_relation _ eq (lookup_state fgd_fold_grammar) (lookup_state (fold_grammar G (compiled_productions G))) }.
Coercion fgd_fold_grammar : fold_grammar_data >-> aggregate_state.

End FromAbstractInterpretation.
Import Fiat.Common.BoolFacts.
Import Fiat.Common.
Import Fiat.Common.Wf.

Local Open Scope bool_scope.

Global Instance prod_fixedpoint_lattice {prestate0 prestate1}
       {fpldata0 : grammar_fixedpoint_lattice_data prestate0}
       {fpldata1 : grammar_fixedpoint_lattice_data prestate1}
  : grammar_fixedpoint_lattice_data (@state _ fpldata0 * @state _ fpldata1).
Proof.
  refine {| prestate_lt x y := ((state_le (fst x) (fst y) && state_le (snd x) (snd y))
                                  && negb (state_beq (fst x) (fst y) && state_beq (snd x) (snd y)));
            prestate_beq := Equality.prod_beq state_beq state_beq;
            preleast_upper_bound x y
            := constant (least_upper_bound (fst x) (fst y), least_upper_bound (snd x) (snd y)) |};
  try abstract (
        repeat match goal with
               | _ => progress unfold Equality.prod_beq
               | [ |- RelationClasses.Equivalence _ ]
                 => split; repeat intro
               | [ |- well_founded _ ] => fail 1
               | [ |- is_true (?R ?x ?x) ] => reflexivity
               | [ |- is_true true ] => reflexivity
               | [ |- ?R ?x ?x ] => reflexivity
               | _ => congruence
               | [ |- Proper _ _ ] => unfold Proper, respectful
               | [ |- Transitive _ ] => intros ???; cbv beta
               | _ => progress intros
               | [ H : and _ _ |- _ ] => destruct H
               | [ H : prod _ _ |- _ ] => destruct H
               | _ => progress simpl in *
               | [ H : is_true (state_beq ?x ?y) |- _ ]
                 => rewrite H in *; clear x H
               | [ H : is_true (state_beq ?x ?y) |- _ ]
                 => clear x H
               | [ |- context[(?x <= least_upper_bound ?x ?y)%fixedpoint] ]
                 => replace (x <= least_upper_bound x y)%fixedpoint
                    with true by (symmetry; apply least_upper_bound_correct_l)
               | [ |- context[(?y <= least_upper_bound ?x ?y)%fixedpoint] ]
                 => replace (y <= least_upper_bound x y)%fixedpoint
                    with true by (symmetry; apply least_upper_bound_correct_r)
               | [ H : is_true true |- _ ] => clear H
               | [ H : is_true ?x |- context[?x] ]
                 => progress replace x with true by (symmetry; exact H)
               | [ H : is_true ?x, H' : context[?x] |- _ ]
                 => progress replace x with true in H' by (symmetry; exact H)
               | [ H : context[@state_beq ?A ?B ?x ?x] |- _ ]
                 => replace (@state_beq A B x x) with true in H by (symmetry; change (is_true (@state_beq A B x x)); reflexivity)
               | [ H : is_true (?R ?x ?y), H' : is_true (?R ?y ?z) |- _ ]
                 => unique pose proof (transitivity (R := R) H H' : is_true (R x z))
               | [ H : is_true (@state_le ?A ?B ?x ?y), H' : is_true (state_le ?y ?x) |- _ ]
                 => unique pose proof (@antisymmetry _ (@state_beq A B) _ (@state_le A B) _ x y H H' : is_true (state_beq x y))
               | [ |- context[is_true (negb ?x)] ]
                 => destruct x eqn:?; simpl; fold_is_true
               | _ => progress bool_congr_setoid
               | [ |- and _ _ ] => split
               end
      ).
  {
 unfold flip.
    eapply well_founded_subrelation; [ | eapply well_founded_prod_relationA with (eqA := state_beq) ];
      [ .. | eapply state_gt_wf | eapply state_gt_wf ].
    {
 intros x y H.
      unfold prod_relationA, flip, state_le, state in *.
      revert H.
      generalize (@state_lt _ fpldata0).
      generalize (@state_lt _ fpldata1).
      generalize (@state_beq _ fpldata0).
      generalize (@state_beq _ fpldata1).
      unfold state.
      clear.
 admit.
}
    {
 apply prod_relationA_Proper_from_Equivalence; try exact _; [].
      unfold flip; intros ??? x y H H'; subst.
      rewrite H; assumption.
}
 }
Defined.

Global Instance prod_fixedpoint_lattice' {prestate0 prestate1}
       {fpldata0 : grammar_fixedpoint_lattice_data prestate0}
       {fpldata1 : grammar_fixedpoint_lattice_data prestate1}
  : grammar_fixedpoint_lattice_data (lattice_for prestate0 * lattice_for prestate1)
  := prod_fixedpoint_lattice.

Section String.
  Context {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char}.

  Global Instance beq_subrelation_pointwise_iff {A} {R : relation A}
    : subrelation (beq ==> R)%signature (pointwise_relation String R).
  Proof.
    intros f g H x.
    specialize (H x x (reflexivity _)); assumption.
  Qed.
End String.
Import Fiat.Common.Instances.

Lemma simplify_bool_expr' a b (Himpl : is_true a -> is_true b)
  : (a || (b && negb a))%bool -> b.
admit.
Defined.

Section aidata.
  Context {Char : Type} {T T0 T1}
          {fpldata : grammar_fixedpoint_lattice_data T}
          {fpldata0 : grammar_fixedpoint_lattice_data T0}
          {fpldata1 : grammar_fixedpoint_lattice_data T1}.

  Definition prod_on_terminal
             (on_terminal0 : (Char -> bool) -> lattice_for T0)
             (on_terminal1 : (Char -> bool) -> lattice_for T1)
    : (Char -> bool) -> lattice_for (lattice_for T0 * lattice_for T1)
    := fun P => constant (on_terminal0 P, on_terminal1 P).

  Definition prod_on_nil_production
             (on_nil_production0 : lattice_for T0)
             (on_nil_production1 : lattice_for T1)
    : lattice_for (lattice_for T0 * lattice_for T1)
    := constant (on_nil_production0, on_nil_production1).

  Definition prod_precombine_production_dep
             (precombine_production0 : T0 -> T0 -> lattice_for T0)
             (precombine_production1 : lattice_for T0 -> lattice_for T0 -> T1 -> T1 -> lattice_for T1)
    : (lattice_for T0 * lattice_for T1) -> (lattice_for T0 * lattice_for T1) -> lattice_for (lattice_for T0 * lattice_for T1)
    := fun x y => constant (lattice_for_combine_production precombine_production0 (fst x) (fst y),
                            lattice_for_combine_production (precombine_production1 (fst x) (fst y)) (snd x) (snd y)).

  Definition prod_precombine_production_nondep
             (precombine_production0 : T0 -> T0 -> lattice_for T0)
             (precombine_production1 : T1 -> T1 -> lattice_for T1)
    : (lattice_for T0 * lattice_for T1) -> (lattice_for T0 * lattice_for T1) -> lattice_for (lattice_for T0 * lattice_for T1)
    := fun x y => constant (lattice_for_combine_production precombine_production0 (fst x) (fst y),
                            lattice_for_combine_production precombine_production1 (snd x) (snd y)).

  Global Instance prod_precombine_production_dep_Proper
         {precombine_production0 : T0 -> T0 -> lattice_for T0}
         {precombine_production1 : lattice_for T0 -> lattice_for T0 -> T1 -> T1 -> lattice_for T1}
         {HP0 : Proper (prestate_beq ==> prestate_beq ==> state_beq) precombine_production0}
         {HP1 : Proper (state_beq ==> state_beq ==> prestate_beq ==> prestate_beq ==> state_beq) precombine_production1}
    : Proper (prestate_beq ==> prestate_beq ==> state_beq) (prod_precombine_production_dep precombine_production0 precombine_production1).
admit.
Defined.

  Definition prod_aidata_dep
             (on_terminal0 : (Char -> bool) -> lattice_for T0)
             (on_nil_production0 : lattice_for T0)
             (precombine_production0 : T0 -> T0 -> lattice_for T0)
             (on_terminal1 : (Char -> bool) -> lattice_for T1)
             (on_nil_production1 : lattice_for T1)
             (precombine_production1 : lattice_for T0 -> lattice_for T0 -> T1 -> T1 -> lattice_for T1)
             (precombine_production0_Proper
              : Proper (prestate_beq ==> prestate_beq ==> state_beq) precombine_production0)
             (precombine_production1_Proper
              : Proper (state_beq ==> state_beq ==> prestate_beq ==> prestate_beq ==> state_beq) precombine_production1)
    : @AbstractInterpretation Char (lattice_for T0 * lattice_for T1) prod_fixedpoint_lattice'.
  Proof.
    refine {| on_terminal := prod_on_terminal on_terminal0 on_terminal1;
              on_nil_production := prod_on_nil_production on_nil_production0 on_nil_production1;
              precombine_production := prod_precombine_production_dep precombine_production0 precombine_production1 |}.
  Defined.

  Global Instance prod_precombine_production_dep_Proper_le
         {precombine_production0 : T0 -> T0 -> lattice_for T0}
         {precombine_production1 : lattice_for T0 -> lattice_for T0 -> T1 -> T1 -> lattice_for T1}
         {HP0 : Proper (prestate_le ==> prestate_le ==> state_le) precombine_production0}
         {HP1 : Proper (state_le ==> state_le ==> prestate_le ==> prestate_le ==> state_le) precombine_production1}
    : Proper (prestate_le ==> prestate_le ==> state_le) (prod_precombine_production_dep precombine_production0 precombine_production1).
admit.
Defined.

  Global Instance prod_precombine_production_nondep_dep_Proper_le
         {precombine_production0 : lattice_for T -> lattice_for T -> T0 -> T0 -> lattice_for T0}
         {precombine_production1 : lattice_for T -> lattice_for T -> T1 -> T1 -> lattice_for T1}
         {HP0 : Proper (state_le ==> state_le ==> prestate_le ==> prestate_le ==> state_le) precombine_production0}
         {HP1 : Proper (state_le ==> state_le ==> prestate_le ==> prestate_le ==> state_le) precombine_production1}
    : Proper (state_le ==> state_le ==> prestate_le ==> prestate_le ==> state_le) (fun x y => prod_precombine_production_nondep (precombine_production0 x y) (precombine_production1 x y)).
admit.
Defined.
End aidata.

Section aicdata.
  Context {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char}
          {T0 T1}
          {fpldata0 : grammar_fixedpoint_lattice_data T0}
          {fpldata1 : grammar_fixedpoint_lattice_data T1}
          (prerelated0 : Ensemble String -> T0 -> Prop)
          (prerelated1 : Ensemble String -> T1 -> Prop).

  Definition prod_prerelated : Ensemble String -> (lattice_for T0 * lattice_for T1) -> Prop
    := fun P st
       => lattice_for_related prerelated0 P (fst st)
          /\ lattice_for_related prerelated1 P (snd st).

  Local Ltac t_step :=
    idtac;
    match goal with
    | _ => intro
    | _ => progress unfold prod_prerelated, ensemble_least_upper_bound, ensemble_combine_production in *
    | _ => progress simpl in *
    | [ |- and _ True ] => split; [ | tauto ]
    | [ |- and True _ ] => split; [ tauto | ]
    | [ H : ?R _ _, H' : is_true _ |- _ ] => specialize (H _ _ H')
    | [ H : ?R _ _, H' : ?R' _ _ |- _ ] => specialize (H _ _ H')
    | _ => progress destruct_head and
    | [ H : is_true (Equality.prod_beq _ _ _ _) |- _ ]
      => unfold Equality.prod_beq in H;
         apply Bool.andb_true_iff in H
    | _ => progress fold_is_true
    | _ => progress destruct_head prod
    | _ => progress destruct_head ex
    | [ |- (lattice_for_related _ _ _ /\ lattice_for_related _ _ _)
           <-> (lattice_for_related _ _ _ /\ lattice_for_related _ _ _) ]
      => apply and_iff_iff_iff_Proper
    | [ H : is_true (state_beq ?x ?y) |- _ ]
      => lazymatch goal with
         | [ |- context[x] ]
           => fail
         | [ |- context[y] ]
           => fail
         | _ => clear dependent x
         end
    | _ => solve [ unfold not in *; eauto; destruct_head or; eauto ]
    | [ H : context[(_ ⊔ ⊥)%fixedpoint] |- _ ]
      => setoid_rewrite bottom_lub_r in H
    | [ H : context[(⊥ ⊔ _)%fixedpoint] |- _ ]
      => setoid_rewrite bottom_lub_l in H
    | _ => progress rewrite ?bottom_lub_r, ?bottom_lub_l
    | [ H : is_true (state_le ?x ?y) |- _ ] => is_var x; destruct x
    | [ H : is_true (state_le ?x ?y) |- _ ] => is_var y; destruct y
    | [ H : is_true (_ || (_ && negb _)) |- _ ]
      => apply simplify_bool_expr' in H; [ | unfold state_le; bool_congr_setoid; tauto ];
         try apply Bool.andb_true_iff in H
    | [ x : lattice_for (_ * _) |- _ ] => destruct x
    | [ x : lattice_for _ |- _ ] => destruct x
    | _ => congruence
    | _ => tauto
    | [ H : (_ ==> _)%signature (?f _) (?g _) |- _ ]
      => lazymatch goal with
         | [ |- context[f] ]
           => fail
         | [ |- context[g] ]
           => fail
         | _ => clear dependent f
         end
    | _ => progress setoid_subst_rel (beq ==> iff)%signature
    | [ |- and _ _ ] => split
    end.

  Local Ltac t := repeat t_step.

  Global Instance prod_prerelated_ext
         {prerelated0_ext : Proper ((beq ==> iff) ==> prestate_beq ==> iff) prerelated0}
         {prerelated1_ext : Proper ((beq ==> iff) ==> prestate_beq ==> iff) prerelated1}
    : Proper ((beq ==> iff) ==> prestate_beq ==> iff) prod_prerelated.
  Proof.
t.
Qed.

  Lemma prod_related_monotonic
         {related0_monotonic : forall s0 s1, (s0 <= s1)%fixedpoint -> forall v, lattice_for_related prerelated0 v s0 -> lattice_for_related prerelated0 v s1}
         {related1_monotonic : forall s0 s1, (s0 <= s1)%fixedpoint -> forall v, lattice_for_related prerelated1 v s0 -> lattice_for_related prerelated1 v s1}
    : forall s0 s1, (s0 <= s1)%fixedpoint -> forall v, lattice_for_related prod_prerelated v s0 -> lattice_for_related prod_prerelated v s1.
admit.
Defined.

  Lemma prod_lub_correct
        (lub0_correct : forall P1 st1,
            lattice_for_related prerelated0 P1 st1
            -> forall P2 st2,
              lattice_for_related prerelated0 P2 st2
              -> lattice_for_related prerelated0 (ensemble_least_upper_bound P1 P2) (st1 ⊔ st2)%fixedpoint)
        (lub1_correct : forall P1 st1,
            lattice_for_related prerelated1 P1 st1
            -> forall P2 st2,
              lattice_for_related prerelated1 P2 st2
              -> lattice_for_related prerelated1 (ensemble_least_upper_bound P1 P2) (st1 ⊔ st2)%fixedpoint)
    : forall P1 st1,
      lattice_for_related prod_prerelated P1 st1
      -> forall P2 st2,
        lattice_for_related prod_prerelated P2 st2
        -> lattice_for_related prod_prerelated (ensemble_least_upper_bound P1 P2) (st1 ⊔ st2)%fixedpoint.
admit.
Defined.

  Lemma prod_on_terminal_correct
        (on_terminal0 : (Char -> bool) -> lattice_for T0)
        (on_terminal1 : (Char -> bool) -> lattice_for T1)
        (on_terminal0_correct : forall P, lattice_for_related prerelated0 (ensemble_on_terminal P) (on_terminal0 P))
        (on_terminal1_correct : forall P, lattice_for_related prerelated1 (ensemble_on_terminal P) (on_terminal1 P))
    : forall P, lattice_for_related prod_prerelated (ensemble_on_terminal P) (prod_on_terminal on_terminal0 on_terminal1 P).
admit.
Defined.

  Lemma prod_on_nil_production_correct
        (on_nil_production0 : lattice_for T0)
        (on_nil_production1 : lattice_for T1)
        (on_nil_production0_correct : lattice_for_related prerelated0 ensemble_on_nil_production on_nil_production0)
        (on_nil_production1_correct : lattice_for_related prerelated1 ensemble_on_nil_production on_nil_production1)
    : lattice_for_related prod_prerelated ensemble_on_nil_production (prod_on_nil_production on_nil_production0 on_nil_production1).
admit.
Defined.

  Lemma prod_combine_production_dep_correct
        (precombine_production0 : T0 -> T0 -> lattice_for T0)
        (precombine_production1 : lattice_for T0 -> lattice_for T0 -> T1 -> T1 -> lattice_for T1)
        (combine_production0_correct : forall P1 st1,
            lattice_for_related prerelated0 P1 st1
            -> forall P2 st2,
              lattice_for_related prerelated0 P2 st2
              -> lattice_for_related prerelated0 (ensemble_combine_production P1 P2) (lattice_for_combine_production precombine_production0 st1 st2))
        (combine_production1_correct : forall P1 st1 st10,
            lattice_for_related prerelated0 P1 st10
            -> lattice_for_related prerelated1 P1 st1
            -> forall P2 st2 st20,
              lattice_for_related prerelated0 P2 st20
              -> lattice_for_related prerelated1 P2 st2
              -> lattice_for_related prerelated1 (ensemble_combine_production P1 P2) (lattice_for_combine_production (precombine_production1 st10 st20) st1 st2))
    : forall P1 st1,
      lattice_for_related prod_prerelated P1 st1
      -> forall P2 st2,
        lattice_for_related prod_prerelated P2 st2
        -> lattice_for_related prod_prerelated (ensemble_combine_production P1 P2) (lattice_for_combine_production (prod_precombine_production_dep precombine_production0 precombine_production1) st1 st2).
admit.
Defined.

  Lemma prod_combine_production_nondep_correct_specific
        (precombine_production0 : T0 -> T0 -> lattice_for T0)
        (precombine_production1 : T1 -> T1 -> lattice_for T1)
        P1 st1
        (Hrel1 : lattice_for_related prod_prerelated P1 st1)
        P2 st2
        (Hrel2 : lattice_for_related prod_prerelated P2 st2)
        (combine_production0_correct
         : forall st1v,
            st1 = constant st1v
            -> forall st2v,
              st2 = constant st2v
              -> lattice_for_related prerelated0 (ensemble_combine_production P1 P2) (lattice_for_combine_production precombine_production0 (fst st1v) (fst st2v)))
        (combine_production1_correct
         : forall st1v,
            st1 = constant st1v
            -> forall st2v,
              st2 = constant st2v
              -> lattice_for_related prerelated1 (ensemble_combine_production P1 P2) (lattice_for_combine_production precombine_production1 (snd st1v) (snd st2v)))
    : lattice_for_related prod_prerelated (ensemble_combine_production P1 P2) (lattice_for_combine_production (prod_precombine_production_nondep precombine_production0 precombine_production1) st1 st2).
admit.
Defined.
End aicdata.

Global Arguments prod_prerelated_ext {_ _ _ _ T0 T1 _ _ prerelated0 prerelated1} _ _ _ _ _ _ _ _.
Global Arguments prod_related_monotonic {_ _ T0 T1 _ _ prerelated0 prerelated1} _ _ _ _ _ _ _.
Global Arguments prod_lub_correct {_ _ T0 T1 _ _ prerelated0 prerelated1} _ _ _ _ _ _ _ _.
Global Arguments prod_on_terminal_correct {_ _ _ T0 T1 prerelated0 prerelated1 on_terminal0 on_terminal1} _ _ _.
Global Arguments prod_on_nil_production_correct {_ _ T0 T1 prerelated0 prerelated1 on_nil_production0 on_nil_production1} _ _.
Global Arguments prod_precombine_production_dep_Proper_le {T0 T1 _ _ precombine_production0 precombine_production1} _ _ _ _ _ _ _ _.
Global Arguments prod_combine_production_dep_correct {_ _ _ T0 T1 prerelated0 prerelated1 precombine_production0 precombine_production1} _ _ _ _ _ _ _ _.
Global Arguments prod_precombine_production_nondep_dep_Proper_le {T T0 T1 _ _ _ precombine_production0 precombine_production1} _ _ _ _ _ _ _ _ _ _ _ _ _ _.

Inductive nonemptyT := nonempty | could_be_empty.

Global Instance might_be_empty_lattice : grammar_fixedpoint_lattice_data nonemptyT.
admit.
Defined.

Global Instance might_be_empty_aidata {Char} : @AbstractInterpretation Char nonemptyT _.
admit.
Defined.

Section correctness.
  Context {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char}.

  Definition might_be_empty_accurate
             (P : String -> Prop) (nonemptyv : nonemptyT)
    : Prop
    := nonemptyv = nonempty -> forall str, P str -> length str <> 0.

  Global Instance might_be_empty_aicdata
    : AbstractInterpretationCorrectness might_be_empty_accurate.
admit.
Defined.
End correctness.

Definition might_be_emptyT := lattice_for nonemptyT.
Coercion collapse_might_be_empty (x : might_be_emptyT) : bool
  := match x with
     | ⊤ => true
     | constant could_be_empty => true
     | constant nonempty => false
     | ⊥ => false
     end.
Local Open Scope string_like_scope.

Section forall_chars.
  Context {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char}.

  Definition forall_chars (str : String) (P : Char -> Prop)
    := forall n ch,
         take 1 (drop n str) ~= [ ch ]
         -> P ch.

  Global Instance forall_chars_Proper
  : Proper (beq ==> pointwise_relation _ impl ==> impl) forall_chars.
admit.
Defined.

  Global Instance forall_chars_Proper_flip
  : Proper (beq ==> pointwise_relation _ (flip impl) ==> flip impl) forall_chars.
admit.
Defined.

  Global Opaque forall_chars.

  Lemma forall_chars_get (str : String) P
  : forall_chars str P <-> (forall n ch, get n str = Some ch -> P ch).
admit.
Defined.
End forall_chars.

Section for_first_char.
  Context {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char}.

  Definition for_first_char (str : String) (P : Char -> Prop)
    := forall ch,
         take 1 str ~= [ ch ]
         -> P ch.

  Lemma for_first_char_True (str : String) (P : _ -> Prop) (p : forall ch, P ch)
  : for_first_char str P.
admit.
Defined.
End for_first_char.

Section for_last_char.
  Context {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char}.

  Definition for_last_char (str : String) (P : Char -> Prop)
    := forall ch,
         drop (pred (length str)) str ~= [ ch ]
         -> P ch.

  Lemma for_last_char_True (str : String) (P : _ -> Prop) (p : forall ch, P ch)
  : for_last_char str P.
admit.
Defined.
End for_last_char.

Import Coq.MSets.MSetPositive.
Import Fiat.Common.LogicFacts.

Definition all_possible_ascii' : PositiveSet.t
  := List.fold_right
       PositiveSet.add
       PositiveSet.empty
       (List.map (fun x => BinPos.Pos.of_nat (S x))
                 (Operations.List.up_to (S (Ascii.nat_of_ascii (Ascii.Ascii true true true true true true true true))))).

Definition all_possible_ascii : PositiveSet.t
  := Eval compute in all_possible_ascii'.

Definition pos_of_ascii (x : Ascii.ascii) : BinNums.positive
  := match Ascii.N_of_ascii x with
     | BinNums.N0 => max_ascii
     | BinNums.Npos x => x
     end.

Lemma In_all ch
  : PositiveSet.In (pos_of_ascii ch) all_possible_ascii.
admit.
Defined.

Definition all_but (P : Ascii.ascii -> bool) : PositiveSet.t
  := PositiveSet.filter (fun n => negb (P (Ascii.ascii_of_pos n))) all_possible_ascii.

  Definition possible_terminals_prestate
    := (@state _ might_be_empty_lattice
        * lattice_for
            (lattice_for
               (@state _ positive_set_fpdata
                * @state _ positive_set_fpdata  )
             * @state _ positive_set_fpdata  ))%type.

  Global Instance possible_terminals_prestate_lattice : grammar_fixedpoint_lattice_data possible_terminals_prestate
    := _.

  Global Instance possible_terminals_aidata : @AbstractInterpretation Ascii.ascii possible_terminals_prestate _.
  Proof.
    refine (@prod_aidata_dep
              _ _ _ _ _
              on_terminal
              (@on_nil_production Ascii.ascii _ _ might_be_empty_aidata)
              (@precombine_production Ascii.ascii _ _ might_be_empty_aidata)
              (prod_on_terminal
                 (prod_on_terminal
                    (fun P => constant (all_but P))
                    (fun P => constant (all_but P)))
                 (fun P => constant (all_but P)))
              (prod_on_nil_production
                 (prod_on_nil_production
                    (constant all_possible_ascii)
                    (constant all_possible_ascii))
                 (constant all_possible_ascii))
              (fun xmbe ymbe
               => prod_precombine_production_nondep
                    (prod_precombine_production_nondep
                       (fun x' y'
                        => constant (if collapse_might_be_empty xmbe
                                     then PositiveSet.inter x' y'
                                     else x'))
                       (fun x' y'
                        => constant (if collapse_might_be_empty ymbe
                                     then PositiveSet.inter x' y'
                                     else y')))
                    (fun x' y'
                     => constant (PositiveSet.inter x' y')))
              _ _).
    intros x0 y0 H0 x1 y1 H1 x2 y2 H2 x3 y3 H3.
    repeat match goal with
           | [ H : is_true (state_beq ?x ?y) |- context[collapse_might_be_empty ?x] ]
             => replace (collapse_might_be_empty x)
                with (collapse_might_be_empty y)
               by (rewrite H; reflexivity);
                  clear x H
           end.
    repeat first [ eapply @prod_precombine_production_nondep_Proper
                 | eassumption
                 | match goal with
                   | [ |- context[collapse_might_be_empty ?v] ]
                     => destruct (collapse_might_be_empty v)
                   end ];
      clear; admit.
  Defined.

Section correctness.
  Context {HSLM : StringLikeMin Ascii.ascii} {HSL : StringLike Ascii.ascii} {HSLP : StringLikeProperties Ascii.ascii}.

  Definition possible_accurate
    : forall (P : String -> Prop) (st : possible_terminals_prestate), Prop
    := prod_prerelated
         might_be_empty_accurate
         (prod_prerelated
            (prod_prerelated
               (fun P st
                => forall str, P str -> for_first_char str (fun ch => ~PositiveSet.In (pos_of_ascii ch) st))
               (fun P st
                => forall str, P str -> for_last_char str (fun ch => ~PositiveSet.In (pos_of_ascii ch) st)))
            (fun P st
             => forall str, P str -> forall_chars str (fun ch => ~PositiveSet.In (pos_of_ascii ch) st))).

  Global Program Instance possible_aicdata
    : AbstractInterpretationCorrectness possible_accurate
    := { prerelated_ext
         := prod_prerelated_ext
              (@prerelated_ext Ascii.ascii _ _ _ _ _ _ _ might_be_empty_aicdata)
              (prod_prerelated_ext (prod_prerelated_ext _ _) _);
         related_monotonic
         := prod_related_monotonic
              (@related_monotonic Ascii.ascii _ _ _ _ _ _ _ might_be_empty_aicdata)
              (prod_related_monotonic (prod_related_monotonic _ _) _);
         lub_correct
         := prod_lub_correct
              (@lub_correct Ascii.ascii _ _ _ _ _ _ _ might_be_empty_aicdata)
              (prod_lub_correct (prod_lub_correct _ _) _);
         on_terminal_correct
         := prod_on_terminal_correct
              (@on_terminal_correct Ascii.ascii _ _ _ _ _ _ _ might_be_empty_aicdata)
              (prod_on_terminal_correct (prod_on_terminal_correct _ _) _);
         on_nil_production_correct
         := prod_on_nil_production_correct
              (@on_nil_production_correct Ascii.ascii _ _ _ _ _ _ _ might_be_empty_aicdata)
              (prod_on_nil_production_correct (prod_on_nil_production_correct _ _) _);
         precombine_production_Proper_le
         := prod_precombine_production_dep_Proper_le
              (@precombine_production_Proper_le Ascii.ascii _ _ _ _ _ _ _ might_be_empty_aicdata)
              (prod_precombine_production_nondep_dep_Proper_le (prod_precombine_production_nondep_dep_Proper_le _ _) _);
         combine_production_correct
         := prod_combine_production_dep_correct
              (@combine_production_correct Ascii.ascii _ _ _ _ _ _ _ might_be_empty_aicdata)
              (fun P1 st1 st10 R10 R1 P2 st2 st20 R20 R2
               => prod_combine_production_nondep_correct_specific
                    _ _ _ _ _ _ _ _
                    (fun st1v Hst1v st2v Hst2v
                     => prod_combine_production_nondep_correct_specific
                          _ _ _ _ _ _ _ _ _ _)
                    _)
       }.
Admit Obligations.

End correctness.

Definition possible_data (G : pregrammar' Ascii.ascii)
  := @fold_grammar_data _ _ _ possible_terminals_aidata G.
Existing Class possible_data.

Definition possible_characters_result := PositiveSet.t.
Record possible_result :=
  { might_be_empty_of_pr : bool;
    possible_first_characters_of_pr : possible_characters_result;
    possible_last_characters_of_pr : possible_characters_result;
    all_possible_characters_of_pr : possible_characters_result }.

Definition make_all_possible_result (negated_set : lattice_for PositiveSet.t) : possible_characters_result
  := match negated_set with
     | ⊤ => all_possible_ascii
     | constant v' => PositiveSet.filter (fun ch => negb (PositiveSet.mem ch v')) all_possible_ascii
     | ⊥ => PositiveSet.empty
     end.

Definition norm_lattice_prod {A B} (x : lattice_for (lattice_for A * lattice_for B)) : lattice_for A * lattice_for B
  := match x with
     | ⊤ => (⊤, ⊤)
     | constant v => v
     | ⊥ => (⊥, ⊥)
     end.

Definition collapse_to_possible_result (x : lattice_for possible_terminals_prestate) : possible_result
  := let x := norm_lattice_prod x in
     let x0 := fst x in
     let x123 := norm_lattice_prod (snd x) in
     let '(x12, x3) := (fst x123, snd x123) in
     let x12 := norm_lattice_prod x12 in
     let '(x1, x2) := (fst x12, snd x12) in
     {| might_be_empty_of_pr := collapse_might_be_empty x0;
        possible_first_characters_of_pr := make_all_possible_result x1;
        possible_last_characters_of_pr := make_all_possible_result x2;
        all_possible_characters_of_pr := make_all_possible_result x3 |}.

Local Declare Reduction opt_possible :=
  cbv [FromAbstractInterpretationDefinitions.fixedpoint_by_abstract_interpretation Definitions.prestate Definitions.lattice_data Fix.lookup_state].

Section defs.
  Context (G : pregrammar' Ascii.ascii)
          {pdata : possible_data G}.
  Local Hint Immediate (compile_item_data_of_abstract_interpretation G) : typeclass_instances.

  Definition all_possible_characters_of_nt
    : String.string -> possible_characters_result
    := Eval opt_possible in fun nt => all_possible_characters_of_pr (collapse_to_possible_result (lookup_state pdata (@of_nonterminal _ (@rdp_list_predata _ G) nt))).
  Definition unfold_all_possible_characters_of_nt
    : all_possible_characters_of_nt = fun nt => all_possible_characters_of_pr (collapse_to_possible_result (lookup_state pdata (@of_nonterminal _ (@rdp_list_predata _ G) nt)))
    := eq_refl.

  Definition might_be_empty_of_pr_nt
    : String.string -> bool
    := Eval opt_possible in fun nt => might_be_empty_of_pr (collapse_to_possible_result (lookup_state pdata (@of_nonterminal _ (@rdp_list_predata _ G) nt))).
  Definition unfold_might_be_empty_of_pr_nt
    : might_be_empty_of_pr_nt = fun nt => might_be_empty_of_pr (collapse_to_possible_result (lookup_state pdata (@of_nonterminal _ (@rdp_list_predata _ G) nt)))
    := eq_refl.

  Definition possible_first_characters_of_nt
    : String.string -> possible_characters_result
    := Eval opt_possible in fun nt => possible_first_characters_of_pr (collapse_to_possible_result (lookup_state pdata (@of_nonterminal _ (@rdp_list_predata _ G) nt))).
  Definition unfold_possible_first_characters_of_nt
    : possible_first_characters_of_nt = fun nt => possible_first_characters_of_pr (collapse_to_possible_result (lookup_state pdata (@of_nonterminal _ (@rdp_list_predata _ G) nt)))
    := eq_refl.

  Definition possible_last_characters_of_nt
    : String.string -> possible_characters_result
    := Eval opt_possible in fun nt => possible_last_characters_of_pr (collapse_to_possible_result (lookup_state pdata (@of_nonterminal _ (@rdp_list_predata _ G) nt))).
  Definition unfold_possible_last_characters_of_nt
    : possible_last_characters_of_nt = fun nt => possible_last_characters_of_pr (collapse_to_possible_result (lookup_state pdata (@of_nonterminal _ (@rdp_list_predata _ G) nt)))
    := eq_refl.

  Definition all_possible_characters_of_production
    : production Ascii.ascii -> possible_characters_result
    := Eval opt_possible in fun ps => all_possible_characters_of_pr (collapse_to_possible_result (fold_production' (lookup_state pdata) (opt.compile_production ps))).
  Definition unfold_all_possible_characters_of_production
    : all_possible_characters_of_production = fun ps => all_possible_characters_of_pr (collapse_to_possible_result (fold_production' (lookup_state pdata) (opt.compile_production ps)))
    := eq_refl.

  Definition might_be_empty_of_pr_production
    : production Ascii.ascii -> bool
    := Eval opt_possible in fun ps => might_be_empty_of_pr (collapse_to_possible_result (fold_production' (lookup_state pdata) (opt.compile_production ps))).
  Definition unfold_might_be_empty_of_pr_production
    : might_be_empty_of_pr_production = fun ps => might_be_empty_of_pr (collapse_to_possible_result (fold_production' (lookup_state pdata) (opt.compile_production ps)))
    := eq_refl.

  Definition possible_first_characters_of_production
    : production Ascii.ascii -> possible_characters_result
    := Eval opt_possible in fun ps => possible_first_characters_of_pr (collapse_to_possible_result (fold_production' (lookup_state pdata) (opt.compile_production ps))).
  Definition unfold_possible_first_characters_of_production
    : possible_first_characters_of_production = fun ps => possible_first_characters_of_pr (collapse_to_possible_result (fold_production' (lookup_state pdata) (opt.compile_production ps)))
    := eq_refl.

  Definition possible_last_characters_of_production
    : production Ascii.ascii -> possible_characters_result
    := Eval opt_possible in fun ps => possible_last_characters_of_pr (collapse_to_possible_result (fold_production' (lookup_state pdata) (opt.compile_production ps))).
  Definition unfold_possible_last_characters_of_production
    : possible_last_characters_of_production = fun ps => possible_last_characters_of_pr (collapse_to_possible_result (fold_production' (lookup_state pdata) (opt.compile_production ps)))
    := eq_refl.
End defs.
Global Arguments all_possible_characters_of_nt G {_} _.

Section correctness_lemmas.
  Context {HSLM : StringLikeMin Ascii.ascii}
          {HSL : StringLike Ascii.ascii}
          {HSLP : StringLikeProperties Ascii.ascii}
          (G : pregrammar' Ascii.ascii)
          {pdata : possible_data G}
          (nt : String.string)
          (ps : production Ascii.ascii)
          (str : String).

  Local Ltac pre_correct_t :=
    rewrite
      ?unfold_all_possible_characters_of_nt,
    ?unfold_might_be_empty_of_pr_nt,
    ?unfold_possible_first_characters_of_nt,
    ?unfold_possible_last_characters_of_nt,
    ?unfold_all_possible_characters_of_production,
    ?unfold_might_be_empty_of_pr_production,
    ?unfold_possible_first_characters_of_production,
    ?unfold_possible_last_characters_of_production;
    try (let x := match goal with
                  | [ |- ?v = _ ] => head v
                  end in
         unfold x).

  Local Ltac correct_t_step :=
    idtac;
    match goal with
    | _ => assumption
    | _ => tauto
    | [ |- ?R ?x ?x ] => reflexivity
    | [ H : ?x = ?x -> _ |- _ ] => specialize (H eq_refl)
    | [ |- context[fold_production' (lookup_state fgd_fold_grammar) _] ]
      => setoid_rewrite fgd_fold_grammar_correct
    | _ => rewrite fgd_fold_grammar_correct
    | [ p : parse_of_item _ _ _ |- context[@fixedpoint_by_abstract_interpretation _ _ _ ?aidata ?G] ]
      => apply (@fold_grammar_correct_item _ _ _ _ _ _ aidata _ _ _ _ eq_refl) in p
    | [ p : parse_of_production _ _ _ |- context[@fixedpoint_by_abstract_interpretation _ _ _ ?aidata ?G] ]
      => apply (@fold_grammar_correct_production _ _ _ _ _ _ aidata _ _ _ _ eq_refl) in p
    | [ p : parse_of _ _ _ |- context[@fixedpoint_by_abstract_interpretation _ _ _ ?aidata ?G] ]
      => apply (@fold_grammar_correct _ _ _ _ _ _ aidata _ _ _ _ eq_refl) in p
    | [ H : context[lookup_state _ ?nt] |- context[lookup_state _ ?nt'] ]
      => lazymatch constr:((nt, nt')) with
         | (opt.compile_nonterminal _, of_nonterminal _)
           => change nt with nt' in *
         end
    | [ |- context G[lookup_state ?g ?nt] ]
      =>
      let G' := context G[lookup_state g nt] in
      change G';
      destruct (lookup_state g nt) eqn:?
    | [ |- context[fold_production' ?f ?ps] ]
      => destruct (fold_production' f ps) eqn:?
    | _ => progress simpl in *
    | _ => progress destruct_head ex
    | _ => progress destruct_head and
    | _ => progress destruct_head prod
    | _ => progress unfold possible_accurate, possible_terminals_prestate, state, prod_prerelated, lattice_for_related, collapse_might_be_empty, might_be_empty_accurate, related, norm_lattice_prod, make_all_possible_result in *
    | [ H : ?x = _, H' : context[?x] |- _ ] => rewrite H in H'
    | [ |- context[match ?x with _ => _ end] ] => is_var x; destruct x
    | _ => solve [ exfalso; unfold not in *; eauto with nocore ]
    | [ |- context[PositiveSet.In _ all_possible_ascii] ]
      => first [ rewrite forall_chars_get | apply for_first_char_True | apply for_last_char_True ];
         setoid_rewrite (fun v => True_iff (In_all v)); constructor
    | [ |- context[PositiveSet.In _ all_possible_ascii] ]
      => setoid_rewrite (fun v => True_iff (In_all v))
    | [ H : ?P _, H' : forall str, ?P str -> _ |- _ ] => unique pose proof (H' _ H)
    | _ => progress PositiveSetExtensions.push_In
    | _ => progress PositiveSetExtensions.to_caps
    | _ => progress setoid_rewrite_logic
    end.
  Local Ltac correct_t := try pre_correct_t; repeat correct_t_step.

  Lemma all_possible_characters_of_item_nt
        (p : parse_of_item G str (NonTerminal nt))
    : forall_chars str (fun ch => PositiveSet.In (pos_of_ascii ch) (all_possible_characters_of_nt G nt)).
  Proof.
    correct_t.
    eapply forall_chars_Proper; [ reflexivity | intros ?? | try eassumption ].
