
(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "-deprecated-native-compiler-option" "-native-compiler" "no" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/metacoq/utils/theories" "MetaCoq.Utils" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/metacoq/common/theories" "MetaCoq.Common" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/metacoq/pcuic/theories" "MetaCoq.PCUIC" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Equations" "Equations" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-top" "Top.bug_01") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 406 lines to 79 lines, then from 92 lines to 4252 lines, then from 4249 lines to 89 lines, then from 102 lines to 901 lines, then from 906 lines to 127 lines, then from 140 lines to 1768 lines, then from 1773 lines to 2117 lines, then from 2107 lines to 389 lines, then from 402 lines to 1300 lines, then from 1304 lines to 550 lines, then from 563 lines to 2362 lines, then from 2361 lines to 555 lines, then from 568 lines to 1055 lines, then from 1060 lines to 562 lines, then from 575 lines to 2873 lines, then from 2875 lines to 659 lines, then from 672 lines to 2567 lines, then from 2571 lines to 2380 lines, then from 2352 lines to 834 lines, then from 847 lines to 1437 lines, then from 1440 lines to 958 lines, then from 971 lines to 2213 lines, then from 2212 lines to 973 lines, then from 986 lines to 1399 lines, then from 1404 lines to 976 lines, then from 989 lines to 2449 lines, then from 2450 lines to 1233 lines, then from 1246 lines to 1504 lines, then from 1509 lines to 1251 lines, then from 1268 lines to 1242 lines, then from 1255 lines to 3288 lines, then from 3289 lines to 1428 lines, then from 1441 lines to 2827 lines, then from 2828 lines to 1575 lines, then from 1579 lines to 1561 lines, then from 1574 lines to 1665 lines, then from 1670 lines to 1563 lines, then from 1576 lines to 2146 lines, then from 2148 lines to 1568 lines, then from 1581 lines to 4426 lines, then from 4402 lines to 2092 lines, then from 2082 lines to 1899 lines, then from 1912 lines to 2790 lines, then from 2792 lines to 1979 lines, then from 1992 lines to 2585 lines, then from 2590 lines to 2047 lines, then from 2060 lines to 2192 lines, then from 2197 lines to 2061 lines, then from 2074 lines to 2386 lines, then from 2389 lines to 2340 lines, then from 2346 lines to 2080 lines, then from 2093 lines to 6088 lines, then from 6083 lines to 2114 lines, then from 2127 lines to 2424 lines, then from 2426 lines to 2123 lines, then from 2136 lines to 3670 lines, then from 3668 lines to 3051 lines, then from 3058 lines to 2143 lines, then from 2156 lines to 2332 lines, then from 2337 lines to 2154 lines, then from 2167 lines to 2395 lines, then from 2397 lines to 2155 lines, then from 2168 lines to 2315 lines, then from 2319 lines to 2161 lines, then from 2174 lines to 2729 lines, then from 2734 lines to 2214 lines, then from 2227 lines to 2395 lines, then from 2400 lines to 2216 lines, then from 2229 lines to 2511 lines, then from 2515 lines to 2425 lines, then from 2428 lines to 2288 lines, then from 2301 lines to 2555 lines, then from 2557 lines to 2307 lines, then from 2320 lines to 2386 lines, then from 2391 lines to 2308 lines, then from 2321 lines to 2383 lines, then from 2388 lines to 2307 lines, then from 2320 lines to 2494 lines, then from 2499 lines to 2347 lines, then from 2360 lines to 2469 lines, then from 2474 lines to 2369 lines, then from 2382 lines to 2926 lines, then from 2932 lines to 2892 lines, then from 2906 lines to 3068 lines, then from 3074 lines to 3025 lines *)
(* coqc version 8.20+alpha compiled with OCaml 4.09.0
   coqtop version c74786003383:/builds/coq/coq/_build/default,(HEAD detached at f7aaed9) (f7aaed98877033e8fd8c34e63e9c7269aff2f1c7)
   Modules that could not be inlined: Equations.Prop.DepElim
   Expected coqc runtime on this file: 1.921 sec *)
Require Coq.Init.Ltac.
Require Coq.Floats.FloatAxioms.
Require Coq.Bool.Bool.
Require Coq.Classes.CRelationClasses.
Require Coq.Classes.RelationClasses.
Require Coq.btauto.Btauto.
Require Coq.ssr.ssrbool.
Require Coq.ssr.ssreflect.
Require Coq.MSets.MSetAVL.
Require Coq.MSets.MSetList.
Require Coq.Program.Tactics.
Require Coq.Unicode.Utf8_core.
Require Coq.extraction.Extraction.
Require Equations.Init.
Require Equations.Signature.
Require Equations.CoreTactics.
Require Coq.Relations.Relation_Definitions.
Require Equations.Prop.Logic.
Require Equations.Prop.Classes.
Require Equations.Prop.EqDec.
Require Equations.Prop.DepElim.
Require Coq.Structures.OrderedType.

Module Export AdmitTactic.
Module Import LocalFalse.
Inductive False : Prop := .
End LocalFalse.
Axiom proof_admitted : False.
Import Coq.Init.Ltac.
Tactic Notation "admit" := abstract case proof_admitted.
End AdmitTactic.

Module Export MetaCoq_DOT_Common_DOT_config_WRAPPED.
Module Export config.
Import Coq.Bool.Bool.
Import Coq.Classes.RelationClasses.
Import Coq.btauto.Btauto.
Import Coq.ssr.ssreflect.
Import Coq.ssr.ssrbool.

Class checker_flags := {
   

   
  check_univs : bool ;

   
  prop_sub_type : bool ;

   
  indices_matter : bool ;

   
  lets_in_constructor_types : bool
}.
Local Instance default_checker_flags : checker_flags. exact ({|
  check_univs := true ;
  prop_sub_type := true;
  indices_matter := false;
  lets_in_constructor_types := true
|}). Defined.
Local Instance type_in_type : checker_flags. exact ({|
  check_univs := false ;
  prop_sub_type := true;
  indices_matter := false;
  lets_in_constructor_types := true
|}). Defined.
Local Instance extraction_checker_flags : checker_flags. exact ({|
  check_univs := true ;
  prop_sub_type := false;
  indices_matter := false;
  lets_in_constructor_types := false
|}). Defined.
#[local] Definition impl (cf1 cf2 : checker_flags) : bool. exact (implb cf2.(@check_univs) cf1.(@check_univs)
     && implb cf1.(@prop_sub_type) cf2.(@prop_sub_type)
     && implb cf2.(@indices_matter) cf1.(@indices_matter)
     && implb cf1.(@lets_in_constructor_types) cf2.(@lets_in_constructor_types)). Defined.

#[local] Definition impl_reflb cf : impl cf cf = true.
Admitted.
#[local] Definition impl_refl : Reflexive impl. exact (impl_reflb). Defined.
#[local] Definition impl_crefl : CRelationClasses.Reflexive impl. exact (impl_reflb). Defined.
#[local] Definition impl_trans : Transitive impl.
Admitted.
#[local] Definition impl_ctrans : CRelationClasses.Transitive impl. exact (impl_trans). Defined.
#[global] Existing Instances
  impl_refl impl_crefl
  impl_trans impl_ctrans
| 100.
Definition laxest_checker_flags : checker_flags. exact ({|
  check_univs := false ;
  prop_sub_type := true;
  indices_matter := false;
  lets_in_constructor_types := true
|}). Defined.
Definition strictest_checker_flags : checker_flags. exact ({|
  check_univs := true ;
  prop_sub_type := false;
  indices_matter := true;
  lets_in_constructor_types := false
|}). Defined.

Lemma laxest_checker_flags_laxest : forall cf, impl cf laxest_checker_flags.
Admitted.

Lemma strictest_checker_flags_strictest : forall cf, impl strictest_checker_flags cf.
Admitted.
Definition union_checker_flags (cf1 cf2 : checker_flags) : checker_flags. exact ({| check_univs := andb cf2.(@check_univs) cf1.(@check_univs)
     ; prop_sub_type := orb cf1.(@prop_sub_type) cf2.(@prop_sub_type)
     ; indices_matter := andb cf2.(@indices_matter) cf1.(@indices_matter)
     ; lets_in_constructor_types := orb cf1.(@lets_in_constructor_types) cf2.(@lets_in_constructor_types) |}). Defined.
Definition inter_checker_flags (cf1 cf2 : checker_flags) : checker_flags. exact ({| check_univs := orb cf2.(@check_univs) cf1.(@check_univs)
     ; prop_sub_type := andb cf1.(@prop_sub_type) cf2.(@prop_sub_type)
     ; indices_matter := orb cf2.(@indices_matter) cf1.(@indices_matter)
     ; lets_in_constructor_types := andb cf1.(@lets_in_constructor_types) cf2.(@lets_in_constructor_types) |}). Defined.

Lemma union_checker_flags_spec cf1 cf2 (cf' := union_checker_flags cf1 cf2)
  : impl cf1 cf' /\ impl cf2 cf' /\ (forall cf'', impl cf1 cf'' -> impl cf2 cf'' -> impl cf' cf'').
Admitted.

Lemma inter_checker_flags_spec cf1 cf2 (cf' := inter_checker_flags cf1 cf2)
  : impl cf' cf1 /\ impl cf' cf2 /\ (forall cf'', impl cf'' cf1 -> impl cf'' cf2 -> impl cf'' cf').
Admitted.

End config.

End MetaCoq_DOT_Common_DOT_config_WRAPPED.
Module Export MetaCoq_DOT_Common_DOT_config.
Module Export MetaCoq.
Module Export Common.
Module Export config.
Include MetaCoq_DOT_Common_DOT_config_WRAPPED.config.
End config.

End Common.

End MetaCoq.

End MetaCoq_DOT_Common_DOT_config.
Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.
Module Export ByteCompare.
Import Coq.Strings.Byte.
Import Coq.NArith.BinNat.

Module Export ByteN.
Definition N1 := 1%N.
Definition N2 := 2%N.
Definition N3 := 3%N.
Definition N4 := 4%N.
Definition N5 := 5%N.
Definition N6 := 6%N.
Definition N7 := 7%N.
Definition N8 := 8%N.
Definition N9 := 9%N.
Definition N10 := 10%N.
Definition N11 := 11%N.
Definition N12 := 12%N.
Definition N13 := 13%N.
Definition N14 := 14%N.
Definition N15 := 15%N.
Definition N16 := 16%N.
Definition N17 := 17%N.
Definition N18 := 18%N.
Definition N19 := 19%N.
Definition N20 := 20%N.
Definition N21 := 21%N.
Definition N22 := 22%N.
Definition N23 := 23%N.
Definition N24 := 24%N.
Definition N25 := 25%N.
Definition N26 := 26%N.
Definition N27 := 27%N.
Definition N28 := 28%N.
Definition N29 := 29%N.
Definition N30 := 30%N.
Definition N31 := 31%N.
Definition N32 := 32%N.
Definition N33 := 33%N.
Definition N34 := 34%N.
Definition N35 := 35%N.
Definition N36 := 36%N.
Definition N37 := 37%N.
Definition N38 := 38%N.
Definition N39 := 39%N.
Definition N40 := 40%N.
Definition N41 := 41%N.
Definition N42 := 42%N.
Definition N43 := 43%N.
Definition N44 := 44%N.
Definition N45 := 45%N.
Definition N46 := 46%N.
Definition N47 := 47%N.
Definition N48 := 48%N.
Definition N49 := 49%N.
Definition N50 := 50%N.
Definition N51 := 51%N.
Definition N52 := 52%N.
Definition N53 := 53%N.
Definition N54 := 54%N.
Definition N55 := 55%N.
Definition N56 := 56%N.
Definition N57 := 57%N.
Definition N58 := 58%N.
Definition N59 := 59%N.
Definition N60 := 60%N.
Definition N61 := 61%N.
Definition N62 := 62%N.
Definition N63 := 63%N.
Definition N64 := 64%N.
Definition N65 := 65%N.
Definition N66 := 66%N.
Definition N67 := 67%N.
Definition N68 := 68%N.
Definition N69 := 69%N.
Definition N70 := 70%N.
Definition N71 := 71%N.
Definition N72 := 72%N.
Definition N73 := 73%N.
Definition N74 := 74%N.
Definition N75 := 75%N.
Definition N76 := 76%N.
Definition N77 := 77%N.
Definition N78 := 78%N.
Definition N79 := 79%N.
Definition N80 := 80%N.
Definition N81 := 81%N.
Definition N82 := 82%N.
Definition N83 := 83%N.
Definition N84 := 84%N.
Definition N85 := 85%N.
Definition N86 := 86%N.
Definition N87 := 87%N.
Definition N88 := 88%N.
Definition N89 := 89%N.
Definition N90 := 90%N.
Definition N91 := 91%N.
Definition N92 := 92%N.
Definition N93 := 93%N.
Definition N94 := 94%N.
Definition N95 := 95%N.
Definition N96 := 96%N.
Definition N97 := 97%N.
Definition N98 := 98%N.
Definition N99 := 99%N.
Definition N100 := 100%N.
Definition N101 := 101%N.
Definition N102 := 102%N.
Definition N103 := 103%N.
Definition N104 := 104%N.
Definition N105 := 105%N.
Definition N106 := 106%N.
Definition N107 := 107%N.
Definition N108 := 108%N.
Definition N109 := 109%N.
Definition N110 := 110%N.
Definition N111 := 111%N.
Definition N112 := 112%N.
Definition N113 := 113%N.
Definition N114 := 114%N.
Definition N115 := 115%N.
Definition N116 := 116%N.
Definition N117 := 117%N.
Definition N118 := 118%N.
Definition N119 := 119%N.
Definition N120 := 120%N.
Definition N121 := 121%N.
Definition N122 := 122%N.
Definition N123 := 123%N.
Definition N124 := 124%N.
Definition N125 := 125%N.
Definition N126 := 126%N.
Definition N127 := 127%N.
Definition N128 := 128%N.
Definition N129 := 129%N.
Definition N130 := 130%N.
Definition N131 := 131%N.
Definition N132 := 132%N.
Definition N133 := 133%N.
Definition N134 := 134%N.
Definition N135 := 135%N.
Definition N136 := 136%N.
Definition N137 := 137%N.
Definition N138 := 138%N.
Definition N139 := 139%N.
Definition N140 := 140%N.
Definition N141 := 141%N.
Definition N142 := 142%N.
Definition N143 := 143%N.
Definition N144 := 144%N.
Definition N145 := 145%N.
Definition N146 := 146%N.
Definition N147 := 147%N.
Definition N148 := 148%N.
Definition N149 := 149%N.
Definition N150 := 150%N.
Definition N151 := 151%N.
Definition N152 := 152%N.
Definition N153 := 153%N.
Definition N154 := 154%N.
Definition N155 := 155%N.
Definition N156 := 156%N.
Definition N157 := 157%N.
Definition N158 := 158%N.
Definition N159 := 159%N.
Definition N160 := 160%N.
Definition N161 := 161%N.
Definition N162 := 162%N.
Definition N163 := 163%N.
Definition N164 := 164%N.
Definition N165 := 165%N.
Definition N166 := 166%N.
Definition N167 := 167%N.
Definition N168 := 168%N.
Definition N169 := 169%N.
Definition N170 := 170%N.
Definition N171 := 171%N.
Definition N172 := 172%N.
Definition N173 := 173%N.
Definition N174 := 174%N.
Definition N175 := 175%N.
Definition N176 := 176%N.
Definition N177 := 177%N.
Definition N178 := 178%N.
Definition N179 := 179%N.
Definition N180 := 180%N.
Definition N181 := 181%N.
Definition N182 := 182%N.
Definition N183 := 183%N.
Definition N184 := 184%N.
Definition N185 := 185%N.
Definition N186 := 186%N.
Definition N187 := 187%N.
Definition N188 := 188%N.
Definition N189 := 189%N.
Definition N190 := 190%N.
Definition N191 := 191%N.
Definition N192 := 192%N.
Definition N193 := 193%N.
Definition N194 := 194%N.
Definition N195 := 195%N.
Definition N196 := 196%N.
Definition N197 := 197%N.
Definition N198 := 198%N.
Definition N199 := 199%N.
Definition N200 := 200%N.
Definition N201 := 201%N.
Definition N202 := 202%N.
Definition N203 := 203%N.
Definition N204 := 204%N.
Definition N205 := 205%N.
Definition N206 := 206%N.
Definition N207 := 207%N.
Definition N208 := 208%N.
Definition N209 := 209%N.
Definition N210 := 210%N.
Definition N211 := 211%N.
Definition N212 := 212%N.
Definition N213 := 213%N.
Definition N214 := 214%N.
Definition N215 := 215%N.
Definition N216 := 216%N.
Definition N217 := 217%N.
Definition N218 := 218%N.
Definition N219 := 219%N.
Definition N220 := 220%N.
Definition N221 := 221%N.
Definition N222 := 222%N.
Definition N223 := 223%N.
Definition N224 := 224%N.
Definition N225 := 225%N.
Definition N226 := 226%N.
Definition N227 := 227%N.
Definition N228 := 228%N.
Definition N229 := 229%N.
Definition N230 := 230%N.
Definition N231 := 231%N.
Definition N232 := 232%N.
Definition N233 := 233%N.
Definition N234 := 234%N.
Definition N235 := 235%N.
Definition N236 := 236%N.
Definition N237 := 237%N.
Definition N238 := 238%N.
Definition N239 := 239%N.
Definition N240 := 240%N.
Definition N241 := 241%N.
Definition N242 := 242%N.
Definition N243 := 243%N.
Definition N244 := 244%N.
Definition N245 := 245%N.
Definition N246 := 246%N.
Definition N247 := 247%N.
Definition N248 := 248%N.
Definition N249 := 249%N.
Definition N250 := 250%N.
Definition N251 := 251%N.
Definition N252 := 252%N.
Definition N253 := 253%N.
Definition N254 := 254%N.
Definition N255 := 255%N.

Definition to_N (x : byte) :=
  match x with
  | "000"%byte => N0
  | "001"%byte => N1
  | "002"%byte => N2
  | "003"%byte => N3
  | "004"%byte => N4
  | "005"%byte => N5
  | "006"%byte => N6
  | "007"%byte => N7
  | "008"%byte => N8
  | "009"%byte => N9
  | "010"%byte => N10
  | "011"%byte => N11
  | "012"%byte => N12
  | "013"%byte => N13
  | "014"%byte => N14
  | "015"%byte => N15
  | "016"%byte => N16
  | "017"%byte => N17
  | "018"%byte => N18
  | "019"%byte => N19
  | "020"%byte => N20
  | "021"%byte => N21
  | "022"%byte => N22
  | "023"%byte => N23
  | "024"%byte => N24
  | "025"%byte => N25
  | "026"%byte => N26
  | "027"%byte => N27
  | "028"%byte => N28
  | "029"%byte => N29
  | "030"%byte => N30
  | "031"%byte => N31
  | "032"%byte => N32
  | "033"%byte => N33
  | "034"%byte => N34
  | "035"%byte => N35
  | "036"%byte => N36
  | "037"%byte => N37
  | "038"%byte => N38
  | "039"%byte => N39
  | "040"%byte => N40
  | "041"%byte => N41
  | "042"%byte => N42
  | "043"%byte => N43
  | "044"%byte => N44
  | "045"%byte => N45
  | "046"%byte => N46
  | "047"%byte => N47
  | "048"%byte => N48
  | "049"%byte => N49
  | "050"%byte => N50
  | "051"%byte => N51
  | "052"%byte => N52
  | "053"%byte => N53
  | "054"%byte => N54
  | "055"%byte => N55
  | "056"%byte => N56
  | "057"%byte => N57
  | "058"%byte => N58
  | "059"%byte => N59
  | "060"%byte => N60
  | "061"%byte => N61
  | "062"%byte => N62
  | "063"%byte => N63
  | "064"%byte => N64
  | "065"%byte => N65
  | "066"%byte => N66
  | "067"%byte => N67
  | "068"%byte => N68
  | "069"%byte => N69
  | "070"%byte => N70
  | "071"%byte => N71
  | "072"%byte => N72
  | "073"%byte => N73
  | "074"%byte => N74
  | "075"%byte => N75
  | "076"%byte => N76
  | "077"%byte => N77
  | "078"%byte => N78
  | "079"%byte => N79
  | "080"%byte => N80
  | "081"%byte => N81
  | "082"%byte => N82
  | "083"%byte => N83
  | "084"%byte => N84
  | "085"%byte => N85
  | "086"%byte => N86
  | "087"%byte => N87
  | "088"%byte => N88
  | "089"%byte => N89
  | "090"%byte => N90
  | "091"%byte => N91
  | "092"%byte => N92
  | "093"%byte => N93
  | "094"%byte => N94
  | "095"%byte => N95
  | "096"%byte => N96
  | "097"%byte => N97
  | "098"%byte => N98
  | "099"%byte => N99
  | "100"%byte => N100
  | "101"%byte => N101
  | "102"%byte => N102
  | "103"%byte => N103
  | "104"%byte => N104
  | "105"%byte => N105
  | "106"%byte => N106
  | "107"%byte => N107
  | "108"%byte => N108
  | "109"%byte => N109
  | "110"%byte => N110
  | "111"%byte => N111
  | "112"%byte => N112
  | "113"%byte => N113
  | "114"%byte => N114
  | "115"%byte => N115
  | "116"%byte => N116
  | "117"%byte => N117
  | "118"%byte => N118
  | "119"%byte => N119
  | "120"%byte => N120
  | "121"%byte => N121
  | "122"%byte => N122
  | "123"%byte => N123
  | "124"%byte => N124
  | "125"%byte => N125
  | "126"%byte => N126
  | "127"%byte => N127
  | "128"%byte => N128
  | "129"%byte => N129
  | "130"%byte => N130
  | "131"%byte => N131
  | "132"%byte => N132
  | "133"%byte => N133
  | "134"%byte => N134
  | "135"%byte => N135
  | "136"%byte => N136
  | "137"%byte => N137
  | "138"%byte => N138
  | "139"%byte => N139
  | "140"%byte => N140
  | "141"%byte => N141
  | "142"%byte => N142
  | "143"%byte => N143
  | "144"%byte => N144
  | "145"%byte => N145
  | "146"%byte => N146
  | "147"%byte => N147
  | "148"%byte => N148
  | "149"%byte => N149
  | "150"%byte => N150
  | "151"%byte => N151
  | "152"%byte => N152
  | "153"%byte => N153
  | "154"%byte => N154
  | "155"%byte => N155
  | "156"%byte => N156
  | "157"%byte => N157
  | "158"%byte => N158
  | "159"%byte => N159
  | "160"%byte => N160
  | "161"%byte => N161
  | "162"%byte => N162
  | "163"%byte => N163
  | "164"%byte => N164
  | "165"%byte => N165
  | "166"%byte => N166
  | "167"%byte => N167
  | "168"%byte => N168
  | "169"%byte => N169
  | "170"%byte => N170
  | "171"%byte => N171
  | "172"%byte => N172
  | "173"%byte => N173
  | "174"%byte => N174
  | "175"%byte => N175
  | "176"%byte => N176
  | "177"%byte => N177
  | "178"%byte => N178
  | "179"%byte => N179
  | "180"%byte => N180
  | "181"%byte => N181
  | "182"%byte => N182
  | "183"%byte => N183
  | "184"%byte => N184
  | "185"%byte => N185
  | "186"%byte => N186
  | "187"%byte => N187
  | "188"%byte => N188
  | "189"%byte => N189
  | "190"%byte => N190
  | "191"%byte => N191
  | "192"%byte => N192
  | "193"%byte => N193
  | "194"%byte => N194
  | "195"%byte => N195
  | "196"%byte => N196
  | "197"%byte => N197
  | "198"%byte => N198
  | "199"%byte => N199
  | "200"%byte => N200
  | "201"%byte => N201
  | "202"%byte => N202
  | "203"%byte => N203
  | "204"%byte => N204
  | "205"%byte => N205
  | "206"%byte => N206
  | "207"%byte => N207
  | "208"%byte => N208
  | "209"%byte => N209
  | "210"%byte => N210
  | "211"%byte => N211
  | "212"%byte => N212
  | "213"%byte => N213
  | "214"%byte => N214
  | "215"%byte => N215
  | "216"%byte => N216
  | "217"%byte => N217
  | "218"%byte => N218
  | "219"%byte => N219
  | "220"%byte => N220
  | "221"%byte => N221
  | "222"%byte => N222
  | "223"%byte => N223
  | "224"%byte => N224
  | "225"%byte => N225
  | "226"%byte => N226
  | "227"%byte => N227
  | "228"%byte => N228
  | "229"%byte => N229
  | "230"%byte => N230
  | "231"%byte => N231
  | "232"%byte => N232
  | "233"%byte => N233
  | "234"%byte => N234
  | "235"%byte => N235
  | "236"%byte => N236
  | "237"%byte => N237
  | "238"%byte => N238
  | "239"%byte => N239
  | "240"%byte => N240
  | "241"%byte => N241
  | "242"%byte => N242
  | "243"%byte => N243
  | "244"%byte => N244
  | "245"%byte => N245
  | "246"%byte => N246
  | "247"%byte => N247
  | "248"%byte => N248
  | "249"%byte => N249
  | "250"%byte => N250
  | "251"%byte => N251
  | "252"%byte => N252
  | "253"%byte => N253
  | "254"%byte => N254
  | "255"%byte => N255
  end.
End ByteN.

Definition compare (x y : byte) :=
  N.compare (ByteN.to_N x) (ByteN.to_N y).

Register Equations.Init.sigma as equations.sigma.type.
Register Equations.Init.sigmaI as equations.sigma.intro.
Register Equations.Init.pr1 as equations.sigma.pr1.
Register Equations.Init.pr2 as equations.sigma.pr2.

Register Init.Logic.eq as equations.equality.type.
Register Init.Logic.eq_refl as equations.equality.refl.

Register Init.Logic.False as equations.bottom.type.
Register Init.Logic.False_rect as equations.bottom.case.

Register Init.Logic.True as equations.top.type.

Register Equations.Prop.DepElim.solution_left as equations.depelim.solution_left.
Register Equations.Prop.DepElim.solution_right as equations.depelim.solution_right.

Register Equations.Prop.Classes.NoConfusionPackage as equations.noconfusion.class.
Register Equations.Prop.Classes.apply_noConfusion as equations.depelim.apply_noConfusion.

Register Equations.Prop.DepElim.eq_simplification_sigma1 as equations.depelim.simpl_sigma.
Register Equations.Prop.DepElim.opaque_ind_pack_eq_inv as equations.depelim.opaque_ind_pack_eq_inv.
Import Equations.CoreTactics.
Import Equations.Prop.DepElim.

Ltac solve_noconf_prf := intros;
  on_last_hyp ltac:(fun id => destruct id) ;
  on_last_hyp ltac:(fun id =>
                      destruct_sigma id;
                      destruct id) ;
  constructor.

Ltac solve_noconf_inv_eq a b :=
  destruct_sigma a; destruct_sigma b;
  destruct a ; depelim b; simpl in * |-;
  on_last_hyp ltac:(fun id => hnf in id; destruct_tele_eq id || destruct id);
  solve [constructor].

Ltac solve_noconf_inv := intros;
  match goal with
    |- ?R ?a ?b => destruct_sigma a; destruct_sigma b;
                   destruct a ; depelim b; simpl in * |-;
                 on_last_hyp ltac:(fun id => hnf in id; destruct_tele_eq id || destruct id);
                 solve [constructor]
  | |- @eq _ (?f ?a ?b _) _ => solve_noconf_inv_eq a b
  end.

Ltac solve_noconf_inv_equiv :=
  intros;

  on_last_hyp ltac:(fun id => destruct id) ;

  on_last_hyp ltac:(fun id => destruct_sigma id; destruct id) ;
  simpl; constructor.

Ltac solve_noconf := simpl; intros;
    match goal with
      [ H : @eq _ _ _ |- @eq _ _ _ ] => try solve_noconf_inv_equiv
    | [ H : @eq _ _ _ |- _ ] => try solve_noconf_prf
    | [ |- @eq _ _ _ ] => try solve_noconf_inv
    end.

Ltac Equations.Init.solve_noconf ::= solve_noconf.
Export Equations.Prop.Classes.

Module Export MetaCoq_DOT_Utils_DOT_ReflectEq_WRAPPED.
Module Export ReflectEq.

Inductive reflectProp (P : Prop) : bool -> Prop :=
 | reflectP : P -> reflectProp P true
 | reflectF : ~ P -> reflectProp P false.

Class ReflectEq A := {
  eqb : A -> A -> bool ;
  eqb_spec : forall x y : A, reflectProp (x = y) (eqb x y)
}.

End ReflectEq.
Module Export MetaCoq.
Module Export Utils.
Module Export ReflectEq.
Include MetaCoq_DOT_Utils_DOT_ReflectEq_WRAPPED.ReflectEq.
End ReflectEq.
Import Coq.Structures.OrderedType.
Import Coq.Structures.Orders.
Definition compare_cont (c : comparison) (d : comparison) : comparison.
Admitted.

Module BoolOT <: UsualOrderedType.
  Definition t := bool.
Definition compare (x y : bool) : comparison.
Admitted.

  Definition lt (x y : bool) :=
    if x then False else y = true.

  Definition compare_spec (x y : bool) : CompareSpec (x = y) (lt x y) (lt y x) (compare x y).
Admitted.
Definition eq : t -> t -> Prop.
exact (eq).
Defined.
Definition eq_equiv : Equivalence eq.
exact (_).
Defined.

  Definition eq_dec (l1 l2 : t) : {l1 = l2}+{l1 <> l2}.
Admitted.

  Definition lt_strorder : StrictOrder lt.
Admitted.

  Definition lt_compat : Proper (eq ==> eq ==> iff) lt.
Admitted.

End BoolOT.

Module ListOrderedType (A : UsualOrderedType) <: UsualOrderedType.
  Definition t := list A.t.
Import ListNotations.
Fixpoint compare (l1 l2 : t) : comparison.
Admitted.
Definition eq : t -> t -> Prop.
exact (eq).
Defined.
Definition eq_equiv : Equivalence eq.
exact (_).
Defined.

  Inductive lt_ : t -> t -> Prop :=
  | lt_nil_cons hd tl : lt_ [] (hd :: tl)
  | lt_cons_cons_hd hd tl hd' tl' : A.lt hd hd' -> lt_ (hd :: tl) (hd' :: tl')
  | lt_cons_cons_tl hd tl tl' : lt_ tl tl' -> lt_ (hd :: tl) (hd :: tl').

  Definition lt := lt_.

  Global Instance lt_strorder : StrictOrder lt.
Admitted.

  Global Instance lt_compat : Proper (eq ==> eq ==> iff) lt.
Admitted.

  Definition compare_spec :
    forall x y : t, CompareSpec (x = y) (lt x y) (lt y x) (compare x y).
Admitted.
Definition eqb (l1 l2 : t) : bool.
Admitted.

  Program Definition eqb_dec (x y : t) : { x = y } + { x <> y } :=
    match eqb x y with
    | true => left _
    | false => right _
    end.
Admit Obligations.

  Global Instance eq_dec : EqDec t := { eq_dec := eqb_dec }.

End ListOrderedType.

Module Export String.
  Inductive t : Set :=
  | EmptyString
  | String (_ : Byte.byte) (_ : t).
Fixpoint compare (xs ys : t) : comparison.
Admitted.
Notation string := String.t.

Module OT_byte <: OrderedType.OrderedType with Definition t := Byte.byte.
  Definition t := Byte.byte.
  Definition eq := @Logic.eq t.
  Definition lt := fun l r => ByteCompare.compare l r = Lt.
  Theorem eq_refl : forall x : t, eq x x.
Admitted.
  Theorem eq_sym : forall x y : t, eq x y -> eq y x.
Admitted.
  Theorem eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
Admitted.
  Theorem lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
Admitted.
  Theorem lt_not_eq : forall x y : t, lt x y -> not (eq x y).
Admitted.
  Definition compare (x y : t) : OrderedType.Compare lt eq x y.
Admitted.
Definition eq_dec : forall x y : t, {eq x y} + {not (eq x y)}.
Admitted.
End OT_byte.

Module StringOT <: UsualOrderedType.
  Definition t := string.
Definition eq : t -> t -> Prop.
exact (eq).
Defined.
Definition eq_equiv : Equivalence eq.
exact (_).
Defined.

  Definition compare := String.compare.
  Definition lt x y : Prop := compare x y = Lt.

  Theorem compare_spec : forall x y, CompareSpec (x = y) (lt x y) (lt y x) (compare x y).
Admitted.
Definition eq_dec : forall x y : t, {eq x y} + {not (eq x y)}.
Admitted.

  Global Instance lt_strorder : StrictOrder lt.
Admitted.

  Definition lt_compat : Proper (eq ==> eq ==> iff) lt.
Admitted.

End StringOT.

Notation "p .1" := (fst p)
  (at level 2, left associativity, format "p .1") : pair_scope.
Notation "p .2" := (snd p)
  (at level 2, left associativity, format "p .2") : pair_scope.
Open Scope pair_scope.

Notation "x × y" := (prod x y ) (at level 80, right associativity).

Notation on_Trel_eq R f g :=
  (fun x y => (R (f x) (f y) * (g x = g y)))%type.

Coercion is_true : bool >-> Sortclass.

Notation "'eta_compose'" := (fun g f x => g (f x)).

Notation "g ∘ f" := (eta_compose g f) (at level 40, left associativity).

Notation "'∑' x .. y , p" := (sigT (fun x => .. (sigT (fun y => p%type)) ..))
  (at level 200, x binder, right associativity,
   format "'[' '∑'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.
Notation "x .π1" := (@projT1 _ _ x) (at level 3, format "x '.π1'").
Ltac tea := try eassumption.

Export ListNotations.

Notation "#| l |" := (List.length l) (at level 0, l at level 99, format "#| l |").

Fixpoint mapi_rec {A B} (f : nat -> A -> B) (l : list A) (n : nat) : list B :=
  match l with
  | [] => []
  | hd :: tl => f n hd :: mapi_rec f tl (S n)
  end.

Definition mapi {A B} (f : nat -> A -> B) (l : list A) := mapi_rec f l 0.

Section map2.

  Context {A B C} (f : A -> B -> C).
Fixpoint map2 (l : list A) (l' : list B) : list C.
Admitted.

End map2.

Fixpoint map_option_out {A} (l : list (option A)) : option (list A) :=
  match l with
  | nil => Some nil
  | hd :: tl => match hd, map_option_out tl with
                | Some hd, Some tl => Some (hd :: tl)
                | _, _ => None
                end
  end.

Inductive All {A} (P : A -> Type) : list A -> Type :=
    All_nil : All P []
  | All_cons : forall (x : A) (l : list A),
                  P x -> All P l -> All P (x :: l).

Inductive All2 {A B : Type} (R : A -> B -> Type) : list A -> list B -> Type :=
  All2_nil : All2 R [] []
| All2_cons : forall (x : A) (y : B) (l : list A) (l' : list B),
    R x y -> All2 R l l' -> All2 R (x :: l) (y :: l').

Inductive All2i {A B : Type} (R : nat -> A -> B -> Type) (n : nat)
  : list A -> list B -> Type :=
| All2i_nil : All2i R n [] []
| All2i_cons :
    forall x y l r,
      R n x y ->
      All2i R (S n) l r ->
      All2i R n (x :: l) (y :: r).

Section alli.
  Context {A} (p : nat -> A -> bool).
Fixpoint alli (n : nat) (l : list A) : bool.
Admitted.
End alli.

Inductive OnOne2 {A : Type} (P : A -> A -> Type) : list A -> list A -> Type :=
| OnOne2_hd hd hd' tl : P hd hd' -> OnOne2 P (hd :: tl) (hd' :: tl)
| OnOne2_tl hd tl tl' : OnOne2 P tl tl' -> OnOne2 P (hd :: tl) (hd :: tl').

Inductive All2_fold {A} (P : list A -> list A -> A -> A -> Type)
            : list A -> list A -> Type :=
| All2_fold_nil : All2_fold P nil nil
| All2_fold_cons {d d' Γ Γ'} : All2_fold P Γ Γ' -> P Γ Γ' d d' -> All2_fold P (d :: Γ) (d' :: Γ').

Module Export MetaCoq_DOT_Utils_DOT_MCUtils_WRAPPED.
Module Export MCUtils.
Export MetaCoq.Utils.ReflectEq.

End MCUtils.
Module Export MetaCoq.
Module Export Utils.
Module Export MCUtils.
Include MetaCoq_DOT_Utils_DOT_MCUtils_WRAPPED.MCUtils.
End MCUtils.

Module Export MetaCoq_DOT_Utils_DOT_utils_WRAPPED.
Module Export utils.
Export Coq.ZArith.ZArith.
Export MetaCoq.Utils.MCUtils.
Notation "A * B" := (prod A B) : type_scope2.
Global Open Scope type_scope2.

End utils.
Module Export MetaCoq.
Module Export Utils.
Module Export utils.
Include MetaCoq_DOT_Utils_DOT_utils_WRAPPED.utils.
End utils.

Definition ident   := string.

Definition dirpath := list ident.

Module IdentOT := StringOT.

Module DirPathOT := ListOrderedType IdentOT.

Inductive modpath :=
| MPfile  (dp : dirpath)
| MPbound (dp : dirpath) (id : ident) (i : nat)
| MPdot   (mp : modpath) (id : ident).

Definition kername := modpath × ident.

Module Export ModPathComp.

  Definition mpbound_compare dp id k dp' id' k' :=
    compare_cont (DirPathOT.compare dp dp')
      (compare_cont (IdentOT.compare id id') (Nat.compare k k')).

  Fixpoint compare mp mp' :=
    match mp, mp' with
    | MPfile dp, MPfile dp' => DirPathOT.compare dp dp'
    | MPbound dp id k, MPbound dp' id' k' =>
      mpbound_compare dp id k dp' id' k'
    | MPdot mp id, MPdot mp' id' =>
      compare_cont (compare mp mp') (IdentOT.compare id id')
    | MPfile _, _ => Gt
    | _, MPfile _ => Lt
    | MPbound _ _ _, _ => Gt
    | _, MPbound _ _ _ => Lt
    end.

End ModPathComp.

  Definition compare kn kn' :=
    match kn, kn' with
    | (mp, id), (mp', id') =>
      compare_cont (ModPathComp.compare mp mp') (IdentOT.compare id id')
    end.

  Definition eqb kn kn' :=
    match compare kn kn' with
    | Eq => true
    | _ => false
    end.

  #[global, program] Instance reflect_kername : ReflectEq kername := {
    eqb := eqb
  }.
Admit Obligations.

Record inductive : Set := mkInd { inductive_mind : kername ;
                                  inductive_ind : nat }.

Record projection := mkProjection
  { proj_ind : inductive;
    proj_npars : nat;
    proj_arg : nat   }.

Inductive global_reference :=
| VarRef : ident -> global_reference
| ConstRef : kername -> global_reference
| IndRef : inductive -> global_reference
| ConstructRef : inductive -> nat -> global_reference.
Module Export BasicAst.

Inductive name : Set :=
| nAnon
| nNamed (_ : ident).

Inductive relevance : Set := Relevant | Irrelevant.

Record binder_annot (A : Type) := mkBindAnn { binder_name : A; binder_relevance : relevance }.
Definition eq_binder_annot {A B} (b : binder_annot A) (b' : binder_annot B) : Prop.
Admitted.

Definition aname := binder_annot name.

Record case_info := mk_case_info {
  ci_ind : inductive;
  ci_npar : nat;

  ci_relevance : relevance }.

Inductive recursivity_kind :=
  | Finite
  | CoFinite
  | BiFinite  .

Inductive conv_pb :=
  | Conv
  | Cumul.

Record def term := mkdef {
  dname : aname;
  dtype : term;
  dbody : term;
  rarg  : nat    }.

Arguments dname {term} _.
Arguments dtype {term} _.
Arguments dbody {term} _.
Arguments rarg {term} _.

Definition map_def {A B} (tyf bodyf : A -> B) (d : def A) :=
  {| dname := d.(dname); dtype := tyf d.(dtype); dbody := bodyf d.(dbody); rarg := d.(rarg) |}.

Definition mfixpoint term := list (def term).

Variant typ_or_sort_ {term} := Typ (T : term) | Sort.
Arguments typ_or_sort_ : clear implicits.

Section Contexts.
  Context {term : Type}.

  Record context_decl := mkdecl {
    decl_name : aname ;
    decl_body : option term ;
    decl_type : term
  }.
End Contexts.

Arguments context_decl : clear implicits.
Definition map_decl {term term'} (f : term -> term') (d : context_decl term) : context_decl term'.
Admitted.
Definition test_decl {term} (f : term -> bool) (d : context_decl term) : bool.
Admitted.

Definition snoc {A} (Γ : list A) (d : A) := d :: Γ.

Notation " Γ ,, d " := (snoc Γ d) (at level 20, d at next level).

Section Contexts.
  Context {term term' term'' : Type}.

  Definition fold_context_k (f : nat -> term -> term') Γ :=
    List.rev (mapi (fun k' decl => map_decl (f k') decl) (List.rev Γ)).
Definition forget_types (c : list (BasicAst.context_decl term)) : list aname.
admit.
Defined.

End Contexts.

Module Export Universes.
Import Coq.MSets.MSetList.
Import MetaCoq.Utils.utils.
Import MetaCoq.Common.config.

Record valuation :=
  { valuation_mono : string -> positive ;
    valuation_poly : nat -> nat }.

Class Evaluable (A : Type) := val : valuation -> A -> nat.

Module Level.
  Inductive t_ : Set :=
  | lzero
  | level (_ : string)
  | lvar (_ : nat)  .

  Definition t := t_.
Global Instance Evaluable : Evaluable t.
Admitted.
Definition compare (l1 l2 : t) : comparison.
Admitted.
Definition eq : t -> t -> Prop.
exact (eq).
Defined.
Definition eq_equiv : Equivalence eq.
Admitted.

  Inductive lt_ : t -> t -> Prop :=
  | ltSetLevel s : lt_ lzero (level s)
  | ltSetlvar n : lt_ lzero (lvar n)
  | ltLevelLevel s s' : StringOT.lt s s' -> lt_ (level s) (level s')
  | ltLevellvar s n : lt_ (level s) (lvar n)
  | ltlvarlvar n n' : Nat.lt n n' -> lt_ (lvar n) (lvar n').

  Definition lt := lt_.

  Definition lt_strorder : StrictOrder lt.
Admitted.

  Definition lt_compat : Proper (eq ==> eq ==> iff) lt.
Admitted.

  Definition compare_spec :
    forall x y : t, CompareSpec (x = y) (lt x y) (lt y x) (compare x y).
Admitted.
Definition eq_dec : forall (l1 l2 : t), {l1 = l2}+{l1 <> l2}.
Admitted.

End Level.

Module LevelSet := MSetAVL.Make Level.

Module LevelExpr.

  Definition t := (Level.t * nat)%type.
Definition get_level (e : t) : Level.t.
Admitted.
Definition eq : t -> t -> Prop.
exact (eq).
Defined.
Definition eq_equiv : Equivalence eq.
Admitted.

  Inductive lt_ : t -> t -> Prop :=
  | ltLevelExpr1 l n n' : (n < n')%nat -> lt_ (l, n) (l, n')
  | ltLevelExpr2 l l' b b' : Level.lt l l' -> lt_ (l, b) (l', b').

  Definition lt := lt_.

  Global Instance lt_strorder : StrictOrder lt.
Admitted.

  Definition lt_compat : Proper (Logic.eq ==> Logic.eq ==> iff) lt.
Admitted.
Definition compare (x y : t) : comparison.
Admitted.

  Definition compare_spec :
    forall x y : t, CompareSpec (x = y) (lt x y) (lt y x) (compare x y).
Admitted.
Definition eq_dec : forall (l1 l2 : t), {l1 = l2} + {l1 <> l2}.
Admitted.
Definition eq_leibniz (x y : t) : eq x y -> x = y.
Admitted.

End LevelExpr.

Module LevelExprSet := MSetList.MakeWithLeibniz LevelExpr.

Record nonEmptyLevelExprSet
  := { t_set : LevelExprSet.t ;
       t_ne  : LevelExprSet.is_empty t_set = false }.

Coercion t_set : nonEmptyLevelExprSet >-> LevelExprSet.t.

Module Export LevelAlgExpr.

  Definition t := nonEmptyLevelExprSet.
Global Instance Evaluable : Evaluable LevelAlgExpr.t.
Admitted.
Definition lt : t -> t -> Prop.
Admitted.
End LevelAlgExpr.

Inductive allowed_eliminations : Set :=
  | IntoSProp
  | IntoPropSProp
  | IntoSetPropSProp
  | IntoAny.

Module Export Universe.
  Inductive t_ :=
    lProp | lSProp | lType (_ : LevelAlgExpr.t).

  Definition t := t_.

  Definition on_sort (P: LevelAlgExpr.t -> Prop) (def: Prop) (s : t) :=
    match s with
    | lProp | lSProp => def
    | lType l => P l
    end.
Definition make (l : Level.t) : t.
Admitted.
Definition is_sprop (u : t) : bool.
Admitted.
Definition is_prop (u : t) : bool.
Admitted.
Definition type0 : t.
Admitted.
Definition super (l : t) : t.
Admitted.
Definition sup (u v : t) : t.
Admitted.

  Definition sort_of_product (domsort rangsort : t) :=

    if Universe.is_prop rangsort || Universe.is_sprop rangsort then rangsort
    else Universe.sup domsort rangsort.

  Inductive lt_ : t -> t -> Prop :=
  | ltPropSProp : lt_ lProp lSProp
  | ltPropType s : lt_ lProp (lType s)
  | ltSPropType s : lt_ lSProp (lType s)
  | ltTypeType s1 s2 : LevelAlgExpr.lt s1 s2 -> lt_ (lType s1) (lType s2).

  Definition lt := lt_.

  Module OT <: OrderedType.
    Definition t := t.
#[local] Definition eq : t -> t -> Prop.
exact (eq).
Defined.
#[local] Definition eq_equiv : Equivalence eq.
Admitted.
    Definition lt := lt.
    #[local] Instance lt_strorder : StrictOrder lt.
Admitted.

    Definition lt_compat : Proper (eq ==> eq ==> iff) lt.
Admitted.
Definition compare (x y : t) : comparison.
Admitted.
    Lemma compare_spec x y : CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
Admitted.
    Definition eq_dec (x y : t) : {x = y} + {x <> y}.
Admitted.
  End OT.
End Universe.

Definition is_propositional u :=
  Universe.is_prop u || Universe.is_sprop u.

Module Export ConstraintType.
  Inductive t_ : Set := Le (z : Z) | Eq.

  Definition t := t_.

  Inductive lt_ : t -> t -> Prop :=
  | LeLe n m : (n < m)%Z -> lt_ (Le n) (Le m)
  | LeEq n : lt_ (Le n) Eq.
  Definition lt := lt_.
End ConstraintType.

Module UnivConstraint.
Definition t : Set.
exact (Level.t * ConstraintType.t * Level.t).
Defined.
Definition eq : t -> t -> Prop.
Admitted.
Definition eq_equiv : Equivalence eq.
Admitted.

  Inductive lt_ : t -> t -> Prop :=
  | lt_Level2 l1 t l2 l2' : Level.lt l2 l2' -> lt_ (l1, t, l2) (l1, t, l2')
  | lt_Cstr l1 t t' l2 l2' : ConstraintType.lt t t' -> lt_ (l1, t, l2) (l1, t', l2')
  | lt_Level1 l1 l1' t t' l2 l2' : Level.lt l1 l1' -> lt_ (l1, t, l2) (l1', t', l2').
  Definition lt := lt_.

  Lemma lt_strorder : StrictOrder lt.
Admitted.

  Lemma lt_compat : Proper (eq ==> eq ==> iff) lt.
Admitted.
Definition compare : t -> t -> comparison.
Admitted.

  Lemma compare_spec x y
    : CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
Admitted.

  Lemma eq_dec x y : {eq x y} + {~ eq x y}.
Admitted.
End UnivConstraint.

Module ConstraintSet := MSetAVL.Make UnivConstraint.

Module Export Instance.
Definition t : Set.
exact (list Level.t).
Defined.
Definition empty : t.
Admitted.
End Instance.

Module Export UContext.
  Definition t := list name × (Instance.t × ConstraintSet.t).
Definition instance : t -> Instance.t.
Admitted.
End UContext.

Module Export AUContext.
  Definition t := list name × ConstraintSet.t.
Definition repr (x : t) : UContext.t.
Admitted.
End AUContext.

Module Export ContextSet.
  Definition t := LevelSet.t × ConstraintSet.t.
End ContextSet.

Module Export Variance.

  Inductive t :=
  | Irrelevant : t
  | Covariant : t
  | Invariant : t.

Inductive universes_decl : Type :=
| Monomorphic_ctx
| Polymorphic_ctx (cst : AUContext.t).

Section Univ.
  Context {cf: checker_flags}.

  Inductive satisfies0 (v : valuation) : UnivConstraint.t -> Prop :=
  | satisfies0_Lt (l l' : Level.t) (z : Z) : (Z.of_nat (val v l) <= Z.of_nat (val v l') - z)%Z
                         -> satisfies0 v (l, ConstraintType.Le z, l')
  | satisfies0_Eq (l l' : Level.t) : val v l = val v l'
                         -> satisfies0 v (l, ConstraintType.Eq, l').

  Definition satisfies v : ConstraintSet.t -> Prop :=
    ConstraintSet.For_all (satisfies0 v).

  Definition leq0_levelalg_n n φ (u u' : LevelAlgExpr.t) :=
    forall v, satisfies v φ -> (Z.of_nat (val v u) <= Z.of_nat (val v u') - n)%Z.

  Definition leq_levelalg_n n φ (u u' : LevelAlgExpr.t) :=
    if check_univs then leq0_levelalg_n n φ u u' else True.

  Definition leq_universe_n_ {CS} leq_levelalg_n n (φ: CS) s s' :=
    match s, s' with
    | Universe.lProp,   Universe.lProp
    | Universe.lSProp,  Universe.lSProp => (n = 0)%Z
    | Universe.lType u, Universe.lType u' => leq_levelalg_n n φ u u'
    | Universe.lProp,   Universe.lType u => prop_sub_type
    | _, _ => False
    end.

  Definition leq_universe_n := leq_universe_n_ leq_levelalg_n.

  Definition eq0_levelalg φ (u u' : LevelAlgExpr.t) :=
    forall v, satisfies v φ -> val v u = val v u'.

  Definition eq_levelalg φ (u u' : LevelAlgExpr.t) :=
    if check_univs then eq0_levelalg φ u u' else True.

  Definition eq_universe_ {CS} eq_levelalg (φ: CS) s s' :=
    match s, s' with
    | Universe.lProp,   Universe.lProp
    | Universe.lSProp,  Universe.lSProp => True
    | Universe.lType u, Universe.lType u' => eq_levelalg φ u u'
    | _, _ => False
    end.

  Definition eq_universe := eq_universe_ eq_levelalg.
  Definition leq_universe := leq_universe_n 0.

  Definition compare_universe (pb : conv_pb) :=
    match pb with
    | Conv => eq_universe
    | Cumul => leq_universe
    end.

  Definition valid_constraints0 φ ctrs
    := forall v, satisfies v φ -> satisfies v ctrs.

  Definition valid_constraints φ ctrs
    := if check_univs then valid_constraints0 φ ctrs else True.

  Definition is_lSet φ s := eq_universe φ s Universe.type0.

  Definition is_allowed_elimination φ allowed : Universe.t -> Prop :=
    match allowed with
    | IntoSProp => Universe.is_sprop
    | IntoPropSProp => is_propositional
    | IntoSetPropSProp => fun s => is_propositional s \/ is_lSet φ s
    | IntoAny => fun s => True
    end.

End Univ.

Class UnivSubst A := subst_instance : Instance.t -> A -> A.

Notation "x @[ u ]" := (subst_instance u x) (at level 3,
  format "x @[ u ]").
#[global] Instance subst_instance_cstrs : UnivSubst ConstraintSet.t.
Admitted.

Definition abstract_instance decl :=
  match decl with
  | Monomorphic_ctx => Instance.empty
  | Polymorphic_ctx auctx => UContext.instance (AUContext.repr auctx)
  end.

#[global] Instance reflect_recursivity_kind : ReflectEq recursivity_kind.
Admitted.

Variant prim_tag :=
  | primInt
  | primFloat.
Import Coq.ssr.ssrbool.

Module Type Term.

  Parameter Inline term : Type.

  Parameter Inline tRel : nat -> term.
  Parameter Inline tSort : Universe.t -> term.
  Parameter Inline tLambda : aname -> term -> term -> term.
  Parameter Inline tLetIn : aname -> term -> term -> term -> term.

  Parameter Inline lift : nat -> nat -> term -> term.
  Parameter Inline subst : list term -> nat -> term -> term.
End Term.

Module Type TermDecide (Import T : Term).
End TermDecide.

Module TermDecideReflectInstances (Import T : Term) (Import TDec : TermDecide T).
End TermDecideReflectInstances.

Module Export Retroknowledge.

  Record t := mk_retroknowledge {
    retro_int63 : option kername;
    retro_float64 : option kername;
  }.

Module Environment (T : Term).

  Import T.

  Definition typ_or_sort := typ_or_sort_ term.

  Notation context_decl := (context_decl term).

  Definition vass x A : context_decl :=
    {| decl_name := x ; decl_body := None ; decl_type := A |}.

  Definition vdef x t A : context_decl :=
    {| decl_name := x ; decl_body := Some t ; decl_type := A |}.

  Definition context := list context_decl.

  Definition lift_context n k (Γ : context) : context :=
    fold_context_k (fun k' => lift n (k' + k)) Γ.

  Definition subst_context s k (Γ : context) : context :=
    fold_context_k (fun k' => subst s (k' + k)) Γ.

  Definition subst_telescope s k (Γ : context) : context :=
    mapi (fun k' decl => map_decl (subst s (k' + k)) decl) Γ.
Global Instance subst_instance_context : UnivSubst context.
Admitted.
Definition set_binder_name (na : aname) (x : context_decl) : context_decl.
Admitted.

  Fixpoint context_assumptions (Γ : context) :=
    match Γ with
    | [] => 0
    | d :: Γ =>
      match d.(decl_body) with
      | Some _ => context_assumptions Γ
      | None => S (context_assumptions Γ)
      end
    end.
Fixpoint smash_context (Γ Γ' : context) : context.
Admitted.

  Fixpoint extended_subst (Γ : context) (n : nat)
    :=
  match Γ with
  | nil => nil
  | cons d vs =>
    match decl_body d with
    | Some b =>

      let s := extended_subst vs n in

      let b' := lift (context_assumptions vs + n) #|s| b in

      let b' := subst s 0 b' in

      b' :: s
    | None => tRel n :: extended_subst vs (S n)
    end
  end.

  Definition expand_lets_k Γ k t :=
    (subst (extended_subst Γ 0) k (lift (context_assumptions Γ) (k + #|Γ|) t)).

  Definition expand_lets Γ t := expand_lets_k Γ 0 t.

  Definition expand_lets_k_ctx Γ k Δ :=
    (subst_context (extended_subst Γ 0) k (lift_context (context_assumptions Γ) (k + #|Γ|) Δ)).

  Definition expand_lets_ctx Γ Δ := expand_lets_k_ctx Γ 0 Δ.
Definition fix_context (m : mfixpoint term) : context.
Admitted.

  Record constructor_body := {
    cstr_name : ident;

    cstr_args : context;
    cstr_indices : list term;
    cstr_type : term;

    cstr_arity : nat;
  }.

  Record projection_body := {
    proj_name : ident;

    proj_relevance : relevance;
    proj_type : term;
  }.

  Record one_inductive_body := {
    ind_name : ident;
    ind_indices : context;
    ind_sort : Universe.t;
    ind_type : term;
    ind_kelim : allowed_eliminations;
    ind_ctors : list constructor_body;
    ind_projs : list projection_body;
    ind_relevance : relevance   }.

  Record mutual_inductive_body := {
    ind_finite : recursivity_kind;
    ind_npars : nat;
    ind_params : context;
    ind_bodies : list one_inductive_body ;
    ind_universes : universes_decl;
    ind_variance : option (list Universes.Variance.t) }.

  Record constant_body := {
    cst_type : term;
    cst_body : option term;
    cst_universes : universes_decl;
    cst_relevance : relevance }.

  Inductive global_decl :=
  | ConstantDecl : constant_body -> global_decl
  | InductiveDecl : mutual_inductive_body -> global_decl.

  Definition global_declarations := list (kername * global_decl).

  Record global_env := mk_global_env
    { universes : ContextSet.t;
      declarations : global_declarations;
      retroknowledge : Retroknowledge.t }.
Fixpoint lookup_global (Σ : global_declarations) (kn : kername) : option global_decl.
Admitted.

  Definition lookup_env (Σ : global_env) (kn : kername) := lookup_global Σ.(declarations) kn.
Definition primitive_constant (Σ : global_env) (p : prim_tag) : option kername.
Admitted.

  Definition primitive_invariants (cdecl : constant_body) :=
    ∑ s, [/\ cdecl.(cst_type) = tSort s, cdecl.(cst_body) = None &
             cdecl.(cst_universes) = Monomorphic_ctx].
Definition global_env_ext : Type.
exact (global_env * universes_decl).
Defined.
Definition fst_ctx : global_env_ext -> global_env.
Admitted.
  Coercion fst_ctx : global_env_ext >-> global_env.
Definition app_context (Γ Γ' : context) : context.
Admitted.
  Notation "Γ ,,, Γ'" :=
    (app_context Γ Γ') (at level 25, Γ' at next level, left associativity).

  Definition mkLambda_or_LetIn d t :=
    match d.(decl_body) with
    | None => tLambda d.(decl_name) d.(decl_type) t
    | Some b => tLetIn d.(decl_name) b d.(decl_type) t
    end.

  Definition it_mkLambda_or_LetIn (l : context) (t : term) :=
    List.fold_left (fun acc d => mkLambda_or_LetIn d acc) l t.
Fixpoint reln (l : list term) (p : nat) (Γ0 : list context_decl) {struct Γ0} : list term.
Admitted.

  Definition to_extended_list_k Γ k := reln [] k Γ.
  Definition to_extended_list Γ := to_extended_list_k Γ 0.

End Environment.

Module Type EnvironmentSig (T : Term).
 Include Environment T.
End EnvironmentSig.

Module Type EnvironmentDecide (T : Term) (Import E : EnvironmentSig T).
End EnvironmentDecide.

Module EnvironmentDecideReflectInstances (T : Term) (Import E : EnvironmentSig T) (Import EDec : EnvironmentDecide T E).
End EnvironmentDecideReflectInstances.

Module Type TermUtils (T: Term) (E: EnvironmentSig T).

End TermUtils.
Module Export EnvironmentTyping.

Module Lookup (T : Term) (E : EnvironmentSig T).
Import E.

  Definition declared_constant (Σ : global_env) id decl := In (id,ConstantDecl decl) (declarations Σ).

  Definition declared_minductive Σ mind decl := In (mind,InductiveDecl decl) (declarations Σ).

  Definition declared_inductive Σ ind mdecl decl :=
    declared_minductive Σ (inductive_mind ind) mdecl /\
    List.nth_error mdecl.(ind_bodies) (inductive_ind ind) = Some decl.

  Definition declared_constructor Σ cstr mdecl idecl cdecl :=
    declared_inductive Σ (fst cstr) mdecl idecl /\
    List.nth_error idecl.(ind_ctors) (snd cstr) = Some cdecl.

  Definition declared_projection Σ (proj : projection) mdecl idecl cdecl pdecl
  : Prop :=
    declared_constructor Σ (proj.(proj_ind), 0) mdecl idecl cdecl /\
    List.nth_error idecl.(ind_projs) proj.(proj_arg) = Some pdecl /\
    mdecl.(ind_npars) = proj.(proj_npars).

  Definition lookup_minductive_gen (lookup : kername -> option global_decl) mind :=
    match lookup mind with
    | Some (InductiveDecl decl) => Some decl
    | _ => None
    end.

  Definition lookup_inductive_gen lookup ind :=
    match lookup_minductive_gen lookup (inductive_mind ind) with
    | Some mdecl =>
      match nth_error mdecl.(ind_bodies) (inductive_ind ind) with
      | Some idecl => Some (mdecl, idecl)
      | None => None
      end
    | None => None
    end.

  Definition lookup_constructor_gen lookup ind k :=
    match lookup_inductive_gen lookup ind with
    | Some (mdecl, idecl) =>
      match nth_error idecl.(ind_ctors) k with
      | Some cdecl => Some (mdecl, idecl, cdecl)
      | None => None
      end
    | _ => None
    end.
Definition global_ext_levels (Σ : global_env_ext) : LevelSet.t.
Admitted.
Definition global_ext_constraints (Σ : global_env_ext) : ConstraintSet.t.
Admitted.

  Coercion global_ext_constraints : global_env_ext >-> ConstraintSet.t.

  Definition consistent_instance `{checker_flags} (lvs : LevelSet.t) (φ : ConstraintSet.t) uctx (u : Instance.t) :=
    match uctx with
    | Monomorphic_ctx => List.length u = 0
    | Polymorphic_ctx c =>

      forallb (fun l => LevelSet.mem l lvs) u /\
      List.length u = List.length c.1 /\
      valid_constraints φ (subst_instance_cstrs u c.2)
    end.

  Definition consistent_instance_ext `{checker_flags} Σ :=
    consistent_instance (global_ext_levels Σ) (global_ext_constraints Σ).

  Definition wf_universe Σ s : Prop :=
    Universe.on_sort
      (fun u => forall l, LevelExprSet.In l u -> LevelSet.In (LevelExpr.get_level l) (global_ext_levels Σ))
      True s.

End Lookup.

Module Type LookupSig (T : Term) (E : EnvironmentSig T).
End LookupSig.

Module EnvTyping (T : Term) (E : EnvironmentSig T) (TU : TermUtils T E).
Import T.
Import E.

  Section TypeLocal.
    Context (typing : forall (Γ : context), term -> typ_or_sort -> Type).

    Inductive All_local_env : context -> Type :=
    | localenv_nil :
        All_local_env []

    | localenv_cons_abs Γ na t :
        All_local_env Γ ->
        typing Γ t Sort ->
        All_local_env (Γ ,, vass na t)

    | localenv_cons_def Γ na b t :
        All_local_env Γ ->
        typing Γ t Sort ->
        typing Γ b (Typ t) ->
        All_local_env (Γ ,, vdef na b t).
  End TypeLocal.

  Definition lift_judgment
    (check : global_env_ext -> context -> term -> term -> Type)
    (infer_sort : global_env_ext -> context -> term -> Type) :
    (global_env_ext -> context -> term -> typ_or_sort -> Type).
admit.
Defined.

  Definition infer_sort (sorting : global_env_ext -> context -> term -> Universe.t -> Type) := (fun Σ Γ T => { s : Universe.t & sorting Σ Γ T s }).
  Notation typing_sort typing := (fun Σ Γ T s => typing Σ Γ T (tSort s)).

  Definition lift_typing typing := lift_judgment typing (infer_sort (typing_sort typing)).

  Section TypeCtxInst.
    Context (typing : forall (Σ : global_env_ext) (Γ : context), term -> term -> Type).

    Inductive ctx_inst Σ (Γ : context) : list term -> context -> Type :=
    | ctx_inst_nil : ctx_inst Σ Γ [] []
    | ctx_inst_ass na t i inst Δ :
        typing Σ Γ i t ->
        ctx_inst Σ Γ inst (subst_telescope [i] 0 Δ) ->
        ctx_inst Σ Γ (i :: inst) (vass na t :: Δ)
    | ctx_inst_def na b t inst Δ :
        ctx_inst Σ Γ inst (subst_telescope [b] 0 Δ) ->
        ctx_inst Σ Γ inst (vdef na b t :: Δ).
  End TypeCtxInst.

  End EnvTyping.

Module Type EnvTypingSig (T : Term) (E : EnvironmentSig T) (TU : TermUtils T E).
  Include EnvTyping T E TU.
End EnvTypingSig.

Module Conversion (T : Term) (E : EnvironmentSig T) (TU : TermUtils T E) (ET : EnvTypingSig T E TU).

  End Conversion.

Module Type ConversionSig (T : Term) (E : EnvironmentSig T) (TU : TermUtils T E) (ET : EnvTypingSig T E TU).
End ConversionSig.

Module GlobalMaps (T: Term) (E: EnvironmentSig T) (TU : TermUtils T E) (ET: EnvTypingSig T E TU) (C: ConversionSig T E TU ET) (L: LookupSig T E).
Import T.
Import E.

  Section GlobalMaps.
    Context (Pcmp: global_env_ext -> context -> conv_pb -> term -> term -> Type).
    Context (P : global_env_ext -> context -> term -> typ_or_sort -> Type).
Definition on_global_env (g : global_env) : Type.
Admitted.

  End GlobalMaps.

End GlobalMaps.

Module Type GlobalMapsSig (T: Term) (E: EnvironmentSig T) (TU : TermUtils T E) (ET: EnvTypingSig T E TU) (C: ConversionSig T E TU ET) (L: LookupSig T E).
  Include GlobalMaps T E TU ET C L.
End GlobalMapsSig.

Module Type ConversionParSig (T : Term) (E : EnvironmentSig T) (TU : TermUtils T E) (ET : EnvTypingSig T E TU).
Import T.
Import E.

  Parameter Inline cumul_gen : forall {cf : checker_flags}, global_env_ext -> context -> conv_pb -> term -> term -> Type.

End ConversionParSig.

Module Type Typing (T : Term) (E : EnvironmentSig T) (TU : TermUtils T E) (ET : EnvTypingSig T E TU)
  (CT : ConversionSig T E TU ET) (CS : ConversionParSig T E TU ET).

End Typing.

Module DeclarationTyping (T : Term) (E : EnvironmentSig T) (TU : TermUtils T E)
  (ET : EnvTypingSig T E TU) (CT : ConversionSig T E TU ET)
  (CS : ConversionParSig T E TU ET) (Ty : Typing T E TU ET CT CS)
  (L : LookupSig T E) (GM : GlobalMapsSig T E TU ET CT L).
Import T.
Import E.
Import ET.
Import GM.
Import CS.

  Definition Forall_decls_typing `{checker_flags}
            (P : global_env_ext -> context -> term -> term -> Type)
    := on_global_env cumul_gen (lift_typing P).

  End DeclarationTyping.

Inductive prim_model (term : Type) : prim_tag -> Type :=
| primIntModel (i : PrimInt63.int) : prim_model term primInt
| primFloatModel (f : PrimFloat.float) : prim_model term primFloat.

Definition prim_val term := ∑ t : prim_tag, prim_model term t.
Definition prim_val_tag {term} (s : prim_val term) := s.π1.

Record predicate {term} := mk_predicate {
  pparams : list term;
  puinst : Instance.t;
  pcontext : list (context_decl term);

  preturn : term;   }.
Arguments predicate : clear implicits.

Section map_predicate_k.
  Context {term : Type}.
  Context (uf : Instance.t -> Instance.t).
  Context (f : nat -> term -> term).

  Definition map_predicate_k k (p : predicate term) :=
    {| pparams := map (f k) p.(pparams);
        puinst := uf p.(puinst);
        pcontext := p.(pcontext);
        preturn := f (#|p.(pcontext)| + k) p.(preturn) |}.

End map_predicate_k.

Section Branch.
  Context {term : Type}.

  Record branch := mk_branch {
    bcontext : list (context_decl term);

    bbody : term;   }.

End Branch.
Arguments branch : clear implicits.

Section map_branch_k.
  Context {term term' : Type}.
  Context (f : nat -> term -> term').
  Context (g : list (BasicAst.context_decl term) -> list (BasicAst.context_decl term')).
  Definition map_branch_k k (b : branch term) :=
  {| bcontext := g b.(bcontext);
     bbody := f (#|b.(bcontext)| + k) b.(bbody) |}.
End map_branch_k.

Notation map_branches_k f h k brs :=
  (List.map (map_branch_k f h k) brs).

Inductive term :=
| tRel (n : nat)
| tVar (i : ident)
| tEvar (n : nat) (l : list term)
| tSort (u : Universe.t)
| tProd (na : aname) (A B : term)
| tLambda (na : aname) (A t : term)
| tLetIn (na : aname) (b B t : term)
| tApp (u v : term)
| tConst (k : kername) (ui : Instance.t)
| tInd (ind : inductive) (ui : Instance.t)
| tConstruct (ind : inductive) (n : nat) (ui : Instance.t)
| tCase (indn : case_info) (p : predicate term) (c : term) (brs : list (branch term))
| tProj (p : projection) (c : term)
| tFix (mfix : mfixpoint term) (idx : nat)
| tCoFix (mfix : mfixpoint term) (idx : nat)
| tPrim (prim : prim_val term).

Derive NoConfusion for term.

Fixpoint mkApps t us :=
  match us with
  | nil => t
  | u :: us => mkApps (tApp t u) us
  end.

Definition isLambda t :=
  match t with
  | tLambda _ _ _ => true
  | _ => false
  end.

Fixpoint lift n k t : term :=
  match t with
  | tRel i => tRel (if Nat.leb k i then (n + i) else i)
  | tEvar ev args => tEvar ev (List.map (lift n k) args)
  | tLambda na T M => tLambda na (lift n k T) (lift n (S k) M)
  | tApp u v => tApp (lift n k u) (lift n k v)
  | tProd na A B => tProd na (lift n k A) (lift n (S k) B)
  | tLetIn na b t b' => tLetIn na (lift n k b) (lift n k t) (lift n (S k) b')
  | tCase ind p c brs =>
    let p' := map_predicate_k id (lift n) k p in
    let brs' := map_branches_k (lift n) id k brs in
    tCase ind p' (lift n k c) brs'
  | tProj p c => tProj p (lift n k c)
  | tFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (lift n k) (lift n k')) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (lift n k) (lift n k')) mfix in
    tCoFix mfix' idx
  | x => x
  end.

Notation lift0 n := (lift n 0).

Fixpoint subst s k u :=
  match u with
  | tRel n =>
    if Nat.leb k n then
      match nth_error s (n - k) with
      | Some b => lift0 k b
      | None => tRel (n - List.length s)
      end
    else tRel n
  | tEvar ev args => tEvar ev (List.map (subst s k) args)
  | tLambda na T M => tLambda na (subst s k T) (subst s (S k) M)
  | tApp u v => tApp (subst s k u) (subst s k v)
  | tProd na A B => tProd na (subst s k A) (subst s (S k) B)
  | tLetIn na b ty b' => tLetIn na (subst s k b) (subst s k ty) (subst s (S k) b')
  | tCase ind p c brs =>
    let p' := map_predicate_k id (subst s) k p in
    let brs' := map_branches_k (subst s) id k brs in
    tCase ind p' (subst s k c) brs'
  | tProj p c => tProj p (subst s k c)
  | tFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (subst s k) (subst s k')) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (subst s k) (subst s k')) mfix in
    tCoFix mfix' idx
  | x => x
  end.

Notation subst0 t := (subst t 0).
Definition subst1 t k u := subst [t] k u.
Notation "M { j := N }" := (subst1 N j M) (at level 10, right associativity).
#[global]
Instance subst_instance_constr : UnivSubst term.
Admitted.

Module PCUICTerm <: Term.

  Definition term := term.

  Definition tRel := tRel.
  Definition tSort := tSort.
  Definition tLambda := tLambda.
  Definition tLetIn := tLetIn.

  Definition lift := lift.
  Definition subst := subst.
End PCUICTerm.

Module PCUICEnvironment := Environment PCUICTerm.
Export PCUICEnvironment.

Fixpoint destArity Γ (t : term) :=
  match t with
  | tProd na t b => destArity (Γ ,, vass na t) b
  | tLetIn na b b_ty b' => destArity (Γ ,, vdef na b b_ty) b'
  | tSort s => Some (Γ, s)
  | _ => None
  end.

Definition inds ind u (l : list one_inductive_body) :=
  let fix aux n :=
      match n with
      | 0 => []
      | S n => tInd (mkInd ind n) u :: aux n
      end
  in aux (List.length l).

Module PCUICTermUtils <: TermUtils PCUICTerm PCUICEnvironment.

End PCUICTermUtils.

Module PCUICEnvTyping := EnvironmentTyping.EnvTyping PCUICTerm PCUICEnvironment PCUICTermUtils.

Module PCUICConversion := EnvironmentTyping.Conversion PCUICTerm PCUICEnvironment PCUICTermUtils PCUICEnvTyping.

Module PCUICLookup := EnvironmentTyping.Lookup PCUICTerm PCUICEnvironment.
Include PCUICLookup.

Module PCUICGlobalMaps := EnvironmentTyping.GlobalMaps
  PCUICTerm
  PCUICEnvironment
  PCUICTermUtils
  PCUICEnvTyping
  PCUICConversion
  PCUICLookup
.
Definition set_preturn (p : predicate term) (pret' : term) : predicate term.
Admitted.
Definition set_pparams (p : predicate term) (pars' : list term) : predicate term.
Admitted.

Fixpoint decompose_app_rec (t : term) l :=
  match t with
  | tApp f a => decompose_app_rec f (a :: l)
  | _ => (t, l)
  end.

Definition decompose_app t := decompose_app_rec t [].

Definition isConstruct_app t :=
  match fst (decompose_app t) with
  | tConstruct _ _ _ => true
  | _ => false
  end.
Fixpoint decompose_prod_assum (Γ : context) (t : term) : context * term.
Admitted.

Coercion ci_ind : case_info >-> inductive.

Definition ind_predicate_context ind mdecl idecl : context :=
  let ictx := (expand_lets_ctx mdecl.(ind_params) idecl.(ind_indices)) in
  let indty := mkApps (tInd ind (abstract_instance mdecl.(ind_universes)))
    (to_extended_list (smash_context [] mdecl.(ind_params) ,,, ictx)) in
  let inddecl :=
    {| decl_name :=
      {| binder_name := nNamed (ind_name idecl); binder_relevance := idecl.(ind_relevance) |};
       decl_body := None;
       decl_type := indty |}
  in (inddecl :: ictx).

Definition inst_case_context params puinst (pctx : context) :=
  subst_context (List.rev params) 0 (subst_instance puinst pctx).

Definition inst_case_predicate_context (p : predicate term) :=
  inst_case_context p.(pparams) p.(puinst) p.(pcontext).

Definition inst_case_branch_context (p : predicate term) (br : branch term) :=
  inst_case_context p.(pparams) p.(puinst) br.(bcontext).

Definition iota_red npar p args br :=
  subst (List.rev (List.skipn npar args)) 0
    (expand_lets (inst_case_branch_context p br) (bbody br)).

Definition pre_case_predicate_context_gen ind mdecl idecl params puinst : context :=
  inst_case_context params puinst (ind_predicate_context ind mdecl idecl).

Definition case_predicate_context_gen ind mdecl idecl params puinst pctx :=
  map2 set_binder_name pctx (pre_case_predicate_context_gen ind mdecl idecl params puinst).

Definition case_predicate_context ind mdecl idecl p : context :=
  case_predicate_context_gen ind mdecl idecl p.(pparams) p.(puinst) (forget_types p.(pcontext)).

Definition cstr_branch_context ind mdecl cdecl : context :=
  expand_lets_ctx mdecl.(ind_params)
    (subst_context (inds (inductive_mind ind) (abstract_instance mdecl.(ind_universes))
       mdecl.(ind_bodies)) #|mdecl.(ind_params)|
      cdecl.(cstr_args)).

Definition pre_case_branch_context_gen ind mdecl cdecl params puinst : context :=
  inst_case_context params puinst (cstr_branch_context ind mdecl cdecl).

Definition case_branch_context_gen ind mdecl params puinst pctx cdecl :=
  map2 set_binder_name pctx (pre_case_branch_context_gen ind mdecl cdecl params puinst).

Definition case_branch_type_gen ind mdecl (idecl : one_inductive_body) params puinst bctx ptm i cdecl : context * term :=
  let cstr := tConstruct ind i puinst in
  let args := to_extended_list cdecl.(cstr_args) in
  let cstrapp := mkApps cstr (map (lift0 #|cdecl.(cstr_args)|) params ++ args) in
  let brctx := case_branch_context_gen ind mdecl params puinst bctx cdecl in
  let upars := subst_instance puinst mdecl.(ind_params) in
  let indices :=
    (map (subst (List.rev params) #|cdecl.(cstr_args)|)
      (map (expand_lets_k upars #|cdecl.(cstr_args)|)
        (map (subst (inds (inductive_mind ind) puinst mdecl.(ind_bodies))
                    (#|mdecl.(ind_params)| + #|cdecl.(cstr_args)|))
          (map (subst_instance puinst) cdecl.(cstr_indices))))) in
  let ty := mkApps (lift0 #|cdecl.(cstr_args)| ptm) (indices ++ [cstrapp]) in
  (brctx, ty).

Definition case_branch_type ind mdecl idecl p (b : branch term) ptm i cdecl : context * term :=
  case_branch_type_gen ind mdecl idecl p.(pparams) p.(puinst) (forget_types b.(bcontext)) ptm i cdecl.

Definition idecl_binder idecl :=
  {| decl_name :=
    {| binder_name := nNamed idecl.(ind_name);
        binder_relevance := idecl.(ind_relevance) |};
     decl_body := None;
     decl_type := idecl.(ind_type) |}.

Definition wf_predicate_gen mdecl idecl (pparams : list term) (pcontext : list aname) : Prop :=
  let decl := idecl_binder idecl in
  (#|pparams| = mdecl.(ind_npars)) /\
  (Forall2 (fun na decl => eq_binder_annot na decl.(decl_name))
    pcontext (decl :: idecl.(ind_indices))).

Definition wf_predicate mdecl idecl (p : predicate term) : Prop :=
  wf_predicate_gen mdecl idecl p.(pparams) (forget_types p.(pcontext)).

Definition wf_branch_gen cdecl (bctx : list aname) : Prop :=
  (Forall2 (fun na decl => eq_binder_annot na decl.(decl_name))
    bctx cdecl.(cstr_args)).

Definition wf_branch cdecl (b : branch term) : Prop :=
  wf_branch_gen cdecl (forget_types b.(bcontext)).

Definition wf_branches idecl (brs : list (branch term)) : Prop :=
  Forall2 wf_branch idecl.(ind_ctors) brs.

Definition fix_subst (l : mfixpoint term) :=
  let fix aux n :=
      match n with
      | 0 => []
      | S n => tFix l n :: aux n
      end
  in aux (List.length l).

Definition unfold_fix (mfix : mfixpoint term) (idx : nat) :=
  match List.nth_error mfix idx with
  | Some d => Some (d.(rarg), subst0 (fix_subst mfix) d.(dbody))
  | None => None
  end.

Definition cofix_subst (l : mfixpoint term) :=
  let fix aux n :=
      match n with
      | 0 => []
      | S n => tCoFix l n :: aux n
      end
  in aux (List.length l).

Definition unfold_cofix (mfix : mfixpoint term) (idx : nat) :=
  match List.nth_error mfix idx with
  | Some d => Some (d.(rarg), subst0 (cofix_subst mfix) d.(dbody))
  | None => None
  end.

Definition is_constructor n ts :=
  match List.nth_error ts n with
  | Some a => isConstruct_app a
  | None => false
  end.

Definition R_universe_instance R :=
  fun u u' => Forall2 R (List.map Universe.make u) (List.map Universe.make u').

Definition R_universe_variance (Re Rle : Universe.t -> Universe.t -> Prop) v u u' :=
  match v with
  | Variance.Irrelevant => True
  | Variance.Covariant => Rle (Universe.make u) (Universe.make u')
  | Variance.Invariant => Re (Universe.make u) (Universe.make u')
  end.

Fixpoint R_universe_instance_variance Re Rle v u u' :=
  match u, u' return Prop with
  | u :: us, u' :: us' =>
    match v with
    | [] => R_universe_instance_variance Re Rle v us us'

    | v :: vs => R_universe_variance Re Rle v u u' /\
        R_universe_instance_variance Re Rle vs us us'
    end
  | [], [] => True
  | _, _ => False
  end.

Definition global_variance_gen lookup gr napp :=
  match gr with
  | IndRef ind =>
    match lookup_inductive_gen lookup ind with
    | Some (mdecl, idecl) =>
      match destArity [] idecl.(ind_type) with
      | Some (ctx, _) => if (context_assumptions ctx) <=? napp then mdecl.(ind_variance)
        else None
      | None => None
      end
    | None => None
    end
  | ConstructRef ind k =>
    match lookup_constructor_gen lookup ind k with
    | Some (mdecl, idecl, cdecl) =>
      if (cdecl.(cstr_arity) + mdecl.(ind_npars))%nat <=? napp then

        Some []
      else None
    | _ => None
    end
  | _ => None
  end.

Definition R_opt_variance Re Rle v :=
  match v with
  | Some v => R_universe_instance_variance Re Rle v
  | None => R_universe_instance Re
  end.

Definition R_global_instance_gen Σ Re Rle gr napp :=
  R_opt_variance Re Rle (global_variance_gen Σ gr napp).

Notation R_global_instance Σ := (R_global_instance_gen (lookup_env Σ)).

Section compare_decls.

  Context {eq_term leq_term : term -> term -> Type}.
  Inductive compare_decls  : context_decl -> context_decl -> Type :=
  | compare_vass {na T na' T'} :
    eq_binder_annot na na' ->
    leq_term T T' ->
    compare_decls (vass na T) (vass na' T')
  | compare_vdef {na b T na' b' T'} :
    eq_binder_annot na na' ->
    eq_term b b' ->
    leq_term T T' ->
    compare_decls (vdef na b T) (vdef na' b' T').
End compare_decls.
Arguments compare_decls : clear implicits.

Notation eq_context_upto_names := (All2 (compare_decls eq eq)).

Notation eq_context_gen eq_term leq_term :=
  (All2_fold (fun _ _ => compare_decls eq_term leq_term)).

Definition eq_predicate (eq_term : term -> term -> Type) Re p p' :=
  All2 eq_term p.(pparams) p'.(pparams) *
  (R_universe_instance Re p.(puinst) p'.(puinst) *
  ((eq_context_gen eq eq p.(pcontext) p'.(pcontext)) *
    eq_term p.(preturn) p'.(preturn))).

Reserved Notation " Σ ⊢ t <==[ Rle , napp ] u" (at level 50, t, u at next level,
  format "Σ  ⊢  t  <==[ Rle , napp ]  u").

Inductive eq_term_upto_univ_napp Σ (Re Rle : Universe.t -> Universe.t -> Prop) (napp : nat) : term -> term -> Type :=
| eq_Rel : forall n,
    Σ ⊢ tRel n <==[ Rle , napp ] tRel n

| eq_Evar : forall e args args',
    All2 (eq_term_upto_univ_napp Σ Re Re 0) args args' ->
    Σ ⊢ tEvar e args <==[ Rle , napp ] tEvar e args'

| eq_Var : forall id,
    Σ ⊢ tVar id <==[ Rle , napp ] tVar id

| eq_Sort : forall s s',
    Rle s s' ->
    Σ ⊢ tSort s  <==[ Rle , napp ] tSort s'

| eq_App : forall t t' u u',
    Σ ⊢ t <==[ Rle , S napp ] t' ->
    Σ ⊢ u <==[ Re , 0 ] u' ->
    Σ ⊢ tApp t u <==[ Rle , napp ] tApp t' u'

| eq_Const : forall c u u',
    R_universe_instance Re u u' ->
    Σ ⊢ tConst c u <==[ Rle , napp ] tConst c u'

| eq_Ind : forall i u u',
    R_global_instance Σ Re Rle (IndRef i) napp u u' ->
    Σ ⊢ tInd i u <==[ Rle , napp ] tInd i u'

| eq_Construct : forall i k u u',
    R_global_instance Σ Re Rle (ConstructRef i k) napp u u' ->
    Σ ⊢ tConstruct i k u <==[ Rle , napp ] tConstruct i k u'

| eq_Lambda : forall na na' ty ty' t t',
    eq_binder_annot na na' ->
    Σ ⊢ ty <==[ Re , 0 ] ty' ->
    Σ ⊢ t <==[ Rle , 0 ] t' ->
    Σ ⊢ tLambda na ty t <==[ Rle , napp ] tLambda na' ty' t'

| eq_Prod : forall na na' a a' b b',
    eq_binder_annot na na' ->
    Σ ⊢ a <==[ Re , 0 ] a' ->
    Σ ⊢ b <==[ Rle , 0 ] b' ->
    Σ ⊢ tProd na a b <==[ Rle , napp ] tProd na' a' b'

| eq_LetIn : forall na na' t t' ty ty' u u',
    eq_binder_annot na na' ->
    Σ ⊢ t <==[ Re , 0 ] t' ->
    Σ ⊢ ty <==[ Re , 0 ] ty' ->
    Σ ⊢ u <==[ Rle , 0 ] u' ->
    Σ ⊢ tLetIn na t ty u <==[ Rle , napp ] tLetIn na' t' ty' u'

| eq_Case : forall indn p p' c c' brs brs',
    eq_predicate (eq_term_upto_univ_napp Σ Re Re 0) Re p p' ->
    Σ ⊢ c <==[ Re , 0 ] c' ->
    All2 (fun x y =>
      eq_context_gen eq eq (bcontext x) (bcontext y) *
      (Σ ⊢ x.(bbody) <==[ Re , 0 ] y.(bbody))
    ) brs brs' ->
    Σ ⊢ tCase indn p c brs <==[ Rle , napp ] tCase indn p' c' brs'

| eq_Proj : forall p c c',
    Σ ⊢ c <==[ Re , 0 ] c' ->
    Σ ⊢ tProj p c <==[ Rle , napp ] tProj p c'

| eq_Fix : forall mfix mfix' idx,
    All2 (fun x y =>
      (Σ ⊢ x.(dtype) <==[ Re , 0 ] y.(dtype)) *
      (Σ ⊢ x.(dbody) <==[ Re , 0 ] y.(dbody)) *
      (x.(rarg) = y.(rarg)) *
      eq_binder_annot x.(dname) y.(dname)
    )%type mfix mfix' ->
    Σ ⊢ tFix mfix idx <==[ Rle , napp ] tFix mfix' idx

| eq_CoFix : forall mfix mfix' idx,
    All2 (fun x y =>
      (Σ ⊢ x.(dtype) <==[ Re , 0 ] y.(dtype)) *
      (Σ ⊢ x.(dbody) <==[ Re , 0 ] y.(dbody)) *
      (x.(rarg) = y.(rarg)) *
      eq_binder_annot x.(dname) y.(dname)
    ) mfix mfix' ->
    Σ ⊢ tCoFix mfix idx <==[ Rle , napp ] tCoFix mfix' idx

| eq_Prim i : eq_term_upto_univ_napp Σ Re Rle napp (tPrim i) (tPrim i)
where " Σ ⊢ t <==[ Rle , napp ] u " := (eq_term_upto_univ_napp Σ _ Rle napp t u) : type_scope.

Notation eq_term_upto_univ Σ Re Rle := (eq_term_upto_univ_napp Σ Re Rle 0).

Definition compare_term `{checker_flags} (pb : conv_pb) Σ φ (t u : term) :=
  eq_term_upto_univ Σ (eq_universe φ) (compare_universe pb φ) t u.

Reserved Notation " Σ ;;; Γ |- t ⇝ u " (at level 50, Γ, t, u at next level).

Inductive red1 (Σ : global_env) (Γ : context) : term -> term -> Type :=

| red_beta na t b a :
  Σ ;;; Γ |- tApp (tLambda na t b) a ⇝ b {0 := a}

| red_zeta na b t b' :
  Σ ;;; Γ |- tLetIn na b t b' ⇝ b' {0 := b}

| red_rel i body :
    option_map decl_body (nth_error Γ i) = Some (Some body) ->
    Σ ;;; Γ |- tRel i ⇝ lift0 (S i) body

| red_iota ci c u args p brs br :
    nth_error brs c = Some br ->
    #|args| = (ci.(ci_npar) + context_assumptions br.(bcontext))%nat ->
    Σ ;;; Γ |- tCase ci p (mkApps (tConstruct ci.(ci_ind) c u) args) brs
        ⇝ iota_red ci.(ci_npar) p args br

| red_fix mfix idx args narg fn :
    unfold_fix mfix idx = Some (narg, fn) ->
    is_constructor narg args = true ->
    Σ ;;; Γ |- mkApps (tFix mfix idx) args ⇝ mkApps fn args

| red_cofix_case ip p mfix idx args narg fn brs :
    unfold_cofix mfix idx = Some (narg, fn) ->
    Σ ;;; Γ |- tCase ip p (mkApps (tCoFix mfix idx) args) brs ⇝
         tCase ip p (mkApps fn args) brs

| red_cofix_proj p mfix idx args narg fn :
    unfold_cofix mfix idx = Some (narg, fn) ->
    Σ ;;; Γ |- tProj p (mkApps (tCoFix mfix idx) args) ⇝ tProj p (mkApps fn args)

| red_delta c decl body (isdecl : declared_constant Σ c decl) u :
    decl.(cst_body) = Some body ->
    Σ ;;; Γ |- tConst c u ⇝ subst_instance u body

| red_proj p args u arg:
    nth_error args (p.(proj_npars) + p.(proj_arg)) = Some arg ->
    Σ ;;; Γ |- tProj p (mkApps (tConstruct p.(proj_ind) 0 u) args) ⇝ arg

| abs_red_l na M M' N : Σ ;;; Γ |- M ⇝ M' -> Σ ;;; Γ |- tLambda na M N ⇝ tLambda na M' N
| abs_red_r na M M' N : Σ ;;; Γ ,, vass na N |- M ⇝ M' -> Σ ;;; Γ |- tLambda na N M ⇝ tLambda na N M'

| letin_red_def na b t b' r : Σ ;;; Γ |- b ⇝ r -> Σ ;;; Γ |- tLetIn na b t b' ⇝ tLetIn na r t b'
| letin_red_ty na b t b' r : Σ ;;; Γ |- t ⇝ r -> Σ ;;; Γ |- tLetIn na b t b' ⇝ tLetIn na b r b'
| letin_red_body na b t b' r : Σ ;;; Γ ,, vdef na b t |- b' ⇝ r -> Σ ;;; Γ |- tLetIn na b t b' ⇝ tLetIn na b t r

| case_red_param ci p params' c brs :
    OnOne2 (fun t u => Σ ;;; Γ |- t ⇝ u) p.(pparams) params' ->
    Σ ;;; Γ |- tCase ci p c brs ⇝ tCase ci (set_pparams p params') c brs

| case_red_return ci p preturn' c brs :
  Σ ;;; Γ ,,, inst_case_predicate_context p |- p.(preturn) ⇝ preturn' ->
  Σ ;;; Γ |- tCase ci p c brs ⇝ tCase ci (set_preturn p preturn') c brs

| case_red_discr ci p c c' brs :
  Σ ;;; Γ |- c ⇝ c' -> Σ ;;; Γ |- tCase ci p c brs ⇝ tCase ci p c' brs

| case_red_brs ci p c brs brs' :
    OnOne2 (fun br br' =>
      on_Trel_eq (fun t u => Σ ;;; Γ ,,, inst_case_branch_context p br |- t ⇝ u) bbody bcontext br br')
      brs brs' ->
    Σ ;;; Γ |- tCase ci p c brs ⇝ tCase ci p c brs'

| proj_red p c c' : Σ ;;; Γ |- c ⇝ c' -> Σ ;;; Γ |- tProj p c ⇝ tProj p c'

| app_red_l M1 N1 M2 : Σ ;;; Γ |- M1 ⇝ N1 -> Σ ;;; Γ |- tApp M1 M2 ⇝ tApp N1 M2
| app_red_r M2 N2 M1 : Σ ;;; Γ |- M2 ⇝ N2 -> Σ ;;; Γ |- tApp M1 M2 ⇝ tApp M1 N2

| prod_red_l na M1 M2 N1 : Σ ;;; Γ |- M1 ⇝ N1 -> Σ ;;; Γ |- tProd na M1 M2 ⇝ tProd na N1 M2
| prod_red_r na M2 N2 M1 : Σ ;;; Γ ,, vass na M1 |- M2 ⇝ N2 ->
                           Σ ;;; Γ |- tProd na M1 M2 ⇝ tProd na M1 N2

| evar_red ev l l' : OnOne2 (fun t u => Σ ;;; Γ |- t ⇝ u) l l' -> Σ ;;; Γ |- tEvar ev l ⇝ tEvar ev l'

| fix_red_ty mfix0 mfix1 idx :
    OnOne2 (on_Trel_eq (fun t u => Σ ;;; Γ |- t ⇝ u) dtype (fun x => (dname x, dbody x, rarg x))) mfix0 mfix1 ->
    Σ ;;; Γ |- tFix mfix0 idx ⇝ tFix mfix1 idx

| fix_red_body mfix0 mfix1 idx :
    OnOne2 (on_Trel_eq (fun t u => Σ ;;; Γ ,,, fix_context mfix0 |- t ⇝ u) dbody (fun x => (dname x, dtype x, rarg x)))
           mfix0 mfix1 ->
    Σ ;;; Γ |- tFix mfix0 idx ⇝ tFix mfix1 idx

| cofix_red_ty mfix0 mfix1 idx :
    OnOne2 (on_Trel_eq (fun t u => Σ ;;; Γ |- t ⇝ u) dtype (fun x => (dname x, dbody x, rarg x))) mfix0 mfix1 ->
    Σ ;;; Γ |- tCoFix mfix0 idx ⇝ tCoFix mfix1 idx

| cofix_red_body mfix0 mfix1 idx :
    OnOne2 (on_Trel_eq (fun t u => Σ ;;; Γ ,,, fix_context mfix0 |- t ⇝ u) dbody (fun x => (dname x, dtype x, rarg x))) mfix0 mfix1 ->
    Σ ;;; Γ |- tCoFix mfix0 idx ⇝ tCoFix mfix1 idx
where " Σ ;;; Γ |- t ⇝ u " := (red1 Σ Γ t u).

Reserved Notation " Σ ;;; Γ |- t <=[ pb ] u" (at level 50, Γ, t, u at next level,
  format "Σ  ;;;  Γ  |-  t  <=[ pb ] u").

Notation " Σ ⊢ t <===[ pb ] u" := (compare_term pb Σ Σ t u) (at level 50, t, u at next level).

Inductive cumulAlgo_gen `{checker_flags} (Σ : global_env_ext) (Γ : context) (pb : conv_pb) : term -> term -> Type :=
| cumul_refl t u : Σ ⊢ t <===[ pb ] u -> Σ ;;; Γ |- t <=[pb] u
| cumul_red_l t u v : Σ ;;; Γ |- t ⇝ v -> Σ ;;; Γ |- v <=[pb] u -> Σ ;;; Γ |- t <=[pb] u
| cumul_red_r t u v : Σ ;;; Γ |- t <=[pb] v -> Σ ;;; Γ |- u ⇝ v -> Σ ;;; Γ |- t <=[pb] u
where " Σ ;;; Γ |- t <=[ pb ] u " := (cumulAlgo_gen Σ Γ pb t u) : type_scope.
Notation " Σ ;;; Γ |- t <= u " := (cumulAlgo_gen Σ Γ Cumul t u) (at level 50, Γ, t, u at next level) : type_scope.

Definition shiftnP k p i :=
  (i <? k) || p (i - k).
Fixpoint on_free_vars (p : nat -> bool) (t : term) : bool.
Admitted.

Definition on_free_vars_decl P d :=
  test_decl (on_free_vars P) d.

Definition on_free_vars_ctx P ctx :=
  alli (fun k => (on_free_vars_decl (shiftnP k P))) 0 (List.rev ctx).

Notation is_open_term Γ := (on_free_vars (shiftnP #|Γ| xpred0)).
Notation is_closed_context := (on_free_vars_ctx xpred0).
Module Export PCUICCumulativitySpec.

Implicit Types (cf : checker_flags).

Definition cumul_predicate (cumul : context -> term -> term -> Type) Γ Re p p' :=
  All2 (cumul Γ) p.(pparams) p'.(pparams) *
  (R_universe_instance Re p.(puinst) p'.(puinst) *
  ((eq_context_gen eq eq p.(pcontext) p'.(pcontext)) *
    cumul (Γ ,,, inst_case_predicate_context p) p.(preturn) p'.(preturn))).

Reserved Notation " Σ ;;; Γ ⊢ t ≤s[ pb ] u" (at level 50, Γ, t, u at next level,
  format "Σ  ;;;  Γ  ⊢  t  ≤s[ pb ]  u").

Definition cumul_Ind_univ {cf} (Σ : global_env_ext) pb i napp :=
  R_global_instance Σ (eq_universe Σ) (compare_universe pb Σ) (IndRef i) napp.

Definition cumul_Construct_univ {cf} (Σ : global_env_ext) pb  i k napp :=
  R_global_instance Σ (eq_universe Σ) (compare_universe pb Σ) (ConstructRef i k) napp.
Inductive cumulSpec0 {cf : checker_flags} (Σ : global_env_ext) Γ (pb : conv_pb) : term -> term -> Type :=

| cumul_Trans : forall t u v,
    is_closed_context Γ -> is_open_term Γ u ->
    Σ ;;; Γ ⊢ t ≤s[pb] u ->
    Σ ;;; Γ ⊢ u ≤s[pb] v ->
    Σ ;;; Γ ⊢ t ≤s[pb] v

| cumul_Sym : forall t u,
    Σ ;;; Γ ⊢ t ≤s[Conv] u ->
    Σ ;;; Γ ⊢ u ≤s[pb] t

| cumul_Refl : forall t,
    Σ ;;; Γ ⊢ t ≤s[pb] t

| cumul_Ind : forall i u u' args args',
    cumul_Ind_univ Σ pb i #|args| u u' ->
    All2 (fun t u => Σ ;;; Γ ⊢ t ≤s[Conv] u) args args' ->
    Σ ;;; Γ ⊢ mkApps (tInd i u) args ≤s[pb] mkApps (tInd i u') args'

| cumul_Construct : forall i k u u' args args',
    cumul_Construct_univ Σ pb i k #|args| u u' ->
    All2 (fun t u => Σ ;;; Γ ⊢ t ≤s[Conv] u) args args' ->
    Σ ;;; Γ ⊢ mkApps (tConstruct i k u) args ≤s[pb] mkApps (tConstruct i k u') args'

| cumul_Sort : forall s s',
    compare_universe pb Σ s s' ->
    Σ ;;; Γ ⊢ tSort s ≤s[pb] tSort s'

| cumul_Const : forall c u u',
    R_universe_instance (compare_universe Conv Σ) u u' ->
    Σ ;;; Γ ⊢ tConst c u ≤s[pb] tConst c u'

| cumul_Evar : forall e args args',
    All2 (fun t u => Σ ;;; Γ ⊢ t ≤s[Conv] u) args args' ->
    Σ ;;; Γ ⊢ tEvar e args ≤s[pb] tEvar e args'

| cumul_App : forall t t' u u',
    Σ ;;; Γ ⊢ t ≤s[pb] t' ->
    Σ ;;; Γ ⊢ u ≤s[Conv] u' ->
    Σ ;;; Γ ⊢ tApp t u ≤s[pb] tApp t' u'

| cumul_Lambda : forall na na' ty ty' t t',
    eq_binder_annot na na' ->
    Σ ;;; Γ ⊢ ty ≤s[Conv] ty' ->
    Σ ;;; Γ ,, vass na ty ⊢ t ≤s[pb] t' ->
    Σ ;;; Γ ⊢ tLambda na ty t ≤s[pb] tLambda na' ty' t'

| cumul_Prod : forall na na' a a' b b',
    eq_binder_annot na na' ->
    Σ ;;; Γ ⊢ a ≤s[Conv] a' ->
    Σ ;;; Γ ,, vass na a ⊢ b ≤s[pb] b' ->
    Σ ;;; Γ ⊢ tProd na a b ≤s[pb] tProd na' a' b'

| cumul_LetIn : forall na na' t t' ty ty' u u',
    eq_binder_annot na na' ->
    Σ ;;; Γ ⊢ t ≤s[Conv] t' ->
    Σ ;;; Γ ⊢ ty ≤s[Conv] ty' ->
    Σ ;;; Γ ,, vdef na t ty ⊢ u ≤s[pb] u' ->
    Σ ;;; Γ ⊢ tLetIn na t ty u ≤s[pb] tLetIn na' t' ty' u'

| cumul_Case indn : forall p p' c c' brs brs',
    cumul_predicate (fun Γ t u => Σ ;;; Γ ⊢ t ≤s[Conv] u) Γ (compare_universe Conv Σ) p p' ->
    Σ ;;; Γ ⊢ c ≤s[Conv] c' ->
    All2 (fun br br' =>
      eq_context_gen eq eq (bcontext br) (bcontext br') ×
      Σ ;;; Γ ,,, inst_case_branch_context p br ⊢ bbody br ≤s[Conv] bbody br'
    ) brs brs' ->
    Σ ;;; Γ ⊢ tCase indn p c brs ≤s[pb] tCase indn p' c' brs'

| cumul_Proj : forall p c c',
    Σ ;;; Γ ⊢ c ≤s[Conv] c' ->
    Σ ;;; Γ ⊢ tProj p c ≤s[pb] tProj p c'

| cumul_Fix : forall mfix mfix' idx,
    All2 (fun x y =>
      Σ ;;; Γ ⊢ x.(dtype) ≤s[Conv] y.(dtype) ×
      Σ ;;; Γ ,,, fix_context mfix ⊢ x.(dbody) ≤s[Conv] y.(dbody) ×
      (x.(rarg) = y.(rarg)) ×
      eq_binder_annot x.(dname) y.(dname)
    ) mfix mfix' ->
    Σ ;;; Γ ⊢ tFix mfix idx ≤s[pb] tFix mfix' idx

| cumul_CoFix : forall mfix mfix' idx,
    All2 (fun x y =>
      Σ ;;; Γ ⊢ x.(dtype) ≤s[Conv] y.(dtype) ×
      Σ ;;; Γ ,,, fix_context mfix ⊢ x.(dbody) ≤s[Conv] y.(dbody) ×
      (x.(rarg) = y.(rarg)) ×
      eq_binder_annot x.(dname) y.(dname)
    ) mfix mfix' ->
    Σ ;;; Γ ⊢ tCoFix mfix idx ≤s[pb] tCoFix mfix' idx

| cumul_beta : forall na t b a,
    Σ ;;; Γ ⊢ tApp (tLambda na t b) a ≤s[pb] b {0 := a}

| cumul_zeta : forall na b t b',
    Σ ;;; Γ ⊢ tLetIn na b t b' ≤s[pb] b' {0 := b}

| cumul_rel i body :
    option_map decl_body (nth_error Γ i) = Some (Some body) ->
    Σ ;;; Γ ⊢ tRel i ≤s[pb] lift0 (S i) body

| cumul_iota : forall ci c u args p brs br,
    nth_error brs c = Some br ->
    #|args| = (ci.(ci_npar) + context_assumptions br.(bcontext))%nat ->
    Σ ;;; Γ ⊢ tCase ci p (mkApps (tConstruct ci.(ci_ind) c u) args) brs  ≤s[pb] iota_red ci.(ci_npar) p args br

| cumul_fix : forall mfix idx args narg fn,
    unfold_fix mfix idx = Some (narg, fn) ->
    is_constructor narg args = true ->
    Σ ;;; Γ ⊢ mkApps (tFix mfix idx) args ≤s[pb] mkApps fn args

| cumul_cofix_case : forall ip p mfix idx args narg fn brs,
    unfold_cofix mfix idx = Some (narg, fn) ->
    Σ ;;; Γ ⊢ tCase ip p (mkApps (tCoFix mfix idx) args) brs ≤s[pb] tCase ip p (mkApps fn args) brs

| cumul_cofix_proj : forall p mfix idx args narg fn,
    unfold_cofix mfix idx = Some (narg, fn) ->
    Σ ;;; Γ ⊢ tProj p (mkApps (tCoFix mfix idx) args) ≤s[pb] tProj p (mkApps fn args)

| cumul_delta : forall c decl body (isdecl : declared_constant Σ c decl) u,
    decl.(cst_body) = Some body ->
    Σ ;;; Γ ⊢ tConst c u ≤s[pb] body@[u]

| cumul_proj : forall p args u arg,
    nth_error args (p.(proj_npars) + p.(proj_arg)) = Some arg ->
    Σ ;;; Γ ⊢ tProj p (mkApps (tConstruct p.(proj_ind) 0 u) args) ≤s[pb] arg

where " Σ ;;; Γ ⊢ t ≤s[ pb ] u " := (@cumulSpec0 _ Σ Γ pb t u) : type_scope.
Definition cumulSpec `{checker_flags} (Σ : global_env_ext) Γ := cumulSpec0 Σ Γ Cumul.

Notation " Σ ;;; Γ |- t <=s u " := (@cumulSpec _ Σ Γ t u) (at level 50, Γ, t, u at next level).

Module PCUICConversionParSpec <: EnvironmentTyping.ConversionParSig PCUICTerm PCUICEnvironment PCUICTermUtils PCUICEnvTyping.
  Definition cumul_gen := @cumulSpec0.
End PCUICConversionParSpec.

End PCUICCumulativitySpec.
Module Export PCUICTyping.

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

Definition type_of_constructor mdecl (cdecl : constructor_body) (c : inductive * nat) (u : list Level.t) :=
  let mind := inductive_mind (fst c) in
  subst0 (inds mind u mdecl.(ind_bodies)) (subst_instance u (cstr_type cdecl)).

Include PCUICEnvTyping.

Inductive FixCoFix : Type := Fix | CoFix.

Class GuardChecker :=
{
  guard : FixCoFix -> global_env_ext -> context -> mfixpoint term -> Prop ;
}.

Axiom guard_checking : GuardChecker.
#[global]
Existing Instance guard_checking.

Definition fix_guard := guard Fix.
Definition cofix_guard := guard CoFix.

Definition destInd (t : term) :=
  match t with
  | tInd ind u => Some (ind, u)
  | _ => None
  end.

Definition isCoFinite (r : recursivity_kind) :=
  match r with
  | CoFinite => true
  | _ => false
  end.

Definition check_recursivity_kind
  (lookup: kername -> option global_decl) ind r :=
  match lookup ind with
  | Some (InductiveDecl mib) => ReflectEq.eqb mib.(ind_finite) r
  | _ => false
  end.

Definition check_one_fix d :=
  let '{| dname := na;
         dtype := ty;
         dbody := b;
         rarg := arg |} := d in
  let '(ctx, ty) := decompose_prod_assum [] ty in
  match nth_error (List.rev (smash_context [] ctx)) arg with
  | Some argd =>
    let (hd, args) := decompose_app argd.(decl_type) in
    match destInd hd with
    | Some (mkInd mind _, u) => Some mind
    | None => None
    end
  | None => None
  end.

Definition wf_fixpoint_gen
  (lookup: kername -> option global_decl) mfix :=
  forallb (isLambda ∘ dbody) mfix &&
  let checks := map check_one_fix mfix in
  match map_option_out checks with
  | Some (ind :: inds) =>

    forallb (eqb ind) inds &&
    check_recursivity_kind lookup ind Finite
  | _ => false
  end.

Definition wf_fixpoint (Σ : global_env) := wf_fixpoint_gen (lookup_env Σ).

Definition check_one_cofix d :=
  let '{| dname := na;
         dtype := ty;
         dbody := b;
         rarg := arg |} := d in
  let '(ctx, ty) := decompose_prod_assum [] ty in
  let (hd, args) := decompose_app ty in
  match destInd hd with
  | Some (mkInd ind _, u) => Some ind
  | None => None
  end.

Definition wf_cofixpoint_gen
  (lookup: kername -> option global_decl) mfix :=
  let checks := map check_one_cofix mfix in
  match map_option_out checks with
  | Some (ind :: inds) =>

    forallb (eqb ind) inds &&
    check_recursivity_kind lookup ind CoFinite
  | _ => false
  end.

Definition wf_cofixpoint (Σ : global_env) := wf_cofixpoint_gen (lookup_env Σ).

Reserved Notation "'wf_local' Σ Γ " (at level 9, Σ, Γ at next level).

Reserved Notation " Σ ;;; Γ |- t : T " (at level 50, Γ, t, T at next level).

Variant case_side_conditions `{checker_flags} wf_local_fun typing Σ Γ ci p ps mdecl idecl indices predctx :=
| case_side_info
    (eq_npars : mdecl.(ind_npars) = ci.(ci_npar))
    (wf_pred : wf_predicate mdecl idecl p)
    (cons : consistent_instance_ext Σ (ind_universes mdecl) p.(puinst))
    (wf_pctx : wf_local_fun Σ (Γ ,,, predctx))

    (conv_pctx : eq_context_upto_names p.(pcontext) (ind_predicate_context ci.(ci_ind) mdecl idecl))
    (allowed_elim : is_allowed_elimination Σ idecl.(ind_kelim) ps)
    (ind_inst : ctx_inst typing Σ Γ (p.(pparams) ++ indices)
                         (List.rev (subst_instance p.(puinst)
                                                   (ind_params mdecl ,,, ind_indices idecl))))
    (not_cofinite : isCoFinite mdecl.(ind_finite) = false).

Variant case_branch_typing `{checker_flags} wf_local_fun typing Σ Γ (ci:case_info) p ps mdecl idecl ptm  brs :=
| case_branch_info
    (wf_brs : wf_branches idecl brs)
    (brs_ty :
       All2i (fun i cdecl br =>

                eq_context_upto_names br.(bcontext) (cstr_branch_context ci mdecl cdecl) ×
                let brctxty := case_branch_type ci.(ci_ind) mdecl idecl p br ptm i cdecl in
                (wf_local_fun Σ (Γ ,,, brctxty.1) ×
                ((typing Σ (Γ ,,, brctxty.1) br.(bbody) (brctxty.2)) ×
                (typing Σ (Γ ,,, brctxty.1) brctxty.2 (tSort ps)))))
             0 idecl.(ind_ctors) brs).

Inductive typing `{checker_flags} (Σ : global_env_ext) (Γ : context) : term -> term -> Type :=
| type_Rel : forall n decl,
    wf_local Σ Γ ->
    nth_error Γ n = Some decl ->
    Σ ;;; Γ |- tRel n : lift0 (S n) decl.(decl_type)

| type_Sort : forall s,
    wf_local Σ Γ ->
    wf_universe Σ s ->
    Σ ;;; Γ |- tSort s : tSort (Universe.super s)

| type_Prod : forall na A B s1 s2,
    Σ ;;; Γ |- A : tSort s1 ->
    Σ ;;; Γ ,, vass na A |- B : tSort s2 ->
    Σ ;;; Γ |- tProd na A B : tSort (Universe.sort_of_product s1 s2)

| type_Lambda : forall na A t s1 B,
    Σ ;;; Γ |- A : tSort s1 ->
    Σ ;;; Γ ,, vass na A |- t : B ->
    Σ ;;; Γ |- tLambda na A t : tProd na A B

| type_LetIn : forall na b B t s1 A,
    Σ ;;; Γ |- B : tSort s1 ->
    Σ ;;; Γ |- b : B ->
    Σ ;;; Γ ,, vdef na b B |- t : A ->
    Σ ;;; Γ |- tLetIn na b B t : tLetIn na b B A

| type_App : forall t na A B s u,

    Σ ;;; Γ |- tProd na A B : tSort s ->
    Σ ;;; Γ |- t : tProd na A B ->
    Σ ;;; Γ |- u : A ->
    Σ ;;; Γ |- tApp t u : B{0 := u}

| type_Const : forall cst u decl,
    wf_local Σ Γ ->
    declared_constant Σ cst decl ->
    consistent_instance_ext Σ decl.(cst_universes) u ->
    Σ ;;; Γ |- tConst cst u : decl.(cst_type)@[u]

| type_Ind : forall ind u mdecl idecl,
    wf_local Σ Γ ->
    declared_inductive Σ ind mdecl idecl ->
    consistent_instance_ext Σ mdecl.(ind_universes) u ->
    Σ ;;; Γ |- tInd ind u : idecl.(ind_type)@[u]

| type_Construct : forall ind i u mdecl idecl cdecl,
    wf_local Σ Γ ->
    declared_constructor Σ (ind, i) mdecl idecl cdecl ->
    consistent_instance_ext Σ mdecl.(ind_universes) u ->
    Σ ;;; Γ |- tConstruct ind i u : type_of_constructor mdecl cdecl (ind, i) u

| type_Case : forall ci p c brs indices ps mdecl idecl,
    let predctx := case_predicate_context ci.(ci_ind) mdecl idecl p in
    let ptm := it_mkLambda_or_LetIn predctx p.(preturn) in
    declared_inductive Σ ci.(ci_ind) mdecl idecl ->
    Σ ;;; Γ ,,, predctx |- p.(preturn) : tSort ps ->
    Σ ;;; Γ |- c : mkApps (tInd ci.(ci_ind) p.(puinst)) (p.(pparams) ++ indices) ->
    case_side_conditions (fun Σ Γ => wf_local Σ Γ) typing Σ Γ ci p ps
                         mdecl idecl indices predctx  ->
    case_branch_typing (fun Σ Γ => wf_local Σ Γ) typing Σ Γ ci p ps
                        mdecl idecl ptm brs ->
    Σ ;;; Γ |- tCase ci p c brs : mkApps ptm (indices ++ [c])

| type_Proj : forall p c u mdecl idecl cdecl pdecl args,
    declared_projection Σ p mdecl idecl cdecl pdecl ->
    Σ ;;; Γ |- c : mkApps (tInd p.(proj_ind) u) args ->
    #|args| = ind_npars mdecl ->
    Σ ;;; Γ |- tProj p c : subst0 (c :: List.rev args) pdecl.(proj_type)@[u]

| type_Fix : forall mfix n decl,
    wf_local Σ Γ ->
    fix_guard Σ Γ mfix ->
    nth_error mfix n = Some decl ->
    All (fun d => {s & Σ ;;; Γ |- d.(dtype) :  tSort s}) mfix ->
    All (fun d => (Σ ;;; Γ ,,, fix_context mfix |- d.(dbody) : lift0 #|fix_context mfix| d.(dtype))) mfix ->
    wf_fixpoint Σ mfix ->
    Σ ;;; Γ |- tFix mfix n : decl.(dtype)

| type_CoFix : forall mfix n decl,
    wf_local Σ Γ ->
    cofix_guard Σ Γ mfix ->
    nth_error mfix n = Some decl ->
    All (fun d => {s & Σ ;;; Γ |- d.(dtype) :  tSort s}) mfix ->
    All (fun d => Σ ;;; Γ ,,, fix_context mfix |- d.(dbody) : lift0 #|fix_context mfix| d.(dtype)) mfix ->
    wf_cofixpoint Σ mfix ->
    Σ ;;; Γ |- tCoFix mfix n : decl.(dtype)

| type_Prim p prim_ty cdecl :
   wf_local Σ Γ ->
   primitive_constant Σ (prim_val_tag p) = Some prim_ty ->
   declared_constant Σ prim_ty cdecl ->
   primitive_invariants cdecl ->
   Σ ;;; Γ |- tPrim p : tConst prim_ty []

| type_Cumul : forall t A B s,
    Σ ;;; Γ |- t : A ->
    Σ ;;; Γ |- B : tSort s ->
    Σ ;;; Γ |- A <=s B ->
    Σ ;;; Γ |- t : B

where " Σ ;;; Γ |- t : T " := (typing Σ Γ t T)
and "'wf_local' Σ Γ " := (All_local_env (lift_typing typing Σ) Γ).

Module PCUICTypingDef <: EnvironmentTyping.Typing PCUICTerm PCUICEnvironment PCUICTermUtils PCUICEnvTyping PCUICConversion PCUICConversionParSpec.

End PCUICTypingDef.

Module PCUICDeclarationTyping :=
  EnvironmentTyping.DeclarationTyping
    PCUICTerm
    PCUICEnvironment
    PCUICTermUtils
    PCUICEnvTyping
    PCUICConversion
    PCUICConversionParSpec
    PCUICTypingDef
    PCUICLookup
    PCUICGlobalMaps.
Include PCUICDeclarationTyping.

Definition wf `{checker_flags} := Forall_decls_typing typing.
Existing Class wf.

End PCUICTyping.
Module Export PCUICWellScopedCumulativity.
Import Coq.Classes.CRelationClasses.

Reserved Notation " Σ ;;; Γ ⊢ t ≤[ pb ] u" (at level 50, Γ, t, u at next level,
  format "Σ  ;;;  Γ  ⊢  t  ≤[ pb ]  u").

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

Inductive ws_cumul_pb {cf} (pb : conv_pb) (Σ : global_env_ext) (Γ : context) : term -> term -> Type :=
| ws_cumul_pb_compare (t u : term) :
  is_closed_context Γ -> is_open_term Γ t -> is_open_term Γ u ->
  compare_term pb Σ.1 (global_ext_constraints Σ) t u -> Σ ;;; Γ ⊢ t ≤[pb] u
| ws_cumul_pb_red_l (t u v : term) :
  is_closed_context Γ ->
  is_open_term Γ t -> is_open_term Γ u -> is_open_term Γ v ->
  red1 Σ Γ t v -> Σ ;;; Γ ⊢ v ≤[pb] u -> Σ ;;; Γ ⊢ t ≤[pb] u
| ws_cumul_pb_red_r (t u v : term) :
  is_closed_context Γ ->
  is_open_term Γ t -> is_open_term Γ u -> is_open_term Γ v ->
  Σ ;;; Γ ⊢ t ≤[pb] v -> red1 Σ Γ u v -> Σ ;;; Γ ⊢ t ≤[pb] u
where " Σ ;;; Γ ⊢ t ≤[ pb ] u " := (ws_cumul_pb pb Σ Γ t u) : type_scope.

Notation " Σ ;;; Γ ⊢ t ≤ u " := (ws_cumul_pb Cumul Σ Γ t u) (at level 50, Γ, t, u at next level,
    format "Σ  ;;;  Γ  ⊢  t  ≤  u") : type_scope.

#[global]
Instance ws_cumul_pb_trans {cf:checker_flags} {pb} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ} :
  Transitive (ws_cumul_pb pb Σ Γ).
Admitted.

End PCUICWellScopedCumulativity.

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

Lemma cumulSpec_typed_cumulAlgo {cf} {Σ} {wfΣ : wf Σ} {Γ : context} {t A B s} :
  Σ ;;; Γ |- t : A ->
  Σ ;;; Γ |- B : tSort s ->
  Σ ;;; Γ |- A <=s B  ->
  Σ ;;; Γ ⊢ A ≤ B.
Admitted.
#[global] Hint Immediate cumulSpec_typed_cumulAlgo : pcuic.

Section Inversion.

  Context {cf : checker_flags}.
  Context (Σ : global_env_ext).
  Context (wfΣ : wf Σ).

  Ltac insum :=
    match goal with
    | |- ∑ x : _, _ =>
      eexists
    end.

  Ltac intimes :=
    match goal with
    | |- _ × _ =>
      split
    end.

  Ltac outsum :=
    match goal with
    | ih : ∑ x : _, _ |- _ =>
      destruct ih as [? ?]
    end.

  Ltac outtimes :=
    match goal with
    | ih : _ × _ |- _ =>
      destruct ih as [? ?]
    end.

  Lemma into_ws_cumul {Γ t T U s} :
    Σ ;;; Γ |- t : T ->
    Σ ;;; Γ |- U : tSort s ->
    Σ ;;; Γ |- T <= U ->
    Σ ;;; Γ ⊢ T ≤ U.
Admitted.

  Lemma typing_ws_cumul_pb le Γ t T :
    Σ ;;; Γ |- t : T ->
    Σ ;;; Γ ⊢ T ≤[le] T.
Admitted.

  Ltac invtac h :=
    dependent induction h ; [
      repeat insum ;
      repeat intimes ;
      [ try first [ eassumption | try reflexivity ] .. | try solve [eapply typing_ws_cumul_pb; econstructor; eauto] ]
    | repeat outsum ;
      repeat outtimes ;
      repeat insum ;
      repeat intimes ;
      [ try first [ eassumption | reflexivity ] ..
      | try etransitivity ; try eassumption;
        try eauto with pcuic;
        try solve [eapply into_ws_cumul; tea] ]
    ].

  Lemma inversion_Rel :
    forall {Γ n T},
      Σ ;;; Γ |- tRel n : T ->
      ∑ decl,
        wf_local Σ Γ ×
        (nth_error Γ n = Some decl) ×
        Σ ;;; Γ ⊢ lift0 (S n) (decl_type decl) ≤ T.
  Proof using wfΣ.
    intros Γ n T h.
invtac h.
  Qed.
