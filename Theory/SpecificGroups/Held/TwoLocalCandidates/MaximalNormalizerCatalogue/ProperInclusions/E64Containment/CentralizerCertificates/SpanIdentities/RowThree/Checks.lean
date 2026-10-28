module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment.CentralizerCertificates.SpanIdentities.LiteralBridge
import Mathlib.Tactic.FinCases
public import Mathlib.Order.Fin.Basic

/-!
# The centralizer-index span of literal Held core candidate 3

A checked right-generator transition table and four-point signatures certify
an injective exhaustive word enumeration. The resulting finite multiplication
computes all singleton centralizers, including every element outside the E64
row. Explicit word witnesses prove that the selected elements generate exactly
row 20. All permutation equalities use the faithful literal Held action.

Source: the original ATLAS words, GLS3 Table 5.3p, and quasithin condition E.
The generator and discovery data in `source/` are untrusted; every finite check
below is performed by the Lean kernel.
-/

@[expose] public section

namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.E64Containment.CentralizerCertificates.SpanCertificates.RowThree
open Subgroup

-- Serial elaboration prevents independent kernel reductions retaining memory together.
set_option Elab.async false

def code (i : Fin 256) : List (Fin 8) :=
  (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then [] else [2, 4, 6]) else (if i.val < 3 then [0] else [4, 5])) else (if i.val < 6 then (if i.val < 5 then [0, 6, 2] else [0, 2, 4, 6]) else (if i.val < 7 then [6, 2] else [0, 4, 5]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then [0, 7, 2] else [4, 6, 7]) else (if i.val < 11 then [0, 2, 7, 4] else [0, 7, 4, 6])) else (if i.val < 14 then (if i.val < 13 then [3, 7, 2] else [6, 7, 0]) else (if i.val < 15 then [2, 3, 7, 4] else [6, 7])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then [6, 1] else [1, 2, 3, 4]) else (if i.val < 19 then [0, 1, 2, 3, 4] else [1, 2, 3, 5])) else (if i.val < 22 then (if i.val < 21 then [0, 1, 2, 3, 5] else [0, 4, 5, 6, 1]) else (if i.val < 23 then [0, 6, 1] else [4, 5, 6, 1]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then [4, 6, 1] else [1, 2, 3]) else (if i.val < 27 then [0, 1, 2, 3] else [1, 2, 3, 4, 5])) else (if i.val < 30 then (if i.val < 29 then [0, 1, 2, 3, 4, 5] else [0, 5, 6, 1]) else (if i.val < 31 then [0, 4, 6, 1] else [5, 6, 1]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then [1, 2, 6] else [1, 5]) else (if i.val < 35 then [0, 1, 5] else [1, 4])) else (if i.val < 38 then (if i.val < 37 then [0, 1, 4] else [0, 1, 4, 6, 2]) else (if i.val < 39 then [0, 1, 2, 6] else [1, 4, 6, 2]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then [0, 1, 2, 7, 4] else [1, 4, 6, 7]) else (if i.val < 43 then [0, 1, 7, 4, 6] else [0, 1, 7, 2])) else (if i.val < 46 then (if i.val < 45 then [0, 6, 1, 7] else [2, 4, 7, 1]) else (if i.val < 47 then [2, 7, 1] else [1, 6, 7])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then [2, 3, 5] else [3, 6]) else (if i.val < 51 then [0, 2, 3, 5] else [2, 3, 4])) else (if i.val < 54 then (if i.val < 53 then [0, 3, 4, 5, 6] else [0, 3, 6]) else (if i.val < 55 then [3, 4, 5, 6] else [0, 2, 3, 4]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then [4, 7, 6] else [2, 4, 7]) else (if i.val < 59 then [0, 6, 7, 4] else [7, 0, 6])) else (if i.val < 62 then (if i.val < 61 then [2, 7, 0] else [2, 7]) else (if i.val < 63 then [2, 4, 7, 0] else [7, 6])))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then [5, 7, 0] else [7, 2, 6]) else (if i.val < 67 then [7, 0, 4] else [0, 2, 6, 7])) else (if i.val < 70 then (if i.val < 69 then [5, 7] else [0, 2, 4, 6, 7]) else (if i.val < 71 then [7, 4] else [2, 7, 4, 6]))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then [0, 5, 6] else [2]) else (if i.val < 75 then [0, 2] else [2, 4, 5])) else (if i.val < 78 then (if i.val < 77 then [0, 2, 4, 5] else [4, 6]) else (if i.val < 79 then [0, 4, 6] else [5, 6])))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then [6, 1, 7] else [1, 2, 7, 4]) else (if i.val < 83 then [0, 1, 6, 7] else [0, 2, 7, 1])) else (if i.val < 86 then (if i.val < 85 then [1, 7, 2] else [0, 1, 4, 6, 7]) else (if i.val < 87 then [0, 2, 4, 7, 1] else [1, 7, 4, 6]))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then [2, 3, 4, 5] else [3, 4, 6]) else (if i.val < 91 then [0, 2, 3, 4, 5] else [2, 3])) else (if i.val < 94 then (if i.val < 93 then [0, 3, 5, 6] else [0, 3, 4, 6]) else (if i.val < 95 then [3, 5, 6] else [0, 2, 3]))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then [1, 4, 7, 6] else [1, 2, 7]) else (if i.val < 99 then [0, 1, 6, 7, 4] else [0, 2, 7, 1, 4])) else (if i.val < 102 then (if i.val < 101 then [1, 2, 4, 7] else [0, 6, 7, 1]) else (if i.val < 103 then [0, 7, 1, 2] else [1, 7, 6]))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then [0, 3, 6, 2] else [3, 4, 5]) else (if i.val < 107 then [0, 3, 4, 5] else [3])) else (if i.val < 110 then (if i.val < 109 then [0, 3] else [2, 3, 4, 6]) else (if i.val < 111 then [0, 2, 3, 4, 6] else [3, 6, 2])))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then [6, 2, 7] else [3, 4, 7]) else (if i.val < 115 then [0, 2, 7, 6] else [0, 2, 4, 7, 6])) else (if i.val < 118 then (if i.val < 117 then [0, 7] else [3, 7]) else (if i.val < 119 then [0, 4, 7] else [2, 6, 7, 4]))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then [1, 2, 4, 6, 7] else [4, 7, 1]) else (if i.val < 123 then [0, 1, 2, 7, 4, 6] else [7, 0, 1])) else (if i.val < 126 then (if i.val < 125 then [7, 1] else [0, 1, 7, 2, 6]) else (if i.val < 127 then [0, 1, 7, 4] else [1, 2, 6, 7]))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then [0, 4, 7, 1] else [1, 7, 2, 6]) else (if i.val < 131 then [0, 1, 2, 6, 7] else [0, 7, 1])) else (if i.val < 134 then (if i.val < 133 then [0, 1, 2, 4, 6, 7] else [1, 7, 4]) else (if i.val < 135 then [1, 5, 7] else [1, 2, 7, 4, 6]))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then [0, 4, 5, 6] else [2, 4]) else (if i.val < 139 then [0, 2, 4] else [2, 5])) else (if i.val < 142 then (if i.val < 141 then [0, 2, 5] else [6]) else (if i.val < 143 then [0, 6] else [4, 5, 6])))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then [0, 1, 2, 7] else [6, 7, 1]) else (if i.val < 147 then [0, 1, 7, 6] else [0, 1, 2, 4, 7])) else (if i.val < 150 then (if i.val < 149 then [0, 1, 4, 7, 6] else [7, 1, 2]) else (if i.val < 151 then [2, 7, 1, 4] else [1, 6, 7, 4]))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then [1, 2, 4, 5] else [0, 1, 2, 4, 5]) else (if i.val < 155 then [0, 1, 5, 6] else [1, 2])) else (if i.val < 158 then (if i.val < 157 then [1, 4, 6] else [0, 1, 4, 6]) else (if i.val < 159 then [0, 1, 2] else [1, 5, 6]))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then [1, 7, 0] else [1, 2, 4, 7, 6]) else (if i.val < 163 then [0, 1, 2, 6, 7, 4] else [0, 7, 1, 4])) else (if i.val < 166 then (if i.val < 165 then [0, 1, 6, 2, 7] else [1, 7]) else (if i.val < 167 then [1, 4, 7] else [1, 2, 7, 6]))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then [1, 2, 5] else [0, 1, 2, 5]) else (if i.val < 171 then [0, 1, 4, 5, 6] else [1, 2, 4])) else (if i.val < 174 then (if i.val < 173 then [1, 6] else [0, 1, 6]) else (if i.val < 175 then [0, 1, 2, 4] else [1, 4, 5, 6])))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then [4] else [2, 6]) else (if i.val < 179 then [0, 4] else [5])) else (if i.val < 182 then (if i.val < 181 then [0, 4, 6, 2] else [0, 2, 6]) else (if i.val < 183 then [4, 6, 2] else [0, 5]))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then [0, 3, 4, 6, 2] else [3, 5]) else (if i.val < 187 then [0, 3, 5] else [3, 4])) else (if i.val < 190 then (if i.val < 189 then [0, 3, 4] else [2, 3, 6]) else (if i.val < 191 then [0, 2, 3, 6] else [3, 4, 6, 2])))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then [1, 2, 4, 6] else [1, 4, 5]) else (if i.val < 195 then [0, 1, 4, 5] else [1])) else (if i.val < 198 then (if i.val < 197 then [0, 1] else [0, 1, 6, 2]) else (if i.val < 199 then [0, 1, 2, 4, 6] else [1, 6, 2]))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then [1, 3, 4] else [0, 1, 3, 4]) else (if i.val < 203 then [0, 4, 6, 1, 2] else [1, 3, 5])) else (if i.val < 206 then (if i.val < 205 then [2, 6, 1] else [0, 2, 6, 1]) else (if i.val < 207 then [0, 1, 3, 5] else [4, 6, 1, 2])))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then [4, 7, 0] else [2, 4, 7, 6]) else (if i.val < 211 then [7, 0] else [0, 2, 6, 7, 4])) else (if i.val < 214 then (if i.val < 213 then [4, 7] else [0, 6, 2, 7]) else (if i.val < 215 then [7] else [2, 7, 6]))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then [3, 6, 7] else [7, 2]) else (if i.val < 219 then [0, 6, 7] else [0, 4, 6, 7])) else (if i.val < 222 then (if i.val < 221 then [2, 7, 0, 4] else [2, 7, 4]) else (if i.val < 223 then [7, 0, 2] else [7, 4, 6]))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then [0, 2, 4, 7] else [3, 7, 6]) else (if i.val < 227 then [0, 2, 7] else [0, 7, 6])) else (if i.val < 230 then (if i.val < 229 then [2, 3, 4, 7] else [0, 4, 7, 6]) else (if i.val < 231 then [2, 3, 7] else [6, 7, 4]))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then [1, 6, 2, 7] else [1, 3, 7]) else (if i.val < 235 then [0, 1, 2, 7, 6] else [0, 1, 4, 7])) else (if i.val < 238 then (if i.val < 237 then [7, 1, 4] else [0, 1, 2, 4, 7, 6]) else (if i.val < 239 then [0, 1, 7] else [1, 2, 6, 7, 4])))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then [1, 3] else [0, 1, 3]) else (if i.val < 243 then [0, 6, 1, 2] else [1, 3, 4, 5])) else (if i.val < 246 then (if i.val < 245 then [2, 4, 6, 1] else [0, 2, 4, 6, 1]) else (if i.val < 247 then [0, 1, 3, 4, 5] else [6, 1, 2]))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then [2, 4, 6, 7] else [1, 7, 1]) else (if i.val < 251 then [0, 2, 7, 4, 6] else [0, 7, 2, 6])) else (if i.val < 254 then (if i.val < 253 then [0, 7, 4] else [3, 7, 4]) else (if i.val < 255 then [0, 5, 7] else [2, 6, 7]))))))))
def step (i : Fin 256) (a : Fin 8) : Fin 256 :=
  Fin.ofNat 256 ((if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then [2, 195, 73, 107, 176, 179, 141, 214] else [5, 244, 143, 109, 177, 182, 75, 248]) else (if i.val < 3 then [0, 196, 74, 108, 178, 183, 142, 116] else [7, 193, 75, 105, 179, 176, 143, 70])) else (if i.val < 6 then (if i.val < 5 then [6, 242, 142, 104, 180, 181, 74, 213] else [1, 245, 136, 110, 181, 180, 76, 69]) else (if i.val < 7 then [4, 247, 141, 111, 182, 177, 73, 112] else [3, 194, 76, 106, 183, 178, 136, 252]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then [12, 102, 116, 222, 224, 226, 251, 50] else [11, 151, 248, 223, 225, 231, 113, 89]) else (if i.val < 11 then [14, 99, 118, 220, 226, 224, 250, 90] else [9, 148, 250, 219, 227, 229, 118, 78])) else (if i.val < 14 then (if i.val < 13 then [8, 97, 117, 217, 228, 230, 255, 139] else [15, 146, 251, 218, 229, 227, 116, 142]) else (if i.val < 15 then [10, 100, 113, 221, 230, 228, 248, 75] else [13, 145, 255, 216, 231, 225, 117, 49])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then [22, 141, 247, 172, 24, 31, 203, 80] else [18, 51, 200, 171, 25, 27, 244, 150]) else (if i.val < 19 then [17, 55, 201, 174, 26, 28, 245, 99] else [20, 48, 203, 168, 27, 25, 247, 46])) else (if i.val < 22 then (if i.val < 21 then [19, 50, 206, 169, 28, 26, 242, 83] else [23, 136, 245, 170, 29, 30, 201, 148]) else (if i.val < 23 then [16, 142, 242, 173, 30, 29, 206, 44] else [21, 143, 244, 175, 31, 24, 200, 96]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then [30, 77, 207, 156, 16, 23, 243, 87] else [26, 91, 240, 155, 17, 19, 204, 149]) else (if i.val < 27 then [25, 95, 241, 158, 18, 20, 205, 102] else [28, 88, 243, 152, 19, 17, 207, 45])) else (if i.val < 30 then (if i.val < 29 then [27, 90, 246, 153, 20, 18, 202, 86] else [31, 72, 205, 154, 21, 22, 241, 146]) else (if i.val < 31 then [24, 78, 202, 157, 22, 21, 246, 42] else [29, 79, 204, 159, 23, 16, 240, 103]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then [38, 189, 159, 204, 192, 199, 168, 127] else [34, 179, 168, 203, 193, 195, 159, 134]) else (if i.val < 35 then [33, 183, 169, 206, 194, 196, 154, 123] else [36, 176, 171, 200, 195, 193, 156, 166])) else (if i.val < 38 then (if i.val < 37 then [35, 178, 174, 201, 196, 194, 157, 235] else [39, 184, 157, 202, 197, 198, 174, 162]) else (if i.val < 39 then [32, 190, 154, 205, 198, 197, 169, 130] else [37, 191, 156, 207, 199, 192, 171, 239]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then [45, 62, 235, 86, 144, 147, 122, 28] else [42, 231, 120, 87, 145, 151, 236, 24]) else (if i.val < 43 then [41, 229, 122, 85, 146, 148, 235, 157] else [46, 60, 238, 83, 147, 144, 125, 20])) else (if i.val < 46 then (if i.val < 45 then [47, 227, 125, 82, 148, 146, 238, 173] else [40, 57, 236, 81, 149, 150, 120, 152]) else (if i.val < 47 then [43, 61, 233, 84, 150, 149, 127, 168] else [44, 225, 127, 80, 151, 145, 233, 16])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then [50, 19, 185, 139, 88, 91, 111, 12] else [53, 172, 111, 141, 89, 94, 185, 216]) else (if i.val < 51 then [48, 20, 186, 140, 90, 95, 104, 222] else [55, 17, 187, 137, 91, 88, 109, 228])) else (if i.val < 54 then (if i.val < 53 then [54, 170, 110, 136, 92, 93, 188, 229] else [49, 173, 104, 142, 93, 92, 186, 13]) else (if i.val < 55 then [52, 175, 109, 143, 94, 89, 187, 56] else [51, 18, 188, 138, 95, 90, 110, 62]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then [58, 87, 209, 231, 216, 223, 70, 143] else [62, 45, 70, 228, 217, 221, 209, 51]) else (if i.val < 59 then [56, 85, 211, 229, 218, 219, 66, 52] else [63, 82, 213, 227, 219, 218, 64, 92])) else (if i.val < 62 then (if i.val < 61 then [61, 43, 64, 226, 220, 222, 213, 74] else [60, 46, 68, 230, 221, 217, 215, 91]) else (if i.val < 63 then [57, 40, 66, 224, 222, 220, 211, 138] else [59, 80, 215, 225, 223, 216, 68, 79])))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then [68, 238, 60, 254, 208, 210, 218, 183] else [67, 167, 216, 255, 209, 215, 61, 177]) else (if i.val < 67 then [70, 235, 62, 252, 210, 208, 219, 7] else [65, 164, 218, 251, 211, 213, 60, 190])) else (if i.val < 70 then (if i.val < 69 then [64, 233, 61, 249, 212, 214, 216, 185] else [71, 162, 219, 250, 213, 211, 62, 110]) else (if i.val < 71 then [66, 236, 57, 253, 214, 212, 223, 105] else [69, 161, 223, 248, 215, 209, 57, 1]))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then [79, 29, 181, 92, 136, 142, 2, 59] else [74, 155, 0, 91, 137, 139, 177, 61]) else (if i.val < 75 then [73, 158, 2, 95, 138, 140, 181, 226] else [76, 152, 3, 88, 139, 137, 182, 221])) else (if i.val < 78 then (if i.val < 77 then [75, 153, 7, 90, 140, 138, 180, 10] else [78, 24, 182, 89, 141, 143, 3, 9]) else (if i.val < 79 then [77, 30, 180, 93, 142, 136, 7, 219] else [72, 31, 177, 94, 143, 141, 0, 225])))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then [82, 63, 129, 47, 96, 103, 165, 172] else [86, 228, 166, 45, 97, 100, 135, 27]) else (if i.val < 83 then [80, 59, 130, 44, 98, 101, 160, 22] else [84, 226, 160, 43, 99, 102, 130, 169])) else (if i.val < 86 then (if i.val < 85 then [83, 230, 165, 46, 100, 97, 129, 19] else [87, 58, 132, 42, 101, 98, 163, 30]) else (if i.val < 87 then [81, 224, 163, 40, 102, 99, 132, 153] else [85, 56, 135, 41, 103, 96, 166, 156]))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then [90, 27, 105, 75, 48, 51, 191, 14] else [93, 156, 191, 77, 49, 54, 105, 223]) else (if i.val < 91 then [88, 28, 106, 76, 50, 55, 184, 220] else [95, 25, 107, 73, 51, 48, 189, 230])) else (if i.val < 94 then (if i.val < 93 then [94, 154, 190, 72, 52, 53, 108, 227] else [89, 157, 184, 78, 53, 52, 106, 11]) else (if i.val < 95 then [92, 159, 189, 79, 54, 49, 107, 63] else [91, 26, 108, 74, 55, 50, 190, 60]))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then [98, 223, 161, 151, 80, 87, 133, 175] else [102, 12, 134, 149, 81, 84, 167, 25]) else (if i.val < 99 then [96, 219, 162, 148, 82, 85, 128, 21] else [100, 10, 128, 147, 83, 86, 162, 174])) else (if i.val < 102 then (if i.val < 101 then [99, 14, 133, 150, 84, 81, 161, 17] else [103, 218, 164, 146, 85, 82, 131, 29]) else (if i.val < 103 then [97, 8, 131, 144, 86, 83, 164, 158] else [101, 216, 167, 145, 87, 80, 134, 159]))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then [111, 197, 53, 4, 184, 190, 95, 114] else [106, 243, 88, 3, 185, 187, 54, 253]) else (if i.val < 107 then [105, 246, 90, 7, 186, 188, 52, 66] else [108, 240, 91, 0, 187, 185, 49, 117])) else (if i.val < 110 then (if i.val < 109 then [107, 241, 95, 2, 188, 186, 53, 210] else [110, 192, 54, 1, 189, 191, 88, 71]) else (if i.val < 111 then [109, 198, 52, 5, 190, 184, 90, 250] else [104, 199, 49, 6, 191, 189, 91, 215])))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then [114, 127, 225, 215, 248, 255, 12, 111] else [118, 133, 14, 212, 249, 253, 231, 176]) else (if i.val < 115 then [112, 125, 227, 213, 250, 251, 8, 4] else [119, 122, 229, 211, 251, 250, 10, 180])) else (if i.val < 118 then (if i.val < 117 then [117, 131, 8, 210, 252, 254, 227, 108] else [116, 134, 12, 214, 253, 249, 225, 0]) else (if i.val < 119 then [113, 128, 10, 208, 254, 252, 229, 188] else [115, 120, 231, 209, 255, 248, 14, 191]))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then [122, 119, 41, 135, 232, 239, 150, 244] else [126, 212, 150, 133, 233, 236, 41, 193]) else (if i.val < 123 then [120, 115, 42, 132, 234, 237, 147, 198] else [124, 210, 144, 131, 235, 238, 44, 206])) else (if i.val < 126 then (if i.val < 125 then [123, 214, 149, 134, 236, 233, 47, 33] else [127, 114, 44, 130, 237, 234, 144, 38]) else (if i.val < 127 then [121, 208, 147, 128, 238, 235, 42, 246] else [125, 112, 47, 129, 239, 232, 149, 204]))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then [133, 118, 99, 126, 160, 163, 85, 194] else [130, 215, 80, 127, 161, 167, 97, 32]) else (if i.val < 131 then [129, 213, 82, 125, 162, 164, 102, 205] else [134, 116, 102, 123, 163, 160, 82, 34])) else (if i.val < 134 then (if i.val < 133 then [135, 211, 85, 122, 164, 162, 99, 245] else [128, 113, 100, 121, 165, 166, 87, 243]) else (if i.val < 135 then [131, 117, 97, 124, 166, 165, 80, 203] else [132, 209, 87, 120, 167, 161, 100, 192]))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then [143, 21, 5, 52, 72, 78, 178, 58] else [138, 171, 176, 51, 73, 75, 1, 57]) else (if i.val < 139 then [137, 174, 178, 55, 74, 76, 5, 224] else [140, 168, 179, 48, 75, 73, 6, 217])) else (if i.val < 142 then (if i.val < 141 then [139, 169, 183, 50, 76, 74, 4, 8] else [142, 16, 6, 49, 77, 79, 179, 15]) else (if i.val < 143 then [141, 22, 4, 53, 78, 72, 183, 218] else [136, 23, 1, 54, 79, 77, 176, 231])))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then [149, 222, 123, 102, 40, 43, 234, 26] else [146, 15, 232, 103, 41, 47, 124, 31]) else (if i.val < 147 then [145, 13, 234, 101, 42, 44, 123, 154] else [150, 220, 126, 99, 43, 40, 237, 18])) else (if i.val < 150 then (if i.val < 149 then [151, 11, 237, 98, 44, 42, 126, 170] else [144, 217, 124, 97, 45, 46, 232, 155]) else (if i.val < 151 then [147, 221, 121, 100, 46, 45, 239, 171] else [148, 9, 239, 96, 47, 41, 121, 23]))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then [153, 75, 193, 27, 168, 171, 39, 81] else [152, 76, 194, 28, 169, 174, 37, 40]) else (if i.val < 155 then [159, 92, 38, 29, 170, 173, 196, 101] else [158, 73, 195, 25, 171, 168, 32, 97])) else (if i.val < 158 then (if i.val < 157 then [157, 89, 39, 24, 172, 175, 193, 41] else [156, 93, 37, 30, 173, 170, 194, 85]) else (if i.val < 159 then [155, 74, 196, 26, 174, 169, 38, 144] else [154, 94, 32, 31, 175, 172, 195, 145]))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then [165, 254, 83, 238, 128, 131, 101, 196] else [162, 71, 96, 239, 129, 135, 81, 39]) else (if i.val < 163 then [161, 69, 98, 237, 130, 132, 86, 202] else [166, 252, 86, 235, 131, 128, 98, 36])) else (if i.val < 166 then (if i.val < 165 then [167, 67, 101, 234, 132, 130, 83, 242] else [160, 249, 84, 233, 133, 134, 103, 240]) else (if i.val < 167 then [163, 253, 81, 236, 134, 133, 96, 200] else [164, 65, 103, 232, 135, 129, 84, 199]))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then [169, 139, 33, 19, 152, 155, 199, 84] else [168, 140, 34, 20, 153, 158, 197, 43]) else (if i.val < 171 then [175, 52, 198, 21, 154, 157, 36, 98] else [174, 137, 35, 17, 155, 152, 192, 100])) else (if i.val < 174 then (if i.val < 173 then [173, 49, 199, 16, 156, 159, 33, 47] else [172, 53, 197, 22, 157, 154, 34, 82]) else (if i.val < 175 then [171, 138, 36, 18, 158, 153, 198, 147] else [170, 54, 192, 23, 159, 156, 35, 151])))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then [178, 35, 137, 187, 0, 3, 77, 212] else [181, 204, 79, 189, 1, 6, 139, 255]) else (if i.val < 179 then [176, 36, 138, 188, 2, 7, 78, 118] else [183, 33, 139, 185, 3, 0, 79, 68])) else (if i.val < 182 then (if i.val < 181 then [182, 202, 78, 184, 4, 5, 138, 211] else [177, 205, 72, 190, 5, 4, 140, 67]) else (if i.val < 183 then [180, 207, 77, 191, 6, 1, 137, 119] else [179, 34, 140, 186, 7, 2, 72, 254]))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then [191, 37, 93, 180, 104, 110, 55, 115] else [186, 203, 48, 179, 105, 107, 94, 249]) else (if i.val < 187 then [185, 206, 50, 183, 106, 108, 92, 64] else [188, 200, 51, 176, 107, 105, 89, 113])) else (if i.val < 190 then (if i.val < 189 then [187, 201, 55, 178, 108, 106, 93, 208] else [190, 32, 94, 177, 109, 111, 48, 65]) else (if i.val < 191 then [189, 38, 92, 181, 110, 104, 50, 251] else [184, 39, 89, 182, 111, 109, 51, 209])))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then [198, 109, 175, 244, 32, 39, 152, 120] else [194, 3, 152, 243, 33, 35, 175, 133]) else (if i.val < 195 then [193, 7, 153, 246, 34, 36, 170, 126] else [196, 0, 155, 240, 35, 33, 172, 165])) else (if i.val < 198 then (if i.val < 197 then [195, 2, 158, 241, 36, 34, 173, 238] else [199, 104, 173, 242, 37, 38, 158, 164]) else (if i.val < 199 then [192, 110, 170, 245, 38, 37, 153, 132] else [197, 111, 172, 247, 39, 32, 155, 232]))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then [201, 187, 17, 35, 240, 243, 24, 236] else [200, 188, 18, 36, 241, 246, 30, 163]) else (if i.val < 203 then [207, 180, 30, 37, 242, 245, 18, 237] else [206, 185, 19, 33, 243, 240, 31, 124])) else (if i.val < 206 then (if i.val < 205 then [205, 177, 31, 32, 244, 247, 19, 129] else [204, 181, 29, 38, 245, 242, 20, 125]) else (if i.val < 207 then [203, 186, 20, 34, 246, 241, 29, 131] else [202, 182, 24, 39, 247, 244, 17, 161])))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then [212, 126, 220, 118, 64, 66, 58, 178] else [211, 135, 56, 119, 65, 71, 221, 182]) else (if i.val < 211 then [214, 123, 222, 116, 66, 64, 59, 2] else [209, 132, 58, 115, 67, 69, 220, 184])) else (if i.val < 214 then (if i.val < 213 then [208, 121, 221, 113, 68, 70, 56, 187] else [215, 130, 59, 114, 69, 67, 222, 104]) else (if i.val < 215 then [210, 124, 217, 117, 70, 68, 63, 107] else [213, 129, 63, 112, 71, 65, 217, 6]))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then [218, 103, 65, 15, 56, 63, 214, 141] else [222, 149, 214, 12, 57, 61, 65, 48]) else (if i.val < 219 then [216, 101, 67, 13, 58, 59, 210, 53] else [223, 98, 69, 11, 59, 58, 208, 93])) else (if i.val < 222 then (if i.val < 221 then [221, 147, 208, 10, 60, 62, 69, 76] else [220, 150, 212, 14, 61, 57, 71, 88]) else (if i.val < 223 then [217, 144, 210, 8, 62, 60, 67, 140] else [219, 96, 71, 9, 63, 56, 212, 77]))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then [228, 86, 252, 62, 8, 10, 115, 55] else [227, 47, 112, 63, 9, 15, 249, 94]) else (if i.val < 227 then [230, 83, 254, 60, 10, 8, 114, 95] else [225, 44, 114, 59, 11, 13, 254, 72])) else (if i.val < 230 then (if i.val < 229 then [224, 81, 253, 57, 12, 14, 119, 137] else [231, 42, 115, 58, 13, 11, 252, 136]) else (if i.val < 231 then [226, 84, 249, 61, 14, 12, 112, 73] else [229, 41, 119, 56, 15, 9, 253, 54]))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then [234, 255, 145, 167, 120, 127, 46, 247] else [238, 68, 46, 165, 121, 124, 145, 195]) else (if i.val < 235 then [232, 251, 146, 164, 122, 125, 43, 197] else [236, 66, 40, 163, 123, 126, 148, 201])) else (if i.val < 238 then (if i.val < 237 then [235, 70, 45, 166, 124, 121, 151, 35] else [239, 250, 148, 162, 125, 122, 40, 37]) else (if i.val < 239 then [233, 64, 43, 160, 126, 123, 146, 241] else [237, 248, 151, 161, 127, 120, 45, 207])))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then [241, 107, 25, 195, 200, 203, 16, 233] else [240, 108, 26, 196, 201, 206, 22, 160]) else (if i.val < 243 then [247, 4, 22, 197, 202, 205, 26, 234] else [246, 105, 27, 193, 203, 200, 23, 121])) else (if i.val < 246 then (if i.val < 245 then [245, 1, 23, 192, 204, 207, 27, 135] else [244, 5, 21, 198, 205, 202, 28, 122]) else (if i.val < 247 then [243, 106, 28, 194, 206, 201, 21, 128] else [242, 6, 16, 199, 207, 204, 25, 167]))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then [250, 239, 9, 71, 112, 119, 228, 109] else [254, 165, 230, 68, 113, 117, 15, 179]) else (if i.val < 251 then [248, 237, 11, 69, 114, 115, 224, 5] else [255, 234, 13, 67, 115, 114, 226, 181])) else (if i.val < 254 then (if i.val < 253 then [253, 163, 224, 66, 116, 118, 11, 106] else [252, 166, 228, 70, 117, 113, 9, 3]) else (if i.val < 255 then [249, 160, 226, 64, 118, 116, 13, 186] else [251, 232, 15, 65, 119, 112, 230, 189])))))))) : List Nat)[a.val]!
def key (i : Fin 256) : ℕ := (#[4239483, 1197844299, 1508389929, 3826338194, 6024209734, 6387873506, 6461700645, 6773933810, 157658804746, 158543030812, 160424371722, 161489794411, 161632980607, 162619222334, 163362297645, 165556599904, 428298501190, 431285689831, 431562816206, 432009976869, 432069301368, 433128542759, 433492920324, 433565464865, 576476599863, 579464433579, 579744502949, 580189065543, 580247793626, 581306390008, 581671539091, 581742192613, 1090742074651, 1093730078667, 1094008617637, 1094453117969, 1094514377335, 1095572206109, 1095938280106, 1096009730155, 1465117608901, 1465363685497, 1467803191027, 1467882847016, 1468676383746, 1469089338090, 1470821994099, 1472349800933, 1908892401924, 1910081575699, 1910395820010, 1912715551179, 1914913810052, 1915276696968, 1915349372375, 1915660823075, 2912280702614, 2913681827921, 2914719208676, 2915598430556, 2916128577686, 2916711923683, 2918016811099, 2919269593523, 2929468933285, 2930352727209, 2932232523441, 2933295618672, 2933440389794, 2934425483536, 2935174238426, 2937365496001, 3097106881275, 3098496137724, 3098777501643, 3099221377913, 3099281480609, 3099934753272, 3101053316810, 3102826062189, 3235425328545, 3236188195323, 3238371967668, 3238634194387, 3239215723004, 3239501017144, 3240519929373, 3242438516336, 3259932971232, 3261121448904, 3261434779571, 3263751867960, 3265948855581, 3266314896425, 3266387669424, 3266699985975, 4603898875764, 4604661994611, 4606840932587, 4607105636180, 4607689467613, 4607970212771, 4608991236699, 4610909949317, 5067010848544, 5068399778882, 5068676409629, 5069122940224, 5069183781224, 5069834091043, 5070957731133, 5072726768738, 6381400435902, 6382802195999, 6383839214137, 6384715707852, 6385245090079, 6385829295283, 6387134113003, 6388388957043, 7061918123103, 7062678391512, 7064860837916, 7065121506910, 7065707272200, 7065989311520, 7067013821759, 7068929846118, 7226642470006, 7226888150275, 7229326533908, 7229408203188, 7230206488209, 7230613660949, 7232346931164, 7233878082914, 8013144745841, 8014533350818, 8014812252716, 8015257675240, 8015317805092, 8015968858761, 8017093196519, 8018863426428, 8255176391266, 8255422385679, 8257858731050, 8257941751583, 8258737279232, 8259148615524, 8260882076426, 8262409911280, 9099906841458, 9101410844102, 9102694420674, 9103724918170, 9105516640094, 9106640956757, 9106673705008, 9108410495602, 9222692462375, 9222938242107, 9225378216471, 9225461147148, 9226257558880, 9226666684122, 9228398987583, 9229928827050, 9692619240760, 9694121758036, 9695407040550, 9696438181208, 9698230684041, 9699353408194, 9699389894252, 9701123917729, 12159357113256, 12160545583242, 12160858167605, 12163174623554, 12165374274642, 12165739025156, 12165811425454, 12166122348199, 12685126686251, 12686515489525, 12686793013892, 12687240171237, 12687295996224, 12687951620542, 12689072725067, 12690842994293, 13197793342073, 13200780411682, 13201061149596, 13201506251856, 13201562231070, 13202624460408, 13202987683045, 13203059869249, 14216420554732, 14217922210538, 14219209539368, 14220240303308, 14222032634602, 14223156124428, 14223188154131, 14224924187158, 14295625095294, 14296509668788, 14298393008862, 14299453839968, 14299597348502, 14300584263842, 14301330367859, 14303523181497, 14356888296223, 14358288645881, 14359327042753, 14360203732660, 14360733200136, 14361315432305, 14362619103722, 14363876943760, 15080098358825, 15080986665053, 15082864937598, 15083927981143, 15084071116697, 15085061431362, 15085807070121, 15088000220149, 15325045107687, 15325805990548, 15327985782723, 15328248645758, 15328836223847, 15329117865756, 15330138408520, 15332056353621, 15654625242137, 15656127657198, 15657411731041, 15658442360649, 15660235150167, 15661359212016, 15661391190847, 15663127139131, 16152458930932, 16153864288505, 16154900156353, 16155778957560, 16156307303938, 16156889127341, 16158194886254, 16159449479728] : Array ℕ)[i.val]!
def gen (a : Fin 8) : He := wordGenerator (spanWords 3) a
def genPerm (a : Fin 8) : Equiv.Perm (Fin 2058) := wordPerm (spanWords 3) a
theorem genPerm_eq (a : Fin 8) : genPerm a = representation (gen a) :=
  wordPerm_eq _ _
def target (a : Fin 6) : He := wordGenerator (generatorWords 20) a
def targetPerm (a : Fin 6) : Equiv.Perm (Fin 2058) := wordPerm (generatorWords 20) a
theorem targetPerm_eq (a : Fin 6) : targetPerm a = representation (target a) :=
  wordPerm_eq _ _
def elem (i : Fin 256) : He := eval gen (code i)
def perm (i : Fin 256) : Equiv.Perm (Fin 2058) := ((code i).map genPerm).prod
theorem perm_eq (i : Fin 256) : perm i = representation (elem i) :=
  eval_map representation gen genPerm genPerm_eq (code i)

set_option maxRecDepth 8192 in
private theorem step_check_0 : ∀ i : Fin 256, ∀ v : Fin 4,
    perm (step i 0) ⟨v.val, by omega⟩ =
      (perm i * genPerm 0) ⟨v.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem step_check_1 : ∀ i : Fin 256, ∀ v : Fin 4,
    perm (step i 1) ⟨v.val, by omega⟩ =
      (perm i * genPerm 1) ⟨v.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem step_check_2 : ∀ i : Fin 256, ∀ v : Fin 4,
    perm (step i 2) ⟨v.val, by omega⟩ =
      (perm i * genPerm 2) ⟨v.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem step_check_3 : ∀ i : Fin 256, ∀ v : Fin 4,
    perm (step i 3) ⟨v.val, by omega⟩ =
      (perm i * genPerm 3) ⟨v.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem step_check_4 : ∀ i : Fin 256, ∀ v : Fin 4,
    perm (step i 4) ⟨v.val, by omega⟩ =
      (perm i * genPerm 4) ⟨v.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem step_check_5 : ∀ i : Fin 256, ∀ v : Fin 4,
    perm (step i 5) ⟨v.val, by omega⟩ =
      (perm i * genPerm 5) ⟨v.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem step_check_6 : ∀ i : Fin 256, ∀ v : Fin 4,
    perm (step i 6) ⟨v.val, by omega⟩ =
      (perm i * genPerm 6) ⟨v.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem step_check_7 : ∀ i : Fin 256, ∀ v : Fin 4,
    perm (step i 7) ⟨v.val, by omega⟩ =
      (perm i * genPerm 7) ⟨v.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem step_eq (i : Fin 256) (a : Fin 8) :
    elem (step i a) = elem i * gen a := by
  apply Held.eq_of_four_point_images
  rw [map_mul, ← perm_eq, ← perm_eq, ← genPerm_eq a]
  fin_cases a
  · exact step_check_0 i
  · exact step_check_1 i
  · exact step_check_2 i
  · exact step_check_3 i
  · exact step_check_4 i
  · exact step_check_5 i
  · exact step_check_6 i
  · exact step_check_7 i

set_option maxRecDepth 8192 in
private theorem key_check : ∀ i : Fin 256,
    (((perm i 0).val * 2058 + (perm i 1).val) * 2058 + (perm i 2).val) * 2058 +
      (perm i 3).val = key i := by decide +kernel

set_option maxRecDepth 8192 in
private theorem increasing_check : ∀ i : Fin 255, key i.castSucc < key i.succ := by
  decide +kernel

private theorem elem_injective : Function.Injective elem := by
  intro i k h
  apply (Fin.strictMono_iff_lt_succ.mpr increasing_check).injective
  rw [← key_check, ← key_check, perm_eq, perm_eq, h]

set_option maxRecDepth 8192 in
def enumeration : Enumeration gen 256 where
  code := code
  root := 0
  step := step
  root_eq := rfl
  step_eq := by exact step_eq
  injective := by exact elem_injective

def counts (i : Fin 256) : ℕ := (#[256, 64, 128, 128, 64, 64, 64, 128, 64, 64, 64, 64, 64, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 64, 64, 128, 128, 64, 64, 64, 64, 64, 64, 64, 128, 128, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 128, 64, 128, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 128, 128, 256, 128, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 128, 64, 128, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 128, 64, 64, 64, 64, 64, 128, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 128, 64, 128, 64, 64, 64, 64, 128, 64, 128, 256, 64, 64, 64, 128, 64, 256, 128, 128, 128, 64, 64, 64, 64, 128, 128, 64, 64, 64, 64, 64, 128, 128, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 64, 64, 64, 64, 64, 64] : Array ℕ)[i.val]!

set_option maxRecDepth 8192 in
private theorem count_0 : enumeration.count (0 : Fin 256) = counts 0 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_1 : enumeration.count (1 : Fin 256) = counts 1 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_2 : enumeration.count (2 : Fin 256) = counts 2 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_3 : enumeration.count (3 : Fin 256) = counts 3 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_4 : enumeration.count (4 : Fin 256) = counts 4 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_5 : enumeration.count (5 : Fin 256) = counts 5 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_6 : enumeration.count (6 : Fin 256) = counts 6 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_7 : enumeration.count (7 : Fin 256) = counts 7 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_8 : enumeration.count (8 : Fin 256) = counts 8 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_9 : enumeration.count (9 : Fin 256) = counts 9 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_10 : enumeration.count (10 : Fin 256) = counts 10 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_11 : enumeration.count (11 : Fin 256) = counts 11 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_12 : enumeration.count (12 : Fin 256) = counts 12 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_13 : enumeration.count (13 : Fin 256) = counts 13 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_14 : enumeration.count (14 : Fin 256) = counts 14 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_15 : enumeration.count (15 : Fin 256) = counts 15 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_16 : enumeration.count (16 : Fin 256) = counts 16 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_17 : enumeration.count (17 : Fin 256) = counts 17 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_18 : enumeration.count (18 : Fin 256) = counts 18 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_19 : enumeration.count (19 : Fin 256) = counts 19 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_20 : enumeration.count (20 : Fin 256) = counts 20 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_21 : enumeration.count (21 : Fin 256) = counts 21 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_22 : enumeration.count (22 : Fin 256) = counts 22 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_23 : enumeration.count (23 : Fin 256) = counts 23 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_24 : enumeration.count (24 : Fin 256) = counts 24 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_25 : enumeration.count (25 : Fin 256) = counts 25 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_26 : enumeration.count (26 : Fin 256) = counts 26 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_27 : enumeration.count (27 : Fin 256) = counts 27 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_28 : enumeration.count (28 : Fin 256) = counts 28 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_29 : enumeration.count (29 : Fin 256) = counts 29 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_30 : enumeration.count (30 : Fin 256) = counts 30 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_31 : enumeration.count (31 : Fin 256) = counts 31 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_32 : enumeration.count (32 : Fin 256) = counts 32 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_33 : enumeration.count (33 : Fin 256) = counts 33 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_34 : enumeration.count (34 : Fin 256) = counts 34 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_35 : enumeration.count (35 : Fin 256) = counts 35 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_36 : enumeration.count (36 : Fin 256) = counts 36 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_37 : enumeration.count (37 : Fin 256) = counts 37 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_38 : enumeration.count (38 : Fin 256) = counts 38 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_39 : enumeration.count (39 : Fin 256) = counts 39 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_40 : enumeration.count (40 : Fin 256) = counts 40 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_41 : enumeration.count (41 : Fin 256) = counts 41 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_42 : enumeration.count (42 : Fin 256) = counts 42 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_43 : enumeration.count (43 : Fin 256) = counts 43 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_44 : enumeration.count (44 : Fin 256) = counts 44 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_45 : enumeration.count (45 : Fin 256) = counts 45 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_46 : enumeration.count (46 : Fin 256) = counts 46 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_47 : enumeration.count (47 : Fin 256) = counts 47 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_48 : enumeration.count (48 : Fin 256) = counts 48 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_49 : enumeration.count (49 : Fin 256) = counts 49 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_50 : enumeration.count (50 : Fin 256) = counts 50 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_51 : enumeration.count (51 : Fin 256) = counts 51 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_52 : enumeration.count (52 : Fin 256) = counts 52 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_53 : enumeration.count (53 : Fin 256) = counts 53 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_54 : enumeration.count (54 : Fin 256) = counts 54 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_55 : enumeration.count (55 : Fin 256) = counts 55 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_56 : enumeration.count (56 : Fin 256) = counts 56 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_57 : enumeration.count (57 : Fin 256) = counts 57 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_58 : enumeration.count (58 : Fin 256) = counts 58 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_59 : enumeration.count (59 : Fin 256) = counts 59 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_60 : enumeration.count (60 : Fin 256) = counts 60 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_61 : enumeration.count (61 : Fin 256) = counts 61 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_62 : enumeration.count (62 : Fin 256) = counts 62 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_63 : enumeration.count (63 : Fin 256) = counts 63 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_64 : enumeration.count (64 : Fin 256) = counts 64 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_65 : enumeration.count (65 : Fin 256) = counts 65 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_66 : enumeration.count (66 : Fin 256) = counts 66 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_67 : enumeration.count (67 : Fin 256) = counts 67 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_68 : enumeration.count (68 : Fin 256) = counts 68 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_69 : enumeration.count (69 : Fin 256) = counts 69 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_70 : enumeration.count (70 : Fin 256) = counts 70 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_71 : enumeration.count (71 : Fin 256) = counts 71 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_72 : enumeration.count (72 : Fin 256) = counts 72 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_73 : enumeration.count (73 : Fin 256) = counts 73 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_74 : enumeration.count (74 : Fin 256) = counts 74 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_75 : enumeration.count (75 : Fin 256) = counts 75 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_76 : enumeration.count (76 : Fin 256) = counts 76 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_77 : enumeration.count (77 : Fin 256) = counts 77 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_78 : enumeration.count (78 : Fin 256) = counts 78 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_79 : enumeration.count (79 : Fin 256) = counts 79 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_80 : enumeration.count (80 : Fin 256) = counts 80 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_81 : enumeration.count (81 : Fin 256) = counts 81 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_82 : enumeration.count (82 : Fin 256) = counts 82 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_83 : enumeration.count (83 : Fin 256) = counts 83 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_84 : enumeration.count (84 : Fin 256) = counts 84 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_85 : enumeration.count (85 : Fin 256) = counts 85 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_86 : enumeration.count (86 : Fin 256) = counts 86 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_87 : enumeration.count (87 : Fin 256) = counts 87 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_88 : enumeration.count (88 : Fin 256) = counts 88 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_89 : enumeration.count (89 : Fin 256) = counts 89 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_90 : enumeration.count (90 : Fin 256) = counts 90 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_91 : enumeration.count (91 : Fin 256) = counts 91 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_92 : enumeration.count (92 : Fin 256) = counts 92 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_93 : enumeration.count (93 : Fin 256) = counts 93 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_94 : enumeration.count (94 : Fin 256) = counts 94 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_95 : enumeration.count (95 : Fin 256) = counts 95 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_96 : enumeration.count (96 : Fin 256) = counts 96 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_97 : enumeration.count (97 : Fin 256) = counts 97 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_98 : enumeration.count (98 : Fin 256) = counts 98 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_99 : enumeration.count (99 : Fin 256) = counts 99 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_100 : enumeration.count (100 : Fin 256) = counts 100 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_101 : enumeration.count (101 : Fin 256) = counts 101 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_102 : enumeration.count (102 : Fin 256) = counts 102 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_103 : enumeration.count (103 : Fin 256) = counts 103 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_104 : enumeration.count (104 : Fin 256) = counts 104 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_105 : enumeration.count (105 : Fin 256) = counts 105 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_106 : enumeration.count (106 : Fin 256) = counts 106 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_107 : enumeration.count (107 : Fin 256) = counts 107 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_108 : enumeration.count (108 : Fin 256) = counts 108 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_109 : enumeration.count (109 : Fin 256) = counts 109 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_110 : enumeration.count (110 : Fin 256) = counts 110 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_111 : enumeration.count (111 : Fin 256) = counts 111 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_112 : enumeration.count (112 : Fin 256) = counts 112 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_113 : enumeration.count (113 : Fin 256) = counts 113 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_114 : enumeration.count (114 : Fin 256) = counts 114 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_115 : enumeration.count (115 : Fin 256) = counts 115 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_116 : enumeration.count (116 : Fin 256) = counts 116 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_117 : enumeration.count (117 : Fin 256) = counts 117 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_118 : enumeration.count (118 : Fin 256) = counts 118 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_119 : enumeration.count (119 : Fin 256) = counts 119 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_120 : enumeration.count (120 : Fin 256) = counts 120 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_121 : enumeration.count (121 : Fin 256) = counts 121 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_122 : enumeration.count (122 : Fin 256) = counts 122 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_123 : enumeration.count (123 : Fin 256) = counts 123 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_124 : enumeration.count (124 : Fin 256) = counts 124 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_125 : enumeration.count (125 : Fin 256) = counts 125 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_126 : enumeration.count (126 : Fin 256) = counts 126 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_127 : enumeration.count (127 : Fin 256) = counts 127 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_128 : enumeration.count (128 : Fin 256) = counts 128 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_129 : enumeration.count (129 : Fin 256) = counts 129 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_130 : enumeration.count (130 : Fin 256) = counts 130 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_131 : enumeration.count (131 : Fin 256) = counts 131 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_132 : enumeration.count (132 : Fin 256) = counts 132 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_133 : enumeration.count (133 : Fin 256) = counts 133 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_134 : enumeration.count (134 : Fin 256) = counts 134 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_135 : enumeration.count (135 : Fin 256) = counts 135 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_136 : enumeration.count (136 : Fin 256) = counts 136 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_137 : enumeration.count (137 : Fin 256) = counts 137 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_138 : enumeration.count (138 : Fin 256) = counts 138 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_139 : enumeration.count (139 : Fin 256) = counts 139 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_140 : enumeration.count (140 : Fin 256) = counts 140 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_141 : enumeration.count (141 : Fin 256) = counts 141 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_142 : enumeration.count (142 : Fin 256) = counts 142 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_143 : enumeration.count (143 : Fin 256) = counts 143 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_144 : enumeration.count (144 : Fin 256) = counts 144 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_145 : enumeration.count (145 : Fin 256) = counts 145 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_146 : enumeration.count (146 : Fin 256) = counts 146 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_147 : enumeration.count (147 : Fin 256) = counts 147 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_148 : enumeration.count (148 : Fin 256) = counts 148 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_149 : enumeration.count (149 : Fin 256) = counts 149 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_150 : enumeration.count (150 : Fin 256) = counts 150 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_151 : enumeration.count (151 : Fin 256) = counts 151 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_152 : enumeration.count (152 : Fin 256) = counts 152 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_153 : enumeration.count (153 : Fin 256) = counts 153 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_154 : enumeration.count (154 : Fin 256) = counts 154 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_155 : enumeration.count (155 : Fin 256) = counts 155 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_156 : enumeration.count (156 : Fin 256) = counts 156 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_157 : enumeration.count (157 : Fin 256) = counts 157 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_158 : enumeration.count (158 : Fin 256) = counts 158 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_159 : enumeration.count (159 : Fin 256) = counts 159 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_160 : enumeration.count (160 : Fin 256) = counts 160 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_161 : enumeration.count (161 : Fin 256) = counts 161 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_162 : enumeration.count (162 : Fin 256) = counts 162 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_163 : enumeration.count (163 : Fin 256) = counts 163 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_164 : enumeration.count (164 : Fin 256) = counts 164 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_165 : enumeration.count (165 : Fin 256) = counts 165 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_166 : enumeration.count (166 : Fin 256) = counts 166 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_167 : enumeration.count (167 : Fin 256) = counts 167 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_168 : enumeration.count (168 : Fin 256) = counts 168 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_169 : enumeration.count (169 : Fin 256) = counts 169 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_170 : enumeration.count (170 : Fin 256) = counts 170 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_171 : enumeration.count (171 : Fin 256) = counts 171 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_172 : enumeration.count (172 : Fin 256) = counts 172 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_173 : enumeration.count (173 : Fin 256) = counts 173 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_174 : enumeration.count (174 : Fin 256) = counts 174 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_175 : enumeration.count (175 : Fin 256) = counts 175 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_176 : enumeration.count (176 : Fin 256) = counts 176 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_177 : enumeration.count (177 : Fin 256) = counts 177 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_178 : enumeration.count (178 : Fin 256) = counts 178 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_179 : enumeration.count (179 : Fin 256) = counts 179 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_180 : enumeration.count (180 : Fin 256) = counts 180 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_181 : enumeration.count (181 : Fin 256) = counts 181 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_182 : enumeration.count (182 : Fin 256) = counts 182 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_183 : enumeration.count (183 : Fin 256) = counts 183 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_184 : enumeration.count (184 : Fin 256) = counts 184 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_185 : enumeration.count (185 : Fin 256) = counts 185 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_186 : enumeration.count (186 : Fin 256) = counts 186 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_187 : enumeration.count (187 : Fin 256) = counts 187 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_188 : enumeration.count (188 : Fin 256) = counts 188 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_189 : enumeration.count (189 : Fin 256) = counts 189 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_190 : enumeration.count (190 : Fin 256) = counts 190 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_191 : enumeration.count (191 : Fin 256) = counts 191 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_192 : enumeration.count (192 : Fin 256) = counts 192 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_193 : enumeration.count (193 : Fin 256) = counts 193 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_194 : enumeration.count (194 : Fin 256) = counts 194 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_195 : enumeration.count (195 : Fin 256) = counts 195 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_196 : enumeration.count (196 : Fin 256) = counts 196 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_197 : enumeration.count (197 : Fin 256) = counts 197 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_198 : enumeration.count (198 : Fin 256) = counts 198 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_199 : enumeration.count (199 : Fin 256) = counts 199 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_200 : enumeration.count (200 : Fin 256) = counts 200 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_201 : enumeration.count (201 : Fin 256) = counts 201 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_202 : enumeration.count (202 : Fin 256) = counts 202 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_203 : enumeration.count (203 : Fin 256) = counts 203 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_204 : enumeration.count (204 : Fin 256) = counts 204 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_205 : enumeration.count (205 : Fin 256) = counts 205 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_206 : enumeration.count (206 : Fin 256) = counts 206 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_207 : enumeration.count (207 : Fin 256) = counts 207 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_208 : enumeration.count (208 : Fin 256) = counts 208 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_209 : enumeration.count (209 : Fin 256) = counts 209 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_210 : enumeration.count (210 : Fin 256) = counts 210 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_211 : enumeration.count (211 : Fin 256) = counts 211 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_212 : enumeration.count (212 : Fin 256) = counts 212 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_213 : enumeration.count (213 : Fin 256) = counts 213 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_214 : enumeration.count (214 : Fin 256) = counts 214 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_215 : enumeration.count (215 : Fin 256) = counts 215 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_216 : enumeration.count (216 : Fin 256) = counts 216 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_217 : enumeration.count (217 : Fin 256) = counts 217 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_218 : enumeration.count (218 : Fin 256) = counts 218 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_219 : enumeration.count (219 : Fin 256) = counts 219 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_220 : enumeration.count (220 : Fin 256) = counts 220 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_221 : enumeration.count (221 : Fin 256) = counts 221 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_222 : enumeration.count (222 : Fin 256) = counts 222 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_223 : enumeration.count (223 : Fin 256) = counts 223 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_224 : enumeration.count (224 : Fin 256) = counts 224 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_225 : enumeration.count (225 : Fin 256) = counts 225 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_226 : enumeration.count (226 : Fin 256) = counts 226 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_227 : enumeration.count (227 : Fin 256) = counts 227 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_228 : enumeration.count (228 : Fin 256) = counts 228 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_229 : enumeration.count (229 : Fin 256) = counts 229 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_230 : enumeration.count (230 : Fin 256) = counts 230 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_231 : enumeration.count (231 : Fin 256) = counts 231 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_232 : enumeration.count (232 : Fin 256) = counts 232 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_233 : enumeration.count (233 : Fin 256) = counts 233 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_234 : enumeration.count (234 : Fin 256) = counts 234 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_235 : enumeration.count (235 : Fin 256) = counts 235 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_236 : enumeration.count (236 : Fin 256) = counts 236 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_237 : enumeration.count (237 : Fin 256) = counts 237 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_238 : enumeration.count (238 : Fin 256) = counts 238 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_239 : enumeration.count (239 : Fin 256) = counts 239 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_240 : enumeration.count (240 : Fin 256) = counts 240 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_241 : enumeration.count (241 : Fin 256) = counts 241 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_242 : enumeration.count (242 : Fin 256) = counts 242 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_243 : enumeration.count (243 : Fin 256) = counts 243 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_244 : enumeration.count (244 : Fin 256) = counts 244 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_245 : enumeration.count (245 : Fin 256) = counts 245 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_246 : enumeration.count (246 : Fin 256) = counts 246 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_247 : enumeration.count (247 : Fin 256) = counts 247 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_248 : enumeration.count (248 : Fin 256) = counts 248 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_249 : enumeration.count (249 : Fin 256) = counts 249 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_250 : enumeration.count (250 : Fin 256) = counts 250 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_251 : enumeration.count (251 : Fin 256) = counts 251 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_252 : enumeration.count (252 : Fin 256) = counts 252 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_253 : enumeration.count (253 : Fin 256) = counts 253 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_254 : enumeration.count (254 : Fin 256) = counts 254 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_255 : enumeration.count (255 : Fin 256) = counts 255 := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem counts_check (i : Fin 256) : enumeration.count i = counts i := by
  fin_cases i
  · exact count_0
  · exact count_1
  · exact count_2
  · exact count_3
  · exact count_4
  · exact count_5
  · exact count_6
  · exact count_7
  · exact count_8
  · exact count_9
  · exact count_10
  · exact count_11
  · exact count_12
  · exact count_13
  · exact count_14
  · exact count_15
  · exact count_16
  · exact count_17
  · exact count_18
  · exact count_19
  · exact count_20
  · exact count_21
  · exact count_22
  · exact count_23
  · exact count_24
  · exact count_25
  · exact count_26
  · exact count_27
  · exact count_28
  · exact count_29
  · exact count_30
  · exact count_31
  · exact count_32
  · exact count_33
  · exact count_34
  · exact count_35
  · exact count_36
  · exact count_37
  · exact count_38
  · exact count_39
  · exact count_40
  · exact count_41
  · exact count_42
  · exact count_43
  · exact count_44
  · exact count_45
  · exact count_46
  · exact count_47
  · exact count_48
  · exact count_49
  · exact count_50
  · exact count_51
  · exact count_52
  · exact count_53
  · exact count_54
  · exact count_55
  · exact count_56
  · exact count_57
  · exact count_58
  · exact count_59
  · exact count_60
  · exact count_61
  · exact count_62
  · exact count_63
  · exact count_64
  · exact count_65
  · exact count_66
  · exact count_67
  · exact count_68
  · exact count_69
  · exact count_70
  · exact count_71
  · exact count_72
  · exact count_73
  · exact count_74
  · exact count_75
  · exact count_76
  · exact count_77
  · exact count_78
  · exact count_79
  · exact count_80
  · exact count_81
  · exact count_82
  · exact count_83
  · exact count_84
  · exact count_85
  · exact count_86
  · exact count_87
  · exact count_88
  · exact count_89
  · exact count_90
  · exact count_91
  · exact count_92
  · exact count_93
  · exact count_94
  · exact count_95
  · exact count_96
  · exact count_97
  · exact count_98
  · exact count_99
  · exact count_100
  · exact count_101
  · exact count_102
  · exact count_103
  · exact count_104
  · exact count_105
  · exact count_106
  · exact count_107
  · exact count_108
  · exact count_109
  · exact count_110
  · exact count_111
  · exact count_112
  · exact count_113
  · exact count_114
  · exact count_115
  · exact count_116
  · exact count_117
  · exact count_118
  · exact count_119
  · exact count_120
  · exact count_121
  · exact count_122
  · exact count_123
  · exact count_124
  · exact count_125
  · exact count_126
  · exact count_127
  · exact count_128
  · exact count_129
  · exact count_130
  · exact count_131
  · exact count_132
  · exact count_133
  · exact count_134
  · exact count_135
  · exact count_136
  · exact count_137
  · exact count_138
  · exact count_139
  · exact count_140
  · exact count_141
  · exact count_142
  · exact count_143
  · exact count_144
  · exact count_145
  · exact count_146
  · exact count_147
  · exact count_148
  · exact count_149
  · exact count_150
  · exact count_151
  · exact count_152
  · exact count_153
  · exact count_154
  · exact count_155
  · exact count_156
  · exact count_157
  · exact count_158
  · exact count_159
  · exact count_160
  · exact count_161
  · exact count_162
  · exact count_163
  · exact count_164
  · exact count_165
  · exact count_166
  · exact count_167
  · exact count_168
  · exact count_169
  · exact count_170
  · exact count_171
  · exact count_172
  · exact count_173
  · exact count_174
  · exact count_175
  · exact count_176
  · exact count_177
  · exact count_178
  · exact count_179
  · exact count_180
  · exact count_181
  · exact count_182
  · exact count_183
  · exact count_184
  · exact count_185
  · exact count_186
  · exact count_187
  · exact count_188
  · exact count_189
  · exact count_190
  · exact count_191
  · exact count_192
  · exact count_193
  · exact count_194
  · exact count_195
  · exact count_196
  · exact count_197
  · exact count_198
  · exact count_199
  · exact count_200
  · exact count_201
  · exact count_202
  · exact count_203
  · exact count_204
  · exact count_205
  · exact count_206
  · exact count_207
  · exact count_208
  · exact count_209
  · exact count_210
  · exact count_211
  · exact count_212
  · exact count_213
  · exact count_214
  · exact count_215
  · exact count_216
  · exact count_217
  · exact count_218
  · exact count_219
  · exact count_220
  · exact count_221
  · exact count_222
  · exact count_223
  · exact count_224
  · exact count_225
  · exact count_226
  · exact count_227
  · exact count_228
  · exact count_229
  · exact count_230
  · exact count_231
  · exact count_232
  · exact count_233
  · exact count_234
  · exact count_235
  · exact count_236
  · exact count_237
  · exact count_238
  · exact count_239
  · exact count_240
  · exact count_241
  · exact count_242
  · exact count_243
  · exact count_244
  · exact count_245
  · exact count_246
  · exact count_247
  · exact count_248
  · exact count_249
  · exact count_250
  · exact count_251
  · exact count_252
  · exact count_253
  · exact count_254
  · exact count_255

def upperWord (i : Fin 256) : List (Fin 6) :=
  (#[[], [], [0], [4, 5], [], [], [], [0, 4, 5], [], [], [], [], [], [], [], [], [], [1, 2, 3, 4], [0, 1, 2, 3, 4], [1, 2, 3, 5], [0, 1, 2, 3, 5], [], [], [], [], [1, 2, 3], [0, 1, 2, 3], [1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5], [], [], [], [], [1, 5], [0, 1, 5], [1, 4], [0, 1, 4], [], [], [], [], [], [], [], [], [], [], [], [2, 3, 5], [], [0, 2, 3, 5], [2, 3, 4], [], [], [], [0, 2, 3, 4], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [2], [0, 2], [2, 4, 5], [0, 2, 4, 5], [], [], [], [], [], [], [], [], [], [], [], [2, 3, 4, 5], [], [0, 2, 3, 4, 5], [2, 3], [], [], [], [0, 2, 3], [], [], [], [], [], [], [], [], [], [3, 4, 5], [0, 3, 4, 5], [3], [0, 3], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [2, 4], [0, 2, 4], [2, 5], [0, 2, 5], [], [], [], [], [], [], [], [], [], [], [], [1, 2, 4, 5], [0, 1, 2, 4, 5], [], [1, 2], [], [], [0, 1, 2], [], [], [], [], [], [], [], [], [], [1, 2, 5], [0, 1, 2, 5], [], [1, 2, 4], [], [], [0, 1, 2, 4], [], [4], [], [0, 4], [5], [], [], [], [0, 5], [], [3, 5], [0, 3, 5], [3, 4], [0, 3, 4], [], [], [], [], [1, 4, 5], [0, 1, 4, 5], [1], [0, 1], [], [], [], [1, 3, 4], [0, 1, 3, 4], [], [1, 3, 5], [], [], [0, 1, 3, 5], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [1, 3], [0, 1, 3], [], [1, 3, 4, 5], [], [], [0, 1, 3, 4, 5], [], [], [], [], [], [], [], [], []] : Array (List (Fin 6)))[i.val]!
def lowerWord (a : Fin 6) : List (Fin 256) :=
  (#[[2], [176, 35], [73], [107], [176], [179]] : Array (List (Fin 256)))[a.val]!

set_option maxRecDepth 8192 in
theorem upper_check : ∀ i : Fin 256, 256 ≤ 2 * counts i → ∀ v : Fin 4,
    perm i ⟨v.val, by omega⟩ =
      eval targetPerm (upperWord i) ⟨v.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem lower_selected : ∀ a : Fin 6, ∀ i ∈ lowerWord a, 256 ≤ 2 * counts i := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem lower_check : ∀ a : Fin 6, ∀ v : Fin 4,
    ((lowerWord a).map perm).prod ⟨v.val, by omega⟩ =
      targetPerm a ⟨v.val, by omega⟩ := by
  decide +kernel


end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.E64Containment.CentralizerCertificates.SpanCertificates.RowThree
