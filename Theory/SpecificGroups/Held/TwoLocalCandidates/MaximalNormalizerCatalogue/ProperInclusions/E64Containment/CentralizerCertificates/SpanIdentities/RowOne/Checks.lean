module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment.CentralizerCertificates.SpanIdentities.LiteralBridge
import Mathlib.Tactic.FinCases
public import Mathlib.Order.Fin.Basic

/-!
# The centralizer-index span of literal Held core candidate 1

A checked right-generator transition table and four-point signatures certify
an injective exhaustive word enumeration. The resulting finite multiplication
computes all singleton centralizers, including every element outside the E64
row. Explicit word witnesses prove that the selected elements generate exactly
row 21. All permutation equalities use the faithful literal Held action.

Source: the original ATLAS words, GLS3 Table 5.3p, and quasithin condition E.
The generator and discovery data in `source/` are untrusted; every finite check
below is performed by the Lean kernel.
-/

@[expose] public section

namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.E64Containment.CentralizerCertificates.SpanCertificates.RowOne
open Subgroup

-- Serial elaboration prevents independent kernel reductions retaining memory together.
set_option Elab.async false

def code (i : Fin 256) : List (Fin 8) :=
  (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then [] else [6]) else (if i.val < 3 then [6, 7, 2] else [7, 2])) else (if i.val < 6 then (if i.val < 5 then [3, 4, 6, 7] else [3, 4, 7]) else (if i.val < 7 then [2, 3, 4, 5] else [1, 4, 6, 1]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then [0, 1, 2, 4, 5] else [0, 1, 2, 6, 4]) else (if i.val < 11 then [0, 1, 4, 6, 7] else [0, 1, 4, 7])) else (if i.val < 14 then (if i.val < 13 then [1, 2, 4, 5] else [1, 2, 6, 4]) else (if i.val < 15 then [1, 4, 6, 7] else [1, 4, 7])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then [1, 5] else [1, 5, 6]) else (if i.val < 19 then [1, 2, 6, 7] else [1, 2, 7])) else (if i.val < 22 then (if i.val < 21 then [1, 3, 4] else [1, 3, 4, 6]) else (if i.val < 23 then [4, 6, 1, 7] else [4, 7, 1]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then [0, 1, 7, 4] else [0, 1, 6, 4, 7]) else (if i.val < 27 then [0, 1, 2, 4, 6] else [0, 1, 2, 4])) else (if i.val < 30 then (if i.val < 29 then [1, 2, 4, 6, 7] else [1, 2, 4, 7]) else (if i.val < 31 then [1, 4, 5] else [1, 6, 4]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then [0, 6, 1, 4, 7] else [0, 7, 1, 4]) else (if i.val < 35 then [0, 1, 3, 4, 5] else [0, 1, 3, 6, 4])) else (if i.val < 38 then (if i.val < 37 then [0, 1, 2, 6] else [0, 1, 2]) else (if i.val < 39 then [0, 1, 5, 7] else [0, 1, 5, 6, 7]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then [2, 3, 5] else [1, 6, 1]) else (if i.val < 43 then [3, 6, 7] else [3, 7])) else (if i.val < 46 then (if i.val < 45 then [5, 7] else [5, 6, 7]) else (if i.val < 47 then [2, 6] else [2])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then [6, 4] else [4, 5]) else (if i.val < 51 then [2, 4, 7] else [2, 4, 6, 7])) else (if i.val < 54 then (if i.val < 53 then [2, 4] else [2, 4, 6]) else (if i.val < 55 then [6, 4, 7] else [7, 4]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then [0, 1, 3, 6, 4, 7] else [0, 1, 3, 7, 4]) else (if i.val < 59 then [0, 1, 2, 3, 4] else [0, 6, 1, 4])) else (if i.val < 62 then (if i.val < 61 then [6, 7, 3] else [7, 3]) else (if i.val < 63 then [2, 3] else [2, 3, 6])))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then [0, 3, 4, 7] else [0, 3, 4, 6, 7]) else (if i.val < 67 then [0, 1, 4, 6, 1] else [7, 0, 4, 7])) else (if i.val < 70 then (if i.val < 69 then [0, 3] else [0, 3, 6]) else (if i.val < 71 then [6, 7, 0] else [7, 0]))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then [1, 3, 6, 4, 7] else [1, 3, 7, 4]) else (if i.val < 75 then [1, 2, 3, 4] else [6, 1, 4])) else (if i.val < 78 then (if i.val < 77 then [1, 7, 4] else [1, 6, 4, 7]) else (if i.val < 79 then [1, 2, 4, 6] else [1, 2, 4])))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then [0, 4, 6, 1] else [0, 4, 6, 1, 6]) else (if i.val < 83 then [0, 1, 3, 4, 7] else [0, 1, 3, 4, 6, 7])) else (if i.val < 86 then (if i.val < 85 then [6, 1, 7] else [7, 1]) else (if i.val < 87 then [1, 3] else [1, 3, 6]))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then [0, 4, 6, 7, 0] else [0, 4, 7, 0]) else (if i.val < 91 then [3, 4] else [3, 4, 6])) else (if i.val < 94 then (if i.val < 93 then [0, 2, 7] else [0, 2, 6, 7]) else (if i.val < 95 then [0, 5, 6] else [0, 5]))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then [3] else [3, 6]) else (if i.val < 99 then [0, 6, 7, 0] else [0, 7, 0])) else (if i.val < 102 then (if i.val < 101 then [0, 1, 4, 6] else [0, 1, 4]) else (if i.val < 103 then [0, 1, 2, 7, 4] else [0, 1, 2, 6, 4, 7]))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then [0, 7, 1] else [0, 6, 1, 7]) else (if i.val < 107 then [0, 1, 3, 6] else [0, 1, 3])) else (if i.val < 110 then (if i.val < 109 then [0, 5, 6, 7] else [0, 5, 7]) else (if i.val < 111 then [0, 2] else [0, 2, 6])))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then [0, 2, 4, 6] else [0, 2, 4]) else (if i.val < 115 then [0, 7, 4] else [0, 6, 4, 7])) else (if i.val < 118 then (if i.val < 117 then [4, 7] else [4, 6, 7]) else (if i.val < 119 then [2, 6, 4] else [2, 4, 5]))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then [1, 3, 5] else [2, 6, 1]) else (if i.val < 123 then [5, 6, 1, 7] else [5, 7, 1])) else (if i.val < 126 then (if i.val < 125 then [1, 2] else [1, 2, 6]) else (if i.val < 127 then [1, 5, 6, 7] else [1, 5, 7]))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then [0, 1, 6, 7] else [0, 1, 7]) else (if i.val < 131 then [0, 1, 2, 5] else [0, 3, 6, 1])) else (if i.val < 134 then (if i.val < 133 then [0, 5, 6, 1] else [0, 1, 2, 3]) else (if i.val < 135 then [0, 1, 7, 3] else [0, 1, 6, 7, 3]))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then [0, 2, 5] else [0, 2, 5, 6]) else (if i.val < 139 then [0, 6, 7] else [0, 7])) else (if i.val < 142 then (if i.val < 141 then [0, 1, 3, 5] else [0, 2, 6, 1]) else (if i.val < 143 then [0, 5, 6, 1, 7] else [0, 5, 7, 1])))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then [0, 4, 6, 7] else [0, 4, 7]) else (if i.val < 147 then [0, 2, 4, 5] else [0, 2, 6, 4])) else (if i.val < 150 then (if i.val < 149 then [0, 7, 3] else [0, 6, 7, 3]) else (if i.val < 151 then [0, 2, 3, 6] else [0, 2, 3]))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then [0, 1, 3, 6, 7] else [0, 1, 3, 7]) else (if i.val < 155 then [0, 6, 1, 6] else [0, 6, 1])) else (if i.val < 158 then (if i.val < 157 then [5, 7, 0] else [5, 6, 7, 0]) else (if i.val < 159 then [0, 3, 5, 6] else [0, 3, 5]))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then [1, 7] else [1, 6, 7]) else (if i.val < 163 then [3, 6, 1] else [1, 2, 5])) else (if i.val < 166 then (if i.val < 165 then [1, 2, 3] else [5, 6, 1]) else (if i.val < 167 then [1, 6, 7, 3] else [1, 7, 3]))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then [0, 3, 4, 5] else [0, 3, 6, 4]) else (if i.val < 171 then [6, 4, 7, 0] else [7, 0, 4])) else (if i.val < 174 then (if i.val < 173 then [2, 6, 7] else [2, 7]) else (if i.val < 175 then [5] else [5, 6])))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then [1, 7, 2] else [1, 6, 7, 2]) else (if i.val < 179 then [1, 6] else [1])) else (if i.val < 182 then (if i.val < 181 then [1, 3, 7] else [1, 3, 6, 7]) else (if i.val < 183 then [6, 1] else [6, 1, 6]))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then [3, 4, 5] else [3, 6, 4]) else (if i.val < 187 then [0, 6, 4, 7, 0] else [0, 7, 0, 4])) else (if i.val < 190 then (if i.val < 189 then [0, 1, 3, 4] else [0, 1, 3, 4, 6]) else (if i.val < 191 then [0, 4, 6, 1, 7] else [0, 4, 7, 1])))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then [7, 1, 4] else [6, 1, 4, 7]) else (if i.val < 195 then [1, 3, 6, 4] else [1, 3, 4, 5])) else (if i.val < 198 then (if i.val < 197 then [4, 7, 0] else [4, 6, 7, 0]) else (if i.val < 199 then [0, 3, 4, 6] else [0, 3, 4]))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then [0, 1, 5, 6] else [0, 1, 5]) else (if i.val < 203 then [0, 1, 2, 7] else [0, 1, 2, 6, 7])) else (if i.val < 206 then (if i.val < 205 then [2, 6, 4, 7] else [2, 7, 4]) else (if i.val < 207 then [4] else [4, 6])))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then [2, 5] else [2, 5, 6]) else (if i.val < 211 then [6, 7] else [7])) else (if i.val < 214 then (if i.val < 213 then [0, 1, 6, 1] else [0, 2, 3, 5]) else (if i.val < 215 then [0, 3, 7] else [0, 3, 6, 7]))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then [0] else [0, 6]) else (if i.val < 219 then [0, 6, 7, 2] else [0, 7, 2])) else (if i.val < 222 then (if i.val < 221 then [1, 6, 1, 4] else [2, 3, 4]) else (if i.val < 223 then [3, 7, 4] else [3, 6, 4, 7]))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then [0, 1, 2, 4, 6, 7] else [0, 1, 2, 4, 7]) else (if i.val < 227 then [0, 1, 4, 5] else [0, 1, 6, 4])) else (if i.val < 230 then (if i.val < 229 then [0, 1, 6, 7, 2] else [0, 1, 7, 2]) else (if i.val < 231 then [0, 1] else [0, 1, 6]))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then [4, 6, 1, 6] else [4, 6, 1]) else (if i.val < 235 then [1, 3, 4, 6, 7] else [1, 3, 4, 7])) else (if i.val < 238 then (if i.val < 237 then [0, 1, 6, 1, 4] else [0, 2, 3, 4]) else (if i.val < 239 then [0, 3, 7, 4] else [0, 3, 6, 4, 7])))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then [0, 4, 5] else [0, 6, 4]) else (if i.val < 243 then [0, 2, 4, 6, 7] else [0, 2, 4, 7])) else (if i.val < 246 then (if i.val < 245 then [2, 3, 7] else [2, 3, 6, 7]) else (if i.val < 247 then [3, 5, 6] else [3, 5]))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then [0, 2, 6, 4, 7] else [0, 2, 7, 4]) else (if i.val < 251 then [0, 4] else [0, 4, 6])) else (if i.val < 254 then (if i.val < 253 then [1, 4] else [1, 4, 6]) else (if i.val < 255 then [1, 2, 6, 4, 7] else [1, 2, 7, 4]))))))))
def step (i : Fin 256) (a : Fin 8) : Fin 256 :=
  Fin.ofNat 256 ((if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then [216, 179, 47, 96, 206, 174, 1, 211] else [217, 182, 46, 97, 48, 175, 0, 210]) else (if i.val < 3 then [215, 177, 210, 245, 204, 172, 3, 46] else [214, 180, 211, 244, 50, 173, 2, 47])) else (if i.val < 6 then (if i.val < 5 then [248, 234, 88, 54, 42, 223, 5, 185] else [249, 255, 89, 55, 61, 222, 4, 184]) else (if i.val < 7 then [67, 232, 184, 119, 40, 221, 7, 89] else [66, 253, 185, 118, 63, 220, 6, 88]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then [12, 146, 226, 81, 130, 27, 9, 102] else [13, 198, 227, 80, 36, 26, 8, 103]) else (if i.val < 11 then [22, 144, 103, 56, 128, 25, 11, 227] else [23, 196, 102, 57, 38, 24, 10, 226])) else (if i.val < 14 then (if i.val < 13 then [8, 119, 30, 232, 163, 79, 13, 255] else [9, 91, 31, 233, 125, 78, 12, 254]) else (if i.val < 15 then [190, 117, 254, 72, 161, 77, 15, 31] else [191, 89, 255, 73, 127, 76, 14, 30])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then [201, 174, 163, 120, 30, 179, 17, 127] else [200, 63, 162, 121, 253, 178, 16, 126]) else (if i.val < 19 then [135, 172, 126, 84, 28, 177, 19, 162] else [134, 61, 127, 85, 255, 176, 18, 163])) else (if i.val < 22 then (if i.val < 21 then [188, 90, 74, 252, 86, 195, 21, 235] else [189, 118, 75, 253, 121, 194, 20, 234]) else (if i.val < 23 then [10, 88, 234, 28, 84, 193, 23, 75] else [11, 116, 235, 29, 123, 192, 22, 74]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then [192, 171, 225, 82, 129, 11, 25, 101] else [193, 115, 224, 83, 39, 10, 24, 100]) else (if i.val < 27 then [78, 169, 100, 59, 131, 9, 27, 224] else [79, 113, 101, 58, 37, 8, 26, 225])) else (if i.val < 30 then (if i.val < 29 then [56, 51, 77, 22, 18, 254, 29, 13] else [57, 222, 76, 23, 176, 255, 28, 12]) else (if i.val < 31 then [226, 49, 12, 195, 16, 252, 31, 76] else [227, 220, 13, 194, 178, 253, 30, 77]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then [77, 170, 56, 103, 142, 190, 33, 80] else [76, 114, 57, 102, 104, 191, 32, 81]) else (if i.val < 35 then [195, 168, 81, 226, 140, 188, 35, 57] else [194, 112, 80, 227, 106, 189, 34, 56])) else (if i.val < 38 then (if i.val < 37 then [125, 158, 231, 132, 9, 131, 37, 203] else [124, 110, 230, 133, 27, 130, 36, 202]) else (if i.val < 39 then [123, 156, 202, 153, 11, 129, 39, 230] else [122, 108, 203, 152, 25, 128, 38, 231]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then [213, 183, 247, 208, 6, 62, 41, 99] else [212, 178, 246, 209, 220, 63, 40, 98]) else (if i.val < 43 then [218, 181, 98, 45, 4, 60, 43, 246] else [219, 176, 99, 44, 222, 61, 42, 247])) else (if i.val < 46 then (if i.val < 45 then [156, 123, 173, 43, 116, 211, 45, 0] else [157, 126, 172, 42, 54, 210, 44, 1]) else (if i.val < 47 then [111, 121, 1, 63, 118, 209, 47, 172] else [110, 124, 0, 62, 52, 208, 46, 173])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then [241, 75, 118, 185, 1, 207, 49, 54] else [240, 30, 119, 184, 174, 206, 48, 55]) else (if i.val < 51 then [238, 73, 55, 89, 3, 205, 51, 119] else [239, 28, 54, 88, 172, 204, 50, 118])) else (if i.val < 54 then (if i.val < 53 then [113, 79, 206, 221, 47, 119, 53, 50] else [112, 194, 207, 220, 209, 118, 52, 51]) else (if i.val < 55 then [170, 77, 51, 4, 45, 117, 55, 207] else [171, 192, 50, 5, 211, 116, 54, 206]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then [28, 239, 32, 10, 135, 83, 57, 189] else [29, 243, 33, 11, 153, 82, 56, 188]) else (if i.val < 59 then [74, 237, 188, 27, 133, 81, 59, 33] else [75, 241, 189, 26, 155, 80, 58, 32])) else (if i.val < 62 then (if i.val < 61 then [93, 166, 245, 210, 223, 42, 61, 97] else [92, 19, 244, 211, 5, 43, 60, 96]) else (if i.val < 63 then [151, 164, 96, 47, 221, 40, 63, 244] else [150, 17, 97, 46, 7, 41, 62, 245])))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then [205, 102, 196, 114, 148, 238, 65, 168] else [204, 83, 197, 115, 215, 239, 64, 169]) else (if i.val < 67 then [7, 100, 169, 147, 150, 236, 67, 197] else [6, 81, 168, 146, 213, 237, 66, 196])) else (if i.val < 70 then (if i.val < 69 then [96, 107, 151, 216, 199, 159, 69, 214] else [97, 131, 150, 217, 169, 158, 68, 215]) else (if i.val < 71 then [210, 105, 215, 93, 197, 157, 71, 150] else [211, 129, 214, 92, 171, 156, 70, 151]))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then [224, 223, 193, 14, 166, 234, 73, 21] else [225, 50, 192, 15, 180, 235, 72, 20]) else (if i.val < 75 then [58, 221, 20, 79, 164, 232, 75, 192] else [59, 48, 21, 78, 182, 233, 74, 193])) else (if i.val < 78 then (if i.val < 77 then [33, 187, 29, 235, 160, 15, 77, 252] else [32, 54, 28, 234, 126, 14, 76, 253]) else (if i.val < 79 then [26, 185, 253, 75, 162, 13, 79, 28] else [27, 52, 252, 74, 124, 12, 78, 29])))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then [233, 251, 35, 9, 132, 59, 81, 190] else [232, 67, 34, 8, 154, 58, 80, 191]) else (if i.val < 83 then [255, 249, 191, 24, 134, 57, 83, 34] else [254, 65, 190, 25, 152, 56, 82, 35])) else (if i.val < 86 then (if i.val < 85 then [128, 98, 181, 18, 22, 122, 85, 165] else [129, 211, 180, 19, 192, 123, 84, 164]) else (if i.val < 87 then [107, 96, 164, 179, 20, 120, 87, 180] else [106, 209, 165, 178, 194, 121, 86, 181]))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then [144, 22, 4, 51, 98, 186, 89, 220] else [145, 15, 5, 50, 244, 187, 88, 221]) else (if i.val < 91 then [199, 20, 221, 206, 96, 184, 91, 5] else [198, 13, 220, 207, 246, 185, 90, 4])) else (if i.val < 94 then (if i.val < 93 then [61, 134, 109, 71, 249, 219, 93, 136] else [60, 203, 108, 70, 242, 218, 92, 137]) else (if i.val < 95 then [175, 132, 137, 158, 251, 217, 95, 108] else [174, 201, 136, 159, 240, 216, 94, 109]))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then [68, 86, 62, 0, 90, 247, 97, 43] else [69, 162, 63, 1, 185, 246, 96, 42]) else (if i.val < 99 then [138, 84, 42, 172, 88, 245, 99, 63] else [139, 160, 43, 173, 187, 244, 98, 62])) else (if i.val < 102 then (if i.val < 101 then [253, 66, 26, 189, 200, 227, 101, 10] else [252, 250, 27, 188, 230, 226, 100, 11]) else (if i.val < 103 then [235, 64, 11, 33, 202, 225, 103, 27] else [234, 248, 10, 32, 228, 224, 102, 26]))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then [160, 139, 153, 202, 33, 143, 105, 133] else [161, 70, 152, 203, 190, 142, 104, 132]) else (if i.val < 107 then [87, 137, 132, 231, 35, 141, 107, 152] else [86, 68, 133, 230, 188, 140, 106, 153])) else (if i.val < 110 then (if i.val < 109 then [245, 39, 93, 215, 115, 138, 109, 217] else [244, 143, 92, 214, 145, 139, 108, 216]) else (if i.val < 111 then [47, 37, 216, 151, 113, 136, 111, 92] else [46, 141, 217, 150, 147, 137, 110, 93])))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then [53, 35, 251, 236, 137, 147, 113, 242] else [52, 27, 250, 237, 110, 146, 112, 243]) else (if i.val < 115 then [187, 33, 243, 64, 139, 145, 115, 250] else [186, 25, 242, 65, 108, 144, 114, 251])) else (if i.val < 118 then (if i.val < 117 then [196, 23, 205, 222, 44, 55, 117, 49] else [197, 14, 204, 223, 210, 54, 116, 48]) else (if i.val < 119 then [147, 21, 48, 7, 46, 53, 119, 204] else [146, 12, 49, 6, 208, 52, 118, 205]))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then [140, 247, 183, 16, 195, 86, 121, 167] else [141, 46, 182, 17, 21, 87, 120, 166]) else (if i.val < 123 then [39, 245, 166, 177, 193, 84, 123, 182] else [38, 44, 167, 176, 23, 85, 122, 183])) else (if i.val < 126 then (if i.val < 125 then [37, 47, 179, 164, 79, 163, 125, 19] else [36, 246, 178, 165, 13, 162, 124, 18]) else (if i.val < 127 then [142, 45, 18, 181, 77, 161, 127, 178] else [143, 244, 19, 180, 15, 160, 126, 179]))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then [84, 138, 228, 135, 10, 39, 129, 200] else [85, 71, 229, 134, 24, 38, 128, 201]) else (if i.val < 131 then [163, 136, 201, 154, 8, 37, 131, 229] else [162, 69, 200, 155, 26, 36, 130, 228])) else (if i.val < 134 then (if i.val < 133 then [165, 94, 106, 36, 80, 155, 133, 142] else [164, 151, 107, 37, 58, 154, 132, 143]) else (if i.val < 135 then [19, 92, 143, 129, 82, 153, 135, 107] else [18, 149, 142, 128, 56, 152, 134, 106]))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then [208, 130, 95, 213, 146, 110, 137, 219] else [209, 106, 94, 212, 112, 111, 136, 218]) else (if i.val < 139 then [98, 128, 218, 149, 144, 108, 139, 94] else [99, 104, 219, 148, 114, 109, 138, 95])) else (if i.val < 142 then (if i.val < 141 then [120, 159, 154, 201, 34, 107, 141, 134] else [121, 111, 155, 200, 189, 106, 140, 135]) else (if i.val < 143 then [126, 157, 135, 228, 32, 105, 143, 155] else [127, 109, 134, 229, 191, 104, 142, 154])))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then [88, 10, 248, 239, 138, 115, 145, 241] else [89, 191, 249, 238, 109, 114, 144, 240]) else (if i.val < 147 then [119, 8, 240, 67, 136, 113, 147, 249] else [118, 189, 241, 66, 111, 112, 146, 248])) else (if i.val < 150 then (if i.val < 149 then [173, 202, 156, 139, 64, 214, 149, 68] else [172, 135, 157, 138, 239, 215, 148, 69]) else (if i.val < 151 then [63, 200, 69, 111, 66, 212, 151, 157] else [62, 133, 68, 110, 237, 213, 150, 156]))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then [177, 215, 105, 39, 83, 135, 153, 141] else [176, 219, 104, 38, 57, 134, 152, 140]) else (if i.val < 155 then [183, 213, 140, 130, 81, 133, 155, 104] else [182, 217, 141, 131, 59, 132, 154, 105])) else (if i.val < 158 then (if i.val < 157 then [44, 38, 148, 219, 196, 71, 157, 213] else [45, 142, 149, 218, 170, 70, 156, 212]) else (if i.val < 159 then [246, 36, 212, 94, 198, 69, 159, 149] else [247, 140, 213, 95, 168, 68, 158, 148]))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then [104, 99, 176, 167, 76, 127, 161, 16] else [105, 210, 177, 166, 14, 126, 160, 17]) else (if i.val < 163 then [131, 97, 17, 182, 78, 125, 163, 177] else [130, 208, 16, 183, 12, 124, 162, 176])) else (if i.val < 166 then (if i.val < 165 then [133, 62, 86, 124, 74, 183, 165, 123] else [132, 175, 87, 125, 233, 182, 164, 122]) else (if i.val < 167 then [203, 60, 122, 161, 72, 181, 167, 87] else [202, 173, 123, 160, 235, 180, 166, 86]))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then [184, 34, 67, 240, 159, 199, 169, 238] else [185, 26, 66, 241, 69, 198, 168, 239]) else (if i.val < 171 then [54, 32, 239, 248, 157, 197, 171, 66] else [55, 24, 238, 249, 71, 196, 170, 67])) else (if i.val < 174 then (if i.val < 173 then [149, 18, 45, 98, 51, 2, 173, 209] else [148, 167, 44, 99, 205, 3, 172, 208]) else (if i.val < 175 then [95, 16, 208, 247, 49, 0, 175, 44] else [94, 165, 209, 246, 207, 1, 174, 45])))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then [153, 43, 160, 123, 29, 19, 177, 124] else [152, 2, 161, 122, 254, 18, 176, 125]) else (if i.val < 179 then [231, 41, 125, 87, 31, 17, 179, 161] else [230, 0, 124, 86, 252, 16, 178, 160])) else (if i.val < 182 then (if i.val < 181 then [229, 3, 85, 127, 73, 167, 181, 120] else [228, 42, 84, 126, 234, 166, 180, 121]) else (if i.val < 183 then [155, 1, 121, 162, 75, 165, 183, 84] else [154, 40, 120, 163, 232, 164, 182, 85]))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then [168, 195, 6, 49, 247, 90, 185, 222] else [169, 78, 7, 48, 97, 91, 184, 223]) else (if i.val < 187 then [115, 193, 223, 204, 245, 88, 187, 7] else [114, 76, 222, 205, 99, 89, 186, 6])) else (if i.val < 190 then (if i.val < 189 then [20, 199, 58, 101, 107, 34, 189, 82] else [21, 147, 59, 100, 141, 35, 188, 83]) else (if i.val < 191 then [14, 197, 83, 224, 105, 32, 191, 59] else [15, 145, 82, 225, 143, 33, 190, 58])))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then [24, 55, 73, 255, 85, 23, 193, 232] else [25, 186, 72, 254, 122, 22, 192, 233]) else (if i.val < 195 then [35, 53, 233, 31, 87, 21, 195, 72] else [34, 184, 232, 30, 120, 20, 194, 73])) else (if i.val < 198 then (if i.val < 197 then [116, 11, 64, 243, 156, 171, 197, 237] else [117, 190, 65, 242, 70, 170, 196, 236]) else (if i.val < 199 then [91, 9, 236, 251, 158, 169, 199, 65] else [90, 188, 237, 250, 68, 168, 198, 64]))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then [17, 150, 131, 141, 100, 231, 201, 39] else [16, 95, 130, 140, 226, 230, 200, 38]) else (if i.val < 203 then [167, 148, 38, 104, 102, 229, 203, 130] else [166, 93, 39, 105, 224, 228, 202, 131])) else (if i.val < 206 then (if i.val < 205 then [65, 254, 117, 186, 2, 51, 205, 53] else [64, 235, 116, 187, 173, 50, 204, 52]) else (if i.val < 207 then [250, 252, 52, 90, 0, 49, 207, 116] else [251, 233, 53, 91, 175, 48, 206, 117])))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then [136, 163, 174, 40, 119, 47, 209, 3] else [137, 87, 175, 41, 53, 46, 208, 2]) else (if i.val < 211 then [70, 161, 2, 60, 117, 45, 211, 175] else [71, 85, 3, 61, 55, 44, 210, 174])) else (if i.val < 214 then (if i.val < 213 then [41, 231, 158, 137, 236, 150, 213, 70] else [40, 154, 159, 136, 67, 151, 212, 71]) else (if i.val < 215 then [3, 229, 71, 109, 238, 148, 215, 159] else [2, 152, 70, 108, 65, 149, 214, 158]))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then [0, 230, 110, 68, 250, 95, 217, 139] else [1, 155, 111, 69, 241, 94, 216, 138]) else (if i.val < 219 then [42, 228, 138, 157, 248, 93, 219, 111] else [43, 153, 139, 156, 243, 92, 218, 110])) else (if i.val < 222 then (if i.val < 221 then [236, 31, 91, 53, 41, 7, 221, 186] else [237, 74, 90, 52, 62, 6, 220, 187]) else (if i.val < 223 then [243, 29, 187, 116, 43, 5, 223, 90] else [242, 72, 186, 117, 60, 4, 222, 91]))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then [72, 242, 25, 190, 203, 103, 225, 9] else [73, 238, 24, 191, 229, 102, 224, 8]) else (if i.val < 227 then [30, 240, 8, 34, 201, 101, 227, 24] else [31, 236, 9, 35, 231, 100, 226, 25])) else (if i.val < 230 then (if i.val < 229 then [181, 218, 128, 142, 103, 203, 229, 36] else [180, 214, 129, 143, 225, 202, 228, 37]) else (if i.val < 231 then [179, 216, 37, 107, 101, 201, 231, 129] else [178, 212, 36, 106, 227, 200, 230, 128]))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then [81, 6, 195, 12, 183, 74, 233, 23] else [80, 207, 194, 13, 165, 75, 232, 22]) else (if i.val < 235 then [103, 4, 22, 77, 181, 72, 235, 194] else [102, 205, 23, 76, 167, 73, 234, 195])) else (if i.val < 238 then (if i.val < 237 then [220, 227, 198, 112, 212, 66, 237, 170] else [221, 58, 199, 113, 151, 67, 236, 171]) else (if i.val < 239 then [50, 225, 171, 145, 214, 64, 239, 199] else [51, 56, 170, 144, 149, 65, 238, 198])))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then [49, 226, 146, 168, 95, 250, 241, 114] else [48, 59, 147, 169, 217, 251, 240, 115]) else (if i.val < 243 then [223, 224, 115, 197, 93, 248, 243, 147] else [222, 57, 114, 196, 219, 249, 242, 146])) else (if i.val < 246 then (if i.val < 245 then [109, 127, 61, 3, 89, 99, 245, 40] else [108, 122, 60, 2, 186, 98, 244, 41]) else (if i.val < 247 then [158, 125, 41, 175, 91, 97, 247, 60] else [159, 120, 40, 174, 184, 96, 246, 61]))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then [4, 103, 144, 170, 218, 242, 249, 112] else [5, 82, 145, 171, 92, 243, 248, 113]) else (if i.val < 251 then [206, 101, 113, 199, 216, 240, 251, 145] else [207, 80, 112, 198, 94, 241, 250, 144])) else (if i.val < 254 then (if i.val < 253 then [101, 206, 79, 20, 179, 30, 253, 15] else [100, 7, 78, 21, 17, 31, 252, 14]) else (if i.val < 255 then [83, 204, 14, 193, 177, 28, 255, 78] else [82, 5, 15, 192, 19, 29, 254, 79])))))))) : List Nat)[a.val]!
def key (i : Fin 256) : ℕ := (#[4239483, 6039666, 3824539862, 3826338194, 158542836719, 158543030812, 165556599904, 165556793125, 431285689831, 431285729367, 432009935325, 432009976869, 457434636652, 457436196311, 458158883605, 458160443602, 479405542164, 479405882606, 483225840570, 483226180734, 553314791194, 553315267815, 554039038428, 554039514398, 579464433579, 579464820049, 580188681081, 580189065543, 1056330570970, 1056333444907, 1063344333353, 1063347207220, 1093728872260, 1093730078667, 1094453117969, 1094454327588, 1465361450133, 1465363685497, 1472349800933, 1472352035980, 1908892401924, 1908895252278, 1912712700174, 1912715551179, 2912280702614, 2912281242091, 2919269054080, 2919269593523, 2930351732746, 2930352727209, 2937365496001, 2937366490545, 3098496137724, 3098497130716, 3099220384978, 3099221377913, 3235424753868, 3235425328545, 3242438516336, 3242439091409, 3259931569710, 3259932971232, 3263751867960, 3263753270133, 3348738569897, 3348739123317, 3355752332601, 3355752885951, 3635741600638, 3635741829924, 3642729951355, 3642730181569, 3871719887571, 3871722830839, 3878733649803, 3878736594094, 3926552967263, 3926553813406, 3927277214554, 3927278060359, 4603896186453, 4603898875764, 4610909949317, 4610912638232, 4646839332047, 4646841294867, 4653827681815, 4653829646398, 5068398692689, 5068399778882, 5069122940224, 5069124026787, 5378013219464, 5378013295034, 5381833517837, 5381833594416, 6381400435902, 6381400607374, 6388388785354, 6388388957043, 7061916083691, 7061918123103, 7068929846118, 7068931886037, 7226888150275, 7226889732477, 7233876499830, 7233878082914, 7627841870810, 7627842849029, 7634830221573, 7634831199429, 7770475834725, 7770477524027, 7771200081711, 7771201772806, 8014533350818, 8014533427986, 8015257598015, 8015257675240, 8063659415045, 8063662707333, 8070647764813, 8070651058864, 8203122885064, 8203123003510, 8210111236812, 8210111353244, 8255421560797, 8255422385679, 8262409911280, 8262410736479, 9099904619422, 9099906841458, 9103724918170, 9103727138732, 9188072779004, 9188074450769, 9195061129767, 9195062801169, 9222938242107, 9222940477495, 9229926592544, 9229928827050, 9391721731841, 9391723956855, 9392445980620, 9392448203841, 9527007725236, 9527010090273, 9530828023144, 9530830389028, 9692617883934, 9692619240760, 9696438181208, 9696439539508, 10024846381320, 10024846804420, 10031834732965, 10031835155137, 10085859292636, 10085862226204, 10092847642370, 10092850577952, 10363779118892, 10363782036579, 10367599415169, 10367602334334, 11919473073693, 11919473910882, 11920197322687, 11920198156449, 12159354323175, 12159357113256, 12163174623554, 12163177411784, 12368546565368, 12368549439522, 12372366863496, 12372369737928, 12638754597531, 12638755738220, 12642574895286, 12642576034497, 12686515489525, 12686515923332, 12687239737060, 12687240171237, 13200780411682, 13200782002935, 13201504657391, 13201506251856, 13279226110341, 13279229574790, 13279950356924, 13279953822024, 14115999936534, 14116002062865, 14116724182101, 14116726311859, 14216420005025, 14216420554732, 14220240303308, 14220240852633, 14296509418161, 14296509668788, 14303523181497, 14303523432043, 14356888296223, 14356888592294, 14363876647655, 14363876943760, 14416895744392, 14416895841513, 14420716042300, 14420716140268, 14948594958698, 14948595858620, 14952415258080, 14952416156993, 15080986457836, 15080986665053, 15088000220149, 15088000428238, 15325042590687, 15325045107687, 15332056353621, 15332058870114, 15654622062748, 15654625242137, 15658442360649, 15658445540420, 15708563944119, 15708566708341, 15715577706351, 15715580471596, 16048502094359, 16048502444037, 16055515857063, 16055516206671, 16092083472470, 16092084835134, 16099097235570, 16099098598275, 16152458930932, 16152461130276, 16159447280601, 16159449479728, 16257697412738, 16257698721894, 16264711175838, 16264712485035, 17382109053172, 17382109309333, 17389122815555, 17389123071646] : Array ℕ)[i.val]!
def gen (a : Fin 8) : He := wordGenerator (spanWords 1) a
def genPerm (a : Fin 8) : Equiv.Perm (Fin 2058) := wordPerm (spanWords 1) a
theorem genPerm_eq (a : Fin 8) : genPerm a = representation (gen a) :=
  wordPerm_eq _ _
def target (a : Fin 6) : He := wordGenerator (generatorWords 21) a
def targetPerm (a : Fin 6) : Equiv.Perm (Fin 2058) := wordPerm (generatorWords 21) a
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

def counts (i : Fin 256) : ℕ := (#[256, 64, 64, 64, 64, 64, 128, 64, 128, 64, 64, 64, 64, 64, 64, 64, 128, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 128, 64, 64, 64, 64, 64, 256, 64, 64, 64, 64, 64, 64, 128, 64, 128, 64, 64, 128, 64, 64, 64, 64, 64, 64, 64, 64, 64, 256, 64, 64, 64, 64, 64, 128, 64, 64, 64, 64, 64, 128, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 128, 64, 64, 64, 64, 128, 128, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 128, 64, 64, 64, 64, 64, 64, 64, 64, 128, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 64, 128, 64, 64, 64, 64, 128, 64, 64, 64, 64, 64, 64, 64, 64, 64, 256, 64, 64, 64, 64, 128, 64, 64, 64, 128, 128, 64, 64, 64, 128, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 128, 64, 64, 64, 64, 128, 64, 128, 64, 64, 64, 64, 128, 64, 64, 128, 64, 64, 64, 64, 128, 64, 64, 64, 64, 64, 64, 64, 64, 128, 64, 128, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 128, 64, 64, 64, 64, 128, 64, 64, 64] : Array ℕ)[i.val]!

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
  (#[[], [], [], [], [], [], [2, 3, 4, 5], [], [0, 1, 2, 4, 5], [], [], [], [1, 2, 4, 5], [], [], [], [1, 5], [], [], [], [1, 3, 4], [], [], [], [], [], [], [0, 1, 2, 4], [], [], [1, 4, 5], [], [], [], [0, 1, 3, 4, 5], [], [], [0, 1, 2], [], [], [2, 3, 5], [], [], [], [], [], [], [2], [], [4, 5], [], [], [2, 4], [], [], [], [], [], [0, 1, 2, 3, 4], [], [], [], [2, 3], [], [], [], [], [0, 2, 3, 4, 5], [0, 3], [], [], [], [], [], [1, 2, 3, 4], [], [], [], [], [1, 2, 4], [], [0, 1, 2, 3, 4, 5], [], [], [], [], [1, 3], [], [], [], [3, 4], [], [], [], [], [0, 5], [3], [], [], [], [], [0, 1, 4], [], [], [], [], [], [0, 1, 3], [], [], [0, 2], [], [], [0, 2, 4], [], [], [], [], [], [2, 4, 5], [1, 3, 5], [], [], [], [1, 2], [], [], [], [], [], [0, 1, 2, 5], [], [], [0, 1, 2, 3], [], [], [0, 2, 5], [], [], [], [0, 1, 3, 5], [], [], [], [], [], [0, 2, 4, 5], [], [], [], [], [0, 2, 3], [], [], [0, 1, 2, 3, 5], [], [], [], [], [0, 3, 5], [], [], [], [1, 2, 5], [1, 2, 3], [], [], [], [0, 3, 4, 5], [], [], [], [], [], [5], [], [], [], [], [1], [], [], [], [1, 2, 3, 5], [3, 4, 5], [], [], [], [0, 1, 3, 4], [], [], [], [], [], [], [1, 3, 4, 5], [], [], [], [0, 3, 4], [], [0, 1, 5], [], [], [], [], [4], [], [2, 5], [], [], [], [], [0, 2, 3, 5], [], [], [0], [], [], [], [], [2, 3, 4], [], [], [], [], [0, 1, 4, 5], [], [], [], [0, 1], [], [1, 2, 3, 4, 5], [], [], [], [], [0, 2, 3, 4], [], [], [0, 4, 5], [], [], [], [], [], [], [3, 5], [], [], [0, 4], [], [1, 4], [], [], []] : Array (List (Fin 6)))[i.val]!
def lowerWord (a : Fin 6) : List (Fin 256) :=
  (#[[216], [179], [47], [96], [206], [174]] : Array (List (Fin 256)))[a.val]!

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


end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.E64Containment.CentralizerCertificates.SpanCertificates.RowOne
