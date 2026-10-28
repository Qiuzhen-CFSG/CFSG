module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment.CentralizerCertificates.SpanIdentities.LiteralBridge
import Mathlib.Tactic.FinCases
public import Mathlib.Order.Fin.Basic

/-!
# The centralizer-index span of literal Held core candidate 5

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

namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.E64Containment.CentralizerCertificates.SpanCertificates.RowFive
open Subgroup

-- Serial elaboration prevents independent kernel reductions retaining memory together.
set_option Elab.async false

def code (i : Fin 128) : List (Fin 7) :=
  (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then [] else [0, 6]) else (if i.val < 3 then [0] else [6])) else (if i.val < 6 then (if i.val < 5 then [6, 0] else [4, 5]) else (if i.val < 7 then [0, 6, 0] else [0, 4, 5]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then [1, 2, 3, 4] else [0, 4, 6, 1]) else (if i.val < 11 then [0, 1, 2, 3, 4] else [4, 6, 1])) else (if i.val < 14 then (if i.val < 13 then [0, 5, 6, 1] else [1, 2, 3, 5]) else (if i.val < 15 then [5, 6, 1] else [0, 1, 2, 3, 5])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then [1, 2, 3] else [0, 6, 1]) else (if i.val < 19 then [6, 1] else [0, 1, 2, 3])) else (if i.val < 22 then (if i.val < 21 then [6, 0, 1] else [6, 1, 6]) else (if i.val < 23 then [0, 6, 1, 6] else [0, 6, 0, 1]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then [0, 1, 5, 6] else [1, 5]) else (if i.val < 27 then [0, 1, 5] else [1, 5, 6])) else (if i.val < 30 then (if i.val < 29 then [1, 4] else [0, 1, 4, 6]) else (if i.val < 31 then [1, 4, 6] else [0, 1, 4]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then [2, 3, 5] else [0, 2, 6, 3]) else (if i.val < 35 then [0, 2, 3, 5] else [2, 6, 3])) else (if i.val < 38 then (if i.val < 37 then [2, 6, 0, 3] else [2, 3, 4]) else (if i.val < 39 then [1, 4, 6, 1] else [0, 2, 3, 4]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then [2] else [0, 2, 6]) else (if i.val < 43 then [2, 6] else [0, 2])) else (if i.val < 46 then (if i.val < 45 then [2, 6, 0] else [2, 4, 5]) else (if i.val < 47 then [0, 2, 4, 5] else [4, 6, 2])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then [1, 6, 0, 1] else [1, 6, 1, 6]) else (if i.val < 51 then [0, 1, 6, 1, 6] else [2, 4, 6, 3])) else (if i.val < 54 then (if i.val < 53 then [2, 3] else [0, 1, 6, 1]) else (if i.val < 55 then [1, 6, 1] else [0, 2, 3]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then [3, 6, 0] else [3, 4, 5]) else (if i.val < 59 then [0, 3, 4, 5] else [4, 6, 3])) else (if i.val < 62 then (if i.val < 61 then [3] else [0, 3, 6]) else (if i.val < 63 then [3, 6] else [0, 3])))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then [2, 4] else [6, 0, 2]) else (if i.val < 67 then [0, 2, 4] else [2, 4, 6])) else (if i.val < 70 then (if i.val < 69 then [0, 6, 2] else [2, 5]) else (if i.val < 71 then [6, 2] else [0, 2, 5]))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then [1, 2, 6, 0] else [1, 2, 4, 5]) else (if i.val < 75 then [1, 4, 6, 2] else [0, 1, 2, 4, 5])) else (if i.val < 78 then (if i.val < 77 then [1, 2] else [0, 1, 2, 6]) else (if i.val < 79 then [0, 1, 2] else [1, 2, 6])))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then [0, 1, 6, 2] else [1, 2, 5]) else (if i.val < 83 then [0, 1, 2, 5] else [1, 6, 2])) else (if i.val < 86 then (if i.val < 85 then [1, 2, 4] else [1, 6, 0, 2]) else (if i.val < 87 then [1, 2, 4, 6] else [0, 1, 2, 4]))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then [0, 4, 6] else [4]) else (if i.val < 91 then [4, 6] else [0, 4])) else (if i.val < 94 then (if i.val < 93 then [5] else [0, 5, 6]) else (if i.val < 95 then [0, 5] else [5, 6]))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then [3, 5] else [0, 6, 3]) else (if i.val < 99 then [6, 3] else [0, 3, 5])) else (if i.val < 102 then (if i.val < 101 then [6, 0, 3] else [3, 4]) else (if i.val < 103 then [0, 3, 4] else [3, 4, 6]))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then [1, 4, 5] else [1, 6, 0]) else (if i.val < 107 then [0, 1, 6, 0] else [0, 1, 4, 5])) else (if i.val < 110 then (if i.val < 109 then [0, 1, 6] else [1]) else (if i.val < 111 then [0, 1] else [1, 6])))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then [1, 6, 0, 3] else [1, 3, 4]) else (if i.val < 115 then [0, 1, 3, 4] else [1, 3, 4, 6])) else (if i.val < 118 then (if i.val < 117 then [1, 3, 5] else [0, 1, 6, 3]) else (if i.val < 119 then [1, 6, 3] else [0, 1, 3, 5]))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then [0, 1, 3, 6] else [1, 3]) else (if i.val < 123 then [1, 3, 6] else [0, 1, 3])) else (if i.val < 126 then (if i.val < 125 then [1, 3, 4, 5] else [1, 3, 6, 0]) else (if i.val < 127 then [0, 1, 3, 4, 5] else [1, 4, 6, 3])))))))
def step (i : Fin 128) (a : Fin 7) : Fin 128 :=
  Fin.ofNat 128 ((if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then [2, 109, 40, 60, 89, 92, 3] else [6, 17, 68, 97, 88, 93, 7]) else (if i.val < 3 then [0, 110, 43, 63, 91, 94, 1] else [4, 18, 70, 98, 90, 95, 5])) else (if i.val < 6 then (if i.val < 5 then [3, 20, 65, 100, 93, 88, 2] else [7, 104, 45, 57, 92, 89, 6]) else (if i.val < 7 then [1, 23, 67, 103, 95, 90, 0] else [5, 107, 46, 58, 94, 91, 4]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then [10, 37, 113, 84, 16, 21, 11] else [14, 88, 125, 72, 17, 20, 15]) else (if i.val < 11 then [8, 39, 114, 87, 19, 22, 9] else [12, 90, 127, 74, 18, 23, 13])) else (if i.val < 14 then (if i.val < 13 then [11, 93, 120, 77, 20, 17, 10] else [15, 32, 116, 81, 21, 16, 14]) else (if i.val < 15 then [9, 95, 122, 79, 23, 18, 8] else [13, 34, 119, 82, 22, 19, 12])))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then [19, 52, 121, 76, 8, 13, 18] else [23, 1, 117, 80, 9, 12, 22]) else (if i.val < 19 then [20, 3, 118, 83, 11, 14, 21] else [16, 55, 123, 78, 10, 15, 17])) else (if i.val < 22 then (if i.val < 21 then [18, 4, 112, 85, 12, 9, 19] else [22, 49, 124, 73, 13, 8, 23]) else (if i.val < 23 then [21, 50, 126, 75, 15, 10, 20] else [17, 6, 115, 86, 14, 11, 16]))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then [30, 33, 77, 120, 105, 108, 31] else [26, 92, 81, 116, 104, 109, 27]) else (if i.val < 27 then [25, 94, 82, 119, 107, 110, 24] else [29, 35, 79, 122, 106, 111, 28])) else (if i.val < 30 then (if i.val < 29 then [31, 89, 84, 113, 109, 104, 30] else [27, 36, 72, 125, 108, 105, 26]) else (if i.val < 31 then [24, 38, 74, 127, 111, 106, 25] else [28, 91, 87, 114, 110, 107, 29]))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then [34, 13, 96, 69, 49, 52, 35] else [38, 24, 61, 41, 48, 53, 39]) else (if i.val < 35 then [32, 15, 99, 71, 50, 55, 33] else [36, 27, 62, 42, 51, 54, 37])) else (if i.val < 38 then (if i.val < 37 then [35, 29, 56, 44, 53, 48, 34] else [39, 8, 101, 64, 52, 49, 38]) else (if i.val < 39 then [33, 30, 59, 47, 54, 51, 32] else [37, 10, 102, 66, 55, 50, 36]))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then [43, 76, 0, 52, 64, 69, 42] else [47, 120, 93, 33, 65, 68, 46]) else (if i.val < 43 then [44, 122, 95, 35, 67, 70, 45] else [40, 78, 2, 55, 66, 71, 41])) else (if i.val < 46 then (if i.val < 45 then [42, 125, 88, 36, 68, 65, 43] else [46, 73, 5, 49, 69, 64, 47]) else (if i.val < 47 then [45, 75, 7, 50, 71, 66, 44] else [41, 127, 90, 38, 70, 67, 40])))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then [54, 105, 100, 65, 33, 36, 55] else [50, 21, 57, 45, 32, 37, 51]) else (if i.val < 51 then [49, 22, 58, 46, 34, 39, 48] else [53, 106, 103, 67, 35, 38, 52])) else (if i.val < 54 then (if i.val < 53 then [55, 16, 60, 40, 37, 32, 54] else [51, 108, 97, 68, 36, 33, 50]) else (if i.val < 55 then [48, 111, 98, 70, 38, 35, 49] else [52, 19, 63, 43, 39, 34, 53]))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then [62, 72, 36, 88, 97, 100, 63] else [58, 124, 49, 5, 96, 101, 59]) else (if i.val < 59 then [57, 126, 50, 7, 99, 102, 56] else [61, 74, 38, 90, 98, 103, 60])) else (if i.val < 62 then (if i.val < 61 then [63, 121, 52, 0, 101, 96, 62] else [59, 77, 33, 93, 100, 97, 58]) else (if i.val < 63 then [56, 79, 35, 95, 103, 98, 57] else [60, 123, 55, 2, 102, 99, 61])))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then [66, 84, 89, 37, 40, 45, 67] else [70, 112, 4, 48, 41, 44, 71]) else (if i.val < 67 then [64, 87, 91, 39, 43, 46, 65] else [68, 115, 6, 51, 42, 47, 69])) else (if i.val < 70 then (if i.val < 69 then [67, 117, 1, 53, 44, 41, 66] else [71, 81, 92, 32, 45, 40, 70]) else (if i.val < 71 then [65, 118, 3, 54, 47, 42, 64] else [69, 82, 94, 34, 46, 43, 68]))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then [79, 56, 29, 9, 80, 85, 78] else [75, 45, 104, 21, 81, 84, 74]) else (if i.val < 75 then [77, 59, 30, 11, 83, 86, 76] else [73, 46, 107, 22, 82, 87, 72])) else (if i.val < 78 then (if i.val < 77 then [78, 40, 109, 16, 84, 81, 79] else [74, 61, 24, 12, 85, 80, 75]) else (if i.val < 79 then [76, 43, 110, 19, 87, 82, 77] else [72, 62, 27, 14, 86, 83, 73])))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then [86, 97, 108, 17, 72, 77, 87] else [82, 69, 25, 13, 73, 76, 83]) else (if i.val < 83 then [81, 71, 26, 15, 75, 78, 80] else [85, 98, 111, 18, 74, 79, 84])) else (if i.val < 86 then (if i.val < 85 then [87, 64, 28, 8, 76, 73, 86] else [83, 100, 105, 20, 77, 72, 82]) else (if i.val < 87 then [80, 103, 106, 23, 79, 74, 81] else [84, 66, 31, 10, 78, 75, 85]))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then [95, 9, 44, 56, 1, 4, 94] else [91, 28, 64, 101, 0, 5, 90]) else (if i.val < 91 then [93, 11, 47, 59, 3, 6, 92] else [89, 31, 66, 102, 2, 7, 88])) else (if i.val < 94 then (if i.val < 93 then [94, 25, 69, 96, 5, 0, 95] else [90, 12, 41, 61, 4, 1, 91]) else (if i.val < 95 then [92, 26, 71, 99, 7, 2, 93] else [88, 14, 42, 62, 6, 3, 89]))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then [99, 116, 32, 92, 57, 60, 98] else [103, 80, 53, 1, 56, 61, 102]) else (if i.val < 99 then [100, 83, 54, 3, 59, 62, 101] else [96, 119, 34, 94, 58, 63, 97])) else (if i.val < 102 then (if i.val < 101 then [98, 85, 48, 4, 61, 56, 99] else [102, 113, 37, 89, 60, 57, 103]) else (if i.val < 103 then [101, 114, 39, 91, 63, 58, 100] else [97, 86, 51, 6, 62, 59, 96]))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then [107, 5, 73, 124, 25, 28, 106] else [111, 48, 85, 112, 24, 29, 110]) else (if i.val < 107 then [108, 51, 86, 115, 27, 30, 109] else [104, 7, 75, 126, 26, 31, 105])) else (if i.val < 110 then (if i.val < 109 then [106, 53, 80, 117, 29, 24, 107] else [110, 0, 76, 121, 28, 25, 111]) else (if i.val < 111 then [109, 2, 78, 123, 31, 26, 108] else [105, 54, 83, 118, 30, 27, 104])))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then [118, 65, 20, 105, 120, 125, 119] else [114, 101, 8, 28, 121, 124, 115]) else (if i.val < 115 then [113, 102, 10, 31, 123, 126, 112] else [117, 67, 23, 106, 122, 127, 116])) else (if i.val < 118 then (if i.val < 117 then [119, 96, 13, 25, 124, 121, 118] else [115, 68, 17, 108, 125, 120, 114]) else (if i.val < 119 then [112, 70, 18, 111, 127, 122, 113] else [116, 99, 15, 26, 126, 123, 117]))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then [127, 41, 12, 24, 112, 117, 126] else [123, 60, 16, 109, 113, 116, 122]) else (if i.val < 123 then [125, 42, 14, 27, 115, 118, 124] else [121, 63, 19, 110, 114, 119, 120])) else (if i.val < 126 then (if i.val < 125 then [126, 57, 21, 104, 116, 113, 127] else [122, 44, 9, 29, 117, 112, 123]) else (if i.val < 127 then [124, 58, 22, 107, 119, 114, 125] else [120, 47, 11, 30, 118, 115, 121]))))))) : List Nat)[a.val]!
def key (i : Fin 128) : ℕ := (#[4239483, 6039666, 1508389929, 1509376337, 3824539862, 3826338194, 6772947763, 6773933810, 431285689831, 431285729367, 431562816206, 431565292469, 432009935325, 432009976869, 432066825614, 432069301368, 579464433579, 579464820049, 579743784218, 579744502949, 580188681081, 580189065543, 580247793626, 580248511848, 1093728872260, 1093730078667, 1094008617637, 1094010369576, 1094453117969, 1094454327588, 1094512626168, 1094514377335, 1908892401924, 1908895252278, 1910395820010, 1910396264171, 1912712700174, 1912715551179, 1915660377777, 1915660823075, 3098496137724, 3098497130716, 3098777471156, 3098777501643, 3099220384978, 3099221377913, 3099281480609, 3099281508844, 3259931569710, 3259932971232, 3261434779571, 3261435428208, 3263751867960, 3263753270133, 3266699338475, 3266699985975, 5068398692689, 5068399778882, 5068676409629, 5068679773280, 5069122940224, 5069124026787, 5069180417724, 5069183781224, 8014533350818, 8014533427986, 8014812252716, 8014813797891, 8015257598015, 8015257675240, 8015316262169, 8015317805092, 9099904619422, 9099906841458, 9101409147364, 9101410844102, 9103724918170, 9103727138732, 9106673705008, 9106675400510, 9692617883934, 9692619240760, 9694121758036, 9694125337844, 9696438181208, 9696439539508, 9699386315680, 9699389894252, 12159354323175, 12159357113256, 12160857790365, 12160858167605, 12163174623554, 12163177411784, 12166122348199, 12166122725078, 12686515489525, 12686515923332, 12686791988129, 12686793013892, 12687239737060, 12687240171237, 12687295996224, 12687297021836, 13200780411682, 13200782002935, 13201058222539, 13201061149596, 13201504657391, 13201506251856, 13201562231070, 13201565157355, 14216420005025, 14216420554732, 14217922210538, 14217923595204, 14220240303308, 14220240852633, 14223186768703, 14223188154131, 15654622062748, 15654625242137, 15656126632682, 15656127657198, 15658442360649, 15658445540420, 15661391190847, 15661392216125] : Array ℕ)[i.val]!
def gen (a : Fin 7) : He := wordGenerator (spanWords 5) a
def genPerm (a : Fin 7) : Equiv.Perm (Fin 2058) := wordPerm (spanWords 5) a
theorem genPerm_eq (a : Fin 7) : genPerm a = representation (gen a) :=
  wordPerm_eq _ _
def target (a : Fin 6) : He := wordGenerator (generatorWords 20) a
def targetPerm (a : Fin 6) : Equiv.Perm (Fin 2058) := wordPerm (generatorWords 20) a
theorem targetPerm_eq (a : Fin 6) : targetPerm a = representation (target a) :=
  wordPerm_eq _ _
def elem (i : Fin 128) : He := eval gen (code i)
def perm (i : Fin 128) : Equiv.Perm (Fin 2058) := ((code i).map genPerm).prod
theorem perm_eq (i : Fin 128) : perm i = representation (elem i) :=
  eval_map representation gen genPerm genPerm_eq (code i)

set_option maxRecDepth 8192 in
private theorem step_check_0 : ∀ i : Fin 128, ∀ v : Fin 4,
    perm (step i 0) ⟨v.val, by omega⟩ =
      (perm i * genPerm 0) ⟨v.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem step_check_1 : ∀ i : Fin 128, ∀ v : Fin 4,
    perm (step i 1) ⟨v.val, by omega⟩ =
      (perm i * genPerm 1) ⟨v.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem step_check_2 : ∀ i : Fin 128, ∀ v : Fin 4,
    perm (step i 2) ⟨v.val, by omega⟩ =
      (perm i * genPerm 2) ⟨v.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem step_check_3 : ∀ i : Fin 128, ∀ v : Fin 4,
    perm (step i 3) ⟨v.val, by omega⟩ =
      (perm i * genPerm 3) ⟨v.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem step_check_4 : ∀ i : Fin 128, ∀ v : Fin 4,
    perm (step i 4) ⟨v.val, by omega⟩ =
      (perm i * genPerm 4) ⟨v.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem step_check_5 : ∀ i : Fin 128, ∀ v : Fin 4,
    perm (step i 5) ⟨v.val, by omega⟩ =
      (perm i * genPerm 5) ⟨v.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem step_check_6 : ∀ i : Fin 128, ∀ v : Fin 4,
    perm (step i 6) ⟨v.val, by omega⟩ =
      (perm i * genPerm 6) ⟨v.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem step_eq (i : Fin 128) (a : Fin 7) :
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

set_option maxRecDepth 8192 in
private theorem key_check : ∀ i : Fin 128,
    (((perm i 0).val * 2058 + (perm i 1).val) * 2058 + (perm i 2).val) * 2058 +
      (perm i 3).val = key i := by decide +kernel

set_option maxRecDepth 8192 in
private theorem increasing_check : ∀ i : Fin 127, key i.castSucc < key i.succ := by
  decide +kernel

private theorem elem_injective : Function.Injective elem := by
  intro i k h
  apply (Fin.strictMono_iff_lt_succ.mpr increasing_check).injective
  rw [← key_check, ← key_check, perm_eq, perm_eq, h]

set_option maxRecDepth 8192 in
def enumeration : Enumeration gen 128 where
  code := code
  root := 0
  step := step
  root_eq := rfl
  step_eq := by exact step_eq
  injective := by exact elem_injective

def counts (i : Fin 128) : ℕ := (#[128, 16, 64, 16, 16, 128, 16, 64, 64, 16, 64, 16, 16, 64, 16, 64, 64, 16, 16, 64, 16, 64, 64, 16, 16, 64, 64, 16, 64, 16, 16, 64, 128, 16, 64, 16, 16, 128, 16, 64, 64, 16, 16, 64, 16, 64, 64, 16, 16, 128, 64, 16, 128, 16, 16, 64, 16, 64, 64, 16, 64, 16, 16, 64, 64, 16, 64, 16, 16, 64, 16, 64, 16, 64, 16, 64, 64, 16, 64, 16, 16, 64, 64, 16, 64, 16, 16, 64, 16, 128, 16, 64, 128, 16, 64, 16, 64, 16, 16, 64, 16, 64, 64, 16, 64, 16, 16, 64, 16, 64, 64, 16, 16, 64, 64, 16, 64, 16, 16, 64, 16, 64, 16, 64, 64, 16, 64, 16] : Array ℕ)[i.val]!

set_option maxRecDepth 8192 in
private theorem count_0 : enumeration.count (0 : Fin 128) = counts 0 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_1 : enumeration.count (1 : Fin 128) = counts 1 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_2 : enumeration.count (2 : Fin 128) = counts 2 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_3 : enumeration.count (3 : Fin 128) = counts 3 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_4 : enumeration.count (4 : Fin 128) = counts 4 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_5 : enumeration.count (5 : Fin 128) = counts 5 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_6 : enumeration.count (6 : Fin 128) = counts 6 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_7 : enumeration.count (7 : Fin 128) = counts 7 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_8 : enumeration.count (8 : Fin 128) = counts 8 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_9 : enumeration.count (9 : Fin 128) = counts 9 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_10 : enumeration.count (10 : Fin 128) = counts 10 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_11 : enumeration.count (11 : Fin 128) = counts 11 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_12 : enumeration.count (12 : Fin 128) = counts 12 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_13 : enumeration.count (13 : Fin 128) = counts 13 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_14 : enumeration.count (14 : Fin 128) = counts 14 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_15 : enumeration.count (15 : Fin 128) = counts 15 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_16 : enumeration.count (16 : Fin 128) = counts 16 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_17 : enumeration.count (17 : Fin 128) = counts 17 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_18 : enumeration.count (18 : Fin 128) = counts 18 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_19 : enumeration.count (19 : Fin 128) = counts 19 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_20 : enumeration.count (20 : Fin 128) = counts 20 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_21 : enumeration.count (21 : Fin 128) = counts 21 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_22 : enumeration.count (22 : Fin 128) = counts 22 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_23 : enumeration.count (23 : Fin 128) = counts 23 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_24 : enumeration.count (24 : Fin 128) = counts 24 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_25 : enumeration.count (25 : Fin 128) = counts 25 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_26 : enumeration.count (26 : Fin 128) = counts 26 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_27 : enumeration.count (27 : Fin 128) = counts 27 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_28 : enumeration.count (28 : Fin 128) = counts 28 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_29 : enumeration.count (29 : Fin 128) = counts 29 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_30 : enumeration.count (30 : Fin 128) = counts 30 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_31 : enumeration.count (31 : Fin 128) = counts 31 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_32 : enumeration.count (32 : Fin 128) = counts 32 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_33 : enumeration.count (33 : Fin 128) = counts 33 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_34 : enumeration.count (34 : Fin 128) = counts 34 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_35 : enumeration.count (35 : Fin 128) = counts 35 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_36 : enumeration.count (36 : Fin 128) = counts 36 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_37 : enumeration.count (37 : Fin 128) = counts 37 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_38 : enumeration.count (38 : Fin 128) = counts 38 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_39 : enumeration.count (39 : Fin 128) = counts 39 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_40 : enumeration.count (40 : Fin 128) = counts 40 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_41 : enumeration.count (41 : Fin 128) = counts 41 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_42 : enumeration.count (42 : Fin 128) = counts 42 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_43 : enumeration.count (43 : Fin 128) = counts 43 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_44 : enumeration.count (44 : Fin 128) = counts 44 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_45 : enumeration.count (45 : Fin 128) = counts 45 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_46 : enumeration.count (46 : Fin 128) = counts 46 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_47 : enumeration.count (47 : Fin 128) = counts 47 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_48 : enumeration.count (48 : Fin 128) = counts 48 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_49 : enumeration.count (49 : Fin 128) = counts 49 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_50 : enumeration.count (50 : Fin 128) = counts 50 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_51 : enumeration.count (51 : Fin 128) = counts 51 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_52 : enumeration.count (52 : Fin 128) = counts 52 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_53 : enumeration.count (53 : Fin 128) = counts 53 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_54 : enumeration.count (54 : Fin 128) = counts 54 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_55 : enumeration.count (55 : Fin 128) = counts 55 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_56 : enumeration.count (56 : Fin 128) = counts 56 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_57 : enumeration.count (57 : Fin 128) = counts 57 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_58 : enumeration.count (58 : Fin 128) = counts 58 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_59 : enumeration.count (59 : Fin 128) = counts 59 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_60 : enumeration.count (60 : Fin 128) = counts 60 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_61 : enumeration.count (61 : Fin 128) = counts 61 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_62 : enumeration.count (62 : Fin 128) = counts 62 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_63 : enumeration.count (63 : Fin 128) = counts 63 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_64 : enumeration.count (64 : Fin 128) = counts 64 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_65 : enumeration.count (65 : Fin 128) = counts 65 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_66 : enumeration.count (66 : Fin 128) = counts 66 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_67 : enumeration.count (67 : Fin 128) = counts 67 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_68 : enumeration.count (68 : Fin 128) = counts 68 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_69 : enumeration.count (69 : Fin 128) = counts 69 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_70 : enumeration.count (70 : Fin 128) = counts 70 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_71 : enumeration.count (71 : Fin 128) = counts 71 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_72 : enumeration.count (72 : Fin 128) = counts 72 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_73 : enumeration.count (73 : Fin 128) = counts 73 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_74 : enumeration.count (74 : Fin 128) = counts 74 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_75 : enumeration.count (75 : Fin 128) = counts 75 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_76 : enumeration.count (76 : Fin 128) = counts 76 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_77 : enumeration.count (77 : Fin 128) = counts 77 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_78 : enumeration.count (78 : Fin 128) = counts 78 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_79 : enumeration.count (79 : Fin 128) = counts 79 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_80 : enumeration.count (80 : Fin 128) = counts 80 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_81 : enumeration.count (81 : Fin 128) = counts 81 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_82 : enumeration.count (82 : Fin 128) = counts 82 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_83 : enumeration.count (83 : Fin 128) = counts 83 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_84 : enumeration.count (84 : Fin 128) = counts 84 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_85 : enumeration.count (85 : Fin 128) = counts 85 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_86 : enumeration.count (86 : Fin 128) = counts 86 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_87 : enumeration.count (87 : Fin 128) = counts 87 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_88 : enumeration.count (88 : Fin 128) = counts 88 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_89 : enumeration.count (89 : Fin 128) = counts 89 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_90 : enumeration.count (90 : Fin 128) = counts 90 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_91 : enumeration.count (91 : Fin 128) = counts 91 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_92 : enumeration.count (92 : Fin 128) = counts 92 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_93 : enumeration.count (93 : Fin 128) = counts 93 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_94 : enumeration.count (94 : Fin 128) = counts 94 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_95 : enumeration.count (95 : Fin 128) = counts 95 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_96 : enumeration.count (96 : Fin 128) = counts 96 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_97 : enumeration.count (97 : Fin 128) = counts 97 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_98 : enumeration.count (98 : Fin 128) = counts 98 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_99 : enumeration.count (99 : Fin 128) = counts 99 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_100 : enumeration.count (100 : Fin 128) = counts 100 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_101 : enumeration.count (101 : Fin 128) = counts 101 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_102 : enumeration.count (102 : Fin 128) = counts 102 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_103 : enumeration.count (103 : Fin 128) = counts 103 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_104 : enumeration.count (104 : Fin 128) = counts 104 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_105 : enumeration.count (105 : Fin 128) = counts 105 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_106 : enumeration.count (106 : Fin 128) = counts 106 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_107 : enumeration.count (107 : Fin 128) = counts 107 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_108 : enumeration.count (108 : Fin 128) = counts 108 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_109 : enumeration.count (109 : Fin 128) = counts 109 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_110 : enumeration.count (110 : Fin 128) = counts 110 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_111 : enumeration.count (111 : Fin 128) = counts 111 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_112 : enumeration.count (112 : Fin 128) = counts 112 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_113 : enumeration.count (113 : Fin 128) = counts 113 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_114 : enumeration.count (114 : Fin 128) = counts 114 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_115 : enumeration.count (115 : Fin 128) = counts 115 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_116 : enumeration.count (116 : Fin 128) = counts 116 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_117 : enumeration.count (117 : Fin 128) = counts 117 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_118 : enumeration.count (118 : Fin 128) = counts 118 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_119 : enumeration.count (119 : Fin 128) = counts 119 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_120 : enumeration.count (120 : Fin 128) = counts 120 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_121 : enumeration.count (121 : Fin 128) = counts 121 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_122 : enumeration.count (122 : Fin 128) = counts 122 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_123 : enumeration.count (123 : Fin 128) = counts 123 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_124 : enumeration.count (124 : Fin 128) = counts 124 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_125 : enumeration.count (125 : Fin 128) = counts 125 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_126 : enumeration.count (126 : Fin 128) = counts 126 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem count_127 : enumeration.count (127 : Fin 128) = counts 127 := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem counts_check (i : Fin 128) : enumeration.count i = counts i := by
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

def upperWord (i : Fin 128) : List (Fin 6) :=
  (#[[], [], [0], [], [], [4, 5], [], [0, 4, 5], [1, 2, 3, 4], [], [0, 1, 2, 3, 4], [], [], [1, 2, 3, 5], [], [0, 1, 2, 3, 5], [1, 2, 3], [], [], [0, 1, 2, 3], [], [1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5], [], [], [1, 5], [0, 1, 5], [], [1, 4], [], [], [0, 1, 4], [2, 3, 5], [], [0, 2, 3, 5], [], [], [2, 3, 4], [], [0, 2, 3, 4], [2], [], [], [0, 2], [], [2, 4, 5], [0, 2, 4, 5], [], [], [2, 3, 4, 5], [0, 2, 3, 4, 5], [], [2, 3], [], [], [0, 2, 3], [], [3, 4, 5], [0, 3, 4, 5], [], [3], [], [], [0, 3], [2, 4], [], [0, 2, 4], [], [], [2, 5], [], [0, 2, 5], [], [1, 2, 4, 5], [], [0, 1, 2, 4, 5], [1, 2], [], [0, 1, 2], [], [], [1, 2, 5], [0, 1, 2, 5], [], [1, 2, 4], [], [], [0, 1, 2, 4], [], [4], [], [0, 4], [5], [], [0, 5], [], [3, 5], [], [], [0, 3, 5], [], [3, 4], [0, 3, 4], [], [1, 4, 5], [], [], [0, 1, 4, 5], [], [1], [0, 1], [], [], [1, 3, 4], [0, 1, 3, 4], [], [1, 3, 5], [], [], [0, 1, 3, 5], [], [1, 3], [], [0, 1, 3], [1, 3, 4, 5], [], [0, 1, 3, 4, 5], []] : Array (List (Fin 6)))[i.val]!
def lowerWord (a : Fin 6) : List (Fin 128) :=
  (#[[2], [109], [40], [60], [89], [92]] : Array (List (Fin 128)))[a.val]!

set_option maxRecDepth 8192 in
theorem upper_check : ∀ i : Fin 128, 128 ≤ 2 * counts i → ∀ v : Fin 4,
    perm i ⟨v.val, by omega⟩ =
      eval targetPerm (upperWord i) ⟨v.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem lower_selected : ∀ a : Fin 6, ∀ i ∈ lowerWord a, 128 ≤ 2 * counts i := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem lower_check : ∀ a : Fin 6, ∀ v : Fin 4,
    ((lowerWord a).map perm).prod ⟨v.val, by omega⟩ =
      targetPerm a ⟨v.val, by omega⟩ := by
  decide +kernel


end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.E64Containment.CentralizerCertificates.SpanCertificates.RowFive
