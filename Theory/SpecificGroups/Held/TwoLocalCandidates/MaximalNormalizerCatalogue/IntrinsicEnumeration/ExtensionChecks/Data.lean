module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration.Words

/-!
# Finite data for the Held extension checks

`members` and `target` copy the indices in `extension_discovery.json` without
changing the literal normal forms or subgroup entries. They assert no membership
or equality: the finite membership theorem and the branch checks must be proved
separately. In particular, an omitted transition defaults to the bottom node;
this default is only usable after the branch has been formally rejected.

Source: the existing ATLAS Held subgroup discovery, reproduced by
`IntrinsicEnumeration/source/verify.py`. `Source/generate_data.py` produces this
file; it is not a proof certificate.
-/

@[expose] public section
namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration.ExtensionChecks

/-- Proposed complete lists of binary words in each of the 23 literal nodes. -/
def members : Option (Fin 22) → List (Fin 1024)
  | none => [0]
  | (some 0) => [0, 512]
  | (some 1) => [0, 512, 368, 880]
  | (some 2) => [0, 512, 144, 656]
  | (some 3) => [0, 512, 480, 992]
  | (some 4) => [0, 512, 272, 96, 784, 608, 368, 880]
  | (some 5) => [0, 512, 384, 896, 240, 368, 752, 880]
  | (some 6) => [0, 512, 144, 656, 368, 480, 880, 992]
  | (some 7) => [0, 512, 48, 560, 464, 480, 976, 992]
  | (some 8) => [0, 512, 160, 320, 672, 832, 480, 992]
  | (some 9) => [0, 512, 272, 96, 162, 194, 784, 608, 674, 706, 368, 434, 466, 880, 946, 978]
  | (some 10) => [0, 2, 512, 514, 384, 386, 896, 898, 240, 368, 242, 370, 752, 880, 754, 882]
  | (some 11) => [0, 512, 258, 48, 770, 560, 306, 210, 226, 464, 480, 818, 722, 738, 976, 992]
  | (some 12) => [0, 512, 12, 144, 524, 656, 156, 368, 480, 668, 880, 992, 380, 492, 892, 1004]
  | (some 13) => [0, 512, 144, 656, 60, 172, 332, 368, 480, 572, 684, 844, 880, 992, 476, 988]
  | (some 14) => [0, 512, 144, 656, 284, 108, 396, 368, 480, 796, 620, 908, 880, 992, 252, 764]
  | (some 15) => [0, 512, 144, 272, 96, 384, 656, 784, 608, 896, 240, 368, 480, 752, 880, 992]
  | (some 16) => [0, 512, 34, 130, 160, 320, 546, 642, 672, 832, 354, 450, 480, 866, 962, 992]
  | (some 17) => [0, 512, 48, 144, 160, 320, 560, 656, 672, 832, 368, 464, 480, 880, 976, 992]
  | (some 18) => [0, 512, 12, 144, 272, 96, 384, 524, 656, 784, 608, 896, 156, 284, 108, 396, 240, 368, 480, 668, 796, 620, 908, 752, 880, 992, 252, 380, 492, 764, 892, 1004]
  | (some 19) => [0, 512, 12, 48, 144, 160, 320, 524, 560, 656, 672, 832, 60, 156, 172, 332, 368, 464, 480, 572, 668, 684, 844, 880, 976, 992, 380, 476, 492, 892, 988, 1004]
  | (some 20) => [0, 512, 3, 12, 144, 272, 96, 384, 515, 524, 656, 784, 608, 896, 15, 147, 275, 99, 387, 156, 284, 108, 396, 240, 368, 480, 527, 659, 787, 611, 899, 668, 796, 620, 908, 752, 880, 992, 159, 287, 111, 399, 243, 371, 483, 252, 380, 492, 671, 799, 623, 911, 755, 883, 995, 764, 892, 1004, 255, 383, 495, 767, 895, 1007]
  | (some _) => [0, 4, 8, 512, 12, 516, 520, 48, 144, 160, 320, 524, 52, 148, 164, 324, 56, 152, 168, 328, 560, 656, 672, 832, 60, 156, 172, 332, 564, 660, 676, 836, 568, 664, 680, 840, 368, 464, 480, 572, 668, 684, 844, 372, 468, 484, 376, 472, 488, 880, 976, 992, 380, 476, 492, 884, 980, 996, 888, 984, 1000, 892, 988, 1004]

/-- Proposed targets for the eligible extensions, with the discovery indices unchanged. -/
def transitions : Option (Fin 22) → List (Fin 1024 × Option (Fin 22))
  | none => [(0, none), (512, (some 0))]
  | (some 0) => [(0, (some 0)), (144, (some 2)), (368, (some 1)), (480, (some 3)), (512, (some 0)), (656, (some 2)), (880, (some 1)), (992, (some 3))]
  | (some 1) => [(0, (some 1)), (96, (some 4)), (144, (some 6)), (240, (some 5)), (272, (some 4)), (368, (some 1)), (384, (some 5)), (480, (some 6)), (512, (some 1)), (608, (some 4)), (656, (some 6)), (752, (some 5)), (784, (some 4)), (880, (some 1)), (896, (some 5)), (992, (some 6))]
  | (some 2) => [(0, (some 2)), (144, (some 2)), (368, (some 6)), (480, (some 6)), (512, (some 2)), (656, (some 2)), (880, (some 6)), (992, (some 6))]
  | (some 3) => [(0, (some 3)), (48, (some 7)), (144, (some 6)), (160, (some 8)), (320, (some 8)), (368, (some 6)), (464, (some 7)), (480, (some 3)), (512, (some 3)), (560, (some 7)), (656, (some 6)), (672, (some 8)), (832, (some 8)), (880, (some 6)), (976, (some 7)), (992, (some 3))]
  | (some 4) => [(0, (some 4)), (96, (some 4)), (144, (some 15)), (162, (some 9)), (194, (some 9)), (240, (some 15)), (272, (some 4)), (368, (some 4)), (384, (some 15)), (434, (some 9)), (466, (some 9)), (480, (some 15)), (512, (some 4)), (608, (some 4)), (656, (some 15)), (674, (some 9)), (706, (some 9)), (752, (some 15)), (784, (some 4)), (880, (some 4)), (896, (some 15)), (946, (some 9)), (978, (some 9)), (992, (some 15))]
  | (some 5) => [(0, (some 5)), (2, (some 10)), (96, (some 15)), (144, (some 15)), (240, (some 5)), (242, (some 10)), (272, (some 15)), (368, (some 5)), (370, (some 10)), (384, (some 5)), (386, (some 10)), (480, (some 15)), (512, (some 5)), (514, (some 10)), (608, (some 15)), (656, (some 15)), (752, (some 5)), (754, (some 10)), (784, (some 15)), (880, (some 5)), (882, (some 10)), (896, (some 5)), (898, (some 10)), (992, (some 15))]
  | (some 6) => [(0, (some 6)), (12, (some 12)), (48, (some 17)), (60, (some 13)), (96, (some 15)), (108, (some 14)), (144, (some 6)), (156, (some 12)), (160, (some 17)), (172, (some 13)), (240, (some 15)), (252, (some 14)), (272, (some 15)), (284, (some 14)), (320, (some 17)), (332, (some 13)), (368, (some 6)), (380, (some 12)), (384, (some 15)), (396, (some 14)), (464, (some 17)), (476, (some 13)), (480, (some 6)), (492, (some 12)), (512, (some 6)), (524, (some 12)), (560, (some 17)), (572, (some 13)), (608, (some 15)), (620, (some 14)), (656, (some 6)), (668, (some 12)), (672, (some 17)), (684, (some 13)), (752, (some 15)), (764, (some 14)), (784, (some 15)), (796, (some 14)), (832, (some 17)), (844, (some 13)), (880, (some 6)), (892, (some 12)), (896, (some 15)), (908, (some 14)), (976, (some 17)), (988, (some 13)), (992, (some 6)), (1004, (some 12))]
  | (some 7) => [(0, (some 7)), (48, (some 7)), (144, (some 17)), (160, (some 17)), (210, (some 11)), (226, (some 11)), (258, (some 11)), (306, (some 11)), (320, (some 17)), (368, (some 17)), (464, (some 7)), (480, (some 7)), (512, (some 7)), (560, (some 7)), (656, (some 17)), (672, (some 17)), (722, (some 11)), (738, (some 11)), (770, (some 11)), (818, (some 11)), (832, (some 17)), (880, (some 17)), (976, (some 7)), (992, (some 7))]
  | (some 8) => [(0, (some 8)), (34, (some 16)), (48, (some 17)), (130, (some 16)), (144, (some 17)), (160, (some 8)), (320, (some 8)), (354, (some 16)), (368, (some 17)), (450, (some 16)), (464, (some 17)), (480, (some 8)), (512, (some 8)), (546, (some 16)), (560, (some 17)), (642, (some 16)), (656, (some 17)), (672, (some 8)), (832, (some 8)), (866, (some 16)), (880, (some 17)), (962, (some 16)), (976, (some 17)), (992, (some 8))]
  | (some 9) => [(0, (some 9)), (96, (some 9)), (162, (some 9)), (194, (some 9)), (272, (some 9)), (368, (some 9)), (434, (some 9)), (466, (some 9)), (512, (some 9)), (608, (some 9)), (674, (some 9)), (706, (some 9)), (784, (some 9)), (880, (some 9)), (946, (some 9)), (978, (some 9))]
  | (some 10) => [(0, (some 10)), (2, (some 10)), (240, (some 10)), (242, (some 10)), (368, (some 10)), (370, (some 10)), (384, (some 10)), (386, (some 10)), (512, (some 10)), (514, (some 10)), (752, (some 10)), (754, (some 10)), (880, (some 10)), (882, (some 10)), (896, (some 10)), (898, (some 10))]
  | (some 11) => [(0, (some 11)), (48, (some 11)), (210, (some 11)), (226, (some 11)), (258, (some 11)), (306, (some 11)), (464, (some 11)), (480, (some 11)), (512, (some 11)), (560, (some 11)), (722, (some 11)), (738, (some 11)), (770, (some 11)), (818, (some 11)), (976, (some 11)), (992, (some 11))]
  | (some 12) => [(0, (some 12)), (12, (some 12)), (48, (some 19)), (60, (some 19)), (96, (some 18)), (108, (some 18)), (144, (some 12)), (156, (some 12)), (160, (some 19)), (172, (some 19)), (240, (some 18)), (252, (some 18)), (272, (some 18)), (284, (some 18)), (320, (some 19)), (332, (some 19)), (368, (some 12)), (380, (some 12)), (384, (some 18)), (396, (some 18)), (464, (some 19)), (476, (some 19)), (480, (some 12)), (492, (some 12)), (512, (some 12)), (524, (some 12)), (560, (some 19)), (572, (some 19)), (608, (some 18)), (620, (some 18)), (656, (some 12)), (668, (some 12)), (672, (some 19)), (684, (some 19)), (752, (some 18)), (764, (some 18)), (784, (some 18)), (796, (some 18)), (832, (some 19)), (844, (some 19)), (880, (some 12)), (892, (some 12)), (896, (some 18)), (908, (some 18)), (976, (some 19)), (988, (some 19)), (992, (some 12)), (1004, (some 12))]
  | (some 13) => [(0, (some 13)), (12, (some 19)), (48, (some 19)), (60, (some 13)), (144, (some 13)), (156, (some 19)), (160, (some 19)), (172, (some 13)), (320, (some 19)), (332, (some 13)), (368, (some 13)), (380, (some 19)), (464, (some 19)), (476, (some 13)), (480, (some 13)), (492, (some 19)), (512, (some 13)), (524, (some 19)), (560, (some 19)), (572, (some 13)), (656, (some 13)), (668, (some 19)), (672, (some 19)), (684, (some 13)), (832, (some 19)), (844, (some 13)), (880, (some 13)), (892, (some 19)), (976, (some 19)), (988, (some 13)), (992, (some 13)), (1004, (some 19))]
  | (some 14) => [(0, (some 14)), (12, (some 18)), (96, (some 18)), (108, (some 14)), (144, (some 14)), (156, (some 18)), (240, (some 18)), (252, (some 14)), (272, (some 18)), (284, (some 14)), (368, (some 14)), (380, (some 18)), (384, (some 18)), (396, (some 14)), (480, (some 14)), (492, (some 18)), (512, (some 14)), (524, (some 18)), (608, (some 18)), (620, (some 14)), (656, (some 14)), (668, (some 18)), (752, (some 18)), (764, (some 14)), (784, (some 18)), (796, (some 14)), (880, (some 14)), (892, (some 18)), (896, (some 18)), (908, (some 14)), (992, (some 14)), (1004, (some 18))]
  | (some 15) => [(0, (some 15)), (12, (some 18)), (96, (some 15)), (108, (some 18)), (144, (some 15)), (156, (some 18)), (240, (some 15)), (252, (some 18)), (272, (some 15)), (284, (some 18)), (368, (some 15)), (380, (some 18)), (384, (some 15)), (396, (some 18)), (480, (some 15)), (492, (some 18)), (512, (some 15)), (524, (some 18)), (608, (some 15)), (620, (some 18)), (656, (some 15)), (668, (some 18)), (752, (some 15)), (764, (some 18)), (784, (some 15)), (796, (some 18)), (880, (some 15)), (892, (some 18)), (896, (some 15)), (908, (some 18)), (992, (some 15)), (1004, (some 18))]
  | (some 16) => [(0, (some 16)), (34, (some 16)), (130, (some 16)), (160, (some 16)), (320, (some 16)), (354, (some 16)), (450, (some 16)), (480, (some 16)), (512, (some 16)), (546, (some 16)), (642, (some 16)), (672, (some 16)), (832, (some 16)), (866, (some 16)), (962, (some 16)), (992, (some 16))]
  | (some 17) => [(0, (some 17)), (12, (some 19)), (48, (some 17)), (60, (some 19)), (144, (some 17)), (156, (some 19)), (160, (some 17)), (172, (some 19)), (320, (some 17)), (332, (some 19)), (368, (some 17)), (380, (some 19)), (464, (some 17)), (476, (some 19)), (480, (some 17)), (492, (some 19)), (512, (some 17)), (524, (some 19)), (560, (some 17)), (572, (some 19)), (656, (some 17)), (668, (some 19)), (672, (some 17)), (684, (some 19)), (832, (some 17)), (844, (some 19)), (880, (some 17)), (892, (some 19)), (976, (some 17)), (988, (some 19)), (992, (some 17)), (1004, (some 19))]
  | (some 18) => [(0, (some 18)), (3, (some 20)), (12, (some 18)), (15, (some 20)), (96, (some 18)), (99, (some 20)), (108, (some 18)), (111, (some 20)), (144, (some 18)), (147, (some 20)), (156, (some 18)), (159, (some 20)), (240, (some 18)), (243, (some 20)), (252, (some 18)), (255, (some 20)), (272, (some 18)), (275, (some 20)), (284, (some 18)), (287, (some 20)), (368, (some 18)), (371, (some 20)), (380, (some 18)), (383, (some 20)), (384, (some 18)), (387, (some 20)), (396, (some 18)), (399, (some 20)), (480, (some 18)), (483, (some 20)), (492, (some 18)), (495, (some 20)), (512, (some 18)), (515, (some 20)), (524, (some 18)), (527, (some 20)), (608, (some 18)), (611, (some 20)), (620, (some 18)), (623, (some 20)), (656, (some 18)), (659, (some 20)), (668, (some 18)), (671, (some 20)), (752, (some 18)), (755, (some 20)), (764, (some 18)), (767, (some 20)), (784, (some 18)), (787, (some 20)), (796, (some 18)), (799, (some 20)), (880, (some 18)), (883, (some 20)), (892, (some 18)), (895, (some 20)), (896, (some 18)), (899, (some 20)), (908, (some 18)), (911, (some 20)), (992, (some 18)), (995, (some 20)), (1004, (some 18)), (1007, (some 20))]
  | (some 19) => [(0, (some 19)), (4, (some 21)), (8, (some 21)), (12, (some 19)), (48, (some 19)), (52, (some 21)), (56, (some 21)), (60, (some 19)), (144, (some 19)), (148, (some 21)), (152, (some 21)), (156, (some 19)), (160, (some 19)), (164, (some 21)), (168, (some 21)), (172, (some 19)), (320, (some 19)), (324, (some 21)), (328, (some 21)), (332, (some 19)), (368, (some 19)), (372, (some 21)), (376, (some 21)), (380, (some 19)), (464, (some 19)), (468, (some 21)), (472, (some 21)), (476, (some 19)), (480, (some 19)), (484, (some 21)), (488, (some 21)), (492, (some 19)), (512, (some 19)), (516, (some 21)), (520, (some 21)), (524, (some 19)), (560, (some 19)), (564, (some 21)), (568, (some 21)), (572, (some 19)), (656, (some 19)), (660, (some 21)), (664, (some 21)), (668, (some 19)), (672, (some 19)), (676, (some 21)), (680, (some 21)), (684, (some 19)), (832, (some 19)), (836, (some 21)), (840, (some 21)), (844, (some 19)), (880, (some 19)), (884, (some 21)), (888, (some 21)), (892, (some 19)), (976, (some 19)), (980, (some 21)), (984, (some 21)), (988, (some 19)), (992, (some 19)), (996, (some 21)), (1000, (some 21)), (1004, (some 19))]
  | (some 20) => [(0, (some 20)), (3, (some 20)), (12, (some 20)), (15, (some 20)), (96, (some 20)), (99, (some 20)), (108, (some 20)), (111, (some 20)), (144, (some 20)), (147, (some 20)), (156, (some 20)), (159, (some 20)), (240, (some 20)), (243, (some 20)), (252, (some 20)), (255, (some 20)), (272, (some 20)), (275, (some 20)), (284, (some 20)), (287, (some 20)), (368, (some 20)), (371, (some 20)), (380, (some 20)), (383, (some 20)), (384, (some 20)), (387, (some 20)), (396, (some 20)), (399, (some 20)), (480, (some 20)), (483, (some 20)), (492, (some 20)), (495, (some 20)), (512, (some 20)), (515, (some 20)), (524, (some 20)), (527, (some 20)), (608, (some 20)), (611, (some 20)), (620, (some 20)), (623, (some 20)), (656, (some 20)), (659, (some 20)), (668, (some 20)), (671, (some 20)), (752, (some 20)), (755, (some 20)), (764, (some 20)), (767, (some 20)), (784, (some 20)), (787, (some 20)), (796, (some 20)), (799, (some 20)), (880, (some 20)), (883, (some 20)), (892, (some 20)), (895, (some 20)), (896, (some 20)), (899, (some 20)), (908, (some 20)), (911, (some 20)), (992, (some 20)), (995, (some 20)), (1004, (some 20)), (1007, (some 20))]
  | (some _) => [(0, (some 21)), (4, (some 21)), (8, (some 21)), (12, (some 21)), (48, (some 21)), (52, (some 21)), (56, (some 21)), (60, (some 21)), (144, (some 21)), (148, (some 21)), (152, (some 21)), (156, (some 21)), (160, (some 21)), (164, (some 21)), (168, (some 21)), (172, (some 21)), (320, (some 21)), (324, (some 21)), (328, (some 21)), (332, (some 21)), (368, (some 21)), (372, (some 21)), (376, (some 21)), (380, (some 21)), (464, (some 21)), (468, (some 21)), (472, (some 21)), (476, (some 21)), (480, (some 21)), (484, (some 21)), (488, (some 21)), (492, (some 21)), (512, (some 21)), (516, (some 21)), (520, (some 21)), (524, (some 21)), (560, (some 21)), (564, (some 21)), (568, (some 21)), (572, (some 21)), (656, (some 21)), (660, (some 21)), (664, (some 21)), (668, (some 21)), (672, (some 21)), (676, (some 21)), (680, (some 21)), (684, (some 21)), (832, (some 21)), (836, (some 21)), (840, (some 21)), (844, (some 21)), (880, (some 21)), (884, (some 21)), (888, (some 21)), (892, (some 21)), (976, (some 21)), (980, (some 21)), (984, (some 21)), (988, (some 21)), (992, (some 21)), (996, (some 21)), (1000, (some 21)), (1004, (some 21))]

/-- The proposed target, defaulting to bottom on omitted branches. -/
def target (i : Option (Fin 22)) (n : Fin 1024) : Option (Fin 22) :=
  ((transitions i).find? (fun row => row.1 == n)).map Prod.snd |>.getD none

/-- The original generating words of a node; bottom has no generators. -/
def rowGenerators : Option (Fin 22) → List (List ℤ)
  | none => []
  | some j => generatorWords j

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration.ExtensionChecks
