module
public import Theory.SpecificGroups.PSL3Three.CosetCover.Check
/-!
# Checked right cosets for node 31

These are untrusted matrix codes and subgroup words generated from the fixed
lists in `RepresentativeBounds`. The kernel checks determinants, word values,
and every transition by the four ambient generators. `cover` then follows from
`RightCosetTable.sound`, using the proved generation of the actual SL₃(3).

Source: the elementary coset-table argument in `SubgroupEnumeration` and
GLS III, Theorem 6.5.3. Row zero represents the identity matrix.
-/

namespace Matrix.PSL3Three.CertifiedEnumeration.Cosets31
open Theory.GroupTheory Theory.GroupTheory.SubgroupEnumeration CosetCheck
set_option maxRecDepth 100000

@[expose] public def codeBlock0 : Lean.RArray (MatrixCode) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 6643) (.leaf 828)) (.branch 3 (.leaf 829) (.leaf 830))) (.branch 6 (.branch 5 (.leaf 855) (.leaf 856)) (.branch 7 (.leaf 857) (.leaf 882)))) (.branch 12 (.branch 10 (.branch 9 (.leaf 883) (.leaf 884)) (.branch 11 (.leaf 975) (.leaf 976))) (.branch 14 (.branch 13 (.leaf 977) (.leaf 1002)) (.branch 15 (.leaf 1003) (.leaf 1004))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf 1029) (.leaf 1030)) (.branch 19 (.leaf 1031) (.leaf 1056))) (.branch 22 (.branch 21 (.leaf 1057) (.leaf 1058)) (.branch 23 (.leaf 1083) (.leaf 1084)))) (.branch 28 (.branch 26 (.branch 25 (.leaf 1085) (.leaf 1110)) (.branch 27 (.leaf 1111) (.leaf 1112))) (.branch 30 (.branch 29 (.leaf 1137) (.leaf 1138)) (.branch 31 (.leaf 1139) (.leaf 1164))))))

@[expose] public def codeBlock1 : Lean.RArray (MatrixCode) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 1165) (.leaf 1166)) (.branch 3 (.leaf 1191) (.leaf 1192))) (.branch 6 (.branch 5 (.leaf 1193) (.leaf 2304)) (.branch 7 (.leaf 2307) (.leaf 2310)))) (.branch 12 (.branch 10 (.branch 9 (.leaf 2435) (.leaf 2438)) (.branch 11 (.leaf 2459) (.leaf 2462))) (.branch 14 (.branch 13 (.leaf 2465) (.leaf 2486)) (.branch 15 (.leaf 2489) (.leaf 2492))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf 2513) (.leaf 2516)) (.branch 19 (.leaf 2519) (.leaf 2540))) (.branch 22 (.branch 21 (.leaf 2543) (.leaf 2546)) (.branch 23 (.leaf 2567) (.leaf 2570)))) (.branch 28 (.branch 26 (.branch 25 (.leaf 2573) (.leaf 2594)) (.branch 27 (.leaf 2597) (.leaf 2600))) (.branch 30 (.branch 29 (.leaf 2621) (.leaf 2624)) (.branch 31 (.leaf 2627) (.leaf 2648))))))

@[expose] public def codeBlock2 : Lean.RArray (MatrixCode) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 2651) (.leaf 2654)) (.branch 3 (.leaf 3161) (.leaf 3162))) (.branch 6 (.branch 5 (.leaf 3166) (.leaf 3188)) (.branch 7 (.leaf 3189) (.leaf 3193)))) (.branch 12 (.branch 10 (.branch 9 (.leaf 3215) (.leaf 3216)) (.branch 11 (.leaf 3220) (.leaf 3242))) (.branch 14 (.branch 13 (.leaf 3243) (.leaf 3247)) (.branch 15 (.leaf 3269) (.leaf 3270))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf 3274) (.leaf 3296)) (.branch 19 (.leaf 3297) (.leaf 3301))) (.branch 22 (.branch 21 (.leaf 3323) (.leaf 3324)) (.branch 23 (.leaf 3328) (.leaf 3350)))) (.branch 28 (.branch 26 (.branch 25 (.leaf 3351) (.leaf 3355)) (.branch 27 (.leaf 3377) (.leaf 3378))) (.branch 30 (.branch 29 (.leaf 3382) (.leaf 3890)) (.branch 31 (.leaf 3892) (.leaf 3894))))))

@[expose] public def codeBlock3 : Lean.RArray (MatrixCode) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 3917) (.leaf 3919)) (.branch 3 (.leaf 3921) (.leaf 3944))) (.branch 6 (.branch 5 (.leaf 3946) (.leaf 3948)) (.branch 7 (.leaf 3971) (.leaf 3973)))) (.branch 12 (.branch 10 (.branch 9 (.leaf 3975) (.leaf 3998)) (.branch 11 (.leaf 4000) (.leaf 4002))) (.branch 14 (.branch 13 (.leaf 4025) (.leaf 4027)) (.branch 15 (.leaf 4029) (.leaf 4052))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf 4054) (.leaf 4056)) (.branch 19 (.leaf 4079) (.leaf 4081))) (.branch 22 (.branch 21 (.leaf 4083) (.leaf 4106)) (.branch 23 (.leaf 4108) (.leaf 4110)))) (.branch 28 (.branch 26 (.branch 25 (.leaf 6837) (.leaf 6846)) (.branch 27 (.leaf 6855) (.leaf 6886))) (.branch 30 (.branch 29 (.leaf 6895) (.leaf 6904)) (.branch 31 (.leaf 6913) (.leaf 6922))))))

@[expose] public def codeBlock4 : Lean.RArray (MatrixCode) := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf 6931) (.branch 2 (.leaf 6940) (.leaf 6949))) (.branch 5 (.branch 4 (.leaf 6958) (.leaf 7615)) (.branch 6 (.leaf 7625) (.leaf 7632)))) (.branch 10 (.branch 8 (.leaf 7642) (.branch 9 (.leaf 7652) (.leaf 7659))) (.branch 12 (.branch 11 (.leaf 7669) (.leaf 7679)) (.branch 13 (.leaf 7686) (.leaf 8344))))) (.branch 21 (.branch 17 (.branch 15 (.leaf 8352) (.branch 16 (.leaf 8363) (.leaf 8371))) (.branch 19 (.branch 18 (.leaf 8379) (.leaf 8390)) (.branch 20 (.leaf 8398) (.leaf 8406)))) (.branch 24 (.branch 22 (.leaf 8417) (.branch 23 (.leaf 9105) (.leaf 9108))) (.branch 26 (.branch 25 (.leaf 9120) (.leaf 11373)) (.branch 27 (.leaf 11379) (.leaf 11385))))))

@[expose] public def nextBlock0 : Lean.RArray (Fin 4 → Fin 156) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![1, 41, 10, 40]) (.leaf ![10, 37, 0, 7])) (.branch 3 (.leaf ![12, 39, 40, 9]) (.leaf ![11, 38, 41, 8]))) (.branch 6 (.branch 5 (.leaf ![120, 4, 48, 4]) (.leaf ![121, 5, 49, 5])) (.branch 7 (.leaf ![122, 6, 50, 6]) (.leaf ![16, 1, 57, 37])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![17, 3, 58, 38]) (.leaf ![18, 2, 59, 39])) (.branch 11 (.leaf ![0, 67, 1, 116]) (.leaf ![41, 68, 3, 114]))) (.branch 14 (.branch 13 (.leaf ![40, 66, 2, 115]) (.leaf ![123, 79, 37, 110])) (.branch 15 (.leaf ![124, 80, 38, 108]) (.leaf ![125, 78, 39, 109]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![57, 91, 7, 95]) (.leaf ![58, 92, 8, 93])) (.branch 19 (.leaf ![59, 90, 9, 94]) (.leaf ![66, 76, 43, 98]))) (.branch 22 (.branch 21 (.leaf ![68, 77, 44, 96]) (.leaf ![67, 75, 42, 97])) (.branch 23 (.leaf ![126, 88, 51, 119]) (.leaf ![127, 89, 52, 117])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![128, 87, 53, 118]) (.leaf ![90, 73, 62, 104])) (.branch 27 (.leaf ![91, 74, 60, 102]) (.leaf ![92, 72, 61, 103]))) (.branch 30 (.branch 29 (.leaf ![93, 85, 64, 107]) (.leaf ![95, 86, 63, 105])) (.branch 31 (.leaf ![94, 84, 65, 106]) (.leaf ![129, 70, 54, 101]))))))

@[expose] public def nextBlock1 : Lean.RArray (Fin 4 → Fin 156) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![130, 71, 56, 99]) (.leaf ![131, 69, 55, 100])) (.branch 3 (.leaf ![114, 82, 47, 113]) (.leaf ![115, 83, 46, 111]))) (.branch 6 (.branch 5 (.leaf ![116, 81, 45, 112]) (.leaf ![13, 7, 123, 1])) (.branch 7 (.leaf ![14, 8, 124, 3]) (.leaf ![15, 9, 125, 2])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![2, 0, 12, 41]) (.leaf ![3, 40, 11, 0])) (.branch 11 (.leaf ![21, 53, 67, 61]) (.leaf ![19, 51, 66, 62]))) (.branch 14 (.branch 13 (.leaf ![20, 52, 68, 60]) (.leaf ![36, 65, 116, 55])) (.branch 15 (.leaf ![35, 63, 115, 56]) (.leaf ![34, 64, 114, 54]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![4, 50, 120, 49]) (.leaf ![5, 48, 121, 50])) (.branch 19 (.leaf ![6, 49, 122, 48]) (.leaf ![22, 62, 126, 43]))) (.branch 22 (.branch 21 (.leaf ![23, 60, 127, 44]) (.leaf ![24, 61, 128, 42])) (.branch 23 (.leaf ![31, 47, 129, 64]) (.leaf ![33, 45, 131, 65])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![32, 46, 130, 63]) (.leaf ![7, 59, 16, 58])) (.branch 27 (.leaf ![8, 57, 17, 59]) (.leaf ![9, 58, 18, 57]))) (.branch 30 (.branch 29 (.leaf ![26, 44, 91, 52]) (.leaf ![27, 42, 92, 53])) (.branch 31 (.leaf ![25, 43, 90, 51]) (.leaf ![29, 56, 95, 46]))))))

@[expose] public def nextBlock2 : Lean.RArray (Fin 4 → Fin 156) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![28, 54, 93, 47]) (.leaf ![30, 55, 94, 45])) (.branch 3 (.leaf ![43, 115, 19, 12]) (.leaf ![42, 116, 21, 10]))) (.branch 6 (.branch 5 (.leaf ![44, 114, 20, 11]) (.leaf ![134, 100, 76, 33])) (.branch 7 (.leaf ![132, 101, 75, 31]) (.leaf ![133, 99, 77, 32])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![86, 103, 98, 27]) (.leaf ![84, 104, 97, 25])) (.branch 11 (.leaf ![85, 102, 96, 26]) (.leaf ![70, 97, 132, 21]))) (.branch 14 (.branch 13 (.leaf ![69, 98, 134, 19]) (.leaf ![71, 96, 133, 20])) (.branch 15 (.leaf ![137, 109, 150, 15]) (.leaf ![135, 110, 151, 13]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![136, 108, 152, 14]) (.leaf ![119, 112, 141, 36])) (.branch 19 (.leaf ![117, 113, 142, 34]) (.leaf ![118, 111, 143, 35]))) (.branch 22 (.branch 21 (.leaf ![97, 106, 73, 30]) (.leaf ![96, 107, 74, 28])) (.branch 23 (.leaf ![98, 105, 72, 29]) (.leaf ![140, 118, 104, 24])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![138, 119, 102, 22]) (.leaf ![139, 117, 103, 23])) (.branch 27 (.leaf ![62, 94, 25, 18]) (.leaf ![60, 95, 26, 16]))) (.branch 30 (.branch 29 (.leaf ![61, 93, 27, 17]) (.leaf ![64, 17, 28, 92])) (.branch 31 (.leaf ![65, 18, 30, 90]) (.leaf ![63, 16, 29, 91]))))))

@[expose] public def nextBlock3 : Lean.RArray (Fin 4 → Fin 156) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![74, 20, 85, 77]) (.leaf ![73, 21, 84, 75])) (.branch 3 (.leaf ![72, 19, 86, 76]) (.leaf ![145, 32, 107, 71]))) (.branch 6 (.branch 5 (.leaf ![146, 33, 106, 69]) (.leaf ![144, 31, 105, 70])) (.branch 7 (.leaf ![88, 26, 138, 74]) (.leaf ![89, 27, 139, 72])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![87, 25, 140, 73]) (.leaf ![101, 29, 144, 86])) (.branch 11 (.leaf ![100, 30, 146, 84]) (.leaf ![99, 28, 145, 85]))) (.branch 14 (.branch 13 (.leaf ![148, 14, 153, 80]) (.leaf ![149, 15, 154, 78])) (.branch 15 (.leaf ![147, 13, 155, 79]) (.leaf ![112, 35, 113, 83]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![113, 36, 111, 81]) (.leaf ![111, 34, 112, 82])) (.branch 19 (.leaf ![47, 11, 34, 68]) (.leaf ![46, 12, 35, 66]))) (.branch 22 (.branch 21 (.leaf ![45, 10, 36, 67]) (.leaf ![142, 23, 82, 89])) (.branch 23 (.leaf ![143, 24, 83, 87]) (.leaf ![141, 22, 81, 88])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![48, 126, 4, 129]) (.leaf ![49, 127, 5, 131])) (.branch 27 (.leaf ![50, 128, 6, 130]) (.leaf ![37, 123, 13, 123]))) (.branch 30 (.branch 29 (.leaf ![38, 124, 14, 124]) (.leaf ![39, 125, 15, 125])) (.branch 31 (.leaf ![51, 129, 22, 120]) (.leaf ![52, 131, 23, 121]))))))

@[expose] public def nextBlock4 : Lean.RArray (Fin 4 → Fin 156) := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf ![53, 130, 24, 122]) (.branch 2 (.leaf ![54, 120, 31, 126]) (.leaf ![56, 122, 32, 128]))) (.branch 5 (.branch 4 (.leaf ![55, 121, 33, 127]) (.leaf ![75, 150, 70, 141])) (.branch 6 (.leaf ![77, 152, 71, 143]) (.leaf ![76, 151, 69, 142])))) (.branch 10 (.branch 8 (.leaf ![151, 135, 79, 135]) (.branch 9 (.leaf ![152, 136, 80, 136]) (.leaf ![150, 137, 78, 137]))) (.branch 12 (.branch 11 (.leaf ![102, 144, 88, 153]) (.leaf ![103, 146, 89, 154])) (.branch 13 (.leaf ![104, 145, 87, 155]) (.leaf ![81, 132, 119, 150]))))) (.branch 21 (.branch 17 (.branch 15 (.leaf ![82, 134, 117, 151]) (.branch 16 (.leaf ![83, 133, 118, 152]) (.leaf ![105, 153, 101, 138]))) (.branch 19 (.branch 18 (.leaf ![107, 155, 99, 140]) (.leaf ![106, 154, 100, 139])) (.branch 20 (.leaf ![155, 147, 110, 147]) (.leaf ![153, 148, 108, 148])))) (.branch 24 (.branch 22 (.leaf ![154, 149, 109, 149]) (.branch 23 (.leaf ![78, 141, 137, 132]) (.leaf ![79, 142, 135, 134]))) (.branch 26 (.branch 25 (.leaf ![80, 143, 136, 133]) (.leaf ![108, 138, 148, 144])) (.branch 27 (.leaf ![109, 139, 149, 146]) (.leaf ![110, 140, 147, 145]))))))

@[expose] public def factorBlock0 : Lean.RArray (Fin 4 → Fin 27) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![21, 21, 0, 21]) (.leaf ![21, 21, 21, 13])) (.branch 3 (.leaf ![12, 12, 0, 8]) (.leaf ![11, 11, 0, 5]))) (.branch 6 (.branch 5 (.leaf ![0, 17, 0, 15]) (.leaf ![0, 19, 0, 20])) (.branch 7 (.leaf ![0, 18, 0, 16]) (.leaf ![24, 14, 0, 24])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![26, 7, 0, 26]) (.leaf ![25, 6, 0, 25])) (.branch 11 (.leaf ![0, 0, 21, 2]) (.leaf ![12, 0, 12, 2]))) (.branch 14 (.branch 13 (.leaf ![11, 0, 11, 2]) (.leaf ![0, 0, 0, 2])) (.branch 15 (.leaf ![0, 0, 0, 2]) (.leaf ![0, 0, 0, 2]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![24, 0, 24, 2]) (.leaf ![26, 0, 26, 2])) (.branch 19 (.leaf ![25, 0, 25, 2]) (.leaf ![21, 0, 4, 2]))) (.branch 22 (.branch 21 (.leaf ![12, 0, 4, 2]) (.leaf ![11, 0, 4, 2])) (.branch 23 (.leaf ![0, 0, 4, 2]) (.leaf ![0, 0, 4, 2])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![0, 0, 4, 2]) (.leaf ![24, 0, 4, 2])) (.branch 27 (.leaf ![26, 0, 4, 2]) (.leaf ![25, 0, 4, 2]))) (.branch 30 (.branch 29 (.leaf ![21, 0, 22, 2]) (.leaf ![12, 0, 22, 2])) (.branch 31 (.leaf ![11, 0, 22, 2]) (.leaf ![0, 0, 22, 2]))))))

@[expose] public def factorBlock1 : Lean.RArray (Fin 4 → Fin 27) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![0, 0, 22, 2]) (.leaf ![0, 0, 22, 2])) (.branch 3 (.leaf ![24, 0, 22, 2]) (.leaf ![26, 0, 22, 2]))) (.branch 6 (.branch 5 (.leaf ![25, 0, 22, 2]) (.leaf ![0, 24, 0, 21])) (.branch 7 (.leaf ![0, 26, 0, 12]) (.leaf ![0, 25, 0, 11])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![0, 21, 12, 0]) (.leaf ![0, 0, 11, 21])) (.branch 11 (.leaf ![9, 0, 21, 0]) (.leaf ![9, 0, 12, 0]))) (.branch 14 (.branch 13 (.leaf ![9, 0, 11, 0]) (.leaf ![23, 0, 14, 0])) (.branch 15 (.leaf ![23, 0, 7, 0]) (.leaf ![23, 0, 6, 0]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![0, 0, 0, 0]) (.leaf ![0, 0, 0, 0])) (.branch 19 (.leaf ![0, 0, 0, 0]) (.leaf ![9, 0, 9, 0]))) (.branch 22 (.branch 21 (.leaf ![9, 0, 9, 0]) (.leaf ![9, 0, 9, 0])) (.branch 23 (.leaf ![23, 0, 23, 0]) (.leaf ![23, 0, 23, 0])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![23, 0, 23, 0]) (.leaf ![0, 0, 24, 0])) (.branch 27 (.leaf ![0, 0, 26, 0]) (.leaf ![0, 0, 25, 0]))) (.branch 30 (.branch 29 (.leaf ![9, 0, 24, 0]) (.leaf ![9, 0, 26, 0])) (.branch 31 (.leaf ![9, 0, 25, 0]) (.leaf ![23, 0, 17, 0]))))))

@[expose] public def factorBlock2 : Lean.RArray (Fin 4 → Fin 27) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![23, 0, 19, 0]) (.leaf ![23, 0, 18, 0])) (.branch 3 (.leaf ![11, 2, 21, 0]) (.leaf ![21, 2, 12, 0]))) (.branch 6 (.branch 5 (.leaf ![12, 2, 11, 0]) (.leaf ![0, 2, 21, 0])) (.branch 7 (.leaf ![0, 2, 12, 0]) (.leaf ![0, 2, 11, 0])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![25, 2, 14, 0]) (.leaf ![24, 2, 7, 0])) (.branch 11 (.leaf ![26, 2, 6, 0]) (.leaf ![11, 2, 11, 0]))) (.branch 14 (.branch 13 (.leaf ![21, 2, 21, 0]) (.leaf ![12, 2, 12, 0])) (.branch 15 (.leaf ![0, 2, 0, 0]) (.leaf ![0, 2, 0, 0]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![0, 2, 0, 0]) (.leaf ![25, 2, 18, 0])) (.branch 19 (.leaf ![24, 2, 17, 0]) (.leaf ![26, 2, 19, 0]))) (.branch 22 (.branch 21 (.leaf ![11, 2, 24, 0]) (.leaf ![21, 2, 26, 0])) (.branch 23 (.leaf ![12, 2, 25, 0]) (.leaf ![0, 2, 17, 0])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![0, 2, 19, 0]) (.leaf ![0, 2, 18, 0])) (.branch 27 (.leaf ![25, 2, 24, 0]) (.leaf ![24, 2, 26, 0]))) (.branch 30 (.branch 29 (.leaf ![26, 2, 25, 0]) (.leaf ![20, 2, 21, 2])) (.branch 31 (.leaf ![16, 2, 12, 2]) (.leaf ![15, 2, 11, 2]))))))

@[expose] public def factorBlock3 : Lean.RArray (Fin 4 → Fin 27) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![8, 2, 21, 2]) (.leaf ![5, 2, 12, 2])) (.branch 3 (.leaf ![13, 2, 11, 2]) (.leaf ![2, 2, 14, 2]))) (.branch 6 (.branch 5 (.leaf ![2, 2, 7, 2]) (.leaf ![2, 2, 6, 2])) (.branch 7 (.leaf ![20, 2, 20, 2]) (.leaf ![16, 2, 16, 2])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![15, 2, 15, 2]) (.leaf ![8, 2, 3, 2])) (.branch 11 (.leaf ![5, 2, 1, 2]) (.leaf ![13, 2, 10, 2]))) (.branch 14 (.branch 13 (.leaf ![2, 2, 0, 2]) (.leaf ![2, 2, 0, 2])) (.branch 15 (.leaf ![2, 2, 0, 2]) (.leaf ![20, 2, 17, 2]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![16, 2, 19, 2]) (.leaf ![15, 2, 18, 2])) (.branch 19 (.leaf ![8, 2, 24, 2]) (.leaf ![5, 2, 26, 2]))) (.branch 22 (.branch 21 (.leaf ![13, 2, 25, 2]) (.leaf ![2, 2, 24, 2])) (.branch 23 (.leaf ![2, 2, 26, 2]) (.leaf ![2, 2, 25, 2])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![0, 9, 0, 23]) (.leaf ![0, 9, 0, 23])) (.branch 27 (.leaf ![0, 9, 0, 23]) (.leaf ![0, 4, 0, 9]))) (.branch 30 (.branch 29 (.leaf ![0, 4, 0, 9]) (.leaf ![0, 4, 0, 9])) (.branch 31 (.leaf ![4, 22, 0, 4]) (.leaf ![4, 22, 0, 4]))))))

@[expose] public def factorBlock4 : Lean.RArray (Fin 4 → Fin 27) := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf ![4, 22, 0, 4]) (.branch 2 (.leaf ![22, 22, 0, 23]) (.leaf ![22, 22, 0, 23]))) (.branch 5 (.branch 4 (.leaf ![22, 22, 0, 23]) (.leaf ![12, 12, 0, 3])) (.branch 6 (.leaf ![11, 11, 0, 1]) (.leaf ![21, 21, 0, 10])))) (.branch 10 (.branch 8 (.leaf ![0, 19, 0, 20]) (.branch 9 (.leaf ![0, 18, 0, 16]) (.leaf ![0, 17, 0, 15]))) (.branch 12 (.branch 11 (.leaf ![19, 12, 0, 19]) (.leaf ![18, 11, 0, 18])) (.branch 13 (.leaf ![17, 21, 0, 17]) (.leaf ![16, 1, 2, 16]))))) (.branch 21 (.branch 17 (.branch 15 (.leaf ![15, 10, 2, 15]) (.branch 16 (.leaf ![20, 3, 2, 20]) (.leaf ![1, 1, 2, 11]))) (.branch 19 (.branch 18 (.leaf ![10, 10, 2, 21]) (.leaf ![3, 3, 2, 12])) (.branch 20 (.leaf ![2, 16, 2, 18]) (.leaf ![2, 15, 2, 17])))) (.branch 24 (.branch 22 (.leaf ![2, 20, 2, 19]) (.branch 23 (.leaf ![0, 18, 0, 11]) (.leaf ![0, 17, 0, 21]))) (.branch 26 (.branch 25 (.leaf ![0, 19, 0, 12]) (.leaf ![0, 20, 2, 3])) (.branch 27 (.leaf ![0, 16, 2, 1]) (.leaf ![0, 15, 2, 10]))))))
@[expose] public def codes : Fin 156 → MatrixCode := fun j =>
  ((.branch 2 (.branch 1 (.leaf codeBlock0) (.leaf codeBlock1)) (.branch 3 (.leaf codeBlock2) (.branch 4 (.leaf codeBlock3) (.leaf codeBlock4)))) : Lean.RArray (Lean.RArray (MatrixCode))).get (j.val / 32) |>.get (j.val % 32)
@[expose] public def detCheck (k : Nat) : Bool := (codeDet (codes ⟨k % 156, Nat.mod_lt _ (by decide)⟩)).val == 1
set_option maxHeartbeats 4000000 in
private theorem detCheck_0 : checkRange detCheck 0 64 = true := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem detCheck_1 : checkRange detCheck 64 64 = true := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem detCheck_2 : checkRange detCheck 128 28 = true := by decide +kernel

public theorem det : ∀ j, codeDet (codes j) = 1 := by
  have h := checkRange_fin (by decide : 0 < 156)
    (fun j => (codeDet (codes j)).val == 1) (checkRange_append detCheck_0 (checkRange_append detCheck_1 detCheck_2))
  intro j
  apply Fin.ext
  exact beq_iff_eq.mp (h j)
@[expose] public def rep (j : Fin 156) : SL := finiteModelEquiv ⟨codes j, det j⟩
@[expose] public def words : Fin 27 → List (Fin 4) := fun j =>
  ((.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf []) (.branch 2 (.leaf [0]) (.leaf [1]))) (.branch 4 (.leaf [2]) (.branch 5 (.leaf [0, 0]) (.leaf [0, 1])))) (.branch 9 (.branch 7 (.leaf [1, 0]) (.branch 8 (.leaf [1, 2]) (.leaf [2, 1]))) (.branch 11 (.branch 10 (.leaf [2, 2]) (.leaf [0, 0, 0])) (.branch 12 (.leaf [1, 0, 1]) (.leaf [1, 2, 1]))))) (.branch 20 (.branch 16 (.branch 14 (.leaf [0, 0, 0, 1]) (.branch 15 (.leaf [0, 0, 1, 2]) (.leaf [0, 1, 0, 1]))) (.branch 18 (.branch 17 (.leaf [0, 1, 2, 1]) (.leaf [1, 0, 1, 0])) (.branch 19 (.leaf [1, 0, 1, 2]) (.leaf [1, 2, 1, 0])))) (.branch 23 (.branch 21 (.leaf [2, 1, 0, 1]) (.branch 22 (.leaf [0, 0, 1, 2, 1]) (.leaf [0, 1, 0, 1, 0]))) (.branch 25 (.branch 24 (.leaf [0, 1, 0, 1, 2]) (.leaf [1, 0, 1, 0, 1])) (.branch 26 (.leaf [1, 0, 1, 2, 1]) (.leaf [1, 2, 1, 0, 1])))))) : Lean.RArray (List (Fin 4))).get j.val
@[expose] public def wordCodes : Fin 27 → MatrixCode := fun j =>
  ((.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf 6643) (.branch 2 (.leaf 17600) (.leaf 13448))) (.branch 4 (.leaf 17594) (.branch 5 (.leaf 6664) (.leaf 4720)))) (.branch 9 (.branch 7 (.leaf 9250) (.branch 8 (.leaf 9256) (.leaf 4714))) (.branch 11 (.branch 10 (.leaf 6658) (.leaf 17579)) (.branch 12 (.leaf 2447) (.leaf 2453))))) (.branch 20 (.branch 16 (.branch 14 (.leaf 4699) (.branch 15 (.leaf 9235) (.leaf 17740))) (.branch 18 (.branch 17 (.leaf 17761) (.leaf 2836)) (.branch 19 (.leaf 2851) (.leaf 2857)))) (.branch 23 (.branch 21 (.leaf 17755) (.branch 22 (.leaf 2432) (.leaf 7232))) (.branch 25 (.branch 24 (.leaf 7226) (.leaf 8912)) (.branch 26 (.leaf 8927) (.leaf 8933)))))) : Lean.RArray MatrixCode).get j.val
set_option maxHeartbeats 4000000 in
public theorem wordEval : ∀ j, (evalWord (nodeGenerator 31) (words j)).val =
    decodeMatrix (wordCodes j) := by decide +kernel
@[expose] public def next : Fin 156 → Fin 4 → Fin 156 := fun j =>
  ((.branch 2 (.branch 1 (.leaf nextBlock0) (.leaf nextBlock1)) (.branch 3 (.leaf nextBlock2) (.branch 4 (.leaf nextBlock3) (.leaf nextBlock4)))) : Lean.RArray (Lean.RArray (Fin 4 → Fin 156))).get (j.val / 32) |>.get (j.val % 32)
@[expose] public def factorIndex : Fin 156 → Fin 4 → Fin 27 := fun j =>
  ((.branch 2 (.branch 1 (.leaf factorBlock0) (.leaf factorBlock1)) (.branch 3 (.leaf factorBlock2) (.branch 4 (.leaf factorBlock3) (.leaf factorBlock4)))) : Lean.RArray (Lean.RArray (Fin 4 → Fin 27))).get (j.val / 32) |>.get (j.val % 32)
@[expose] public def table : RightCosetTable 4 4 156 where
  base := 0
  next := next
  factor := fun j k => words (factorIndex j k)
@[expose] public def transitionCheck (j : Fin 156) : Bool :=
  matrixEq ((rep j).val * (ambientGenerator 0).val)
    (decodeMatrix (wordCodes (factorIndex j 0)) * (rep (next j 0)).val) &&
  matrixEq ((rep j).val * (ambientGenerator 1).val)
    (decodeMatrix (wordCodes (factorIndex j 1)) * (rep (next j 1)).val) &&
  matrixEq ((rep j).val * (ambientGenerator 2).val)
    (decodeMatrix (wordCodes (factorIndex j 2)) * (rep (next j 2)).val) &&
  matrixEq ((rep j).val * (ambientGenerator 3).val)
    (decodeMatrix (wordCodes (factorIndex j 3)) * (rep (next j 3)).val)
@[expose] public def rowCheck (k : Nat) : Bool := transitionCheck ⟨k % 156, Nat.mod_lt _ (by decide)⟩
set_option maxHeartbeats 4000000 in
private theorem rowCheck_0 : checkRange rowCheck 0 64 = true := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem rowCheck_1 : checkRange rowCheck 64 64 = true := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem rowCheck_2 : checkRange rowCheck 128 28 = true := by decide +kernel

public theorem checked : ∀ j, transitionCheck j = true :=
  checkRange_fin (by decide) transitionCheck (checkRange_append rowCheck_0 (checkRange_append rowCheck_1 rowCheck_2))
public theorem transitions : ∀ j k, (rep j).val * (ambientGenerator k).val =
    decodeMatrix (wordCodes (factorIndex j k)) * (rep (next j k)).val := by
  intro j k
  have h := checked j
  simp only [transitionCheck, Bool.and_eq_true] at h
  fin_cases k
  · exact matrixEq_sound h.1.1.1
  · exact matrixEq_sound h.1.1.2
  · exact matrixEq_sound h.1.2
  · exact matrixEq_sound h.2
public theorem valid : table.Valid ambientGenerator (nodeGenerator 31) rep := by
  constructor
  · decide +kernel
  · intro j k
    apply Subtype.ext
    change (rep j).val * (ambientGenerator k).val =
      (evalWord (nodeGenerator 31) (words (factorIndex j k))).val * (rep (next j k)).val
    rw [wordEval]
    exact transitions j k
public theorem cover : RightCosetCover (properNode 31) rep := by
  rw [properNode_eq_wordSubgroup]
  exact table.sound ambientGenerator ambientInverse ambientGenerator_inv
    ambient_wordSubgroup_eq_top (nodeGenerator 31) (symmInv (n := (generatorCodes 31).length))
    (nodeGenerator_inv 31) rep valid
end Matrix.PSL3Three.CertifiedEnumeration.Cosets31
