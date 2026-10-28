module
public import Theory.SpecificGroups.PSL3Three.CosetCover.Check
/-!
# Checked right cosets for node 29

These are untrusted matrix codes and subgroup words generated from the fixed
lists in `RepresentativeBounds`. The kernel checks determinants, word values,
and every transition by the four ambient generators. `cover` then follows from
`RightCosetTable.sound`, using the proved generation of the actual SL₃(3).

Source: the elementary coset-table argument in `SubgroupEnumeration` and
GLS III, Theorem 6.5.3. Row zero represents the identity matrix.
-/

namespace Matrix.PSL3Three.CertifiedEnumeration.Cosets29
open Theory.GroupTheory Theory.GroupTheory.SubgroupEnumeration CosetCheck
set_option maxRecDepth 100000

@[expose] public def codeBlock0 : Lean.RArray (MatrixCode) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 6643) (.leaf 828)) (.branch 3 (.leaf 829) (.leaf 830))) (.branch 6 (.branch 5 (.leaf 831) (.leaf 832)) (.branch 7 (.leaf 833) (.leaf 834)))) (.branch 12 (.branch 10 (.branch 9 (.leaf 835) (.leaf 836)) (.branch 11 (.leaf 855) (.leaf 856))) (.branch 14 (.branch 13 (.leaf 857) (.leaf 858)) (.branch 15 (.leaf 859) (.leaf 860))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf 861) (.leaf 862)) (.branch 19 (.leaf 863) (.leaf 882))) (.branch 22 (.branch 21 (.leaf 883) (.leaf 884)) (.branch 23 (.leaf 885) (.leaf 886)))) (.branch 28 (.branch 26 (.branch 25 (.leaf 887) (.leaf 888)) (.branch 27 (.leaf 889) (.leaf 890))) (.branch 30 (.branch 29 (.leaf 900) (.leaf 901)) (.branch 31 (.leaf 902) (.leaf 903))))))

@[expose] public def codeBlock1 : Lean.RArray (MatrixCode) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 904) (.leaf 905)) (.branch 3 (.leaf 906) (.leaf 907))) (.branch 6 (.branch 5 (.leaf 908) (.leaf 927)) (.branch 7 (.leaf 928) (.leaf 929)))) (.branch 12 (.branch 10 (.branch 9 (.leaf 930) (.leaf 931)) (.branch 11 (.leaf 932) (.leaf 933))) (.branch 14 (.branch 13 (.leaf 934) (.leaf 935)) (.branch 15 (.leaf 954) (.leaf 955))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf 956) (.leaf 957)) (.branch 19 (.leaf 958) (.leaf 959))) (.branch 22 (.branch 21 (.leaf 960) (.leaf 961)) (.branch 23 (.leaf 962) (.leaf 975)))) (.branch 28 (.branch 26 (.branch 25 (.leaf 976) (.leaf 977)) (.branch 27 (.leaf 1002) (.leaf 1003))) (.branch 30 (.branch 29 (.leaf 1004) (.leaf 1029)) (.branch 31 (.leaf 1030) (.leaf 1031))))))

@[expose] public def codeBlock2 : Lean.RArray (MatrixCode) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 1221) (.leaf 1222)) (.branch 3 (.leaf 1223) (.leaf 1248))) (.branch 6 (.branch 5 (.leaf 1249) (.leaf 1250)) (.branch 7 (.leaf 1275) (.leaf 1276)))) (.branch 12 (.branch 10 (.branch 9 (.leaf 1277) (.leaf 2304)) (.branch 11 (.leaf 2305) (.leaf 2306))) (.branch 14 (.branch 13 (.leaf 2307) (.leaf 2308)) (.branch 15 (.leaf 2309) (.leaf 2310))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf 2311) (.leaf 2312)) (.branch 19 (.leaf 2340) (.leaf 2341))) (.branch 22 (.branch 21 (.leaf 2342) (.leaf 2343)) (.branch 23 (.leaf 2344) (.leaf 2345)))) (.branch 28 (.branch 26 (.branch 25 (.leaf 2346) (.leaf 2347)) (.branch 27 (.leaf 2348) (.leaf 2385))) (.branch 30 (.branch 29 (.leaf 2386) (.leaf 2387)) (.branch 31 (.leaf 2388) (.leaf 2389))))))

@[expose] public def codeBlock3 : Lean.RArray (MatrixCode) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 2390) (.leaf 2391)) (.branch 3 (.leaf 2392) (.leaf 2393))) (.branch 6 (.branch 5 (.leaf 2421) (.leaf 2422)) (.branch 7 (.leaf 2423) (.leaf 2424)))) (.branch 12 (.branch 10 (.branch 9 (.leaf 2425) (.leaf 2426)) (.branch 11 (.leaf 2427) (.leaf 2428))) (.branch 14 (.branch 13 (.leaf 2429) (.leaf 2432)) (.branch 15 (.leaf 2513) (.leaf 2594))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf 2755) (.leaf 2836)) (.branch 19 (.leaf 3060) (.leaf 3061))) (.branch 22 (.branch 21 (.leaf 3062) (.leaf 3063)) (.branch 23 (.leaf 3064) (.leaf 3065)))) (.branch 28 (.branch 26 (.branch 25 (.leaf 3066) (.leaf 3067)) (.branch 27 (.leaf 3068) (.leaf 3123))) (.branch 30 (.branch 29 (.leaf 3124) (.leaf 3125)) (.branch 31 (.leaf 3126) (.leaf 3127))))))

@[expose] public def codeBlock4 : Lean.RArray (MatrixCode) := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf 3128) (.branch 2 (.leaf 3129) (.leaf 3130))) (.branch 5 (.branch 4 (.leaf 3131) (.leaf 6837)) (.branch 6 (.leaf 6838) (.leaf 6839)))) (.branch 10 (.branch 8 (.leaf 6861) (.branch 9 (.leaf 6862) (.leaf 6863))) (.branch 12 (.branch 11 (.leaf 6886) (.leaf 6968)) (.branch 13 (.leaf 7080) (.leaf 7081))))) (.branch 21 (.branch 17 (.branch 15 (.leaf 7082) (.branch 16 (.leaf 7104) (.leaf 7105))) (.branch 19 (.branch 18 (.leaf 7106) (.leaf 7129)) (.branch 20 (.leaf 7211) (.leaf 7593)))) (.branch 24 (.branch 22 (.leaf 7594) (.branch 23 (.leaf 7595) (.leaf 7806))) (.branch 26 (.branch 25 (.leaf 7807) (.leaf 7808)) (.branch 27 (.leaf 9154) (.leaf 9317))))))

@[expose] public def nextBlock0 : Lean.RArray (Fin 4 → Fin 156) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![28, 56, 55, 65]) (.leaf ![64, 100, 109, 82])) (.branch 3 (.leaf ![34, 104, 57, 89]) (.leaf ![7, 108, 66, 87]))) (.branch 6 (.branch 5 (.leaf ![65, 103, 30, 85]) (.leaf ![44, 107, 96, 83])) (.branch 7 (.leaf ![26, 102, 81, 90]) (.leaf ![66, 106, 3, 88])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![54, 101, 87, 86]) (.leaf ![18, 105, 108, 84])) (.branch 11 (.leaf ![132, 123, 110, 19]) (.leaf ![79, 127, 60, 26]))) (.branch 14 (.branch 13 (.leaf ![88, 131, 69, 24]) (.leaf ![133, 126, 75, 22])) (.branch 15 (.leaf ![98, 130, 33, 20]) (.leaf ![130, 125, 99, 27]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![134, 129, 84, 25]) (.leaf ![122, 124, 105, 23])) (.branch 19 (.leaf ![108, 128, 9, 21]) (.leaf ![140, 10, 111, 123]))) (.branch 22 (.branch 21 (.leaf ![97, 14, 63, 130]) (.leaf ![106, 18, 72, 128])) (.branch 23 (.leaf ![141, 13, 93, 126]) (.leaf ![121, 17, 78, 124])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![89, 12, 36, 131]) (.leaf ![142, 16, 102, 129])) (.branch 27 (.leaf ![81, 11, 6, 127]) (.leaf ![131, 15, 90, 125]))) (.branch 30 (.branch 29 (.leaf ![55, 73, 0, 91]) (.leaf ![31, 77, 56, 98])) (.branch 31 (.leaf ![4, 81, 65, 96]) (.leaf ![56, 76, 29, 94]))))))

@[expose] public def nextBlock1 : Lean.RArray (Fin 4 → Fin 156) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![50, 80, 77, 92]) (.leaf ![14, 75, 98, 99])) (.branch 3 (.leaf ![57, 79, 2, 97]) (.leaf ![42, 74, 104, 95]))) (.branch 6 (.branch 5 (.leaf ![24, 78, 89, 93]) (.leaf ![135, 46, 112, 114])) (.branch 7 (.leaf ![76, 50, 59, 121]) (.leaf ![85, 54, 68, 119])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![136, 49, 74, 117]) (.leaf ![118, 53, 95, 115])) (.branch 11 (.leaf ![104, 48, 35, 122]) (.leaf ![137, 52, 83, 120]))) (.branch 14 (.branch 13 (.leaf ![96, 47, 5, 118]) (.leaf ![128, 51, 107, 116])) (.branch 15 (.leaf ![143, 114, 113, 37]) (.leaf ![94, 118, 62, 44]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![103, 122, 71, 42]) (.leaf ![144, 117, 92, 40])) (.branch 19 (.leaf ![77, 121, 32, 38]) (.leaf ![127, 116, 80, 45]))) (.branch 22 (.branch 21 (.leaf ![145, 120, 101, 43]) (.leaf ![119, 115, 86, 41])) (.branch 23 (.leaf ![87, 119, 8, 39]) (.leaf ![0, 55, 28, 55])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![29, 65, 31, 0]) (.leaf ![2, 109, 34, 66])) (.branch 27 (.leaf ![138, 58, 73, 58]) (.leaf ![38, 68, 76, 112]))) (.branch 30 (.branch 29 (.leaf ![11, 110, 79, 69]) (.leaf ![146, 61, 91, 61])) (.branch 31 (.leaf ![47, 71, 94, 113]) (.leaf ![20, 111, 97, 72]))))))

@[expose] public def nextBlock2 : Lean.RArray (Fin 4 → Fin 156) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![109, 64, 1, 64]) (.leaf ![30, 0, 4, 56])) (.branch 3 (.leaf ![3, 57, 7, 109]) (.leaf ![139, 67, 82, 67]))) (.branch 6 (.branch 5 (.leaf ![39, 112, 85, 59]) (.leaf ![12, 60, 88, 110])) (.branch 7 (.leaf ![147, 70, 100, 70]) (.leaf ![48, 113, 103, 62])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![21, 63, 106, 111]) (.leaf ![58, 91, 138, 28])) (.branch 11 (.leaf ![40, 95, 136, 35]) (.leaf ![13, 99, 133, 33]))) (.branch 14 (.branch 13 (.leaf ![59, 94, 38, 31]) (.leaf ![32, 98, 50, 29])) (.branch 15 (.leaf ![23, 93, 121, 36]) (.leaf ![60, 97, 11, 34]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![51, 92, 127, 32]) (.leaf ![6, 96, 26, 30])) (.branch 19 (.leaf ![67, 1, 139, 100]) (.leaf ![43, 5, 137, 107]))) (.branch 22 (.branch 21 (.leaf ![16, 9, 134, 105]) (.leaf ![68, 4, 39, 103])) (.branch 23 (.leaf ![53, 8, 119, 101]) (.leaf ![8, 3, 54, 108])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![69, 7, 12, 106]) (.leaf ![36, 2, 24, 104])) (.branch 27 (.leaf ![27, 6, 131, 102]) (.leaf ![61, 28, 146, 73]))) (.branch 30 (.branch 29 (.leaf ![49, 32, 144, 80]) (.leaf ![22, 36, 141, 78])) (.branch 31 (.leaf ![62, 31, 47, 76]) (.leaf ![41, 35, 118, 74]))))))

@[expose] public def nextBlock3 : Lean.RArray (Fin 4 → Fin 156) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![5, 30, 44, 81]) (.leaf ![63, 34, 20, 79])) (.branch 3 (.leaf ![33, 29, 14, 77]) (.leaf ![15, 33, 130, 75]))) (.branch 6 (.branch 5 (.leaf ![70, 82, 147, 1]) (.leaf ![52, 86, 145, 8])) (.branch 7 (.leaf ![25, 90, 142, 6]) (.leaf ![71, 85, 48, 4])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![35, 89, 42, 2]) (.leaf ![17, 84, 122, 9])) (.branch 11 (.leaf ![72, 88, 21, 7]) (.leaf ![45, 83, 128, 5]))) (.branch 14 (.branch 13 (.leaf ![9, 87, 18, 3]) (.leaf ![1, 66, 64, 57])) (.branch 15 (.leaf ![10, 69, 132, 60]) (.leaf ![19, 72, 140, 63]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![37, 59, 135, 68]) (.leaf ![46, 62, 143, 71])) (.branch 19 (.leaf ![151, 37, 154, 46]) (.leaf ![117, 41, 152, 53]))) (.branch 22 (.branch 21 (.leaf ![126, 45, 149, 51]) (.leaf ![152, 40, 115, 49])) (.branch 23 (.leaf ![95, 44, 41, 47]) (.leaf ![86, 39, 53, 54])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![153, 43, 124, 52]) (.leaf ![78, 38, 23, 50])) (.branch 27 (.leaf ![105, 42, 17, 48]) (.leaf ![148, 19, 155, 10]))) (.branch 30 (.branch 29 (.leaf ![120, 23, 153, 17]) (.leaf ![129, 27, 150, 15])) (.branch 31 (.leaf ![149, 22, 116, 13]) (.leaf ![80, 26, 51, 11]))))))

@[expose] public def nextBlock4 : Lean.RArray (Fin 4 → Fin 156) := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf ![107, 21, 45, 18]) (.branch 2 (.leaf ![150, 25, 125, 16]) (.leaf ![99, 20, 15, 14]))) (.branch 5 (.branch 4 (.leaf ![90, 24, 27, 12]) (.leaf ![110, 132, 10, 132])) (.branch 6 (.leaf ![75, 138, 13, 136]) (.leaf ![84, 137, 16, 139])))) (.branch 10 (.branch 8 (.leaf ![112, 135, 37, 135]) (.branch 9 (.leaf ![74, 133, 40, 138]) (.leaf ![83, 139, 43, 134]))) (.branch 12 (.branch 11 (.leaf ![73, 136, 58, 133]) (.leaf ![82, 134, 67, 137])) (.branch 13 (.leaf ![111, 140, 19, 140]) (.leaf ![93, 146, 22, 144]))))) (.branch 21 (.branch 17 (.branch 15 (.leaf ![102, 145, 25, 147]) (.branch 16 (.leaf ![113, 143, 46, 143]) (.leaf ![92, 141, 49, 146]))) (.branch 19 (.branch 18 (.leaf ![101, 147, 52, 142]) (.leaf ![91, 144, 61, 141])) (.branch 20 (.leaf ![100, 142, 70, 145]) (.leaf ![155, 148, 123, 148])))) (.branch 24 (.branch 22 (.leaf ![116, 154, 126, 152]) (.branch 23 (.leaf ![125, 153, 129, 155]) (.leaf ![154, 151, 114, 151]))) (.branch 26 (.branch 25 (.leaf ![115, 149, 117, 154]) (.leaf ![124, 155, 120, 150])) (.branch 27 (.leaf ![114, 152, 151, 149]) (.leaf ![123, 150, 148, 153]))))))

@[expose] public def factorBlock0 : Lean.RArray (Fin 4 → Fin 33) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![17, 16, 0, 25]) (.leaf ![17, 17, 0, 17])) (.branch 3 (.leaf ![18, 17, 22, 17]) (.leaf ![6, 17, 21, 17]))) (.branch 6 (.branch 5 (.leaf ![17, 17, 12, 17]) (.leaf ![18, 17, 3, 17])) (.branch 7 (.leaf ![6, 17, 3, 17]) (.leaf ![17, 17, 9, 17])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![18, 17, 1, 17]) (.leaf ![6, 17, 1, 17])) (.branch 11 (.leaf ![0, 0, 0, 17]) (.leaf ![32, 0, 32, 17]))) (.branch 14 (.branch 13 (.leaf ![28, 0, 28, 17]) (.leaf ![0, 0, 3, 17])) (.branch 15 (.leaf ![13, 0, 12, 17]) (.leaf ![2, 0, 3, 17]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![0, 0, 1, 17]) (.leaf ![32, 0, 1, 17])) (.branch 19 (.leaf ![2, 0, 9, 17]) (.leaf ![0, 24, 0, 24]))) (.branch 22 (.branch 21 (.leaf ![29, 24, 29, 24]) (.leaf ![31, 24, 31, 24])) (.branch 23 (.leaf ![0, 24, 3, 24]) (.leaf ![7, 24, 3, 24])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![4, 24, 12, 24]) (.leaf ![0, 24, 1, 24])) (.branch 27 (.leaf ![7, 24, 9, 24]) (.leaf ![31, 24, 1, 24]))) (.branch 30 (.branch 29 (.leaf ![24, 24, 24, 24]) (.leaf ![23, 24, 8, 24])) (.branch 31 (.leaf ![10, 24, 19, 24]) (.leaf ![24, 24, 25, 24]))))))

@[expose] public def factorBlock1 : Lean.RArray (Fin 4 → Fin 33) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![23, 24, 1, 24]) (.leaf ![10, 24, 1, 24])) (.branch 3 (.leaf ![24, 24, 16, 24]) (.leaf ![23, 24, 3, 24]))) (.branch 6 (.branch 5 (.leaf ![10, 24, 3, 24]) (.leaf ![0, 17, 0, 17])) (.branch 7 (.leaf ![20, 17, 20, 17]) (.leaf ![27, 17, 27, 17])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![0, 17, 1, 17]) (.leaf ![20, 17, 1, 17])) (.branch 11 (.leaf ![11, 17, 25, 17]) (.leaf ![0, 17, 3, 17]))) (.branch 14 (.branch 13 (.leaf ![14, 17, 16, 17]) (.leaf ![11, 17, 3, 17])) (.branch 15 (.leaf ![0, 0, 0, 24]) (.leaf ![15, 0, 15, 24]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![30, 0, 30, 24]) (.leaf ![0, 0, 1, 24])) (.branch 19 (.leaf ![26, 0, 25, 24]) (.leaf ![30, 0, 1, 24]))) (.branch 22 (.branch 21 (.leaf ![0, 0, 3, 24]) (.leaf ![26, 0, 3, 24])) (.branch 23 (.leaf ![5, 0, 16, 24]) (.leaf ![0, 22, 17, 19])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![8, 21, 17, 18]) (.leaf ![19, 19, 17, 8])) (.branch 27 (.leaf ![0, 32, 0, 27]) (.leaf ![20, 28, 0, 20]))) (.branch 30 (.branch 29 (.leaf ![27, 27, 0, 20]) (.leaf ![0, 29, 0, 30])) (.branch 31 (.leaf ![15, 31, 0, 15]) (.leaf ![30, 30, 0, 15]))))))

@[expose] public def factorBlock2 : Lean.RArray (Fin 4 → Fin 33) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![24, 19, 24, 22]) (.leaf ![22, 23, 24, 21])) (.branch 3 (.leaf ![21, 8, 24, 21]) (.leaf ![0, 27, 0, 32]))) (.branch 6 (.branch 5 (.leaf ![32, 32, 0, 28]) (.leaf ![28, 20, 0, 28])) (.branch 7 (.leaf ![0, 30, 0, 29]) (.leaf ![29, 29, 0, 31])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![31, 15, 0, 31]) (.leaf ![0, 0, 0, 17])) (.branch 11 (.leaf ![3, 0, 3, 17]) (.leaf ![1, 0, 1, 17]))) (.branch 14 (.branch 13 (.leaf ![0, 0, 20, 17]) (.leaf ![3, 0, 14, 17])) (.branch 15 (.leaf ![1, 0, 14, 17]) (.leaf ![0, 0, 27, 17]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![3, 0, 27, 17]) (.leaf ![1, 0, 11, 17])) (.branch 19 (.leaf ![0, 24, 0, 0]) (.leaf ![1, 24, 1, 0]))) (.branch 22 (.branch 21 (.leaf ![3, 24, 3, 0]) (.leaf ![0, 24, 32, 0])) (.branch 23 (.leaf ![1, 24, 13, 0]) (.leaf ![3, 24, 13, 0])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![0, 24, 28, 0]) (.leaf ![1, 24, 2, 0])) (.branch 27 (.leaf ![3, 24, 28, 0]) (.leaf ![0, 17, 0, 0]))) (.branch 30 (.branch 29 (.leaf ![3, 17, 3, 0]) (.leaf ![1, 17, 1, 0])) (.branch 31 (.leaf ![0, 17, 15, 0]) (.leaf ![3, 17, 15, 0]))))))

@[expose] public def factorBlock3 : Lean.RArray (Fin 4 → Fin 33) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![1, 17, 26, 0]) (.leaf ![0, 17, 30, 0])) (.branch 3 (.leaf ![3, 17, 5, 0]) (.leaf ![1, 17, 5, 0]))) (.branch 6 (.branch 5 (.leaf ![0, 0, 0, 24]) (.leaf ![1, 0, 1, 24])) (.branch 7 (.leaf ![3, 0, 3, 24]) (.leaf ![0, 0, 29, 24])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![1, 0, 7, 24]) (.leaf ![3, 0, 29, 24])) (.branch 11 (.leaf ![0, 0, 31, 24]) (.leaf ![1, 0, 4, 24]))) (.branch 14 (.branch 13 (.leaf ![3, 0, 4, 24]) (.leaf ![0, 21, 17, 22])) (.branch 15 (.leaf ![0, 28, 0, 32]) (.leaf ![0, 31, 0, 29]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![0, 20, 0, 27]) (.leaf ![0, 15, 0, 30])) (.branch 19 (.leaf ![0, 24, 0, 0]) (.leaf ![26, 24, 26, 0]))) (.branch 22 (.branch 21 (.leaf ![30, 24, 30, 0]) (.leaf ![0, 24, 14, 0])) (.branch 23 (.leaf ![15, 24, 20, 0]) (.leaf ![5, 24, 14, 0])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![0, 24, 27, 0]) (.leaf ![26, 24, 11, 0])) (.branch 27 (.leaf ![30, 24, 27, 0]) (.leaf ![0, 17, 0, 0]))) (.branch 30 (.branch 29 (.leaf ![32, 17, 32, 0]) (.leaf ![2, 17, 2, 0])) (.branch 31 (.leaf ![0, 17, 29, 0]) (.leaf ![32, 17, 29, 0]))))))

@[expose] public def factorBlock4 : Lean.RArray (Fin 4 → Fin 33) := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf ![2, 17, 7, 0]) (.branch 2 (.leaf ![0, 17, 4, 0]) (.leaf ![13, 17, 4, 0]))) (.branch 5 (.branch 4 (.leaf ![28, 17, 31, 0]) (.leaf ![0, 1, 0, 3])) (.branch 6 (.leaf ![3, 3, 0, 1]) (.leaf ![1, 3, 0, 1])))) (.branch 10 (.branch 8 (.leaf ![0, 1, 0, 3]) (.branch 9 (.leaf ![1, 3, 0, 1]) (.leaf ![3, 3, 0, 1]))) (.branch 12 (.branch 11 (.leaf ![0, 3, 0, 1]) (.leaf ![0, 3, 0, 1])) (.branch 13 (.leaf ![0, 1, 0, 3]) (.leaf ![3, 3, 0, 1]))))) (.branch 21 (.branch 17 (.branch 15 (.leaf ![1, 3, 0, 1]) (.branch 16 (.leaf ![0, 1, 0, 3]) (.leaf ![1, 3, 0, 1]))) (.branch 19 (.branch 18 (.leaf ![3, 3, 0, 1]) (.leaf ![0, 3, 0, 1])) (.branch 20 (.leaf ![0, 3, 0, 1]) (.leaf ![0, 30, 0, 29])))) (.branch 24 (.branch 22 (.leaf ![29, 29, 0, 4]) (.branch 23 (.leaf ![4, 26, 0, 4]) (.leaf ![0, 32, 0, 27]))) (.branch 26 (.branch 25 (.leaf ![14, 2, 0, 14]) (.leaf ![27, 27, 0, 14])) (.branch 27 (.leaf ![0, 26, 0, 30]) (.leaf ![0, 2, 0, 32]))))))
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
@[expose] public def words : Fin 33 → List (Fin 4) := fun j =>
  ((.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf []) (.leaf [0])) (.branch 3 (.leaf [1]) (.leaf [2]))) (.branch 6 (.branch 5 (.leaf [3]) (.leaf [0, 1])) (.branch 7 (.leaf [0, 3]) (.leaf [1, 0])))) (.branch 12 (.branch 10 (.branch 9 (.leaf [1, 1]) (.leaf [1, 2])) (.branch 11 (.leaf [2, 1]) (.leaf [2, 3]))) (.branch 14 (.branch 13 (.leaf [3, 0]) (.leaf [3, 2])) (.branch 15 (.leaf [0, 1, 0]) (.leaf [0, 1, 1]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf [0, 1, 2]) (.leaf [0, 3, 0])) (.branch 19 (.leaf [0, 3, 2]) (.leaf [1, 0, 3]))) (.branch 22 (.branch 21 (.leaf [1, 1, 0]) (.leaf [1, 2, 1])) (.branch 23 (.leaf [1, 2, 3]) (.leaf [2, 1, 0])))) (.branch 28 (.branch 26 (.branch 25 (.leaf [2, 1, 2]) (.leaf [2, 3, 0])) (.branch 27 (.leaf [2, 3, 2]) (.leaf [0, 1, 0, 3]))) (.branch 30 (.branch 29 (.leaf [0, 1, 2, 1]) (.leaf [0, 1, 2, 3])) (.branch 31 (.leaf [1, 0, 3, 2]) (.branch 32 (.leaf [1, 2, 1, 0]) (.leaf [1, 2, 3, 2]))))))) : Lean.RArray (List (Fin 4))).get j.val
@[expose] public def wordCodes : Fin 33 → MatrixCode := fun j =>
  ((.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 6643) (.leaf 6697)) (.branch 3 (.leaf 4186) (.leaf 6670))) (.branch 6 (.branch 5 (.leaf 6103) (.leaf 4159)) (.branch 7 (.leaf 6076) (.leaf 3457)))) (.branch 12 (.branch 10 (.branch 9 (.leaf 14014) (.leaf 2728)) (.branch 11 (.leaf 4132) (.leaf 6130))) (.branch 14 (.branch 13 (.leaf 4645) (.leaf 5374)) (.branch 15 (.leaf 3430) (.leaf 14068))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf 2701) (.leaf 4618)) (.branch 19 (.leaf 5347) (.leaf 8101))) (.branch 22 (.branch 21 (.leaf 14041) (.leaf 14743)) (.branch 23 (.leaf 7372) (.leaf 3403)))) (.branch 28 (.branch 26 (.branch 25 (.leaf 2674) (.leaf 4672)) (.branch 27 (.leaf 5401) (.leaf 8155))) (.branch 30 (.branch 29 (.leaf 14797) (.leaf 7426)) (.branch 31 (.leaf 8128) (.branch 32 (.leaf 14770) (.leaf 7399))))))) : Lean.RArray MatrixCode).get j.val
set_option maxHeartbeats 4000000 in
public theorem wordEval : ∀ j, (evalWord (nodeGenerator 29) (words j)).val =
    decodeMatrix (wordCodes j) := by decide +kernel
@[expose] public def next : Fin 156 → Fin 4 → Fin 156 := fun j =>
  ((.branch 2 (.branch 1 (.leaf nextBlock0) (.leaf nextBlock1)) (.branch 3 (.leaf nextBlock2) (.branch 4 (.leaf nextBlock3) (.leaf nextBlock4)))) : Lean.RArray (Lean.RArray (Fin 4 → Fin 156))).get (j.val / 32) |>.get (j.val % 32)
@[expose] public def factorIndex : Fin 156 → Fin 4 → Fin 33 := fun j =>
  ((.branch 2 (.branch 1 (.leaf factorBlock0) (.leaf factorBlock1)) (.branch 3 (.leaf factorBlock2) (.branch 4 (.leaf factorBlock3) (.leaf factorBlock4)))) : Lean.RArray (Lean.RArray (Fin 4 → Fin 33))).get (j.val / 32) |>.get (j.val % 32)
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
public theorem valid : table.Valid ambientGenerator (nodeGenerator 29) rep := by
  constructor
  · decide +kernel
  · intro j k
    apply Subtype.ext
    change (rep j).val * (ambientGenerator k).val =
      (evalWord (nodeGenerator 29) (words (factorIndex j k))).val * (rep (next j k)).val
    rw [wordEval]
    exact transitions j k
public theorem cover : RightCosetCover (properNode 29) rep := by
  rw [properNode_eq_wordSubgroup]
  exact table.sound ambientGenerator ambientInverse ambientGenerator_inv
    ambient_wordSubgroup_eq_top (nodeGenerator 29) (symmInv (n := (generatorCodes 29).length))
    (nodeGenerator_inv 29) rep valid
end Matrix.PSL3Three.CertifiedEnumeration.Cosets29
