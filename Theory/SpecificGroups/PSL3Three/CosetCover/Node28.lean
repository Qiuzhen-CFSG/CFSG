module
public import Theory.SpecificGroups.PSL3Three.CosetCover.Check
/-!
# Checked right cosets for node 28

These are untrusted matrix codes and subgroup words generated from the fixed
lists in `RepresentativeBounds`. The kernel checks determinants, word values,
and every transition by the four ambient generators. `cover` then follows from
`RightCosetTable.sound`, using the proved generation of the actual SL₃(3).

Source: the elementary coset-table argument in `SubgroupEnumeration` and
GLS III, Theorem 6.5.3. Row zero represents the identity matrix.
-/

namespace Matrix.PSL3Three.CertifiedEnumeration.Cosets28
open Theory.GroupTheory Theory.GroupTheory.SubgroupEnumeration CosetCheck
set_option maxRecDepth 100000

@[expose] public def codeBlock0 : Lean.RArray (MatrixCode) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 6643) (.leaf 828)) (.branch 3 (.leaf 855) (.leaf 882))) (.branch 6 (.branch 5 (.leaf 900) (.leaf 927)) (.branch 7 (.leaf 954) (.leaf 975)))) (.branch 12 (.branch 10 (.branch 9 (.leaf 1002) (.leaf 1029)) (.branch 11 (.leaf 1056) (.leaf 1083))) (.branch 14 (.branch 13 (.leaf 1110) (.leaf 1137)) (.branch 15 (.leaf 1164) (.leaf 1191))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf 1221) (.leaf 1248)) (.branch 19 (.leaf 1275) (.leaf 1302))) (.branch 22 (.branch 21 (.leaf 1329) (.leaf 1356)) (.branch 23 (.leaf 1383) (.leaf 1410)))) (.branch 28 (.branch 26 (.branch 25 (.leaf 1437) (.leaf 2304)) (.branch 27 (.leaf 2340) (.leaf 2385))) (.branch 30 (.branch 29 (.leaf 2421) (.leaf 2432)) (.branch 31 (.leaf 2459) (.leaf 2486))))))

@[expose] public def codeBlock1 : Lean.RArray (MatrixCode) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 2513) (.leaf 2540)) (.branch 3 (.leaf 2567) (.leaf 2594))) (.branch 6 (.branch 5 (.leaf 2621) (.leaf 2648)) (.branch 7 (.leaf 2701) (.leaf 2728)))) (.branch 12 (.branch 10 (.branch 9 (.leaf 2755) (.leaf 2782)) (.branch 11 (.leaf 2809) (.leaf 2836))) (.branch 14 (.branch 13 (.leaf 2863) (.leaf 2890)) (.branch 15 (.leaf 3060) (.leaf 3123))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf 3161) (.leaf 3188)) (.branch 19 (.leaf 3215) (.leaf 3242))) (.branch 22 (.branch 21 (.leaf 3269) (.leaf 3296)) (.branch 23 (.leaf 3323) (.leaf 3350)))) (.branch 28 (.branch 26 (.branch 25 (.leaf 3377) (.leaf 3403)) (.branch 27 (.leaf 3430) (.leaf 3457))) (.branch 30 (.branch 29 (.leaf 3484) (.leaf 3511)) (.branch 31 (.leaf 3538) (.leaf 3565))))))

@[expose] public def codeBlock2 : Lean.RArray (MatrixCode) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 3592) (.leaf 3619)) (.branch 3 (.leaf 3890) (.leaf 3917))) (.branch 6 (.branch 5 (.leaf 3944) (.leaf 3971)) (.branch 7 (.leaf 3998) (.leaf 4025)))) (.branch 12 (.branch 10 (.branch 9 (.leaf 4052) (.leaf 4079)) (.branch 11 (.leaf 4106) (.leaf 4132))) (.branch 14 (.branch 13 (.leaf 4159) (.leaf 4186)) (.branch 15 (.leaf 4213) (.leaf 4240))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf 4267) (.leaf 4294)) (.branch 19 (.leaf 4321) (.leaf 4348))) (.branch 22 (.branch 21 (.leaf 6837) (.leaf 6861)) (.branch 23 (.leaf 6886) (.leaf 6913)))) (.branch 28 (.branch 26 (.branch 25 (.leaf 6940) (.leaf 6968)) (.branch 27 (.leaf 6995) (.leaf 7022))) (.branch 30 (.branch 29 (.leaf 7080) (.leaf 7104)) (.branch 31 (.leaf 7129) (.leaf 7156))))))

@[expose] public def codeBlock3 : Lean.RArray (MatrixCode) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 7183) (.leaf 7211)) (.branch 3 (.leaf 7238) (.leaf 7265))) (.branch 6 (.branch 5 (.leaf 7593) (.leaf 7615)) (.branch 7 (.leaf 7642) (.leaf 7669)))) (.branch 12 (.branch 10 (.branch 9 (.leaf 7697) (.leaf 7724)) (.branch 11 (.leaf 7751) (.leaf 7806))) (.branch 14 (.branch 13 (.leaf 7858) (.leaf 7885)) (.branch 15 (.leaf 7912) (.leaf 7940))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf 7967) (.leaf 7994)) (.branch 19 (.leaf 8344) (.leaf 8371))) (.branch 22 (.branch 21 (.leaf 8398) (.leaf 8426)) (.branch 23 (.leaf 8453) (.leaf 8480)))) (.branch 28 (.branch 26 (.branch 25 (.leaf 8587) (.leaf 8614)) (.branch 27 (.leaf 8641) (.leaf 8669))) (.branch 30 (.branch 29 (.leaf 8696) (.leaf 8723)) (.branch 31 (.leaf 9105) (.leaf 9129))))))

@[expose] public def codeBlock4 : Lean.RArray (MatrixCode) := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf 9154) (.branch 2 (.leaf 9181) (.leaf 9208))) (.branch 5 (.branch 4 (.leaf 9317) (.leaf 9344)) (.branch 6 (.leaf 9371) (.leaf 9429)))) (.branch 10 (.branch 8 (.leaf 9453) (.branch 9 (.leaf 9861) (.leaf 9883))) (.branch 12 (.branch 11 (.leaf 9910) (.leaf 9937)) (.branch 13 (.leaf 10046) (.leaf 10073))))) (.branch 21 (.branch 17 (.branch 15 (.leaf 10100) (.branch 16 (.leaf 10155) (.leaf 10612))) (.branch 19 (.branch 18 (.leaf 10639) (.leaf 10666)) (.branch 20 (.leaf 10775) (.leaf 10802)))) (.branch 24 (.branch 22 (.leaf 10829) (.branch 23 (.leaf 11373) (.leaf 11397))) (.branch 26 (.branch 25 (.leaf 11535) (.leaf 11559)) (.branch 27 (.leaf 12129) (.leaf 12261))))))

@[expose] public def nextBlock0 : Lean.RArray (Fin 4 → Fin 156) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![4, 0, 7, 0]) (.leaf ![16, 28, 29, 26])) (.branch 3 (.leaf ![84, 47, 32, 3]) (.leaf ![92, 2, 35, 47]))) (.branch 6 (.branch 5 (.leaf ![7, 25, 0, 27]) (.leaf ![85, 6, 40, 46])) (.branch 7 (.leaf ![93, 46, 43, 5]) (.leaf ![0, 48, 4, 75])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![86, 52, 25, 80]) (.leaf ![94, 56, 27, 82])) (.branch 11 (.leaf ![57, 51, 30, 81]) (.leaf ![87, 55, 33, 77]))) (.branch 14 (.branch 13 (.leaf ![95, 50, 36, 79]) (.leaf ![75, 54, 38, 78])) (.branch 15 (.leaf ![88, 49, 41, 83]) (.leaf ![96, 53, 44, 76]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![29, 57, 1, 66]) (.leaf ![89, 61, 26, 71])) (.branch 19 (.leaf ![97, 65, 28, 73]) (.leaf ![66, 60, 31, 72]))) (.branch 22 (.branch 21 (.leaf ![90, 64, 34, 68]) (.leaf ![98, 59, 37, 70])) (.branch 23 (.leaf ![48, 63, 39, 69]) (.leaf ![91, 58, 42, 74])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![99, 62, 45, 67]) (.leaf ![8, 27, 86, 4])) (.branch 27 (.leaf ![17, 1, 89, 28]) (.leaf ![9, 4, 94, 25]))) (.branch 30 (.branch 29 (.leaf ![18, 26, 97, 1]) (.leaf ![1, 29, 16, 29])) (.branch 31 (.leaf ![10, 33, 57, 36]) (.leaf ![19, 37, 66, 34]))))))

@[expose] public def nextBlock1 : Lean.RArray (Fin 4 → Fin 156) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![2, 32, 84, 32]) (.leaf ![11, 36, 87, 30])) (.branch 3 (.leaf ![20, 31, 90, 37]) (.leaf ![3, 35, 92, 35]))) (.branch 6 (.branch 5 (.leaf ![12, 30, 95, 33]) (.leaf ![21, 34, 98, 31])) (.branch 7 (.leaf ![13, 41, 75, 44]) (.leaf ![22, 45, 48, 42])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![5, 40, 85, 40]) (.leaf ![14, 44, 88, 38])) (.branch 11 (.leaf ![23, 39, 91, 45]) (.leaf ![6, 43, 93, 43]))) (.branch 14 (.branch 13 (.leaf ![15, 38, 96, 41]) (.leaf ![24, 42, 99, 39])) (.branch 15 (.leaf ![107, 5, 128, 6]) (.leaf ![100, 3, 131, 2]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![39, 75, 22, 7]) (.leaf ![101, 83, 63, 14])) (.branch 19 (.leaf ![108, 79, 69, 12]) (.leaf ![59, 81, 111, 10]))) (.branch 22 (.branch 21 (.leaf ![102, 80, 126, 8]) (.leaf ![109, 76, 129, 15])) (.branch 23 (.leaf ![77, 78, 114, 13]) (.leaf ![103, 77, 132, 11])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![110, 82, 134, 9]) (.leaf ![30, 66, 10, 16])) (.branch 27 (.leaf ![104, 74, 81, 23]) (.leaf ![111, 70, 51, 21]))) (.branch 30 (.branch 29 (.leaf ![67, 72, 123, 19]) (.leaf ![105, 71, 127, 17])) (.branch 31 (.leaf ![112, 67, 130, 24]) (.leaf ![49, 69, 101, 22]))))))

@[expose] public def nextBlock2 : Lean.RArray (Fin 4 → Fin 156) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![106, 68, 133, 20]) (.leaf ![113, 73, 135, 18])) (.branch 3 (.leaf ![31, 16, 19, 57]) (.leaf ![123, 24, 60, 62]))) (.branch 6 (.branch 5 (.leaf ![117, 20, 72, 64]) (.leaf ![50, 22, 108, 63])) (.branch 7 (.leaf ![125, 21, 140, 59]) (.leaf ![119, 17, 150, 61])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![68, 19, 117, 60]) (.leaf ![124, 18, 152, 65])) (.branch 11 (.leaf ![118, 23, 144, 58]) (.leaf ![38, 7, 13, 48]))) (.branch 14 (.branch 13 (.leaf ![120, 15, 78, 53]) (.leaf ![114, 11, 54, 55])) (.branch 15 (.leaf ![76, 13, 120, 54]) (.leaf ![122, 12, 147, 50]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![116, 8, 151, 52]) (.leaf ![58, 10, 104, 51])) (.branch 19 (.leaf ![121, 9, 153, 56]) (.leaf ![115, 14, 137, 49]))) (.branch 22 (.branch 21 (.leaf ![32, 87, 2, 90]) (.leaf ![40, 91, 5, 88])) (.branch 23 (.leaf ![25, 86, 8, 86]) (.leaf ![33, 90, 11, 84])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![41, 85, 14, 91]) (.leaf ![26, 89, 17, 89])) (.branch 27 (.leaf ![34, 84, 20, 87]) (.leaf ![42, 88, 23, 85]))) (.branch 30 (.branch 29 (.leaf ![35, 95, 3, 98]) (.leaf ![43, 99, 6, 96])) (.branch 31 (.leaf ![27, 94, 9, 94]) (.leaf ![36, 98, 12, 92]))))))

@[expose] public def nextBlock3 : Lean.RArray (Fin 4 → Fin 156) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![44, 93, 15, 99]) (.leaf ![28, 97, 18, 97])) (.branch 3 (.leaf ![37, 92, 21, 95]) (.leaf ![45, 96, 24, 93]))) (.branch 6 (.branch 5 (.leaf ![131, 139, 47, 149]) (.leaf ![63, 135, 49, 133])) (.branch 7 (.leaf ![126, 138, 52, 110]) (.leaf ![132, 125, 55, 154])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![81, 137, 58, 153]) (.leaf ![127, 113, 61, 142])) (.branch 11 (.leaf ![133, 136, 64, 122]) (.leaf ![128, 141, 46, 145]))) (.branch 14 (.branch 13 (.leaf ![69, 140, 50, 150]) (.leaf ![129, 143, 53, 118])) (.branch 15 (.leaf ![134, 102, 56, 138]) (.leaf ![51, 126, 59, 129]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![130, 115, 62, 155]) (.leaf ![135, 142, 65, 105])) (.branch 19 (.leaf ![54, 132, 77, 134]) (.leaf ![137, 155, 83, 112]))) (.branch 22 (.branch 21 (.leaf ![151, 121, 80, 146]) (.leaf ![72, 152, 68, 144])) (.branch 23 (.leaf ![144, 109, 74, 143]) (.leaf ![150, 148, 71, 124])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![78, 151, 76, 147]) (.leaf ![153, 146, 82, 116])) (.branch 27 (.leaf ![147, 106, 79, 136]) (.leaf ![60, 130, 67, 127]))) (.branch 30 (.branch 29 (.leaf ![152, 119, 73, 148]) (.leaf ![140, 154, 70, 103])) (.branch 31 (.leaf ![52, 129, 102, 111]) (.leaf ![61, 123, 105, 130]))))))

@[expose] public def nextBlock4 : Lean.RArray (Fin 4 → Fin 156) := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf ![46, 128, 107, 128]) (.branch 2 (.leaf ![53, 111, 109, 126]) (.leaf ![62, 127, 112, 123]))) (.branch 5 (.branch 4 (.leaf ![47, 131, 100, 131]) (.leaf ![55, 134, 103, 114])) (.branch 6 (.leaf ![64, 101, 106, 135]) (.leaf ![56, 114, 110, 132])))) (.branch 10 (.branch 8 (.leaf ![65, 133, 113, 101]) (.branch 9 (.leaf ![141, 122, 138, 106]) (.leaf ![83, 153, 115, 104]))) (.branch 12 (.branch 11 (.leaf ![136, 110, 141, 102]) (.leaf ![142, 149, 143, 100])) (.branch 13 (.leaf ![70, 150, 125, 108]) (.leaf ![138, 145, 136, 107]))))) (.branch 21 (.branch 17 (.branch 15 (.leaf ![143, 105, 139, 113]) (.branch 16 (.leaf ![139, 118, 142, 109]) (.leaf ![74, 117, 118, 152]))) (.branch 19 (.branch 18 (.leaf ![146, 107, 155, 141]) (.leaf ![155, 116, 145, 121])) (.branch 20 (.leaf ![79, 120, 122, 151]) (.leaf ![154, 124, 149, 119])))) (.branch 24 (.branch 22 (.leaf ![148, 100, 154, 139]) (.branch 23 (.leaf ![71, 108, 119, 140]) (.leaf ![80, 147, 116, 120]))) (.branch 26 (.branch 25 (.leaf ![73, 144, 124, 117]) (.leaf ![82, 104, 121, 137])) (.branch 27 (.leaf ![149, 103, 148, 125]) (.leaf ![145, 112, 146, 115]))))))

@[expose] public def factorBlock0 : Lean.RArray (Fin 4 → Fin 25) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![18, 12, 0, 11]) (.leaf ![18, 18, 0, 18])) (.branch 3 (.leaf ![0, 0, 0, 18]) (.leaf ![0, 13, 0, 13]))) (.branch 6 (.branch 5 (.leaf ![13, 13, 13, 13]) (.leaf ![0, 18, 0, 18])) (.branch 7 (.leaf ![0, 0, 0, 13]) (.leaf ![0, 1, 18, 21])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![0, 1, 0, 21]) (.leaf ![0, 1, 0, 21])) (.branch 11 (.leaf ![18, 1, 12, 21]) (.leaf ![0, 1, 24, 21]))) (.branch 14 (.branch 13 (.leaf ![0, 1, 23, 21]) (.leaf ![18, 1, 11, 21])) (.branch 15 (.leaf ![0, 1, 19, 21]) (.leaf ![0, 1, 20, 21]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![13, 2, 13, 22]) (.leaf ![0, 2, 0, 22])) (.branch 19 (.leaf ![0, 2, 0, 22]) (.leaf ![13, 2, 11, 22]))) (.branch 22 (.branch 21 (.leaf ![0, 2, 19, 22]) (.leaf ![0, 2, 20, 22])) (.branch 23 (.leaf ![13, 2, 12, 22]) (.leaf ![0, 2, 24, 22])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![0, 2, 23, 22]) (.leaf ![0, 0, 0, 18])) (.branch 27 (.leaf ![0, 13, 0, 0]) (.leaf ![0, 18, 0, 0]))) (.branch 30 (.branch 29 (.leaf ![0, 0, 0, 13]) (.leaf ![0, 2, 18, 1])) (.branch 31 (.leaf ![11, 2, 17, 1]) (.leaf ![12, 2, 5, 1]))))))

@[expose] public def factorBlock1 : Lean.RArray (Fin 4 → Fin 25) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![0, 2, 0, 1]) (.leaf ![19, 2, 19, 1])) (.branch 3 (.leaf ![24, 2, 24, 1]) (.leaf ![0, 2, 0, 1]))) (.branch 6 (.branch 5 (.leaf ![20, 2, 20, 1]) (.leaf ![23, 2, 23, 1])) (.branch 7 (.leaf ![12, 1, 10, 2]) (.leaf ![11, 1, 14, 2])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![0, 1, 0, 2]) (.leaf ![24, 1, 24, 2])) (.branch 11 (.leaf ![19, 1, 19, 2]) (.leaf ![0, 1, 0, 2]))) (.branch 14 (.branch 13 (.leaf ![23, 1, 23, 2]) (.leaf ![20, 1, 20, 2])) (.branch 15 (.leaf ![0, 13, 0, 0]) (.leaf ![0, 18, 0, 0]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![15, 22, 18, 2]) (.leaf ![2, 22, 17, 2])) (.branch 19 (.leaf ![2, 22, 5, 2]) (.leaf ![15, 22, 6, 2]))) (.branch 22 (.branch 21 (.leaf ![2, 22, 0, 2]) (.leaf ![2, 22, 19, 2])) (.branch 23 (.leaf ![15, 22, 4, 2]) (.leaf ![2, 22, 23, 2])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![2, 22, 0, 2]) (.leaf ![16, 21, 13, 1])) (.branch 27 (.leaf ![1, 21, 10, 1]) (.leaf ![1, 21, 14, 1]))) (.branch 30 (.branch 29 (.leaf ![16, 21, 7, 1]) (.leaf ![1, 21, 0, 1])) (.branch 31 (.leaf ![1, 21, 24, 1]) (.leaf ![16, 21, 9, 1]))))))

@[expose] public def factorBlock2 : Lean.RArray (Fin 4 → Fin 25) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![1, 21, 20, 1]) (.leaf ![1, 21, 0, 1])) (.branch 3 (.leaf ![8, 22, 18, 21]) (.leaf ![22, 22, 17, 21]))) (.branch 6 (.branch 5 (.leaf ![22, 22, 5, 21]) (.leaf ![8, 22, 7, 21])) (.branch 7 (.leaf ![22, 22, 6, 21]) (.leaf ![22, 22, 0, 21])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![8, 22, 9, 21]) (.leaf ![22, 22, 0, 21])) (.branch 11 (.leaf ![22, 22, 4, 21]) (.leaf ![3, 21, 13, 22]))) (.branch 14 (.branch 13 (.leaf ![21, 21, 10, 22]) (.leaf ![21, 21, 14, 22])) (.branch 15 (.leaf ![3, 21, 6, 22]) (.leaf ![21, 21, 7, 22]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![21, 21, 0, 22]) (.leaf ![3, 21, 4, 22])) (.branch 19 (.leaf ![21, 21, 0, 22]) (.leaf ![21, 21, 9, 22]))) (.branch 22 (.branch 21 (.leaf ![0, 19, 0, 24]) (.leaf ![0, 19, 0, 24])) (.branch 23 (.leaf ![0, 24, 0, 19]) (.leaf ![24, 19, 0, 24])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![19, 19, 0, 24]) (.leaf ![0, 24, 0, 19])) (.branch 27 (.leaf ![19, 19, 0, 24]) (.leaf ![24, 19, 0, 24]))) (.branch 30 (.branch 29 (.leaf ![0, 20, 0, 23]) (.leaf ![0, 20, 0, 23])) (.branch 31 (.leaf ![0, 23, 0, 20]) (.leaf ![23, 20, 0, 23]))))))

@[expose] public def factorBlock3 : Lean.RArray (Fin 4 → Fin 25) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![20, 20, 0, 23]) (.leaf ![0, 23, 0, 20])) (.branch 3 (.leaf ![20, 20, 0, 23]) (.leaf ![23, 20, 0, 23]))) (.branch 6 (.branch 5 (.leaf ![0, 19, 0, 6]) (.leaf ![7, 7, 1, 6])) (.branch 7 (.leaf ![1, 24, 1, 7]) (.leaf ![24, 7, 1, 24])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![6, 19, 2, 6]) (.leaf ![2, 6, 2, 7])) (.branch 11 (.leaf ![19, 19, 2, 6]) (.leaf ![0, 20, 0, 9]))) (.branch 14 (.branch 13 (.leaf ![9, 20, 1, 9]) (.leaf ![20, 20, 1, 9])) (.branch 15 (.leaf ![1, 9, 1, 4]) (.leaf ![4, 4, 2, 9]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![23, 4, 2, 23]) (.leaf ![2, 23, 2, 4])) (.branch 19 (.leaf ![6, 7, 21, 6]) (.leaf ![7, 7, 21, 6]))) (.branch 22 (.branch 21 (.leaf ![21, 6, 21, 19]) (.leaf ![7, 7, 22, 24])) (.branch 23 (.leaf ![6, 7, 22, 6]) (.leaf ![22, 6, 22, 7])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![4, 4, 21, 23]) (.leaf ![21, 9, 21, 4])) (.branch 27 (.leaf ![9, 4, 21, 9]) (.leaf ![9, 4, 22, 9]))) (.branch 30 (.branch 29 (.leaf ![22, 9, 22, 20]) (.leaf ![4, 4, 22, 9])) (.branch 31 (.leaf ![0, 19, 2, 6]) (.leaf ![0, 7, 1, 24]))))))

@[expose] public def factorBlock4 : Lean.RArray (Fin 4 → Fin 25) := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf ![0, 24, 0, 19]) (.branch 2 (.leaf ![24, 7, 23, 24]) (.leaf ![19, 19, 20, 6]))) (.branch 5 (.branch 4 (.leaf ![0, 23, 0, 20]) (.leaf ![20, 20, 19, 9])) (.branch 6 (.leaf ![23, 4, 24, 23]) (.leaf ![0, 4, 2, 23])))) (.branch 10 (.branch 8 (.leaf ![0, 20, 1, 9]) (.branch 9 (.leaf ![0, 7, 23, 24]) (.leaf ![7, 7, 9, 24]))) (.branch 12 (.branch 11 (.leaf ![20, 6, 20, 19]) (.leaf ![24, 7, 0, 24])) (.branch 13 (.leaf ![4, 4, 6, 23]) (.leaf ![23, 4, 0, 23]))))) (.branch 21 (.branch 17 (.branch 15 (.leaf ![19, 9, 19, 20]) (.branch 16 (.leaf ![0, 4, 24, 23]) (.leaf ![6, 19, 4, 6]))) (.branch 19 (.branch 18 (.leaf ![7, 7, 0, 6]) (.leaf ![9, 24, 9, 7])) (.branch 20 (.leaf ![9, 20, 7, 9]) (.leaf ![6, 23, 6, 4])))) (.branch 24 (.branch 22 (.leaf ![4, 4, 0, 9]) (.branch 23 (.leaf ![0, 7, 22, 6]) (.leaf ![0, 7, 21, 6]))) (.branch 26 (.branch 25 (.leaf ![0, 4, 22, 9]) (.leaf ![0, 4, 21, 9])) (.branch 27 (.leaf ![0, 19, 4, 6]) (.leaf ![0, 20, 7, 9]))))))
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
@[expose] public def words : Fin 25 → List (Fin 4) := fun j =>
  ((.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf []) (.branch 2 (.leaf [1]) (.leaf [3]))) (.branch 4 (.leaf [0, 1]) (.branch 5 (.leaf [0, 3]) (.leaf [1, 0])))) (.branch 9 (.branch 7 (.leaf [1, 2]) (.branch 8 (.leaf [2, 1]) (.leaf [2, 3]))) (.branch 10 (.leaf [3, 0]) (.branch 11 (.leaf [3, 2]) (.leaf [0, 1, 2]))))) (.branch 18 (.branch 15 (.branch 13 (.leaf [0, 3, 2]) (.branch 14 (.leaf [1, 0, 1]) (.leaf [1, 0, 3]))) (.branch 16 (.leaf [1, 2, 3]) (.branch 17 (.leaf [3, 0, 1]) (.leaf [3, 2, 1])))) (.branch 21 (.branch 19 (.leaf [3, 2, 3]) (.branch 20 (.leaf [0, 1, 2, 1]) (.leaf [0, 1, 2, 3]))) (.branch 23 (.branch 22 (.leaf [0, 3, 0, 1]) (.leaf [0, 3, 0, 3])) (.branch 24 (.leaf [0, 3, 2, 1]) (.leaf [0, 3, 2, 3])))))) : Lean.RArray (List (Fin 4))).get j.val
@[expose] public def wordCodes : Fin 25 → MatrixCode := fun j =>
  ((.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf 6643) (.branch 2 (.leaf 6652) (.leaf 6661))) (.branch 4 (.leaf 2680) (.branch 5 (.leaf 2689) (.leaf 2692)))) (.branch 9 (.branch 7 (.leaf 4630) (.branch 8 (.leaf 4642) (.leaf 4624))) (.branch 10 (.leaf 2695) (.branch 11 (.leaf 4627) (.leaf 6649))))) (.branch 18 (.branch 15 (.branch 13 (.leaf 6646) (.branch 14 (.leaf 2674) (.leaf 2683))) (.branch 16 (.leaf 4621) (.branch 17 (.leaf 2677) (.leaf 4636)))) (.branch 21 (.branch 19 (.leaf 4618) (.branch 20 (.leaf 6658) (.leaf 6667))) (.branch 23 (.branch 22 (.leaf 13294) (.leaf 13303)) (.branch 24 (.leaf 6655) (.leaf 6664)))))) : Lean.RArray MatrixCode).get j.val
set_option maxHeartbeats 4000000 in
public theorem wordEval : ∀ j, (evalWord (nodeGenerator 28) (words j)).val =
    decodeMatrix (wordCodes j) := by decide +kernel
@[expose] public def next : Fin 156 → Fin 4 → Fin 156 := fun j =>
  ((.branch 2 (.branch 1 (.leaf nextBlock0) (.leaf nextBlock1)) (.branch 3 (.leaf nextBlock2) (.branch 4 (.leaf nextBlock3) (.leaf nextBlock4)))) : Lean.RArray (Lean.RArray (Fin 4 → Fin 156))).get (j.val / 32) |>.get (j.val % 32)
@[expose] public def factorIndex : Fin 156 → Fin 4 → Fin 25 := fun j =>
  ((.branch 2 (.branch 1 (.leaf factorBlock0) (.leaf factorBlock1)) (.branch 3 (.leaf factorBlock2) (.branch 4 (.leaf factorBlock3) (.leaf factorBlock4)))) : Lean.RArray (Lean.RArray (Fin 4 → Fin 25))).get (j.val / 32) |>.get (j.val % 32)
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
public theorem valid : table.Valid ambientGenerator (nodeGenerator 28) rep := by
  constructor
  · decide +kernel
  · intro j k
    apply Subtype.ext
    change (rep j).val * (ambientGenerator k).val =
      (evalWord (nodeGenerator 28) (words (factorIndex j k))).val * (rep (next j k)).val
    rw [wordEval]
    exact transitions j k
public theorem cover : RightCosetCover (properNode 28) rep := by
  rw [properNode_eq_wordSubgroup]
  exact table.sound ambientGenerator ambientInverse ambientGenerator_inv
    ambient_wordSubgroup_eq_top (nodeGenerator 28) (symmInv (n := (generatorCodes 28).length))
    (nodeGenerator_inv 28) rep valid
end Matrix.PSL3Three.CertifiedEnumeration.Cosets28
