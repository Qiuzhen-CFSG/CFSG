module
public import Theory.SpecificGroups.PSL3Three.CosetCover.Check
/-!
# Checked right cosets for node 30

These are untrusted matrix codes and subgroup words generated from the fixed
lists in `RepresentativeBounds`. The kernel checks determinants, word values,
and every transition by the four ambient generators. `cover` then follows from
`RightCosetTable.sound`, using the proved generation of the actual SL₃(3).

Source: the elementary coset-table argument in `SubgroupEnumeration` and
GLS III, Theorem 6.5.3. Row zero represents the identity matrix.
-/

namespace Matrix.PSL3Three.CertifiedEnumeration.Cosets30
open Theory.GroupTheory Theory.GroupTheory.SubgroupEnumeration CosetCheck
set_option maxRecDepth 100000

@[expose] public def codeBlock0 : Lean.RArray (MatrixCode) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 6643) (.leaf 828)) (.branch 3 (.leaf 855) (.leaf 882))) (.branch 6 (.branch 5 (.leaf 975) (.leaf 1002)) (.branch 7 (.leaf 1029) (.leaf 1056)))) (.branch 12 (.branch 10 (.branch 9 (.leaf 1083) (.leaf 1110)) (.branch 11 (.leaf 1137) (.leaf 1164))) (.branch 14 (.branch 13 (.leaf 1191) (.leaf 2223)) (.branch 15 (.leaf 2304) (.leaf 2340))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf 2432) (.leaf 2459)) (.branch 19 (.leaf 2486) (.leaf 2513))) (.branch 22 (.branch 21 (.leaf 2540) (.leaf 2567)) (.branch 23 (.leaf 2594) (.leaf 2621)))) (.branch 28 (.branch 26 (.branch 25 (.leaf 2648) (.leaf 2952)) (.branch 27 (.leaf 3015) (.leaf 3060))) (.branch 30 (.branch 29 (.leaf 3161) (.leaf 3188)) (.branch 31 (.leaf 3215) (.leaf 3242))))))

@[expose] public def codeBlock1 : Lean.RArray (MatrixCode) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 3269) (.leaf 3296)) (.branch 3 (.leaf 3323) (.leaf 3350))) (.branch 6 (.branch 5 (.leaf 3377) (.leaf 3681)) (.branch 7 (.leaf 3735) (.leaf 3771)))) (.branch 12 (.branch 10 (.branch 9 (.leaf 3890) (.leaf 3917)) (.branch 11 (.leaf 3944) (.leaf 3971))) (.branch 14 (.branch 13 (.leaf 3998) (.leaf 4025)) (.branch 15 (.leaf 4052) (.leaf 4079))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf 4106) (.leaf 6594)) (.branch 19 (.leaf 6670) (.leaf 6697))) (.branch 22 (.branch 21 (.leaf 6837) (.leaf 6861)) (.branch 23 (.leaf 6886) (.leaf 6913)))) (.branch 28 (.branch 26 (.branch 25 (.leaf 6940) (.leaf 6968)) (.branch 27 (.leaf 6995) (.leaf 7022))) (.branch 30 (.branch 29 (.leaf 7323) (.leaf 7372)) (.branch 31 (.leaf 7399) (.leaf 7426))))))

@[expose] public def codeBlock2 : Lean.RArray (MatrixCode) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 7536) (.leaf 7593)) (.branch 3 (.leaf 7615) (.leaf 7642))) (.branch 6 (.branch 5 (.leaf 7669) (.leaf 7697)) (.branch 7 (.leaf 7724) (.leaf 7751)))) (.branch 12 (.branch 10 (.branch 9 (.leaf 8052) (.leaf 8101)) (.branch 11 (.leaf 8128) (.leaf 8155))) (.branch 14 (.branch 13 (.leaf 8268) (.leaf 8292)) (.branch 15 (.leaf 8344) (.leaf 8371))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf 8398) (.leaf 8426)) (.branch 19 (.leaf 8453) (.leaf 8480))) (.branch 22 (.branch 21 (.leaf 8781) (.leaf 8830)) (.branch 23 (.leaf 8857) (.leaf 8884)))) (.branch 28 (.branch 26 (.branch 25 (.leaf 8993) (.leaf 9020)) (.branch 27 (.leaf 9047) (.leaf 9105))) (.branch 30 (.branch 29 (.leaf 9129) (.leaf 9154)) (.branch 31 (.leaf 9181) (.leaf 9208))))))

@[expose] public def codeBlock3 : Lean.RArray (MatrixCode) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 9510) (.leaf 9559)) (.branch 3 (.leaf 9586) (.leaf 9613))) (.branch 6 (.branch 5 (.leaf 9722) (.leaf 9749)) (.branch 7 (.leaf 9776) (.leaf 9804)))) (.branch 12 (.branch 10 (.branch 9 (.leaf 9861) (.leaf 9883)) (.branch 11 (.leaf 9910) (.leaf 9937))) (.branch 14 (.branch 13 (.leaf 10239) (.leaf 10288)) (.branch 15 (.leaf 10315) (.leaf 10342))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf 10451) (.leaf 10478)) (.branch 19 (.leaf 10505) (.leaf 10536))) (.branch 22 (.branch 21 (.leaf 10560) (.leaf 10612)) (.branch 23 (.leaf 10639) (.leaf 10666)))) (.branch 28 (.branch 26 (.branch 25 (.leaf 10968) (.leaf 11017)) (.branch 27 (.leaf 11044) (.leaf 11071))) (.branch 30 (.branch 29 (.leaf 11179) (.leaf 11206)) (.branch 31 (.leaf 11233) (.leaf 11261))))))

@[expose] public def codeBlock4 : Lean.RArray (MatrixCode) := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf 11288) (.branch 2 (.leaf 11315) (.leaf 11373))) (.branch 5 (.branch 4 (.leaf 11397) (.leaf 11697)) (.branch 6 (.leaf 11746) (.leaf 11773)))) (.branch 10 (.branch 8 (.leaf 11800) (.branch 9 (.leaf 11908) (.leaf 11935))) (.branch 12 (.branch 11 (.leaf 11962) (.leaf 11990)) (.branch 13 (.leaf 12017) (.leaf 12044))))) (.branch 21 (.branch 17 (.branch 15 (.leaf 12072) (.branch 16 (.leaf 12129) (.leaf 12426))) (.branch 19 (.branch 18 (.leaf 12475) (.leaf 12502)) (.branch 20 (.leaf 12529) (.leaf 12637)))) (.branch 24 (.branch 22 (.leaf 12664) (.branch 23 (.leaf 12691) (.leaf 12719))) (.branch 26 (.branch 25 (.leaf 12746) (.leaf 12773)) (.branch 27 (.leaf 12804) (.leaf 12828))))))

@[expose] public def nextBlock0 : Lean.RArray (Fin 4 → Fin 156) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![13, 0, 4, 0]) (.leaf ![49, 26, 16, 38])) (.branch 3 (.leaf ![52, 27, 19, 37]) (.leaf ![53, 25, 22, 39]))) (.branch 6 (.branch 5 (.leaf ![0, 28, 13, 40]) (.leaf ![54, 32, 14, 47])) (.branch 7 (.leaf ![57, 36, 15, 45]) (.leaf ![50, 31, 17, 43])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![55, 35, 20, 41]) (.leaf ![59, 30, 23, 48])) (.branch 11 (.leaf ![51, 34, 18, 46]) (.leaf ![56, 29, 24, 44]))) (.branch 14 (.branch 13 (.leaf ![58, 33, 21, 42]) (.leaf ![4, 14, 0, 15])) (.branch 15 (.leaf ![5, 15, 54, 13]) (.leaf ![6, 13, 57, 14]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![1, 16, 49, 16]) (.leaf ![7, 20, 50, 23])) (.branch 19 (.leaf ![10, 24, 51, 21]) (.leaf ![2, 19, 52, 19]))) (.branch 22 (.branch 21 (.leaf ![8, 23, 55, 17]) (.leaf ![12, 18, 58, 24])) (.branch 23 (.leaf ![3, 22, 53, 22]) (.leaf ![9, 17, 59, 20])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![11, 21, 56, 18]) (.leaf ![64, 39, 85, 3])) (.branch 27 (.leaf ![60, 38, 88, 1]) (.leaf ![65, 37, 93, 2]))) (.branch 30 (.branch 29 (.leaf ![61, 40, 84, 4]) (.leaf ![66, 44, 86, 11])) (.branch 31 (.leaf ![69, 48, 87, 9]) (.leaf ![62, 43, 89, 7]))))))

@[expose] public def nextBlock1 : Lean.RArray (Fin 4 → Fin 156) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![67, 47, 91, 5]) (.leaf ![71, 42, 94, 12])) (.branch 3 (.leaf ![63, 46, 90, 10]) (.leaf ![68, 41, 95, 8]))) (.branch 6 (.branch 5 (.leaf ![70, 45, 92, 6]) (.leaf ![76, 2, 121, 27])) (.branch 7 (.leaf ![72, 1, 124, 26]) (.leaf ![77, 3, 127, 25])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![73, 4, 120, 28]) (.leaf ![78, 8, 122, 35])) (.branch 11 (.leaf ![81, 12, 123, 33]) (.leaf ![74, 7, 125, 31]))) (.branch 14 (.branch 13 (.leaf ![79, 11, 128, 29]) (.leaf ![83, 6, 130, 36])) (.branch 15 (.leaf ![75, 10, 126, 34]) (.leaf ![80, 5, 131, 32]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![82, 9, 129, 30]) (.leaf ![16, 50, 1, 51])) (.branch 19 (.leaf ![17, 51, 7, 49]) (.leaf ![18, 49, 10, 50]))) (.branch 22 (.branch 21 (.leaf ![19, 55, 2, 58]) (.leaf ![22, 59, 3, 56])) (.branch 23 (.leaf ![14, 54, 5, 54]) (.leaf ![20, 58, 8, 52])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![24, 53, 11, 59]) (.leaf ![15, 57, 6, 57])) (.branch 27 (.leaf ![21, 52, 12, 55]) (.leaf ![23, 56, 9, 53]))) (.branch 30 (.branch 29 (.leaf ![88, 98, 26, 135]) (.leaf ![84, 97, 28, 133])) (.branch 31 (.leaf ![89, 99, 31, 132]) (.leaf ![90, 96, 34, 134]))))))

@[expose] public def nextBlock2 : Lean.RArray (Fin 4 → Fin 156) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![85, 100, 25, 136]) (.leaf ![93, 107, 27, 141])) (.branch 3 (.leaf ![86, 103, 29, 139]) (.leaf ![91, 106, 32, 137]))) (.branch 6 (.branch 5 (.leaf ![95, 102, 35, 143]) (.leaf ![87, 105, 30, 142])) (.branch 7 (.leaf ![92, 101, 36, 140]) (.leaf ![94, 104, 33, 138])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![124, 146, 38, 111]) (.leaf ![120, 145, 40, 109])) (.branch 11 (.leaf ![125, 147, 43, 108]) (.leaf ![126, 144, 46, 110]))) (.branch 14 (.branch 13 (.leaf ![121, 148, 37, 112]) (.leaf ![127, 152, 39, 118])) (.branch 15 (.leaf ![122, 151, 41, 115]) (.leaf ![128, 155, 44, 113]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![131, 150, 47, 119]) (.leaf ![123, 154, 42, 117])) (.branch 19 (.leaf ![129, 149, 48, 116]) (.leaf ![130, 153, 45, 114]))) (.branch 22 (.branch 21 (.leaf ![28, 86, 61, 87]) (.leaf ![25, 85, 64, 85])) (.branch 23 (.leaf ![29, 87, 66, 84]) (.leaf ![30, 84, 69, 86])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![26, 88, 60, 88]) (.leaf ![31, 91, 62, 94])) (.branch 27 (.leaf ![34, 95, 63, 92]) (.leaf ![32, 94, 67, 89]))) (.branch 30 (.branch 29 (.leaf ![36, 90, 70, 95]) (.leaf ![27, 93, 65, 93])) (.branch 31 (.leaf ![33, 89, 71, 91]) (.leaf ![35, 92, 68, 90]))))))

@[expose] public def nextBlock3 : Lean.RArray (Fin 4 → Fin 156) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![100, 134, 97, 63]) (.leaf ![96, 133, 100, 61])) (.branch 3 (.leaf ![101, 135, 103, 60]) (.leaf ![102, 132, 105, 62]))) (.branch 6 (.branch 5 (.leaf ![97, 136, 96, 64]) (.leaf ![103, 140, 98, 70])) (.branch 7 (.leaf ![105, 143, 99, 68]) (.leaf ![98, 139, 101, 66])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![107, 138, 106, 71]) (.leaf ![99, 142, 102, 69])) (.branch 11 (.leaf ![104, 137, 107, 67]) (.leaf ![106, 141, 104, 65]))) (.branch 14 (.branch 13 (.leaf ![148, 74, 133, 147]) (.leaf ![144, 73, 136, 145])) (.branch 15 (.leaf ![149, 75, 139, 144]) (.leaf ![150, 72, 142, 146]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![145, 76, 132, 148]) (.leaf ![151, 79, 134, 155])) (.branch 19 (.leaf ![154, 83, 135, 153]) (.leaf ![146, 78, 137, 151]))) (.branch 22 (.branch 21 (.leaf ![152, 82, 140, 149]) (.leaf ![147, 81, 138, 154])) (.branch 23 (.leaf ![153, 77, 143, 152]) (.leaf ![155, 80, 141, 150])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![40, 122, 73, 123]) (.leaf ![37, 121, 76, 121])) (.branch 27 (.leaf ![41, 123, 78, 120]) (.leaf ![42, 120, 81, 122]))) (.branch 30 (.branch 29 (.leaf ![38, 124, 72, 124]) (.leaf ![43, 128, 74, 130])) (.branch 31 (.leaf ![46, 131, 75, 129]) (.leaf ![39, 127, 77, 127]))))))

@[expose] public def nextBlock4 : Lean.RArray (Fin 4 → Fin 156) := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf ![44, 130, 79, 125]) (.branch 2 (.leaf ![48, 126, 82, 131]) (.leaf ![45, 125, 83, 128]))) (.branch 5 (.branch 4 (.leaf ![47, 129, 80, 126]) (.leaf ![112, 62, 145, 99])) (.branch 6 (.leaf ![108, 61, 148, 97]) (.leaf ![113, 63, 151, 96])))) (.branch 10 (.branch 8 (.leaf ![114, 60, 154, 98]) (.branch 9 (.leaf ![109, 64, 144, 100]) (.leaf ![115, 67, 146, 106]))) (.branch 12 (.branch 11 (.leaf ![117, 71, 147, 104]) (.leaf ![110, 66, 149, 103])) (.branch 13 (.leaf ![116, 70, 152, 101]) (.leaf ![119, 65, 155, 107]))))) (.branch 21 (.branch 17 (.branch 15 (.leaf ![111, 69, 150, 105]) (.branch 16 (.leaf ![118, 68, 153, 102]) (.leaf ![136, 110, 109, 75]))) (.branch 19 (.branch 18 (.leaf ![132, 109, 112, 73]) (.leaf ![137, 111, 115, 72])) (.branch 20 (.leaf ![138, 108, 117, 74]) (.leaf ![133, 112, 108, 76])))) (.branch 24 (.branch 22 (.leaf ![139, 116, 110, 82]) (.branch 23 (.leaf ![142, 119, 111, 80]) (.leaf ![134, 115, 113, 78]))) (.branch 26 (.branch 25 (.leaf ![140, 118, 116, 77]) (.leaf ![143, 114, 118, 83])) (.branch 27 (.leaf ![135, 117, 114, 81]) (.leaf ![141, 113, 119, 79]))))))

@[expose] public def factorBlock0 : Lean.RArray (Fin 4 → Fin 32) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![0, 16, 0, 20]) (.leaf ![0, 0, 0, 25])) (.branch 3 (.leaf ![0, 31, 0, 25]) (.leaf ![31, 31, 0, 13]))) (.branch 6 (.branch 5 (.leaf ![0, 9, 0, 10]) (.leaf ![0, 9, 0, 10])) (.branch 7 (.leaf ![31, 9, 31, 10]) (.leaf ![0, 9, 16, 10])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![0, 9, 19, 10]) (.leaf ![31, 9, 17, 10])) (.branch 11 (.leaf ![0, 9, 18, 10]) (.leaf ![0, 9, 5, 10]))) (.branch 14 (.branch 13 (.leaf ![31, 9, 4, 10]) (.leaf ![0, 0, 0, 31])) (.branch 15 (.leaf ![0, 31, 0, 0]) (.leaf ![31, 31, 0, 31]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![0, 7, 0, 9]) (.leaf ![20, 7, 20, 9])) (.branch 19 (.leaf ![22, 7, 22, 9]) (.leaf ![0, 7, 0, 9]))) (.branch 22 (.branch 21 (.leaf ![23, 7, 23, 9]) (.leaf ![8, 7, 19, 9])) (.branch 23 (.leaf ![0, 7, 31, 9]) (.leaf ![21, 7, 4, 9])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![6, 7, 6, 9]) (.leaf ![0, 25, 0, 31])) (.branch 27 (.leaf ![0, 25, 0, 0]) (.leaf ![31, 13, 0, 31]))) (.branch 30 (.branch 29 (.leaf ![7, 12, 0, 7]) (.leaf ![7, 12, 20, 7])) (.branch 31 (.leaf ![30, 12, 22, 7]) (.leaf ![7, 12, 19, 7]))))))

@[expose] public def factorBlock1 : Lean.RArray (Fin 4 → Fin 32) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![7, 12, 0, 7]) (.leaf ![30, 12, 23, 7])) (.branch 3 (.leaf ![7, 12, 4, 7]) (.leaf ![7, 12, 6, 7]))) (.branch 6 (.branch 5 (.leaf ![30, 12, 31, 7]) (.leaf ![25, 25, 0, 13])) (.branch 7 (.leaf ![25, 25, 0, 25]) (.leaf ![25, 13, 0, 25])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![12, 12, 0, 10]) (.leaf ![12, 12, 20, 10])) (.branch 11 (.leaf ![15, 12, 22, 10]) (.leaf ![12, 12, 23, 10]))) (.branch 14 (.branch 13 (.leaf ![12, 12, 19, 10]) (.leaf ![15, 12, 0, 10])) (.branch 15 (.leaf ![12, 12, 6, 10]) (.leaf ![12, 12, 31, 10]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![15, 12, 4, 10]) (.leaf ![0, 20, 0, 22])) (.branch 19 (.leaf ![16, 18, 0, 16]) (.leaf ![18, 18, 0, 22]))) (.branch 22 (.branch 21 (.leaf ![0, 23, 0, 19]) (.leaf ![31, 23, 31, 19])) (.branch 23 (.leaf ![0, 19, 0, 23]) (.leaf ![19, 23, 0, 19])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![5, 23, 0, 19]) (.leaf ![0, 19, 31, 23])) (.branch 27 (.leaf ![23, 23, 31, 19]) (.leaf ![8, 23, 31, 19]))) (.branch 30 (.branch 29 (.leaf ![0, 20, 0, 22]) (.leaf ![9, 16, 9, 20])) (.branch 31 (.leaf ![16, 18, 9, 16]) (.leaf ![18, 18, 9, 22]))))))

@[expose] public def factorBlock2 : Lean.RArray (Fin 4 → Fin 32) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![0, 23, 0, 19]) (.leaf ![31, 23, 31, 19])) (.branch 3 (.leaf ![23, 23, 9, 19]) (.leaf ![9, 19, 9, 23]))) (.branch 6 (.branch 5 (.leaf ![8, 23, 9, 19]) (.leaf ![19, 23, 30, 19])) (.branch 7 (.leaf ![7, 19, 30, 23]) (.leaf ![5, 23, 30, 19])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![25, 20, 25, 22]) (.leaf ![10, 16, 10, 20])) (.branch 11 (.leaf ![29, 18, 10, 16]) (.leaf ![24, 18, 10, 22]))) (.branch 14 (.branch 13 (.leaf ![25, 23, 25, 19]) (.leaf ![25, 23, 25, 19])) (.branch 15 (.leaf ![28, 23, 10, 19]) (.leaf ![2, 23, 10, 19]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![14, 19, 10, 23]) (.leaf ![2, 23, 15, 19])) (.branch 19 (.leaf ![28, 23, 15, 19]) (.leaf ![15, 19, 15, 23]))) (.branch 22 (.branch 21 (.leaf ![0, 20, 7, 22]) (.leaf ![0, 16, 0, 20])) (.branch 23 (.leaf ![16, 18, 19, 16]) (.leaf ![18, 18, 23, 22])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![0, 19, 0, 23]) (.leaf ![23, 23, 20, 19])) (.branch 27 (.leaf ![8, 23, 22, 19]) (.leaf ![0, 23, 7, 19]))) (.branch 30 (.branch 29 (.leaf ![31, 23, 9, 19]) (.leaf ![0, 19, 31, 23])) (.branch 31 (.leaf ![19, 23, 6, 19]) (.leaf ![5, 23, 4, 19]))))))

@[expose] public def factorBlock3 : Lean.RArray (Fin 4 → Fin 32) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![0, 20, 19, 22]) (.leaf ![23, 16, 23, 20])) (.branch 3 (.leaf ![16, 18, 0, 16]) (.leaf ![18, 18, 19, 22]))) (.branch 6 (.branch 5 (.leaf ![19, 23, 0, 19]) (.leaf ![20, 19, 20, 23])) (.branch 7 (.leaf ![5, 23, 22, 19]) (.leaf ![0, 23, 16, 19])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![31, 23, 17, 19]) (.leaf ![23, 23, 6, 19])) (.branch 11 (.leaf ![21, 19, 4, 23]) (.leaf ![8, 23, 31, 19]))) (.branch 14 (.branch 13 (.leaf ![25, 20, 21, 22]) (.leaf ![28, 16, 19, 20])) (.branch 15 (.leaf ![29, 18, 23, 16]) (.leaf ![24, 18, 0, 22]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![2, 23, 0, 19]) (.leaf ![28, 23, 20, 19])) (.branch 19 (.leaf ![1, 19, 22, 23]) (.leaf ![25, 23, 20, 19]))) (.branch 22 (.branch 21 (.leaf ![25, 23, 21, 19]) (.leaf ![28, 23, 4, 19])) (.branch 23 (.leaf ![2, 23, 31, 19]) (.leaf ![11, 19, 6, 23])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![0, 20, 12, 22]) (.leaf ![0, 16, 25, 20])) (.branch 27 (.leaf ![16, 18, 27, 16]) (.leaf ![18, 18, 3, 22]))) (.branch 30 (.branch 29 (.leaf ![0, 19, 25, 23]) (.leaf ![19, 23, 29, 19])) (.branch 31 (.leaf ![5, 23, 24, 19]) (.leaf ![0, 19, 25, 23]))))))

@[expose] public def factorBlock4 : Lean.RArray (Fin 4 → Fin 32) := (.branch 14 (.branch 7 (.branch 3 (.branch 1 (.leaf ![23, 23, 3, 19]) (.branch 2 (.leaf ![8, 23, 27, 19]) (.leaf ![0, 23, 15, 19]))) (.branch 5 (.branch 4 (.leaf ![31, 23, 14, 19]) (.leaf ![0, 20, 2, 22])) (.branch 6 (.leaf ![17, 16, 27, 20]) (.leaf ![16, 18, 3, 16])))) (.branch 10 (.branch 8 (.leaf ![18, 18, 25, 22]) (.branch 9 (.leaf ![23, 23, 25, 19]) (.leaf ![16, 19, 29, 23]))) (.branch 12 (.branch 11 (.leaf ![8, 23, 24, 19]) (.leaf ![19, 23, 3, 19])) (.branch 13 (.leaf ![17, 19, 27, 23]) (.leaf ![5, 23, 25, 19]))))) (.branch 21 (.branch 17 (.branch 15 (.leaf ![0, 23, 24, 19]) (.branch 16 (.leaf ![31, 23, 26, 19]) (.leaf ![25, 20, 27, 22]))) (.branch 19 (.branch 18 (.leaf ![3, 16, 3, 20]) (.leaf ![29, 18, 25, 16])) (.branch 20 (.leaf ![24, 18, 27, 22]) (.leaf ![28, 23, 25, 19])))) (.branch 24 (.branch 22 (.leaf ![2, 23, 29, 19]) (.branch 23 (.leaf ![24, 19, 24, 23]) (.leaf ![2, 23, 27, 19]))) (.branch 26 (.branch 25 (.leaf ![28, 23, 25, 19]) (.leaf ![26, 19, 3, 23])) (.branch 27 (.leaf ![25, 23, 1, 19]) (.leaf ![25, 23, 11, 19]))))))
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
@[expose] public def words : Fin 32 → List (Fin 4) := fun j =>
  ((.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf []) (.leaf [0])) (.branch 3 (.leaf [1]) (.leaf [3]))) (.branch 6 (.branch 5 (.leaf [0, 1]) (.leaf [0, 3])) (.branch 7 (.leaf [1, 0]) (.leaf [1, 1])))) (.branch 12 (.branch 10 (.branch 9 (.leaf [3, 0]) (.leaf [3, 3])) (.branch 11 (.leaf [0, 1, 0]) (.leaf [0, 1, 1]))) (.branch 14 (.branch 13 (.leaf [0, 3, 0]) (.leaf [1, 0, 1])) (.branch 15 (.leaf [1, 0, 3]) (.leaf [3, 0, 1]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf [0, 1, 0, 1]) (.leaf [0, 1, 0, 3])) (.branch 19 (.leaf [0, 1, 1, 1]) (.leaf [0, 3, 0, 1]))) (.branch 22 (.branch 21 (.leaf [1, 0, 1, 0]) (.leaf [1, 0, 3, 0])) (.branch 23 (.leaf [1, 0, 3, 3]) (.leaf [3, 0, 1, 0])))) (.branch 28 (.branch 26 (.branch 25 (.leaf [0, 1, 0, 1, 0]) (.leaf [0, 1, 0, 3, 3])) (.branch 27 (.leaf [0, 3, 0, 1, 0]) (.leaf [1, 0, 1, 0, 1]))) (.branch 30 (.branch 29 (.leaf [1, 0, 1, 0, 3]) (.leaf [1, 0, 3, 0, 1])) (.branch 31 (.leaf [0, 1, 0, 1, 0, 1]) (.leaf [0, 1, 0, 3, 0, 1])))))) : Lean.RArray (List (Fin 4))).get j.val
@[expose] public def wordCodes : Fin 32 → MatrixCode := fun j =>
  ((.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 6643) (.leaf 13291)) (.branch 3 (.leaf 13229) (.leaf 13220))) (.branch 6 (.branch 5 (.leaf 6746) (.leaf 6737)) (.branch 7 (.leaf 6740) (.leaf 6661)))) (.branch 12 (.branch 10 (.branch 9 (.leaf 6749) (.leaf 6652)) (.branch 11 (.leaf 13214) (.leaf 13309))) (.branch 14 (.branch 13 (.leaf 13223) (.leaf 13285)) (.branch 15 (.leaf 13294) (.leaf 13303))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf 6646) (.leaf 6655)) (.branch 19 (.leaf 6728) (.leaf 6664))) (.branch 22 (.branch 21 (.leaf 6649) (.leaf 6667)) (.branch 23 (.leaf 6731) (.leaf 6658)))) (.branch 28 (.branch 26 (.branch 25 (.leaf 13288) (.leaf 13205)) (.branch 27 (.leaf 13297) (.leaf 13226))) (.branch 30 (.branch 29 (.leaf 13217) (.leaf 13208)) (.branch 31 (.leaf 6743) (.leaf 6725)))))) : Lean.RArray MatrixCode).get j.val
set_option maxHeartbeats 4000000 in
public theorem wordEval : ∀ j, (evalWord (nodeGenerator 30) (words j)).val =
    decodeMatrix (wordCodes j) := by decide +kernel
@[expose] public def next : Fin 156 → Fin 4 → Fin 156 := fun j =>
  ((.branch 2 (.branch 1 (.leaf nextBlock0) (.leaf nextBlock1)) (.branch 3 (.leaf nextBlock2) (.branch 4 (.leaf nextBlock3) (.leaf nextBlock4)))) : Lean.RArray (Lean.RArray (Fin 4 → Fin 156))).get (j.val / 32) |>.get (j.val % 32)
@[expose] public def factorIndex : Fin 156 → Fin 4 → Fin 32 := fun j =>
  ((.branch 2 (.branch 1 (.leaf factorBlock0) (.leaf factorBlock1)) (.branch 3 (.leaf factorBlock2) (.branch 4 (.leaf factorBlock3) (.leaf factorBlock4)))) : Lean.RArray (Lean.RArray (Fin 4 → Fin 32))).get (j.val / 32) |>.get (j.val % 32)
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
public theorem valid : table.Valid ambientGenerator (nodeGenerator 30) rep := by
  constructor
  · decide +kernel
  · intro j k
    apply Subtype.ext
    change (rep j).val * (ambientGenerator k).val =
      (evalWord (nodeGenerator 30) (words (factorIndex j k))).val * (rep (next j k)).val
    rw [wordEval]
    exact transitions j k
public theorem cover : RightCosetCover (properNode 30) rep := by
  rw [properNode_eq_wordSubgroup]
  exact table.sound ambientGenerator ambientInverse ambientGenerator_inv
    ambient_wordSubgroup_eq_top (nodeGenerator 30) (symmInv (n := (generatorCodes 30).length))
    (nodeGenerator_inv 30) rep valid
end Matrix.PSL3Three.CertifiedEnumeration.Cosets30
