module
public import Theory.SpecificGroups.PSL3Three.CosetCover.Check
/-!
# Checked right cosets for node 32

These are untrusted matrix codes and subgroup words generated from the fixed
lists in `RepresentativeBounds`. The kernel checks determinants, word values,
and every transition by the four ambient generators. `cover` then follows from
`RightCosetTable.sound`, using the proved generation of the actual SL₃(3).

Source: the elementary coset-table argument in `SubgroupEnumeration` and
GLS III, Theorem 6.5.3. Row zero represents the identity matrix.
-/

namespace Matrix.PSL3Three.CertifiedEnumeration.Cosets32
open Theory.GroupTheory Theory.GroupTheory.SubgroupEnumeration CosetCheck
set_option maxRecDepth 100000

@[expose] public def codeBlock0 : Lean.RArray (MatrixCode) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 6643) (.leaf 828)) (.branch 3 (.leaf 829) (.leaf 830))) (.branch 6 (.branch 5 (.leaf 831) (.leaf 832)) (.branch 7 (.leaf 833) (.leaf 834)))) (.branch 12 (.branch 10 (.branch 9 (.leaf 835) (.leaf 836)) (.branch 11 (.leaf 900) (.leaf 901))) (.branch 14 (.branch 13 (.leaf 902) (.leaf 903)) (.branch 15 (.leaf 904) (.leaf 905))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf 906) (.leaf 907)) (.branch 19 (.leaf 908) (.leaf 975))) (.branch 22 (.branch 21 (.leaf 976) (.leaf 984)) (.branch 23 (.leaf 985) (.leaf 986)))) (.branch 28 (.branch 26 (.branch 25 (.leaf 993) (.leaf 994)) (.branch 27 (.leaf 995) (.leaf 1056))) (.branch 30 (.branch 29 (.leaf 1057) (.leaf 1058)) (.branch 31 (.leaf 1068) (.leaf 1069))))))

@[expose] public def codeBlock1 : Lean.RArray (MatrixCode) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 1070) (.leaf 1071)) (.branch 3 (.leaf 1072) (.leaf 1073))) (.branch 6 (.branch 5 (.leaf 1137) (.leaf 1138)) (.branch 7 (.leaf 1139) (.leaf 1143)))) (.branch 12 (.branch 10 (.branch 9 (.leaf 1144) (.leaf 1145)) (.branch 11 (.leaf 1158) (.leaf 1159))) (.branch 14 (.branch 13 (.leaf 1160) (.leaf 1221)) (.branch 15 (.leaf 1222) (.leaf 1223))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf 1230) (.leaf 1231)) (.branch 19 (.leaf 1232) (.leaf 1239))) (.branch 22 (.branch 21 (.leaf 1240) (.leaf 1241)) (.branch 23 (.leaf 1302) (.leaf 1303)))) (.branch 28 (.branch 26 (.branch 25 (.leaf 1304) (.leaf 1308)) (.branch 27 (.leaf 1309) (.leaf 1310))) (.branch 30 (.branch 29 (.leaf 1314) (.leaf 1315)) (.branch 31 (.leaf 1316) (.leaf 1383))))))

@[expose] public def codeBlock2 : Lean.RArray (MatrixCode) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 1384) (.leaf 1385)) (.branch 3 (.leaf 1386) (.leaf 1387))) (.branch 6 (.branch 5 (.leaf 1388) (.leaf 1398)) (.branch 7 (.leaf 1399) (.leaf 1400)))) (.branch 12 (.branch 10 (.branch 9 (.leaf 1548) (.leaf 1549)) (.branch 11 (.leaf 1550) (.leaf 1551))) (.branch 14 (.branch 13 (.leaf 1552) (.leaf 1553)) (.branch 15 (.leaf 1554) (.leaf 1555))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf 1556) (.leaf 1638)) (.branch 19 (.leaf 1639) (.leaf 1640))) (.branch 22 (.branch 21 (.leaf 1641) (.leaf 1642)) (.branch 23 (.leaf 1643) (.leaf 1644)))) (.branch 28 (.branch 26 (.branch 25 (.leaf 1645) (.leaf 1646)) (.branch 27 (.leaf 1707) (.leaf 1708))) (.branch 30 (.branch 29 (.leaf 1709) (.leaf 1716)) (.branch 31 (.leaf 1717) (.leaf 1718))))))

@[expose] public def codeBlock3 : Lean.RArray (MatrixCode) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 1725) (.leaf 1726)) (.branch 3 (.leaf 1727) (.leaf 1788))) (.branch 6 (.branch 5 (.leaf 1789) (.leaf 1790)) (.branch 7 (.leaf 1791) (.leaf 1792)))) (.branch 12 (.branch 10 (.branch 9 (.leaf 1793) (.leaf 1803)) (.branch 11 (.leaf 1804) (.leaf 1805))) (.branch 14 (.branch 13 (.leaf 1869) (.leaf 1870)) (.branch 15 (.leaf 1871) (.leaf 1875))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf 1876) (.leaf 1877)) (.branch 19 (.leaf 1881) (.leaf 1882))) (.branch 22 (.branch 21 (.leaf 1883) (.leaf 1947)) (.branch 23 (.leaf 1948) (.leaf 1949)))) (.branch 28 (.branch 26 (.branch 25 (.leaf 1956) (.leaf 1957)) (.branch 27 (.leaf 1958) (.leaf 1965))) (.branch 30 (.branch 29 (.leaf 1966) (.leaf 1967)) (.branch 31 (.leaf 2028) (.leaf 2029))))))

@[expose] public def codeBlock4 : Lean.RArray (MatrixCode) := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 2030) (.leaf 2034)) (.branch 3 (.leaf 2035) (.leaf 2036))) (.branch 6 (.branch 5 (.leaf 2049) (.leaf 2050)) (.branch 7 (.leaf 2051) (.leaf 2109)))) (.branch 12 (.branch 10 (.branch 9 (.leaf 2110) (.leaf 2111)) (.branch 11 (.leaf 2121) (.leaf 2122))) (.branch 14 (.branch 13 (.leaf 2123) (.leaf 2124)) (.branch 15 (.leaf 2125) (.leaf 2126)))))

@[expose] public def nextBlock0 : Lean.RArray (Fin 4 → Fin 144) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![27, 80, 19, 101]) (.leaf ![39, 125, 73, 48])) (.branch 3 (.leaf ![66, 127, 43, 64]) (.leaf ![10, 140, 102, 60]))) (.branch 6 (.branch 5 (.leaf ![44, 134, 25, 57]) (.leaf ![65, 136, 111, 46])) (.branch 7 (.leaf ![18, 122, 76, 69]) (.leaf ![38, 143, 34, 66])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![71, 118, 93, 55]) (.leaf ![15, 131, 79, 51])) (.branch 11 (.leaf ![102, 24, 3, 95]) (.leaf ![129, 28, 140, 109]))) (.branch 14 (.branch 13 (.leaf ![72, 39, 60, 107]) (.leaf ![100, 33, 131, 104])) (.branch 15 (.leaf ![133, 37, 51, 91]) (.leaf ![79, 21, 9, 116]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![106, 42, 122, 113]) (.leaf ![127, 20, 69, 100])) (.branch 19 (.leaf ![76, 30, 6, 98]) (.leaf ![0, 41, 27, 44]))) (.branch 22 (.branch 21 (.leaf ![134, 100, 36, 17]) (.leaf ![80, 116, 32, 15])) (.branch 23 (.leaf ![57, 72, 41, 96]) (.leaf ![23, 26, 23, 27])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![101, 95, 35, 10]) (.leaf ![4, 76, 44, 111])) (.branch 27 (.leaf ![26, 27, 26, 23]) (.leaf ![19, 23, 0, 26]))) (.branch 30 (.branch 29 (.leaf ![128, 109, 110, 11]) (.leaf ![30, 74, 77, 110])) (.branch 31 (.leaf ![77, 98, 29, 18]) (.leaf ![54, 75, 92, 105]))))))

@[expose] public def nextBlock1 : Lean.RArray (Fin 4 → Fin 144) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![21, 35, 80, 36]) (.leaf ![107, 104, 74, 13])) (.branch 3 (.leaf ![7, 79, 38, 93]) (.leaf ![24, 36, 101, 32]))) (.branch 6 (.branch 5 (.leaf ![20, 32, 134, 35]) (.leaf ![130, 91, 48, 14])) (.branch 7 (.leaf ![34, 77, 7, 92]) (.leaf ![73, 107, 1, 12])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![61, 78, 143, 114]) (.leaf ![22, 44, 57, 19])) (.branch 11 (.leaf ![103, 113, 125, 16]) (.leaf ![2, 73, 66, 102]))) (.branch 14 (.branch 13 (.leaf ![25, 19, 4, 41]) (.leaf ![91, 59, 126, 62])) (.branch 15 (.leaf ![70, 5, 135, 136]) (.leaf ![108, 137, 117, 86]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![37, 1, 130, 125]) (.leaf ![87, 132, 139, 88])) (.branch 19 (.leaf ![97, 53, 121, 63]) (.leaf ![14, 9, 133, 131]))) (.branch 22 (.branch 21 (.leaf ![138, 120, 142, 81]) (.leaf ![94, 63, 124, 50])) (.branch 23 (.leaf ![92, 68, 31, 71]) (.leaf ![68, 8, 96, 118])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![116, 119, 78, 89]) (.leaf ![41, 4, 22, 134])) (.branch 27 (.leaf ![83, 141, 114, 82]) (.leaf ![98, 62, 75, 45]))) (.branch 30 (.branch 29 (.leaf ![12, 3, 72, 140]) (.leaf ![143, 129, 40, 84])) (.branch 31 (.leaf ![95, 45, 105, 59]) (.leaf ![90, 50, 118, 53]))))))

@[expose] public def nextBlock2 : Lean.RArray (Fin 4 → Fin 144) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![64, 2, 64, 127]) (.leaf ![111, 128, 5, 83])) (.branch 3 (.leaf ![43, 7, 2, 143]) (.leaf ![84, 123, 136, 85]))) (.branch 6 (.branch 5 (.leaf ![96, 71, 55, 54]) (.leaf ![17, 6, 127, 122])) (.branch 7 (.leaf ![135, 138, 46, 87]) (.leaf ![93, 54, 8, 68])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![60, 96, 12, 22]) (.leaf ![1, 102, 39, 43])) (.branch 11 (.leaf ![33, 110, 107, 29]) (.leaf ![59, 105, 98, 31]))) (.branch 14 (.branch 13 (.leaf ![6, 111, 18, 25]) (.leaf ![29, 92, 30, 38])) (.branch 15 (.leaf ![56, 114, 116, 40]) (.leaf ![9, 93, 15, 34]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![32, 101, 21, 0]) (.leaf ![141, 52, 82, 120])) (.branch 19 (.leaf ![81, 58, 141, 141]) (.leaf ![114, 65, 58, 128]))) (.branch 22 (.branch 21 (.leaf ![136, 61, 67, 129]) (.leaf ![85, 67, 85, 123])) (.branch 23 (.leaf ![112, 47, 123, 137]) (.leaf ![139, 70, 49, 138])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![88, 49, 88, 132]) (.leaf ![109, 56, 132, 119])) (.branch 27 (.leaf ![118, 103, 63, 106]) (.leaf ![126, 14, 45, 37]))) (.branch 30 (.branch 29 (.leaf ![31, 38, 54, 77]) (.leaf ![8, 34, 71, 79])) (.branch 31 (.leaf ![124, 97, 53, 108]) (.leaf ![105, 10, 62, 24]))))))

@[expose] public def nextBlock3 : Lean.RArray (Fin 4 → Fin 144) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![55, 22, 68, 72]) (.leaf ![121, 108, 50, 94])) (.branch 3 (.leaf ![75, 18, 59, 30]) (.leaf ![119, 112, 113, 115]))) (.branch 6 (.branch 5 (.leaf ![131, 17, 13, 20]) (.leaf ![35, 0, 24, 80])) (.branch 7 (.leaf ![3, 43, 10, 73]) (.leaf ![125, 106, 42, 90])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![104, 13, 104, 33]) (.leaf ![62, 31, 95, 75])) (.branch 11 (.leaf ![122, 90, 16, 103]) (.leaf ![74, 12, 33, 39]))) (.branch 14 (.branch 13 (.leaf ![117, 94, 47, 97]) (.leaf ![132, 11, 89, 28])) (.branch 15 (.leaf ![28, 29, 128, 74]) (.leaf ![5, 25, 65, 76]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![123, 115, 86, 99]) (.leaf ![99, 16, 119, 42])) (.branch 19 (.leaf ![58, 40, 83, 78]) (.leaf ![120, 99, 137, 112]))) (.branch 22 (.branch 21 (.leaf ![78, 15, 56, 21]) (.leaf ![47, 139, 108, 142])) (.branch 23 (.leaf ![63, 55, 90, 8]) (.leaf ![113, 89, 99, 56])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![137, 81, 115, 52]) (.leaf ![50, 124, 97, 126])) (.branch 27 (.leaf ![16, 69, 106, 6]) (.leaf ![86, 85, 112, 67]))) (.branch 30 (.branch 29 (.leaf ![53, 126, 94, 121]) (.leaf ![42, 48, 103, 1])) (.branch 31 (.leaf ![45, 121, 91, 124]) (.leaf ![69, 64, 17, 2]))))))

@[expose] public def nextBlock4 : Lean.RArray (Fin 4 → Fin 144) := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![110, 83, 28, 65]) (.leaf ![140, 84, 11, 61])) (.branch 3 (.leaf ![48, 133, 37, 135]) (.leaf ![13, 51, 100, 9]))) (.branch 6 (.branch 5 (.leaf ![89, 88, 109, 49]) (.leaf ![51, 135, 14, 130])) (.branch 7 (.leaf ![36, 57, 20, 4]) (.leaf ![46, 130, 70, 133])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![67, 46, 84, 5]) (.leaf ![115, 86, 120, 47])) (.branch 11 (.leaf ![142, 87, 52, 70]) (.leaf ![49, 142, 87, 117]))) (.branch 14 (.branch 13 (.leaf ![11, 60, 129, 3]) (.leaf ![82, 82, 81, 58])) (.branch 15 (.leaf ![52, 117, 138, 139]) (.leaf ![40, 66, 61, 7])))))

@[expose] public def factorBlock0 : Lean.RArray (Fin 4 → Fin 37) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![1, 22, 0, 4]) (.leaf ![1, 18, 3, 13])) (.branch 3 (.leaf ![1, 17, 36, 19]) (.leaf ![1, 29, 5, 15]))) (.branch 6 (.branch 5 (.leaf ![34, 18, 22, 13]) (.leaf ![34, 17, 6, 19])) (.branch 7 (.leaf ![34, 29, 31, 15]) (.leaf ![26, 18, 4, 13])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![26, 17, 27, 19]) (.leaf ![26, 29, 20, 15])) (.branch 11 (.leaf ![1, 13, 3, 18]) (.leaf ![1, 19, 36, 17]))) (.branch 14 (.branch 13 (.leaf ![1, 15, 5, 29]) (.leaf ![26, 13, 4, 18])) (.branch 15 (.leaf ![26, 19, 27, 17]) (.leaf ![26, 15, 20, 29]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![34, 13, 22, 18]) (.leaf ![34, 19, 6, 17])) (.branch 19 (.leaf ![34, 15, 31, 29]) (.leaf ![0, 8, 1, 28]))) (.branch 22 (.branch 21 (.leaf ![36, 9, 1, 21]) (.leaf ![22, 33, 34, 25])) (.branch 23 (.leaf ![6, 23, 34, 22]) (.leaf ![31, 22, 34, 12])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![4, 27, 26, 10]) (.leaf ![27, 30, 26, 35])) (.branch 27 (.leaf ![20, 16, 26, 27]) (.leaf ![3, 8, 3, 28]))) (.branch 30 (.branch 29 (.leaf ![8, 9, 12, 21]) (.leaf ![28, 24, 31, 7])) (.branch 31 (.leaf ![14, 33, 16, 25]) (.leaf ![33, 23, 32, 22]))))))

@[expose] public def factorBlock1 : Lean.RArray (Fin 4 → Fin 37) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![31, 22, 20, 12]) (.leaf ![35, 27, 3, 10])) (.branch 3 (.leaf ![2, 30, 7, 35]) (.leaf ![20, 16, 9, 27]))) (.branch 6 (.branch 5 (.leaf ![3, 8, 35, 28]) (.leaf ![7, 9, 2, 21])) (.branch 7 (.leaf ![9, 24, 20, 7]) (.leaf ![11, 33, 3, 25])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![12, 23, 8, 22]) (.leaf ![31, 22, 28, 12])) (.branch 11 (.leaf ![16, 27, 14, 10]) (.leaf ![32, 30, 33, 35]))) (.branch 14 (.branch 13 (.leaf ![20, 16, 31, 27]) (.leaf ![3, 28, 1, 8])) (.branch 15 (.leaf ![36, 21, 1, 9]) (.leaf ![5, 7, 1, 24]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![4, 10, 26, 27]) (.leaf ![27, 35, 26, 30])) (.branch 19 (.leaf ![20, 27, 26, 16]) (.leaf ![22, 25, 34, 33]))) (.branch 22 (.branch 21 (.leaf ![6, 22, 34, 23]) (.leaf ![31, 12, 34, 22])) (.branch 23 (.leaf ![3, 28, 35, 8]) (.leaf ![7, 21, 2, 9])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![9, 7, 20, 24]) (.leaf ![16, 10, 14, 27])) (.branch 27 (.leaf ![32, 35, 33, 30]) (.leaf ![20, 27, 31, 16]))) (.branch 30 (.branch 29 (.leaf ![11, 25, 3, 33]) (.leaf ![12, 22, 8, 23])) (.branch 31 (.leaf ![31, 12, 28, 22]) (.leaf ![3, 28, 11, 8]))))))

@[expose] public def factorBlock2 : Lean.RArray (Fin 4 → Fin 37) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![8, 21, 12, 9]) (.leaf ![28, 7, 31, 24])) (.branch 3 (.leaf ![35, 10, 3, 27]) (.leaf ![2, 35, 7, 30]))) (.branch 6 (.branch 5 (.leaf ![20, 27, 9, 16]) (.leaf ![14, 25, 16, 33])) (.branch 7 (.leaf ![33, 22, 32, 23]) (.leaf ![31, 12, 20, 22])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![1, 13, 3, 18]) (.leaf ![1, 15, 5, 29])) (.branch 11 (.leaf ![1, 19, 36, 17]) (.leaf ![34, 13, 22, 18]))) (.branch 14 (.branch 13 (.leaf ![34, 15, 31, 29]) (.leaf ![34, 19, 6, 17])) (.branch 15 (.leaf ![26, 13, 4, 18]) (.leaf ![26, 15, 20, 29]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![26, 19, 27, 27]) (.leaf ![1, 18, 3, 13])) (.branch 19 (.leaf ![1, 29, 5, 15]) (.leaf ![1, 17, 36, 19]))) (.branch 22 (.branch 21 (.leaf ![26, 18, 4, 13]) (.leaf ![26, 29, 20, 15])) (.branch 23 (.leaf ![26, 17, 27, 19]) (.leaf ![34, 18, 22, 13])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![34, 29, 31, 15]) (.leaf ![34, 17, 6, 19])) (.branch 27 (.leaf ![3, 8, 1, 28]) (.leaf ![5, 24, 1, 7]))) (.branch 30 (.branch 29 (.leaf ![36, 9, 1, 21]) (.leaf ![22, 33, 34, 25])) (.branch 31 (.leaf ![31, 22, 34, 12]) (.leaf ![6, 23, 34, 22]))))))

@[expose] public def factorBlock3 : Lean.RArray (Fin 4 → Fin 37) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![4, 27, 26, 10]) (.leaf ![20, 16, 26, 27])) (.branch 3 (.leaf ![27, 30, 26, 35]) (.leaf ![3, 8, 35, 28]))) (.branch 6 (.branch 5 (.leaf ![9, 24, 20, 7]) (.leaf ![7, 2, 2, 21])) (.branch 7 (.leaf ![11, 33, 3, 25]) (.leaf ![31, 22, 28, 12])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![12, 23, 8, 22]) (.leaf ![16, 27, 14, 10])) (.branch 11 (.leaf ![20, 16, 31, 27]) (.leaf ![32, 30, 33, 35]))) (.branch 14 (.branch 13 (.leaf ![3, 8, 11, 28]) (.leaf ![28, 24, 31, 7])) (.branch 15 (.leaf ![8, 9, 12, 21]) (.leaf ![14, 33, 16, 25]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![31, 22, 20, 12]) (.leaf ![33, 23, 32, 22])) (.branch 19 (.leaf ![35, 27, 3, 10]) (.leaf ![20, 16, 9, 27]))) (.branch 22 (.branch 21 (.leaf ![2, 30, 7, 35]) (.leaf ![3, 28, 1, 8])) (.branch 23 (.leaf ![5, 7, 1, 24]) (.leaf ![36, 21, 1, 9])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![4, 10, 26, 27]) (.leaf ![20, 27, 26, 16])) (.branch 27 (.leaf ![27, 35, 26, 30]) (.leaf ![22, 25, 34, 33]))) (.branch 30 (.branch 29 (.leaf ![31, 12, 34, 22]) (.leaf ![6, 22, 34, 23])) (.branch 31 (.leaf ![3, 28, 11, 8]) (.leaf ![28, 7, 31, 24]))))))

@[expose] public def factorBlock4 : Lean.RArray (Fin 4 → Fin 37) := (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![8, 21, 12, 9]) (.leaf ![35, 10, 3, 27])) (.branch 3 (.leaf ![20, 27, 9, 16]) (.leaf ![2, 35, 7, 30]))) (.branch 6 (.branch 5 (.leaf ![14, 25, 16, 33]) (.leaf ![31, 12, 20, 22])) (.branch 7 (.leaf ![33, 22, 32, 23]) (.leaf ![3, 28, 35, 8])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![9, 7, 20, 24]) (.leaf ![7, 21, 2, 9])) (.branch 11 (.leaf ![16, 10, 14, 27]) (.leaf ![20, 27, 31, 16]))) (.branch 14 (.branch 13 (.leaf ![32, 35, 33, 30]) (.leaf ![11, 25, 3, 33])) (.branch 15 (.leaf ![31, 12, 28, 22]) (.leaf ![12, 22, 8, 23])))))
@[expose] public def codes : Fin 144 → MatrixCode := fun j =>
  ((.branch 2 (.branch 1 (.leaf codeBlock0) (.leaf codeBlock1)) (.branch 3 (.leaf codeBlock2) (.branch 4 (.leaf codeBlock3) (.leaf codeBlock4)))) : Lean.RArray (Lean.RArray (MatrixCode))).get (j.val / 32) |>.get (j.val % 32)
@[expose] public def detCheck (k : Nat) : Bool := (codeDet (codes ⟨k % 144, Nat.mod_lt _ (by decide)⟩)).val == 1
set_option maxHeartbeats 4000000 in
private theorem detCheck_0 : checkRange detCheck 0 64 = true := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem detCheck_1 : checkRange detCheck 64 64 = true := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem detCheck_2 : checkRange detCheck 128 16 = true := by decide +kernel

public theorem det : ∀ j, codeDet (codes j) = 1 := by
  have h := checkRange_fin (by decide : 0 < 144)
    (fun j => (codeDet (codes j)).val == 1) (checkRange_append detCheck_0 (checkRange_append detCheck_1 detCheck_2))
  intro j
  apply Fin.ext
  exact beq_iff_eq.mp (h j)
@[expose] public def rep (j : Fin 144) : SL := finiteModelEquiv ⟨codes j, det j⟩
@[expose] public def words : Fin 37 → List (Fin 4) := fun j =>
  ((.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf []) (.leaf [0])) (.branch 3 (.leaf [1]) (.leaf [2]))) (.branch 6 (.branch 5 (.leaf [3]) (.leaf [0, 0])) (.branch 7 (.leaf [0, 1]) (.branch 8 (.leaf [0, 3]) (.leaf [1, 0]))))) (.branch 13 (.branch 11 (.branch 10 (.leaf [1, 2]) (.leaf [2, 1])) (.branch 12 (.leaf [2, 2]) (.leaf [2, 3]))) (.branch 15 (.branch 14 (.leaf [3, 0]) (.leaf [3, 2])) (.branch 16 (.leaf [0, 0, 0]) (.branch 17 (.leaf [0, 0, 1]) (.leaf [0, 0, 3])))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf [0, 1, 0]) (.leaf [0, 1, 2])) (.branch 21 (.leaf [0, 3, 0]) (.leaf [0, 3, 2]))) (.branch 24 (.branch 23 (.leaf [1, 0, 0]) (.leaf [1, 0, 1])) (.branch 25 (.leaf [1, 2, 2]) (.branch 26 (.leaf [1, 2, 3]) (.leaf [2, 1, 2]))))) (.branch 32 (.branch 29 (.branch 28 (.leaf [2, 2, 3]) (.leaf [2, 3, 0])) (.branch 30 (.leaf [3, 0, 1]) (.branch 31 (.leaf [3, 2, 1]) (.leaf [0, 0, 1, 0])))) (.branch 34 (.branch 33 (.leaf [0, 3, 2, 1]) (.leaf [1, 0, 0, 3])) (.branch 35 (.leaf [1, 0, 1, 2]) (.branch 36 (.leaf [1, 2, 2, 3]) (.leaf [2, 3, 0, 1]))))))) : Lean.RArray (List (Fin 4))).get j.val
@[expose] public def wordCodes : Fin 37 → MatrixCode := fun j =>
  ((.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf 6643) (.leaf 977)) (.branch 3 (.leaf 6161) (.leaf 2466))) (.branch 6 (.branch 5 (.leaf 16345) (.leaf 3688)) (.branch 7 (.leaf 3871) (.branch 8 (.leaf 7885) (.leaf 18511))))) (.branch 13 (.branch 11 (.branch 10 (.leaf 8371) (.leaf 8783)) (.branch 12 (.leaf 7617) (.leaf 8176))) (.branch 15 (.branch 14 (.leaf 9696) (.leaf 18804)) (.branch 16 (.leaf 11820) (.branch 17 (.leaf 7450) (.leaf 1020)))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf 12342) (.leaf 1038)) (.branch 21 (.leaf 2543) (.leaf 9432))) (.branch 24 (.branch 23 (.leaf 16140) (.leaf 15361)) (.branch 25 (.leaf 15912) (.branch 26 (.leaf 9109) (.leaf 9731))))) (.branch 32 (.branch 29 (.branch 28 (.leaf 3737) (.leaf 6277)) (.branch 30 (.leaf 10083) (.branch 31 (.leaf 15752) (.leaf 2641)))) (.branch 34 (.branch 33 (.leaf 8594) (.leaf 6154)) (.branch 35 (.leaf 11915) (.branch 36 (.leaf 18463) (.leaf 16726))))))) : Lean.RArray MatrixCode).get j.val
set_option maxHeartbeats 4000000 in
public theorem wordEval : ∀ j, (evalWord (nodeGenerator 32) (words j)).val =
    decodeMatrix (wordCodes j) := by decide +kernel
@[expose] public def next : Fin 144 → Fin 4 → Fin 144 := fun j =>
  ((.branch 2 (.branch 1 (.leaf nextBlock0) (.leaf nextBlock1)) (.branch 3 (.leaf nextBlock2) (.branch 4 (.leaf nextBlock3) (.leaf nextBlock4)))) : Lean.RArray (Lean.RArray (Fin 4 → Fin 144))).get (j.val / 32) |>.get (j.val % 32)
@[expose] public def factorIndex : Fin 144 → Fin 4 → Fin 37 := fun j =>
  ((.branch 2 (.branch 1 (.leaf factorBlock0) (.leaf factorBlock1)) (.branch 3 (.leaf factorBlock2) (.branch 4 (.leaf factorBlock3) (.leaf factorBlock4)))) : Lean.RArray (Lean.RArray (Fin 4 → Fin 37))).get (j.val / 32) |>.get (j.val % 32)
@[expose] public def table : RightCosetTable 4 4 144 where
  base := 0
  next := next
  factor := fun j k => words (factorIndex j k)
@[expose] public def transitionCheck (j : Fin 144) : Bool :=
  matrixEq ((rep j).val * (ambientGenerator 0).val)
    (decodeMatrix (wordCodes (factorIndex j 0)) * (rep (next j 0)).val) &&
  matrixEq ((rep j).val * (ambientGenerator 1).val)
    (decodeMatrix (wordCodes (factorIndex j 1)) * (rep (next j 1)).val) &&
  matrixEq ((rep j).val * (ambientGenerator 2).val)
    (decodeMatrix (wordCodes (factorIndex j 2)) * (rep (next j 2)).val) &&
  matrixEq ((rep j).val * (ambientGenerator 3).val)
    (decodeMatrix (wordCodes (factorIndex j 3)) * (rep (next j 3)).val)
@[expose] public def rowCheck (k : Nat) : Bool := transitionCheck ⟨k % 144, Nat.mod_lt _ (by decide)⟩
set_option maxHeartbeats 4000000 in
private theorem rowCheck_0 : checkRange rowCheck 0 64 = true := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem rowCheck_1 : checkRange rowCheck 64 64 = true := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem rowCheck_2 : checkRange rowCheck 128 16 = true := by decide +kernel

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
public theorem valid : table.Valid ambientGenerator (nodeGenerator 32) rep := by
  constructor
  · decide +kernel
  · intro j k
    apply Subtype.ext
    change (rep j).val * (ambientGenerator k).val =
      (evalWord (nodeGenerator 32) (words (factorIndex j k))).val * (rep (next j k)).val
    rw [wordEval]
    exact transitions j k
public theorem cover : RightCosetCover (properNode 32) rep := by
  rw [properNode_eq_wordSubgroup]
  exact table.sound ambientGenerator ambientInverse ambientGenerator_inv
    ambient_wordSubgroup_eq_top (nodeGenerator 32) (symmInv (n := (generatorCodes 32).length))
    (nodeGenerator_inv 32) rep valid
end Matrix.PSL3Three.CertifiedEnumeration.Cosets32
