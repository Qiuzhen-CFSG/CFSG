module
public import Theory.SpecificGroups.PSL3Three.CosetCover.Check
/-!
# Checked right cosets for node 33

These are untrusted matrix codes and subgroup words generated from the fixed
lists in `RepresentativeBounds`. The kernel checks determinants, word values,
and every transition by the four ambient generators. `cover` then follows from
`RightCosetTable.sound`, using the proved generation of the actual SL₃(3).

Source: the elementary coset-table argument in `SubgroupEnumeration` and
GLS III, Theorem 6.5.3. Row zero represents the identity matrix.
-/

namespace Matrix.PSL3Three.CertifiedEnumeration.Cosets33
open Theory.GroupTheory Theory.GroupTheory.SubgroupEnumeration CosetCheck
set_option maxRecDepth 100000

@[expose] public def codeBlock0 : Lean.RArray (MatrixCode) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 6643) (.leaf 828)) (.branch 3 (.leaf 829) (.leaf 830))) (.branch 6 (.branch 5 (.leaf 831) (.leaf 832)) (.branch 7 (.leaf 833) (.leaf 834)))) (.branch 12 (.branch 10 (.branch 9 (.leaf 835) (.leaf 836)) (.branch 11 (.leaf 975) (.leaf 976))) (.branch 14 (.branch 13 (.leaf 977) (.leaf 984)) (.branch 15 (.leaf 985) (.leaf 986))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf 993) (.leaf 994)) (.branch 19 (.leaf 995) (.leaf 1056))) (.branch 22 (.branch 21 (.leaf 1057) (.leaf 1058)) (.branch 23 (.leaf 1068) (.leaf 1069)))) (.branch 28 (.branch 26 (.branch 25 (.leaf 1070) (.leaf 1071)) (.branch 27 (.leaf 1072) (.leaf 1073))) (.branch 30 (.branch 29 (.leaf 1137) (.leaf 1138)) (.branch 31 (.leaf 1139) (.leaf 1143))))))

@[expose] public def codeBlock1 : Lean.RArray (MatrixCode) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 1144) (.leaf 1145)) (.branch 3 (.leaf 1158) (.leaf 1159))) (.branch 6 (.branch 5 (.leaf 1160) (.leaf 2432)) (.branch 7 (.leaf 2435) (.leaf 2438)))) (.branch 12 (.branch 10 (.branch 9 (.leaf 2441) (.leaf 2444)) (.branch 11 (.leaf 2447) (.leaf 2450))) (.branch 14 (.branch 13 (.leaf 2453) (.leaf 2459)) (.branch 15 (.leaf 2462) (.leaf 2465))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf 2466) (.leaf 2469)) (.branch 19 (.leaf 2472) (.leaf 2476))) (.branch 22 (.branch 21 (.leaf 2479) (.leaf 2482)) (.branch 23 (.leaf 2486) (.leaf 2489)))) (.branch 28 (.branch 26 (.branch 25 (.leaf 2492) (.leaf 2494)) (.branch 27 (.leaf 2497) (.leaf 2500))) (.branch 30 (.branch 29 (.leaf 2502) (.leaf 2505)) (.branch 31 (.leaf 2508) (.leaf 3161))))))

@[expose] public def codeBlock2 : Lean.RArray (MatrixCode) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 3162) (.leaf 3166)) (.branch 3 (.leaf 3170) (.leaf 3171))) (.branch 6 (.branch 5 (.leaf 3175) (.leaf 3179)) (.branch 7 (.leaf 3180) (.leaf 3184)))) (.branch 12 (.branch 10 (.branch 9 (.leaf 3188) (.leaf 3189)) (.branch 11 (.leaf 3193) (.leaf 3195))) (.branch 14 (.branch 13 (.leaf 3199) (.leaf 3203)) (.branch 15 (.leaf 3205) (.leaf 3209))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf 3210) (.leaf 3215)) (.branch 19 (.leaf 3216) (.leaf 3220))) (.branch 22 (.branch 21 (.leaf 3223) (.leaf 3227)) (.branch 23 (.leaf 3228) (.leaf 3231)))) (.branch 28 (.branch 26 (.branch 25 (.leaf 3235) (.leaf 3239)) (.branch 27 (.leaf 3890) (.leaf 3892))) (.branch 30 (.branch 29 (.leaf 3894) (.leaf 3899)) (.branch 31 (.leaf 3901) (.leaf 3903))))))

@[expose] public def codeBlock3 : Lean.RArray (MatrixCode) := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf 3908) (.leaf 3910)) (.branch 3 (.leaf 3912) (.branch 4 (.leaf 3917) (.leaf 3919)))) (.branch 7 (.branch 6 (.leaf 3921) (.leaf 3924)) (.branch 8 (.leaf 3929) (.branch 9 (.leaf 3931) (.leaf 3934))))) (.branch 15 (.branch 12 (.branch 11 (.leaf 3936) (.leaf 3941)) (.branch 13 (.leaf 3944) (.branch 14 (.leaf 3946) (.leaf 3948)))) (.branch 18 (.branch 16 (.leaf 3952) (.branch 17 (.leaf 3954) (.leaf 3959))) (.branch 19 (.leaf 3960) (.branch 20 (.leaf 3965) (.leaf 3967))))))

@[expose] public def nextBlock0 : Lean.RArray (Fin 4 → Fin 117) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![9, 44, 10, 43]) (.leaf ![18, 1, 37, 1])) (.branch 3 (.leaf ![15, 5, 38, 8]) (.leaf ![12, 9, 39, 6]))) (.branch 6 (.branch 5 (.leaf ![17, 4, 40, 4]) (.leaf ![14, 8, 41, 2])) (.branch 7 (.leaf ![11, 3, 42, 9]) (.leaf ![16, 7, 43, 7])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![13, 2, 44, 5]) (.leaf ![10, 6, 0, 3])) (.branch 11 (.leaf ![0, 64, 9, 95]) (.leaf ![42, 65, 6, 93]))) (.branch 14 (.branch 13 (.leaf ![39, 63, 3, 94]) (.leaf ![44, 67, 8, 92])) (.branch 15 (.leaf ![41, 68, 5, 90]) (.leaf ![38, 66, 2, 91]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![43, 70, 7, 98]) (.leaf ![40, 71, 4, 96])) (.branch 19 (.leaf ![37, 69, 1, 97]) (.leaf ![71, 83, 48, 103]))) (.branch 22 (.branch 21 (.leaf ![68, 81, 49, 104]) (.leaf ![65, 82, 50, 102])) (.branch 23 (.leaf ![70, 84, 51, 99]) (.leaf ![67, 85, 52, 100])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![64, 86, 53, 101]) (.leaf ![69, 88, 45, 107])) (.branch 27 (.leaf ![66, 89, 46, 105]) (.leaf ![63, 87, 47, 106]))) (.branch 30 (.branch 29 (.leaf ![98, 72, 60, 111]) (.leaf ![95, 73, 62, 112])) (.branch 31 (.leaf ![92, 74, 61, 113]) (.leaf ![97, 77, 54, 109]))))))

@[expose] public def nextBlock1 : Lean.RArray (Fin 4 → Fin 117) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![94, 75, 56, 110]) (.leaf ![91, 76, 55, 108])) (.branch 3 (.leaf ![96, 79, 57, 116]) (.leaf ![93, 80, 59, 114]))) (.branch 6 (.branch 5 (.leaf ![90, 78, 58, 115]) (.leaf ![1, 39, 18, 38])) (.branch 7 (.leaf ![2, 37, 15, 39]) (.leaf ![3, 38, 12, 37])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![4, 42, 17, 41]) (.leaf ![5, 40, 14, 42])) (.branch 11 (.leaf ![6, 41, 11, 40]) (.leaf ![7, 0, 16, 44]))) (.branch 14 (.branch 13 (.leaf ![8, 43, 13, 0]) (.leaf ![25, 45, 69, 45])) (.branch 15 (.leaf ![26, 46, 66, 46]) (.leaf ![27, 47, 63, 47]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![19, 49, 71, 50]) (.leaf ![20, 50, 68, 48])) (.branch 19 (.leaf ![21, 48, 65, 49]) (.leaf ![22, 53, 70, 52]))) (.branch 22 (.branch 21 (.leaf ![23, 51, 67, 53]) (.leaf ![24, 52, 64, 51])) (.branch 23 (.leaf ![31, 55, 97, 56]) (.leaf ![33, 56, 91, 54])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![32, 54, 94, 55]) (.leaf ![34, 57, 96, 57])) (.branch 27 (.leaf ![36, 58, 90, 58]) (.leaf ![35, 59, 93, 59]))) (.branch 30 (.branch 29 (.leaf ![28, 62, 98, 61]) (.leaf ![30, 60, 92, 62])) (.branch 31 (.leaf ![29, 61, 95, 60]) (.leaf ![47, 94, 27, 12]))))))

@[expose] public def nextBlock2 : Lean.RArray (Fin 4 → Fin 117) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![53, 95, 24, 10]) (.leaf ![50, 93, 21, 11])) (.branch 3 (.leaf ![46, 91, 26, 15]) (.leaf ![52, 92, 23, 13]))) (.branch 6 (.branch 5 (.leaf ![49, 90, 20, 14]) (.leaf ![45, 97, 25, 18])) (.branch 7 (.leaf ![51, 98, 22, 16]) (.leaf ![48, 96, 19, 17])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![107, 111, 87, 28]) (.leaf ![104, 112, 86, 29])) (.branch 11 (.leaf ![101, 113, 82, 30]) (.leaf ![103, 110, 89, 32]))) (.branch 14 (.branch 13 (.leaf ![100, 108, 85, 33]) (.leaf ![106, 109, 81, 31])) (.branch 15 (.leaf ![99, 115, 88, 36]) (.leaf ![105, 116, 84, 34]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![102, 114, 83, 35]) (.leaf ![77, 104, 106, 20])) (.branch 19 (.leaf ![74, 102, 101, 21]) (.leaf ![80, 103, 102, 19]))) (.branch 22 (.branch 21 (.leaf ![79, 99, 105, 22]) (.leaf ![76, 100, 100, 23])) (.branch 23 (.leaf ![73, 101, 104, 24]) (.leaf ![72, 106, 107, 27])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![78, 107, 99, 25]) (.leaf ![75, 105, 103, 26])) (.branch 27 (.leaf ![58, 14, 36, 68]) (.leaf ![55, 15, 33, 66]))) (.branch 30 (.branch 29 (.leaf ![61, 13, 30, 67]) (.leaf ![59, 11, 35, 65])) (.branch 31 (.leaf ![56, 12, 32, 63]) (.leaf ![62, 10, 29, 64]))))))

@[expose] public def nextBlock3 : Lean.RArray (Fin 4 → Fin 117) := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf ![57, 17, 34, 71]) (.leaf ![54, 18, 31, 69])) (.branch 3 (.leaf ![60, 16, 28, 70]) (.branch 4 (.leaf ![88, 22, 78, 84]) (.leaf ![85, 23, 76, 85])))) (.branch 7 (.branch 6 (.leaf ![82, 24, 74, 86]) (.leaf ![83, 21, 80, 82])) (.branch 8 (.leaf ![89, 19, 75, 83]) (.branch 9 (.leaf ![86, 20, 73, 81]) (.leaf ![84, 26, 79, 89]))))) (.branch 15 (.branch 12 (.branch 11 (.leaf ![81, 27, 77, 87]) (.leaf ![87, 25, 72, 88])) (.branch 13 (.leaf ![109, 33, 115, 76]) (.branch 14 (.leaf ![115, 31, 108, 77]) (.leaf ![112, 32, 113, 75])))) (.branch 18 (.branch 16 (.leaf ![116, 28, 114, 72]) (.branch 17 (.leaf ![113, 29, 110, 73]) (.leaf ![110, 30, 112, 74]))) (.branch 19 (.leaf ![111, 35, 116, 80]) (.branch 20 (.leaf ![108, 36, 109, 78]) (.leaf ![114, 34, 111, 79]))))))

@[expose] public def factorBlock0 : Lean.RArray (Fin 4 → Fin 20) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![19, 19, 0, 19]) (.leaf ![19, 2, 0, 1])) (.branch 3 (.leaf ![19, 2, 0, 1]) (.leaf ![19, 2, 0, 1]))) (.branch 6 (.branch 5 (.leaf ![19, 2, 0, 1]) (.leaf ![19, 2, 0, 1])) (.branch 7 (.leaf ![19, 2, 0, 1]) (.leaf ![19, 2, 0, 1])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![19, 2, 0, 1]) (.leaf ![19, 2, 19, 1])) (.branch 11 (.leaf ![0, 0, 19, 18]) (.leaf ![19, 0, 19, 18]))) (.branch 14 (.branch 13 (.leaf ![19, 0, 19, 18]) (.leaf ![19, 0, 19, 18])) (.branch 15 (.leaf ![19, 0, 19, 18]) (.leaf ![19, 0, 19, 18]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![19, 0, 19, 18]) (.leaf ![19, 0, 19, 18])) (.branch 19 (.leaf ![19, 0, 19, 18]) (.leaf ![19, 15, 0, 13]))) (.branch 22 (.branch 21 (.leaf ![19, 15, 0, 13]) (.leaf ![19, 15, 0, 13])) (.branch 23 (.leaf ![19, 15, 0, 13]) (.leaf ![19, 15, 0, 13])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![19, 15, 0, 13]) (.leaf ![19, 15, 0, 13])) (.branch 27 (.leaf ![19, 15, 0, 13]) (.leaf ![19, 15, 0, 13]))) (.branch 30 (.branch 29 (.leaf ![19, 10, 17, 3]) (.leaf ![19, 10, 17, 3])) (.branch 31 (.leaf ![19, 10, 17, 3]) (.leaf ![19, 10, 17, 3]))))))

@[expose] public def factorBlock1 : Lean.RArray (Fin 4 → Fin 20) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![19, 10, 17, 3]) (.leaf ![19, 10, 17, 3])) (.branch 3 (.leaf ![19, 10, 17, 3]) (.leaf ![19, 10, 17, 3]))) (.branch 6 (.branch 5 (.leaf ![19, 10, 17, 3]) (.leaf ![0, 0, 19, 0])) (.branch 7 (.leaf ![0, 0, 19, 0]) (.leaf ![0, 0, 19, 0])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![0, 0, 19, 0]) (.leaf ![0, 0, 19, 0])) (.branch 11 (.leaf ![0, 0, 19, 0]) (.leaf ![0, 19, 19, 0]))) (.branch 14 (.branch 13 (.leaf ![0, 0, 19, 19]) (.leaf ![0, 15, 19, 10])) (.branch 15 (.leaf ![0, 15, 19, 10]) (.leaf ![0, 15, 19, 10]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![0, 15, 19, 10]) (.leaf ![0, 15, 19, 10])) (.branch 19 (.leaf ![0, 15, 19, 10]) (.leaf ![0, 15, 19, 10]))) (.branch 22 (.branch 21 (.leaf ![0, 15, 19, 10]) (.leaf ![0, 15, 19, 10])) (.branch 23 (.leaf ![17, 10, 4, 15]) (.leaf ![17, 10, 4, 15])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![17, 10, 4, 15]) (.leaf ![17, 10, 4, 15])) (.branch 27 (.leaf ![17, 10, 4, 15]) (.leaf ![17, 10, 4, 15]))) (.branch 30 (.branch 29 (.leaf ![17, 10, 4, 15]) (.leaf ![17, 10, 4, 15])) (.branch 31 (.leaf ![17, 10, 4, 15]) (.leaf ![19, 18, 19, 0]))))))

@[expose] public def factorBlock2 : Lean.RArray (Fin 4 → Fin 20) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![19, 18, 19, 0]) (.leaf ![19, 18, 19, 0])) (.branch 3 (.leaf ![19, 18, 19, 0]) (.leaf ![19, 18, 19, 0]))) (.branch 6 (.branch 5 (.leaf ![19, 18, 19, 0]) (.leaf ![19, 18, 19, 0])) (.branch 7 (.leaf ![19, 18, 19, 0]) (.leaf ![19, 18, 19, 0])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![11, 13, 16, 15]) (.leaf ![11, 13, 16, 15])) (.branch 11 (.leaf ![11, 13, 16, 15]) (.leaf ![11, 13, 16, 15]))) (.branch 14 (.branch 13 (.leaf ![11, 13, 16, 15]) (.leaf ![11, 13, 16, 15])) (.branch 15 (.leaf ![11, 13, 16, 15]) (.leaf ![11, 13, 16, 15]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![11, 13, 16, 15]) (.leaf ![14, 3, 6, 10])) (.branch 19 (.leaf ![14, 3, 6, 10]) (.leaf ![14, 3, 6, 10]))) (.branch 22 (.branch 21 (.leaf ![14, 3, 6, 10]) (.leaf ![14, 3, 6, 10])) (.branch 23 (.leaf ![14, 3, 6, 10]) (.leaf ![14, 3, 6, 10])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![14, 3, 6, 10]) (.leaf ![14, 3, 6, 10])) (.branch 27 (.leaf ![5, 18, 19, 18]) (.leaf ![5, 18, 19, 18]))) (.branch 30 (.branch 29 (.leaf ![5, 18, 19, 18]) (.leaf ![5, 18, 19, 18])) (.branch 31 (.leaf ![5, 18, 19, 18]) (.leaf ![5, 18, 19, 18]))))))

@[expose] public def factorBlock3 : Lean.RArray (Fin 4 → Fin 20) := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf ![5, 18, 19, 18]) (.leaf ![5, 18, 19, 18])) (.branch 3 (.leaf ![5, 18, 19, 18]) (.branch 4 (.leaf ![9, 13, 12, 3]) (.leaf ![9, 13, 12, 3])))) (.branch 7 (.branch 6 (.leaf ![9, 13, 12, 3]) (.leaf ![9, 13, 12, 3])) (.branch 8 (.leaf ![9, 13, 12, 3]) (.branch 9 (.leaf ![9, 13, 12, 3]) (.leaf ![9, 13, 12, 3]))))) (.branch 15 (.branch 12 (.branch 11 (.leaf ![9, 13, 12, 3]) (.leaf ![9, 13, 12, 3])) (.branch 13 (.leaf ![8, 3, 7, 13]) (.branch 14 (.leaf ![8, 3, 7, 13]) (.leaf ![8, 3, 7, 13])))) (.branch 18 (.branch 16 (.leaf ![8, 3, 7, 13]) (.branch 17 (.leaf ![8, 3, 7, 13]) (.leaf ![8, 3, 7, 13]))) (.branch 19 (.leaf ![8, 3, 7, 13]) (.branch 20 (.leaf ![8, 3, 7, 13]) (.leaf ![8, 3, 7, 13]))))))
@[expose] public def codes : Fin 117 → MatrixCode := fun j =>
  ((.branch 2 (.branch 1 (.leaf codeBlock0) (.leaf codeBlock1)) (.branch 3 (.leaf codeBlock2) (.leaf codeBlock3))) : Lean.RArray (Lean.RArray (MatrixCode))).get (j.val / 32) |>.get (j.val % 32)
@[expose] public def detCheck (k : Nat) : Bool := (codeDet (codes ⟨k % 117, Nat.mod_lt _ (by decide)⟩)).val == 1
set_option maxHeartbeats 4000000 in
private theorem detCheck_0 : checkRange detCheck 0 64 = true := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem detCheck_1 : checkRange detCheck 64 53 = true := by decide +kernel

public theorem det : ∀ j, codeDet (codes j) = 1 := by
  have h := checkRange_fin (by decide : 0 < 117)
    (fun j => (codeDet (codes j)).val == 1) (checkRange_append detCheck_0 detCheck_1)
  intro j
  apply Fin.ext
  exact beq_iff_eq.mp (h j)
@[expose] public def rep (j : Fin 117) : SL := finiteModelEquiv ⟨codes j, det j⟩
@[expose] public def words : Fin 20 → List (Fin 4) := fun j =>
  ((.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf []) (.leaf [0])) (.branch 3 (.leaf [2]) (.branch 4 (.leaf [0, 3]) (.leaf [1, 1])))) (.branch 7 (.branch 6 (.leaf [3, 3]) (.leaf [0, 1, 1])) (.branch 8 (.leaf [2, 1, 1]) (.branch 9 (.leaf [3, 2, 1]) (.leaf [3, 3, 2]))))) (.branch 15 (.branch 12 (.branch 11 (.leaf [0, 1, 1, 0]) (.leaf [0, 3, 3, 3])) (.branch 13 (.leaf [1, 1, 0, 3]) (.branch 14 (.leaf [1, 1, 1, 0]) (.leaf [2, 1, 1, 1])))) (.branch 17 (.branch 16 (.leaf [2, 3, 3, 2]) (.leaf [3, 3, 2, 1])) (.branch 18 (.leaf [0, 1, 0, 1, 1]) (.branch 19 (.leaf [0, 1, 0, 3, 3]) (.leaf [0, 3, 3, 2, 1])))))) : Lean.RArray (List (Fin 4))).get j.val
@[expose] public def wordCodes : Fin 20 → MatrixCode := fun j =>
  ((.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf 6643) (.leaf 11017)) (.branch 3 (.leaf 8830) (.branch 4 (.leaf 13703) (.leaf 2686)))) (.branch 7 (.branch 6 (.leaf 4639) (.leaf 9247)) (.branch 8 (.leaf 15808) (.branch 9 (.leaf 4804) (.leaf 4717))))) (.branch 15 (.branch 12 (.branch 11 (.leaf 7138) (.leaf 2534)) (.branch 13 (.leaf 15578) (.branch 14 (.leaf 13469) (.leaf 2612)))) (.branch 17 (.branch 16 (.leaf 6904) (.leaf 9017)) (.branch 18 (.leaf 6725) (.branch 19 (.leaf 13208) (.leaf 2456)))))) : Lean.RArray MatrixCode).get j.val
set_option maxHeartbeats 4000000 in
public theorem wordEval : ∀ j, (evalWord (nodeGenerator 33) (words j)).val =
    decodeMatrix (wordCodes j) := by decide +kernel
@[expose] public def next : Fin 117 → Fin 4 → Fin 117 := fun j =>
  ((.branch 2 (.branch 1 (.leaf nextBlock0) (.leaf nextBlock1)) (.branch 3 (.leaf nextBlock2) (.leaf nextBlock3))) : Lean.RArray (Lean.RArray (Fin 4 → Fin 117))).get (j.val / 32) |>.get (j.val % 32)
@[expose] public def factorIndex : Fin 117 → Fin 4 → Fin 20 := fun j =>
  ((.branch 2 (.branch 1 (.leaf factorBlock0) (.leaf factorBlock1)) (.branch 3 (.leaf factorBlock2) (.leaf factorBlock3))) : Lean.RArray (Lean.RArray (Fin 4 → Fin 20))).get (j.val / 32) |>.get (j.val % 32)
@[expose] public def table : RightCosetTable 4 4 117 where
  base := 0
  next := next
  factor := fun j k => words (factorIndex j k)
@[expose] public def transitionCheck (j : Fin 117) : Bool :=
  matrixEq ((rep j).val * (ambientGenerator 0).val)
    (decodeMatrix (wordCodes (factorIndex j 0)) * (rep (next j 0)).val) &&
  matrixEq ((rep j).val * (ambientGenerator 1).val)
    (decodeMatrix (wordCodes (factorIndex j 1)) * (rep (next j 1)).val) &&
  matrixEq ((rep j).val * (ambientGenerator 2).val)
    (decodeMatrix (wordCodes (factorIndex j 2)) * (rep (next j 2)).val) &&
  matrixEq ((rep j).val * (ambientGenerator 3).val)
    (decodeMatrix (wordCodes (factorIndex j 3)) * (rep (next j 3)).val)
@[expose] public def rowCheck (k : Nat) : Bool := transitionCheck ⟨k % 117, Nat.mod_lt _ (by decide)⟩
set_option maxHeartbeats 4000000 in
private theorem rowCheck_0 : checkRange rowCheck 0 64 = true := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem rowCheck_1 : checkRange rowCheck 64 53 = true := by decide +kernel

public theorem checked : ∀ j, transitionCheck j = true :=
  checkRange_fin (by decide) transitionCheck (checkRange_append rowCheck_0 rowCheck_1)
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
public theorem valid : table.Valid ambientGenerator (nodeGenerator 33) rep := by
  constructor
  · decide +kernel
  · intro j k
    apply Subtype.ext
    change (rep j).val * (ambientGenerator k).val =
      (evalWord (nodeGenerator 33) (words (factorIndex j k))).val * (rep (next j k)).val
    rw [wordEval]
    exact transitions j k
public theorem cover : RightCosetCover (properNode 33) rep := by
  rw [properNode_eq_wordSubgroup]
  exact table.sound ambientGenerator ambientInverse ambientGenerator_inv
    ambient_wordSubgroup_eq_top (nodeGenerator 33) (symmInv (n := (generatorCodes 33).length))
    (nodeGenerator_inv 33) rep valid
end Matrix.PSL3Three.CertifiedEnumeration.Cosets33
