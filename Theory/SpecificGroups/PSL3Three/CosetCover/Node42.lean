module
public import Theory.SpecificGroups.PSL3Three.CosetCover.Check
/-!
# Checked right cosets for node 42

These are untrusted matrix codes and subgroup words generated from the fixed
lists in `RepresentativeBounds`. The kernel checks determinants, word values,
and every transition by the four ambient generators. `cover` then follows from
`RightCosetTable.sound`, using the proved generation of the actual SL₃(3).

Source: the elementary coset-table argument in `SubgroupEnumeration` and
GLS III, Theorem 6.5.3. Row zero represents the identity matrix.
-/

namespace Matrix.PSL3Three.CertifiedEnumeration.Cosets42
open Theory.GroupTheory Theory.GroupTheory.SubgroupEnumeration CosetCheck
set_option maxRecDepth 100000

@[expose] public def codeBlock0 : Lean.RArray (MatrixCode) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 6643) (.leaf 828)) (.branch 3 (.leaf 855) (.leaf 882))) (.branch 6 (.branch 5 (.leaf 900) (.leaf 927)) (.branch 7 (.leaf 954) (.leaf 975)))) (.branch 12 (.branch 10 (.branch 9 (.leaf 1002) (.leaf 1029)) (.branch 11 (.leaf 1056) (.leaf 1083))) (.branch 14 (.branch 13 (.leaf 1110) (.leaf 1137)) (.branch 15 (.leaf 1164) (.leaf 1191))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf 1221) (.leaf 1248)) (.branch 19 (.leaf 1275) (.leaf 1302))) (.branch 22 (.branch 21 (.leaf 1329) (.leaf 1356)) (.branch 23 (.leaf 1383) (.leaf 1410)))) (.branch 28 (.branch 26 (.branch 25 (.leaf 1437) (.leaf 2432)) (.branch 27 (.leaf 2459) (.leaf 2486))) (.branch 30 (.branch 29 (.leaf 2513) (.leaf 2540)) (.branch 31 (.leaf 2567) (.leaf 2594))))))

@[expose] public def codeBlock1 : Lean.RArray (MatrixCode) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 2621) (.leaf 2648)) (.branch 3 (.leaf 2701) (.leaf 2728))) (.branch 6 (.branch 5 (.leaf 2755) (.leaf 2782)) (.branch 7 (.leaf 2809) (.leaf 2836)))) (.branch 12 (.branch 10 (.branch 9 (.leaf 2863) (.leaf 2890)) (.branch 11 (.leaf 3161) (.leaf 3188))) (.branch 14 (.branch 13 (.leaf 3215) (.leaf 3242)) (.branch 15 (.leaf 3269) (.leaf 3296))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf 3323) (.leaf 3350)) (.branch 19 (.leaf 3377) (.leaf 3403))) (.branch 22 (.branch 21 (.leaf 3430) (.leaf 3457)) (.branch 23 (.leaf 3484) (.leaf 3511)))) (.branch 28 (.branch 26 (.branch 25 (.leaf 3538) (.leaf 3565)) (.branch 27 (.leaf 3592) (.leaf 3619))) (.branch 30 (.branch 29 (.leaf 3890) (.leaf 3917)) (.branch 31 (.leaf 3944) (.leaf 3971))))))

@[expose] public def codeBlock2 : Lean.RArray (MatrixCode) := (.branch 7 (.branch 3 (.branch 1 (.leaf 3998) (.branch 2 (.leaf 4025) (.leaf 4052))) (.branch 5 (.branch 4 (.leaf 4079) (.leaf 4106)) (.branch 6 (.leaf 4132) (.leaf 4159)))) (.branch 10 (.branch 8 (.leaf 4186) (.branch 9 (.leaf 4213) (.leaf 4240))) (.branch 12 (.branch 11 (.leaf 4267) (.leaf 4294)) (.branch 13 (.leaf 4321) (.leaf 4348)))))

@[expose] public def nextBlock0 : Lean.RArray (Fin 4 → Fin 78) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![4, 0, 7, 0]) (.leaf ![16, 5, 25, 6])) (.branch 3 (.leaf ![9, 4, 28, 3]) (.leaf ![8, 2, 31, 4]))) (.branch 6 (.branch 5 (.leaf ![7, 3, 0, 2]) (.leaf ![18, 6, 36, 1])) (.branch 7 (.leaf ![17, 1, 39, 5]) (.leaf ![0, 42, 4, 69])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![31, 46, 3, 74]) (.leaf ![28, 50, 2, 76])) (.branch 11 (.leaf ![51, 45, 26, 75]) (.leaf ![50, 49, 29, 71]))) (.branch 14 (.branch 13 (.leaf ![46, 44, 32, 73]) (.leaf ![69, 48, 34, 72])) (.branch 15 (.leaf ![67, 43, 37, 77]) (.leaf ![65, 47, 40, 70]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![25, 51, 1, 60]) (.leaf ![39, 55, 6, 65])) (.branch 19 (.leaf ![36, 59, 5, 67]) (.leaf ![60, 54, 27, 66]))) (.branch 22 (.branch 21 (.leaf ![76, 58, 30, 62]) (.leaf ![74, 53, 33, 64])) (.branch 23 (.leaf ![42, 57, 35, 63]) (.leaf ![59, 52, 38, 68])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![55, 56, 41, 61]) (.leaf ![1, 25, 16, 25])) (.branch 27 (.leaf ![10, 29, 51, 32]) (.leaf ![19, 33, 60, 30]))) (.branch 30 (.branch 29 (.leaf ![2, 28, 9, 28]) (.leaf ![11, 32, 50, 26])) (.branch 31 (.leaf ![20, 27, 76, 33]) (.leaf ![3, 31, 8, 31]))))))

@[expose] public def nextBlock1 : Lean.RArray (Fin 4 → Fin 78) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![12, 26, 46, 29]) (.leaf ![21, 30, 74, 27])) (.branch 3 (.leaf ![13, 37, 69, 40]) (.leaf ![22, 41, 42, 38]))) (.branch 6 (.branch 5 (.leaf ![5, 36, 18, 36]) (.leaf ![14, 40, 67, 34])) (.branch 7 (.leaf ![23, 35, 59, 41]) (.leaf ![6, 39, 17, 39])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![15, 34, 65, 37]) (.leaf ![24, 38, 55, 35])) (.branch 11 (.leaf ![35, 69, 22, 7]) (.leaf ![68, 77, 57, 14]))) (.branch 14 (.branch 13 (.leaf ![47, 73, 63, 12]) (.leaf ![53, 75, 73, 10])) (.branch 15 (.leaf ![32, 74, 12, 8]) (.leaf ![63, 70, 44, 15]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![71, 72, 49, 13]) (.leaf ![48, 71, 71, 11])) (.branch 19 (.leaf ![29, 76, 11, 9]) (.leaf ![26, 60, 10, 16]))) (.branch 22 (.branch 21 (.leaf ![58, 68, 75, 23]) (.leaf ![73, 64, 45, 21])) (.branch 23 (.leaf ![61, 66, 56, 19]) (.leaf ![41, 65, 24, 17])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![54, 61, 61, 24]) (.leaf ![43, 63, 68, 22])) (.branch 27 (.leaf ![75, 62, 52, 20]) (.leaf ![38, 67, 23, 18]))) (.branch 30 (.branch 29 (.leaf ![27, 16, 19, 51]) (.leaf ![56, 24, 54, 56])) (.branch 31 (.leaf ![77, 20, 66, 58]) (.leaf ![44, 22, 47, 57]))))))

@[expose] public def nextBlock2 : Lean.RArray (Fin 4 → Fin 78) := (.branch 7 (.branch 3 (.branch 1 (.leaf ![72, 21, 70, 53]) (.branch 2 (.leaf ![40, 17, 15, 55]) (.leaf ![62, 19, 77, 54]))) (.branch 5 (.branch 4 (.leaf ![37, 18, 14, 59]) (.leaf ![57, 23, 43, 52])) (.branch 6 (.leaf ![34, 7, 13, 42]) (.leaf ![64, 15, 72, 47])))) (.branch 10 (.branch 8 (.leaf ![49, 11, 48, 49]) (.branch 9 (.leaf ![70, 13, 64, 48]) (.leaf ![45, 12, 53, 44]))) (.branch 12 (.branch 11 (.leaf ![33, 8, 21, 46]) (.leaf ![52, 10, 58, 45])) (.branch 13 (.leaf ![30, 9, 20, 50]) (.leaf ![66, 14, 62, 43])))))

@[expose] public def factorBlock0 : Lean.RArray (Fin 4 → Fin 41) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![27, 29, 0, 30]) (.leaf ![27, 37, 0, 8])) (.branch 3 (.leaf ![5, 34, 0, 27]) (.leaf ![8, 31, 0, 5]))) (.branch 6 (.branch 5 (.leaf ![31, 8, 31, 37]) (.leaf ![37, 27, 0, 34])) (.branch 7 (.leaf ![34, 5, 0, 31]) (.leaf ![0, 1, 27, 40])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![5, 1, 5, 40]) (.leaf ![8, 1, 8, 40])) (.branch 11 (.leaf ![27, 1, 29, 40]) (.leaf ![5, 1, 18, 40]))) (.branch 14 (.branch 13 (.leaf ![8, 1, 23, 40]) (.leaf ![27, 1, 30, 40])) (.branch 15 (.leaf ![5, 1, 14, 40]) (.leaf ![8, 1, 21, 40]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![31, 3, 31, 39]) (.leaf ![37, 3, 37, 39])) (.branch 19 (.leaf ![34, 3, 34, 39]) (.leaf ![31, 3, 30, 39]))) (.branch 22 (.branch 21 (.leaf ![37, 3, 14, 39]) (.leaf ![34, 3, 21, 39])) (.branch 23 (.leaf ![31, 3, 29, 39]) (.leaf ![37, 3, 18, 39])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![34, 3, 23, 39]) (.leaf ![0, 3, 27, 1])) (.branch 27 (.leaf ![30, 3, 17, 1]) (.leaf ![29, 3, 12, 1]))) (.branch 30 (.branch 29 (.leaf ![0, 3, 5, 1]) (.leaf ![14, 3, 9, 1])) (.branch 31 (.leaf ![18, 3, 38, 1]) (.leaf ![0, 3, 8, 1]))))))

@[expose] public def factorBlock1 : Lean.RArray (Fin 4 → Fin 41) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![21, 3, 4, 1]) (.leaf ![23, 3, 33, 1])) (.branch 3 (.leaf ![29, 1, 19, 3]) (.leaf ![30, 1, 24, 3]))) (.branch 6 (.branch 5 (.leaf ![0, 1, 37, 3]) (.leaf ![18, 1, 10, 3])) (.branch 7 (.leaf ![14, 1, 26, 3]) (.leaf ![0, 1, 34, 3])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![23, 1, 7, 3]) (.leaf ![21, 1, 32, 3])) (.branch 11 (.leaf ![13, 39, 27, 3]) (.leaf ![2, 39, 17, 3]))) (.branch 14 (.branch 13 (.leaf ![20, 39, 12, 3]) (.leaf ![13, 39, 38, 3])) (.branch 15 (.leaf ![2, 39, 5, 3]) (.leaf ![20, 39, 9, 3]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![13, 39, 4, 3]) (.leaf ![2, 39, 33, 3])) (.branch 19 (.leaf ![20, 39, 8, 3]) (.leaf ![22, 40, 31, 1]))) (.branch 22 (.branch 21 (.leaf ![36, 40, 19, 1]) (.leaf ![15, 40, 24, 1])) (.branch 23 (.leaf ![22, 40, 26, 1]) (.leaf ![36, 40, 37, 1])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![15, 40, 10, 1]) (.leaf ![22, 40, 7, 1])) (.branch 27 (.leaf ![36, 40, 32, 1]) (.leaf ![15, 40, 34, 1]))) (.branch 30 (.branch 29 (.leaf ![16, 39, 27, 40]) (.leaf ![11, 39, 17, 40])) (.branch 31 (.leaf ![6, 39, 12, 40]) (.leaf ![16, 39, 9, 40]))))))

@[expose] public def factorBlock2 : Lean.RArray (Fin 4 → Fin 41) := (.branch 7 (.branch 3 (.branch 1 (.leaf ![11, 39, 38, 40]) (.branch 2 (.leaf ![6, 39, 5, 40]) (.leaf ![16, 39, 33, 40]))) (.branch 5 (.branch 4 (.leaf ![11, 39, 8, 40]) (.leaf ![6, 39, 4, 40])) (.branch 6 (.leaf ![25, 40, 31, 39]) (.leaf ![28, 40, 19, 39])))) (.branch 10 (.branch 8 (.leaf ![35, 40, 24, 39]) (.branch 9 (.leaf ![25, 40, 10, 39]) (.leaf ![28, 40, 26, 39]))) (.branch 12 (.branch 11 (.leaf ![35, 40, 37, 39]) (.leaf ![25, 40, 32, 39])) (.branch 13 (.leaf ![28, 40, 34, 39]) (.leaf ![35, 40, 7, 39])))))
@[expose] public def codes : Fin 78 → MatrixCode := fun j =>
  ((.branch 1 (.leaf codeBlock0) (.branch 2 (.leaf codeBlock1) (.leaf codeBlock2))) : Lean.RArray (Lean.RArray (MatrixCode))).get (j.val / 32) |>.get (j.val % 32)
@[expose] public def detCheck (k : Nat) : Bool := (codeDet (codes ⟨k % 78, Nat.mod_lt _ (by decide)⟩)).val == 1
set_option maxHeartbeats 4000000 in
private theorem detCheck_0 : checkRange detCheck 0 64 = true := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem detCheck_1 : checkRange detCheck 64 14 = true := by decide +kernel

public theorem det : ∀ j, codeDet (codes j) = 1 := by
  have h := checkRange_fin (by decide : 0 < 78)
    (fun j => (codeDet (codes j)).val == 1) (checkRange_append detCheck_0 detCheck_1)
  intro j
  apply Fin.ext
  exact beq_iff_eq.mp (h j)
@[expose] public def rep (j : Fin 78) : SL := finiteModelEquiv ⟨codes j, det j⟩
@[expose] public def words : Fin 41 → List (Fin 4) := fun j =>
  ((.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf []) (.leaf [0])) (.branch 3 (.leaf [1]) (.branch 4 (.leaf [2]) (.leaf [3])))) (.branch 7 (.branch 6 (.leaf [0, 1]) (.leaf [2, 1])) (.branch 8 (.leaf [3, 0]) (.branch 9 (.leaf [3, 2]) (.leaf [0, 1, 0]))))) (.branch 15 (.branch 12 (.branch 11 (.leaf [0, 1, 2]) (.leaf [0, 3, 2])) (.branch 13 (.leaf [0, 3, 3]) (.branch 14 (.leaf [1, 0, 1]) (.leaf [1, 0, 3])))) (.branch 17 (.branch 16 (.leaf [1, 1, 1]) (.leaf [1, 1, 2])) (.branch 18 (.leaf [1, 2, 1]) (.branch 19 (.leaf [1, 2, 3]) (.leaf [2, 1, 1])))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf [2, 3, 2]) (.leaf [3, 0, 1])) (.branch 23 (.leaf [3, 0, 3]) (.branch 24 (.leaf [3, 2, 1]) (.leaf [3, 2, 3])))) (.branch 27 (.branch 26 (.leaf [3, 3, 0]) (.leaf [3, 3, 3])) (.branch 28 (.leaf [0, 1, 0, 1]) (.branch 29 (.leaf [0, 1, 1, 1]) (.leaf [0, 1, 2, 3]))))) (.branch 35 (.branch 32 (.branch 31 (.leaf [0, 3, 0, 1]) (.leaf [0, 3, 3, 0])) (.branch 33 (.leaf [1, 0, 1, 1]) (.branch 34 (.leaf [1, 1, 0, 1]) (.leaf [2, 1, 1, 1])))) (.branch 38 (.branch 36 (.leaf [3, 2, 3, 3]) (.branch 37 (.leaf [3, 3, 2, 3]) (.leaf [3, 3, 3, 0]))) (.branch 39 (.leaf [3, 3, 3, 2]) (.branch 40 (.leaf [1, 1, 1, 0, 1]) (.leaf [1, 2, 1, 1, 1]))))))) : Lean.RArray (List (Fin 4))).get j.val
@[expose] public def wordCodes : Fin 41 → MatrixCode := fun j =>
  ((.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf 6643) (.leaf 6652)) (.branch 3 (.leaf 9341) (.branch 4 (.leaf 6661) (.leaf 15977)))) (.branch 7 (.branch 6 (.leaf 9317) (.leaf 9329)) (.branch 8 (.leaf 15968) (.branch 9 (.leaf 15959) (.leaf 9335))))) (.branch 15 (.branch 12 (.branch 11 (.leaf 9326) (.leaf 15980)) (.branch 13 (.leaf 2692) (.branch 14 (.leaf 4621) (.leaf 6658)))) (.branch 17 (.branch 16 (.leaf 11276) (.leaf 4624)) (.branch 18 (.leaf 4636) (.branch 19 (.leaf 6664) (.leaf 4627)))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf 15974) (.leaf 6667)) (.branch 23 (.leaf 2677) (.branch 24 (.leaf 6655) (.leaf 2683)))) (.branch 27 (.branch 26 (.leaf 2680) (.leaf 17912)) (.branch 28 (.leaf 4618) (.branch 29 (.leaf 11282) (.leaf 6646))))) (.branch 35 (.branch 32 (.branch 31 (.leaf 6649) (.leaf 2674)) (.branch 33 (.leaf 11270) (.branch 34 (.leaf 11279) (.leaf 11261)))) (.branch 38 (.branch 36 (.leaf 17915) (.branch 37 (.leaf 17927) (.leaf 17903))) (.branch 39 (.leaf 17921) (.branch 40 (.leaf 13303) (.leaf 13294))))))) : Lean.RArray MatrixCode).get j.val
set_option maxHeartbeats 4000000 in
public theorem wordEval : ∀ j, (evalWord (nodeGenerator 42) (words j)).val =
    decodeMatrix (wordCodes j) := by decide +kernel
@[expose] public def next : Fin 78 → Fin 4 → Fin 78 := fun j =>
  ((.branch 1 (.leaf nextBlock0) (.branch 2 (.leaf nextBlock1) (.leaf nextBlock2))) : Lean.RArray (Lean.RArray (Fin 4 → Fin 78))).get (j.val / 32) |>.get (j.val % 32)
@[expose] public def factorIndex : Fin 78 → Fin 4 → Fin 41 := fun j =>
  ((.branch 1 (.leaf factorBlock0) (.branch 2 (.leaf factorBlock1) (.leaf factorBlock2))) : Lean.RArray (Lean.RArray (Fin 4 → Fin 41))).get (j.val / 32) |>.get (j.val % 32)
@[expose] public def table : RightCosetTable 4 4 78 where
  base := 0
  next := next
  factor := fun j k => words (factorIndex j k)
@[expose] public def transitionCheck (j : Fin 78) : Bool :=
  matrixEq ((rep j).val * (ambientGenerator 0).val)
    (decodeMatrix (wordCodes (factorIndex j 0)) * (rep (next j 0)).val) &&
  matrixEq ((rep j).val * (ambientGenerator 1).val)
    (decodeMatrix (wordCodes (factorIndex j 1)) * (rep (next j 1)).val) &&
  matrixEq ((rep j).val * (ambientGenerator 2).val)
    (decodeMatrix (wordCodes (factorIndex j 2)) * (rep (next j 2)).val) &&
  matrixEq ((rep j).val * (ambientGenerator 3).val)
    (decodeMatrix (wordCodes (factorIndex j 3)) * (rep (next j 3)).val)
@[expose] public def rowCheck (k : Nat) : Bool := transitionCheck ⟨k % 78, Nat.mod_lt _ (by decide)⟩
set_option maxHeartbeats 4000000 in
private theorem rowCheck_0 : checkRange rowCheck 0 64 = true := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem rowCheck_1 : checkRange rowCheck 64 14 = true := by decide +kernel

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
public theorem valid : table.Valid ambientGenerator (nodeGenerator 42) rep := by
  constructor
  · decide +kernel
  · intro j k
    apply Subtype.ext
    change (rep j).val * (ambientGenerator k).val =
      (evalWord (nodeGenerator 42) (words (factorIndex j k))).val * (rep (next j k)).val
    rw [wordEval]
    exact transitions j k
public theorem cover : RightCosetCover (properNode 42) rep := by
  rw [properNode_eq_wordSubgroup]
  exact table.sound ambientGenerator ambientInverse ambientGenerator_inv
    ambient_wordSubgroup_eq_top (nodeGenerator 42) (symmInv (n := (generatorCodes 42).length))
    (nodeGenerator_inv 42) rep valid
end Matrix.PSL3Three.CertifiedEnumeration.Cosets42
