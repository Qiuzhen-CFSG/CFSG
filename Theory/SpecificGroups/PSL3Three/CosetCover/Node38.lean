module
public import Theory.SpecificGroups.PSL3Three.CosetCover.Check
/-!
# Checked right cosets for node 38

These are untrusted matrix codes and subgroup words generated from the fixed
lists in `RepresentativeBounds`. The kernel checks determinants, word values,
and every transition by the four ambient generators. `cover` then follows from
`RightCosetTable.sound`, using the proved generation of the actual SL₃(3).

Source: the elementary coset-table argument in `SubgroupEnumeration` and
GLS III, Theorem 6.5.3. Row zero represents the identity matrix.
-/

namespace Matrix.PSL3Three.CertifiedEnumeration.Cosets38
open Theory.GroupTheory Theory.GroupTheory.SubgroupEnumeration CosetCheck
set_option maxRecDepth 100000

@[expose] public def codeBlock0 : Lean.RArray (MatrixCode) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 6643) (.leaf 828)) (.branch 3 (.leaf 855) (.leaf 882))) (.branch 6 (.branch 5 (.leaf 900) (.leaf 927)) (.branch 7 (.leaf 954) (.leaf 975)))) (.branch 12 (.branch 10 (.branch 9 (.leaf 1002) (.leaf 1029)) (.branch 11 (.leaf 1056) (.leaf 1083))) (.branch 14 (.branch 13 (.leaf 1110) (.leaf 1137)) (.branch 15 (.leaf 1164) (.leaf 1191))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf 1221) (.leaf 1248)) (.branch 19 (.leaf 1275) (.leaf 1302))) (.branch 22 (.branch 21 (.leaf 1329) (.leaf 1356)) (.branch 23 (.leaf 1383) (.leaf 1410)))) (.branch 28 (.branch 26 (.branch 25 (.leaf 1437) (.leaf 2432)) (.branch 27 (.leaf 2459) (.leaf 2486))) (.branch 30 (.branch 29 (.leaf 2513) (.leaf 2540)) (.branch 31 (.leaf 2567) (.leaf 2594))))))

@[expose] public def codeBlock1 : Lean.RArray (MatrixCode) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 2621) (.leaf 2648)) (.branch 3 (.leaf 2701) (.leaf 2728))) (.branch 6 (.branch 5 (.leaf 2755) (.leaf 2782)) (.branch 7 (.leaf 2809) (.leaf 2836)))) (.branch 12 (.branch 10 (.branch 9 (.leaf 2863) (.leaf 2890)) (.branch 11 (.leaf 3161) (.leaf 3188))) (.branch 14 (.branch 13 (.leaf 3215) (.leaf 3242)) (.branch 15 (.leaf 3269) (.leaf 3296))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf 3323) (.leaf 3350)) (.branch 19 (.leaf 3377) (.leaf 3403))) (.branch 22 (.branch 21 (.leaf 3430) (.leaf 3457)) (.branch 23 (.leaf 3484) (.leaf 3511)))) (.branch 28 (.branch 26 (.branch 25 (.leaf 3538) (.leaf 3565)) (.branch 27 (.leaf 3592) (.leaf 3619))) (.branch 30 (.branch 29 (.leaf 3890) (.leaf 3917)) (.branch 31 (.leaf 3944) (.leaf 3971))))))

@[expose] public def codeBlock2 : Lean.RArray (MatrixCode) := (.branch 7 (.branch 3 (.branch 1 (.leaf 3998) (.branch 2 (.leaf 4025) (.leaf 4052))) (.branch 5 (.branch 4 (.leaf 4079) (.leaf 4106)) (.branch 6 (.leaf 4132) (.leaf 4159)))) (.branch 10 (.branch 8 (.leaf 4186) (.branch 9 (.leaf 4213) (.leaf 4240))) (.branch 12 (.branch 11 (.leaf 4267) (.leaf 4294)) (.branch 13 (.leaf 4321) (.leaf 4348)))))

@[expose] public def nextBlock0 : Lean.RArray (Fin 4 → Fin 78) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![4, 0, 7, 0]) (.leaf ![16, 3, 25, 2])) (.branch 3 (.leaf ![17, 1, 28, 3]) (.leaf ![18, 2, 31, 1]))) (.branch 6 (.branch 5 (.leaf ![7, 5, 0, 6]) (.leaf ![8, 6, 36, 4])) (.branch 7 (.leaf ![9, 4, 39, 5]) (.leaf ![0, 42, 4, 69])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![36, 46, 5, 74]) (.leaf ![39, 50, 6, 76])) (.branch 11 (.leaf ![51, 45, 26, 75]) (.leaf ![55, 49, 29, 71]))) (.branch 14 (.branch 13 (.leaf ![59, 44, 32, 73]) (.leaf ![69, 48, 34, 72])) (.branch 15 (.leaf ![74, 43, 37, 77]) (.leaf ![76, 47, 40, 70]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![25, 51, 1, 60]) (.leaf ![28, 55, 2, 65])) (.branch 19 (.leaf ![31, 59, 3, 67]) (.leaf ![60, 54, 27, 66]))) (.branch 22 (.branch 21 (.leaf ![65, 58, 30, 62]) (.leaf ![67, 53, 33, 64])) (.branch 23 (.leaf ![42, 57, 35, 63]) (.leaf ![46, 52, 38, 68])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![50, 56, 41, 61]) (.leaf ![1, 25, 16, 25])) (.branch 27 (.leaf ![10, 29, 51, 32]) (.leaf ![19, 33, 60, 30]))) (.branch 30 (.branch 29 (.leaf ![2, 28, 17, 28]) (.leaf ![11, 32, 55, 26])) (.branch 31 (.leaf ![20, 27, 65, 33]) (.leaf ![3, 31, 18, 31]))))))

@[expose] public def nextBlock1 : Lean.RArray (Fin 4 → Fin 78) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![12, 26, 59, 29]) (.leaf ![21, 30, 67, 27])) (.branch 3 (.leaf ![13, 37, 69, 40]) (.leaf ![22, 41, 42, 38]))) (.branch 6 (.branch 5 (.leaf ![5, 36, 8, 36]) (.leaf ![14, 40, 74, 34])) (.branch 7 (.leaf ![23, 35, 46, 41]) (.leaf ![6, 39, 9, 39])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![15, 34, 76, 37]) (.leaf ![24, 38, 50, 35])) (.branch 11 (.leaf ![35, 69, 22, 7]) (.leaf ![73, 77, 57, 14]))) (.branch 14 (.branch 13 (.leaf ![58, 73, 63, 12]) (.leaf ![53, 75, 68, 10])) (.branch 15 (.leaf ![38, 74, 23, 8]) (.leaf ![75, 70, 52, 15]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![71, 72, 56, 13]) (.leaf ![54, 71, 61, 11])) (.branch 19 (.leaf ![41, 76, 24, 9]) (.leaf ![26, 60, 10, 16]))) (.branch 22 (.branch 21 (.leaf ![47, 68, 75, 23]) (.leaf ![68, 64, 45, 21])) (.branch 23 (.leaf ![61, 66, 49, 19]) (.leaf ![29, 65, 11, 17])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![48, 61, 71, 24]) (.leaf ![43, 63, 73, 22])) (.branch 27 (.leaf ![63, 62, 44, 20]) (.leaf ![32, 67, 12, 18]))) (.branch 30 (.branch 29 (.leaf ![27, 16, 19, 51]) (.leaf ![49, 24, 54, 56])) (.branch 31 (.leaf ![64, 20, 66, 58]) (.leaf ![44, 22, 58, 57]))))))

@[expose] public def nextBlock2 : Lean.RArray (Fin 4 → Fin 78) := (.branch 7 (.branch 3 (.branch 1 (.leaf ![66, 21, 62, 53]) (.branch 2 (.leaf ![30, 17, 20, 55]) (.leaf ![62, 19, 64, 54]))) (.branch 5 (.branch 4 (.leaf ![33, 18, 21, 59]) (.leaf ![45, 23, 53, 52])) (.branch 6 (.leaf ![34, 7, 13, 42]) (.leaf ![77, 15, 72, 47])))) (.branch 10 (.branch 8 (.leaf ![56, 11, 48, 49]) (.branch 9 (.leaf ![70, 13, 77, 48]) (.leaf ![57, 12, 43, 44]))) (.branch 12 (.branch 11 (.leaf ![37, 8, 14, 46]) (.leaf ![52, 10, 47, 45])) (.branch 13 (.leaf ![40, 9, 15, 50]) (.leaf ![72, 14, 70, 43])))))

@[expose] public def factorBlock0 : Lean.RArray (Fin 4 → Fin 41) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![7, 28, 0, 26]) (.leaf ![7, 24, 0, 5])) (.branch 3 (.leaf ![23, 17, 0, 7]) (.leaf ![5, 13, 0, 23]))) (.branch 6 (.branch 5 (.leaf ![13, 5, 13, 24]) (.leaf ![24, 7, 0, 17])) (.branch 7 (.leaf ![17, 23, 0, 13]) (.leaf ![0, 33, 7, 31])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![23, 33, 23, 31]) (.leaf ![5, 33, 5, 31])) (.branch 11 (.leaf ![7, 33, 28, 31]) (.leaf ![23, 33, 21, 31]))) (.branch 14 (.branch 13 (.leaf ![5, 33, 30, 31]) (.leaf ![7, 33, 26, 31])) (.branch 15 (.leaf ![23, 33, 32, 31]) (.leaf ![5, 33, 27, 31]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![13, 35, 13, 25]) (.leaf ![24, 35, 24, 25])) (.branch 19 (.leaf ![17, 35, 17, 25]) (.leaf ![13, 35, 26, 25]))) (.branch 22 (.branch 21 (.leaf ![24, 35, 32, 25]) (.leaf ![17, 35, 27, 25])) (.branch 23 (.leaf ![13, 35, 28, 25]) (.leaf ![24, 35, 21, 25])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![17, 35, 30, 25]) (.leaf ![0, 35, 7, 33])) (.branch 27 (.leaf ![26, 35, 18, 33]) (.leaf ![28, 35, 37, 33]))) (.branch 30 (.branch 29 (.leaf ![0, 35, 23, 33]) (.leaf ![32, 35, 2, 33])) (.branch 31 (.leaf ![21, 35, 3, 33]) (.leaf ![0, 35, 5, 33]))))))

@[expose] public def factorBlock1 : Lean.RArray (Fin 4 → Fin 41) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![27, 35, 39, 33]) (.leaf ![30, 35, 10, 33])) (.branch 3 (.leaf ![28, 33, 14, 35]) (.leaf ![26, 33, 15, 35]))) (.branch 6 (.branch 5 (.leaf ![0, 33, 24, 35]) (.leaf ![21, 33, 29, 35])) (.branch 7 (.leaf ![32, 33, 36, 35]) (.leaf ![0, 33, 17, 35])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![30, 33, 11, 35]) (.leaf ![27, 33, 16, 35])) (.branch 11 (.leaf ![12, 25, 7, 35]) (.leaf ![34, 25, 18, 35]))) (.branch 14 (.branch 13 (.leaf ![9, 25, 37, 35]) (.leaf ![12, 25, 3, 35])) (.branch 15 (.leaf ![34, 25, 23, 35]) (.leaf ![9, 25, 2, 35]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![12, 25, 39, 35]) (.leaf ![34, 25, 10, 35])) (.branch 19 (.leaf ![9, 25, 5, 35]) (.leaf ![20, 31, 13, 33]))) (.branch 22 (.branch 21 (.leaf ![1, 31, 14, 33]) (.leaf ![40, 31, 15, 33])) (.branch 23 (.leaf ![20, 31, 36, 33]) (.leaf ![1, 31, 24, 33])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![40, 31, 29, 33]) (.leaf ![20, 31, 11, 33])) (.branch 27 (.leaf ![1, 31, 16, 33]) (.leaf ![40, 31, 17, 33]))) (.branch 30 (.branch 29 (.leaf ![38, 25, 7, 31]) (.leaf ![8, 25, 18, 31])) (.branch 31 (.leaf ![4, 25, 37, 31]) (.leaf ![38, 25, 2, 31]))))))

@[expose] public def factorBlock2 : Lean.RArray (Fin 4 → Fin 41) := (.branch 7 (.branch 3 (.branch 1 (.leaf ![8, 25, 3, 31]) (.branch 2 (.leaf ![4, 25, 23, 31]) (.leaf ![38, 25, 10, 31]))) (.branch 5 (.branch 4 (.leaf ![8, 25, 5, 31]) (.leaf ![4, 25, 39, 31])) (.branch 6 (.leaf ![19, 31, 13, 25]) (.leaf ![6, 31, 14, 25])))) (.branch 10 (.branch 8 (.leaf ![22, 31, 15, 25]) (.branch 9 (.leaf ![19, 31, 29, 25]) (.leaf ![6, 31, 36, 25]))) (.branch 12 (.branch 11 (.leaf ![22, 31, 24, 25]) (.leaf ![19, 31, 16, 25])) (.branch 13 (.leaf ![6, 31, 17, 25]) (.leaf ![22, 31, 11, 25])))))
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
  ((.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf []) (.leaf [0, 3])) (.branch 3 (.leaf [1, 2]) (.branch 4 (.leaf [2, 1]) (.leaf [3, 0])))) (.branch 7 (.branch 6 (.leaf [0, 0, 1]) (.leaf [0, 0, 3])) (.branch 8 (.leaf [0, 1, 1]) (.branch 9 (.leaf [0, 1, 2]) (.leaf [0, 3, 0]))))) (.branch 15 (.branch 12 (.branch 11 (.leaf [0, 3, 2]) (.leaf [1, 0, 0])) (.branch 13 (.leaf [1, 1, 0]) (.branch 14 (.leaf [1, 1, 2]) (.leaf [1, 2, 1])))) (.branch 17 (.branch 16 (.leaf [2, 1, 1]) (.leaf [2, 1, 2])) (.branch 18 (.leaf [3, 0, 0]) (.branch 19 (.leaf [3, 0, 1]) (.leaf [3, 0, 3])))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf [3, 2, 1]) (.leaf [0, 0, 1, 1])) (.branch 23 (.leaf [0, 0, 1, 2]) (.branch 24 (.leaf [0, 0, 3, 2]) (.leaf [0, 1, 0, 0])))) (.branch 27 (.branch 26 (.leaf [0, 1, 0, 1]) (.leaf [0, 1, 0, 3])) (.branch 28 (.leaf [0, 1, 1, 0]) (.branch 29 (.leaf [0, 1, 2, 1]) (.leaf [0, 3, 0, 0]))))) (.branch 35 (.branch 32 (.branch 31 (.leaf [0, 3, 0, 1]) (.leaf [0, 3, 2, 1])) (.branch 33 (.leaf [0, 3, 2, 3]) (.branch 34 (.leaf [1, 0, 3, 0]) (.leaf [1, 1, 2, 1])))) (.branch 38 (.branch 36 (.leaf [1, 2, 1, 0]) (.branch 37 (.leaf [3, 0, 1, 1]) (.leaf [0, 0, 1, 2, 1]))) (.branch 39 (.leaf [0, 0, 1, 2, 3]) (.branch 40 (.leaf [0, 1, 1, 2, 1]) (.leaf [0, 3, 0, 1, 1]))))))) : Lean.RArray (List (Fin 4))).get j.val
@[expose] public def wordCodes : Fin 41 → MatrixCode := fun j =>
  ((.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf 6643) (.leaf 15655)) (.branch 3 (.leaf 11602) (.branch 4 (.leaf 15652) (.leaf 11599)))) (.branch 7 (.branch 6 (.leaf 18064) (.leaf 9178)) (.branch 8 (.leaf 4618) (.branch 9 (.leaf 18088) (.leaf 18076))))) (.branch 15 (.branch 12 (.branch 11 (.leaf 9172) (.leaf 18073)) (.branch 13 (.leaf 4621) (.branch 14 (.leaf 2674) (.leaf 4627)))) (.branch 17 (.branch 16 (.leaf 2683) (.leaf 9163)) (.branch 18 (.leaf 9154) (.branch 19 (.leaf 4636) (.leaf 2680)))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf 2677) (.leaf 6664)) (.branch 23 (.leaf 15649) (.branch 24 (.leaf 11584) (.leaf 15634)))) (.branch 27 (.branch 26 (.leaf 13303) (.leaf 6649)) (.branch 28 (.leaf 6667) (.branch 29 (.leaf 6646) (.leaf 11593))))) (.branch 35 (.branch 32 (.branch 31 (.leaf 6655) (.leaf 13294)) (.branch 33 (.leaf 6658) (.branch 34 (.leaf 6652) (.leaf 11605)))) (.branch 38 (.branch 36 (.leaf 6661) (.branch 37 (.leaf 15643) (.leaf 2692))) (.branch 39 (.leaf 4624) (.branch 40 (.leaf 18082) (.leaf 9166))))))) : Lean.RArray MatrixCode).get j.val
set_option maxHeartbeats 4000000 in
public theorem wordEval : ∀ j, (evalWord (nodeGenerator 38) (words j)).val =
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
public theorem valid : table.Valid ambientGenerator (nodeGenerator 38) rep := by
  constructor
  · decide +kernel
  · intro j k
    apply Subtype.ext
    change (rep j).val * (ambientGenerator k).val =
      (evalWord (nodeGenerator 38) (words (factorIndex j k))).val * (rep (next j k)).val
    rw [wordEval]
    exact transitions j k
public theorem cover : RightCosetCover (properNode 38) rep := by
  rw [properNode_eq_wordSubgroup]
  exact table.sound ambientGenerator ambientInverse ambientGenerator_inv
    ambient_wordSubgroup_eq_top (nodeGenerator 38) (symmInv (n := (generatorCodes 38).length))
    (nodeGenerator_inv 38) rep valid
end Matrix.PSL3Three.CertifiedEnumeration.Cosets38
