module
public import Theory.SpecificGroups.PSL3Three.CosetCover.Check
/-!
# Checked right cosets for node 40

These are untrusted matrix codes and subgroup words generated from the fixed
lists in `RepresentativeBounds`. The kernel checks determinants, word values,
and every transition by the four ambient generators. `cover` then follows from
`RightCosetTable.sound`, using the proved generation of the actual SL₃(3).

Source: the elementary coset-table argument in `SubgroupEnumeration` and
GLS III, Theorem 6.5.3. Row zero represents the identity matrix.
-/

namespace Matrix.PSL3Three.CertifiedEnumeration.Cosets40
open Theory.GroupTheory Theory.GroupTheory.SubgroupEnumeration CosetCheck
set_option maxRecDepth 100000

@[expose] public def codeBlock0 : Lean.RArray (MatrixCode) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 6643) (.leaf 828)) (.branch 3 (.leaf 829) (.leaf 830))) (.branch 6 (.branch 5 (.leaf 831) (.leaf 832)) (.branch 7 (.leaf 833) (.leaf 834)))) (.branch 12 (.branch 10 (.branch 9 (.leaf 835) (.leaf 836)) (.branch 11 (.leaf 855) (.leaf 856))) (.branch 14 (.branch 13 (.leaf 857) (.leaf 858)) (.branch 15 (.leaf 859) (.leaf 860))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf 861) (.leaf 862)) (.branch 19 (.leaf 863) (.leaf 882))) (.branch 22 (.branch 21 (.leaf 883) (.leaf 884)) (.branch 23 (.leaf 885) (.leaf 886)))) (.branch 28 (.branch 26 (.branch 25 (.leaf 887) (.leaf 888)) (.branch 27 (.leaf 889) (.leaf 890))) (.branch 30 (.branch 29 (.leaf 900) (.leaf 901)) (.branch 31 (.leaf 902) (.leaf 903))))))

@[expose] public def codeBlock1 : Lean.RArray (MatrixCode) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 904) (.leaf 905)) (.branch 3 (.leaf 906) (.leaf 907))) (.branch 6 (.branch 5 (.leaf 908) (.leaf 927)) (.branch 7 (.leaf 928) (.leaf 929)))) (.branch 12 (.branch 10 (.branch 9 (.leaf 930) (.leaf 931)) (.branch 11 (.leaf 932) (.leaf 933))) (.branch 14 (.branch 13 (.leaf 934) (.leaf 935)) (.branch 15 (.leaf 954) (.leaf 955))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf 956) (.leaf 957)) (.branch 19 (.leaf 958) (.leaf 959))) (.branch 22 (.branch 21 (.leaf 960) (.leaf 961)) (.branch 23 (.leaf 962) (.leaf 975)))) (.branch 28 (.branch 26 (.branch 25 (.leaf 976) (.leaf 977)) (.branch 27 (.leaf 1002) (.leaf 1003))) (.branch 30 (.branch 29 (.leaf 1004) (.leaf 1029)) (.branch 31 (.leaf 1030) (.leaf 1031))))))

@[expose] public def codeBlock2 : Lean.RArray (MatrixCode) := (.branch 7 (.branch 3 (.branch 1 (.leaf 1221) (.branch 2 (.leaf 1222) (.leaf 1223))) (.branch 5 (.branch 4 (.leaf 1248) (.leaf 1249)) (.branch 6 (.leaf 1250) (.leaf 1275)))) (.branch 10 (.branch 8 (.leaf 1276) (.branch 9 (.leaf 1277) (.leaf 2432))) (.branch 12 (.branch 11 (.leaf 2513) (.leaf 2594)) (.branch 13 (.leaf 2755) (.leaf 2836)))))

@[expose] public def nextBlock0 : Lean.RArray (Fin 4 → Fin 78) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![28, 56, 55, 65]) (.leaf ![64, 37, 73, 46])) (.branch 3 (.leaf ![34, 45, 57, 51]) (.leaf ![7, 41, 66, 53]))) (.branch 6 (.branch 5 (.leaf ![65, 43, 30, 52]) (.leaf ![44, 42, 17, 48])) (.branch 7 (.leaf ![26, 38, 23, 50]) (.leaf ![66, 40, 3, 49])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![54, 39, 53, 54]) (.leaf ![18, 44, 41, 47])) (.branch 11 (.leaf ![61, 28, 74, 19]) (.leaf ![22, 36, 60, 26]))) (.branch 14 (.branch 13 (.leaf ![49, 32, 69, 24]) (.leaf ![63, 34, 20, 22])) (.branch 15 (.leaf ![15, 33, 33, 20]) (.leaf ![33, 29, 14, 27]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![62, 31, 47, 25]) (.leaf ![5, 30, 44, 23])) (.branch 19 (.leaf ![41, 35, 9, 21]) (.leaf ![58, 10, 75, 28]))) (.branch 22 (.branch 21 (.leaf ![13, 14, 63, 33]) (.leaf ![40, 18, 72, 35])) (.branch 23 (.leaf ![60, 13, 11, 34]) (.leaf ![6, 17, 26, 30])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![51, 12, 36, 32]) (.leaf ![59, 16, 38, 31])) (.branch 27 (.leaf ![23, 11, 6, 36]) (.leaf ![32, 15, 50, 29]))) (.branch 30 (.branch 29 (.leaf ![55, 19, 0, 10]) (.leaf ![31, 27, 56, 15])) (.branch 31 (.leaf ![4, 23, 65, 17]) (.leaf ![56, 25, 29, 16]))))))

@[expose] public def nextBlock1 : Lean.RArray (Fin 4 → Fin 78) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![50, 24, 27, 12]) (.leaf ![14, 20, 15, 14])) (.branch 3 (.leaf ![57, 22, 2, 13]) (.leaf ![42, 21, 45, 18]))) (.branch 6 (.branch 5 (.leaf ![24, 26, 51, 11]) (.leaf ![70, 46, 76, 1])) (.branch 7 (.leaf ![25, 50, 59, 6]) (.leaf ![52, 54, 68, 8])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![72, 49, 21, 7]) (.leaf ![9, 53, 18, 3])) (.branch 11 (.leaf ![45, 48, 35, 5]) (.leaf ![71, 52, 48, 4]))) (.branch 14 (.branch 13 (.leaf ![17, 47, 5, 9]) (.leaf ![35, 51, 42, 2])) (.branch 15 (.leaf ![67, 1, 77, 37]) (.leaf ![16, 9, 62, 44]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![43, 5, 71, 42]) (.leaf ![69, 7, 12, 40])) (.branch 19 (.leaf ![27, 6, 32, 38]) (.leaf ![36, 2, 24, 45]))) (.branch 22 (.branch 21 (.leaf ![68, 4, 39, 43]) (.leaf ![8, 3, 54, 41])) (.branch 23 (.leaf ![53, 8, 8, 39]) (.leaf ![0, 55, 28, 55])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![29, 65, 31, 0]) (.leaf ![2, 73, 34, 66])) (.branch 27 (.leaf ![75, 58, 19, 58]) (.leaf ![38, 68, 25, 76]))) (.branch 30 (.branch 29 (.leaf ![11, 74, 22, 69]) (.leaf ![74, 61, 10, 61])) (.branch 31 (.leaf ![47, 71, 16, 77]) (.leaf ![20, 75, 13, 72]))))))

@[expose] public def nextBlock2 : Lean.RArray (Fin 4 → Fin 78) := (.branch 7 (.branch 3 (.branch 1 (.leaf ![73, 64, 1, 64]) (.branch 2 (.leaf ![30, 0, 4, 56]) (.leaf ![3, 57, 7, 73]))) (.branch 5 (.branch 4 (.leaf ![77, 67, 46, 67]) (.leaf ![39, 76, 52, 59])) (.branch 6 (.leaf ![12, 60, 49, 74]) (.leaf ![76, 70, 37, 70])))) (.branch 10 (.branch 8 (.leaf ![48, 77, 43, 62]) (.branch 9 (.leaf ![21, 63, 40, 75]) (.leaf ![1, 66, 64, 57]))) (.branch 12 (.branch 11 (.leaf ![10, 69, 61, 60]) (.leaf ![19, 72, 58, 63])) (.branch 13 (.leaf ![37, 59, 70, 68]) (.leaf ![46, 62, 67, 71])))))

@[expose] public def factorBlock0 : Lean.RArray (Fin 4 → Fin 43) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![33, 11, 0, 20]) (.leaf ![33, 6, 0, 34])) (.branch 3 (.leaf ![16, 6, 32, 34]) (.leaf ![14, 6, 41, 34]))) (.branch 6 (.branch 5 (.leaf ![33, 6, 17, 34]) (.leaf ![16, 6, 18, 34])) (.branch 7 (.leaf ![14, 6, 28, 34]) (.leaf ![33, 6, 8, 34])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![16, 6, 2, 34]) (.leaf ![14, 6, 13, 34])) (.branch 11 (.leaf ![27, 3, 0, 33]) (.leaf ![7, 3, 19, 33]))) (.branch 14 (.branch 13 (.leaf ![26, 3, 42, 33]) (.leaf ![27, 3, 28, 33])) (.branch 15 (.leaf ![7, 3, 17, 33]) (.leaf ![26, 3, 18, 33]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![27, 3, 2, 33]) (.leaf ![7, 3, 13, 33])) (.branch 19 (.leaf ![26, 3, 8, 33]) (.leaf ![34, 30, 0, 27]))) (.branch 22 (.branch 21 (.leaf ![36, 30, 12, 27]) (.leaf ![35, 30, 40, 27])) (.branch 23 (.leaf ![34, 30, 18, 27]) (.leaf ![36, 30, 28, 27])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![35, 30, 17, 27]) (.leaf ![34, 30, 13, 27])) (.branch 27 (.leaf ![36, 30, 8, 27]) (.leaf ![35, 30, 2, 27]))) (.branch 30 (.branch 29 (.leaf ![30, 34, 30, 6]) (.leaf ![9, 34, 25, 6])) (.branch 31 (.leaf ![21, 34, 31, 6]) (.leaf ![30, 34, 20, 6]))))))

@[expose] public def factorBlock1 : Lean.RArray (Fin 4 → Fin 43) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![9, 34, 29, 6]) (.leaf ![21, 34, 37, 6])) (.branch 3 (.leaf ![30, 34, 11, 6]) (.leaf ![9, 34, 22, 6]))) (.branch 6 (.branch 5 (.leaf ![21, 34, 5, 6]) (.leaf ![6, 33, 0, 3])) (.branch 7 (.leaf ![24, 33, 38, 3]) (.leaf ![23, 33, 15, 3])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![6, 33, 29, 3]) (.leaf ![24, 33, 37, 3])) (.branch 11 (.leaf ![23, 33, 20, 3]) (.leaf ![6, 33, 5, 3]))) (.branch 14 (.branch 13 (.leaf ![24, 33, 11, 3]) (.leaf ![23, 33, 22, 3])) (.branch 15 (.leaf ![3, 27, 0, 30]) (.leaf ![1, 27, 39, 30]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![4, 27, 10, 30]) (.leaf ![3, 27, 37, 30])) (.branch 19 (.leaf ![1, 27, 20, 30]) (.leaf ![4, 27, 29, 30]))) (.branch 22 (.branch 21 (.leaf ![3, 27, 22, 30]) (.leaf ![1, 27, 5, 30])) (.branch 23 (.leaf ![4, 27, 11, 30]) (.leaf ![0, 32, 33, 31])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![25, 41, 33, 16]) (.leaf ![31, 31, 33, 25])) (.branch 27 (.leaf ![27, 19, 27, 15]) (.leaf ![38, 42, 27, 38]))) (.branch 30 (.branch 29 (.leaf ![15, 15, 27, 38]) (.leaf ![34, 12, 34, 10])) (.branch 31 (.leaf ![39, 40, 34, 39]) (.leaf ![10, 10, 34, 39]))))))

@[expose] public def factorBlock2 : Lean.RArray (Fin 4 → Fin 43) := (.branch 7 (.branch 3 (.branch 1 (.leaf ![30, 31, 30, 32]) (.branch 2 (.leaf ![32, 9, 30, 41]) (.leaf ![41, 25, 30, 41]))) (.branch 5 (.branch 4 (.leaf ![6, 15, 6, 19]) (.leaf ![19, 19, 6, 42])) (.branch 6 (.leaf ![42, 38, 6, 42]) (.leaf ![3, 10, 3, 12])))) (.branch 10 (.branch 8 (.leaf ![12, 12, 3, 40]) (.branch 9 (.leaf ![40, 39, 3, 40]) (.leaf ![0, 41, 33, 32]))) (.branch 12 (.branch 11 (.leaf ![0, 42, 27, 19]) (.leaf ![0, 40, 34, 12])) (.branch 13 (.leaf ![0, 38, 6, 15]) (.leaf ![0, 39, 3, 10])))))
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
@[expose] public def words : Fin 43 → List (Fin 4) := fun j =>
  ((.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf []) (.leaf [0])) (.branch 3 (.leaf [2]) (.branch 4 (.leaf [0, 1]) (.leaf [0, 3])))) (.branch 7 (.branch 6 (.leaf [1, 2]) (.leaf [3, 2])) (.branch 8 (.leaf [0, 0, 0]) (.branch 9 (.leaf [0, 0, 3]) (.leaf [0, 1, 0]))))) (.branch 15 (.branch 12 (.branch 11 (.leaf [0, 1, 2]) (.leaf [0, 3, 0])) (.branch 13 (.leaf [0, 3, 2]) (.branch 14 (.leaf [1, 0, 1]) (.leaf [1, 2, 2])))) (.branch 18 (.branch 16 (.leaf [2, 1, 0]) (.branch 17 (.leaf [2, 1, 2]) (.leaf [2, 2, 1]))) (.branch 19 (.leaf [2, 2, 2]) (.branch 20 (.leaf [2, 3, 0]) (.leaf [2, 3, 2])))))) (.branch 32 (.branch 26 (.branch 23 (.branch 22 (.leaf [3, 0, 0]) (.leaf [3, 0, 1])) (.branch 24 (.leaf [3, 2, 1]) (.branch 25 (.leaf [3, 2, 3]) (.leaf [0, 0, 0, 0])))) (.branch 29 (.branch 27 (.leaf [0, 0, 0, 1]) (.branch 28 (.leaf [0, 0, 0, 3]) (.leaf [0, 0, 1, 0]))) (.branch 30 (.leaf [0, 1, 0, 0]) (.branch 31 (.leaf [0, 1, 0, 1]) (.leaf [0, 1, 2, 1]))))) (.branch 37 (.branch 34 (.branch 33 (.leaf [0, 3, 2, 3]) (.leaf [1, 2, 2, 1])) (.branch 35 (.leaf [1, 2, 2, 2]) (.branch 36 (.leaf [2, 2, 3, 2]) (.leaf [2, 3, 2, 2])))) (.branch 40 (.branch 38 (.leaf [3, 2, 2, 2]) (.branch 39 (.leaf [0, 0, 0, 0, 1]) (.leaf [0, 0, 0, 0, 3]))) (.branch 41 (.leaf [0, 0, 0, 1, 0]) (.branch 42 (.leaf [0, 0, 3, 0, 0]) (.leaf [0, 3, 0, 0, 0]))))))) : Lean.RArray (List (Fin 4))).get j.val
@[expose] public def wordCodes : Fin 43 → MatrixCode := fun j =>
  ((.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf 6643) (.leaf 12746)) (.branch 3 (.leaf 17930) (.branch 4 (.leaf 11261) (.leaf 12044)))) (.branch 7 (.branch 6 (.leaf 17957) (.leaf 17903)) (.branch 8 (.leaf 10829) (.branch 9 (.leaf 2728) (.leaf 3403))))) (.branch 15 (.branch 12 (.branch 11 (.leaf 8128) (.leaf 2701)) (.branch 13 (.leaf 7426) (.branch 14 (.leaf 11288) (.leaf 6076)))) (.branch 18 (.branch 16 (.leaf 8155) (.branch 17 (.leaf 5347) (.leaf 4645))) (.branch 19 (.leaf 16013) (.branch 20 (.leaf 7399) (.leaf 4672)))))) (.branch 32 (.branch 26 (.branch 23 (.branch 22 (.leaf 4132) (.leaf 11315)) (.branch 24 (.leaf 18659) (.branch 25 (.leaf 19415) (.leaf 14014)))) (.branch 29 (.branch 27 (.leaf 10073) (.branch 28 (.leaf 9317) (.leaf 9371))) (.branch 30 (.leaf 9344) (.branch 31 (.leaf 2674) (.leaf 8101))))) (.branch 37 (.branch 34 (.branch 33 (.leaf 7372) (.leaf 4618)) (.branch 35 (.leaf 15959) (.branch 36 (.leaf 16742) (.leaf 17444)))) (.branch 40 (.branch 38 (.leaf 15986) (.branch 39 (.leaf 14041) (.leaf 14068))) (.branch 41 (.leaf 14770) (.branch 42 (.leaf 14743) (.leaf 14797))))))) : Lean.RArray MatrixCode).get j.val
set_option maxHeartbeats 4000000 in
public theorem wordEval : ∀ j, (evalWord (nodeGenerator 40) (words j)).val =
    decodeMatrix (wordCodes j) := by decide +kernel
@[expose] public def next : Fin 78 → Fin 4 → Fin 78 := fun j =>
  ((.branch 1 (.leaf nextBlock0) (.branch 2 (.leaf nextBlock1) (.leaf nextBlock2))) : Lean.RArray (Lean.RArray (Fin 4 → Fin 78))).get (j.val / 32) |>.get (j.val % 32)
@[expose] public def factorIndex : Fin 78 → Fin 4 → Fin 43 := fun j =>
  ((.branch 1 (.leaf factorBlock0) (.branch 2 (.leaf factorBlock1) (.leaf factorBlock2))) : Lean.RArray (Lean.RArray (Fin 4 → Fin 43))).get (j.val / 32) |>.get (j.val % 32)
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
public theorem valid : table.Valid ambientGenerator (nodeGenerator 40) rep := by
  constructor
  · decide +kernel
  · intro j k
    apply Subtype.ext
    change (rep j).val * (ambientGenerator k).val =
      (evalWord (nodeGenerator 40) (words (factorIndex j k))).val * (rep (next j k)).val
    rw [wordEval]
    exact transitions j k
public theorem cover : RightCosetCover (properNode 40) rep := by
  rw [properNode_eq_wordSubgroup]
  exact table.sound ambientGenerator ambientInverse ambientGenerator_inv
    ambient_wordSubgroup_eq_top (nodeGenerator 40) (symmInv (n := (generatorCodes 40).length))
    (nodeGenerator_inv 40) rep valid
end Matrix.PSL3Three.CertifiedEnumeration.Cosets40
