module
public import Theory.SpecificGroups.PSL3Three.CosetCover.Check
/-!
# Checked right cosets for node 37

These are untrusted matrix codes and subgroup words generated from the fixed
lists in `RepresentativeBounds`. The kernel checks determinants, word values,
and every transition by the four ambient generators. `cover` then follows from
`RightCosetTable.sound`, using the proved generation of the actual SL₃(3).

Source: the elementary coset-table argument in `SubgroupEnumeration` and
GLS III, Theorem 6.5.3. Row zero represents the identity matrix.
-/

namespace Matrix.PSL3Three.CertifiedEnumeration.Cosets37
open Theory.GroupTheory Theory.GroupTheory.SubgroupEnumeration CosetCheck
set_option maxRecDepth 100000

@[expose] public def codeBlock0 : Lean.RArray (MatrixCode) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 6643) (.leaf 828)) (.branch 3 (.leaf 829) (.leaf 830))) (.branch 6 (.branch 5 (.leaf 831) (.leaf 832)) (.branch 7 (.leaf 833) (.leaf 834)))) (.branch 12 (.branch 10 (.branch 9 (.leaf 835) (.leaf 836)) (.branch 11 (.leaf 855) (.leaf 856))) (.branch 14 (.branch 13 (.leaf 857) (.leaf 858)) (.branch 15 (.leaf 859) (.leaf 860))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf 861) (.leaf 862)) (.branch 19 (.leaf 863) (.leaf 882))) (.branch 22 (.branch 21 (.leaf 883) (.leaf 884)) (.branch 23 (.leaf 885) (.leaf 886)))) (.branch 28 (.branch 26 (.branch 25 (.leaf 887) (.leaf 888)) (.branch 27 (.leaf 889) (.leaf 890))) (.branch 30 (.branch 29 (.leaf 900) (.leaf 901)) (.branch 31 (.leaf 902) (.leaf 903))))))

@[expose] public def codeBlock1 : Lean.RArray (MatrixCode) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 904) (.leaf 905)) (.branch 3 (.leaf 906) (.leaf 907))) (.branch 6 (.branch 5 (.leaf 908) (.leaf 927)) (.branch 7 (.leaf 928) (.leaf 929)))) (.branch 12 (.branch 10 (.branch 9 (.leaf 930) (.leaf 931)) (.branch 11 (.leaf 932) (.leaf 933))) (.branch 14 (.branch 13 (.leaf 934) (.leaf 935)) (.branch 15 (.leaf 954) (.leaf 955))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf 956) (.leaf 957)) (.branch 19 (.leaf 958) (.leaf 959))) (.branch 22 (.branch 21 (.leaf 960) (.leaf 961)) (.branch 23 (.leaf 962) (.leaf 975)))) (.branch 28 (.branch 26 (.branch 25 (.leaf 976) (.leaf 977)) (.branch 27 (.leaf 1002) (.leaf 1003))) (.branch 30 (.branch 29 (.leaf 1004) (.leaf 1029)) (.branch 31 (.leaf 1030) (.leaf 1031))))))

@[expose] public def codeBlock2 : Lean.RArray (MatrixCode) := (.branch 7 (.branch 3 (.branch 1 (.leaf 1221) (.branch 2 (.leaf 1222) (.leaf 1223))) (.branch 5 (.branch 4 (.leaf 1248) (.leaf 1249)) (.branch 6 (.leaf 1250) (.leaf 1275)))) (.branch 10 (.branch 8 (.leaf 1276) (.branch 9 (.leaf 1277) (.leaf 2432))) (.branch 12 (.branch 11 (.leaf 2513) (.leaf 2594)) (.branch 13 (.leaf 2755) (.leaf 2836)))))

@[expose] public def nextBlock0 : Lean.RArray (Fin 4 → Fin 78) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![28, 56, 55, 65]) (.leaf ![64, 19, 73, 10])) (.branch 3 (.leaf ![34, 23, 57, 17]) (.leaf ![7, 27, 66, 15]))) (.branch 6 (.branch 5 (.leaf ![65, 22, 30, 13]) (.leaf ![44, 26, 51, 11])) (.branch 7 (.leaf ![26, 21, 45, 18]) (.leaf ![66, 25, 3, 16])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![54, 20, 15, 14]) (.leaf ![18, 24, 27, 12])) (.branch 11 (.leaf ![67, 1, 74, 19]) (.leaf ![43, 5, 60, 26]))) (.branch 14 (.branch 13 (.leaf ![16, 9, 69, 24]) (.leaf ![68, 4, 39, 22])) (.branch 15 (.leaf ![53, 8, 33, 20]) (.leaf ![8, 3, 54, 27]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![69, 7, 12, 25]) (.leaf ![36, 2, 24, 23])) (.branch 19 (.leaf ![27, 6, 9, 21]) (.leaf ![70, 10, 75, 1]))) (.branch 22 (.branch 21 (.leaf ![52, 14, 63, 8]) (.leaf ![25, 18, 72, 6])) (.branch 23 (.leaf ![71, 13, 48, 4]) (.leaf ![35, 17, 42, 2])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![17, 12, 36, 9]) (.leaf ![72, 16, 21, 7])) (.branch 27 (.leaf ![45, 11, 6, 5]) (.leaf ![9, 15, 18, 3]))) (.branch 30 (.branch 29 (.leaf ![55, 37, 0, 46]) (.leaf ![31, 41, 56, 53])) (.branch 31 (.leaf ![4, 45, 65, 51]) (.leaf ![56, 40, 29, 49]))))))

@[expose] public def nextBlock1 : Lean.RArray (Fin 4 → Fin 78) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![50, 44, 41, 47]) (.leaf ![14, 39, 53, 54])) (.branch 3 (.leaf ![57, 43, 2, 52]) (.leaf ![42, 38, 23, 50]))) (.branch 6 (.branch 5 (.leaf ![24, 42, 17, 48]) (.leaf ![58, 46, 76, 28])) (.branch 7 (.leaf ![40, 50, 59, 35]) (.leaf ![13, 54, 68, 33])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![59, 49, 38, 31]) (.leaf ![32, 53, 50, 29])) (.branch 11 (.leaf ![23, 48, 35, 36]) (.leaf ![60, 52, 11, 34]))) (.branch 14 (.branch 13 (.leaf ![51, 47, 5, 32]) (.leaf ![6, 51, 26, 30])) (.branch 15 (.leaf ![61, 28, 77, 37]) (.leaf ![49, 32, 62, 44]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![22, 36, 71, 42]) (.leaf ![62, 31, 47, 40])) (.branch 19 (.leaf ![41, 35, 32, 38]) (.leaf ![5, 30, 44, 45]))) (.branch 22 (.branch 21 (.leaf ![63, 34, 20, 43]) (.leaf ![33, 29, 14, 41])) (.branch 23 (.leaf ![15, 33, 8, 39]) (.leaf ![0, 55, 28, 55])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![29, 65, 31, 0]) (.leaf ![2, 73, 34, 66])) (.branch 27 (.leaf ![76, 58, 37, 58]) (.leaf ![38, 68, 40, 76]))) (.branch 30 (.branch 29 (.leaf ![11, 74, 43, 69]) (.leaf ![77, 61, 46, 61])) (.branch 31 (.leaf ![47, 71, 49, 77]) (.leaf ![20, 75, 52, 72]))))))

@[expose] public def nextBlock2 : Lean.RArray (Fin 4 → Fin 78) := (.branch 7 (.branch 3 (.branch 1 (.leaf ![73, 64, 1, 64]) (.branch 2 (.leaf ![30, 0, 4, 56]) (.leaf ![3, 57, 7, 73]))) (.branch 5 (.branch 4 (.leaf ![74, 67, 10, 67]) (.leaf ![39, 76, 13, 59])) (.branch 6 (.leaf ![12, 60, 16, 74]) (.leaf ![75, 70, 19, 70])))) (.branch 10 (.branch 8 (.leaf ![48, 77, 22, 62]) (.branch 9 (.leaf ![21, 63, 25, 75]) (.leaf ![1, 66, 64, 57]))) (.branch 12 (.branch 11 (.leaf ![10, 69, 67, 60]) (.leaf ![19, 72, 70, 63])) (.branch 13 (.leaf ![37, 59, 58, 68]) (.leaf ![46, 62, 61, 71])))))

@[expose] public def factorBlock0 : Lean.RArray (Fin 4 → Fin 43) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![21, 15, 0, 19]) (.leaf ![21, 3, 0, 9])) (.branch 3 (.leaf ![12, 3, 29, 9]) (.leaf ![11, 3, 37, 9]))) (.branch 6 (.branch 5 (.leaf ![21, 3, 40, 9]) (.leaf ![12, 3, 14, 9])) (.branch 7 (.leaf ![11, 3, 24, 9]) (.leaf ![21, 3, 13, 9])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![12, 3, 2, 9]) (.leaf ![11, 3, 18, 9])) (.branch 11 (.leaf ![5, 7, 0, 21]) (.leaf ![22, 7, 23, 21]))) (.branch 14 (.branch 13 (.leaf ![4, 7, 26, 21]) (.leaf ![5, 7, 24, 21])) (.branch 15 (.leaf ![22, 7, 40, 21]) (.leaf ![4, 7, 14, 21]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![5, 7, 2, 21]) (.leaf ![22, 7, 18, 21])) (.branch 19 (.leaf ![4, 7, 13, 21]) (.leaf ![9, 10, 0, 5]))) (.branch 22 (.branch 21 (.leaf ![41, 10, 31, 5]) (.leaf ![6, 10, 33, 5])) (.branch 23 (.leaf ![9, 10, 14, 5]) (.leaf ![41, 10, 24, 5])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![6, 10, 40, 5]) (.leaf ![9, 10, 18, 5])) (.branch 27 (.leaf ![41, 10, 13, 5]) (.leaf ![6, 10, 2, 5]))) (.branch 30 (.branch 29 (.leaf ![10, 9, 10, 3]) (.leaf ![20, 9, 1, 3])) (.branch 31 (.leaf ![39, 9, 27, 3]) (.leaf ![10, 9, 19, 3]))))))

@[expose] public def factorBlock1 : Lean.RArray (Fin 4 → Fin 43) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![20, 9, 35, 3]) (.leaf ![39, 9, 17, 3])) (.branch 3 (.leaf ![10, 9, 15, 3]) (.leaf ![20, 9, 42, 3]))) (.branch 6 (.branch 5 (.leaf ![39, 9, 36, 3]) (.leaf ![3, 21, 0, 7])) (.branch 7 (.leaf ![38, 21, 32, 7]) (.leaf ![25, 21, 34, 7])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![3, 21, 35, 7]) (.leaf ![38, 21, 17, 7])) (.branch 11 (.leaf ![25, 21, 19, 7]) (.leaf ![3, 21, 36, 7]))) (.branch 14 (.branch 13 (.leaf ![38, 21, 15, 7]) (.leaf ![25, 21, 42, 7])) (.branch 15 (.leaf ![7, 5, 0, 10]) (.leaf ![8, 5, 30, 10]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![16, 5, 28, 10]) (.leaf ![7, 5, 17, 10])) (.branch 19 (.leaf ![8, 5, 19, 10]) (.leaf ![16, 5, 35, 10]))) (.branch 22 (.branch 21 (.leaf ![7, 5, 42, 10]) (.leaf ![8, 5, 36, 10])) (.branch 23 (.leaf ![16, 5, 15, 10]) (.leaf ![0, 29, 21, 27])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![1, 37, 21, 12]) (.leaf ![27, 27, 21, 1])) (.branch 27 (.leaf ![5, 23, 5, 34]) (.leaf ![32, 26, 5, 32]))) (.branch 30 (.branch 29 (.leaf ![34, 34, 5, 32]) (.leaf ![9, 31, 9, 28])) (.branch 31 (.leaf ![30, 33, 9, 30]) (.leaf ![28, 28, 9, 30]))))))

@[expose] public def factorBlock2 : Lean.RArray (Fin 4 → Fin 43) := (.branch 7 (.branch 3 (.branch 1 (.leaf ![10, 27, 10, 29]) (.branch 2 (.leaf ![29, 20, 10, 37]) (.leaf ![37, 1, 10, 37]))) (.branch 5 (.branch 4 (.leaf ![3, 34, 3, 23]) (.leaf ![23, 23, 3, 26])) (.branch 6 (.leaf ![26, 32, 3, 26]) (.leaf ![7, 28, 7, 31])))) (.branch 10 (.branch 8 (.leaf ![31, 31, 7, 33]) (.branch 9 (.leaf ![33, 30, 7, 33]) (.leaf ![0, 37, 21, 29]))) (.branch 12 (.branch 11 (.leaf ![0, 26, 5, 23]) (.leaf ![0, 33, 9, 31])) (.branch 13 (.leaf ![0, 32, 3, 34]) (.leaf ![0, 30, 7, 28])))))
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
  ((.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf []) (.leaf [0, 0])) (.branch 3 (.leaf [1, 0]) (.branch 4 (.leaf [2, 1]) (.leaf [2, 3])))) (.branch 7 (.branch 6 (.leaf [3, 0]) (.leaf [0, 0, 1])) (.branch 8 (.leaf [0, 0, 3]) (.branch 9 (.leaf [0, 1, 0]) (.leaf [1, 0, 0]))))) (.branch 15 (.branch 12 (.branch 11 (.leaf [1, 0, 1]) (.leaf [1, 0, 3])) (.branch 13 (.leaf [1, 1, 0]) (.branch 14 (.leaf [1, 2, 3]) (.leaf [2, 1, 0])))) (.branch 18 (.branch 16 (.leaf [2, 1, 1]) (.branch 17 (.leaf [2, 3, 0]) (.leaf [2, 3, 2]))) (.branch 19 (.leaf [3, 0, 0]) (.branch 20 (.leaf [3, 0, 1]) (.leaf [3, 2, 1])))))) (.branch 32 (.branch 26 (.branch 23 (.branch 22 (.leaf [3, 2, 3]) (.leaf [0, 0, 1, 0])) (.branch 24 (.leaf [0, 0, 1, 1]) (.branch 25 (.leaf [0, 0, 3, 2]) (.leaf [0, 1, 0, 0])))) (.branch 29 (.branch 27 (.leaf [0, 1, 0, 1]) (.branch 28 (.leaf [0, 1, 0, 3]) (.leaf [0, 1, 1, 0]))) (.branch 30 (.leaf [0, 1, 2, 1]) (.branch 31 (.leaf [0, 1, 2, 3]) (.leaf [0, 3, 0, 1]))))) (.branch 37 (.branch 34 (.branch 33 (.leaf [0, 3, 0, 3]) (.leaf [0, 3, 2, 1])) (.branch 35 (.leaf [0, 3, 2, 3]) (.branch 36 (.leaf [1, 1, 2, 1]) (.leaf [1, 2, 1, 1])))) (.branch 40 (.branch 38 (.leaf [1, 2, 3, 0]) (.branch 39 (.leaf [3, 0, 1, 1]) (.leaf [0, 0, 1, 0, 3]))) (.branch 41 (.leaf [0, 0, 3, 0, 3]) (.branch 42 (.leaf [0, 1, 1, 2, 1]) (.leaf [0, 3, 0, 1, 1]))))))) : Lean.RArray (List (Fin 4))).get j.val
@[expose] public def wordCodes : Fin 43 → MatrixCode := fun j =>
  ((.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf 6643) (.leaf 14014)) (.branch 3 (.leaf 15688) (.branch 4 (.leaf 15634) (.leaf 13096)))) (.branch 7 (.branch 6 (.leaf 11584) (.leaf 19549)) (.branch 8 (.leaf 9154) (.branch 9 (.leaf 9937) (.leaf 18064))))) (.branch 15 (.branch 12 (.branch 11 (.leaf 2674) (.leaf 6076)) (.branch 13 (.leaf 5347) (.branch 14 (.leaf 2728) (.leaf 18091)))) (.branch 18 (.branch 16 (.leaf 2701) (.branch 17 (.leaf 10639) (.leaf 18118))) (.branch 19 (.leaf 9208) (.branch 20 (.leaf 4672) (.leaf 3403)))))) (.branch 32 (.branch 26 (.branch 23 (.branch 22 (.leaf 4618) (.leaf 12340)) (.branch 24 (.leaf 7399) (.branch 25 (.leaf 11611) (.leaf 17146)))) (.branch 29 (.branch 27 (.leaf 14797) (.branch 28 (.leaf 8101) (.leaf 8128))) (.branch 30 (.leaf 7372) (.branch 31 (.leaf 14068) (.leaf 7426))))) (.branch 37 (.branch 34 (.branch 33 (.leaf 14041) (.leaf 14770)) (.branch 35 (.leaf 8155) (.branch 36 (.leaf 11638) (.leaf 15661)))) (.branch 40 (.branch 38 (.leaf 14743) (.branch 39 (.leaf 16390) (.leaf 4132))) (.branch 41 (.leaf 4645) (.branch 42 (.leaf 18847) (.leaf 9181))))))) : Lean.RArray MatrixCode).get j.val
set_option maxHeartbeats 4000000 in
public theorem wordEval : ∀ j, (evalWord (nodeGenerator 37) (words j)).val =
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
public theorem valid : table.Valid ambientGenerator (nodeGenerator 37) rep := by
  constructor
  · decide +kernel
  · intro j k
    apply Subtype.ext
    change (rep j).val * (ambientGenerator k).val =
      (evalWord (nodeGenerator 37) (words (factorIndex j k))).val * (rep (next j k)).val
    rw [wordEval]
    exact transitions j k
public theorem cover : RightCosetCover (properNode 37) rep := by
  rw [properNode_eq_wordSubgroup]
  exact table.sound ambientGenerator ambientInverse ambientGenerator_inv
    ambient_wordSubgroup_eq_top (nodeGenerator 37) (symmInv (n := (generatorCodes 37).length))
    (nodeGenerator_inv 37) rep valid
end Matrix.PSL3Three.CertifiedEnumeration.Cosets37
