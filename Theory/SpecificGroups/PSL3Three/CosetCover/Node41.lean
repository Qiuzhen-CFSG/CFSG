module
public import Theory.SpecificGroups.PSL3Three.CosetCover.Check
/-!
# Checked right cosets for node 41

These are untrusted matrix codes and subgroup words generated from the fixed
lists in `RepresentativeBounds`. The kernel checks determinants, word values,
and every transition by the four ambient generators. `cover` then follows from
`RightCosetTable.sound`, using the proved generation of the actual SL₃(3).

Source: the elementary coset-table argument in `SubgroupEnumeration` and
GLS III, Theorem 6.5.3. Row zero represents the identity matrix.
-/

namespace Matrix.PSL3Three.CertifiedEnumeration.Cosets41
open Theory.GroupTheory Theory.GroupTheory.SubgroupEnumeration CosetCheck
set_option maxRecDepth 100000

@[expose] public def codeBlock0 : Lean.RArray (MatrixCode) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 6643) (.leaf 828)) (.branch 3 (.leaf 855) (.leaf 882))) (.branch 6 (.branch 5 (.leaf 975) (.leaf 1002)) (.branch 7 (.leaf 1029) (.leaf 1056)))) (.branch 12 (.branch 10 (.branch 9 (.leaf 1083) (.leaf 1110)) (.branch 11 (.leaf 1137) (.leaf 1164))) (.branch 14 (.branch 13 (.leaf 1191) (.leaf 2304)) (.branch 15 (.leaf 2340) (.leaf 2459))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf 2486) (.leaf 2513)) (.branch 19 (.leaf 2540) (.leaf 2567))) (.branch 22 (.branch 21 (.leaf 2594) (.leaf 2621)) (.branch 23 (.leaf 2648) (.leaf 3060)))) (.branch 28 (.branch 26 (.branch 25 (.leaf 3161) (.leaf 3188)) (.branch 27 (.leaf 3215) (.leaf 3242))) (.branch 30 (.branch 29 (.leaf 3269) (.leaf 3296)) (.branch 31 (.leaf 3323) (.leaf 3350))))))

@[expose] public def codeBlock1 : Lean.RArray (MatrixCode) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 3377) (.leaf 3890)) (.branch 3 (.leaf 3917) (.leaf 3944))) (.branch 6 (.branch 5 (.leaf 3971) (.leaf 3998)) (.branch 7 (.leaf 4025) (.leaf 4052)))) (.branch 12 (.branch 10 (.branch 9 (.leaf 4079) (.leaf 4106)) (.branch 11 (.leaf 6837) (.leaf 6861))) (.branch 14 (.branch 13 (.leaf 6886) (.leaf 6913)) (.branch 15 (.leaf 6940) (.leaf 6968))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf 6995) (.leaf 7022)) (.branch 19 (.leaf 7593) (.leaf 7615))) (.branch 22 (.branch 21 (.leaf 7642) (.leaf 7669)) (.branch 23 (.leaf 7697) (.leaf 7724)))) (.branch 28 (.branch 26 (.branch 25 (.leaf 7751) (.leaf 8344)) (.branch 27 (.leaf 8371) (.leaf 8398))) (.branch 30 (.branch 29 (.leaf 8426) (.leaf 8453)) (.branch 31 (.leaf 8480) (.leaf 9105))))))

@[expose] public def codeBlock2 : Lean.RArray (MatrixCode) := (.branch 7 (.branch 3 (.branch 1 (.leaf 9129) (.branch 2 (.leaf 9154) (.leaf 9181))) (.branch 5 (.branch 4 (.leaf 9208) (.leaf 9861)) (.branch 6 (.leaf 9883) (.leaf 9910)))) (.branch 10 (.branch 8 (.leaf 9937) (.branch 9 (.leaf 10612) (.leaf 10639))) (.branch 12 (.branch 11 (.leaf 10666) (.leaf 11373)) (.branch 13 (.leaf 11397) (.leaf 12129)))))

@[expose] public def nextBlock0 : Lean.RArray (Fin 4 → Fin 78) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![1, 0, 4, 0]) (.leaf ![4, 13, 0, 14])) (.branch 3 (.leaf ![42, 23, 17, 3]) (.leaf ![43, 2, 20, 23]))) (.branch 6 (.branch 5 (.leaf ![0, 24, 1, 33]) (.leaf ![44, 28, 13, 40])) (.branch 7 (.leaf ![47, 32, 14, 38]) (.leaf ![24, 27, 15, 36])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![45, 31, 18, 34]) (.leaf ![49, 26, 21, 41])) (.branch 11 (.leaf ![33, 30, 16, 39]) (.leaf ![46, 25, 22, 37]))) (.branch 14 (.branch 13 (.leaf ![48, 29, 19, 35]) (.leaf ![5, 14, 44, 1])) (.branch 15 (.leaf ![6, 1, 47, 13]) (.leaf ![7, 18, 24, 21]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![10, 22, 33, 19]) (.leaf ![2, 17, 42, 17])) (.branch 19 (.leaf ![8, 21, 45, 15]) (.leaf ![12, 16, 48, 22]))) (.branch 22 (.branch 21 (.leaf ![3, 20, 43, 20]) (.leaf ![9, 15, 49, 18])) (.branch 23 (.leaf ![11, 19, 46, 16]) (.leaf ![50, 3, 65, 2])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![15, 33, 7, 4]) (.leaf ![51, 37, 27, 11])) (.branch 27 (.leaf ![54, 41, 36, 9]) (.leaf ![25, 36, 51, 7]))) (.branch 30 (.branch 29 (.leaf ![52, 40, 63, 5]) (.leaf ![56, 35, 66, 12])) (.branch 31 (.leaf ![34, 39, 57, 10]) (.leaf ![53, 34, 67, 8]))))))

@[expose] public def nextBlock1 : Lean.RArray (Fin 4 → Fin 78) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![55, 38, 64, 6]) (.leaf ![16, 4, 10, 24])) (.branch 3 (.leaf ![57, 8, 30, 31]) (.leaf ![60, 12, 39, 29]))) (.branch 6 (.branch 5 (.leaf ![26, 7, 54, 27]) (.leaf ![58, 11, 69, 25])) (.branch 7 (.leaf ![62, 6, 75, 32]) (.leaf ![35, 10, 60, 30])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![59, 5, 76, 28]) (.leaf ![61, 9, 72, 26])) (.branch 11 (.leaf ![17, 45, 2, 48]) (.leaf ![20, 49, 3, 46]))) (.branch 14 (.branch 13 (.leaf ![13, 44, 5, 44]) (.leaf ![18, 48, 8, 42])) (.branch 15 (.leaf ![22, 43, 11, 49]) (.leaf ![14, 47, 6, 47]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![19, 42, 12, 45]) (.leaf ![21, 46, 9, 43])) (.branch 19 (.leaf ![65, 71, 23, 73]) (.leaf ![27, 63, 25, 66]))) (.branch 22 (.branch 21 (.leaf ![63, 70, 28, 55]) (.leaf ![67, 58, 31, 77])) (.branch 23 (.leaf ![36, 69, 26, 75]) (.leaf ![64, 52, 32, 70])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![66, 68, 29, 61]) (.leaf ![30, 67, 34, 64])) (.branch 27 (.leaf ![69, 77, 37, 53]) (.leaf ![76, 62, 40, 74]))) (.branch 30 (.branch 29 (.leaf ![39, 76, 35, 72]) (.leaf ![72, 56, 41, 68])) (.branch 31 (.leaf ![75, 74, 38, 59]) (.leaf ![28, 66, 52, 51]))))))

@[expose] public def nextBlock2 : Lean.RArray (Fin 4 → Fin 78) := (.branch 7 (.branch 3 (.branch 1 (.leaf ![32, 57, 55, 67]) (.branch 2 (.leaf ![23, 65, 50, 65]) (.leaf ![29, 51, 56, 63]))) (.branch 5 (.branch 4 (.leaf ![31, 64, 53, 57]) (.leaf ![71, 61, 70, 56])) (.branch 6 (.leaf ![37, 75, 58, 54]) (.leaf ![68, 55, 71, 52])))) (.branch 10 (.branch 8 (.leaf ![70, 73, 68, 50]) (.branch 9 (.leaf ![41, 60, 61, 76]) (.leaf ![74, 50, 77, 71]))) (.branch 12 (.branch 11 (.leaf ![77, 59, 73, 62]) (.leaf ![38, 54, 62, 69])) (.branch 13 (.leaf ![40, 72, 59, 60]) (.leaf ![73, 53, 74, 58])))))

@[expose] public def factorBlock0 : Lean.RArray (Fin 4 → Fin 37) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![2, 22, 0, 20]) (.leaf ![2, 2, 2, 35])) (.branch 3 (.leaf ![0, 36, 0, 35]) (.leaf ![36, 32, 0, 4]))) (.branch 6 (.branch 5 (.leaf ![0, 3, 2, 9]) (.leaf ![0, 3, 0, 9])) (.branch 7 (.leaf ![36, 3, 36, 9]) (.leaf ![2, 3, 22, 9])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![0, 3, 28, 9]) (.leaf ![36, 3, 23, 9])) (.branch 11 (.leaf ![2, 3, 34, 9]) (.leaf ![0, 3, 14, 9]))) (.branch 14 (.branch 13 (.leaf ![36, 3, 10, 9]) (.leaf ![0, 36, 0, 2])) (.branch 15 (.leaf ![36, 32, 0, 36]) (.leaf ![20, 6, 1, 3]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![31, 6, 13, 3]) (.leaf ![0, 6, 0, 3])) (.branch 19 (.leaf ![19, 6, 19, 3]) (.leaf ![8, 6, 28, 3]))) (.branch 22 (.branch 21 (.leaf ![0, 6, 36, 3]) (.leaf ![27, 6, 10, 3])) (.branch 23 (.leaf ![7, 6, 7, 3]) (.leaf ![36, 4, 0, 36])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![5, 16, 2, 6]) (.leaf ![6, 16, 1, 6])) (.branch 27 (.leaf ![33, 16, 13, 6]) (.leaf ![5, 16, 29, 6]))) (.branch 30 (.branch 29 (.leaf ![6, 16, 0, 6]) (.leaf ![33, 16, 19, 6])) (.branch 31 (.leaf ![5, 16, 11, 6]) (.leaf ![6, 16, 7, 6]))))))

@[expose] public def factorBlock1 : Lean.RArray (Fin 4 → Fin 37) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![33, 16, 36, 6]) (.leaf ![17, 16, 2, 9])) (.branch 3 (.leaf ![16, 16, 1, 9]) (.leaf ![21, 16, 13, 9]))) (.branch 6 (.branch 5 (.leaf ![17, 16, 25, 9]) (.leaf ![16, 16, 29, 9])) (.branch 7 (.leaf ![21, 16, 0, 9]) (.leaf ![17, 16, 18, 9])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![16, 16, 36, 9]) (.leaf ![21, 16, 11, 9])) (.branch 11 (.leaf ![0, 19, 0, 28]) (.leaf ![36, 19, 36, 28]))) (.branch 14 (.branch 13 (.leaf ![0, 28, 0, 19]) (.leaf ![28, 19, 0, 28])) (.branch 15 (.leaf ![14, 19, 0, 28]) (.leaf ![0, 28, 36, 19]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![19, 19, 36, 28]) (.leaf ![8, 19, 36, 28])) (.branch 19 (.leaf ![36, 19, 36, 29]) (.leaf ![25, 25, 3, 29]))) (.branch 22 (.branch 21 (.leaf ![3, 28, 3, 25]) (.leaf ![8, 25, 3, 28])) (.branch 23 (.leaf ![29, 19, 33, 29]) (.leaf ![6, 29, 33, 25])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![14, 19, 33, 29]) (.leaf ![12, 25, 9, 29])) (.branch 27 (.leaf ![15, 25, 9, 29]) (.leaf ![26, 29, 9, 19]))) (.branch 30 (.branch 29 (.leaf ![15, 25, 21, 28]) (.leaf ![12, 25, 21, 29])) (.branch 31 (.leaf ![21, 29, 21, 25]) (.leaf ![0, 19, 6, 29]))))))

@[expose] public def factorBlock2 : Lean.RArray (Fin 4 → Fin 37) := (.branch 7 (.branch 3 (.branch 1 (.leaf ![36, 25, 3, 28]) (.branch 2 (.leaf ![0, 28, 36, 19]) (.leaf ![28, 25, 7, 28]))) (.branch 5 (.branch 4 (.leaf ![14, 19, 10, 29]) (.leaf ![36, 25, 23, 28])) (.branch 6 (.leaf ![25, 25, 18, 28]) (.leaf ![27, 29, 10, 19])))) (.branch 10 (.branch 8 (.leaf ![8, 25, 36, 28]) (.branch 9 (.leaf ![12, 19, 11, 29]) (.leaf ![15, 25, 36, 29]))) (.branch 12 (.branch 11 (.leaf ![24, 28, 18, 25]) (.leaf ![0, 25, 21, 29])) (.branch 13 (.leaf ![36, 25, 26, 29]) (.leaf ![36, 19, 30, 29])))))
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
@[expose] public def words : Fin 37 → List (Fin 4) := fun j =>
  ((.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf []) (.leaf [0, 1])) (.branch 3 (.leaf [0, 3]) (.leaf [1, 1]))) (.branch 6 (.branch 5 (.leaf [2, 1]) (.leaf [3, 2])) (.branch 7 (.leaf [3, 3]) (.branch 8 (.leaf [0, 0, 1]) (.leaf [0, 0, 3]))))) (.branch 13 (.branch 11 (.branch 10 (.leaf [0, 1, 0]) (.leaf [0, 3, 2])) (.branch 12 (.leaf [0, 3, 3]) (.leaf [1, 0, 3]))) (.branch 15 (.branch 14 (.leaf [1, 1, 0]) (.leaf [2, 1, 0])) (.branch 16 (.leaf [2, 1, 1]) (.branch 17 (.leaf [2, 3, 2]) (.leaf [2, 3, 3])))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf [3, 2, 1]) (.leaf [0, 1, 0, 1])) (.branch 21 (.leaf [0, 1, 0, 3]) (.leaf [0, 3, 2, 3]))) (.branch 24 (.branch 23 (.leaf [0, 3, 3, 2]) (.leaf [1, 0, 1, 0])) (.branch 25 (.leaf [1, 0, 1, 1]) (.branch 26 (.leaf [1, 1, 0, 1]) (.leaf [2, 1, 0, 1]))))) (.branch 32 (.branch 29 (.branch 28 (.leaf [2, 3, 2, 3]) (.leaf [3, 2, 3, 2])) (.branch 30 (.leaf [3, 2, 3, 3]) (.branch 31 (.leaf [3, 3, 2, 3]) (.leaf [0, 0, 1, 1, 1])))) (.branch 34 (.branch 33 (.leaf [0, 1, 0, 1, 0]) (.leaf [0, 1, 1, 0, 3])) (.branch 35 (.leaf [0, 3, 2, 3, 3]) (.branch 36 (.leaf [2, 3, 2, 3, 2]) (.leaf [0, 0, 1, 0, 1, 0, 1]))))))) : Lean.RArray (List (Fin 4))).get j.val
@[expose] public def wordCodes : Fin 37 → MatrixCode := fun j =>
  ((.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf 6643) (.leaf 2450)) (.branch 3 (.leaf 2432) (.leaf 6652))) (.branch 6 (.branch 5 (.leaf 4862) (.leaf 2438)) (.branch 7 (.leaf 6661) (.branch 8 (.leaf 6740) (.leaf 6749))))) (.branch 13 (.branch 11 (.branch 10 (.leaf 13214) (.leaf 6746)) (.branch 12 (.leaf 2689) (.leaf 4630))) (.branch 15 (.branch 14 (.leaf 2692) (.leaf 6737)) (.branch 16 (.leaf 4642) (.branch 17 (.leaf 13223) (.leaf 4624)))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf 2695) (.leaf 6658)) (.branch 21 (.leaf 6649) (.leaf 13303))) (.branch 24 (.branch 23 (.leaf 6646) (.leaf 6655)) (.branch 25 (.leaf 4886) (.branch 26 (.leaf 2453) (.leaf 13294))))) (.branch 32 (.branch 29 (.branch 28 (.leaf 6667) (.leaf 6664)) (.branch 30 (.leaf 2447) (.branch 31 (.leaf 4874) (.leaf 6731)))) (.branch 34 (.branch 33 (.leaf 2674) (.leaf 6743)) (.branch 35 (.leaf 6728) (.branch 36 (.leaf 4618) (.leaf 6725))))))) : Lean.RArray MatrixCode).get j.val
set_option maxHeartbeats 4000000 in
public theorem wordEval : ∀ j, (evalWord (nodeGenerator 41) (words j)).val =
    decodeMatrix (wordCodes j) := by decide +kernel
@[expose] public def next : Fin 78 → Fin 4 → Fin 78 := fun j =>
  ((.branch 1 (.leaf nextBlock0) (.branch 2 (.leaf nextBlock1) (.leaf nextBlock2))) : Lean.RArray (Lean.RArray (Fin 4 → Fin 78))).get (j.val / 32) |>.get (j.val % 32)
@[expose] public def factorIndex : Fin 78 → Fin 4 → Fin 37 := fun j =>
  ((.branch 1 (.leaf factorBlock0) (.branch 2 (.leaf factorBlock1) (.leaf factorBlock2))) : Lean.RArray (Lean.RArray (Fin 4 → Fin 37))).get (j.val / 32) |>.get (j.val % 32)
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
public theorem valid : table.Valid ambientGenerator (nodeGenerator 41) rep := by
  constructor
  · decide +kernel
  · intro j k
    apply Subtype.ext
    change (rep j).val * (ambientGenerator k).val =
      (evalWord (nodeGenerator 41) (words (factorIndex j k))).val * (rep (next j k)).val
    rw [wordEval]
    exact transitions j k
public theorem cover : RightCosetCover (properNode 41) rep := by
  rw [properNode_eq_wordSubgroup]
  exact table.sound ambientGenerator ambientInverse ambientGenerator_inv
    ambient_wordSubgroup_eq_top (nodeGenerator 41) (symmInv (n := (generatorCodes 41).length))
    (nodeGenerator_inv 41) rep valid
end Matrix.PSL3Three.CertifiedEnumeration.Cosets41
