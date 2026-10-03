module
public import Theory.SpecificGroups.PSL3Three.CosetCover.Check
/-!
# Checked right cosets for node 39

These are untrusted matrix codes and subgroup words generated from the fixed
lists in `RepresentativeBounds`. The kernel checks determinants, word values,
and every transition by the four ambient generators. `cover` then follows from
`RightCosetTable.sound`, using the proved generation of the actual SL₃(3).

Source: the elementary coset-table argument in `SubgroupEnumeration` and
GLS III, Theorem 6.5.3. Row zero represents the identity matrix.
-/

namespace Matrix.PSL3Three.CertifiedEnumeration.Cosets39
open Theory.GroupTheory Theory.GroupTheory.SubgroupEnumeration CosetCheck
set_option maxRecDepth 100000

@[expose] public def codeBlock0 : Lean.RArray (MatrixCode) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 6643) (.leaf 828)) (.branch 3 (.leaf 829) (.leaf 830))) (.branch 6 (.branch 5 (.leaf 831) (.leaf 832)) (.branch 7 (.leaf 833) (.leaf 834)))) (.branch 12 (.branch 10 (.branch 9 (.leaf 835) (.leaf 836)) (.branch 11 (.leaf 855) (.leaf 856))) (.branch 14 (.branch 13 (.leaf 857) (.leaf 858)) (.branch 15 (.leaf 859) (.leaf 860))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf 861) (.leaf 862)) (.branch 19 (.leaf 863) (.leaf 882))) (.branch 22 (.branch 21 (.leaf 883) (.leaf 884)) (.branch 23 (.leaf 885) (.leaf 886)))) (.branch 28 (.branch 26 (.branch 25 (.leaf 887) (.leaf 888)) (.branch 27 (.leaf 889) (.leaf 890))) (.branch 30 (.branch 29 (.leaf 975) (.leaf 976)) (.branch 31 (.leaf 977) (.leaf 1002))))))

@[expose] public def codeBlock1 : Lean.RArray (MatrixCode) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 1003) (.leaf 1004)) (.branch 3 (.leaf 1029) (.leaf 1030))) (.branch 6 (.branch 5 (.leaf 1031) (.leaf 2304)) (.branch 7 (.leaf 2305) (.leaf 2306)))) (.branch 12 (.branch 10 (.branch 9 (.leaf 2307) (.leaf 2308)) (.branch 11 (.leaf 2309) (.leaf 2310))) (.branch 14 (.branch 13 (.leaf 2311) (.leaf 2312)) (.branch 15 (.leaf 2340) (.leaf 2341))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf 2342) (.leaf 2343)) (.branch 19 (.leaf 2344) (.leaf 2345))) (.branch 22 (.branch 21 (.leaf 2346) (.leaf 2347)) (.branch 23 (.leaf 2348) (.leaf 2513)))) (.branch 28 (.branch 26 (.branch 25 (.leaf 2594) (.leaf 3060)) (.branch 27 (.leaf 3061) (.leaf 3062))) (.branch 30 (.branch 29 (.leaf 3063) (.leaf 3064)) (.branch 31 (.leaf 3065) (.leaf 3066))))))

@[expose] public def codeBlock2 : Lean.RArray (MatrixCode) := (.branch 7 (.branch 3 (.branch 1 (.leaf 3067) (.branch 2 (.leaf 3068) (.leaf 6837))) (.branch 5 (.branch 4 (.leaf 6838) (.leaf 6839)) (.branch 6 (.leaf 6861) (.leaf 6862)))) (.branch 10 (.branch 8 (.leaf 6863) (.branch 9 (.leaf 6886) (.leaf 6968))) (.branch 12 (.branch 11 (.leaf 7593) (.leaf 7594)) (.branch 13 (.leaf 7595) (.leaf 9154)))))

@[expose] public def nextBlock0 : Lean.RArray (Fin 4 → Fin 78) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![1, 29, 28, 30]) (.leaf ![28, 37, 0, 46])) (.branch 3 (.leaf ![4, 45, 30, 53]) (.leaf ![7, 41, 29, 51]))) (.branch 6 (.branch 5 (.leaf ![30, 43, 2, 49]) (.leaf ![24, 42, 53, 47])) (.branch 7 (.leaf ![26, 38, 45, 54]) (.leaf ![29, 40, 3, 52])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![14, 39, 51, 50]) (.leaf ![18, 44, 41, 48])) (.branch 11 (.leaf ![66, 57, 55, 19]) (.leaf ![43, 65, 33, 26]))) (.branch 14 (.branch 13 (.leaf ![52, 61, 35, 24]) (.leaf ![67, 63, 39, 22])) (.branch 15 (.leaf ![51, 62, 8, 20]) (.leaf ![62, 58, 50, 27]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![68, 60, 48, 25]) (.leaf ![65, 59, 44, 23])) (.branch 19 (.leaf ![41, 64, 9, 21]) (.leaf ![69, 10, 56, 57]))) (.branch 22 (.branch 21 (.leaf ![49, 14, 36, 62]) (.leaf ![40, 18, 32, 64])) (.branch 23 (.leaf ![71, 13, 47, 63]) (.leaf ![64, 17, 42, 59])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![53, 12, 5, 61]) (.leaf ![70, 16, 38, 60])) (.branch 27 (.leaf ![45, 11, 6, 65]) (.leaf ![61, 15, 54, 58]))) (.branch 30 (.branch 29 (.leaf ![0, 28, 1, 28]) (.leaf ![3, 30, 7, 0])) (.branch 31 (.leaf ![2, 0, 4, 29]) (.leaf ![72, 31, 37, 31]))))))

@[expose] public def nextBlock1 : Lean.RArray (Fin 4 → Fin 78) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![21, 36, 40, 56]) (.leaf ![11, 55, 43, 35])) (.branch 3 (.leaf ![73, 34, 46, 34]) (.leaf ![12, 33, 52, 55]))) (.branch 6 (.branch 5 (.leaf ![20, 56, 49, 32]) (.leaf ![31, 46, 72, 1])) (.branch 7 (.leaf ![25, 54, 70, 6]) (.leaf ![13, 50, 67, 8])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![32, 52, 21, 7]) (.leaf ![9, 51, 18, 3])) (.branch 11 (.leaf ![23, 47, 64, 5]) (.leaf ![33, 49, 11, 4]))) (.branch 14 (.branch 13 (.leaf ![17, 48, 65, 9]) (.leaf ![6, 53, 26, 2])) (.branch 15 (.leaf ![34, 1, 73, 37]) (.leaf ![22, 5, 71, 42]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![16, 9, 68, 44]) (.leaf ![36, 4, 20, 43])) (.branch 19 (.leaf ![15, 8, 62, 39]) (.leaf ![8, 3, 14, 41]))) (.branch 22 (.branch 21 (.leaf ![35, 7, 12, 40]) (.leaf ![5, 2, 24, 45])) (.branch 23 (.leaf ![27, 6, 61, 38]) (.leaf ![10, 35, 66, 33])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![19, 32, 69, 36]) (.leaf ![74, 19, 77, 10])) (.branch 27 (.leaf ![60, 27, 76, 15]) (.leaf ![63, 23, 75, 17]))) (.branch 30 (.branch 29 (.leaf ![76, 25, 58, 16]) (.leaf ![54, 24, 27, 12])) (.branch 31 (.leaf ![50, 20, 15, 14]) (.leaf ![75, 22, 59, 13]))))))

@[expose] public def nextBlock2 : Lean.RArray (Fin 4 → Fin 78) := (.branch 7 (.branch 3 (.branch 1 (.leaf ![42, 21, 23, 18]) (.branch 2 (.leaf ![44, 26, 17, 11]) (.leaf ![55, 66, 10, 66]))) (.branch 5 (.branch 4 (.leaf ![39, 72, 13, 70]) (.leaf ![48, 71, 16, 73])) (.branch 6 (.leaf ![56, 69, 19, 69]) (.leaf ![38, 67, 25, 72])))) (.branch 10 (.branch 8 (.leaf ![47, 73, 22, 68]) (.branch 9 (.leaf ![37, 70, 31, 67]) (.leaf ![46, 68, 34, 71]))) (.branch 12 (.branch 11 (.leaf ![77, 74, 57, 74]) (.leaf ![59, 77, 63, 76])) (.branch 13 (.leaf ![58, 75, 60, 77]) (.leaf ![57, 76, 74, 75])))))

@[expose] public def factorBlock0 : Lean.RArray (Fin 4 → Fin 48) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![1, 23, 0, 16]) (.leaf ![1, 1, 1, 46])) (.branch 3 (.leaf ![13, 1, 18, 46]) (.leaf ![26, 1, 31, 46]))) (.branch 6 (.branch 5 (.leaf ![1, 1, 15, 46]) (.leaf ![13, 1, 34, 46])) (.branch 7 (.leaf ![26, 1, 7, 46]) (.leaf ![1, 1, 19, 46])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![13, 1, 9, 46]) (.leaf ![26, 1, 33, 46])) (.branch 11 (.leaf ![0, 47, 0, 46]) (.leaf ![43, 47, 43, 46]))) (.branch 14 (.branch 13 (.leaf ![42, 47, 32, 46]) (.leaf ![0, 47, 7, 46])) (.branch 15 (.leaf ![36, 47, 15, 46]) (.leaf ![38, 47, 34, 46]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![0, 47, 9, 46]) (.leaf ![43, 47, 33, 46])) (.branch 19 (.leaf ![38, 47, 19, 46]) (.leaf ![47, 45, 0, 14]))) (.branch 22 (.branch 21 (.leaf ![29, 45, 44, 14]) (.leaf ![12, 45, 12, 14])) (.branch 23 (.leaf ![47, 45, 34, 14]) (.leaf ![20, 45, 7, 14])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![5, 45, 15, 14]) (.leaf ![47, 45, 33, 14])) (.branch 27 (.leaf ![20, 45, 19, 14]) (.leaf ![12, 45, 9, 14]))) (.branch 30 (.branch 29 (.leaf ![0, 18, 1, 17]) (.leaf ![27, 31, 1, 25])) (.branch 31 (.leaf ![17, 11, 1, 27]) (.leaf ![0, 43, 0, 41]))))))

@[expose] public def factorBlock1 : Lean.RArray (Fin 4 → Fin 48) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![10, 32, 0, 10]) (.leaf ![41, 41, 0, 10])) (.branch 3 (.leaf ![47, 44, 47, 40]) (.leaf ![28, 12, 47, 28]))) (.branch 6 (.branch 5 (.leaf ![40, 40, 47, 28]) (.leaf ![0, 47, 0, 1])) (.branch 7 (.leaf ![34, 47, 7, 1]) (.leaf ![9, 47, 9, 1])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![0, 47, 10, 1]) (.leaf ![34, 47, 37, 1])) (.branch 11 (.leaf ![9, 47, 24, 1]) (.leaf ![0, 47, 41, 1]))) (.branch 14 (.branch 13 (.leaf ![34, 47, 2, 1]) (.leaf ![9, 47, 22, 1])) (.branch 15 (.leaf ![47, 45, 0, 47]) (.leaf ![33, 45, 9, 47]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![7, 45, 7, 47]) (.leaf ![47, 45, 30, 47])) (.branch 19 (.leaf ![33, 45, 4, 47]) (.leaf ![7, 45, 36, 47]))) (.branch 22 (.branch 21 (.leaf ![47, 45, 42, 47]) (.leaf ![33, 45, 6, 47])) (.branch 23 (.leaf ![7, 45, 32, 47]) (.leaf ![0, 32, 0, 43])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![0, 12, 47, 44]) (.leaf ![47, 14, 0, 47])) (.branch 27 (.leaf ![21, 14, 39, 47]) (.leaf ![3, 14, 40, 47]))) (.branch 30 (.branch 29 (.leaf ![47, 14, 24, 47]) (.leaf ![28, 14, 10, 47])) (.branch 31 (.leaf ![8, 14, 37, 47]) (.leaf ![47, 14, 2, 47]))))))

@[expose] public def factorBlock2 : Lean.RArray (Fin 4 → Fin 48) := (.branch 7 (.branch 3 (.branch 1 (.leaf ![21, 14, 22, 47]) (.branch 2 (.leaf ![3, 14, 41, 47]) (.leaf ![0, 9, 0, 7]))) (.branch 5 (.branch 4 (.leaf ![7, 7, 0, 9]) (.leaf ![9, 7, 0, 9])) (.branch 6 (.leaf ![47, 9, 47, 7]) (.leaf ![9, 7, 47, 9])))) (.branch 10 (.branch 8 (.leaf ![7, 7, 47, 9]) (.branch 9 (.leaf ![0, 7, 0, 9]) (.leaf ![0, 7, 47, 9]))) (.branch 12 (.branch 11 (.leaf ![47, 40, 47, 44]) (.leaf ![44, 44, 47, 35])) (.branch 13 (.leaf ![35, 39, 47, 35]) (.leaf ![0, 39, 47, 40])))))
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
@[expose] public def words : Fin 48 → List (Fin 4) := fun j =>
  ((.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf []) (.branch 2 (.leaf [0]) (.leaf [1]))) (.branch 4 (.leaf [3]) (.branch 5 (.leaf [0, 1]) (.leaf [0, 3])))) (.branch 9 (.branch 7 (.leaf [1, 0]) (.branch 8 (.leaf [1, 1]) (.leaf [3, 0]))) (.branch 10 (.leaf [3, 3]) (.branch 11 (.leaf [0, 1, 0]) (.leaf [0, 1, 1]))))) (.branch 18 (.branch 15 (.branch 13 (.leaf [0, 3, 0]) (.branch 14 (.leaf [0, 3, 3]) (.leaf [1, 0, 3]))) (.branch 16 (.leaf [1, 1, 0]) (.branch 17 (.leaf [3, 3, 0]) (.leaf [0, 1, 1, 0])))) (.branch 21 (.branch 19 (.leaf [0, 3, 3, 0]) (.branch 20 (.leaf [1, 0, 1, 1]) (.leaf [1, 0, 3, 3]))) (.branch 22 (.leaf [1, 1, 0, 1]) (.branch 23 (.leaf [1, 1, 0, 3]) (.leaf [3, 0, 1, 1])))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf [3, 0, 3, 3]) (.branch 26 (.leaf [3, 3, 0, 1]) (.leaf [3, 3, 0, 3]))) (.branch 28 (.leaf [0, 1, 0, 1, 1]) (.branch 29 (.leaf [0, 1, 0, 3, 3]) (.leaf [0, 1, 1, 0, 1])))) (.branch 33 (.branch 31 (.leaf [0, 1, 1, 0, 3]) (.branch 32 (.leaf [0, 3, 0, 1, 1]) (.leaf [0, 3, 0, 3, 3]))) (.branch 34 (.leaf [0, 3, 3, 0, 1]) (.branch 35 (.leaf [0, 3, 3, 0, 3]) (.leaf [1, 1, 0, 1, 1]))))) (.branch 42 (.branch 39 (.branch 37 (.leaf [1, 1, 0, 3, 3]) (.branch 38 (.leaf [1, 1, 1, 0, 1]) (.leaf [3, 0, 1, 1, 1]))) (.branch 40 (.leaf [3, 3, 0, 3, 3]) (.branch 41 (.leaf [0, 1, 1, 0, 1, 1]) (.leaf [0, 1, 1, 0, 3, 3])))) (.branch 45 (.branch 43 (.leaf [0, 1, 1, 1, 0, 1]) (.branch 44 (.leaf [0, 3, 3, 0, 1, 1]) (.leaf [0, 3, 3, 0, 3, 3]))) (.branch 46 (.leaf [1, 1, 1, 0, 1, 1]) (.branch 47 (.leaf [3, 3, 0, 1, 1, 1]) (.leaf [0, 3, 3, 0, 1, 1, 1]))))))) : Lean.RArray (List (Fin 4))).get j.val
@[expose] public def wordCodes : Fin 48 → MatrixCode := fun j =>
  ((.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf 6643) (.branch 2 (.leaf 2432) (.leaf 7481))) (.branch 4 (.leaf 7508) (.branch 5 (.leaf 5374) (.leaf 6103)))) (.branch 9 (.branch 7 (.leaf 4186) (.branch 8 (.leaf 6670) (.leaf 4159))) (.branch 10 (.leaf 6697) (.branch 11 (.leaf 14717) (.leaf 3161))))) (.branch 18 (.branch 15 (.branch 13 (.leaf 13988) (.branch 14 (.leaf 3890) (.leaf 4862))) (.branch 16 (.leaf 2486) (.branch 17 (.leaf 2459) (.leaf 8101)))) (.branch 21 (.branch 19 (.leaf 7372) (.branch 20 (.leaf 2728) (.leaf 3457))) (.branch 22 (.leaf 5401) (.branch 23 (.leaf 6130) (.leaf 2701)))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf 3430) (.branch 26 (.leaf 5347) (.leaf 6076))) (.branch 28 (.leaf 14663) (.branch 29 (.leaf 14690) (.leaf 8210)))) (.branch 33 (.branch 31 (.leaf 8237) (.branch 32 (.leaf 13934) (.leaf 13961))) (.branch 34 (.leaf 6752) (.branch 35 (.leaf 6779) (.leaf 3215))))) (.branch 42 (.branch 39 (.branch 37 (.leaf 3944) (.branch 38 (.leaf 6374) (.leaf 5618))) (.branch 40 (.leaf 3917) (.branch 41 (.leaf 8128) (.leaf 8155)))) (.branch 45 (.branch 43 (.leaf 14797) (.branch 44 (.leaf 7399) (.leaf 7426))) (.branch 46 (.leaf 2674) (.branch 47 (.leaf 4618) (.leaf 6725))))))) : Lean.RArray MatrixCode).get j.val
set_option maxHeartbeats 4000000 in
public theorem wordEval : ∀ j, (evalWord (nodeGenerator 39) (words j)).val =
    decodeMatrix (wordCodes j) := by decide +kernel
@[expose] public def next : Fin 78 → Fin 4 → Fin 78 := fun j =>
  ((.branch 1 (.leaf nextBlock0) (.branch 2 (.leaf nextBlock1) (.leaf nextBlock2))) : Lean.RArray (Lean.RArray (Fin 4 → Fin 78))).get (j.val / 32) |>.get (j.val % 32)
@[expose] public def factorIndex : Fin 78 → Fin 4 → Fin 48 := fun j =>
  ((.branch 1 (.leaf factorBlock0) (.branch 2 (.leaf factorBlock1) (.leaf factorBlock2))) : Lean.RArray (Lean.RArray (Fin 4 → Fin 48))).get (j.val / 32) |>.get (j.val % 32)
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
public theorem valid : table.Valid ambientGenerator (nodeGenerator 39) rep := by
  constructor
  · decide +kernel
  · intro j k
    apply Subtype.ext
    change (rep j).val * (ambientGenerator k).val =
      (evalWord (nodeGenerator 39) (words (factorIndex j k))).val * (rep (next j k)).val
    rw [wordEval]
    exact transitions j k
public theorem cover : RightCosetCover (properNode 39) rep := by
  rw [properNode_eq_wordSubgroup]
  exact table.sound ambientGenerator ambientInverse ambientGenerator_inv
    ambient_wordSubgroup_eq_top (nodeGenerator 39) (symmInv (n := (generatorCodes 39).length))
    (nodeGenerator_inv 39) rep valid
end Matrix.PSL3Three.CertifiedEnumeration.Cosets39
