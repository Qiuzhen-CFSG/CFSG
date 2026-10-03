module
public import Theory.SpecificGroups.PSL3Three.CosetCover.Check
/-!
# Checked right cosets for node 35

These are untrusted matrix codes and subgroup words generated from the fixed
lists in `RepresentativeBounds`. The kernel checks determinants, word values,
and every transition by the four ambient generators. `cover` then follows from
`RightCosetTable.sound`, using the proved generation of the actual SL₃(3).

Source: the elementary coset-table argument in `SubgroupEnumeration` and
GLS III, Theorem 6.5.3. Row zero represents the identity matrix.
-/

namespace Matrix.PSL3Three.CertifiedEnumeration.Cosets35
open Theory.GroupTheory Theory.GroupTheory.SubgroupEnumeration CosetCheck
set_option maxRecDepth 100000

@[expose] public def codeBlock0 : Lean.RArray (MatrixCode) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 6643) (.leaf 828)) (.branch 3 (.leaf 855) (.leaf 882))) (.branch 6 (.branch 5 (.leaf 900) (.leaf 927)) (.branch 7 (.leaf 954) (.leaf 975)))) (.branch 12 (.branch 10 (.branch 9 (.leaf 1002) (.leaf 1029)) (.branch 11 (.leaf 1056) (.leaf 1083))) (.branch 14 (.branch 13 (.leaf 1110) (.leaf 1137)) (.branch 15 (.leaf 1164) (.leaf 1191))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf 1221) (.leaf 1248)) (.branch 19 (.leaf 1275) (.leaf 1302))) (.branch 22 (.branch 21 (.leaf 1329) (.leaf 1356)) (.branch 23 (.leaf 1383) (.leaf 1410)))) (.branch 28 (.branch 26 (.branch 25 (.leaf 1437) (.leaf 2304)) (.branch 27 (.leaf 2340) (.leaf 2432))) (.branch 30 (.branch 29 (.leaf 2459) (.leaf 2486)) (.branch 31 (.leaf 2513) (.leaf 2540))))))

@[expose] public def codeBlock1 : Lean.RArray (MatrixCode) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 2567) (.leaf 2594)) (.branch 3 (.leaf 2621) (.leaf 2648))) (.branch 6 (.branch 5 (.leaf 2674) (.leaf 2701)) (.branch 7 (.leaf 2728) (.leaf 2755)))) (.branch 12 (.branch 10 (.branch 9 (.leaf 2782) (.leaf 2809)) (.branch 11 (.leaf 2863) (.leaf 2890))) (.branch 14 (.branch 13 (.leaf 3161) (.leaf 3188)) (.branch 15 (.leaf 3215) (.leaf 3242))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf 3269) (.leaf 3296)) (.branch 19 (.leaf 3323) (.leaf 3350))) (.branch 22 (.branch 21 (.leaf 3377) (.leaf 3403)) (.branch 23 (.leaf 3430) (.leaf 3457)))) (.branch 28 (.branch 26 (.branch 25 (.leaf 3484) (.leaf 3511)) (.branch 27 (.leaf 3538) (.leaf 3565))) (.branch 30 (.branch 29 (.leaf 3592) (.leaf 3619)) (.branch 31 (.leaf 3890) (.leaf 3917))))))

@[expose] public def codeBlock2 : Lean.RArray (MatrixCode) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 3944) (.leaf 3971)) (.branch 3 (.leaf 3998) (.leaf 4025))) (.branch 6 (.branch 5 (.leaf 4052) (.leaf 4079)) (.branch 7 (.leaf 4106) (.leaf 4132)))) (.branch 12 (.branch 10 (.branch 9 (.leaf 4159) (.leaf 4186)) (.branch 11 (.leaf 4213) (.leaf 4240))) (.branch 14 (.branch 13 (.leaf 4267) (.leaf 4294)) (.branch 15 (.leaf 4321) (.leaf 4348))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf 6837) (.leaf 6861)) (.branch 19 (.leaf 6886) (.leaf 6913))) (.branch 22 (.branch 21 (.leaf 6940) (.leaf 6968)) (.branch 23 (.leaf 6995) (.leaf 7022)))) (.branch 28 (.branch 26 (.branch 25 (.leaf 7615) (.leaf 7642)) (.branch 27 (.leaf 7669) (.leaf 7697))) (.branch 30 (.branch 29 (.leaf 7724) (.leaf 7751)) (.branch 31 (.leaf 8344) (.leaf 8371))))))

@[expose] public def codeBlock3 : Lean.RArray (MatrixCode) := (.branch 4 (.branch 2 (.branch 1 (.leaf 8398) (.leaf 8426)) (.branch 3 (.leaf 8453) (.leaf 8480))) (.branch 6 (.branch 5 (.leaf 9105) (.leaf 9129)) (.branch 7 (.leaf 11373) (.leaf 11397))))

@[expose] public def nextBlock0 : Lean.RArray (Fin 4 → Fin 104) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![6, 0, 7, 0]) (.leaf ![18, 26, 27, 4])) (.branch 3 (.leaf ![80, 2, 30, 2]) (.leaf ![9, 6, 33, 25]))) (.branch 6 (.branch 5 (.leaf ![16, 1, 36, 26]) (.leaf ![81, 5, 39, 5])) (.branch 7 (.leaf ![7, 25, 0, 3]) (.leaf ![0, 44, 6, 69])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![82, 48, 25, 67]) (.leaf ![33, 52, 3, 62])) (.branch 11 (.leaf ![61, 47, 28, 63]) (.leaf ![83, 51, 31, 70]))) (.branch 14 (.branch 13 (.leaf ![52, 46, 34, 65]) (.leaf ![78, 50, 37, 66])) (.branch 15 (.leaf ![84, 45, 40, 64]) (.leaf ![69, 49, 42, 68]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![36, 53, 4, 78]) (.leaf ![85, 57, 26, 76])) (.branch 19 (.leaf ![27, 61, 1, 71]) (.leaf ![71, 56, 29, 72]))) (.branch 22 (.branch 21 (.leaf ![86, 60, 32, 79]) (.leaf ![62, 55, 35, 74])) (.branch 23 (.leaf ![53, 59, 38, 75]) (.leaf ![87, 54, 41, 73])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![44, 58, 43, 77]) (.leaf ![8, 3, 82, 6])) (.branch 27 (.leaf ![17, 4, 85, 1]) (.leaf ![1, 27, 18, 27]))) (.branch 30 (.branch 29 (.leaf ![10, 31, 61, 34]) (.leaf ![19, 35, 71, 32])) (.branch 31 (.leaf ![2, 30, 80, 30]) (.leaf ![11, 34, 83, 28]))))))

@[expose] public def nextBlock1 : Lean.RArray (Fin 4 → Fin 104) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![20, 29, 86, 35]) (.leaf ![3, 33, 9, 33])) (.branch 3 (.leaf ![12, 28, 52, 31]) (.leaf ![21, 32, 62, 29]))) (.branch 6 (.branch 5 (.leaf ![4, 36, 16, 36]) (.leaf ![13, 40, 78, 42])) (.branch 7 (.leaf ![22, 43, 53, 41]) (.leaf ![5, 39, 81, 39])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![14, 42, 84, 37]) (.leaf ![23, 38, 87, 43])) (.branch 11 (.leaf ![15, 37, 69, 40]) (.leaf ![24, 41, 44, 38]))) (.branch 14 (.branch 13 (.leaf ![43, 69, 24, 7]) (.leaf ![88, 64, 58, 14])) (.branch 15 (.leaf ![50, 65, 77, 12]) (.leaf ![60, 63, 93, 10]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![89, 67, 100, 8]) (.leaf ![70, 68, 94, 15])) (.branch 19 (.leaf ![77, 66, 46, 13]) (.leaf ![90, 70, 65, 11]))) (.branch 22 (.branch 21 (.leaf ![34, 62, 12, 9]) (.leaf ![38, 78, 22, 16])) (.branch 23 (.leaf ![91, 73, 75, 23]) (.leaf ![63, 74, 59, 21])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![73, 72, 98, 19]) (.leaf ![92, 76, 101, 17])) (.branch 27 (.leaf ![45, 77, 88, 24]) (.leaf ![55, 75, 63, 22]))) (.branch 30 (.branch 29 (.leaf ![93, 79, 47, 20]) (.leaf ![28, 71, 10, 18])) (.branch 31 (.leaf ![35, 9, 21, 52]) (.leaf ![59, 10, 55, 47]))))))

@[expose] public def nextBlock2 : Lean.RArray (Fin 4 → Fin 104) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![95, 14, 74, 45]) (.leaf ![51, 12, 90, 46])) (.branch 3 (.leaf ![79, 13, 97, 50]) (.leaf ![96, 8, 102, 48]))) (.branch 6 (.branch 5 (.leaf ![68, 15, 68, 49]) (.leaf ![42, 7, 15, 44])) (.branch 7 (.leaf ![94, 11, 49, 51]) (.leaf ![29, 18, 19, 61])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![72, 19, 72, 56]) (.leaf ![98, 23, 56, 54])) (.branch 11 (.leaf ![64, 21, 95, 55]) (.leaf ![54, 22, 91, 59]))) (.branch 14 (.branch 13 (.leaf ![99, 17, 103, 57]) (.leaf ![46, 24, 50, 58])) (.branch 15 (.leaf ![37, 16, 13, 53]) (.leaf ![97, 20, 66, 60]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![30, 83, 2, 86]) (.leaf ![39, 87, 5, 84])) (.branch 19 (.leaf ![25, 82, 8, 82]) (.leaf ![31, 86, 11, 80]))) (.branch 22 (.branch 21 (.leaf ![40, 81, 14, 87]) (.leaf ![26, 85, 17, 85])) (.branch 23 (.leaf ![32, 80, 20, 83]) (.leaf ![41, 84, 23, 81])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![58, 101, 45, 98]) (.leaf ![100, 89, 48, 89])) (.branch 27 (.leaf ![65, 97, 51, 102]) (.leaf ![75, 95, 54, 103]))) (.branch 30 (.branch 29 (.leaf ![101, 92, 57, 92]) (.leaf ![47, 100, 60, 94])) (.branch 31 (.leaf ![49, 93, 70, 100]) (.leaf ![74, 103, 64, 91]))))))

@[expose] public def nextBlock3 : Lean.RArray (Fin 4 → Fin 104) := (.branch 4 (.branch 2 (.branch 1 (.leaf ![102, 96, 67, 96]) (.leaf ![66, 102, 79, 90])) (.branch 3 (.leaf ![56, 88, 73, 101]) (.leaf ![103, 99, 76, 99]))) (.branch 6 (.branch 5 (.leaf ![48, 94, 89, 93]) (.leaf ![57, 98, 92, 88])) (.branch 7 (.leaf ![67, 90, 96, 97]) (.leaf ![76, 91, 99, 95]))))

@[expose] public def factorBlock0 : Lean.RArray (Fin 4 → Fin 35) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![16, 33, 0, 30]) (.leaf ![16, 16, 0, 34])) (.branch 3 (.leaf ![0, 20, 0, 16]) (.leaf ![34, 18, 0, 34]))) (.branch 6 (.branch 5 (.leaf ![18, 34, 0, 18]) (.leaf ![0, 16, 0, 20])) (.branch 7 (.leaf ![20, 20, 20, 18]) (.leaf ![0, 32, 16, 7])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![0, 32, 0, 7]) (.leaf ![34, 32, 34, 7])) (.branch 11 (.leaf ![16, 32, 33, 7]) (.leaf ![0, 32, 31, 7]))) (.branch 14 (.branch 13 (.leaf ![34, 32, 5, 7]) (.leaf ![16, 32, 30, 7])) (.branch 15 (.leaf ![0, 32, 29, 7]) (.leaf ![34, 32, 8, 7]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![18, 28, 18, 3]) (.leaf ![0, 28, 0, 3])) (.branch 19 (.leaf ![20, 28, 20, 3]) (.leaf ![18, 28, 30, 3]))) (.branch 22 (.branch 21 (.leaf ![0, 28, 29, 3]) (.leaf ![20, 28, 8, 3])) (.branch 23 (.leaf ![18, 28, 33, 3]) (.leaf ![0, 28, 31, 3])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![20, 28, 5, 3]) (.leaf ![0, 34, 0, 16])) (.branch 27 (.leaf ![0, 18, 0, 20]) (.leaf ![0, 28, 16, 32]))) (.branch 30 (.branch 29 (.leaf ![30, 28, 19, 32]) (.leaf ![33, 28, 9, 32])) (.branch 31 (.leaf ![0, 28, 0, 32]) (.leaf ![29, 28, 29, 32]))))))

@[expose] public def factorBlock1 : Lean.RArray (Fin 4 → Fin 35) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![31, 28, 31, 32]) (.leaf ![0, 28, 34, 32])) (.branch 3 (.leaf ![8, 28, 11, 32]) (.leaf ![5, 28, 10, 32]))) (.branch 6 (.branch 5 (.leaf ![0, 32, 18, 28]) (.leaf ![33, 32, 23, 28])) (.branch 7 (.leaf ![30, 32, 12, 28]) (.leaf ![0, 32, 0, 28])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![31, 32, 31, 28]) (.leaf ![29, 32, 29, 28])) (.branch 11 (.leaf ![5, 32, 6, 28]) (.leaf ![8, 32, 26, 28]))) (.branch 14 (.branch 13 (.leaf ![15, 3, 16, 28]) (.leaf ![28, 3, 19, 28])) (.branch 15 (.leaf ![13, 3, 9, 28]) (.leaf ![15, 3, 2, 28]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![28, 3, 0, 28]) (.leaf ![13, 3, 1, 28])) (.branch 19 (.leaf ![15, 3, 11, 28]) (.leaf ![28, 3, 10, 28]))) (.branch 22 (.branch 21 (.leaf ![13, 3, 34, 28]) (.leaf ![21, 7, 18, 32])) (.branch 23 (.leaf ![32, 7, 23, 32]) (.leaf ![14, 7, 12, 32])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![21, 7, 24, 32]) (.leaf ![32, 7, 0, 32])) (.branch 27 (.leaf ![14, 7, 25, 32]) (.leaf ![21, 7, 6, 32]))) (.branch 30 (.branch 29 (.leaf ![32, 7, 26, 32]) (.leaf ![14, 7, 20, 32])) (.branch 31 (.leaf ![27, 3, 16, 7]) (.leaf ![4, 3, 19, 7]))))))

@[expose] public def factorBlock2 : Lean.RArray (Fin 4 → Fin 35) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![3, 3, 9, 7]) (.leaf ![27, 3, 24, 7])) (.branch 3 (.leaf ![4, 3, 25, 7]) (.leaf ![3, 3, 0, 7]))) (.branch 6 (.branch 5 (.leaf ![27, 3, 10, 7]) (.leaf ![4, 3, 34, 7])) (.branch 7 (.leaf ![3, 3, 11, 7]) (.leaf ![22, 7, 18, 3])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![17, 7, 23, 3]) (.leaf ![7, 7, 12, 3])) (.branch 11 (.leaf ![22, 7, 2, 3]) (.leaf ![17, 7, 1, 3]))) (.branch 14 (.branch 13 (.leaf ![7, 7, 0, 3]) (.leaf ![22, 7, 26, 3])) (.branch 15 (.leaf ![17, 7, 20, 3]) (.leaf ![7, 7, 6, 3]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![0, 29, 0, 31]) (.leaf ![0, 29, 0, 31])) (.branch 19 (.leaf ![0, 31, 0, 29]) (.leaf ![31, 29, 0, 31]))) (.branch 22 (.branch 21 (.leaf ![29, 29, 0, 31]) (.leaf ![0, 31, 0, 29])) (.branch 23 (.leaf ![29, 29, 0, 31]) (.leaf ![31, 29, 0, 31])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![24, 24, 32, 25]) (.leaf ![32, 25, 32, 24])) (.branch 27 (.leaf ![25, 24, 32, 25]) (.leaf ![2, 1, 28, 2]))) (.branch 30 (.branch 29 (.leaf ![28, 2, 28, 1]) (.leaf ![1, 1, 28, 2])) (.branch 31 (.leaf ![2, 1, 7, 2]) (.leaf ![1, 1, 7, 2]))))))

@[expose] public def factorBlock3 : Lean.RArray (Fin 4 → Fin 35) := (.branch 4 (.branch 2 (.branch 1 (.leaf ![7, 2, 7, 1]) (.leaf ![24, 24, 3, 25])) (.branch 3 (.leaf ![25, 24, 3, 25]) (.leaf ![3, 25, 3, 24]))) (.branch 6 (.branch 5 (.leaf ![0, 1, 28, 2]) (.leaf ![0, 24, 32, 25])) (.branch 7 (.leaf ![0, 24, 3, 25]) (.leaf ![0, 1, 7, 2]))))
@[expose] public def codes : Fin 104 → MatrixCode := fun j =>
  ((.branch 2 (.branch 1 (.leaf codeBlock0) (.leaf codeBlock1)) (.branch 3 (.leaf codeBlock2) (.leaf codeBlock3))) : Lean.RArray (Lean.RArray (MatrixCode))).get (j.val / 32) |>.get (j.val % 32)
@[expose] public def detCheck (k : Nat) : Bool := (codeDet (codes ⟨k % 104, Nat.mod_lt _ (by decide)⟩)).val == 1
set_option maxHeartbeats 4000000 in
private theorem detCheck_0 : checkRange detCheck 0 64 = true := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem detCheck_1 : checkRange detCheck 64 40 = true := by decide +kernel

public theorem det : ∀ j, codeDet (codes j) = 1 := by
  have h := checkRange_fin (by decide : 0 < 104)
    (fun j => (codeDet (codes j)).val == 1) (checkRange_append detCheck_0 detCheck_1)
  intro j
  apply Fin.ext
  exact beq_iff_eq.mp (h j)
@[expose] public def rep (j : Fin 104) : SL := finiteModelEquiv ⟨codes j, det j⟩
@[expose] public def words : Fin 35 → List (Fin 4) := fun j =>
  ((.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf []) (.leaf [0])) (.branch 3 (.leaf [2]) (.leaf [0, 1]))) (.branch 6 (.branch 5 (.leaf [1, 0]) (.leaf [1, 1])) (.branch 7 (.leaf [2, 3]) (.leaf [3, 2])))) (.branch 12 (.branch 10 (.branch 9 (.leaf [3, 3]) (.leaf [0, 1, 0])) (.branch 11 (.leaf [0, 1, 1]) (.leaf [0, 1, 2]))) (.branch 14 (.branch 13 (.leaf [0, 3, 0]) (.leaf [0, 3, 2])) (.branch 15 (.leaf [0, 3, 3]) (.branch 16 (.leaf [1, 0, 1]) (.leaf [1, 0, 3])))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf [1, 1, 0]) (.leaf [1, 1, 1])) (.branch 20 (.leaf [1, 1, 2]) (.leaf [1, 2, 3]))) (.branch 23 (.branch 22 (.leaf [2, 1, 2]) (.leaf [2, 3, 2])) (.branch 24 (.leaf [2, 3, 3]) (.branch 25 (.leaf [3, 0, 1]) (.leaf [3, 2, 1]))))) (.branch 30 (.branch 28 (.branch 27 (.leaf [3, 2, 3]) (.leaf [3, 3, 2])) (.branch 29 (.leaf [0, 1, 0, 1]) (.leaf [0, 1, 0, 3]))) (.branch 32 (.branch 31 (.leaf [0, 1, 1, 2]) (.leaf [0, 3, 0, 1])) (.branch 33 (.leaf [0, 3, 0, 3]) (.branch 34 (.leaf [0, 3, 3, 2]) (.leaf [1, 0, 1, 1]))))))) : Lean.RArray (List (Fin 4))).get j.val
@[expose] public def wordCodes : Fin 35 → MatrixCode := fun j =>
  ((.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 6643) (.leaf 2851)) (.branch 3 (.leaf 17761) (.leaf 13466))) (.branch 6 (.branch 5 (.leaf 8924) (.leaf 6655)) (.branch 7 (.leaf 8921) (.leaf 13457)))) (.branch 12 (.branch 10 (.branch 9 (.leaf 6667) (.leaf 4880)) (.branch 11 (.leaf 2854) (.leaf 8930))) (.branch 14 (.branch 13 (.leaf 4871) (.leaf 8936)) (.branch 15 (.leaf 2839) (.branch 16 (.leaf 17752) (.leaf 17740)))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf 2842) (.leaf 4862)) (.branch 20 (.leaf 17758) (.leaf 2836))) (.branch 23 (.branch 22 (.leaf 4868) (.leaf 4865)) (.branch 24 (.leaf 17749) (.branch 25 (.leaf 17755) (.leaf 2857))))) (.branch 30 (.branch 28 (.branch 27 (.leaf 2845) (.leaf 17764)) (.branch 29 (.leaf 6661) (.leaf 6658))) (.branch 32 (.branch 31 (.leaf 6649) (.leaf 6664)) (.branch 33 (.leaf 6652) (.branch 34 (.leaf 6646) (.leaf 8912))))))) : Lean.RArray MatrixCode).get j.val
set_option maxHeartbeats 4000000 in
public theorem wordEval : ∀ j, (evalWord (nodeGenerator 35) (words j)).val =
    decodeMatrix (wordCodes j) := by decide +kernel
@[expose] public def next : Fin 104 → Fin 4 → Fin 104 := fun j =>
  ((.branch 2 (.branch 1 (.leaf nextBlock0) (.leaf nextBlock1)) (.branch 3 (.leaf nextBlock2) (.leaf nextBlock3))) : Lean.RArray (Lean.RArray (Fin 4 → Fin 104))).get (j.val / 32) |>.get (j.val % 32)
@[expose] public def factorIndex : Fin 104 → Fin 4 → Fin 35 := fun j =>
  ((.branch 2 (.branch 1 (.leaf factorBlock0) (.leaf factorBlock1)) (.branch 3 (.leaf factorBlock2) (.leaf factorBlock3))) : Lean.RArray (Lean.RArray (Fin 4 → Fin 35))).get (j.val / 32) |>.get (j.val % 32)
@[expose] public def table : RightCosetTable 4 4 104 where
  base := 0
  next := next
  factor := fun j k => words (factorIndex j k)
@[expose] public def transitionCheck (j : Fin 104) : Bool :=
  matrixEq ((rep j).val * (ambientGenerator 0).val)
    (decodeMatrix (wordCodes (factorIndex j 0)) * (rep (next j 0)).val) &&
  matrixEq ((rep j).val * (ambientGenerator 1).val)
    (decodeMatrix (wordCodes (factorIndex j 1)) * (rep (next j 1)).val) &&
  matrixEq ((rep j).val * (ambientGenerator 2).val)
    (decodeMatrix (wordCodes (factorIndex j 2)) * (rep (next j 2)).val) &&
  matrixEq ((rep j).val * (ambientGenerator 3).val)
    (decodeMatrix (wordCodes (factorIndex j 3)) * (rep (next j 3)).val)
@[expose] public def rowCheck (k : Nat) : Bool := transitionCheck ⟨k % 104, Nat.mod_lt _ (by decide)⟩
set_option maxHeartbeats 4000000 in
private theorem rowCheck_0 : checkRange rowCheck 0 64 = true := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem rowCheck_1 : checkRange rowCheck 64 40 = true := by decide +kernel

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
public theorem valid : table.Valid ambientGenerator (nodeGenerator 35) rep := by
  constructor
  · decide +kernel
  · intro j k
    apply Subtype.ext
    change (rep j).val * (ambientGenerator k).val =
      (evalWord (nodeGenerator 35) (words (factorIndex j k))).val * (rep (next j k)).val
    rw [wordEval]
    exact transitions j k
public theorem cover : RightCosetCover (properNode 35) rep := by
  rw [properNode_eq_wordSubgroup]
  exact table.sound ambientGenerator ambientInverse ambientGenerator_inv
    ambient_wordSubgroup_eq_top (nodeGenerator 35) (symmInv (n := (generatorCodes 35).length))
    (nodeGenerator_inv 35) rep valid
end Matrix.PSL3Three.CertifiedEnumeration.Cosets35
