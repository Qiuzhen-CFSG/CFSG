module
public import Theory.SpecificGroups.PSL3Three.CosetCover.Check
/-!
# Checked right cosets for node 34

These are untrusted matrix codes and subgroup words generated from the fixed
lists in `RepresentativeBounds`. The kernel checks determinants, word values,
and every transition by the four ambient generators. `cover` then follows from
`RightCosetTable.sound`, using the proved generation of the actual SL₃(3).

Source: the elementary coset-table argument in `SubgroupEnumeration` and
GLS III, Theorem 6.5.3. Row zero represents the identity matrix.
-/

namespace Matrix.PSL3Three.CertifiedEnumeration.Cosets34
open Theory.GroupTheory Theory.GroupTheory.SubgroupEnumeration CosetCheck
set_option maxRecDepth 100000

@[expose] public def codeBlock0 : Lean.RArray (MatrixCode) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 6643) (.leaf 828)) (.branch 3 (.leaf 855) (.leaf 882))) (.branch 6 (.branch 5 (.leaf 900) (.leaf 927)) (.branch 7 (.leaf 954) (.leaf 975)))) (.branch 12 (.branch 10 (.branch 9 (.leaf 1002) (.leaf 1029)) (.branch 11 (.leaf 1056) (.leaf 1083))) (.branch 14 (.branch 13 (.leaf 1110) (.leaf 1137)) (.branch 15 (.leaf 1164) (.leaf 1191))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf 1221) (.leaf 1248)) (.branch 19 (.leaf 1275) (.leaf 1302))) (.branch 22 (.branch 21 (.leaf 1329) (.leaf 1356)) (.branch 23 (.leaf 1383) (.leaf 1410)))) (.branch 28 (.branch 26 (.branch 25 (.leaf 1437) (.leaf 2304)) (.branch 27 (.leaf 2340) (.leaf 2432))) (.branch 30 (.branch 29 (.leaf 2459) (.leaf 2486)) (.branch 31 (.leaf 2513) (.leaf 2540))))))

@[expose] public def codeBlock1 : Lean.RArray (MatrixCode) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 2567) (.leaf 2594)) (.branch 3 (.leaf 2621) (.leaf 2648))) (.branch 6 (.branch 5 (.leaf 2674) (.leaf 2701)) (.branch 7 (.leaf 2728) (.leaf 2755)))) (.branch 12 (.branch 10 (.branch 9 (.leaf 2782) (.leaf 2809)) (.branch 11 (.leaf 2863) (.leaf 2890))) (.branch 14 (.branch 13 (.leaf 3161) (.leaf 3188)) (.branch 15 (.leaf 3215) (.leaf 3242))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf 3269) (.leaf 3296)) (.branch 19 (.leaf 3323) (.leaf 3350))) (.branch 22 (.branch 21 (.leaf 3377) (.leaf 3403)) (.branch 23 (.leaf 3430) (.leaf 3457)))) (.branch 28 (.branch 26 (.branch 25 (.leaf 3484) (.leaf 3511)) (.branch 27 (.leaf 3538) (.leaf 3565))) (.branch 30 (.branch 29 (.leaf 3592) (.leaf 3619)) (.branch 31 (.leaf 3890) (.leaf 3917))))))

@[expose] public def codeBlock2 : Lean.RArray (MatrixCode) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 3944) (.leaf 3971)) (.branch 3 (.leaf 3998) (.leaf 4025))) (.branch 6 (.branch 5 (.leaf 4052) (.leaf 4079)) (.branch 7 (.leaf 4106) (.leaf 4132)))) (.branch 12 (.branch 10 (.branch 9 (.leaf 4159) (.leaf 4186)) (.branch 11 (.leaf 4213) (.leaf 4240))) (.branch 14 (.branch 13 (.leaf 4267) (.leaf 4294)) (.branch 15 (.leaf 4321) (.leaf 4348))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf 6837) (.leaf 6861)) (.branch 19 (.leaf 6886) (.leaf 6913))) (.branch 22 (.branch 21 (.leaf 6940) (.leaf 6968)) (.branch 23 (.leaf 6995) (.leaf 7022)))) (.branch 28 (.branch 26 (.branch 25 (.leaf 7615) (.leaf 7642)) (.branch 27 (.leaf 7669) (.leaf 7697))) (.branch 30 (.branch 29 (.leaf 7724) (.leaf 7751)) (.branch 31 (.leaf 8344) (.leaf 8371))))))

@[expose] public def codeBlock3 : Lean.RArray (MatrixCode) := (.branch 4 (.branch 2 (.branch 1 (.leaf 8398) (.leaf 8426)) (.branch 3 (.leaf 8453) (.leaf 8480))) (.branch 6 (.branch 5 (.leaf 9105) (.leaf 9129)) (.branch 7 (.leaf 11373) (.leaf 11397))))

@[expose] public def nextBlock0 : Lean.RArray (Fin 4 → Fin 104) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![6, 0, 7, 0]) (.leaf ![18, 26, 27, 3])) (.branch 3 (.leaf ![80, 2, 30, 2]) (.leaf ![16, 1, 33, 26]))) (.branch 6 (.branch 5 (.leaf ![9, 6, 36, 25]) (.leaf ![81, 5, 39, 5])) (.branch 7 (.leaf ![7, 25, 0, 4]) (.leaf ![0, 44, 6, 71])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![82, 48, 25, 76]) (.leaf ![36, 52, 4, 78])) (.branch 11 (.leaf ![61, 47, 28, 77]) (.leaf ![83, 51, 31, 73]))) (.branch 14 (.branch 13 (.leaf ![53, 46, 34, 75]) (.leaf ![78, 50, 37, 74])) (.branch 15 (.leaf ![84, 45, 40, 79]) (.leaf ![71, 49, 42, 72]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![33, 53, 3, 62]) (.leaf ![85, 57, 26, 67])) (.branch 19 (.leaf ![27, 61, 1, 69]) (.leaf ![69, 56, 29, 68]))) (.branch 22 (.branch 21 (.leaf ![86, 60, 32, 64]) (.leaf ![62, 55, 35, 66])) (.branch 23 (.leaf ![52, 59, 38, 65]) (.leaf ![87, 54, 41, 70])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![44, 58, 43, 63]) (.leaf ![8, 4, 82, 6])) (.branch 27 (.leaf ![17, 3, 85, 1]) (.leaf ![1, 27, 18, 27]))) (.branch 30 (.branch 29 (.leaf ![10, 31, 61, 34]) (.leaf ![19, 35, 69, 32])) (.branch 31 (.leaf ![2, 30, 80, 30]) (.leaf ![11, 34, 83, 28]))))))

@[expose] public def nextBlock1 : Lean.RArray (Fin 4 → Fin 104) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![20, 29, 86, 35]) (.leaf ![3, 33, 16, 33])) (.branch 3 (.leaf ![12, 28, 53, 31]) (.leaf ![21, 32, 62, 29]))) (.branch 6 (.branch 5 (.leaf ![4, 36, 9, 36]) (.leaf ![13, 40, 78, 42])) (.branch 7 (.leaf ![22, 43, 52, 41]) (.leaf ![5, 39, 81, 39])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![14, 42, 84, 37]) (.leaf ![23, 38, 87, 43])) (.branch 11 (.leaf ![15, 37, 71, 40]) (.leaf ![24, 41, 44, 38]))) (.branch 14 (.branch 13 (.leaf ![43, 71, 24, 7]) (.leaf ![88, 79, 58, 14])) (.branch 15 (.leaf ![55, 75, 63, 12]) (.leaf ![60, 77, 93, 10]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![89, 76, 100, 8]) (.leaf ![73, 72, 94, 15])) (.branch 19 (.leaf ![77, 74, 59, 13]) (.leaf ![90, 73, 65, 11]))) (.branch 22 (.branch 21 (.leaf ![38, 78, 22, 9]) (.leaf ![34, 62, 12, 16])) (.branch 23 (.leaf ![91, 70, 75, 23]) (.leaf ![63, 66, 46, 21])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![70, 68, 98, 19]) (.leaf ![92, 67, 101, 17])) (.branch 27 (.leaf ![45, 63, 88, 24]) (.leaf ![50, 65, 77, 22]))) (.branch 30 (.branch 29 (.leaf ![93, 64, 47, 20]) (.leaf ![28, 69, 10, 18])) (.branch 31 (.leaf ![35, 16, 21, 53]) (.leaf ![46, 24, 55, 58]))))))

@[expose] public def nextBlock2 : Lean.RArray (Fin 4 → Fin 104) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![97, 20, 66, 60]) (.leaf ![51, 22, 90, 59])) (.branch 3 (.leaf ![64, 21, 97, 55]) (.leaf ![99, 17, 102, 57]))) (.branch 6 (.branch 5 (.leaf ![68, 19, 68, 56]) (.leaf ![29, 18, 19, 61])) (.branch 7 (.leaf ![98, 23, 56, 54]) (.leaf ![42, 7, 15, 44])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![72, 15, 72, 49]) (.leaf ![94, 11, 49, 51])) (.branch 11 (.leaf ![79, 13, 95, 50]) (.leaf ![54, 12, 91, 46]))) (.branch 14 (.branch 13 (.leaf ![96, 8, 103, 48]) (.leaf ![59, 10, 50, 47])) (.branch 15 (.leaf ![37, 9, 13, 52]) (.leaf ![95, 14, 74, 45]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![30, 83, 2, 86]) (.leaf ![39, 87, 5, 84])) (.branch 19 (.leaf ![25, 82, 8, 82]) (.leaf ![31, 86, 11, 80]))) (.branch 22 (.branch 21 (.leaf ![40, 81, 14, 87]) (.leaf ![26, 85, 17, 85])) (.branch 23 (.leaf ![32, 80, 20, 83]) (.leaf ![41, 84, 23, 81])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![58, 101, 45, 98]) (.leaf ![100, 89, 48, 89])) (.branch 27 (.leaf ![65, 97, 51, 102]) (.leaf ![75, 95, 54, 103]))) (.branch 30 (.branch 29 (.leaf ![101, 92, 57, 92]) (.leaf ![47, 100, 60, 94])) (.branch 31 (.leaf ![49, 93, 73, 100]) (.leaf ![74, 103, 79, 91]))))))

@[expose] public def nextBlock3 : Lean.RArray (Fin 4 → Fin 104) := (.branch 4 (.branch 2 (.branch 1 (.leaf ![103, 96, 76, 96]) (.leaf ![66, 102, 64, 90])) (.branch 3 (.leaf ![56, 88, 70, 101]) (.leaf ![102, 99, 67, 99]))) (.branch 6 (.branch 5 (.leaf ![48, 94, 89, 93]) (.leaf ![57, 98, 92, 88])) (.branch 7 (.leaf ![67, 90, 99, 97]) (.leaf ![76, 91, 96, 95]))))

@[expose] public def factorBlock0 : Lean.RArray (Fin 4 → Fin 35) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![8, 24, 0, 23]) (.leaf ![8, 8, 0, 2])) (.branch 3 (.leaf ![0, 14, 0, 8]) (.leaf ![2, 4, 0, 2]))) (.branch 6 (.branch 5 (.leaf ![4, 2, 0, 4]) (.leaf ![0, 8, 0, 14])) (.branch 7 (.leaf ![14, 14, 14, 4]) (.leaf ![0, 1, 8, 34])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![0, 1, 0, 34]) (.leaf ![2, 1, 2, 34])) (.branch 11 (.leaf ![8, 1, 24, 34]) (.leaf ![0, 1, 28, 34]))) (.branch 14 (.branch 13 (.leaf ![2, 1, 17, 34]) (.leaf ![8, 1, 23, 34])) (.branch 15 (.leaf ![0, 1, 31, 34]) (.leaf ![2, 1, 20, 34]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![4, 3, 4, 29]) (.leaf ![0, 3, 0, 29])) (.branch 19 (.leaf ![14, 3, 14, 29]) (.leaf ![4, 3, 23, 29]))) (.branch 22 (.branch 21 (.leaf ![0, 3, 31, 29]) (.leaf ![14, 3, 20, 29])) (.branch 23 (.leaf ![4, 3, 24, 29]) (.leaf ![0, 3, 28, 29])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![14, 3, 17, 29]) (.leaf ![0, 2, 0, 8])) (.branch 27 (.leaf ![0, 4, 0, 14]) (.leaf ![0, 3, 8, 1]))) (.branch 30 (.branch 29 (.leaf ![23, 3, 19, 1]) (.leaf ![24, 3, 13, 1])) (.branch 31 (.leaf ![0, 3, 0, 1]) (.leaf ![31, 3, 31, 1]))))))

@[expose] public def factorBlock1 : Lean.RArray (Fin 4 → Fin 35) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![28, 3, 28, 1]) (.leaf ![0, 3, 2, 1])) (.branch 3 (.leaf ![20, 3, 9, 1]) (.leaf ![17, 3, 26, 1]))) (.branch 6 (.branch 5 (.leaf ![0, 1, 4, 3]) (.leaf ![24, 1, 18, 3])) (.branch 7 (.leaf ![23, 1, 12, 3]) (.leaf ![0, 1, 0, 3])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![28, 1, 28, 3]) (.leaf ![31, 1, 31, 3])) (.branch 11 (.leaf ![17, 1, 7, 3]) (.leaf ![20, 1, 25, 3]))) (.branch 14 (.branch 13 (.leaf ![21, 29, 8, 3]) (.leaf ![3, 29, 19, 3])) (.branch 15 (.leaf ![10, 29, 13, 3]) (.leaf ![21, 29, 27, 3]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![3, 29, 0, 3]) (.leaf ![10, 29, 32, 3])) (.branch 19 (.leaf ![21, 29, 9, 3]) (.leaf ![3, 29, 26, 3]))) (.branch 22 (.branch 21 (.leaf ![10, 29, 2, 3]) (.leaf ![6, 34, 4, 1])) (.branch 23 (.leaf ![1, 34, 18, 1]) (.leaf ![16, 34, 12, 1])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![6, 34, 30, 1]) (.leaf ![1, 34, 0, 1])) (.branch 27 (.leaf ![16, 34, 33, 1]) (.leaf ![6, 34, 7, 1]))) (.branch 30 (.branch 29 (.leaf ![1, 34, 25, 1]) (.leaf ![16, 34, 14, 1])) (.branch 31 (.leaf ![15, 29, 8, 34]) (.leaf ![5, 29, 19, 34]))))))

@[expose] public def factorBlock2 : Lean.RArray (Fin 4 → Fin 35) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![29, 29, 13, 34]) (.leaf ![15, 29, 30, 34])) (.branch 3 (.leaf ![5, 29, 33, 34]) (.leaf ![29, 29, 0, 34]))) (.branch 6 (.branch 5 (.leaf ![15, 29, 26, 34]) (.leaf ![5, 29, 2, 34])) (.branch 7 (.leaf ![29, 29, 9, 34]) (.leaf ![11, 34, 4, 29])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![22, 34, 18, 29]) (.leaf ![34, 34, 12, 29])) (.branch 11 (.leaf ![11, 34, 27, 29]) (.leaf ![22, 34, 32, 29]))) (.branch 14 (.branch 13 (.leaf ![34, 34, 0, 29]) (.leaf ![11, 34, 25, 29])) (.branch 15 (.leaf ![22, 34, 14, 29]) (.leaf ![34, 34, 7, 29]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![0, 31, 0, 28]) (.leaf ![0, 31, 0, 28])) (.branch 19 (.leaf ![0, 28, 0, 31]) (.leaf ![28, 31, 0, 28]))) (.branch 22 (.branch 21 (.leaf ![31, 31, 0, 28]) (.leaf ![0, 28, 0, 31])) (.branch 23 (.leaf ![31, 31, 0, 28]) (.leaf ![28, 31, 0, 28])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![30, 30, 1, 33]) (.leaf ![1, 33, 1, 30])) (.branch 27 (.leaf ![33, 30, 1, 33]) (.leaf ![27, 32, 3, 27]))) (.branch 30 (.branch 29 (.leaf ![3, 27, 3, 32]) (.leaf ![32, 32, 3, 27])) (.branch 31 (.leaf ![27, 32, 34, 27]) (.leaf ![32, 32, 34, 27]))))))

@[expose] public def factorBlock3 : Lean.RArray (Fin 4 → Fin 35) := (.branch 4 (.branch 2 (.branch 1 (.leaf ![34, 27, 34, 32]) (.leaf ![30, 30, 29, 33])) (.branch 3 (.leaf ![33, 30, 29, 33]) (.leaf ![29, 33, 29, 30]))) (.branch 6 (.branch 5 (.leaf ![0, 32, 3, 27]) (.leaf ![0, 30, 1, 33])) (.branch 7 (.leaf ![0, 30, 29, 33]) (.leaf ![0, 32, 34, 27]))))
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
  ((.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf []) (.leaf [0])) (.branch 3 (.leaf [1]) (.leaf [2]))) (.branch 6 (.branch 5 (.leaf [3]) (.leaf [0, 1])) (.branch 7 (.leaf [0, 3]) (.leaf [1, 0])))) (.branch 12 (.branch 10 (.branch 9 (.leaf [1, 1]) (.leaf [1, 2])) (.branch 11 (.leaf [2, 1]) (.leaf [2, 3]))) (.branch 14 (.branch 13 (.leaf [3, 0]) (.leaf [3, 2])) (.branch 15 (.leaf [3, 3]) (.branch 16 (.leaf [0, 1, 1]) (.leaf [0, 3, 3])))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf [1, 0, 3]) (.leaf [1, 1, 0])) (.branch 20 (.leaf [1, 1, 2]) (.leaf [1, 2, 3]))) (.branch 23 (.branch 22 (.leaf [2, 1, 1]) (.leaf [2, 3, 3])) (.branch 24 (.leaf [3, 0, 1]) (.branch 25 (.leaf [3, 2, 1]) (.leaf [3, 3, 0]))))) (.branch 30 (.branch 28 (.branch 27 (.leaf [3, 3, 2]) (.leaf [0, 1, 0, 1])) (.branch 29 (.leaf [0, 1, 0, 3]) (.leaf [0, 1, 1, 1]))) (.branch 32 (.branch 31 (.leaf [0, 1, 1, 2]) (.leaf [0, 3, 0, 1])) (.branch 33 (.leaf [0, 3, 0, 3]) (.branch 34 (.leaf [0, 3, 3, 2]) (.leaf [1, 1, 1, 0]))))))) : Lean.RArray (List (Fin 4))).get j.val
@[expose] public def wordCodes : Fin 35 → MatrixCode := fun j =>
  ((.branch 17 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 6643) (.leaf 6652)) (.branch 3 (.leaf 4699) (.leaf 6661))) (.branch 6 (.branch 5 (.leaf 9235) (.leaf 4705)) (.branch 7 (.leaf 9247) (.leaf 4708)))) (.branch 12 (.branch 10 (.branch 9 (.leaf 17740) (.leaf 4717)) (.branch 11 (.leaf 4702) (.leaf 9259))) (.branch 14 (.branch 13 (.leaf 9244) (.leaf 9253)) (.branch 15 (.leaf 2836) (.branch 16 (.leaf 17764) (.leaf 2839)))))) (.branch 26 (.branch 21 (.branch 19 (.branch 18 (.leaf 6655) (.leaf 17749)) (.branch 20 (.leaf 17758) (.leaf 6667))) (.branch 23 (.branch 22 (.leaf 17752) (.leaf 2842)) (.branch 24 (.leaf 6649) (.branch 25 (.leaf 6646) (.leaf 2845))))) (.branch 30 (.branch 28 (.branch 27 (.leaf 2854) (.leaf 17761)) (.branch 29 (.leaf 6664) (.leaf 13303))) (.branch 32 (.branch 31 (.leaf 17755) (.leaf 6658)) (.branch 33 (.leaf 2851) (.branch 34 (.leaf 2857) (.leaf 13294))))))) : Lean.RArray MatrixCode).get j.val
set_option maxHeartbeats 4000000 in
public theorem wordEval : ∀ j, (evalWord (nodeGenerator 34) (words j)).val =
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
public theorem valid : table.Valid ambientGenerator (nodeGenerator 34) rep := by
  constructor
  · decide +kernel
  · intro j k
    apply Subtype.ext
    change (rep j).val * (ambientGenerator k).val =
      (evalWord (nodeGenerator 34) (words (factorIndex j k))).val * (rep (next j k)).val
    rw [wordEval]
    exact transitions j k
public theorem cover : RightCosetCover (properNode 34) rep := by
  rw [properNode_eq_wordSubgroup]
  exact table.sound ambientGenerator ambientInverse ambientGenerator_inv
    ambient_wordSubgroup_eq_top (nodeGenerator 34) (symmInv (n := (generatorCodes 34).length))
    (nodeGenerator_inv 34) rep valid
end Matrix.PSL3Three.CertifiedEnumeration.Cosets34
