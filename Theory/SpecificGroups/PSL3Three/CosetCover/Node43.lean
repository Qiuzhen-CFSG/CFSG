module
public import Theory.SpecificGroups.PSL3Three.CosetCover.Check
/-!
# Checked right cosets for node 43

These are untrusted matrix codes and subgroup words generated from the fixed
lists in `RepresentativeBounds`. The kernel checks determinants, word values,
and every transition by the four ambient generators. `cover` then follows from
`RightCosetTable.sound`, using the proved generation of the actual SL₃(3).

Source: the elementary coset-table argument in `SubgroupEnumeration` and
GLS III, Theorem 6.5.3. Row zero represents the identity matrix.
-/

namespace Matrix.PSL3Three.CertifiedEnumeration.Cosets43
open Theory.GroupTheory Theory.GroupTheory.SubgroupEnumeration CosetCheck
set_option maxRecDepth 100000

@[expose] public def codeBlock0 : Lean.RArray (MatrixCode) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 6643) (.leaf 828)) (.branch 3 (.leaf 855) (.leaf 882))) (.branch 6 (.branch 5 (.leaf 975) (.leaf 1002)) (.branch 7 (.leaf 1029) (.leaf 1056)))) (.branch 12 (.branch 10 (.branch 9 (.leaf 1083) (.leaf 1110)) (.branch 11 (.leaf 1137) (.leaf 1164))) (.branch 14 (.branch 13 (.leaf 1191) (.leaf 2304)) (.branch 15 (.leaf 2459) (.leaf 2486))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf 2513) (.leaf 2540)) (.branch 19 (.leaf 2567) (.leaf 2594))) (.branch 22 (.branch 21 (.leaf 2621) (.leaf 2648)) (.branch 23 (.leaf 3161) (.leaf 3188)))) (.branch 28 (.branch 26 (.branch 25 (.leaf 3215) (.leaf 3242)) (.branch 27 (.leaf 3269) (.leaf 3296))) (.branch 30 (.branch 29 (.leaf 3323) (.leaf 3350)) (.branch 31 (.leaf 3377) (.leaf 3890))))))

@[expose] public def codeBlock1 : Lean.RArray (MatrixCode) := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf 3917) (.leaf 3944)) (.branch 3 (.leaf 3971) (.branch 4 (.leaf 3998) (.leaf 4025)))) (.branch 7 (.branch 6 (.leaf 4052) (.leaf 4079)) (.branch 8 (.leaf 4106) (.branch 9 (.leaf 6837) (.leaf 6886))))) (.branch 15 (.branch 12 (.branch 11 (.leaf 6913) (.leaf 6940)) (.branch 13 (.leaf 7615) (.branch 14 (.leaf 7642) (.leaf 7669)))) (.branch 17 (.branch 16 (.leaf 8344) (.leaf 8371)) (.branch 18 (.leaf 8398) (.branch 19 (.leaf 9105) (.leaf 11373))))))

@[expose] public def nextBlock0 : Lean.RArray (Fin 4 → Fin 52) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![1, 0, 4, 0]) (.leaf ![4, 13, 0, 3])) (.branch 3 (.leaf ![40, 2, 16, 2]) (.leaf ![6, 1, 19, 13]))) (.branch 6 (.branch 5 (.leaf ![0, 22, 1, 38]) (.leaf ![41, 26, 13, 36])) (.branch 7 (.leaf ![19, 30, 3, 31]) (.leaf ![22, 25, 14, 32])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![42, 29, 17, 39]) (.leaf ![30, 24, 20, 34])) (.branch 11 (.leaf ![31, 28, 21, 35]) (.leaf ![43, 23, 18, 33]))) (.branch 14 (.branch 13 (.leaf ![38, 27, 15, 37]) (.leaf ![5, 3, 41, 1])) (.branch 15 (.leaf ![7, 17, 22, 20]) (.leaf ![12, 21, 38, 18]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![2, 16, 40, 16]) (.leaf ![8, 20, 42, 14])) (.branch 19 (.leaf ![11, 15, 43, 21]) (.leaf ![3, 19, 6, 19]))) (.branch 22 (.branch 21 (.leaf ![9, 14, 30, 17]) (.leaf ![10, 18, 31, 15])) (.branch 23 (.leaf ![14, 38, 7, 4]) (.leaf ![44, 33, 25, 11])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![28, 34, 32, 9]) (.leaf ![23, 32, 44, 7])) (.branch 27 (.leaf ![45, 36, 50, 5]) (.leaf ![39, 37, 47, 12]))) (.branch 30 (.branch 29 (.leaf ![32, 35, 24, 10]) (.leaf ![46, 39, 34, 8])) (.branch 31 (.leaf ![20, 31, 9, 6]) (.leaf ![21, 6, 10, 30]))))))

@[expose] public def nextBlock1 : Lean.RArray (Fin 4 → Fin 52) := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf ![24, 7, 28, 25]) (.leaf ![48, 11, 35, 23])) (.branch 3 (.leaf ![29, 9, 46, 24]) (.branch 4 (.leaf ![33, 10, 48, 28]) (.leaf ![49, 5, 51, 26])))) (.branch 7 (.branch 6 (.leaf ![37, 12, 37, 27]) (.leaf ![15, 4, 12, 22])) (.branch 8 (.leaf ![47, 8, 27, 29]) (.branch 9 (.leaf ![16, 42, 2, 43]) (.leaf ![13, 41, 5, 41]))))) (.branch 15 (.branch 12 (.branch 11 (.leaf ![17, 43, 8, 40]) (.leaf ![18, 40, 11, 42])) (.branch 13 (.leaf ![25, 50, 23, 47]) (.branch 14 (.leaf ![50, 45, 26, 45]) (.leaf ![34, 48, 29, 51])))) (.branch 17 (.branch 16 (.leaf ![27, 44, 39, 50]) (.leaf ![35, 51, 33, 46])) (.branch 18 (.leaf ![51, 49, 36, 49]) (.branch 19 (.leaf ![26, 47, 45, 44]) (.leaf ![36, 46, 49, 48]))))))

@[expose] public def factorBlock0 : Lean.RArray (Fin 4 → Fin 39) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![36, 29, 0, 28]) (.leaf ![36, 36, 36, 15])) (.branch 3 (.leaf ![0, 31, 0, 32]) (.leaf ![38, 14, 0, 38]))) (.branch 6 (.branch 5 (.leaf ![0, 4, 36, 18]) (.leaf ![0, 4, 0, 18])) (.branch 7 (.leaf ![38, 4, 38, 18]) (.leaf ![36, 4, 29, 18])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![0, 4, 30, 18]) (.leaf ![38, 4, 11, 18])) (.branch 11 (.leaf ![36, 4, 34, 18]) (.leaf ![0, 4, 17, 18]))) (.branch 14 (.branch 13 (.leaf ![38, 4, 33, 18]) (.leaf ![0, 38, 0, 36])) (.branch 15 (.leaf ![28, 3, 22, 4]) (.leaf ![37, 3, 2, 4]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![0, 3, 0, 4]) (.leaf ![27, 3, 27, 4])) (.branch 19 (.leaf ![19, 3, 19, 4]) (.leaf ![0, 3, 38, 4]))) (.branch 22 (.branch 21 (.leaf ![9, 3, 20, 4]) (.leaf ![35, 3, 13, 4])) (.branch 23 (.leaf ![23, 25, 36, 3]) (.leaf ![3, 25, 22, 3])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![24, 25, 2, 3]) (.leaf ![23, 25, 6, 3])) (.branch 27 (.leaf ![3, 25, 0, 3]) (.leaf ![24, 25, 12, 3]))) (.branch 30 (.branch 29 (.leaf ![23, 25, 20, 3]) (.leaf ![3, 25, 13, 3])) (.branch 31 (.leaf ![24, 25, 38, 3]) (.leaf ![8, 25, 36, 18]))))))

@[expose] public def factorBlock1 : Lean.RArray (Fin 4 → Fin 39) := (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf ![1, 25, 22, 18]) (.leaf ![25, 25, 2, 18])) (.branch 3 (.leaf ![8, 25, 7, 18]) (.branch 4 (.leaf ![1, 25, 26, 18]) (.leaf ![25, 25, 0, 18])))) (.branch 7 (.branch 6 (.leaf ![8, 25, 13, 18]) (.leaf ![1, 25, 38, 18])) (.branch 8 (.leaf ![25, 25, 20, 18]) (.branch 9 (.leaf ![0, 27, 0, 19]) (.leaf ![0, 30, 0, 27]))))) (.branch 15 (.branch 12 (.branch 11 (.leaf ![30, 17, 0, 30]) (.leaf ![17, 17, 0, 19])) (.branch 13 (.leaf ![5, 5, 4, 26]) (.branch 14 (.leaf ![4, 16, 4, 7]) (.leaf ![16, 5, 4, 16])))) (.branch 17 (.branch 16 (.leaf ![10, 21, 18, 10]) (.leaf ![21, 21, 18, 6])) (.branch 18 (.leaf ![18, 10, 18, 12]) (.branch 19 (.leaf ![0, 12, 3, 6]) (.leaf ![0, 7, 25, 26]))))))
@[expose] public def codes : Fin 52 → MatrixCode := fun j =>
  ((.branch 1 (.leaf codeBlock0) (.leaf codeBlock1)) : Lean.RArray (Lean.RArray (MatrixCode))).get (j.val / 32) |>.get (j.val % 32)
@[expose] public def detCheck (k : Nat) : Bool := (codeDet (codes ⟨k % 52, Nat.mod_lt _ (by decide)⟩)).val == 1
set_option maxHeartbeats 4000000 in
private theorem detCheck_0 : checkRange detCheck 0 52 = true := by decide +kernel

public theorem det : ∀ j, codeDet (codes j) = 1 := by
  have h := checkRange_fin (by decide : 0 < 52)
    (fun j => (codeDet (codes j)).val == 1) detCheck_0
  intro j
  apply Fin.ext
  exact beq_iff_eq.mp (h j)
@[expose] public def rep (j : Fin 52) : SL := finiteModelEquiv ⟨codes j, det j⟩
@[expose] public def words : Fin 39 → List (Fin 4) := fun j =>
  ((.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf []) (.leaf [0, 3])) (.branch 3 (.leaf [1, 0]) (.leaf [1, 1]))) (.branch 6 (.branch 5 (.leaf [3, 3]) (.leaf [1, 0, 1])) (.branch 7 (.leaf [3, 0, 3]) (.branch 8 (.leaf [0, 1, 0, 1]) (.leaf [0, 1, 0, 3]))))) (.branch 14 (.branch 11 (.branch 10 (.leaf [0, 1, 1, 0]) (.leaf [0, 3, 0, 3])) (.branch 12 (.leaf [0, 3, 3, 0]) (.branch 13 (.leaf [1, 0, 1, 0]) (.leaf [1, 0, 3, 0])))) (.branch 16 (.branch 15 (.leaf [1, 0, 3, 3]) (.leaf [1, 1, 0, 3])) (.branch 17 (.leaf [3, 0, 3, 0]) (.branch 18 (.leaf [0, 1, 0, 1, 0]) (.leaf [0, 1, 1, 0, 1])))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf [0, 3, 0, 3, 0]) (.leaf [1, 0, 1, 0, 1])) (.branch 22 (.leaf [1, 1, 0, 1, 1]) (.branch 23 (.leaf [1, 1, 1, 0, 1]) (.leaf [3, 0, 1, 1, 1])))) (.branch 26 (.branch 25 (.leaf [3, 0, 3, 0, 3]) (.leaf [3, 0, 3, 3, 0])) (.branch 27 (.leaf [3, 3, 0, 3, 3]) (.branch 28 (.leaf [0, 1, 1, 0, 1, 1]) (.leaf [0, 1, 1, 0, 3, 3]))))) (.branch 34 (.branch 31 (.branch 30 (.leaf [0, 3, 3, 0, 1, 1]) (.leaf [0, 3, 3, 0, 3, 3])) (.branch 32 (.leaf [1, 0, 3, 0, 3, 3]) (.branch 33 (.leaf [1, 1, 0, 1, 0, 3]) (.leaf [0, 1, 0, 1, 0, 1, 1])))) (.branch 36 (.branch 35 (.leaf [0, 1, 0, 1, 0, 3, 3]) (.leaf [0, 1, 0, 1, 1, 1, 0])) (.branch 37 (.leaf [0, 1, 1, 0, 1, 0, 3]) (.branch 38 (.leaf [0, 1, 1, 1, 0, 1, 0]) (.leaf [1, 0, 1, 0, 1, 1, 1]))))))) : Lean.RArray (List (Fin 4))).get j.val
@[expose] public def wordCodes : Fin 39 → MatrixCode := fun j =>
  ((.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf 6643) (.leaf 4705)) (.branch 3 (.leaf 9253) (.leaf 6661))) (.branch 6 (.branch 5 (.leaf 6652) (.leaf 2453)) (.branch 7 (.leaf 2447) (.branch 8 (.leaf 17755) (.leaf 17764))))) (.branch 14 (.branch 11 (.branch 10 (.leaf 6667) (.leaf 17761)) (.branch 12 (.leaf 6655) (.branch 13 (.leaf 2851) (.leaf 2854)))) (.branch 16 (.branch 15 (.leaf 9235) (.leaf 4699)) (.branch 17 (.leaf 2857) (.branch 18 (.leaf 7232) (.leaf 13457)))))) (.branch 29 (.branch 24 (.branch 21 (.branch 20 (.leaf 7226) (.leaf 8930)) (.branch 22 (.leaf 17600) (.branch 23 (.leaf 2450) (.leaf 2438)))) (.branch 26 (.branch 25 (.leaf 8936) (.leaf 13466)) (.branch 27 (.leaf 17594) (.branch 28 (.leaf 6658) (.leaf 6649))))) (.branch 34 (.branch 31 (.branch 30 (.leaf 6646) (.leaf 6664)) (.branch 32 (.leaf 2836) (.branch 33 (.leaf 17740) (.leaf 7214)))) (.branch 36 (.branch 35 (.leaf 7223) (.leaf 7217)) (.branch 37 (.leaf 2432) (.branch 38 (.leaf 7235) (.leaf 8912))))))) : Lean.RArray MatrixCode).get j.val
set_option maxHeartbeats 4000000 in
public theorem wordEval : ∀ j, (evalWord (nodeGenerator 43) (words j)).val =
    decodeMatrix (wordCodes j) := by decide +kernel
@[expose] public def next : Fin 52 → Fin 4 → Fin 52 := fun j =>
  ((.branch 1 (.leaf nextBlock0) (.leaf nextBlock1)) : Lean.RArray (Lean.RArray (Fin 4 → Fin 52))).get (j.val / 32) |>.get (j.val % 32)
@[expose] public def factorIndex : Fin 52 → Fin 4 → Fin 39 := fun j =>
  ((.branch 1 (.leaf factorBlock0) (.leaf factorBlock1)) : Lean.RArray (Lean.RArray (Fin 4 → Fin 39))).get (j.val / 32) |>.get (j.val % 32)
@[expose] public def table : RightCosetTable 4 4 52 where
  base := 0
  next := next
  factor := fun j k => words (factorIndex j k)
@[expose] public def transitionCheck (j : Fin 52) : Bool :=
  matrixEq ((rep j).val * (ambientGenerator 0).val)
    (decodeMatrix (wordCodes (factorIndex j 0)) * (rep (next j 0)).val) &&
  matrixEq ((rep j).val * (ambientGenerator 1).val)
    (decodeMatrix (wordCodes (factorIndex j 1)) * (rep (next j 1)).val) &&
  matrixEq ((rep j).val * (ambientGenerator 2).val)
    (decodeMatrix (wordCodes (factorIndex j 2)) * (rep (next j 2)).val) &&
  matrixEq ((rep j).val * (ambientGenerator 3).val)
    (decodeMatrix (wordCodes (factorIndex j 3)) * (rep (next j 3)).val)
@[expose] public def rowCheck (k : Nat) : Bool := transitionCheck ⟨k % 52, Nat.mod_lt _ (by decide)⟩
set_option maxHeartbeats 4000000 in
private theorem rowCheck_0 : checkRange rowCheck 0 52 = true := by decide +kernel

public theorem checked : ∀ j, transitionCheck j = true :=
  checkRange_fin (by decide) transitionCheck rowCheck_0
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
public theorem valid : table.Valid ambientGenerator (nodeGenerator 43) rep := by
  constructor
  · decide +kernel
  · intro j k
    apply Subtype.ext
    change (rep j).val * (ambientGenerator k).val =
      (evalWord (nodeGenerator 43) (words (factorIndex j k))).val * (rep (next j k)).val
    rw [wordEval]
    exact transitions j k
public theorem cover : RightCosetCover (properNode 43) rep := by
  rw [properNode_eq_wordSubgroup]
  exact table.sound ambientGenerator ambientInverse ambientGenerator_inv
    ambient_wordSubgroup_eq_top (nodeGenerator 43) (symmInv (n := (generatorCodes 43).length))
    (nodeGenerator_inv 43) rep valid
end Matrix.PSL3Three.CertifiedEnumeration.Cosets43
