module
public import Theory.SpecificGroups.PSL3Three.CosetCover.Check
/-!
# Checked right cosets for node 48

These are untrusted matrix codes and subgroup words generated from the fixed
lists in `RepresentativeBounds`. The kernel checks determinants, word values,
and every transition by the four ambient generators. `cover` then follows from
`RightCosetTable.sound`, using the proved generation of the actual SL₃(3).

Source: the elementary coset-table argument in `SubgroupEnumeration` and
GLS III, Theorem 6.5.3. Row zero represents the identity matrix.
-/

namespace Matrix.PSL3Three.CertifiedEnumeration.Cosets48
open Theory.GroupTheory Theory.GroupTheory.SubgroupEnumeration CosetCheck
set_option maxRecDepth 100000

@[expose] public def codeBlock0 : Lean.RArray (MatrixCode) := (.branch 6 (.branch 3 (.branch 1 (.leaf 6643) (.branch 2 (.leaf 828) (.leaf 829))) (.branch 4 (.leaf 830) (.branch 5 (.leaf 831) (.leaf 832)))) (.branch 9 (.branch 7 (.leaf 833) (.branch 8 (.leaf 834) (.leaf 835))) (.branch 11 (.branch 10 (.leaf 836) (.leaf 975)) (.branch 12 (.leaf 976) (.leaf 977)))))

@[expose] public def nextBlock0 : Lean.RArray (Fin 4 → Fin 13) := (.branch 6 (.branch 3 (.branch 1 (.leaf ![1, 11, 10, 12]) (.branch 2 (.leaf ![10, 1, 0, 1]) (.leaf ![4, 5, 12, 8]))) (.branch 4 (.leaf ![7, 9, 11, 6]) (.branch 5 (.leaf ![12, 4, 2, 4]) (.leaf ![6, 8, 8, 2])))) (.branch 9 (.branch 7 (.leaf ![8, 3, 5, 9]) (.branch 8 (.leaf ![11, 7, 3, 7]) (.leaf ![5, 2, 6, 5]))) (.branch 11 (.branch 10 (.leaf ![9, 6, 9, 3]) (.leaf ![0, 10, 1, 10])) (.branch 12 (.leaf ![3, 12, 7, 0]) (.leaf ![2, 0, 4, 11])))))

@[expose] public def factorBlock0 : Lean.RArray (Fin 4 → Fin 24) := (.branch 6 (.branch 3 (.branch 1 (.leaf ![16, 18, 0, 4]) (.branch 2 (.leaf ![16, 11, 16, 13]) (.leaf ![21, 11, 5, 13]))) (.branch 4 (.leaf ![15, 11, 10, 13]) (.branch 5 (.leaf ![16, 11, 20, 13]) (.leaf ![7, 11, 1, 13])))) (.branch 9 (.branch 7 (.leaf ![9, 11, 8, 13]) (.branch 8 (.leaf ![16, 11, 19, 13]) (.leaf ![3, 11, 14, 13]))) (.branch 11 (.branch 10 (.leaf ![23, 11, 22, 13]) (.leaf ![0, 5, 16, 6])) (.branch 12 (.leaf ![12, 10, 16, 17]) (.leaf ![6, 2, 16, 12])))))
@[expose] public def codes : Fin 13 → MatrixCode := fun j =>
  ((.leaf codeBlock0) : Lean.RArray (Lean.RArray (MatrixCode))).get (j.val / 32) |>.get (j.val % 32)
@[expose] public def detCheck (k : Nat) : Bool := (codeDet (codes ⟨k % 13, Nat.mod_lt _ (by decide)⟩)).val == 1
set_option maxHeartbeats 4000000 in
private theorem detCheck_0 : checkRange detCheck 0 13 = true := by decide +kernel

public theorem det : ∀ j, codeDet (codes j) = 1 := by
  have h := checkRange_fin (by decide : 0 < 13)
    (fun j => (codeDet (codes j)).val == 1) detCheck_0
  intro j
  apply Fin.ext
  exact beq_iff_eq.mp (h j)
@[expose] public def rep (j : Fin 13) : SL := finiteModelEquiv ⟨codes j, det j⟩
@[expose] public def words : Fin 24 → List (Fin 4) := fun j =>
  ((.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf []) (.branch 2 (.leaf [0, 1, 2]) (.leaf [0, 3, 0]))) (.branch 4 (.leaf [0, 3, 2]) (.branch 5 (.leaf [2, 1, 2]) (.leaf [1, 0, 1, 0])))) (.branch 9 (.branch 7 (.leaf [2, 3, 2, 3]) (.branch 8 (.leaf [1, 0, 1, 2, 3]) (.leaf [1, 0, 3, 2, 3]))) (.branch 10 (.leaf [1, 1, 1, 0, 1]) (.branch 11 (.leaf [1, 2, 3, 3, 0]) (.leaf [2, 1, 0, 3, 0]))))) (.branch 18 (.branch 15 (.branch 13 (.leaf [2, 1, 1, 0, 3]) (.branch 14 (.leaf [2, 1, 2, 3, 0]) (.leaf [3, 2, 3, 3, 3]))) (.branch 16 (.leaf [0, 1, 0, 1, 1, 1]) (.branch 17 (.leaf [1, 0, 1, 2, 3, 0]) (.leaf [1, 1, 1, 0, 1, 0])))) (.branch 21 (.branch 19 (.leaf [2, 3, 2, 3, 3, 3]) (.branch 20 (.leaf [3, 3, 3, 2, 3, 2]) (.leaf [0, 1, 0, 1, 0, 3, 0]))) (.branch 22 (.leaf [0, 1, 0, 1, 2, 1, 2]) (.branch 23 (.leaf [0, 3, 0, 1, 1, 1, 2]) (.leaf [0, 3, 3, 3, 2, 1, 2])))))) : Lean.RArray (List (Fin 4))).get j.val
@[expose] public def wordCodes : Fin 24 → MatrixCode := fun j =>
  ((.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf 6643) (.branch 2 (.leaf 2648) (.leaf 3161))) (.branch 4 (.leaf 10451) (.branch 5 (.leaf 2459) (.leaf 7372)))) (.branch 9 (.branch 7 (.leaf 8101) (.branch 8 (.leaf 17012) (.leaf 2567))) (.branch 10 (.leaf 12637) (.branch 11 (.leaf 13934) (.leaf 8830))))) (.branch 18 (.branch 15 (.branch 13 (.leaf 14663) (.branch 14 (.leaf 11017) (.leaf 2809))) (.branch 16 (.leaf 6076) (.branch 17 (.leaf 2432) (.leaf 5347)))) (.branch 21 (.branch 19 (.leaf 2701) (.branch 20 (.leaf 2728) (.leaf 2486))) (.branch 22 (.leaf 3890) (.branch 23 (.leaf 2890) (.leaf 19198)))))) : Lean.RArray MatrixCode).get j.val
set_option maxHeartbeats 4000000 in
public theorem wordEval : ∀ j, (evalWord (nodeGenerator 48) (words j)).val =
    decodeMatrix (wordCodes j) := by decide +kernel
@[expose] public def next : Fin 13 → Fin 4 → Fin 13 := fun j =>
  ((.leaf nextBlock0) : Lean.RArray (Lean.RArray (Fin 4 → Fin 13))).get (j.val / 32) |>.get (j.val % 32)
@[expose] public def factorIndex : Fin 13 → Fin 4 → Fin 24 := fun j =>
  ((.leaf factorBlock0) : Lean.RArray (Lean.RArray (Fin 4 → Fin 24))).get (j.val / 32) |>.get (j.val % 32)
@[expose] public def table : RightCosetTable 4 4 13 where
  base := 0
  next := next
  factor := fun j k => words (factorIndex j k)
@[expose] public def transitionCheck (j : Fin 13) : Bool :=
  matrixEq ((rep j).val * (ambientGenerator 0).val)
    (decodeMatrix (wordCodes (factorIndex j 0)) * (rep (next j 0)).val) &&
  matrixEq ((rep j).val * (ambientGenerator 1).val)
    (decodeMatrix (wordCodes (factorIndex j 1)) * (rep (next j 1)).val) &&
  matrixEq ((rep j).val * (ambientGenerator 2).val)
    (decodeMatrix (wordCodes (factorIndex j 2)) * (rep (next j 2)).val) &&
  matrixEq ((rep j).val * (ambientGenerator 3).val)
    (decodeMatrix (wordCodes (factorIndex j 3)) * (rep (next j 3)).val)
@[expose] public def rowCheck (k : Nat) : Bool := transitionCheck ⟨k % 13, Nat.mod_lt _ (by decide)⟩
set_option maxHeartbeats 4000000 in
private theorem rowCheck_0 : checkRange rowCheck 0 13 = true := by decide +kernel

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
public theorem valid : table.Valid ambientGenerator (nodeGenerator 48) rep := by
  constructor
  · decide +kernel
  · intro j k
    apply Subtype.ext
    change (rep j).val * (ambientGenerator k).val =
      (evalWord (nodeGenerator 48) (words (factorIndex j k))).val * (rep (next j k)).val
    rw [wordEval]
    exact transitions j k
public theorem cover : RightCosetCover (properNode 48) rep := by
  rw [properNode_eq_wordSubgroup]
  exact table.sound ambientGenerator ambientInverse ambientGenerator_inv
    ambient_wordSubgroup_eq_top (nodeGenerator 48) (symmInv (n := (generatorCodes 48).length))
    (nodeGenerator_inv 48) rep valid
end Matrix.PSL3Three.CertifiedEnumeration.Cosets48
