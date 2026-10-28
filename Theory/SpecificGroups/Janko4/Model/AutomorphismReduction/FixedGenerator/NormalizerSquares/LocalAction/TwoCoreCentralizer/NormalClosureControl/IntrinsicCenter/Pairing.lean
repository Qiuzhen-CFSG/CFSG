module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.IntrinsicCenter.BinaryForms
/-!
# Nondegeneracy of the certified max2 commutator pairing

The Boolean table below records the precise published pair relations. Each
entry is proved from `Certificates.Relations`, including reversed pairs.
Twelve explicit XOR combinations recover coordinates 1 through 12 from their
pairings with the generators. Thus the radical consists only of coordinate 0.
These are identities in Boolean variables, checked by rewriting; neither the
rank proposed in the JSON source nor an external computation is trusted.

The coefficients follow `Certificates/source/kernel_candidate.json`. Source
motivation is the intrinsic center of the normal two-subgroup in GLS3,
Table 5.3i, printed p.270. This proves no assertion about elements outside the
relative seed normal closure.
-/

set_option maxRecDepth 10000

@[expose] public section

namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.IntrinsicCenter
-- Prevent XOR from expanding into nested Boolean comparisons during elaboration.
attribute [local irreducible] bne

/-- The exact commutator table, with the central involution in coordinate zero. -/
def commutatorForm : Fin 13 → Fin 13 → Bool :=
  ![![false, false, false, false, false, false, false, false, false, false, false, false, false],
    ![false, false, false, false, false, true, true, false, true, false, true, false, true],
    ![false, false, false, false, false, false, false, true, true, true, true, true, false],
    ![false, false, false, false, true, false, true, false, false, true, false, true, true],
    ![false, false, false, true, false, true, false, true, false, false, false, true, true],
    ![false, true, false, false, true, false, true, true, false, false, true, false, false],
    ![false, true, false, true, false, true, false, false, true, true, false, true, false],
    ![false, false, true, false, true, true, false, false, true, true, false, false, false],
    ![false, true, true, false, false, false, true, true, false, false, true, true, true],
    ![false, false, true, true, false, false, true, true, false, false, true, false, false],
    ![false, true, true, false, false, true, false, false, true, true, false, true, true],
    ![false, false, true, true, true, false, true, false, true, false, true, false, false],
    ![false, true, false, true, true, false, false, false, true, false, true, false, false]]

private lemma row1 (v : Fin 13 → Bool) : pairing v (commutatorForm 1) = (v 5 ^^ v 6 ^^ v 8 ^^ v 10 ^^ v 12) := by
  change ((v 0 && false) ^^ ((v 1 && false) ^^ ((v 2 && false) ^^ ((v 3 && false) ^^ ((v 4 && false) ^^ ((v 5 && true) ^^ ((v 6 && true) ^^ ((v 7 && false) ^^ ((v 8 && true) ^^ ((v 9 && false) ^^ ((v 10 && true) ^^ ((v 11 && false) ^^ ((v 12 && true) ^^ false))))))))))))) = (v 5 ^^ v 6 ^^ v 8 ^^ v 10 ^^ v 12)
  simp only [Bool.and_true, Bool.and_false, Bool.false_xor, Bool.xor_false, Bool.xor_assoc]

private lemma row2 (v : Fin 13 → Bool) : pairing v (commutatorForm 2) = (v 7 ^^ v 8 ^^ v 9 ^^ v 10 ^^ v 11) := by
  change ((v 0 && false) ^^ ((v 1 && false) ^^ ((v 2 && false) ^^ ((v 3 && false) ^^ ((v 4 && false) ^^ ((v 5 && false) ^^ ((v 6 && false) ^^ ((v 7 && true) ^^ ((v 8 && true) ^^ ((v 9 && true) ^^ ((v 10 && true) ^^ ((v 11 && true) ^^ ((v 12 && false) ^^ false))))))))))))) = (v 7 ^^ v 8 ^^ v 9 ^^ v 10 ^^ v 11)
  simp only [Bool.and_true, Bool.and_false, Bool.false_xor, Bool.xor_false, Bool.xor_assoc]

private lemma row3 (v : Fin 13 → Bool) : pairing v (commutatorForm 3) = (v 4 ^^ v 6 ^^ v 9 ^^ v 11 ^^ v 12) := by
  change ((v 0 && false) ^^ ((v 1 && false) ^^ ((v 2 && false) ^^ ((v 3 && false) ^^ ((v 4 && true) ^^ ((v 5 && false) ^^ ((v 6 && true) ^^ ((v 7 && false) ^^ ((v 8 && false) ^^ ((v 9 && true) ^^ ((v 10 && false) ^^ ((v 11 && true) ^^ ((v 12 && true) ^^ false))))))))))))) = (v 4 ^^ v 6 ^^ v 9 ^^ v 11 ^^ v 12)
  simp only [Bool.and_true, Bool.and_false, Bool.false_xor, Bool.xor_false, Bool.xor_assoc]

private lemma row4 (v : Fin 13 → Bool) : pairing v (commutatorForm 4) = (v 3 ^^ v 5 ^^ v 7 ^^ v 11 ^^ v 12) := by
  change ((v 0 && false) ^^ ((v 1 && false) ^^ ((v 2 && false) ^^ ((v 3 && true) ^^ ((v 4 && false) ^^ ((v 5 && true) ^^ ((v 6 && false) ^^ ((v 7 && true) ^^ ((v 8 && false) ^^ ((v 9 && false) ^^ ((v 10 && false) ^^ ((v 11 && true) ^^ ((v 12 && true) ^^ false))))))))))))) = (v 3 ^^ v 5 ^^ v 7 ^^ v 11 ^^ v 12)
  simp only [Bool.and_true, Bool.and_false, Bool.false_xor, Bool.xor_false, Bool.xor_assoc]

private lemma row5 (v : Fin 13 → Bool) : pairing v (commutatorForm 5) = (v 1 ^^ v 4 ^^ v 6 ^^ v 7 ^^ v 10) := by
  change ((v 0 && false) ^^ ((v 1 && true) ^^ ((v 2 && false) ^^ ((v 3 && false) ^^ ((v 4 && true) ^^ ((v 5 && false) ^^ ((v 6 && true) ^^ ((v 7 && true) ^^ ((v 8 && false) ^^ ((v 9 && false) ^^ ((v 10 && true) ^^ ((v 11 && false) ^^ ((v 12 && false) ^^ false))))))))))))) = (v 1 ^^ v 4 ^^ v 6 ^^ v 7 ^^ v 10)
  simp only [Bool.and_true, Bool.and_false, Bool.false_xor, Bool.xor_false, Bool.xor_assoc]

private lemma row6 (v : Fin 13 → Bool) : pairing v (commutatorForm 6) = (v 1 ^^ v 3 ^^ v 5 ^^ v 8 ^^ v 9 ^^ v 11) := by
  change ((v 0 && false) ^^ ((v 1 && true) ^^ ((v 2 && false) ^^ ((v 3 && true) ^^ ((v 4 && false) ^^ ((v 5 && true) ^^ ((v 6 && false) ^^ ((v 7 && false) ^^ ((v 8 && true) ^^ ((v 9 && true) ^^ ((v 10 && false) ^^ ((v 11 && true) ^^ ((v 12 && false) ^^ false))))))))))))) = (v 1 ^^ v 3 ^^ v 5 ^^ v 8 ^^ v 9 ^^ v 11)
  simp only [Bool.and_true, Bool.and_false, Bool.false_xor, Bool.xor_false, Bool.xor_assoc]

private lemma row7 (v : Fin 13 → Bool) : pairing v (commutatorForm 7) = (v 2 ^^ v 4 ^^ v 5 ^^ v 8 ^^ v 9) := by
  change ((v 0 && false) ^^ ((v 1 && false) ^^ ((v 2 && true) ^^ ((v 3 && false) ^^ ((v 4 && true) ^^ ((v 5 && true) ^^ ((v 6 && false) ^^ ((v 7 && false) ^^ ((v 8 && true) ^^ ((v 9 && true) ^^ ((v 10 && false) ^^ ((v 11 && false) ^^ ((v 12 && false) ^^ false))))))))))))) = (v 2 ^^ v 4 ^^ v 5 ^^ v 8 ^^ v 9)
  simp only [Bool.and_true, Bool.and_false, Bool.false_xor, Bool.xor_false, Bool.xor_assoc]

private lemma row8 (v : Fin 13 → Bool) : pairing v (commutatorForm 8) = (v 1 ^^ v 2 ^^ v 6 ^^ v 7 ^^ v 10 ^^ v 11 ^^ v 12) := by
  change ((v 0 && false) ^^ ((v 1 && true) ^^ ((v 2 && true) ^^ ((v 3 && false) ^^ ((v 4 && false) ^^ ((v 5 && false) ^^ ((v 6 && true) ^^ ((v 7 && true) ^^ ((v 8 && false) ^^ ((v 9 && false) ^^ ((v 10 && true) ^^ ((v 11 && true) ^^ ((v 12 && true) ^^ false))))))))))))) = (v 1 ^^ v 2 ^^ v 6 ^^ v 7 ^^ v 10 ^^ v 11 ^^ v 12)
  simp only [Bool.and_true, Bool.and_false, Bool.false_xor, Bool.xor_false, Bool.xor_assoc]

private lemma row9 (v : Fin 13 → Bool) : pairing v (commutatorForm 9) = (v 2 ^^ v 3 ^^ v 6 ^^ v 7 ^^ v 10) := by
  change ((v 0 && false) ^^ ((v 1 && false) ^^ ((v 2 && true) ^^ ((v 3 && true) ^^ ((v 4 && false) ^^ ((v 5 && false) ^^ ((v 6 && true) ^^ ((v 7 && true) ^^ ((v 8 && false) ^^ ((v 9 && false) ^^ ((v 10 && true) ^^ ((v 11 && false) ^^ ((v 12 && false) ^^ false))))))))))))) = (v 2 ^^ v 3 ^^ v 6 ^^ v 7 ^^ v 10)
  simp only [Bool.and_true, Bool.and_false, Bool.false_xor, Bool.xor_false, Bool.xor_assoc]

private lemma row10 (v : Fin 13 → Bool) : pairing v (commutatorForm 10) = (v 1 ^^ v 2 ^^ v 5 ^^ v 8 ^^ v 9 ^^ v 11 ^^ v 12) := by
  change ((v 0 && false) ^^ ((v 1 && true) ^^ ((v 2 && true) ^^ ((v 3 && false) ^^ ((v 4 && false) ^^ ((v 5 && true) ^^ ((v 6 && false) ^^ ((v 7 && false) ^^ ((v 8 && true) ^^ ((v 9 && true) ^^ ((v 10 && false) ^^ ((v 11 && true) ^^ ((v 12 && true) ^^ false))))))))))))) = (v 1 ^^ v 2 ^^ v 5 ^^ v 8 ^^ v 9 ^^ v 11 ^^ v 12)
  simp only [Bool.and_true, Bool.and_false, Bool.false_xor, Bool.xor_false, Bool.xor_assoc]

private lemma row11 (v : Fin 13 → Bool) : pairing v (commutatorForm 11) = (v 2 ^^ v 3 ^^ v 4 ^^ v 6 ^^ v 8 ^^ v 10) := by
  change ((v 0 && false) ^^ ((v 1 && false) ^^ ((v 2 && true) ^^ ((v 3 && true) ^^ ((v 4 && true) ^^ ((v 5 && false) ^^ ((v 6 && true) ^^ ((v 7 && false) ^^ ((v 8 && true) ^^ ((v 9 && false) ^^ ((v 10 && true) ^^ ((v 11 && false) ^^ ((v 12 && false) ^^ false))))))))))))) = (v 2 ^^ v 3 ^^ v 4 ^^ v 6 ^^ v 8 ^^ v 10)
  simp only [Bool.and_true, Bool.and_false, Bool.false_xor, Bool.xor_false, Bool.xor_assoc]

private lemma row12 (v : Fin 13 → Bool) : pairing v (commutatorForm 12) = (v 1 ^^ v 3 ^^ v 4 ^^ v 8 ^^ v 10) := by
  change ((v 0 && false) ^^ ((v 1 && true) ^^ ((v 2 && false) ^^ ((v 3 && true) ^^ ((v 4 && true) ^^ ((v 5 && false) ^^ ((v 6 && false) ^^ ((v 7 && false) ^^ ((v 8 && true) ^^ ((v 9 && false) ^^ ((v 10 && true) ^^ ((v 11 && false) ^^ ((v 12 && false) ^^ false))))))))))))) = (v 1 ^^ v 3 ^^ v 4 ^^ v 8 ^^ v 10)
  simp only [Bool.and_true, Bool.and_false, Bool.false_xor, Bool.xor_false, Bool.xor_assoc]

private lemma xor_cancel (a b : Bool) : (a ^^ (a ^^ b)) = b := by
  rw [← Bool.xor_assoc, Bool.xor_self, Bool.false_xor]

private lemma coordinate1 (v : Fin 13 → Bool) : v 1 = (pairing v (commutatorForm 3) ^^ pairing v (commutatorForm 4) ^^ pairing v (commutatorForm 8) ^^ pairing v (commutatorForm 10) ^^ pairing v (commutatorForm 12)) := by
  simp only [row3, row4, row8, row10, row12]
  simp only [Bool.false_xor,
    Bool.xor_assoc, Bool.xor_comm, Bool.xor_left_comm, Bool.xor_self, xor_cancel]

private lemma coordinate2 (v : Fin 13 → Bool) : v 2 = (pairing v (commutatorForm 3) ^^ pairing v (commutatorForm 4) ^^ pairing v (commutatorForm 5) ^^ pairing v (commutatorForm 7) ^^ pairing v (commutatorForm 12)) := by
  simp only [row3, row4, row5, row7, row12]
  simp only [Bool.false_xor,
    Bool.xor_assoc, Bool.xor_comm, Bool.xor_left_comm, Bool.xor_self, xor_cancel]

private lemma coordinate3 (v : Fin 13 → Bool) : v 3 = (pairing v (commutatorForm 1) ^^ pairing v (commutatorForm 2) ^^ pairing v (commutatorForm 7) ^^ pairing v (commutatorForm 8) ^^ pairing v (commutatorForm 12)) := by
  simp only [row1, row2, row7, row8, row12]
  simp only [Bool.false_xor,
    Bool.xor_assoc, Bool.xor_comm, Bool.xor_left_comm, Bool.xor_self, xor_cancel]

private lemma coordinate4 (v : Fin 13 → Bool) : v 4 = (pairing v (commutatorForm 1) ^^ pairing v (commutatorForm 2) ^^ pairing v (commutatorForm 9) ^^ pairing v (commutatorForm 10) ^^ pairing v (commutatorForm 12)) := by
  simp only [row1, row2, row9, row10, row12]
  simp only [Bool.false_xor,
    Bool.xor_assoc, Bool.xor_comm, Bool.xor_left_comm, Bool.xor_self, xor_cancel]

private lemma coordinate5 (v : Fin 13 → Bool) : v 5 = (pairing v (commutatorForm 2) ^^ pairing v (commutatorForm 6) ^^ pairing v (commutatorForm 9) ^^ pairing v (commutatorForm 11) ^^ pairing v (commutatorForm 12)) := by
  simp only [row2, row6, row9, row11, row12]
  simp only [Bool.false_xor,
    Bool.xor_assoc, Bool.xor_comm, Bool.xor_left_comm, Bool.xor_self, xor_cancel]

private lemma coordinate6 (v : Fin 13 → Bool) : v 6 = (pairing v (commutatorForm 5) ^^ pairing v (commutatorForm 7) ^^ pairing v (commutatorForm 8) ^^ pairing v (commutatorForm 10) ^^ pairing v (commutatorForm 11) ^^ pairing v (commutatorForm 12)) := by
  simp only [row5, row7, row8, row10, row11, row12]
  simp only [Bool.false_xor,
    Bool.xor_assoc, Bool.xor_comm, Bool.xor_left_comm, Bool.xor_self, xor_cancel]

private lemma coordinate7 (v : Fin 13 → Bool) : v 7 = (pairing v (commutatorForm 2) ^^ pairing v (commutatorForm 3) ^^ pairing v (commutatorForm 6) ^^ pairing v (commutatorForm 10) ^^ pairing v (commutatorForm 11)) := by
  simp only [row2, row3, row6, row10, row11]
  simp only [Bool.false_xor,
    Bool.xor_assoc, Bool.xor_comm, Bool.xor_left_comm, Bool.xor_self, xor_cancel]

private lemma coordinate8 (v : Fin 13 → Bool) : v 8 = (pairing v (commutatorForm 1) ^^ pairing v (commutatorForm 3) ^^ pairing v (commutatorForm 6) ^^ pairing v (commutatorForm 12)) := by
  simp only [row1, row3, row6, row12]
  simp only [Bool.false_xor,
    Bool.xor_assoc, Bool.xor_comm, Bool.xor_left_comm, Bool.xor_self, xor_cancel]

private lemma coordinate9 (v : Fin 13 → Bool) : v 9 = (pairing v (commutatorForm 4) ^^ pairing v (commutatorForm 5) ^^ pairing v (commutatorForm 10) ^^ pairing v (commutatorForm 11)) := by
  simp only [row4, row5, row10, row11]
  simp only [Bool.false_xor,
    Bool.xor_assoc, Bool.xor_comm, Bool.xor_left_comm, Bool.xor_self, xor_cancel]

private lemma coordinate10 (v : Fin 13 → Bool) : v 10 = (pairing v (commutatorForm 1) ^^ pairing v (commutatorForm 4) ^^ pairing v (commutatorForm 6) ^^ pairing v (commutatorForm 7) ^^ pairing v (commutatorForm 9) ^^ pairing v (commutatorForm 12)) := by
  simp only [row1, row4, row6, row7, row9, row12]
  simp only [Bool.false_xor,
    Bool.xor_assoc, Bool.xor_comm, Bool.xor_left_comm, Bool.xor_self, xor_cancel]

private lemma coordinate11 (v : Fin 13 → Bool) : v 11 = (pairing v (commutatorForm 5) ^^ pairing v (commutatorForm 6) ^^ pairing v (commutatorForm 7) ^^ pairing v (commutatorForm 9)) := by
  simp only [row5, row6, row7, row9]
  simp only [    Bool.xor_assoc, Bool.xor_comm, Bool.xor_left_comm, xor_cancel]

private lemma coordinate12 (v : Fin 13 → Bool) : v 12 = (pairing v (commutatorForm 1) ^^ pairing v (commutatorForm 2) ^^ pairing v (commutatorForm 3) ^^ pairing v (commutatorForm 4) ^^ pairing v (commutatorForm 5) ^^ pairing v (commutatorForm 6) ^^ pairing v (commutatorForm 8) ^^ pairing v (commutatorForm 10)) := by
  simp only [row1, row2, row3, row4, row5, row6, row8, row10]
  simp only [Bool.false_xor,
    Bool.xor_assoc, Bool.xor_comm, Bool.xor_left_comm, Bool.xor_self, xor_cancel]

/-- Vanishing pairings force every noncentral coordinate to vanish. -/
lemma radical (v : Fin 13 → Bool) (h : ∀ i, pairing v (commutatorForm i) = false) :
    ∀ j, j ≠ 0 → v j = false := by
  have h1 := coordinate1 v
  rw [h 3, h 4, h 8, h 10, h 12] at h1
  simp only [Bool.false_xor] at h1
  have h2 := coordinate2 v
  rw [h 3, h 4, h 5, h 7, h 12] at h2
  simp only [Bool.false_xor] at h2
  have h3 := coordinate3 v
  rw [h 1, h 2, h 7, h 8, h 12] at h3
  simp only [Bool.false_xor] at h3
  have h4 := coordinate4 v
  rw [h 1, h 2, h 9, h 10, h 12] at h4
  simp only [Bool.false_xor] at h4
  have h5 := coordinate5 v
  rw [h 2, h 6, h 9, h 11, h 12] at h5
  simp only [Bool.false_xor] at h5
  have h6 := coordinate6 v
  rw [h 5, h 7, h 8, h 10, h 11, h 12] at h6
  simp only [Bool.false_xor] at h6
  have h7 := coordinate7 v
  rw [h 2, h 3, h 6, h 10, h 11] at h7
  simp only [Bool.false_xor] at h7
  have h8 := coordinate8 v
  rw [h 1, h 3, h 6, h 12] at h8
  simp only [Bool.false_xor] at h8
  have h9 := coordinate9 v
  rw [h 4, h 5, h 10, h 11] at h9
  simp only [Bool.false_xor] at h9
  have h10 := coordinate10 v
  rw [h 1, h 4, h 6, h 7, h 9, h 12] at h10
  simp only [Bool.false_xor] at h10
  have h11 := coordinate11 v
  rw [h 5, h 6, h 7, h 9] at h11
  simp only [Bool.false_xor] at h11
  have h12 := coordinate12 v
  rw [h 1, h 2, h 3, h 4, h 5, h 6, h 8, h 10] at h12
  simp only [Bool.false_xor] at h12
  intro j hj
  fin_cases j
  · exact (hj rfl).elim
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact h8
  · exact h9
  · exact h10
  · exact h11
  · exact h12


private lemma basis_zero : basis 0 = subgroupInvolution := rfl

attribute [local irreducible] basis

private lemma reverse_relation {G : Type*} [Group G] {a b t : G}
    (ht : t ^ 2 = 1) (h : a * b = b * a * t) : b * a = a * b * t := by
  rw [h, mul_assoc (b * a), ← pow_two, ht, mul_one]

private lemma basis_twist_row0 (j : Fin 13) :
    basis j * basis 0 = basis 0 * basis j * bit subgroupInvolution (commutatorForm 0 j) := by
  fin_cases j
  · change basis 0 * basis 0 = basis 0 * basis 0 * 1
    rw [mul_one]
  · change basis 1 * basis 0 = basis 0 * basis 1 * 1
    rw [mul_one]
    rw [basis_zero]
    exact (Subgroup.mem_center_iff.mp involution_mem_center) (basis 1)
  · change basis 2 * basis 0 = basis 0 * basis 2 * 1
    rw [mul_one]
    rw [basis_zero]
    exact (Subgroup.mem_center_iff.mp involution_mem_center) (basis 2)
  · change basis 3 * basis 0 = basis 0 * basis 3 * 1
    rw [mul_one]
    rw [basis_zero]
    exact (Subgroup.mem_center_iff.mp involution_mem_center) (basis 3)
  · change basis 4 * basis 0 = basis 0 * basis 4 * 1
    rw [mul_one]
    rw [basis_zero]
    exact (Subgroup.mem_center_iff.mp involution_mem_center) (basis 4)
  · change basis 5 * basis 0 = basis 0 * basis 5 * 1
    rw [mul_one]
    rw [basis_zero]
    exact (Subgroup.mem_center_iff.mp involution_mem_center) (basis 5)
  · change basis 6 * basis 0 = basis 0 * basis 6 * 1
    rw [mul_one]
    rw [basis_zero]
    exact (Subgroup.mem_center_iff.mp involution_mem_center) (basis 6)
  · change basis 7 * basis 0 = basis 0 * basis 7 * 1
    rw [mul_one]
    rw [basis_zero]
    exact (Subgroup.mem_center_iff.mp involution_mem_center) (basis 7)
  · change basis 8 * basis 0 = basis 0 * basis 8 * 1
    rw [mul_one]
    rw [basis_zero]
    exact (Subgroup.mem_center_iff.mp involution_mem_center) (basis 8)
  · change basis 9 * basis 0 = basis 0 * basis 9 * 1
    rw [mul_one]
    rw [basis_zero]
    exact (Subgroup.mem_center_iff.mp involution_mem_center) (basis 9)
  · change basis 10 * basis 0 = basis 0 * basis 10 * 1
    rw [mul_one]
    rw [basis_zero]
    exact (Subgroup.mem_center_iff.mp involution_mem_center) (basis 10)
  · change basis 11 * basis 0 = basis 0 * basis 11 * 1
    rw [mul_one]
    rw [basis_zero]
    exact (Subgroup.mem_center_iff.mp involution_mem_center) (basis 11)
  · change basis 12 * basis 0 = basis 0 * basis 12 * 1
    rw [mul_one]
    rw [basis_zero]
    exact (Subgroup.mem_center_iff.mp involution_mem_center) (basis 12)

private lemma basis_twist_row1 (j : Fin 13) :
    basis j * basis 1 = basis 1 * basis j * bit subgroupInvolution (commutatorForm 1 j) := by
  fin_cases j
  · change basis 0 * basis 1 = basis 1 * basis 0 * 1
    rw [mul_one]
    rw [basis_zero]
    exact ((Subgroup.mem_center_iff.mp involution_mem_center) (basis 1)).symm
  · change basis 1 * basis 1 = basis 1 * basis 1 * 1
    rw [mul_one]
  · change basis 2 * basis 1 = basis 1 * basis 2 * 1
    rw [mul_one]
    exact relation_1_2.symm
  · change basis 3 * basis 1 = basis 1 * basis 3 * 1
    rw [mul_one]
    exact relation_1_3.symm
  · change basis 4 * basis 1 = basis 1 * basis 4 * 1
    rw [mul_one]
    exact relation_1_4.symm
  · change basis 5 * basis 1 = basis 1 * basis 5 * subgroupInvolution
    exact reverse_relation (a := basis 1) (b := basis 5) (t := subgroupInvolution) involution_pow_two relation_1_5
  · change basis 6 * basis 1 = basis 1 * basis 6 * subgroupInvolution
    exact reverse_relation (a := basis 1) (b := basis 6) (t := subgroupInvolution) involution_pow_two relation_1_6
  · change basis 7 * basis 1 = basis 1 * basis 7 * 1
    rw [mul_one]
    exact relation_1_7.symm
  · change basis 8 * basis 1 = basis 1 * basis 8 * subgroupInvolution
    exact reverse_relation (a := basis 1) (b := basis 8) (t := subgroupInvolution) involution_pow_two relation_1_8
  · change basis 9 * basis 1 = basis 1 * basis 9 * 1
    rw [mul_one]
    exact relation_1_9.symm
  · change basis 10 * basis 1 = basis 1 * basis 10 * subgroupInvolution
    exact reverse_relation (a := basis 1) (b := basis 10) (t := subgroupInvolution) involution_pow_two relation_1_10
  · change basis 11 * basis 1 = basis 1 * basis 11 * 1
    rw [mul_one]
    exact relation_1_11.symm
  · change basis 12 * basis 1 = basis 1 * basis 12 * subgroupInvolution
    exact reverse_relation (a := basis 1) (b := basis 12) (t := subgroupInvolution) involution_pow_two relation_1_12

private lemma basis_twist_row2 (j : Fin 13) :
    basis j * basis 2 = basis 2 * basis j * bit subgroupInvolution (commutatorForm 2 j) := by
  fin_cases j
  · change basis 0 * basis 2 = basis 2 * basis 0 * 1
    rw [mul_one]
    rw [basis_zero]
    exact ((Subgroup.mem_center_iff.mp involution_mem_center) (basis 2)).symm
  · change basis 1 * basis 2 = basis 2 * basis 1 * 1
    rw [mul_one]
    exact relation_1_2
  · change basis 2 * basis 2 = basis 2 * basis 2 * 1
    rw [mul_one]
  · change basis 3 * basis 2 = basis 2 * basis 3 * 1
    rw [mul_one]
    exact relation_2_3.symm
  · change basis 4 * basis 2 = basis 2 * basis 4 * 1
    rw [mul_one]
    exact relation_2_4.symm
  · change basis 5 * basis 2 = basis 2 * basis 5 * 1
    rw [mul_one]
    exact relation_2_5.symm
  · change basis 6 * basis 2 = basis 2 * basis 6 * 1
    rw [mul_one]
    exact relation_2_6.symm
  · change basis 7 * basis 2 = basis 2 * basis 7 * subgroupInvolution
    exact reverse_relation (a := basis 2) (b := basis 7) (t := subgroupInvolution) involution_pow_two relation_2_7
  · change basis 8 * basis 2 = basis 2 * basis 8 * subgroupInvolution
    exact reverse_relation (a := basis 2) (b := basis 8) (t := subgroupInvolution) involution_pow_two relation_2_8
  · change basis 9 * basis 2 = basis 2 * basis 9 * subgroupInvolution
    exact reverse_relation (a := basis 2) (b := basis 9) (t := subgroupInvolution) involution_pow_two relation_2_9
  · change basis 10 * basis 2 = basis 2 * basis 10 * subgroupInvolution
    exact reverse_relation (a := basis 2) (b := basis 10) (t := subgroupInvolution) involution_pow_two relation_2_10
  · change basis 11 * basis 2 = basis 2 * basis 11 * subgroupInvolution
    exact reverse_relation (a := basis 2) (b := basis 11) (t := subgroupInvolution) involution_pow_two relation_2_11
  · change basis 12 * basis 2 = basis 2 * basis 12 * 1
    rw [mul_one]
    exact relation_2_12.symm

private lemma basis_twist_row3 (j : Fin 13) :
    basis j * basis 3 = basis 3 * basis j * bit subgroupInvolution (commutatorForm 3 j) := by
  fin_cases j
  · change basis 0 * basis 3 = basis 3 * basis 0 * 1
    rw [mul_one]
    rw [basis_zero]
    exact ((Subgroup.mem_center_iff.mp involution_mem_center) (basis 3)).symm
  · change basis 1 * basis 3 = basis 3 * basis 1 * 1
    rw [mul_one]
    exact relation_1_3
  · change basis 2 * basis 3 = basis 3 * basis 2 * 1
    rw [mul_one]
    exact relation_2_3
  · change basis 3 * basis 3 = basis 3 * basis 3 * 1
    rw [mul_one]
  · change basis 4 * basis 3 = basis 3 * basis 4 * subgroupInvolution
    exact reverse_relation (a := basis 3) (b := basis 4) (t := subgroupInvolution) involution_pow_two relation_3_4
  · change basis 5 * basis 3 = basis 3 * basis 5 * 1
    rw [mul_one]
    exact relation_3_5.symm
  · change basis 6 * basis 3 = basis 3 * basis 6 * subgroupInvolution
    exact reverse_relation (a := basis 3) (b := basis 6) (t := subgroupInvolution) involution_pow_two relation_3_6
  · change basis 7 * basis 3 = basis 3 * basis 7 * 1
    rw [mul_one]
    exact relation_3_7.symm
  · change basis 8 * basis 3 = basis 3 * basis 8 * 1
    rw [mul_one]
    exact relation_3_8.symm
  · change basis 9 * basis 3 = basis 3 * basis 9 * subgroupInvolution
    exact reverse_relation (a := basis 3) (b := basis 9) (t := subgroupInvolution) involution_pow_two relation_3_9
  · change basis 10 * basis 3 = basis 3 * basis 10 * 1
    rw [mul_one]
    exact relation_3_10.symm
  · change basis 11 * basis 3 = basis 3 * basis 11 * subgroupInvolution
    exact reverse_relation (a := basis 3) (b := basis 11) (t := subgroupInvolution) involution_pow_two relation_3_11
  · change basis 12 * basis 3 = basis 3 * basis 12 * subgroupInvolution
    exact reverse_relation (a := basis 3) (b := basis 12) (t := subgroupInvolution) involution_pow_two relation_3_12

private lemma basis_twist_row4 (j : Fin 13) :
    basis j * basis 4 = basis 4 * basis j * bit subgroupInvolution (commutatorForm 4 j) := by
  fin_cases j
  · change basis 0 * basis 4 = basis 4 * basis 0 * 1
    rw [mul_one]
    rw [basis_zero]
    exact ((Subgroup.mem_center_iff.mp involution_mem_center) (basis 4)).symm
  · change basis 1 * basis 4 = basis 4 * basis 1 * 1
    rw [mul_one]
    exact relation_1_4
  · change basis 2 * basis 4 = basis 4 * basis 2 * 1
    rw [mul_one]
    exact relation_2_4
  · change basis 3 * basis 4 = basis 4 * basis 3 * subgroupInvolution
    exact relation_3_4
  · change basis 4 * basis 4 = basis 4 * basis 4 * 1
    rw [mul_one]
  · change basis 5 * basis 4 = basis 4 * basis 5 * subgroupInvolution
    exact reverse_relation (a := basis 4) (b := basis 5) (t := subgroupInvolution) involution_pow_two relation_4_5
  · change basis 6 * basis 4 = basis 4 * basis 6 * 1
    rw [mul_one]
    exact relation_4_6.symm
  · change basis 7 * basis 4 = basis 4 * basis 7 * subgroupInvolution
    exact reverse_relation (a := basis 4) (b := basis 7) (t := subgroupInvolution) involution_pow_two relation_4_7
  · change basis 8 * basis 4 = basis 4 * basis 8 * 1
    rw [mul_one]
    exact relation_4_8.symm
  · change basis 9 * basis 4 = basis 4 * basis 9 * 1
    rw [mul_one]
    exact relation_4_9.symm
  · change basis 10 * basis 4 = basis 4 * basis 10 * 1
    rw [mul_one]
    exact relation_4_10.symm
  · change basis 11 * basis 4 = basis 4 * basis 11 * subgroupInvolution
    exact reverse_relation (a := basis 4) (b := basis 11) (t := subgroupInvolution) involution_pow_two relation_4_11
  · change basis 12 * basis 4 = basis 4 * basis 12 * subgroupInvolution
    exact reverse_relation (a := basis 4) (b := basis 12) (t := subgroupInvolution) involution_pow_two relation_4_12

private lemma basis_twist_row5 (j : Fin 13) :
    basis j * basis 5 = basis 5 * basis j * bit subgroupInvolution (commutatorForm 5 j) := by
  fin_cases j
  · change basis 0 * basis 5 = basis 5 * basis 0 * 1
    rw [mul_one]
    rw [basis_zero]
    exact ((Subgroup.mem_center_iff.mp involution_mem_center) (basis 5)).symm
  · change basis 1 * basis 5 = basis 5 * basis 1 * subgroupInvolution
    exact relation_1_5
  · change basis 2 * basis 5 = basis 5 * basis 2 * 1
    rw [mul_one]
    exact relation_2_5
  · change basis 3 * basis 5 = basis 5 * basis 3 * 1
    rw [mul_one]
    exact relation_3_5
  · change basis 4 * basis 5 = basis 5 * basis 4 * subgroupInvolution
    exact relation_4_5
  · change basis 5 * basis 5 = basis 5 * basis 5 * 1
    rw [mul_one]
  · change basis 6 * basis 5 = basis 5 * basis 6 * subgroupInvolution
    exact reverse_relation (a := basis 5) (b := basis 6) (t := subgroupInvolution) involution_pow_two relation_5_6
  · change basis 7 * basis 5 = basis 5 * basis 7 * subgroupInvolution
    exact reverse_relation (a := basis 5) (b := basis 7) (t := subgroupInvolution) involution_pow_two relation_5_7
  · change basis 8 * basis 5 = basis 5 * basis 8 * 1
    rw [mul_one]
    exact relation_5_8.symm
  · change basis 9 * basis 5 = basis 5 * basis 9 * 1
    rw [mul_one]
    exact relation_5_9.symm
  · change basis 10 * basis 5 = basis 5 * basis 10 * subgroupInvolution
    exact reverse_relation (a := basis 5) (b := basis 10) (t := subgroupInvolution) involution_pow_two relation_5_10
  · change basis 11 * basis 5 = basis 5 * basis 11 * 1
    rw [mul_one]
    exact relation_5_11.symm
  · change basis 12 * basis 5 = basis 5 * basis 12 * 1
    rw [mul_one]
    exact relation_5_12.symm

private lemma basis_twist_row6 (j : Fin 13) :
    basis j * basis 6 = basis 6 * basis j * bit subgroupInvolution (commutatorForm 6 j) := by
  fin_cases j
  · change basis 0 * basis 6 = basis 6 * basis 0 * 1
    rw [mul_one]
    rw [basis_zero]
    exact ((Subgroup.mem_center_iff.mp involution_mem_center) (basis 6)).symm
  · change basis 1 * basis 6 = basis 6 * basis 1 * subgroupInvolution
    exact relation_1_6
  · change basis 2 * basis 6 = basis 6 * basis 2 * 1
    rw [mul_one]
    exact relation_2_6
  · change basis 3 * basis 6 = basis 6 * basis 3 * subgroupInvolution
    exact relation_3_6
  · change basis 4 * basis 6 = basis 6 * basis 4 * 1
    rw [mul_one]
    exact relation_4_6
  · change basis 5 * basis 6 = basis 6 * basis 5 * subgroupInvolution
    exact relation_5_6
  · change basis 6 * basis 6 = basis 6 * basis 6 * 1
    rw [mul_one]
  · change basis 7 * basis 6 = basis 6 * basis 7 * 1
    rw [mul_one]
    exact relation_6_7.symm
  · change basis 8 * basis 6 = basis 6 * basis 8 * subgroupInvolution
    exact reverse_relation (a := basis 6) (b := basis 8) (t := subgroupInvolution) involution_pow_two relation_6_8
  · change basis 9 * basis 6 = basis 6 * basis 9 * subgroupInvolution
    exact reverse_relation (a := basis 6) (b := basis 9) (t := subgroupInvolution) involution_pow_two relation_6_9
  · change basis 10 * basis 6 = basis 6 * basis 10 * 1
    rw [mul_one]
    exact relation_6_10.symm
  · change basis 11 * basis 6 = basis 6 * basis 11 * subgroupInvolution
    exact reverse_relation (a := basis 6) (b := basis 11) (t := subgroupInvolution) involution_pow_two relation_6_11
  · change basis 12 * basis 6 = basis 6 * basis 12 * 1
    rw [mul_one]
    exact relation_6_12.symm

private lemma basis_twist_row7 (j : Fin 13) :
    basis j * basis 7 = basis 7 * basis j * bit subgroupInvolution (commutatorForm 7 j) := by
  fin_cases j
  · change basis 0 * basis 7 = basis 7 * basis 0 * 1
    rw [mul_one]
    rw [basis_zero]
    exact ((Subgroup.mem_center_iff.mp involution_mem_center) (basis 7)).symm
  · change basis 1 * basis 7 = basis 7 * basis 1 * 1
    rw [mul_one]
    exact relation_1_7
  · change basis 2 * basis 7 = basis 7 * basis 2 * subgroupInvolution
    exact relation_2_7
  · change basis 3 * basis 7 = basis 7 * basis 3 * 1
    rw [mul_one]
    exact relation_3_7
  · change basis 4 * basis 7 = basis 7 * basis 4 * subgroupInvolution
    exact relation_4_7
  · change basis 5 * basis 7 = basis 7 * basis 5 * subgroupInvolution
    exact relation_5_7
  · change basis 6 * basis 7 = basis 7 * basis 6 * 1
    rw [mul_one]
    exact relation_6_7
  · change basis 7 * basis 7 = basis 7 * basis 7 * 1
    rw [mul_one]
  · change basis 8 * basis 7 = basis 7 * basis 8 * subgroupInvolution
    exact reverse_relation (a := basis 7) (b := basis 8) (t := subgroupInvolution) involution_pow_two relation_7_8
  · change basis 9 * basis 7 = basis 7 * basis 9 * subgroupInvolution
    exact reverse_relation (a := basis 7) (b := basis 9) (t := subgroupInvolution) involution_pow_two relation_7_9
  · change basis 10 * basis 7 = basis 7 * basis 10 * 1
    rw [mul_one]
    exact relation_7_10.symm
  · change basis 11 * basis 7 = basis 7 * basis 11 * 1
    rw [mul_one]
    exact relation_7_11.symm
  · change basis 12 * basis 7 = basis 7 * basis 12 * 1
    rw [mul_one]
    exact relation_7_12.symm

private lemma basis_twist_row8 (j : Fin 13) :
    basis j * basis 8 = basis 8 * basis j * bit subgroupInvolution (commutatorForm 8 j) := by
  fin_cases j
  · change basis 0 * basis 8 = basis 8 * basis 0 * 1
    rw [mul_one]
    rw [basis_zero]
    exact ((Subgroup.mem_center_iff.mp involution_mem_center) (basis 8)).symm
  · change basis 1 * basis 8 = basis 8 * basis 1 * subgroupInvolution
    exact relation_1_8
  · change basis 2 * basis 8 = basis 8 * basis 2 * subgroupInvolution
    exact relation_2_8
  · change basis 3 * basis 8 = basis 8 * basis 3 * 1
    rw [mul_one]
    exact relation_3_8
  · change basis 4 * basis 8 = basis 8 * basis 4 * 1
    rw [mul_one]
    exact relation_4_8
  · change basis 5 * basis 8 = basis 8 * basis 5 * 1
    rw [mul_one]
    exact relation_5_8
  · change basis 6 * basis 8 = basis 8 * basis 6 * subgroupInvolution
    exact relation_6_8
  · change basis 7 * basis 8 = basis 8 * basis 7 * subgroupInvolution
    exact relation_7_8
  · change basis 8 * basis 8 = basis 8 * basis 8 * 1
    rw [mul_one]
  · change basis 9 * basis 8 = basis 8 * basis 9 * 1
    rw [mul_one]
    exact relation_8_9.symm
  · change basis 10 * basis 8 = basis 8 * basis 10 * subgroupInvolution
    exact reverse_relation (a := basis 8) (b := basis 10) (t := subgroupInvolution) involution_pow_two relation_8_10
  · change basis 11 * basis 8 = basis 8 * basis 11 * subgroupInvolution
    exact reverse_relation (a := basis 8) (b := basis 11) (t := subgroupInvolution) involution_pow_two relation_8_11
  · change basis 12 * basis 8 = basis 8 * basis 12 * subgroupInvolution
    exact reverse_relation (a := basis 8) (b := basis 12) (t := subgroupInvolution) involution_pow_two relation_8_12

private lemma basis_twist_row9 (j : Fin 13) :
    basis j * basis 9 = basis 9 * basis j * bit subgroupInvolution (commutatorForm 9 j) := by
  fin_cases j
  · change basis 0 * basis 9 = basis 9 * basis 0 * 1
    rw [mul_one]
    rw [basis_zero]
    exact ((Subgroup.mem_center_iff.mp involution_mem_center) (basis 9)).symm
  · change basis 1 * basis 9 = basis 9 * basis 1 * 1
    rw [mul_one]
    exact relation_1_9
  · change basis 2 * basis 9 = basis 9 * basis 2 * subgroupInvolution
    exact relation_2_9
  · change basis 3 * basis 9 = basis 9 * basis 3 * subgroupInvolution
    exact relation_3_9
  · change basis 4 * basis 9 = basis 9 * basis 4 * 1
    rw [mul_one]
    exact relation_4_9
  · change basis 5 * basis 9 = basis 9 * basis 5 * 1
    rw [mul_one]
    exact relation_5_9
  · change basis 6 * basis 9 = basis 9 * basis 6 * subgroupInvolution
    exact relation_6_9
  · change basis 7 * basis 9 = basis 9 * basis 7 * subgroupInvolution
    exact relation_7_9
  · change basis 8 * basis 9 = basis 9 * basis 8 * 1
    rw [mul_one]
    exact relation_8_9
  · change basis 9 * basis 9 = basis 9 * basis 9 * 1
    rw [mul_one]
  · change basis 10 * basis 9 = basis 9 * basis 10 * subgroupInvolution
    exact reverse_relation (a := basis 9) (b := basis 10) (t := subgroupInvolution) involution_pow_two relation_9_10
  · change basis 11 * basis 9 = basis 9 * basis 11 * 1
    rw [mul_one]
    exact relation_9_11.symm
  · change basis 12 * basis 9 = basis 9 * basis 12 * 1
    rw [mul_one]
    exact relation_9_12.symm

private lemma basis_twist_row10 (j : Fin 13) :
    basis j * basis 10 = basis 10 * basis j * bit subgroupInvolution (commutatorForm 10 j) := by
  fin_cases j
  · change basis 0 * basis 10 = basis 10 * basis 0 * 1
    rw [mul_one]
    rw [basis_zero]
    exact ((Subgroup.mem_center_iff.mp involution_mem_center) (basis 10)).symm
  · change basis 1 * basis 10 = basis 10 * basis 1 * subgroupInvolution
    exact relation_1_10
  · change basis 2 * basis 10 = basis 10 * basis 2 * subgroupInvolution
    exact relation_2_10
  · change basis 3 * basis 10 = basis 10 * basis 3 * 1
    rw [mul_one]
    exact relation_3_10
  · change basis 4 * basis 10 = basis 10 * basis 4 * 1
    rw [mul_one]
    exact relation_4_10
  · change basis 5 * basis 10 = basis 10 * basis 5 * subgroupInvolution
    exact relation_5_10
  · change basis 6 * basis 10 = basis 10 * basis 6 * 1
    rw [mul_one]
    exact relation_6_10
  · change basis 7 * basis 10 = basis 10 * basis 7 * 1
    rw [mul_one]
    exact relation_7_10
  · change basis 8 * basis 10 = basis 10 * basis 8 * subgroupInvolution
    exact relation_8_10
  · change basis 9 * basis 10 = basis 10 * basis 9 * subgroupInvolution
    exact relation_9_10
  · change basis 10 * basis 10 = basis 10 * basis 10 * 1
    rw [mul_one]
  · change basis 11 * basis 10 = basis 10 * basis 11 * subgroupInvolution
    exact reverse_relation (a := basis 10) (b := basis 11) (t := subgroupInvolution) involution_pow_two relation_10_11
  · change basis 12 * basis 10 = basis 10 * basis 12 * subgroupInvolution
    exact reverse_relation (a := basis 10) (b := basis 12) (t := subgroupInvolution) involution_pow_two relation_10_12

private lemma basis_twist_row11 (j : Fin 13) :
    basis j * basis 11 = basis 11 * basis j * bit subgroupInvolution (commutatorForm 11 j) := by
  fin_cases j
  · change basis 0 * basis 11 = basis 11 * basis 0 * 1
    rw [mul_one]
    rw [basis_zero]
    exact ((Subgroup.mem_center_iff.mp involution_mem_center) (basis 11)).symm
  · change basis 1 * basis 11 = basis 11 * basis 1 * 1
    rw [mul_one]
    exact relation_1_11
  · change basis 2 * basis 11 = basis 11 * basis 2 * subgroupInvolution
    exact relation_2_11
  · change basis 3 * basis 11 = basis 11 * basis 3 * subgroupInvolution
    exact relation_3_11
  · change basis 4 * basis 11 = basis 11 * basis 4 * subgroupInvolution
    exact relation_4_11
  · change basis 5 * basis 11 = basis 11 * basis 5 * 1
    rw [mul_one]
    exact relation_5_11
  · change basis 6 * basis 11 = basis 11 * basis 6 * subgroupInvolution
    exact relation_6_11
  · change basis 7 * basis 11 = basis 11 * basis 7 * 1
    rw [mul_one]
    exact relation_7_11
  · change basis 8 * basis 11 = basis 11 * basis 8 * subgroupInvolution
    exact relation_8_11
  · change basis 9 * basis 11 = basis 11 * basis 9 * 1
    rw [mul_one]
    exact relation_9_11
  · change basis 10 * basis 11 = basis 11 * basis 10 * subgroupInvolution
    exact relation_10_11
  · change basis 11 * basis 11 = basis 11 * basis 11 * 1
    rw [mul_one]
  · change basis 12 * basis 11 = basis 11 * basis 12 * 1
    rw [mul_one]
    exact relation_11_12.symm

private lemma basis_twist_row12 (j : Fin 13) :
    basis j * basis 12 = basis 12 * basis j * bit subgroupInvolution (commutatorForm 12 j) := by
  fin_cases j
  · change basis 0 * basis 12 = basis 12 * basis 0 * 1
    rw [mul_one]
    rw [basis_zero]
    exact ((Subgroup.mem_center_iff.mp involution_mem_center) (basis 12)).symm
  · change basis 1 * basis 12 = basis 12 * basis 1 * subgroupInvolution
    exact relation_1_12
  · change basis 2 * basis 12 = basis 12 * basis 2 * 1
    rw [mul_one]
    exact relation_2_12
  · change basis 3 * basis 12 = basis 12 * basis 3 * subgroupInvolution
    exact relation_3_12
  · change basis 4 * basis 12 = basis 12 * basis 4 * subgroupInvolution
    exact relation_4_12
  · change basis 5 * basis 12 = basis 12 * basis 5 * 1
    rw [mul_one]
    exact relation_5_12
  · change basis 6 * basis 12 = basis 12 * basis 6 * 1
    rw [mul_one]
    exact relation_6_12
  · change basis 7 * basis 12 = basis 12 * basis 7 * 1
    rw [mul_one]
    exact relation_7_12
  · change basis 8 * basis 12 = basis 12 * basis 8 * subgroupInvolution
    exact relation_8_12
  · change basis 9 * basis 12 = basis 12 * basis 9 * 1
    rw [mul_one]
    exact relation_9_12
  · change basis 10 * basis 12 = basis 12 * basis 10 * subgroupInvolution
    exact relation_10_12
  · change basis 11 * basis 12 = basis 12 * basis 11 * 1
    rw [mul_one]
    exact relation_11_12
  · change basis 12 * basis 12 = basis 12 * basis 12 * 1
    rw [mul_one]

/-- Every table entry is the corresponding relation in the actual local subgroup. -/
lemma basis_twist (i j : Fin 13) :
    basis j * basis i = basis i * basis j * bit subgroupInvolution (commutatorForm i j) := by
  fin_cases i
  · exact basis_twist_row0 j
  · exact basis_twist_row1 j
  · exact basis_twist_row2 j
  · exact basis_twist_row3 j
  · exact basis_twist_row4 j
  · exact basis_twist_row5 j
  · exact basis_twist_row6 j
  · exact basis_twist_row7 j
  · exact basis_twist_row8 j
  · exact basis_twist_row9 j
  · exact basis_twist_row10 j
  · exact basis_twist_row11 j
  · exact basis_twist_row12 j

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.IntrinsicCenter
