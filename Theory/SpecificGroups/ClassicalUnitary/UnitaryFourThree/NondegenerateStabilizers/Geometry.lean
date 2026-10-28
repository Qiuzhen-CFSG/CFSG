module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.ReducibleGeometry
public import Mathlib.Algebra.Star.Pi
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Nondegenerate subspaces in the field-nine unitary module

Conjugating a subspace entrywise converts its Hermitian orthogonal complement
into a dot-product orthogonal complement. Conjugation preserves its cardinality,
hence its dimension over the finite field. This proves the dimension formula,
double orthogonal complementation, and the orthogonal direct decomposition of
an arbitrary nondegenerate subspace.

A subspace and its orthogonal complement have identical SU stabilizers and
identical images in the actual projective model. In dimension four this reduces
the three-dimensional stabilizer calculation to the one-dimensional calculation.
The coordinate subspaces and their explicit restriction equivalences provide a
shared interface for the remaining change-of-basis and block calculations.

Source: the unitary conventions and nondegenerate Hermitian geometry in
`refs/KGroup/GLS3/chapter2.tex`, sections 2.6–2.7. These are geometric inputs to
Aschbacher–Smith, Theorem 0.1.2(4), condition K, printed pp.4,482 of
`refs/quasithin.pdf`; no stabilizer classification is assumed here.
-/

open Matrix Module
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.ReducibleGeometry

public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.NondegenerateStabilizers
variable {n : ℕ}

private def conjugateSubspace (W : Submodule FiniteField.Nine (Space n)) :
    Submodule FiniteField.Nine (Space n) where
  carrier := {v | star v ∈ W}
  zero_mem' := by simp
  add_mem' := by intro v w hv hw; simpa using W.add_mem hv hw
  smul_mem' := by intro c v hv; simpa using W.smul_mem (star c) hv

private def conjugateSubspaceEquiv (W : Submodule FiniteField.Nine (Space n)) :
    W ≃ conjugateSubspace W where
  toFun v := ⟨star v.val, by
    change star (star v.val) ∈ W
    rw [star_star]
    exact v.property⟩
  invFun v := ⟨star v.val, v.property⟩
  left_inv v := Subtype.ext (star_star _)
  right_inv v := Subtype.ext (star_star _)

private theorem finrank_conjugateSubspace (W : Submodule FiniteField.Nine (Space n)) :
    finrank FiniteField.Nine (conjugateSubspace W) = finrank FiniteField.Nine W := by
  have h := Nat.card_congr (conjugateSubspaceEquiv W)
  rw [Module.natCard_eq_pow_finrank (K := FiniteField.Nine) (V := W),
    Module.natCard_eq_pow_finrank (K := FiniteField.Nine) (V := conjugateSubspace W),
    FiniteField.Nine.natCard] at h
  exact (Nat.pow_right_injective (by decide : 2 ≤ 9) h).symm

private theorem dotProduct_nondegenerate :
    (dotProductBilin FiniteField.Nine FiniteField.Nine :
      LinearMap.BilinForm FiniteField.Nine (Space n)).Nondegenerate := by
  constructor
  · intro v hv
    apply funext
    intro i
    simpa using hv (Pi.single i 1)
  · intro v hv
    apply funext
    intro i
    simpa using hv (Pi.single i 1)

private theorem orthogonal_eq_dotProduct (W : Submodule FiniteField.Nine (Space n)) :
    orthogonal W = LinearMap.BilinForm.orthogonal
      (dotProductBilin FiniteField.Nine FiniteField.Nine :
        LinearMap.BilinForm FiniteField.Nine (Space n)) (conjugateSubspace W) := by
  ext v
  constructor
  · intro hv w hw
    have h := hv (star w) hw
    simpa [pairing] using h
  · intro hv w hw
    exact hv (star w) (by simpa [conjugateSubspace] using hw)

/-- Hermitian symmetry for the shared pairing. -/
theorem star_pairing (v w : Space n) : star (pairing v w) = pairing w v := by
  exact (Matrix.star_dotProduct w v).symm

/-- The orthogonal complement has the complementary dimension. -/
theorem finrank_orthogonal (W : Submodule FiniteField.Nine (Space n)) :
    finrank FiniteField.Nine (orthogonal W) = n - finrank FiniteField.Nine W := by
  rw [orthogonal_eq_dotProduct,
    LinearMap.BilinForm.finrank_orthogonal dotProduct_nondegenerate,
    finrank_conjugateSubspace]
  simp [Space]

/-- Dimension identity for arbitrary subspaces, without a nondegeneracy assumption. -/
theorem finrank_add_finrank_orthogonal (W : Submodule FiniteField.Nine (Space n)) :
    finrank FiniteField.Nine W + finrank FiniteField.Nine (orthogonal W) = n := by
  rw [finrank_orthogonal]
  have h := Submodule.finrank_le W
  have hd : finrank FiniteField.Nine (Space n) = n := by simp [Space]
  rw [hd] at h
  omega

/-- Orthogonal complementation is an involution. -/
theorem orthogonal_orthogonal (W : Submodule FiniteField.Nine (Space n)) :
    orthogonal (orthogonal W) = W := by
  have hle : W ≤ orthogonal (orthogonal W) := by
    intro v hv w hw
    rw [← star_pairing, hw v hv, star_zero]
  apply (Submodule.eq_of_le_of_finrank_le hle ?_).symm
  rw [finrank_orthogonal, finrank_orthogonal]
  omega

/-- A nondegenerate subspace and its orthogonal complement split the whole space. -/
theorem isCompl_orthogonal (W : Submodule FiniteField.Nine (Space n))
    (hW : radical W = ⊥) : IsCompl W (orthogonal W) := by
  apply IsCompl.of_eq hW
  apply Submodule.eq_top_of_finrank_eq
  have h := Submodule.finrank_sup_add_finrank_inf_eq W (orthogonal W)
  have hr : W ⊓ orthogonal W = ⊥ := hW
  rw [hr, finrank_bot, add_zero, finrank_add_finrank_orthogonal] at h
  simpa [Space] using h

/-- Nondegeneracy is preserved by orthogonal complementation. -/
theorem radical_orthogonal (W : Submodule FiniteField.Nine (Space n)) :
    radical (orthogonal W) = radical W := by
  unfold radical
  rw [orthogonal_orthogonal, inf_comm]

/-- SU has the same setwise stabilizer on the two orthogonal subspaces. -/
theorem specialStabilizer_orthogonal (W : Submodule FiniteField.Nine (Space n)) :
    specialStabilizer (orthogonal W) = specialStabilizer W := by
  apply le_antisymm
  · simpa only [orthogonal_orthogonal] using specialStabilizer_le_orthogonal (orthogonal W)
  · exact specialStabilizer_le_orthogonal W

/-- The equality of stabilizers survives the actual scalar quotient. -/
theorem projectiveStabilizer_orthogonal (W : Submodule FiniteField.Nine (Space n)) :
    projectiveStabilizer (orthogonal W) = projectiveStabilizer W := by
  unfold projectiveStabilizer
  rw [specialStabilizer_orthogonal]

/-- Every nonzero proper four-dimensional subspace has dimension one, two or three. -/
theorem finrank_cases (W : Submodule FiniteField.Nine (Space 4))
    (h0 : W ≠ ⊥) (ht : W ≠ ⊤) :
    finrank FiniteField.Nine W = 1 ∨ finrank FiniteField.Nine W = 2 ∨
      finrank FiniteField.Nine W = 3 := by
  have hpos : finrank FiniteField.Nine W ≠ 0 := by
    intro h
    exact h0 (Submodule.finrank_eq_zero.mp h)
  have hlt := Submodule.finrank_lt ht
  have hdim : finrank FiniteField.Nine (Space 4) = 4 := by simp [Space]
  rw [hdim] at hlt
  omega


/-- The first `d` coordinates of the defining four-dimensional module. -/
@[expose] def coordinateSubspace (d : ℕ) : Submodule FiniteField.Nine (Space 4) where
  carrier := {v | ∀ i : Fin 4, d ≤ i.val → v i = 0}
  zero_mem' := by intro i hi; rfl
  add_mem' := by intro v w hv hw i hi; simp [hv i hi, hw i hi]
  smul_mem' := by intro c v hv i hi; simp [hv i hi]

theorem mem_coordinateSubspace (d : ℕ) (v : Space 4) :
    v ∈ coordinateSubspace d ↔ ∀ i : Fin 4, d ≤ i.val → v i = 0 := Iff.rfl

/-- Restriction and extension by zero identify the coordinate subspace with `Nineᵈ`. -/
def coordinateEquiv (d : ℕ) (hd : d ≤ 4) :
    coordinateSubspace d ≃ₗ[FiniteField.Nine] Space d where
  toFun v i := v.val ⟨i.val, lt_of_lt_of_le i.isLt hd⟩
  invFun v := ⟨fun i => if h : i.val < d then v ⟨i.val, h⟩ else 0, by
    intro i hi
    exact dif_neg (Nat.not_lt.mpr hi)⟩
  left_inv v := by
    apply Subtype.ext
    apply funext
    intro i
    change (if h : i.val < d then v.val ⟨i.val, lt_of_lt_of_le h hd⟩ else 0) = v.val i
    by_cases hi : i.val < d
    · simp [hi]
    · simpa [hi] using (v.property i (Nat.le_of_not_lt hi)).symm
  right_inv v := by
    apply funext
    intro i
    change (if h : i.val < d then v ⟨i.val, h⟩ else 0) = v i
    simp [i.isLt]
  map_add' v w := rfl
  map_smul' c v := rfl

theorem coordinateEquiv_apply (d : ℕ) (hd : d ≤ 4)
    (v : coordinateSubspace d) (i : Fin d) :
    coordinateEquiv d hd v i = v.val ⟨i.val, lt_of_lt_of_le i.isLt hd⟩ := by
  simp [coordinateEquiv]

theorem coordinateEquiv_symm_apply (d : ℕ) (hd : d ≤ 4) (v : Space d) (i : Fin 4) :
    ((coordinateEquiv d hd).symm v).val i =
      if h : i.val < d then v ⟨i.val, h⟩ else 0 := by
  simp [coordinateEquiv]

theorem finrank_coordinateSubspace (d : ℕ) (hd : d ≤ 4) :
    finrank FiniteField.Nine (coordinateSubspace d) = d := by
  rw [(coordinateEquiv d hd).finrank_eq]
  simp [Space]

/-- Every coordinate subspace is nondegenerate for the identity form. -/
theorem radical_coordinateSubspace (d : ℕ) : radical (coordinateSubspace d) = ⊥ := by
  apply bot_unique
  intro v hv
  change v = 0
  apply funext
  intro i
  by_cases hi : d ≤ i.val
  · exact hv.1 i hi
  · have he : Pi.single i (1 : FiniteField.Nine) ∈ coordinateSubspace d := by
      intro j hj
      have hne : j ≠ i := by rintro rfl; exact hi hj
      change (Pi.single i (1 : FiniteField.Nine) : Space 4) j = 0
      simp [hne]
    have h := hv.2 (Pi.single i (1 : FiniteField.Nine)) he
    simpa [pairing] using h

/-- The nondegenerate splitting as an actual linear equivalence. -/
def orthogonalDecomposition (W : Submodule FiniteField.Nine (Space n))
    (hW : radical W = ⊥) : (W × orthogonal W) ≃ₗ[FiniteField.Nine] Space n :=
  W.prodEquivOfIsCompl (orthogonal W) (isCompl_orthogonal W hW)

theorem orthogonalDecomposition_apply (W : Submodule FiniteField.Nine (Space n))
    (hW : radical W = ⊥) (v : W) (w : orthogonal W) :
    orthogonalDecomposition W hW (v, w) = v.val + w.val := by
  simp [orthogonalDecomposition]

/-- The splitting has no mixed terms in its Hermitian Gram matrix. -/
theorem pairing_orthogonalDecomposition (W : Submodule FiniteField.Nine (Space n))
    (hW : radical W = ⊥) (v₁ v₂ : W) (w₁ w₂ : orthogonal W) :
    pairing (orthogonalDecomposition W hW (v₁, w₁))
      (orthogonalDecomposition W hW (v₂, w₂)) =
        pairing v₁.val v₂.val + pairing w₁.val w₂.val := by
  have h12 : pairing v₁.val w₂.val = 0 := w₂.property v₁.val v₁.property
  have h21 : pairing w₁.val v₂.val = 0 := by
    rw [← star_pairing, w₁.property v₂.val v₂.property, star_zero]
  simp only [orthogonalDecomposition_apply, pairing, star_add, add_dotProduct,
    dotProduct_add] at h12 h21 ⊢
  rw [h12, h21]
  simp

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.NondegenerateStabilizers
