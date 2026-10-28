module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.Model
public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.Algebra.Pointwise.Stabilizer
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

/-!
# Reducible subgroups of the field-nine projective unitary model

Subspace stabilizers are defined first in SU and then mapped to its actual
image in PGL. Every scalar in the projection kernel fixes every subspace,
so the inverse image of the projective stabilizer is exactly the SU
stabilizer. This identifies containment with invariance under the full lift.

Isometries preserve orthogonal complements and radicals. Thus every
reducible subgroup stabilizes either a nonzero proper totally isotropic
subspace (the radical), or a nonzero proper nondegenerate subspace. This
covers arbitrary degenerate subspaces, not only chosen coordinate parabolics.
No classification of the stabilizers is asserted here.

The pairing is conjugate-linear in the first variable and linear in the
second, with the identity Gram matrix and cube conjugation of the shared
model. Source: the unitary geometry in GLS3, chapter 2, and the reducible
case of Aschbacher–Smith, Theorem 0.1.2(4), condition K, printed pp.4,482
of `refs/quasithin.pdf`.
-/

open scoped Pointwise
open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree

public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.ReducibleGeometry

/-- The defining vector space over the field of nine elements. -/
abbrev Space (n : ℕ) := Fin n → FiniteField.Nine

variable {n : ℕ}

/-- The identity Hermitian pairing, conjugate-linear in its first argument. -/
@[expose] def pairing (v w : Space n) : FiniteField.Nine := star v ⬝ᵥ w

/-- The right orthogonal complement for the stored Hermitian pairing. -/
@[expose] def orthogonal (W : Submodule FiniteField.Nine (Space n)) :
    Submodule FiniteField.Nine (Space n) where
  carrier := {v | ∀ w ∈ W, pairing w v = 0}
  zero_mem' := by simp [pairing]
  add_mem' := by
    intro v w hv hw x hx
    change star x ⬝ᵥ (v + w) = 0
    rw [dotProduct_add, show star x ⬝ᵥ v = 0 from hv x hx,
      show star x ⬝ᵥ w = 0 from hw x hx, add_zero]
  smul_mem' := by
    intro c v hv w hw
    change star w ⬝ᵥ (c • v) = 0
    rw [dotProduct_smul, show star w ⬝ᵥ v = 0 from hv w hw, smul_zero]

/-- The radical of the restricted Hermitian form. -/
@[expose] def radical (W : Submodule FiniteField.Nine (Space n)) := W ⊓ orthogonal W

/-- The defining linear action of SU, before taking the scalar quotient. -/
@[expose] def linearAction (n : ℕ) : (form n).specialSubgroup →*
    ((Space n) ≃ₗ[FiniteField.Nine] (Space n)) :=
  ((LinearMap.GeneralLinearGroup.generalLinearEquiv FiniteField.Nine (Space n)).toMonoidHom.comp
    Matrix.GeneralLinearGroup.toLin.toMonoidHom).comp (form n).specialSubgroup.subtype

/-- The full setwise stabilizer of a subspace in SU. -/
@[expose] def specialStabilizer (W : Submodule FiniteField.Nine (Space n)) :
    Subgroup (form n).specialSubgroup :=
  (MulAction.stabilizer ((Space n) ≃ₗ[FiniteField.Nine] (Space n)) W).comap (linearAction n)

theorem mem_specialStabilizer_iff (W : Submodule FiniteField.Nine (Space n))
    (g : (form n).specialSubgroup) :
    g ∈ specialStabilizer W ↔ ∀ v, g.val.val.mulVec v ∈ W ↔ v ∈ W := by
  change linearAction n g ∈ MulAction.stabilizer _ W ↔ _
  rw [Submodule.stabilizer_coe, MulAction.mem_stabilizer_set]
  rfl

theorem pairing_mulVec (g : (form n).specialSubgroup) (v w : Space n) :
    pairing (g.val.val.mulVec v) (g.val.val.mulVec w) = pairing v w := by
  have hg := ((form n).mem_specialSubgroup_iff g.val).mp g.property
  have hA : g.val.val.conjTranspose * g.val.val = 1 := by
    have h := hg.1
    change g.val.val.conjTranspose * 1 * g.val.val = 1 at h
    simpa using h
  unfold pairing
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, hA, one_mulVec]

theorem specialStabilizer_le_orthogonal (W : Submodule FiniteField.Nine (Space n)) :
    specialStabilizer W ≤ specialStabilizer (orthogonal W) := by
  have aux : ∀ (g : (form n).specialSubgroup), g ∈ specialStabilizer W →
      ∀ v ∈ orthogonal W, g.val.val.mulVec v ∈ orthogonal W := by
    intro g hg v hv w hw
    have hi := (mem_specialStabilizer_iff W (g⁻¹)).mp ((specialStabilizer W).inv_mem hg)
    have hw' := hv _ ((hi w).mpr hw)
    have he := pairing_mulVec g ((g⁻¹).val.val.mulVec w) v
    simpa only [mulVec_mulVec, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel,
      Subgroup.coe_one, Units.val_one, one_mulVec, hw'] using he
  intro g hg
  rw [mem_specialStabilizer_iff]
  intro v
  constructor
  · intro hv
    have h := aux (g⁻¹) ((specialStabilizer W).inv_mem hg) _ hv
    simpa only [mulVec_mulVec, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel,
      Subgroup.coe_one, Units.val_one, one_mulVec] using h
  · exact aux g hg v

theorem specialStabilizer_le_radical (W : Submodule FiniteField.Nine (Space n)) :
    specialStabilizer W ≤ specialStabilizer (radical W) := by
  intro g hg
  have h1 := (mem_specialStabilizer_iff W g).mp hg
  have h2 := (mem_specialStabilizer_iff (orthogonal W) g).mp
    (specialStabilizer_le_orthogonal W hg)
  rw [mem_specialStabilizer_iff]
  intro v
  exact and_congr (h1 v) (h2 v)

theorem radical_totallyIsotropic (W : Submodule FiniteField.Nine (Space n)) :
    radical W ≤ orthogonal (radical W) := by
  intro v hv w hw
  exact hv.2 w hw.1

/-- The image of the full SU stabilizer in the actual projective model. -/
@[expose] def projectiveStabilizer (W : Submodule FiniteField.Nine (Space n)) :
    Subgroup (Carrier n) := (specialStabilizer W).map (project n)

theorem ker_project_le_specialStabilizer (W : Submodule FiniteField.Nine (Space n)) :
    (project n).ker ≤ specialStabilizer W := by
  intro g hg
  have h : ProjGenLinGroup.mk g.val = 1 :=
    congrArg Subtype.val (MonoidHom.mem_ker.mp hg)
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at h
  obtain ⟨u, hu⟩ := h
  rw [mem_specialStabilizer_iff]
  intro v
  rw [← hu]
  change (Matrix.diagonal (fun _ : Fin n => u.val)) *ᵥ v ∈ W ↔ v ∈ W
  rw [Matrix.diagonal_const_mulVec]
  exact W.smul_mem_iff u.ne_zero

theorem comap_projectiveStabilizer (W : Submodule FiniteField.Nine (Space n)) :
    (projectiveStabilizer W).comap (project n) = specialStabilizer W := by
  ext g
  constructor
  · rintro ⟨a, ha, hag⟩
    have hker : a⁻¹ * g ∈ (project n).ker := by
      simp only [MonoidHom.mem_ker, map_mul, map_inv, hag, inv_mul_cancel]
    have h := (specialStabilizer W).mul_mem ha (ker_project_le_specialStabilizer W hker)
    simpa using h
  · intro hg
    exact ⟨g, hg, rfl⟩

theorem le_projectiveStabilizer_iff (U : Subgroup (Carrier n))
    (W : Submodule FiniteField.Nine (Space n)) :
    U ≤ projectiveStabilizer W ↔
      ∀ g : (form n).specialSubgroup, project n g ∈ U →
        ∀ v ∈ W, g.val.val.mulVec v ∈ W := by
  constructor
  · intro h g hg
    have hs : g ∈ specialStabilizer W := by
      rw [← comap_projectiveStabilizer]
      exact h hg
    exact fun v hv => ((mem_specialStabilizer_iff W g).mp hs v).mpr hv
  · intro h x hx
    obtain ⟨g, rfl⟩ := project_surjective n x
    refine ⟨g, ?_, rfl⟩
    change g ∈ specialStabilizer W
    rw [mem_specialStabilizer_iff]
    intro v
    constructor
    · intro hv
      have hi : project n (g⁻¹) ∈ U := by simpa only [map_inv] using U.inv_mem hx
      have hh := h (g⁻¹) hi _ hv
      simpa only [mulVec_mulVec, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel,
        Subgroup.coe_one, Units.val_one, one_mulVec] using hh
    · exact h g hx v

theorem projectiveStabilizer_le_radical (W : Submodule FiniteField.Nine (Space n)) :
    projectiveStabilizer W ≤ projectiveStabilizer (radical W) :=
  Subgroup.map_mono (specialStabilizer_le_radical W)

/-- Every reducible subgroup lies in one of the two geometric stabilizer families. -/
theorem reducible_stabilizer_alternative (U : Subgroup (Carrier 4)) (hU : IsReducible U) :
    (∃ W : Submodule FiniteField.Nine (Space 4), W ≠ ⊥ ∧ W ≠ ⊤ ∧
      W ≤ orthogonal W ∧ U ≤ projectiveStabilizer W) ∨
    (∃ W : Submodule FiniteField.Nine (Space 4), W ≠ ⊥ ∧ W ≠ ⊤ ∧
      radical W = ⊥ ∧ U ≤ projectiveStabilizer W) := by
  obtain ⟨W, hW0, hWtop, hW⟩ := hU
  have hle := (le_projectiveStabilizer_iff U W).mpr hW
  by_cases hr : radical W = ⊥
  · exact Or.inr ⟨W, hW0, hWtop, hr, hle⟩
  · refine Or.inl ⟨radical W, hr, ?_, radical_totallyIsotropic W,
      hle.trans (projectiveStabilizer_le_radical W)⟩
    intro ht
    exact hWtop (top_unique (ht ▸ (inf_le_left : radical W ≤ W)))

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.ReducibleGeometry
