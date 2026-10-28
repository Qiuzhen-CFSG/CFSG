module

public import Theory.SpecificGroups.Monster.Construction.LocalC.ShortVectors
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.SignedModules.Spin
public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# The natural-spin tensor summand

The fixed carrier is the tensor product of the real coordinate space and
the actual signed Parker spin space. Its dimension is 24 times 4096, and
its bilinear form is exactly the tensor product of the forms on these
factors. The tensor product of their orthonormal bases proves positivity.
The finite coordinate form is kept separate to avoid expanding the Parker
quotient while checking elementary scalar identities.

Source: Aschbacher, *Sporadic Groups*, the construction preceding Lemma
27.5, printed p. 147. Identification of the natural coordinate action and
its tensor kernel remains with the triality/local-group assembly.
-/

@[expose] public section
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators TensorProduct
namespace Sporadic.Monster.Construction.LocalC
open TrialitySpin

/-- The standard real form on the natural coordinate space. -/
def coordinateDot (ι : Type*) [Fintype ι] : LinearMap.BilinForm ℝ (ι → ℝ) where
  toFun v :=
    { toFun w := ∑ i, v i * w i
      map_add' := by intro u w; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by intro a w; simp [Finset.mul_sum, mul_left_comm] }
  map_add' := by intro v w; ext u; simp [add_mul, Finset.sum_add_distrib]
  map_smul' := by intro a v; ext w; simp [Finset.mul_sum, mul_assoc]

abbrev naturalForm := coordinateDot (Fin 24)

theorem naturalForm_basis (i j : Fin 24) :
    naturalForm ((Pi.basisFun ℝ (Fin 24)) i) ((Pi.basisFun ℝ (Fin 24)) j) =
      if i = j then 1 else 0 := by
  simp [coordinateDot, Pi.basisFun_apply, Pi.single_apply, ite_mul]

/-- The fixed tensor summand, with the source's actual Parker spin space. -/
abbrev MinusSpace := NaturalSpace ⊗[ℝ] SpinSpace

def minusForm : LinearMap.BilinForm ℝ MinusSpace := naturalForm.tmul bothAxesDomain.form

abbrev MinusIndex := Fin 24 × bothAxesDomain.signedOrbits.toPairing.Orbit
instance : Fintype MinusIndex := Fintype.ofFinite _

def minusBasis : Module.Basis MinusIndex ℝ MinusSpace :=
  (Pi.basisFun ℝ (Fin 24)).tensorProduct bothAxesDomain.basis

theorem minusSpace_finrank : Module.finrank ℝ MinusSpace = 98304 := by
  rw [Module.finrank_tensorProduct, Module.finrank_fintype_fun_eq_card, finrank_spinSpace]
  rfl

/-- The prescribed product form, on pure tensors. -/
theorem minusForm_tmul (a b : NaturalSpace) (v w : SpinSpace) :
    minusForm (a ⊗ₜ[ℝ] v) (b ⊗ₜ[ℝ] w) = naturalForm a b * bothAxesDomain.form v w := by
  rw [minusForm, LinearMap.BilinForm.tensorDistrib_tmul]
  exact mul_comm _ _

theorem minusBasis_orthonormal (i j : MinusIndex) :
    minusForm (minusBasis i) (minusBasis j) = if i = j then 1 else 0 := by
  simp only [minusBasis, Module.Basis.tensorProduct_apply', minusForm_tmul,
    naturalForm_basis, SpinDomain.basis_orthonormal]
  by_cases h₁ : i.1 = j.1 <;> by_cases h₂ : i.2 = j.2 <;>
    simp [h₁, h₂, Prod.ext_iff]

def minusCoordinateForm : LinearMap.BilinForm ℝ MinusSpace :=
  (coordinateDot MinusIndex).compl₁₂ minusBasis.equivFun.toLinearMap
    minusBasis.equivFun.toLinearMap

theorem minusForm_eq_coordinates : minusForm = minusCoordinateForm := by
  apply LinearMap.BilinForm.ext_basis minusBasis
  intro i j
  rw [minusBasis_orthonormal]
  change (if i = j then (1 : ℝ) else 0) =
    ∑ k, minusBasis.repr (minusBasis i) k * minusBasis.repr (minusBasis j) k
  simp only [Module.Basis.repr_self, Finsupp.single_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [eq_comm]

theorem minusForm_coordinates (v w : MinusSpace) :
    minusForm v w = ∑ i, minusBasis.repr v i * minusBasis.repr w i := by
  rw [minusForm_eq_coordinates]
  rfl

theorem minusForm_symmetric (v w : MinusSpace) : minusForm v w = minusForm w v := by
  rw [minusForm_coordinates, minusForm_coordinates]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

theorem minusForm_nonneg (v : MinusSpace) : 0 ≤ minusForm v v := by
  rw [minusForm_coordinates]
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)

theorem minusForm_pos (v : MinusSpace) (hv : v ≠ 0) : 0 < minusForm v v := by
  rw [minusForm_coordinates]
  apply (Finset.sum_pos_iff_of_nonneg (fun i _ => mul_self_nonneg (minusBasis.repr v i))).2
  have hx : ∃ i, minusBasis.repr v i ≠ 0 := by
    by_contra h
    push Not at h
    apply hv
    apply minusBasis.repr.injective
    ext i
    simpa using h i
  obtain ⟨i, hi⟩ := hx
  exact ⟨i, Finset.mem_univ _, mul_self_pos.mpr hi⟩

end Sporadic.Monster.Construction.LocalC
