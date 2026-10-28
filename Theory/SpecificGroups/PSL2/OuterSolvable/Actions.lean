module

public import Theory.SpecificGroups.PSL2.ElementaryAutomorphisms.FieldAction
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
import Mathlib.Tactic.FinCases

/-!
# Diagonal and field automorphisms of PSL₂

Conjugation by `diag(u,1)` scales the upper and lower off-diagonal entries
by `u` and `u⁻¹`. This gives a homomorphism from the field units to
`Aut(SL₂)`. Both it and entrywise field automorphisms descend through the
characteristic center to the actual matrix quotient PSL₂. Applying a field
automorphism to the diagonal parameter gives the conjugation relation.

These are the concrete A₁ actions in GLS3, Theorem 2.5.12 and §2.7
(`refs/KGroup/GLS3/chapter2.tex`). They are defined in every characteristic;
coverage of arbitrary group automorphisms is a separate assertion.
-/

namespace Theory.PSL2.OuterSolvable
open Matrix
variable {K : Type*} [Field K]

@[expose] public def slDiagonal (u : Kˣ) (A : SpecialLinearGroup (Fin 2) K) :
    SpecialLinearGroup (Fin 2) K :=
  ⟨!![A 0 0, (u : K) * A 0 1; (↑u⁻¹ : K) * A 1 0, A 1 1], by
    have h := A.property
    simp only [det_fin_two] at h ⊢
    simpa [mul_mul_mul_comm] using h⟩

@[simp] public theorem slDiagonal_apply (u : Kˣ) (A : SpecialLinearGroup (Fin 2) K) :
    (slDiagonal u A).val = !![A 0 0, (u : K) * A 0 1; (↑u⁻¹ : K) * A 1 0, A 1 1] := rfl

@[expose] public def slDiagonalAut (u : Kˣ) : MulAut (SpecialLinearGroup (Fin 2) K) where
  toFun := slDiagonal u
  invFun := slDiagonal u⁻¹
  left_inv A := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [slDiagonal]
  right_inv A := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [slDiagonal]
  map_mul' A B := by
    apply Subtype.ext
    change (slDiagonal u (A * B)).val = (slDiagonal u A).val * (slDiagonal u B).val
    dsimp [slDiagonal]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, mul_add,
        mul_assoc, mul_left_comm]

@[expose] public def slDiagonalHom : Kˣ →* MulAut (SpecialLinearGroup (Fin 2) K) where
  toFun := slDiagonalAut
  map_one' := by ext A i j; fin_cases i <;> fin_cases j <;> simp [slDiagonalAut, slDiagonal]
  map_mul' u v := by
    apply MulEquiv.ext
    intro A
    change slDiagonal (u * v) A = slDiagonal u (slDiagonal v A)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [slDiagonal, mul_assoc, mul_comm]

@[expose] public def diagonalAutHom : Kˣ →* MulAut (Group K) :=
  (Subgroup.quotientAut (Subgroup.center (SpecialLinearGroup (Fin 2) K))).comp slDiagonalHom

@[expose] public def slFieldAutHom : (K ≃+* K) →* MulAut (SpecialLinearGroup (Fin 2) K) where
  toFun := sl2FieldAut
  map_one' := by ext A i j; rfl
  map_mul' σ τ := by ext A i j; rfl

@[expose] public def projectiveFieldAutHom : (K ≃+* K) →* MulAut (Group K) :=
  (Subgroup.quotientAut (Subgroup.center (SpecialLinearGroup (Fin 2) K))).comp slFieldAutHom

@[expose] public def fieldUnitsAction : (K ≃+* K) →* MulAut Kˣ where
  toFun σ := Units.mapEquiv σ.toMulEquiv
  map_one' := by ext; rfl
  map_mul' σ τ := by ext; rfl

public theorem slDiagonal_field_covariance (σ : K ≃+* K) (u : Kˣ) :
    slDiagonalHom (fieldUnitsAction σ u) =
      slFieldAutHom σ * slDiagonalHom u * (slFieldAutHom σ)⁻¹ := by
  ext A i j
  fin_cases i <;> fin_cases j
  · change A 0 0 = σ (σ.symm (A 0 0))
    simp
  · change σ (↑u) * A 0 1 = σ ((↑u) * σ.symm (A 0 1))
    simp
  · change σ (↑u⁻¹) * A 1 0 = σ ((↑u⁻¹) * σ.symm (A 1 0))
    simp
  · change A 1 1 = σ (σ.symm (A 1 1))
    simp
/-- Diagonal conjugation on the central quotient is given by its matrix formula. -/
public theorem diagonalAutHom_apply_quotientMap (u : Kˣ)
    (A : SpecialLinearGroup (Fin 2) K) :
    diagonalAutHom u (quotientMap K A) = quotientMap K (slDiagonal u A) :=
  Subgroup.quotientAut_apply_mk _ _ _

/-- Entrywise field application descends to the central quotient in every characteristic. -/
public theorem projectiveFieldAutHom_apply_quotientMap (σ : K ≃+* K)
    (A : SpecialLinearGroup (Fin 2) K) :
    projectiveFieldAutHom σ (quotientMap K A) = quotientMap K (sl2FieldAut σ A) :=
  Subgroup.quotientAut_apply_mk _ _ _

/-- The general quotient construction agrees with the established binary field action. -/
public theorem projectiveFieldAutHom_eq_fieldAut [CharP K 2] (σ : K ≃+* K) :
    projectiveFieldAutHom σ = fieldAut σ := by
  ext x
  obtain ⟨A, rfl⟩ := quotientMap_surjective K x
  rw [projectiveFieldAutHom_apply_quotientMap, fieldAut_apply_quotientMap]
  rfl

/-- Field automorphisms normalize diagonal automorphisms on the actual quotient. -/
public theorem diagonal_field_covariance (σ : K ≃+* K) (u : Kˣ) :
    diagonalAutHom (fieldUnitsAction σ u) =
      projectiveFieldAutHom σ * diagonalAutHom u * (projectiveFieldAutHom σ)⁻¹ := by
  have h := congrArg
    (Subgroup.quotientAut (Subgroup.center (SpecialLinearGroup (Fin 2) K)))
    (slDiagonal_field_covariance σ u)
  simpa only [map_mul, map_inv, diagonalAutHom, projectiveFieldAutHom,
    MonoidHom.comp_apply] using h

end Theory.PSL2.OuterSolvable
