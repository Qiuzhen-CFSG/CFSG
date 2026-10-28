module
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.Setup
import Mathlib.Tactic.FinCases

/-!
# Two involution representatives on Λ²(F₂⁵)

We calculate with j₁ = 1 + E₁₅ and j₂ = (1 + E₁₃)(1 + E₂₄).
These are genuine determinant-one matrices. Their exterior action is calculated
through the proved minor formula, giving the fixed space in Aschbacher--Smith
12.5.5(1), printed p.819/PDF p.836. Conjugacy exhaustion is a separate result.
-/

@[expose] public section
namespace Representation.SL5ExteriorSquare
open SL5TenDimensional
open scoped BigOperators

/-- The rank-one representative, chosen to fit the source's standard flag. -/
def j₁ : Group := elementary 0 4
/-- A representative with two independent Jordan blocks of size two. -/
def j₂ : Group := elementary 0 2 * elementary 1 3

theorem j₁_sq : j₁ * j₁ = 1 := elementary_square 0 4
theorem j₂_sq : j₂ * j₂ = 1 := by decide
theorem j₁_ne_one : j₁ ≠ 1 := by decide
theorem j₂_ne_one : j₂ ≠ 1 := by decide

private theorem matrix_j₁ : actionMatrix j₁ = ![![1, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl
private theorem matrix_j₂ : actionMatrix j₂ = ![![1, 0, 1, 0, 1, 0, 0, 1, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 1, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Full coordinate formula for the first involution. -/
theorem coordinates_j₁ (v : V) :
    coordinates (exteriorAction 2 j₁ v) =
      ![coordinates v 0 + coordinates v 6, coordinates v 1 + coordinates v 8,
        coordinates v 2 + coordinates v 9, coordinates v 3, coordinates v 4,
        coordinates v 5, coordinates v 6, coordinates v 7, coordinates v 8,
        coordinates v 9] := by
  rw [coordinates_action, matrix_j₁]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- Full coordinate formula for the second involution. -/
theorem coordinates_j₂ (v : V) :
    coordinates (exteriorAction 2 j₂ v) =
      ![coordinates v 0 + coordinates v 2 + coordinates v 4 + coordinates v 7,
        coordinates v 1, coordinates v 2 + coordinates v 7,
        coordinates v 3 + coordinates v 8, coordinates v 4 + coordinates v 7,
        coordinates v 5, coordinates v 6 + coordinates v 9,
        coordinates v 7, coordinates v 8, coordinates v 9] := by
  rw [coordinates_action, matrix_j₂]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, add_assoc]

/-- The displacement operator whose range is the commutator space. -/
noncomputable def displacement (g : Group) : V →ₗ[ZMod 2] V :=
  exteriorAction 2 g - LinearMap.id

/-- The fixed space is the kernel of displacement. -/
noncomputable def fixedSpace (g : Group) : Submodule (ZMod 2) V :=
  LinearMap.ker (displacement g)

@[simp] theorem mem_fixedSpace (g : Group) (v : V) :
    v ∈ fixedSpace g ↔ exteriorAction 2 g v = v := by
  change exteriorAction 2 g v - v = 0 ↔ _
  exact sub_eq_zero

/-- Fixedness under j₁ imposes precisely three coordinate equations. -/
theorem fixed_j₁_iff (v : V) :
    exteriorAction 2 j₁ v = v ↔
      coordinates v 6 = 0 ∧ coordinates v 8 = 0 ∧ coordinates v 9 = 0 := by
  rw [← coordinates.injective.eq_iff, coordinates_j₁]
  simp [funext_iff, Fin.forall_fin_succ]

/-- Fixedness under j₂ imposes four independent coordinate equations. -/
theorem fixed_j₂_iff (v : V) :
    exteriorAction 2 j₂ v = v ↔
      coordinates v 2 = coordinates v 4 ∧ coordinates v 7 = 0 ∧
        coordinates v 8 = 0 ∧ coordinates v 9 = 0 := by
  rw [← coordinates.injective.eq_iff, coordinates_j₂]
  simp only [funext_iff]
  constructor
  · intro h
    have h7 : coordinates v 7 = 0 := by simpa using h 2
    have h8 : coordinates v 8 = 0 := by simpa using h 3
    have h9 : coordinates v 9 = 0 := by simpa using h 6
    refine ⟨?_, h7, h8, h9⟩
    have h0 : coordinates v 2 + coordinates v 4 = 0 := by
      simpa only [Matrix.cons_val_zero, h7, add_zero, add_assoc, add_eq_left] using h 0
    exact (add_eq_zero_iff_eq_neg.mp h0).trans (ZMod.neg_eq_self_mod_two _)
  · rintro ⟨h24, h7, h8, h9⟩ i
    have hzero : coordinates v 4 + coordinates v 4 = 0 := by
      rw [← neg_eq_iff_add_eq_zero]
      exact ZMod.neg_eq_self_mod_two _
    fin_cases i <;> simp [-coordinates_apply, h24, h7, h8, h9, add_assoc, hzero]

/-- Sums of coordinate subspaces are unions of their basis supports. -/
theorem coordinateSpan_union (S T : Finset (Fin 10)) :
    coordinateSpan (S ∪ T) = coordinateSpan S ⊔ coordinateSpan T := by
  simp only [coordinateSpan, Finset.coe_union, Set.image_union, Submodule.span_union]

/-- The literal fixed space in 12.5.5(1), for the chosen standard flag. -/
theorem fixedSpace_j₁ : fixedSpace j₁ = V₄ ⊔ V₆ := by
  change fixedSpace j₁ = coordinateSpan {0, 1, 2, 3} ⊔ coordinateSpan {0, 1, 2, 4, 5, 7}
  rw [← coordinateSpan_union]
  ext v
  rw [mem_fixedSpace, fixed_j₁_iff, mem_coordinateSpan]
  simp [Fin.forall_fin_succ]

/-- The first involution has a seven-dimensional fixed space. -/
theorem finrank_fixedSpace_j₁ : Module.finrank (ZMod 2) (fixedSpace j₁) = 7 := by
  have h : fixedSpace j₁ = coordinateSpan {0, 1, 2, 3, 4, 5, 7} := by
    rw [fixedSpace_j₁]
    change coordinateSpan {0, 1, 2, 3} ⊔ coordinateSpan {0, 1, 2, 4, 5, 7} = _
    rw [← coordinateSpan_union]
    congr 1
    decide
  rw [h]
  exact (finrank_coordinateSpan _).trans (by decide)

/-- Its displacement rank on the exterior square is three. -/
theorem finrank_displacement_j₁ :
    Module.finrank (ZMod 2) (LinearMap.range (displacement j₁)) = 3 := by
  have h := LinearMap.finrank_range_add_finrank_ker (displacement j₁)
  change Module.finrank (ZMod 2) (LinearMap.range (displacement j₁)) +
    Module.finrank (ZMod 2) (fixedSpace j₁) = Module.finrank (ZMod 2) V at h
  rw [finrank_fixedSpace_j₁, finrank_exteriorModule_two] at h
  omega

/-- Six free coordinates parametrizing the fixed space of j₂. -/
noncomputable def fixedSpace_j₂_equiv : fixedSpace j₂ ≃ₗ[ZMod 2] (Fin 6 → ZMod 2) where
  toFun v := ![coordinates v 0, coordinates v 1, coordinates v 2,
    coordinates v 3, coordinates v 5, coordinates v 6]
  invFun w := ⟨coordinates.symm ![w 0, w 1, w 2, w 3, w 2, w 4, w 5, 0, 0, 0], by
    apply (mem_fixedSpace _ _).mpr
    apply (fixed_j₂_iff _).mpr
    simp [-coordinates_apply]⟩
  left_inv v := by
    apply Subtype.ext
    apply coordinates.injective
    rw [LinearEquiv.apply_symm_apply]
    obtain ⟨h24, h7, h8, h9⟩ := (fixed_j₂_iff v).mp ((mem_fixedSpace _ _).mp v.property)
    ext i
    fin_cases i <;> simp [-coordinates_apply, h24, h7, h8, h9]
  right_inv w := by
    ext i
    fin_cases i <;> simp [-coordinates_apply]
  map_add' v w := by
    ext i
    fin_cases i <;> simp [-coordinates_apply]
  map_smul' c v := by
    ext i
    fin_cases i <;> simp [-coordinates_apply]

/-- The second involution has a six-dimensional fixed space. -/
theorem finrank_fixedSpace_j₂ : Module.finrank (ZMod 2) (fixedSpace j₂) = 6 := by
  rw [fixedSpace_j₂_equiv.finrank_eq]
  simp

/-- Its displacement rank on the exterior square is four. -/
theorem finrank_displacement_j₂ :
    Module.finrank (ZMod 2) (LinearMap.range (displacement j₂)) = 4 := by
  have h := LinearMap.finrank_range_add_finrank_ker (displacement j₂)
  change Module.finrank (ZMod 2) (LinearMap.range (displacement j₂)) +
    Module.finrank (ZMod 2) (fixedSpace j₂) = Module.finrank (ZMod 2) V at h
  rw [finrank_fixedSpace_j₂, finrank_exteriorModule_two] at h
  omega

/-- Displacement on the actual five-dimensional natural module. -/
def naturalDisplacement (g : Group) : (Fin 5 → ZMod 2) →ₗ[ZMod 2] (Fin 5 → ZMod 2) :=
  specialLinearNatural 5 g - LinearMap.id

private theorem naturalDisplacement_j₁ (v : Fin 5 → ZMod 2) :
    naturalDisplacement j₁ v = ![v 4, 0, 0, 0, 0] := by
  change j₁.val.mulVec v - v = _
  ext i
  fin_cases i <;> simp [j₁, elementary, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.one_apply]

private theorem naturalDisplacement_j₂ (v : Fin 5 → ZMod 2) :
    naturalDisplacement j₂ v = ![v 2, v 3, 0, 0, 0] := by
  change j₂.val.mulVec v - v = _
  ext i
  fin_cases i <;> simp [j₂, elementary, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.one_apply, Matrix.mul_apply]

/-- The first representative has one-dimensional natural displacement. -/
theorem range_naturalDisplacement_j₁ :
    LinearMap.range (naturalDisplacement j₁) = naturalFlag 1 := by
  apply le_antisymm
  · rintro x ⟨v, rfl⟩
    change ∀ i : Fin 5, 1 ≤ i.val → naturalDisplacement j₁ v i = 0
    rw [naturalDisplacement_j₁]
    intro i hi
    fin_cases i <;> simp_all
  · intro x hx
    change ∀ i : Fin 5, 1 ≤ i.val → x i = 0 at hx
    refine ⟨![0, 0, 0, 0, x 0], ?_⟩
    rw [naturalDisplacement_j₁]
    ext i
    fin_cases i <;> simp [hx 1 (by decide), hx 2 (by decide),
      hx 3 (by decide), hx 4 (by decide)]

/-- The second representative has two-dimensional natural displacement. -/
theorem range_naturalDisplacement_j₂ :
    LinearMap.range (naturalDisplacement j₂) = naturalFlag 2 := by
  apply le_antisymm
  · rintro x ⟨v, rfl⟩
    change ∀ i : Fin 5, 2 ≤ i.val → naturalDisplacement j₂ v i = 0
    rw [naturalDisplacement_j₂]
    intro i hi
    fin_cases i <;> simp_all
  · intro x hx
    change ∀ i : Fin 5, 2 ≤ i.val → x i = 0 at hx
    refine ⟨![0, 0, x 0, x 1, 0], ?_⟩
    rw [naturalDisplacement_j₂]
    ext i
    fin_cases i <;> simp [hx 2 (by decide), hx 3 (by decide), hx 4 (by decide)]

theorem finrank_naturalDisplacement_j₁ :
    Module.finrank (ZMod 2) (LinearMap.range (naturalDisplacement j₁)) = 1 := by
  rw [range_naturalDisplacement_j₁]
  exact finrank_naturalFlag 1 (by decide)

theorem finrank_naturalDisplacement_j₂ :
    Module.finrank (ZMod 2) (LinearMap.range (naturalDisplacement j₂)) = 2 := by
  rw [range_naturalDisplacement_j₂]
  exact finrank_naturalFlag 2 (by decide)

end Representation.SL5ExteriorSquare
