module
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.Involutions
public import Theory.Representation.BinaryOffender.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Last-column shears in the binary exterior-square representation

The additive parameter space is identified with the actual matrix subgroup U.
The exterior displacement is the wedge of the quotient coordinate with the
shear parameter. These are the intrinsic calculations behind Aschbacher--Smith
12.5.7 and 12.5.10, printed pp.820--821 (PDF pp.837--838).
-/

@[expose] public section
namespace Representation.SL5ExteriorSquare
open SL5TenDimensional
open scoped BigOperators

abbrev ShearParameter := Fin 4 → ZMod 2

theorem matrix_shear (u : ShearParameter) : (shear u).val =
    ![![1,0,0,0,u 0], ![0,1,0,0,u 1], ![0,0,1,0,u 2],
      ![0,0,0,1,u 3], ![0,0,0,0,1]] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [shear, List.ofFn_succ, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

@[simp] theorem shear_zero : shear 0 = 1 := by
  apply Subtype.ext
  rw [matrix_shear]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

@[simp] theorem shear_add (u w : ShearParameter) : shear (u + w) = shear u * shear w := by
  apply Subtype.ext
  ext i j
  change (shear (u + w)).val i j = ∑ k, (shear u).val i k * (shear w).val k j
  simp only [matrix_shear]
  fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_succ, add_comm]

theorem shear_injective : Function.Injective shear := by
  intro u w h
  have hm := congrArg Subtype.val h
  rw [matrix_shear, matrix_shear] at hm
  funext i
  fin_cases i
  · exact congrArg (fun m => m 0 4) hm
  · exact congrArg (fun m => m 1 4) hm
  · exact congrArg (fun m => m 2 4) hm
  · exact congrArg (fun m => m 3 4) hm

@[simp] theorem shear_eq_one_iff (u : ShearParameter) : shear u = 1 ↔ u = 0 := by
  rw [← shear_zero, shear_injective.eq_iff]

/-- The parameter map into the actual ambient matrix group. -/
def shearHom : Multiplicative ShearParameter →* Group where
  toFun u := shear u.toAdd
  map_one' := shear_zero
  map_mul' u w := shear_add u.toAdd w.toAdd

theorem shearHom_range : shearHom.range = shearSubgroup := by
  apply le_antisymm
  · rintro g ⟨u, rfl⟩
    exact shear_mem u.toAdd
  · apply (Subgroup.closure_le _).mpr
    rintro g ⟨u, rfl⟩
    exact ⟨Multiplicative.ofAdd u, rfl⟩

@[simp] theorem mem_shearSubgroup (g : Group) :
    g ∈ shearSubgroup ↔ ∃ u, shear u = g := by
  rw [← shearHom_range]
  rfl

/-- The parameter map corestricted to U. -/
def shearToSubgroup : Multiplicative ShearParameter →* shearSubgroup where
  toFun u := ⟨shear u.toAdd, shear_mem _⟩
  map_one' := Subtype.ext shear_zero
  map_mul' u w := Subtype.ext (shear_add u.toAdd w.toAdd)

/-- The elementary-abelian parameterization, with its literal matrices. -/
noncomputable def shearEquiv : Multiplicative ShearParameter ≃* shearSubgroup :=
  MulEquiv.ofBijective shearToSubgroup ⟨by
    intro u w h
    change u.toAdd = w.toAdd
    have he := congrArg (fun g : shearSubgroup => (g : Group)) h
    change shear u.toAdd = shear w.toAdd at he
    exact shear_injective he, by
    intro g
    obtain ⟨u, hu⟩ := (mem_shearSubgroup g).mp g.property
    refine ⟨Multiplicative.ofAdd u, ?_⟩
    apply Subtype.ext
    change shear u = g.val
    exact hu⟩

@[simp] theorem shearEquiv_apply (u : Multiplicative ShearParameter) :
    (shearEquiv u : Group) = shear u.toAdd := rfl

theorem shear_square (u : ShearParameter) : shear u * shear u = 1 := by
  rw [← shear_add]
  have h : u + u = 0 := by
    ext i
    exact (neg_eq_iff_add_eq_zero.mp (ZMod.neg_eq_self_mod_two (u i)))
  rw [h, shear_zero]

instance shearSubgroup_elementary : IsElementaryAbelian 2 shearSubgroup where
  toIsMulCommutative := ⟨⟨by
    intro g h
    obtain ⟨u, rfl⟩ := shearEquiv.surjective g
    obtain ⟨w, rfl⟩ := shearEquiv.surjective h
    rw [← map_mul, ← map_mul, mul_comm]⟩⟩
  exponent_dvd_p := by
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro g
    obtain ⟨u, rfl⟩ := shearEquiv.surjective g
    apply Subtype.ext
    exact (pow_two _).trans (shear_square u.toAdd)

theorem card_shearSubgroup : Nat.card shearSubgroup = 16 := by
  rw [← Nat.card_congr shearEquiv.toEquiv]
  change Nat.card ShearParameter = 16
  simp [Nat.card_eq_fintype_card]

/-- Coordinates on the natural quotient V / Λ²Γ₄. -/
noncomputable def shearQuotient : V →ₗ[ZMod 2] ShearParameter where
  toFun v := ![coordinates v 3, coordinates v 6, coordinates v 8, coordinates v 9]
  map_add' v w := by ext i; fin_cases i <;> simp [-coordinates_apply]
  map_smul' c v := by ext i; fin_cases i <;> simp [-coordinates_apply]

/-- The chosen complement Γ₄ ∧ e₅ of Λ²Γ₄. -/
noncomputable def shearSection : ShearParameter →ₗ[ZMod 2] V where
  toFun w := coordinates.symm ![0,0,0,w 0,0,0,w 1,0,w 2,w 3]
  map_add' v w := by
    apply coordinates.injective
    ext i
    fin_cases i <;> simp [-coordinates_apply]
  map_smul' c v := by
    apply coordinates.injective
    ext i
    fin_cases i <;> simp [-coordinates_apply]

@[simp] theorem shearQuotient_section (w : ShearParameter) :
    shearQuotient (shearSection w) = w := by
  ext i
  fin_cases i <;> simp [shearQuotient, shearSection, -coordinates_apply]

theorem mem_V₆_iff_shearQuotient (v : V) : v ∈ V₆ ↔ shearQuotient v = 0 := by
  rw [V₆, mem_coordinateSpan]
  simp [shearQuotient, funext_iff, Fin.forall_fin_succ, -coordinates_apply]

theorem ker_shearQuotient : LinearMap.ker shearQuotient = V₆ := by
  ext v
  exact (mem_V₆_iff_shearQuotient v).symm

/-- Wedge of two vectors in Γ₄, written in the actual exterior square. -/
noncomputable def shearWedge (w u : ShearParameter) : V :=
  coordinates.symm ![w 0 * u 1 + w 1 * u 0, w 0 * u 2 + w 2 * u 0,
    w 0 * u 3 + w 3 * u 0, 0, w 1 * u 2 + w 2 * u 1,
    w 1 * u 3 + w 3 * u 1, 0, w 2 * u 3 + w 3 * u 2, 0, 0]

/-- Actual exterior action, relative to Λ²Γ₄ ⊕ (Γ₄ ∧ e₅). -/
theorem shear_action (u : ShearParameter) (v : V) :
    exteriorAction 2 (shear u) v = v + shearWedge (shearQuotient v) u := by
  apply coordinates.injective
  rw [coordinates_action, map_add]
  ext i
  fin_cases i <;>
    simp [actionMatrix, matrix_shear, pair, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, shearWedge, shearQuotient, sub_eq_add_neg,
      ZMod.neg_eq_self_mod_two, -coordinates_apply] <;> ring

theorem shear_displacement (u : ShearParameter) (v : V) :
    displacement (shear u) v = shearWedge (shearQuotient v) u := by
  change exteriorAction 2 (shear u) v - v = _
  rw [shear_action, add_sub_cancel_left]

end Representation.SL5ExteriorSquare
