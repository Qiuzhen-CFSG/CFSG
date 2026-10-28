module

public import Theory.Character.ClassFunction
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.BigOperators.Field

/-!
# The mass of a character on a two-section

For a two-element u, the mass of its section is the average, over C(u), of
the squared absolute values at uv with v of odd order. Counting conjugacy
fibers identifies this with the ambient normalized squared norm on that
section. The definition below is the actual local sum; it does not postulate
generalized decomposition numbers or quadratic-form witnesses.

Source: the section form of ordinary row orthogonality, as used in Fong
(1967), pp. 73–74, in the method of contributions.
-/

public section
noncomputable section
open scoped BigOperators
namespace Theory.Character
attribute [local instance] Fintype.ofFinite
variable {G : Type*} [Group G] [Finite G]

/-- The local normalized squared norm on the two-section based at u.
For a Sylow two-subgroup of order 32, Fong's contribution is 32 times this
quantity. -/
@[expose] def twoSectionMass (χ : ClassFunction G) (u : G) : ℝ :=
  (Nat.card (Subgroup.centralizer ({u} : Set G)) : ℝ)⁻¹ *
    ∑ v : Subgroup.centralizer ({u} : Set G),
      if Odd (orderOf v) then Complex.normSq (χ (u * (v : G))) else 0

/-- Every actual section mass is nonnegative. -/
theorem twoSectionMass_nonneg (χ : ClassFunction G) (u : G) :
    0 ≤ twoSectionMass χ u := by
  classical
  apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
  apply Finset.sum_nonneg
  intro v _
  split_ifs
  · exact Complex.normSq_nonneg _
  · exact le_rfl

/-- A nonzero degree gives strictly positive identity-section mass. -/
theorem twoSectionMass_one_pos (χ : ClassFunction G) (hχ : χ 1 ≠ 0) :
    0 < twoSectionMass χ 1 := by
  classical
  let : Fintype (Subgroup.centralizer ({(1 : G)} : Set G)) := Fintype.ofFinite _
  apply mul_pos (inv_pos.mpr (by exact_mod_cast
    (Nat.card_pos (α := Subgroup.centralizer ({(1 : G)} : Set G)))))
  apply lt_of_lt_of_le (show 0 < Complex.normSq (χ 1) from
    Complex.normSq_pos.mpr hχ)
  have h := Finset.single_le_sum
    (f := fun v : Subgroup.centralizer ({(1 : G)} : Set G) =>
      if Odd (orderOf v) then Complex.normSq (χ (1 * (v : G))) else 0)
    (fun v _ => by split_ifs; exact Complex.normSq_nonneg _; exact le_rfl)
    (Finset.mem_univ (1 : Subgroup.centralizer ({(1 : G)} : Set G)))
  simpa using h

end Theory.Character
