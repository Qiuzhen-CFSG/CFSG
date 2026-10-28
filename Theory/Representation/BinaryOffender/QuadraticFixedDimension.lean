module
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.Representation.BinaryOffender.RestrictionComparison

/-!
# A fixed-dimension criterion for quadratic binary actions

The fixed space of a subgroup lies in every element fixed space. If the common
fixed dimension reaches a uniform upper bound for the nonidentity element
fixed dimensions, these spaces coincide. An involution fixes its own
displacements in characteristic two, so all displacements are fixed by the
whole subgroup.

Application: the characteristic-two case of Niles, *Pushing-up in finite
groups* (1979), Lemma 3.4, printed pp.37–39, where the upper bound comes
from a natural submodule and natural quotient.
-/

public section
namespace Representation.BinaryOffender
open Subgroup
variable {G Y : Type*} [Group G] [AddCommGroup Y] [Module (ZMod 2) Y]
  [FiniteDimensional (ZMod 2) Y]

/-- An elementary two-actor is quadratic if its common fixed dimension reaches
an upper bound for the fixed dimension of each nonidentity element. -/
theorem isQuadratic_of_fixedDimension_bound (ρ : Representation (ZMod 2) G Y)
    (A : Subgroup G) (hsq : ∀ a ∈ A, a ^ 2 = 1) (d : ℕ)
    (hbound : ∀ a ∈ A, a ≠ 1 → Module.finrank (ZMod 2) (fixedSpace ρ (zpowers a)) ≤ d)
    (hfixed : d ≤ Module.finrank (ZMod 2) (fixedSpace ρ A)) : IsQuadratic ρ A := by
  intro a ha b hb v
  by_cases hb1 : b = 1
  · simp [hb1]
  have hle := fixedSpace_antitone ρ (zpowers_le.mpr hb)
  have he : fixedSpace ρ A = fixedSpace ρ (zpowers b) :=
    Submodule.eq_of_le_of_finrank_eq hle (by
      have := Submodule.finrank_mono hle
      have := hbound b hb hb1
      omega)
  have hneg (w : Y) : -w = w := by
    have hw : w + w = 0 := by
      simpa only [add_smul, one_smul, zero_smul] using
        congrArg (fun c : ZMod 2 => c • w) (by decide : (1 : ZMod 2) + 1 = 0)
    exact neg_eq_of_add_eq_zero_left hw
  have hbb : ρ b (ρ b v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, ← pow_two, hsq b hb, map_one,
      Module.End.one_apply]
  have hv : ρ b v - v ∈ fixedSpace ρ (zpowers b) := by
    rw [mem_fixedSpace_zpowers_iff, map_sub, hbb]
    simp only [sub_eq_add_neg, hneg, add_comm]
  rw [← he] at hv
  exact hv ⟨a, ha⟩
end Representation.BinaryOffender
