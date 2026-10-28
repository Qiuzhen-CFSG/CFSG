module
public import Theory.Representation.SL5ExteriorSquare.TwoGeneratorRecognition.Image
public import Mathlib.Data.Set.Card

/-!
# Sizes of the two generated nonzero exterior orbits

The nondecomposable stabilizer already has index 868. Orbit–stabilizer gives
its orbit size; exhaustion and the existing total of 1024 vectors give 155
for the decomposable orbit. These counts apply to the two specified generators
via their proved exterior-image generation, without another orbit enumeration.
Source: Aschbacher–Smith, 12.5.5, printed p.819.
-/

public noncomputable section
namespace Representation.SL5ExteriorSquare.TwoGeneratorRecognition
open SL5TenDimensional

/-- The existing stabilizer calculation gives the full nondecomposable orbit size. -/
theorem card_nondecomposable_orbit :
    Nat.card {v : V // InExteriorOrbit nondecomposable v} = 868 := by
  let _ : MulAction Group V := {
    smul g v := exteriorAction 2 g v
    one_smul v := by change exteriorAction 2 1 v = v; rw [map_one]; rfl
    mul_smul g h v := by
      change exteriorAction 2 (g*h) v = exteriorAction 2 g (exteriorAction 2 h v)
      rw [map_mul]; rfl }
  change Nat.card (MulAction.orbit Group nondecomposable) = 868
  rw [Nat.card_congr (MulAction.orbitEquivQuotientStabilizer Group nondecomposable)]
  exact index_nondecomposableStabilizer

/-- The other nonzero orbit has size 155, by exhaustion and the 1024-vector count. -/
theorem card_decomposable_orbit :
    Nat.card {v : V // InExteriorOrbit decomposable v} = 155 := by
  classical
  let : Finite V := Finite.of_injective coordinates coordinates.injective
  let D : Set V := {v | InExteriorOrbit decomposable v}
  let U : Set V := {v | InExteriorOrbit nondecomposable v}
  have hD0 : (0 : V) ∉ D := fun h => decomposable_ne_zero (h.eq_zero_iff.mpr rfl)
  have hU0 : (0 : V) ∉ U := fun h => nondecomposable_ne_zero (h.eq_zero_iff.mpr rfl)
  have hcompl : Uᶜ = insert 0 D := by
    ext v
    constructor
    · intro h
      by_cases hv : v = 0
      · exact Or.inl hv
      · exact Or.inr ((exterior_orbits_exhaustive v hv).resolve_right h)
    · rintro (rfl | h)
      · exact hU0
      · exact fun hu => exterior_orbits_disjoint v ⟨h,hu⟩
  have h := Set.ncard_add_ncard_compl U
  rw [hcompl,Set.ncard_insert_of_notMem hD0,card_exteriorSquare] at h
  change Nat.card {v : V // InExteriorOrbit nondecomposable v} +
    (Nat.card {v : V // InExteriorOrbit decomposable v} + 1) = 1024 at h
  rw [card_nondecomposable_orbit] at h
  omega

/-- The two-generator action has the same complete nonzero orbit sizes. -/
theorem generated_orbit_cardinalities :
    Nat.card {v : V // ∃ a ∈ Subgroup.closure
      ({exteriorHom A0,exteriorHom A1} : Set (V ≃ₗ[ZMod 2] V)), a decomposable = v} = 155 ∧
    Nat.card {v : V // ∃ a ∈ Subgroup.closure
      ({exteriorHom A0,exteriorHom A1} : Set (V ≃ₗ[ZMod 2] V)), a nondecomposable = v} = 868 := by
  simp only [generated_orbit_iff]
  exact ⟨card_decomposable_orbit,card_nondecomposable_orbit⟩

end Representation.SL5ExteriorSquare.TwoGeneratorRecognition
