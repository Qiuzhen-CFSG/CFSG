module

public import Theory.SpecificGroups.FFG2DerivedCenter
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.Semilinear

/-!
# Centers of the derived even G₂ models

Above field order two, perfectness and the proved center calculation for
the full octonion model give a trivial center. At field order two,
coefficient transport identifies the actual commutator with G₂(2)′, whose
center was calculated using its marked Sylow subgroup and a moving root
actor. No binary simplicity assumption is needed.

Source application: Aschbacher–Smith 2.3.9(7), printed p.526. This reuses
the licensed ATLAS octonion model; see LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff.
-/

public section

open Subgroup

private theorem center_trivial_transport {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) (hY : center Y = ⊥) : center X = ⊥ := by
  apply bot_unique
  intro x hx
  have hy : e x ∈ center Y := (centerCongr e ⟨x, hx⟩).property
  rw [hY, mem_bot] at hy
  exact e.injective (hy.trans (map_one e).symm)

/-- The actual derived split G₂ model is centerless at every finite even field,
including field order two. -/
theorem Theory.SpecificGroups.g2_derived_even_center_eq_bot {F : Type*} [Field F] [Finite F] [CharP F 2] :
    center (commutator (Atlas.G2.Model F)) = ⊥ := by
  by_cases hq : Nat.card F = 2
  · let e := Atlas.G2.fieldEquiv (Atlas.G2.binaryFieldEquiv hq)
    have he : (commutator (Atlas.G2.Model F)).map e.toMonoidHom =
        commutator (Atlas.G2.Model (ZMod 2)) := by
      rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
      rfl
    exact center_trivial_transport
      ((e.subgroupMap _).trans (MulEquiv.subgroupCongr he))
      Theory.SpecificGroups.g2_derived_two_center_eq_bot
  · have hgt : 2 < Nat.card F := by
      have := Finite.one_lt_card (α := F)
      omega
    let := Atlas.G2.isPerfect hgt
    exact center_trivial_transport
      ((MulEquiv.subgroupCongr (Group.IsPerfect.commutator_eq_top (G := Atlas.G2.Model F))).trans
        topEquiv)
      (Atlas.G2.LieAutomorphismExtensions.model_center_eq_bot hgt)


end
