module

public import Theory.AtlasPort.Janko2.Conway.IcosianProjectiveReflections

/-!
# Generation from a root orbit

A subgroup transitive on the actual root points and containing one root
reflection contains all its conjugates, hence every root reflection. The
existing reflection-generation theorem then gives the whole sign quotient.
Since there are exactly 315 root points, 315 distinct translates suffice.

This uses Gerald Höhn's actual icosian root geometry, whose attribution and
license are retained in the imported ATLAS modules. The criterion supplies
the generation clause for the ATLAS `J2G1-P2` pair construction.
-/

public section

namespace Sporadic.LeechRelated.J2.IcosianComparison.Generators
open Atlas.Conway

/-- Transitivity and one reflection force generation of the whole quotient. -/
theorem subgroup_eq_top_of_root_orbit (H : Subgroup IcosianProjectiveModel)
    (p : IcosianRootPoint) (hreflection : icosianProjectiveReflection p ∈ H)
    (horbit : ∀ q : IcosianRootPoint, ∃ g : H, (g : IcosianProjectiveModel) • p = q) :
    H = ⊤ := by
  apply top_unique
  rw [← icosianProjectiveReflection_generation]
  apply (Subgroup.closure_le H).mpr
  rintro _ ⟨q, rfl⟩
  obtain ⟨g, rfl⟩ := horbit q
  rw [← icosianProjectiveReflection_conjugate]
  exact H.mul_mem (H.mul_mem g.property hreflection) (H.inv_mem g.property)

/-- An injective list of 315 translates is an exhaustive root orbit. -/
theorem root_orbit_surjective_of_injective (H : Subgroup IcosianProjectiveModel)
    (p : IcosianRootPoint) (g : Fin 315 → H)
    (hg : Function.Injective (fun i => (g i : IcosianProjectiveModel) • p)) :
    ∀ q : IcosianRootPoint, ∃ h : H, (h : IcosianProjectiveModel) • p = q := by
  have hs := (hg.bijective_of_nat_card_le (by
    rw [icosianRootPoint_card, Nat.card_fin])).surjective
  intro q
  obtain ⟨i, hi⟩ := hs q
  exact ⟨g i, hi⟩

/-- Finite orbit certificates give a concrete generation criterion. -/
theorem subgroup_eq_top_of_315_translates (H : Subgroup IcosianProjectiveModel)
    (p : IcosianRootPoint) (hreflection : icosianProjectiveReflection p ∈ H)
    (g : Fin 315 → H)
    (hg : Function.Injective (fun i => (g i : IcosianProjectiveModel) • p)) :
    H = ⊤ :=
  subgroup_eq_top_of_root_orbit H p hreflection
    (root_orbit_surjective_of_injective H p g hg)

end Sporadic.LeechRelated.J2.IcosianComparison.Generators
