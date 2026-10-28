module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.IcosianComparison.Generators.Relations
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.IcosianComparison.Generators.GenerationCriterion
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.IcosianComparison.Generators.Orbit

/-!
# A generating ATLAS pair in the projective icosian group

The fixed lattice pair satisfies all five ATLAS `J2G1-P2` relations and
generates the full Hermitian lattice group modulo its two central signs.
The certified sixth commutator power supplies one reflection, and 315 distinct
translates of its genuine root point force all reflections into the pair
subgroup. The existing reflection-generation theorem completes the proof.

The independent permutation presentation-exactness input is not used here.
`Generators.Application` connects this pair to the actual comparison
consumer without creating an import cycle. Source: ATLAS `J2G1-P2` and
Gerald Höhn's icosian construction; the imported roots retain its license.
-/

public section
namespace Sporadic.LeechRelated.J2.IcosianComparison.Generators
open Atlas.Conway
open G2FourModule.Embedding.InnerRealization

/-- An unconditional generating pair satisfying all five literal ATLAS relators. -/
theorem exists_generatingPair :
    ∃ x y : IcosianProjectiveModel, Presentation.Relations x y ∧
      Subgroup.closure ({x, y} : Set IcosianProjectiveModel) = ⊤ :=
  ⟨x, y, relations, closure_pair_eq_top⟩

/-- The fixed pair needs only a reflection and a root-orbit certificate. -/
theorem exists_generatingPair_of_root_orbit (p : IcosianRootPoint)
    (hr : icosianProjectiveReflection p ∈
      Subgroup.closure ({x, y} : Set IcosianProjectiveModel))
    (ho : ∀ q : IcosianRootPoint,
      ∃ g : Subgroup.closure ({x, y} : Set IcosianProjectiveModel),
        (g : IcosianProjectiveModel) • p = q) :
    ∃ a b : IcosianProjectiveModel, Presentation.Relations a b ∧
      Subgroup.closure ({a, b} : Set IcosianProjectiveModel) = ⊤ :=
  ⟨x, y, relations, subgroup_eq_top_of_root_orbit _ p hr ho⟩

/-- An injective table of 315 translates suffices for the requested pair. -/
theorem exists_generatingPair_of_315_translates (p : IcosianRootPoint)
    (hr : icosianProjectiveReflection p ∈
      Subgroup.closure ({x, y} : Set IcosianProjectiveModel))
    (g : Fin 315 → Subgroup.closure ({x, y} : Set IcosianProjectiveModel))
    (hg : Function.Injective (fun i => (g i : IcosianProjectiveModel) • p)) :
    ∃ a b : IcosianProjectiveModel, Presentation.Relations a b ∧
      Subgroup.closure ({a, b} : Set IcosianProjectiveModel) = ⊤ :=
  ⟨x, y, relations, subgroup_eq_top_of_315_translates _ p hr g hg⟩

end Sporadic.LeechRelated.J2.IcosianComparison.Generators
