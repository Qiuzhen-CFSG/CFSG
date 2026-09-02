module
import Stellmacher.SectionFiveToSeven.Defs
open scoped Pointwise
namespace Stellmacher.SectionsFiveToSeven
open CosetGraphContext
universe u v
example {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G} (Γ : CosetGraphContext G S P1 P2)
    :
  ∀ d l : Γ.Vertex, l ∈ neighborhood Γ d →
    ∀ T : Sylow 2 ↥(stabilizer Γ d ⊓ stabilizer Γ l),
      IsSylowTwoIn (Subgroup.map (Subgroup.subtype (stabilizer Γ d ⊓ stabilizer Γ l))
        (T : Subgroup (↥(stabilizer Γ d ⊓ stabilizer Γ l)))) (stabilizer Γ d) := by
  sorry
end Stellmacher.SectionsFiveToSeven
