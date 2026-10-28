module

public import Stellmacher.Recognition.GTwoSixtyFourInitialCoreActions
public import Stellmacher.Recognition.GTwoSixtyFourNextCoreActions

/-!
# Ambient actions on the order-64 vertex cores

This is the assembly boundary for normalizer control of the two vertex cores
in Stellmacher (8.6)(a). The initial-core result identifies its intersection
with the transfer subgroup as its characteristic C₄ × C₄ base.
The second-core reduction controls its vertex and centralizer. The theorem
below assembles both cases conditional on the remaining ambient normalizer
containment; it does not assert that containment from the global hypotheses.

Source: `refs/latex/stellmacher-n-group.tex`, (8.6)(a).
-/

namespace Stellmacher.Recognition

open Later SectionsFiveToSeven SevenSix

/-- Both vertex-core cases reduce to the second core's ambient normalizer
containment. This is a conditional assembly, with the unfinished global
inference kept as an explicit hypothesis. -/
public theorem gTwo_card64_core_normalizer_preserves_transfer_of_next_normalizer_le
    {G : Type*} [Group G] [Finite G] (data : GTwoTwoDerivedTypeData G)
    (hcard : Nat.card data.sylowIntersection = 64) :
    letI := data.groupK
    letI := data.finiteK
    let Qb := (QAt data.Γ data.criticalPath.firstStep).map data.embedding
    Subgroup.normalizer (Qb : Set G) ≤
      (GAt data.Γ data.criticalPath.firstStep).map data.embedding ⊔
        Subgroup.centralizer (Qb : Set G) →
    ∀ X : Subgroup G,
      (X = (QAt data.Γ data.criticalPath.a).map data.embedding ∨ X = Qb) →
      ∀ g ∈ Subgroup.normalizer (X : Set G), ∀ x y : data.sylowIntersection,
        (x : G) ∈ X → g⁻¹ * (x : G) * g = (y : G) →
        (x ∈ gTwoCard64TransferSubgroup data ↔ y ∈ gTwoCard64TransferSubgroup data) := by
  let := data.groupK
  let := data.finiteK
  dsimp only
  intro hnext X hX
  rcases hX with rfl | rfl
  · exact gTwo_card64_initial_core_normalizer_preserves_transfer data hcard
  · exact gTwo_card64_next_core_preserves_transfer_of_normalizer_le data hcard hnext

end Stellmacher.Recognition
