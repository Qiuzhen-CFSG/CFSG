module

public import Stellmacher.Recognition.GTwoSixtyFourPairNormalizerReduction
public import Stellmacher.Recognition.GTwoSixtyFourInitialEightGeometry
public import Stellmacher.Recognition.GTwoSixtyFourInitialEightNormality
public import Stellmacher.Recognition.GTwoSixtyFourInitialEightPlaneAction

/-!
# Assembly of the initial elementary-eight package

The actual neighboring-core intersection is an elementary eight normalized
by the initial vertex, whose conjugation image is a plane stabilizer of order 24.
Containment in the second core and the exact Sylow centralizer are consequences
of the marked sign-and-swap geometry. Together these give the initial-eight
package without additional transport or fusion assumptions.

Source: Stellmacher (8.6)(a), `refs/latex/stellmacher-n-group.tex`.
-/

namespace Stellmacher.Recognition

open Later SectionsFiveToSeven SevenSix

/-- Initial-vertex normality and a plane image complete the initial-eight
package; second-core containment and the exact Sylow centralizer follow
from the marked Sylow rather than being additional inputs. -/
public theorem gTwo_card64_initial_eight_of_vertex_eight
    {G : Type*} [Group G] [Finite G] (data : GTwoTwoDerivedTypeData G)
    (hcard : Nat.card data.sylowIntersection = 64)
    (U : Subgroup G) [IsElementaryAbelian 2 U] (hU : Nat.card U = 8)
    (plane : ElementaryEightPlaneImage U) :
    letI := data.groupK
    letI := data.finiteK
    U ≤ (QAt data.Γ data.criticalPath.a).map data.embedding →
    (GAt data.Γ data.criticalPath.a).map data.embedding ≤
      Subgroup.normalizer (U : Set G) →
    Nonempty (GTwoCard64InitialEight data) := by
  let := data.groupK
  let := data.finiteK
  intro hUQa hPaN
  have hSN : (data.sylowIntersection : Subgroup G) ≤ Subgroup.normalizer (U : Set G) := by
    apply le_trans ?_ hPaN
    rw [← data.intersection_eq]
    exact inf_le_left
  obtain ⟨hUQb, hcent⟩ := gTwo_card64_initial_eight_geometry data hcard U hU hSN hUQa
  exact ⟨⟨U, inferInstance, hU, hUQb, hSN, hcent, plane⟩⟩

/-- The initial vertex supplies an elementary eight in the second core,
normalized and self-centralizing in the supplied Sylow, with an actual
order-24 plane stabilizer image. -/
public theorem gTwo_card64_initial_eight
    {G : Type*} [Group G] [Finite G] (hN : IsNTwoGroup G)
    (hcore : ∀ V : Subgroup G, IsTwoLocal V → pPrimeCore 2 V = ⊥)
    (data : GTwoTwoDerivedTypeData G) (hcard : Nat.card data.sylowIntersection = 64) :
    Nonempty (GTwoCard64InitialEight data) := by
  let := data.groupK
  let := data.finiteK
  obtain ⟨U, hUelem, hU, hUQa, hPaN⟩ := gTwo_card64_initial_eight_exists data hcard
  let := hUelem
  obtain ⟨plane⟩ := gTwo_card64_initial_eight_plane_image hN hcore data hcard U hU hUQa hPaN
  exact gTwo_card64_initial_eight_of_vertex_eight data hcard U hU plane hUQa hPaN

end Stellmacher.Recognition
