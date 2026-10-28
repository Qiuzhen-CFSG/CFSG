module

public import Stellmacher.Recognition.GTwoSixtyFourInitialEight
public import Theory.GroupTheory.QuaternionCentralProductEightPoint

/-!
# Pair normalizer rigidity in the order-64 branch

The initial vertex supplies an actual elementary eight with a full plane
stabilizer in its automizer. If the second core's ambient normalizer had
order 576, its independent cubic actors would supply a full point stabilizer
on the same eight. These two images make its two-local normalizer nonsolvable,
contrary to the N₂ hypothesis. The normalizer order dichotomy then identifies
the second core's ambient normalizer with the second vertex.

Source: Stellmacher (8.6)(a), `refs/latex/stellmacher-n-group.tex`.
-/

namespace Stellmacher.Recognition

open Later SectionsFiveToSeven SevenSix

/-- The actions of the initial vertex and the second-core normalizer on the
same elementary eight exclude the order-576 enlargement. -/
public theorem gTwo_card64_next_normalizer_ne_576
    {G : Type*} [Group G] [Finite G] (hN : IsNTwoGroup G)
    (hcore : ∀ V : Subgroup G, IsTwoLocal V → pPrimeCore 2 V = ⊥)
    (data : GTwoTwoDerivedTypeData G) (hcard : Nat.card data.sylowIntersection = 64) :
    letI := data.groupK
    letI := data.finiteK
    let Qb := (QAt data.Γ data.criticalPath.firstStep).map data.embedding
    Nat.card (Subgroup.normalizer (Qb : Set G)) ≠ 576 := by
  let := data.groupK
  let := data.finiteK
  apply gTwo_card64_next_normalizer_ne_576_of_eight_transport hN hcore data hcard
    (gTwo_card64_initial_eight hN hcore data hcard)
  intro B C hB hC hinter hcomm hQ actors eight
  let := eight.elementary
  have hUQ : eight.U ≤ B ⊔ C := hQ ▸ eight.le_next_core
  have hQS : B ⊔ C ≤ (data.sylowIntersection : Subgroup G) :=
    hQ ▸ (gTwo_card64_cores_le_sylow data).2
  exact actors.point_image eight.U (data.sylowIntersection : Subgroup G)
    hB hC hinter hcomm eight.card hUQ hcard hQS
    eight.sylow_normalizes eight.sylow_centralizer

/-- The second vertex is the full ambient normalizer of its two-core. -/
public theorem gTwo_card64_next_normalizer_eq_vertex
    {G : Type*} [Group G] [Finite G] (hN : IsNTwoGroup G)
    (hcore : ∀ V : Subgroup G, IsTwoLocal V → pPrimeCore 2 V = ⊥)
    (data : GTwoTwoDerivedTypeData G) (hcard : Nat.card data.sylowIntersection = 64) :
    letI := data.groupK
    letI := data.finiteK
    let Qb := (QAt data.Γ data.criticalPath.firstStep).map data.embedding
    Subgroup.normalizer (Qb : Set G) =
      (GAt data.Γ data.criticalPath.firstStep).map data.embedding := by
  let := data.groupK
  let := data.finiteK
  apply gTwo_card64_next_normalizer_eq_vertex_of_card192 data hcard
  exact (gTwo_card64_next_normalizer_order_dichotomy hN hcore data hcard).resolve_right
    (gTwo_card64_next_normalizer_ne_576 hN hcore data hcard)

/-- The ambient second-core normalizer satisfies the containment needed by
the transfer argument. -/
public theorem gTwo_card64_next_normalizer_le
    {G : Type*} [Group G] [Finite G] (hN : IsNTwoGroup G)
    (hcore : ∀ V : Subgroup G, IsTwoLocal V → pPrimeCore 2 V = ⊥)
    (data : GTwoTwoDerivedTypeData G) (hcard : Nat.card data.sylowIntersection = 64) :
    letI := data.groupK
    letI := data.finiteK
    let Qb := (QAt data.Γ data.criticalPath.firstStep).map data.embedding
    Subgroup.normalizer (Qb : Set G) ≤
      (GAt data.Γ data.criticalPath.firstStep).map data.embedding ⊔
        Subgroup.centralizer (Qb : Set G) := by
  let := data.groupK
  let := data.finiteK
  dsimp only
  rw [gTwo_card64_next_normalizer_eq_vertex hN hcore data hcard]
  exact le_sup_left

end Stellmacher.Recognition
