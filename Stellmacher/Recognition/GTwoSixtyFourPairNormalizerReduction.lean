module

public import Stellmacher.Recognition.GTwoSixtyFourNextNormalizerOrders
public import Theory.GroupTheory.QuaternionCentralProductIndependentCubics
public import Theory.GroupTheory.ElementaryEightPlanePoint

/-!
# Elementary-eight reduction for rigidity of the second normalizer

The order-576 alternative supplies independent cubic actors on the actual
embedded quaternion factors. To contradict the N₂ hypothesis, it suffices
to find an elementary eight on which the initial vertex supplies a full
plane stabilizer and the second normalizer supplies a full point stabilizer.
The resulting normalizer is nonsolvable by the plane/point image theorem.

This module currently supplies the embedded actors, the exact initial-eight
interface, and the ambient contradiction from the two actions. Construction
of the initial eight and transport of the cubic actors to its point
stabilizer remain separate mathematical steps; no unconditional exclusion
of order 576 is asserted here.

Source: the actual pair in Stellmacher (8.6)(a),
`refs/latex/stellmacher-n-group.tex`.
-/

namespace Stellmacher.Recognition

open Later SectionsFiveToSeven SevenSix

/-- The initial vertex's elementary eight, retaining the embedding needed
to apply the second-core action to the very same subgroup. -/
public structure GTwoCard64InitialEight
    {G : Type*} [Group G] [Finite G] (data : GTwoTwoDerivedTypeData G) where
  U : Subgroup G
  elementary : IsElementaryAbelian 2 U
  card : Nat.card U = 8
  le_next_core :
    letI := data.groupK
    letI := data.finiteK
    U ≤ (QAt data.Γ data.criticalPath.firstStep).map data.embedding
  sylow_normalizes : (data.sylowIntersection : Subgroup G) ≤
    Subgroup.normalizer (U : Set G)
  sylow_centralizer : (data.sylowIntersection : Subgroup G) ⊓
    Subgroup.centralizer (U : Set G) = U
  plane : ElementaryEightPlaneImage U

/-- Independent cubic actors live on the actual embedded second core,
with both quaternion factors and their embedding equality retained. -/
public theorem gTwo_card64_next_independent_cubics_of_card576
    {G : Type*} [Group G] [Finite G] (hN : IsNTwoGroup G)
    (hcore : ∀ V : Subgroup G, IsTwoLocal V → pPrimeCore 2 V = ⊥)
    (data : GTwoTwoDerivedTypeData G) (hcard : Nat.card data.sylowIntersection = 64) :
    letI := data.groupK
    letI := data.finiteK
    let Qb := (QAt data.Γ data.criticalPath.firstStep).map data.embedding
    Nat.card (Subgroup.normalizer (Qb : Set G)) = 576 →
    ∃ B C : Subgroup G,
      Nonempty (B ≃* QuaternionGroup 2) ∧ Nonempty (C ≃* QuaternionGroup 2) ∧
      Nat.card (B ⊓ C : Subgroup G) = 2 ∧
      (∀ b ∈ B, ∀ c ∈ C, b * c = c * b) ∧ Qb = B ⊔ C ∧
      Nonempty (Subgroup.QuaternionIndependentCubics B C) := by
  let := data.groupK
  let := data.finiteK
  let Qb := (QAt data.Γ data.criticalPath.firstStep).map data.embedding
  dsimp only
  intro h576
  obtain ⟨_, _, _, _, B0, C0, ⟨eB⟩, ⟨eC⟩, hQeq, hinter, hcomm, _⟩ :=
    gTwo_card64_vertex_structure data hcard
  let B := B0.map data.embedding
  let C := C0.map data.embedding
  have hB : Nonempty (B ≃* QuaternionGroup 2) :=
    ⟨(B0.equivMapOfInjective data.embedding data.embedding_injective).symm.trans eB⟩
  have hC : Nonempty (C ≃* QuaternionGroup 2) :=
    ⟨(C0.equivMapOfInjective data.embedding data.embedding_injective).symm.trans eC⟩
  have hBC : Nat.card (B ⊓ C : Subgroup G) = 2 := by
    rw [← Subgroup.map_inf B0 C0 data.embedding data.embedding_injective,
      Subgroup.card_map_of_injective data.embedding_injective, hinter]
  have hcomm' : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b := by
    rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩
    rw [← map_mul, ← map_mul, hcomm b hb c hc]
  have hQ : Qb = B ⊔ C := by
    dsimp [Qb, B, C]
    rw [hQeq, Subgroup.map_sup]
  have hcentral := gTwo_card64_next_core_centralizer_le hN hcore data hcard
  change Subgroup.centralizer (Qb : Set G) ≤ Qb at hcentral
  change Nat.card (Subgroup.normalizer (Qb : Set G)) = 576 at h576
  rw [hQ] at hcentral h576
  exact ⟨B, C, hB, hC, hBC, hcomm', hQ,
    Subgroup.exists_independent_cubics_of_quaternion_central_product
      B C hB hC hBC hcomm' hcentral h576⟩

/-- A point-stabilizer image on the initial eight contradicts N₂. This
uses an actual two-local normalizer, without any ambient fusion premise. -/
public theorem gTwo_card64_initial_eight_point_impossible
    {G : Type*} [Group G] [Finite G] (hN : IsNTwoGroup G)
    (data : GTwoTwoDerivedTypeData G) (eight : GTwoCard64InitialEight data)
    (point : ElementaryEightPointImage eight.U) : False := by
  let := eight.elementary
  have hne : eight.U ≠ ⊥ := by
    intro heq
    have h := eight.card
    rw [heq, Subgroup.card_bot] at h
    norm_num at h
  exact elementaryEight_normalizer_not_isSolvable_of_plane_point
    eight.U eight.card eight.plane point
    (hN _ ⟨eight.U, hne, IsElementaryAbelian.isPGroup 2 eight.U, rfl⟩)

/-- The order-576 exclusion reduces to two precise constructions: an
initial eight, and transport of the independent actors to a point image
on that same eight. The transport receives the actual quaternion factors,
their join equality, and the complete cubic-action package. -/
public theorem gTwo_card64_next_normalizer_ne_576_of_eight_transport
    {G : Type*} [Group G] [Finite G] (hN : IsNTwoGroup G)
    (hcore : ∀ V : Subgroup G, IsTwoLocal V → pPrimeCore 2 V = ⊥)
    (data : GTwoTwoDerivedTypeData G) (hcard : Nat.card data.sylowIntersection = 64)
    (hInitial : Nonempty (GTwoCard64InitialEight data)) :
    letI := data.groupK
    letI := data.finiteK
    let Qb := (QAt data.Γ data.criticalPath.firstStep).map data.embedding
    (∀ B C : Subgroup G,
      Nonempty (B ≃* QuaternionGroup 2) → Nonempty (C ≃* QuaternionGroup 2) →
      Nat.card (B ⊓ C : Subgroup G) = 2 →
      (∀ b ∈ B, ∀ c ∈ C, b * c = c * b) → Qb = B ⊔ C →
      Subgroup.QuaternionIndependentCubics B C →
      ∀ eight : GTwoCard64InitialEight data,
        Nonempty (ElementaryEightPointImage eight.U)) →
    Nat.card (Subgroup.normalizer (Qb : Set G)) ≠ 576 := by
  let := data.groupK
  let := data.finiteK
  dsimp only
  intro htransport h576
  obtain ⟨B, C, hB, hC, hinter, hcomm, hQ, ⟨actors⟩⟩ :=
    gTwo_card64_next_independent_cubics_of_card576 hN hcore data hcard h576
  obtain ⟨eight⟩ := hInitial
  obtain ⟨point⟩ := htransport B C hB hC hinter hcomm hQ actors eight
  exact gTwo_card64_initial_eight_point_impossible hN data eight point

end Stellmacher.Recognition
