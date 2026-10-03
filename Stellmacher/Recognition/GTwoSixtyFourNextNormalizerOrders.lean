module

public import Stellmacher.Recognition.GTwoSixtyFourNextCoreActions
public import Theory.GroupTheory.QuaternionCentralProductAutomorphisms

/-!
# Orders of the ambient second-core normalizer

In the order-64 G₂ configuration the second core is Q₈ ∘ Q₈ and is
self-centralizing in the ambient group. Its normalizer therefore has order
dividing 2304, by the intrinsic quaternion factors and their automorphism
orders. The normalizer contains the supplied second vertex, of order 192,
and its two-part is at most 64 because the distinguished Sylow is ambient.
Consequently its order is 192 or 576. In the former case containment and
equal orders identify it with the supplied vertex.

Source: the actual exceptional local data in Stellmacher (8.6)(a),
`refs/latex/stellmacher-n-group.tex`. No full-normalizer equality is assumed.
-/

namespace Stellmacher.Recognition

open Later SectionsFiveToSeven SevenSix

private theorem next_vertex_le_normalizer
    {G : Type*} [Group G] [Finite G] (data : GTwoTwoDerivedTypeData G) :
    letI := data.groupK
    letI := data.finiteK
    (GAt data.Γ data.criticalPath.firstStep).map data.embedding ≤
      Subgroup.normalizer
        ((QAt data.Γ data.criticalPath.firstStep).map data.embedding : Set G) := by
  let := data.groupK
  let := data.finiteK
  have hQ : QAt data.Γ data.criticalPath.firstStep =
      twoCoreIn (GAt data.Γ data.criticalPath.firstStep) :=
    data.Γ.twoCoreAt_def data.criticalPath.firstStep
  have hle : GAt data.Γ data.criticalPath.firstStep ≤
      Subgroup.normalizer (QAt data.Γ data.criticalPath.firstStep : Set data.K) := by
    rw [hQ]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (twoCoreIn_le _)).mp
      (twoCoreIn_normal _)
  exact (Subgroup.map_mono hle).trans (Subgroup.le_normalizer_map data.embedding)

/-- The full ambient normalizer of the second core has order 192 or 576. -/
public theorem gTwo_card64_next_normalizer_order_dichotomy
    {G : Type*} [Group G] [Finite G] (hN : IsNTwoGroup G)
    (hcore : ∀ V : Subgroup G, IsTwoLocal V → pPrimeCore 2 V = ⊥)
    (data : GTwoTwoDerivedTypeData G) (hcard : Nat.card data.sylowIntersection = 64) :
    letI := data.groupK
    letI := data.finiteK
    let Qb := (QAt data.Γ data.criticalPath.firstStep).map data.embedding
    let N := Subgroup.normalizer (Qb : Set G)
    Nat.card N = 192 ∨ Nat.card N = 576 := by
  let := data.groupK
  let := data.finiteK
  let Qb := (QAt data.Γ data.criticalPath.firstStep).map data.embedding
  let Pb := (GAt data.Γ data.criticalPath.firstStep).map data.embedding
  let N := Subgroup.normalizer (Qb : Set G)
  change Nat.card N = 192 ∨ Nat.card N = 576
  obtain ⟨_, _, _, hPb, hmodel⟩ := gTwo_card64_vertex_structure data hcard
  have hPbCard : Nat.card Pb = 192 := by
    rw [Subgroup.card_map_of_injective data.embedding_injective]
    exact hPb
  have hdiv : 192 ∣ Nat.card N := by
    rw [← hPbCard]
    exact Subgroup.card_dvd_of_le (next_vertex_le_normalizer data)
  have hbound : Nat.card N ∣ 2304 := by
    obtain ⟨B, C, ⟨eB⟩, ⟨eC⟩, hQeq, hinter, hcomm, _⟩ := hmodel
    have hcentral := gTwo_card64_next_core_centralizer_le hN hcore data hcard
    change Subgroup.centralizer (Qb : Set G) ≤ Qb at hcentral
    have hQmap : Qb = B.map data.embedding ⊔ C.map data.embedding := by
      dsimp [Qb]
      rw [hQeq, Subgroup.map_sup]
    change Nat.card (Subgroup.normalizer (Qb : Set G)) ∣ 2304
    rw [hQmap] at hcentral ⊢
    apply Subgroup.normalizer_card_dvd_of_quaternion_central_product
      (B.map data.embedding) (C.map data.embedding)
      ⟨(B.equivMapOfInjective data.embedding data.embedding_injective).symm.trans eB⟩
      ⟨(C.equivMapOfInjective data.embedding data.embedding_injective).symm.trans eC⟩
      ?_ ?_ hcentral
    · rw [← Subgroup.map_inf B C data.embedding data.embedding_injective,
        Subgroup.card_map_of_injective data.embedding_injective, hinter]
    · rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩
      rw [← map_mul, ← map_mul, hcomm b hb c hc]
  have hnot : ¬ 128 ∣ Nat.card N := by
    intro hd
    have h := data.sylowIntersection.pow_dvd_card_of_pow_dvd_card (n := 7)
      (hd.trans N.card_subgroup_dvd_card)
    rw [hcard] at h
    norm_num at h
  have hle : Nat.card N ≤ 2304 := Nat.le_of_dvd (by decide) hbound
  obtain ⟨k, hk⟩ := hdiv
  have hkbound : k ≤ 12 := by omega
  rw [hk] at hbound hnot ⊢
  interval_cases k <;> norm_num at *

/-- The order-192 alternative identifies the ambient normalizer with the
actual second vertex. -/
public theorem gTwo_card64_next_normalizer_eq_vertex_of_card192
    {G : Type*} [Group G] [Finite G]
    (data : GTwoTwoDerivedTypeData G) (hcard : Nat.card data.sylowIntersection = 64) :
    letI := data.groupK
    letI := data.finiteK
    let Qb := (QAt data.Γ data.criticalPath.firstStep).map data.embedding
    let Pb := (GAt data.Γ data.criticalPath.firstStep).map data.embedding
    let N := Subgroup.normalizer (Qb : Set G)
    Nat.card N = 192 → N = Pb := by
  let := data.groupK
  let := data.finiteK
  dsimp only
  intro hNcard
  symm
  apply Subgroup.eq_of_le_of_card_ge (next_vertex_le_normalizer data)
  rw [hNcard, Subgroup.card_map_of_injective data.embedding_injective,
    (gTwo_card64_vertex_structure data hcard).2.2.2.1]

end Stellmacher.Recognition
