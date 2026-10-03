module

public import Stellmacher.Recognition.GTwoSixtyFourIndexTwo
public import Theory.GroupTheory.C4SquareInvertingCharacteristic

/-!
# Normalizer actions on the order-64 vertex cores

The initial vertex core has a characteristic C₄ × C₄ base. Its intersection
with the canonical transfer subgroup is exactly that base, so its ambient
normalizer preserves transfer membership, even without restricting to involutions.

The characteristic property follows from the bound of eight on abelian
subgroups crossing the base. The supplied inverter lies outside the transfer
subgroup; the index-two coset rule then identifies the intersection.

Source: Stellmacher (8.6)(a), `refs/latex/stellmacher-n-group.tex`.
-/

namespace Stellmacher.Recognition

open Later SectionsFiveToSeven SevenSix

/-- The initial base is characteristic in its vertex core and is its exact
intersection with the canonical transfer subgroup. -/
public theorem gTwo_card64_initial_core_base
    {G : Type*} [Group G] [Finite G] (data : GTwoTwoDerivedTypeData G)
    (hcard : Nat.card data.sylowIntersection = 64) :
    letI := data.groupK
    letI := data.finiteK
    let A := (twoCoreIn (EAt data.Γ data.criticalPath.a)).map data.embedding
    let Q := (QAt data.Γ data.criticalPath.a).map data.embedding
    A ≤ Q ∧ (A.subgroupOf Q).Characteristic ∧
      ∀ x : data.sylowIntersection, (x : G) ∈ Q →
        (x ∈ gTwoCard64TransferSubgroup data ↔ (x : G) ∈ A) := by
  let := data.groupK
  let := data.finiteK
  let A0 := twoCoreIn (EAt data.Γ data.criticalPath.a)
  let Q0 := QAt data.Γ data.criticalPath.a
  let A := A0.map data.embedding
  let Q := Q0.map data.embedding
  let U := gTwoCard64TransferSubgroup data
  have hA0Q0 : A0 ≤ Q0 := by
    obtain ⟨_, _, _, _, hgen⟩ := gTwo_card64_outside_inverter data hcard
    dsimp [A0, Q0]
    rw [hgen]
    exact le_sup_left
  have hAQ : A ≤ Q := Subgroup.map_mono hA0Q0
  have hAmodel : Nonempty (A ≃* C4 × C4) := by
    obtain ⟨e⟩ := data.caseA.twoCore_model
    exact ⟨(A0.equivMapOfInjective data.embedding data.embedding_injective).symm.trans e⟩
  have hAc : Nat.card A = 16 := by
    obtain ⟨e⟩ := hAmodel
    rw [Nat.card_congr e.toEquiv, Nat.card_prod]
    norm_num [C4]
  have hQc : Nat.card Q = 32 := by
    rw [Subgroup.card_map_of_injective data.embedding_injective]
    exact (gTwo_card64_vertex_structure data hcard).1
  have hi : (A.subgroupOf Q).index = 2 := by
    have hh := (A.subgroupOf Q).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAQ).toEquiv, hAc, hQc] at hh
    omega
  have hAU (x : data.sylowIntersection) (hx : (x : G) ∈ A) : x ∈ U :=
    Subgroup.mem_sup_left hx
  obtain ⟨t, htQ, htU, htInv⟩ := gTwo_card64_initial_inverter_outside_transfer data hcard
  let tQ : Q := ⟨t, htQ⟩
  have htA : tQ ∉ A.subgroupOf Q := fun h => htU (hAU t h)
  have hchar : (A.subgroupOf Q).Characteristic :=
    Subgroup.characteristic_of_inverted_c4_square (A.subgroupOf Q)
      (hAmodel.elim (fun e => ⟨(Subgroup.subgroupOfEquivOfLe hAQ).trans e⟩))
      hi tQ htA (fun a ha => Subtype.ext (htInv a ha))
  refine ⟨hAQ, hchar, ?_⟩
  intro x hxQ
  constructor
  · intro hxU
    by_contra hxA
    have hprod : (⟨x, hxQ⟩ : Q) * tQ ∈ A.subgroupOf Q :=
      ((A.subgroupOf Q).mul_mem_iff_of_index_two hi).mpr (iff_of_false hxA htA)
    have hprodU : x * t ∈ U := hAU (x * t) hprod
    exact htU ((U.mul_mem_cancel_left hxU).mp hprodU)
  · exact hAU x

/-- Every ambient normalizer of the initial vertex core preserves canonical
transfer membership. This holds for all core elements, hence for involutions. -/
public theorem gTwo_card64_initial_core_normalizer_preserves_transfer
    {G : Type*} [Group G] [Finite G] (data : GTwoTwoDerivedTypeData G)
    (hcard : Nat.card data.sylowIntersection = 64) :
    letI := data.groupK
    letI := data.finiteK
    ∀ (g : G),
      g ∈ Subgroup.normalizer ((QAt data.Γ data.criticalPath.a).map data.embedding : Set G) →
      ∀ x y : data.sylowIntersection,
        (x : G) ∈ (QAt data.Γ data.criticalPath.a).map data.embedding →
        g⁻¹ * (x : G) * g = (y : G) →
        (x ∈ gTwoCard64TransferSubgroup data ↔ y ∈ gTwoCard64TransferSubgroup data) := by
  let := data.groupK
  let := data.finiteK
  let A := (twoCoreIn (EAt data.Γ data.criticalPath.a)).map data.embedding
  let Q := (QAt data.Γ data.criticalPath.a).map data.embedding
  obtain ⟨_, hchar, hmem⟩ := gTwo_card64_initial_core_base data hcard
  intro g hg x y hx hxy
  have hgi : g⁻¹ ∈ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.normalizer (Q : Set G)).inv_mem hg
  have hy : (y : G) ∈ Q := by
    have hh := (Subgroup.mem_normalizer_iff.mp hgi (x : G)).mp hx
    simpa only [inv_inv, hxy] using hh
  rw [hmem x hx, hmem y hy]
  let φ : MulAut Q := Q.normalizerMonoidHom ⟨g⁻¹, hgi⟩
  have hfix := hchar.fixed φ
  have heq : φ ⟨x, hx⟩ = (⟨y, hy⟩ : Q) := Subtype.ext (by
    change g⁻¹ * (x : G) * (g⁻¹)⁻¹ = (y : G)
    simpa only [inv_inv] using hxy)
  have hh : (⟨x, hx⟩ : Q) ∈ (A.subgroupOf Q).comap φ.toMonoidHom ↔
      (⟨x, hx⟩ : Q) ∈ A.subgroupOf Q := by rw [hfix]
  change φ ⟨x, hx⟩ ∈ A.subgroupOf Q ↔ (x : G) ∈ A at hh
  rw [heq] at hh
  exact hh.symm

end Stellmacher.Recognition
