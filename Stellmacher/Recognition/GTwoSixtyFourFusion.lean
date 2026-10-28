module

public import Stellmacher.Recognition.GTwoSixtyFourNormalizer
public import ABG.ChapterII.Section1.CentricFusionRelation

/-!
# Ambient fusion separation for the order-64 G₂ configuration

The canonical index-two subgroup of the distinguished Sylow subgroup has an
outside involution whose ambient conjugacy class misses that subgroup.
Centric normalizer control preserves membership in the canonical subgroup on
involutions; the centric fusion theorem extends this preservation to ambient
conjugacy. Sylow conjugacy then transports both the subgroup and the separated
involution to any supplied Sylow two-subgroup.

The argument uses the actual exceptional-type configuration, local N₂
solvability, and trivial odd cores of two-local subgroups. Simplicity and
nonsolvability are unnecessary for separation itself; they enter the later
transfer contradiction.

Source: Stellmacher (8.6)(a) and the subsequent local-type definition,
`refs/latex/stellmacher-n-group.tex`; the centric fusion reduction is ABG,
Chapter II §1 (article pp.10–11).
-/

namespace Stellmacher.Recognition

open BenderSuzuki.External BenderSuzuki.PFchapter1section1

/-- An involution outside the canonical subgroup has no ambient conjugate
inside it. The normalizer theorem supplies the ambient fusion input. -/
public theorem gTwo_card64_transfer_fusion_separation
    {G : Type*} [Group G] [Finite G] (hN : IsNTwoGroup G)
    (hcore : ∀ V : Subgroup G, IsTwoLocal V → pPrimeCore 2 V = ⊥)
    (data : GTwoTwoDerivedTypeData G)
    (hcard : Nat.card data.sylowIntersection = 64) :
    ∃ t : data.sylowIntersection, orderOf t = 2 ∧
      ∀ u : data.sylowIntersection, u ∈ gTwoCard64TransferSubgroup data →
        ¬ IsConj (t : G) (u : G) := by
  let S := data.sylowIntersection
  let U := gTwoCard64TransferSubgroup data
  obtain ⟨t, ht, htU⟩ := gTwo_card64_outside_involution data hcard
  let R : S → S → Prop := fun x y =>
    orderOf x = 2 → orderOf y = 2 ∧ (x ∈ U ↔ y ∈ U)
  have hrefl : ∀ x, R x x := fun x hx => ⟨hx, Iff.rfl⟩
  have htrans : ∀ {x y z}, R x y → R y z → R x z := by
    intro x y z hxy hyz hx
    obtain ⟨hy, hUxy⟩ := hxy hx
    obtain ⟨hz, hUyz⟩ := hyz hy
    exact ⟨hz, hUxy.trans hUyz⟩
  have hstep : ∀ (X : Subgroup G), HuppertExtremal S X →
      subgroupCentralizerIn (S : Subgroup G) X ≤ X →
      ∀ g : G, g ∈ Subgroup.normalizer (X : Set G) →
      ∀ x y : S, (x : G) ∈ X →
      g⁻¹ * (x : G) * g = (y : G) → R x y := by
    intro X hX hc g hg x y hx hxy hx2
    have hconj : IsConj (x : G) (y : G) :=
      isConj_iff.mpr ⟨g⁻¹, by simpa only [inv_inv] using hxy⟩
    have horder : orderOf x = orderOf y := by
      obtain ⟨c, hc⟩ := hconj
      simpa only [Subgroup.orderOf_coe] using hc.orderOf_eq (c : G)
    exact ⟨horder.symm.trans hx2,
      gTwo_card64_normalizer_preserves_transfer hN hcore data hcard
        X hX hc g hg x y hx hxy hx2⟩
  refine ⟨t, ht, ?_⟩
  intro u hu hconj
  have hR := ABG.centric_fusion_relation S R hrefl htrans hstep hconj
  exact htU ((hR ht).2.mpr hu)

/-- Every Sylow two-subgroup of order 64 in the actual G₂ local type has an
index-two subgroup separated by ambient fusion from an involution. -/
public theorem gTwo_card64_fusion_separation
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hN : IsNTwoGroup G)
    (hcore : ∀ V : Subgroup G, IsTwoLocal V → pPrimeCore 2 V = ⊥)
    (hType : IsOfGTwoTwoDerivedType G) (hcard : Nat.card S = 64) :
    ∃ (U : Subgroup S) (t : S), U.index = 2 ∧ orderOf t = 2 ∧
      ∀ u : S, u ∈ U → ¬ IsConj (t : G) (u : G) := by
  obtain ⟨data⟩ := hType
  have hcard₀ : Nat.card data.sylowIntersection = 64 :=
    (Nat.card_congr (data.sylowIntersection.equiv S).toEquiv).trans hcard
  obtain ⟨t, ht, hsep⟩ := gTwo_card64_transfer_fusion_separation hN hcore data hcard₀
  let U := gTwoCard64TransferSubgroup data
  have hindex : U.index = 2 := gTwo_card64_transfer_index data hcard₀
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G data.sylowIntersection S
  let e := data.sylowIntersection.equivSMul g
  refine ⟨U.map e.toMonoidHom, e t, ?_, ?_, ?_⟩
  · exact (U.index_map_equiv e).trans hindex
  · exact (orderOf_injective e.toMonoidHom e.injective t).trans ht
  · intro u hu hconj
    obtain ⟨v, hv, rfl⟩ := hu
    have htconj : IsConj (t : G) (e t : G) := isConj_iff.mpr ⟨g, rfl⟩
    have hvconj : IsConj (v : G) (e v : G) := isConj_iff.mpr ⟨g, rfl⟩
    exact hsep v hv (htconj.trans (hconj.trans hvconj.symm))

end Stellmacher.Recognition
