module
public import Theory.GroupTheory.CComponent.CenterlessRankNormal
public import Theory.GroupTheory.CubicIntersectionRankLower

/-!
# Normality with a center of order at most three

Distinct component conjugates commute, and their intersection embeds in a
component center. Two factors of cubic rank at least two with intersection
of order at most three force cubic rank at least three. Thus an ambient
cubic-rank bound of two forces normality. Passing through the ambient
two-core gives the corresponding result for original C-components.

Source: Aschbacher–Smith A.3.8(3), printed p.46, and the normality step
of C.4.5, printed p.152. The cubic intersection calculation also retains
nontrivial cubic centers; no centerless hypothesis is needed.
-/

public section
open Subgroup Theory.GroupTheory
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

theorem IsComponent.normal_of_cubic_center_threeRank
    {D : Subgroup G} (hD : IsComponent G D)
    (hz : Nat.card (center D) ≤ 3)
    (hD2 : 2 ≤ primeRank 3 D) (hG2 : primeRank 3 G ≤ 2) : D.Normal := by
  apply normal_iff_map_conj_eq.mpr
  intro g
  by_contra hne
  let E := D.map (MulAut.conj g).toMonoidHom
  have hDE : D ≤ centralizer (E : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (hD.commutator_eq_bot_of_ne (hD.map_conj g) (fun he => hne he.symm))
  have hI : D ⊓ E ≤ (center D).map D.subtype := by
    rintro x ⟨hxD,hxE⟩
    refine ⟨⟨x,hxD⟩,mem_center_iff.mpr ?_,rfl⟩
    intro y
    exact Subtype.ext ((le_centralizer_iff.mp hDE) hxE y y.property)
  have hc : Nat.card (D ⊓ E : Subgroup G) ≤ 3 :=
    (card_le_of_le hI).trans (by
      rwa [card_map_of_injective D.subtype_injective])
  have he : primeRank 3 D = primeRank 3 E :=
    primeRank_equiv 3 ((MulAut.conj g).subgroupMap D)
  have h3 := three_le_primeRank_of_cubic_intersection D E hDE hc hD2 (he ▸ hD2)
  omega
end Theory.GroupTheory

namespace Subgroup
variable {G : Type*} [Group G] [Finite G] {K : Subgroup G}
theorem IsCComponent.normal_of_cubic_core_center_threeRank
    (hK : K.IsCComponent) [IsQuasisimple (K ⧸ pCore 2 K)]
    (hz : Nat.card (center (K ⧸ pCore 2 K)) ≤ 3)
    (hrK : 2 ≤ primeRank 3 (K ⧸ pCore 2 K)) (hrG : primeRank 3 G ≤ 2) : K.Normal := by
  let := pCore_isNilpotent (p := 2) (G := G)
  let q := QuotientGroup.mk' (pCore 2 G)
  let B := K.map q
  let e : (K ⧸ pCore 2 K) ≃* B := cComponentTwoCoreQuotientEquiv hK
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv e
  have hb : IsComponent (G ⧸ pCore 2 G) B :=
    ⟨(hK.map_quotient (pCore 2 G)).subnormal,inferInstance⟩
  have hcz : Nat.card (center B) ≤ 3 := by
    rwa [← Nat.card_congr (centerCongr e).toEquiv]
  have hrB : 2 ≤ primeRank 3 B := by rwa [←primeRank_congr 3 e]
  have hrQ : primeRank 3 (G ⧸ pCore 2 G) ≤ 2 :=
    (primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup).trans hrG
  let : B.Normal := hb.normal_of_cubic_center_threeRank hcz hrB hrQ
  exact cComponent_normal_of_quotient_normal hK (pCore 2 G) inferInstance
end Subgroup

