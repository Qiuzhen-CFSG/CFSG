module

public import Theory.GroupTheory.CComponent.HexacodeTheta.InnerAction
public import Theory.GroupTheory.CComponent.HexacodeTheta.ExponentThree
public import Theory.Representation.HexacodeAction.OuterTwo
public import Theory.GroupTheory.PResidual.PrimeTo

/-!
# Order-three elements normalizing the hexacode C-component

If a C-component L has intrinsic two-core quotient the concrete triple
cover of A₆ and the ambient three-rank is at most two, every order-three
element normalizing L lies in L.

Work inside the actual normalizer N_G(L), then factor out its two-core.
The component image is the given triple cover. Its outer automorphism
group is a two-group, so an order-three actor acts by an inner
automorphism. The center has order three and the Sylow three-subgroups
have exponent three; the inner-action obstruction therefore puts the
actor in the component image. Finally, the relative index of L in
L O₂(N_G(L)) is coprime to three, which lifts membership to L.

This proves the intrinsic element-containment assertion used for the
Â₆ case of A.3.18(3a), without an ambient normality or theta-containment
assumption. Source: Aschbacher–Smith, combined manuscript (1 March
2004), printed pp.51–52, applied in 15.3.49(k), printed p.1144.
-/

public section

open Subgroup
namespace Theory.GroupTheory.HexacodeTheta

private theorem order_three_mem_of_normal_cComponent {G : Type*} [Group G] [Finite G]
    (L : Subgroup G) [L.Normal] (hL : L.IsCComponent)
    (e : (L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms)
    (hr : primeRank 3 G ≤ 2) {x : G} (hx : x ^ 3 = 1) : x ∈ L := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let B := L.map q
  let eB : B ≃* Atlas.Codes.HexEvenAutomorphisms :=
    (cComponentTwoCoreQuotientEquiv hL).symm.trans e
  let _ : B.Normal := (inferInstance : L.Normal).map q (QuotientGroup.mk'_surjective _)
  have hzc : Nat.card (center B) = 3 :=
    (Nat.card_congr (centerCongr eB).toEquiv).trans Representation.Hexacode.even_center_card
  have hz : ∀ z ∈ center B, z ^ 3 = 1 := by
    intro z hz
    have hh : (⟨z, hz⟩ : center B) ^ Nat.card (center B) = 1 := pow_card_eq_one'
    rw [hzc] at hh
    exact congrArg Subtype.val hh
  have hexp : ∀ z : B, z ^ 9 = 1 → z ^ 3 = 1 := by
    intro z hz
    apply eB.injective
    simpa only [map_pow, map_one] using
      cube_eq_one_of_ninth (g := eB z) (by simpa only [map_pow, map_one] using congrArg eB hz)
  have ho : IsPGroup 2 (MulAut.Outer B) :=
    Representation.Hexacode.even_outer_two.of_injective
      (MulAut.outerCongr eB).toMonoidHom (MulAut.outerCongr eB).injective
  have hrB : 2 ≤ primeRank 3 B := by
    rw [primeRank_congr 3 eB]
    exact Representation.Hexacode.two_le_primeRank_even
  have hbar : q x ∈ B := order_three_mem_of_normal B hz hexp ho hrB
    ((primeRank_quotient_le_of_isTwoGroup 3 (by decide) (pCore 2 G) pCore_isPGroup).trans hr)
    (by simpa only [map_pow, map_one] using congrArg q hx)
  have hxK : x ∈ L ⊔ pCore 2 G := by
    have hh : x ∈ (L.map q).comap q := hbar
    simpa only [comap_map_eq, q, QuotientGroup.ker_mk'] using hh
  let K := L ⊔ pCore 2 G
  let D := L.subgroupOf K
  have hi : Nat.Coprime 3 D.index := by
    change Nat.Coprime 3 (L.relIndex (L ⊔ pCore 2 G))
    rw [relIndex_sup_left]
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := G)).exists_card_dvd_pow
    exact (((by decide : Nat.Coprime 3 2).pow_right n).coprime_dvd_right hn).coprime_dvd_right
      (relIndex_dvd_card _ _)
  have hx3 : (⟨x, hxK⟩ : K) ^ (3 ^ 1) = 1 := by
    apply Subtype.ext
    simpa using hx
  exact primeToResidual_le D hi (mem_primeToResidual_of_pow hx3)

/-- An order-three element normalizing a hexacode C-component lies in it. -/
theorem order_three_mem {G : Type*} [Group G] [Finite G]
    (L : Subgroup G) (hL : L.IsCComponent)
    (e : (L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms)
    (hr : primeRank 3 G ≤ 2) {x : G}
    (hx : orderOf x = 3) (hn : x ∈ normalizer (L : Set G)) : x ∈ L := by
  let N := normalizer (L : Set G)
  let D := L.subgroupOf N
  let eD : (D ⧸ pCore 2 D) ≃* Atlas.Codes.HexEvenAutomorphisms :=
    (QuotientGroup.congr _ _ (subgroupOfEquivOfLe L.le_normalizer)
      (pCore_map_iso 2 _)).trans e
  have hx3 : (⟨x, hn⟩ : N) ^ 3 = 1 := by
    apply Subtype.ext
    simpa [hx] using pow_orderOf_eq_one x
  exact order_three_mem_of_normal_cComponent D (hL.subgroupOf L.le_normalizer) eD
    ((primeRank_le_of_injective 3 N.subtype N.subtype_injective).trans hr) hx3

end Theory.GroupTheory.HexacodeTheta
