module

public import Theory.GroupTheory.CComponent.HexacodeTheta.InnerAction
public import Theory.GroupTheory.PResidual.PrimeTo
public import Theory.Mathieu.M22.TripleCover.CubicFacts

/-!
# Order-three actors on a Mathieu triple-cover C-component

Pass to the component image in the normalizer modulo its two-core.
The genuine triple-cover quotient has cubic center, three-rank at least
two, no order-nine elements, and a two-group of outer automorphisms.
The inner-action rank obstruction forces an order-three actor into the
component image. Its original membership then lifts across the two-group
supplement, using the actual intrinsic component quotient.

This supplies the M̂₂₂ containment used in the source field sieve; the
chapter consumer constructs its marked replacement on the native hexad.
Source: Aschbacher–Smith A.3.18, printed pp.51–52, and 13.8.21(2), p.956.
-/

public section
open Subgroup
namespace Theory.GroupTheory.TripleMathieuTheta

private theorem order_three_mem_of_normal_cComponent {G : Type*} [Group G] [Finite G]
    (L : Subgroup G) [L.Normal] (hL : L.IsCComponent)
    {A : Type*} [Group A] [Finite A]
    (hcenter : Nat.card (center A) = 3)
    (hcubic : ∀ z : A, z ^ 9 = 1 → z ^ 3 = 1)
    (houter : IsPGroup 2 (MulAut.Outer A)) (hrank : 2 ≤ primeRank 3 A)
    (e : (L ⧸ pCore 2 L) ≃* A)
    (hr : primeRank 3 G ≤ 2) {x : G} (hx : x ^ 3 = 1) : x ∈ L := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let B := L.map q
  let eB : B ≃* A :=
    (cComponentTwoCoreQuotientEquiv hL).symm.trans e
  let _ : B.Normal := (inferInstance : L.Normal).map q (QuotientGroup.mk'_surjective _)
  have hzc : Nat.card (center B) = 3 :=
    (Nat.card_congr (centerCongr eB).toEquiv).trans hcenter
  have hz : ∀ z ∈ center B, z ^ 3 = 1 := by
    intro z hz
    have hh : (⟨z, hz⟩ : center B) ^ Nat.card (center B) = 1 := pow_card_eq_one'
    rw [hzc] at hh
    exact congrArg Subtype.val hh
  have hexp : ∀ z : B, z ^ 9 = 1 → z ^ 3 = 1 := by
    intro z hz
    apply eB.injective
    simpa only [map_pow, map_one] using
      hcubic (eB z) (by simpa only [map_pow, map_one] using congrArg eB hz)
  have ho : IsPGroup 2 (MulAut.Outer B) :=
    houter.of_injective
      (MulAut.outerCongr eB).toMonoidHom (MulAut.outerCongr eB).injective
  have hrB : 2 ≤ primeRank 3 B := by
    rw [primeRank_congr 3 eB]
    exact hrank
  have hbar : q x ∈ B := HexacodeTheta.order_three_mem_of_normal B hz hexp ho hrB
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

/-- An order-three element normalizing a triple M₂₂ C-component lies in it. -/
theorem order_three_mem {G : Type*} [Group G] [Finite G]
    (L : Subgroup G) (hL : L.IsCComponent)
    (e : (L ⧸ pCore 2 L) ≃* Sporadic.Mathieu.M22TripleCover)
    (hr : primeRank 3 G ≤ 2) {x : G}
    (hx : orderOf x = 3) (hn : x ∈ normalizer (L : Set G)) : x ∈ L := by
  let N := normalizer (L : Set G)
  let D := L.subgroupOf N
  let eD : (D ⧸ pCore 2 D) ≃* Sporadic.Mathieu.M22TripleCover :=
    (QuotientGroup.congr _ _ (subgroupOfEquivOfLe L.le_normalizer)
      (pCore_map_iso 2 _)).trans e
  have hx3 : (⟨x, hn⟩ : N) ^ 3 = 1 := by
    apply Subtype.ext
    simpa [hx] using pow_orderOf_eq_one x
  exact order_three_mem_of_normal_cComponent D (hL.subgroupOf L.le_normalizer)
    Sporadic.Mathieu.M22TripleCover.center_card
    (fun _ => Sporadic.Mathieu.M22TripleCover.cube_eq_one_of_ninth)
    Sporadic.Mathieu.M22TripleCover.outer_two Sporadic.Mathieu.M22TripleCover.two_le_threeRank eD
    ((primeRank_le_of_injective 3 N.subtype N.subtype_injective).trans hr) hx3

end Theory.GroupTheory.TripleMathieuTheta
