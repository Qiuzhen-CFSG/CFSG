module

public import Theory.GroupTheory.UniqueInvolutionCoreCardTwo
public import Theory.GroupTheory.SylowNormalIntersection
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Restriction of the fused-involution calculation to the selected Sylow

The source normal subgroups are intersections inside the actual selected
Sylow subgroup. Restrict the ambient centralizer containment to that group,
retaining the elementary root subgroup and both normal intersections. The
unique-involution fusion argument then gives order two. A second calculation
transports a normal Sylow intersection to every Sylow of the normal subgroup.

Source: GLS IV, Chapter 2, Corollary 16.6(b).
-/

noncomputable section
namespace BenderSuzuki.ZD.Section16.NativeSource
open Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- The ambient centralizer formula implies the literal order-two result
inside the selected two-subgroup. -/
public theorem centralizer_intersection_card_two
    (T L Q : Subgroup G) (hT : IsPGroup 2 T)
    (hTL : T ≤ normalizer (L : Set G)) (hQT : Q ≤ T) (hQL : Q ≤ L)
    [IsElementaryAbelian 2 Q]
    (hcent : T ⊓ centralizer (T ⊓ L : Subgroup G) ≤ Q ⊔ centralizer (L : Set G))
    (u : T) (huC : (u : G) ∈ centralizer (L : Set G)) (hu2 : orderOf u = 2)
    (huniq : ∀ v : T, (v : G) ∈ centralizer (L : Set G) → orderOf v = 2 → v = u)
    (a : MulAut T) (hne : a u ≠ u) (hout : (a u : G) ∉ L) :
    Nat.card ((centralizer (L : Set G)).subgroupOf T) = 2 := by
  let U := (centralizer (L : Set G)).subgroupOf T
  let P := L.subgroupOf T
  let R := Q.subgroupOf T
  let : P.Normal := normal_subgroupOf_of_le_normalizer hTL
  have hNC : normalizer (L : Set G) ≤ normalizer (centralizer (L : Set G) : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (centralizer_le_normalizer (L : Set G))).mp inferInstance
  let : U.Normal := normal_subgroupOf_of_le_normalizer (hTL.trans hNC)
  let : IsElementaryAbelian 2 R := IsElementaryAbelian.subgroupOf hQT
  have hQC : Q ≤ centralizer (centralizer (L : Set G) : Set G) := by
    intro q hq c hc
    exact (hc q (hQL hq)).symm
  have hRU : R ≤ centralizer (U : Set T) := by
    intro q hq c hc
    exact Subtype.ext (hQC hq c hc)
  have hrestrict : centralizer (P : Set T) ≤ R ⊔ U := by
    intro x hx
    have hxC : (x : G) ∈ centralizer (T ⊓ L : Subgroup G) := by
      intro y hy
      exact congrArg Subtype.val (hx (⟨y, hy.1⟩ : T) hy.2)
    have hxQU := hcent ⟨x.property, hxC⟩
    rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right Q _
      (hQC.trans (centralizer_le_normalizer _))] at hxQU
    obtain ⟨q, hq, c, hc, he⟩ := hxQU
    have hcT : c ∈ T := by
      have hh := T.mul_mem (T.inv_mem (hQT hq)) x.property
      simpa only [← he, inv_mul_cancel_left] using hh
    have hh : (⟨q, hQT hq⟩ : T) * ⟨c, hcT⟩ ∈ R ⊔ U := mul_mem_sup hq hc
    exact (show (⟨q, hQT hq⟩ : T) * ⟨c, hcT⟩ = x from Subtype.ext he) ▸ hh
  exact card_eq_two_of_fused_unique_involution hT U P R u huC hu2
    (fun v hv hv2 => huniq v hv hv2) a hne hout hRU hrestrict

/-- Cardinality of one normal Sylow intersection controls every Sylow of
that same normal subgroup, through the original ambient subtype map. -/
public theorem sylow_card_eq_of_normal_intersection
    (B : Subgroup G) (J : Subgroup B) [J.Normal] (T : Sylow 2 B)
    {k : ℕ}
    (hc : Nat.card ((J.map B.subtype).subgroupOf ((T : Subgroup B).map B.subtype)) = k)
    (S : Sylow 2 J) : Nat.card S = k := by
  obtain ⟨S₀, hS₀⟩ := T.exists_subgroupOf_eq_of_normal J
  have hcard : Nat.card ((T : Subgroup B).subgroupOf J) = k := by
    rw [← card_map_of_injective J.subtype_injective,
      subgroupOf_map_subtype, ← card_map_of_injective B.subtype_injective,
      map_inf _ _ _ B.subtype_injective]
    rw [← card_map_of_injective ((T : Subgroup B).map B.subtype).subtype_injective,
      subgroupOf_map_subtype] at hc
    simpa only [inf_comm] using hc
  rw [← hS₀] at hcard
  rw [S.card_eq_multiplicity, ← S₀.card_eq_multiplicity]
  exact hcard

end BenderSuzuki.ZD.Section16.NativeSource
