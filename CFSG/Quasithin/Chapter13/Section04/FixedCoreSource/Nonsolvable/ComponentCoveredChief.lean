module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.CoveredIntersection
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.CentralResidual

/-!
# The covered original row has at least three L₀ chief factors

Retain L₀ = O²(O₂,Z(L)), its actual inclusion in L, and its intrinsic two-core.
The original faithful-local hypothesis gives F*(L)=O₂(L), hence the core is
self-centralizing. The central-cubic chief-section theorem therefore puts
cubic length at least three on O₂(L₀). Every complete L₀ chief series has
that same noncentral binary count because its two-core quotient has order three.

This is the lower bound used in 13.4.10(2). Placement of the same L₀ and
its moved core in the selected linear-three Baumann group, the upper-bound
comparison, and the rest of 13.4.10--17 remain with the nonsolvable owner.
Source: Aschbacher--Smith, 13.4.10(2), printed p.908 and Notation13.2.1, p.877.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02
open Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open NoncentralChiefRefinement NoncentralChiefRefinement.CubicComparison
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- Every actual cubic of the original L₀ moves at least three layers on O₂(L₀). -/
theorem covered_zero_cubic_length_ge_three
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hc : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (A : Subgroup G) (hA : Nat.card A = 3) (hAZ : A ≤ zero L) :
    3 ≤ conjugationCubicLength A ((zero L).pCoreIn 2) := by
  let N := (zero L).subgroupOf L
  have hAL : A ≤ L := hAZ.trans (zero_le L)
  let : N.Normal := normal_subgroupOf_of_le_normalizer (L_normalizes_zero L)
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect h.maximal_faithful.1.1
  have hpN : IsPPerfect 2 N := (residual_isPPerfect _).of_surjective
    (subgroupOfEquivOfLe (zero_le L)).symm.toMonoidHom
    (subgroupOfEquivOfLe (zero_le L)).symm.surjective
  have hq : Nat.card (N ⧸ pCore 2 N) = 3 := by
    let e := subgroupOfEquivOfLe (zero_le L)
    exact (Nat.card_congr (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).toEquiv).trans
      (Solvable.covered_zero_core_card hc)
  have hcenter : N.map (QuotientGroup.mk' (pCore 2 L)) ≤ center (L ⧸ pCore 2 L) := by
    rintro _ ⟨l,hl,rfl⟩
    obtain ⟨x,hx,hxl⟩ := residual_le (centralPreimage L) hl
    have he : x = l := Subtype.ext hxl
    exact he ▸ hx
  have hself : centralizer (pCore 2 L : Set L) ≤ pCore 2 L := by
    rw [←h.maximal_faithful.2.1.2.2]
    exact centralizer_generalizedFitting_le L
  have hAi : Nat.card (A.subgroupOf L) = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAL).toEquiv).trans hA
  have hb := central_residual_cubic_length_ge_three N hpN hcenter hq hself
    (A.subgroupOf L) hAi (fun _ hx => hAZ hx)
  rw [←length_map_injective L.subtype L.subtype_injective,
    map_subgroupOf_eq_of_le hAL,map_pCoreIn_of_injective 2 _ _ L.subtype_injective,
    map_subgroupOf_eq_of_le (zero_le L)] at hb
  exact hb

/-- Every complete chief series of the literal original L₀ has at least three noncentral binary factors. -/
theorem covered_zero_chief_count_ge_three
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hc : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (s : ChiefSeries (zero L)) (h0 : s.head = ⊥) (h1 : s.last = ⊤) :
    3 ≤ s.noncentralTwoCount := by
  have hq := Solvable.covered_zero_core_card hc
  have hd : 3 ∣ Nat.card (zero L) := by
    rw [←hq,←index_eq_card]
    exact (pCore 2 (zero L)).index_dvd_card
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := zero L) 3 hd
  let A := zpowers (a : G)
  have hA : Nat.card A = 3 := by rw [Nat.card_zpowers,(zero L).orderOf_coe a,ha]
  have hAZ : A ≤ zero L := zpowers_le.mpr a.property
  have hb := covered_zero_cubic_length_ge_three h hc A hA hAZ
  have hAi : Nat.card (A.subgroupOf (zero L)) = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAZ).toEquiv).trans hA
  rw [count_of_core_quotient_card_three hq (A.subgroupOf (zero L)) hAi s h0 h1]
  have he := length_map_injective (zero L).subtype (zero L).subtype_injective
    (A.subgroupOf (zero L)) (pCore 2 (zero L))
  rw [map_subgroupOf_eq_of_le hAZ] at he
  exact he ▸ hb

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
