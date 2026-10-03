module

public import Stellmacher.Recognition.Parrott.CentralizerStructure

/-!
# Conjugating the two lifts in a derived central fiber

For H=C_G(z) and J=O₂(H), the literal quotient J′/Z(J) is elementary
abelian of order sixteen. Every element t of the ambient image of J′
outside ⟨z⟩ is conjugate to zt by an element of J. Indeed J′=Z₂(J),
so [J,t] lies in Z(J)=⟨z⟩. Since t is not central, one commutator is
nonidentity and therefore equals z. The theorem retains the actual
conjugator in the two-core, for lifting quotient orbits to H-conjugacy.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
p.674, “as t ∼_J tz” in the local-centralizer paragraph.
-/

open Subgroup
open scoped commutatorElement IsMulCommutative

namespace Stellmacher.Recognition

/-- The literal derived central quotient is elementary abelian of order sixteen. -/
public theorem parrott_derived_quotient_structure
    {G : Type*} [Group G] [Finite G]
    (z : G) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let D := commutator J
    let Z := (center J).subgroupOf D
    IsElementaryAbelian 2 (D ⧸ Z) ∧ Nat.card (D ⧸ Z) = 16 := by
  intro H J D Z
  obtain ⟨hZmap, _, _, _, hUpper, hElem, hDcard, _⟩ := parrott_centralizer_structure z h
  let : IsElementaryAbelian 2 D := hElem
  have hZD : center J ≤ D := by
    rw [show D = Subgroup.upperCentralSeries J 2 from hUpper,
      ← Subgroup.upperCentralSeries_one]
    exact Subgroup.upperCentralSeries_mono J (by decide : 1 ≤ 2)
  have hZJcard : Nat.card (center J) = 2 := by
    have hc := card_map_of_injective (K := center J) (f := H.subtype.comp J.subtype)
      (H.subtype_injective.comp J.subtype_injective)
    rw [hZmap, Nat.card_zpowers, h.involution] at hc
    exact hc.symm
  have hZcard : Nat.card Z = 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe hZD).toEquiv).trans hZJcard
  refine ⟨{
    toIsMulCommutative := inferInstance
    exponent_dvd_p := (Group.exponent_quotient_dvd Z).trans
      (IsElementaryAbelian.exponent_dvd_p 2 D) }, ?_⟩
  have hc := Z.index_mul_card
  change Nat.card (D ⧸ Z) * Nat.card Z = Nat.card D at hc
  rw [hZcard, hDcard] at hc
  omega

/-- The two elements over a nonidentity derived central quotient element
are conjugate by an element of the actual two-core. -/
public theorem parrott_derived_central_twist_conjugator
    {G : Type*} [Group G] [Finite G]
    (z : G) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    ∀ t : G, t ∈ E → t ∉ zpowers z →
      ∃ g : H, g ∈ J ∧ (g : G) * t * (g : G)⁻¹ = z * t := by
  classical
  intro H J E t ht htz
  let embed := H.subtype.comp J.subtype
  have hinj : Function.Injective embed := H.subtype_injective.comp J.subtype_injective
  obtain ⟨hZmap, _, _, _, hUpper, _, _, _⟩ := parrott_centralizer_structure z h
  obtain ⟨x, hx, rfl⟩ := ht
  have hxZ : x ∉ center J := by
    intro hxZ
    apply htz
    rw [← hZmap]
    exact mem_map_of_mem embed hxZ
  obtain ⟨y, hy⟩ : ∃ y : J, y * x ≠ x * y := by
    simpa only [mem_center_iff, not_forall] using hxZ
  have hcomm : ⁅(⊤ : Subgroup J), commutator J⁆ ≤ center J := by
    rw [commutator_comm, hUpper]
    simpa only [Subgroup.upperCentralSeries_one] using commutator_upperCentralSeries_top_le J 1
  have hcZ : embed ⁅y, x⁆ ∈ zpowers z := by
    rw [← hZmap]
    exact mem_map_of_mem embed (hcomm (commutator_mem_commutator (mem_top y) hx))
  have hcne : embed ⁅y, x⁆ ≠ 1 := by
    intro heq
    exact hy (commutatorElement_eq_one_iff_mul_comm.mp
      (hinj (heq.trans (map_one embed).symm)))
  have hcz : embed ⁅y, x⁆ = z := by
    rw [mem_zpowers_iff_mem_range_orderOf, h.involution] at hcZ
    obtain ⟨n, hn, heq⟩ := Finset.mem_image.mp hcZ
    have hn2 := Finset.mem_range.mp hn
    interval_cases n
    · exact (hcne (by simpa using heq.symm)).elim
    · simpa using heq.symm
  refine ⟨y, y.property, ?_⟩
  change embed y * embed x * (embed y)⁻¹ = z * embed x
  rw [← hcz, commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv]
  group

end Stellmacher.Recognition
