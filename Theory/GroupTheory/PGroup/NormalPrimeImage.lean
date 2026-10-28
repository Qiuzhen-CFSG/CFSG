module

public import Theory.GroupTheory.PGroup.NormalSubgroups
public import Theory.GroupTheory.PCoreImage

/-!
# Small normal images in prime-group quotients

A normal subgroup of a finite p-group whose order divides p is central:
if it is nontrivial, the central subgroup of order p already exhausts it.
Consequently a normal subgroup A with |A/O_q(A)| dividing p has central
image in G/O_q(G), provided that quotient is a p-group. The proof uses
the natural inclusion and quotient maps, including O_q(A) ≤ O_q(G).

This is the elementary normal-subgroup argument used in Aschbacher--Smith,
proof of 15.3.38, printed p.1136, to exclude the extraspecial alternative.
-/

public section
open Subgroup
namespace IsPGroup
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- Normal subgroups of order one or p in a finite p-group are central. -/
theorem normal_le_center_of_card_dvd_prime (hG : IsPGroup p G)
    (N : Subgroup G) [N.Normal] (hcard : Nat.card N ∣ p) : N ≤ center G := by
  by_cases hN : N = ⊥
  · rw [hN]
    exact bot_le
  let : Fact (IsPGroup p G) := ⟨hG⟩
  have hn : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hN
  obtain ⟨Z, _, hZN, hZcard, hZ⟩ :=
    exists_central_subgroup_card_eq_prime_in_normal (p := p) N hn
  have he : Z = N := eq_of_le_of_card_ge hZN (by
    rw [hZcard]
    exact Nat.le_of_dvd (Fact.out : p.Prime).pos hcard)
  exact he ▸ hZ

end IsPGroup

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The actual quotient image of a relatively normal subgroup has order
dividing its own prime-core quotient order. -/
theorem card_image_core_quotient_dvd {q : ℕ} [Fact q.Prime]
    {A Y : Subgroup G} (hAY : A ≤ Y) (hYA : Y ≤ normalizer (A : Set G)) :
    Nat.card ((A.subgroupOf Y).map (QuotientGroup.mk' (pCore q Y))) ∣
      Nat.card (A ⧸ pCore q A) := by
  let f := (QuotientGroup.mk' (pCore q Y)).comp (inclusion hAY)
  have hk : pCore q A ≤ f.ker := by
    intro a ha
    have hc := pCoreIn_mono_of_normalizes (p := q) hAY hYA
      (mem_map_of_mem A.subtype ha)
    obtain ⟨b, hb, he⟩ := hc
    have he' : b = inclusion hAY a := Subtype.ext he
    rw [he'] at hb
    exact (QuotientGroup.eq_one_iff _).mpr hb
  let fbar := QuotientGroup.lift (pCore q A) f hk
  have hr : fbar.range = (A.subgroupOf Y).map (QuotientGroup.mk' (pCore q Y)) := by
    ext z
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (pCore q A) a
      exact ⟨inclusion hAY a, a.property, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨QuotientGroup.mk' (pCore q A) ⟨a, ha⟩, rfl⟩
  rw [← hr]
  exact card_range_dvd fbar

/-- A normal residual with small prime-core quotient maps into the actual
centre preimage, with no supplement or product hypothesis. -/
theorem image_core_quotient_le_center {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {A Y : Subgroup G} (hAY : A ≤ Y) (hYA : Y ≤ normalizer (A : Set G))
    (hY : IsPGroup p (Y ⧸ pCore q Y))
    (hA : Nat.card (A ⧸ pCore q A) ∣ p) :
    (A.subgroupOf Y).map (QuotientGroup.mk' (pCore q Y)) ≤
      center (Y ⧸ pCore q Y) := by
  let : (A.subgroupOf Y).Normal := normal_subgroupOf_of_le_normalizer hYA
  let : ((A.subgroupOf Y).map (QuotientGroup.mk' (pCore q Y))).Normal :=
    (inferInstance : (A.subgroupOf Y).Normal).map _ (QuotientGroup.mk'_surjective _)
  exact hY.normal_le_center_of_card_dvd_prime _
    ((card_image_core_quotient_dvd hAY hYA).trans hA)

end Subgroup
