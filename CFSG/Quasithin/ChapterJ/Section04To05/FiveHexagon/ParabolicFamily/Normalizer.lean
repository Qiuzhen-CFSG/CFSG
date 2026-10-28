module

public import CFSG.Quasithin.ChapterJ.Section04To05.SourceAmalgam.FirstOvergroup
public import CFSG.Quasithin.ChapterJ.Section04To05.FiveNormalizer.Image
public import Mathlib.GroupTheory.IndexNormal

/-!
# The original first endpoint normalizer

The original F₁ has index two in F₁Q, so Q normalizes it. Its image in H/Q
is the normalizer of the original Sylow five-group. A Sylow normalizer is
self-normalizing, hence every element of H normalizing F₁ belongs to F₁Q.
The quotient image therefore remembers the original H-conjugate of F₁.

The same index-two argument places every order-five subgroup of F₁Q in F₁.
This retains arbitrary original lifts of a quotient pentagon, rather than
selecting a particular five-subgroup above it. Source: J.4.7, printed p.443.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.ParabolicFamily
open Centralizers.Choices
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}
  (p : Plane d) (s : SourceChoice p) (B5 : Sylow 5 d.toTypeRuSetup.H)
  (hi : ∀ a ∈ B5Image B5, s.v*a*s.v⁻¹=a⁻¹)
include s hi

/-- The original inverse image of the quotient five-normalizer is F₁Q. -/
theorem preimage_fiveNormalizer :
    (normalizer (B5.map d.ru2.quotientMap : Set S5)).comap d.ru2.quotientMap =
      (p.F₁ B5 ⊔ d.toTypeRuSetup.Q).subgroupOf d.toTypeRuSetup.H := by
  rw [← s.F₁_image p B5 hi, comap_map_eq, d.ru2.quotient_kernel,
    subgroupOf_sup (p.F₁_le_H B5) (pCoreIn_le 2 _)]

/-- Index two is used with the original endpoint inside its original product with Q. -/
theorem first_normal_in_product :
    ((p.F₁ B5).subgroupOf (p.F₁ B5 ⊔ d.toTypeRuSetup.Q)).Normal :=
  normal_of_index_eq_two (s.F₁_relIndex_sup_Q p B5 hi)

/-- The actual centralizer-normalizer is exactly F₁Q. -/
theorem first_relative_normalizer :
    d.toTypeRuSetup.H ⊓ normalizer (p.F₁ B5 : Set G) = p.F₁ B5 ⊔ d.toTypeRuSetup.Q := by
  have hnorm : p.F₁ B5 ⊔ d.toTypeRuSetup.Q ≤ normalizer (p.F₁ B5 : Set G) :=
    (normal_subgroupOf_iff_le_normalizer le_sup_left).mp (first_normal_in_product p s B5 hi)
  apply le_antisymm
  · rintro x ⟨hxH, hxN⟩
    let xH : d.toTypeRuSetup.H := ⟨x, hxH⟩
    have hxNH : xH ∈ normalizer ((p.F₁ B5).subgroupOf d.toTypeRuSetup.H : Set d.toTypeRuSetup.H) := by
      rw [← subgroupOf_normalizer_eq (p.F₁_le_H B5)]
      exact hxN
    have hxIm := ((p.F₁ B5).subgroupOf d.toTypeRuSetup.H).le_normalizer_map
      d.ru2.quotientMap (mem_map_of_mem d.ru2.quotientMap hxNH)
    rw [s.F₁_image p B5 hi] at hxIm
    have he := (B5.mapSurjective d.ru2.quotient_surjective).normalizer_normalizer
    change normalizer (normalizer (B5.map d.ru2.quotientMap : Set S5) : Set S5) =
      normalizer (B5.map d.ru2.quotientMap : Set S5) at he
    rw [he] at hxIm
    have hxpre : xH ∈ (normalizer (B5.map d.ru2.quotientMap : Set S5)).comap
        d.ru2.quotientMap := hxIm
    rw [preimage_fiveNormalizer p s B5 hi] at hxpre
    exact hxpre
  · exact le_inf (sup_le (p.F₁_le_H B5) (pCoreIn_le 2 _)) hnorm

/-- Squaring in the original product lands in the original index-two endpoint. -/
theorem square_mem_first {x : G} (hx : x ∈ p.F₁ B5 ⊔ d.toTypeRuSetup.Q) :
    x^2 ∈ p.F₁ B5 := by
  let : ((p.F₁ B5).subgroupOf (p.F₁ B5 ⊔ d.toTypeRuSetup.Q)).Normal :=
    first_normal_in_product p s B5 hi
  have hh := ((p.F₁ B5).subgroupOf (p.F₁ B5 ⊔ d.toTypeRuSetup.Q)).pow_index_mem ⟨x, hx⟩
  change x ^ (p.F₁ B5).relIndex (p.F₁ B5 ⊔ d.toTypeRuSetup.Q) ∈ p.F₁ B5 at hh
  rwa [s.F₁_relIndex_sup_Q p B5 hi] at hh

/-- Any original order-five subgroup with the matching quotient image lies
in F₁, including distinct lifts of the same quotient pentagon. -/
theorem five_le_first_of_image (B : Subgroup G) (hB : B ≤ d.toTypeRuSetup.H)
    (hc : Nat.card B = 5)
    (himage : (B.subgroupOf d.toTypeRuSetup.H).map d.ru2.quotientMap ≤
      B5.map d.ru2.quotientMap) : B ≤ p.F₁ B5 := by
  intro b hb
  let bH : d.toTypeRuSetup.H := ⟨b, hB hb⟩
  have him : d.ru2.quotientMap bH ∈ normalizer (B5.map d.ru2.quotientMap : Set S5) :=
    (B5.map d.ru2.quotientMap).le_normalizer (himage (mem_map_of_mem _ hb))
  have hpre : b ∈ p.F₁ B5 ⊔ d.toTypeRuSetup.Q := by
    have hh : bH ∈ (normalizer (B5.map d.ru2.quotientMap : Set S5)).comap
        d.ru2.quotientMap := him
    rw [preimage_fiveNormalizer p s B5 hi] at hh
    exact hh
  have hb2 := square_mem_first p s B5 hi hpre
  have hb5 : b^5 = 1 := by
    have hh := congrArg Subtype.val (pow_card_eq_one' (x := (⟨b, hb⟩ : B)))
    simpa only [hc, coe_pow, coe_one] using hh
  have hb6 := (p.F₁ B5).pow_mem hb2 3
  have he : (b^2)^3 = b := by rw [← pow_mul, show 2*3=5+1 by rfl, pow_succ, hb5, one_mul]
  exact he ▸ hb6

end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.ParabolicFamily
