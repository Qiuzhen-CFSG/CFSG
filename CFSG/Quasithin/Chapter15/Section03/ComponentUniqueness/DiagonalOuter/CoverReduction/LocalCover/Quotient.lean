module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.LocalCover.Algebra
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.QuotientCoordinates

/-!
# The order-nine quotient in the diagonal branch

Multiplication from Y_L and the cyclic order-three supplement bounds the
order of Y₊. Relative normality puts O₂(Y_L) inside O₂(Y₊), so the Borel
calculation |Y_L/O₂(Y_L)|=3 bounds |Y₊/O₂(Y₊)| by nine. This excludes the
extraspecial alternative in 15.3.11(5); the elementary alternative constructs
an actual multiplicative equivalence with E₉.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
proof of 15.3.38, printed pp.1135--1136.
-/

public section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover
variable {G : Type*} [Group G] [Finite G]

theorem quotient_card_le_nine_of_cyclic_supplement {Y A : Subgroup G} {y : G}
    (hAY : A ≤ Y) (hYA : Y ≤ normalizer (A : Set G))
    (hyY : y ∈ Y) (hy : orderOf y = 3)
    (hprod : (Y : Set G) = (A : Set G) * (zpowers y : Set G))
    (hA : Nat.card (A ⧸ pCore 2 A) = 3) :
    Nat.card (Y ⧸ pCore 2 Y) ≤ 9 := by
  let f : A × zpowers y → Y := fun a =>
    ⟨a.1 * a.2, Y.mul_mem (hAY a.1.property) ((zpowers_le.mpr hyY) a.2.property)⟩
  have hf : Function.Surjective f := by
    intro z
    have hz : (z : G) ∈ (A : Set G) * (zpowers y : Set G) := hprod ▸ z.property
    obtain ⟨a, ha, b, hb, hab⟩ := hz
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
  have hcard := Nat.card_le_card_of_surjective f hf
  rw [Nat.card_prod, Nat.card_zpowers, hy] at hcard
  have hc : Nat.card (pCore 2 A) ≤ Nat.card (pCore 2 Y) := by
    have h := card_le_of_le (pCoreIn_mono_of_normalizes (p := 2) hAY hYA)
    rw [pCoreIn, pCoreIn, card_map_of_injective A.subtype_injective,
      card_map_of_injective Y.subtype_injective] at h
    exact h
  have hYAcard := (pCore 2 Y).card_mul_index
  have hAAcard := (pCore 2 A).card_mul_index
  rw [index_eq_card] at hYAcard hAAcard
  rw [hA] at hAAcard
  have hpos : 0 < Nat.card (pCore 2 Y) := Nat.card_pos
  nlinarith

/-- The cyclic supplement in 15.3.37 excludes the extraspecial branch of
15.3.11(5) once the Borel calculation gives |Y_L/O₂(Y_L)|=3. -/
theorem elementary_nine_of_diagonal_product {Y L L₀ : Subgroup G}
    (hYL : Y ≤ normalizer (L : Set G))
    (hdiag : Candidates.RankTwoDiagonal Y L L₀)
    (hA : Nat.card (componentPart Y L ⧸ pCore 2 (componentPart Y L)) = 3)
    (hquot : (IsElementaryAbelian 3 (Y ⧸ pCore 2 Y) ∧
        Nat.card (Y ⧸ pCore 2 Y) = 9) ∨ Nat.card (Y ⧸ pCore 2 Y) = 27) :
    IsElementaryAbelian 3 (Y ⧸ pCore 2 Y) ∧
      Nat.card (Y ⧸ pCore 2 Y) = 9 ∧
      Nonempty ((Y ⧸ pCore 2 Y) ≃* Multiplicative (Fin 2 → ZMod 3)) := by
  obtain ⟨_, _, y, hyY, hy, hprod, _⟩ := hdiag
  have hbound := quotient_card_le_nine_of_cyclic_supplement
    ((map_subtype_le _).trans inf_le_left)
    (ComponentIntersection.normalizes_intersectionResidual hYL) hyY hy hprod hA
  rcases hquot with ⟨he, hc⟩ | hc
  · let := he
    exact ⟨he, hc, ComponentIntersection.quotient_equiv_elementaryNine_of_card hc
      (IsElementaryAbelian.exponent_dvd_p 3 _)⟩
  · omega

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover
