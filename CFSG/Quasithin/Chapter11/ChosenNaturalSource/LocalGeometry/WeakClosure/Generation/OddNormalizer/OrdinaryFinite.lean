module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.OrdinaryModels
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.OrderBound

/-!
# Five finite ordinary rows excluded by the full covering order

Below the HS order, the only possible nonbinary natural quotient orders
are those of SL₃(4), SL₃(8) and Sp₄(4). Larger fields and G₂ exceed the
bound. None of these three orders divides the orders of M₁₁, M₁₂, M₂₂,
M₂₃ or HS. Projection through the ordinary component has only a two-group
kernel, so the full source quotient order divides its central quotient
order. In particular the cubic center of SL₃(4) is not discarded.

ResidualCases applies the exclusions to the original covering pair, and
Source to the literal Hall kernel. Source: Aschbacher--Smith C.3.1--5,
pp.149--150, and 4.4.6, p.620.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
include D S
private theorem quotient_order_not_dvd_small
    (n : ℕ) (hn : 0 < n) (hbound : n ≤ 44352000)
    (h4 : ¬60480 ∣ n) (h8 : ¬16482816 ∣ n) (hs : ¬979200 ∣ n) :
    ¬ Nat.card (L ⧸ pCore 2 L) ∣ n := by
  intro hd
  have hb : Nat.card (L ⧸ pCore 2 L) ≤ 44352000 := (Nat.le_of_dvd hn hd).trans hbound
  have hq : 4 ≤ Nat.card S.field.Carrier := by
    rw [S.field.card_eq]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) S.nonbinary
  cases S.natural with
  | sl3 hm =>
    rw [Nat.card_congr hm.some.groupEquiv.toEquiv,linear_three_order] at hd hb
    have hf : S.field.degree ≤ 3 := by
      by_contra! hf
      have hq' : 16 ≤ Nat.card S.field.Carrier := by
        rw [S.field.card_eq]
        exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 4 ≤ S.field.degree)
      have hl := Nat.mul_le_mul
        (Nat.mul_le_mul (Nat.pow_le_pow_left hq' 3)
          (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq' 3) 1))
        (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq' 2) 1)
      norm_num at hl
      omega
    have hf23 : S.field.degree = 2 ∨ S.field.degree = 3 := by have := S.nonbinary; omega
    rcases hf23 with hf | hf
    · exact h4 (by simpa [S.field.card_eq,hf] using hd)
    · exact h8 (by simpa [S.field.card_eq,hf] using hd)
  | sp4 hm =>
    rw [Nat.card_congr hm.some.groupEquiv.toEquiv,
      Theory.SpecificGroups.SymplecticFour.card_sp] at hd hb
    have hf : S.field.degree = 2 := by
      by_contra hf
      have hq' : 8 ≤ Nat.card S.field.Carrier := by
        rw [S.field.card_eq]
        exact Nat.pow_le_pow_right (by decide : 0 < 2) (by have := S.nonbinary; omega : 3 ≤ S.field.degree)
      have hl := Nat.mul_le_mul
        (Nat.mul_le_mul (Nat.pow_le_pow_left hq' 4)
          (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq' 2) 1))
        (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq' 4) 1)
      norm_num at hl
      omega
    exact hs (by simpa [S.field.card_eq,hf] using hd)
  | g2 hm =>
    rw [Nat.card_congr hm.some.groupEquiv.toEquiv,Atlas.G2.card_Model] at hb
    have hl := Nat.mul_le_mul
      (Nat.mul_le_mul (Nat.pow_le_pow_left hq 6)
        (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 6) 1))
      (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1)
    norm_num at hl
    omega

theorem no_ordinary_natural_small_sporadic {H M B R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (e : (B ⧸ pCore 2 B) ≃* (L ⧸ pCore 2 L))
    (K : Subgroup H) (hK : IsComponent H K)
    (n : ClassificationModels.SporadicName)
    (hn : n = .m11 ∨ n = .m12 ∨ n = .m22 ∨ n = .m23 ∨ n = .hs)
    (ek : K ⧸ center K ≃* n.Carrier) : False := by
  have hd := ordinary_natural_quotient_card_dvd h e K hK
  rw [Nat.card_congr ek.toEquiv] at hd
  rcases hn with rfl | rfl | rfl | rfl | rfl
  · change Nat.card (L ⧸ pCore 2 L) ∣ Nat.card Sporadic.Mathieu.M11 at hd
    rw [Sporadic.Mathieu.m11_order] at hd
    exact quotient_order_not_dvd_small D S _ (by decide) (by decide) (by decide) (by decide) (by decide) hd
  · change Nat.card (L ⧸ pCore 2 L) ∣ Nat.card Sporadic.Mathieu.M12 at hd
    rw [Sporadic.Mathieu.m12_order] at hd
    exact quotient_order_not_dvd_small D S _ (by decide) (by decide) (by decide) (by decide) (by decide) hd
  · change Nat.card (L ⧸ pCore 2 L) ∣ Nat.card Sporadic.Mathieu.M22 at hd
    rw [Sporadic.Mathieu.m22_order] at hd
    exact quotient_order_not_dvd_small D S _ (by decide) (by decide) (by decide) (by decide) (by decide) hd
  · change Nat.card (L ⧸ pCore 2 L) ∣ Nat.card Sporadic.Mathieu.M23 at hd
    rw [Sporadic.Mathieu.m23_order] at hd
    exact quotient_order_not_dvd_small D S _ (by decide) (by decide) (by decide) (by decide) (by decide) hd
  · have hd' := hd.trans Sporadic.LeechRelated.HS.card_carrier_dvd
    exact quotient_order_not_dvd_small D S _ (by decide) (by decide) (by decide) (by decide) (by decide) hd'
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
