module
public import CFSG.Quasithin.Chapter16.Section04To05.IntersectionStructure.RankResidual.EvenParameter.Orders
public import CFSG.Quasithin.Chapter16.Section01To02.SourceHypothesis
public import Theory.Mathieu.M12.Properties.Order
public import Theory.Mathieu.M22.Properties.Order
public import Theory.Mathieu.M24.Properties.Order
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizerIndex.CarrierOrder
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.Order

/-!
# The fixed-order sporadics in the E2 comparison

The signed projective-three order bounds exclude M₁₁, M₁₂, M₂₂, M₂₃,
M₂₄, J₂ and HS using proved orders of the exact carriers in E2.
The J₂ carrier here is the native permutation group, not the separate
icosian construction. J₄ and Ru remain explicit alternatives; no conditional
order certification for either group is used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E2(iii),
p.1170, and the proof of Lemma 16.4.5, p.1184.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.EvenParameter
open Chapter1.Section02.LocalModels ClassificationModels Sporadic.Mathieu
variable {S : Type*} [Group S] {unitary : Bool} {q : ℕ}

/-- Seven exact sporadic carrier orders are incompatible with the supplied signed model. -/
theorem sporadic_remaining (he : IsEvenTypeSporadicQuotient S)
    (hm : IsPSLSign S unitary 3 q) (hc : q % 3 = if unitary then 2 else 1) :
    Nonempty (S ≃* Janko4.Model) ∨ Nonempty (S ≃* Rudvalis.Model) := by
  obtain ⟨name, hj3, hhe, ⟨e⟩⟩ := he
  have hcard := Nat.card_congr e.toEquiv
  cases name with
  | m11 =>
    change Nat.card S = Nat.card M11 at hcard
    rw [m11_order] at hcard
    exact (not_card_in_gap hm hc (N := 3) (c := 7920) (by norm_num) (by norm_num) hcard).elim
  | m12 =>
    change Nat.card S = Nat.card M12 at hcard
    rw [m12_order] at hcard
    exact (not_card_in_gap hm hc (N := 4) (c := 95040) (by norm_num) (by norm_num) hcard).elim
  | m22 =>
    change Nat.card S = Nat.card M22 at hcard
    rw [m22_order] at hcard
    exact (not_card_in_gap hm hc (N := 5) (c := 443520) (by norm_num) (by norm_num) hcard).elim
  | m23 =>
    change Nat.card S = Nat.card M23 at hcard
    rw [m23_order] at hcard
    exact (not_card_in_gap hm hc (N := 8) (c := 10200960) (by norm_num) (by norm_num) hcard).elim
  | m24 =>
    change Nat.card S = Nat.card M24 at hcard
    rw [m24_order] at hcard
    exact (not_card_in_gap hm hc (N := 12) (c := 244823040) (by norm_num) (by norm_num) hcard).elim
  | j2 =>
    change Nat.card S = Nat.card Sporadic.LeechRelated.J2.Carrier at hcard
    rw [Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier] at hcard
    exact (not_card_in_gap hm hc (N := 6) (c := 604800) (by norm_num) (by norm_num) hcard).elim
  | hs =>
    change Nat.card S = Nat.card Sporadic.LeechRelated.HS.Carrier at hcard
    rw [Sporadic.LeechRelated.HS.NormalizerIndex.card_carrier] at hcard
    exact (not_card_in_gap hm hc (N := 10) (c := 44352000) (by norm_num) (by norm_num) hcard).elim
  | j3 => exact (hj3 rfl).elim
  | he => exact (hhe rfl).elim
  | j4 => exact Or.inl ⟨e⟩
  | ru => exact Or.inr ⟨e⟩

end CFSG.Quasithin.Chapter16.Intersections.EvenParameter
