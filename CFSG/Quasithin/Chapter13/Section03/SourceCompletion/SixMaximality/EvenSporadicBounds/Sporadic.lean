module

public import CFSG.Quasithin.ChapterA.Section02.Statements.Models
public import Theory.Mathieu.M12.Properties.Order
public import Theory.Mathieu.M22.Properties.Order
public import Theory.Mathieu.M23.Properties.Order
public import Theory.Mathieu.M24.Properties.Order
public import Theory.SpecificGroups.Janko1.Model.Certification.Order
public import Theory.SpecificGroups.Janko4.Model.Cardinality
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.Order
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizerIndex.CarrierOrder
public import Theory.SpecificGroups.Held.TwoPartDivisibility
public import Theory.SpecificGroups.Rudvalis.Model.Order

/-!
# Sporadic exclusions for the six-maximality argument

An order dividing `|GL₅(2)| = 9999360` excludes M₁₁ and J₁. Every other
sporadic in the literal Theorem C list has order divisible by 64, excluding
it when the two-part has order at most 32. The proof transports the existing
certified carrier orders; for Held the proved two-part divisibility suffices.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Theorem C as listed in A.2.4, applied to 13.3.2.
-/

public section

namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.SixMaximality.EvenSporadicBounds

open ClassificationModels

variable {G : Type*} [Group G]

/-- No permitted named sporadic has both of the source order bounds. -/
theorem sporadicName_excluded (hdiv : Nat.card G ∣ 9999360)
    (hsmall : ¬64 ∣ Nat.card G) (name : SporadicName) (hne : name ≠ .j3)
    (iso : Nonempty (G ≃* name.Carrier)) : False := by
  obtain ⟨e⟩ := iso
  cases name with
  | m11 =>
    have hc : Nat.card G = 7920 :=
      (Nat.card_congr e.toEquiv).trans Sporadic.Mathieu.m11_order
    rw [hc] at hdiv
    exact (by decide : ¬7920 ∣ 9999360) hdiv
  | m12 =>
    apply hsmall
    rw [Nat.card_congr e.toEquiv]
    change 64 ∣ Nat.card Sporadic.Mathieu.M12
    rw [Sporadic.Mathieu.m12_order]
    decide
  | m22 =>
    apply hsmall
    rw [Nat.card_congr e.toEquiv]
    change 64 ∣ Nat.card Sporadic.Mathieu.M22
    rw [Sporadic.Mathieu.m22_order]
    decide
  | m23 =>
    apply hsmall
    rw [Nat.card_congr e.toEquiv]
    change 64 ∣ Nat.card Sporadic.Mathieu.M23
    rw [Sporadic.Mathieu.m23_order]
    decide
  | m24 =>
    apply hsmall
    rw [Nat.card_congr e.toEquiv]
    change 64 ∣ Nat.card Sporadic.Mathieu.M24
    rw [Sporadic.Mathieu.m24_order]
    decide
  | j2 =>
    apply hsmall
    rw [Nat.card_congr e.toEquiv]
    change 64 ∣ Nat.card Sporadic.LeechRelated.J2.Carrier
    rw [Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier]
    decide
  | j3 => exact hne rfl
  | j4 =>
    apply hsmall
    rw [Nat.card_congr e.toEquiv]
    change 64 ∣ Nat.card Janko4.Model
    rw [Janko4.Cardinality.model_card]
    decide
  | hs =>
    apply hsmall
    rw [Nat.card_congr e.toEquiv]
    change 64 ∣ Nat.card Sporadic.LeechRelated.HS.Carrier
    rw [Sporadic.LeechRelated.HS.NormalizerIndex.card_carrier]
    decide
  | he =>
    apply hsmall
    rw [Nat.card_congr e.toEquiv]
    exact (by decide : 64 ∣ 2 ^ 10).trans Held.two_pow_ten_dvd_card
  | ru =>
    apply hsmall
    rw [Nat.card_congr e.toEquiv]
    change 64 ∣ Nat.card Rudvalis.Model
    rw [Rudvalis.model_card]
    decide

/-- J₁ does not have order dividing the binary degree-five linear group. -/
theorem jankoOne_excluded (hdiv : Nat.card G ∣ 9999360)
    (iso : Nonempty (G ≃* Janko1.Model)) : False := by
  obtain ⟨e⟩ := iso
  have hc : Nat.card G = 175560 := (Nat.card_congr e.toEquiv).trans Janko1.card_model
  rw [hc] at hdiv
  exact (by decide : ¬175560 ∣ 9999360) hdiv

/-- The actual sporadic alternative of Theorem C contradicts the source bounds. -/
theorem sporadic_excluded (hdiv : Nat.card G ∣ 9999360)
    (hsmall : ¬64 ∣ Nat.card G)
    (hmodel : ChapterA.Section02.IsTheoremCSporadicModel G) : False := by
  rcases hmodel with ⟨name, hne, iso⟩ | iso
  · exact sporadicName_excluded hdiv hsmall name hne iso
  · exact jankoOne_excluded hdiv iso

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.SixMaximality.EvenSporadicBounds
