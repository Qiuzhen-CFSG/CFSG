module

public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.Parameters
public import Theory.Mathieu.M11.Properties.Order
public import Theory.Mathieu.M12.Properties.Order
public import Theory.Mathieu.M22.Properties.Order
public import Theory.Mathieu.M23.Properties.Order
public import Theory.Mathieu.M24.Properties.Order
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.Order
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizerIndex.CarrierOrder
public import Theory.SpecificGroups.Janko4.Model.Cardinality.Thompson
public import Theory.SpecificGroups.SporadicTrivialMultipliers.OddPrimary.HeldBounds
public import Theory.SpecificGroups.Held.TwoPartDivisibility
public import Theory.SpecificGroups.Rudvalis.Model.Order

/-!
# The sporadic order sieve for the actual faithful Sylow action

A binary PSL₂ subgroup has order 2ⁿ(2²ⁿ−1). Its order must divide the order
of the containing group, while the full ambient Sylow subgroup acting
faithfully on it has order dividing 2ⁿn. Certified sporadic orders make
these conditions incompatible for every noncubic n. For Held it suffices
to use the proved ambient order-divisor and the certified lower two-part;
no exact Held order is assumed. The M₂₂ triple cover has order three times
its central quotient and satisfies the same obstruction.

The complete ten-name Theorem C sporadic catalogue is retained. J₃ is
excluded by that catalogue itself, and J₁ is a separate source family.
Source: Aschbacher–Smith C.5.13, printed pp.162–163.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
open ClassificationModels Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

private def orderBound : SporadicName → ℕ
  | .m11 => 7920
  | .m12 => 95040
  | .m22 => 443520
  | .m23 => 10200960
  | .m24 => 244823040
  | .j2 => 604800
  | .j3 => 1
  | .j4 => 86775571046077562880
  | .hs => 44352000
  | .he => 16121548800
  | .ru => 145926144000

private def upperTwoExponent : SporadicName → ℕ
  | .m11 => 4
  | .m12 => 6
  | .m22 => 7
  | .m23 => 7
  | .m24 => 10
  | .j2 => 7
  | .j3 => 0
  | .j4 => 21
  | .hs => 9
  | .he => 12
  | .ru => 14

private def lowerTwoExponent : SporadicName → ℕ
  | .m11 => 4
  | .m12 => 6
  | .m22 => 7
  | .m23 => 7
  | .m24 => 10
  | .j2 => 7
  | .j3 => 0
  | .j4 => 21
  | .hs => 9
  | .he => 10
  | .ru => 14

private theorem sporadic_order_bounds (name : SporadicName) (hne : name ≠ .j3) :
    Nat.card name.Carrier ∣ orderBound name ∧
      2 ^ lowerTwoExponent name ∣ Nat.card name.Carrier := by
  cases name with
  | m11 =>
      change Nat.card Sporadic.Mathieu.M11 ∣ 7920 ∧ 2^4 ∣ Nat.card Sporadic.Mathieu.M11
      rw [Sporadic.Mathieu.m11_order]
      norm_num
  | m12 =>
      change Nat.card Sporadic.Mathieu.M12 ∣ 95040 ∧ 2^6 ∣ Nat.card Sporadic.Mathieu.M12
      rw [Sporadic.Mathieu.m12_order]
      norm_num
  | m22 =>
      change Nat.card Sporadic.Mathieu.M22 ∣ 443520 ∧ 2^7 ∣ Nat.card Sporadic.Mathieu.M22
      rw [Sporadic.Mathieu.m22_order]
      norm_num
  | m23 =>
      change Nat.card Sporadic.Mathieu.M23 ∣ 10200960 ∧ 2^7 ∣ Nat.card Sporadic.Mathieu.M23
      rw [Sporadic.Mathieu.m23_order]
      norm_num
  | m24 =>
      change Nat.card Sporadic.Mathieu.M24 ∣ 244823040 ∧ 2^10 ∣ Nat.card Sporadic.Mathieu.M24
      rw [Sporadic.Mathieu.m24_order]
      norm_num
  | j2 =>
      change Nat.card Sporadic.LeechRelated.J2.Carrier ∣ 604800 ∧ 2^7 ∣ Nat.card Sporadic.LeechRelated.J2.Carrier
      rw [Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier]
      norm_num
  | j3 =>
      exact (hne rfl).elim
  | j4 =>
      change Nat.card Janko4.Model ∣ 86775571046077562880 ∧ 2^21 ∣ Nat.card Janko4.Model
      rw [Janko4.Cardinality.Thompson.model_card]
      norm_num
  | hs =>
      change Nat.card Sporadic.LeechRelated.HS.Carrier ∣ 44352000 ∧ 2^9 ∣ Nat.card Sporadic.LeechRelated.HS.Carrier
      rw [Sporadic.LeechRelated.HS.NormalizerIndex.card_carrier]
      norm_num
  | he =>
      exact ⟨Held.OddPrimary.card_dvd, Held.two_pow_ten_dvd_card⟩
  | ru =>
      change Nat.card Rudvalis.Model ∣ 145926144000 ∧ 2^14 ∣ Nat.card Rudvalis.Model
      rw [Rudvalis.model_card]
      norm_num

private theorem sporadic_order_upper (name : SporadicName) :
    ¬ 2 ^ (upperTwoExponent name + 1) ∣ orderBound name := by
  cases name <;> norm_num [upperTwoExponent, orderBound]

private theorem sporadic_order_sieve (name : SporadicName)
    (n : ℕ) (hn : 1 < n) (hu : n ≤ upperTwoExponent name)
    (hc : 2^n * ((2^n)^2 - 1) ∣ orderBound name) :
    ¬ 2 ^ lowerTwoExponent name ∣ 2^n*n := by
  intro hs
  have hd := And.intro hc hs
  cases name <;> simp only [upperTwoExponent, lowerTwoExponent, orderBound] at hu hd
  all_goals interval_cases n <;> norm_num at hd

private theorem not_containing_of_order_sieve
    (Q : Sylow 2 G) (B D : Subgroup G) (hBD : B ≤ D) {n c k m : ℕ}
    (hn : 1 < n) (hB : ClassicalGroup.IsPSL B 2 (2^n))
    (hQB : (Q : Subgroup G) ≤ normalizer (B : Set G))
    (hfaith : (Q : Subgroup G) ⊓ centralizer (B : Set G) = ⊥)
    (hc : Nat.card D ∣ c) (hl : 2^m ∣ Nat.card D)
    (hupper : ¬ 2^(k+1) ∣ c)
    (hsieve : ∀ n, 1 < n → n ≤ k → 2^n*((2^n)^2-1) ∣ c → ¬ 2^m ∣ 2^n*n) :
    False := by
  have hbc : 2^n*((2^n)^2-1) ∣ c := by
    rw [← binary_card hB]
    exact (card_dvd_of_le hBD).trans hc
  have hnk : n ≤ k := by
    by_contra! hh
    exact hupper ((pow_dvd_pow 2 hh).trans ((dvd_mul_right _ _).trans hbc))
  have hq : 2^m ∣ Nat.card Q :=
    Q.pow_dvd_card_of_pow_dvd_card (hl.trans D.card_subgroup_dvd_card)
  exact hsieve n hn hnk hbc
    (hq.trans (binary_normalizer_card_dvd Q B (by omega) hB hQB hfaith))

/-- Every actual Theorem C sporadic containing model contradicts the
faithful full-Sylow action on the noncubic binary block. -/
theorem not_sporadic_containing
    (Q : Sylow 2 G) (B D : Subgroup G) (hBD : B ≤ D) {n : ℕ}
    (hn : 1 < n) (hB : ClassicalGroup.IsPSL B 2 (2^n))
    (hQB : (Q : Subgroup G) ≤ normalizer (B : Set G))
    (hfaith : (Q : Subgroup G) ⊓ centralizer (B : Set G) = ⊥)
    (name : SporadicName) (hne : name ≠ .j3) :
    ¬ Nonempty (D ≃* name.Carrier) := by
  rintro ⟨e⟩
  obtain ⟨hc, hl⟩ := sporadic_order_bounds name hne
  rw [← Nat.card_congr e.toEquiv] at hc hl
  exact not_containing_of_order_sieve Q B D hBD hn hB hQB hfaith hc hl
    (sporadic_order_upper name) (sporadic_order_sieve name)

/-- The central quotient and center supplied by the genuine triple-cover
predicate give its exact order; no comparison with a chosen cover is needed. -/
theorem not_mathieu_twentyTwo_cover_containing
    (Q : Sylow 2 G) (B D : Subgroup G) (hBD : B ≤ D) {n : ℕ}
    (hn : 1 < n) (hB : ClassicalGroup.IsPSL B 2 (2^n))
    (hQB : (Q : Subgroup G) ≤ normalizer (B : Set G))
    (hfaith : (Q : Subgroup G) ⊓ centralizer (B : Set G) = ⊥) :
    ¬ IsM22Cover D := by
  rintro ⟨_hq, ⟨ec⟩, ⟨eq⟩⟩
  have hcenter : Nat.card (center D) = 3 := by
    rw [Nat.card_congr ec.toEquiv]
    simp
  have hcard : Nat.card D = 1330560 := by
    have h := (center D).card_mul_index
    rw [hcenter, Subgroup.index_eq_card, Nat.card_congr eq.toEquiv,
      Sporadic.Mathieu.m22_order] at h
    exact h.symm
  apply not_containing_of_order_sieve Q B D hBD hn hB hQB hfaith
    (c := 1330560) (k := 7) (m := 7)
  · rw [hcard]
  · rw [hcard]; norm_num
  · norm_num
  · intro i hi hu hc hs
    have hd := And.intro hc hs
    interval_cases i <;> norm_num at hd

end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
