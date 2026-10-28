module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.SignedReduction.ModelIntersection.Basic
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order
public import Theory.Representation.SU3.BinaryDegree.ProjectiveOrder
public import Theory.Mathieu.M12.Properties.Order
public import Theory.Mathieu.M22.Properties.Order
public import Theory.Mathieu.M24.Properties.Order
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizerIndex.CarrierOrder
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.Order
public import Theory.SpecificGroups.Janko4.Model.Cardinality
public import Theory.SpecificGroups.Rudvalis.Model.Order
public import Theory.SpecificGroups.Held.OddOrderBound
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups.PairBound
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.SeventeenSylow.Preservation
public import Theory.SpecificGroups.Held.Automorphisms.Normalizer.LowerBound

/-!
# Sporadic carriers do not occur in the signed degree-three intersection

For the source congruence q ≡ ε (mod 3), the scalar denominator in
PSL₃(q) or PSU₃(q) is exactly three. The actual matrix-group order formulas
therefore give 3|S| = q³(q³ − ε)(q² − 1). The unitary calculation first
recovers the fixed field of order q from the prescribed Frobenius involution
on the matrix field of order q².

The proved orders of the five Mathieu carriers, J₂, J₄, HS and Ru lie in
strict gaps between consecutive values of these increasing numerators.
For Held, the checked lower bound and order-divisibility bound force
19 ≤ q ≤ 21, and none of the resulting signed numerators divides three
times the carrier bound. Thus no additional order or simplicity
certification is needed. All comparisons use the literal carriers from
`ClassificationModels.Families`, including the ATLAS J₂ and HS models.

`sporadic_separation` supplies exactly the `hSporadic` premise of
`ModelIntersection.intersection_of_carrier_comparisons`. Its model transport
uses the supplied multiplicative equivalence to the actual simple quotient.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), A.3.18(2)
(printed pp.51--52), the full sporadic list in 1.1.5(3)(f) (pp.501--503),
and its signed-model intersections on pp.1135 and 1139. The imported carrier
order and Held bound modules retain their ATLAS source and certificate
attribution.
-/

open CFSG.Quasithin.Chapter1.Section02.LocalModels
open CFSG.Quasithin.ClassificationModels Theory.GroupTheory
open CFSG.Quasithin.Chapter15.Section03.Candidates.SignedReduction.ModelIntersection
namespace CFSG.Quasithin.Chapter15.Section03.Candidates.SignedReduction.ModelIntersection.SporadicModels
variable {S : Type*} [Group S] {unitary : Bool} {q : ℕ}

def numerator (unitary : Bool) (q : ℕ) : ℕ :=
  q ^ 3 * (if unitary then q ^ 3 + 1 else q ^ 3 - 1) * (q ^ 2 - 1)

theorem card_mul_three (hm : IsPSLSign S unitary 3 q)
    (hmod : q % 3 = (if unitary then 2 else 1)) :
    Nat.card S * 3 = numerator unitary q := by
  cases unitary with
  | false =>
    obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hm
    have h := Matrix.PSL3.LinearThree.card_projective_mul_scalar F
    rw [← Nat.card_congr e.toEquiv, hcard] at h
    have hg : Nat.gcd 3 (q - 1) = 3 := Nat.gcd_eq_left
      (Nat.dvd_of_mod_eq_zero (by simp only [Bool.false_eq_true, ↓reduceIte] at hmod; omega))
    simpa only [hg, numerator, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hpp := signed_parameter_primePower hm
    obtain ⟨p, n, hp, hn, hpn⟩ := (isPrimePow_nat_iff q).mp hpp
    let : Fact p.Prime := ⟨hp⟩
    obtain ⟨F, hF, hfin, J, hcard, hconj, ⟨e⟩⟩ := hm
    have hfixed : Nat.card {x : F // J.conj x = x} = q := by
      rw [← hpn] at hcard hconj ⊢
      exact FiniteField.card_fixed_of_quadratic_frobenius J.conj p n hn hcard hconj
    have hc := Representation.SU3.BinaryDegree.card_projective J hcard hfixed
    rw [← Nat.card_congr e.toEquiv] at hc
    have hd : 3 ∣ q + 1 := Nat.dvd_of_mod_eq_zero (by simp only [↓reduceIte] at hmod; omega)
    rw [Nat.gcd_eq_left hd] at hc
    have hsq : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      simpa [mul_comm] using Nat.sq_sub_sq q 1
    have hdiv : 3 ∣ (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) := by
      rw [hsq]
      exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hd _) _
    rw [hc, Nat.div_mul_cancel hdiv]
    simp only [numerator, ↓reduceIte]
    ring

theorem numerator_mono (unitary : Bool) : Monotone (numerator unitary) := by
  intro a b hab
  cases unitary <;> simp only [numerator, Bool.false_eq_true, ↓reduceIte] <;> gcongr

theorem numerator_lower (unitary : Bool) (q : ℕ) :
    numerator false q ≤ numerator unitary q := by
  cases unitary
  · rfl
  · simp only [numerator, Bool.false_eq_true, ↓reduceIte]
    gcongr
    omega

theorem numerator_upper (unitary : Bool) (q : ℕ) :
    numerator unitary q ≤ numerator true q := by
  cases unitary
  · simp only [numerator, Bool.false_eq_true, ↓reduceIte]
    gcongr
    omega
  · rfl

theorem card_ne_of_gap {a c : ℕ} (hm : IsPSLSign S unitary 3 q)
    (hmod : q % 3 = (if unitary then 2 else 1))
    (ha : numerator true a < 3 * c)
    (hb : 3 * c < numerator false (a + 1)) : Nat.card S ≠ c := by
  intro hc
  have h := card_mul_three hm hmod
  rw [hc, Nat.mul_comm] at h
  by_cases hq : q ≤ a
  · have := (numerator_mono unitary hq).trans (numerator_upper unitary a)
    omega
  · have := (numerator_lower unitary (a + 1)).trans
      (numerator_mono unitary (show a + 1 ≤ q by omega))
    omega

theorem held_separation (hmod : q % 3 = (if unitary then 2 else 1))
    (hm : IsPSLSign Held.He unitary 3 q) : False := by
  have hg := Held.Realization.MarkedConjugacy.Seventeen.permutationGroup_le_preservingGroup
  have hd : Nat.card Held.He ∣ 16121548800 := by
    simpa using Held.OddOrderBound.card_dvd_of_graph_and_pair_bound hg
      (Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups.pairStabilizer_card_dvd hg)
  have hlo := Held.NormalizerBounds.card_lower_bound
  have hhi : Nat.card Held.He ≤ 16121548800 := Nat.le_of_dvd (by decide) hd
  have heq := card_mul_three hm hmod
  have hqlo : 19 ≤ q := by
    by_contra hq
    have hb : numerator unitary q ≤ 10987832088 := calc
      _ ≤ numerator true 18 :=
        (numerator_mono unitary (show q ≤ 18 by omega)).trans
          (numerator_upper unitary 18)
      _ = _ := by norm_num [numerator]
    omega
  have hqhi : q ≤ 21 := by
    by_contra hq
    have hb : 54757350648 ≤ numerator unitary q := calc
      _ = numerator false 22 := by norm_num [numerator]
      _ ≤ _ := (numerator_lower unitary 22).trans
        (numerator_mono unitary (show 22 ≤ q by omega))
    omega
  have hd' : numerator unitary q ∣ 16121548800 * 3 := by
    rw [← heq]
    exact Nat.mul_dvd_mul hd (dvd_refl 3)
  interval_cases q <;> cases unitary <;> norm_num [numerator] at hd'

/-- None of the ten actual carriers in 1.1.5(3)(f) is a signed degree-three
model with the source congruence. This comparison needs no simplicity assumption. -/
public theorem sporadic_carrier_separation (name : SporadicName) (hne : name ≠ .j3)
    (hmod : q % 3 = (if unitary then 2 else 1))
    (hm : IsPSLSign name.Carrier unitary 3 q) : False := by
  cases name with
  | m11 =>
    exact card_ne_of_gap (a := 3) (c := 7920) hm hmod
      (by norm_num [numerator]) (by norm_num [numerator]) Sporadic.Mathieu.m11_order
  | m12 =>
    exact card_ne_of_gap (a := 4) (c := 95040) hm hmod
      (by norm_num [numerator]) (by norm_num [numerator]) Sporadic.Mathieu.m12_order
  | m22 =>
    exact card_ne_of_gap (a := 5) (c := 443520) hm hmod
      (by norm_num [numerator]) (by norm_num [numerator]) Sporadic.Mathieu.m22_order
  | m23 =>
    exact card_ne_of_gap (a := 8) (c := 10200960) hm hmod
      (by norm_num [numerator]) (by norm_num [numerator]) Sporadic.Mathieu.m23_order
  | m24 =>
    exact card_ne_of_gap (a := 12) (c := 244823040) hm hmod
      (by norm_num [numerator]) (by norm_num [numerator]) Sporadic.Mathieu.m24_order
  | j2 =>
    exact card_ne_of_gap (a := 6) (c := 604800) hm hmod
      (by norm_num [numerator]) (by norm_num [numerator])
      Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier
  | j4 =>
    exact card_ne_of_gap (a := 356) (c := 86775571046077562880) hm hmod
      (by norm_num [numerator]) (by norm_num [numerator]) Janko4.Cardinality.model_card
  | hs =>
    exact card_ne_of_gap (a := 10) (c := 44352000) hm hmod
      (by norm_num [numerator]) (by norm_num [numerator])
      Sporadic.LeechRelated.HS.NormalizerIndex.card_carrier
  | ru =>
    exact card_ne_of_gap (a := 28) (c := 145926144000) hm hmod
      (by norm_num [numerator]) (by norm_num [numerator]) Rudvalis.model_card
  | he => exact held_separation hmod hm
  | j3 => exact hne rfl

/-- The exact sporadic comparison premise of the parent model intersection,
transported along the given isomorphism without changing the signed parameter. -/
public theorem sporadic_separation (S : Type*) [Group S] [Finite S]
    [IsQuasisimple S] [IsSimpleGroup S]
    (name : SporadicName) (hne : name ≠ .j3) (e : Nonempty (S ≃* name.Carrier))
    (unitary : Bool) (q : ℕ) (hmod : q % 3 = (if unitary then 2 else 1))
    (hm : IsPSLSign S unitary 3 q) : False := by
  obtain ⟨e⟩ := e
  exact sporadic_carrier_separation name hne hmod (signed_transport hm e.symm)

end CFSG.Quasithin.Chapter15.Section03.Candidates.SignedReduction.ModelIntersection.SporadicModels
