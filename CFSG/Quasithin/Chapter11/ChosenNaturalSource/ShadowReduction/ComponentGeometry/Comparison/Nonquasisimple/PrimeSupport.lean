module
public import CFSG.Quasithin.Chapter3.Section02.RadicalCentralization.ChosenStars.SinglePrime
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Nonquasisimple.Frattini.Catalogue.Fitting

/-!
# Prime support of the actual nonquasisimple Fitting quotient

The kernel of an elementary-plane extension of odd SL₂ is its literal
Fitting subgroup. Its order therefore discharges the prime-power premise
of the complete single-prime radical-centralization theorem.

The finite odd-order dichotomy records the precise remaining case: at
least two distinct odd primes. The chosen-flag comparison uses it after
excluding every other catalogue row; the same owner retains that branch.
Source: Aschbacher--Smith, 1.3.8, pp.512--514; 11.4.2, p.777.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison
open Chapter1.Section02.LocalModels
variable {A : Type*} [Group A] [Finite A]

/-- The actual elementary extension has prime-power Fitting subgroup in
its literal two-core quotient. No action marking or splitting is used. -/
theorem fitting_isPGroup_of_elementary_extension {p : ℕ} [Fact p.Prime]
    (hp : 3 < p)
    (hm : HasExtension (A ⧸ pCore 2 A) (ElementaryModel p 2)
      (fun Q _ => Source.IsSL Q 2 p)) :
    IsPGroup p (fittingSubgroup (A ⧸ pCore 2 A)) := by
  obtain ⟨N,hN,⟨e⟩,hmodel⟩ := hm
  let : N.Normal := hN
  have hcard : Nat.card N = p ^ 2 := by
    rw [Nat.card_congr e.toEquiv]
    simp [Nat.card_eq_fintype_card]
  have hP : IsPGroup p N := IsPGroup.of_card hcard
  let : Group.IsNilpotent N := hP.isNilpotent
  rw [Frattini.fitting_eq_extension_kernel (pCore_quotient_pCore_eq_bot 2) N hp
    ((Fact.out : p.Prime).odd_of_ne_two (by omega)) hmodel]
  exact hP

/-- Every finite odd-order group is a prime-power group, or its order has
two distinct odd prime divisors. -/
theorem primePower_or_two_odd_primes (ho : Odd (Nat.card A)) :
    (∃ p : ℕ, p.Prime ∧ IsPGroup p A) ∨
      ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ Odd p ∧ Odd q ∧ p ≠ q ∧
        p ∣ Nat.card A ∧ q ∣ Nat.card A := by
  by_cases ht : Nat.card A = 1
  · exact Or.inl ⟨2,Nat.prime_two,IsPGroup.of_card (n := 0) (by simpa using ht)⟩
  obtain ⟨p,hp,hd⟩ := Nat.exists_prime_and_dvd ht
  by_cases hs : ∀ q : ℕ, q.Prime → q ∣ Nat.card A → q = p
  · left
    refine ⟨p,hp,?_⟩
    apply (isPGroup_iff_primeFactors_card_subset hp.ne_zero).mpr
    intro q hq
    obtain ⟨hq,hdq,_⟩ := Nat.mem_primeFactors.mp hq
    rw [hs q hq hdq]
    exact hp.mem_primeFactors_self
  · push Not at hs
    obtain ⟨q,hq,hdq,hne⟩ := hs
    exact Or.inr ⟨p,q,hp,hq,ho.of_dvd_nat hd,ho.of_dvd_nat hdq,Ne.symm hne,hd,hdq⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison
