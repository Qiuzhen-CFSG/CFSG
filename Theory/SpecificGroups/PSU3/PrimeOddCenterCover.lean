module

public import Theory.SpecificGroups.PSU3.UniversalCover.OddPartDescent
public import Theory.SpecificGroups.PSU3.UniversalCover.OddKernelBound.OddCrossCharacteristic
public import Theory.SpecificGroups.PSU3.UniversalCover.OddKernelBound.OddCrossCharacteristic.SplitTorus
public import Theory.SpecificGroups.PSU3.UniversalCover.OddKernelBound.OddCrossCharacteristic.ThreeTorus.Matrix
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCore

/-!
# Odd-center covers of prime-field projective unitary groups

The defining-prime transfer, split and nonsplit torus calculations discharge
all odd-primary inputs to scalar-cover descent at an odd prime fixed-field
order. Kernel comparison then recognizes every nontrivial odd-center
quasisimple cover as the actual SU₃ group, preserving its projective marking.

Source: Aschbacher–Smith A.2.12(I), printed pp.36–37; I.1.3(2), p.407.
The coefficient field has order p² and its stored involution is x ↦ xᵖ.
-/

public section

open Subgroup Theory.GroupTheory PerfectCentralCovering
open BenderSuzuki.MatrixGroups
namespace BenderSuzuki.MatrixGroups.HermitianForm.PrimeOddCenterCover
open UniversalCover OddKernelBound.OddCrossCharacteristic
universe u v
variable {F : Type u} [Field F] [Finite F] (J : HermitianForm 3 F)
variable {L : Type v} [Group L] [Finite L] [IsQuasisimple L]

private theorem twoCore_eq_bot (ho : Odd (Nat.card (center L))) :
    pCore 2 L = ⊥ := by
  obtain ⟨k, hk⟩ := (pCore_isPGroup (p := 2) (G := L)).exists_card_eq
  have hd := card_dvd_of_le (IsQuasisimple.pCore_le_center (G := L) 2)
  have hk0 : k = 0 := by
    by_contra hk0
    exact ho.not_two_dvd_nat ((dvd_pow_self 2 hk0).trans (hk ▸ hd))
  exact (pCore 2 L).eq_bot_of_card_eq (by simpa [hk0] using hk)

/-- The genuine scalar-cover lift at every odd prime fixed-field order. -/
theorem exists_scalar_lift {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcard : Nat.card F = p ^ 2) (hc : ∀ x, J.conj x = x ^ p)
    (e : L ⧸ center L ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (ho : Odd (Nat.card (center L))) :
    ∃ k : J.specialSubgroup →* L, Function.Surjective k ∧
      (centralQuotientCover e).toMonoidHom.comp k = J.specialToProjective := by
  have hpgt : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp2)
  let := projective_isQuasisimple J hpgt hcard hc
  apply OddPartDescent.exists_lift_odd J (e := 1) hp hp2 (by decide) (by decide)
    (by simpa only [pow_one] using hcard) (by simpa only [pow_one] using hc)
    (by omega) _ _ (centralQuotientCover e).toMonoidHom
    (centralQuotientCover e).surjective (twoCore_eq_bot ho)
  · intro r hr hr2 hr3 hrp
    by_cases hd : r ∣ p + 1
    · exact SplitTorus.not_dvd_kernel_of_dvd_add_one J hr hr2 hr3 hd hcard hc
        (universalCover _)
    · exact not_dvd_kernel_of_not_dvd_add_one J (e := 1) hp (by decide) hr hr2 hr3 hrp
        (by simpa only [pow_one] using hcard) (by simpa only [pow_one] using hc)
        (by simpa only [pow_one] using hd) (universalCover _)
  · intro hm
    exact OddThreeMatrix.not_nine_dvd_kernel J hcard hc
      (by simpa only [pow_one] using hm) (universalCover _)

/-- The center bound for the original odd-prime unitary cover. -/
theorem center_card_dvd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcard : Nat.card F = p ^ 2) (hc : ∀ x, J.conj x = x ^ p)
    (e : L ⧸ center L ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (ho : Odd (Nat.card (center L))) :
    Nat.card (center L) ∣ Nat.gcd 3 (p + 1) := by
  obtain ⟨k, hks, hk⟩ := exists_scalar_lift J hp hp2 hcard hc e ho
  have hd := kernel_card_dvd_of_surjective_factor J.specialToProjective
    (centralQuotientCover e).toMonoidHom k hks hk
  simpa only [centralQuotientCover_ker, card_kernel J hcard hc] using hd

/-- A nontrivial odd-center cover is SU₃(p), with scalar center of order three. -/
theorem nontrivial_center_recognition {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcard : Nat.card F = p ^ 2) (hc : ∀ x, J.conj x = x ^ p)
    (e : L ⧸ center L ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (ho : Odd (Nat.card (center L))) (hz : center L ≠ ⊥) :
    p % 3 = 2 ∧ Nat.card (center L) = 3 ∧
      Nonempty (center L ≃* Multiplicative (ZMod 3)) ∧
      ∃ j : J.specialSubgroup ≃* L,
        (centralQuotientCover e).toMonoidHom.comp j.toMonoidHom = J.specialToProjective := by
  have hd := center_card_dvd J hp hp2 hcard hc e ho
  have h3 : Nat.card (center L) = 3 := by
    rcases Nat.prime_three.eq_one_or_self_of_dvd _
      (hd.trans (Nat.gcd_dvd_left 3 (p + 1))) with h1 | h3
    · exact (hz ((center L).eq_bot_of_card_eq h1)).elim
    · exact h3
  have hg : Nat.gcd 3 (p + 1) = 3 := Nat.dvd_antisymm (Nat.gcd_dvd_left _ _) (h3 ▸ hd)
  have hm : p % 3 = 2 := by
    have hd3 : 3 ∣ p + 1 := hg ▸ Nat.gcd_dvd_right 3 (p + 1)
    have := Nat.mod_eq_zero_of_dvd hd3
    omega
  obtain ⟨k, hks, hk⟩ := exists_scalar_lift J hp hp2 hcard hc e ho
  have hcount := kernel_card_eq_mul_of_surjective_factor J.specialToProjective
    (centralQuotientCover e).toMonoidHom k (centralQuotientCover e).surjective hks hk
  have hker : Nat.card k.ker = 1 := by
    rw [card_kernel J hcard hc, hg, centralQuotientCover_ker, h3] at hcount
    omega
  let j : J.specialSubgroup ≃* L := MulEquiv.ofBijective k
    ⟨k.ker_eq_bot_iff.mp (k.ker.eq_bot_of_card_eq hker), hks⟩
  exact ⟨hm, h3, ⟨mulEquivOfPrimeCardEq h3 (by simp)⟩, j, hk⟩

end BenderSuzuki.MatrixGroups.HermitianForm.PrimeOddCenterCover
