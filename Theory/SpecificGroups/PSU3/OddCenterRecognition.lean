module
public import Theory.SpecificGroups.PSU3.UniversalCover.OddPartDescent
public import Theory.SpecificGroups.PSU3.UniversalCover.OddKernelBound.PrimeSquare
public import Theory.SpecificGroups.PSU3.UniversalCover.OddKernelBound.OddCrossCharacteristic

/-!
# Odd centers of PSU₃ prime and prime-square covers

The concrete defining-prime and cross-characteristic kernel calculations
leave only the scalar factor gcd(3,q+1). Thus a nontrivial odd covering
center has order three and q is minus one modulo three.
Source: Aschbacher–Smith A.2.17 and I.1.3, printed pp.39 and 407.
-/

open Subgroup Theory.GroupTheory PerfectCentralCovering
open BenderSuzuki.MatrixGroups
namespace BenderSuzuki.MatrixGroups.HermitianForm.OddCenterRecognition
variable {F L : Type*} [Field F] [Finite F] [Group L] [Finite L] [Group.IsPerfect L]
  (J : HermitianForm 3 F)

public theorem center_card_dvd {p e : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (he1 : 1 ≤ e) (he2 : e ≤ 2)
    (hcard : Nat.card F = (p^e)^2) (hconj : ∀ x, J.conj x = x^(p^e))
    (iso : L ⧸ center L ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (ho : Odd (Nat.card (center L))) :
    Nat.card (center L) ∣ Nat.gcd 3 (p^e+1) := by
  let f := centralQuotientCover iso
  apply UniversalCover.OddPartDescent.center_card_dvd_gcd_of_odd_center
    J hp hodd he1 he2 hcard hconj iso ho
  · intro heq
    subst e
    simpa only [f, centralQuotientCover_ker] using
      UniversalCover.OddKernelBound.PrimeSquare.not_defining_prime_dvd_kernel
        J f hp hodd hcard hconj
  · intro r hr hr2 hr3 hrp
    simpa only [f, centralQuotientCover_ker] using
      UniversalCover.OddKernelBound.OddCrossCharacteristic.not_dvd_kernel
        J hp (by omega) hr hr2 hr3 hrp hcard hconj f
  · intro hm
    simpa only [f, centralQuotientCover_ker] using
      UniversalCover.OddKernelBound.OddCrossCharacteristic.not_nine_dvd_kernel
        J hcard hconj hm f

public theorem nontrivial_center_card {p e : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (he1 : 1 ≤ e) (he2 : e ≤ 2)
    (hcard : Nat.card F = (p^e)^2) (hconj : ∀ x, J.conj x = x^(p^e))
    (iso : L ⧸ center L ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (ho : Odd (Nat.card (center L))) (hz : center L ≠ ⊥) :
    Nat.card (center L) = 3 ∧ (p^e)%3 = 2 := by
  have hd := center_card_dvd J hp hodd he1 he2 hcard hconj iso ho
  have h3 : Nat.card (center L) = 3 := by
    rcases Nat.prime_three.eq_one_or_self_of_dvd _
      (hd.trans (Nat.gcd_dvd_left 3 (p^e+1))) with h1 | h3
    · exact (hz ((center L).eq_bot_of_card_eq h1)).elim
    · exact h3
  refine ⟨h3, ?_⟩
  have hdiv : 3 ∣ p^e+1 := by
    rw [h3] at hd
    exact hd.trans (Nat.gcd_dvd_right _ _)
  have hm := Nat.mod_eq_zero_of_dvd hdiv
  omega
end BenderSuzuki.MatrixGroups.HermitianForm.OddCenterRecognition
