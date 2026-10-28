module

public import Theory.SpecificGroups.PSU3.UniversalCover.OddPartDescent
public import Theory.SpecificGroups.PSU3.UniversalCover.EvenKernelBound.LargePrimary.Complete
public import Theory.SpecificGroups.PSU3.UniversalCover.EvenKernelBound.ThreePrimary.Complete
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCore

/-!
# Odd-center covers of binary projective unitary groups

For a quasisimple group with marked central quotient PSU₃(2ⁿ), an odd
center forces the scalar SU₃ cover to map onto the original group. The
large-prime and three-primary kernel calculations discharge every premise
of odd-part descent. Comparing kernels shows that the center divides
gcd(3,2ⁿ+1). If it is nontrivial, the scalar map is an isomorphism, n is
odd, and n ≥ 3. The isomorphism retains the original quotient triangle.

Here 2ⁿ is the fixed-field order; the matrix field has order (2ⁿ)².
Source: Aschbacher–Smith A.2.12(I) and A.2.18, printed pp.36–37 and 40;
I.1.3 supplies the covering convention.
-/

public section

open Subgroup Theory.GroupTheory PerfectCentralCovering
open BenderSuzuki.MatrixGroups

namespace BenderSuzuki.MatrixGroups.HermitianForm.EvenOddCenterCover

open UniversalCover

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

/-- The scalar SU₃ map onto the supplied odd-center cover, over the exact
central quotient marking. All odd-primary bounds have been discharged. -/
theorem exists_scalar_lift {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card F = (2 ^ n) ^ 2) (hc : ∀ x, J.conj x = x ^ (2 ^ n))
    (e : L ⧸ center L ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (ho : Odd (Nat.card (center L))) :
    ∃ k : J.specialSubgroup →* L, Function.Surjective k ∧
      (centralQuotientCover e).toMonoidHom.comp k = J.specialToProjective := by
  exact OddPartDescent.exists_lift_even J hn hcard hc
    (fun r hr hr3 => EvenKernelBound.LargePrimary.not_dvd_universal_kernel
      J hn hr hr3 hcard hc)
    (fun hodd => EvenKernelBound.ThreePrimary.not_nine_dvd_universal_kernel
      J hn hodd hcard hc)
    (centralQuotientCover e).toMonoidHom (centralQuotientCover e).surjective
    (twoCore_eq_bot ho)

/-- The center order of the original cover divides the scalar kernel order. -/
theorem center_card_dvd {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card F = (2 ^ n) ^ 2) (hc : ∀ x, J.conj x = x ^ (2 ^ n))
    (e : L ⧸ center L ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (ho : Odd (Nat.card (center L))) :
    Nat.card (center L) ∣ Nat.gcd 3 (2 ^ n + 1) := by
  obtain ⟨k, hks, hk⟩ := exists_scalar_lift J hn hcard hc e ho
  have hd := kernel_card_dvd_of_surjective_factor J.specialToProjective
    (centralQuotientCover e).toMonoidHom k hks hk
  simpa only [centralQuotientCover_ker, card_kernel J hcard hc] using hd

/-- Nontrivial odd-center covers are the actual SU₃ group, with center C₃
and odd exponent at least three. The equivalence commutes with projection. -/
theorem nontrivial_center_recognition {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card F = (2 ^ n) ^ 2) (hc : ∀ x, J.conj x = x ^ (2 ^ n))
    (e : L ⧸ center L ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (ho : Odd (Nat.card (center L))) (hz : center L ≠ ⊥) :
    Odd n ∧ 3 ≤ n ∧ Nat.card (center L) = 3 ∧
      Nonempty (center L ≃* Multiplicative (ZMod 3)) ∧
      ∃ j : J.specialSubgroup ≃* L,
        (centralQuotientCover e).toMonoidHom.comp j.toMonoidHom =
          J.specialToProjective := by
  have hd := center_card_dvd J hn hcard hc e ho
  have h3 : Nat.card (center L) = 3 := by
    rcases Nat.prime_three.eq_one_or_self_of_dvd _
      (hd.trans (Nat.gcd_dvd_left 3 (2 ^ n + 1))) with h1 | h3
    · exact (hz ((center L).eq_bot_of_card_eq h1)).elim
    · exact h3
  have hg : Nat.gcd 3 (2 ^ n + 1) = 3 :=
    Nat.dvd_antisymm (Nat.gcd_dvd_left _ _) (h3 ▸ hd)
  have hdiv : 3 ∣ 2 ^ n + 1 := hg ▸ Nat.gcd_dvd_right 3 (2 ^ n + 1)
  have hnodd : Odd n := by
    rw [Nat.odd_iff]
    have hm := Nat.BinaryTorusParity.two_pow_mod_three n
    have hm0 := Nat.mod_eq_zero_of_dvd hdiv
    split_ifs at hm <;> omega
  obtain ⟨k, hks, hk⟩ := exists_scalar_lift J hn hcard hc e ho
  have hcount := kernel_card_eq_mul_of_surjective_factor J.specialToProjective
    (centralQuotientCover e).toMonoidHom k (centralQuotientCover e).surjective hks hk
  have hker : Nat.card k.ker = 1 := by
    rw [card_kernel J hcard hc, hg, centralQuotientCover_ker, h3] at hcount
    omega
  let j : J.specialSubgroup ≃* L := MulEquiv.ofBijective k
    ⟨k.ker_eq_bot_iff.mp (k.ker.eq_bot_of_card_eq hker), hks⟩
  refine ⟨hnodd, ?_, h3, ⟨mulEquivOfPrimeCardEq h3 (by simp)⟩, j, hk⟩
  have := Nat.odd_iff.mp hnodd
  omega

end BenderSuzuki.MatrixGroups.HermitianForm.EvenOddCenterCover
