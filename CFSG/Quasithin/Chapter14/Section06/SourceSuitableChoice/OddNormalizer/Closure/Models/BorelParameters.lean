module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.Targets
public import Theory.NumberTheory.BinaryMersenneSmallPrimeSupport

/-!
# The field parameter from the literal solvable-overgroup prime bound

Once a Borel construction supplies a solvable H ≤ J ≤ Mc whose order is
divisible by 2^m-1, the original prime bound restricts m to two or four.
For p=3 the divisor five excludes m=4. For p=5 the original congruence
2^m ≡ 1 modulo p excludes m=2.

The overgroup and its order divisibility remain explicit: this proves the
arithmetic deduction, not the Borel placement or the full wreath quotient.
Both must still be supplied in the source model-recognition argument.
Source: Aschbacher--Smith, proof of 14.6.14, printed p.1033.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer
variable {G : Type*} [Group G]

/-- Apply the arithmetic restriction to the actual solvable overgroup J.
No Borel existence or automorphism-model conclusion is assumed here. -/
theorem field_parameter_of_solvable_overgroup
    {H Mc : Subgroup G} {p : ℕ} (hp : p = 3 ∨ p = 5)
    (hbound : SolvableOvergroupPrimeBound H Mc p)
    (J : Subgroup G) (hHJ : H ≤ J) (hJMc : J ≤ Mc) (hs : Group.IsSolvable J)
    {m : ℕ} (hm : 2 ≤ m) (hdiv : 2 ^ m - 1 ∣ Nat.card J)
    (hcong : Nat.ModEq p (2 ^ m) 1) :
    (p = 3 ∧ m = 2) ∨ (p = 5 ∧ m = 4) := by
  have hparam : m = 2 ∨ m = 4 := Nat.two_pow_sub_one_small_prime_support hm (by
    intro q hq hqd
    rcases hbound J hHJ hJMc hs q hq (hqd.trans hdiv) with rfl | hthree | ⟨_,hfive⟩
    · have hpow : 2 ∣ (2 : ℕ) ^ m := dvd_pow_self _ (by omega)
      have hpos : 1 ≤ (2 : ℕ) ^ m := Nat.one_le_pow _ _ (by decide)
      have hsum : 2 ∣ (2 ^ m - 1) + 1 := (Nat.sub_add_cancel hpos).symm ▸ hpow
      have hone : 2 ∣ 1 := (Nat.dvd_add_iff_right hqd).mpr hsum
      exact (by decide : ¬ 2 ∣ 1) hone |>.elim
    · exact Or.inl hthree
    · exact Or.inr hfive)
  rcases hp with rfl | rfl
  · rcases hparam with hm | rfl
    · exact Or.inl ⟨rfl,hm⟩
    · have hfive : 5 ∣ Nat.card J := (by norm_num : 5 ∣ (2 : ℕ) ^ 4 - 1).trans hdiv
      rcases hbound J hHJ hJMc hs 5 (by decide) hfive with h | h | ⟨h,_⟩ <;>
        norm_num at h
  · rcases hparam with rfl | hm
    · norm_num [Nat.ModEq] at hcong
    · exact Or.inr ⟨rfl,hm⟩

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer
