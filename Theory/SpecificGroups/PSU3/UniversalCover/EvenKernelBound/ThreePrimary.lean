module

public import Theory.SpecificGroups.PSU3.UniversalCover.Projection
public import Theory.SpecificGroups.PSU3.UniversalCover.EvenKernelBound.ThreePrimary.LocalStructure
public import Theory.GroupTheory.PerfectCentralCoverCyclicFixedBound
public import Theory.GroupTheory.PerfectCentralCoverExistence

/-!
# The three-primary kernel bound from the actual projective torus

An ambient coordinate swap makes the preimage of the odd-order diagonal
torus abelian in every central cover. The derived subgroup of its extension
by a three-cycle is the range of a commutator homomorphism factoring through
the projective torus. The torus fixed subgroup bounds the kernel of this
homomorphism's range over the base. Transfer then excludes nine from the
perfect central kernel when that fixed subgroup has order at most three.

The theorems here apply this argument to the literal PSU₃ carrier and its
universal projection. The matrix configuration remains an explicit input;
constructing it is required to finish the unconditional odd-exponent bound.
In particular, neither `q = 8` nor higher three-power torus exponents are
excluded by the argument.

Source: Aschbacher–Smith I.1.3(2), printed p.407 (PDF p.418), and
GLS III, Theorem 6.1.4 and Tables 6.1.2–3.
-/

public section

open BenderSuzuki.MatrixGroups PerfectCentralCovering

namespace BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.EvenKernelBound.ThreePrimary

universe u v
variable {F : Type u} [Field F] [Finite F] (J : HermitianForm 3 F)

/-- The concrete torus configuration excludes nine from every finite perfect
central cover. The field and Frobenius hypotheses are needed only to construct
the configuration, not for this transfer argument. -/
theorem not_nine_dvd_cover_kernel_of_torus
    {n : ℕ} (hn : 0 < n) (t : TorusConfiguration J n)
    {E : Type v} [Group E] [Finite E]
    (f : Cover E (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ¬ 3 ^ 2 ∣ Nat.card f.toMonoidHom.ker := by
  have hm : (2 ^ n + 1).Coprime 2 := by
    apply Nat.coprime_two_right.mpr
    exact (Even.add_odd ((even_two : Even (2 : ℕ)).pow_of_ne_zero (by omega)) odd_one)
  exact f.not_primePower_dvd_kernel_of_swapped_torus_fixed
    t.torus t.first t.second t.cycle t.swap t.generate t.commute
    t.swap_first t.swap_second hm t.first_pow t.normalizes t.index_prime_to_three
    (lt_of_le_of_lt t.fixed_card_le (by decide : 3 < 3 ^ 2))

/-- Application to the literal universal projection. The remaining extra
premise is exactly the local matrix configuration, not a covering conclusion. -/
theorem not_nine_dvd_universal_kernel_of_torus
    {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card F = (2 ^ n) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (t : TorusConfiguration J n) :
    ¬ 3 ^ 2 ∣ Nat.card (universalProjection (ProjectiveSpecialUnitaryMatrixGroup J)).ker := by
  have hq : 2 < 2 ^ n := lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
    (Nat.pow_le_pow_right (by decide) hn)
  let := projective_isQuasisimple J hq hcard hconj
  exact not_nine_dvd_cover_kernel_of_torus J (by omega) t (universalCover _)

end BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.EvenKernelBound.ThreePrimary
