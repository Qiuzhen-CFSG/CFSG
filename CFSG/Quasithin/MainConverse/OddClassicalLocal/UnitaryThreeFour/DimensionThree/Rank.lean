module

public import CFSG.Quasithin.Defs
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.FormTransport
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport
public import BenderSuzuki.External.Huppert.II.theorem_10_12
public import Theory.GroupTheory.PrimeRankNonabelianCube

/-!
# Odd-prime ranks of PSU₃(3)

Huppert's explicit root subgroup has order 27 and derived subgroup of order
three. Its index is 224, so it is a nonabelian Sylow three-subgroup. Every
abelian subgroup of it is proper and has rank at most two. The order 6048
excludes cubes of all other odd primes. Basis change transports these facts
from the antidiagonal form to the given actual projective unitary image.

Source: Aschbacher–Smith, Theorem 0.1.2(4), printed pp.4 and 482;
Huppert, Endliche Gruppen I, II.10.12, pp.264–265.
-/

namespace CFSG.Quasithin.MainConverse.UnitaryThree

open BenderSuzuki.MatrixGroups BenderSuzuki.External
open HermitianForm.OddPrimeSylow.NormalizedOuter

variable {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)

private theorem fixed_card (hF : Nat.card F = 3 ^ 2)
    (hc : ∀ x, J.conj x = x ^ 3) : Nat.card {x : F // J.conj x = x} = 3 := by
  simpa only [pow_one] using
    FiniteField.card_fixed_of_quadratic_frobenius J.conj 3 1 (by decide) hF hc

/-- The order is computed for the actual image in PGL, with any allowed form. -/
public theorem projective_card (hF : Nat.card F = 3 ^ 2)
    (hc : ∀ x, J.conj x = x ^ 3) :
    Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) = 6048 := by
  have hf := fixed_card J hF hc
  obtain ⟨e⟩ := FormTransport.exists_projectiveEquiv J 3 hF hf
  rw [Nat.card_congr e.toEquiv]
  obtain ⟨_, _, _, _, _, _, _, _, hG, _⟩ :=
    huppert_II_10_12 (FormTransport.standardForm J) 3 hF hf rfl
  exact hG

/-- The defining-prime bound comes from a nonabelian root Sylow of order 27. -/
public theorem primeRank_three_le_two (hF : Nat.card F = 3 ^ 2)
    (hc : ∀ x, J.conj x = x ^ 3) :
    primeRank 3 (ProjectiveSpecialUnitaryMatrixGroup J) ≤ 2 := by
  let : Finite (Matrix.ProjGenLinGroup (Fin 3) F) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have hf := fixed_card J hF hc
  obtain ⟨e⟩ := FormTransport.exists_projectiveEquiv J 3 hF hf
  rw [Theory.GroupTheory.primeRank_equiv 3 e]
  obtain ⟨_, _, _, _, _, _, ht, _, hG, _⟩ :=
    huppert_II_10_12 (FormTransport.standardForm J) 3 hF hf rfl
  obtain ⟨R, _, _, _, _, _, _, _, hR, _, hcomm, _⟩ := ht
  have hRi : R.index = 224 := by
    have he := R.card_mul_index
    have hG' : Nat.card (ProjectiveSpecialUnitaryMatrixGroup (FormTransport.standardForm J)) =
        6048 := hG
    rw [hR, hG'] at he
    omega
  let S : Sylow 3 _ := (IsPGroup.of_card hR).toSylow (by rw [hRi]; decide)
  apply primeRank_le_two_of_nonabelian_sylow_cube S hR
  intro hab
  rw [(commutator_eq_bot_iff R).mpr hab, Subgroup.card_bot] at hcomm
  norm_num at hcomm

/-- Every odd-prime rank is bounded in the whole group. -/
public theorem stronglyQuasithin (hF : Nat.card F = 3 ^ 2)
    (hc : ∀ x, J.conj x = x ^ 3) :
    IsStronglyQuasithin (ProjectiveSpecialUnitaryMatrixGroup J) := by
  let : Finite (Matrix.ProjGenLinGroup (Fin 3) F) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  by_cases h3 : p = 3
  · subst p
    exact primeRank_three_le_two J hF hc
  apply primeRank_le_two_of_cube_not_dvd
  rw [projective_card J hF hc]
  intro hd
  have hpd : p ∣ 2 ^ 5 * (3 ^ 3 * 7) := by
    norm_num
    exact (dvd_pow_self p (by decide : 3 ≠ 0)).trans hd
  have hpv : p = 2 ∨ p = 3 ∨ p = 7 := by
    rcases hp.dvd_mul.mp hpd with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
        (hp.dvd_of_dvd_pow h))
    rcases hp.dvd_mul.mp h with h | h
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
        (hp.dvd_of_dvd_pow h)))
    · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h))
  rcases hpv with rfl | rfl | rfl
  · exact ho.not_two_dvd_nat (dvd_refl 2)
  · exact h3 rfl
  · norm_num at hd

/-- In particular, all two-local subgroups satisfy the required odd-rank bound. -/
public theorem twoLocal_primeRank_le_two (hF : Nat.card F = 3 ^ 2)
    (hc : ∀ x, J.conj x = x ^ 3)
    (M : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) (_hM : IsTwoLocal M)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) : primeRank p M ≤ 2 := by
  let : Finite (Matrix.ProjGenLinGroup (Fin 3) F) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  exact (stronglyQuasithin J hF hc).subgroup M p hp ho

end CFSG.Quasithin.MainConverse.UnitaryThree
