module
public import Theory.SpecificGroups.SU3.OddThreeLocal.CyclicSylow
public import Theory.GroupTheory.PrimeRankCyclicSylow
public import Theory.NumberTheory.BinaryTorusParity

/-!
# Cubic rank detects the parity of a binary PSU₃ fixed field

For even fixed-field degree, the genuine unitary torus of order q²−1
has index prime to three. Every cubic Sylow subgroup is therefore cyclic.
Cubic rank at least two forces odd degree. The finite-field fixed-point
calculation retains the original Hermitian form and its Frobenius involution.

Source: Huppert II.10.12; Aschbacher–Smith 1.3.4, p.511, and A.3.18, pp.51–53.
-/

@[expose] public section
noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
namespace BenderSuzuki.MatrixGroups.HermitianForm.BinaryCubicRankParity
variable {F : Type*} [Field F] [Finite F] {f : ℕ}

/-- An even fixed-field degree gives cyclic cubic Sylow subgroups of PSU₃. -/
theorem rank_le_one_of_even (J : HermitianForm 3 F) (hf : 0 < f)
    (hF : Nat.card F = (2 ^ f) ^ 2) (hc : ∀ x, J.conj x = x ^ (2 ^ f))
    (he : Even f) : primeRank 3 (ProjectiveSpecialUnitaryMatrixGroup J) ≤ 1 := by
  let : Finite (Matrix.ProjGenLinGroup (Fin 3) F) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  let P : Sylow 3 (ProjectiveSpecialUnitaryMatrixGroup J) := default
  have hmod : 2 ^ f % 3 = 1 := by
    rw [Nat.BinaryTorusParity.two_pow_mod_three, if_pos (Nat.even_iff.mp he)]
  exact P.primeRank_le_one_of_isCyclic
    (OddThreeLocal.cyclic_three_sylow_of_mod_one J (2 ^ f)
      (one_lt_pow₀ (by decide) (by omega)) hmod hF
      (FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 f hf hF hc) P)

/-- Cubic rank two forces the nonsplit, odd-degree unitary parameter. -/
theorem odd_of_rank_two (J : HermitianForm 3 F) (hf : 0 < f)
    (hF : Nat.card F = (2 ^ f) ^ 2) (hc : ∀ x, J.conj x = x ^ (2 ^ f))
    (hr : 2 ≤ primeRank 3 (ProjectiveSpecialUnitaryMatrixGroup J)) : Odd f := by
  apply Nat.not_even_iff_odd.mp
  intro he
  have hb := rank_le_one_of_even J hf hF hc he
  omega
end BenderSuzuki.MatrixGroups.HermitianForm.BinaryCubicRankParity
