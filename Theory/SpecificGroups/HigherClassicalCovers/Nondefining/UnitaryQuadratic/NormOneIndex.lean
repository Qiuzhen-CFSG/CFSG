module

public import Theory.SpecificGroups.HigherClassicalCovers.Nondefining.UnitaryQuadratic.Diagonal
public import Theory.SpecificGroups.HigherClassicalCovers.Nondefining.UnitaryQuadratic.NormOneIndex.Geometry
public import Theory.SpecificGroups.HigherClassicalCovers.Nondefining.UnitaryQuadratic.NormOneIndex.Parameters
public import Theory.SpecificGroups.HigherClassicalCovers.Nondefining.UnitaryQuadratic.NormOneIndex.Order

/-!
# Prime-to-r index of the PSU₄ norm-one torus and cycle

Let F have order p², with the stored Hermitian conjugation x ↦ x^p and
identity form. For odd primes r dividing p+1, choose a Sylow r-subgroup C
of Fˣ. Its full order divides p+1, so its elements have norm one. The
published diagonal map embeds C³ into the actual projective SU group.
Adjoining the published coordinate cycle gives order `3 * |C|^3`.

The projective group's order divides the order of the determinant kernel
in GL₄(F). The r-valuation of that bound is `3*v_r(|F|−1) + v_r(3)`, exactly
the valuation of the constructed subgroup. Its index is therefore prime
to r, including r=3 and arbitrarily large r-valuation of p+1. Applying the
three-cycle covering theorem excludes r from every finite perfect central
covering kernel of this actual standard-form projective group.

This discharges the norm-one torus index input for the nondefining-prime
PSU₄ covering step in Aschbacher–Smith A.2.17, printed p.39; covering and
multiplier conventions are I.1.1–I.1.4, printed pp.407–408. Arbitrary-form
transport remains in the parent `UnitaryQuadratic` module. No order or
simplicity classification of the unitary group is assumed.
-/

public noncomputable section
open Matrix Subgroup BenderSuzuki.MatrixGroups PerfectCentralCovering
open Theory.SpecificGroups.ClassicalUnitary
namespace Theory.SpecificGroups.HigherClassicalCovers.Nondefining.UnitaryQuadratic
variable {F : Type*} [Field F] [Finite F]

/-- Full Sylow parameters and the literal coordinate cycle exhaust the ambient r-part. -/
theorem diagonal_cycle_index_of_sylow (J : HermitianForm 4 F) (hJ : J.form = 1)
    {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2) (hd : r ∣ Nat.card F - 1)
    (P : Sylow r Fˣ) (hC : ∀ u : P, J.conj (u.val : F) * (u.val : F) = 1) :
    ¬ r ∣ ((diagonalProjective J hJ P.toSubgroup hC).range ⊔ zpowers (cycle J hJ)).index := by
  let T : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
    (diagonalProjective J hJ P.toSubgroup hC).range ⊔ zpowers (cycle J hJ)
  have ho := sylow_units_card_coprime_two hr2 P
  have hcard : Nat.card T = Nat.card P ^ 3 * 3 := diagonal_cycle_card J hJ P.toSubgroup hC ho
  have hm : padicValNat r (Nat.card P) = padicValNat r (Nat.card F - 1) := by
    rw [P.card_eq_multiplicity, padicValNat.prime_pow, Nat.card_units,
      Nat.factorization_def _ (Fact.out : r.Prime)]
  have hval : padicValNat r (Nat.card T) =
      3 * padicValNat r (Nat.card F - 1) + padicValNat r 3 := by
    rw [hcard, padicValNat.mul (pow_ne_zero _ Nat.card_pos.ne') (by decide),
      padicValNat.pow, hm]
  have hle : padicValNat r (Nat.card (ProjectiveSpecialUnitaryMatrixGroup J)) ≤
      padicValNat r (Nat.card (GeneralLinearGroup.det : GL (Fin 4) F →* Fˣ).ker) :=
    (padicValNat_dvd_iff_le Nat.card_pos.ne').mp
      (pow_padicValNat_dvd.trans (card_projective_dvd_detKernel J))
  rw [card_detKernel_four, valuation_detKernel_order hr2 Finite.one_lt_card hd] at hle
  have hmul := congrArg (padicValNat r) T.card_mul_index
  rw [padicValNat.mul Nat.card_pos.ne' T.index_ne_zero_of_finite, hval] at hmul
  intro hi
  have hpos := one_le_padicValNat_of_dvd T.index_ne_zero_of_finite hi
  omega

/-- Construct the requested odd norm-one torus with prime-to-r torus-by-cycle index. -/
theorem exists_normOne_torus_prime_index
    {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (J : HermitianForm 4 F) (hJ : J.form = 1)
    (_hp2 : p ≠ 2) (hr2 : r ≠ 2) (_hrp : r ≠ p) (hd : r ∣ p + 1)
    (hF : Nat.card F = p ^ 2) (hconj : ∀ x, J.conj x = x ^ p) :
    ∃ (C : Subgroup Fˣ) (hC : ∀ u : C, J.conj (u.val : F) * (u.val : F) = 1),
      (Nat.card C).Coprime 2 ∧
        ¬ r ∣ ((diagonalProjective J hJ C hC).range ⊔ zpowers (cycle J hJ)).index := by
  let P : Sylow r Fˣ := default
  have hC := sylow_units_norm J hr2 hd hF hconj P
  refine ⟨P.toSubgroup, hC, sylow_units_card_coprime_two hr2 P, ?_⟩
  apply diagonal_cycle_index_of_sylow J hJ hr2 _ P hC
  rw [hF]
  have he : p ^ 2 - 1 = (p - 1) * (p + 1) := by
    simpa only [one_pow, mul_comm] using Nat.sq_sub_sq p 1
  rw [he]
  exact dvd_mul_of_dvd_right hd _

/-- Every finite perfect central cover of the actual standard-form PSU₄ has r-free kernel for odd r dividing p+1. -/
theorem not_dvd_kernel_of_dvd_succ
    {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (J : HermitianForm 4 F) (hJ : J.form = 1)
    (hp2 : p ≠ 2) (hr2 : r ≠ 2) (hrp : r ≠ p) (hd : r ∣ p + 1)
    (hF : Nat.card F = p ^ 2) (hconj : ∀ x, J.conj x = x ^ p)
    {E : Type*} [Group E] [Finite E] (f : Cover E (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ¬ r ∣ Nat.card f.toMonoidHom.ker := by
  obtain ⟨C, hC, ho, hi⟩ := exists_normOne_torus_prime_index J hJ hp2 hr2 hrp hd hF hconj
  exact f.not_dvd_kernel_of_permuted_torus (diagonalProjective J hJ C hC)
    (diagonalProjective_injective J hJ C hC ho) ho
    (exists_coordinate_swap J hJ C hC) (cycle J hJ) (cycle_cube J hJ)
    (cycle_diagonal J hJ C hC) hi

end Theory.SpecificGroups.HigherClassicalCovers.Nondefining.UnitaryQuadratic
