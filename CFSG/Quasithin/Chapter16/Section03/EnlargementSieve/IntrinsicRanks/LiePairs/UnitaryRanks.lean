module

public import CFSG.Quasithin.ClassicalModels
public import Theory.SpecificGroups.SU3.EvenTwoRank.Automorphisms.Unconditional

/-!
# Unitary-three ranks on the source model witnesses

The exact rank n transports through the actual projective model in `IsPSU`.
The automorphism estimate n+1 uses the proved arbitrary-automorphism
semilinear coverage on the standard form and a genuine Hermitian basis
change. Both estimates retain the fixed-field order in the source witness.
The earlier conditional coverage interface is preserved.

Source: Aschbacher–Smith, 16.1.7(3b), printed p.1172, the ordinary-pair
elimination on p.1180, and the correct automorphism bound on p.356.
-/

public section

open Theory.GroupTheory BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter16.EnlargementSieve.IntrinsicRanks.LiePairs

/-- The actual PSU₃(2ⁿ) model has two-rank n. -/
theorem unitaryThree_rank {M : Type*} [Group M] [Finite M] {n : ℕ}
    (hn : 0 < n) (hM : ClassicalGroup.IsPSU M 3 (2 ^ n)) :
    primeRank 2 M = n := by
  obtain ⟨F, _, _, J, hcard, hconj, ⟨e⟩⟩ := hM
  let : Finite (Matrix.ProjGenLinGroup (Fin 3) F) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  let : Fintype (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Fintype.ofFinite _
  rw [primeRank_equiv 2 e]
  exact HermitianForm.EvenTwoRank.two_rank J hn hcard hconj

/-- The concrete semilinear coverage theorem suffices for the source bound.
The premise is structural and supplies no rank conclusion. -/
theorem unitaryThree_automorphism_rank_le_of_coverage
    {n : ℕ} (hn : 2 ≤ n)
    (hcoverage : ∀ (E : Type) [Field E] [Finite E] (J : HermitianForm 3 E),
      J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] →
      Nat.card E = (2 ^ n) ^ 2 → Nat.card {x : E // J.conj x = x} = 2 ^ n →
      ∀ a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J),
        ∃ σ : E ≃+* E, J.HasUnitarySemilinearForm a σ)
    {M : Type*} [Group M] [Finite M] (hM : ClassicalGroup.IsPSU M 3 (2 ^ n)) :
    primeRank 2 (MulAut M) ≤ n + 1 := by
  obtain ⟨F, _, _, J, hcard, hconj, ⟨e⟩⟩ := hM
  let : Finite (Matrix.ProjGenLinGroup (Fin 3) F) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  let : Fintype (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Fintype.ofFinite _
  have hfixed : Nat.card {x : F // J.conj x = x} = 2 ^ n :=
    FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hcard hconj
  rw [primeRank_equiv 2 (MulAut.congr e)]
  apply HermitianForm.EvenTwoRank.automorphism_two_rank_le_of_standard_coverage
    J (by omega) hcard hconj
  exact hcoverage F
    (HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J)
    rfl hcard hfixed

/-- The source automorphism bound on a genuine PSU₃(2ⁿ) model witness.
All semilinear coverage and form-transport premises are discharged. -/
theorem unitaryThree_automorphism_rank_le
    {n : ℕ} (hn : 2 ≤ n)
    {M : Type*} [Group M] [Finite M] (hM : ClassicalGroup.IsPSU M 3 (2 ^ n)) :
    primeRank 2 (MulAut M) ≤ n + 1 := by
  obtain ⟨F, _, _, J, hcard, hconj, ⟨e⟩⟩ := hM
  let : Finite (Matrix.ProjGenLinGroup (Fin 3) F) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  let : Fintype (ProjectiveSpecialUnitaryMatrixGroup J) := Fintype.ofFinite _
  rw [primeRank_equiv 2 (MulAut.congr e)]
  exact HermitianForm.EvenTwoRank.automorphism_two_rank_le J hn hcard hconj

end CFSG.Quasithin.Chapter16.EnlargementSieve.IntrinsicRanks.LiePairs
