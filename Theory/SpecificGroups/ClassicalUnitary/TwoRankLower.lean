module
public import Theory.SpecificGroups.ClassicalUnitary.TwoRankLower.OddFour
public import Theory.SpecificGroups.ClassicalUnitary.TwoRankLower.Binary
public import Theory.SpecificGroups.ClassicalUnitary.TwoRankLower.Diagonal
/-!
# Ordinary two-rank in every higher projective unitary group

PSU4 contains an elementary eight by the binary shear or odd sign-and-swap
construction. In larger dimensions, an SU4 block remains injective after
projectivization because the unused coordinates force every scalar to one.
Orthonormalization handles each original Hermitian form and its stored
Frobenius involution. No simplicity assumption is used.
Source: Aschbacher--Smith A.2.12, printed p.36.
-/
public noncomputable section
open Matrix BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.ClassicalUnitary.TwoRank
variable {F : Type*} [Field F] [Finite F]
local instance finiteGL (n : ℕ) : Finite (GL (Fin n) F) :=
  Finite.of_injective Units.val Units.val_injective
local instance finitePSU {n : ℕ} (J : HermitianForm n F) :
    Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
  Finite.of_surjective (ProjectiveKernel.project J) (ProjectiveKernel.project_surjective J)

private theorem char_two_or_odd {q : ℕ} (hq : IsPrimePow q) (hc : Nat.card F=q^2) :
    (2:F)=0 ∨ (Odd q ∧ (2:F)≠0) := by
  obtain ⟨p,e,hp,he,rfl⟩ := (isPrimePow_nat_iff q).mp hq
  let : Fact p.Prime := ⟨hp⟩
  let : Fintype F := Fintype.ofFinite F
  let : CharP F p := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card,←pow_mul] using hc)
  rcases hp.eq_two_or_odd with rfl | ho
  · left
    exact CharP.cast_eq_zero F 2
  · right
    refine ⟨(Nat.odd_iff.mpr ho).pow,?_⟩
    intro hz
    have hd := (CharP.cast_eq_zero_iff F p 2).mp hz
    have hp2 : p=2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd
    omega

/-- Every genuine PSU4 model has ordinary two-rank at least three. -/
theorem four_three_le (J : HermitianForm 4 F) {q : ℕ}
    (hq : IsPrimePow q) (hcard : Nat.card F=q^2) (hconj : ∀x,J.conj x=x^q) :
    3 ≤ primeRank 2 (ProjectiveSpecialUnitaryMatrixGroup J) := by
  rcases char_two_or_odd hq hcard with h2 | ⟨_,h2⟩
  · let : CharP F 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr h2
    exact Binary.projective_three_le J hq hcard hconj
  · obtain ⟨P,hP⟩ := BenderSuzuki.External.huppert_II_10_4_a_orthonormal_basis
      4 J q hcard (J.fixed_card_prime_power hq hcard hconj)
    rw [Theory.GroupTheory.primeRank_equiv 2 (HermitianForm.IdentityGram.projectiveEquiv J P hP)]
    exact OddFour.three_le J.conj J.conj_involutive h2

/-- Higher-dimensional projective unitary groups retain a faithful SU4 block. -/
theorem higher_three_le {d : ℕ} (hd : 4 ≤ d) (J : HermitianForm d F) {q : ℕ}
    (hq : IsPrimePow q) (hcard : Nat.card F=q^2) (hconj : ∀x,J.conj x=x^q) :
    3 ≤ primeRank 2 (ProjectiveSpecialUnitaryMatrixGroup J) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le hd
  by_cases hn : n=0
  · subst n
    exact four_three_le J hq hcard hconj
  let : NeZero n := ⟨hn⟩
  let J4 := OddFundamental.form J.conj J.conj_involutive 4
  have h4 : 3 ≤ primeRank 2 J4.specialSubgroup := by
    rcases char_two_or_odd hq hcard with h2 | ⟨ho,_⟩
    · let : CharP F 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr h2
      exact Binary.identity_special_three_le J4 hq hcard hconj
    · exact Diagonal.three_le J4 rfl ho hcard hconj
  have hl := h4.trans (Theory.GroupTheory.primeRank_le_of_injective 2
    (OddFundamental.projectLeft J.conj J.conj_involutive (m:=4) (n:=n))
    (OddFundamental.projectLeft_injective _ _))
  obtain ⟨P,hP⟩ := BenderSuzuki.External.huppert_II_10_4_a_orthonormal_basis
    (4+n) J q hcard (J.fixed_card_prime_power hq hcard hconj)
  rw [Theory.GroupTheory.primeRank_equiv 2 (HermitianForm.IdentityGram.projectiveEquiv J P hP)]
  exact hl
end Theory.SpecificGroups.ClassicalUnitary.TwoRank
