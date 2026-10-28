module
public import Theory.SpecificGroups.ClassicalUnitary.OddFourRanks.Defining
public import Theory.SpecificGroups.ClassicalUnitary.EvenSmallRanks
public import Theory.SpecificGroups.ClassicalUnitary.OddFundamental
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag
/-!
# Binary unitary fours in the ordinary two-rank sieve

The existing three-coordinate hyperbolic shear at scalar one is an elementary
eight in characteristic two. Orthonormalization moves it to the identity form;
the literal SU4-to-PSU4 projection is injective in this characteristic.
Source: Aschbacher--Smith A.2.12, printed p.36.
-/
public noncomputable section
open Matrix BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.ClassicalUnitary.TwoRank.Binary
open OddFourRanks.Defining
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
variable (J : HermitianForm 4 F)
local instance : Finite (GL (Fin 4) F) := Finite.of_injective Units.val Units.val_injective
local instance (K : HermitianForm 4 F) : Finite (ProjectiveSpecialUnitaryMatrixGroup K) :=
  Finite.of_surjective (ProjectiveKernel.project K) (ProjectiveKernel.project_surjective K)
def embedding : Multiplicative (Fin 3 → ZMod 2) →* (hyperbolicForm J).specialSubgroup :=
  shearSpecial J 1 (by simp [CharTwo.neg_eq])
omit [Finite F] in
theorem embedding_injective : Function.Injective (embedding J) := by
  intro a b h
  apply projectiveShear_injective (r:=2) J 1 (by simp [CharTwo.neg_eq]) one_ne_zero
  exact congrArg (ProjectiveKernel.project (hyperbolicForm J)) h
theorem special_three_le : 3 ≤ primeRank 2 (hyperbolicForm J).specialSubgroup := by
  apply primeRank_ge_of_elementary_embedding (f := embedding J)
  · intro x
    change (2:ℕ) • x.toAdd = 0
    ext i
    change (2:ℕ) • x.toAdd i = 0
    rw [nsmul_eq_mul]
    change (2:ZMod 2) * x.toAdd i = 0
    rw [show (2:ZMod 2)=0 by decide +kernel,zero_mul]
  · simp
  · exact embedding_injective J

theorem identity_special_three_le {q : ℕ} (hq : IsPrimePow q)
    (hcard : Nat.card F = q^2) (hconj : ∀x,J.conj x=x^q) :
    3 ≤ primeRank 2 (HermitianForm.IdentityGram.identityGram J).specialSubgroup := by
  obtain ⟨P,hP⟩ := BenderSuzuki.External.huppert_II_10_4_a_orthonormal_basis
    4 (hyperbolicForm J) q hcard ((hyperbolicForm J).fixed_card_prime_power hq hcard hconj)
  have he := HermitianForm.IdentityGram.specialEquiv (hyperbolicForm J) P hP
  have hh := special_three_le J
  rw [Theory.GroupTheory.primeRank_equiv 2 he] at hh
  exact hh

theorem projective_three_le {q : ℕ} (hq : IsPrimePow q)
    (hcard : Nat.card F = q^2) (hconj : ∀x,J.conj x=x^q) :
    3 ≤ primeRank 2 (ProjectiveSpecialUnitaryMatrixGroup J) := by
  obtain ⟨P,hP⟩ := BenderSuzuki.External.huppert_II_10_4_a_orthonormal_basis
    4 J q hcard (J.fixed_card_prime_power hq hcard hconj)
  rw [Theory.GroupTheory.primeRank_equiv 2 (HermitianForm.IdentityGram.projectiveEquiv J P hP)]
  exact (identity_special_three_le J hq hcard hconj).trans
    (Theory.GroupTheory.primeRank_le_of_injective 2 (UnitaryFourFlag.project F _)
      (UnitaryFourFlag.project_injective F _))
end Theory.SpecificGroups.ClassicalUnitary.TwoRank.Binary
