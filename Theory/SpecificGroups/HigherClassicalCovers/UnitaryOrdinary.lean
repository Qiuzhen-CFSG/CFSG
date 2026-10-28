module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.Perfectness
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.Universality

/-!
# The ordinary degree-four and degree-five unitary natural covers

The literal projection from special unitary matrices to their image in PGL
is a covering in each required ordinary range. Its kernel is C₄ for
Mersenne primes q > 3, trivial for even q, and C₅ for SU₅(4), whose
coefficient field has order sixteen. Projective quasisimplicity is inherited
from the actual source quotient; special-unitary perfectness is proved here.

Universality is assembled conditionally from central closure of each
special-unitary group. These explicitly named conditional results do not
assert that the closure premises have been proved. Those three intrinsic
central-extension calculations remain necessary to complete the ordinary
rows of Aschbacher--Smith I.1.3--4, pp.407--408, and GLS3 Section 6.1.
The exceptional parameters PSU₄(2) and PSU₄(3) are not covered by the
universal-property applications.
-/

@[expose] public noncomputable section

open BenderSuzuki.MatrixGroups Theory.GroupTheory
open Theory.SpecificGroups.ClassicalUnitary.ProjectiveKernel

namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary
universe u w
variable {F : Type u} [Field F] [Finite F]

/-- The natural projection in this ordinary range, with matrix perfectness proved. -/
def fourMersenneCover (J : HermitianForm 4 F) {q : ℕ}
    (hp : q.Prime) (hq : 3 < q) (hm : ∃ k : ℕ, q + 1 = 2 ^ k)
    (hcard : Nat.card F = q ^ 2) (hconj : ∀ x, J.conj x = x ^ q)
    [IsQuasisimple (ProjectiveSpecialUnitaryMatrixGroup J)] :
    letI := fourMersenne_isPerfect J hp hq hm hcard hconj
    letI := natural_isQuasisimple J
    Covering J.specialSubgroup (ProjectiveSpecialUnitaryMatrixGroup J) := by
  letI := fourMersenne_isPerfect J hp hq hm hcard hconj
  exact naturalCover J

/-- The packaged covering uses precisely the original projective map. -/
@[simp] theorem fourMersenneCover_toMonoidHom (J : HermitianForm 4 F) {q : ℕ}
    (hp : q.Prime) (hq : 3 < q) (hm : ∃ k : ℕ, q + 1 = 2 ^ k)
    (hcard : Nat.card F = q ^ 2) (hconj : ∀ x, J.conj x = x ^ q)
    [IsQuasisimple (ProjectiveSpecialUnitaryMatrixGroup J)] :
    letI := fourMersenne_isPerfect J hp hq hm hcard hconj
    letI := natural_isQuasisimple J
    (fourMersenneCover J hp hq hm hcard hconj).toMonoidHom = project J := rfl

/-- Conditional final assembly; central closure is still an explicit obligation. -/
theorem fourMersenneCover_isUniversal_of_closed (J : HermitianForm 4 F) {q : ℕ}
    (hp : q.Prime) (hq : 3 < q) (hm : ∃ k : ℕ, q + 1 = 2 ^ k)
    (hcard : Nat.card F = q ^ 2) (hconj : ∀ x, J.conj x = x ^ q)
    [IsQuasisimple (ProjectiveSpecialUnitaryMatrixGroup J)]
    (hclosed : ∀ (E : Type u) [Group E] [Finite E]
      (c : PerfectCentralCovering.Cover E J.specialSubgroup),
      Function.Injective c.toMonoidHom) :
    letI := fourMersenne_isPerfect J hp hq hm hcard hconj
    letI := natural_isQuasisimple J
    Covering.IsUniversal.{u, u, w} (fourMersenneCover J hp hq hm hcard hconj) := by
  let := fourMersenne_isPerfect J hp hq hm hcard hconj
  exact naturalCover_isUniversal_of_closed J hclosed

/-- The natural projection in this ordinary range, with matrix perfectness proved. -/
def fourBinaryCover (J : HermitianForm 4 F) (f : ℕ) (hf : 2 ≤ f)
    (hcard : Nat.card F = (2 ^ f) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ f))
    [IsQuasisimple (ProjectiveSpecialUnitaryMatrixGroup J)] :
    letI := fourEven_isPerfect J (Nat.even_pow.mpr ⟨even_two, by omega⟩) hcard hconj
    letI := natural_isQuasisimple J
    Covering J.specialSubgroup (ProjectiveSpecialUnitaryMatrixGroup J) := by
  letI := fourEven_isPerfect J (Nat.even_pow.mpr ⟨even_two, by omega⟩) hcard hconj
  exact naturalCover J

/-- The packaged covering uses precisely the original projective map. -/
@[simp] theorem fourBinaryCover_toMonoidHom (J : HermitianForm 4 F) (f : ℕ) (hf : 2 ≤ f)
    (hcard : Nat.card F = (2 ^ f) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ f))
    [IsQuasisimple (ProjectiveSpecialUnitaryMatrixGroup J)] :
    letI := fourEven_isPerfect J (Nat.even_pow.mpr ⟨even_two, by omega⟩) hcard hconj
    letI := natural_isQuasisimple J
    (fourBinaryCover J f hf hcard hconj).toMonoidHom = project J := rfl

/-- Conditional final assembly; central closure is still an explicit obligation. -/
theorem fourBinaryCover_isUniversal_of_closed (J : HermitianForm 4 F) (f : ℕ) (hf : 2 ≤ f)
    (hcard : Nat.card F = (2 ^ f) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ f))
    [IsQuasisimple (ProjectiveSpecialUnitaryMatrixGroup J)]
    (hclosed : ∀ (E : Type u) [Group E] [Finite E]
      (c : PerfectCentralCovering.Cover E J.specialSubgroup),
      Function.Injective c.toMonoidHom) :
    letI := fourEven_isPerfect J (Nat.even_pow.mpr ⟨even_two, by omega⟩) hcard hconj
    letI := natural_isQuasisimple J
    Covering.IsUniversal.{u, u, w} (fourBinaryCover J f hf hcard hconj) := by
  let := fourEven_isPerfect J (Nat.even_pow.mpr ⟨even_two, by omega⟩) hcard hconj
  exact naturalCover_isUniversal_of_closed J hclosed

/-- The natural projection in this ordinary range, with matrix perfectness proved. -/
def fiveFourCover (J : HermitianForm 5 F) (hcard : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x ^ 4)
    [IsQuasisimple (ProjectiveSpecialUnitaryMatrixGroup J)] :
    letI := fiveFour_isPerfect J hcard hconj
    letI := natural_isQuasisimple J
    Covering J.specialSubgroup (ProjectiveSpecialUnitaryMatrixGroup J) := by
  letI := fiveFour_isPerfect J hcard hconj
  exact naturalCover J

/-- The packaged covering uses precisely the original projective map. -/
@[simp] theorem fiveFourCover_toMonoidHom (J : HermitianForm 5 F) (hcard : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x ^ 4)
    [IsQuasisimple (ProjectiveSpecialUnitaryMatrixGroup J)] :
    letI := fiveFour_isPerfect J hcard hconj
    letI := natural_isQuasisimple J
    (fiveFourCover J hcard hconj).toMonoidHom = project J := rfl

/-- Conditional final assembly; central closure is still an explicit obligation. -/
theorem fiveFourCover_isUniversal_of_closed (J : HermitianForm 5 F) (hcard : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x ^ 4)
    [IsQuasisimple (ProjectiveSpecialUnitaryMatrixGroup J)]
    (hclosed : ∀ (E : Type u) [Group E] [Finite E]
      (c : PerfectCentralCovering.Cover E J.specialSubgroup),
      Function.Injective c.toMonoidHom) :
    letI := fiveFour_isPerfect J hcard hconj
    letI := natural_isQuasisimple J
    Covering.IsUniversal.{u, u, w} (fiveFourCover J hcard hconj) := by
  let := fiveFour_isPerfect J hcard hconj
  exact naturalCover_isUniversal_of_closed J hclosed


/-- The kernel of the packaged Mersenne cover, with the literal projection retained. -/
def fourMersenneCoverKernelEquiv (J : HermitianForm 4 F) {q : ℕ}
    (hp : q.Prime) (hq : 3 < q) (hm : ∃ k : ℕ, q + 1 = 2 ^ k)
    (hcard : Nat.card F = q ^ 2) (hconj : ∀ x, J.conj x = x ^ q)
    [IsQuasisimple (ProjectiveSpecialUnitaryMatrixGroup J)] :
    letI := fourMersenne_isPerfect J hp hq hm hcard hconj
    letI := natural_isQuasisimple J
    (fourMersenneCover J hp hq hm hcard hconj).toMonoidHom.ker ≃*
      Multiplicative (ZMod 4) :=
  fourMersenneKernelEquiv J hq hm hcard hconj

/-- The packaged binary cover has trivial kernel. -/
theorem fourBinaryCover_kernel_eq_bot (J : HermitianForm 4 F) (f : ℕ) (hf : 2 ≤ f)
    (hcard : Nat.card F = (2 ^ f) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ f))
    [IsQuasisimple (ProjectiveSpecialUnitaryMatrixGroup J)] :
    letI := fourEven_isPerfect J (Nat.even_pow.mpr ⟨even_two, by omega⟩) hcard hconj
    letI := natural_isQuasisimple J
    (fourBinaryCover J f hf hcard hconj).toMonoidHom.ker = ⊥ :=
  fourEven_kernel_eq_bot J (Nat.even_pow.mpr ⟨even_two, by omega⟩) hcard hconj

/-- Its kernel is isomorphic to the trivial group. -/
def fourBinaryCoverKernelEquiv (J : HermitianForm 4 F) (f : ℕ) (hf : 2 ≤ f)
    (hcard : Nat.card F = (2 ^ f) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ f))
    [IsQuasisimple (ProjectiveSpecialUnitaryMatrixGroup J)] :
    letI := fourEven_isPerfect J (Nat.even_pow.mpr ⟨even_two, by omega⟩) hcard hconj
    letI := natural_isQuasisimple J
    (fourBinaryCover J f hf hcard hconj).toMonoidHom.ker ≃* PUnit := by
  letI := fourEven_isPerfect J (Nat.even_pow.mpr ⟨even_two, by omega⟩) hcard hconj
  letI := natural_isQuasisimple J
  have hk := fourBinaryCover_kernel_eq_bot J f hf hcard hconj
  letI : Subsingleton (fourBinaryCover J f hf hcard hconj).toMonoidHom.ker := by
    rw [hk]
    infer_instance
  letI : Unique (fourBinaryCover J f hf hcard hconj).toMonoidHom.ker := uniqueOfSubsingleton 1
  exact MulEquiv.ofUnique

/-- The packaged SU₅(4) cover has its actual scalar C₅ kernel. -/
def fiveFourCoverKernelEquiv (J : HermitianForm 5 F) (hcard : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x ^ 4)
    [IsQuasisimple (ProjectiveSpecialUnitaryMatrixGroup J)] :
    letI := fiveFour_isPerfect J hcard hconj
    letI := natural_isQuasisimple J
    (fiveFourCover J hcard hconj).toMonoidHom.ker ≃* Multiplicative (ZMod 5) :=
  fiveFourKernelEquiv J hcard hconj

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary
