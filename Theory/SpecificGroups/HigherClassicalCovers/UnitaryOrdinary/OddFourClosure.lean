module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.Basic
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.Perfectness
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.Universality
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddFourClosure.Reduction

/-!
# Central-closure assembly for SU₄ at Mersenne primes

Perfectness of SU₄ and the independent PSU₄ nondefining-prime exclusion
reduce central closure to covers of SU₄ of degree q or two. Apply the
prime-degree reduction to an arbitrary finite cover, and then apply
`naturalCover_isUniversal_of_closed` to the original natural projection.

The two prime-degree exclusions remain explicit in the theorems here.
They must be supplied by the defining-prime and two-primary calculations
before this assembly proves Aschbacher--Smith I.1.4(3), printed p.408.
The source is GLS3 §6.1; the natural scalar kernel C₄ alone is insufficient.
-/

public section

open BenderSuzuki.MatrixGroups Theory.GroupTheory

namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary

universe u w
variable {F : Type u} [Field F] [Finite F]

/-- Conditional central closure with exactly the two outstanding prime-degree
calculations shown. Perfectness and the nondefining-prime transfer are proved. -/
theorem fourMersenne_injective_of_prime_kernel_exclusions
    (J : HermitianForm 4 F) {q : ℕ}
    (hp : q.Prime) (hq : 3 < q) (hm : ∃ k : ℕ, q + 1 = 2 ^ k)
    (hcard : Nat.card F = q ^ 2) (hconj : ∀ x, J.conj x = x ^ q)
    [IsQuasisimple (ProjectiveSpecialUnitaryMatrixGroup J)]
    (hnondef : OddFourClosure.NondefiningKernelExclusion J q)
    (hdef : OddFourClosure.NoPrimeKernel J q)
    (htwo : OddFourClosure.NoPrimeKernel J 2)
    {E : Type u} [Group E] [Finite E]
    (f : PerfectCentralCovering.Cover E J.specialSubgroup) :
    Function.Injective f.toMonoidHom := by
  let := fourMersenne_isPerfect J hp hq hm hcard hconj
  exact OddFourClosure.injective_of_prime_kernel_exclusions J hp hnondef hdef htwo f

/-- Application to the literal SU₄ → PSU₄ cover in every target universe.
The two outstanding prime-degree calculations are explicit source obligations. -/
theorem fourMersenne_naturalCover_isUniversal_of_prime_kernel_exclusions
    (J : HermitianForm 4 F) {q : ℕ}
    (hp : q.Prime) (hq : 3 < q) (hm : ∃ k : ℕ, q + 1 = 2 ^ k)
    (hcard : Nat.card F = q ^ 2) (hconj : ∀ x, J.conj x = x ^ q)
    [IsQuasisimple (ProjectiveSpecialUnitaryMatrixGroup J)]
    (hnondef : OddFourClosure.NondefiningKernelExclusion J q)
    (hdef : OddFourClosure.NoPrimeKernel J q)
    (htwo : OddFourClosure.NoPrimeKernel J 2) :
    letI := fourMersenne_isPerfect J hp hq hm hcard hconj
    letI := natural_isQuasisimple J
    Covering.IsUniversal.{u, u, w} (naturalCover J) := by
  let := fourMersenne_isPerfect J hp hq hm hcard hconj
  apply naturalCover_isUniversal_of_closed J
  intro E _ _ f
  exact fourMersenne_injective_of_prime_kernel_exclusions J hp hq hm hcard hconj
    hnondef hdef htwo f

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary
