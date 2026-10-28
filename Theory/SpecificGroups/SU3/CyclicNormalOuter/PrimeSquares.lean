module

public import Theory.SpecificGroups.SU3.CyclicNormalOuter
public import Theory.SpecificGroups.SU3.CyclicNormalOuter.OddCoverage
public import Theory.FieldTheory.FiniteAutomorphismOrder

/-!
# Outer squares of PSU₃ over odd prime fixed fields

The matrix field has prime-square order, so each field automorphism has
square one. The proved semilinear coverage therefore puts every automorphism
square in the unitary conjugation image. Modulo inner automorphisms this
image is cyclic, by the determinant-kernel calculation.

Source: GLS3, Theorem 2.5.12(c,d,f), and the unitary matrix description
in §2.7, `refs/KGroup/GLS3/chapter2.tex`.
-/

public section
namespace BenderSuzuki.MatrixGroups.HermitianForm
variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)

/-- Over a prime-square matrix field, every outer square of PSU₃ is diagonal. -/
theorem outer_square_mem_unitary_of_odd_prime
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hcard : Nat.card E = p ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = p)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) :
    (QuotientGroup.mk' (MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J)) a) ^ 2 ∈
      J.unitaryOuterHom.range := by
  obtain ⟨σ, ha⟩ := OddPrimeSylow.NormalizedOuter.Coverage.semilinear_coverage_odd
    J hJ hp ho hcard hfixed a
  have hσ : σ ^ 2 = 1 := FiniteField.ringAut_sq_of_card_prime_pow hp (by decide) hcard σ
  have ha2 : J.HasUnitarySemilinearForm (a ^ 2) 1 := by
    simpa only [← pow_two, hσ] using ha.mul J hJ ha
  obtain ⟨u, hu⟩ := (HasUnitarySemilinearForm.one_iff J).mp ha2
  refine ⟨u, ?_⟩
  change QuotientGroup.mk' (MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (J.unitaryConjHom u) = _
  rw [unitaryConjHom_apply, ← hu, map_pow]

end BenderSuzuki.MatrixGroups.HermitianForm
