module
public import Theory.SpecificGroups.SU3.CyclicNormalOuter.PrimeSquares

/-!
# Cubic diagonal automorphisms of prime-field PSU₃

The coefficient field has prime-square order. Squaring an automorphism
therefore removes its field parameter. If the original actor has cube one,
squaring again recovers it, giving an actual unitary conjugating matrix.
The literal nonblock quotient application is in
`NonblockEndgameSieveCubicAction`.

Source: GLS3 Theorem 2.5.12 and §2.7; Aschbacher–Smith A.3.18,
printed pp.51–53, and original 4.3.12(2), printed p.617.
-/

public section
open Subgroup Matrix BenderSuzuki.MatrixGroups
namespace BenderSuzuki.MatrixGroups.HermitianForm
variable {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)

/-- A cubic automorphism over an odd prime fixed field is induced by a unitary matrix. -/
theorem cubic_mem_unitary_of_odd_prime
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    {r : ℕ} (hr : r.Prime) (ho : Odd r)
    (hcard : Nat.card F = r^2)
    (hfixed : Nat.card {x : F // J.conj x=x} = r)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (ha : a^3=1) :
    a ∈ J.unitaryConjHom.range := by
  obtain ⟨σ,hσ⟩ := OddPrimeSylow.NormalizedOuter.Coverage.semilinear_coverage_odd
    J hJ hr ho hcard hfixed a
  have hs : σ^2=1 := FiniteField.ringAut_sq_of_card_prime_pow hr (by decide) hcard σ
  have hb : J.HasUnitarySemilinearForm (a^2) 1 := by
    simpa only [←pow_two,hs] using hσ.mul J hJ hσ
  obtain ⟨u,hu⟩ := (HasUnitarySemilinearForm.one_iff J).mp hb
  refine ⟨u^2,?_⟩
  rw [map_pow,J.unitaryConjHom_apply,←hu,←pow_mul,show 2*2=3+1 from rfl,
    pow_succ,ha,one_mul]
end BenderSuzuki.MatrixGroups.HermitianForm
