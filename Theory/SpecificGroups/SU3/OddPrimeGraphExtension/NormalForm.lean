module
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Coverage
public import Theory.SpecificGroups.SU3.CyclicNormalOuter

/-!
# The cubic-diagonal normal form for odd-prime projective unitary automorphisms

The actual semilinear coverage theorem gives field part identity or the
stored quadratic conjugation. Unitary conjugation has outer cube one.
Consequently the literal outer quotient is a three-subgroup together with
its coset by entrywise conjugation. This is the input to outer Sylow
alignment in the ambient graph-extension construction.

Source: GLS3 2.5.12 and 2.7; Aschbacher–Smith F.6.18(11), printed p.310.
-/

public noncomputable section
open Matrix Subgroup
namespace BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeGraphExtension
open OddPrimeSylow.NormalizedOuter
variable {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)

omit [Finite F] in
lemma unitary_outer_is_three : IsPGroup 3 J.unitaryOuterHom.range := by
  intro x
  refine ⟨1, Subtype.ext ?_⟩
  obtain ⟨u, hu⟩ := x.property
  change (x : MulAut.Outer (ProjectiveSpecialUnitaryMatrixGroup J)) ^ (3 ^ 1) = 1
  rw [pow_one, ← hu]
  change (QuotientGroup.mk' (MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (J.unitaryConjHom u)) ^ 3 = 1
  rw [J.unitaryConjHom_apply]
  rw [← map_pow]
  obtain ⟨y, hy⟩ := J.unitaryConj_cube_is_inner u
  rw [hy]
  exact (QuotientGroup.eq_one_iff _).mpr ⟨y, rfl⟩

lemma outer_normal_form
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    {p : ℕ} (hp : p.Prime) (hp8 : p % 8 = 3)
    (hcard : Nat.card F = p ^ 2)
    (hfixed : Nat.card {x : F // J.conj x = x} = p)
    (γ : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hγ : J.IsEntrywiseConjugation γ) :
    ∀ x : MulAut.Outer (ProjectiveSpecialUnitaryMatrixGroup J),
      ∃ d ∈ J.unitaryOuterHom.range, x = d ∨
        x = d * QuotientGroup.mk' (MulAut.innerSubgroup _) γ := by
  intro x
  let q := QuotientGroup.mk' (MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J))
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective _ x
  obtain ⟨σ, hσ⟩ := Coverage.semilinear_coverage J hJ hp hp8 hcard hfixed a
  rcases fieldAut_eq_one_or_conj J hp hcard hfixed σ with rfl | rfl
  · obtain ⟨u, hu⟩ := (HasUnitarySemilinearForm.one_iff J).mp hσ
    refine ⟨q (J.unitaryConj u), ⟨u, congrArg q (J.unitaryConjHom_apply u)⟩, .inl ?_⟩
    exact congrArg q hu
  · obtain ⟨u, hu⟩ := (HasUnitarySemilinearForm.conj_iff J hγ).mp hσ
    refine ⟨q (J.unitaryConj u), ⟨u, congrArg q (J.unitaryConjHom_apply u)⟩, .inr ?_⟩
    rw [hu, map_mul]

end BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeGraphExtension
