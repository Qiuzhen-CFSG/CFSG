module

public import Theory.SpecificGroups.SU3.OddInvolutionNormalization
public import Theory.SpecificGroups.SU3.OrthogonalFixed

/-!
# Outer involution fixed groups for odd-prime PSU₃

Normalize an outer involution using a genuine projective group equivalence,
then restrict the fixed matrices to the original Hermitian involution's fixed
field. This identifies the full fixed group with the ternary special orthogonal
group, for every odd prime including three and every nondegenerate Gram matrix.

Source: GLS3, §§2.7 and 4.3; Aschbacher–Smith E.6.18, printed p.252,
and Theorem C, printed p.33.
-/

public section
namespace BenderSuzuki.MatrixGroups.HermitianForm.OddInvolutionNormalization
open OddPrimeSylow
variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)

/-- The whole fixed group of an outer involution is the actual fixed-field
ternary special orthogonal group. -/
theorem fixed_equiv_orthogonal
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hcard : Nat.card E = p ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = p)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (ha : a ^ 2 = 1) (houter : ¬ ∃ k, a = MulAut.conj k) :
    Nonempty (a.fixedSubgroup ≃*
      (splitOrthogonalForm (FixedBy.subfield E J.conj)).specialSubgroup) := by
  obtain ⟨J₀, e, hconj, hform, hentry⟩ := normalized_outer J hp ho hcard hfixed a ha houter
  let f := (MulAut.fixedSubgroupCongr e a).trans
    (projectiveFixedEquivOrthogonal J₀ hform hentry)
  have transport (σ τ : E ≃+* E) (h : σ = τ) :
      (splitOrthogonalForm (FixedBy.subfield E σ)).specialSubgroup ≃*
        (splitOrthogonalForm (FixedBy.subfield E τ)).specialSubgroup := by
    subst τ
    exact MulEquiv.refl _
  exact ⟨f.trans (transport _ _ hconj)⟩

end BenderSuzuki.MatrixGroups.HermitianForm.OddInvolutionNormalization
