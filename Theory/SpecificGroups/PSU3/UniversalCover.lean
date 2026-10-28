module

public import Theory.SpecificGroups.PSU3.UniversalCover.Projection
public import Theory.GroupTheory.CoveringKernelBound

/-!
# Canonical PSU₃ coverings and the remaining multiplier bound

This module exports the actual finite quasisimple covering SU(J) → PSU(J)
and its kernel equivalences with `C₃` or `C₁`. A bound of `gcd(3,q+1)` on
the constructed universal kernel forces this covering to be universal.
The resulting lift theorem retains the literal matrix projection and applies
to any finite quasisimple cover, including covers in another universe.

The numerical upper bound remains an explicit premise. The characteristic-two
and odd prime/prime-square bounds must be proved before these conditional
results establish the corresponding source multiplier rows. Neither the scalar
kernel calculation nor quasisimplicity supplies that missing upper bound.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, I.1.1,
I.1.3(2), I.1.4(2), printed pp.407–408 (PDF pp.418–419), with the family
restrictions of A.2.2–3; GLS3, Theorem 6.1.4 and Tables 6.1.2–3.
-/

public section

open Matrix Subgroup BenderSuzuki.MatrixGroups Theory.GroupTheory
namespace BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover
universe u w
variable {F : Type u} [Field F] [Finite F] (J : HermitianForm 3 F)

/-- The numerical upper bound turns the canonical matrix covering into a
universal covering, in every target universe. -/
theorem covering_isUniversal_of_kernel_bound {q : ℕ} (hq : 2 < q)
    (hcard : Nat.card F = q ^ 2) (hconj : ∀ x, J.conj x = x ^ q)
    (hbound : Nat.card (PerfectCentralCovering.universalProjection
      (ProjectiveSpecialUnitaryMatrixGroup J)).ker ≤ Nat.gcd 3 (q + 1)) :
    let _ := special_isQuasisimple J hq hcard hconj
    let _ := projective_isQuasisimple J hq hcard hconj
    Covering.IsUniversal.{u,u,w} (covering J) := by
  let := special_isQuasisimple J hq hcard hconj
  let := projective_isQuasisimple J hq hcard hconj
  apply Covering.isUniversal_of_kernel_card_le (covering J)
  simpa only [covering_toMonoidHom, card_kernel J hcard hconj] using hbound

/-- Application to an arbitrary finite quasisimple cover of the actual
projective image. The lifted map commutes with the literal projection. -/
theorem exists_lift_of_kernel_bound {q : ℕ} (hq : 2 < q)
    (hcard : Nat.card F = q ^ 2) (hconj : ∀ x, J.conj x = x ^ q)
    (hbound : Nat.card (PerfectCentralCovering.universalProjection
      (ProjectiveSpecialUnitaryMatrixGroup J)).ker ≤ Nat.gcd 3 (q + 1))
    {M : Type w} [Group M] [Finite M] [IsQuasisimple M]
    (f : M →* ProjectiveSpecialUnitaryMatrixGroup J) (hf : Function.Surjective f) :
    ∃ g : J.specialSubgroup →* M,
      Function.Surjective g ∧ f.comp g = J.specialToProjective := by
  let := special_isQuasisimple J hq hcard hconj
  let := projective_isQuasisimple J hq hcard hconj
  let fc : Covering M (ProjectiveSpecialUnitaryMatrixGroup J) := ⟨f, hf⟩
  obtain ⟨g, hg, _⟩ := covering_isUniversal_of_kernel_bound J hq hcard hconj hbound M fc
  refine ⟨g.toMonoidHom, g.surjective, ?_⟩
  simpa only [Covering.comp_toMonoidHom, covering_toMonoidHom] using
    congrArg Covering.toMonoidHom hg

end BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover
