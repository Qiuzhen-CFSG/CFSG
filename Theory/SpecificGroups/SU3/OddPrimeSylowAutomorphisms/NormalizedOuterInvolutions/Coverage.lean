module

public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Coverage.RootSylow
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.SemilinearReduction
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Coverage.Geometry
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Coverage.RootRigidity

/-!
# Semilinear coverage for odd-prime projective SU₃

A semilinear formula on the two explicit root groups extends to the whole
projective image when those groups generate it. Multiplication by an inner
automorphism preserves the formula, using an actual special-unitary lift of
the conjugating projective element. Thus geometric normalization to the two
root groups and rigidity on their coordinates suffice for coverage.

The final theorem discharges the geometric and coordinate hypotheses using
`Geometry` and `RootRigidity`. Every automorphism of the actual projective
image over a field of order `p²`, with `p % 8 = 3`, therefore has a semilinear
formula with an actual unitary representative. In particular this covers
outer involutions, including `p = 3`.

This is the prime-field SU₃ case of Steinberg's Theorem 36
(`refs/KGroup/GLS3/Chapter2St1.tex`, proof steps (1)–(7)), underlying GLS3,
Theorem 2.5.12(a,d,f), and its actual PSU/PGU identification in §2.7.
The explicit simplicity hypothesis is used only for root-group generation;
perfectness is not needed.
-/

open Matrix BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.Coverage
variable {E : Type*} [Field E] (J : HermitianForm 3 E)

/-- Inner multiplication preserves a concrete unitary-semilinear formula.
The new unitary representative is the product of an actual special-unitary
lift with the supplied unitary matrix. -/
public theorem semilinearForm_conj_mul
    (k : ProjectiveSpecialUnitaryMatrixGroup J)
    {a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)} {σ : E ≃+* E}
    (hsem : J.HasUnitarySemilinearForm a σ) :
    J.HasUnitarySemilinearForm (MulAut.conj k * a) σ := by
  obtain ⟨x, rfl⟩ := J.specialToProjective_surjective k
  obtain ⟨u, hu⟩ := hsem
  let v : J.unitarySubgroup := ⟨x.val, x.property.1⟩
  refine ⟨v * u, fun b => ?_⟩
  change (J.specialToProjective x).val * (a b).val *
    (J.specialToProjective x).val⁻¹ = _
  rw [hu, J.specialToProjective_apply_val]
  change _ = ProjGenLinGroup.mk (x.val * u.val) *
    ProjGenLinGroup.map σ.toRingHom b.val * (ProjGenLinGroup.mk (x.val * u.val))⁻¹
  simp only [map_mul, _root_.mul_inv_rev]
  group

variable (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])

/-- The two concrete root formulas extend through generation in the actual
projective image. No automorphism classification is used in this step. -/
public theorem semilinearForm_of_root_formulas
    (hgen : rootGroup J hJ ⊔ oppositeRootGroup J hJ = ⊤)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (σ : E ≃+* E) (u : J.unitarySubgroup)
    (hroot : ∀ z : hermitianUnipotentCoord J,
      (a (root J hJ z)).val = ProjGenLinGroup.mk u.val *
        ProjGenLinGroup.map σ.toRingHom (root J hJ z).val *
        (ProjGenLinGroup.mk u.val)⁻¹)
    (hopposite : ∀ z : hermitianUnipotentCoord J,
      (a (oppositeRoot J hJ z)).val = ProjGenLinGroup.mk u.val *
        ProjGenLinGroup.map σ.toRingHom (oppositeRoot J hJ z).val *
        (ProjGenLinGroup.mk u.val)⁻¹) :
    J.HasUnitarySemilinearForm a σ := by
  let f : ProjectiveSpecialUnitaryMatrixGroup J →* ProjGenLinGroup (Fin 3) E :=
    (ProjectiveSpecialUnitaryMatrixGroup J).subtype.comp a.toMonoidHom
  let g : ProjectiveSpecialUnitaryMatrixGroup J →* ProjGenLinGroup (Fin 3) E :=
    (MulAut.conj (ProjGenLinGroup.mk u.val)).toMonoidHom.comp
      ((ProjGenLinGroup.map σ.toRingHom).comp
        (ProjectiveSpecialUnitaryMatrixGroup J).subtype)
  have heq : f = g := hom_ext_of_rootGroup_sup_eq_top J hJ hgen f g hroot hopposite
  exact ⟨u, fun b => DFunLike.congr_fun heq b⟩

/-- Conditional coverage assembly. Its geometric normalization and coordinate
rigidity inputs must be proved before obtaining the source theorem. -/
public theorem semilinear_coverage_of_root_geometry
    (hgen : rootGroup J hJ ⊔ oppositeRootGroup J hJ = ⊤)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hnormalize : ∃ (k : ProjectiveSpecialUnitaryMatrixGroup J)
        (b : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)),
      a = MulAut.conj k * b ∧
      (rootGroup J hJ).map b.toMonoidHom = rootGroup J hJ ∧
      (oppositeRootGroup J hJ).map b.toMonoidHom = oppositeRootGroup J hJ)
    (hrigid : ∀ b : MulAut (ProjectiveSpecialUnitaryMatrixGroup J),
      (rootGroup J hJ).map b.toMonoidHom = rootGroup J hJ →
      (oppositeRootGroup J hJ).map b.toMonoidHom = oppositeRootGroup J hJ →
      ∃ (σ : E ≃+* E) (u : J.unitarySubgroup),
        (∀ z : hermitianUnipotentCoord J,
          (b (root J hJ z)).val = ProjGenLinGroup.mk u.val *
            ProjGenLinGroup.map σ.toRingHom (root J hJ z).val *
            (ProjGenLinGroup.mk u.val)⁻¹) ∧
        (∀ z : hermitianUnipotentCoord J,
          (b (oppositeRoot J hJ z)).val = ProjGenLinGroup.mk u.val *
            ProjGenLinGroup.map σ.toRingHom (oppositeRoot J hJ z).val *
            (ProjGenLinGroup.mk u.val)⁻¹)) :
    ∃ σ : E ≃+* E, J.HasUnitarySemilinearForm a σ := by
  obtain ⟨k, b, rfl, hroot, hopposite⟩ := hnormalize
  obtain ⟨σ, u, hu, hv⟩ := hrigid b hroot hopposite
  exact ⟨σ, semilinearForm_conj_mul J k
    (semilinearForm_of_root_formulas J hJ hgen b σ u hu hv)⟩

include hJ in
/-- Every automorphism of the actual projective SU₃ image has a unitary
semilinear formula when the fixed field has prime order `p ≡ 3 (mod 8)`.
The conclusion supplies a field automorphism and a genuine unitary matrix;
no automorphism classification or semilinearity premise is assumed.
This includes the outer-involution case and retains `p = 3`. -/
public theorem semilinear_coverage [Finite E]
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    {p : ℕ} (hp : p.Prime) (hp8 : p % 8 = 3)
    (hcard : Nat.card E = p ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = p)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ∃ σ : E ≃+* E, J.HasUnitarySemilinearForm a σ := by
  exact semilinear_coverage_of_root_geometry J hJ
    (rootGroup_sup_oppositeRootGroup J hJ hp.one_lt hcard hfixed) a
    (exists_root_pair_normalization J hJ hp hcard hfixed a)
    (root_formulas_of_opposite_root_preserving J hJ hp hp8 hcard)

end BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.Coverage
