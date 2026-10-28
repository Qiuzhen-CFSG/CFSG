module

public import Theory.SpecificGroups.ClassicalUnitary.FiveIsotropicTransitivity.Coordinates
public import Theory.SpecificGroups.ClassicalUnitary.FiveIsotropicTransitivity.Determinant
public import Theory.SpecificGroups.ClassicalUnitary.FiveIsotropicTransitivity.LineBasis
public import Theory.SpecificGroups.ClassicalUnitary.FiveIsotropicTransitivity.PlaneBasis
public import Theory.SpecificGroups.ClassicalUnitary.FiveIsotropicGeometry

/-!
# Special-unitary transitivity on isotropic subspaces in dimension five

Comparing an adapted basis with the explicit reference basis gives a genuine
unitary isometry. Correcting its determinant on the last coordinate gives
an element of the exact special unitary group with the same subspace image.
The dimension bound reduces transitivity to lines and planes. Over the field
of sixteen elements with fourth-power conjugation, the proved adapted-basis
constructions discharge both cases. Thus every nonzero totally isotropic
subspace is the special-unitary image of the standard line or plane.

Source: GLS3, Lemmas 2.7.1–2, printed pp.89–90, in
`refs/KGroup/GLS3/chapter2.tex`. The intended application is the parabolic
geometry for Aschbacher–Smith, Theorem 0.1.2(1), printed p.4, and F.1.12(7),
printed pp.263–264, in `refs/quasithin.pdf`.
-/

public section

open Matrix BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.UnitaryFive.IsotropicTransitivity
variable {F : Type*} [Field F] (J : HermitianForm 5 F)
variable [CharP F 2]

/-- An adapted basis with the specified Gram matrix gives the required actual
SU transport. Existence of the adapted basis is a separate geometric assertion. -/
theorem special_image_of_adapted_basis (hJ : J.form = 1) (b : Bool)
    (W : Submodule F (Fin 5 → F)) (P : GL (Fin 5) F)
    (hP : J.conjTranspose P.val * P.val = referenceGram b)
    (hW : W = (coordinateSubspace F b).map P.val.mulVecLin) :
    ∃ g : J.specialSubgroup,
      W = (if b then plane F else line F).map (linearAction J g).toLinearMap := by
  let C : GL (Fin 5) F := referenceGL b
  have hPC : J.conjTranspose P.val * P.val = J.conjTranspose C.val * C.val :=
    hP.trans (referenceMatrix_gram J b).symm
  obtain ⟨g, hg⟩ := special_image_of_unitary J hJ b (P * C⁻¹)
    (unitary_of_same_gram J hJ P C hPC)
  refine ⟨g, ?_⟩
  rw [← hg, ← referenceMatrix_map]
  rw [← Submodule.map_comp]
  have he : (P * C⁻¹).val.mulVecLin.comp (referenceMatrix b).mulVecLin =
      P.val.mulVecLin := by
    rw [← mulVecLin_mul]
    change ((P.val * (C⁻¹).val) * C.val).mulVecLin = P.val.mulVecLin
    rw [mul_assoc, Units.inv_mul, mul_one]
  rw [he]
  exact hW

/-- The two adapted-basis existence assertions supply SU transitivity.
This conditional assembly does not assert those geometric existence results. -/
theorem transitive_of_adapted_bases [Finite F] (hJ : J.form = 1)
    (hline : ∀ W : Submodule F (Fin 5 → F), Module.finrank F W = 1 →
      W ≤ IsotropicGeometry.orthogonal J W → HasAdaptedBasis J false W)
    (hplane : ∀ W : Submodule F (Fin 5 → F), Module.finrank F W = 2 →
      W ≤ IsotropicGeometry.orthogonal J W → HasAdaptedBasis J true W)
    (W : Submodule F (Fin 5 → F)) (hne : W ≠ ⊥)
    (hW : W ≤ IsotropicGeometry.orthogonal J W) :
    ∃ (b : Bool) (g : J.specialSubgroup),
      W = (if b then plane F else line F).map (linearAction J g).toLinearMap := by
  rcases IsotropicGeometry.finrank_one_or_two J W hne hW with hd | hd
  · obtain ⟨P, hP, hPW⟩ := hline W hd hW
    obtain ⟨g, hg⟩ := special_image_of_adapted_basis J hJ false W P hP hPW
    exact ⟨false, g, hg⟩
  · obtain ⟨P, hP, hPW⟩ := hplane W hd hW
    obtain ⟨g, hg⟩ := special_image_of_adapted_basis J hJ true W P hP hPW
    exact ⟨true, g, hg⟩

/-- Every nonzero totally isotropic subspace of the identity-form five-space
over the field of sixteen elements is an actual special-unitary image of the
standard line or plane. Both adapted-basis existence premises are discharged. -/
theorem transitive [Finite F] (hcard : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x ^ 4) (hJ : J.form = 1)
    (W : Submodule F (Fin 5 → F)) (hne : W ≠ ⊥)
    (hW : W ≤ IsotropicGeometry.orthogonal J W) :
    ∃ (b : Bool) (g : J.specialSubgroup),
      W = (if b then plane F else line F).map (linearAction J g).toLinearMap := by
  exact transitive_of_adapted_bases J hJ
    (hasAdaptedBasis_line J hcard hconj hJ)
    (hasAdaptedBasis_plane J hcard hconj hJ) W hne hW

end Theory.SpecificGroups.UnitaryFive.IsotropicTransitivity
