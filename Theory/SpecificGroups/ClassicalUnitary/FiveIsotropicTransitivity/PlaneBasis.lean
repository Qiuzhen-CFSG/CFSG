module

public import Theory.SpecificGroups.ClassicalUnitary.FiveIsotropicTransitivity.Coordinates
public import Theory.SpecificGroups.ClassicalUnitary.FiveIsotropicGeometry
public import Theory.SpecificGroups.ClassicalUnitary.FiveIsotropicTransitivity.PlaneBasis.Complement

/-!
# Adapted bases for isotropic planes in unitary five-space

Every totally isotropic plane over the field of sixteen elements has a basis
whose Gram matrix is the specified two-block reference matrix. Dual partners
are adjusted using trace surjectivity, and the perpendicular complement is
normalized using norm surjectivity. Columns zero and two are a basis of the
original plane, giving exactly the required coordinate-subspace image.

This constructs the plane case of the Hermitian Witt-extension argument in
GLS3 Lemma 2.7.1, printed p.89, `refs/KGroup/GLS3/chapter2.tex`. Determinant-one
correction and the line case belong to the transitivity assembly.
-/

public section

open Matrix Module BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.UnitaryFive.IsotropicGeometry
namespace Theory.SpecificGroups.UnitaryFive.IsotropicTransitivity
open PlaneBasis
variable {F : Type*} [Field F]

/-- Every totally isotropic plane admits the published reference Gram matrix,
with its two isotropic basis vectors in columns zero and two. -/
theorem hasAdaptedBasis_plane [Finite F] [CharP F 2] (J : HermitianForm 5 F)
    (hcard : Nat.card F = 16) (hconj : ∀ x, J.conj x = x ^ 4)
    (_hJ : J.form = 1) (W : Submodule F (Fin 5 → F))
    (hd : Module.finrank F W = 2) (hi : W ≤ orthogonal J W) :
    HasAdaptedBasis J true W := by
  classical
  obtain ⟨e, v, hv0, hv2, hv⟩ := exists_plane_frame J hcard hconj W hd hi
  obtain ⟨z, hzz, hz⟩ := exists_complement_unit J hcard hconj v hv
  have hzne : z ≠ 0 := by
    intro hh
    rw [hh, pair_zero_left] at hzz
    exact zero_ne_one hzz
  obtain ⟨P, hP⟩ := completeMatrix_isUnit J v hv z hz hzne
  refine ⟨P, ?_, ?_⟩
  · rw [hP]
    exact completeMatrix_gram J v hv z hzz hz
  · rw [hP]
    ext w
    constructor
    · intro hw
      let w' : W := ⟨w, hw⟩
      refine ⟨![e.repr w' 0, 0, e.repr w' 1, 0, 0], ?_, ?_⟩
      · simp [coordinateSubspace]
      · change completeMatrix v z *ᵥ _ = w
        have he := congrArg Subtype.val (e.sum_repr w')
        simp [completeMatrix_mulVec, hv0, hv2]
        simpa only [Fin.sum_univ_two, Submodule.coe_add, Submodule.coe_smul] using he
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨h1, h3, h4, _⟩ := hx
      change completeMatrix v z *ᵥ x ∈ W
      rw [completeMatrix_mulVec, h1, h3, h4]
      simpa [hv0, hv2] using
        W.add_mem (W.smul_mem (x 0) (e 0).property) (W.smul_mem (x 2) (e 1).property)

end Theory.SpecificGroups.UnitaryFive.IsotropicTransitivity
