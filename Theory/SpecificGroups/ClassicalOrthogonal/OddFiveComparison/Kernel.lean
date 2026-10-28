/-
Copyright (c) 2026 Gerald Höhn and ATLAS contributors. All rights reserved.
Adapted from ATLAS, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
See also LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.SpecificGroups.ClassicalOrthogonal.OddFiveComparison.Action
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8.ExteriorKernel
public import Theory.SpecificGroups.PSp4Three.ProjectiveGeometry

/-!
# Exact kernel of the odd-five exterior representation

An element fixing the five-dimensional contraction kernel fixes all bivectors:
Pfaffian polarization recovers the remaining coordinates, and `2 ≠ 0` separates
the two contraction coordinates. The existing exterior kernel theorem then
forces the original matrix to be scalar. Conversely the center consists of
square-one scalars, which act trivially on the exterior square.

Adapted from ATLAS `LinearGroups/Orthogonal/B2ExteriorKernel.lean`,
`B2ExteriorScalar.lean`, and `B2ExteriorKernelExact.lean`. Reuse CFSG's existing
full exterior kernel and central-scalar proofs, and target its literal
quadratic isometry group. No image or group-order assertion is used.
Source: GLS3 §2.7, the odd B₂/C₂ comparison.
-/

@[expose] public noncomputable section
namespace ClassicalOrthogonal.OddFiveComparison
open Matrix Atlas.Order20160A8.Bivectors
variable {F : Type} [Field F]

theorem kernelMap_eq_of_toOrthogonal_eq_one (g : Matrix.PSp4Three.Sp 2 F)
    (hg : toOrthogonal g = 1) (w : LinearMap.ker (contraction (F := F))) :
    kernelMap g w = w := by
  have h := congrArg (fun z : Theory.AlgebraicGroup.quadraticIsometrySubgroup (formB 2 F) => z.val (kernelEquiv.symm w)) hg
  change kernelEquiv.symm (kernelMap g (kernelEquiv (kernelEquiv.symm w))) =
    kernelEquiv.symm w at h
  rw [LinearEquiv.apply_symm_apply] at h
  exact kernelEquiv.symm.injective h

theorem exteriorMap_eq_of_toOrthogonal_eq_one (h2 : (2 : F) ≠ 0)
    (g : Matrix.PSp4Three.Sp 2 F) (hg : toOrthogonal g = 1) (w : Six F) :
    exteriorMap (symplecticMatrix g) w = w := by
  let T := exteriorMap (symplecticMatrix g)
  have hk (b : Six F) (hb : contraction b = 0) : T b = b :=
    congrArg Subtype.val (kernelMap_eq_of_toOrthogonal_eq_one g hg ⟨b,hb⟩)
  have hp (b : Six F) (hb : contraction b = 0) :
      pfaffian (T w + b) - pfaffian (T w) = pfaffian (w + b) - pfaffian w := by
    conv_lhs => rw [← hk b hb, ← map_add]
    exact congrArg₂ (· - ·) (symplectic_pfaffian g (w+b)) (symplectic_pfaffian g w)
  have h0 := hp ![0,0,0,0,0,1] (by simp)
  have h5 := hp ![1,0,0,0,0,0] (by simp)
  have h2' := hp ![0,0,0,1,0,0] (by simp)
  have h3 := hp ![0,0,1,0,0,0] (by simp)
  have h14 := hp ![0,1,0,0,-1,0] (by simp)
  have hc := symplectic_contraction g w
  change T w 1 + T w 4 = w 1 + w 4 at hc
  simp [pfaffian_apply, Matrix.vecHead, Matrix.vecTail] at h0 h5 h2' h3 h14
  have he1 : T w 1 = w 1 := by
    apply (mul_left_cancel₀ h2)
    linear_combination h14 + hc
  have he4 : T w 4 = w 4 := by linear_combination hc - he1
  have he0 : T w 0 = w 0 := by linear_combination h0
  have he2 : T w 2 = w 2 := by linear_combination h2'
  have he3 : T w 3 = w 3 := by linear_combination h3
  have he5 : T w 5 = w 5 := by linear_combination h5
  change T w = w
  ext i
  fin_cases i <;> assumption

/-- The actual kernel consists of square-one scalar matrices, uniformly over odd fields. -/
theorem scalar_of_toOrthogonal_eq_one (h2 : (2 : F) ≠ 0)
    (g : Matrix.PSp4Three.Sp 2 F) (hg : toOrthogonal g = 1) :
    ∃ c : F, c ^ 2 = 1 ∧ symplecticMatrix g = c • 1 :=
  scalar_of_exteriorMap_eq_id (symplecticMatrix g)
    (exteriorMap_eq_of_toOrthogonal_eq_one h2 g hg)

omit [Field F] in
theorem symplecticCoordinates_injective :
    Function.Injective (symplecticCoordinates (F := F)) := by
  intro u v h
  rw [symplecticCoordinates_eq, symplecticCoordinates_eq] at h
  funext i
  have he := congrFun h ((finSumFinEquiv : Matrix.PSp4Three.Index 2 ≃ Fin 4) i)
  simpa only [Function.comp_apply, Equiv.symm_apply_apply] using he

theorem symplecticMatrix_scalar_action (g : Matrix.PSp4Three.Sp 2 F) (c : F)
    (hc : symplecticMatrix g = c • (1 : Matrix (Fin 4) (Fin 4) F)) :
    ∀ v : Matrix.PSp4Three.Vector 2 F, g • v = c • v := by
  intro v
  apply symplecticCoordinates_injective
  change symplecticCoordinates (g.val *ᵥ v) = symplecticCoordinates (c • v)
  rw [← symplecticMatrix_mulVec, hc, Matrix.smul_mulVec, Matrix.one_mulVec]
  funext j
  simp only [symplecticCoordinates_eq, Function.comp_apply, Pi.smul_apply]

theorem exteriorMap_scalar (c : F) :
    exteriorMap (c • (1 : Matrix (Fin 4) (Fin 4) F)) = c^2 • LinearMap.id := by
  apply exterior_ext
  intro u v
  rw [exteriorMap_wedge]
  ext i
  fin_cases i <;> simp [Matrix.smul_mulVec, wedge, pow_two] <;> ring

theorem toOrthogonal_eq_one_of_center (g : Matrix.PSp4Three.Sp 2 F)
    (hg : g ∈ Subgroup.center (Matrix.PSp4Three.Sp 2 F)) : toOrthogonal g = 1 := by
  obtain ⟨c, hcg⟩ := Matrix.PSp4Three.central_is_scalar g hg
  have hs := Matrix.PSp4Three.preserves g (Matrix.PSp4Three.e 0) (Matrix.PSp4Three.f 0)
  rw [← Matrix.PSp4Three.smul_eq_mulVec, ← Matrix.PSp4Three.smul_eq_mulVec, hcg, hcg] at hs
  have hc : c ^ 2 = 1 := by
    simpa [map_smul, Matrix.PSp4Three.e, Pi.single_apply, pow_two] using hs
  have hm : symplecticMatrix g = c • (1 : Matrix (Fin 4) (Fin 4) F) := by
    apply Matrix.ext_of_mulVec_single
    intro i
    obtain ⟨v, hv⟩ := symplecticCoordinates_surjective (F := F) (Pi.single i 1)
    rw [← hv, symplecticMatrix_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    change symplecticCoordinates (g • v) = c • symplecticCoordinates v
    rw [hcg]
    funext j
    simp only [symplecticCoordinates_eq, Function.comp_apply, Pi.smul_apply]
  have he : exteriorMap (symplecticMatrix g) = LinearMap.id := by
    rw [hm, exteriorMap_scalar, hc, one_smul]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  change kernelEquiv.symm (kernelMap g (kernelEquiv v)) = v
  have hk : kernelMap g (kernelEquiv v) = kernelEquiv v := by
    apply Subtype.ext
    change exteriorMap (symplecticMatrix g) (kernelEquiv v).val = _
    rw [he, LinearMap.id_apply]
  rw [hk, LinearEquiv.symm_apply_apply]
/-- The exact scalar-center kernel, proved through the actual exterior-square matrices. -/
theorem toOrthogonal_eq_one_iff_center (h2 : (2 : F) ≠ 0)
    (g : Matrix.PSp4Three.Sp 2 F) :
    toOrthogonal g = 1 ↔ g ∈ Subgroup.center (Matrix.PSp4Three.Sp 2 F) := by
  constructor
  · intro hg
    obtain ⟨c, _, hc⟩ := scalar_of_toOrthogonal_eq_one h2 g hg
    exact Matrix.PSp4Three.scalar_is_central g c (symplecticMatrix_scalar_action g c hc)
  · exact toOrthogonal_eq_one_of_center g

/-- Equality of actual subgroups, not merely their orders. -/
theorem toOrthogonal_kernel (h2 : (2 : F) ≠ 0) :
    (toOrthogonal (F := F)).ker = Subgroup.center (Matrix.PSp4Three.Sp 2 F) := by
  ext g
  exact toOrthogonal_eq_one_iff_center h2 g

/-- The genuine exterior representation descends through the matrix center. -/
def fromPSp (h2 : (2 : F) ≠ 0) : Matrix.PSp4Three.PSp 2 F →*
    Theory.AlgebraicGroup.quadraticIsometrySubgroup (formB 2 F) :=
  QuotientGroup.lift _ toOrthogonal (by rw [toOrthogonal_kernel h2])

/-- On every matrix lift this is the original exterior action. -/
theorem fromPSp_projection (h2 : (2 : F) ≠ 0) (g : Matrix.PSp4Three.Sp 2 F) :
    fromPSp h2 (QuotientGroup.mk g) = toOrthogonal g := rfl

/-- Exactness, rather than an order comparison, makes the descended action faithful. -/
theorem fromPSp_injective (h2 : (2 : F) ≠ 0) : Function.Injective (fromPSp h2) :=
  (QuotientGroup.injective_lift_iff _ _ _).mpr (toOrthogonal_kernel h2).symm

end ClassicalOrthogonal.OddFiveComparison
