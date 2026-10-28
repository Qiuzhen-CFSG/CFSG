/-
Uses Gerald Höhn's retained ATLAS icosian coordinates, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917. Distributed under the ATLAS
Research and Attribution License 1.0; see LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianScalarIsometries
public import Theory.AtlasPort.OtherSporadic.Conway.LeechCentralQuotient

/-!
# A semilinear isometry of the actual icosian Leech lattice

On each golden quaternion, multiply field conjugation by τ and apply the
rotation i ↦ -i, j ↦ k, k ↦ j. On rational coefficients this is a signed
permutation; its square is minus the identity. The explicit integral basis
formula and the 36 existing glue generators prove lattice preservation.
The retained comparison then gives actual Co₀ and Co₁ elements.

This module establishes the isometry, including its semilinear matrix rule.
Its scalar action is a separate calculation. The source application is
Aschbacher, *Sporadic Groups* (1994), 48.3(3), pp.268–269, and the normalizer
step of 49.5, p.284. The construction uses the attributed lattice model
rather than an assumed source root-subgroup identification.
-/

open Atlas.Algebra Atlas.Lattices Atlas.Conway
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.Outer

set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
local instance : DecidableEq IcosianQuaternion := fun a b =>
  decidable_of_iff (a.re = b.re ∧ a.imI = b.imI ∧ a.imJ = b.imJ ∧ a.imK = b.imK)
    QuaternionAlgebra.ext_iff.symm

def rotate (a : GoldenRational) : GoldenRational := ⟨-a.im, a.re⟩

def twistQuaternion (q : IcosianQuaternion) : IcosianQuaternion :=
  ⟨rotate q.re, -rotate q.imI, rotate q.imK, rotate q.imJ⟩

/-- Golden-field conjugation combined with the rotation i ↦ -i, j ↦ k, k ↦ j. -/
def sigmaQuaternion (q : IcosianQuaternion) : IcosianQuaternion :=
  ⟨⟨q.re.re + q.re.im, -q.re.im⟩,
    ⟨-q.imI.re - q.imI.im, q.imI.im⟩,
    ⟨q.imK.re + q.imK.im, -q.imK.im⟩,
    ⟨q.imJ.re + q.imJ.im, -q.imJ.im⟩⟩

theorem twistQuaternion_add (q r : IcosianQuaternion) :
    twistQuaternion (q + r) = twistQuaternion q + twistQuaternion r := by
  ext <;> simp [twistQuaternion, rotate, add_comm]

theorem twistQuaternion_mul (q r : IcosianQuaternion) :
    twistQuaternion (q * r) = sigmaQuaternion q * twistQuaternion r := by
  ext <;> simp [twistQuaternion, sigmaQuaternion, rotate,
    Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul] <;> ring

def twist : IcosianRationalCoordinates ≃ₗ[ℚ] IcosianRationalCoordinates where
  toFun v i := twistQuaternion (v i)
  invFun v i := -twistQuaternion (v i)
  left_inv v := by funext i; ext <;> simp [twistQuaternion, rotate]
  right_inv v := by funext i; ext <;> simp [twistQuaternion, rotate]
  map_add' v w := by funext i; ext <;> simp [twistQuaternion, rotate, Pi.add_apply, add_comm]
  map_smul' a v := by funext i; ext <;> simp [twistQuaternion, rotate, Pi.smul_apply]

theorem twist_mulVec (M : Matrix (Fin 3) (Fin 3) IcosianQuaternion)
    (v : IcosianRationalCoordinates) :
    twist (M.mulVec v) = (show Matrix (Fin 3) (Fin 3) IcosianQuaternion from fun i j => sigmaQuaternion (M i j)).mulVec (twist v) := by
  funext i
  change twistQuaternion (M.mulVec v i) = _
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, twistQuaternion_add, twistQuaternion_mul]
  rfl

theorem twist_twice (v : IcosianRationalCoordinates) : twist (twist v) = -v := by
  funext i
  ext <;> simp [twist, twistQuaternion, rotate]

theorem twist_bilinear (v w : IcosianRationalCoordinates) :
    icosianBilinear (twist v) (twist w) = icosianBilinear v w := by
  simp [icosianBilinear_eq_dot, icosianRealCoordinates, icosianQuaternionCoordinate,
    dotProduct, Fintype.sum_prod_type, Fin.sum_univ_succ, twist, twistQuaternion, rotate]
  ring

/-- Integral basis coordinates for the coefficient rotation. -/
def twistCoefficients (a : Fin 4 → GoldenInteger) : Fin 4 → GoldenInteger :=
  ![⟨-(a 0).im - (a 2).re - 2*(a 2).im + (a 3).im,
      (a 0).re + (a 2).re + (a 2).im - (a 3).re⟩,
    ⟨(a 1).im + (a 2).im + (a 3).re + 2*(a 3).im,
      -(a 1).re - (a 2).re - (a 3).re - (a 3).im⟩,
    ⟨-(a 3).re - 2*(a 3).im, (a 3).re + (a 3).im⟩,
    ⟨-(a 2).re - 2*(a 2).im, (a 2).re + (a 2).im⟩]

theorem twist_synthesis (a : Fin 4 → GoldenInteger) :
    (icosianIntegralSynthesis (twistCoefficients a)).val =
      twistQuaternion (icosianIntegralSynthesis a).val := by
  ext <;> simp [icosianIntegralSynthesis, icosianBasisSynthesis, twistCoefficients,
    goldenIntegerToRational, icosianI, icosianGenerator, twistQuaternion, rotate] <;> ring

private def imageGenerator (j : Fin 36) : IcosianCoordinates := fun i =>
  icosianIntegralSynthesis (twistCoefficients (icosianComparisonSourceCoefficients j i))

private theorem imageGenerator_value (j : Fin 36) :
    icosianCoordinateEmbedding (imageGenerator j) =
      twist (icosianCoordinateEmbedding (icosianComparisonSourceGenerator j)) := by
  funext i
  exact twist_synthesis _

private theorem imageGenerator_mem (j : Fin 36) : imageGenerator j ∈ icosianLeechModule := by
  rw [icosianLeechModule_mem, icosianP_mem, icosianP_mem, icosianPZero_mem]
  simp only [imageGenerator, map_sub, map_add,
    icosianModuloTwo_synthesis, Matrix.sub_apply, Matrix.add_apply]
  revert j
  decide +kernel

theorem twist_lattice {v : IcosianRationalCoordinates} (hv : v ∈ rationalIcosianLattice) :
    twist v ∈ rationalIcosianLattice := by
  obtain ⟨x, hx, rfl⟩ := hv
  let S : Submodule ℤ IcosianCoordinates := rationalIcosianLattice.comap
    ((twist.toLinearMap.restrictScalars ℤ).comp icosianCoordinateEmbedding)
  apply icosianLeechModule_le_of_generators S _ hx
  intro j
  exact ⟨imageGenerator j, imageGenerator_mem j, imageGenerator_value j⟩

theorem twist_lattice_iff (v : IcosianRationalCoordinates) :
    v ∈ rationalIcosianLattice ↔ twist v ∈ rationalIcosianLattice := by
  refine ⟨twist_lattice, fun hv => ?_⟩
  have h := twist_lattice hv
  rw [twist_twice] at h
  exact (Submodule.neg_mem_iff _).mp h

def twistRational : rationalLatticeIsometries :=
  ⟨Atlas.LinearAlgebra.linearAutomorphismCongr icosianComparison twist, by
    constructor
    · intro x y
      change rationalForm (icosianComparison (twist (icosianComparison.symm x)))
        (icosianComparison (twist (icosianComparison.symm y))) = _
      rw [icosianComparison_isometry]
      rw [twist_bilinear]
      simpa only [LinearEquiv.apply_symm_apply] using
        (icosianComparison_isometry (icosianComparison.symm x)
          (icosianComparison.symm y)).symm
    · intro x
      change x ∈ rationalLeech ↔
        icosianComparison (twist (icosianComparison.symm x)) ∈ rationalLeech
      rw [← icosianComparison_lattice_iff, ← twist_lattice_iff]
      simpa only [icosianComparison.apply_symm_apply] using
        (icosianComparison_lattice_iff (icosianComparison.symm x)).symm⟩

def twistCo0 : LeechIsometryGroup := fullIsometryEquiv.symm twistRational

theorem twistCo0_extension : fullIsometryEquiv twistCo0 = twistRational :=
  fullIsometryEquiv.apply_symm_apply _

def twistCo1 : LeechCentralQuotient := leechCentralProjection twistCo0

end
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.Outer
