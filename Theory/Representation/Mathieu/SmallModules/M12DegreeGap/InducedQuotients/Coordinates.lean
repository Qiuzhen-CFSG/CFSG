module

public import Theory.Representation.Mathieu.SmallModules.M12DegreeGap.InducedQuotients.TensorModel
public import Theory.Representation.Mathieu.SmallModules.M12DegreeGap.InducedQuotients.Data
public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointExtension.Coordinates

/-!
# Native coordinates for the 120-dimensional M₁₂ tensor model

Apply the existing ten heart coordinates to each of the twelve native
points. The two action matrices are computed in this fixed basis; no
abstract group isomorphism or field extension is involved.
Source context: James, J. Algebra 27 (1973), 57–111.
-/

@[expose] public noncomputable section
namespace Representation.MathieuSmall.M12DegreeGap.InducedQuotients
open Sporadic.Mathieu M12Recognition.PointExtension

abbrev CoordinateSpace := Fin 120 → ZMod 2

def flatIndex : Fin 12 × Fin 10 ≃ Fin 120 := finProdFinEquiv

/-- Point-major ordering of the actual heart coordinates. -/
def tensorCoordinates : TensorSpace ≃ₗ[ZMod 2] CoordinateSpace where
  toFun v y := coordinateEquivalence (v (flatIndex.symm y).1) (flatIndex.symm y).2
  invFun w x := coordinateEquivalence.symm (fun i => w (flatIndex (x, i)))
  left_inv v := by
    funext x
    apply coordinateEquivalence.injective
    ext i
    simp
  right_inv w := by
    funext y
    simp
  map_add' := by intros; ext y; simp
  map_smul' := by intros; ext y; simp

/-- The column matrix of the diagonal permutation/heart action. -/
def tensorMatrix (g : Equiv.Perm (Fin 12)) : Matrix (Fin 120) (Fin 120) (ZMod 2) :=
  fun r c => if (flatIndex.symm c).1 = g.symm (flatIndex.symm r).1 then
    permutationMatrix g (flatIndex.symm r).2 (flatIndex.symm c).2 else 0

private theorem heart_coordinates (g : M12) (v : M12Heart) :
    coordinateEquivalence (m12HeartRepresentation g v) =
      (permutationMatrix g.val).mulVec (coordinateEquivalence v) := by
  have h := LinearMap.toMatrix'_mulVec
    (coordinateEquivalence.conj (m12HeartRepresentation g)) (coordinateEquivalence v)
  change (matrixEquivalence (m12HeartRepresentation g)).mulVec (coordinateEquivalence v) = _ at h
  rw [show matrixEquivalence (m12HeartRepresentation g) = permutationMatrix g.val from
    matrix_natural_eq g.val] at h
  simpa only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using h.symm

/-- Coordinates intertwine every native group element with the explicit matrix. -/
theorem tensorCoordinates_action (g : M12) (v : TensorSpace) :
    tensorCoordinates (tensorAction g v) = (tensorMatrix g.val).mulVec (tensorCoordinates v) := by
  funext r
  change coordinateEquivalence (m12HeartRepresentation g (v (g⁻¹ • (flatIndex.symm r).1)))
      (flatIndex.symm r).2 = _
  rw [heart_coordinates]
  change (∑ i : Fin 10, permutationMatrix g.val (flatIndex.symm r).2 i *
      coordinateEquivalence (v (g⁻¹ • (flatIndex.symm r).1)) i) =
    ∑ c : Fin 120, tensorMatrix g.val r c * tensorCoordinates v c
  rw [← flatIndex.sum_comp]
  simp only [tensorMatrix, tensorCoordinates, LinearEquiv.coe_mk,
    Fintype.sum_prod_type, ite_mul, zero_mul]
  simp
  rfl

/-- The two literal native standard generators in the certificate order. -/
def actor (j : Fin 2) : M12 :=
  ![⟨m12GeneratorA, m12GeneratorA_mem⟩, ⟨m12GeneratorB, m12GeneratorB_mem⟩] j

def actorPerm (j : Fin 2) : _root_.Equiv.Perm (Fin 12) := ![m12GeneratorA, m12GeneratorB] j

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 8192 in
/-- The finite raw matrices agree with the literal permutation formulas. -/
theorem generatorMatrix_eq : ∀ j : Fin 2,
    CertificateData.generatorMatrix j = tensorMatrix (actor j).val := by
  have ha (j : Fin 2) : (actor j).val = actorPerm j := by fin_cases j <;> rfl
  simp only [ha]
  intro j
  ext r c
  simp only [tensorMatrix, permutationMatrix_formula]
  revert j r c
  decide +kernel

/-- Concrete action equation used by the invariant-flag calculation. -/
theorem tensorCoordinates_generator (j : Fin 2) (v : TensorSpace) :
    tensorCoordinates (tensorAction (actor j) v) =
      (CertificateData.generatorMatrix j).mulVec (tensorCoordinates v) := by
  rw [generatorMatrix_eq]
  exact tensorCoordinates_action _ _

end Representation.MathieuSmall.M12DegreeGap.InducedQuotients
