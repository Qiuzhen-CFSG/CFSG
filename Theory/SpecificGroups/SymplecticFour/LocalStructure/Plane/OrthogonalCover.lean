module
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Plane.CentralModule
public import Theory.Representation.SL2OrthogonalCover.Universal
public import Theory.ElementaryAbelian.VectorSpace

/-!
# The complete orthogonal cover in the symplectic plane radical

Taking square roots of the off-diagonal and the two diagonal entries of a
symmetric matrix identifies the full radical with the three-dimensional
orthogonal cover. Congruence becomes the literal SL₂ action over the same
field; the original natural quotient and alternating central layer are
preserved. The additive equivalence is linear over the binary prime field.

Source: Aschbacher--Smith, 2.4.8(4), F.1.12(I)(2) and I.2.3, together with
the concrete plane radical in `Plane.Extension` and `Plane.CentralModule`.
-/

@[expose] public section
noncomputable section
open Matrix
open scoped IsMulCommutative
namespace Theory.SpecificGroups.SymplecticFour.Plane
namespace OrthogonalCover
open Representation.SL2OrthogonalCover
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Square roots of all three independent symmetric-matrix entries. -/
def coordinates : symmetricMatrices F ≃+ Space F where
  toFun B := ![root (B.val 0 1), root (B.val 0 0), root (B.val 1 1)]
  invFun v := ⟨!![v 1 ^ 2, v 0 ^ 2; v 0 ^ 2, v 2 ^ 2], by
    ext i j; fin_cases i <;> fin_cases j <;> rfl⟩
  left_inv B := by
    apply Subtype.ext
    ext i j
    have hs : B.val 1 0 = B.val 0 1 := congrFun (congrFun B.property 0) 1
    fin_cases i <;> fin_cases j <;> simp [hs]
  right_inv v := by ext i; fin_cases i <;> simp [root_sq]
  map_add' B C := by ext i; fin_cases i <;> simp [map_add]

@[simp] theorem coordinates_apply (B : symmetricMatrices F) :
    coordinates B = ![root (B.val 0 1), root (B.val 0 0), root (B.val 1 1)] := rfl

/-- The full radical has the binary orthogonal-cover coordinates. -/
def radicalCoordinates : radical (F := F) ≃* Multiplicative (Space F) :=
  radicalEquiv.trans coordinates.toMultiplicative

@[simp] theorem radicalCoordinates_apply (q : radical (F := F)) :
    (radicalCoordinates q).toAdd = coordinates (radicalEquiv q).toAdd := rfl

omit [Finite F] in
private theorem congruence_off_diagonal (g : SL F) (B : symmetricMatrices F) :
    (congruence g B).val 0 1 =
      g.val 0 0 * g.val 1 0 * B.val 0 0 + B.val 0 1 +
        g.val 0 1 * g.val 1 1 * B.val 1 1 := by
  have hs : B.val 1 0 = B.val 0 1 := congrFun (congrFun B.property 0) 1
  change (g.val * B.val * g.valᵀ) 0 1 = _
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, hs]
  calc
    _ = g.val 0 0 * g.val 1 0 * B.val 0 0 +
      (g.val 0 0 * g.val 1 1 + g.val 0 1 * g.val 1 0) * B.val 0 1 +
      g.val 0 1 * g.val 1 1 * B.val 1 1 := by ring
    _ = _ := by rw [det_relation, one_mul]

/-- Congruence on the entire radical is the orthogonal-cover action. -/
theorem coordinates_congruence (g : SL F) (B : symmetricMatrices F) :
    coordinates (congruence g B) = action g (coordinates B) := by
  ext i
  fin_cases i
  · change root ((congruence g B).val 0 1) = root (B.val 0 1) +
      root (g.val 0 0 * g.val 1 0) * root (B.val 0 0) +
      root (g.val 0 1 * g.val 1 1) * root (B.val 1 1)
    simp only [congruence_off_diagonal, map_add, map_mul]
    ring
  · change root ((congruence g B).val 0 0) =
      g.val 0 0 * root (B.val 0 0) + g.val 0 1 * root (B.val 1 1)
    rw [congruence_diagonal, map_add, map_mul, map_mul, root_sq, root_sq]
  · change root ((congruence g B).val 1 1) =
      g.val 1 0 * root (B.val 0 0) + g.val 1 1 * root (B.val 1 1)
    rw [congruence_diagonal, map_add, map_mul, map_mul, root_sq, root_sq]

/-- Every actual local element acts through its original SL₂ quotient. -/
theorem radicalCoordinates_conjugate (g : planeLocal (F := F)) (q : radical (F := F)) :
    (radicalCoordinates (conjugate g q)).toAdd =
      action (quotientMap g) (radicalCoordinates q).toAdd := by
  simp only [radicalCoordinates_apply, radicalEquiv_conjugate, coordinates_congruence]

/-- The original natural quotient is the projection of the full-cover coordinates. -/
theorem radicalCoordinates_projection (q : radical (F := F)) :
    projection (radicalCoordinates q).toAdd = (naturalCoordinates q).toAdd := by
  ext i; fin_cases i <;> rfl

/-- The actual central radical is preserved as the orthogonal kernel. -/
theorem radicalCoordinates_central_iff (q : radical (F := F)) :
    q ∈ (Subgroup.center (planeLocal (F := F))).subgroupOf radical ↔
      (radicalCoordinates q).toAdd ∈ (projection (F := F)).toLinearMap.ker := by
  rw [← naturalCoordinates_ker, MonoidHom.mem_ker, LinearMap.mem_ker]
  change naturalCoordinates q = 1 ↔ projection (radicalCoordinates q).toAdd = 0
  rw [radicalCoordinates_projection]
  exact ⟨fun h => congrArg Multiplicative.toAdd h, fun h => Multiplicative.toAdd.injective h⟩

variable [Algebra (ZMod 2) F]

/-- Binary linear coordinates use the canonical additive structure on the radical. -/
def radicalLinearCoordinates : Additive (radical (F := F)) ≃ₗ[ZMod 2] Space F :=
  let e := radicalCoordinates.toAdditive.trans (AddEquiv.additiveMultiplicative (Space F))
  e.toLinearEquiv (fun c x => ZMod.map_smul e.toAddMonoidHom c x)

@[simp] theorem radicalLinearCoordinates_apply (q : Additive (radical (F := F))) :
    radicalLinearCoordinates q = (radicalCoordinates q.toMul).toAdd := rfl

/-- Full-radical SL₂ equivariance over the source binary scalar field. -/
theorem radicalLinearCoordinates_conjugate (g : planeLocal (F := F))
    (q : radical (F := F)) :
    radicalLinearCoordinates (Additive.ofMul (conjugate g q)) =
      binaryAction (quotientMap g) (radicalLinearCoordinates (Additive.ofMul q)) :=
  radicalCoordinates_conjugate g q

end OrthogonalCover
end Theory.SpecificGroups.SymplecticFour.Plane
