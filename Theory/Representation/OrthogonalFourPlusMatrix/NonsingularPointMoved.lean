module
public import Theory.Representation.OrthogonalFourPlusMatrix.NonsingularPointOrbit
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.FieldTheory.Finiteness

/-!
# The complete moved hyperplane of a nonsingular point stabilizer

An upper transvection supplies a nonzero singular displacement. The additive
orbit theorem then shows that all displacements generate the perpendicular
hyperplane, without assuming that their additive span is field-linear.
The trace functional after right multiplication by the inverse fixed matrix
is nonzero, so its kernel has dimension three and cardinality q³.

Source: Aschbacher--Smith 9.1.2(4) and 9.4.1, printed pp.729 and 735.
-/

public noncomputable section
open Matrix
namespace ClassicalOrthogonal.FourPlusMatrix.PointOrbit
variable {F : Type*} [Field F] [CharP F 2] [Finite F]

/-- Any additive subgroup containing all stabilizer displacements contains the full hyperplane. -/
theorem pointHyperplane_le_of_displacements (v : Mat (F := F)) (hv : v.det ≠ 0)
    (W : AddSubgroup (Mat (F := F)))
    (hd : ∀ g : pointStabilizer v, ∀ M : Mat (F := F),
      matrixAction g.val M - M ∈ W) : (pointHyperplane v).toAddSubgroup ≤ W := by
  let u : SpecialLinearGroup (Fin 2) F := ⟨!![1,1;0,1],by simp [det_fin_two]⟩
  have hu : u⁻¹ = u := by
    apply inv_eq_of_mul_eq_one_left
    apply Subtype.ext
    change !![1,1;0,1] * !![1,1;0,1] = (1 : Mat (F := F))
    ext i j
    fin_cases i <;> fin_cases j <;> simp [CharTwo.add_self_eq_zero]
  obtain ⟨g,hg⟩ := (pointProjection_bijective v hv).2 u
  change g.val.1 = u at hg
  let M : Mat (F := F) := !![0,0;0,1]
  let z : Mat (F := F) := !![0,1;0,0] * v
  have hmove : matrixAction g.val (M*v) - M*v = z := by
    rw [point_action_mul,hg,←sub_mul]
    change (u.val*M*u⁻¹.val-M)*v = _
    rw [hu]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [u,M]
  have hz : z ∈ W := hmove ▸ hd g (M*v)
  have hz0 : z ≠ 0 := by
    intro he
    have hh := congrArg (fun X : Mat (F := F) => X*v⁻¹) he
    have hi := Matrix.mul_nonsing_inv v (isUnit_iff_ne_zero.mpr hv)
    have he0 : (!![0,1;0,0] : Mat (F := F)) = 0 := by
      simpa only [z,mul_assoc,hi,mul_one,zero_mul] using hh
    have he1 := congrArg (fun X : Mat (F := F) => X 0 1) he0
    exact one_ne_zero he1
  have hzd : z.det = 0 := by
    change Matrix.det ((!![0,1;0,0] : Mat (F := F))*v) = 0
    rw [Matrix.det_mul]
    simp [det_fin_two]
  have hzt : z ∈ pointHyperplane v := hmove ▸ point_displacement_mem v hv g (M*v)
  apply pointHyperplane_le_of_singular v hv W _ z hz hz0 hzd hzt
  intro a x hx
  have hh := W.add_mem (hd a x) hx
  simpa only [sub_add_cancel] using hh

omit [CharP F 2] [Finite F] in
/-- The perpendicular hyperplane of an invertible two-by-two matrix has dimension three. -/
theorem pointHyperplane_finrank (v : Mat (F := F)) (hv : v.det ≠ 0) :
    Module.finrank F (pointHyperplane v) = 3 := by
  let f := (Matrix.traceLinearMap (Fin 2) F F).comp (LinearMap.mulRight F v⁻¹)
  have hf : f ≠ 0 := by
    intro he
    have hh := congrArg (fun a : Mat (F := F) →ₗ[F] F =>
      a ((!![1,0;0,0] : Mat (F := F))*v)) he
    have hi := Matrix.mul_nonsing_inv v (isUnit_iff_ne_zero.mpr hv)
    change ((!![1,0;0,0] : Mat (F := F))*v*v⁻¹).trace = 0 at hh
    rw [mul_assoc,hi,mul_one] at hh
    simp [Matrix.trace,Fin.sum_univ_two] at hh
  have hdim := Module.Dual.finrank_ker_add_one_of_ne_zero hf
  have hmat : Module.finrank F (Mat (F := F)) = 4 := by
    simp [Mat,Module.finrank_matrix]
  change Module.finrank F (pointHyperplane v) + 1 = _ at hdim
  rw [hmat] at hdim
  omega

omit [CharP F 2] [Finite F] in
/-- The moved hyperplane has q³ elements over a field with q elements. -/
theorem pointHyperplane_card (v : Mat (F := F)) (hv : v.det ≠ 0) :
    Nat.card (pointHyperplane v) = Nat.card F ^ 3 := by
  rw [Module.natCard_eq_pow_finrank (K := F),pointHyperplane_finrank v hv]
end ClassicalOrthogonal.FourPlusMatrix.PointOrbit
