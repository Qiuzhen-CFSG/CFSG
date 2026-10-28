module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.ModelFlag.FactorSimplicity.Checks
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.FactorSimplicity.Certificates

/-!
# Explicit coordinates on the literal cubic factors

The image coordinates are Lx, with inverse Uy. The middle coordinates are
[x] ↦ Sx, with inverse y ↦ [Wy], on precisely ker N / range N. Checked
coefficient identities prove the maps and their two generator formulas after
evaluation at the original cubic scalar. There is no additional embedding
hypothesis and no simplicity assertion in this module.

Source motivation: Guralnick–Malle Proposition 4.3, p.10;
Aschbacher–Smith K.2, p.453. Density of the two fixed matrix pairs is the
remaining finite obligation for the existing literal-quotient consumer.
-/

@[expose] public noncomputable section
namespace Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag.FactorCoordinates
open Certificate Certificate.Packed
open G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations
universe v
attribute [local irreducible] generatorMatrix nilpotentMatrix
variable {K : Type v} [Field K] [CharP K 2]

namespace Scalar
variable (z : K) (hz : z ^ 2 + z + 1 = 0)

def u := (matrix 21 U).map (evaluate z hz)
def v := (matrix 126 V).map (evaluate z hz)
def l := (matrix 126 L).map (evaluate z hz)
def r := (matrix 21 R).map (evaluate z hz)
def w := (matrix 84 W).map (evaluate z hz)
def s := (matrix 126 S).map (evaluate z hz)

private theorem map_nilpotent :
    (matrix 126 N).map (evaluate z hz) = nilpotentMatrix z hz := by
  rw [nilpotent_agreement, nilpotentMatrix]
  rfl

private theorem map_generator (a : Fin 2) :
    (matrix 126 (G a)).map (evaluate z hz) = generatorMatrix z hz a := by
  rw [generator_agreement, generatorMatrix]
  rfl

theorem factor : nilpotentMatrix z hz = u z hz * v z hz := by
  simpa only [Matrix.map_mul, map_nilpotent, u, v] using
    congrArg (fun M : Matrix (Fin 126) (Fin 126) CoefficientField =>
      M.map (evaluate z hz)) factorization

theorem lu : l z hz * u z hz = 1 := by
  simpa only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), l, u] using
    congrArg (fun M : Matrix (Fin 21) (Fin 21) CoefficientField =>
      M.map (evaluate z hz)) left_inverse

theorem vr : v z hz * r z hz = 1 := by
  simpa only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), v, r] using
    congrArg (fun M : Matrix (Fin 21) (Fin 21) CoefficientField =>
      M.map (evaluate z hz)) right_inverse

theorem sw : s z hz * w z hz = 1 := by
  simpa only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), s, w] using
    congrArg (fun M : Matrix (Fin 84) (Fin 84) CoefficientField =>
      M.map (evaluate z hz)) middle_left_inverse

theorem su : s z hz * u z hz = 0 := by
  simpa only [Matrix.map_mul, Matrix.map_zero _ (map_zero _), s, u] using
    congrArg (fun M : Matrix (Fin 84) (Fin 21) CoefficientField =>
      M.map (evaluate z hz)) middle_annihilates_image

theorem vw : v z hz * w z hz = 0 := by
  simpa only [Matrix.map_mul, Matrix.map_zero _ (map_zero _), v, w] using
    congrArg (fun M : Matrix (Fin 21) (Fin 84) CoefficientField =>
      M.map (evaluate z hz)) middle_in_kernel

theorem gu (a : Fin 2) :
    generatorMatrix z hz a * u z hz = u z hz * (imageMatrices a).map (evaluate z hz) := by
  simpa only [Matrix.map_mul, map_generator, u] using
    congrArg (fun M : Matrix (Fin 126) (Fin 21) CoefficientField =>
      M.map (evaluate z hz)) (image_intertwining a)

theorem sg (a : Fin 2) :
    s z hz * generatorMatrix z hz a =
      (middleMatrices a).map (evaluate z hz) * s z hz +
        (matrix 21 (H a)).map (evaluate z hz) * v z hz := by
  simpa only [Matrix.map_mul, Matrix.map_add _ (map_add _), map_generator, s, v] using
    congrArg (fun M : Matrix (Fin 84) (Fin 126) CoefficientField =>
      M.map (evaluate z hz)) (middle_intertwining a)

theorem image_recover (x : LinearMap.range (nilpotentMatrix z hz).toLin') :
    (u z hz).mulVec ((l z hz).mulVec x.val) = x.val := by
  obtain ⟨y, hy⟩ := x.property
  change (nilpotentMatrix z hz).mulVec y = x.val at hy
  rw [← hy, factor, ← Matrix.mulVec_mulVec]
  rw [Matrix.mulVec_mulVec _ (l z hz) (u z hz), lu, Matrix.one_mulVec]

theorem v_eq_zero_of_nilpotent (x : Fin 126 → K)
    (hx : (nilpotentMatrix z hz).mulVec x = 0) : (v z hz).mulVec x = 0 := by
  have he := congrArg (Matrix.mulVec (l z hz)) hx
  rw [factor, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec _ (l z hz) (u z hz),
    lu, Matrix.one_mulVec, Matrix.mulVec_zero] at he
  exact he

theorem w_mem_kernel (x : Fin 84 → K) :
    (w z hz).mulVec x ∈ LinearMap.ker (nilpotentMatrix z hz).toLin' := by
  change (nilpotentMatrix z hz).mulVec ((w z hz).mulVec x) = 0
  rw [factor, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec _ (v z hz) (w z hz),
    vw, Matrix.zero_mulVec, Matrix.mulVec_zero]

theorem s_image_zero (x : LinearMap.range (nilpotentMatrix z hz).toLin') :
    (s z hz).mulVec x.val = 0 := by
  rw [← image_recover z hz x, Matrix.mulVec_mulVec, su, Matrix.zero_mulVec]

end Scalar

attribute [local irreducible] Scalar.u Scalar.v Scalar.l Scalar.r Scalar.w Scalar.s

open Scalar
variable (z : K) (hz : z ^ 2 + z + 1 = 0)

/-- Image coordinates x ↦ Lx, with the explicitly specified inverse y ↦ Uy. -/
def imageCoordinates : LinearMap.range (nilpotentMatrix z hz).toLin' ≃ₗ[K] (Fin 21 → K) where
  toFun x := (l z hz).mulVec x.val
  invFun x := ⟨(u z hz).mulVec x, (r z hz).mulVec x, by
    change (nilpotentMatrix z hz).mulVec ((r z hz).mulVec x) = (u z hz).mulVec x
    rw [factor, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec _ (v z hz) (r z hz),
      vr, Matrix.one_mulVec]⟩
  left_inv x := Subtype.ext (image_recover z hz x)
  right_inv x := by
    change (l z hz).mulVec ((u z hz).mulVec x) = x
    rw [Matrix.mulVec_mulVec, lu, Matrix.one_mulVec]
  map_add' x y := (l z hz).mulVec_add x.val y.val
  map_smul' a x := (l z hz).mulVec_smul a x.val

theorem imageCoordinates_apply
    (x : LinearMap.range (nilpotentMatrix z hz).toLin') :
    imageCoordinates z hz x = (l z hz).mulVec x.val := by
  funext i
  rfl

@[simp] theorem imageCoordinates_symm_apply (x : Fin 21 → K) :
    ((imageCoordinates z hz).symm x).val = (u z hz).mulVec x := rfl

/-- The image coordinate formula for the exact restricted generator. -/
theorem image_action (h : MatrixRelations.{v}) (a : Fin 2)
    (x : LinearMap.range (nilpotentMatrix z hz).toLin') :
    imageCoordinates z hz
      (CubicCalculation.FactorSimplicity.imageActor z hz h a x) =
        ((imageMatrices a).map (evaluate z hz)).mulVec (imageCoordinates z hz x) := by
  rw [imageCoordinates_apply, CubicCalculation.FactorSimplicity.imageActor_val]
  conv_lhs => rw [← image_recover z hz x]
  rw [Matrix.mulVec_mulVec _ (generatorMatrix z hz a) (u z hz), gu,
    ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec _ (l z hz) (u z hz), lu, Matrix.one_mulVec]
  rfl

variable {z hz} {χ : standardBorel modelForm →* Kˣ}
  (c : Coordinates χ) (h : MatrixRelations.{v})

/-- S on representatives in the actual kernel stage. -/
def middleMap : (c.matrixStage h 2).toSubmodule →ₗ[K] (Fin 84 → K) :=
  (s c.z c.quadratic).toLin'.comp (c.matrixStage h 2).toSubmodule.subtype

private theorem middleMap_zero :
    (within (c.matrixStage h 1) (c.matrixStage h 2)).toSubmodule ≤
      LinearMap.ker (middleMap c h) := by
  intro x hx
  change x.val ∈ (c.matrixStage h 1).toSubmodule at hx
  rw [c.matrixStage_one h] at hx
  exact s_image_zero c.z c.quadratic ⟨x.val, hx⟩

/-- The literal quotient map [x] ↦ Sx. -/
def middleLift : ((c.matrixStage h 2).toSubmodule ⧸
    (within (c.matrixStage h 1) (c.matrixStage h 2)).toSubmodule) →ₗ[K] (Fin 84 → K) :=
  Submodule.liftQ _ (middleMap c h) (by exact middleMap_zero c h)

/-- The specified inverse representatives lie in the literal kernel stage. -/
def middleRepresentative (x : Fin 84 → K) : (c.matrixStage h 2).toSubmodule :=
  ⟨(w c.z c.quadratic).mulVec x, by
    rw [c.matrixStage_two h]
    exact w_mem_kernel c.z c.quadratic x⟩

theorem middleLift_surjective : Function.Surjective (middleLift c h) := by
  intro x
  refine ⟨Submodule.Quotient.mk (middleRepresentative c h x), ?_⟩
  change (s c.z c.quadratic).mulVec ((w c.z c.quadratic).mulVec x) = x
  rw [Matrix.mulVec_mulVec, sw, Matrix.one_mulVec]

/-- Explicit coordinates on precisely the transported quotient ker N / range N. -/
def middleCoordinates : ((c.matrixStage h 2).toSubmodule ⧸
    (within (c.matrixStage h 1) (c.matrixStage h 2)).toSubmodule) ≃ₗ[K] (Fin 84 → K) :=
  LinearEquiv.ofBijective (middleLift c h) ⟨
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
      simpa using c.matrixQuotient_degree h 1 (by decide))).mpr (middleLift_surjective c h),
    middleLift_surjective c h⟩

theorem middleCoordinates_mk (x : (c.matrixStage h 2).toSubmodule) :
    middleCoordinates c h (Submodule.Quotient.mk x) = (s c.z c.quadratic).mulVec x.val := by
  funext i
  rfl

@[simp] theorem middleCoordinates_symm_apply (x : Fin 84 → K) :
    (middleCoordinates c h).symm x = Submodule.Quotient.mk (middleRepresentative c h x) := by
  apply (middleCoordinates c h).injective
  rw [LinearEquiv.apply_symm_apply, middleCoordinates_mk]
  change x = (s c.z c.quadratic).mulVec ((w c.z c.quadratic).mulVec x)
  rw [Matrix.mulVec_mulVec, sw, Matrix.one_mulVec]

/-- The generator action on the literal middle quotient in these coordinates. -/
theorem middle_action (a : Fin 2)
    (x : (c.matrixStage h 2).toSubmodule ⧸
      (within (c.matrixStage h 1) (c.matrixStage h 2)).toSubmodule) :
    middleCoordinates c h
      ((within (c.matrixStage h 1) (c.matrixStage h 2)).quotientRepresentation (c.actor a) x) =
      ((middleMatrices a).map (evaluate c.z c.quadratic)).mulVec (middleCoordinates c h x) := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    change (s c.z c.quadratic).mulVec
      (((c.matrixStage h 2).toRepresentation (c.actor a) x).val) =
      ((middleMatrices a).map (evaluate c.z c.quadratic)).mulVec
        ((s c.z c.quadratic).mulVec x.val)
    rw [c.matrixStage_actor, Matrix.mulVec_mulVec, sg, Matrix.add_mulVec,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have hx := x.property
    simp only [c.matrixStage_two h] at hx
    rw [v_eq_zero_of_nilpotent c.z c.quadratic x.val hx, Matrix.mulVec_zero, add_zero]

end Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag.FactorCoordinates
