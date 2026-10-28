module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.ModelFlag.Quotients
public import Mathlib.Algebra.Algebra.Subalgebra.Tower
public import Mathlib.Data.Matrix.Basis

/-!
# Cubic factor certificates and their literal quotient consumers

A certificate supplies matrices over the four-element coefficient field,
coordinates for the fixed nilpotent image and the literal middle quotient,
and the two generator-action identities. Full matrix-algebra density over
that field survives the constructed evaluation map into every original
characteristic-two field. It therefore proves absolute simplicity, with no
additional field-embedding premise.

The first and last literal quotients both map equivariantly to the same
nilpotent image, so one image certificate proves both cases. The middle
case uses the existing equivariant quotient comparison. No certificate is
constructed here: the finite density calculations and their coordinates
remain explicit inputs, separately from this quotient assembly.

Source motivation: Guralnick–Malle, Proposition 4.3, p.10;
Aschbacher–Smith K.2, printed p.453.
-/

@[expose] public noncomputable section

open G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations
namespace Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.FactorSimplicity
open ModelFlag
universe v
attribute [local irreducible] generatorMatrix nilpotentMatrix

/-- Density of a pair of matrices over its coefficient field. -/
def MatrixDensity {F : Type*} [Field F] {d : ℕ}
    (A : Fin 2 → Matrix (Fin d) (Fin d) F) : Prop :=
  ∀ Q : Subalgebra F (Matrix (Fin d) (Fin d) F), (∀ a, A a ∈ Q) → Q = ⊤

/-- Full matrix-algebra density survives the constructed cubic coefficient map. -/
theorem density_evaluate {K : Type*} [Field K] [CharP K 2]
    (z : K) (hz : z ^ 2 + z + 1 = 0) {d : ℕ}
    (A : Fin 2 → Matrix (Fin d) (Fin d) CoefficientField)
    (hA : MatrixDensity A) : MatrixDensity (fun a => (A a).map (evaluate z hz)) := by
  let : Algebra CoefficientField K := (evaluate z hz).toAlgebra
  let φ : Matrix (Fin d) (Fin d) CoefficientField →ₐ[CoefficientField]
      Matrix (Fin d) (Fin d) K := (Algebra.ofId CoefficientField K).mapMatrix
  intro S hS
  let Q := (S.restrictScalars CoefficientField).comap φ
  have hQ : Q = ⊤ := hA Q hS
  have hunit (i j : Fin d) : Matrix.single i j (1 : K) ∈ S := by
    have hm : Matrix.single i j (1 : CoefficientField) ∈ Q := by rw [hQ]; trivial
    change φ (Matrix.single i j (1 : CoefficientField)) ∈ S at hm
    simpa [φ, Matrix.single_apply] using hm
  apply top_unique
  intro M _
  rw [Matrix.matrix_eq_sum_single M]
  exact S.sum_mem (fun i _ => S.sum_mem (fun j _ => by
    simpa using S.smul_mem (hunit i j) (M i j)))

variable {K : Type v} [Field K] [CharP K 2]

/-- The fixed generator restricted to the image of the fixed nilpotent. -/
def imageActor (z : K) (hz : z ^ 2 + z + 1 = 0)
    (h : MatrixRelations.{v}) (a : Fin 2) :
    Module.End K (LinearMap.range (nilpotentMatrix z hz).toLin') :=
  (generatorMatrix z hz a).toLin'.restrict (by
    rintro x ⟨y, rfl⟩
    refine ⟨(generatorMatrix z hz a).mulVec y, ?_⟩
    change (nilpotentMatrix z hz).mulVec ((generatorMatrix z hz a).mulVec y) =
      (generatorMatrix z hz a).mulVec ((nilpotentMatrix z hz).mulVec y)
    rw [Matrix.mulVec_mulVec, h.commutes K, Matrix.mulVec_mulVec])

theorem imageActor_val (z : K) (hz : z ^ 2 + z + 1 = 0)
    (h : MatrixRelations.{v}) (a : Fin 2)
    (x : LinearMap.range (nilpotentMatrix z hz).toLin') :
    (imageActor z hz h a x).val = (generatorMatrix z hz a).mulVec x.val := by
  exact LinearMap.coe_restrict_apply _ _

/-- Finite matrix data, density, and action comparisons for the two different
factors. The middle space is the actual transported quotient, not a space
chosen only by its dimension. The same image action handles both end factors. -/
structure Certificate {χ : standardBorel modelForm →* Kˣ}
    (c : Coordinates χ) (h : MatrixRelations.{v}) where
  imageMatrices : Fin 2 → Matrix (Fin 21) (Fin 21) CoefficientField
  middleMatrices : Fin 2 → Matrix (Fin 84) (Fin 84) CoefficientField
  imageCoordinates : LinearMap.range (nilpotentMatrix c.z c.quadratic).toLin' ≃ₗ[K]
    (Fin 21 → K)
  middleCoordinates : ((c.matrixStage h 2).toSubmodule ⧸
    (within (c.matrixStage h 1) (c.matrixStage h 2)).toSubmodule) ≃ₗ[K] (Fin 84 → K)
  image_action : ∀ a x, imageCoordinates (imageActor c.z c.quadratic h a x) =
    ((imageMatrices a).map (evaluate c.z c.quadratic)).mulVec (imageCoordinates x)
  middle_action : ∀ a x, middleCoordinates
    ((within (c.matrixStage h 1) (c.matrixStage h 2)).quotientRepresentation (c.actor a) x) =
    ((middleMatrices a).map (evaluate c.z c.quadratic)).mulVec (middleCoordinates x)
  image_density : MatrixDensity imageMatrices
  middle_density : MatrixDensity middleMatrices

variable {χ : standardBorel modelForm →* Kˣ} {c : Coordinates χ} {h : MatrixRelations.{v}}

/-- The first literal quotient is simple by the image certificate. -/
theorem Certificate.first_simple (C : Certificate c h) :
    IsIrreducible (within ((c.flag h).stage 0) ((c.flag h).stage 1)).quotientRepresentation := by
  apply irreducible_of_coordinate_matrices (by decide) c.actor
    (fun a => (C.imageMatrices a).map (evaluate c.z c.quadratic))
    ((c.firstQuotientCoordinates h).trans C.imageCoordinates)
  · intro a x
    have he : c.firstQuotientCoordinates h
        ((within ((c.flag h).stage 0) ((c.flag h).stage 1)).quotientRepresentation (c.actor a) x) =
        imageActor c.z c.quadratic h a (c.firstQuotientCoordinates h x) := by
      apply Subtype.ext
      exact c.firstQuotientCoordinates_action h a x
    exact (congrArg C.imageCoordinates he).trans (C.image_action a _)
  · exact density_evaluate c.z c.quadratic C.imageMatrices C.image_density

/-- The middle literal quotient is simple through its equivariant coordinates. -/
theorem Certificate.middle_simple (C : Certificate c h) :
    IsIrreducible (within ((c.flag h).stage 1) ((c.flag h).stage 2)).quotientRepresentation := by
  apply irreducible_of_coordinate_matrices (by decide) c.actor
    (fun a => (C.middleMatrices a).map (evaluate c.z c.quadratic))
    ((c.quotientEquiv h 1).trans C.middleCoordinates)
  · intro a x
    exact (congrArg C.middleCoordinates
      (c.quotientEquiv_action h 1 (c.actor a) x)).trans (C.middle_action a _)
  · exact density_evaluate c.z c.quadratic C.middleMatrices C.middle_density

/-- The last literal quotient uses the very same image certificate as the first. -/
theorem Certificate.last_simple (C : Certificate c h) :
    IsIrreducible (within ((c.flag h).stage 2) ((c.flag h).stage 3)).quotientRepresentation := by
  apply irreducible_of_coordinate_matrices (by decide) c.actor
    (fun a => (C.imageMatrices a).map (evaluate c.z c.quadratic))
    ((c.lastQuotientCoordinates h).trans C.imageCoordinates)
  · intro a x
    have he : c.lastQuotientCoordinates h
        ((within ((c.flag h).stage 2) ((c.flag h).stage 3)).quotientRepresentation (c.actor a) x) =
        imageActor c.z c.quadratic h a (c.lastQuotientCoordinates h x) := by
      apply Subtype.ext
      exact c.lastQuotientCoordinates_action h a x
    exact (congrArg C.imageCoordinates he).trans (C.image_action a _)
  · exact density_evaluate c.z c.quadratic C.imageMatrices C.image_density

/-- Assemble simplicity of all three literal successive quotient actions. -/
theorem Certificate.simple (C : Certificate c h) : (c.flag h).Simple := by
  intro m hm
  interval_cases m
  · exact C.first_simple
  · exact C.middle_simple
  · exact C.last_simple

end Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.FactorSimplicity

