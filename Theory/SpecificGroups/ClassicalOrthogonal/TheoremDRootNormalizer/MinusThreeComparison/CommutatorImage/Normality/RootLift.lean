module

public import Theory.SpecificGroups.ClassicalOrthogonal.TheoremDRootNormalizer.MinusThreeComparison.Descent
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPlaneRadical
public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.Elementary

/-!
# A unitary lift of a minus-six Siegel root group

The Hermitian upper unipotent with block parameters c, d, z has exterior
square equal to the Siegel transformation along the first coordinate line
of k⁴ ⊕ E. The proof calculates the six actual minors and uses the public
descent intertwining equation. In particular it identifies the whole root
group with concrete matrices in SU₄, rather than an abstract group label.

This is the local calculation for the twisted A₃/D₃ comparison in GLS3
§2.7, printed pp.85–89. The orthogonal commutator and image normality are
handled separately; no split-form image theorem is used.
-/

@[expose] public noncomputable section
namespace ClassicalOrthogonal.TheoremDRootNormalizer.MinusThreeComparison
open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary
open Atlas.Order20160A8.Bivectors
open Representation.OrthogonalFourMinus
namespace Normality
variable (n : ℕ) [NeZero n]

/-- The first singular coordinate vector. -/
def direction : Space n := (![(1,0),(0,0)],0)
/-- Its hyperbolic partner. -/
def opposite : Space n := (![(0,1),(0,0)],0)

theorem direction_singular : form n (direction n) = 0 := by
  apply Subtype.ext
  simp [direction, form_apply, FiniteModel.norm]

theorem polar_direction (v : Space n) :
    (form n).polarBilin (direction n) v = (v.1 0).2 := by
  apply Subtype.ext
  simp [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, form_apply,
    direction, FiniteModel.norm]
  ring

theorem polar_coe (v w : Space n) :
    ((form n).polarBilin v w : Field n) =
      (v.1 0).1 * (w.1 0).2 + (w.1 0).1 * (v.1 0).2 +
      (v.1 1).1 * (w.1 1).2 + (w.1 1).1 * (v.1 1).2 +
      v.2 * conjugation n w.2 + w.2 * conjugation n v.2 := by
  simp [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, form_apply,
    FiniteModel.norm, map_add]
  ring

/-- The Hermitian parameter of the plane radical. -/
def parameterMatrix (v : Space n) : UnitaryFourPlaneRadical.hermitianMatrices
    (Field n) (conjugation n) :=
  ⟨!![(v.1 1).1,v.2;conjugation n v.2,(v.1 1).2], by
    ext i j
    fin_cases i <;> fin_cases j
    · exact (v.1 1).1.property
    · exact FiniteModel.conjugation_involutive n v.2
    · rfl
    · exact (v.1 1).2.property⟩

/-- The actual determinant-one unitary upper unipotent. -/
def rootLift (v : Space n) : SU n :=
  UnitaryFourPlaneRadical.unipotentSU (Field n) (conjugation n)
    (FiniteModel.conjugation_involutive n) (parameterMatrix n v)

/-- The six-minor formula is precisely the Siegel action. -/
theorem rootLift_exterior (v x : Space n)
    (hv : (form n).polarBilin (direction n) v = 0) :
    exterior n (rootLift n v) (toBivector n x) =
      toBivector n (Quadratic.siegel (form n) (direction n) v x) := by
  have hb : (v.1 0).2 = 0 := (polar_direction n v).symm.trans hv
  have hp : (form n).polarBilin x (direction n) = (x.1 0).2 :=
    (Quadratic.polar_swap _ _ _).trans (polar_direction n x)
  rw [MinusThreeComparison.exterior_apply]
  simp only [Quadratic.siegel, hp]
  ext i
  fin_cases i <;>
    simp [-QuadraticMap.polarBilin_apply_apply, rootLift, UnitaryFourPlaneRadical.unipotentSU,
      UnitaryFourPlaneRadical.unipotentMatrix, parameterMatrix, exteriorMap,
      compound, first, second, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, toBivector, direction,
      Subfield.smul_def, polar_coe, form_apply, hb, FiniteModel.norm,
      map_add, map_sub, CharTwo.sub_eq_add] <;> ring_nf
  simp [CharTwo.two_eq_zero]

/-- The entire coordinate Siegel root group lies in the descended image. -/
theorem rootLift_action (hD : Descends n) (v : Space n)
    (hv : (form n).polarBilin (direction n) v = 0) :
    orthogonalAction n hD (rootLift n v) =
      siegelElement (form n) (direction n) v (direction_singular n) hv := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  apply toBivector_injective n
  rw [orthogonalAction_intertwines, rootLift_exterior n v x hv]
  rfl

end Normality
end ClassicalOrthogonal.TheoremDRootNormalizer.MinusThreeComparison
