module

public import Theory.SpecificGroups.ClassicalOrthogonal.TheoremDRootNormalizer.MinusThreeComparison.CommutatorImage.Normality.RootLift
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourGeneration
/-!
# Singular-line transitivity of the genuine descended exterior action

A nonzero singular vector has a nonzero hyperbolic coordinate, since the
extension norm is anisotropic. Two existing special unitary coordinate
permutations bring that coordinate to the pivot. The explicit Siegel lift
then clears the other hyperbolic plane and the extension coordinate;
quadratic preservation clears the last coordinate. This sends the vector
to a nonzero multiple of the first singular coordinate vector.

Thus the concrete exterior image is transitive on singular lines, without
an orthogonal generation, order, recognition, or Witt-extension premise.
This is the coordinate argument needed for the minus-six comparison in
GLS3 §2.7, printed pp.85–89.
-/

@[expose] public noncomputable section
namespace ClassicalOrthogonal.TheoremDRootNormalizer.MinusThreeComparison
open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary
open Atlas.Order20160A8.Bivectors
open Representation.OrthogonalFourMinus
namespace Normality
variable (n : ℕ) [NeZero n]

/-- Quadratic preservation through the full group's public membership criterion. -/
theorem form_preserved (g : FullOrthogonal n) (x : Space n) :
    form n (g.val x) = form n x :=
  (Theory.AlgebraicGroup.mem_quadraticIsometrySubgroup _ _).mp g.property x

/-- The four coordinates needed by singular-vector elimination. -/
theorem siegel_direction_coordinates (v x : Space n) :
    let y := Quadratic.siegel (form n) (direction n) v x
    (y.1 0).2 = (x.1 0).2 - (x.1 0).2 * (v.1 0).2 ∧
    (y.1 1).1 = (x.1 1).1 - (x.1 0).2 * (v.1 1).1 ∧
    (y.1 1).2 = (x.1 1).2 - (x.1 0).2 * (v.1 1).2 ∧
    y.2 = x.2 - ((x.1 0).2 : Field n) * v.2 := by
  have hp : (form n).polarBilin x (direction n) = (x.1 0).2 :=
    (Quadratic.polar_swap _ _ _).trans (polar_direction n x)
  simp only [Quadratic.siegel, hp]
  simp [direction, Subfield.smul_def, Matrix.vecHead, Matrix.vecTail]

/-- A unitary plane-radical element clears every nonpivot coordinate. -/
theorem root_clears (hD : Descends n) (x : Space n)
    (hx : form n x = 0) (hb : (x.1 0).2 ≠ 0) :
    ∃ g : SU n, (orthogonalAction n hD g).val x = (x.1 0).2 • opposite n := by
  let b := (x.1 0).2
  let v : Space n := (![(0,0),((x.1 1).1 / b, (x.1 1).2 / b)], b⁻¹ • x.2)
  have hv : (form n).polarBilin (direction n) v = 0 := by
    rw [polar_direction]; rfl
  refine ⟨rootLift n v, ?_⟩
  rw [rootLift_action n hD v hv]
  change Quadratic.siegel (form n) (direction n) v x = _
  let y := Quadratic.siegel (form n) (direction n) v x
  have hcoords := siegel_direction_coordinates n v x
  have hbE : (b : Field n) ≠ 0 := fun h => hb (Subtype.ext h)
  have hb' : (y.1 0).2 = b := by simpa [v, b] using hcoords.1
  have hc : (y.1 1).1 = 0 := by
    simpa [v, b, mul_div_cancel₀ _ hb] using hcoords.2.1
  have hd : (y.1 1).2 = 0 := by
    simpa [v, b, mul_div_cancel₀ _ hb] using hcoords.2.2.1
  have hz : y.2 = 0 := by
    simpa [y, v, Subfield.smul_def, ← mul_assoc, show (x.1 0).2 = b from rfl, hbE] using hcoords.2.2.2
  have hy : form n y = 0 := (Quadratic.siegel_preserves _ _ _ _
    (direction_singular n) hv).trans hx
  have ha : (y.1 0).1 = 0 := by
    rw [form_apply, hb', hc, hz] at hy
    have hm : (y.1 0).1 * b = 0 := by
      simpa only [zero_mul, add_zero, (FiniteModel.norm_eq_zero_iff n 0).mpr rfl] using hy
    exact (mul_eq_zero.mp hm).resolve_right hb
  change y = _
  apply Prod.ext
  · funext i
    fin_cases i <;> apply Prod.ext
    · simpa [opposite] using ha
    · simpa [opposite] using hb'
    · simpa [opposite] using hc
    · simpa [opposite] using hd
  · simpa [opposite] using hz

/-- The existing antidiagonal unitary permutation. -/
def reversal : SU n := UnitaryFourGeneration.reverse (Field n) (conjugation n)
  (FiniteModel.conjugation_involutive n)
/-- The existing unitary permutation interchanging the hyperbolic planes. -/
def interchange : SU n := UnitaryFourGeneration.middleSwap (Field n) (conjugation n)
  (FiniteModel.conjugation_involutive n)

theorem reversal_action (hD : Descends n) (x : Space n) :
    (orthogonalAction n hD (reversal n)).val x =
      (![((x.1 0).2,(x.1 0).1),((x.1 1).2,(x.1 1).1)], x.2) := by
  apply toBivector_injective n
  rw [orthogonalAction_intertwines, MinusThreeComparison.exterior_apply]
  change exteriorMap (UnitaryFourGeneration.reverse (Field n) (conjugation n)
    (FiniteModel.conjugation_involutive n)).val.val (toBivector n x) = _
  rw [UnitaryFourGeneration.reverse_val]
  ext i
  fin_cases i <;>
    simp [exteriorMap, compound, first, second, Matrix.toLin'_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, UnitaryFourFlag.gram,
      toBivector, CharTwo.neg_eq]

theorem interchange_action (hD : Descends n) (x : Space n) :
    (orthogonalAction n hD (interchange n)).val x =
      (![(x.1 1),(x.1 0)], x.2) := by
  apply toBivector_injective n
  rw [orthogonalAction_intertwines, MinusThreeComparison.exterior_apply]
  ext i
  fin_cases i <;>
    simp [interchange, UnitaryFourGeneration.middleSwap,
      UnitaryFourGeneration.involutionElement, UnitaryFourGeneration.middleSwapMatrix,
      exteriorMap, compound, first, second, Matrix.toLin'_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, toBivector, CharTwo.neg_eq]

/-- One of four unitary permutations gives a nonzero pivot. -/
theorem exists_pivot (hD : Descends n) (x : Space n)
    (hx : form n x = 0) (hxn : x ≠ 0) :
    ∃ g : SU n, (((orthogonalAction n hD g).val x).1 0).2 ≠ 0 := by
  by_cases hb : (x.1 0).2 ≠ 0
  · exact ⟨1, by simpa using hb⟩
  by_cases ha : (x.1 0).1 ≠ 0
  · exact ⟨reversal n, by simpa [reversal_action] using ha⟩
  by_cases hd : (x.1 1).2 ≠ 0
  · exact ⟨interchange n, by simpa [interchange_action] using hd⟩
  by_cases hc : (x.1 1).1 ≠ 0
  · refine ⟨interchange n * reversal n, ?_⟩
    simpa [map_mul, LinearEquiv.mul_apply, interchange_action, reversal_action] using hc
  have ha0 := not_ne_iff.mp ha
  have hb0 := not_ne_iff.mp hb
  have hc0 := not_ne_iff.mp hc
  have hd0 := not_ne_iff.mp hd
  have hz : x.2 = 0 := by
    rw [form_apply, ha0, hc0, zero_mul, zero_mul, zero_add, zero_add] at hx
    exact (FiniteModel.norm_eq_zero_iff n _).mp hx
  exfalso
  apply hxn
  apply Prod.ext
  · funext i
    fin_cases i <;> apply Prod.ext <;> assumption
  · exact hz

/-- Every nonzero singular vector is carried to the coordinate singular line. -/
theorem singular_line_transport (hD : Descends n) (x : Space n)
    (hx : form n x = 0) (hxn : x ≠ 0) :
    ∃ (g : SU n) (b : FixedField n), b ≠ 0 ∧
      (orthogonalAction n hD g).val x = b • direction n := by
  obtain ⟨g, hg⟩ := exists_pivot n hD x hx hxn
  let y := (orthogonalAction n hD g).val x
  have hy : form n y = 0 := (form_preserved n (orthogonalAction n hD g) x).trans hx
  obtain ⟨h, hh⟩ := root_clears n hD y hy hg
  refine ⟨reversal n * h * g, (y.1 0).2, hg, ?_⟩
  simp only [map_mul, Subgroup.coe_mul, LinearEquiv.mul_apply]
  change (orthogonalAction n hD (reversal n)).val
    ((orthogonalAction n hD h).val y) = _
  rw [hh, map_smul, reversal_action]
  rfl

end Normality
end ClassicalOrthogonal.TheoremDRootNormalizer.MinusThreeComparison
