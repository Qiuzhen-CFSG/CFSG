module

public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddSixComparison.Image.Root
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddSixComparison.Image.SingularLines.Monomial

/-!
# Singular-line transport and all Siegel lifts for the signed exterior action

Anisotropy gives a nonzero hyperbolic coordinate in every nonzero singular
vector. The special unitary monomial matrices move it to the first opposite
coordinate. The signed root lift clears the second hyperbolic plane and the
anisotropic coordinates; preservation of the quadratic form clears the last
coordinate. Reversal then sends the remaining vector to the first line.

Combining this explicit transport with the proved first-direction root lifts
and Siegel covariance gives an exterior lift of every Siegel transformation
on the original minus-six space. No simplicity, generation or image premise
is needed. The signed chart already supplies the scalar identities used here,
so the transport does not require additional characteristic or cardinality
hypotheses on its given realization.

Source: GLS3 §2.7 and the small orthogonal reduction in Aschbacher–Smith
A.2.17, printed pp.38–39. The elimination strategy parallels the existing
characteristic-two comparison, with the monomial matrices and signs verified
here for the actual signed action.
-/

@[expose] public noncomputable section
namespace ClassicalOrthogonal.Minus.OddSixComparison
open Matrix BenderSuzuki.MatrixGroups Atlas.Order20160A8.Bivectors
open Theory.SpecificGroups.ClassicalUnitary


namespace Image.SingularLines
variable {p n : ℕ} [Fact p.Prime] [NeZero n]
variable {F : Type} [Field F] [Finite F]
variable (R : ExteriorRealization F (Extension p n) (unitaryForm p n))
variable (C : SignedCoordinates R)

private theorem siegel_direction_coordinates (v x : Space F 2) :
    let y := Quadratic.siegel (quadraticForm F 3) (direction F) v x
    (y.1 0).2 = (x.1 0).2 - (x.1 0).2 * (v.1 0).2 ∧
    (y.1 1).1 = (x.1 1).1 - (x.1 0).2 * (v.1 1).1 ∧
    (y.1 1).2 = (x.1 1).2 - (x.1 0).2 * (v.1 1).2 ∧
    y.2.1 = x.2.1 - (x.1 0).2 * v.2.1 ∧
    y.2.2 = x.2.2 - (x.1 0).2 * v.2.2 := by
  have hp : (quadraticForm F 3).polarBilin x (direction F) = (x.1 0).2 :=
    (Quadratic.polar_swap _ _ _).trans (polar_direction F x)
  simp only [Quadratic.siegel, hp]
  simp [direction, Matrix.vecHead, Matrix.vecTail]

include C in
/-- The explicit signed root clears all nonpivot coordinates. -/
theorem root_clears (x : Space F 2)
    (hx : quadraticForm F 3 x = 0) (hb : (x.1 0).2 ≠ 0) :
    ∃ g : (unitaryForm p n).specialSubgroup,
      (R.action g).val x = (x.1 0).2 • opposite F := by
  let b := (x.1 0).2
  let v : Space F 2 :=
    (![(0, 0), ((x.1 1).1 / b, (x.1 1).2 / b)], (x.2.1 / b, x.2.2 / b))
  have hv : (quadraticForm F 3).polarBilin (direction F) v = 0 := by
    rw [polar_direction]; rfl
  refine ⟨rootLift R C v, ?_⟩
  rw [rootLift_action R C v hv]
  change Quadratic.siegel (quadraticForm F 3) (direction F) v x = _
  let y := Quadratic.siegel (quadraticForm F 3) (direction F) v x
  have hcoords := siegel_direction_coordinates v x
  have hb' : (y.1 0).2 = b := by simpa [v, b] using hcoords.1
  have hc : (y.1 1).1 = 0 := by
    simpa [v, b, mul_div_cancel₀ _ hb] using hcoords.2.1
  have hd : (y.1 1).2 = 0 := by
    simpa [v, b, mul_div_cancel₀ _ hb] using hcoords.2.2.1
  have hz : y.2 = 0 := by
    apply Prod.ext
    · simpa [v, b, mul_div_cancel₀ _ hb] using hcoords.2.2.2.1
    · simpa [v, b, mul_div_cancel₀ _ hb] using hcoords.2.2.2.2
  have hy : quadraticForm F 3 y = 0 :=
    (Quadratic.siegel_preserves _ _ _ _ (direction_singular F) hv).trans hx
  have ha : (y.1 0).1 = 0 := by
    have hm : (y.1 0).1 * b = 0 := by
      simpa [quadraticForm, form_apply, Fin.sum_univ_succ, hb', hc, hz] using hy
    exact (mul_eq_zero.mp hm).resolve_right hb
  change y = _
  apply Prod.ext
  · funext i
    fin_cases i <;> apply Prod.ext
    · simpa [opposite] using ha
    · simpa [opposite] using hb'
    · simpa [opposite] using hc
    · simpa [opposite] using hd
  · change y.2 = b • (0 : F × F)
    simpa only [smul_zero] using hz

include C in
/-- A nonzero singular vector has a hyperbolic coordinate, which one of four
special unitary monomial elements moves to the pivot. -/
theorem exists_pivot (x : Space F 2)
    (hx : quadraticForm F 3 x = 0) (hxn : x ≠ 0) :
    ∃ g : (unitaryForm p n).specialSubgroup,
      (((R.action g).val x).1 0).2 ≠ 0 := by
  by_cases hb : (x.1 0).2 ≠ 0
  · exact ⟨1, by simpa using hb⟩
  by_cases ha : (x.1 0).1 ≠ 0
  · exact ⟨reversal, by simpa [reversal_pivot R C] using ha⟩
  by_cases hd : (x.1 1).2 ≠ 0
  · exact ⟨interchange R C, interchange_pivot_ne_zero R C x hd⟩
  by_cases hc : (x.1 1).1 ≠ 0
  · refine ⟨interchange R C * reversal, ?_⟩
    simp only [map_mul, Subgroup.coe_mul, LinearEquiv.mul_apply]
    exact interchange_pivot_ne_zero R C _ (reversal_second_ne_zero R C x hc)
  have ha0 := not_ne_iff.mp ha
  have hb0 := not_ne_iff.mp hb
  have hc0 := not_ne_iff.mp hc
  have hd0 := not_ne_iff.mp hd
  have hz : x.2 = 0 := by
    apply quadraticForm_anisotropic_plane F
    simpa [quadraticForm, form_apply, Fin.sum_univ_succ, ha0, hc0] using hx
  exfalso
  apply hxn
  apply Prod.ext
  · funext i
    fin_cases i <;> apply Prod.ext <;> assumption
  · exact hz

end Image.SingularLines

namespace Image
variable {p n : ℕ} [Fact p.Prime] [NeZero n]
variable {F : Type} [Field F] [Finite F]
variable (R : ExteriorRealization F (Extension p n) (unitaryForm p n))
variable (C : SignedCoordinates R)
include C

/-- The actual signed exterior action transports every nonzero singular line
to the first coordinate line. No simplicity or image hypothesis is required. -/
theorem singular_line_transport (x : Space F 2)
    (hx : quadraticForm F 3 x = 0) (hxn : x ≠ 0) :
    ∃ (g : (unitaryForm p n).specialSubgroup) (b : F), b ≠ 0 ∧
      (R.action g).val x = b • direction F := by
  obtain ⟨g, hg⟩ := SingularLines.exists_pivot R C x hx hxn
  let y := (R.action g).val x
  have hy : quadraticForm F 3 y = 0 := (form_preserved F (R.action g) x).trans hx
  obtain ⟨h, hh⟩ := SingularLines.root_clears R C y hy hg
  refine ⟨SingularLines.reversal * h * g, -(y.1 0).2, neg_ne_zero.mpr hg, ?_⟩
  simp only [map_mul, Subgroup.coe_mul, LinearEquiv.mul_apply]
  change (R.action SingularLines.reversal).val ((R.action h).val y) = _
  rw [hh, map_smul, SingularLines.reversal_opposite R C]
  simp only [smul_neg, neg_smul]

/-- Every Siegel transformation of the original minus-six form has an actual
special unitary exterior lift, with precisely the displayed parameters. -/
theorem siegel_mem_range (u v : Space F 2) (hu : quadraticForm F 3 u = 0)
    (huv : (quadraticForm F 3).polarBilin u v = 0) :
    siegelElement (quadraticForm F 3) u v hu huv ∈ R.action.range :=
  R.siegel_mem_range_of_direction_and_transport
    (direction_siegel_mem_range R C) (singular_line_transport R C) u v hu huv

end Image

end ClassicalOrthogonal.Minus.OddSixComparison
