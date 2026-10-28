module

public import Theory.SpecificGroups.PSL3.OuterSolvable.Actions
public import Theory.SpecificGroups.SL3.CenterProjectiveComparison

/-!
# Removing cubic scalars from fourth-power test elements

An equality in PSL₃ between two elements whose fourth powers are one has a
central discrepancy. That discrepancy has cube one by the degree-three center
calculation, and fourth power one by centrality. Hence it is one. In particular,
projective fixation of each order-four test lifts to literal fixation in SL₃.
This does not require the whole projection to be injective.

Source: scalar ambiguity in the GLS3 §2.7 matrix description, used for the
linear alternatives in Aschbacher–Smith F.6.18(10)–(11), pp.309–310, and
15.4.18, pp.1162–1163.
-/

public section
open scoped MatrixGroups
namespace Matrix.PSL3.SylowFixedActions.Standard
open Matrix.PSL3.OuterSolvable
variable (F : Type*) [Field F] [Finite F]

/-- Equality in PSL₃ lifts between elements of exponent dividing four.
The possible cubic scalar discrepancy has both cube and fourth power one. -/
theorem eq_of_projection_eq_of_pow_four {x y : SL(3, F)}
    (hx : x ^ 4 = 1) (hy : y ^ 4 = 1)
    (h : projection F x = projection F y) : x = y := by
  let z := x⁻¹ * y
  have hz : z ∈ Subgroup.center SL(3, F) := QuotientGroup.eq.mp h
  have hcomm : Commute x z := Subgroup.mem_center_iff.mp hz x
  have hyz : y = x * z := by simp [z]
  have hz4 : z ^ 4 = 1 := by
    rw [hyz, hcomm.mul_pow, hx, one_mul] at hy
    exact hy
  have hz3 : z ^ 3 = 1 := by
    let c : Subgroup.center SL(3, F) := ⟨z, hz⟩
    have hc : c ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.mp
      ((orderOf_dvd_natCard c).trans (Matrix.SL3.card_center_dvd_three F))
    exact congrArg Subtype.val hc
  have hz1 : z = 1 := by simpa only [pow_succ, hz3, one_mul] using hz4
  simpa only [hz1, mul_one] using hyz.symm

/-- A projectively fixed element of exponent four is fixed in SL₃ itself. -/
theorem centerAction_fixes_iff_of_pow_four (a : MulAut SL(3, F))
    (x : SL(3, F)) (hx : x ^ 4 = 1) :
    centerAction F a (projection F x) = projection F x ↔ a x = x := by
  constructor
  · intro h
    apply eq_of_projection_eq_of_pow_four F (x := a x) (y := x) _ hx h
    rw [← map_pow, hx, map_one]
  · intro h
    change projection F (a x) = projection F x
    rw [h]

end Matrix.PSL3.SylowFixedActions.Standard
