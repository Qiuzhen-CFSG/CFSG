module

public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.LinearExtension.OuterData
public import Theory.SpecificGroups.PSL3.StandardCubicFixedNine.Descent

/-!
# Cube-one containment in the linear circle extension

Projective cubic descent computes the scalar twisted matrix norm, lifts that
scalar through the finite-field norm, and applies matrix Hilbert--90. Its
conjugator is a genuine GL₃ actor. The degree-2n Frobenius commutes with every
linear outer class, by the determinant parameter, so this conjugacy forces
the linear factor of a cube-one actor to have cube determinant.

A lift of the mixed outer generator has a linear representative whose
determinant is the chosen noncube. This excludes cube-one elements in that
coset. Squaring reduces the other nontrivial coset to the first. Thus every
cube-one element of the literal `linearCircle` belongs to its marked
`linearCircleComponent`, retaining the original inner embedding. This
discharges the cube-containment premise of the parent's nonsplitting theorem.

Source: Aschbacher--Smith, Notation A.3.16, printed p.51 (PDF p.62), using
the projective descent of GLS3, Proposition 4.9.1(d), proved in
`Theory.SpecificGroups.PSL3.StandardCubicFixedNine.Descent`.
-/

public section

open scoped MatrixGroups
open Matrix Subgroup Matrix.PSL3.OuterSolvable Matrix.PSL3.ExtensionBorel

namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Cubic projective descent and the determinant outer parameter force the
linear factor of a cube-one actor with the source Frobenius to have cube determinant. -/
theorem circleField_det_cube_of_cube_one {n : ℕ} (hn : 0 < n)
    (hc : Nat.card F = 2 ^ (6 * n)) (m : GL (Fin 3) F)
    (h : (linearConj F m * fieldAction F (circleField F n)) ^ 3 = 1) :
    ∃ r : Fˣ, r ^ 3 = GeneralLinearGroup.det m := by
  obtain ⟨P, hP⟩ := Matrix.PSL3.StandardCubicFixedNine.Descent.exists_linear_conjugate_field
    m (circleField F n) (circleField_order hn hc) h
  have hcomm : Commute (qOuter F (fieldAction F (circleField F n)))
      (qOuter F (linearConj F P)) := by
    change Commute _ (linearOuterAction F P)
    rw [linearOuterAction_eq_circleDiagonal_det]
    exact circle_outer_commute n _
  have hcongr : MulAut.congr (linearConj F P)
      (linearConj F m * fieldAction F (circleField F n)) =
        linearConj F P * (linearConj F m * fieldAction F (circleField F n)) *
          (linearConj F P)⁻¹ := by
    ext x
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulAut.mul_apply]
    rfl
  have he := congrArg (qOuter F) hP
  rw [hcongr, map_mul, map_mul, map_inv] at he
  have he' : qOuter F (linearConj F m) * qOuter F (fieldAction F (circleField F n)) =
      qOuter F (fieldAction F (circleField F n)) := by
    apply mul_left_cancel (a := qOuter F (linearConj F P))
    rw [← hcomm.eq]
    exact (mul_inv_eq_iff_eq_mul).mp he
  have hm : qOuter F (linearConj F m) = 1 := by
    apply mul_right_cancel (b := qOuter F (fieldAction F (circleField F n)))
    simpa only [one_mul] using he'
  exact (linearConj_inner_iff_det_cube m).mp ((QuotientGroup.eq_one_iff _).mp hm)

private theorem not_cube_one_mixed_coset {n : ℕ} (hn : 0 < n)
    (hc : Nat.card F = 2 ^ (6 * n)) (a : Fˣ) (ha : Noncube a)
    (α : MulAut PSL(3,F))
    (hα : qOuter F α = qOuter F (fieldAction F (circleField F n)) * circleDiagonalOuter a)
    (h3 : α ^ 3 = 1) : False := by
  let β := linearConj F (circleDiagonalGL a) * fieldAction F (circleField F n)
  have hβ : qOuter F β =
      qOuter F (fieldAction F (circleField F n)) * circleDiagonalOuter a := by
    rw [map_mul]
    exact (circle_outer_commute n a).eq.symm
  have hi : α * β⁻¹ ∈ MulAut.innerSubgroup PSL(3,F) := by
    apply (QuotientGroup.eq_one_iff _).mp
    change qOuter F (α * β⁻¹) = 1
    rw [map_mul, map_inv, hα, ← hβ, mul_inv_cancel]
  obtain ⟨x, hx⟩ := hi
  obtain ⟨s, rfl⟩ := Matrix.PSL3.projection_surjective F x
  have hs : linearConj F (SpecialLinearGroup.toGL s) = α * β⁻¹ := by
    rw [linearConj_toGL]
    exact hx
  let m := SpecialLinearGroup.toGL s * circleDiagonalGL a
  have hm : linearConj F m * fieldAction F (circleField F n) = α := by
    dsimp only [m]
    rw [map_mul, mul_assoc, hs]
    change (α * β⁻¹) * β = α
    group
  obtain ⟨r, hr⟩ := circleField_det_cube_of_cube_one hn hc m (by rw [hm]; exact h3)
  apply ha r
  simpa only [m, map_mul, SpecialLinearGroup.coeToGL_det, circleDiagonalGL_det, one_mul]
    using hr

/-- Every cube-one element of A.3.16's literal linear circle group belongs to
the component defined by its original inner-automorphism embedding. -/
theorem linearCircle_cube_one_mem_component {n : ℕ} (hn : 0 < n)
    (hc : Nat.card F = 2 ^ (6 * n)) (a : Fˣ) (ha : Noncube a)
    (x : linearCircle F n a) (hx : x ^ 3 = 1) : x ∈ linearCircleComponent F n a := by
  classical
  let g := qOuter F (fieldAction F (circleField F n)) * circleDiagonalOuter a
  have hg : orderOf g = 3 := linearCircle_outer_order hn hc a ha
  have hg3 : g ^ 3 = 1 := by simpa only [hg] using pow_orderOf_eq_one g
  have hm : qOuter F x.val ∈ zpowers g := x.property
  have hx3 : x.val ^ 3 = 1 := congrArg Subtype.val hx
  have hj := mem_zpowers_iff_mem_range_orderOf.mp hm
  rw [hg] at hj
  obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hj
  have hj' : j < 3 := Finset.mem_range.mp hj
  change x.val ∈ MulAut.innerSubgroup PSL(3,F)
  interval_cases j
  · have he0 : qOuter F x.val = 1 := by simpa only [pow_zero] using he.symm
    exact (QuotientGroup.eq_one_iff _).mp he0
  · exact (not_cube_one_mixed_coset hn hc a ha x.val
      (by simpa only [pow_one] using he.symm) hx3).elim
  · have hx2 : (x.val ^ 2) ^ 3 = 1 := by
      rw [← pow_mul, Nat.mul_comm 2 3, pow_mul, hx3, one_pow]
    have he2 : qOuter F (x.val ^ 2) = g := by
      rw [map_pow, ← he, ← pow_mul]
      change g ^ (3 + 1) = g
      rw [pow_succ, hg3, one_mul]
    exact (not_cube_one_mixed_coset hn hc a ha (x.val ^ 2) he2 hx2).elim

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels
