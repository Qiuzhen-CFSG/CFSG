module

public import Theory.Representation.Triality.BinaryDegree.CarrierTransport.RationalGeneration.RootWords
import Mathlib.Tactic

/-!
# Coordinate elimination without enlarging the coefficient field

All pivoting, clearing and scaling coefficients are obtained by field operations
from the input coordinates. Consequently the existing rank-four elimination
algorithm carries a rational norm-one vector to e₀ + f₀ using rational root
words. This refines the unrestricted elimination in
`EvenOrthogonalElementaryGeneration.Coordinates`; see GLS3, §§1.10–1.12 and §2.7.
-/

@[expose] public section
noncomputable section
namespace Theory.AlgebraicGroup.RationalOrthogonal
open StandardRootSystem EvenOrthogonalElementary
variable {k : Type*} [Field k]
variable (F : Subfield k)

theorem upper_mem (i j : Fin 4) (hij : i ≠ j) {a : k} (ha : a ∈ F) :
    hyperbolicUpperRootPoint 4 i j hij a ∈ rootSubgroup F := by
  rcases lt_or_gt_of_ne hij with h | h
  · simpa [evenOrthogonalRootQuadraticPoint, evenOrthogonalRootIsometry,
      show (-1 : ℝ) ≠ 1 by norm_num, hyperbolicUpperRootPoint] using root_mem F (⟨(i, j), h⟩, ⟨1, by simp⟩, ⟨-1, by simp⟩) ha
  · simpa [evenOrthogonalRootQuadraticPoint, evenOrthogonalRootIsometry,
      show (-1 : ℝ) ≠ 1 by norm_num, hyperbolicUpperRootPoint] using root_mem F (⟨(j, i), h⟩, ⟨-1, by simp⟩, ⟨1, by simp⟩) ha

theorem lower_mem (i j : Fin 4) (hij : i ≠ j) {a : k} (ha : a ∈ F) :
    hyperbolicLowerRootPoint 4 i j hij a ∈ rootSubgroup F := by
  rcases lt_or_gt_of_ne hij with h | h
  · simpa [evenOrthogonalRootQuadraticPoint, evenOrthogonalRootIsometry,
      show (-1 : ℝ) ≠ 1 by norm_num, hyperbolicLowerRootPoint] using root_mem F (⟨(i, j), h⟩, ⟨-1, by simp⟩, ⟨-1, by simp⟩) ha
  · have heq : hyperbolicLowerRootPoint 4 i j hij a =
        hyperbolicLowerRootPoint 4 j i hij.symm (-a) := by
      apply Subtype.ext
      apply LinearEquiv.ext
      intro z
      apply Prod.ext
      · rfl
      · funext p
        simp [hyperbolicLowerRootPoint, hyperbolicLowerRoot,
          hyperbolicLowerRootLinearEquiv]
        ring
    rw [heq]
    simpa [evenOrthogonalRootQuadraticPoint, evenOrthogonalRootIsometry,
      show (-1 : ℝ) ≠ 1 by norm_num, hyperbolicLowerRootPoint] using root_mem F (⟨(j, i), h⟩, ⟨-1, by simp⟩, ⟨-1, by simp⟩) (F.neg_mem ha)

theorem skewUpper_mem (i j : Fin 4) (hij : i ≠ j) {a : k} (ha : a ∈ F) :
    hyperbolicSkewUpperRootPoint 4 i j hij a ∈ rootSubgroup F := by
  rcases lt_or_gt_of_ne hij with h | h
  · simpa [evenOrthogonalRootQuadraticPoint, evenOrthogonalRootIsometry,
      show (-1 : ℝ) ≠ 1 by norm_num, hyperbolicSkewUpperRootPoint] using root_mem F (⟨(i, j), h⟩, ⟨1, by simp⟩, ⟨1, by simp⟩) ha
  · have heq : hyperbolicSkewUpperRootPoint 4 i j hij a =
        hyperbolicSkewUpperRootPoint 4 j i hij.symm (-a) := by
      apply Subtype.ext
      apply LinearEquiv.ext
      intro z
      apply Prod.ext
      · funext p
        simp [hyperbolicSkewUpperRootPoint, hyperbolicSkewUpperRoot,
          hyperbolicSkewUpperRootLinearEquiv]
        ring
      · rfl
    rw [heq]
    simpa [evenOrthogonalRootQuadraticPoint, evenOrthogonalRootIsometry,
      show (-1 : ℝ) ≠ 1 by norm_num, hyperbolicSkewUpperRootPoint] using root_mem F (⟨(j, i), h⟩, ⟨1, by simp⟩, ⟨1, by simp⟩) (F.neg_mem ha)


private theorem single_mem (i j : Fin 4) : (Pi.single i (1 : k) : Fin 4 → k) j ∈ F := by
  classical
  by_cases h : j = i <;> simp [h]

private theorem upper_coordinates (i j : Fin 4) (hij : i ≠ j)
    {a : k} (ha : a ∈ F) {v : HyperbolicSpace k 4} (hv : HasCoordinates F v) :
    HasCoordinates F ((hyperbolicUpperRootPoint 4 i j hij a).1 v) := by
  rw [upper_apply]
  exact ⟨fun p => F.add_mem (hv.1 p) (F.mul_mem (F.mul_mem ha (hv.1 j)) (single_mem F i p)),
    fun p => F.sub_mem (hv.2 p) (F.mul_mem (F.mul_mem ha (hv.2 i)) (single_mem F j p))⟩

private theorem lower_coordinates (i j : Fin 4) (hij : i ≠ j)
    {a : k} (ha : a ∈ F) {v : HyperbolicSpace k 4} (hv : HasCoordinates F v) :
    HasCoordinates F ((hyperbolicLowerRootPoint 4 i j hij a).1 v) := by
  rw [lower_apply]
  exact ⟨hv.1, fun p => F.sub_mem
    (F.add_mem (hv.2 p) (F.mul_mem (F.mul_mem ha (hv.1 j)) (single_mem F i p)))
    (F.mul_mem (F.mul_mem ha (hv.1 i)) (single_mem F j p))⟩

private theorem skewUpper_coordinates (i j : Fin 4) (hij : i ≠ j)
    {a : k} (ha : a ∈ F) {v : HyperbolicSpace k 4} (hv : HasCoordinates F v) :
    HasCoordinates F ((hyperbolicSkewUpperRootPoint 4 i j hij a).1 v) := by
  rw [skewUpper_apply]
  exact ⟨fun p => F.sub_mem
    (F.add_mem (hv.1 p) (F.mul_mem (F.mul_mem ha (hv.2 j)) (single_mem F i p)))
    (F.mul_mem (F.mul_mem ha (hv.2 i)) (single_mem F j p)), hv.2⟩

private theorem root_coordinates (r : TypeDRootIndex 4)
    {a : k} (ha : a ∈ F) {v : HyperbolicSpace k 4} (hv : HasCoordinates F v) :
    HasCoordinates F ((evenOrthogonalRootQuadraticPoint 4 r a).1 v) := by
  rcases r with ⟨⟨⟨i, j⟩, hij⟩, ⟨s, hs⟩, ⟨t, ht⟩⟩
  rcases hs with hs | hs <;> rcases ht with ht | ht <;>
    subst s <;> subst t <;>
    norm_num only [evenOrthogonalRootQuadraticPoint, evenOrthogonalRootIsometry,
      reduceDIte]
  · exact lower_coordinates F i j hij.ne ha hv
  · exact upper_coordinates F j i hij.ne' ha hv
  · exact upper_coordinates F i j hij.ne ha hv
  · exact skewUpper_coordinates F i j hij.ne ha hv

variable [IsAlgClosed k]

/-- Every rational root word preserves the coefficient subspace. -/
theorem coordinates_apply {g : quadraticIsometrySubgroup (hyperbolicForm (k := k) 4)}
    (hg : g ∈ rootSubgroup F) {v : HyperbolicSpace k 4} (hv : HasCoordinates F v) :
    HasCoordinates F (g.1 v) := by
  have h : (∀ v, HasCoordinates F v → HasCoordinates F (g.1 v)) ∧
      (∀ v, HasCoordinates F v → HasCoordinates F ((g⁻¹).1 v)) := by
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨⟨r, a⟩, rfl⟩ := hx
      have hi : (evenOrthogonalRootQuadraticPoint 4 r (a : k))⁻¹ =
          evenOrthogonalRootQuadraticPoint 4 r (-(a : k)) := by
        apply inv_eq_of_mul_eq_one_right
        rw [← evenOrthogonalRootQuadraticPoint_add, add_neg_cancel,
          evenOrthogonalRootQuadraticPoint_zero]
      exact ⟨fun v hv => root_coordinates F r a.property hv,
        fun v hv => by rw [hi]; exact root_coordinates F r (F.neg_mem a.property) hv⟩
    | one => exact ⟨fun v hv => hv, fun v hv => hv⟩
    | mul x y hx hy ihx ihy =>
      refine ⟨fun v hv => ihx.1 _ (ihy.1 _ hv), fun v hv => ?_⟩
      simpa only [mul_inv_rev, point_mul_apply] using ihy.2 _ (ihx.2 _ hv)
    | inv x hx ih => simpa only [inv_inv] using ih.symm
  exact h.1 v hv

omit [IsAlgClosed k] in
private theorem exists_pivot (v : HyperbolicSpace k 4)
    (hv : hyperbolicForm 4 v ≠ 0) :
    ∃ g : quadraticIsometrySubgroup (hyperbolicForm (k := k) 4),
      g ∈ rootSubgroup F ∧ (g.1 v).1 0 ≠ 0 := by
  by_cases h : v.1 0 ≠ 0
  · exact ⟨1, one_mem _, h⟩
  · have h0 : v.1 0 = 0 := not_ne_iff.mp h
    obtain ⟨i, hi⟩ : ∃ i, v.1 i ≠ 0 := by
      by_contra hn
      push Not at hn
      apply hv
      simp [hyperbolicForm_apply, hn]
    have hi0 : (0 : Fin 4) ≠ i := by
      rintro rfl
      exact hi h0
    refine ⟨hyperbolicUpperRootPoint 4 0 i hi0 1, upper_mem F _ _ _ F.one_mem, ?_⟩
    simpa [upper_apply, h0] using hi

omit [IsAlgClosed k] in
private theorem exists_first_basis (v : HyperbolicSpace k 4) (hr : HasCoordinates F v)
    (hv : v.1 0 ≠ 0) :
    ∃ g : quadraticIsometrySubgroup (hyperbolicForm (k := k) 4),
      g ∈ rootSubgroup F ∧ (g.1 v).1 = Pi.single 0 1 := by
  let a := v.1 0
  let h := hyperbolicUpperRootPoint 4 1 0 (by decide) (-v.1 1 / a) *
    hyperbolicUpperRootPoint 4 2 0 (by decide) (-v.1 2 / a) *
    hyperbolicUpperRootPoint 4 3 0 (by decide) (-v.1 3 / a)
  have hh : h ∈ rootSubgroup F :=
    mul_mem (mul_mem (upper_mem F _ _ _ (F.div_mem (F.neg_mem (hr.1 1)) (hr.1 0)))
      (upper_mem F _ _ _ (F.div_mem (F.neg_mem (hr.1 2)) (hr.1 0))))
      (upper_mem F _ _ _ (F.div_mem (F.neg_mem (hr.1 3)) (hr.1 0)))
  have hx : (h.1 v).1 = Pi.single 0 a := by
    funext i
    fin_cases i <;>
      simp [h, upper_apply, a] <;> field_simp [hv] <;> ring
  let s := hyperbolicUpperRootPoint 4 1 0 (by decide) (-1 : k) *
    hyperbolicUpperRootPoint 4 0 1 (by decide) (1 - a) *
    hyperbolicUpperRootPoint 4 1 0 (by decide) a⁻¹
  have hs : s ∈ rootSubgroup F :=
    mul_mem (mul_mem (upper_mem F _ _ _ (F.neg_mem F.one_mem))
      (upper_mem F _ _ _ (F.sub_mem F.one_mem (hr.1 0))))
      (upper_mem F _ _ _ (F.inv_mem (hr.1 0)))
  refine ⟨s * h, mul_mem hs hh, ?_⟩
  rw [point_mul_apply]
  funext i
  fin_cases i <;> simp [s, upper_apply, hx, a, hv]

/-- Rational norm-one vectors can be reduced using only rational coefficients. -/
theorem exists_map_norm_one (v : HyperbolicSpace k 4) (hr : HasCoordinates F v)
    (hv : hyperbolicForm 4 v = 1) :
    ∃ g : quadraticIsometrySubgroup (hyperbolicForm (k := k) 4),
      g ∈ rootSubgroup F ∧ g.1 v = (Pi.single 0 1, Pi.single 0 1) := by
  obtain ⟨g, hg, hpivot⟩ := exists_pivot F v (by rw [hv]; exact one_ne_zero)
  obtain ⟨h, hh, hfirst⟩ := exists_first_basis F (g.1 v) (coordinates_apply F hg hr) hpivot
  let w := (h * g).1 v
  have hw : w.1 = Pi.single 0 1 := hfirst
  have hwr : HasCoordinates F w := coordinates_apply F (mul_mem hh hg) hr
  have hq : hyperbolicForm 4 w = 1 := by
    rw [(mem_quadraticIsometrySubgroup _ _).1 (h * g).2, hv]
  have hy0 : w.2 0 = 1 := by
    simpa [hyperbolicForm_apply, hw, Pi.single_apply] using hq
  let s := hyperbolicLowerRootPoint 4 1 0 (by decide) (-w.2 1) *
    hyperbolicLowerRootPoint 4 2 0 (by decide) (-w.2 2) *
    hyperbolicLowerRootPoint 4 3 0 (by decide) (-w.2 3)
  have hs : s ∈ rootSubgroup F :=
    mul_mem (mul_mem (lower_mem F _ _ _ (F.neg_mem (hwr.2 1)))
      (lower_mem F _ _ _ (F.neg_mem (hwr.2 2))))
      (lower_mem F _ _ _ (F.neg_mem (hwr.2 3)))
  refine ⟨s * (h * g), mul_mem hs (mul_mem hh hg), ?_⟩
  change s.1 w = _
  apply Prod.ext
  · simpa [s, lower_apply] using hw
  · funext i
    fin_cases i <;> simp [s, lower_apply, hw, hy0]

end Theory.AlgebraicGroup.RationalOrthogonal
