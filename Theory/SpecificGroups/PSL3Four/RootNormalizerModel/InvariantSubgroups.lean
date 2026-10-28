module
public import Theory.SpecificGroups.PSL3Four.RootNormalizerModel.CubicGeometry

/-!
# Non-elementary subgroups invariant under the diagonal nine-group

The full diagonal group acts on UT₃(F₄) by independent scaling of the two
simple-root coordinates. If an invariant subgroup is not elementary abelian,
it contains an element whose two simple-root coordinates are nonzero. Its
square and diagonal orbit give the full center. Differences of diagonal
translates then give the two simple-root axes, which generate the root group.

This is the intrinsic Sylow calculation in the last paragraph of
Aschbacher--Smith 2.5.7, printed p.556. Identification of the original common
Sylow-three subgroup with this diagonal action is a separate ambient step.
-/

public section

open Subgroup
open scoped IsMulCommutative
namespace Matrix.PSL3Four.RootNormalizerModel

private theorem elementary_of_coordinates (A : Subgroup Root)
    (h : ∀ q ∈ A, q.x * q.y = 0) : IsElementaryAbelian 2 A := by
  have hs (q : A) : q ^ 2 = 1 := by
    rw [pow_two]
    apply Subtype.ext
    apply SylowModel.U.ext
    · change q.val.x + q.val.x = 0
      exact CharTwo.add_self_eq_zero _
    · change q.val.y + q.val.y = 0
      exact CharTwo.add_self_eq_zero _
    · change q.val.c + q.val.c + q.val.x * q.val.y = 0
      rw [CharTwo.add_self_eq_zero, zero_add, h _ q.property]
  have hi (q : A) : q⁻¹ = q := by
    exact inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hs q)
  have hc : IsMulCommutative A := ⟨⟨fun a b => by
    calc a * b = (a * b)⁻¹ := (hi _).symm
         _ = b * a := by rw [_root_.mul_inv_rev, hi, hi]⟩⟩
  exact { toIsMulCommutative := hc
          exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hs }

private theorem exists_unit_ne_one : ∃ u : Fˣ, (u : F) ≠ 1 := by
  obtain ⟨x, hx⟩ := exists_fieldFrobenius_ne
  have hx0 : x ≠ 0 := by intro h; exact hx (by simp [h])
  have hx1 : x ≠ 1 := by intro h; exact hx (by simp [h])
  exact ⟨Units.mk0 x hx0, hx1⟩

/-- A non-elementary subgroup invariant under both independent diagonal scalings
is the whole marked Sylow group. -/
theorem diagonal_invariant_eq_top (A : Subgroup Root)
    (hinv : ∀ d : Fˣ × Fˣ, ∀ q ∈ A, diagonal d q ∈ A)
    (hne : ¬ IsElementaryAbelian 2 A) : A = ⊤ := by
  obtain ⟨q, hq, hxy⟩ : ∃ q ∈ A, q.x * q.y ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (elementary_of_coordinates A h)
  have hx : q.x ≠ 0 := (mul_ne_zero_iff.mp hxy).1
  have hy : q.y ≠ 0 := (mul_ne_zero_iff.mp hxy).2
  have hz (c : F) : (⟨0, 0, c⟩ : Root) ∈ A := by
    by_cases hc : c = 0
    · subst c; exact A.one_mem
    · have hqq : (⟨0, 0, q.x * q.y⟩ : Root) ∈ A := by
        convert A.mul_mem hq hq using 1
        ext <;> simp [CharTwo.add_self_eq_zero]
      let u : Fˣ := Units.mk0 (c / (q.x * q.y)) (div_ne_zero hc hxy)
      convert hinv (u, 1) _ hqq using 1
      apply SylowModel.U.ext <;> simp [diagonal, u, hxy]
  have strip {a : Root} (ha : a ∈ A) : (⟨a.x, a.y, 0⟩ : Root) ∈ A := by
    convert A.mul_mem ha (hz a.c) using 1
    ext <;> simp [CharTwo.add_self_eq_zero]
  obtain ⟨u, hu⟩ := exists_unit_ne_one
  have hux : (↑u : F) * q.x + q.x ≠ 0 := by
    intro he
    have he' : (↑u : F) * q.x = q.x := by
      calc _ = (↑u : F) * q.x + q.x + q.x := by simp [add_assoc, CharTwo.add_self_eq_zero]
           _ = q.x := by rw [he, zero_add]
    exact hu (mul_right_cancel₀ hx (by simpa using he'))
  have huy : (↑u : F) * q.y + q.y ≠ 0 := by
    intro he
    have he' : (↑u : F) * q.y = q.y := by
      calc _ = (↑u : F) * q.y + q.y + q.y := by simp [add_assoc, CharTwo.add_self_eq_zero]
           _ = q.y := by rw [he, zero_add]
    exact hu (mul_right_cancel₀ hy (by simpa using he'))
  have hax : (⟨(↑u : F) * q.x + q.x, 0, 0⟩ : Root) ∈ A := by
    convert strip (A.mul_mem (hinv (u, 1) q hq) hq) using 1
    ext <;> simp [diagonal, CharTwo.add_self_eq_zero]
  have hay : (⟨0, (↑u : F) * q.y + q.y, 0⟩ : Root) ∈ A := by
    convert strip (A.mul_mem (hinv (1, u) q hq) hq) using 1
    ext <;> simp [diagonal, CharTwo.add_self_eq_zero]
  have hX (a : F) : (⟨a, 0, 0⟩ : Root) ∈ A := by
    by_cases ha : a = 0
    · subst a; exact A.one_mem
    · let v : Fˣ := Units.mk0 (a / ((↑u : F) * q.x + q.x)) (div_ne_zero ha hux)
      convert hinv (v, 1) _ hax using 1
      apply SylowModel.U.ext <;> simp [diagonal, v, hux]
  have hY (b : F) : (⟨0, b, 0⟩ : Root) ∈ A := by
    by_cases hb : b = 0
    · subst b; exact A.one_mem
    · let v : Fˣ := Units.mk0 (b / ((↑u : F) * q.y + q.y)) (div_ne_zero hb huy)
      convert hinv (1, v) _ hay using 1
      apply SylowModel.U.ext <;> simp [diagonal, v, huy]
  apply top_unique
  intro a _
  convert A.mul_mem (A.mul_mem (hY a.y) (hX a.x)) (hz a.c) using 1
  ext <;> simp

end Matrix.PSL3Four.RootNormalizerModel
