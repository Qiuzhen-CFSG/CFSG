module

public import Theory.GroupTheory.SpecificGroups.DihedralFiveAutomorphisms

/-!
# Inner automorphisms of D₁₀ from the rotation action

If neither an automorphism nor its inverse squares the marked five-rotation,
its rotation action is identity or inversion. A small calculation on the
rotation and reflection images then constructs an inner conjugator.

The two no-squaring hypotheses are supplied by actual projective conjugation
in the J₃ overlap normalizer; no enumeration of the automorphism group is used.
-/

public section

namespace DihedralGroup

private theorem aut_ext_generators (a b : MulAut (DihedralGroup 5))
    (hr : a (r 1) = b (r 1)) (hs : a (sr 0) = b (sr 0)) : a = b := by
  ext x
  have hrot (i : ZMod 5) : a (r i) = b (r i) := by
    have he : (r i : DihedralGroup 5) = (r 1) ^ i.val := by
      rw [r_one_pow, ZMod.natCast_zmod_val]
    rw [he, map_pow, map_pow, hr]
  cases x with
  | r i => exact hrot i
  | sr i =>
    have he : (sr i : DihedralGroup 5) = sr 0 * r i := by simp
    rw [he, map_mul, map_mul, hs, hrot]

private theorem rotation_cases (x : DihedralGroup 5)
    (hpow : x ^ 5 = 1) (hne : x ≠ 1) :
    x = r 1 ∨ x = (r 1) ^ 2 ∨ x = (r 1) ^ 3 ∨ x = (r 1)⁻¹ := by
  revert x
  decide +kernel

private theorem inner_generator_pair (x y : DihedralGroup 5)
    (hx : x = r 1 ∨ x = (r 1)⁻¹) (hy : y ^ 2 = 1 ∧ y ≠ 1) :
    ∃ b : DihedralGroup 5,
      b * r 1 * b⁻¹ = x ∧ b * sr 0 * b⁻¹ = y := by
  revert x y
  decide +kernel

/-- A D₁₀ automorphism is inner when it and its inverse do not square the
literal marked five-rotation. -/
theorem five_aut_inner_of_no_square (a : MulAut (DihedralGroup 5))
    (h : a (r 1) ≠ (r 1) ^ 2) (hi : a.symm (r 1) ≠ (r 1) ^ 2) :
    ∃ b : DihedralGroup 5, a = MulAut.conj b := by
  have har : a (r 1) ^ 5 = 1 := by
    rw [← map_pow, show (r 1 : DihedralGroup 5) ^ 5 = 1 by decide, map_one]
  have hane : a (r 1) ≠ 1 := a.map_ne_one_iff.mpr (by decide)
  have hrotation : a (r 1) = r 1 ∨ a (r 1) = (r 1)⁻¹ := by
    rcases rotation_cases _ har hane with h1 | h2 | h3 | h4
    · exact Or.inl h1
    · exact (h h2).elim
    · apply False.elim
      apply hi
      apply a.injective
      rw [a.apply_symm_apply, map_pow, h3]
      decide +kernel
    · exact Or.inr h4
  have hs : a (sr 0) ^ 2 = 1 ∧ a (sr 0) ≠ 1 := by
    constructor
    · rw [← map_pow, show (sr 0 : DihedralGroup 5) ^ 2 = 1 by decide, map_one]
    · exact a.map_ne_one_iff.mpr (by decide)
  obtain ⟨b, hbr, hbs⟩ := inner_generator_pair _ _ hrotation hs
  exact ⟨b, aut_ext_generators a (MulAut.conj b) hbr.symm hbs.symm⟩

end DihedralGroup
