module

public import Mathlib.GroupTheory.OrderOfElement

/-!
# Order-three fusion through a kernel of exponent two

If two elements whose cubes are one have the same image, the word `x*y*x`
is a conjugator between them. Both this word and `x*y⁻¹` lie in the kernel,
so their squares are one. Lifting a conjugator proves reflection of fusion.
No finiteness or centrality of the kernel is required.

This supplies the order-three class marking for inflation from A6 in
Janko, *A characterization of the Mathieu simple groups, I*, §6.
-/

namespace MonoidHom
variable {G H : Type*} [Group G] [Group H]

/-- Equal images of cube roots of one are conjugate through a kernel of exponent two. -/
public theorem isConj_of_map_eq_of_cube_eq_one_of_square_kernel
    (f : G →* H) (hk : ∀ g, f g = 1 → g ^ 2 = 1)
    {x y : G} (hx : x ^ 3 = 1) (hy : y ^ 3 = 1)
    (hxy : f x = f y) : IsConj x y := by
  have hw : (x * y⁻¹) ^ 2 = 1 := hk _ (by simp [hxy])
  have hv : (x * y * x) ^ 2 = 1 := hk _ (by
    simpa only [map_mul, ← hxy, pow_succ, pow_zero, one_mul, map_one] using congrArg f hx)
  have hi : (x * y * x)⁻¹ = x * y * x :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hv)
  have hyi : y ^ 2 = y⁻¹ := by
    apply mul_right_cancel (b := y)
    simpa only [← pow_succ, inv_mul_cancel] using hy
  have hw' : x * y⁻¹ * x = y := by
    apply mul_right_cancel (b := y⁻¹)
    simpa only [pow_two, mul_assoc, mul_inv_cancel] using hw
  apply isConj_iff.mpr
  refine ⟨x * y * x, ?_⟩
  calc
    (x * y * x) * x * (x * y * x)⁻¹ = x * y * (x ^ 3) * y * x := by
      rw [hi]
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = x * (y ^ 2) * x := by simp only [hx, mul_one, pow_two, mul_assoc]
    _ = y := by rw [hyi, hw']

/-- A surjection with kernel of exponent two reflects fusion of elements
whose cubes are one. -/
public theorem isConj_of_map_isConj_of_cube_eq_one_of_square_kernel
    (f : G →* H) (hf : Function.Surjective f)
    (hk : ∀ g, f g = 1 → g ^ 2 = 1)
    {x y : G} (hx : x ^ 3 = 1) (hy : y ^ 3 = 1)
    (hxy : IsConj (f x) (f y)) : IsConj x y := by
  obtain ⟨a, ha⟩ := isConj_iff.mp hxy
  obtain ⟨g, rfl⟩ := hf a
  have hm : f (MulAut.conj g x) = f y := by
    simpa only [MulAut.conj_apply, map_mul, map_inv] using ha
  exact (isConj_iff.mpr ⟨g, rfl⟩).trans
    (f.isConj_of_map_eq_of_cube_eq_one_of_square_kernel hk
      (by simpa only [map_pow, map_one, MulAut.conj_apply] using
        congrArg (MulAut.conj g) hx) hy hm)

end MonoidHom
