module

public import Mathlib.Algebra.Group.Conj
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Squares in extensions with central elementary binary kernel

Two lifts of the same element have the same square when the kernel is central
of exponent two. If their images are conjugate and the first square is central,
the squares are equal as well. These statements concern the actual projection;
no covering-group recognition or conjugacy-table assumption is needed.

Application: the fusion marks in Aschbacher–Smith, I.2.2(5), printed p.412.
-/

public section
namespace MonoidHom
variable {G H : Type*} [Group G] [Group H]

/-- Changing a lift by a central element of exponent two preserves its square. -/
theorem square_eq_of_map_eq_of_central_binary_kernel (f : G →* H)
    (hc : f.ker ≤ Subgroup.center G) (h2 : ∀ z ∈ f.ker, z ^ 2 = 1)
    {x y : G} (hxy : f x = f y) : x ^ 2 = y ^ 2 := by
  have hk : x * y⁻¹ ∈ f.ker := by simp [mem_ker, hxy]
  have hh : Commute (x * y⁻¹) y := (Subgroup.mem_center_iff.mp (hc hk) y).symm
  calc
    x ^ 2 = ((x * y⁻¹) * y) ^ 2 := by rw [inv_mul_cancel_right]
    _ = (x * y⁻¹) ^ 2 * y ^ 2 := hh.mul_pow 2
    _ = y ^ 2 := by rw [h2 _ hk, one_mul]

/-- Fusion in the quotient preserves a central square. -/
theorem square_eq_of_isConj_map_of_central_binary_kernel (f : G →* H)
    (hf : Function.Surjective f) (hc : f.ker ≤ Subgroup.center G)
    (h2 : ∀ z ∈ f.ker, z ^ 2 = 1) {x y : G}
    (hs : x ^ 2 ∈ Subgroup.center G) (hxy : IsConj (f x) (f y)) :
    x ^ 2 = y ^ 2 := by
  obtain ⟨a, ha⟩ := isConj_iff.mp hxy
  obtain ⟨g, rfl⟩ := hf a
  have he : f (g * x * g⁻¹) = f y := by simpa only [map_mul, map_inv] using ha
  have hh := f.square_eq_of_map_eq_of_central_binary_kernel hc h2 he
  rw [conj_pow, Subgroup.mem_center_iff.mp hs g, mul_inv_cancel_right] at hh
  exact hh

end MonoidHom
