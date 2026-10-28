module

public import Theory.Mathieu.M24.Properties.Sylow3
public import Theory.GroupTheory.SylowElementConjugacy
import all Theory.Mathieu.M24.Properties.Sylow3

/-!
# Excluding order nine in native M₂₄

The published Heisenberg Sylow three subgroup has exponent three: cubing
its coordinates gives zero. Sylow conjugacy then excludes order nine from
every native element, including elements of mixed order with a factor nine.
This is an input for the odd-order spectrum in the degree-eleven trace proof.
The intentional private import reuses the established coordinate law and
preserves the shared public subgroup definition.
-/

public section
namespace Sporadic.Mathieu.M24OddCyclic

/-- The existing native Sylow three subgroup has exponent three. -/
theorem sylowThree_cube_eq_one (g : M24) (hg : g ∈ m24Sylow3Subgroup) : g ^ 3 = 1 := by
  obtain ⟨t, rfl⟩ := hg
  have h : ∀ t : Fin 3 × Fin 3 × Fin 3,
      Sporadic.Mathieu.product (Sporadic.Mathieu.product t t) t = (0, 0, 0) := by
    decide +kernel
  rw [show 3 = 2 + 1 by rfl, pow_succ, pow_two,
    ← Sporadic.Mathieu.evaluate_mul, ← Sporadic.Mathieu.evaluate_mul, h,
    Sporadic.Mathieu.evaluate_one]

/-- No native element order contains a factor nine. -/
theorem nine_not_dvd_orderOf (g : M24) : ¬ 9 ∣ orderOf g := by
  intro hg
  let x := g ^ (orderOf g / 9)
  have hx : orderOf x = 9 := orderOf_pow_orderOf_div (orderOf_pos g).ne' hg
  obtain ⟨y, hy⟩ := m24Sylow3.exists_isConj_of_orderOf_eq_prime_pow
    (show orderOf x = 3 ^ 2 from hx)
  obtain ⟨c, hc⟩ := isConj_iff.mp hy
  have hy3 := sylowThree_cube_eq_one y y.property
  have hx3 : x ^ 3 = 1 := by
    apply (MulAut.conj c).injective
    rw [map_pow, show MulAut.conj c x = (y : M24) from hc, hy3, map_one]
  have hd := orderOf_dvd_of_pow_eq_one hx3
  rw [hx] at hd
  norm_num at hd

end Sporadic.Mathieu.M24OddCyclic
