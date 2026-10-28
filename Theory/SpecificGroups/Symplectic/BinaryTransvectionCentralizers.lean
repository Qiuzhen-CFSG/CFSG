module

public import Theory.SpecificGroups.PSp4Three.Transvections
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.Field.ZMod

/-!
# Binary symplectic transvections and pointwise hyperplane kernels

A binary transvection determines its direction vector. Two such
transvections commute precisely when their directions are orthogonal.
An isometry fixing the orthogonal hyperplane of a nonzero vector is either
identity or its transvection: its displacement of a complementary vector
lies in the double orthogonal, hence in that vector's one-dimensional span.

These calculations use the existing ATLAS-attributed matrix/transvection
API and apply in every symplectic dimension. They identify the marked
point-center involution and its commuting pairs in the source argument
of Aschbacher–Smith 13.4.9, printed pp.906–907.
-/

public noncomputable section
namespace Matrix.PSp4Three
variable {n : ℕ}
local notation "F" => ZMod 2
local notation "V" => Vector n F

private theorem binary_cases (a : F) : a = 0 ∨ a = 1 := by
  exact (by decide : ∀ a : F, a = 0 ∨ a = 1) a

private theorem binary_form_swap (u v : V) : form u v = form v u := by
  rw [form_swap, CharTwo.neg_eq]

private theorem binary_add_self (v : V) : v + v = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (v i)

theorem binary_transvection_injective :
    Function.Injective (fun v : V => transvection v (1 : F)) := by
  intro v w h
  by_cases hv : v = 0
  · subst v
    by_contra hw
    exact transvection_ne_one (Ne.symm hw) one_ne_zero (h.symm.trans (transvection_zero_vector _))
  obtain ⟨x, hx⟩ := exists_form_left hv (1 : F)
  have he := congrArg (fun g : Sp n F => g • x) h
  simp only [transvection_apply, one_mul, hx, one_smul] at he
  have hh := add_left_cancel he
  rcases binary_cases (form x w) with h0 | h1
  · rw [h0, zero_smul] at hh
    exact (hv hh).elim
  · simpa only [h1, one_smul] using hh

theorem binary_transvection_commute_iff (v w : V) :
    Commute (transvection v (1 : F)) (transvection w 1) ↔ form v w = 0 := by
  refine ⟨?_, fun h => transvection_commute h _ _⟩
  intro h
  have he : transvection (transvection v 1 • w) (1 : F) = transvection w 1 := by
    rw [← transvection_conjugate, h.eq, mul_inv_cancel_right]
  have hf := binary_transvection_injective he
  have hz : form w v • v = 0 := by
    simpa only [transvection_apply, one_mul, add_eq_left] using hf
  rcases smul_eq_zero.mp hz with hz | hv
  · rwa [binary_form_swap]
  · simp [hv]

/-- The binary symplectic pointwise kernel of v-perp consists of one transvection. -/
theorem binary_eq_one_or_transvection_of_fixes_perp (v : V) (hv : v ≠ 0)
    (g : Sp n F) (hfix : ∀ y : V, form v y = 0 → g • y = y) :
    g = 1 ∨ g = transvection v 1 := by
  obtain ⟨x, hx⟩ := exists_form_left hv (1 : F)
  let W : Submodule F V := Submodule.span F {v}
  have hk : g • x + x ∈ W := by
    rw [← LinearMap.BilinForm.orthogonal_orthogonal form_nondegenerate
      form_alternating.isRefl W]
    intro y hy
    have hyv : form v y = 0 := hy v (Submodule.subset_span (by simp))
    have hh := preserves g y x
    change form (g • y) (g • x) = form y x at hh
    rw [hfix y hyv] at hh
    rw [map_add, hh, CharTwo.add_self_eq_zero]
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hk
  have hgx : g • x = x + a • v := by
    rw [ha, add_comm x, add_assoc, binary_add_self, add_zero]
  have determine {k : Sp n F} (hkx : k • x = g • x)
      (hkfix : ∀ y : V, form v y = 0 → k • y = y) : k = g := by
    apply ext_action
    intro y
    have hperp : form v (y + form y v • x) = 0 := by
      rw [map_add, map_smul, smul_eq_mul, binary_form_swap v x, hx, mul_one,
        binary_form_swap v y, CharTwo.add_self_eq_zero]
    have hh := (hkfix _ hperp).trans (hfix _ hperp).symm
    change toLinear k (y + form y v • x) = toLinear g (y + form y v • x) at hh
    simp only [map_add, map_smul, toLinear_apply, hkx] at hh
    exact add_right_cancel hh
  rcases binary_cases a with h0 | h1
  · left
    apply (determine (k := 1) ?_ ?_).symm
    · simp [hgx, h0]
    · intro y _; exact one_smul _ _
  · right
    apply (determine (k := transvection v 1) ?_ ?_).symm
    · simp [hgx, h1, transvection_apply, hx]
    · intro y hy
      simp [transvection_apply, binary_form_swap y v, hy]
end Matrix.PSp4Three
