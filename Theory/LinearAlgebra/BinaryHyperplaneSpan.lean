module
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Spanning by distinct binary hyperplanes

Two different binary linear functionals have kernels spanning the whole
space. Choose a vector on which their values differ. Any vector outside
both kernels then splits using that vector. Nonzero scalars are unique,
so no independent nonproportionality hypothesis is needed.

Source application: Aschbacher--Smith, 12.6.24(5), printed p.831.
-/

public section
namespace LinearMap
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
/-- Distinct binary functionals have complementary generating kernels. -/
theorem binary_ker_sup_eq_top_of_ne (f g : W →ₗ[ZMod 2] ZMod 2) (hne : f ≠ g) :
    f.ker ⊔ g.ker = ⊤ := by
  have hbin : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
  obtain ⟨x,hx⟩ : ∃ x, f x ≠ g x := by
    by_contra! hh
    exact hne (LinearMap.ext hh)
  have hl {y : W} (hy : f y = 0) : y ∈ f.ker ⊔ g.ker := (show f.ker ≤ f.ker ⊔ g.ker from le_sup_left) hy
  have hr {y : W} (hy : g y = 0) : y ∈ f.ker ⊔ g.ker := (show g.ker ≤ f.ker ⊔ g.ker from le_sup_right) hy
  apply top_unique
  intro v _
  by_cases hf : f v = 0
  · exact hl hf
  by_cases hg : g v = 0
  · exact hr hg
  have hvf := hbin _ hf
  have hvg := hbin _ hg
  by_cases hxf : f x = 0
  · have hxg : g x = 1 := hbin _ (by intro hh; exact hx (hxf.trans hh.symm))
    have hvx : v-x ∈ g.ker := by change g (v-x)=0; rw [map_sub,hvg,hxg,sub_self]
    exact sub_add_cancel v x ▸ Submodule.add_mem _ (hr hvx) (hl hxf)
  · have hxg : g x = 0 := by
      by_contra hh
      exact hx ((hbin _ hxf).trans (hbin _ hh).symm)
    have hvx : v-x ∈ f.ker := by change f (v-x)=0; rw [map_sub,hvf,hbin _ hxf,sub_self]
    exact sub_add_cancel v x ▸ Submodule.add_mem _ (hl hvx) (hr hxg)
end LinearMap
