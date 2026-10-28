module
public import Theory.SpecificGroups.BinaryLinear.Parabolics
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# Alternating forms preserved by the full binary linear group

In dimension at least three, such a form is zero. If a vector has a nonzero
pairing, invariance under every transvection centered on it forces the kernel
of its pairing form into its own line, contradicting the dimension bound.
This is the natural-module non-self-duality step in G.10.4, with the actual
invariant alternating form retained.
-/

public section
namespace LinearMap.BilinForm
open Module
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- There is no nonzero alternating form preserved by GL(V) in binary
dimension at least three. -/
theorem eq_zero_of_full_binary_linear_invariance
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.IsAlt)
    (hinv : ∀ e : V ≃ₗ[ZMod 2] V, ∀ x y, B (e x) (e y) = B x y)
    (hdim : 3 ≤ finrank (ZMod 2) V) : B = 0 := by
  ext v a
  by_contra ha
  change B v a ≠ 0 at ha
  have hv : v ≠ 0 := fun hv => ha (by rw [hv]; simp)
  have hk : (B v).ker ≤ Submodule.span (ZMod 2) {v} := by
    intro w hw
    by_contra hn
    obtain ⟨φ, hφw, hφ⟩ := (Submodule.span (ZMod 2) {v}).exists_le_ker_of_notMem hn
    have hφv := hφ (Submodule.mem_span_singleton_self v)
    have he := hinv (BinaryLinear.transvection v φ hφv) w a
    change B (w + φ w • v) (a + φ a • v) = B w a at he
    have hwa : B w v = 0 := hB.eq_iff.mpr hw
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul, hwa, hB.self_eq_zero, mul_zero, add_zero] at he
    exact (mul_ne_zero hφw ha) (add_eq_left.mp he)
  have hd := (B v).finrank_range_add_finrank_ker
  have hr : finrank (ZMod 2) (B v).range ≤ 1 := by
    simpa using (Submodule.finrank_le (B v).range)
  have hker : finrank (ZMod 2) (B v).ker ≤ 1 := by
    simpa [finrank_span_singleton hv] using Submodule.finrank_mono hk
  omega

end LinearMap.BilinForm
