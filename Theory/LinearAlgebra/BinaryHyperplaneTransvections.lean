module

public import Theory.GroupAction.BinaryTransvectionImage
public import Theory.LinearAlgebra.AlternatingFinrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Full transvections on a hyperplane of a binary alternating space

The full center action is specified by its actual displacements and by one
actor realizing each entire linear functional. Invariant alternating forms
force its center to lie in the radical of the restricted form when the
subspace has dimension at least three. For a hyperplane of a nondegenerate
space of dimension greater than two, the hyperplane is consequently the
orthogonal complement of the center.

The proof uses separation by linear functionals: if the center has a nonzero
pairing, the kernel of that pairing is just the center line, forcing the
subspace to have dimension at most two. This is the linear-algebra step in
Aschbacher--Smith, combined manuscript (1 March 2004), G.12.12(2), pp.374--375.
-/

@[expose] public section
namespace BinaryTransvection
variable {A V : Type*} [Group A] [AddCommGroup V] [Module (ZMod 2) V]

/-- Equality with the full group of transvections having the given center,
including the identity. No faithfulness on the subspace is required. -/
structure FullCenterAction (ρ : A →* (V ≃ₗ[ZMod 2] V))
    (W : Submodule (ZMod 2) V) (v : W) : Prop where
  nonzero : (v : V) ≠ 0
  fixes : ∀ a, ρ a v = (v : V)
  displacement : ∀ a (w : W), ρ a w - w ∈ Submodule.span (ZMod 2) {(v : V)}
  full : ∀ φ : Module.Dual (ZMod 2) W, φ v = 0 →
    ∃ a : A, ∀ w : W, ρ a w = (w : V) + φ w • (v : V)

/-- The common fixed-space criterion supplies the literal full action. -/
theorem fullCenterAction_of_fixedSpace
    (ρ : A →* (V ≃ₗ[ZMod 2] V)) (W : Submodule (ZMod 2) V)
    [FiniteDimensional (ZMod 2) W] (v : W) (hv : (v : V) ≠ 0)
    (hmove : ∀ a (w : W), ρ a w - w ∈ Submodule.span (ZMod 2) {(v : V)})
    (hfixed : ∀ w : W, (∀ a, ρ a w = (w : V)) ↔
      w ∈ Submodule.span (ZMod 2) {v}) : FullCenterAction ρ W v := by
  refine ⟨hv, ?_, hmove, (full_action_of_fixed_space ρ W v hv hmove hfixed).2⟩
  exact (hfixed v).mpr (Submodule.mem_span_singleton_self v)

/-- The converse fixed-space statement uses a separating functional. -/
theorem FullCenterAction.fixedSpace
    {ρ : A →* (V ≃ₗ[ZMod 2] V)} {W : Submodule (ZMod 2) V} {v : W}
    (h : FullCenterAction ρ W v) (w : W) :
    (∀ a, ρ a w = (w : V)) ↔ w ∈ Submodule.span (ZMod 2) {v} := by
  constructor
  · intro hw
    by_contra hn
    obtain ⟨φ, hφw, hφ⟩ := (Submodule.span (ZMod 2) {v}).exists_le_ker_of_notMem hn
    obtain ⟨a, ha⟩ := h.full φ (hφ (Submodule.mem_span_singleton_self v))
    have he : φ w • (v : V) = 0 := by
      have he := ha w
      rw [hw a] at he
      exact (add_eq_left.mp he.symm)
    exact (smul_ne_zero hφw h.nonzero) he
  · intro hw a
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hw
    simpa only [Submodule.coe_smul, map_smul] using congrArg (t • ·) (h.fixes a)

/-- Full transvections force the center into the radical of a sufficiently
large invariant alternating subspace. -/
theorem FullCenterAction.orthogonal
    {ρ : A →* (V ≃ₗ[ZMod 2] V)} {W : Submodule (ZMod 2) V} {v : W}
    [FiniteDimensional (ZMod 2) W] (h : FullCenterAction ρ W v)
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.IsAlt)
    (hinv : ∀ a x y, B (ρ a x) (ρ a y) = B x y)
    (hdim : 3 ≤ Module.finrank (ZMod 2) W) :
    ∀ w : W, B v w = 0 := by
  by_contra! hn
  obtain ⟨a, ha⟩ := hn
  let f : W →ₗ[ZMod 2] ZMod 2 := (B v).comp W.subtype
  have hk : f.ker ≤ Submodule.span (ZMod 2) {v} := by
    intro w hw
    by_contra hn
    obtain ⟨φ, hφw, hφ⟩ := (Submodule.span (ZMod 2) {v}).exists_le_ker_of_notMem hn
    obtain ⟨g, hg⟩ := h.full φ (hφ (Submodule.mem_span_singleton_self v))
    have he := hinv g w a
    rw [hg w, hg a] at he
    have hwa : B (w : V) v = 0 := hB.eq_iff.mpr hw
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul, hwa, hB.self_eq_zero, mul_zero, add_zero] at he
    have hz : φ w * B (v : V) a = 0 := add_eq_left.mp he
    exact (mul_ne_zero hφw ha) hz
  have hd := f.finrank_range_add_finrank_ker
  have hr : Module.finrank (ZMod 2) f.range ≤ 1 := by
    simpa using (Submodule.finrank_le f.range)
  have hv : v ≠ 0 := fun hv => h.nonzero (congrArg Subtype.val hv)
  have hker : Module.finrank (ZMod 2) f.ker ≤ 1 := by
    have := Submodule.finrank_mono hk
    simpa [finrank_span_singleton hv] using this
  omega

/-- G.12.12(2)'s geometric step with its invariant symplectic form explicit.
Evenness of the ambient dimension supplies the required hyperplane dimension. -/
theorem FullCenterAction.hyperplane_eq_orthogonal
    {ρ : A →* (V ≃ₗ[ZMod 2] V)} {W : Submodule (ZMod 2) V} {v : W}
    [FiniteDimensional (ZMod 2) V] (h : FullCenterAction ρ W v)
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (hinv : ∀ a x y, B (ρ a x) (ρ a y) = B x y)
    (hW : Module.finrank (ZMod 2) W + 1 = Module.finrank (ZMod 2) V)
    (hdim : 2 < Module.finrank (ZMod 2) V) : W = (B v).ker := by
  obtain ⟨n, hn⟩ := AlternatingForm.even_finrank B hB hnd
  have hdW : 3 ≤ Module.finrank (ZMod 2) W := by omega
  have hle : W ≤ (B v).ker := fun w hw => h.orthogonal B hB hinv hdW ⟨w, hw⟩
  have hne : B (v : V) ≠ 0 := by
    intro he
    exact h.nonzero (hnd.1 v (fun w => by rw [he]; rfl))
  apply Submodule.eq_of_le_of_finrank_eq hle
  have hd := (B (v : V)).finrank_range_add_finrank_ker
  have hr : (B (v : V)).range = ⊤ := Module.Dual.range_eq_top_of_ne_zero hne
  rw [hr] at hd
  simp only [finrank_top, Module.finrank_self] at hd
  omega

end BinaryTransvection
