module

public import Theory.Representation.TwoDimensionalOddOrder
public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.RepresentationTheory.Subrepresentation

/-!
# Cyclicity from a fixed line and a unipotent-invariant pairing

For a proper invariant orbit span, its right orthogonal complement is nonzero
by the dimension formula for an arbitrary bilinear form. It is invariant under
the given finite p-subgroup. In defining characteristic it contains a nonzero
fixed vector, so highest-line uniqueness puts the highest vector in this
orthogonal complement. A nonzero pairing with one orbit vector contradicts this.

Neither nondegeneracy nor invariance under the whole group is needed. This is
the linear-algebra step used for the actual G₂ tensors in GLS3, 2.8.6(a).
-/

public noncomputable section
open scoped TensorProduct
namespace Atlas.G2.TensorClassification.Cyclicity
variable {K G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- A fixed line and one nonzero invariant pairing force highest-vector cyclicity. -/
theorem orbit_span_eq_top_of_fixedLine_pairing (ρ : Representation K G V)
    (U : Subgroup G) [Finite U] (hc : ringChar K ≠ 0)
    (hp : IsPGroup (ringChar K) U) (v₀ : V)
    (hfixed : ∀ v : V, (∀ g ∈ U, ρ g v = v) → ∃ c : K, v = c • v₀)
    (B : LinearMap.BilinForm K V)
    (hB : ∀ g ∈ U, ∀ x y, B (ρ g x) (ρ g y) = B x y)
    (g₀ : G) (hpair : B (ρ g₀ v₀) v₀ ≠ 0) :
    Submodule.span K (Set.range fun g : G => ρ g v₀) = ⊤ := by
  let S : Subrepresentation ρ :=
    { toSubmodule := Submodule.span K (Set.range fun g : G => ρ g v₀)
      apply_mem_toSubmodule := by
        intro g v hv
        induction hv using Submodule.span_induction with
        | mem v hv =>
          obtain ⟨h, rfl⟩ := hv
          exact Submodule.subset_span ⟨g * h, by simp⟩
        | zero => simp
        | add x y hx hy ihx ihy => simpa using Submodule.add_mem _ ihx ihy
        | smul a x hx ih => simpa using Submodule.smul_mem _ a ih }
  change S.toSubmodule = ⊤
  by_contra hS
  let P : Subrepresentation (ρ.comp U.subtype) :=
    { toSubmodule := B.orthogonal S.toSubmodule
      apply_mem_toSubmodule := by
        intro g y hy
        change ∀ x ∈ S.toSubmodule, B x (ρ (g : G) y) = 0
        intro x hx
        have he := hB g g.property (ρ (g : G)⁻¹ x) y
        have hh : ρ (g : G) (ρ (g : G)⁻¹ x) = x := by
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
          rfl
        rw [hh] at he
        rw [he]
        exact hy _ (S.apply_mem_toSubmodule _ hx) }
  have hP : P.toSubmodule ≠ ⊥ := by
    intro hz
    have hd := LinearMap.BilinForm.finrank_add_finrank_orthogonal' (B := B) S.toSubmodule
    have hlt := Submodule.finrank_lt hS
    change B.orthogonal S.toSubmodule = ⊥ at hz
    rw [hz, finrank_bot] at hd
    omega
  let : Nontrivial P.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hP
  obtain ⟨v, hv, hfix⟩ := Representation.pGroup_fix_nonzero_vector hc hp P.toRepresentation
  obtain ⟨c, he⟩ := hfixed v.val (fun g hg => congrArg Subtype.val (hfix ⟨g, hg⟩))
  have hc0 : c ≠ 0 := by
    intro hc0
    apply hv
    apply Subtype.ext
    simpa [hc0] using he
  have hz := v.property (ρ g₀ v₀) (Submodule.subset_span ⟨g₀, rfl⟩)
  rw [he, map_smul, smul_eq_mul] at hz
  exact (mul_ne_zero hc0 hpair) hz

omit [FiniteDimensional K V] in
attribute [local ext] TensorProduct.ext in
/-- Tensor products preserve invariance of bilinear forms. -/
theorem tensorProductForm_invariant {W : Type*} [AddCommGroup W] [Module K W]
    (B : LinearMap.BilinForm K V) (C : LinearMap.BilinForm K W)
    (f : V →ₗ[K] V) (g : W →ₗ[K] W)
    (hf : ∀ x y, B (f x) (f y) = B x y)
    (hg : ∀ x y, C (g x) (g y) = C x y)
    (x y : V ⊗[K] W) :
    B.tmul C (TensorProduct.map f g x) (TensorProduct.map f g y) = B.tmul C x y := by
  have he : (B.tmul C).compl₁₂ (TensorProduct.map f g) (TensorProduct.map f g) =
      B.tmul C := by
    ext a b c d
    simp [hf, hg]
  exact LinearMap.congr_fun (LinearMap.congr_fun he x) y
end Atlas.G2.TensorClassification.Cyclicity

end
