module
public import Theory.Representation.QuadraticFourGroup.TensorClassification.ExternalTensor

/-!
# A tensor slice and its shear displacement

An equivariant tensor marking transports the fixing and shear identities of
one factor to the literal slice in the tensor product. Both actors and the
marked vector are retained. The result applies to an arbitrary subspace of
that slice and to any field.

Source application: the natural second-tensor row of Aschbacher–Smith
13.8.29(4)–30, *The Classification of Quasithin Groups*, printed p.964.
-/

public section
open scoped TensorProduct
namespace Representation.QuadraticFourGroup.TensorClassification
variable {k K I U V W : Type*} [Field k] [Group K] [Group I]
  [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]
  (σ : Representation k K U) (μ : Representation k I V)
  (ρ : Representation k (K × I) W) (e : (externalTensor σ μ).Equiv ρ)

/-- The tensor slice inherits the fixing and shear identities of its marked
vector, with the original two actors retained. -/
theorem tensor_slice_shear (v : V) (a b : I)
    (hfix : μ b v = v) (hshear : μ b (μ a v) = μ a v + v)
    (P : Submodule k W) (hP : ∀ w ∈ P, ∃ u, e (u ⊗ₜ[k] v) = w) :
    (∀ w ∈ P, ρ (1,b) w = w) ∧
    (∀ w ∈ P, ρ (1,b) (ρ (1,a) w) - ρ (1,a) w = w) := by
  have he (i : I) (u : U) (z : V) :
      ρ (1,i) (e (u ⊗ₜ[k] z)) = e (u ⊗ₜ[k] μ i z) := by
    have hh := IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap (1,i) (u ⊗ₜ[k] z)
    simpa [externalTensor_apply, TensorProduct.map_tmul] using hh.symm
  constructor
  · intro w hw
    obtain ⟨u,rfl⟩ := hP w hw
    rw [he, hfix]
  · intro w hw
    obtain ⟨u,rfl⟩ := hP w hw
    rw [he, he, hshear, TensorProduct.tmul_add, map_add, add_sub_cancel_left]

end Representation.QuadraticFourGroup.TensorClassification
