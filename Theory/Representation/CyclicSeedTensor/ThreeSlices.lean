module
public import Theory.Representation.CyclicSeedTensor

/-!
# Three cyclic tensor slices

Three vectors spanning the second tensor factor give three slices spanning
the tensor product. In the binary natural plane plus a trivial line, the
cubic translates (e₀,1), (e₁,1), (e₀+e₁,1) span the full three-space.
The explicit coefficients apply without enumerating the first factor.

Source application: the three-conjugate product in Aschbacher–Smith,
*The Classification of Quasithin Groups*, 13.8.29(4), printed p.964.
-/

public section
open scoped TensorProduct
namespace Representation.CyclicSeedTensor
variable {k U V : Type*} [Field k] [AddCommGroup U] [Module k U]
  [AddCommGroup V] [Module k V]

/-- Three spanning vectors give three actual tensor slices, over any field. -/
theorem tensor_three_slices (v₀ v₁ v₂ : V)
    (hspan : ∀ v : V, ∃ r s t : k, v = r • v₀ + s • v₁ + t • v₂)
    (z : U ⊗[k] V) :
    ∃ u₀ u₁ u₂ : U, z = u₀ ⊗ₜ[k] v₀ + u₁ ⊗ₜ[k] v₁ + u₂ ⊗ₜ[k] v₂ := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0,0,0,by simp⟩
  | tmul u v =>
    obtain ⟨r,s,t,rfl⟩ := hspan v
    exact ⟨r • u,s • u,t • u,by simp [TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.smul_tmul]⟩
  | add z w hz hw =>
    obtain ⟨u₀,u₁,u₂,rfl⟩ := hz
    obtain ⟨v₀',v₁',v₂',rfl⟩ := hw
    exact ⟨u₀+v₀',u₁+v₁',u₂+v₂',by simp only [TensorProduct.add_tmul]; abel⟩

/-- The three cubic translates of the marked vector span the natural plane
plus its trivial line. -/
theorem natural_trivial_three_vectors (v : (Fin 2 → ZMod 2) × ZMod 2) :
    ∃ r s t : ZMod 2,
      v = r • (first, 1) + s • (second, 1) + t • (first + second, 1) := by
  refine ⟨v.2 + v.1 1, v.2 + v.1 0, v.2 + v.1 0 + v.1 1, ?_⟩
  ext i
  · fin_cases i <;> simp [first, second, add_assoc, CharTwo.add_self_eq_zero, CharTwo.add_cancel_left,
      add_comm, add_left_comm]
  · simp [add_assoc, CharTwo.add_self_eq_zero, CharTwo.add_cancel_left, add_comm, add_left_comm]

end Representation.CyclicSeedTensor
