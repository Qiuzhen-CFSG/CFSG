module

public import Theory.Representation.InvertedCubicTensor

/-!
# Marking the inverted cubic tensor by a specified fixed section

An injective linear map whose image is the inverter-fixed space identifies
that particular domain with the cubic multiplicity module. Transporting the
explicit tensor coordinates gives a tensor product with this marked domain,
with its original commuting action. Pure tensors have an explicit formula;
no unrelated space of the same dimension is substituted.

Source application: Aschbacher–Smith 8.2.8(5), printed pp.718–719, the
I/P = S₃ case, via `TensorRecognition.Cubic` and the literal B/U inclusion.
-/

public section
open scoped TensorProduct
namespace InvertedCubicTensor
variable {V B : Type*} [AddCommGroup V] [Module F V] [AddCommGroup B] [Module F B]
variable (σ : Representation F S₃ V) (ι : B →ₗ[F] V)
  (hi : Function.Injective ι) (hr : LinearMap.range ι = multiplicitySpace σ)

include hi in
/-- Fixedness and the source's two-copy dimension identity identify the
marked image with the entire inverter-fixed space. -/
theorem marked_range_eq_fixed [FiniteDimensional F V] [FiniteDimensional F B]
    (h : ∀ v, σ cubic v = v → v = 0)
    (hf : ∀ b, σ inverter (ι b) = ι b)
    (hd : Module.finrank F V = 2 * Module.finrank F B) :
    LinearMap.range ι = multiplicitySpace σ := by
  have hle : LinearMap.range ι ≤ multiplicitySpace σ := by
    rintro _ ⟨b, rfl⟩
    exact (mem_multiplicitySpace σ _).mpr (hf b)
  have hp := (pairEquiv σ h).finrank_eq
  rw [Module.finrank_prod, hd] at hp
  have hi' := (LinearEquiv.ofInjective ι hi).finrank_eq
  apply Submodule.eq_of_le_of_finrank_eq hle
  omega

/-- The specified domain is identified with the actual inverter-fixed space. -/
@[expose] noncomputable def markedFixedEquiv : B ≃ₗ[F] multiplicitySpace σ :=
  (LinearEquiv.ofInjective ι hi).trans (LinearEquiv.ofEq _ _ hr)

theorem markedFixedEquiv_coe (b : B) :
    (markedFixedEquiv σ ι hi hr b : V) = ι b := rfl

/-- Tensor coordinates retaining the marked fixed-section factor. -/
noncomputable def markedTensorEquiv (h : ∀ v, σ cubic v = v → v = 0) :
    BinaryPermutation.core (Fin 3) ⊗[F] B ≃ₗ[F] V :=
  ((TensorProduct.comm F _ _).trans
    (TensorProduct.congr (markedFixedEquiv σ ι hi hr) (LinearEquiv.refl F _))).trans
    (tensorEquiv σ h)

theorem markedTensorEquiv_tmul (h : ∀ v, σ cubic v = v → v = 0)
    (n : BinaryPermutation.core (Fin 3)) (b : B) :
    markedTensorEquiv σ ι hi hr h (n ⊗ₜ[F] b) =
      n.val 0 • ι b + n.val 2 • σ cubic (ι b) := by
  change tensorEquiv σ h (markedFixedEquiv σ ι hi hr b ⊗ₜ[F] n) = _
  exact tensorEquiv_tmul σ h _ _

variable {K : Type*} [Group K] (κ : Representation F K V)
  (τ : Representation F K B)
  (hc : ∀ k g v, κ k (σ g v) = σ g (κ k v))
  (he : ∀ k b, ι (τ k b) = κ k (ι b))

include hc he in
theorem markedTensorEquiv_equivariant_tmul
    (h : ∀ v, σ cubic v = v → v = 0) (k : K) (g : S₃)
    (n : BinaryPermutation.core (Fin 3)) (b : B) :
    markedTensorEquiv σ ι hi hr h
      (BinaryPermutation.coreRepresentation (Fin 3) g n ⊗ₜ[F] τ k b) =
        κ k (σ g (markedTensorEquiv σ ι hi hr h (n ⊗ₜ[F] b))) := by
  have hm : markedFixedEquiv σ ι hi hr (τ k b) =
      multiplicity σ κ hc k (markedFixedEquiv σ ι hi hr b) :=
    Subtype.ext (he k b)
  change tensorEquiv σ h (markedFixedEquiv σ ι hi hr (τ k b) ⊗ₜ[F]
    BinaryPermutation.coreRepresentation (Fin 3) g n) =
      κ k (σ g (tensorEquiv σ h (markedFixedEquiv σ ι hi hr b ⊗ₜ[F] n)))
  rw [hm, tensorEquiv_multiplicity, tensorEquiv_symmetric]

include hc he in
theorem markedTensorEquiv_equivariant
    (h : ∀ v, σ cubic v = v → v = 0) (k : K) (g : S₃)
    (z : BinaryPermutation.core (Fin 3) ⊗[F] B) :
    markedTensorEquiv σ ι hi hr h
      (TensorProduct.map (BinaryPermutation.coreRepresentation (Fin 3) g) (τ k) z) =
        κ k (σ g (markedTensorEquiv σ ι hi hr h z)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul n b => exact markedTensorEquiv_equivariant_tmul σ ι hi hr κ τ hc he h k g n b
  | add x y hx hy => simp only [map_add, hx, hy]

end InvertedCubicTensor
