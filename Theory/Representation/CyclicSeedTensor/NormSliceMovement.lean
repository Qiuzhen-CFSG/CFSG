module
public import Theory.Representation.CyclicSeedTensor.SliceMovement
public import Theory.Representation.CyclicSeedTensor

/-!
# Tensor shear modulo the cubic norm

The norm of a cubic vanishes on its natural binary plane and is the
identity on a trivial line. Thus the shear identity on the natural plane
extends to its sum with the trivial line after subtracting the cubic norm.
Equivariant tensor coordinates preserve this identity on the marked slice.

Source application: the extra-line row of Aschbacher–Smith 13.8.29(4)–30,
*The Classification of Quasithin Groups*, printed p.964.
-/

public section


open scoped TensorProduct
namespace Representation.QuadraticFourGroup.TensorClassification
variable {k K I U V W : Type*} [Field k] [Group K] [Group I]
  [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]
  (σ : Representation k K U) (μ : Representation k I V)
  (ρ : Representation k (K × I) W) (e : (externalTensor σ μ).Equiv ρ)

/-- Tensor coordinates transport the shear identity modulo the same cubic norm. -/
theorem tensor_slice_shear_mod_norm (v : V) (a b c : I)
    (hfix : μ b v = v)
    (hshear : μ b (μ a v) - μ a v = v - (μ c (μ c v) + μ c v + v))
    (P : Submodule k W) (hP : ∀ w ∈ P, ∃ u, e (u ⊗ₜ[k] v) = w) :
    (∀ w ∈ P, ρ (1,b) w = w) ∧
    (∀ w ∈ P, ρ (1,b) (ρ (1,a) w) - ρ (1,a) w =
      w - (ρ (1,c) (ρ (1,c) w) + ρ (1,c) w + w)) := by
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
    simp only [he]
    rw [← map_sub, ← TensorProduct.tmul_sub, hshear]
    simp only [TensorProduct.tmul_sub, TensorProduct.tmul_add, map_sub, map_add]

end Representation.QuadraticFourGroup.TensorClassification

namespace Representation.CyclicSeedTensor
variable {I : Type*} [Group I]
  (μ : Representation (ZMod 2) I (Fin 2 → ZMod 2))

/-- The natural plane plus a trivial line satisfies the corrected shear identity
for every marked trivial coordinate. -/
theorem natural_trivial_shear_mod_norm (a b c : I)
    (ha : μ a first = second) (hb0 : μ b first = first)
    (hb1 : μ b second = first + second)
    (hc0 : μ c first = second) (hc1 : μ c second = first + second)
    (ε : ZMod 2) :
    let ν := μ.prod (Representation.trivial (ZMod 2) I (ZMod 2))
    ν b (first, ε) = (first, ε) ∧
      ν b (ν a (first, ε)) - ν a (first, ε) =
        (first, ε) - (ν c (ν c (first, ε)) + ν c (first, ε) + (first, ε)) := by
  constructor
  · change (μ b first, ε) = (first, ε)
    rw [hb0]
  · change (μ b (μ a first) - μ a first, ε - ε) =
      (first - (μ c (μ c first) + μ c first + first), ε - (ε + ε + ε))
    rw [ha, hb1, hc0, hc1]
    ext i
    · fin_cases i <;> norm_num [first, second] <;> decide
    · fin_cases ε <;> decide

end Representation.CyclicSeedTensor
