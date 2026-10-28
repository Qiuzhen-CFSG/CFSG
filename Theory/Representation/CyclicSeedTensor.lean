module

public import Theory.Representation.QuadraticFourGroup.TensorClassification.ExternalTensor
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Tensor coordinates from a shared cyclic seed

Two commuting factors act on a module. A cyclic module for the first factor
and a two-dimensional module for the second share one marked vector. The
second factor contains a shear fixing that vector. Transporting the seed
relations along the first orbit constructs an injective tensor map; generation
by the product gives an equivalence. Its second tensor coordinate is the
image under the specified actor, which is never replaced by a new conjugator.

This is the linear algebra behind Aschbacher–Smith, 13.8.29(3), printed p.964.
The source application retains the literal subgroup quotient and proves
surjectivity from its conjugate-span definition.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace Representation.CyclicSeedTensor
open QuadraticFourGroup.TensorClassification
variable {k K I U W : Type*} [Field k] [Group K] [Group I]
  [AddCommGroup U] [Module k U] [AddCommGroup W] [Module k W]
  (ρ : Representation k (K × I) W) (σ : Representation k K U)
  (μ : Representation k I (Fin 2 → k))

abbrev first : Fin 2 → k := Pi.single 0 1
abbrev second : Fin 2 → k := Pi.single 1 1

private theorem expand (v : Fin 2 → k) : v = v 0 • first + v 1 • second := by
  ext i
  fin_cases i <;> simp [first, second]

private theorem commuting (a : I) (g : K) (w : W) :
    ρ (1,a) (ρ (g,1) w) = ρ (g,1) (ρ (1,a) w) := by
  simp only [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul, mul_one]

variable (f : σ.IntertwiningMap (ρ.comp (MonoidHom.inl K I))) (a : I)

def coordinateMap : (Fin 2 → U) →ₗ[k] W :=
  f.toLinearMap.comp (LinearMap.proj 0) +
    (ρ (1,a)).comp (f.toLinearMap.comp (LinearMap.proj 1))

theorem coordinateMap_apply (x : Fin 2 → U) :
    coordinateMap ρ σ f a x = f (x 0) + ρ (1,a) (f (x 1)) := rfl

def tensorMap : U ⊗[k] (Fin 2 → k) →ₗ[k] W :=
  (coordinateMap ρ σ f a).comp (TensorProduct.piScalarRight k k U (Fin 2)).toLinearMap

theorem tensorMap_tmul (u : U) (v : Fin 2 → k) :
    tensorMap ρ σ f a (u ⊗ₜ[k] v) = v 0 • f u + v 1 • ρ (1,a) (f u) := by
  change f (v 0 • u) + ρ (1,a) (f (v 1 • u)) = _
  simp only [map_smul]

variable (u₀ : U) (hcyclic : Submodule.span k (Set.range fun g => σ g u₀) = ⊤)
  (t : μ.IntertwiningMap (ρ.comp (MonoidHom.inr K I)))
  (ht : t first = f u₀) (ha : μ a first = second)

include ht ha in
theorem seed_tensor (v : Fin 2 → k) : tensorMap ρ σ f a (u₀ ⊗ₜ[k] v) = t v := by
  have ht1 : t second = ρ (1,a) (f u₀) := by
    rw [← ha, IntertwiningMap.isIntertwining, ht]
    rfl
  rw [tensorMap_tmul]
  conv_rhs => arg 2; rw [expand v]
  rw [map_add, map_smul, map_smul, ht, ht1]

include hcyclic ht ha in
theorem right_first (i : I) (u : U) :
    ρ (1,i) (f u) = (μ i first) 0 • f u + (μ i first) 1 • ρ (1,a) (f u) := by
  have ht1 : t second = ρ (1,a) (f u₀) := by
    rw [← ha, IntertwiningMap.isIntertwining, ht]
    rfl
  have hseed : ρ (1,i) (f u₀) =
      (μ i first) 0 • f u₀ + (μ i first) 1 • ρ (1,a) (f u₀) := by
    calc
      ρ (1,i) (f u₀) = t (μ i first) := by
        rw [IntertwiningMap.isIntertwining, ht]; rfl
      _ = _ := by
        conv_lhs => arg 2; rw [expand (μ i first)]
        rw [map_add, map_smul, map_smul, ht, ht1]
  let A := (ρ (1,i)).comp f.toLinearMap
  let B := (μ i first) 0 • f.toLinearMap +
    (μ i first) 1 • (ρ (1,a)).comp f.toLinearMap
  have he : A = B := LinearMap.ext_on_range hcyclic (fun g => by
    change ρ (1,i) (f (σ g u₀)) =
      (μ i first) 0 • f (σ g u₀) + (μ i first) 1 • ρ (1,a) (f (σ g u₀))
    rw [IntertwiningMap.isIntertwining]
    change ρ (1,i) (ρ (g,1) (f u₀)) =
      (μ i first) 0 • ρ (g,1) (f u₀) + (μ i first) 1 • ρ (1,a) (ρ (g,1) (f u₀))
    rw [commuting, commuting, hseed, map_add, map_smul, map_smul])
  exact LinearMap.congr_fun he u

include hcyclic ht ha in
theorem right_second (i : I) (u : U) :
    ρ (1,i) (ρ (1,a) (f u)) =
      (μ i second) 0 • f u + (μ i second) 1 • ρ (1,a) (f u) := by
  have h := right_first ρ σ μ f a u₀ hcyclic t ht ha (i*a) u
  rw [← Module.End.mul_apply, ← map_mul]
  simpa only [map_mul, Module.End.mul_apply, Prod.mk_mul_mk, one_mul, ha] using h

include hcyclic ht ha in
theorem tensorMap_intertwines (g : K × I) :
    (tensorMap ρ σ f a).comp (externalTensor σ μ g) =
      (ρ g).comp (tensorMap ρ σ f a) := by
  apply TensorProduct.ext'
  intro u v
  change tensorMap ρ σ f a (σ g.1 u ⊗ₜ[k] μ g.2 v) =
    ρ g (tensorMap ρ σ f a (u ⊗ₜ[k] v))
  have hleft (j : K) (v : Fin 2 → k) :
      tensorMap ρ σ f a (σ j u ⊗ₜ[k] v) = ρ (j,1) (tensorMap ρ σ f a (u ⊗ₜ[k] v)) := by
    simp only [tensorMap_tmul, IntertwiningMap.isIntertwining,
      MonoidHom.comp_apply, MonoidHom.inl_apply, map_add, map_smul, commuting]
  have hright (i : I) :
      tensorMap ρ σ f a (u ⊗ₜ[k] μ i v) = ρ (1,i) (tensorMap ρ σ f a (u ⊗ₜ[k] v)) := by
    rw [tensorMap_tmul, tensorMap_tmul, map_add, map_smul, map_smul,
      right_first ρ σ μ f a u₀ hcyclic t ht ha i u,
      right_second ρ σ μ f a u₀ hcyclic t ht ha i u]
    have hv := congrArg (μ i) (expand v)
    simp only [map_add, map_smul] at hv
    rw [hv]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    module
  rw [hleft, hright]
  simp only [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul,
    Prod.mk.eta]

include hcyclic ht ha in
theorem coordinateMap_injective (hf : Function.Injective f)
    (b : I) (hb0 : μ b first = first) (hb1 : μ b second = first + second) :
    Function.Injective (coordinateMap ρ σ f a) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm ?_ bot_le
  intro x hx
  have hz : f (x 0) + ρ (1,a) (f (x 1)) = 0 := hx
  have hz' := congrArg (ρ (1,b)) hz
  rw [map_add, map_zero,
    right_first ρ σ μ f a u₀ hcyclic t ht ha,
    right_second ρ σ μ f a u₀ hcyclic t ht ha, hb0, hb1] at hz'
  simp [first, second] at hz'
  have h1 : f (x 1) = 0 := by
    have : f (x 1) + (f (x 0) + ρ (1,a) (f (x 1))) = 0 := by
      simpa only [add_assoc, add_comm, add_left_comm] using hz'
    simpa only [hz, add_zero] using this
  have hx1 : x 1 = 0 := hf (h1.trans (map_zero f).symm)
  have hx0 : x 0 = 0 := by
    rw [hx1, map_zero, map_zero, add_zero] at hz
    exact hf (hz.trans (map_zero f).symm)
  ext i
  fin_cases i <;> assumption

include hcyclic ht ha in
theorem tensorMap_injective (hf : Function.Injective f)
    (b : I) (hb0 : μ b first = first) (hb1 : μ b second = first + second) :
    Function.Injective (tensorMap ρ σ f a) :=
  (coordinateMap_injective ρ σ μ f a u₀ hcyclic t ht ha hf b hb0 hb1).comp
    (TensorProduct.piScalarRight k k U (Fin 2)).injective

include hcyclic ht ha in
theorem seed_injective (hf : Function.Injective f) (hu₀ : u₀ ≠ 0)
    (b : I) (hb0 : μ b first = first) (hb1 : μ b second = first + second) :
    Function.Injective t := by
  intro v w he
  have htensor := tensorMap_injective ρ σ μ f a u₀ hcyclic t ht ha hf b hb0 hb1
    (show tensorMap ρ σ f a (u₀ ⊗ₜ[k] v) = tensorMap ρ σ f a (u₀ ⊗ₜ[k] w) by
      rw [seed_tensor ρ σ μ f a u₀ t ht ha, seed_tensor ρ σ μ f a u₀ t ht ha, he])
  have hc := congrArg (TensorProduct.piScalarRight k k U (Fin 2)) htensor
  ext i
  have hi : v i • u₀ = w i • u₀ := congrFun hc i
  exact (smul_left_injective k hu₀) hi

include hcyclic ht ha in
theorem tensorMap_surjective
    (hgen : Submodule.span k (Set.range fun gu : (K × I) × U => ρ gu.1 (f gu.2)) = ⊤) :
    Function.Surjective (tensorMap ρ σ f a) := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← hgen]
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨g,u⟩,rfl⟩
  refine ⟨externalTensor σ μ g (u ⊗ₜ[k] first), ?_⟩
  have he := LinearMap.congr_fun
    (tensorMap_intertwines ρ σ μ f a u₀ hcyclic t ht ha g) (u ⊗ₜ[k] first)
  simpa [tensorMap_tmul,first] using he

/-- The coordinates are constructed from the cyclic seed, retaining the chosen actor a. -/
def tensorEquiv (hf : Function.Injective f)
    (b : I) (hb0 : μ b first = first) (hb1 : μ b second = first + second)
    (hgen : Submodule.span k (Set.range fun gu : (K × I) × U => ρ gu.1 (f gu.2)) = ⊤) :
    (externalTensor σ μ).Equiv ρ :=
  .mk (LinearEquiv.ofBijective (tensorMap ρ σ f a)
    ⟨tensorMap_injective ρ σ μ f a u₀ hcyclic t ht ha hf b hb0 hb1,
      tensorMap_surjective ρ σ μ f a u₀ hcyclic t ht ha hgen⟩)
    (tensorMap_intertwines ρ σ μ f a u₀ hcyclic t ht ha)

end Representation.CyclicSeedTensor
