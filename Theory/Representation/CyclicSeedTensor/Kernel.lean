module

public import Theory.Representation.CyclicSeedTensor

/-!
# Detecting a tensor kernel by a shear

In the tensor constructed from a shared cyclic seed, a shear fixes the first
copy and adds it to the second. An invariant subspace containing the seed
plane is exactly that plane if its intersection with the first copy is the
seed line: subtracting the original vector from its shear isolates the second
coordinate, and then the first. Injectivity of the tensor coordinates also
identifies the first copy's intersection with the seed plane.

Source application: the kernel on U₀ in Aschbacher–Smith, 13.8.30, printed p.964.
-/

public section
open scoped TensorProduct
namespace Representation.CyclicSeedTensor
variable {k K I U W : Type*} [Field k] [Group K] [Group I]
  [AddCommGroup U] [Module k U] [AddCommGroup W] [Module k W]
  (ρ : Representation k (K × I) W) (σ : Representation k K U)
  (μ : Representation k I (Fin 2 → k))
  (f : σ.IntertwiningMap (ρ.comp (MonoidHom.inl K I))) (a : I)
  (u₀ : U) (hcyclic : Submodule.span k (Set.range fun g => σ g u₀) = ⊤)
  (t : μ.IntertwiningMap (ρ.comp (MonoidHom.inr K I)))
  (ht : t first = f u₀) (ha : μ a first = second)

include hcyclic ht ha in
theorem kernel_eq_seed_of_shear (b : I) (hb0 : μ b first = first) (hb1 : μ b second = first + second)
    (honto : Function.Surjective (coordinateMap ρ σ f a))
    (N : Submodule k W) (hseed : t.range.toSubmodule ≤ N)
    (hfirst : ∀ u, f u ∈ N → u ∈ k ∙ u₀)
    (hstable : ∀ w ∈ N, ρ (1,b) w ∈ N) : N = t.range.toSubmodule := by
  apply le_antisymm ?_ hseed
  intro w hw
  obtain ⟨x,rfl⟩ := honto w
  have hshear : ρ (1,b) (coordinateMap ρ σ f a x) =
      coordinateMap ρ σ f a x + f (x 1) := by
    rw [coordinateMap_apply, map_add,
      right_first ρ σ μ f a u₀ hcyclic t ht ha,
      right_second ρ σ μ f a u₀ hcyclic t ht ha, hb0, hb1]
    simp [first, second, add_comm, add_left_comm]
  have hx1 : f (x 1) ∈ N := by
    have he := N.sub_mem (hstable _ hw) hw
    rwa [hshear, add_sub_cancel_left] at he
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp (hfirst _ hx1)
  have ht1 : t second = ρ (1,a) (f u₀) := by
    rw [← ha, IntertwiningMap.isIntertwining, ht]
    rfl
  have hs1 : ρ (1,a) (f (x 1)) ∈ t.range.toSubmodule := by
    refine ⟨c • second, ?_⟩
    change t (c • second) = _
    rw [map_smul, ht1, ← hc, map_smul, map_smul]
  have hx0 : f (x 0) ∈ N := by
    have he := N.sub_mem hw (hseed hs1)
    simpa only [coordinateMap_apply, add_sub_cancel_right] using he
  obtain ⟨d,hd⟩ := Submodule.mem_span_singleton.mp (hfirst _ hx0)
  apply t.range.toSubmodule.add_mem ?_ hs1
  refine ⟨d • first, ?_⟩
  change t (d • first) = f (x 0)
  rw [map_smul, ht, ← hd, map_smul]
include hcyclic ht ha in
theorem first_mem_seed (hf : Function.Injective f)
    (b : I) (hb0 : μ b first = first) (hb1 : μ b second = first + second)
    (u : U) (hu : f u ∈ t.range.toSubmodule) : u ∈ k ∙ u₀ := by
  obtain ⟨v,hv⟩ := hu
  have hc : coordinateMap ρ σ f a ![u,0] =
      coordinateMap ρ σ f a (fun i => v i • u₀) := by
    calc
      _ = f u := by simp [coordinateMap_apply]
      _ = t v := hv.symm
      _ = tensorMap ρ σ f a (u₀ ⊗ₜ[k] v) :=
        (seed_tensor ρ σ μ f a u₀ t ht ha v).symm
      _ = _ := by simp only [tensorMap_tmul, coordinateMap_apply, map_smul]
  have he := coordinateMap_injective ρ σ μ f a u₀ hcyclic t ht ha hf b hb0 hb1 hc
  exact Submodule.mem_span_singleton.mpr ⟨v 0,(congrFun he 0).symm⟩
end Representation.CyclicSeedTensor
