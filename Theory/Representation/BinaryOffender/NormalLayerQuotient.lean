module
public import Theory.Representation.BinaryOffender.CentralSectionAction
/-!
# A full faithful quotient action from a natural normal-layer marking

The fixed space of a normal layer is invariant under the ambient group.
Thus a surjection with exactly that kernel transports the induced quotient
action to its supplied coordinates, without requiring ambient equivariance
as input. Faithfulness on the layer kills the intersection of its ambient
kernel with the layer. Normality and self-centralization then kill the
whole kernel. The original coordinate map is equivariant by construction.
This supplies the full semilinear action from the original layer-equivariant
marker in Aschbacher–Smith B.6.10, printed p.117.
-/
public section
open Subgroup
namespace Representation.BinaryOffender
variable {H V W : Type*} [Group H]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
theorem exists_faithful_action_of_normal_layer_stable_quotient
    (α : Representation (ZMod 2) H V) (L : Subgroup H) [L.Normal]
    (hL : centralizer (L : Set H) ≤ L)
    (τ : Representation (ZMod 2) L W) (hτ : Function.Injective τ)
    (f : V →ₗ[ZMod 2] W) (hf : Function.Surjective f)
    (hstable : ∀ g, f.ker ≤ f.ker.comap (α g))
    (he : ∀ (g : L) v, f (α (g : H) v) = τ g (f v)) :
    ∃ ρ : Representation (ZMod 2) H W, Function.Injective ρ ∧
      (∀ g v, f (α g v) = ρ g (f v)) ∧
      ∀ (g : L) v, ρ (g : H) v = τ g v := by
  let e := f.quotKerEquivOfSurjective hf
  let ρ : Representation (ZMod 2) H W :=
    e.conjRingEquiv.toMonoidHom.comp (α.quotient f.ker hstable)
  have hρ (g : H) (v : V) : ρ g (f v) = f (α g v) := by
    simp [ρ,e,LinearEquiv.conjRingEquiv,Representation.quotient,Submodule.mapQ_apply]
  have hres (g : L) (v : W) : ρ (g : H) v = τ g v := by
    obtain ⟨v,rfl⟩ := hf v
    exact (hρ g v).trans (he g v)
  refine ⟨ρ,?_,fun g v => (hρ g v).symm,hres⟩
  have hNL : ρ.ker ⊓ L = ⊥ := by
    apply bot_unique
    intro a ha
    have heq : (⟨a,ha.2⟩ : L) = 1 := by
      apply hτ
      apply LinearMap.ext
      intro v
      rw [map_one,Module.End.one_apply]
      exact (hres ⟨a,ha.2⟩ v).symm.trans (LinearMap.congr_fun ha.1 v)
    exact congrArg Subtype.val heq
  have hc : ρ.ker ≤ centralizer (L : Set H) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (commutator_eq_bot_of_disjoint (disjoint_iff.mpr hNL))
  apply (MonoidHom.ker_eq_bot_iff ρ).mp
  exact bot_unique (fun _ hn => hNL.le ⟨hn,hL (hc hn)⟩)
theorem exists_faithful_action_of_normal_layer_quotient
    (α : Representation (ZMod 2) H V) (L : Subgroup H) [L.Normal]
    (hL : centralizer (L : Set H) ≤ L)
    (τ : Representation (ZMod 2) L W) (hτ : Function.Injective τ)
    (f : V →ₗ[ZMod 2] W) (hf : Function.Surjective f)
    (hk : f.ker = fixedSpace α L)
    (he : ∀ (g : L) v, f (α (g : H) v) = τ g (f v)) :
    ∃ ρ : Representation (ZMod 2) H W, Function.Injective ρ ∧
      (∀ g v, f (α g v) = ρ g (f v)) ∧
      ∀ (g : L) v, ρ (g : H) v = τ g v := by
  apply exists_faithful_action_of_normal_layer_stable_quotient α L hL τ hτ f hf _ he
  intro g
  rw [hk]
  exact fun v hv => (fixedSpace_stable_of_normalizes α
    (le_normalizer_of_normal : (⊤ : Subgroup H) ≤ normalizer (L : Set H))
    (mem_top g) v).mpr hv
end Representation.BinaryOffender
