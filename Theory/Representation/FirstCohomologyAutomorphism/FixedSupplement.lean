module
public import Theory.Representation.FirstCohomologyAutomorphism.Subkernel
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Fixed supplements from vanishing first cohomology

Let V be a module in H and U an overgroup of V with [U,H] ≤ V.
If the kernel of the action quotient centralizes U and H¹ vanishes,
then U = V C_U(H). For each u, conjugation by u has displacement in V;
the subkernel cohomology theorem makes it inner by an element of V.
The quotient kernel may properly contain V.

Source application: Aschbacher–Smith 9.2.2, printed p.730, with
H = L₀, U = Ω₁Z(O₂(L₀T)), and the original tensor module V.
-/

public section
open Subgroup
open scoped commutatorElement
namespace Representation.OneCohomology
variable {k G A W : Type*} [Field k] [Group G] [Group A]
  [AddCommGroup W] [Module k W]

/-- Vanishing first cohomology splits a centralizing extension of the module.
The quotient kernel may be larger than the module. -/
theorem eq_sup_inf_centralizer_of_H1_zero
    (H V U : Subgroup G) (hVH : V ≤ H) (hVU : V ≤ U)
    (f : H →* A) (hf : Function.Surjective f)
    (e : V ≃* Multiplicative W) (ρ : Representation k A W)
    (he : ∀ (g : H) (w : W),
      (e.symm (Multiplicative.ofAdd (ρ (f g) w)) : G) =
        g * (e.symm (Multiplicative.ofAdd w) : G) * (g : G)⁻¹)
    [Subsingleton (H1 ρ)]
    (hker : f.ker.map H.subtype ≤ centralizer (U : Set G))
    (hcomm : ⁅U,H⁆ ≤ V) : U = V ⊔ (U ⊓ centralizer (H : Set G)) := by
  have hUN : U ≤ normalizer (H : Set G) :=
    le_normalizer_iff_commutator_le_right.mpr (hcomm.trans hVH)
  apply le_antisymm _ (sup_le hVU inf_le_left)
  intro u hu
  let N := V.subgroupOf H
  let eN : N ≃* Multiplicative W := (subgroupOfEquivOfLe hVH).trans e
  let α : MulAut H := H.normalizerMonoidHom ⟨u,hUN hu⟩
  have heN (g : H) (w : W) :
      (eN.symm (Multiplicative.ofAdd (ρ (f g) w)) : H) =
        g * (eN.symm (Multiplicative.ofAdd w) : H) * g⁻¹ := by
    apply Subtype.ext
    exact he g w
  have hdis (g : H) : α g * g⁻¹ ∈ N := by
    change u * (g : G) * u⁻¹ * (g : G)⁻¹ ∈ V
    exact hcomm (commutator_mem_commutator hu g.property)
  have hfix (n : H) (hn : n ∈ f.ker) : α n = n := by
    apply Subtype.ext
    change u * (n : G) * u⁻¹ = n
    have hc := hker (mem_map.mpr ⟨n,hn,rfl⟩) u hu
    change u * (n : G) = (n : G) * u at hc
    rw [hc,mul_inv_cancel_right]
  obtain ⟨n,hn⟩ := automorphism_inner_of_H1_zero_of_subkernel N f hf eN ρ heN α hdis hfix
  have hnV : ((n : H) : G) ∈ V := n.property
  have hnu : ((n : H) : G) * u ∈ U ⊓ centralizer (H : Set G) := by
    refine ⟨U.mul_mem (hVU hnV) hu,?_⟩
    intro h hh
    have heq := congrArg Subtype.val (hn ⟨h,hh⟩)
    change u * h * u⁻¹ = ((n : H) : G)⁻¹ * h * ((n : H) : G) at heq
    calc
      h * (((n : H) : G) * u) = ((n : H) : G) *
          (((n : H) : G)⁻¹ * h * ((n : H) : G)) * u := by group
      _ = ((n : H) : G) * (u * h * u⁻¹) * u := by rw [heq]
      _ = (((n : H) : G) * u) * h := by group
  have hh := (V ⊔ (U ⊓ centralizer (H : Set G))).mul_mem
    ((show V ≤ V ⊔ (U ⊓ centralizer (H : Set G)) from le_sup_left) (V.inv_mem hnV))
    ((show U ⊓ centralizer (H : Set G) ≤ V ⊔ (U ⊓ centralizer (H : Set G)) from le_sup_right) hnu)
  simpa only [inv_mul_cancel_left] using hh
end Representation.OneCohomology
