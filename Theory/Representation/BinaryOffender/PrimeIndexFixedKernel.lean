module
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Pointwise kernels at prime index

A subgroup of prime relative index is the full pointwise kernel of any
subspace it fixes which is not fixed by the larger group. A factor fixing
the subspace can then be split off from a normalized product.

These elementary action facts identify the dihedral-factor centralizer
in Aschbacher--Smith 15.1.16(a), printed p.1092.
-/

public section
open Subgroup Representation
open scoped Pointwise
namespace Representation.BinaryOffender
variable {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]

/-- Prime relative index identifies a proper pointwise kernel. -/
theorem subspaceKernel_eq_of_prime_index (ρ : Representation (ZMod 2) D W)
    (A B : Subgroup D) (U : Submodule (ZMod 2) W)
    (hBA : B ≤ A) (hi : (B.relIndex A).Prime)
    (hf : U ≤ fixedSpace ρ B) (hn : ¬ U ≤ fixedSpace ρ A) :
    subspaceKernel ρ U A = B := by
  let K := subspaceKernel ρ U A
  have hBK : B ≤ K := fun b hb => ⟨hBA hb,fun v hv => hf hv ⟨b,hb⟩⟩
  have hKA : K ≤ A := subspaceKernel_le ρ U A
  have hmul := relIndex_mul_relIndex B K A hBK hKA
  have hp : (B.relIndex K * K.relIndex A).Prime := hmul ▸ hi
  rcases Nat.prime_mul_iff.mp hp with ⟨_,hKAone⟩ | ⟨_,hBKone⟩
  · have hAK := relIndex_eq_one.mp hKAone
    exact False.elim (hn (fun v hv a => (hAK a.property).2 v hv))
  · exact le_antisymm (relIndex_eq_one.mp hBKone) hBK

/-- An actor fixing the whole support can be split off from its pointwise kernel. -/
theorem subspaceKernel_sup_of_fixed (ρ : Representation (ZMod 2) D W)
    (A B : Subgroup D) (U : Submodule (ZMod 2) W)
    (hn : B ≤ normalizer (A : Set D)) (hf : U ≤ fixedSpace ρ B) :
    subspaceKernel ρ U (A ⊔ B) = subspaceKernel ρ U A ⊔ B := by
  apply le_antisymm
  · intro x hx
    have hm : x ∈ (A : Set D) * (B : Set D) := by
      rw [←coe_mul_of_right_le_normalizer_left A B hn]
      exact hx.1
    obtain ⟨a,ha,b,hb,rfl⟩ := hm
    have hak : a ∈ subspaceKernel ρ U A := by
      refine ⟨ha,?_⟩
      intro v hv
      have he := hx.2 v hv
      have hbfix : ρ b v = v := hf hv ⟨b,hb⟩
      simpa only [map_mul,Module.End.mul_apply,hbfix] using he
    exact mul_mem_sup hak hb
  · apply sup_le
    · exact fun a ha => ⟨mem_sup_left ha.1,ha.2⟩
    · exact fun b hb => ⟨mem_sup_right hb,fun v hv => hf hv ⟨b,hb⟩⟩
end Representation.BinaryOffender
