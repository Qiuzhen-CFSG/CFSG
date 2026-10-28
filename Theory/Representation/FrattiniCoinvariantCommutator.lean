module
public import Mathlib.RepresentationTheory.Coinvariants
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Frattini

/-!
# Lifting full displacement through a Frattini kernel

An actual equivariant quotient whose kernel lies in the Frattini subgroup
lifts full linear displacement to a subgroup commutator equality. Only
normalization by the given actor is needed; the subgroup need not be normal
in the whole ambient group. This is used for the original closure and
selected component in Aschbacher–Smith 14.2.16, printed pp.985–986.
-/

public section
open Subgroup Representation
namespace Representation
variable {G A V : Type*} [Group G] [Group A] [AddCommGroup V] [Module (ZMod 2) V]

theorem subgroup_eq_commutator_of_frattini_coinvariants
    (Q : Subgroup G) [Finite Q]
    (actor : A →* G) (hn : actor.range ≤ normalizer (Q : Set G))
    (ρ : Representation (ZMod 2) A V)
    (f : Q →* Multiplicative V) (hf : Function.Surjective f)
    (hk : f.ker ≤ frattini Q)
    (ha : ∀ (a : A) (q q' : Q), (q' : G) = actor a * (q : G) * (actor a)⁻¹ →
      (f q').toAdd = ρ a (f q).toAdd)
    (hgen : Coinvariants.ker ρ = ⊤) :
    Q = ⁅Q,actor.range⁆ := by
  let N : Subgroup Q := ⁅Q,actor.range⁆.subgroupOf Q
  let W : Submodule (ZMod 2) V :=
    AddSubgroup.toZModSubmodule 2 (AddSubgroup.toSubgroup.symm (N.map f))
  have hspan : Coinvariants.ker ρ ≤ W := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a,v⟩,rfl⟩
    obtain ⟨q,hq⟩ := hf (Multiplicative.ofAdd v)
    let q' : Q := ⟨actor a * (q:G) * (actor a)⁻¹,
      le_normalizer_iff.mp hn (actor a) ⟨a,rfl⟩ q q.property⟩
    change Multiplicative.ofAdd (ρ a v - v) ∈ N.map f
    refine mem_map.mpr ⟨q' * q⁻¹, ?_, ?_⟩
    · change actor a * (q:G) * (actor a)⁻¹ * (q:G)⁻¹ ∈ ⁅Q,actor.range⁆
      rw [commutator_comm Q actor.range]
      exact commutator_mem_commutator ⟨a,rfl⟩ q.property
    · rw [map_mul,map_inv]
      have he : f q' = Multiplicative.ofAdd (ρ a v) := by
        have hh := ha a q q' rfl
        rw [hq] at hh
        exact congrArg Multiplicative.ofAdd hh
      rw [he,hq]
      exact congrArg Multiplicative.ofAdd (sub_eq_add_neg _ _).symm
  have hN : N.map f = ⊤ := by
    apply top_unique
    intro v _
    exact hspan (hgen ▸ (show v.toAdd ∈ (⊤ : Submodule (ZMod 2) V) from Submodule.mem_top))
  have hcover : N ⊔ frattini Q = ⊤ := by
    apply top_unique
    intro q _
    obtain ⟨n,hn,hfn⟩ := (show f q ∈ N.map f from hN ▸ mem_top _)
    have hz : q * n⁻¹ ∈ frattini Q := by
      apply hk
      change f (q * n⁻¹) = 1
      rw [map_mul,map_inv,hfn,mul_inv_cancel]
    simpa only [inv_mul_cancel_right] using
      (N ⊔ frattini Q).mul_mem (mem_sup_right hz) (mem_sup_left hn)
  have htop : N = ⊤ := frattini_nongenerating hcover
  apply le_antisymm
  · intro q hq
    exact (show (⟨q,hq⟩ : Q) ∈ N from htop ▸ mem_top _)
  · exact le_normalizer_iff_commutator_le_left.mp hn
end Representation
