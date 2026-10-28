module
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Movement and fixed vectors of an involution on a subspace

For an actor of order two, the displacement span of any subspace is the
image of the generator minus the identity restricted to that subspace.
Rank-nullity therefore counts its movement and its ambient fixed vectors,
without requiring the subspace to be invariant.

Source application: the actual cubic displacement space in Aschbacher--Smith,
proof of12.6.26, printed p.833.
-/

public section
namespace Representation.BinaryOffender
open Subgroup
variable {J W : Type*} [Group J] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

theorem card_two_moved_add_fixed_finrank (ρ : Representation (ZMod 2) J W)
    (B : Subgroup J) (hB : Nat.card B = 2) (I : Submodule (ZMod 2) W) :
    Module.finrank (ZMod 2) (subspaceCommutator ρ I B) +
      Module.finrank (ZMod 2) (I ⊓ fixedSpace ρ B : Submodule (ZMod 2) W) =
      Module.finrank (ZMod 2) I := by
  obtain ⟨t,ht,hu⟩ := (Nat.card_eq_two_iff' (1 : B)).mp hB
  have hcases (b : B) : b = 1 ∨ b = t := by
    by_cases hb : b = 1
    · exact Or.inl hb
    · exact Or.inr (hu b hb)
  let f := (ρ t.val - LinearMap.id).domRestrict I
  have hr : subspaceCommutator ρ I B = LinearMap.range f := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨b,hb,v,hv,rfl⟩
      rcases hcases ⟨b,hb⟩ with he | he
      · have he' : b = 1 := congrArg Subtype.val he
        rw [he',map_one,Module.End.one_apply,sub_self]
        exact Submodule.zero_mem _
      · have he' : b = t.val := congrArg Subtype.val he
        exact ⟨⟨v,hv⟩,by change ρ t.val v-v = ρ b v-v; rw [he']⟩
    · rintro _ ⟨v,rfl⟩
      exact Submodule.subset_span ⟨t.val,t.property,v,v.property,rfl⟩
  have hk (v : I) : f v = 0 ↔ (v : W) ∈ fixedSpace ρ B := by
    change ρ t.val v-v = 0 ↔ _
    rw [sub_eq_zero]
    constructor
    · intro hv b
      rcases hcases b with rfl | rfl
      · exact LinearMap.congr_fun ρ.map_one v
      · exact hv
    · intro hv
      exact hv t
  let e : LinearMap.ker f ≃ₗ[ZMod 2] (I ⊓ fixedSpace ρ B : Submodule (ZMod 2) W) := {
    toFun := fun v => ⟨v.val,v.val.property,(hk v.val).mp v.property⟩
    invFun := fun v => ⟨⟨v,v.property.1⟩,(hk ⟨v,v.property.1⟩).mpr v.property.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  rw [hr,←e.finrank_eq]
  exact f.finrank_range_add_finrank_ker
end Representation.BinaryOffender

