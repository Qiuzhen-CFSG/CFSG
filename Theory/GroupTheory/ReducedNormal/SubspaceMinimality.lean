module
public import Theory.GroupTheory.ReducedNormal.SubspaceGroupConsequences

/-!
# Minimality of the literal ambient seed

A proper subgroup of an Irr⁺ seed which is normalized by its actor is
centralized by that actor. The proof pulls the subgroup back through the
original inclusion of the reduced-two subgroup and applies invariant
subspace minimality. No quotient or action marking is changed.

Source: Aschbacher–Smith, A.1.40–41 and D.3.6, printed pp.31 and196.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
open Representation.BinaryOffender
namespace Theory.GroupTheory.ReducedNormal
variable {G : Type*} [Group G] (H X : Subgroup G) (hXH : X ≤ H)
  {I : Submodule (ZMod 2) (Additive (ModuleGroup H))}

include hXH in
/-- Invariant subgroup minimality in the original ambient group. -/
theorem subspaceImage_eq_or_le_centralizer
    (hI : IsIrrPlus (representation H) (X.subgroupOf H) I)
    (J : Subgroup G) (hJI : J ≤ subspaceImage H I)
    (hXJ : X ≤ normalizer (J : Set G)) :
    J = subspaceImage H I ∨ J ≤ centralizer (X : Set G) := by
  let U : Submodule (ZMod 2) (Additive (ModuleGroup H)) :=
    AddSubgroup.toZModSubmodule 2
      (((J.comap H.subtype).comap (ModuleGroup H).subtype).toAddSubgroup)
  have hUI : U ≤ I := by
    intro v hv
    obtain ⟨_, ⟨w, hw, rfl⟩, he⟩ := hJI hv
    have hwv : w = v.toMul := Subtype.ext (Subtype.ext he)
    change Additive.ofMul w ∈ I at hw
    simpa only [hwv, ofMul_toMul] using hw
  have hU : X.subgroupOf H ≤ subspaceStabilizer (representation H) U := by
    apply le_subspaceStabilizer
    intro x hx v hv
    exact (mem_normalizer_iff.mp (hXJ hx) v.toMul.val.val).mp hv
  rcases hI.eq_or_le_fixedSpace (representation H) hU hUI with he | hf
  · left
    apply le_antisymm hJI
    rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact (show Additive.ofMul v ∈ U from he.symm ▸ hv)
  · right
    intro j hj
    obtain ⟨_, ⟨v, hv, rfl⟩, rfl⟩ := hJI hj
    exact (mem_reduced_fixedSpace_iff H X hXH (Additive.ofMul v)).mp (hf hj)

end Theory.GroupTheory.ReducedNormal
