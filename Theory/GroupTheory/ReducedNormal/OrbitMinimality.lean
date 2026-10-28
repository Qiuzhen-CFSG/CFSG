module
public import Theory.Representation.BinaryOffender.Homogeneous.OrbitMinimality
public import Theory.GroupTheory.ReducedNormal.SubspaceMinimality

/-!
# Minimality of the literal homogeneous orbit subgroup

An ambient subgroup inside the orbit of a homogeneous Irr⁺ seed is either
the whole orbit or centralized by the original actor, provided both the
actor and the orbit group normalize it. Pullback through the reduced-two
subgroup inclusion applies homogeneous orbit minimality without changing
the original fixed-space quotient or ambient embedding.

Source: Aschbacher--Smith D.3.4 and D.3.6, printed pp.193--196.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace Theory.GroupTheory.ReducedNormal
variable {G : Type*} [Group G] [Finite G] (H X T : Subgroup G)
  (hXH : X ≤ H) (hTH : T ≤ H)
  {I : Submodule (ZMod 2) (Additive (ModuleGroup H))}

include hXH hTH in
/-- Orbit-invariant subgroups are either the full original orbit or actor-central. -/
theorem subspaceImage_orbit_eq_or_le_centralizer
    (hI : Homogeneous.IsIrrPlusWith (representation H) (X.subgroupOf H) (T.subgroupOf H) I)
    (J : Subgroup G) (hJI : J ≤ componentOrbit (subspaceImage H I) T)
    (hXJ : X ≤ normalizer (J : Set G)) (hTJ : T ≤ normalizer (J : Set G)) :
    J = componentOrbit (subspaceImage H I) T ∨ J ≤ centralizer (X : Set G) := by
  let W := Representation.BinaryOffender.Homogeneous.orbitSpan (representation H) (T.subgroupOf H) I
  have hW : subspaceImage H W = componentOrbit (subspaceImage H I) T :=
    subspaceImage_orbitSpan H T hTH I
  have hJW : J ≤ subspaceImage H W := hJI.trans_eq hW.symm
  let U : Submodule (ZMod 2) (Additive (ModuleGroup H)) :=
    AddSubgroup.toZModSubmodule 2
      (((J.comap H.subtype).comap (ModuleGroup H).subtype).toAddSubgroup)
  have hUW : U ≤ W := by
    intro v hv
    obtain ⟨_, ⟨w, hw, rfl⟩, he⟩ := hJW hv
    have hwv : w = v.toMul := Subtype.ext (Subtype.ext he)
    change Additive.ofMul w ∈ W at hw
    simpa only [hwv, ofMul_toMul] using hw
  have hU (A : Subgroup G) (hAJ : A ≤ normalizer (J : Set G)) :
      A.subgroupOf H ≤ subspaceStabilizer (representation H) U := by
    apply le_subspaceStabilizer
    intro x hx v hv
    exact (mem_normalizer_iff.mp (hAJ hx) v.toMul.val.val).mp hv
  rcases hI.eq_or_le_fixedSpace_of_invariant (representation H) U hUW
      (hU X hXJ) (hU T hTJ) with he | hf
  · left
    apply le_antisymm hJI
    rw [←hW]
    rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact (show Additive.ofMul v ∈ U from he.symm ▸ hv)
  · right
    intro j hj
    obtain ⟨_, ⟨v, hv, rfl⟩, rfl⟩ := hJW hj
    exact (mem_reduced_fixedSpace_iff H X hXH (Additive.ofMul v)).mp (hf hj)
end Theory.GroupTheory.ReducedNormal

