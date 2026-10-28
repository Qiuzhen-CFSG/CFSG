module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.Max1RelativeRigidity.Core

/-!
# The literal max1 and marked-centralizer overlap

Here M is the actual ATLAS max1 subgroup, K its intrinsic binary kernel,
and E its image in the Janko matrix model. The marked pair vM lies in K;
v is its ambient image and C is the full ambient centralizer of v.
The intrinsic centralizer HM maps to H = M ∩ C, and D is this overlap
as a subgroup of C. In particular E lies in both local groups.

These are carrier identities and inclusions, without any generation or
amalgam-rigidity assertion. The later assembly uses precisely these maps.
Source context: GLS3 Table 5.3i, printed p.270, and the literal ATLAS
max1 words documented in `Cardinality.Subgroup`.
-/

set_option backward.isDefEq.respectTransparency true
@[expose] public section

open Subgroup
namespace Janko4.Max1AmalgamRigidity
abbrev M := Max1RelativeRigidity.M
abbrev K : Subgroup M := Max1RelativeRigidity.K
abbrev vM : M := Max1RelativeRigidity.v
abbrev v : Model := (vM : Model)
abbrev E : Subgroup Model := K.map M.subtype
abbrev C : Subgroup Model := centralizer ({v} : Set Model)
abbrev HM : Subgroup M := centralizer ({vM} : Set M)
abbrev H : Subgroup Model := HM.map M.subtype
abbrev D : Subgroup C := H.subgroupOf C

attribute [local irreducible] modelGroup matrixA matrixB Cardinality.max1Subgroup
  Cardinality.localKernel Cardinality.localX Cardinality.localY Cardinality.localKernelSeed

theorem vM_mem_K : vM ∈ K := by
  change Simplicity.Max1Fusion.kernelPair matrixA_mul_self matrixB_pow_four ∈ K
  rw [← Simplicity.Max1Fusion.KernelOrbits.maskValue_three
    matrixA_mul_self matrixB_pow_four]
  exact (Simplicity.Max1Fusion.KernelOrbits.maskValue
    matrixA_mul_self matrixB_pow_four 3).property

theorem v_mem_E : v ∈ E := mem_map.mpr ⟨vM, vM_mem_K, rfl⟩

theorem v_sq : v ^ 2 = 1 := by
  exact congrArg M.subtype (Simplicity.Max1Fusion.kernelPair_sq
    matrixA_mul_self matrixB_pow_four)

theorem E_le_M : E ≤ M := map_subtype_le K

theorem E_commute {e f : Model} (he : e ∈ E) (hf : f ∈ E) : Commute e f := by
  obtain ⟨e, heK, rfl⟩ := (mem_map (f := M.subtype) (K := K)).mp he
  obtain ⟨f, hfK, rfl⟩ := (mem_map (f := M.subtype) (K := K)).mp hf
  exact congrArg M.subtype (Cardinality.QuotientCount.Image.localKernel_commute
    matrixA_mul_self matrixB_pow_four e heK f hfK)

theorem E_le_C : E ≤ C := by
  intro e he
  exact mem_centralizer_singleton_iff.mpr (E_commute he v_mem_E)

theorem H_eq_inf : H = M ⊓ C := by
  ext g
  constructor
  · rintro ⟨m, hm, rfl⟩
    refine ⟨m.property, mem_centralizer_singleton_iff.mpr ?_⟩
    exact congrArg M.subtype (mem_centralizer_singleton_iff.mp hm)
  · rintro ⟨hm, hc⟩
    refine mem_map.mpr ⟨⟨g, hm⟩, mem_centralizer_singleton_iff.mpr ?_, rfl⟩
    exact Subtype.ext (mem_centralizer_singleton_iff.mp hc)

theorem H_le_C : H ≤ C := H_eq_inf ▸ inf_le_right

theorem mem_H_iff {g : Model} : g ∈ H ↔ g ∈ M ∧ g ∈ C := by
  rw [H_eq_inf, mem_inf]

end Janko4.Max1AmalgamRigidity
