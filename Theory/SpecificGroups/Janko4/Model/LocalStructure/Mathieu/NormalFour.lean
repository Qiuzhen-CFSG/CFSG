module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.Max1RelativeRigidity.PairOrbit
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.KernelOrbits

/-!
# No normal subgroup of order four in the literal J₄ max1 subgroup

A normal subgroup of order four lies in the certified elementary two-core.
The two checked nonidentity kernel orbits give the obstruction: the seed
normally generates all 2048 kernel elements, while the pair orbit has 1771
members. Neither can lie in a subgroup of order four.

This uses the actual ATLAS max1 subgroup and its existing coordinate and
conjugation certificates. No ambient order, simplicity, automorphism rigidity,
or exhaustive local-subgroup classification is needed.

Source: GLS3, Table 5.3i, and the sporadic inspection in Aschbacher–Smith,
15.3.43, printed p.1140. The literal ATLAS program and its attribution are
preserved in `Cardinality.Subgroup` and the imported certificate modules.
-/

public section

open Subgroup Janko4 Janko4.Cardinality
namespace Janko4.LocalStructure

attribute [local irreducible] modelGroup matrixA matrixB localKernel max1Subgroup

/-- The concrete Mathieu local subgroup has no normal subgroup of order four. -/
theorem max1_normal_card_ne_four (V : Subgroup (max1Subgroup matrixA_mul_self matrixB_pow_four)) [V.Normal]
    : Nat.card V ≠ 4 := by
  intro hV
  have hp : IsPGroup 2 V := IsPGroup.of_card (n := 2) hV
  have hVK : V ≤ localKernel matrixA_mul_self matrixB_pow_four := by
    rw [LocalStructure.localKernel_eq_twoCore]
    exact le_sSup ⟨inferInstance, hp⟩
  have hne : V ≠ ⊥ := by
    intro he
    rw [he, card_bot] at hV
    omega
  obtain ⟨z, hz⟩ := ne_bot_iff_exists_ne_one.mp hne
  have hz' : (z : max1Subgroup matrixA_mul_self matrixB_pow_four) ≠ 1 := by
    exact fun he => hz (Subtype.ext he)
  obtain ⟨g, hg | hg⟩ := Simplicity.Max1Fusion.kernel_nonidentity_orbits
    matrixA_mul_self matrixB_pow_four z (hVK z.property) hz'
  · have hs : localKernelSeed matrixA_mul_self matrixB_pow_four ∈ V := by
      rw [hg]
      exact Normal.conj_mem inferInstance (z : max1Subgroup matrixA_mul_self matrixB_pow_four) z.property g
    have hKV : localKernel matrixA_mul_self matrixB_pow_four ≤ V := by
      unfold localKernel
      exact normalClosure_le_normal (Set.singleton_subset_iff.mpr hs)
    have hc := Subgroup.card_le_of_le hKV
    rw [localKernel_card, hV] at hc
    omega
  · have hs : Max1RelativeRigidity.v ∈ V := by
      rw [show Max1RelativeRigidity.v = g * z * g⁻¹ from hg]
      exact Normal.conj_mem inferInstance (z : max1Subgroup matrixA_mul_self matrixB_pow_four) z.property g
    have hsub : MulAction.orbit (ConjAct Max1RelativeRigidity.M)
        Max1RelativeRigidity.v ⊆ (V : Set Max1RelativeRigidity.M) := by
      rintro w ⟨a, rfl⟩
      exact Normal.conj_mem inferInstance _ hs a.ofConjAct
    have hc := Nat.card_le_card_of_injective _ (Set.inclusion_injective hsub)
    change Nat.card (MulAction.orbit (ConjAct Max1RelativeRigidity.M)
      Max1RelativeRigidity.v) ≤ Nat.card V at hc
    rw [Max1RelativeRigidity.pair_orbit_card, hV] at hc
    omega

end Janko4.LocalStructure
