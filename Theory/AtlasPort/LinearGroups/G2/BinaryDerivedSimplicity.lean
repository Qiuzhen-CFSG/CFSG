module

public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.DerivedGroup
public import Theory.GroupAction.IwasawaNormalClosure
public import Theory.GroupTheory.ChiefFactorDirectPower.SimpleOrder

/-!
# Simplicity of the actual derived octonion group G₂(2)′

The long-root commutator [B(1), E(1)] = A(1) lies in the derived subgroup
of the long-root normal closure H. Normal generation then proves H perfect.
The faithful primitive singular-point action and its abelian long-root local
subgroup imply that H is minimal normal in G₂(2). Hence H is a positive
direct power of a simple group. Its already proved order 6048 is divisible
by 7 but not 49, forcing this power to have one factor.

Finally, the existing equality of H with the actual commutator subgroup
gives the requested simplicity theorem. No comparison with a unitary model
is used. Root coordinates, the primitive action and the order calculation
come from the licensed ATLAS port cited in the imported G₂ modules;
the normal-subgroup and direct-power arguments are cited in their imports.
-/

public section

namespace Atlas.G2.BinaryException
open Atlas.G2.Explicit BinaryCore
open scoped commutatorElement

/-- The binary long-root normal closure is perfect, including the exceptional
field where the full octonion automorphism group is not perfect. -/
theorem H_isPerfect : Group.IsPerfect H := by
  apply Subgroup.isPerfect_iff.mpr
  apply le_antisymm (Subgroup.commutator_le_left H H)
  apply Subgroup.normalClosure_le_normal
  have hA : rootA (1 : ZMod 2) ∈ ⁅H, H⁆ := by
    have he : ⁅(⟨0, 1, 0, 0, 0⟩ : Coordinates), (⟨0, 0, 0, 0, 1⟩ : Coordinates)⁆ =
        involution := by decide +kernel
    rw [← embedding_involution, ← he, map_commutatorElement]
    apply Subgroup.commutator_mem_commutator
    · simpa [embedding, parameters, unipotentProduct] using rootB_in_H 1
    · simpa [embedding, parameters, unipotentProduct] using rootE_in_H 1
  have hAall (a : ZMod 2) : rootA a ∈ ⁅H, H⁆ := by
    have hb : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide +kernel
    rcases hb a with rfl | rfl
    · rw [rootA_zero]; exact Subgroup.one_mem _
    · exact hA
  rintro _ ⟨⟨a, b⟩, rfl⟩
  change rootA a * rootB b ∈ ⁅H, H⁆
  apply Subgroup.mul_mem _ (hAall a)
  rw [← weylR_rootA]
  exact (inferInstance : (⁅H, H⁆ : Subgroup (Model (ZMod 2))).Normal).conj_mem _ (hAall b) _

/-- Every nontrivial normal subgroup of the full binary group contains H. -/
theorem H_le_normal (N : Subgroup (Model (ZMod 2))) [N.Normal] (hne : N ≠ ⊥) :
    H ≤ N := by
  let := singularPoints_primitive (K := ZMod 2)
  let : Group.IsPerfect (Subgroup.normalClosure
      (longRootLocal (F := ZMod 2) : Set (Model (ZMod 2)))) := H_isPerfect
  exact MulAction.perfect_normalClosure_le_normal firstPoint longRootLocal
    longRootLocal_le_pointStabilizer longRootLocal_normal_in_pointStabilizer N hne

/-- The long-root normal closure in the binary octonion group is simple. -/
theorem H_isSimple : IsSimpleGroup H := by
  let : Nontrivial H := H.nontrivial_iff_ne_bot.mpr H_ne_bot
  apply CharacteristicallySimple.isSimpleGroup_of_prime_dvd_card_of_sq_not_dvd
    (p := 7)
  · apply ChiefFactor.characteristic_eq_bot_or_top_of_minimal_normal
    intro N hN hNH
    by_cases hne : N = ⊥
    · exact Or.inl hne
    · exact Or.inr (le_antisymm hNH (H_le_normal N hne))
  · decide
  · rw [card_H]; decide
  · rw [card_H]; decide

end Atlas.G2.BinaryException

namespace Atlas.G2

/-- The actual commutator subgroup of the split-octonion automorphism group
over the two-element field is simple. -/
theorem isSimple_commutator_binary : IsSimpleGroup (commutator (Model (ZMod 2))) := by
  rw [BinaryParabolicPair.commutator_eq_longRootClosure]
  exact BinaryException.H_isSimple

end Atlas.G2
