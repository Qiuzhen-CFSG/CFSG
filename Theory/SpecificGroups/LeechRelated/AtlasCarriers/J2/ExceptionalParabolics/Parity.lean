module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.Automorphisms
public import Mathlib.GroupTheory.Perm.Sign

/-!
# The explicit outer involution of the degree-100 Hall--Janko carrier

The two published generators are even and the constructed normalizing
involution is odd. Faithfulness of the normalizer action then proves that
its induced automorphism is outer. These assertions concern the exact
ATLAS permutation carrier; no comparison with the icosian model is used.

Source: the retained ATLAS `J2G1-p100B0` permutations, and the involution
constructed in `Automorphisms`. Every finite equality is kernel checked.
-/

@[expose] public section

namespace Sporadic.LeechRelated.J2.ExceptionalParabolics
open GeneratorPair
set_option maxRecDepth 20000
set_option maxHeartbeats 800000

theorem generatorA_sign : Equiv.Perm.sign generatorA = 1 := by
  rw [generatorA_eq_table]
  decide +kernel

theorem generatorB_sign : Equiv.Perm.sign generatorB = 1 := by
  rw [generatorB_eq_table]
  decide +kernel

theorem involution_sign : Equiv.Perm.sign involution = -1 := by
  decide +kernel
/-- Every element of the original carrier is an even permutation. -/
theorem generated_le_sign_ker : generated ≤ Equiv.Perm.sign.ker := by
  apply (Subgroup.closure_le _).mpr
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · exact generatorA_sign
  · rw [Set.mem_singleton_iff] at hx
    subst x
    exact generatorB_sign

/-- The extra permutation lies outside the original generated subgroup. -/
theorem involution_not_mem_generated : involution ∉ generated := by
  intro h
  have hs : Equiv.Perm.sign involution = 1 := generated_le_sign_ker h
  rw [involution_sign] at hs
  exact (by decide : (-1 : ℤˣ) ≠ 1) hs

/-- The constructed involution induces an outer, not merely a nonidentity,
automorphism of the actual carrier. -/
theorem involutionAut_not_inner :
    involutionAut ∉ (MulAut.conj : Carrier →* MulAut Carrier).range := by
  rintro ⟨g, hg⟩
  have hx : intoExtension g = extensionInvolution := extensionAction_injective (by
    rw [extensionAction_inner, extensionAction_involution]
    exact hg)
  have hp : (g : Equiv.Perm (Fin 100)) = involution := congrArg Subtype.val hx
  exact involution_not_mem_generated (hp ▸ g.property)

end Sporadic.LeechRelated.J2.ExceptionalParabolics
