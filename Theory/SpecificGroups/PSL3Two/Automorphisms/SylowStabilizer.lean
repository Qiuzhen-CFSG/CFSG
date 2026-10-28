module

public import Theory.GroupTheory.SylowAutomorphismPGroup
public import Theory.SpecificGroups.PSL3Two.BorelCenterNormalizer
public import Theory.SpecificGroups.PSL3Two.Automorphisms.OuterOrder

/-!
# Sylow stabilizers in Aut(SL₃(2))

Sylow conjugacy transports the checked self-normalizing Borel to every
Sylow two-subgroup. The inner stabilizer is that two-group, and the outer
automorphism group has order two. Hence the full automorphism stabilizer
is a two-group. This is the model input for the PSL₃(2) branch of
Aschbacher–Smith 13.7.4(1), printed p.937.
-/

public section
open Subgroup
open scoped Pointwise

namespace Matrix.PSL3Two
private noncomputable def chosenBorelSylow : Sylow 2 SL := Sylow.ofCard borelSL (by
  rw [card_borelSL, card_SL]
  decide +kernel)

/-- Every Sylow two-subgroup of SL₃(2) is self-normalizing. -/
theorem self_normalizing_sylow (S : Sylow 2 SL) :
    normalizer (S : Set SL) = (S : Subgroup SL) := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq SL chosenBorelSylow S
  have he : borelSL.map (MulAut.conj g).toMonoidHom = (S : Subgroup SL) := by
    exact congrArg Sylow.toSubgroup hg
  change normalizer ((S : Subgroup SL) : Set SL) = _
  rw [← he, ← map_equiv_normalizer_eq, BorelCenterNormalizer.normalizer_borel]

/-- The stabilizer of a Sylow two-subgroup in Aut(SL₃(2)) is a two-group. -/
theorem automorphism_sylow_stabilizer_two (S : Sylow 2 SL) :
    IsPGroup 2 (MulAction.stabilizer (MulAut SL) (S : Subgroup SL)) :=
  MulAut.isPGroup_sylow_stabilizer_of_self_normalizing S (self_normalizing_sylow S) Automorphisms.outer_sl_isTwoGroup
end Matrix.PSL3Two
