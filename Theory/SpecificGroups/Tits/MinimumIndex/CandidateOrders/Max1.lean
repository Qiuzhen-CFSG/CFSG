module

public import Theory.SpecificGroups.Tits.MinimumIndex.Candidates
public import Theory.SpecificGroups.Tits.Atlas1600Primitive
public import Theory.SpecificGroups.Tits.Atlas1600Order

/-!
# The first candidate lies in a degree-1600 point stabilizer

The literal final registers of primary ATLAS max1 both fix source point 1416
(Lean point 1415). Orbit–stabilizer and the certified ambient order give the
bound 17971200 / 1600 = 11232. No maximal-subgroup catalogue is used.
Source: the unmodified program `MinimumIndex/source/TF42G1-max1W1`.
-/

namespace Tits.MinimumIndexCandidates

/-- The literal max1 fixes a point of the transitive degree-1600 action. -/
public theorem max1_card_le : Nat.card max1 ≤ 11232 := by
  let K := MulAction.stabilizer Atlas1600Group (1415 : Fin 1600)
  have hle : max1 ≤ K := by
    apply (Subgroup.closure_le K).mpr
    intro g hg
    rcases hg with rfl | hg
    · change max1Generators.1.val 1415 = 1415
      decide +kernel
    · have hg' : g = max1Generators.2 := hg
      subst g
      change max1Generators.2.val 1415 = 1415
      decide +kernel
  have hi : K.index = 1600 := by
    simpa only [Nat.card_fin] using
      (MulAction.index_stabilizer_of_transitive Atlas1600Group (1415 : Fin 1600))
  have hc := K.card_mul_index
  rw [hi, atlas1600Group_card] at hc
  have hk : Nat.card K = 11232 := by omega
  exact hk ▸ Subgroup.card_le_of_le hle

end Tits.MinimumIndexCandidates
