module

public import Theory.SpecificGroups.ReeF4.SubfieldTitsEmbedding
public import Theory.SpecificGroups.Tits.TwoRankLower
public import Theory.GroupTheory.QuasithinBasic

/-!
# Elementary eights in all Ree F₄ models

The proved embedding of the actual Tits group into each Ree fixed group
transports its explicit elementary eight. This includes the full group at
parameter zero, separately from the simple Tits endpoint.
Source: Aschbacher–Smith A.2.12, printed p.36; the subfield construction cited
in `SubfieldTitsEmbedding`.
-/

public section
namespace ReeF4
open Theory.GroupTheory

/-- Every actual Ree F₄ fixed-group carrier has two-rank at least three. -/
theorem three_le_twoRank (m : ℕ) : 3 ≤ primeRank 2 (Model m) := by
  obtain ⟨j, hj⟩ := Subfield.exists_tits_embedding m
  exact Tits.TwoRank.three_le.trans (primeRank_le_of_injective 2 j hj)

end ReeF4
