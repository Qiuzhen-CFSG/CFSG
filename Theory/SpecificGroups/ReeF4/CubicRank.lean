module

public import Theory.SpecificGroups.ReeF4.SubfieldTitsEmbedding
public import Theory.SpecificGroups.ReeF4.Model.LocalBlock
public import Theory.SpecificGroups.Tits.ThreeRankLowerBound
public import Theory.SpecificGroups.Tits.FiniteSimple
public import Theory.GroupTheory.QuasithinBasic

/-!
# Three-rank of the actual Ree fixed groups

The concrete Tits three-subgroup gives rank at least two. Its proved
embedding into every Ree model transports this bound to every supplied
exceptional root endomorphism, using the actual fixed-group equivalence.
No order or simplicity certification for the Ree groups is needed.

Source: Aschbacher–Smith, proof of 13.6.6(ii), printed p.927;
the subfield construction and Parrott comparison cited in the imports.
-/

public section
namespace ReeF4.CubicRank
open Theory.GroupTheory

/-- Every concrete Ree model contains the rank-two Tits three-subgroup. -/
theorem model (m : ℕ) : 2 ≤ primeRank 3 (Model m) := by
  have hT : 2 ≤ primeRank 3 Tits.ParrottGroup := by
    rw [primeRank_equiv 3 Tits.parrottFiniteImageEquiv]
    exact Tits.ThreeRank.rank_two_le
  obtain ⟨j, hj⟩ := Subfield.exists_tits_embedding m
  exact hT.trans (primeRank_le_of_injective 3 j hj)

/-- The same rank bound holds for the fixed group of the supplied root construction. -/
theorem fixedGroup {m : ℕ} (d : LocalBlockInput m) :
    2 ≤ primeRank 3 d.fixedGroup := by
  rw [primeRank_equiv 3 d.modelEquiv]
  exact model m

end ReeF4.CubicRank
