module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Local
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.Geometry
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear.Three
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear.Four
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear.Five

/-!
# Index-three Sylow overgroups in the binary linear components

In degrees three, four, and five, construct a basis flag for the actual Sylow
overgroup. The prime-index formula and adjacent basis swaps force precisely
one proper dimension to be omitted. The resulting flag stabilizer is the
original ambient subgroup, and the witness retains the supplied projective
model equivalence. No flag position or BN-pair assertion is an input.

This proves the conditional linear geometric step of Aschbacher–Smith
15.3.49(l), combined manuscript (1 March 2004), printed pp.1143–1145.
The local subgroup and component hypotheses are supplied by the parent
assembly through `ParabolicIdentification.Local`.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear
open Chapter2.ComponentRefinement.LieType.Binary Chapter1

/-- Every index-three overgroup of a Sylow two-subgroup in the prescribed
binary component is the actual stabilizer of a flag with one node omitted. -/
theorem exists_position {K : Type*} [Group K] [Finite K]
    (L S P : Subgroup K) (n : ℕ) [NeZero n] (hn : 3 ≤ n) (hn' : n ≤ 5)
    (e : L ≃* PSL n) (hs : IsSylowIn 2 S L) (hSP : S ≤ P) (hPL : P ≤ L)
    (hi : S.relIndex P = 3) :
    ∃ pos : ModelExclusions.BinaryGeometry.Position L P n, pos.model = e := by
  have hcases : n = 3 ∨ n = 4 ∨ n = 5 := by omega
  rcases hcases with rfl | rfl | rfl
  · exact Three.exists_position L S P e hs hSP hPL hi
  · exact Four.exists_position L S P e hs hSP hPL hi
  · exact Five.exists_position L S P e hs hSP hPL hi

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear
