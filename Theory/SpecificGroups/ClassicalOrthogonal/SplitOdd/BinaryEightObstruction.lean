module

public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.BinaryEightObstruction.Rank
public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.BinaryEightObstruction.Simplicity

/-!
# The binary split-eight simple-section obstruction

The actual elementary orthogonal carrier modulo scalars is nonabelian simple
and contains the rank-three subgroup constructed in `BinaryEightObstruction.Rank`.
Simplicity follows from the faithful primitive action on nonzero singular
vectors, perfectness and the normal abelian root subgroup in a point stabilizer.
The subgroup of order 27 is built from actual Siegel words and remains injective
under the literal scalar quotient map. No recognition, simplicity or rank
premise is required.

These intrinsic facts concern the Ω₈⁺(2) section in GLS3 Table 5.3l
(`refs/KGroup/GLS3/Chapter5(sec3-).tex`). Its 3-rank contradicts the bound
for semisimple sections of proper two-local subgroups in Aschbacher–Smith
A.2.15(2), used in A.2.19 (`refs/quasithin.pdf`, printed pp. 37–41).
The Chapter A consumer supplies the actual sporadic section and the source
minimal-counterexample hypotheses.
-/

public section
namespace ClassicalOrthogonal.BinaryEightObstruction

/-- The intrinsic odd-prime rank obstruction for the exact split projective model. -/
theorem primeRank_three_gt_two : 2 < primeRank 3 (POmegaPlus 4 (ZMod 2)) :=
  lt_of_lt_of_le (by decide) primeRank_three_ge

/-- All intrinsic facts needed for the split-eight simple-section obstruction. -/
theorem simple_nonabelian_rank_obstruction :
    IsSimpleGroup (POmegaPlus 4 (ZMod 2)) ∧
      ¬ IsMulCommutative (POmegaPlus 4 (ZMod 2)) ∧
        2 < primeRank 3 (POmegaPlus 4 (ZMod 2)) :=
  ⟨isSimpleGroup, not_isMulCommutative, primeRank_three_gt_two⟩

end ClassicalOrthogonal.BinaryEightObstruction
