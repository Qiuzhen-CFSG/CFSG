module

public import CFSG.Quasithin.ClassicalModels
public import Theory.SpecificGroups.SymplecticSix.Simplicity
public import Theory.SpecificGroups.SymplecticSix.BinaryThreeRank
public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.BinaryEightObstruction
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.BinarySixObstruction

/-!
# Intrinsic classical obstructions for the Leech centralizer sections

GLS3 Tables 5.3j, 5.3k, 5.3l and 5.3o identify Sp₆(2), Sp₆(2), Ω₈⁺(2)
and Ω₆⁻(2) sections of the Co₃, Co₂, Co₁ and Suz involution centralizers.
The theorems below prove that each exact projective carrier is nonabelian
simple and has 3-rank greater than two, without extra hypotheses.

The lower-layer constructions embed `(C₃)³` by independent plane rotations
or explicit Siegel words, proving membership in the defining groups and
injectivity under the literal scalar quotient maps. Simplicity follows from
faithful primitive actions and abelian root subgroups via Iwasawa's criterion.
For Ω₆⁻(2), elementary generation is proved for the full orthogonal group's
commutator subgroup; for Ω₈⁺(2), the carrier is the Siegel-generated group.

These facts supply the classical target assertions in the application of
Aschbacher–Smith A.2.15(2) to A.2.19 (`refs/quasithin.pdf`, printed pp. 37–41).
The sporadic quotient maps and the smaller-section induction belong to
`LeechCentralizerSections`. This module supplies their intrinsic classical
target assertions; the four sporadic exclusions require those separate maps
and the source minimal-counterexample hypotheses.
-/

namespace CFSG.Quasithin.ChapterA

/-- The exact split orthogonal section target for the Co₁ branch. -/
public theorem leechPOmega8PlusTwo_simple :
    IsSimpleGroup (ClassicalOrthogonal.POmegaPlus 4 (ZMod 2)) :=
  ClassicalOrthogonal.BinaryEightObstruction.isSimpleGroup

public theorem leechPOmega8PlusTwo_nonabelian :
    ¬ IsMulCommutative (ClassicalOrthogonal.POmegaPlus 4 (ZMod 2)) :=
  ClassicalOrthogonal.BinaryEightObstruction.not_isMulCommutative

/-- The split orthogonal section violates the bound in A.2.15(2). -/
public theorem leechPOmega8PlusTwo_primeRank_three_gt_two :
    2 < primeRank 3 (ClassicalOrthogonal.POmegaPlus 4 (ZMod 2)) :=
  ClassicalOrthogonal.BinaryEightObstruction.primeRank_three_gt_two

/-- The exact symplectic section target for the Co₂ and Co₃ branches. -/
public theorem leechPSp6Two_simple : IsSimpleGroup (ClassicalGroup.PSp 3 (ZMod 2)) :=
  Theory.SpecificGroups.SymplecticSix.isSimpleGroup_binary

public theorem leechPSp6Two_nonabelian : ¬ IsMulCommutative (ClassicalGroup.PSp 3 (ZMod 2)) :=
  Theory.SpecificGroups.SymplecticSix.not_isMulCommutative_binary

/-- The numerical obstruction contradicting the bound supplied by A.2.15(2). -/
public theorem leechPSp6Two_primeRank_three_gt_two :
    2 < primeRank 3 (ClassicalGroup.PSp 3 (ZMod 2)) :=
  lt_of_lt_of_le (by decide) Theory.SpecificGroups.SymplecticSix.BinaryThreeRank.primeRank_three_ge

/-- The exact minus orthogonal section target for the Suz branch. -/
public theorem leechPOmega6MinusTwo_simple :
    IsSimpleGroup (ClassicalGroup.POmegaMinus 3 (ZMod 2)) :=
  ClassicalOrthogonal.Minus.BinarySixObstruction.isSimpleGroup

public theorem leechPOmega6MinusTwo_nonabelian :
    ¬ IsMulCommutative (ClassicalGroup.POmegaMinus 3 (ZMod 2)) :=
  ClassicalOrthogonal.Minus.BinarySixObstruction.not_isMulCommutative

/-- The minus orthogonal section violates the bound in A.2.15(2). -/
public theorem leechPOmega6MinusTwo_primeRank_three_gt_two :
    2 < primeRank 3 (ClassicalGroup.POmegaMinus 3 (ZMod 2)) :=
  ClassicalOrthogonal.Minus.BinarySixObstruction.two_lt_primeRank_three

end CFSG.Quasithin.ChapterA
