module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.FirstExclusion.Criterion
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.FirstExclusion.ModelCharacter
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.FirstExclusion.FiniteModel

/-!
# Exclusion of the first nonsplit Held centralizer

The actual involution centralizer in a finite simple group satisfying
`LocalData` cannot be isomorphic to `NonsplitModels.First`. Its binary character,
fourth root and intrinsic centralizer facts are proved from the published
permutation generators and the certified enumeration in `FiniteModel`.
Order-four transfer and the two-group normalizer condition then give the
ambient contradiction through `Criterion`.

The unconditional theorem discharges every finite-model premise of the
retained conditional interface. It uses the original local hypotheses, with
no splitting or recognition assumption.

Source: Huppert--Blackburn III, XII.1.18(b), p.314, citing Held,
J. Algebra 8 (1968), 436--449, DOI 10.1016/0021-8693(68)90054-9.
-/

namespace Theory.GroupTheory.HeldM22A10.LocalData

/-- The first exclusion, conditional on its remaining intrinsic finite checks.
The assembly owner must supply `h` before asserting the source exclusion. -/
public theorem not_nonempty_equiv_first_of_modelFacts
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] (D : LocalData G)
    (h : FirstExclusion.ModelFacts) : ¬ Nonempty (D.centralizer ≃* NonsplitModels.First) := by
  rintro ⟨e⟩
  exact FirstExclusion.false_of_equiv_pattern D (FirstExclusion.pattern_of_modelFacts h) e

/-- The first nonsplit permutation model cannot be the actual involution
centralizer under the original finite simple ambient-group hypotheses. -/
public theorem not_nonempty_equiv_first
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] (D : LocalData G) :
    ¬ Nonempty (D.centralizer ≃* NonsplitModels.First) :=
  D.not_nonempty_equiv_first_of_modelFacts FirstExclusion.modelFacts

end Theory.GroupTheory.HeldM22A10.LocalData
