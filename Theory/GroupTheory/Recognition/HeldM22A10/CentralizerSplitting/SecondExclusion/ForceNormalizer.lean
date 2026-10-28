module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.Enumeration
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.Structure
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.Context
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.ForceNormalizer.Ambient
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.ForceNormalizer.Candidates
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.ForceNormalizer.Transport

/-!
# Conditional exclusion of the second nonsplit Held centralizer

The fixed generated subgroups are certified: the Sylow has order 128,
the transfer kernel is normal in the entire model and has order 64, and the
exceptional subgroup is normal of index two in the Sylow. The actual embedding
gives an ambient Sylow and its binary kernel without a conjugacy choice.

The proved concrete candidate assertion and its transport give characteristic
kernel intersections for every centric intrinsic-radical subgroup except the
fixed exceptional subgroup. If its ambient normalizer lies in the involution
centralizer, local normality handles this last case. Character fusion and
transfer then contradict simplicity.

`ForceNormalizer.false_of_normalizer_le` discharges all candidate premises.
The exceptional-normalizer containment remains its explicit hypothesis; proving
that containment and assembling the unconditional exclusion are separate tasks.

Source problem: Huppert--Blackburn III, XII.1.18(b), p.314, citing Held,
J. Algebra 8 (1968), 436--449. This is the conditional transfer step toward
the source splitting theorem.
-/

namespace Theory.GroupTheory.HeldM22A10.SecondExclusion.ForceNormalizer

universe u

/-- In the second nonsplit model, containment of the actual exceptional
normalizer in the involution centralizer contradicts ambient simplicity.
The concrete subgroup assertion and its transport are both discharged. -/
public theorem false_of_normalizer_le
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    (D : LocalData G) (e : D.centralizer ≃* NonsplitModels.Second)
    (hN : Subgroup.normalizer (ambientExceptionalSubgroup D e : Set G) ≤ D.centralizer) :
    False :=
  false_of_ambient_candidates D e hN
    (ambient_candidates_of_candidates D e candidateProperty)

end Theory.GroupTheory.HeldM22A10.SecondExclusion.ForceNormalizer
