module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.ForceNormalizer.Candidates.Certificates
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.ForceNormalizer.Candidates.Obstructions.Entry02
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.ForceNormalizer.Candidates.Obstructions.Entry04
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.ForceNormalizer.Candidates.Obstructions.Entry06
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.ForceNormalizer.Candidates.Obstructions.Entry07
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.ForceNormalizer.Candidates.Obstructions.Entry09
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.ForceNormalizer.Candidates.Obstructions.Entry10
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.ForceNormalizer.Candidates.Obstructions.Entry13
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.ForceNormalizer.Candidates.Obstructions.Entry14
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.ForceNormalizer.Candidates.Obstructions.Entry16
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.ForceNormalizer.Candidates.Obstructions.Entry19
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.ForceNormalizer.Candidates.Obstructions.Entry20
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.ForceNormalizer.Candidates.Obstructions.Entry23
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.ForceNormalizer.Candidates.Obstructions.Entry27
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.ForceNormalizer.Candidates.Obstructions.Entry33
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.ForceNormalizer.Candidates.Obstructions.Entry34
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.ForceNormalizer.Candidates.Obstructions.Entry35
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.ForceNormalizer.Candidates.Obstructions.Entry36
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.ForceNormalizer.Candidates.Obstructions.Entry42
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.ForceNormalizer.Candidates.Obstructions.Entry43

/-!
# Two-core normalizer obstructions for the second Held candidates

Each of the nineteen fixed obstruction entries has a certified outside Sylow
normalizer element. Fourteen act trivially on the Frattini quotient; entry 13
acts trivially on the involution/square characteristic series; the other four
act trivially on the center/square characteristic series. Each action therefore
lies in the two-core of the full automorphism group of the actual subgroup.

This completes the obstruction input for the intermediate finite calculation
in the proposed proof of Huppert--Blackburn III, XII.1.18(b), printed p.314.
It is independent of the coverage and characteristic-intersection checks.
-/

namespace Theory.GroupTheory.HeldM22A10.SecondExclusion.ForceNormalizer.Candidates

/-- All nineteen fixed representatives have outside normalizer two-core witnesses. -/
public theorem obstructionChecks : ObstructionChecks := by
  intro j
  fin_cases j
  · exact Obstructions.representative2_hasPCoreNormalizerWitness
  · exact Obstructions.representative4_hasPCoreNormalizerWitness
  · exact Obstructions.representative6_hasPCoreNormalizerWitness
  · exact Obstructions.representative7_hasPCoreNormalizerWitness
  · exact Obstructions.representative9_hasPCoreNormalizerWitness
  · exact Obstructions.representative10_hasPCoreNormalizerWitness
  · exact Obstructions.representative13_hasPCoreNormalizerWitness
  · exact Obstructions.representative14_hasPCoreNormalizerWitness
  · exact Obstructions.representative16_hasPCoreNormalizerWitness
  · exact Obstructions.representative19_hasPCoreNormalizerWitness
  · exact Obstructions.representative20_hasPCoreNormalizerWitness
  · exact Obstructions.representative23_hasPCoreNormalizerWitness
  · exact Obstructions.representative27_hasPCoreNormalizerWitness
  · exact Obstructions.representative33_hasPCoreNormalizerWitness
  · exact Obstructions.representative34_hasPCoreNormalizerWitness
  · exact Obstructions.representative35_hasPCoreNormalizerWitness
  · exact Obstructions.representative36_hasPCoreNormalizerWitness
  · exact Obstructions.representative42_hasPCoreNormalizerWitness
  · exact Obstructions.representative43_hasPCoreNormalizerWitness

end Theory.GroupTheory.HeldM22A10.SecondExclusion.ForceNormalizer.Candidates
