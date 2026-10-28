module

public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.SourcePrime
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Supercritical.Offenders.Selection
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Factors.Decomposition.OffenderReduction

/-!
# The actual D.2.13 inputs in the original 13.8 source argument

The assembled prime theorem supplies both universal contracts on their
literal faithful binary actions. In particular, the five-prime contract
retains the original actor, odd core, moved space and fixed complement.
Neither prime restriction nor the full five-prime geometry remains an
earlier-source premise of these Chapter 13 applications.

Source: Aschbacher--Smith, D.2.13(1)--(2), printed pp.184--185;
13.8.8(2) and 13.8.13, printed pp.949--951.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion
universe u v

theorem Three.Supercritical.Offenders.d213PrimeRestriction_source :
    Three.Supercritical.Offenders.D213PrimeRestriction.{u,v} := by
  intro K _ _ W _ _ _ ρ hf _ A hA p hp ho hm
  let : Fact p.Prime := ⟨hp⟩
  exact (ChapterD.source_lemma_D_2_13_one_two ρ hf hA ho hm).1

theorem Five.sourceD213PrimeInput_source : Five.SourceD213PrimeInput.{u} := by
  intro K W _ _ _ _ _ ρ hf _ p _ ho A hA hm
  exact ChapterD.source_lemma_D_2_13_one_two ρ hf hA ho hm

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion
