module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.ThompsonNoncentral
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Family.SourceConstruction.ThompsonFactors.SourceInput

/-!
# Source-family existence from the original empty-family branch

The actual centralizer-overgroup hypothesis supplies the source preparation
and the noncentral Thompson action. Solvable Thompson factorization then
constructs a genuine Y-member inside every maximal local overgroup, together
with its literal elementary quotient and moved-module rank. This is the
existence part of source 15.4.12, including the full original module input.
The classification of all members and the later double-factor reduction
remain separate deductions.

Source: Aschbacher--Smith, 15.4.11--12, printed pp.1160--1161.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.InitialSource
open FamilySource ModuleStructure ChapterA.Section05To06
universe u
variable {G : Type u} [Group G] [Finite G]
variable
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
    (h311 : RatioSource.Earlier311 (G := G))
    (hD15 : RatioSource.InsideCore.EarlierD15.{u})
    (hD14 : RatioSource.InsideCore.EarlierD14Sylow.{u})
    (h29 : RatioSource.OutsideWitness.EarlierE29Solvable.{u})
    (hB : Chapter1.RadicalNormalizers.ThompsonSource.TheoremB216.{u})

include hA hC h311 hD15 hD14 h29 hB

/-- Construct every original source input for some member in each maximal
local, with the full known-simple class and empty faithful family unchanged. -/
theorem source_family_input_of_empty
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hmany : 1 < (maximalTwoLocalOvergroups
      (centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))).ncard) :
    ∀ M ∈ maximalLocals T, ∃ X : Subgroup G, ∃ s : ℕ,
      Input KnownSimple.IsKnownSimple T M X s := by
  obtain ⟨hc,hlocals,_⟩ := source_local_preparation hA hC h311 hD15 hD14 h29
    hG T hempty hmany
  have hmove := source_thompson_noncentral hA hC h311 hD15 hD14 h29 hB
    hG T hempty hmany
  intro M hM
  exact ThompsonFactors.source_input_of_noncentral hB hG T M hM.1 hM.2
    (hlocals M hM).1 hc (hmove M hM)

end CFSG.Quasithin.Chapter15.Section04.InitialSource
