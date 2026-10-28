module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Catalogue.SevenKernel.Inputs
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Catalogue.SevenKernel.Quotient
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Catalogue.SevenKernel.Preparation
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Catalogue.SevenKernel.Selection
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Catalogue.SevenKernel.Natural.Source
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Catalogue.SevenKernel.Exceptional.Source

/-!
# Original A₇ kernel recovery from the two relative selection branches

The original C.2.7 configuration supplies the full moved-module classification
and the MS conditions on the same component-radical product. Once either
relative selection branch constructs a block, its core commutator lies in the
star module and has exactly the two-core as centralizer. This kills the entire
comparison kernel, including its possible cubic part.

Both relative selection branches are proved under the original hypotheses.
The final recovery theorem therefore has no extra block or kernel premise.

Source: Aschbacher--Smith C.2.7(3)(a),(b),(d), pp.145--147, and original
14.6.10(5), p.1029.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.ParabolicCatalogue.SevenKernel
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))

/-- The original recovery contract follows once both source selection branches
are proved. Final assembly must discharge these two premises. -/
theorem sevenRecoveryInput_of_selections
    (hnatural : NaturalSelectionInput hG T hempty hM hunique hmany hcard e hab)
    (hexceptional : ExceptionalSelectionInput hG T hempty hM hunique hmany hcard e hab) :
    SevenRecoveryInput hG T hempty hM hunique hmany hcard e hab := by
  intro H hH d I hI he
  obtain ⟨eC⟩ := he
  obtain ⟨m⟩ := generated_actionData hG T hempty hM hunique hmany hcard e hab H hH d I hI eC
  have hb : ChapterC.IsBlock ((sourceGeneratedComponent T M Mc I d.H2).subgroupOf
      (sourceGeneratedComponent T M Mc I d.H2 ⊔ firstCore T M Mc I d.H2)) := by
    apply block_of_selection
      (prepared hG T hempty hM hunique hmany hcard e hab H hH d I hI).1
    rcases m.models with hn | hx
    · exact hnatural H hH d I hI eC m hn
    · exact hexceptional H hH d I hI eC m hx
  exact ⟨quotientEquiv_of_block
    (prepared hG T hempty hM hunique hmany hcard e hab H hH d I hI).1 eC hb⟩

/-- Recover the full A₇ quotient of every original generated component.
Both relative selection branches and the possible cubic kernel are discharged. -/
theorem sevenRecoveryInput :
    SevenRecoveryInput hG T hempty hM hunique hmany hcard e hab :=
  sevenRecoveryInput_of_selections hG T hempty hM hunique hmany hcard e hab
    (Natural.naturalSelectionInput hG T hempty hM hunique hmany hcard e hab)
    (Exceptional.exceptionalSelectionInput hG T hempty hM hunique hmany hcard e hab)

end CFSG.Quasithin.Chapter14.Section06.ParabolicCatalogue.SevenKernel
