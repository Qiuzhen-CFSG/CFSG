module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.KnownSimple.UniformPair
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.SolvableSource.DirectRows

/-!+# The original many-overgroup source argument with its component bound proved

The large-center branch uses the actual intrinsic embedding and component
normal-or-index-two theorems. The small-center branch constructs the single
universal characteristic pair and applies the proved wreath exclusion.
Full known-simple A/B/C, solvable D.1 and E.2.9, Thompson factorization and
adequate B.5 are all instantiated on their original subgroup actions.

The remaining parameters are the genuine earlier common-normal, residual,
Goldschmidt and corrected F.6 source implications. The complete exchanged
component sieve is proved on the original local module, removing both
C.2.7 and C.1.34 parameters from this source route. This is the many-overgroup
branch; the independent Section 15.3 branch is not assumed or asserted here.
Source: Aschbacher--Smith 15.4.2--25.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.InitialSource.KnownSimpleSource
open FamilySource FamilySource.ModuleStructure ChapterA.Section05To06
open LocalSetup.SourceWitnesses LocalSetup.EmbeddingReduction
open LocalSetup.TwoFactors LocalSetup.TwoFactors.MixedLocal
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
universe u
variable {G : Type u} [Group G] [Finite G]

theorem source_many_theoremE_from_direct_rows
    (h311 : RatioSource.Earlier311 (G := G))
    (classification : SingleOvergroup.GoldschmidtClassification.{u})
    (residual : TwoOrbitResidualTheorem.{u} KnownSimple.IsKnownSimple)
    (sourceF : FSource.SourceClassificationInput.{u} KnownSimple.IsKnownSimple)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hmany : 1 < (maximalTwoLocalOvergroups
      (centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))).ncard) :
    ClassificationModels.IsTheoremEModel G := by
  have hnonzero := Subgroup.one_lt_card_iff_ne_bot
    (omegaOneCenterAmbient (T : Subgroup G)) |>.mpr (centralOmega_ne_bot hG T)
  by_cases hlarge : 2 < Nat.card (omegaOneCenterAmbient (T : Subgroup G))
  · exact (SolvableSource.source_large_center_contradiction_directRows
      (fun H _ _ => ChapterA.Section02.theoremsABC_knownSimple (G := H))
      h311 RatioSource.OutsideWitness.source_earlierE29Solvable
      Chapter1.RadicalNormalizers.ThompsonSource.source_theoremB216
      classification residual
      FFBranch.ClassificationComparison.FFAlternatives.SourceB5.classification sourceF
      hG T hempty hmany hlarge).elim
  · exact source_small_center_theoremE_from_uniform_sources h311 hG T hempty hmany
      (by omega)

end CFSG.Quasithin.Chapter15.Section04.InitialSource.KnownSimpleSource
