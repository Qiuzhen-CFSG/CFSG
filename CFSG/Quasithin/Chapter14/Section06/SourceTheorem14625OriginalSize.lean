module
public import CFSG.Quasithin.Chapter14.Section06.SourceTheorem14625EarlierFactors
public import CFSG.Quasithin.Chapter14.Section09.ShortRoute.MixedSize

/-!
# Original 14.6.25 with the mixed-size source theorem supplied

The original mixed A₅/S₃ pair satisfies the checked DGS order bound. Apply
that theorem inside the fixed-M consumer, preserving its actual subgroups
and quotient markings. The numerical MixedSizeInput is no longer a premise.
The independent whole-core A₆ reconstruction, terminal solvability and
original exchanged-factor family remain explicit.

Source: Aschbacher--Smith F.1.12(I) and 14.6.25, printed pp.262--264,1042.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 Chapter12.Section08
open Chapter14.Section03.NonabelianSource.SourceAbelianReduction
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The genuine mixed-size theorem discharges the numerical input of the
original fixed-M classification. No recognition or profile input is added. -/
theorem source_theorem_14_6_25_of_original_size
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hrank : RankTwoHypothesis KnownSimple.IsKnownSimple T (sourceResidual M Mc) M)
    (ha : AlternatingSixReconstructionInput.{u} KnownSimple.IsKnownSimple)
    (hterminal : ¬ ClassificationModels.IsTheoremEModel G →
      ∀ (F : InvariantFlag T (rankTwoSeed T M) 2), ¬ IsMulCommutative F.U →
      ∀ g ∈ F.P (sourceResidual M Mc), g ∉ F.H →
        Group.IsSolvable F.TerminalHdot)
    (h12 : ¬ ClassificationModels.IsTheoremEModel G →
      IsMulCommutative (conjugateSpanBy (localModule T M) Mc) → SourceExchangedFactorFamily T M) :
    ClassificationModels.IsTheoremEModel G := by
  apply source_theorem_14_6_25_of_earlier_factors
    hG T hempty hM hu hmany hrank ha hterminal h12
  intro K U S h _ _ hK hU _
  exact ChapterF.Source.DGS85.ShortRoute.mixed_original_sylow_card_le h hK.some hU.some

end CFSG.Quasithin.Chapter14.Section06
