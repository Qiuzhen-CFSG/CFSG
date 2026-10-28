module

public import CFSG.Quasithin.Chapter15.SourceAssembly.OriginalSylowSource
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.Exhaustion.Source
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.Reconstruction
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.A6Irreducibility

/-!
# Theorem E with the original Sylow A₆ branches assembled

The quotient-center split reduces A₆ reconstruction to the natural core and
the exceptional cubic cover.  The natural exhaustion consumer retains only
the MS93 distance-four input; the exceptional reconstruction is proved for the
actual Sylow radical.  Their whole-core conclusions supply the original
rank-one source consumer in Theorem E.

The literal 15.1.3 and 15.3.13 hypotheses remain explicit.  No universal
`EarlierMSClassifications` or C.1.34 premise is used, and no nonsylow cubic
exhaustion premise is required.

Source: Aschbacher--Smith 15.3.25--32 and Theorem E, pp.1130--1134,1165;
C.1.31--32, pp.135--136; MS93 (5.12) and Section 7, pp.924--927,932--933.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15
open Section03 ChapterA.Section05To06
open CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The full original-Sylow A₆ reconstruction, after the natural distance-four
source input. The exceptional branch uses its checked Sylow reconstruction. -/
theorem original_sylow_A6_reconstruction_of_distanceFour
    (hfour : AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFourInput.{u}
      KnownSimple.IsKnownSimple)
    {L R : Subgroup G} (h : SmallMSPair KnownSimple.IsKnownSimple L R)
    (hSyl : Chapter1.IsSylowIn 2 R (L ⊔ R))
    (e : (L ⧸ centralPreimage (pCore 2 L)) ≃*
      commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))) :
    AlternatingSixReconstruction L := by
  rcases h.alternating_center_cases e with hz | hz
  · obtain ⟨he, hc, hm⟩ :=
      AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.naturalCore_of_distanceFour_knownSimple
        hfour G L R h e hz
    exact ⟨he, hc, hm.alternating_six_irreducible, Or.inl hm⟩
  · exact AlternatingSixReconstruction.Exceptional.OriginalSylow.reconstruction h e hz hSyl

/-- Theorem E now consumes only natural distance four and the two original
Section 15 source implications. The original Sylow exceptional A₆ branch and
the binary and G₂ rank-one rows are discharged by existing source theorems. -/
theorem source_theoremE_of_original_sylow_distanceFour
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (h1513 : ∀ Mc : Subgroup G,
      maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc} →
      ClassificationModels.IsTheoremEModel G ∨
        ∃ M : Subgroup G, IsOrderingMaximal T M ∧
          Nonempty (NaturalOrthogonalAction M (localModule T M)))
    (hfour : AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFourInput.{u}
      KnownSimple.IsKnownSimple)
    (h13 : ∀ d : CharacteristicTwo.LocalData G, d.T = T →
      IsOrderingMaximal d.T d.M →
      maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc} →
      ∀ Yplus : Subgroup G, Hypothesis15310 d.M d.Y d.S d.V₁ Yplus →
      primeRank 3 Yplus = 2 →
      ∀ I ∈ outsideFamily Yplus d.S d.M, generalizedFitting I ≠ pCore 2 I) :
    ClassificationModels.IsTheoremEModel G :=
  source_theoremE_of_original_sylow_A6_reconstruction hG T hmany hempty h1513
    (fun _ _ h hSyl e => original_sylow_A6_reconstruction_of_distanceFour hfour h hSyl e) h13

end CFSG.Quasithin.Chapter15
