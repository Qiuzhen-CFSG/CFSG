module

public import CFSG.Quasithin.Chapter15.SourceAssembly.BinaryRankOneSource
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.OriginalSylowA6
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.G2Reconstruction.Source

/-!
# Theorem E from alternating-six reconstruction at original Sylow pairs

Each original rank-one source has `I = c.L ⊔ d.S` and an actual Sylow
subgroup of `I` mapping to `d.S`. Retaining this fact asks for alternating-six
whole-core reconstruction only on original Sylow pairs. The binary row and
the complete G₂ reconstruction are supplied by their existing producers.

The alternating-six input still requires the whole intrinsic core and both
natural and exceptional outcomes. Its exceptional cubic plane branch is
excluded in `OriginalSylowA6` at the literal source; the Borel and natural
reconstruction obligations remain. The original 15.1.3 and 15.3.13 hypotheses
are preserved. This separate endpoint does not change the uniform C.1.32
contract or assert the completion of Theorem E.

Source: Aschbacher--Smith 15.3.25--32 and the proof of Theorem E,
printed pp.1130--1134 and 1165; C.1.31--32.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15
open Section03 ChapterA.Section05To06
open CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original E consumer needs alternating-six reconstruction only when
the original radical is Sylow in its actual join. The G₂ input is discharged. -/
theorem source_theoremE_of_original_sylow_A6_reconstruction
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (h1513 : ∀ Mc : Subgroup G,
      maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc} →
      ClassificationModels.IsTheoremEModel G ∨
        ∃ M : Subgroup G, IsOrderingMaximal T M ∧
          Nonempty (NaturalOrthogonalAction M (localModule T M)))
    (ha : ∀ (L R : Subgroup G),
      SmallMSPair KnownSimple.IsKnownSimple L R →
      Chapter1.IsSylowIn 2 R (L ⊔ R) →
      ((L ⧸ centralPreimage (pCore 2 L)) ≃*
        commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))) →
      AlternatingSixReconstruction L)
    (h13 : ∀ d : CharacteristicTwo.LocalData G, d.T = T →
      IsOrderingMaximal d.T d.M →
      maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc} →
      ∀ Yplus : Subgroup G, Hypothesis15310 d.M d.Y d.S d.V₁ Yplus →
      primeRank 3 Yplus = 2 →
      ∀ I ∈ outsideFamily Yplus d.S d.M, generalizedFitting I ≠ pCore 2 I) :
    ClassificationModels.IsTheoremEModel G := by
  apply source_theoremE_of_original_exclusions hG T hmany hempty h1513 h13
  intro d hd hM hu Yplus hchoice hshadow
  let d' : CharacteristicTwo.LocalData G := { d with Yplus := Yplus, choice := hchoice }
  have he : MainForward.faithfulLocalComponents d'.T = ∅ := hd ▸ hempty
  have hn : 1 < (maximalTwoLocalOvergroups (d'.T : Subgroup G)).ncard := hd ▸ hmany
  apply CharacteristicTwo.SourceRankOne.OriginalSource.source_lemma_15_3_25_of_rankTwo_source
    hG d' he hM hu hn hshadow
  intro I c s hm
  have hms := CharacteristicTwo.SourceRankOne.OriginalSource.source_smallMSPair s hm
  have hSyl :=
    CharacteristicTwo.SourceRankOne.OriginalSource.source_smallMSPair_original_sylow s
  rcases hms.rankTwo with hb | ha6 | hg2
  · obtain ⟨e⟩ := hb
    exact hms.rankTwo_of_binary e
  · obtain ⟨e⟩ := ha6
    exact hms.rankTwo_of_alternatingSix_reconstruction e
      (ha c.L d'.S hms hSyl e)
  · obtain ⟨e⟩ := hg2
    exact hms.rankTwo_g2_knownSimple e

end CFSG.Quasithin.Chapter15
