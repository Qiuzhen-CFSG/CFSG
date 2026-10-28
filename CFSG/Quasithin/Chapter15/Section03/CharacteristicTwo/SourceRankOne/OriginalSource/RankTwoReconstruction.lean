module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.RankTwoBinary
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.MSAssembly
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.RankTwoReconstruction

/-!
# Original rank-one applications of the two MS reconstruction inputs

The original source data supplies the complete small MS-pair. Splitting its
three quotient rows uses the proved binary theorem and the two explicit
whole-core reconstruction inputs. The second application feeds the resulting
earlier classifications into the original 15.3.25 argument.

The alternating-six and G₂ reconstruction implications, and the independent
C.1.34 implication, remain premises. These conditional applications do not
assert C.1.32 or C.1.34 without their producers.

Source: Aschbacher--Smith C.1.31--34 and 15.3.25--32, printed pp.135--137,
1130--1134; Meierfrankenfeld--Stellmacher (1993), Main Theorem (2),(6),(10).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
open ChapterA.Section05To06 RankOneConfiguration SmallExtension MarkedMS
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Apply the reconstructed rows to the actual original marking. The binary
row is already unconditional through `source_linearThree_rankTwo`. -/
theorem source_rankTwo_of_reconstruction {κ : GroupClass.{u}}
    (ha : AlternatingSixReconstructionInput κ) (hg : G2ReconstructionInput κ)
    {d : LocalData G} {I : Subgroup G} {c : ComponentWitness d I}
    (s : SourceData κ d c) (hm : Parabolics.SmallParabolicMarking d I c.L) :
    RankTwoAlternatives c.L d.S := by
  cases hm with
  | linearThree m => exact source_linearThree_rankTwo s m
  | symplecticDerived m =>
    have hms := smallMSPair_of_source d c s.sqtk s.characteristicTwo s.generated s.normal
      ⟨s.sylow, s.sylow_eq⟩ s.characteristic (.symplecticDerived m)
    let e := (centralCoreQuotientEquivStar d c s.normal s.sylow s.sylow_eq
      (.symplecticDerived m)).trans m.equiv
    exact hms.rankTwo_of_alternatingSix_reconstruction e (ha G c.L d.S hms e)
  | g2Derived m =>
    have hms := smallMSPair_of_source d c s.sqtk s.characteristicTwo s.generated s.normal
      ⟨s.sylow, s.sylow_eq⟩ s.characteristic (.g2Derived m)
    let e := (centralCoreQuotientEquivStar d c s.normal s.sylow s.sylow_eq
      (.g2Derived m)).trans m.equiv
    exact hms.rankTwo_of_g2_reconstruction e (hg G c.L d.S hms e)

/-- The literal original 15.3.25 assembly, with precisely the two C.1.32
reconstructions and the independently owned C.1.34 implication left explicit. -/
theorem source_lemma_15_3_25_of_reconstruction
    (ha : AlternatingSixReconstructionInput.{u} KnownSimple.IsKnownSimple)
    (hg : G2ReconstructionInput.{u} KnownSimple.IsKnownSimple)
    (linearThree : ∀ (J : Type u) [Group J] [Finite J] (L R : Subgroup J),
      SmallMSPair KnownSimple.IsKnownSimple L R → ∀ (n : ℕ), 1 ≤ n →
      ∀ (F : Type) [Field F] [Finite F], Nat.card F = 2 ^ n →
      Nonempty ((L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) F) →
      ∀ S : Subgroup J, Chapter1.IsSylowIn 2 S (L ⊔ R) → R ≤ S →
        ∃ e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) F,
          MSModuleAlternatives L R S n F e)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hshadow : SymmetricThreeShadow d.Yplus d.S) :
    ∀ I ∈ d.Hplus, generalizedFitting I ≠ pCore 2 I :=
  source_lemma_15_3_25_of_MS_classifications
    (earlierMSClassifications_of_reconstruction ha hg linearThree)
    hG d hempty hM hu hmany hshadow

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
