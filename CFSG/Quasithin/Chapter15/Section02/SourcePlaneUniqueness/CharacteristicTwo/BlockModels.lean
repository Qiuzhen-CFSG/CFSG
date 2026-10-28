module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.NoChiBlocks
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.BlockModels.LinearThree

/-!
# The complete preliminary block exclusions in original 15.2.23

The rank-one and alternating constituents exclude every chi-block. For a
binary linear-three C-component with the genuine original MS input, the
actual XQI construction excludes all non-block C.1.34 rows and retains the
natural block. C.1.28 then excludes NI≤MI on the original intersections.
This module re-exports the whole local family and applies it to one literal
source component; no model, action or local core comparison is assumed.

The universal C.1.34 input is owned by qt-rank-two-ms93. The Kc orbit input
is owned by qt-e-152-plane-geometry and qt-e-152-small-parabolic. Their final
discharge remains with qt-e-152-plane-characteristic-two and qt-theorem-e.
These conditional preliminary reductions do not prove all of 15.2.23.

Source: Aschbacher--Smith, preliminary 15.2.23 and its NI≤MI branch,
printed pp.1115--1116; C.1.28 and C.1.34; refs/quasithin.pdf.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding
open Section01 Section03 ChapterA.Section04 ChapterA.Section05To06
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- The source consumer combines all block exclusions and the original
NI≤MI contradiction, retaining the genuine natural binary block. -/
theorem source_block_exclusions_of_ms_component
    (classify : ∀ (J : Type u) [Group J] [Finite J] (L R : Subgroup J),
      SmallMSPair KnownSimple.IsKnownSimple L R → ∀ (n : ℕ), 1 ≤ n →
      ∀ (F : Type) [Field F] [Finite F], Nat.card F = 2 ^ n →
      Nonempty ((L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) F) →
      ∀ S : Subgroup J, Chapter1.IsSylowIn 2 S (L ⊔ R) → R ≤ S →
        ∃ e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) F,
          MSModuleAlternatives L R S n F e)
    (horbit : conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc = (pResidual 2 H).map H.subtype ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    {X : Subgroup I} (hX : X.IsCComponent)
    (eX : (X ⧸ pCore 2 X) ≃* Matrix.PSL3Two.PSL)
    {R : Subgroup G} (hR : IsPGroup 2 R) {n : ℕ} {F : Type} [Field F] [Finite F]
    (hms : LinearThreeMSPair KnownSimple.IsKnownSimple (X.map I.subtype) R n F) :
    (∀ B : Subgroup I, ¬ ChapterC.IsChiBlockIn B) ∧
      ChapterC.IsBlock X ∧ ChapterC.IsSL3EvenBlock (X.map I.subtype) 1 ∧
      ¬ M ⊓ I ≤ Mc ⊓ I := by
  obtain ⟨hblock,hmodel⟩ := d.linearThree_component_isBlock_of_source classify horbit
    hI hfit hX eX hR hms
  exact ⟨d.no_chi_block horbit hI hfit,hblock,hmodel,
    d.characteristicTwo_false_of_intersection_le_of_orbit horbit hI hfit⟩

end CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding
