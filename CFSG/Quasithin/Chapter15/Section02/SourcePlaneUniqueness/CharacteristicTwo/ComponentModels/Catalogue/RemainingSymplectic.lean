module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.Symplectic
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.Remaining

/-!
# Symplectic restrictions on the original remaining component

The original escape selects one normalized component and retains its full
B.5.1 conclusion after the completed linear exclusions. For that same X,
R and NI, every remaining nonbinary symplectic marking now has even degree
and identifies the entire core quotient and original maximal parabolic.
The Omega action supplies the needed core identity internally.

Other nonlinear exclusions, the even symplectic degrees and full KS placement
remain open. The earlier small C.1.34 input keeps its independent producer
and final discharge at Theorem E.

Source: Aschbacher--Smith original 15.2.23, pp.1116--1117;
refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
open Section01 PlaneUniquenessPreceding TerminalLinear ChapterD ChapterD.UniqueFactor
open Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source ChapterB.QuasisimpleSource ChapterB.SourceInduction.ProjectiveLine
open Theory.SpecificGroups.SymplecticFour
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- The selected escaping component retains its full moved-section conclusion;
every surviving nonbinary symplectic model has even degree and the literal
full-core maximal-parabolic marking. -/
theorem exists_remaining_component_symplectic_marked
    (hC134 : EarlierMSClassifications.{u} KnownSimple.IsKnownSimple)
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃* ChosenGeometry.Wreath))
    (horbit : smallActionKc H Mc = smallActionK H ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        smallActionKc H Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hno : ∀ Y : Subgroup I, ¬ ChapterC.IsChiBlockIn Y)
    (hNI : ¬ M ⊓ I ≤ Mc ⊓ I)
    (ha : letI := hsource.prepared.elementary;
      Nonempty (internalActionImage M V hsource.prepared.normalized ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) ∨
      SourceCases.Omega (imageRepresentation M V hsource.prepared.normalized))
    (hi : OmegaAction.PlaneInverter hsource ZS) :
    ∃ X : Subgroup G, Normalized H M I X ∧
      (let R := (M ⊓ I).pCoreIn 2
       let ρ := starRepresentation X R
       let J := offenderSubgroup ρ
       starImage X R X ≤ J ∧
         ∃ c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
             (ρ.comp J.subtype) ((starImage X R X).subgroupOf J),
           RemainingActionCase (ρ.comp J.subtype) ((starImage X R X).subgroupOf J)
             c.sectionData) ∧
      ∀ (F : BinaryField), 1 < F.degree →
        ∀ e : starImage X ((M ⊓ I).pCoreIn 2) X ≃* Sp F.Carrier,
          Even F.degree ∧ ∃ a : (X ⧸ pCore 2 X) ≃* Sp F.Carrier,
            (∀ x : X, a (QuotientGroup.mk' (pCore 2 X) x) =
              e (toStarImage X ((M ⊓ I).pCoreIn 2) x)) ∧
            ∃ g : Sp F.Carrier,
              (((M ⊓ I).subgroupOf X).map
                (a.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X)))).map
                  (MulAut.conj g).toMonoidHom = pointParabolic ∨
              (((M ⊓ I).subgroupOf X).map
                (a.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X)))).map
                  (MulAut.conj g).toMonoidHom = planeParabolic := by
  obtain ⟨X,s,hc⟩ := exists_remaining_component d hC134 hquotient horbit hI hfit hno hNI ha hi
  refine ⟨X,s,hc,?_⟩
  let := hsource.prepared.elementary
  have ho := OmegaAction.omega_of_restricted_actions d hI ha hNI
  obtain ⟨eNI⟩ := OmegaAction.intersection_image_equiv_of_omega d hI hNI ho hi
  obtain ⟨f,hf,hker⟩ := OmegaAction.exists_symmetricThree_action_of_image_equiv eNI
  have hcore := d.intersection_core_eq_of_centralizes hI
    (intersection_core_centralizes_of_symmetricThree f hf hker)
  intro F hn e
  exact normalized_component_symplectic_marking d hI hcore s hn F.card_eq e

end CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
