module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.BinaryBranch.SourceClassification.Recognition.NaturalDual
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.BinaryBranch.SourceClassification.Recognition.AlternatingEight
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.BinaryBranch.SourceClassification.Recognition.ModelOrders
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.BinaryBranch.SourceClassification.Recognition.ExteriorFive
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ExceptionalFixedSpace.TripleSix
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ExceptionalFixedSpace.BinaryG2

/-!
# Exclusion of the actual binary branch in 15.4.20

Apply the full corrected B.5.1 implication to the original offender actor.
Its socle has already been identified with the literal inner PSL₄(2) or
PSL₅(2). Exact order comparisons remove the incompatible rank-one and
larger-field cases. Every remaining actual module produces a cubic fixing
the Sylow fixed space, or contradicts its stated centralizer quotient.
The original seed centralizer excludes each case, retaining the same
submodule, quotient maps, group markings and nonsplit extensions.

The only classification premise in the final source endpoint is the genuine
universal B.5.1 implication with the full known-simple class. It contains
neither this binary exclusion nor a local small-section certificate.
Source: Aschbacher–Smith, B.4.2/B.5.1, pp.86,99–103; 15.4.20, p.1164.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.BinaryBranch.SourceClassification.Recognition
open TwoFactors.FFBranch TwoFactors.FFBranch.ClassificationComparison FFAlternatives
universe u
variable {G : Type u} [Group G] [Finite G]
  {d : Source.Geometry G} {i j : Bool} {H U K : Subgroup G}

/-- All actual B.5.1 module clauses are impossible for the binary source branch. -/
theorem excluded_of_quasisimple_conclusion (h : Input d i j H U K) {n : ℕ}
    (hn : n = 4 ∨ n = 5)
    (e : (H ⧸ pCore 2 H) ≃* MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2)))
    (c : let := h.module_properties.1;
      ProjectiveLine.QuasisimpleSourceConclusion (sourceAction h)
        (generalizedFitting (sourceGroup h))) : False := by
  let := h.module_properties.1
  have hcard := sourceFitting_card h hn e
  have hordinary : ¬ NativeSections.SectionModel
      (c.sectionData.action.comp (generalizedFitting (sourceGroup h)).subtype) :=
    offenderAction_not_sectionModel h.placed.sylow (d.Z.subgroupOf H)
      h.seed_inputs.2.2.1 (generalizedFitting (sourceGroup h)) c.sectionData
  cases c.clause_one with
  | irreducible _ faithful irreducible source _ =>
    cases source with
    | linearTwo F _ a _ _ => exact no_linearTwo hcard F a.groupEquiv
    | linearThree F _ a _ => exact hordinary (.linearThree F a)
    | symplectic F hF _ a _ => exact no_symplectic hcard F hF a.groupEquiv
    | symplecticTwo a _ => exact hordinary (.symplecticDerived (NativeSections.restrictMarked a))
    | g2 F hF _ a _ _ => exact no_g2 hcard F hF a.groupEquiv
    | g2Two a _ _ =>
      exact offenderAction_not_binaryG2 h.placed.sylow (d.Z.subgroupOf H)
        h.seed_inputs.2.2.1 _ c.sectionData a
    | symmetric m hm a _ _ =>
      rcases hm with rfl | rfl
      · exact no_linearTwo hcard BinaryField.four
          (a.subgroupEquiv.trans alternatingFiveLinearEquiv)
      · exact hordinary (.alternating 7 (Or.inr rfl) (NativeSections.restrictMarked a))
    | alternatingSix _ a _ _ => exact hordinary (.alternating 6 (Or.inl rfl) a)
    | alternatingSeven _ _ a dimension _ _ =>
      exact hordinary (.alternatingFour a (faithful.comp Subtype.val_injective) dimension)
    | tripleSix _ a _ =>
      exact offenderAction_not_tripleSix h.placed.sylow (d.Z.subgroupOf H)
        h.seed_inputs.2.2.1 _ c.sectionData faithful ⟨a⟩
    | binaryLinear m hm _ a _ => exact sourceAction_not_natural h c.sectionData hm a
    | orthogonalSix _ _ a _ _ => exact sourceAction_not_alternatingEight h c.sectionData a
    | symmetricEight _ a _ =>
      exact sourceAction_not_alternatingEight h c.sectionData (NativeSections.restrictMarked a)
    | exteriorFive _ _ a dimension _ _ =>
      exact ExteriorFive.sourceAction_not_exteriorFive h c.sectionData irreducible a dimension
  | doubleThree F _ a _ _ =>
    have hm : NativeSections.SectionModel
        (c.sectionData.space.toRepresentation.comp (generalizedFitting (sourceGroup h)).subtype) :=
      .repeatedThree F 2 a
    exact offenderAction_not_movedSpaceModel h.placed.sylow (d.Z.subgroupOf H)
      h.seed_inputs.2.2.1 _ c.sectionData hm
  | naturalDual m hm whole natural => exact not_naturalDual h c hm whole natural
  | repeatedNatural m r hm _ _ _ natural =>
    obtain ⟨a⟩ := natural
    exact sourceAction_not_repeatedNatural h c.sectionData hm r a

/-- The binary source quotient is excluded using only the genuine earlier universal classifier. -/
theorem excluded_of_classification (h : Input d i j H U K) {n : ℕ}
    (hn : n = 4 ∨ n = 5)
    (e : (H ⧸ pCore 2 H) ≃* MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2)))
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (earlier : ProjectiveLine.QuasisimpleClassificationInput.{u,u} KnownSimple.IsKnownSimple) :
    False := by
  obtain ⟨c⟩ := quasisimple_source_conclusion h hn e hH earlier
  exact excluded_of_quasisimple_conclusion h hn e c

/-- Apply the exclusion to the unchanged binary alternative of the source block sieve. -/
theorem not_binaryEmbedding (h : Input d i j H U K)
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (earlier : ProjectiveLine.QuasisimpleClassificationInput.{u,u} KnownSimple.IsKnownSimple) :
    ¬ BinaryEmbedding H K := by
  rintro ⟨_, n, hn, ⟨e⟩⟩
  exact excluded_of_classification h hn e hH earlier

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.BinaryBranch.SourceClassification.Recognition
