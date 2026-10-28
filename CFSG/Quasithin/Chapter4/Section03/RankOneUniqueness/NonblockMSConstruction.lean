module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockMSNaturalCenter
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockMSParabolicMarking
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockMSMarkingApplications

/-!
# Original MS and secondary witnesses from the third classification row

The exact whole natural-center and doubled-dual sections now construct
MSData with both original markings. Parabolic recognition, line orientation,
the full-module identity and the Sylow centralizer are all discharged.
The same constructed witness selects the normal secondary component and
places the quadratic root-normalizer orbit inside its intrinsic two-core.

The whole-core section models and Sylow radical inequalities remain the
independently owned nonbinary classification input. This task retains their
final discharge, selection of the third row and strict secondary-core
enlargement; these conditional constructions do not complete original 4.3.2.
Source: Aschbacher--Smith C.1.34(3), pp.136--137; original 4.3.8--14,
pp.616--618.
-/

public section
open Subgroup Theory.GroupTheory Matrix.PSL3.LinearThree
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L}

/-- Construct MSData and both markings from the whole sections and radical
inequalities, with no local-image or full-module premise. -/
theorem exists_msData_of_caseThree_sections
    (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K) (n : ℕ) (hn : 1 < n)
    (F : ChapterB.QuasisimpleSource.BinaryField) (hdegree : F.degree = n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F.Carrier))
    (hnat : HasSectionModel (K c) (U c) ⊥ (linearThreeActor e)
      (Representation.specialLinearNatural (k := F.Carrier) 3))
    (hdual : HasSectionModel (K c) (Q c) (U c) (linearThreeActor e)
      ((Representation.specialLinearNatural (k := F.Carrier) 3).dual.prod
        (Representation.specialLinearNatural (k := F.Carrier) 3).dual))
    (hrad : ∀ P : Sylow 2 (K c ⊔ c.I.pCoreIn 2 : Subgroup G),
      c.I.pCoreIn 2 ≤ (P : Subgroup (K c ⊔ c.I.pCoreIn 2 : Subgroup G)).map
        (K c ⊔ c.I.pCoreIn 2 : Subgroup G).subtype →
      MSNotCentralizerCore (K c) (c.I.pCoreIn 2)
        ((P : Subgroup (K c ⊔ c.I.pCoreIn 2 : Subgroup G)).map
          (K c ⊔ c.I.pCoreIn 2 : Subgroup G).subtype)) :
    ∃ d : MSData c n, d.field = F ∧
      (L.subgroupOf (K c)).map (linearThreeActor d.model) = lineLocalSL d.field.Carrier ∧
      ((S c ⊓ L).subgroupOf (K c)).map (linearThreeActor d.model) = unipotentSL d.field.Carrier := by
  have hF : Nat.card F.Carrier = 2^n := F.card_eq.trans (congrArg (2^·) hdegree)
  obtain ⟨e',hnat',hdual',hpar⟩ := exists_reframed_natural_center_sections D hf hn hF e hnat hdual
  exact exists_msData_of_natural_center_sections D hf n hn F hdegree e' hnat' hdual' hpar hrad

/-- Apply the constructed MS witness to the actual secondary component and
its quadratic two-core layer, preserving both original embeddings. -/
theorem exists_sourceComponent_of_natural_center_sections
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hf : generalizedFitting c.K = pCore 2 c.K) (n : ℕ) (hn : 1 < n)
    (F : ChapterB.QuasisimpleSource.BinaryField) (hdegree : F.degree = n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F.Carrier))
    (hnat : HasSectionModel (K c) (U c) ⊥ (linearThreeActor e)
      (Representation.specialLinearNatural (k := F.Carrier) 3))
    (hdual : HasSectionModel (K c) (Q c) (U c) (linearThreeActor e)
      ((Representation.specialLinearNatural (k := F.Carrier) 3).dual.prod
        (Representation.specialLinearNatural (k := F.Carrier) 3).dual))
    (hrad : ∀ P : Sylow 2 (K c ⊔ c.I.pCoreIn 2 : Subgroup G),
      c.I.pCoreIn 2 ≤ (P : Subgroup (K c ⊔ c.I.pCoreIn 2 : Subgroup G)).map
        (K c ⊔ c.I.pCoreIn 2 : Subgroup G).subtype →
      MSNotCentralizerCore (K c) (c.I.pCoreIn 2)
        ((P : Subgroup (K c ⊔ c.I.pCoreIn 2 : Subgroup G)).map
          (K c ⊔ c.I.pCoreIn 2 : Subgroup G).subtype)) :
    ∃ B : Subgroup (rootNormalizer c),
      B.IsCComponent ∧ B.Normal ∧ IsQuasisimple (B ⧸ pCore 2 B) ∧
      secondary c < B.map (rootNormalizer c).subtype ∧
      B.map (rootNormalizer c).subtype ≤ Subgroup.centralizer (root c : Set G) ∧
      U c < rootCoreLayer c ∧
      rootCoreLayer c ≤ (B.map (rootNormalizer c).subtype).pCoreIn 2 ∧
      (B.map (rootNormalizer c).subtype ⊔ (T : Subgroup G)).pCoreIn 2 ≤ R₂ c ∧
      (frattini (rootCoreLayer c)).map (rootCoreLayer c).subtype ≤ root c ∧
      ⁅rootCoreLayer c,rootCoreLayer c⁆ ≤ root c := by
  obtain ⟨d,_,hL,_⟩ := exists_msData_of_caseThree_sections D hf n hn F hdegree e
    hnat hdual hrad
  exact d.exists_sourceComponent_of_line_marking hn D h hL

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
