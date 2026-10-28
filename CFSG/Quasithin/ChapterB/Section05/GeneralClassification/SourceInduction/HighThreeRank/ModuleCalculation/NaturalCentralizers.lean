module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.ModuleCalculation.NaturalCentralizers.NormalizerTransport
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.ModuleCalculation.NaturalCentralizers.OffenderPlane
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.ModuleCalculation.NaturalCentralizers.OffenderPlane.SourceEndgame

/-!
# The cubic core and both ambient centralizers in B.5.7

The concrete scalar commutants fix the original component moved space by
O₃(G). Given the surviving six-point marking and the two-dimensional cubic
moved space, odd-order averaging identifies the original O₃(G) with C₃.
The full normalizer of the marked action supplies a local symmetric
supplement. Offender generation removes the extra central factor and proves
C_G(L) = O₃(G); the remaining index-two calculation proves
C_G(O₃(G)) = L O₃(G). Both model identifications are actual equivalences.

`cubicCentralizers_of_moved_model` completes this calculation from an actual
`SymmetricMovedModel` and a best offender moving O₃(G). The proved concrete
commutants supply the crossed fixation needed by `source_offender_plane`;
its seven-point exclusion and cubic plane dimension feed the ambient
centralizer assembly. No numerical, span, commutant, or universal earlier-source
premise remains. The old inconsistent `OffenderPlaneBounds` record is not used.
The five-dimensional augmentation core and its fixed line are retained.
Constructing the marked moved model remains with the preceding source argument.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.7,
printed p.106, final paragraph.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.ModuleCalculation.NaturalCentralizers
universe u v
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}
variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
variable (ρ : Representation (ZMod 2) G V)

/-- Both literal centralizer equalities follow from the surviving marked
six-point action and the original cubic moved plane. No centralizer equality,
outer shape, or global fixed-space splitting is an input. -/
theorem cubicCentralizers_of_six_plane (hyp : FFHypothesis K ρ)
    {L : Subgroup G} (hL : IsComponent G L) (d : NoncentralContext K G L)
    {A : Subgroup G} (m : SymmetricMovedModel ρ L A)
    (marking :
      Nonempty (MarkedActionEquiv m.sectionData.space.toRepresentation ⊤
        (L.subgroupOf (L ⊔ A)) (BinaryPermutation.naturalRepresentation (Fin 6))
        (alternatingGroup (Fin 6))) ∨
      Nonempty (MarkedActionEquiv m.sectionData.space.toRepresentation ⊤
        (L.subgroupOf (L ⊔ A)) (BinaryPermutation.coreRepresentation (Fin 6))
        (alternatingGroup (Fin 6))))
    (plane : Module.finrank (ZMod 2) (moved ρ (pCore 3 G)) = 2) :
    Nonempty (CubicCentralizers G L) := by
  let : L.Normal := d.normal
  have hthree := threeCore_card_of_plane ρ hyp d plane
  let eX := threeCoreEquiv_of_plane ρ hyp d plane
  rcases marking with hn | hc
  · obtain ⟨e⟩ := hn
    obtain ⟨hc, hd, hi⟩ := marked_symmetric_supplement ρ m
      (BinaryPermutation.naturalRepresentation (Fin 6))
      CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.symmetricAction_injective
      CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.normalizer_alternatingImage e
    let eL := (subgroupOfEquivOfLe (le_sup_left : L ≤ L ⊔ A)).symm.trans e.subgroupEquiv
    have hh := centralizers_of_symmetric_supplement ρ hyp hL d eL hthree (L ⊔ A) hc hd hi
    exact ⟨⟨eL, eX, hh.1, hh.2⟩⟩
  · obtain ⟨e⟩ := hc
    obtain ⟨hc, hd, hi⟩ := marked_symmetric_supplement ρ m
      (BinaryPermutation.coreRepresentation (Fin 6))
      CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.coreAction_injective
      ConcreteModels.core_six_normalizer e
    let eL := (subgroupOfEquivOfLe (le_sup_left : L ≤ L ⊔ A)).symm.trans e.subgroupEquiv
    have hh := centralizers_of_symmetric_supplement ρ hyp hL d eL hthree (L ⊔ A) hc hd hi
    exact ⟨⟨eL, eX, hh.1, hh.2⟩⟩

/-- Actual consumer of a completed offender endgame. The group identifications
are reconstructed from its marking and plane; both ambient centralizers are
proved through the module normalizer and offender generation. -/
theorem cubicCentralizers_of_offender_conclusion (hyp : FFHypothesis K ρ)
    {L : Subgroup G} (hL : IsComponent G L) (d : NoncentralContext K G L)
    {A : Subgroup G} (m : SymmetricMovedModel ρ L A)
    (c : OffenderPlaneConclusion ρ d m) : Nonempty (CubicCentralizers G L) :=
  cubicCentralizers_of_six_plane ρ hyp hL d m c.marking c.plane

/-- The B.5.7 module endgame from the actual marked moved module. The concrete
commutants discharge crossed fixation, the source offender argument determines
the six-point marking and cubic plane, and the ambient normalizer calculation
proves both centralizer equalities. No global fixed-space splitting is needed. -/
theorem cubicCentralizers_of_moved_model (hyp : FFHypothesis K ρ)
    {L : Subgroup G} (hL : IsComponent G L) (d : NoncentralContext K G L)
    {A : Subgroup G} (hA : IsBestOffender ρ A)
    (hm : ¬ A ≤ centralizer (pCore 3 G : Set G))
    (m : SymmetricMovedModel ρ L A) : Nonempty (CubicCentralizers G L) := by
  have hfix := threeCore_fixes_model ρ ConcreteModels.modelCommutants hL d m
  exact cubicCentralizers_of_offender_conclusion ρ hyp hL d m
    (source_offender_plane ρ hyp hL d hA hm hfix m)

end CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.ModuleCalculation.NaturalCentralizers
