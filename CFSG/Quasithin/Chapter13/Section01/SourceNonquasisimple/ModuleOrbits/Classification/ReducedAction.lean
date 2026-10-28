module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification.Statement
public import CFSG.Quasithin.ChapterB.InternalThompsonAction
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.OffenderSubgroup
public import Stellmacher.ElementaryAbelianMaxJMap

/-!
# The original reduced action inside the best-offender actor

The quotient N_G(L)/C_{N_G(L)}(R₂(N_G(L))) acts faithfully on the literal
reduced subgroup. Its normal best-offender subgroup inherits the trivial
two-core, and the original normalizer supplies a genuine SQTK cover. Thus
the completed B.5 classification applies with no additional FF hypothesis.

Maximum elementary subgroups of the original Sylow map to best offenders.
The authorized earlier equality L=[L,J(T)] therefore puts the actual image
of L inside this classified actor. The equality uses the repository's
maximum-elementary Thompson convention. Its source proof remains with
`qt-d-1317-supplements`; the four module markings remain with this module's
classification family, rather than being assumed by this construction.

Source: Aschbacher--Smith, 13.1.9(2)--13.1.10, printed pp.870--872,
and B.2.5, B.5.3--6, printed pp.76,104--105.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification
open Chapter1 Chapter1.Section02 Chapter12.Section02
open ChapterB.SourceInduction ChapterB.InternalThompsonAction
universe u
variable {G : Type u} [Group G] [Finite G]

@[expose] instance reducedElementary (L : Subgroup G) :
    IsElementaryAbelian 2 (NormalizerReducedAction.Core L) :=
  isPReduced_reducedPSubgroup.elementary

@[expose] def reducedRepresentation (L : Subgroup G) :
    Representation (ZMod 2) (NormalizerReducedAction.Star L)
      (Additive (NormalizerReducedAction.Core L)) :=
  ChapterB.InternalThompsonAction.action (NormalizerReducedAction.Core L)

omit [Finite G] in
theorem reducedRepresentation_apply (L : Subgroup G)
    (m : NormalizerReducedAction.Ambient L)
    (v : Additive (NormalizerReducedAction.Core L)) :
    ((reducedRepresentation L (NormalizerReducedAction.quotient L m) v).toMul :
      NormalizerReducedAction.Ambient L) = m * (v.toMul : NormalizerReducedAction.Ambient L) * m⁻¹ :=
  ChapterB.InternalThompsonAction.action_apply _ m v

omit [Finite G] in
theorem reducedRepresentation_faithful (L : Subgroup G) :
    Function.Injective (reducedRepresentation L) :=
  ChapterB.InternalThompsonAction.action_faithful _

omit [Finite G] in
theorem reducedStar_twoCore (L : Subgroup G) :
    pCore 2 (NormalizerReducedAction.Star L) = ⊥ :=
  isPReduced_reducedPSubgroup.quotient_pCore_eq_bot

theorem normalizer_sqtk {T : Sylow 2 G} {L : Subgroup G}
    (h : Hypothesis1311 T) (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) :
    IsSQTK KnownSimple.IsKnownSimple (NormalizerReducedAction.Ambient L) := by
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  obtain ⟨he, hne, _, hnorm⟩ := faithful_maximal_normalizer_moved h.simpleQTKE hL hTL
  let : IsElementaryAbelian 2 (normalizerMoved L) := he
  exact h.simpleQTKE.twoLocal_sqtk
    ⟨normalizerMoved L, hne, IsElementaryAbelian.isPGroup 2 _, hnorm.symm⟩

theorem reducedOffender_hypothesis {T : Sylow 2 G} {L : Subgroup G}
    (h : Hypothesis1311 T) (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) :
    FFHypothesis KnownSimple.IsKnownSimple
      ((reducedRepresentation L).comp (offenderSubgroup (reducedRepresentation L)).subtype) :=
  ChapterB.InternalThompsonAction.offender_hypothesis _
    (NormalizerReducedAction.quotient L) (QuotientGroup.mk'_surjective _)
    (normalizer_sqtk h hL hn) (reducedRepresentation_faithful L) (reducedStar_twoCore L)

theorem reducedOffender_adequateAlternative {T : Sylow 2 G} {L : Subgroup G}
    (h : Hypothesis1311 T) (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) :
    AdequateAlternative
      ((reducedRepresentation L).comp (offenderSubgroup (reducedRepresentation L)).subtype) :=
  adequateAlternative_knownSimple _ (reducedOffender_hypothesis h hL hn)

theorem componentImage_commutator_thompson {T : Sylow 2 G} {L : Subgroup G}
    (hTL : (T : Subgroup G) ≤ NormalizerReducedAction.Ambient L)
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆) :
    ⁅NormalizerReducedAction.componentImage L,
      (elementaryAbelianMaxJ ((T.subtype hTL : Sylow 2 (NormalizerReducedAction.Ambient L)) :
        Subgroup (NormalizerReducedAction.Ambient L))).map (NormalizerReducedAction.quotient L)⁆ =
      NormalizerReducedAction.componentImage L := by
  let M := NormalizerReducedAction.Ambient L
  have he : ⁅L.subgroupOf M, elementaryAbelianMaxJ ((T : Subgroup G).subgroupOf M)⁆ =
      L.subgroupOf M := by
    apply map_injective M.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le L.le_normalizer,
      ← elementaryAbelianMaxJ_map_injective M.subtype M.subtype_injective,
      map_subgroupOf_eq_of_le hTL, ← ChapterB.thompsonJ_zero]
    exact hmove.symm
  rw [NormalizerReducedAction.componentImage_eq, Sylow.coe_subtype]
  change ⁅(L.subgroupOf M).map (NormalizerReducedAction.quotient L),
    (elementaryAbelianMaxJ ((T : Subgroup G).subgroupOf M)).map (NormalizerReducedAction.quotient L)⁆ = _
  rw [← map_commutator, he]

theorem componentImage_le_reducedOffender {T : Sylow 2 G} {L : Subgroup G}
    (h : Hypothesis1311 T) (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆) :
    NormalizerReducedAction.componentImage L ≤ offenderSubgroup (reducedRepresentation L) := by
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  let : (offenderSubgroup (reducedRepresentation L)).Normal := offenderSubgroup_normal _
  have hj := ChapterB.InternalThompsonAction.thompson_image_le
    (T.subtype hTL) (NormalizerReducedAction.Core L)
  rw [← componentImage_commutator_thompson hTL hmove]
  have hj' : (elementaryAbelianMaxJ ((T.subtype hTL : Sylow 2 (NormalizerReducedAction.Ambient L)) :
      Subgroup (NormalizerReducedAction.Ambient L))).map (NormalizerReducedAction.quotient L) ≤
      offenderSubgroup (reducedRepresentation L) := hj
  exact (commutator_mono le_rfl hj').trans (commutator_le_right _ _)

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification
