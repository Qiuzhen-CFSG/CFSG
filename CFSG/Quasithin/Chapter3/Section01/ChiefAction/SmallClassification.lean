module
public import CFSG.Quasithin.Chapter3.Section01.ChiefAction.SeedAlignment
public import CFSG.Quasithin.Chapter3.Section01.ChiefAction.SeedClassification
public import CFSG.Quasithin.Chapter3.Section01.ChiefAction.Natural
public import CFSG.Quasithin.ChapterB.Section06To07.ChiefActions.ResidualClassification
public import CFSG.Quasithin.ChapterB.Section06To07.ChiefActions.SmallResidual
/-!
# Small natural actions on every original noncentral chief factor

The original maximal elementary subgroup offends sharply on every chief
factor and on the essential seed action. The seed geometry classifies the
latter among the small natural rows, where no offender lies in the two-residual.
For a nonsolvable original actor, all the literal chief kernels equal its
canonical core. Residual membership of the same subgroup therefore agrees
with its membership in the essential action. Larger linear rows would put
that offender in the residual, giving a contradiction. Solvable original
actors are classified directly by their small natural wreath actions.

This proves the field-exclusion and matching step of original 3.1.9(5)
from the original hypotheses, without an extra classification, matching,
or faithful-action premise. It retains the actual factor representations
of every chief series of the original span and their full moved spaces.
Source: Aschbacher–Smith, printed pp.577–578, used in 15.1.12(3).
-/
public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory NoncentralChiefRefinement Stellmacher
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter3
open ChapterD ChapterD.UniqueFactor ChapterB
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {M M₀ H V : Subgroup G}

theorem EssentialSeedAction.all_chief_small_of_sharp
    [IsElementaryAbelian 2 ((conjugateSpan H V).subgroupOf H)]
    {S : Sylow 2 H} {hVH : V ≤ H}
    (a : EssentialSeedAction H V S hVH)
    (hD : IsSQTK KnownSimple.IsKnownSimple H)
    (hsmall : ChiefSmallNaturalAlternatives a.imageRepresentation)
    (A : Subgroup H)
    (hff : ∀ (s : SeriesOn ((conjugateSpan H V).subgroupOf H)) (i : Fin s.series.length),
      ¬ s.Central i →
      IsOffender (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i))
        (actionSubgroup (s.factorRepresentation i) A) ∧
      rank (actionSubgroup (s.factorRepresentation i) A) =
        fixedCodim (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i))
          (actionSubgroup (s.factorRepresentation i) A)) :
    ∀ (s : SeriesOn ((conjugateSpan H V).subgroupOf H)) (i : Fin s.series.length),
      ¬ s.Central i →
      ChiefSmallNaturalAlternatives
        (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i)) := by
  have hseed := a.sharp_offender_of_chiefs A hff
  have hn : ¬ A.map a.projection ≤ pResidual 2 a.Actor :=
    small_natural_offender_not_le_twoResidual a.imageRepresentation
      (imageRepresentation_injective a.representation)
      (imageRepresentation_irreducible a.representation a.irreducible)
      (S.mapSurjective a.projection_surjective) a.reduced_minimal a.twoCore_eq_bot hsmall hseed.1
  intro s i hi
  let := s.factorRepresentation_irreducible i
  have hb := minimalParabolic_sharp_image_isBestOffender
    (s.factorRepresentation i) hD S a.original_minimal (hff s i hi).1 (hff s i hi).2
  apply minimalParabolic_chief_small_of_offender_not_residual
    (s.factorRepresentation i) hD S a.original_minimal hb
  intro hs hres
  exact hn ((a.chief_residual_membership_iff hD hs ⟨_,hseed.1⟩ s i
    ⟨_,(hff s i hi).1⟩ A).mp hres)

theorem QrcHypotheses.sqtk_chief_small_natural_alternatives
    (h : QrcHypotheses T M M₀ H V) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → M₀ ≤ N → N = M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (hne : V ≠ ⊥) (hV : V ≤ twoCoreIn H)
    (hdual : ¬ DualFF (h.toQRCConfiguration (h.no_common_normal hu)))
    (hq : letI := h.module_elementary
      quadraticRatio (imageRepresentation M₀ V h.module_normalized) = 2)
    (hres : (pResidual 2 (H ⊓ M : Subgroup G)).map (H ⊓ M).subtype ≤
      centralizer (V : Set G)) :
    let d := h.toQRCConfiguration (h.no_common_normal hu)
    let U := (conjugateSpan H V).subgroupOf H
    letI := d.module_elementary
    letI := source_elementary_span_of_notFF d hV (source_notFF_of_ratio_two d hq)
    letI : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
      ((span_le_right_core d hV).trans (twoCore_le H))
    ∀ (s : SeriesOn U) (i : Fin s.series.length), ¬ s.Central i →
      ChiefSmallNaturalAlternatives (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i)) ∧
      subspaceCommutator (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i)) ⊤
        (offenderSubgroup (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i))) = ⊤ := by
  let d := h.toQRCConfiguration (h.no_common_normal hu)
  let := d.module_elementary
  let := source_elementary_span_of_notFF d hV (source_notFF_of_ratio_two d hq)
  let U := (conjugateSpan H V).subgroupOf H
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    ((span_le_right_core d hV).trans (twoCore_le H))
  obtain ⟨A,hA,hAR,hff⟩ := h.sqtk_chief_ff_actor hG hM hu hJ hne hV hdual hq
  obtain ⟨a⟩ := h.sqtk_essential_seed_action hu hne hV hq
  have hseed := a.sharp_offender_of_chiefs A hff
  have hsmall := a.small_natural_alternatives h hG hres ⟨_,hseed.1⟩
  have hc := a.all_chief_small_of_sharp (sqtk_of_mem_H hG h.right_mem.1.1.1) hsmall A hff
  have hg := h.sqtk_chief_natural_alternatives hG hM hu hJ hne hV hdual hq
  dsimp only
  intro s i hi
  exact ⟨hc s i hi,(hg s i hi).2⟩
end CFSG.Quasithin.Chapter3
