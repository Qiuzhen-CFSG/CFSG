module
public import CFSG.Quasithin.Chapter3.Section01.ChiefAction.Offender
public import CFSG.Quasithin.ChapterB.Section06To07.ChiefActions.NaturalSource

/-!
# Natural classification on the original qrc chief factors

The actual source equality supplies a sharp FF offender on each noncentral
factor of every chief series of the original H-span of V. The original
SQTK group and minimal parabolic then supply B.6.9's natural alternatives,
with the same factor representation and its literal faithful image.
No classification, image-faithfulness, or chief-module premise is added.

This is the classification step in3.1.9(5), used by15.1.12(3). The extra
residual-centralizer hypothesis is reserved for the subsequent exclusion
of larger-field SL₂ factors; that exclusion is not asserted here.
Source: Aschbacher–Smith, printed pp.577–578 and1089–1090.
-/

public section
open Subgroup Representation Representation.BinaryOffender NoncentralChiefRefinement Stellmacher
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter3
open ChapterD ChapterD.UniqueFactor Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M M₀ H V : Subgroup G}

theorem QrcHypotheses.sqtk_chief_natural_alternatives
    (h : QrcHypotheses T M M₀ H V) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → M₀ ≤ N → N = M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (hne : V ≠ ⊥) (hV : V ≤ twoCoreIn H)
    (hdual : ¬ DualFF (h.toQRCConfiguration (h.no_common_normal hu)))
    (hq : letI := h.module_elementary
      quadraticRatio (imageRepresentation M₀ V h.module_normalized) = 2) :
    let d := h.toQRCConfiguration (h.no_common_normal hu)
    let U := (conjugateSpan H V).subgroupOf H
    letI := d.module_elementary
    letI := source_elementary_span_of_notFF d hV (source_notFF_of_ratio_two d hq)
    letI : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
      ((span_le_right_core d hV).trans (twoCore_le H))
    ∀ (s : SeriesOn U) (i : Fin s.series.length), ¬ s.Central i →
      ChapterB.ChiefNaturalAlternatives (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i)) ∧
      subspaceCommutator (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i)) ⊤
        (offenderSubgroup (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i))) = ⊤ := by
  let d := h.toQRCConfiguration (h.no_common_normal hu)
  let := d.module_elementary
  let := source_elementary_span_of_notFF d hV (source_notFF_of_ratio_two d hq)
  let U := (conjugateSpan H V).subgroupOf H
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    ((span_le_right_core d hV).trans (twoCore_le H))
  let S := T.subtype h.right_mem.1.1.2
  have hS : (S : Subgroup H).map H.subtype = T := map_subgroupOf_eq_of_le h.right_mem.1.1.2
  obtain ⟨A,hA,hAR,hff⟩ := h.sqtk_chief_ff_actor hG hM hu hJ hne hV hdual hq
  dsimp only
  intro s i hi
  let := s.factorRepresentation_irreducible i
  exact ChapterB.minimalParabolic_chief_natural_alternatives (s.factorRepresentation i)
    (sqtk_of_mem_H hG h.right_mem.1.1.1) S
    (source_intrinsic_minimalParabolic_of_notFF d hne (source_notFF_of_ratio_two d hq) S hS)
    ⟨_,(hff s i hi).1⟩


end CFSG.Quasithin.Chapter3
