module
public import CFSG.Quasithin.Chapter3.Section01.ChiefAction.SeedClassification
public import CFSG.Quasithin.Chapter3.Section01.ChiefAction.SeedOffender

/-!
# Small natural essential actions from the original qrc hypotheses

The source maximal elementary subgroup is a sharp offender on every chief
factor and on every essential seed action. Applying the Borel exclusions to
that very action eliminates the higher-field alternatives. This discharges
the FF premise in `SeedClassification` using the original source hypotheses.

Source: Aschbacher–Smith, original 3.1.9(5), printed pp.577–578, as used in
original 15.1.12(3).
-/

public section
open Subgroup Representation Representation.BinaryOffender NoncentralChiefRefinement Stellmacher
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter3
open ChapterD ChapterD.UniqueFactor Theory.GroupTheory ChapterB
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M M₀ H V : Subgroup G}

theorem QrcHypotheses.sqtk_essential_small_natural_alternatives
    (h : QrcHypotheses T M M₀ H V) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → M₀ ≤ N → N = M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (hne : V ≠ ⊥) (hV : V ≤ twoCoreIn H)
    (hdual : ¬ DualFF (h.toQRCConfiguration (h.no_common_normal hu)))
    (hres : (pResidual 2 (H ⊓ M : Subgroup G)).map (H ⊓ M).subtype ≤ centralizer (V : Set G))
    (hq : letI := h.module_elementary
      quadraticRatio (imageRepresentation M₀ V h.module_normalized) = 2) :
    let d := h.toQRCConfiguration (h.no_common_normal hu)
    let U := (conjugateSpan H V).subgroupOf H
    let S := T.subtype h.right_mem.1.1.2
    letI := d.module_elementary
    letI := source_elementary_span_of_notFF d hV (source_notFF_of_ratio_two d hq)
    letI : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
      ((span_le_right_core d hV).trans (twoCore_le H))
    ∀ a : EssentialSeedAction H V S (hV.trans (twoCore_le H)),
      ChiefSmallNaturalAlternatives a.imageRepresentation := by
  let d := h.toQRCConfiguration (h.no_common_normal hu)
  let := d.module_elementary
  let := source_elementary_span_of_notFF d hV (source_notFF_of_ratio_two d hq)
  let U := (conjugateSpan H V).subgroupOf H
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    ((span_le_right_core d hV).trans (twoCore_le H))
  obtain ⟨A,hA,hAR,hchief,hseed⟩ :=
    h.sqtk_essential_sharp_offender hG hM hu hJ hne hV hdual hq
  exact fun a => a.small_natural_alternatives h hG hres ⟨_,(hseed a).1⟩

end CFSG.Quasithin.Chapter3
