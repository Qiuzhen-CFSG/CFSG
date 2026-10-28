module
public import CFSG.Quasithin.Chapter3.Section01.ChiefAction.Alignment
public import CFSG.Quasithin.Chapter3.Section01.ChiefAction.SeedAction
public import Theory.GroupAction.NormalPChiefSeries.Sections
public import Theory.Representation.BinaryOffender.ChiefImageTransport

/-!
# The same sharp offender on the essential source action

The essential residual image is an irreducible submodule of a quotient of the
original elementary abelian span. Pulling its two endpoints back gives an
actual chief interval, and refinement puts that interval into a chief series.
The source sharp-offender theorem applies to every such series. Its specified
linear coordinates therefore transfer the same original subgroup A to the
faithful essential action, including equality of rank and fixed codimension.

Source: Aschbacher–Smith3.1.9(5), printed p.578, used in15.1.12(3).
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory NoncentralChiefRefinement Stellmacher
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter3
open ChapterD ChapterD.UniqueFactor Theory.GroupTheory ChapterB
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M M₀ H V : Subgroup G}

theorem EssentialSeedAction.sharp_offender_of_chiefs
    [IsElementaryAbelian 2 ((conjugateSpan H V).subgroupOf H)]
    {S : Sylow 2 H} {hVH : V ≤ H}
    (a : EssentialSeedAction H V S hVH) (A : Subgroup H)
    (hff : ∀ (s : SeriesOn ((conjugateSpan H V).subgroupOf H)) (i : Fin s.series.length),
      ¬ s.Central i →
      IsOffender (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i))
        (actionSubgroup (s.factorRepresentation i) A) ∧
      rank (actionSubgroup (s.factorRepresentation i) A) =
        fixedCodim (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i))
          (actionSubgroup (s.factorRepresentation i) A)) :
    IsOffender a.imageRepresentation (A.map a.projection) ∧
      rank (A.map a.projection) = fixedCodim a.imageRepresentation (A.map a.projection) := by
  let := a.irreducible
  have hn : ∃ g v, a.representation g v ≠ v := by
    by_contra hn
    push Not at hn
    apply a.projection_kernel_ne_top
    apply top_unique
    intro g _
    exact (actionHom_eq_one_iff a.representation g).mpr (hn g)
  obtain ⟨s,i,hi,e,he⟩ := SeriesOn.exists_irreducible_subquotient_coordinates ((conjugateSpan H V).subgroupOf H) a.kernel a.socle hn
  exact sharp_image_offender_of_equivariant a.representation (s.factorRepresentation i)
    e (fun g v => (he g v).symm) (hff s i hi).1 (hff s i hi).2


theorem QrcHypotheses.sqtk_essential_sharp_offender
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
    let S := T.subtype h.right_mem.1.1.2
    letI := d.module_elementary
    letI := source_elementary_span_of_notFF d hV (source_notFF_of_ratio_two d hq)
    letI : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
      ((span_le_right_core d hV).trans (twoCore_le H))
    ∃ A ∈ elementaryAbelianMaxSubgroups (S : Subgroup H), ¬ A ≤ pCore 2 H ∧
      (∀ (s : SeriesOn U) (i : Fin s.series.length), ¬ s.Central i →
        IsOffender (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i))
          (actionSubgroup (s.factorRepresentation i) A) ∧
        rank (actionSubgroup (s.factorRepresentation i) A) =
          fixedCodim (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i))
            (actionSubgroup (s.factorRepresentation i) A)) ∧
      ∀ a : EssentialSeedAction H V S (hV.trans (twoCore_le H)),
        IsOffender a.imageRepresentation (A.map a.projection) ∧
          rank (A.map a.projection) = fixedCodim a.imageRepresentation (A.map a.projection) := by
  let d := h.toQRCConfiguration (h.no_common_normal hu)
  let := d.module_elementary
  let := source_elementary_span_of_notFF d hV (source_notFF_of_ratio_two d hq)
  let U := (conjugateSpan H V).subgroupOf H
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    ((span_le_right_core d hV).trans (twoCore_le H))
  obtain ⟨A,hA,hAR,hff⟩ := h.sqtk_chief_ff_actor hG hM hu hJ hne hV hdual hq
  refine ⟨A,hA,hAR,hff,?_⟩
  exact fun a => a.sharp_offender_of_chiefs A hff

end CFSG.Quasithin.Chapter3
