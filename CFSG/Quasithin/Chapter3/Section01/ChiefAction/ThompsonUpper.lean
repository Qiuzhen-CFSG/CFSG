module
public import CFSG.Quasithin.Chapter3.Section01.ChiefAction.ThompsonReplacement
public import Theory.GroupTheory.ElementaryThompsonSpan
/-!
# The source Thompson upper bound from paired centralizers

Every moving maximum elementary subgroup contains an offender in its
literal noncentral chief image, by quadratic replacement. Its whole image
centralizes that offender. Thus a centralizer bound for the chief model
puts every Sylow maximum image inside the offender subgroup. Normality and
Sylow conjugacy give the same upper bound for the original global J(H).

The only remaining input is the stated model centralizer bound; it is
consumed on the actual chief action, not on a substituted subgroup.
Source: Aschbacher–Smith 3.1.9(5), printed p.578.
-/

public section
open Subgroup Representation Representation.BinaryOffender NoncentralChiefRefinement Stellmacher
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter3
open ChapterD ChapterD.UniqueFactor Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M M₀ H V : Subgroup G}

set_option backward.isDefEq.respectTransparency false in
theorem QrcHypotheses.sqtk_chief_thompson_image_le_of_offender_centralizers
    (h : QrcHypotheses T M M₀ H V) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → M₀ ≤ N → N = M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (hne : V ≠ ⊥) (hV : V ≤ twoCoreIn H)
    (hdual : ¬ DualFF (h.toQRCConfiguration (h.no_common_normal hu)))
    (hq : let := h.module_elementary
      quadraticRatio (imageRepresentation M₀ V h.module_normalized) = 2) :
    let d := h.toQRCConfiguration (h.no_common_normal hu)
    let U := (conjugateSpan H V).subgroupOf H
    let := d.module_elementary
    let := source_elementary_span_of_notFF d hV (source_notFF_of_ratio_two d hq)
    let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
      ((span_le_right_core d hV).trans (twoCore_le H))
    ∀ (s : SeriesOn U) (i : Fin s.series.length), ¬ s.Central i →
      (∀ B : Subgroup (actionImage (s.factorRepresentation i)),
        IsOffender (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i)) B →
        centralizer (B : Set (actionImage (s.factorRepresentation i))) ≤
          offenderSubgroup (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i))) →
      (elementaryAbelianMaxJ (⊤ : Subgroup H)).map (actionHom (s.factorRepresentation i)) ≤
        offenderSubgroup (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i)) := by
  let d := h.toQRCConfiguration (h.no_common_normal hu)
  let := d.module_elementary
  have hnf := source_notFF_of_ratio_two d hq
  let := source_elementary_span_of_notFF d hV hnf
  let U := (conjugateSpan H V).subgroupOf H
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    ((span_le_right_core d hV).trans (twoCore_le H))
  let S := T.subtype h.right_mem.1.1.2
  have hS : (S : Subgroup H).map H.subtype = T := map_subgroupOf_eq_of_le h.right_mem.1.1.2
  have hP := source_intrinsic_minimalParabolic_of_notFF d hne hnf S hS
  have hreplace := h.sqtk_chief_max_contains_offender hG hM hu hJ hne hV hdual hq
  dsimp only
  intro s i hi hcent
  let ρ := s.factorRepresentation i
  let Y := offenderSubgroup (Representation.BinaryOffender.imageRepresentation ρ)
  let q := actionHom ρ
  let : Y.Normal := offenderSubgroup_normal _
  have hlocal : elementaryAbelianMaxJ (S : Subgroup H) ≤ Y.comap q := by
    apply sSup_le
    intro A hA
    apply Subgroup.map_le_iff_le_comap.mp
    by_cases hAR : A ≤ pCore 2 H
    · have hk := MultipleFactors.source_chief_sylow_kernel U S hP s i hi A hA.1
      have hAk : A ≤ ρ.ker := by
        rw [inf_eq_left.mpr hAR] at hk
        exact hk.ge.trans inf_le_right
      have he : A.map q = ⊥ := (Subgroup.map_eq_bot_iff A).mpr (by
        rwa [actionHom_ker_eq])
      rw [he]
      exact bot_le
    · obtain ⟨B,hB,hBA⟩ := hreplace A hA hAR s i hi
      let : IsElementaryAbelian 2 A := hA.2.1
      let : IsElementaryAbelian 2 (A.map q) := IsElementaryAbelian.map q
      have hc : A.map q ≤ centralizer (B : Set (actionImage ρ)) := by
        intro a ha b hb
        exact setLike_mul_comm (s := A.map q) (hBA hb) ha
      exact hc.trans (hcent B hB)
  apply Subgroup.map_le_iff_le_comap.mpr
  rw [elementaryAbelianMaxJ_eq_conjugateSpan_sylow S]
  exact conjugateSpanBy_le hlocal (by
    rw [Subgroup.normalizer_eq_top])
end CFSG.Quasithin.Chapter3
