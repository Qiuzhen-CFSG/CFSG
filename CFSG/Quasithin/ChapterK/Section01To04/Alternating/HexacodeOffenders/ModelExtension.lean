module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.HexacodeOffenders.ModelContract
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.HexacodeOffenders.PlaneKernels
public import Theory.Representation.BinaryOffender.GeneratedCore
public import Theory.Representation.BinaryOffender.RatioFromStrong

/-!
# Extending the even-cover offender calculation

Once best offenders in the full hexacode group are known to be even,
restriction supplies all their weight comparisons in the even cover.
The plane kernels in the two groups agree by semilinearity. Generation
and the ratio then follow from the even calculation: strong replacement
would put a strong best offender in the even cover, where ratio one
excludes it.

This proves the extension step of K.1.3 conditionally on its two distinct
local calculations. Source: Aschbacher–Smith, combined manuscript of
1 March 2004, printed p.453 (PDF p.464).
-/

public section
open Subgroup Representation Representation.BinaryOffender Atlas.Codes

namespace CFSG.Quasithin.ChapterK.Alternating.HexacodeOffenders

/-- The outer branch needs only the exclusion of best offenders meeting the odd coset.
It does not need a second independent plane or ratio classification. -/
theorem full_model_of_even
    (heven : ModelCalculation Hexacode.evenAction ⊤)
    (hout : ∀ A, IsBestOffender Hexacode.action A → A ≤ hexSign.ker) :
    ModelCalculation Hexacode.action hexSign.ker := by
  have hgen : offenderSubgroup Hexacode.action = hexSign.ker := by
    apply le_antisymm
    · apply iSup_le
      intro A
      apply iSup_le
      rintro ⟨hA, _⟩
      exact hout A hA
    · have hm : (offenderSubgroup Hexacode.evenAction).map hexSign.ker.subtype =
          hexSign.ker := by
        rw [heven.generated]
        ext x
        exact ⟨fun ⟨g, _, hg⟩ => hg ▸ g.property,
          fun hx => ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩⟩
      rw [← hm, offenderSubgroup, generatedBy, Subgroup.map_iSup]
      apply iSup_le
      intro A
      rw [Subgroup.map_iSup]
      apply iSup_le
      rintro ⟨hA, _⟩
      exact (hA.map_subtype Hexacode.action).le_offenderSubgroup Hexacode.action
  have hno : ¬ IsStrongFFModule Hexacode.evenAction := by
    rw [isStrongFFModule_iff_quadraticRatio_lt_one, heven.ratio]
    exact lt_irrefl _
  have hff : IsFFModule Hexacode.action := by
    have he : IsFFModule Hexacode.evenAction :=
      (isFFModule_iff_quadraticRatio_le_one _).mpr heven.ratio.le
    exact he.map_equivariant Hexacode.evenAction Hexacode.action
      hexSign.ker.subtype hexSign.ker.subtype_injective (LinearEquiv.refl _ _) (fun _ _ => rfl)
  have hratio : quadraticRatio Hexacode.action = 1 := by
    apply quadraticRatio_eq_one_of_no_strong Hexacode.action hff
    intro A hA
    obtain ⟨B, _, hB, hs⟩ := hA.exists_bestOffender Hexacode.action
    have hBL := hout B hB
    apply hno
    refine ⟨B.subgroupOf hexSign.ker, (hB.subgroupOf Hexacode.action hBL).1, ?_⟩
    change fixedCodim (Hexacode.action.comp hexSign.ker.subtype)
      (B.subgroupOf hexSign.ker) < rank (B.subgroupOf hexSign.ker)
    rw [fixedCodim_subgroupOf Hexacode.action hBL, rank_subgroupOf hBL]
    exact hs.2
  refine ⟨hgen, hratio, ?_⟩
  intro A hA
  have hAL := hout A hA
  obtain ⟨P, hd, hP⟩ := heven.offenders _ (hA.subgroupOf Hexacode.action hAL)
  refine ⟨P, hd, ?_⟩
  have h := congrArg (Subgroup.map hexSign.ker.subtype) hP
  rw [Subgroup.map_subgroupOf_eq_of_le hAL, planeKernel_even_map P hd] at h
  exact h

end CFSG.Quasithin.ChapterK.Alternating.HexacodeOffenders
