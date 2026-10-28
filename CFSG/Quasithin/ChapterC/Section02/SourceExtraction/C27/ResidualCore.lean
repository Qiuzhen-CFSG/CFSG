module
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.ResidualModule
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.MSInputs

/-!
# The original residual product has the same two-core

The odd-index radical contains O₂(I). The product O²(I)R is subnormal in I,
so its embedded two-core is contained in O₂(I); normality of O₂(I) gives the
reverse inclusion. Consequently the moved star subgroup is precisely the
commutator of the original omega-center with O²(I).

This identifies the two actual elementary layers used in 14.6.10(5). It
makes no assertion that the commutator of the entire two-core is elementary.
Source: Aschbacher–Smith C.1.31, C.2.7 and 14.6.10(5), pp.135,146,1029.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction
variable {G : Type*} [Group G] [Finite G]

/-- The original residual product retains the complete ambient two-core. -/
theorem residual_join_twoCore_eq (I R : Subgroup G)
    (hRI : R ≤ I) (hr : MSOddIndexRadical (R.subgroupOf I)) :
    let C := (pResidual 2 I).map I.subtype
    (C ⊔ R).pCoreIn 2 = I.pCoreIn 2 := by
  let C := (pResidual 2 I).map I.subtype
  let J := C ⊔ R
  have hCI : C ≤ I := map_subtype_le _
  have hJI : J ≤ I := sup_le hCI hRI
  have hJsub : (J.subgroupOf I).IsSubnormal :=
    residual_overgroup_subnormal _ (fun x hx => mem_sup_left (mem_map_of_mem I.subtype hx))
  have hQ : J.pCoreIn 2 ≤ I.pCoreIn 2 := by
    have hh := map_mono (f := I.subtype) (pCoreIn_le_of_subnormal 2 hJsub)
    rw [map_pCoreIn_of_injective 2 _ I.subtype I.subtype_injective,
      map_subgroupOf_eq_of_le hJI] at hh
    exact hh
  have hQR : I.pCoreIn 2 ≤ R := by
    have hh := map_mono (f := I.subtype) hr.twoCore_le
    rwa [map_subgroupOf_eq_of_le hRI] at hh
  have hIQ : I ≤ normalizer (I.pCoreIn 2 : Set G) := I.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image I (pCore 2 I))
  exact le_antisymm hQ (le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 I)
    (hQR.trans le_sup_right) (hJI.trans hIQ))

/-- Literal star coordinates identify the original omega-center commutator. -/
theorem residual_star_moved_eq_omegaCore_commutator (I R : Subgroup G)
    (hRI : R ≤ I) (hr : MSOddIndexRadical (R.subgroupOf I)) :
    let C := (pResidual 2 I).map I.subtype
    (⁅starV C R,C.subgroupOf (C ⊔ R)⁆).map (C ⊔ R : Subgroup G).subtype =
      ⁅omegaOneCenterAmbient (I.pCoreIn 2),C⁆ := by
  intro C
  rw [map_commutator,map_subgroupOf_eq_of_le (show C ≤ C ⊔ R from le_sup_left)]
  have he : (starV C R).map (C ⊔ R : Subgroup G).subtype =
      omegaOneCenterAmbient ((C ⊔ R).pCoreIn 2) := by
    exact (omegaOneCenterAmbient_map_injective _ (C ⊔ R : Subgroup G).subtype_injective
      (pCore 2 (C ⊔ R : Subgroup G))).symm
  rw [he,residual_join_twoCore_eq I R hRI hr]
end CFSG.Quasithin.ChapterC.C27Source
