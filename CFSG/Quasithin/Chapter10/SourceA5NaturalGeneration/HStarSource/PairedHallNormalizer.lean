module
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.HStarSource.PairedHallCubic
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.PairedFactorOrbit.CanonicalNormalizer
public import Theory.GroupTheory.Hall.NormalTwoCore
/-!
# The prescribed Hall subgroup normalizes the selected paired component

The canonical component selected by the original paired source is normal
in the offender preimage. Its proved two-conjugate cover puts the entire
two-residual in that preimage. Every odd Hall subgroup of the maximal
overlap lies in the ambient two-residual, and therefore normalizes both
the same selected component and each of its Sylow conjugates. The original
quotient, first source factor and chosen component remain unchanged.
Source: Aschbacher--Smith 10.2.3(4), pp.746--747.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterB ChapterB.SourceInduction
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

set_option backward.isDefEq.respectTransparency false in
/-- Apply directly to `hcan` and `hcover` returned by
`source_hstar_paired_component_and_hall_cubic`. No new choice of component
or quotient marking is made, and the conclusion covers its Hall-conjugated cubic. -/
theorem source_hstar_paired_hall_normalizes
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (BH : Subgroup H) (hBM : BH ≤ D.maximalLocal.subgroupOf H)
    (hHall : IsHallSubgroup Subgroup.OddHall.oddPrimes
      (BH.subgroupOf (D.maximalLocal.subgroupOf H))) :
    let S := T.subtype hH.1.1.2
    let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
    letI := (source_hstar_omega_orbit_reduced D hH).normal
    letI := (source_hstar_omega_orbit_reduced D hH).elementary
    let C := centralizer (U : Set H)
    let q := QuotientGroup.mk' C
    let hq := QuotientGroup.mk'_surjective C
    let hk := QuotientGroup.ker_mk' C
    let α := NormalElementaryQuotient.representation U q hq hk
    let Y := offenderSubgroup α
    ∀ (d : SourceTwoFactorCase (α.comp Y.subtype)) (K : Subgroup H),
      (solvableResidual (ChapterB.RankOneBaumann.PairedFactorOrbit.factorPreimage q Y d.first)).map
        (ChapterB.RankOneBaumann.PairedFactorOrbit.factorPreimage q Y d.first).subtype = K →
      (∃ t ∈ (S : Subgroup H), pResidual 2 H = K ⊔ K.map (MulAut.conj t).toMonoidHom) →
      BH ≤ normalizer (K : Set H) ∧
        ∀ t : H, BH ≤ normalizer (K.map (MulAut.conj t).toMonoidHom : Set H) := by
  let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
  let := (source_hstar_omega_orbit_reduced D hH).normal
  let := (source_hstar_omega_orbit_reduced D hH).elementary
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  let α := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  let Y := offenderSubgroup α
  let := offenderSubgroup_normal α
  dsimp only
  intro d K hcan hcover
  let := d.product.first_normal
  have hBR : BH ≤ pResidual 2 H := by
    have hh := hall_le_normal_of_two_quotient
      (pResidual 2 (D.maximalLocal.subgroupOf H))
      (BH.subgroupOf (D.maximalLocal.subgroupOf H)) (isPGroup_quotient_pResidual 2) hHall
    have hm := (map_mono (f := (D.maximalLocal.subgroupOf H).subtype) hh).trans
      (map_pResidual_le 2 (D.maximalLocal.subgroupOf H).subtype)
    rwa [map_subgroupOf_eq_of_le hBM] at hm
  have hn := ChapterB.RankOneBaumann.PairedFactorOrbit.canonical_factor_residual_normalizes_conjugates
    q Y d.first K hcan (by obtain ⟨t,_,ht⟩ := hcover; exact ⟨t,ht⟩)
  exact ⟨hBR.trans hn.1,fun t => hBR.trans (hn.2 t)⟩
end CFSG.Quasithin.Chapter10
