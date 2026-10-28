module
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.SeedGeneration
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.FactorImages
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.PairedLinearField
/-!
# The common Baumann subgroup is Sylow in the actual residual

The source seed-centralizer condition excludes both five-letter rows.
In the single and paired natural rows the offender group is perfect, and
the Baumann image lies in the residual image. If the actual action kernel
already lies in the residual, image containment lifts to the original group.
The E.2.3 Sylow conclusion therefore holds inside the residual itself.
Source: Aschbacher--Smith E.2.3 and 10.2.3(4), pp.216--217 and747.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open ChapterB ChapterB.QuasisimpleSource ChapterB.SourceInduction ChapterE.ThompsonAction
universe u
variable {G : Type u} [Group G] [Finite G]
set_option backward.isDefEq.respectTransparency false in
theorem source_baumann_sylow_in_residual_of_seed_centralizer
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) (hU : IsPReduced 2 U)
    (hns : ¬ Group.IsSolvable G)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (Z : Subgroup G) (hZU : Z ≤ U)
    (hCZ : centralizer (Z : Set G) = (T : Subgroup G))
    (hkr : centralizer (U : Set G) ≤ pResidual 2 G) :
    Chapter1.IsSylowIn 2 (baumann (T : Subgroup G)) (pResidual 2 G) := by
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set G)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk : q.ker = centralizer (U : Set G) := QuotientGroup.ker_mk' C
  let α := NormalElementaryQuotient.representation U q hq hk
  let Y := offenderSubgroup α
  let := offenderSubgroup_normal α
  have hcore : pCore 2 (G ⧸ C) = ⊥ := hU.quotient_pCore_eq_bot
  have hn : q.ker ≠ ⊤ := by
    intro he
    exact hJ (hk ▸ (he ▸ (le_top : elementaryAbelianMaxJ (T : Subgroup G) ≤ ⊤)))
  have hp := (minimalParabolic_reduced_image T hP q hq hcore hn).2
  have hff : IsFFModule α := by
    obtain hf | ⟨_,hf,_,_,_⟩ := lemma_B_2_7 U q hq hk T
    · exact (hJ ((elementaryAbelianMaxJ_sylow_le_top T).trans hf.1)).elim
    · exact hf
  have lift (hB : (baumann (T : Subgroup G)).map q ≤ (pResidual 2 G).map q)
      (hS : Chapter1.IsSylowIn 2 (baumann (T : Subgroup G))
        (pResidual 2 G ⊔ baumann (T : Subgroup G))) :
      Chapter1.IsSylowIn 2 (baumann (T : Subgroup G)) (pResidual 2 G) := by
    have hBR := map_le_iff_le_comap.mp hB
    rw [comap_map_eq,sup_eq_left.mpr (hk.symm ▸ hkr)] at hBR
    simpa only [sup_eq_left.mpr hBR] using hS
  rcases source_nonsolvable_natural_factors hG T hP U hU hns hJ with
    ⟨hqs,c,hlinear | hfive⟩ | ⟨d,_,_⟩
  · obtain ⟨F,hF⟩ := hlinear
    have htop := (quasisimple_linear_whole_source T hP U hU hJ q hq hk
      hqs c.sectionData F hF).2.1
    have hY : Y = (pResidual 2 G).map q := by
      have hh := (source_quasisimple_fitting_eq_residual (T.mapSurjective hq) hp Y
        (offender_generation (T.mapSurjective hq) hp α hff hcore).2 hqs).1
      rw [htop,←MonoidHom.range_eq_map,range_subtype] at hh
      rwa [map_pResidual_of_surjective 2 q hq]
    apply lift
    · exact (quasisimple_linear_source_images T hP U hU hJ q hq hk
        hqs c.sectionData F hF).2.le.trans (inf_le_right.trans hY.le)
    · exact (quasisimple_linear_baumann_of_section T hP U hU hJ q hq hk
        hqs c.sectionData F hF).1
  · obtain ⟨a⟩ := hfive
    exfalso
    apply not_five_movedSection_of_seed U Z q hq hk hZU T hCZ Y
      (generalizedFitting Y) c.sectionData
    refine ⟨a.subgroupEquiv,a.action.linearEquiv,?_⟩
    intro g v
    exact (a.action.intertwines ⟨g,a.contained g.property⟩ v).trans
      (congrArg (fun k => BinaryPermutation.naturalRepresentation (Fin 5) k
        (a.action.linearEquiv v)) (a.compatible g))
  · obtain ⟨t,ht₁,ht₂,hkind⟩ := source_offender_two_factor_shared_natural
      α (T.mapSurjective hq) hp hff hcore d
    rcases hkind with ⟨F,hlin⟩ | hsym
    · obtain ⟨c⟩ := hlin
      have hF := ChapterC.RankOne.ChiProduct.SelectedRankOne.paired_linear_field_large
        T hP U hU hJ q hq hk hns d F c
      have hlarge : 3 < Nat.card F.Carrier := by
        rw [F.card_eq] at hF ⊢
        have hd : 2 ≤ F.degree := by
          by_contra! hh
          have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hh
          norm_num at hp
          omega
        have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hd
        norm_num at hp
        omega
      let A := Matrix.SpecialLinearGroup (Fin 2) F.Carrier
      let : Group.IsPerfect A := GorensteinWalter.sl2_isPerfect_of_card_gt_three F.Carrier hlarge
      let : Group.IsPerfect (A × A) := ⟨by
        rw [commutator_def,←top_prod_top,commutator_prod_prod]
        simp only [←commutator_def,Group.IsPerfect.commutator_eq_top]⟩
      let : Group.IsPerfect Y := Group.IsPerfect.ofSurjective
        (f := c.action.groupEquiv.symm.toMonoidHom) c.action.groupEquiv.symm.surjective
      have hY : Y ≤ (pResidual 2 G).map q := by
        rw [map_pResidual_of_surjective 2 q hq]
        let : Group.IsNilpotent ((G ⧸ C) ⧸ pResidual 2 (G ⧸ C)) :=
          (isPGroup_quotient_pResidual 2).isNilpotent
        exact le_of_isPerfect_of_solvable_quotient Y _
      obtain ⟨_,_,_,_,⟨_,hB⟩,_⟩ := RankOneBaumann.PairedFactorOrbit.source_images_and_fixedSpace
        T hP U hU hJ q hq hk d F c ⟨t,ht₁,ht₂⟩
      exact lift (hB.le.trans (inf_le_right.trans hY))
        (RankOneBaumann.PairedFactorOrbit.source_global_baumann_and_alpha
          T hP U hU hJ q hq hk d F c ⟨t,ht₁,ht₂⟩).1
    · obtain ⟨c⟩ := hsym
      exact (not_pairedFive_of_seed U Z q hq hk hZU T hCZ Y d c).elim
end CFSG.Quasithin.Chapter10
