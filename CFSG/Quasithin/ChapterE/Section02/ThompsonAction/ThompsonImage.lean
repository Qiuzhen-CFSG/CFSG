module
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.Basic
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.PairedFiveImages
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.PairResidualImages
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricFive.Paired.LocalIndex
public import Theory.GroupTheory.ElementaryThompsonSpan
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.PairedFactorOrbit.SourceGeometry
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricFive.Paired.LocalSpan

/-!
# The global Thompson image on the original paired factors

The Sylow Thompson image lies in the original offender product; global
Thompson generation gives the same containment for J(G). In the natural
linear pair its Sylow image and the residual generate both factors. In the
symmetric pair, the alternating axes and the actual transposition four-groups
generate the same product. Residual containment in J(G) proves the reverse
inclusion, preserving the actual quotient and chosen factor pair.

Source: Aschbacher–Smith E.2.3(1), printed pp.216–217.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.ThompsonAction
open ChapterB ChapterB.SourceInduction
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]

theorem global_thompson_image_le_offender
    (T : Sylow 2 G) (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G)) (hUT : U ≤ T) :
    (elementaryAbelianMaxJ (⊤ : Subgroup G)).map q ≤
      offenderSubgroup (NormalElementaryQuotient.representation U q hq hker) := by
  let Y := offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)
  let := offenderSubgroup_normal (NormalElementaryQuotient.representation U q hq hker)
  have hJT := RankOneBaumann.thompson_image_le_offender_layer T U q hq hker hUT Y le_rfl
  rw [elementaryAbelianMaxJ_eq_conjugateSpan_sylow T]
  apply map_le_iff_le_comap.mpr
  exact conjugateSpanBy_le (map_le_iff_le_comap.mp hJT) le_normalizer_of_normal

theorem paired_symmetric_global_thompson_image
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (d : SourceTwoFactorCase ((NormalElementaryQuotient.representation U q hq hker).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype))
    (c : d.MarkedProduct (BinaryPermutation.naturalRepresentation (Fin 5)))
    (hexchange : letI := offenderSubgroup_normal (NormalElementaryQuotient.representation U q hq hker)
      ∃ t : T.mapSurjective hq,
        d.first.map (MulAut.conjNormal (t:H)).toMonoidHom = d.second ∧
        d.second.map (MulAut.conjNormal (t:H)).toMonoidHom = d.first) :
    (elementaryAbelianMaxJ (⊤ : Subgroup G)).map q =
      offenderSubgroup (NormalElementaryQuotient.representation U q hq hker) := by
  let α := NormalElementaryQuotient.representation U q hq hker
  let Y := offenderSubgroup α
  let j := Y.subtype.comp c.action.groupEquiv.symm.toMonoidHom
  obtain ⟨a,b,hJT⟩ := paired_thompson_of_symmetric_model T U hU hJ q hq hker d c hexchange
  have hgen := paired_residual_factors_generate T hP U hU hJ q hq hker d
  have hres : (pResidual 2 G).map q =
      ((alternatingGroup (Fin 5)).prod (alternatingGroup (Fin 5))).map j := by
    rw [←hgen,Subgroup.map_sup,paired_symmetric_first_residual_image α q hq d c,
      paired_symmetric_second_residual_image α q hq d c,←Subgroup.map_sup,
      ChapterC.SymmetricFive.Paired.prod_sup_prod,sup_bot_eq,bot_sup_eq]
  have hjoint : (pResidual 2 G).map q ⊔
      (elementaryAbelianMaxJ (T : Subgroup G)).map q = Y := by
    rw [hres,hJT,←Subgroup.map_sup,ChapterC.SymmetricFive.Paired.prod_sup_prod,
      ChapterC.SymmetricFive.Paired.alternating_sup_transposition,
      ChapterC.SymmetricFive.Paired.alternating_sup_transposition,top_prod_top]
    change (⊤ : Subgroup (Equiv.Perm (Fin 5) × Equiv.Perm (Fin 5))).map
      (Y.subtype.comp c.action.groupEquiv.symm.toMonoidHom) = Y
    rw [←Subgroup.map_map,map_top_of_surjective _ c.action.groupEquiv.symm.surjective,
      ←MonoidHom.range_eq_map,range_subtype]
  refine le_antisymm (global_thompson_image_le_offender T U q hq hker
    (hU.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal T))) ?_
  change Y ≤ _
  rw [←hjoint]
  exact sup_le (map_mono (residual_le_thompson T hP U hU hJ).1)
    (map_mono (elementaryAbelianMaxJ_sylow_le_top T))
theorem paired_linear_global_thompson_image
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (d : SourceTwoFactorCase ((NormalElementaryQuotient.representation U q hq hker).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype))
    (F : ChapterB.QuasisimpleSource.BinaryField) (c : d.MarkedProduct (ChapterB.QuasisimpleSource.linearNatural F 2))
    (hexchange : letI := offenderSubgroup_normal (NormalElementaryQuotient.representation U q hq hker)
      ∃ t : T.mapSurjective hq,
        d.first.map (MulAut.conjNormal (t:H)).toMonoidHom = d.second ∧
        d.second.map (MulAut.conjNormal (t:H)).toMonoidHom = d.first) :
    (elementaryAbelianMaxJ (⊤ : Subgroup G)).map q =
      offenderSubgroup (NormalElementaryQuotient.representation U q hq hker) := by
  let α := NormalElementaryQuotient.representation U q hq hker
  let Y := offenderSubgroup α
  let := offenderSubgroup_normal α
  obtain ⟨ρ,hρ,hnat,he,⟨hJT,hBT⟩,hfix⟩ :=
    RankOneBaumann.PairedFactorOrbit.source_images_and_fixedSpace T hP U hU hJ q hq hker d F c hexchange
  obtain ⟨P,hPmap⟩ := (T.mapSurjective hq).exists_sylow_map_eq_inf_of_normal Y
  change (P : Subgroup Y).map Y.subtype = (T : Subgroup G).map q ⊓ Y at hPmap
  have hsup : (pResidual 2 Y).map Y.subtype ⊔ (elementaryAbelianMaxJ (T : Subgroup G)).map q = Y := by
    rw [show (elementaryAbelianMaxJ (T : Subgroup G)).map q = (T : Subgroup G).map q ⊓ Y from hJT,←hPmap,←Subgroup.map_sup,pResidual_sup_sylow_eq_top,
      ←MonoidHom.range_eq_map,range_subtype]
  apply le_antisymm (global_thompson_image_le_offender T U q hq hker
    (hU.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal T)))
  change Y ≤ _
  rw [←hsup]
  apply sup_le _ (map_mono (elementaryAbelianMaxJ_sylow_le_top T))
  apply (map_pResidual_le 2 Y.subtype).trans
  rw [←map_pResidual_of_surjective 2 q hq]
  exact map_mono (residual_le_thompson T hP U hU hJ).1
end CFSG.Quasithin.ChapterE.ThompsonAction
