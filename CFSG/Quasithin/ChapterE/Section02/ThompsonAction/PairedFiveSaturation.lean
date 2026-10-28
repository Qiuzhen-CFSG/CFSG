module
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.PairedFiveBounds

/-!
# Baumann alpha and kernel saturation on the genuine symmetric-five pair

The actual paired quotient supplies a residual conjugator joining two
Thompson images to the whole offender layer. Their codimensions four and
four sum to the residual codimension eight. Strong replacement and the
genuine source Frattini theorem discharge the remaining hypotheses of
B.2.18. This gives the original alpha identity and Sylow saturation in
the actual centralizer; no two-group centralizer assumption is added.

Source: Aschbacher--Smith B.2.18, B.6.10 and E.2.3(3).
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.ChapterE.ThompsonAction
open ChapterB ChapterB.SourceInduction BinaryPermutation
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]

theorem paired_alpha_and_saturation_of_symmetric_model
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (d : SourceTwoFactorCase ((NormalElementaryQuotient.representation U q hq hker).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype))
    (c : d.MarkedProduct (naturalRepresentation (Fin 5)))
    (hexchange : letI := offenderSubgroup_normal (NormalElementaryQuotient.representation U q hq hker)
      ∃ t : T.mapSurjective hq,
        d.first.map (MulAut.conjNormal (t:H)).toMonoidHom = d.second ∧
        d.second.map (MulAut.conjNormal (t:H)).toMonoidHom = d.first) :
    (pCore 2 (pResidual 2 G)).map (pResidual 2 G).subtype ≤ baumann (T : Subgroup G) ∧
      thompsonAlpha (T : Subgroup G) =
        (thompsonAlpha (T : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G)) ⊔
          (U ⊓ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)) ∧
      IsSylowSubgroupIn (baumann (T : Subgroup G) ⊓ centralizer (U : Set G))
        ((pResidual 2 G ⊔ baumann (T : Subgroup G)) ⊓ centralizer (U : Set G)) := by
  let α := NormalElementaryQuotient.representation U q hq hker
  let Y := offenderSubgroup α
  let e := c.action.groupEquiv
  let j := Y.subtype.comp e.symm.toMonoidHom
  have hres := source_symmetric_residual T hP U hU hJ q hq hker d c
  obtain ⟨a,b,ha⟩ := paired_thompson_of_symmetric_model T U hU hJ q hq hker d c hexchange
  obtain ⟨z,hz,hgen0⟩ := ChapterC.SymmetricFive.Paired.exists_residual_conjugate_transposition_product a b
  have hzmap : j z ∈ (pResidual 2 G).map q := by
    rw [hres]
    exact mem_map_of_mem j hz
  obtain ⟨g,hg,hqg⟩ := hzmap
  have himage : ((elementaryAbelianMaxJ (T : Subgroup G)).map (MulAut.conj g).toMonoidHom).map q =
      ((elementaryAbelianMaxJ (T : Subgroup G)).map q).map (MulAut.conj (q g)).toMonoidHom := by
    rw [map_map,map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply]
  have hcj (A : Subgroup (FiveCentralExtension.Sym × FiveCentralExtension.Sym)) :
      (A.map j).map (MulAut.conj (j z)).toMonoidHom =
        (A.map (MulAut.conj z).toMonoidHom).map j := by
    rw [map_map,map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply]
  have hgen : (pResidual 2 G).map q ≤ (elementaryAbelianMaxJ (T : Subgroup G)).map q ⊔
      ((elementaryAbelianMaxJ (T : Subgroup G)).map (MulAut.conj g).toMonoidHom).map q := by
    rw [himage,ha,hqg]
    change (pResidual 2 G).map q ≤ _ ⊔ ((_ : Subgroup _).map j).map (MulAut.conj (j z)).toMonoidHom
    rw [hcj,←Subgroup.map_sup,hgen0,hres]
    exact map_mono le_top
  have hcod : 2 * BaumannArgument.fixedCodim U (elementaryAbelianMaxJ (T : Subgroup G)) ≤
      BaumannArgument.fixedCodim U (pResidual 2 G) := by
    rw [BaumannArgument.fixedCodim_eq_centralizer_quotient U q hq hker,
      BaumannArgument.fixedCodim_eq_centralizer_quotient U q hq hker,ha,hres,
      source_symmetric_fixedCodim U q hq hker d c,
      source_symmetric_fixedCodim U q hq hker d c,
      ChapterC.SymmetricFive.Paired.fixedCodim_transposition_product,
      ChapterC.SymmetricFive.Paired.fixedCodim_residual_product]
  exact RankOneBaumann.two_conjugate_alpha_and_saturation T hP U hU hJ q hker
    (RankOneBaumann.residual_centralizer_le_coreFrattini T hP U hU hJ)
    (BaumannArgument.noStrong_of_centralizer_quotient U q hq hker
      (c.symmetric_not_strong α d) (T : Subgroup G)) g hg hgen hcod
end CFSG.Quasithin.ChapterE.ThompsonAction
