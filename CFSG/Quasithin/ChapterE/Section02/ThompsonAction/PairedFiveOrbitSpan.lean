module
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.PairedFiveSaturation
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.PairSourceOrbitSpan
/-!
# The original symmetric-five pair's moved alpha orbit

The same actual pair supplies the sharp two-conjugate dimension bound.
Its genuine moved-space decomposition absorbs the offender-fixed summand
into the original fixed alpha subgroup. Thus the residual orbit identity
retains [U,O²(H)] and the same original E. The per-component index-two
Sylow geometry is supplied separately by the paired C.1.24 argument.
Source: Aschbacher–Smith B.6.10, E.2.3(3), pp.117 and216–217.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.ChapterE.ThompsonAction
open ChapterB ChapterB.SourceInduction BinaryPermutation
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]

theorem paired_five_source_orbit_span
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
    conjugateSpanBy (thompsonAlpha (T : Subgroup G)) (pResidual 2 G) =
      (⁅U,pResidual 2 G⁆ : Subgroup G) ⊔
        (thompsonAlpha (T : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G)) := by
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
  have hα := (paired_alpha_and_saturation_of_symmetric_model T hP U hU hJ q hq hker d c hexchange).2.1
  have hspan := RankOneBaumann.thompsonAlpha_span_of_two_conjugates T U q hq hker
    g hg hgen hcod (hα.trans (sup_comm _ _))
  have hfix : U ⊓ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ≤
      thompsonAlpha (T : Subgroup G) := le_sup_right.trans hα.ge
  rw [hspan]
  exact le_antisymm
    (sup_le (paired_module_le_moved_sup_alpha_fixed T hP U hU hJ q hq hker d _ hfix) le_sup_right)
    (sup_le_sup_right (commutator_le_left _ _) _)
end CFSG.Quasithin.ChapterE.ThompsonAction
