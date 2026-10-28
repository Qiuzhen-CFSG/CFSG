module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.EndNodeGeometry
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedOffenders.ActionTransport
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedOffenders.PairedMinimality
public import Theory.ElementaryAbelian.Injective

/-!
The original end-node modules and their conjugates construct the paired
configuration used in [AS, 15.3.25]. The action kernels are their literal
centralizers, and 15.3.32(5–6) supplies the disjoint modules and core generation.
The fixed-line residual identity from 15.3.32(3) remains an explicit input;
the subsequent quotient geometry is a separate construction.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
open Subgroup RankOneConfiguration EightGeometry
variable {G : Type*} [Group G] [Finite G] {d : LocalData G} {I : Subgroup G}
  {c : ComponentWitness d I}

namespace EndNodeData
/-- The original natural and conjugate modules construct the complete paired
configuration. Only the separate fixed-line residual identity is needed. -/
def pairedConfiguration (e : EndNodeData d I c)
    (hL : c.L = RankOne.threeResidualIn
      (centralizer ((d.ZS ⊓ d.V₁ : Subgroup G) : Set G)))
    (t : G) (ht : t ∈ (d.T : Subgroup G)) (htS : t ∉ d.S) :
    PairedMinimality.Configuration d I c.L
      (RankOne.threeResidualIn (centralizer (d.ZS : Set G))) t := by
  let X := RankOne.threeResidualIn (centralizer (d.ZS : Set G))
  let N := X ⊔ d.S
  let U := d.componentModule I c.L
  have hi := d.action.planeStabilizer_index_two d.T d.sylow_le 1
  have hTS : (d.T : Subgroup G) ≤ normalizer (d.S : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (show d.S ≤ (d.T : Subgroup G) from inf_le_left)).mp
      (normal_of_index_eq_two hi)
  have hS : d.S.conjBy t = d.S := mem_normalizer_iff_map_conj_eq.mp (hTS ht)
  have hTN := residual_join_normalized_by_sylow d hi
  have hN : N.conjBy t = N := mem_normalizer_iff_map_conj_eq.mp (hTN ht)
  have hP : (N.pCoreIn 2).conjBy t = N.pCoreIn 2 := by
    change (N.pCoreIn 2).map (MulAut.conj t).toMonoidHom = _
    rw [map_pCoreIn_of_injective 2 _ _ (MulAut.conj t).injective]
    exact congrArg (fun H : Subgroup G => H.pCoreIn 2) hN
  have hNI : N ≤ I := residual_join_le_of_line_centralizer d e.source.minimal.1 c hL
  have hNIt : N ≤ I.conjBy t := by
    have hh := map_mono (f := (MulAut.conj t).toMonoidHom) hNI
    change N.conjBy t ≤ I.conjBy t at hh
    rwa [hN] at hh
  have hUS : U ≤ d.S := componentModule_le_sylow d e.source.minimal.1 c e.action
    e.source.sylow e.source.sylow_eq
  have hUtS : U.conjBy t ≤ d.S := by
    have hh := map_mono (f := (MulAut.conj t).toMonoidHom) hUS
    change U.conjBy t ≤ d.S.conjBy t at hh
    rwa [hS] at hh
  have hUN : U ≤ N := hUS.trans le_sup_right
  have hUtN : U.conjBy t ≤ N := hUtS.trans le_sup_right
  have hnU : N ≤ normalizer (U : Set G) := hNI.trans e.action.normalizes
  let conjugateAction :=  e.action.conjugate t
  have hnUt : N ≤ normalizer (U.conjBy t : Set G) := hNIt.trans conjugateAction.normalizes
  have hfk := e.action.restrictActor_kernel N hNI hUN
  have hgk := conjugateAction.restrictActor_kernel N hNIt hUtN
  have hfka : (e.action.restrictActor N hNI).ker = actionCentralizer N U :=
    hfk.trans (NaturalEightAction.restricted_centralizer N hUN)
  have hgka : (conjugateAction.restrictActor N hNIt).ker = actionCentralizer N (U.conjBy t) :=
    hgk.trans (NaturalEightAction.restricted_centralizer N hUtN)
  obtain ⟨hCU,hCV,hgen⟩ := e.source_core_generation hL t ht htS
  have hfS : (e.action.restrictActor N hNI).ker ≤ d.S.subgroupOf N := by
    rw [hfka]
    intro x hx
    exact hCU ⟨x.property,hx⟩
  have hgS : (conjugateAction.restrictActor N hNIt).ker ≤ d.S.subgroupOf N := by
    rw [hgka]
    intro x hx
    exact hCV ⟨x.property,hx⟩
  have hgen' : pCore 2 N = (e.action.restrictActor N hNI).ker ⊔
      (conjugateAction.restrictActor N hNIt).ker := by rwa [hfka,hgka]
  obtain ⟨hdis,_,hcomm,_⟩ := e.source_conjugate_product hL t ht htS
  let := e.action.elementary
  let := conjugateAction.elementary
  refine {
    t_mem := ht
    t_outside := htS
    preserves_S := hS
    preserves_J := hN
    preserves_P := hP
    local_le := hNI
    local_le_conjugate := hNIt
    first_le := hUS
    second_le := hUtS
    first_normal := normal_subgroupOf_of_le_normalizer hnU
    second_normal := normal_subgroupOf_of_le_normalizer hnUt
    first_elementary := IsElementaryAbelian.comap_of_injective N.subtype N.subtype_injective U
    second_elementary := IsElementaryAbelian.comap_of_injective N.subtype N.subtype_injective (U.conjBy t)
    commutes := ?_
    disjoint := ?_
    action := e.action
    conjugateAction := conjugateAction
    first_kernel := hfk
    second_kernel := hgk
    first_kernel_le := hfS
    second_kernel_le := hgS
    core_product := ?_ }
  · intro v hv u hu
    apply Subtype.ext
    exact (hcomm hu v hv).symm
  · apply disjoint_iff.mpr
    apply _root_.eq_bot_iff.mpr
    intro x hx
    apply mem_bot.mpr
    apply Subtype.ext
    exact mem_bot.mp (disjoint_iff.mp hdis ▸ And.intro hx.1 hx.2)
  · refine ⟨?_,?_⟩
    · rw [MonoidHom.ker_prod,hgen']
      exact inf_le_left.trans le_sup_left
    · dsimp only
      rw [inf_eq_right.mpr hfS,inf_eq_right.mpr hgS,←Subgroup.map_sup,←hgen']

end EndNodeData
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
