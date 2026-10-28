module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureInnerCoreIndex
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixActionKernel
public import Theory.Representation.HexacodeAction.ChiefCentralization
public import CFSG.Quasithin.ChapterC.Section01.BlockDefs

/-!
# The original whole core commutator in the inner branch

The actual KT action has a two-group kernel. The closure induces its marked
even Klein four and has at most one dimension of displacement on every
chief interval above U. The involution bound centralizes all those intervals;
two-perfectness then yields [O2(KT),K]=U and the literal block module U(K)=U.

Source: Aschbacher--Smith 12.7.16, printed p.844.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterB.QuasisimpleSource Atlas.Codes
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- Every original core chief layer above U is central; the unchanged
whole U is exactly the component's block commutator module. -/
theorem original_tripleSix_central_closure_inner_block_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z:G)} : Set G))
    (hnot : ¬ U ≤ (centralizer ({(z:G)} : Set G)).pCoreIn 2)
    (hinner : inducedAutomizer U (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z:G)} : Set G)))) ≤ inducedAutomizer U K) :
    ⁅(K ⊔ (T : Subgroup G)).pCoreIn 2,K⁆=U ∧ (ChapterC.blockU K).map K.subtype=U := by
  let M := K ⊔ (T : Subgroup G)
  let Q := M.pCoreIn 2
  let W := conjugateSpanBy (tripleSixPoint D a z) (conjugateSpanBy U (centralizer ({(z:G)} : Set G)))
  have hTU := ((structural K h).2.2 U D).1
  have hMU : M≤normalizer (U : Set G) := sup_le D.normalizes hTU
  have hWT : W≤(T : Subgroup G) :=
    (original_tripleSix_central_closure_automizer h structural D a z hz hzT hnot).1
  have hWM : W≤M := hWT.trans le_sup_right
  have hUM : U≤M := D.le_component.trans le_sup_left
  obtain ⟨f,hf,hfk,hK,_⟩ := original_tripleSix_full_automizer h structural D a
  let α := U.normalizerMonoidHom.rangeRestrict.comp (inclusion hMU)
  let π := f.comp α
  have hmap (X : Subgroup G) (hX : X≤M) :
      (X.subgroupOf M).map π=(inducedAutomizer U X).map f := by
    apply le_antisymm
    · rintro _ ⟨m,hm,rfl⟩
      exact ⟨α m,⟨⟨m,hMU m.property⟩,hm,rfl⟩,rfl⟩
    · rintro _ ⟨_,⟨m,hm,rfl⟩,rfl⟩
      exact ⟨⟨m,hX hm⟩,hm,rfl⟩
  have hE : hexSign.ker≤π.range := by
    rw [←hK,←hmap K le_sup_left]
    exact map_le_range _ _
  have hk : π.ker≤pCore 2 M := by
    intro g hg
    have hα : α g=1 := hf (hg.trans (map_one f).symm)
    have hnorm : (⟨g,hMU g.property⟩ : normalizer (U : Set G))∈U.normalizerMonoidHom.ker :=
      congrArg Subtype.val hα
    rw [normalizerMonoidHom_ker] at hnorm
    have hm := (original_tripleSix_action_kernel h structural D a).1 ⟨g.property,hnorm⟩
    change g∈((pCore 2 M).map M.subtype).comap M.subtype at hm
    rwa [comap_map_eq_self_of_injective M.subtype_injective] at hm
  have hp : IsPGroup 2 π.ker := pCore_isPGroup.to_le hk
  let A := W.subgroupOf M
  have hAE : A.map π≤hexSign.ker := by
    rw [hmap W hWM,←hK]
    exact map_mono hinner
  have hcard : Nat.card (A.map π)=4 := by
    rw [hmap W hWM,card_map_of_injective hf]
    exact (original_tripleSix_central_closure_inner_intersections
      h structural D a z hz hzT hnot hinner).2.2.1
  obtain ⟨b,hbo⟩ := exists_prime_orderOf_dvd_card' (G:=A.map π) 2 (by rw [hcard]; decide)
  let t : HexEvenAutomorphisms := ⟨b,hAE b.property⟩
  have ht : orderOf t=2 := by
    rw [Subgroup.orderOf_mk]
    exact (Subgroup.orderOf_coe b).trans hbo
  let Z := U.subgroupOf M
  let B := (Q ⊓ W).subgroupOf M
  let L := K.subgroupOf M
  let : Z.Normal := normal_subgroupOf_of_le_normalizer hMU
  let : L.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le K.le_normalizer D.sylow_normalizes_component)
  have hUQ : U≤Q := D.le_componentCore.trans (pCoreIn_mono_of_normalizes le_sup_left
    (sup_le K.le_normalizer D.sylow_normalizes_component))
  have hZQ : Z≤pCore 2 M := by
    intro u hu
    have hm := hUQ hu
    change u∈((pCore 2 M).map M.subtype).comap M.subtype at hm
    rwa [comap_map_eq_self_of_injective M.subtype_injective] at hm
  have hci := original_tripleSix_central_closure_inner_core_index h structural D a z hz hzT hnot hinner
  change (Nat.card (Q ⊓ W : Subgroup G)=4 ∨ Nat.card (Q ⊓ W : Subgroup G)=8) ∧
    U.relIndex (Q ⊓ W)≤2 ∧ ⁅Q,W⁆≤Q ⊓ W at hci
  have hcomm : ⁅pCore 2 M,A⁆≤B := by
    apply (map_le_map_iff_of_injective M.subtype_injective).mp
    rw [map_commutator,map_subgroupOf_eq_of_le hWM,
      map_subgroupOf_eq_of_le (inf_le_left.trans (pCoreIn_le 2 M))]
    exact hci.2.2
  have hidx : Z.relIndex B≤2 := by
    have hh := relIndex_map_map_of_injective Z B M.subtype_injective
    rw [map_subgroupOf_eq_of_le hUM,
      map_subgroupOf_eq_of_le (inf_le_left.trans (pCoreIn_le 2 M))] at hh
    exact hh.symm ▸ hci.2.1
  have hc := Hexacode.residual_commutator_le_of_displacement_index_two
    π hE hp (pCore 2 M) Z pCore_isPGroup hZQ A B hAE t ht b.property hcomm hidx
  have hgen : L ⊔ (T : Subgroup G).subgroupOf M=⊤ := by
    rw [←subgroupOf_sup (show K≤M from le_sup_left) (show (T : Subgroup G)≤M from le_sup_right),subgroupOf_self]
  have hLp : IsPPerfect 2 L := h.maximal_faithful.2.1.2.1.of_surjective
    (subgroupOfEquivOfLe (show K≤M from le_sup_left)).symm.toMonoidHom
    (subgroupOfEquivOfLe (show K≤M from le_sup_left)).symm.surjective
  rw [pResidual_eq_of_isPPerfect_sup L ((T : Subgroup G).subgroupOf M) hLp
    T.isPGroup'.comap_subtype hgen] at hc
  have hbound : ⁅Q,K⁆≤U := by
    have hh := map_mono (f:=M.subtype) hc
    dsimp only [L,Z] at hh
    rw [map_commutator,map_subgroupOf_eq_of_le (show K≤M from le_sup_left),
      map_subgroupOf_eq_of_le hUM] at hh
    exact hh
  have he : ⁅Q,K⁆=U := le_antisymm hbound
    (by rw [D.eq_commutator]; exact commutator_mono hUQ le_rfl)
  have hKQ : K.pCoreIn 2≤Q := pCoreIn_mono_of_normalizes le_sup_left
    (sup_le K.le_normalizer D.sylow_normalizes_component)
  have heK : ⁅K.pCoreIn 2,K⁆=U := le_antisymm ((commutator_mono hKQ le_rfl).trans hbound)
    (by rw [D.eq_commutator]; exact commutator_mono D.le_componentCore le_rfl)
  refine ⟨he,?_⟩
  simpa only [ChapterC.blockU,pCoreIn,map_commutator,←MonoidHom.range_eq_map,range_subtype] using heK

end CFSG.Quasithin.Chapter12.Section07
