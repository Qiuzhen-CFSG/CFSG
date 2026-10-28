module
public import CFSG.Quasithin.Chapter5.RankOneBaumannSourceAlternatives
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.FiveBlockSource.ExternalCharacteristic
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.Source.Transport
public import Theory.GroupTheory.PResidual.SubnormalCoreAction

/-!
# The original alternating block forced by Baumann escape

The five-point section on [W,L] identifies the actual component quotient
and supplies the C.1.24 characteristic-pair argument. Uniqueness over LT
excludes both characteristic-subgroup alternatives. The surviving block
is the original L, and its two-core support is exactly [W,L].

This is the block-construction step of 5.1.7(1); the crossing argument and
its earlier uniqueness over L are still required for the normalizer bound.
Source: Aschbacher--Smith 5.1.7(1), p.633, using E.2.3(4).
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open ChapterC ChapterC.RankOne ChapterC.RankOne.FiveBlockSource
open ChapterC.RankOne.ChiProduct.SelectedRankOne
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L W : Subgroup G} {n : ℕ}
attribute [local instance] ChapterB.RankOneBaumann.semilinear_moved_elementary

/-- Escape forces the original component to be an alternating block with
support the original moved module. No chosen module or flag is used. -/
theorem Input.alternating_block_of_baumann_escape
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hout : ¬normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G)) :
    IsBlock (L.subgroupOf (L ⊔ (T : Subgroup G))) ∧ IsAlternatingBlock L 5 ∧
      (blockU L).map L.subtype = ⁅W,L⁆ ∧
      L = ⁅L,elementaryAbelianMaxJ (T : Subgroup G)⁆ := by
  let H := L ⊔ (T : Subgroup G)
  let A := L.subgroupOf H
  let U := W.subgroupOf H
  let := h.reduced_internal.normal
  let := h.reduced_internal.elementary
  let V := ⁅U,pResidual 2 H⁆
  let R := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  let : A.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer h.sylow_normalizes)
  have hr : IsPReduced 2 V := h.reduced_internal.moved U
  have hVmap : V.map H.subtype = ⁅W,L⁆ := h.local_moved_map
  have hAmap : A.map H.subtype = L := map_subgroupOf_eq_of_le le_sup_left
  have hres : pResidual 2 H = A :=
    (map_injective H.subtype_injective) (h.local_residual_eq.trans hAmap.symm)
  obtain ⟨q,hq,hk,f,hf,he,hfk⟩ := h.five_section_of_baumann_escape hout
  change q.ker = centralizer (V : Set H) at hk
  have hAq : A.map q = alternatingGroup (Fin 5) := by
    rw [←hres]
    exact ChapterC.SymmetricFive.source_residual_image q hq
  let e : A ≃* L := subgroupOfEquivOfLe (show L ≤ H from le_sup_left)
  let eqv : (A ⧸ pCore 2 A) ≃* (L ⧸ pCore 2 L) :=
    QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  let := h.quotient_quasisimple
  let : IsQuasisimple (A ⧸ pCore 2 A) := IsQuasisimple.of_mulEquiv eqv.symm
  have hzA : center (A ⧸ pCore 2 A) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    exact eqv.map_eq_one_iff.mp
      (h.quotient_center_eq_bot.le ((centerCongr eqv) ⟨x,hx⟩).property)
  have hmA : ⁅V,A⁆ ≠ ⊥ := by
    intro hz
    apply h.commutator_input.noncentral
    have hh := congrArg (map H.subtype) hz
    simpa only [map_commutator,hVmap,hAmap,Subgroup.map_bot] using hh
  have hkA : (q.subgroupMap A).ker = pCore 2 A := by
    calc (q.subgroupMap A).ker = (centralizer (V : Set H)).subgroupOf A := by
           rw [Subgroup.ker_subgroupMap,hk]
         _ = ((QuotientGroup.mk' (centralizer (V : Set H))).subgroupMap A).ker := by
           rw [Subgroup.ker_subgroupMap,QuotientGroup.ker_mk']
         _ = pCore 2 A := reduced_quasisimple_subgroupMap_ker V A hr hzA hmA
  let eL : (A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 5) :=
    ((QuotientGroup.quotientMulEquivOfEq hkA.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (q.subgroupMap A)
        (q.subgroupMap_surjective A))).trans (MulEquiv.subgroupCongr hAq)
  have hfit : generalizedFitting H = pCore 2 H :=
    generalizedFitting_eq_pCore_of_selfCentralizing 2
      (centralizer_pCore_sup_le 2 L (T : Subgroup G)
        (by rw [←h.local_mem.2.2.2.1]; exact centralizer_generalizedFitting_le L)
        T.isPGroup' h.sylow_normalizes)
  have hRmap : (R : Subgroup H).map H.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le le_sup_right
  have hprod : A ⊔ (R : Subgroup H) = ⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup,hAmap,hRmap,←MonoidHom.range_eq_map,range_subtype]
  have hJR : ¬elementaryAbelianMaxJ (R : Subgroup H) ≤ centralizer (V : Set H) := by
    intro hc
    apply hout
    apply Chapter5.RankOneBaumannSource.baumann_normalizer_of_thompson_centralizes
      h.qtke h.maximal_local h.sylow_normalizes h.commutator_reduced.1
      h.commutator_input.reduced_internal h.quotient_center_eq_bot
      h.commutator_input.noncentral
    have hjm : (elementaryAbelianMaxJ (R : Subgroup H)).map H.subtype =
        elementaryAbelianMaxJ (T : Subgroup G) := by
      rw [←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,hRmap]
    rw [←hjm,←hVmap]
    rintro x ⟨x,hx,rfl⟩ v ⟨v,hv,rfl⟩
    exact congrArg H.subtype (hc hx v hv)
  have hTne : (T : Subgroup G) ≠ ⊥ := by
    intro hz
    exact h.maximal_local.1.2.2 (bot_unique
      ((pCoreIn_le_sylow H R).trans_eq (hRmap.trans hz)))
  obtain ⟨D,hD⟩ := exists_baumann_universal_pair.{u,u} (T : Subgroup G) T.isPGroup' hTne
  have hno (C : Subgroup (ChapterB.baumann (T : Subgroup G)))
      (hc : C.Characteristic) (hne : C ≠ ⊥) :
      ¬H ≤ normalizer (C.map (ChapterB.baumann (T : Subgroup G)).subtype : Set G) := by
    intro hn
    exact hne (Chapter5.RankOneBaumannSource.characteristic_baumann_eq_bot_of_escape
      h.qtke h.maximal_local h.sylow_normalizes hout C hc
      (normal_subgroupOf_of_le_normalizer hn))
  have hfix : ∀ v, f v = 0 → ∀ g ∈ alternatingGroup (Fin 5),
      NormalElementaryQuotient.representation V q hq hk g v = v := by
    intro v hv g hg
    have hvf : v ∈ fixedSpace (NormalElementaryQuotient.representation V q hq hk)
        ((pResidual 2 H).map q) := hfk ▸ hv
    exact (mem_fixedSpace_iff _ _ v).mp hvf g
      ((ChapterC.SymmetricFive.source_residual_image q hq).symm ▸ hg)
  rcases external_normal_source_conclusion (T : Subgroup G) H R
      (hRmap ▸ inf_le_left) hRmap.le hfit A h.maximal_local.1.1 hprod eL
      V q hq hk hAq f hf he hfix hJR D hD with hfirst | hsecond | hb
  · exact (hno D.first D.first_characteristic D.first_ne_bot hfirst).elim
  · exact (hno D.second D.second_characteristic D.second_ne_bot hsecond).elim
  · obtain ⟨hb,ha,hm,hs,_⟩ := hb
    have hsame : (blockU A).map (H.subtype.comp A.subtype) =
        (blockU L).map L.subtype := by
      rw [←RankOne.Solvable.blockU_map_equiv e,map_map]
      rfl
    have hcomm : ⁅⁅W,L⁆,L⁆ = ⁅W,L⁆ := by
      let := h.reduced.2.1
      exact commutator_isPPerfect_idempotent L W h.local_mem.2.2.1
        (IsElementaryAbelian.isPGroup 2 W) (le_sup_left.trans (reduced_normalizes h.reduced))
    rw [hAmap] at hm
    rw [hsame,hVmap,hAmap,hcomm] at hs
    exact ⟨hb,RankOne.Solvable.isAlternatingBlock_of_equiv e ha,hs,hm⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
