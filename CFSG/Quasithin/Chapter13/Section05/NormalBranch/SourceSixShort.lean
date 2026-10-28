module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceSixLayer

/-!
# Shortness of the original six-point subgroup

Once its block layer has been identified with V, irreducibility follows by
restriction to the selected A₅ pair. Characteristic two, two-perfection,
and the original Sylow centralizer identity supply the remaining short-group
conditions. This is the structural step in source13.5.15(4), printed p.920.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceSixShort
open Section08.SourceCompletion
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open PlaneGeometry.TwoBlocks
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
  (g : D.L) (hK : NormalBranch.K D g.val≤D.L)
  (a : alternatingGroup (Fin 6))
  (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d)=
    FivePair.five.map (MulAut.conj a.val).toMonoidHom)
  (hB : (ChapterC.blockU D.L).map D.L.subtype=D.V)
include d hK a hi hB

theorem block_invariant (N : Subgroup D.L) (hn : N.Normal) (hN : N≤ChapterC.blockU D.L) :
    N=⊥∨N=ChapterC.blockU D.L := by
  have hNV : N.map D.L.subtype≤D.V := (map_mono hN).trans_eq hB
  have hLN : D.L≤normalizer (N.map D.L.subtype:Set G) := by
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using N.le_normalizer_map D.L.subtype
  rcases SourceFiveSpan.invariant_subgroup d hK a hi _ hNV (hK.trans hLN) with hz|he
  · left
    apply map_injective D.L.subtype_injective
    simpa only [Subgroup.map_bot] using hz
  · right
    exact map_injective D.L.subtype_injective (he.trans hB.symm)

omit d hK a hi in
theorem block_ne_bot (h : D.Hypothesis) : ChapterC.blockU D.L≠⊥ := by
  intro he
  have hv := hB
  rw [he,Subgroup.map_bot] at hv
  have hz : D.V₁=⊥ := le_bot_iff.mp ((h.point_lt.le.trans h.plus_le).trans hv.ge)
  have hc := h.point_card
  rw [hz,card_bot] at hc
  contradiction

theorem fixed_inf_bot (h : D.Hypothesis)
    (hfull : ⁅D.V,D.L⁆=D.V) : ChapterC.blockU D.L⊓center D.L=⊥ := by
  rcases block_invariant d g hK a hi hB (ChapterC.blockU D.L⊓center D.L) inferInstance inf_le_left with hz|he
  · exact hz
  · have hVC : D.V≤centralizer (D.L:Set G) := by
      rw [←hB,←he]
      rintro _ ⟨v,hv,rfl⟩ l hl
      exact congrArg Subtype.val (mem_center_iff.mp hv.2 ⟨l,hl⟩)
    have hz : D.V=⊥ := hfull.symm.trans (commutator_eq_bot_iff_le_centralizer.mpr hVC)
    have hc := h.point_card
    have hp : D.V₁=⊥ := le_bot_iff.mp ((h.point_lt.le.trans h.plus_le).trans_eq hz)
    rw [hp,card_bot] at hc
    contradiction

theorem short (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L)≃*alternatingGroup (Fin 6))
    (hfull : ⁅D.V,D.L⁆=D.V) : ChapterC.IsShort D.L := by
  let eV : ChapterC.blockU D.L≃*D.V :=
    ((ChapterC.blockU D.L).equivMapOfInjective D.L.subtype D.L.subtype_injective).trans
      (MulEquiv.subgroupCongr hB)
  let : IsElementaryAbelian 2 (ChapterC.blockU D.L) := by
    let : IsElementaryAbelian 2 D.V := h.elementary
    exact IsElementaryAbelian.of_injective eV.toMonoidHom eV.injective
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsQuasisimple (alternatingGroup (Fin 6)) := {
    toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    simple := ((QuotientGroup.quotientMulEquivOfEq
      (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }
  refine {
    finite := inferInstance
    twoPerfect := (pResidual_eq_top_iff 2 D.L).mp h.residual
    fitting := h.characteristic_L
    elementary := inferInstance
    central := ?_
    quotient := Or.inl (IsQuasisimple.of_mulEquiv e.symm)
    irreducible := ?_ }
  · intro u hu x hx
    apply Subtype.ext
    have hc : x.val∈centralizer (D.V:Set G) :=
      (h.sylow_centralizer.symm.le (SourcePairResidual.local_core_le_LT_core h
        (mem_map_of_mem D.L.subtype hx))).2
    exact (hc u.val (hB ▸ mem_map_of_mem D.L.subtype hu)).symm
  · rw [ChapterC.BlockModuleIrreducible,fixed_inf_bot d g hK a hi hB h hfull]
    exact ⟨bot_lt_iff_ne_bot.mpr (block_ne_bot hB h),
      fun N hn _ hN => block_invariant d g hK a hi hB N hn hN⟩

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceSixShort
end
