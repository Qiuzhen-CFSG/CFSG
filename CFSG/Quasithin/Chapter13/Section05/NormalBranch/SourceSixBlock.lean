module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceSixShort

/-!
# The original A₆ block in source13.5.15(4)

The original natural action descends through the actual two-core quotient.
Its representative-level coordinate identity constructs the block module
model after the proved commutator-layer and shortness results. The final
consumer chooses the original A₅ pair internally: no block, core-collapse,
or recognition conclusion is assumed.

Source: Aschbacher–Smith,13.5.15(4), printed p.920.
-/

@[expose] public section
open Subgroup BinaryPermutation
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceSixBlock
open Section08.SourceCompletion
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open PlaneGeometry.TwoBlocks
open ChapterC
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)

noncomputable def actor : D.L→*alternatingGroup (Fin 6) :=
  d.local_quotient.toMonoidHom.comp (QuotientGroup.mk' _)

theorem actor_surjective : Function.Surjective (actor d) :=
  d.local_quotient.surjective.comp (QuotientGroup.mk'_surjective _)

theorem actor_ker (e : (D.L ⧸ pCore 2 D.L)≃*alternatingGroup (Fin 6)) :
    (actor d).ker=pCore 2 D.L := by
  rw [←SourceBarred.local_kernel_eq_core d e]
  ext l
  change actor d l=1↔(actor d l).val=1
  exact Subtype.ext_iff

noncomputable def quotientEquiv
    (e : (D.L ⧸ pCore 2 D.L)≃*alternatingGroup (Fin 6)) :
    (D.L ⧸ pCore 2 D.L)≃*alternatingGroup (Fin 6) :=
  (QuotientGroup.quotientMulEquivOfEq (actor_ker d e).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (actor d) (actor_surjective d))

theorem quotientEquiv_mk (e : (D.L ⧸ pCore 2 D.L)≃*alternatingGroup (Fin 6)) (l : D.L) :
    quotientEquiv d e (QuotientGroup.mk' (pCore 2 D.L) l)=actor d l := rfl

noncomputable def layerEquiv (hB : (blockU D.L).map D.L.subtype=D.V) :
    blockU D.L≃*Multiplicative (natural (Fin 6)) :=
  (((blockU D.L).equivMapOfInjective D.L.subtype D.L.subtype_injective).trans
    (MulEquiv.subgroupCongr hB)).trans d.coordinate

theorem layerEquiv_equivariant (hB : (blockU D.L).map D.L.subtype=D.V)
    (l : D.L) (u : blockU D.L) :
    (layerEquiv d hB (blockConjugate D.L l u)).toAdd=
      alternatingNaturalRepresentation (Fin 6) (actor d l) (layerEquiv d hB u).toAdd := by
  exact d.conjugation l ⟨u.val.val,hB ▸ mem_map_of_mem D.L.subtype u.property⟩

noncomputable def moduleEquiv (hB : (blockU D.L).map D.L.subtype=D.V)
    (hF : blockFixed D.L=⊥) :
    BlockModule D.L≃*Multiplicative (natural (Fin 6)) :=
  ((QuotientGroup.quotientMulEquivOfEq hF).trans QuotientGroup.quotientBot).trans (layerEquiv d hB)

theorem moduleEquiv_mk (hB : (blockU D.L).map D.L.subtype=D.V)
    (hF : blockFixed D.L=⊥) (u : blockU D.L) :
    moduleEquiv d hB hF (QuotientGroup.mk' (blockFixed D.L) u)=layerEquiv d hB u := rfl

noncomputable def blockModel (e : (D.L ⧸ pCore 2 D.L)≃*alternatingGroup (Fin 6))
    (hB : (blockU D.L).map D.L.subtype=D.V) (hF : blockFixed D.L=⊥) :
    BlockModuleModel D.L ((naturalMulAction (Fin 6)).comp (alternatingGroup (Fin 6)).subtype) where
  quotientIso := quotientEquiv d e
  moduleIso := moduleEquiv d hB hF
  intertwining l u := by
    apply Multiplicative.toAdd.injective
    rw [moduleEquiv_mk,moduleEquiv_mk,quotientEquiv_mk]
    exact layerEquiv_equivariant d hB l u

include d in
theorem alternatingBlock (e : (D.L ⧸ pCore 2 D.L)≃*alternatingGroup (Fin 6))
    (hS : IsShort D.L) (hB : (blockU D.L).map D.L.subtype=D.V)
    (hF : blockFixed D.L=⊥) : IsAlternatingBlock D.L 6 := by
  exact ⟨by decide,hS,(naturalMulAction (Fin 6)).comp (alternatingGroup (Fin 6)).subtype,
    ⟨blockModel d e hB hF⟩,fun _ _=>rfl⟩

include d in
theorem source13_5_15_four (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L)≃*alternatingGroup (Fin 6))
    (hseed : D.Vplus=⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
    (hU : ¬IsMulCommutative D.UH) : IsAlternatingBlock D.L 6 ∧
      (blockU D.L).map D.L.subtype=D.V ∧ blockFixed D.L=⊥ := by
  obtain ⟨a,g,_,_,hK,hL,_,_,_,hi,hS⟩ :=
    SourceCoreCollapse.exists_original_collapsed_pair d h e hseed hn hU
  have hB := SourceSixLayer.block_layer_eq_module d h e hseed hn hU g hK hL a hi hS
  have hfull : ⁅D.V,D.L⁆=D.V := by
    apply le_antisymm (le_normalizer_iff_commutator_le_left.mp (le_sup_left.trans d.normalizes_V))
    exact (SourceFiveSpan.module_commutator d hK a hi h hL hseed).symm.le.trans
      (commutator_mono le_rfl hK)
  have hF : blockFixed D.L=⊥ := by
    apply map_injective (blockU D.L).subtype_injective
    rw [blockFixed_map,SourceSixShort.fixed_inf_bot d g hK a hi hB h hfull,Subgroup.map_bot]
  exact ⟨alternatingBlock d e (SourceSixShort.short d g hK a hi hB h e hfull) hB hF,hB,hF⟩

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceSixBlock
end
