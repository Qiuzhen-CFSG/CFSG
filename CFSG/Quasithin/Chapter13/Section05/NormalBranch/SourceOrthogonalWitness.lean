module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceOrthogonal

/-!
# The actual cubic and singular involution in the orthogonal image

The injective original starred action sends L₁* to an order-three subgroup
normalized by the whole H* image. The actual V action supplies a nonidentity
singular involution centralizing that subgroup, using [V,L₁]=V₃≤Q_H.
These are literal inputs to the finite orthogonal cubic-normalizer theorem.

Source: Aschbacher–Smith13.5.15, printed p.920.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceOrthogonalWitness
open Section08.SourceCompletion
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open PlaneGeometry.TwoBlocks
open SourceOrthogonal
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
  (h : D.Hypothesis) (e : (D.L ⧸ pCore 2 D.L)≃*alternatingGroup (Fin 6))
  (hseed : D.Vplus=⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
  (hU : ¬IsMulCommutative D.UH)

noncomputable def localCubic : Subgroup BinaryFourPlus.Wreath :=
  (Section08.Source.starImage D.H D.L₁).map (starEmbedding d h e hseed hn hU)

theorem localCubic_card : Nat.card (localCubic d h e hseed hn hU)=3 := by
  rw [localCubic,card_map_of_injective (starEmbedding_injective d h e hseed hn hU)]
  obtain ⟨f⟩ := SourceStar.original_star_cyclic d h e hn
  rw [Nat.card_congr f.toEquiv]
  simp only [Nat.card_eq_fintype_card,Fintype.card_multiplicative,ZMod.card]

theorem range_normalizes_local : (starEmbedding d h e hseed hn hU).range≤
    normalizer (localCubic d h e hseed hn hU:Set BinaryFourPlus.Wreath) := by
  let : (D.L₁.subgroupOf D.H).Normal := hn
  let : (Section08.Source.starImage D.H D.L₁).Normal :=
    Normal.map hn (QuotientGroup.mk' (pCore 2 D.H)) (QuotientGroup.mk'_surjective _)
  simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,localCubic] using
    (Section08.Source.starImage D.H D.L₁).le_normalizer_map (starEmbedding d h e hseed hn hU)

theorem module_actor_centralizes_local (v : D.V) :
    starEmbedding d h e hseed hn hU (QuotientGroup.mk' (pCore 2 D.H) (inclusion h.V_le_H v))∈
      centralizer (localCubic d h e hseed hn hU:Set BinaryFourPlus.Wreath) := by
  rintro _ ⟨_,⟨l,hl,rfl⟩,rfl⟩
  let vH := inclusion h.V_le_H v
  have hc : ⁅vH,l⁆∈pCore 2 D.H := by
    have hm : (⁅vH,l⁆:D.H).val∈D.QH :=
      h.UH_le_QH (le_conjugateSpanBy _ _ (hseed.symm ▸ commutator_mem_commutator v.property hl))
    exact (show D.QH.subgroupOf D.H=pCore 2 D.H from
      comap_map_eq_self_of_injective D.H.subtype_injective _) ▸ hm
  let π := QuotientGroup.mk' (pCore 2 D.H)
  have hh : π vH * π l=π l * π vH := by
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [←map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr hc
  simpa only [map_mul] using (congrArg (starEmbedding d h e hseed hn hU) hh).symm

include d h e hseed hn hU in
theorem exists_original_cubic_normalizer_witness :
    let f := starEmbedding d h e hseed hn hU
    let A := localCubic d h e hseed hn hU
    Function.Injective f ∧ Nat.card A=3 ∧ f.range≤normalizer (A:Set BinaryFourPlus.Wreath) ∧
    ∃s:BinaryFourPlus.Wreath,s∈f.range ∧ s≠1 ∧ s^2=1 ∧
      BinaryFourPlus.SingularDisplacements s ∧ s∈centralizer (A:Set BinaryFourPlus.Wreath) := by
  dsimp only
  have hvn := module_not_le_core h hU
  obtain ⟨v,hv,hvq⟩ := Set.not_subset.mp hvn
  let vV : D.V := ⟨v,hv⟩
  let vH := inclusion h.V_le_H vV
  let f := starEmbedding d h e hseed hn hU
  let x := QuotientGroup.mk' (pCore 2 D.H) vH
  have hx : x≠1 := by
    intro he
    exact hvq (mem_map_of_mem D.H.subtype ((QuotientGroup.eq_one_iff vH).mp he))
  have hs : f x≠1 := fun he=>hx ((starEmbedding_injective d h e hseed hn hU) (he.trans f.map_one.symm))
  have hv2 : vH^2=1 := by
    apply Subtype.ext
    let := h.elementary
    exact elemPow_eq_one_of_isElementaryAbelian v hv
  refine ⟨starEmbedding_injective d h e hseed hn hU,localCubic_card d h e hseed hn hU,
    range_normalizes_local d h e hseed hn hU,f x,⟨x,rfl⟩,hs,?_,
    module_actor_singular d h e hseed hn hU vV,module_actor_centralizes_local d h e hseed hn hU vV⟩
  rw [←map_pow]
  change f (QuotientGroup.mk' (pCore 2 D.H) vH^2)=1
  rw [←map_pow,hv2,map_one,map_one]

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceOrthogonalWitness
end
