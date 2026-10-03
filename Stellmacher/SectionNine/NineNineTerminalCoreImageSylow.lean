module
public import Stellmacher.SectionNine.NineInitialEdgeCoreProduct

/-!
# The penultimate-core image in the terminal quotient

For any supplied surjective homomorphism from the terminal stabilizer whose
kernel is exactly its two-core, the image of the penultimate core is a Sylow
two-subgroup. Under the terminal `SL₂(2) ≀ C₂` quotient model this image has
order eight. No choice of a replacement quotient or action is imposed on
the consumer.

Endpoint alignment transports the initial adjacent-core product to the
terminal edge. The initial edge is the distinguished Sylow, so its transported
edge is a two-group; (7.3) makes that entire edge a Sylow subgroup of the
terminal stabilizer. Mapping the product of its two cores kills the terminal
core and leaves precisely the penultimate-core image. For the cardinality
corollary, the supplied map and the model map have identical kernels, so their
codomains are isomorphic. The wreath product has order 72 and Sylow two-part 8.

Source: the adjacent-core product remark after Stellmacher (9.3), printed
p.50, and its terminal quotient use in (9.9), printed p.56/PDF p.46 of
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_nine_terminal_core_image_sylow
    {H G K : Type u} [Group H] [Finite H] [Group G] [Finite G] [Group K] [Finite K]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (f : GAt ctx.Γ ctx.criticalPath.a' →* K) (hsurj : Function.Surjective f)
    (hkernel : f.ker = pCore 2 (GAt ctx.Γ ctx.criticalPath.a')) :
    let penultimate := ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,
      Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
    ∃ sylow : Sylow 2 K, (sylow : Subgroup K) =
      ((QAt ctx.Γ penultimate).subgroupOf (GAt ctx.Γ ctx.criticalPath.a')).map f := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let penultimate := cp.path ⟨cp.length - 1,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let P := GAt Γ cp.a'
  let Qm := QAt Γ penultimate
  let Qt := QAt Γ cp.a'
  let edge := GAt Γ penultimate ⊓ P
  obtain ⟨alignment,halign,hterminal⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  let equiv := MulAut.conj alignment⁻¹
  have hQa : (QAt Γ cp.a).map equiv.toMonoidHom = Qm := by rw [← q_act,halign]
  have hQn : (QAt Γ cp.firstStep).map equiv.toMonoidHom = Qt := by rw [← q_act,hterminal]
  have hGa : (GAt Γ cp.a).map equiv.toMonoidHom = GAt Γ penultimate := by
    change conjugateBy (stabilizer Γ cp.a) alignment⁻¹ = _
    rw [← stabilizer_act,halign]
  have hGn : (GAt Γ cp.firstStep).map equiv.toMonoidHom = P := by
    change conjugateBy (stabilizer Γ cp.firstStep) alignment⁻¹ = _
    rw [← stabilizer_act,hterminal]
  have hinitial := (nine_initial_edge_core_product ctx hb).1
  have hedge : Qm ⊔ Qt = edge := by
    have hh := congrArg (fun J : Subgroup G => J.map equiv.toMonoidHom) hinitial
    rw [Subgroup.map_sup,Subgroup.map_inf _ _ _ equiv.injective,hQa,hQn,hGa,hGn] at hh
    exact hh
  have hTa : QAt Γ cp.a ≤ T := (local_cores_le_edge_sylow ctx.sectionSeven Γ cp).1
  have hTn : QAt Γ cp.firstStep ≤ T := (local_cores_le_edge_sylow ctx.sectionSeven Γ cp).2
  have hTedge : T = GAt Γ cp.a ⊓ GAt Γ cp.firstStep :=
    le_antisymm cp.S_le_edge_stabilizers (hinitial ▸ sup_le hTa hTn)
  obtain ⟨_,sylowInitial,hsylowInitial⟩ := (edge_sylow_data ctx.sectionSeven Γ cp).2
  have hTp : IsPGroup 2 T := by
    rw [← hsylowInitial]
    exact sylowInitial.isPGroup'.map _
  have hmapT : T.map equiv.toMonoidHom = edge := by
    rw [hTedge,Subgroup.map_inf _ _ _ equiv.injective,hGa,hGn]
  have hedgep : IsPGroup 2 edge := hmapT ▸ hTp.map equiv.toMonoidHom
  let edgeSylow : Sylow 2 edge := default
  have hedgeTop : (edgeSylow : Subgroup edge) = ⊤ :=
    (edgeSylow.is_maximal' (hedgep.to_subgroup ⊤) le_top).symm
  have hedgeAmbient : sylowTwoAmbient edge edgeSylow = edge := by
    rw [sylowTwoAmbient,hedgeTop,← MonoidHom.range_eq_map,Subgroup.range_subtype]
  have hterminalAdj : Γ.adjacent penultimate cp.a' := by
    have hh := cp.path_adj ⟨cp.length - 1,by have := cp.length_pos; omega⟩
    convert hh using 1
    · apply congrArg cp.path
      apply Fin.ext
      rfl
    · rw [← cp.path_end]
      apply congrArg cp.path
      apply Fin.ext
      simp
      have := cp.length_pos
      omega
  have hedgeSylow : IsSylowTwoIn edge P := by
    have hh := ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core penultimate cp.a'
      ((mem_neighborhood_iff_adjacent Γ).mpr hterminalAdj) edgeSylow).2.1
    change IsSylowTwoIn (sylowTwoAmbient edge edgeSylow) P at hh
    rwa [hedgeAmbient] at hh
  obtain ⟨hEdgeP,original,horiginal⟩ := hedgeSylow
  have hQmP : Qm ≤ P := (hedge ▸ le_sup_left).trans hEdgeP
  have hQtP : Qt ≤ P := (hedge ▸ le_sup_right).trans hEdgeP
  have hedgeNative : edge.subgroupOf P = (original : Subgroup P) := by
    rw [← horiginal]
    exact Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
  have hjoinNative : edge.subgroupOf P = Qm.subgroupOf P ⊔ Qt.subgroupOf P := by
    rw [← hedge,Subgroup.subgroupOf_sup hQmP hQtP]
  have hQtKer : Qt.subgroupOf P = f.ker := by
    rw [hkernel]
    change (Γ.twoCoreAt cp.a').subgroupOf P = _
    rw [Γ.twoCoreAt_def]
    exact Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
  have himage : (original : Subgroup P).map f = (Qm.subgroupOf P).map f := by
    have hzero : f.ker.map f = ⊥ := (Subgroup.map_eq_bot_iff _).mpr le_rfl
    rw [← hedgeNative,hjoinNative,Subgroup.map_sup,hQtKer,hzero,sup_bot_eq]
  exact ⟨original.mapSurjective hsurj,(Sylow.coe_mapSurjective hsurj original).trans himage⟩

public theorem nine_nine_terminal_core_image_card_eight
    {H G K : Type u} [Group H] [Finite H] [Group G] [Finite G] [Group K] [Finite K]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (f : GAt ctx.Γ ctx.criticalPath.a' →* K) (hsurj : Function.Surjective f)
    (hkernel : f.ker = pCore 2 (GAt ctx.Γ ctx.criticalPath.a'))
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a')
      (QAt ctx.Γ ctx.criticalPath.a') SL2TwoWreathC2) :
    let penultimate := ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,
      Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
    Nat.card (((QAt ctx.Γ penultimate).subgroupOf
      (GAt ctx.Γ ctx.criticalPath.a')).map f) = 8 := by
  let P := GAt ctx.Γ ctx.criticalPath.a'
  obtain ⟨sylow,hsylow⟩ := nine_nine_terminal_core_image_sylow ctx hb f hsurj hkernel
  obtain ⟨projection,hprojection,hmodelKernel⟩ := hmodel
  have hQ : (QAt ctx.Γ ctx.criticalPath.a').subgroupOf P = pCore 2 P := by
    change (ctx.Γ.twoCoreAt ctx.criticalPath.a').subgroupOf P = _
    rw [ctx.Γ.twoCoreAt_def]
    exact Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
  have hsame : f.ker = projection.ker := hkernel.trans (hQ.symm.trans hmodelKernel.symm)
  let equiv : K ≃* SL2TwoWreathC2 :=
    (QuotientGroup.quotientKerEquivOfSurjective f hsurj).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hsame).trans
        (QuotientGroup.quotientKerEquivOfSurjective projection hprojection))
  have hcardK : Nat.card K = 72 := by
    rw [Nat.card_congr equiv.toEquiv,RegularWreathProduct.card]
    have hsl : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) = 6 :=
      SectionOne.RankOneThreeGroupAssembly.isSL2Two_card ⟨MulEquiv.refl _⟩
    rw [hsl]
    norm_num [Nat.card_eq_fintype_card]
  dsimp only
  rw [← hsylow]
  change Nat.card sylow = 8
  rw [sylow.card_eq_multiplicity,hcardK]
  decide +kernel

end Stellmacher.SectionNine
