module
public import Stellmacher.SectionNine.NineFourAuxiliaryCore
public import Theory.GroupTheory.IndexTwoConjugateCore
public import Theory.GroupAction.SubgroupQuotientFullAction

/-!
# The literal quotient action in the central case of (9.4)

For the literal auxiliary group F, let N=Q_a intersect Q_next and let
Qstar be the intersection of all F-conjugates of N. The quotient
Q_next/Qstar is elementary abelian of exponent two, and F has its actual
conjugation action on this quotient. The theorem retains the normality
witness and the action formula on quotient representatives.

The initial edge-core product theorem gives index two for N in Q_next.
Every conjugate of N is normal of index two in Q_next, so the generic
index-two conjugate-core theorem gives invariance and an elementary
quotient. The existing quotient-conjugation construction supplies the
literal action. This construction needs no all-central hypothesis and
makes no assertion yet about faithfulness or the image being SL₂(2).

Source: Stellmacher (9.4), printed pp.51–52, the action on Q_next/Qstar
in the all-central case, in refs/files/stellmacher-n-group.pdf.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_four_central_core_quotient_action
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A0 B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A0 B)
    (hb : 1 < ctx.criticalPath.length)
    (remote : ctx.Γ.Vertex)
    (actor : G) (hactor : actor ∈ GAt ctx.Γ ctx.criticalPath.firstStep) :
    let F := (QAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ remote) ⊔
      Subgroup.zpowers actor
    let K := QAt ctx.Γ ctx.criticalPath.firstStep
    let N := QAt ctx.Γ ctx.criticalPath.a ⊓ K
    let C := ⨅ mover : F, N.map (MulAut.conj (mover : G)).toMonoidHom
    ∃ hN : (C.subgroupOf K).Normal,
      let _ := hN
      IsElementaryAbelian 2 (K ⧸ C.subgroupOf K) ∧
      ∃ action : F →* MulAut (K ⧸ C.subgroupOf K),
        ∀ mover : F, ∀ point : K,
          ∃ hconj : (mover : G) * (point : G) * (mover : G)⁻¹ ∈ K,
            action mover (QuotientGroup.mk' (C.subgroupOf K) point) =
              QuotientGroup.mk' (C.subgroupOf K)
                ⟨(mover : G) * (point : G) * (mover : G)⁻¹, hconj⟩ := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let Qa := QAt Γ cp.a
  let K := QAt Γ cp.firstStep
  let F := (Qa ⊓ QAt Γ remote) ⊔ Subgroup.zpowers actor
  let N := Qa ⊓ K
  let C := ⨅ mover : F, N.map (MulAut.conj (mover : G)).toMonoidHom
  have hFK : F ≤ Subgroup.normalizer K :=
    (nine_four_auxiliary_core_geometry ctx hb remote actor hactor).1.trans
      (stabilizer_le_normalizer_q Γ cp.firstStep)
  have hNK : N ≤ K := inf_le_right
  have hindex : N.relIndex K = 2 := by
    have hproduct := nine_initial_edge_core_product ctx hb
    have hQaEdge : Qa ≤ GAt Γ cp.a ⊓ GAt Γ cp.firstStep :=
      (local_cores_le_edge_sylow ctx.sectionSeven Γ cp).1.trans cp.S_le_edge_stabilizers
    have hcount := (Qa.subgroupOf (GAt Γ cp.a ⊓ GAt Γ cp.firstStep)).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQaEdge).toEquiv] at hcount
    have hQaIndex : Qa.relIndex (GAt Γ cp.a ⊓ GAt Γ cp.firstStep) = 2 :=
      Nat.eq_of_mul_eq_mul_right Nat.card_pos (hcount.trans hproduct.2)
    have hQnEdge : K ≤ GAt Γ cp.a ⊓ GAt Γ cp.firstStep :=
      (local_cores_le_edge_sylow ctx.sectionSeven Γ cp).2.trans cp.S_le_edge_stabilizers
    let P := Qa ⊔ K
    let _ : (Qa.subgroupOf P).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer
        (sup_le Qa.le_normalizer
          (hQnEdge.trans (inf_le_left.trans (stabilizer_le_normalizer_q Γ cp.a))))
    have h := Subgroup.relIndex_sup_left (K.subgroupOf P) (Qa.subgroupOf P)
    rw [← Subgroup.subgroupOf_sup (show Qa ≤ P from le_sup_left)
      (show K ≤ P from le_sup_right), Subgroup.relIndex_subgroupOf le_rfl,
      Subgroup.relIndex_subgroupOf (show K ≤ P from le_sup_right)] at h
    change Qa.relIndex (Qa ⊔ K) = Qa.relIndex K at h
    rw [show Qa ⊔ K = GAt Γ cp.a ⊓ GAt Γ cp.firstStep from hproduct.1, hQaIndex] at h
    change (Qa ⊓ K).relIndex K = 2
    rw [Subgroup.inf_relIndex_right]
    exact h.symm
  have hdata := Subgroup.index_two_conjugate_core_data F K N hFK hNK hindex
  obtain ⟨hN,hW⟩ := Subgroup.index_two_conjugate_core_quotient_elementary F K N hFK hNK hindex
  let _ := hN
  obtain ⟨action,haction⟩ := Subgroup.exists_quotient_conjugation_action F K C hFK hdata.2.1 hN
  refine ⟨hN,hW,action,?_⟩
  intro mover point
  exact ⟨_,haction mover point⟩

end Stellmacher.SectionNine
