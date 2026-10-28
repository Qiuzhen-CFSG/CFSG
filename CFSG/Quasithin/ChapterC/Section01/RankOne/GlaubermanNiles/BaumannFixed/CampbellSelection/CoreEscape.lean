module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellAutomorphisms.AutomorphismOrbit
public import Theory.GroupTheory.MinimalParabolicResidual
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.PResidual.PerfectCover
/-!
# A noncore actor forces one residual natural layer

A normal commutator preimage containing a noncore Sylow subgroup contains
O²(H), by the unique maximal Sylow overgroup. Residual commutator idempotence
then improves [O²(H),O₂(H)] ≤ F to containment in the actual Campbell V.
This is the exact input to the exceptional block recognition branch.

Source: Campbell, Pushing up in Finite Groups, II.8, printed pp.36–38,
specialized to the original C.1.17 marked family.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
variable {B H : Type*} [Group B] [Finite B] [Group H] [Finite H] {e : B →* H}

omit [Finite B] in
theorem InLocalClass.residual_le_of_normal_noncore (h : InLocalClass e)
    (N : Subgroup H) [N.Normal] (hn : ¬ e.range ⊓ N ≤ pCore 2 H) :
    pResidual 2 H ≤ N := by
  obtain ⟨T,he,hT⟩ := h.sylow
  have hu := hT.1
  obtain ⟨M,hM,_⟩ := hu.2
  have hgen : N ⊔ (T : Subgroup H)=⊤ := by
    by_contra hneq
    have hNM : N ≤ M := le_sup_left.trans
      (hu.le_maximal hM le_sup_right (lt_top_iff_ne_top.mpr hneq))
    apply hn
    rw [he]
    exact sylow_inf_normal_le_twoCore_of_uniqueMaximal T hu M N
      ⟨hM.1,hM.2.isCoatom⟩ hNM
  exact sInf_le ⟨inferInstance,isPGroup_quotient_of_sup_eq_top N T T.isPGroup' hgen⟩

omit [Finite H] in
private theorem preimage_normal (Q F : Subgroup H) [Q.Normal] [F.Normal] :
    (commutatorPreimage ⊤ Q F).Normal := by
  apply normalizer_eq_top_iff.mp
  exact top_le_iff.mp (commutatorPreimage_normalized ⊤ Q F ⊤
    le_normalizer_of_normal le_normalizer_of_normal le_normalizer_of_normal
    le_normalizer_of_normal)

theorem InLocalClass.residual_commutator_F_le_V (h : InLocalClass e) (hB : IsBaumannFixed B) :
    ⁅pResidual 2 H,Campbell.F H⁆ ≤ Campbell.V H := by
  obtain ⟨d,_,hS⟩ := h.exists_campbellEmbedding hB
  obtain ⟨n,hn,F,_,_,_,hcard,⟨m⟩⟩ := h.natural
  let : (Campbell.F H).Normal := Campbell.F_normal
  let : (Campbell.V H).Normal := by rw [h.campbellV_eq_moved hB m]; infer_instance
  let N := commutatorPreimage ⊤ (Campbell.F H) (Campbell.V H)
  let : N.Normal := preimage_normal _ _
  have hJN : Campbell.J (d.sylow : Subgroup H) ≤ N := by
    apply le_commutatorPreimage le_top
    rw [h.thompson_commutator_campbellF_eq hB m d]
    exact commutator_le_right _ _
  have hglobal : Campbell.J (⊤ : Subgroup H) ≤ N := by
    change elementaryAbelianMaxJ (⊤ : Subgroup H) ≤ N
    rw [elementaryAbelianMaxJ_top_eq_normalClosure_sylow d.sylow]
    exact normalClosure_le_normal hJN
  have hP : pResidual 2 H ≤ Campbell.J (⊤ : Subgroup H) := by
    let : (Campbell.J (⊤ : Subgroup H)).Normal := by
      change (elementaryAbelianMaxJ (⊤ : Subgroup H)).Normal
      let : (elementaryAbelianMaxJ (⊤ : Subgroup H)).Characteristic := elementaryAbelianMaxJ_top_characteristic
      infer_instance
    exact sInf_le ⟨inferInstance,isPGroup_quotient_of_sup_eq_top _ _ pCore_isPGroup
      (h.global_thompson_sup_core_eq_top hB)⟩
  exact (commutator_mono (hP.trans hglobal) le_rfl).trans
    (commutator_commutatorPreimage_le ⊤ _ _ le_normalizer_of_normal)

theorem InLocalClass.residual_core_le_V_of_noncore_commutator (h : InLocalClass e)
    (hB : IsBaumannFixed B) (X : Subgroup H) (hXS : X ≤ e.range)
    (hXQ : ¬ X ≤ pCore 2 H) (hXF : ⁅X,pCore 2 H⁆ ≤ Campbell.F H) :
    ⁅pResidual 2 H,pCore 2 H⁆ ≤ Campbell.V H := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : (Campbell.F H).Normal := Campbell.F_normal
  let N := commutatorPreimage ⊤ (pCore 2 H) (Campbell.F H)
  let : N.Normal := preimage_normal _ _
  have hXN : X ≤ N := le_commutatorPreimage le_top hXF
  have hPN : pResidual 2 H ≤ N := h.residual_le_of_normal_noncore N
    (fun hz => hXQ ((le_inf hXS hXN).trans hz))
  have hb : ⁅pCore 2 H,pResidual 2 H⁆ ≤ Campbell.F H := by
    rw [commutator_comm]
    exact (commutator_mono hPN le_rfl).trans
      (commutator_commutatorPreimage_le ⊤ _ _ le_normalizer_of_normal)
  rw [commutator_comm]
  rw [←commutator_isPPerfect_idempotent (pResidual 2 H) (pCore 2 H)
    (isPPerfect_pResidual 2) pCore_isPGroup le_normalizer_of_normal]
  exact (commutator_mono hb le_rfl).trans
    ((commutator_comm _ _).le.trans (h.residual_commutator_F_le_V hB))
end CFSG.Quasithin.ChapterC.GlaubermanNiles
