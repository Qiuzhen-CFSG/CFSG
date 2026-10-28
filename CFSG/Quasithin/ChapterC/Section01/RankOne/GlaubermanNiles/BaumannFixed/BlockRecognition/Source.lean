module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.BlockRecognition.Short
/-!
# The source one-layer block alternative

Campbell's residual commutator bound identifies the original residual's
core quotient and natural module and gives shortness. Over a field larger
than F₂ the original actor chart yields the named L₂ block; over F₂ its
cubic quotient yields the named A₃ block. Normality of the actual residual
supplies the ambient block condition. No block, kernel or classification
conclusion is assumed.

Source: Campbell II.8, printed p.38; Aschbacher–Smith C.1.18(3), p.126.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles.BlockRecognition
variable {B H : Type*} [Group B] [Finite B] [Group H] [Finite H] {e : B →* H}
variable (h : InLocalClass e) (hB : IsBaumannFixed B)
    (hc : ⁅pResidual 2 H,pCore 2 H⁆≤Campbell.V H)
variable {F : Type} [Field F] [Finite F] [CharP F 2] (m : NaturalModel e F)

include h hB hc m in
theorem residual_linearBlockModel (hF:2<Nat.card F) :
    IsLinearBlockModel (pResidual 2 H) (Representation.specialLinearNatural (k:=F) 2) := by
  obtain ⟨E,hE⟩ := m.exists_actor_equiv_sl hF
  let d:=residualNaturalModel h hB hc m
  let d':BlockModuleModel (pResidual 2 H) (Matrix.SL2.naturalAction F):={
    quotientIso := (residualCoreEquiv h hB hc).trans E
    moduleIso := d.moduleIso
    intertwining := by
      intro l u
      change d.moduleIso (QuotientGroup.mk' (blockFixed (pResidual 2 H)) (blockConjugate (pResidual 2 H) l u))=
        Matrix.SL2.naturalAction F (E (residualActor h hB l))
          (d.moduleIso (QuotientGroup.mk' (blockFixed (pResidual 2 H)) u))
      rw [hE]
      exact d.intertwining l u }
  exact ⟨Matrix.SL2.naturalAction F,⟨d'⟩,fun _ _ => rfl⟩

include h hB hc m in
theorem residual_l2_block {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n) :
    IsL2EvenBlock (pResidual 2 H) n := by
  have hl:2<Nat.card F := by
    rw [hF]
    exact (by simpa using Nat.pow_lt_pow_right (by decide : 1<2) hn)
  obtain ⟨E,_⟩:=m.exists_actor_equiv_sl hl
  refine ⟨hn,residual_short h hB hc m,F,inferInstance,inferInstance,hF,?_,
    residual_linearBlockModel h hB hc m hl⟩
  exact ⟨F,inferInstance,inferInstance,hF,
    ⟨((residualCoreEquiv h hB hc).trans E).trans Atlas.RankOneFieldAutomorphisms.slEquivPSL⟩⟩

include h hB hc m in
theorem residual_alternatingThree_block (hF:Nat.card F=2) :
    IsAlternatingBlock (pResidual 2 H) 3 := by
  apply (residual_short h hB hc m).isAlternatingBlock_of_quotient_three
  exact (Nat.card_congr (residualCoreEquiv h hB hc).toEquiv).trans
    (m.actor_card_of_field_card_two e hF)

end BlockRecognition

variable {B H : Type*} [Group B] [Finite B] [Group H] [Finite H] {e : B →* H}

theorem InLocalClass.blockAlternative_of_residual_commutator_le
    (h:InLocalClass e) (hB:IsBaumannFixed B)
    (hc:⁅pResidual 2 H,pCore 2 H⁆≤Campbell.V H) : BlockAlternative H := by
  obtain ⟨n,hn,F,_,_,_,hF,⟨m⟩⟩ := h.natural
  refine ⟨⟨inferInstance,BlockRecognition.residual_short h hB hc m,
    (inferInstance : (pResidual 2 H).Normal).isSubnormal⟩,?_⟩
  rcases hn.eq_or_lt with he|he
  · right
    apply BlockRecognition.residual_alternatingThree_block h hB hc m
    simpa only [←he,pow_one] using hF
  · exact Or.inl ⟨n,BlockRecognition.residual_l2_block h hB hc m he hF⟩
end CFSG.Quasithin.ChapterC.GlaubermanNiles
