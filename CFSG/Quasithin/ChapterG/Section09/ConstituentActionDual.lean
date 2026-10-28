module
public import CFSG.Quasithin.ChapterG.Section09.ConstituentAction
public import CFSG.Quasithin.ChapterG.Section09.ActionQuotientDual

/-!
# Constituents with a possibly dual component partner

Restrict to the literal generated subgroup and descend its action kernel.
Both alternatives in G.9.3 are preserved, including the contragredient action
of the second component. This extends the ordinary-comparison interface
without changing it and is used by the exchanged G.11.6 branch.

Source: Aschbacher--Smith G.11.6, printed p.366.
-/
@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterG.Section09
universe u v
variable {G : Type u} [Group G] [Finite G]
 {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- G.9.3 for the actual faithful action image Aut_HA(I). The cover is the
literal preimage of HA in the original cover; its section-rank bounds are
therefore retained. Faithfulness of the actor is an explicit assumption. -/
theorem componentHypothesis_constituent_or_dual {K : GroupClass.{u}}
 (ρ : Representation (ZMod 2) G V) (cover : Nonempty (SQTKCover K G))
 (A L H : Subgroup G) [H.Normal] [IsElementaryAbelian 2 A]
 (I : Submodule (ZMod 2) V) (hH : H ≤ subspaceStabilizer ρ I)
 (hA : A ≤ subspaceStabilizer ρ I)
 (hfH : Function.Injective (invariantSubspace ρ H I hH).toRepresentation)
 (hfA : Function.Injective (invariantSubspace ρ A I hA).toRepresentation)
 (hi : IsIrreducible (invariantSubspace ρ H I hH).toRepresentation)
 (m : ℕ) (ha : Nat.card A = 2^m) (hd : Module.finrank (ZMod 2) I ≤ 2*(m+1))
 (hL : IsComponent G L) (hm : ⁅L,A⁆ ≠ ⊥) (hLH : L ≤ H)
 (hc : H = L ∨ ∃ L₂ : Subgroup G, ∃ h₂H : L₂ ≤ H,
   IsComponent G L₂ ∧ H = L ⊔ L₂ ∧
   (Quasiequivalent (invariantSubspace ρ L I (hLH.trans hH)).toRepresentation
      (invariantSubspace ρ L₂ I (h₂H.trans hH)).toRepresentation ∨
    Quasiequivalent (invariantSubspace ρ L I (hLH.trans hH)).toRepresentation
      (invariantSubspace ρ L₂ I (h₂H.trans hH)).toRepresentation.dual)) :
 let P := H ⊔ A
 let σ := constituentAction ρ H A I hH hA
 let q := QuotientGroup.mk' σ.ker
 ComponentHypothesis K (kerRepresentation σ) ((A.subgroupOf P).map q)
   ((L.subgroupOf P).map q) ((H.subgroupOf P).map q) m := by
  let P := H ⊔ A
  let σ := constituentAction ρ H A I hH hA
  let q := QuotientGroup.mk' σ.ker
  let eH := subgroupOfEquivOfLe (show H ≤ P from le_sup_left)
  let eA := subgroupOfEquivOfLe (show A ≤ P from le_sup_right)
  have hHP : H ≤ P := le_sup_left
  have hAP : A ≤ P := le_sup_right
  have hLP : L ≤ P := hLH.trans hHP
  have hh : σ.comp (H.subgroupOf P).subtype =
      (invariantSubspace ρ H I hH).toRepresentation.comp eH.toMonoidHom := rfl
  have ha' : σ.comp (A.subgroupOf P).subtype =
      (invariantSubspace ρ A I hA).toRepresentation.comp eA.toMonoidHom := rfl
  have hσH : Function.Injective (σ.comp (H.subgroupOf P).subtype) := by
    rw [hh]; exact hfH.comp eH.injective
  have hσA : Function.Injective (σ.comp (A.subgroupOf P).subtype) := by
    rw [ha']; exact hfA.comp eA.injective
  have hi' : IsIrreducible (σ.comp (H.subgroupOf P).subtype) := by
    rw [hh]
    exact (irreducible_comp_surjective_iff eH.toMonoidHom eH.surjective _).mpr hi
  have hm' : ⁅L.subgroupOf P,A.subgroupOf P⁆ ≠ ⊥ := by
    intro hz
    have he := congrArg (Subgroup.map P.subtype) hz
    rw [map_commutator,map_subgroupOf_eq_of_le hLP,map_subgroupOf_eq_of_le hAP,Subgroup.map_bot] at he
    exact hm he
  have hc' : H.subgroupOf P = L.subgroupOf P ∨ ∃ L₂ : Subgroup P,
      IsComponent P L₂ ∧ H.subgroupOf P = L.subgroupOf P ⊔ L₂ ∧
      (Quasiequivalent (σ.comp (L.subgroupOf P).subtype) (σ.comp L₂.subtype) ∨
       Quasiequivalent (σ.comp (L.subgroupOf P).subtype) (Representation.dual (σ.comp L₂.subtype))) := by
    rcases hc with h | ⟨L₂,h₂H,h₂,h,qv⟩
    · exact Or.inl (congrArg (fun J : Subgroup G => J.subgroupOf P) h)
    have h₂P := h₂H.trans hHP
    refine Or.inr ⟨L₂.subgroupOf P,h₂.subgroupOf h₂P,?_,?_⟩
    · rw [h,subgroupOf_sup hLP h₂P]
    let eL := subgroupOfEquivOfLe hLP
    let e₂ := subgroupOfEquivOfLe h₂P
    rcases qv with ⟨e,t,ht⟩ | ⟨e,t,ht⟩
    · exact Or.inl ⟨eL.trans (e.trans e₂.symm),t,fun l w => ht (eL l) w⟩
    · exact Or.inr ⟨eL.trans (e.trans e₂.symm),t,fun l w => ht (eL l) w⟩
  let : IsElementaryAbelian 2 (A.subgroupOf P) := IsElementaryAbelian.subgroupOf hAP
  exact componentHypothesis_of_faithful_quotient_or_dual σ (kerRepresentation σ) q
    (QuotientGroup.mk'_surjective _) rfl (kerRepresentation_faithful σ)
    (cover.map (fun c => c.subgroup P)) (A.subgroupOf P) (L.subgroupOf P) (H.subgroupOf P) m
    hσA hσH ((Nat.card_congr eA.toEquiv).trans ha) hd (hL.subgroupOf hLP) hm' hi' hc'
end CFSG.Quasithin.ChapterG.Section09
