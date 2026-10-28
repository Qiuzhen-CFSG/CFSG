module
public import CFSG.Quasithin.ChapterG.Section09.ActionQuotient
public import Theory.Representation.NormalComponentConstituents.Homogeneous
/-!
# G.9 on a faithful constituent action image

In a homogeneous normal restriction, each conjugate of a component has
quasiequivalent action on the chosen simple constituent. An actual
intertwiner between the constituent and its conjugate supplies the linear
part of this quasiequivalence.

Restriction to HA and descent by its action kernel then give every field
of G.9.3 for Aut_HA(I). The covering group is the preimage of HA in the
original SQTK cover. Faithfulness of A on I remains explicit, as in the
contradiction argument of Aschbacher--Smith G.11.7, printed pp.366–367.
-/
@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterG.Section09
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
 (ρ : Representation (ZMod 2) G V) (H : Subgroup G) [H.Normal]
 (I : Submodule (ZMod 2) V) (hI : H ≤ subspaceStabilizer ρ I)

/-- Homogeneity makes conjugate components quasiequivalent on the literal
constituent, even when its subspace is not ambient invariant. -/
theorem constituent_quasiequivalent_conjugate
 (hi : IsIrreducible (invariantSubspace ρ H I hI).toRepresentation)
 (hh : ∀ J : Subrepresentation (ρ.comp H.subtype), IsIrreducible J.toRepresentation →
   Homogeneous.SameModule (invariantSubspace ρ H I hI) J)
 (L : Subgroup G) (hLH : L ≤ H) (g : G)
 (hL : L ≤ subspaceStabilizer ρ I)
 (hLg : L.map (MulAut.conj g).toMonoidHom ≤ subspaceStabilizer ρ I) :
 Quasiequivalent (invariantSubspace ρ L I hL).toRepresentation
   (invariantSubspace ρ (L.map (MulAut.conj g).toMonoidHom) I hLg).toRepresentation := by
  let R := invariantSubspace ρ H I hI
  let J := conjugateSubrepresentation ρ H R g
  have hJ : IsIrreducible J.toRepresentation := by
    apply (Subrepresentation.irreducible_iff_isAtom _).mpr
    simpa only [J,conjugateSubrepresentationOrderIso_apply,inv_inv] using
      ((conjugateSubrepresentationOrderIso ρ H g⁻¹).isAtom_iff R).mpr
        ((Subrepresentation.irreducible_iff_isAtom R).mp hi)
  obtain ⟨e⟩ := (Homogeneous.sameModule_iff_repEquiv R J).mp (hh J hJ)
  let c := conjugateSubrepresentationEquiv ρ H R g
  refine ⟨(MulAut.conj g).subgroupMap L,e.toLinearEquiv.trans c.toLinearEquiv,?_⟩
  intro l w
  have he := LinearMap.congr_fun (e.isIntertwining' ⟨l,hLH l.2⟩) w
  have hc := Representation.RepEquiv.isIntertwining c ⟨l,hLH l.2⟩ (e w)
  exact (congrArg c he).trans hc

end CFSG.Quasithin.ChapterG.Section09

namespace CFSG.Quasithin.ChapterG.Section09
universe u v
variable {G : Type u} [Group G] [Finite G]
 {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- The actual action of the generated group on the chosen invariant constituent. -/
def constituentAction (ρ : Representation (ZMod 2) G V) (H A : Subgroup G)
 (I : Submodule (ZMod 2) V) (hH : H ≤ subspaceStabilizer ρ I)
 (hA : A ≤ subspaceStabilizer ρ I) : Representation (ZMod 2) (H ⊔ A : Subgroup G) I :=
 (invariantSubspace ρ (H ⊔ A) I (sup_le hH hA)).toRepresentation

/-- G.9.3 for the actual faithful action image Aut_HA(I). The cover is the
literal preimage of HA in the original cover; its section-rank bounds are
therefore retained. Faithfulness of the actor is an explicit assumption. -/
theorem componentHypothesis_constituent {K : GroupClass.{u}}
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
   Quasiequivalent (invariantSubspace ρ L I (hLH.trans hH)).toRepresentation
     (invariantSubspace ρ L₂ I (h₂H.trans hH)).toRepresentation) :
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
      Quasiequivalent (σ.comp (L.subgroupOf P).subtype) (σ.comp L₂.subtype) := by
    rcases hc with h | ⟨L₂,h₂H,h₂,h,qv⟩
    · exact Or.inl (congrArg (fun J : Subgroup G => J.subgroupOf P) h)
    have h₂P := h₂H.trans hHP
    refine Or.inr ⟨L₂.subgroupOf P,h₂.subgroupOf h₂P,?_,?_⟩
    · rw [h,subgroupOf_sup hLP h₂P]
    obtain ⟨e,t,ht⟩ := qv
    let eL := subgroupOfEquivOfLe hLP
    let e₂ := subgroupOfEquivOfLe h₂P
    refine ⟨eL.trans (e.trans e₂.symm),t,?_⟩
    intro l w
    exact ht (eL l) w
  let : IsElementaryAbelian 2 (A.subgroupOf P) := IsElementaryAbelian.subgroupOf hAP
  exact componentHypothesis_of_faithful_quotient σ (kerRepresentation σ) q
    (QuotientGroup.mk'_surjective _) rfl (kerRepresentation_faithful σ)
    (cover.map (fun c => c.subgroup P)) (A.subgroupOf P) (L.subgroupOf P) (H.subgroupOf P) m
    hσA hσH ((Nat.card_congr eA.toEquiv).trans ha) hd (hL.subgroupOf hLP) hm' hi' hc'
end CFSG.Quasithin.ChapterG.Section09
