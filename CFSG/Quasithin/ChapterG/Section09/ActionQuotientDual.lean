module
public import CFSG.Quasithin.ChapterG.Section09.ActionQuotient

/-!
# Dual component comparison through a faithful action quotient

The literal component images retain either ordinary or dual quasiequivalence.
In the dual case the intertwining identity is checked on inverse actors, so
no self-duality or change of the component marking is assumed.

Source: Aschbacher--Smith G.9.3 and G.11.6, printed pp.353,366.
-/
@[expose] public noncomputable section
open Subgroup Representation Theory.GroupTheory
namespace CFSG.Quasithin.ChapterG.Section09
universe u v
variable {G Q : Type u} [Group G] [Group Q] [Finite G] [Finite Q]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem faithful_le {ρ : Representation (ZMod 2) G V} {L H : Subgroup G}
    (hH : Function.Injective (ρ.comp H.subtype)) (hLH : L ≤ H) :
    Function.Injective (ρ.comp L.subtype) := by
  intro a b hab
  exact Subtype.ext (congrArg (fun z : H => (z : G)) (hH (a₁ :=  ⟨a,hLH a.2⟩) (a₂ :=  ⟨b,hLH b.2⟩) hab))

omit [Finite G] in
/-- All literal fields of G.9.3 descend to a faithful quotient, provided the
normal component group and the actor act faithfully before descent. -/
theorem componentHypothesis_of_faithful_quotient_or_dual {K : GroupClass.{u}}
    (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) Q V)
    (f : G →* Q) (hf : Function.Surjective f) (he : σ.comp f = ρ)
    (hs : Function.Injective σ) (cover : Nonempty (SQTKCover K G))
    (A L H : Subgroup G) (m : ℕ) [IsElementaryAbelian 2 A]
    (hA : Function.Injective (ρ.comp A.subtype))
    (hH : Function.Injective (ρ.comp H.subtype))
    (ha : Nat.card A = 2^m) (hd : Module.finrank (ZMod 2) V ≤ 2*(m+1))
    (hL : IsComponent G L) (hm : ⁅L,A⁆ ≠ ⊥) [H.Normal]
    (hi : IsIrreducible (ρ.comp H.subtype))
    (hc : H = L ∨ ∃ L₂ : Subgroup G, IsComponent G L₂ ∧ H = L ⊔ L₂ ∧
      (Quasiequivalent (ρ.comp L.subtype) (ρ.comp L₂.subtype) ∨
       Quasiequivalent (ρ.comp L.subtype) (Representation.dual (ρ.comp L₂.subtype)))) :
    ComponentHypothesis K σ (A.map f) (L.map f) (H.map f) m := by
  have hLH : L ≤ H := by
    rcases hc with h | ⟨L₂,_,h,_⟩
    · exact h.symm.le
    · rw [h]; exact le_sup_left
  have hLf := faithful_le hH hLH
  let eL := actionImageEquiv ρ σ f he L hLf
  have hL0 : L.map f ≠ ⊥ := by
    intro hz
    have hone : ∀ l : L, l = 1 := by
      intro l
      apply eL.injective
      apply Subtype.ext
      have hh := (eL l).2
      have hh0 := hz.le hh
      simpa using hh0
    have hbot : L = ⊥ := by
      apply eq_bot_iff.mpr
      intro l hl
      exact congrArg Subtype.val (hone ⟨l,hl⟩)
    exact hm (by simp [hbot])
  refine { faithful := hs
           elementary := IsElementaryAbelian.map f
           card_actor := ?_
           degree_le := hd
           quotient := ?_
           component := (hL.map_surjective f hf).resolve_left hL0
           noncentral := ?_
           normal_H := Subgroup.Normal.map inferInstance f hf
           irreducible := ?_
           components := ?_ }
  · exact (Nat.card_congr (actionImageEquiv ρ σ f he A hA).toEquiv).symm.trans ha
  · exact cover.map (fun c => c.map f hf)
  · intro hz
    apply hm
    apply eq_bot_iff.mpr
    intro x hx
    have hxH : x ∈ H := ((commutator_mono hLH le_rfl).trans (commutator_le_left H A)) hx
    have hfx : f x = 1 := by
      have : f x ∈ (⁅L,A⁆).map f := mem_map.mpr ⟨x,hx,rfl⟩
      rw [map_commutator,hz] at this
      exact this
    have hinj := (actionImageEquiv ρ σ f he H hH).injective
    exact congrArg Subtype.val (hinj (a₁ :=  ⟨x,hxH⟩) (a₂ :=  1) (Subtype.ext (by simpa using hfx)))
  · apply (irreducible_comp_surjective_iff (f.subgroupMap H) (f.subgroupMap_surjective H)
      (σ.comp (H.map f).subtype)).mp
    convert hi using 1
    apply MonoidHom.ext
    intro h
    exact congrArg (fun r : Representation (ZMod 2) G V => r (h : G)) he
  · rcases hc with h | ⟨L₂,h₂,h,q⟩
    · exact Or.inl (congrArg (map f) h)
    have h₂H : L₂ ≤ H := by rw [h]; exact le_sup_right
    have h₂f := faithful_le hH h₂H
    let e₂ := actionImageEquiv ρ σ f he L₂ h₂f
    have h₂0 : L₂.map f ≠ ⊥ := by
      intro hz
      have hbot : L₂ = ⊥ := by
        apply eq_bot_iff.mpr
        intro l hl
        exact congrArg Subtype.val (e₂.injective (a₁ :=  ⟨l,hl⟩) (a₂ :=  1)
          (Subtype.ext (by
            have hh := (e₂ ⟨l,hl⟩).2
            have hh0 := hz.le hh
            simpa using hh0)))
      let := h₂.2
      let : IsSimpleGroup (L₂ ⧸ center L₂) := IsQuasisimple.simple
      let : Nontrivial L₂ := (QuotientGroup.mk'_surjective (center L₂)).nontrivial
      exact (nontrivial_iff_ne_bot L₂).mp inferInstance hbot
    refine Or.inr ⟨_,(h₂.map_surjective f hf).resolve_left h₂0,?_,?_⟩
    · rw [h,Subgroup.map_sup]
    have hx (x : G) : σ (f x) = ρ x :=
      congrArg (fun r : Representation (ZMod 2) G V => r x) he
    rcases q with ⟨e,t,ht⟩ | ⟨e,t,ht⟩
    · refine Or.inl ⟨eL.symm.trans (e.trans e₂),t,?_⟩
      intro l w
      obtain ⟨a,rfl⟩ := eL.surjective l
      simp only [MulEquiv.trans_apply,MulEquiv.symm_apply_apply]
      change t (σ (f (a : G)) w) = σ (f (e a : G)) (t w)
      rw [hx,hx]
      exact ht a w
    · refine Or.inr ⟨eL.symm.trans (e.trans e₂),t,?_⟩
      intro l w
      obtain ⟨a,rfl⟩ := eL.surjective l
      simp only [MulEquiv.trans_apply,MulEquiv.symm_apply_apply]
      ext z
      change t (σ (f (a : G)) w) z = t w (σ ((f (e a : G))⁻¹) z)
      rw [← map_inv,hx,hx]
      exact congrArg (fun u => u z) (ht a w)

end CFSG.Quasithin.ChapterG.Section09
