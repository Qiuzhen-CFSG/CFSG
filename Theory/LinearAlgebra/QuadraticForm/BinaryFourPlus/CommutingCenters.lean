module
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus
import all Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus.Plane
/-!
# Commuting rank-one centers in the binary plus four-space

A nonidentity rank-one isometry reflects exactly one of the two anisotropic
planes. Its only nonzero fixed vector on that plane is its displacement
center. Commuting actors fix each other's centers, so distinct centers lie
on opposite planes. The small certificate treats one actor at a time;
commutation and simultaneous orientation are proved algebraically.

The orientation uses the literal plane-swap actor and conjugates the group
marking by that same actor. Source application: the positive-center A₅
geometry in Aschbacher--Smith 10.2.1, printed p.743.
-/

public section
namespace BinaryFourPlus
private instance : DecidableEq Wreath :=
  (RegularWreathProduct.equivProd (Equiv.Perm (Fin 3)) C2).injective.decidableEq
private instance : Fintype Wreath := Fintype.ofEquiv _
  (RegularWreathProduct.equivProd (Equiv.Perm (Fin 3)) C2).symm
private def eval (w : Wreath) (v : V) : V :=
  if w.right=1 then (planeLinear (w.left 1) v.1,planeLinear (w.left swapIndex) v.2)
  else (planeLinear (w.left 1) v.2,planeLinear (w.left swapIndex) v.1)
set_option synthInstance.maxSize 2000 in
private theorem rank_one_certificate : ∀ (w : Wreath) (u : V),
    u ≠ 0 → (∃ x, eval w x - x = u) →
    (∀ x, eval w x - x = 0 ∨ eval w x - x = u) →
    (u.2 = 0 ∧ ∀ v : Plane, eval w (v,0) = (v,0) → v = 0 ∨ v = u.1) ∨
    (u.1 = 0 ∧ ∀ v : Plane, eval w (0,v) = (0,v) → v = 0 ∨ v = u.2) := by
  decide +kernel


private theorem eval_eq (w : Wreath) (v : V) :
    eval w v = (wreathToIsometry w).val v := (wreathToIsometry_apply w v).symm

private theorem action_mul (a b : Wreath) (v : V) :
    (wreathToIsometry (a*b)).val v =
      (wreathToIsometry a).val ((wreathToIsometry b).val v) := by
  rw [map_mul]
  rfl

/-- Commutation preserves the unique nonzero displacement vector. -/
theorem commuting_fixes_rank_one_center (a b : Wreath) (u : V)
    (hu : u ≠ 0) (hab : Commute a b)
    (hline : ∀ x, (wreathToIsometry a).val x-x=0 ∨ (wreathToIsometry a).val x-x=u)
    (hwit : ∃ x, (wreathToIsometry a).val x-x=u) :
    (wreathToIsometry b).val u=u := by
  obtain ⟨x,hx⟩ := hwit
  have hc : (wreathToIsometry a).val ((wreathToIsometry b).val x)=
      (wreathToIsometry b).val ((wreathToIsometry a).val x) := by
    simpa only [action_mul] using congrArg (fun w : Wreath => (wreathToIsometry w).val x) hab.eq
  have hd : (wreathToIsometry a).val ((wreathToIsometry b).val x)-
      (wreathToIsometry b).val x=(wreathToIsometry b).val u := by
    rw [hc,←map_sub,hx]
  rcases hline ((wreathToIsometry b).val x) with hz | he
  · exact ((wreathToIsometry b).val.map_ne_zero_iff.mpr hu (hd.symm.trans hz)).elim
  · exact hd.symm.trans he

/-- Two distinct nonzero centers of commuting rank-one actors lie in opposite
anisotropic coordinate planes. -/
theorem commuting_rank_one_centers_opposite (w₁ w₂ : Wreath) (u₁ u₂ : V)
    (hcomm : Commute w₁ w₂) (h₁ : u₁ ≠ 0) (h₂ : u₂ ≠ 0) (hne : u₁ ≠ u₂)
    (hline₁ : ∀ x, (wreathToIsometry w₁).val x-x=0 ∨ (wreathToIsometry w₁).val x-x=u₁)
    (hline₂ : ∀ x, (wreathToIsometry w₂).val x-x=0 ∨ (wreathToIsometry w₂).val x-x=u₂)
    (hwit₁ : ∃ x, (wreathToIsometry w₁).val x-x=u₁)
    (hwit₂ : ∃ x, (wreathToIsometry w₂).val x-x=u₂) :
    (u₁.2=0 ∧ u₂.1=0) ∨ (u₁.1=0 ∧ u₂.2=0) := by
  have hfix := commuting_fixes_rank_one_center w₂ w₁ u₂ h₂ hcomm.symm hline₂ hwit₂
  have hc₁ := rank_one_certificate w₁ u₁ h₁
    (by simpa only [eval_eq] using hwit₁) (by simpa only [eval_eq] using hline₁)
  have hc₂ := rank_one_certificate w₂ u₂ h₂
    (by simpa only [eval_eq] using hwit₂) (by simpa only [eval_eq] using hline₂)
  rcases hc₁ with ⟨ha,hfa⟩ | ⟨ha,hfa⟩ <;>
    rcases hc₂ with ⟨hb,_⟩ | ⟨hb,_⟩
  · have he : (u₂.1,0) = u₂ := Prod.ext rfl hb.symm
    rcases hfa u₂.1 (by rw [he,eval_eq]; exact hfix) with hz | hz
    · exact (h₂ (Prod.ext hz hb)).elim
    · exact (hne (Prod.ext hz.symm (ha.trans hb.symm))).elim
  · exact .inl ⟨ha,hb⟩
  · exact .inr ⟨ha,hb⟩
  · have he : (0,u₂.2) = u₂ := Prod.ext hb.symm rfl
    rcases hfa u₂.2 (by rw [he,eval_eq]; exact hfix) with hz | hz
    · exact (h₂ (Prod.ext hb hz)).elim
    · exact (hne (Prod.ext (ha.trans hb.symm) hz.symm)).elim

/-- The literal actor interchanging the two anisotropic coordinate planes. -/
@[expose] def planeSwap : Wreath := RegularWreathProduct.inl swapIndex

@[simp] theorem planeSwap_apply (v : V) :
    (wreathToIsometry planeSwap).val v = (v.2,v.1) := by
  rw [wreathToIsometry_apply]
  simp [planeSwap,swapIndex_ne_one]

/-- Simultaneously conjugating actors and changing coordinates preserves the
original action. This applies to the chosen plane swap as well as any isometry. -/
theorem wreath_action_conj_apply (s w : Wreath) (v : V) :
    (wreathToIsometry (MulAut.conj s w)).val ((wreathToIsometry s).val v) =
      (wreathToIsometry s).val ((wreathToIsometry w).val v) := by
  rw [MulAut.conj_apply,action_mul,action_mul]
  congr 1
  congr 1
  have hi := action_mul s⁻¹ s v
  simpa only [inv_mul_cancel,map_one,Subgroup.coe_one,LinearEquiv.coe_one,id_eq] using hi.symm

/-- Orient the two original marked centers by either the identity or the
literal plane swap; both nonzero coordinates are retained. -/
theorem exists_oriented_commuting_centers (w₁ w₂ : Wreath) (u₁ u₂ : V)
    (hcomm : Commute w₁ w₂) (h₁ : u₁ ≠ 0) (h₂ : u₂ ≠ 0) (hne : u₁ ≠ u₂)
    (hline₁ : ∀ x, (wreathToIsometry w₁).val x-x=0 ∨ (wreathToIsometry w₁).val x-x=u₁)
    (hline₂ : ∀ x, (wreathToIsometry w₂).val x-x=0 ∨ (wreathToIsometry w₂).val x-x=u₂)
    (hwit₁ : ∃ x, (wreathToIsometry w₁).val x-x=u₁)
    (hwit₂ : ∃ x, (wreathToIsometry w₂).val x-x=u₂) :
    ∃ (s : Wreath) (a b : Plane), (s=1 ∨ s=planeSwap) ∧ a≠0 ∧ b≠0 ∧
      (wreathToIsometry s).val u₁=(a,0) ∧ (wreathToIsometry s).val u₂=(0,b) := by
  rcases commuting_rank_one_centers_opposite w₁ w₂ u₁ u₂ hcomm h₁ h₂ hne
    hline₁ hline₂ hwit₁ hwit₂ with h | h
  · refine ⟨1,u₁.1,u₂.2,Or.inl rfl,?_,?_,?_,?_⟩
    · exact fun hz => h₁ (Prod.ext hz h.1)
    · exact fun hz => h₂ (Prod.ext h.2 hz)
    · simpa only [map_one,Subgroup.coe_one,LinearEquiv.coe_one,id_eq] using
        (Prod.ext rfl h.1 : u₁=(u₁.1,0))
    · simpa only [map_one,Subgroup.coe_one,LinearEquiv.coe_one,id_eq] using
        (Prod.ext h.2 rfl : u₂=(0,u₂.2))
  · refine ⟨planeSwap,u₁.2,u₂.1,Or.inr rfl,?_,?_,?_,?_⟩
    · exact fun hz => h₁ (Prod.ext h.1 hz)
    · exact fun hz => h₂ (Prod.ext hz h.2)
    · rw [planeSwap_apply,h.1]
    · rw [planeSwap_apply,h.2]

/-- Consumer adapter: compose the original coordinate marking and actor
marking with the same isometry and its inner automorphism. -/
theorem conjugated_marking_equivariant
    {A U : Type*} [Group A] [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : A → U → U) (c : U ≃ₗ[ZMod 2] V) (e : A ≃* Wreath)
    (he : ∀ g v, c (ρ g v)=(wreathToIsometry (e g)).val (c v)) (s : Wreath) :
    ∀ g v, (c.trans (wreathToIsometry s).val) (ρ g v)=
      (wreathToIsometry ((e.trans (MulAut.conj s)) g)).val
        ((c.trans (wreathToIsometry s).val) v) := by
  intro g v
  change (wreathToIsometry s).val (c (ρ g v)) = _
  rw [he]
  exact (wreath_action_conj_apply s (e g) (c v)).symm

end BinaryFourPlus
