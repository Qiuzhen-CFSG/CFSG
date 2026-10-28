module

public import Mathlib.GroupTheory.SchurZassenhaus

/-!
# Lifting a complement through a coprime kernel

A quotient complement lifts when its order is coprime to the kernel order.
Apply Schur–Zassenhaus to the kernel in the inverse image of the chosen
complement. The lifted complement maps isomorphically onto the original
one. The isomorphism retains the original projection pointwise, so actions
can be transported without replacing their quotient maps.

The kernel need not be central. This matters for Aschbacher, *Sporadic
Groups* (1994), 47.3(3), p.262: the cyclic eight-group acts nontrivially on
the order-three kernel of the projective normalizer.
-/

open Subgroup

namespace MonoidHom
variable {A B : Type*} [Group A] [Group B]

public theorem exists_complement_lift_of_coprime_kernel
    (f : A →* B) (hf : Function.Surjective f)
    (U T : Subgroup B) (hUT : U.IsComplement' T)
    (hcop : Nat.Coprime (Nat.card f.ker) (Nat.card T)) :
    ∃ E : Subgroup A, (U.comap f).IsComplement' E ∧
      ∃ e : E ≃* T, ∀ x : E, (e x : B) = f x := by
  classical
  let V := T.comap f
  let r : V →* T := (f.comp V.subtype).codRestrict T (fun x => x.property)
  have hr : Function.Surjective r := by
    intro t
    obtain ⟨a, ha⟩ := hf t
    exact ⟨⟨a, show f a ∈ T from ha.symm ▸ t.property⟩, Subtype.ext ha⟩
  let k : r.ker ≃* f.ker :=
    { toFun := fun x => ⟨x.val.val, congrArg Subtype.val x.property⟩
      invFun := fun x => ⟨⟨x, by change f x ∈ T; rw [x.property]; exact T.one_mem⟩,
        Subtype.ext x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  have hrindex : r.ker.index = Nat.card T := by
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective r hr).toEquiv
  obtain ⟨W, hW⟩ := exists_right_complement'_of_coprime (N := r.ker)
    (by rw [Nat.card_congr k.toEquiv, hrindex]; exact hcop)
  let s : W →* T := r.comp W.subtype
  have hs : Function.Bijective s := by
    constructor
    · apply (MonoidHom.ker_eq_bot_iff s).mp
      apply bot_unique
      intro x hx
      apply Subtype.ext
      exact disjoint_def.mp hW.disjoint hx x.property
    · intro t
      obtain ⟨v, hv⟩ := hr t
      obtain ⟨⟨a, b⟩, hab⟩ := hW.2 v
      refine ⟨b, ?_⟩
      change r b = t
      rw [← hv, ← hab, map_mul, show r a = 1 from a.property, one_mul]
  let E := W.map V.subtype
  let e : E ≃* T := (W.equivMapOfInjective V.subtype V.subtype_injective).symm.trans
    (MulEquiv.ofBijective s hs)
  have he (x : E) : (e x : B) = f x := by
    obtain ⟨w, rfl⟩ := (W.equivMapOfInjective V.subtype V.subtype_injective).surjective x
    simp only [e, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rfl
  have hd : Disjoint (U.comap f) E := by
    apply disjoint_def.mpr
    intro x hxU hxE
    have hfx : f x = 1 := disjoint_def.mp hUT.disjoint hxU
      ((he ⟨x, hxE⟩) ▸ (e ⟨x, hxE⟩).property)
    have hxe : e ⟨x, hxE⟩ = 1 := Subtype.ext ((he _).trans hfx)
    exact congrArg Subtype.val (e.injective (hxe.trans e.map_one.symm))
  refine ⟨E, ⟨mul_injective_of_disjoint hd, ?_⟩, e, he⟩
  intro a
  obtain ⟨⟨u, t⟩, hut⟩ := hUT.2 (f a)
  let x := e.symm t
  have hx : f x = (t : B) := (he x).symm.trans (congrArg Subtype.val (e.apply_symm_apply t))
  have hax : a * (x : A)⁻¹ ∈ U.comap f := by
    change f (a * (x : A)⁻¹) ∈ U
    rw [map_mul, map_inv, hx, ← hut, mul_inv_cancel_right]
    exact u.property
  exact ⟨⟨⟨a * (x : A)⁻¹, hax⟩, x⟩, inv_mul_cancel_right _ _⟩

end MonoidHom
