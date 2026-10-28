module
public import Theory.GroupAction.KleinFourFactorization

/-!
# Cubic fixed points under a fixed-point-free four-group

Let two commuting involutions act on a finite abelian group of odd order,
with trivial common fixed subgroup. If a cubic automorphism cycles the
three nontrivial characters of this four-group, the order of its fixed
subgroup cubed is the group order.

The unique fixed/inverted decomposition identifies the group with three
copies of one character factor. In these actual coordinates the cubic
rotates the three factors, and its fixed subgroup is the diagonal.

This is the action calculation in Bender, *Finite groups with large
subgroups* (1974), proof of (4.1), printed p.225. The result applies to any
odd abelian group; no elementary-abelian or faithfulness assumption is needed.
-/

namespace Theory.GroupAction
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] [IsMulCommutative G]

/-- A cubic cycling the three nontrivial Klein-four characters has a fixed
subgroup whose order is the cube root of the group order. -/
public theorem cubic_fixed_card_cube
    (hodd : Odd (Nat.card G)) (a b t : MulAut G)
    (ha : Function.Involutive a) (hb : Function.Involutive b) (hab : Commute a b)
    (ht : ∀ x, t (t (t x)) = x)
    (hat : ∀ x, a (t x) = t (a (b x)))
    (hbt : ∀ x, b (t x) = t (a x))
    (hcommon : ∀ x, a x = x → b x = x → x = 1) :
    Nat.card (MulAut.fixedSubgroup t) ^ 3 = Nat.card G := by
  let U := {x : G // a x = x ∧ b x = x⁻¹}
  let W := {x : G // a x = x⁻¹ ∧ b x = x}
  let Z := {x : G // a x = x⁻¹ ∧ b x = x⁻¹}
  have huw (x : G) (hx : a x = x ∧ b x = x⁻¹) :
      a (t x) = (t x)⁻¹ ∧ b (t x) = t x := by
    simp only [hat, hbt, hx.2, map_inv, hx.1, and_self]
  have hwz (x : G) (hx : a x = x⁻¹ ∧ b x = x) :
      a (t x) = (t x)⁻¹ ∧ b (t x) = (t x)⁻¹ := by
    simp only [hat, hbt, hx.2, hx.1, map_inv, and_self]
  have hzu (x : G) (hx : a x = x⁻¹ ∧ b x = x⁻¹) :
      a (t x) = t x ∧ b (t x) = (t x)⁻¹ := by
    simp only [hat, hbt, hx.2, map_inv, hx.1, inv_inv, and_self]
  let m : U × U × U → G := fun p => p.1.val * t p.2.1.val * t (t p.2.2.val)
  have hinj : Function.Injective m := by
    intro p q he
    have hf := (MulAut.fixed_inverted_four_factor_bijective hodd a b ha hb hab).injective
    let lift (p : U × U × U) :
        {h : G // a h = h ∧ b h = h} × U × W × Z :=
      (⟨1, by simp⟩, p.1, ⟨t p.2.1, huw _ p.2.1.property⟩,
        ⟨t (t p.2.2), hwz _ (huw _ p.2.2.property)⟩)
    have he' : lift p = lift q := hf (by simpa only [lift, one_mul] using he)
    have hu : p.1 = q.1 := congrArg (fun r => r.2.1) he'
    have hv : p.2.1 = q.2.1 := Subtype.ext (t.injective
      (congrArg (fun r => r.2.2.1.val) he'))
    have hw : p.2.2 = q.2.2 := Subtype.ext (t.injective (t.injective
      (congrArg (fun r => r.2.2.2.val) he')))
    exact Prod.ext hu (Prod.ext hv hw)
  have hsurj : Function.Surjective m := by
    intro x
    obtain ⟨⟨h,u,v,w⟩, he⟩ :=
      (MulAut.fixed_inverted_four_factor_bijective hodd a b ha hb hab).surjective x
    have hh := hcommon h h.property.1 h.property.2
    refine ⟨(u, ⟨t (t v), hzu _ (hwz _ v.property)⟩,
      ⟨t w, hzu _ w.property⟩), ?_⟩
    change u.val * t (t (t v.val)) * t (t (t w.val)) = x
    simpa only [hh, one_mul, ht] using he
  have hrotate (u v w : U) : t (m (u,v,w)) = m (w,u,v) := by
    dsimp [m]
    rw [map_mul, map_mul, ht]
    ac_rfl
  let d : U → MulAut.fixedSubgroup t := fun u => ⟨m (u,u,u), by simpa only [MulAut.mem_fixedSubgroup] using hrotate u u u⟩
  have hd : Function.Bijective d := by
    constructor
    · intro u v he
      exact congrArg Prod.fst (hinj (congrArg Subtype.val he))
    · intro x
      obtain ⟨⟨u,v,w⟩, he⟩ := hsurj x.val
      have hr : m (w,u,v) = m (u,v,w) := by
        rw [← hrotate, he]
        simpa only [MulAut.mem_fixedSubgroup] using x.property
      have hc := hinj hr
      have hwu : w = u := congrArg Prod.fst hc
      have huv : u = v := congrArg (fun p => p.2.1) hc
      refine ⟨u, Subtype.ext ?_⟩
      change m (u,u,u) = x.val
      simpa only [← huv, hwu] using he
  rw [← Nat.card_congr (Equiv.ofBijective d hd)]
  have hc := Nat.card_congr (Equiv.ofBijective m ⟨hinj,hsurj⟩)
  simpa only [Nat.card_prod, pow_succ, pow_zero, Nat.mul_one, Nat.one_mul, mul_assoc] using hc
end Theory.GroupAction
