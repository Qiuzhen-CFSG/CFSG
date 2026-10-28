module
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.Fintype.EquivFin
/-!
# Additive functions constant away from the identity

An additive function constant on the nonidentity elements of a group of
order greater than two vanishes. This elementary cancellation argument
identifies singular lines from regular torus orbits in the orthogonal cover.
-/
public section

/-- An additive function on a finite group cannot have one constant value
on its nonidentity elements when the group has order greater than two. -/
theorem constant_nonidentity_additive_eq_zero
    {W A : Type*} [Group W] [Finite W] [AddGroup A]
    (f : W → A) (hf : ∀ a b, f (a*b)=f a+f b)
    (hc : 2<Nat.card W) (hconst : ∀ a≠1,∀ b≠1,f a=f b) : ∀a,f a=0 := by
  classical
  let := Fintype.ofFinite W
  have hzero : f 1=0 := by
    have hh := hf 1 1
    rw [one_mul] at hh
    exact add_left_cancel (a := f 1) (by simpa only [add_zero] using hh.symm)
  intro a
  by_cases ha : a=1
  · exact ha ▸ hzero
  have hcard : ({1,a} : Finset W).card < (Finset.univ : Finset W).card := by
    have hp : ({1,a} : Finset W).card ≤ 2 := by exact Finset.card_insert_le _ _ |>.trans (by simp)
    simpa only [Finset.card_univ,←Nat.card_eq_fintype_card] using lt_of_le_of_lt hp hc
  obtain ⟨b,_,hb⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hb' : b≠1 ∧ b≠a := by simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using hb
  have hd : a*b⁻¹≠1 := fun he => hb'.2 (mul_inv_eq_one.mp he).symm
  have hi : b⁻¹≠1 := inv_ne_one.mpr hb'.1
  have hh := hf a b⁻¹
  rw [hconst _ hd a ha,hconst _ hi a ha] at hh
  exact add_left_cancel (a := f a) (by simpa only [add_zero] using hh.symm)
