module

public import Theory.Representation.BinaryPermutation.SixCoreOrbits

/-!
# Constant-weight subgroups of the binary six-letter module

A subgroup whose nonzero words all have weight two, or all have weight four,
has order at most four. For three independent words, each active coordinate
contributes exactly four to the sum of the seven nonzero combination weights.
That sum is divisible by four and at most twenty-four, whereas constant
weight would make it fourteen or twenty-eight. This avoids enumeration of
triples of words and applies also to injectively marked abstract groups.

Source: Aschbacher–Smith 13.4.16–17, printed pp.913–914.
-/

public noncomputable section
namespace BinaryPermutation
private def bit (x : ZMod 2) : ℕ := if x = 0 then 0 else 1
private theorem bit_triple (a b c : ZMod 2) :
    bit a + bit b + bit c + bit (a+b) + bit (a+c) + bit (b+c) + bit (a+b+c) =
      4 * (if a = 0 ∧ b = 0 ∧ c = 0 then 0 else 1) := by
  revert a b c
  decide
private theorem weight_sum (v : Full (Fin 6)) : wordWeight v = ∑ i, bit (v i) := by
  simp [wordWeight, bit, Finset.sum_ite, Finset.filter_not]
private theorem triple_weight (v w x : Full (Fin 6)) :
    wordWeight v + wordWeight w + wordWeight x + wordWeight (v+w) +
      wordWeight (v+x) + wordWeight (w+x) + wordWeight (v+w+x) =
    4 * (Finset.univ.filter (fun i => ¬ (v i = 0 ∧ w i = 0 ∧ x i = 0))).card := by
  simp only [weight_sum, Pi.add_apply, ← Finset.sum_add_distrib, bit_triple]
  rw [← Finset.mul_sum]
  congr 1
  simp [Finset.sum_ite]


/-- A constant-weight binary subgroup on six coordinates has rank at most two. -/
theorem six_constant_weight_card_le_four (U : AddSubgroup (Full (Fin 6))) (k : ℕ)
    (hk : k = 2 ∨ k = 4) (hw : ∀ x ∈ U, x ≠ 0 → wordWeight x = k) :
    Nat.card U ≤ 4 := by
  classical
  have bound (v w : Full (Fin 6)) (h : ∀ x ∈ U, x = 0 ∨ x = v ∨ x = w ∨ x = v+w) :
      Nat.card U ≤ 4 := by
    let s : Finset (Full (Fin 6)) := {0,v,w,v+w}
    let f : U → s := fun x => ⟨x.val, by simpa [s] using h x.val x.property⟩
    have hh := Nat.card_le_card_of_injective f (fun a b he => Subtype.ext (show a.val = b.val from congrArg (fun z : s => z.val) he))
    have hs : s.card ≤ 4 := (Finset.card_insert_le _ _).trans
      (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans
        (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans
          (by simp)))))
    exact hh.trans (by simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using hs)
  by_cases hv : ∃ v ∈ U, v ≠ 0
  swap
  · apply bound 0 0
    intro x hx
    exact Or.inl (by by_contra hh; exact hv ⟨x,hx,hh⟩)
  obtain ⟨v,hvU,hv0⟩ := hv
  by_cases hw' : ∃ w ∈ U, w ≠ 0 ∧ w ≠ v
  swap
  · apply bound v 0
    intro x hx
    by_cases hx0 : x = 0
    · exact Or.inl hx0
    · exact Or.inr (Or.inl (by by_contra hh; exact hw' ⟨x,hx,hx0,hh⟩))
  obtain ⟨w,hwU,hw0,hwv⟩ := hw'
  apply bound v w
  intro x hxU
  by_contra hx
  have hxs : x ≠ 0 ∧ x ≠ v ∧ x ≠ w ∧ x ≠ v+w := by simpa only [not_or] using hx
  have hvw : v+w ≠ 0 := fun he => hwv (funext fun i => (CharTwo.add_eq_zero.mp (congrFun he i)).symm)
  have hvx : v+x ≠ 0 := fun he => hxs.2.1 (funext fun i => (CharTwo.add_eq_zero.mp (congrFun he i)).symm)
  have hwx : w+x ≠ 0 := fun he => hxs.2.2.1 (funext fun i => (CharTwo.add_eq_zero.mp (congrFun he i)).symm)
  have hvwx : v+w+x ≠ 0 := fun he => hxs.2.2.2 (funext fun i => (CharTwo.add_eq_zero.mp (congrFun he i)).symm)
  have ht := triple_weight v w x
  rw [hw _ hvU hv0, hw _ hwU hw0, hw _ hxU hxs.1,
    hw _ (U.add_mem hvU hwU) hvw, hw _ (U.add_mem hvU hxU) hvx,
    hw _ (U.add_mem hwU hxU) hwx,
    hw _ (U.add_mem (U.add_mem hvU hwU) hxU) hvwx] at ht
  have hc : (Finset.univ.filter (fun i => ¬ (v i = 0 ∧ w i = 0 ∧ x i = 0))).card ≤ 6 :=
    (Finset.card_filter_le _ _).trans (by simp)
  rcases hk with rfl | rfl <;> omega


/-- The bound transports along the actual injective coordinate homomorphism. -/
theorem six_constant_weight_card_le_four_of_injective
    {A : Type*} [Group A] (f : A →* Multiplicative (Full (Fin 6)))
    (hf : Function.Injective f) (k : ℕ) (hk : k = 2 ∨ k = 4)
    (hw : ∀ a : A, a ≠ 1 → wordWeight (f a).toAdd = k) : Nat.card A ≤ 4 := by
  let U := f.range.toAddSubgroup'
  let j : A → U := fun a => ⟨(f a).toAdd, ⟨a,rfl⟩⟩
  have hj : Function.Injective j := by
    intro a b he
    exact hf (Multiplicative.toAdd.injective (congrArg (fun u : U => u.val) he))
  apply (Nat.card_le_card_of_injective j hj).trans
  apply six_constant_weight_card_le_four U k hk
  intro x hx hx0
  obtain ⟨a,ha⟩ := hx
  have ha1 : a ≠ 1 := by
    intro he
    subst a
    rw [map_one] at ha
    exact hx0 (congrArg Multiplicative.toAdd ha.symm)
  rw [← show (f a).toAdd = x from congrArg Multiplicative.toAdd ha]
  exact hw a ha1

local instance : DecidablePred (· ∈ core (Fin 6)) := fun x =>
  inferInstanceAs (Decidable ((∑ i, x i) = 0))
local instance : Fintype (core (Fin 6)) := Subtype.fintype _

/-- The two nonconstant weight classes of the original augmentation core. -/
theorem sixCore_nonconstant_weight (v : core (Fin 6)) (h0 : v ≠ 0)
    (hc : v ≠ sixCoreConstant) : wordWeight v.val = 2 ∨ wordWeight v.val = 4 := by
  revert v
  decide +kernel

/-- Multiplying by the fixed generator complements the six coordinates. -/
theorem sixCore_complement_weight (v : core (Fin 6)) :
    wordWeight (v + sixCoreConstant).val = 6 - wordWeight v.val := by
  revert v
  decide +kernel

end BinaryPermutation
