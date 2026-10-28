module
public import Theory.Representation.BinaryPermutation.SixCoreOrbits
public import Theory.ElementaryAbelian.Basic

/-!
# Involutions on planes in quotients of the six-letter even core

Distinct even words of equal weight are exchanged by an even involution.
The finite certificate enumerates the 45 double transpositions. For a
four-group in an equivariant quotient of the even core, avoiding the
constant image forces every lift of a nonidentity point to have weight
two or four. Three points and two weights give a pair with distinct images.
The certified involution therefore preserves and moves the entire plane.

The application is to the original moving plane inside the full covered
M₂₂ hexad core, retaining its central kernel. A general plane containing
the constant line need not satisfy this conclusion.

Source: Aschbacher--Smith B.3.3 and I.2.2(6), printed pp.84 and412;
the original 15.1.20(2) setting, printed p.1094.
-/

public section
namespace BinaryPermutation

open Equiv

private def swaps : Fin 45 → Fin 4 → Fin 6 := ![
  ![0, 1, 2, 3],
  ![0, 2, 1, 3],
  ![0, 3, 1, 2],
  ![0, 1, 2, 4],
  ![0, 2, 1, 4],
  ![0, 4, 1, 2],
  ![0, 1, 2, 5],
  ![0, 2, 1, 5],
  ![0, 5, 1, 2],
  ![0, 1, 3, 4],
  ![0, 3, 1, 4],
  ![0, 4, 1, 3],
  ![0, 1, 3, 5],
  ![0, 3, 1, 5],
  ![0, 5, 1, 3],
  ![0, 1, 4, 5],
  ![0, 4, 1, 5],
  ![0, 5, 1, 4],
  ![0, 2, 3, 4],
  ![0, 3, 2, 4],
  ![0, 4, 2, 3],
  ![0, 2, 3, 5],
  ![0, 3, 2, 5],
  ![0, 5, 2, 3],
  ![0, 2, 4, 5],
  ![0, 4, 2, 5],
  ![0, 5, 2, 4],
  ![0, 3, 4, 5],
  ![0, 4, 3, 5],
  ![0, 5, 3, 4],
  ![1, 2, 3, 4],
  ![1, 3, 2, 4],
  ![1, 4, 2, 3],
  ![1, 2, 3, 5],
  ![1, 3, 2, 5],
  ![1, 5, 2, 3],
  ![1, 2, 4, 5],
  ![1, 4, 2, 5],
  ![1, 5, 2, 4],
  ![1, 3, 4, 5],
  ![1, 4, 3, 5],
  ![1, 5, 3, 4],
  ![2, 3, 4, 5],
  ![2, 4, 3, 5],
  ![2, 5, 3, 4]]
private def actor (i : Fin 45) : Equiv.Perm (Fin 6) :=
  Equiv.swap (swaps i 0) (swaps i 1) * Equiv.swap (swaps i 2) (swaps i 3)

private theorem actor_facts (i : Fin 45) :
    actor i ∈ alternatingGroup (Fin 6) ∧ actor i ^ 2 = 1 := by
  have h : ∀ i : Fin 45, (actor i).sign = 1 ∧ actor i ^ 2 = 1 := by decide +kernel
  exact ⟨Equiv.Perm.mem_alternatingGroup.mpr (h i).1,(h i).2⟩

private def eligible (u v : Fin 6 → ZMod 2) : Bool :=
  decide ((∑ i, u i) = 0) && decide ((∑ i, v i) = 0) &&
  decide (wordWeight u = wordWeight v) && decide (u ≠ v)
private def checkPair (u v : Fin 6 → ZMod 2) : Bool :=
  decide (∃ i : Fin 45, ∀ j, u (actor i j) = v j)
private theorem pair_check :
    ∀ u v : Fin 6 → ZMod 2, eligible u v = true → checkPair u v = true := by
  decide +kernel
private theorem pair_certificate (u v : Fin 6 → ZMod 2)
    (hu : (∑ i, u i) = 0) (hv : (∑ i, v i) = 0)
    (hw : wordWeight u = wordWeight v) (hn : u ≠ v) :
    ∃ i : Fin 45, ∀ j, u (actor i j) = v j := by
  have h := pair_check u v (by simp [eligible,hu,hv,hw,hn])
  exact of_decide_eq_true h

/-- Equal-weight distinct even six-letter words can be exchanged by an
actual even involution. Its action on their span is a transvection. -/
theorem even_pair_involution (u v : core (Fin 6))
    (hw : wordWeight u.val = wordWeight v.val) (hne : u ≠ v) :
    ∃ a : alternatingGroup (Fin 6), a ^ 2 = 1 ∧
      alternatingCoreRepresentation (Fin 6) a u = v ∧
      alternatingCoreRepresentation (Fin 6) a v = u := by
  obtain ⟨i,hi⟩ := pair_certificate u.val v.val u.property v.property hw
    (fun he => hne (Subtype.ext he))
  let a : alternatingGroup (Fin 6) := ⟨actor i,(actor_facts i).1⟩
  have ha : a ^ 2 = 1 := Subtype.ext (actor_facts i).2
  have hai : (actor i).symm = actor i := by
    exact inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using (actor_facts i).2)
  have huv : alternatingCoreRepresentation (Fin 6) a u = v := by
    apply Subtype.ext
    funext j
    change u.val ((actor i).symm j) = v.val j
    rw [hai]
    exact hi j
  refine ⟨a,ha,huv,?_⟩
  rw [←huv]
  change ((alternatingCoreRepresentation (Fin 6)) a *
    (alternatingCoreRepresentation (Fin 6)) a) u = u
  rw [←map_mul,←pow_two,ha,map_one]
  rfl


open Subgroup
open scoped IsMulCommutative
local instance : DecidablePred (· ∈ core (Fin 6)) := fun x =>
  inferInstanceAs (Decidable ((∑ i, x i) = 0))
local instance : Fintype (core (Fin 6)) := Subtype.fintype _

private theorem nonconstant_weights (v : core (Fin 6)) (h0 : v ≠ 0)
    (hz : v ≠ sixCoreConstant) : wordWeight v.val = 2 ∨ wordWeight v.val = 4 := by
  revert v
  decide +kernel

/-- In a four-group avoiding the constant image, some distinct nonidentity
points have equal-weight lifts through any surjection from the even core. -/
theorem four_group_equal_weight_lifts
    {D : Type*} [Group D] [Finite D] (b : Multiplicative (core (Fin 6)) →* D)
    (hb : Function.Surjective b) (W : Subgroup D) (hc : Nat.card W = 4)
    (hz : b (Multiplicative.ofAdd sixCoreConstant) ∈ W →
      b (Multiplicative.ofAdd sixCoreConstant) = 1) :
    ∃ u v : core (Fin 6),
      b (Multiplicative.ofAdd u) ∈ W ∧ b (Multiplicative.ofAdd v) ∈ W ∧
      b (Multiplicative.ofAdd u) ≠ 1 ∧ b (Multiplicative.ofAdd v) ≠ 1 ∧
      b (Multiplicative.ofAdd u) ≠ b (Multiplicative.ofAdd v) ∧
      wordWeight u.val = wordWeight v.val := by
  classical
  let : Fintype W := Fintype.ofFinite W
  choose f hf using hb
  let u (w : W) : core (Fin 6) := (f w.val).toAdd
  have hu (w : W) : b (Multiplicative.ofAdd (u w)) = w := hf w.val
  have hw (w : W) (hn : w ≠ 1) :
      wordWeight (u w).val = 2 ∨ wordWeight (u w).val = 4 := by
    apply nonconstant_weights
    · intro he
      apply hn
      apply Subtype.ext
      rw [←hu w,he]
      exact b.map_one
    · intro he
      apply hn
      apply Subtype.ext
      have hm : b (Multiplicative.ofAdd sixCoreConstant) = w := he ▸ hu w
      exact hm.symm.trans (hz (hm ▸ w.property))
  by_contra h
  have hpair (x y : W) (hx : x ≠ 1) (hy : y ≠ 1)
      (he : wordWeight (u x).val = wordWeight (u y).val) : x = y := by
    by_contra hxy
    apply h
    refine ⟨u x,u y,?_,?_,?_,?_,?_,he⟩
    · rw [hu]; exact x.property
    · rw [hu]; exact y.property
    · rw [hu]; exact fun hh => hx (Subtype.ext hh)
    · rw [hu]; exact fun hh => hy (Subtype.ext hh)
    · rw [hu,hu]; exact fun hh => hxy (Subtype.ext hh)
  let color (w : W) : Fin 3 :=
    if w = 1 then 0 else if wordWeight (u w).val = 2 then 1 else 2
  have hi : Function.Injective color := by
    intro x y he
    by_cases hx : x = 1
    · by_cases hy : y = 1
      · exact hx.trans hy.symm
      · simp only [color,hx,hy,ite_true,ite_false] at he
        split_ifs at he <;> contradiction
    by_cases hy : y = 1
    · simp only [color,hx,hy,ite_true,ite_false] at he
      split_ifs at he <;> contradiction
    apply hpair x y hx hy
    have hwx := hw x hx
    have hwy := hw y hy
    simp only [color,hx,hy,ite_false] at he
    split_ifs at he <;> simp_all
  have hbound := Nat.card_le_card_of_injective color hi
  rw [hc,Nat.card_fin] at hbound
  omega

private theorem four_group_cases
    {D : Type*} [Group D] [Finite D] (W : Subgroup D)
    [IsElementaryAbelian 2 W] (hc : Nat.card W = 4)
    (x y : W) (hx : x ≠ 1) (hy : y ≠ 1) (hxy : x ≠ y) (w : W) :
    w = 1 ∨ w = x ∨ w = y ∨ w = x*y := by
  classical
  let : Fintype W := Fintype.ofFinite W
  have hx2 : x*x = 1 := by
    simpa only [pow_two] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 W) x
  have hxy1 : x*y ≠ 1 := by
    intro he
    apply hxy
    have hh := congrArg (fun z : W => x*z) he
    simpa only [←mul_assoc,hx2,one_mul,mul_one] using hh.symm
  have hs : ({1,x,y,x*y} : Finset W).card = 4 := by
    have hyx : y ≠ x*y := fun he => hx (mul_right_cancel (he.symm.trans (one_mul y).symm))
    have hxx : x ≠ x*y := fun he => hy (mul_left_cancel (he.symm.trans (mul_one x).symm))
    exact Finset.card_eq_four.mpr ⟨1,x,y,x*y,hx.symm,hy.symm,hxy1.symm,hxy,hxx,hyx,rfl⟩
  have he : ({1,x,y,x*y} : Finset W) = Finset.univ :=
    Finset.eq_univ_of_card _ (by simpa only [←Nat.card_eq_fintype_card,hc] using hs)
  have hm : w ∈ ({1,x,y,x*y} : Finset W) := he ▸ Finset.mem_univ w
  simpa only [Finset.mem_insert,Finset.mem_singleton] using hm

/-- An elementary plane disjoint from the constant image has an actual even
involution acting nontrivially on it, in the full quotient of the even core. -/
theorem four_group_involution
    {D : Type*} [Group D] [Finite D]
    (φ : alternatingGroup (Fin 6) →* MulAut D)
    (b : Multiplicative (core (Fin 6)) →* D) (hb : Function.Surjective b)
    (he : ∀ a v, b (Multiplicative.ofAdd
      (alternatingCoreRepresentation (Fin 6) a v.toAdd)) = φ a (b v))
    (W : Subgroup D) [IsElementaryAbelian 2 W] (hc : Nat.card W = 4)
    (hz : b (Multiplicative.ofAdd sixCoreConstant) ∈ W →
      b (Multiplicative.ofAdd sixCoreConstant) = 1) :
    ∃ a : alternatingGroup (Fin 6), a ^ 2 = 1 ∧
      (∀ w ∈ W, φ a w ∈ W) ∧ ∃ w ∈ W, φ a w ≠ w := by
  obtain ⟨u,v,hu,hv,hu1,hv1,huv,hw⟩ := four_group_equal_weight_lifts b hb W hc hz
  obtain ⟨a,ha,hau,hav⟩ := even_pair_involution u v hw (by
    intro hh; exact huv (congrArg (fun z => b (Multiplicative.ofAdd z)) hh))
  let x : W := ⟨b (Multiplicative.ofAdd u),hu⟩
  let y : W := ⟨b (Multiplicative.ofAdd v),hv⟩
  have hax : φ a x = y := by
    simpa only [toAdd_ofAdd,hau] using (he a (Multiplicative.ofAdd u)).symm
  have hay : φ a y = x := by
    simpa only [toAdd_ofAdd,hav] using (he a (Multiplicative.ofAdd v)).symm
  refine ⟨a,ha,?_,x,x.property,fun hh => huv (hh.symm.trans hax)⟩
  intro w hw
  rcases four_group_cases W hc x y
      (fun hh => hu1 (congrArg Subtype.val hh))
      (fun hh => hv1 (congrArg Subtype.val hh))
      (fun hh => huv (congrArg Subtype.val hh)) ⟨w,hw⟩ with h1 | hx | hy | hxy
  · have hh : w = 1 := congrArg Subtype.val h1
    simp only [hh,map_one,one_mem]
  · have hh : w = x.val := congrArg Subtype.val hx
    rw [hh,hax]; exact y.property
  · have hh : w = y.val := congrArg Subtype.val hy
    rw [hh,hay]; exact x.property
  · have hh := congrArg Subtype.val hxy
    change w = x.val*y.val at hh
    rw [hh,map_mul,hax,hay]
    exact W.mul_mem y.property x.property
end BinaryPermutation
