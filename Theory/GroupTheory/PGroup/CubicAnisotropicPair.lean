module
public import Theory.GroupTheory.PGroup.AnisotropicFactors
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.PGroup.ExtraspecialInvolution
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
/-!
# Cubic conjugates of anisotropic subgroups

A fixed-point-free cubic on a group with center of order four is transitive
on the nonidentity center. It therefore balances the three nonidentity
square fibers. If an order-sixteen subgroup in a class-two group of order
sixty-four has one constant nontrivial square outside the center, its cubic
conjugate has a different square value. Their intersection is exactly the
center, and the product-order formula proves that they generate the group.

An index-two intersection with an extraspecial group of order thirty-two
provides the first anisotropic subgroup when its involutions are central
in the other group.

These are intrinsic inputs to recognition by anisotropic factors. They do
not assert the further factor-centralizer hypothesis or identify a model.
Source application: Delgado--Goldschmidt--Stellmacher, Groups and Graphs
(1985), proof of (10.9), printed p.163, followed by (5.16), pp.116--117.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory

private theorem cubic_four_orbit {X : Type*} [Group X] [Finite X]
    (hX : Nat.card X = 4) (a : MulAut X) (ha : a ^ 3 = 1)
    (hf : ∀ x, a x = x → x = 1) (x : X) (hx : x ≠ 1) (y : X) :
    y = 1 ∨ y = x ∨ y = a x ∨ y = a (a x) := by
  classical
  let := Fintype.ofFinite X
  have h1 : a x ≠ 1 := by simpa using hx
  have h2 : a (a x) ≠ 1 := by simpa using hx
  have h01 : x ≠ a x := fun he => hx (hf x he.symm)
  have h12 : a x ≠ a (a x) := fun he => h01 (a.injective he)
  have hc : a (a (a x)) = x := by
    have hh := congrArg (fun b : MulAut X => b x) ha
    simpa only [pow_succ, pow_zero, MulAut.mul_apply, MulAut.one_apply] using hh
  have h02 : x ≠ a (a x) := by
    intro he
    have hh := congrArg a he
    rw [hc] at hh
    exact h01 hh.symm
  have hs : ({1,x,a x,a (a x)} : Finset X) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [←Nat.card_eq_fintype_card,hX]
    simp [h01,h02,h12,Ne.symm hx,Ne.symm h1,Ne.symm h2]
  have hm : y ∈ ({1,x,a x,a (a x)} : Finset X) := hs.symm ▸ Finset.mem_univ y
  simpa only [Finset.mem_insert,Finset.mem_singleton] using hm

/-- A fixed-free cubic balances the three nonidentity square fibers over a center of order four. -/
theorem square_fibers_balanced_of_fixed_free_cubic
    {H : Type*} [Group H] [Finite H] (hZ : Nat.card (center H) = 4)
    (a : MulAut H) (ha : a ^ 3 = 1) (hf : ∀ x, a x = x → x = 1)
    (z u : center H) (hz : z ≠ 1) (hu : u ≠ 1) :
    Nat.card {x : H // x ^ 2 = (z : H)} = Nat.card {x : H // x ^ 2 = (u : H)} := by
  let b := MulAut.characteristic (center H) a
  have hb : b ^ 3 = 1 := by rw [←map_pow,ha,map_one]
  have hbf : ∀ x, b x = x → x = 1 := by
    intro x hx
    exact Subtype.ext (hf x (congrArg Subtype.val hx))
  rcases cubic_four_orbit hZ b hb hbf z hz u with h | h | h | h
  · exact (hu h).elim
  · subst u
    rfl
  · have hh := squareFiber_card_eq a (z : H)
    rw [h]
    exact hh
  · have hh := squareFiber_card_eq (a*a) (z : H)
    rw [h]
    exact hh

/-- An anisotropic sixteen and its cubic conjugate generate a special sixty-four.
The intersection and square values refer to the actual subgroup images. -/
theorem anisotropic_pair_of_fixed_free_cubic
    {H : Type*} [Group H] [Finite H]
    (hH : Nat.card H = 64) (hZ : Nat.card (center H) = 4)
    (hclass : commutator H ≤ center H)
    (a : MulAut H) (ha : a ^ 3 = 1) (hf : ∀ x, a x = x → x = 1)
    (A : Subgroup H) (hA : Nat.card A = 16) (hZA : center H ≤ A)
    (z : center H) (hz : z ≠ 1)
    (hs : ∀ x ∈ A, x ∉ center H → x ^ 2 = (z : H)) :
    ∃ u : center H, u ≠ 1 ∧ z ≠ u ∧
      Nat.card (A.map a.toMonoidHom) = 16 ∧
      A ⊓ A.map a.toMonoidHom = center H ∧
      A ⊔ A.map a.toMonoidHom = ⊤ ∧
      (∀ x ∈ A.map a.toMonoidHom, x ∉ center H → x ^ 2 = (u : H)) ∧
      (∀ z' u' : center H, z' ≠ 1 → u' ≠ 1 →
        Nat.card {x : H // x ^ 2 = (z' : H)} =
          Nat.card {x : H // x ^ 2 = (u' : H)}) := by
  let b := MulAut.characteristic (center H) a
  let u : center H := b z
  have hu : u ≠ 1 := by
    change b z ≠ 1
    simpa using hz
  have hzu : z ≠ u := by
    intro he
    apply hz
    exact Subtype.ext (hf z (congrArg Subtype.val he.symm))
  have hB : Nat.card (A.map a.toMonoidHom) = 16 := by
    rw [card_map_of_injective a.injective,hA]
  have hsB : ∀ x ∈ A.map a.toMonoidHom, x ∉ center H → x ^ 2 = (u : H) := by
    rintro x ⟨y,hy,rfl⟩ hn
    have hyn : y ∉ center H := by
      intro hyZ
      exact hn ((b ⟨y,hyZ⟩).property)
    change a y ^ 2 = a (z : H)
    exact (map_pow a y 2).symm.trans (congrArg a (hs y hy hyn))
  have hZB : center H ≤ A.map a.toMonoidHom := by
    intro x hx
    refine ⟨a.symm x,hZA ((MulAut.characteristic (center H) a.symm ⟨x,hx⟩).property),?_⟩
    exact a.apply_symm_apply x
  have hi : A ⊓ A.map a.toMonoidHom = center H := by
    apply le_antisymm
    · intro x hx
      by_contra hn
      exact hzu (Subtype.ext ((hs x hx.1 hn).symm.trans (hsB x hx.2 hn)))
    · exact le_inf hZA hZB
  let : A.Normal := Normal.of_commutator_le H (hclass.trans hZA)
  have hg : A ⊔ A.map a.toMonoidHom = ⊤ := by
    have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes A (A.map a.toMonoidHom)
      le_normalizer_of_normal
    rw [hA,hB,hi,hZ] at hc
    apply eq_top_of_card_eq
    omega
  exact ⟨u,hu,hzu,hB,hi,hg,hsB,square_fibers_balanced_of_fixed_free_cubic hZ a ha hf⟩
/-- An index-two intersection with an extraspecial thirty-two has a single
nonidentity square value if its involutions are central in the other group. -/
theorem extraspecial_anisotropic_intersection
    {G : Type*} [Group G] (Q R : Subgroup G) [Finite R] [IsExtraspecial 2 R]
    (hR : Nat.card R = 32) (hi : Q.relIndex R = 2)
    (hc : (center R).map R.subtype ≤ (center Q).map Q.subtype)
    (hsq : ∀ x ∈ Q ⊓ R, x ^ 2 = 1 → x ∈ (center Q).map Q.subtype) :
    Nat.card (R.subgroupOf Q) = 16 ∧
      ∃ z : center Q, z ≠ 1 ∧
        ∀ x ∈ R.subgroupOf Q, x ∉ center Q → x ^ 2 = (z : Q) := by
  have hmem (x : Q) : (x : G) ∈ (center Q).map Q.subtype ↔ x ∈ center Q := by
    constructor
    · rintro ⟨y,hy,he⟩
      exact Q.subtype_injective he ▸ hy
    · exact mem_map_of_mem Q.subtype
  have hRI : Nat.card (Q.subgroupOf R) = 16 := by
    have hh := (Q.subgroupOf R).card_mul_index
    change Nat.card (Q.subgroupOf R) * Q.relIndex R = Nat.card R at hh
    rw [hi,hR] at hh
    omega
  let ei : R.subgroupOf Q ≃ Q.subgroupOf R := {
    toFun x := ⟨⟨x,x.property⟩,x.val.property⟩
    invFun x := ⟨⟨x,x.property⟩,x.val.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  have hA : Nat.card (R.subgroupOf Q) = 16 := (Nat.card_congr ei).trans hRI
  obtain ⟨z,hz,hunique⟩ := (Nat.card_eq_two_iff' (1 : center R)).mp
    (IsExtraspecial.center_order_p 2 R)
  have hzZ : ((z : R) : G) ∈ (center Q).map Q.subtype :=
    hc (mem_map_of_mem R.subtype z.property)
  have hzQ : ((z : R) : G) ∈ Q := map_subtype_le _ hzZ
  let z₀ : center Q := ⟨⟨((z : R) : G),hzQ⟩,(hmem _).mp hzZ⟩
  have hz₀ : z₀ ≠ 1 := by
    intro he
    apply hz
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun w : center Q => ((w : Q) : G)) he
  refine ⟨hA,z₀,hz₀,?_⟩
  intro x hx hn
  let y : R := ⟨x,hx⟩
  have hyn : y^2 ≠ 1 := by
    intro hy
    apply hn
    apply (hmem x).mp
    exact hsq x ⟨x.property,hx⟩ (congrArg (fun q : R => (q : G)) hy)
  have he := hunique ⟨y^2,IsExtraspecial.square_mem_center y⟩
    (fun hh => hyn (congrArg Subtype.val hh))
  exact Subtype.ext (congrArg (fun w : center R => ((w : R) : G)) he)

end Theory.GroupTheory
