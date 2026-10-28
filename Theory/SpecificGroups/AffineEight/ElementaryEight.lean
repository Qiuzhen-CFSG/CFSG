module
public import Theory.SpecificGroups.AffineEight.Basic
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.Index

/-!
# Elementary eight subgroups of the affine group over Z/8

Every elementary abelian subgroup of order eight in the actual affine
model is conjugate to `evenElementary`. An involution with odd translation
has at most four commuting square-one elements, so it cannot belong to
such a subgroup. Inside the even-translation subgroup, a commuting pair
calculation puts the whole elementary subgroup in one of two subgroups:
`evenElementary` or its conjugate by translation by one. Both have order
eight, so containment is equality.

The finite calculations use the semidirect product operations and the
translation-divisibility description from `AffineEight.Basic`. This is the
local holomorph-of-C8 geometry used with the transfer argument of
Andersen–Oliver–Ventura, `Fusion systems and amalgams`, Proposition 2.3(b),
author manuscript p.6. No ambient group is identified with this model here.
-/

open scoped IsMulCommutative

namespace AffineEight

private def shift : Model :=
  SemidirectProduct.inl (Multiplicative.ofAdd (1 : ZMod 8))

private def otherElementary : Subgroup Model :=
  evenElementary.map (MulAut.conj shift).toMonoidHom

private instance : DecidablePred (· ∈ evenElementary) := fun x =>
  decidable_of_iff (x.left.toAdd.val % 4 = 0) (mem_evenElementary_iff x).symm

private instance : DecidablePred (· ∈ otherElementary) := fun x =>
  decidable_of_iff ((MulAut.conj shift).symm x ∈ evenElementary)
    (Subgroup.mem_map_equiv (f := MulAut.conj shift) (K := evenElementary)).symm

private theorem odd_translation_bound : ∀ x : Model,
    x ^ 2 = 1 → x.left.toAdd.val % 2 ≠ 0 →
      Fintype.card {y : Model // y ^ 2 = 1 ∧ x * y = y * x} ≤ 4 := by
  decide

private theorem pair_cover : ∀ x y : Model,
    x ^ 2 = 1 → y ^ 2 = 1 →
    x.left.toAdd.val % 2 = 0 → y.left.toAdd.val % 2 = 0 →
    x * y = y * x → x ∉ evenElementary → y ∈ otherElementary := by
  decide

public theorem evenElementary_isElementaryAbelian :
    IsElementaryAbelian 2 evenElementary := by
  refine {
    toIsMulCommutative := ⟨⟨?_⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_
  }
  · decide
  · decide

public theorem card_evenElementary : Nat.card evenElementary = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide

/-- A group of elementary two-rank at most two cannot contain the holomorph of C₈.
The obstruction is its explicit elementary subgroup of order eight. -/
public theorem not_injective_of_elementary_card_lt_eight
    {G : Type*} [Group G]
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (f : Model →* G) : ¬ Function.Injective f := by
  intro hinj
  let : IsElementaryAbelian 2 evenElementary := evenElementary_isElementaryAbelian
  have hA : IsElementaryAbelian 2 (evenElementary.map f) := IsElementaryAbelian.map f
  have hlt := hrank (evenElementary.map f) hA
  rw [Subgroup.card_map_of_injective hinj, card_evenElementary] at hlt
  omega

private theorem otherElementary_card : Nat.card otherElementary = 8 := by
  exact (Nat.card_congr
    ((MulAut.conj shift).subgroupMap evenElementary).toEquiv).symm.trans card_evenElementary

public theorem exists_conj_evenElementary
    (A : Subgroup Model) (hA : IsElementaryAbelian 2 A) (hcard : Nat.card A = 8) :
    ∃ g : Model, A = evenElementary.map (MulAut.conj g).toMonoidHom := by
  classical
  let := hA
  have hpow (x : Model) (hx : x ∈ A) : x ^ 2 = 1 :=
    elemPow_eq_one_of_isElementaryAbelian x hx
  have hcomm (x y : Model) (hx : x ∈ A) (hy : y ∈ A) : x * y = y * x :=
    congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : A) ⟨y, hy⟩)
  have heven (x : Model) (hx : x ∈ A) : x.left.toAdd.val % 2 = 0 := by
    by_contra hodd
    let f : A → {y : Model // y ^ 2 = 1 ∧ x * y = y * x} :=
      fun y => ⟨y, hpow y y.property, hcomm x y hx y.property⟩
    have hf : Function.Injective f := fun a b h =>
      Subtype.ext (congrArg (fun y : {y : Model // y ^ 2 = 1 ∧ x * y = y * x} =>
        (y : Model)) h)
    have hle := Nat.card_le_card_of_injective f hf
    rw [hcard, Nat.card_eq_fintype_card] at hle
    have hbound := odd_translation_bound x (hpow x hx) hodd
    omega
  by_cases hle : A ≤ evenElementary
  · have heq : A = evenElementary :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [card_evenElementary, hcard])
    refine ⟨1, ?_⟩
    have hid : (MulAut.conj (1 : Model)).toMonoidHom = MonoidHom.id Model := by
      apply MonoidHom.ext
      intro x
      change (1 : Model) * x * 1⁻¹ = x
      simp
    simpa only [hid, Subgroup.map_id] using heq
  · obtain ⟨x, hx, hxnot⟩ := SetLike.not_le_iff_exists.mp hle
    have hother : A ≤ otherElementary := by
      intro y hy
      exact pair_cover x y (hpow x hx) (hpow y hy)
        (heven x hx) (heven y hy) (hcomm x y hx hy) hxnot
    refine ⟨shift, ?_⟩
    change A = otherElementary
    exact Subgroup.eq_of_le_of_card_ge hother
      (by rw [otherElementary_card, hcard])

end AffineEight
