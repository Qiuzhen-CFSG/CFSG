module

public import Theory.GroupAction.FixedFreeThreeClassTwo
public import Mathlib.GroupTheory.PGroup

/-!
# Automorphisms moving the involutions of a two-group

Transitivity on a three-element set supplies an automorphism moving every
point. For the involutions of a finite two-group, this automorphism is
fixed-point-free on the whole group: a nontrivial fixed subgroup would have
an involution by Cauchy's theorem. More generally the same criterion works
for elements of prime order in a finite p-group.

When the supplied automorphism has order three, Neumann's theorem then
makes the derived subgroup central. The transitivity result does not assert
order three for its automorphism: lifting a three-cycle from the permutation
image is a separate structural issue.

The permutation argument is the elementary three-point calculation; the
class bound uses B. H. Neumann's theorem as cited in Higman, *Suzuki 2-groups*,
Illinois J. Math. 7 (1963), Lemma 6.
-/

namespace IsPGroup

open Subgroup

/-- An automorphism of a finite p-group fixing no element of order p is fixed-point-free. -/
public theorem fixedPointFree_of_no_fixed_prime_order
    {p : ℕ} [Fact p.Prime] {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup p P) (a : MulAut P)
    (hmove : ∀ x : P, orderOf x = p → a x ≠ x) :
    MonoidHom.FixedPointFree a := by
  let K := a.toMonoidHom.eqLocus (MonoidHom.id P)
  have hK : K = ⊥ := by
    by_contra hne
    have hd : p ∣ Nat.card K :=
      (hP.to_subgroup K).card_eq_or_dvd.resolve_left
        (fun hc => hne (card_eq_one.mp hc))
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := K) p hd
    exact hmove x ((orderOf_coe x).trans hx) x.property
  intro x hx
  have hm : x ∈ K := hx
  simpa only [hK, mem_bot] using hm

private def involutionPermHom (P : Type*) [Group P] :
    MulAut P →* Equiv.Perm {x : P // orderOf x = 2} where
  toFun a := Equiv.Perm.subtypePerm a.toEquiv (fun x => by
    change orderOf (a x) = 2 ↔ orderOf x = 2
    rw [a.orderOf_eq])
  map_one' := by ext x; rfl
  map_mul' a b := by ext x; rfl

private theorem three_point_derangement :
    ∀ a b : Equiv.Perm (Fin 3), a 0 = 1 → b 0 = 2 →
      (∀ x, a x ≠ x) ∨ (∀ x, b x ≠ x) ∨ (∀ x, (a * b) x ≠ x) := by
  decide +kernel

/-- Transitivity on exactly three involutions supplies a fixed-point-free automorphism.
This does not assert that the automorphism has order three. -/
public theorem exists_fixedPointFree_of_three_transitive_involutions
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hthree : Nat.card {x : P // orderOf x = 2} = 3)
    (htrans : ∀ x y : P, orderOf x = 2 → orderOf y = 2 →
      ∃ a : MulAut P, a x = y) :
    ∃ a : MulAut P, MonoidHom.FixedPointFree a := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let I := {x : P // orderOf x = 2}
  let : Fintype I := Fintype.ofFinite I
  let e : I ≃ Fin 3 := Fintype.equivFinOfCardEq
    (by simpa only [Nat.card_eq_fintype_card] using hthree)
  let f : MulAut P →* Equiv.Perm (Fin 3) :=
    e.permCongrHom.toMonoidHom.comp (involutionPermHom P)
  have hf (a : MulAut P) (x : I) : f a (e x) = e ⟨a x, (a.orderOf_eq x).trans x.property⟩ := by
    simp [f, involutionPermHom]
    rfl
  obtain ⟨a, ha⟩ := htrans (e.symm 0) (e.symm 1) (e.symm 0).property (e.symm 1).property
  obtain ⟨b, hb⟩ := htrans (e.symm 0) (e.symm 2) (e.symm 0).property (e.symm 2).property
  have hfa : f a 0 = 1 := by
    simpa only [e.apply_symm_apply] using (hf a (e.symm 0)).trans
      (congrArg e (Subtype.ext ha))
  have hfb : f b 0 = 2 := by
    simpa only [e.apply_symm_apply] using (hf b (e.symm 0)).trans
      (congrArg e (Subtype.ext hb))
  have hfree (c : MulAut P) (hc : ∀ x, f c x ≠ x) : MonoidHom.FixedPointFree c := by
    apply hP.fixedPointFree_of_no_fixed_prime_order c
    intro x hx heq
    apply hc (e ⟨x, hx⟩)
    rw [hf]
    exact congrArg e (Subtype.ext heq)
  rcases three_point_derangement (f a) (f b) hfa hfb with ha | hb | hab
  · exact ⟨a, hfree a ha⟩
  · exact ⟨b, hfree b hb⟩
  · exact ⟨a * b, hfree (a * b) (by simpa only [map_mul] using hab)⟩

/-- A cubic automorphism moving every involution makes every commutator central. -/
public theorem commutator_le_center_of_order_three_of_moves_involutions
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (a : MulAut P) (ha : orderOf a = 3)
    (hmove : ∀ x : P, orderOf x = 2 → a x ≠ x) :
    commutator P ≤ center P := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact a.commutator_le_center_of_orderOf_eq_three_of_fixedPointFree ha
    (hP.fixedPointFree_of_no_fixed_prime_order a hmove)

end IsPGroup
