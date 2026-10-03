module

public import Theory.GroupTheory.PGroup.TransitiveInvolutions
public import Theory.GroupTheory.PGroup.CyclicInvolution

/-!
# Central roots of transitive involutions

For a finite two-group with automorphism-transitive involutions, either the
center has exponent at most two, or every involution has a central square
root. A nontrivial square subgroup of the center contains an involution;
automorphisms transport its central root to all the other involutions.
If involutions are central, subtracting a central root detects centrality.

Two complementary reductions support the class-two exponent argument: an
elementary center forces exponent at most four, while three transitive
involutions force the derived subgroup of a nonabelian group to be noncyclic.
These are elementary reductions for the three-involution structure problem
in Janko–Thompson, Math. Z. 113 (1970), Theorem 1.3 and Lemma 5.1.
-/

open Subgroup
open scoped commutatorElement IsMulCommutative

namespace IsPGroup

/-- Central commutators and an elementary center force fourth powers to vanish. -/
public theorem exponent_four_of_class_two_of_center_exponent_two
    {P : Type*} [Group P]
    (hclass : commutator P ≤ center P)
    (hZ : ∀ z : P, z ∈ center P → z ^ 2 = 1) :
    ∀ x : P, x ^ 4 = 1 := by
  intro x
  have hsquare : x ^ 2 ∈ center P := by
    apply mem_center_iff.mpr
    intro y
    apply Eq.symm
    apply commutatorElement_eq_one_iff_mul_comm.mp
    have hc : ⁅x,y⁆ ∈ center P :=
      hclass (commutator_mem_commutator (mem_top x) (mem_top y))
    rw [pow_two, commutatorElement_mul_left_eq_conj_mul,
      mem_center_iff.mp hc x, mul_inv_cancel_right, ← pow_two, hZ _ hc]
  simpa only [← pow_mul] using hZ _ hsquare

/-- Transitivity gives a dichotomy between an elementary center and central roots. -/
public theorem center_exponent_two_or_involutions_have_central_square_roots
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (htrans : ∀ x y : P, orderOf x = 2 → orderOf y = 2 →
      ∃ a : MulAut P, a x = y) :
    (∀ z : P, z ∈ center P → z ^ 2 = 1) ∨
      (∀ t : P, t ^ 2 = 1 → ∃ z : center P, (z : P) ^ 2 = t) := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases he : ∀ z : P, z ∈ center P → z ^ 2 = 1
  · exact Or.inl he
  right
  let square : center P →* center P := powMonoidHom 2
  have hR : square.range ≠ ⊥ := by
    intro hbot
    apply he
    intro z hz
    have hm : (⟨z,hz⟩ : center P)^2 ∈ square.range := ⟨⟨z,hz⟩, rfl⟩
    rw [hbot, mem_bot] at hm
    exact congrArg Subtype.val hm
  have hdiv : 2 ∣ Nat.card square.range :=
    ((hP.to_subgroup (center P)).to_subgroup square.range).card_eq_or_dvd.resolve_left
      (fun h => hR (card_eq_one.mp h))
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := square.range) 2 hdiv
  obtain ⟨z, hz⟩ := t.property
  have htP : orderOf ((t : center P) : P) = 2 := by
    simpa only [orderOf_coe] using ht
  intro u hu
  by_cases hu1 : u = 1
  · exact ⟨1, by simp [hu1]⟩
  obtain ⟨a, ha⟩ := htrans t u htP (orderOf_eq_prime hu hu1)
  have haz : a z ∈ center P := characteristic_iff_le_comap.mp inferInstance a z.property
  refine ⟨⟨a z, haz⟩, ?_⟩
  rw [← map_pow]
  exact (congrArg a (congrArg Subtype.val hz)).trans ha

/-- A cyclic derived subgroup cannot contain three transitive involutions. -/
public theorem not_isCyclic_commutator_of_transitive_three_involutions
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hnonab : ¬ IsMulCommutative P)
    (hthree : Nat.card {x : P // orderOf x = 2} = 3)
    (htrans : ∀ x y : P, orderOf x = 2 → orderOf y = 2 →
      ∃ a : MulAut P, a x = y) : ¬ IsCyclic (commutator P) := by
  intro hcyc
  let : IsCyclic (commutator P) := hcyc
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne : commutator P ≠ ⊥ := fun he => hnonab ((commutator_eq_bot_iff P).mp he)
  have hle := hP.omega_one_le_characteristic_of_transitive_prime_order htrans
    (commutator P) hne
  have hmem (x : P) (hx : orderOf x = 2) : x ∈ commutator P :=
    hle (subset_closure (by simpa [hx] using pow_orderOf_eq_one x))
  have : Subsingleton {x : P // orderOf x = 2} := by
    constructor
    intro x y
    apply Subtype.ext
    exact congrArg (fun z : commutator P => (z : P)) (IsCyclic.eq_of_orderOf_eq_two
      (x := (⟨x, hmem x x.property⟩ : commutator P))
      (y := (⟨y, hmem y y.property⟩ : commutator P))
      (by rw [← orderOf_coe]; exact x.property)
      (by rw [← orderOf_coe]; exact y.property))
  have : Nonempty {x : P // orderOf x = 2} :=
    (Nat.card_pos_iff.mp (show 0 < Nat.card {x : P // orderOf x = 2} by omega)).1
  have hb := Nat.card_unique (α := {x : P // orderOf x = 2})
  omega

/-- A central square root of the square of an element makes that element central,
provided all involutions are central. -/
public theorem mem_center_of_square_eq_central_square
    {P : Type*} [Group P]
    (hcentral : ∀ x : P, x ^ 2 = 1 → x ∈ center P)
    (x : P) (z : center P) (hsquare : x ^ 2 = (z : P) ^ 2) :
    x ∈ center P := by
  have hc : Commute x (z : P)⁻¹ :=
    (show Commute x (z : P) from mem_center_iff.mp z.property x).inv_right
  have hone : (x * (z : P)⁻¹) ^ 2 = 1 := by
    rw [hc.mul_pow, inv_pow, hsquare, mul_inv_cancel]
  have hm := (center P).mul_mem (hcentral _ hone) z.property
  simpa only [inv_mul_cancel_right] using hm

/-- If all involutions admit central square roots, all elements whose fourth
power is one are central. -/
public theorem mem_center_of_pow_four_eq_one_of_central_square_roots
    {P : Type*} [Group P]
    (hcentral : ∀ x : P, x ^ 2 = 1 → x ∈ center P)
    (hroots : ∀ t : P, t ^ 2 = 1 → ∃ z : center P, (z : P) ^ 2 = t)
    (x : P) (hx : x ^ 4 = 1) : x ∈ center P := by
  obtain ⟨z, hz⟩ := hroots (x ^ 2) (by simpa only [← pow_mul] using hx)
  exact mem_center_of_square_eq_central_square hcentral x z hz.symm

end IsPGroup
