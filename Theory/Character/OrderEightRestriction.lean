module

public import Theory.Character.IntegralRestriction
public import Theory.Character.RationalPower
public import Theory.Character.AbelianLinearCharacters
public import Mathlib.GroupTheory.SpecificGroups.Quaternion

/-!
# Character restriction numerators for the groups of order eight

On a cyclic group of order eight, pair an integral-valued character with a
faithful linear character. Coprime-power invariance cancels the odd powers,
and the second and sixth powers cancel as well, leaving `d - a`, where `a`
is the value at the fourth power. On the quaternion group the principal
pairing counts one identity, one involution, and six order-four elements.
The integrality of character pairings makes each numerator divisible by eight.

Source: ordinary character restriction; P. Fong, *Some Sylow subgroups of
order 32 and a characterization of U(3,3)* (1967), printed p. 73.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Fintype.ofFinite

private def cyclicHom {M : Type*} [Monoid M] (x : M) (hx : x ^ 8 = 1) :
    Multiplicative (ZMod 8) →* M where
  toFun i := x ^ i.toAdd.val
  map_one' := by simp
  map_mul' i j := by
    change x ^ (i.toAdd + j.toAdd).val = x ^ i.toAdd.val * x ^ j.toAdd.val
    rw [ZMod.val_add, ← pow_add]
    exact (pow_eq_pow_mod _ hx).symm

/-- Pairing an integral-valued character on a cyclic group of period eight
with a faithful linear character makes its degree minus its fourth-power
value divisible by eight. -/
public theorem IsCharacter.eight_dvd_degree_sub_fourth_power {G : Type*} [Group G] {χ : ClassFunction G} (hχ : IsCharacter χ)
    (g : G) (hg : g ^ 8 = 1) (hint : ∀ x, ∃ z : ℤ, χ x = (z : ℂ))
    (d a : ℤ) (hd : χ 1 = (d : ℂ)) (ha : χ (g ^ 4) = (a : ℂ)) :
    (8 : ℤ) ∣ d - a := by
  classical
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 8)
  have hζ : IsPrimitiveRoot ζ 8 := Complex.isPrimitiveRoot_exp 8 (by decide)
  have hζ4 : ζ ^ 4 = -1 := (IsPrimitiveRoot.pow (by decide) hζ (show 8 = 4 * 2 by decide)).eq_neg_one_of_two_right
  let e := cyclicHom g hg
  let η := cyclicHom ζ hζ.pow_eq_one
  have h3 : χ (g ^ 3) = χ g := hχ.pow_eq_of_integer_value g (by decide) hg (by decide) (hint g)
  have h5 : χ (g ^ 5) = χ g := hχ.pow_eq_of_integer_value g (by decide) hg (by decide) (hint g)
  have h7 : χ (g ^ 7) = χ g := hχ.pow_eq_of_integer_value g (by decide) hg (by decide) (hint g)
  have h6 : χ (g ^ 6) = χ (g ^ 2) := by
    have hg2 : (g ^ 2) ^ 4 = 1 := by simpa only [← pow_mul] using hg
    simpa only [← pow_mul] using hχ.pow_eq_of_integer_value (g ^ 2) (by decide) hg2 (show Nat.Coprime 3 4 by decide) (hint _)
  have hs : (∑ i : Multiplicative (ZMod 8), χ (e i) * star (η i)) = ((d-a : ℤ) : ℂ) := by
    change (∑ i : Multiplicative (ZMod 8), χ (g ^ i.toAdd.val) * star (ζ ^ i.toAdd.val)) = _
    rw [(Multiplicative.toAdd : Multiplicative (ZMod 8) ≃ ZMod 8).sum_comp
      (fun i => χ (g ^ i.val) * star (ζ ^ i.val))]
    change (∑ i : Fin 8, χ (g ^ i.val) * star (ζ ^ i.val)) = _
    simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ]
    norm_num only [pow_zero, pow_one, h3, h5, h7, h6, hd, ha, star_one, mul_one]
    have hs4 : star ζ ^ 4 = -1 := by rw [← star_pow, hζ4, star_neg, star_one]
    simp only [star_pow]
    push_cast
    linear_combination (χ (g ^ 2) * star ζ ^ 2 + χ g * (star ζ ^ 3 + star ζ) + (a : ℂ)) * hs4
  have hη : IsCharacter (η : Multiplicative (ZMod 8) → ℂ) := by
    obtain ⟨n, ρ, _, hρ⟩ := η.isLinearCharacter.1
    exact ⟨n, ρ, hρ⟩
  have hz : IsCharacter (0 : ClassFunction (Multiplicative (ZMod 8))) := by
    refine ⟨0, Representation.trivial ℂ _ (Fin 0 → ℂ), ?_⟩
    funext x
    simp [Representation.character]
  have hηg : IsGeneralizedCharacter (η : Multiplicative (ZMod 8) → ℂ) :=
    ⟨η, 0, hη, hz, (sub_zero _).symm⟩
  have hh := hχ.card_dvd_restriction_numerator e hηg (d-a) (by
    convert hs using 1
    congr 2
    exact Subsingleton.elim _ _)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card, Nat.cast_ofNat] using hh

/-- The principal quaternion restriction has numerator `d + a + 6b`
when the involution has value `a` and all six order-four elements have value `b`. -/
public theorem IsCharacter.eight_dvd_quaternion_restriction_sum {G : Type*} [Group G] {χ : ClassFunction G} (hχ : IsCharacter χ)
    (f : QuaternionGroup 2 →* G) (d a b : ℤ) (hd : χ 1 = (d : ℂ))
    (htwo : ∀ x : QuaternionGroup 2, orderOf x = 2 → χ (f x) = (a : ℂ))
    (hfour : ∀ x : QuaternionGroup 2, orderOf x = 4 → χ (f x) = (b : ℂ)) :
    (8 : ℤ) ∣ d + a + 6 * b := by
  classical
  have hs : (∑ x : QuaternionGroup 2, χ (f x)) = ((d+a+6*b : ℤ) : ℂ) := by
    let eqv : ZMod 4 ⊕ ZMod 4 ≃ QuaternionGroup 2 := {
      toFun := fun x => match x with
        | Sum.inl i => QuaternionGroup.a i
        | Sum.inr i => QuaternionGroup.xa i
      invFun := fun x => match x with
        | QuaternionGroup.a i => Sum.inl i
        | QuaternionGroup.xa i => Sum.inr i
      left_inv := by rintro (i | i) <;> rfl
      right_inv := by rintro (i | i) <;> rfl }
    rw [← eqv.sum_comp (fun x => χ (f x))]
    rw [Fintype.sum_sum_type]
    change (∑ i : Fin 4, χ (f (QuaternionGroup.a i))) +
      (∑ i : Fin 4, χ (f (QuaternionGroup.xa i))) = _
    simp only [Fin.sum_univ_succ]
    have h0 : χ (f (QuaternionGroup.a 0)) = (d : ℂ) := by simpa using hd
    have h1 := hfour (QuaternionGroup.a 1) (by rw [QuaternionGroup.orderOf_a]; decide)
    have h2 := htwo (QuaternionGroup.a 2) (by rw [QuaternionGroup.orderOf_a]; decide)
    have h3 := hfour (QuaternionGroup.a 3) (by rw [QuaternionGroup.orderOf_a]; decide)
    have hxa (i : ZMod 4) := hfour (QuaternionGroup.xa i) (QuaternionGroup.orderOf_xa (n := 2) i)
    change χ (f (QuaternionGroup.a 0)) + (χ (f (QuaternionGroup.a 1)) +
      (χ (f (QuaternionGroup.a 2)) + (χ (f (QuaternionGroup.a 3)) + 0))) +
      (χ (f (QuaternionGroup.xa 0)) + (χ (f (QuaternionGroup.xa 1)) +
      (χ (f (QuaternionGroup.xa 2)) + (χ (f (QuaternionGroup.xa 3)) + 0)))) = _
    rw [h0, h1, h2, h3, hxa, hxa, hxa, hxa]
    push_cast
    ring
  have hh := hχ.card_dvd_restriction_sum f (d+a+6*b) (by
    convert hs using 1
    congr 2
    exact Subsingleton.elim _ _)
  simpa only [Nat.card_eq_fintype_card, QuaternionGroup.card, Nat.cast_mul, Nat.cast_ofNat, show (4 : ℤ) * 2 = 8 by decide] using hh