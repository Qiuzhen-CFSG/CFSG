module

public import Theory.ElementaryAbelian.Basic
public import Mathlib.Algebra.Group.End

/-!
# Transport of an automorphism square-action calculation

A group isomorphism transports fixed subgroups and conjugating elements. Thus a
calculation of an elementary fixed four and a square root in a specified coset
of inner automorphisms can be carried from a concrete model to an intrinsic
group without changing the prescribed automorphism.

The proof conjugates automorphisms through the isomorphism, identifies the two
fixed subgroups, and transports the square-root witness back. This is the model
transfer needed for the extraspecial calculation in Janko–Thompson (1970), §4,
printed p.390.
-/

namespace MulEquiv
variable {G K : Type*} [Group G] [Group K]

private theorem congr_inner (e : G ≃* K) (x : G) :
    MulAut.congr e (MulAut.conj x) = MulAut.conj (e x) := by
  ext y
  simp [MulAut.congr_apply, MulAut.conj_apply]

/-- Conjugating an automorphism through an isomorphism identifies its fixed subgroup. -/
public def automorphismFixedEquiv (e : G ≃* K) (a : MulAut G) :
    a.toMonoidHom.eqLocus (MonoidHom.id G) ≃*
      (MulAut.congr e a).toMonoidHom.eqLocus (MonoidHom.id K) where
  toFun x := ⟨e x, by
    change (MulAut.congr e a) (e x) = e x
    change e (a (e.symm (e x))) = e x
    rw [e.symm_apply_apply]
    exact congrArg e x.property⟩
  invFun x := ⟨e.symm x, by
    apply e.injective
    have h := x.property
    change (MulAut.congr e a) x = x at h
    change e (a (e.symm x)) = x at h
    change e (a (e.symm x)) = e (e.symm x)
    rw [e.apply_symm_apply]
    exact h⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv x := Subtype.ext (e.apply_symm_apply x)
  map_mul' x y := Subtype.ext (e.map_mul x y)

/-- Transfer a fixed-four and corrected-square-root calculation along an isomorphism. -/
public theorem square_action_fixed_four_transfer (e : G ≃* K)
    (hcalc : ∀ (a b : MulAut K) (p : K) (n : ℕ),
      b ^ (2 ^ n) = 1 → a = MulAut.conj p * b ^ 2 → a ^ 2 = 1 →
      (¬ ∃ x : K, a = MulAut.conj x) →
      IsElementaryAbelian 2 (a.toMonoidHom.eqLocus (MonoidHom.id K)) ∧
      Nat.card (a.toMonoidHom.eqLocus (MonoidHom.id K)) = 4 ∧
      ∃ x : K, (MulAut.conj x * b) ^ 2 = a)
    (a b : MulAut G) (p : G) (n : ℕ)
    (hb : b ^ (2 ^ n) = 1) (hab : a = MulAut.conj p * b ^ 2)
    (ha : a ^ 2 = 1) (hout : ¬ ∃ x : G, a = MulAut.conj x) :
    IsElementaryAbelian 2 (a.toMonoidHom.eqLocus (MonoidHom.id G)) ∧
    Nat.card (a.toMonoidHom.eqLocus (MonoidHom.id G)) = 4 ∧
    ∃ x : G, (MulAut.conj x * b) ^ 2 = a := by
  let c := MulAut.congr e
  have hb' : c b ^ (2 ^ n) = 1 := by rw [← map_pow, hb, map_one]
  have ha' : c a ^ 2 = 1 := by rw [← map_pow, ha, map_one]
  have hab' : c a = MulAut.conj (e p) * c b ^ 2 := by
    rw [hab, map_mul, map_pow]
    exact congrArg (· * c b ^ 2) (congr_inner e p)
  have hout' : ¬ ∃ x : K, c a = MulAut.conj x := by
    rintro ⟨x, hx⟩
    apply hout
    refine ⟨e.symm x, c.injective ?_⟩
    rw [congr_inner, e.apply_symm_apply]
    exact hx
  obtain ⟨hE, hcard, x, hx⟩ := hcalc (c a) (c b) (e p) n hb' hab' ha' hout'
  let f := automorphismFixedEquiv e a
  let := hE
  have helem : IsElementaryAbelian 2 (a.toMonoidHom.eqLocus (MonoidHom.id G)) := by
    refine { toIsMulCommutative := ⟨⟨fun x y => f.injective ?_⟩⟩
             exponent_dvd_p := ?_ }
    · simp only [map_mul]
      exact (IsMulCommutative.is_comm (M := (c a).toMonoidHom.eqLocus (MonoidHom.id K))).comm _ _
    · rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      intro y
      apply f.injective
      rw [map_pow, map_one]
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 ((c a).toMonoidHom.eqLocus (MonoidHom.id K))) _
  refine ⟨helem, (Nat.card_congr f.toEquiv).trans hcard, e.symm x, c.injective ?_⟩
  rw [map_pow, map_mul, congr_inner, e.apply_symm_apply]
  exact hx

end MulEquiv
