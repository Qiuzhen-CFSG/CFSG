module
public import ABG.Basic
public import Theory.FieldTheory.QuadraticFrobeniusFixed
public import BenderSuzuki.External.Huppert.II.theorem_10_4
public import Mathlib.Tactic

/-!
# Coordinates for the actual quadratic unitary field

For the standard unitary form over GF(p^(2n)), with odd p and nonzero n,
there are elements z,t satisfying z*conj(z)=-1, t nonzero and conj(t)=-t.
The actual fixed subfield of its stored involution is ring-isomorphic to
GF(p^n). No replacement field or involution instance is introduced, and
the field orders three and nine are included.

The Frobenius fixed-field cardinality is p^n. Surjectivity of the quadratic
norm supplies z. Since the quadratic field is larger than its fixed field,
a nonfixed a exists; t=a-conj(a) is nonzero and anti-fixed by involutivity.
Uniqueness of finite fields of a given cardinality supplies the ring
equivalence. These coordinates support the matrix conjugacy SU2 to SL2
in ABG II.2 Lemma1(vi), article p17, used later in II.3 Proposition3.
-/

namespace ABG

public theorem unitaryQuadraticCoordinates (p n : ℕ) [Fact p.Prime] (_hp : Odd p) (hn : n ≠ 0) :
    (∃ z t : GaloisField p (2 * n),
      z * (unitaryForm 2 p n hn).conj z = -1 ∧
      t ≠ 0 ∧ (unitaryForm 2 p n hn).conj t = -t) ∧
    Nonempty ((FixedBy.subfield (GaloisField p (2 * n)) (unitaryForm 2 p n hn).conj) ≃+*
      GaloisField p n) := by
  classical
  let F := GaloisField p (2 * n)
  let J := unitaryForm 2 p n hn
  let k := FixedBy.subfield F J.conj
  have hk : Nat.card k = p ^ n := GaloisField.card_fixedBy_quadraticFrobenius p n hn
  have hFc : Nat.card F = (p ^ n) ^ 2 := by
    rw [GaloisField.card p (2 * n) (Nat.mul_ne_zero (by decide) hn), ← pow_mul,
      Nat.mul_comm n 2]
  have hfix : Nat.card {x : F // J.conj x = x} = p ^ n := hk
  obtain ⟨z, _hz0, hz⟩ := BenderSuzuki.External.huppert_II_10_4_norm_surjective
    J (p ^ n) hFc hfix (-1) (by simp) (by simp)
  have hex : ∃ a : F, J.conj a ≠ a := by
    by_contra! hall
    let e : k ≃ F :=
      { toFun := Subtype.val
        invFun := fun a => ⟨a, hall a⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have he := Nat.card_congr e
    rw [hk, hFc] at he
    have hq : 1 < p ^ n := Nat.one_lt_pow hn (Fact.out : p.Prime).one_lt
    nlinarith
  obtain ⟨a, ha⟩ := hex
  refine ⟨⟨z, a - J.conj a, hz, sub_ne_zero.mpr ha.symm, ?_⟩, ?_⟩
  · rw [map_sub, J.conj_involutive a]
    ring
  · let : Fintype k := Fintype.ofFinite k
    let : Fintype (GaloisField p n) := Fintype.ofFinite _
    exact ⟨FiniteField.ringEquivOfCardEq (by
      simpa only [← Nat.card_eq_fintype_card] using hk.trans (GaloisField.card p n hn).symm)⟩

end ABG

