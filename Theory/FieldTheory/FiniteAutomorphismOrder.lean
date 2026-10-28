module

public import Theory.FieldTheory.OddQuadraticCoefficientLift

/-!
# Automorphism order for arbitrary finite-field carriers

A field of order pⁿ has n ring automorphisms. Transport to GF(pⁿ)
identifies the automorphisms by conjugation, so the existing Galois-field
calculation applies without imposing a particular field carrier.
In degrees at most two every field automorphism has square one.

Source: the finite-field factor in GLS3, Theorem 2.5.12(d),
`refs/KGroup/GLS3/chapter2.tex`.
-/

public section
namespace FiniteField
variable {F : Type*} [Field F] [Finite F]

/-- The number of ring automorphisms of a finite field of prime-power order. -/
theorem card_ringAut_of_card_prime_pow {p n : ℕ} (hp : p.Prime)
    (hcard : Nat.card F = p ^ n) : Nat.card (F ≃+* F) = n := by
  classical
  have hn : n ≠ 0 := by
    intro hn
    have := Finite.one_lt_card (α := F)
    simp [hn] at hcard
    omega
  let : Fact p.Prime := ⟨hp⟩
  let K := GaloisField p n
  let : Fintype F := Fintype.ofFinite F
  let : Fintype K := Fintype.ofFinite K
  let e : F ≃+* K := ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card] using
      hcard.trans (GaloisField.card p n hn).symm)
  let c : (F ≃+* F) ≃ (K ≃+* K) :=
    { toFun := fun a => (e.symm.trans a).trans e
      invFun := fun a => (e.trans a).trans e.symm
      left_inv := fun a => by ext x; simp
      right_inv := fun a => by ext x; simp }
  exact (Nat.card_congr c).trans (GaloisField.card_ringAut p n hn)

/-- Every automorphism of a field of degree at most two has square one. -/
theorem ringAut_sq_of_card_prime_pow {p n : ℕ} (hp : p.Prime)
    (hn : n ≤ 2) (hcard : Nat.card F = p ^ n) (a : F ≃+* F) : a ^ 2 = 1 := by
  let : Finite (F ≃+* F) := Finite.of_injective
    (fun a : F ≃+* F => (a : F → F)) DFunLike.coe_injective
  have hc := card_ringAut_of_card_prime_pow hp hcard
  have hpos : 0 < n := hc ▸ Nat.card_pos (α := F ≃+* F)
  have hd : n ∣ 2 := by interval_cases n <;> norm_num
  exact orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_natCard a).trans (hc.symm ▸ hd))

/-- Ring automorphisms of a prime-order field are trivial. -/
theorem ringAut_eq_one_of_card_prime {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card F = p) (a : F ≃+* F) : a = 1 := by
  have hc : Nat.card (F ≃+* F) = 1 :=
    card_ringAut_of_card_prime_pow hp (by simpa only [pow_one] using hcard)
  let : Subsingleton (F ≃+* F) := (Nat.card_eq_one_iff_unique.mp hc).1
  exact Subsingleton.elim a 1

end FiniteField
