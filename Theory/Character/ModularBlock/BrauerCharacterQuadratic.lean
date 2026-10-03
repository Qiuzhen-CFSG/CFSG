module

public import Theory.Character.ModularBlock.BrauerCharacterBasis
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Tactic.LinearCombination

/-!
# Lifted Brauer values for a quadratic cyclotomic polynomial

Eigenvalue lifting commutes with powers of an odd-order root. Consequently a
characteristic polynomial `X² + X + 1` on a two-dimensional representation in
characteristic two gives Brauer value `-1`: its roots are a nontrivial cube root
and its square, and their characteristic-zero lifts sum to `-1`.

This supplies the eigenvalue calculation used in the characteristic-two S₄
computation of Fong, *Some Sylow subgroups of order 32*, J. Algebra 6 (1967),
p. 71. No lifting of the residue-field trace is used.
-/

public section
noncomputable section
open ModularBlock PrincipalBlockConstruction BrauerCoefficientExtension
open Polynomial
namespace ModularBlock.BrauerCharacter
variable {G : Type*} [Group G] [Finite G] (d : PrincipalCongruenceBlockData G)
/-- Lifting an odd-order root commutes with taking natural powers. -/
theorem eigenvalueLift_pow (n : ℕ) (hn : Odd n) (hdiv : n ∣ Nat.card G)
    (a : splittingField d) (ha : a ^ n = 1) (k : ℕ) :
    eigenvalueLift d (a ^ k) = eigenvalueLift d a ^ k := by
  have hak : (a ^ k) ^ n = 1 := by rw [← pow_mul, Nat.mul_comm, pow_mul, ha, one_pow]
  rw [eigenvalueLift_eq_liftAtOrder d n hn hdiv _ hak,
    eigenvalueLift_eq_liftAtOrder d n hn hdiv _ ha]
  apply odd_root_eq_of_reduction_eq d hn hn hdiv hdiv
    (liftAtOrder_pow d n hn hdiv _ hak)
  · rw [← pow_mul, Nat.mul_comm, pow_mul, liftAtOrder_pow, one_pow]
  · rw [map_pow, reduction_liftAtOrder, reduction_liftAtOrder]

/-- A two-dimensional cyclotomic characteristic polynomial has lifted value `-1`. -/
theorem value_eq_neg_one_of_charpoly (hdiv : 3 ∣ Nat.card G)
    (ρ : Representation (splittingField d) G (Fin 2 → splittingField d)) (g : G)
    (hp : (ρ g).charpoly = X ^ 2 + X + 1) : value d ρ g = -1 := by
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root (ρ g).charpoly (by
    rw [Polynomial.degree_eq_natDegree (LinearMap.charpoly_monic _).ne_zero,
      LinearMap.charpoly_natDegree]
    simp)
  have ha0 : a ^ 2 + a + 1 = 0 := by simpa [hp, Polynomial.IsRoot] using ha
  have ha3 : a ^ 3 = 1 := by linear_combination (a - 1) * ha0
  have ha1 : a ≠ 1 := by
    intro he
    rw [he] at ha0
    simp [CharTwo.add_self_eq_zero] at ha0
  have hasum : a + a ^ 2 = -1 := by linear_combination ha0
  have hfactor : (ρ g).charpoly = (X - C a) * (X - C (a ^ 2)) := by
    rw [hp]
    calc
      X ^ 2 + X + 1 = X ^ 2 - C (a + a ^ 2) * X + C (a ^ 3) := by
        rw [hasum, ha3]
        simp
      _ = (X - C a) * (X - C (a ^ 2)) := by simp only [map_add, map_pow]; ring
  have hroots : (ρ g).charpoly.roots = {a, a ^ 2} := by
    rw [hfactor, Polynomial.roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)),
      roots_X_sub_C, roots_X_sub_C]
    rfl
  let z : ℂ := (eigenvalueLift d a : ℂ)
  have hz3 : z ^ 3 = 1 := by
    have h := liftAtOrder_pow d 3 (by decide) hdiv a ha3
    rw [← eigenvalueLift_eq_liftAtOrder] at h
    exact congrArg (fun x : cyclotomicOrder d.eta => (x : ℂ)) h
  have hz1 : z ≠ 1 := by
    intro h
    apply ha1
    have he : eigenvalueLift d a = 1 := Subtype.ext h
    have hl := reduction_eigenvalueLift d a ⟨3, by decide, hdiv, ha3⟩
    rw [he, map_one] at hl
    exact hl.symm
  have hzsum : z + z ^ 2 = -1 := by
    have hmul : (z - 1) * (z ^ 2 + z + 1) = 0 := by linear_combination hz3
    have hzero := (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hz1)
    linear_combination hzero
  simp only [value, integralValue, hroots]
  rw [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.sum_cons, Multiset.sum_singleton]
  rw [eigenvalueLift_pow d 3 (by decide) hdiv a ha3 2]
  exact hzsum
end ModularBlock.BrauerCharacter
