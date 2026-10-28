module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.PolygonParameters.OctagonDegrees

/-!
# Opposite binary degrees in a finite octagon

The finite polygon square theorem says that twice the product of the two
root orders is a square. For binary root orders this forces opposite
exponent parity. In particular two unitary root orders have opposite
field-degree parity, while a unitary root opposite a square-order root
has odd field degree. All orders are those of the actual marked roots.

Source: Fong--Seitz I (1J) and the initial reductions in (6F), pp.45--48.
These restrictions do not themselves exclude the unitary octagon cases.
-/

public noncomputable section
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}

/-- The two binary root exponents in an octagon have opposite parity. -/
theorem octagon_binary_degree_parity
    (Q : MarkedQuotient P) (split : SplitData Q.tits) (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j) {a b : ℕ}
    (hi : Nat.card (simpleRoot Q split i) = 2 ^ a)
    (hj : Nat.card (simpleRoot Q split j) = 2 ^ b) : a % 2 ≠ b % 2 := by
  obtain ⟨k,hk⟩ := octagon_twice_root_product_isSquare_of_ne Q split hm i j hij
  rw [hi,hj] at hk
  have he : 2 * 2 ^ a * 2 ^ b = 2 ^ (1 + a + b) := by
    rw [← pow_succ',← pow_add]
    congr 1
    omega
  rw [he] at hk
  intro hab
  have hp := Nat.BinaryTorusParity.two_pow_mod_three (1 + a + b)
  rw [if_neg (by omega : (1 + a + b) % 2 ≠ 0)] at hp
  have hs := congrArg (fun x : ℕ => x % 3) hk
  rw [Nat.mul_mod,hp] at hs
  have hk3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hk3 with hk3 | hk3 | hk3 <;> norm_num [hk3] at hs

/-- Cubic binary root orders retain the parity of their field degrees. -/
theorem octagon_unitary_degree_parity
    (Q : MarkedQuotient P) (split : SplitData Q.tits) (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j) {a b : ℕ}
    (hi : Nat.card (simpleRoot Q split i) = (2 ^ a) ^ 3)
    (hj : Nat.card (simpleRoot Q split j) = (2 ^ b) ^ 3) : a % 2 ≠ b % 2 := by
  have hh := octagon_binary_degree_parity Q split hm i j hij
    (a := a * 3) (b := b * 3)
    (by simpa only [← pow_mul] using hi) (by simpa only [← pow_mul] using hj)
  omega

/-- The linear and unitary degrees have opposite parity in an octagon. -/
theorem octagon_linear_unitary_degree_parity
    (Q : MarkedQuotient P) (split : SplitData Q.tits) (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j) {a b : ℕ}
    (hi : Nat.card (simpleRoot Q split i) = 2 ^ a)
    (hj : Nat.card (simpleRoot Q split j) = (2 ^ b) ^ 3) : a % 2 ≠ b % 2 := by
  have hh := octagon_binary_degree_parity Q split hm i j hij
    (a := a) (b := b * 3) hi
    (by simpa only [← pow_mul] using hj)
  omega

/-- A unitary root opposite a square binary root has odd field degree. -/
theorem octagon_unitary_degree_odd_of_square_root
    (Q : MarkedQuotient P) (split : SplitData Q.tits) (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j) {a b : ℕ}
    (hi : Nat.card (simpleRoot Q split i) = (2 ^ a) ^ 3)
    (hj : Nat.card (simpleRoot Q split j) = (2 ^ b) ^ 2) : Odd a := by
  have hh := octagon_binary_degree_parity Q split hm i j hij
    (a := a * 3) (b := b * 2)
    (by simpa only [← pow_mul] using hi) (by simpa only [← pow_mul] using hj)
  exact Nat.odd_iff.mpr (by omega)

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
