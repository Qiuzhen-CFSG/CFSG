module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.PolygonParameters.SquareExports
public import Theory.NumberTheory.BinaryTorusParity

/-!
# Binary degrees in a finite marked octagon

The Feit--Higman square condition forces the degree of a linear root to
be odd when the opposite root has square binary order. It also excludes
two roots of square binary order. The argument reduces powers of two
modulo three, where a square cannot have residue two.

Source: Fong--Seitz I (1J) and its use in (6H)(a), printed pp.6 and 51.
The source panel markings supply the literal root orders in the consumers.
-/

public noncomputable section
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}

private theorem even_exponent_of_square {n : ℕ} (h : IsSquare (2 ^ n)) : n % 2 = 0 := by
  obtain ⟨k,hk⟩ := h
  have hp := Nat.BinaryTorusParity.two_pow_mod_three n
  have hs := congrArg (fun x : ℕ => x % 3) hk
  rw [Nat.mul_mod] at hs
  by_contra hn
  rw [if_neg hn] at hp
  rw [hp] at hs
  have hk3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hk3 with hk3 | hk3 | hk3 <;> norm_num [hk3] at hs

/-- A linear binary root opposite a square-order root has odd degree. -/
theorem octagon_linear_degree_odd
    (Q : MarkedQuotient P) (split : SplitData Q.tits) (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j) {n k : ℕ}
    (hi : Nat.card (simpleRoot Q split i) = 2 ^ n)
    (hj : Nat.card (simpleRoot Q split j) = (2 ^ k) ^ 2) : Odd n := by
  have hs := octagon_twice_root_product_isSquare_of_ne Q split hm i j hij
  rw [hi,hj] at hs
  have he : 2 * 2 ^ n * (2 ^ k) ^ 2 = 2 ^ (1 + n + 2 * k) := by
    rw [← pow_mul,← pow_succ',← pow_add]
    congr 1
    omega
  rw [he] at hs
  have hp := even_exponent_of_square hs
  exact Nat.odd_iff.mpr (by omega)

/-- The two simple roots of a marked octagon cannot both have square binary order. -/
theorem octagon_two_square_binary_roots_excluded
    (Q : MarkedQuotient P) (split : SplitData Q.tits) (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j) {a b : ℕ}
    (hi : Nat.card (simpleRoot Q split i) = (2 ^ a) ^ 2)
    (hj : Nat.card (simpleRoot Q split j) = (2 ^ b) ^ 2) : False := by
  have ho := octagon_linear_degree_odd Q split hm i j hij
    (n := 2 * a) (by simpa only [← pow_mul,Nat.mul_comm] using hi) hj
  obtain ⟨k,hk⟩ := ho
  omega

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
