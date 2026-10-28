module
public import Theory.Combinatorics.SimpleGraph.PolygonParameters.OctagonMultiplicity
public import Theory.NumberTheory.BinaryOctagonBound
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.PolygonParameters.OctagonDegrees

/-!
# Bounds on binary root degrees in a marked octagon

The actual marked coset graph supplies the octagon distance operators and
point count. Their integral multiplicity, together with the square condition
for twice the root product, bounds either binary root degree by twice the
other. No eigenvalue, divisibility, oddness or degree-bound premise remains.

Source: Fong--Seitz I (1K), printed pp.6--7; the two-linear application is
(6G), printed p.49. Both endpoint orientations and degree one are retained.
-/

public noncomputable section
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open PolygonParameters
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}

private theorem odd_sum_of_twice_binary_product_isSquare {a b : ℕ}
    (h : IsSquare (2*2^a*2^b)) : Odd (a+b) := by
  have he : 2*2^a*2^b = 2^(1+(a+b)) := by
    rw [pow_add, pow_add]
    ring
  rw [he] at h
  obtain ⟨k,hk⟩ := h
  have hp := Nat.BinaryTorusParity.two_pow_mod_three (1+(a+b))
  have hs := congrArg (fun x : ℕ => x % 3) hk
  rw [Nat.mul_mod] at hs
  have hn : (1+(a+b)) % 2 = 0 := by
    by_contra hn
    rw [if_neg hn] at hp
    rw [hp] at hs
    have hk3 : k%3=0 ∨ k%3=1 ∨ k%3=2 := by omega
    rcases hk3 with hk3 | hk3 | hk3 <;> norm_num [hk3] at hs
  exact Nat.odd_iff.mpr (by omega)

/-- In a marked finite binary octagon, either root degree is at most twice
that of the other root. The literal root orders are the only model inputs. -/
theorem octagon_binary_degree_le_twice
    (Q : MarkedQuotient P) (split : SplitData Q.tits) (hm : rotationOrder Q=8)
    (i j : Fin 2) (hij : i≠j) {a b : ℕ}
    (hi : Nat.card (simpleRoot Q split i)=2^a)
    (hj : Nat.card (simpleRoot Q split j)=2^b) : b≤2*a := by
  have ha : 0<a := by
    have hgt := simpleRoot_card_gt_one Q split i
    rw [hi] at hgt
    by_contra hh
    have he : a=0 := by omega
    simp [he] at hgt
  have ho : Odd (a+b) := by
    apply odd_sum_of_twice_binary_product_isSquare
    simpa only [hi,hj] using
      octagon_twice_root_product_isSquare_of_ne Q split hm i j hij
  have hd := SimpleGraph.PolygonParameters.octagon_parameter_divisibility
    (octagonMetricDatum Q split hm)
    (show 0<Nat.card (simpleRoot Q split 1) from Nat.card_pos)
    (octagonMetricDatum_point Q split hm)
  have hd' : Nat.card (simpleRoot Q split 1)+Nat.card (simpleRoot Q split 0) ∣
      Nat.card (simpleRoot Q split 1)^4 *
      (Nat.card (simpleRoot Q split 1)*Nat.card (simpleRoot Q split 0)+1) *
      (Nat.card (simpleRoot Q split 1)^2*Nat.card (simpleRoot Q split 0)^2+1) :=
    (dvd_mul_right _ _).trans hd
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · change Nat.card (simpleRoot Q split 0)=2^a at hi
    change Nat.card (simpleRoot Q split 1)=2^b at hj
    apply Nat.binary_octagon_degree_le_twice (e := 4*b) ha ho
    rw [hi,hj] at hd'
    simpa only [← pow_mul, ← pow_add, Nat.mul_add, Nat.add_mul,
      Nat.mul_comm, Nat.add_comm] using hd'
  · change Nat.card (simpleRoot Q split 1)=2^a at hi
    change Nat.card (simpleRoot Q split 0)=2^b at hj
    apply Nat.binary_octagon_degree_le_twice (e := 4*a) ha ho
    rw [hi,hj] at hd'
    simpa only [← pow_mul, ← pow_add, Nat.mul_add, Nat.add_mul,
      Nat.mul_comm, Nat.add_comm] using hd'
  · exact (hij rfl).elim

/-- The symmetric pair of bounds keeps both original endpoint indices. -/
theorem octagon_binary_degree_bounds
    (Q : MarkedQuotient P) (split : SplitData Q.tits) (hm : rotationOrder Q=8)
    (i j : Fin 2) (hij : i≠j) {a b : ℕ}
    (hi : Nat.card (simpleRoot Q split i)=2^a)
    (hj : Nat.card (simpleRoot Q split j)=2^b) : a≤2*b ∧ b≤2*a :=
  ⟨octagon_binary_degree_le_twice Q split hm j i hij.symm hj hi,
    octagon_binary_degree_le_twice Q split hm i j hij hi hj⟩

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
