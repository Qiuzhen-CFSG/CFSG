module

public import Theory.SpecificGroups.PSp4Three.Primitivity

/-!
# Primitivity of the symplectic four-space projective action

For every finite field of order q, the point-stabilizer orbits have sizes
1, q + q², and q³. Neither possible proper nonsingleton block size divides
the total 1 + q + q² + q³. The existing generic alternating-frame and
projective-action results therefore give primitivity.

Adapted from Gerald Höhn, ATLAS, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`,
`Atlas/LinearGroups/Symplectic/{PointCount,Primitivity}.lean` and
`Atlas/Algebra/GeometricSumBounds.lean`.
Covered by the ATLAS Research and Attribution License 1.0; see
`LICENSES/ATLAS.txt` and `LICENSES/ATLAS-CITATION.cff`.
Changes: specialize to dimension four and reuse CFSG's module-compatible
`Matrix.PSp4Three` geometry, which is generic in the field.
-/

public section

namespace Theory.SpecificGroups.SymplecticFour.SimpleQuotients

open Matrix.PSp4Three
variable {F : Type*} [Field F] [Finite F]

private theorem card_points_four :
    Nat.card (Points 2 F) = 1 + Nat.card F + Nat.card F ^ 2 + Nat.card F ^ 3 := by
  have h := Projectivization.card_of_finrank F (Vector 2 F)
    (show Module.finrank F (Vector 2 F) = 4 by simp [Matrix.PSp4Three.Vector, Index])
  simpa [Finset.sum_range_succ] using h

private theorem card_perpendicular_points_four (p : Points 2 F) :
    Nat.card {q : Points 2 F // Orthogonal p q} = 1 + Nat.card F + Nat.card F ^ 2 := by
  rw [← Nat.card_congr (perpendicularPointsEquiv p)]
  have hd : Module.finrank F (form p.rep).ker = 3 := by
    obtain ⟨v, hv⟩ := Frame.exists_partner form form_nondegenerate p.rep_nonzero
    have hr : LinearMap.range (form p.rep) = ⊤ := by
      apply LinearMap.range_eq_top.mpr
      intro a
      exact ⟨a • v, by simp [map_smul, hv]⟩
    have h := (form p.rep).finrank_range_add_finrank_ker
    rw [hr, finrank_top, Module.finrank_self] at h
    have hdim : Module.finrank F (Vector 2 F) = 4 := by simp [Matrix.PSp4Three.Vector, Index]
    omega
  simpa [Finset.sum_range_succ] using Projectivization.card_of_finrank F (form p.rep).ker hd

private theorem block_nondivisibility {q : ℕ} (hq : 2 ≤ q) :
    ¬ (1 + q + q ^ 2) ∣ (1 + q + q ^ 2 + q ^ 3) ∧
    ¬ (1 + q ^ 3) ∣ (1 + q + q ^ 2 + q ^ 3) := by
  have hq2 : 2 * q ≤ q ^ 2 := by simpa [pow_two] using Nat.mul_le_mul_right q hq
  have hq3 : 2 * q ^ 2 ≤ q ^ 3 := by
    calc
      _ ≤ q * q ^ 2 := Nat.mul_le_mul_right (q ^ 2) hq
      _ = q ^ 3 := by ring
  have hlt : 1 + q + q ^ 2 < q ^ 3 := by omega
  constructor
  · intro hd
    have he : 1 + q + q ^ 2 + q ^ 3 = q * (1 + q + q ^ 2) + 1 := by ring
    rw [he] at hd
    have h1 : 1 + q + q ^ 2 ∣ 1 :=
      (Nat.dvd_add_iff_right (dvd_mul_left (1 + q + q ^ 2) q)).mpr hd
    have := Nat.le_of_dvd (by decide : 0 < 1) h1
    omega
  · rintro ⟨k, hk⟩
    by_cases hle : k ≤ 1
    · have := Nat.mul_le_mul_left (1 + q ^ 3) hle
      nlinarith
    · have := Nat.mul_le_mul_left (1 + q ^ 3) (show 2 ≤ k by omega)
      nlinarith

/-- The faithful projective action of the actual central quotient is primitive
in dimension four over every finite field. -/
theorem projective_preprimitive :
    MulAction.IsPreprimitive (PSp 2 F) (Points 2 F) := by
  classical
  let p : Points 2 F := ePoint 0
  let q := Nat.card F
  have hcard : Nat.card (Points 2 F) = 1 + q + q ^ 2 + q ^ 3 :=
    card_points_four
  have hperp : Nat.card {x : Points 2 F // Orthogonal p x} = 1 + q + q ^ 2 :=
    card_perpendicular_points_four p
  have hq : 2 ≤ q := Finite.one_lt_card
  have hnd := block_nondivisibility hq
  apply Blocks.primitive_of_rankThree_nondivisibility p (suborbitIndex p)
    (suborbitIndex_self p) (fun x y h => suborbitIndex_transitive (by decide) p x y h)
    ![1, q + q ^ 2, q ^ 3] rfl
  · intro i
    fin_cases i
    · exact card_suborbit_zero p
    · change Nat.card {x : Points 2 F // suborbitIndex p x = 1} = q + q ^ 2
      rw [card_suborbit_one, hperp]
      omega
    · change Nat.card {x : Points 2 F // suborbitIndex p x = 2} = q ^ 3
      rw [card_suborbit_two, hcard, hperp]
      omega
  · change Nat.card (Points 2 F) = 1 + (q + q ^ 2) + q ^ 3
    simpa only [Nat.add_assoc] using hcard
  · change ¬ (1 + (q + q ^ 2)) ∣ Nat.card (Points 2 F)
    simpa only [hcard, ← Nat.add_assoc] using hnd.1
  · change ¬ (1 + q ^ 3) ∣ Nat.card (Points 2 F)
    simpa only [hcard] using hnd.2

end Theory.SpecificGroups.SymplecticFour.SimpleQuotients
