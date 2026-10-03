module

public import Stellmacher.Recognition.LyonsU3Four.TableISurvivorForcing
public import Stellmacher.Recognition.LyonsU3Four.TableISurvivorUInitial
public import Stellmacher.Recognition.LyonsU3Four.TableISurvivorVInitial
import Mathlib.Tactic
/-!
# Unconditional completion of the U/V survivor degrees

Once the first signed degree is −13, reciprocal bounds force the fourth
and middle degrees. Their equation attains the upper reciprocal bound,
forcing both remaining odd degrees to be 65. Positivity then gives degree
52, and the existing prefix calculation supplies degree −12 and its unique
row. In V, the separated degree-13 row excludes middle degrees −139 and
−203 via their prime divisors. No separation of duplicate middle rows is used.

The conditional tail calculations take `x 1 = -13`; the initial U/V
eliminations discharge this from the actual degree, order and prime constraints.
The unconditional prefix constructors retain every normalized coordinate,
and yield all signed degrees and `DegreeTwelveWitness` for the original
normalized degree functions.

Source: R. Lyons, *A Characterization of the Group U₃(4)* (1972),
calculations (U), (V), p. 386.
-/

@[expose] public section
namespace Stellmacher.Recognition.LyonsU3Four
open GeneralizedDecompositionData

private theorem pair_forced {a b : ℤ}
    (ga : a ≤ -63 ∨ 65 ≤ a) (gb : b ≤ -63 ∨ 65 ≤ b)
    (ma : (a + 63) % 64 = 0) (mb : (b + 63) % 64 = 0)
    (he : (4 : ℚ) / a + 1 / b = 1 / 13) : a = 65 ∧ b = 65 := by
  have ba := survivor_inv_bounds (by norm_num : (-63 : ℤ) < 0) (by norm_num : (0 : ℤ) < 65) ga
  have bb := survivor_inv_bounds (by norm_num : (-63 : ℤ) < 0) (by norm_num : (0 : ℤ) < 65) gb
  simp only [div_eq_mul_inv] at he
  constructor
  · by_contra hn
    have gg : a ≤ -63 ∨ 129 ≤ a := by omega
    have hh := (survivor_inv_bounds (by norm_num : (-63 : ℤ) < 0)
      (by norm_num : (0 : ℤ) < 129) gg).2
    norm_num at ba bb hh
    linarith
  · by_contra hn
    have gg : b ≤ -63 ∨ 129 ≤ b := by omega
    have hh := (survivor_inv_bounds (by norm_num : (-63 : ℤ) < 0)
      (by norm_num : (0 : ℤ) < 129) gg).2
    norm_num at ba bb hh
    linarith

namespace SurvivorU

theorem tail_of_x1 {x : Fin 8 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 (degree x))
    (ho : data.OrderConstraints (degree x) g c e) (hx1 : x 1 = -13) :
    x 4 = 39 ∧ x 5 = -150 ∧ x 3 = 65 ∧ x 6 = 65 ∧ x 2 = 52 := by
  have h1 := (equations hd ho).h₁
  have h3 := (equations hd ho).h₃
  have g2 : x 2 ≤ -12 ∨ 52 ≤ x 2 := degree_bounds hd 2 (by decide)
  have g3 : x 3 ≤ -63 ∨ 65 ≤ x 3 := degree_bounds hd 3 (by decide)
  have g4 : x 4 ≤ -25 ∨ 39 ≤ x 4 := degree_bounds hd 4 (by decide)
  have g5 : x 5 ≤ -150 ∨ 42 ≤ x 5 := degree_bounds hd 5 (by decide)
  have g6 : x 6 ≤ -63 ∨ 65 ≤ x 6 := degree_bounds hd 6 (by decide)
  have m2 : (x 2 + 12) % 64 = 0 := degree_mod hd 2
  have m3 : (x 3 + 63) % 64 = 0 := degree_mod hd 3
  have m4 : (x 4 - 39) % 64 = 0 := degree_mod hd 4
  have m5 : (x 5 + 150) % 64 = 0 := degree_mod hd 5
  have m6 : (x 6 + 63) % 64 = 0 := degree_mod hd 6
  have b3 := survivor_inv_bounds (by norm_num : (-63 : ℤ) < 0) (by norm_num : (0 : ℤ) < 65) g3
  have b5 := survivor_inv_bounds (by norm_num : (-150 : ℤ) < 0) (by norm_num : (0 : ℤ) < 42) g5
  have b6 := survivor_inv_bounds (by norm_num : (-63 : ℤ) < 0) (by norm_num : (0 : ℤ) < 65) g6
  rw [hx1] at h1 h3
  norm_num [div_eq_mul_inv] at h1 h3 b3 b5 b6
  have v4 : x 4 = 39 := by
    by_contra hn
    have gg : x 4 ≤ -25 ∨ 103 ≤ x 4 := by omega
    have hh := (survivor_inv_bounds (by norm_num : (-25 : ℤ) < 0)
      (by norm_num : (0 : ℤ) < 103) gg).2
    norm_num at hh
    linarith
  have v5 : x 5 = -150 := by
    by_contra hn
    have gg : x 5 ≤ -214 ∨ 42 ≤ x 5 := by omega
    have hh := (survivor_inv_bounds (by norm_num : (-214 : ℤ) < 0)
      (by norm_num : (0 : ℤ) < 42) gg).1
    norm_num [v4] at h1
    norm_num at hh
    linarith
  have he : (4 : ℚ) / x 3 + 1 / x 6 = 1 / 13 := by
    norm_num [v4, v5] at h1
    simp only [div_eq_mul_inv]
    linarith
  obtain ⟨v3, v6⟩ := pair_forced g3 g6 m3 m6 he
  have v2 : x 2 = 52 := by
    by_contra hn
    have gg : x 2 ≤ -12 ∨ 116 ≤ x 2 := by omega
    have hh := (survivor_inv_bounds (by norm_num : (-12 : ℤ) < 0)
      (by norm_num : (0 : ℤ) < 116) gg).2
    norm_num [v4, v5, v6] at h3
    norm_num at hh
    linarith
  exact ⟨v4, v5, v3, v6, v2⟩

def prefix_of_x1 {x : Fin 8 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 (degree x))
    (ho : data.OrderConstraints (degree x) g c e) (hx1 : x 1 = -13) : UPrefix := by
  have ht := tail_of_x1 hd ho hx1
  have v4 := ht.1
  have v5 := ht.2.1
  have v3 := ht.2.2.1
  have v6 := ht.2.2.2.1
  have v2 := ht.2.2.2.2
  exact {
    x1 := x 1, x2 := x 2, x3 := x 3, x4 := x 4, x5 := x 5, x6 := x 6, x7 := x 7
    h1 := (survivorU1_iff ..).mpr (equations hd ho).h₁
    h2 := (survivorU2_iff ..).mpr (equations hd ho).h₂
    h3 := (survivorU3_iff ..).mpr (equations hd ho).h₃
    hx1 := hx1, hx4 := v4, hx5 := v5, hx3x6 := v3.trans v6.symm
    hx2 := Or.inl v2, hne3 := degree_nonzero hd 3, hne6 := degree_nonzero hd 6
    hne7 := degree_nonzero hd 7
    hpair_eq := by rw [v3, v6]; norm_num
    hx2_not_neg := by omega }


/-- The prefix retains the original normalized coordinates. -/
theorem coordinate_prefix_of_x1 {x : Fin 8 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 (degree x))
    (ho : data.OrderConstraints (degree x) g c e) (hx1 : x 1 = -13) :
    coordinate (prefix_of_x1 hd ho hx1) = x := by
  funext i
  fin_cases i <;> first | exact hd.principal_degree.symm | rfl

/-- The degree-twelve witness follows once the first signed degree is known. -/
def degree_twelve_witness_of_x1 {x : Fin 8 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 (degree x))
    (ho : data.OrderConstraints (degree x) g c e) (hx1 : x 1 = -13) :
    DegreeTwelveWitness data (degree x) := by
  have hw := degree_twelve_witness (prefix_of_x1 hd ho hx1)
  rw [coordinate_prefix_of_x1] at hw
  exact hw

/-- The actual U constraints supply every hypothesis of the arithmetic prefix. -/
def prefix_of_constraints {x : Fin 8 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 (degree x))
    (ho : data.OrderConstraints (degree x) g c e)
    (hp : data.PrimeConstraints (degree x) g) : UPrefix :=
  prefix_of_x1 hd ho (x1_eq_neg_thirteen hd ho hp)

/-- Unconditional prefix construction preserves the normalized degrees. -/
theorem coordinate_prefix_of_constraints {x : Fin 8 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 (degree x))
    (ho : data.OrderConstraints (degree x) g c e)
    (hp : data.PrimeConstraints (degree x) g) :
    coordinate (prefix_of_constraints hd ho hp) = x :=
  coordinate_prefix_of_x1 hd ho (x1_eq_neg_thirteen hd ho hp)

/-- All nonprincipal signed degrees in case U are forced by the actual constraints. -/
theorem degrees_forced {x : Fin 8 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 (degree x))
    (ho : data.OrderConstraints (degree x) g c e)
    (hp : data.PrimeConstraints (degree x) g) :
    x 1 = -13 ∧ x 2 = 52 ∧ x 3 = 65 ∧ x 4 = 39 ∧
      x 5 = -150 ∧ x 6 = 65 ∧ x 7 = -12 :=
  survivorU_forced (prefix_of_constraints hd ho hp)

/-- The actual U constraints yield the unique degree-twelve row and its weight identity. -/
def degree_twelve_witness_of_constraints {x : Fin 8 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 (degree x))
    (ho : data.OrderConstraints (degree x) g c e)
    (hp : data.PrimeConstraints (degree x) g) :
    DegreeTwelveWitness data (degree x) :=
  degree_twelve_witness_of_x1 hd ho (x1_eq_neg_thirteen hd ho hp)

end SurvivorU

namespace SurvivorV

theorem tail_of_x1 {x : Fin 11 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 (degree x))
    (ho : data.OrderConstraints (degree x) g c e)
    (hp : data.PrimeConstraints (degree x) g) (hx1 : x 1 = -13) :
    x 4 = 39 ∧ (∀ i, x (middleIndex i) = -75) ∧ x 3 = 65 ∧ x 9 = 65 ∧ x 2 = 52 := by
  have h1 := (equations hd ho).h₁
  have h3 := (equations hd ho).h₃
  have g2 : x 2 ≤ -12 ∨ 52 ≤ x 2 := degree_bounds hd 2 (by decide)
  have g3 : x 3 ≤ -63 ∨ 65 ≤ x 3 := degree_bounds hd 3 (by decide)
  have g4 : x 4 ≤ -25 ∨ 39 ≤ x 4 := degree_bounds hd 4 (by decide)
  have gm (i : Fin 4) : x (middleIndex i) ≤ -75 ∨ 53 ≤ x (middleIndex i) := by
    have := degree_bounds hd (middleIndex i) (by fin_cases i <;> decide)
    fin_cases i <;> exact this
  have g6 : x 9 ≤ -63 ∨ 65 ≤ x 9 := degree_bounds hd 9 (by decide)
  have m2 : (x 2 + 12) % 64 = 0 := degree_mod hd 2
  have m3 : (x 3 + 63) % 64 = 0 := degree_mod hd 3
  have m4 : (x 4 - 39) % 64 = 0 := degree_mod hd 4
  have mm (i : Fin 4) : (x (middleIndex i) + 75) % 64 = 0 := by
    have := degree_mod hd (middleIndex i)
    fin_cases i <;> exact this
  have m6 : (x 9 + 63) % 64 = 0 := degree_mod hd 9
  have b3 := survivor_inv_bounds (by norm_num : (-63 : ℤ) < 0) (by norm_num : (0 : ℤ) < 65) g3
  have bm (i : Fin 4) := survivor_inv_bounds (by norm_num : (-75 : ℤ) < 0)
    (by norm_num : (0 : ℤ) < 53) (gm i)
  have b6 := survivor_inv_bounds (by norm_num : (-63 : ℤ) < 0) (by norm_num : (0 : ℤ) < 65) g6
  have bm0 := bm 0
  have bm1 := bm 1
  have bm2 := bm 2
  have bm3 := bm 3
  rw [hx1] at h1 h3
  norm_num [Fin.sum_univ_succ, div_eq_mul_inv, middleIndex] at h1 h3 b3 b6 bm0 bm1 bm2 bm3
  have v4 : x 4 = 39 := by
    by_contra hn
    have gg : x 4 ≤ -25 ∨ 103 ≤ x 4 := by omega
    have hh := (survivor_inv_bounds (by norm_num : (-25 : ℤ) < 0)
      (by norm_num : (0 : ℤ) < 103) gg).2
    norm_num at hh
    linarith
  have vm (i : Fin 4) : x (middleIndex i) = -75 := by
    by_contra hn
    have hn139 : x (middleIndex i) ≠ -139 := by
      intro he
      have hh := prime_bound hd hp 1 (Or.inl rfl) (middleIndex i) 139
        (by norm_num) (by rw [he]; norm_num)
      norm_num [hx1] at hh
    have hn203 : x (middleIndex i) ≠ -203 := by
      intro he
      have hh := prime_bound hd hp 1 (Or.inl rfl) (middleIndex i) 29
        (by norm_num) (by rw [he]; norm_num)
      norm_num [hx1] at hh
    have gg : x (middleIndex i) ≤ -267 ∨ 53 ≤ x (middleIndex i) := by
      have := gm i
      have := mm i
      omega
    have hh := (survivor_inv_bounds (by norm_num : (-267 : ℤ) < 0)
      (by norm_num : (0 : ℤ) < 53) gg).1
    norm_num [v4] at h1
    norm_num at hh
    fin_cases i <;> norm_num [middleIndex] at hh <;> linarith
  have he : (4 : ℚ) / x 3 + 1 / x 9 = 1 / 13 := by
    have hh := (equations hd ho).h₁
    simp_rw [hx1, v4, vm] at hh
    norm_num [div_eq_mul_inv] at hh ⊢
    linarith
  obtain ⟨v3, v6⟩ := pair_forced g3 g6 m3 m6 he
  have v2 : x 2 = 52 := by
    by_contra hn
    have gg : x 2 ≤ -12 ∨ 116 ≤ x 2 := by omega
    have hh := (survivor_inv_bounds (by norm_num : (-12 : ℤ) < 0)
      (by norm_num : (0 : ℤ) < 116) gg).2
    have hpos := (equations hd ho).h₃
    simp_rw [hx1, v4, v6, vm] at hpos
    norm_num [div_eq_mul_inv] at hpos hh
    linarith
  exact ⟨v4, vm, v3, v6, v2⟩

def prefix_of_x1 {x : Fin 11 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 (degree x))
    (ho : data.OrderConstraints (degree x) g c e)
    (hp : data.PrimeConstraints (degree x) g) (hx1 : x 1 = -13) : VPrefix := by
  have ht := tail_of_x1 hd ho hp hx1
  have v4 := ht.1
  have vm := ht.2.1
  have v3 := ht.2.2.1
  have v6 := ht.2.2.2.1
  have v2 := ht.2.2.2.2
  exact {
    x1 := x 1, x2 := x 2, x3 := x 3, x4 := x 4, x6 := x 9, x7 := x 10
    middle := fun i => x (middleIndex i)
    h1 := by exact (equations hd ho).h₁
    h2 := (survivorU2_iff ..).mpr (equations hd ho).h₂
    h3 := by exact (equations hd ho).h₃
    hx1 := hx1, hx4 := v4, hmiddle := vm, hx3x6 := v3.trans v6.symm
    hx2 := Or.inl v2, hne3 := degree_nonzero hd 3, hne6 := degree_nonzero hd 9
    hne7 := degree_nonzero hd 10
    hpair_eq := by rw [v3, v6]; norm_num
    hx2_not_neg := by omega }


/-- The prefix retains the original normalized coordinates. -/
theorem coordinate_prefix_of_x1 {x : Fin 11 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 (degree x))
    (ho : data.OrderConstraints (degree x) g c e)
    (hp : data.PrimeConstraints (degree x) g) (hx1 : x 1 = -13) :
    coordinate (prefix_of_x1 hd ho hp hx1) = x := by
  funext i
  fin_cases i <;> first | exact hd.principal_degree.symm | rfl

/-- The degree-twelve witness follows once the first signed degree is known. -/
def degree_twelve_witness_of_x1 {x : Fin 11 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 (degree x))
    (ho : data.OrderConstraints (degree x) g c e)
    (hp : data.PrimeConstraints (degree x) g) (hx1 : x 1 = -13) :
    DegreeTwelveWitness data (degree x) := by
  have hw := degree_twelve_witness (prefix_of_x1 hd ho hp hx1)
  rw [coordinate_prefix_of_x1] at hw
  exact hw

/-- The actual V constraints supply every hypothesis of the arithmetic prefix. -/
def prefix_of_constraints {x : Fin 11 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 (degree x))
    (ho : data.OrderConstraints (degree x) g c e)
    (hp : data.PrimeConstraints (degree x) g) : VPrefix :=
  prefix_of_x1 hd ho hp (x1_eq_neg_thirteen hd ho hp)

/-- Unconditional prefix construction preserves all four independent middle degrees. -/
theorem coordinate_prefix_of_constraints {x : Fin 11 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 (degree x))
    (ho : data.OrderConstraints (degree x) g c e)
    (hp : data.PrimeConstraints (degree x) g) :
    coordinate (prefix_of_constraints hd ho hp) = x :=
  coordinate_prefix_of_x1 hd ho hp (x1_eq_neg_thirteen hd ho hp)

/-- All signed degrees in case V are forced; printed degrees six and seven use indices nine
and ten because the four middle degrees have independent coordinates. -/
theorem degrees_forced {x : Fin 11 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 (degree x))
    (ho : data.OrderConstraints (degree x) g c e)
    (hp : data.PrimeConstraints (degree x) g) :
    x 1 = -13 ∧ x 2 = 52 ∧ x 3 = 65 ∧ x 4 = 39 ∧
      (∀ i, x (middleIndex i) = -75) ∧ x 9 = 65 ∧ x 10 = -12 :=
  survivorV_forced (prefix_of_constraints hd ho hp)

/-- The actual V constraints yield the unique degree-twelve row and its weight identity. -/
def degree_twelve_witness_of_constraints {x : Fin 11 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 (degree x))
    (ho : data.OrderConstraints (degree x) g c e)
    (hp : data.PrimeConstraints (degree x) g) :
    DegreeTwelveWitness data (degree x) :=
  degree_twelve_witness_of_x1 hd ho hp (x1_eq_neg_thirteen hd ho hp)

end SurvivorV
end Stellmacher.Recognition.LyonsU3Four
