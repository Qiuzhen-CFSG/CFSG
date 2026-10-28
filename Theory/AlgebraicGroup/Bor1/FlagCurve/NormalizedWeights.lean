module

public import Theory.AlgebraicGroup.Bor1.FlagCurve.WeightNormalization
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Coprime weights for the literal projective torus orbit

Starting with an occupied zero weight and an occupied positive weight, divide
all occupied exponents by their gcd and zero the unused coordinates. The
result has coprime exponents, actual occupied extrema and bounded weights,
while preserving the full unit-parameter orbit over an algebraically closed
field. This is the characteristic-sensitive normalization step in Borel §13.13.
-/

public noncomputable section

namespace Theory.AlgebraicGroup.Bor1.FlagCurve
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] {ι : Type} [Fintype ι]

theorem exists_normalized_monomial_weights
    (c : ι → k) (n : ι → ℕ) (a b : ι)
    (ha : n a = 0) (hca : c a ≠ 0) (hb : n b ≠ 0) (hcb : c b ≠ 0) :
    ∃ (m : ι → ℕ) (N : ℕ) (j : ι) (s : Finset ι),
      0 < N ∧ m a = 0 ∧ m j = N ∧ c j ≠ 0 ∧ a ∈ s ∧
      (∀ l ∈ s, c l ≠ 0) ∧ s.gcd m = 1 ∧ (∀ l, m l ≤ N) ∧
      Set.range (fun t : kˣ => fun l => c l * (t : k) ^ n l) =
        Set.range (fun t : kˣ => fun l => c l * (t : k) ^ m l) := by
  classical
  let s := Finset.univ.filter (fun i => c i ≠ 0)
  have has : a ∈ s := by simp [s, hca]
  have hbs : b ∈ s := by simp [s, hcb]
  let d := s.gcd n
  let m := fun i => if c i = 0 then 0 else n i / d
  have hms (i : ι) (hi : i ∈ s) : m i = n i / d := by
    have hc := (Finset.mem_filter.mp hi).2
    simp [m, hc]
  have hma : m a = 0 := by simp [m, ha]
  have hgcd : s.gcd m = 1 := by
    rw [Finset.gcd_congr rfl hms]
    exact Finset.gcd_div_eq_one hbs hb
  obtain ⟨j, hj, hmax⟩ := Finset.exists_mem_eq_sup s ⟨a, has⟩ m
  let N := s.sup m
  have hbound (l : ι) : m l ≤ N := by
    by_cases hl : l ∈ s
    · exact Finset.le_sup hl
    · have hc : c l = 0 := by simpa [s] using hl
      simp [m, hc]
  have hN : 0 < N := by
    by_contra hN
    have hNz : N = 0 := Nat.eq_zero_of_not_pos hN
    have hmzero : ∀ l ∈ s, m l = 0 := by
      intro l _
      exact Nat.eq_zero_of_le_zero (hNz ▸ hbound l)
    have hz := Finset.gcd_eq_zero_iff.mpr hmzero
    rw [hgcd] at hz
    exact one_ne_zero hz
  refine ⟨m, N, j, s, hN, hma, hmax.symm,
    (Finset.mem_filter.mp hj).2, has, fun l hl => (Finset.mem_filter.mp hl).2, hgcd, hbound, ?_⟩
  rw [monomial_orbit_range_normalize s c n
    (fun l hl => by simpa [s] using hl) b hbs hb]
  congr 1
  funext t l
  by_cases hl : c l = 0
  · simp [hl]
  · simp [m, hl, d]

end Theory.AlgebraicGroup.Bor1.FlagCurve
