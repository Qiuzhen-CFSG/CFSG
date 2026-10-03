module

public import Stellmacher.Recognition.LyonsU3Four.GeneralizedDecompositionData

/-!
# Degree constraints for Lyons's Table I

Table I permits a sign change in each row. Its last column therefore contains
signed degrees, not necessarily positive character degrees. The functional
`weightedColumn` is Lyons's `L` divided by the group order. `DegreeConstraints`
records Lemma 5, including the sign of the restriction multiplicity, and the
degree invariance under the Galois permutation from §3;
`OrderConstraints` records Lemma 4 with denominators cleared.

The prime bound used in the elimination is stronger than integrality of the
decomposition columns. `PrimeConstraints` keeps it as a separate input: a row
separated by its degree and its six entries, up to simultaneous sign, has its
character field contained in the fifth cyclotomic field. Schur then bounds all
prime divisors of the group order. Realizing this input requires character
Galois transport; the single row permutation in `GaloisSymmetry` alone does not
supply it.

These are interfaces for the numerical elimination, with no assertion of
existence. The ambient realization must establish them from actual characters.
Source: R. Lyons, *A Characterization of the Group U₃(4)*, Trans. Amer. Math.
Soc. 164 (1972), Lemmas 4–5 and (*), pp. 381–382. Local source:
`refs/original/n-group-global/odd-core-rank-two-source/lyons-u3four-1972-ams-wayback.pdf`.
-/

@[expose] public section
namespace Stellmacher.Recognition.LyonsU3Four.GeneralizedDecompositionData
open scoped BigOperators
variable {I : Type*} [Fintype I]

/-- The normalized class-product functional `L(a) / |G|`. The degrees and
columns have undergone the same row sign changes. -/
def weightedColumn (d : GeneralizedDecompositionData I) (degree : I → ℤ)
    (a : I → ℤ) : ℚ :=
  ∑ j, (d.zValue j : ℚ) ^ 2 * (a j : ℚ) / (degree j : ℚ)

theorem weightedColumn_sub (d : GeneralizedDecompositionData I)
    (degree a b : I → ℤ) :
    d.weightedColumn degree (fun j => a j - b j) =
      d.weightedColumn degree a - d.weightedColumn degree b := by
  simp only [weightedColumn, Int.cast_sub, mul_sub, sub_div, Finset.sum_sub_distrib]

/-- Galois conjugation preserves the actual positive degree. The relative
sign appears when two conjugate rows have been normalized independently. -/
def SignedGaloisSymmetry (d : GeneralizedDecompositionData I)
    (degree : I → ℤ) : Prop :=
  ∃ σ : Equiv.Perm I, ∀ j, ∃ ε : ℤ, ε ^ 2 = 1 ∧
    degree j = ε * degree (σ j) ∧ d.dT j = ε * d.dT (σ j) ∧
      ∀ i, d.iDz i j = ε * d.iDz (galoisColumn i) (σ j)

/-- Lemma 5 in signed coordinates. The product in `multiplicity_nonneg`
accounts for the sign of the row; requiring the numerator itself to be
nonnegative would incorrectly discard negative signed degrees. -/
structure DegreeConstraints (d : GeneralizedDecompositionData I)
    (principal : I) (degree : I → ℤ) : Prop where
  principal_degree : degree principal = 1
  degree_nonzero : ∀ j, degree j ≠ 0
  degree_lower : ∀ j, j ≠ principal → 12 ≤ (degree j).natAbs
  multiplicity_integral : ∀ j,
    Int.ModEq 64 (degree j + 3 * d.zValue j + 60 * d.dT j) 0
  multiplicity_nonneg : ∀ j,
    0 ≤ degree j * (degree j + 3 * d.zValue j + 60 * d.dT j)
  orthogonal_t : columnInner degree d.dT = 0
  orthogonal_z : ∀ i, columnInner degree (d.iDz i) = 0
  galois_symmetry : d.SignedGaloisSymmetry degree

/-- Lemma 4, with `g = |G|`, `c = |C_G(z)|`, and `e = |C_G(Z(T))|`.
The coefficient is 128 here; 195 appears only after evaluating the surviving
character degrees. -/
structure OrderConstraints (d : GeneralizedDecompositionData I)
    (degree : I → ℤ) (g c e : ℕ) : Prop where
  group_pos : 0 < g
  centralizer_pos : 0 < c
  center_centralizer_pos : 0 < e
  zero_t : d.weightedColumn degree d.dT = 0
  equal_z : ∀ i, d.weightedColumn degree (d.iDz i) =
    d.weightedColumn degree (d.iDz 0)
  centralizer_identity :
    (g : ℚ) * e ^ 2 * d.weightedColumn degree (d.iDz 0) = 128 * c ^ 3

/-- Separation invariant under the simultaneous sign changes of Table I.
The degree is included because equal columns can have distinct degrees. -/
def RowSeparated (d : GeneralizedDecompositionData I) (degree : I → ℤ)
    (j : I) : Prop :=
  ∀ k ε, ε ^ 2 = (1 : ℤ) → degree k = ε * degree j →
    d.dT k = ε * d.dT j → (∀ i, d.iDz i k = ε * d.iDz i j) → k = j

/-- Degree divisibility and the consequence (*) of Schur's theorem used on
pp. 382–386. The ambient character argument must establish this input. -/
structure PrimeConstraints (d : GeneralizedDecompositionData I)
    (degree : I → ℤ) (g : ℕ) : Prop where
  degree_dvd : ∀ j, (degree j).natAbs ∣ g
  prime_bound : ∀ j, 5 < (degree j).natAbs → d.RowSeparated degree j →
    ∀ p : ℕ, p.Prime → p ∣ g → p ≤ (degree j).natAbs + 1

omit [Fintype I] in
/-- The frequently used form of (*): primes in any other character degree
are bounded by the degree of a separated row plus one. -/
theorem PrimeConstraints.prime_dvd_degree_le
    {d : GeneralizedDecompositionData I} {degree : I → ℤ} {g : ℕ}
    (h : d.PrimeConstraints degree g) {j : I}
    (hj : 5 < (degree j).natAbs) (hsep : d.RowSeparated degree j)
    (k : I) {p : ℕ} (hp : p.Prime) (hpk : p ∣ (degree k).natAbs) :
    p ≤ (degree j).natAbs + 1 :=
  h.prime_bound j hj hsep p hp (hpk.trans (h.degree_dvd k))

/-- Evaluation of the remaining weighted column gives equation (4.1). -/
theorem OrderConstraints.centralizer_formula
    {d : GeneralizedDecompositionData I} {degree : I → ℤ} {g c e : ℕ}
    (h : d.OrderConstraints degree g c e)
    (hvalue : d.weightedColumn degree (d.iDz 0) = 128 / 195) :
    g * e ^ 2 = 195 * c ^ 3 := by
  have he : (g : ℚ) * e ^ 2 = 195 * c ^ 3 := by
    have hi := h.centralizer_identity
    rw [hvalue] at hi
    linarith
  exact_mod_cast he

end Stellmacher.Recognition.LyonsU3Four.GeneralizedDecompositionData
