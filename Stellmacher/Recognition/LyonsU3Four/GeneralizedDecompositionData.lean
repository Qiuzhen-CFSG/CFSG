module

public import Theory.Character.ModularBlock.Congruence
public import Mathlib.Data.Int.ModEq
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-!
# The ambient columns in Lyons's Table I calculation

For fixed elements `t` of order four and `z = t²`, Lyons uses one column `dᵗ`
and five columns `ᵢdᶻ`. The subscript `i` labels the basis
`1, μ, μ², μ⁴, μ³`; it is not the imaginary unit. All six columns are integral.
We separate the integer matrix and its numerical Table I hypotheses from
its realization by actual characters of the ambient principal two-block.

`Equation3_1` is the expansion on odd parts of the two sections. `Equation3_2`
is the Gram matrix identity, `ContributionBound` is the strict inequality
(3.3), and `Equation3_4` is the congruence modulo four. `GaloisSymmetry`
permutes rows and rotates the last four columns. Besides these identities,
the pattern argument uses the principal row and nonvanishing at `z`.
The latter is made explicit rather than allowing arbitrary zero rows.

The small proofs convert the integer formulation to complex inner products,
derive rationality and automorphism invariance of entries, and extract
finite bounds from the contribution inequality. This module supplies an
interface: existence for the actual local groups and classification into
Table I are separate results, not assumptions asserted as theorems here.

Source: R. Lyons, *A Characterization of the Group U₃(4)*, Trans. Amer. Math.
Soc. 164 (1972), pp. 373--375, equations (3.1)--(3.4), Table I; the explicit
principal-row normalization and nonvanishing used in its proof are on
pp. 377--378. Local source:
`refs/original/n-group-global/odd-core-rank-two-source/lyons-u3four-1972-ams-wayback.pdf`.
-/

@[expose] public section
namespace Stellmacher.Recognition.LyonsU3Four
open scoped BigOperators

/-- Six integral columns indexed by the ordinary principal-block rows.
`iDz 0` through `iDz 4` are Lyons's columns `₁dᶻ` through `₅dᶻ`. -/
structure GeneralizedDecompositionData (I : Type*) where
  dT : I → ℤ
  iDz : Fin 5 → I → ℤ

namespace GeneralizedDecompositionData
variable {I : Type*}

/-- Exponents in Lyons's ordered local basic set. -/
def basicExponent : Fin 5 → ℕ := ![0, 1, 2, 4, 3]

/-- Column permutation in the displayed Galois identities on p. 374. -/
def galoisColumn : Fin 5 → Fin 5 := ![0, 4, 1, 2, 3]

theorem galoisColumn_four (i : Fin 5) :
    galoisColumn (galoisColumn (galoisColumn (galoisColumn i))) = i := by
  fin_cases i <;> rfl

theorem galoisColumn_exponent (i : Fin 5) :
    (2 * basicExponent (galoisColumn i)) % 5 = basicExponent i := by
  fin_cases i <;> rfl

variable (d : GeneralizedDecompositionData I)

/-- Character value at `z`, since every member of the local basic set has degree one. -/
def zValue (j : I) : ℤ := ∑ i, d.iDz i j

/-- The numerator of the combined section contribution in (3.3).
Each unordered pair of the five columns occurs exactly once. -/
def contribution (j : I) : ℤ :=
  4 * d.dT j ^ 2 + (∑ i, d.iDz i j ^ 2) +
    3 * ∑ i : Fin 5, ∑ h ∈ Finset.Iio i, (d.iDz h j - d.iDz i j) ^ 2

/-- Equation (3.1), on all odd-order elements of the two centralizers. -/
def Equation3_1 {G : Type*} [Group G] (χ : I → G → ℂ) (t z : G)
    (μ : Subgroup.centralizer ({z} : Set G) →* ℂ) : Prop :=
  (∀ j (ρ : Subgroup.centralizer ({t} : Set G)), Odd (orderOf ρ) →
    χ j (t * (ρ : G)) = (d.dT j : ℂ)) ∧
  (∀ j (π : Subgroup.centralizer ({z} : Set G)), Odd (orderOf π) →
    χ j (z * (π : G)) = ∑ i, (d.iDz i j : ℂ) * μ π ^ basicExponent i)

theorem Equation3_1.at_t {G : Type*} [Group G] {χ : I → G → ℂ} {t z : G}
    {μ : Subgroup.centralizer ({z} : Set G) →* ℂ}
    (h : d.Equation3_1 χ t z μ) (j : I) : χ j t = (d.dT j : ℂ) := by
  simpa using h.1 j 1 (by simp)

theorem Equation3_1.at_z {G : Type*} [Group G] {χ : I → G → ℂ} {t z : G}
    {μ : Subgroup.centralizer ({z} : Set G) →* ℂ}
    (h : d.Equation3_1 χ t z μ) (j : I) : χ j z = (d.zValue j : ℂ) := by
  simpa [zValue] using h.2 j 1 (by simp)

/-- Rationality of the column `dᵗ`. This does not assert rationality of an
entire ordinary character. -/
theorem dT_rational (j : I) : ∃ q : ℚ, (d.dT j : ℂ) = (q : ℂ) := by
  exact ⟨(d.dT j : ℚ), by simp⟩

/-- Rationality of each column `ᵢdᶻ`. -/
theorem iDz_rational (i : Fin 5) (j : I) :
    ∃ q : ℚ, (d.iDz i j : ℂ) = (q : ℂ) := by
  exact ⟨(d.iDz i j : ℚ), by simp⟩

theorem dT_galois_fixed (σ : ℂ ≃+* ℂ) (j : I) :
    σ (d.dT j : ℂ) = (d.dT j : ℂ) := by simp

theorem iDz_galois_fixed (σ : ℂ ≃+* ℂ) (i : Fin 5) (j : I) :
    σ (d.iDz i j : ℂ) = (d.iDz i j : ℂ) := by simp

/-- Galois symmetry is a row permutation, not just conjugation of entries.
For `k = σ j` the column identities read
`dᵗⱼ = dᵗₖ`, `₁dᶻⱼ = ₁dᶻₖ`, `₂dᶻⱼ = ₅dᶻₖ`,
`₃dᶻⱼ = ₂dᶻₖ`, `₄dᶻⱼ = ₃dᶻₖ`, `₅dᶻⱼ = ₄dᶻₖ`. -/
def GaloisSymmetry : Prop :=
  ∃ σ : Equiv.Perm I, ∀ j,
    d.dT j = d.dT (σ j) ∧ ∀ i, d.iDz i j = d.iDz (galoisColumn i) (σ j)

/-- The strict contribution inequality (3.3). -/
def ContributionBound : Prop := ∀ j, d.contribution j < 64

theorem contribution_nonneg (j : I) : 0 ≤ d.contribution j := by
  unfold contribution
  positivity

theorem four_mul_dT_sq_le_contribution (j : I) :
    4 * d.dT j ^ 2 ≤ d.contribution j := by
  have h₁ : 0 ≤ ∑ i : Fin 5, d.iDz i j ^ 2 := by positivity
  have h₂ : 0 ≤ ∑ i : Fin 5, ∑ h ∈ Finset.Iio i,
      (d.iDz h j - d.iDz i j) ^ 2 := by positivity
  unfold contribution
  linarith

theorem iDz_sq_le_contribution (i : Fin 5) (j : I) :
    d.iDz i j ^ 2 ≤ d.contribution j := by
  have h₁ : d.iDz i j ^ 2 ≤ ∑ k : Fin 5, d.iDz k j ^ 2 :=
    Finset.single_le_sum (fun k _ => sq_nonneg (d.iDz k j)) (Finset.mem_univ i)
  have h₂ : 0 ≤ ∑ k : Fin 5, ∑ h ∈ Finset.Iio k,
      (d.iDz h j - d.iDz k j) ^ 2 := by positivity
  unfold contribution
  nlinarith [sq_nonneg (d.dT j)]

/-- The order-four column entries lie in `[-3,3]`. -/
theorem ContributionBound.dT_bounds (h : d.ContributionBound) (j : I) :
    -3 ≤ d.dT j ∧ d.dT j ≤ 3 := by
  have hb := lt_of_le_of_lt (d.four_mul_dT_sq_le_contribution j) (h j)
  constructor <;> nlinarith [sq_nonneg (d.dT j + 4), sq_nonneg (d.dT j - 4)]

/-- An initial finite bound on the five involution columns. -/
theorem ContributionBound.iDz_bounds (h : d.ContributionBound) (i : Fin 5) (j : I) :
    -7 ≤ d.iDz i j ∧ d.iDz i j ≤ 7 := by
  have hb := lt_of_le_of_lt (d.iDz_sq_le_contribution i j) (h j)
  constructor <;> nlinarith [sq_nonneg (d.iDz i j + 8), sq_nonneg (d.iDz i j - 8)]

/-- Equation (3.4), obtained from `χ(z) ≡ χ(t) (mod 4)`. -/
def Equation3_4 : Prop := ∀ j, Int.ModEq 4 (d.dT j) (d.zValue j)

variable [Fintype I]

/-- Integer form of Lyons's Hermitian inner product, valid because all entries
are integers. -/
def columnInner (a b : I → ℤ) : ℤ := ∑ j, a j * b j

theorem columnInner_complex (a b : I → ℤ) :
    ∑ j, (a j : ℂ) * star (b j : ℂ) = (columnInner a b : ℂ) := by
  simp [columnInner]

/-- All three identities in (3.2), with fixed diagonal 16 and off-diagonal 12. -/
structure Equation3_2 : Prop where
  tt : columnInner d.dT d.dT = 16
  tz : ∀ i, columnInner d.dT (d.iDz i) = 0
  zz : ∀ i k, columnInner (d.iDz i) (d.iDz k) = 4 * (3 + if i = k then 1 else 0)

theorem Equation3_2.complex_tt (h : d.Equation3_2) :
    ∑ j, (d.dT j : ℂ) * star (d.dT j : ℂ) = 16 := by
  rw [columnInner_complex, h.tt]
  norm_num

theorem Equation3_2.complex_tz (h : d.Equation3_2) (i : Fin 5) :
    ∑ j, (d.dT j : ℂ) * star (d.iDz i j : ℂ) = 0 := by
  rw [columnInner_complex, h.tz]
  norm_num

theorem Equation3_2.complex_zz (h : d.Equation3_2) (i k : Fin 5) :
    ∑ j, (d.iDz i j : ℂ) * star (d.iDz k j : ℂ) =
      4 * (3 + if i = k then 1 else 0) := by
  rw [columnInner_complex, h.zz]
  push_cast
  rfl

/-- Numerical input to the Table I classification. The distinguished principal
row and nonzero `χ(z)` are also used in the proof (pp. 377--378). Without the
last hypothesis arbitrary zero rows could be added to a matrix. -/
structure TableIPatternHypotheses (principal : I) : Prop where
  equation_3_2 : d.Equation3_2
  equation_3_3 : d.ContributionBound
  equation_3_4 : d.Equation3_4
  galois_symmetry : d.GaloisSymmetry
  principal_dT : d.dT principal = 1
  principal_iDz : ∀ i, d.iDz i principal = if i = 0 then 1 else 0
  z_nonzero : ∀ j, d.zValue j ≠ 0

end GeneralizedDecompositionData

open ModularBlock.PrincipalBlockConstruction

/-- Connection to the actual ambient principal block. The row type is exactly
the subtype of principal-block indices. A realization must supply every
numerical hypothesis, as well as the genuine character expansion (3.1).
No existence assertion is made by this structure. -/
structure AmbientGeneralizedDecompositionData
    {G : Type*} [Group G] [Finite G] (b : PrincipalCongruenceBlockData G)
    (t z : G) (μ : Subgroup.centralizer ({z} : Set G) →* ℂ) where
  order_t : orderOf t = 4
  square_t : t ^ 2 = z
  order_mu : orderOf μ = 5
  columns : GeneralizedDecompositionData {j // j ∈ b.block}
  equation_3_1 : columns.Equation3_1
    (fun j g => b.chi j.1 (ConjClasses.mk g)) t z μ
  pattern : columns.TableIPatternHypotheses ⟨b.principal, b.principal_mem⟩

end Stellmacher.Recognition.LyonsU3Four
