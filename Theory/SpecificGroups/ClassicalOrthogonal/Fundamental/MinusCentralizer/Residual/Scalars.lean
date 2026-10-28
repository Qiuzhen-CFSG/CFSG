module

public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.MinusCentralizer.Residual.Basic
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Common scalar kernels and the minus discriminant

The published square-one scalar kernel reduces to identity or simultaneous
negation. If complementary negation belongs to the actual commutator group,
the kernel is precisely its diagonal cyclic subgroup of order two; otherwise
the block map is injective.

For the chosen anisotropic-plane parameter `a`, completing the square shows
that `1 + 4 * a` is nonsquare. The quadratic character then shows that
`(-1)^m * (1 + 4*a)` is square exactly for odd `m` and field cardinality
congruent to three modulo four. The final adapters explicitly retain the
separate commutator-membership/spinor comparison; this file does not assert it.

Source: Aschbacher–Smith A.2.17, printed p.39, and GLS3 §2.7, printed pp.88–89.
The latter gives the minus center factor `(4, q^m + 1) / 2`. All kernel
statements here use the literal published complementary commutator carrier.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Matrix Theory.AlgebraicGroup
namespace ClassicalOrthogonal.Fundamental.MinusCentralizer
open FourPlusMatrix TheoremDRootNormalizer.HigherRanks
variable {F : Type*} [Field F]

/-- The kernel consists exactly of the identity and the common negative scalar, when present. -/
theorem projectiveBlockHom_kernel_signs [Finite F] (r : ℕ) (hq : 2 < Nat.card F)
    (g : SpecialLinearGroup (Fin 2) F ×
      Minus.Omega F (Minus.Space F r) (Minus.quadraticForm F (r + 1))) :
    projectiveBlockHom r hq g = 1 ↔
      g = 1 ∨ g.1 = negativeSL ∧ g.2.val = negativeComplement r := by
  rw [projectiveBlockHom_kernel_commonScalar]
  constructor
  · rintro ⟨c, hc, h1, h2⟩
    rcases sq_eq_one_iff.mp hc with hc | hc
    · left
      apply Prod.ext
      · apply Subtype.ext
        simpa [hc] using h1
      · apply Subtype.ext
        apply Subtype.ext
        apply LinearEquiv.ext
        intro v
        simpa [hc] using h2 v
    · right
      constructor
      · apply Subtype.ext
        simpa [hc, negativeSL] using h1
      · apply Subtype.ext
        apply LinearEquiv.ext
        intro v
        simpa [hc, negativeComplement] using h2 v
  · rintro (rfl | ⟨h1, h2⟩)
    · exact ⟨1, by simp, by simp, fun _ => by simp⟩
    · refine ⟨-1, by simp, ?_, ?_⟩
      · simp [h1, negativeSL]
      · intro v
        rw [h2]
        simp [negativeComplement]

/-- The only obstruction to injectivity is actual complementary Omega membership of negation. -/
theorem projectiveBlockHom_injective_iff [Finite F]
    (r : ℕ) (hq : 2 < Nat.card F) (h2 : (2 : F) ≠ 0) :
    Function.Injective (projectiveBlockHom r hq) ↔
      negativeComplement (F := F) r ∉
        Minus.Omega F (Minus.Space F r) (Minus.quadraticForm F (r + 1)) := by
  constructor
  · intro hinj hm
    let z : SpecialLinearGroup (Fin 2) F ×
        Minus.Omega F (Minus.Space F r) (Minus.quadraticForm F (r + 1)) :=
      (negativeSL (F := F), ⟨negativeComplement r, hm⟩)
    have hz : projectiveBlockHom r hq z = 1 :=
      (projectiveBlockHom_kernel_signs r hq z).mpr (Or.inr ⟨rfl, rfl⟩)
    have he := hinj (hz.trans (map_one _).symm)
    have hh := congrArg (fun g => g.1.val 0 0) he
    have hn : (-1 : F) = 1 := by simpa [z, negativeSL] using hh
    apply h2
    calc
      (2 : F) = 1 - (-1) := by ring
      _ = 0 := by rw [hn, sub_self]
  · intro hn
    apply (injective_iff_map_eq_one _).mpr
    intro g hg
    rcases (projectiveBlockHom_kernel_signs r hq g).mp hg with hg | ⟨_, hg⟩
    · exact hg
    · exact False.elim (hn (hg ▸ g.2.property))

/-- Injectivity after supplying the separate complementary scalar-membership theorem. -/
theorem projectiveBlockHom_injective_iff_of_scalarCriterion [Finite F]
    (r : ℕ) (hq : 2 < Nat.card F) (h2 : (2 : F) ≠ 0)
    (hscalar : negativeComplement (F := F) r ∈
      Minus.Omega F (Minus.Space F r) (Minus.quadraticForm F (r + 1)) ↔
      Odd (r + 1) ∧ Nat.card F % 4 = 3) :
    Function.Injective (projectiveBlockHom r hq) ↔
      ¬ (Odd (r + 1) ∧ Nat.card F % 4 = 3) := by
  rw [projectiveBlockHom_injective_iff r hq h2, hscalar]

/-- The discriminant of the chosen anisotropic plane is nonsquare in odd characteristic. -/
theorem parameter_discriminant_nonsquare [Finite F] (h2 : (2 : F) ≠ 0) :
    ¬ IsSquare ((1 : F) + 4 * Minus.parameter F) := by
  rintro ⟨t, ht⟩
  apply Minus.parameter_spec F ((t - 1) / 2)
  have h4 : (4 : F) ≠ 0 := by
    have hh := mul_ne_zero h2 h2
    norm_num at hh ⊢
    exact hh
  apply mul_left_cancel₀ h4
  calc
    4 * (((t - 1) / 2) ^ 2 + (t - 1) / 2) = t * t - 1 := by
      field_simp [h2]
      ring
    _ = 4 * Minus.parameter F := by linear_combination -ht

/-- The square-class arithmetic for the minus form in dimension `2 * m`. -/
theorem minus_discriminant_isSquare_iff [Finite F] (h2 : (2 : F) ≠ 0) (m : ℕ) :
    IsSquare ((-1 : F) ^ m * (1 + 4 * Minus.parameter F)) ↔
      Odd m ∧ Nat.card F % 4 = 3 := by
  classical
  let := Fintype.ofFinite F
  have hd := parameter_discriminant_nonsquare (F := F) h2
  have hd0 : (1 : F) + 4 * Minus.parameter F ≠ 0 := by
    intro hz
    exact hd (hz ▸ IsSquare.zero)
  have hn : IsSquare (-((1 : F) + 4 * Minus.parameter F)) ↔ Nat.card F % 4 = 3 := by
    rw [← quadraticChar_one_iff_isSquare (neg_ne_zero.mpr hd0)]
    rw [← neg_one_mul ((1 : F) + 4 * Minus.parameter F), map_mul,
      quadraticChar_neg_one_iff_not_isSquare.mpr hd, mul_neg_one,
      neg_eq_iff_eq_neg, quadraticChar_neg_one_iff_not_isSquare,
      FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card, not_not]
  rcases Nat.even_or_odd m with hm | hm
  · have hno : ¬ Odd m := Nat.not_odd_iff_even.mpr hm
    simp [hm.neg_one_pow, hd, hno]
  · simpa [hm.neg_one_pow, hm] using hn


/-- The common negative scalar, given its membership in the actual complementary commutator. -/
def commonNegative [Finite F] (r : ℕ)
    (hneg : negativeComplement (F := F) r ∈
      Minus.Omega F (Minus.Space F r) (Minus.quadraticForm F (r + 1))) :
    SpecialLinearGroup (Fin 2) F ×
      Minus.Omega F (Minus.Space F r) (Minus.quadraticForm F (r + 1)) :=
  (negativeSL, ⟨negativeComplement r, hneg⟩)

/-- When the common negative scalar exists, it generates the entire projective kernel. -/
theorem projectiveBlockHom_kernel_eq_zpowers [Finite F] (r : ℕ) (hq : 2 < Nat.card F)
    (hneg : negativeComplement (F := F) r ∈
      Minus.Omega F (Minus.Space F r) (Minus.quadraticForm F (r + 1))) :
    (projectiveBlockHom r hq).ker = Subgroup.zpowers (commonNegative r hneg) := by
  apply le_antisymm
  · intro g hg
    rcases (projectiveBlockHom_kernel_signs r hq g).mp hg with hg | ⟨h1, h2⟩
    · rw [hg]
      exact Subgroup.one_mem _
    · have he : g = commonNegative r hneg := Prod.ext h1 (Subtype.ext h2)
      rw [he]
      exact Subgroup.mem_zpowers _
  · intro g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    apply Subgroup.zpow_mem
    exact (projectiveBlockHom_kernel_signs r hq _).mpr (Or.inr ⟨rfl, rfl⟩)

/-- In odd characteristic the common negative scalar has order two. -/
theorem commonNegative_order [Finite F] (r : ℕ) (hq : 2 < Nat.card F)
    (h2 : (2 : F) ≠ 0)
    (hneg : negativeComplement (F := F) r ∈
      Minus.Omega F (Minus.Space F r) (Minus.quadraticForm F (r + 1))) :
    orderOf (commonNegative r hneg) = 2 := by
  apply orderOf_eq_prime
  · exact projectiveBlockHom_kernel_square r hq _
      ((projectiveBlockHom_kernel_signs r hq _).mpr (Or.inr ⟨rfl, rfl⟩))
  · intro he
    have hh := congrArg (fun g => g.1.val 0 0) he
    have hn : (-1 : F) = 1 := by simpa [commonNegative, negativeSL] using hh
    apply h2
    calc
      (2 : F) = 1 - (-1) := by ring
      _ = 0 := by rw [hn, sub_self]

/-- A complementary negative scalar gives a kernel of order two. -/
theorem projectiveBlockHom_kernel_card_of_mem [Finite F] (r : ℕ) (hq : 2 < Nat.card F)
    (h2 : (2 : F) ≠ 0)
    (hneg : negativeComplement (F := F) r ∈
      Minus.Omega F (Minus.Space F r) (Minus.quadraticForm F (r + 1))) :
    Nat.card (projectiveBlockHom r hq).ker = 2 := by
  rw [projectiveBlockHom_kernel_eq_zpowers r hq hneg, Nat.card_zpowers,
    commonNegative_order r hq h2 hneg]

/-- The precise kernel order after the scalar-membership calculation is supplied. -/
theorem projectiveBlockHom_kernel_card_of_scalarCriterion [Finite F]
    (r : ℕ) (hq : 2 < Nat.card F) (h2 : (2 : F) ≠ 0)
    (hscalar : negativeComplement (F := F) r ∈
      Minus.Omega F (Minus.Space F r) (Minus.quadraticForm F (r + 1)) ↔
      Odd (r + 1) ∧ Nat.card F % 4 = 3) :
    Nat.card (projectiveBlockHom r hq).ker =
      if Odd (r + 1) ∧ Nat.card F % 4 = 3 then 2 else 1 := by
  classical
  split_ifs with hc
  · exact projectiveBlockHom_kernel_card_of_mem r hq h2 (hscalar.mpr hc)
  · have hi := (projectiveBlockHom_injective_iff_of_scalarCriterion r hq h2 hscalar).mpr hc
    rw [(projectiveBlockHom r hq).ker_eq_bot_iff.mpr hi]
    exact Subgroup.card_bot

/-- Convert a genuine commutator/spinor calculation into the parity and field-cardinality criterion. -/
theorem negativeComplement_mem_iff_of_squareCriterion [Finite F]
    (r : ℕ) (h2 : (2 : F) ≠ 0)
    (hspinor : negativeComplement (F := F) r ∈
      Minus.Omega F (Minus.Space F r) (Minus.quadraticForm F (r + 1)) ↔
      IsSquare ((-1 : F) ^ (r + 1) * (1 + 4 * Minus.parameter F))) :
    negativeComplement (F := F) r ∈
      Minus.Omega F (Minus.Space F r) (Minus.quadraticForm F (r + 1)) ↔
      Odd (r + 1) ∧ Nat.card F % 4 = 3 :=
  hspinor.trans (minus_discriminant_isSquare_iff h2 (r + 1))


end ClassicalOrthogonal.Fundamental.MinusCentralizer
