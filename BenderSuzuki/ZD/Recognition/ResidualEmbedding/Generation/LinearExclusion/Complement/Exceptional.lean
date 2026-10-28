module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.Setup
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Data.ZMod.Basic

/-!
# The square produced by the exceptional linear quotient

In GLS, Volume 4, Chapter 2, Lemma 15.7, the equality case of the
two-core argument produces a normal subgroup `R₀` of `M` and identifies
`M/R₀` with the actual matrix group `SL₂(7)`. The nontrivial centralizer
element maps to `-I`, and every element of its `R₀`-coset is conjugate to it
in the ambient group. Lifting the matrix `[[0,-1],[1,0]]` therefore makes
that element a square in the ambient group.

The theorem below proves this lifting step. Its quotient identification,
marking, and fusion premises remain to be established from the local
linear setup. In particular it does not yet exclude equality of the
centralizer closure and the two-core. Both `R₀` and its normality are
relative to `M`; the quotient here is `M/R₀`, not `M/M°`.

Source: `refs/KGroup/GLS4/Chapter2.tex`, Lemma 15.7, last two paragraphs.
-/

open scoped MatrixGroups

namespace BenderSuzuki.ZD

private def exceptionalQuarterTurn : SL(2, ZMod 7) :=
  ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two_of]⟩

private theorem exceptionalQuarterTurn_sq : exceptionalQuarterTurn ^ 2 = -1 := by
  apply Subtype.ext
  change (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod 7)) ^ 2 = -1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two]

/-- The marked `SL₂(7)` quotient and fusion of the marked coset produce
an actual square root in the ambient group. The three local premises are
explicit: this is the endpoint of the source argument, not its recognition
or nonsquareness theorem. -/
public theorem linear_exceptional_square_of_sl2Seven_quotient
    {G : Type*} [Group G] {M : Subgroup G}
    (R₀ : Subgroup M) [R₀.Normal] (u : M)
    (e : M ⧸ R₀ ≃* SL(2, ZMod 7))
    (hu : e (QuotientGroup.mk' R₀ u) = -1)
    (hfusion : ∀ v : M, QuotientGroup.mk' R₀ v = QuotientGroup.mk' R₀ u →
      IsConj (v : G) (u : G)) :
    ∃ x : G, x ^ 2 = (u : G) := by
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective R₀ (e.symm exceptionalQuarterTurn)
  have himage : e (QuotientGroup.mk' R₀ x) = exceptionalQuarterTurn := by
    rw [hx, e.apply_symm_apply]
  have hsq : QuotientGroup.mk' R₀ (x ^ 2) = QuotientGroup.mk' R₀ u := by
    apply e.injective
    rw [map_pow, map_pow, himage, exceptionalQuarterTurn_sq, hu]
  obtain ⟨g, hg⟩ := isConj_iff.mp (hfusion (x ^ 2) hsq)
  refine ⟨MulAut.conj g (x : G), ?_⟩
  rw [← map_pow]
  exact hg

end BenderSuzuki.ZD
