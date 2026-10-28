module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.PointModels.LinearThree
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.PointModels.SymplecticFour

/-!
# Marked point residuals, generation and the source intersection bound

Both native model calculations are now proved: two distinct field-line
residuals generate full SL₃ or Sp₄ over the nonbinary field. Their literal
images generate the chosen quotient L/O₂(L), and perfectness lifts this to
L itself. Together with the previously proved point-residual identification,
this supplies 11.5.3(1--2) from the named preceding source hypotheses.
No point-generation, residual-identification or line-pair callback remains.

Source: Aschbacher--Smith, 11.5.3(1--2), printed p.779.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.PointModels
open Subgroup
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {E : Geometry D} (F₀ : MarkedFlag E)

theorem marked_linePairGeneration :
    LinePairGeneration E.input.field F₀.action.coordinates.modelAction := by
  cases ha : F₀.action with
  | sl3 m => exact LinearThree.linePairGeneration _ E.input.nonbinary
  | sp4 m => exact SymplecticFour.linePairGeneration _ E.input.nonbinary

include F₀ in
/-- Generation in the literal L/O₂(L), using both proved model calculations. -/
theorem quotientPointGeneration
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (hz : E.z ∈ E.V₁) (hz1 : E.z ≠ 1)
    (htrans : ∀ u ∈ V, u ≠ 1 → ∀ v ∈ V, v ≠ 1 →
      ∃ l ∈ L, (MulAut.conj l) u = v) :
    QuotientPointGeneration L V E.V₁ :=
  quotientPointGeneration_of_linePair F₀ hfixed hz hz1 htrans
    (marked_linePairGeneration F₀)

include F₀ in
/-- Perfectness lifts the proved quotient generation to the original L. -/
theorem pointGeneration
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (hz : E.z ∈ E.V₁) (hz1 : E.z ≠ 1)
    (htrans : ∀ u ∈ V, u ≠ 1 → ∀ v ∈ V, v ≠ 1 →
      ∃ l ∈ L, (MulAut.conj l) u = v) :
    PointGeneration L V E.V₁ :=
  pointGeneration_of_quotient D E.input E.V₁
    (quotientPointGeneration F₀ hfixed hz hz1 htrans)

/-- Source 11.5.3(1--2), with no residual or point-generation callback. -/
theorem intersection_and_rank
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (hz : E.z ∈ E.V₁) (hz1 : E.z ≠ 1)
    (htrans : ∀ u ∈ V, u ≠ 1 → ∀ v ∈ V, v ≠ 1 →
      ∃ l ∈ L, (MulAut.conj l) u = v)
    (hK : E.Kz = E.K)
    (hTI : ∀ g ∈ normalizer (L : Set G),
      V ⊓ V.map (MulAut.conj g : G →* G) = ⊥ ∨ V.map (MulAut.conj g : G →* G) = V)
    (hKL : E.K = E.L₁) :
    (∀ g : G, g ∉ normalizer (V : Set G) →
      ∃ l ∈ L, V ⊓ V.map (MulAut.conj g : G →* G) ≤
        E.V₁.map (MulAut.conj l : G →* G)) ∧
      (((F₀.action.dimension - 1) * E.input.field.degree : ℕ) : ℕ∞) ≤ ChapterE.globalR V :=
  intersection_and_rank_of_linePair F₀ hfixed hz hz1 htrans hK
    (marked_linePairGeneration F₀) hTI hKL

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.PointModels
