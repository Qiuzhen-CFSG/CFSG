module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.OriginalSupplement
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Consumers.Parameters

/-!
# The four natural weak-closure parameter clauses

The full central cover supplies normalizer representatives for the original
hyperplane in the exceptional Sp₄(4) case. Together with the earlier hyperplane
and E.6.3 arguments this proves the global lower bound in every marking.
The existing seed-automizer calculation supplies the fixed codimensions and
root geometry; the original residual, global-parameter and weak-closure
consumers then give 11.2.2(1--4), retaining the nonsplit kernel.

Only the earlier uniqueness over L, third-space centralizer and fixed-line
conclusions remain explicit. They retain the relative-component, normalizer
and flag producers qt-d-1222-natural-relative-components,
qt-d-1222-natural-normalizer-source and qt-d-1222-natural-flag-cartan.
The final owner qt-d-1222-natural-weak-closure-source discharges these inputs.
No hyperplane, supplement, fixed-codimension or root-geometry premise remains.

Source: Aschbacher--Smith, 11.2.2(1--4), printed pp.767--768.
-/

public noncomputable section
open Subgroup
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterE CFSG.Quasithin.ChapterE.Section06
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- The global lower bound for the actual seed, including its nonsplit central part. -/
theorem natural_globalR_lower_bound (c : Coordinates D S.field)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      L ≤ N → N = normalizer (L : Set G)) :
    (naturalParameter D S c : ℕ∞) ≤ globalR V := by
  have hE := hypothesisE61_of_ti D S (Preliminary.seed_ti D S)
  exact lower_bound_of_hyperplanes D S (natural_fixedCodimensions D S c) hE
    (fun _U hUV hU => Hyperplanes.OriginalSupplement.hyperplane_centralizer_le
      D S c hE hunique hUV hU)

/-- Source 11.2.2(1--4) on the original action, quotient and flag.
Only the named earlier-source conclusions are explicit; final source assembly
belongs to qt-d-1222-natural-weak-closure-source. -/
theorem source_parameters {c : Coordinates D S.field}
    (f : InvariantFlag c)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      L ≤ N → N = normalizer (L : Set G))
    (hthree : centralizer (f.Vi 2 : Set G) ≤ normalizer (L : Set G))
    (hline : f.Vi 0 ≤ V ⊓ centralizer (sourceTL T L : Set G)) :
    @localM G _ V D.elementary = naturalParameter D S c ∧
    (∀ U : Subgroup G, U ≤ V → subgroupCorank V U < 2 * naturalParameter D S c →
      oddCentralizerCondition (normalizer (L : Set G)) V U →
      centralizer (U : Set G) ≤ normalizer (L : Set G) ∧
        (primeToResidual 2 ↥(centralizer (U : Set G))).map
          (centralizer (U : Set G)).subtype ≤
            normalizer (L : Set G) ⊓ centralizer (V : Set G)) ∧
    (((naturalParameter D S c : ℕ∞) < globalR V ∨
      (Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) ∧
        globalR V = naturalParameter D S c ∧
        ¬ centralizer (f.Vi 1 : Set G) ≤ normalizer (L : Set G))) ∧
      @globalS G _ V D.elementary = naturalParameter D S c) ∧
    (∀ j : ℕ, j < naturalParameter D S c - 1 →
      indexedWeakClosure V (T : Subgroup G) j ≤ sourceTL T L ∧
        f.Vi 0 ≤ V ⊓ centralizer (indexedWeakClosure V (T : Subgroup G) j : Set G)) := by
  exact source_parameters_of_seed_and_lower_bound D S f
    (natural_globalR_lower_bound D S c hunique) hthree hline

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters
