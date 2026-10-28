module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Residual.SeedAutomizer
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters

/-!
# The parameter consumer without unrestricted cubic containment

The original seed automizer supplies the fixed-codimension and root geometry.
Together with preliminary TI this gives 11.2.2(1--4) from the independent
lower bound, third-space centralizer and fixed-line inputs. In the SL₃ row
the vanishing central kernel supplies hyperplane control and the lower bound.
The flag and component producers retain the third-space and fixed-line
inputs; qt-d-1222-natural-weak-closure-source retains the lower bound;
qt-d-1222-natural-local-geometry retains their final discharge.
Source: Aschbacher--Smith, 11.2.2, printed pp.767--768.
-/

public noncomputable section
open Subgroup
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterE CFSG.Quasithin.ChapterE.Section06
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- All four parameter clauses using the actual seed automizer and lower bound. -/
theorem source_parameters_of_seed_and_lower_bound {c : Coordinates D S.field}
    (f : InvariantFlag c)
    (hr : (naturalParameter D S c : ℕ∞) ≤ globalR V)
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
  exact source_parameters_of_model_and_lower_bound D S f
    (natural_fixedCodimensions D S c) (natural_rootGeometry D S f)
    hr (Preliminary.seed_ti D S) hthree hline

/-- All four parameter clauses using the actual seed automizer and hyperplanes. -/
theorem source_parameters_of_seed_and_hyperplanes {c : Coordinates D S.field}
    (f : InvariantFlag c)
    (hhyper : ∀ U : Subgroup G, U ≤ V → subgroupCorank V U = 1 →
      centralizer (U : Set G) ≤ normalizer (L : Set G))
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
  exact source_parameters_of_model_and_hyperplanes D S f
    (natural_fixedCodimensions D S c) (natural_rootGeometry D S f)
    hhyper (Preliminary.seed_ti D S) hthree hline

/-- The actual SL₃ application, with the lower bound and hyperplanes discharged.
Only the earlier third-space and fixed-line conclusions remain explicit. -/
theorem source_parameters_sl3_of_seed
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (Coordinates.sl3 m))
    (hthree : centralizer (f.Vi 2 : Set G) ≤ normalizer (L : Set G))
    (hline : f.Vi 0 ≤ V ⊓ centralizer (sourceTL T L : Set G)) :
    @localM G _ V D.elementary = naturalParameter D S (Coordinates.sl3 m) ∧
    (∀ U : Subgroup G, U ≤ V → subgroupCorank V U < 2 * naturalParameter D S (Coordinates.sl3 m) →
      oddCentralizerCondition (normalizer (L : Set G)) V U →
      centralizer (U : Set G) ≤ normalizer (L : Set G) ∧
        (primeToResidual 2 ↥(centralizer (U : Set G))).map
          (centralizer (U : Set G)).subtype ≤
            normalizer (L : Set G) ⊓ centralizer (V : Set G)) ∧
    (((naturalParameter D S (Coordinates.sl3 m) : ℕ∞) < globalR V ∨
      (Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) ∧
        globalR V = naturalParameter D S (Coordinates.sl3 m) ∧
        ¬ centralizer (f.Vi 1 : Set G) ≤ normalizer (L : Set G))) ∧
      @globalS G _ V D.elementary = naturalParameter D S (Coordinates.sl3 m)) ∧
    (∀ j : ℕ, j < naturalParameter D S (Coordinates.sl3 m) - 1 →
      indexedWeakClosure V (T : Subgroup G) j ≤ sourceTL T L ∧
        f.Vi 0 ≤ V ⊓ centralizer (indexedWeakClosure V (T : Subgroup G) j : Set G)) := by
  exact source_parameters_of_seed_and_hyperplanes D S f
    (fun _U hUV hU => Hyperplanes.centralizer_le_of_central_kernel_eq_bot D S
      (Coordinates.sl3 m) (hypothesisE61_of_ti D S (Preliminary.seed_ti D S))
      (Preliminary.sl3_centralizer_eq_bot D S m) hUV hU) hthree hline

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters
