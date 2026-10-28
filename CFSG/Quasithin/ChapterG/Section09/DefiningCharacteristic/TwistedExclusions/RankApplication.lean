module

public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.TwistedExclusions.ComponentRank
public import Theory.SpecificGroups.Triality.StandardTwoRank.Sylow

/-!
# Applying the triality radical rank calculation to G.9

The source's actual triality-model witness transports the component to the
binary carrier. The proved exact intrinsic rank supplies the bound 5*n,
and inner–coefficient coverage then gives the existing exclusion for n ≥ 3.
Only coverage remains explicit in `not_triality_of_coefficient_coverage`;
its producer is the separate `OuterOddSubgroups.Coverage` development.
The original conditional radical adapter is preserved. Neither adapter
settles n = 1 or n = 2.

Source: Aschbacher–Smith G.9, printed p.356 (`refs/quasithin.pdf`).
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterG.Section09
open Triality.Standard Triality.Standard.Parabolics
namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.TwistedExclusions

universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {K : CFSG.Quasithin.GroupClass.{u}} {ρ : Representation (ZMod 2) G V}
  {A L : Subgroup G} {m : ℕ}

/-- The literal G.9 application with explicit radical estimates and Sylow placement.
The following adapter discharges these two inputs, leaving coefficient coverage. -/
theorem not_triality_of_elementary_radical_bounds
    (h : ComponentHypothesis K ρ A L L m) {n : ℕ} (hn : 3 ≤ n)
    (model : IsTrialityGroupAt (2 ^ n) L)
    (hcover : ∀ E : Subgroup (unipotent (binaryParameters n (by omega))),
      IsElementaryAbelian 2 E →
      E.map (unipotent (binaryParameters n (by omega))).subtype ≤
        radical (binaryParameters n (by omega)) .arms ∨
      E.map (unipotent (binaryParameters n (by omega))).subtype ≤
        radical (binaryParameters n (by omega)) .central)
    (hbound : ∀ a (E : Subgroup (radical (binaryParameters n (by omega)) a)),
      IsElementaryAbelian 2 E → Nat.card E ≤ (binaryParameters n (by omega)).q ^ 5)
    (hcoverage : IsSimpleGroup (BinaryCarrier n (by omega)) →
      Group.IsPerfect (BinaryCarrier n (by omega)) →
      ∀ a : MulAut (BinaryCarrier n (by omega)),
        ∃ g : BinaryCarrier n (by omega),
        ∃ f : OuterOdd.CoefficientAut (binaryParameters n (by omega)),
          a = MulAut.conj g * OuterOdd.coefficientAction (binaryParameters n (by omega)) f) :
    False :=
  not_triality_of_coarse_model_estimates h hn model
    (TwoRank.twoRank_le_of_radical_bounds n (by omega) hcover hbound) hcoverage

/-- The actual G.9 triality witness is excluded for n ≥ 3 using the proved
intrinsic rank. The component supplies simplicity and perfectness; only
inner–coefficient coverage remains to be discharged by its separate owner. -/
theorem not_triality_of_coefficient_coverage
    (h : ComponentHypothesis K ρ A L L m) {n : ℕ} (hn : 3 ≤ n)
    (model : IsTrialityGroupAt (2 ^ n) L)
    (hcoverage : IsSimpleGroup (BinaryCarrier n (by omega)) →
      Group.IsPerfect (BinaryCarrier n (by omega)) →
      ∀ a : MulAut (BinaryCarrier n (by omega)),
        ∃ g : BinaryCarrier n (by omega),
        ∃ f : OuterOdd.CoefficientAut (binaryParameters n (by omega)),
          a = MulAut.conj g * OuterOdd.coefficientAction (binaryParameters n (by omega)) f) :
    False :=
  not_triality_of_coarse_model_estimates h hn model
    (TwoRank.twoRank_le_five_mul n (by omega)) hcoverage

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.TwistedExclusions
