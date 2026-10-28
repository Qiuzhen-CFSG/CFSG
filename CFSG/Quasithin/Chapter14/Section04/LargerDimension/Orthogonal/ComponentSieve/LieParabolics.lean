module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.ComponentSieve.LieParabolics.AffineAction
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.ComponentSieve.LieParabolics.LinearPlacement
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.ComponentSieve.LieParabolics.NonlinearCores
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.ComponentSieve.Module

/-!
# The A.3.14 Lie-parabolic obstruction

For each of the five actual ambient models in A.3.14(1), a maximal
parabolic residual with two-core of order sixteen has the natural SL₂(4)
conjugation action. The nonlinear models are excluded by their intrinsic
core orders. In the two linear-three models, parabolic placement identifies
the residual with the special affine plane, whose translation and linear
coordinates identify both the intrinsic core and its literal quotient map.

Transport through the source's embedded residual gives the action on the
original subgroup B. The binary A₅ action on that same core is incompatible
with this natural action, discharging the Lie-parabolic branch of the
terminal sieve in Lemma 14.4.9. Construction of B and the other thirteen
A.3.14 alternatives remain with the enclosing component sieve.

Source: Aschbacher–Smith, A.3.14(1), printed pp.49–50, and the terminal
paragraph of Lemma 14.4.9, printed p.1010.
-/

public section
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.ComponentSieve.LieParabolics
open Chapter1.Section02 Chapter1.Section02.LocalModels

/-- Across all five actual Lie models, a maximal parabolic residual with
two-core of order sixteen is a special affine plane over a field of order four.
The core-order exclusions discharge all three nonlinear alternatives. -/
theorem lieFamily_residual_affine {L : Type*} [Group L] [Finite L]
    (hL : LieFamily L) (P : Subgroup L)
    (hP : LieParabolicTwo P) (hmax : IsCoatom P)
    (hcard : Nat.card (pCore 2 (embeddedResidual P)) = 16) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
      Nonempty (embeddedResidual P ≃* Matrix.SL2.Affine F) := by
  rcases hL with hlinear | hnonlinear
  · exact linearFamily_residual_affine hlinear P hP hmax
  · exact (nonlinear_core_order_exclusion hnonlinear P hP hmax hcard).elim

/-- The order-sixteen core forces the natural action in the actual
parabolic residual. The action includes the quotient by the intrinsic core
and the conjugation identity for every element of the residual. -/
theorem lieFamily_residual_natural {L : Type*} [Group L] [Finite L]
    (hL : LieFamily L) (P : Subgroup L)
    (hP : LieParabolicTwo P) (hmax : IsCoatom P)
    (hcard : Nat.card (pCore 2 (embeddedResidual P)) = 16) :
    NaturalSL2Action (embeddedResidual P) (pCore 2 (embeddedResidual P)) 4 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := lieFamily_residual_affine hL P hP hmax hcard
  exact naturalSL2Action_of_affineEquiv F hF e

/-- Apply the five-family result to A.3.14(1)'s original embedded subgroup.
The source A₅ quotient is transported along the actual residual inclusion;
affine coordinates then give the natural action on B's intrinsic two-core. -/
theorem parabolicResidual_natural {G : Type*} [Group G] {B K : Subgroup G}
    [Finite K] (hK : LieFamily K) (h : IsParabolicResidual B K true)
    (hcard : Nat.card (pCore 2 B) = 16)
    (hquot : IsAlternating (B ⧸ pCore 2 B) 5) :
    NaturalSL2Action B (pCore 2 B) 4 := by
  obtain ⟨P, hP, hmax, hc, _, e, _⟩ := exists_parabolic_core_data h hcard hquot
  obtain ⟨F, _, _, hF, ⟨a⟩⟩ := lieFamily_residual_affine hK P hP hmax hc
  exact naturalSL2Action_of_affineEquiv F hF (e.symm.trans a)

/-- The actual binary A₅ action in Lemma 14.4.9 excludes A.3.14(1).
Its coordinates supply both the order-sixteen core and the source A₅ quotient,
so no separate core-order, quotient or natural-action premise is required. -/
theorem binary_core_not_parabolicResidual {G : Type*} [Group G]
    {B K : Subgroup G} [Finite K] (hK : LieFamily K)
    (hB : BinaryPermutation.FiveConjugation B (pCore 2 B)) :
    ¬ IsParabolicResidual B K true := by
  intro h
  exact binary_core_not_natural_block hB
    (parabolicResidual_natural hK h hB.card ⟨hB.actor⟩)

/-- The actual affine conjugation identity excludes the binary five-point
action on the same intrinsic two-core. -/
theorem binary_core_not_affine {B : Type*} [Group B]
    (F : Type) [Field F] [Finite F] (hF : Nat.card F = 4)
    (hB : BinaryPermutation.FiveConjugation B (pCore 2 B)) :
    ¬ Nonempty (B ≃* Matrix.SL2.Affine F) := by
  rintro ⟨e⟩
  exact binary_core_not_natural_block hB (naturalSL2Action_of_affineEquiv F hF e)

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.ComponentSieve.LieParabolics
