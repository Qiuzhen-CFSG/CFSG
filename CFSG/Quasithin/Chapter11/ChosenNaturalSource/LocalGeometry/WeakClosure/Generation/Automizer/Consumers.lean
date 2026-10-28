module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.Automizer.ModelTori
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.Doubling.Source

/-!
# The literal generation consumer of the Cartan normalizer reduction

Apply solvable Sylow control to the actual automizers on V and V_M. Their
Cartan parameters are bounded once the corresponding odd normalizer
exponents are established; no further permutation, solvability, Sylow
placement or arithmetic premise remains. This feeds the existing H-star
assembly with the already proved doubled natural module.

Both outer exponent calculations and the exact odd-kernel normalizer
contract remain explicit. The weak-closure source owner must discharge them
before this conditional application establishes 11.2.1.
Source: Aschbacher--Smith, 11.2.1, printed pp.766--767.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterE CFSG.Quasithin.ChapterE.Section06.FixedPointBounds
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.Automizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- Odd exponent on the normalizer of the actual relative layer Sylow. -/
def LayerNormalizerExponent (U J : Subgroup G) (n : ℕ) : Prop :=
  ∀ (P : Sylow 2 (inducedAutomizer U J)) (a : inducedAutomizer U J),
    a ∈ normalizer ((P : Subgroup (inducedAutomizer U J)) ⊓
      (inducedAutomizer U L).subgroupOf (inducedAutomizer U J) :
        Set (inducedAutomizer U J)) →
    Odd (orderOf a) → a ^ (n * (2 ^ n - 1)) = 1

/-- Both original automizer bounds follow from their odd normalizer exponents. -/
theorem automizer_bounds_of_normalizer_exponents
    (hseed : LayerNormalizerExponent (L := L) V
      (normalizer (L : Set G) ⊓ normalizer (V : Set G)) S.field.degree)
    (hfull : DoubledNatural D S → LayerNormalizerExponent (L := L)
      (Source.conjugateSpan (normalizer (L : Set G)) V)
      (normalizer (L : Set G)) (2 * S.field.degree)) : AutomizerBounds D S := by
  constructor
  · exact actual_nPrime_le_of_normalizer_exponent D S le_rfl
      (le_inf L.le_normalizer D.normalizes) inf_le_right inf_le_left
      (by have := S.nonbinary; omega) hseed
  · intro hd
    exact actual_nPrime_le_of_normalizer_exponent D S (le_componentOrbit V _)
      L.le_normalizer (le_normalizer_componentOrbit V _) le_rfl
      (by have := S.nonbinary; omega) (hfull hd)

/-- The original H-star alternative, with the remaining exponent and odd-kernel inputs explicit. -/
theorem conclusion_of_normalizer_exponents
    (hcontrol : OddKernelNormalizer (T := T) (L := L) (V := V))
    (hseed : LayerNormalizerExponent (L := L) V
      (normalizer (L : Set G) ⊓ normalizer (V : Set G)) S.field.degree)
    (hfull : DoubledNatural D S → LayerNormalizerExponent (L := L)
      (Source.conjugateSpan (normalizer (L : Set G)) V)
      (normalizer (L : Set G)) (2 * S.field.degree))
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    Conclusion D S H :=
  Doubling.conclusion_of_automizer_bounds D S hcontrol
    (automizer_bounds_of_normalizer_exponents D S hseed hfull) hH

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.Automizer
