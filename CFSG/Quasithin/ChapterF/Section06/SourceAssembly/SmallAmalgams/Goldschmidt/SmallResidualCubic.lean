module
public import Theory.GroupTheory.GeneralizedFitting.OddNormalObstruction
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Excluding Goldschmidt's cubic residual under characteristic two

A cubic two-residual is a normal subgroup of order three. Such a subgroup
lies in the generalized Fitting subgroup and cannot lie in the two-core.
Thus the original characteristic-two hypotheses exclude the cubic residual
at both endpoints before the universal normal-base reduction is used.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), the cubic
case (4.1), printed p.392, and the standing exclusions in Section 6,
printed p.395; Aschbacher--Smith F.1.12 and F.6.5 supply F* = O₂.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt

variable {H : Type*} [Group H] [Finite H]

/-- The two-residual of a characteristic-two finite group is not cubic. -/
theorem residual_not_cubic_of_characteristicTwo
    (hfit : generalizedFitting H = pCore 2 H) :
    ¬ Nonempty ((pResidual 2 H) ≃* Multiplicative (ZMod 3)) := by
  rintro ⟨e⟩
  apply not_characteristicTwo_of_normal_three (pResidual 2 H) _ hfit
  exact (Nat.card_congr e.toEquiv).trans (by simp)

/-- Both original local hypotheses exclude the cubic residual, with the
endpoint order retained for the universal-amalgam transport. -/
theorem original_residual_not_cubic {A B : Subgroup H}
    (hA : generalizedFitting A = pCore 2 A)
    (hB : generalizedFitting B = pCore 2 B) (i : Bool) :
    ¬ Nonempty ((pResidual 2 (if i then B else A : Subgroup H)) ≃* Multiplicative (ZMod 3)) := by
  cases i
  · exact residual_not_cubic_of_characteristicTwo hA
  · exact residual_not_cubic_of_characteristicTwo hB

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
