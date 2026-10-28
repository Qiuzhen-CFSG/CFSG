module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.RemainingSieve.OddActions.Covers
public import Theory.Mathieu.SchurMultipliers.FiniteCovers

/-!
# Removing the M₁₁ cover in the odd E.6.8 branch

The proved finite perfect central-cover calculation for the concrete M₁₁
discharges the universal kernel bound in `Covers`. Quasisimplicity makes the
component's actual two-core central, so the literal quotient map
L → L/O₂(L) ≃ M₁₁ has trivial kernel. This identifies L itself with M₁₁.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, I.1.3,
printed p.407, 1.1.5(3)(f), p.502, and E.6.8(5), pp.247–248.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components.RemainingSieve.OddActions
open Chapter1.XiEmbedding.InvariantThree.SporadicRemaining
universe u

/-- The proved Mathieu cover calculation supplies the earlier conditional API. -/
theorem m11_centralKernelDivides_one :
    CentralKernelDivides.{u,0} Sporadic.Mathieu.M11 1 := by
  intro E _ _ _ f hs hc
  let c : PerfectCentralCovering.Cover E Sporadic.Mathieu.M11 :=
    { toMonoidHom := f
      surjective := hs
      ker_le_center := hc
      isPerfect := inferInstance }
  have hk := Sporadic.Mathieu.SchurMultipliers.m11_cover_kernel_eq_bot c
  change f.ker = ⊥ at hk
  rw [hk]
  simp

variable {X : Type u} [Group X] [Finite X] [IsQuasisimple X]

/-- No nontrivial two-core survives in a quasisimple cover of M₁₁. -/
theorem m11_core_eq_bot (e : (X ⧸ pCore 2 X) ≃* Sporadic.Mathieu.M11) :
    pCore 2 X = ⊥ :=
  m11_core_eq_bot_of_multiplier m11_centralKernelDivides_one e

/-- The actual quotient model lifts to an isomorphism on the original group. -/
theorem m11_model (e : (X ⧸ pCore 2 X) ≃* Sporadic.Mathieu.M11) :
    Nonempty (X ≃* Sporadic.Mathieu.M11) :=
  m11_model_of_multiplier m11_centralKernelDivides_one e

variable {G : Type u} [Group G] [Finite G] {U L : Subgroup G}

/-- Apply the proved cover elimination to a component relative to C_G(U). -/
theorem component_m11_model
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hmodel : Nonempty ((L ⧸ pCore 2 L) ≃* Sporadic.Mathieu.M11)) :
    Nonempty (L ≃* Sporadic.Mathieu.M11) :=
  component_m11_model_of_multiplier m11_centralKernelDivides_one hL hmodel

end CFSG.Quasithin.ChapterE.Section06.Components.RemainingSieve.OddActions
