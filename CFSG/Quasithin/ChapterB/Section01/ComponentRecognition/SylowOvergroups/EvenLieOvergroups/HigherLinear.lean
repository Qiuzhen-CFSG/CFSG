module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.EvenLieOvergroups.Transport
public import Theory.SpecificGroups.HigherLinear.ParabolicGeometry
public import Theory.SpecificGroups.HigherLinear.BinaryFive

/-!
# Higher-dimensional projective linear Sylow overgroups

For PSL₅(2), actual flag exhaustion and the binary subspace-radical
centralizer calculation prove the proper-overgroup bound without additional
premises. The final application uses the literal local intersection and
component-equality theorem from `SylowOvergroups.Reduction`.

For arbitrary dimension and binary field extensions, this module separates
the remaining exhaustive subspace placement and projective radical
centralizer calculations. The conditional assembly proves the intrinsic
Fitting calculation from those two geometric inputs; it does not assert
that they are already established. The unipotent radical's two-group
property and relative normality are proved in the shared geometry module.

All transport uses an actual equivalence with SLₙ(F)/Z(SLₙ(F)). Nothing
identifies an arbitrary covering component with SLₙ(F).
Source: Aschbacher–Smith B.1.13, printed p.74 (PDF p.85), and GLS III, 2.6.5.
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups

/-- The intrinsic calculation inside an actual projective subspace parabolic.
The remaining matrix centralizer calculation is explicit. -/
theorem generalizedFitting_eq_twoCore_of_linear_parabolic
    {n : ℕ} {F : Type*} [Field F] [Finite F] [CharP F 2]
    (S : Sylow 2 PSL(n,F)) (X : Subgroup PSL(n,F))
    (W : Submodule F (Fin n → F))
    (hSX : (S : Subgroup PSL(n,F)) ≤ X)
    (hXP : X ≤ Matrix.HigherLinear.parabolic W)
    (hc : centralizer (Matrix.HigherLinear.radical W : Set PSL(n,F)) ≤
      Matrix.HigherLinear.radical W) :
    generalizedFitting X = pCore 2 X :=
  generalizedFitting_eq_pCore_of_sylow_le_normalizer S X
    (Matrix.HigherLinear.parabolic W) (Matrix.HigherLinear.radical W)
    hSX hXP (Matrix.HigherLinear.radical_le_parabolic W)
    (Matrix.HigherLinear.parabolic_le_normalizer W)
    (Matrix.HigherLinear.radical_isPGroup W) hc

/-- Conditional assembly of the two independent general-field geometry inputs.
Neither placement nor the radical centralizer estimate is assumed to follow
from the family name. -/
theorem properSylowFittingBound_psl_of_parabolic_geometry
    {n : ℕ} {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hplacement : ∀ (S : Sylow 2 PSL(n,F)) (X : Subgroup PSL(n,F)),
      (S : Subgroup PSL(n,F)) ≤ X → X ≠ ⊤ →
      ∃ W : Submodule F (Fin n → F), W ≠ ⊥ ∧ W ≠ ⊤ ∧
        X ≤ Matrix.HigherLinear.parabolic W)
    (hcentralizer : ∀ W : Submodule F (Fin n → F), W ≠ ⊥ → W ≠ ⊤ →
      centralizer (Matrix.HigherLinear.radical W : Set PSL(n,F)) ≤
        Matrix.HigherLinear.radical W) :
    ProperSylowFittingBound PSL(n,F) := by
  intro S X hSX hX
  obtain ⟨W, hW, hWt, hXP⟩ := hplacement S X hSX hX
  rw [generalizedFitting_eq_twoCore_of_linear_parabolic S X W hSX hXP
    (hcentralizer W hW hWt)]
  exact le_sup_left

/-- The completed binary five-dimensional instance uses actual flag geometry. -/
theorem properSylowFittingBound_psl5_two :
    ProperSylowFittingBound PSL(5, ZMod 2) := by
  apply properSylowFittingBound_of_equiv
    (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 5))
  intro S X hSX hX
  rw [BinaryLinear.FiveFlagGeometry.generalizedFitting_eq_twoCore_of_sylow_le S X hSX hX]
  exact le_sup_left

variable {G : Type*} [Group G] [Finite G]

/-- Literal B.1.13 component equality in the completed PSL₅(2) case. -/
theorem eq_component_of_psl5_two (K L : Subgroup G) (T : Sylow 2 G)
    (hL : IsComponent G L) (hLK : ⁅L, K⁆ = L)
    (hkind : IsQuasisimple K ∨ Nat.card K = 3)
    (hK : (K.subgroupOf (K ⊔ (T : Subgroup G))).IsSubnormal) (hKL : K ≤ L)
    (e : L ≃* PSL(5, ZMod 2)) : K = L :=
  eq_component_of_proper_sylow_fitting_bound K L T hL hLK hkind hK hKL
    (properSylowFittingBound_of_equiv e properSylowFittingBound_psl5_two)

/-- Source application for the general linear branch, retaining precisely its
two outstanding geometric premises and the actual model equivalence. -/
theorem eq_component_of_higherLinear_parabolic_geometry
    (K L : Subgroup G) (T : Sylow 2 G)
    (hL : IsComponent G L) (hLK : ⁅L, K⁆ = L)
    (hkind : IsQuasisimple K ∨ Nat.card K = 3)
    (hK : (K.subgroupOf (K ⊔ (T : Subgroup G))).IsSubnormal) (hKL : K ≤ L)
    {n : ℕ} {F : Type*} [Field F] [Finite F] [CharP F 2] (e : L ≃* PSL(n,F))
    (hplacement : ∀ (S : Sylow 2 PSL(n,F)) (X : Subgroup PSL(n,F)),
      (S : Subgroup PSL(n,F)) ≤ X → X ≠ ⊤ →
      ∃ W : Submodule F (Fin n → F), W ≠ ⊥ ∧ W ≠ ⊤ ∧
        X ≤ Matrix.HigherLinear.parabolic W)
    (hcentralizer : ∀ W : Submodule F (Fin n → F), W ≠ ⊥ → W ≠ ⊤ →
      centralizer (Matrix.HigherLinear.radical W : Set PSL(n,F)) ≤
        Matrix.HigherLinear.radical W) : K = L :=
  eq_component_of_proper_sylow_fitting_bound K L T hL hLK hkind hK hKL
    (properSylowFittingBound_of_equiv e
      (properSylowFittingBound_psl_of_parabolic_geometry hplacement hcentralizer))

end CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups
