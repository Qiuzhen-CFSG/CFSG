module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.EvenLieOvergroups.SplitExceptional.ParabolicReduction
public import Theory.AtlasPort.LinearGroups.G2.ProperSylowOvergroups
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Split exceptional proper Sylow-overgroup bounds

For the actual split-octonion G₂ carrier, exhaustive Bruhat-cell descent places
each proper Sylow overgroup in a conjugate of one of the two root parabolics.
Their self-centralizing two-cores pass to the overgroup, giving F*(X) = O₂(X).
An actual model equivalence then discharges the literal B.1.13 reduction.

This proves the G₂ branch, including every binary field of order greater than
two. The stronger intrinsic bound also holds for the full G₂(2), which is not
the separately treated simple endpoint G₂(2)′. The F₄, E₆, E₇ and E₈ branches
still require exhaustive placement and radical centralizer calculations in
their actual root-generated central quotients. `ParabolicReduction` exports
the explicit independent inputs and their conditional applications to all four
carriers and the literal source component reduction.

Sources: Aschbacher–Smith B.1.13, printed p.74 (PDF p.85); GLS III,
Theorems 2.3.5 and 2.6.5–2.6.7 (`refs/KGroup/GLS3/chapter2.tex`).
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups

/-- The complete proper-overgroup bound on an actual binary split G₂ model. -/
theorem properSylowFittingBound_g2 (F : Type*) [Field F] [Finite F] [CharP F 2]
    {A : Type*} [Group A] [Finite A] (e : A ≃* Atlas.G2.Model F) :
    ProperSylowFittingBound A := by
  apply properSylowFittingBound_of_equiv e
  intro S X hSX hX
  rw [Atlas.G2.ProperSylowOvergroups.generalizedFitting_eq_twoCore S X hSX hX]
  exact le_sup_left

/-- Binary cardinality supplies the characteristic instance on the literal carrier. -/
theorem properSylowFittingBound_g2_of_card (F : Type*) [Field F] [Finite F]
    (n : ℕ) (hcard : Nat.card F = 2 ^ n)
    {A : Type*} [Group A] [Finite A] (e : A ≃* Atlas.G2.Model F) :
    ProperSylowFittingBound A := by
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  exact properSylowFittingBound_g2 F e

variable {G : Type*} [Group G] [Finite G]

/-- The G₂ calculation discharges the source proper-overgroup premise on
L ∩ (K ∨ T), through the specified model equivalence. -/
theorem eq_component_of_g2 (K L : Subgroup G) (T : Sylow 2 G)
    (hL : IsComponent G L) (hLK : ⁅L, K⁆ = L)
    (hkind : IsQuasisimple K ∨ Nat.card K = 3)
    (hK : (K.subgroupOf (K ⊔ (T : Subgroup G))).IsSubnormal) (hKL : K ≤ L)
    (F : Type*) [Field F] [Finite F] [CharP F 2]
    (e : L ≃* Atlas.G2.Model F) : K = L :=
  eq_component_of_proper_sylow_fitting_bound K L T hL hLK hkind hK hKL
    (properSylowFittingBound_g2 F e)

/-- The same literal component application with the source field-order parameter. -/
theorem eq_component_of_g2_of_card (K L : Subgroup G) (T : Sylow 2 G)
    (hL : IsComponent G L) (hLK : ⁅L, K⁆ = L)
    (hkind : IsQuasisimple K ∨ Nat.card K = 3)
    (hK : (K.subgroupOf (K ⊔ (T : Subgroup G))).IsSubnormal) (hKL : K ≤ L)
    (F : Type*) [Field F] [Finite F] (n : ℕ) (hcard : Nat.card F = 2 ^ n)
    (e : L ≃* Atlas.G2.Model F) : K = L :=
  eq_component_of_proper_sylow_fitting_bound K L T hL hLK hkind hK hKL
    (properSylowFittingBound_g2_of_card F n hcard e)

end CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups
