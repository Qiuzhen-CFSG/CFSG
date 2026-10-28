module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Chief.Action

/-!
# The preliminary centralizer argument in 11.5.8

The uniqueness input controls N_G(V), so C_KT(U) lies in M1. The actual
solvable residual L1 of L intersect G1 is normalized by M1. Consequently
C_K(U) normalizes L1. These assertions use relative normality throughout.

The further bound C_K(U) <= O_{2,Z}(K) requires the surviving exceptional
component models and is not asserted here.
Source: Aschbacher--Smith, last paragraph of 11.5.8, printed p.784.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Chief
open Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Closure.Geometry D)

/-- The full seed normalizer is controlled by the original uniqueness input. -/
theorem seed_normalizer_le_M (h : LocalInputs E) : normalizer (V : Set G) ≤ E.M := by
  let := D.elementary
  exact normalizer_le_of_unique_maximalTwoLocal h.unique
    (IsElementaryAbelian.isPGroup 2 V) D.ne_bot
    (sup_le D.normalizes E.input.sylow_normalizes)

/-- The first containment used in the last paragraph of 11.5.8. -/
theorem closure_centralizer_le_M₁ (h : LocalInputs E) :
    KT E ⊓ centralizer (localClosure E : Set G) ≤ E.M₁ := by
  apply le_inf
  · exact (inf_le_right.trans (centralizer_le (le_conjugateSpanBy V (KT E)))).trans
      ((centralizer_le_normalizer (V : Set G)).trans (seed_normalizer_le_M E h))
  · exact inf_le_left.trans (KT_le_G₁ E h)

/-- Relative normality of the literal solvable residual L₁ in M₁. -/
theorem M₁_normalizes_L₁ : E.M₁ ≤ normalizer (E.L₁ : Set G) := by
  have hn : E.M₁ ≤ normalizer (L ⊓ E.G₁ : Set G) :=
    (le_inf (show E.M₁ ≤ normalizer (L : Set G) from inf_le_left)
      (inf_le_right.trans E.G₁.le_normalizer)).trans inf_normalizer_le_normalizer_inf
  exact hn.trans (normalizer_le_normalizer_characteristic_image (L ⊓ E.G₁)
    (solvableResidual (L ⊓ E.G₁ : Subgroup G)))

theorem L₁_relative_normal : (E.L₁.subgroupOf E.M₁).Normal := by
  have hle : E.L₁ ≤ E.M₁ := le_inf (E.L₁_le.trans L.le_normalizer)
    ((residualIn_le _).trans inf_le_right)
  exact (normal_subgroupOf_iff_le_normalizer hle).mpr (M₁_normalizes_L₁ E)

/-- The actual kernel in K normalizes L₁; bounding it by O₂,Z(K) remains
the exceptional-component structure argument. -/
theorem K_centralizer_normalizes_L₁ (h : LocalInputs E) :
    E.K ⊓ centralizer (localClosure E : Set G) ≤ normalizer (E.L₁ : Set G) :=
  ((inf_le_inf (show E.K ≤ KT E from le_sup_left) le_rfl).trans
    (closure_centralizer_le_M₁ E h)).trans (M₁_normalizes_L₁ E)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Chief
