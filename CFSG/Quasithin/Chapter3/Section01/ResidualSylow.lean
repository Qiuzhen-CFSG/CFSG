module

public import CFSG.Quasithin.Chapter3.Section01.Configuration
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents

/-!
# The residual-Sylow specialization of the common-normal theorem

The genuine source 3.1.1 implication, supplied by the C.5.8 proof, applies
to the original two-core in Hypothesis 3.1.5. All local membership,
normality and Sylow-containment premises are proved here; only the
source residual-Sylow premise is retained. Uniqueness then excludes it.

The earlier implication is universal with the exact relative-normality
conclusion. It is not an ambient-normality certificate. Its producer is
the C.5.8/3.1.1 source proof, also consumed as CommonNormalInput in E.6.
Source: Aschbacher–Smith, Theorem 3.1.1 and the observation after
Hypothesis 3.1.5, combined manuscript of 1 March 2004, pp.571–573.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter3
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {M M₀ H V : Subgroup G}

omit [Finite G] in
/-- The genuine earlier-source 3.1.1 implication specializes to the original core. -/
theorem QrcHypotheses.common_normal_of_residual_sylow
    (h : QrcHypotheses T M M₀ H V)
    (h311 : ∀ A H R : Subgroup G,
      A ∈ Chapter1.HOver G (T : Set G) → H ∈ Chapter1.HOver G (T : Set G) →
      Order.HasUniqueMaximalOver (T : Subgroup G) H →
      R ≠ ⊥ → R ≤ T →
      Chapter1.IsSylowIn 2 R ((pResidual 2 H).map H.subtype ⊔ R) →
      A ≤ normalizer (R : Set G) → HasCommonNormal A H R)
    (hne : M₀.pCoreIn 2 ≠ ⊥)
    (hs : Chapter1.IsSylowIn 2 (M₀.pCoreIn 2)
      ((pResidual 2 H).map H.subtype ⊔ M₀.pCoreIn 2)) :
    HasCommonNormal M₀ H (M₀.pCoreIn 2) := by
  have hRT : M₀.pCoreIn 2 ≤ (T : Subgroup G) := by
    rw [h.core_eq_centralizer]
    exact inf_le_left
  have hn : M₀ ≤ normalizer (M₀.pCoreIn 2 : Set G) := by
    simpa only [pCoreIn, normalizer_eq_top, ← MonoidHom.range_eq_map,
      range_subtype] using (pCore 2 M₀).le_normalizer_map M₀.subtype
  exact h311 M₀ H (M₀.pCoreIn 2) ⟨hne, h.sylow_le⟩ h.right_mem.1.1
    (HStar.hasUniqueMaximalOver T (h.sylow_le.trans h.left_le) h.right_mem)
    hne hRT hs hn

/-- Uniqueness rules out the residual Sylow configuration once source 3.1.1 is proved. -/
theorem QrcHypotheses.not_residual_sylow
    (h : QrcHypotheses T M M₀ H V)
    (h311 : ∀ A H R : Subgroup G,
      A ∈ Chapter1.HOver G (T : Set G) → H ∈ Chapter1.HOver G (T : Set G) →
      Order.HasUniqueMaximalOver (T : Subgroup G) H →
      R ≠ ⊥ → R ≤ T →
      Chapter1.IsSylowIn 2 R ((pResidual 2 H).map H.subtype ⊔ R) →
      A ≤ normalizer (R : Set G) → HasCommonNormal A H R)
    (hne : M₀.pCoreIn 2 ≠ ⊥)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → M₀ ≤ N → N = M) :
    ¬ Chapter1.IsSylowIn 2 (M₀.pCoreIn 2)
      ((pResidual 2 H).map H.subtype ⊔ M₀.pCoreIn 2) := by
  intro hs
  exact h.no_common_normal hu (h.common_normal_of_residual_sylow h311 hne hs)

end CFSG.Quasithin.Chapter3
