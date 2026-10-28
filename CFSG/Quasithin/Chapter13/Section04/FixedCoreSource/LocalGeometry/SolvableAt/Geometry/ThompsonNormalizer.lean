module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NormalizerAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.PlanePairAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Geometry.ThompsonNormalizer

public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Normalizer
public import Stellmacher.OmegaOneCenterMap
public import Stellmacher.ElementaryAbelianMaxOrder
public import Theory.GroupTheory.ConjugateSpanOrder

/-!
# The ambient Thompson normalizer from the source overgroup supplement: structure at the original group

Specialize the original proof to `Structural1222At` at the same G,T.
All action maps, full quotient kernels and source hypotheses are retained;
no universal Chapter12 record is inferred. Intrinsic model and group lemmas
are reused from the preserved source module. This family feeds guarded
solvable-centralizer recognition on the actual five-dimensional module.

Source: Aschbacher--Smith 13.4.8--9, printed pp.904--907;
see the original `Solvable/Geometry/ThompsonNormalizer` proof for the local step.
-/

public noncomputable section

namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Subgroup Theory.GroupTheory Stellmacher
open Chapter12.Section02 Chapter14.Section03.FaithfulSource SolvableCentralizerC3
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

open scoped Pointwise in
/-- Apply the earlier overgroup supplement to N_G(J(T)), proving its applicability. -/
theorem thompson_normalizer_le_generated_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D) (z : G) (H₀ : Subgroup G)
    (hnormal : H₀ ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G))
    (supplement : ∀ X : Subgroup G, X ∈ Chapter1.HOver G (H₀ : Set G) →
      (X : Set G) = (H₀ : Set G) *
        (X ⊓ centralizer (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H₀ : Set G) : Subgroup G)) :
    normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ≤
      generated (normalizer (L : Set G)) z H₀ := by
  let J := elementaryAbelianMaxJ (T : Subgroup G)
  let N := normalizer (J : Set G)
  have hJT : J ≤ T := sSup_le fun _ hA => hA.1
  have hJN : J ≤ N := J.le_normalizer
  have hcore : J ≤ N.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (T.isPGroup'.to_le hJT) hJN le_rfl
  have hN : N ∈ Chapter1.HOver G (H₀ : Set G) := by
    refine ⟨?_, hnormal⟩
    intro hbot
    exact original_maxJ_ne_bot D m (le_bot_iff.mp (hbot ▸ hcore))
  have hcent : centralizer
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H₀ : Set G) ≤
      normalizer (L : Set G) := by
    rw [← fixed_centralizer_eq_normalizer_at h structural D m]
    exact centralizer_le ((LocalGeometry.fixed_le_original_omegaCenter_at h structural D m).trans
      (le_conjugateSpanBy _ _))
  intro x hx
  obtain ⟨a, ha, c, hc, rfl⟩ := (supplement N hN).le hx
  exact (generated (normalizer (L : Set G)) z H₀).mul_mem
    ((show H₀ ≤ generated (normalizer (L : Set G)) z H₀ from le_sup_right) ha)
    ((first_le_generated _ _ _) (hcent hc.2))

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
