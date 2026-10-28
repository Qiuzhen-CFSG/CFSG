module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.SuzukiRecognition
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Suzuki

/-!
# The Suzuki source branch of K.3.6

Natural-module recognition supplies the actual marked matrix model required
by the Sylow and ratio calculations. Applying them to this constructed model
gives every K.3.6 conclusion on the original ambient group and binary module,
starting only with the source hypotheses and the specified central quotient.

Source: Aschbacher–Smith, reduction preceding K.3.5 and K.3.6, printed p.457
(1 March 2004 manuscript); Guralnick–Malle, *Classification of 2F-modules, II*,
Theorem 8.1 and Table 17.
-/

public section
namespace CFSG.Quasithin.ChapterK.RankOne
open BenderSuzuki.MatrixGroups Subgroup Representation.BinaryOffender
open scoped ENNReal

variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {m : ℕ} {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

/-- K.3.6 with its natural-module premise discharged by the source recognition
theorem. The residual, Sylow omega, action ratios and unique threshold subgroup
are all taken in the original ambient group. -/
theorem SourceHypotheses.suzuki_case_of_quotient (h : SourceHypotheses ρ L)
    (hm : 1 ≤ m) (e : (L ⧸ Subgroup.center L) ≃* SuzukiMatrixGroup m) (T : Sylow 2 G) :
    Odd L.index ∧ primeToResidual 2 G = L ∧ (T : Subgroup G) ≤ L ∧
    IsElementaryTwo (omegaOneAmbient (T : Subgroup G)) ∧
    rank (omegaOneAmbient (T : Subgroup G)) = 2 * m + 1 ∧
    Module.finrank (ZMod 2) V = 4 * (2 * m + 1) ∧
    Module.finrank (ZMod 2) (fixedSpace ρ (omegaOneAmbient (T : Subgroup G))) =
      2 * (2 * m + 1) ∧
    (∀ t : G, t ≠ 1 → t ^ 2 = 1 →
      LinearMap.range (ρ t - LinearMap.id) = LinearMap.ker (ρ t - LinearMap.id)) ∧
    IsQuadratic ρ (omegaOneAmbient (T : Subgroup G)) ∧
    actionRatio ρ (omegaOneAmbient (T : Subgroup G)) = 2 ∧
    quadraticRatio ρ = 2 ∧ cubicRatio ρ = 2 ∧
    {A : Subgroup G | A ≤ T ∧ IsElementaryTwo A ∧ IsQuadratic ρ A ∧ actionRatio ρ A ≤ 2} =
      {omegaOneAmbient (T : Subgroup G)} :=
  h.suzuki_case (h.suzukiModel hm e) hm T

end CFSG.Quasithin.ChapterK.RankOne
