module

public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.LinearThree
public import CFSG.Quasithin.Chapter3.Section01.E23Input

/-!
# The original qrc action has no natural SL3 residual

Apply the two-parabolic obstruction at the original H and the original orbit
span of the Sylow omega-center. All quotient maps and representations are the
ones constructed from the qrc hypotheses, not additional model data.

Source: Aschbacher–Smith, 3.1.7 via E.2.3 and B.6.9, printed pp.575–576,
216–217 and116 (1 March 2004 manuscript).
-/

public section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Stellmacher Representation
namespace CFSG.Quasithin.Chapter3
universe u
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}
  {T : Sylow 2 G} {M M₀ H V : Subgroup G}

theorem QrcHypotheses.e23_not_repeated_natural_residual_three
    (h : QrcHypotheses T M M₀ H V) (hG : IsSimpleQTKE K G)
    (hM : IsMaximalTwoLocal M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → M₀ ≤ N → N = M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (hZ : ¬ omegaOneCenterAmbient (T : Subgroup G) ≤ (center H).map H.subtype)
    (F : ChapterB.QuasisimpleSource.BinaryField) (r : ℕ) (hr : 0 < r) :
    let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
    let hU := h.sylowOmega_reduced (hG.evenCharacteristic T)
    let := hU.normal
    let := hU.elementary
    let C := centralizer (U : Set H)
    let q := QuotientGroup.mk' C
    let ρ := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    ¬ ChapterB.QuasisimpleSource.IsRepeatedLinearNatural
      (ρ.comp (pResidual 2 (H ⧸ C)).subtype) F 3 r := by
  obtain ⟨_, _, hp, hU, hj⟩ := h.e23_hypotheses hG hM hu hJ hZ
  exact ChapterE.ThompsonAction.source_not_repeated_natural_residual_three
    _ hp _ hU hj F r hr

end CFSG.Quasithin.Chapter3
