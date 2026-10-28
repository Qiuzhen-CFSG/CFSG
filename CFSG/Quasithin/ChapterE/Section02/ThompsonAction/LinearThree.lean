module

public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.LinearThree
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.Basic
public import Theory.Representation.NormalElementaryQuotient

/-!
# Excluding the natural SL3 residual in the original reduced action

The noncentral reduced action has a minimal-parabolic centralizer quotient.
Apply the genuine two-parabolic obstruction to its literal two-residual and
its original representation on U. This excludes a repeated natural SL3
branch without replacing the action or assuming an invariant flag.

Source: Aschbacher–Smith, B.6.9 and E.2.3, printed pp.116 and216–217
(1 March 2004). Extracting the natural action of an individual component
from a general FF module remains a separate classification step.
-/

public section
open scoped IsMulCommutative
open Subgroup Stellmacher Theory.GroupTheory Representation
namespace CFSG.Quasithin.ChapterE.ThompsonAction
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]

/-- No marked reduced-image action has a repeated natural SL3 two-residual. -/
theorem not_repeated_natural_residual_three
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G)) (hcore : pCore 2 H = ⊥)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (F : ChapterB.QuasisimpleSource.BinaryField) (r : ℕ) (hr : 0 < r) :
    ¬ ChapterB.QuasisimpleSource.IsRepeatedLinearNatural
      ((NormalElementaryQuotient.representation U q hq hker).comp
        (pResidual 2 H).subtype) F 3 r := by
  have hn : q.ker ≠ ⊤ := by
    intro he
    apply hJ
    rw [← hker, he]
    exact le_top
  have hp := (ChapterB.minimalParabolic_reduced_image T hP q hq hcore hn).2
  exact ChapterB.minimalParabolic_not_repeated_natural_residual_three
    (T.mapSurjective hq) hp _ F r hr

/-- The same exclusion for the original centralizer quotient and its literal action. -/
theorem source_not_repeated_natural_residual_three
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (F : ChapterB.QuasisimpleSource.BinaryField) (r : ℕ) (hr : 0 < r) :
    let := hU.normal
    let := hU.elementary
    let C := centralizer (U : Set G)
    let q := QuotientGroup.mk' C
    let ρ := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    ¬ ChapterB.QuasisimpleSource.IsRepeatedLinearNatural
      (ρ.comp (pResidual 2 (G ⧸ C)).subtype) F 3 r := by
  let := hU.normal
  let := hU.elementary
  exact not_repeated_natural_residual_three T hP U _ (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _) hU.quotient_pCore_eq_bot hJ F r hr

end CFSG.Quasithin.ChapterE.ThompsonAction
