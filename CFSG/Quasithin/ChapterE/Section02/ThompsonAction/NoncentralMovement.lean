module
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.Basic
public import CFSG.Quasithin.ChapterB.Section02.OffenderFactorization
/-!
# Noncentral reduced modules and the Baumann normality obstruction

A proper reduced centralizer lies in the minimal-parabolic core, independently
of Thompson movement. Hence its Sylow intersection is the two-core. If the
Thompson subgroup centralizes this module, B.2.10 makes the original Baumann
subgroup normal. This supplies the movement step for the H* omega orbit in
Aschbacher--Smith 10.2.2(2), printed p.744.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.ThompsonAction
variable {G : Type*} [Group G] [Finite G]

theorem reduced_centralizer_sylow_of_proper
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) (hU : IsPReduced 2 U)
    (hc : centralizer (U : Set G) ≠ ⊤) :
    (T : Subgroup G) ⊓ centralizer (U : Set G) = pCore 2 G := by
  let := hU.normal
  let C := centralizer (U : Set G)
  let q := QuotientGroup.mk' C
  have hk : q.ker ≠ ⊤ := by simpa only [q, QuotientGroup.ker_mk'] using hc
  have hC := (ChapterB.minimalParabolic_reduced_image T hP q
    (QuotientGroup.mk'_surjective C) hU.quotient_pCore_eq_bot hk).1
  rw [QuotientGroup.ker_mk'] at hC
  apply le_antisymm
  · exact (inf_le_inf_left _ hC).trans (ChapterB.minimalParabolic_sylow_inf_core T hP).le
  · exact le_inf (pCore_isPGroup.le_sylow_of_normal T)
      (le_centralizer_iff.mp hU.le_centralizer_pCore)

theorem thompson_moves_of_noncentral_reduced_baumann_not_normal
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) (hU : IsPReduced 2 U)
    (hc : centralizer (U : Set G) ≠ ⊤)
    (hB : ¬ (ChapterB.baumann (T : Subgroup G)).Normal) :
    ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G) := by
  let := hU.normal
  let := hU.elementary
  intro hJ
  apply hB
  exact (ChapterB.lemma_B_2_10_centralizing U (T : Subgroup G)
    (hU.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal T))
    (pCore_isPGroup.le_sylow_of_normal T)
    (reduced_centralizer_sylow_of_proper T hP U hU hc).symm
    (by simpa only [ChapterB.thompsonJ_zero] using hJ)).2.2.2
end CFSG.Quasithin.ChapterE.ThompsonAction
