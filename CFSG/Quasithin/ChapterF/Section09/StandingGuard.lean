module

public import CFSG.Quasithin.ChapterF.Section09.Basic
public import CFSG.Quasithin.Chapter3.Section01.CoreFreeStandingGuard

/-!
# The genuine Chapter 3 standing guard from F.9.1

The original flag line is nontrivial and lies in both local two-cores:
in LT by reducedness of V, and in H by the F.9.2 conjugate-span bound.
F.9.1 explicitly says their join has trivial two-core. Thus this actual
pair supplies two distinct maximal two-locals over T, and an outside
maximal two-local for every subsequent selected normalizer.

Source: Aschbacher--Smith F.9.1--2, pp.317--318, and the standing condition
after 2.1.1, p.518. No conclusion of the unique-maximal classification is used.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.Section09.Setup.Hypothesis
variable {G : Type*} [Group G] [Finite G] {D : Setup G} (h : D.Hypothesis)
include h

/-- The original flag line lies in the intrinsic ambient core of LT. -/
theorem point_le_LT_core : D.V₁ ≤ D.LT.pCoreIn 2 := by
  have hv : D.V ≤ D.LT.pCoreIn 2 := by
    simpa only [pCoreIn, map_subgroupOf_eq_of_le h.V_le_LT] using
      map_mono (f := D.LT.subtype) h.reduced.le_pCore
  exact h.point_lt.le.trans (h.plus_le.trans hv)

/-- Both local groups used in the F.9.1 core-free join have nontrivial cores. -/
theorem local_cores_ne_bot : pCore 2 D.LT ≠ ⊥ ∧ pCore 2 D.H ≠ ⊥ := by
  have hn : D.V₁ ≠ ⊥ := h.g2_hypothesis.point_ne_bot
  have hH : D.V₁ ≤ D.H.pCoreIn 2 :=
    h.point_lt.le.trans ((le_conjugateSpanBy D.Vplus D.H).trans h.UH_le_QH)
  constructor
  · intro hz
    apply hn
    apply bot_unique
    simpa only [pCoreIn, hz, Subgroup.map_bot] using h.point_le_LT_core
  · intro hz
    apply hn
    apply bot_unique
    simpa only [pCoreIn, hz, Subgroup.map_bot] using hH

/-- Every maximal two-local over T has an actual outside maximal two-local. -/
theorem hasMaximalOutside (M : Subgroup G) (hM : IsMaximalTwoLocal M)
    (hTM : (D.T : Subgroup G) ≤ M) : Chapter3.HasMaximalOutside D.T M :=
  Chapter3.hasMaximalOutside_of_core_free_pair D.T D.LT D.H le_sup_right h.T_le_H
    h.local_cores_ne_bot.1 h.local_cores_ne_bot.2 h.generated_core M hM hTM

/-- The original source pair supplies an actual HStar member at any selected
maximal normalizer. -/
theorem exists_HStar (M : Subgroup G) (hM : IsMaximalTwoLocal M)
    (hTM : (D.T : Subgroup G) ≤ M) :
    ∃ K : Subgroup G, K ∈ Chapter3.HStar (D.T : Subgroup G) M :=
  Chapter3.exists_HStar_of_hasMaximalOutside (h.hasMaximalOutside M hM hTM)

end CFSG.Quasithin.ChapterF.Section09.Setup.Hypothesis
