module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalContainment
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.Intersections

/-!
# TerminalContainment at the original ambient group and Sylow subgroup

These are the same source arguments as `TerminalContainment`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02 ChapterE

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G} (S : Setup T L V)

variable (structural : Structural1222At KnownSimple.IsKnownSimple T)

include S structural

theorem chosen_sylow_orbit_eq_at : componentOrbit V (T : Subgroup G) = V := by
  apply le_antisymm _ (le_componentOrbit V _)
  exact iSup_conjugates_le_of_le_normalizer V (T : Subgroup G) V le_rfl
    ((structural L S.hypothesis).2.2 V S.chosen).1

theorem chosen_centralizer_unique_at : maximalTwoLocalOvergroups (normalizer
    (((T : Subgroup G) ⊓ centralizer (V : Set G) : Subgroup G) : Set G)) =
    {normalizer (L : Set G)} := by
  simpa only [chosen_sylow_orbit_eq_at S structural] using
    S.chosen.doubledOrbit_centralizer_unique S.hypothesis

theorem generation_one_le_normalizer_at {H : Subgroup G} (hTH : (T : Subgroup G) ≤ H)
    (hn : generationParameter H = 1)
    (hr : (1 : ℕ∞) < globalR V) (hw : (1 : ℕ∞) < globalW V (T : Subgroup G)) :
    H ≤ normalizer (L : Set G) := by
  let := S.chosen.elementary
  have hT : HypothesisE322 V T := ⟨S.chosen.ne_bot, S.chosen.le_sylow,
    ((structural L S.hypothesis).2.2 V S.chosen).1⟩
  apply SourceContainment.le_of_generationParameter_pos hT (T.subtype hTH)
    (chosen_centralizer_unique_at S structural)
  · exact inf_le_right.trans ((Subgroup.centralizer_le_normalizer _).trans
      (S.hypothesis.source_chosen_normalizer_le_at structural
        (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
        (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X)) S.chosen))
  · simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] using
      (inf_le_left : (T : Subgroup G) ⊓ centralizer (V : Set G) ≤ T)
  · rw [hn]; decide
  · simpa only [hn, Nat.cast_one, lt_min_iff] using And.intro hw hr

theorem solvable_le_normalizer_at {H : Subgroup G} [Group.IsSolvable H]
    (hTH : (T : Subgroup G) ≤ H)
    (hr : (1 : ℕ∞) < globalR V) (hw : (1 : ℕ∞) < globalW V (T : Subgroup G)) :
    H ≤ normalizer (L : Set G) := by
  let := S.chosen.elementary
  have hT : HypothesisE322 V T := ⟨S.chosen.ne_bot, S.chosen.le_sylow,
    ((structural L S.hypothesis).2.2 V S.chosen).1⟩
  apply SourceContainment.le_of_solvable hT (T.subtype hTH)
    (chosen_centralizer_unique_at S structural)
  · exact inf_le_right.trans ((Subgroup.centralizer_le_normalizer _).trans
      (S.hypothesis.source_chosen_normalizer_le_at structural
        (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
        (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X)) S.chosen))
  · simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] using
      (inf_le_left : (T : Subgroup G) ⊓ centralizer (V : Set G) ≤ T)
  · exact lt_min hw hr

theorem hstar_not_solvable_at {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hr : (1 : ℕ∞) < globalR V) (hw : (1 : ℕ∞) < globalW V (T : Subgroup G)) :
    ¬ Group.IsSolvable H := by
  intro hs
  let := hs
  exact hH.1.2 (solvable_le_normalizer_at S structural hH.1.1.2 hr hw)

theorem hstar_generation_ne_one_at {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hr : (1 : ℕ∞) < globalR V) (hw : (1 : ℕ∞) < globalW V (T : Subgroup G)) :
    generationParameter H ≠ 1 :=
  fun hn => hH.1.2 (generation_one_le_normalizer_at S structural hH.1.1.2 hn hr hw)

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

