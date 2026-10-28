module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.Intersections
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.DoubleNaturalExcludedSetup
public import CFSG.Quasithin.ChapterE.Section03.SourceContainment

/-!
# Generation-one containment in the original A₇ setup

The structural input makes the chosen module its own Sylow conjugate span.
The source kernel and uniqueness theorems then supply the literal uniqueness
premise for E.3.35. Consequently r,w>1 put every overgroup of generation
parameter one in N_G(L); the solvable clause also follows without any
attainment hypothesis. The selected escaping H-star member is therefore
nonsolvable, as required at the start of 12.3.12.

Source: Aschbacher--Smith, 12.3.11--12, printed p.811, using E.3.35(1).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02 ChapterE
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} (S : Setup T L V)
variable (structural : Structural1222 KnownSimple.IsKnownSimple.{u})

include S structural

theorem chosen_sylow_orbit_eq : componentOrbit V (T : Subgroup G) = V := by
  apply le_antisymm _ (le_componentOrbit V _)
  exact iSup_conjugates_le_of_le_normalizer V (T : Subgroup G) V le_rfl
    ((structural G T L S.hypothesis).2.2 V S.chosen).1

theorem chosen_centralizer_unique : maximalTwoLocalOvergroups (normalizer
    (((T : Subgroup G) ⊓ centralizer (V : Set G) : Subgroup G) : Set G)) =
    {normalizer (L : Set G)} := by
  simpa only [chosen_sylow_orbit_eq S structural] using
    S.chosen.doubledOrbit_centralizer_unique S.hypothesis

theorem generation_one_le_normalizer {H : Subgroup G} (hTH : (T : Subgroup G) ≤ H)
    (hn : generationParameter H = 1)
    (hr : (1 : ℕ∞) < globalR V) (hw : (1 : ℕ∞) < globalW V (T : Subgroup G)) :
    H ≤ normalizer (L : Set G) := by
  let := S.chosen.elementary
  have hT : HypothesisE322 V T := ⟨S.chosen.ne_bot, S.chosen.le_sylow,
    ((structural G T L S.hypothesis).2.2 V S.chosen).1⟩
  apply SourceContainment.le_of_generationParameter_pos hT (T.subtype hTH)
    (chosen_centralizer_unique S structural)
  · exact inf_le_right.trans ((Subgroup.centralizer_le_normalizer _).trans
      (S.hypothesis.source_chosen_normalizer_le structural
        (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
        (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X)) S.chosen))
  · simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] using
      (inf_le_left : (T : Subgroup G) ⊓ centralizer (V : Set G) ≤ T)
  · rw [hn]; decide
  · simpa only [hn, Nat.cast_one, lt_min_iff] using And.intro hw hr

/-- The solvable E.3.35 clause uses the proved E.1.13 generation theorem. -/
theorem solvable_le_normalizer {H : Subgroup G} [Group.IsSolvable H]
    (hTH : (T : Subgroup G) ≤ H)
    (hr : (1 : ℕ∞) < globalR V) (hw : (1 : ℕ∞) < globalW V (T : Subgroup G)) :
    H ≤ normalizer (L : Set G) := by
  let := S.chosen.elementary
  have hT : HypothesisE322 V T := ⟨S.chosen.ne_bot, S.chosen.le_sylow,
    ((structural G T L S.hypothesis).2.2 V S.chosen).1⟩
  apply SourceContainment.le_of_solvable hT (T.subtype hTH)
    (chosen_centralizer_unique S structural)
  · exact inf_le_right.trans ((Subgroup.centralizer_le_normalizer _).trans
      (S.hypothesis.source_chosen_normalizer_le structural
        (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
        (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X)) S.chosen))
  · simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] using
      (inf_le_left : (T : Subgroup G) ⊓ centralizer (V : Set G) ≤ T)
  · exact lt_min hw hr

/-- The actual H-star chosen before 12.3.12 is nonsolvable. -/
theorem hstar_not_solvable {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hr : (1 : ℕ∞) < globalR V) (hw : (1 : ℕ∞) < globalW V (T : Subgroup G)) :
    ¬ Group.IsSolvable H := by
  intro hs
  let := hs
  exact hH.1.2 (solvable_le_normalizer S structural hH.1.1.2 hr hw)

/-- Generation parameter one is impossible for that same escaping H-star. -/
theorem hstar_generation_ne_one {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hr : (1 : ℕ∞) < globalR V) (hw : (1 : ℕ∞) < globalW V (T : Subgroup G)) :
    generationParameter H ≠ 1 :=
  fun hn => hH.1.2 (generation_one_le_normalizer S structural hH.1.1.2 hn hr hw)

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
