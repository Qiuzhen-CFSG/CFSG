module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.LocalBranches.QuotientTheta.Source
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.LocalBranches.SecondAction
public import Theory.GroupTheory.PCoreImage
public import Mathlib.GroupTheory.IndexNormal

/-!
# The shared core calculation before quotient recognition

The plane stabilizer S has index two in T, so YS is normal in YT.
Consequently O₂(YS) lies in the earlier O₂(YT)=C_T(V). Conversely C_T(V)
lies in S and is normal in YT, giving O₂(YS)=C_T(V). The same lower bound
holds for O₂(Y₊S) in either choice. These arguments use relative normality
and do not require the quotient identifications or the final local alternative.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.7 and 15.3.11(5), printed pp.1122–1124.
-/

public section

open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter15.Section03.OutsideStructure.LocalBranches.QuotientTheta
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem chosen_join_le_yt (d : CharacteristicTwo.LocalData G) :
    d.Yplus ⊔ d.S ≤ d.Y ⊔ (d.T : Subgroup G) :=
  sup_le_sup (choice_le d.M d.Y d.S d.V₁ d.Yplus d.choice) inf_le_left

omit [Finite G] in
/-- Centralizing the whole module preserves its first definite plane. -/
theorem centralizer_in_t_le_s (d : CharacteristicTwo.LocalData G) :
    (d.T : Subgroup G) ⊓ centralizer (d.V : Set G) ≤ d.S := by
  apply le_inf inf_le_left
  exact inf_le_right.trans ((centralizer_le (d.action.plane_le 1)).trans
    (Subgroup.centralizer_le_normalizer _))

/-- The relative normality of YS in YT follows from the index-two plane stabilizer. -/
theorem yt_normalizes_ys (d : CharacteristicTwo.LocalData G) :
    d.Y ⊔ (d.T : Subgroup G) ≤ normalizer ((d.Y ⊔ d.S : Subgroup G) : Set G) := by
  have hTS : (d.T : Subgroup G) ≤ normalizer (d.S : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (show d.S ≤ (d.T : Subgroup G) from inf_le_left)).mp
      (normal_of_index_eq_two (d.action.planeStabilizer_index_two d.T d.sylow_le 1))
  exact sup_le (le_sup_left.trans (d.Y ⊔ d.S).le_normalizer)
    ((le_inf (d.sylow_le.trans (m_normalizes_y d)) hTS).trans
      (normalizer_inf_normalizer_le_normalizer_sup d.Y d.S))

omit [Finite G] in
/-- The earlier YT core lies in the chosen local core for both choices. -/
theorem centralizer_in_t_le_r (d : CharacteristicTwo.LocalData G)
    (h7core : (d.Y ⊔ (d.T : Subgroup G)).pCoreIn 2 =
      (d.T : Subgroup G) ⊓ centralizer (d.V : Set G)) :
    (d.T : Subgroup G) ⊓ centralizer (d.V : Set G) ≤ d.R := by
  apply le_pCoreIn_of_normalizes (d.T.isPGroup'.to_le inf_le_left)
    ((centralizer_in_t_le_s d).trans le_sup_right)
  rw [← h7core]
  exact (chosen_join_le_yt d).trans ((d.Y ⊔ (d.T : Subgroup G)).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))

/-- Restrict the earlier core identity from YT to its normal subgroup YS. -/
theorem ys_core_eq_centralizer (d : CharacteristicTwo.LocalData G)
    (h7core : (d.Y ⊔ (d.T : Subgroup G)).pCoreIn 2 =
      (d.T : Subgroup G) ⊓ centralizer (d.V : Set G)) :
    (d.Y ⊔ d.S).pCoreIn 2 = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G) := by
  apply le_antisymm
  · exact (pCoreIn_mono_of_normalizes (sup_le_sup_left (show d.S ≤ (d.T : Subgroup G)
      from inf_le_left) _) (yt_normalizes_ys d)).trans_eq h7core
  · apply le_pCoreIn_of_normalizes (d.T.isPGroup'.to_le inf_le_left)
      ((centralizer_in_t_le_s d).trans le_sup_right)
    rw [← h7core]
    exact (sup_le_sup_left (show d.S ≤ (d.T : Subgroup G) from inf_le_left) _).trans
      ((d.Y ⊔ (d.T : Subgroup G)).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))

/-- Both core equalities in clause (5i) for the first choice. -/
theorem first_choice_core (d : CharacteristicTwo.LocalData G)
    (hfirst : d.Yplus = d.Y)
    (h7core : (d.Y ⊔ (d.T : Subgroup G)).pCoreIn 2 =
      (d.T : Subgroup G) ⊓ centralizer (d.V : Set G)) :
    d.R = (d.Y ⊔ d.S).pCoreIn 2 ∧
      d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G) := by
  have he : d.R = (d.Y ⊔ d.S).pCoreIn 2 := by
    change (d.Yplus ⊔ d.S).pCoreIn 2 = _
    rw [hfirst]
  exact ⟨he, he.trans (ys_core_eq_centralizer d h7core)⟩

end CFSG.Quasithin.Chapter15.Section03.OutsideStructure.LocalBranches.QuotientTheta

end
