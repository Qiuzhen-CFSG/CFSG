module

public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SmallSource
public import Theory.GroupTheory.GeneralizedFitting.ComponentRankNormality
public import Theory.Quasithin.NormalTwoRank
public import Theory.SpecificGroups.PSL3Three.RankLower
public import Theory.Mathieu.M11.Properties.RankLower

/-!
# Normality of the actual small non-Bender components

The original Gamma group has nontrivial two-core, so quasithinness bounds
its ordinary three-rank by two. Both PSL3(3) and M11 contain an actual
elementary nine and have trivial center. Distinct conjugate components
would therefore give rank four, proving normality in H.

Source: Aschbacher--Smith 2.5.3(4), printed p.553, the assertion K=K0
in case 2.5.2(3). Only original quasithinness and Gamma membership are used;
no ambient rank bound or component normality is assumed.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {M H : Subgroup G}

private theorem center_bot_of_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (h : center B = ⊥) : center A = ⊥ := by
  apply eq_bot_iff.mpr
  intro a ha
  have hb : e a ∈ center B := ((centerCongr e) ⟨a, ha⟩).property
  have hb1 : e a = 1 := by simpa only [h, mem_bot] using hb
  exact mem_bot.mpr (e.injective (hb1.trans (map_one e).symm))

/-- Both small source components are normal in the original Gamma group. -/
theorem small_component_normal
    (hG : IsQuasithin G) (hH : H ∈ gammaZero (Chapter1.He G) M)
    (D : Subgroup H) (hD : IsComponent H D)
    (hm : Nonempty (D ≃* Matrix.PSL3Three.PSL) ∨ Nonempty (D ≃* Sporadic.Mathieu.M11)) :
    D.Normal := by
  have hcore : pCore 2 H ≠ ⊥ := by
    intro hb
    have hne := (hH.elim (fun h => h.1.1) (fun h => h.1)).1
    apply hne
    simp only [twoCore, hb, Subgroup.map_bot]
  have hHrank : primeRank 3 H ≤ 2 :=
    Theory.Quasithin.primeRank_subgroup_le_two_of_normal_two_subgroup hG H (pCore 2 H)
      hcore pCore_isPGroup 3 Nat.prime_three (by decide)
  have hc : center D = ⊥ := by
    rcases hm with hm | hm
    · obtain ⟨e⟩ := hm
      exact center_bot_of_equiv (e.trans Matrix.PSL3Three.equiv.symm)
        Matrix.PSL3Three.center_eq_bot
    · obtain ⟨e⟩ := hm
      exact center_bot_of_equiv e Sporadic.Mathieu.m11_center_eq_bot
  have hd : 2 ≤ primeRank 3 D := by
    rcases hm with hm | hm
    · obtain ⟨e⟩ := hm
      rw [primeRank_equiv 3 e]
      exact Matrix.PSL3Three.primeRank_three_ge_two
    · obtain ⟨e⟩ := hm
      rw [primeRank_equiv 3 e]
      exact Sporadic.Mathieu.m11_primeRank_three_ge_two
  exact hD.normal_of_centerless_primeRank hc hd hHrank

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
