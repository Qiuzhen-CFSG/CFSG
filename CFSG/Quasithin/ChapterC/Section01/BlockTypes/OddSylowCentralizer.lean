module
public import Theory.GroupTheory.CoprimeSelfCentralizingAction
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.CubicSylowCentralizer
/-!
# Odd actors fixing a full Sylow subgroup of a short group

The two-core of a short group is self-centralizing. An odd actor fixing a
full Sylow fixes that core, so coprime self-centralizing action makes it
fix the whole block. A subgroup normalizing the block then has its
commutators with the odd actor in the same centralizer.

This retains the actual ambient action and applies to Hall axes over any
even field. Source: Aschbacher–Smith 10.2.3(4), printed p.747.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC
variable {G : Type*} [Group G] [Finite G]

/-- Every odd normalizing actor fixing a full Sylow fixes the short group. -/
theorem IsShort.centralizes_of_odd_sylow_fixed (K P A : Subgroup G) (hK : IsShort K)
    (hP : Chapter1.IsSylowIn 2 P K)
    (hA : Odd (Nat.card A)) (hAK : A ≤ normalizer (K : Set G))
    (hAP : A ≤ centralizer (P : Set G)) : A ≤ centralizer (K : Set G) := by
  have hself : centralizer (pCore 2 K : Set K) ≤ pCore 2 K := by
    rw [←hK.fitting]
    exact centralizer_generalizedFitting_le K
  obtain ⟨Q,hQ⟩ := hP
  have hQP : K.pCoreIn 2 ≤ P :=
    (map_mono (pCore_isPGroup.le_sylow_of_normal Q)).trans_eq hQ
  have hcop : Nat.Coprime (Nat.card A) (Nat.card (pCore 2 K)) := by
    obtain ⟨m,hm⟩ := (pCore_isPGroup (p := 2) (G := K)).exists_card_eq
    rw [hm]
    exact hA.coprime_two_right.pow_right m
  exact Subgroup.centralizes_of_coprime_of_selfCentralizing_normal A K (pCore 2 K)
    hcop hAK hself (hAP.trans (centralizer_le hQP))

/-- The literal odd-axis commutator Borel centralizes the short group. -/
theorem IsShort.odd_and_commutator_centralize (K P A S : Subgroup G) (hK : IsShort K)
    (hP : Chapter1.IsSylowIn 2 P K) (hA : Odd (Nat.card A))
    (hAK : A ≤ normalizer (K : Set G)) (hAP : A ≤ centralizer (P : Set G))
    (hSK : S ≤ normalizer (K : Set G)) :
    A ≤ centralizer (K : Set G) ∧ (⁅S,A⁆ ⊔ A : Subgroup G) ≤ centralizer (K : Set G) := by
  have hc := IsShort.centralizes_of_odd_sylow_fixed K P A hK hP hA hAK hAP
  have hSC := hSK.trans (normalizer_le_normalizer_centralizer K)
  have hh := le_normalizer_iff_commutator_le_left.mp hSC
  refine ⟨hc,sup_le ?_ hc⟩
  exact (commutator_mono le_rfl hc).trans (by rwa [commutator_comm] at hh)
end CFSG.Quasithin.ChapterC
