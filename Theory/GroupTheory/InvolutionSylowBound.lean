module

public import Theory.GroupTheory.InvolutionCentralizerControl
public import Mathlib.GroupTheory.Sylow

/-!
# Sylow bounds from a self-centralizing involution

If an involution is self-centralizing, its cyclic subgroup is Sylow: any
larger two-subgroup contradicts the normalizer condition. Sylow divisibility
then bounds every two-subgroup, without requiring it to contain the involution.

This is the first reduction in GLS, volume 4, Chapter 2, Lemma 13.3.
-/

namespace Subgroup

/-- A self-centralizing involution generates an actual Sylow two-subgroup. -/
public theorem exists_sylow_of_self_centralizing_involution
    {G : Type*} [Group G] [Finite G] (u : G) (hu : orderOf u = 2)
    (hc : centralizer ({u} : Set G) ≤ zpowers u) :
    ∃ S : Sylow 2 G, (S : Subgroup G) = zpowers u := by
  have hz : Nat.card (zpowers u) = 2 := (Nat.card_zpowers u).trans hu
  refine ⟨{ toSubgroup := zpowers u
            isPGroup' := IsPGroup.of_card (n := 1) (by simpa using hz)
            is_maximal' := ?_ }, rfl⟩
  intro Q hQ hle
  let := hQ.isNilpotent
  apply le_antisymm _ hle
  apply le_of_nilpotent_of_card_two_of_centralizer_le Q (zpowers u) hle hz
  intro x hx
  exact hc (mem_centralizer_singleton_iff.mpr
    ((mem_centralizer_iff.mp hx.2) u (mem_zpowers u)).symm)

/-- Every two-subgroup has order at most two when an involution is self-centralizing. -/
public theorem card_le_two_of_self_centralizing_involution
    {G : Type*} [Group G] [Finite G] (u : G) (hu : orderOf u = 2)
    (hc : centralizer ({u} : Set G) ≤ zpowers u)
    (P : Subgroup G) (hP : IsPGroup 2 P) : Nat.card P ≤ 2 := by
  obtain ⟨S, hS⟩ := exists_sylow_of_self_centralizing_involution u hu hc
  have hSc : Nat.card S = 2 := by
    rw [hS, Nat.card_zpowers, hu]
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hd : Nat.card P ∣ Nat.card S := hk ▸ S.pow_dvd_card_of_pow_dvd_card
    (hk ▸ P.card_subgroup_dvd_card)
  exact Nat.le_of_dvd (by omega) (hSc ▸ hd)

end Subgroup
