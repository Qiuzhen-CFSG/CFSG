module

public import Theory.Alternating.Aut
public import Theory.SpecificGroups.Alternating.TwoThreeCycles
public import Theory.GroupTheory.CComponent.ThreeResidual

/-!
# The cubic index of a normal A₈ C-component

The actual A₈ quotient is centerless, contains an elementary nine, and has
outer automorphism group a two-group. The rank-two normal-component
argument therefore makes its index prime to three. Normality is required
only in the group to which this theorem is applied; the Chapter 12
consumer applies it inside N_G(L).

Source: Aschbacher–Smith A.3.18, printed pp.51–52, and the residual
comparison in 3.3.21(e), p.596 (combined manuscript, 1 March 2004).
-/

public section
open Subgroup Theory.GroupTheory
namespace alternatingGroup.EightComponent

theorem outer_two : IsPGroup 2 (MulAut.Outer (alternatingGroup (Fin 8))) := by
  let A := alternatingGroup (Fin 8)
  have htwo : IsPGroup 2 (Equiv.Perm (Fin 8) ⧸ A) := by
    apply IsPGroup.of_card (n := 1)
    rw [← A.index_eq_card, alternatingGroup.index_eq_two]
    rfl
  apply htwo.of_surjective (MulAut.outerAction A)
  intro x
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup A) x
  obtain ⟨σ, rfl⟩ :=
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 8 (by decide) (by decide)).surjective a
  exact ⟨QuotientGroup.mk' A σ, rfl⟩

theorem index_coprime_three {G : Type*} [Group G] [Finite G]
    (L : Subgroup G) [L.Normal] (hL : L.IsCComponent)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 8))
    (hr : primeRank 3 G ≤ 2) : Nat.Coprime 3 L.index := by
  have hz : center (L ⧸ pCore 2 L) = ⊥ := by
    apply eq_bot_iff.mpr
    intro z hz
    have he := (centerCongr e ⟨z, hz⟩).property
    change e z ∈ center (alternatingGroup (Fin 8)) at he
    rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at he
    exact e.map_eq_one_iff.mp he
  have hrL : 2 ≤ primeRank 3 (L ⧸ pCore 2 L) := by
    rw [primeRank_congr 3 e]
    exact alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide)
  have ho : Nat.Coprime 3 (Nat.card (MulAut.Outer (L ⧸ pCore 2 L))) := by
    rw [Nat.card_congr (MulAut.outerCongr e).toEquiv]
    obtain ⟨n, hn⟩ := outer_two.exists_card_dvd_pow
    exact ((by decide : Nat.Coprime 3 2).pow_right n).coprime_dvd_right hn
  exact cComponent_index_coprime_three_of_quotient L hL hz hrL hr ho

end alternatingGroup.EightComponent
