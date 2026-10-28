module

public import Theory.Alternating.Aut
public import Theory.SpecificGroups.Alternating.TwoThreeCycles
public import Theory.GroupTheory.CComponent.ThreeResidual
public import Theory.GroupTheory.PResidual.PrimeTo

/-!
# Order-three elements normalizing an A₇ C-component

A₇ has centerless two-core quotient, contains an elementary nine, and has
a two-group of outer automorphisms. The centralizer rank bound therefore
makes its relative normalizer index prime to three. Every order-three
element of that normalizer lies in the component.

The proof works inside the normalizer and assumes only C-component
membership in the ambient group; ambient normality is not required.
This proves the part of the ordinary residual argument of A.3.18 used for
A₇ in 15.3.49(k): Aschbacher–Smith, combined manuscript (1 March 2004),
printed pp.51–52 and 1144.
-/

public section

open Subgroup
namespace alternatingGroup.SevenComponent

theorem outer_two : IsPGroup 2 (MulAut.Outer (alternatingGroup (Fin 7))) := by
  let A := alternatingGroup (Fin 7)
  have htwo : IsPGroup 2 (Equiv.Perm (Fin 7) ⧸ A) := by
    apply IsPGroup.of_card (n := 1)
    rw [← A.index_eq_card, alternatingGroup.index_eq_two]
    rfl
  apply htwo.of_surjective (MulAut.outerAction A)
  intro x
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup A) x
  obtain ⟨σ, rfl⟩ :=
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by decide) (by decide)).surjective a
  exact ⟨QuotientGroup.mk' A σ, rfl⟩

theorem order_three_mem {G : Type*} [Group G] [Finite G]
    (L : Subgroup G) (hL : L.IsCComponent)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 7))
    (hr : primeRank 3 G ≤ 2) {x : G}
    (hx : orderOf x = 3) (hn : x ∈ normalizer (L : Set G)) : x ∈ L := by
  let N := normalizer (L : Set G)
  let D := L.subgroupOf N
  let eD : (D ⧸ pCore 2 D) ≃* alternatingGroup (Fin 7) :=
    (QuotientGroup.congr _ _ (subgroupOfEquivOfLe L.le_normalizer)
      (pCore_map_iso 2 _)).trans e
  have hz : center (D ⧸ pCore 2 D) = ⊥ := by
    apply eq_bot_iff.mpr
    intro z hz
    have he := (centerCongr eD ⟨z, hz⟩).property
    change eD z ∈ center (alternatingGroup (Fin 7)) at he
    rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at he
    exact eD.map_eq_one_iff.mp he
  have hrD : 2 ≤ primeRank 3 (D ⧸ pCore 2 D) := by
    rw [primeRank_congr 3 eD]
    exact alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide)
  have ho : Nat.Coprime 3 (Nat.card (MulAut.Outer (D ⧸ pCore 2 D))) := by
    rw [Nat.card_congr (MulAut.outerCongr eD).toEquiv]
    obtain ⟨n, hn⟩ := outer_two.exists_card_dvd_pow
    exact ((by decide : Nat.Coprime 3 2).pow_right n).coprime_dvd_right hn
  have hi := Theory.GroupTheory.cComponent_index_coprime_three_of_quotient D
    (hL.subgroupOf L.le_normalizer) hz hrD
    ((primeRank_le_of_injective 3 N.subtype N.subtype_injective).trans hr) ho
  have hx3 : (⟨x, hn⟩ : N) ^ (3 ^ 1) = 1 := by
    apply Subtype.ext
    simpa [hx] using pow_orderOf_eq_one x
  exact primeToResidual_le D hi (mem_primeToResidual_of_pow hx3)

end alternatingGroup.SevenComponent
