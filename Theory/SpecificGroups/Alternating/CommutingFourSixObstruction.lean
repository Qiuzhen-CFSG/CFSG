module

public import Theory.SpecificGroups.Alternating.E9A4LocalRank
public import Theory.SpecificGroups.Alternating.TwoThreeCycles
public import Theory.GroupTheory.DisjointCommutingProduct

/-!
# Commuting A₄ and A₆ subgroups obstruct quasithinness

The A₄ factor is centerless, so the two commuting factors have trivial
intersection. Two independent three-cycles in A₆ and the entire A₄ factor
then embed E₉ × A₄. Its normal four-group makes the rank-three witness a
two-local witness, which contradicts quasithinness.

This is the A₆ exclusion in Aschbacher–Smith, proof of 13.9.1, printed
p.974. It requires no classification of proper subgroups and does not
replace two-local rank by ordinary ambient rank.
-/

public section

namespace Theory.Quasithin

open Subgroup

private def e9Coordinates : Multiplicative (ZMod 3 × ZMod 3) →*
    (Fin 2 → Multiplicative (ZMod 3)) where
  toFun a i := if i = 0 then Multiplicative.ofAdd a.toAdd.1
    else Multiplicative.ofAdd a.toAdd.2
  map_one' := by funext i; split <;> rfl
  map_mul' a b := by
    funext i
    simp only [Pi.mul_apply]
    split_ifs <;> rfl

private theorem e9Coordinates_injective : Function.Injective e9Coordinates := by
  intro a b h
  apply Multiplicative.toAdd.injective
  apply Prod.ext
  · have h0 := congrFun h 0
    simpa [e9Coordinates] using h0
  · have h1 := congrFun h 1
    simpa [e9Coordinates] using h1

/-- Actual commuting A₄ and A₆ subgroups produce a rank-three two-local. -/
theorem not_quasithin_of_commuting_a4_a6
    {G : Type*} [Group G] [Finite G] (A H : Subgroup G)
    (eA : A ≃* alternatingGroup (Fin 4))
    (eH : H ≃* alternatingGroup (Fin 6))
    (hc : A ≤ centralizer (H : Set G)) : ¬ IsQuasithin G := by
  have hcenter : center A = ⊥ := by
    apply eq_bot_iff.mpr
    intro a ha
    have hm := ((centerCongr eA) ⟨a, ha⟩).property
    change eA a ∈ center (alternatingGroup (Fin 4)) at hm
    rw [alternatingGroup.center_eq_bot (by norm_num : 4 ≤ Nat.card (Fin 4))] at hm
    exact eA.injective (by simpa only [map_one] using Subgroup.mem_bot.mp hm)
  have hd : Disjoint H A := by
    apply disjoint_def.mpr
    intro x hxH hxA
    have hxa : (⟨x, hxA⟩ : A) ∈ center A := by
      rw [mem_center_iff]
      intro a
      apply Subtype.ext
      exact (mem_centralizer_iff.mp (hc a.property) x hxH).symm
    have hx1 : (⟨x, hxA⟩ : A) = 1 := by simpa only [hcenter, mem_bot] using hxa
    exact congrArg Subtype.val hx1
  obtain ⟨e, _⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting H A hd
    (le_centralizer_iff.mp hc)
  let f9 : Multiplicative (ZMod 3 × ZMod 3) →* H :=
    eH.symm.toMonoidHom.comp
      ((alternatingGroup.TwoThreeCycles.embedding (n := 6) (by decide)).comp e9Coordinates)
  have hf9 : Function.Injective f9 := eH.symm.injective.comp
    ((alternatingGroup.TwoThreeCycles.embedding_injective (n := 6) (by decide)).comp
      e9Coordinates_injective)
  let f := (H ⊔ A).subtype.comp
    (e.toMonoidHom.comp (f9.prodMap eA.symm.toMonoidHom))
  apply not_quasithin_of_e9_prod_a4_embedding f
  apply (H ⊔ A).subtype_injective.comp
  apply e.injective.comp
  intro a b hab
  exact Prod.ext (hf9 (congrArg Prod.fst hab)) (eA.symm.injective (congrArg Prod.snd hab))

end Theory.Quasithin
