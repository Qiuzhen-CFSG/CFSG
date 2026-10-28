module

public import Theory.GroupTheory.C4SquareInvertingCharacteristic
public import Theory.ElementaryAbelian.Basic

/-!
# Elementary eights crossing a C₄-square base

An elementary eight in a group of order 32 meets any C₄ × C₄ subgroup
of order 16 in a four-group. The base has only four elements of square one,
so the eight crosses its index-two coset. Restricting that index gives the
intersection order. This is the elementary plane in generalized-dihedral
core geometry, independently of a choice of inverter.

Source: the initial-core geometry in Stellmacher (8.6)(a),
`refs/latex/stellmacher-n-group.tex`.
-/

namespace Subgroup

/-- The intersection of an elementary eight with an index-two C₄-square
base in an order-32 subgroup has order four. -/
public theorem c4_square_intersection_elementary_eight_card
    {G : Type*} [Group G] [Finite G] (A Q U : Subgroup G)
    (hA : Nonempty (A ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 4)))
    (hAQ : A ≤ Q) (hQ : Nat.card Q = 32)
    [IsElementaryAbelian 2 U] (hU : Nat.card U = 8) (hUQ : U ≤ Q) :
    Nat.card (A.subgroupOf U) = 4 := by
  obtain ⟨e⟩ := hA
  have hAc : Nat.card A = 16 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod]
    norm_num
  have hi : (A.subgroupOf Q).index = 2 := by
    have h := (A.subgroupOf Q).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hAQ).toEquiv, hAc, hQ] at h
    omega
  have hn : ¬ U ≤ A := by
    intro hle
    let f : U → {a : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) // a ^ 2 = 1} :=
      fun u => ⟨e ⟨u, hle u.property⟩, by
        rw [← map_pow]
        have hu : (⟨u, hle u.property⟩ : A) ^ 2 = 1 :=
          Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (u : G) u.property)
        rw [hu, map_one]⟩
    have hf : Function.Injective f := by
      intro u v huv
      exact Subtype.ext (congrArg (fun a : A => (a : G))
        (e.injective (congrArg Subtype.val huv)))
    have hbound := Nat.card_le_card_of_injective f hf
    have hfour : Nat.card {a : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) //
        a ^ 2 = 1} = 4 := by
      rw [Nat.card_eq_fintype_card]
      decide
    rw [hU, hfour] at hbound
    omega
  have hiU : (A.subgroupOf U).index = 2 := by
    have h := subgroupOf_index_eq_two (A.subgroupOf Q) (U.subgroupOf Q) hi (by
      intro hle
      exact hn (fun u hu => hle (show (⟨u, hUQ hu⟩ : Q) ∈ U.subgroupOf Q from hu)))
    change (A.subgroupOf Q).relIndex (U.subgroupOf Q) = 2 at h
    rwa [relIndex_subgroupOf hUQ] at h
  have h := (A.subgroupOf U).card_mul_index
  rw [hiU, hU] at h
  omega

end Subgroup
