module

public import Theory.SpecificGroups.MacWilliams.HallJankoCenter
public import Stellmacher.Recognition.SimpleInvolutionFusion

/-!
# Central involution setup for the Hall–Janko Sylow branch

The concrete seven-generator presentation has center of order two. Transporting
this calculation to an ambient Sylow subgroup gives a unique central involution.
In a nonsolvable finite simple group this involution has a distinct conjugate
in the Sylow subgroup, by the existing Z-star consequence.

These are the initial inputs to the Hall–Janko branch of Janko–Thompson,
Math. Z. 113 (1970), Theorem 1.5, printed p.386. The further assertion that
an involution centralizer is nonsolvable requires the ambient argument of
Gorenstein–Harada, cited there as reference [7]. It is not a consequence of
the order and center calculations proved here.
-/

namespace Stellmacher.Recognition.NormalEightHallJankoCentralizer

open Subgroup MacWilliamsSylow

/-- The Sylow model determines the order and the center order. -/
public theorem sylow_card_and_center_card
    {G : Type*} [Group G] (S : Sylow 2 G)
    (hmodel : Nonempty (S ≃* HallJankoSylow)) :
    Nat.card S = 128 ∧ Nat.card (center S) = 2 := by
  obtain ⟨e⟩ := hmodel
  exact ⟨(Nat.card_congr e.toEquiv).trans hallJankoSylow_card,
    (Nat.card_congr (centerCongr e).toEquiv).trans hallJankoSylow_center_card⟩

/-- There is exactly one central involution in the specified Sylow subgroup. -/
public theorem exists_unique_central_involution
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hmodel : Nonempty (S ≃* HallJankoSylow)) :
    ∃! z : S, z ∈ center S ∧ orderOf z = 2 := by
  have hc := (sylow_card_and_center_card S hmodel).2
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card'
    (G := center S) 2 (by rw [hc])
  refine ⟨z, ⟨z.property, (orderOf_coe z).trans hz⟩, ?_⟩
  intro t ht
  obtain ⟨w, _, hw⟩ := (Nat.card_eq_two_iff' (1 : center S)).mp hc
  have htne : (⟨t, ht.1⟩ : center S) ≠ 1 := by
    intro h
    have hone : t = 1 := congrArg Subtype.val h
    simp [hone] at ht
  have hzne : z ≠ 1 := by
    intro h
    simp [h] at hz
  exact congrArg Subtype.val ((hw _ htne).trans (hw z hzne).symm)

/-- The central involution is not weakly closed in an ambient nonsolvable
finite simple group. This gives the initial fusion required by recognition. -/
public theorem exists_central_involution_and_distinct_conjugate
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G)
    (hmodel : Nonempty (S ≃* HallJankoSylow)) :
    ∃ z t : S, z ∈ center S ∧ orderOf z = 2 ∧ t ≠ z ∧
      IsConj (z : G) (t : G) := by
  obtain ⟨z, hz, _⟩ := exists_unique_central_involution S hmodel
  obtain ⟨t, ht, hzt⟩ := exists_distinct_isConj_in_sylow hns S z hz.2
  exact ⟨z, t, hz.1, hz.2, ht, hzt⟩

end Stellmacher.Recognition.NormalEightHallJankoCentralizer
