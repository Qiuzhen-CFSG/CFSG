module

public import Stellmacher.LaterDefs
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.SL2Products

/-!
# Self-normalizing order-two subgroups of SL₂(2)

An order-two subgroup has prime index three in SL₂(2), so its normalizer is
either itself or the whole group. The latter case is impossible: a normal
order-two subgroup is central, whereas SL₂(2) has trivial center.
-/

namespace Stellmacher

private theorem normal_le_center_of_card_two
    {G : Type*} [Group G] (U : Subgroup G) [U.Normal]
    (hcard : Nat.card U = 2) : U ≤ Subgroup.center G := by
  obtain ⟨involution, _, hunique⟩ := (Nat.card_eq_two_iff' (1 : U)).mp hcard
  intro element helement
  rw [Subgroup.mem_center_iff]
  intro actor
  by_cases hone : element = 1
  · simp [hone]
  have heq : (⟨element, helement⟩ : U) = involution :=
    hunique _ (fun hh => hone (congrArg Subtype.val hh))
  have hconj : actor * element * actor⁻¹ ∈ U :=
    Subgroup.Normal.conj_mem ‹U.Normal› element helement actor
  have hconj_ne : (⟨actor * element * actor⁻¹, hconj⟩ : U) ≠ 1 := by
    intro hh
    have hhval := congrArg Subtype.val hh
    have : element = 1 := by
      simpa [mul_assoc] using congrArg (fun value => actor⁻¹ * value * actor) hhval
    exact hone this
  have hfixed : actor * element * actor⁻¹ = element :=
    congrArg Subtype.val ((hunique _ hconj_ne).trans heq.symm)
  simpa [mul_assoc] using congrArg (fun value => value * actor) hfixed

/-- Every order-two subgroup of a finite group isomorphic to SL₂(2) is
self-normalizing. -/
public theorem isSL2Two_normalizer_eq_of_card_two
    {G : Type*} [Group G] [Finite G] (hG : IsSL2Two G)
    (U : Subgroup G) (hcard : Nat.card U = 2) :
    Subgroup.normalizer (U : Set G) = U := by
  have hgroupcard := SectionOne.RankOneThreeGroupAssembly.isSL2Two_card hG
  have hindex : U.index = 3 := by
    have hmul := U.card_mul_index
    rw [hcard, hgroupcard] at hmul
    omega
  have hdiv : (Subgroup.normalizer (U : Set G)).index ∣ 3 := by
    rw [← hindex]
    exact Subgroup.index_dvd_of_le U.le_normalizer
  rcases (Nat.dvd_prime Nat.prime_three).mp hdiv with hone | hthree
  · have htop := Subgroup.index_eq_one.mp hone
    let : U.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    have hcentral := normal_le_center_of_card_two U hcard
    rw [SectionOne.RankOneThreeGroupAssembly.center_eq_bot_of_isSL2Two hG] at hcentral
    have hbot : U = ⊥ := le_bot_iff.mp hcentral
    have hcardone := Subgroup.card_eq_one.mpr hbot
    omega
  · apply le_antisymm _ U.le_normalizer
    have hmul := Subgroup.relIndex_mul_index U.le_normalizer
    rw [hthree, hindex] at hmul
    have hrel : U.relIndex (Subgroup.normalizer (U : Set G)) = 1 := by omega
    exact Subgroup.relIndex_eq_one.mp hrel

/-- The transposition subgroups of the concrete SL₂(2) model are self-normalizing. -/
public theorem sl2Two_normalizer_eq_of_card_two
    (U : Subgroup Later.SL2Two) (hcard : Nat.card U = 2) :
    Subgroup.normalizer (U : Set Later.SL2Two) = U :=
  isSL2Two_normalizer_eq_of_card_two ⟨MulEquiv.refl _⟩ U hcard

end Stellmacher
