module

public import Theory.GroupTheory.ElementarySixtyFourPrimeCores
public import Theory.GroupTheory.ElementarySixtyFourThreeRank
public import Theory.GroupTheory.PGroup.ThreeGroupSmallAutomorphisms

/-!
# No five-automorphisms of binary six-dimensional three-subgroups

A three-subgroup A of the automorphism group of an elementary binary group
of order at most 64 has order at most 81, by the order of GL(6,2). An
automorphism of order five would force A to be elementary abelian of order
81, using orbit counting and the coprime Frattini-action theorem. The
binary rank exclusion rules out this remaining case. No solvability
hypothesis is needed.

This assembles the general-linear order bound in `ElementarySixtyFourPrimeCores`,
the Burnside basis-kernel argument in `PGroup.ThreeGroupSmallAutomorphisms`,
and the coprime fixed-factor argument in `ElementarySixtyFourThreeRank`.
-/

/-- A three-subgroup in binary dimension at most six has no automorphism of order five. -/
public theorem not_five_dvd_card_mulAut_three_subgroup_of_elementary_card_le_sixtyfour
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E ≤ 64) (A : Subgroup (MulAut E)) (hA : IsPGroup 3 A) :
    ¬ 5 ∣ Nat.card (MulAut A) := by
  obtain ⟨n, hn⟩ := hA.exists_card_eq
  have hdiv : 3 ^ n ∣ 20158709760 := by
    rw [← hn]
    exact A.card_subgroup_dvd_card.trans
      (card_mulAut_dvd_of_elementary_card_le_sixtyfour hE)
  have hnle : n ≤ 4 := by
    by_contra! hh
    have hbad : 243 ∣ 20158709760 := (pow_dvd_pow 3 hh).trans hdiv
    norm_num at hbad
  have hbound : Nat.card A ≤ 81 := by
    rw [hn]
    exact Nat.pow_le_pow_right (by decide : 0 < 3) hnle
  intro hfive
  obtain ⟨hcard, helementary⟩ :=
    elementary_three_of_card_le_eightyone_of_five_dvd_card_mulAut hA hbound hfive
  let : IsElementaryAbelian 3 A := helementary
  exact not_card_eightyone_elementary_three_subgroup_binary_le_sixtyfour hE A hcard
