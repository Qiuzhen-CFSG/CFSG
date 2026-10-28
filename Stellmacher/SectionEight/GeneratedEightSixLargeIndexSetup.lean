module

public import Stellmacher.SectionEight.GeneratedEightSixNeighborObstruction

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven

universe u

public theorem eight_six_index_ge_four_of_not_le
    {G : Type u} [Group G] [Finite G]
    (A D : Subgroup G) (htwo : IsPGroup 2 A)
    (hnotle : ¬ A ≤ D) (hindex : ¬ QuotientCardEq A (A ⊓ D) 2) :
    4 ≤ (A ⊓ D).relIndex A ∧ 4 * Nat.card (A ⊓ D : Subgroup G) ≤ Nat.card A := by
  have hcard : (A ⊓ D).relIndex A * Nat.card (A ⊓ D : Subgroup G) = Nat.card A := by
    have heq := ((A ⊓ D).subgroupOf A).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show A ⊓ D ≤ A from inf_le_left)).toEquiv] at heq
    exact heq
  have hneone : (A ⊓ D).relIndex A ≠ 1 := by
    intro heq
    exact hnotle (((Subgroup.relIndex_eq_one.mp heq).trans inf_le_right))
  have hnetwo : (A ⊓ D).relIndex A ≠ 2 := by
    intro heq
    apply hindex
    exact (heq ▸ hcard).symm
  obtain ⟨exponent, hpower⟩ := htwo.exists_card_eq
  obtain ⟨indexExponent, _, hindexPower⟩ :=
    (Nat.dvd_prime_pow Nat.prime_two).mp
      (hpower ▸ (A ⊓ D).relIndex_dvd_card (K := A))
  have hexponent : 2 ≤ indexExponent := by
    by_contra hsmall
    have hcases : indexExponent = 0 ∨ indexExponent = 1 := by omega
    rcases hcases with hzero | hone
    · exact hneone (by simpa [hzero] using hindexPower)
    · exact hnetwo (by simpa [hone] using hindexPower)
  have hfour : 4 ≤ (A ⊓ D).relIndex A := by
    rw [hindexPower]
    exact (show (2 : ℕ) ^ 2 ≤ 2 ^ indexExponent from
      Nat.pow_le_pow_right (by decide) hexponent)
  exact ⟨hfour, (Nat.mul_le_mul_right (Nat.card (A ⊓ D : Subgroup G)) hfour).trans_eq hcard⟩

public theorem generated_eight_six_index_ge_four_of_not_le
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : GeneratedSectionEightContext H S0 S P1 P2)
    (previous : ctx.Γ.Vertex) (D : Subgroup (P1 ⊔ P2 : Subgroup H))
    (hnotle : ¬ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a ≤ D)
    (hindex : ¬ QuotientCardEq
      (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a)
      ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊓ D) 2) :
    4 ≤ ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊓ D).relIndex
      (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ∧
    4 * Nat.card ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊓ D :
      Subgroup (P1 ⊔ P2 : Subgroup H)) ≤
      Nat.card (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a :
        Subgroup (P1 ⊔ P2 : Subgroup H)) := by
  have hcore : IsPGroup 2 (QAt ctx.Γ ctx.criticalPath.a) := by
    change IsPGroup 2 (ctx.Γ.twoCoreAt ctx.criticalPath.a)
    rw [ctx.Γ.twoCoreAt_def]
    exact (pCore_isPGroup (p := 2)).map _
  exact eight_six_index_ge_four_of_not_le _ D (hcore.to_le inf_le_right) hnotle hindex

public theorem generated_eight_six_bad_local_of_normalizer_alternative
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : GeneratedSectionEightContext H S0 S P1 P2)
    (hlength : ctx.criticalPath.length = 2)
    (halternative :
      (∃ W : Subgroup (P1 ⊔ P2 : Subgroup H),
        IsElementaryAbelianSubgroup 2 W ∧ Nat.card W = 2 ^ 4 ∧
          IsNonsolvableNormalizer W) ∨
      (∃ vertex : ctx.Γ.Vertex,
        vertex ∈ Neighborhood ctx.Γ ctx.criticalPath.firstStep ∧
        QuotientIsModel
          (Subgroup.normalizer
            ((ZAt ctx.Γ vertex ⊔ ZAt ctx.Γ ctx.criticalPath.a :
              Subgroup (P1 ⊔ P2 : Subgroup H)) : Set (P1 ⊔ P2 : Subgroup H)))
          (Subgroup.centralizer
            ((ZAt ctx.Γ vertex ⊔ ZAt ctx.Γ ctx.criticalPath.a :
              Subgroup (P1 ⊔ P2 : Subgroup H)) : Set (P1 ⊔ P2 : Subgroup H))) L3Two)) :
    ∃ U : Subgroup H, IsTwoLocal U ∧ ¬ Group.IsSolvable U := by
  rcases halternative with ⟨W, helementary, hcard, hbad⟩ | ⟨vertex, hneighbor, hmodel⟩
  · exact ambient_bad_local_of_elementary_sixteen_normalizer
      (P1 ⊔ P2).subtype (P1 ⊔ P2).subtype_injective W helementary hcard hbad
  · exact generated_eight_six_bad_local_of_neighbor_quotient ctx
      (by omega) vertex hneighbor hmodel

end Stellmacher.SectionEight
