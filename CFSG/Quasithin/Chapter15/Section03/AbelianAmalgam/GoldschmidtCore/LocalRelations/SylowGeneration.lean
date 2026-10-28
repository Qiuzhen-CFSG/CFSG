module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Basic

/-!
# Reducing terminal Sylow generation to orthogonal geometry

A two-subgroup properly containing the index-two subgroup `T_E` has
order at most that of the ambient Sylow subgroup `T`. The index is
therefore two, so that overgroup normalizes `T_E`. Once the orthogonal
calculation gives `N_M(T_E)≤T`, the overgroup equals `T`. Consequently
`⟨Y_F,T⟩=M` supplies exactly the generation premise consumed by
`GoldschmidtCore.Sylow`. Neither geometric calculation is assumed proved.

The two distinct index-two stabilizers also give the choice of an
element in the definite-plane stabilizer outside `T_E`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
construction preceding 15.3.68 and proof of (3), printed p.1154.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem card_mul_relIndex (D U : Subgroup G) (hDU : D ≤ U) :
    Nat.card D * D.relIndex U = Nat.card U := by
  simpa only [relIndex_bot_left] using
    relIndex_mul_relIndex (⊥ : Subgroup G) D U bot_le hDU

/-- With `N_M(T_E) ≤ T`, every two-subgroup of `M` properly containing
the index-two subgroup `T_E` is exactly the fixed ambient Sylow subgroup.
The proof first forces index two in that overgroup, hence normalization. -/
theorem lineT_two_overgroup_eq (T : Sylow 2 G) (M E : Subgroup G)
    (hi : (lineT (T : Subgroup G) E).relIndex (T : Subgroup G) = 2)
    (hN : M ⊓ normalizer (lineT (T : Subgroup G) E : Set G) ≤ (T : Subgroup G))
    (U : Subgroup G) (hUM : U ≤ M) (hU : IsPGroup 2 U)
    (hDU : lineT (T : Subgroup G) E < U) : U = (T : Subgroup G) := by
  let D := lineT (T : Subgroup G) E
  have hUTcard : Nat.card U ≤ Nat.card (T : Subgroup G) := by
    obtain ⟨P, hUP⟩ := hU.exists_le_sylow
    calc
      Nat.card U ≤ Nat.card (P : Subgroup G) := card_le_of_le hUP
      _ = Nat.card (T : Subgroup G) := by rw [P.card_eq_multiplicity, T.card_eq_multiplicity]
  have hcU := card_mul_relIndex D U hDU.le
  have hcT := card_mul_relIndex D (T : Subgroup G) (show D ≤ (T : Subgroup G) from inf_le_left)
  rw [hi] at hcT
  have hne : D.relIndex U ≠ 1 := fun h => hDU.not_ge (relIndex_eq_one.mp h)
  have hpos : 0 < D.relIndex U :=
    Nat.pos_of_ne_zero (D.subgroupOf U).index_ne_zero_of_finite
  have hiU : D.relIndex U = 2 := by
    have hle : D.relIndex U ≤ 2 := by
      apply Nat.le_of_mul_le_mul_left (c := Nat.card D)
      · rw [hcU, hcT]
        exact hUTcard
      · exact Nat.card_pos
    omega
  have hnorm : U ≤ normalizer (D : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hDU.le).mp (normal_of_index_eq_two hiU)
  have hUT : U ≤ (T : Subgroup G) := (le_inf hUM hnorm).trans hN
  apply eq_of_le_of_card_ge hUT
  rw [← hcU, hiU, hcT]

/-- This discharges the generation premise of `Sylow.lean` from the two
orthogonal-action calculations `N_M(T_E)≤T` and `⟨Y_F,T⟩=M`.
Neither calculation is asserted by this reduction. -/
theorem lineT_generation_of_normalizer (T : Sylow 2 G) (M Y E F : Subgroup G)
    (hi : (lineT (T : Subgroup G) E).relIndex (T : Subgroup G) = 2)
    (hN : M ⊓ normalizer (lineT (T : Subgroup G) E : Set G) ≤ (T : Subgroup G))
    (hgen : M ≤ lineY Y F ⊔ (T : Subgroup G)) :
    ∀ U : Subgroup G, U ≤ M → IsPGroup 2 U → lineT (T : Subgroup G) E < U →
      M ≤ lineY Y F ⊔ U := by
  intro U hUM hU hDU
  rw [lineT_two_overgroup_eq T M E hi hN U hUM hU hDU]
  exact hgen

/-- The distinct index-two stabilizers supplied by 15.3.66(3) give the
source's choice `s ∈ S - T_E`, with the definite-plane stabilizer unchanged. -/
theorem exists_plane_element_outside_lineT (T : Sylow 2 G) (V₁ E : Subgroup G)
    (hS : (planeStabilizer T V₁).relIndex (T : Subgroup G) = 2)
    (hD : (lineT (T : Subgroup G) E).relIndex (T : Subgroup G) = 2)
    (hne : planeStabilizer T V₁ ≠ lineT (T : Subgroup G) E) :
    ∃ s ∈ planeStabilizer T V₁, s ∉ lineT (T : Subgroup G) E := by
  by_contra h
  push Not at h
  apply hne
  apply eq_of_le_of_card_ge h
  have hcS := card_mul_relIndex (planeStabilizer T V₁) (T : Subgroup G)
    (show planeStabilizer T V₁ ≤ (T : Subgroup G) from inf_le_left)
  have hcD := card_mul_relIndex (lineT (T : Subgroup G) E) (T : Subgroup G)
    (show lineT (T : Subgroup G) E ≤ (T : Subgroup G) from inf_le_left)
  rw [hS] at hcS
  rw [hD] at hcD
  omega

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations
