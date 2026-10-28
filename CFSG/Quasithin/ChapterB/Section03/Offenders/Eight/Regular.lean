module

public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Regular.Fixed
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Regular.Involutions
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Regular.Planes

/-!
# Regular elementary eight offenders

Every subgroup of a regular elementary eight group is trivial, has order two
or four, or equals the whole group. The natural fixed dimensions four and
three for the two proper nontrivial orders imply bestness: each proper
nontrivial subgroup has weight five, while the whole group and the trivial
subgroup have weight six. The affine-function calculations in the imported
modules establish these dimensions and discharge the bestness comparison
for every subgroup, including the trivial subgroup.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Proposition B.3.2(3),(6), printed pp.83–84.
-/

public section

open BinaryPermutation Representation.BinaryOffender

namespace CFSG.Quasithin.ChapterB.Offenders
/-- Every proper nontrivial subgroup of a regular eight group has order two or four. -/
theorem regularEight_subgroup_cases {A : Subgroup (Equiv.Perm (Fin 8))}
    (hA : IsRegularEight A) (B : Subgroup (Equiv.Perm (Fin 8))) (hBA : B ≤ A) :
    B = ⊥ ∨ (Nat.card B = 2 ∧ rank B = 1) ∨
      (Nat.card B = 4 ∧ rank B = 2) ∨ B = A := by
  by_cases hB : B = ⊥
  · exact Or.inl hB
  have hEB := hA.1.of_le hBA hB
  have hpos := hEB.rank_pos
  have hbound : rank B ≤ 3 := by
    calc
      rank B = Nat.log 2 (Nat.card B) := rfl
      _ ≤ Nat.log 2 (Nat.card A) := Nat.log_monotone (Subgroup.card_le_of_le hBA)
      _ = 3 := rank_eq_three_of_isRegularEight hA
  have hcases : rank B = 1 ∨ rank B = 2 ∨ rank B = 3 := by omega
  rcases hcases with hr | hr | hr
  · exact Or.inr (Or.inl ⟨by simpa [hr] using hEB.card_eq_two_pow_rank, hr⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨by simpa [hr] using hEB.card_eq_two_pow_rank, hr⟩))
  · apply Or.inr; apply Or.inr; apply Or.inr
    apply Subgroup.eq_of_le_of_card_ge hBA
    rw [hA.2.1, hEB.card_eq_two_pow_rank, hr]
    decide

/-- The proper-subgroup dimension calculations suffice for bestness. The regular
fixed dimension is proved independently, and the trivial subgroup is included. -/
theorem regularEight_best_of_proper_fixed_dimensions
    {A : Subgroup (Equiv.Perm (Fin 8))} (hA : IsRegularEight A)
    (htwo : ∀ B ≤ A, Nat.card B = 2 →
      Module.finrank (ZMod 2) (fixedSpace (naturalRepresentation (Fin 8)) B) = 4)
    (hfour : ∀ B ≤ A, Nat.card B = 4 →
      Module.finrank (ZMod 2) (fixedSpace (naturalRepresentation (Fin 8)) B) = 3) :
    IsBestOffender (naturalRepresentation (Fin 8)) A := by
  refine ⟨hA.1, ?_⟩
  intro B hBA
  have hweight : weight (naturalRepresentation (Fin 8)) A = 6 := by
    rw [weight, regularEight_rank_three hA, fixedSpace_natural_regularEight_finrank hA]
  rw [hweight]
  rcases regularEight_subgroup_cases hA B hBA with rfl | ⟨hcard, hr⟩ | ⟨hcard, hr⟩ | rfl
  · rw [weight_bot]
    simpa using le_of_eq (finrank_natural_even (Fin 8) (by decide : Even 8))
  · rw [weight, hr, htwo B hBA hcard]
    decide
  · rw [weight, hr, hfour B hBA hcard]
    decide
  · exact hweight.le

/-- An order-four subgroup of a regular elementary eight group has natural
fixed codimension three. -/
theorem fixedCodim_natural_regularEight_four
    {A B : Subgroup (Equiv.Perm (Fin 8))}
    (hA : IsRegularEight A) (hBA : B ≤ A) (hB : Nat.card B = 4) :
    fixedCodim (naturalRepresentation (Fin 8)) B = 3 := by
  apply fixedCodim_eq_of_finrank_fixedSpace _ B (d := 6) (k := 3)
  · simpa using finrank_natural_even (Fin 8) (by decide : Even 8)
  · exact fixedSpace_natural_regularEight_four_finrank hA hBA hB

/-- The regular elementary eight groups belong to the best-offender family
on the natural module, as asserted in B.3.2(6). -/
theorem isBestOffender_natural_regularEight
    {A : Subgroup (Equiv.Perm (Fin 8))} (hA : IsRegularEight A) :
    IsBestOffender (naturalRepresentation (Fin 8)) A :=
  regularEight_best_of_proper_fixed_dimensions hA
    (fun _ hBA hB => fixedSpace_natural_regularEight_orderTwo_finrank hA hBA hB)
    (fun _ hBA hB => fixedSpace_natural_regularEight_four_finrank hA hBA hB)

end CFSG.Quasithin.ChapterB.Offenders
