module

public import Theory.Representation.BinaryOffender.CubicRatio
public import Theory.Representation.BinaryOffender.EndFieldTransfer

/-!
# The squared offender inequality over the endomorphism field

For an elementary binary actor, codimension at most a times its rank is
equivalent to |V| ≤ |A|^a |C_V(A)|. The change to the commuting endomorphism
field preserves the cardinalities, the group and the chosen actor. In
particular cubic ratio at most two gives the precise 2F inequality used by
Guralnick--Malle, Classification of 2F-modules I, (1.1), manuscript p.1.
This retains the exponent two, separately from the existing FF transport.
-/

public section
namespace Representation.BinaryOffender
open scoped ENNReal
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The cardinality formulation with its exact exponent. -/
theorem fixedCodim_le_mul_rank_iff_card_pow (A : Subgroup G)
    (hA : IsElementaryTwo A) (a : ℕ) :
    fixedCodim ρ A ≤ a * rank A ↔
      Nat.card V ≤ Nat.card A ^ a * Nat.card (fixedSpace ρ A) := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V),
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedSpace ρ A),
    Nat.card_zmod, hA.card_eq_two_pow_rank, ← pow_mul, ← pow_add,
    Nat.pow_le_pow_iff_right (by decide : 1 < 2), Nat.mul_comm (rank A) a]
  have hd := fixedCodim_add_finrank ρ A
  omega

/-- The cubic infimum is attained by a subgroup satisfying the same cardinal bound. -/
theorem cubicRatio_le_nat_iff_card_pow (a : ℕ) :
    cubicRatio ρ ≤ (a : ℝ≥0∞) ↔
      ∃ A, IsElementaryTwo A ∧ IsCubic ρ A ∧
        Nat.card V ≤ Nat.card A ^ a * Nat.card (fixedSpace ρ A) := by
  rw [cubicRatio_le_nat_iff]
  constructor
  · rintro ⟨A, hA, hc, hd⟩
    exact ⟨A, hA, hc, (fixedCodim_le_mul_rank_iff_card_pow ρ A hA a).mp hd⟩
  · rintro ⟨A, hA, hc, hd⟩
    exact ⟨A, hA, hc, (fixedCodim_le_mul_rank_iff_card_pow ρ A hA a).mpr hd⟩

/-- A cubic 2F actor is retained literally on passage to the Schur field. -/
theorem exists_endField_twoF_actor [IsIrreducible ρ]
    (hq : cubicRatio ρ ≤ 2) :
    ∃ A, IsElementaryTwo A ∧ IsCubic ρ A ∧
      Nat.card ρ.asModule ≤ Nat.card A ^ 2 *
        Nat.card (invariants (ρ.endFieldRep.comp A.subtype)) := by
  obtain ⟨A, hA, hc, hd⟩ := (cubicRatio_le_nat_iff_card_pow ρ 2).mp hq
  refine ⟨A, hA, hc, ?_⟩
  rw [Nat.card_congr ρ.asModuleEquiv.toEquiv, EndFieldTransfer.card_invariants]
  exact hd

end Representation.BinaryOffender
