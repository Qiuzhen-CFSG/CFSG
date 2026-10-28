module
public import Theory.Representation.SL2.TwoSubgroupFixedIndex
public import Theory.Representation.BinaryOffender.FaithfulRankOne

/-!
# The DGS size bound for every binary SL₂ actor

Every nontrivial two-subgroup of SL₂(F) moves at least the binary degree of F
in a faithful representation. Its order is at most the Sylow order |F|, giving
|A| ≤ |V/C_V(A)|. At field order two, faithfulness gives the needed positive
codimension directly. Thus the strict DGS inequality also forces |F| < |A|².

This proves the SL₂ branch of DGS85 (5.12)(a), printed p.113, and the large-actor
step on p.114, for arbitrary positive field degree and arbitrary subgroups of
the prescribed Sylow. These estimates do not require quadraticity or the
corrected fixed-space generation condition. Recognition for a proper actor
still requires additional arguments.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender
open scoped MatrixGroups
namespace Representation.RankOne.QuadraticRecognition
variable {F V : Type*} [Field F] [Finite F] [CharP F 2]
  [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

local instance finiteSl2ActorQuotient (C : Submodule (ZMod 2) V) : Finite (V ⧸ C) :=
  Finite.of_surjective _ C.mkQ_surjective

/-- A nontrivial actor moves at least one full field degree. -/
theorem sl2_actor_field_bound (ρ : Representation (ZMod 2) SL(2,F) V)
    (hf : Function.Injective ρ) (S : Sylow 2 SL(2,F))
    (A : Subgroup SL(2,F)) (hAS : A ≤ S) (hA : A ≠ ⊥)
    {n : ℕ} (hF : Nat.card F = 2^n) :
    Nat.card F ≤ Nat.card (V ⧸ fixedSpace ρ A) := by
  have hd : n ≤ fixedCodim ρ A := by
    by_cases hn : 1 < n
    · obtain ⟨a,ha,ha1⟩ := A.bot_or_exists_ne_one.resolve_left hA
      have hnt : ∃ g, ρ g ≠ 1 := ⟨a,fun he => ha1 (hf (he.trans ρ.map_one.symm))⟩
      exact SL2.two_subgroup_fixedCodim_lower ρ hnt hn hF A
        (S.isPGroup'.of_injective (Subgroup.inclusion hAS) (Subgroup.inclusion_injective hAS)) hA
    · have hp := fixedCodim_pos_of_faithful ρ hf hA
      omega
  rw [hF,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  exact Nat.pow_le_pow_right (by decide) hd

/-- DGS (5.12)(a) for all binary SL₂ actors, including the trivial actor. -/
theorem sl2_actor_bound (ρ : Representation (ZMod 2) SL(2,F) V)
    (hf : Function.Injective ρ) (S : Sylow 2 SL(2,F))
    (A : Subgroup SL(2,F)) (hAS : A ≤ S)
    {n : ℕ} (hF : Nat.card F = 2^n) :
    Nat.card A ≤ Nat.card (V ⧸ fixedSpace ρ A) := by
  by_cases hA : A = ⊥
  · rw [hA,card_bot]
    exact Nat.card_pos
  have hS : Nat.card S = Nat.card F := Nat.card_congr
    (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 S).symm.toEquiv
  have hcard := Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hAS)
  rw [hS] at hcard
  exact hcard.trans (sl2_actor_field_bound ρ hf S A hAS hA hF)

/-- The strict recognition branch forces the source large-actor inequality. -/
theorem sl2_strict_actor_large (ρ : Representation (ZMod 2) SL(2,F) V)
    (hf : Function.Injective ρ) (S : Sylow 2 SL(2,F))
    (A : Subgroup SL(2,F)) (hAS : A ≤ S)
    {n : ℕ} (hF : Nat.card F = 2^n)
    (hstrict : Nat.card (V ⧸ fixedSpace ρ A) < Nat.card A ^ 2) :
    Nat.card F < Nat.card A ^ 2 := by
  have hA : A ≠ ⊥ := by
    intro h
    rw [h,card_bot,one_pow] at hstrict
    have hp : 0 < Nat.card (V ⧸ fixedSpace ρ ⊥) := Nat.card_pos
    omega
  exact (sl2_actor_field_bound ρ hf S A hAS hA hF).trans_lt hstrict
end Representation.RankOne.QuadraticRecognition
