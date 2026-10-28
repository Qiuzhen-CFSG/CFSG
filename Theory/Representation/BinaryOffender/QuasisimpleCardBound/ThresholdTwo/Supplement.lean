module

public import Theory.Representation.BinaryOffender.QuasisimpleCardBound.ThresholdTwo
public import Theory.Representation.BinaryOffender.QuasisimpleNormalizer
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Threshold-two bounds for a linear-normalizer supplement

The literal join of the action image and the chosen normalizer actor is
faithful and irreducible. The same actor has the same fixed space there, so
threshold-two maximization bounds |V| by the square of this join's order.
Normalization bounds that order by the product of the two factor orders.

Source: Guralnick–Malle, Classification of 2F-modules II, §2.1 Lemma 2.1
and the order estimate in §3.5, equation (3.3).
-/

public section
namespace Representation.BinaryOffender.QuasisimpleNormalizer
open Subgroup
variable {L V : Type*} [Group L] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (σ : Representation (ZMod 2) L V)

/-- The actual supplement has order at most the product of its two factors. -/
theorem card_supplement_le (A : Subgroup (linearNormalizer σ)) :
    Nat.card (supplement σ A) ≤ Nat.card (actionImage σ) * Nat.card A := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (Module.End (ZMod 2) V) := Finite.of_injective
    (fun f : Module.End (ZMod 2) V => (f : V → V)) DFunLike.coe_injective
  have hn : A.map (linearNormalizer σ).subtype ≤
      normalizer (actionImage σ : Set (Module.End (ZMod 2) V)ˣ) := by
    rintro x ⟨a, _, rfl⟩
    exact a.property
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes
    (actionImage σ) (A.map (linearNormalizer σ).subtype) hn
  have hp : 1 ≤ Nat.card (actionImage σ ⊓ A.map (linearNormalizer σ).subtype :
      Subgroup (Module.End (ZMod 2) V)ˣ) := Nat.card_pos
  have hb := Nat.mul_le_mul_right (Nat.card (supplement σ A)) hp
  rw [one_mul, supplement, ← hc, Subgroup.card_map_of_injective (linearNormalizer σ).subtype_injective] at hb
  exact hb

/-- A threshold-two actor in the normalizer remains such an actor in its actual
supplement, whose tautological action is faithful and irreducible. -/
theorem card_le_supplement_sq_of_small_actor [IsIrreducible σ]
    (A : Subgroup (linearNormalizer σ)) (hA : IsElementaryTwo A)
    (hsmall : fixedCodim (normalizerRepresentation σ) A ≤ 2 * rank A) :
    Nat.card V ≤ Nat.card (supplement σ A) ^ 2 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsElementaryAbelian 2 A := hA.2
  let B := A.map (linearNormalizer σ).subtype
  have hB : IsElementaryTwo B := ⟨fun hz =>
    hA.1 ((A.map_eq_bot_iff_of_injective (linearNormalizer σ).subtype_injective).mp hz),
    IsElementaryAbelian.map _⟩
  let : IsElementaryAbelian 2 B := hB.2
  have hBH : B ≤ supplement σ A := le_sup_right
  have hC : IsElementaryTwo (B.subgroupOf (supplement σ A)) := by
    refine ⟨?_, IsElementaryAbelian.subgroupOf hBH⟩
    intro hz
    exact hB.1 (by rw [← map_subgroupOf_eq_of_le hBH, hz, Subgroup.map_bot])
  have hr : rank (B.subgroupOf (supplement σ A)) = rank A := by
    rw [rank_subgroupOf hBH, rank_map_injective _ (linearNormalizer σ).subtype_injective]
  have hd : fixedCodim (linearAction (supplement σ A))
      (B.subgroupOf (supplement σ A)) = fixedCodim (normalizerRepresentation σ) A := by
    change fixedCodim (((Units.coeHom _) : Representation (ZMod 2)
      (Module.End (ZMod 2) V)ˣ V).comp (supplement σ A).subtype) _ = _
    rw [fixedCodim_subgroupOf _ hBH]
    unfold fixedCodim normalizerRepresentation
    rw [fixedSpace_comp_map]
  let := supplement_finite σ A
  let := supplement_irreducible σ A
  apply ThresholdTwoCardBound.card_le_group_sq_of_small_actor
    (linearAction (supplement σ A)) (linearAction_injective _) hC
  rwa [hd, hr]

end Representation.BinaryOffender.QuasisimpleNormalizer
