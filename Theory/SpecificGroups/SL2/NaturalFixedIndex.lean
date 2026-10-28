module

public import Theory.Representation.SL2NaturalOffenders.Internal

/-!
# The fixed-point index of a natural SL₂ two-subgroup

A nonidentity two by two matrix fixes at most one field line. Hence the
fixed subgroup in the additive group of F² has index at least |F|. In
characteristic two, each two-subgroup embeds into a Sylow subgroup of order
|F|, giving the actor-order bound without assuming the actor is Sylow.

The fixed subgroup uses the existing matrix action, with the additive carrier
written multiplicatively so finite-group quotient index lemmas apply directly.
This is the model calculation used in Campbell, *Pushing up in Finite Groups*
(1979), Chapter II, the opening of Lemma 4.1, printed p.25. Its group-theoretic
application constructs the actual equivariant section separately.
-/

@[expose] public section

open Matrix Matrix.SpecialLinearGroup

namespace Theory.SpecificGroups.SL2.NaturalFixedIndex
variable {F : Type*} [Field F]
/-- Vectors fixed by the literal natural matrix action of a subgroup. -/
def fixed (B : Subgroup (SpecialLinearGroup (Fin 2) F)) :
    Subgroup (Multiplicative (Fin 2 → F)) where
  carrier := {v | ∀ b ∈ B, b • v.toAdd = v.toAdd}
  one_mem' := by intro b _; exact smul_zero b
  mul_mem' := by
    intro v w hv hw b hb
    change b • (v.toAdd + w.toAdd) = v.toAdd + w.toAdd
    rw [smul_add, hv b hb, hw b hb]
  inv_mem' := by
    intro v hv b hb
    change b • (-v.toAdd) = -v.toAdd
    rw [smul_neg, hv b hb]

variable [Finite F]
/-- A nontrivial subgroup fixes at most one field line. -/
theorem card_fixed_le {B : Subgroup (SpecialLinearGroup (Fin 2) F)} (hB : B ≠ ⊥) :
    Nat.card (fixed B) ≤ Nat.card F := by
  obtain ⟨⟨b, hb⟩, hne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB
  have hM : b.val ≠ 1 := by
    intro he
    exact hne (Subtype.ext (Subtype.ext he))
  let f : fixed B → {v : Fin 2 → F // b.val.mulVec v = v} :=
    fun v => ⟨v.val.toAdd, v.property b hb⟩
  exact (Nat.card_le_card_of_injective f (fun v w h =>
    Subtype.ext (congrArg (fun z : {v : Fin 2 → F // b.val.mulVec v = v} => z.val) h))).trans
    (Representation.SL2NaturalOffenders.fixedVectors_card_le b.val hM)

/-- The fixed subgroup of a nontrivial actor has index at least the field order. -/
theorem field_card_le_fixed_index {B : Subgroup (SpecialLinearGroup (Fin 2) F)}
    (hB : B ≠ ⊥) : Nat.card F ≤ (fixed B).index := by
  have hc : Nat.card (Multiplicative (Fin 2 → F)) = Nat.card F * Nat.card F := by
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin 2 → F) ≃ (Fin 2 → F)),
      Nat.card_fun]
    simp [pow_two]
  have hprod : Nat.card F * Nat.card F ≤ (fixed B).index * Nat.card F := by
    rw [← hc, ← (fixed B).index_mul_card]
    exact Nat.mul_le_mul_left _ (card_fixed_le hB)
  exact Nat.le_of_mul_le_mul_right hprod Nat.card_pos

/-- Every nontrivial two-subgroup has order at most its natural fixed-point index. -/
theorem card_le_fixed_index [CharP F 2]
    {B : Subgroup (SpecialLinearGroup (Fin 2) F)} (hB : B ≠ ⊥)
    (hp : IsPGroup 2 B) : Nat.card B ≤ (fixed B).index := by
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  have hcard : Nat.card B ≤ Nat.card F := by
    calc
      Nat.card B ≤ Nat.card P := Nat.card_le_card_of_injective (Subgroup.inclusion hP) (Subgroup.inclusion_injective hP)
      _ = Nat.card (upperUnipotentSylow F 2) :=
        Nat.card_congr (P.equiv (upperUnipotentSylow F 2)).toEquiv
      _ = Nat.card F := card_upperUnipotent F
  exact hcard.trans (field_card_le_fixed_index hB)
end Theory.SpecificGroups.SL2.NaturalFixedIndex

end
