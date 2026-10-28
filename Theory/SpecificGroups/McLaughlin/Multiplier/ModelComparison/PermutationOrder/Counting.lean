module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.McL
public import Theory.GroupTheory.WordSubgroup

/-!
# Counting the prefix stabilizers of the literal McL carrier

Multiplication embeds a family of representatives with distinct images of a
base letter times its next stabilizer into the current stabilizer. Inductively,
this converts the finite word certificates into a lower bound for the actual
generated subgroup. There is no closure or exhaustiveness premise on the
representatives.

The concrete base is `[0, 1, 2, 3, 4, 5]` in the ATLAS `McLG1-p275B0`
representation, with the inverse-source convention of `McL.lean`.
-/

@[expose] public section
open Theory.GroupTheory Sporadic.LeechRelated.McL

namespace Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison.PermutationOrder


/-- Exhaustive checking with a linear Boolean traversal of the finite domain. -/
def checkFin {n : Nat} (f : Fin n → Bool) : Bool :=
  (List.range n).all (fun i => if h : i < n then f ⟨i, h⟩ else true)

theorem allFin {n : Nat} (P : Fin n → Prop) [DecidablePred P]
    (h : checkFin (fun i => decide (P i)) = true) : ∀ i, P i := by
  intro i
  have hi := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
  simpa only [dif_pos i.isLt, decide_eq_true_eq] using hi

/-- The literal carrier restricted to permutations fixing the first `k` letters. -/
def stabilizer (k : Nat) : Subgroup (Equiv.Perm (Fin 275)) where
  carrier := {g | g ∈ generated ∧ ∀ i : Fin 275, i.val < k → g i = i}
  one_mem' := ⟨generated.one_mem, fun _ _ => rfl⟩
  mul_mem' := by
    rintro g h ⟨hg, hgf⟩ ⟨hh, hhf⟩
    exact ⟨generated.mul_mem hg hh, fun i hi => by
      rw [Equiv.Perm.mul_apply, hhf i hi, hgf i hi]⟩
  inv_mem' := by
    rintro g ⟨hg, hgf⟩
    refine ⟨generated.inv_mem hg, fun i hi => ?_⟩
    apply g.injective
    change g (g.symm i) = g i
    rw [g.apply_symm_apply, hgf i hi]

theorem stabilizer_zero : stabilizer 0 = generated := by
  ext g
  simp [stabilizer]

theorem stabilizer_succ_le (k : Nat) : stabilizer (k + 1) ≤ stabilizer k := by
  rintro g ⟨hg, hf⟩
  exact ⟨hg, fun i hi => hf i (Nat.lt_succ_of_lt hi)⟩

theorem word_mem {n : Nat} (gen : Fin n → Equiv.Perm (Fin 275))
    (H : Subgroup (Equiv.Perm (Fin 275))) (hgen : ∀ i, gen i ∈ H)
    (w : List (Fin n)) : evalWord gen w ∈ H := by
  induction w with
  | nil => exact H.one_mem
  | cons i w ih => exact H.mul_mem (hgen i) ih

/-- Distinct images of the next base letter separate cosets of its stabilizer. -/
theorem orbit_mul_card_le {m k : Nat} (hk : k < 275)
    (rep : Fin m → Equiv.Perm (Fin 275))
    (hmem : ∀ r, rep r ∈ stabilizer k)
    (hinj : Function.Injective (fun r => rep r ⟨k, hk⟩)) :
    m * Nat.card (stabilizer (k + 1)) ≤ Nat.card (stabilizer k) := by
  let f : Fin m × stabilizer (k + 1) → stabilizer k := fun x =>
    ⟨rep x.1 * x.2.val,
      (stabilizer k).mul_mem (hmem x.1) (stabilizer_succ_le k x.2.property)⟩
  have hf : Function.Injective f := by
    rintro ⟨r, g⟩ ⟨s, h⟩ heq
    have he : rep r * g.val = rep s * h.val := congrArg Subtype.val heq
    have hrs : r = s := by
      apply hinj
      have he' := congrArg (fun p : Equiv.Perm (Fin 275) => p ⟨k, hk⟩) he
      simpa only [Equiv.Perm.mul_apply,
        g.property.2 ⟨k, hk⟩ (Nat.lt_succ_self k),
        h.property.2 ⟨k, hk⟩ (Nat.lt_succ_self k)] using he'
    subst s
    exact Prod.ext rfl (Subtype.ext (mul_left_cancel he))
  simpa only [Nat.card_prod, Nat.card_fin] using Nat.card_le_card_of_injective f hf

end Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison.PermutationOrder
