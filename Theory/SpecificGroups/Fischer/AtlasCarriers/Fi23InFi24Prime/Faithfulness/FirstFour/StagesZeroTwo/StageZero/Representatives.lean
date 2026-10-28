module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesZeroTwo.StageZero.Checks
public import Theory.GroupTheory.CosetWordCertificate

/-!
# Word-defined representatives for the first model stage

The right words of the checked defining tree are inverted to obtain left
representatives. Induction on the tree proves their values at the actual base
point. The checked nonroot labels then prove that every representative returning
to that base is the identity. Defining edges give genuine permutation equalities.

This proves the representative and separation parts of a positive Schreier
table, without asserting the remaining transition factors. In particular, no
faithfulness or smaller-orbit equality is used. Source: ATLAS F24G1-p306936B0,
GLS3 Table 5.3v and `source/representatives.py`.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesZeroTwo.StageZero
open Subgroup.CosetWordCertificate

/-- Actual positive right words, compatible with `CosetWordCertificate`. -/
def definitions : Definitions (Fin 2) where
  parent := parent
  letter j := (letter j, true)
  parent_lt := parent_lt

/-- Inverting a right word gives the required left representative. -/
def representativeNat (j : Nat) : Equiv.Perm (Fin 306936) :=
  (definitions.repr (generators 0) j)⁻¹

def representative (j : Fin 31671) : Equiv.Perm (Fin 306936) :=
  representativeNat j.val

def labelPoint (j : Nat) : Fin 306936 :=
  ⟨label j, Nat.mod_lt _ (by decide)⟩

theorem representativeNat_zero : representativeNat 0 = 1 := by
  simp only [representativeNat, Definitions.repr_zero, inv_one]

theorem representative_zero : representative 0 = 1 := representativeNat_zero

/-- The defining edges are full ambient permutation equalities. -/
theorem representativeNat_step (j : Nat) (hj : j ≠ 0) :
    representativeNat j = (generators 0 (letter j))⁻¹ * representativeNat (parent j) := by
  have h := congrArg Inv.inv (definitions.repr_edge (generators 0) j hj)
  simpa only [eval_letter, definitions, ite_true, mul_inv_rev, representativeNat] using h.symm

private theorem val_inverse_generator (a : Fin 2) (x : Fin 306936) :
    ((generators 0 a)⁻¹ x).val =
      if a = 0 then rawA x.val else rawB (rawB x.val) := by
  fin_cases a <;> rfl

/-- The checked numeric edge uses the same inverse-action convention. -/
theorem labelPoint_step (j : Nat) (hj : j < 31671) (hj0 : j ≠ 0) :
    (generators 0 (letter j))⁻¹ (labelPoint (parent j)) = labelPoint j := by
  have h := treeCheck_eq_true j hj
  simp only [treeCheck, if_neg hj0, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h
  apply Fin.ext
  rw [val_inverse_generator]
  exact h.1.2

/-- Tree induction evaluates one generator per step, not an entire word afresh. -/
theorem representativeNat_base (j : Nat) (hj : j < 31671) :
    representativeNat j (508 : Fin 306936) = labelPoint j := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    by_cases hj0 : j = 0
    · subst j
      rw [representativeNat_zero]
      rfl
    · have hp : parent j < j := by
        cases j with
        | zero => exact (hj0 rfl).elim
        | succ k => exact parent_lt k
      rw [representativeNat_step j hj0, Equiv.Perm.mul_apply,
        ih (parent j) hp (hp.trans hj)]
      exact labelPoint_step j hj hj0

/-- The actual base point of the stage has the certified representative label. -/
theorem representative_base (j : Fin 31671) :
    representative j (point 0) = labelPoint j.val := by
  rw [point_zero]
  exact representativeNat_base j.val j.isLt

/-- This is the `returns_base` clause, with no stabilizer or orbit premise. -/
theorem returns_base (j : Fin 31671)
    (h : representative j (point 0) = point 0) : representative j = 1 := by
  have hl : label j.val = 508 := by
    rw [representative_base, point_zero] at h
    exact congrArg Fin.val h
  have hj : j.val = 0 := by
    by_contra hj
    have hc := treeCheck_eq_true j.val j.isLt
    simp only [treeCheck, if_neg hj, Bool.and_eq_true] at hc
    have hn := hc.2
    simp only [hl, BEq.rfl, Bool.not_true] at hn
    contradiction
  have he : j = 0 := Fin.ext hj
  subst j
  exact representative_zero

/-- Parent indices stay inside the certified representative family. -/
def parentIndex (j : Fin 31671) : Fin 31671 :=
  ⟨parent j.val, by
    have h := Nat.min_le_right (rawParent j.val) (j.val - 1)
    change min (rawParent j.val) (j.val - 1) < 31671
    omega⟩

/-- Every nonroot defining edge is already a positive transition with factor 1. -/
theorem defining_transition (j : Fin 31671) (hj : j ≠ 0) :
    generators 0 (letter j.val) * representative j = representative (parentIndex j) := by
  have hj0 : j.val ≠ 0 := fun h => hj (Fin.ext h)
  change generators 0 (letter j.val) * representativeNat j.val =
    representativeNat (parent j.val)
  rw [representativeNat_step j.val hj0, mul_inv_cancel_left]

end Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesZeroTwo.StageZero
