module

public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.Definitions
public import Theory.SpecificGroups.Rudvalis.Model.OrderCheck
import Mathlib.Tactic.FinCases

/-!
# Interfaces for the two local Rudvalis cardinality certificates

The certificates use the word-subgroup Schreier decomposition and the existing
kernel-checked finite enumeration. The comparison below identifies a subgroup
of `Rudvalis.Model` with its image in the degree-4060 permutation group before
any cardinality is transported. No order or simplicity theorem for Rudvalis is
used. See the ATLAS source attribution in `SylowOvergroups.Definitions`.
-/

namespace Rudvalis.SylowOvergroups.LocalCardinality
open Theory.GroupTheory

/-- The image of a two-generator subgroup under the faithful model inclusion. -/
public theorem card_closure_pair (x y : Model) :
    Nat.card (Subgroup.closure ({x, y} : Set Model)) =
      Nat.card (Subgroup.closure
        ({modelSubgroup.subtype x, modelSubgroup.subtype y} :
          Set (Equiv.Perm (Fin 4060)))) := by
  have h := Nat.card_congr ((Subgroup.closure ({x, y} : Set Model)).equivMapOfInjective
    modelSubgroup.subtype Subtype.val_injective).toEquiv
  erw [MonoidHom.map_closure modelSubgroup.subtype ({x, y} : Set Model), Set.image_pair] at h
  exact h

/-- Four signed generators give the same subgroup as their two positive generators. -/
public theorem wordSubgroup_eq_pair {G : Type*} [Group G]
    (gen : Fin 4 → G) (invOf : Fin 4 → Fin 4)
    (hInv : ∀ i, gen (invOf i) = (gen i)⁻¹)
    (h2 : gen 2 = (gen 0)⁻¹) (h3 : gen 3 = (gen 1)⁻¹) :
    wordSubgroup gen invOf hInv = Subgroup.closure {gen 0, gen 1} := by
  apply le_antisymm
  · have hgen : ∀ i, gen i ∈ Subgroup.closure ({gen 0, gen 1} : Set G) := by
      intro i
      have h0 : gen 0 ∈ Subgroup.closure ({gen 0, gen 1} : Set G) :=
        Subgroup.subset_closure (Set.mem_insert _ _)
      have h1 : gen 1 ∈ Subgroup.closure ({gen 0, gen 1} : Set G) :=
        Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
      fin_cases i
      · exact h0
      · exact h1
      · exact h2.symm ▸ Subgroup.inv_mem _ h0
      · exact h3.symm ▸ Subgroup.inv_mem _ h1
    rintro g ⟨w, rfl⟩
    induction w with
    | nil => exact Subgroup.one_mem _
    | cons i w ih => exact Subgroup.mul_mem _ (hgen i) ih
  · apply (Subgroup.closure_le _).mpr
    rintro g (rfl | hg)
    · exact ⟨[0], mul_one _⟩
    · obtain rfl := Set.mem_singleton_iff.mp hg
      exact ⟨[1], mul_one _⟩

/-- Reverse a certified positive Schreier transition. -/
public theorem reverse_step {G : Type*} [Group G] {a b c d : G}
    (h : a * b = c * d) : a⁻¹ * c = b * d⁻¹ := by
  apply (eq_mul_inv_iff_mul_eq).2
  rw [mul_assoc, ← h, inv_mul_cancel_left]

end Rudvalis.SylowOvergroups.LocalCardinality
