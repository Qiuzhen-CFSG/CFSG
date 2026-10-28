module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Second.Orbit

/-!
# Actual Schreier representatives at letter 13

The checked orbit tree defines genuine permutations. Induction along the tree
proves their action on the base letter, so only the identity representative can
return to that letter. Every tree edge, in either direction, has trivial
Schreier factor. The remaining factors must be certified in the literal second
subgroup; their membership is not a consequence of the orbit table.

Source application: ATLAS F23G1-p31671B0 and GLS3 Table 5.3u.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.SecondCertificate

/-- Left-action tree word sending 13 to the indicated orbit letter. -/
def representative (i : Fin 3510) : Equiv.Perm (Fin 31671) :=
  if _hi : i = 0 then 1
  else signedGenerator (label i) * representative (parent i)
termination_by i.val
decreasing_by exact parent_lt i _hi

theorem representative_zero : representative 0 = 1 := by
  rw [representative]
  exact dif_pos rfl

theorem representative_edge (i : Fin 3510) (hi : i ≠ 0) :
    representative i = signedGenerator (label i) * representative (parent i) := by
  rw [representative, dif_neg hi]

theorem representative_point (i : Fin 3510) : representative i 13 = point i := by
  induction i using (measure (fun i : Fin 3510 => i.val)).wf.induction with
  | h i ih =>
    by_cases hi : i = 0
    · subst i
      rw [representative_zero]
      exact point_zero.symm
    · rw [representative_edge i hi, Equiv.Perm.mul_apply,
        ih (parent i) (parent_lt i hi)]
      exact tree_edge i hi

theorem representative_returns (i : Fin 3510) (hi : representative i 13 = 13) :
    representative i = 1 := by
  rw [representative_point] at hi
  rw [point_eq_base i hi, representative_zero]

/-- Positive and negative labels retain the literal first-generator ordering. -/
def positive (a : Fin 2) : Fin 4 := ⟨a.val, Nat.lt_trans a.isLt (by decide)⟩
def negative (a : Fin 2) : Fin 4 := ⟨a.val + 2, Nat.add_lt_add_right a.isLt 2⟩

theorem signed_positive (a : Fin 2) :
    signedGenerator (positive a) = KernelUpperData.firstGenerator a := by
  fin_cases a <;> rfl

theorem signed_negative (a : Fin 2) :
    signedGenerator (negative a) = (KernelUpperData.firstGenerator a)⁻¹ := by
  fin_cases a <;> rfl

/-- The concrete left-action Schreier element at a positive edge. -/
def schreier (a : Fin 2) (i : Fin 3510) : Equiv.Perm (Fin 31671) :=
  (representative (next a i))⁻¹ * KernelUpperData.firstGenerator a * representative i

/-- Tree edges and their reverses need no permutation computation. -/
def TreeEdge (a : Fin 2) (i : Fin 3510) : Prop :=
  (next a i ≠ 0 ∧ parent (next a i) = i ∧ label (next a i) = positive a) ∨
  (i ≠ 0 ∧ parent i = next a i ∧ label i = negative a)

instance (a : Fin 2) (i : Fin 3510) : Decidable (TreeEdge a i) :=
  inferInstanceAs (Decidable ((_ ∧ _ ∧ _) ∨ (_ ∧ _ ∧ _)))

theorem schreier_eq_one_of_tree (a : Fin 2) (i : Fin 3510) (hi : TreeEdge a i) :
    schreier a i = 1 := by
  rcases hi with ⟨hj, hp, hl⟩ | ⟨hj, hp, hl⟩
  · have he := representative_edge (next a i) hj
    rw [hp, hl, signed_positive] at he
    simp only [schreier, he, mul_inv_rev, mul_assoc, inv_mul_cancel, one_mul]
  · have he := representative_edge i hj
    rw [hp, hl, signed_negative] at he
    simp only [schreier, he, mul_assoc, mul_inv_cancel_left, inv_mul_cancel]

theorem schreier_mem_of_tree (a : Fin 2) (i : Fin 3510) (hi : TreeEdge a i) :
    schreier a i ∈ KernelUpperData.second := by
  rw [schreier_eq_one_of_tree a i hi]
  exact Subgroup.one_mem _

/-- Only the non-tree edges remain as concrete certificate obligations. -/
theorem schreier_mem_of_non_tree (a : Fin 2)
    (h : ∀ i, ¬ TreeEdge a i → schreier a i ∈ KernelUpperData.second) :
    ∀ i, schreier a i ∈ KernelUpperData.second := by
  intro i
  by_cases hi : TreeEdge a i
  · exact schreier_mem_of_tree a i hi
  · exact h i hi

end Sporadic.Fischer.Fi23.CentralizerSection.SecondCertificate
