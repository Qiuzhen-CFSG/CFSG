module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Checks
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.SourceActions

/-!
# Actual representatives for the first Fi23 stabilizer step

Recursion down the checked tree constructs permutations taking letter 1 to
each specified letter. The complete three-cycles in the tree make every
non-loop second-generator edge trivial. First-generator tree edges are also
trivial in both directions, using its checked involution relation.

Source: ATLAS F23G1-p31671B0; first prefix bound for GLS3 Table 5.3u.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.FirstTree
open Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate

/-- The actual permutation prescribed by the label on a tree edge. -/
def treeGenerator (x : Fin 31671) : Equiv.Perm (Fin 31671) :=
  if isB x then generatorB else generatorA

theorem treeGenerator_parent (x : Fin 31671) (hx : x ≠ 1) :
    treeGenerator x (parent x) = x := by
  cases hk : isB x <;>
    simpa [treeGenerator, hk, generatorA_apply_eq_sourceA,
      generatorB_apply_eq_sourceB] using parent_action x hx

/-- The tree word is evaluated in the literal cycle-decoded carrier action. -/
def representative (x : Fin 31671) : Equiv.Perm (Fin 31671) :=
  if _h : x = 1 then 1 else treeGenerator x * representative (parent x)
termination_by depth x
decreasing_by exact parent_depth_lt x _h

theorem representative_one : representative 1 = 1 := by
  rw [representative, dif_pos rfl]

theorem representative_step (x : Fin 31671) (hx : x ≠ 1) :
    representative x = treeGenerator x * representative (parent x) := by
  rw [representative, dif_neg hx]

/-- In particular the representative returning the base letter is the identity. -/
theorem representative_base (x : Fin 31671) : representative x 1 = x := by
  induction x using (measure depth).wf.induction with
  | h x ih =>
    by_cases hx : x = 1
    · subst x
      rw [representative_one]
      rfl
    · rw [representative_step x hx, Equiv.Perm.mul_apply,
        ih (parent x) (parent_depth_lt x hx)]
      exact treeGenerator_parent x hx

theorem generatorA_involutive (x : Fin 31671) : generatorA (generatorA x) = x := by
  simpa only [generatorA_apply_eq_sourceA] using sourceA_involutive x

theorem generatorA_square : generatorA * generatorA = 1 := by
  apply Equiv.ext
  intro x
  exact generatorA_involutive x

theorem generatorB_cube_eq : generatorB * (generatorB * generatorB) = 1 := by
  apply Equiv.ext
  intro x
  change generatorB (generatorB (generatorB x)) = x
  simpa only [generatorB_apply_eq_sourceB] using sourceB_cube x

/-- All non-loop second-generator transitions follow from two tree edges
and the cube relation, without subgroup membership certificates. -/
theorem b_transition (x : Fin 31671) (hx : generatorB x ≠ x) :
    generatorB * representative x = representative (generatorB x) := by
  have shape := b_shape x
  simp only [← generatorB_apply_eq_sourceB] at shape
  rcases shape with h | ⟨hne, hp, hk⟩ | ⟨hne, hpne, hk, hpk, hpp⟩
  · exact (hx h).elim
  · rw [representative_step _ hne, treeGenerator, hk, if_pos rfl, hp]
  · rw [representative_step x hne, treeGenerator, hk, if_pos rfl,
      representative_step (parent x) hpne, treeGenerator, hpk, if_pos rfl, hpp,
      ← mul_assoc generatorB generatorB, ← mul_assoc,
      mul_assoc generatorB generatorB generatorB, generatorB_cube_eq, one_mul]

/-- Both directions of a first-generator tree edge have trivial factor. -/
theorem a_tree_transition (x : Fin 31671) (hx : aTree x = true) :
    generatorA * representative x = representative (generatorA x) := by
  simp only [aTree, Bool.or_eq_true, decide_eq_true_eq,
    ← generatorA_apply_eq_sourceA] at hx
  rcases hx with ⟨hne, hp, hk⟩ | ⟨hne, hp, hk⟩
  · simp only [representative_step _ hne, treeGenerator, hk, Bool.false_eq_true, if_false, hp]
  · simp only [representative_step x hne, treeGenerator, hk, Bool.false_eq_true, if_false, hp,
      ← mul_assoc, generatorA_square, one_mul]

/-- The actual left-action Schreier element at a letter. -/
def edge (s : Equiv.Perm (Fin 31671)) (x : Fin 31671) : Equiv.Perm (Fin 31671) :=
  (representative (s x))⁻¹ * s * representative x

theorem b_edge_eq_one (x : Fin 31671) (hx : generatorB x ≠ x) :
    edge generatorB x = 1 := by
  rw [edge, mul_assoc, b_transition x hx, inv_mul_cancel]

theorem a_tree_edge_eq_one (x : Fin 31671) (hx : aTree x = true) :
    edge generatorA x = 1 := by
  rw [edge, mul_assoc, a_tree_transition x hx, inv_mul_cancel]

/-- Only one orientation of a non-loop first-generator edge needs checking. -/
theorem a_edge_reverse (x : Fin 31671) :
    edge generatorA (generatorA x) = (edge generatorA x)⁻¹ := by
  have hi : generatorA⁻¹ = generatorA := by
    apply inv_eq_of_mul_eq_one_left
    exact generatorA_square
  simp only [edge, generatorA_involutive, mul_inv_rev, inv_inv, hi, mul_assoc]

end Sporadic.Fischer.Fi23.CentralizerSection.FirstTree
