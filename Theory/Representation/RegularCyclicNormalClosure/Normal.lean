module

public import Theory.Representation.RegularCyclicNormalClosure.Basic

/-!
# The normal cyclic branch

When the given cyclic subgroup is normal, it is its own normal closure.
The one-factor decomposition uses exactly its displacement span. Conjugation
preserves the subgroup, and equivariance of displacement spans preserves the
summand. This constructs all the internal group and module data required by
E.6.24 in this branch; the nonnormal branch remains a separate obligation.

Source: the first alternative of Aschbacher–Smith E.6.24, printed p.255,
citing Aschbacher, J. Algebra 70 (1981), 10.4.
-/

public section

namespace Representation.RegularCyclicNormalClosure
open Subgroup BinaryOffender
variable {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) A W)
/-- The actual one-factor decomposition when C is normal. -/
noncomputable def decompositionOfNormal {C : Subgroup A} (h : Input ρ C) [C.Normal] :
    Decomposition ρ C where
  size := 1
  positive := by decide
  factor := fun _ => C
  summand := fun _ => displacementSpan ρ C ⊤
  distinguished := 0
  contained := le_rfl
  group_eq := by simp [normalClosure_eq_self]
  group_independent := iSupIndep_subsingleton _
  commuting := by intro i j hij; exact False.elim (hij (Subsingleton.elim i j))
  split := by simpa only [normalClosure_eq_self] using h.split
  moved_eq := by simp [normalClosure_eq_self]
  summands_independent := iSupIndep_subsingleton _
  self_moved := fun _ => displacementSpan_self_of_split ρ C h.split
  cross_fixed := by intro i j hij; exact False.elim (hij (Subsingleton.elim i j))
  permuted := by
    intro a
    exact ⟨_root_.Equiv.refl _, fun _ => ⟨Subgroup.Normal.map_conj_eq _ a,
      displacementSpan_map_of_normalized ρ C a (Subgroup.Normal.map_conj_eq _ a)⟩⟩
  transitive := by
    intro i j
    exact ⟨1, Subgroup.Normal.map_conj_eq _ 1,
      displacementSpan_map_of_normalized ρ C 1 (Subgroup.Normal.map_conj_eq _ 1)⟩
  alternatives := Or.inl rfl

/-- Existence of the complete decomposition in the normal-subgroup branch. -/
theorem exists_decomposition_of_normal {C : Subgroup A} (h : Input ρ C) [C.Normal] :
    Nonempty (Decomposition ρ C) := ⟨decompositionOfNormal ρ h⟩

end Representation.RegularCyclicNormalClosure
