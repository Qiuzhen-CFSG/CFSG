module

public import Theory.SpecificGroups.Janko3.Model.Basic
public import Theory.GroupTheory.CentralCoprimeLocalProductLift
public import Mathlib.Data.ZMod.Basic

/-!
# A local configuration sufficient for the J₃ three-cover argument

This interface describes subgroups and maps in the actual permutation model.
The intended construction uses the affine local `2⁴ : GL₂(4)`: its scalar
three-group centralizes an A₅ complement and both normalize the translation
group. The scalar group also lies in a perfect involution centralizer with
cyclic Sylow three-subgroups. Those two perfect supports allow splitting in
every central three-extension.

This module asserts no existence of the configuration and no covering-group
rank bound. In particular the ordinary-rank construction of I.2.1 is not an
inhabitant of this interface without the stated normalization facts.

Sources: Aschbacher--Smith, A.2.19, printed p.41, and I.2.1, printed p.409;
GLS, Number 3, Table 5.3h, printed p.269.
-/

namespace Sporadic.Janko3

/-- Concrete downstairs data; no splitting or rank conclusion is a field. -/
public structure ThreeCoverLocalConfiguration where
  twoSubgroup : Subgroup Model
  two_nontrivial : twoSubgroup ≠ ⊥
  two_isPGroup : IsPGroup 2 twoSubgroup
  leftSupport : Subgroup Model
  rightSupport : Subgroup Model
  left_perfect : Group.IsPerfect leftSupport
  right_perfect : Group.IsPerfect rightSupport
  left_cyclicSylow : ∀ S : Sylow 3 leftSupport, IsCyclic S
  right_cyclicSylow : ∀ S : Sylow 3 rightSupport, IsCyclic S
  plane : (Multiplicative (ZMod 3) × Multiplicative (ZMod 3)) →* Model
  plane_injective : Function.Injective plane
  left_mem : ∀ a, plane (a, 1) ∈ leftSupport
  right_mem : ∀ b, plane (1, b) ∈ rightSupport
  left_centralizes : ∀ a, plane (a, 1) ∈ Subgroup.centralizer (rightSupport : Set Model)
  normalizes : ∀ a, plane a ∈ Subgroup.normalizer (twoSubgroup : Set Model)

end Sporadic.Janko3
