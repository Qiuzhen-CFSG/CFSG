module
public import Theory.Representation.BinaryOffender.Basic
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
/-!
# The group index of a binary fixed space

The cardinal formula for a finite binary vector space turns fixed codimension
into the index of the fixed subgroup on the original elementary abelian carrier.
The first-hat source application uses this to retain its literal quotient.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace Representation.BinaryOffender
variable {D E : Type*} [Group D] [Group E] [Finite E] [IsElementaryAbelian 2 E]
theorem fixed_subgroup_index
    (σ : Representation (ZMod 2) D (Additive E)) :
    (AddSubgroup.toSubgroup' (fixedSpace σ ⊤).toAddSubgroup).index = 2 ^ fixedCodim σ ⊤ := by
  let F := AddSubgroup.toSubgroup' (fixedSpace σ ⊤).toAddSubgroup
  have hc := F.card_mul_index
  have hf : Nat.card F = 2 ^ Module.finrank (ZMod 2) (fixedSpace σ ⊤) := by
    exact (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedSpace σ ⊤)).trans
      (by rw [Nat.card_zmod])
  have he : Nat.card E = 2 ^ Module.finrank (ZMod 2) (Additive E) := by
    exact (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive E)).trans
      (by rw [Nat.card_zmod])
  rw [hf, he, ← fixedCodim_add_finrank σ ⊤, add_comm, pow_add] at hc
  exact Nat.eq_of_mul_eq_mul_left (by positivity) hc
end Representation.BinaryOffender
