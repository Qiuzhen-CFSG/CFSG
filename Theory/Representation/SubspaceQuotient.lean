module

public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Quotient actions on invariant subspaces

An invariant subspace has its literal quotient representation, induced by the
original linear maps. The image of any other invariant subspace is invariant
in this quotient. If the quotient is irreducible, the image is zero or the
whole quotient; equivalently, the original subspace lies in the kernel or
supplements it.

These are the linear constructions used in Aschbacher–Smith,
*The Classification of Quasithin Groups*, A.1.40 and B.7.2.
-/

@[expose] public section

namespace Subrepresentation
variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  {ρ : Representation k G V}

/-- The action induced on the actual vector-space quotient. -/
def quotientRepresentation (U : Subrepresentation ρ) :
    Representation k G (V ⧸ U.toSubmodule) where
  toFun g := U.toSubmodule.mapQ U.toSubmodule (ρ g) (U.apply_mem_toSubmodule g)
  map_one' := by
    apply LinearMap.ext
    intro v
    induction v using Submodule.Quotient.induction_on
    simp [Submodule.mapQ_apply]
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    induction v using Submodule.Quotient.induction_on
    simp [Submodule.mapQ_apply, Module.End.mul_apply]

@[simp] theorem quotientRepresentation_mk (U : Subrepresentation ρ) (g : G) (v : V) :
    U.quotientRepresentation g (U.toSubmodule.mkQ v) = U.toSubmodule.mkQ (ρ g v) := rfl

/-- Images of invariant subspaces in an invariant quotient. -/
def quotientImage (U W : Subrepresentation ρ) : Subrepresentation U.quotientRepresentation where
  toSubmodule := W.toSubmodule.map U.toSubmodule.mkQ
  apply_mem_toSubmodule g := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨ρ g w, W.apply_mem_toSubmodule g hw, rfl⟩

theorem quotientImage_eq_bot_iff (U W : Subrepresentation ρ) :
    U.quotientImage W = ⊥ ↔ W ≤ U := by
  constructor
  · intro heq w hw
    have hm : U.toSubmodule.mkQ w ∈ U.quotientImage W := ⟨w, hw, rfl⟩
    rw [heq] at hm
    exact (Submodule.Quotient.mk_eq_zero U.toSubmodule).mp hm
  · intro h
    apply Subrepresentation.toSubmodule_injective
    apply le_antisymm _ bot_le
    rintro _ ⟨w, hw, rfl⟩
    exact (Submodule.Quotient.mk_eq_zero U.toSubmodule).mpr (h hw)

theorem quotientImage_eq_top_iff (U W : Subrepresentation ρ) :
    U.quotientImage W = ⊤ ↔ U.toSubmodule ⊔ W.toSubmodule = ⊤ := by
  rw [← Subrepresentation.toSubmodule_injective.eq_iff]
  exact Submodule.map_mkQ_eq_top _ _

/-- An irreducible quotient forces every invariant subspace either into its
kernel or to surject onto the quotient. -/
theorem le_or_sup_eq_top_of_irreducible_quotient (U W : Subrepresentation ρ)
    [Representation.IsIrreducible U.quotientRepresentation] :
    W ≤ U ∨ U.toSubmodule ⊔ W.toSubmodule = ⊤ := by
  rcases eq_bot_or_eq_top (U.quotientImage W) with h | h
  · exact Or.inl ((quotientImage_eq_bot_iff U W).mp h)
  · exact Or.inr ((quotientImage_eq_top_iff U W).mp h)
end Subrepresentation
