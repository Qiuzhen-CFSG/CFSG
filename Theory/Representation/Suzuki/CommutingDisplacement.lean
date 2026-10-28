module
public import Theory.Representation.Suzuki.CentralizerDisplacement

/-!
# Nonzero operators commuting with a fixed-free Suzuki action

The image of a commuting operator is a Suzuki submodule. If the ambient
action has no fixed vectors, simplicity makes every nonzero such image
faithful. Its binary dimension is therefore at least 4(2m+1).

This version permits a kernel in an unrelated ambient actor and applies to
invariant subspaces. The Chapter 10 central Hall support argument uses it
after removing the actor's pointwise kernel on a homogeneous orbit.
Source: Aschbacher--Smith D.3.9, printed pp.200--201; the degree bound is
the primitive-prime argument in Suzuki.BinaryDegree.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.Suzuki
variable {S V : Type*} [Group S] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- A nonzero commuting operator on a fixed-free Suzuki module has large image. -/
theorem commuting_operator_rank_bound
    (ρ : Representation (ZMod 2) S V) (hfix : ρ.invariants = ⊥)
    (m : ℕ) (hm : 0 < m) (e : S ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (f : Module.End (ZMod 2) V) (hf : f ≠ 0)
    (hc : ∀ s : S, f * ρ s = ρ s * f) :
    4 * (2*m+1) ≤ Module.finrank (ZMod 2) f.range := by
  let : Fact (0 < m) := ⟨hm⟩
  let : IsSimpleGroup S := e.isSimpleGroup
  let U : Subrepresentation ρ := {
    toSubmodule := f.range
    apply_mem_toSubmodule s v hv := by
      obtain ⟨w,rfl⟩ := hv
      exact ⟨ρ s w,LinearMap.congr_fun (hc s) w⟩ }
  have hU : U ≠ ⊥ := by
    intro he
    apply hf
    apply LinearMap.range_eq_bot.mp
    exact congrArg Subrepresentation.toSubmodule he
  have hfaith := simple_subrepresentation_faithful_of_fixed_eq_bot ρ hfix U hU
  exact finrank_ge (by omega : 1 ≤ m) (U.toRepresentation.comp e.symm.toMonoidHom)
    (hfaith.comp e.symm.injective)
end Representation.Suzuki
