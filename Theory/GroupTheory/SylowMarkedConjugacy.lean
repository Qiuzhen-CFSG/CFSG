module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Subgroup.Center

/-!
# Sylow conjugacy preserving a central mark

Conjugation identifies any two Sylow subgroups of a finite group and fixes
every central element. Thus a specified central element lying in both Sylow
subgroups can be preserved literally, rather than only up to conjugacy.

Source: the Sylow conjugacy theorem, as formalized in Mathlib.
-/

open scoped Pointwise

namespace Sylow
public theorem exists_equiv_fix_central
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P Q : Sylow p G) (z : G) (hz : z ∈ Subgroup.center G)
    (hzP : z ∈ P) (hzQ : z ∈ Q) :
    ∃ e : P ≃* Q, e ⟨z, hzP⟩ = ⟨z, hzQ⟩ := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G P Q
  refine ⟨P.equivSMul g, ?_⟩
  apply Subtype.ext
  change g * z * g⁻¹ = z
  rw [(Subgroup.mem_center_iff.mp hz g), mul_inv_cancel_right]
end Sylow
