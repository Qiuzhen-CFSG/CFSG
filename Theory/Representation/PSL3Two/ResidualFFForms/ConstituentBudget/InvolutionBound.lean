module
public import Theory.Representation.PSL3Two.ResidualFFForms.ConstituentBudget.Dimension
import all Theory.Representation.PSL3Two.ResidualFFForms.ConstituentBudget.Dimension

/-!
# Dimension from one involution in binary SL₃(2)

Three conjugate involutions generate the group. For a fully moved module,
their displacement spaces span the module, so its dimension is at most three
times the fixed codimension of any involution. This is the version of the
constituent budget used by the outer-automorphism natural–dual recognition.

The `import all` intentionally reuses the private generator calculation in
`Dimension` within this constituent-budget implementation split.
Source: Aschbacher–Smith B.5.1 and E.2.17.
-/

public section
open Representation Representation.BinaryOffender
namespace BinaryLinearThree.ResidualFFForms.ConstituentBudget
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) Matrix.PSL3Two.SL V)

theorem finrank_le_three_mul_involution_fixedCodim
    (hfull : subspaceCommutator ρ ⊤ ⊤ = ⊤)
    (a : Matrix.PSL3Two.SL) (ha : a ^ 2 = 1) (hne : a ≠ 1) :
    Module.finrank (ZMod 2) V ≤ 3 * fixedCodim ρ (Subgroup.zpowers a) := by
  obtain ⟨c,hc⟩ := involution_conjugacy a ha hne
  have he : c * a * c⁻¹ = x := by rw [hc,mul_inv_cancel_right]
  have hb := bound_by_involution ρ hfull
  rwa [←he,fixedCodim_zpowers_conj] at hb
end BinaryLinearThree.ResidualFFForms.ConstituentBudget
