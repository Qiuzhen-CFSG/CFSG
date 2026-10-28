module

public import Theory.SpecificGroups.SymmetricFourTranspositionResidual
public import Theory.SpecificGroups.SymmetricFourResidualCore

/-!
# The marked witness for the terminal contradiction

In the original factor `M₁`, lift the transposition `(0 1)` through its
chosen S₄ isomorphism. Sign detects that this lift lies outside `O²(M₁)`.
Since `M₁ ∩ A = O₂(M₁)` and that core lies in the residual, the lift also
lies outside `A`. Source 13.9.3(3) therefore puts it in the actual class
`Δ₃`. Once 13.9.9(3) has fused that class to `z`, this supplies the
particular terminal witness in `M₁ \ O²(M₁)`.

The final fusion premise is intentionally explicit here. Its discharge
belongs to the assembly of 13.9.9, not to the transposition calculation.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.9.3(3), 13.9.9(3), and the final paragraph of 13.9.1, pp.970, 973–974.
-/

public section

namespace CFSG.Quasithin.Chapter13.Section09.FusionAlignment

open Subgroup Theory.SpecificGroups.SymmetricFour

variable {G : Type*} [Group G]

/-- Construct the original-factor involution needed by the terminal
consumer, including its escape from the literal embedded residual. -/
theorem exists_factor_involution_outside_residual
    (M₁ A : Subgroup G) (e : M₁ ≃* Equiv.Perm (Fin 4))
    (hcore : M₁ ⊓ A = M₁.pCoreIn 2) (Δ₃ : Set G)
    (hclass : ∀ x : G, x ∈ M₁ → orderOf x = 2 → x ∉ A → x ∈ Δ₃) :
    ∃ x : G, x ∈ M₁ ∧ x ∈ Δ₃ ∧ x ∉ (pResidual 2 M₁).map M₁.subtype := by
  let x := e.symm (Equiv.swap (0 : Fin 4) 1)
  obtain ⟨hxorder, hxres⟩ := transposition_lift_outside_twoResidual e
  have hres : (x : G) ∉ (pResidual 2 M₁).map M₁.subtype := by
    rintro ⟨y, hy, hyx⟩
    exact hxres (show x ∈ pResidual 2 M₁ from (Subtype.ext hyx : y = x) ▸ hy)
  have hnotA : (x : G) ∉ A := by
    intro hxA
    have hxcore : (x : G) ∈ M₁.pCoreIn 2 := hcore ▸ ⟨x.property, hxA⟩
    exact hres (map_mono (f := M₁.subtype) (twoCore_le_twoResidual_of_equiv e) hxcore)
  refine ⟨x, x.property, hclass x x.property ?_ hnotA, hres⟩
  exact (Subgroup.orderOf_coe x).trans hxorder

/-- Applying the fusion of `Δ₃` produces a conjugate of `z` in the original
`M₁`, outside its two-residual as required on p.974. -/
theorem exists_z_conjugate_in_factor_outside_residual
    (M₁ A : Subgroup G) (e : M₁ ≃* Equiv.Perm (Fin 4))
    (hcore : M₁ ⊓ A = M₁.pCoreIn 2) (Δ₃ : Set G) (z : G)
    (hclass : ∀ x : G, x ∈ M₁ → orderOf x = 2 → x ∉ A → x ∈ Δ₃)
    (hfusion : ∀ x ∈ Δ₃, IsConj z x) :
    ∃ x : G, x ∈ M₁ ∧ x ∉ (pResidual 2 M₁).map M₁.subtype ∧ IsConj z x := by
  obtain ⟨x, hxM, hxΔ, hxres⟩ :=
    exists_factor_involution_outside_residual M₁ A e hcore Δ₃ hclass
  exact ⟨x, hxM, hxres, hfusion x hxΔ⟩

end CFSG.Quasithin.Chapter13.Section09.FusionAlignment
