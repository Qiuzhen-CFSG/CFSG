module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5ResidualReduction

/-!
# Three intervals for Rudvalis part-5 residual group 0

The 69 prescribed transitions split into three independent intervals of 23.
Division with remainder proves that their certificates cover exactly the requested
batch. Source: `residualBatch` and `target` in `OrderLevel0Part5ResidualReduction`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual0Checks

@[expose] public def block (b : Fin 3) : Prop :=
  ∀ s : Fin 23, residualCheck ⟨23 * b.val + s.val, by omega⟩

/-- Three exact interval certificates complete residual batch 0. -/
public theorem residuals0_of_blocks (h : ∀ b : Fin 3, block b) : residualBatch 0 := by
  intro s hs
  have hk := h ⟨s.val / 23, by omega⟩ ⟨s.val % 23, by omega⟩
  change residualCheck ⟨23 * (s.val / 23) + s.val % 23, _⟩ at hk
  have heq : (⟨23 * (s.val / 23) + s.val % 23, by omega⟩ : Fin 275) =
      ⟨69 * (0 : Fin 4).val + s.val, hs⟩ := by
    apply Fin.ext
    simp only [Fin.val_zero, Nat.mul_zero, Nat.zero_add]
    omega
  exact heq ▸ hk

end Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual0Checks
