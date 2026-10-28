module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5ResidualReduction

/-!+# Coverage for the last Rudvalis part-5 residual certificate

The 68 prescribed transitions at residual indices 207 through 274 split into
four intervals of 17. Division with remainder by 17 assembles their certificates
into the original residual batch. Its bound excludes local index 68.

Source: `Part5Residual.target` in `OrderLevel0Part5ResidualReduction`, with
transition witnesses from `OrderLevel0Data` and `OrderCertificate/GenerateChain.g`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual3Checks

/-- Seventeen consecutive residual checks, with the original transition witnesses. -/
@[expose] public def block (b : Fin 4) : Prop :=
  ∀ s : Fin 17, residualCheck ⟨207 + 17 * b.val + s.val, by omega⟩

/-- The four intervals cover precisely the final residual batch. -/
public theorem ofBlocks (h : ∀ b : Fin 4, block b) : residualBatch 3 := by
  intro s hs
  let b : Fin 4 := ⟨s.val / 17, by omega⟩
  let t : Fin 17 := ⟨s.val % 17, by omega⟩
  have heq : (⟨207 + 17 * b.val + t.val, by omega⟩ : Fin 275) =
      ⟨69 * (3 : Fin 4).val + s.val, hs⟩ := by
    apply Fin.ext
    dsimp [b, t]
    omega
  simpa only [heq] using h b t

end Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual3Checks
