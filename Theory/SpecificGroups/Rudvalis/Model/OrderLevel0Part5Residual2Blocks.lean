module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5ResidualReduction

/-!
# Coverage for Rudvalis part-5 residual group 2

The 69 prescribed transitions at residual indices 138 through 206 split into
three independent intervals of 23. Division with remainder proves that these
intervals cover exactly residual group 2, preserving every representative and
factor word in the original certificate.

Source: `Part5Residual.target` in `OrderLevel0Part5ResidualReduction`, with
witnesses documented in `OrderCertificate/GenerateChain.g`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual2

/-- Twenty-three consecutive, prescribed residual transition identities. -/
@[expose] public def block (b : Fin 3) : Prop :=
  ∀ s : Fin 23, residualCheck ⟨138 + 23 * b.val + s.val, by omega⟩

/-- The three intervals cover exactly residual group 2. -/
public theorem assemble (h : ∀ b : Fin 3, block b) : residualBatch 2 := by
  intro s hs
  let b : Fin 3 := ⟨s.val / 23, by omega⟩
  let t : Fin 23 := ⟨s.val % 23, by omega⟩
  have hk : (⟨138 + 23 * b.val + t.val, by omega⟩ : Fin 275) =
      ⟨69 * (2 : Fin 4).val + s.val, hs⟩ := by
    apply Fin.ext
    dsimp [b, t]
    omega
  simpa only [hk] using h b t

end Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual2
