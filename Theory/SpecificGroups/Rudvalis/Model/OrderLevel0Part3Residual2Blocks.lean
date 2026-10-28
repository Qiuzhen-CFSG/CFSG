module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3ResidualReduction

/-!
# Coverage for Rudvalis part-3 residual group 2

The 68 fixed transitions at residual indices 136 through 203 split into four
independent blocks of 17. The coverage theorem assembles those blocks into the
original residual batch, without changing any representative or factor word.
Source: `Part3Residual.target` in `OrderLevel0Part3ResidualReduction`, with
witnesses documented in `OrderCertificate/GenerateChain.g`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual2

/-- Seventeen consecutive, prescribed residual transition identities. -/
@[expose] public def block (b : Fin 4) : Prop :=
  ∀ s : Fin 17, residualCheck ⟨136 + 17 * b.val + s.val, by omega⟩

/-- The four blocks cover exactly residual group 2. -/
public theorem assemble (h : ∀ b : Fin 4, block b) : residualBatch 2 := by
  intro s hs
  let b : Fin 4 := ⟨s.val / 17, by omega⟩
  let t : Fin 17 := ⟨s.val % 17, by omega⟩
  have hk : (⟨136 + 17 * b.val + t.val, by omega⟩ : Fin 271) =
      ⟨68 * (2 : Fin 4).val + s.val, hs⟩ := by
    apply Fin.ext
    dsimp [b, t]
    omega
  simpa only [hk] using h b t

end Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual2
