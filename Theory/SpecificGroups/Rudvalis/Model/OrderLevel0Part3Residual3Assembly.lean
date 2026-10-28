module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3ResidualReduction

/-!
# Assembly of the last Rudvalis part-3 residual certificate

The residual indices 204 through 270 are partitioned into four intervals of
at most 17 transitions. The bound in `subbatch` excludes index 271, just as
the bound in `residualBatch 3` excludes its final slot. Division with remainder
by 17 reconstructs the full certificate from these independent intervals.

Source: the fixed transition enumeration `Part3Residual.target` in
`OrderLevel0Part3ResidualReduction`, with witnesses from `OrderLevel0Data`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual3Checks

/-- Four disjoint intervals cover the 67 transitions of residual group 3. -/
@[expose] public def subbatch (b : Fin 4) : Prop :=
  ∀ (s : Fin 17) (h : 204 + 17 * b.val + s.val < 271),
    residualCheck ⟨204 + 17 * b.val + s.val, h⟩

/-- Assemble the last residual group from its four bounded intervals. -/
public theorem ofSubbatches (h : ∀ b : Fin 4, subbatch b) : residualBatch 3 := by
  intro s hs
  let b : Fin 4 := ⟨s.val / 17, by omega⟩
  let t : Fin 17 := ⟨s.val % 17, by omega⟩
  have hlt : 204 + 17 * b.val + t.val < 271 := by
    dsimp [b, t]
    omega
  have heq : (⟨204 + 17 * b.val + t.val, hlt⟩ : Fin 271) =
      ⟨68 * (3 : Fin 4).val + s.val, hs⟩ := by
    apply Fin.ext
    dsimp [b, t]
    omega
  simpa only [heq] using h b t hlt

end Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual3Checks
