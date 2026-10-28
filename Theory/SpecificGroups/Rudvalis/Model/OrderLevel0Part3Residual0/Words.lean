module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual0.Nat

/-!
# Explicit words for Rudvalis residual group 0

Decode the three fixed words once, with checked equalities to the original
witnesses. The individual point checks then evaluate those explicit lists.
This avoids repeating word decoding in each kernel reduction. Source:
`OrderLevel0Data`; the action comparison is `Residual0Nat.ofSlices`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual0Nat

@[expose] public def wordSlice (i : Fin 2) (w u v : List (Fin 4)) (b : Fin 29) : Bool :=
  checkFin (fun x : Fin 140 =>
    decide (gen0 (i.castLE (by decide)) (eval gen0 w (140 * b.val + x.val)) =
      eval gen0 u (eval gen1 v (140 * b.val + x.val))))

/-- Checked word expansions transfer the explicit checks to the source witnesses. -/
public theorem ofWordSlices (i : Fin 2) (r : Fin 4060) (w u v : List (Fin 4))
    (hw : L0RepWord r = w)
    (hu : L0RepWord (L0Act (i.castLE (by decide)) r) = u)
    (hv : L0Factor (i.castLE (by decide)) r = v)
    (h : ∀ b, wordSlice i w u v b = true) : stepCheck i r := by
  apply ofSlices
  intro b
  simpa only [slice, point, hw, hu, hv, wordSlice] using h b

end Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual0Nat
