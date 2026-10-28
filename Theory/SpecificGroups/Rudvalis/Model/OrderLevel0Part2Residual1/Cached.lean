module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2ResidualReduction
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block2.Base

/-!
# Sliced comparison of certified Rudvalis lookup functions

Twenty-point slices cover all 4060 points. This interface lets the residual
certificates reuse products whose lookup functions were already certified in
`OrderLevel0Part6Block2`, instead of evaluating their expanded words again.
Source: the finite permutation checks of `OrderLevel0Reduction`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part2Residual.Residual1Cache

@[expose] public def slice (l r : Nat → Nat) (c : Fin 203) : Bool :=
  checkFin (fun x : Fin 20 => decide (l (20 * c.val + x.val) = r (20 * c.val + x.val)))

public theorem ofSlices {l r : Nat → Nat}
    (h : ∀ c : Fin 203, slice l r c = true) (x : Fin 4060) : l x.val = r x.val := by
  have hx := (checkFin_spec _).mp (h ⟨x.val / 20, by omega⟩) ⟨x.val % 20, by omega⟩
  change decide (l (20 * (x.val / 20) + x.val % 20) =
    r (20 * (x.val / 20) + x.val % 20)) = true at hx
  have heq : 20 * (x.val / 20) + x.val % 20 = x.val := by omega
  simpa only [heq, decide_eq_true_eq] using hx

end Rudvalis.OrderCertificate.ForwardReduction.Part2Residual.Residual1Cache
