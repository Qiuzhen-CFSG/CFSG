module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part2ResidualReduction
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Nat

/-!
# Specialized word checks for the first Rudvalis part-2 residual batch

The 72 fixed transitions are split into three intervals of 24. To avoid
repeatedly decoding the source words during each numerical slice, the evaluator
accepts explicit representative and factor words. Equalities with the prescribed
words transfer its checks to the original transition, without changing witnesses.

Each permutation identity is recovered from 203 slices of 20 points using
`Part6Nat.ofSlices`. Source: `OrderLevel0Data`, the residual enumeration in
`OrderLevel0Part2ResidualReduction`, and the certified `OrderLevel0Part6Nat`
evaluator. No external computation is used as a proof.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part2Residual.Residual0Checks

/-- One third of the first residual batch, with the original residual indices. -/
@[expose] public def block (g : Fin 3) : Prop :=
  ∀ s : Fin 24, residualCheck ⟨24 * g.val + s.val, by omega⟩

/-- The three independently checked intervals cover residuals 0 through 71. -/
public theorem residuals0_of_blocks (h : ∀ g : Fin 3, block g) : residualBatch 0 := by
  intro s hs
  have hk := h ⟨s.val / 24, by omega⟩ ⟨s.val % 24, by omega⟩
  change residualCheck ⟨24 * (s.val / 24) + s.val % 24, _⟩ at hk
  have heq : (⟨24 * (s.val / 24) + s.val % 24, by omega⟩ : Fin 285) =
      ⟨72 * (0 : Fin 4).val + s.val, hs⟩ := by
    apply Fin.ext
    simp only [Fin.val_zero, Nat.mul_zero, Nat.zero_add]
    omega
  exact heq ▸ hk

/-- Evaluate an explicit pair of representatives and the intervening factor. -/
@[expose] public def point (i : Fin 2) (u v w : List (Fin 4)) (x : Nat) : Bool :=
  decide (Part6Nat.gen0 (i.castLE (by decide)) (Part6Nat.eval Part6Nat.gen0 u x) =
    Part6Nat.eval Part6Nat.gen0 v (Part6Nat.eval Part6Nat.gen1 w x))

/-- Twenty-point checks with the source words already expanded. -/
@[expose] public def slice (i : Fin 2) (u v w : List (Fin 4)) (c : Fin 203) : Bool :=
  checkFin (fun x : Fin 20 => point i u v w (20 * c.val + x.val))

/-- Explicit-word checks prove precisely the prescribed source transition. -/
public theorem ofSlices (i : Fin 2) (r : Fin 4060) (u v w : List (Fin 4))
    (hu : L0RepWord r = u)
    (hv : L0RepWord (L0Act (i.castLE (by decide)) r) = v)
    (hw : L0Factor (i.castLE (by decide)) r = w)
    (h : ∀ c : Fin 203, slice i u v w c = true) : stepCheck i r := by
  apply Part6Nat.ofSlices
  intro c
  simpa only [Part6Nat.slice, Part6Nat.point, hu, hv, hw, slice, point] using h c

end Rudvalis.OrderCertificate.ForwardReduction.Part2Residual.Residual0Checks
