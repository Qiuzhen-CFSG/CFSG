module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Nat

/-!
# Explicit-word checks for Rudvalis part-6 block 0

Decode the three words of a transition once, then check their actions in
slices of twenty points. This avoids repeatedly decoding the packed ATLAS
witnesses in `OrderLevel0Data` during each point calculation. The word
identifications and every action check are verified by Lean's kernel.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block0

@[expose] public def wordSlice (i : Fin 2) (w v f : List (Fin 4)) (b : Fin 203) : Bool :=
  checkFin (fun x : Fin 20 => decide
    (Part6Nat.gen0 (i.castLE (by decide))
        (Part6Nat.eval Part6Nat.gen0 w (20 * b.val + x.val)) =
      Part6Nat.eval Part6Nat.gen0 v
        (Part6Nat.eval Part6Nat.gen1 f (20 * b.val + x.val))))

public theorem ofWords (i : Fin 2) (r : Fin 4060) (w v f : List (Fin 4))
    (hw : L0RepWord r = w)
    (hv : L0RepWord (L0Act (i.castLE (by decide)) r) = v)
    (hf : L0Factor (i.castLE (by decide)) r = f)
    (h : ∀ b, wordSlice i w v f b = true) : stepCheck i r := by
  apply Part6Nat.ofSlices
  intro b
  simpa only [Part6Nat.slice, Part6Nat.point, hw, hv, hf, wordSlice] using h b

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block0
