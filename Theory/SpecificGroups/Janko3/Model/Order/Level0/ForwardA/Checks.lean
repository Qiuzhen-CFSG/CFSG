module

public import Theory.SpecificGroups.Janko3.Model.Order.Level0.ForwardA.Pairing
import Lean.Elab.Tactic.Omega

/-!
# Bounded point checks for an exceptional A transition

The 6156 letters are partitioned into 18 blocks of 18 groups of 19 letters.
Checking each block separately bounds the size of a single kernel reduction.
Only the packed, previously certified generator permutations are evaluated.
The soundness theorem turns these point checks into the original transition.
Source: ATLAS J3G1-p6156B0 and `Order/data/witnesses.json`.
-/

namespace Sporadic.Janko3.OrderCertificate.Level0
open Theory.GroupTheory

@[expose] public def aCheckPoint (b k : Fin 18) (x : Fin 19) : Fin 6156 :=
  ⟨342 * b.val + 19 * k.val + x.val, by omega⟩

@[expose] public def aPointBlock (r : Fin 6156) (b : Fin 18) : Prop :=
  ∀ k : Fin 18, ∀ x : Fin 19,
    (fastL0Gen 0 * evalWord fastL0Gen (L0RepWord r)) (aCheckPoint b k x) =
    (evalWord fastL0Gen (L0RepWord (L0Act 0 r)) *
      evalWord L1Gen (L0Factor 0 r)) (aCheckPoint b k x)

public theorem forwardAStep_of_pointBlocks (r : Fin 6156)
    (h : ∀ b, aPointBlock r b) : forwardAStep r := by
  apply Equiv.ext
  intro x
  let b : Fin 18 := ⟨x.val / 342, by omega⟩
  let k : Fin 18 := ⟨x.val % 342 / 19, by omega⟩
  let j : Fin 19 := ⟨x.val % 19, by omega⟩
  have hx : aCheckPoint b k j = x := by
    apply Fin.ext
    dsimp [aCheckPoint, b, k, j]
    omega
  have hh := h b k j
  simpa only [hx, fastL0Gen_eq, L0Rep] using hh

end Sporadic.Janko3.OrderCertificate.Level0
