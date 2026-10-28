module

public import Theory.SpecificGroups.Janko3.Model.Order.Level0.Reduction
import Lean.Elab.Tactic.Omega

/-!
# Batching the forward J3 Schreier transitions

Each forward generator has 6156 transitions, partitioned into 324 batches of
19 representatives. A batch can use word normalization for the free-product
relations and pointwise permutation checks for the remaining identities.
The soundness lemmas isolate numerical certificates from final assembly.
Source: `Order/data/witnesses.json`, from ATLAS J3G1-p6156B0.
-/

namespace Sporadic.Janko3.OrderCertificate.Level0
open Theory.GroupTheory

/-- A complete transition row for one signed generator. -/
public abbrev ForwardRow (i : Fin 4) : Prop := ∀ r : Fin 6156,
  L0Gen i * L0Rep r = L0Rep (L0Act i r) * evalWord L1Gen (L0Factor i r)

@[expose] public def batchRep (b : Fin 324) (r : Fin 19) : Fin 6156 :=
  ⟨19 * b.val + r.val, by omega⟩

@[expose] public def stepBatch (i : Fin 4) (b : Fin 324) : Prop :=
  ∀ r : Fin 19, L0Gen i * L0Rep (batchRep b r) =
    L0Rep (L0Act i (batchRep b r)) * evalWord L1Gen (L0Factor i (batchRep b r))

@[expose] public def stepBatchCheck (i : Fin 4) (b : Fin 324) : Prop :=
  ∀ r : Fin 19, algebraic i (batchRep b r) ∨ fastCheck i (batchRep b r)

public theorem ofStepBatchCheck (i : Fin 4) (b : Fin 324)
    (h : stepBatchCheck i b) : stepBatch i b :=
  fun r => step_of_check i (batchRep b r) (h r)

/-- The finite batches cover every representative exactly at its quotient and remainder. -/
public theorem forwardRow_of_batches (i : Fin 4) (h : ∀ b, stepBatch i b) :
    ForwardRow i := by
  intro r
  let b : Fin 324 := ⟨r.val / 19, by omega⟩
  let s : Fin 19 := ⟨r.val % 19, by omega⟩
  have hrs : batchRep b s = r := by
    apply Fin.ext
    dsimp [batchRep, b, s]
    omega
  simpa only [hrs] using h b s

end Sporadic.Janko3.OrderCertificate.Level0
