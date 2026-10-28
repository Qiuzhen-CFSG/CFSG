module

public import Theory.SpecificGroups.Janko3.Model.Order.Level0.ForwardB.SeedsHigh.Data

/-!
# Soundness of the short-block checks for the upper J3 B row

The block-table identities and the 257 transition checks are independent finite
certificates. Their conjunction implies exactly the requested high seed steps.
The word-expansion and seed-coverage identities are already checked in Data.
Source: the ATLAS-derived J3 witnesses in `Order/data/witnesses.json`.
-/

namespace Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsHigh
open Theory.GroupTheory

/-- Correctness of the 72 short-block permutation tables. -/
public abbrev BlockSound : Prop := ∀ b (x : Fin 6156),
  lookup (blockTable b) x.val = run mixedNat (blockWords b) x.val

/-- Pointwise comparison after replacing short words by their packed maps. -/
@[expose] public def Check (i : Fin 257) : Prop :=
  checkFin (fun x : Fin 6156 =>
    run (fun b => lookup (blockTable b)) (leftBlocks i) x.val ==
    run (fun b => lookup (blockTable b)) (rightBlocks i) x.val) = true

public instance (i : Fin 257) : Decidable (Check i) :=
  inferInstanceAs (Decidable (_ = _))

public theorem step_of_check (hblocks : BlockSound) (i : Fin 257) (h : Check i) :
    L0Gen 1 * L0Rep (seedAt i) = L0Rep (L0Act 1 (seedAt i)) *
      evalWord L1Gen (L0Factor 1 (seedAt i)) := by
  apply Equiv.ext
  intro x
  apply Fin.ext
  have hx := allFin (fun x : Fin 6156 =>
    run (fun b => lookup (blockTable b)) (leftBlocks i) x.val =
    run (fun b => lookup (blockTable b)) (rightBlocks i) x.val) h x
  rw [run_blocks_eq blockWords blockTable hblocks,
    run_blocks_eq blockWords blockTable hblocks,
    (words_expand i).1, (words_expand i).2,
    evalWord_append, eval_lift0, eval_lift0, eval_lift1, fastL0Gen_eq] at hx
  exact hx

/-- Four independent batches cover the 256 seeds after the first. -/
@[expose] public def batchIndex (b : Fin 4) (i : Fin 64) : Fin 257 :=
  ⟨1 + 64 * b.val + i.val, by omega⟩

public theorem checks_of_batches (hzero : Check 0)
    (hb : ∀ b i, Check (batchIndex b i)) : ∀ i, Check i := by
  intro i
  by_cases hi : i.val = 0
  · have he : i = 0 := Fin.ext hi
    simpa only [he] using hzero
  · let b : Fin 4 := ⟨(i.val - 1) / 64, by omega⟩
    let s : Fin 64 := ⟨(i.val - 1) % 64, by omega⟩
    have he : batchIndex b s = i := by
      apply Fin.ext
      dsimp [batchIndex, b, s]
      omega
    simpa only [he] using hb b s

/-- Assembly interface; the final seed theorem discharges both finite premises. -/
public theorem seedStepsHigh_of_checks (hblocks : BlockSound) (hchecks : ∀ i, Check i) :
    ∀ r : Fin 6156, Seed r → 4714 ≤ r.val →
      L0Gen 1 * L0Rep r = L0Rep (L0Act 1 r) * evalWord L1Gen (L0Factor 1 r) := by
  intro r hr hge
  have hi := step_of_check hblocks (seedIndex r) (hchecks _)
  simpa only [seedAt_index r hr hge] using hi

end Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsHigh
