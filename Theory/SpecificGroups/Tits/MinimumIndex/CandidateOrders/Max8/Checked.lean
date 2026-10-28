module

public import Theory.SpecificGroups.Tits.MinimumIndex.CandidateOrders.Max8.Level0Checks00
public import Theory.SpecificGroups.Tits.MinimumIndex.CandidateOrders.Max8.Level0Checks10
public import Theory.SpecificGroups.Tits.MinimumIndex.CandidateOrders.Max8.Level1Checks00
public import Theory.SpecificGroups.Tits.MinimumIndex.CandidateOrders.Max8.Level2Checks00
public import Theory.SpecificGroups.Tits.MinimumIndex.CandidateOrders.Max8.Level3Checks00
import Mathlib.Tactic.FinCases

/-! Assembly of the finite covers; see `Data.lean` for source and conventions. -/

namespace Tits.MinimumIndexCandidates.OrderCertificate.Max8
open Theory.GroupTheory

public theorem L0step (i : Fin 4) (r : Fin 100) (x : Fin 1600) :
    L0Gen i (L0Rep r x) =
      L0Rep (L0Act i r) (evalWord L1Gen (L0Factor i r) x) := by
  have batches (b : Fin 20) : L0Batch b := by
    fin_cases b
    · exact L0batch0
    · exact L0batch1
    · exact L0batch2
    · exact L0batch3
    · exact L0batch4
    · exact L0batch5
    · exact L0batch6
    · exact L0batch7
    · exact L0batch8
    · exact L0batch9
    · exact L0batch10
    · exact L0batch11
    · exact L0batch12
    · exact L0batch13
    · exact L0batch14
    · exact L0batch15
    · exact L0batch16
    · exact L0batch17
    · exact L0batch18
    · exact L0batch19
  let b : Fin 20 := ⟨r.val / 5, by omega⟩
  let s : Fin 5 := ⟨r.val % 5, Nat.mod_lt _ (by decide)⟩
  have hrs : L0BatchRep b s = r := by
    apply Fin.ext
    dsimp [L0BatchRep, b, s]
    omega
  simpa only [hrs] using batches b i s x

public theorem L0card_step : Nat.card L0H ≤ 100 * Nat.card L1H :=
  card_le_of_map_transitions L0Gen L0Inv L0Inv_spec
    L1Gen L1Inv L1Inv_spec L0Rep L0Act L0Factor 0
    L0Rep_initial L0step

public theorem L1step (i : Fin 4) (r : Fin 2) (x : Fin 1600) :
    L1Gen i (L1Rep r x) =
      L1Rep (L1Act i r) (evalWord L2Gen (L1Factor i r) x) := by
  have batches (b : Fin 1) : L1Batch b := by
    fin_cases b
    · exact L1batch0
  let b : Fin 1 := ⟨r.val / 2, by omega⟩
  let s : Fin 2 := ⟨r.val % 2, Nat.mod_lt _ (by decide)⟩
  have hrs : L1BatchRep b s = r := by
    apply Fin.ext
    dsimp [L1BatchRep, b, s]
    omega
  simpa only [hrs] using batches b i s x

public theorem L1card_step : Nat.card L1H ≤ 2 * Nat.card L2H :=
  card_le_of_map_transitions L1Gen L1Inv L1Inv_spec
    L2Gen L2Inv L2Inv_spec L1Rep L1Act L1Factor 0
    L1Rep_initial L1step

public theorem L2step (i : Fin 4) (r : Fin 2) (x : Fin 1600) :
    L2Gen i (L2Rep r x) =
      L2Rep (L2Act i r) (evalWord L3Gen (L2Factor i r) x) := by
  have batches (b : Fin 1) : L2Batch b := by
    fin_cases b
    · exact L2batch0
  let b : Fin 1 := ⟨r.val / 2, by omega⟩
  let s : Fin 2 := ⟨r.val % 2, Nat.mod_lt _ (by decide)⟩
  have hrs : L2BatchRep b s = r := by
    apply Fin.ext
    dsimp [L2BatchRep, b, s]
    omega
  simpa only [hrs] using batches b i s x

public theorem L2card_step : Nat.card L2H ≤ 2 * Nat.card L3H :=
  card_le_of_map_transitions L2Gen L2Inv L2Inv_spec
    L3Gen L3Inv L3Inv_spec L2Rep L2Act L2Factor 0
    L2Rep_initial L2step

public theorem L3step (i : Fin 2) (r : Fin 3) (x : Fin 1600) :
    L3Gen i (L3Rep r x) =
      L3Rep (L3Act i r) (evalWord L4Gen (L3Factor i r) x) := by
  have batches (b : Fin 1) : L3Batch b := by
    fin_cases b
    · exact L3batch0
  let b : Fin 1 := ⟨r.val / 3, by omega⟩
  let s : Fin 3 := ⟨r.val % 3, Nat.mod_lt _ (by decide)⟩
  have hrs : L3BatchRep b s = r := by
    apply Fin.ext
    dsimp [L3BatchRep, b, s]
    omega
  simpa only [hrs] using batches b i s x

public theorem L3card_step : Nat.card L3H ≤ 3 * Nat.card L4H :=
  card_le_of_map_transitions L3Gen L3Inv L3Inv_spec
    L4Gen L4Inv L4Inv_spec L3Rep L3Act L3Factor 0
    L3Rep_initial L3step

public theorem card_bound : Nat.card L0H ≤ 1200 := by
  have h0 := L0card_step
  have h1 := L1card_step
  have h2 := L2card_step
  have h3 := L3card_step
  rw [L4card] at h3
  omega

end Tits.MinimumIndexCandidates.OrderCertificate.Max8
