module

public import Theory.SpecificGroups.Tits.MinimumIndex.CandidateOrders.Max2.Level0Checks00
public import Theory.SpecificGroups.Tits.MinimumIndex.CandidateOrders.Max2.Level0Checks10
public import Theory.SpecificGroups.Tits.MinimumIndex.CandidateOrders.Max2.Level1Checks00
public import Theory.SpecificGroups.Tits.MinimumIndex.CandidateOrders.Max2.Level2Checks00
public import Theory.SpecificGroups.Tits.MinimumIndex.CandidateOrders.Max2.Level3Checks00
public import Theory.SpecificGroups.Tits.MinimumIndex.CandidateOrders.Max2.Level4Checks00
public import Theory.SpecificGroups.Tits.MinimumIndex.CandidateOrders.Max2.Level5Checks00
import Mathlib.Tactic.FinCases

/-! Assembly of the finite covers; see `Data.lean` for source and conventions. -/

namespace Tits.MinimumIndexCandidates.OrderCertificate.Max2
open Theory.GroupTheory

public theorem L0step (i : Fin 4) (r : Fin 52) (x : Fin 1600) :
    L0Gen i (L0Rep r x) =
      L0Rep (L0Act i r) (evalWord L1Gen (L0Factor i r) x) := by
  have batches (b : Fin 11) : L0Batch b := by
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
  let b : Fin 11 := ⟨r.val / 5, by omega⟩
  let s : Fin 5 := ⟨r.val % 5, Nat.mod_lt _ (by decide)⟩
  have hrs : L0BatchRep b s = r := by
    apply Fin.ext
    dsimp [L0BatchRep, b, s]
    omega
  simpa only [hrs] using batches b i s x

public theorem L0card_step : Nat.card L0H ≤ 52 * Nat.card L1H :=
  card_le_of_map_transitions L0Gen L0Inv L0Inv_spec
    L1Gen L1Inv L1Inv_spec L0Rep L0Act L0Factor 0
    L0Rep_initial L0step

public theorem L1step (i : Fin 4) (r : Fin 6) (x : Fin 1600) :
    L1Gen i (L1Rep r x) =
      L1Rep (L1Act i r) (evalWord L2Gen (L1Factor i r) x) := by
  have batches (b : Fin 2) : L1Batch b := by
    fin_cases b
    · exact L1batch0
    · exact L1batch1
  let b : Fin 2 := ⟨r.val / 5, by omega⟩
  let s : Fin 5 := ⟨r.val % 5, Nat.mod_lt _ (by decide)⟩
  have hrs : L1BatchRep b s = r := by
    apply Fin.ext
    dsimp [L1BatchRep, b, s]
    omega
  simpa only [hrs] using batches b i s x

public theorem L1card_step : Nat.card L1H ≤ 6 * Nat.card L2H :=
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

public theorem L3step (i : Fin 6) (r : Fin 3) (x : Fin 1600) :
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

public theorem L4step (i : Fin 4) (r : Fin 2) (x : Fin 1600) :
    L4Gen i (L4Rep r x) =
      L4Rep (L4Act i r) (evalWord L5Gen (L4Factor i r) x) := by
  have batches (b : Fin 1) : L4Batch b := by
    fin_cases b
    · exact L4batch0
  let b : Fin 1 := ⟨r.val / 2, by omega⟩
  let s : Fin 2 := ⟨r.val % 2, Nat.mod_lt _ (by decide)⟩
  have hrs : L4BatchRep b s = r := by
    apply Fin.ext
    dsimp [L4BatchRep, b, s]
    omega
  simpa only [hrs] using batches b i s x

public theorem L4card_step : Nat.card L4H ≤ 2 * Nat.card L5H :=
  card_le_of_map_transitions L4Gen L4Inv L4Inv_spec
    L5Gen L5Inv L5Inv_spec L4Rep L4Act L4Factor 0
    L4Rep_initial L4step

public theorem L5step (i : Fin 2) (r : Fin 3) (x : Fin 1600) :
    L5Gen i (L5Rep r x) =
      L5Rep (L5Act i r) (evalWord L6Gen (L5Factor i r) x) := by
  have batches (b : Fin 1) : L5Batch b := by
    fin_cases b
    · exact L5batch0
  let b : Fin 1 := ⟨r.val / 3, by omega⟩
  let s : Fin 3 := ⟨r.val % 3, Nat.mod_lt _ (by decide)⟩
  have hrs : L5BatchRep b s = r := by
    apply Fin.ext
    dsimp [L5BatchRep, b, s]
    omega
  simpa only [hrs] using batches b i s x

public theorem L5card_step : Nat.card L5H ≤ 3 * Nat.card L6H :=
  card_le_of_map_transitions L5Gen L5Inv L5Inv_spec
    L6Gen L6Inv L6Inv_spec L5Rep L5Act L5Factor 0
    L5Rep_initial L5step

public theorem card_bound : Nat.card L0H ≤ 11232 := by
  have h0 := L0card_step
  have h1 := L1card_step
  have h2 := L2card_step
  have h3 := L3card_step
  have h4 := L4card_step
  have h5 := L5card_step
  rw [L6card] at h5
  omega

end Tits.MinimumIndexCandidates.OrderCertificate.Max2
