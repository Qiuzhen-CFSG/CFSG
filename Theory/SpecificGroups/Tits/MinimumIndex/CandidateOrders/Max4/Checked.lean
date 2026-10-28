module

public import Theory.SpecificGroups.Tits.MinimumIndex.CandidateOrders.Max4.Level0Checks00
public import Theory.SpecificGroups.Tits.MinimumIndex.CandidateOrders.Max4.Level0Checks10
public import Theory.SpecificGroups.Tits.MinimumIndex.CandidateOrders.Max4.Level0Checks20
public import Theory.SpecificGroups.Tits.MinimumIndex.CandidateOrders.Max4.Level0Checks30
public import Theory.SpecificGroups.Tits.MinimumIndex.CandidateOrders.Max4.Level0Checks40
public import Theory.SpecificGroups.Tits.MinimumIndex.CandidateOrders.Max4.Level0Checks50
public import Theory.SpecificGroups.Tits.MinimumIndex.CandidateOrders.Max4.Level1Checks00
public import Theory.SpecificGroups.Tits.MinimumIndex.CandidateOrders.Max4.Level2Checks00
import Mathlib.Tactic.FinCases

/-! Assembly of the finite covers; see `Data.lean` for source and conventions. -/

namespace Tits.MinimumIndexCandidates.OrderCertificate.Max4
open Theory.GroupTheory

public theorem L0step (i : Fin 4) (r : Fin 300) (x : Fin 1600) :
    L0Gen i (L0Rep r x) =
      L0Rep (L0Act i r) (evalWord L1Gen (L0Factor i r) x) := by
  have batches (b : Fin 60) : L0Batch b := by
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
    · exact L0batch20
    · exact L0batch21
    · exact L0batch22
    · exact L0batch23
    · exact L0batch24
    · exact L0batch25
    · exact L0batch26
    · exact L0batch27
    · exact L0batch28
    · exact L0batch29
    · exact L0batch30
    · exact L0batch31
    · exact L0batch32
    · exact L0batch33
    · exact L0batch34
    · exact L0batch35
    · exact L0batch36
    · exact L0batch37
    · exact L0batch38
    · exact L0batch39
    · exact L0batch40
    · exact L0batch41
    · exact L0batch42
    · exact L0batch43
    · exact L0batch44
    · exact L0batch45
    · exact L0batch46
    · exact L0batch47
    · exact L0batch48
    · exact L0batch49
    · exact L0batch50
    · exact L0batch51
    · exact L0batch52
    · exact L0batch53
    · exact L0batch54
    · exact L0batch55
    · exact L0batch56
    · exact L0batch57
    · exact L0batch58
    · exact L0batch59
  let b : Fin 60 := ⟨r.val / 5, by omega⟩
  let s : Fin 5 := ⟨r.val % 5, Nat.mod_lt _ (by decide)⟩
  have hrs : L0BatchRep b s = r := by
    apply Fin.ext
    dsimp [L0BatchRep, b, s]
    omega
  simpa only [hrs] using batches b i s x

public theorem L0card_step : Nat.card L0H ≤ 300 * Nat.card L1H :=
  card_le_of_map_transitions L0Gen L0Inv L0Inv_spec
    L1Gen L1Inv L1Inv_spec L0Rep L0Act L0Factor 0
    L0Rep_initial L0step

public theorem L1step (i : Fin 4) (r : Fin 13) (x : Fin 1600) :
    L1Gen i (L1Rep r x) =
      L1Rep (L1Act i r) (evalWord L2Gen (L1Factor i r) x) := by
  have batches (b : Fin 3) : L1Batch b := by
    fin_cases b
    · exact L1batch0
    · exact L1batch1
    · exact L1batch2
  let b : Fin 3 := ⟨r.val / 5, by omega⟩
  let s : Fin 5 := ⟨r.val % 5, Nat.mod_lt _ (by decide)⟩
  have hrs : L1BatchRep b s = r := by
    apply Fin.ext
    dsimp [L1BatchRep, b, s]
    omega
  simpa only [hrs] using batches b i s x

public theorem L1card_step : Nat.card L1H ≤ 13 * Nat.card L2H :=
  card_le_of_map_transitions L1Gen L1Inv L1Inv_spec
    L2Gen L2Inv L2Inv_spec L1Rep L1Act L1Factor 0
    L1Rep_initial L1step

public theorem L2step (i : Fin 2) (r : Fin 2) (x : Fin 1600) :
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

public theorem card_bound : Nat.card L0H ≤ 7800 := by
  have h0 := L0card_step
  have h1 := L1card_step
  have h2 := L2card_step
  rw [L3card] at h2
  omega

end Tits.MinimumIndexCandidates.OrderCertificate.Max4
