module

public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel
public import Theory.SpecificGroups.PSL3Two.Parabolics.Fano
public import Mathlib.Algebra.Pointwise.Stabilizer
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Tactic.FinCases
/-!
# Coordinate flag stabilizers in SL₃(2)

The standard incident flag is the point e₀ in the plane v₂ = 0. Its two
stabilizers have order 24, and their intersection, the upper triangular
subgroup, has order eight. Membership and cardinalities are checked directly
in binary coordinates.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, I.5.3–4,
printed pp. 419–420.
-/

@[expose] public section
namespace Matrix.PSL3Two
open scoped Pointwise

def flagPoint : Fano.Point := ⟨![1, 0, 0], by decide⟩
def flagLine : Fano.Line := ⟨⟨![0, 0, 1], by decide⟩⟩
theorem flag_incident : Fano.Incident flagPoint flagLine := by decide

def pointParabolicSL : Subgroup SL :=
  MulAction.stabilizer SL {v : Fin 3 → ZMod 2 | v 1 = 0 ∧ v 2 = 0}
def lineParabolicSL : Subgroup SL :=
  MulAction.stabilizer SL {v : Fin 3 → ZMod 2 | v 2 = 0}
def borelSL : Subgroup SL := pointParabolicSL ⊓ lineParabolicSL

theorem mem_pointParabolicSL_iff (g : SL) :
    g ∈ pointParabolicSL ↔ g.val 1 0 = 0 ∧ g.val 2 0 = 0 := by
  rw [pointParabolicSL, MulAction.mem_stabilizer_set' (Set.toFinite _)]
  change (∀ ⦃v : Fin 3 → ZMod 2⦄, v 1 = 0 ∧ v 2 = 0 →
    (g.val.mulVec v) 1 = 0 ∧ (g.val.mulVec v) 2 = 0) ↔ _
  constructor
  · intro h
    simpa [mulVec, dotProduct, Fin.sum_univ_three] using
      h (v := ![1, 0, 0]) (by simp)
  · rintro ⟨h1, h2⟩ v ⟨v1, v2⟩
    simp [mulVec, dotProduct, Fin.sum_univ_three, h1, h2, v1, v2]

theorem mem_lineParabolicSL_iff (g : SL) :
    g ∈ lineParabolicSL ↔ g.val 2 0 = 0 ∧ g.val 2 1 = 0 := by
  rw [lineParabolicSL, MulAction.mem_stabilizer_set' (Set.toFinite _)]
  change (∀ ⦃v : Fin 3 → ZMod 2⦄, v 2 = 0 → (g.val.mulVec v) 2 = 0) ↔ _
  constructor
  · intro h
    constructor
    · simpa [mulVec, dotProduct, Fin.sum_univ_three] using
        h (v := ![1, 0, 0]) (by simp)
    · simpa [mulVec, dotProduct, Fin.sum_univ_three] using
        h (v := ![0, 1, 0]) (by simp)
  · rintro ⟨h1, h2⟩ v v2
    simp [mulVec, dotProduct, Fin.sum_univ_three, h1, h2, v2]

theorem mem_borelSL_iff (g : SL) : g ∈ borelSL ↔
    g.val 1 0 = 0 ∧ g.val 2 0 = 0 ∧ g.val 2 1 = 0 := by
  simp only [borelSL, Subgroup.mem_inf, mem_pointParabolicSL_iff, mem_lineParabolicSL_iff]
  tauto

instance : DecidablePred (· ∈ pointParabolicSL) :=
  fun g => decidable_of_iff _ (mem_pointParabolicSL_iff g).symm
instance : DecidablePred (· ∈ lineParabolicSL) :=
  fun g => decidable_of_iff _ (mem_lineParabolicSL_iff g).symm
instance : DecidablePred (· ∈ borelSL) :=
  fun g => decidable_of_iff _ (mem_borelSL_iff g).symm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem card_pointParabolicSL : Nat.card pointParabolicSL = 24 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem card_lineParabolicSL : Nat.card lineParabolicSL = 24 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem card_borelSL : Nat.card borelSL = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel
end Matrix.PSL3Two
