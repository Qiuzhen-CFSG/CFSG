module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair
public import Theory.GroupTheory.WordSubgroup

/-!
# Table checking for the second-generator calculation

The compact tables support kernel reduction of pointwise permutation identities.

Source: the retained ATLAS `J2G1-p100B0` permutations; GLS3, Table 5.3g
for the outer-group application. The data-generation scripts supply witnesses
only. Every finite identity claimed in this module is checked by Lean.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.GeneratorPair.SecondOrbitCertificate
open Theory.GroupTheory
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option Elab.async false

/-- Exhaustive Boolean check over a finite interval. -/
def checkFin {n : Nat} (f : Fin n → Bool) : Bool :=
  (List.range n).all (fun i => if h : i < n then f ⟨i, h⟩ else true)

theorem allFin {n : Nat} (P : Fin n → Prop) [DecidablePred P]
    (h : checkFin (fun i => decide (P i)) = true) : ∀ i, P i := by
  intro i
  have hi := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
  simpa only [dif_pos i.isLt, decide_eq_true_eq] using hi

/-- A 100-entry table, with seven bits per entry. -/
def packedMap (code : Nat) (x : Fin 100) : Fin 100 :=
  ⟨(code >>> (7 * x.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩


end Sporadic.LeechRelated.J2.GeneratorPair.SecondOrbitCertificate
