module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Representatives
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Data

/-!
# Relator deductions for the first Fi23 Schreier tree

Schreier factors satisfy a product identity. Consequently, if a relator
starts with an A edge and all subsequent factors lie in the candidate
subgroup, its first factor also lies there. Cyclic cuts allow any chosen
edge of a relator to be placed first. The rank checker records exactly
which later A edges may be used in this deduction; B factors follow from
the explicit B-loop hypothesis and the checked tree.

Source: ATLAS F23G1-p31671B0; first prefix bound for GLS3 Table 5.3u.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.FirstTree.Links
open Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate

def symbol (i : Fin 3) : Equiv.Perm (Fin 31671) :=
  if i = 0 then generatorA else if i = 1 then generatorB else generatorB * generatorB

def symbolMap (i : Fin 3) (x : Fin 31671) : Fin 31671 :=
  if i = 0 then sourceA x else if i = 1 then sourceB x else sourceB (sourceB x)

theorem symbolMap_eq (i : Fin 3) (x : Fin 31671) : symbolMap i x = symbol i x := by
  simp only [symbolMap, symbol, ← generatorA_apply_eq_sourceA,
    ← generatorB_apply_eq_sourceB]
  split
  · rfl
  · split <;> rfl

/-- Letters are listed in the order in which they act. -/
def wordValue : List (Fin 3) → Equiv.Perm (Fin 31671)
  | [] => 1
  | s :: w => wordValue w * symbol s

def wordRun : List (Fin 3) → Fin 31671 → Fin 31671
  | [], x => x
  | s :: w, x => wordRun w (symbolMap s x)

theorem wordRun_eq (w : List (Fin 3)) (x : Fin 31671) :
    wordRun w x = wordValue w x := by
  induction w generalizing x with
  | nil => rfl
  | cons s w ih => simp only [wordRun, wordValue, ih, symbolMap_eq, Equiv.Perm.mul_apply]

theorem wordValue_append (u v : List (Fin 3)) :
    wordValue (u ++ v) = wordValue v * wordValue u := by
  induction u with
  | nil => simp [wordValue]
  | cons s u ih => simp only [List.cons_append, wordValue, ih, mul_assoc]

/-- Cutting a relator at any position gives another relator. -/
theorem wordValue_cut (w : List (Fin 3)) (n : Nat) (h : wordValue w = 1) :
    wordValue (w.drop n ++ w.take n) = 1 := by
  have he := congrArg wordValue (List.take_append_drop n w)
  rw [wordValue_append, h] at he
  rw [wordValue_append]
  exact mul_eq_one_comm.mp he

theorem edge_mul (s t : Equiv.Perm (Fin 31671)) (x : Fin 31671) :
    edge (s * t) x = edge s (t x) * edge t x := by
  simp only [edge, Equiv.Perm.mul_apply, mul_assoc, mul_inv_cancel_left]

theorem b_edge_mem
    (hBloops : ∀ x : Fin 31671, generatorB x = x → edge generatorB x ∈ KernelUpperData.first)
    (x : Fin 31671) : edge generatorB x ∈ KernelUpperData.first := by
  by_cases h : generatorB x = x
  · exact hBloops x h
  · rw [b_edge_eq_one x h]
    exact KernelUpperData.first.one_mem

theorem symbol_edge_mem
    (hBloops : ∀ x : Fin 31671, generatorB x = x → edge generatorB x ∈ KernelUpperData.first)
    (i : Fin 3) (x : Fin 31671)
    (hA : i = 0 → edge generatorA x ∈ KernelUpperData.first) :
    edge (symbol i) x ∈ KernelUpperData.first := by
  by_cases h0 : i = 0
  · simpa only [symbol, if_pos h0] using hA h0
  by_cases h1 : i = 1
  · simpa only [symbol, if_neg h0, if_pos h1] using b_edge_mem hBloops x
  · simp only [symbol, if_neg h0, if_neg h1, edge_mul]
    exact KernelUpperData.first.mul_mem (b_edge_mem hBloops _) (b_edge_mem hBloops _)

/-- Every A edge on this path has strictly smaller rank. -/
def pathBelow (rank : Fin 31671 → Nat) (r : Nat) : List (Fin 3) → Fin 31671 → Bool
  | [], _ => true
  | s :: w, x => (decide (s ≠ 0) || decide (rank x < r)) &&
      pathBelow rank r w (symbolMap s x)

theorem pathBelow_mem (rank : Fin 31671 → Nat) (r : Nat)
    (hBloops : ∀ x : Fin 31671, generatorB x = x → edge generatorB x ∈ KernelUpperData.first)
    (ih : ∀ x, rank x < r → edge generatorA x ∈ KernelUpperData.first)
    (w : List (Fin 3)) (x : Fin 31671) (hw : pathBelow rank r w x = true) :
    edge (wordValue w) x ∈ KernelUpperData.first := by
  induction w generalizing x with
  | nil =>
    simp only [wordValue, edge, Equiv.Perm.one_apply, mul_one, inv_mul_cancel]
    exact KernelUpperData.first.one_mem
  | cons s w hw' =>
    simp only [pathBelow, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hw
    rw [wordValue, edge_mul]
    refine KernelUpperData.first.mul_mem ?_ (symbol_edge_mem hBloops s x ?_)
    · exact hw' (symbol s x) (by simpa only [symbolMap_eq] using hw.2)
    · intro hs
      exact ih x (hw.1.resolve_left (fun hn => hn hs))

/-- A relator isolates its first edge once all subsequent edges are known. -/
theorem first_edge_mem (w : List (Fin 3)) (x : Fin 31671)
    (hrel : wordValue (0 :: w) = 1)
    (htail : edge (wordValue w) (generatorA x) ∈ KernelUpperData.first) :
    edge generatorA x ∈ KernelUpperData.first := by
  have he := congrArg (fun p => edge p x) hrel
  simp only [wordValue, symbol, edge_mul] at he
  have hright : edge (1 : Equiv.Perm (Fin 31671)) x = 1 := by
    simp only [edge, Equiv.Perm.one_apply, mul_one, inv_mul_cancel]
  rw [hright] at he
  have eqinv : edge generatorA x = (edge (wordValue w) (generatorA x))⁻¹ :=
    eq_inv_of_mul_eq_one_right he
  rw [eqinv]
  exact KernelUpperData.first.inv_mem htail

end Sporadic.Fischer.Fi23.CentralizerSection.FirstTree.Links
