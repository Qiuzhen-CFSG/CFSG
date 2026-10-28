module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.OrbitAction.Data

/-!
# Kernel checks for the cyclic-subgroup orbit

The signed generator transitions check all 100 points. Tree transitions
have positive sign, so their words evaluate to the displayed generators.
Fixed-point codes have checked left inverses on both rows and points.
Source: the ATLAS permutations and Aschbacher, *Sporadic Groups*, 47.5.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.RecognitionGeometry.OrbitAction
open GeneratorPair FirstFusion Data
set_option maxRecDepth 100000
set_option Elab.async false

def xPerm : Equiv.Perm (Fin 100) := (tableA * tableB * tableA * tableB⁻¹) ^ 4

theorem inclusion_x : inclusion x = xPerm := by
  simp only [x, xPerm, map_pow, map_mul, map_inv,
    (show inclusion a = tableA from generatorA_eq_table),
    (show inclusion b = tableB from generatorB_eq_table)]

theorem value_zero : ∀ p : Fin 100, value 0 p = xPerm p := by
  apply allFin
  decide +kernel

theorem word_data : ∀ i : Fin 280, i ≠ 0 →
    (parent i).val < i.val ∧
    words i = words (parent i) ++ [parentLetter i] ∧
    nextRow (parent i) (parentLetter i) = i ∧
    flip (parent i) (parentLetter i) = false := by
  apply allFin
  decide +kernel

theorem identifyRow_spec : ∀ i : Fin 280, identifyRow (rowCode i) = i := by
  apply allFin
  decide +kernel

theorem identifyPoint_spec : ∀ p : Fin 100, identifyPoint (pointCode p) = p := by
  apply allFin
  decide +kernel

def checkSteps (lo count : Nat) : Bool :=
  (List.range count).all fun j =>
    if h : lo + j < 280 then
      checkFin (fun s : Fin 3 => checkFin (fun p : Fin 100 => decide
        (signedValue (nextRow ⟨lo + j, h⟩ s) (flip ⟨lo + j, h⟩ s) p =
          letterValue (invLetter s) (value ⟨lo + j, h⟩ (letterValue s p)))))
    else true

theorem all_steps : checkSteps 0 280 = true := by
  decide +kernel

theorem value_step (i : Fin 280) (s : Fin 3) (p : Fin 100) :
    signedValue (nextRow i s) (flip i s) p =
      (permLetter s)⁻¹ (value i (permLetter s p)) := by
  have hi := List.all_eq_true.mp all_steps i.val (List.mem_range.mpr i.isLt)
  simp only [Nat.zero_add, dif_pos i.isLt] at hi
  have hs := allFin (fun s : Fin 3 => checkFin (fun p : Fin 100 => decide
    (signedValue (nextRow i s) (flip i s) p =
      letterValue (invLetter s) (value i (letterValue s p)))) = true)
    (by simpa only [Bool.decide_eq_true] using hi) s
  have hp := allFin (fun p : Fin 100 =>
    signedValue (nextRow i s) (flip i s) p =
      letterValue (invLetter s) (value i (letterValue s p))) hs p
  rw [letterValue_inv_eq, letterValue_eq] at hp
  exact hp

end Sporadic.LeechRelated.J2.RecognitionGeometry.OrbitAction
