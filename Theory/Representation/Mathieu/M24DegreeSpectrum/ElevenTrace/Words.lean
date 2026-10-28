module

public import Theory.Mathieu.M24.Basic
public import Mathlib.Data.Fin.VecNotation

/-!
# Word certificates for native M₂₄ elements

The alphabet denotes A, B and B⁻¹ for the standard Witt-design generators.
A checked point evaluator lets finite certificates use small tables while
`evaluate` constructs an element of the actual design automorphism group.
This is used by the odd cyclic and Sylow three square-conjugacy certificates.
-/

namespace Sporadic.Mathieu.M24OddCyclic.Words

private def letterPerm : Fin 3 → Equiv.Perm (Fin 24)
  | 0 => m24GeneratorA
  | 1 => m24GeneratorB
  | _ => m24GeneratorB⁻¹

@[expose] public def letterPoint : Fin 3 → Fin 24 → Fin 24
  | 0 => ![20,4,7,17,1,13,9,2,15,6,19,18,21,5,16,8,14,3,11,10,0,12,23,22]
  | 1 => ![23,4,21,9,6,18,1,7,8,15,5,11,12,17,2,3,13,16,10,0,20,14,22,19]
  | _ => ![19,6,14,15,1,10,4,7,8,3,18,11,12,16,21,9,17,13,5,23,20,2,22,0]

private theorem letter_apply : ∀ i x, letterPerm i x = letterPoint i x := by
  decide +kernel

private theorem letter_mem (i : Fin 3) : letterPerm i ∈ M24 := by
  fin_cases i
  · exact m24GeneratorA_mem
  · exact m24GeneratorB_mem
  · exact M24.inv_mem m24GeneratorB_mem

public noncomputable def evaluate : List (Fin 3) → M24
  | [] => 1
  | i :: w => ⟨letterPerm i, letter_mem i⟩ * evaluate w

@[expose] public def wordPoint : List (Fin 3) → Fin 24 → Fin 24
  | [], x => x
  | i :: w, x => letterPoint i (wordPoint w x)

public theorem evaluate_apply (w : List (Fin 3)) (x : Fin 24) :
    (evaluate w).val x = wordPoint w x := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change letterPerm i ((evaluate w).val x) = _
    rw [letter_apply, ih]
    rfl

end Sporadic.Mathieu.M24OddCyclic.Words
