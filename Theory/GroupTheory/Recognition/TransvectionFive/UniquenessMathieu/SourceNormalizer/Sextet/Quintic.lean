module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Sextet.Stabilizer

/-!
# Quintic symmetries fixing the exceptional four-groups

For each of the six exceptional binary two-spaces, a specified additive
symmetry of order dividing five fixes exactly that two-space. Linearity is
proved once from XOR distributivity; small kernel-checked certificates verify
the fifth powers, preservation of the exceptional locus, and fixed sets.
These elements detect the fixed subgroup of the S₅ stabilizer's residual.

Source: Aschbacher, *Sporadic Groups* (1994), 40.4(2), p.218.
-/

public section

namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer.Sextet
open UniquenessLinear.PlaneCensus (Code)
private def quinticImages : Fin 6 → Fin 6 → Code :=
  ![![42,25,49,61,19,62], ![43,45,19,53,5,10], ![57,51,58,55,46,47],
    ![7,49,25,56,62,19], ![19,42,43,10,61,53], ![63,5,10,7,40,25]]
private def quinticEval (i : Fin 6) (x : Code) : Code :=
  (if x.getLsbD 0 then quinticImages i 0 else 0) ^^^
  (if x.getLsbD 1 then quinticImages i 1 else 0) ^^^
  (if x.getLsbD 2 then quinticImages i 2 else 0) ^^^
  (if x.getLsbD 3 then quinticImages i 3 else 0) ^^^
  (if x.getLsbD 4 then quinticImages i 4 else 0) ^^^
  (if x.getLsbD 5 then quinticImages i 5 else 0)
private theorem quintic_fifth : ∀ (i : Fin 6) (x : Code),
    quinticEval i (quinticEval i (quinticEval i (quinticEval i (quinticEval i x)))) = x := by decide +kernel
private theorem bit_xor (a b : Bool) (v : Code) :
    (if a ^^ b then v else 0) = (if a then v else 0) ^^^ (if b then v else 0) := by
  cases a <;> cases b <;> simp
private theorem quintic_xor (i : Fin 6) (x y : Code) :
    quinticEval i (x ^^^ y) = quinticEval i x ^^^ quinticEval i y := by
  simp only [quinticEval, BitVec.getLsbD_xor, bit_xor]
  ac_rfl
private theorem quintic_exceptional : ∀ (i : Fin 6) (x : Code),
    exceptional (quinticEval i x) = exceptional x := by decide +kernel
private theorem quintic_fixed : ∀ (i : Fin 6) (x : Code),
    quinticEval i x = x ↔ x ∈ line i := by decide +kernel

def quintic (i : Fin 6) : symmetryGroup :=
  ⟨{ toFun := quinticEval i
     invFun := fun x => quinticEval i (quinticEval i (quinticEval i (quinticEval i x)))
     left_inv := quintic_fifth i
     right_inv := quintic_fifth i },
    (mem_symmetryGroup _).mpr ⟨quintic_xor i, quintic_exceptional i⟩⟩
theorem quintic_pow (i : Fin 6) : quintic i ^ 5 = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  exact quintic_fifth i x

theorem quintic_fixed_iff (i : Fin 6) (x : Code) : (quintic i).val x = x ↔ x ∈ line i :=
  quintic_fixed i x
end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer.Sextet
