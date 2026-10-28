module

public import Theory.AlgebraicGroup.RootSystems.F4WeightAction.TwistedCoordinates
/-!
# Coordinate formulas for odd exceptional iterates

Two exceptional parameter steps square each fundamental orbit sum. Induction
therefore gives the exact exponents 2^(m+1) and 2^m for the odd iterate
2m+1 that defines the finite Ree fixed group.

Source: Steinberg (1963), §12.2.
-/

public noncomputable section
namespace Theory.AlgebraicGroup.StandardRootSystem.F4WeightAction
variable {F : Type*} [Field F] [CharP F 2]

lemma fundamentalValue_torusTwist_twice (t : Fin 4 → Fˣ) (i : Fin 4) :
    fundamentalValue (torusTwist (torusTwist t)) i = fundamentalValue t i ^ 2 := by
  rw [fundamentalValue_torusTwist, fundamentalValue_torusTwist]
  fin_cases i <;> simp [Fin.revPerm, Fin.rev]

lemma fundamentalValue_torusTwist_iterate_even (t : Fin 4 → Fˣ) (m : ℕ) (i : Fin 4) :
    fundamentalValue ((torusTwist (F:=F))^[2*m] t) i = fundamentalValue t i ^ (2^m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have he : 2*(m+1)=2+2*m := by omega
    rw [he, Function.iterate_add_apply]
    change fundamentalValue (torusTwist (torusTwist ((torusTwist (F:=F))^[2*m] t))) i = _
    rw [fundamentalValue_torusTwist_twice, ih, ← pow_mul, pow_succ]

lemma fundamentalValue_torusTwist_iterate_odd (t : Fin 4 → Fˣ) (m : ℕ) (i : Fin 4) :
    fundamentalValue ((torusTwist (F:=F))^[2*m+1] t) i =
      if i.val < 2 then fundamentalValue t (Fin.revPerm i) ^ (2^(m+1))
      else fundamentalValue t (Fin.revPerm i) ^ (2^m) := by
  rw [Function.iterate_add_apply]
  change fundamentalValue ((torusTwist (F:=F))^[2*m] (torusTwist t)) i = _
  rw [fundamentalValue_torusTwist_iterate_even, fundamentalValue_torusTwist]
  split_ifs with hi
  · rw [← pow_mul, pow_succ']
  · rfl
end Theory.AlgebraicGroup.StandardRootSystem.F4WeightAction
