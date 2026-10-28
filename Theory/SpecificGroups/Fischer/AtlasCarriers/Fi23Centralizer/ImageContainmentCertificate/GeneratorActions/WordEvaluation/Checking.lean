module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageContainmentCertificate.GeneratorActions.Checking

/-!
# Natural-number checks for shared word tables

These checkers avoid constructing intermediate `Fin` values during numerical
reduction. The two bridge theorems identify them with the existing `mapCheck`
on the literal total table actions, including both modular reductions and
out-of-range padding. Their checked equations are consumed in `Checks*` and
then by the permutation induction in `WordEvaluation.lean`.

Source application: the shared Fi22 image words for GLS3 Table 5.3u.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.ImageContainmentCertificate.GeneratorActions.WordEvaluation

/-- Check a proposed product at one input; padding is ignored. -/
def mulCheck (a b c i : Nat) : Bool :=
  if i < 3510 then
    Nat.beq ((a >>> (12 * (((b >>> (12*i)) % 4096) % 3510))) % 4096 % 3510)
      ((c >>> (12*i)) % 4096 % 3510)
  else true

/-- Check a proposed right inverse at one input; padding is ignored. -/
def invCheck (a b i : Nat) : Bool :=
  if i < 3510 then
    Nat.beq ((a >>> (12 * (((b >>> (12*i)) % 4096) % 3510))) % 4096 % 3510) i
  else true

theorem mapCheck_mul_eq (a b c : Nat) :
    mapCheck (fun x => tableAction a (tableAction b x)) (tableAction c) =
      mulCheck a b c := by
  funext i
  rw [Bool.eq_iff_iff]
  by_cases h : i < 3510 <;>
    simp [mapCheck, mulCheck, tableAction, h, Fin.ext_iff, Nat.beq_eq]

theorem mapCheck_inv_eq (a b : Nat) :
    mapCheck (fun x => tableAction a (tableAction b x)) (fun x : Fin 3510 => x) =
      invCheck a b := by
  funext i
  rw [Bool.eq_iff_iff]
  by_cases h : i < 3510 <;>
    simp [mapCheck, invCheck, tableAction, h, Fin.ext_iff, Nat.beq_eq]

end Sporadic.Fischer.Fi23.CentralizerSection.ImageContainmentCertificate.GeneratorActions.WordEvaluation
