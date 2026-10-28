module

public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.GroupTheory.QuasithinBasic
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Mathlib.Algebra.CharP.Two

/-!
# An elementary subgroup of order 64 in PSL₅(2)

The six entries in the upper-right 2-by-3 block give commuting involutory
linear maps on the binary five-space. Evaluating on the last three basis
vectors proves injectivity. The genuine matrix-action equivalence
PSL₅(2) ≃ GL₅(2) transports this elementary subgroup to the projective model.
Entrywise field transport gives the same result for every field of order two.

Source: Aschbacher–Smith, 16.1.7(3e), printed p.1172, and the exceptional
rank comparison in 16.3.9, printed p.1180.
-/

namespace Theory.SpecificGroups.PSL5Two
open Subgroup Theory.GroupTheory

open BinaryLinear
open scoped CharTwo

private abbrev V5 := Fin 5 → ZMod 2

private def sixCorrection (a : Fin 2 → Fin 3 → ZMod 2) (v : V5) : V5 :=
  fun k => if k = 0 then a 0 0 * v 2 + a 0 1 * v 3 + a 0 2 * v 4
    else if k = 1 then a 1 0 * v 2 + a 1 1 * v 3 + a 1 2 * v 4 else 0

private def sixMap (a : Fin 2 → Fin 3 → ZMod 2) : BinaryLinear.GL V5 where
  toFun v := v + sixCorrection a v
  invFun v := v + sixCorrection a v
  map_add' v w := by
    funext i
    fin_cases i <;> simp [sixCorrection] <;> ring
  map_smul' c v := by
    funext i
    fin_cases i <;> simp [sixCorrection] <;> ring
  left_inv v := by
    have hc : sixCorrection a (v + sixCorrection a v) = sixCorrection a v := by
      funext i
      fin_cases i <;> simp [sixCorrection]
    simp only [hc]
    funext i
    fin_cases i <;> simp [sixCorrection, add_assoc]
  right_inv v := by
    have hc : sixCorrection a (v + sixCorrection a v) = sixCorrection a v := by
      funext i
      fin_cases i <;> simp [sixCorrection]
    simp only [hc]
    funext i
    fin_cases i <;> simp [sixCorrection, add_assoc]

private theorem sixMap_add (a b : Fin 2 → Fin 3 → ZMod 2) :
    sixMap (a + b) = sixMap a * sixMap b := by
  ext v i
  fin_cases i <;> simp [sixMap, sixCorrection, LinearEquiv.mul_apply] <;> ring

private def sixHom : Multiplicative (Fin 2 → Fin 3 → ZMod 2) →* BinaryLinear.GL V5 where
  toFun x := sixMap x.toAdd
  map_one' := by
    apply LinearEquiv.ext
    intro v
    funext i
    fin_cases i <;> simp [sixMap, sixCorrection]
  map_mul' x y := by
    rw [toAdd_mul]
    exact sixMap_add _ _

private theorem sixHom_injective : Function.Injective sixHom := by
  intro x y hxy
  apply Multiplicative.toAdd.injective
  funext i j
  have hh := congrArg (fun g : BinaryLinear.GL V5 =>
    g (Pi.single (⟨j.val + 2, by omega⟩ : Fin 5) 1) (⟨i.val, by omega⟩ : Fin 5)) hxy
  fin_cases i <;> fin_cases j <;>
    simpa [sixHom, sixMap, sixCorrection, Pi.single_apply] using hh

public theorem six_le_primeRank :
    6 ≤ primeRank 2 (Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2)) := by
  let A := Multiplicative (Fin 2 → Fin 3 → ZMod 2)
  let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
  let _ : CommGroup A := inferInstance
  have hpow : ∀ a : A, a ^ 2 = 1 := by
    intro a
    change Multiplicative.ofAdd a.toAdd ^ 2 = 1
    rw [pow_two, ← ofAdd_add, ← ofAdd_zero]
    congr 1
    funext i j
    simp
  have hcard : Nat.card A = 2 ^ 6 := by
    change Nat.card (Fin 2 → Fin 3 → ZMod 2) = 2 ^ 6
    simp [ZMod.card]
  let e := BinaryLinear.OuterCyclic.projectiveEquivLinear (n := 5) (by omega)
  let f : A →* Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2) :=
    e.symm.toMonoidHom.comp sixHom
  have hf : Function.Injective f := by
    intro x y hxy
    apply sixHom_injective
    exact e.symm.injective hxy
  exact primeRank_ge_of_elementary_embedding hpow hcard f hf


/-- The same elementary subgroup over an arbitrary field of order two. -/
public theorem six_le_primeRank_of_card_two {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 2) :
    6 ≤ primeRank 2 (Matrix.ProjectiveSpecialLinearGroup (Fin 5) F) := by
  let := Fintype.ofFinite F
  let e : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
  rw [primeRank_equiv 2 (Atlas.fieldEquivPSL 5 e)]
  exact six_le_primeRank

end Theory.SpecificGroups.PSL5Two
