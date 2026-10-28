module

public import Theory.Representation.SLHigherNaturalFirstCohomology.Elementary
/-!
# An exceptional natural cocycle for SL₃(2)

The table indexes a binary matrix by its nine entries in row order, with the
first entry the least significant bit. Each output encodes a vector in three
bits. Singular matrix indices are unused. It was obtained by solving the
cocycle equations on the six elementary transvections. Lean's kernel checks
compatibility with each transvection; elementary generation then proves the
full cocycle identity for the actual matrix action.

The spare coordinate of every elementary value is one, which prevents this
cocycle from being principal. This is the exceptional class in
Aschbacher--Smith, *The Classification of Quasithin Groups*, Lemma I.1.6(4),
printed p.408 (PDF p.419).
-/

open Matrix Matrix.SpecialLinearGroup
namespace Representation.OneCohomology.SLHigherNatural.SLThreeBinary
private abbrev SL := SpecialLinearGroup (Fin 3) (ZMod 2)
private def binaryCode (a : SL) : Nat :=
  (a 0 0).val + 2 * (a 0 1).val + 4 * (a 0 2).val +
  8 * (a 1 0).val + 16 * (a 1 1).val + 32 * (a 1 2).val +
  64 * (a 2 0).val + 128 * (a 2 1).val + 256 * (a 2 2).val
set_option maxRecDepth 10000 in
private def table : Array Nat := #[
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 7, 5, 3, 0, 0, 0, 0, 0, 4, 6, 2, 1,
  0, 0, 3, 0, 0, 0, 7, 5, 0, 0, 2, 1, 0, 0, 4, 6,
  0, 0, 7, 5, 3, 0, 0, 0, 0, 0, 4, 6, 2, 1, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 2, 4, 1,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 3, 7, 0,
  0, 1, 0, 2, 0, 4, 0, 6, 0, 5, 0, 7, 0, 0, 3, 0,
  0, 0, 0, 3, 0, 7, 0, 5, 0, 6, 0, 4, 1, 0, 2, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 7, 5, 0,
  0, 0, 0, 0, 2, 4, 6, 1, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 7, 5, 0, 0, 3, 0, 0, 0, 3, 0, 0, 7, 0, 0, 5,
  0, 2, 1, 0, 4, 0, 0, 6, 0, 4, 6, 0, 0, 2, 1, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 1, 0, 0, 6, 2,
  0, 0, 0, 5, 0, 3, 0, 7, 0, 6, 2, 0, 0, 4, 1, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 5, 3,
  0, 1, 0, 6, 0, 2, 0, 4, 0, 5, 3, 0, 0, 7, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 3, 7,
  0, 2, 0, 6, 1, 0, 4, 0, 0, 4, 1, 0, 6, 0, 0, 2,
  0, 0, 6, 1, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 7, 0, 0, 5, 0, 0, 3, 0, 3, 0, 5, 0, 0, 7, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 2, 4, 1, 0, 0,
  0, 1, 0, 4, 0, 6, 0, 2, 0, 5, 0, 0, 3, 0, 0, 7,
  0, 0, 0, 7, 0, 5, 0, 3, 0, 6, 1, 0, 2, 0, 0, 4,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 3, 7, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 7, 5, 0, 0, 0,
  0, 7, 0, 3, 0, 0, 5, 0, 0, 3, 7, 0, 0, 5, 0, 0,
  0, 2, 4, 0, 0, 6, 1, 0, 0, 4, 0, 2, 1, 0, 6, 0,
  0, 0, 2, 4, 6, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
]
private def exceptionalValue (g : SL) : Fin 3 → ZMod 2 :=
  fun i => ((table[binaryCode g]?.getD 0) / 2 ^ i.val % 2 : Nat)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private lemma value_transvection_mul : ∀ (i j : Fin 3) (hij : i ≠ j) (g : SL),
    exceptionalValue (transvection hij 1 * g) =
      specialLinearNatural 3 (transvection hij 1) (exceptionalValue g) +
        exceptionalValue (transvection hij 1) := by
  decide +kernel
private lemma value_one : exceptionalValue 1 = 0 := by decide +kernel

/-- A nonprincipal crossed homomorphism for the actual natural matrix action. -/
public def exceptional : cocycles (specialLinearNatural (k := ZMod 2) 3) :=
  ⟨exceptionalValue, by
    intro g h
    induction g using transvection_induction generalizing h with
    | htrans i j hij c =>
      have hc : c = 0 ∨ c = 1 := by revert c; decide
      rcases hc with rfl | rfl
      · simp [value_one]
      · exact value_transvection_mul i j hij h
    | hmul a b ha hb =>
      rw [mul_assoc, ha, hb, ha, map_add, map_mul, Module.End.mul_apply]
      simp only [add_assoc]⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- Every elementary value has spare coordinate one. -/
public lemma exceptional_spare (i j k : Fin 3) (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) :
    exceptional.val (transvection hij 1) k = 1 := by
  have h : ∀ (i j k : Fin 3) (hij : i ≠ j), i ≠ k → j ≠ k →
      exceptionalValue (transvection hij 1) k = 1 := by decide +kernel
  exact h i j k hij hik hjk

/-- The exceptional cocycle is not a principal cocycle. -/
public lemma exceptional_not_principal :
    ¬ ∃ v, principal (specialLinearNatural (k := ZMod 2) 3) v = exceptional := by
  rintro ⟨v, hv⟩
  have h := congrArg (fun f : cocycles (specialLinearNatural (k := ZMod 2) 3) =>
    f.val (transvection (show (0 : Fin 3) ≠ 1 by decide) 1) 2) hv
  rw [principal_transvection, exceptional_spare 0 1 2 (by decide) (by decide) (by decide)] at h
  simp at h
end Representation.OneCohomology.SLHigherNatural.SLThreeBinary
