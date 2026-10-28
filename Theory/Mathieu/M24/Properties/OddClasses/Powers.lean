module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.ElevenTrace.Representatives

/-!
# Thirteen representatives cover four native odd cyclic groups

The existing native square conjugators identify powers whose exponents differ
by multiplication by two. A small kernel-checked modular arithmetic calculation
leaves thirteen representatives across the marked groups of orders 15, 21, 11
and 23. The cubic representatives occur as powers of the first two generators.
The global coverage argument in `OddClasses` applies this local calculation.

Source: ATLAS M24 conjugacy data,
https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/M24/.
-/

namespace Sporadic.Mathieu.M24OddClasses
open M24OddCyclic

/-- Generator indices and exponents for the thirteen native candidates. -/
@[expose] public def classParameters : Fin 13 → Fin 4 × ℕ :=
  ![(0, 0), (0, 5), (1, 7), (0, 3), (1, 3), (1, 9), (2, 1),
    (0, 1), (0, 7), (1, 1), (1, 5), (3, 1), (3, 5)]

/-- Thirteen native elements, including the identity and both cubic types. -/
@[expose] public noncomputable def classRepresentative (j : Fin 13) : M24 :=
  representative (classParameters j).1 ^ (classParameters j).2

public theorem classRepresentative_zero : classRepresentative 0 = 1 := by
  simp [classRepresentative, classParameters]

private theorem conjugate_two_power {G : Type*} [Group G] {x : G}
    (h : IsConj x (x ^ 2)) (k : ℕ) : IsConj x (x ^ (2 ^ k)) := by
  induction k with
  | zero => simpa using IsConj.refl x
  | succ k ih =>
    simpa only [pow_succ 2 k, pow_mul] using h.trans (IsConj.pow 2 ih)

private theorem exponent_coverage : ∀ (i : Fin 4) (n : Fin (period i)), n.val ≠ 0 →
    ∃ (j : Fin 13) (k : Fin 11), (classParameters j).1 = i ∧
      ((classParameters j).2 * 2 ^ k.val) % period i = n.val := by
  decide +kernel

/-- All powers of the four marked cyclic generators lie in thirteen classes. -/
public theorem representative_power_coverage (i : Fin 4) (n : ℕ) :
    ∃ j : Fin 13, IsConj (representative i ^ n) (classRepresentative j) := by
  let m := n % period i
  have hm : m < period i := Nat.mod_lt _ (by fin_cases i <;> decide)
  have he : representative i ^ m = representative i ^ n := by
    simpa only [representative_order] using pow_mod_orderOf (representative i) n
  by_cases hz : m = 0
  · refine ⟨0, ?_⟩
    rw [← he, hz, pow_zero, classRepresentative_zero]
  obtain ⟨j, k, hi, hk⟩ := exponent_coverage i ⟨m, hm⟩ hz
  have hc := IsConj.pow (classParameters j).2
    (conjugate_two_power (representative_square_conjugacy i) k.val)
  have hp : (representative i ^ (2 ^ k.val)) ^ (classParameters j).2 =
      representative i ^ n := by
    rw [← pow_mul, Nat.mul_comm (2 ^ k.val)]
    rw [← pow_mod_orderOf (representative i)
      ((classParameters j).2 * 2 ^ k.val), representative_order, hk]
    exact he
  refine ⟨j, ?_⟩
  rw [hp] at hc
  simpa only [classRepresentative, hi] using hc.symm

end Sporadic.Mathieu.M24OddClasses
