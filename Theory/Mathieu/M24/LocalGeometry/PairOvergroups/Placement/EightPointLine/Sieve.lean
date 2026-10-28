module

public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.Placement.EightPointLine.Contracts

/-!+# The invariant-line sieve for the fixed Sylow subgroup of A₈

For each of the 280 pairs of disjoint triples, the kernel checks either that
its index is one of sixteen survivors or that some product `p * d` lies outside
`D * P`. Here `p` is one of six specified elements of the fixed Sylow subgroup
and `d` is one of the two three-cycle generators. The nine normal forms in `D`
and the reconstruction test for `P` certify the obstruction to permutability.

For each survivor, the kernel checks all 64 possible conjugators in `P`.
If both generators are conjugated into `D`, their product is conjugated to
itself or its inverse. Integer powers then give invariance of the diagonal
line. All group operations and conjugators are in the literal A₈ carrier.

Source application: Aschbacher–Smith, proof of 1.3.4, printed p.511 (PDF p.528);
GLS3, Table 5.3e, the octad stabilizer `E₁₆.A₈`. The diagnostics in
`source/check_candidates.py` suggest the tests; all checks below use the kernel.
-/

namespace Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.Placement.EightPoint
open Subgroup
open scoped Pointwise

private abbrev survives (i : Fin 280) : Prop :=
  i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨
  i = 66 ∨ i = 67 ∨ i = 68 ∨ i = 69 ∨ i = 210 ∨ i = 211 ∨ i = 212 ∨ i = 213

private def testIndex : Fin 6 → Fin 64 := ![1, 2, 4, 8, 16, 32]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem rejection_check : ∀ i : Fin 280, survives i ∨
    ∃ p : Fin 6, ∃ k : Fin 2, ∀ j : Fin 9,
      let x := ((nineWord i j)⁻¹ * twoElement (testIndex p) * nineGenerator i k).val
      twoWord (twoIndex x) ≠ x := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem normalizer_check : ∀ i : Fin 280, survives i → ∀ p : Fin 64,
    (∃ j : Fin 9, nineWord i j = twoElement p * nineGenerator i 0 * (twoElement p)⁻¹) →
    (∃ j : Fin 9, nineWord i j = twoElement p * nineGenerator i 1 * (twoElement p)⁻¹) →
    twoElement p * nineWord i 4 * (twoElement p)⁻¹ = nineWord i 4 ∨
    twoElement p * nineWord i 4 * (twoElement p)⁻¹ = (nineWord i 4)⁻¹ := by
  intro i hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +kernel

private theorem survives_of_permute (i : Fin 280)
    (hperm : (nineGroup i : Set Alt) * (twoGroup : Set Alt) =
      (twoGroup : Set Alt) * (nineGroup i : Set Alt)) : survives i := by
  rcases rejection_check i with hi | ⟨p, k, hbad⟩
  · exact hi
  · have hm : twoElement (testIndex p) * nineGenerator i k ∈
        (twoGroup : Set Alt) * (nineGroup i : Set Alt) :=
      Set.mem_mul.mpr ⟨_, (mem_twoGroup _).mpr ⟨_, rfl⟩,
        _, nineGenerator_mem i k, rfl⟩
    rw [← hperm] at hm
    obtain ⟨a, ha, b, hb, he⟩ := Set.mem_mul.mp hm
    obtain ⟨j, rfl⟩ := (mem_nineGroup i a).mp ha
    have hb' : (nineWord i j)⁻¹ * twoElement (testIndex p) * nineGenerator i k ∈
        twoGroup := by
      rwa [mul_assoc, ← he, inv_mul_cancel_left]
    exact False.elim (hbad j ((mem_twoGroup_iff_test _).mp hb'))

/-- Every candidate permuting with the fixed Sylow subgroup has its diagonal
line invariant under the normalizer inside that Sylow subgroup. -/
public theorem nineSieve : NineSieve := by
  intro i hperm g hg x hx
  obtain ⟨p, rfl⟩ := (mem_twoGroup g).mp hg.1
  have hn (k : Fin 2) : ∃ j : Fin 9,
      nineWord i j = twoElement p * nineGenerator i k * (twoElement p)⁻¹ :=
    (mem_nineGroup i _).mp
      ((mem_set_normalizer_iff.mp hg.2 _).mp (nineGenerator_mem i k))
  have hgen : twoElement p * nineWord i 4 * (twoElement p)⁻¹ ∈ nineLine i := by
    rcases normalizer_check i (survives_of_permute i hperm) p (hn 0) (hn 1) with h | h
    · rw [h]
      exact mem_zpowers _
    · rw [h]
      exact (nineLine i).inv_mem (mem_zpowers _)
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hx
  rw [← conj_zpow]
  exact (nineLine i).zpow_mem hgen n

end Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.Placement.EightPoint
