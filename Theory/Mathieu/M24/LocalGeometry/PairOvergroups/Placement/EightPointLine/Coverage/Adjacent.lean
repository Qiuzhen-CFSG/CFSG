module

public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.Placement.EightPointLine.Contracts
public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.Placement.EightPointLine.Coverage.TripleCertificate
/-!
# Adjacent transpositions preserve the candidate elementary nines

Conjugation carries a three-cycle to the cycle on its three image points.
Rotating these points preserves the cycle; reversing them inverts it.
The finite coordinate certificate in `TripleCertificate` identifies the image triples under
all seven adjacent transpositions, allowing exchange of the two generators.
Thus the image subgroup lies in another candidate. Their common order nine
then gives equality.

The coordinate identities are checked by Lean's kernel; table size alone
is not used to infer coverage.

Source application: Aschbacher–Smith, proof of 1.3.4, printed p.511 (PDF p.528);
GLS3, Table 5.3e, the octad stabilizer `E₁₆.A₈`.
-/

namespace Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.Placement.EightPoint.Coverage
open Subgroup
private def cycle (a b c : Fin 8) : Sym := Equiv.swap a b * Equiv.swap b c
private theorem cycle_rotate (a b c : Fin 8) (hab : a ≠ b) (hac : a ≠ c) :
    cycle b c a = cycle a b c := by
  unfold cycle
  rw [Equiv.mul_swap_eq_swap_mul, Equiv.swap_apply_right,
    Equiv.swap_apply_of_ne_of_ne hab hac, Equiv.swap_comm b a]
private theorem cycle_reverse (a b c : Fin 8) :
    cycle c b a = (cycle a b c)⁻¹ := by
  simp only [cycle, mul_inv_rev, Equiv.swap_inv, Equiv.swap_comm c b, Equiv.swap_comm b a]
private theorem cycle_reorder (t : Fin 3 → Fin 8)
    (hab : t 0 ≠ t 1) (hac : t 0 ≠ t 2) (hbc : t 1 ≠ t 2) (q : Fin 6) :
    cycle (t (tripleOrder q 0)) (t (tripleOrder q 1)) (t (tripleOrder q 2)) =
      if q.val < 3 then cycle (t 0) (t 1) (t 2) else (cycle (t 0) (t 1) (t 2))⁻¹ := by
  have h1 := cycle_rotate (t 0) (t 1) (t 2) hab hac
  have h2 := (cycle_rotate (t 1) (t 2) (t 0) hbc hab.symm).trans h1
  fin_cases q
  · rfl
  · exact h1
  · exact h2
  · exact cycle_reverse (t 0) (t 1) (t 2)
  · exact (cycle_reverse (t 2) (t 0) (t 1)).trans (congrArg Inv.inv h2)
  · exact (cycle_reverse (t 1) (t 2) (t 0)).trans (congrArg Inv.inv h1)
private theorem cycle_conj (g : Sym) (a b c : Fin 8) :
    g * cycle a b c * g⁻¹ = cycle (g a) (g b) (g c) := by
  change (MulAut.conj g) (cycle a b c) = _
  unfold cycle
  rw [map_mul]
  simp only [MulAut.conj_apply, ← Equiv.swap_apply_apply]

private theorem rawNineGenerator_eq_cycle (i : Fin 280) (k : Fin 2) :
    rawNineGenerator i k = cycle (genTriple i k 0) (genTriple i k 1) (genTriple i k 2) := by
  fin_cases k <;> rfl

private theorem conjugate_generator_mem (g : Sym) (i j : Fin 280) (k l : Fin 2)
    (q : Fin 6) (h : ∀ n, g (genTriple i k n) = genTriple j l (tripleOrder q n)) :
    (MulAut.conjNormal g : MulAut Alt) (nineGenerator i k) ∈ nineGroup j := by
  have he : ((MulAut.conjNormal g : MulAut Alt) (nineGenerator i k)).val =
      if q.val < 3 then (nineGenerator j l).val else ((nineGenerator j l)⁻¹).val := by
    change g * rawNineGenerator i k * g⁻¹ = _
    rw [rawNineGenerator_eq_cycle, cycle_conj, h 0, h 1, h 2]
    obtain ⟨h01, h02, h12⟩ := genTriple_distinct j l
    rw [cycle_reorder _ h01 h02 h12]
    rw [← rawNineGenerator_eq_cycle]
    rfl
  split_ifs at he with hq
  · have he' := Subtype.ext he
    rw [he']
    exact nineGenerator_mem j l
  · have he' := Subtype.ext he
    rw [he']
    exact (nineGroup j).inv_mem (nineGenerator_mem j l)

/-- The candidate family is closed under each adjacent transposition of S₈. -/
public theorem conjugate_nineGroup_adjacent (r : Fin 7) (i : Fin 280) :
    ∃ j : Fin 280, (nineGroup i).map
      (MulAut.conjNormal (Equiv.swap r.castSucc r.succ)).toMonoidHom = nineGroup j := by
  obtain ⟨j, hj⟩ := adjacent_triples r i
  refine ⟨j, eq_of_le_of_card_ge ?_ ?_⟩
  · rw [map_le_iff_le_comap, nineGroup, closure_le]
    rintro x ⟨k, rfl⟩
    obtain ⟨l, q, h⟩ := hj k
    exact conjugate_generator_mem _ i j k l q h
  · rw [card_map_of_injective
      (f := (MulAut.conjNormal (Equiv.swap r.castSucc r.succ) : MulAut Alt).toMonoidHom)
      (MulAut.conjNormal _).injective, card_nineGroup, card_nineGroup]

end Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.Placement.EightPoint.Coverage
