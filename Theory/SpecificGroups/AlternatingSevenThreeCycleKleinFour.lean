module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# A Klein four centralizing a three-cycle in A₇

The double transpositions on the four letters outside a three-cycle's support
form a Klein four subgroup of its centralizer. We check two generators for the
cycle `(0 2 1)` and transport them by conjugation in the full symmetric group.
Conjugation preserves the alternating group, so the conjugating permutation
need not be even.

This is the permutation input to the fixed-point argument for binary
four-dimensional A₇ representations in Aschbacher--Smith, *The Classification
of Quasithin Groups*, Lemma I.1.6(8), printed p.408/PDF p.419.
-/

namespace alternatingGroup

open Equiv Equiv.Perm

private def t : alternatingGroup (Fin 7) :=
  ⟨swap 0 1 * swap 0 2, by simp [mem_alternatingGroup, Equiv.Perm.sign_mul]⟩
private def b : alternatingGroup (Fin 7) :=
  ⟨swap 3 4 * swap 5 6, by simp [mem_alternatingGroup, Equiv.Perm.sign_mul]⟩
private def c : alternatingGroup (Fin 7) :=
  ⟨swap 3 5 * swap 4 6, by simp [mem_alternatingGroup, Equiv.Perm.sign_mul]⟩

private theorem ht : IsThreeCycle (t : Equiv.Perm (Fin 7)) := by
  exact isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)

private theorem witnesses : b ^ 2 = 1 ∧ c ^ 2 = 1 ∧ b ≠ 1 ∧ c ≠ 1 ∧ b ≠ c ∧
    Commute t b ∧ Commute t c ∧ Commute b c := by
  change b ^ 2 = 1 ∧ c ^ 2 = 1 ∧ b ≠ 1 ∧ c ≠ 1 ∧ b ≠ c ∧
    t * b = b * t ∧ t * c = c * t ∧ b * c = c * b
  decide +kernel

/-- A three-cycle in A₇ centralizes two distinct nonidentity commuting
involutions. -/
public theorem threeCycle_exists_commuting_involutions (a : alternatingGroup (Fin 7))
    (ha : IsThreeCycle (a : Equiv.Perm (Fin 7))) :
    ∃ b c : alternatingGroup (Fin 7),
      b ^ 2 = 1 ∧ c ^ 2 = 1 ∧ b ≠ 1 ∧ c ≠ 1 ∧ b ≠ c ∧
      Commute a b ∧ Commute a c ∧ Commute b c := by
  obtain ⟨s, hs⟩ := isConj_iff.mp (isConj_of_cycleType_eq (ht.cycleType.trans ha.cycleType.symm))
  let f : MulAut (alternatingGroup (Fin 7)) := MulAut.conjNormal s
  have hfa : f t = a := Subtype.ext hs
  rcases witnesses with ⟨hb, hc, hbne, hcne, hbcne, htb, htc, hbc⟩
  refine ⟨f b, f c, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hbc.map f⟩
  · rw [← map_pow, hb, map_one]
  · rw [← map_pow, hc, map_one]
  · exact fun h => hbne (f.map_eq_one_iff.mp h)
  · exact fun h => hcne (f.map_eq_one_iff.mp h)
  · exact fun h => hbcne (f.injective h)
  · rw [← hfa]
    exact htb.map f
  · rw [← hfa]
    exact htc.map f

end alternatingGroup
