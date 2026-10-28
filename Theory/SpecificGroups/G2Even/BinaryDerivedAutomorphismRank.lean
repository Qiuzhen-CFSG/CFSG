module

public import Theory.SpecificGroups.SU3.BinaryG2Comparison
public import Theory.SpecificGroups.OddThreeRank.Automorphisms

/-!
# Automorphism two-rank of the actual binary G₂ derived group

The exceptional isomorphism identifies the commutator subgroup of the binary
octonion automorphism group with the projective special unitary matrix group
PSU₃(3). Transporting the odd-prime unitary automorphism bound gives two-rank
at most three. Simplicity is supplied by the binary octonion calculation;
the coefficient field on the unitary side has order nine and cube conjugation.

Source: Aschbacher–Smith, G.7.3(1), printed p.348, and the exceptional rank
comparison in 16.3.9, printed p.1180. The genuine comparison, including its
Fong recognition argument and ATLAS attribution, is in `SU3.BinaryG2Comparison`.
-/

public section

open Theory.GroupTheory
namespace Atlas.G2

/-- The full automorphism group of G₂(2)′ has two-rank at most three. -/
theorem binary_derived_automorphism_two_rank_le_three :
    primeRank 2 (MulAut (commutator (Model (ZMod 2)))) ≤ 3 := by
  obtain ⟨e⟩ := nonempty_commutator_binary_equiv_psu3
  let : IsSimpleGroup (commutator (Model (ZMod 2))) := isSimple_commutator_binary
  let : IsSimpleGroup (ABG.PSU3 3 1 Nat.one_ne_zero) := e.symm.isSimpleGroup
  let : Finite (ABG.PSU3 3 1 Nat.one_ne_zero) := Finite.of_equiv _ e.toEquiv
  rw [primeRank_equiv 2 (MulAut.congr e)]
  exact Theory.SpecificGroups.OddThreeRank.psu3_automorphism_two_rank_le_three
    (p := 3) (ABG.unitaryForm 3 3 1 Nat.one_ne_zero) Nat.prime_three (by decide)
    (GaloisField.card 3 2 (by decide))
    (by intro x; simp only [ABG.unitaryForm, iterateFrobeniusEquiv_def, pow_one])

end Atlas.G2
