module

public import CFSG.Quasithin.MainConverse.OddClassicalLocal.PSL2Rank
public import CFSG.Quasithin.MainConverse.OddClassicalLocal.PSL2Even
public import CFSG.Quasithin.MainConverse.OddClassicalLocal.LinearThreeFour
public import CFSG.Quasithin.MainConverse.OddClassicalLocal.UnitaryThreeFour
public import CFSG.Quasithin.MainConverse.Transport

/-!
# Local conditions for the odd classical converse

This module proves QT and E for the odd classical alternatives: PSL₂(p) for
Fermat–Mersenne primes p ≥ 5, PSL₃(3), PSL₄(3), PSU₃(3), and PSU₄(3). Every
model witness is an actual projective matrix-group isomorphism. All prime
fields of order at least five give QT for PSL₂; the Fermat–Mersenne restriction
supplies the two-group involution centralizers used to prove E.

In dimensions three and four, the intrinsic matrix calculations bound the
odd-prime ranks of the actual two-locals and show that the two-cores inside
Sylow-containing maximal two-locals are self-centralizing. The unitary model
allows every nondegenerate Hermitian form, with matrix-field order nine and
cube conjugation. Actual projective equivalences transport the local results.
No proper-K or pre-existing QT/E hypothesis is needed, so these results apply
directly on the approved proper-K induction domain.

Source: Aschbacher–Smith, Theorem 0.1.2(4), printed p.4, repeated as Theorem
0.1.1(4) on p.482 of `refs/quasithin.pdf`. G₂(3) is treated in the separate
exceptional-model assembly.
-/

namespace CFSG.Quasithin.MainConverse

/-- The QT and E clauses of the PSL₂ prime alternative, including p = 5 and p = 7.
The model supplies an actual isomorphism, with no additional local hypotheses. -/
public theorem psl2_fermatMersenne_qt_and_evenCharacteristic_of_isPSL
    {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : IsFermatOrMersennePrime p) (hp5 : 5 ≤ p)
    (hG : ClassicalGroup.IsPSL G 2 p) :
    IsQuasithin G ∧ IsEvenCharacteristic G := by
  have hqt := psl2_prime_quasithin_of_isPSL hp.1 hp5 hG
  obtain ⟨F, hfield, hfinite, hF, ⟨e⟩⟩ := hG
  exact ⟨hqt, evenCharacteristic_of_model_equiv e
    (psl2_fermatMersenne_evenCharacteristic F hF hp hp5)⟩

/-- All odd classical alternatives of source Theorem 0.1.2(4) satisfy QT and E.
The hypotheses retain the exact prime bounds, dimensions, and actual model
isomorphisms; the three family calculations discharge every local premise. -/
public theorem odd_classical_qt_and_evenCharacteristic
    {G : Type*} [Group G] [Finite G]
    (hG : (∃ p : ℕ, IsFermatOrMersennePrime p ∧ 5 ≤ p ∧
        ClassicalGroup.IsPSL G 2 p) ∨
      (∃ n : ℕ, (n = 3 ∨ n = 4) ∧ ClassicalGroup.IsPSL G n 3) ∨
      (∃ n : ℕ, (n = 3 ∨ n = 4) ∧ ClassicalGroup.IsPSU G n 3)) :
    IsQuasithin G ∧ IsEvenCharacteristic G := by
  rcases hG with ⟨p, hp, hp5, hmodel⟩ | ⟨n, hn, hmodel⟩ | ⟨n, hn, hmodel⟩
  · exact psl2_fermatMersenne_qt_and_evenCharacteristic_of_isPSL hp hp5 hmodel
  · exact psl_three_four_qt_and_evenCharacteristic_of_isPSL hn hmodel
  · exact psu_three_four_qt_and_evenCharacteristic_of_isPSU hn hmodel

end CFSG.Quasithin.MainConverse
