module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.AlternatingBinary.Basic
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.AlternatingBinary.Six
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.AlternatingBinary.Seven
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8

/-!
# Alternating and binary-linear entries in the three-rank Sylow-pair sieve

The A₅, A₆ and A₇ exclusions hold for arbitrary finite central covers. They
use, respectively, cyclic Sylow three-subgroups and transfer, the faithful
coset-action obstruction to an index-five subgroup, and the invariant line
coming from the unique four-point orbit of the A₇ Sylow pair. The last two
arguments retain the actual automorphism action on R/Φ(R) through the center.

For L₄(2) and L₅(2), `AlternatingBinary.binary_surviving` constructs the E₉
complement and identifies the actual group, retaining only the explicit
universal multiplier bounds `AlternatingBinary.BinaryMultiplierBound` from
the earlier chapter. No local irreducibility or model-sieve conclusion is
part of those bounds.

The actual A₈ ≃ L₄(2) equivalence transports the remaining alternating central
quotient to the binary-linear case. `alternating_or_binary` assembles precisely
the alternating and binary-linear entries of Theorem C: either every
two-subgroup of the pair automizer is reducible, or R is E₉ and Q is one of
the exceptional models. The earlier universal multiplier implication remains
an explicit parameter for the source theorem's owner to discharge.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, proof of
Proposition 1.3.4, printed p.511 (PDF p.528).
-/

public section

open Subgroup
open CFSG.Quasithin.Chapter1.Section02.LocalModels
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.AlternatingBinary
universe u
variable {Q : Type u} [Group Q] [Finite Q]

omit [Finite Q] in
private theorem alternating_eight_quotient
    (e : Q ⧸ center Q ≃* alternatingGroup (Fin 8)) :
    ClassicalGroup.IsPSL (Q ⧸ center Q) 4 2 :=
  ⟨ZMod 2, inferInstance, inferInstance, Nat.card_zmod 2,
    ⟨e.trans Atlas.Comparisons.Exceptional.alt8EquivPSL4Two⟩⟩

/-- The surviving A₈ central quotient identifies Q itself with L₄(2),
using the actual exceptional equivalence and the permitted multiplier bound. -/
theorem alternating_eight_model (hMult : BinaryMultiplierBound.{u})
    {S : Sylow 2 Q} {R : Subgroup Q} (h : PairInput S R)
    (e : Q ⧸ center Q ≃* alternatingGroup (Fin 8)) :
    ClassicalGroup.IsPSL Q 4 2 :=
  binary_model hMult h (Or.inl rfl) (alternating_eight_quotient e)

/-- The A₈ branch supplies both the actual E₉ complement and exceptional model. -/
theorem alternating_eight_surviving (hMult : BinaryMultiplierBound.{u})
    {S : Sylow 2 Q} {R : Subgroup Q} (h : PairInput S R)
    (e : Q ⧸ center Q ≃* alternatingGroup (Fin 8)) :
    Nonempty (R ≃* Plane 3) ∧ ExceptionalModel Q :=
  binary_surviving hMult h (Or.inl rfl) (alternating_eight_quotient e)

/-- All alternating entries of Theorem C, including arbitrary central covers.
The A₅–A₇ branches give the action exclusion; A₈ gives the surviving model. -/
theorem alternating (hMult : BinaryMultiplierBound.{u})
    {S : Sylow 2 Q} {R : Subgroup Q} (h : PairInput S R)
    {n : ℕ} (hn : 5 ≤ n ∧ n ≤ 8) (he : IsAlternating (Q ⧸ center Q) n) :
    PairReducible (S : Subgroup Q) R ∨
      (Nonempty (R ≃* Plane 3) ∧ ExceptionalModel Q) := by
  obtain ⟨e⟩ := he
  obtain rfl | rfl | rfl | rfl : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 := by omega
  · exact Or.inl (alternating_five h e)
  · exact Or.inl (alternating_six h e)
  · exact Or.inl (alternating_seven h e)
  · exact Or.inr (alternating_eight_surviving hMult h e)

/-- The full alternating and binary-linear part of the invariant-three sieve.
Both model predicates contain actual multiplicative equivalences. The only
additional premise is the universal earlier multiplier implication. -/
theorem alternating_or_binary (hMult : BinaryMultiplierBound.{u})
    {S : Sylow 2 Q} {R : Subgroup Q} (h : PairInput S R)
    (hmodel : (∃ n : ℕ, (5 ≤ n ∧ n ≤ 8) ∧ IsAlternating (Q ⧸ center Q) n) ∨
      ∃ n : ℕ, (n = 4 ∨ n = 5) ∧ ClassicalGroup.IsPSL (Q ⧸ center Q) n 2) :
    PairReducible (S : Subgroup Q) R ∨
      (Nonempty (R ≃* Plane 3) ∧ ExceptionalModel Q) := by
  rcases hmodel with ⟨n, hn, he⟩ | ⟨n, hn, he⟩
  · exact alternating hMult h hn he
  · exact Or.inr (binary_surviving hMult h hn he)

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.AlternatingBinary
