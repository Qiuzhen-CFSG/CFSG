module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.LocalPair
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.SmallLinear
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.RankOne
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.LinearThree
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.UnitaryThree

/-!
# Odd-characteristic cases of the three-complement pair sieve

The two odd-characteristic constructors of `Section02.LocalModels.TheoremCModel`
are PSL₂(pᵉ), with e = 1 or 2, and PSL₃(p) or PSU₃(p), for odd primes p.
`alternative` assembles their local computations. Every pair is reducible
unless its complement is the actual elementary plane E₉ and its ambient
group has an actual SL₃(3) or PSL₃(3) model.

Cyclic Sylow three-subgroups exclude the rank-one and opposite-congruence
cases, while permutability excludes PSL₂(9) and PSU₃(3). In the remaining
degree-three cases, the elementary intersection and extraspecial local-core
computations give proper invariant subgroups of R/Φ(R). In particular,
PSL₃(3) has an order-nine local core when R has order 27; only its elementary
complement gives the surviving plane alternative.

All local subgroup and action premises are discharged. The three explicit
cover inputs are universal earlier implications of I.1.3, independent of
S, R and their action. They must be supplied by the source-theorem assembly
owner. `alternative_of_three_odd` directly matches the signed degree-three
constructor; the re-exported `reducible_of_psl_two_odd` matches the other one.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, proof of
Proposition 1.3.4, printed p.511 (PDF p.528), and I.1.3, printed p.407
(PDF p.418).
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical
universe u
variable {Q : Type u} [Group Q] [Finite Q]

/-- The signed degree-three constructor of Theorem C: linear and unitary
parameters use their actual projective models and all allowed central covers. -/
theorem alternative_of_three_odd
    (hthree : LinearThree.TrivialThreeCover.{u})
    (hsplit : LinearThree.Split.SplitPrimeCover.{u})
    (hunitary : UnitaryThree.ModTwoExtraspecial.PrimeCover.{u})
    {S : Sylow 2 Q} {R : Subgroup Q} (h : PairInput S R)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (unitary : Bool)
    (hm : Section02.LocalModels.IsPSLSign (Q ⧸ center Q) unitary 3 p) :
    PairReducible (S : Subgroup Q) R ∨
      (Nonempty (R ≃* Plane 3) ∧ LinearThreeModel 3 Q) := by
  cases unitary with
  | false => exact LinearThree.alternative hthree hsplit h hp ho hm
  | true => exact Or.inl (reducible_of_psu_three hunitary h p hp ho hm)

/-- The complete odd-characteristic part of the three-complement pair sieve.
The model hypothesis is exactly the disjunction of the `linear_odd` and
`three_odd` constructor hypotheses of Theorem C, including every parameter
restriction. Only the universal earlier cover implications remain inputs. -/
theorem alternative
    (hthree : LinearThree.TrivialThreeCover.{u})
    (hsplit : LinearThree.Split.SplitPrimeCover.{u})
    (hunitary : UnitaryThree.ModTwoExtraspecial.PrimeCover.{u})
    {S : Sylow 2 Q} {R : Subgroup Q} (h : PairInput S R)
    (hm : (∃ p e : ℕ, p.Prime ∧ Odd p ∧ (e = 1 ∨ e = 2) ∧ 4 ≤ p ^ e ∧
        ClassicalGroup.IsPSL (Q ⧸ center Q) 2 (p ^ e)) ∨
      (∃ (p : ℕ) (unitary : Bool), p.Prime ∧ Odd p ∧
        Section02.LocalModels.IsPSLSign (Q ⧸ center Q) unitary 3 p)) :
    PairReducible (S : Subgroup Q) R ∨
      (Nonempty (R ≃* Plane 3) ∧ LinearThreeModel 3 Q) := by
  rcases hm with ⟨p, e, hp, ho, he, hsimple, hm⟩ | ⟨p, unitary, hp, ho, hm⟩
  · exact Or.inl (reducible_of_psl_two_odd h hp ho he hsimple hm)
  · exact alternative_of_three_odd hthree hsplit hunitary h hp ho unitary hm

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical
