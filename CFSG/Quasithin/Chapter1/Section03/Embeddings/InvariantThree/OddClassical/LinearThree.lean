module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.LinearThree.Basic
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.LinearThree.CoreThree
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.LinearThree.Split

/-!
# Odd PSL₃ pairs and the surviving PSL₃(3) alternative

The congruence class −1 modulo three is excluded by a concrete cyclic Sylow
calculation, including every quasisimple central cover. In the split class,
the elementary intersection and extraspecial local-core calculations give
proper invariant subgroups of the Frattini quotient. For field order three,
the elementary complement gives the actual E₉ and linear-three models, while
the extraspecial complement has a local three-core intersection of order nine
and is therefore excluded.

`alternative` assembles all odd-prime cases. Every local subgroup and action
premise is discharged. Only `TrivialThreeCover` and `Split.SplitPrimeCover`
remain explicit: these are universal earlier cover implications independent
of the pair and its action, retaining actual SL₃ or PSL₃ equivalences.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, proof of
Proposition 1.3.4, printed p.511 (PDF p.528); the independent universal cover
inputs are the PSL₃ implications of I.1.3 on printed p.407 (PDF p.418).
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.LinearThree
universe u
variable {Q : Type u} [Group Q] [Finite Q]

/-- The local core must be computed for the extraspecial complement; the
elementary complement already supplies the surviving source alternative. -/
theorem alternative_at_three_of_local_core (hcover : TrivialThreeCover.{u})
    {S : Sylow 2 Q} {R : Subgroup Q} (h : PairInput S R)
    (hm : ClassicalGroup.IsPSL (Q ⧸ center Q) 3 3)
    (hcore : Nat.card R = 27 →
      Nat.card (((R ⊔ (S : Subgroup Q)).pCoreIn 3).subgroupOf R) = 9) :
    PairReducible (S : Subgroup Q) R ∨
      (Nonempty (R ≃* Plane 3) ∧ LinearThreeModel 3 Q) := by
  rcases h.oddComplement with ⟨he, hc⟩ | ⟨_, hc, _⟩
  · exact Or.inr (elementary_alternative hcover h hm he (by simpa using hc))
  · have hc' : Nat.card R = 27 := by simpa using hc
    exact Or.inl (reducible_of_extraspecial_local_core_nine h hc' (hcore hc'))

/-- At field order three, the computed extraspecial core excludes order 27;
the elementary case retains the actual plane and covering-group model. -/
theorem alternative_at_three (hcover : TrivialThreeCover.{u})
    {S : Sylow 2 Q} {R : Subgroup Q} (h : PairInput S R)
    (hm : ClassicalGroup.IsPSL (Q ⧸ center Q) 3 3) :
    PairReducible (S : Subgroup Q) R ∨
      (Nonempty (R ≃* Plane 3) ∧ LinearThreeModel 3 Q) := by
  exact alternative_at_three_of_local_core hcover h hm
    (local_threeCore_card hcover h hm)

/-- Both congruence classes exclude odd primes greater than three, including
the central covers supplied by the universal split-cover implication. -/
theorem reducible_of_three_lt (hcover : Split.SplitPrimeCover.{u})
    {S : Sylow 2 Q} {R : Subgroup Q} (h : PairInput S R)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hlarge : 3 < p)
    (hm : ClassicalGroup.IsPSL (Q ⧸ center Q) 3 p) :
    PairReducible (S : Subgroup Q) R := by
  have hmod : p % 3 ≠ 0 := by
    intro hz
    have hd : 3 ∣ p := Nat.dvd_of_mod_eq_zero hz
    rcases (Nat.dvd_prime hp).mp hd with hh | hh <;> omega
  have hcases : p % 3 = 1 ∨ p % 3 = 2 := by omega
  rcases hcases with h1 | h2
  · exact Split.reducible_of_mod_three_eq_one hcover h hp ho hlarge h1 hm
  · exact reducible_of_mod_three_eq_two h hp h2 hm

/-- The odd PSL₃ pair alternative. All local calculations are proved; the
only earlier-theorem inputs are the two universal central-cover implications. -/
theorem alternative (hthree : TrivialThreeCover.{u})
    (hsplit : Split.SplitPrimeCover.{u})
    {S : Sylow 2 Q} {R : Subgroup Q} (h : PairInput S R)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (Q ⧸ center Q) 3 p) :
    PairReducible (S : Subgroup Q) R ∨
      (Nonempty (R ≃* Plane 3) ∧ LinearThreeModel 3 Q) := by
  by_cases h3 : p = 3
  · subst p
    exact alternative_at_three hthree h hm
  · have hlarge : 3 < p := by
      have hp2 := hp.two_le
      obtain ⟨k, hk⟩ := ho
      omega
    exact Or.inl (reducible_of_three_lt hsplit h hp ho hlarge hm)

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.LinearThree
