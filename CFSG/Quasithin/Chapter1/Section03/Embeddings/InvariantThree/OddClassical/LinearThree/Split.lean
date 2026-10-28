module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.LinearThree.Basic
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.LinearThree.Split.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.LinearThree.Split.Elementary
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.LinearThree.Split.Extraspecial

/-!
# The split odd PSL₃ pair sieve

The universal cover implication supplies an actual SL₃ or PSL₃ model. The
elementary complement has an invariant order-three intersection with Z(Q)
or the derived subgroup of C_Q(Z(S)). The extraspecial complement has an
order-nine intersection with O₃(RS), taken inside R ⊔ S. In each case the
intersection gives a proper nonzero invariant subgroup of R/Φ(R).

`reducible_of_mod_three_eq_one` discharges both local computations, including
the subgroup positions derived from RS = SR and the ambient Sylow hypothesis.
Its only earlier-result parameter is `SplitPrimeCover`, the universal
Schur-multiplier implication independent of S, R and their action.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, proof of
Proposition 1.3.4, printed p.511 (PDF p.528), and I.1.3, printed p.407 (PDF p.418).
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.LinearThree.Split
universe u
variable {Q : Type u} [Group Q]

/-- Conditional assembly from the two model intersection computations.
Both local premises are discharged in `reducible_of_mod_three_eq_one`. -/
theorem reducible_of_split_model_intersections [Finite Q]
    (hcover : SplitPrimeCover.{u}) {S : Sylow 2 Q} {R : Subgroup Q}
    (h : PairInput S R) {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hlarge : 3 < p) (hmod : p % 3 = 1)
    (hm : ClassicalGroup.IsPSL (Q ⧸ center Q) 3 p)
    (helem : LinearThreeModel p Q → IsElementaryAbelian 3 R → Nat.card R = 9 →
      Nat.card ((center Q).subgroupOf R) = 3 ∨
        Nat.card ((centralizerDerived (S : Subgroup Q)).subgroupOf R) = 3)
    (hextra : LinearThreeModel p Q → Nat.card R = 27 →
      Nat.card (((R ⊔ (S : Subgroup Q)).pCoreIn 3).subgroupOf R) = 9) :
    PairReducible (S : Subgroup Q) R := by
  have hmodel := hcover p hp ho hlarge hmod Q h.quasisimple hm
  rcases h.oddComplement with ⟨he, hc⟩ | ⟨_, hc, _⟩
  · have hc' : Nat.card R = 9 := by simpa using hc
    exact reducible_of_elementary_intersections h he hc' (helem hmodel he hc')
  · have hc' : Nat.card R = 27 := by simpa using hc
    exact reducible_of_extraspecial_local_core_nine h hc' (hextra hmodel hc')

/-- The split odd PSL₃ exclusion, including actual central covers through
the universal earlier cover implication. Both elementary order-nine and
extraspecial order-27 complements give reducible actions on R/Φ(R). -/
theorem reducible_of_mod_three_eq_one [Finite Q]
    (hcover : SplitPrimeCover.{u}) {S : Sylow 2 Q} {R : Subgroup Q}
    (h : PairInput S R) {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hlarge : 3 < p) (hmod : p % 3 = 1)
    (hm : ClassicalGroup.IsPSL (Q ⧸ center Q) 3 p) :
    PairReducible (S : Subgroup Q) R := by
  apply reducible_of_split_model_intersections hcover h hp ho hlarge hmod hm
  · exact elementary_intersections h hp ho hlarge hmod
  · exact extraspecial_local_core_nine h hp ho hlarge hmod

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.LinearThree.Split
