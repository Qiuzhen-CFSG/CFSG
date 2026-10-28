module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.Reduction
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.UnitaryThree.ModTwoElementary.CentralTransport
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.UnitaryThree.ModTwoElementary.ModelCases
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.UnitaryThree.ModTwoElementary.AbelianLift
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.UnitaryThree.ModTwoElementary.NonabelianLift

/-!
# The elementary order-nine branch for odd PSU₃

The central-cover argument reduces the source pair to an elementary subgroup
of order nine in the actual projective matrix model. Its full SU₃ preimage
is either abelian or nonabelian. In the abelian case, the image of the cube-one
subgroup supplies an invariant line; in the nonabelian case, the local three-core
supplies it. Both constructions control the full pair automizer, including
outer automorphisms.

The final theorem combines the proved model calculations and central-cover
transport to establish the p > 3, p ≡ 2 modulo three order-nine exclusion.
It applies to every quasisimple central cover without a multiplier assumption.
The earlier conditional assembly remains available independently of the prime
and congruence restrictions.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, proof of
Proposition 1.3.4, printed p.511 (PDF p.528 of `refs/quasithin.pdf`).
-/

public section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical
universe u
variable {Q : Type u} [Group Q] [Finite Q]

/-- Conditional assembly for every central cover, with the two genuine
matrix-action obligations explicitly retained. -/
theorem reducible_of_psu_three_elementary_of_lift_cases {S : Sylow 2 Q} {R : Subgroup Q}
    (h : PairInput S R) (hcard : Nat.card R = 9) (p : ℕ)
    (hm : ClassicalGroup.IsPSU (Q ⧸ center Q) 3 p)
    (ha : UnitaryThree.ModTwoElementary.AbelianLiftReducibility p)
    (hn : UnitaryThree.ModTwoElementary.NonabelianLiftReducibility p) :
    PairReducible (S : Subgroup Q) R := by
  obtain ⟨E, _, _, J, hfield, hconj, ⟨e⟩⟩ := hm
  let _ := h.quasisimple
  let _ : IsSimpleGroup (Q ⧸ center Q) := IsQuasisimple.simple
  have hs : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) := e.symm.isSimpleGroup
  apply UnitaryThree.ModTwoElementary.reducible_of_elementary_model h hcard e
  intro T U he hU hperm
  by_cases hab : IsMulCommutative (U.comap J.specialToProjective)
  · exact ha J hs hfield hconj T U he hU hab hperm
  · exact hn J hs hfield hconj T U he hU hab hperm

/-- Every order-nine pair in a quasisimple central cover of PSU₃(p) is
reducible for odd primes p > 3 with p ≡ 2 modulo three. Both special-unitary
lift cases and all central-cover transport premises are discharged. -/
theorem reducible_of_psu_three_mod_two_elementary {S : Sylow 2 Q} {R : Subgroup Q}
    (h : PairInput S R) (hcard : Nat.card R = 9) (p : ℕ)
    (hp : p.Prime) (ho : Odd p) (hlarge : 3 < p) (hmod : p % 3 = 2)
    (hm : ClassicalGroup.IsPSU (Q ⧸ center Q) 3 p) :
    PairReducible (S : Subgroup Q) R :=
  reducible_of_psu_three_elementary_of_lift_cases h hcard p hm
    (UnitaryThree.ModTwoElementary.abelian_lift_reducibility p hp ho hlarge hmod)
    (UnitaryThree.ModTwoElementary.nonabelian_lift_reducibility p hp ho hlarge hmod)

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical
