module
public import CFSG.KnownSimple.PrimeToFifteen.Reduction
public import CFSG.KnownSimple.PrimeToFifteen.Basic
public import CFSG.KnownSimple.PrimeToFifteen.Classical
public import CFSG.KnownSimple.PrimeToFifteen.Exceptional
public import CFSG.KnownSimple.PrimeToFifteen.Sporadic

/-!
# Finite known-simple K-groups of order prime to fifteen are solvable

Every branch of the full carrier catalogue is handled: prime cyclic groups,
alternating groups, all six classical families at arbitrary ranks, every
exceptional and twisted family, Suzuki, the small derived carriers, and all
twenty-six sporadics. Their concrete small-prime witnesses exclude three-free
and five-free nonsolvable simple sections. Strong induction on group order
then removes proper normal subgroups and quotients.

The intended consumer is solvability of the actual C_Q(J) in the original
A₅ full/local module passage, followed by Aschbacher–Smith D.2.13. This theorem
uses the full KnownSimple class and does not infer SQTK for arbitrary quotients.
-/

public section
namespace CFSG.KnownSimple
universe u

theorem IsKnownSimpleCarrier.solvable_of_coprime_three_five
    {G : Type u} [Group G] [Finite G] (h : IsKnownSimpleCarrier G)
    (h3 : Nat.Coprime 3 (Nat.card G)) (h5 : Nat.Coprime 5 (Nat.card G)) :
    Group.IsSolvable G := by
  have hnot3 := Nat.prime_three.coprime_iff_not_dvd.mp h3
  cases h with
  | cyclic h => exact PrimeToFifteen.solvable_of_primeCyclic h
  | alternating n hn iso =>
    obtain ⟨e⟩ := iso
    exact (PrimeToFifteen.not_coprime_three_of_alternating hn e h3).elim
  | classical h => exact (hnot3 h.three_dvd_card).elim
  | g2 h => exact (hnot3 h.three_dvd_card).elim
  | suzuki m hm iso =>
    obtain ⟨e⟩ := iso
    exact (PrimeToFifteen.not_coprime_five_of_suzuki hm e h5).elim
  | exceptional h => exact (hnot3 h.three_dvd_card).elim
  | triality h => exact (hnot3 h.three_dvd_card).elim
  | reeF4 h => exact (hnot3 h.three_dvd_card).elim
  | smallDerived h => exact PrimeToFifteen.solvable_of_smallDerived h h3 h5
  | sporadic h => exact h.solvable_of_coprime_three_five h3 h5

/-- A finite group whose simple sections lie in the full known-simple catalogue
is solvable when its order is prime to both three and five. -/
theorem isSolvable_of_coprime_three_five
    (G : Type u) [Group G] [Finite G]
    (hK : Quasithin.IsKGroup IsKnownSimple G)
    (h3 : Nat.Coprime 3 (Nat.card G)) (h5 : Nat.Coprime 5 (Nat.card G)) :
    Group.IsSolvable G := by
  exact Quasithin.IsKGroup.isSolvable_of_coprime_simple
    (fun _ _ _ _ h h3 h5 => h.2.2.solvable_of_coprime_three_five h3 h5)
    G hK h3 h5
end CFSG.KnownSimple
