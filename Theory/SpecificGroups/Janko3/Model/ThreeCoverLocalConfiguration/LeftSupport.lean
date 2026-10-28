module

public import Theory.SpecificGroups.Janko3.Model.ThreeCoverLocalConfiguration.LeftSupport.Perfect
public import Theory.SpecificGroups.Janko3.Model.ThreeCoverLocalConfiguration.LeftSupport.Membership
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Centralizer.Orders
public import Mathlib.GroupTheory.Sylow

/-!
# The J₃ left perfect support

The literal subgroup `leftSupport` is the conjugate of the fixed centralizer
candidate by the certified model word `conjugator`. Commutator identities
prove that candidate perfect; conjugation preserves perfectness and its
certified order 1920. Its Sylow three-subgroups therefore have order three
and are cyclic. A separate checked word proves that the marked scalar `x`
belongs to this very conjugate.

These are precisely the three left-support inputs of
`ThreeCoverConfig.configurationOfSupports`. This module is independent of
that assembly module, so it can be imported there without a cycle.
Sources: GLS3, Table 5.3h, printed p.269; Aschbacher--Smith A.2.19, p.41,
and I.2.1, p.409. No abstract centralizer identification is assumed.
-/

namespace Sporadic.Janko3.ThreeCoverConfig
open TwoLocal LeftSupportCertificate

private theorem card_map_conj {G : Type*} [Group G] (H : Subgroup G) (g : G) :
    Nat.card (H.map (MulAut.conj g).toMonoidHom) = Nat.card H :=
  Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
    (MulAut.conj g).injective

/-- The concrete conjugated left support is perfect. -/
public theorem leftSupport_perfect : Group.IsPerfect leftSupport := by
  let : Group.IsPerfect centralizerCandidate := centralizerCandidate_perfect
  exact Group.IsPerfect.map (H := centralizerCandidate)
    (MulAut.conj conjugator).toMonoidHom

/-- Conjugation preserves the certified order of the centralizer candidate. -/
public theorem leftSupport_card : Nat.card leftSupport = 1920 :=
  (card_map_conj centralizerCandidate conjugator).trans centralizerCandidate_card

/-- Every Sylow three-subgroup of the concrete left support is cyclic. -/
public theorem leftSupport_cyclicSylow (S : Sylow 3 leftSupport) : IsCyclic S := by
  have hc : Nat.card S = 3 := by
    rw [S.card_eq_multiplicity, leftSupport_card]
    decide +kernel
  exact isCyclic_of_prime_card (α := S) (p := 3) hc

end Sporadic.Janko3.ThreeCoverConfig
