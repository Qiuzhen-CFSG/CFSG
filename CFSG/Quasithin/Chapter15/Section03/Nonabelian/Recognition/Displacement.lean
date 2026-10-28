module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.Action
public import Theory.Representation.NormalConstituentDisplacement

/-!
# The rank-two reductions in 15.3.57(2)

The source's rank-two commutator is the image of `v - 1` on the actual
binary quotient. Irreducible constituents of rank at least three force
noncentralization and are individually invariant under the cyclic actor.
The source's semisimple decomposition and two-summand conclusion are separate
remaining steps; these lemmas do not assume them.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), p.1148.
-/

public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition
variable {G : Type*} [Group G] [Finite G] (Z ZS : Subgroup G)
  [(Z.subgroupOf (closureU Z ZS)).Normal]
  [IsElementaryAbelian 2 (VectorQuotient Z ZS)]
  (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))

/-- The noncentralization conclusion of 15.3.57(2), with the source's
`V*` given as the cyclic subgroup of its actual generating involution. -/
theorem commutator_ne_bot_of_constituent_rank
    (K : Subgroup (ActorQuotient Z)) (v : ActorQuotient Z)
    (hsmall : ∀ J : Subrepresentation ((actorRepresentation Z ZS hkernel).comp K.subtype),
      J.toRepresentation.IsIrreducible → 3 ≤ Module.finrank (ZMod 2) J.toSubmodule)
    (hrank : Module.finrank (ZMod 2)
      (LinearMap.range (actorRepresentation Z ZS hkernel v - LinearMap.id)) = 2) :
    ⁅K, zpowers v⁆ ≠ ⊥ := by
  apply Representation.commutator_zpowers_ne_bot_of_small_displacement
    (actorRepresentation Z ZS hkernel) K v
  · intro J hJ
    rw [hrank]
    exact hsmall J hJ
  · rw [hrank]; decide

/-- Every simple constituent in 15.3.57(2) is invariant under `V*`. -/
theorem constituent_invariant_of_rank_two
    (K : Subgroup (ActorQuotient Z)) [K.Normal] (v : ActorQuotient Z)
    (hrank : Module.finrank (ZMod 2)
      (LinearMap.range (actorRepresentation Z ZS hkernel v - LinearMap.id)) = 2)
    (J : Subrepresentation ((actorRepresentation Z ZS hkernel).comp K.subtype))
    (hJ : J.toRepresentation.IsIrreducible)
    (hdim : 3 ≤ Module.finrank (ZMod 2) J.toSubmodule) :
    J.toSubmodule.map (actorRepresentation Z ZS hkernel v) = J.toSubmodule := by
  apply Representation.map_constituent_eq_self_of_displacement_lt
    (actorRepresentation Z ZS hkernel) K v J hJ
  rwa [hrank]

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition
