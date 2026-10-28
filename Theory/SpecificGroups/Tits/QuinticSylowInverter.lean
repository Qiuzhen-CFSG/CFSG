module

public import Theory.SpecificGroups.Tits.EscapingSylowOvergroups
public import Theory.GroupTheory.SelfNormalizingSylowQuinticInverter

/-!
# An inverter in the actual Tits component Sylow

The native Sylow normalizer calculation is self-normalizing. It therefore
supplies an inverter of every normalized subgroup with two-core quotient
of order five. The whole subgroup and the supplied Sylow marking are
retained, including a potentially nontrivial two-core in the actor.

Source application: Aschbacher--Smith 6.1.4, printed pp.665--666.
-/

public section
open Subgroup
namespace Tits

/-- An actual supplied Tits Sylow element inverts the whole quintic actor
modulo the actor's full two-core. Its lift need not be an involution. -/
theorem quintic_sylow_inverter
    {G : Type*} [Group G] (e : G ≃* ParrottGroup)
    (S : Sylow 2 G) (Y : Subgroup G)
    (hSY : (S : Subgroup G) ≤ normalizer (Y : Set G))
    (hfive : Nat.card (Y ⧸ pCore 2 Y) = 5) :
    ∃ u : G, u ∈ S ∧ ∀ y ∈ Y, u*y*u⁻¹*y ∈ Y.pCoreIn 2 := by
  let : Finite G := Finite.of_equiv ParrottGroup e.symm.toEquiv
  exact Theory.GroupTheory.self_normalizing_sylow_quintic_inverter S Y
    (BinarySylowOvergroups.sylow_geometry e S).1 hSY hfive

end Tits
