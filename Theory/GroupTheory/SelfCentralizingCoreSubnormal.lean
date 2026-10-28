module

public import Theory.GroupTheory.PGroup.SubnormalCore
/-!
# Prime cores in subnormal subgroups of a group of characteristic p

Distinct prime cores commute. If O_p(G) contains its centralizer, every
other prime core is therefore trivial. The p-core monotonicity theorem
along a subnormal chain gives the same vanishing for subnormal subgroups.

This is the odd-core obstruction used for characteristic-two intersections
in Aschbacher–Smith 2.3.9(7), printed pp.525–526. It only needs the intrinsic
centralizer condition and subnormality in the stated finite group.
-/

@[expose] public section

open Subgroup

namespace Subgroup
variable {G : Type*} [Group G]

/-- A self-centralizing p-core rules out every other prime core. -/
theorem pCore_eq_bot_of_other_selfCentralizingCore
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hne : q ≠ p)
    (hc : centralizer (pCore p G : Set G) ≤ pCore p G) : pCore q G = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  have hxc : x ∈ centralizer (pCore p G : Set G) := by
    apply mem_centralizer_iff.mpr
    intro y hy
    exact (pCore_commute_of_ne q p hne x hx y hy).symm
  exact Subgroup.disjoint_def.mp (pCore_disjoint_of_ne q p hne) hx (hc hxc)

/-- The same prime cores vanish in every subnormal subgroup. -/
theorem subnormal_pCore_eq_bot_of_other_selfCentralizingCore [Finite G]
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hne : q ≠ p)
    (hc : centralizer (pCore p G : Set G) ≤ pCore p G)
    (N : Subgroup G) (hN : N.IsSubnormal) : pCore q N = ⊥ := by
  have hcore : (pCore q N).map N.subtype ≤ pCore q G := by
    have hm := pCoreAmbient_mono_of_isSubnormalIn N ⊤ q le_top
      (hN.comap (⊤ : Subgroup G).subtype)
    have he : (pCore q (⊤ : Subgroup G)).map (⊤ : Subgroup G).subtype = pCore q G :=
      pCore_map_iso q Subgroup.topEquiv
    rwa [he] at hm
  rw [pCore_eq_bot_of_other_selfCentralizingCore p q hne hc] at hcore
  apply le_bot_iff.mp
  intro x hx
  exact Subtype.ext (hcore (Subgroup.mem_map_of_mem N.subtype hx))
end Subgroup

end
