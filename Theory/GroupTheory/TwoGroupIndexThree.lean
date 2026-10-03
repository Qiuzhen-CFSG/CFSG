module
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Index

/-!
# Two-subgroups meet an index-three subgroup with index at most two

If a finite two-subgroup lies in P and K has relative index three in P,
its intersection with K has index at most two. Relative index is monotone
in the upper subgroup, so it is bounded by three. The index of any subgroup
of a finite two-group is a power of two, leaving only one or two.

This elementary index step is used for the terminal normalizer in
Stellmacher (9.9), printed p.56/PDF p.46 of
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Subgroup
universe u

public theorem two_group_relIndex_le_two_of_relIndex_three
    {G : Type u} [Group G] [Finite G]
    (U K P : Subgroup G) (hU : IsPGroup 2 U) (hUP : U≤P)
    (hindex : K.relIndex P=3) : K.relIndex U≤2 := by
  have hbound : K.relIndex U≤3 :=
    (Subgroup.relIndex_le_of_le_right hUP (by rw [hindex]; decide)).trans_eq hindex
  obtain ⟨n,hn⟩ := hU.index (K.subgroupOf U)
  change K.relIndex U=2^n at hn
  rw [hn] at hbound ⊢
  by_cases hsmall : n≤1
  · exact (Nat.pow_le_pow_right (by decide : 1≤2) hsmall).trans (by decide)
  · have hlarge : 2≤n := by omega
    have hh := Nat.pow_le_pow_right (by decide : 1≤2) hlarge
    omega

end Subgroup
