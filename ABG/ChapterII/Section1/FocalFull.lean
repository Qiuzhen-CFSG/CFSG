module
public import ABG.ChapterII.Section1.FusionPatterns
public import GorensteinWalter.GWLemma21

/-!
# Full focal subgroup excludes a normal subgroup of index two

If the focal subgroup of a Sylow two-subgroup is the whole Sylow subgroup,
the ambient finite group has no normal subgroup of index two. This is the
common final step in ABG Chapter II, Section 1, Propositions 1(i) and 2(i),
article pp.10--13.

Mapping the focal subgroup into the ambient group identifies the intersection
of the Sylow subgroup with the ambient commutator subgroup as the whole
Sylow subgroup. The index-two divisibility bound for that intersection then
would say that two divides one. This argument is extracted unchanged from
the quasi-dihedral fusion assembly so both fusion propositions can use it.
-/

namespace ABG

/-- Full Sylow-two focal subgroup rules out an ambient normal subgroup of index two. -/
public theorem no_normal_index_two_of_focal_top
    {G : Type*} [Group G] [Finite G] (P : Sylow 2 G)
    (hF : (P : Subgroup G).focalSubgroupOf = ⊤) : HasNoNormalIndexTwoSubgroup G := by
  have hm := congrArg (fun U : Subgroup P => U.map (P : Subgroup G).subtype) hF
  rw [Subgroup.map_focalSubgroupOf, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hm
  have hcomm : commutator G ⊓ (P : Subgroup G) = (P : Subgroup G) :=
    (Subgroup.commutator_inf_eq_focalSubgroup P).trans hm
  intro N hN hindex
  have hd := GorensteinWalter.normal_index_two_dvd_sylow_inf_commutator_relIndex P N hN hindex
  rw [inf_comm, hcomm] at hd
  norm_num at hd
end ABG
