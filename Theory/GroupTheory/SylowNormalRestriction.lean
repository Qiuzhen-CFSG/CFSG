module
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Ambient images of Sylow restrictions

In a finite group, a supplied Sylow `p`-subgroup meets every normal subgroup
`N` in the ambient image of a Sylow `p`-subgroup of `N`. The result retains
the supplied Sylow subgroup, with no change by conjugation in the conclusion.

The intrinsic restriction theorem in `SylowNormalIntersection` produces the
Sylow subgroup of `N`. Mapping its defining equality along `N.subtype` turns
`subgroupOf` into the ambient intersection.

This standard Sylow restriction supplies the normal-centralizer Sylow subgroup
in Stellmacher (10.1)(a3), journal p.61 of
`refs/latex/stellmacher-n-group.tex`.
-/

/-- The intersection of a supplied Sylow subgroup with a normal subgroup is
the ambient image of a Sylow subgroup of that normal subgroup. -/
public theorem Sylow.exists_sylow_map_eq_inf_of_normal
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (N : Subgroup G) [N.Normal] :
    ∃ Q : Sylow p N,
      (Q : Subgroup N).map N.subtype = (P : Subgroup G) ⊓ N := by
  obtain ⟨Q, hQ⟩ := P.exists_subgroupOf_eq_of_normal N
  refine ⟨Q, ?_⟩
  rw [hQ, Subgroup.subgroupOf_map_subtype]
