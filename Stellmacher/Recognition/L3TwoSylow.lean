module

public import Stellmacher.ExceptionalType
public import Theory.SpecificGroups.SymmetricFourSylow

/-!
# The dihedral Sylow subgroup of the local L₃(2) type

Any supplied Sylow two-subgroup of a finite group of local `L₃(2)` type is
dihedral. The local pair's intersection is an ambient Sylow subgroup and is
contained in its first subgroup, which is isomorphic to `S₄`. Restricting
the Sylow to that subgroup and transporting the concrete `S₄` Sylow model
gives `DihedralGroup 4`. Ambient Sylow conjugacy then reaches the supplied
Sylow subgroup.

Only the actual local-pair data is used. This bridge applies without
simplicity, a local-solvability hypothesis, or generation of the ambient
group by the pair. It feeds the dihedral branch of global recognition.

Source: the definition of type `L₃(2)` following (8.2) in
`refs/latex/stellmacher-n-group.tex`, and the finite `S₄` Sylow calculation
in `Theory.SpecificGroups.SymmetricFourSylow`.
-/

namespace Stellmacher.Recognition

/-- The actual local `L₃(2)` type makes every supplied ambient Sylow
two-subgroup dihedral. -/
public theorem dihedral_sylow_of_l3Two_type
    {G : Type*} [Group G] [Finite G] (S0 : Sylow 2 G)
    (hType : IsOfL3TwoType G) : IsDihedralGroup S0 := by
  obtain ⟨pair, ⟨model⟩, _⟩ := hType
  have hle : (pair.sylowIntersection : Subgroup G) ≤ pair.first := by
    rw [← pair.intersection_eq]
    exact inf_le_left
  let localSylow := pair.sylowIntersection.subtype hle
  let image := localSylow.mapSurjective (f := model.toMonoidHom) model.surjective
  let toImage : localSylow ≃* image :=
    (localSylow : Subgroup pair.first).equivMapOfInjective
      model.toMonoidHom model.injective
  obtain ⟨dihedralModel⟩ := Equiv.Perm.sylow_two_equiv_dihedral_four image
  refine ⟨4, ⟨?_⟩⟩
  exact (S0.equiv pair.sylowIntersection).trans
    ((Subgroup.subgroupOfEquivOfLe hle).symm.trans
      (toImage.trans dihedralModel))

end Stellmacher.Recognition
