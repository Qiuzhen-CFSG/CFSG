module

public import CFSG.Quasithin.Chapter16.Section03.ThompsonObstruction.AmbientComputation.DihedralActions.ActionConstruction.Choice
public import CFSG.Quasithin.Chapter16.Section03.ThompsonObstruction.AmbientComputation.DihedralActions.ActionConstruction.DihedralFactors
public import CFSG.Quasithin.Chapter16.Section03.ThompsonObstruction.AmbientComputation.DihedralActions.ActionConstruction.MaximalAction

/-!
# Construction of the Thompson action data

Choose characteristic index-two rotations and the candidate in `{u,t*u}` with
the largest fixed subgroup. Its proved action alternative determines the factor:
when it centralizes the commuting Sylow subgroup, take the whole dihedral group
or the index-two omega subgroup of the semidihedral group; otherwise take
`⟨y²,t⟩`. The factor constructions supply actual dihedral equivalences and identify
the ambient center with `⟨z⟩` in both cases.

This constructs every field of `ActionData` from `Prepared`, without a rank
geometry assumption. The rank-geometry wrapper supplies the requested interface
for the later Thompson-subgroup assembly, which remains a separate calculation.

Source: Aschbacher--Smith, 16.3.12, printed pp.1181--1182 / PDF pp.1198--1199.
-/

public section

namespace CFSG.Quasithin.Chapter16.ThompsonObstruction.AmbientComputation
open Subgroup ActionConstruction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {z t : G} {L : Subgroup G}

/-- The prepared local data construct the rotations, maximizing action, and
dihedral factor, including its original ambient center and all index clauses. -/
theorem exists_actionData_of_prepared (d : Prepared T z t L) : Nonempty (ActionData d) := by
  obtain ⟨a⟩ := exists_rotationChoice d
  rcases maximizing_action_cases d a with hcentral | ⟨hlarge, haction⟩
  · obtain ⟨R, hR, hD, hZ, hfactor⟩ := exists_standard_factor d a
    exact ⟨{
      y := a.y
      rotation_le := a.rotation_le
      rotation_characteristic := a.characteristic
      rotation_index := a.index
      rotation_order := ⟨a.exponent, a.exponent_ge, a.order⟩
      reflection_generation := a.generation
      reflection_action := a.reflection_action d
      w := a.w
      candidate := a.candidate
      maximizing := a.maximizing
      involution := a.involution d
      R := R
      R_le := hR
      dihedral := hD
      center_eq := hZ
      alternative := Or.inl ⟨hcentral, hfactor⟩ }⟩
  · obtain ⟨hR, hD, hZ⟩ := even_rotation_factor d a hlarge
    exact ⟨{
      y := a.y
      rotation_le := a.rotation_le
      rotation_characteristic := a.characteristic
      rotation_index := a.index
      rotation_order := ⟨a.exponent, a.exponent_ge, a.order⟩
      reflection_generation := a.generation
      reflection_action := a.reflection_action d
      w := a.w
      candidate := a.candidate
      maximizing := a.maximizing
      involution := a.involution d
      R := zpowers (a.y ^ 2) ⊔ zpowers t
      R_le := hR
      dihedral := hD
      center_eq := hZ
      alternative := Or.inr ⟨hlarge, haction, rfl⟩ }⟩

/-- The action-data input to the Thompson calculation is discharged for the
source rank geometry; the construction itself already follows from `Prepared`. -/
theorem exists_actionData (d : Prepared T z t L) (_r : RankGeometry d) :
    Nonempty (ActionData d) :=
  exists_actionData_of_prepared d

end CFSG.Quasithin.Chapter16.ThompsonObstruction.AmbientComputation
