module

public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Point.RadicalAction.Geometry
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Point.RadicalAction.Transport

/-!
# The point-radical action in the natural symplectic group

For a nonbinary field of characteristic two, the embedded two-core of the
point local is elementary abelian, and its parabolic-invariant subgroup
lattice is exactly `1 < Z < Q`. Thus both factors are chief factors over the
binary field, and the action is indecomposable even without defining-field
scalar closure. Here `Z` is the literal long root zero. Its natural
displacement is the point, the displacement of `Q` is the perpendicular
hyperplane, and the full pointwise hyperplane fixer is `Z`.

The imported lattice proof uses binary natural irreducibility, `[Q,D]=Q`,
and the root torus. The geometric proof uses the actual matrices and
nondegeneracy of the form. The final identities keep the literal conjugation
and natural linear maps for application to a marked source action.

Source: Aschbacher--Smith 11.5.7, assertion (!) and its applications,
refs/quasithin.pdf, printed pp.782--783.
-/

public noncomputable section
open Subgroup
namespace Theory.SpecificGroups.SymplecticFour.PointRadicalAction
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
variable {n : ℕ} (hcard : Nat.card F = 2 ^ n) (hn : 1 < n)

include hcard hn

/-- The ambient two-core is the embedded explicit point radical. -/
theorem core_eq_radical :
    (pointLocal (F := F)).pCoreIn 2 = pointRadical.map pointLocal.subtype := by
  rw [pCoreIn, pointLocal_core_eq hcard hn]

/-- The radical is a binary vector group in the actual symplectic carrier. -/
theorem core_elementaryAbelian :
    IsElementaryAbelian 2 ((pointLocal (F := F)).pCoreIn 2) := by
  rw [core_eq_radical hcard hn]
  exact IsElementaryAbelian.map pointLocal.subtype

/-- The embedded local center moves exactly the standard point. -/
theorem center_displacement :
    displacementSpace ((center (pointLocal (F := F))).map pointLocal.subtype) =
      point F := by
  rw [center_eq_root hcard hn, root_displacement]

/-- The literal ambient two-core moves exactly the perpendicular hyperplane. -/
theorem core_displacement :
    displacementSpace ((pointLocal (F := F)).pCoreIn 2) =
      (form F).orthogonal (point F) := by
  rw [core_eq_radical hcard hn, radical_displacement]

/-- The entire pointwise hyperplane fixer is the embedded local center. -/
theorem hyperplane_fixer_eq_center :
    fixingSubgroup (Sp F) ((form F).orthogonal (point F) : Set (Vector F)) =
      (center (pointLocal (F := F))).map pointLocal.subtype := by
  rw [hyperplane_fixer, center_eq_root hcard hn]

/-- Center displacement at an arbitrary symplectically conjugate point. -/
theorem conjugate_center_displacement (g : Sp F) :
    displacementSpace
      (((center (pointLocal (F := F))).map pointLocal.subtype).map
        (MulAut.conj g).toMonoidHom) =
      (point F).map (toLinear g).toLinearMap := by
  rw [displacement_conjugate, center_displacement hcard hn]

/-- Two-core displacement at an arbitrary symplectically conjugate point. -/
theorem conjugate_core_displacement (g : Sp F) :
    displacementSpace
      (((pointLocal (F := F)).map (MulAut.conj g).toMonoidHom).pCoreIn 2) =
      ((form F).orthogonal (point F)).map (toLinear g).toLinearMap := by
  rw [← map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective,
    displacement_conjugate, core_displacement hcard hn]

/-- The pointwise fixer uses the same conjugation as the transported center. -/
theorem conjugate_hyperplane_fixer (g : Sp F) :
    fixingSubgroup (Sp F)
      (((form F).orthogonal (point F)).map (toLinear g).toLinearMap : Set (Vector F)) =
      ((center (pointLocal (F := F))).map pointLocal.subtype).map
        (MulAut.conj g).toMonoidHom := by
  rw [fixer_conjugate, hyperplane_fixer_eq_center hcard hn]

end Theory.SpecificGroups.SymplecticFour.PointRadicalAction
