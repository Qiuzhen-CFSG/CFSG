module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.MarkedPlane.Scalar.Core
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.MarkedPlane.Scalar.Geometry
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.MarkedPlane.Scalar.ExternalEven
public import Theory.Representation.HexacodeAction.EvenCommutant

/-!
# External scalar action and the marked definite planes

The external residual `Y_E` acts on the full source normal-closure module
by binary linear automorphisms commuting with the even hexacode group.
The concrete commutant calculation identifies each such automorphism
with a power of `hexZ`. Its ambient conjugation formula proves
`ScalarActionOn` for every element of `Y_E`, including actors outside `G₀`.

The genuine orthogonal marking shows that `Y_E` preserves both definite
planes, while `V = [V,Y_E]` forces a nonidentity scalar to occur. Since
either nonidentity scalar generates the cubic scalar group, each actual
marked plane is stable under `hexZ`. These conclusions use only the
source configuration and the given hexacode coordinates. Construction
of those inputs and the full-weight recognition remain with their owners.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
printed pp.1121–1122 and 1152–1155, with the field convention of K.1.3
on printed p.453.
-/

public section

open Subgroup
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.MarkedPlane

variable {G : Type*} [Group G] {G₀ M V : Subgroup G}
  {d : NaturalOrthogonalAction M V}
  [IsElementaryAbelian 2 (moduleClosure (V.subgroupOf G₀))]
  {hC : IsPGroup 2 (centralizer (V.subgroupOf G₀ : Set G₀))}
  {hcore : pCore 2 G₀ ≤ centralizer (V.subgroupOf G₀ : Set G₀)}
  (c : HexacodeCoordinates (V.subgroupOf G₀) hC hcore)

/-- Every actual external residual actor is a cubic scalar on the whole module. -/
theorem first_residual_scalarAction (cfg : SourceConfiguration G₀ M V d) :
    ScalarActionOn c cfg.YE := by
  intro y hy
  obtain ⟨k, hk⟩ := Representation.Hexacode.commuting_even_automorphism_eq_scalar
    (externalAction c cfg ⟨y, hy⟩) (externalAction_commutes_even c cfg ⟨y, hy⟩)
  refine ⟨k, fun w => ?_⟩
  rw [← externalAction_ambient c cfg ⟨y, hy⟩ w, hk w]

/-- The specific cubic scalar stabilizes each original definite plane. -/
theorem plane_scalar_stable [Finite G] (cfg : SourceConfiguration G₀ M V d)
    (i : OrthogonalPlaneIndex) :
    Atlas.Codes.hexZ ∈ Representation.BinaryOffender.subspaceStabilizer
      Representation.Hexacode.action (vectorImage c (d.plane i)) :=
  plane_scalar_stable_of_scalarAction c cfg (first_residual_scalarAction c cfg) i

end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.MarkedPlane
