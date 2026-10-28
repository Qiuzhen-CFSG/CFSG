module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry

/-!
# The same flag in the local and final component geometry

The final geometry is built from the original marked field flag and its
binary pullbacks. Its V1, L1 and R1 agree definitionally with the preceding
local geometry, so no subgroup transport or replacement quotient is needed
when applying the relative-Sylow weak-closure theorem.
Source: Aschbacher--Smith, §§11.1, 11.4--11.5, pp.760,777--779.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry
open Subgroup
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)

/-- Name the final component geometry using exactly the preceding field flag. -/
def ofFlag : Closure.Geometry D where
  input := S
  point := c.binarySubspace (f.space 0)
  plane := c.binarySubspace (f.space 1)
  threeSpace := c.binarySubspace (f.space 2)
  X := X
  z := z
  H := H

theorem ofFlag_point : (ofFlag S f X z H).V₁ = f.Vi 0 := rfl
theorem ofFlag_plane : (ofFlag S f X z H).V₂ = f.Vi 1 := rfl
theorem ofFlag_threeSpace : (ofFlag S f X z H).V₃ = f.Vi 2 := rfl
theorem ofFlag_firstResidual : (ofFlag S f X z H).L₁ = f.Li 0 := rfl
theorem ofFlag_secondResidual : (ofFlag S f X z H).L₂ = f.Li 1 := rfl
theorem ofFlag_firstRadical : (ofFlag S f X z H).R₁ = f.Ri 0 := rfl
theorem ofFlag_secondRadical : (ofFlag S f X z H).R₂ = f.Ri 1 := rfl

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry
