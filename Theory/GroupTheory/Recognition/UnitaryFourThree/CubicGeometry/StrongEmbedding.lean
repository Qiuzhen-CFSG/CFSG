module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.StrongEmbedding
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.ComponentAction
/-!
# The original cubic component stabilizer is not strongly embedded

Apply the proved source IsType obstruction to the literal stabilizer of
the connected cubic component. Its order, recognition model, and internal
fusion are not substituted for the original subgroup.
Source: Aschbacher, Sporadic Groups (1994), 45.11, printed pp.248–249.
-/
public section
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsType z}
variable {P : Sylow 3 (centralizer z)}
theorem SourceConfiguration.componentStabilizer_not_stronglyEmbedded
    (c : SourceConfiguration h P) :
    ¬ BenderSuzuki.IsStronglyEmbedded c.componentStabilizer :=
  h.not_stronglyEmbedded c.componentStabilizer
end Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry
