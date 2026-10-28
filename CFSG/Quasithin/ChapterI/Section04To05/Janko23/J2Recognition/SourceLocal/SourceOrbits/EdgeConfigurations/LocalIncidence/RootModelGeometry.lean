module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.SourceOrbits.EdgeConfigurations.LocalIncidence.RootReduction
public import Theory.SpecificGroups.HeisenbergFour.CubicIncidence

/-!
# Heisenberg-four geometry for the inner incidence branch

The intrinsic model theorem supplies the cubic-pair input of the existing
root-centralizer reduction. The equivalence identifying each pure four-group
centralizer remains the explicit, independent earlier-source input. The
application retains the literal X-conjugates and joins of the source graph.

Source: Aschbacher, *Sporadic Groups* (1994), proof of 47.6(1), p.264;
the centralizer model comes from 46.3 and 46.14.
-/

public section
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.EdgeConfigurations
variable {G : Type*} [Group G] [Finite G]

/-- Intrinsic cubic incidence for the actual published Heisenberg-four carrier. -/
theorem rootModelCubicGeometry : RootModelCubicGeometry :=
  HeisenbergFour.CubicIncidence.cubic_pair_SL23

/-- The inner source branch with model geometry discharged. Pure centralizer
recognition is the independent earlier-source premise, retained explicitly. -/
theorem inner_sl2Join_of_heisenberg_geometry
    (D : Seed G) (hcentralizers : PureFourCentralizerModels D) (Y : D.Vertex)
    (hY : D.graph.Adj D.base Y)
    (hF : Nonempty (fixer D Y ≃* alternatingGroup (Fin 5)))
    (hclass : ∀ t ∈ fixer D Y, orderOf t = 2 → IsConj D.z t)
    (g : localCentralizer D) (hg : (g : G) ∉ actor D Y)
    (eI : intersection D Y g ≃* alternatingGroup (Fin 4)) (x : D.X) :
    sl2Join D Y ((x : G) • ((g : G) • Y)) :=
  inner_sl2Join_of_root_geometry rootModelCubicGeometry D hcentralizers Y hY hF hclass g hg eI x

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.EdgeConfigurations
