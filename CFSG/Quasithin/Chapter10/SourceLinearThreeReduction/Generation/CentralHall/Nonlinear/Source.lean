module

public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Inputs

/-!
# Assembly of the nonlinear central Hall torus calculation

The source module analysis and the independent Hall geometry eliminate
the natural and Suzuki rows. In the orthogonal row the actual quotient
isomorphism is retained. The Cartan fixed-vector calculation then places
the literal original Hall action image in the two norm-one factors.

Both source inputs remain explicit. This conditional theorem does not
establish `NonlinearTorusAt` until their producers have discharged them.
Source: Aschbacher--Smith, 10.1.1--2 and 10.2.3, pp.741--742,745.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear
universe u
variable {G : Type u} [Group G] [Finite G] (T : Sylow 2 G)

/-- The two genuine source inputs complete the literal nonlinear action branch. -/
theorem nonlinearTorus_of_moduleAnalysis_and_hallGeometry
    (hmodules : ModuleAnalysisAt T) (hhall : HallGeometryAt T) :
    NonlinearTorusAt T := by
  intro L D H B c hnot
  obtain ⟨geometry, row⟩ := hmodules L D H B c hnot
  have hall := hhall L D H B c geometry
  cases row with
  | natural r hr e coordinates =>
    obtain ⟨coordinates⟩ := coordinates
    exact (hall.natural_excluded r hr e coordinates).elim
  | orthogonal n hn e coordinates =>
    obtain ⟨coordinates⟩ := coordinates
    obtain ⟨e', p⟩ := hall.orthogonal n hn e coordinates
    obtain ⟨p⟩ := p
    obtain ⟨f, hf⟩ := p.image_embedding c.faithful
    exact ⟨n, hn, ⟨e'⟩, f, hf⟩
  | suzuki m hm e coordinates =>
    obtain ⟨coordinates⟩ := coordinates
    exact (hall.suzuki_excluded m hm e coordinates).elim

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear
