module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection.Edges.Algebra
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection.Edges.Parabolic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection.Edges.Plane

/-!
# The opposite initial edge calculation

The opposite natural action selects a compatible parabolic fixing the moving
class modulo B_c, with zero fixed subgroup on U_c. It normalizes the original
cyclic displacement, which is therefore a plane in the actual U_c. The
algebraic calculation identifies this plane with both endpoint edge
commutators and proves the kernel centralizer product.

The constructor below discharges the parabolic and plane premises from the
original noncontainment and opposite frame. Critical-path placement remains
the separate geometric step after these identities on printed p.891.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4.1), claim (1), pp.890–891.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The opposite frame supplies the moving element, both edge identities,
and the relative kernel centralizer product at the actual common neighbor. -/
theorem edgeData_nonempty (common : CommonFacts R source geometry)
    {a c : Vertex R} (hb : 4 < geometry.b R)
    (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2)
    (hn : ¬ ⁅Z R a, Q R c⁆ ≤ fixedCore R c)
    (f : FrameAt a c) (hop : ¬ f.SameOrientation) : Nonempty (EdgeData a c) := by
  obtain ⟨p⟩ := parabolicSeed_nonempty common hb ha hc hd hn f hop
  exact p.edgeData_nonempty common hb ha hc hd f hop

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection
