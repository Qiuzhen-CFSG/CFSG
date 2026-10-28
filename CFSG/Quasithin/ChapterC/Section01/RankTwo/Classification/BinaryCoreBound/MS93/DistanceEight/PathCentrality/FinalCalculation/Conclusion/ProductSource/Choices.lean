module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion.Selected

/-!
# The two source choices in the final MS93 product

Each choice retains an actual local conjugator taking alpha+1, alpha+2
to beta, delta, and the critical pair (delta, alpha'-2). The avoided
subgroup is the literal critical commutator at (alpha, alpha'). The two
chosen edge subgroups have trivial intersection in Q_(alpha'). These
are the geometric selection clauses on printed p.895; no Ri nontriviality,
terminal-product order, fixed-core conclusion or edge equality is a field.

The construction of the choices and the evaluation of their commutators
are separate source obligations. The elementary geometry below feeds the
already proved local Ri bounds and the product assembly.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), conclusion of (4.4), printed p.895 after (4.4.5).
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion.ProductSource
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- A literal incident conjugate selected in the proof, before evaluating Ri. -/
structure SelectedVertex {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a) where
  beta : Vertex R
  delta : Vertex R
  conjugator : FreeAmalgam R
  mem_stabilizer : conjugator ∈ stabilizer R a
  beta_eq : act R conjugator (e.walk.getVert 5) = beta
  delta_eq : act R conjugator (e.walk.getVert 6) = delta
  critical : CriticalPath R geometry delta (e.walk.getVert (2 + geometry.b R))
  avoids : ¬ ⁅Z R a, Z R (e.walk.getVert (4 + geometry.b R))⁆ ≤
    edgeCommutator R a beta

/-- The printed intersection clause refers to the terminal kernel, not
to a centralizer in an unrelated quotient model. -/
structure SelectedPair {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a) where
  left : SelectedVertex e
  right : SelectedVertex e
  separated : (edgeCommutator R a left.beta ⊓ edgeCommutator R a right.beta) ⊓
    Q R (e.walk.getVert (4 + geometry.b R)) = ⊥

namespace SelectedVertex
variable {a : Vertex R} {e : RegularPaths.ExtendedPath geometry a} (s : SelectedVertex e)

/-- The selected beta is genuinely incident with the original center. -/
theorem adjacent_center : Adjacent R a s.beta := by
  have h := (adjacent_act_iff R s.conjugator (e.walk.getVert 4)
    (e.walk.getVert 5)).mpr (path_adjacent e 4 (by omega))
  rwa [e.center_eq, s.mem_stabilizer, s.beta_eq] at h

/-- The same conjugator makes delta incident with the selected beta. -/
theorem adjacent_delta : Adjacent R s.beta s.delta := by
  have h := (adjacent_act_iff R s.conjugator (e.walk.getVert 5)
    (e.walk.getVert 6)).mpr (path_adjacent e 5 (by omega))
  rwa [s.beta_eq, s.delta_eq] at h

/-- Orbit membership gives the exact distance two, not just a radius bound. -/
theorem distance : (cosetGraph R).dist a s.delta = 2 := by
  have h := dist_act R s.conjugator (e.walk.getVert 4) (e.walk.getVert 6)
  rw [e.center_eq, s.mem_stabilizer, s.delta_eq] at h
  exact h.trans (by simpa only [e.center_eq] using
    (ExtendedPath.distance e (i := 4) (j := 6) (by decide) (by omega)))

/-- Actual application of the preceding local-control theorem to this Ri. -/
theorem local_bounds (common : CommonFacts R source geometry)
    (hb : 6 < geometry.b R) (hlocal : LocalCommutatorControl R) :
    selectedCommutator e s.delta ≤ V R s.delta ⊓ fixedCore R s.delta :=
  selectedCommutator_bounds_of_critical common hb hlocal e s.distance s.critical

end SelectedVertex

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion.ProductSource
