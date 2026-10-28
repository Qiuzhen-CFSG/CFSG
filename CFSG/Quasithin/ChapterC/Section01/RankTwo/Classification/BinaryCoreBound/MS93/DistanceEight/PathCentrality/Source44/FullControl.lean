module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Source44.RegularPaths
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape

/-!
# The genuine Earlier consumer from full source local control

Full (4.4.1) local control directly supplies the R1 fixed-core bound in
(4.4.5), so this route does not need the stronger critical-prefix
natural-section exclusion used by the parallel source-critical interface.
The actual first image calculation and quotient recognition construct the
full radius natural section.  The original orbit-escape theorem and source
replacement construct the extended path, and the concluding calculation
fills every field of the existing Earlier record.

The only preceding source conclusions still required are full local
commutator control and prescribed replacement.  Their producers remain
separate obligations. No local natural section, final centrality, distance
eight, or edge index is an additional premise.

Source: MS93 (4.4.1)--(4.4.5), printed pp.890--895.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44.FullControl
open PathCentrality.RegularPaths PathCentrality.FinalCalculation
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

omit [Finite M] in
/-- Full local control supplies the literal R1 fixed-core estimate directly. -/
theorem firstCommutator_le_fixed
    (hb : 6 < geometry.b R) (hlocal : LocalCommutatorControl R)
    {a : Vertex R} (e : PathCentrality.RegularPaths.ExtendedPath geometry a) :
    ExtendedPath.firstCommutator e ≤ fixedCore R (e.walk.getVert 4) := by
  have hc := ExtendedPath.vertex_color e (i := 4) (by decide) (by omega)
  have hf := ExtendedPath.vertex_color e (i := 6) (by decide) (by omega)
  have hfc : (cosetGraph R).dist (e.walk.getVert 6) (e.walk.getVert 4) = 2 := by
    rw [SimpleGraph.dist_comm, ExtendedPath.distance e (by decide) (by omega)]
  obtain ⟨g,hg,hturn⟩ := e.turns 4 (by decide) (by decide) (by omega)
  have hspan : Z R (e.walk.getVert 2) ≤ localZSpan R (e.walk.getVert 6) (e.walk.getVert 4) := by
    have hh := le_iSup (fun k : stabilizer R (e.walk.getVert 4) =>
      Z R (act R k (e.walk.getVert 6))) ⟨g,hg⟩
    have hturn' : act R g (e.walk.getVert 6) = e.walk.getVert 2 := by
      simpa only [Nat.reduceAdd, Nat.reduceSub] using hturn
    simpa only [hturn', localZSpan] using hh
  have hv := (e.window 2 (by decide) (by decide)).end_color
  have hV : V R (e.walk.getVert (2 + geometry.b R)) ≤ Q R (e.walk.getVert 6) := by
    apply V_le_Q_of_dist_add_two_lt R hv
    rw [SimpleGraph.dist_comm, ExtendedPath.distance e (by omega) (by omega)]
    omega
  exact (commutator_mono hspan (inf_le_inf hV le_rfl)).trans
    (CommutatorPropagation.span_kernel_intersection_le_fixed (by omega) hlocal hf hc hfc)

/-- Fixed-core transport and the retained endpoint exclude an R1 larger
than the original critical line. -/
theorem firstCommutator_le_critical
    (common : CommonFacts R source geometry) (hb : 6 < geometry.b R)
    (hlocal : LocalCommutatorControl R)
    {a : Vertex R} (e : PathCentrality.RegularPaths.ExtendedPath geometry a) :
    ExtendedPath.firstCommutator e ≤
      ⁅Z R (e.walk.getVert 2),Z R (e.walk.getVert (2 + geometry.b R))⁆ := by
  by_contra hn
  have hE := RadiusImage.transport_equality (source := source) e 2 (by decide) (by omega)
    (firstCommutator_le_fixed hb hlocal e)
    (ExtendedPath.firstCommutator_eq_edge_of_not_le_critical e common hn)
  have hc : ExtendedPath.firstCommutator e ≤
      centralizer (Z R (e.walk.getVert (6 + geometry.b R)) : Set (FreeAmalgam R)) :=
    (ExtendedPath.firstCommutator_le_radius e common).trans
      (ExtendedPath.radius_centralizes_later_Z e hb)
  have hn' := (le_centralizer_iff.mp hc).trans (Subgroup.centralizer_le_normalizer _)
  have hlocal' := (e.window 6 (by decide) (by decide)).endpoint_Z_le_start_stabilizer (by omega)
  apply e.nonnormalization 6 (by decide) (by decide) (by decide)
  apply le_inf hlocal'
  simpa only [hE] using hn'

/-- Both actual (4.4.5) calculations construct the full radius section,
including its literal quotient projection and conjugation action. -/
theorem natural_section
    (common : CommonFacts R source geometry) (hb : 6 < geometry.b R)
    (hlocal : LocalCommutatorControl R)
    {a : Vertex R} (e : PathCentrality.RegularPaths.ExtendedPath geometry a)
    {c : Vertex R} (hc : color R c = false) :
    Nonempty (Escape.NaturalSectionAt c (V R c) (Z R c)) := by
  obtain ⟨s⟩ := natural_section_of_critical_hyperplane common
    (e.window 2 (by decide) (by decide))
    (RadiusImage.source_image_le_two common hb hlocal e)
    (firstCommutator_le_critical common hb hlocal e)
  exact natural_section_at_any_center (e.window 2 (by decide) (by decide)).end_color hc s

/-- The original full-control orbit escape and prescribed replacement
construct an extended source path at every M-vertex. -/
theorem extended
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    (hlocal : LocalCommutatorControl R)
    (replacement : ∀ {a a'} (p : CriticalPath R geometry a a'),
      HasTurnConjugators R p → PrescribedReplacement R p)
    (a : Vertex R) (ha : color R a = false) :
    Nonempty (PathCentrality.RegularPaths.ExtendedPath geometry a) := by
  obtain ⟨a',p,hp⟩ := exists_regular_of_orbitEscape hb
    (fun p => orbitEscapeAlternative common hb hlocal p) a ha
  exact Source44.RegularPaths.extended_of_regular_and_replacement common hb.le replacement p hp a ha

/-- Actual final consumer: every Earlier field is constructed from full
local control and prescribed replacement, without prefix exclusion. -/
theorem earlier
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    (hlocal : LocalCommutatorControl R)
    (replacement : ∀ {a a'} (p : CriticalPath R geometry a a'),
      HasTurnConjugators R p → PrescribedReplacement R p) : CoreFactors.Earlier R geometry := by
  obtain ⟨e⟩ := extended common hb hlocal replacement (alpha R) rfl
  have hsix := CommutatorPropagation.six_lt common hb hlocal
    (e.window 0 (by decide) (by decide)) (e.window_regular 0 (by decide) (by decide))
  have hn := fun c hc => natural_section common hsix hlocal e (c := c) hc
  obtain ⟨hd,hc,hi⟩ := Conclusion.ProductSource.OriginalSource.conclusions common hsix hlocal replacement hn e
  exact {
    distance := hd
    natural_section := hn
    centrality := hc
    edge_Z_index := fun a t ha hat => (hi a t ha hat).1
    edge_Q_index := fun a t ha hat => (hi a t ha hat).2
    extended := extended common hb hlocal replacement
    replacement := fun _ _ p hp => replacement p hp }

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44.FullControl
