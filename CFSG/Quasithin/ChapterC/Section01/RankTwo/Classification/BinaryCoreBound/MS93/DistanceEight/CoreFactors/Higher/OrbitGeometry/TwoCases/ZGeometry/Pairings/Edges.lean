module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases.ZGeometry.Pairings.Reduction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.First.Layer.Displacement
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Edges
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.LocalLayers

/-!
# The first neighboring image and the edge annihilator

The genuine edge indices in Earlier give an order-four displacement, which
is the fixed plane in the natural eight-group. The common fixed summand is
centralized by the full local group. Decomposing an edge element therefore
puts it in the product of the displacement and that summand. At the opposite
end of the edge, normalization of an index-two subgroup places the first
neighbor's displacement in the same edge group.

These arguments discharge the first two fields of EdgeDisplacements and give
the exact first character image for every conjugate, without a second-layer
hypothesis. The final export reduces the entire comparison to the one still
unproved bound [hatV_c, Q_beta] <= hatV_a. In particular it does not claim to
construct that bound or to finish the source Z-case argument.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4)--(4.5.5), pp.890--899;
the edge indices are those of (4.4), and the product consumer is on p.899.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases.ZGeometry.Pairings
open PathCentrality.LocalCommutator
variable {M : Type*} [Group M] {L R : Subgroup M}
  {geometry : Geometry R} {source : LocalSource L R}

private theorem displacement_le_edge (earlier : Earlier R geometry)
    {a t : Vertex R} (ha : color R a = false) (hat : Adjacent R a t) :
    ⁅Z R a, Q R t⁆ ≤ Z R t := by
  have hloc : Q R t ≤ stabilizer R a := fun _ hx => hx.2 a (adjacent_symm R hat)
  exact commutator_le_of_normalized_index_two _ _ _
    (Escape.EdgeTransfer.edge_Z_le a t ha hat) (earlier.edge_Z_index a t ha hat)
    (hloc.trans (Z_normalized R a))
    ((show Q R t ≤ stabilizer R t from fun _ hx => hx.1).trans (Z_normalized R t))

/-- The actual edge lies in its displacement joined with the common fixed summand. -/
theorem edge_span [Finite M] (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {t : Vertex R} (hat : Adjacent R (alpha R) t) :
    Z R t ≤ ⁅Z R (alpha R), Q R t⁆ ⊔ fixedSummand (R := R) := by
  have hloc : Q R t ≤ stabilizer R (alpha R) := fun _ hx => hx.2 _ (adjacent_symm R hat)
  have hf : fixedSummand (R := R) ≤ centralizer (stabilizer R (alpha R) : Set (FreeAmalgam R)) := by
    have hh := source.X_fixed_eq_stabilizer_fixed (alpha R) rfl
    rw [common.X_eq_Z _ rfl] at hh
    exact hh.le.trans inf_le_right
  have hfZ : fixedSummand (R := R) ≤ Z R t := by
    rw [Escape.EdgeTransfer.edge_Z_eq_fixed common.large_distance (moduleFacts common) _ _ rfl hat]
    exact le_inf inf_le_left (hf.trans (centralizer_le hloc))
  have hplane := Escape.Propagation.edge_fixed_natural_eq_commutator common.large_distance
    (moduleFacts common) (alpha R) t rfl hat (displacement_le_edge earlier rfl hat)
    (Early.First.Layer.edge_displacement_card common earlier rfl hat)
  intro z hz
  let z₀ : Z R (alpha R) := ⟨z,Escape.EdgeTransfer.edge_Z_le _ _ rfl hat hz⟩
  obtain ⟨u,f,huf⟩ := exists_natural_fixed_decomposition common z₀
  change (u : FreeAmalgam R) * f = z at huf
  have hu : (u : FreeAmalgam R) ∈ Z R t := by
    have hh := (Z R t).mul_mem hz ((Z R t).inv_mem (hfZ f.property))
    change z * (f : FreeAmalgam R)⁻¹ ∈ Z R t at hh
    rwa [← huf, mul_inv_cancel_right] at hh
  have huc : (u : FreeAmalgam R) ∈ ⁅Z R (alpha R), Q R t⁆ := hplane ▸ ⟨u.property,hu⟩
  have hh := (⁅Z R (alpha R), Q R t⁆ ⊔ fixedSummand (R := R)).mul_mem
    (mem_sup_left huc) (mem_sup_right f.property)
  exact huf ▸ hh

/-- The two incident Z-groups share the index-two edge, which contains the first displacement. -/
theorem neighbor_movement_le (earlier : Earlier R geometry)
    {a c t : Vertex R} (ha : color R a = false) (hc : color R c = false)
    (hat : Adjacent R a t) (hct : Adjacent R c t) : ⁅Z R c, Q R t⁆ ≤ Z R a :=
  (displacement_le_edge earlier hc hct).trans (Escape.EdgeTransfer.edge_Z_le _ _ ha hat)

private theorem path_edge (p : Higher.SourcePath (alpha R)) :
    Adjacent R (alpha R) (p.walk.getVert 5) := by
  have h := (cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ (i := 4)
    (by rw [p.length_eq]; decide))
  simpa only [p.center_eq] using h

private theorem path_next_edge (p : Higher.SourcePath (alpha R)) :
    Adjacent R (p.walk.getVert 6) (p.walk.getVert 5) :=
  adjacent_symm R ((cosetGraph_adj R _ _).mp
    (p.walk.adj_getVert_succ (i := 5) (by rw [p.length_eq]; decide)))

private theorem path_next_color (p : Higher.SourcePath (alpha R)) :
    color R (p.walk.getVert 6) = false :=
  (PathCentrality.RegularPaths.walk_vertex_color p.start_color p.walk
    (by rw [p.length_eq]; decide : 6 ≤ p.walk.length)).mpr (by decide)

/-- The first map has the exact neighboring image using only CommonFacts, Earlier and its marked section. -/
theorem firstMap_edge [Finite M] (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    (p : Higher.SourcePath (alpha R))
    (s : MarkedDualSection source common (hatV R (alpha R) (p.walk.getVert 6)) (Z R (alpha R)))
    (g : stabilizer R (alpha R)) :
    ((Z R (act R g (p.walk.getVert 6))).subgroupOf
      (hatV R (alpha R) (p.walk.getVert 6))).map (firstMap common s) =
        edgeCharacters (alpha R) (act R g (p.walk.getVert 5)) := by
  have hat : Adjacent R (alpha R) (act R g (p.walk.getVert 5)) := by
    simpa only [show act R g (alpha R) = alpha R from g.property] using
      (adjacent_act_iff R g _ _).mpr (path_edge p)
  have hct := (adjacent_act_iff R g _ _).mpr (path_next_edge p)
  have hc : color R (act R g (p.walk.getVert 6)) = false := by
    simpa only [action_preserves_color] using path_next_color p
  exact firstMap_edge_of_local_bounds common p earlier s g
    (edge_span common earlier hat) (neighbor_movement_le earlier rfl hc hat hct)

/-- Only the second-layer edge displacement remains in the geometric input contract. -/
theorem edgeDisplacements_of_second_movement [Finite M] (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Higher.SourcePath (alpha R))
    (hsecond : ⁅hatV R (p.walk.getVert 6) (p.walk.getVert 8),
      Q R (p.walk.getVert 5)⁆ ≤ hatV R (alpha R) (p.walk.getVert 6)) : EdgeDisplacements p :=
  ⟨edge_span common earlier (path_edge p),
    neighbor_movement_le earlier rfl (path_next_color p) (path_edge p) (path_next_edge p),
    hsecond⟩

/-- Construct both character comparisons once the remaining second-layer displacement is supplied. -/
theorem characterComparisons_of_second_movement [Finite M] (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Higher.SourcePath (alpha R))
    (s : MarkedDualSection source common (hatV R (alpha R) (p.walk.getVert 6)) (Z R (alpha R)))
    (t : MarkedPairSection source common
      (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8))
      (hatV R (alpha R) (p.walk.getVert 6)) true)
    (hsecond : ⁅hatV R (p.walk.getVert 6) (p.walk.getVert 8),
      Q R (p.walk.getVert 5)⁆ ≤ hatV R (alpha R) (p.walk.getVert 6)) : Nonempty (CharacterComparisons p) :=
  characterComparisons_of_displacements common p earlier s t
    (edgeDisplacements_of_second_movement common earlier p hsecond)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases.ZGeometry.Pairings
