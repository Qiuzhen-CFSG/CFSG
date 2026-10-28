module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.DistanceReduction.Backward
public import Theory.GroupTheory.ConjugateSpanOrder

/-!
# The central seed in the source (5.9) orbit span

If two original-group vertices share an edge neighbor, the orbit span of
one Z-layer under the other's stabilizer contains the latter Z-layer.
The shared edge omega-center belongs to the first layer, and local
transitivity carries it over every generator of the second layer.

This supplies the literal inclusion Z_mu <= <Z_c^(G_mu)> used at the end
of MS93 (5.9), printed pp.921--922. It uses the full central layers.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.StrictIndex
variable {M : Type*} [Group M] [Finite M] {R : Subgroup M}

/-- The source orbit span contains the full center layer at its acting vertex. -/
theorem local_seed_le_conjugateSpan_of_common_neighbor
    {c mu t : Vertex R} (hc : color R c = false) (hmu : color R mu = false)
    (hct : Adjacent R c t) (hmut : Adjacent R mu t) :
    Z R mu ≤ conjugateSpanBy (Z R c) (stabilizer R mu) := by
  conv_lhs => rw [Z, if_pos hmu]
  apply iSup_le
  intro u
  apply iSup_le
  intro hmu_u
  have hu : color R u ≠ false := by
    simpa only [hmu] using (adjacent_color_ne R hmu_u).symm
  obtain ⟨g,hg,hgu⟩ := stabilizer_transitive_neighbors R mu hmut hmu_u
  have hseed : Z R t ≤ conjugateSpanBy (Z R c) (stabilizer R mu) :=
    (adjacent_Z_le R hc hct).trans (le_conjugateSpanBy _ _)
  have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hseed
  have hn := le_normalizer_conjugateSpanBy (Z R c) (stabilizer R mu)
    ((stabilizer R mu).inv_mem hg)
  have he : (conjugateSpanBy (Z R c) (stabilizer R mu)).map
      (MulAut.conj g⁻¹).toMonoidHom =
      conjugateSpanBy (Z R c) (stabilizer R mu) := mem_normalizer_iff_map_conj_eq.mp hn
  rw [he,←Z_act,hgu] at hh
  simpa only [Z,if_neg hu] using hh

/-- The source conjugator and original first two edges supply that inclusion
with the literal mu = a^y. -/
theorem conjugated_start_seed_le_source_span
    {geometry : Geometry R} (hb : 2 ≤ geometry.b R) {a e : Vertex R}
    (p : CriticalPath R geometry a e) (y : FreeAmalgam R)
    (hy : y ∈ stabilizer R (p.walk.getVert 2)) :
    Z R (act R y a) ≤ conjugateSpanBy (Z R (p.walk.getVert 2))
      (stabilizer R (act R y a)) := by
  have hlen : 2 ≤ p.walk.length := by rwa [p.length_eq_b]
  have hc := (p.vertex_color hlen).mpr (by decide : Even 2)
  have hmu : color R (act R y a) = false := by
    rw [action_preserves_color]
    exact p.start_color
  have hat : Adjacent R a (p.walk.getVert 1) := by
    have hh := (cosetGraph_adj R _ _).mp
      (p.walk.adj_getVert_succ (by omega : 0 < p.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using hh
  have hct : Adjacent R (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm R ((cosetGraph_adj R _ _).mp
      (p.walk.adj_getVert_succ (by omega : 1 < p.walk.length)))
  apply local_seed_le_conjugateSpan_of_common_neighbor hc hmu
    (t := act R y (p.walk.getVert 1))
  · have hh := (adjacent_act_iff R y _ _).mpr hct
    rwa [show act R y (p.walk.getVert 2) = p.walk.getVert 2 from hy] at hh
  · exact (adjacent_act_iff R y _ _).mpr hat

end CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.StrictIndex
