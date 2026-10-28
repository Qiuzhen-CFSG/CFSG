module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.ForwardCoreKernel
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.ForwardSpanAction
/-!
# The core commutator has second-vertex image of order at most two

At distance four the forward hyperplane kernel moves the second vertex's
natural module through a line. The literal fixed-index formula and the
natural hyperplane-fixer calculation bound its image modulo the second
kernel by two. The core commutator lies in this hyperplane kernel, so it
inherits the same bound. This supplies the residual index used in the
central-extension transfer in MS93 (3.10)(i), printed p.880, for the terminal
(5.12) configuration. The final application uses the actual characteristic
replacement from SourceData.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)

/-- The entire forward hyperplane kernel has image of order at most two. -/
theorem forward_hyperplane_kernel_second_vertex_index_le_two
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : s.geometry.b R=4) {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e) :
    (Q R (p.walk.getVert 2)).relIndex (Q R (alpha R)⊓centralizer
      (U R (p.walk.getVert 2)⊓B R (alpha R) (s.geometry.Z_normal _):Set (FreeAmalgam R)))≤2 := by
  let T₀ := Q R (alpha R)⊓centralizer
    (U R (p.walk.getVert 2)⊓B R (alpha R) (s.geometry.Z_normal _):Set (FreeAmalgam R))
  have hl : p.walk.length=4 := p.length_eq_b.trans hb
  have hc : color R (p.walk.getVert 2)=false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent R (alpha R) (p.walk.getVert 1) := by
    apply (cosetGraph_adj R _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i:=0) (by omega)
  have hct : Adjacent R (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm R ((cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ (i:=1) (by omega)))
  have ht : color R (p.walk.getVert 1)=true := by
    have hn := adjacent_color_ne R hat
    change false≠color R (p.walk.getVert 1) at hn
    cases hh:color R (p.walk.getVert 1) <;> simp_all
  have hTG : T₀≤stabilizer R (p.walk.getVert 2) :=
    (inf_le_left.trans (Q_le_adjacent_h R ht hat)).trans
      (fun _ hx => hx.2 _ (adjacent_symm R hct))
  have hi := s.forward_moving_index_eq_two_of_distance_four h u hfull hb p
  have hcard := (s.moving_hyperplane_commutator_le_seed h u hfull rfl hc hat hct hi.le).1
  let := finite_stabilizer R (p.walk.getVert 2)
  let : Finite (U R (p.walk.getVert 2)) := Finite.of_injective
    (inclusion ((DistanceEight.U_le_Z R _).trans (Z_le_stabilizer R _))) (inclusion_injective _)
  have hfixed : (centralizer (T₀:Set (FreeAmalgam R))).relIndex (U R (p.walk.getVert 2))≤2 := by
    rw [s.moving_fixedIndex_eq_commutator_card h
      (s.projection_surjective_of_radical_image_le_conjugate u hfull.le) _ hc T₀ hTG]
    exact hcard
  exact s.moving_small_fixed_index_implies_small_image h hc T₀ hTG hfixed

/-- The source residual inherits the index bound needed for derived transfer. -/
theorem core_commutator_second_vertex_index_le_two
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : s.geometry.b R=4) {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e) :
    (Q R (p.walk.getVert 2)).relIndex ⁅Q R (alpha R),Ltilde R (alpha R)⁆≤2 := by
  have ht := s.core_commutator_le_forward_hyperplane_kernel u hfull (by omega) p
  let : Finite (Q R (alpha R)⊓centralizer
      (U R (p.walk.getVert 2)⊓B R (alpha R) (s.geometry.Z_normal _):Set (FreeAmalgam R)) :
        Subgroup (FreeAmalgam R)) := by
    let := finite_stabilizer R (alpha R)
    have hQG : Q R (alpha R)≤stabilizer R (alpha R) := fun _ hx => hx.1
    exact Finite.of_injective (inclusion (inf_le_left.trans hQG)) (inclusion_injective _)
  exact (relIndex_le_of_le_right ht index_ne_zero_of_finite).trans
    (s.forward_hyperplane_kernel_second_vertex_index_le_two h u hfull hb p)
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
variable {K : Type*} [Group K] [Finite K] {L W : Subgroup K} [L.Normal] [W.Normal]
  {T : Sylow 2 K} (d : NaturalSixControl.SourceData L W T) (hm : IntrinsicMSPair d)
local notation "J" => (L⊔d.B : Subgroup K)
local notation "R" => d.B.subgroupOf J

/-- The actual characteristic replacement supplies the residual index bound. -/
theorem reducedSource_block_or_core_commutator_second_vertex_index_le_two
    (r : CharacteristicReduction (L.subgroupOf J) R) {e : Vertex r.radical}
    (p : CriticalPath r.radical ((originalSource d hm).reduce r).geometry (alpha r.radical) e)
    (hb : ((originalSource d hm).reduce r).geometry.b r.radical=4) :
    IsAlternatingBlock L 6 ∨
      (Q r.radical (p.walk.getVert 2)).relIndex
        ⁅Q r.radical (alpha r.radical),Ltilde r.radical (alpha r.radical)⁆≤2 := by
  rcases reducedSource_block_or_full_point_image d hm r with hblock|hfull
  · exact Or.inl hblock
  · right
    let s := (originalSource d hm).reduce r
    have hf : r.radical.map s.projection=Model.E.map (MulAut.conj d.relabeler.val⁻¹).toMonoidHom := by
      simpa only [Model.pointCore_eq_exceptional] using hfull
    exact s.core_commutator_second_vertex_index_le_two (reduced_nativeCentralLayer d hm r) _ hf hb p
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
