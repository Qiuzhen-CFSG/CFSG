module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.SelectedChain
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.SelectedKernel
/-!
# Forward Baumann index two at critical distance four

Choose the native simultaneous neighbor and preserve that same coordinated
choice throughout. Its prescribed backward critical image is small by the
selected-chain theorem. The selected-kernel argument then gives exactly two
for the Baumann index of the original forward moving layer.

The actual characteristic replacement retains only its separately excluded
alternating-block alternative. There is no remaining selected-image,
centrality, or quotient-recognition premise.

Source: MS93 (5.12)(3), in the native full point-core branch.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)

/-- At critical distance four, the prescribed forward moving layer has
Baumann index exactly two. The selected backward smallness is discharged. -/
theorem forward_moving_index_eq_two_of_distance_four
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : s.geometry.b R=4) {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e) :
    (B R (alpha R) (s.geometry.Z_normal _)).relIndex (U R (p.walk.getVert 2))=2 := by
  have hl : p.walk.length=4 := p.length_eq_b.trans hb
  have hd : Adjacent R (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm R ((cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ (i:=1) (by omega)))
  obtain ⟨c⟩ := s.exists_coordinatedChoice h u hfull p _ hd
  exact s.forward_moving_index_eq_two_of_small_choice h u hfull (by omega) p c
    (c.backward_image_lt_four_of_distance_four s h u hfull hb)
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
variable {K : Type*} [Group K] [Finite K]
  {L W : Subgroup K} [L.Normal] [W.Normal] {T : Sylow 2 K}
  (d : NaturalSixControl.SourceData L W T) (hm : IntrinsicMSPair d)
local notation "J" => (L⊔d.B:Subgroup K)

/-- The actual characteristic replacement supplies the source (5.12)(3)
forward index at distance four, apart from its separate block alternative. -/
theorem reducedSource_block_or_forward_index_eq_two_of_distance_four
    (r : CharacteristicReduction (L.subgroupOf J) (d.B.subgroupOf J))
    (hb : ((originalSource d hm).reduce r).geometry.b r.radical=4)
    {e : Vertex r.radical}
    (p : CriticalPath r.radical ((originalSource d hm).reduce r).geometry (alpha r.radical) e) :
    IsAlternatingBlock L 6 ∨
      (B r.radical (alpha r.radical) (((originalSource d hm).reduce r).geometry.Z_normal _)).relIndex
        (U r.radical (p.walk.getVert 2))=2 := by
  rcases reducedSource_block_or_full_point_image d hm r with hblock|hfull
  · exact Or.inl hblock
  · right
    let s := (originalSource d hm).reduce r
    have hf : r.radical.map s.projection=Model.E.map (MulAut.conj d.relabeler.val⁻¹).toMonoidHom := by
      simpa only [Model.pointCore_eq_exceptional] using hfull
    exact s.forward_moving_index_eq_two_of_distance_four (reduced_nativeCentralLayer d hm r) _ hf hb p
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
