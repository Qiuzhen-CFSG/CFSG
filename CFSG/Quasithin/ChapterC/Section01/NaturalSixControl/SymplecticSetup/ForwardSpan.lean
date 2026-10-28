module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.ForwardFixedLine
public import Theory.GroupTheory.Commutator.RelativeGeneration
/-!
# The normal forward span has a fixed commutator line

The forward hyperplane-kernel line centralizes the starting stabilizer: it
is fixed by the component and lies in the common edge seed. Normal generation
therefore preserves the same commutator bound for the full starting-stabilizer
span of the forward Z-layer. Conjugation supplies the span V and kernel T2 in
the second paragraph of MS93 (5.9), printed pp.920--921.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)

theorem critical_forward_span_commutator_le_line
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection = Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : 4 < s.geometry.b R) {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e)
    (hindex : (B R (alpha R) (s.geometry.Z_normal _)).relIndex
      (U R (p.walk.getVert 2)) ≤ 2) :
    let T₀ := Q R (alpha R) ⊓ centralizer
      (U R (p.walk.getVert 2) ⊓ B R (alpha R) (s.geometry.Z_normal _) : Set (FreeAmalgam R))
    let H := ⁅U R (p.walk.getVert 2),T₀⁆
    H ≤ centralizer (stabilizer R (alpha R) : Set (FreeAmalgam R)) ∧
      ⁅localZSpan R (p.walk.getVert 2) (alpha R),T₀⁆ ≤ H := by
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  let T₀ := Q R (alpha R) ⊓ centralizer
    (U R c ⊓ B R (alpha R) (s.geometry.Z_normal _) : Set (FreeAmalgam R))
  let H := ⁅U R c,T₀⁆
  change H ≤ centralizer (stabilizer R (alpha R) : Set (FreeAmalgam R)) ∧
    ⁅localZSpan R c (alpha R),T₀⁆ ≤ H
  have hb2 : 2 < s.geometry.b R := by omega
  have hl := p.length_eq_b
  have hc : color R c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent R (alpha R) t := by
    apply (cosetGraph_adj R _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i:=0) (by omega)
  have hct : Adjacent R c t := adjacent_symm R ((cosetGraph_adj R _ _).mp
    (p.walk.adj_getVert_succ (i:=1) (by omega)))
  have ht : color R t ≠ false := Ne.symm (adjacent_color_ne R hat)
  have hTQt : T₀ ≤ Q R t := inf_le_left.trans (Q_le_adjacent_h R (by cases hh:color R t <;> simp_all) hat)
  have hseed : Z R t ≤ centralizer (Q R t : Set (FreeAmalgam R)) := by
    intro z hz
    rw [Z,if_neg ht] at hz
    exact (mem_omegaCenter_iff.mp hz).2.2
  have hHZ := (s.moving_hyperplane_commutator_le_seed h u hfull rfl hc hat hct hindex).2
  have hHD := s.critical_forward_commutator_le_fixedCore h u hfull hb p hindex
  have hHC : H ≤ centralizer (stabilizer R (alpha R) : Set (FreeAmalgam R)) := by
    apply le_centralizer_iff.mp
    rw [←s.residual_edge_generation rfl hat]
    apply sup_le
    · exact le_centralizer_iff.mp (hHD.trans inf_le_right)
    · exact le_centralizer_iff.mp (hHZ.trans hseed)
  have hHN : stabilizer R (alpha R) ≤ normalizer (H : Set (FreeAmalgam R)) :=
    (le_centralizer_iff.mp hHC).trans (Subgroup.centralizer_le_normalizer _)
  have hTN : stabilizer R (alpha R) ≤ normalizer (T₀ : Set (FreeAmalgam R)) :=
    s.moving_hyperplane_kernel_normalized hb2 rfl hat hct
  have hZcG : Z R c ≤ stabilizer R (alpha R) :=
    ((Z_le_localZSpan R c (alpha R)).trans (localZSpan_le_V R (by
      rw [SimpleGraph.dist_comm,p.dist_start (by omega)]))).trans
      (s.geometry.V_local (alpha R) rfl hb2)
  have hZcT : ⁅Z R c,T₀⁆ ≤ H := by
    rw [s.Z_eq_moving_sup_edge_at h hc hct]
    apply commutator_sup_le_of_relative_normal (stabilizer R (alpha R))
      (U R c) (Z R t) T₀ H hHN
      ((DistanceEight.U_le_Z R c).trans hZcG)
      ((adjacent_Z_le R rfl hat).trans (Z_le_stabilizer R (alpha R))) le_rfl
    exact (commutator_eq_bot_iff_le_centralizer.mpr (hseed.trans (centralizer_le hTQt))).le.trans bot_le
  refine ⟨hHC,?_⟩
  rw [localZSpan_eq_conjugates]
  apply commutator_iSup_le_of_relative_normal (stabilizer R (alpha R)) T₀ H _ hHN
  · intro g
    have hgmap : (stabilizer R (alpha R)).map
        (MulAut.conj (g:FreeAmalgam R)⁻¹).toMonoidHom = stabilizer R (alpha R) :=
      mem_normalizer_iff_map_conj_eq.mp ((stabilizer R (alpha R)).le_normalizer
        ((stabilizer R (alpha R)).inv_mem g.property))
    exact (map_mono hZcG).trans_eq hgmap
  · intro g
    have hm := map_mono (f:=(MulAut.conj (g:FreeAmalgam R)⁻¹).toMonoidHom) hZcT
    have hTm : T₀.map (MulAut.conj (g:FreeAmalgam R)⁻¹).toMonoidHom = T₀ :=
      mem_normalizer_iff_map_conj_eq.mp (hTN ((stabilizer R (alpha R)).inv_mem g.property))
    have hHm : H.map (MulAut.conj (g:FreeAmalgam R)⁻¹).toMonoidHom = H :=
      mem_normalizer_iff_map_conj_eq.mp (hHN ((stabilizer R (alpha R)).inv_mem g.property))
    rwa [map_commutator,hTm,hHm] at hm
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
variable {K : Type*} [Group K] [Finite K]
  {L W : Subgroup K} [L.Normal] [W.Normal] {T : Sylow 2 K}
  (d : NaturalSixControl.SourceData L W T) (hm : IntrinsicMSPair d)
local notation "J" => (L ⊔ d.B : Subgroup K)
local notation "R" => d.B.subgroupOf J

theorem reducedSource_block_or_forward_span
    (r : CharacteristicReduction (L.subgroupOf J) R) {e : Vertex r.radical}
    (p : CriticalPath r.radical ((originalSource d hm).reduce r).geometry (alpha r.radical) e)
    (hb : 4 < ((originalSource d hm).reduce r).geometry.b r.radical)
    (hindex : (B r.radical (alpha r.radical) (((originalSource d hm).reduce r).geometry.Z_normal _)).relIndex
      (U r.radical (p.walk.getVert 2)) ≤ 2) :
    IsAlternatingBlock L 6 ∨
      (let T₀ := Q r.radical (alpha r.radical) ⊓ centralizer
         (U r.radical (p.walk.getVert 2) ⊓ B r.radical (alpha r.radical)
           (((originalSource d hm).reduce r).geometry.Z_normal _) : Set (FreeAmalgam r.radical))
       let H := ⁅U r.radical (p.walk.getVert 2),T₀⁆
       H ≤ centralizer (stabilizer r.radical (alpha r.radical) : Set (FreeAmalgam r.radical)) ∧
         ⁅localZSpan r.radical (p.walk.getVert 2) (alpha r.radical),T₀⁆ ≤ H) := by
  rcases reducedSource_block_or_full_point_image d hm r with hblock | hfull
  · exact Or.inl hblock
  · right
    let s := (originalSource d hm).reduce r
    have h := reduced_nativeCentralLayer d hm r
    have hf : r.radical.map s.projection = Model.E.map (MulAut.conj d.relabeler.val⁻¹).toMonoidHom := by
      simpa only [Model.pointCore_eq_exceptional] using hfull
    exact s.critical_forward_span_commutator_le_line h _ hf hb p hindex
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
