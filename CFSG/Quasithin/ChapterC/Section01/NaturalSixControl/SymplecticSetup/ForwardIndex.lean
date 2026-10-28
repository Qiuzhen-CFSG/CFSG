module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.CommonKernelLine
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.PointLineChoice
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.ShiftedForwardConfiguration
/-!
# The strict forward Baumann index in the native symplectic source

Assume the forward moving layer has Baumann index two. Its hyperplane-kernel
commutator is a nonzero line. Choose a shifted critical endpoint and one
conjugator placing that line in a generating edge. The same-choice source
configuration puts the centralizer span of the shifted starting Z-layer in
the old endpoint kernel. The common-kernel span exclusion contradicts this,
because forward critical nonnormality keeps the shifted Z-layer outside B.

This proves MS93 (5.9), printed pp.920--922, for the actual full point-core
image. The characteristic-replacement application is the source required
by Aschbacher--Smith C.1.37 and the original Baumann bound in 13.7.4(1).
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)

private theorem shifted_forward_seed_span_escape
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : 4<s.geometry.b R) {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e)
    (d : Vertex R) (_hd : color R d=false) (hed : (cosetGraph R).dist e d=2)
    (hcrit : CriticalPair R (p.walk.getVert 2) d
      (s.geometry.exists_critical _ ((p.vertex_color (by rw [p.length_eq_b]; omega)).mpr (by decide))))
    (t : Vertex R) (hct : Adjacent R (p.walk.getVert 2) t)
    (hgen : Q R t⊔Z R d=stabilizer R (p.walk.getVert 2))
    (H : Subgroup (FreeAmalgam R)) (hHseed : H≤Z R (p.walk.getVert 1)) (hHne : H≠⊥)
    (y : FreeAmalgam R) (hy : y∈stabilizer R (p.walk.getVert 2))
    (hline : H.map (MulAut.conj y).toMonoidHom=U R (p.walk.getVert 2)⊓Z R t) :
    ¬conjugateSpanBy (Z R (act R y⁻¹ (alpha R)))
        (stabilizer R (p.walk.getVert 2)⊓centralizer (H.map (MulAut.conj y).toMonoidHom:Set (FreeAmalgam R)))≤Q R e := by
  let c := p.walk.getVert 2
  let k := p.walk.getVert 1
  let mu := act R y⁻¹ (alpha R)
  let H₂ := H.map (MulAut.conj y).toMonoidHom
  have hl : 4<p.walk.length := p.length_eq_b ▸ hb
  have hc : color R c=false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent R (alpha R) k := by
    apply (cosetGraph_adj R _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i:=0) (by omega)
  have hck : Adjacent R c k := adjacent_symm R ((cosetGraph_adj R _ _).mp
    (p.walk.adj_getVert_succ (i:=1) (by omega)))
  obtain ⟨q,hq⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist e d
  have hql : q.length=2 := hq.trans hed
  let walk := (p.walk.drop 2).append q
  have hcd : (cosetGraph R).dist c d=s.geometry.b R :=
    hcrit.1.trans (s.geometry.distance_constant c hc)
  have hwlen : walk.length=p.walk.length := by
    dsimp only [walk]
    rw [SimpleGraph.Walk.length_append,SimpleGraph.Walk.drop_length,hql]
    omega
  let p' : CriticalPath R s.geometry c d := ⟨hc,walk,by rw [hwlen,p.length_eq_b,hcd],hcrit⟩
  have hpre : p'.walk.getVert (p'.walk.length-2)=e := by
    change walk.getVert (walk.length-2)=e
    rw [hwlen]
    dsimp only [walk]
    rw [SimpleGraph.Walk.getVert_append,SimpleGraph.Walk.drop_length,if_neg (by omega)]
    simp only [Nat.sub_self,SimpleGraph.Walk.getVert_zero]
  have hfix : act R y⁻¹ c=c := (stabilizer R c).inv_mem hy
  have hmu : color R mu=false := by simp only [mu,action_preserves_color]; rfl
  have hmuV : Z R mu≤V R c := by
    have hbase : Z R (alpha R)≤V R c := by
      apply le_iSup_of_le (alpha R)
      apply le_iSup_of_le (show (cosetGraph R).dist (alpha R) c≤2 from (p.dist_start (by omega)).le)
      exact le_rfl
    change Z R (act R y⁻¹ (alpha R))≤V R c
    rw [Z_act,inv_inv]
    exact (map_mono hbase).trans_eq (mem_normalizer_iff_map_conj_eq.mp (V_normalized c hy))
  have hmuB : ¬Z R mu≤B R c (s.geometry.Z_normal _) := by
    intro hbad
    have hBm : (B R c (s.geometry.Z_normal _)).map (MulAut.conj y).toMonoidHom=
        B R c (s.geometry.Z_normal _) :=
      mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized (by omega) c hc hy)
    change Z R (act R y⁻¹ (alpha R))≤_ at hbad
    rw [Z_act,inv_inv,←hBm] at hbad
    exact s.critical_start_not_le_forward_B (by omega) p
      ((map_le_map_iff_of_injective (MulAut.conj y).injective).mp hbad)
  have hH₂ne : H₂≠⊥ := by
    intro he
    apply hHne
    apply map_injective (f:=(MulAut.conj y).toMonoidHom) (MulAut.conj y).injective
    simpa only [Subgroup.map_bot] using he
  have hH₂k : H₂≤Z R (act R y⁻¹ k) := by
    rw [Z_act,inv_inv]
    exact map_mono hHseed
  have hactck : Adjacent R c (act R y⁻¹ k) := by
    simpa only [hfix] using (adjacent_act_iff R y⁻¹ c k).mpr hck
  have hh := s.critical_moving_line_span_not_le_predecessor h u hfull (by omega) hc p' t hct hgen
    mu (act R y⁻¹ k) hmu ((adjacent_act_iff R y⁻¹ (alpha R) k).mpr hat) hactck
    hmuV hmuB H₂ hline.le hH₂ne hH₂k
  rwa [hpre] at hh


/-- Native source (5.9): the forward moving layer has index strictly above two. -/
theorem forward_moving_index_two_lt
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : 4<s.geometry.b R) {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e) :
    2<(B R (alpha R) (s.geometry.Z_normal _)).relIndex (U R (p.walk.getVert 2)) := by
  by_contra hn
  have hlo := s.forward_moving_index_two_le h u hfull (by omega) p
  have hindex : (B R (alpha R) (s.geometry.Z_normal _)).relIndex (U R (p.walk.getVert 2))=2 := by omega
  let c := p.walk.getVert 2
  let k := p.walk.getVert 1
  let T₀ := Q R (alpha R)⊓centralizer (U R c⊓B R (alpha R) (s.geometry.Z_normal _):Set (FreeAmalgam R))
  let H := ⁅U R c,T₀⁆
  have hl : 4<p.walk.length := p.length_eq_b ▸ hb
  have hc : color R c=false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent R (alpha R) k := by
    apply (cosetGraph_adj R _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i:=0) (by omega)
  have hck : Adjacent R c k := adjacent_symm R ((cosetGraph_adj R _ _).mp
    (p.walk.adj_getVert_succ (i:=1) (by omega)))
  have hk : color R k=true := by
    have hh := adjacent_color_ne R hat
    change false≠color R k at hh
    cases he:color R k <;> simp_all
  have hTQk : T₀≤Q R k := inf_le_left.trans (Q_le_adjacent_h R hk hat)
  have hTGc : T₀≤stabilizer R c := hTQk.trans (fun _ hx => hx.2 _ (adjacent_symm R hck))
  have hHU : H≤U R c := le_normalizer_iff_commutator_le_left.mp (hTGc.trans (U_normalized c))
  have hHne : H≠⊥ := s.critical_forward_kernel_commutator_ne_bot h u hfull hb p hindex
  have hHline := s.moving_hyperplane_commutator_le_seed h u hfull rfl hc hat hck hindex.le
  obtain ⟨d,hd,hed,hcrit⟩ := s.exists_shifted_critical_endpoint h u hfull hb p
  obtain ⟨t,hct,hgen,y,hy,hline,hPgen,hmove⟩ :=
    s.exists_moving_line_edge_generator_at h u hfull hc hcrit H hHU hHne hHline.1
  have cfg := s.shifted_forward_configuration_of_choice h u hfull hb p hindex d hd hed hcrit y hy hPgen hmove
  rcases cfg with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,hspan,_⟩
  exact s.shifted_forward_seed_span_escape h u hfull hb p d hd hed hcrit t hct hgen
    H hHline.2 hHne y hy hline hspan

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
variable {K : Type*} [Group K] [Finite K]
  {L W : Subgroup K} [L.Normal] [W.Normal] {T : Sylow 2 K}
  (d : NaturalSixControl.SourceData L W T) (hm : IntrinsicMSPair d)
local notation "J" => (L⊔d.B : Subgroup K)
local notation "R" => d.B.subgroupOf J

/-- The original replacement has the strict forward index, or the block alternative. -/
theorem reducedSource_block_or_forward_index_two_lt
    (r : CharacteristicReduction (L.subgroupOf J) R) {e : Vertex r.radical}
    (p : CriticalPath r.radical ((originalSource d hm).reduce r).geometry (alpha r.radical) e)
    (hb : 4<((originalSource d hm).reduce r).geometry.b r.radical) :
    IsAlternatingBlock L 6 ∨
      2<(B r.radical (alpha r.radical) (((originalSource d hm).reduce r).geometry.Z_normal _)).relIndex
        (U r.radical (p.walk.getVert 2)) := by
  rcases reducedSource_block_or_full_point_image d hm r with hblock|hfull
  · exact Or.inl hblock
  · right
    let s := (originalSource d hm).reduce r
    have hf : r.radical.map s.projection=Model.E.map (MulAut.conj d.relabeler.val⁻¹).toMonoidHom := by
      simpa only [Model.pointCore_eq_exceptional] using hfull
    exact s.forward_moving_index_two_lt (reduced_nativeCentralLayer d hm r) _ hf hb p

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
