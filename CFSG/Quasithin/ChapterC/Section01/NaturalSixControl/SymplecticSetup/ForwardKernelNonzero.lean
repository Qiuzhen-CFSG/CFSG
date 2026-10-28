module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.ForwardClosure
/-!
# The forward-kernel commutator is nonzero

In the index-two contrary case of MS93 (5.9), put c = p[2] and
T₀ = Qα ∩ C(Uc ∩ Bα). If [Uc,T₀] vanished, the edge-seed decomposition
would make Zc centralize T₀. Since Gα normalizes T₀, the whole local span
of Zc would centralize it. The inner-layer containment and critical
commutator bound then put this normal span in Bα, contradicting the
prescribed index two of Uc.

This supplies the implicit nonvanishing needed before the second line
choice on printed p.920. It uses the literal path and forward kernel,
with no additional local action assumption.

Source: Meierfrankenfeld--Stellmacher (1993), proof of (5.9), printed p.920.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)

/-- The forward kernel moves the actual second-vertex natural layer nontrivially
in the index-two contrary case of source (5.9). -/
theorem critical_forward_kernel_commutator_ne_bot (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : 4<s.geometry.b R) {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e)
    (hindex : (B R (alpha R) (s.geometry.Z_normal _)).relIndex (U R (p.walk.getVert 2))=2) :
    let T₀ := Q R (alpha R) ⊓ centralizer
      (U R (p.walk.getVert 2) ⊓ B R (alpha R) (s.geometry.Z_normal _) : Set (FreeAmalgam R))
    ⁅U R (p.walk.getVert 2),T₀⁆≠⊥ := by
  let T₀ := Q R (alpha R) ⊓ centralizer
    (U R (p.walk.getVert 2) ⊓ B R (alpha R) (s.geometry.Z_normal _) : Set (FreeAmalgam R))
  change ⁅U R (p.walk.getVert 2),T₀⁆≠⊥
  intro hzero
  have hl := p.length_eq_b
  have hb2 : 2<s.geometry.b R := by omega
  have hc : color R (p.walk.getVert 2)=false :=
    (p.vertex_color (by omega : 2≤p.walk.length)).mpr (by decide)
  have hat : Adjacent R (alpha R) (p.walk.getVert 1) := by
    have hh := p.walk.adj_getVert_succ (i:=0) (by omega)
    simpa only [SimpleGraph.Walk.getVert_zero,Nat.zero_add] using (cosetGraph_adj R _ _).mp hh
  have hct : Adjacent R (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm R ((cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ (i:=1) (by omega)))
  have ht : color R (p.walk.getVert 1)=true := by
    have hh := adjacent_color_ne R hat
    change false≠color R (p.walk.getVert 1) at hh
    cases he : color R (p.walk.getVert 1) <;> simp_all
  have hTQ : T₀≤Q R (alpha R) := inf_le_left
  have hTN : stabilizer R (alpha R)≤normalizer (T₀:Set (FreeAmalgam R)) :=
    s.moving_hyperplane_kernel_normalized hb2 rfl hat hct
  have hTQt : T₀≤Q R (p.walk.getVert 1) := hTQ.trans (Q_le_adjacent_h R ht hat)
  have hseed : Z R (p.walk.getVert 1)≤centralizer (Q R (p.walk.getVert 1):Set (FreeAmalgam R)) := by
    intro z hz
    rw [Z,if_neg (by simp [ht])] at hz
    exact (mem_omegaCenter_iff.mp hz).2.2
  have hZc : Z R (p.walk.getVert 2)≤centralizer (T₀:Set (FreeAmalgam R)) := by
    rw [s.Z_eq_moving_sup_edge_at h hc hct]
    exact sup_le (commutator_eq_bot_iff_le_centralizer.mp hzero)
      (hseed.trans (centralizer_le hTQt))
  let D := localZSpan R (p.walk.getVert 2) (alpha R)
  have hDC : D≤centralizer (T₀:Set (FreeAmalgam R)) := by
    have hNC : stabilizer R (alpha R)≤normalizer
        (centralizer (T₀:Set (FreeAmalgam R)):Set (FreeAmalgam R)) :=
      hTN.trans (le_normalizer_of_normal_subgroupOf (Subgroup.centralizer_le_normalizer _))
    dsimp only [D]
    rw [localZSpan_eq_conjugates]
    apply iSup_le
    intro g
    rintro _ ⟨z,hz,rfl⟩
    exact (mem_normalizer_iff.mp (hNC ((stabilizer R (alpha R)).inv_mem g.property)) z).mp (hZc hz)
  have hDV : D≤V R (alpha R) := localZSpan_le_V R (by
    rw [SimpleGraph.dist_comm,p.dist_start (by omega : 2≤p.walk.length)])
  have hinner := s.critical_forward_kernel_contains_inner_layers hb p
  have hDfix := hDC.trans (centralizer_le hinner)
  have hcomm : ⁅D,Z R e⁆≤Z R (alpha R) :=
    s.critical_commutator_le_start_of_predecessor_fixed h u hfull hb2 p D hDV
    (hDfix.trans (centralizer_le (show Z R (p.walk.getVert (p.walk.length-2)) ≤
      Z R (p.walk.getVert (p.walk.length-2)) ⊔ (Z R e ⊓ Q R (alpha R)) from le_sup_left)))
    (hDfix.trans (centralizer_le (show (Z R e ⊓ Q R (alpha R):Subgroup (FreeAmalgam R)) ≤
      Z R (p.walk.getVert (p.walk.length-2)) ⊔ (Z R e ⊓ Q R (alpha R)) from le_sup_right)))
  have hDB := s.normalized_radius_le_B_of_critical_commutator u hfull hb2 p D hDV
    (localZSpan_normalized R _ _) hcomm
  have hUB : U R (p.walk.getVert 2)≤B R (alpha R) (s.geometry.Z_normal _) :=
    (DistanceEight.U_le_Z R _).trans ((Z_le_localZSpan R _ _).trans hDB)
  have hi := relIndex_eq_one.mpr hUB
  omega

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
variable {K : Type*} [Group K] [Finite K] {L W : Subgroup K} [L.Normal] [W.Normal]
  {T : Sylow 2 K} (d : NaturalSixControl.SourceData L W T)

/-- The nonzero forward-kernel input on the literal characteristic replacement. -/
theorem reducedSource_block_or_forward_kernel_nonzero (hm : IntrinsicMSPair d)
    (r : CharacteristicReduction (L.subgroupOf (L⊔d.B)) (d.B.subgroupOf (L⊔d.B)))
    {e : Vertex r.radical}
    (p : CriticalPath r.radical ((originalSource d hm).reduce r).geometry (alpha r.radical) e)
    (hb : 4<((originalSource d hm).reduce r).geometry.b r.radical)
    (hindex : (B r.radical (alpha r.radical)
      (((originalSource d hm).reduce r).geometry.Z_normal _)).relIndex
        (U r.radical (p.walk.getVert 2))=2) :
    IsAlternatingBlock L 6 ∨
      (let T₀ := Q r.radical (alpha r.radical) ⊓ centralizer
        (U r.radical (p.walk.getVert 2) ⊓ B r.radical (alpha r.radical)
          (((originalSource d hm).reduce r).geometry.Z_normal _) : Set (FreeAmalgam r.radical))
       ⁅U r.radical (p.walk.getVert 2),T₀⁆≠⊥) := by
  rcases reducedSource_block_or_full_point_image d hm r with hblock|hfull
  · exact Or.inl hblock
  · apply Or.inr
    exact Source.critical_forward_kernel_commutator_ne_bot ((originalSource d hm).reduce r)
      (reduced_nativeCentralLayer d hm r) d.relabeler.val⁻¹
      (by simpa only [Model.pointCore_eq_exceptional] using hfull) hb p hindex

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
