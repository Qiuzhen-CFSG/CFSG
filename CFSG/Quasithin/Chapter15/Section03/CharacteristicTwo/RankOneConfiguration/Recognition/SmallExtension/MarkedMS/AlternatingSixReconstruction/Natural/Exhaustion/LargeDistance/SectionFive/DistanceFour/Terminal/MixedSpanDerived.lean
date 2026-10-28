module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedSpanCenter
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedGeneratedLine

/-!
# The derived subgroup of a mixed selected span

The selected backward seed has the same full orbit span as the original
midpoint seed. Its commutator with the starting radius is the critical line,
which is fixed by the whole starting stabilizer. Conjugate generation then
identifies the span's entire derived subgroup with this line, of order two.

For a strict mixed slice, this supplies the nonabelianness, derived fixation
and index premises of the selected natural terminal consumer. The endpoint
commutator and the two opposite residual-core estimates remain explicit;
this module does not establish the unconditional mixed exclusion.
Both moving covers, all central attachments and the original graph are retained.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), the selected-span argument in (5.12), printed pp.925--927.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise IsMulCommutative
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

/-- The selected span's entire derived subgroup is the one critical line;
that line is fixed by the full starting stabilizer. -/
theorem mixed_selected_span_derived_data_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (q : MixedBackwardShift (h := h) p) :
    let P := localZSpan d.radical (p.walk.getVert 2) a
    let H := ⁅Z d.radical q.start,Z d.radical (p.walk.getVert 2)⁆
    ⁅P,P⁆ = H ∧ Nat.card (⁅P,P⁆ : Subgroup (FreeAmalgam d.radical)) = 2 ∧
      ⁅P,P⁆ ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
  let P := localZSpan d.radical (p.walk.getVert 2) a
  let H := ⁅Z d.radical q.start,Z d.radical (p.walk.getVert 2)⁆
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hq2 : q.path.walk.getVert 2 = a := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using q.overlap 0 (Nat.zero_le _)
  have hPV : P ≤ V d.radical a := localZSpan_le_V d.radical
    (by rw [SimpleGraph.dist_comm,p.dist_start (by omega)])
  have hPG : P ≤ stabilizer d.radical a :=
    hPV.trans ((V_le_Q d.radical p.start_color hb2).trans (fun _ hx => hx.1))
  have hZcP : Z d.radical q.start ≤ P := by
    rw [show P=localZSpan d.radical (p.walk.getVert 2) a from rfl,←q.span_eq hb]
    exact Z_le_localZSpan d.radical _ _
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hR : d.radical.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom := by
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s,him]
    exact map_mono plus_le_D
  have hHC : H ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
    have hh := cube_generated_four_critical_line_central s hc hb u hR q.path (q.interior_generation hb2)
    simpa only [hl,hq2] using hh
  have hHN : stabilizer d.radical a ≤ normalizer (H : Set (FreeAmalgam d.radical)) :=
    (le_centralizer_iff.mp hHC).trans (Subgroup.centralizer_le_normalizer _)
  have hline : ⁅Z d.radical q.start,V d.radical a⁆ = H := by
    have hh := (mixed_midpoint_radius_data_knownSimple hb u him q.path).2.2.1
    simpa only [hl,hq2] using hh
  have hPVline : ⁅P,V d.radical a⁆ ≤ H := by
    change ⁅localZSpan d.radical (p.walk.getVert 2) a,V d.radical a⁆ ≤ H
    rw [←q.span_eq hb,localZSpan_eq_conjugates]
    apply commutator_iSup_le_of_relative_normal (stabilizer d.radical a)
      (V d.radical a) H _ hHN
    · intro g
      exact ((map_mono hZcP).trans_eq (mem_normalizer_iff_map_conj_eq.mp
        (localZSpan_normalized d.radical (p.walk.getVert 2) a
          ((stabilizer d.radical a).inv_mem g.property)))).trans hPG
    · intro g
      have hVmap : (V d.radical a).map (MulAut.conj (g : FreeAmalgam d.radical)⁻¹).toMonoidHom =
          V d.radical a := mem_normalizer_iff_map_conj_eq.mp
        (DistanceEight.V_normalized d.radical a ((stabilizer d.radical a).inv_mem g.property))
      have hHmap : H.map (MulAut.conj (g : FreeAmalgam d.radical)⁻¹).toMonoidHom = H :=
        mem_normalizer_iff_map_conj_eq.mp (hHN ((stabilizer d.radical a).inv_mem g.property))
      have hh := congrArg (Subgroup.map (MulAut.conj (g : FreeAmalgam d.radical)⁻¹).toMonoidHom) hline
      rw [map_commutator,hVmap,hHmap] at hh
      exact hh.le
  have he : ⁅P,P⁆ = H := le_antisymm
    ((commutator_mono le_rfl hPV).trans hPVline)
    (commutator_mono hZcP (Z_le_localZSpan d.radical _ _))
  refine ⟨he,?_,he.le.trans hHC⟩
  rw [he]
  have hh := small_critical_commutator_card s hc q.path
    (critical_image_small_at_knownSimple (e := e) (hz := hz) (hn := hn) hb q.path)
  simpa only [hl] using hh

/-- A strict mixed forward slice supplies the derived fixation and exact
order required by the selected natural-span terminal interface. -/
theorem mixed_strict_selected_span_derived_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2))) :
    let P := localZSpan d.radical (p.walk.getVert 2) a
    Nat.card (⁅P,P⁆ : Subgroup (FreeAmalgam d.radical)) = 2 ∧
      ⁅P,P⁆ ≤ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) := by
  obtain ⟨q⟩ := mixed_strict_backward_shift_at_knownSimple hb u him p hstrict
  have hh := mixed_selected_span_derived_data_knownSimple hb u him p q
  exact ⟨hh.2.1,hh.2.2.trans (centralizer_le (Ltilde_le_stabilizer _))⟩

/-- The mixed strict branch discharges nonabelianness, small critical image,
derived fixation and the selected index in the literal terminal consumer.
The endpoint commutator and the opposite residual-core estimates remain. -/
theorem mixed_strict_terminal_false_of_remaining_estimates_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hstrict : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)))
    (hcomm : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) ⊓
      Q d.radical (p.walk.getVert 2),Z d.radical z⁆ ≤ Z d.radical (alpha d.radical))
    (hCcard : Nat.card (⁅⁅Q d.radical (p.walk.getVert 2),Ltilde d.radical (p.walk.getVert 2)⁆,
      ⁅Q d.radical (p.walk.getVert 2),Ltilde d.radical (p.walk.getVert 2)⁆⁆ :
        Subgroup (FreeAmalgam d.radical)) ≤ 2)
    (hcross : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) ⊓
      Q d.radical (p.walk.getVert 2),
      ⁅Q d.radical (p.walk.getVert 2),Ltilde d.radical (p.walk.getVert 2)⁆⁆ ≤
      ⁅⁅Q d.radical (p.walk.getVert 2),Ltilde d.radical (p.walk.getVert 2)⁆,
        ⁅Q d.radical (p.walk.getVert 2),Ltilde d.radical (p.walk.getVert 2)⁆⁆) : False := by
  have hb2 : 2 < replacementDistance h d := by omega
  obtain ⟨q⟩ := mixed_strict_backward_shift_knownSimple hb u him p hstrict
  have hd := mixed_selected_span_derived_data_knownSimple hb u him p q
  have hnon : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥ := by
    intro he
    have hi := hd.2.1
    rw [he,card_bot] at hi
    omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hq2 : q.path.walk.getVert 2 = alpha d.radical := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using q.overlap 0 (Nat.zero_le _)
  have hradius := mixed_four_backward_radius_index_knownSimple hb u him p q.path hq2
  rw [hl] at hradius
  have hPV : localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) ≤
      V d.radical (alpha d.radical) := localZSpan_le_V d.radical
    (by rw [SimpleGraph.dist_comm,p.dist_start (by omega)])
  let := finite_stabilizer d.radical (alpha d.radical)
  let : Finite (V d.radical (alpha d.radical)) := Finite.of_injective
    (inclusion ((V_le_Q d.radical rfl hb2).trans (fun _ hx => hx.1))) (inclusion_injective _)
  have hindex : (Q d.radical (p.walk.getVert 2)).relIndex
      (localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)) ≤ 2 :=
    (relIndex_le_of_le_right hPV index_ne_zero_of_finite).trans_eq hradius
  exact selected_natural_terminal_false_knownSimple (e := e) (hz := hz) (hn := hn) hb2 p hnon
    (critical_image_small_at_knownSimple (e := e) (hz := hz) (hn := hn) hb p)
    (hd.2.2.trans (centralizer_le (Ltilde_le_stabilizer _))) hindex hcomm hCcard hcross

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
