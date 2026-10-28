module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.ControlledBackward
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeLargeShift

/-!
# Large images and compatible backward paths in the nonsylow branch

At distance four a large critical image excludes the point-core radical
image. The actual nonsylow image classification therefore supplies the
three-pair radical image. The controlled backward selector preserves its
transporter, generating edge, overlapping vertices and Baumann slice index.
The strict forward slice forces the selected backward image to be large.
Quadratic three-pair action then fixes the whole backward critical commutator
at the old starting stabilizer; that commutator is noncentral at its own
start, where the selected span is nonabelian.

This is a same-path reduction of the large-image branch of MS93 (5.12)(2),
not its exclusion. In particular, the two-successive-shifts exclusion above
distance four is not applied at distance four: its final distance inequality
is strict and is unavailable here. The source kernel-normality and chosen
full-seed-slice arguments remain in the terminal assembly.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (5.2), (5.8), and (5.12), printed pp.913--915,919--920,924--927.
All vertices are on the literal natural replacement, with both moving
covers and the full central attachments retained.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

include e hz hn in
/-- The same selected backward path has a large critical image and strict
slice, with its full commutator fixed at the old base and noncentral at its
new start. The three-pair radical hypothesis is constructed internally. -/
theorem nonsylow_large_image_backward_knownSimple
    (hb : replacementDistance h d = 4)
    (hns : ¬ ∃ P : Sylow 2 (L ⊔ R : Subgroup G),
      (P : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical))) :
    ∃ c t x, x ∈ stabilizer d.radical (alpha d.radical) ∧
      act d.radical x (p.walk.getVert 2) = c ∧
      Adjacent d.radical (alpha d.radical) t ∧ Adjacent d.radical c t ∧
      Q d.radical t ⊔ Z d.radical a' = stabilizer d.radical (alpha d.radical) ∧
      ∃ q : CriticalPath d.radical (replacementGeometry h d) c (p.walk.getVert 2),
        q.walk.getVert 1 = t ∧ q.walk.getVert 2 = alpha d.radical ∧
        q.walk.getVert 3 = p.walk.getVert 1 ∧
        4 ≤ (Q d.radical (p.walk.getVert 2)).relIndex (Z d.radical c) ∧
        (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical c) =
        (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical (p.walk.getVert 2)) ∧
        2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical c) ∧
        ⁅Z d.radical c,Z d.radical (p.walk.getVert 2)⁆ ≤
          centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) ∧
        (¬ ⁅Z d.radical c,Z d.radical (p.walk.getVert 2)⁆ ≤
          centralizer (stabilizer d.radical c : Set (FreeAmalgam d.radical))) ∧
        ⁅localZSpan d.radical (alpha d.radical) c,
          localZSpan d.radical (alpha d.radical) c⁆ ≠ ⊥ := by
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hdelta : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hstrict := large_image_forward_slice_gt_two_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hlarge
  have hel : ¬ U d.radical (p.walk.getVert 2) ≤
      B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) := by
    intro hh
    have he := relIndex_eq_one.mpr hh
    omega
  obtain ⟨t,hat,hgen,x,hx,hxt,q,hq1,hover,hsmall⟩ :=
    nonsylow_large_image_backward_shift_knownSimple
      (e := e) (hz := hz) (hn := hn) hb2 hns p hlarge hdelta hel
  have hct : Adjacent d.radical (act d.radical x (p.walk.getVert 2)) t := by
    rw [←hxt]
    exact (adjacent_act_iff d.radical x _ _).mpr hdelta
  have hlargeq : 4 ≤ (Q d.radical (p.walk.getVert (p.walk.length-2))).relIndex
      (Z d.radical (act d.radical x (p.walk.getVert 2))) := by
    by_contra! hbad
    have he := hsmall hbad
    omega
  have hq2 : q.walk.getVert 2 = alpha d.radical := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (by omega)
  have hq3 : q.walk.getVert 3 = p.walk.getVert 1 := hover 1 (by omega)
  have hB : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map
      (MulAut.conj x⁻¹).toMonoidHom = B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      hb2 (alpha d.radical) rfl ((stabilizer d.radical (alpha d.radical)).inv_mem hx))
  have hidx : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (act d.radical x (p.walk.getVert 2))) =
      (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (p.walk.getVert 2)) := by
    rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective,hB]
  have hcube : ∃ u, d.radical.map s.projection = (CFSG.Quasithin.ChapterB.Offenders.D 6).map (MulAut.conj u).toMonoidHom := by
    rcases nonsylow_radical_image_maximal_knownSimple
      (e := e) (hz := hz) (hn := hn) hb2 hns with ⟨u,hu⟩ | ⟨u,hu⟩
    · exact (large_critical_image_four_false_knownSimple hb u hu p hlarge).elim
    · exact ⟨u,by rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]⟩
  obtain ⟨u,hu⟩ := hcube
  let shift : BackwardShift (h := h) p := {
    start := act d.radical x (p.walk.getVert 2)
    edge := t
    transporter := x
    transporter_mem := hx
    start_eq := rfl
    adjacent_start := hat
    adjacent_shift := hct
    generation := hgen
    path := q
    first := hq1
    overlap := hover }
  have hcentral := cube_backward_commutator_central s hc hb2 u hu.le p shift
  have hnoncentral := critical_commutator_not_central s hc q
  have hnon := large_image_selected_span_nonabelian s hc hb q hlargeq
  rw [hq2] at hnon
  have he : p.walk.length-2 = 2 := by omega
  have hout : ∃ q' : CriticalPath d.radical (replacementGeometry h d)
      (act d.radical x (p.walk.getVert 2)) (p.walk.getVert (p.walk.length-2)),
      q'.walk.getVert 1 = t ∧ q'.walk.getVert 2 = alpha d.radical ∧
      q'.walk.getVert 3 = p.walk.getVert 1 := ⟨q,hq1,hq2,hq3⟩
  rw [he] at hout hlargeq hnoncentral
  change ⁅Z d.radical (act d.radical x (p.walk.getVert 2)),
    Z d.radical (p.walk.getVert (p.walk.length-2))⁆ ≤ _ at hcentral
  rw [he] at hcentral
  obtain ⟨q',hq1',hq2',hq3'⟩ := hout
  refine ⟨_,t,x,hx,rfl,hat,hct,hgen,q',hq1',hq2',hq3',hlargeq,hidx,?_,hcentral,
    hnoncentral,hnon⟩
  rwa [hidx]

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
