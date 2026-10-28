module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SmallKernelNormalization
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SmallKernelObstruction

/-!
# The full-kernel failure line on the actual backward selector

The completed image-eight selector retains its transporter, generating edge,
strict slice and overlapping critical path. The terminal obstruction makes
that backward image large unless the original endpoint fails to normalize
its full-kernel join. The full-kernel reduction then constructs a nonzero
line in the three literal seeds and full omega central generation everywhere.

Source: MS93 (5.7)--(5.8), (5.12)(1)--(3), printed pp.919--920,924--927.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

include e hz hn in
/-- The completed source selector either has a large backward critical image,
or the full omega layer at every component vertex is centrally generated.
The same original transporter, both kernels and strict slice are retained. -/
theorem eight_strict_backward_large_or_central_generation_knownSimple
    (hne : ¬ IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8)
    (hb : replacementDistance h d = 4)
    {z delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4)
    (hdelta : Adjacent d.radical delta (p.walk.getVert 1))
    (hstrict : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical delta)) :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      ∃ g ∈ stabilizer d.radical (alpha d.radical),
        act d.radical g (p.walk.getVert 1) = t ∧
        Adjacent d.radical (act d.radical g delta) t ∧
        Q d.radical t ⊔ Z d.radical z = stabilizer d.radical (alpha d.radical) ∧
        2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical (act d.radical g delta)) ∧
        ∃ q : CriticalPath d.radical (replacementGeometry h d)
            (act d.radical g delta) (p.walk.getVert 2),
          q.walk.getVert 1 = t ∧ q.walk.getVert 2 = alpha d.radical ∧
          q.walk.getVert 3 = p.walk.getVert 1 ∧
          (4 ≤ (Q d.radical (p.walk.getVert 2)).relIndex (Z d.radical (act d.radical g delta)) ∨
            (∀ v : Vertex d.radical, color d.radical v = false →
              X d.radical v = U d.radical v ⊔
                (X d.radical v ⊓ centralizer (stabilizer d.radical v : Set (FreeAmalgam d.radical))))) := by
  obtain ⟨t,hat,g,hg,hgt,hct,hgen,hi,q,hq1,hq2,hq3,hout⟩ :=
    eight_strict_backward_kernel_obstruction_knownSimple
      (e := e) (hz := hz) (hn := hn) hne hcard hb p hsmall hdelta hstrict
  refine ⟨t,hat,g,hg,hgt,hct,hgen,hi,q,hq1,hq2,hq3,?_⟩
  rcases hout with hlarge | hbad
  · exact Or.inl hlarge
  right
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hnear : (cosetGraph d.radical).dist (act d.radical g delta) (alpha d.radical) ≤ 2 := by
    rw [←hq2,q.dist_start (by have hl : q.walk.length = 4 := q.length_eq_b.trans hb; omega)]
  exact (small_backward_kernel_normalized_or_centrally_generated s hc hb p hsmall
    q.start_color hnear).resolve_left hbad


include e hz hn in
/-- The actual image-eight selector either has a large backward critical image,
or constructs a nonzero line in the three full seeds. This retains the exact
transporter, generating edge and strict slice used by the terminal consumer. -/
theorem eight_strict_backward_large_or_three_seed_line_knownSimple
    (hne : ¬ IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8)
    (hb : replacementDistance h d = 4)
    {z delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4)
    (hdelta : Adjacent d.radical delta (p.walk.getVert 1))
    (hstrict : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical delta)) :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      ∃ g ∈ stabilizer d.radical (alpha d.radical),
        act d.radical g (p.walk.getVert 1) = t ∧
        Adjacent d.radical (act d.radical g delta) t ∧
        Q d.radical t ⊔ Z d.radical z = stabilizer d.radical (alpha d.radical) ∧
        2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical (act d.radical g delta)) ∧
        ∃ q : CriticalPath d.radical (replacementGeometry h d)
            (act d.radical g delta) (p.walk.getVert 2),
          q.walk.getVert 1 = t ∧ q.walk.getVert 2 = alpha d.radical ∧
          q.walk.getVert 3 = p.walk.getVert 1 ∧
          (4 ≤ (Q d.radical (p.walk.getVert 2)).relIndex (Z d.radical (act d.radical g delta)) ∨
            (∀ v : Vertex d.radical, color d.radical v = false →
              X d.radical v = U d.radical v ⊔
                (X d.radical v ⊓ centralizer (stabilizer d.radical v : Set (FreeAmalgam d.radical)))) ∧
            let H := ⁅Z d.radical (act d.radical g delta) ⊓ Q d.radical (p.walk.getVert 2),
              Z d.radical z ⊓ Q d.radical (alpha d.radical)⁆
            Nat.card H = 2 ∧
              H ≤ Z d.radical (act d.radical g delta) ⊓
                Z d.radical (p.walk.getVert 2) ⊓ Z d.radical z) := by
  obtain ⟨t,hat,g,hg,hgt,hct,hgen,hi,q,hq1,hq2,hq3,hout⟩ :=
    eight_strict_backward_kernel_obstruction_knownSimple
      (e := e) (hz := hz) (hn := hn) hne hcard hb p hsmall hdelta hstrict
  refine ⟨t,hat,g,hg,hgt,hct,hgen,hi,q,hq1,hq2,hq3,?_⟩
  rcases hout with hlarge | hbad
  · exact Or.inl hlarge
  right
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hnear : (cosetGraph d.radical).dist (act d.radical g delta) (alpha d.radical) ≤ 2 := by
    rw [←hq2,q.dist_start (by have hl : q.walk.length = 4 := q.length_eq_b.trans hb; omega)]
  exact small_backward_kernel_nonnormal_three_seed_line s hc hb p hsmall
    q.start_color hnear hbad


end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

