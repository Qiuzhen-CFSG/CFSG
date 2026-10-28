module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowUnequalKernel
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.ResidualSmallSection
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeFullKernel
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTrappedExclusion

/-!
# Normalizing the full trapped-kernel fixer

The aligned kernel line from SylowUnequalKernel bounds the fixed index of
F = Z_z intersect Q_a on the actual neighboring moved cover by two. The
proved Sylow small-action theorem therefore puts F in that neighbor's
small mover E. This containment, rather than F's placement in Q_a alone,
makes E preserve the whole-seed fixer D = C_(Z_c)(F).

The critical seed and E both normalize Y = D Z_a. Its section over Z_a
has order at most eight. ResidualSmallSection now shows that the actual
residual cannot lie in E Z_z for a strict trapped candidate: it would
force D into the Baumann slice. The original-radical application retains
one selected edge, transporter and every overlapping path vertex. Its
trapped branch also gives full-X central generation at every component
vertex, excluding the second alternative of the source selector.

No equality of neighboring movers is assumed. Both moving covers and all
central attachments are retained. SylowUnequalResidual supplies the
remaining source residual generation for unequal movers.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.5)(c) and (5.7), printed pp.915--919.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

include e hz hn in
/-- The full reverse kernel lies in the candidate's own small mover, which
therefore preserves its whole-seed fixer. Equal neighboring movers are unnecessary. -/
theorem sixteen_trapped_strict_fixer_normalized_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a z c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (htrap : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    (hnorm : ¬ Z d.radical z ≤ normalizer
      ((Z d.radical c ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) :
        Set (FreeAmalgam d.radical)))
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c)) :
    let F := Z d.radical z ⊓ Q d.radical a
    let D := Z d.radical c ⊓ centralizer (F : Set (FreeAmalgam d.radical))
    let E := SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4
    F ≤ E ∧ ⁅E,F⁆ ≤ Q d.radical c ∧
      E ≤ normalizer (D : Set (FreeAmalgam d.radical)) ∧
      E ⊔ Z d.radical z ≤ normalizer ((D ⊔ Z d.radical a :
        Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) := by
  let F := Z d.radical z ⊓ Q d.radical a
  let D := Z d.radical c ⊓ centralizer (F : Set (FreeAmalgam d.radical))
  let E := SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    rw [p.start_color] at hh
    cases ht : color d.radical t <;> simp_all
  have hc : color d.radical c = false := by
    have hh := adjacent_color_ne d.radical hct
    rw [ht] at hh
    cases hc : color d.radical c <;> simp_all
  have hfix := trapped_strict_seed_fixer_escape_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall hat hct htrap hnorm hstrict
  obtain ⟨J,_,hJ,_,_,_,_,_,hsmallActor⟩ :=
    SylowSmallMovers.edge_normalizer_small_movers_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hc hct
  have hT := SylowLarge.sixteen_edge_relative_normalizer_knownSimple
    (e := e) (hz := hz) (hn := hn) (by omega : 2 < replacementDistance h d) hcard hc hct
  rw [hT] at hJ
  have hFT : F ≤ Q d.radical t := inf_le_right.trans (Q_le_adjacent_h d.radical ht hat)
  have hFE : F ≤ E ∧ ⁅E,F⁆ ≤ Q d.radical c := by
    have hh := hsmallActor F hFT hfix.1
    rwa [←hJ] at hh
  have hEN : E ≤ normalizer (D : Set (FreeAmalgam d.radical)) :=
    SylowPairedFixer.small_mover_preserves_seed_fixer_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hcard hc hct F hFE.1
  refine ⟨hFE.1,hFE.2,hEN,sup_le ?_ hfix.2.2⟩
  have hEG : E ≤ stabilizer d.radical a := (SmallMover.join_le _ _ _ _).trans
    (fun _ hx => hx.2 _ (adjacent_symm d.radical hat))
  exact (le_inf hEN (hEG.trans (Z_normalized d.radical a))).trans
    (normalizer_inf_normalizer_le_normalizer_sup _ _)

include e hz hn in
/-- A strict trapped candidate cannot supply the source residual generation:
its literal mover and critical seed normalize a small fixer span outside the slice. -/
theorem sixteen_trapped_strict_residual_not_le_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a z c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (htrap : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    (hnorm : ¬ Z d.radical z ≤ normalizer
      ((Z d.radical c ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) :
        Set (FreeAmalgam d.radical)))
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c)) :
    ¬ Ltilde d.radical a ≤
      SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4 ⊔ Z d.radical z := by
  let F := Z d.radical z ⊓ Q d.radical a
  let D := Z d.radical c ⊓ centralizer (F : Set (FreeAmalgam d.radical))
  let Y := D ⊔ Z d.radical a
  have hnormal := sixteen_trapped_strict_fixer_normalized_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard p hsmall hat hct htrap hnorm hstrict
  have hf := trapped_strict_seed_fixer_escape_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall hat hct htrap hnorm hstrict
  intro hgen
  have hYN : Ltilde d.radical a ≤ normalizer (Y : Set (FreeAmalgam d.radical)) :=
    hgen.trans hnormal.2.2.2
  have hZV : Z d.radical c ≤ V d.radical a := neighbor_seed_le_radius hat hct
  have hYV : Y ≤ V d.radical a := sup_le (inf_le_left.trans hZV) (Z_le_VBall d.radical a 2)
  have hVG : V d.radical a ≤ stabilizer d.radical a :=
    (replacementGeometry h d).V_local a p.start_color (by
      rw [(replacementGeometry h d).distance_constant a p.start_color]
      exact (by omega : 2 < replacementDistance h d))
  let := finite_stabilizer d.radical a
  let : Finite (Z d.radical c ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective
      (inclusion (sup_le (hZV.trans hVG) (Z_le_stabilizer d.radical a))) (inclusion_injective _)
  have hindex : (Z d.radical a).relIndex Y ≤ 8 :=
    (relIndex_le_of_le_right (show Y ≤ Z d.radical c ⊔ Z d.radical a from
      sup_le_sup inf_le_left le_rfl) index_ne_zero_of_finite).trans
        (SylowSpanSelection.adjacent_seed_span_index_le_eight
          (e := e) (hz := hz) (hn := hn) hb p.start_color hat hct)
  exact hf.2.1 (le_sup_left.trans (residual_small_radius_le_slice_knownSimple (e := e)
    (by omega : 2 < replacementDistance h d) p.start_color Y hYV hYN hindex))

include e hz hn in
/-- The actual original radical and the same transported candidate yield
an overlapping backward path or a precise residual-generation obstruction.
In the latter case full-X central generation holds at every component vertex. -/
theorem original_radical_strict_backward_residual_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {z delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4)
    (hfirst : p.walk.getVert 1 = beta d.radical)
    (hdelta : Adjacent d.radical delta (beta d.radical))
    (hstrict : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical delta)) :
    let T := ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical)
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      ∃ g ∈ stabilizer d.radical (alpha d.radical),
        act d.radical g (beta d.radical) = t ∧
        Adjacent d.radical (act d.radical g delta) t ∧
        T.map (MulAut.conj g⁻¹).toMonoidHom ⊔ Z d.radical z = stabilizer d.radical (alpha d.radical) ∧
        2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical (act d.radical g delta)) ∧
        let c := act d.radical g delta
        ¬ Z d.radical z ≤ normalizer ((Z d.radical c ⊔ Z d.radical (alpha d.radical) :
          Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) ∧
        ((∃ q : CriticalPath d.radical (replacementGeometry h d)
            c (p.walk.getVert (p.walk.length-2)),
          q.walk.getVert 1 = t ∧
          ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∨
        (let F := Z d.radical z ⊓ Q d.radical (alpha d.radical)
         let D := Z d.radical c ⊓ centralizer (F : Set (FreeAmalgam d.radical))
         let E := SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4
         Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) ∧
         Nat.card (⁅Z d.radical c,F⁆ : Subgroup (FreeAmalgam d.radical)) = 2 ∧
         ⁅Z d.radical c,F⁆ ≤ ⁅Z d.radical (alpha d.radical),Z d.radical z⁆ ⊔
           (Z d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))) ∧
         F ≤ E ∧ ⁅E,F⁆ ≤ Q d.radical c ∧
         E ≤ normalizer (D : Set (FreeAmalgam d.radical)) ∧
         E ⊔ Z d.radical z ≤ normalizer ((D ⊔ Z d.radical (alpha d.radical) :
           Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) ∧
         ¬ D ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) ∧
         ¬ Ltilde d.radical (alpha d.radical) ≤ E ⊔ Z d.radical z ∧
         ∀ v, color d.radical v = false →
           X d.radical v = U d.radical v ⊔
             (X d.radical v ⊓ centralizer (stabilizer d.radical v : Set (FreeAmalgam d.radical))))) := by
  obtain ⟨t,hat,g,hg,hgt,hct,hgen,hi,hnorm,halt⟩ :=
    original_radical_strict_backward_line_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hcard p hsmall hfirst hdelta hstrict
  refine ⟨t,hat,g,hg,hgt,hct,hgen,hi,hnorm,?_⟩
  rcases halt with hpath | htrap
  · exact Or.inl hpath
  · have hnE := sixteen_trapped_strict_fixer_normalized_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hcard p hsmall hat hct htrap.1 hnorm hi
    have hres := sixteen_trapped_strict_residual_not_le_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hcard p hsmall hat hct htrap.1 hnorm hi
    have hX := SylowPairedFixer.trapped_nonnormalized_full_kernel_knownSimple
      (e := e) (hz := hz) (hn := hn) (by omega : 2 < replacementDistance h d)
        p hsmall hat hct htrap.1 hnorm
    exact Or.inr ⟨htrap.1,htrap.2.1,htrap.2.2.1,hnE.1,hnE.2.1,hnE.2.2.1,hnE.2.2.2,
      htrap.2.2.2.2.1,hres,X_central_generation_all p.end_color hX.1⟩

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
