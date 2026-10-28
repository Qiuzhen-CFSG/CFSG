module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SmallKernelNormalizationIntersection
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SixteenSmallSelection
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.SixteenEqual
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.SixteenUnequal
/-!
# Strict intersections for the image-sixteen movers

On an equal neighboring pair of full cube movers, the common omega subgroup
has index four in each full seed. A strict Baumann slice makes a larger seed
intersection impossible, so the seed intersection is exactly that omega.
For two compatible edges whose original and selected movers generate the
stabilizer, their common triple-seed intersection is therefore central.

This consumes the original/selected generation data retained by
SixteenSmallSelection and the generic index argument of
SmallKernelNormalizationIntersection. It is the full-seed form of the
compatible intersection step in MS93 (5.6), (5.12)(1), printed pp.917,924--925.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped commutatorElement Pointwise IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SixteenSmall
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}
local notation "edgeMover" => fun a t : Vertex d.radical =>
  SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4
include e hz hn in
/-- Strict equal-mover seed intersections are the whole central omega of the
common mover; the strict bound rules out larger intermediate subgroups. -/
theorem sixteen_equal_strict_seed_intersection_knownSimple
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    (hb : 2 < replacementDistance h d)
    {a c t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hequal : edgeMover c t =
      edgeMover a t)
    (hgen : ∀ v : Vertex d.radical, color d.radical v = false →
      X d.radical v = U d.radical v ⊔
        (X d.radical v ⊓ centralizer (stabilizer d.radical v : Set (FreeAmalgam d.radical))))
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical c)) :
    Z d.radical a ⊓ Z d.radical c =
      omegaCenter (edgeMover a t) := by
  let J := edgeMover a t
  let W := Z d.radical a ⊓ Z d.radical c
  have hc : color d.radical c = false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hct
    rw [ha] at h1
    cases ht : color d.radical t <;> cases hcc : color d.radical c <;> simp_all
  have hOa := (SixteenEqual.sixteen_equal_mover_omega_control_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard ha hat hct hequal (SylowPairedFixer.central_generation_eq_seed (h := h) ha hat (hgen a ha))).1
  have hOc := (SixteenEqual.sixteen_equal_mover_omega_control_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard hc hct hat hequal.symm (SylowPairedFixer.central_generation_eq_seed (h := h) hc hct (hgen c hc))).1
  dsimp only at hequal
  rw [hequal] at hOc
  change omegaCenter J = _ at hOa hOc
  have hXc := SylowPairedFixer.central_generation_eq_seed (h := h) hc hct (hgen c hc)
  have hZgen : Z d.radical c = U d.radical c ⊔
      (Z d.radical c ⊓ centralizer (stabilizer d.radical c : Set (FreeAmalgam d.radical))) := by
    simpa only [hXc] using hgen c hc
  have hJGc : J ≤ stabilizer d.radical c := by
    change SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4 ≤ _
    rw [←hequal]
    exact (SmallMover.join_le _ _ _ _).trans (fun _ hx => hx.2 _ (adjacent_symm d.radical hct))
  have hfix : (centralizer (J : Set (FreeAmalgam d.radical))).relIndex (U d.radical c) = 4 := by
    obtain ⟨J',_,hJ',_,_,_,_,hfix,_⟩ := Nonelementary.edge_normalizer_small_movers_knownSimple
      (e := e) (hz := hz) (hn := hn) (SixteenUnequal.sixteen_nonelementary hcard) hb hc hct
    rw [SylowLarge.sixteen_edge_relative_normalizer_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hcard hc hct] at hJ'
    change SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4 = _ at hJ'
    rw [hequal] at hJ'
    change (centralizer (SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4 : Set (FreeAmalgam d.radical))).relIndex (U d.radical c) = 4
    rwa [hJ']
  exact strict_seed_intersection_eq_omega hb ha hc J hOa hOc hZgen hJGc hfix hstrict

include e hz hn in
/-- The actual equal-mover triple uses the original and selected full seed
fixers. The same two strict slices justify both intersection identifications. -/
theorem sixteen_equal_compatible_triple_central_knownSimple
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    (hb : 2 < replacementDistance h d)
    {a v c b t : Vertex d.radical} (ha : color d.radical a = false)
    (hab : Adjacent d.radical a b) (hvb : Adjacent d.radical v b)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (heq0 : edgeMover v b =
      edgeMover a b)
    (heq1 : edgeMover c t =
      edgeMover a t)
    (hgen : ∀ w : Vertex d.radical, color d.radical w = false →
      X d.radical w = U d.radical w ⊔
        (X d.radical w ⊓ centralizer (stabilizer d.radical w : Set (FreeAmalgam d.radical))))
    (hstrict0 : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical v))
    (hstrict1 : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical c))
    (hcross : edgeMover a b ⊔ edgeMover a t = stabilizer d.radical a) :
    Z d.radical v ⊓ Z d.radical a ⊓ Z d.radical c ≤
      centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
  have h0 := sixteen_equal_strict_seed_intersection_knownSimple
    (e := e) (hz := hz) (hn := hn) hcard hb ha hab hvb heq0 hgen hstrict0
  have h1 := sixteen_equal_strict_seed_intersection_knownSimple
    (e := e) (hz := hz) (hn := hn) hcard hb ha hat hct heq1 hgen hstrict1
  have hOmega0 := (SixteenEqual.sixteen_equal_mover_omega_control_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard ha hab hvb heq0 (SylowPairedFixer.central_generation_eq_seed (h := h) ha hab (hgen a ha))).1
  have hOmega1 := (SixteenEqual.sixteen_equal_mover_omega_control_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard ha hat hct heq1 (SylowPairedFixer.central_generation_eq_seed (h := h) ha hat (hgen a ha))).1
  have hle : Z d.radical v ⊓ Z d.radical a ⊓ Z d.radical c ≤
      (Z d.radical a ⊓ centralizer
        (edgeMover a b : Set (FreeAmalgam d.radical))) ⊓
        centralizer (edgeMover a t : Set (FreeAmalgam d.radical)) := by
    apply le_inf
    · exact (le_inf (inf_le_left.trans inf_le_right) (inf_le_left.trans inf_le_left)).trans
        (h0.le.trans hOmega0.le)
    · exact (le_inf (inf_le_left.trans inf_le_right) inf_le_right).trans
        (h1.le.trans (hOmega1.le.trans inf_le_right))
  apply le_centralizer_iff.mpr
  rw [←hcross]
  exact sup_le
    (le_centralizer_iff.mp (hle.trans (inf_le_left.trans inf_le_right)))
    (le_centralizer_iff.mp (hle.trans inf_le_right))

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SixteenSmall
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
