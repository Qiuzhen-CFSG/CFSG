module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SmallKernelNormalizationCompatible
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTerminalLines
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.EightEqual
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.EightEqual

/-!
# Strict seed intersections and compatible triple centrality

When two equal neighboring movers have centrally generated full omega
layers, their common central omega lies in both seeds and has index four.
A strict Baumann slice prevents the seed intersection from being any larger.
Thus the intersection is exactly the full mover fixer, with central
attachments retained. Two compatible original and selected mover fixers
then make the triple seed intersection central in the middle stabilizer.

Source: MS93 (5.6)(b), (5.12)(1), printed pp.917,924--925.
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


/-- An index-four full-seed fixer cannot sit properly inside a seed
intersection whose Baumann slice index is strictly larger than two. -/
theorem strict_seed_intersection_eq_omega
    (hb : 2 < replacementDistance h d)
    {a c : Vertex d.radical} (ha : color d.radical a = false)
    (hc : color d.radical c = false)
    (J : Subgroup (FreeAmalgam d.radical))
    (hOa : omegaCenter J = Z d.radical a ⊓ centralizer (J : Set (FreeAmalgam d.radical)))
    (hOc : omegaCenter J = Z d.radical c ⊓ centralizer (J : Set (FreeAmalgam d.radical)))
    (hZgen : Z d.radical c = U d.radical c ⊔
      (Z d.radical c ⊓ centralizer (stabilizer d.radical c : Set (FreeAmalgam d.radical))))
    (hJGc : J ≤ stabilizer d.radical c)
    (hfix : (centralizer (J : Set (FreeAmalgam d.radical))).relIndex (U d.radical c) = 4)
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical c)) :
    Z d.radical a ⊓ Z d.radical c = omegaCenter J := by
  let W := Z d.radical a ⊓ Z d.radical c
  have hOW : omegaCenter J ≤ W := le_inf (hOa.le.trans inf_le_left) (hOc.le.trans inf_le_left)
  have hZsup : U d.radical c ⊔ omegaCenter J = Z d.radical c := by
    apply le_antisymm (sup_le (DistanceEight.U_le_Z d.radical c) (hOc.le.trans inf_le_left))
    rw [hZgen]
    exact sup_le le_sup_left ((inf_le_inf_left _ (centralizer_le hJGc)).trans
      (hOc.ge.trans le_sup_right))
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) c hc
  have hON : Z d.radical c ≤ normalizer (omegaCenter J : Set (FreeAmalgam d.radical)) :=
    ((le_centralizer_iff_isMulCommutative.mpr inferInstance : Z d.radical c ≤
      centralizer (Z d.radical c : Set (FreeAmalgam d.radical))).trans
      (centralizer_le (hOc.le.trans inf_le_left))).trans (Subgroup.centralizer_le_normalizer _)
  let : ((omegaCenter J).subgroupOf (Z d.radical c)).Normal :=
    normal_subgroupOf_of_le_normalizer hON
  have hi := relIndex_sup_right ((U d.radical c).subgroupOf (Z d.radical c))
    ((omegaCenter J).subgroupOf (Z d.radical c))
  rw [←subgroupOf_sup (DistanceEight.U_le_Z d.radical c) (hOc.le.trans inf_le_left),
    relIndex_subgroupOf (sup_le (DistanceEight.U_le_Z d.radical c) (hOc.le.trans inf_le_left)),
    relIndex_subgroupOf (DistanceEight.U_le_Z d.radical c),hZsup] at hi
  have hindex : (omegaCenter J).relIndex (Z d.radical c) = 4 := by
    rw [hi,hOc]
    have hinf : (Z d.radical c ⊓ centralizer (J : Set (FreeAmalgam d.radical))) ⊓ U d.radical c =
        centralizer (J : Set (FreeAmalgam d.radical)) ⊓ U d.radical c := by
      rw [inf_assoc,inf_eq_right.mpr (inf_le_right.trans (DistanceEight.U_le_Z d.radical c))]
    rw [←inf_relIndex_right,hinf,inf_relIndex_right]
    exact hfix
  let := finite_Z d.radical c
  let : Finite (U d.radical c) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z d.radical c)) (inclusion_injective _)
  have hWB : W ≤ B d.radical a ((replacementGeometry h d).Z_normal _) :=
    inf_le_left.trans (Escape.EdgeTransfer.Z_le_B hb a ha)
  have hWi : 2 < W.relIndex (Z d.radical c) :=
    hstrict.trans_le ((relIndex_le_of_le_left hWB index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (DistanceEight.U_le_Z d.radical c) index_ne_zero_of_finite))
  have hm := relIndex_mul_relIndex (omegaCenter J) W (Z d.radical c) hOW inf_le_right
  rw [hindex] at hm
  have hpos : 0 < (omegaCenter J).relIndex W :=
    Nat.pos_of_ne_zero (by intro he; rw [he,zero_mul] at hm; omega)
  have hone : (omegaCenter J).relIndex W = 1 := by nlinarith
  exact le_antisymm (relIndex_eq_one.mp hone) hOW

include e hz hn in
/-- Strict equal-mover seed intersections are the whole central omega of the
common mover; the strict bound rules out larger intermediate subgroups. -/
theorem eight_equal_strict_seed_intersection_knownSimple
    (hne : ¬ IsElementaryAbelian 2 (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8)
    (hb : 2 < replacementDistance h d)
    {a c t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hequal : EightEdgeComparison.edgeMover (d := d) c t =
      EightEdgeComparison.edgeMover (d := d) a t)
    (hgen : ∀ v : Vertex d.radical, color d.radical v = false →
      X d.radical v = U d.radical v ⊔
        (X d.radical v ⊓ centralizer (stabilizer d.radical v : Set (FreeAmalgam d.radical))))
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical c)) :
    Z d.radical a ⊓ Z d.radical c =
      omegaCenter (EightEdgeComparison.edgeMover (d := d) a t) := by
  let J := EightEdgeComparison.edgeMover (d := d) a t
  let W := Z d.radical a ⊓ Z d.radical c
  have hc : color d.radical c = false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hct
    rw [ha] at h1
    cases ht : color d.radical t <;> cases hcc : color d.radical c <;> simp_all
  have hOa := (EightEqual.equal_mover_omega_control_knownSimple
    (e := e) (hz := hz) (hn := hn) hne hcard hb ha hat hct hequal (hgen a ha)).1
  have hOc := (EightEqual.equal_mover_omega_control_knownSimple
    (e := e) (hz := hz) (hn := hn) hne hcard hb hc hct hat hequal.symm (hgen c hc)).1
  rw [hequal] at hOc
  change omegaCenter J = _ at hOa hOc
  have hXc := SylowPairedFixer.central_generation_eq_seed (h := h) hc hct (hgen c hc)
  have hZgen : Z d.radical c = U d.radical c ⊔
      (Z d.radical c ⊓ centralizer (stabilizer d.radical c : Set (FreeAmalgam d.radical))) := by
    simpa only [hXc] using hgen c hc
  have hJGc : J ≤ stabilizer d.radical c := by
    change EightEdgeComparison.edgeMover (d := d) a t ≤ _
    rw [←hequal]
    exact EightEqual.edgeMover_le_stabilizer (d := d) hct
  have hfix := (EightMovers.edge_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hne hcard hb hc hct).2.2.2.2.2.2.2.2.1
  change (centralizer (EightEdgeComparison.edgeMover (d := d) c t : Set (FreeAmalgam d.radical))).relIndex
    (U d.radical c) = 4 at hfix
  rw [hequal] at hfix
  exact strict_seed_intersection_eq_omega hb ha hc J hOa hOc hZgen hJGc hfix hstrict

include e hz hn in
/-- The actual equal-mover triple uses the original and selected full seed
fixers. The same two strict slices justify both intersection identifications. -/
theorem eight_equal_compatible_triple_central_knownSimple
    (hne : ¬ IsElementaryAbelian 2 (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8)
    (hb : 2 < replacementDistance h d)
    {a v c b t : Vertex d.radical} (ha : color d.radical a = false)
    (hab : Adjacent d.radical a b) (hvb : Adjacent d.radical v b)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (heq0 : EightEdgeComparison.edgeMover (d := d) v b =
      EightEdgeComparison.edgeMover (d := d) a b)
    (heq1 : EightEdgeComparison.edgeMover (d := d) c t =
      EightEdgeComparison.edgeMover (d := d) a t)
    (hgen : ∀ w : Vertex d.radical, color d.radical w = false →
      X d.radical w = U d.radical w ⊔
        (X d.radical w ⊓ centralizer (stabilizer d.radical w : Set (FreeAmalgam d.radical))))
    (hstrict0 : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical v))
    (hstrict1 : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical c))
    (hfixed : (Z d.radical a ⊓ centralizer
      (EightEdgeComparison.edgeMover (d := d) a b : Set (FreeAmalgam d.radical))) ⊓
      centralizer (EightEdgeComparison.edgeMover (d := d) a t : Set (FreeAmalgam d.radical)) =
      Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) :
    Z d.radical v ⊓ Z d.radical a ⊓ Z d.radical c ≤
      centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
  have h0 := eight_equal_strict_seed_intersection_knownSimple
    (e := e) (hz := hz) (hn := hn) hne hcard hb ha hab hvb heq0 hgen hstrict0
  have h1 := eight_equal_strict_seed_intersection_knownSimple
    (e := e) (hz := hz) (hn := hn) hne hcard hb ha hat hct heq1 hgen hstrict1
  have hOmega0 := (EightEqual.equal_mover_omega_control_knownSimple
    (e := e) (hz := hz) (hn := hn) hne hcard hb ha hab hvb heq0 (hgen a ha)).1
  have hOmega1 := (EightEqual.equal_mover_omega_control_knownSimple
    (e := e) (hz := hz) (hn := hn) hne hcard hb ha hat hct heq1 (hgen a ha)).1
  have hle : Z d.radical v ⊓ Z d.radical a ⊓ Z d.radical c ≤
      (Z d.radical a ⊓ centralizer
        (EightEdgeComparison.edgeMover (d := d) a b : Set (FreeAmalgam d.radical))) ⊓
        centralizer (EightEdgeComparison.edgeMover (d := d) a t : Set (FreeAmalgam d.radical)) := by
    apply le_inf
    · exact (le_inf (inf_le_left.trans inf_le_right) (inf_le_left.trans inf_le_left)).trans
        (h0.le.trans hOmega0.le)
    · exact (le_inf (inf_le_left.trans inf_le_right) inf_le_right).trans
        (h1.le.trans (hOmega1.le.trans inf_le_right))
  exact hle.trans (hfixed.le.trans inf_le_right)

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
