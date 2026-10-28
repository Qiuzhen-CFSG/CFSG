module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTrappedExclusion
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTrappedExclusion
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.ElementaryKernelControl

/-!
# The trapped kernel line without equal neighboring movers

For a trapped nonnormalizing seed, join it to the starting seed inside the
abelian radius. This elementary actor lies in the endpoint's last edge
radical. The full-displacement alternative would make the endpoint normalize
the selected span, so the two-cover elementary-actor bound gives a kernel
commutator of order at most two. Nonnormalization makes it nonzero.
The line lies in the critical line times the entire endpoint fixed subgroup;
equal neighboring movers and radical-image restrictions are unnecessary.

For a strict slice, the full kernel fixer has index at most two on the
moving cover and cannot lie in the Baumann slice. The endpoint nevertheless
normalizes its join with the starting seed. The original-radical consumer
now returns either a backward critical path or this precise trapped
configuration, together with the proved full-X central generation.

The missing source-(5.5) selector must still normalize this same fixer span
by the appropriate neighboring mover and supply residual generation.
Neither full edge generation nor unequal movers alone implies that premise.
Both moving covers and all central attachments are retained.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.3)(ii)(2), (5.5)(c), and (5.7), printed pp.866--867,915--919.
The internal imports reuse the checked kernel identification and central
attachment calculation within this local proof family.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped commutatorElement Pointwise IsMulCommutative
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
/-- The selected trapped seed has an actual order-two kernel commutator,
aligned with the critical line and the whole endpoint fixed subgroup. -/
theorem trapped_nonnormalizing_seed_kernel_line_knownSimple
    (hb : 4 < replacementDistance h d)
    {a z c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (htrap : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    (hnorm : ¬ Z d.radical z ≤ normalizer
      ((Z d.radical c ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) :
        Set (FreeAmalgam d.radical))) :
    let K := ⁅Z d.radical c,Z d.radical z ⊓ Q d.radical a⁆
    Nat.card K = 2 ∧
      K ≤ ⁅Z d.radical a,Z d.radical z⁆ ⊔
        (Z d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))) := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let F := Z d.radical z ⊓ Q d.radical a
  let P := Z d.radical c ⊔ Z d.radical a
  let K := ⁅Z d.radical c,F⁆
  have hlast := critical_last_edge_inputs (h := h) hb2 p
  have hfixed := critical_full_kernel_eq s hc p
  have hCV := neighbor_seed_le_radius hat hct
  have hAV : Z d.radical a ≤ V d.radical a := Z_le_VBall d.radical a 2
  have hVV : V d.radical a ≤ centralizer (V d.radical a : Set (FreeAmalgam d.radical)) :=
    le_centralizer_iff_isMulCommutative.mpr (V_abelian_of_four_lt d.radical p.start_color hb)
  have hAC : Z d.radical a ≤ centralizer (Z d.radical c : Set (FreeAmalgam d.radical)) :=
    hAV.trans (hVV.trans (centralizer_le hCV))
  have hAF : Z d.radical a ≤ centralizer (F : Set (FreeAmalgam d.radical)) :=
    (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical a p.start_color)).trans
      (centralizer_le inf_le_right)
  have hPF : ⁅P,F⁆ = K := elementary_commutator_sup_central
    (Z d.radical c) (Z d.radical a) F (hAC.trans (Subgroup.centralizer_le_normalizer _)) hAF
  have hcol : color d.radical c = false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hct
    rw [p.start_color] at h1
    cases hc : color d.radical c <;> cases ht : color d.radical t <;> simp_all
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) a p.start_color
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) c hcol
  have hel : IsElementaryAbelian 2 P := IsElementaryAbelian.sup_of_le_centralizer hAC
  have hPt : P ≤ Q d.radical (p.walk.getVert (p.walk.length-1)) :=
    sup_le (htrap.trans hlast.2.1) hlast.2.2
  have hindex : (centralizer (Z d.radical a : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical z) ≤ 2 := by
    let := finite_Z d.radical z
    let : Finite (U d.radical z) := Finite.of_injective
      (inclusion (DistanceEight.U_le_Z d.radical z)) (inclusion_injective _)
    have hQC : Q d.radical a ≤ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical a p.start_color))
    exact ((relIndex_le_of_le_left hQC index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (DistanceEight.U_le_Z d.radical z) index_ne_zero_of_finite)).trans_eq
        (small_critical_indices s hc p hsmall).2
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    rw [p.start_color] at hh
    cases ht : color d.radical t <;> simp_all
  have hFG : F ≤ stabilizer d.radical c :=
    (inf_le_right.trans (Q_le_adjacent_h d.radical ht hat)).trans
      (fun _ hx => hx.2 _ (adjacent_symm d.radical hct))
  have hKC : K ≤ Z d.radical c :=
    le_normalizer_iff_commutator_le_left.mp (hFG.trans (Z_normalized d.radical c))
  have hcrit : ⁅Z d.radical z,Z d.radical a⁆ ≤ Z d.radical a := by
    rw [commutator_comm]
    exact ((critical_Z_commutator_le_moving (h := h) p).trans inf_le_left).trans
      (DistanceEight.U_le_Z d.radical a)
  have hfail : ¬ ⁅Z d.radical z,P⁆ ≤
      ⁅Z d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)),P⁆ ⊔
        ⁅Z d.radical z,Z d.radical a⁆ := by
    intro hh
    rw [←hfixed,commutator_comm F P,hPF] at hh
    apply hnorm
    exact le_normalizer_iff_commutator_le_right.mpr
      (hh.trans (sup_le (hKC.trans le_sup_left) (hcrit.trans le_sup_right)))
  have hcontrol := elementary_edge_kernel_small_aligned s hc p.end_color hlast.1
    (Z d.radical a) P hlast.2.2 hPt le_sup_right hel p.critical.2 hindex hfail
  rw [←hfixed,commutator_comm F P,hPF] at hcontrol
  have hCG : Z d.radical c ≤ stabilizer d.radical z :=
    (htrap.trans hlast.2.1).trans (fun _ hx => hx.2 _ (adjacent_symm d.radical hlast.1))
  have hne := nonnormalizing_seed_kernel_ne_bot s hc hb2 p hsmall hCV hCG hnorm
  let := finite_Z d.radical c
  let : Finite K := Finite.of_injective (inclusion hKC) (inclusion_injective _)
  have hpos : 1 < Nat.card K := (one_lt_card_iff_ne_bot K).mpr hne
  have hbound : Nat.card K ≤ 2 := hcontrol.1
  change Nat.card K = 2 ∧ _
  refine ⟨by omega,?_⟩
  simpa only [commutator_comm (Z d.radical z) (Z d.radical a)] using hcontrol.2

include e hz hn in
/-- The whole kernel fixer escapes the strict Baumann slice although the
critical endpoint normalizes its join with the starting seed. -/
theorem trapped_strict_seed_fixer_escape_knownSimple
    (hb : 4 < replacementDistance h d)
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
    (centralizer (F : Set (FreeAmalgam d.radical))).relIndex (U d.radical c) ≤ 2 ∧
      ¬ D ≤ B d.radical a ((replacementGeometry h d).Z_normal _) ∧
      Z d.radical z ≤ normalizer ((D ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) :
        Set (FreeAmalgam d.radical)) := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let F := Z d.radical z ⊓ Q d.radical a
  let D := Z d.radical c ⊓ centralizer (F : Set (FreeAmalgam d.radical))
  have hline := trapped_nonnormalizing_seed_kernel_line_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall hat hct htrap hnorm
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    rw [p.start_color] at hh
    cases ht : color d.radical t <;> simp_all
  have hcol : color d.radical c = false := by
    have hh := adjacent_color_ne d.radical hct
    rw [ht] at hh
    cases hc : color d.radical c <;> simp_all
  have hFG : F ≤ stabilizer d.radical c :=
    (inf_le_right.trans (Q_le_adjacent_h d.radical ht hat)).trans
      (fun _ hx => hx.2 _ (adjacent_symm d.radical hct))
  let := finite_Z d.radical c
  have hKC : ⁅Z d.radical c,F⁆ ≤ Z d.radical c :=
    le_normalizer_iff_commutator_le_left.mp (hFG.trans (Z_normalized d.radical c))
  let : Finite (⁅Z d.radical c,F⁆ : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion hKC) (inclusion_injective _)
  have hsmallU : Nat.card (⁅U d.radical c,F⁆ : Subgroup (FreeAmalgam d.radical)) ≤ 2 :=
    (card_le_of_le (commutator_mono (DistanceEight.U_le_Z d.radical c) le_rfl)).trans_eq hline.1
  have hi := moving_small_commutator_fixed_index s hc hcol F hFG hsmallU
  refine ⟨hi,?_,?_⟩
  · intro hDB
    let : Finite (U d.radical c) := Finite.of_injective
      (inclusion (DistanceEight.U_le_Z d.radical c)) (inclusion_injective _)
    have hUB : U d.radical c ⊓ centralizer (F : Set (FreeAmalgam d.radical)) ≤
        B d.radical a ((replacementGeometry h d).Z_normal _) :=
      (inf_le_inf_right _ (DistanceEight.U_le_Z d.radical c)).trans hDB
    have hh := relIndex_le_of_le_left hUB
      (index_ne_zero_of_finite (H := (U d.radical c ⊓
        centralizer (F : Set (FreeAmalgam d.radical))).subgroupOf (U d.radical c)))
    rw [inf_relIndex_left] at hh
    exact (Nat.not_le_of_gt hstrict) (hh.trans hi)
  · have hDmove : ⁅D,Z d.radical z⁆ ≤ Z d.radical a :=
      small_critical_predecessor_commutator s hc hb2 p hsmall D (inf_le_left.trans htrap) inf_le_right
    have hcrit : ⁅Z d.radical a,Z d.radical z⁆ ≤ Z d.radical a :=
      ((critical_Z_commutator_le_moving (h := h) p).trans inf_le_left).trans
        (DistanceEight.U_le_Z d.radical a)
    have hCG : Z d.radical c ≤ stabilizer d.radical a :=
      (neighbor_seed_le_radius hat hct).trans ((replacementGeometry h d).V_local a p.start_color (by
        rw [(replacementGeometry h d).distance_constant a p.start_color]; exact hb2))
    have hmove := commutator_sup_le_of_relative_normal (stabilizer d.radical a)
      D (Z d.radical a) (Z d.radical z) (Z d.radical a) (Z_normalized d.radical a)
      (inf_le_left.trans hCG) (Z_le_stabilizer d.radical a) hDmove hcrit
    exact le_normalizer_iff_commutator_le_left.mpr (hmove.trans le_sup_right)

include e hz hn in
/-- The literal original radical supplies a backward path or an aligned
trapped kernel line with its escaping fixer and full-X central generation. -/
theorem original_radical_strict_backward_line_knownSimple
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
         Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) ∧
         Nat.card (⁅Z d.radical c,F⁆ : Subgroup (FreeAmalgam d.radical)) = 2 ∧
         ⁅Z d.radical c,F⁆ ≤ ⁅Z d.radical (alpha d.radical),Z d.radical z⁆ ⊔
           (Z d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))) ∧
         (centralizer (F : Set (FreeAmalgam d.radical))).relIndex (U d.radical c) ≤ 2 ∧
         ¬ D ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) ∧
         Z d.radical z ≤ normalizer ((D ⊔ Z d.radical (alpha d.radical) :
           Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) ∧
         X d.radical z = U d.radical z ⊔
           (X d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))) ∧
         X d.radical z ⊓ Q d.radical (alpha d.radical) = F ⊔
           (X d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))))) := by
  obtain ⟨t,hat,g,hg,hgt,hct,hgen,hi,hnorm,halt⟩ :=
    SylowSpanSelection.original_radical_strict_backward_alternative_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hcard p hsmall hfirst hdelta hstrict
  rw [hfirst] at hgt
  refine ⟨t,hat,g,hg,hgt,hct,hgen,hi,hnorm,?_⟩
  rcases halt with hpath | htrap
  · exact Or.inl hpath
  · have hline := trapped_nonnormalizing_seed_kernel_line_knownSimple
      (e := e) (hz := hz) (hn := hn) hb p hsmall hat hct htrap.1 hnorm
    have hfix := trapped_strict_seed_fixer_escape_knownSimple
      (e := e) (hz := hz) (hn := hn) hb p hsmall hat hct htrap.1 hnorm hi
    have hX := SylowPairedFixer.trapped_nonnormalized_full_kernel_knownSimple
      (e := e) (hz := hz) (hn := hn) (by omega : 2 < replacementDistance h d)
        p hsmall hat hct htrap.1 hnorm
    exact Or.inr ⟨htrap.1,hline.1,hline.2,hfix.1,hfix.2.1,hfix.2.2,hX.1,hX.2.1⟩

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
