module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MidpointCore
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.PredecessorResidual
/-!
# Bounds for the entire midpoint-core movement

For a large distance-four critical path, the entire midpoint core acts
quadratically on the starting seed. Its movement is contained in the
moving cover and fixed by the opposite endpoint. That endpoint has image
of order at least four, so its fixed subgroup has index at least four.
Consequently the midpoint-core movement has order at most eight in either
of the moving covers of orders sixteen and thirty-two.

For every critical image, the full endpoint kernel has commutator of order
at most eight with the midpoint core. Joining the kernel to the central
midpoint seed does not change that commutator. Thus an actor normalizing
this join also normalizes the full kernel/core commutator. The final theorem
applies both calculations to the same full endpoint restriction and backward
path constructed in FullSeedBackward, retaining the central attachment,
index, exact critical commutator, whole-kernel join and relative normalizer.

The normalization proved here is by the selected endpoint restriction.
The original-Sylow small-backward obstruction still concerns the relative
edge normalizer. These bounds do not establish normalization by that group,
fixedness under the whole midpoint stabilizer, or bounds on the derived
subgroup of the whole residual core [Q,Ltilde]. The remaining large-image
and chosen large-slice contradictions stay with this terminal family.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (5.2)(ii), (5.12)(1)--(2), printed pp.914--915,924--926.
The graph and quotient maps are those of the natural characteristic
replacement of Section 7, with both full central covers retained.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.GroupTheory Representation.NormalElementaryQuotient
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)


include s in
/-- The movement of the whole midpoint core has order at most eight. -/
theorem large_midpoint_movement_card
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hlarge : 4 ≤ (Q d.radical z).relIndex (Z d.radical a)) :
    Nat.card (⁅Z d.radical a,Q d.radical (p.walk.getVert 2)⁆ :
      Subgroup (FreeAmalgam d.radical)) ≤ 8 := by
  let H := ⁅Z d.radical a,Q d.radical (p.walk.getVert 2)⁆
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hHU : H ≤ U d.radical a := (large_midpoint_movement s hc hb p hlarge).1
  have hZQ : Z d.radical z ≤ Q d.radical (p.walk.getVert 2) := by
    apply Z_le_Q_of_dist_lt d.radical z ((replacementGeometry h d).exists_critical z p.end_color)
    rw [(replacementGeometry h d).distance_constant _ p.end_color,SimpleGraph.dist_comm,p.dist_end,hl]
    exact show 2 < replacementDistance h d by omega
  have hHZ : H ≤ centralizer (Z d.radical z : Set (FreeAmalgam d.radical)) :=
    (large_midpoint_core_quadratic s hc hb p hlarge).trans (centralizer_le hZQ)
  obtain ⟨i,hi,hir,hiQ,hiU⟩ := vertex_coordinates (h := h) hc a p.start_color
  have hZG : Z d.radical z ≤ i.range := by
    rw [hir]
    exact critical_Z_le_stabilizer d.radical (replacementGeometry h d) a p.start_color
      (by rw [(replacementGeometry h d).distance_constant _ p.start_color]
          exact replacementDistance_pos h d) p.critical
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) z p.end_color
  have hindex : 4 ≤ H.relIndex (U d.radical a) := by
    rw [←hiU]
    apply embedded_centralizing_index_four_le s i hi (Z d.radical z) H hZG hHZ
    rw [hiQ]
    exact reverse_critical_image_four_le s hc (replacementDistance_pos h d) p hlarge
  have hprod := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam d.radical)) H
    (U d.radical a) bot_le hHU
  simp only [relIndex_bot_left] at hprod
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color d.radical p.start_color
  have hact : act d.radical g (alpha d.radical) = mVertex d.radical g := by
    simp only [alpha,act_mVertex,one_mul]
  have hcard : Nat.card (U d.radical (mVertex d.radical g)) ≤ 32 := by
    rw [←hact,U_act,card_map_of_injective (MulAut.conj g⁻¹).injective]
    rcases graph_U_card s hc with hh | hh <;> omega
  nlinarith

private theorem kernel_join_core_normalized
    {F : Type*} [Group F] (K Z Q A : Subgroup F)
    (hZQ : ⁅Z,Q⁆ = ⊥) (hKQ : K ≤ Q)
    (hAN : A ≤ normalizer ((K ⊔ Z : Subgroup F) : Set F))
    (hAQ : A ≤ normalizer (Q : Set F)) :
    A ≤ normalizer ((⁅K,Q⁆ : Subgroup F) : Set F) := by
  have he : ⁅K ⊔ Z,Q⁆ = ⁅K,Q⁆ := by
    rw [commutator_comm (K ⊔ Z),commutator_comm K]
    symm
    exact commutator_eq_of_centralizing_sup (sup_comm _ _)
      (commutator_eq_bot_iff_le_centralizer.mp hZQ)
      (hKQ.trans Q.le_normalizer)
  rw [←he]
  intro x hx
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [map_commutator,mem_normalizer_iff_map_conj_eq.mp (hAN hx),
    mem_normalizer_iff_map_conj_eq.mp (hAQ hx)]

include s in
/-- The exact whole backward kernel inherits the chosen actor's normality
on its midpoint-core commutator, with the uniform eight-element bound. -/
theorem critical_kernel_core_control
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (A : Subgroup (FreeAmalgam d.radical))
    (hAG : A ≤ stabilizer d.radical (p.walk.getVert 2))
    (hAN : A ≤ normalizer (((Z d.radical a ⊓ Q d.radical z) ⊔
      Z d.radical (p.walk.getVert 2) : Subgroup (FreeAmalgam d.radical)) : Set _)) :
    let F := ⁅Z d.radical a ⊓ Q d.radical z,Q d.radical (p.walk.getVert 2)⁆
    F ≤ Q d.radical (p.walk.getVert 2) ∧ Nat.card F ≤ 8 ∧
      A ≤ normalizer (F : Set (FreeAmalgam d.radical)) := by
  let c := p.walk.getVert 2
  let K := Z d.radical a ⊓ Q d.radical z
  let F := ⁅K,Q d.radical c⁆
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hcol : color d.radical c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hZQ : Z d.radical a ≤ Q d.radical c := by
    apply Z_le_Q_of_dist_lt d.radical a ((replacementGeometry h d).exists_critical a p.start_color)
    rw [(replacementGeometry h d).distance_constant _ p.start_color,p.dist_start (by omega)]
    exact show 2 < replacementDistance h d by omega
  have hKQ : K ≤ Q d.radical c := inf_le_left.trans hZQ
  have hFQ : F ≤ Q d.radical c :=
    (Subgroup.commutator_le_sup _ _).trans (sup_le hKQ le_rfl)
  have hnorm : A ≤ normalizer (F : Set (FreeAmalgam d.radical)) :=
    kernel_join_core_normalized K (Z d.radical c) (Q d.radical c) A
      (Z_centralizes_Q d.radical c hcol) hKQ hAN
      (hAG.trans (Q_normalized d.radical c))
  let q : CriticalPath d.radical (replacementGeometry h d) z a := {
    start_color := p.end_color
    walk := p.walk.reverse
    shortest := by rw [SimpleGraph.Walk.length_reverse,p.shortest,SimpleGraph.dist_comm]
    critical := critical_reverse_pair s hc p }
  have hqmid : q.walk.getVert 2 = c := by
    change p.walk.reverse.getVert 2 = p.walk.getVert 2
    rw [SimpleGraph.Walk.getVert_reverse,hl]
  have hcard := critical_midpoint_whole_core_card s hc hb q
  rw [hqmid] at hcard
  exact ⟨hFQ,hcard,hnorm⟩

include e hz hn in
/-- The same full endpoint restriction controls the entire selected backward
kernel and midpoint core. Both image alternatives and the relative normalizer
are retained; no whole-stabilizer normalization is assumed. -/
theorem large_image_full_seed_backward_core_bounds_knownSimple
    (hb : replacementDistance h d = 4)
    {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hlarge : 4 ≤ (Q d.radical z).relIndex (Z d.radical (alpha d.radical))) :
    ∃ (W : Subgroup (FreeAmalgam d.radical)) (t c : Vertex d.radical),
      Z d.radical (p.walk.getVert 3) ≤ W ∧ W ≤ Z d.radical z ∧
      W.relIndex (Z d.radical z) ≤ 2 ∧
      ⁅Z d.radical (alpha d.radical),W⁆ =
        ⁅Z d.radical (alpha d.radical),Z d.radical z⁆ ∧
      (¬ W ≤ Q d.radical (alpha d.radical)) ∧
      Adjacent d.radical (alpha d.radical) t ∧ Adjacent d.radical c t ∧
      (normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
        stabilizer d.radical (alpha d.radical)) ⊔ W = stabilizer d.radical (alpha d.radical) ∧
      ∃ q : CriticalPath d.radical (replacementGeometry h d) c (p.walk.getVert 2),
        q.walk.getVert 1 = t ∧ q.walk.getVert 2 = alpha d.radical ∧
        q.walk.getVert 3 = p.walk.getVert 1 ∧
        2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical c) ∧
        (let K := Z d.radical c ⊓ Q d.radical (p.walk.getVert 2);
         let D := K ⊔ Z d.radical (alpha d.radical);
         let F := ⁅K,Q d.radical (alpha d.radical)⁆;
         ⁅D,W⁆ = ⁅Z d.radical (alpha d.radical),Z d.radical z⁆ ∧
         W ≤ normalizer (D : Set (FreeAmalgam d.radical)) ∧
         F ≤ Q d.radical (alpha d.radical) ∧ Nat.card F ≤ 8 ∧
         W ≤ normalizer (F : Set (FreeAmalgam d.radical)) ∧
         ((Q d.radical (p.walk.getVert 2)).relIndex (Z d.radical c) < 4 →
           ¬ normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
             stabilizer d.radical (alpha d.radical) ≤ normalizer (D : Set (FreeAmalgam d.radical)))) ∧
        ⁅Z d.radical c,Z d.radical (p.walk.getVert 2)⁆ ≤
          centralizer (W : Set (FreeAmalgam d.radical)) ∧
        (4 ≤ (Q d.radical (p.walk.getVert 2)).relIndex (Z d.radical c) →
          let H := ⁅Z d.radical c,Q d.radical (alpha d.radical)⁆;
          H ≤ U d.radical c ∧ H ≤ X d.radical (alpha d.radical) ∧ Nat.card H ≤ 8 ∧
          Q d.radical t ≤ normalizer (H : Set (FreeAmalgam d.radical)) ∧
          ⁅Z d.radical c,Z d.radical (p.walk.getVert 2)⁆ ≤ H) ∧
        ((¬ ∃ P : Sylow 2 (L ⊔ R : Subgroup G),
          (P : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R)) →
          4 ≤ (Q d.radical (p.walk.getVert 2)).relIndex (Z d.radical c)) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨W,hFE,hWZ,hi,hcomm,hWne,_,t,c,hat,hct,hgen,_,q,hq1,hq2,hq3,
    _,hstrict,_,_,hDexact,hWD,hcent,hsmall,hns⟩ :=
    large_image_full_seed_backward_knownSimple (e := e) (hz := hz) (hn := hn) hb p hlarge
  have hWG : W ≤ stabilizer d.radical (alpha d.radical) := le_sup_right.trans_eq hgen
  have hcore := critical_kernel_core_control s hc hb q W
    (hq2.symm ▸ hWG) (by simpa only [hq2] using hWD)
  rw [hq2] at hcore
  refine ⟨W,t,c,hFE,hWZ,hi,hcomm,hWne,hat,hct,hgen,q,hq1,hq2,hq3,hstrict,
    ⟨hDexact,hWD,hcore.1,hcore.2.1,hcore.2.2,hsmall⟩,hcent,?_,hns⟩
  intro hq
  have hm := large_midpoint_movement s hc hb q hq
  have hcq := large_midpoint_movement_card s hc hb q hq
  rw [hq1,hq2] at hm
  rw [hq2] at hcq
  exact ⟨hm.1,hm.2.1,hcq,hm.2.2.1,hm.2.2.2⟩

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
