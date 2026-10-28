module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowStrictShift
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubePredecessorSlice
public import Theory.GroupTheory.Commutator.NilpotentSaturation
public import Theory.GroupTheory.SubgroupPartitionCounting
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubePredecessorSlice

import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTrappedExclusion

/-!
# Residual fixedness of a full predecessor kernel

A predecessor moving-slice index at most two identifies the full reverse
critical kernel with the predecessor slice. The last edge core normalizes
this kernel and its moving part. Retain the central edge attachment: the
full kernel is the moving kernel joined with the last edge seed, and that
seed centralizes the edge core. The moving kernel is proper in a cover of
order sixteen or thirty-two, so it has order at most sixteen. Nilpotent
commutator saturation makes its core commutator proper, hence of order at
most eight.

The predecessor residual normalizes that commutator by fixing the slice
modulo the predecessor seed. Together with edge-core normalization this
gives normality in the entire predecessor stabilizer. The symmetric-six
small-section theorem then gives residual fixedness. Whole-stabilizer
centrality is not asserted. No radical-image hypothesis or cube model is
needed for this argument.

In the image-sixteen trapped-radius branch, the proved strict shifts supply
the slice premise at every critical predecessor. The consumer preserves the
full kernel commutator while conjugating any predecessor-core actor by the
same residual element. This is the residual transport needed for (5.8).
The internal imports reuse existing generic commutator and graph lemmas
without changing their public boundaries.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.3) and (5.7)--(5.8), printed pp.866--867 and 919--920.
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

private theorem nilpotent_small_commutator_card {H : Type*} [Group H]
    (T F : Subgroup H) [Finite F] (hT : Group.IsNilpotent T)
    (hFT : F ≤ T) (hTF : T ≤ normalizer (F : Set H))
    (hcard : Nat.card F ≤ 16) : Nat.card (⁅F,T⁆ : Subgroup H) ≤ 8 := by
  let N := ⁅F,T⁆
  have hNF : N ≤ F := le_normalizer_iff_commutator_le_left.mp hTF
  let : Finite N := Finite.of_injective (inclusion hNF) (inclusion_injective _)
  by_cases hbot : F = ⊥
  · simp only [hbot,commutator_bot_left,card_bot]
    decide
  have hi : N.relIndex F ≠ 1 := by
    intro hi
    have hFN : F ≤ N := relIndex_eq_one.mp hi
    have hz : F ≤ (⊥ : Subgroup H) :=
      le_of_le_sup_commutator_of_isNilpotent T F ⊥ T hT hFT bot_le le_rfl
        (by rw [Subgroup.normalizer_eq_top]; exact le_top) (by simpa only [bot_sup_eq] using hFN)
    exact hbot (le_bot_iff.mp hz)
  have hip : 0 < N.relIndex F := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hi2 : 2 ≤ N.relIndex F := by omega
  have hc := relIndex_mul_card_of_le hNF
  have hbound : 2 * Nat.card N ≤ 16 :=
    (Nat.mul_le_mul_right (Nat.card N) hi2).trans (hc.le.trans hcard)
  change Nat.card N ≤ 8
  omega

/-- A small full predecessor slice has a residual-fixed core commutator,
without a condition on the radical image. -/
theorem predecessor_slice_commutator_residual_fixed
    (s : FullSymmetricAction h e hz hn d) (hc : DistanceTwo.CentralLayer d)
    (hb : 2 < replacementDistance h d) {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hindex : (B d.radical (p.walk.getVert (p.walk.length-2))
      ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical z) ≤ 2) :
    let c := p.walk.getVert (p.walk.length-2)
    let K := Z d.radical z ⊓ Q d.radical a
    let N := ⁅K,Q d.radical c⁆
    Nat.card N ≤ 8 ∧ N ≤ fixedCore d.radical c ∧
      stabilizer d.radical c ≤ normalizer (N : Set (FreeAmalgam d.radical)) := by
  let c := p.walk.getVert (p.walk.length-2)
  let t := p.walk.getVert (p.walk.length-1)
  let K := Z d.radical z ⊓ Q d.radical a
  let F := U d.radical z ⊓ Q d.radical a
  let N := ⁅K,Q d.radical c⁆
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hcol : color d.radical c = false := by
    apply (p.vertex_color (Nat.sub_le _ _)).mpr
    have he := replacementDistance_even h d
    rw [Nat.even_iff] at he ⊢
    have hh : p.walk.length = replacementDistance h d := p.length_eq_b
    omega
  have hct : Adjacent d.radical c t := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  have hzt : Adjacent d.radical z t := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hct
    rw [hcol] at hh
    cases hx : color d.radical t <;> simp_all
  have hQtGz : Q d.radical t ≤ stabilizer d.radical z :=
    fun _ hx => hx.2 _ (adjacent_symm d.radical hzt)
  have hQtGc : Q d.radical t ≤ stabilizer d.radical c :=
    fun _ hx => hx.2 _ (adjacent_symm d.radical hct)
  have hQcQt : Q d.radical c ≤ Q d.radical t := Q_le_adjacent_h d.radical ht hct
  have hslice := critical_predecessor_slice_eq_kernel s hc hb p hindex
  have hKB : K ≤ B d.radical c ((replacementGeometry h d).Z_normal _) :=
    hslice.1.ge.trans inf_le_right
  have hVG := ((replacementGeometry h d).V_le_Q hb c hcol).trans
    (show Q d.radical c ≤ stabilizer d.radical c from fun _ hx => hx.1)
  have hKQ : K ≤ Q d.radical c := by
    intro x hx
    exact (replacementGeometry h d).V_le_Q hb c hcol
      (((mem_B_iff d.radical c _ hVG x).mp (hKB hx)).1)
  have hKn : Q d.radical t ≤ normalizer (K : Set (FreeAmalgam d.radical)) := by
    rw [show K = Z d.radical z ⊓ B d.radical c ((replacementGeometry h d).Z_normal _)
      from hslice.1.symm]
    exact (le_inf (hQtGz.trans (Z_normalized d.radical z))
      (hQtGc.trans (Escape.Propagation.Rigidity.B_normalized hb c hcol))).trans
        inf_normalizer_le_normalizer_inf
  have hFK : F = U d.radical z ⊓ K := by
    dsimp only [F,K]
    rw [←inf_assoc,inf_eq_left.mpr (DistanceEight.U_le_Z d.radical z)]
  have hFQ : F ≤ Q d.radical c := hFK ▸ inf_le_right.trans hKQ
  have hFn : Q d.radical t ≤ normalizer (F : Set (FreeAmalgam d.radical)) := by
    rw [hFK]
    exact (le_inf (hQtGz.trans (U_normalized z)) hKn).trans
      inf_normalizer_le_normalizer_inf
  have hfixed : K = Z d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) :=
    critical_full_kernel_eq s hc p
  have hFC : F = U d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) := by
    rw [hFK,hfixed,←inf_assoc,inf_eq_left.mpr (DistanceEight.U_le_Z d.radical z)]
  have hZaQt : Z d.radical a ≤ Q d.radical t := by
    apply Z_le_Q_of_dist_lt d.radical a ((replacementGeometry h d).exists_critical a p.start_color)
    rw [(replacementGeometry h d).distance_constant a p.start_color,p.dist_start (Nat.sub_le _ _)]
    have he : p.walk.length = replacementDistance h d := p.length_eq_b
    change p.walk.length-1 < replacementDistance h d
    omega
  have hseed : Z d.radical t ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
    intro x hx
    rw [Z,if_neg (by simp [ht])] at hx
    exact (mem_omegaCenter_iff.mp hx).2.2
  have hseedA := hseed.trans (centralizer_le hZaQt)
  have hseedN : Z d.radical t ≤ normalizer (U d.radical z : Set (FreeAmalgam d.radical)) :=
    ((adjacent_Z_le d.radical p.end_color hzt).trans (Z_le_stabilizer d.radical z)).trans
      (U_normalized z)
  have hdecomp : K = F ⊔ Z d.radical t := by
    rw [hfixed,hFC,DistanceTwo.CentralLayer.Z_eq_moving_sup_edge_at h e hz d p.end_color hzt,
      sup_comm (U d.radical z),inf_centralizer_sup_of_centralizing _ _ _ hseedN hseedA]
    exact sup_comm _ _
  have hNF : N = ⁅F,Q d.radical c⁆ := by
    apply le_antisymm _ (commutator_mono (hFK ▸ inf_le_right) le_rfl)
    rw [hdecomp]
    apply commutator_le.mpr
    intro x hx r hr
    have hn : Z d.radical t ≤ normalizer (F : Set (FreeAmalgam d.radical)) := by
      rw [hFC]
      exact (le_inf hseedN (hseedA.trans (centralizer (Z d.radical a : Set
        (FreeAmalgam d.radical))).le_normalizer)).trans inf_normalizer_le_normalizer_inf
    have hp : x ∈ (F : Set (FreeAmalgam d.radical)) * (Z d.radical t : Set (FreeAmalgam d.radical)) := by
      rw [←coe_mul_of_right_le_normalizer_left F (Z d.radical t) hn]
      exact hx
    obtain ⟨w,hw,v,hv,rfl⟩ := hp
    have hzero : ⁅v,r⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (hseed hv r (hQcQt hr)).symm
    rw [commutatorElement_mul_left_eq_conj_mul,hzero,mul_one,mul_inv_cancel,one_mul]
    exact commutator_mem_commutator hw hr
  let := finite_Z d.radical z
  let : Finite (U d.radical z) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z d.radical z)) (inclusion_injective _)
  let : Finite F := Finite.of_injective (inclusion (show F ≤ U d.radical z from inf_le_left))
    (inclusion_injective _)
  have hFU : F ≤ U d.radical z := inf_le_left
  have hi : F.relIndex (U d.radical z) ≠ 1 := by
    intro hi
    have hUK : U d.radical z ≤ K := (relIndex_eq_one.mp hi).trans (hFK ▸ inf_le_right)
    have hcentral : U d.radical z ≤ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) :=
      hUK.trans (hfixed ▸ inf_le_right)
    let q := CriticalPath.ofPair (geometry := replacementGeometry h d) p.end_color
      (critical_reverse_pair s hc p)
    have heq := small_critical_moving_commutator_eq s hc q (by rw [hslice.2.2]; decide)
    have hbot := commutator_eq_bot_iff_le_centralizer.mpr hcentral
    rw [heq,commutator_comm] at hbot
    exact critical_Z_commutator_ne_bot s hc p hbot
  have hip : 0 < F.relIndex (U d.radical z) := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hi2 : 2 ≤ F.relIndex (U d.radical z) := by omega
  have hUcard : Nat.card (U d.radical z) ≤ 32 := by
    obtain ⟨i,hi,_,_,hiU⟩ := vertex_coordinates (h := h) hc z p.end_color
    rw [←hiU,card_map_of_injective hi]
    rcases moved_card s with he | he <;> omega
  have hFcard : Nat.card F ≤ 16 := by
    have he := relIndex_mul_card_of_le hFU
    have hh := (Nat.mul_le_mul_right (Nat.card F) hi2).trans (he.le.trans hUcard)
    omega
  let := finite_stabilizer d.radical c
  let : Finite (Q d.radical c) := Finite.of_injective
    (inclusion (show Q d.radical c ≤ stabilizer d.radical c from fun _ hx => hx.1))
      (inclusion_injective _)
  have hNcard : Nat.card N ≤ 8 := by
    rw [hNF]
    exact nilpotent_small_commutator_card (Q d.radical c) F
      (Q_isPGroup d.radical (replacement_radical_isPGroup h d)
        (replacement_core_le_radical h d) c hcol).isNilpotent hFQ (hQcQt.trans hFn) hFcard
  have hNQ : N ≤ Q d.radical c :=
    (Subgroup.commutator_le_sup _ _).trans (sup_le hKQ le_rfl)
  have hfix : ⁅Ltilde d.radical c,K⁆ ≤ centralizer (Q d.radical c : Set (FreeAmalgam d.radical)) := by
    apply le_trans _ (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical c hcol))
    apply commutator_le.mpr
    intro l hl x hx
    exact ((mem_B_iff d.radical c _ hVG x).mp (hKB hx)).2 l hl
  have hLn : Ltilde d.radical c ≤ normalizer (N : Set (FreeAmalgam d.radical)) :=
    fixed_mod_seed_normalizes_commutator K (Q d.radical c) (Ltilde d.radical c)
      (hKQ.trans (Q d.radical c).le_normalizer)
      ((Ltilde_le_stabilizer c).trans (Q_normalized d.radical c)) hfix
  have hTn : Q d.radical t ≤ normalizer (N : Set (FreeAmalgam d.radical)) := by
    intro x hx
    apply mem_normalizer_iff_map_conj_eq.mpr
    dsimp only [N]
    rw [map_commutator,mem_normalizer_iff_map_conj_eq.mp (hKn hx),
      mem_normalizer_iff_map_conj_eq.mp ((hQtGc.trans (Q_normalized d.radical c)) hx)]
  have hNn : stabilizer d.radical c ≤ normalizer (N : Set (FreeAmalgam d.radical)) := by
    rw [←core_residual_edge_generation (h := h) hcol hct]
    exact sup_le hLn hTn
  exact ⟨hNcard,le_inf hNQ (small_normal_core_fixed s hcol N hNQ hNn hNcard),hNn⟩

include e hz hn in
/-- Trapping in the image-sixteen branch supplies residual fixedness at every
critical predecessor, with the full reverse kernel and both covers retained. -/
theorem sixteen_trapped_predecessor_residual_fixed_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a₀ z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a₀ z)
    (htrap : V d.radical a₀ ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    {a a' : Vertex d.radical}
    (q : CriticalPath d.radical (replacementGeometry h d) a a') :
    let c := q.walk.getVert (q.walk.length-2)
    let N := ⁅Z d.radical a' ⊓ Q d.radical a,Q d.radical c⁆
    Nat.card N ≤ 8 ∧ N ≤ fixedCore d.radical c ∧
      stabilizer d.radical c ≤ normalizer (N : Set (FreeAmalgam d.radical)) := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hl : 2 < q.walk.length := q.length_eq_b ▸ hb2
  have hcol : color d.radical (q.walk.getVert (q.walk.length-2)) = false := by
    apply (q.vertex_color (Nat.sub_le _ _)).mpr
    have he := replacementDistance_even h d
    rw [Nat.even_iff] at he ⊢
    have hh : q.walk.length = replacementDistance h d := q.length_eq_b
    omega
  have hct : Adjacent d.radical (q.walk.getVert (q.walk.length-2))
      (q.walk.getVert (q.walk.length-1)) := by
    have hh := q.walk.adj_getVert_succ (i := q.walk.length-2) (by omega)
    rw [show q.walk.length-2+1=q.walk.length-1 by omega] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  have het : Adjacent d.radical a' (q.walk.getVert (q.walk.length-1)) := by
    have hh := q.walk.adj_getVert_succ (i := q.walk.length-1) (by omega)
    rw [show q.walk.length-1+1=q.walk.length by omega,q.walk.getVert_length] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  exact predecessor_slice_commutator_residual_fixed s hc hb2 q
    (sixteen_trapped_all_slices_le_two_knownSimple (e := e) (hz := hz) (hn := hn)
      hb hcard p htrap hcol hct het)

include e hz hn in
/-- A predecessor residual element preserves the commutator while conjugating
an arbitrary core actor, using the literal full reverse kernel. -/
theorem sixteen_trapped_radius_residual_transport_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a₀ a₁ : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a₀ a₁)
    (hbad : V d.radical a₀ ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    {a a' : Vertex d.radical}
    (q : CriticalPath d.radical (replacementGeometry h d) a a')
    (D : Subgroup (FreeAmalgam d.radical))
    (hD : D ≤ Q d.radical (q.walk.getVert (q.walk.length-2)))
    (k : FreeAmalgam d.radical)
    (hk : k ∈ Ltilde d.radical (q.walk.getVert (q.walk.length-2))) :
    ⁅Z d.radical a' ⊓ Q d.radical a,D.map (MulAut.conj k).toMonoidHom⁆ =
      ⁅Z d.radical a' ⊓ Q d.radical a,D⁆ := by
  have hh := sixteen_trapped_predecessor_kernel_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard p hbad q
  have hn := sixteen_trapped_predecessor_residual_fixed_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard p hbad q
  have hcol : color d.radical (q.walk.getVert (q.walk.length-2)) = false := by
    apply (q.vertex_color (Nat.sub_le _ _)).mpr
    have he := replacementDistance_even h d
    rw [Nat.even_iff] at he ⊢
    have hl : q.walk.length = replacementDistance h d := q.length_eq_b
    omega
  exact slice_commutator_transport_of_fixed (h := h) (by omega) hcol _
    (hh.1.ge.trans inf_le_right) (hn.2.1.trans inf_le_right) D hD k hk

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
