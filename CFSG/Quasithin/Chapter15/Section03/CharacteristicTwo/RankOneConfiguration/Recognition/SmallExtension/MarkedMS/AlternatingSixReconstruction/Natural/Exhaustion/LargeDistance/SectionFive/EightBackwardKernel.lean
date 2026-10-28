module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EightSmallMovers
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowKernelPair
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowKernelDecomposition
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowSingleMover

/-!
# Backward common kernels in the surviving image-eight branch

The replacement edge core and its larger relative normalizer fix exactly
the same small critical lines. The edge's unique small mover has index two;
if only the larger actor moved the line, the whole edge would lie in that
proper mover. A moving edge element gives two distinct full critical
hyperplanes. Their intersection is therefore the common kernel for both
actors, with index four in the entire starting seed.

The existing full-cover displacement estimate then applies to the actual
edge orbit. Its common kernel is the internal product of the critical line
and the whole edge omega seed. Every edge subactor has the same commutator
on that kernel as on the critical line. Reversing the literal critical walk
shows that a trapped backward seed centralizes the common reverse kernel;
each full reverse hyperplane has centralizer index at most two.

Movement on a prescribed backward seed, or on the whole starting radius,
constructs an actual backward critical path with every overlapping vertex
retained. The original-radical consumers keep its literal embedding and
index two over the replacement edge, both moved-cover orders sixteen and
thirty-two, and all central attachments. The fixed-common-kernel branch,
unconditional backward selection, image-eight terminal exclusion and general
distance-four estimates remain required for LargeDistanceInput.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.5)--(5.8), printed pp.915--920. The private imports reuse the
generic orbit/fixer and finite-index arguments of the existing natural
graph family; no equality with its exceptional graph is used.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped commutatorElement Pointwise IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EightBackwardKernel
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

include e hz hn in
/-- In image eight, the edge core fixes the small critical line exactly
when its larger relative normalizer does. Properness of the edge's small
mover rules out an extra fixed-line case after restriction. -/
theorem critical_line_fixed_iff_knownSimple
    (hb : 4 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4) :
    let T := Q d.radical (p.walk.getVert 1)
    let N := normalizer (T : Set (FreeAmalgam d.radical)) ⊓ stabilizer d.radical a
    N ≤ centralizer ((⁅Z d.radical a,Z d.radical a'⁆ :
      Subgroup (FreeAmalgam d.radical)) : Set _) ↔
      T ≤ centralizer ((⁅Z d.radical a,Z d.radical a'⁆ :
        Subgroup (FreeAmalgam d.radical)) : Set _) := by
  classical
  let T := Q d.radical (p.walk.getVert 1)
  let N := normalizer (T : Set (FreeAmalgam d.radical)) ⊓ stabilizer d.radical a
  let J := SmallMover.join (U d.radical a) (Q d.radical a) T 4
  let K := Z d.radical a ⊓ Q d.radical a'
  have hl : 0 < p.walk.length := p.length_eq_b ▸ replacementDistance_pos h d
  have hat : Adjacent d.radical a (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) hl
  have hTN : T ≤ N := le_inf T.le_normalizer
    (fun _ hx => hx.2 _ (adjacent_symm d.radical hat))
  constructor
  · exact fun hh => hTN.trans hh
  intro hfixed
  by_contra hmove
  obtain ⟨hJ,_,_,_,_,hJi,_⟩ := EightSmallMovers.edge_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p.start_color hat
  have hk := SylowSmallMovers.small_critical_kernel_small_movers_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hTK : T ≤ normalizer (K : Set (FreeAmalgam d.radical)) := by
    have hh := le_inf (hTN.trans inf_le_right) hfixed
    rw [←small_critical_kernel_normalizer_eq_line_centralizer s hc p hsmall] at hh
    exact hh.trans inf_le_right
  have hTJ : T ≤ J := by
    rw [show J = _ from hJ,←hk.2.2.2 hmove]
    exact le_inf le_rfl (le_inf hTN hTK)
  have hi : J.relIndex T = 1 := relIndex_eq_one.mpr hTJ
  change J.relIndex T = 2 at hJi
  omega


include e hz hn in
/-- When the actual edge core moves the critical line, its common full
kernel equals the kernel fixed by the larger relative-normalizer orbit. -/
theorem edge_orbit_kernel_eq_knownSimple
    (hb : 4 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hmove : ¬ Q d.radical (p.walk.getVert 1) ≤ centralizer
      ((⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) : Set _)) :
    let T := Q d.radical (p.walk.getVert 1)
    let N := normalizer (T : Set (FreeAmalgam d.radical)) ⊓ stabilizer d.radical a
    let K := Z d.radical a ⊓ Q d.radical a'
    let F := Z d.radical a ⊓ centralizer (componentOrbit (Z d.radical a') T : Set _)
    F = Z d.radical a ⊓ centralizer (componentOrbit (Z d.radical a') N : Set _) ∧
      F = ⨅ x : T, K.map (MulAut.conj (x : FreeAmalgam d.radical)).toMonoidHom ∧
      F.relIndex (Z d.radical a) = 4 ∧
      N ≤ normalizer (F : Set (FreeAmalgam d.radical)) := by
  classical
  let T := Q d.radical (p.walk.getVert 1)
  let N := normalizer (T : Set (FreeAmalgam d.radical)) ⊓ stabilizer d.radical a
  let K := Z d.radical a ⊓ Q d.radical a'
  have hl : 0 < p.walk.length := p.length_eq_b ▸ replacementDistance_pos h d
  have hat : Adjacent d.radical a (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) hl
  have hTN : T ≤ N := le_inf T.le_normalizer
    (fun _ hx => hx.2 _ (adjacent_symm d.radical hat))
  obtain ⟨x,hx,hxD⟩ := SetLike.not_le_iff_exists.mp hmove
  have hp := SylowKernelPair.small_kernel_pair_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall x (hTN hx) hxD
  have hi := SylowKernelPair.small_seed_orbit_identifications_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p
  let I := ⨅ x : T, K.map (MulAut.conj (x : FreeAmalgam d.radical)).toMonoidHom
  have hpair : I = K ⊓ K.map (MulAut.conj x).toMonoidHom := by
    apply le_antisymm
    · apply le_inf
      · have hh := iInf_le (fun y : T => K.map
          (MulAut.conj (y : FreeAmalgam d.radical)).toMonoidHom) 1
        have he : (MulAut.conj ((1 : T) : FreeAmalgam d.radical)).toMonoidHom = MonoidHom.id _ := by
          apply MonoidHom.ext
          intro y
          change (1 : FreeAmalgam d.radical)*y*(1 : FreeAmalgam d.radical)⁻¹=y
          simp only [one_mul,inv_one,mul_one]
        rwa [he,Subgroup.map_id] at hh
      · exact iInf_le (fun y : T => K.map (MulAut.conj (y : FreeAmalgam d.radical)).toMonoidHom) ⟨x,hx⟩
    · rw [←hp.1]
      exact le_iInf (fun y : T => iInf_le (fun z : N => K.map (MulAut.conj (z : FreeAmalgam d.radical)).toMonoidHom) ⟨y,hTN y.property⟩)
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hfixed : Z d.radical a ⊓ centralizer (Z d.radical a' : Set (FreeAmalgam d.radical)) = K := by
    apply le_antisymm
    · apply le_inf inf_le_left
      rw [←C_eq_Q s hc a' p.end_color]
      exact le_inf (inf_le_left.trans (Z_le_stabilizer_of_dist_le a _ p.critical.1.le)) inf_le_right
    · exact inf_le_inf_left _ (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical a' p.end_color)))
  have hF : Z d.radical a ⊓ centralizer (componentOrbit (Z d.radical a') T : Set _) = I := by
    rw [SylowKernelPair.orbit_fixer _ _ _
      ((hTN.trans inf_le_right).trans (Z_normalized d.radical a)),hfixed]
  dsimp only
  refine ⟨?_,hF,?_,?_⟩
  · rw [hF,hpair,hi.2.2.2,hp.1]
  · rw [hF,hpair]; exact hp.2.2.2
  · rw [hF,hpair]; exact hp.2.1

include e hz hn in
/-- The whole common kernel has one nontrivial displacement line under the
actual edge core. This line is fixed even by its larger relative normalizer. -/
theorem common_kernel_line_displacement_knownSimple
    (hb : 4 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hmove : ¬ Q d.radical (p.walk.getVert 1) ≤ centralizer
      ((⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) : Set _)) :
    let T := Q d.radical (p.walk.getVert 1)
    let N := normalizer (T : Set (FreeAmalgam d.radical)) ⊓ stabilizer d.radical a
    let D := ⁅Z d.radical a,Z d.radical a'⁆
    let W := componentOrbit D T
    let F := Z d.radical a ⊓ centralizer (componentOrbit (Z d.radical a') T : Set _)
    W ≤ F ∧ ⁅D,T⁆ = ⁅W,T⁆ ∧ ⁅D,T⁆ = ⁅F,T⁆ ∧
      Nat.card (⁅D,T⁆ : Subgroup (FreeAmalgam d.radical)) = 2 ∧
      ⁅D,T⁆ ≤ Z d.radical (p.walk.getVert 1) ∧
      ⁅D,T⁆ ≤ centralizer (N : Set (FreeAmalgam d.radical)) := by
  let T := Q d.radical (p.walk.getVert 1)
  let N := normalizer (T : Set (FreeAmalgam d.radical)) ⊓ stabilizer d.radical a
  let D := ⁅Z d.radical a,Z d.radical a'⁆
  let W := componentOrbit D T
  let E := componentOrbit (Z d.radical a') N
  let F := Z d.radical a ⊓ centralizer (componentOrbit (Z d.radical a') T : Set _)
  have hl : 0 < p.walk.length := p.length_eq_b ▸ replacementDistance_pos h d
  have hat : Adjacent d.radical a (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) hl
  have hTN : T ≤ N := le_inf T.le_normalizer
    (fun _ hx => hx.2 _ (adjacent_symm d.radical hat))
  have hmoveN := fun hh => hmove (hTN.trans hh)
  have he := edge_orbit_kernel_eq_knownSimple (e := e) (hz := hz) (hn := hn) hb p hsmall hmove
  have hi := SylowKernelPair.small_seed_orbit_identifications_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p
  have hq := SylowKernelPair.small_seed_orbit_quadratic_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall
  have ho := SylowMovingLine.small_critical_line_orbit_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall
  have hc := SylowCommonKernel.moving_common_kernel_edge_control_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall hmoveN
  have hWN : W ≤ componentOrbit D N := by
    apply iSup_le
    intro x
    exact le_iSup_of_le ⟨x,hTN x.property⟩ le_rfl
  have hWE : componentOrbit D N ≤ centralizer (E : Set (FreeAmalgam d.radical)) := by
    have hh := commutator_eq_bot_iff_le_centralizer.mp hq.1
    rwa [hi.2.2.1] at hh
  have hWF : W ≤ F := by
    rw [show F = _ from he.1]
    exact hWN.trans (le_inf (ho.1.trans (DistanceEight.U_le_Z d.radical a)) hWE)
  have hDF : D ≤ F := (le_componentOrbit D T).trans hWF
  have hle : ⁅D,T⁆ ≤ ⁅F,T⁆ := commutator_mono hDF le_rfl
  have hboundF : Nat.card (⁅F,T⁆ : Subgroup (FreeAmalgam d.radical)) ≤ 2 := by
    rw [show F = _ from he.1]; exact hc.2.2.1
  have hseed : ⁅F,T⁆ ≤ Z d.radical (p.walk.getVert 1) := by
    rw [show F = _ from he.1]; exact hc.2.2.2.1
  have hcent : ⁅F,T⁆ ≤ centralizer (N : Set (FreeAmalgam d.radical)) := by
    rw [show F = _ from he.1]; exact hc.2.2.2.2
  let := finite_Z d.radical (p.walk.getVert 1)
  let : Finite (⁅F,T⁆ : Subgroup (FreeAmalgam d.radical)) := Finite.of_injective
    (inclusion hseed) (inclusion_injective _)
  let : Finite (⁅D,T⁆ : Subgroup (FreeAmalgam d.radical)) := Finite.of_injective
    (inclusion hle) (inclusion_injective _)
  have hnz : ⁅D,T⁆ ≠ ⊥ := by
    intro hh
    exact hmove (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hh))
  have hpos := (one_lt_card_iff_ne_bot (⁅D,T⁆ : Subgroup (FreeAmalgam d.radical))).mpr hnz
  have hbound := card_le_of_le hle
  have hcardD : Nat.card (⁅D,T⁆ : Subgroup (FreeAmalgam d.radical)) = 2 := by omega
  have hDFcomm : ⁅D,T⁆ = ⁅F,T⁆ := eq_of_le_of_card_ge hle (by omega)
  have hDW : ⁅D,T⁆ = ⁅W,T⁆ := le_antisymm
    (commutator_mono (le_componentOrbit D T) le_rfl)
    ((commutator_mono hWF le_rfl).trans_eq hDFcomm.symm)
  exact ⟨hWF,hDW,hDFcomm,hcardD,hDFcomm ▸ hseed,hDFcomm ▸ hcent⟩

include e hz hn in
/-- Every edge element moving the small critical line has the same fixer
on the common full kernel as the whole edge core. That kernel is the
internal product of the critical line and the entire fixed subgroup. -/
theorem line_mover_common_kernel_knownSimple
    (hb : 4 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (x : FreeAmalgam d.radical) (hx : x ∈ Q d.radical (p.walk.getVert 1))
    (hxD : x ∉ centralizer ((⁅Z d.radical a,Z d.radical a'⁆ :
      Subgroup (FreeAmalgam d.radical)) : Set _)) :
    let T := Q d.radical (p.walk.getVert 1)
    let D := ⁅Z d.radical a,Z d.radical a'⁆
    let F := Z d.radical a ⊓ centralizer (componentOrbit (Z d.radical a') T : Set _)
    let C := Z d.radical a ⊓ centralizer (T : Set (FreeAmalgam d.radical))
    F = D ⊔ C ∧ D ⊓ C = ⊥ ∧ C.relIndex (Z d.radical a) = 8 ∧
      C.relIndex F = 2 ∧
      F ⊓ centralizer ({x} : Set (FreeAmalgam d.radical)) = C ∧
      ⁅F,zpowers x⁆ = ⁅D,T⁆ := by
  let T := Q d.radical (p.walk.getVert 1)
  let D := ⁅Z d.radical a,Z d.radical a'⁆
  let E := componentOrbit (Z d.radical a') T
  let F := Z d.radical a ⊓ centralizer (E : Set (FreeAmalgam d.radical))
  let C := Z d.radical a ⊓ centralizer (T : Set (FreeAmalgam d.radical))
  have hmove : ¬ T ≤ centralizer (D : Set (FreeAmalgam d.radical)) := fun hh => hxD (hh hx)
  have hd := common_kernel_line_displacement_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall hmove
  have hDF : D ≤ F := (le_componentOrbit D T).trans hd.1
  have hFZ : F ≤ Z d.radical a := inf_le_left
  have hl : 0 < p.walk.length := p.length_eq_b ▸ replacementDistance_pos h d
  have hat : Adjacent d.radical a (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) hl
  have hiN := SylowKernelPair.small_seed_orbit_identifications_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p
  have hc := edge_orbit_kernel_eq_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall hmove
  have hAT : Z d.radical a' ≤ T := (le_componentOrbit _ _).trans hiN.1
  have hET : E ≤ T := (componentOrbit_le_sup _ _).trans (sup_le hAT le_rfl)
  have hTS : T ≤ stabilizer d.radical a := fun _ ht => ht.2 _ (adjacent_symm d.radical hat)
  have hTF : T ≤ normalizer (F : Set (FreeAmalgam d.radical)) :=
    (le_inf (hTS.trans (Z_normalized d.radical a))
      ((le_normalizer_componentOrbit (Z d.radical a') T).trans
        (normalizer_le_normalizer_centralizer E))).trans
        inf_normalizer_le_normalizer_inf
  let := finite_Z d.radical a
  let : Finite F := Finite.of_injective (inclusion hFZ) (inclusion_injective _)
  let : Finite D := Finite.of_injective (inclusion (hDF.trans hFZ)) (inclusion_injective _)
  let : Finite C := Finite.of_injective
    (inclusion (show C ≤ Z d.radical a from inf_le_left)) (inclusion_injective _)
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) a p.start_color
  have hFFT : ⁅F,T⁆ ≤ F := le_normalizer_iff_commutator_le_left.mp hTF
  let : Finite (⁅F,T⁆ : Subgroup (FreeAmalgam d.radical)) := Finite.of_injective
    (inclusion hFFT) (inclusion_injective _)
  have hcardFT : Nat.card (⁅F,T⁆ : Subgroup (FreeAmalgam d.radical)) = 2 :=
    hd.2.2.1 ▸ hd.2.2.2.1
  have hxF : x ∉ centralizer (F : Set (FreeAmalgam d.radical)) :=
    fun hh => hxD (centralizer_le hDF hh)
  have hcentral : ⁅F,T⁆ ≤ centralizer (F : Set (FreeAmalgam d.radical)) :=
    (hFFT.trans hFZ).trans ((le_centralizer (Z d.radical a)).trans (centralizer_le hFZ))
  have hfx := SylowSingleMover.single_mover_fixed_index F ⁅F,T⁆ x
    (commutator_mono le_rfl (zpowers_le.mpr hx)) hcentral hcardFT hxF
  have hCF : C ≤ F := inf_le_inf_left _ (centralizer_le hET)
  have hCx : C ≤ F ⊓ centralizer ({x} : Set (FreeAmalgam d.radical)) := by
    refine le_inf hCF ?_
    intro z hz
    exact mem_centralizer_singleton_iff.mpr ((hz.2 x hx).symm)
  have hFindex : F.relIndex (Z d.radical a) = 4 := hc.2.2.1
  have hbound : C.relIndex (Z d.radical a) ≤ 8 := by
    rw [show C = Z d.radical a ⊓ centralizer (T : Set (FreeAmalgam d.radical)) from rfl,
      inf_relIndex_left]
    exact SylowKernelDecomposition.edge_fixed_index_bound (e := e) (hz := hz) (hn := hn) hb p.start_color hat
  have hmul := relIndex_mul_relIndex C F (Z d.radical a) hCF hFZ
  rw [hFindex] at hmul
  have hupper : C.relIndex F ≤ 2 := by omega
  have hlower : 2 ≤ C.relIndex F := by
    have hh := relIndex_le_of_le_left hCx
      (index_ne_zero_of_finite : C.relIndex F ≠ 0)
    rw [inf_relIndex_left] at hh
    exact hfx ▸ hh
  have hidxC : C.relIndex F = 2 := by omega
  have hfull : C.relIndex (Z d.radical a) = 8 := by omega
  have hmulx := relIndex_mul_relIndex C
    (F ⊓ centralizer ({x} : Set (FreeAmalgam d.radical))) F hCx inf_le_left
  rw [inf_relIndex_left,hfx,hidxC] at hmulx
  have hfixed : F ⊓ centralizer ({x} : Set (FreeAmalgam d.radical)) = C :=
    le_antisymm (relIndex_eq_one.mp (by omega)) hCx
  have hxle : ⁅F,zpowers x⁆ ≤ ⁅F,T⁆ := commutator_mono le_rfl (zpowers_le.mpr hx)
  let : Finite (⁅F,zpowers x⁆ : Subgroup (FreeAmalgam d.radical)) := Finite.of_injective
    (inclusion hxle) (inclusion_injective _)
  have hxne : ⁅F,zpowers x⁆ ≠ ⊥ := by
    intro he
    have hh := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he)
    exact hxF (hh (mem_zpowers x))
  have hxpos := (one_lt_card_iff_ne_bot (⁅F,zpowers x⁆ : Subgroup (FreeAmalgam d.radical))).mpr hxne
  have hxeq : ⁅F,zpowers x⁆ = ⁅F,T⁆ := eq_of_le_of_card_ge hxle (by omega)
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hcent := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hcardD : Nat.card D = 2 := small_critical_commutator_card s hcent p hsmall
  have hnotDC : ¬ D ≤ C := by
    intro hh
    exact hxD (le_centralizer_iff.mp (hh.trans inf_le_right) hx)
  let : Finite (D ⊓ C : Subgroup (FreeAmalgam d.radical)) := Finite.of_injective
    (inclusion inf_le_left) (inclusion_injective _)
  have hdisjoint : D ⊓ C = ⊥ := by
    by_contra hh
    have hpos := (one_lt_card_iff_ne_bot (D ⊓ C : Subgroup (FreeAmalgam d.radical))).mpr hh
    have heq : D ⊓ C = D := eq_of_le_of_card_ge inf_le_left (by omega)
    exact hnotDC (heq ▸ (show D ⊓ C ≤ C from inf_le_right))
  have hCD : C ≤ normalizer (D : Set (FreeAmalgam d.radical)) :=
    ((show C ≤ Z d.radical a from inf_le_left).trans
      ((le_centralizer (Z d.radical a)).trans (centralizer_le (hDF.trans hFZ)))).trans
        (Subgroup.centralizer_le_normalizer _)
  have hjoinindex : C.relIndex (D ⊔ C) = 2 := by
    rw [relIndex_sup_of_normalizes D C hCD,←inf_relIndex_right,inf_comm,hdisjoint]
    simpa using hcardD
  have hjoinF : D ⊔ C ≤ F := sup_le hDF hCF
  have hmuljoin := relIndex_mul_relIndex C (D ⊔ C) F le_sup_right hjoinF
  rw [hjoinindex,hidxC] at hmuljoin
  have hjoin : F = D ⊔ C := le_antisymm (relIndex_eq_one.mp (by omega)) hjoinF
  exact ⟨hjoin,hdisjoint,hfull,hidxC,hfixed,hxeq.trans hd.2.2.1.symm⟩



include e hz hn in
/-- Any subactor of the actual edge core has the same displacement on the
common full kernel as on the original critical line. This is the estimate
used after restricting to the predecessor core. -/
theorem common_kernel_subactor_knownSimple
    (hb : 4 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hmove : ¬ Q d.radical (p.walk.getVert 1) ≤ centralizer
      ((⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) : Set _))
    (A : Subgroup (FreeAmalgam d.radical)) (hA : A ≤ Q d.radical (p.walk.getVert 1)) :
    let T := Q d.radical (p.walk.getVert 1)
    let D := ⁅Z d.radical a,Z d.radical a'⁆
    let F := Z d.radical a ⊓ centralizer (componentOrbit (Z d.radical a') T : Set _)
    ⁅F,A⁆ = ⁅D,A⁆ ∧
      Nat.card (⁅F,A⁆ : Subgroup (FreeAmalgam d.radical)) ≤ 2 ∧
      ⁅F,A⁆ ≤ Z d.radical (p.walk.getVert 1) ∧
      ⁅F,A⁆ ≤ centralizer (T : Set (FreeAmalgam d.radical)) := by
  classical
  let T := Q d.radical (p.walk.getVert 1)
  let D := ⁅Z d.radical a,Z d.radical a'⁆
  let F := Z d.radical a ⊓ centralizer (componentOrbit (Z d.radical a') T : Set _)
  let C := Z d.radical a ⊓ centralizer (T : Set (FreeAmalgam d.radical))
  obtain ⟨x,hx,hxD⟩ := Set.not_subset.mp hmove
  have hs := line_mover_common_kernel_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall x hx hxD
  have hd := common_kernel_line_displacement_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall hmove
  have hDF : D ≤ F := (le_componentOrbit D T).trans hd.1
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) a p.start_color
  have hDC : D ≤ centralizer (C : Set (FreeAmalgam d.radical)) :=
    (hDF.trans inf_le_left).trans
      ((le_centralizer (Z d.radical a)).trans (centralizer_le inf_le_left))
  have hCA : C ≤ centralizer (A : Set (FreeAmalgam d.radical)) :=
    inf_le_right.trans (centralizer_le hA)
  have hAC : A ≤ normalizer (C : Set (FreeAmalgam d.radical)) :=
    (le_centralizer_iff.mp hCA).trans (Subgroup.centralizer_le_normalizer _)
  have hgen : F = D ⊔ C := hs.1
  have heq : ⁅F,A⁆ = ⁅D,A⁆ := by
    rw [hgen,commutator_sup_of_commuting_factors D C A hDC hAC,
      commutator_eq_bot_iff_le_centralizer.mpr hCA,sup_bot_eq]
  have hle : ⁅F,A⁆ ≤ ⁅D,T⁆ := by
    rw [heq]
    exact commutator_mono le_rfl hA
  let := finite_Z d.radical (p.walk.getVert 1)
  let : Finite (⁅D,T⁆ : Subgroup (FreeAmalgam d.radical)) := Finite.of_injective
    (inclusion hd.2.2.2.2.1) (inclusion_injective _)
  exact ⟨heq,(card_le_of_le hle).trans_eq hd.2.2.2.1,
    hle.trans hd.2.2.2.2.1,hle.trans (hd.2.2.2.2.2.trans (centralizer_le
      (le_inf T.le_normalizer (fun _ hx => hx.2 _ (by
        have hl : 0 < p.walk.length := p.length_eq_b ▸ replacementDistance_pos h d
        apply adjacent_symm d.radical
        apply (cosetGraph_adj d.radical _ _).mp
        simpa only [SimpleGraph.Walk.getVert_zero] using
          p.walk.adj_getVert_succ (i := 0) hl)))))⟩


include e hz hn in
/-- A seed near the opposite critical endpoint centralizes the common full
kernel whenever it belongs to the first edge core. -/
theorem near_seed_common_kernel_knownSimple
    (hb : 4 < replacementDistance h d)
    {a a' c : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hmove : ¬ Q d.radical (p.walk.getVert 1) ≤ centralizer
      ((⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) : Set _))
    (hc : color d.radical c = false)
    (hnear : (cosetGraph d.radical).dist c a' ≤ 2)
    (htrap : Z d.radical c ≤ Q d.radical (p.walk.getVert 1)) :
    let F := Z d.radical a ⊓ centralizer
      (componentOrbit (Z d.radical a') (Q d.radical (p.walk.getVert 1)) : Set _)
    F ≤ centralizer (Z d.radical c : Set (FreeAmalgam d.radical)) := by
  let D := ⁅Z d.radical a,Z d.radical a'⁆
  have hZQ : Z d.radical c ≤ Q d.radical a' := by
    apply Z_le_Q_of_dist_lt d.radical c ((replacementGeometry h d).exists_critical c hc)
    rw [(replacementGeometry h d).distance_constant c hc]
    change (cosetGraph d.radical).dist c a' < replacementDistance h d
    exact lt_of_le_of_lt hnear (by omega)
  have hDZ : D ≤ Z d.radical a' :=
    (critical_Z_commutator_le_moving (h := h) p).trans
      (inf_le_right.trans (DistanceEight.U_le_Z d.radical a'))
  have hDC : D ≤ centralizer (Z d.radical c : Set (FreeAmalgam d.radical)) :=
    hDZ.trans ((commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical a' p.end_color)).trans (centralizer_le hZQ))
  have hh := common_kernel_subactor_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall hmove (Z d.radical c) htrap
  exact commutator_eq_bot_iff_le_centralizer.mp
    (hh.1.trans (commutator_eq_bot_iff_le_centralizer.mpr hDC))

include e hz hn in
/-- The centralizer of a subgroup centralized by the common kernel has
index at most two in every conjugate full critical kernel. -/
theorem common_fixed_full_kernel_indices_knownSimple
    (hb : 4 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hmove : ¬ Q d.radical (p.walk.getVert 1) ≤ centralizer
      ((⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) : Set _))
    (A : Subgroup (FreeAmalgam d.radical))
    (hFC : Z d.radical a ⊓ centralizer
      (componentOrbit (Z d.radical a') (Q d.radical (p.walk.getVert 1)) : Set _) ≤
        centralizer (A : Set (FreeAmalgam d.radical))) :
    ∀ x ∈ Q d.radical (p.walk.getVert 1),
      (centralizer (A : Set (FreeAmalgam d.radical))).relIndex
        ((Z d.radical a ⊓ Q d.radical a').map (MulAut.conj x).toMonoidHom) ≤ 2 := by
  let T := Q d.radical (p.walk.getVert 1)
  let K := Z d.radical a ⊓ Q d.radical a'
  let F := Z d.radical a ⊓ centralizer
    (componentOrbit (Z d.radical a') T : Set (FreeAmalgam d.radical))
  have hl : 0 < p.walk.length := p.length_eq_b ▸ replacementDistance_pos h d
  have hat : Adjacent d.radical a (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) hl
  have hf := edge_orbit_kernel_eq_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall hmove
  have hFZ : F.relIndex (Z d.radical a) = 4 := hf.2.2.1
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hcent := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hKZ : K.relIndex (Z d.radical a) = 2 := by
    rw [show K = Z d.radical a ⊓ Q d.radical a' from rfl,inf_relIndex_left]
    exact (small_critical_indices s hcent p hsmall).1
  intro x hx
  let Kx := K.map (MulAut.conj x).toMonoidHom
  have hzx : (Z d.radical a).map (MulAut.conj x).toMonoidHom = Z d.radical a :=
    mem_normalizer_iff_map_conj_eq.mp (Z_normalized d.radical a
      (hx.2 a (adjacent_symm d.radical hat)))
  have hxZ : Kx ≤ Z d.radical a := (map_mono inf_le_left).trans_eq hzx
  have hxindex : Kx.relIndex (Z d.radical a) = 2 := by
    change (K.map (MulAut.conj x).toMonoidHom).relIndex (Z d.radical a) = 2
    rw [←hzx,relIndex_map_map_of_injective _ _ (MulAut.conj x).injective]
    exact hKZ
  have hFx : F ≤ Kx := by
    rw [show F = ⨅ t : T, K.map (MulAut.conj (t : FreeAmalgam d.radical)).toMonoidHom
      from hf.2.1]
    exact iInf_le _ (⟨x,hx⟩ : T)
  have hmul := relIndex_mul_relIndex F Kx (Z d.radical a) hFx hxZ
  rw [hFZ,hxindex] at hmul
  have hidx : F.relIndex Kx = 2 := by omega
  let := finite_Z d.radical a
  let : Finite Kx := Finite.of_injective (inclusion hxZ) (inclusion_injective _)
  exact (relIndex_le_of_le_left hFC
    (index_ne_zero_of_finite : F.relIndex Kx ≠ 0)).trans_eq hidx

include e hz hn in
/-- A trapped backward seed centralizes the common reverse kernel. Each
full reverse critical kernel has centralizer index at most two. -/
theorem trapped_backward_seed_common_kernel_knownSimple
    (hb : 4 < replacementDistance h d)
    {a a' c : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hmove : ¬ Q d.radical (p.walk.getVert (p.walk.length-1)) ≤ centralizer
      ((⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) : Set _))
    (hc : color d.radical c = false)
    (hnear : (cosetGraph d.radical).dist c a ≤ 2)
    (htrap : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2))) :
    let F := Z d.radical a' ⊓ centralizer
      (componentOrbit (Z d.radical a)
        (Q d.radical (p.walk.getVert (p.walk.length-1))) : Set _)
    F ≤ centralizer (Z d.radical c : Set (FreeAmalgam d.radical)) ∧
      ∀ x ∈ Q d.radical (p.walk.getVert (p.walk.length-1)),
        (centralizer (Z d.radical c : Set (FreeAmalgam d.radical))).relIndex
          ((Z d.radical a' ⊓ Q d.radical a).map (MulAut.conj x).toMonoidHom) ≤ 2 := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hcent := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let r : CriticalPath d.radical (replacementGeometry h d) a' a := {
    start_color := p.end_color
    walk := p.walk.reverse
    shortest := by rw [SimpleGraph.Walk.length_reverse,p.shortest,SimpleGraph.dist_comm]
    critical := critical_reverse_pair s hcent p }
  have hr : r.walk.getVert 1 = p.walk.getVert (p.walk.length-1) :=
    p.walk.getVert_reverse 1
  have hrs : (Q d.radical a).relIndex (Z d.radical a') < 4 := by
    rw [(small_critical_indices s hcent p hsmall).2]
    decide
  have hrm : ¬ Q d.radical (r.walk.getVert 1) ≤ centralizer
      ((⁅Z d.radical a',Z d.radical a⁆ : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    rwa [hr,commutator_comm (Z d.radical a')]
  have hl : 2 < p.walk.length := p.length_eq_b ▸ (by omega : 2 < replacementDistance h d)
  have hct : Adjacent d.radical (p.walk.getVert (p.walk.length-2))
      (p.walk.getVert (p.walk.length-1)) := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  have het : Adjacent d.radical a' (p.walk.getVert (p.walk.length-1)) := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  have ht : color d.radical (p.walk.getVert (p.walk.length-1)) = true := by
    have hh := adjacent_color_ne d.radical het
    rw [p.end_color] at hh
    cases he : color d.radical (p.walk.getVert (p.walk.length-1)) <;> simp_all
  have htrap' : Z d.radical c ≤ Q d.radical (r.walk.getVert 1) := by
    rw [hr]
    exact htrap.trans (Q_le_adjacent_h d.radical ht hct)
  have hh := near_seed_common_kernel_knownSimple
    (e := e) (hz := hz) (hn := hn) hb r hrs hrm hc hnear htrap'
  have hi := common_fixed_full_kernel_indices_knownSimple
    (e := e) (hz := hz) (hn := hn) hb r hrs hrm (Z d.radical c) hh
  dsimp only at hh hi ⊢
  rw [hr] at hh hi
  exact ⟨hh,hi⟩

include e hz hn in
/-- Movement of the common reverse kernel selects a backward critical path
through the prescribed two-edge seed, retaining the entire overlap. -/
theorem backward_path_of_common_kernel_movement_knownSimple
    (hb : 4 < replacementDistance h d)
    {a a' c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hmove : ¬ Q d.radical (p.walk.getVert (p.walk.length-1)) ≤ centralizer
      ((⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) : Set _))
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hnotfixed : ¬ (Z d.radical a' ⊓ centralizer
      (componentOrbit (Z d.radical a)
        (Q d.radical (p.walk.getVert (p.walk.length-1))) : Set _)) ≤
          centralizer (Z d.radical c : Set (FreeAmalgam d.radical))) :
    ∃ q : CriticalPath d.radical (replacementGeometry h d) c
        (p.walk.getVert (p.walk.length-2)),
      q.walk.getVert 1 = t ∧
      (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
      2 ≤ (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical c) := by
  have hc : color d.radical c = false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hct
    rw [p.start_color] at h1
    cases hc : color d.radical c <;> cases ht : color d.radical t <;> simp_all
  let w : (cosetGraph d.radical).Walk c a :=
    .cons ((cosetGraph_adj d.radical _ _).mpr hct)
      (.cons ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat)) .nil)
  have hw : w.length = 2 := rfl
  have hnear : (cosetGraph d.radical).dist c a ≤ 2 := hw ▸ SimpleGraph.dist_le w
  have hbad : ¬ Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) :=
    fun hh => hnotfixed (trapped_backward_seed_common_kernel_knownSimple
      (e := e) (hz := hz) (hn := hn) hb p hsmall hmove hc hnear hh).1
  let q := p.prepend_two (by exact Nat.le_of_lt (by omega : 2 < replacementDistance h d))
    hc w hw hbad
  have hqt : q.walk.getVert 1 = t := by
    simp only [q,CriticalPath.prepend_two_walk,SimpleGraph.Walk.getVert_append,
      hw,show 1<2 from by decide,ite_true,w,SimpleGraph.Walk.getVert_cons_succ,
      SimpleGraph.Walk.getVert_zero]
  have hover (i : ℕ) (hi : i ≤ p.walk.length-2) :
      q.walk.getVert (i+2) = p.walk.getVert i :=
    p.prepend_two_overlap _ _ _ _ _ hi
  have hqa : q.walk.getVert 2 = a := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (Nat.zero_le _)
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hcent := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hi := critical_start_slice_index_two_le s hcent (by omega) q
  rw [hqa] at hi
  exact ⟨q,hqt,hover,hi⟩


include e hz hn in
/-- Failure of radius escape forces the whole starting radius to centralize
the common reverse kernel, including its central attachment. -/
theorem trapped_radius_common_kernel_knownSimple
    (hb : 4 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hmove : ¬ Q d.radical (p.walk.getVert (p.walk.length-1)) ≤ centralizer
      ((⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) : Set _))
    (htrap : V d.radical a ≤ Q d.radical (p.walk.getVert (p.walk.length-2))) :
    let F := Z d.radical a' ⊓ centralizer
      (componentOrbit (Z d.radical a)
        (Q d.radical (p.walk.getVert (p.walk.length-1))) : Set _)
    F ≤ centralizer (V d.radical a : Set (FreeAmalgam d.radical)) := by
  apply le_centralizer_iff.mpr
  apply (V_le_iff d.radical p.start_color _).mpr
  intro c hc hca
  have hZV : Z d.radical c ≤ V d.radical a :=
    (V_le_iff d.radical p.start_color _).mp le_rfl c hc hca
  exact le_centralizer_iff.mp
    (trapped_backward_seed_common_kernel_knownSimple
      (e := e) (hz := hz) (hn := hn) hb p hsmall hmove hc hca (hZV.trans htrap)).1

include e hz hn in
/-- Noncentrality on the full radius constructs an actual backward critical
path, its first edge and its nontrivial Baumann slice. -/
theorem backward_path_of_radius_kernel_movement_knownSimple
    (hb : 4 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hmove : ¬ Q d.radical (p.walk.getVert (p.walk.length-1)) ≤ centralizer
      ((⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) : Set _))
    (hnotfixed : ¬ (Z d.radical a' ⊓ centralizer
      (componentOrbit (Z d.radical a)
        (Q d.radical (p.walk.getVert (p.walk.length-1))) : Set _)) ≤
          centralizer (V d.radical a : Set (FreeAmalgam d.radical))) :
    ∃ c t, Adjacent d.radical a t ∧ Adjacent d.radical c t ∧
      ∃ q : CriticalPath d.radical (replacementGeometry h d) c
        (p.walk.getVert (p.walk.length-2)),
        q.walk.getVert 1 = t ∧
        (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
        2 ≤ (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical c) := by
  have hescape : ¬ V d.radical a ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) :=
    fun hh => hnotfixed (trapped_radius_common_kernel_knownSimple
      (e := e) (hz := hz) (hn := hn) hb p hsmall hmove hh)
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hcent := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb2
  have hd : (cosetGraph d.radical).dist a (p.walk.getVert (p.walk.length-2)) + 2 =
      (replacementGeometry h d).b d.radical := by
    rw [p.dist_start (Nat.sub_le _ _),p.length_eq_b]
    change replacementDistance h d - 2 + 2 = replacementDistance h d
    omega
  obtain ⟨c,hcol,hca,hcrit⟩ := exists_critical_shift d.radical p.start_color hd hescape
  obtain ⟨w,hw⟩ := (cosetGraph_connected d.radical).exists_walk_length_eq_dist c a
  have hwlen : w.length = 2 := hw.trans hca
  let t := w.getVert 1
  have hct : Adjacent d.radical c t := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      w.adj_getVert_succ (i := 0) (by omega)
  have hat : Adjacent d.radical a t := by
    apply adjacent_symm d.radical
    apply (cosetGraph_adj d.radical _ _).mp
    have hh := w.adj_getVert_succ (i := 1) (by omega)
    simpa only [show 1+1=w.length by omega,SimpleGraph.Walk.getVert_length] using hh
  let q := p.prepend_two (Nat.le_of_lt hb2) hcol w hwlen hcrit.2
  have hqt : q.walk.getVert 1 = t := by
    simp only [q,CriticalPath.prepend_two_walk,SimpleGraph.Walk.getVert_append,
      hwlen,show 1<2 from by decide,ite_true,t]
  have hover (i : ℕ) (hi : i ≤ p.walk.length-2) :
      q.walk.getVert (i+2) = p.walk.getVert i :=
    p.prepend_two_overlap _ _ _ _ _ hi
  have hqa : q.walk.getVert 2 = a := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (Nat.zero_le _)
  refine ⟨c,t,hat,hct,q,hqt,hover,?_⟩
  have hh := critical_start_slice_index_two_le s hcent hb2 q
  rwa [hqa] at hh


include h in
private theorem full_seed_fixer_eq_edge
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) :
    Z d.radical a ⊓ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) =
      Z d.radical t := by
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    cases he : color d.radical t <;> simp_all
  have hZaQ : Z d.radical a ≤ Q d.radical a := by
    apply Z_le_Q_of_dist_lt d.radical _ ((replacementGeometry h d).exists_critical _ ha)
    rw [SimpleGraph.dist_self,(replacementGeometry h d).distance_constant _ ha]
    exact replacementDistance_pos h d
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) a ha
  apply le_antisymm
  · intro x hx
    rw [Z,if_neg (by simp [ht])]
    exact mem_omegaCenter_iff.mpr ⟨(hZaQ.trans (Q_le_adjacent_h d.radical ht hat)) hx.1,
      elemPow_eq_one_of_isElementaryAbelian x hx.1,hx.2⟩
  · apply le_inf (adjacent_Z_le d.radical ha hat)
    intro x hx
    rw [Z,if_neg (by simp [ht])] at hx
    exact (mem_omegaCenter_iff.mp hx).2.2

include e hz hn in
/-- The common full kernel is the critical line times the whole edge
omega seed, with trivial intersection and edge-seed index two. -/
theorem common_kernel_eq_line_sup_edge_seed_knownSimple
    (hb : 4 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hmove : ¬ Q d.radical (p.walk.getVert 1) ≤ centralizer
      ((⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) : Set _)) :
    let D := ⁅Z d.radical a,Z d.radical a'⁆
    let F := Z d.radical a ⊓ centralizer
      (componentOrbit (Z d.radical a') (Q d.radical (p.walk.getVert 1)) : Set _)
    F = D ⊔ Z d.radical (p.walk.getVert 1) ∧
      D ⊓ Z d.radical (p.walk.getVert 1) = ⊥ ∧
      (Z d.radical (p.walk.getVert 1)).relIndex (Z d.radical a) = 8 ∧
      (Z d.radical (p.walk.getVert 1)).relIndex F = 2 := by
  classical
  obtain ⟨x,hx,hxD⟩ := SetLike.not_le_iff_exists.mp hmove
  have hd := line_mover_common_kernel_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall x hx hxD
  have hl : 0 < p.walk.length := p.length_eq_b ▸ replacementDistance_pos h d
  have hat : Adjacent d.radical a (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) hl
  dsimp only at hd ⊢
  rw [full_seed_fixer_eq_edge (h := h) p.start_color hat] at hd
  exact ⟨hd.1,hd.2.1,hd.2.2.1,hd.2.2.2.1⟩



include e hz hn in
/-- The actual restricted original radical and replacement edge give the
same common kernel in the moving-line branch, while retaining their index
two distinction. The whole-kernel decomposition and every subactor estimate
apply through the original embedding. -/
theorem original_radical_common_kernel_knownSimple
    (hb : 4 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hfirst : p.walk.getVert 1 = beta d.radical)
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hmove : ¬ ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical) ≤
      centralizer ((⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ :
        Subgroup (FreeAmalgam d.radical)) : Set _)) :
    let T := ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical)
    let D := ⁅Z d.radical (alpha d.radical),Z d.radical a'⁆
    let F := Z d.radical (alpha d.radical) ⊓ centralizer
      (componentOrbit (Z d.radical a') T : Set (FreeAmalgam d.radical))
    let C := Z d.radical (beta d.radical)
    (Q d.radical (beta d.radical)).relIndex T = 2 ∧
      F = Z d.radical (alpha d.radical) ⊓ centralizer
        (componentOrbit (Z d.radical a') (Q d.radical (beta d.radical)) : Set _) ∧
      F = D ⊔ C ∧ D ⊓ C = ⊥ ∧
      C.relIndex (Z d.radical (alpha d.radical)) = 8 ∧ C.relIndex F = 2 ∧
      ∀ A : Subgroup (FreeAmalgam d.radical), A ≤ Q d.radical (beta d.radical) →
        ⁅F,A⁆ = ⁅D,A⁆ ∧ Nat.card (⁅F,A⁆ : Subgroup (FreeAmalgam d.radical)) ≤ 2 ∧
          ⁅F,A⁆ ≤ Z d.radical (beta d.radical) ∧
          ⁅F,A⁆ ≤ centralizer (Q d.radical (beta d.radical) : Set _) := by
  classical
  have hN := SylowSmallNormalizer.four_lt_base_edge_normalizer_knownSimple
    (e := e) (hz := hz) (hn := hn) hb
  have hfix := critical_line_fixed_iff_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall
  dsimp only at hfix
  rw [hfirst,hN] at hfix
  have hm : ¬ Q d.radical (p.walk.getVert 1) ≤ centralizer
      ((⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ :
        Subgroup (FreeAmalgam d.radical)) : Set _) := by
    rw [hfirst]
    exact fun hh => hmove (hfix.mpr hh)
  have hd := common_kernel_eq_line_sup_edge_seed_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall hm
  have he := edge_orbit_kernel_eq_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall hm
  dsimp only at hd he ⊢
  rw [hfirst] at hd he
  rw [hN] at he
  refine ⟨?_,he.1.symm,he.1.symm.trans hd.1,hd.2.1,hd.2.2.1,?_,?_⟩
  · rw [Q_beta,relIndex_map_map_of_injective _ _ (embedM_injective d.radical)]
    exact (SylowWholeCore.four_lt_original_sylow_eight_image_knownSimple
      (e := e) (hz := hz) (hn := hn) hb).2.2.1
  · rw [←he.1]; exact hd.2.2.2
  · intro A hA
    have hh := common_kernel_subactor_knownSimple
      (e := e) (hz := hz) (hn := hn) hb p hsmall hm A (hfirst.symm ▸ hA)
    dsimp only at hh
    rw [hfirst,he.1] at hh
    exact hh

include e hz hn in
/-- Backward selection with the opposite endpoint at the original embedded
vertex. Its relative-normalizer movement and common-kernel movement on the
whole starting radius produce an actual overlapping critical path. -/
theorem original_radical_backward_path_knownSimple
    (hb : 4 < replacementDistance h d)
    {a : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a (alpha d.radical))
    (hlast : p.walk.getVert (p.walk.length-1) = beta d.radical)
    (hsmall : (Q d.radical (alpha d.radical)).relIndex (Z d.radical a) < 4)
    (hmove : ¬ ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical) ≤
      centralizer ((⁅Z d.radical a,Z d.radical (alpha d.radical)⁆ :
        Subgroup (FreeAmalgam d.radical)) : Set _))
    (hnotfixed : ¬ (Z d.radical (alpha d.radical) ⊓ centralizer
      (componentOrbit (Z d.radical a)
        (((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical)) : Set _)) ≤
          centralizer (V d.radical a : Set (FreeAmalgam d.radical))) :
    ∃ c t, Adjacent d.radical a t ∧ Adjacent d.radical c t ∧
      ∃ q : CriticalPath d.radical (replacementGeometry h d) c
        (p.walk.getVert (p.walk.length-2)),
        q.walk.getVert 1 = t ∧
        (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
        2 ≤ (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical c) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let r : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a := {
    start_color := p.end_color
    walk := p.walk.reverse
    shortest := by rw [SimpleGraph.Walk.length_reverse,p.shortest,SimpleGraph.dist_comm]
    critical := critical_reverse_pair s hc p }
  have hr : r.walk.getVert 1 = beta d.radical :=
    (p.walk.getVert_reverse 1).trans hlast
  have hrs : (Q d.radical a).relIndex (Z d.radical (alpha d.radical)) < 4 := by
    rw [(small_critical_indices s hc p hsmall).2]
    decide
  have hm : ¬ ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical) ≤
      centralizer ((⁅Z d.radical (alpha d.radical),Z d.radical a⁆ :
        Subgroup (FreeAmalgam d.radical)) : Set _) := by
    rwa [commutator_comm]
  have hN := SylowSmallNormalizer.four_lt_base_edge_normalizer_knownSimple
    (e := e) (hz := hz) (hn := hn) hb
  have hfix := critical_line_fixed_iff_knownSimple
    (e := e) (hz := hz) (hn := hn) hb r hrs
  dsimp only at hfix
  rw [hr,hN] at hfix
  have hmT : ¬ Q d.radical (r.walk.getVert 1) ≤ centralizer
      ((⁅Z d.radical (alpha d.radical),Z d.radical a⁆ :
        Subgroup (FreeAmalgam d.radical)) : Set _) := by
    rw [hr]
    exact fun hh => hm (hfix.mpr hh)
  have he := (edge_orbit_kernel_eq_knownSimple
    (e := e) (hz := hz) (hn := hn) hb r hrs hmT).1
  rw [hr,hN] at he
  apply backward_path_of_radius_kernel_movement_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall
  · rwa [hlast,←hr,commutator_comm]
  · rw [hlast,he]
    exact hnotfixed


end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EightBackwardKernel
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

