module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.ElementaryKernelControl
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowPairedFixer
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeKernelChoice

/-!
# Excluding the paired trapped alternative

In the image-sixteen branch above distance four, the compatible equal-mover
pair cannot have both backward seeds trapped. Their join with the starting
seed is elementary abelian because it lies in the abelian radius. Its full
endpoint displacement is not controlled by the critical line and its kernel
displacement: that would normalize the forbidden selected span. The two-cover
kernel bound therefore gives one subgroup of order at most two containing
both nonzero selected kernel commutators. They coincide, so the paired
intersection estimate makes this common subgroup fixed by the whole starting
stabilizer. Transport by the inverse residual conjugator then bounds joint
movement on both full kernels by two, contradicting the strict-slice bound.

The consumer retains the same selected edge, residual conjugator, both full
critical walks, both neighbor candidates and the original radical embedding.
It produces one of the two overlapping backward critical paths with no new
hypothesis. Both moving covers and all central attachments are retained.
This excludes the trapped alternative in this equal-mover branch; the other
image, unequal-mover and distance-four cases are separate obligations.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.3)(ii)(2) and (5.7), printed pp.866--867 and 919.
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
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

omit [Finite G] in
private theorem neighbor_seed_le_radius {a c t : Vertex d.radical}
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t) :
    Z d.radical c ≤ V d.radical a := by
  have hdist : (cosetGraph d.radical).dist c a ≤ 2 := by
    have h1 : (cosetGraph d.radical).dist c t = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hct)
    have h2 : (cosetGraph d.radical).dist t a = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr
        ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat))
    simpa only [h1,h2] using (cosetGraph_connected d.radical).dist_triangle
      (u := c) (v := t) (w := a)
  exact (Z_le_localZSpan d.radical _ _).trans (localZSpan_le_V d.radical hdist)

include s in
private theorem critical_full_kernel_eq (hc : DistanceTwo.CentralLayer d)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z) :
    Z d.radical z ⊓ Q d.radical a =
      Z d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) := by
  apply le_antisymm
  · exact inf_le_inf_left _ (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical a p.start_color)))
  · intro x hx
    refine ⟨hx.1,?_⟩
    rw [←C_eq_Q s hc a p.start_color]
    exact ⟨critical_Z_le_stabilizer d.radical (replacementGeometry h d) a p.start_color
      (by rw [(replacementGeometry h d).distance_constant a p.start_color]
          exact replacementDistance_pos h d) p.critical hx.1,hx.2⟩

include s in
private theorem nonnormalizing_seed_kernel_ne_bot (hc : DistanceTwo.CentralLayer d)
    (hb : 2 < replacementDistance h d) {a z c : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (hCV : Z d.radical c ≤ V d.radical a)
    (hCG : Z d.radical c ≤ stabilizer d.radical z)
    (hnorm : ¬ Z d.radical z ≤ normalizer
      ((Z d.radical c ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) :
        Set (FreeAmalgam d.radical))) :
    ⁅Z d.radical c,Z d.radical z ⊓ Q d.radical a⁆ ≠ ⊥ := by
  intro hzero
  have hmove := small_critical_kernel_commutator s hc p hsmall (Z d.radical c) hCG
    (commutator_eq_bot_iff_le_centralizer.mp hzero)
  have hcrit : ⁅Z d.radical a,Z d.radical z⁆ ≤ Z d.radical a :=
    ((critical_Z_commutator_le_moving (h := h) p).trans inf_le_left).trans
      (DistanceEight.U_le_Z d.radical a)
  have htotal := commutator_sup_le_of_relative_normal (stabilizer d.radical a)
    (Z d.radical c) (Z d.radical a) (Z d.radical z) (Z d.radical a)
    (Z_normalized d.radical a)
    (hCV.trans ((replacementGeometry h d).V_local a p.start_color (by
      rw [(replacementGeometry h d).distance_constant a p.start_color]; exact hb)))
    (Z_le_stabilizer d.radical a) (hmove.trans hcrit) hcrit
  exact hnorm (le_normalizer_iff_commutator_le_left.mpr (htotal.trans le_sup_right))

include s in
private theorem combined_actor_kernel_card_le_two (hc : DistanceTwo.CentralLayer d)
    (hb : 2 < replacementDistance h d) {a z c : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (P : Subgroup (FreeAmalgam d.radical)) (hel : IsElementaryAbelian 2 P)
    (hAP : Z d.radical a ≤ P) (hCP : Z d.radical c ≤ P)
    (hCV : Z d.radical c ≤ V d.radical a)
    (hPt : P ≤ Q d.radical (p.walk.getVert (p.walk.length-1)))
    (hK : ⁅P,Z d.radical z ⊓ Q d.radical a⁆ ≤ Z d.radical a)
    (hnorm : ¬ Z d.radical z ≤ normalizer
      ((Z d.radical c ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) :
        Set (FreeAmalgam d.radical))) :
    Nat.card (⁅P,Z d.radical z ⊓ Q d.radical a⁆ : Subgroup (FreeAmalgam d.radical)) ≤ 2 := by
  have hlast := critical_last_edge_inputs (h := h) hb p
  have hfixed := critical_full_kernel_eq s hc p
  let := finite_Z d.radical z
  let : Finite (U d.radical z) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z d.radical z)) (inclusion_injective _)
  have hindex : (centralizer (Z d.radical a : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical z) ≤ 2 := by
    have hQC : Q d.radical a ≤ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical a p.start_color))
    exact ((relIndex_le_of_le_left hQC index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (DistanceEight.U_le_Z d.radical z) index_ne_zero_of_finite)).trans_eq
        (small_critical_indices s hc p hsmall).2
  have hcrit : ⁅Z d.radical a,Z d.radical z⁆ ≤ Z d.radical a :=
    ((critical_Z_commutator_le_moving (h := h) p).trans inf_le_left).trans
      (DistanceEight.U_le_Z d.radical a)
  have hfail : ¬ ⁅Z d.radical z,P⁆ ≤
      ⁅Z d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)),P⁆ ⊔
        ⁅Z d.radical z,Z d.radical a⁆ := by
    intro hh
    rw [←hfixed,commutator_comm (Z d.radical z ⊓ Q d.radical a) P,
      commutator_comm (Z d.radical z) (Z d.radical a)] at hh
    have hmove : ⁅Z d.radical c,Z d.radical z⁆ ≤ Z d.radical a := by
      rw [commutator_comm]
      exact (commutator_mono le_rfl hCP).trans (hh.trans (sup_le hK hcrit))
    have htotal := commutator_sup_le_of_relative_normal (stabilizer d.radical a)
      (Z d.radical c) (Z d.radical a) (Z d.radical z) (Z d.radical a)
      (Z_normalized d.radical a)
      (hCV.trans ((replacementGeometry h d).V_local a p.start_color (by
        rw [(replacementGeometry h d).distance_constant a p.start_color]; exact hb)))
      (Z_le_stabilizer d.radical a) hmove hcrit
    exact hnorm (le_normalizer_iff_commutator_le_left.mpr (htotal.trans le_sup_right))
  have hh := (elementary_edge_kernel_small_aligned s hc p.end_color hlast.1
    (Z d.radical a) P hlast.2.2 hPt hAP hel p.critical.2 hindex hfail).1
  rwa [←hfixed,commutator_comm] at hh

include e hz hn in
private theorem paired_traps_impossible
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a z c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hequal : SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4 =
      SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4)
    (x : FreeAmalgam d.radical) (hx : x ∈ stabilizer d.radical a)
    (q : CriticalPath d.radical (replacementGeometry h d) a (act d.radical x z))
    (hq : ∀ i, q.walk.getVert i = act d.radical x (p.walk.getVert i))
    (hqs : (Q d.radical (act d.radical x z)).relIndex (Z d.radical a) < 4)
    (hgen : SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4 ⊔
      Z d.radical z ⊔ Z d.radical (act d.radical x z) = stabilizer d.radical a)
    (hpair : SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4 ⊔
      (SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4).map
        (MulAut.conj x).toMonoidHom = stabilizer d.radical a)
    (hpbad : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    (hqbad : Z d.radical c ≤ Q d.radical (q.walk.getVert (q.walk.length-2)))
    (hnorm : ¬ Z d.radical z ≤ normalizer
      ((Z d.radical c ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) :
        Set (FreeAmalgam d.radical)))
    (hnorm₂ : ¬ Z d.radical z ≤ normalizer
      ((Z d.radical (act d.radical x⁻¹ c) ⊔ Z d.radical a :
        Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)))
    (hindex : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c)) : False := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let F := Z d.radical z ⊓ Q d.radical a
  let F₂ := Z d.radical (act d.radical x z) ⊓ Q d.radical a
  let C₂ := Z d.radical (act d.radical x⁻¹ c)
  let P := Z d.radical a ⊔ Z d.radical c ⊔ C₂
  let K := ⁅P,F⁆
  have hQa : (Q d.radical a).map (MulAut.conj x).toMonoidHom = Q d.radical a :=
    mem_normalizer_iff_map_conj_eq.mp (Q_normalized d.radical a hx)
  have hZa : (Z d.radical a).map (MulAut.conj x).toMonoidHom = Z d.radical a :=
    mem_normalizer_iff_map_conj_eq.mp (Z_normalized d.radical a hx)
  have hC₂ : C₂ = (Z d.radical c).map (MulAut.conj x).toMonoidHom := by
    simp only [C₂,Z_act,inv_inv]
  have hCV := neighbor_seed_le_radius hat hct
  have hC₂V : C₂ ≤ V d.radical a := by
    have hh := map_mono (f := (MulAut.conj x).toMonoidHom) hCV
    have he : (V d.radical a).map (MulAut.conj x).toMonoidHom = V d.radical a :=
      mem_normalizer_iff_map_conj_eq.mp (DistanceEight.V_normalized d.radical a hx)
    rwa [←hC₂,he] at hh
  have hAV : Z d.radical a ≤ V d.radical a := Z_le_VBall d.radical a 2
  have hVG := (replacementGeometry h d).V_local a p.start_color (by
    rw [(replacementGeometry h d).distance_constant a p.start_color]; exact hb2)
  have hlast := critical_last_edge_inputs (h := h) hb2 p
  have hC₂pre : C₂ ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) := by
    have hh := map_mono (f := (MulAut.conj x).toMonoidHom) hqbad
    have hlen : q.walk.length = p.walk.length := q.length_eq_b.trans p.length_eq_b.symm
    rw [hlen,hq] at hh
    have he := Q_act d.radical x⁻¹ (act d.radical x (p.walk.getVert (p.walk.length-2)))
    simp only [inv_inv,←act_mul,mul_inv_cancel,act_one] at he
    rwa [←hC₂,←he] at hh
  have hPt : P ≤ Q d.radical (p.walk.getVert (p.walk.length-1)) :=
    sup_le (sup_le hlast.2.2 (hpbad.trans hlast.2.1)) (hC₂pre.trans hlast.2.1)
  have hpreG : Q d.radical (p.walk.getVert (p.walk.length-2)) ≤ stabilizer d.radical z :=
    hlast.2.1.trans (fun _ hv => hv.2 _ (adjacent_symm d.radical hlast.1))
  have hXz := (SylowPairedFixer.trapped_nonnormalized_full_kernel_knownSimple
    (e := e) (hz := hz) (hn := hn) hb2 p hsmall hat hct hpbad hnorm).1
  have hXa := SylowPairedFixer.central_generation_eq_seed (h := h) p.start_color hat
    (X_central_generation_all p.end_color hXz a p.start_color)
  have hcontrol := SylowPairedFixer.equal_mover_pair_control
    (e := e) (hz := hz) (hn := hn) hb hcard p.start_color hat hct hequal hXa x hx hpair
    (Q d.radical a) le_rfl
  have hC₂Q : ⁅C₂,Q d.radical a⁆ ≤ Z d.radical a := by
    have hh := map_mono (f := (MulAut.conj x).toMonoidHom) hcontrol.1
    rwa [map_commutator,←hC₂,hQa,hZa] at hh
  have hK : K ≤ Z d.radical a := by
    apply commutator_sup_le_of_relative_normal (stabilizer d.radical a)
      (Z d.radical a ⊔ Z d.radical c) C₂ F (Z d.radical a)
      (Z_normalized d.radical a) ((sup_le hAV hCV).trans hVG) (hC₂V.trans hVG)
    · apply commutator_sup_le_of_relative_normal (stabilizer d.radical a)
        (Z d.radical a) (Z d.radical c) F (Z d.radical a)
        (Z_normalized d.radical a) (Z_le_stabilizer d.radical a) (hCV.trans hVG)
      · exact (commutator_mono le_rfl inf_le_right).trans_eq
          (Z_centralizes_Q d.radical a p.start_color) |>.trans bot_le
      · exact (commutator_mono le_rfl inf_le_right).trans hcontrol.1
    · exact (commutator_mono le_rfl inf_le_right).trans hC₂Q
  have hcol : color d.radical c = false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hct
    rw [p.start_color] at h1
    cases hc : color d.radical c <;> cases ht : color d.radical t <;> simp_all
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) a p.start_color
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) c hcol
  let : IsElementaryAbelian 2 C₂ := hC₂ ▸ IsElementaryAbelian.map (MulAut.conj x).toMonoidHom
  have hVV : V d.radical a ≤ centralizer (V d.radical a : Set (FreeAmalgam d.radical)) :=
    le_centralizer_iff_isMulCommutative.mpr (V_abelian_of_four_lt d.radical p.start_color hb)
  let : IsElementaryAbelian 2 (Z d.radical a ⊔ Z d.radical c : Subgroup (FreeAmalgam d.radical)) :=
    IsElementaryAbelian.sup_of_le_centralizer (hCV.trans (hVV.trans (centralizer_le hAV)))
  have hel : IsElementaryAbelian 2 P := IsElementaryAbelian.sup_of_le_centralizer
    (hC₂V.trans (hVV.trans (centralizer_le (sup_le hAV hCV))))
  have hbound : Nat.card K ≤ 2 := combined_actor_kernel_card_le_two s hc hb2 p hsmall
    P hel (le_sup_left.trans le_sup_left) (le_sup_right.trans le_sup_left) hCV hPt hK hnorm
  have hne₁ := nonnormalizing_seed_kernel_ne_bot s hc hb2 p hsmall hCV
    (hpbad.trans hpreG) hnorm
  have hne₂ := nonnormalizing_seed_kernel_ne_bot s hc hb2 p hsmall hC₂V
    (hC₂pre.trans hpreG) hnorm₂
  have h₁ : ⁅Z d.radical c,F⁆ ≤ K := commutator_mono (le_sup_right.trans le_sup_left) le_rfl
  have h₂ : ⁅C₂,F⁆ ≤ K := commutator_mono le_sup_right le_rfl
  let := finite_Z d.radical a
  let : Finite K := Finite.of_injective (inclusion hK) (inclusion_injective _)
  let : Finite (⁅Z d.radical c,F⁆ : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion h₁) (inclusion_injective _)
  let : Finite (⁅C₂,F⁆ : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion h₂) (inclusion_injective _)
  have hpos₁ : 1 < Nat.card (⁅Z d.radical c,F⁆ : Subgroup (FreeAmalgam d.radical)) :=
    (one_lt_card_iff_ne_bot _).mpr hne₁
  have hpos₂ : 1 < Nat.card (⁅C₂,F⁆ : Subgroup (FreeAmalgam d.radical)) :=
    (one_lt_card_iff_ne_bot _).mpr hne₂
  have heq₁ : ⁅Z d.radical c,F⁆ = K := eq_of_le_of_card_ge h₁ (by omega)
  have heq₂ : ⁅C₂,F⁆ = K := eq_of_le_of_card_ge h₂ (by omega)
  have hcentral : K ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
    have hh := (SylowPairedFixer.equal_mover_pair_control
      (e := e) (hz := hz) (hn := hn) hb hcard p.start_color hat hct hequal hXa x hx hpair F inf_le_right).2
    change ⁅Z d.radical c,F⁆ ⊓ ⁅C₂,F⁆ ≤ _ at hh
    rw [heq₁,heq₂,inf_idem] at hh
    exact hh.trans inf_le_right
  have hMK : stabilizer d.radical a ≤ normalizer (K : Set (FreeAmalgam d.radical)) :=
    (le_centralizer_iff.mp hcentral).trans (Subgroup.centralizer_le_normalizer _)
  have hmapK : K.map (MulAut.conj x⁻¹).toMonoidHom = K :=
    mem_normalizer_iff_map_conj_eq.mp (hMK ((stabilizer d.radical a).inv_mem hx))
  have hmapC : C₂.map (MulAut.conj x⁻¹).toMonoidHom = Z d.radical c := by
    dsimp only [C₂]
    rw [←Z_act,←act_mul,inv_mul_cancel,act_one]
  have hmapF : F.map (MulAut.conj x⁻¹).toMonoidHom = F₂ := by
    have he : (Q d.radical a).map (MulAut.conj x⁻¹).toMonoidHom = Q d.radical a :=
      mem_normalizer_iff_map_conj_eq.mp (Q_normalized d.radical a ((stabilizer d.radical a).inv_mem hx))
    dsimp only [F,F₂]
    rw [Subgroup.map_inf _ _ _ (MulAut.conj x⁻¹).injective,←Z_act,he]
  have heq₃ : ⁅Z d.radical c,F₂⁆ = K := by
    have hh := congrArg (Subgroup.map (MulAut.conj x⁻¹).toMonoidHom) heq₂
    rwa [map_commutator,hmapC,hmapF,hmapK] at hh
  have hjoin : ⁅F ⊔ F₂,Z d.radical c⁆ ≤ K :=
    commutator_sup_le_of_relative_normal (stabilizer d.radical a) F F₂ (Z d.radical c) K
      hMK (inf_le_right.trans (show Q d.radical a ≤ stabilizer d.radical a from fun _ hv => hv.1))
      (inf_le_right.trans (show Q d.radical a ≤ stabilizer d.radical a from fun _ hv => hv.1))
      (by rw [commutator_comm]; exact heq₁.le) (by rw [commutator_comm]; exact heq₃.le)
  have hU : ⁅U d.radical c,F ⊔ F₂⁆ ≤ K := by
    rw [commutator_comm] at hjoin
    exact (commutator_mono (DistanceEight.U_le_Z d.radical c) le_rfl).trans hjoin
  have hlarge := SylowPairedFixer.sixteen_paired_trapped_joint_movement_gt_two_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard p q hsmall hqs hat hct hequal hgen hpbad hqbad hindex
  exact (Nat.not_le_of_gt hlarge) ((card_le_of_le hU).trans hbound)

include e hz hn in
/-- The compatible equal-mover pair has an actual overlapping backward critical
path. The two trapped alternatives are excluded on the same selected pair,
without changing its residual transporter or original-radical embedding. -/
theorem sixteen_equal_mover_strict_backward_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {z delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4)
    (hdelta : Adjacent d.radical delta (p.walk.getVert 1))
    (hequal : SmallMover.join (U d.radical delta) (Q d.radical delta)
        (Q d.radical (p.walk.getVert 1)) 4 =
      SmallMover.join (U d.radical (alpha d.radical)) (Q d.radical (alpha d.radical))
        (Q d.radical (p.walk.getVert 1)) 4)
    (hstrict : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical delta)) :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      ∃ g ∈ stabilizer d.radical (alpha d.radical),
        act d.radical g (p.walk.getVert 1) = t ∧
        Adjacent d.radical (act d.radical g delta) t ∧
        2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical (act d.radical g delta)) ∧
        ∃ x ∈ Ltilde d.radical (alpha d.radical),
          x^3 ∈ Q d.radical (alpha d.radical) ∧
          ∃ q : CriticalPath d.radical (replacementGeometry h d)
              (alpha d.radical) (act d.radical x z),
            (∀ i, q.walk.getVert i = act d.radical x (p.walk.getVert i)) ∧
            (Q d.radical (act d.radical x z)).relIndex (Z d.radical (alpha d.radical)) < 4 ∧
            let c := act d.radical g delta
            let J := SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4
            J = SmallMover.join (U d.radical (alpha d.radical))
              (Q d.radical (alpha d.radical)) (Q d.radical t) 4 ∧
            Q d.radical t ⊔ Z d.radical z = stabilizer d.radical (alpha d.radical) ∧
            Q d.radical t ⊔ Z d.radical (act d.radical x z) = stabilizer d.radical (alpha d.radical) ∧
            J ⊔ Z d.radical z ⊔ Z d.radical (act d.radical x z) = stabilizer d.radical (alpha d.radical) ∧
            J ⊔ J.map (MulAut.conj x).toMonoidHom = stabilizer d.radical (alpha d.radical) ∧
            (Z d.radical (alpha d.radical) ⊓ centralizer (J : Set (FreeAmalgam d.radical))) ⊓
              centralizer (J.map (MulAut.conj x).toMonoidHom : Set (FreeAmalgam d.radical)) =
              Z d.radical (alpha d.radical) ⊓
                centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) ∧
            ¬ Z d.radical z ≤ normalizer ((Z d.radical c ⊔ Z d.radical (alpha d.radical) :
              Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) ∧
            ¬ Z d.radical (act d.radical x z) ≤ normalizer
              ((Z d.radical c ⊔ Z d.radical (alpha d.radical) : Subgroup (FreeAmalgam d.radical)) :
                Set (FreeAmalgam d.radical)) ∧
            Adjacent d.radical (alpha d.radical) (act d.radical x⁻¹ t) ∧
            Adjacent d.radical (act d.radical x⁻¹ c) (act d.radical x⁻¹ t) ∧
            2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
              (U d.radical (act d.radical x⁻¹ c)) ∧
            J.map (MulAut.conj x).toMonoidHom =
              SmallMover.join (U d.radical (act d.radical x⁻¹ c))
                (Q d.radical (act d.radical x⁻¹ c)) (Q d.radical (act d.radical x⁻¹ t)) 4 ∧
            Q d.radical (act d.radical x⁻¹ t) ⊔ Z d.radical z = stabilizer d.radical (alpha d.radical) ∧
            ¬ Z d.radical z ≤ normalizer
              ((Z d.radical (act d.radical x⁻¹ c) ⊔ Z d.radical (alpha d.radical) :
                Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) ∧
            (let T := ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical)
             ∃ r ∈ stabilizer d.radical (alpha d.radical),
               T.map (MulAut.conj r⁻¹).toMonoidHom = Q d.radical t ∧
               (SmallMover.join (U d.radical (alpha d.radical)) (Q d.radical (alpha d.radical))
                 T 4).map (MulAut.conj r⁻¹).toMonoidHom = J) ∧
            ((∃ b : CriticalPath d.radical (replacementGeometry h d)
                c (p.walk.getVert (p.walk.length-2)),
                b.walk.getVert 1 = t ∧
                ∀ i ≤ p.walk.length-2, b.walk.getVert (i+2) = p.walk.getVert i) ∨
             (∃ b : CriticalPath d.radical (replacementGeometry h d)
                c (q.walk.getVert (q.walk.length-2)),
                b.walk.getVert 1 = t ∧
                ∀ i ≤ q.walk.length-2, b.walk.getVert (i+2) = q.walk.getVert i)) := by
  obtain ⟨t,hat,g,hg,hgt,hct,hi,x,hx,hx3,q,hq,hqs,heq,hgen₀,hgen₁,hgen,hpair,hfix,
    hn₀,hn₁,hat₂,hct₂,hi₂,hJ₂,hgen₂,hn₂,hOriginal,halt⟩ :=
    SylowPairedFixer.sixteen_equal_mover_strict_kernel_alternative_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hcard p hsmall hdelta hequal hstrict
  refine ⟨t,hat,g,hg,hgt,hct,hi,x,hx,hx3,q,hq,hqs,heq,hgen₀,hgen₁,hgen,hpair,hfix,
    hn₀,hn₁,hat₂,hct₂,hi₂,hJ₂,hgen₂,hn₂,hOriginal,?_⟩
  rcases halt with hp | hq' | htrap
  · exact Or.inl hp
  · exact Or.inr hq'
  · exact (paired_traps_impossible (e := e) (hz := hz) (hn := hn) hb hcard p hsmall
      hat hct heq x (Ltilde_le_stabilizer _ hx) q hq hqs hgen hpair
      htrap.1 htrap.2.1 hn₀ hn₂ hi).elim

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
