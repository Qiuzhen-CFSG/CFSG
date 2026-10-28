module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowForwardKernel
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowSixteenEscape
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeSpanCollapse
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowSpanSelection
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeFullKernel

import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTrappedExclusion

import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeSpanCollapse

/-!
# Endpoint control for all shifted normal sections

Each conjugate section is elementary, even when its whole orbit span is not.
A nonzero seed-kernel commutator has order two and the section escapes it,
forcing endpoint control. If the seed-kernel commutator is zero, the kernel
lies in the conjugate source centralizer T; its section displacement lies in
H. Since H has order two and is moved by the endpoint, that displacement is
zero. The exact critical-kernel centralizer then gives endpoint control.
Relative normal generation assembles the controls on the whole orbit span.
The literal image-sixteen application collapses that span, contradicts a
forward slice of index at most two and supplies a strict backward shift at
every component vertex. The original-radical consumer preserves both subgroup
maps and the transporter. Both moving covers and central attachments remain.
The large critical-image, terminal and distance-four branches remain open.

Source: MS93 (3.3), (5.9), printed pp.866--867,920--922.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped commutatorElement IsMulCommutative Pointwise
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u

variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)


namespace SylowForwardSpan
open SylowForwardKernel
include s

/-- Every conjugate normal section is controlled, including the zero seed-kernel case. -/
theorem conjugate_section_control
    (hc : DistanceTwo.CentralLayer d) (hb : 4 < replacementDistance h d)
    {c z a : Vertex d.radical}
    (q : CriticalPath d.radical (replacementGeometry h d) c z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical c) < 4)
    (ha : color d.radical a = false) (hca : (cosetGraph d.radical).dist c a ≤ 2)
    (Y H P : Subgroup (FreeAmalgam d.radical))
    (hYV : Y ≤ V d.radical a)
    (hYN : stabilizer d.radical a ≤ normalizer (Y : Set (FreeAmalgam d.radical)))
    (hYB : ¬ Y ≤ B d.radical a ((replacementGeometry h d).Z_normal _))
    (hZaY : Z d.radical a ≤ Y) (hZcY : Z d.radical c ≤ Y)
    (hPG : P ≤ stabilizer d.radical c) (hPH : P ≤ centralizer (H : Set (FreeAmalgam d.radical)))
    (hHcard : Nat.card H = 2) (hmove : ¬ H ≤ centralizer (Z d.radical z : Set (FreeAmalgam d.radical)))
    (hcomm : ⁅Y,Q d.radical a ⊓ centralizer
      (U d.radical c ⊓ B d.radical a ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))⁆ ≤ H)
    (hDcard : Nat.card (⁅conjugateSpanBy (Z d.radical a) P,Z d.radical z ⊓ Q d.radical c⁆ :
      Subgroup (FreeAmalgam d.radical)) = 2)
    (hWpre : conjugateSpanBy Y P ≤ Q d.radical (q.walk.getVert (q.walk.length-2)))
    (x : P) :
    let Yx := Y.map (MulAut.conj (x : FreeAmalgam d.radical)).toMonoidHom
    ⁅Yx,Z d.radical z⁆ ≤ ⁅Yx,Z d.radical z ⊓ Q d.radical c⁆ ⊔ ⁅Z d.radical c,Z d.radical z⁆ := by
  let K := Z d.radical z ⊓ Q d.radical c
  let f := (MulAut.conj (x : FreeAmalgam d.radical)).toMonoidHom
  let fi := (MulAut.conj (x : FreeAmalgam d.radical)⁻¹).toMonoidHom
  let Yx := Y.map f
  let J := ⁅(Z d.radical a).map f,K⁆
  let E := ⁅Yx,K⁆
  let D := conjugateSpanBy (Z d.radical a) P
  have hxG := hPG x.property
  have hYxW : Yx ≤ conjugateSpanBy Y P := by
    rw [conjugateSpanBy_eq_iSup_conj]
    exact le_iSup (fun k : P => Y.map (MulAut.conj (k : FreeAmalgam d.radical)).toMonoidHom) x
  have hZxD : (Z d.radical a).map f ≤ D := by
    rw [show D = conjugateSpanBy (Z d.radical a) P from rfl,conjugateSpanBy_eq_iSup_conj]
    exact le_iSup (fun k : P => (Z d.radical a).map
      (MulAut.conj (k : FreeAmalgam d.radical)).toMonoidHom) x
  have hedge := critical_last_edge_inputs (h := h) (by omega : 2 < replacementDistance h d) q
  have hYxt := (hYxW.trans hWpre).trans hedge.2.1
  have hYxz : Yx ≤ stabilizer d.radical z :=
    hYxt.trans (fun _ hx => hx.2 _ (adjacent_symm d.radical hedge.1))
  have hEZ : E ≤ Z d.radical z := by
    rw [show E = ⁅Yx,K⁆ from rfl,commutator_comm]
    exact (commutator_mono inf_le_left le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp (hYxz.trans (Z_normalized d.radical z)))
  let := finite_Z d.radical z
  let : Finite E := Finite.of_injective (inclusion hEZ) (inclusion_injective _)
  have hJE : J ≤ E := commutator_mono (map_mono hZaY) le_rfl
  let : Finite J := Finite.of_injective (inclusion hJE) (inclusion_injective _)
  have hZcYx : Z d.radical c ≤ Yx := by
    exact (mem_normalizer_iff_map_conj_eq.mp (Z_normalized d.radical c hxG)).symm.le.trans
      (map_mono hZcY)
  have hfixed := critical_full_kernel_eq s hc q
  by_cases hJ : J = ⊥
  · let A := K.map fi
    have hAf : A.map f = K := by
      rw [map_map]
      have he : f.comp fi = MonoidHom.id (FreeAmalgam d.radical) := by
        apply MonoidHom.ext
        intro v
        change (x : FreeAmalgam d.radical)*((x : FreeAmalgam d.radical)⁻¹*v*
          ((x : FreeAmalgam d.radical)⁻¹)⁻¹)*(x : FreeAmalgam d.radical)⁻¹ = v
        group
      rw [he,map_id]
    have hAQc : A ≤ Q d.radical c := (map_mono (show K ≤ Q d.radical c from inf_le_right)).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp
        (Q_normalized d.radical c ((stabilizer d.radical c).inv_mem hxG)))
    have hAGa : A ≤ stabilizer d.radical a := hAQc.trans
      (Q_le_stabilizer_of_dist_le_two c a q.start_color ha hca)
    have hzero : ⁅Z d.radical a,A⁆ = ⊥ := by
      apply (map_injective (f := f) (MulAut.conj (x : FreeAmalgam d.radical)).injective)
      rw [map_commutator,hAf,Subgroup.map_bot]
      exact hJ
    have hAQa : A ≤ Q d.radical a := by
      rw [←C_eq_Q s hc a ha]
      exact le_inf hAGa (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hzero))
    have hAT : A ≤ Q d.radical a ⊓ centralizer
        (U d.radical c ⊓ B d.radical a ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical)) :=
      le_inf hAQa ((hAQc.trans (le_centralizer_iff.mp
        (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical c q.start_color)))).trans
          (centralizer_le (inf_le_left.trans (DistanceEight.U_le_Z d.radical c))))
    have hEH : E ≤ H := by
      have hh := map_mono (f := f) ((commutator_mono le_rfl hAT).trans hcomm)
      rw [map_commutator,hAf] at hh
      have hHmap : H.map f = H := mem_normalizer_iff_map_conj_eq.mp
        (Subgroup.centralizer_le_normalizer _ (hPH x.property))
      exact hh.trans_eq hHmap
    have hEbot : E = ⊥ := by
      by_contra hn
      have hpos := (one_lt_card_iff_ne_bot E).mpr hn
      let : Finite H := Nat.finite_of_card_ne_zero (by omega)
      have he : E = H := eq_of_le_of_card_ge hEH (by omega)
      have hHZ := he ▸ hEZ
      let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) z q.end_color
      exact hmove (hHZ.trans (le_centralizer_iff_isMulCommutative.mpr inferInstance))
    exact (small_critical_kernel_commutator s hc q hsmall Yx hYxz
      (commutator_eq_bot_iff_le_centralizer.mp hEbot)).trans le_sup_right
  · have hDfinite : Finite (⁅D,K⁆ : Subgroup (FreeAmalgam d.radical)) :=
      Nat.finite_of_card_ne_zero (by change Nat.card (⁅D,K⁆ : Subgroup (FreeAmalgam d.radical)) = 2 at hDcard; omega)
    let := hDfinite
    have hJle : J ≤ ⁅D,K⁆ := commutator_mono hZxD le_rfl
    have hJcard : Nat.card J = 2 := by
      have hpos := (one_lt_card_iff_ne_bot J).mpr hJ
      have hbound := card_le_of_le hJle
      change Nat.card (⁅D,K⁆ : Subgroup (FreeAmalgam d.radical)) = 2 at hDcard
      omega
    have hnot := predecessor_kernel_displacement_escape s (by omega : 2 < replacementDistance h d)
      q ha hca Y hYV hYN hYB x hxG hJ
    by_contra hfail
    have hfail' : ¬ ⁅Z d.radical z,Yx⁆ ≤
        ⁅Z d.radical z ⊓ centralizer (Z d.radical c : Set (FreeAmalgam d.radical)),Yx⁆ ⊔
          ⁅Z d.radical z,Z d.radical c⁆ := by
      simpa only [←hfixed,commutator_comm (Z d.radical z) Yx,commutator_comm (Z d.radical z ⊓ Q d.radical c) Yx,
        commutator_comm (Z d.radical z) (Z d.radical c)] using hfail
    have hQC : Q d.radical c ≤ centralizer (Z d.radical c : Set (FreeAmalgam d.radical)) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical c q.start_color))
    let : Finite (U d.radical z) := Finite.of_injective
      (inclusion (DistanceEight.U_le_Z d.radical z)) (inclusion_injective _)
    have hindex : (centralizer (Z d.radical c : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical z) ≤ 2 :=
      ((relIndex_le_of_le_left hQC index_ne_zero_of_finite).trans
        (relIndex_le_of_le_right (DistanceEight.U_le_Z d.radical z) index_ne_zero_of_finite)).trans_eq
          (small_critical_indices s hc q hsmall).2
    let := V_elementary_of_four_lt d.radical ha hb
    let : IsElementaryAbelian 2 Y := IsElementaryAbelian.of_le hYV
    have hel : IsElementaryAbelian 2 Yx := IsElementaryAbelian.map f
    have hh := (elementary_edge_kernel_small_aligned s hc q.end_color hedge.1
      (Z d.radical c) Yx hedge.2.2 hYxt hZcYx hel q.critical.2 hindex hfail').1
    rw [←hfixed,commutator_comm] at hh
    have he : J = E := eq_of_le_of_card_ge hJE (by change Nat.card E ≤ 2 at hh; omega)
    exact hnot he.symm.le

/-- Control on the individual elementary sections controls their whole orbit span
and collapses it, without asserting that the whole span is elementary. -/
theorem shifted_span_collapse
    (hc : DistanceTwo.CentralLayer d) (hb : 4 < replacementDistance h d)
    {c z a : Vertex d.radical}
    (q : CriticalPath d.radical (replacementGeometry h d) c z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical c) < 4)
    (ha : color d.radical a = false) (hca : (cosetGraph d.radical).dist c a ≤ 2)
    (Y H P : Subgroup (FreeAmalgam d.radical))
    (hYV : Y ≤ V d.radical a)
    (hYN : stabilizer d.radical a ≤ normalizer (Y : Set (FreeAmalgam d.radical)))
    (hYB : ¬ Y ≤ B d.radical a ((replacementGeometry h d).Z_normal _))
    (hZaY : Z d.radical a ≤ Y) (hZcY : Z d.radical c ≤ Y)
    (hPG : P ≤ stabilizer d.radical c) (hPH : P ≤ centralizer (H : Set (FreeAmalgam d.radical)))
    (hgen : P ⊔ Z d.radical z = stabilizer d.radical c)
    (hHcard : Nat.card H = 2) (hmove : ¬ H ≤ centralizer (Z d.radical z : Set (FreeAmalgam d.radical)))
    (hcomm : ⁅Y,Q d.radical a ⊓ centralizer
      (U d.radical c ⊓ B d.radical a ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))⁆ ≤ H)
    (hDcard : Nat.card (⁅conjugateSpanBy (Z d.radical a) P,Z d.radical z ⊓ Q d.radical c⁆ :
      Subgroup (FreeAmalgam d.radical)) = 2)
    (hWpre : conjugateSpanBy Y P ≤ Q d.radical (q.walk.getVert (q.walk.length-2))) :
    let W := conjugateSpanBy Y P
    stabilizer d.radical c ≤ normalizer (W : Set (FreeAmalgam d.radical)) ∧
      ⁅W,Z d.radical z⁆ ≤ ⁅W,Z d.radical z ⊓ Q d.radical c⁆ ⊔ ⁅Z d.radical c,Z d.radical z⁆ ∧
      W = Y := by
  let W := conjugateSpanBy Y P
  let K := Z d.radical z ⊓ Q d.radical c
  let Yx (x : P) := Y.map (MulAut.conj (x : FreeAmalgam d.radical)).toMonoidHom
  have hcontrols (x : P) : ⁅Yx x,Z d.radical z⁆ ≤ ⁅Yx x,K⁆ ⊔ ⁅Z d.radical c,Z d.radical z⁆ :=
    conjugate_section_control s hc hb q hsmall ha hca Y H P hYV hYN hYB hZaY hZcY hPG hPH
      hHcard hmove hcomm hDcard hWpre x
  have hcrit : ⁅Z d.radical c,Z d.radical z⁆ ≤ Z d.radical c :=
    ((critical_Z_commutator_le_moving (h := h) q).trans inf_le_left).trans
      (DistanceEight.U_le_Z d.radical c)
  have hQY : Q d.radical c ≤ normalizer (Y : Set (FreeAmalgam d.radical)) :=
    (Q_le_stabilizer_of_dist_le_two c a q.start_color ha hca).trans hYN
  have hQYx (x : P) : Q d.radical c ≤ normalizer (Yx x : Set (FreeAmalgam d.radical)) := by
    have hh := (map_mono (f := (MulAut.conj (x : FreeAmalgam d.radical)).toMonoidHom) hQY).trans
      (Y.le_normalizer_map (MulAut.conj (x : FreeAmalgam d.radical)).toMonoidHom)
    exact (mem_normalizer_iff_map_conj_eq.mp (Q_normalized d.radical c (hPG x.property))).symm.le.trans hh
  have hZYx (x : P) : Z d.radical c ≤ Yx x := by
    have hh := map_mono (f := (MulAut.conj (x : FreeAmalgam d.radical)).toMonoidHom) hZcY
    exact (mem_normalizer_iff_map_conj_eq.mp (Z_normalized d.radical c (hPG x.property))).symm.le.trans hh
  have hZYnorm (x : P) : Z d.radical z ≤ normalizer (Yx x : Set (FreeAmalgam d.radical)) :=
    le_normalizer_iff_commutator_le_left.mpr ((hcontrols x).trans
      (sup_le (le_normalizer_iff_commutator_le_left.mp (inf_le_right.trans (hQYx x)))
        (hcrit.trans (hZYx x))))
  have hZW : Z d.radical z ≤ normalizer (W : Set (FreeAmalgam d.radical)) := by
    rw [show W = conjugateSpanBy Y P from rfl,conjugateSpanBy_eq_iSup_conj]
    exact (le_iInf hZYnorm).trans (iInf_normalizer_le_normalizer_iSup _)
  have hWN : stabilizer d.radical c ≤ normalizer (W : Set (FreeAmalgam d.radical)) := by
    rw [←hgen]
    exact sup_le (le_normalizer_conjugateSpanBy Y P) hZW
  have hYQ : Y ≤ Q d.radical c := hYV.trans
    (V_le_Q_of_dist_add_two_lt d.radical (geometry := replacementGeometry h d) ha (by
      change (cosetGraph d.radical).dist a c + 2 < replacementDistance h d
      rw [SimpleGraph.dist_comm]
      omega))
  have hWQ : W ≤ Q d.radical c := conjugateSpanBy_le hYQ (hPG.trans (Q_normalized d.radical c))
  have hedge := critical_last_edge_inputs (h := h) (by omega : 2 < replacementDistance h d) q
  have hWz : W ≤ stabilizer d.radical z :=
    (hWpre.trans hedge.2.1).trans (fun _ hx => hx.2 _ (adjacent_symm d.radical hedge.1))
  have hWc : W ≤ stabilizer d.radical c := hWQ.trans (fun _ hx => hx.1)
  have hQC : Q d.radical c ≤ centralizer (Z d.radical c : Set (FreeAmalgam d.radical)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical c q.start_color))
  have hWK : W ≤ normalizer (K : Set (FreeAmalgam d.radical)) := by
    rw [show K = Z d.radical z ⊓ Q d.radical c from rfl,critical_full_kernel_eq s hc q]
    exact (le_inf (hWz.trans (Z_normalized d.radical z))
      ((hWQ.trans hQC).trans (centralizer (Z d.radical c : Set (FreeAmalgam d.radical))).le_normalizer)).trans
        inf_normalizer_le_normalizer_inf
  let M := ⁅W,K⁆ ⊔ ⁅Z d.radical c,Z d.radical z⁆
  have hMN : W ≤ normalizer (M : Set (FreeAmalgam d.radical)) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq]
    dsimp only [M]
    rw [Subgroup.map_sup,map_commutator,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (W.le_normalizer hg),
      mem_normalizer_iff_map_conj_eq.mp (hWK hg),
      mem_normalizer_iff_map_conj_eq.mp (Z_normalized d.radical c (hWc hg)),
      mem_normalizer_iff_map_conj_eq.mp (Z_normalized d.radical z (hWz hg))]
  have hYxW (x : P) : Yx x ≤ W := by
    rw [show W = conjugateSpanBy Y P from rfl,conjugateSpanBy_eq_iSup_conj]
    exact le_iSup (fun k : P => Y.map (MulAut.conj (k : FreeAmalgam d.radical)).toMonoidHom) x
  have hcontrol : ⁅W,Z d.radical z⁆ ≤ M := by
    conv_lhs => rw [show W = conjugateSpanBy Y P from rfl,conjugateSpanBy_eq_iSup_conj]
    exact commutator_iSup_le_of_relative_normal W (Z d.radical z) M Yx hMN hYxW
      (fun x => (hcontrols x).trans (sup_le_sup_right (commutator_mono (hYxW x) le_rfl) _))
  exact ⟨hWN,hcontrol,small_critical_span_collapse s hc hb q hsmall ha hca
    Y P hYV hYN hZcY hPG hWN hcontrol⟩

omit s in
/-- Source (5.9): the actual image-sixteen replacement has a strict forward slice
in the small critical-image branch, including an original Sylow radical. -/
theorem sixteen_small_forward_slice_strict_knownSimple
    (hb : 4 < replacementDistance h d)
    (himage : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4) :
    2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) := by
  by_contra! hslice
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨z,q,hd,hover,hpre,hi,y,hy,hgen,hmove,hT,hZcY,hYV,hYN,hYB,hHZa,hHcard,hHCa,
    hcomm,hZaQ,hYQ,hDQ,hWQ,hZaV,hZaB,tx,hctx,hatx,hfull,hKfull,hXfull,hJcard,hJalign,hJnot,
    x,hx,hxeq,hYnot,hWnot⟩ :=
    sixteen_small_shifted_kernel_escape_knownSimple (e := e) (hz := hz) (hn := hn)
      hb himage p hsmall hslice
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  let T := Q d.radical (alpha d.radical) ⊓ centralizer
    (U d.radical c ⊓ B d.radical (alpha d.radical)
      ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))
  let H := ⁅U d.radical c,T⁆
  let a := act d.radical y⁻¹ (alpha d.radical)
  let T₂ := T.map (MulAut.conj y).toMonoidHom
  let H₂ := H.map (MulAut.conj y).toMonoidHom
  let Y := (localZSpan d.radical c (alpha d.radical)).map (MulAut.conj y).toMonoidHom
  let P := stabilizer d.radical c ⊓ centralizer (H₂ : Set (FreeAmalgam d.radical))
  have hyG : y ∈ stabilizer d.radical c := Ltilde_le_stabilizer c hy
  have ha : color d.radical a = false := by rw [action_preserves_color]; rfl
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb2
  have hat : Adjacent d.radical (alpha d.radical) t := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent d.radical c t := adjacent_symm d.radical
    ((cosetGraph_adj d.radical _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    change false ≠ color d.radical t at hh
    cases he : color d.radical t with
    | false => exact False.elim (hh he.symm)
    | true => rfl
  have hca : (cosetGraph d.radical).dist c a = 2 := by
    have hfix : act d.radical y⁻¹ c = c := (stabilizer d.radical c).inv_mem hyG
    have hh := dist_act d.radical y⁻¹ c (alpha d.radical)
    rw [hfix,SimpleGraph.dist_comm (u := c) (v := alpha d.radical)] at hh
    exact hh.trans (p.dist_start (by omega))
  have hZaY : Z d.radical a ≤ Y := by
    have hh := map_mono (f := (MulAut.conj y).toMonoidHom)
      (acting_seed_le_local_span (d := d) q.start_color rfl hct hat)
    simpa only [a,Y,c,Z_act,inv_inv] using hh
  have hWpre : conjugateSpanBy Y P ≤ Q d.radical (q.walk.getVert (q.walk.length-2)) := by
    rw [hpre]
    exact hWQ
  have hcomm' : ⁅Y,Q d.radical a ⊓ centralizer
      (U d.radical c ⊓ B d.radical a ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))⁆ ≤ H₂ := by
    rw [←hT]
    exact hcomm
  have hcollapse := shifted_span_collapse s hc hb q (by rw [hi]; decide) ha hca.le
    Y H₂ P hYV hYN hYB hZaY hZcY inf_le_left inf_le_right hgen hHcard hmove hcomm' hJcard hWpre
  have hYG : stabilizer d.radical c ≤ normalizer (Y : Set (FreeAmalgam d.radical)) := by
    rw [←hcollapse.2.2]
    exact hcollapse.1
  have hTG : T ≤ stabilizer d.radical c :=
    (inf_le_left.trans (Q_le_adjacent_h d.radical ht hat)).trans
      (fun _ hx => hx.2 _ (adjacent_symm d.radical hct))
  have hHU : H ≤ U d.radical c :=
    le_normalizer_iff_commutator_le_left.mp (hTG.trans (U_normalized c))
  have hHc : H₂ ≤ Z d.radical c :=
    ((map_mono hHU).trans_eq (mem_normalizer_iff_map_conj_eq.mp
      (U_normalized c hyG))).trans (DistanceEight.U_le_Z d.radical c)
  have hT₂G : T₂ ≤ stabilizer d.radical c :=
    (show T₂ ≤ Q d.radical a by
      change T₂ = Q d.radical a ⊓ _ at hT
      rw [hT]
      exact inf_le_left).trans
      (Q_le_stabilizer_of_dist_le_two a c ha q.start_color (by rw [SimpleGraph.dist_comm]; exact hca.le))
  have hcommU : ⁅U d.radical c,T₂⁆ = H₂ := by
    have hUm : (U d.radical c).map (MulAut.conj y).toMonoidHom = U d.radical c :=
      mem_normalizer_iff_map_conj_eq.mp (U_normalized c hyG)
    dsimp only [H₂,H]
    rw [map_commutator,hUm]
  have hT₂ne : ¬ T₂ ≤ Q d.radical c := by
    intro hle
    have he : ⁅U d.radical c,T₂⁆ = ⊥ := le_bot_iff.mp
      ((commutator_mono (DistanceEight.U_le_Z d.radical c) hle).trans_eq
        (Z_centralizes_Q d.radical c q.start_color))
    rw [hcommU] at he
    change Nat.card H₂ = 2 at hHcard
    rw [he,card_bot] at hHcard
    omega
  let E := conjugateSpanBy (Z d.radical a) (stabilizer d.radical c)
  have hEY : E ≤ Y := conjugateSpanBy_le hZaY hYG
  have hEV : E ≤ V d.radical c :=
    conjugateSpanBy_le hZaV (DistanceEight.V_normalized d.radical c)
  have hEB := normalized_radius_le_slice_of_actor_at s hb2 q.start_color E T₂ hEV
    (le_normalizer_conjugateSpanBy _ _) hT₂G hT₂ne
    (((commutator_mono hEY le_rfl).trans hcomm).trans hHc)
  exact hZaB ((le_conjugateSpanBy _ _).trans hEB)

omit s in
/-- The strict bound on every original component vertex, with the actual
critical walk and the same second vertex. -/
theorem sixteen_small_forward_slice_strict_at_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 4 < replacementDistance h d)
    (himage : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4) :
    2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical g⁻¹ a = alpha d.radical := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have hpact : ∃ p₀ : CriticalPath d.radical (replacementGeometry h d)
      (act d.radical g⁻¹ a) (act d.radical g⁻¹ a'),
      p₀.walk.getVert 2 = act d.radical g⁻¹ (p.walk.getVert 2) :=
    ⟨p.act g⁻¹,by simp only [CriticalPath.act,actWalk_getVert]⟩
  rw [hbase] at hpact
  obtain ⟨p₀,hvert⟩ := hpact
  have hsmall₀ : (Q d.radical (act d.radical g⁻¹ a')).relIndex
      (Z d.radical (alpha d.radical)) < 4 := by
    rw [←hbase,Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹⁻¹).injective]
    exact hsmall
  have hB := Escape.PairingControl.FirstPairing.B_act
    (geometry := replacementGeometry h d) (by change 2 < replacementDistance h d; omega)
    g⁻¹ a p.start_color
  rw [hbase,inv_inv] at hB
  have hi := sixteen_small_forward_slice_strict_knownSimple (e := e) (hz := hz) (hn := hn) hb himage p₀ hsmall₀
  rw [hvert,U_act,inv_inv,hB,relIndex_map_map_of_injective _ _ (MulAut.conj g).injective] at hi
  exact hi


omit s in
/-- The original image-sixteen backward shift with its strictness premise discharged. -/
theorem sixteen_small_backward_shift_of_four_lt_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4) :
    ∃ t, Adjacent d.radical a t ∧
      ∃ g ∈ stabilizer d.radical a,
        act d.radical g (p.walk.getVert 1) = t ∧
        Adjacent d.radical (act d.radical g (p.walk.getVert 2)) t ∧
        Q d.radical t ⊔ Z d.radical z = stabilizer d.radical a ∧
        2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical (act d.radical g (p.walk.getVert 2))) ∧
        ∃ q : CriticalPath d.radical (replacementGeometry h d)
            (act d.radical g (p.walk.getVert 2)) (p.walk.getVert (p.walk.length-2)),
          q.walk.getVert 1 = t ∧
          ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i := by
  have hstrict := sixteen_small_forward_slice_strict_at_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard p hsmall
  have hl : p.walk.length = replacementDistance h d := p.length_eq_b
  have hdelta : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  exact sixteen_strict_backward_shift_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard p hsmall hdelta hstrict

omit s in
/-- The strict-forward proof supplies the original-radical shift, retaining the literal maps. -/
theorem original_radical_small_backward_shift_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4)
    (hfirst : p.walk.getVert 1 = beta d.radical) :
    let T := ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical)
    let J := SmallMover.join (U d.radical (p.walk.getVert 2)) (Q d.radical (p.walk.getVert 2)) T 4
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      ∃ g ∈ stabilizer d.radical (alpha d.radical),
        act d.radical g (beta d.radical) = t ∧
        Adjacent d.radical (act d.radical g (p.walk.getVert 2)) t ∧
        T.map (MulAut.conj g⁻¹).toMonoidHom = Q d.radical t ∧
        J.map (MulAut.conj g⁻¹).toMonoidHom =
          SmallMover.join (U d.radical (act d.radical g (p.walk.getVert 2)))
            (Q d.radical (act d.radical g (p.walk.getVert 2))) (Q d.radical t) 4 ∧
        T.map (MulAut.conj g⁻¹).toMonoidHom ⊔ Z d.radical z = stabilizer d.radical (alpha d.radical) ∧
        (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
            (U d.radical (act d.radical g (p.walk.getVert 2))) =
          (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
            (U d.radical (p.walk.getVert 2)) ∧
        ∃ q : CriticalPath d.radical (replacementGeometry h d)
            (act d.radical g (p.walk.getVert 2)) (p.walk.getVert (p.walk.length-2)),
          q.walk.getVert 1 = t ∧
          ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i := by
  have hstrict := sixteen_small_forward_slice_strict_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard p hsmall
  have hl : p.walk.length = replacementDistance h d := p.length_eq_b
  have hdelta : Adjacent d.radical (p.walk.getVert 2) (beta d.radical) := by
    rw [←hfirst]
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  exact original_radical_strict_backward_shift_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard p hsmall hfirst hdelta hstrict

end SylowForwardSpan
end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
