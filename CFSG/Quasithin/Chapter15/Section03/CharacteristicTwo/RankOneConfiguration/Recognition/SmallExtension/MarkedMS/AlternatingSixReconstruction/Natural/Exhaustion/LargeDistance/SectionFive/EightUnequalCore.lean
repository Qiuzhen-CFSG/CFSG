module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EightResidualTransport
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowUnequalResidual
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTrappedExclusion
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowPairedFixer
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeFullKernel

/-!
# Whole-core comparison for unequal movers in image eight

Let E be the small mover at a neighboring component vertex on the actual
replacement edge. A trapped nonnormalizing seed forces central generation
of the full omega centers at every component vertex. If E contains the
starting core, its omega center and that of the starting mover have the
same order, whereas their fixed indices are eight and four. This rules
out containment. Consequently the whole starting core times E equals the
edge core, with the two cross indices exactly two and eight.

The full reverse critical kernel lies in E. Its whole-seed fixer is
normalized by E, and its join with the starting seed is normalized by the
critical endpoint. The small-section argument excludes residual generation
by these two actors in a strict trapped slice. If the edge core itself
generates with the endpoint, strictness supplies nonnormalization and the
argument constructs an overlapping backward critical path. That generation premise is explicit and is stronger than generation
by the relative normalizer; this module does not substitute one for the other.

The literal original-radical application records index four for E in the
restricted original Sylow, as well as index two for the edge core. Both
moving covers and the entire central attachments remain. Unconditional
backward selection and the final distance exclusions remain to be proved.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (5.5)(c) and (5.7), printed pp.917--919. This extends the whole-omega
and fixer arguments of SylowUnequalResidual and SylowUnequalFixer to the
surviving image-eight branch, using their generic private group lemmas.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EightUnequalCore
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

include e hz hn in
/-- If an unequal neighboring mover contains the starting core, the full X
cannot be centrally generated. Equal omega orders contradict the two fixed indices. -/
theorem unequal_containing_core_not_centrally_generated_knownSimple
    (hb : 4 < replacementDistance h d)
    {a c t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hne : SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4 ≠
      SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4)
    (hcore : Q d.radical a ≤ SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4) :
    X d.radical a ≠ U d.radical a ⊔
      (X d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) := by
  intro hsplit
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hcentral := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let J := SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4
  let E := SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    rw [ha] at hh
    cases he : color d.radical t <;> simp_all
  have hc : color d.radical c = false := by
    have hh := adjacent_color_ne d.radical hct
    rw [ht] at hh
    cases he : color d.radical c <;> simp_all
  obtain ⟨_,_,hQJ,hJT,_,_,_,_,hfixJ,_⟩ := EightSmallMovers.edge_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hb ha hat
  have hET : E ≤ Q d.radical t := SmallMover.join_le _ _ _ _
  have hfixE : 4 < (centralizer (E : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) := by
    rw [(EightSmallMovers.unequal_neighbor_indices_knownSimple
      (e := e) (hz := hz) (hn := hn) hb ha hat hct hne).2]
    decide
  have hTP : Q d.radical t ≤ stabilizer d.radical a := fun _ hx => hx.2 _ (adjacent_symm d.radical hat)
  have hXP : X d.radical a ≤ stabilizer d.radical a := (omegaCenter_le (Q d.radical a)).trans
    (fun _ hx => hx.1)
  have hXZ := SylowPairedFixer.central_generation_eq_seed (h := h) ha hat hsplit
  have hself : stabilizer d.radical a ⊓ centralizer (Q d.radical a : Set (FreeAmalgam d.radical)) ≤
      Q d.radical a := by
    intro x hx
    rw [←C_eq_Q s hcentral a ha]
    exact ⟨hx.1,fun y hy => hx.2 y (hXZ.ge.trans (omegaCenter_le _) hy)⟩
  let := finite_stabilizer d.radical a
  let : Finite (X d.radical a) := Finite.of_injective (inclusion hXP) (inclusion_injective _)
  have fixed_index (A : Subgroup (FreeAmalgam d.radical))
      (hQA : Q d.radical a ≤ A) (hAT : A ≤ Q d.radical t) :
      (omegaCenter A).relIndex (X d.radical a) =
        (centralizer (A : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) := by
    have he := SectionFive.omegaCenter_eq_fixed_of_selfcentralizing (stabilizer d.radical a) (Q d.radical a) A
      hQA (hAT.trans hTP) hself
    change omegaCenter A = X d.radical a ⊓ centralizer (A : Set (FreeAmalgam d.radical)) at he
    let F := X d.radical a ⊓ centralizer (A : Set (FreeAmalgam d.radical))
    have hUF : U d.radical a ⊔ F = X d.radical a := by
      apply le_antisymm (sup_le (hsplit ▸ le_sup_left) inf_le_left)
      rw [hsplit]
      exact sup_le le_sup_left ((inf_le_inf_left _ (centralizer_le (hAT.trans hTP))).trans le_sup_right)
    have hUX : U d.radical a ≤ X d.radical a := hsplit ▸ le_sup_left
    let : Finite F := Finite.of_injective (inclusion (show F ≤ X d.radical a from inf_le_left))
      (inclusion_injective _)
    rw [he]
    change F.relIndex (X d.radical a) = _
    have hidx := relIndex_sup_of_normalizes (U d.radical a) F
      ((inf_le_left.trans hXP).trans (U_normalized a))
    rw [hUF] at hidx
    rw [hidx]
    have hfu : F ⊓ U d.radical a = U d.radical a ⊓ centralizer (A : Set (FreeAmalgam d.radical)) := by
      dsimp only [F]
      ext v
      exact ⟨fun hv => ⟨hv.2,hv.1.2⟩,fun hv => ⟨⟨hUX hv.1,hv.2⟩,hv.1⟩⟩
    rw [←inf_relIndex_right F (U d.radical a),hfu,inf_relIndex_left]
  have hia := fixed_index J hQJ hJT
  have hic := fixed_index E hcore hET
  rw [hfixJ] at hia
  obtain ⟨g,hg,hga⟩ := stabilizer_transitive_neighbors d.radical t
    (adjacent_symm d.radical hat) (adjacent_symm d.radical hct)
  have hgt : act d.radical g t = t := hg
  have hconj : E = J.map (MulAut.conj g⁻¹).toMonoidHom := by
    dsimp only [J,E]
    rw [SmallMover.join_map _ (MulAut.conj g⁻¹).injective,←U_act,←Q_act,←Q_act,hga,hgt]
  have homega : Nat.card (omegaCenter J) = Nat.card (omegaCenter E) := by
    rw [hconj,omegaCenter_map _ _ (MulAut.conj g⁻¹).injective,
      card_map_of_injective (MulAut.conj g⁻¹).injective]
  have hea := SectionFive.omegaCenter_eq_fixed_of_selfcentralizing (stabilizer d.radical a) (Q d.radical a) J
    hQJ (hJT.trans hTP) hself
  have hec := SectionFive.omegaCenter_eq_fixed_of_selfcentralizing (stabilizer d.radical a) (Q d.radical a) E
    hcore (hET.trans hTP) hself
  have haX : omegaCenter J ≤ X d.radical a := hea ▸ inf_le_left
  have hcX : omegaCenter E ≤ X d.radical a := hec ▸ inf_le_left
  have hma := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam d.radical)) (omegaCenter J)
    (X d.radical a) bot_le haX
  have hmc := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam d.radical)) (omegaCenter E)
    (X d.radical a) bot_le hcX
  rw [relIndex_bot_left,relIndex_bot_left,hia] at hma
  rw [relIndex_bot_left,relIndex_bot_left,hic,←homega] at hmc
  let : Finite (omegaCenter J) := Finite.of_injective (inclusion haX) (inclusion_injective _)
  have heq := Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := omegaCenter J)) (hma.trans hmc.symm)
  omega

include e hz hn in
/-- The full reverse kernel lies in the candidate's own small mover, which
therefore preserves its whole-seed fixer. Equal neighboring movers are unnecessary. -/
theorem trapped_strict_fixer_normalized_knownSimple
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
  have hFT : F ≤ Q d.radical t := inf_le_right.trans (Q_le_adjacent_h d.radical ht hat)
  have hFN : F ≤ J ∧ ⁅J,F⁆ ≤ Q d.radical c := hsmallActor F hFT hfix.1
  have hE := EightSmallMovers.edge_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hc hct
  have hEJ : E ≤ J := by
    rw [show E = _ from hE.1,hJ]
    exact inf_le_right
  have hFE : F ≤ E ∧ ⁅E,F⁆ ≤ Q d.radical c := by
    constructor
    · rw [show E = _ from hE.1,hJ]
      exact le_inf hFT hFN.1
    · exact (commutator_mono hEJ le_rfl).trans hFN.2
  have hEN : E ≤ normalizer (D : Set (FreeAmalgam d.radical)) := by
    have hh := (EightPairedNormalizer.normalizer_mover_preserves_seed_fixer_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hc hct).2 F
    rw [hJ] at hh
    exact hEJ.trans (hh hFN.1)
  refine ⟨hFE.1,hFE.2,hEN,sup_le ?_ hfix.2.2⟩
  have hEG : E ≤ stabilizer d.radical a := (SmallMover.join_le _ _ _ _).trans
    (fun _ hx => hx.2 _ (adjacent_symm d.radical hat))
  exact (le_inf hEN (hEG.trans (Z_normalized d.radical a))).trans
    (normalizer_inf_normalizer_le_normalizer_sup _ _)

include e hz hn in
/-- A strict trapped candidate cannot supply the source residual generation:
its literal mover and critical seed normalize a small fixer span outside the slice. -/
theorem trapped_strict_residual_not_le_knownSimple
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
    ¬ Ltilde d.radical a ≤
      SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4 ⊔ Z d.radical z := by
  let F := Z d.radical z ⊓ Q d.radical a
  let D := Z d.radical c ⊓ centralizer (F : Set (FreeAmalgam d.radical))
  let Y := D ⊔ Z d.radical a
  have hnormal := trapped_strict_fixer_normalized_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall hat hct htrap hnorm hstrict
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
/-- A trapped nonnormalizing seed forces an unequal opposite mover to omit
the starting core. Its product with that whole core is the entire edge core. -/
theorem trapped_unequal_core_product_knownSimple
    (hb : 4 < replacementDistance h d)
    {a z c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hne : SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4 ≠
      SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4)
    (htrap : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    (hnorm : ¬ Z d.radical z ≤ normalizer
      ((Z d.radical c ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) :
        Set (FreeAmalgam d.radical))) :
    let E := SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4
    ¬ Q d.radical a ≤ E ∧ Q d.radical a ⊔ E = Q d.radical t ∧
      E.relIndex (Q d.radical a) = 2 ∧ (Q d.radical a).relIndex E = 8 := by
  let E := SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4
  have hX := SylowPairedFixer.trapped_nonnormalized_full_kernel_knownSimple
    (e := e) (hz := hz) (hn := hn) (by omega : 2 < replacementDistance h d)
      p hsmall hat hct htrap hnorm
  have hXa := X_central_generation_all p.end_color hX.1 a p.start_color
  have hnot : ¬ Q d.radical a ≤ E := by
    intro hcore
    exact unequal_containing_core_not_centrally_generated_knownSimple
      (e := e) (hz := hz) (hn := hn) hb p.start_color hat hct hne hcore hXa
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    rw [p.start_color] at hh
    cases ht : color d.radical t <;> simp_all
  have hc : color d.radical c = false := by
    have hh := adjacent_color_ne d.radical hct
    rw [ht] at hh
    cases hc : color d.radical c <;> simp_all
  obtain ⟨_,_,_,hET,_,hEi,hEN,_⟩ := EightSmallMovers.edge_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hc hct
  have hQT : Q d.radical a ≤ Q d.radical t := Q_le_adjacent_h d.radical ht hat
  have hsupT : Q d.radical a ⊔ E ≤ Q d.radical t := sup_le hQT hET
  have hm := relIndex_mul_relIndex E (Q d.radical a ⊔ E) (Q d.radical t)
    le_sup_right hsupT
  change E.relIndex (Q d.radical t) = 2 at hEi
  rw [hEi] at hm
  have hd : E.relIndex (Q d.radical a ⊔ E) ∣ 2 :=
    ⟨(Q d.radical a ⊔ E).relIndex (Q d.radical t),hm.symm⟩
  have hprod : Q d.radical a ⊔ E = Q d.radical t := by
    rcases Nat.prime_two.eq_one_or_self_of_dvd _ hd with he | he
    · exact (hnot (le_sup_left.trans (relIndex_eq_one.mp he))).elim
    · rw [he] at hm
      have hone : (Q d.radical a ⊔ E).relIndex (Q d.radical t) = 1 := by omega
      exact le_antisymm hsupT (relIndex_eq_one.mp hone)
  have hEG : E ≤ stabilizer d.radical a :=
    hET.trans (fun _ hx => hx.2 _ (adjacent_symm d.radical hat))
  let := finite_stabilizer d.radical a
  let : Finite E := Finite.of_injective (inclusion hEG) (inclusion_injective _)
  let : Finite (Q d.radical a) := Finite.of_injective
    (inclusion (show Q d.radical a ≤ stabilizer d.radical a from fun _ hx => hx.1))
    (inclusion_injective _)
  have hindex : E.relIndex (Q d.radical a) = 2 := by
    rw [←relIndex_sup_of_normalizes (Q d.radical a) E (hEG.trans (Q_normalized d.radical a)),
      hprod,hEi]
  have hQindex : (Q d.radical a).relIndex (Q d.radical t) = 8 := by
    obtain ⟨_,_,hQJ,hJT,hQJi,hJi,_⟩ := EightSmallMovers.edge_small_mover_knownSimple
      (e := e) (hz := hz) (hn := hn) hb p.start_color hat
    have hh := relIndex_mul_relIndex (Q d.radical a)
      (SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4)
      (Q d.radical t) hQJ hJT
    rw [hQJi,hJi] at hh
    exact hh.symm
  refine ⟨hnot,hprod,hindex,?_⟩
  change (Q d.radical a).relIndex E = 8
  rw [←relIndex_sup_of_normalizes E (Q d.radical a) (hQT.trans hEN),
    sup_comm E,hprod,hQindex]

include e hz hn in
/-- On an edge which itself generates with the critical seed, an unequal
strict neighbor has the actual overlapping backward path, on either cover. -/
theorem unequal_edge_generating_backward_path_knownSimple
    (hb : 4 < replacementDistance h d)
    {a z c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hne : SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4 ≠
      SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4)
    (hgen : Q d.radical t ⊔ Z d.radical z = stabilizer d.radical a)
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c)) :
    ∃ q : CriticalPath d.radical (replacementGeometry h d)
        c (p.walk.getVert (p.walk.length-2)),
      q.walk.getVert 1 = t ∧
      ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i := by
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    rw [p.start_color] at hh
    cases ht : color d.radical t <;> simp_all
  have hc : color d.radical c = false := by
    have hh := adjacent_color_ne d.radical hct
    rw [ht] at hh
    cases hc : color d.radical c <;> simp_all
  have hnorm : ¬ Z d.radical z ≤ normalizer
      ((Z d.radical c ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) :
        Set (FreeAmalgam d.radical)) := by
    intro hbad
    let Y := Z d.radical c ⊔ Z d.radical a
    have hYN : stabilizer d.radical a ≤ normalizer (Y : Set (FreeAmalgam d.radical)) := by
      rw [←hgen]
      refine sup_le ?_ hbad
      apply (le_inf _ _).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
      · exact (show Q d.radical t ≤ stabilizer d.radical c from
          fun _ hx => hx.2 _ (adjacent_symm d.radical hct)).trans (Z_normalized d.radical c)
      · exact (show Q d.radical t ≤ stabilizer d.radical a from
          fun _ hx => hx.2 _ (adjacent_symm d.radical hat)).trans (Z_normalized d.radical a)
    have hYV : Y ≤ V d.radical a :=
      sup_le (neighbor_seed_le_radius hat hct) (Z_le_VBall d.radical a 2)
    have hYB := residual_small_radius_le_slice_knownSimple (e := e)
      (by omega : 2 < replacementDistance h d) p.start_color Y hYV
      ((Ltilde_le_stabilizer a).trans hYN)
      (SylowSpanSelection.adjacent_seed_span_index_le_eight
        (e := e) (hz := hz) (hn := hn) hb p.start_color hat hct)
    have hi := relIndex_eq_one.mpr ((DistanceEight.U_le_Z d.radical c).trans
      (le_sup_left.trans hYB))
    omega
  have hescape : ¬ Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) := by
    intro htrap
    have hp := trapped_unequal_core_product_knownSimple
      (e := e) (hz := hz) (hn := hn) hb p hsmall hat hct hne htrap hnorm
    obtain ⟨_,_,_,hET,_,hEi,_⟩ := EightSmallMovers.edge_small_mover_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hc hct
    let := finite_stabilizer d.radical a
    have hres := SectionFive.index_two_opposite_generation (stabilizer d.radical a)
      (Q d.radical a) (Q d.radical t)
      (SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4)
      (Z d.radical z) (Q_le_adjacent_h d.radical ht hat)
      (fun _ hx => hx.2 _ (adjacent_symm d.radical hat)) hET
      (Q_normalized d.radical a) hEi hp.1 hgen
    exact trapped_strict_residual_not_le_knownSimple
      (e := e) (hz := hz) (hn := hn) hb p hsmall hat hct htrap hnorm hstrict hres.2
  let w : (cosetGraph d.radical).Walk c a :=
    .cons ((cosetGraph_adj d.radical _ _).mpr hct)
      (.cons ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat)) .nil)
  have hw : w.length = 2 := rfl
  have hb2 : 2 ≤ (replacementGeometry h d).b d.radical := by
    change 2 ≤ replacementDistance h d
    omega
  let q := p.prepend_two hb2 hc w hw hescape
  refine ⟨q,?_,fun i hi => p.prepend_two_overlap _ _ _ _ _ hi⟩
  change (p.prepend_two _ hc w hw hescape).walk.getVert 1 = t
  rw [CriticalPath.prepend_two_walk]
  simp only [SimpleGraph.Walk.getVert_append,hw,show 1<2 from by decide,ite_true,
    w,SimpleGraph.Walk.getVert_cons_succ,SimpleGraph.Walk.getVert_zero]

include e hz hn in
/-- The trapped unequal mover has index four in the literal original radical,
not index two. Its full reverse kernel and fixer retain their actual carriers. -/
theorem original_radical_trapped_unequal_core_knownSimple
    (hb : 4 < replacementDistance h d)
    {z c : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4)
    (hct : Adjacent d.radical c (beta d.radical))
    (hne : SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical (beta d.radical)) 4 ≠
      SmallMover.join (U d.radical (alpha d.radical)) (Q d.radical (alpha d.radical))
        (Q d.radical (beta d.radical)) 4)
    (htrap : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    (hnorm : ¬ Z d.radical z ≤ normalizer
      ((Z d.radical c ⊔ Z d.radical (alpha d.radical) : Subgroup (FreeAmalgam d.radical)) :
        Set (FreeAmalgam d.radical)))
    (hstrict : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c)) :
    let T := ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical)
    let E := SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical (beta d.radical)) 4
    let F := Z d.radical z ⊓ Q d.radical (alpha d.radical)
    let D := Z d.radical c ⊓ centralizer (F : Set (FreeAmalgam d.radical))
    (Q d.radical (beta d.radical)).relIndex T = 2 ∧ E.relIndex T = 4 ∧
      Q d.radical (alpha d.radical) ⊔ E = Q d.radical (beta d.radical) ∧
      E.relIndex (Q d.radical (alpha d.radical)) = 2 ∧
      (Q d.radical (alpha d.radical)).relIndex E = 8 ∧
      F ≤ E ∧ ⁅E,F⁆ ≤ Q d.radical c ∧
      E ⊔ Z d.radical z ≤ normalizer ((D ⊔ Z d.radical (alpha d.radical) :
        Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) ∧
      ¬ Ltilde d.radical (alpha d.radical) ≤ E ⊔ Z d.radical z := by
  let T := ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical)
  let E := SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical (beta d.radical)) 4
  have hi : (Q d.radical (beta d.radical)).relIndex T = 2 := by
    rw [Q_beta,relIndex_map_map_of_injective _ _ (embedM_injective d.radical)]
    exact (SylowWholeCore.four_lt_original_sylow_eight_image_knownSimple
      (e := e) (hz := hz) (hn := hn) hb).2.2.1
  have hc : color d.radical c = false := by
    have hh := adjacent_color_ne d.radical hct
    change color d.radical c ≠ true at hh
    cases he : color d.radical c
    · rfl
    · exact (hh he).elim
  obtain ⟨_,_,_,hET,_,hEi,_⟩ := EightSmallMovers.edge_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hc hct
  have hQT : Q d.radical (beta d.radical) ≤ T := by
    dsimp only [T]
    rw [←SylowSmallNormalizer.four_lt_base_edge_normalizer_knownSimple
      (e := e) (hz := hz) (hn := hn) hb]
    exact le_inf (Q d.radical (beta d.radical)).le_normalizer
      (fun _ hx => hx.2 _ (adjacent_symm d.radical (base_adjacent d.radical)))
  have hEiT : E.relIndex T = 4 := by
    have hh := relIndex_mul_relIndex E (Q d.radical (beta d.radical)) T hET hQT
    rw [hEi,hi] at hh
    exact hh.symm
  have hp := trapped_unequal_core_product_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall (base_adjacent d.radical) hct hne htrap hnorm
  have hf := trapped_strict_fixer_normalized_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall (base_adjacent d.radical) hct htrap hnorm hstrict
  exact ⟨hi,hEiT,hp.2.1,hp.2.2.1,hp.2.2.2,hf.1,hf.2.1,hf.2.2.2,
    trapped_strict_residual_not_le_knownSimple
      (e := e) (hz := hz) (hn := hn) hb p hsmall (base_adjacent d.radical) hct htrap hnorm hstrict⟩

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EightUnequalCore
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
