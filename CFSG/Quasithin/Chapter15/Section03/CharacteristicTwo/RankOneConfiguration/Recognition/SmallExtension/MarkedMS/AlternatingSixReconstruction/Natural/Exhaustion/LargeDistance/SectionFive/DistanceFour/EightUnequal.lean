module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.EightGenerating
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.SixteenUnequal
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EightUnequalCore
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EightSmallMovers

/-!
# Image-eight unequal-mover selection at distance four

The two unequal edge movers have equal orders and different fixed indices on
one whole moving cover. If a trapped strict seed centrally generates the full
omega center, that comparison forces the opposite mover to omit the starting
core. Its product with the core is therefore the entire edge core.

The distance-four reverse-kernel line estimate controls its full-seed fixer.
The mover and critical endpoint normalize the resulting small section, which
would lie in the Baumann slice and contradict strictness. Thus a generating
edge supplies an overlapping backward critical path. Both moving covers and
all central attachments are retained; no whole-radius commutativity is used.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.5)(c), (5.7), and their use in (5.12), pp.917--919,924.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterB.Offenders.Six
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.EightUnequal
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

include e hz hn in
/-- Unequal actual edge movers have opposite-cover fixed index eight. -/
theorem unequal_neighbor_indices_knownSimple
    (hne₀ : ¬ IsElementaryAbelian 2 (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8)
    (hb : 2 < replacementDistance h d)
    {a c t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hne : SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4 ≠
      SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4) :
    let E := SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4
    4 ≤ (Q d.radical a).relIndex E ∧
      (centralizer (E : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) = 8 := by
  let S₀ := stabilizer d.radical a
  let U₀ := (U d.radical a).subgroupOf S₀
  let Q₀ := (Q d.radical a).subgroupOf S₀
  let T₀ := (Q d.radical t).subgroupOf S₀
  let J := SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4
  let E := SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4
  let J₀ := J.subgroupOf S₀
  let E₀ := E.subgroupOf S₀
  let := finite_stabilizer d.radical a
  have hc : color d.radical c = false := by
    have hh := adjacent_color_ne d.radical hat
    have hh' := adjacent_color_ne d.radical hct
    rw [ha] at hh
    cases ht : color d.radical t <;> cases hc : color d.radical c <;> simp_all
  obtain ⟨_,_,hQJ,hJT,hQi,hJi,_⟩ := EightMovers.edge_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hne₀ hcard hb ha hat
  obtain ⟨_,_,_,hET,_,hEi,_⟩ := EightMovers.edge_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hne₀ hcard hb hc hct
  have hUS : U d.radical a ≤ S₀ := (DistanceEight.U_le_Z d.radical a).trans (Z_le_stabilizer d.radical a)
  have hQS : Q d.radical a ≤ S₀ := fun _ hx => hx.1
  have hTS : Q d.radical t ≤ S₀ := fun _ hx => hx.2 a (adjacent_symm d.radical hat)
  have hJS : J ≤ S₀ := hJT.trans hTS
  have hES : E ≤ S₀ := hET.trans hTS
  have hjoin : SmallMover.join U₀ Q₀ T₀ 4 = J₀ := by
    apply map_injective S₀.subtype_injective
    rw [SmallMover.join_map S₀.subtype S₀.subtype_injective,
      map_subgroupOf_eq_of_le hUS,map_subgroupOf_eq_of_le hQS,
      map_subgroupOf_eq_of_le hTS,map_subgroupOf_eq_of_le hJS]
  have hcard' : Nat.card J₀ = Nat.card E₀ := by
    rw [←card_map_of_injective S₀.subtype_injective (K := J₀),
      ←card_map_of_injective S₀.subtype_injective (K := E₀),
      map_subgroupOf_eq_of_le hJS,map_subgroupOf_eq_of_le hES]
    have hj := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam d.radical)) J (Q d.radical t) bot_le hJT
    have he := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam d.radical)) E (Q d.radical t) bot_le hET
    rw [relIndex_bot_left,relIndex_bot_left,hJi] at hj
    rw [relIndex_bot_left,relIndex_bot_left,hEi] at he
    omega
  have hlarge : Q₀.relIndex J₀ = 4 := by
    have hh := relIndex_map_map_of_injective Q₀ J₀ S₀.subtype_injective
    rw [map_subgroupOf_eq_of_le hQS,map_subgroupOf_eq_of_le hJS] at hh
    exact hh.symm.trans hQi
  have hEl : 4 ≤ Q₀.relIndex E₀ := by
    rw [←hlarge]
    exact SmallMover.relIndex_le_of_card_eq_of_le Q₀ J₀ E₀ (comap_mono hQJ) hcard'
  have hstrict : 4 < (centralizer (E : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) := by
    by_contra hnidx
    have hi : (centralizer (E₀ : Set S₀)).relIndex U₀ ≤ 4 := by
      have hh := SmallMover.centralizer_index_map S₀.subtype S₀.subtype_injective U₀ E₀
      rw [map_subgroupOf_eq_of_le hUS,map_subgroupOf_eq_of_le hES] at hh
      rw [←hh]
      exact le_of_not_gt hnidx
    have he := SmallMover.eq_join_of_card_eq_of_index_le U₀ Q₀ T₀ 4 (by decide)
      (hjoin.symm ▸ comap_mono hQJ) (by rw [hjoin,hlarge])
      E₀ (comap_mono hET) (hjoin.symm ▸ hcard') hi
    rw [hjoin] at he
    have hh := congrArg (Subgroup.map S₀.subtype) he
    rw [map_subgroupOf_eq_of_le hES,map_subgroupOf_eq_of_le hJS] at hh
    exact hne hh

  refine ⟨?_,?_⟩
  · have hh := relIndex_map_map_of_injective Q₀ E₀ S₀.subtype_injective
    rw [map_subgroupOf_eq_of_le hQS,map_subgroupOf_eq_of_le hES] at hh
    rwa [hh]
  · let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
    have hcent := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
    obtain ⟨i,hinj,hir,hiR,hiQ,hiU⟩ := SylowAdjacent.edge_coordinates (h := h) hcent ha hat
    have hm : (E.comap i).map i = E := map_comap_eq_self (hES.trans_eq hir.symm)
    have hER : E.comap i ≤ d.radical := by
      have hh := comap_mono (f := i) (show E ≤ Q d.radical t from hET)
      rwa [←hiR,comap_map_eq_self_of_injective hinj] at hh
    have hidx := SmallMover.centralizer_index_map i hinj (replacementMoved d) (E.comap i)
    rw [hiU,hm] at hidx
    change (centralizer (E : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) = 8
    rw [hidx]
    exact SylowKernelMovement.cover_two_group_fixed_index_eight s _
      ((replacement_radical_isPGroup h d).of_injective (inclusion hER)
        (inclusion_injective hER)) (by rwa [←hidx])


include e hz hn in
private theorem small_mover_preserves_seed_fixer_knownSimple
    (hne₀ : ¬ IsElementaryAbelian 2 (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8)
    (hb : 2 < replacementDistance h d)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t)
    (A : Subgroup (FreeAmalgam d.radical))
    (hA : A ≤ SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4) :
    let J := SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4
    J ≤ normalizer ((Z d.radical a ⊓ centralizer (A : Set (FreeAmalgam d.radical)) :
      Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) := by
  let J := SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4
  obtain ⟨_,_,_,hJT,_,_,_,hquad,_⟩ := EightMovers.edge_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hne₀ hcard hb ha hat
  have hJderived : ⁅J,J⁆ ≤ J := le_normalizer_iff_commutator_le_left.mp J.le_normalizer
  have hJU : ⁅⁅J,J⁆,U d.radical a⁆ = ⊥ :=
    commutator_commutator_eq_bot_of_rotate
      (by simpa only [commutator_comm J (U d.radical a)] using hquad) hquad
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    cases he : color d.radical t <;> simp_all
  have hZt : Z d.radical t ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
    intro x hx
    rw [Z,if_neg (by simp [ht])] at hx
    exact (mem_omegaCenter_iff.mp hx).2.2
  have hJZ : ⁅J,J⁆ ≤ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) := by
    apply le_centralizer_iff.mpr
    rw [DistanceTwo.CentralLayer.Z_eq_moving_sup_edge_at h e hz d ha hat]
    exact sup_le (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hJU))
      (hZt.trans (centralizer_le (hJderived.trans hJT)))
  have hTG : Q d.radical t ≤ stabilizer d.radical a :=
    fun _ hx => hx.2 _ (adjacent_symm d.radical hat)
  exact CubePairedKernel.abelian_action_preserves_fixed J (Z d.radical a) A
    ((hJT.trans hTG).trans (Z_normalized d.radical a)) hA hJZ


include e hz hn in
/-- If an unequal neighboring mover contains the starting core, the full X
cannot be centrally generated. Equal omega orders contradict the two fixed indices. -/
theorem unequal_containing_core_not_centrally_generated_knownSimple
    (hne₀ : ¬ IsElementaryAbelian 2 (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8)
    (hb : replacementDistance h d = 4)
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
  obtain ⟨_,_,hQJ,hJT,_,_,_,_,hfixJ,_⟩ := EightMovers.edge_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hne₀ hcard (by omega : 2 < replacementDistance h d) ha hat
  have hET : E ≤ Q d.radical t := SmallMover.join_le _ _ _ _
  have hfixE : 4 < (centralizer (E : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) := by
    rw [(unequal_neighbor_indices_knownSimple
      (e := e) (hz := hz) (hn := hn) hne₀ hcard (by omega : 2 < replacementDistance h d) ha hat hct hne).2]
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
    (hne₀ : ¬ IsElementaryAbelian 2 (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8)
    (hb : replacementDistance h d = 4)
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
  have hfix := SixteenUnequal.trapped_strict_seed_fixer_escape_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall hat hct htrap hnorm hstrict
  obtain ⟨J,_,hJ,_,_,_,_,_,hsmallActor⟩ :=
    Nonelementary.edge_normalizer_small_movers_knownSimple
      (e := e) (hz := hz) (hn := hn) hne₀ (by omega : 2 < replacementDistance h d) hc hct
  have hFT : F ≤ Q d.radical t := inf_le_right.trans (Q_le_adjacent_h d.radical ht hat)
  have hFN : F ≤ J ∧ ⁅J,F⁆ ≤ Q d.radical c := hsmallActor F hFT hfix.1
  have hE := EightMovers.edge_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hne₀ hcard (by omega : 2 < replacementDistance h d) hc hct
  have hEJ : E ≤ J := by
    rw [show E = _ from hE.1,hJ]
    exact inf_le_right
  have hFE : F ≤ E ∧ ⁅E,F⁆ ≤ Q d.radical c := by
    constructor
    · rw [show E = _ from hE.1,hJ]
      exact le_inf hFT hFN.1
    · exact (commutator_mono hEJ le_rfl).trans hFN.2
  have hEN : E ≤ normalizer (D : Set (FreeAmalgam d.radical)) :=
    small_mover_preserves_seed_fixer_knownSimple
      (e := e) (hz := hz) (hn := hn) hne₀ hcard (by omega : 2 < replacementDistance h d)
      hc hct F hFE.1
  refine ⟨hFE.1,hFE.2,hEN,sup_le ?_ hfix.2.2⟩
  have hEG : E ≤ stabilizer d.radical a := (SmallMover.join_le _ _ _ _).trans
    (fun _ hx => hx.2 _ (adjacent_symm d.radical hat))
  exact (le_inf hEN (hEG.trans (Z_normalized d.radical a))).trans
    (normalizer_inf_normalizer_le_normalizer_sup _ _)

include e hz hn in
/-- A strict trapped candidate cannot supply the source residual generation:
its literal mover and critical seed normalize a small fixer span outside the slice. -/
theorem trapped_strict_residual_not_le_knownSimple
    (hne₀ : ¬ IsElementaryAbelian 2 (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8)
    (hb : replacementDistance h d = 4)
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
    (e := e) (hz := hz) (hn := hn) hne₀ hcard hb p hsmall hat hct htrap hnorm hstrict
  have hf := SixteenUnequal.trapped_strict_seed_fixer_escape_knownSimple
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
        (DistanceFour.adjacent_seed_span_index_le_eight
          (e := e) (hz := hz) (hn := hn) (by omega : 2 < replacementDistance h d) p.start_color hat hct)
  exact hf.2.1 (le_sup_left.trans (residual_small_radius_le_slice_knownSimple (e := e)
    (by omega : 2 < replacementDistance h d) p.start_color Y hYV hYN hindex))

include e hz hn in
/-- A trapped nonnormalizing seed forces an unequal opposite mover to omit
the starting core. Its product with that whole core is the entire edge core. -/
theorem trapped_unequal_core_product_knownSimple
    (hne₀ : ¬ IsElementaryAbelian 2 (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8)
    (hb : replacementDistance h d = 4)
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
      (e := e) (hz := hz) (hn := hn) hne₀ hcard hb p.start_color hat hct hne hcore hXa
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    rw [p.start_color] at hh
    cases ht : color d.radical t <;> simp_all
  have hc : color d.radical c = false := by
    have hh := adjacent_color_ne d.radical hct
    rw [ht] at hh
    cases hc : color d.radical c <;> simp_all
  obtain ⟨_,_,_,hET,_,hEi,hEN,_⟩ := EightMovers.edge_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hne₀ hcard (by omega : 2 < replacementDistance h d) hc hct
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
    obtain ⟨_,_,hQJ,hJT,hQJi,hJi,_⟩ := EightMovers.edge_small_mover_knownSimple
      (e := e) (hz := hz) (hn := hn) hne₀ hcard (by omega : 2 < replacementDistance h d) p.start_color hat
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
    (hne₀ : ¬ IsElementaryAbelian 2 (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8)
    (hb : replacementDistance h d = 4)
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
      (DistanceFour.adjacent_seed_span_index_le_eight
        (e := e) (hz := hz) (hn := hn) (by omega : 2 < replacementDistance h d) p.start_color hat hct)
    have hi := relIndex_eq_one.mpr ((DistanceEight.U_le_Z d.radical c).trans
      (le_sup_left.trans hYB))
    omega
  have hescape : ¬ Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) := by
    intro htrap
    have hp := trapped_unequal_core_product_knownSimple
      (e := e) (hz := hz) (hn := hn) hne₀ hcard hb p hsmall hat hct hne htrap hnorm
    obtain ⟨_,_,_,hET,_,hEi,_⟩ := EightMovers.edge_small_mover_knownSimple
      (e := e) (hz := hz) (hn := hn) hne₀ hcard (by omega : 2 < replacementDistance h d) hc hct
    let := finite_stabilizer d.radical a
    have hres := SectionFive.index_two_opposite_generation (stabilizer d.radical a)
      (Q d.radical a) (Q d.radical t)
      (SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4)
      (Z d.radical z) (Q_le_adjacent_h d.radical ht hat)
      (fun _ hx => hx.2 _ (adjacent_symm d.radical hat)) hET
      (Q_normalized d.radical a) hEi hp.1 hgen
    exact trapped_strict_residual_not_le_knownSimple
      (e := e) (hz := hz) (hn := hn) hne₀ hcard hb p hsmall hat hct htrap hnorm hstrict hres.2
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
    (hne₀ : ¬ IsElementaryAbelian 2 (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8)
    (hb : replacementDistance h d = 4)
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
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  let N := normalizer (d.radical : Set d.overgroup)
  have hN := (Nonelementary.radical_normalizer_knownSimple
    (e := e) (hz := hz) (hn := hn) hne₀ hb2).1
  obtain ⟨u,hNimage,_⟩ := Nonelementary.normalizer_small_movers_knownSimple
    (e := e) (hz := hz) (hn := hn) hne₀ hb2
  have hker : s.projection.ker ≤ d.radical :=
    s.projection_kernel.symm ▸ replacement_core_le_radical h d
  have hindex : d.radical.relIndex N = 2 := by
    have hh := relIndex_mul_relIndex s.projection.ker d.radical N hker d.radical.le_normalizer
    rw [relIndex_ker,relIndex_ker,hNimage,
      card_map_of_injective (K := sylowCarrier) (MulAut.conj u).injective,card_sylowCarrier,
      SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s,hcard] at hh
    omega
  have hi : (Q d.radical (beta d.radical)).relIndex T = 2 := by
    rw [Q_beta,relIndex_map_map_of_injective _ _ (embedM_injective d.radical),←hN]
    exact hindex
  have hc : color d.radical c = false := by
    have hh := adjacent_color_ne d.radical hct
    change color d.radical c ≠ true at hh
    cases he : color d.radical c
    · rfl
    · exact (hh he).elim
  obtain ⟨_,_,_,hET,_,hEi,_⟩ := EightMovers.edge_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hne₀ hcard (by omega : 2 < replacementDistance h d) hc hct
  have hQT : Q d.radical (beta d.radical) ≤ T := by
    dsimp only [T]
    rw [Q_beta,←hN]
    exact map_mono d.radical.le_normalizer
  have hEiT : E.relIndex T = 4 := by
    have hh := relIndex_mul_relIndex E (Q d.radical (beta d.radical)) T hET hQT
    rw [hEi,hi] at hh
    exact hh.symm
  have hp := trapped_unequal_core_product_knownSimple
    (e := e) (hz := hz) (hn := hn) hne₀ hcard hb p hsmall (base_adjacent d.radical) hct hne htrap hnorm
  have hf := trapped_strict_fixer_normalized_knownSimple
    (e := e) (hz := hz) (hn := hn) hne₀ hcard hb p hsmall (base_adjacent d.radical) hct htrap hnorm hstrict
  exact ⟨hi,hEiT,hp.2.1,hp.2.2.1,hp.2.2.2,hf.1,hf.2.1,hf.2.2.2,
    trapped_strict_residual_not_le_knownSimple
      (e := e) (hz := hz) (hn := hn) hne₀ hcard hb p hsmall (base_adjacent d.radical) hct htrap hnorm hstrict⟩

include e hz hn in
/-- The unequal-mover part of source (5.7) at distance four, with the same
generating edge, conjugator and every overlapping vertex retained. -/
theorem unequal_backward_shift_knownSimple
    (hne₀ : ¬ IsElementaryAbelian 2 (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8)
    (hb : replacementDistance h d = 4)
    (hmodel : EightSelection.ThreeDuadMover h e hz hn d)
    {z delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4)
    (hdelta : Adjacent d.radical delta (p.walk.getVert 1))
    (hne : SmallMover.join (U d.radical delta) (Q d.radical delta)
        (Q d.radical (p.walk.getVert 1)) 4 ≠
      SmallMover.join (U d.radical (alpha d.radical)) (Q d.radical (alpha d.radical))
        (Q d.radical (p.walk.getVert 1)) 4)
    (hstrict : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical delta)) :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      ∃ g ∈ stabilizer d.radical (alpha d.radical),
        act d.radical g (p.walk.getVert 1) = t ∧
        Adjacent d.radical (act d.radical g delta) t ∧
        Q d.radical t ⊔ Z d.radical z = stabilizer d.radical (alpha d.radical) ∧
        2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical (act d.radical g delta)) ∧
        ∃ q : CriticalPath d.radical (replacementGeometry h d)
            (act d.radical g delta) (p.walk.getVert (p.walk.length-2)),
          q.walk.getVert 1 = t ∧
          ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i := by
  have hb2 : 2 < replacementDistance h d := by omega
  obtain ⟨g₀,hg₀,x,hx,hx3,hat,hjoint,hxJ,hgen,hgen'⟩ :=
    EightGenerating.paired_generating_selection_knownSimple
      (e := e) (hz := hz) (hn := hn) hne₀ hcard hb2 hmodel p hsmall
  let t := act d.radical g₀ (beta d.radical)
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have ha1 : Adjacent d.radical (alpha d.radical) (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  obtain ⟨g,hg,hgt⟩ := stabilizer_transitive_neighbors d.radical (alpha d.radical) ha1 hat
  change act d.radical g (p.walk.getVert 1) = t at hgt
  let c := act d.radical g delta
  have hct : Adjacent d.radical c t := by
    rw [←hgt]
    exact (adjacent_act_iff d.radical g _ _).mpr hdelta
  have hga : act d.radical g (alpha d.radical) = alpha d.radical := hg
  have hB : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map
      (MulAut.conj g⁻¹).toMonoidHom =
        B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      hb2 _ rfl ((stabilizer d.radical (alpha d.radical)).inv_mem hg))
  have hi : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c) := by
    change 2 < (B d.radical (alpha d.radical) _).relIndex (U d.radical (act d.radical g delta))
    rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
    exact hstrict
  have hne' : SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4 ≠
      SmallMover.join (U d.radical (alpha d.radical)) (Q d.radical (alpha d.radical))
        (Q d.radical t) 4 := by
    intro he
    apply hne
    apply map_injective (f := (MulAut.conj g⁻¹).toMonoidHom) (MulAut.conj g⁻¹).injective
    rwa [SmallMover.join_map _ (MulAut.conj g⁻¹).injective,
      SmallMover.join_map _ (MulAut.conj g⁻¹).injective,←U_act,←Q_act,←Q_act,←U_act,←Q_act,hga,hgt]
  exact ⟨t,hat,g,hg,hgt,hct,hgen,hi,
    unequal_edge_generating_backward_path_knownSimple
      (e := e) (hz := hz) (hn := hn) hne₀ hcard hb p hsmall hat hct hne' hgen hi⟩

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.EightUnequal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
