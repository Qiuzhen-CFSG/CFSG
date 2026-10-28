module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.NonelementaryMovers
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowUnequalResidual
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowUnequalFixer
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowPairedFixer
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowAdjacent
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowUnequalKernel
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTrappedExclusion
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.NonnormalSelection

/-!
# Unequal-mover initial selection in the image-sixteen branch

The actual edge small mover is a normal subgroup of index two and acts
quadratically on the full moved cover. Two unequal neighboring movers have
equal orders, but the neighboring mover has fixed index greater than four
on the starting cover. If a trapped nonnormalizing seed is present, the
source full-X calculation gives central generation at every component
vertex. Comparing the complete omega centers then shows that the neighboring
mover omits the starting two-core.

Consequently the neighboring mover and critical endpoint generate the
local residual. The full reverse critical kernel lies in that mover, so
both actors normalize its full-seed fixer joined with the starting seed.
The section has order at most eight. The residual small-section theorem
puts it in the Baumann slice, contrary to the original strict slice.
This excludes trapping without an equal-mover or cover-order assumption.

The resulting backward critical path retains the chosen generating edge,
the actual transporter and every overlapping vertex. For a strict forward
slice, its endpoints are two seeds of the selected orbit, proving that
orbit nonabelian. For a small forward slice, the same backward path has
a small predecessor slice; the already proved residual-rotation selection
applies. Both applications are on the literal minimum characteristic
replacement, with moving covers sixteen and thirty-two and all central
attachments retained.

These results close the unequal-mover part of initial selection in the
order-sixteen image. Equal movers, the remaining order-eight images, the
independent selected terminal contradiction and unconditional
DistanceFourInput assembly remain separate obligations.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.5)(c), (5.7)--(5.8), printed pp.915--920, and their use in
(5.12), p.924. The argument reuses the existing source model and generic
relative-normality lemmas; the distance-four kernel estimate replaces the
beyond-four radius-commutativity shortcut.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped commutatorElement Pointwise IsMulCommutative
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.SixteenUnequal
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}
local notation "S" => Equiv.Perm (Fin 6)

private theorem sixteen_nonelementary
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16) :
    ¬ IsElementaryAbelian 2 (d.radical.map (SourceReduction.projection h e hz hn d)) := by
  intro hel
  have hnon : d.radical.map (SourceReduction.projection h e hz hn d) ≠ ⊥ := by
    intro he
    rw [he,card_bot] at hcard
    omega
  obtain ⟨B,hB,hBD | hBE,hAB⟩ := exists_conjugate_le_D_or_exceptional ⟨hnon,hel⟩
  · have hh := card_le_of_le hBD
    rw [←hAB.card_eq,hcard,show Nat.card (D 6) = 8 from card_disjointTranspositions (3 : Fin 4)] at hh
    omega
  · have hh := card_le_of_le hBE
    rw [←hAB.card_eq,hcard,card_exceptional] at hh
    omega

include e hz hn in
private theorem sixteen_edge_small_mover_knownSimple
    (hb : 2 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) :
    let J := SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4
    Q d.radical a ≤ J ∧ J ≤ Q d.radical t ∧
      (Q d.radical a).relIndex J = 8 ∧ J.relIndex (Q d.radical t) = 2 ∧
      Q d.radical t ≤ normalizer (J : Set (FreeAmalgam d.radical)) ∧
      ⁅⁅U d.radical a,J⁆,J⁆ = ⊥ := by
  have hT := SylowLarge.sixteen_edge_relative_normalizer_knownSimple
    (e := e) (hz := hz) (hn := hn) (by omega : 2 < replacementDistance h d) hcard ha hat
  obtain ⟨J,_,hj,hQJ,hJT,hQidx,hidx,_,_⟩ :=
    Nonelementary.edge_normalizer_small_movers_knownSimple
      (e := e) (hz := hz) (hn := hn) (sixteen_nonelementary hcard) hb ha hat
  dsimp only at hj hJT hidx ⊢
  rw [hT] at hj hJT hidx
  rw [hj]
  refine ⟨hQJ,hJT,hQidx,hidx,?_,?_⟩
  · exact (normal_subgroupOf_iff_le_normalizer hJT).mp (normal_of_index_eq_two hidx)
  · have hh := Nonelementary.edge_small_mover_quadratic_knownSimple
      (e := e) (hz := hz) (hn := hn) (sixteen_nonelementary hcard) hb ha hat
    dsimp only at hh
    rwa [hT,hj] at hh

include e hz hn in
private theorem sixteen_unequal_neighbor_indices_knownSimple
    (hb : 2 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a c t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hne : SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4 ≠
      SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4) :
    let E := SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4
    8 ≤ (Q d.radical a).relIndex E ∧
      4 < (centralizer (E : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) := by
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
  obtain ⟨hQJ,hJT,hQi,hJi,_⟩ := sixteen_edge_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard ha hat
  obtain ⟨_,hET,_,hEi,_⟩ := sixteen_edge_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard hc hct
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
  have hlarge : Q₀.relIndex J₀ = 8 := by
    have hh := relIndex_map_map_of_injective Q₀ J₀ S₀.subtype_injective
    rw [map_subgroupOf_eq_of_le hQS,map_subgroupOf_eq_of_le hJS] at hh
    exact hh.symm.trans hQi
  have hEl : 8 ≤ Q₀.relIndex E₀ := by
    rw [←hlarge]
    exact SmallMover.relIndex_le_of_card_eq_of_le Q₀ J₀ E₀ (comap_mono hQJ) hcard'
  refine ⟨?_,?_⟩
  · have hh := relIndex_map_map_of_injective Q₀ E₀ S₀.subtype_injective
    rw [map_subgroupOf_eq_of_le hQS,map_subgroupOf_eq_of_le hES] at hh
    rwa [hh]
  · by_contra hnidx
    have hi : (centralizer (E₀ : Set S₀)).relIndex U₀ ≤ 4 := by
      have hh := SmallMover.centralizer_index_map S₀.subtype S₀.subtype_injective U₀ E₀
      rw [map_subgroupOf_eq_of_le hUS,map_subgroupOf_eq_of_le hES] at hh
      rw [←hh]
      exact le_of_not_gt hnidx
    have he := SmallMover.eq_join_of_card_eq_of_index_le U₀ Q₀ T₀ 4 (by decide)
      (hjoin.symm ▸ comap_mono hQJ) (by rw [hjoin,hlarge]; decide)
      E₀ (comap_mono hET) (hjoin.symm ▸ hcard') hi
    rw [hjoin] at he
    have hh := congrArg (Subgroup.map S₀.subtype) he
    rw [map_subgroupOf_eq_of_le hES,map_subgroupOf_eq_of_le hJS] at hh
    exact hne hh

include e hz hn in
private theorem small_mover_preserves_seed_fixer_knownSimple
    (hb : 2 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t)
    (A : Subgroup (FreeAmalgam d.radical))
    (hA : A ≤ SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4) :
    let J := SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4
    J ≤ normalizer ((Z d.radical a ⊓ centralizer (A : Set (FreeAmalgam d.radical)) :
      Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) := by
  let J := SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4
  obtain ⟨_,hJT,_,_,_,hquad⟩ := sixteen_edge_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard ha hat
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
private theorem sixteen_opposite_residual_of_core_not_le_knownSimple
    (hb : 2 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a c t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (A : Subgroup (FreeAmalgam d.radical))
    (hgen : Q d.radical t ⊔ A = stabilizer d.radical a)
    (hnot : ¬ Q d.radical a ≤ SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4) :
    let E := SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4
    (E ⊔ A).relIndex (stabilizer d.radical a) ≤ 2 ∧ Ltilde d.radical a ≤ E ⊔ A := by
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    rw [ha] at hh
    cases he : color d.radical t <;> simp_all
  have hc : color d.radical c = false := by
    have hh := adjacent_color_ne d.radical hct
    rw [ht] at hh
    cases he : color d.radical c <;> simp_all
  obtain ⟨_,hET,_,hEi,_,_⟩ := sixteen_edge_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard hc hct
  let := finite_stabilizer d.radical a
  exact SectionFive.index_two_opposite_generation (stabilizer d.radical a) (Q d.radical a) (Q d.radical t)
    (SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4) A
    (Q_le_adjacent_h d.radical ht hat)
    (fun _ hx => hx.2 _ (adjacent_symm d.radical hat)) hET (Q_normalized d.radical a)
    hEi hnot hgen

include e hz hn in
private theorem sixteen_unequal_containing_core_not_centrally_generated_knownSimple
    (hb : 2 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
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
  obtain ⟨hQJ,hJT,_,_,_,_⟩ := sixteen_edge_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard ha hat
  have hET : E ≤ Q d.radical t := SmallMover.join_le _ _ _ _
  have hfixE : 4 < (centralizer (E : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) :=
    (sixteen_unequal_neighbor_indices_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hcard ha hat hct hne).2
  have hfixJ : (centralizer (J : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) = 4 := by
    obtain ⟨J',_,hJ',_,_,_,_,hfix,_⟩ := Nonelementary.edge_normalizer_small_movers_knownSimple
      (e := e) (hz := hz) (hn := hn) (sixteen_nonelementary hcard) hb ha hat
    rw [SylowLarge.sixteen_edge_relative_normalizer_knownSimple
      (e := e) (hz := hz) (hn := hn) hb2 hcard ha hat] at hJ'
    change J = _ at hJ'
    rwa [hJ']
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
private theorem trapped_strict_seed_fixer_escape_knownSimple
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
    (centralizer (F : Set (FreeAmalgam d.radical))).relIndex (U d.radical c) ≤ 2 ∧
      ¬ D ≤ B d.radical a ((replacementGeometry h d).Z_normal _) ∧
      Z d.radical z ≤ normalizer ((D ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) :
        Set (FreeAmalgam d.radical)) := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let F := Z d.radical z ⊓ Q d.radical a
  let D := Z d.radical c ⊓ centralizer (F : Set (FreeAmalgam d.radical))
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hline : Nat.card (⁅Z d.radical c,F⁆ : Subgroup (FreeAmalgam d.radical)) = 2 := by
    have hh := (nonnormal_backward_kernel_line s hc hb p hsmall hat hct
      (by simpa only [hl] using htrap) hnorm).1
    rw [commutator_comm]
    exact hh
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
    (card_le_of_le (commutator_mono (DistanceEight.U_le_Z d.radical c) le_rfl)).trans_eq hline
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
private theorem sixteen_trapped_strict_fixer_normalized_knownSimple
    (hb : replacementDistance h d = 4)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
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
    Nonelementary.edge_normalizer_small_movers_knownSimple
      (e := e) (hz := hz) (hn := hn) (sixteen_nonelementary hcard) (by omega : 2 < replacementDistance h d) hc hct
  have hT := SylowLarge.sixteen_edge_relative_normalizer_knownSimple
    (e := e) (hz := hz) (hn := hn) (by omega : 2 < replacementDistance h d) hcard hc hct
  rw [hT] at hJ
  have hFT : F ≤ Q d.radical t := inf_le_right.trans (Q_le_adjacent_h d.radical ht hat)
  have hFE : F ≤ E ∧ ⁅E,F⁆ ≤ Q d.radical c := by
    have hh := hsmallActor F hFT hfix.1
    rwa [←hJ] at hh
  have hEN : E ≤ normalizer (D : Set (FreeAmalgam d.radical)) :=
    small_mover_preserves_seed_fixer_knownSimple
      (e := e) (hz := hz) (hn := hn) (by omega : 2 < replacementDistance h d) hcard hc hct F hFE.1
  refine ⟨hFE.1,hFE.2,hEN,sup_le ?_ hfix.2.2⟩
  have hEG : E ≤ stabilizer d.radical a := (SmallMover.join_le _ _ _ _).trans
    (fun _ hx => hx.2 _ (adjacent_symm d.radical hat))
  exact (le_inf hEN (hEG.trans (Z_normalized d.radical a))).trans
    (normalizer_inf_normalizer_le_normalizer_sup _ _)

include e hz hn in
private theorem sixteen_trapped_strict_residual_not_le_knownSimple
    (hb : replacementDistance h d = 4)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
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
  have hnormal := sixteen_trapped_strict_fixer_normalized_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard p hsmall hat hct htrap hnorm hstrict
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
        (DistanceFour.adjacent_seed_span_index_le_eight
          (e := e) (hz := hz) (hn := hn) (by omega : 2 < replacementDistance h d) p.start_color hat hct)
  exact hf.2.1 (le_sup_left.trans (residual_small_radius_le_slice_knownSimple (e := e)
    (by omega : 2 < replacementDistance h d) p.start_color Y hYV hYN hindex))

include e hz hn in
private theorem sixteen_unequal_trapped_strict_impossible_knownSimple
    (hb : replacementDistance h d = 4)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a z c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hne : SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4 ≠
      SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4)
    (hgen : Q d.radical t ⊔ Z d.radical z = stabilizer d.radical a)
    (htrap : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    (hnorm : ¬ Z d.radical z ≤ normalizer
      ((Z d.radical c ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) :
        Set (FreeAmalgam d.radical)))
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c)) : False := by
  have hX := SylowPairedFixer.trapped_nonnormalized_full_kernel_knownSimple
    (e := e) (hz := hz) (hn := hn) (by omega : 2 < replacementDistance h d)
      p hsmall hat hct htrap hnorm
  have hXa := X_central_generation_all p.end_color hX.1 a p.start_color
  have hnot : ¬ Q d.radical a ≤
      SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4 := by
    intro hcore
    exact sixteen_unequal_containing_core_not_centrally_generated_knownSimple
      (e := e) (hz := hz) (hn := hn) (by omega : 2 < replacementDistance h d) hcard p.start_color hat hct hne hcore hXa
  have hg := sixteen_opposite_residual_of_core_not_le_knownSimple
    (e := e) (hz := hz) (hn := hn) (by omega : 2 < replacementDistance h d) hcard p.start_color hat hct (Z d.radical z) hgen hnot
  exact sixteen_trapped_strict_residual_not_le_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard p hsmall hat hct htrap hnorm hstrict hg.2


include e hz hn in
/-- The unequal-mover part of source (5.7) at distance four, with the same
generating edge, conjugator and every overlapping vertex retained. -/
theorem unequal_backward_shift_knownSimple
    (hb : replacementDistance h d = 4)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
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
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  obtain ⟨⟨T,hT⟩,_,_⟩ := SylowLarge.sixteen_original_restriction_knownSimple hb2 hcard
  obtain ⟨t,hat,hgen⟩ := SylowNormalizer.sylow_critical_generating_neighbor_knownSimple
    (e := e) (hz := hz) (hn := hn) hb2 T hT p
  rw [SylowLarge.sixteen_edge_relative_normalizer_knownSimple
    (e := e) (hz := hz) (hn := hn) hb2 hcard rfl hat] at hgen
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have ha1 : Adjacent d.radical (alpha d.radical) (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  obtain ⟨g,hg,hgt⟩ := stabilizer_transitive_neighbors d.radical (alpha d.radical) ha1 hat
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
  have hnorm := eligible_generating_seed_not_normalized s hb2 hat hct hgen
    (fun hh => by have he := relIndex_eq_one.mpr hh; omega)
  have hc : color d.radical c = false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hct
    change false ≠ color d.radical t at h1
    cases hc : color d.radical c <;> cases ht : color d.radical t <;> simp_all
  refine ⟨t,hat,g,hg,hgt,hct,hgen,hi,?_⟩
  by_cases htrap : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2))
  · exact (sixteen_unequal_trapped_strict_impossible_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hcard p hsmall hat hct hne' hgen htrap hnorm hi).elim
  · let w : (cosetGraph d.radical).Walk c (alpha d.radical) :=
      .cons ((cosetGraph_adj d.radical _ _).mpr hct)
        (.cons ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat)) .nil)
    have hw : w.length = 2 := rfl
    let q := p.prepend_two (Nat.le_of_lt hb2) hc w hw htrap
    have hqt : q.walk.getVert 1 = t := by
      simp only [q,CriticalPath.prepend_two_walk,SimpleGraph.Walk.getVert_append,
        hw,show 1<2 from by decide,ite_true,w,SimpleGraph.Walk.getVert_cons_succ,
        SimpleGraph.Walk.getVert_zero]
    exact ⟨q,hqt,fun i hi => p.prepend_two_overlap _ _ _ _ _ hi⟩

include e hz hn in
/-- A strict forward slice with unequal neighboring movers supplies initial
nonabelian large-slice selection, including both full moving covers. -/
theorem large_forward_initial_selection_knownSimple
    (hb : replacementDistance h d = 4)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hstrict : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)))
    (hne : SmallMover.join (U d.radical (p.walk.getVert 2)) (Q d.radical (p.walk.getVert 2))
        (Q d.radical (p.walk.getVert 1)) 4 ≠
      SmallMover.join (U d.radical (alpha d.radical)) (Q d.radical (alpha d.radical))
        (Q d.radical (p.walk.getVert 1)) 4) :
    ∃ w, ∃ r : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) w,
      ⁅localZSpan d.radical (r.walk.getVert 2) (alpha d.radical),
        localZSpan d.radical (r.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥ ∧
      2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (r.walk.getVert 2)) := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  refine ⟨z,p,?_,hstrict⟩
  by_cases hlarge : 4 ≤ (Q d.radical z).relIndex (Z d.radical (alpha d.radical))
  · exact large_image_selected_span_nonabelian s hc hb p hlarge
  have hsmall : (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4 := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hct : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  obtain ⟨t,hat,g,hg,hgt,hct,hgen,hi,q,hq,hover⟩ :=
    unequal_backward_shift_knownSimple hb hcard p hsmall hct hne hstrict
  let P := localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)
  have hstart : Z d.radical (act d.radical g (p.walk.getVert 2)) ≤ P := by
    rw [Z_act]
    exact (map_mono (Z_le_localZSpan d.radical _ _)).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp (localZSpan_normalized d.radical _ _
        ((stabilizer d.radical (alpha d.radical)).inv_mem hg)))
  have hend : Z d.radical (p.walk.getVert (p.walk.length-2)) ≤ P := by
    rw [hl]
    exact Z_le_localZSpan d.radical _ _
  intro hzero
  exact critical_Z_commutator_ne_bot s hc q
    (le_bot_iff.mp ((commutator_mono hstart hend).trans_eq hzero))

include e hz hn in
/-- On a small forward slice, any strict unequal neighbor constructs a
backward path with that small predecessor slice. The earlier residual
rotation then supplies initial selection on the literal replacement. -/
theorem small_forward_initial_selection_knownSimple
    (hb : replacementDistance h d = 4)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {z delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hslice : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) ≤ 2)
    (hdelta : Adjacent d.radical delta (p.walk.getVert 1))
    (hne : SmallMover.join (U d.radical delta) (Q d.radical delta)
        (Q d.radical (p.walk.getVert 1)) 4 ≠
      SmallMover.join (U d.radical (alpha d.radical)) (Q d.radical (alpha d.radical))
        (Q d.radical (p.walk.getVert 1)) 4)
    (hstrict : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical delta)) :
    ∃ w, ∃ r : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) w,
      ⁅localZSpan d.radical (r.walk.getVert 2) (alpha d.radical),
        localZSpan d.radical (r.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥ ∧
      2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (r.walk.getVert 2)) := by
  have hsmall := small_slice_critical_indices_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hslice
  obtain ⟨t,hat,g,hg,hgt,hct,hgen,hi,q,hq,hover⟩ :=
    unequal_backward_shift_knownSimple hb hcard p (by omega) hdelta hne hstrict
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hmid : q.walk.getVert 2 = alpha d.radical := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (Nat.zero_le _)
  apply initial_selection_of_small_predecessor_at_knownSimple
    (e := e) (hz := hz) (hn := hn) hb q
  rw [hmid,hl]
  exact hslice


end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.SixteenUnequal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
