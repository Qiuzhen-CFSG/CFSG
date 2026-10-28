module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowUnequalFixer
public import Theory.GroupTheory.NormalizedSupConsequences
public import Mathlib.GroupTheory.IndexNormal
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowPairedFixer
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeFullKernel

/-!
# The unequal-mover residual step on the natural replacement

An opposite small mover E has index two in the same edge core T. If it
omits Q_a, then Q_a E = T. Whenever T and the actual critical seed generate
the starting stabilizer, E and that same seed have index at most two and
contain its two-residual.

If unequal E contains Q_a, compare the central omega subgroups of E and
the starting mover J. They have equal orders by conjugation along their
common edge. Characteristic two identifies them with the fixed subgroups
in X_a. Full-X central generation would make the fixed indices on X_a
agree with those on U_a, but J has index four and E has index greater
than four. Thus this branch forces failure of full-X central generation.

A trapped nonnormalizing span already forces full-X central generation
at every component vertex. It therefore lies in the first alternative,
which contradicts SylowUnequalFixer's proved residual obstruction. This
completes the unequal-mover trapped exclusion on the same selected edge.
SylowStrictShift applies it to the actual backward walk and original radical.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.5)(c) and (5.7), printed pp.915--919. The generic index-two and
omega-order arguments are adapted from Exceptional/OriginalSylow/
BorelOpposite and BorelOppositePair. All mover, kernel and conjugation
hypotheses here are proved on the natural replacement's own graph.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
private theorem residual_le_of_index_le_two {H : Type*} [Group H]
    (P F : Subgroup H) [Finite P] (hi : F.relIndex P ≤ 2) :
    (pResidual 2 P).map P.subtype ≤ F := by
  have hpos : F.relIndex P ≠ 0 := index_ne_zero_of_finite
  have hc : F.relIndex P = 1 ∨ F.relIndex P = 2 := by omega
  rcases hc with hc | hc
  · exact (map_subtype_le _).trans (relIndex_eq_one.mp hc)
  · have hc' : (F.subgroupOf P).index = 2 := hc
    let : (F.subgroupOf P).Normal := normal_of_index_eq_two hc'
    have hquot : IsPGroup 2 (P ⧸ F.subgroupOf P) :=
      IsPGroup.of_card (n := 1) (by simpa only [←index_eq_card,pow_one] using hc')
    exact map_le_iff_le_comap.mpr (show pResidual 2 P ≤ F.subgroupOf P from
      sInf_le ⟨inferInstance,hquot⟩)

private theorem index_two_opposite_generation {H : Type*} [Group H]
    (P Q T J A : Subgroup H) [Finite P]
    (hQT : Q ≤ T) (hTP : T ≤ P) (hJT : J ≤ T)
    (hQN : P ≤ normalizer (Q : Set H)) (hi : J.relIndex T = 2)
    (hnot : ¬ Q ≤ J) (hgen : T ⊔ A = P) :
    (J ⊔ A).relIndex P ≤ 2 ∧ (pResidual 2 P).map P.subtype ≤ J ⊔ A := by
  let F := J ⊔ A
  have hFP : F ≤ P := sup_le (hJT.trans hTP) (le_sup_right.trans hgen.le)
  let : Finite F := Finite.of_injective (inclusion hFP) (inclusion_injective _)
  have hJT' : J ≤ Q ⊔ J := le_sup_right
  have hsupT : Q ⊔ J ≤ T := sup_le hQT hJT
  have hm := relIndex_mul_relIndex J (Q ⊔ J) T hJT' hsupT
  rw [hi] at hm
  have hd : J.relIndex (Q ⊔ J) ∣ 2 := ⟨(Q ⊔ J).relIndex T,by omega⟩
  have hQJ : Q ⊔ J = T := by
    rcases Nat.prime_two.eq_one_or_self_of_dvd _ hd with he | he
    · exact (hnot (le_sup_left.trans (relIndex_eq_one.mp he))).elim
    · rw [he] at hm
      have hone : (Q ⊔ J).relIndex T = 1 := by omega
      exact le_antisymm hsupT (relIndex_eq_one.mp hone)
  have hQF : Q ⊔ F = P := by
    change Q ⊔ (J ⊔ A) = P
    rw [←sup_assoc,hQJ,hgen]
  have hindex : F.relIndex P ≤ 2 := by
    rw [←hQF,relIndex_sup_of_normalizes Q F (hFP.trans hQN)]
    have hFT : F.relIndex T ≤ 2 := by
      have hz : J.relIndex T ≠ 0 := by omega
      exact (relIndex_le_of_le_left (show J ≤ F from le_sup_left) hz).trans_eq hi
    let : Finite T := Finite.of_injective (inclusion hTP) (inclusion_injective _)
    have hFTzero : F.relIndex T ≠ 0 := index_ne_zero_of_finite
    exact (relIndex_le_of_le_right hQT hFTzero).trans hFT
  exact ⟨hindex,residual_le_of_index_le_two P F hindex⟩

private theorem omegaCenter_eq_fixed_of_selfcentralizing
    {H : Type*} [Group H] (P Q J : Subgroup H)
    (hQJ : Q ≤ J) (hJP : J ≤ P)
    (hself : P ⊓ centralizer (Q : Set H) ≤ Q) :
    omegaCenter J = omegaCenter Q ⊓ centralizer (J : Set H) := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxJ,hx2,hxc⟩ := mem_omegaCenter_iff.mp hx
    have hxQ : x ∈ Q := hself ⟨hJP hxJ,fun y hy => hxc y (hQJ hy)⟩
    exact ⟨mem_omegaCenter_iff.mpr ⟨hxQ,hx2,fun y hy => hxc y (hQJ hy)⟩,hxc⟩
  · rintro ⟨hx,hxc⟩
    obtain ⟨hxQ,hx2,_⟩ := mem_omegaCenter_iff.mp hx
    exact mem_omegaCenter_iff.mpr ⟨hQJ hxQ,hx2,hxc⟩

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

include e hz hn in
/-- Omitting the starting core makes an opposite index-two mover generate
the actual local residual with the same critical actor. -/
theorem sixteen_opposite_residual_of_core_not_le_knownSimple
    (hb : 4 < replacementDistance h d)
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
  obtain ⟨_,hET,_,hEi,_,_⟩ := SylowAdjacent.sixteen_edge_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard hc hct
  let := finite_stabilizer d.radical a
  exact index_two_opposite_generation (stabilizer d.radical a) (Q d.radical a) (Q d.radical t)
    (SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4) A
    (Q_le_adjacent_h d.radical ht hat)
    (fun _ hx => hx.2 _ (adjacent_symm d.radical hat)) hET (Q_normalized d.radical a)
    hEi hnot hgen

include e hz hn in
/-- If an unequal neighboring mover contains the starting core, the full X
cannot be centrally generated. Equal omega orders contradict the two fixed indices. -/
theorem sixteen_unequal_containing_core_not_centrally_generated_knownSimple
    (hb : 4 < replacementDistance h d)
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
  obtain ⟨hQJ,hJT,_,_,_,_⟩ := SylowAdjacent.sixteen_edge_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard ha hat
  have hET : E ≤ Q d.radical t := SmallMover.join_le _ _ _ _
  have hfixE : 4 < (centralizer (E : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) :=
    (SylowAdjacent.sixteen_unequal_neighbor_indices_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hcard ha hat hct hne).2
  have hfixJ : (centralizer (J : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) = 4 := by
    obtain ⟨J',_,hJ',_,_,_,_,hfix,_⟩ := SylowSmallMovers.edge_normalizer_small_movers_knownSimple
      (e := e) (hz := hz) (hn := hn) hb ha hat
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
    have he := omegaCenter_eq_fixed_of_selfcentralizing (stabilizer d.radical a) (Q d.radical a) A
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
  have hea := omegaCenter_eq_fixed_of_selfcentralizing (stabilizer d.radical a) (Q d.radical a) J
    hQJ (hJT.trans hTP) hself
  have hec := omegaCenter_eq_fixed_of_selfcentralizing (stabilizer d.radical a) (Q d.radical a) E
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
/-- The source alternative with an unequal mover cannot be trapped at a
strict slice on the same generating edge. Both missing premises are discharged. -/
theorem sixteen_unequal_trapped_strict_impossible_knownSimple
    (hb : 4 < replacementDistance h d)
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
      (e := e) (hz := hz) (hn := hn) hb hcard p.start_color hat hct hne hcore hXa
  have hg := sixteen_opposite_residual_of_core_not_le_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard p.start_color hat hct (Z d.radical z) hgen hnot
  exact sixteen_trapped_strict_residual_not_le_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard p hsmall hat hct htrap hnorm hstrict hg.2

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
