module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.NonelementaryMovers
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EightSmallMovers
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EightSelection

import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.FourOffenderImage

/-!
# Actual image-eight movers above distance two

The non-elementary radical image of order eight has a unique maximum small
mover. Its image is the intersection with the three-duad subgroup of its
Sylow normalizer. The model calculation depends only on that image, so
it applies at distance four as well as at larger distances. The literal
edge transport retains full moved covers of orders sixteen and thirty-two,
all central attachments and the larger relative normalizer.

These results supply the equal- and unequal-mover backward-selection
arguments in source (5.8), used in the initial choice of (5.12).
Source: Meierfrankenfeld--Stellmacher (1993), printed pp.918--920,924.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped commutatorElement IsMulCommutative Pointwise
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.EightMovers
local notation "S" => Equiv.Perm (Fin 6)
local notation "ρ" => naturalRepresentation (Fin 6)
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

include e hz hn in
/-- The actual image-eight radical has a unique maximum small mover of
quotient order four and radical index two. The larger normalizer's mover
restricts to this subgroup; both full covers are retained. -/
theorem radical_small_movers_knownSimple (hne : ¬ IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hcard8 : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8)
    (hb : 2 < replacementDistance h d) :
    let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
    let N := normalizer (d.radical : Set d.overgroup)
    let J := SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) d.radical 4
    ∃ u : S,
      N.map s.projection = sylowCarrier.map (MulAut.conj u).toMonoidHom ∧
      J = d.radical ⊓ SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) N 4 ∧
      SmallMover.Maximal (replacementMoved d) (pCore 2 d.overgroup) d.radical 4 = {J} ∧
      J.map s.projection = d.radical.map s.projection ⊓
        (D 6).map (MulAut.conj u).toMonoidHom ∧
      (pCore 2 d.overgroup).relIndex J = 4 ∧ J.relIndex d.radical = 2 ∧
      (centralizer (J : Set d.overgroup)).relIndex (replacementMoved d) = 4 ∧
      (centralizer (d.radical : Set d.overgroup)).relIndex (replacementMoved d) = 8 := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  let N := normalizer (d.radical : Set d.overgroup)
  have hE' : Nat.card (d.radical.map s.projection) = 8 := by
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
    exact hcard8
  have hne' : ¬ IsElementaryAbelian 2 (d.radical.map s.projection) := by
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
    exact hne
  obtain ⟨u,hN,_,hJN,hJNmap,_,_,hJNfixed⟩ :=
    Nonelementary.normalizer_small_movers_knownSimple
      (e := e) (hz := hz) (hn := hn) hne hb
  let D' := (D 6).map (MulAut.conj u).toMonoidHom
  let F := d.radical ⊓ D'.comap s.projection
  have hFmap : F.map s.projection = d.radical.map s.projection ⊓ D' := by
    apply le_antisymm
    · exact le_inf (map_mono inf_le_left) ((map_mono inf_le_right).trans (map_comap_le _ _))
    · rintro y ⟨⟨x,hx,rfl⟩,hy⟩
      exact mem_map_of_mem s.projection ⟨hx,hy⟩
  have hES : d.radical.map s.projection ≤ sylowCarrier.map (MulAut.conj u).toMonoidHom :=
    (map_mono d.radical.le_normalizer).trans_eq hN
  have hmodel := EightSmallMovers.conjugate_eight_model _ u hES hE' hne'
  have hFcard : Nat.card (F.map s.projection) = 4 := by rw [hFmap]; exact hmodel.1
  have hk : s.projection.ker ≤ d.radical := s.projection_kernel ▸ replacement_core_le_radical h d
  have hkF : s.projection.ker ≤ F := le_inf hk (ker_le_comap _ _)
  have hFi : (pCore 2 d.overgroup).relIndex F = 4 := by
    rw [←s.projection_kernel,relIndex_ker,hFcard]
  have hFfix : (centralizer (F : Set d.overgroup)).relIndex (replacementMoved d) ≤ 4 := by
    have hle : F ≤ N ⊓ D'.comap s.projection :=
      le_inf (inf_le_left.trans d.radical.le_normalizer) inf_le_right
    exact (relIndex_le_of_le_left (centralizer_le hle) index_ne_zero_of_finite).trans_eq hJNfixed
  have hbds (A : Subgroup d.overgroup) :
      2 ^ fixedCodim ρ (A.map s.projection) ≤
        (centralizer (A : Set d.overgroup)).relIndex (replacementMoved d) := by
    let := replacementMoved_normal h d
    rw [NormalElementaryQuotient.centralizer_index_eq_fixedCodim
      (replacementMoved d) s.projection s.surjective
      (s.projection_kernel.trans (moved_centralizer s).symm)]
    have hh := (cover_model s).fixedCodim_bounds (A.map s.projection)
    simp only [map_id] at hh
    exact Nat.pow_le_pow_right (by decide) hh.1
  have hsmall : SmallMover.Admissible (replacementMoved d) (pCore 2 d.overgroup) d.radical 4 F :=
    ⟨inf_le_left,hFi ▸ hFfix,hFfix⟩
  have himage (A : Subgroup d.overgroup)
      (ha : SmallMover.Admissible (replacementMoved d) (pCore 2 d.overgroup) d.radical 4 A)
      (hcard : 4 ≤ Nat.card (A.map s.projection)) : A.map s.projection = F.map s.projection := by
    rw [hFmap]
    exact hmodel.2 _ (map_mono ha.1) hcard
      ((Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp ((hbds A).trans ha.2.2))
  have hfix : replacementMoved d ≤ centralizer (s.projection.ker : Set d.overgroup) := by
    rw [s.projection_kernel,←moved_centralizer s]
    exact le_centralizer_iff.mpr le_rfl
  have hmax : SmallMover.Maximal (replacementMoved d) (pCore 2 d.overgroup) d.radical 4 = {F} := by
    ext A
    rw [←s.projection_kernel,SmallMover.maximal_iff_image_maximal
      s.projection (replacementMoved d) d.radical 4 hk hfix]
    constructor
    · rintro ⟨ha,hkA,hm⟩
      rw [s.projection_kernel] at ha hm
      have hc : 4 ≤ Nat.card (A.map s.projection) := hFcard ▸ hm F hsmall
      exact Set.mem_singleton_iff.mpr (map_injective_of_ker_le s.projection hkA hkF (himage A ha hc))
    · rintro rfl
      refine ⟨s.projection_kernel ▸ hsmall,hkF,?_⟩
      intro A ha
      rw [s.projection_kernel] at ha
      by_cases hc : 4 ≤ Nat.card (A.map s.projection)
      · rw [himage A ha hc]
      · rw [hFcard]; omega
  have hj : SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) d.radical 4 = F := by
    rw [SmallMover.join,hmax,sSup_singleton]
  have hFfixeq : (centralizer (F : Set d.overgroup)).relIndex (replacementMoved d) = 4 := by
    have hlo : 2 ≤ fixedCodim ρ (F.map s.projection) := by
      by_contra! hh
      have hFn : F.map s.projection ≠ ⊥ := by intro he; rw [he,card_bot] at hFcard; omega
      have hle : fixedCodim ρ (F.map s.projection) ≤ 1 := by omega
      obtain ⟨t,_,ht,he⟩ := Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointCoreTranspositionFixed.small_image_eq_zpowers
        _ hFn hle
      rw [he,Nat.card_zpowers,ht.orderOf] at hFcard
      omega
    have hpow := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hlo
    have hh := hbds F
    omega
  have hidx : F.relIndex d.radical = 2 := by
    have hh := relIndex_mul_relIndex s.projection.ker F d.radical hkF inf_le_left
    rw [s.projection_kernel,hFi,←s.projection_kernel,relIndex_ker,hE'] at hh
    omega
  have hlarge : 4 < (centralizer (d.radical : Set d.overgroup)).relIndex (replacementMoved d) := by
    by_contra! hh
    have he := himage d.radical ⟨le_rfl,by
      rw [←s.projection_kernel,relIndex_ker,hE']; omega,hh⟩ (by rw [hE']; decide)
    have hc := congrArg (fun A : Subgroup S => Nat.card A) he
    rw [hE',hFcard] at hc
    omega
  refine ⟨u,hN,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hj,hJN,←inf_assoc,inf_eq_left.mpr d.radical.le_normalizer]
  · rwa [hj]
  · rw [hj]; exact hFmap
  · rw [hj]; exact hFi
  · rw [hj]; exact hidx
  · rw [hj]; exact hFfixeq
  · exact SylowKernelMovement.cover_two_group_fixed_index_eight s d.radical
      (replacement_radical_isPGroup h d) hlarge

include e hz hn in
/-- On every actual edge, the source small mover is the intersection of
the edge core with the larger normalizer's small mover. It has four images,
index two and quadratic action on the whole moved cover. -/
theorem edge_small_mover_knownSimple (hne : ¬ IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hcard8 : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8)
    (hb : 2 < replacementDistance h d)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) :
    let T := normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓ stabilizer d.radical a
    let J := SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4
    J = Q d.radical t ⊓ SmallMover.join (U d.radical a) (Q d.radical a) T 4 ∧
      SmallMover.Maximal (U d.radical a) (Q d.radical a) (Q d.radical t) 4 = {J} ∧
      Q d.radical a ≤ J ∧ J ≤ Q d.radical t ∧
      (Q d.radical a).relIndex J = 4 ∧ J.relIndex (Q d.radical t) = 2 ∧
      Q d.radical t ≤ normalizer (J : Set (FreeAmalgam d.radical)) ∧
      ⁅⁅U d.radical a,J⁆,J⁆ = ⊥ ∧
      (centralizer (J : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) = 4 ∧
      (centralizer (Q d.radical t : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) = 8 := by
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨i,hinj,hir,hiR,hiQ,hiU⟩ := SylowAdjacent.edge_coordinates (h := h) hc ha hat
  let N := normalizer (d.radical : Set d.overgroup)
  let F := SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) d.radical 4
  let J := SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4
  have hj : F.map i = J := by
    rw [SmallMover.join_map i hinj,hiU,hiQ,hiR]
  obtain ⟨u,_,hF,hmax,hFmap,hQi,hFi,hfix,hRfix⟩ :=
    radical_small_movers_knownSimple (e := e) (hz := hz) (hn := hn) hne hcard8 hb
  change F = _ at hF
  have hiN : N.map i = normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
      stabilizer d.radical a := by
    have hh : (normalizer (d.radical.map i : Set _)).comap i = N := by
      rw [comap_normalizer_eq_of_le_range (map_le_range _ _),comap_map_eq_self_of_injective hinj]
    rw [←hh,map_comap_eq,hiR,hir,inf_comm]
  have hQF : pCore 2 d.overgroup ≤ F := by
    let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
    apply SmallMover.kernel_le_join _ _ _ 4 (by decide) (replacement_core_le_radical h d)
    rw [←moved_centralizer s]
    exact le_centralizer_iff.mpr le_rfl
  have hFle : F ≤ d.radical := SmallMover.join_le _ _ _ _
  have hJT : J ≤ Q d.radical t := SmallMover.join_le _ _ _ _
  have hJi : J.relIndex (Q d.radical t) = 2 := by
    rw [←hj,←hiR,relIndex_map_map_of_injective _ _ hinj]
    exact hFi
  refine ⟨?_,?_,?_,hJT,?_,hJi,?_,?_,?_,?_⟩
  · have hh := congrArg (Subgroup.map i) hF
    rwa [hj,map_inf _ _ _ hinj,SmallMover.join_map i hinj,hiU,hiQ,hiR,hiN] at hh
  · have hh := SylowSmallMovers.maximal_map_singleton i hinj _ _ _ _ hmax
    rwa [hiU,hiQ,hiR,hj] at hh
  · change Q d.radical a ≤ J
    rw [←hj,←hiQ]; exact map_mono hQF
  · change (Q d.radical a).relIndex J = 4
    rw [←hj,←hiQ,relIndex_map_map_of_injective _ _ hinj]; exact hQi
  · exact (normal_subgroupOf_iff_le_normalizer hJT).mp (normal_of_index_eq_two hJi)
  · have hle : F ≤ SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) N 4 :=
      hF.le.trans inf_le_right
    have hh : ⁅⁅replacementMoved d,F⁆,F⁆ ≤
        ⁅⁅replacementMoved d,SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) N 4⁆,
          SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) N 4⁆ :=
      commutator_mono (commutator_mono le_rfl hle) hle
    have hzero := Nonelementary.normalizer_small_mover_quadratic_knownSimple
      (e := e) (hz := hz) (hn := hn) hne hb
    have hz : ⁅⁅replacementMoved d,F⁆,F⁆ = ⊥ := bot_unique (hh.trans_eq hzero)
    have hm := congrArg (Subgroup.map i) hz
    rwa [map_commutator,map_commutator,hiU,hj,Subgroup.map_bot] at hm
  · change (centralizer (J : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) = 4
    rw [←hj,←hiU,SmallMover.centralizer_index_map i hinj]; exact hfix
  · rw [←hiR,←hiU,SmallMover.centralizer_index_map i hinj]; exact hRfix

include e hz hn in
/-- The image-eight small mover is one of the three actual order-four
offenders. The remaining two-transposition branch is explicit. -/
theorem radical_mover_image_cases_knownSimple (hne : ¬ IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hcard8 : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8)
    (hb : 2 < replacementDistance h d) :
    let J := SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) d.radical 4
    IsConjugateTo (J.map (SourceReduction.projection h e hz hn d))
      (disjointTranspositions 6 2) ∨ EightSelection.ThreeDuadMover h e hz hn d := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  let J := SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) d.radical 4
  obtain ⟨u,hN,_,_,hJ,_,_,_,_⟩ := radical_small_movers_knownSimple
    (e := e) (hz := hz) (hn := hn) hne hcard8 hb
  obtain ⟨A,hA,hcard,hoff⟩ := large_distance_thompson_contains_four_offender_knownSimple
    (e := e) (hz := hz) (hn := hn) (by omega : 2 < replacementDistance h d)
  rw [←SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s] at hA
  have hE : Nat.card (d.radical.map s.projection) = 8 := by
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
    exact hcard8
  have hne' : ¬ IsElementaryAbelian 2 (d.radical.map s.projection) := by
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
    exact hne
  have hES : d.radical.map s.projection ≤ sylowCarrier.map (MulAut.conj u).toMonoidHom :=
    (map_mono d.radical.le_normalizer).trans_eq hN
  have hAE : A ≤ d.radical.map s.projection :=
    hA.trans (map_mono (sSup_le fun _ hB => hB.1))
  have he := (EightSmallMovers.conjugate_eight_model _ u hES hE hne').2
    A hAE hcard.ge (by
      have hrank : Representation.BinaryOffender.rank A = 2 := by
        rw [Representation.BinaryOffender.rank,hcard]; decide
      exact hoff.2.trans_eq hrank)
  have hJA : J.map (SourceReduction.projection h e hz hn d) = A := by
    rw [←SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
    exact hJ.trans he.symm
  change IsConjugateTo (J.map (SourceReduction.projection h e hz hn d)) _ ∨ _
  rw [hJA]
  rcases FourOffenderImage.four_offender_models A hcard hoff with hp | heven | hm
  · exact Or.inl hp
  · exact Or.inr (Or.inr (hJA.symm ▸ heven))
  · exact Or.inr (Or.inl (hJA.symm ▸ hm))

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.EightMovers
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
