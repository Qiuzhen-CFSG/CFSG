module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.LocalImages.CriticalTwo
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.LocalImages.TranspositionCover
/-!
# The critical transposition and its whole-cover line

The critical image is already known to have order two. Its larger centralizing
kernel image cannot act quadratically on the whole augmentation cover. The
finite fixer calculation therefore identifies its generator as a transposition.
On either possible moved cover its commutator has order two, and faithfulness
of the natural quotient makes that line disjoint from the component-fixed
attachment. All statements transport through the actual opposite-edge map.

The odd transposition also proves that the literal source projection is onto
S₆, without local-image, plane-intersection or paired-orbit hypotheses. The
whole-cover and selected-orbit applications are in CriticalTransposition.Source.
Source: MS93 (3.3)(ii)(2) and (3.6), printed pp.866--871. The entire order-32
cover is retained; no natural complement is chosen.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.LocalImages
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
open LargeDistance PlaneMovement
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
  (d : Replacement L R)

include h e hz hn in
/-- The literal opposite-edge coordinates identify the initial Z-image as
one transposition. Both whole moved-cover and edge-layer maps are retained. -/
theorem critical_transposition_coordinates_with_edge
    (hb : replacementDistance h d = 2)
    (hlarge : ¬ core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical))
    {c : Vertex d.radical}
    (hc : CriticalPair d.radical (alpha d.radical) c
      ((replacementGeometry h d).exists_critical _ rfl)) :
    ∃ (b : Vertex d.radical) (i : d.overgroup →* FreeAmalgam d.radical)
      (A : Subgroup d.overgroup),
      Function.Injective i ∧ Adjacent d.radical (alpha d.radical) b ∧
      Adjacent d.radical c b ∧ A ≤ d.radical ∧
      A.map i = Z d.radical (alpha d.radical) ∧
      (replacementMoved d).map i = U d.radical c ∧
      (omegaCenter d.radical).map i = Z d.radical b ∧
      (pResidual 2 d.overgroup).map i = Ltilde d.radical c ∧
      d.radical.map i = Q d.radical b ∧
      ∃ t : Equiv.Perm (Fin 6), t.IsSwap ∧
        A.map (Recognition.sourceProjection h e hz hn d) = zpowers t := by
  obtain ⟨A,Y,hAY,hYR,hAc,hYA,hne,_,_,hfix,hindex,
      b,i,hi,hAm,hab,hcb,hYm,hiW,hiS,hiL,hiR,_⟩ :=
    critical_image_data_coordinates_with_edge h e hz hn d hb hlarge hc
  let q := Recognition.sourceProjection h e hz hn d
  let := hAc
  have hp : IsPGroup 2 (Y.map q) :=
    ((replacement_radical_isPGroup h d).of_injective (inclusion hYR) (inclusion_injective _)).map q
  have hcent : Y.map q ≤ centralizer (A.map q : Set (Equiv.Perm (Fin 6))) := by
    rintro _ ⟨y,hy,rfl⟩ _ ⟨a,ha,rfl⟩
    exact (map_mul q a y).symm.trans ((congrArg q (hYA hy a ha)).trans (map_mul q y a))
  have hnq := critical_image_nonquadratic h e hz hn d hb hlarge hc hab hcb Y i hi hYm hiW hiS
  have hnon : A.map q ≠ ⊥ := by
    intro he
    exact hne ((Recognition.sourceProjection_kernel h e hz hn d) ▸
      (Subgroup.map_eq_bot_iff A).mp he)
  obtain ⟨t,ht,ht1⟩ := (A.map q).bot_or_exists_ne_one.resolve_left hnon
  let : IsElementaryAbelian 2 (A.map q) := IsElementaryAbelian.map _
  have hswap := isSwap_of_nonquadratic_fixer (A.map q) (Y.map q) hp
    (map_mono hAY) hcent hfix hnq ht ht1
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) t ht)
  have hcard : Nat.card (A.map q) = 2 := hindex.symm.trans
    (critical_image_two h e hz hn d hb hlarge hc)
  have he : A.map q = zpowers t := by
    apply (eq_of_le_of_card_ge (zpowers_le.mpr ht) ?_).symm
    rw [hcard,Nat.card_zpowers,hswap.orderOf]
  exact ⟨b,i,A,hi,hab,hcb,hAY.trans hYR,hAm,hiW,hiS,hiL,hiR,t,hswap,he⟩

include h e hz hn in
/-- Original transposition coordinates, retaining their public interface. -/
theorem critical_transposition_coordinates
    (hb : replacementDistance h d = 2)
    (hlarge : ¬ core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical))
    {c : Vertex d.radical}
    (hc : CriticalPair d.radical (alpha d.radical) c
      ((replacementGeometry h d).exists_critical _ rfl)) :
    ∃ (b : Vertex d.radical) (i : d.overgroup →* FreeAmalgam d.radical)
      (A : Subgroup d.overgroup),
      Function.Injective i ∧ Adjacent d.radical (alpha d.radical) b ∧
      Adjacent d.radical c b ∧ A ≤ d.radical ∧
      A.map i = Z d.radical (alpha d.radical) ∧
      (replacementMoved d).map i = U d.radical c ∧
      (omegaCenter d.radical).map i = Z d.radical b ∧
      (pResidual 2 d.overgroup).map i = Ltilde d.radical c ∧
      ∃ t : Equiv.Perm (Fin 6), t.IsSwap ∧
        A.map (Recognition.sourceProjection h e hz hn d) = zpowers t := by
  obtain ⟨b,i,A,hi,hab,hcb,hAR,hAm,hiW,hiS,hiL,_,t,ht,hA⟩ :=
    critical_transposition_coordinates_with_edge h e hz hn d hb hlarge hc
  exact ⟨b,i,A,hi,hab,hcb,hAR,hAm,hiW,hiS,hiL,t,ht,hA⟩

include h e hz hn in
/-- A literal transposition image has a commutator of order two on the
original whole moved cover. Faithfulness rules out collapse of the line. -/
theorem moved_commutator_card_two (A : Subgroup d.overgroup)
    (t : Equiv.Perm (Fin 6)) (ht : t.IsSwap)
    (hA : A.map (Recognition.sourceProjection h e hz hn d) = zpowers t) :
    Nat.card (⁅A,replacementMoved d⁆ : Subgroup d.overgroup) = 2 := by
  let := replacementMoved_normal h d
  let := moved_elementary h d
  obtain ⟨f,hf,hact⟩ := moved_cover_surjection h e hz hn d
  have hle := commutator_card_le_two_of_transposition (replacementMoved d)
    (Recognition.sourceProjection h e hz hn d) f hf hact A t ht hA
  have hne : (⁅A,replacementMoved d⁆ : Subgroup d.overgroup) ≠ ⊥ := by
    intro he
    have hAC := commutator_eq_bot_iff_le_centralizer.mp he
    rw [moved_centralizer h e hz hn d,
      ←Recognition.sourceProjection_kernel h e hz hn d] at hAC
    have hzero := (Subgroup.map_eq_bot_iff A).mpr hAC
    rw [hA] at hzero
    have hc := congrArg (fun H : Subgroup (Equiv.Perm (Fin 6)) => Nat.card H) hzero
    rw [Nat.card_zpowers,ht.orderOf,card_bot] at hc
    omega
  have hgt := (one_lt_card_iff_ne_bot _).mpr hne
  omega

include h e hz hn in
/-- Nontrivial natural action prevents the entire displacement from lying
in the fixed central attachment of the whole cover. -/
theorem moved_commutator_not_le_fixed (A : Subgroup d.overgroup)
    (hne : ¬ A ≤ pCore 2 d.overgroup) :
    ¬ ⁅A,replacementMoved d⁆ ≤
      centralizer (replacementComponent d : Set d.overgroup) := by
  let := replacementMoved_normal h d
  let := moved_elementary h d
  let p := coverProjection h e hz hn d
  let q := Recognition.sourceProjection h e hz hn d
  intro hle
  apply hne
  rw [←Recognition.sourceProjection_kernel h e hz hn d]
  intro a ha
  apply (naturalRepresentation_injective (Fin 6) (by decide))
  rw [map_one]
  ext v : 1
  obtain ⟨w,hw⟩ := coverProjection_surjective h e hz hn d (Multiplicative.ofAdd v)
  let z : replacementMoved d := MulAut.conjNormal a w * w⁻¹
  have hzC : z ∈ p.ker := by
    rw [coverProjection_kernel]
    exact hle (commutator_mem_commutator ha w.property)
  have heq : (p (MulAut.conjNormal a w)).toAdd =
      naturalRepresentation (Fin 6) (q a) (p w).toAdd := by
    rw [Recognition.sourceProjection_action]
    exact coverProjection_conjugate h e hz hn d a w (MulAut.conjNormal a w) rfl
  have hz0 : (p z).toAdd = 0 := congrArg Multiplicative.toAdd hzC
  have hzval : (p z).toAdd = naturalRepresentation (Fin 6) (q a) v-v := by
    dsimp only [z]
    rw [map_mul,map_inv]
    change (p (MulAut.conjNormal a w)).toAdd + -(p w).toAdd = _
    rw [heq,hw]
    exact (sub_eq_add_neg _ _).symm
  exact sub_eq_zero.mp (hzval.symm.trans hz0)

include h e hz hn in
/-- The critical transposition displacement is disjoint from the possible
fixed central line of the whole cover. No complement of that line is chosen. -/
theorem moved_commutator_inf_fixed_eq_bot (A : Subgroup d.overgroup)
    (t : Equiv.Perm (Fin 6)) (ht : t.IsSwap)
    (hA : A.map (Recognition.sourceProjection h e hz hn d) = zpowers t) :
    ⁅A,replacementMoved d⁆ ⊓ centralizer (replacementComponent d : Set d.overgroup) = ⊥ := by
  let D := (⁅A,replacementMoved d⁆ : Subgroup d.overgroup)
  let C := D ⊓ centralizer (replacementComponent d : Set d.overgroup)
  have hcard : Nat.card D = 2 := moved_commutator_card_two h e hz hn d A t ht hA
  by_contra hnon
  have hgt : 1 < Nat.card C := (one_lt_card_iff_ne_bot _).mpr hnon
  have hd : Nat.card C ∣ 2 := hcard ▸ card_dvd_of_le (show C ≤ D from inf_le_left)
  have hc : Nat.card C = 2 := ((Nat.dvd_prime (by decide : Nat.Prime 2)).mp hd).resolve_left
    (by omega)
  have he : C = D := eq_of_le_of_card_ge inf_le_left (by rw [hc,hcard])
  apply moved_commutator_not_le_fixed h e hz hn d A ?_ (he.ge.trans (show C ≤ _ from inf_le_right))
  intro hle
  have hzA := (Subgroup.map_eq_bot_iff A).mpr
    ((Recognition.sourceProjection_kernel h e hz hn d).symm ▸ hle)
  rw [hA] at hzA
  have hc := congrArg (fun H : Subgroup (Equiv.Perm (Fin 6)) => Nat.card H) hzA
  rw [Nat.card_zpowers,ht.orderOf,card_bot] at hc
  omega

include h e hz hn in
private theorem critical_commutator_realization
    (hb : replacementDistance h d = 2)
    (hlarge : ¬ core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical))
    {c : Vertex d.radical}
    (hc : CriticalPair d.radical (alpha d.radical) c
      ((replacementGeometry h d).exists_critical _ rfl)) :
    ∃ (i : d.overgroup →* FreeAmalgam d.radical) (A : Subgroup d.overgroup)
      (t : Equiv.Perm (Fin 6)), Function.Injective i ∧ t.IsSwap ∧
      A.map (Recognition.sourceProjection h e hz hn d) = zpowers t ∧
      (replacementComponent d).map i = Ltilde d.radical c ∧
      (⁅A,replacementMoved d⁆ : Subgroup d.overgroup).map i =
        ⁅Z d.radical (alpha d.radical),Z d.radical c⁆ := by
  obtain ⟨b,i,A,hi,hab,hcb,hAR,hAm,hiW,hiS,hiL,t,ht,hA⟩ :=
    critical_transposition_coordinates h e hz hn d hb hlarge hc
  let := replacementMoved_normal h d
  have hc0 := critical_endpoint_color d.radical (alpha d.radical) rfl _ hc
  have hZc : Z d.radical c = (replacementMoved d ⊔ omegaCenter d.radical).map i := by
    rw [Subgroup.map_sup,hiW,hiS]
    exact CentralLayer.Z_eq_moving_sup_edge_at h e hz d hc0 hcb
  have hcomm : ⁅A,replacementMoved d ⊔ omegaCenter d.radical⁆ =
      ⁅A,replacementMoved d⁆ := by
    apply le_antisymm
    · apply commutator_le.mpr
      intro a ha x hx
      obtain ⟨w,hw,z,hz,rfl⟩ := mem_sup_of_normal_left.mp hx
      have haz : Commute a z := (mem_omegaCenter_iff.mp hz).2.2 a (hAR ha)
      rw [commutatorElement_mul_right_eq_mul_conj,haz.commutator_eq]
      simp only [mul_one,mul_inv_cancel_right]
      exact commutator_mem_commutator ha hw
    · exact commutator_mono le_rfl le_sup_left
  refine ⟨i,A,t,hi,ht,hA,?_,?_⟩
  · change ((L.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map i = _
    rw [←replacement_residual h d]
    exact hiL
  · rw [←hAm,hZc,←map_commutator,hcomm]

include h e hz hn in
/-- The literal critical commutator has order two on either whole moved
cover. This uses the original non-Frattini hypothesis, with no local-image
or plane-intersection premise. -/
theorem critical_commutator_card_two
    (hb : replacementDistance h d = 2)
    (hlarge : ¬ core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical))
    {c : Vertex d.radical}
    (hc : CriticalPair d.radical (alpha d.radical) c
      ((replacementGeometry h d).exists_critical _ rfl)) :
    Nat.card (⁅Z d.radical (alpha d.radical),Z d.radical c⁆ :
      Subgroup (FreeAmalgam d.radical)) = 2 := by
  obtain ⟨i,A,t,hi,ht,hA,_,hD⟩ := critical_commutator_realization h e hz hn d hb hlarge hc
  rw [←hD,card_map_of_injective hi]
  exact moved_commutator_card_two h e hz hn d A t ht hA

include h e hz hn in
/-- The source critical commutator has no nonidentity element in the
opposite component's fixed central attachment. This does not assert that
the two whole moved layers, or their fixed central lines, are disjoint. -/
theorem critical_commutator_inf_opposite_fixed_eq_bot
    (hb : replacementDistance h d = 2)
    (hlarge : ¬ core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical))
    {c : Vertex d.radical}
    (hc : CriticalPair d.radical (alpha d.radical) c
      ((replacementGeometry h d).exists_critical _ rfl)) :
    ⁅Z d.radical (alpha d.radical),Z d.radical c⁆ ⊓
      centralizer (Ltilde d.radical c : Set (FreeAmalgam d.radical)) = ⊥ := by
  obtain ⟨i,A,t,hi,ht,hA,hK,hD⟩ := critical_commutator_realization h e hz hn d hb hlarge hc
  apply _root_.eq_bot_iff.mpr
  rintro x ⟨hx,hxC⟩
  rw [←hD] at hx
  obtain ⟨z,hzmem,rfl⟩ := hx
  have hzC : z ∈ centralizer (replacementComponent d : Set d.overgroup) := by
    intro k hk
    apply hi
    rw [map_mul,map_mul]
    exact hxC (i k) (hK ▸ mem_map_of_mem i hk)
  have hz1 : z = 1 := mem_bot.mp
    (moved_commutator_inf_fixed_eq_bot h e hz hn d A t ht hA ▸ ⟨hzmem,hzC⟩)
  rw [hz1,map_one]
  exact one_mem _

include h e hz hn in
/-- The original critical transposition supplies the missing odd permutation,
so the actual source projection is onto S₆ before selecting a paired orbit. -/
theorem sourceProjection_surjective_of_nonfrattini
    (hb : replacementDistance h d = 2)
    (hlarge : ¬ core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical)) :
    Function.Surjective (Recognition.sourceProjection h e hz hn d) := by
  obtain ⟨c,hc⟩ := criticalPair_exists d.radical (alpha d.radical)
    ((replacementGeometry h d).exists_critical _ rfl)
  obtain ⟨b,i,A,_,_,_,_,_,_,_,_,t,ht,hA⟩ :=
    critical_transposition_coordinates h e hz hn d hb hlarge hc
  let q := Recognition.sourceProjection h e hz hn d
  have ha : alternatingGroup (Fin 6) ≤ q.range := by
    rw [←Recognition.sourceProjection_component h e hz hn d]
    exact map_le_range _ _
  have htq : t ∈ q.range := (map_le_range q A) (hA ▸ mem_zpowers t)
  have hd := index_dvd_of_le ha
  rw [alternatingGroup.index_eq_two] at hd
  rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hd with h1 | h2
  · exact MonoidHom.range_eq_top.mp (index_eq_one.mp h1)
  · have he : q.range = alternatingGroup (Fin 6) :=
      Equiv.Perm.eq_alternatingGroup_of_index_eq_two h2
    have hs : Equiv.Perm.sign t = 1 := (Equiv.Perm.mem_alternatingGroup.mp (he ▸ htq))
    rw [ht.sign_eq] at hs
    cases hs

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.LocalImages
