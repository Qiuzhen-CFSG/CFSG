module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.CubicCriticalLine
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.LocalImages.TranspositionCover

public import Theory.GroupTheory.MutualBinaryActions

/-!
# The literal cubic-kernel critical commutator line

The entire initial moved subgroup projects equivariantly onto its natural
central quotient, with its component centralizer as kernel. A transposition
moves exactly one line on the whole cover, and that line misses the fixed
attachment. The middle-edge seed contributes no commutator, so these facts
apply to the original graph commutator [Z_alpha,Z_alpha']. Reversing the
critical pair gives centralizer index two in both full X-layers. Their mutual
actions therefore identify [X_alpha,X_alpha'] with that same order-two line;
this does not identify X with Z or replace either whole moved cover.

The final theorem rewrites the source-(3.3) comparison with this literal line.
Its remaining commutator bound is still explicit and is discharged only by
the outstanding orbit argument, owned by alternating-six reconstruction.
CubicCriticalLine.Source applies the result to the whole intrinsic blockU
and the original rank-two consumer. The full reconstruction remains open.

Source: Meierfrankenfeld--Stellmacher (1993), (3.3)(ii)(2), pp.866--867,
and (3.6), pp.870--871.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.CubicAction
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "K" => L.subgroupOf (L ⊔ R)
local notation "X₀" => centralOmega L R
local notation "W" => (⁅X₀,K⁆ : Subgroup M)
local notation "q" => QuotientGroup.mk' (layerKernel L R)
local notation "π" => projection h e hz hk
local notation "s" => layerSection h
local notation "ρ₆" => BinaryPermutation.naturalRepresentation (Fin 6)
local notation "T" => edge L R

/-- The original moved subgroup projects onto its natural central quotient,
with exactly its component-fixed kernel and the original six-letter action. -/
theorem moved_natural_projection :
    let := h.relative_normal
    let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le (commutator_le_left X₀ K)
    ∃ p : Additive W →ₗ[ZMod 2] BinaryPermutation.natural (Fin 6),
      Function.Surjective p ∧
      (∀ v, p v = 0 ↔ (v.toMul : M) ∈ centralizer (K : Set M)) ∧
      ∀ g v, p (Additive.ofMul (MulAut.conjNormal g v.toMul)) = ρ₆ (π g) (p v) := by
  let := h.relative_normal
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le (commutator_le_left X₀ K)
  let := layerComponent_normal h
  let E := NormalElementaryQuotient.movedEquiv X₀ q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) K
  let p := ((s).coverProjection (coordinates h e hz hk)).toLinearMap
  have hs : Function.Surjective p :=
    ((s).coverProjection_isCover (layer_moved_alternating h e hz hk).1
      (coordinates h e hz hk)).1
  refine ⟨p.comp E.toLinearMap,hs.comp E.surjective,?_,?_⟩
  · intro v
    exact ElementaryMovedCover.cover_kernel_iff X₀ K q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
      (coordinates h e hz hk) (E v)
  · intro g v
    have hE : E (Additive.ofMul (MulAut.conjNormal g v.toMul)) =
        (s).space.toRepresentation (q g) (E v) := by
      apply Subtype.ext
      apply Additive.toMul.injective
      apply Subtype.ext
      exact (NormalElementaryQuotient.representation_apply X₀ q
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) g (E v).val).symm
    change p (E (Additive.ofMul (MulAut.conjNormal g v.toMul))) = _
    rw [hE]
    exact ((s).coverProjection_ambient (coordinates h e hz hk) (q g) (E v)).trans
      (permutationAction_apply h e hz hk (q g) (p (E v)))

include h e hz hk in
/-- Nontrivial natural action moves outside the component-fixed attachment,
even though the initial action kernel includes the odd cubic quotient. -/
theorem moved_commutator_not_le_fixed (A : Subgroup M)
    (hne : ¬ A ≤ extensionKernel h) :
    ¬ ⁅A,W⁆ ≤ centralizer (K : Set M) := by
  let := h.relative_normal
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le (commutator_le_left X₀ K)
  obtain ⟨p,hp,hker,hact⟩ := moved_natural_projection h e hz hk
  intro hle
  apply hne
  rw [←projection_kernel h e hz hk]
  intro a ha
  change π a = 1
  apply BinaryPermutation.naturalRepresentation_injective (Fin 6) (by decide)
  rw [map_one]
  ext v : 1
  obtain ⟨w,hw⟩ := hp v
  have hz0 : p (Additive.ofMul (MulAut.conjNormal a w.toMul * w.toMul⁻¹)) = 0 := by
    apply (hker _).mpr
    exact hle (commutator_mem_commutator ha w.toMul.property)
  rw [ofMul_mul,ofMul_inv,ofMul_toMul,←sub_eq_add_neg,map_sub,hact,hw] at hz0
  exact sub_eq_zero.mp hz0

/-- A transposition moves exactly one line on the entire initial moved
cover; faithfulness of its natural quotient prevents that line collapsing. -/
theorem moved_commutator_card_two (hb : sourceDistance h = 2)
    (A : Subgroup M) (t : Equiv.Perm (Fin 6)) (ht : t.IsSwap)
    (hA : A.map π = zpowers t) : Nat.card (⁅A,W⁆ : Subgroup M) = 2 := by
  let := h.relative_normal
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le (commutator_le_left X₀ K)
  obtain ⟨f,hf,hact⟩ := moved_subgroup_surjection h e hz hk hb
  have hle := Natural.Exhaustion.DistanceTwo.Geometry.LocalImages.commutator_card_le_two_of_transposition
    W π f hf hact A t ht hA
  have hne : ¬ A ≤ extensionKernel h := by
    intro he
    have hbA := (Subgroup.map_eq_bot_iff A).mpr ((projection_kernel h e hz hk).symm ▸ he)
    rw [hA] at hbA
    have hh := congrArg (fun H : Subgroup (Equiv.Perm (Fin 6)) => Nat.card H) hbA
    rw [Nat.card_zpowers,ht.orderOf,card_bot] at hh
    omega
  have hn : (⁅A,W⁆ : Subgroup M) ≠ ⊥ := by
    intro he
    exact moved_commutator_not_le_fixed h e hz hk A hne (he ▸ bot_le)
  have hgt := (one_lt_card_iff_ne_bot _).mpr hn
  omega

/-- The literal moved transposition line misses the entire fixed attachment. -/
theorem moved_commutator_inf_fixed_eq_bot (hb : sourceDistance h = 2)
    (A : Subgroup M) (t : Equiv.Perm (Fin 6)) (ht : t.IsSwap)
    (hA : A.map π = zpowers t) : ⁅A,W⁆ ⊓ centralizer (K : Set M) = ⊥ := by
  let D := (⁅A,W⁆ : Subgroup M)
  let C := D ⊓ centralizer (K : Set M)
  have hcard : Nat.card D = 2 := moved_commutator_card_two h e hz hk hb A t ht hA
  by_contra hn
  have hgt : 1 < Nat.card C := (one_lt_card_iff_ne_bot _).mpr hn
  have hd : Nat.card C ∣ 2 := hcard ▸ card_dvd_of_le (show C ≤ D from inf_le_left)
  have hc : Nat.card C = 2 := ((Nat.dvd_prime (by decide : Nat.Prime 2)).mp hd).resolve_left
    (by omega)
  have he : C = D := eq_of_le_of_card_ge inf_le_left (by rw [hc,hcard])
  apply moved_commutator_not_le_fixed h e hz hk A ?_
    (he.ge.trans (show C ≤ _ from inf_le_right))
  intro hle
  have hzA := (Subgroup.map_eq_bot_iff A).mpr ((projection_kernel h e hz hk).symm ▸ hle)
  rw [hA] at hzA
  have hh := congrArg (fun H : Subgroup (Equiv.Perm (Fin 6)) => Nat.card H) hzA
  rw [Nat.card_zpowers,ht.orderOf,card_bot] at hh
  omega

include h e hz in
/-- Realize the literal source commutator using the whole moved subgroup
at the base endpoint. The edge seed contributes no commutator. -/
theorem critical_commutator_realization (hb : sourceDistance h = 2) (c : Vertex T)
    (hc : CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical (alpha T) rfl)) :
    (⁅(Z T c).comap (embedM T),W⁆).map (embedM T) =
      ⁅Z T (alpha T),Z T c⁆ := by
  let := h.relative_normal
  obtain ⟨t,hat,hct,_,_⟩ := distanceTwo_source_actor h e hb c hc
  have ht : color T t = true := by
    have hh := adjacent_color_ne T hat
    change false ≠ color T t at hh
    cases hcol : color T t <;> simp_all
  have hcCol := critical_endpoint_color T (alpha T) rfl _ hc
  have hr := critical_reverse T (sourceGeometry h) (sourceEdgeCentralizer h e)
    (alpha T) rfl (sourceDistance_pos h) c hcCol hc
  have hZX := (sourceGeometry h).omega_bound c hcCol (by
    rw [(sourceGeometry h).distance_constant c hcCol]
    exact sourceDistance_pos h)
  let A := (Z T c).comap (embedM T)
  let D := (Z T t).comap (embedM T)
  have hAm : A.map (embedM T) = Z T c :=
    map_comap_eq_self ((hZX.trans (critical_X_le_vertex h e c hcCol _ hr)).trans_eq
      (stabilizer_m_base T))
  have hDH : Z T t ≤ stabilizer T (alpha T) := by
    simp only [Z,ht,Bool.true_eq_false,if_false,edgeOmega]
    exact (omegaCenter_le _).trans (fun _ hx => hx.2 _ (adjacent_symm T hat))
  have hDm : D.map (embedM T) = Z T t :=
    map_comap_eq_self (hDH.trans_eq (stabilizer_m_base T))
  have hAD : A ≤ centralizer (D : Set M) := by
    intro a ha z hzD
    apply embedM_injective T
    simp only [map_mul]
    change embedM T z ∈ Z T t at hzD
    have hzT : embedM T z ∈ omegaCenter (Q T t) := by
      simpa only [Z,ht,Bool.true_eq_false,if_false,edgeOmega] using hzD
    exact ((mem_omegaCenter_iff.mp hzT).2.2 (embedM T a)
      (Q_le_adjacent_h T ht hct ((omegaCenter_le _) (hZX ha)))).symm
  have hcomm : ⁅A,W ⊔ D⁆ = ⁅A,W⁆ := by
    apply le_antisymm
    · apply commutator_le.mpr
      intro a ha x hx
      obtain ⟨w,hw,z,hzD,rfl⟩ := mem_sup_of_normal_left.mp hx
      have haz : Commute a z := (hAD ha z hzD).symm
      rw [commutatorElement_mul_right_eq_mul_conj,haz.commutator_eq]
      simp only [mul_one,mul_inv_cancel_right]
      exact commutator_mem_commutator ha hw
    · exact commutator_mono le_rfl le_sup_left
  rw [commutator_comm (Z T (alpha T)),graph_Z_eq_moved_sup_edge h e hz hat,
    ←hAm,←hDm,←Subgroup.map_sup,←map_commutator,hcomm,
    comap_map_eq_self_of_injective (embedM_injective T)]

include h e hz hk in
/-- The critical source commutator has order two, with its actual graph
embedding and both entire Z-layers retained. -/
theorem critical_commutator_card_two (hb : sourceDistance h = 2) (c : Vertex T)
    (hc : CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical (alpha T) rfl)) :
    Nat.card (⁅Z T (alpha T),Z T c⁆ : Subgroup (FreeAmalgam T)) = 2 := by
  obtain ⟨t,ht,hA⟩ := critical_image_eq_zpowers_transposition h e hz hk hb c hc
  have hZ : ((Z T c).comap (embedM T)).map π = zpowers t :=
    (critical_Z_image_eq h e hz hk hb c hc).trans hA
  rw [←critical_commutator_realization h e hz hb c hc,
    card_map_of_injective (embedM_injective T)]
  exact moved_commutator_card_two h e hz hk hb _ t ht hZ

include h e hz hk in
/-- The actual critical commutator misses the fixed attachment at the base
component. In particular its order-two line is not a central-cover artifact. -/
theorem critical_commutator_inf_base_fixed_eq_bot
    (hb : sourceDistance h = 2) (c : Vertex T)
    (hc : CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical (alpha T) rfl)) :
    ⁅Z T (alpha T),Z T c⁆ ⊓
      centralizer (Ltilde T (alpha T) : Set (FreeAmalgam T)) = ⊥ := by
  obtain ⟨t,ht,hA⟩ := critical_image_eq_zpowers_transposition h e hz hk hb c hc
  have hZ : ((Z T c).comap (embedM T)).map π = zpowers t :=
    (critical_Z_image_eq h e hz hk hb c hc).trans hA
  apply _root_.eq_bot_iff.mpr
  rintro x ⟨hx,hxC⟩
  rw [←critical_commutator_realization h e hz hb c hc] at hx
  obtain ⟨z,hzmem,rfl⟩ := hx
  have hzC : z ∈ centralizer (K : Set M) := by
    intro k hkK
    apply embedM_injective T
    rw [map_mul,map_mul]
    exact hxC (embedM T k) ((graph_component h).symm ▸ mem_map_of_mem (embedM T) hkK)
  have hz1 : z = 1 := mem_bot.mp
    (moved_commutator_inf_fixed_eq_bot h e hz hk hb _ t ht hZ ▸ ⟨hzmem,hzC⟩)
  rw [hz1,map_one]
  exact one_mem _

include h e hz hk in
/-- Both original X-layers have centralizer index two at a critical pair,
not merely on their natural quotient sections. -/
theorem critical_displacements_two (hb : sourceDistance h = 2) (c : Vertex T)
    (hc : CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical (alpha T) rfl)) :
    Offenders.displacement (X T c) (X T (alpha T)) = 2 ∧
      Offenders.displacement (X T (alpha T)) (X T c) = 2 := by
  have hfirst := (critical_displacement_eq_core_index h e (alpha T) rfl c hc).trans
    (critical_core_index_two h e hz hk hb c hc)
  refine ⟨hfirst,?_⟩
  have hcCol := critical_endpoint_color T (alpha T) rfl _ hc
  have hr := critical_reverse T (sourceGeometry h) (sourceEdgeCentralizer h e)
    (alpha T) rfl (sourceDistance_pos h) c hcCol hc
  obtain ⟨g,hgc⟩ := exists_mVertex_of_color T hcCol
  have hg : act T g⁻¹ c = alpha T := by
    rw [hgc,act_mVertex,mul_inv_cancel]
    rfl
  have hgcCol : color T (act T g⁻¹ c) = false := by rw [hg];rfl
  have hc' := (criticalPair_act_iff T g⁻¹ c (alpha T)
    ((sourceGeometry h).exists_critical c hcCol)
    ((sourceGeometry h).exists_critical (act T g⁻¹ c) hgcCol)).mpr hr
  have hd : CriticalPair T (alpha T) (act T g⁻¹ (alpha T))
      ((sourceGeometry h).exists_critical (alpha T) rfl) := by simpa only [hg] using hc'
  have hh := (critical_displacement_eq_core_index h e (alpha T) rfl _ hd).trans
    (critical_core_index_two h e hz hk hb _ hd)
  have hi : Offenders.displacement (X T (act T g⁻¹ (alpha T)))
      (X T (act T g⁻¹ c)) = 2 := by simpa only [hg] using hh
  rw [X_act,X_act,Offenders.displacement_map] at hi
  exact hi

include h e hz hk in
/-- Enlarging the source Z-layers to the actual X-layers adds no critical
commutator. Both give the same order-two subgroup of the original graph. -/
theorem critical_X_commutator_eq_Z_commutator (hb : sourceDistance h = 2) (c : Vertex T)
    (hc : CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical (alpha T) rfl)) :
    ⁅X T (alpha T),X T c⁆ = ⁅Z T (alpha T),Z T c⁆ := by
  have hcCol := critical_endpoint_color T (alpha T) rfl _ hc
  have hr := critical_reverse T (sourceGeometry h) (sourceEdgeCentralizer h e)
    (alpha T) rfl (sourceDistance_pos h) c hcCol hc
  let B := (X T c).comap (embedM T)
  have hBm : B.map (embedM T) = X T c := map_comap_eq_self
    ((critical_X_le_vertex h e c hcCol _ hr).trans_eq (stabilizer_m_base T))
  have hAB : X₀ ≤ normalizer (B : Set M) := by
    apply le_normalizer_iff_commutator_le_right.mpr
    intro z hzB
    have hm := mem_map_of_mem (embedM T) hzB
    rw [map_commutator,←graph_X h,hBm] at hm
    exact (critical_X_commutator_le h e (alpha T) rfl c hc hm).2
  have hidx (A D : Subgroup M) :
      (centralizer (A : Set M)).relIndex D =
        Offenders.displacement (D.map (embedM T)) (A.map (embedM T)) := by
    have hi := relIndex_map_map_of_injective (D ⊓ centralizer (A : Set M)) D
      (embedM_injective T)
    rw [←map_inf_centralizer_of_injective (embedM T) (embedM_injective T),
      inf_relIndex_left,inf_relIndex_left] at hi
    exact hi.symm
  have hfirst := hidx X₀ B
  have hsecond := hidx B X₀
  rw [←graph_X h,hBm,(critical_displacements_two h e hz hk hb c hc).1] at hfirst
  rw [←graph_X h,hBm,(critical_displacements_two h e hz hk hb c hc).2] at hsecond
  have hbound := commutator_card_le_two_of_mutual_centralizer_indices X₀ B
    le_normalizer_of_normal hAB hfirst.le hsecond.le
  have hmap : (⁅X₀,B⁆).map (embedM T) = ⁅X T (alpha T),X T c⁆ := by
    rw [map_commutator,←graph_X h,hBm]
  have hbound' : Nat.card (⁅X T (alpha T),X T c⁆ : Subgroup (FreeAmalgam T)) ≤ 2 := by
    rw [←hmap,card_map_of_injective (embedM_injective T)]
    exact hbound
  have hZa := (sourceGeometry h).omega_bound _ rfl (sourceDistance_pos h)
  have hZc := (sourceGeometry h).omega_bound c hcCol (by
    rw [(sourceGeometry h).distance_constant c hcCol]
    exact sourceDistance_pos h)
  let : Finite (⁅X T (alpha T),X T c⁆ : Subgroup (FreeAmalgam T)) := by
    exact Finite.of_equiv (⁅X₀,B⁆ : Subgroup M)
      (((⁅X₀,B⁆ : Subgroup M).equivMapOfInjective (embedM T) (embedM_injective T)).trans
        (MulEquiv.subgroupCongr hmap)).toEquiv
  apply (eq_of_le_of_card_ge (commutator_mono hZa hZc) ?_).symm
  rw [critical_commutator_card_two h e hz hk hb c hc]
  exact hbound'

include h e hz hk in
/-- The comparison in source (3.3) can therefore use its literal Z
commutator without silently replacing either of its two layers. -/
theorem coreExhaustion_of_critical_line_bound
    (hb : sourceDistance h = 2) (c : Vertex T)
    (hc : CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical (alpha T) rfl))
    (hbound : ⁅Q T (alpha T),Z T c⁆ ≤
      ⁅Q T (alpha T),X T c ⊓ Q T (alpha T)⁆ ⊔ ⁅Z T (alpha T),Z T c⁆) :
    CoreExhaustion L R := by
  apply coreExhaustion_of_critical_comparison h e hz c hc
  rwa [critical_X_commutator_eq_Z_commutator h e hz hk hb c hc]

end AlternatingSixReconstruction.Exceptional.Exhaustion.CubicAction
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
