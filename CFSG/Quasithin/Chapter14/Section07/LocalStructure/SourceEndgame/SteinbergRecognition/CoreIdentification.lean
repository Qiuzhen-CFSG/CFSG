module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.CoreIdentification.CommutatorGeneration
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.SpecialGroup
public import Theory.SpecificGroups.PSL3Two.InvolutoryLift

/-!
# Core identification from the source involution

Commutator generation already gives S ≤ O₂(L) and [O₂(L),L] = S.
The same original qL descends to L/S, with central two-group kernel exactly
O₂(L)/S. Perfectness is inherited from the original local component L.
An involution in O₂(L₁) outside Q has nonidentity image under this map.
The actual SL₂(7) comparison therefore kills its kernel, proving
S = O₂(L) = [O₂(L),L]. The original Steinberg section and the Ru1 consumer
are supplied after the later T ≤ L from 14.7.74.

This module proves the conditional cover and core argument, including its
application to an H-conjugate of a critical involution. Construction of that
conjugate in Q_H ∩ O₂(L₁) outside Q remains a source obligation; it is not
asserted by these conditional theorems. Here O₂(L₁) is the two-core, and
all quotient maps are the original marked maps.

Source: Aschbacher–Smith, proof of 14.7.72, printed p.1076 (PDF p.1093),
combined manuscript of 1 March 2004.
-/

public section
open Subgroup Representation
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W] (d : Data T L V F W)

namespace CoreIdentification

/-- The original quotient marking descends through S. Its kernel is the
literal image of O₂(L), and the commutator calculation makes it central. -/
theorem core_eq_of_involutory_lift
    (c : SteinbergCoordinates d)
    (hPhi : (frattini (S F L)).map (S F L).subtype = V)
    (hSQ : S F L ≤ Q T L) (h71 : ⁅Q T L,L⁆ ≤ S F L)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (x : L) (hx : x ^ 2 = 1) (hxQ : (x : G) ∉ Q T L) :
    S F L = L.pCoreIn 2 := by
  have hSC := S_le_core d c hPhi hSQ h71 hTL
  have hcomm := core_commutator_eq_S d c hPhi hSQ h71 hTL
  have hcoreQ : L.pCoreIn 2 ≤ Q T L := by
    apply le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 L)
      ((pCoreIn_le 2 L).trans le_sup_left)
    exact (sup_le L.le_normalizer hTL).trans
      (normalizer_le_normalizer_characteristic_image L (pCore 2 L))
  let N := (S F L).subgroupOf L
  let : N.Normal := normal_subgroupOf_of_le_normalizer L_normalizes_S
  let π : L →* L ⧸ N := QuotientGroup.mk' N
  have hNker : N ≤ d.qL.ker := by
    rw [d.qL_ker]
    exact subgroupOf_mono L hSC
  let f : (L ⧸ N) →* BinaryLinearThree.Group := QuotientGroup.lift N d.qL hNker
  have hf : Function.Surjective f :=
    QuotientGroup.lift_surjective_of_surjective N d.qL d.qL_surjective hNker
  have hfk : f.ker = ((L.pCoreIn 2).subgroupOf L).map π := by
    rw [QuotientGroup.ker_lift, d.qL_ker]
  have hfc : f.ker ≤ center (L ⧸ N) := by
    rw [hfk]
    rintro _ ⟨a, ha, rfl⟩
    apply mem_center_iff.mpr
    intro y
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective N y
    apply (commutatorElement_eq_one_iff_mul_comm).mp
    rw [← map_commutatorElement]
    apply (QuotientGroup.eq_one_iff _).mpr
    change ⁅(b : G),(a : G)⁆ ∈ S F L
    rw [← hcomm, commutator_comm]
    exact commutator_mem_commutator b.property ha
  have hf2 : IsPGroup 2 f.ker := by
    rw [hfk]
    exact (isPGroup_pCoreIn 2 L).comap_subtype.map π
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect
    d.natural.source.maximal_faithful.1.1
  let : Group.IsPerfect (L ⧸ N) :=
    Group.IsPerfect.ofSurjective (f := π) (QuotientGroup.mk'_surjective N)
  have hpx : (π x) ^ 2 = 1 := by rw [← map_pow, hx, map_one]
  have hfx : f (π x) ≠ 1 := by
    intro he
    have hk : x ∈ d.qL.ker := he
    rw [d.qL_ker] at hk
    exact hxQ (hcoreQ hk)
  have hbot := BinaryLinearThree.CentralCover.kernel_eq_bot_of_involution
    f hf hfc hf2 (π x) hpx hfx
  apply le_antisymm hSC
  intro a ha
  let aL : L := ⟨a,pCoreIn_le 2 L ha⟩
  have hm : π aL ∈ f.ker := by
    rw [hfk]
    exact mem_map_of_mem π ha
  rw [hbot, mem_bot] at hm
  exact (QuotientGroup.eq_one_iff (N := N) aL).mp hm

/-- Application to the exact source location; O₂(L₁) is its two-core. -/
theorem core_and_commutator_of_source_involution
    (c : SteinbergCoordinates d)
    (hPhi : (frattini (S F L)).map (S F L).subtype = V)
    (hSQ : S F L ≤ Q T L) (h71 : ⁅Q T L,L⁆ ≤ S F L)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (x : G) (_hxH : x ∈ F.H.pCoreIn 2)
    (hx₁ : x ∈ (F.Li L 1).pCoreIn 2)
    (hx : x ^ 2 = 1) (hxQ : x ∉ Q T L) :
    S F L = L.pCoreIn 2 ∧ ⁅L.pCoreIn 2,L⁆ = L.pCoreIn 2 := by
  have hxL : x ∈ L := ((pCoreIn_le 2 _).trans ((F.Li_le L 1).trans inf_le_left)) hx₁
  have he := core_eq_of_involutory_lift d c hPhi hSQ h71 hTL ⟨x,hxL⟩
    (Subtype.ext hx) hxQ
  exact ⟨he, (core_commutator_eq_S d c hPhi hSQ h71 hTL).trans he⟩

/-- The literal section and Ru1 consumer after 14.7.74 supplies T ≤ L.
Construction of the involution is still required for the full source theorem. -/
theorem section_and_ruOne_of_source_involution
    (earlier : d.ModuleSeparation) (c : SteinbergCoordinates d)
    (hcentral : V ≤ (center (S F L)).map (S F L).subtype)
    (hPhi : (frattini (S F L)).map (S F L).subtype = V)
    (hderived : ⁅S F L,S F L⁆ = V)
    (hSQ : S F L ≤ Q T L) (h71 : ⁅Q T L,L⁆ ≤ S F L)
    (hTL : (T : Subgroup G) ≤ L)
    (x : G) (hxH : x ∈ F.H.pCoreIn 2)
    (hx₁ : x ∈ (F.Li L 1).pCoreIn 2)
    (hx : x ^ 2 = 1) (hxQ : x ∉ Q T L) :
    Nonempty (BinaryConjugationSection L (S F L) V (BinaryLinearThree.S.comp d.qL)) ∧
      Nonempty (ChapterJ.RuOne L V) := by
  have hn := hTL.trans L.le_normalizer
  have hcore := (core_and_commutator_of_source_involution d c hPhi hSQ h71 hn
    x hxH hx₁ hx hxQ).1
  exact ⟨⟨c.toSection (S_le_L d c hPhi hSQ h71 hn)⟩,
    ruOne_of_recognized_source d earlier hTL hcore hcentral hPhi hderived c⟩

/-- Retain the critical element and its H-conjugator when applying the cover
argument. Element order is transported through conjugation, not assumed for
an arbitrary lift of a quotient involution. -/
theorem core_and_commutator_of_critical_conjugate
    (c : SteinbergCoordinates d)
    (hPhi : (frattini (S F L)).map (S F L).subtype = V)
    (hSQ : S F L ≤ Q T L) (h71 : ⁅Q T L,L⁆ ≤ S F L)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (Uα : Subgroup G)
    (hw : ∃ u : Uα, orderOf u = 2 ∧ ∃ h : F.H,
      (h : G) * u * (h : G)⁻¹ ∈ F.H.pCoreIn 2 ∧
      (h : G) * u * (h : G)⁻¹ ∈ (F.Li L 1).pCoreIn 2 ∧
      (h : G) * u * (h : G)⁻¹ ∉ Q T L) :
    S F L = L.pCoreIn 2 ∧ ⁅L.pCoreIn 2,L⁆ = L.pCoreIn 2 := by
  obtain ⟨u, hu, h, hH, hP, hQ⟩ := hw
  have hs : (u : G) ^ 2 = 1 := by
    have he : u ^ 2 = 1 := by simpa only [hu] using pow_orderOf_eq_one u
    exact congrArg Subtype.val he
  apply core_and_commutator_of_source_involution d c hPhi hSQ h71 hTL
    ((h : G) * u * (h : G)⁻¹) hH hP ?_ hQ
  rw [conj_pow, hs, mul_one, mul_inv_cancel]

end CoreIdentification

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition
