module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.PairTransport
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.FixedPairSolvable.Selection

/-!
# The same characteristic pair inside a full-Sylow overgroup

The original Sylow subgroup has the same Baumann subgroup after restriction
along H ↪ G. The explicit isomorphism transports the given universal pair;
its two ambient images and central seed are unchanged. The local control
subgroup consequently maps into the original control subgroup. An escaping
H therefore has proper control for this transported pair.

This supplies the original marking needed by the fixed-pair C.1.28 consumer,
without choosing another universal pair in H. Source: 14.1.11, printed p.978.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.FixedPairSolvable
open ChapterB GlaubermanNiles
universe u
variable {G : Type u} [Group G]

@[expose] noncomputable def baumannSubtypeEquiv (T : Sylow 2 G)
    (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H) :
    baumann (T.subtype hTH : Subgroup H) ≃* baumann (T : Subgroup G) :=
  ((baumann (T.subtype hTH : Subgroup H)).equivMapOfInjective H.subtype H.subtype_injective).trans
    (MulEquiv.subgroupCongr (by
      unfold baumann thompsonAlpha
      rw [baumann_map_injective H.subtype H.subtype_injective,
        Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH]))

theorem baumannSubtypeEquiv_coe (T : Sylow 2 G)
    (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    (b : baumann (T.subtype hTH : Subgroup H)) :
    ((baumannSubtypeEquiv T H hTH b : baumann (T : Subgroup G)) : G) = (b : H) := rfl

theorem baumannSubtypeEquiv_symm_coe (T : Sylow 2 G)
    (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    (b : baumann (T : Subgroup G)) :
    (((baumannSubtypeEquiv T H hTH).symm b : baumann (T.subtype hTH : Subgroup H)) : H) = (b : G) := by
  have h := congrArg (baumann (T : Subgroup G)).subtype
    ((baumannSubtypeEquiv T H hTH).apply_symm_apply b)
  exact h

@[expose] noncomputable def subtypePair (T : Sylow 2 G)
    (D : CharacteristicPair (baumann (T : Subgroup G)))
    (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H) :
    CharacteristicPair (baumann (T.subtype hTH : Subgroup H)) :=
  D.map (baumannSubtypeEquiv T H hTH).symm

theorem subtypePair_member_map (T : Sylow 2 G)
    (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    (A : Subgroup (baumann (T : Subgroup G))) :
    ((A.map (baumannSubtypeEquiv T H hTH).symm.toMonoidHom).map
      (baumann (T.subtype hTH : Subgroup H)).subtype).map H.subtype =
      A.map (baumann (T : Subgroup G)).subtype := by
  rw [map_map,map_map]
  congr 1
  ext b
  exact baumannSubtypeEquiv_symm_coe T H hTH b

theorem subtypePair_firstSeed_map (T : Sylow 2 G)
    (D : CharacteristicPair (baumann (T : Subgroup G)))
    (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H) :
    (FixedPair.firstSeed (T.subtype hTH) (subtypePair T D H hTH)).map H.subtype =
      FixedPair.firstSeed T D := by
  have hz : (omegaOneCenterAmbient (T.subtype hTH : Subgroup H)).map H.subtype =
      omegaOneCenterAmbient (T : Subgroup G) := by
    rw [←omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective,
      Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH]
  rw [FixedPair.firstSeed,Subgroup.map_inf _ _ _ H.subtype_injective,hz]
  exact congrArg (fun X => omegaOneCenterAmbient (T : Subgroup G) ⊓ X)
    (subtypePair_member_map T H hTH D.first)

theorem subtypePair_control_map_le (T : Sylow 2 G)
    (D : CharacteristicPair (baumann (T : Subgroup G)))
    (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H) :
    (control (T.subtype hTH) (subtypePair T D H hTH)).map H.subtype ≤ control T D := by
  unfold control
  rw [Subgroup.map_sup]
  apply sup_le
  · rw [map_centralizer_subtype,subtypePair_firstSeed_map]
    exact inf_le_right.trans le_sup_left
  · have hn := ((subtypePair T D H hTH).second.map
    (baumann (T.subtype hTH : Subgroup H)).subtype).le_normalizer_map H.subtype
    simp only [subtypePair,CharacteristicPair.map] at hn
    rw [subtypePair_member_map T H hTH D.second] at hn
    exact hn.trans le_sup_right

theorem subtypePair_control_map_le_relative (T : Sylow 2 G)
    (D : CharacteristicPair (baumann (T : Subgroup G)))
    (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H) :
    (control (T.subtype hTH) (subtypePair T D H hTH)).map H.subtype ≤
      (H ⊓ centralizer (FixedPair.firstSeed T D : Set G)) ⊔
        (H ⊓ normalizer (D.second.map (baumann (T : Subgroup G)).subtype : Set G)) := by
  unfold control
  rw [Subgroup.map_sup]
  apply sup_le
  · rw [map_centralizer_subtype,subtypePair_firstSeed_map]
    exact le_sup_left
  · apply le_sup_of_le_right
    apply le_inf (map_subtype_le _)
    have hn := ((subtypePair T D H hTH).second.map
      (baumann (T.subtype hTH : Subgroup H)).subtype).le_normalizer_map H.subtype
    simp only [subtypePair,CharacteristicPair.map] at hn
    rw [subtypePair_member_map T H hTH D.second] at hn
    exact hn

theorem subtypePair_universal (T : Sylow 2 G)
    (D : CharacteristicPair (baumann (T : Subgroup G))) (hD : D.Universal.{u,u})
    (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H) :
    (subtypePair T D H hTH).Universal.{u,u} := hD.map _

theorem subtypePair_control_ne_top (T : Sylow 2 G)
    (D : CharacteristicPair (baumann (T : Subgroup G)))
    (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H) (hout : ¬ H ≤ control T D) :
    control (T.subtype hTH) (subtypePair T D H hTH) ≠ ⊤ := by
  intro he
  have h := subtypePair_control_map_le T D H hTH
  rw [he,←MonoidHom.range_eq_map,range_subtype] at h
  exact hout h

end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.FixedPairSolvable
