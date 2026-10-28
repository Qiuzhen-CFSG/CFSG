module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LocalAction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.Critical
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.Coordinates
public import Theory.Representation.NormalElementaryQuotient.OriginalAction
public import Theory.GroupTheory.CentralizerInjectiveImage

/-!
# Exhaustion at distance two for the faithful exceptional action

The initial hexacode section supplies coordinates at the opposite critical
vertex. The source radical centralizes the critical X-commutator. The finite
hexacode calculation therefore bounds its entire action as soon as the
opposite endpoint image is an offender.

Restriction to the initial section preserves the favorable displacement
inequality. Reverse and conjugate a critical pair to obtain that inequality,
then apply the actual local bound and Frattini detection. The final theorem
has only the original pair, cubic center, faithful initial kernel, and
distance-two hypotheses. The cubic initial-kernel and larger-distance cases
remain with this reconstruction owner.

Source: Meierfrankenfeld--Stellmacher (1993), (2.2)(vi), p.857,
(3.3), pp.866--868, and the exceptional case of (3.6), p.870.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
local notation "T" => edge L R

private theorem edgeKernel_twoGroup
    (h : SmallMSPair κ L R) {c t : Vertex T}
    (hc : color T c = false) (hct : Adjacent T c t) : IsPGroup 2 (Q T t) := by
  obtain ⟨g, ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ := (adjacent_iff_exists_common T c t).mp hct
  · have he := Q_act T g (beta T)
    simp only [beta,act_hVertex,one_mul] at he
    rw [he]
    change IsPGroup 2 ((Q T (beta T)).map _)
    rw [Q_beta]
    exact (h.relative_radical.isPGroup.map (embedM T)).map _
  · cases hc

/-- In the original graph the local hexacode calculation bounds the full
Q-action, provided the actual endpoint image is an offender. The input
section may be smaller than X; no whole-core exhaustion is assumed. -/
theorem distanceTwo_hexacode_commutator_bound
    (h : SmallMSPair κ L R) (e : CentralMarking L)
    (hb : sourceDistance h = 2) (c : Vertex T)
    (hc : CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical (alpha T) rfl))
    (f : stabilizer T c →* Atlas.Codes.HexAutomorphisms)
    (W : Subgroup (stabilizer T c)) [W.Normal] [IsElementaryAbelian 2 W]
    (hWX : W.map (stabilizer T c).subtype ≤ X T c)
    (φ : Additive W ≃ₗ[ZMod 2] Atlas.Codes.hexacode)
    (hφ : ∀ (g : stabilizer T c) (v : W),
      φ (Additive.ofMul (MulAut.conjNormal g v)) =
        Hexacode.action (f g) (φ (Additive.ofMul v)))
    (hk : f.ker ≤ (Q T c).subgroupOf (stabilizer T c))
    (ho : IsOffender Hexacode.action
      (((X T (alpha T)).subgroupOf (stabilizer T c)).map f)) :
    ⁅Q T (alpha T), X T c⁆ ≤ ⁅X T (alpha T),X T c⁆ := by
  obtain ⟨t,hat,hct,hQt,_⟩ := distanceTwo_source_actor h e hb c hc
  let H := stabilizer T c
  let j := H.subtype
  let E := (X T (alpha T)).subgroupOf H
  let Y := (Q T (alpha T)).subgroupOf H
  let P := (Q T t).subgroupOf H
  let V := (X T c).subgroupOf H
  have hQtH : Q T t ≤ H := fun _ hx => hx.2 c (adjacent_symm T hct)
  have hYH : Q T (alpha T) ≤ H := (hQt.trans inf_le_left).trans hQtH
  have hEH : X T (alpha T) ≤ H := (omegaCenter_le _).trans hYH
  have hVH : X T c ≤ H := (omegaCenter_le _).trans (fun _ hx => hx.1)
  have hP : IsPGroup 2 P := (edgeKernel_twoGroup h
    (critical_endpoint_color T (alpha T) rfl _ hc) hct).of_equiv
      (subgroupOfEquivOfLe hQtH).symm
  have hEP : E ≤ P := fun _ hx => (hQt ((omegaCenter_le _) hx)).1
  have hYP : Y ≤ P := fun _ hx => (hQt hx).1
  have hEY : Y ≤ centralizer (E : Set H) := by
    intro y hy x hx
    apply Subtype.ext
    exact (Q_le_centralizer_X T (alpha T) hy) x hx
  have hcomm : Y ≤ centralizer ((⁅E,W⁆ : Subgroup H) : Set H) := by
    intro y hy z hz
    apply Subtype.ext
    apply Q_le_centralizer_X T (alpha T) hy
    have hz' : (z : FreeAmalgam T) ∈ (⁅E,W⁆).map j := mem_map_of_mem j hz
    rw [map_commutator,show E.map j = X T (alpha T) from map_subgroupOf_eq_of_le hEH] at hz'
    exact ((commutator_mono le_rfl hWX).trans
      ((critical_X_commutator_le h e (alpha T) rfl c hc).trans inf_le_left)) hz'
  have hker : f.ker ≤ centralizer (V : Set H) := by
    intro y hy x hx
    apply Subtype.ext
    exact (Q_le_centralizer_X T c (hk hy)) x hx
  have hh := HexacodeLocal.commutator_le_of_hexacode_offender
    f W φ hφ E Y P V hP hEP hYP hEY hcomm ho hker
  have hm := map_mono (f := j) hh
  rw [map_commutator,map_commutator,
    show E.map j = X T (alpha T) from map_subgroupOf_eq_of_le hEH,
    show Y.map j = Q T (alpha T) from map_subgroupOf_eq_of_le hYH,
    show V.map j = X T c from map_subgroupOf_eq_of_le hVH] at hm
  exact hm

/-- The finite hexacode action supplies the exceptional whole-core conclusion
through the literal critical pair. Construction of the critical offender
from the source remains with this reconstruction owner. -/
theorem coreExhaustion_of_distanceTwo_hexacode_offender
    (h : SmallMSPair κ L R) (e : CentralMarking L)
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (hb : sourceDistance h = 2) (c : Vertex T)
    (hc : CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical (alpha T) rfl))
    (f : stabilizer T c →* Atlas.Codes.HexAutomorphisms)
    (W : Subgroup (stabilizer T c)) [W.Normal] [IsElementaryAbelian 2 W]
    (hWX : W.map (stabilizer T c).subtype ≤ X T c)
    (φ : Additive W ≃ₗ[ZMod 2] Atlas.Codes.hexacode)
    (hφ : ∀ (g : stabilizer T c) (v : W),
      φ (Additive.ofMul (MulAut.conjNormal g v)) =
        Hexacode.action (f g) (φ (Additive.ofMul v)))
    (hk : f.ker ≤ (Q T c).subgroupOf (stabilizer T c))
    (ho : IsOffender Hexacode.action
      (((X T (alpha T)).subgroupOf (stabilizer T c)).map f)) :
    CoreExhaustion L R := by
  apply coreExhaustion_of_critical_comparison h e hz c hc
  have hcCol := critical_endpoint_color T (alpha T) rfl _ hc
  have hZ := (sourceGeometry h).omega_bound c hcCol (by
    rw [(sourceGeometry h).distance_constant c hcCol]
    exact sourceDistance_pos h)
  exact ((commutator_mono le_rfl hZ).trans
    (distanceTwo_hexacode_commutator_bound h e hb c hc f W hWX φ hφ hk ho)).trans
    le_sup_right

end AlternatingSixReconstruction.Exceptional.Exhaustion
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative
universe u

private theorem hexacode_offender_of_index
    {H : Type*} [Group H] [Finite H] (f : H →* Atlas.Codes.HexAutomorphisms)
    (W : Subgroup H) [W.Normal] [IsElementaryAbelian 2 W]
    (φ : Additive W ≃ₗ[ZMod 2] Atlas.Codes.hexacode)
    (hφ : ∀ (g : H) (v : W),
      φ (Additive.ofMul (MulAut.conjNormal g v)) =
        Hexacode.action (f g) (φ (Additive.ofMul v)))
    (E : Subgroup H) [IsElementaryAbelian 2 E]
    (hne : E.map f ≠ ⊥)
    (hbound : (centralizer (E : Set H)).relIndex W ≤ Nat.card (E.map f)) :
    IsOffender Hexacode.action (E.map f) := by
  have hel : IsElementaryTwo (E.map f) := ⟨hne,IsElementaryAbelian.map f⟩
  refine ⟨hel,?_⟩
  let ρ := NormalElementaryQuotient.originalAction W
  have he : ∀ g v, φ (ρ g v) = Hexacode.action (f g) (φ v) := by
    intro g v
    have hh : ρ g v = Additive.ofMul (MulAut.conjNormal g v.toMul) :=
      Additive.toMul.injective (Subtype.ext (NormalElementaryQuotient.originalAction_apply W g v))
    rw [hh,hφ,ofMul_toMul]
  have hd := fixedCodim_map_equivariant ρ Hexacode.action f φ he E
  have hi := NormalElementaryQuotient.original_fixed_index W E
  rw [inf_relIndex_left] at hi
  rw [hi,show fixedCodim (NormalElementaryQuotient.originalAction W) E =
    fixedCodim Hexacode.action (E.map f) from hd,hel.card_eq_two_pow_rank] at hbound
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hbound

variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
local notation "T" => edge L R
local notation "M" => (L ⊔ R : Subgroup G)

/-- A favorable critical orientation gives an actual offender in the
constructed vertex chart, without assuming a bound on Q's action. -/
theorem critical_hexacode_offender_of_comparison
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hb : sourceDistance h = 2) (c : Vertex T)
    (hc : CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical (alpha T) rfl))
    (f : stabilizer T c →* Atlas.Codes.HexAutomorphisms)
    (W : Subgroup (stabilizer T c)) [W.Normal] [IsElementaryAbelian 2 W]
    (hWX : W.map (stabilizer T c).subtype ≤ X T c)
    (φ : Additive W ≃ₗ[ZMod 2] Atlas.Codes.hexacode)
    (hφ : ∀ (g : stabilizer T c) (v : W),
      φ (Additive.ofMul (MulAut.conjNormal g v)) =
        Hexacode.action (f g) (φ (Additive.ofMul v)))
    (hk : f.ker = (Q T c).subgroupOf (stabilizer T c))
    (hcomp : Offenders.displacement (X T c) (X T (alpha T)) ≤
      Offenders.displacement (X T (alpha T)) (X T c)) :
    IsOffender Hexacode.action (((X T (alpha T)).subgroupOf (stabilizer T c)).map f) := by
  obtain ⟨t,hat,hct,hQt,_⟩ := distanceTwo_source_actor h e hb c hc
  let H := stabilizer T c
  let j := H.subtype
  let E := (X T (alpha T)).subgroupOf H
  let V := (X T c).subgroupOf H
  let N := (Q T c).subgroupOf H
  let := finite_stabilizer T c
  let : IsElementaryAbelian 2 (X T (alpha T)) := omegaCenter_elementary _
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.comap_of_injective j H.subtype_injective _
  have hEH : X T (alpha T) ≤ H := critical_X_le_vertex h e (alpha T) rfl c hc
  have hVH : X T c ≤ H := (omegaCenter_le _).trans (fun _ hx => hx.1)
  have hNH : Q T c ≤ H := fun _ hx => hx.1
  have hEm : E.map j = X T (alpha T) := map_subgroupOf_eq_of_le hEH
  have hVm : V.map j = X T c := map_subgroupOf_eq_of_le hVH
  have hNm : N.map j = Q T c := map_subgroupOf_eq_of_le hNH
  have hWV : W ≤ V := fun x hx => hWX (mem_map_of_mem j hx)
  have hne : E.map f ≠ ⊥ := by
    intro hz
    have hh : E ≤ N := by
      have hh : E ≤ f.ker := E.map_eq_bot_iff.mp hz
      rw [hk] at hh
      exact hh
    apply hc.2
    have hm := map_mono (f := j) hh
    rw [hEm,hNm] at hm
    exact ((sourceGeometry h).omega_bound (alpha T) rfl (sourceDistance_pos h)).trans hm
  apply hexacode_offender_of_index f W φ hφ E hne
  have hidx : (centralizer (E : Set H)).relIndex V =
      Offenders.displacement (X T c) (X T (alpha T)) := by
    have hi := relIndex_map_map_of_injective
      (V ⊓ centralizer (E : Set H)) V H.subtype_injective
    rw [←map_inf_centralizer_of_injective j H.subtype_injective, hEm,hVm,inf_relIndex_left,inf_relIndex_left] at hi
    exact hi.symm
  have hcent : X T (alpha T) ⊓ centralizer (X T c : Set (FreeAmalgam T)) =
      X T (alpha T) ⊓ Q T c := by
    have hcCol := critical_endpoint_color T (alpha T) rfl _ hc
    have hZ := (sourceGeometry h).omega_bound c hcCol (by
      rw [(sourceGeometry h).distance_constant c hcCol]
      exact sourceDistance_pos h)
    apply le_antisymm
    · rintro x ⟨hx,hxc⟩
      refine ⟨hx,?_⟩
      rw [←sourceEdgeCentralizer h e c t hcCol hct]
      exact ⟨(hQt ((omegaCenter_le _) hx)).1,centralizer_le hZ hxc⟩
    · exact le_inf inf_le_left (inf_le_right.trans (Q_le_centralizer_X T c))
  have hrev : Offenders.displacement (X T (alpha T)) (X T c) =
      (Q T c).relIndex (X T (alpha T)) := by
    unfold Offenders.displacement
    rw [←inf_relIndex_left (X T (alpha T)),hcent,inf_relIndex_left]
  have hcard : Nat.card (E.map f) = (Q T c).relIndex (X T (alpha T)) := by
    rw [←relIndex_ker,hk]
    have hi := relIndex_map_map_of_injective N E H.subtype_injective
    rw [hNm,hEm] at hi
    exact hi.symm
  rw [hcard]
  exact (relIndex_le_of_le_right hWV (by exact ((centralizer (E : Set H)).subgroupOf V).index_ne_zero_of_finite)).trans
    ((le_of_eq hidx).trans (hcomp.trans_eq hrev))

/-- The faithful initial-action branch at distance two is exhausted once a
favorable critical orientation is selected. All vertex model premises have
been constructed from the original small MS pair. -/
theorem coreExhaustion_of_distanceTwo_favorable
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (hfaith : layerKernel L R = pCore 2 M)
    (hb : sourceDistance h = 2) (c : Vertex T)
    (hc : CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical (alpha T) rfl))
    (hcomp : Offenders.displacement (X T c) (X T (alpha T)) ≤
      Offenders.displacement (X T (alpha T)) (X T c)) : CoreExhaustion L R := by
  obtain ⟨f,W,hWN,hWE,hWX,hker,φ,hφ⟩ := vertex_hexacode_model h e hz hfaith c
    (critical_endpoint_color T (alpha T) rfl _ hc)
  let := hWN
  let := hWE
  exact coreExhaustion_of_distanceTwo_hexacode_offender h e hz hb c hc f W hWX φ hφ hker.le
    (critical_hexacode_offender_of_comparison h e hb c hc f W hWX φ hφ hker hcomp)

end AlternatingSixReconstruction.Exceptional.Exhaustion
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
local notation "T" => edge L R
local notation "M" => (L ⊔ R : Subgroup G)

/-- Reverse and translate a critical pair when necessary, retaining the
actual endpoint layers in the favorable displacement comparison. -/
theorem exists_favorable_critical_pair
    (h : SmallMSPair κ L R) (e : CentralMarking L) :
    ∃ c : Vertex T,
      CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical (alpha T) rfl) ∧
      Offenders.displacement (X T c) (X T (alpha T)) ≤
        Offenders.displacement (X T (alpha T)) (X T c) := by
  obtain ⟨c,hc⟩ := criticalPair_exists T (alpha T)
    ((sourceGeometry h).exists_critical (alpha T) rfl)
  by_cases hh : Offenders.displacement (X T c) (X T (alpha T)) ≤
      Offenders.displacement (X T (alpha T)) (X T c)
  · exact ⟨c,hc,hh⟩
  have hcCol := critical_endpoint_color T (alpha T) rfl _ hc
  have hr := critical_reverse T (sourceGeometry h) (sourceEdgeCentralizer h e)
    (alpha T) rfl (sourceDistance_pos h) c hcCol hc
  obtain ⟨g,hgc⟩ := exists_mVertex_of_color T hcCol
  have hg : act T g⁻¹ c = alpha T := by
    rw [hgc,act_mVertex,mul_inv_cancel]
    rfl
  have hgcCol : color T (act T g⁻¹ c) = false := by rw [hg]; rfl
  have hc' := (criticalPair_act_iff T g⁻¹ c (alpha T)
    ((sourceGeometry h).exists_critical c hcCol)
    ((sourceGeometry h).exists_critical (act T g⁻¹ c) hgcCol)).mpr hr
  have hcmp :
      Offenders.displacement (X T (act T g⁻¹ (alpha T))) (X T (act T g⁻¹ c)) ≤
        Offenders.displacement (X T (act T g⁻¹ c)) (X T (act T g⁻¹ (alpha T))) := by
    rw [X_act,X_act,Offenders.displacement_map,Offenders.displacement_map]
    exact (lt_of_not_ge hh).le
  refine ⟨act T g⁻¹ (alpha T),?_,?_⟩
  · simpa only [hg] using hc'
  · simpa only [hg] using hcmp

/-- The faithful-cover distance-two branch of MS93 (3.6), with every local
coordinate, offender and commutator-bound premise discharged. -/
theorem coreExhaustion_of_distanceTwo_faithful
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (hfaith : layerKernel L R = pCore 2 M)
    (hb : sourceDistance h = 2) : CoreExhaustion L R := by
  obtain ⟨c,hc,hcomp⟩ := exists_favorable_critical_pair h e
  exact coreExhaustion_of_distanceTwo_favorable h e hz hfaith hb c hc hcomp

end AlternatingSixReconstruction.Exceptional.Exhaustion
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
