module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.RankTwoReconstruction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.ComponentQuotient
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.Geometry
public import Theory.GroupTheory.PCoreInRestriction

/-!
# The original MS pair on its generated group

MS2(a) puts the two-core of LR inside R, without making R Sylow.
The subnormal perfect component is the two-residual of the literal product
LR and hence is normal there. Transport preserves the characteristic-subgroup
condition and the actual quotient projection. These are the inputs to the
central-omega action and the MS93 critical-pair construction.

Source: Aschbacher--Smith C.1.31--32, pp.135--136; MS93 (2.0)--(3.2).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open ChapterC
namespace G2Reconstruction
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}

local notation "H" => (L ⊔ R : Subgroup G)
local notation "K" => L.subgroupOf (L ⊔ R)
local notation "T" => R.subgroupOf (L ⊔ R)

omit [Finite G] in
theorem relative_product (h : SmallMSPair κ L R) :
    ∀ g : H, ∃ k ∈ K, ∃ t ∈ T, k * t = g := by
  intro g
  obtain ⟨k,hk,t,ht,he⟩ := h.product g g.property
  exact ⟨⟨k,mem_sup_left hk⟩,hk,⟨t,mem_sup_right ht⟩,ht,Subtype.ext he⟩

omit [Finite G] in
theorem relative_radical (h : SmallMSPair κ L R) : MSOddIndexRadical T := by
  obtain ⟨A,hA,hi,he⟩ := h.radical
  refine ⟨A.subgroupOf (L ⊔ R),lt_top_iff_ne_top.mpr ?_,hi,?_⟩
  · intro ht
    have hm := congrArg (map (L ⊔ R).subtype) ht
    rw [map_subgroupOf_eq_of_le hA.le,← MonoidHom.range_eq_map,range_subtype] at hm
    exact hA.ne hm
  · change (A.subgroupOf (L ⊔ R)).pCoreIn 2 = T
    rw [pCoreIn_subgroupOf 2 A (L ⊔ R) hA.le,he]

omit [Finite G] in
theorem edge_two_group (h : SmallMSPair κ L R) : IsPGroup 2 T :=
  (relative_radical h).isPGroup

theorem core_le_edge (h : SmallMSPair κ L R) : pCore 2 H ≤ T :=
  (relative_radical h).twoCore_le

theorem relative_residual (h : SmallMSPair κ L R) : pResidual 2 H = K :=
  MSCentralOrbit.component_eq_residual K T h.component (edge_two_group h) (relative_product h)

theorem relative_normal (h : SmallMSPair κ L R) : (K).Normal := by
  rw [← relative_residual h]
  infer_instance

theorem relative_twoPerfect (h : SmallMSPair κ L R) : IsPPerfect 2 K := by
  rw [← relative_residual h]
  exact isPPerfect_pResidual 2

theorem core_self_centralizing (h : SmallMSPair κ L R) :
    centralizer (pCore 2 H : Set H) ≤ pCore 2 H := by
  rw [← h.fitting]
  exact centralizer_generalizedFitting_le H

theorem edge_ne_bot (h : SmallMSPair κ L R) : T ≠ ⊥ := by
  intro ht
  have hq : pCore 2 H = ⊥ := le_bot_iff.mp (ht ▸ core_le_edge h)
  have hc := core_self_centralizing h
  rw [hq] at hc
  have hb : (⊤ : Subgroup H) = ⊥ := le_bot_iff.mp (by
    intro x _
    apply hc
    intro y hy
    have hy' : y = 1 := hy
    rw [hy',one_mul,mul_one])
  let : Group.IsSolvable H := Group.isSolvable_of_top_eq_bot H hb
  exact h.component.not_isSolvable inferInstance

omit [Finite G] in
theorem edge_characteristic (h : SmallMSPair κ L R) : MSCharacteristicCondition T := by
  intro C hC hne hn
  let e : T ≃* R := subgroupOfEquivOfLe le_sup_right
  let D := C.map e.toMonoidHom
  have hD : D.Characteristic := by
    apply characteristic_iff_le_comap.mpr
    intro a x hx
    obtain ⟨y,hy,rfl⟩ := hx
    let b : MulAut T := e.trans (a.trans e.symm)
    exact ⟨b y,(characteristic_iff_le_comap.mp hC b) hy,e.apply_symm_apply _⟩
  have he : (D.map R.subtype).subgroupOf (L ⊔ R) = C.map (T).subtype := by
    apply map_injective (L ⊔ R).subtype_injective
    rw [map_subgroupOf_eq_of_le ((map_subtype_le D).trans le_sup_right),map_map,map_map]
    rfl
  exact hne ((map_eq_bot_iff_of_injective C e.injective).mp
    (h.characteristic D hD (he.symm ▸ hn)))

def relativeCoreEquiv (h : SmallMSPair κ L R)
    (e : (L ⧸ centralPreimage (pCore 2 L)) ≃*
      commutator (Atlas.G2.Model (ZMod 2))) :
    (K ⧸ pCore 2 K) ≃* commutator (Atlas.G2.Model (ZMod 2)) := by
  let eK : K ≃* L := subgroupOfEquivOfLe le_sup_left
  exact (QuotientGroup.congr _ _ eK (pCore_map_iso 2 eK)).trans (h.g2CoreQuotientEquiv e)

theorem relativeCoreEquiv_apply (h : SmallMSPair κ L R)
    (e : (L ⧸ centralPreimage (pCore 2 L)) ≃*
      commutator (Atlas.G2.Model (ZMod 2))) (k : K) :
    relativeCoreEquiv h e (QuotientGroup.mk' (pCore 2 K) k) =
      e (QuotientGroup.mk' (centralPreimage (pCore 2 L))
        ((subgroupOfEquivOfLe le_sup_left) k)) :=
  h.g2CoreQuotientEquiv_apply e _

/-- The commutator used by MS93 is the entire intrinsic block core. -/
theorem intrinsic_core_eq (h : SmallMSPair κ L R) :
    ⁅pCore 2 H,K⁆ = (blockU K).map (K).subtype := by
  let := relative_normal h
  exact MSCentralOrbit.commutatorCore_eq_intrinsic K (relative_twoPerfect h)

/-- Mapping the MS93 commutator back to G gives the original blockU L,
not merely a constituent or an isomorphic unnamed subgroup. -/
theorem intrinsic_core_map (h : SmallMSPair κ L R) :
    (⁅pCore 2 H,K⁆).map (H).subtype = (blockU L).map L.subtype := by
  rw [intrinsic_core_eq h,map_map]
  let eK : K ≃* L := subgroupOfEquivOfLe le_sup_left
  have hcomp : (H).subtype.comp (K).subtype = L.subtype.comp eK.toMonoidHom := rfl
  rw [hcomp,← map_map]
  congr 1
  rw [blockU,map_commutator,pCore_map_iso,map_top_of_surjective _ eK.surjective,blockU]

end G2Reconstruction
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
