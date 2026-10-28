module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.SmallCenter.OriginalBaumann
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed
public import Theory.GroupTheory.PGroup.CharacteristicCenterReduction
public import Stellmacher.BaumannNormalizer
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Solvable
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.FullSolvableSource

/-!
# The fixed original characteristic pair forces a genuine local block

A nonzero characteristic subgroup of Baum(T) is normalized by T. If its
exponent is two and |Ω₁(Z(T))|=2, its intersection with Z(T) contains that
entire original seed. Thus the first, central alternative for the selected
local-class member would place it in T, contradicting its generation of M.
The second, normal alternative would make both the selected subgroup and
T normalize the second member, contradicting the prescribed original M.

The complete universal C.1.18 property is retained for ONE pair in the
original Baum(T). The selected subgroup and its literal InLocalClass are
constructed; only the exact earlier uniform theorem remains external.
Source: Aschbacher--Smith C.1.26/28 and 15.4.7, printed pp.132--134,1158.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.InitialSource.SmallCenter
open FamilySource FamilySource.ModuleStructure ChapterC.GlaubermanNiles
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem omega_le_normal_two_subgroup (T : Sylow 2 G) (C : Subgroup G)
    (hCT : C ≤ (T : Subgroup G)) (hTN : (T : Subgroup G) ≤ normalizer (C : Set G))
    (hne : C ≠ ⊥) (hexp : ∀ x ∈ C,x^2=1)
    (hZ : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 2) :
    omegaOneCenterAmbient (T : Subgroup G) ≤ C := by
  let E := C.subgroupOf (T : Subgroup G)
  let : E.Normal := (normal_subgroupOf_iff_le_normalizer hCT).mpr hTN
  have hE : E ≠ ⊥ := by
    intro he
    have hm := congrArg (map (T : Subgroup G).subtype) he
    rw [map_subgroupOf_eq_of_le hCT,Subgroup.map_bot] at hm
    exact hne hm
  let D := (center (T : Subgroup G) ⊓ E).map (T : Subgroup G).subtype
  have hD : D ≠ ⊥ := by
    intro he
    exact center_inf_ne_bot_of_normal T.isPGroup' E hE
      ((map_eq_bot_iff_of_injective _ (T : Subgroup G).subtype_injective).mp he)
  have hDC : D ≤ C := (map_mono inf_le_right).trans_eq (map_subgroupOf_eq_of_le hCT)
  have hDZ : D ≤ omegaOneCenterAmbient (T : Subgroup G) := by
    rintro x ⟨y,hy,rfl⟩
    apply mem_omegaOneCenterAmbient_iff _ _ |>.mpr
    exact ⟨y.property,hexp y hy.2,fun t ht =>
      congrArg Subtype.val ((mem_center_iff.mp hy.1) ⟨t,ht⟩)⟩
  have heq : D = omegaOneCenterAmbient (T : Subgroup G) :=
    eq_of_le_of_card_ge hDZ (by rw [hZ]; exact Nat.succ_le_of_lt (D.one_lt_card_iff_ne_bot.mpr hD))
  exact heq ▸ hDC

private theorem original_first_contains_seed (T : Sylow 2 G)
    (D : CharacteristicPair (ChapterB.baumann (T : Subgroup G)))
    (hZ : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 2) :
    omegaOneCenterAmbient (T : Subgroup G) ≤
      D.first.map (ChapterB.baumann (T : Subgroup G)).subtype := by
  let B := ChapterB.baumann (T : Subgroup G)
  let : D.first.Characteristic := D.first_characteristic
  apply omega_le_normal_two_subgroup T _ ((map_subtype_le D.first).trans inf_le_left)
  · exact ((T : Subgroup G).le_normalizer.trans (normalizer_le_normalizer_baumann _)).trans
      (normalizer_le_normalizer_characteristic_image _ D.first)
  · exact fun he => D.first_ne_bot ((map_eq_bot_iff_of_injective _ B.subtype_injective).mp he)
  · rintro x ⟨y,hy,rfl⟩
    exact congrArg B.subtype ((mem_omegaCenter_iff y).mp (D.first_le_omegaCenter hy)).1
  · exact hZ

/-- The original fixed pair forces the block alternative on the actual
selected overgroup; the other two clauses contradict its prescribed failure. -/
theorem member_fixed_pair_block {T : Sylow 2 G} {M X : Subgroup G} {s : ℕ}
    (h : Input KnownSimple.IsKnownSimple T M X s)
    (hZ : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (D : CharacteristicPair (ChapterB.baumann (T : Subgroup G)))
    (hD : D.Universal.{u,u})
    (hfail : ¬ M ≤ normalizer (D.second.map (ChapterB.baumann (T : Subgroup G)).subtype : Set G)) :
    ∃ (K : Subgroup M) (e : ChapterB.baumann (T : Subgroup G) →* K),
      InLocalClass e ∧ (∀ b, ((e b : M) : G) = (b : G)) ∧
      K ⊔ (T.subtype h.sylow_le : Subgroup M) = ⊤ ∧ BlockAlternative K := by
  obtain ⟨K,e,hclass,he,hgen⟩ := member_original_baumann_localClass h hZ
  refine ⟨K,e,hclass,he,hgen,?_⟩
  rcases hD K e hclass with hc | hn | hb
  · have hzD := original_first_contains_seed T D hZ
    have hKT : K ≤ (T.subtype h.sylow_le : Subgroup M) := by
      intro k hk
      have hcG : (k : G) ∈ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) := by
        intro z hz
        obtain ⟨b,hb,hbz⟩ := hzD hz
        have hh := mem_center_iff.mp (hc (mem_map_of_mem e hb)) (⟨k,hk⟩ : K)
        have hh' := congrArg (fun a : K => ((a : M) : G)) hh
        change (b : G) = z at hbz
        simpa only [Subgroup.coe_mul,he,hbz] using hh'.symm
      change (k : G) ∈ (T : Subgroup G)
      rwa [h.center_centralizer] at hcG
    have heq : (T.subtype h.sylow_le : Subgroup M) = ⊤ := by
      simpa only [sup_eq_right.mpr hKT] using hgen
    exact ((member_minimal_parabolic h hZ).1.1.ne heq).elim
  · let B := ChapterB.baumann (T : Subgroup G)
    let C := D.second.map B.subtype
    let : D.second.Characteristic := D.second_characteristic
    have hTN : (T : Subgroup G) ≤ normalizer (C : Set G) :=
      ((T : Subgroup G).le_normalizer.trans (normalizer_le_normalizer_baumann _)).trans
        (normalizer_le_normalizer_characteristic_image _ D.second)
    have hKnorm : K.map M.subtype ≤ normalizer (C : Set G) := by
      apply le_normalizer_iff.mpr
      rintro g ⟨k,hk,rfl⟩ c ⟨b,hb,rfl⟩
      have hm := hn.conj_mem (e b) (mem_map_of_mem e hb) (⟨k,hk⟩ : K)
      obtain ⟨b',hb',heq⟩ := hm
      refine ⟨b',hb',?_⟩
      have hh := congrArg (fun a : K => ((a : M) : G)) heq
      change (b' : G) = (k : G) * (b : G) * (k : G)⁻¹
      simpa only [Subgroup.coe_mul,Subgroup.coe_inv,he] using hh
    have hm := congrArg (map M.subtype) hgen
    rw [Subgroup.map_sup,Sylow.coe_subtype,map_subgroupOf_eq_of_le h.sylow_le,
      ←MonoidHom.range_eq_map,range_subtype] at hm
    exact (hfail (hm ▸ sup_le hKnorm hTN)).elim
  · exact hb

/-- Solvability selects the original A₃ block on the same two-residual. -/
theorem member_fixed_pair_alternatingThree {T : Sylow 2 G} {M X : Subgroup G} {s : ℕ}
    (h : Input KnownSimple.IsKnownSimple T M X s)
    (hZ : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (D : CharacteristicPair (ChapterB.baumann (T : Subgroup G)))
    (hD : D.Universal.{u,u})
    (hfail : ¬ M ≤ normalizer (D.second.map (ChapterB.baumann (T : Subgroup G)).subtype : Set G)) :
    ∃ (K : Subgroup M) (e : ChapterB.baumann (T : Subgroup G) →* K),
      InLocalClass e ∧ (∀ b, ((e b : M) : G) = (b : G)) ∧
      K ⊔ (T.subtype h.sylow_le : Subgroup M) = ⊤ ∧
      ChapterC.IsBlock (pResidual 2 K) ∧ ChapterC.IsAlternatingBlock (pResidual 2 K) 3 := by
  obtain ⟨K,e,hc,he,hgen,hb,hbtype⟩ := member_fixed_pair_block h hZ D hD hfail
  let : Group.IsSolvable M := h.solvable
  refine ⟨K,e,hc,he,hgen,hb,?_⟩
  rcases hbtype with ⟨n,hn⟩ | ha
  · exact hn.not_solvable.elim
  · exact ha

/-- The raw empty-family, multiple-local, small-center source setup produces
an actual marked local A₃ block from the one universal characteristic pair.
All solvable ratio and D.1 source premises are already discharged. -/
theorem source_fixed_pair_local_block
    (hA : ∀ (H : Type u) [Group H] [Finite H],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple H)
    (hC : ∀ (H : Type u) [Group H] [Finite H],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple H)
    (h311 : RatioSource.Earlier311 (G := G))
    (hB : Chapter1.RadicalNormalizers.ThompsonSource.TheoremB216.{u})
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hmany : 1 < (maximalTwoLocalOvergroups
      (centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))).ncard)
    (hZ : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (D : CharacteristicPair (ChapterB.baumann (T : Subgroup G)))
    (hD : D.Universal.{u,u}) :
    ∃ (M X : Subgroup G) (s : ℕ) (h : Input KnownSimple.IsKnownSimple T M X s)
      (K : Subgroup M) (e : ChapterB.baumann (T : Subgroup G) →* K),
      InLocalClass e ∧ (∀ b, ((e b : M) : G) = (b : G)) ∧
      K ⊔ (T.subtype h.sylow_le : Subgroup M) = ⊤ ∧
      ChapterC.IsBlock (pResidual 2 K) ∧ ChapterC.IsAlternatingBlock (pResidual 2 K) 3 := by
  obtain ⟨hc,hex,_⟩ := FullSolvableSource.source_family_data hA hC h311 hB hG T hempty hmany
  let : D.second.Characteristic := D.second_characteristic
  obtain ⟨M,hM,hfail⟩ := exists_nonnormalizing_local T hc hmany D.second D.second_ne_bot
  obtain ⟨X,s,h⟩ := hex M hM
  obtain ⟨K,e,hc,he,hgen,hb,ha⟩ := member_fixed_pair_alternatingThree h hZ D hD hfail
  exact ⟨M,X,s,h,K,e,hc,he,hgen,hb,ha⟩

end CFSG.Quasithin.Chapter15.Section04.InitialSource.SmallCenter
