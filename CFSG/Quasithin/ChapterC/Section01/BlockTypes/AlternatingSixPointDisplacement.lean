module
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Quotient
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Centralizer
public import Theory.SpecificGroups.AlternatingSix.TwoPrimaryInvolutionData
public import Theory.SpecificGroups.Alternating.FourPairCore
public import Theory.GroupTheory.PCoreSurjective
public import Theory.GroupTheory.PCoreLocalSetup
/-!
# Central attachments and elementary point displacement for A₆

The canonical quotient K/U(K) is a perfect central two-cover of A₆.
The checked Schur-cover involution theorem bounds its kernel by two and
excludes the double cover when an element outside O₂(K) squares into U(K).
Consequently an elementary subgroup of a point radical mapping onto A₄
has its radical commutators in U(K). A short group's center is bounded by
twice the fixed part of U(K), retaining a possible central attachment.

The actual component and mixed-pair applications are in Chapter13,
FixedCoreSource/Nonsolvable/ReciprocalSix. No splitting of K is assumed.
Source: Aschbacher–Smith C.1.8, C.1.13 and 13.4.15, printed pp.123–125,912;
the cover input is GLS3 5.2.3–4, via AlternatingSix.TwoPrimaryInvolutionData.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC
variable {K : Type*} [Group K] [Finite K] [Group.IsPerfect K]

private def sixCover (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6)) :
    PerfectCentralCovering.Cover (K ⧸ blockU K) (alternatingGroup (Fin 6)) where
  toMonoidHom := e.toMonoidHom.comp blockCoreProjection
  surjective := e.surjective.comp blockCoreProjection_surjective
  isPerfect := inferInstance
  ker_le_center := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,blockCoreProjection_ker]
    exact blockU_core_image_le_center

omit [Finite K] in
private theorem sixCover_ker (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6)) :
    (sixCover e).toMonoidHom.ker = (pCore 2 K).map (QuotientGroup.mk' (blockU K)) := by
  change (e.toMonoidHom.comp blockCoreProjection).ker = _
  rw [MonoidHom.ker_comp_of_injective _ _ e.injective,blockCoreProjection_ker]

theorem alternatingSix_core_image_card_le_two
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6)) :
    Nat.card ((pCore 2 K).map (QuotientGroup.mk' (blockU K))) ≤ 2 := by
  have hp : IsPGroup 2 (sixCover e).toMonoidHom.ker := by
    rw [sixCover_ker]; exact pCore_isPGroup.map _
  rw [←sixCover_ker e]
  rcases AlternatingSix.twoPrimaryInvolutionData _ (sixCover e) hp with hh | ⟨hh,_⟩
  · rw [hh,card_bot]; decide
  · omega

theorem alternatingSix_core_eq_blockU_of_square_mem
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))
    (x : K) (hx : x ∉ pCore 2 K) (hs : x ^ 2 ∈ blockU K) :
    pCore 2 K = blockU K := by
  have hp : IsPGroup 2 (sixCover e).toMonoidHom.ker := by
    rw [sixCover_ker]; exact pCore_isPGroup.map _
  have hz : (sixCover e).toMonoidHom.ker = ⊥ := by
    rcases AlternatingSix.twoPrimaryInvolutionData _ (sixCover e) hp with hz | ⟨_,hi⟩
    · exact hz
    · have hh := hi (QuotientGroup.mk' (blockU K) x) (by
        rw [←map_pow]; exact (QuotientGroup.eq_one_iff _).mpr hs)
      have he : e (QuotientGroup.mk' (pCore 2 K) x) = 1 := hh
      exact (hx ((QuotientGroup.eq_one_iff x).mp
        (e.injective (he.trans e.map_one.symm)))).elim
  apply le_antisymm ?_ blockU_le_core
  intro y hy
  apply (QuotientGroup.eq_one_iff y).mp
  have hm := mem_map_of_mem (QuotientGroup.mk' (blockU K)) hy
  rw [←sixCover_ker e,hz,mem_bot] at hm
  exact hm

theorem alternatingSix_elementary_point_displacement
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))
    (J P : Subgroup K) [IsElementaryAbelian 2 P]
    (hP : P ≤ J.pCoreIn 2)
    (f : J →* alternatingGroup (Fin 4)) (hf : Function.Surjective f)
    (hk : f.ker = (pCore 2 K).subgroupOf J) :
    ⁅P,J.pCoreIn 2⁆ ≤ blockU K := by
  by_cases hcore : P ≤ pCore 2 K
  · exact commutator_mono hcore le_top
  obtain ⟨x,hx,hxq⟩ := Set.not_subset.mp hcore
  have hQ : pCore 2 K = blockU K := alternatingSix_core_eq_blockU_of_square_mem e x hxq
    (by rw [elemPow_eq_one_of_isElementaryAbelian x hx]; exact one_mem _)
  have hp : IsPGroup 2 f.ker := by rw [hk]; exact pCore_isPGroup.comap_subtype
  have hmap : pCore 2 J ≤ (pCore 2 (alternatingGroup (Fin 4))).comap f :=
    (f.comap_pCore_of_ker_isPGroup hf hp).ge
  let : IsMulCommutative (pCore 2 (alternatingGroup (Fin 4))) := by
    rw [AlternatingFourPair.twoCore_eq_kleinFour]
    exact (alternatingGroup.kleinFour_isKleinFour (by simp)).isMulCommutative
  have hc : ⁅pCore 2 J,pCore 2 J⁆ ≤ f.ker := by
    apply commutator_le.mpr
    intro a ha b hb
    change f ⁅a,b⁆ = 1
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (congrArg Subtype.val (mul_comm (⟨f a,hmap ha⟩ : pCore 2 (alternatingGroup (Fin 4)))
        ⟨f b,hmap hb⟩))
  have hkm : f.ker.map J.subtype ≤ pCore 2 K := by
    rintro x ⟨a,ha,rfl⟩
    have ha' : a ∈ (pCore 2 K).subgroupOf J := hk ▸ ha
    exact ha'
  have hderived := (map_mono (f := J.subtype) hc).trans hkm
  rw [map_commutator,hQ] at hderived
  exact (commutator_mono hP le_rfl).trans hderived

/-- A central attachment adds at most one binary dimension to the fixed
part of the intrinsic layer of an A₆ block. -/
theorem IsShort.alternatingSix_center_card_le
    (h : IsShort K) (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6)) :
    Nat.card (center K) ≤ 2 * Nat.card (blockU K ⊓ center K : Subgroup K) := by
  let q := QuotientGroup.mk' (blockU K)
  let f := q.subgroupMap (center K)
  have hp : center K ≤ pCore 2 K :=
    (center_le_centralizer _).trans h.centralizer_blockU.le
  have him : Nat.card ((center K).map q) ≤ 2 :=
    (Nat.card_le_card_of_injective (inclusion (map_mono hp)) (inclusion_injective _)).trans (alternatingSix_core_image_card_le_two e)
  have hk : f.ker = (blockU K ⊓ center K).subgroupOf (center K) := by
    ext x
    change f x = 1 ↔ x.val ∈ blockU K ⊓ center K
    rw [Subtype.ext_iff]
    change q x.val = 1 ↔ x.val ∈ blockU K ⊓ center K
    exact (QuotientGroup.eq_one_iff x.val).trans
      (by simp only [mem_inf,and_iff_left x.property])
  have hc := card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f
    (q.subgroupMap_surjective (center K))).toEquiv,hk,
    Nat.card_congr (subgroupOfEquivOfLe
      (show blockU K ⊓ center K ≤ center K from inf_le_right)).toEquiv] at hc
  rw [hc]
  exact Nat.mul_le_mul_right _ him

end CFSG.Quasithin.ChapterC
