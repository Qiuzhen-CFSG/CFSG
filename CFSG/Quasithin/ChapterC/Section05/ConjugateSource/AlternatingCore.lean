module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingPhiNormalizer.Witness
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Centralizer
public import Theory.SpecificGroups.AlternatingFiveInvolutionCover

/-!
# The full two-core of the actual alternating-five block

Choose a transposition lift v in the elementary conjugate Uˣ and the inner
exchange r in R∩K. Since r normalizes Uˣ, their commutator is an involution
in Uˣ∩K inducing the nontrivial diagonal. Its image in K/U is therefore an
involution with nontrivial image in K/O₂(K). The actual perfect central
cover comparison rules out a nontrivial O₂(K)/U, proving O₂(K)=U.

Source: Aschbacher–Smith, C.5.6(7), printed p.159.
-/

public section
open Subgroup BinaryPermutation
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {R K L : Subgroup G}

theorem AlternatingPairSetup.exists_diagonal_involution_in_block
    (h : AlternatingPairSetup R K L) (x : G) (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    ∃ a : (K ⊔ ChapterB.baumann R : Subgroup G),
      (a : G) ∈ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ⊓ K ∧
      a ^ 2 = 1 ∧ h.action a = pairDiagonal := by
  let S := ChapterB.baumann R
  let U := sourceModule K
  let V := U.map (MulAut.conj x⁻¹).toMonoidHom
  have hVS : V ≤ S := (map_mono h.module_le).trans_eq (mem_normalizer_iff_map_conj_eq.mp
    (Stellmacher.normalizer_le_normalizer_baumann R ((normalizer (R : Set G)).inv_mem hx)))
  have hv : ChapterB.Offenders.pairSwap 5 0 ∈ (V.subgroupOf (K ⊔ S)).map h.action := by
    rw [h.conjugate_action_image x hx hnc]
    exact ChapterB.Offenders.pairSwap_mem (n := 5) (m := 2) 0 (by decide)
  obtain ⟨v,hv,hva⟩ := hv
  obtain ⟨r,hr,hra⟩ := h.pairExchange_mem
  have hn := h.transvection_normalizes x hx
  have hRV : ⁅V,R ⊓ K⁆ ≤ V := le_normalizer_iff_commutator_le_left.mp (hn.2.2.trans hn.2.1)
  have hVK : ⁅V,K⁆ ≤ K := le_normalizer_iff_commutator_le_right.mp (hVS.trans h.normalizes)
  have haV : ⁅(v : G),(r : G)⁆ ∈ V := hRV (commutator_mem_commutator hv hr)
  have haK : ⁅(v : G),(r : G)⁆ ∈ K := hVK (commutator_mem_commutator hv hr.2)
  let : IsElementaryAbelian 2 U := by
    let := h.block.2.1.elementary
    exact IsElementaryAbelian.map K.subtype
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map (MulAut.conj x⁻¹).toMonoidHom
  refine ⟨⁅v,r⁆,⟨haV,haK⟩,?_,?_⟩
  · exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian _ haV)
  · rw [map_commutatorElement,hva,hra]
    decide +kernel

theorem AlternatingPairSetup.exists_block_quotient_involution
    (h : AlternatingPairSetup R K L) (x : G) (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    ∃ a : K ⧸ blockU K, a ^ 2 = 1 ∧ blockCoreProjection a ≠ 1 := by
  obtain ⟨a,ha,ha2,haa⟩ := h.exists_diagonal_involution_in_block x hx hnc
  let k : K := ⟨a,ha.2⟩
  have ha2G : (a : G) ^ 2 = 1 := congrArg (fun z : (K ⊔ ChapterB.baumann R : Subgroup G) => (z : G)) ha2
  have hk2 : k ^ 2 = 1 := Subtype.ext ha2G
  refine ⟨QuotientGroup.mk' (blockU K) k,by rw [← map_pow,hk2,map_one],?_⟩
  intro hk
  have hkcore : k ∈ pCore 2 K := by
    change QuotientGroup.mk' (pCore 2 K) k = 1 at hk
    exact (QuotientGroup.eq_one_iff _).mp hk
  have hc : k ∈ centralizer (blockU K : Set K) := h.block.2.1.centralizer_blockU.symm ▸ hkcore
  have haC : (a : G) ∈ centralizer (sourceModule K : Set G) := by
    rintro u ⟨b,hb,rfl⟩
    exact congrArg Subtype.val (hc b hb)
  have he : h.action a = 1 := by
    change a ∈ h.action.ker
    rw [h.action_kernel]
    exact haC
  have hd : pairDiagonal ≠ 1 := by decide +kernel
  exact hd (haa.symm.trans he)
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource

namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource

variable {G : Type*} [Group G] [Finite G] {R K L : Subgroup G}

theorem AlternatingPairSetup.block_core_eq_module
    (h : AlternatingPairSetup R K L) (x : G) (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    pCore 2 K = blockU K := by
  obtain ⟨rho,⟨model⟩,_⟩ := h.block.2.2
  let f := model.quotientIso.toMonoidHom.comp (blockCoreProjection (L := K))
  have hf : Function.Surjective f := model.quotientIso.surjective.comp blockCoreProjection_surjective
  have hk : f.ker = (pCore 2 K).map (QuotientGroup.mk' (blockU K)) := by
    dsimp only [f]
    rw [MonoidHom.ker_comp_of_injective _ _ model.quotientIso.injective,blockCoreProjection_ker]
  have hcentral : f.ker ≤ center (K ⧸ blockU K) := by rw [hk]; exact blockU_core_image_le_center
  have hp : IsPGroup 2 f.ker := by rw [hk]; exact pCore_isPGroup.map _
  let : Group.IsPerfect (alternatingGroup (Fin 5)) := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect (K ⧸ blockU K) :=
    IsPPerfect.isPerfect_of_surjective_pGroup_kernel (h.block.2.1.quotient_twoPerfect (blockU K)) f hf hp
  obtain ⟨a,ha,hna⟩ := h.exists_block_quotient_involution x hx hnc
  have hna' : f a ≠ 1 := by
    intro he
    apply hna
    exact model.quotientIso.injective (he.trans (map_one model.quotientIso).symm)
  have hinj := alternatingGroup.injective_of_central_two_kernel_of_involution f hf hcentral hp a ha hna'
  have hzero : (pCore 2 K).map (QuotientGroup.mk' (blockU K)) = ⊥ :=
    hk.symm.trans ((MonoidHom.ker_eq_bot_iff f).mpr hinj)
  apply le_antisymm _ blockU_le_core
  have hle := (Subgroup.map_eq_bot_iff _).mp hzero
  simpa only [QuotientGroup.ker_mk'] using hle
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource

