module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientHermitianThompsonWitness
public import Theory.GroupTheory.ElementaryThompsonQuotientFusion
public import Stellmacher.ElementaryAbelianMaxSylowImages

/-!
# The nonzero original quotient witness and its returning conjugates

The maximum elementary witness is mapped through the actual quotient
KT/O₂(KT). Its nontrivial image lies in the image of O₂(XT), and every
conjugate of that whole image returning to T* still lies in this same
core image. No assertion about existence of an escaping conjugate is
an input or a conclusion here; that is the remaining odd PSL₂ calculation.

Source: Aschbacher--Smith 6.1.4, final paragraph, printed p.666.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
attribute [local instance] Representation.SL2.BinarySmall.spaceBinaryModule
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V K : Subgroup G} {n : ℕ}

/-- The actual maximum elementary subgroup survives in KT/O₂(KT), and
every returning conjugate of its entire image stays in the literal core image. -/
theorem original_hermitian_outside_quotient_witness
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (Representation.SL2.BinarySmall.hermitian 2)) (hK : ¬ K ≤ M) :
    let J := K ⊔ (T : Subgroup G)
    let q := QuotientGroup.mk' (pCore 2 J)
    let S := (quinticResidual T L ⊔ (T : Subgroup G)).pCoreIn 2
    ∃ A ∈ elementaryAbelianMaxSubgroups (T : Subgroup G),
      (A.subgroupOf J).map q ≠ ⊥ ∧
      (A.subgroupOf J).map q ≤ (S.subgroupOf J).map q ∧
      ∀ y : J ⧸ pCore 2 J,
        ((A.subgroupOf J).map q).map (MulAut.conj y).toMonoidHom ≤
            ((T : Subgroup G).subgroupOf J).map q →
        ((A.subgroupOf J).map q).map (MulAut.conj y).toMonoidHom ≤
            (S.subgroupOf J).map q := by
  let J := K ⊔ (T : Subgroup G)
  let q := QuotientGroup.mk' (pCore 2 J)
  let S := (quinticResidual T L ⊔ (T : Subgroup G)).pCoreIn 2
  obtain ⟨A,hA,hAS,hAR⟩ := original_hermitian_outside_maximum_elementary_witness h hout hm hK
  have hTJ : (T : Subgroup G) ≤ J := le_sup_right
  have hAJ : A ≤ J := hA.1.trans hTJ
  have hmax : A.subgroupOf J ∈ elementaryAbelianMaxSubgroups
      ((T : Subgroup G).subgroupOf J) := by
    apply (maxFamily_map_injective_iff J.subtype J.subtype_injective
      ((T : Subgroup G).subgroupOf J) (A.subgroupOf J)).mp
    rwa [map_subgroupOf_eq_of_le hAJ,map_subgroupOf_eq_of_le hTJ]
  have hJT : elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) :=
    sSup_le fun _ ha => ha.1
  have hJS : elementaryAbelianMaxJ (T : Subgroup G) ≤ S :=
    le_pCoreIn_of_normalizes (T.isPGroup'.to_le hJT) (hJT.trans le_sup_right)
      (original_hermitian_quintic_normalizes_thompson h hout hm)
  have hsub : elementaryAbelianMaxJ ((T : Subgroup G).subgroupOf J) ≤
      S.subgroupOf J := by
    apply sSup_le
    intro B hB
    have hBm := (maxFamily_map_injective_iff J.subtype J.subtype_injective
      ((T : Subgroup G).subgroupOf J) B).mpr hB
    rw [map_subgroupOf_eq_of_le hTJ] at hBm
    intro b hb
    exact hJS ((le_sSup hBm) (mem_map_of_mem J.subtype hb))
  refine ⟨A,hA,?_,map_mono (subgroupOf_mono J hAS),?_⟩
  · intro hz
    have hk : A.subgroupOf J ≤ q.ker := (map_eq_bot_iff (A.subgroupOf J)).mp hz
    rw [QuotientGroup.ker_mk'] at hk
    apply hAR
    intro a ha
    exact ⟨⟨a,hAJ ha⟩,hk ha,rfl⟩
  · intro y hy
    have hk : q.ker ≤ (T : Subgroup G).subgroupOf J := by
      rw [QuotientGroup.ker_mk']
      exact pCore_isPGroup.le_sylow_of_normal (T.subtype hTJ)
    exact (maxFamily_quotient_conjugate_le_maxJ _ q
      (QuotientGroup.mk'_surjective _) hk hmax y hy).trans (map_mono hsub)

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
