module

public import Stellmacher.Recognition.Parrott.SecondNormalizer
public import Stellmacher.Recognition.Parrott.CoreFusionUnderSelfNormalizer
public import Stellmacher.Recognition.Parrott.OuterFusionUnderSelfNormalizer
public import Stellmacher.Recognition.SimpleInvolutionFusion

/-!
# Growth of Parrott's second elementary normalizer

For any supplied second elementary data, the normalizer of F properly
contains the supplied Sylow two-subgroup T. If the two were equal, the
core and outer fusion exclusions would make z weakly closed in T.
The distinct Sylow conjugate theorem for nonsolvable simple groups
contradicts this. Thus no further choice of F or T is needed.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
Lemma 5, pp.675–677, using the local geometry of pp.673–674.
-/

open Subgroup

namespace Stellmacher.Recognition.ParrottSecondElementaryData

/-- Parrott's Lemma 5: the normalizer of the supplied second elementary
subgroup properly contains its supplied Sylow two-subgroup. -/
public theorem sylow_lt_normalizer
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] {z : G}
    (d : ParrottSecondElementaryData z) (hns : ¬ Group.IsSolvable G)
    (hN : IsNTwoGroup G) (h : ParrottCentralizerHypotheses z) :
    (d.sylow : Subgroup G) < normalizer (d.F : Set G) := by
  apply lt_of_le_of_ne d.sylow_le_normalizer
  intro heq
  have hcore := parrott_core_fusion_eq_of_second_normalizer_eq hns hN z h d heq.symm
  let zT : d.sylow := ⟨z, d.le_sylow d.z_mem_inf.2⟩
  have hzT : orderOf zT = 2 := (Subgroup.orderOf_coe zT).symm.trans h.involution
  obtain ⟨t, ht, hconj⟩ := exists_distinct_isConj_in_sylow hns d.sylow zT hzT
  by_cases htJ : (t : G) ∈ (pCore 2 (centralizer ({z} : Set G))).map
      (centralizer ({z} : Set G)).subtype
  · exact ht (Subtype.ext (hcore t htJ hconj))
  · have ht2 : orderOf (t : G) = 2 := by
      obtain ⟨g, hg⟩ := isConj_iff.mp hconj
      rw [← hg]
      exact ((MulAut.conj g).orderOf_eq z).trans h.involution
    exact d.outer_not_isConj_under_selfNormalizer hns hN h heq.symm hcore
      t t.property htJ ht2 hconj

end Stellmacher.Recognition.ParrottSecondElementaryData
