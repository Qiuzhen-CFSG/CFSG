module

public import Stellmacher.Recognition.Parrott.LocalInputs
public import Stellmacher.Recognition.Parrott.CoreFusionLocal
public import Stellmacher.Recognition.Parrott.OuterFusionUnrestricted
public import Stellmacher.Recognition.SimpleInvolutionFusion

/-!
# Growth of the actual second normalizer from local inputs

If N_G(F)=T, the derived normalizer identity gives weak closure in the core,
and the unrestricted outer calculation excludes all remaining fusion in T.
The distinct-conjugate theorem for a nonsolvable simple group contradicts
this. Hence T<N_G(F). This is the growth input consumed by the local
normalizer-fusion assembly; no ambient N₂ conclusion is asserted or used.

Source: Parrott (1972), Lemma 5, printed pp.675–677.
-/

open Subgroup

namespace Stellmacher.Recognition.ParrottSecondElementaryData

/-- Parrott's actual second elementary normalizer properly contains the supplied
Sylow under the local normalizer inputs supplied by the quasithin source. -/
public theorem sylow_lt_normalizer_of_local_inputs
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] {z : G}
    (d : ParrottSecondElementaryData z) (hns : ¬ Group.IsSolvable G)
    (h : ParrottCentralizerHypotheses z) (hlocal : ParrottLocalInputs z) :
    (d.sylow : Subgroup G) < normalizer (d.F : Set G) := by
  apply lt_of_le_of_ne d.sylow_le_normalizer
  intro heq
  have hcore := parrott_core_fusion_eq_of_second_normalizer_eq_of_derived_normalizer
    z hlocal.derived_normalizer h d heq.symm
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
    exact d.outer_not_isConj_of_core_weakClosure_unrestricted h hcore
      t t.property htJ ht2 hconj

end Stellmacher.Recognition.ParrottSecondElementaryData
