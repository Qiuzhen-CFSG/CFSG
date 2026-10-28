module

public import Stellmacher.Recognition.Parrott.SecondNormalizer
public import Stellmacher.Recognition.Parrott.DerivedFusionUnderSelfNormalizer
public import Stellmacher.Recognition.Parrott.CoreOutsideDerivedFusionUnderSelfNormalizer

/-!
# Core fusion under Parrott's second self-normalizer assumption

Put H=C_G(z) and J=O₂(H). If the normalizer of the supplied second
elementary subgroup F equals its supplied Sylow subgroup T, every
conjugate of z in the ambient image of J equals z.

Split according to membership in the ambient image E of J′. The derived
fusion theorem handles E and supplies the derived weak closure premise
of the fusion exclusion outside E. Both cases retain the same F and T.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
Lemma 5, pp.676–677, using the local geometry of pp.673–674.
-/

open Subgroup

namespace Stellmacher.Recognition

/-- Under the second self-normalizer equality, z has no distinct conjugate
in the core of its centralizer, with the supplied F and T retained. -/
public theorem parrott_core_fusion_eq_of_second_normalizer_eq
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (z : G) (h : ParrottCentralizerHypotheses z)
    (d : ParrottSecondElementaryData z)
    (hself : normalizer (d.F : Set G) = (d.sylow : Subgroup G)) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    ∀ t : G, t ∈ J.map H.subtype → IsConj z t → t = z := by
  classical
  intro H J t ht hconj
  let E := (commutator J).map (H.subtype.comp J.subtype)
  have hderived := parrott_derived_fusion_eq_of_second_normalizer_eq hns hN z h d hself
  by_cases htE : t ∈ E
  · exact hderived t htE hconj
  · exact (parrott_not_isConj_of_core_not_mem_derived_of_second_normalizer_eq
      hns hN z h d hself hderived t ht htE hconj).elim

end Stellmacher.Recognition
