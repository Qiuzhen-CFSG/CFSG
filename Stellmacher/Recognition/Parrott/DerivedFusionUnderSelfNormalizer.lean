module

public import Stellmacher.Recognition.Parrott.SecondNormalizer
public import Stellmacher.Recognition.Parrott.DerivedLocalFusion

/-!
# Derived-core fusion under Parrott's second self-normalizer assumption

Put H=C_G(z), J=O₂(H), and E the ambient image of J′. If the normalizer
of the supplied second elementary subgroup F equals its supplied Sylow
subgroup T, every conjugate of z in E equals z.

The local fusion exclusion places such a conjugate in ⟨z⟩. Since z has
order two, this cyclic subgroup consists of 1 and z; conjugacy preserves
order and excludes 1.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
Lemma 5, pp.676–677, using the local geometry of pp.673–674.
-/

open Subgroup

namespace Stellmacher.Recognition

/-- Under the second self-normalizer equality, z has no distinct conjugate
in the derived core, with the supplied F and T retained. -/
public theorem parrott_derived_fusion_eq_of_second_normalizer_eq
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (_hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (z : G) (h : ParrottCentralizerHypotheses z)
    (d : ParrottSecondElementaryData z)
    (hself : normalizer (d.F : Set G) = (d.sylow : Subgroup G)) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    ∀ t : G, t ∈ E → IsConj z t → t = z := by
  classical
  intro H J E t ht hconj
  have htZ : t ∈ zpowers z := by
    by_contra htZ
    exact parrott_derived_not_isConj_of_second_normalizer_eq hN z h d hself
      t ht htZ hconj
  have htorder : orderOf t = 2 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    rw [← hg]
    exact ((MulAut.conj g).orderOf_eq z).trans h.involution
  have ht_cases : t = 1 ∨ t = z := by
    rw [mem_zpowers_iff_mem_range_orderOf, h.involution] at htZ
    obtain ⟨n, hn, heq⟩ := Finset.mem_image.mp htZ
    have hnlt : n < 2 := Finset.mem_range.mp hn
    interval_cases n
    · exact Or.inl (by simpa using heq.symm)
    · exact Or.inr (by simpa using heq.symm)
  rcases ht_cases with rfl | rfl
  · simp at htorder
  · rfl

end Stellmacher.Recognition
