module

public import Stellmacher.Recognition.Parrott.SecondNormalizer
public import Stellmacher.Recognition.Parrott.SecondNormalizerTransport
public import Stellmacher.Recognition.Parrott.ChosenCoreFusionUnderSelfNormalizer

/-!
# Excluding core fusion outside the derived subgroup

Put H=C_G(z), J=O₂(H), and E the ambient image of J′. Under derived weak
closure and the supplied second self-normalizer equality, no element of
J outside E is conjugate to z.

A hypothetical conjugate is an involution and hence defines a second
elementary witness. Transport of self-normalization between the supplied
witness and this new witness allows the chosen-involution fusion exclusion
to apply. In particular, no conjugacy between z and the original chosen
involution is assumed, and the original F and Sylow subgroup are retained.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
pp.673–674 and p.676, from “Next consider the case” through the odd-order
normalizer-action contradiction.
-/

open Subgroup

namespace Stellmacher.Recognition

/-- Derived weak closure and self-normalization of the supplied second
elementary subgroup exclude conjugates of z in the core outside its derived
subgroup. -/
public theorem parrott_not_isConj_of_core_not_mem_derived_of_second_normalizer_eq
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (z : G) (h : ParrottCentralizerHypotheses z)
    (d : ParrottSecondElementaryData z)
    (hself : normalizer (d.F : Set G) = (d.sylow : Subgroup G))
    (hderived : ∀ t : G, t ∈ (commutator (pCore 2 (centralizer ({z} : Set G)))).map
      ((centralizer ({z} : Set G)).subtype.comp
        (pCore 2 (centralizer ({z} : Set G))).subtype) → IsConj z t → t = z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    ∀ u : G, u ∈ J.map H.subtype → u ∉ E → ¬ IsConj z u := by
  intro H J E u huJ huE hconj
  obtain ⟨a, haJ, rfl⟩ := huJ
  change IsConj z (a : G) at hconj
  have ha2G : orderOf (a : G) = 2 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    rw [← hg]
    exact ((MulAut.conj g).orderOf_eq z).trans h.involution
  have ha2 : orderOf a = 2 := (Subgroup.orderOf_coe a).symm.trans ha2G
  have haD : a ∉ (commutator J).map J.subtype := by
    intro haD
    apply huE
    have hmap : ((commutator J).map J.subtype).map H.subtype = E := map_map _ _ _
    exact hmap ▸ mem_map_of_mem H.subtype haD
  obtain ⟨e, hea⟩ := parrott_second_elementary_of_core_involution z h a haJ ha2 haD
  have heself : normalizer (e.F : Set G) = (e.sylow : Subgroup G) :=
    d.normalizer_eq_sylow_of_normalizer_eq_sylow e h hself
  apply parrott_not_isConj_second_involution_of_normalizer_eq hns hN z h e heself hderived
  simpa only [hea] using hconj

end Stellmacher.Recognition
