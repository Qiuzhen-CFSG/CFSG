module

public import Stellmacher.Recognition.Parrott.DerivedLocalRepresentatives
public import Stellmacher.Recognition.Parrott.DerivedTFusion
public import Stellmacher.Recognition.Parrott.DerivedVFusion

/-!
# Local fusion exclusion in Parrott's derived core

Put H=C_G(z), J=O₂(H), and E the ambient image of J′. Under the supplied
second elementary subgroup's self-normalizer equality, no element of
E outside ⟨z⟩ is conjugate to z in G.

The local conjugacy census provides representatives t and v with their
entire H-centralizers in the supplied Sylow subgroup T. The first branch
is excluded using Ω₁(C_T(t)′). The second uses C_T(v)″ when C_T(v)′ is
nonabelian, and the square subgroup ℧¹(C_T(v)′) when it is abelian.
Conjugacy in H then transports these exclusions to every element of E∖⟨z⟩.
All representative and characteristic-subgroup geometry is proved in the
imported modules; only the original hypotheses and the supplied data occur
as premises here.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
pp.673–674, the last two paragraphs of p.676, and the first paragraph of p.677.
-/

open Subgroup

namespace Stellmacher.Recognition

/-- The two local characteristic-subgroup obstructions exclude fusion of z
to any element of the derived core outside ⟨z⟩, retaining the supplied F and T. -/
public theorem parrott_derived_not_isConj_of_second_normalizer_eq
    {G : Type*} [Group G] [Finite G]
    (hN : IsNTwoGroup G) (z : G) (h : ParrottCentralizerHypotheses z)
    (d : ParrottSecondElementaryData z)
    (hself : normalizer (d.F : Set G) = (d.sylow : Subgroup G)) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    ∀ u : G, u ∈ E → u ∉ zpowers z → ¬ IsConj z u := by
  intro H J E u hu huZ hconj
  obtain ⟨t, v, ht, htZ, hv, hvZ, ht2, hzt, hv2, hzv,
    htlocal, htcard, htcenter, hvlocal, hvcard, hvcenter, hcover⟩ :=
    parrott_derived_local_representatives z h d
  rcases hcover u hu huZ with ⟨a, ha⟩ | ⟨a, ha⟩
  · have htu : IsConj t u := isConj_iff.mpr ⟨(a : G), ha⟩
    exact d.derived_t_not_isConj h hN hself t ht htZ ht2 hzt
      htlocal htcard htcenter (hconj.trans htu.symm)
  · have hvu : IsConj v u := isConj_iff.mpr ⟨(a : G), ha⟩
    exact d.derived_v_fusion h hself v hv hvZ hv2 hzv
      hvlocal hvcard hvcenter (hconj.trans hvu.symm)

end Stellmacher.Recognition
