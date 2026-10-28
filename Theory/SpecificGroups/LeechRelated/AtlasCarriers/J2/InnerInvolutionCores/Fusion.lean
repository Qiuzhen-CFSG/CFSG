module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.OuterTwoGroup

/-!
# Exhaustive inner-involution representatives for the degree-100 J₂ carrier

The checked 1920-word centralizer enumeration and odd-index Sylow argument
cover every involution by the actual words `a` and `t = (abab⁻¹)⁶`.
Faithfulness of inner conjugation lifts an inner involutory automorphism to
an involution in the carrier. Conjugation then identifies its whole fixed
subgroup with one of the two representative centralizers.

Adapted from the intrinsic proofs in the preserved module
`CFSG/Quasithin/Chapter16/Section01To02/OtherPreliminaries/
JankoTwoHigmanSims/J2Reduction.lean`, without importing chapter hypotheses.
Source: GLS3 Table 5.3g, classes 2A and 2B, and the retained ATLAS
J2G1-p100B0 certificates. This supplies the exhaustive coverage required by
the fixed-residual calculation on Aschbacher--Smith printed p.1137.
-/

public section
namespace Sporadic.LeechRelated.J2.InnerInvolutionCores
open GeneratorPair ExceptionalParabolics

/-- Conjugation faithfully represents the actual carrier. -/
private theorem fusion_conj_injective : Function.Injective (MulAut.conj : Carrier →* MulAut Carrier) := by
  intro x y h
  have hxy : intoExtension x = intoExtension y := extensionAction_injective (by
    simpa only [extensionAction_inner] using h)
  exact (Subgroup.inclusion_injective (show generated ≤ extension from le_sup_left)) hxy

/-- Every carrier involution is conjugate to one of the two checked representatives. -/
theorem involution_fusion (x : Carrier) (hx : orderOf x = 2) :
    IsConj a x ∨ IsConj FirstFusion.t x := by
  apply FirstFusion.involution_fusion_of_local ?_ (by simpa [hx] using pow_orderOf_eq_one x)
    (by intro h; simp [h] at hx)
  intro z hz hn
  obtain ⟨i, hi⟩ := FirstFusion.centralizerElement_cover z z.property
  rw [hi] at hz hn ⊢
  exact FirstFusion.centralizerElement_involution_fusion i hz hn

/-- Exhaustive inner-automorphism coverage, preserving the actual conjugating element. -/
theorem inner_involution_representatives (r : MulAut Carrier) (hr : orderOf r = 2)
    (hi : ∃ g : Carrier, r = MulAut.conj g) :
    (∃ g : Carrier, r = MulAut.congr (MulAut.conj g) (MulAut.conj a)) ∨
    (∃ g : Carrier, r = MulAut.congr (MulAut.conj g) (MulAut.conj FirstFusion.t)) := by
  obtain ⟨x, rfl⟩ := hi
  have hx : orderOf x = 2 := (orderOf_injective MulAut.conj fusion_conj_injective x).symm.trans hr
  rcases involution_fusion x hx with ha | ht
  · obtain ⟨g, hg⟩ := isConj_iff.mp ha
    exact Or.inl ⟨g, by rw [MulAut.congr_conj]; exact congrArg MulAut.conj hg.symm⟩
  · obtain ⟨g, hg⟩ := isConj_iff.mp ht
    exact Or.inr ⟨g, by rw [MulAut.congr_conj]; exact congrArg MulAut.conj hg.symm⟩

/-- The complete fixed subgroup is one of the two representative centralizers. -/
theorem inner_fixed_representatives (r : MulAut Carrier) (hr : orderOf r = 2)
    (hi : ∃ g : Carrier, r = MulAut.conj g) :
    Nonempty (r.fixedSubgroup ≃* Subgroup.centralizer ({a} : Set Carrier)) ∨
    Nonempty (r.fixedSubgroup ≃* Subgroup.centralizer ({FirstFusion.t} : Set Carrier)) := by
  rcases inner_involution_representatives r hr hi with ⟨g, rfl⟩ | ⟨g, rfl⟩
  · exact Or.inl ⟨(MulAut.fixedSubgroupCongr (MulAut.conj g) (MulAut.conj a)).symm.trans
      (MulEquiv.subgroupCongr (MulAut.fixedSubgroup_conj a))⟩
  · exact Or.inr ⟨(MulAut.fixedSubgroupCongr (MulAut.conj g) (MulAut.conj FirstFusion.t)).symm.trans
      (MulEquiv.subgroupCongr (MulAut.fixedSubgroup_conj FirstFusion.t))⟩

end Sporadic.LeechRelated.J2.InnerInvolutionCores
