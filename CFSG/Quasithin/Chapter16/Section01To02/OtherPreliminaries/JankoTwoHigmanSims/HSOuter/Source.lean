module
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSOuter
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSOuter.PermutationFusion
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSOuter.SymmetricCentralizer
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSOuter.ElementaryCentralizer

/-!
# The complete HS outer involution source

The actual permutation normalizer realizes every automorphism. Fusion reduces
outer involutions to the elementary and symmetric representatives. The former
has a checked self-centralizing normal two-kernel and the latter is equivalent
to S₈. Transport gives both the full fixed-group alternatives and the A₈
component conclusion. Inner involutions use the complete HSInner table.

Source: Aschbacher–Smith 16.1.5(10), 16.1.7(h), printed pp.1172–1173.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims
namespace HSOuter
open Sporadic.LeechRelated.HS

private noncomputable def fixedEquivOfNormalizerConj
    (n k g : PermutationNormalizer) (hn : n = g * k * g⁻¹) :
    (generated.normalizerMonoidHom n).fixedSubgroup ≃* permutationCentralizer k.val := by
  let f := generated.normalizerMonoidHom
  have he : f n = MulAut.congr (f g) (f k) := by
    change f n = f g * f k * (f g)⁻¹
    rw [hn,map_mul,map_mul,map_inv]
  exact ((MulEquiv.subgroupCongr (congrArg MulAut.fixedSubgroup he)).trans
    (MulAut.fixedSubgroupCongr (f g) (f k)).symm).trans
      (MulEquiv.subgroupCongr (fixedSubgroup_eq_permutationCentralizer k))

/-- Full outer fixed-group alternatives, including the checked kernel action.
The actual permutation lift, fusion and both representative calculations
are instantiated; no table or action premise remains. -/
theorem outer_fixed_source (r : MulAut Carrier) (hr : orderOf r = 2)
    (ho : ¬ ∃ g : Carrier, r = MulAut.conj g) :
    Nonempty (r.fixedSubgroup ≃* S8) ∨
      IsHSElementaryExtension r.fixedSubgroup ∧
        HasSelfCentralizingNormalTwoSubgroup r.fixedSubgroup := by
  obtain ⟨n,hn,hno,hout⟩ := outer_involution_lift r hr ho
  rcases outer_involution_permutation_fusion n hno hout with ⟨g,hg⟩ | ⟨g,hg⟩
  · let e := fixedEquivOfNormalizerConj n elementaryNormalizer g (Subtype.ext hg)
    have he : (generated.normalizerMonoidHom n).fixedSubgroup ≃*
        permutationCentralizer elementaryPermutation := e
    rw [hn] at he
    exact Or.inr ⟨elementaryExtension_of_equiv he.symm elementaryCentralizer_isExtension,
      selfCentralizingTwoSubgroup_of_equiv he.symm elementaryCentralizer_hasSelfCentralizingNormalTwoSubgroup⟩
  · let e := fixedEquivOfNormalizerConj n symmetricNormalizer g (Subtype.ext hg)
    have he : (generated.normalizerMonoidHom n).fixedSubgroup ≃*
        permutationCentralizer symmetricPermutation := e
    rw [hn] at he
    exact Or.inl ⟨he.trans symmetricCentralizerEquiv⟩

/-- Every component of an outer involution fixed group is the actual A₈
model. The elementary row is excluded by its proved self-centralizing kernel. -/
theorem outer_component_equiv (r : MulAut Carrier) (hr : orderOf r = 2)
    (ho : ¬ ∃ g : Carrier, r = MulAut.conj g)
    (D : Subgroup r.fixedSubgroup) (hD : IsComponent r.fixedSubgroup D) :
    Nonempty (D ≃* A8) := by
  rcases outer_fixed_source r hr ho with he | h
  · obtain ⟨e⟩ := he
    exact component_equiv_alternating e D hD
  · exact (h.2.not_isComponent D hD).elim
end HSOuter

/-- The complete HS involution alternative for its actual automorphism group. -/
theorem source_hs_involution_alternative
    [IsSimpleGroup Sporadic.LeechRelated.HS.Carrier]
    [Group.IsPerfect Sporadic.LeechRelated.HS.Carrier]
    (r : MulAut Sporadic.LeechRelated.HS.Carrier) (hr : orderOf r = 2) :
    HSInvolutionAlternative r := by
  by_cases hi : ∃ g : Sporadic.LeechRelated.HS.Carrier, r = MulAut.conj g
  · exact HSInner.inner_alternative r hr hi
  · refine Or.inr ⟨hi,?_⟩
    exact (HSOuter.outer_fixed_source r hr hi).imp id And.left
end CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims
