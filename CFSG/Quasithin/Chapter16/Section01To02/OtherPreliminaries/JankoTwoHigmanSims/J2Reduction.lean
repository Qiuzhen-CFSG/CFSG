module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.Conventions
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.Automorphisms
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.FirstFusion
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.SecondOrbits
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# Reducing J₂ involutory automorphisms to the concrete permutation carrier

The checked centralizer enumeration and Sylow fusion cover both inner
involution classes. Faithfulness of the permutation-normalizer action makes
conjugation injective, so an inner automorphism of order two comes from an
actual involution. Transport then identifies its entire fixed subgroup with
one of the two representative centralizers.

The independent checked standard-pair calculations also discharge the
surjectivity premise for the concrete extension, giving an actual equivalence
with the full automorphism group. No source centralizer shape is inferred
merely from the outer-group bound.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 16.1.5(8),
printed p.1172; the retained ATLAS J2G1-p100B0 certificates in the imported
model modules. The representative group structures are separate obligations.
-/

public section
namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.J2Reduction

open Sporadic.LeechRelated.J2
open Sporadic.LeechRelated.J2.GeneratorPair
open Sporadic.LeechRelated.J2.ExceptionalParabolics

/-- Conjugation faithfully represents the actual carrier. -/
theorem conj_injective : Function.Injective (MulAut.conj : Carrier →* MulAut Carrier) := by
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
  have hx : orderOf x = 2 := (orderOf_injective MulAut.conj conj_injective x).symm.trans hr
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

/-- The concrete permutation extension is the full automorphism group. -/
noncomputable def fullAutomorphismEquiv : Extension ≃* MulAut Carrier :=
  extensionEquivAut_of_pair_calculations first_generator_conjugate second_generator_orbits

end CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.J2Reduction
