module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.FirstFusion
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.SecondOrbits
public import Theory.GroupTheory.OuterGeneratingPair
public import Theory.GroupTheory.CyclicNormalOddQuotient

/-!
# The J₂ outer restriction

An automorphism preserves the word tests on the standard generating pair.
The first calculation conjugates its first generator image back to `a`.
The second calculation, inside the centralizer of `a`, conjugates its second
image to `b` or `b⁻¹`. After both inner adjustments the automorphism squares
to one, so the full outer quotient is a two-group. The required cyclic-normal
odd-quotient condition then transports along the actual model isomorphism.

The final theorems discharge both conjugacy calculations using the checked
first-generator fusion and second-generator centralizer orbits for the fixed
degree-100 carrier. The conditional reductions remain available separately.

Source: Aschbacher--Smith, combined 1 March 2004 manuscript, Theorem C on
printed p.33 and the proof of 1.3.4 on p.510; GLS3, Table 5.3g, records
Out(J₂) ≅ C₂. No lattice-model comparison or constructed automorphism subgroup
is used in place of the full automorphism group.
-/

public section
namespace CFSG.Quasithin.Chapter1.XiEmbedding.OuterModels.JankoTwo
open Sporadic.LeechRelated.J2 Sporadic.LeechRelated.J2.GeneratorPair
open Theory.GroupTheory

/-- The two finite pair calculations imply the required full outer two-group
bound. -/
theorem outer_isPGroup_two_of_pair_calculations
    (hfirst : ∀ x y : Carrier, PairProfile x y →
      ∃ g : Carrier, x = MulAut.conj g a)
    (hsecond : ∀ y : Carrier, PairProfile a y →
      ∃ c : Carrier, MulAut.conj c a = a ∧
        (y = MulAut.conj c b ∨ y = MulAut.conj c b⁻¹)) :
    IsPGroup 2 (MulAut.Outer Carrier) := by
  apply MulAut.outer_isPGroup_two_of_generating_pair a b closure_pair_eq_top
  intro f
  obtain ⟨g, hga⟩ := hfirst (f a) (f b) (pair_profile.map f)
  let k : MulAut Carrier := (MulAut.conj g)⁻¹ * f
  have hka : k a = a := by simp [k, MulAut.mul_apply, hga, mul_assoc]
  have hk : PairProfile a (k b) := by simpa only [hka] using pair_profile.map k
  obtain ⟨c, hca, hcb⟩ := hsecond (k b) hk
  have hf (x : Carrier) : f x = MulAut.conj g (k x) := by
    simp [k, MulAut.mul_apply, mul_assoc]
  refine ⟨g * c, ?_, ?_⟩
  · rw [hf a, hka, map_mul, MulAut.mul_apply, hca]
  · rcases hcb with hcb | hcb
    · left
      rw [hf b, hcb, map_mul, MulAut.mul_apply]
    · right
      rw [hf b, hcb, map_mul, MulAut.mul_apply]

/-- Transport of the conditional J₂ calculation through the actual equivalence
used by the classification catalogue. -/
theorem outer_cyclicNormalOddQuotient_of_pair_calculations
    (hfirst : ∀ x y : Carrier, PairProfile x y →
      ∃ g : Carrier, x = MulAut.conj g a)
    (hsecond : ∀ y : Carrier, PairProfile a y →
      ∃ c : Carrier, MulAut.conj c a = a ∧
        (y = MulAut.conj c b ∨ y = MulAut.conj c b⁻¹))
    {S : Type*} [Group S] (e : S ≃* Carrier) :
    HasCyclicNormalOddQuotient (MulAut.Outer S) := by
  have h := hasCyclicNormalOddQuotient_of_isPGroup_two
    (outer_isPGroup_two_of_pair_calculations hfirst hsecond)
  exact h.of_injective (MulAut.outerCongr e).toMonoidHom (MulAut.outerCongr e).injective

/-- The full outer automorphism group of the fixed ATLAS J₂ carrier is a
two-group, with both finite conjugacy calculations discharged. -/
theorem outer_isPGroup_two : IsPGroup 2 (MulAut.Outer Carrier) :=
  outer_isPGroup_two_of_pair_calculations
    first_generator_conjugate second_generator_orbits

/-- The J₂ outer restriction transported through the actual model isomorphism.
No additional model or automorphism hypotheses are required. -/
theorem outer_cyclicNormalOddQuotient
    {S : Type*} [Group S] (e : S ≃* Carrier) :
    HasCyclicNormalOddQuotient (MulAut.Outer S) := by
  have h := hasCyclicNormalOddQuotient_of_isPGroup_two outer_isPGroup_two
  exact h.of_injective (MulAut.outerCongr e).toMonoidHom (MulAut.outerCongr e).injective

end CFSG.Quasithin.Chapter1.XiEmbedding.OuterModels.JankoTwo
