module
public import Theory.GroupTheory.PointCentralizerResidualCore
public import Theory.SpecificGroups.AlternatingSix.NaturalSplit.Restriction
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalTransport

/-!
# Aligning the marked point in a natural split A₆ block

Even permutations act transitively on the fifteen nonzero natural vectors.
Composing a marked split isomorphism with a diagonal lift therefore carries
any chosen nonidentity translation to the distinguished duad 45, preserving
the translation subgroup. Intrinsic point-centralizer residual cores are
transported by this same isomorphism.

Source: Aschbacher–Smith 14.3.19(10), quaternion subgroup marking.
-/

@[expose] public section
namespace BinaryPermutation.SixNaturalSplit
open Subgroup SemidirectProduct
open Theory.SpecificGroups.SymmetricSix.BinaryFlags

public theorem exists_point_aligned_equiv
    {K:Type*} [Group K] (A:Subgroup K) (e:K≃*Model)
    (hA:A.map e.toMonoidHom=translations) (z:K) (hzA:z∈A) (hz:z≠1) :
    ∃ f:K≃*Model, A.map f.toMonoidHom=translations ∧
      f z=inl (Multiplicative.ofAdd (NaturalGeometry.pairVector 4 5)) := by
  have hm:e z∈translations := hA ▸ mem_map_of_mem e.toMonoidHom hzA
  obtain ⟨v,hv⟩ := hm
  have hv0:v.toAdd≠0 := by
    intro h0
    have hv1:v=1 := Multiplicative.toAdd.injective h0
    have he:e z=e 1 := by rw [←hv,hv1,map_one,map_one]
    exact hz (e.injective he)
  obtain ⟨s,hs⟩ := NaturalTransport.exists_even_image v.toAdd hv0
  let f:K≃*Model := e.trans (diagonal s.val).symm
  refine ⟨f,?_,?_⟩
  · change A.map ((diagonal s.val).symm.toMonoidHom.comp e.toMonoidHom)=translations
    rw [←map_map,hA]
    exact characteristic_iff_map_eq.mp translations_characteristic _
  · change (diagonal s.val).symm (e z)=_
    apply (diagonal s.val).injective
    rw [MulEquiv.apply_symm_apply]
    rw [←hv]
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      exact hs.symm
    · change (1:Actor)=MulAut.conjNormal s.val 1
      exact (map_one _).symm

public theorem exists_point_core_aligned_equiv
    {K:Type*} [Group K] [Finite K] (A U:Subgroup K) (e:K≃*Model)
    (hA:A.map e.toMonoidHom=translations) (z:K) (hzA:z∈A) (hz:z≠1)
    (hU:U=pointCentralizerTwoResidualCore z) :
    ∃ f:K≃*Model, A.map f.toMonoidHom=translations ∧
      f z=inl (Multiplicative.ofAdd (NaturalGeometry.pairVector 4 5)) ∧
      U.map f.toMonoidHom=pointCentralizerTwoResidualCore
        (inl (Multiplicative.ofAdd (NaturalGeometry.pairVector 4 5)):Model) := by
  obtain ⟨f,hf,hfz⟩ := exists_point_aligned_equiv A e hA z hzA hz
  refine ⟨f,hf,hfz,?_⟩
  rw [hU,map_pointCentralizerTwoResidualCore,hfz]

end BinaryPermutation.SixNaturalSplit
