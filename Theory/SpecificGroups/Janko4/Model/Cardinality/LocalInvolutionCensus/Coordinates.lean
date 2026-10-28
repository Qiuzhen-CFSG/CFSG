module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.Base
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.LowerBound

set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency true

/-!
# Exhaustive max2 kernel coordinates from matching order bounds

The certified source subgroup has at least 21799895040 elements, its explicit
row quotient has at least 2661120 elements, and 8192 distinct binary word
products lie in the kernel. An upper bound on the local subgroup therefore
makes those kernel words exhaustive. Consequently equality of quotient images
reduces an arbitrary lift to one of these 8192 words times a chosen lift.

The argument uses the actual conjugation equivalence with `H`, the actual
matrix quotient homomorphism, and the kernel--image order formula. It needs
no assertion that `H` is the full centralizer, or that the row quotient is the
canonical column homology quotient. Source words and certificates are in
`TwoCoreCentralizer.Generation.LowerBound`; the census motivation is
Aschbacher--Smith, `refs/quasithin.pdf`, printed pp.64--65, A.6.1--4.
-/

@[expose] public section
namespace Janko4.Cardinality.LocalInvolutionCensus

open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound

theorem card_H_ge : 21799895040 ≤ Nat.card H := by
  rw [← card_sourceSubgroup_eq_localSubgroup]
  exact sourceSubgroup_card_ge

theorem card_H_eq (hH : Nat.card H ≤ 21799895040) : Nat.card H = 21799895040 :=
  le_antisymm hH card_H_ge

namespace Coordinates

theorem quotientMap_seed : quotientMap sourceSeed = 1 :=
  map_sourceSeed_eq_one quotientMap quotientMap_sourceX quotientMap_sourceY

theorem source_generators_generate : Subgroup.closure {sourceX, sourceY} = ⊤ := by
  apply Subgroup.map_injective sourceSubgroup.subtype_injective
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
    Set.image_pair]
  rfl

/-- The certified homomorphism has exactly the two-generator matrix image. -/
theorem quotientMap_range : quotientMap.range = quotientSubgroup := by
  rw [MonoidHom.range_eq_map, ← source_generators_generate, MonoidHom.map_closure,
    Set.image_pair, quotientMap_sourceX, quotientMap_sourceY]
  rfl

@[simp] theorem sourceEquiv_X : sourceSubgroupEquivLocal sourceX = subgroupX := by
  apply eH_injective
  rw [eH_sourceSubgroupEquivLocal]
  rfl

@[simp] theorem sourceEquiv_Y : sourceSubgroupEquivLocal sourceY = subgroupY := by
  apply eH_injective
  rw [eH_sourceSubgroupEquivLocal]
  rfl

@[simp] theorem sourceEquiv_seed : sourceSubgroupEquivLocal sourceSeed = localSeed := by
  simp only [sourceSeed, map_pow, map_mul, sourceEquiv_X, sourceEquiv_Y, localSeed]

/-- The square of the original seed transports to the distinguished involution. -/
@[simp] theorem sourceEquiv_seed_sq : sourceSubgroupEquivLocal (sourceSeed ^ 2) = zH := by
  rw [map_pow, sourceEquiv_seed, localSeed_sq]

/-- The certified binary words, now regarded as elements of the actual kernel. -/
def kernelElement (i : Fin 8192) : quotientMap.ker :=
  ⟨kernelProduct i, map_kernelProduct_eq_one quotientMap quotientMap_seed i⟩

attribute [local irreducible] kernelProduct

theorem kernelElement_injective : Function.Injective kernelElement := by
  intro i j hij
  exact kernelProduct_injective (congrArg (fun u : quotientMap.ker => u.val) hij)

theorem quotientMap_kernel_card_le (hH : Nat.card H ≤ 21799895040) :
    Nat.card quotientMap.ker ≤ 8192 := by
  have himage : 2661120 ≤ Nat.card quotientMap.range :=
    quotientSubgroup_card_ge.trans (Subgroup.card_le_of_le
      (quotientSubgroup_le_range quotientMap quotientMap_sourceX quotientMap_sourceY))
  have hprod : Nat.card quotientMap.ker * Nat.card quotientMap.range =
      Nat.card sourceSubgroup := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  have hupper : Nat.card sourceSubgroup ≤ 21799895040 :=
    card_sourceSubgroup_eq_localSubgroup.le.trans hH
  have hle := (Nat.mul_le_mul_left (Nat.card quotientMap.ker) himage).trans
    (hprod.le.trans hupper)
  exact Nat.le_of_mul_le_mul_right hle (by decide : 0 < 2661120)

/-- The lower-bound witnesses enumerate the whole kernel under the permitted upper bound. -/
theorem kernelElement_bijective (hH : Nat.card H ≤ 21799895040) :
    Function.Bijective kernelElement :=
  kernelElement_injective.bijective_of_nat_card_le
    (by simpa only [Nat.card_fin] using quotientMap_kernel_card_le hH)

theorem quotientMap_kernel_card (hH : Nat.card H ≤ 21799895040) :
    Nat.card quotientMap.ker = 8192 := by
  apply le_antisymm (quotientMap_kernel_card_le hH)
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective
    kernelElement kernelElement_injective

theorem quotientSubgroup_card (hH : Nat.card H ≤ 21799895040) :
    Nat.card quotientSubgroup = 2661120 := by
  have he := quotientMap.ker.card_mul_index
  rw [quotientMap_kernel_card hH, Subgroup.index_ker, quotientMap_range,
    card_sourceSubgroup_eq_localSubgroup, card_H_eq hH] at he
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 8192) he

/-- Every source lift is a prescribed kernel word times any other lift. -/
theorem source_fiber (hH : Nat.card H ≤ 21799895040)
    (u v : sourceSubgroup) (hq : quotientMap u = quotientMap v) :
    ∃ i : Fin 8192, u = kernelProduct i * v := by
  have hk : u * v⁻¹ ∈ quotientMap.ker := by
    change quotientMap (u * v⁻¹) = 1
    rw [map_mul, map_inv, hq, mul_inv_cancel]
  obtain ⟨i, hi⟩ := (kernelElement_bijective hH).surjective ⟨u * v⁻¹, hk⟩
  have he : kernelProduct i = u * v⁻¹ := congrArg Subtype.val hi
  exact ⟨i, by rw [he, inv_mul_cancel_right]⟩

/-- The same actual row quotient, transported to the published local subgroup. -/
noncomputable def localQuotientMap : H →* QuotientMatrixˣ :=
  quotientMap.comp sourceSubgroupEquivLocal.symm.toMonoidHom

@[simp] theorem localQuotientMap_sourceEquiv (u : sourceSubgroup) :
    localQuotientMap (sourceSubgroupEquivLocal u) = quotientMap u := by
  change quotientMap (sourceSubgroupEquivLocal.symm (sourceSubgroupEquivLocal u)) = _
  rw [sourceSubgroupEquivLocal.symm_apply_apply]

theorem localQuotientMap_range : localQuotientMap.range = quotientSubgroup := by
  apply le_antisymm
  · rintro v ⟨u, rfl⟩
    rw [← quotientMap_range]
    exact ⟨sourceSubgroupEquivLocal.symm u, rfl⟩
  · intro v hv
    rw [← quotientMap_range] at hv
    obtain ⟨u, rfl⟩ := hv
    exact ⟨sourceSubgroupEquivLocal u, localQuotientMap_sourceEquiv u⟩

@[simp] theorem localQuotientMap_zH : localQuotientMap zH = 1 := by
  rw [← sourceEquiv_seed_sq, localQuotientMap_sourceEquiv, map_pow,
    quotientMap_seed, one_pow]

/-- The prescribed binary products transported by the certified conjugation. -/
noncomputable def localKernelProduct (i : Fin 8192) : H :=
  sourceSubgroupEquivLocal (kernelProduct i)

/-- Exhaustive lift coordinates on the literal subgroup used in the census. -/
theorem local_fiber (hH : Nat.card H ≤ 21799895040)
    (u v : H) (hq : localQuotientMap u = localQuotientMap v) :
    ∃ i : Fin 8192, u = localKernelProduct i * v := by
  obtain ⟨i, hi⟩ := source_fiber hH (sourceSubgroupEquivLocal.symm u)
    (sourceSubgroupEquivLocal.symm v) hq
  refine ⟨i, ?_⟩
  have he := congrArg sourceSubgroupEquivLocal hi
  simpa only [map_mul, MulEquiv.apply_symm_apply, localKernelProduct] using he

end Coordinates
end Janko4.Cardinality.LocalInvolutionCensus
