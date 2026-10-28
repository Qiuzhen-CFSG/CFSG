module

public import Theory.Representation.BinaryQuadraticPair.Displacement
public import Theory.Representation.BinaryConjugationSection.QuadraticPair

/-!
# Literal displacement preimages in a natural binary section

Coordinates preserve subgroup joins with the actual quotient kernel.
Commutators therefore give the same preimages as linear displacement.
For two complementary natural factors, the translated-subspace criterion
also holds for zero multiplicity; no nontrivial-section premise is needed.
Source: Aschbacher--Smith 13.7.10(4), printed p.942.
-/

public section

open Subgroup
open scoped commutatorElement
namespace Representation.BinaryConjugationSection
variable {G:Type*} [Group G] {H S E:Subgroup G}
  {W:Type*} [AddCommGroup W] [Module (ZMod 2) W]
  {ρ:Representation (ZMod 2) H W} (c:BinaryConjugationSection H S E ρ)

theorem coordinates_mem_imageSpace_iff (K:Subgroup G) (hK:K≤S) (z:S) :
    (c.coordinates z).toAdd∈c.imageSpace K ↔ (z:G)∈K⊔E := by
  change z∈((K.subgroupOf S).map c.coordinates).comap c.coordinates ↔ _
  rw [comap_map_eq,c.kernel_eq,←subgroupOf_sup hK c.kernel_le]
  rfl

theorem displacement_mem_imageSpace_iff (K:Subgroup G) (hK:K≤S) (u:H) (z:S) :
    (ρ u-1) (c.coordinates z).toAdd∈c.imageSpace K ↔ ⁅(u:G),(z:G)⁆∈K⊔E := by
  let z':S:=⟨(u:G)*(z:G)*(u:G)⁻¹,
    (mem_normalizer_iff.mp (c.normalized u.property) z).mp z.property⟩
  let w:S:=z'*z⁻¹
  have he:(c.coordinates w).toAdd=(ρ u-1) (c.coordinates z).toAdd := by
    rw [map_mul,map_inv]
    rw [toAdd_mul,toAdd_inv,←sub_eq_add_neg]
    rw [c.equivariant]
    rfl
  rw [←he,c.coordinates_mem_imageSpace_iff K hK]
  rfl
end Representation.BinaryConjugationSection
open InvertedCubicTensor BinaryPermutation
open scoped TensorProduct
namespace Representation.BinaryQuadraticPair
variable {M V:Type*} [AddCommGroup M] [Module (ZMod 2) M]
  [AddCommGroup V] [Module (ZMod 2) V]
theorem translated_subspace_preimage_of_compl
    (σ:Representation (ZMod 2) S₃ V)
    (e:M ⊗[ZMod 2] BinaryPermutation.core (Fin 3) ≃ₗ[ZMod 2] V)
    (he:∀a z,e ((Representation.tprod (Representation.trivial (ZMod 2) S₃ M)
      (coreRepresentation (Fin 3))) a z)=σ a (e z))
    (t g:S₃) (ht:t*t=1) (ht1:t≠1)
    (W U:Submodule (ZMod 2) V)
    (hk:LinearMap.ker (σ t-1)=W) (hr:LinearMap.range (σ t-1)=W)
    (hc:IsCompl W (W.map (σ g)))
    (x:V) (hx:x∈W.map (σ g)) :
    (σ t-1) x∈U ↔ x∈U.map (σ g) := by
  by_cases hx0:x=0
  · subst x
    simp only [map_zero,Submodule.zero_mem]
  have hWne:W≠⊥ := by
    intro hW
    rw [hW,Submodule.map_bot,Submodule.mem_bot] at hx
    exact hx0 hx
  have hfix (v:V) (hv:v∈W) : σ t v=v := by
    have hmem:v∈LinearMap.ker (σ t-1):=hk.symm ▸ hv
    exact sub_eq_zero.mp hmem
  have hWt:W.map (σ t)=W := by
    apply le_antisymm
    · rintro _ ⟨v,hv,rfl⟩
      rwa [hfix v hv]
    · intro v hv
      exact ⟨v,hv,hfix v hv⟩
  have hg1:g≠1 := by
    intro heq
    rw [heq,map_one,Module.End.one_eq_id,Submodule.map_id] at hc
    exact hWne (by simpa only [inf_idem] using hc.inf_eq_bot)
  have hgt:g≠t := by
    intro heq
    rw [heq,hWt] at hc
    exact hWne (by simpa only [inf_idem] using hc.inf_eq_bot)
  exact translated_subspace_preimage_of_tensor σ e he t g ht ht1 hg1 hgt W U hr x hx
end Representation.BinaryQuadraticPair

open Subgroup InvertedCubicTensor
open scoped TensorProduct commutatorElement
namespace Representation.BinaryConjugationSection
variable {G:Type*} [Group G] {I S E:Subgroup G}
  {M V:Type*} [AddCommGroup M] [Module (ZMod 2) M]
  [AddCommGroup V] [Module (ZMod 2) V]
theorem natural_commutator_preimage
    (σ:Representation (ZMod 2) S₃ V) (π:I→*S₃)
    (c:BinaryConjugationSection I S E (σ.comp π))
    (j:M ⊗[ZMod 2] BinaryPermutation.core (Fin 3) ≃ₗ[ZMod 2] V)
    (hj:∀a z,j ((Representation.tprod (Representation.trivial (ZMod 2) S₃ M)
      (BinaryPermutation.coreRepresentation (Fin 3))) a z)=σ a (j z))
    (A W U:Subgroup G) (hAI:A≤I) (hW:W≤S) (hU:U≤S)
    (u x:I) (hu:(u:G)∈A) (hu1:π u≠1) (hu2:π u*π u=1)
    (hcard:Nat.card ((A.subgroupOf I).map π)=2)
    (hk:LinearMap.ker (σ (π u)-1)=c.imageSpace W)
    (hr:LinearMap.range (σ (π u)-1)=c.imageSpace W)
    (hc:IsCompl (c.imageSpace W) (c.imageSpace (W.conjBy (x:G))))
    (z:S) (hz:(z:G)∈W.conjBy (x:G)) :
    (∀a∈A,⁅a,(z:G)⁆∈U⊔E) ↔ (z:G)∈U.conjBy (x:G)⊔E := by
  have hUx:U.conjBy (x:G)≤S := by
    rintro _ ⟨a,ha,rfl⟩
    exact (mem_normalizer_iff.mp (c.normalized x.property) a).mp (hU ha)
  have hWx:c.imageSpace (W.conjBy (x:G))=(c.imageSpace W).map (σ (π x)):=c.imageSpace_conjBy W hW x
  have hUx':c.imageSpace (U.conjBy (x:G))=(c.imageSpace U).map (σ (π x)):=c.imageSpace_conjBy U hU x
  have hh:=BinaryQuadraticPair.translated_subspace_preimage_of_compl σ j hj
    (π u) (π x) hu2 hu1 (c.imageSpace W) (c.imageSpace U) hk hr
    (hWx ▸ hc) (c.coordinates z).toAdd
    (by rw [←hWx];exact (c.mem_imageSpace_iff _ _).mpr ⟨z,hz,rfl⟩)
  rw [←hUx',c.coordinates_mem_imageSpace_iff _ hUx z] at hh
  have hd (a:I) : (σ (π a)-1) (c.coordinates z).toAdd∈c.imageSpace U ↔
      ⁅(a:G),(z:G)⁆∈U⊔E := c.displacement_mem_imageSpace_iff U hU a z
  constructor
  · intro h
    exact hh.mp ((hd u).mpr (h u hu))
  · intro hzU a ha
    let aI:I:=⟨a,hAI ha⟩
    apply (hd aI).mp
    by_cases ha1:π aI=1
    · rw [ha1,map_one,sub_self]
      exact (c.imageSpace U).zero_mem
    · obtain ⟨y,_,hall⟩ := (Nat.card_eq_two_iff' (1:((A.subgroupOf I).map π))).mp hcard
      have hu':(⟨π u,mem_map_of_mem π hu⟩:((A.subgroupOf I).map π))≠1 := by
        intro he;exact hu1 (congrArg Subtype.val he)
      have ha':(⟨π aI,mem_map_of_mem π ha⟩:((A.subgroupOf I).map π))≠1 := by
        intro he;exact ha1 (congrArg Subtype.val he)
      have heu:π aI=π u:=congrArg Subtype.val ((hall _ ha').trans (hall _ hu').symm)
      rw [heu]
      exact hh.mpr hzU
end Representation.BinaryConjugationSection

open Subgroup
namespace Representation.BinaryConjugationSection
variable {G:Type*} [Group G] {H S E:Subgroup G}
  {W:Type*} [AddCommGroup W] [Module (ZMod 2) W]
  {ρ:Representation (ZMod 2) H W} (c:BinaryConjugationSection H S E ρ)
include c
theorem normalizes_join_kernel (U:Subgroup G) (hU:U≤S) :
    S≤normalizer ((U⊔E:Subgroup G):Set G) := by
  have hn:((U⊔E).subgroupOf S).Normal := by
    rw [subgroupOf_sup hU c.kernel_le,←c.kernel_eq,←comap_map_eq]
    infer_instance
  exact (normal_subgroupOf_iff_le_normalizer (sup_le hU c.kernel_le)).mp hn
end Representation.BinaryConjugationSection
