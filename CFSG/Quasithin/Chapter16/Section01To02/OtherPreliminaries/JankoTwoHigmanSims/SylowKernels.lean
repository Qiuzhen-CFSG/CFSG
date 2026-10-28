module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.Conventions
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.J2Reduction
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.SylowKernels.J2Data
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.SylowKernels.HSTwoGroup
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.Parity
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizerIndex.GraphNormalizer

/-!
# Sylow-centralizing automorphisms of J₂ and HS

The concrete restriction kernels are inner. For J₂, every permutation
centralizing the seed two-subgroup is even, and the even half of the proved
full automorphism extension is the original carrier. For HS, the restriction
kernel in the graph group consists of two permutations in the carrier; every
abstract automorphism is covered by its permutation normalizer. The seed is
proved to be a two-group, so Sylow conjugacy applies to every Sylow subgroup.

These calculations establish innerness without any restriction on the order
of the centralizing automorphism. In particular they include the identity
and every higher-order two-element required by Aschbacher–Smith 16.1.6,
combined manuscript of 1 March 2004, printed p.1172.
-/

public section
namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.SylowKernels
open CFSG.Quasithin.SylowKernelCertificate

section J2
open Sporadic.LeechRelated.J2
open Sporadic.LeechRelated.J2.GeneratorPair
open Sporadic.LeechRelated.J2.ExceptionalParabolics
open scoped Pointwise

private theorem even_mem_generated (p : Extension) (hp : Equiv.Perm.sign p.val = 1) :
    p.val ∈ generated := by
  have hprod : p.val ∈ (generated : Set (Equiv.Perm (Fin 100))) *
      (Subgroup.zpowers involution : Set (Equiv.Perm (Fin 100))) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left generated (Subgroup.zpowers involution)
      (Subgroup.zpowers_le.mpr involution_mem_normalizer)]
    exact p.property
  obtain ⟨u, hu, v, hv, huv⟩ := hprod
  change u ∈ generated at hu
  change u * v = p.val at huv
  have ho : orderOf involution = 2 := orderOf_eq_prime
    (by simpa only [pow_two] using involution_mul_self)
    (fun h => involution_not_mem_generated (h ▸ generated.one_mem))
  have hf : IsOfFinOrder involution := isOfFinOrder_iff_pow_eq_one.mpr
    ⟨2, by decide, by simpa only [pow_two] using involution_mul_self⟩
  change v ∈ Subgroup.zpowers involution at hv
  rw [hf.mem_zpowers_iff_mem_range_orderOf, ho] at hv
  obtain ⟨i, hi, hiv⟩ := Finset.mem_image.mp hv
  have hib := Finset.mem_range.mp hi
  have hic : i = 0 ∨ i = 1 := by omega
  rcases hic with rfl | rfl
  · have hv1 : v = 1 := by simpa using hiv.symm
    rw [← huv, hv1, mul_one]
    exact hu
  · have hv1 : v = involution := by simpa using hiv.symm
    rw [← huv, hv1, map_mul, generated_le_sign_ker hu, involution_sign, one_mul] at hp
    exact False.elim ((by decide : (-1 : ℤˣ) ≠ 1) hp)

/-- Every automorphism fixing the concrete J₂ seed subgroup is inner. -/
theorem j2_fixing_seed_inner (r : MulAut Carrier)
    (hr : ∀ x ∈ Seed.s, r x = x) : ∃ g : Carrier, r = MulAut.conj g := by
  obtain ⟨p, rfl⟩ := extensionAction_surjective_of_pair_calculations
    first_generator_conjugate second_generator_orbits r
  have hc : ∀ i, Commute p.val (J2Data.gen i) := by
    intro i
    have hx := hr (Seed.sGenerator i) (Subgroup.subset_closure ⟨i, rfl⟩)
    have he := congrArg (fun x : Carrier => (x : Equiv.Perm (Fin 100))) hx
    change p.val * inclusion (Seed.sGenerator i) * p.val⁻¹ = inclusion (Seed.sGenerator i) at he
    rw [PairNormalizer.sGenerator_inclusion, ← J2Data.gen_eq] at he
    exact (mul_inv_eq_iff_eq_mul.mp he)
  have hmem := even_mem_generated p (J2Data.centralizer_sign p.val hc)
  refine ⟨⟨p.val, hmem⟩, ?_⟩
  rw [← extensionAction_inner]
  congr 1

/-- The concrete J₂ calculation applies to every Sylow subgroup and every automorphism. -/
theorem j2_fixing_sylow_inner (S : Sylow 2 Carrier) (r : MulAut Carrier)
    (hr : ∀ x ∈ S, r x = x) : ∃ g : Carrier, r = MulAut.conj g :=
  inner_of_fixing_twoSubgroup Seed.s
    (IsPGroup.of_card (n := 7) PairNormalizer.card_s) j2_fixing_seed_inner S r hr

/-- The full arbitrary-two-element contract of 16.1.6 for the exact J₂ carrier. -/
theorem j2 : HasInnerSylowCentralizingTwoAutomorphisms Carrier := by
  intro r _ S _ hS
  exact j2_fixing_sylow_inner S r hS

end J2

section HS
open Sporadic.LeechRelated.HS

/-- Every automorphism fixing the concrete HS seed subgroup is inner. -/
theorem hs_fixing_seed_inner (r : MulAut Carrier)
    (hr : ∀ x ∈ EvenLocalCandidates.subgroup, r x = x) :
    ∃ g : Carrier, r = MulAut.conj g := by
  obtain ⟨p, rfl⟩ := normalizer_surjective_of_pointStabilizer_map pointStabilizer_map r
  have hc : ∀ i, Commute p.val (HSData.gen i) := by
    intro i
    have hx := hr (EvenLocalCandidates.sylowGenerator i) (Subgroup.subset_closure ⟨i, rfl⟩)
    have he := congrArg (fun x : Carrier => (x : Equiv.Perm (Fin 100))) hx
    change p.val * (EvenLocalCandidates.sylowGenerator i : Equiv.Perm (Fin 100)) * p.val⁻¹ =
      (EvenLocalCandidates.sylowGenerator i : Equiv.Perm (Fin 100)) at he
    rw [← HSData.gen_eq] at he
    exact (mul_inv_eq_iff_eq_mul.mp he)
  have hmem := HSData.centralizer_mem p.val hc
    (NormalizerIndex.normalizer_le_graphGroup p.property)
  refine ⟨⟨p.val, hmem⟩, ?_⟩
  ext x
  rfl

/-- The concrete HS calculation applies to every Sylow subgroup and every automorphism. -/
theorem hs_fixing_sylow_inner (S : Sylow 2 Carrier) (r : MulAut Carrier)
    (hr : ∀ x ∈ S, r x = x) : ∃ g : Carrier, r = MulAut.conj g :=
  inner_of_fixing_twoSubgroup EvenLocalCandidates.subgroup HSTwoGroup.isPGroup
    hs_fixing_seed_inner S r hr

/-- The full arbitrary-two-element contract of 16.1.6 for the exact HS carrier. -/
theorem hs : HasInnerSylowCentralizingTwoAutomorphisms Carrier := by
  intro r _ S _ hS
  exact hs_fixing_sylow_inner S r hS

end HS
end CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.SylowKernels
