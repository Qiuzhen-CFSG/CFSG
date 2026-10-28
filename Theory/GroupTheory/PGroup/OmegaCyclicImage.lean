module

public import Theory.GroupTheory.PGroup.Omega
public import Theory.GroupTheory.PGroup.CyclicInvolution

/-!
# The cyclic image of an omega subgroup

If a homomorphism to a cyclic group carries an involution to an involution,
the image of the first two-omega subgroup is precisely the subgroup generated
by that image. Every involution in a cyclic group is the unique involution,
so this follows by applying the homomorphism to the defining generators.
If the chosen involution is central in the domain, the omega subgroup itself
is its join with the image of the omega of the kernel: multiply every generator
outside the kernel by the chosen involution to obtain a kernel generator.
-/

open Subgroup

namespace MonoidHom

/-- A surviving involution generates the cyclic image of the first two-omega. -/
public theorem map_omega₁_eq_zpowers_of_isCyclic
    {G K : Type*} [Group G] [Group K] [Finite K] [IsCyclic K]
    (f : G →* K) (y : G) (hy : y ^ 2 = 1) (hfy : orderOf (f y) = 2) :
    (omega₁ G (p := 2)).map f = zpowers (f y) := by
  apply le_antisymm
  · apply map_le_iff_le_comap.mpr
    refine (closure_le _).mpr ?_
    intro a ha
    have ha2 : a ^ 2 = 1 := by simpa only [Set.mem_ofPred_eq, pow_one] using ha
    change f a ∈ zpowers (f y)
    by_cases hfa : f a = 1
    · exact hfa ▸ (zpowers (f y)).one_mem
    · have hfa2 : orderOf (f a) = 2 := orderOf_eq_prime
        (by rw [← map_pow, ha2, map_one]) hfa
      rw [IsCyclic.eq_of_orderOf_eq_two hfa2 hfy]
      exact mem_zpowers (f y)
  · apply zpowers_le.mpr
    exact mem_map_of_mem f (subset_closure (by
      simpa only [Set.mem_ofPred_eq, pow_one] using hy))

end MonoidHom

namespace Subgroup

/-- A central involution surviving in a cyclic quotient splits off the first
two-omega: its other generators are involutions in the kernel. -/
public theorem omega₁_eq_sup_kernel_omega_of_central_involution
    {G K : Type*} [Group G] [Group K] [Finite K] [IsCyclic K]
    (f : G →* K) (y : G) (hy : y ^ 2 = 1)
    (hycentral : ∀ a : G, Commute a y) (hfy : orderOf (f y) = 2) :
    omega₁ G (p := 2) = zpowers y ⊔ (omega₁ f.ker (p := 2)).map f.ker.subtype := by
  let W := (omega₁ f.ker (p := 2)).map f.ker.subtype
  have hyomega : y ∈ omega₁ G (p := 2) := subset_closure (by
    simpa only [Set.mem_ofPred_eq, pow_one] using hy)
  have hW : W ≤ omega₁ G (p := 2) := by
    apply map_le_iff_le_comap.mpr
    refine (closure_le _).mpr ?_
    intro a ha
    apply subset_closure
    change (f.ker.subtype a) ^ (2 ^ 1) = 1
    simpa only [map_pow, map_one] using congrArg f.ker.subtype ha
  apply le_antisymm
  · refine (closure_le _).mpr ?_
    intro a ha
    change a ∈ zpowers y ⊔ W
    have ha2 : a ^ 2 = 1 := by simpa only [Set.mem_ofPred_eq, pow_one] using ha
    have hmem (b : G) (hb : b ^ 2 = 1) (hbf : f b = 1) : b ∈ W := by
      let bK : f.ker := ⟨b, hbf⟩
      exact mem_map_of_mem f.ker.subtype (show bK ∈ omega₁ f.ker (p := 2) from
        subset_closure (by
          change bK ^ (2 ^ 1) = 1
          apply Subtype.ext
          change b ^ 2 = 1
          exact hb))
    by_cases hfa : f a = 1
    · exact (le_sup_right : W ≤ zpowers y ⊔ W) (hmem a ha2 hfa)
    · have hfa2 : orderOf (f a) = 2 := orderOf_eq_prime
        (by rw [← map_pow, ha2, map_one]) hfa
      have hfaeq : f a = f y := IsCyclic.eq_of_orderOf_eq_two hfa2 hfy
      have hay2 : (a * y) ^ 2 = 1 := by rw [(hycentral a).mul_pow, ha2, hy, one_mul]
      have hayf : f (a * y) = 1 := by
        rw [map_mul, hfaeq, ← pow_two, ← map_pow, hy, map_one]
      have hh := (zpowers y ⊔ W).mul_mem
        ((le_sup_right : W ≤ zpowers y ⊔ W) (hmem (a * y) hay2 hayf))
        ((le_sup_left : zpowers y ≤ zpowers y ⊔ W) (mem_zpowers y))
      simpa only [mul_assoc, ← pow_two, hy, mul_one] using hh
  · exact sup_le (zpowers_le.mpr hyomega) hW

end Subgroup
