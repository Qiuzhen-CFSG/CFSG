module
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Trivial action on a normalized quotient of order two

If F normalizes subgroups N≤K and N has relative index two in K, then
[K,F] lies in N. F need not lie in K, and no ambient normality or finiteness
assumption is required.

The index-two coset criterion proves this directly: k and its conjugated
inverse have the same membership in N, so their product [k,f] lies in N.
This supplies the trivial action on each seed/I in the source-(16)
neighborhood argument of Stellmacher (10.1), printed p.64, while remaining
independent of that graph-theoretic application.
-/

namespace Subgroup
open scoped commutatorElement

public theorem commutator_le_of_normalized_index_two
    {G : Type*} [Group G] (K N F : Subgroup G)
    (_hNK : N ≤ K) (hindex : N.relIndex K = 2)
    (hFK : F ≤ normalizer (K : Set G))
    (hFN : F ≤ normalizer (N : Set G)) : ⁅K,F⁆ ≤ N := by
  apply commutator_le.mpr
  intro k hk f hf
  have hconjK : f*k⁻¹*f⁻¹ ∈ K :=
    (mem_normalizer_iff.mp (hFK hf) k⁻¹).mp (K.inv_mem hk)
  have hsame : k ∈ N ↔ f*k⁻¹*f⁻¹ ∈ N :=
    N.inv_mem_iff.symm.trans (mem_normalizer_iff.mp (hFN hf) k⁻¹)
  have hmul := (N.subgroupOf K).mul_mem_iff_of_index_two hindex
    (a := ⟨k,hk⟩) (b := ⟨f*k⁻¹*f⁻¹,hconjK⟩) |>.mpr hsame
  change k*(f*k⁻¹*f⁻¹) ∈ N at hmul
  simpa only [commutatorElement_def,mul_assoc] using hmul

end Subgroup
