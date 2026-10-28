module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.EmbeddingReduction.BinaryAction.Basic
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.EmbeddingReduction.BinaryAction.FiveOuter

/-!
# Binary-linear branch of the contrary Sylow overgroup

For L/O₂(L) isomorphic to PSL₄(2) or PSL₅(2), the actual conjugation action
of LU on L/O₂(L) is surjective and has kernel O₂(LU). Thus its first
isomorphism theorem gives LU/O₂(LU) ≃ Aut(L/O₂(L)). The actual outer
quotient also has order prime to three, as needed by the residual argument.

Relative normality and the Sylow hypothesis give a permuting Sylow pair in
the component quotient. In both dimensions, inner pair automorphisms would
preserve a proper nontrivial subgroup of the complement's Frattini quotient,
contrary to local irreducibility. Hence an outer automorphism occurs. The
proved inner/graph coverage then gives surjectivity, and centerlessness
identifies the kernel. The source D₈ hypothesis is retained in the component
statement; the stronger local result already follows from this irreducibility.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
printed pp.509–511 and p.1164.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.EmbeddingReduction.BinaryAction
open Chapter1

variable {G : Type*} [Group G] [Finite G] {U X P H L : Subgroup G}

/-- The actual conjugation action fills Aut(L/O₂(L)) and has exactly kernel O₂(LU). -/
theorem binary_action_surjective_and_kernel {n : ℕ}
    (h : XiEmbedding.LocalInput 3 U X P H) (hS : IsSylowIn 2 U H)
    (hLH : L ≤ H) (hLn : (L.subgroupOf H).Normal) (hXL : X ≤ L)
    (hn : n = 4 ∨ n = 5) (hm : ClassicalGroup.IsPSL (XiQuotient L) n 2)
    (hUL : U ≤ normalizer L) :
    Function.Surjective (pCoreJoinAction 2 hUL) ∧
      (pCoreJoinAction 2 hUL).ker = pCore 2 (L ⊔ U : Subgroup G) := by
  refine ⟨?_, pCoreJoinAction_kernel 2 hUL h.two_group
    (binary_linear_center_eq_bot (by omega : 0 < n) hm)⟩
  apply binary_surjective_of_outer hn hm (pCoreJoinAction 2 hUL)
    (inner_le_pCoreJoinAction_range 2 hUL)
  rcases hn with rfl | rfl
  · exact four_outer h hS hLH hLn hXL hm
  · exact outer_range_of_not_innerNormalizer hUL
      (five_not_le_innerNormalizer h hS hLH hLn hXL hm)

/-- Both binary dimensions, using only the local hypotheses consumed by the action proof. -/
theorem binary_quotient_aut_of_local {n : ℕ}
    (h : XiEmbedding.LocalInput 3 U X P H) (hS : IsSylowIn 2 U H)
    (hLH : L ≤ H) (hLn : (L.subgroupOf H).Normal) (hXL : X ≤ L)
    (hn : n = 4 ∨ n = 5) (hm : ClassicalGroup.IsPSL (XiQuotient L) n 2) :
    Nonempty (XiQuotient (L ⊔ U) ≃* MulAut (XiQuotient L)) := by
  have hUL : U ≤ normalizer L := (le_sup_right.trans h.overgroup).trans
    ((normal_subgroupOf_iff_le_normalizer hLH).mp hLn)
  obtain ⟨hs, hk⟩ := binary_action_surjective_and_kernel h hS hLH hLn hXL hn hm hUL
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (pCoreJoinAction 2 hUL) hs)⟩

/-- The complete degree-five companion to `four_quotient_aut`. -/
theorem five_quotient_aut
    (h : XiEmbedding.LocalInput 3 U X P H) (hS : IsSylowIn 2 U H)
    (hLH : L ≤ H) (hLn : (L.subgroupOf H).Normal) (hXL : X ≤ L)
    (hm : ClassicalGroup.IsPSL (XiQuotient L) 5 2) :
    Nonempty (XiQuotient (L ⊔ U) ≃* MulAut (XiQuotient L)) :=
  binary_quotient_aut_of_local h hS hLH hLn hXL (Or.inr rfl) hm

/-- The full binary automorphism quotient under the component inputs of 15.4.20. -/
theorem binary_quotient_aut {κ : GroupClass}
    (_hH : IsSQTK κ H) (h : XiEmbedding.LocalInput 3 U X P H)
    (hS : IsSylowIn 2 U H) (hL : L ∈ cComponentsIn H)
    (hLn : (L.subgroupOf H).Normal) (hXL : X ≤ L)
    (_hq : IsQuasisimple (XiQuotient L))
    (_hD : Nonempty (XiEmbedding.automizer U P ≃* DihedralGroup 4))
    (hm : ClassicalGroup.IsPSL (XiQuotient L) 4 2 ∨
      ClassicalGroup.IsPSL (XiQuotient L) 5 2) :
    Nonempty (XiQuotient (L ⊔ U) ≃* MulAut (XiQuotient L)) := by
  rcases hm with hm | hm
  · exact four_quotient_aut h hS hL.1 hLn hXL hm
  · exact five_quotient_aut h hS hL.1 hLn hXL hm

/-- Prime-to-three order of Aut/Inn for either actual binary model. -/
theorem binary_outer_prime_to_three_of_models {Q : Type*} [Group Q] [Finite Q]
    (hm : ClassicalGroup.IsPSL Q 4 2 ∨ ClassicalGroup.IsPSL Q 5 2) :
    Nat.Coprime 3 (Nat.card (MulAut.Outer Q)) := by
  rcases hm with hm | hm
  · exact binary_outer_prime_to_three (Or.inl rfl) hm
  · exact binary_outer_prime_to_three (Or.inr rfl) hm

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.EmbeddingReduction.BinaryAction
