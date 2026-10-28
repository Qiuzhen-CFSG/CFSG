module

public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Centralizer
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.CoreAction

/-!
# The centralizer above a block product

If K is normal, F*(K)=O₂(K), and H/K is a two-group, then the centralizer
in H of [O₂(K),K] is a normal two-subgroup. This is the upper bound in
C.1.11. For a single block, the two-subgroup action theorem gives the
reverse bound, proving the full conclusion from H=KS with S Sylow two.
The structure of an arbitrary product of blocks remains a separate input.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
C.1.11, printed p.124.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC
variable {G : Type*} [Group G] [Finite G]

/-- The upper centralizer bound for a normal two-constrained subgroup
with two-group quotient. -/
theorem centralizer_blockU_le_core_of_normal (K : Subgroup G) [K.Normal]
    (hf : generalizedFitting K = pCore 2 K) (hq : IsPGroup 2 (G ⧸ K)) :
    centralizer ((blockU K).map K.subtype : Set G) ≤ pCore 2 G := by
  let U := (blockU K).map K.subtype
  let C := centralizer (U : Set G)
  have hUn : U.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    exact (show (⊤ : Subgroup G) ≤ normalizer K from le_normalizer_of_normal).trans
      (normalizer_le_normalizer_characteristic_image K (blockU K))
  let := hUn
  have hCp : IsPGroup 2 C := by
    intro c
    obtain ⟨n, hn⟩ := hq (QuotientGroup.mk' K c)
    have hcK : (c : G) ^ 2 ^ n ∈ K := by
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk' K ((c : G) ^ 2 ^ n) = 1
      rwa [map_pow]
    have hcC : (⟨(c : G) ^ 2 ^ n, hcK⟩ : K) ∈ centralizer (blockU K : Set K) := by
      intro u hu
      apply Subtype.ext
      exact C.pow_mem c.property (2 ^ n) u (mem_map_of_mem K.subtype hu)
    have hcore := centralizer_blockU_le_of_fitting hf hcC
    obtain ⟨m, hm⟩ := (pCore_isPGroup (p := 2) (G := K)) ⟨_, hcore⟩
    refine ⟨n + m, Subtype.ext ?_⟩
    change (c : G) ^ 2 ^ (n + m) = 1
    rw [pow_add, pow_mul]
    exact congrArg (fun x : pCore 2 K => ((x : K) : G)) hm
  exact le_sSup ⟨inferInstance, hCp⟩

/-- C.1.11 for one block. Normality is proved from the actual product
factorization and two-perfection; it is not an additional hypothesis. -/
theorem lemma_C_1_11_single (K : Subgroup G) (hK : IsBlock K) (S : Sylow 2 G)
    (hprod : ∀ g : G, ∃ k ∈ K, ∃ s ∈ (S : Subgroup G), k * s = g) :
    centralizer ((blockU K).map K.subtype : Set G) = pCore 2 G := by
  have he := pResidual_eq_of_subnormal_product K (S : Subgroup G)
    hK.subnormal hK.short.twoPerfect S.isPGroup' hprod
  have hn : K.Normal := he ▸ inferInstance
  let := hn
  have hq : IsPGroup 2 (G ⧸ K) :=
    (isPGroup_quotient_pResidual (G := G) 2).of_equiv
      (QuotientGroup.quotientMulEquivOfEq he)
  exact le_antisymm (centralizer_blockU_le_core_of_normal K hK.short.fitting hq)
    hK.core_centralizes_blockU

end CFSG.Quasithin.ChapterC
