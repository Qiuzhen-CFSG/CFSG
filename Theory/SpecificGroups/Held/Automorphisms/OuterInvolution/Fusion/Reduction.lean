module

public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.Fusion.Normalizer
public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.Fusion.Words
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations

/-!
# Transport of outer involution fusion in the full Held normalizer

Sylow conjugacy reduces a full-normalizer involution to a chosen Sylow.
The index-two decomposition turns the resulting normalizer conjugator into
an actual Held conjugator. Faithfulness gives the implementer's order from
its action's order, and the final transport uses the literal normalizer map.
The finite Sylow fusion premise is explicit until its certificate is supplied.
Source: GLS3 Table 5.3p and the interpretation on pp.260–261.
-/

@[expose] public section
namespace Held.OuterInvolution.Fusion
open Subgroup LocalPairs LocalPairs.SylowGeometry
open scoped Pointwise

def IsCovered (n : PermutationNormalizer) : Prop :=
  ∃ g : He, MulAut.conj (innerEmbedding g) representative = n

theorem IsCovered.conj {n : PermutationNormalizer} (h : IsCovered n)
    (d : PermutationNormalizer) : IsCovered (MulAut.conj d n) := by
  obtain ⟨c, rfl⟩ := h
  rcases normalizer_cases (d * innerEmbedding c) with ⟨g, hg⟩ | ⟨g, hg⟩
  · refine ⟨g, ?_⟩
    rw [← MulAut.mul_apply, ← map_mul, ← hg]
  · refine ⟨g, ?_⟩
    rw [← MulAut.mul_apply, ← map_mul, ← hg, map_mul, MulAut.mul_apply]
    simp [MulAut.conj_apply]

theorem outer_isCovered : IsCovered outer := ⟨shift, rfl⟩

theorem action_coverage_of_isCovered (n : PermutationNormalizer) (h : IsCovered n) :
    ∃ g : He, MulAut.congr (MulAut.conj g) action =
      permutationGroup.normalizerMonoidHom n := by
  obtain ⟨g, rfl⟩ := h
  refine ⟨g, ?_⟩
  rw [MulAut.conj_apply, map_mul, map_mul, map_inv, normalizerAction_innerEmbedding]
  rfl

theorem coverage_of_sylow (P : Sylow 2 PermutationNormalizer)
    (hP : ∀ y : P, orderOf (y : PermutationNormalizer) = 2 →
      (y : PermutationNormalizer) ∉ innerSubgroup → IsCovered y) :
    ∀ n : PermutationNormalizer,
      orderOf (permutationGroup.normalizerMonoidHom n) = 2 →
      (¬ ∃ g : He, MulAut.conj g = permutationGroup.normalizerMonoidHom n) →
      ∃ g : He, MulAut.congr (MulAut.conj g) action =
        permutationGroup.normalizerMonoidHom n := by
  intro n hn hout
  have hn' : orderOf n = 2 := (normalizer_action_order n).symm.trans hn
  have hnout : n ∉ innerSubgroup :=
    fun h => hout ((normalizer_action_inner_iff n).mpr h)
  have hnp : IsPGroup 2 (zpowers n) :=
    IsPGroup.of_card (n := 1) (by simpa only [pow_one, Nat.card_zpowers] using hn')
  obtain ⟨S, hS⟩ := hnp.exists_le_sylow
  obtain ⟨d, hd⟩ := MulAction.exists_smul_eq PermutationNormalizer P S
  have hmem := hS (mem_zpowers n)
  rw [← hd] at hmem
  change n ∈ (P : Subgroup PermutationNormalizer).map (MulAut.conj d).toMonoidHom at hmem
  obtain ⟨y, hy, hyconj⟩ := hmem
  have hyorder : orderOf y = 2 := by
    rw [← orderOf_injective (MulAut.conj d).toMonoidHom (MulAut.conj d).injective y,
      hyconj, hn']
  have hyout : y ∉ innerSubgroup := by
    intro hyin
    apply hnout
    rw [← hyconj]
    exact (inferInstance : innerSubgroup.Normal).conj_mem y hyin d
  apply action_coverage_of_isCovered
  exact hyconj ▸ (hP ⟨y, hy⟩ hyorder hyout).conj d
end Held.OuterInvolution.Fusion
