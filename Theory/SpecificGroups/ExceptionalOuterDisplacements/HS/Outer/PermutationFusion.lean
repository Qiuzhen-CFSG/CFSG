module

public import Theory.SpecificGroups.ExceptionalOuterDisplacements.HS.Outer.PermutationFusion.Enumeration
public import Theory.SpecificGroups.ExceptionalOuterDisplacements.HS.Outer.PermutationFusion.LocalFusion
public import Theory.GroupTheory.SylowElementConjugacy
/-!
Adapted from `CFSG/Quasithin/Chapter16/Section01To02/OtherPreliminaries/
JankoTwoHigmanSims/HSOuter/` for the intrinsic HS displacement theorem.
The original modules and their public interfaces are preserved. Original
ATLAS HSG1-p100B0 attribution is retained in `LICENSES/ATLAS.txt`.

# Exhaustive fusion of the two concrete outer HS involutions

The representatives both normalize the exact ATLAS carrier and lie outside it.
The normalizer has order 88,704,000. The certified subgroup of order 1024 is
therefore Sylow; conjugating an arbitrary involution into it reduces the result
to the checked binary-family fusion calculation. Conjugacy throughout takes
place in the normalizer, and hence preserves membership in HS.

This proves the permutation-fusion input for the outer case of
Aschbacher–Smith 16.1.5(10), printed p.1172, and GLS3 Table 5.3m, classes
2C and 2D. Identifying the two centralizers remains a separate calculation
in the source-theorem assembly owner.
-/

public section
namespace Theory.SpecificGroups.ExceptionalOuterDisplacements.HS.Outer
open Subgroup Sporadic.LeechRelated.HS

/-- Sylow conjugacy reduces fusion of outer involutions to one Sylow subgroup
of the normalizer, retaining normalizing conjugators throughout. -/
theorem permutation_fusion_of_sylow
    (P : Sylow 2 PermutationNormalizer)
    (hP : ∀ y ∈ P, orderOf y = 2 → y.val ∉ generated →
      IsConj y elementaryNormalizer ∨ IsConj y symmetricNormalizer)
    (n : PermutationNormalizer) (hn : orderOf n = 2) (ho : n.val ∉ generated) :
    (∃ g : PermutationNormalizer,
      n.val = g.val * elementaryPermutation * g.val⁻¹) ∨
    (∃ g : PermutationNormalizer,
      n.val = g.val * symmetricPermutation * g.val⁻¹) := by
  obtain ⟨y, hy⟩ := P.exists_isConj_of_orderOf_eq_prime_pow
    (n := 1) (by simpa using hn)
  obtain ⟨g, hg⟩ := isConj_iff.mp hy
  have hyorder : orderOf y.val = 2 := by
    rw [← hg]
    exact ((MulAut.conj g).orderOf_eq n).trans hn
  have hyout : y.val.val ∉ generated := by
    have he : g.val * n.val * g.val⁻¹ = y.val.val := congrArg Subtype.val hg
    intro hm
    apply ho
    exact ((mem_normalizer_iff.mp g.property) n.val).mpr (he.symm ▸ hm)
  rcases hP y.val y.property hyorder hyout with he | hs
  · obtain ⟨g, hg⟩ := isConj_iff.mp (hy.trans he).symm
    exact Or.inl ⟨g, (congrArg Subtype.val hg).symm⟩
  · obtain ⟨g, hg⟩ := isConj_iff.mp (hy.trans hs).symm
    exact Or.inr ⟨g, (congrArg Subtype.val hg).symm⟩

/-- An order-1024 subgroup is Sylow because the normalizer has order
88704000 and 88704000 / 1024 is odd. -/
private noncomputable def sylowOfCard1024 (P : Subgroup PermutationNormalizer)
    (hP : Nat.card P = 1024) : Sylow 2 PermutationNormalizer :=
  (IsPGroup.of_card (show Nat.card P = 2 ^ 10 from hP)).toSylow (by
    have hc := P.card_mul_index
    rw [hP, permutationNormalizer_card] at hc
    have hi : P.index = 86625 := by omega
    rw [hi]
    decide)

/-- Every involution outside HS in its degree-100 normalizer is conjugate,
by an element of that same normalizer, to one of the two specified representatives. -/
theorem outer_involution_permutation_fusion
    (n : PermutationNormalizer) (hn : orderOf n = 2) (ho : n.val ∉ generated) :
    (∃ g : PermutationNormalizer,
      n.val = g.val * elementaryPermutation * g.val⁻¹) ∨
    (∃ g : PermutationNormalizer,
      n.val = g.val * symmetricPermutation * g.val⁻¹) := by
  apply permutation_fusion_of_sylow
    (sylowOfCard1024 PermutationFusion.candidate PermutationFusion.candidate_card) _ n hn ho
  intro y hy hyorder hyout
  change y ∈ PermutationFusion.candidate at hy
  obtain ⟨i, rfl⟩ := PermutationFusion.normalForm_surjective y hy
  exact PermutationFusion.normalForm_fusion i hyorder hyout

end Theory.SpecificGroups.ExceptionalOuterDisplacements.HS.Outer
