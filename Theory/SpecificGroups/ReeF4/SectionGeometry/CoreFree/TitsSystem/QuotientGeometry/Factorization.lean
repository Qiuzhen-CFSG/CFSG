module

public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.TitsSystem.QuotientGeometry.Monomial
public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.TitsSystem.QuotientGeometry.FixedWords

/-!
# Torus factorization and fixed-point descent for Ree normalizer words

The specified Weyl-monomial presentation supplies a simple word with the same
root permutation. Multiplying by its inverse leaves a height-triangular word,
which lies in the torus by the explicit kernel hypothesis. If the original
matrix is fixed, comparison with its twist shows that the simple word has
fixed Weyl action. Faithfulness of the simple-word representation makes that
word fixed as a matrix. Fixed Weyl descent then uses the two orbit words,
and the remaining torus factor is fixed as well.

Only the two stated matrix hypotheses enter the normalizer generation result.
Their unconditional construction belongs to the source-theorem assembly.
Source: GLS3 2.3.2–4, `refs/KGroup/GLS3/chapter2.tex`.
-/

public section
noncomputable section
namespace ReeF4.SectionGeometry.BNPair.QuotientGeometry
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction Subgroup
open Parabolics Parabolics.Binary.FixedGeometry
open Parabolics.Binary.FixedGeometry.BruhatCoverage.FixedWeyl
open LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover
open NormalizerGeometry

/-- Matching the genuine Weyl action leaves exactly a torus factor. -/
theorem exists_torus_mul_simpleWord (m : ℕ)
    (hweyl : ∀ n ∈ splitNormalizerWords m,
      ∃ (w : typeF4RootPairing.weylGroup) (c : F4Chevalley.Root → (CoefficientField m)ˣ),
        RootMonomial n.val.val (typeF4RootPairing.weylGroupToPerm w) c)
    (hkernel : ∀ n ∈ splitNormalizerWords m,
      Overlap.IsHeightTriangular n → n ∈ diagonalTorus m)
    {n : SplitGroup m} (hn : n ∈ splitNormalizerWords m) :
    ∃ t ∈ splitTorus m, ∃ l : List (Fin 4), n = t * simpleWord m l := by
  obtain ⟨w, c, hc⟩ := hweyl n hn
  obtain ⟨l, _, hl⟩ := typeF4RootPairing_base.wordLength_spec w
  let k := l.map typeF4RootPairing_baseEquiv.symm
  have hk : rootWord k = w := by
    simpa [rootWord, k, List.map_map] using hl
  have hm := rootMonomial_mul hc (monomial_inv (simpleWord_rootMonomial m k))
  rw [hk, mul_inv_cancel] at hm
  have ht : n * (simpleWord m k)⁻¹ ∈ splitTorus m := by
    rw [splitTorus_eq_diagonalTorus]
    apply hkernel
    · exact (splitNormalizerWords m).mul_mem hn
        ((splitNormalizerWords m).inv_mem (simpleWord_mem_splitNormalizerWords m k))
    · exact Overlap.heightTriangular_of_rootMonomial_one _ _ hm
  exact ⟨_, ht, k, (inv_mul_cancel_right n (simpleWord m k)).symm⟩

/-- A fixed torus-times-Weyl matrix has a fixed simple-word factor. -/
theorem simpleWord_fixed_of_torus_mul (m : ℕ) {n : Model m} {t : SplitGroup m}
    (ht : t ∈ splitTorus m) {l : List (Fin 4)}
    (he : toSplitGroup m n = t * simpleWord m l) :
    reeTwist m (simpleWord m l) = simpleWord m l := by
  have htf : reeTwist m t ∈ splitTorus m := by
    have h := Subgroup.mem_map_of_mem (reeAutomorphism m).toMonoidHom ht
    rw [splitTorus_invariant] at h
    simpa only [MulEquiv.coe_toMonoidHom, reeAutomorphism_apply] using h
  have he' : reeTwist m t * simpleWord m (l.map Fin.revPerm) =
      t * simpleWord m l := by
    rw [← reeTwist_simpleWord, ← map_mul, ← he, reeTwist_toSplitGroup]
  obtain ⟨a, ha⟩ := torus_rootMonomial ht
  obtain ⟨b, hb⟩ := torus_rootMonomial htf
  have hleft := rootMonomial_mul hb (simpleWord_rootMonomial m (l.map Fin.revPerm))
  have hright := rootMonomial_mul ha (simpleWord_rootMonomial m l)
  change RootMonomial (reeTwist m t * simpleWord m (l.map Fin.revPerm)).val.val _ _ at hleft
  rw [he'] at hleft
  have hw := monomial_perm_unique hleft hright
  simp only [one_mul] at hw
  rw [reeTwist_simpleWord]
  exact (simpleWord_eq_iff m _ _).mpr (weyl_perm_injective hw)

end ReeF4.SectionGeometry.BNPair.QuotientGeometry

namespace ReeF4.SectionGeometry.BNPair
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem Subgroup
open Parabolics Parabolics.Binary.FixedGeometry QuotientGeometry
open LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover
open NormalizerGeometry

/-- The two shared matrix facts give generation by the fixed torus and orbit words. -/
theorem normalizerWords_le_fixedTorus_sup_weylSubgroup_of_monomial (m : ℕ)
    (hweyl : ∀ n ∈ splitNormalizerWords m,
      ∃ (w : typeF4RootPairing.weylGroup) (c : F4Chevalley.Root → (CoefficientField m)ˣ),
        RootMonomial n.val.val (typeF4RootPairing.weylGroupToPerm w) c)
    (hkernel : ∀ n ∈ splitNormalizerWords m,
      Overlap.IsHeightTriangular n → n ∈ diagonalTorus m) :
    normalizerWords m ≤ fixedTorus m ⊔ weylSubgroup m := by
  intro n hn
  obtain ⟨t, ht, l, he⟩ := exists_torus_mul_simpleWord m hweyl hkernel hn
  have hf := simpleWord_fixed_of_torus_mul m ht he
  obtain ⟨v, hv, hval⟩ := fixed_simpleWord_mem_map m l hf
  have ht' : n * v⁻¹ ∈ fixedTorus m := by
    change toSplitGroup m (n * v⁻¹) ∈ splitTorus m
    rw [map_mul, map_inv, hval, he, mul_inv_cancel_right]
    exact ht
  simpa only [inv_mul_cancel_right] using
    (fixedTorus m ⊔ weylSubgroup m).mul_mem (mem_sup_left ht') (mem_sup_right hv)

end ReeF4.SectionGeometry.BNPair
