module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.RootPair
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairNormalization.OppositionCell.RootTransport
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairNormalization.OppositionCell.FixedBruhatCover.Basic
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairNormalization.OppositionCell.FixedBruhatCover.NormalizerGeometry
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairNormalization.OppositionCell.FixedBruhatCover.SplitCoverage

/-!
# Descent of split F₄ normal forms to a supplied Ree fixed group

Twisting a split normal form gives a second normal form of the same fixed
element. Uniqueness of the middle matrix makes it fixed. The positive/negative
intersection argument then fixes both unipotent factors. A root-transport
theorem for the normalizer-word subgroup supplies the exact root action needed
by the opposition-cell argument.

The conditional descent lemmas retain their three explicit geometric premises.
The final theorem discharges them using split root exchange and collection,
root-monomial separation, and exact root transport for the actual nonzero
rank-one words. Thus every element of the supplied fixed group has the required
factorization for `m ≥ 1`, with torus factors retained in the middle matrix.
Simplicity, perfectness and odd index are not needed for this conclusion. No
comparison with `Model`, identification of the whole fixed Weyl group, or
opposition element is used.

Source: GLS3 1.11.5 and 2.3.4–5, 2.3.8(b) in
`refs/KGroup/GLS3/Chapter1.tex` and `refs/KGroup/GLS3/chapter2.tex`.
-/

public section

namespace ReeF4.LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover
open LargeLocalSeeds

/-- Split coverage and middle-factor uniqueness give fixed normal-form
factors directly in the supplied fixed subgroup. This is conditional descent. -/
theorem exists_fixed_factors_of_split {m : ℕ} (d : LocalBlockInput m)
    (hcover : ∀ g : SplitGroup m,
      ∃ u ∈ splitUnipotent m, ∃ n ∈ splitNormalizerWords m,
        ∃ v ∈ rightUnipotent n, g = u * n * v)
    (hseparate : ∀ {u n v u' n' v' : SplitGroup m},
      u ∈ splitUnipotent m → n ∈ splitNormalizerWords m → v ∈ rightUnipotent n →
      u' ∈ splitUnipotent m → n' ∈ splitNormalizerWords m → v' ∈ rightUnipotent n' →
      u * n * v = u' * n' * v' → n = n')
    (x : d.fixedGroup) :
    ∃ u ∈ standardUnipotent d, ∃ n : d.fixedGroup,
      n.val ∈ splitNormalizerWords m ∧
      ∃ v ∈ standardUnipotent d, x = u * n * v := by
  obtain ⟨u, hu, n, hn, v, hv, he⟩ := hcover x.val
  have hxfixed : d.twist x.val = x.val := x.property
  have hproduct : d.twist u * d.twist n * d.twist v = u * n * v := by
    rw [← map_mul, ← map_mul, ← he, hxfixed, he]
  have hnfix : d.twist n = n := hseparate
    (twist_mem_splitUnipotent d hu) (twist_mem_splitNormalizerWords d hn)
    (twist_mem_rightUnipotent d hv) hu hn hv hproduct
  obtain ⟨hufix, hvfix⟩ := fixed_unipotent_factors d hxfixed hnfix hu hv he
  let u₀ : d.fixedGroup := ⟨u, hufix⟩
  let n₀ : d.fixedGroup := ⟨n, hnfix⟩
  let v₀ : d.fixedGroup := ⟨v, hvfix⟩
  refine ⟨u₀, hu, n₀, hn, v₀, hv.1, ?_⟩
  exact Subtype.ext he

/-- The root-transport form of fixed Bruhat coverage follows after all three
split geometric premises have been supplied. The premises are not construction
data for `LocalBlockInput` and must be discharged in the final assembly. -/
theorem exists_root_bruhat_of_split {m : ℕ} (d : LocalBlockInput m)
    (hcover : ∀ g : SplitGroup m,
      ∃ u ∈ splitUnipotent m, ∃ n ∈ splitNormalizerWords m,
        ∃ v ∈ rightUnipotent n, g = u * n * v)
    (hseparate : ∀ {u n v u' n' v' : SplitGroup m},
      u ∈ splitUnipotent m → n ∈ splitNormalizerWords m → v ∈ rightUnipotent n →
      u' ∈ splitUnipotent m → n' ∈ splitNormalizerWords m → v' ∈ rightUnipotent n' →
      u * n * v = u' * n' * v' → n = n')
    (htransport : ∀ n ∈ splitNormalizerWords m, Nonempty (RootTransport n))
    (x : d.fixedGroup) :
    ∃ u ∈ standardUnipotent d, ∃ n : d.fixedGroup,
      Nonempty (RootTransport n.val) ∧
      ∃ v ∈ standardUnipotent d, x = u * n * v := by
  obtain ⟨u, hu, n, hn, v, hv, he⟩ := exists_fixed_factors_of_split d hcover hseparate x
  exact ⟨u, hu, n, htransport n.val hn, v, hv, he⟩

/-- Every element of the supplied Ree fixed group has positive fixed outer
factors and a fixed middle representative acting exactly on all split root
curves. Split coverage, uniqueness and root transport are all discharged. -/
theorem exists_root_bruhat {m : ℕ} (hm : 1 ≤ m) (d : LocalBlockInput m)
    (x : d.fixedGroup) :
    ∃ u ∈ standardUnipotent d, ∃ n : d.fixedGroup,
      Nonempty (RootTransport n.val) ∧
      ∃ v ∈ standardUnipotent d, x = u * n * v := by
  have htransport : ∀ n ∈ splitNormalizerWords m, Nonempty (RootTransport n) :=
    fun _ hn => rootTransport_of_mem_splitNormalizerWords hn
  exact exists_root_bruhat_of_split d (exists_split_normal_form hm htransport)
    middle_representative_unique htransport x

end ReeF4.LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover
