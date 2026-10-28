module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairNormalization.OppositionCell.FixedBruhatCover.Basic
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairNormalization.OppositionCell.FixedBruhatCover.SplitCoverage.Generation
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairNormalization.OppositionCell.FixedBruhatCover.SplitCoverage.Collection
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairNormalization.OppositionCell.FixedBruhatCover.SplitCoverage.NegativeSimple
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.SplitCoordinates.MatrixExchanges

/-!
# Split F₄ normal forms from local root exchange

Negative-simple exchange extends to unrestricted `U N U` coverage by root-word
induction. For a specified middle factor, root transport partitions the
positive roots by the signs of their images. Collecting the positive images
first absorbs them into the left factor; the remaining right factor lies in
`U ∩ n⁻¹ U⁻ n`, with left conjugation used throughout.

The rank-one words defining `N` include all nonzero parameters, so the middle
factor retains the torus. The positive-root exchanges follow from the actual
matrix identities. They supply the local negative-simple exchange theorem,
so `exists_split_normal_form` has root transport as its sole extra geometric
premise. This is the split existence step; the parent owns fixed-point descent
and the remaining normalizer geometry.

Source: GLS3 1.11.5 and 1.12.1, `refs/KGroup/GLS3/Chapter1.tex`;
the fixed-point application is 2.3.5, `refs/KGroup/GLS3/chapter2.tex`.
-/

public section
noncomputable section

namespace ReeF4.LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open Parabolics.RadicalCoordinates LargeLocalSeeds Subgroup

/-- The actual split root matrices satisfy the positive collection relations
over every coefficient field. -/
theorem positiveRootExchanges (m : ℕ) : PositiveRootExchanges m := by
  intro r s a b hrs
  exact rootGenerator_exchange m r s a b hrs

/-- Collect positive root images first and negative root images last.
Only the supplied element's exact root transport is used. -/
theorem rightUnipotent_factorization_of_positive_exchanges {m : ℕ}
    (hswap : PositiveRootExchanges m) {n c : SplitGroup m}
    (a : RootTransport n) (hc : c ∈ splitUnipotent m) :
    ∃ b ∈ splitUnipotent m, n * b * n⁻¹ ∈ splitUnipotent m ∧
      ∃ v ∈ rightUnipotent n, c = b * v := by
  let A := splitUnipotent m ⊓ (splitUnipotent m).comap (MulAut.conj n).toMonoidHom
  have hp (r : Root .positive) (t : CoefficientField m) :
      rootGeneratorInGroup m r.val t ∈ splitUnipotent m :=
    subset_closure ⟨r.val, t, r.property, rfl⟩
  have hpartition (r : Root .positive) :
      (∀ t, rootGeneratorInGroup m r.val t ∈ A) ∨
      (∀ t, rootGeneratorInGroup m r.val t ∈ rightUnipotent n) := by
    by_cases hr : typeF4RootPairing_base.IsPos (a.perm r.val)
    · refine Or.inl (fun t => ⟨hp r t, ?_⟩)
      change (MulAut.conj n) (rootGeneratorInGroup m r.val t) ∈ splitUnipotent m
      rw [a.conj_root]
      exact subset_closure ⟨_, _, hr, rfl⟩
    · refine Or.inr (fun t => ⟨hp r t, ?_⟩)
      change (MulAut.conj n) (rootGeneratorInGroup m r.val t) ∈ splitNegativeUnipotent m
      rw [a.conj_root]
      exact subset_closure ⟨_, _, hr, rfl⟩
  obtain ⟨b, hb, v, hv, he⟩ := positive_factorization_of_root_partition m hswap
    A (rightUnipotent n) hpartition hc
  exact ⟨b, hb.1, hb.2, v, hv, he⟩

/-- Local exchange and root transport give the restricted normal form.
The final theorem below supplies both exchange premises from the root matrices. -/
theorem exists_split_normal_form_of_root_exchanges {m : ℕ}
    (hswap : PositiveRootExchanges m) (hexchange : NegativeSimpleExchange m)
    (htransport : ∀ n ∈ splitNormalizerWords m, Nonempty (RootTransport n))
    (g : SplitGroup m) :
    ∃ u ∈ splitUnipotent m, ∃ n ∈ splitNormalizerWords m,
      ∃ v ∈ rightUnipotent n, g = u * n * v := by
  obtain ⟨u, hu, n, hn, c, hc, he⟩ :=
    exists_unrestricted_factors_of_negativeSimpleExchange m hexchange g
  obtain ⟨a⟩ := htransport n hn
  obtain ⟨b, _, hnb, v, hv, hcv⟩ :=
    rightUnipotent_factorization_of_positive_exchanges hswap a hc
  refine ⟨u * (n * b * n⁻¹), (splitUnipotent m).mul_mem hu hnb, n, hn, v, hv, ?_⟩
  rw [he, hcv]
  group

/-- Every split F₄ matrix has a normal form with its right factor in
`U ∩ n⁻¹ U⁻ n`. Both root-exchange premises are discharged; only exact root
transport for the actual normalizer words remains as a geometric input. -/
theorem exists_split_normal_form {m : ℕ} (hm : 1 ≤ m)
    (htransport : ∀ n ∈ splitNormalizerWords m, Nonempty (RootTransport n))
    (g : SplitGroup m) :
    ∃ u ∈ splitUnipotent m, ∃ n ∈ splitNormalizerWords m,
      ∃ v ∈ rightUnipotent n, g = u * n * v := by
  have hswap := positiveRootExchanges m
  exact exists_split_normal_form_of_root_exchanges hswap
    (negativeSimpleExchange_of_positive_exchanges m hm hswap htransport) htransport g

end ReeF4.LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover
