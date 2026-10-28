module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.GoldschmidtAlternatives
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.NoncyclicExtension

/-!
# The proved noncyclic branch of the universal F.6.18 consumer

Applying F.6.16 to the literal quotient H/O₃′(H) gives row (1) or row (2).
The Heisenberg alternative retains the actual quotient homomorphism and
its kernel isomorphism. This discharges the noncyclic branch of
`F618Universal` with no classification-output premise.

Source: Aschbacher–Smith, F.6.16 and F.6.18, printed pp.308–310,
and the comparison application 15.4.18, printed p.1163.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
universe u
variable {K : GroupClass.{u}} {H : Type u} [Group H] [Finite H]

/-- F.6.18 for the actual source quotient when its three-core is noncyclic. -/
theorem F618_noncyclic_source (hH : IsSQTK K H)
    (G₁ G₂ : Subgroup (threePrimeQuotient H))
    (h : ChapterF.IsGoldschmidtTriple G₁ G₂)
    (hn : ¬ IsCyclic (pCore 3 (threePrimeQuotient H))) :
    GoldschmidtAlternatives.Alternatives G₁ G₂ := by
  obtain ⟨_, hcases⟩ := ChapterF.SourceAssembly.source_lemma_F_6_16 hH (MulEquiv.refl _) h hn
  rcases hcases with ⟨he, hleft, hright⟩ | hprod | heis
  · exact Or.inl (Or.inl ⟨he,
      ((pCore 2 G₁).map_eq_bot_iff_of_injective G₁.subtype_injective).mp hleft,
      ((pCore 2 G₂).map_eq_bot_iff_of_injective G₂.subtype_injective).mp hright, hn⟩)
  · exact Or.inl (Or.inr (Or.inl (Or.inl hprod)))
  · obtain ⟨e⟩ := heis
    obtain ⟨f, hf, hk, _⟩ := ChapterF.SourceAssembly.heisenberg_extension_data e
    exact Or.inl (Or.inr (Or.inl (Or.inr ⟨f, hf, hk⟩)))

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
