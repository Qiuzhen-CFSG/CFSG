module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.NoncyclicExtension

/-!
# Source F.6.18 in the noncyclic three-core case

The complete proved F.6.16 family supplies rows (1) and (2) for the original
Goldschmidt generators. The Heisenberg action is transported through the
ambient equivalence, giving an actual extraspecial kernel of order 27 and
its actual four-group quotient. No F.6.18 classification input is assumed.

Source: Aschbacher–Smith, F.6.16 and F.6.18, printed pp.308–310.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
universe u
variable {K : GroupClass.{u}} {D : Type u} [Group D] [Finite D]
    {G₁ G₂ : Subgroup D}

/-- The original SQTK quotient supplies the first two source alternatives,
with the actual common Sylow subgroup and local cores. -/
theorem noncyclic_source (q : ThreePrimeSQTKQuotient K D)
    (h : ChapterF.IsGoldschmidtTriple G₁ G₂) (S : Sylow 2 D)
    (hS : G₁ ⊓ G₂ = (S : Subgroup D)) (hn : ¬ IsCyclic (pCore 3 D)) :
    Alternative G₁ G₂ S := by
  let := q.coverGroup
  let := q.coverFinite
  obtain ⟨_, hcases⟩ := ChapterF.SourceAssembly.source_lemma_F_6_16 q.sqtk q.equiv.symm h hn
  rcases hcases with ⟨⟨e⟩, hleft, hright⟩ | hprod | heis
  · apply Alternative.one ⟨(MulEquiv.subgroupCongr hS.symm).trans e⟩ _ _ hn
    · exact ((pCore 2 G₁).map_eq_bot_iff_of_injective G₁.subtype_injective).mp hleft
    · exact ((pCore 2 G₂).map_eq_bot_iff_of_injective G₂.subtype_injective).mp hright
  · exact Alternative.two (Or.inl hprod)
  · obtain ⟨e⟩ := heis
    obtain ⟨f, _, _, he, hc, hx, hq⟩ := ChapterF.SourceAssembly.heisenberg_extension_data e
    exact Alternative.two (Or.inr ⟨f.ker, inferInstance, he, hc, hx, hq⟩)

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
