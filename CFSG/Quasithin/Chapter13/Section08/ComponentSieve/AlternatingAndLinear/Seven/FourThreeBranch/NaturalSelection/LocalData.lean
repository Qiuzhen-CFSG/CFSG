module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.FourThreeBranch.NaturalSelection.Factors
public import Theory.GroupTheory.ElementaryNineMarkedResiduals

/-!
# Earlier local residual data for the covered-A₆ branch

This interface records the local consequences used in the proof of 13.7.5(7):
L₁ has elementary-nine quotient above its own two-core, the two two-perfect
residual factors generate it, and a specified actor fixes one cubic quotient
line and inverts the other. The normalization conditions are relative to L₁
and T. Inversion is asserted only in L₁/O₂(L₁).

The record makes no assertion about a seven-point image, surjectivity, or a
natural module. Its local facts are explicit inputs for the 13.8.24 assembly;
the residual definitions themselves occur in Notation 13.2.1, and their
generation in 13.2.2(3). Proving their permutation consequences remains the
responsibility of that assembly, not of these data projections.

Source: Aschbacher–Smith, Notation 13.2.1, 13.2.2(3) and the proof of
13.7.5(7), printed pp.877–878 and 938 (1 March 2004 manuscript).
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.FourThreeBranch.NaturalSelection

/-- Actual earlier local data. Both residual conditions are two-perfectness;
the quotient and all normalization conditions retain their intrinsic carriers. -/
structure LocalResidualData {G : Type*} [Group G] (L₁ L₀ X T : Subgroup G) where
  quotient : L₁ ⧸ pCore 2 L₁ ≃* Multiplicative (ZMod 3) × Multiplicative (ZMod 3)
  generated : L₀ ⊔ X = L₁
  first_perfect : IsPPerfect 2 L₀
  second_perfect : IsPPerfect 2 X
  core_normalizes_first : (pCore 2 L₁).map L₁.subtype ≤ normalizer (L₀ : Set G)
  core_normalizes_second : (pCore 2 L₁).map L₁.subtype ≤ normalizer (X : Set G)
  sylow_normalizes_first : T ≤ normalizer (L₀ : Set G)
  sylow_normalizes_second : T ≤ normalizer (X : Set G)
  first_card : Nat.card ((L₀.subgroupOf L₁).map (QuotientGroup.mk' (pCore 2 L₁))) = 3
  second_card : Nat.card ((X.subgroupOf L₁).map (QuotientGroup.mk' (pCore 2 L₁))) = 3
  actor : normalizer (L₁ : Set G)
  actor_mem : actor.val ∈ T
  fixes_first : ∀ a : L₁, a.val ∈ L₀ →
    QuotientGroup.mk' (pCore 2 L₁) (L₁.normalizerMonoidHom actor a) =
      QuotientGroup.mk' (pCore 2 L₁) a
  inverts_second : ∀ a : L₁, a.val ∈ X →
    QuotientGroup.mk' (pCore 2 L₁) (L₁.normalizerMonoidHom actor a) =
      (QuotientGroup.mk' (pCore 2 L₁) a)⁻¹

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.FourThreeBranch.NaturalSelection
